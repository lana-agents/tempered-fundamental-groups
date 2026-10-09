#!/usr/bin/env bash
# Usage: scripts/mk_all.sh LIB [--check]
#
# `lake exe mk_all --lib LIB --git` regenerates the root module `LIB.lean` as a bare import list,
# without the copyright header that the root module carries. This wrapper runs `mk_all` on the
# root module with its header removed and puts the header back afterwards:
# * without `--check`, it regenerates the import list and keeps the header;
# * with `--check`, it runs `mk_all --check` on the import list below the header, i.e. it checks
#   that every `.lean` file of LIB is imported, in sorted order, and leaves the file unchanged.
set -euo pipefail
lib=$1; shift
root="$lib.lean"
header_end=$(grep -n -m1 '^-/$' "$root" | cut -d: -f1 || true)
if [ "$(head -n 1 "$root")" != "/-" ] || ! sed -n 2p "$root" | grep -q '^Copyright (c) ' \
    || [ -z "$header_end" ]; then
  echo "$root: missing copyright header" >&2
  exit 1
fi
saved=$(mktemp)
trap 'rm -f "$saved" "$saved.new"' EXIT
cp "$root" "$saved"
# The import list: everything after the header and the blank line following it.
tail -n +"$((header_end + 1))" "$saved" | sed '1{/^$/d}' > "$root"
rc=0
lake exe mk_all --lib "$lib" --git "$@" || rc=$?
{ head -n "$header_end" "$saved"; echo; cat "$root"; } > "$saved.new"
cp "$saved.new" "$root"
exit "$rc"
