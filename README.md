# tempered-fundamental-groups

Tempered fundamental groups, developed over formal schemes.

## Goals

Formalise the tempered fundamental group and its relation to the metric graph of a Mumford curve.

The development follows Emmanuel Lepage, *Tempered fundamental group and metric graph of a Mumford curve* (<https://arxiv.org/abs/0811.3169>), but deliberately works in the setting of **formal schemes rather than rigid geometry** — the formal-scheme foundations are built separately in `formal-schemes`.

## Status (branch `wp-tempered`)

The tempered fundamental group of an affine orbifold `[Spec R / A]` over a field `K` with a
valuation subring `O` is defined, as a topological group, together with the continuous comparison
homomorphism to the étale fundamental group (see `Blueprint.md` for the design, the
identification with André's definition, and what is cited rather than proved):

* `TemperedFundamentalGroups.temperedPi1 O R A V hV` — automorphisms of the fibre functor on
  tempered coverings presented by *levels* (finite étale `R`-algebras with a lift of the
  `A`-action), *projective `O`-models* of them, and equivariant covering spaces of the special
  fibres of the models; the fibre over the geometric point `Spec Ω → Spec R` is computed through
  the specialization map of the model (valuative criterion, with a valuation `V` of `Ω` over `O`).
* `TemperedFundamentalGroups.etalePi1 R A Ω` — automorphisms of the fibre functor on
  `A`-equivariant finite étale `R`-algebras; profinite (`etalePi1Profinite`), and for trivial `A`
  isomorphic as a topological group to Mathlib's `Aut (CommAlgCat.FiniteEtale.fiber R Ω)`
  (`etalePi1EquivAutFiber`).
* `TemperedFundamentalGroups.temperedToEtale` — the continuous comparison homomorphism.

Both groups live in `Type u` (all categories are coded so as to be small), as required by
`Iut.Anabelian.TemperedPi1Theory`.

The development works with algebraic `O`-models: the formal completion of a proper `O`-model
along its special fibre has the special fibre as underlying space, and its Zariski-locally
trivial coverings are the covering spaces of that space, so nothing of `formal-schemes` is
imported by the core (Blueprint §2, §7).

## Related repositories

Depends on `formal-schemes` (Spf, affine formal schemes, gluing) and on `conjugacy-separability` (profinite conjugacy control for discrete subgroups).

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
Library sources live under `TemperedFundamentalGroups/`, and every file must be imported from
the root module `TemperedFundamentalGroups.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib TemperedFundamentalGroups --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#7](https://taxis.lana.merten.dev/issues/7)
