/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Valuations for the tempered fundamental group

The tempered fundamental group of a curve over a field `k` depends on a (non-archimedean)
valuation of `k`, and its fibre functor at a geometric point `Spec Ω → Y` on an extension of that
valuation to `Ω` (Blueprint §3.1). This file provides:

* `ValuationSubring.exists_comap_eq`: every valuation subring `O` of `k` extends to any field
  extension `Ω / k`, i.e. there is a valuation subring `V` of `Ω` with `V ∩ k = O` (Chevalley).
* `canonicalValuationSubring k`: the valuation subring used when only the field `k` is given
  (the IUT interface passes `[Field k]` only): a henselian discrete valuation ring of `k` if one
  exists, and `k` itself (the trivial valuation) otherwise.

## Canonicity

For a field `k` which is not separably closed, a nontrivial henselian valuation ring of rank one
is unique (F. K. Schmidt: two independent nontrivial henselian valuations only exist on separably
closed fields; two distinct discrete valuation rings of the same field are independent). Hence
for the completions `K_v` of number fields at finite places — the fields over which IUT
evaluates tempered fundamental groups — `canonicalValuationSubring K_v` is the valuation ring
`O_v`. The definition itself only uses a choice; F. K. Schmidt's theorem and the resulting
identification (`canonicalValuationSubring_eq_of_isHenselianDVR`, valid for every henselian
DVR `O` of `k`) are proved in `TemperedFundamentalGroups.Setup.Schmidt`.
-/

universe u

namespace TemperedFundamentalGroups

/-- **Chevalley's extension theorem** for valuation subrings: a valuation subring `O` of `k`
extends to a valuation subring `V` of any field extension `Ω` with `V ∩ k = O`. -/
theorem ValuationSubring.exists_comap_eq {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (O : ValuationSubring k) : ∃ V : ValuationSubring Ω, V.comap (algebraMap k Ω) = O := by
  obtain ⟨V, hV⟩ := (O.toLocalSubring.map (algebraMap k Ω)).exists_le_valuationSubring
  refine ⟨V, ?_⟩
  have hinj : Function.Injective (algebraMap k Ω) := (algebraMap k Ω).injective
  -- `O` is dominated by `V ∩ k`.
  have hle : O.toLocalSubring ≤ (V.comap (algebraMap k Ω)).toLocalSubring := by
    refine ⟨fun x hx => hV.1 ⟨x, hx, rfl⟩, ⟨fun x hx => ?_⟩⟩
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hx
    have hy' : (x : k) * (y : k) = 1 := congrArg Subtype.val hy
    have hx0 : (x : k) ≠ 0 := left_ne_zero_of_mul_eq_one hy'
    -- the image of `x` in `V` is a unit
    have hunit : IsUnit (Subring.inclusion hV.1 ⟨algebraMap k Ω x, ⟨x, x.2, rfl⟩⟩) := by
      refine isUnit_iff_exists_inv.2 ⟨⟨algebraMap k Ω y, y.2⟩, Subtype.ext ?_⟩
      change algebraMap k Ω x * algebraMap k Ω y = 1
      rw [← map_mul, hy', map_one]
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.1 (hV.2.1 _ hunit)
    obtain ⟨w, hw, hwz⟩ := z.2
    have hxw : (x : k) * w = 1 := by
      apply hinj
      rw [map_mul, map_one, hwz]
      exact congrArg Subtype.val hz
    exact isUnit_iff_exists_inv.2 ⟨⟨w, hw⟩, Subtype.ext hxw⟩
  have := O.isMax_toLocalSubring hle
  exact le_antisymm this.1 hle.1

/-- The predicate "`O` is a henselian discrete valuation ring". -/
def IsHenselianDVR {k : Type*} [Field k] (O : ValuationSubring k) : Prop :=
  IsDiscreteValuationRing O ∧ HenselianLocalRing O

open Classical in
/-- **The canonical valuation subring** of a field: a henselian discrete valuation ring if `k`
has one (by F. K. Schmidt's theorem it is then unique, see
`canonicalValuationSubring_eq_of_isHenselianDVR`; for the completion `K_v` of a number field it
is `O_v`), and the trivial valuation ring `k` otherwise. -/
noncomputable def canonicalValuationSubring (k : Type u) [Field k] : ValuationSubring k :=
  if h : ∃ O : ValuationSubring k, IsHenselianDVR O then h.choose else ⊤

lemma canonicalValuationSubring_isHenselianDVR {k : Type u} [Field k]
    (h : ∃ O : ValuationSubring k, IsHenselianDVR O) :
    IsHenselianDVR (canonicalValuationSubring k) := by
  rw [canonicalValuationSubring, dif_pos h]
  exact h.choose_spec

lemma canonicalValuationSubring_eq_top {k : Type u} [Field k]
    (h : ¬ ∃ O : ValuationSubring k, IsHenselianDVR O) :
    canonicalValuationSubring k = ⊤ := by
  rw [canonicalValuationSubring, dif_neg h]

end TemperedFundamentalGroups
