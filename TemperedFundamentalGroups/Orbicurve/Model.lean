/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Orbicurve.Stable

/-!
# The affine presentation of IUT's model orbicurves

IUT's orbicurve `(E, ℓ, M, ±)` over a field `k` (an elliptic curve `E`, a level `ℓ`, a subgroup
`M ≤ E(k)` and a sign flag) stands for `(E / M) ∖ (E[ℓ] / M)`, possibly modulo `±1`. We present
it as the quotient orbifold `[Y / A]` with

* `Y = E ∖ S` for the set `S = removedSet W ℓ M = E(k)[ℓ] + M` of rational points, whose
  coordinate ring is `orbicurveRing W ℓ M = ringOf W S`;
* `A = affGroup W M pm`, the group of affine automorphisms `P ↦ ε • P + m` with `m ∈ M` and
  `ε = 1` unless `pm = true`, acting on `orbicurveRing W ℓ M` by `k`-algebra automorphisms.

When `M ≤ E(k)[ℓ]` (as in IUT), `S = E(k)[ℓ]` (`removedSet_eq_torsionSet`), and when moreover
`E[ℓ] ⊆ E(k)` this is exactly IUT's orbicurve.
-/

universe u

open WeierstrassCurve

namespace TemperedFundamentalGroups.Orbicurve

noncomputable section

variable {k : Type u} [Field k] [DecidableEq k] (W : WeierstrassCurve k)

/-- IUT's group of affine automorphisms `P ↦ ε • P + m` with `m ∈ M`, and `ε = 1` unless
`pm = true` (then `ε = ±1`): `M` or `M ⋊ {±1}`. -/
def affGroup (M : AddSubgroup W.toAffine.Point) (pm : Bool) : Subgroup (AffAut W) where
  carrier := {g | g.m ∈ M ∧ (pm = false → g.ε = 1)}
  one_mem' := ⟨M.zero_mem, fun _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨M.add_mem ?_ hg, fun hpm => by rw [AffAut.mul_ε, hg' hpm, hh' hpm, mul_one]⟩
    rw [Units.smul_def]
    exact M.zsmul_mem hh _
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨M.neg_mem ?_, fun hpm => by rw [AffAut.inv_ε, hg' hpm, inv_one]⟩
    rw [Units.smul_def]
    exact M.zsmul_mem hg _

variable {W} in
lemma mem_affGroup {M : AddSubgroup W.toAffine.Point} {pm : Bool} {g : AffAut W} :
    g ∈ affGroup W M pm ↔ g.m ∈ M ∧ (pm = false → g.ε = 1) := Iff.rfl

/-- The rational `ℓ`-torsion points `E(k)[ℓ]`. -/
def torsionSet (ℓ : ℕ) : Set W.toAffine.Point :=
  {P | ℓ • P = 0}

/-- The set `E(k)[ℓ] + M` of rational points removed in IUT's orbicurve `(E, ℓ, M, ±)`. -/
def removedSet (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) : Set W.toAffine.Point :=
  {P | ∃ m ∈ M, ℓ • (P - m) = 0}

variable {W}

/-- If `M ≤ E(k)[ℓ]`, the removed set is `E(k)[ℓ]`. -/
lemma removedSet_eq_torsionSet {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}
    (hM : ∀ m ∈ M, ℓ • m = 0) : removedSet W ℓ M = torsionSet W ℓ := by
  ext P
  constructor
  · rintro ⟨m, hm, h⟩
    change ℓ • P = 0
    rw [smul_sub, hM m hm, sub_zero] at h
    exact h
  · intro h
    exact ⟨0, M.zero_mem, by rw [sub_zero]; exact h⟩

instance (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) (pm : Bool) :
    IsAffStable (removedSet W ℓ M) (affGroup W M pm) where
  zero_mem := ⟨0, M.zero_mem, by rw [sub_zero, smul_zero]⟩
  neg_mem := by
    rintro P ⟨m, hm, h⟩
    refine ⟨-m, M.neg_mem hm, ?_⟩
    rw [neg_sub_neg, ← neg_sub, smul_neg, h, neg_zero]
  smul_mem := by
    rintro g ⟨hgm, -⟩ P ⟨m, hm, h⟩
    refine ⟨g.ε • m + g.m, M.add_mem ?_ hgm, ?_⟩
    · rw [Units.smul_def]
      exact M.zsmul_mem hm _
    · rw [AffAut.smul_def, add_sub_add_right_eq_sub, ← smul_sub, smul_comm, h, smul_zero]

lemma isAffStable_torsionSet {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}
    (hM : ∀ m ∈ M, ℓ • m = 0) (pm : Bool) :
    IsAffStable (torsionSet W ℓ) (affGroup W M pm) := by
  rw [← removedSet_eq_torsionSet hM]
  infer_instance

variable (W)

/-- The coordinate ring of `Y = E ∖ (E(k)[ℓ] + M)`, the affine curve presenting IUT's orbicurve
`(E, ℓ, M, ±)` as `[Y / affGroup W M pm]`. -/
abbrev orbicurveRing (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) : Subalgebra k (funField W) :=
  ringOf W (removedSet W ℓ M)

variable {W} in
lemma orbicurveRing_eq_ringOf_torsionSet {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}
    (hM : ∀ m ∈ M, ℓ • m = 0) : orbicurveRing W ℓ M = ringOf W (torsionSet W ℓ) := by
  rw [orbicurveRing, removedSet_eq_torsionSet hM]

example [W.IsElliptic] (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) (pm : Bool) :
    MulSemiringAction (affGroup W M pm) (orbicurveRing W ℓ M) := inferInstance

example [W.IsElliptic] (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) (pm : Bool) :
    SMulCommClass (affGroup W M pm) k (orbicurveRing W ℓ M) := inferInstance

end

end TemperedFundamentalGroups.Orbicurve
