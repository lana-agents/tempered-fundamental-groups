/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.FundamentalInequality

/-!
# Ramification index, inertia degree and defect in towers

Blueprint §9.4, A4. For a tower `K ⊆ L ⊆ M` of fields and a valuation `w` on `M`:

* `ramificationIdx_tower`: `e(w | K) = e(w | L) · e(w|_L | K)`;
* `inertiaDeg_tower`: `f(w | v) = f(w | u) · f(u | v)` for valuations `v`, `u`, `w` on `K`, `L`,
  `M` extending each other (the residue fields form a scalar tower,
  `isScalarTower_residueField`);
* `defectless_tower_iff`: `M / K` is defectless (`e · f = [M : K]`) iff `M / L` and `L / K` are
  (for the restrictions of `w`). This uses the fundamental inequality
  `ramificationIdx_mul_inertiaDeg_le` for both steps.
-/

open IsLocalRing Valuation

namespace SemistableReduction

namespace FundamentalInequality

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

section Residue

variable {Γ₀ Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]
  (v : Valuation K Γ₀) (u : Valuation L Γ₁) (w : Valuation M Γ₂)
  [v.HasExtension u] [u.HasExtension w] [v.HasExtension w]

/-- The residue fields of a tower of valuations form a scalar tower. -/
instance isScalarTower_residueField :
    IsScalarTower (ResidueField v.valuationSubring) (ResidueField u.valuationSubring)
      (ResidueField w.valuationSubring) := by
  refine IsScalarTower.of_algebraMap_eq' (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
  change residue w.valuationSubring (algebraMap _ _ x) =
    residue w.valuationSubring (algebraMap _ _ (algebraMap _ _ x))
  congr 1
  ext
  simp only [HasExtension.coe_algebraMap_valuationSubring_eq]
  exact IsScalarTower.algebraMap_apply K L M x

/-- The inertia degree is multiplicative in towers. -/
theorem inertiaDeg_tower : inertiaDeg v w = inertiaDeg u w * inertiaDeg v u := by
  rw [inertiaDeg, inertiaDeg, inertiaDeg, mul_comm,
    Module.finrank_mul_finrank (ResidueField v.valuationSubring)
      (ResidueField u.valuationSubring) (ResidueField w.valuationSubring)]

end Residue

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation M Γ)

lemma comap_comap_algebraMap :
    (w.comap (algebraMap L M)).comap (algebraMap K L) = w.comap (algebraMap K M) := by
  ext x
  simp [IsScalarTower.algebraMap_apply K L M]

/-- The restriction to `K` of the restriction to `L` is extended by the restriction to `L`. -/
instance hasExtension_comap_comap :
    (w.comap (algebraMap K M)).HasExtension (w.comap (algebraMap L M)) :=
  ⟨by rw [comap_comap_algebraMap]; exact Valuation.IsEquiv.refl⟩

/-- The ramification index is multiplicative in towers. -/
theorem ramificationIdx_tower :
    ramificationIdx K w = ramificationIdx L w * ramificationIdx K (w.comap (algebraMap L M)) := by
  have hA : valueGroup ((w.comap (algebraMap L M)).comap (algebraMap K L)) =
      valueGroup (w.comap (algebraMap K M)) := by
    rw [comap_comap_algebraMap]
  have hAB := valueGroup_comap_le (K := K) (w.comap (algebraMap L M))
  rw [hA] at hAB
  rw [ramificationIdx, ramificationIdx, ramificationIdx, hA, mul_comm,
    Subgroup.relIndex_mul_relIndex _ _ _ hAB (valueGroup_comap_le w)]

/-- `a · b = A · B` with `a ≤ A`, `b ≤ B`, `A, B > 0` forces `a = A` and `b = B`. -/
lemma eq_and_eq_of_mul_eq {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hA : 0 < A) (hB : 0 < B)
    (h : a * b = A * B) : a = A ∧ b = B := by
  refine ⟨le_antisymm ha (not_lt.1 fun hlt ↦ ?_), le_antisymm hb (not_lt.1 fun hlt ↦ ?_)⟩
  · exact (lt_of_le_of_lt (Nat.mul_le_mul_left a hb) (Nat.mul_lt_mul_of_pos_right hlt hB)).ne h
  · exact (lt_of_le_of_lt (Nat.mul_le_mul_right b ha) (Nat.mul_lt_mul_of_pos_left hlt hA)).ne h

/-- **Defect in towers.** `M / K` is defectless iff `M / L` and `L / K` are (for the
restrictions of `w`). -/
theorem defectless_tower_iff [FiniteDimensional K L] [FiniteDimensional L M] :
    ramificationIdx K w * inertiaDeg (w.comap (algebraMap K M)) w = Module.finrank K M ↔
      ramificationIdx L w * inertiaDeg (w.comap (algebraMap L M)) w = Module.finrank L M ∧
      ramificationIdx K (w.comap (algebraMap L M)) *
          inertiaDeg (w.comap (algebraMap K M)) (w.comap (algebraMap L M)) =
        Module.finrank K L := by
  have : FiniteDimensional K M := Module.Finite.trans L M
  rw [ramificationIdx_tower (L := L) w, inertiaDeg_tower _ (w.comap (algebraMap L M)),
    ← Module.finrank_mul_finrank K L M]
  constructor
  · intro h
    have h' := eq_and_eq_of_mul_eq ramificationIdx_mul_inertiaDeg_le
      ramificationIdx_mul_inertiaDeg_le Module.finrank_pos Module.finrank_pos
      ((by ring : _ = _).trans (h.trans (mul_comm _ _)))
    exact h'
  · rintro ⟨h₁, h₂⟩
    rw [mul_comm (Module.finrank K L), ← h₁, ← h₂]
    ring

end FundamentalInequality

end SemistableReduction
