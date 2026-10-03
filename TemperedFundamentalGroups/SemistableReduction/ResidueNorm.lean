/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussReduction
import TemperedFundamentalGroups.SemistableReduction.ResidueCurve

/-!
# The residue of a norm at the Gauss point

Blueprint §9.9, W7 layer S6 (i). Let `F / C(X)` be finite with `e(w) = 1` for all extensions `w`
of the Gauss valuation `w_{0,1}` and `Σ_w f(w) = [F : C(X)]` (W4). For `z ∈ F` with
`gnorm z ≤ 1`, the norm `N_{F/C(X)}(z)` lies in the valuation ring of `w_{0,1}` and its residue
is the product of the residue norms:

  `res (N_{F/C(X)} z) = ∏_w N_{κ(w)/κ(w_{0,1})}(z̄_w)` (`residue_norm_eq_prod`).

Proof: in the orthonormal basis `b` of G6.3 (`GaussFibre.exists_orthonormal_basis'`, indexed by
`Σ_w Fin f(w)`) the matrix of `z` has integral entries; its reduction is block diagonal, the
`w`-block being the matrix of `z̄_w` in the basis of `κ(w)` formed by the residues of the
`b_{(w, l)}` (the `b_{(w', l)}`, `w' ≠ w`, reduce to `0` at `w`). The determinant of a block
diagonal matrix with blocks of varying size is the product of the determinants
(`det_blockDiagonal'`).
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal

namespace Matrix

variable {R o : Type*} [CommRing R] [Fintype o] [DecidableEq o] {m : o → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- The determinant of a block diagonal matrix with square blocks of varying sizes. -/
theorem det_blockDiagonal'' (M : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  letI : LinearOrder o := LinearOrder.lift' (Fintype.equivFin o) (Fintype.equivFin o).injective
  have hT : (blockDiagonal' M).BlockTriangular Sigma.fst := fun i j h ↦ by
    obtain ⟨k, i'⟩ := i
    obtain ⟨k', j'⟩ := j
    exact blockDiagonal'_apply_ne M i' j' (ne_of_gt h)
  rw [hT.det]
  have hblock : ∀ a, ((blockDiagonal' M).toSquareBlock Sigma.fst a).det = (M a).det := by
    intro a
    let e : m a ≃ {i : Σ i, m i // i.1 = a} := Equiv.ofBijective
      (fun l ↦ ⟨⟨a, l⟩, rfl⟩) ⟨fun l l' h ↦ by
        have := congrArg Subtype.val h
        exact eq_of_heq (Sigma.mk.inj this).2, fun ⟨⟨a', l⟩, h⟩ ↦ by subst h; exact ⟨l, rfl⟩⟩
    rw [← det_submatrix_equiv_self e]
    congr 1
    ext l l'
    simp [toSquareBlock, toSquareBlockProp, e]
  simp_rw [hblock]
  refine Finset.prod_subset (Finset.subset_univ _) fun a _ ha ↦ ?_
  haveI : IsEmpty (m a) := ⟨fun l ↦ ha (Finset.mem_image.2 ⟨⟨a, l⟩, Finset.mem_univ _, rfl⟩)⟩
  exact det_isEmpty

end Matrix

namespace SemistableReduction

open FundamentalInequality GaussStability

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [Fintype (Ext C F)] [FiniteDimensional (RatFunc C) F]

local notation "κ₁" => ResidueField (Valuation.valuationSubring (gauss1 C))

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
/-- **The residue of the norm at the Gauss point** (S6 (i)). -/
theorem residue_norm_eq_prod (he : ∀ w : Ext C F, ramificationIdx (RatFunc C) w.1 = 1)
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F)
    {z : F} (hz : gnorm C z ≤ 1) :
    ∃ h : gauss1 C (Algebra.norm (RatFunc C) z) ≤ 1,
      residue (gauss1 C).valuationSubring ⟨_, h⟩ =
        ∏ w : Ext C F, Algebra.norm κ₁ (red C z w) := by
  classical
  obtain ⟨b, horth, hsmall, hres⟩ := exists_orthonormal_basis' he hsum
  choose ℓ hℓli hℓ using hres
  set O := (gauss1 C).valuationSubring
  -- the integral matrix of `z`
  have hM : ∀ i j, gauss1 C (Algebra.leftMulMatrix b z i j) ≤ 1 := fun i j ↦
    (gauss1_leftMulMatrix_le horth z i j).trans hz
  let M' : Matrix (OIndex C F) (OIndex C F) O := fun i j ↦ ⟨_, hM i j⟩
  have hMM : Algebra.leftMulMatrix b z = M'.map (algebraMap O (RatFunc C)) := by
    ext i j; rfl
  have hnorm : Algebra.norm (RatFunc C) z = algebraMap O (RatFunc C) M'.det := by
    rw [Algebra.norm_eq_matrix_det b, hMM, RingHom.map_det, RingHom.mapMatrix_apply]
  refine ⟨by rw [hnorm]; exact M'.det.2, ?_⟩
  -- the bases of the residue fields
  have hfin (w : Ext C F) : Module.Finite κ₁ (ResidueField w.1.valuationSubring) :=
    finite_residueField
  have hne (w : Ext C F) : Nonempty (Fin (inertiaDeg (gauss1 C) w.1)) :=
    ⟨⟨0, Module.finrank_pos⟩⟩
  let β (w : Ext C F) : Module.Basis (Fin (inertiaDeg (gauss1 C) w.1)) κ₁
      (ResidueField w.1.valuationSubring) :=
    basisOfLinearIndependentOfCardEqFinrank (hℓli w) (by rw [Fintype.card_fin]; rfl)
  have hβ (w : Ext C F) (l) : β w l = residue w.1.valuationSubring (ℓ w l) := by
    simp [β, coe_basisOfLinearIndependentOfCardEqFinrank]
  -- reductions of the basis
  have hb1 (i : OIndex C F) (w : Ext C F) : w.1 (b i) ≤ 1 := by
    by_cases hw : w = i.1
    · subst hw
      have : (b i : F) = (b i - ℓ i.1 i.2) + ℓ i.1 i.2 := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le (hℓ i.1 i.2).le (ℓ i.1 i.2).2)
    · exact (hsmall i w hw).le
  have hredb (i : OIndex C F) (w : Ext C F) :
      red C (b i) w = if h : i.1 = w then h ▸ β i.1 i.2 else 0 := by
    split_ifs with h
    · subst h
      rw [hβ, ← sub_eq_zero, ← red_of_le (ℓ i.1 i.2).2, ← red_sub (hb1 i i.1) (ℓ i.1 i.2).2,
        red_eq_zero_iff (by
          have : (b i : F) - ℓ i.1 i.2 = b i + -(ℓ i.1 i.2 : F) := sub_eq_add_neg _ _
          rw [this]
          exact (Valuation.map_add _ _ _).trans (max_le (hb1 i i.1) (by
            rw [Valuation.map_neg]; exact (ℓ i.1 i.2).2)))]
      exact hℓ i.1 i.2
    · exact (red_eq_zero_iff (hb1 i w)).2 (hsmall i w (Ne.symm h))
  -- the reduced matrix is block diagonal
  have hexp (j : OIndex C F) (w : Ext C F) :
      red C z w * red C (b j) w = ∑ l, algebraMap κ₁ (ResidueField w.1.valuationSubring)
        (residue O (M' ⟨w, l⟩ j)) * β w l := by
    have hzb : z * b j = ∑ i, algebraMap (RatFunc C) F (Algebra.leftMulMatrix b z i j) * b i := by
      conv_lhs => rw [← b.sum_repr (z * b j)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.smul_def]
    have hzw : w.1 z ≤ 1 := (le_gnorm w z).trans hz
    rw [← red_mul hzw (hb1 j w), hzb, red_sum _ _ fun i _ ↦ by
      rw [map_mul, valuation_algebraMap]
      exact mul_le_one' (hM i j) (hb1 i w)]
    simp_rw [red_algebraMap_mul _ (hM _ _) (hb1 _ w), hredb]
    rw [Fintype.sum_sigma, Finset.sum_eq_single w]
    · refine Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [dite_eq_ite, if_true]
      rfl
    · intro w' _ hw'
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      simp [hw']
    · simp
  have hblock : M'.map (residue O) = Matrix.blockDiagonal' fun w ↦
      Algebra.leftMulMatrix (β w) (red C z w) := by
    ext ⟨w, l⟩ ⟨w', l'⟩
    rw [Matrix.map_apply, Matrix.blockDiagonal'_apply']
    split_ifs with h
    · subst h
      rw [Algebra.leftMulMatrix_eq_repr_mul]
      simp only [cast_eq]
      have := hexp ⟨w, l'⟩ w
      simp only [hredb, dite_true] at this
      rw [this, map_sum]
      simp_rw [← Algebra.smul_def, map_smul, Module.Basis.repr_self]
      simp [Finsupp.single_apply]
    · have := hexp ⟨w', l'⟩ w
      simp only [hredb, Ne.symm h, dite_false, mul_zero] at this
      have hli := (β w).linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      exact hli _ (by simpa [Algebra.smul_def] using this.symm) l
  have hdet : (⟨Algebra.norm (RatFunc C) z, by rw [hnorm]; exact M'.det.2⟩ : O) = M'.det :=
    Subtype.ext hnorm
  rw [hdet, RingHom.map_det, RingHom.mapMatrix_apply, hblock, Matrix.det_blockDiagonal'']
  exact Finset.prod_congr rfl fun w _ ↦ (Algebra.norm_eq_matrix_det (β w) _).symm

end GaussFibre

end SemistableReduction
