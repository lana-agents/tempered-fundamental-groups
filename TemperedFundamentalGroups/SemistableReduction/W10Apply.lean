/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Compare
import TemperedFundamentalGroups.SemistableReduction.W7Statement
import TemperedFundamentalGroups.Setup.DVRNorm

/-!
# Applying W7 to the geometric components of a smooth cover

Blueprint §9.7a (W10 assembly). Let `K` be a complete discretely valued field of characteristic
`0` with valuation ring `O` and residue characteristic `p`, `C = K̄` with the spectral norm
(`DVRNorm`), and `A` a finite torsion-free smooth `K[X]`-algebra.

* **(A)** `exists_semistableTree`: W7 applied to the components `Comp K C A 𝔪` of `C ⊗_K A`
  (`W10Fields`) and a `Gal(C/K)`-stable family of discs gives a `Gal(C/K)`-stable Gauss tree
  containing it which is semistable for every component. The equivariance input of W7 is the
  semilinear action `piAct` of `Gal(C/K)` (`W10Action`).
* **(B)** `exists_isGalois`: finite sets of constants lie in finite Galois `E / K`;
  `exists_extend`: `K`-automorphisms of `E` extend to `C`. For `E ⊆ C` finite over `K`:
  `OE O E = {x ∈ E | ‖x‖ ≤ 1}`, the integral closure of `O` in `E` (`mem_OE_iff`,
  `isIntegralClosure_OE`), a discrete valuation ring (`isDiscreteValuationRing_OE`) finite over `O`
  (`finite_OE`) with `O_E ∩ K = O` (`comap_OE`), stable under `Gal(E/K)` (`algEquiv_mem_OE`), and
  generated over `O` by finitely many nonzero integral elements (`exists_generators`); the
  restricted norm `normedFieldE` on `E` (isometric inclusion `norm_coe`, ultrametric, complete).
-/

universe u

open Polynomial IsLocalRing

namespace SemistableReduction

namespace W10Apply

open TemperedFundamentalGroups W10Fields

attribute [local instance] polyAlgebra

section W7

variable {K : Type u} [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] {p : ℕ} (hp : p.Prime) (hpO : (p : O) ∈ maximalIdeal O)
  (A : Type u) [CommRing A] [Algebra K[X] A] [Module.Finite K[X] A] [Module.IsTorsionFree K[X] A]
  [Algebra K A] [IsScalarTower K K[X] A] [Algebra.Smooth K A]

local notation "C" => AlgebraicClosure K

include hp hpO in
/-- **(A) W7 for the geometric components.** For a `Gal(C/K)`-stable finite family of discs
`(a₀, c₀)` there is a `Gal(C/K)`-stable Gauss tree `(a, c) ⊇ (a₀, c₀)` which is semistable for
every component `Comp K C A 𝔪` of `C ⊗_K A`. -/
theorem exists_semistableTree (h7 : W7.Statement.{u, u})
    (hdef : letI := DVRNorm.normedFieldAlgCl O; haveI := DVRNorm.isUltrametricDist_algCl O
      ∀ 𝔪 : MaximalSpectrum (LX K C A), DefinedOverDVR C (Comp K C A 𝔪))
    {ι₀ : Type} [Finite ι₀] (a₀ c₀ : ι₀ → C)
    (hc₀ : ∀ k, c₀ k ≠ 0)
    (hstab : ∀ τ : C ≃ₐ[K] C, letI := DVRNorm.normedFieldAlgCl O;
      W7.DiscsLE (fun k ↦ τ (a₀ k)) c₀ a₀ c₀) :
    letI := DVRNorm.normedFieldAlgCl O; haveI := DVRNorm.isUltrametricDist_algCl O
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (a c : ι → C) (hc : ∀ i, c i ≠ 0),
      GaussTree.IsConvex (NormedField.valuation (K := C)) a c ∧
      GaussTree.IsReduced (NormedField.valuation (K := C)) a c ∧
      W7.DiscsLE a₀ c₀ a c ∧
      (∀ 𝔪 : MaximalSpectrum (LX K C A), W7.IsSemistableTree a c hc (Comp K C A 𝔪)) ∧
      ∀ τ : C ≃ₐ[K] C, W7.DiscsLE (fun i ↦ τ (a i)) c a c := by
  letI := DVRNorm.normedField O
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  haveI := Fintype.ofFinite ι₀
  haveI : Fintype (MaximalSpectrum (LX K C A)) := Fintype.ofFinite _
  haveI := isReduced_BX K C A
  set e : Fin (Fintype.card (MaximalSpectrum (LX K C A))) ≃ MaximalSpectrum (LX K C A) :=
    (Fintype.equivFin _).symm
  obtain ⟨ι, hι, hne, a, c, hc, hconv, hred, hle, hss, heq⟩ :=
    h7 C p hp (DVRNorm.norm_natCast_lt_one O hpO) (Fin (Fintype.card (MaximalSpectrum (LX K C A))))
      (fun k ↦ Comp K C A (e k)) (fun k ↦ hdef (e k)) ι₀ a₀ c₀ hc₀
  refine ⟨ι, hι, hne, a, c, hc, hconv, hred, hle, fun 𝔪 ↦ ?_, fun τ ↦ ?_⟩
  · obtain ⟨k, rfl⟩ := e.surjective 𝔪
    exact hss k
  · refine heq τ.toRingEquiv (DVRNorm.norm_algEquiv_apply O τ) ?_ (hstab τ)
    let α : (C ≃ₐ[K] C) →* (C ≃ₐ[K] C) := MonoidHom.id _
    let β : (C ≃ₐ[K] C) →* (A ≃ₐ[K[X]] A) := 1
    let Φ := RingEquiv.piCongrLeft (fun 𝔪 ↦ Comp K C A 𝔪) e
    refine ⟨Φ.trans ((piAct K C A α β τ).trans Φ.symm), fun φ k ↦ ?_⟩
    have hΦ : Φ (fun k ↦ algebraMap (RatFunc C) (Comp K C A (e k)) φ) =
        fun 𝔪 ↦ algebraMap (RatFunc C) (Comp K C A 𝔪) φ := by
      funext 𝔪
      obtain ⟨k, rfl⟩ := e.surjective 𝔪
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    change Φ.symm (piAct K C A α β τ (Φ _)) k = _
    rw [hΦ, piAct_algebraMap]
    exact Equiv.piCongrLeft_symm_apply _ _ _ _

end W7

/-! ### (B) The finite Galois extension `E` -/

section FieldE

variable {K : Type u} [Field K] [CharZero K]

local notation "C" => AlgebraicClosure K

/-- **(B1)** Every finite set of elements of `K̄` lies in a finite Galois extension of `K`. -/
theorem exists_isGalois (S : Finset C) :
    ∃ E : IntermediateField K C, FiniteDimensional K E ∧ IsGalois K E ∧ (S : Set C) ⊆ E := by
  let F := IntermediateField.adjoin K (S : Set C)
  haveI : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  refine ⟨IntermediateField.normalClosure K F C, inferInstance, ?_, ?_⟩
  · rw [isGalois_iff]
    exact ⟨inferInstance, inferInstance⟩
  · exact (IntermediateField.subset_adjoin K (S : Set C)).trans
      (IntermediateField.le_normalClosure F)

/-- **(B3)** Every `K`-automorphism of a normal `E ⊆ K̄` extends to `K̄`. -/
theorem exists_extend (E : IntermediateField K C) (σ : E ≃ₐ[K] E) :
    ∃ τ : C ≃ₐ[K] C, ∀ x : E, τ x = σ x :=
  ⟨σ.liftNormal C, fun x ↦ σ.liftNormal_commutes C x⟩

end FieldE

section ValE

variable {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] (E : IntermediateField K (AlgebraicClosure K))

instance : IsScalarTower O E (AlgebraicClosure K) := .of_algebraMap_eq fun _ ↦ rfl

/-- `O_E = {x ∈ E | ‖x‖ ≤ 1}`, for the spectral norm of `K̄`. -/
noncomputable def OE : ValuationSubring E :=
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  (NormedField.valuation (K := AlgebraicClosure K)).valuationSubring.comap
    (algebraMap E (AlgebraicClosure K))

lemma mem_OE_iff_norm (x : E) :
    letI := DVRNorm.normedFieldAlgCl O
    x ∈ OE O E ↔ ‖(x : AlgebraicClosure K)‖ ≤ 1 := by
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  change NormedField.valuation (algebraMap E (AlgebraicClosure K) x) ≤ 1 ↔ _
  rw [NormedField.valuation_apply, ← NNReal.coe_le_coe]
  rfl

/-- `O_E` is the integral closure of `O` in `E`. -/
lemma mem_OE_iff (x : E) : x ∈ OE O E ↔ IsIntegral O x := by
  rw [mem_OE_iff_norm, DVRNorm.norm_le_one_iff_isIntegral,
    ← isIntegral_algHom_iff (IsScalarTower.toAlgHom O E (AlgebraicClosure K))
      (algebraMap E (AlgebraicClosure K)).injective]
  rfl

/-- `O → O_E`. -/
noncomputable instance algebraOE : Algebra O (OE O E) :=
  ((algebraMap O E).codRestrict (OE O E).toSubring fun _ ↦
    (mem_OE_iff O E _).2 isIntegral_algebraMap).toAlgebra

instance : IsScalarTower O (OE O E) E := .of_algebraMap_eq fun _ ↦ rfl

instance isIntegralClosure_OE : IsIntegralClosure (OE O E) O E where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := ⟨fun h ↦ ⟨⟨x, (mem_OE_iff O E x).2 h⟩, rfl⟩,
    by rintro ⟨y, rfl⟩; exact (mem_OE_iff O E y).1 y.2⟩

/-- `O_E ∩ K = O`. -/
theorem comap_OE : (OE O E).comap (algebraMap K E) = O := by
  ext x
  rw [ValuationSubring.mem_comap, mem_OE_iff]
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K E) (algebraMap K E).injective).trans ?_
  rw [IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- `K`-automorphisms of `E` preserve `O_E`. -/
theorem algEquiv_mem_OE (σ : E ≃ₐ[K] E) {x : E} (hx : x ∈ OE O E) : σ x ∈ OE O E := by
  rw [mem_OE_iff] at hx ⊢
  exact hx.map ((σ : E →ₐ[K] E).restrictScalars O)

/-- The norm of `E`, restricted from `K̄`. -/
@[implicit_reducible]
noncomputable def normedFieldE : NontriviallyNormedField E :=
  letI := DVRNorm.normedField O
  letI := DVRNorm.normedFieldAlgCl O
  { SubfieldClass.toNormedField E with
    non_trivial := by
      obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm K
      refine ⟨algebraMap K E k, ?_⟩
      change 1 < ‖algebraMap K (AlgebraicClosure K) k‖
      rw [DVRNorm.norm_algebraMap]
      exact hk }

/-- The inclusion `E → K̄` is isometric. -/
lemma norm_coe (x : E) :
    letI := normedFieldE O E; letI := DVRNorm.normedFieldAlgCl O
    ‖x‖ = ‖(x : AlgebraicClosure K)‖ := rfl

lemma isUltrametricDist_E : letI := normedFieldE O E; IsUltrametricDist E := by
  letI := normedFieldE O E
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  exact ⟨fun x y z ↦ dist_triangle_max (x : AlgebraicClosure K) y z⟩

/-- `K` acts isometrically on `E`. -/
@[implicit_reducible]
noncomputable def normedSpaceE :
    letI := DVRNorm.normedField O; letI := normedFieldE O E; NormedSpace K E :=
  letI := DVRNorm.normedField O
  letI := normedFieldE O E
  letI := DVRNorm.normedFieldAlgCl O
  { norm_smul_le := fun k x ↦ le_of_eq (by
      change ‖((k • x : E) : AlgebraicClosure K)‖ = _
      rw [IntermediateField.coe_smul, Algebra.smul_def, norm_mul, DVRNorm.norm_algebraMap]
      rfl) }

lemma completeSpace_E [FiniteDimensional K E] : letI := normedFieldE O E; CompleteSpace E := by
  letI := DVRNorm.normedField O
  letI := normedFieldE O E
  letI := normedSpaceE O E
  haveI := DVRNorm.completeSpace O
  exact FiniteDimensional.complete K E

variable [CharZero K] [FiniteDimensional K E]

instance finite_OE : Module.Finite O (OE O E) :=
  IsIntegralClosure.finite O K E (OE O E)

instance isNoetherianRing_OE : IsNoetherianRing (OE O E) :=
  IsIntegralClosure.isNoetherianRing O K E (OE O E)

/-- **`O_E` is a discrete valuation ring.** -/
instance isDiscreteValuationRing_OE : IsDiscreteValuationRing (OE O E) := by
  have hnf : ¬ IsField (OE O E) := by
    intro hF
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hϖ0 : (ϖ : K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
    set y : OE O E := algebraMap O (OE O E) ϖ
    have hy : (y : E) = algebraMap K E ϖ := rfl
    have hy0 : y ≠ 0 := by
      intro h
      apply hϖ0
      have h' : (y : E) = 0 := by rw [h]; rfl
      rw [hy] at h'
      exact (map_eq_zero _).1 h'
    obtain ⟨z, hz⟩ := hF.mul_inv_cancel hy0
    have hz' : (z : E) = (y : E)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      have := congrArg (fun w : OE O E ↦ (w : E)) hz
      simpa using this
    have h2 : (ϖ : K)⁻¹ ∈ (OE O E).comap (algebraMap K E) := by
      rw [ValuationSubring.mem_comap, map_inv₀, ← hy, ← hz']
      exact z.2
    have hinv : (ϖ : K)⁻¹ ∈ O := (comap_OE O E).le h2
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O) (Subtype.ext (mul_inv_cancel₀ hϖ0)))
  have h := (IsDiscreteValuationRing.TFAE (R := OE O E) hnf).out 1 0
  exact h.1 (inferInstanceAs (ValuationRing (OE O E)))

lemma exists_irreducible_OE : ∃ ϖ : OE O E, Irreducible ϖ :=
  IsDiscreteValuationRing.exists_irreducible _

/-- **Generators**: `O_E` is generated as a ring by `O` and finitely many nonzero elements. -/
theorem exists_generators :
    ∃ (r : ℕ) (θ : Fin r → E), (∀ i, θ i ≠ 0) ∧ (∀ i, θ i ∈ OE O E) ∧
      (∀ i, IsIntegral O (θ i)) ∧
      ((OE O E : Set E) ⊆ Subring.closure (Set.range (algebraMap O E) ∪ Set.range θ)) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := OE O E)
  set s' := s.filter (· ≠ 0)
  refine ⟨s'.card, fun i ↦ ((s'.equivFin.symm i : OE O E) : E), fun i ↦ ?_, fun i ↦ ?_,
    fun i ↦ (mem_OE_iff O E _).1 (s'.equivFin.symm i : OE O E).2, ?_⟩
  · have := (Finset.mem_filter.1 (s'.equivFin.symm i).2).2
    exact fun h ↦ this (Subtype.ext h)
  · exact (s'.equivFin.symm i : OE O E).2
  · intro x hx
    have hmem : (⟨x, hx⟩ : OE O E) ∈ Submodule.span O (s : Set (OE O E)) := by rw [hs]; trivial
    set R := Subring.closure (Set.range (algebraMap O E) ∪
      Set.range fun i ↦ ((s'.equivFin.symm i : OE O E) : E))
    suffices ∀ z ∈ Submodule.span O (s : Set (OE O E)), (z : E) ∈ R from this _ hmem
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      by_cases h0 : z = 0
      · rw [h0]; exact zero_mem _
      · refine Subring.subset_closure (Or.inr ⟨s'.equivFin ⟨z, Finset.mem_filter.2 ⟨hz, h0⟩⟩, ?_⟩)
        simp
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul o z _ hz =>
      rw [Algebra.smul_def, MulMemClass.coe_mul]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨o, rfl⟩)) hz

end ValE

end W10Apply

end SemistableReduction
