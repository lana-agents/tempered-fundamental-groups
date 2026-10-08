/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentNodeData

/-!
# Semistability over `O_E` at ordinary double points over `C` (O1, W10 form)

Blueprint §9.12, O1. `isSemistableAt_of_descentData`: under the descent data of
`DVRDescentAssembly`, the integral closure `B_E` of the node chart over `O_E` is semistable at
`P' ∩ B_E`: it is étale-locally the node (`BranchData.isAnnulusAt`, S9).

* `isSemistableAt_of_descentData`: the semistability (`BranchData.isAnnulusAt` applied to
  `branchData`).
* `faithfulSMul_algO`, `finiteType_algO`: `B_E` is a faithful `O_E`-algebra of finite type.
-/

open NNReal Polynomial IsLocalRing Valuation WithZero

namespace SemistableReduction

namespace DVRDescent

open GaussTube

universe u v

variable {E : Type v} [NontriviallyNormedField E] [IsUltrametricDist E]
  {F₀ : Type v} [Field F₀] [Algebra (RatFunc E) F₀]

/-- `B_E` is a faithful `O_E`-algebra. -/
lemma faithfulSMul_algO (c₀ : E) :
    letI := algO (F₀ := F₀) c₀
    FaithfulSMul (HenselComplete.integers E) (BE F₀ c₀) := by
  letI := algO (F₀ := F₀) c₀
  refine (faithfulSMul_iff_algebraMap_injective _ _).mpr fun o o' h ↦ ?_
  have := congrArg (fun z : BE F₀ c₀ ↦ (z : F₀)) h
  simp only [algO_apply] at this
  change algebraMap (RatFunc E) F₀ (algebraMap E (RatFunc E) o) =
    algebraMap (RatFunc E) F₀ (algebraMap E (RatFunc E) o') at this
  exact Subtype.ext
    ((algebraMap E (RatFunc E)).injective ((algebraMap (RatFunc E) F₀).injective this))

/-- `B_E` is an `O_E`-algebra of finite type. -/
lemma finiteType_algO [IsNoetherianRing (HenselComplete.integers E)]
    [FiniteDimensional (RatFunc E) F₀] [Algebra.IsSeparable (RatFunc E) F₀] {c₀ : E}
    (hc0 : c₀ ≠ 0) (hc1 : ‖c₀‖ ≤ 1) :
    letI := algO (F₀ := F₀) c₀
    Algebra.FiniteType (HenselComplete.integers E) (BE F₀ c₀) := by
  letI := algO (F₀ := F₀) c₀
  have hcO : NormedField.valuation (K := E) c₀ ≤ 1 := by
    rw [NormedField.valuation_apply]; exact_mod_cast hc1
  -- the node chart is of finite type over `O_E`
  letI : Algebra (HenselComplete.integers E) (nodeRing c₀) :=
    (((algebraMap E (RatFunc E)).comp (HenselComplete.integers E).subtype).codRestrict _
      fun e ↦ algebraMap_mem_nodeRing ((HenselComplete.mem_integers_iff _).1 e.2)).toAlgebra
  haveI : IsScalarTower (HenselComplete.integers E) (nodeRing c₀) (BE F₀ c₀) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  set f := ZariskiModel.nodeLift (v := NormedField.valuation (K := E))
    (y := (RatFunc.X : RatFunc E)) RatFunc.X_ne_zero hcO
  have h := ZariskiModel.range_nodeLift (v := NormedField.valuation (K := E))
    (y := (RatFunc.X : RatFunc E)) RatFunc.X_ne_zero hcO
  haveI : Algebra.FiniteType (HenselComplete.integers E) (nodeRing c₀) := by
    let g : Node (HenselComplete.integers E) (ZariskiModel.elemO hcO) →ₐ[HenselComplete.integers E]
        nodeRing c₀ :=
      { toRingHom := f.toRingHom.codRestrict _ fun z ↦ by
          have : f z ∈ f.range.toSubring := ⟨z, rfl⟩
          rw [h] at this; exact this
        commutes' := fun o ↦ Subtype.ext (f.commutes o) }
    refine Algebra.FiniteType.of_surjective g ?_
    rintro ⟨z, hz⟩
    have hz' : z ∈ f.range.toSubring := by rw [h]; exact hz
    obtain ⟨w, rfl⟩ := hz'
    exact ⟨w, rfl⟩
  haveI := isNoetherianRing_nodeRing (C := E) hc1
  haveI := isIntegrallyClosed_nodeRing hc0 hc1
  haveI := isFractionRing_nodeRing c₀
  haveI : Module.Finite (nodeRing c₀) (BE F₀ c₀) :=
    IsIntegralClosure.finite (nodeRing c₀) (RatFunc E) F₀ (BE F₀ c₀)
  exact Algebra.FiniteType.trans (S := nodeRing c₀) inferInstance inferInstance

section Descent

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] {φ : E →+* C}
  {χ : F₀ →+* F'}

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm ConstantDescent

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

set_option maxHeartbeats 1000000 in
-- the branch types are elaboration-heavy
/-- **Semistability at the descended node point** from the descent data: `B_E` is étale-locally
the node at `P' ∩ B_E`. -/
theorem isSemistableAt_of_descentData (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    [IsDiscreteValuationRing (HenselComplete.integers E)] [FiniteDimensional (RatFunc E) F₀]
    [Algebra.IsSeparable (RatFunc E) F₀]
    (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    {c₀ : E} {c : C} (hcc : φ c₀ = c) (hc : ‖c‖ < 1) (hc0 : c ≠ 0)
    {P' : Ideal (Rint c F')} [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c)
    (hODP : IsNodeODP hc hc0 P') {b₁ : OuterBranch C F'} (hb₁ : outerBranches hc P' = {b₁})
    {b₂ : OuterBranch C (Inv c hc0 F')} (hb₂ : innerBranches hc hc0 P' = {b₂})
    (ι : BE F₀ c₀ →+* Rint c F') (hι : ∀ y, (ι y : F') = χ y)
    (heo : ∀ (v : Ext C F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    (hei : ∀ (v : GaussExtension (0 : C) (invRad hc0 1) F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    (hLD₁ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE χ b₁.1))
    (hLD₂ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE (χInv hc0 χ) b₂.1))
    (t₀ : BE F₀ c₀) (ht₀ : ι t₀ ∉ P')
    (ht₀o : ∀ v : Ext C F', v ≠ b₁.1 → redHom hc v (ι t₀) = 0)
    (ht₀i : ∀ w : Ext C (Inv c hc0 F'), w ≠ b₂.1 → redHomInv hc hc0 w (ι t₀) = 0)
    (yu : BE F₀ c₀) (hyu₁ : b₁.2.1.valuation (redHom hc b₁.1 (ι yu)) = exp (-1))
    (hyu₂ : redHomInv hc hc0 b₂.1 (ι yu) = 0)
    (yv : BE F₀ c₀) (hyv₂ : b₂.2.1.valuation (redHomInv hc hc0 b₂.1 (ι yv)) = exp (-1))
    (hyv₁ : redHom hc b₁.1 (ι yv) = 0)
    (hspan : ∀ y : Rint c F', IsSpanned 𝓀 ι.range (redHom hc b₁.1) (redHomInv hc hc0 b₂.1) y)
    (hres : letI := kEAlgebra φ; ∀ b : BE F₀ c₀, ∃ t : kE φ,
      placeHom hc b₁.1 b₁.2.2 (ι b) = algebraMap (kE φ) 𝓀 t)
    (halgk : letI := kEAlgebra φ; Algebra.IsAlgebraic (kE φ) 𝓀)
    {ϖ : HenselComplete.integers E} (hϖ : Irreducible ϖ) :
    letI := algO (F₀ := F₀) c₀
    IsSemistableAt ϖ (P'.comap ι) := by
  classical
  subst hcc
  have hc₀0 : c₀ ≠ 0 := by rintro rfl; exact hc0 (map_zero φ)
  have hc₀1 : ‖c₀‖ < 1 := by rw [← hφ]; exact hc
  letI := algO (F₀ := F₀) c₀
  haveI : IsNoetherianRing (BE F₀ c₀) := isNoetherianRing_BE F₀ hc₀0 hc₀1.le
  haveI : IsIntegrallyClosed (BE F₀ c₀) := isIntegrallyClosed_BE F₀ c₀
  haveI := faithfulSMul_algO (F₀ := F₀) c₀
  haveI := finiteType_algO (F₀ := F₀) hc₀0 hc₀1.le
  letI := isLocalRing_placeSub (Q := b₁.2.1) (M := resE χ b₁.1) fun _ ha ↦ resE_inv_mem ha
  letI := isLocalRing_placeSub (Q := b₂.2.1) (M := resE (χInv hc0 χ) b₂.1)
    fun _ ha ↦ resE_inv_mem ha
  haveI : (P'.comap ι).IsPrime := Ideal.comap_isPrime ι P'
  obtain ⟨_, _, -, H⟩ := branchData hp hp1 hφ hχ hdeg hθ hc hc0 hODP hb₁ hb₂ hι heo hei hLD₁
    hLD₂ t₀ ht₀ ht₀o ht₀i yu hyu₁ hyu₂ yv hyv₂ hyv₁ hspan hres halgk hϖ
  exact IsAnnulusAt.isSemistableAt (BranchData.isAnnulusAt H)

end Descent

end DVRDescent

end SemistableReduction
