/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalLevelNode
import TemperedFundamentalGroups.SemistableReduction.AdmissibleLift

/-!
# The level formal Kummer form along the nodes (MR12 T2 S6, step G2)

Let `R` be a chart over `O` with node coordinates `x y = ϖⁿ`, `B` an `R`-algebra and `D j` chosen
Kummer data (`FormalKummer.KummerNormAtData`) at nodes `𝔪 j` of `R`. Let `R'` be an `R`-algebra
(a level `R/ϖᵏ⁺¹R` of the chart), Noetherian, with `f ∈ R'` such that `V(f)` is the finite set of
maximal ideals `𝔪' j` (the nodes of `R'`; lemma F, `CompletionProd`), residue maps
`r j : N₁(D j) → R'/𝔪' j`, and formal node coordinates `χ_p : O[u,v]/(uv − ϖⁿ) → R̂'` (`R̂'` the
`f`-adic completion of `R'`) sending `u, v ↦ x, y`, for `p = (j, i)` running over the Kummer
factors. Then (**`FormalLevel.levelEquiv`**)

  `R̂' ⊗_R B ≃ₐ[R̂'] ∏_{p = (j,i)} (R̂'/(1 − εⱼ)) ⊗_{O[u,v]/(uv − ϖⁿ)} O[s,t]/(st − ϖ^{mᵢ})`,

the right side being the lifted Kummer model `∏_p AdmissibleLift.N f χ_p εⱼ` of the M2 lift
(`εⱼ = CompletionProd.idem`): the product over the nodes of the level Kummer forms
`FormalLevel.nodeEquiv` (base change of `D j`'s splitting along `hatLift (r j)`), with
`R̂'/(1 − εⱼ) ≅ R̂'_{𝔪' j}` (`CompletionProd.quotEquiv`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalLevel

noncomputable section

open KummerEtale FormalKummer

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] {ϖ : O} {n M' : ℕ} {x y : R}
  (hxy : x * y = algebraMap O R (ϖ ^ n))
  {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra O R'] [IsScalarTower O R R']
  [IsNoetherianRing R'] {f : R'} {ι : Type} [Fintype ι] [DecidableEq ι] {𝔪' : ι → Ideal R'}
  [∀ j, (𝔪' j).IsMaximal] (hinj : Function.Injective 𝔪') (hf : ∀ j, f ∈ 𝔪' j)
  (hrad : ⨅ j, 𝔪' j ≤ (Ideal.span {f}).radical)
  {𝔪 : ι → Ideal R} (D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j))
  (r : ∀ j, (D j).N₁ →ₐ[R] R' ⧸ 𝔪' j)
  (χ : ∀ p : (Σ j, Fin (D j).r),
    A (ϖ ^ (D p.1).m p.2) ((D p.1).d p.2) →ₐ[O] FormalPatchLevel.Hat f)
  (hχ : ∀ p a, χ p a = algebraMap R (FormalPatchLevel.Hat f) (chart hxy (D p.1) p.2 a))
  (ε : ι → FormalPatchLevel.Hat f) (hε : ∀ j, ε j = CompletionProd.idem hinj hf hrad j)

/-- The completion `R̂'_{𝔪' j}` at the node `j`. -/
abbrev Tj (j : ι) : Type u := AdicCompletion (𝔪' j) R'

/-- `O[s,t]/(st − c)` is the Kummer node `KNode c d`. -/
def knodeEquiv (c : O) (d : ℕ) : KNode c d ≃ₐ[A c d] KummerEtale.B c := AlgEquiv.refl

include hχ hε in
/-- `R̂'_{𝔪' j} ≅ R̂'/(1 − εⱼ)` as algebras over the node ring of the factor `p = (j, i)`
(`εⱼ` any idempotent equal to `CompletionProd.idem j`, e.g. the chosen lift of the M2 tower). -/
def pieceIso (p : Σ j, Fin (D j).r) :
    letI := hatAlg (𝔪' := 𝔪' p.1) hxy (D p.1) p.2
    Tj (𝔪' := 𝔪') p.1 ≃ₐ[A (ϖ ^ (D p.1).m p.2) ((D p.1).d p.2)]
      AdmissibleLift.LPiece f (χ p) (ε p.1) :=
  letI := hatAlg (𝔪' := 𝔪' p.1) hxy (D p.1) p.2
  AlgEquiv.ofRingEquiv (f := (CompletionProd.quotEquiv hinj hf hrad p.1).symm.trans
      (Ideal.quotEquivOfEq (by rw [hε]))) fun a ↦ by
    have e2 : CompletionProd.quotEquiv hinj hf hrad p.1 (Ideal.Quotient.mk _ (χ p a)) =
        algebraMap R (Tj (𝔪' := 𝔪') p.1) (chart hxy (D p.1) p.2 a) := by
      rw [hχ]
      exact CompletionProd.quotEquiv_algebraMap hinj hf hrad p.1 (algebraMap R R' _)
    rw [RingEquiv.trans_apply]
    change Ideal.quotEquivOfEq _ ((CompletionProd.quotEquiv hinj hf hrad p.1).symm
      (algebraMap R (Tj (𝔪' := 𝔪') p.1) (chart hxy (D p.1) p.2 a))) = _
    rw [← e2, RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]
    rfl

/-- `R̂' ≃ ∏ⱼ R̂'_{𝔪' j}` over `R`. -/
def hatEquivR : FormalPatchLevel.Hat f ≃ₐ[R] ∀ j, Tj (𝔪' := 𝔪') j :=
  AlgEquiv.ofRingEquiv (f := CompletionProd.equiv hinj hf hrad) fun a ↦
    CompletionProd.equiv_algebraMap hinj hf hrad (algebraMap R R' a)

/-- `(∏ⱼ Tⱼ) ⊗_R B ≃ ∏ⱼ Tⱼ ⊗_R B`. -/
def piLeftEquivR : (∀ j, Tj (𝔪' := 𝔪') j) ⊗[R] B ≃ₐ[R] ∀ j, Tj (𝔪' := 𝔪') j ⊗[R] B :=
  (Algebra.TensorProduct.comm R _ B).trans
    ((Algebra.TensorProduct.piRight R R B (Tj (𝔪' := 𝔪'))).trans
      (AlgEquiv.piCongrRight fun j ↦ Algebra.TensorProduct.comm R B (Tj (𝔪' := 𝔪') j)))

omit [IsNoetherianRing R'] [∀ j, (𝔪' j).IsMaximal] in
lemma piLeftEquivR_tmul (t : ∀ j, Tj (𝔪' := 𝔪') j) (b : B) :
    piLeftEquivR (R := R) (B := B) (t ⊗ₜ b) = fun j ↦ t j ⊗ₜ b := rfl

include hχ hε in
/-- **The level formal Kummer form along the nodes** (see the module docstring). -/
def levelEquiv :
    FormalPatchLevel.Hat f ⊗[R] B ≃ₐ[FormalPatchLevel.Hat f]
      ∀ p : (Σ j, Fin (D j).r), AdmissibleLift.N f (χ p) (ε p.1) :=
  AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.congr (hatEquivR (R := R) hinj hf hrad) AlgEquiv.refl).trans
      (piLeftEquivR (R := R) (B := B) (𝔪' := 𝔪'))).toRingEquiv.trans
      ((RingEquiv.piCongrRight fun j ↦ (nodeEquiv hxy (D j) (r j)).toRingEquiv).trans
        ((RingEquiv.piCongrRight fun j ↦ RingEquiv.piCongrRight fun i ↦
          letI := hatAlg (𝔪' := 𝔪' j) hxy (D j) i
          (Algebra.TensorProduct.congr (pieceIso hxy hinj hf hrad D χ hχ ε hε ⟨j, i⟩)
            (knodeEquiv (ϖ ^ (D j).m i) ((D j).d i))).toRingEquiv).trans
          (piCurryRingEquiv _)))) (by
    intro h
    funext p
    obtain ⟨j, i⟩ := p
    letI := fun i ↦ hatAlg (𝔪' := 𝔪' j) hxy (D j) i
    have h1 : (nodeEquiv hxy (D j) (r j)) (hatEquivR (R := R) hinj hf hrad h j ⊗ₜ (1 : B)) =
        algebraMap (Tj (𝔪' := 𝔪') j) _ (hatEquivR (R := R) hinj hf hrad h j) := by
      rw [← (nodeEquiv hxy (D j) (r j)).commutes]
      rfl
    have h2 : (CompletionProd.quotEquiv hinj hf hrad j).symm
        (hatEquivR (R := R) hinj hf hrad h j) =
        Ideal.Quotient.mk _ h := by
      refine (RingEquiv.symm_apply_eq _).mpr ?_
      rw [CompletionProd.quotEquiv_mk]
      rfl
    change (Algebra.TensorProduct.congr (pieceIso hxy hinj hf hrad D χ hχ ε hε ⟨j, i⟩)
      (knodeEquiv _ _)) ((nodeEquiv hxy (D j) (r j))
        (hatEquivR (R := R) hinj hf hrad h j ⊗ₜ (1 : B)) i) = _
    rw [h1]
    change (Algebra.TensorProduct.congr (pieceIso hxy hinj hf hrad D χ hχ ε hε ⟨j, i⟩)
      (knodeEquiv _ _)) (hatEquivR (R := R) hinj hf hrad h j ⊗ₜ (1 : KNode _ _)) = _
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    have h3 : (pieceIso hxy hinj hf hrad D χ hχ ε hε ⟨j, i⟩) (hatEquivR (R := R) hinj hf hrad h j) =
        algebraMap (FormalPatchLevel.Hat f)
          (AdmissibleLift.LPiece f (χ ⟨j, i⟩) (ε j)) h := by
      rw [pieceIso, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, h2]
      exact Ideal.quotEquivOfEq_mk _ h
    refine (congrArg (fun z ↦ z ⊗ₜ[A (ϖ ^ (D j).m i) ((D j).d i)]
      (knodeEquiv (ϖ ^ (D j).m i) ((D j).d i) 1)) h3).trans ?_
    rfl)

end

end FormalLevel

end SemistableReduction
