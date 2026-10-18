/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelModel

/-!
# The level step with a free target element (Blueprint §12.8, M2.3 (e'), tower)

In a tower of charts `R_{n+1} → R_n` the elements `f_n` cutting out the nodes satisfy
`q(f_{n+1}) = f_n` only propositionally in general, while `LevelStep.stepEquiv` is stated for the
target element `f' f = q f`. This file restates the step for any `f₂` with `hf : q f = f₂`
(proofs by `subst`):

* `LevelStep.ψ₂`: the completion map `R̂ → R'^∧` along `f₂`, `ψ₂_algebraMap`;
* **`LevelStep.stepEquiv₂`**: `R' ⊗_R G ≃ₐ[R'] G'` for the patched algebras at `f` and `f₂`;
* `LevelStep.ker_includeRight`: for `q : R → R'` surjective, `G → R' ⊗_R G` is surjective with
  kernel `(ker q) G` (Mathlib `Algebra.TensorProduct.rTensor_ker`);
* **`LevelStep.trans₂`**: the transition map `G → G'`, surjective (`surjective_trans₂`) with
  kernel `(ker q) G` (`ker_trans₂`), and `trans₂_algebraMap`.
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

namespace LevelStep

noncomputable section

/-! ### The transition out of a base change along a surjection (generic) -/

section Generic

variable {R R' G : Type u} [CommRing R] [CommRing R'] [CommRing G] [Algebra R R'] [Algebra R G]

/-- **The kernel of `G → R' ⊗_R G`** is `(ker q) G` for `q : R → R'` surjective. -/
theorem ker_includeRight (hq : Function.Surjective (algebraMap R R')) :
    RingHom.ker (Algebra.TensorProduct.includeRight : G →ₐ[R] R' ⊗[R] G) =
      (RingHom.ker (algebraMap R R')).map (algebraMap R G) := by
  have hker := Algebra.TensorProduct.rTensor_ker (R := R) (S := R) (C := G) (Algebra.ofId R R') hq
  have hmap : ((RingHom.ker (Algebra.ofId R R')).map
      (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] G)).map
        (Algebra.TensorProduct.lid R G) = (RingHom.ker (algebraMap R R')).map (algebraMap R G) := by
    rw [← Ideal.map_coe (Algebra.TensorProduct.lid R G), ← Ideal.map_coe
      (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] G), Ideal.map_map]
    congr 1
    refine RingHom.ext fun r ↦ ?_
    simp [Algebra.algebraMap_eq_smul_one]
  ext g
  have h1 : (Algebra.TensorProduct.includeRight : G →ₐ[R] R' ⊗[R] G) g =
      Algebra.TensorProduct.map (Algebra.ofId R R') (AlgHom.id R G) ((1 : R) ⊗ₜ g) := by
    simp
  rw [RingHom.mem_ker, h1, ← RingHom.mem_ker, hker, ← hmap, Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, by simp⟩
  · rintro ⟨x, hx, hxg⟩
    have : x = (1 : R) ⊗ₜ g := (Algebra.TensorProduct.lid R G).injective (by
      rw [hxg, Algebra.TensorProduct.lid_tmul, one_smul])
    rwa [← this]

end Generic

/-- The patched algebra of an admissible covering at one level (notation). -/
abbrev patchOf {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
    {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
    {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
    (hθ : Function.Surjective θ) (cov₀ : Admissible.Covering φ₀ ψ₀) {πL : cov₀.ι → O}
    {S : Type u} [CommRing S] [Algebra O S] [Algebra k (S ⧸ J θ (R := S))]
    [IsNoetherianRing S] (g : S) {e : R₀ ≃ₐ[k] (S ⧸ J θ (R := S))} (h : e f₀ = fbar θ g)
    (L : KummerLift (cov₀.transport (h := h)) πL) (M : CuspLift (cov₀.transport (h := h)))
    {m : ℕ} (hJ : J θ (R := S) ^ m = ⊥)
    {Q : Type u} [CommRing Q] [Algebra S Q] [Algebra.FormallyEtale S Q]
    (σ : (Q ⧸ (J θ).map (algebraMap S Q)) ≃ₐ[S]
      Localization.Away (algebraMap S (cov₀.transport (h := h)).C g)) : Type u :=
  FormalPatchLevel.patch g (J θ) hJ (FormalPatchLevel.alphaOfEquiv g (J θ)
    (FormalPatchLevel.specialFibreEquiv g (J θ) σ (kappaF L M hθ)))

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {R' : Type u} [CommRing R'] [Algebra O R']
  [Algebra R R'] (f : R) (f₂ : R') (hf : f' (R' := R') f = f₂)

/-- The completion map `R̂ → R'^∧` along `f₂ = q f`. -/
def ψ₂ : FormalPatchLevel.Hat f →ₐ[R] FormalPatchLevel.Hat f₂ := by
  subst hf
  exact KummerReduce.ψI f

lemma ψ₂_rfl : ψ₂ f (f' (R' := R') f) rfl = KummerReduce.ψI f := rfl

lemma ψ₂_algebraMap (r : R) :
    ψ₂ f f₂ hf (algebraMap R (FormalPatchLevel.Hat f) r) =
      algebraMap R' (FormalPatchLevel.Hat f₂) (algebraMap R R' r) := by
  subst hf
  rw [ψ₂_rfl, AlgHom.commutes, IsScalarTower.algebraMap_apply R R'
    (FormalPatchLevel.Hat (f' (R' := R') f))]

variable [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {e₁ : R₀ ≃ₐ[k] (R ⧸ J θ (R := R))} {e₂ : R₀ ≃ₐ[k] (R' ⧸ J θ (R := R'))}
  (h₁ : e₁ f₀ = fbar θ f) (h₂ : e₂ f₀ = fbar θ f₂)
  (he : ∀ r : R, e₂ (e₁.symm (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (algebraMap R R' r))
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  [IsNoetherianRing R] [IsNoetherianRing R'] [IsScalarTower O R R']
  (hq : Function.Surjective (algebraMap R R'))
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (cov₀ : Admissible.Covering φ₀ ψ₀)
  {πL : cov₀.ι → O} (L : KummerLift (cov₀.transport (h := h₁)) πL)
  (M : CuspLift (cov₀.transport (h := h₁)))
  (L' : KummerLift (cov₀.transport (h := h₂)) πL) (M' : CuspLift (cov₀.transport (h := h₂)))
  (hχχ : ∀ j a, ψ₂ f f₂ hf (L.χ j a) = L'.χ j a)
  (hεε : ∀ j, ψ₂ f f₂ hf (L.ε j) = L'.ε j)
  (hδδ : ∀ i, ψ₂ f f₂ hf (M.δ i) = M'.δ i) (htt : ψ₂ f f₂ hf M.t = M'.t)
  {n n' : ℕ} (hJ : J θ (R := R) ^ n = ⊥) (hJ' : J θ (R := R') ^ n' = ⊥)
  {I₁ I₂ : Ideal O} (hflat : ∀ j, KummerFactorQuot.KFlat I₁ (L.χ j).toRingHom)
  (hidem : ∀ j, IsIdempotentElem (L.ε j))
  (hfχ : ∀ j, L.χ j (fA (πL j)) = algebraMap R (FormalPatchLevel.Hat f) f)
  (hcidem : ∀ i, IsIdempotentElem (M.δ i))
  (hreg : ∀ y : FormalPatchLevel.Hat f, algebraMap R _ f * y = 0 → y = 0)
  (hflat' : ∀ j, KummerFactorQuot.KFlat I₂ (L'.χ j).toRingHom)
  (hidem' : ∀ j, IsIdempotentElem (L'.ε j))
  (hfχ' : ∀ j, L'.χ j (fA (πL j)) = algebraMap R' (FormalPatchLevel.Hat f₂) f₂)
  (hcidem' : ∀ i, IsIdempotentElem (M'.δ i))
  (hreg' : ∀ y : FormalPatchLevel.Hat f₂, algebraMap R' _ f₂ * y = 0 → y = 0)
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  {P' : Type u} [CommRing P'] [Algebra R' P'] [Algebra.FormallyEtale R' P'] [Algebra R P']
  [IsScalarTower R R' P']
  (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R]
    Localization.Away (algebraMap R (cov₀.transport (h := h₁)).C f))
  (σP' : (P' ⧸ (J θ).map (algebraMap R' P')) ≃ₐ[R']
    Localization.Away (algebraMap R' (cov₀.transport (h := h₂)).C f₂))
  (hfP : IsUnit (algebraMap R P f)) (hfP' : IsUnit (algebraMap R' P' f₂))

include hf he hq hO hχχ hεε hδδ htt hflat hidem hfχ hcidem hreg hflat' hidem' hfχ' hcidem' hreg'
  hfP hfP' in
/-- **The level step with a free target element**: `R' ⊗_R G ≃ₐ[R'] G'` for the patched
algebras at `f` and `f₂ = q f`. -/
def stepEquiv₂ :
    R' ⊗[R] patchOf hθ cov₀ f h₁ L M hJ σP ≃ₐ[R'] patchOf hθ cov₀ f₂ h₂ L' M' hJ' σP' := by
  subst hf
  exact stepEquiv f h₁ he hq hθ hO cov₀ L M L' M' hχχ hεε hδδ htt hJ hJ' hflat hidem hfχ hcidem
    hreg hflat' hidem' hfχ' hcidem' hreg' σP σP' hfP hfP'

/-- **The transition map** `G → G'` of the tower. -/
def trans₂ : patchOf hθ cov₀ f h₁ L M hJ σP →+* patchOf hθ cov₀ f₂ h₂ L' M' hJ' σP' :=
  (stepEquiv₂ f f₂ hf h₁ h₂ he hq hθ hO cov₀ L M L' M' hχχ hεε hδδ htt hJ hJ' hflat hidem hfχ
    hcidem hreg hflat' hidem' hfχ' hcidem' hreg' σP σP' hfP hfP').toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight : _ →ₐ[R] R' ⊗[R] _).toRingHom

/-- The transition map is surjective. -/
theorem surjective_trans₂ :
    Function.Surjective (trans₂ f f₂ hf h₁ h₂ he hq hθ hO cov₀ L M L' M' hχχ hεε hδδ htt hJ hJ'
      hflat hidem hfχ hcidem hreg hflat' hidem' hfχ' hcidem' hreg' σP σP' hfP hfP') :=
  (stepEquiv₂ f f₂ hf h₁ h₂ he hq hθ hO cov₀ L M L' M' hχχ hεε hδδ htt hJ hJ' hflat hidem hfχ
    hcidem hreg hflat' hidem' hfχ' hcidem' hreg' σP σP' hfP hfP').surjective.comp
    (Algebra.TensorProduct.includeRight_surjective _ hq)

/-- **The kernel of the transition map** is `(ker q) G`. -/
theorem ker_trans₂ :
    RingHom.ker (trans₂ f f₂ hf h₁ h₂ he hq hθ hO cov₀ L M L' M' hχχ hεε hδδ htt hJ hJ'
      hflat hidem hfχ hcidem hreg hflat' hidem' hfχ' hcidem' hreg' σP σP' hfP hfP') =
      (RingHom.ker (algebraMap R R')).map (algebraMap R (patchOf hθ cov₀ f h₁ L M hJ σP)) := by
  ext g
  rw [RingHom.mem_ker, trans₂, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, map_eq_zero_iff _ (RingEquiv.injective _), ← RingHom.mem_ker]
  exact SetLike.ext_iff.mp (ker_includeRight hq) g

/-- The transition map is semilinear over `q`. -/
theorem trans₂_algebraMap (r : R) :
    trans₂ f f₂ hf h₁ h₂ he hq hθ hO cov₀ L M L' M' hχχ hεε hδδ htt hJ hJ'
      hflat hidem hfχ hcidem hreg hflat' hidem' hfχ' hcidem' hreg' σP σP' hfP hfP'
        (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) := by
  rw [trans₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, ← Algebra.TensorProduct.tmul_one_eq_one_tmul,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
  exact AlgEquiv.commutes _ _

end

end LevelStep

end SemistableReduction
