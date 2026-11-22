/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Faithful

/-!
# The Galois group of a cover acting on its special-fibre datum (MR12, interface I3)

* **`OmegaPair.Hom.instMonoid`**: the endomorphisms of a special-fibre pair form a monoid under
  composition (generic); `mulEquivMrange`: an injective monoid hom is an isomorphism onto its
  range (generic);
* **`TateS6.galHom C : (C.L ≃ₐ[K] C.L) →* Datum.Hom (datum C) (datum C)`**: `datumHom` on the
  Galois group of a tame cover (`datumHom_id`, `datumHom_comp`), **`galHom_injective`**
  (`datumHom_injective`), and **`galEquiv C : Gal(C.L/K) ≃* (galHom C).mrange`**.

The range of `galHom` is described in `TateS6SurjCov` (I3 surjectivity: it contains every
balanced automorphism of the datum).

Statements relating `galHom` and `datumHom` by `rfl` (or through `Units.val`) are avoided:
checking them when the module is written (`lake build`, `lean -o`) does not terminate in
reasonable time (MR12 c50b/c51).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace OmegaPair.Hom

variable {S₀ S₁ : Type u} [CommRing S₀] [CommRing S₁] {a₀ : S₀} {a₁ : S₁}
  {C₀ C₁ : Type u} [CommRing C₀] [CommRing C₁] [Algebra S₀ C₀] [Algebra S₁ C₁]
  {ω : Localization.Away (algebraMap S₀ C₀ a₀) → Localization.Away (algebraMap S₁ C₁ a₁)}

/-- **The endomorphisms of a special-fibre pair form a monoid** under composition. -/
instance instMonoid : Monoid (Hom a₀ a₁ ω ω) where
  mul ψ φ := ψ.comp φ
  one := id a₀ a₁ ω
  mul_assoc χ ψ φ := comp_assoc χ ψ φ
  one_mul := id_comp
  mul_one := comp_id

lemma mul_def (ψ φ : Hom a₀ a₁ ω ω) : ψ * φ = ψ.comp φ := rfl

lemma one_def : (1 : Hom a₀ a₁ ω ω) = id a₀ a₁ ω := rfl

end OmegaPair.Hom

/-- An injective monoid hom is an isomorphism onto its range (for a monoid codomain). -/
noncomputable def mulEquivMrange {G M : Type*} [Monoid G] [Monoid M] (f : G →* M)
    (hf : Function.Injective f) : G ≃* MonoidHom.mrange f :=
  MulEquiv.ofBijective f.mrangeRestrict
    ⟨fun a b h ↦ hf (by simpa only [MonoidHom.coe_mrangeRestrict] using congrArg Subtype.val h),
      MonoidHom.mrangeRestrict_surjective f⟩

lemma mulEquivMrange_apply {G M : Type*} [Monoid G] [Monoid M] (f : G →* M)
    (hf : Function.Injective f) (g : G) : (mulEquivMrange f hf g : M) = f g := rfl

namespace TateS6

open TateTwoChart TateTwoChartNode TateGlue0 TateLevel AdmissibleLift

noncomputable section

section Functor

set_option linter.unusedSectionVars false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  [IsSepClosed k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m] [hsq : Fact (IsSquare (θ b₆))]
  (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
  {hκ : κ * (t ^ 2 - b₆) = 1} (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) (hb₆ : IsUnit b₆)
  {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M') (hM'k : (M' : k) ≠ 0)
  [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
  {K : Type u} [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K]
  [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
  (hK : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) K (toNode b₄ hκ rfl x) =
    algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) K x)
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (RcT (ε * ϖ ^ m) b₄ t κ) K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ M') {ζe : K} (hζe : IsPrimitiveRoot ζe e)
  (τ : TateGlue1.Rb b₄ b₆ ϖ m ε)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 (ε * ϖ ^ m) b₄ t κ) (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) (h0 (ε * ϖ ^ m) b₄ t
        κ))))

set_option hygiene false in
/-- The chart instances of a Tate cover `C`, stated over the concrete Tate charts. -/
local macro "cov_inst " C:term : tactic => `(tactic| (
  letI : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).algT1
  haveI : IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K ($C).L := ($C).towT1
  letI : Algebra (T0 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).algT0
  haveI : IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).towT0
  letI : Algebra (T01 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).algT01
  haveI : IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) (T01 (ε * ϖ ^ m) b₄ t κ) ($C).L :=
    Cov.towT01 $C
  letI : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) ($C).B₁ := ($C).algB₁
  haveI : IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) ($C).B₁ ($C).L := ($C).towB₁
  haveI : IsIntegralClosure ($C).B₁ (T1 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).intB₁
  haveI : IsLocalization.Away (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) ($C).B₁
    (DT (ε * ϖ ^ m) b₄ t κ)) ($C).Bn := ($C).locBn
  letI : Algebra (T0 (ε * ϖ ^ m) b₄ t κ) ($C).B₀ := ($C).algB₀
  haveI : IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) ($C).B₀ ($C).L := ($C).towB₀
  haveI : IsIntegralClosure ($C).B₀ (T0 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).intB₀
  haveI : IsLocalization.Away (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) ($C).B₀
    (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ)) ($C).Bc := ($C).locBc))

set_option hygiene false in
/-- `datumHom` with the fixed Tate data of this section. -/
local notation "𝔥" f:max => datumHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ f

set_option hygiene false in
/-- The datum of a cover, with the fixed Tate data of this section. -/
local notation "𝔇" C:max => datum hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C

/-- **The Galois group of a tame cover acting on its special-fibre datum**: `σ ↦ datumHom σ`. -/
def galHom (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) : (C.L ≃ₐ[K] C.L) →* Datum.Hom (𝔇 C) (𝔇 C) where
  toFun σ := 𝔥 (σ : C.L →ₐ[K] C.L)
  map_one' := datumHom_id hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C
  map_mul' σ σ' :=
    datumHom_comp hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀
      (σ' : C.L →ₐ[K] C.L) (σ : C.L →ₐ[K] C.L)

/-- **`galHom` is injective** (`datumHom_injective`). -/
theorem galHom_injective (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) :
    Function.Injective (galHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C) :=
  fun _ _ h ↦ AlgEquiv.coe_toAlgHom_injective
    (datumHom_injective hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ h)


/-- **The Galois group of a tame cover is isomorphic to the image of `galHom`** in the
endomorphisms of its special-fibre datum (`galHom_injective`). -/
def galEquiv (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) :
    (C.L ≃ₐ[K] C.L) ≃* MonoidHom.mrange
      (galHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C) :=
  mulEquivMrange _ (galHom_injective hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C)

end Functor

end

end TateS6

end SemistableReduction
