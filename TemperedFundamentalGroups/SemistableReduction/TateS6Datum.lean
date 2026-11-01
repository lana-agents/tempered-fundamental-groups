/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Cov
import TemperedFundamentalGroups.SemistableReduction.OmegaPairHom

/-!
# The special-fibre datum of a tame cover of the Tate curve as a functor (MR12, interface I2)

**`TateS6.Datum`** is the triple that `TateS5.liftCusp` takes: a covering `Sp` of the special
fibre over `V₁` (`TateGlue1.Special1`, with its node covering `cov₀`), a covering `Sc` over the
cusp chart (`CuspTower.CuspSpecial`) and the overlap identification
`ω : Sc.C0[1/h̄] ≃ Sp.C1[1/h̄']` (`TateGlue0.OmegaC`). It is the Tate instance (an `abbrev`) of the
generic bundle `TateS6.DatumData`: a `structure` with fields over the concrete Tate charts does not
elaborate (rule 17, MR12 c43).

**`TateS6.Datum.Hom D D'`** (`OmegaPair.Hom`): algebra maps `f₁ : D.Sp.C1 → D'.Sp.C1` over
`T1/J`, `f₀ : D.Sc.C0 → D'.Sc.C0` over `T0/J` commuting with the overlap identifications; no
condition on the chosen Kummer data. `Datum.Hom.id`, `Datum.Hom.comp`.

**The functor on covers.** For a tame cover `C : TateS6.Cov …`, **`TateS6.datum C`**
`= ⟨cov C, sp C, sc C, om C⟩` (the data of `TateS5`), and for a `K`-algebra map
`f : C.L → C'.L`, **`TateS6.datumHom f`**: the reductions modulo `J` of the maps
`(chartMap f).f1 : C.B₁ → C'.B₁`, `(chartMap f).f0 : C.B₀ → C'.B₀` of normalisations (I1),
compatible with `om` by `TateGlue0.omegaNorm_natural`. **`datumHom_id`**, **`datumHom_comp`**,
and `datumHom_f₁`, `datumHom_f₀` (the reductions of `CovData.map1 f`, `CovData.map0 f`).
-/

universe u

open Module Polynomial

namespace SemistableReduction

namespace TateS6

open TateTwoChart TateTwoChartNode TateGlue0 TateLevel AdmissibleLift

noncomputable section

/-- **The generic bundle of a special-fibre datum**: a node covering `cov₀`, a covering `Sp`
over `V₁` restricting to it, a covering `Sc` over the cusp chart and an overlap datum `ω`. -/
structure DatumData (Cov0 : Type (u + 1)) (Sp1 : Cov0 → Type (u + 1)) (ScT : Type (u + 1))
    (Om : ∀ c, Sp1 c → ScT → Type u) where
  /-- the admissible covering of the node chart -/
  cov₀ : Cov0
  /-- the covering of the special fibre over `V₁` -/
  Sp : Sp1 cov₀
  /-- the covering of the special fibre over the cusp chart -/
  Sc : ScT
  /-- the overlap identification -/
  ω : Om cov₀ Sp Sc

section Datum

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  [Fact (Function.Surjective θ)] (ϖ b₄ b₆ t κ ε : O) (m : ℕ) (hκ : κ * (t ^ 2 - b₆) = 1)
  (hπe : θ (ϖ ^ m) = 0) (τ : TateGlue1.Rb b₄ b₆ ϖ m ε)

/-- **I2: the special-fibre datum** of a covering of the Tate curve (the input of
`TateS5.liftCusp`). -/
abbrev Datum : Type (u + 1) :=
  DatumData (Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ))
    (fun cov₀ ↦ TateGlue1.Special1 hκ rfl hπe τ cov₀)
    (CuspTower.CuspSpecial (T0 (ε * ϖ ^ m) b₄ t κ) (c0 (ε * ϖ ^ m) b₄ t κ)
      (h0 (ε * ϖ ^ m) b₄ t κ) (θ := θ))
    (fun _ Sp Sc ↦ OmegaC hκ rfl Sp Sc.C0)

variable {θ ϖ b₄ b₆ t κ ε m hκ hπe τ}

/-- **I2: morphisms of special-fibre data**: algebra maps of the coverings over `V₁` and over
the cusp chart commuting with the overlap identifications. -/
abbrev Datum.Hom (D D' : Datum θ ϖ b₄ b₆ t κ ε m hκ hπe τ) : Type u :=
  OmegaPair.Hom (Ideal.Quotient.mk (J θ (R := T0 (ε * ϖ ^ m) b₄ t κ)) (h0 (ε * ϖ ^ m) b₄ t κ))
    (Ideal.Quotient.mk (J θ (R := T1 (ε * ϖ ^ m) b₄ t κ)) (h1 (ε * ϖ ^ m) b₄ t κ)) ⇑D.ω ⇑D'.ω

/-- The identity morphism of a special-fibre datum. -/
abbrev Datum.Hom.id (D : Datum θ ϖ b₄ b₆ t κ ε m hκ hπe τ) : D.Hom D :=
  OmegaPair.Hom.id _ _ _

/-- Composition of morphisms of special-fibre data. -/
abbrev Datum.Hom.comp {D D' D'' : Datum θ ϖ b₄ b₆ t κ ε m hκ hπe τ} (ψ : D'.Hom D'')
    (φ : D.Hom D') : D.Hom D'' :=
  OmegaPair.Hom.comp ψ φ

end Datum

namespace CovData

variable {A : Type u} [CommRing A] {K : Type u} [Field K] {D : ProjectiveLine.TwoChartRings A}
  {Rn Rc : Type u} [CommRing Rn] [CommRing Rc] [Algebra D.R1 K] [Algebra Rn K] [Algebra Rc K]
  [Algebra D.R0 Rc] {toN : D.R1 → Rn} {dT : D.R1} {c0 : D.R0} {ϖ1 : D.R1} {ϖ0 : D.R0}
  {I0 : Ideal D.R0} {q e : ℕ} {C C' : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e}

/-- A `K`-algebra map of covers is compatible with the maps from `D.R0`. -/
lemma map_algebraMap_R0 (f : C.L →ₐ[K] C'.L) (a : D.R0) :
    f (algebraMap D.R0 C.L a) = algebraMap D.R0 C'.L a := by
  rw [← C.hρ, ← C'.hρ, map_algebraMap_R01]

/-- The ring map `C.B₀ → C'.B₀` of normalisations induced by `f` (`(chartMap f).f0`). -/
def map0 (f : C.L →ₐ[K] C'.L) : C.B₀ →+* C'.B₀ := (chartMap f).f0.toRingHom

/-- The ring map `C.B₁ → C'.B₁` of normalisations induced by `f` (`(chartMap f).f1`). -/
def map1 (f : C.L →ₐ[K] C'.L) : C.B₁ →+* C'.B₁ := (chartMap f).f1.toRingHom

lemma map0_eq (f : C.L →ₐ[K] C'.L) (b : C.B₀) : map0 f b = (chartMap f).f0 b := rfl

lemma map1_eq (f : C.L →ₐ[K] C'.L) (b : C.B₁) : map1 f b = (chartMap f).f1 b := rfl

/-- Generic-fibre compatibility of `map0`. -/
lemma algebraMap_map0 (f : C.L →ₐ[K] C'.L) (b : C.B₀) :
    algebraMap C'.B₀ C'.L (map0 f b) = f (algebraMap C.B₀ C.L b) :=
  chartMap_f0_algebraMap f b

/-- Generic-fibre compatibility of `map1`. -/
lemma algebraMap_map1 (f : C.L →ₐ[K] C'.L) (b : C.B₁) :
    algebraMap C'.B₁ C'.L (map1 f b) = f (algebraMap C.B₁ C.L b) :=
  chartMap_f1_algebraMap f b

/-- `map0 f` is a map over `D.R0`. -/
lemma map0_algebraMap (f : C.L →ₐ[K] C'.L) (a : D.R0) :
    map0 f (algebraMap D.R0 C.B₀ a) = algebraMap D.R0 C'.B₀ a :=
  IsIntegralClosure.algebraMap_injective C'.B₀ D.R0 C'.L (by
    rw [algebraMap_map0, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, map_algebraMap_R0])

/-- `map1 f` is a map over `D.R1`. -/
lemma map1_algebraMap (f : C.L →ₐ[K] C'.L) (a : D.R1) :
    map1 f (algebraMap D.R1 C.B₁ a) = algebraMap D.R1 C'.B₁ a :=
  IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L (by
    rw [algebraMap_map1, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, map_algebraMap_R1])

lemma map0_id (b : C.B₀) : map0 (AlgHom.id K C.L) b = b :=
  IsIntegralClosure.algebraMap_injective C.B₀ D.R0 C.L (algebraMap_map0 _ b)

lemma map1_id (b : C.B₁) : map1 (AlgHom.id K C.L) b = b :=
  IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L (algebraMap_map1 _ b)

lemma map0_comp {C'' : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e} (f : C.L →ₐ[K] C'.L)
    (g : C'.L →ₐ[K] C''.L) (b : C.B₀) : map0 (g.comp f) b = map0 g (map0 f b) :=
  IsIntegralClosure.algebraMap_injective C''.B₀ D.R0 C''.L (by
    rw [algebraMap_map0, algebraMap_map0, algebraMap_map0, AlgHom.comp_apply])

lemma map1_comp {C'' : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e} (f : C.L →ₐ[K] C'.L)
    (g : C'.L →ₐ[K] C''.L) (b : C.B₁) : map1 (g.comp f) b = map1 g (map1 f b) :=
  IsIntegralClosure.algebraMap_injective C''.B₁ D.R1 C''.L (by
    rw [algebraMap_map1, algebraMap_map1, algebraMap_map1, AlgHom.comp_apply])

end CovData

section Functor

set_option linter.unusedSectionVars false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  [IsAlgClosed k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m]
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

/-- **I2: the special-fibre datum of a tame cover** `C` (`TateS5.cov`, `sp`, `sc`, `om`). -/
def datum (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) :
    Datum θ ϖ b₄ b₆ t κ ε m hκ (TateS5.θ_pow hker) τ := by
  cov_inst C
  exact ⟨TateS5.cov hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ C.hL C.hBn C.hunr₁ τ,
    TateS5.sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ C.hL C.hBn C.hunr₁ τ,
    TateS5.sc hϖ hker hκ hε h3 hE hb₆ he hζe C.hd C.hBc C.hunr₀ φ₀,
    TateS5.om hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe C.hL C.hd C.hρ C.hBn C.hBc
      C.hunr₁ C.hunr₀ τ φ₀⟩

set_option hygiene false in
/-- The datum of a cover, with the fixed Tate data of this section. -/
local notation "𝔇" C:max => datum hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C

/-- **I2: the morphism of special-fibre data induced by a `K`-algebra map of covers**: the
reductions modulo `J` of the maps of normalisations `(chartMap f).f1`, `(chartMap f).f0`. -/
def datumHom {C C' : Cov ϖ b₄ b₆ t κ ε m hκ q e K} (f : C.L →ₐ[K] C'.L) :
    Datum.Hom (𝔇 C) (𝔇 C') := by
  cov_inst C
  cov_inst C'
  exact
  { f₁ := OmegaPair.csMap (J θ (R := T1 (ε * ϖ ^ m) b₄ t κ)) (CovData.map1 f)
      (CovData.map1_algebraMap f)
    f₀ := OmegaPair.csMap (J θ (R := T0 (ε * ϖ ^ m) b₄ t κ)) (CovData.map0 f)
      (CovData.map0_algebraMap f)
    hω := fun c ↦ omegaNormC_natural θ C.hρ (TateS5.h0_ne_zero C.hρ) TateS5.h1_ne_zero C'.hρ
        (TateS5.h0_ne_zero C'.hρ) TateS5.h1_ne_zero (f : C.L →+* C'.L)
        (CovData.map_algebraMap_R1 f) (CovData.map0 f) (CovData.map0_algebraMap f)
        (CovData.algebraMap_map0 f) (CovData.map1 f) (CovData.map1_algebraMap f)
        (CovData.algebraMap_map1 f) hκ rfl (𝔇 C).Sp (𝔇 C').Sp AlgEquiv.refl AlgEquiv.refl
        (OmegaPair.csMap (J θ (R := T1 (ε * ϖ ^ m) b₄ t κ)) (CovData.map1 f)
          (CovData.map1_algebraMap f)) (fun _ ↦ rfl) c }

set_option hygiene false in
/-- `datumHom` with the fixed Tate data of this section. -/
local notation "𝔥" f:max => datumHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ f

/-- `datumHom f` on the residues of `B₁`. -/
lemma datumHom_f₁ {C C' : Cov ϖ b₄ b₆ t κ ε m hκ q e K} (f : C.L →ₐ[K] C'.L) :
    (𝔥 f).f₁ = OmegaPair.csMap (J θ (R := (twoChart (ε * ϖ ^ m) b₄ t κ).R1)) (CovData.map1 f)
      (CovData.map1_algebraMap f) :=
  rfl

/-- `datumHom f` on the residues of `B₀`. -/
lemma datumHom_f₀ {C C' : Cov ϖ b₄ b₆ t κ ε m hκ q e K} (f : C.L →ₐ[K] C'.L) :
    (𝔥 f).f₀ = OmegaPair.csMap (J θ (R := (twoChart (ε * ϖ ^ m) b₄ t κ).R0)) (CovData.map0 f)
      (CovData.map0_algebraMap f) :=
  rfl

/-- **`datumHom` of the identity.** -/
theorem datumHom_id (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) :
    (𝔥 (AlgHom.id K C.L)) = Datum.Hom.id (𝔇 C) :=
  OmegaPair.Hom.ext
    (OmegaPair.csMap_eq_id (J θ (R := (twoChart (ε * ϖ ^ m) b₄ t κ).R1)) (CovData.map1 _)
      (CovData.map1_algebraMap _) CovData.map1_id)
    (OmegaPair.csMap_eq_id (J θ (R := (twoChart (ε * ϖ ^ m) b₄ t κ).R0)) (CovData.map0 _)
      (CovData.map0_algebraMap _) CovData.map0_id)

/-- **`datumHom` of a composition.** -/
theorem datumHom_comp {C C' C'' : Cov ϖ b₄ b₆ t κ ε m hκ q e K} (f : C.L →ₐ[K] C'.L)
    (g : C'.L →ₐ[K] C''.L) : (𝔥 (g.comp f)) = Datum.Hom.comp (𝔥 g) (𝔥 f) :=
  OmegaPair.Hom.ext
    (OmegaPair.csMap_eq_comp (J θ (R := (twoChart (ε * ϖ ^ m) b₄ t κ).R1)) (CovData.map1 f)
      (CovData.map1_algebraMap f) (CovData.map1 g) (CovData.map1_algebraMap g)
      (CovData.map1 (g.comp f)) (CovData.map1_algebraMap _) (CovData.map1_comp f g))
    (OmegaPair.csMap_eq_comp (J θ (R := (twoChart (ε * ϖ ^ m) b₄ t κ).R0)) (CovData.map0 f)
      (CovData.map0_algebraMap f) (CovData.map0 g) (CovData.map0_algebraMap g)
      (CovData.map0 (g.comp f)) (CovData.map0_algebraMap _) (CovData.map0_comp f g))

end Functor

end

end TateS6

end SemistableReduction
