/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNormalisationChart
import TemperedFundamentalGroups.SemistableReduction.TwoChartNormMap

/-!
# Tame covers of the Tate curve as a category, acting on their normalisations
(MR12, interfaces I0 and I1 of MR13)

**I0.** `TateS6.Cov` (the Tate instance of the generic `TateS6.CovData` over two-chart
rings `D`, here `D = TateTwoChart.twoChart (ε ϖᵐ) b₄ t κ`) bundles the per-cover data of
`TateS5`/`TateS6Lift` (the field `L`, finite Galois over the function field `K`, with its algebra
structures over the charts `T0`, `T1`, `T01`, `NR`, `Rc`, the normalisations `B₀`, `B₁`, their
localizations `Bn`, `Bc`, and the hypotheses `hρ`, `hBn`, `hBc`, `hL`, `hd`, `hunr₀`, `hunr₁`)
over the fixed Tate data; `C.P = TwoChartNorm.twoChart C.B₀ C.B₁ C.hρ C.h1L` (definitionally
`twoChartL C.L C.hρ C.B₀ C.B₁` with the instances of `C` and the tower `Cov.towT01`) is the
normalisation `P_L` of the Tate model in `C.L`.

The structure is stated over abstract two-chart rings `D` (and abstract node and cusp charts):
fields over the concrete chart types `T0 …`, `T1 …` do not elaborate (the structure command and
instance search reduce the defining polynomials when comparing `T0 …` with `T1 …`). Over
`D = twoChart …` the chart instances have types `Algebra D.R0 C.L` etc., which are defeq to
`Algebra (T0 …) C.L`.

**I1.** A `K`-algebra map `f : C.L → C'.L` induces a morphism of two-chart rings
`C.P → C'.P` (**`TateS6.Cov.chartMap`**, from `TwoChartNorm.normMap`), hence of chart algebras
(**`chartHom`**, **`isHom_chartHom`**), compatible with the generic fibres
(**`chartMap_f0_algebraMap`**, **`chartMap_f1_algebraMap`**), the structure maps from the Tate
model (**`chartMap_comp_toNorm`**), identities and composition (**`chartMap_id`**,
**`chartMap_comp`**). In particular `Gal(C.L / K)` acts on `C.P`
(**`TateS6.Cov.galAct`**, a monoid map into the endomorphisms of `C.P`, and
**`galActUnits`** into its automorphisms).
-/

universe u

open Module Polynomial

namespace SemistableReduction

namespace TateS6

open TateTwoChart TateTwoChartNode TateGlue0

noncomputable section

section Generic

variable {A : Type u} [CommRing A] (K : Type u) [Field K] (D : ProjectiveLine.TwoChartRings A)
  (Rn Rc : Type u) [CommRing Rn] [CommRing Rc] [Algebra D.R1 K] [Algebra Rn K] [Algebra Rc K]
  [Algebra D.R0 Rc] (toN : D.R1 → Rn) (dT : D.R1) (c0 : D.R0) (ϖ1 : D.R1) (ϖ0 : D.R0)
  (I0 : Ideal D.R0) (q e : ℕ)

/-- **The per-cover data of `TateS5`, over abstract two-chart rings `D`** (node chart `Rn`, cusp
chart `Rc`; the Tate instance is `TateS6.Cov`). -/
structure CovData where
  /-- the function field of the cover -/
  L : Type u
  [field : Field L]
  [algK : Algebra K L]
  [fin : FiniteDimensional K L]
  [gal : IsGalois K L]
  [algT1 : Algebra D.R1 L]
  [towT1 : IsScalarTower D.R1 K L]
  [algNR : Algebra Rn L]
  [towNR : IsScalarTower Rn K L]
  [algRc : Algebra Rc L]
  [towRc : IsScalarTower Rc K L]
  [algT0 : Algebra D.R0 L]
  [towT0 : IsScalarTower D.R0 Rc L]
  [algT01 : Algebra D.R01 L]
  hρ : ∀ x, algebraMap D.R01 L (D.ρ0 x) = algebraMap D.R0 L x
  h1L : ∀ x, algebraMap D.R01 L (D.ρ1 x) = algebraMap D.R1 L x
  hL : (finrank K L).Coprime q
  hd : finrank K L ∣ e
  /-- the normalisation of `T1` in `L` -/
  B₁ : Type u
  [ringB₁ : CommRing B₁]
  [algB₁ : Algebra D.R1 B₁]
  [algB₁L : Algebra B₁ L]
  [towB₁ : IsScalarTower D.R1 B₁ L]
  [intB₁ : IsIntegralClosure B₁ D.R1 L]
  /-- the node chart of the normalisation, `B₁[1/D]` -/
  Bn : Type u
  [ringBn : CommRing Bn]
  [algBn : Algebra Rn Bn]
  [algBnL : Algebra Bn L]
  [towBn : IsScalarTower Rn Bn L]
  [algB₁Bn : Algebra B₁ Bn]
  [towB₁Bn : IsScalarTower B₁ Bn L]
  [locBn : IsLocalization.Away (algebraMap D.R1 B₁ dT) Bn]
  hBn : ∀ x, algebraMap Rn Bn (toN x) = algebraMap B₁ Bn (algebraMap D.R1 B₁ x)
  /-- the normalisation of `T0` in `L` -/
  B₀ : Type u
  [ringB₀ : CommRing B₀]
  [algB₀ : Algebra D.R0 B₀]
  [algB₀L : Algebra B₀ L]
  [towB₀ : IsScalarTower D.R0 B₀ L]
  [intB₀ : IsIntegralClosure B₀ D.R0 L]
  /-- the cusp chart of the normalisation, `B₀[1/(1 + h)]` -/
  Bc : Type u
  [ringBc : CommRing Bc]
  [algBc : Algebra Rc Bc]
  [algBcL : Algebra Bc L]
  [towBc : IsScalarTower Rc Bc L]
  [algB₀Bc : Algebra B₀ Bc]
  [towB₀Bc : IsScalarTower B₀ Bc L]
  [locBc : IsLocalization.Away (algebraMap D.R0 B₀ c0) Bc]
  hBc : ∀ x, algebraMap Rc Bc (algebraMap D.R0 Rc x) = algebraMap B₀ Bc (algebraMap D.R0 B₀ x)
  hunr₁ : ∀ (P : Ideal D.R1) [P.IsMaximal], ϖ1 ∈ P → ∀ (Q : Ideal B₁) [Q.IsPrime],
    Q.comap (algebraMap D.R1 B₁) < P → Algebra.IsUnramifiedAt D.R1 Q
  hunr₀ : ∀ (P : Ideal D.R0) [P.IsMaximal], ϖ0 ∈ P → ∀ (Q : Ideal B₀) [Q.IsPrime],
    Q.comap (algebraMap D.R0 B₀) < P → Q.comap (algebraMap D.R0 B₀) ≠ I0 →
      Algebra.IsUnramifiedAt D.R0 Q

namespace CovData

attribute [instance] field algK fin gal algT1 towT1 algNR towNR algRc towRc algT0 algT01
  ringB₁ algB₁ algB₁L towB₁ intB₁ ringBn algBn algBnL towBn algB₁Bn towB₁Bn locBn ringB₀
  algB₀ algB₀L towB₀ intB₀ ringBc algBc algBcL towBc algB₀Bc towB₀Bc locBc

variable {K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e}

/-- **The normalisation `P_L` of `D` in the cover**, as two-chart rings. -/
abbrev P (C : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e) : ProjectiveLine.TwoChartRings A :=
  TwoChartNorm.twoChart C.B₀ C.B₁ C.hρ C.h1L

/-- The structure map from `D` to `C.P`. -/
abbrev toNorm (C : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e) : TwoChartMap D C.P :=
  TwoChartNorm.toNorm C.B₀ C.B₁ C.hρ C.h1L

variable {C C' C'' : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e}

/-- A `K`-algebra map of covers is compatible with the maps from `D.R1`. -/
lemma map_algebraMap_R1 (f : C.L →ₐ[K] C'.L) (a : D.R1) :
    f (algebraMap D.R1 C.L a) = algebraMap D.R1 C'.L a := by
  rw [IsScalarTower.algebraMap_apply D.R1 K C.L, f.commutes, ← IsScalarTower.algebraMap_apply]

/-- A `K`-algebra map of covers is compatible with the maps from the overlap `D.R01`
(a localization of `D.R1`). -/
lemma map_algebraMap_R01 (f : C.L →ₐ[K] C'.L) (a : D.R01) :
    f (algebraMap D.R01 C.L a) = algebraMap D.R01 C'.L a := by
  letI := D.ρ1.toRingHom.toAlgebra
  haveI := D.isLocalization_ρ1
  have h : (f : C.L →+* C'.L).comp (algebraMap D.R01 C.L) = algebraMap D.R01 C'.L :=
    IsLocalization.ringHom_ext (Submonoid.powers D.y) (RingHom.ext fun a ↦ by
      change f (algebraMap D.R01 C.L (D.ρ1 a)) = algebraMap D.R01 C'.L (D.ρ1 a)
      rw [C.h1L, C'.h1L]
      exact map_algebraMap_R1 f a)
  exact RingHom.congr_fun h a

/-- **I1: the morphism `C.P → C'.P` of normalisations induced by `f : C.L → C'.L`.** -/
def chartMap (f : C.L →ₐ[K] C'.L) : TwoChartMap C.P C'.P :=
  TwoChartNorm.normMap C.hρ C.h1L C'.hρ C'.h1L (f : C.L →+* C'.L) (map_algebraMap_R01 f)
    C.B₀ C.B₁ C'.B₀ C'.B₁

/-- **Generic-fibre compatibility of `chartMap` on `B₀`.** -/
lemma chartMap_f0_algebraMap (f : C.L →ₐ[K] C'.L) (b : C.B₀) :
    algebraMap C'.B₀ C'.L ((chartMap f).f0 b) = f (algebraMap C.B₀ C.L b) :=
  TwoChartNorm.normMap_f0_algebraMap _ _ _ _ _ _ _ _ _ _ b

/-- **Generic-fibre compatibility of `chartMap` on `B₁`.** -/
lemma chartMap_f1_algebraMap (f : C.L →ₐ[K] C'.L) (b : C.B₁) :
    algebraMap C'.B₁ C'.L ((chartMap f).f1 b) = f (algebraMap C.B₁ C.L b) :=
  TwoChartNorm.normMap_f1_algebraMap _ _ _ _ _ _ _ _ _ _ b

/-- **Generic-fibre compatibility of `chartMap` on the overlap.** -/
lemma chartMap_f01_val (f : C.L →ₐ[K] C'.L) (z : integralClosure D.R01 C.L) :
    Subtype.val (p := (· ∈ integralClosure D.R01 C'.L)) ((chartMap f).f01 z) = f z :=
  rfl

/-- `chartMap f` is determined by its generic-fibre compatibility on the charts. -/
lemma chartMap_ext {f : C.L →ₐ[K] C'.L} {φ : TwoChartMap C.P C'.P}
    (h0 : ∀ b : C.B₀, algebraMap C'.B₀ C'.L (φ.f0 b) = f (algebraMap C.B₀ C.L b))
    (h1 : ∀ b : C.B₁, algebraMap C'.B₁ C'.L (φ.f1 b) = f (algebraMap C.B₁ C.L b)) :
    φ = chartMap f := by
  refine TwoChartMap.ext_of_f0_f1 (AlgHom.ext fun b ↦ ?_) (AlgHom.ext fun b ↦ ?_)
  · exact IsIntegralClosure.algebraMap_injective C'.B₀ D.R0 C'.L
      ((h0 b).trans (chartMap_f0_algebraMap f b).symm)
  · exact IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L
      ((h1 b).trans (chartMap_f1_algebraMap f b).symm)

/-- **`chartMap` of the identity.** -/
lemma chartMap_id : chartMap (AlgHom.id K C.L) = TwoChartMap.id C.P :=
  (chartMap_ext (fun _ ↦ rfl) (fun _ ↦ rfl)).symm

/-- **`chartMap` of a composition.** -/
lemma chartMap_comp (f : C.L →ₐ[K] C'.L) (g : C'.L →ₐ[K] C''.L) :
    chartMap (g.comp f) = (chartMap g).comp (chartMap f) := by
  refine (chartMap_ext (fun b ↦ ?_) (fun b ↦ ?_)).symm
  · rw [TwoChartMap.comp_f0, chartMap_f0_algebraMap, chartMap_f0_algebraMap, AlgHom.comp_apply]
  · rw [TwoChartMap.comp_f1, chartMap_f1_algebraMap, chartMap_f1_algebraMap, AlgHom.comp_apply]

/-- **`chartMap` is compatible with the structure maps from `D`.** -/
lemma chartMap_comp_toNorm (f : C.L →ₐ[K] C'.L) : (chartMap f).comp C.toNorm = C'.toNorm :=
  TwoChartNorm.normMap_comp_toNorm _ _ _ _ _ _ _ _ _ _

/-- **I1: the morphism of chart modules `C.P → C'.P` induced by `f`.** -/
abbrev chartHom (f : C.L →ₐ[K] C'.L) :
    ProjectiveLine.ChartModule.Hom C.P.chartModule C'.P.chartModule :=
  (chartMap f).toHom

/-- **`chartHom f` is a morphism of chart algebras.** -/
theorem isHom_chartHom (f : C.L →ₐ[K] C'.L) : C.P.algStr.IsHom C'.P.algStr (chartHom f) :=
  TwoChartMap.isHom _

/-- **The Galois action on the normalisation**: `σ ↦ chartMap σ`, a monoid map from
`Gal(C.L / K)` to the endomorphisms of `C.P`. -/
def galAct (C : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e) :
    (C.L ≃ₐ[K] C.L) →* TwoChartMap C.P C.P where
  toFun σ := chartMap (σ : C.L →ₐ[K] C.L)
  map_one' := chartMap_id
  map_mul' σ τ := chartMap_comp (τ : C.L →ₐ[K] C.L) (σ : C.L →ₐ[K] C.L)

/-- **The Galois action on the normalisation by automorphisms.** -/
def galActUnits (C : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e) :
    (C.L ≃ₐ[K] C.L) →* (TwoChartMap C.P C.P)ˣ :=
  MonoidHom.toHomUnits C.galAct

lemma galAct_apply (σ : C.L ≃ₐ[K] C.L) : C.galAct σ = chartMap (σ : C.L →ₐ[K] C.L) := rfl

end CovData

end Generic

variable {O : Type u} [CommRing O] (ϖ b₄ b₆ t κ ε : O) (m : ℕ) (hκ : κ * (t ^ 2 - b₆) = 1)
  (q e : ℕ) (K : Type u) [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K]
  [Algebra (NR b₄ b₆ ϖ m ε) K] [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K]

/-- `K` as an algebra over the chart `(twoChart …).R1 = T1 …` (for the projections of `Cov`). -/
instance instAlgebraR1K : Algebra (twoChart (ε * ϖ ^ m) b₄ t κ).R1 K :=
  inferInstanceAs (Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K)

/-- `Rc` as an algebra over the chart `(twoChart …).R0 = T0 …` (for the projections of `Cov`). -/
instance instAlgebraR0Rc :
    Algebra (twoChart (ε * ϖ ^ m) b₄ t κ).R0 (RcT (ε * ϖ ^ m) b₄ t κ) :=
  inferInstanceAs (Algebra (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ))

/-- **A tame cover of the Tate curve (I0)**: the per-cover data of `TateS5` (fields `L`, `B₁`,
`Bn`, `B₀`, `Bc` with their instances, `hρ`, `h1L`, `hL`, `hd`, `hBn`, `hBc`, `hunr₁`, `hunr₀`)
over the fixed Tate data `(ϖ, b₄, b₆, t, κ, ε, m)`, the function field `K` and `q`, `e`. -/
abbrev Cov : Type (u + 1) :=
  CovData K (twoChart (ε * ϖ ^ m) b₄ t κ) (NR b₄ b₆ ϖ m ε) (RcT (ε * ϖ ^ m) b₄ t κ)
    (toNode b₄ hκ rfl) (DT (ε * ϖ ^ m) b₄ t κ) (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ)
    (algebraMap O (T1 (ε * ϖ ^ m) b₄ t κ) ϖ) (algebraMap O (T0 (ε * ϖ ^ m) b₄ t κ) ϖ)
    (Ideal.span {h0 (ε * ϖ ^ m) b₄ t κ, z0 (ε * ϖ ^ m) b₄ t κ}) q e

variable {ϖ b₄ b₆ t κ ε m hκ q e K}

/-- The tower `T1 → T01 → C.L` of a Tate cover (with the chart instances of `C`). -/
lemma Cov.towT01 (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) :
    letI : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) C.L := C.algT1
    letI : Algebra (T01 (ε * ϖ ^ m) b₄ t κ) C.L := C.algT01
    IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) (T01 (ε * ϖ ^ m) b₄ t κ) C.L := by
  letI : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) C.L := C.algT1
  letI : Algebra (T01 (ε * ϖ ^ m) b₄ t κ) C.L := C.algT01
  exact IsScalarTower.of_algebraMap_eq fun x ↦ (C.h1L x).symm

end

end TateS6

end SemistableReduction
