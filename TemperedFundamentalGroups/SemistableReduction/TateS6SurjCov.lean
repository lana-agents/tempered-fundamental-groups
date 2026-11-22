/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Surj
import TemperedFundamentalGroups.SemistableReduction.TateS6Faithful
import TemperedFundamentalGroups.SemistableReduction.TateS6Extend
import TemperedFundamentalGroups.SemistableReduction.TateS6Gal

/-!
# The special-fibre datum functor: surjectivity onto balanced morphisms (MR12, interface I3)

* **`TateS6.CovBalanced F`**: a morphism `F : Datum.Hom (datum C) (datum C')` of the special-fibre
  data of two tame covers is balanced at the nodes (`TateGlue1.Balanced` of `F.f₁`, the node
  balance condition of the lead decision after MR12 c47);
* **`TateS6.exists_datumHom_eq`** (I3, surjectivity): every balanced `F` is `datumHom f` for a
  `K`-algebra map `f : C.L → C'.L` (`exists_hom_spec` gives a morphism of chart algebras of the
  normalisations reducing to `F`, `CovData.ofHom` the map of covers, and the generic
  `CovData.csMap_map1_ofHom`, `csMap_map0_ofHom` identify its reductions);
* **`TateS6.mem_mrange_galHom`**: every balanced endomorphism of the datum of `C` comes from
  `Gal(C.L/K)` (`galHom`, `TateS6Gal`); with `galEquiv`, `Gal(C.L/K)` is isomorphic to a
  submonoid of the endomorphisms of the datum containing all balanced ones. The converse (I5(b):
  `datumHom f` is balanced) is not formalised yet.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateS6

open TateTwoChart TateTwoChartNode TateGlue0 TateLevel AdmissibleLift

noncomputable section

namespace CovData

variable {A : Type u} [CommRing A] {K : Type u} [Field K] {D : ProjectiveLine.TwoChartRings A}
  {Rn Rc : Type u} [CommRing Rn] [CommRing Rc] [Algebra D.R1 K] [Algebra Rn K] [Algebra Rc K]
  [Algebra D.R0 Rc] {toN : D.R1 → Rn} {dT : D.R1} {c0 : D.R0} {ϖ1 : D.R1} {ϖ0 : D.R0}
  {I0 : Ideal D.R0} {q e : ℕ} {C C' : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e}
  [IsDomain D.R1] [IsFractionRing D.R1 K]
  (Φ : ProjectiveLine.ChartModule.Hom C.P.chartModule C'.P.chartModule)
  (hΦ : C.P.algStr.IsHom C'.P.algStr Φ)
  (hΦ1 : ∀ a, Φ.f1 (algebraMap D.R1 C.B₁ a) = algebraMap D.R1 C'.B₁ a)

include hΦ1 in
/-- **The reduction of `map1 (ofHom Φ)` modulo an ideal of `D.R1`** is any algebra map `F`
compatible with `Φ` on residues. -/
lemma csMap_map1_ofHom (I : Ideal D.R1)
    (F : (C.B₁ ⧸ I.map (algebraMap D.R1 C.B₁)) →ₐ[D.R1 ⧸ I]
      (C'.B₁ ⧸ I.map (algebraMap D.R1 C'.B₁)))
    (h : ∀ b, Ideal.Quotient.mk _ (Φ.f1 b) = F (Ideal.Quotient.mk _ b)) :
    OmegaPair.csMap I (map1 (ofHom Φ hΦ hΦ1)) (map1_algebraMap _) = F := by
  refine AlgHom.ext fun x ↦ ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [OmegaPair.csMap_mk, map1_ofHom]
  exact h b

include hΦ1 in
/-- **The reduction of `map0 (ofHom Φ)` modulo an ideal of `D.R0`** is any algebra map `F`
compatible with `Φ` on residues. -/
lemma csMap_map0_ofHom (I : Ideal D.R0)
    (F : (C.B₀ ⧸ I.map (algebraMap D.R0 C.B₀)) →ₐ[D.R0 ⧸ I]
      (C'.B₀ ⧸ I.map (algebraMap D.R0 C'.B₀)))
    (h : ∀ b, Ideal.Quotient.mk _ (Φ.f0 b) = F (Ideal.Quotient.mk _ b)) :
    OmegaPair.csMap I (map0 (ofHom Φ hΦ hΦ1)) (map0_algebraMap _) = F := by
  refine AlgHom.ext fun x ↦ ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [OmegaPair.csMap_mk, map0_ofHom]
  exact h b

omit [IsDomain D.R1] in
/-- `eq_zero_of_mem_pow` with the primality of `P` as an explicit argument. -/
theorem eq_zero_of_mem_pow' (C : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e)
    [IsNoetherianRing C.B₁] (ϖ : A) (P : Ideal D.R1) (hP : P.IsPrime)
    (hϖ : algebraMap A D.R1 ϖ ∈ P) (b : C.P.R1)
    (hb : ∀ n, b ∈ (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap A C.P.R1)) : b = 0 :=
  haveI := hP
  eq_zero_of_mem_pow C ϖ P hϖ b hb

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

set_option hygiene false in
/-- `datumHom` with the fixed Tate data of this section. -/
local notation "𝔥" f:max => datumHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ f

set_option hygiene false in
/-- The datum of a cover, with the fixed Tate data of this section. -/
local notation "𝔇" C:max => datum hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C

/-- **Balanced morphisms of special-fibre data of covers**: `f₁` is balanced at the nodes
(`TateGlue1.Balanced`, with the node parameters `π' j = ϖ^(m / e j)` of `TateS5.piP`). -/
def CovBalanced {C C' : Cov ϖ b₄ b₆ t κ ε m hκ q e K} (F : Datum.Hom (𝔇 C) (𝔇 C')) : Prop := by
  cov_inst C
  cov_inst C'
  exact TateGlue1.Balanced hκ rfl hε
    (TateS5.sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ C.hL C.hBn C.hunr₁ τ)
    (TateS5.sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ C'.hL C'.hBn C'.hunr₁ τ)
    (TateS5.θ_ϖ hker) (TateS5.piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ C.hL C.hBn C.hunr₁ τ)
    (TateS5.piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ C'.hL C'.hBn C'.hunr₁ τ) F.f₁

set_option maxHeartbeats 1000000 in
-- instantiating `exists_hom_spec` at two covers
/-- **I3, surjectivity: every balanced morphism of special-fibre data comes from a map of
covers.** -/
theorem exists_datumHom_eq [IsAdicComplete (Ideal.span {ϖ}) O] (h2 : (2 : k) ≠ 0)
    {C C' : Cov ϖ b₄ b₆ t κ ε m hκ q e K} (F : Datum.Hom (𝔇 C) (𝔇 C'))
    (hbal : CovBalanced hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ F) :
    ∃ f : C.L →ₐ[K] C'.L, 𝔥 f = F := by
  cov_inst C
  cov_inst C'
  haveI : IsDomain (twoChart (ε * ϖ ^ m) b₄ t κ).R1 := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
  haveI : IsFractionRing (twoChart (ε * ϖ ^ m) b₄ t κ).R1 K :=
    inferInstanceAs (IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K)
  obtain ⟨P, hPm, hϖP, -⟩ := exists_regular_point_T1 (θ := θ) hϖ hker hκ hε h3 hE (m := m)
  haveI := finite_B₁ hϖ hker hκ hε h3 hE K C.L C.B₁
  haveI := finite_B₁ hϖ hker hκ hε h3 hE K C'.L C'.B₁
  haveI : IsNoetherianRing C.B₁ :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower (T1 (ε * ϖ ^ m) b₄ t κ) inferInstance)
  haveI : IsNoetherianRing C'.B₁ :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower (T1 (ε * ϖ ^ m) b₄ t κ) inferInstance)
  obtain ⟨Φ, hΦ, hb, hr1, hr0⟩ := exists_hom_spec (hϖ := hϖ) (hker := hker) (hκ := hκ) (hε := hε)
    (h3 := h3) (hE := hE) (hb₆ := hb₆) (hqM := hqM) (hq := hq) (hM' := hM') (hM'k := hM'k)
    (he := he) (hK := hK) (hζ := hζ) (hζe := hζe) (hL := C.hL) (hd := C.hd) (hρ := C.hρ)
    (hBn := C.hBn) (hBc := C.hBc) (hunr₁ := C.hunr₁) (hunr₀ := C.hunr₀) (hL' := C'.hL)
    (hd' := C'.hd) (hρ' := C'.hρ) (hBn' := C'.hBn) (hBc' := C'.hBc) (hunr₁' := C'.hunr₁)
    (hunr₀' := C'.hunr₀) (τ := τ) (φ₀ := φ₀) h2 F hbal
    (fun b hb ↦ CovData.eq_zero_of_mem_pow' C ϖ P hPm.isPrime hϖP b hb)
    (fun b hb ↦ CovData.eq_zero_of_mem_pow' C' ϖ P hPm.isPrime hϖP b hb)
  refine ⟨CovData.ofHom Φ hΦ hb, OmegaPair.Hom.ext ?_ ?_⟩
  · exact (datumHom_f₁ hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ _).trans
      (CovData.csMap_map1_ofHom Φ hΦ hb _ F.f₁ hr1)
  · exact (datumHom_f₀ hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ _).trans
      (CovData.csMap_map0_ofHom Φ hΦ hb _ F.f₀ hr0)

/-- **I3 at the Galois group: every balanced endomorphism of the special-fibre datum of a tame
cover comes from `Gal(C.L/K)`** (`exists_datumHom_eq`; an endomorphism of the finite extension
`C.L/K` is an automorphism). -/
theorem mem_mrange_galHom [IsAdicComplete (Ideal.span {ϖ}) O] (h2 : (2 : k) ≠ 0)
    (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) (F : Datum.Hom (𝔇 C) (𝔇 C))
    (hbal : CovBalanced hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ F) :
    F ∈ MonoidHom.mrange (galHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C) := by
  have ex := exists_datumHom_eq hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ h2 (C := C)
    (C' := C) F hbal
  have hfb : Function.Bijective ex.choose := AlgHom.bijective _
  refine MonoidHom.mem_mrange.mpr ⟨AlgEquiv.ofBijective _ hfb, Eq.trans ?_ ex.choose_spec⟩
  simp only [galHom, MonoidHom.coe_mk, OneHom.coe_mk]
  exact congrArg (fun g ↦ 𝔥 g) (AlgHom.ext fun _ ↦ rfl)

end Functor

end

end TateS6

end SemistableReduction
