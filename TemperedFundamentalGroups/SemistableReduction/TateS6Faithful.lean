/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Datum
import TemperedFundamentalGroups.SemistableReduction.UnramifiedHomExt

/-!
# The special-fibre datum functor is faithful (MR12, interface I3, injectivity)

**`TateS6.datumHom_injective`**: two `K`-algebra maps `f g : C.L → C'.L` of tame covers of the
Tate curve with the same morphism of special-fibre data (`datumHom f = datumHom g`; in fact
equality of the components over `V₁` suffices) are equal.

Proof: the maps of normalisations `C.B₁ → C'.B₁` agree modulo `J`; at a closed point `P` of the
special fibre of `T1` with `w ∉ P` (**`TateTwoChart.exists_point_T1`**: `w = 1`,
`κ (h'² + (2t + 1) h' + t) = -1`, solvable as `k` is algebraically closed) the chart is regular
(`exists_regular_pair_T1`), so `C.B₁` is étale over `T1` at every point over `P` (purity, from
`hunr₁`), and `UnramifiedHomExt.eq_of_normalisation_sub_mem` applies (generic form for covers
over abstract two-chart rings: **`TateS6.CovData.eq_of_map1_sub_mem`**; the point:
**`TateTwoChart.exists_regular_point_T1`**).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateTwoChart

variable {O : Type u} [CommRing O] {k : Type u} [Field k] [IsAlgClosed k] {θ : O →+* k}
  {π b₄ t κ ϖ : O}

/-- The point `(h', w) = (h₀, 1)` of the special fibre of `T1`. -/
noncomputable def evPoint (h₀ : k)
    (h : 1 + θ κ * (2 * θ t * h₀ + (θ t - θ π * θ b₄)) + θ κ * (h₀ ^ 2 + h₀) - θ κ * θ π = 0) :
    T1 π b₄ t κ →+* k :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom θ h₀) 1 (by
    simp only [G1, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
      coe_eval₂RingHom, map_mul, map_add, map_pow, eval₂_X, eval₂_C, one_pow, mul_one]
    rw [← h, map_ofNat, map_sub, map_mul])

include θ in
/-- **A closed point of the special fibre of `T1` where `w` is a unit.** -/
theorem exists_point_T1 (hθ : Function.Surjective θ) (hπ : θ π = 0) (hϖ : θ ϖ = 0)
    (hκ : θ κ ≠ 0) :
    ∃ P : Ideal (T1 π b₄ t κ), P.IsMaximal ∧ algebraMap O _ ϖ ∈ P ∧ w1 π b₄ t κ ∉ P := by
  obtain ⟨h₀, hh₀⟩ := IsAlgClosed.exists_root
    (C (θ κ) * X ^ 2 + C (θ κ * (2 * θ t + 1)) * X + C (θ κ * θ t + 1)) (by
      rw [Polynomial.degree_quadratic hκ]; decide)
  have h : 1 + θ κ * (2 * θ t * h₀ + (θ t - θ π * θ b₄)) + θ κ * (h₀ ^ 2 + h₀) -
      θ κ * θ π = 0 := by
    rw [IsRoot, eval_add, eval_add, eval_mul, eval_mul, eval_C, eval_C, eval_C, eval_pow,
      eval_X] at hh₀
    rw [hπ]
    linear_combination hh₀
  have hev : ∀ o : O,
      evPoint (π := π) (b₄ := b₄) (t := t) (κ := κ) h₀ h (algebraMap O _ o) = θ o :=
    fun o ↦ by
    rw [← of_C]
    unfold evPoint
    rw [AdjoinRoot.lift_of]
    simp
  refine ⟨RingHom.ker (evPoint (π := π) (b₄ := b₄) (t := t) (κ := κ) h₀ h),
    RingHom.ker_isMaximal_of_surjective _ fun x ↦ ?_, ?_, ?_⟩
  · obtain ⟨o, rfl⟩ := hθ x
    exact ⟨_, hev o⟩
  · rw [RingHom.mem_ker, hev, hϖ]
  · rw [RingHom.mem_ker, w1]
    unfold evPoint
    rw [AdjoinRoot.lift_root]
    exact one_ne_zero

/-- **A regular closed point of the special fibre of the Tate chart `T1`**: a maximal ideal `P`
containing `ϖ` (hence `J`) at which `T1` is regular (`w ∉ P`, `exists_regular_pair_T1`). -/
theorem exists_regular_point_T1 [IsDomain O] [IsDiscreteValuationRing O]
    {θ : O →+* k} [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hκ : κ * (t ^ 2 - b₆) = 1)
    (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) :
    ∃ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) (_ : P.IsMaximal), algebraMap O _ ϖ ∈ P ∧
      AdmissibleLift.J θ (R := T1 (ε * ϖ ^ m) b₄ t κ) ≤ P ∧
        ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
        IsLocalRing.maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y} := by
  haveI := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
  have hθϖ : θ ϖ = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ϖ
  have hθπ : θ (ε * ϖ ^ m) = 0 := by
    rw [map_mul, map_pow, hθϖ, zero_pow (NeZero.ne m), mul_zero]
  have hθκ : θ κ ≠ 0 := fun h0 ↦ by
    have := congrArg θ hκ
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  obtain ⟨P, hPm, hϖP, hwP⟩ := exists_point_T1 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
    hθ.out hθπ hθϖ hθκ
  obtain ⟨y, hx, hy, hm⟩ := exists_regular_pair_T1 hϖ hθ.out hker rfl (Nat.pos_of_neZero m) hκ
    P hϖP hwP
  refine ⟨P, hPm, hϖP, ?_, _, y, hx, hy, hm⟩
  rw [AdmissibleLift.J, hker, Ideal.map_span, Ideal.span_le, Set.image_singleton,
    Set.singleton_subset_iff]
  exact hϖP

end TateTwoChart

namespace TateS6

open TateTwoChart TateTwoChartNode TateGlue0 TateLevel AdmissibleLift

noncomputable section

namespace CovData

variable {A : Type u} [CommRing A] {K : Type u} [Field K] {D : ProjectiveLine.TwoChartRings A}
  {Rn Rc : Type u} [CommRing Rn] [CommRing Rc] [Algebra D.R1 K] [Algebra Rn K] [Algebra Rc K]
  [Algebra D.R0 Rc] {toN : D.R1 → Rn} {dT : D.R1} {c0 : D.R0} {ϖ1 : D.R1} {ϖ0 : D.R0}
  {I0 : Ideal D.R0} {q e : ℕ} {C C' : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e}
  [IsDomain D.R1] [IsNoetherianRing D.R1] [IsIntegrallyClosed D.R1] [IsFractionRing D.R1 K]

/-- **Faithfulness on `V₁`, generic**: `K`-algebra maps of covers whose maps of normalisations
of `D.R1` agree modulo `I₀`, for `I₀` inside a regular closed point `P ∋ ϖ1`, are equal. -/
theorem eq_of_map1_sub_mem (P : Ideal D.R1) (hϖP : ϖ1 ∈ P)
    (hreg : ∃ (_ : P.IsMaximal) (x y : Localization.AtPrime P), Prime x ∧
      y ∉ Ideal.span {x} ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (I₀ : Ideal D.R1) (hI₀ : I₀ ≤ P) {f g : C.L →ₐ[K] C'.L}
    (hfg : ∀ b, map1 f b - map1 g b ∈ I₀.map (algebraMap D.R1 C'.B₁)) : f = g := by
  obtain ⟨hP, x, y, hx, hy, hm⟩ := hreg
  exact UnramifiedHomExt.eq_of_normalisation_sub_mem K C.B₁ C'.B₁ P hx hy hm
    (fun Q _ hQ ↦ C.hunr₁ P hϖP Q hQ) I₀ hI₀ (map1 f) (map1 g) (algebraMap_map1 f)
    (algebraMap_map1 g) hfg

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

/-- **I3, injectivity: the special-fibre datum functor is faithful.** Two `K`-algebra maps of
tame covers with the same morphism of special-fibre data are equal. -/
theorem datumHom_injective {C C' : Cov ϖ b₄ b₆ t κ ε m hκ q e K} :
    Function.Injective (fun f : C.L →ₐ[K] C'.L ↦ 𝔥 f) := by
  intro f g hfg
  obtain ⟨P, hPm, hϖP, hJP, y₁, y₂, hx, hy, hm⟩ :=
    exists_regular_point_T1 (θ := θ) hϖ hker hκ hε h3 hE (m := m)
  haveI : IsDomain (twoChart (ε * ϖ ^ m) b₄ t κ).R1 := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
  haveI : IsIntegrallyClosed (twoChart (ε * ϖ ^ m) b₄ t κ).R1 :=
    TateGlue1.isIntegrallyClosed_T1' (k := k) (θ := θ) hϖ hker hκ hε h3 hE
  haveI : IsNoetherianRing (twoChart (ε * ϖ ^ m) b₄ t κ).R1 :=
    inferInstanceAs (IsNoetherianRing (T1 (ε * ϖ ^ m) b₄ t κ))
  haveI : IsFractionRing (twoChart (ε * ϖ ^ m) b₄ t κ).R1 K :=
    inferInstanceAs (IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K)
  have h₁ : (𝔥 f).f₁ = (𝔥 g).f₁ := congrArg OmegaPair.Hom.f₁ hfg
  refine CovData.eq_of_map1_sub_mem (D := twoChart (ε * ϖ ^ m) b₄ t κ) P hϖP
    ⟨hPm, y₁, y₂, hx, hy, hm⟩ _ hJP fun b ↦ ?_
  have := DFunLike.congr_fun h₁ (Ideal.Quotient.mk _ b)
  simp only [datumHom_f₁] at this
  exact Ideal.Quotient.eq.1 this

end Functor

end

end TateS6


end SemistableReduction
