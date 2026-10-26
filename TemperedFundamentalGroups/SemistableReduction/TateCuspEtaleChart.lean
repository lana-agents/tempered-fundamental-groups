/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateCuspCovGeneric
import TemperedFundamentalGroups.SemistableReduction.TateT0Regular
import TemperedFundamentalGroups.SemistableReduction.CuspEtaleChart

/-!
# The Tate cusp chart is étale over `O[h]` at the cusp (MR12 S5.6)

On the Tate chart `T0 = O[h][z]/(G₀)` the derivative `G₀'(z) = 3z² + 2κ(2t + (t − πb₄)h)z +
κ(1 + h)` is `≡ κ(1 + h)` modulo `z`. So the localization `N = Rc[1/G₀'(z)]` of the cusp chart
`Rc = T0[1/(1 + h)]` is standard étale over `O[h]` (`TateCuspCov.etale_NC`, Mathlib's
`StandardEtalePair`), and every prime of `Rc` containing `z` misses `G₀'(z)`
(`TateCuspCov.dG0_notMem`). Hence (**`TateCuspCov.isTameCuspKummerAt_cusp`**, from
`Cusp.isTameCuspKummerAt_of_isLocalization_etale`): a tame Galois cover of `Rc` of degree dividing
`e` (with `ζ_e` in the function field, `CharZero O`) whose normalisation over `Rc_𝔪` is unramified
off the closed point and the prime `(h)` is tamely Kummer at every prime `𝔪 ∋ ϖ, h, z` with the
coordinate `s = h`.
-/

universe u

open Polynomial IsLocalRing Module

namespace SemistableReduction

namespace TateCuspCov

open TateTwoChart

noncomputable section

variable {O : Type u} [CommRing O] {π b₄ t κ b₆ : O}

local notation "𝒯" => T0 π b₄ t κ

local notation "ℛ" => CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ)

variable (π b₄ t κ) in
/-- `∂G₀/∂z` at `z`, in `T0`. -/
abbrev dG0 : 𝒯 := AdjoinRoot.mk (G0 π b₄ t κ) (derivative (G0 π b₄ t κ))

lemma dG0_eq : dG0 π b₄ t κ = algebraMap O 𝒯 κ * TateGlue0.c0 π b₄ t κ + z0 π b₄ t κ *
    (3 * z0 π b₄ t κ + 2 * algebraMap O 𝒯 κ * (algebraMap O 𝒯 (2 * t) +
      algebraMap O 𝒯 (t - π * b₄) * h0 π b₄ t κ)) := by
  have hd : derivative (G0 π b₄ t κ) = 3 * X ^ 2 +
      C (C κ * (C (2 * t) + C (t - π * b₄) * X)) * (2 * X) + C (C κ * (1 + X)) := by
    simp only [G0, derivative_sub, derivative_add, derivative_mul, derivative_C,
      derivative_X_pow, derivative_X, zero_mul, zero_add, mul_one, sub_zero]
    norm_num
    simp only [map_ofNat]
  rw [dG0, hd]
  simp only [map_add, map_mul, map_pow, map_ofNat, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_one,
    of_C, TateGlue0.c0, h0, z0]
  ring

lemma q0_eq : TateT0Regular.q0 π b₄ t κ = algebraMap O 𝒯 κ * TateGlue0.c0 π b₄ t κ +
    z0 π b₄ t κ * (z0 π b₄ t κ + algebraMap O 𝒯 κ * algebraMap O 𝒯 t *
      (2 + h0 π b₄ t κ)) := by
  simp only [TateT0Regular.q0, TateGlue0.c0]
  ring

/-- **`κ (1 + h) + z w` is a unit at the primes of `Rc` containing `z`.** -/
lemma notMem_of_eq (hκ : κ * (t ^ 2 - b₆) = 1) (P : Ideal ℛ) [P.IsPrime]
    (hz : algebraMap 𝒯 ℛ (z0 π b₄ t κ) ∈ P) {x w : 𝒯}
    (hx : x = algebraMap O 𝒯 κ * TateGlue0.c0 π b₄ t κ + z0 π b₄ t κ * w) :
    algebraMap 𝒯 ℛ x ∉ P := by
  intro hxP
  have h1 : algebraMap 𝒯 ℛ (algebraMap O 𝒯 κ * TateGlue0.c0 π b₄ t κ) ∈ P := by
    have e : algebraMap 𝒯 ℛ (algebraMap O 𝒯 κ * TateGlue0.c0 π b₄ t κ) =
        algebraMap 𝒯 ℛ x - algebraMap 𝒯 ℛ (z0 π b₄ t κ) * algebraMap 𝒯 ℛ w := by
      rw [hx, map_add, map_mul (algebraMap 𝒯 ℛ) (z0 π b₄ t κ)]
      ring
    rw [e]
    exact P.sub_mem hxP (P.mul_mem_right _ hz)
  have hu : IsUnit (algebraMap 𝒯 ℛ (algebraMap O 𝒯 κ * TateGlue0.c0 π b₄ t κ)) := by
    rw [map_mul]
    exact ((IsUnit.of_mul_eq_one _ hκ).map (algebraMap O 𝒯)).map _ |>.mul
      (IsLocalization.Away.algebraMap_isUnit _)
  exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ h1 hu)

lemma dG0_notMem (hκ : κ * (t ^ 2 - b₆) = 1) (P : Ideal ℛ) [P.IsPrime]
    (hz : algebraMap 𝒯 ℛ (z0 π b₄ t κ) ∈ P) : algebraMap 𝒯 ℛ (dG0 π b₄ t κ) ∉ P :=
  notMem_of_eq hκ P hz dG0_eq

lemma q0_notMem (hκ : κ * (t ^ 2 - b₆) = 1) (P : Ideal ℛ) [P.IsPrime]
    (hz : algebraMap 𝒯 ℛ (z0 π b₄ t κ) ∈ P) :
    algebraMap 𝒯 ℛ (TateT0Regular.q0 π b₄ t κ) ∉ P :=
  notMem_of_eq hκ P hz q0_eq

/-! ### The étale chart `N = Rc[1/G₀'(z)]` -/

variable (π b₄ t κ) in
/-- The standard étale pair `(G₀, G₀' · (1 + h))` over `O[h]`. -/
def stdPair : StandardEtalePair O[X] where
  f := G0 π b₄ t κ
  monic_f := monic_G0 π b₄ t κ
  g := derivative (G0 π b₄ t κ) * C (1 + X)
  cond := ⟨C (1 + X), 0, 1, by ring⟩

lemma mk_stdPair_g : AdjoinRoot.mk (G0 π b₄ t κ) (stdPair π b₄ t κ).g =
    dG0 π b₄ t κ * TateGlue0.c0 π b₄ t κ := by
  simp only [stdPair, map_mul, AdjoinRoot.mk_C, map_add, map_one, TateGlue0.c0, h0]

variable (π b₄ t κ) in
/-- **The étale chart at the cusp**: `N = Rc[1/G₀'(z)]`. -/
abbrev NC : Type u := Localization.Away (algebraMap 𝒯 ℛ (dG0 π b₄ t κ))

/-- `N = T0[1/(G₀'(z) (1 + h))]`. -/
lemma isLocalization_NC : IsLocalization.Away (AdjoinRoot.mk (G0 π b₄ t κ) (stdPair π b₄ t κ).g)
    (NC π b₄ t κ) := by
  rw [mk_stdPair_g]
  exact IsLocalization.Away.mul ℛ (NC π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (dG0 π b₄ t κ)

/-- **`N = Rc[1/G₀'(z)]` is étale over `O[h]`.** -/
theorem etale_NC : Algebra.Etale O[X] (NC π b₄ t κ) := by
  haveI := isLocalization_NC (π := π) (b₄ := b₄) (t := t) (κ := κ)
  let e : Localization.Away (AdjoinRoot.mk (G0 π b₄ t κ) (stdPair π b₄ t κ).g) ≃ₐ[𝒯]
      NC π b₄ t κ :=
    IsLocalization.algEquiv
      (Submonoid.powers (AdjoinRoot.mk (G0 π b₄ t κ) (stdPair π b₄ t κ).g)) _ _
  exact Algebra.Etale.of_equiv ((stdPair π b₄ t κ).equivAwayAdjoinRoot.trans
    (e.restrictScalars O[X]))

lemma algebraMap_X_Rc : algebraMap O[X] ℛ X = CuspTower.sC 𝒯 (TateGlue0.c0 π b₄ t κ)
    (h0 π b₄ t κ) := by
  rw [IsScalarTower.algebraMap_apply O[X] 𝒯 ℛ, AdjoinRoot.algebraMap_eq]

/-- A prime of `Rc` containing `ϖ` and `h` lies over the cusp point of `O[h]`. -/
lemma comap_eq_cuspIdeal [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (P : Ideal ℛ) [P.IsPrime] (hϖP : algebraMap O ℛ ϖ ∈ P)
    (hs : CuspTower.sC 𝒯 (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ) ∈ P) :
    P.comap (algebraMap O[X] ℛ) = Cusp.cuspIdeal O := by
  refine ((Cusp.cuspIdeal_isMaximal O).eq_of_le (Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top ‹_›))
    fun p hp ↦ ?_).symm
  rw [Cusp.mem_cuspIdeal, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  obtain ⟨a, ha⟩ := hp
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := p)
  rw [Ideal.mem_comap, show p = C (p.coeff 0) + X * q by rw [← hq]; ring, map_add, map_mul,
    algebraMap_X_Rc, ha, ← Polynomial.algebraMap_eq (R := O), ← IsScalarTower.algebraMap_apply,
    map_mul]
  exact P.add_mem (P.mul_mem_right _ hϖP) (P.mul_mem_right _ hs)

set_option maxHeartbeats 400000 in
-- Many localization structures.
/-- **Tame covers of the cusp chart are tamely Kummer at the cusp** (S3 for `Rc`): for a prime
`𝔪` of `Rc` containing `ϖ`, `h` and `z`, `L / K` finite Galois of degree dividing `e`, `ζ_e ∈ K`,
whose normalisation over `Rc_𝔪` is unramified off the closed point and the prime `(h)`. -/
theorem isTameCuspKummerAt_cusp [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {e : ℕ}
    [NeZero e] {ϖ : O} (hϖ : Irreducible ϖ) (hκ : κ * (t ^ 2 - b₆) = 1) [IsDomain ℛ]
    (𝔪 : Ideal ℛ) [𝔪.IsPrime] (hϖ𝔪 : algebraMap O ℛ ϖ ∈ 𝔪)
    (hs : CuspTower.sC 𝒯 (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ) ∈ 𝔪)
    (hz : algebraMap 𝒯 ℛ (z0 π b₄ t κ) ∈ 𝔪)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    [Algebra (Localization.AtPrime 𝔪) L] [IsScalarTower ℛ (Localization.AtPrime 𝔪) L]
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime 𝔪) B] [Algebra B L]
    [IsScalarTower (Localization.AtPrime 𝔪) B L] [IsIntegralClosure B (Localization.AtPrime 𝔪) L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap (Localization.AtPrime 𝔪) B) ≠ maximalIdeal (Localization.AtPrime 𝔪) →
      Q.comap (algebraMap (Localization.AtPrime 𝔪) B) ≠
        Ideal.span {algebraMap ℛ (Localization.AtPrime 𝔪)
          (CuspTower.sC 𝒯 (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))} →
      Algebra.IsUnramifiedAt (Localization.AtPrime 𝔪) Q) :
    Cusp.IsTameCuspKummerAt O e (CuspTower.sC 𝒯 (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ)) L 𝔪 := by
  have hg := dG0_notMem hκ 𝔪 hz
  have hg0 : algebraMap 𝒯 ℛ (dG0 π b₄ t κ) ≠ 0 := fun h ↦ hg (h ▸ 𝔪.zero_mem)
  haveI : IsDomain (NC π b₄ t κ) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg0)
  haveI : Algebra.Etale O[X] (NC π b₄ t κ) := etale_NC
  haveI : Algebra.Etale ℛ (NC π b₄ t κ) :=
    Algebra.Etale.of_isLocalizationAway (algebraMap 𝒯 ℛ (dG0 π b₄ t κ))
  have hdisj : Disjoint ((Submonoid.powers (algebraMap 𝒯 ℛ (dG0 π b₄ t κ)) : Submonoid ℛ) :
      Set ℛ) 𝔪 := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hy
    exact hg (Ideal.IsPrime.mem_of_pow_mem ‹_› n hy)
  have h := Cusp.isTameCuspKummerAt_of_isLocalization_etale hϖ (NC π b₄ t κ)
    (Submonoid.powers (algebraMap 𝒯 ℛ (dG0 π b₄ t κ))) (algebraMap O[X] ℛ)
    (fun a ↦ IsScalarTower.algebraMap_apply _ _ _ a) 𝔪 hdisj
    (comap_eq_cuspIdeal hϖ 𝔪 hϖ𝔪 hs) K hζ L hd B
    (fun Q _ h1 h2 ↦ hunr Q h1 (by rwa [algebraMap_X_Rc] at h2))
  rwa [algebraMap_X_Rc] at h

end

end TateCuspCov

end SemistableReduction
