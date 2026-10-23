/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateTwoChart
import TemperedFundamentalGroups.Setup.SmoothNormal
import TemperedFundamentalGroups.Andre.TateNormalAlgebra

/-!
# The generic fibre of the Tate two-chart model is a Dedekind domain

Let `K` be a field and `π b₄ b₆ t κ ∈ K` with `κ (t² − b₆) = 1`, `3 ≠ 0`, `π ≠ 0` and
`E = tateE π b₄ b₆ ≠ 0` (with `π ≠ 0` this says that the discriminant `Δ = −π² E` of
`y² + xy = x³ + π² b₄ x + π² b₆` is nonzero, `TateNormal.tateDisc_eq`). Then the chart rings
`TateTwoChart.T0 π b₄ t κ = K[h][z]/(G₀)` and `TateTwoChart.T1 π b₄ t κ = K[h'][w]/(G₁)` are
Dedekind domains (**`TateTwoChart.isDedekindDomain_T0`**, **`TateTwoChart.isDedekindDomain_T1`**).

Over a domain `O` with `ϖ ≠ 0` and a field `K` which is the localization `O[1/ϖ]` (for a discrete
valuation ring `O` and a nonzero nonunit `ϖ`, `K = Frac O`: `isLocalization_away_fractionRing`),
the chart ring over `K` (with the parameters mapped to `K`) is `T_i[1/ϖ]`
(`TateTwoChart.awayEquiv0`, `TateTwoChart.awayEquiv1`), hence
**`TateTwoChart.isDedekindDomain_away_T0`**, **`TateTwoChart.isDedekindDomain_away_T1`**:
`Localization.Away (algebraMap O T_i ϖ)` is a Dedekind domain (and the variants `..._of_dvr`).

## Proof

* **Smoothness** (`PlaneCurve.formallySmooth_of_lift`): `A = K[X][Y]/(G)` is formally smooth over
  `K` as soon as the generators lift to a zero of `G` in `K[X][Y]/J²`, `J = ker (K[X][Y] → A)`
  (`Algebra.FormallySmooth.iff_split_surjection`). If `a ∂ₓG + b ∂ᵧG + c G = u` with `u ∈ Kˣ`,
  the lift `(x − G a/u, y − G b/u)` works (first-order Taylor expansion, `G² ∈ J²`). For the Tate
  charts such a certificate exists with `u = 3 π E κ` (`TateTwoChart.cert0`, `TateTwoChart.cert1`);
  it comes from the certificate `3 π E ℓ⁴ ∈ (F_u, F_v, F_w)` for the Tate cubic
  `F = v² w + u v w − π u³ − π b₄ u w² − b₆ w³` (`ℓ = v − t w`, resp. `ℓ = u`) and the Euler
  relation.
* **Domain**: `G₀`, `G₁` are monic cubics over `K[X]` without roots in `K[X]` (a root divides
  `κ π X³`, resp. the unit `κ π`, and comparing coefficients excludes `c Xⁱ`).
* `A` is finite over `K[X]`, hence noetherian of dimension `≤ 1`, and it is integrally closed
  as a smooth domain over a field (`SmoothNormal.isIntegrallyClosed_of_smooth`).
* **Flatness** (`PlaneCurve.flat_of_isIntegral`): over a Dedekind domain `T` integral over a
  domain `R`, every `T`-module flat over `R` is flat over `T` (for the flatness of the
  algebraized covering over `T_i[1/ϖ]`).
* **Base change** (`PlaneCurve.isLocalization_adjoinRoot_map`): for `G ∈ O[X][Y]` monic and
  `K = M⁻¹ O` (`M` without zero divisors), `K[X][Y]/(G_K)` is the localization of `O[X][Y]/(G)` at
  the image of `M` (injectivity via division by the monic `G`).
-/

open Polynomial TemperedFundamentalGroups

namespace SemistableReduction

noncomputable section

namespace PlaneCurve

section Smooth

variable {K : Type*} [Field K] (G : K[X][X])

/-- The quotient map `K[X][Y] → K[X][Y]/(G)` as a `K`-algebra map. -/
abbrev mkK : K[X][X] →ₐ[K] AdjoinRoot G := (AdjoinRoot.mkₐ G).restrictScalars K

/-- The first-order thickening `K[X][Y]/J²` of `AdjoinRoot G`, `J = (G)`. -/
abbrev Thick : Type _ := K[X][X] ⧸ RingHom.ker (mkK G).toRingHom ^ 2

/-- The quotient map onto the thickening. -/
abbrev mkT : K[X][X] →+* Thick G := Ideal.Quotient.mk (RingHom.ker (mkK G).toRingHom ^ 2)

/-- `G² = 0` in the thickening. -/
lemma sq_mk_self : mkT G G ^ 2 = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (RingHom.mem_ker.mpr AdjoinRoot.mk_self) 2

/-- The image of `p ∈ K[X][Y]` in the thickening is `p` evaluated at the images of `X`, `Y`. -/
lemma mk_eq_eval₂ (p : K[X][X]) : mkT G p =
    p.eval₂ ((aeval (mkT G (C X)) : K[X] →ₐ[K] Thick G) : K[X] →+* Thick G) (mkT G X) := by
  calc mkT G p = mkT G (p.eval₂ C X) := by
          rw [eval₂_C_X]
    _ = _ := by
      rw [Polynomial.hom_eval₂]
      congr 1
      refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, aeval_C]
        rw [← Ideal.Quotient.mk_algebraMap]
        rfl
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, aeval_X]

/-- **Formal smoothness from a first-order lift**: if `(x + G α, y + G β)` is a zero of `G` in
the thickening `K[X][Y]/J²`, then `K[X][Y]/(G)` is formally smooth over `K`. -/
theorem formallySmooth_of_lift (α β : Thick G)
    (h : G.eval₂ ((aeval (mkT G (C X) + mkT G G * α) : K[X] →ₐ[K] Thick G) : K[X] →+* Thick G)
      (mkT G X + mkT G G * β) = 0) :
    Algebra.FormallySmooth K (AdjoinRoot G) := by
  haveI : Algebra.FormallySmooth K K[X][X] := Algebra.FormallySmooth.comp K K[X] K[X][X]
  rw [Algebra.FormallySmooth.iff_split_surjection (mkK G) AdjoinRoot.mk_surjective]
  refine ⟨AdjoinRoot.liftAlgHom G (aeval _) _ h, ?_⟩
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective α
  obtain ⟨β, rfl⟩ := Ideal.Quotient.mk_surjective β
  have hG : mkK G G = 0 := AdjoinRoot.mk_self
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom, AdjoinRoot.liftAlgHom_of, aeval_X,
      AlgHom.id_apply]
    rw [← map_mul, ← map_add, AlgHom.kerSquareLift_mk, map_add, map_mul, hG, zero_mul, add_zero]
    exact AdjoinRoot.mk_C X
  · simp only [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root, AlgHom.id_apply]
    rw [← map_mul, ← map_add, AlgHom.kerSquareLift_mk, map_add, map_mul, hG, zero_mul, add_zero]
    exact AdjoinRoot.mk_X

/-- **A smooth plane curve, finite over the line and irreducible, is a Dedekind domain.** -/
theorem isDedekindDomain_of_irreducible {G : K[X][X]} (hm : G.Monic) (hirr : Irreducible G)
    [Algebra.FormallySmooth K (AdjoinRoot G)] : IsDedekindDomain (AdjoinRoot G) := by
  haveI : IsDomain (AdjoinRoot G) := AdjoinRoot.isDomain_of_prime hirr.prime
  haveI : Module.Finite K[X] (AdjoinRoot G) := (AdjoinRoot.powerBasis' hm).finite
  haveI : Algebra.Smooth K (AdjoinRoot G) := {}
  haveI : IsNoetherianRing (AdjoinRoot G) := Algebra.FiniteType.isNoetherianRing K _
  haveI : Ring.DimensionLEOne (AdjoinRoot G) := Ring.DimensionLEOne.of_isIntegral K[X] _
  haveI : IsIntegrallyClosed (AdjoinRoot G) :=
    SmoothNormal.isIntegrallyClosed_of_smooth K (AdjoinRoot G)
  exact (isDedekindDomain_iff _ (FractionRing (AdjoinRoot G))).mpr ⟨inferInstance,
    inferInstance, inferInstance,
    fun hx ↦ (isIntegrallyClosed_iff (FractionRing (AdjoinRoot G))).mp inferInstance hx⟩

end Smooth

/-- Dedekind domains are stable under ring isomorphisms. -/
theorem isDedekindDomain_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsDedekindDomain B] (e : A ≃+* B) : IsDedekindDomain A := by
  haveI : IsDomain A := MulEquiv.isDomain B e.toMulEquiv
  haveI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv B e.symm
  haveI : Ring.DimensionLEOne A := Ring.DimensionLEOne.of_ringEquiv e
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.symm
  exact (isDedekindDomain_iff A (FractionRing A)).mpr ⟨inferInstance, inferInstance,
    inferInstance, fun hx ↦ (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance hx⟩

/-- **Flatness over a Dedekind domain integral over a domain.** If `T` is a Dedekind domain,
integral over the domain `R`, then every `T`-module `B` which is flat over `R` is flat over `T`:
a nonzero `s ∈ T` divides a nonzero `r ∈ R` (`IsIntegral.comap_ne_bot`), so `T`-torsion of `B`
is `R`-torsion, and `B` is `R`-torsion free (`IsDedekindDomain.flat_iff_torsion_eq_bot`). -/
theorem flat_of_isIntegral (R T B : Type*) [CommRing R] [IsDomain R] [CommRing T]
    [IsDedekindDomain T] [Algebra R T] [Algebra.IsIntegral R T] [AddCommGroup B] [Module R B]
    [Module T B] [IsScalarTower R T B] [Module.Flat R B] : Module.Flat T B := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule.eq_bot_iff]
  intro b hb
  obtain ⟨⟨s, hs⟩, hsb⟩ := (Submodule.mem_torsion_iff b).mp hb
  have hsb' : s • b = 0 := hsb
  have hI : Ideal.span {s} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hs
  obtain ⟨r, hr, hr0⟩ := (Submodule.ne_bot_iff _).mp (Ideal.IsIntegral.comap_ne_bot R hI)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hr)
  have hrb : r • b = r • 0 := by
    rw [smul_zero, ← algebraMap_smul T r b, ← hu, mul_smul, hsb', smul_zero]
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr0) hrb

section BaseChange

variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [CommRing K] [IsDomain K] [Algebra O K]
  {G : O[X][X]}
  {q : K[X][X]} (hq : G.map (mapRingHom (algebraMap O K)) = q)

/-- The base change map `O[X][Y]/(G) → K[X][Y]/(G_K)`. -/
abbrev baseMap : AdjoinRoot G →+* AdjoinRoot q :=
  AdjoinRoot.map (mapRingHom (algebraMap O K)) G q (by rw [hq])

omit [IsDomain O] [IsDomain K] in
lemma baseMap_mk (p : O[X][X]) :
    baseMap hq (AdjoinRoot.mk G p) = AdjoinRoot.mk q (p.map (mapRingHom (algebraMap O K))) := by
  have : (baseMap hq).comp (AdjoinRoot.mk G) =
      (AdjoinRoot.mk q).comp (mapRingHom (mapRingHom (algebraMap O K))) :=
    Polynomial.ringHom_ext (fun a ↦ by simp [AdjoinRoot.mk_C]) (by simp [AdjoinRoot.mk_X])
  exact congrArg (fun f ↦ f p) this

omit [IsDomain O] [IsDomain K] in
lemma baseMap_algebraMap (o : O) :
    baseMap hq (algebraMap O (AdjoinRoot G) o) =
      algebraMap K (AdjoinRoot q) (algebraMap O K o) := by
  simp [AdjoinRoot.algebraMap_eq', Polynomial.algebraMap_eq]

variable (M : Submonoid O) [IsLocalization M K]

/-- **Base change of a monic plane curve to a localization**: `K[X][Y]/(G_K)` is the localization
of `O[X][Y]/(G)` at the image of `M`. -/
theorem isLocalization_adjoinRoot_map (hM : M ≤ nonZeroDivisors O) (hG : G.Monic) :
    letI := (baseMap hq).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (AdjoinRoot G) M) (AdjoinRoot q) := by
  letI := (baseMap hq).toAlgebra
  set F := baseMap hq
  have hF : ∀ a, algebraMap (AdjoinRoot G) (AdjoinRoot q) a = F a := fun _ ↦ rfl
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' := AdjoinRoot.mk_leftInverse hG a
    set p := AdjoinRoot.modByMonicHom hG a
    have hp : p.degree < G.degree := by
      induction a using AdjoinRoot.induction_on with
      | ih p₀ =>
        simp only [p, AdjoinRoot.modByMonicHom_mk]
        exact degree_modByMonic_lt _ hG
    rw [← ha', baseMap_mk, AdjoinRoot.mk_eq_zero] at ha
    have hφ : Function.Injective (mapRingHom (algebraMap O K)) :=
      Polynomial.map_injective _ (IsLocalization.injective K hM)
    have hdeg : (p.map (mapRingHom (algebraMap O K))).degree < q.degree := by
      rw [← hq, hG.degree_map]
      exact (degree_map_le).trans_lt hp
    have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt ha hdeg
    rw [← Polynomial.map_zero (mapRingHom (algebraMap O K))] at h0
    rw [← ha', Polynomial.map_injective _ hφ h0, map_zero]
  rw [isLocalization_iff]
  refine ⟨?_, ?_, fun {a b} hab ↦ ⟨1, by rw [hinj hab]⟩⟩
  · rintro ⟨_, m, hm, rfl⟩
    rw [hF, baseMap_algebraMap]
    exact (IsLocalization.map_units K ⟨m, hm⟩).map _
  · -- every element has the form `F a / m`
    let P : AdjoinRoot q → Prop := fun z ↦
      ∃ a : AdjoinRoot G, ∃ m ∈ M, z * F (algebraMap O _ m) = F a
    have hFP : ∀ a, P (F a) := fun a ↦ ⟨a, 1, M.one_mem, by rw [map_one, map_one, mul_one]⟩
    have hadd : ∀ z₁ z₂, P z₁ → P z₂ → P (z₁ + z₂) := by
      rintro z₁ z₂ ⟨a₁, m₁, hm₁, h₁⟩ ⟨a₂, m₂, hm₂, h₂⟩
      refine ⟨a₁ * algebraMap O _ m₂ + a₂ * algebraMap O _ m₁, m₁ * m₂, M.mul_mem hm₁ hm₂, ?_⟩
      simp only [map_mul, map_add]
      linear_combination F (algebraMap O (AdjoinRoot G) m₂) * h₁ +
        F (algebraMap O (AdjoinRoot G) m₁) * h₂
    have hmul : ∀ z₁ z₂, P z₁ → P z₂ → P (z₁ * z₂) := by
      rintro z₁ z₂ ⟨a₁, m₁, hm₁, h₁⟩ ⟨a₂, m₂, hm₂, h₂⟩
      refine ⟨a₁ * a₂, m₁ * m₂, M.mul_mem hm₁ hm₂, ?_⟩
      simp only [map_mul]
      linear_combination z₁ * F (algebraMap O (AdjoinRoot G) m₁) * h₂ + F a₂ * h₁
    have hK : ∀ k : K, P (AdjoinRoot.of q (C k)) := by
      intro k
      obtain ⟨⟨o, m⟩, hk⟩ := IsLocalization.surj M k
      simp only at hk
      refine ⟨algebraMap O _ o, m, m.2, ?_⟩
      rw [baseMap_algebraMap, baseMap_algebraMap, AdjoinRoot.algebraMap_eq']
      simp only [RingHom.comp_apply, Polynomial.algebraMap_eq]
      rw [← map_mul, ← map_mul, hk]
    have hX : P (AdjoinRoot.of q X) := by
      have := hFP (AdjoinRoot.of G X)
      simpa [F] using this
    have hroot : P (AdjoinRoot.root q) := by
      have := hFP (AdjoinRoot.root G)
      simpa [F] using this
    have hpow : ∀ z n, P z → P (z ^ n) := by
      intro z n hz
      induction n with
      | zero => simpa using hFP 1
      | succ n ih => rw [pow_succ]; exact hmul _ _ ih hz
    intro z
    induction z using AdjoinRoot.induction_on with
    | ih p =>
    suffices P (AdjoinRoot.mk q p) by
      obtain ⟨a, m, hm, h⟩ := this
      exact ⟨⟨a, ⟨_, m, hm, rfl⟩⟩, h⟩
    induction p using Polynomial.induction_on with
    | C a =>
      rw [AdjoinRoot.mk_C]
      induction a using Polynomial.induction_on with
      | C k => exact hK k
      | add f g hf hg => rw [map_add]; exact hadd _ _ hf hg
      | monomial n k ih =>
        rw [pow_succ, ← mul_assoc, map_mul]
        exact hmul _ _ ih hX
    | add f g hf hg => rw [map_add]; exact hadd _ _ hf hg
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
      exact hmul _ _ ih hroot

end BaseChange

end PlaneCurve

/-- For a discrete valuation ring `O` and a nonzero nonunit `ϖ`, `Frac O = O[1/ϖ]`. -/
theorem isLocalization_away_fractionRing {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (h0 : ϖ ≠ 0) (hu : ¬IsUnit ϖ) :
    IsLocalization.Away ϖ (FractionRing O) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨b, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hp
  have hb : b ≠ 0 := by
    rintro rfl
    exact hu (by rw [hv, pow_zero, mul_one]; exact v.isUnit)
  have hdvd : ∀ n ∈ nonZeroDivisors O, ∃ m ∈ Submonoid.powers ϖ, n ∣ m := by
    intro n hn
    obtain ⟨a, u, hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hn) hp
    refine ⟨ϖ ^ a, ⟨a, rfl⟩, ?_⟩
    rw [hu', Units.mul_left_dvd, hv, mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_left (pow_dvd_pow p (Nat.le_mul_of_pos_left a (Nat.pos_of_ne_zero hb))) _
  haveI : IsFractionRing O (Localization.Away ϖ) :=
    IsLocalization.of_le_of_exists_dvd (Submonoid.powers ϖ) _
      (powers_le_nonZeroDivisors_of_noZeroDivisors h0) hdvd
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers ϖ)
    (IsLocalization.algEquiv (nonZeroDivisors O) (Localization.Away ϖ) (FractionRing O))

namespace TateTwoChart

/-! ### The Jacobian certificates -/

section Certificate

variable {S : Type*} [CommRing S]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
-- the certificates are large polynomials
/-- The coefficient of `∂_h G0` in the Jacobian certificate of the chart `T0`. -/
def cert0a (π b₄ t _κ b₆ x y : S) : S :=
  (-b₆ + b₄ ^ 2 * π ^ 2 - x * b₆ - 432 * π ^ 2 * b₆ ^ 2 - 64 * b₄ ^ 3 * π ^ 4 - 3 * b₆ ^ 2 * y ^ 2 +
    x * b₄ ^ 2 * π ^ 2 - π * y * t ^ 4 - π * t ^ 5 * y ^ 2 - b₆ * t ^ 2 * y ^ 2 : S) +
  (-972 * π ^ 2 * b₆ ^ 3 * y ^ 2 - 378 * x * π ^ 2 * b₆ ^ 2 - 192 * b₄ ^ 4 * x ^ 2 * π ^ 6 - 58 * x
    * b₄ ^ 3 * π ^ 4 - 9 * π * y * b₆ ^ 2 - 4 * y * b₄ ^ 3 * π ^ 3 - 2 * b₆ * t * y + 3 * x ^ 2 * π
    ^ 2 * t ^ 4 + 6 * x * π ^ 2 * t ^ 4 + 6 * b₄ ^ 3 * x ^ 2 * π ^ 4 : S) +
  (27 * x ^ 2 * π ^ 2 * b₆ ^ 2 + 72 * b₄ * b₆ * π ^ 2 + 192 * y * b₄ ^ 4 * π ^ 5 + b₄ ^ 2 * π ^ 2 *
    t ^ 2 * y ^ 2 - x * π * y * t ^ 4 - 2592 * t * x ^ 2 * π ^ 3 * b₆ ^ 2 - 1944 * x * y * π ^ 3 *
    b₆ ^ 3 - 1296 * b₄ * x ^ 2 * π ^ 4 * b₆ ^ 2 - 648 * π ^ 2 * b₆ ^ 2 * t ^ 2 * y ^ 2 - 432 * t * y
    * π ^ 2 * b₆ ^ 2 : S) +
  (-384 * t * b₄ ^ 3 * x ^ 2 * π ^ 5 - 288 * b₄ * x * π ^ 4 * t ^ 4 - 216 * b₆ * y * b₄ ^ 2 * π ^ 3
    - 192 * b₄ ^ 2 * π ^ 4 * t ^ 4 * y ^ 2 - 144 * b₄ * x ^ 2 * π ^ 4 * t ^ 4 - 144 * b₆ * y * π ^ 2
    * t ^ 3 - 144 * b₆ * b₄ ^ 3 * π ^ 4 * y ^ 2 - 108 * x * b₆ * π ^ 2 * t ^ 2 - 108 * b₆ * π ^ 2 *
    t ^ 4 * y ^ 2 - 96 * x * b₄ ^ 5 * π ^ 6 * y ^ 2 : S) +
  (-64 * t * y * b₄ ^ 3 * π ^ 4 - 54 * b₆ * x ^ 2 * π ^ 2 * t ^ 2 - 24 * b₄ * x * π ^ 3 * t ^ 3 - 24
    * y * b₄ ^ 2 * π ^ 3 * t ^ 2 - 24 * b₄ ^ 2 * π ^ 3 * t ^ 3 * y ^ 2 - 15 * x * t * b₄ ^ 2 * π ^ 3
    - 12 * b₄ * x ^ 2 * π ^ 3 * t ^ 3 - 9 * x * π * y * b₆ ^ 2 - 6 * b₄ * b₆ * x ^ 2 * π ^ 2 - 4 * t
    * b₄ ^ 3 * π ^ 3 * y ^ 2 : S) +
  (-3 * x * b₆ * t * y - 3 * x * y * b₄ ^ 3 * π ^ 3 - 3 * π * b₆ * t * x ^ 2 - 2 * x * π * t ^ 5 * y
    ^ 2 - 2 * x * b₆ * t ^ 2 * y ^ 2 + 2 * x * b₄ ^ 4 * π ^ 4 * y ^ 2 + 2 * t * y * b₄ ^ 2 * π ^ 2 +
    3 * b₆ * b₄ ^ 2 * π ^ 2 * y ^ 2 + 3 * t * b₄ ^ 2 * x ^ 2 * π ^ 3 + 3 * y * x ^ 2 * π ^ 2 * t ^ 5
    : S) +
  (4 * b₄ * π * b₆ * y + 4 * b₄ * y * π ^ 2 * t ^ 3 + 6 * π * b₆ * t ^ 3 * y ^ 2 + 7 * b₄ * π ^ 2 *
    t ^ 4 * y ^ 2 + 9 * π * y * x ^ 2 * b₆ ^ 2 + 15 * x * π * b₆ * t + 18 * x * π ^ 2 * t ^ 6 * y ^
    2 + 18 * π * b₆ * y * t ^ 2 + 24 * x * y * π ^ 2 * t ^ 5 + 27 * π * t * b₆ ^ 2 * y ^ 2 : S) +
  (48 * b₄ * y * π ^ 3 * t ^ 4 + 48 * b₄ * π ^ 3 * t ^ 5 * y ^ 2 + 66 * b₄ * x * b₆ * π ^ 2 + 72 *
    b₄ ^ 2 * x ^ 2 * π ^ 4 * t ^ 2 + 144 * x * b₄ ^ 2 * π ^ 4 * t ^ 2 + 152 * x * y * b₄ ^ 4 * π ^ 5
    + 171 * b₄ * π ^ 2 * b₆ ^ 2 * y ^ 2 + 192 * t * b₄ ^ 4 * π ^ 5 * y ^ 2 + 216 * b₆ * b₄ ^ 2 * x ^
    2 * π ^ 4 + 432 * b₆ * x ^ 2 * π ^ 3 * t ^ 3 : S) +
  (576 * x * t * b₄ ^ 3 * π ^ 5 + 864 * x * b₆ * π ^ 3 * t ^ 3 + 1296 * b₄ * y * π ^ 3 * b₆ ^ 2 +
    2916 * y * x ^ 2 * π ^ 3 * b₆ ^ 3 + 3888 * x * t * π ^ 3 * b₆ ^ 2 - 1944 * x * t * π ^ 3 * b₆ ^
    3 * y ^ 2 - 1152 * b₄ * x * y * π ^ 4 * t ^ 5 - 864 * b₄ * x * π ^ 4 * t ^ 6 * y ^ 2 - 864 * x *
    t * y * π ^ 2 * b₆ ^ 2 - 720 * b₄ * x * b₆ * t * π ^ 3 : S) +
  (-648 * x * b₄ ^ 2 * π ^ 4 * b₆ ^ 2 * y ^ 2 - 648 * y * x ^ 2 * π ^ 3 * b₆ ^ 2 * t ^ 2 - 513 * b₄
    * y * x ^ 2 * π ^ 3 * b₆ ^ 2 - 504 * x * b₆ * y * π ^ 2 * t ^ 3 - 486 * x * π ^ 2 * b₆ ^ 2 * t ^
    2 * y ^ 2 - 396 * x * b₆ * π ^ 2 * t ^ 4 * y ^ 2 - 384 * y * b₄ ^ 3 * x ^ 2 * π ^ 5 * t ^ 2 -
    288 * x * b₆ * y * b₄ ^ 3 * π ^ 5 - 264 * b₆ * t * b₄ ^ 2 * π ^ 3 * y ^ 2 - 192 * t * y * b₄ ^ 4
    * x ^ 2 * π ^ 6 : S) +
  (-168 * x * b₆ * y * b₄ ^ 2 * π ^ 3 - 144 * b₄ * y * x ^ 2 * π ^ 4 * t ^ 5 - 128 * x * t * y * b₄
    ^ 3 * π ^ 4 - 81 * t * y * x ^ 2 * π ^ 2 * b₆ ^ 2 - 48 * x * y * b₄ ^ 2 * π ^ 3 * t ^ 2 - 47 * x
    * b₄ ^ 2 * π ^ 3 * t ^ 3 * y ^ 2 - 42 * b₄ * x * y * π ^ 3 * t ^ 4 - 42 * x * b₄ ^ 3 * π ^ 4 * t
    ^ 2 * y ^ 2 - 21 * b₄ * y * x ^ 2 * π ^ 3 * t ^ 4 - 18 * b₆ * y * x ^ 2 * π ^ 2 * t ^ 3 : S) +
  (-9 * x * π * t * b₆ ^ 2 * y ^ 2 - 9 * b₆ * y * b₄ ^ 2 * x ^ 2 * π ^ 3 - 4 * x * t * b₄ ^ 3 * π ^
    3 * y ^ 2 - 3 * π * b₆ * y * x ^ 2 * t ^ 2 - 2 * x * b₆ * b₄ ^ 2 * π ^ 2 * y ^ 2 + 2 * x * b₄ ^
    2 * π ^ 2 * t ^ 2 * y ^ 2 + 3 * b₄ * x * π * b₆ * y + 3 * x * t * y * b₄ ^ 2 * π ^ 2 + 3 * y *
    b₄ ^ 2 * x ^ 2 * π ^ 3 * t ^ 2 + 4 * b₄ * x * y * π ^ 2 * t ^ 3 : S) +
  (4 * b₄ * π * b₆ * t * y ^ 2 + 6 * t * y * b₄ ^ 3 * x ^ 2 * π ^ 4 + 10 * b₄ * x * π ^ 2 * t ^ 4 *
    y ^ 2 + 24 * x * b₄ ^ 2 * π ^ 4 * t ^ 4 * y ^ 2 + 27 * x * π * b₆ * t ^ 3 * y ^ 2 + 30 * b₄ * b₆
    * π ^ 2 * t ^ 2 * y ^ 2 + 42 * b₄ * x * π ^ 3 * t ^ 5 * y ^ 2 + 42 * x * π * b₆ * y * t ^ 2 + 72
    * y * b₄ ^ 2 * x ^ 2 * π ^ 4 * t ^ 3 + 84 * b₄ * b₆ * t * y * π ^ 2 : S) +
  (114 * x * b₆ * b₄ ^ 3 * π ^ 4 * y ^ 2 + 168 * x * t * b₄ ^ 4 * π ^ 5 * y ^ 2 + 324 * b₆ * y * x ^
    2 * π ^ 3 * t ^ 4 + 384 * x * b₄ ^ 3 * π ^ 5 * t ^ 3 * y ^ 2 + 396 * b₄ * b₆ * t * x ^ 2 * π ^ 3
    + 432 * b₆ * y * b₄ ^ 3 * x ^ 2 * π ^ 5 + 480 * x * y * b₄ ^ 2 * π ^ 4 * t ^ 3 + 576 * b₄ * b₆ *
    π ^ 3 * t ^ 3 * y ^ 2 + 576 * x * y * b₄ ^ 3 * π ^ 5 * t ^ 2 + 576 * y * b₄ ^ 2 * x ^ 2 * π ^ 5
    * t ^ 4 : S) +
  (1296 * b₄ * t * π ^ 3 * b₆ ^ 2 * y ^ 2 + 1350 * b₄ * x * y * π ^ 3 * b₆ ^ 2 + 1944 * x * b₆ * π ^
    3 * t ^ 5 * y ^ 2 + 3240 * x * b₆ * y * π ^ 3 * t ^ 4 + 3888 * x * y * π ^ 3 * b₆ ^ 2 * t ^ 2 -
    1728 * b₄ * b₆ * y * x ^ 2 * π ^ 4 * t ^ 3 - 1296 * b₄ * t * y * x ^ 2 * π ^ 4 * b₆ ^ 2 - 828 *
    b₄ * x * b₆ * y * π ^ 3 * t ^ 2 - 432 * x * b₆ * b₄ ^ 2 * π ^ 4 * t ^ 2 * y ^ 2 - 288 * x * b₆ *
    t * b₄ ^ 3 * π ^ 5 * y ^ 2 : S) +
  (-201 * x * b₆ * t * b₄ ^ 2 * π ^ 3 * y ^ 2 - 6 * b₄ * b₆ * t * y * x ^ 2 * π ^ 2 + 4 * b₄ * x * π
    * b₆ * t * y ^ 2 + 78 * b₄ * x * b₆ * π ^ 2 * t ^ 2 * y ^ 2 + 108 * b₄ * x * b₆ * π ^ 3 * t ^ 3
    * y ^ 2 + 156 * b₄ * x * b₆ * t * y * π ^ 2 + 342 * b₄ * b₆ * y * x ^ 2 * π ^ 3 * t ^ 2 + 360 *
    b₆ * t * y * b₄ ^ 2 * x ^ 2 * π ^ 4 + 864 * b₄ * x * b₆ * π ^ 4 * t ^ 4 * y ^ 2 + 1674 * b₄ * x
    * t * π ^ 3 * b₆ ^ 2 * y ^ 2 : S)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
-- the certificates are large polynomials
/-- The coefficient of `∂_z G0` in the Jacobian certificate of the chart `T0`. -/
def cert0b (π b₄ t _κ b₆ x y : S) : S :=
  (-3 * b₄ ^ 2 * π ^ 3 - 2 * b₆ * y + 3 * π * b₆ + 192 * b₄ ^ 3 * π ^ 5 + 1296 * π ^ 3 * b₆ ^ 2 -
    1944 * π ^ 3 * b₆ ^ 3 * y ^ 2 - 1296 * x * π ^ 3 * b₆ ^ 2 - 702 * y * π ^ 2 * b₆ ^ 2 - 216 * b₄
    * b₆ * π ^ 3 - 192 * x * b₄ ^ 3 * π ^ 5 : S) +
  (-110 * y * b₄ ^ 3 * π ^ 4 - 96 * b₄ ^ 5 * π ^ 6 * y ^ 3 - 9 * π * b₆ ^ 2 * y ^ 2 - 4 * b₆ * t * y
    ^ 2 - 4 * b₄ ^ 3 * π ^ 3 * y ^ 2 - 3 * x * π * b₆ - 2 * π * t ^ 4 * y ^ 2 - 2 * π * t ^ 5 * y ^
    3 - 2 * b₆ * t ^ 2 * y ^ 3 + 2 * y * b₄ ^ 2 * π ^ 2 : S) +
  (2 * b₄ ^ 4 * π ^ 4 * y ^ 3 + 3 * x * b₄ ^ 2 * π ^ 3 + 18 * y * π ^ 2 * t ^ 4 + 18 * π ^ 2 * t ^ 6
    * y ^ 3 + 36 * π ^ 2 * t ^ 5 * y ^ 2 + 200 * b₄ ^ 4 * π ^ 5 * y ^ 2 - 1944 * t * π ^ 3 * b₆ ^ 3
    * y ^ 3 - 1728 * b₄ * π ^ 4 * t ^ 5 * y ^ 2 - 1188 * t * π ^ 2 * b₆ ^ 2 * y ^ 2 - 864 * b₄ * y *
    π ^ 4 * t ^ 4 : S) +
  (-864 * b₄ * π ^ 4 * t ^ 6 * y ^ 3 - 720 * b₆ * π ^ 2 * t ^ 3 * y ^ 2 - 648 * b₄ ^ 2 * π ^ 4 * b₆
    ^ 2 * y ^ 3 - 486 * π ^ 2 * b₆ ^ 2 * t ^ 2 * y ^ 3 - 396 * b₆ * π ^ 2 * t ^ 4 * y ^ 3 - 324 * b₆
    * y * π ^ 2 * t ^ 2 - 288 * b₆ * b₄ ^ 3 * π ^ 5 * y ^ 2 - 225 * b₆ * b₄ ^ 2 * π ^ 3 * y ^ 2 -
    192 * x * y * b₄ ^ 4 * π ^ 6 - 164 * t * b₄ ^ 3 * π ^ 4 * y ^ 2 : S) +
  (-72 * b₄ * y * π ^ 3 * t ^ 3 - 69 * b₄ ^ 2 * π ^ 3 * t ^ 2 * y ^ 2 - 47 * b₄ ^ 2 * π ^ 3 * t ^ 3
    * y ^ 3 - 42 * b₄ ^ 3 * π ^ 4 * t ^ 2 * y ^ 3 - 33 * t * y * b₄ ^ 2 * π ^ 3 - 30 * b₄ * π ^ 3 *
    t ^ 4 * y ^ 2 - 9 * π * t * b₆ ^ 2 * y ^ 3 - 4 * t * b₄ ^ 3 * π ^ 3 * y ^ 3 - 2 * b₆ * b₄ ^ 2 *
    π ^ 2 * y ^ 3 + 2 * b₄ ^ 2 * π ^ 2 * t ^ 2 * y ^ 3 : S) +
  (3 * x * y * π ^ 2 * t ^ 4 + 3 * x * π ^ 2 * t ^ 5 * y ^ 2 + 4 * b₄ * π * b₆ * y ^ 2 + 4 * t * b₄
    ^ 2 * π ^ 2 * y ^ 2 + 6 * x * y * b₄ ^ 3 * π ^ 4 + 8 * b₄ * π ^ 2 * t ^ 3 * y ^ 2 + 9 * x * π *
    b₆ ^ 2 * y ^ 2 + 10 * b₄ * π ^ 2 * t ^ 4 * y ^ 3 + 24 * b₄ ^ 2 * π ^ 4 * t ^ 4 * y ^ 3 + 27 * x
    * y * π ^ 2 * b₆ ^ 2 : S) +
  (27 * π * b₆ * t ^ 3 * y ^ 3 + 33 * π * b₆ * t * y + 42 * b₄ * π ^ 3 * t ^ 5 * y ^ 3 + 57 * π * b₆
    * t ^ 2 * y ^ 2 + 114 * b₆ * b₄ ^ 3 * π ^ 4 * y ^ 3 + 126 * b₄ * b₆ * y * π ^ 2 + 168 * t * b₄ ^
    4 * π ^ 5 * y ^ 3 + 216 * b₄ * x * b₆ * π ^ 3 + 384 * b₄ ^ 3 * π ^ 5 * t ^ 3 * y ^ 3 + 432 * y *
    b₄ ^ 2 * π ^ 4 * t ^ 2 : S) +
  (576 * b₄ ^ 2 * π ^ 4 * t ^ 3 * y ^ 2 + 768 * b₄ ^ 3 * π ^ 5 * t ^ 2 * y ^ 2 + 960 * t * y * b₄ ^
    3 * π ^ 5 + 1674 * b₄ * π ^ 3 * b₆ ^ 2 * y ^ 2 + 1944 * b₆ * π ^ 3 * t ^ 5 * y ^ 3 + 2592 * b₆ *
    y * π ^ 3 * t ^ 3 + 2916 * x * π ^ 3 * b₆ ^ 3 * y ^ 2 + 4536 * b₆ * π ^ 3 * t ^ 4 * y ^ 2 + 5184
    * π ^ 3 * b₆ ^ 2 * t ^ 2 * y ^ 2 + 6480 * t * y * π ^ 3 * b₆ ^ 2 : S) +
  (-3888 * x * t * y * π ^ 3 * b₆ ^ 2 - 1296 * b₄ * x * y * π ^ 4 * b₆ ^ 2 - 1296 * b₄ * b₆ * t * y
    * π ^ 3 - 972 * b₄ * b₆ * π ^ 3 * t ^ 2 * y ^ 2 - 648 * x * π ^ 3 * b₆ ^ 2 * t ^ 2 * y ^ 2 - 576
    * x * t * y * b₄ ^ 3 * π ^ 5 - 513 * b₄ * x * π ^ 3 * b₆ ^ 2 * y ^ 2 - 432 * b₆ * b₄ ^ 2 * π ^ 4
    * t ^ 2 * y ^ 3 - 384 * x * b₄ ^ 3 * π ^ 5 * t ^ 2 * y ^ 2 - 288 * b₆ * t * b₄ ^ 3 * π ^ 5 * y ^
    3 : S) +
  (-201 * b₆ * t * b₄ ^ 2 * π ^ 3 * y ^ 3 - 192 * x * t * b₄ ^ 4 * π ^ 6 * y ^ 2 - 144 * b₄ * x * y
    * π ^ 4 * t ^ 4 - 144 * b₄ * x * π ^ 4 * t ^ 5 * y ^ 2 - 81 * x * t * π ^ 2 * b₆ ^ 2 * y ^ 2 -
    54 * x * b₆ * y * π ^ 2 * t ^ 2 - 21 * b₄ * x * π ^ 3 * t ^ 4 * y ^ 2 - 18 * x * b₆ * π ^ 2 * t
    ^ 3 * y ^ 2 - 12 * b₄ * x * y * π ^ 3 * t ^ 3 - 9 * x * b₆ * b₄ ^ 2 * π ^ 3 * y ^ 2 : S) +
  (-6 * b₄ * x * b₆ * y * π ^ 2 - 6 * x * π * b₆ * t * y - 3 * x * π * b₆ * t ^ 2 * y ^ 2 + 3 * x *
    b₄ ^ 2 * π ^ 3 * t ^ 2 * y ^ 2 + 4 * b₄ * π * b₆ * t * y ^ 3 + 6 * x * t * y * b₄ ^ 2 * π ^ 3 +
    6 * x * t * b₄ ^ 3 * π ^ 4 * y ^ 2 + 72 * x * y * b₄ ^ 2 * π ^ 4 * t ^ 2 + 72 * x * b₄ ^ 2 * π ^
    4 * t ^ 3 * y ^ 2 + 78 * b₄ * b₆ * π ^ 2 * t ^ 2 * y ^ 3 : S) +
  (108 * b₄ * b₆ * π ^ 3 * t ^ 3 * y ^ 3 + 204 * b₄ * b₆ * t * π ^ 2 * y ^ 2 + 216 * x * b₆ * y * b₄
    ^ 2 * π ^ 4 + 324 * x * b₆ * π ^ 3 * t ^ 4 * y ^ 2 + 432 * x * b₆ * y * π ^ 3 * t ^ 3 + 432 * x
    * b₆ * b₄ ^ 3 * π ^ 5 * y ^ 2 + 576 * x * b₄ ^ 2 * π ^ 5 * t ^ 4 * y ^ 2 + 864 * b₄ * b₆ * π ^ 4
    * t ^ 4 * y ^ 3 + 1674 * b₄ * t * π ^ 3 * b₆ ^ 2 * y ^ 3 - 1728 * b₄ * x * b₆ * π ^ 4 * t ^ 3 *
    y ^ 2 : S) +
  (-1296 * b₄ * x * t * π ^ 4 * b₆ ^ 2 * y ^ 2 - 6 * b₄ * x * b₆ * t * π ^ 2 * y ^ 2 + 342 * b₄ * x
    * b₆ * π ^ 3 * t ^ 2 * y ^ 2 + 360 * x * b₆ * t * b₄ ^ 2 * π ^ 4 * y ^ 2 + 612 * b₄ * x * b₆ * t
    * y * π ^ 3 : S)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
-- the certificates are large polynomials
/-- The coefficient of `G0` in the Jacobian certificate of the chart `T0`. -/
def cert0c (π b₄ t _κ b₆ x y : S) : S :=
  (3 * b₆ - 18 * π ^ 2 * t ^ 4 - 3 * b₄ ^ 2 * π ^ 2 + 174 * b₄ ^ 3 * π ^ 4 + 1134 * π ^ 2 * b₆ ^ 2 -
    11664 * t * π ^ 3 * b₆ ^ 2 - 2592 * b₆ * π ^ 3 * t ^ 3 - 1728 * t * b₄ ^ 3 * π ^ 5 - 456 * y *
    b₄ ^ 4 * π ^ 5 - 432 * b₄ ^ 2 * π ^ 4 * t ^ 2 : S) +
  (-198 * b₄ * b₆ * π ^ 2 - 81 * x * π ^ 2 * b₆ ^ 2 - 72 * y * π ^ 2 * t ^ 5 - 54 * π ^ 2 * t ^ 6 *
    y ^ 2 - 45 * π * b₆ * t - 18 * x * b₄ ^ 3 * π ^ 4 - 9 * x * π ^ 2 * t ^ 4 - 6 * b₄ ^ 4 * π ^ 4 *
    y ^ 2 + 3 * π * y * t ^ 4 + 6 * π * t ^ 5 * y ^ 2 : S) +
  (6 * b₆ * t ^ 2 * y ^ 2 + 9 * b₆ * t * y + 9 * y * b₄ ^ 3 * π ^ 3 + 27 * π * y * b₆ ^ 2 + 45 * t *
    b₄ ^ 2 * π ^ 3 + 72 * b₄ * π ^ 3 * t ^ 3 + 288 * b₄ ^ 5 * π ^ 6 * y ^ 2 + 324 * b₆ * π ^ 2 * t ^
    2 + 576 * x * b₄ ^ 4 * π ^ 6 + 864 * b₄ * π ^ 4 * t ^ 4 : S) +
  (5832 * y * π ^ 3 * b₆ ^ 3 - 11664 * y * π ^ 3 * b₆ ^ 2 * t ^ 2 - 9720 * b₆ * y * π ^ 3 * t ^ 4 -
    8748 * x * y * π ^ 3 * b₆ ^ 3 - 5832 * b₆ * π ^ 3 * t ^ 5 * y ^ 2 - 4050 * b₄ * y * π ^ 3 * b₆ ^
    2 - 1728 * y * b₄ ^ 3 * π ^ 5 * t ^ 2 - 1440 * y * b₄ ^ 2 * π ^ 4 * t ^ 3 - 1296 * x * b₆ * π ^
    3 * t ^ 3 - 1152 * b₄ ^ 3 * π ^ 5 * t ^ 3 * y ^ 2 : S) +
  (-648 * x * b₆ * b₄ ^ 2 * π ^ 4 - 504 * t * b₄ ^ 4 * π ^ 5 * y ^ 2 - 342 * b₆ * b₄ ^ 3 * π ^ 4 * y
    ^ 2 - 216 * x * b₄ ^ 2 * π ^ 4 * t ^ 2 - 126 * b₄ * π ^ 3 * t ^ 5 * y ^ 2 - 126 * π * b₆ * y * t
    ^ 2 - 81 * π * b₆ * t ^ 3 * y ^ 2 - 72 * b₄ ^ 2 * π ^ 4 * t ^ 4 * y ^ 2 - 30 * b₄ * π ^ 2 * t ^
    4 * y ^ 2 - 27 * x * π * y * b₆ ^ 2 : S) +
  (-12 * b₄ * y * π ^ 2 * t ^ 3 - 9 * b₄ * π * b₆ * y - 9 * x * t * b₄ ^ 2 * π ^ 3 - 9 * x * y * π ^
    2 * t ^ 5 - 9 * t * y * b₄ ^ 2 * π ^ 2 - 6 * b₄ ^ 2 * π ^ 2 * t ^ 2 * y ^ 2 + 6 * b₆ * b₄ ^ 2 *
    π ^ 2 * y ^ 2 + 9 * x * π * b₆ * t + 12 * t * b₄ ^ 3 * π ^ 3 * y ^ 2 + 18 * b₄ * x * b₆ * π ^ 2
    : S) +
  (27 * π * t * b₆ ^ 2 * y ^ 2 + 36 * b₄ * x * π ^ 3 * t ^ 3 + 126 * b₄ * y * π ^ 3 * t ^ 4 + 126 *
    b₄ ^ 3 * π ^ 4 * t ^ 2 * y ^ 2 + 141 * b₄ ^ 2 * π ^ 3 * t ^ 3 * y ^ 2 + 144 * y * b₄ ^ 2 * π ^ 3
    * t ^ 2 + 162 * x * b₆ * π ^ 2 * t ^ 2 + 384 * t * y * b₄ ^ 3 * π ^ 4 + 432 * b₄ * x * π ^ 4 * t
    ^ 4 + 504 * b₆ * y * b₄ ^ 2 * π ^ 3 : S) +
  (864 * b₆ * y * b₄ ^ 3 * π ^ 5 + 1152 * x * t * b₄ ^ 3 * π ^ 5 + 1188 * b₆ * π ^ 2 * t ^ 4 * y ^ 2
    + 1458 * π ^ 2 * b₆ ^ 2 * t ^ 2 * y ^ 2 + 1512 * b₆ * y * π ^ 2 * t ^ 3 + 1944 * b₄ ^ 2 * π ^ 4
    * b₆ ^ 2 * y ^ 2 + 2160 * b₄ * b₆ * t * π ^ 3 + 2592 * b₄ * π ^ 4 * t ^ 6 * y ^ 2 + 2592 * t * y
    * π ^ 2 * b₆ ^ 2 + 3456 * b₄ * y * π ^ 4 * t ^ 5 : S) +
  (3888 * b₄ * x * π ^ 4 * b₆ ^ 2 + 5832 * t * π ^ 3 * b₆ ^ 3 * y ^ 2 + 7776 * x * t * π ^ 3 * b₆ ^
    2 - 5022 * b₄ * t * π ^ 3 * b₆ ^ 2 * y ^ 2 - 2592 * b₄ * b₆ * π ^ 4 * t ^ 4 * y ^ 2 - 1728 * x *
    y * b₄ ^ 2 * π ^ 5 * t ^ 4 - 1296 * x * b₆ * y * b₄ ^ 3 * π ^ 5 - 1188 * b₄ * x * b₆ * t * π ^ 3
    - 972 * x * b₆ * y * π ^ 3 * t ^ 4 - 468 * b₄ * b₆ * t * y * π ^ 2 : S) +
  (-324 * b₄ * b₆ * π ^ 3 * t ^ 3 * y ^ 2 - 234 * b₄ * b₆ * π ^ 2 * t ^ 2 * y ^ 2 - 216 * x * y * b₄
    ^ 2 * π ^ 4 * t ^ 3 - 18 * x * t * y * b₄ ^ 3 * π ^ 4 - 12 * b₄ * π * b₆ * t * y ^ 2 - 9 * x * y
    * b₄ ^ 2 * π ^ 3 * t ^ 2 + 9 * x * π * b₆ * y * t ^ 2 + 27 * x * b₆ * y * b₄ ^ 2 * π ^ 3 + 54 *
    x * b₆ * y * π ^ 2 * t ^ 3 + 63 * b₄ * x * y * π ^ 3 * t ^ 4 : S) +
  (243 * x * t * y * π ^ 2 * b₆ ^ 2 + 432 * b₄ * x * y * π ^ 4 * t ^ 5 + 576 * x * t * y * b₄ ^ 4 *
    π ^ 6 + 603 * b₆ * t * b₄ ^ 2 * π ^ 3 * y ^ 2 + 864 * b₆ * t * b₄ ^ 3 * π ^ 5 * y ^ 2 + 1152 * x
    * y * b₄ ^ 3 * π ^ 5 * t ^ 2 + 1296 * b₆ * b₄ ^ 2 * π ^ 4 * t ^ 2 * y ^ 2 + 1539 * b₄ * x * y *
    π ^ 3 * b₆ ^ 2 + 1944 * x * y * π ^ 3 * b₆ ^ 2 * t ^ 2 + 2484 * b₄ * b₆ * y * π ^ 3 * t ^ 2 : S)
    +
  (-1080 * x * b₆ * t * y * b₄ ^ 2 * π ^ 4 - 1026 * b₄ * x * b₆ * y * π ^ 3 * t ^ 2 + 18 * b₄ * x *
    b₆ * t * y * π ^ 2 + 3888 * b₄ * x * t * y * π ^ 4 * b₆ ^ 2 + 5184 * b₄ * x * b₆ * y * π ^ 4 * t
    ^ 3 : S)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
-- the certificates are large polynomials
/-- The coefficient of `∂_h' G1` in the Jacobian certificate of the chart `T1`. -/
def cert1a (π b₄ t _κ b₆ x y : S) : S :=
  (2 * x * b₆ + 2 * b₆ * x ^ 2 + b₆ * t * y + y * b₄ ^ 3 * π ^ 3 - 64 * y * b₄ ^ 4 * π ^ 5 - 36 * π
    * y * b₆ ^ 2 - 8 * b₄ ^ 4 * π ^ 4 * y ^ 2 - 2 * x * b₄ ^ 2 * π ^ 2 - 2 * b₄ ^ 2 * x ^ 2 * π ^ 2
    + 6 * b₆ * t ^ 2 * y ^ 2 : S) +
  (12 * x * b₆ ^ 2 * y ^ 2 + 32 * b₄ ^ 3 * x ^ 2 * π ^ 4 + 80 * x * b₄ ^ 3 * π ^ 4 + 432 * x * π ^ 2
    * b₆ ^ 2 - b₄ * π * b₆ * y - t * y * b₄ ^ 2 * π ^ 2 - 96 * b₄ * x * b₆ * π ^ 2 - 96 * b₆ * b₄ ^
    3 * π ^ 4 * y ^ 2 - 48 * b₄ * b₆ * x ^ 2 * π ^ 2 - 6 * b₄ ^ 2 * π ^ 2 * t ^ 2 * y ^ 2 : S) +
  (8 * x * b₆ * t * y + 8 * b₆ * b₄ ^ 2 * π ^ 2 * y ^ 2 + 10 * x * y * b₄ ^ 3 * π ^ 3 + 14 * t * b₄
    ^ 3 * π ^ 3 * y ^ 2 + 16 * t * y * b₄ ^ 3 * π ^ 4 + 16 * y * b₄ ^ 3 * x ^ 2 * π ^ 3 + 72 * x * π
    * y * b₆ ^ 2 + 72 * π * t * b₆ ^ 2 * y ^ 2 + 96 * b₄ ^ 3 * π ^ 4 * t ^ 2 * y ^ 2 + 108 * b₆ * y
    * b₄ ^ 2 * π ^ 3 : S) +
  (144 * π * y * x ^ 2 * b₆ ^ 2 - 144 * b₄ * x * π ^ 2 * b₆ ^ 2 * y ^ 2 - 144 * b₄ * b₆ * π ^ 2 * t
    ^ 2 * y ^ 2 - 24 * b₄ * b₆ * t * y * π ^ 2 - 16 * b₄ * π * b₆ * y * x ^ 2 - 14 * b₄ * π * b₆ * t
    * y ^ 2 - 12 * x * b₆ * b₄ ^ 2 * π ^ 2 * y ^ 2 - 10 * b₄ * x * π * b₆ * y - 8 * x * t * y * b₄ ^
    2 * π ^ 2 + 16 * x * t * b₄ ^ 3 * π ^ 3 * y ^ 2 : S) +
  (24 * x * b₆ * y * b₄ ^ 2 * π ^ 3 + 72 * b₆ * t * b₄ ^ 2 * π ^ 3 * y ^ 2 + 128 * x * t * y * b₄ ^
    3 * π ^ 4 + 144 * x * π * t * b₆ ^ 2 * y ^ 2 - 192 * b₄ * x * b₆ * t * y * π ^ 2 - 16 * b₄ * x *
    π * b₆ * t * y ^ 2 : S)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
-- the certificates are large polynomials
/-- The coefficient of `∂_w G1` in the Jacobian certificate of the chart `T1`. -/
def cert1b (π b₄ t _κ b₆ x y : S) : S :=
  (b₆ * y + 12 * b₆ ^ 2 * y ^ 3 - y * b₄ ^ 2 * π ^ 2 - 4 * x * b₆ * y - 4 * b₆ * t * y ^ 2 - 4 * b₄
    ^ 3 * π ^ 3 * y ^ 2 + 64 * y * b₄ ^ 3 * π ^ 4 + 432 * y * π ^ 2 * b₆ ^ 2 - 144 * b₄ * π ^ 2 * b₆
    ^ 2 * y ^ 3 - 72 * b₄ * b₆ * y * π ^ 2 : S) +
  (-64 * x * y * b₄ ^ 3 * π ^ 4 - 64 * t * b₄ ^ 3 * π ^ 4 * y ^ 2 - 48 * b₆ * b₄ ^ 2 * π ^ 3 * y ^ 2
    - 12 * b₆ * b₄ ^ 2 * π ^ 2 * y ^ 3 + 4 * b₄ * π * b₆ * y ^ 2 + 4 * x * y * b₄ ^ 2 * π ^ 2 + 4 *
    t * b₄ ^ 2 * π ^ 2 * y ^ 2 + 16 * x * b₄ ^ 3 * π ^ 3 * y ^ 2 + 16 * t * b₄ ^ 3 * π ^ 3 * y ^ 3 +
    144 * x * π * b₆ ^ 2 * y ^ 2 : S) +
  (144 * π * t * b₆ ^ 2 * y ^ 3 - 16 * b₄ * x * π * b₆ * y ^ 2 - 16 * b₄ * π * b₆ * t * y ^ 3 + 96 *
    b₄ * x * b₆ * y * π ^ 2 + 96 * b₄ * b₆ * t * π ^ 2 * y ^ 2 : S)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
-- the certificates are large polynomials
/-- The coefficient of `G1` in the Jacobian certificate of the chart `T1`. -/
def cert1c (π b₄ t _κ b₆ x y : S) : S :=
  (-3 * b₆ - 1296 * π ^ 2 * b₆ ^ 2 - 192 * b₄ ^ 3 * π ^ 4 - 36 * b₆ ^ 2 * y ^ 2 + 3 * b₄ ^ 2 * π ^ 2
    + 216 * b₄ * b₆ * π ^ 2 - 432 * x * π * y * b₆ ^ 2 - 432 * π * t * b₆ ^ 2 * y ^ 2 - 48 * x * y *
    b₄ ^ 3 * π ^ 3 - 48 * t * b₄ ^ 3 * π ^ 3 * y ^ 2 : S) +
  (36 * b₆ * b₄ ^ 2 * π ^ 2 * y ^ 2 + 432 * b₄ * π ^ 2 * b₆ ^ 2 * y ^ 2 + 48 * b₄ * x * π * b₆ * y +
    48 * b₄ * π * b₆ * t * y ^ 2 : S)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
-- the certificates are large polynomials
/-- **The Jacobian certificate of the chart `T0`**: `a ∂ₕG₀ + b ∂_zG₀ + c G₀ = 3 π E κ`. -/
theorem cert0 (π b₄ t κ b₆ x y : S) (hκ : κ * (t ^ 2 - b₆) = 1) :
    cert0a π b₄ t κ b₆ x y * (κ * (t - π * b₄) * y ^ 2 + κ * y - 3 * κ * π * x ^ 2) +
      cert0b π b₄ t κ b₆ x y * (3 * y ^ 2 + 2 * κ * (2 * t + (t - π * b₄) * x) * y +
        κ * (1 + x)) +
      cert0c π b₄ t κ b₆ x y * (y ^ 3 + κ * (2 * t + (t - π * b₄) * x) * y ^ 2 +
        κ * (1 + x) * y - κ * π * x ^ 3) = 3 * π * TateNormal.tateE π b₄ b₆ * κ := by
  unfold cert0a cert0b cert0c TateNormal.tateE
  linear_combination (
    (3 * b₆ * y ^ 3 - 3888 * π ^ 3 * b₆ ^ 2 * y ^ 2 - 576 * b₄ ^ 3 * π ^ 5 * y ^ 2 - 144 * b₄ ^ 4 *
      π ^ 5 * y ^ 4 - 36 * π ^ 2 * t ^ 4 * y ^ 3 - 36 * π ^ 2 * t ^ 5 * y ^ 4 - 9 * π * b₆ * y ^ 2 -
      3 * b₄ ^ 2 * π ^ 2 * y ^ 3 + 3 * π * t ^ 4 * y ^ 4 + 3 * b₆ * t * y ^ 4 : S) +
    (3 * b₄ ^ 3 * π ^ 3 * y ^ 4 + 9 * b₄ ^ 2 * π ^ 3 * y ^ 2 + 156 * b₄ ^ 3 * π ^ 4 * y ^ 3 + 972 *
      π ^ 2 * b₆ ^ 2 * y ^ 3 - 7776 * t * π ^ 3 * b₆ ^ 2 * y ^ 3 - 5184 * b₆ * π ^ 3 * t ^ 3 * y ^ 3
      - 3888 * b₆ * π ^ 3 * t ^ 4 * y ^ 4 - 3888 * π ^ 3 * b₆ ^ 2 * t ^ 2 * y ^ 4 - 1152 * t * b₄ ^
      3 * π ^ 5 * y ^ 3 - 972 * b₄ * π ^ 3 * b₆ ^ 2 * y ^ 4 : S) +
    (-864 * b₄ ^ 2 * π ^ 4 * t ^ 2 * y ^ 3 - 576 * b₄ ^ 3 * π ^ 5 * t ^ 2 * y ^ 4 - 288 * b₄ ^ 2 * π
      ^ 4 * t ^ 3 * y ^ 4 - 180 * b₄ * b₆ * π ^ 2 * y ^ 3 - 54 * π * b₆ * t * y ^ 3 - 45 * π * b₆ *
      t ^ 2 * y ^ 4 - 36 * b₄ * π ^ 3 * t ^ 4 * y ^ 4 - 12 * b₄ * π ^ 2 * t ^ 3 * y ^ 4 - 9 * x * b₄
      ^ 2 * π ^ 3 * y ^ 2 - 3 * b₄ * π * b₆ * y ^ 4 : S) +
    (-3 * t * b₄ ^ 2 * π ^ 2 * y ^ 4 + 9 * x * π * b₆ * y ^ 2 + 54 * t * b₄ ^ 2 * π ^ 3 * y ^ 3 + 63
      * b₄ ^ 2 * π ^ 3 * t ^ 2 * y ^ 4 + 108 * t * b₄ ^ 3 * π ^ 4 * y ^ 4 + 144 * b₄ * π ^ 3 * t ^ 3
      * y ^ 3 + 171 * b₆ * b₄ ^ 2 * π ^ 3 * y ^ 4 + 576 * x * b₄ ^ 3 * π ^ 5 * y ^ 2 + 648 * b₄ * b₆
      * π ^ 3 * y ^ 2 + 648 * b₆ * π ^ 2 * t ^ 2 * y ^ 3 : S) +
    (648 * b₆ * π ^ 2 * t ^ 3 * y ^ 4 + 972 * t * π ^ 2 * b₆ ^ 2 * y ^ 4 + 1728 * b₄ * π ^ 4 * t ^ 4
      * y ^ 3 + 1728 * b₄ * π ^ 4 * t ^ 5 * y ^ 4 + 3888 * x * π ^ 3 * b₆ ^ 2 * y ^ 2 - 648 * b₄ * x
      * b₆ * π ^ 3 * y ^ 2 - 144 * b₄ * b₆ * t * π ^ 2 * y ^ 4 - 9 * x * t * b₄ ^ 2 * π ^ 3 * y ^ 3
      + 9 * x * π * b₆ * t * y ^ 3 + 432 * b₄ * b₆ * π ^ 3 * t ^ 2 * y ^ 4 : S) +
    (576 * x * t * b₄ ^ 3 * π ^ 5 * y ^ 3 + 1728 * b₄ * b₆ * t * π ^ 3 * y ^ 3 + 3888 * x * t * π ^
      3 * b₆ ^ 2 * y ^ 3 - 648 * b₄ * x * b₆ * t * π ^ 3 * y ^ 3 : S)) * hκ

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
-- the certificates are large polynomials
/-- **The Jacobian certificate of the chart `T1`**: `a ∂_{h'}G₁ + b ∂_wG₁ + c G₁ = 3 π E κ`. -/
theorem cert1 (π b₄ t κ b₆ x y : S) (hκ : κ * (t ^ 2 - b₆) = 1) :
    cert1a π b₄ t κ b₆ x y * (2 * κ * t * y ^ 2 + 2 * κ * x * y + κ * y) +
      cert1b π b₄ t κ b₆ x y * (3 * y ^ 2 + 2 * κ * (2 * t * x + (t - π * b₄)) * y +
        κ * (x ^ 2 + x)) +
      cert1c π b₄ t κ b₆ x y * (y ^ 3 + κ * (2 * t * x + (t - π * b₄)) * y ^ 2 +
        κ * (x ^ 2 + x) * y - κ * π) = 3 * π * TateNormal.tateE π b₄ b₆ * κ := by
  unfold cert1a cert1b cert1c TateNormal.tateE
  linear_combination (
    (12 * x * b₆ * y ^ 3 + 12 * b₆ * t * y ^ 4 + 12 * b₄ ^ 3 * π ^ 3 * y ^ 4 - 12 * b₄ * π * b₆ * y
      ^ 4 - 12 * x * b₄ ^ 2 * π ^ 2 * y ^ 3 - 12 * t * b₄ ^ 2 * π ^ 2 * y ^ 4 + 144 * b₆ * b₄ ^ 2 *
      π ^ 3 * y ^ 4 + 192 * x * b₄ ^ 3 * π ^ 4 * y ^ 3 + 192 * t * b₄ ^ 3 * π ^ 4 * y ^ 4 - 288 * b₄
      * x * b₆ * π ^ 2 * y ^ 3 : S) +
    (-288 * b₄ * b₆ * t * π ^ 2 * y ^ 4 : S)) * hκ

/-- The first-order lift for `G₀`. -/
theorem lift0 (π b₄ t κ x y e α β c : S) (he : e ^ 2 = 0)
    (hG : y ^ 3 + κ * (2 * t + (t - π * b₄) * x) * y ^ 2 + κ * (1 + x) * y - κ * π * x ^ 3 = e)
    (hc : α * (κ * (t - π * b₄) * y ^ 2 + κ * y - 3 * κ * π * x ^ 2) +
      β * (3 * y ^ 2 + 2 * κ * (2 * t + (t - π * b₄) * x) * y + κ * (1 + x)) + 1 = c * e) :
    (y + e * β) ^ 3 + κ * (2 * t + (t - π * b₄) * (x + e * α)) * (y + e * β) ^ 2 +
      κ * (1 + (x + e * α)) * (y + e * β) - κ * π * (x + e * α) ^ 3 = 0 := by
  linear_combination hG + (c - α ^ 3 * e * κ * π - 3 * α ^ 2 * κ * π * x -
    α * b₄ * β ^ 2 * e * κ * π - 2 * α * b₄ * β * κ * π * y + α * β ^ 2 * e * κ * t +
    2 * α * β * κ * t * y + α * β * κ - b₄ * β ^ 2 * κ * π * x + β ^ 3 * e + β ^ 2 * κ * t * x +
    2 * β ^ 2 * κ * t + 3 * β ^ 2 * y) * he + e * hc

/-- The first-order lift for `G₁`. -/
theorem lift1 (π b₄ t κ x y e α β c : S) (he : e ^ 2 = 0)
    (hG : y ^ 3 + κ * (2 * t * x + (t - π * b₄)) * y ^ 2 + κ * (x ^ 2 + x) * y - κ * π = e)
    (hc : α * (2 * κ * t * y ^ 2 + 2 * κ * x * y + κ * y) +
      β * (3 * y ^ 2 + 2 * κ * (2 * t * x + (t - π * b₄)) * y + κ * (x ^ 2 + x)) + 1 = c * e) :
    (y + e * β) ^ 3 + κ * (2 * t * (x + e * α) + (t - π * b₄)) * (y + e * β) ^ 2 +
      κ * ((x + e * α) ^ 2 + (x + e * α)) * (y + e * β) - κ * π = 0 := by
  linear_combination hG + (c + α ^ 2 * β * e * κ + α ^ 2 * κ * y + 2 * α * β ^ 2 * e * κ * t +
    4 * α * β * κ * t * y + 2 * α * β * κ * x + α * β * κ - b₄ * β ^ 2 * κ * π + β ^ 3 * e +
    2 * β ^ 2 * κ * t * x + β ^ 2 * κ * t + 3 * β ^ 2 * y) * he + e * hc

end Certificate

section Eval

variable {K : Type*} [CommRing K] (π b₄ t κ : K) {S : Type*} [CommRing S] [Algebra K S]

lemma eval₂_G0 (x y : S) : (G0 π b₄ t κ).eval₂ ((aeval x : K[X] →ₐ[K] S) : K[X] →+* S) y =
    y ^ 3 + algebraMap K S κ * (2 * algebraMap K S t + (algebraMap K S t -
      algebraMap K S π * algebraMap K S b₄) * x) * y ^ 2 + algebraMap K S κ * (1 + x) * y -
      algebraMap K S κ * algebraMap K S π * x ^ 3 := by
  simp only [G0, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, RingHom.coe_coe,
    map_mul, map_add, map_sub, map_one, map_pow, aeval_C, aeval_X, map_ofNat, eval₂_ofNat,
    eval₂_one]

lemma eval₂_G1 (x y : S) : (G1 π b₄ t κ).eval₂ ((aeval x : K[X] →ₐ[K] S) : K[X] →+* S) y =
    y ^ 3 + algebraMap K S κ * (2 * algebraMap K S t * x + (algebraMap K S t -
      algebraMap K S π * algebraMap K S b₄)) * y ^ 2 + algebraMap K S κ * (x ^ 2 + x) * y -
      algebraMap K S κ * algebraMap K S π := by
  simp only [G1, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, RingHom.coe_coe,
    map_mul, map_add, map_sub, map_pow, aeval_C, aeval_X, map_ofNat, eval₂_ofNat]

lemma map_G0 {L : Type*} [CommRing L] (φ : K →+* L) :
    (G0 π b₄ t κ).map (mapRingHom φ) = G0 (φ π) (φ b₄) (φ t) (φ κ) := by
  simp only [G0, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_one, coe_mapRingHom, map_mul, map_sub,
    map_ofNat, map_add, map_one, Polynomial.map_ofNat]

lemma map_G1 {L : Type*} [CommRing L] (φ : K →+* L) :
    (G1 π b₄ t κ).map (mapRingHom φ) = G1 (φ π) (φ b₄) (φ t) (φ κ) := by
  simp only [G1, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, coe_mapRingHom, map_mul, map_sub, map_ofNat, map_add,
    Polynomial.map_ofNat]

lemma tateE_map {L : Type*} [CommRing L] (φ : K →+* L) (b₆ : K) :
    TateNormal.tateE (φ π) (φ b₄) (φ b₆) = φ (TateNormal.tateE π b₄ b₆) := by
  simp only [TateNormal.tateE, map_add, map_sub, map_mul, map_pow, map_ofNat]

end Eval

/-! ### Smoothness, irreducibility, Dedekind -/

section Field

variable {K : Type*} [Field K] (π b₄ t κ : K) {b₆ : K}

variable {π b₄ t κ} in
/-- The first-order lift of the generators of `T0` (in any `K`-algebra with `e² = 0`). -/
theorem eval₂_lift0 {S : Type*} [CommRing S] [Algebra K S] (hκ : κ * (t ^ 2 - b₆) = 1)
    (hu : 3 * π * TateNormal.tateE π b₄ b₆ * κ ≠ 0) (x y e : S) (he : e ^ 2 = 0)
    (hG : (G0 π b₄ t κ).eval₂ ((aeval x : K[X] →ₐ[K] S) : K[X] →+* S) y = e) :
    (G0 π b₄ t κ).eval₂ ((aeval (x + e * -(algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ)⁻¹ *
      cert0a (algebraMap K S π) (algebraMap K S b₄) (algebraMap K S t) (algebraMap K S κ)
        (algebraMap K S b₆) x y)) : K[X] →ₐ[K] S) : K[X] →+* S)
      (y + e * -(algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ)⁻¹ *
      cert0b (algebraMap K S π) (algebraMap K S b₄) (algebraMap K S t) (algebraMap K S κ)
        (algebraMap K S b₆) x y)) = 0 := by
  rw [eval₂_G0] at hG ⊢
  have hw : algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ) *
      algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hu, map_one]
  have hκ' : algebraMap K S κ * (algebraMap K S t ^ 2 - algebraMap K S b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  simp only [map_mul, map_ofNat] at hw
  rw [← tateE_map π b₄ (algebraMap K S) b₆] at hw
  set w := algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ)⁻¹
  set φ := algebraMap K S
  have hc := cert0 (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y hκ'
  linear_combination lift0 (φ π) (φ b₄) (φ t) (φ κ) x y e
    (-(w * cert0a (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y))
    (-(w * cert0b (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y))
    (w * cert0c (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y) he hG
    (by linear_combination (-w) * hc + (w * cert0c (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y) * hG - hw)

variable {π b₄ t κ} in
/-- The first-order lift of the generators of `T1` (in any `K`-algebra with `e² = 0`). -/
theorem eval₂_lift1 {S : Type*} [CommRing S] [Algebra K S] (hκ : κ * (t ^ 2 - b₆) = 1)
    (hu : 3 * π * TateNormal.tateE π b₄ b₆ * κ ≠ 0) (x y e : S) (he : e ^ 2 = 0)
    (hG : (G1 π b₄ t κ).eval₂ ((aeval x : K[X] →ₐ[K] S) : K[X] →+* S) y = e) :
    (G1 π b₄ t κ).eval₂ ((aeval (x + e * -(algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ)⁻¹ *
      cert1a (algebraMap K S π) (algebraMap K S b₄) (algebraMap K S t) (algebraMap K S κ)
        (algebraMap K S b₆) x y)) : K[X] →ₐ[K] S) : K[X] →+* S)
      (y + e * -(algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ)⁻¹ *
      cert1b (algebraMap K S π) (algebraMap K S b₄) (algebraMap K S t) (algebraMap K S κ)
        (algebraMap K S b₆) x y)) = 0 := by
  rw [eval₂_G1] at hG ⊢
  have hw : algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ) *
      algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hu, map_one]
  have hκ' : algebraMap K S κ * (algebraMap K S t ^ 2 - algebraMap K S b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  simp only [map_mul, map_ofNat] at hw
  rw [← tateE_map π b₄ (algebraMap K S) b₆] at hw
  set w := algebraMap K S (3 * π * TateNormal.tateE π b₄ b₆ * κ)⁻¹
  set φ := algebraMap K S
  have hc := cert1 (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y hκ'
  linear_combination lift1 (φ π) (φ b₄) (φ t) (φ κ) x y e
    (-(w * cert1a (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y))
    (-(w * cert1b (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y))
    (w * cert1c (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y) he hG
    (by linear_combination (-w) * hc + (w * cert1c (φ π) (φ b₄) (φ t) (φ κ) (φ b₆) x y) * hG - hw)

/-- **The chart `T0` of the generic fibre is smooth** (`3 π E κ ≠ 0`). -/
theorem formallySmooth_T0 (hκ : κ * (t ^ 2 - b₆) = 1)
    (hu : 3 * π * TateNormal.tateE π b₄ b₆ * κ ≠ 0) : Algebra.FormallySmooth K (T0 π b₄ t κ) :=
  PlaneCurve.formallySmooth_of_lift _ _ _ (eval₂_lift0 hκ hu _ _ _ (PlaneCurve.sq_mk_self _)
    (PlaneCurve.mk_eq_eval₂ _ _).symm)

/-- **The chart `T1` of the generic fibre is smooth** (`3 π E κ ≠ 0`). -/
theorem formallySmooth_T1 (hκ : κ * (t ^ 2 - b₆) = 1)
    (hu : 3 * π * TateNormal.tateE π b₄ b₆ * κ ≠ 0) : Algebra.FormallySmooth K (T1 π b₄ t κ) :=
  PlaneCurve.formallySmooth_of_lift _ _ _ (eval₂_lift1 hκ hu _ _ _ (PlaneCurve.sq_mk_self _)
    (PlaneCurve.mk_eq_eval₂ _ _).symm)

lemma natDegree_G0 : (G0 π b₄ t κ).natDegree = 3 := by
  unfold G0
  compute_degree!

lemma natDegree_G1 : (G1 π b₄ t κ).natDegree = 3 := by
  unfold G1
  compute_degree!

/-- `G₀` is irreducible over `K[X]`: a root in `K[X]` would be `c Xⁱ`, `i ≤ 3`. -/
theorem irreducible_G0 (hκ0 : κ ≠ 0) (hπ : π ≠ 0) : Irreducible (G0 π b₄ t κ) := by
  rw [(monic_G0 π b₄ t κ).irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [natDegree_G0]; norm_num) (by rw [natDegree_G0])]
  refine Multiset.eq_zero_of_forall_notMem fun r hr ↦ ?_
  rw [mem_roots (monic_G0 π b₄ t κ).ne_zero, IsRoot] at hr
  simp only [G0, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
  have hd : r ∣ X ^ 3 := by
    have h : C (κ * π) * X ^ 3 = r * (r ^ 2 + C κ * (C (2 * t) + C (t - π * b₄) * X) * r +
        C κ * (1 + X)) := by linear_combination -hr
    exact ((isUnit_C.mpr (IsUnit.mk0 _ (mul_ne_zero hκ0 hπ))).dvd_mul_left).mp ⟨_, h⟩
  obtain ⟨i, hi, u, hu⟩ := (dvd_prime_pow prime_X 3).1 hd
  have hr' : r = (X ^ i : K[X]) * ((u⁻¹ : K[X]ˣ) : K[X]) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp (u⁻¹).isUnit
  rw [hr', ← hcu] at hr
  have hc0 := hc.ne_zero
  interval_cases i
  · have h : C (c ^ 3 + 2 * κ * t * c ^ 2 + κ * c) * X ^ 0 +
        C (κ * (t - π * b₄) * c ^ 2 + κ * c) * X ^ 1 - C (κ * π) * X ^ 3 = 0 := by
      rw [← hr]; simp only [map_add, map_mul, map_sub, map_pow, map_ofNat]; ring
    have := congrArg (coeff · 3) h
    simp only [coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_zero] at this
    norm_num [hκ0, hπ] at this
  · have h : C (κ * c) * X ^ 1 + C (2 * κ * t * c ^ 2 + κ * c) * X ^ 2 +
        C (c ^ 3 + κ * (t - π * b₄) * c ^ 2 - κ * π) * X ^ 3 = 0 := by
      rw [← hr]; simp only [map_add, map_mul, map_sub, map_pow, map_ofNat]; ring
    have := congrArg (coeff · 1) h
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_zero] at this
    norm_num [hκ0, hc0] at this
  · have h : C (κ * c) * X ^ 2 + C (κ * c - κ * π) * X ^ 3 + C (2 * κ * t * c ^ 2) * X ^ 4 +
        C (κ * (t - π * b₄) * c ^ 2) * X ^ 5 + C (c ^ 3) * X ^ 6 = 0 := by
      rw [← hr]; simp only [map_mul, map_sub, map_pow, map_ofNat]; ring
    have := congrArg (coeff · 6) h
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_zero] at this
    norm_num [hc0] at this
  · have h : C (κ * c - κ * π) * X ^ 3 + C (κ * c) * X ^ 4 + C (2 * κ * t * c ^ 2) * X ^ 6 +
        C (κ * (t - π * b₄) * c ^ 2) * X ^ 7 + C (c ^ 3) * X ^ 9 = 0 := by
      rw [← hr]; simp only [map_mul, map_sub, map_pow, map_ofNat]; ring
    have := congrArg (coeff · 9) h
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_zero] at this
    norm_num [hc0] at this

/-- `G₁` is irreducible over `K[X]`: a root in `K[X]` divides the unit `κ π`. -/
theorem irreducible_G1 (hκ0 : κ ≠ 0) (hπ : π ≠ 0) : Irreducible (G1 π b₄ t κ) := by
  rw [(monic_G1 π b₄ t κ).irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [natDegree_G1]; norm_num) (by rw [natDegree_G1])]
  refine Multiset.eq_zero_of_forall_notMem fun r hr ↦ ?_
  rw [mem_roots (monic_G1 π b₄ t κ).ne_zero, IsRoot] at hr
  simp only [G1, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
  have hd : r ∣ C (κ * π) := ⟨r ^ 2 + C κ * (C (2 * t) * X + C (t - π * b₄)) * r +
    C κ * (X ^ 2 + X), by linear_combination -hr⟩
  obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp
    (isUnit_of_dvd_unit hd (isUnit_C.mpr (IsUnit.mk0 _ (mul_ne_zero hκ0 hπ))))
  have h : C (c ^ 3 + κ * (t - π * b₄) * c ^ 2 - κ * π) * X ^ 0 +
      C (2 * κ * t * c ^ 2 + κ * c) * X ^ 1 + C (κ * c) * X ^ 2 = 0 := by
    rw [← hr]; simp only [map_add, map_mul, map_sub, map_pow, map_ofNat]; ring
  have := congrArg (coeff · 2) h
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_zero] at this
  norm_num [hκ0, hc.ne_zero] at this

/-- **The chart `T0` of the generic fibre is a Dedekind domain.** -/
theorem isDedekindDomain_T0 (hκ : κ * (t ^ 2 - b₆) = 1) (h3 : (3 : K) ≠ 0) (hπ : π ≠ 0)
    (hE : TateNormal.tateE π b₄ b₆ ≠ 0) : IsDedekindDomain (T0 π b₄ t κ) := by
  have hκ0 : κ ≠ 0 := left_ne_zero_of_mul_eq_one hκ
  haveI := formallySmooth_T0 π b₄ t κ hκ (by simp [h3, hπ, hE, hκ0])
  exact PlaneCurve.isDedekindDomain_of_irreducible (monic_G0 π b₄ t κ)
    (irreducible_G0 π b₄ t κ hκ0 hπ)

/-- **The chart `T1` of the generic fibre is a Dedekind domain.** -/
theorem isDedekindDomain_T1 (hκ : κ * (t ^ 2 - b₆) = 1) (h3 : (3 : K) ≠ 0) (hπ : π ≠ 0)
    (hE : TateNormal.tateE π b₄ b₆ ≠ 0) : IsDedekindDomain (T1 π b₄ t κ) := by
  have hκ0 : κ ≠ 0 := left_ne_zero_of_mul_eq_one hκ
  haveI := formallySmooth_T1 π b₄ t κ hκ (by simp [h3, hπ, hE, hκ0])
  exact PlaneCurve.isDedekindDomain_of_irreducible (monic_G1 π b₄ t κ)
    (irreducible_G1 π b₄ t κ hκ0 hπ)

end Field

/-! ### `T_i[1/ϖ]` -/

section Away

variable {O : Type*} [CommRing O] [IsDomain O] {ϖ : O} (hϖ : ϖ ≠ 0)

section Equiv

variable (K : Type*) [CommRing K] [IsDomain K] [Algebra O K] [IsLocalization.Away ϖ K]
  (π b₄ t κ : O)

include hϖ in
/-- **`T0[1/ϖ]` is the chart ring `T0` over `K = O[1/ϖ]`.** -/
def awayEquiv0 : Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ) ≃+*
    T0 (algebraMap O K π) (algebraMap O K b₄) (algebraMap O K t) (algebraMap O K κ) :=
  letI := (PlaneCurve.baseMap (map_G0 π b₄ t κ (algebraMap O K))).toAlgebra
  haveI := PlaneCurve.isLocalization_adjoinRoot_map (map_G0 π b₄ t κ (algebraMap O K))
    (Submonoid.powers ϖ) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ) (monic_G0 π b₄ t κ)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (T0 π b₄ t κ) (Submonoid.powers ϖ))
      (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (T0 π b₄ t κ) (Submonoid.powers ϖ))
    _ _).toRingEquiv

include hϖ in
/-- **`T1[1/ϖ]` is the chart ring `T1` over `K = O[1/ϖ]`.** -/
def awayEquiv1 : Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ) ≃+*
    T1 (algebraMap O K π) (algebraMap O K b₄) (algebraMap O K t) (algebraMap O K κ) :=
  letI := (PlaneCurve.baseMap (map_G1 π b₄ t κ (algebraMap O K))).toAlgebra
  haveI := PlaneCurve.isLocalization_adjoinRoot_map (map_G1 π b₄ t κ (algebraMap O K))
    (Submonoid.powers ϖ) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ) (monic_G1 π b₄ t κ)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (T1 π b₄ t κ) (Submonoid.powers ϖ))
      (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (T1 π b₄ t κ) (Submonoid.powers ϖ))
    _ _).toRingEquiv

end Equiv

variable {π b₄ t κ : O} {b₆ : O}

include hϖ in
/-- **The generic fibre `T0[1/ϖ]` is a Dedekind domain** (`K = O[1/ϖ]` a field). -/
theorem isDedekindDomain_away_T0 (K : Type*) [Field K] [Algebra O K] [IsLocalization.Away ϖ K]
    (hκ : κ * (t ^ 2 - b₆) = 1) (h3 : (3 : K) ≠ 0) (hπ : algebraMap O K π ≠ 0)
    (hE : algebraMap O K (TateNormal.tateE π b₄ b₆) ≠ 0) :
    IsDedekindDomain (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) := by
  haveI := isDedekindDomain_T0 (algebraMap O K π) (algebraMap O K b₄) (algebraMap O K t)
    (algebraMap O K κ) (b₆ := algebraMap O K b₆)
    (by rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]) h3 hπ
    (by rwa [tateE_map π b₄ (algebraMap O K) b₆])
  exact PlaneCurve.isDedekindDomain_of_ringEquiv (awayEquiv0 hϖ K π b₄ t κ)

include hϖ in
/-- **The generic fibre `T1[1/ϖ]` is a Dedekind domain** (`K = O[1/ϖ]` a field). -/
theorem isDedekindDomain_away_T1 (K : Type*) [Field K] [Algebra O K] [IsLocalization.Away ϖ K]
    (hκ : κ * (t ^ 2 - b₆) = 1) (h3 : (3 : K) ≠ 0) (hπ : algebraMap O K π ≠ 0)
    (hE : algebraMap O K (TateNormal.tateE π b₄ b₆) ≠ 0) :
    IsDedekindDomain (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ)) := by
  haveI := isDedekindDomain_T1 (algebraMap O K π) (algebraMap O K b₄) (algebraMap O K t)
    (algebraMap O K κ) (b₆ := algebraMap O K b₆)
    (by rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]) h3 hπ
    (by rwa [tateE_map π b₄ (algebraMap O K) b₆])
  exact PlaneCurve.isDedekindDomain_of_ringEquiv (awayEquiv1 hϖ K π b₄ t κ)

variable [IsDiscreteValuationRing O]

include hϖ in
/-- **`T0[1/ϖ]` is a Dedekind domain** for a discrete valuation ring `O`, `ϖ` a nonzero nonunit,
`κ (t² − b₆) = 1`, `3 ≠ 0`, `π ≠ 0`, `E ≠ 0`. -/
theorem isDedekindDomain_away_T0_of_dvr (hu : ¬IsUnit ϖ) (hκ : κ * (t ^ 2 - b₆) = 1)
    (h3 : (3 : O) ≠ 0) (hπ : π ≠ 0) (hE : TateNormal.tateE π b₄ b₆ ≠ 0) :
    IsDedekindDomain (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) := by
  haveI := isLocalization_away_fractionRing hϖ hu
  have hinj := IsFractionRing.injective O (FractionRing O)
  exact isDedekindDomain_away_T0 hϖ (FractionRing O) hκ
    (by rw [← map_ofNat (algebraMap O (FractionRing O)) 3]
        exact (map_ne_zero_iff _ hinj).mpr h3) ((map_ne_zero_iff _ hinj).mpr hπ)
    ((map_ne_zero_iff _ hinj).mpr hE)

include hϖ in
/-- **`T1[1/ϖ]` is a Dedekind domain** for a discrete valuation ring `O`, `ϖ` a nonzero nonunit,
`κ (t² − b₆) = 1`, `3 ≠ 0`, `π ≠ 0`, `E ≠ 0`. -/
theorem isDedekindDomain_away_T1_of_dvr (hu : ¬IsUnit ϖ) (hκ : κ * (t ^ 2 - b₆) = 1)
    (h3 : (3 : O) ≠ 0) (hπ : π ≠ 0) (hE : TateNormal.tateE π b₄ b₆ ≠ 0) :
    IsDedekindDomain (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ)) := by
  haveI := isLocalization_away_fractionRing hϖ hu
  have hinj := IsFractionRing.injective O (FractionRing O)
  exact isDedekindDomain_away_T1 hϖ (FractionRing O) hκ
    (by rw [← map_ofNat (algebraMap O (FractionRing O)) 3]
        exact (map_ne_zero_iff _ hinj).mpr h3) ((map_ne_zero_iff _ hinj).mpr hπ)
    ((map_ne_zero_iff _ hinj).mpr hE)

end Away

end TateTwoChart

end

end SemistableReduction
