/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerTateChartTransfer
import TemperedFundamentalGroups.SemistableReduction.KummerTateChartDomain
import TemperedFundamentalGroups.SemistableReduction.KummerEtaleChart

/-!
# Tame covers of the Tate chart are Kummer at the nodes (MR12 T2 S4, Tate chart)

The chart `u ≠ 0` of the Tate model, localized at `D = 1 + b₄ w²`, is the quadratic node chart
`T1[1/D] ≅ NR = (A[S]/(S² + S − c))[1/D]` over the node ring `A = O[u,v]/(uv − ϖᵐ)`
(`TateTwoChartNode.chartEquiv`); `toT1D : A → T1[1/D]` is the resulting node chart, with
`u ↦ w` (`toT1D_u`).

**`TateTwoChartNode.isKummerAt_T1D`**: let `O` be a discrete valuation ring with uniformizer `ϖ`,
`m = q M' ≥ 1`, `𝔫` a prime of `T1[1/D]` over the closed point `u = v = ϖ = 0` of `A` (a node of
the special fibre), `K = Frac T1[1/D]` containing a primitive `M'`-th root of unity, and `L / K`
finite Galois of degree prime to `q` whose normalisation over the local ring `T1[1/D]_𝔫` is
unramified over its punctured spectrum. Then `L` is Kummer at `𝔫` with the node coordinates
`u, v` of the chart.

Proof: the generic step is **`NodeCover.isKummerAt_of_isLocalization_etale`**: if a domain `N'`
with a map `A → N'` has a localization `N = S⁻¹ N'` which is étale over `N'` and over `A` and a
domain, then `NodeCover.isKummerAt_of_etale` for `N` descends to `N'` at every prime `𝔫` of `N'`
disjoint from `S` over the closed point (`IsKummerAt.comap_of_isLocalization`); the fraction field
and the local ring `N'_𝔫 ≅ N_𝔫` are the same, and the hypotheses on the normalisation are
transported along this isomorphism (`isIntegralClosure_of_ringEquiv`,
`isUnramifiedAt_of_ringEquiv`). For the Tate chart, `N = NE = NR[1/(2S+1)]` (étale over `A`, a
domain: `KummerTateChartDomain`), a localization of `T1[1/D]` via `chartEquiv`; at the nodes
`c ∈ 𝔫` (`cN_mem_closedPoint`), so `2S + 1 ∉ 𝔫` since `(2S+1)² = 1 + 4c` (`twoS1_notMem`).
-/

universe u

open Polynomial IsLocalRing Module

namespace SemistableReduction

open KummerEtale TateTwoChart

namespace NodeCover

open Node

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {s : O} {M : ℕ}
  [NeZero M] [(closedPoint s (s ^ M)).IsPrime]

set_option maxHeartbeats 1000000 in
-- Many localization structures.
/-- **Tame covers of a chart which becomes étale over the node after localization are Kummer.**
Let `N'` be a domain with a map `f : A = Node O (s ^ M) → N'` and `N = S⁻¹ N'` a localization,
étale over `N'` and (via `f`) over `A`, and a domain. Let `𝔫` be a prime of `N'` disjoint from `S`
over the closed point of `A`, `K = Frac N' ∋ ζ_{M'}`, `M = q M'`, and `L / K` finite Galois of
degree prime to `q` whose normalisation `B` over `N'_𝔫` is unramified over the punctured spectrum.
Then `L` is Kummer at `𝔫` with the coordinates `f u, f v` (from `isKummerAt_of_etale` for `N`,
descended along `N' → N`). -/
theorem isKummerAt_of_isLocalization_etale (hs : Irreducible s) {q M' : ℕ} (hqM : q * M' = M)
    (hq : 0 < q) (hM' : 0 < M') {N' : Type u} [CommRing N'] [IsDomain N'] [Algebra O N']
    (N : Type u) [CommRing N] [IsDomain N] [Algebra O N] [Algebra (Node O (s ^ M)) N]
    [IsScalarTower O (Node O (s ^ M)) N] [Algebra.Etale (Node O (s ^ M)) N] [Algebra N' N]
    [IsScalarTower O N' N] (S : Submonoid N') [IsLocalization S N] [Algebra.Etale N' N]
    (f : Node O (s ^ M) →+* N')
    (hf : ∀ a, algebraMap (Node O (s ^ M)) N a = algebraMap N' N (f a))
    (𝔫 : Ideal N') [𝔫.IsPrime] (hdisj : Disjoint (S : Set N') 𝔫)
    (h𝔫 : 𝔫.comap f = closedPoint s (s ^ M))
    (K : Type u) [Field K] [Algebra N' K] [IsFractionRing N' K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (finrank K L).Coprime q) [Algebra N' L] [IsScalarTower N' K L]
    [Algebra (Localization.AtPrime 𝔫) L] [IsScalarTower N' (Localization.AtPrime 𝔫) L]
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime 𝔫) B] [Algebra B L]
    [IsScalarTower (Localization.AtPrime 𝔫) B L] [IsIntegralClosure B (Localization.AtPrime 𝔫) L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap (Localization.AtPrime 𝔫) B) ≠ maximalIdeal (Localization.AtPrime 𝔫) →
      Algebra.IsUnramifiedAt (Localization.AtPrime 𝔫) Q) :
    IsKummerAt s M (f (Node.u (s ^ M))) (f (Node.v (s ^ M))) L 𝔫 := by
  classical
  -- the prime of the étale chart over `𝔫`
  set 𝔫E : Ideal N := 𝔫.map (algebraMap N' N)
  haveI : 𝔫E.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint S _ 𝔫 inferInstance hdisj
  letI : SMul N' (Localization.AtPrime 𝔫E) := Algebra.toSMul
  have hc : 𝔫E.comap (algebraMap N' N) = 𝔫 :=
    IsLocalization.under_map_of_isPrime_disjoint S _ inferInstance hdisj
  have h𝔫E : 𝔫E.comap (algebraMap (Node O (s ^ M)) N) = closedPoint s (s ^ M) := by
    rw [show algebraMap (Node O (s ^ M)) N =
      (algebraMap N' N).comp f from RingHom.ext hf,
      ← Ideal.comap_comap, hc, h𝔫]
  -- the fraction field
  have hSle : S ≤ nonZeroDivisors N' := fun y hy ↦ mem_nonZeroDivisors_of_ne_zero fun h0 ↦
    Set.disjoint_left.mp hdisj hy (h0 ▸ 𝔫.zero_mem)
  have hunitK : ∀ y : S, IsUnit (algebraMap N' K y) := fun y ↦
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr
      (nonZeroDivisors.ne_zero (hSle y.2)))
  letI : Algebra N K := (IsLocalization.lift (M := S) hunitK).toAlgebra
  haveI : IsScalarTower N' N K := IsScalarTower.of_algebraMap_eq
    fun y ↦ (IsLocalization.lift_eq (M := S) hunitK y).symm
  haveI : IsFractionRing N K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S _ K
  letI : Algebra N L :=
    ((algebraMap K L).comp (algebraMap N K)).toAlgebra
  haveI : IsScalarTower N K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower N' N L := IsScalarTower.of_algebraMap_eq fun y ↦ by
    change _ = algebraMap K L (algebraMap N K (algebraMap N' N y))
    rw [← IsScalarTower.algebraMap_apply N' N K, ← IsScalarTower.algebraMap_apply N' K L]
  -- the local rings
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔫E) 𝔫 := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S
      (Localization.AtPrime 𝔫E) 𝔫E
    have hpc : (𝔫E.comap (algebraMap N' N)).primeCompl =
        𝔫.primeCompl := by
      ext y
      simp only [Ideal.mem_primeCompl_iff, hc]
    change IsLocalization (𝔫E.comap (algebraMap N' N)).primeCompl _ at this
    rw [hpc] at this
    exact this
  let e : Localization.AtPrime 𝔫 ≃ₐ[N'] Localization.AtPrime 𝔫E :=
    IsLocalization.algEquiv 𝔫.primeCompl _ _
  letI : Algebra (Localization.AtPrime 𝔫E) L :=
    ((algebraMap (Localization.AtPrime 𝔫) L).comp e.symm.toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower N (Localization.AtPrime 𝔫E) L := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext S (RingHom.ext fun y ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply N' N L,
      ← IsScalarTower.algebraMap_apply N' N (Localization.AtPrime 𝔫E)]
    change _ = algebraMap (Localization.AtPrime 𝔫) L
      (e.symm (algebraMap N' (Localization.AtPrime 𝔫E) y))
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  letI : Algebra (Localization.AtPrime 𝔫E) B :=
    ((algebraMap (Localization.AtPrime 𝔫) B).comp e.symm.toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime 𝔫E) B L := IsScalarTower.of_algebraMap_eq fun y ↦
    IsScalarTower.algebraMap_apply (Localization.AtPrime 𝔫) B L (e.symm y)
  have he : ∀ r, algebraMap (Localization.AtPrime 𝔫E) B (e.toRingEquiv r) =
      algebraMap (Localization.AtPrime 𝔫) B r := fun r ↦ by
    change algebraMap (Localization.AtPrime 𝔫) B (e.symm (e r)) = _
    rw [AlgEquiv.symm_apply_apply]
  have he' : ∀ r, algebraMap (Localization.AtPrime 𝔫) B (e.symm.toRingEquiv r) =
      algebraMap (Localization.AtPrime 𝔫E) B r := fun _ ↦ rfl
  haveI : IsIntegralClosure B (Localization.AtPrime 𝔫E) L :=
    isIntegralClosure_of_ringEquiv e.toRingEquiv he
  have hunr' : ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap (Localization.AtPrime 𝔫E) B) ≠ maximalIdeal (Localization.AtPrime 𝔫E) →
      Algebra.IsUnramifiedAt (Localization.AtPrime 𝔫E) Q := fun Q _ hQ ↦
    isUnramifiedAt_of_ringEquiv e.toRingEquiv he Q
      (hunr Q (comap_ne_maximalIdeal_of_ringEquiv e.symm.toRingEquiv he' Q hQ))
  -- the étale chart is Kummer at `𝔫E`, and this descends to `T1[1/D]`
  have hK := isKummerAt_of_etale hs hqM hq hM' N 𝔫E h𝔫E K hζ L hL B
    hunr'
  rw [hf, hf] at hK
  have := hK.comap_of_isLocalization S
  rwa [hc] at this

end NodeCover

namespace TateTwoChartNode

variable {O : Type u} [CommRing O] {π b₄ b₆ t κ ϖ ε εi : O} {m : ℕ}

variable (b₄) in
/-- **The node chart of the Tate model** `A = O[u,v]/(uv − ϖᵐ) → T1[1/D]` (via `chartEquiv`). -/
noncomputable def toT1D (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1) :
    A ϖ m →+* T1D π b₄ t κ :=
  (chartEquiv b₄ hκ hπ hε).symm.toRingEquiv.toRingHom.comp
    (algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε))

lemma toT1D_apply (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
    (a : A ϖ m) : toT1D b₄ hκ hπ hε a =
      (chartEquiv b₄ hκ hπ hε).symm (algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) a) :=
  rfl

/-- The coordinate `u` of the node chart is the coordinate `w` of `T1`. -/
lemma toT1D_u (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1) :
    toT1D b₄ hκ hπ hε (Node.u (ϖ ^ m)) = algebraMap _ _ (w1 π b₄ t κ) := by
  change (chartEquiv b₄ hκ hπ hε).symm (uR b₄ b₆ ϖ m ε) = _
  rw [AlgEquiv.symm_apply_eq, chartEquiv_w1]

/-- **`2S + 1` is a unit at the nodes**: `(2S + 1)² = 1 + 4c` and `c` vanishes there. -/
lemma twoS1_notMem (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
    (𝔫 : Ideal (T1D π b₄ t κ)) [𝔫.IsPrime]
    (h𝔫 : 𝔫.comap (toT1D b₄ hκ hπ hε) = Node.closedPoint ϖ (ϖ ^ m)) :
    (chartEquiv b₄ hκ hπ hε).symm (twoS1 b₄ b₆ ϖ m ε) ∉ 𝔫 := by
  intro h
  have h0 : cN b₄ b₆ ϖ m ε ∈ 𝔫.comap (toT1D b₄ hκ hπ hε) := by
    rw [h𝔫]
    exact cN_mem_closedPoint b₄ b₆
  have hc𝔫 := Ideal.mem_comap.mp h0
  rw [toT1D_apply] at hc𝔫
  set P : Ideal (NR b₄ b₆ ϖ m ε) := 𝔫.comap (chartEquiv b₄ hκ hπ hε).symm with hP
  haveI : P.IsPrime := Ideal.comap_isPrime _ 𝔫
  have hx : twoS1 b₄ b₆ ϖ m ε ∈ P := Ideal.mem_comap.mpr h
  have hcP : algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (cN b₄ b₆ ϖ m ε) ∈ P :=
    Ideal.mem_comap.mpr hc𝔫
  have h3 := P.pow_mem_of_mem hx 2 two_pos
  rw [twoS1_sq] at h3
  have h1P : (1 : NR b₄ b₆ ϖ m ε) ∈ P := (P.add_mem_iff_left (P.mul_mem_left _ hcP)).mp h3
  exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h1P)

set_option maxHeartbeats 1000000 in
-- Many localization structures on the concrete charts.
/-- **Tame covers of the Tate chart are Kummer at the nodes** (MR12 T2 S4 for the Tate model).
Let `O` be a discrete valuation ring with uniformizer `ϖ`, `m = q M' ≥ 1`, `𝔫` a prime of the
Tate chart `T1[1/D] ≅ (A[S]/(S² + S − c))[1/D]` over the closed point `u = v = ϖ = 0` of the node
ring `A = O[u,v]/(uv − ϖᵐ)`, `K = Frac T1[1/D] ∋ ζ_{M'}`, and `L / K` finite Galois of degree prime
to `q` whose normalisation `B` over the local ring `T1[1/D]_𝔫` is unramified over the punctured
spectrum. Then `L` is Kummer at `𝔫` (`IsKummerAt ϖ m u v L 𝔫`) for the node coordinates
`u = w`, `v` of the chart. -/
theorem isKummerAt_T1D [IsDomain O] [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) [NeZero m]
    (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
    {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M')
    (𝔫 : Ideal (T1D π b₄ t κ)) [𝔫.IsPrime]
    (h𝔫 : 𝔫.comap (toT1D b₄ hκ hπ hε) = Node.closedPoint ϖ (ϖ ^ m))
    (K : Type u) [Field K] [Algebra (T1D π b₄ t κ) K] [IsFractionRing (T1D π b₄ t κ) K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (finrank K L).Coprime q) [Algebra (T1D π b₄ t κ) L] [IsScalarTower (T1D π b₄ t κ) K L]
    [Algebra (Localization.AtPrime 𝔫) L] [IsScalarTower (T1D π b₄ t κ) (Localization.AtPrime 𝔫) L]
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime 𝔫) B] [Algebra B L]
    [IsScalarTower (Localization.AtPrime 𝔫) B L] [IsIntegralClosure B (Localization.AtPrime 𝔫) L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap (Localization.AtPrime 𝔫) B) ≠ maximalIdeal (Localization.AtPrime 𝔫) →
      Algebra.IsUnramifiedAt (Localization.AtPrime 𝔫) Q) :
    IsKummerAt ϖ m (toT1D b₄ hκ hπ hε (Node.u (ϖ ^ m))) (toT1D b₄ hκ hπ hε (Node.v (ϖ ^ m)))
      L 𝔫 := by
  classical
  have hϖp : Prime ϖ := hϖ.prime
  have hm : 1 ≤ m := Nat.pos_of_neZero m
  have hεu : IsUnit ε := IsUnit.of_mul_eq_one_right εi hε
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : (Node.closedPoint ϖ (ϖ ^ m)).IsPrime :=
    (Node.isMaximal_closedPoint ϖ (dvd_pow_self ϖ (NeZero.ne m))).isPrime
  -- the charts are domains
  haveI : IsDomain (NR b₄ b₆ ϖ m ε) := isDomain_NR b₄ b₆ hϖp hm hεu
  haveI : IsDomain (T1D π b₄ t κ) :=
    MulEquiv.isDomain (NR b₄ b₆ ϖ m ε) (chartEquiv b₄ hκ hπ hε).toMulEquiv
  haveI : IsDomain (NE b₄ b₆ ϖ m ε) := isDomain_NE hϖp hm hεu
  -- the étale chart `NE` as a localization of `T1[1/D]`
  set e₀ : NR b₄ b₆ ϖ m ε ≃+* T1D π b₄ t κ := (chartEquiv b₄ hκ hπ hε).symm.toRingEquiv
    with he₀
  letI : Algebra (T1D π b₄ t κ) (NE b₄ b₆ ϖ m ε) :=
    ((algebraMap (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε)).comp e₀.symm.toRingHom).toAlgebra
  letI : SMul (T1D π b₄ t κ) (NE b₄ b₆ ϖ m ε) := Algebra.toSMul
  set S := (Submonoid.powers (twoS1 b₄ b₆ ϖ m ε)).map e₀ with hS
  haveI hloc : IsLocalization S (NE b₄ b₆ ϖ m ε) :=
    IsLocalization.isLocalization_of_base_ringEquiv (M := Submonoid.powers (twoS1 b₄ b₆ ϖ m ε))
      (S := NE b₄ b₆ ϖ m ε) e₀
  haveI : Algebra.Etale (T1D π b₄ t κ) (NE b₄ b₆ ϖ m ε) := by
    haveI : IsLocalization.Away (e₀ (twoS1 b₄ b₆ ϖ m ε)) (NE b₄ b₆ ϖ m ε) := by
      have := hloc
      rwa [hS, Submonoid.map_powers] at this
    exact Algebra.Etale.of_isLocalizationAway (e₀ (twoS1 b₄ b₆ ϖ m ε))
  have halg : ∀ y : T1D π b₄ t κ, algebraMap (T1D π b₄ t κ) (NE b₄ b₆ ϖ m ε) y =
      algebraMap (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε) (chartEquiv b₄ hκ hπ hε y) := fun _ ↦ rfl
  haveI : IsScalarTower O (T1D π b₄ t κ) (NE b₄ b₆ ϖ m ε) :=
    IsScalarTower.of_algebraMap_eq (R := O) (S := T1D π b₄ t κ) (A := NE b₄ b₆ ϖ m ε) fun a ↦ by
      rw [halg, (chartEquiv b₄ hκ hπ hε).commutes a,
        ← IsScalarTower.algebraMap_apply O (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε)]
  have hA : ∀ a : A ϖ m, algebraMap (A ϖ m) (NE b₄ b₆ ϖ m ε) a =
      algebraMap (T1D π b₄ t κ) (NE b₄ b₆ ϖ m ε) (toT1D b₄ hκ hπ hε a) := fun a ↦ by
    rw [halg]
    change _ = algebraMap (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε)
      (chartEquiv b₄ hκ hπ hε ((chartEquiv b₄ hκ hπ hε).symm (algebraMap (A ϖ m) _ a)))
    rw [AlgEquiv.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
  -- `2S + 1` is a unit at the nodes
  have he₀ : ∀ y, e₀ y = (chartEquiv b₄ hκ hπ hε).symm y := fun _ ↦ rfl
  have h2 : e₀ (twoS1 b₄ b₆ ϖ m ε) ∉ 𝔫 := by
    rw [he₀]
    exact twoS1_notMem hκ hπ hε 𝔫 h𝔫
  have hdisj : Disjoint (S : Set (T1D π b₄ t κ)) 𝔫 := by
    rw [hS, Submonoid.map_powers, Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hy
    exact h2 (Ideal.IsPrime.mem_of_pow_mem ‹_› k hy)
  exact NodeCover.isKummerAt_of_isLocalization_etale hϖ hqM hq hM' (NE b₄ b₆ ϖ m ε) S
    (toT1D b₄ hκ hπ hε) hA 𝔫 hdisj h𝔫 K hζ L hL B hunr

end TateTwoChartNode

end SemistableReduction
