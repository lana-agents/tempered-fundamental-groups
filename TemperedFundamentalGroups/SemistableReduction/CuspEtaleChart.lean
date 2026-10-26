/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspEtaleNbhd
import TemperedFundamentalGroups.SemistableReduction.CuspTame
import TemperedFundamentalGroups.SemistableReduction.KummerEtaleChart
import TemperedFundamentalGroups.SemistableReduction.KummerTateChartTransfer

/-!
# Tame covers of charts étale over the cusp chart are Kummer (MR12 T2 S3, étale charts)

Let `O` be a discrete valuation ring of characteristic zero (`CharZero O`) with uniformizer `ϖ`,
`N` an étale domain over the cusp chart `O[t]`, with fraction field `K_N`, and `𝔫` a prime of `N`
over the cusp point `(ϖ, t)`. Let `e ≥ 1` with `ζ_e ∈ K_N`.

**`Cusp.isTameCuspKummerAt_of_etale`**: a finite Galois extension `L / K_N` of degree dividing `e`
whose normalisation over `N_𝔫` is unramified at every prime of `N_𝔫` other than the maximal ideal
and the primes over `(t)` (i.e. `(t) N_𝔫`, which is prime) is tamely Kummer at `𝔫`
(`IsTameCuspKummerAt O e t L 𝔫`, `t` the image of the chart coordinate).

Proof: the cusp analogue of `NodeCover.isTameKummerAt_of_etale`. "S4-local" over `N_𝔫`
(`Cusp.exists_etale_tensor_algEquiv_pi_of_etaleNbhd`, applied with `R_M = O[t]_{(ϖ, t)}`,
`R_1 = O[t']_{(ϖ, t')}`, `t = t' ^ e`, `R' = R_M ⊗_{O[t]} N`, `P` the prime over `𝔫`) splits
`L` over the function field of an étale neighbourhood of the closed point of `N_𝔫` into copies
of `K_N ⊗_{K(T ^ e)} K(T ^ e)(T ^ n)`; the neighbourhood descends to an étale domain `N₁` over
`N` (`EtaleDescent.exists_etale_isDomain_localization_equiv`), and the factors are identified with
the cusp Kummer factors `N₁ ⊗_{O[t]} Frac O[y]`, `t ↦ y ^ e'`, `n e' = e`
(`tensorTensorEquiv`, `Cusp.adjoinPowCuspEquiv`).

**`Cusp.isTameCuspKummerAt_of_isLocalization_etale`**: the same for a domain `N'` with a map
`O[t] → N'` having a localization `N = S⁻¹ N'` which is étale over `N'` and over `O[t]` and a
domain, at primes of `N'` disjoint from `S` (the cusp analogue of
`NodeCover.isTameKummerAt_of_isLocalization_etale`; descent along
`IsTameCuspKummerAt.comap_of_isLocalization`).
-/

open Polynomial IsLocalRing IntermediateField Module TensorProduct

universe u

namespace SemistableReduction.Cusp

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {e : ℕ} [NeZero e]

local notation "𝔎" => FractionRing O
local notation "R" => Localization.AtPrime (cuspIdeal O)
local notation "R_e" => Localization.AtPrime (KPoly.ideal O e)
local notation "𝕂" => 𝔎⟮(RatFunc.X : RatFunc 𝔎) ^ e⟯

attribute [local instance 2000] adjoinPowAlgebra locAdjoinPowAlgebra kPolyRatFuncAlgebra
  locRatFuncAlgebra localKummerAlgebra

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search through the intermediate fields of `K(T)` is slow.
set_option maxHeartbeats 1000000 in
-- The many tensor product, localization and intermediate field structures make this slow.
/-- **Tame covers of a chart étale over the cusp chart are tamely Kummer** (MR12 T2 S3 for étale
charts). Let `O` be a discrete valuation ring of characteristic zero with uniformizer `ϖ`, `N` an
étale domain over the cusp chart `O[t]`, `K_N = Frac N`, `𝔫` a prime of `N` over the cusp point,
`K_N ∋ ζ_e`, and `L / K_N` finite Galois of degree dividing `e` whose normalisation `B` over
`N_𝔫` is unramified at every prime over a prime of `N_𝔫` other than the maximal ideal and `(t)`.
Then `L` is tamely Kummer at `𝔫`: étale-locally a product of Kummer covers `t = y ^ e'`,
`e' ∣ e`, of an étale chart `O[X] → N₁`, `X ↦ t`. -/
theorem isTameCuspKummerAt_of_etale [CharZero O] {ϖ : O} (hϖ : Irreducible ϖ)
    (N : Type u) [CommRing N] [IsDomain N] [Algebra O N] [Algebra O[X] N]
    [IsScalarTower O O[X] N] [Algebra.Etale O[X] N] (𝔫 : Ideal N) [𝔫.IsPrime]
    (h𝔫 : 𝔫.comap (algebraMap O[X] N) = cuspIdeal O)
    (K_N : Type u) [Field K_N] [Algebra N K_N] [IsFractionRing N K_N] {ζ : K_N}
    (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K_N L] [FiniteDimensional K_N L] [IsGalois K_N L]
    (hd : finrank K_N L ∣ e) [Algebra N L] [IsScalarTower N K_N L]
    [Algebra (Localization.AtPrime 𝔫) L] [IsScalarTower N (Localization.AtPrime 𝔫) L]
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime 𝔫) B] [Algebra B L]
    [IsScalarTower (Localization.AtPrime 𝔫) B L]
    [IsIntegralClosure B (Localization.AtPrime 𝔫) L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap (Localization.AtPrime 𝔫) B) ≠ maximalIdeal (Localization.AtPrime 𝔫) →
      Q.comap (algebraMap (Localization.AtPrime 𝔫) B) ≠
        Ideal.span {algebraMap N (Localization.AtPrime 𝔫) (algebraMap O[X] N X)} →
      Algebra.IsUnramifiedAt (Localization.AtPrime 𝔫) Q) :
    IsTameCuspKummerAt O e (algebraMap O[X] N X) L 𝔫 := by
  classical
  have he : 0 < e := Nat.pos_of_neZero e
  haveI : IsIntegrallyClosed N := isIntegrallyClosed_of_etale O[X] N
  haveI : IsNoetherianRing N := Algebra.FiniteType.isNoetherianRing O[X] N
  -- the local rings and function fields of the cusp chart (as in `isTameCuspKummerAt_chart`)
  letI := locAdjoinPowAlgebra O e
  haveI := isFractionRing_loc_adjoinPow O e
  haveI := isScalarTower_poly_loc_adjoinPow O e
  haveI : IsFractionRing O[X] 𝕂 := isFractionRing_adjoinPow (O := O) he
  letI := locRatFuncAlgebra' O e
  haveI := isScalarTower_loc_adjoinPow_ratFunc O e
  haveI : IsFractionRing R_e (RatFunc 𝔎) := isFractionRing_locE O e
  haveI : IsScalarTower R R_e (RatFunc 𝔎) := isScalarTower_loc O e
  haveI : IsNoetherianRing R_e := isNoetherianRing_locE O e
  haveI : IsIntegrallyClosed R_e := isIntegrallyClosed_locE O e
  haveI : IsNoetherianRing R := isNoetherianRing_loc O
  haveI : IsIntegrallyClosed R := isIntegrallyClosed_loc O
  haveI := localKummer_finite O e
  -- the generic fibre `𝕂 ⊗_{O[t]} N` of `N` is its fraction field
  letI algNG : Algebra N (𝕂 ⊗[O[X]] N) := Algebra.TensorProduct.rightAlgebra
  have hG : IsField (𝕂 ⊗[O[X]] N) := MulEquiv.isField
    (EtaleDescent.isField_tensor_fractionRing O[X] N)
    ((Algebra.TensorProduct.congr (FractionRing.algEquiv O[X] 𝕂).symm AlgEquiv.refl).trans
      (Algebra.TensorProduct.comm O[X] (FractionRing O[X]) N)).toRingEquiv.toMulEquiv
  haveI : IsLocalization (Algebra.algebraMapSubmonoid N (nonZeroDivisors O[X]))
      (𝕂 ⊗[O[X]] N) :=
    IsLocalization.tensorRight (S := N) 𝕂 (nonZeroDivisors O[X])
  haveI : IsFractionRing N (𝕂 ⊗[O[X]] N) :=
    isFractionRing_of_isLocalization_of_isField
      (Algebra.algebraMapSubmonoid N (nonZeroDivisors O[X])) hG
  let ι₀ : 𝕂 ⊗[O[X]] N ≃ₐ[N] K_N :=
    IsLocalization.algEquiv (nonZeroDivisors N) (𝕂 ⊗[O[X]] N) K_N
  letI : Algebra 𝕂 K_N := (ι₀.toAlgHom.toRingHom.comp (algebraMap 𝕂 (𝕂 ⊗[O[X]] N))).toAlgebra
  let ι : 𝕂 ⊗[O[X]] N ≃ₐ[𝕂] K_N := AlgEquiv.ofRingEquiv (f := ι₀.toRingEquiv) fun _ ↦ rfl
  have hι : ∀ n : N, ι ((1 : 𝕂) ⊗ₜ n) = algebraMap N K_N n := fun n ↦ ι₀.commutes n
  have hιA : ∀ a : O[X], algebraMap 𝕂 K_N (algebraMap O[X] 𝕂 a) =
      algebraMap N K_N (algebraMap O[X] N a) := fun a ↦ by
    rw [← hι]
    change ι₀ (algebraMap O[X] 𝕂 a ⊗ₜ (1 : N)) = _
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  letI : Algebra R K_N := ((algebraMap 𝕂 K_N).comp (algebraMap R 𝕂)).toAlgebra
  haveI : IsScalarTower R 𝕂 K_N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- the étale neighbourhood `R' = R ⊗_{O[t]} N` and the prime `P` over `𝔫`
  letI algNR' : Algebra N (R ⊗[O[X]] N) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid N (cuspIdeal O).primeCompl)
      (R ⊗[O[X]] N) :=
    IsLocalization.tensorRight (S := N) R (cuspIdeal O).primeCompl
  set S := Algebra.algebraMapSubmonoid N (cuspIdeal O).primeCompl with hSdef
  have hS : S ≤ 𝔫.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩ h
    exact ha (by rw [← h𝔫]; exact h)
  have hdisj : Disjoint (S : Set N) 𝔫 := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hS hy hy'
  set P : Ideal (R ⊗[O[X]] N) := 𝔫.map (algebraMap N (R ⊗[O[X]] N)) with hPdef
  haveI hPprime : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint S _ 𝔫 inferInstance hdisj
  have hPc : P.comap (algebraMap N (R ⊗[O[X]] N)) = 𝔫 :=
    IsLocalization.under_map_of_isPrime_disjoint S _ inferInstance hdisj
  have hAN : ∀ a : O[X], algebraMap R (R ⊗[O[X]] N) (algebraMap O[X] R a) =
      algebraMap N (R ⊗[O[X]] N) (algebraMap O[X] N a) := fun a ↦
    Algebra.TensorProduct.tmul_one_eq_one_tmul a
  haveI hPo : P.LiesOver (maximalIdeal R) := by
    refine ⟨?_⟩
    set Q := P.comap (algebraMap R (R ⊗[O[X]] N))
    have hQ : Q.comap (algebraMap O[X] R) = cuspIdeal O := by
      ext a
      change algebraMap R (R ⊗[O[X]] N) (algebraMap O[X] R a) ∈ P ↔ a ∈ cuspIdeal O
      rw [hAN, ← Ideal.mem_comap, hPc, ← Ideal.mem_comap, h𝔫]
    have hQ' : Q = (cuspIdeal O).map (algebraMap O[X] R) := by
      conv_lhs => rw [← IsLocalization.map_under (cuspIdeal O).primeCompl R Q]
      exact congrArg (Ideal.map (algebraMap O[X] R)) hQ
    exact (hQ'.trans Localization.AtPrime.map_eq_maximalIdeal).symm
  -- `N_𝔫` as the local ring of `R'` at `P`
  set Rn := Localization.AtPrime 𝔫
  have hunitS : ∀ y : S, IsUnit (algebraMap N Rn y) := fun y ↦
    IsLocalization.map_units Rn (⟨y, hS y.2⟩ : 𝔫.primeCompl)
  letI : Algebra (R ⊗[O[X]] N) Rn := (IsLocalization.lift (M := S) hunitS).toAlgebra
  haveI : IsScalarTower N (R ⊗[O[X]] N) Rn := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.lift_eq (M := S) hunitS x).symm
  haveI : IsLocalization.AtPrime Rn P := by
    have h0 := IsLocalization.isLocalization_of_submonoid_le (S := R ⊗[O[X]] N)
      (T := Rn) S 𝔫.primeCompl hS
    refine IsLocalization.of_le (𝔫.primeCompl.map (algebraMap N (R ⊗[O[X]] N))) P.primeCompl
      ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩ h
      exact hn (by rw [← hPc]; exact h)
    · intro z hz
      obtain ⟨⟨n, t⟩, rfl⟩ := IsLocalization.mk'_surjective S z
      change IsLocalization.mk' (R ⊗[O[X]] N) n t ∈ P.primeCompl at hz
      change IsUnit (algebraMap (R ⊗[O[X]] N) Rn (IsLocalization.mk' (R ⊗[O[X]] N) n t))
      have hn : n ∉ 𝔫 := fun h ↦ hz (by
        rw [← hPc] at h
        have : IsLocalization.mk' (R ⊗[O[X]] N) n t =
            algebraMap N (R ⊗[O[X]] N) n * IsLocalization.mk' (R ⊗[O[X]] N) (1 : N) t := by
          rw [← IsLocalization.mk'_one (M := S) (R ⊗[O[X]] N) n, ← IsLocalization.mk'_mul,
            mul_one, one_mul]
        rw [this]
        exact P.mul_mem_right _ h)
      have h1 : algebraMap (R ⊗[O[X]] N) Rn (IsLocalization.mk' (R ⊗[O[X]] N) n t) *
          algebraMap N Rn t = algebraMap N Rn n := by
        rw [IsScalarTower.algebraMap_apply N (R ⊗[O[X]] N) Rn t, ← map_mul,
          IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
      have hu : IsUnit (algebraMap N Rn n) := IsLocalization.map_units Rn (⟨n, hn⟩ : 𝔫.primeCompl)
      rw [← h1] at hu
      exact isUnit_of_mul_isUnit_left hu
  letI : Algebra R Rn := ((algebraMap (R ⊗[O[X]] N) Rn).comp
    (algebraMap R (R ⊗[O[X]] N))).toAlgebra
  haveI : IsScalarTower R (R ⊗[O[X]] N) Rn := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hRn : ∀ a : O[X], algebraMap R Rn (algebraMap O[X] R a) =
      algebraMap N Rn (algebraMap O[X] N a) := fun a ↦ by
    rw [IsScalarTower.algebraMap_apply R (R ⊗[O[X]] N) Rn, hAN,
      ← IsScalarTower.algebraMap_apply N (R ⊗[O[X]] N) Rn]
  -- `K_N` as the fraction field of `N_𝔫`
  have hunitK : ∀ t : 𝔫.primeCompl, IsUnit (algebraMap N K_N t) := fun t ↦
    isUnit_iff_ne_zero.mpr fun h ↦ t.2 (by
      rw [(IsFractionRing.injective N K_N) (h.trans (map_zero _).symm)]
      exact 𝔫.zero_mem)
  letI : Algebra Rn K_N := (IsLocalization.lift (M := 𝔫.primeCompl) hunitK).toAlgebra
  haveI : IsScalarTower N Rn K_N := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.lift_eq (M := 𝔫.primeCompl) hunitK x).symm
  haveI : IsFractionRing Rn K_N :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔫.primeCompl Rn K_N
  haveI : IsScalarTower R Rn K_N := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext
      (cuspIdeal O).primeCompl (RingHom.ext fun a ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply R 𝕂 K_N, ← IsScalarTower.algebraMap_apply O[X] R 𝕂, hιA,
      hRn, ← IsScalarTower.algebraMap_apply N Rn K_N]
  haveI : IsScalarTower Rn K_N L := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext 𝔫.primeCompl
      (RingHom.ext fun n ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply N Rn L, ← IsScalarTower.algebraMap_apply N Rn K_N,
      ← IsScalarTower.algebraMap_apply N K_N L]
  -- the parameters of the cusp chart
  have hOR : ∀ c : O, algebraMap O R c = algebraMap O[X] R (C c) := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply O O[X] R, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
  have hϖ₀ : algebraMap O R ϖ ∉ Ideal.span {algebraMap O[X] R X} := by
    rw [hOR]; exact C_notMem_span_t hϖ.ne_zero
  have hm₀ : maximalIdeal R = Ideal.span {algebraMap O[X] R X, algebraMap O R ϖ} := by
    rw [hOR]; exact maximalIdeal_loc_eq_span hϖ
  have htx₀ : algebraMap R R_e (algebraMap O[X] R X) =
      algebraMap (KPoly O e) R_e KPoly.Y ^ e := by
    rw [localKummer_algebraMap, ← KPoly.Y_pow, map_pow]
  have hXx : algebraMap R_e (RatFunc 𝔎) (algebraMap (KPoly O e) R_e KPoly.Y) = RatFunc.X := by
    rw [algebraMap_locE_ratFunc]
    change toRatFunc O 1 X = _
    rw [toRatFunc_X, pow_one]
  have hunr' : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap Rn B) ≠ maximalIdeal Rn →
      Q.comap (algebraMap Rn B) ≠ Ideal.span {algebraMap R Rn (algebraMap O[X] R X)} →
        Algebra.IsUnramifiedAt Rn Q := fun Q _ h1 h2 ↦ hunr Q h1 (by rwa [hRn] at h2)
  -- "S4-local" over `N_𝔫`
  obtain ⟨R'', _, _, _, P'', _, hP'', E, _, _, ⟨φ⟩, e', he', r, ⟨Φ⟩⟩ :=
    exists_etale_tensor_algEquiv_pi_of_etaleNbhd (M := e)
      (residueField_map_localKummer_bijective O e) (prime_t' O e)
      (C_notMem_span_t' (e := e) hϖ.ne_zero) (maximalIdeal_locE_eq_span hϖ) O hϖ
      (prime_t O) hϖ₀ hm₀ htx₀ 𝕂 (RatFunc 𝔎) (X := RatFunc.X)
      (x := ⟨RatFunc.X ^ e, mem_adjoin_simple_self 𝔎 _⟩) rfl
      (Node.adjoin_X_eq_top (O := O) e) (Node.finrank_adjoin_X_pow (O := O) e) hXx
      (R ⊗[O[X]] N) P Rn K_N hζ L hd B hunr'
  obtain ⟨n, hn⟩ : ∃ n, e / e' = n := ⟨_, rfl⟩
  rw [hn] at Φ
  have hne : n * e' = e := by rw [← hn, Nat.div_mul_cancel he']
  have he'0 : 0 < e' := Nat.pos_of_dvd_of_pos he' he
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h ↦ NeZero.ne e (by rw [← hne, h, zero_mul])
  -- descent to an étale domain `N₁` over `N`
  obtain ⟨N₁, _, _, _, _, 𝔫₁, _, h𝔫₁, eL, heL⟩ :=
    EtaleDescent.exists_etale_isDomain_localization_equiv 𝔫 P''
  have h𝔫₁' : 𝔫₁.comap (algebraMap N N₁) = 𝔫 := by
    have h1 : P''.comap (algebraMap Rn R'') = maximalIdeal Rn := hP''.over.symm
    rw [h𝔫₁, ← Ideal.comap_comap, h1]
    exact Localization.AtPrime.under_maximalIdeal
  -- the generic fibre of `N₁` is the function field `E` of the neighbourhood
  have hEfield : IsField (K_N ⊗[Rn] Localization.AtPrime P'') :=
    MulEquiv.isField (Field.toIsField E) φ.toRingEquiv.toMulEquiv
  obtain ⟨θ⟩ := nonempty_tensor_algEquiv_of_localization_equiv
    (B := Rn) (N₁ := N₁) 𝔫₁ eL (fun a ↦ by
      rw [← IsScalarTower.algebraMap_apply N N₁ (Localization.AtPrime 𝔫₁) a, heL,
        IsScalarTower.algebraMap_apply Rn R'' (Localization.AtPrime P'')]) hEfield
  -- the splitting of `N₁ ⊗_N L`
  set F₀ := (𝕂)⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯
  letI : Algebra O[X] F₀ := ((algebraMap 𝕂 F₀).comp (algebraMap O[X] 𝕂)).toAlgebra
  haveI : IsScalarTower O[X] 𝕂 F₀ := IsScalarTower.of_algebraMap_eq' rfl
  let Ψ₁ := tensorEquivPiOfEquiv (θ.trans φ) Φ
  -- the chart `O[X] → N₁`, `X ↦ t`
  letI algAN₁ : Algebra O[X] N₁ := ((algebraMap N N₁).comp (algebraMap O[X] N)).toAlgebra
  haveI : IsScalarTower O[X] N N₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.Etale O[X] N₁ := Algebra.Etale.comp O[X] N N₁
  letI algO : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
  haveI : IsScalarTower O O[X] N₁ := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change algebraMap N N₁ (algebraMap O N c) =
      algebraMap N N₁ (algebraMap O[X] N (algebraMap O O[X] c))
    rw [← IsScalarTower.algebraMap_apply O O[X] N]
  have hX𝔫 : algebraMap O[X] N₁ X ∈ 𝔫₁ := by
    have := X_mem_cuspIdeal (O := O)
    rw [← h𝔫, ← h𝔫₁'] at this
    exact this
  let χ := adjoinPowCuspEquiv (O := O) (e := e) hn0 hne
  let Ψ : N₁ ⊗[N] L ≃ₐ[N₁] (Fin r → CuspFactor O e' N₁) :=
    Ψ₁.trans (AlgEquiv.piCongrRight fun _ ↦
      (tensorTensorEquiv (tensorTensorRingEquiv ι) (tensorTensorRingEquiv_tmul_one ι hι)).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl χ))
  exact ⟨N₁, inferInstance, inferInstance, inferInstance, 𝔫₁, inferInstance, h𝔫₁', algAN₁,
    inferInstance, rfl, inferInstance, hX𝔫, r, fun _ ↦ e', fun _ ↦ he'0, fun _ ↦ he', ⟨Ψ⟩⟩

set_option maxHeartbeats 1000000 in
-- Many localization structures.
/-- **Tame covers of a chart which becomes étale over the cusp chart after localization are
tamely Kummer.** Let `N'` be a domain with a map `f : O[t] → N'` and `N = S⁻¹ N'` a localization,
étale over `N'` and (via `f`) over `O[t]`, and a domain. Let `𝔫` be a prime of `N'` disjoint from
`S` over the cusp point, `K = Frac N' ∋ ζ_e`, and `L / K` finite Galois of degree dividing `e`
whose normalisation `B` over `N'_𝔫` is unramified at every prime over a prime of `N'_𝔫` other than
the maximal ideal and `(f t)`. Then `L` is tamely Kummer at `𝔫` with the coordinate `f t` (from
`isTameCuspKummerAt_of_etale` for `N`, descended along `N' → N`). -/
theorem isTameCuspKummerAt_of_isLocalization_etale [CharZero O] {ϖ : O} (hϖ : Irreducible ϖ)
    {N' : Type u} [CommRing N'] [IsDomain N'] [Algebra O N']
    (N : Type u) [CommRing N] [IsDomain N] [Algebra O N] [Algebra O[X] N]
    [IsScalarTower O O[X] N] [Algebra.Etale O[X] N] [Algebra N' N]
    [IsScalarTower O N' N] (S : Submonoid N') [IsLocalization S N] [Algebra.Etale N' N]
    (f : O[X] →+* N') (hf : ∀ a, algebraMap O[X] N a = algebraMap N' N (f a))
    (𝔫 : Ideal N') [𝔫.IsPrime] (hdisj : Disjoint (S : Set N') 𝔫)
    (h𝔫 : 𝔫.comap f = cuspIdeal O)
    (K : Type u) [Field K] [Algebra N' K] [IsFractionRing N' K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra N' L] [IsScalarTower N' K L]
    [Algebra (Localization.AtPrime 𝔫) L] [IsScalarTower N' (Localization.AtPrime 𝔫) L]
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime 𝔫) B] [Algebra B L]
    [IsScalarTower (Localization.AtPrime 𝔫) B L] [IsIntegralClosure B (Localization.AtPrime 𝔫) L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap (Localization.AtPrime 𝔫) B) ≠ maximalIdeal (Localization.AtPrime 𝔫) →
      Q.comap (algebraMap (Localization.AtPrime 𝔫) B) ≠
        Ideal.span {algebraMap N' (Localization.AtPrime 𝔫) (f X)} →
      Algebra.IsUnramifiedAt (Localization.AtPrime 𝔫) Q) :
    IsTameCuspKummerAt O e (f X) L 𝔫 := by
  classical
  -- the prime of the étale chart over `𝔫`
  set 𝔫E : Ideal N := 𝔫.map (algebraMap N' N)
  haveI : 𝔫E.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint S _ 𝔫 inferInstance hdisj
  letI : SMul N' (Localization.AtPrime 𝔫E) := Algebra.toSMul
  have hc : 𝔫E.comap (algebraMap N' N) = 𝔫 :=
    IsLocalization.under_map_of_isPrime_disjoint S _ inferInstance hdisj
  have h𝔫E : 𝔫E.comap (algebraMap O[X] N) = cuspIdeal O := by
    rw [show algebraMap O[X] N = (algebraMap N' N).comp f from RingHom.ext hf,
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
  letI : Algebra N L := ((algebraMap K L).comp (algebraMap N K)).toAlgebra
  haveI : IsScalarTower N K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower N' N L := IsScalarTower.of_algebraMap_eq fun y ↦ by
    change _ = algebraMap K L (algebraMap N K (algebraMap N' N y))
    rw [← IsScalarTower.algebraMap_apply N' N K, ← IsScalarTower.algebraMap_apply N' K L]
  -- the local rings
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔫E) 𝔫 := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S
      (Localization.AtPrime 𝔫E) 𝔫E
    have hpc : (𝔫E.comap (algebraMap N' N)).primeCompl = 𝔫.primeCompl := by
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
  have hspan : ∀ (Q : Ideal B), Q.comap (algebraMap (Localization.AtPrime 𝔫) B) =
      Ideal.span {algebraMap N' (Localization.AtPrime 𝔫) (f X)} →
      Q.comap (algebraMap (Localization.AtPrime 𝔫E) B) =
        Ideal.span {algebraMap N (Localization.AtPrime 𝔫E) (algebraMap O[X] N X)} := by
    intro Q h
    have h1 : Q.comap (algebraMap (Localization.AtPrime 𝔫E) B) =
        (Q.comap (algebraMap (Localization.AtPrime 𝔫) B)).map
          (e.toRingEquiv : Localization.AtPrime 𝔫 →+* Localization.AtPrime 𝔫E) := by
      rw [Ideal.map_comap_of_equiv]
      rfl
    rw [h1, h, Ideal.map_span, Set.image_singleton, hf,
      ← IsScalarTower.algebraMap_apply N' N (Localization.AtPrime 𝔫E)]
    congr 2
    exact e.commutes (f X)
  have hunr' : ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap (Localization.AtPrime 𝔫E) B) ≠ maximalIdeal (Localization.AtPrime 𝔫E) →
      Q.comap (algebraMap (Localization.AtPrime 𝔫E) B) ≠
        Ideal.span {algebraMap N (Localization.AtPrime 𝔫E) (algebraMap O[X] N X)} →
      Algebra.IsUnramifiedAt (Localization.AtPrime 𝔫E) Q := fun Q _ hQ hQt ↦
    isUnramifiedAt_of_ringEquiv e.toRingEquiv he Q
      (hunr Q (comap_ne_maximalIdeal_of_ringEquiv e.symm.toRingEquiv he' Q hQ)
        fun h ↦ hQt (hspan Q h))
  -- the étale chart is tamely Kummer at `𝔫E`, and this descends to `N'`
  have hK := isTameCuspKummerAt_of_etale hϖ N 𝔫E h𝔫E K hζ L hd B hunr'
  rw [hf] at hK
  have := hK.comap_of_isLocalization S
  rwa [hc] at this

end SemistableReduction.Cusp
