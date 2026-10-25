/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerNodeChart
import TemperedFundamentalGroups.SemistableReduction.NodeCoverEtaleNbhd

/-!
# Tame covers of charts étale over the node are Kummer (MR12 T2 S4, étale charts)

Let `O` be a discrete valuation ring with uniformizer `s`, `A = Node O (s ^ M)` the node chart
`O[u, v] ⧸ (u v - s ^ M)` and `N` an étale `A`-algebra which is a domain (e.g. the Tate chart near
its nodes, `TateTwoChartNode`), with fraction field `K_N`, and `𝔫` a prime of `N` over the closed
point of `A`. Write `M = q M'` and let `K_N` contain a primitive `M'`-th root of unity.

**`NodeCover.isKummerAt_of_etale`**: a finite Galois extension `L / K_N` of degree prime to `q`
whose normalisation over `N_𝔫` is unramified over the punctured spectrum is Kummer at `𝔫`
(`IsKummerAt s M u v L 𝔫`, `u, v` the images of the node coordinates).

Proof: "S4-local" over the local ring `N_𝔫`
(`NodeCover.exists_etale_tensor_algEquiv_pi_of_etaleNbhd`, applied with `R' = R_M ⊗_A N`,
`P` the prime over `𝔫`, `R = N_𝔫`) splits `L` over the function field
of an étale neighbourhood of the closed point of `N_𝔫` into copies of
`K_N ⊗_{K_M} K_M(T ^ n)`; the neighbourhood descends to an étale domain `N₁` over `N`
(`EtaleDescent.exists_etale_isDomain_localization_equiv`; `N` is integrally closed,
`isIntegrallyClosed_of_etale`), and the factors are identified with the Kummer factors
`N₁ ⊗_A Frac (Node O (s ^ n))` (`tensorTensorEquiv`, `K_N ≅ K_M ⊗_A N`).
-/

open Algebra TensorProduct IsLocalRing IntermediateField Module

universe u

namespace SemistableReduction

section IntegrallyClosed

variable {A N : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing N]
  [IsDomain N] [Algebra A N] [Algebra.Etale A N]

variable (A N) in
include A in
/-- **An étale domain over an integrally closed domain is integrally closed.** -/
theorem isIntegrallyClosed_of_etale : IsIntegrallyClosed N := by
  have := EtaleDescent.isFractionRing_tensor_fractionRing A N
  rw [isIntegrallyClosed_iff (N ⊗[A] FractionRing A)]
  intro e he
  have H : Function.Bijective (TensorProduct.toIntegralClosure A N (FractionRing A)) :=
    TensorProduct.toIntegralClosure_bijective_of_smooth
  obtain ⟨t, ht⟩ := H.2 ⟨e, he⟩
  have ht' : (Algebra.TensorProduct.map (AlgHom.id N N)
      (integralClosure A (FractionRing A)).val) t = e := congrArg Subtype.val ht
  rw [← ht']
  clear ht ht' H
  induction t with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | tmul d k =>
    have hk : (k : FractionRing A) ∈ (⊥ : Subalgebra A (FractionRing A)) := by
      rw [← IsIntegrallyClosed.integralClosure_eq_bot A (FractionRing A)]
      exact k.2
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hk
    refine ⟨r • d, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

end IntegrallyClosed

section TensorTensor

variable {A N K₀ K N₁ F₀ : Type*} [CommRing A] [CommRing N] [CommRing K₀] [CommRing K]
  [CommRing N₁] [CommRing F₀] [Algebra A N] [Algebra A K₀] [Algebra K₀ K] [Algebra N K]
  [Algebra N N₁] [Algebra K₀ F₀] [Algebra A F₀] [IsScalarTower A K₀ F₀]
  [Algebra A N₁] [IsScalarTower A N N₁]

/-- The ring isomorphism `K ⊗_{K₀} F₀ ≅ N ⊗_A F₀` induced by `K₀ ⊗_A N ≅ K`. -/
noncomputable def tensorTensorRingEquiv (ι : K₀ ⊗[A] N ≃ₐ[K₀] K) :
    K ⊗[K₀] F₀ ≃+* N ⊗[A] F₀ :=
  (Algebra.TensorProduct.congr ι.symm AlgEquiv.refl).toRingEquiv.trans <|
    (Algebra.TensorProduct.comm K₀ (K₀ ⊗[A] N) F₀).toRingEquiv.trans <|
      (Algebra.TensorProduct.cancelBaseChange A K₀ F₀ F₀ N).toRingEquiv.trans
        (Algebra.TensorProduct.comm A F₀ N).toRingEquiv

lemma tensorTensorRingEquiv_tmul_one (ι : K₀ ⊗[A] N ≃ₐ[K₀] K)
    (hι : ∀ n : N, ι ((1 : K₀) ⊗ₜ n) = algebraMap N K n) (n : N) :
    tensorTensorRingEquiv (F₀ := F₀) ι (algebraMap N K n ⊗ₜ[K₀] (1 : F₀)) =
      algebraMap N (N ⊗[A] F₀) n := by
  have h2 : ι.symm (algebraMap N K n) = (1 : K₀) ⊗ₜ n := by
    rw [AlgEquiv.symm_apply_eq, hι]
  change Algebra.TensorProduct.comm A F₀ N (Algebra.TensorProduct.cancelBaseChange A K₀ F₀ F₀ N
    (Algebra.TensorProduct.comm K₀ (K₀ ⊗[A] N) F₀
      (ι.symm (algebraMap N K n) ⊗ₜ[K₀] (1 : F₀)))) = _
  rw [h2, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul, one_smul, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- **Cancelling the generic fibre.** An `N`-algebra `F` with a ring isomorphism
`γ : F ≅ N ⊗_A F₀` compatible with the maps from `N` (e.g. `F = K ⊗_{K₀} F₀` for
`K ≅ K₀ ⊗_A N`, `tensorTensorRingEquiv`) gives `N₁ ⊗_N F ≅ N₁ ⊗_A F₀`. -/
noncomputable def tensorTensorEquiv {F : Type*} [CommRing F] [Algebra N F] (γ : F ≃+* N ⊗[A] F₀)
    (hγ : ∀ n : N, γ (algebraMap N F n) = algebraMap N (N ⊗[A] F₀) n) :
    N₁ ⊗[N] F ≃ₐ[N₁] N₁ ⊗[A] F₀ :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofRingEquiv (f := γ) hγ)).trans
    (Algebra.TensorProduct.cancelBaseChange A N N₁ N₁ F₀)

end TensorTensor


namespace NodeCover

open Node

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {s : O} {M : ℕ}
  [NeZero M] [(closedPoint s (s ^ M)).IsPrime]

local notation "K" => FractionRing O
local notation "A" => Node O (s ^ M)
local notation "R_M" => Localization.AtPrime (closedPoint s (s ^ M))
local notation "R_1" => Localization.AtPrime (closedPoint s s)
local notation "𝕂" => K⟮(RatFunc.X : RatFunc K) ^ M⟯

attribute [local instance] Node.adjoinPowAlgebra

set_option maxHeartbeats 1000000 in
-- The many tensor product, localization and intermediate field structures make this slow.
/-- **Tame covers of a chart étale over the node are Kummer** (MR12 T2 S4 for étale charts). Let
`N` be an étale domain over the node chart `A = Node O (s ^ M)` (`s` a uniformizer of the
discrete valuation ring `O`), `K_N = Frac N`, `𝔫` a prime of `N` over the closed point of `A`,
`M = q M'`, `K_N ∋ ζ_{M'}`, and `L / K_N` finite Galois of degree prime to `q` whose
normalisation `B` over `N_𝔫` is unramified over the punctured spectrum of `N_𝔫`. Then `L` is
Kummer at `𝔫`: étale-locally a product of Kummer covers `u = w ^ e`, `v = z ^ e`, `e ∣ M'`. -/
theorem isKummerAt_of_etale (hs : Irreducible s) {q M' : ℕ} (hqM : q * M' = M) (hq : 0 < q)
    (hM' : 0 < M') (N : Type u) [CommRing N] [IsDomain N] [Algebra O N] [Algebra A N]
    [IsScalarTower O A N] [Algebra.Etale A N] (𝔫 : Ideal N) [𝔫.IsPrime]
    (h𝔫 : 𝔫.comap (algebraMap A N) = closedPoint s (s ^ M))
    (K_N : Type u) [Field K_N] [Algebra N K_N] [IsFractionRing N K_N] {ζ : K_N}
    (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K_N L] [FiniteDimensional K_N L] [IsGalois K_N L]
    (hL : (finrank K_N L).Coprime q) [Algebra N L] [IsScalarTower N K_N L]
    [Algebra (Localization.AtPrime 𝔫) L] [IsScalarTower N (Localization.AtPrime 𝔫) L]
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime 𝔫) B] [Algebra B L]
    [IsScalarTower (Localization.AtPrime 𝔫) B L]
    [IsIntegralClosure B (Localization.AtPrime 𝔫) L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap (Localization.AtPrime 𝔫) B) ≠ maximalIdeal (Localization.AtPrime 𝔫) →
      Algebra.IsUnramifiedAt (Localization.AtPrime 𝔫) Q) :
    IsKummerAt s M (algebraMap A N (u (s ^ M))) (algebraMap A N (v (s ^ M))) L 𝔫 := by
  classical
  have hs0 : s ≠ 0 := hs.ne_zero
  have hM : 0 < M := Nat.pos_of_neZero M
  haveI : (Ideal.span {s}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hs
  haveI : (closedPoint s s).IsPrime := (isMaximal_closedPoint s (dvd_refl s)).isPrime
  haveI : IsDomain A := Node.isDomain (pow_ne_zero M hs0)
  haveI : IsIntegrallyClosed A := Node.isIntegrallyClosed (pow_ne_zero M hs0)
  haveI : IsIntegrallyClosed N := isIntegrallyClosed_of_etale A N
  haveI : IsNoetherianRing N := Algebra.FiniteType.isNoetherianRing A N
  -- the local rings and function fields of the node (as in `isKummerAt_node`)
  letI : Algebra R_M 𝕂 := (localToAdjoinPow s M hs0).toAlgebra
  haveI : IsFractionRing R_M 𝕂 := isFractionRing_localToAdjoinPow s M hs0
  haveI : IsFractionRing A 𝕂 := isFractionRing_adjoin_pow hs0 hM
  haveI : IsScalarTower A R_M 𝕂 := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.lift_eq (S := R_M) (toAdjoinPow_isUnit s M hs0) x).symm
  letI := localKummerAlgebra s M
  letI : Algebra R_1 (RatFunc K) := (localToRatFunc s hs0).toAlgebra
  haveI : IsFractionRing R_1 (RatFunc K) := isFractionRing_localToRatFunc s hs0
  letI : Algebra R_M (RatFunc K) :=
    ((algebraMap 𝕂 (RatFunc K)).comp (localToAdjoinPow s M hs0)).toAlgebra
  obtain ⟨h₁, h₂⟩ := isScalarTower_localToRatFunc s M hs0
  have := Node.isDomain_localization s M hs0
  have := Node.isNoetherianRing_localization s M
  have := Node.isIntegrallyClosed_localization s M hs0
  have := ThicknessOne.isDomain R_1 hs0
  have := ThicknessOne.isNoetherianRing (s := s) R_1
  have := ThicknessOne.isIntegrallyClosed R_1 hs0
  have := Node.localKummer_finite s M
  have : IsLocalHom (algebraMap R_M R_1) := Node.isLocalHom_localKummer s M
  -- the generic fibre `𝕂 ⊗_A N` of `N` is its fraction field
  letI algNG : Algebra N (𝕂 ⊗[A] N) := Algebra.TensorProduct.rightAlgebra
  have hG : IsField (𝕂 ⊗[A] N) := MulEquiv.isField (EtaleDescent.isField_tensor_fractionRing A N)
    ((Algebra.TensorProduct.congr (FractionRing.algEquiv A 𝕂).symm AlgEquiv.refl).trans
      (Algebra.TensorProduct.comm A (FractionRing A) N)).toRingEquiv.toMulEquiv
  haveI : IsLocalization (Algebra.algebraMapSubmonoid N (nonZeroDivisors A)) (𝕂 ⊗[A] N) :=
    IsLocalization.tensorRight (S := N) 𝕂 (nonZeroDivisors A)
  haveI : IsFractionRing N (𝕂 ⊗[A] N) :=
    isFractionRing_of_isLocalization_of_isField
      (Algebra.algebraMapSubmonoid N (nonZeroDivisors A)) hG
  let ι₀ : 𝕂 ⊗[A] N ≃ₐ[N] K_N := IsLocalization.algEquiv (nonZeroDivisors N) (𝕂 ⊗[A] N) K_N
  letI : Algebra 𝕂 K_N := (ι₀.toAlgHom.toRingHom.comp (algebraMap 𝕂 (𝕂 ⊗[A] N))).toAlgebra
  let ι : 𝕂 ⊗[A] N ≃ₐ[𝕂] K_N := AlgEquiv.ofRingEquiv (f := ι₀.toRingEquiv) fun _ ↦ rfl
  have hι : ∀ n : N, ι ((1 : 𝕂) ⊗ₜ n) = algebraMap N K_N n := fun n ↦ ι₀.commutes n
  have hιA : ∀ a : A, algebraMap 𝕂 K_N (algebraMap A 𝕂 a) = algebraMap N K_N (algebraMap A N a) :=
    fun a ↦ by
      rw [← hι]
      change ι₀ (algebraMap A 𝕂 a ⊗ₜ (1 : N)) = _
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
      rfl
  letI : Algebra R_M K_N := ((algebraMap 𝕂 K_N).comp (algebraMap R_M 𝕂)).toAlgebra
  haveI : IsScalarTower R_M 𝕂 K_N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- the étale neighbourhood `R' = R_M ⊗_A N` and the prime `P` over `𝔫`
  letI algNR' : Algebra N (R_M ⊗[A] N) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid N (closedPoint s (s ^ M)).primeCompl)
      (R_M ⊗[A] N) :=
    IsLocalization.tensorRight (S := N) R_M (closedPoint s (s ^ M)).primeCompl
  set S := Algebra.algebraMapSubmonoid N (closedPoint s (s ^ M)).primeCompl with hSdef
  have hS : S ≤ 𝔫.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩ h
    exact ha (by rw [← h𝔫]; exact h)
  have hdisj : Disjoint (S : Set N) 𝔫 := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hS hy hy'
  set P : Ideal (R_M ⊗[A] N) := 𝔫.map (algebraMap N (R_M ⊗[A] N)) with hPdef
  haveI hPprime : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint S _ 𝔫 inferInstance hdisj
  have hPc : P.comap (algebraMap N (R_M ⊗[A] N)) = 𝔫 :=
    IsLocalization.under_map_of_isPrime_disjoint S _ inferInstance hdisj
  have hAN : ∀ a : A, algebraMap R_M (R_M ⊗[A] N) (algebraMap A R_M a) =
      algebraMap N (R_M ⊗[A] N) (algebraMap A N a) := fun a ↦
    Algebra.TensorProduct.tmul_one_eq_one_tmul a
  haveI hPo : P.LiesOver (maximalIdeal R_M) := by
    refine ⟨?_⟩
    set Q := P.comap (algebraMap R_M (R_M ⊗[A] N))
    have hQ : Q.comap (algebraMap A R_M) = closedPoint s (s ^ M) := by
      ext a
      change algebraMap R_M (R_M ⊗[A] N) (algebraMap A R_M a) ∈ P ↔ a ∈ closedPoint s (s ^ M)
      rw [hAN, ← Ideal.mem_comap, hPc, ← Ideal.mem_comap, h𝔫]
    have hQ' : Q = (closedPoint s (s ^ M)).map (algebraMap A R_M) := by
      conv_lhs => rw [← IsLocalization.map_under (closedPoint s (s ^ M)).primeCompl R_M Q]
      exact congrArg (Ideal.map (algebraMap A R_M)) hQ
    exact (hQ'.trans Localization.AtPrime.map_eq_maximalIdeal).symm
  -- `R = N_𝔫` as the local ring of `R'` at `P`
  set Rn := Localization.AtPrime 𝔫
  have hunitS : ∀ y : S, IsUnit (algebraMap N Rn y) := fun y ↦
    IsLocalization.map_units Rn (⟨y, hS y.2⟩ : 𝔫.primeCompl)
  letI : Algebra (R_M ⊗[A] N) Rn := (IsLocalization.lift (M := S) hunitS).toAlgebra
  haveI : IsScalarTower N (R_M ⊗[A] N) Rn := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.lift_eq (M := S) hunitS x).symm
  haveI : IsLocalization.AtPrime Rn P := by
    have h0 := IsLocalization.isLocalization_of_submonoid_le (R := N) (S := R_M ⊗[A] N) (T := Rn)
      S 𝔫.primeCompl hS
    refine IsLocalization.of_le (𝔫.primeCompl.map (algebraMap N (R_M ⊗[A] N))) P.primeCompl
      ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩ h
      exact hn (by rw [← hPc]; exact h)
    · intro z hz
      obtain ⟨⟨n, t⟩, rfl⟩ := IsLocalization.mk'_surjective S z
      change IsLocalization.mk' (R_M ⊗[A] N) n t ∈ P.primeCompl at hz
      change IsUnit (algebraMap (R_M ⊗[A] N) Rn (IsLocalization.mk' (R_M ⊗[A] N) n t))
      have hn : n ∉ 𝔫 := fun h ↦ hz (by
        rw [← hPc] at h
        have : IsLocalization.mk' (R_M ⊗[A] N) n t =
            algebraMap N (R_M ⊗[A] N) n * IsLocalization.mk' (R_M ⊗[A] N) (1 : N) t := by
          rw [← IsLocalization.mk'_one (M := S) (R_M ⊗[A] N) n, ← IsLocalization.mk'_mul,
            mul_one, one_mul]
        rw [this]
        exact P.mul_mem_right _ h)
      have h1 : algebraMap (R_M ⊗[A] N) Rn (IsLocalization.mk' (R_M ⊗[A] N) n t) *
          algebraMap N Rn t = algebraMap N Rn n := by
        rw [IsScalarTower.algebraMap_apply N (R_M ⊗[A] N) Rn t, ← map_mul,
          IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
      have hu : IsUnit (algebraMap N Rn n) := IsLocalization.map_units Rn (⟨n, hn⟩ : 𝔫.primeCompl)
      rw [← h1] at hu
      exact isUnit_of_mul_isUnit_left hu
  letI : Algebra R_M Rn := ((algebraMap (R_M ⊗[A] N) Rn).comp
    (algebraMap R_M (R_M ⊗[A] N))).toAlgebra
  haveI : IsScalarTower R_M (R_M ⊗[A] N) Rn := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- `K_N` as the fraction field of `R`
  have hunitK : ∀ t : 𝔫.primeCompl, IsUnit (algebraMap N K_N t) := fun t ↦
    isUnit_iff_ne_zero.mpr fun h ↦ t.2 (by
      rw [(IsFractionRing.injective N K_N) (h.trans (map_zero _).symm)]
      exact 𝔫.zero_mem)
  letI : Algebra Rn K_N := (IsLocalization.lift (M := 𝔫.primeCompl) hunitK).toAlgebra
  haveI : IsScalarTower N Rn K_N := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.lift_eq (M := 𝔫.primeCompl) hunitK x).symm
  haveI : IsFractionRing Rn K_N :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔫.primeCompl Rn K_N
  haveI : IsScalarTower R_M Rn K_N := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext
      (closedPoint s (s ^ M)).primeCompl (RingHom.ext fun a ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply R_M 𝕂 K_N, ← IsScalarTower.algebraMap_apply A R_M 𝕂, hιA,
      IsScalarTower.algebraMap_apply R_M (R_M ⊗[A] N) Rn, hAN,
      ← IsScalarTower.algebraMap_apply N (R_M ⊗[A] N) Rn,
      ← IsScalarTower.algebraMap_apply N Rn K_N]
  haveI : IsScalarTower Rn K_N L := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext 𝔫.primeCompl
      (RingHom.ext fun n ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply N Rn L, ← IsScalarTower.algebraMap_apply N Rn K_N,
      ← IsScalarTower.algebraMap_apply N K_N L]
  -- "S4-local" over `N_𝔫`
  obtain ⟨R'', _, _, _, P'', _, hP'', E, _, _, ⟨φ⟩, e, he, r, ⟨Φ⟩⟩ :=
    exists_etale_tensor_algEquiv_pi_of_etaleNbhd
      (residueField_map_localKummer_bijective s M) (ThicknessOne.prime_u R_1 hs)
      (ThicknessOne.v_notMem_span_u R_1 hs) (ThicknessOne.maximalIdeal_eq (s := s) R_1)
      𝕂 (RatFunc K) (X := RatFunc.X) (x := ⟨RatFunc.X ^ M, mem_adjoin_simple_self K _⟩) rfl
      (Node.adjoin_X_eq_top (O := O) M) (Node.finrank_adjoin_X_pow (O := O) M)
      (R_M ⊗[A] N) P Rn K_N hqM hq hM' hζ L hL B hunr
  obtain ⟨n, hn⟩ : ∃ n, q * (M' / e) = n := ⟨_, rfl⟩
  rw [hn] at Φ
  have hne : n * e = M := by rw [← hn, mul_assoc, Nat.div_mul_cancel he, hqM]
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he hM'
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h ↦ NeZero.ne M (by rw [← hne, h, zero_mul])
  have hc : s ^ M = (s ^ n) ^ e := by rw [← pow_mul, hne]
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
  set F₀ := (𝕂)⟮(RatFunc.X : RatFunc K) ^ n⟯
  letI : Algebra A F₀ := ((algebraMap 𝕂 F₀).comp (algebraMap A 𝕂)).toAlgebra
  haveI : IsScalarTower A 𝕂 F₀ := IsScalarTower.of_algebraMap_eq' rfl
  let Ψ₁ := tensorEquivPiOfEquiv (θ.trans φ) Φ
  -- the node chart `Node O ((s ^ n) ^ e) → N₁`
  letI algAN₁ : Algebra A N₁ := ((algebraMap N N₁).comp (algebraMap A N)).toAlgebra
  haveI : IsScalarTower A N N₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.Etale A N₁ := Algebra.Etale.comp A N N₁
  letI algO : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
  haveI : IsScalarTower O A N₁ := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change algebraMap N N₁ (algebraMap O N c) = algebraMap N N₁ (algebraMap A N (algebraMap O A c))
    rw [← IsScalarTower.algebraMap_apply O A N]
  obtain ⟨u₁, hu₁⟩ : ∃ y, y = algebraMap A N₁ (u (s ^ M)) := ⟨_, rfl⟩
  obtain ⟨v₁, hv₁⟩ : ∃ y, y = algebraMap A N₁ (v (s ^ M)) := ⟨_, rfl⟩
  have huv : u₁ * v₁ = algebraMap O N₁ (s ^ M) := by
    rw [hu₁, hv₁, ← map_mul, u_mul_v, ← IsScalarTower.algebraMap_apply]
  have huv' : u₁ * v₁ = algebraMap O N₁ ((s ^ n) ^ e) := by rw [← hc]; exact huv
  have hlift : Node.lift u₁ v₁ huv = IsScalarTower.toAlgHom O A N₁ :=
    Node.algHom_ext (by rw [Node.lift_u, hu₁]; rfl) (by rw [Node.lift_v, hv₁]; rfl)
  have hEt : (Node.lift u₁ v₁ huv).toRingHom.Etale := by
    rw [hlift]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hu𝔫 : u₁ ∈ 𝔫₁ := by
    have := u_mem_closedPoint (a := s ^ M) s
    rw [← h𝔫, ← h𝔫₁'] at this
    rw [hu₁]
    exact this
  have hv𝔫 : v₁ ∈ 𝔫₁ := by
    have := v_mem_closedPoint (a := s ^ M) s
    rw [← h𝔫, ← h𝔫₁'] at this
    rw [hv₁]
    exact this
  letI : Algebra (Node O ((s ^ n) ^ e)) N₁ := nodeAlgebra N₁ (s ^ n) e huv'
  letI : Algebra A (Node O ((s ^ n) ^ e)) := (Node.congr hc).toAlgHom.toRingHom.toAlgebra
  have hN' : (Node.lift u₁ v₁ huv').comp (Node.congr hc).toAlgHom =
      IsScalarTower.toAlgHom O A N₁ := by
    refine Node.algHom_ext ?_ ?_
    · change Node.lift u₁ v₁ huv' (Node.congr hc (u (s ^ M))) = _
      rw [Node.congr_u, Node.lift_u, hu₁]
      rfl
    · change Node.lift u₁ v₁ huv' (Node.congr hc (v (s ^ M))) = _
      rw [Node.congr_v, Node.lift_v, hv₁]
      rfl
  haveI : IsScalarTower A (Node O ((s ^ n) ^ e)) N₁ :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (DFunLike.congr_fun hN' x).symm
  letI : Algebra A (KummerField (s ^ n) e) :=
    ((algebraMap (Node O ((s ^ n) ^ e)) (KummerField (s ^ n) e)).comp
      (algebraMap A (Node O ((s ^ n) ^ e)))).toAlgebra
  haveI : IsScalarTower A (Node O ((s ^ n) ^ e)) (KummerField (s ^ n) e) :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- the factors: `K(T ^ M)(T ^ n) ≅ Frac (Node O (s ^ n))` over `A`
  have hKF : ∀ y : Node O ((s ^ n) ^ e), algebraMap (Node O ((s ^ n) ^ e))
      (KummerField (s ^ n) e) y =
        algebraMap (Node O (s ^ n)) (FractionRing (Node O (s ^ n))) (kummer (s ^ n) e y) :=
    fun y ↦ IsScalarTower.algebraMap_apply (Node O ((s ^ n) ^ e)) (KNode (s ^ n) e)
      (KummerField (s ^ n) e) y
  let χ : F₀ ≃ₐ[A] KummerField (s ^ n) e :=
    AlgEquiv.ofRingEquiv (f := adjoinPowFieldEquiv hs0 hn0 hne) fun x ↦
      (adjoinPowFieldEquiv_algebraMap hs0 hn0 hne hc x).trans (hKF _).symm
  have hsurj : Function.Surjective
      (algebraMap A (Node O ((s ^ n) ^ e))) := (Node.congr hc).surjective
  refine ⟨N₁, inferInstance, inferInstance, inferInstance, 𝔫₁, inferInstance, h𝔫₁', u₁, v₁, huv,
    hEt, hu𝔫, hv𝔫, ⟨1, 1, isUnit_one, isUnit_one, by rw [one_mul, hu₁]; rfl,
      by rw [one_mul, hv₁]; rfl⟩,
    r, fun _ ↦ n, fun _ ↦ e, fun _ ↦ he0, fun _ ↦ hne, ⟨Ψ₁.trans (AlgEquiv.piCongrRight fun _ ↦
      (tensorTensorEquiv (tensorTensorRingEquiv ι) (tensorTensorRingEquiv_tmul_one ι hι)).trans
        ((Algebra.TensorProduct.congr AlgEquiv.refl χ).trans
          (tensorEquivOfSurjective hsurj)))⟩⟩

end NodeCover

end SemistableReduction
