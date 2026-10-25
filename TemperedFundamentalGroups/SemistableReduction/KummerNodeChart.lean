/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerNode
import TemperedFundamentalGroups.SemistableReduction.NodeCoverSplitNode
import TemperedFundamentalGroups.SemistableReduction.EtaleDescent

/-!
# Tame covers of the node chart are Kummer (MR12 T2 S4, step C)

Let `O` be a discrete valuation ring with uniformizer `s`, `K = Frac O`, `N = Node O (s ^ M)` the
node chart `O[u, v] ⧸ (u v - s ^ M)` with closed point `𝔪 = (u, v, s)`, `R_M = N_𝔪` and
`K_M = K(T ^ M)` its function field (`u ↦ T ^ M`). Write `M = q M'` and let `K_M` contain a
primitive `M'`-th root of unity.

**`NodeCover.isKummerAt_node`**: let `L / K_M` be finite Galois of degree prime to `q` whose
normalisation over `R_M` is unramified over the punctured spectrum. Then `L` is Kummer at the
closed point of the node chart (`IsKummerAt s M u v L 𝔪`): over an étale neighbourhood `N₁` of
`𝔪` in `N`, `N₁ ⊗_N L` is a product of copies of `N₁ ⊗_{Node O (s ^ M)} Frac (Node O (s ^ n))`,
`n e = M`, for the Kummer map `u ↦ w ^ e`, `v ↦ z ^ e`.

Proof: "S4-local" (`NodeCover.exists_etale_tensor_algEquiv_pi`) gives an étale neighbourhood
`(R', P)` of the closed point of `R_M` with function field `E` over which `L` splits into
copies of `K_M(T ^ n)`. It descends to an étale domain `N₁` over `N` with `(N₁)_𝔫 ≅ R'_P`
(`EtaleDescent.exists_etale_isDomain_localization_equiv`), and the generic fibre
`K_M ⊗_N N₁` is then `K_M`-isomorphic to `E` (both are fraction fields of `R'_P`,
`nonempty_tensor_algEquiv_of_localization_equiv`). Cancelling the base change
(`tensorEquivPiOfEquiv`) splits `N₁ ⊗_N L` into copies of `N₁ ⊗_N K_M(T ^ n)`, and
`K_M(T ^ n) = K(T ^ n) = Frac (Node O (s ^ n))` compatibly with the Kummer map
(`Node.adjoinPowFieldEquiv_algebraMap`). Finally `N₁ ⊗_N F = N₁ ⊗_{Node O ((s ^ n) ^ e)} F`
along `Node.congr` (`tensorEquivOfSurjective`).
-/

open Algebra TensorProduct IsLocalRing IntermediateField Module

universe u

namespace SemistableReduction

section BaseIso

variable {R R' A B : Type*} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
  [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R' A] [Algebra R' B]
  [IsScalarTower R R' A] [IsScalarTower R R' B]

/-- If `R → R'` is surjective, then `A ⊗_R B ≅ A ⊗_{R'} B` for `R'`-algebras `A`, `B`. -/
noncomputable def tensorEquivOfSurjective (h : Function.Surjective (algebraMap R R')) :
    A ⊗[R] B ≃ₐ[A] A ⊗[R'] B :=
  haveI : TensorProduct.CompatibleSMul R R' A B := ⟨fun r a b ↦ by
    obtain ⟨r, rfl⟩ := h r
    rw [algebraMap_smul R' r a, algebraMap_smul R' r b, TensorProduct.smul_tmul]⟩
  Algebra.TensorProduct.equivOfCompatibleSMul R' R A A B

end BaseIso

section Chain

variable (N K N₁ : Type*) [CommRing N] [CommRing K] [CommRing N₁] [Algebra N K]
  [Algebra N N₁]

/-- `N₁ ⊗_N L ≅ L ⊗_K (K ⊗_N N₁)` for a `K`-algebra `L` (`x ⊗ l ↦ l ⊗ (1 ⊗ x)`). -/
noncomputable def tensorCancelEquiv (L : Type*) [CommRing L] [Algebra K L] [Algebra N L]
    [IsScalarTower N K L] : N₁ ⊗[N] L ≃+* L ⊗[K] (K ⊗[N] N₁) :=
  (Algebra.TensorProduct.comm N N₁ L).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange N K K L N₁).symm.toRingEquiv

variable {N K N₁}

lemma tensorCancelEquiv_tmul {L : Type*} [CommRing L] [Algebra K L] [Algebra N L]
    [IsScalarTower N K L] (x : N₁) (l : L) :
    tensorCancelEquiv N K N₁ L (x ⊗ₜ l) = l ⊗ₜ[K] ((1 : K) ⊗ₜ[N] x) := by
  change (Algebra.TensorProduct.cancelBaseChange N K K L N₁).symm
    (Algebra.TensorProduct.comm N N₁ L (x ⊗ₜ l)) = _
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_symm_tmul]

variable {L F E : Type*} [CommRing L] [CommRing F] [CommRing E] [Algebra K L] [Algebra N L]
  [IsScalarTower N K L] [Algebra K F] [Algebra N F] [IsScalarTower N K F] [Algebra K E]

/-- **Cancelling the base change.** A splitting `E ⊗_K L ≅ ∏ E ⊗_K F` over a `K`-algebra `E`
isomorphic to `K ⊗_N N₁` gives an `N₁`-algebra splitting `N₁ ⊗_N L ≅ ∏ N₁ ⊗_N F`. -/
noncomputable def tensorEquivPiOfEquiv {r : ℕ} (ψ : K ⊗[N] N₁ ≃ₐ[K] E)
    (Φ : E ⊗[K] L ≃ₐ[E] (Fin r → E ⊗[K] F)) : N₁ ⊗[N] L ≃ₐ[N₁] (Fin r → N₁ ⊗[N] F) :=
  AlgEquiv.ofRingEquiv (f := (tensorCancelEquiv N K N₁ L).trans
    ((Algebra.TensorProduct.comm K L (K ⊗[N] N₁)).toRingEquiv.trans
      ((Algebra.TensorProduct.congr ψ AlgEquiv.refl).toRingEquiv.trans
        (Φ.toRingEquiv.trans (RingEquiv.piCongrRight fun _ ↦
          (Algebra.TensorProduct.congr ψ.symm AlgEquiv.refl).toRingEquiv.trans
            ((Algebra.TensorProduct.comm K (K ⊗[N] N₁) F).toRingEquiv.trans
              (tensorCancelEquiv N K N₁ F).symm))))))
    (fun x ↦ by
      funext i
      simp only [Pi.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      have e3 : Algebra.TensorProduct.congr ψ AlgEquiv.refl
          (((1 : K) ⊗ₜ[N] x) ⊗ₜ[K] (1 : L)) = algebraMap E (E ⊗[K] L) (ψ ((1 : K) ⊗ₜ[N] x)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rfl
      have e4 : Φ (algebraMap E (E ⊗[K] L) (ψ ((1 : K) ⊗ₜ[N] x))) i =
          ψ ((1 : K) ⊗ₜ[N] x) ⊗ₜ[K] (1 : F) := by
        rw [AlgEquiv.commutes, Pi.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
      have e5 : Algebra.TensorProduct.congr ψ.symm AlgEquiv.refl
          (ψ ((1 : K) ⊗ₜ[N] x) ⊗ₜ[K] (1 : F)) = ((1 : K) ⊗ₜ[N] x) ⊗ₜ[K] (1 : F) := by
        change ψ.symm (ψ _) ⊗ₜ[K] (AlgEquiv.refl : F ≃ₐ[K] F) 1 = _
        rw [AlgEquiv.symm_apply_apply]
        rfl
      have e7 : (tensorCancelEquiv N K N₁ F).symm ((1 : F) ⊗ₜ[K] ((1 : K) ⊗ₜ[N] x)) =
          x ⊗ₜ[N] (1 : F) :=
        (RingEquiv.symm_apply_eq _).mpr (tensorCancelEquiv_tmul x 1).symm
      change (tensorCancelEquiv N K N₁ F).symm (Algebra.TensorProduct.comm K (K ⊗[N] N₁) F
        (Algebra.TensorProduct.congr ψ.symm AlgEquiv.refl
          (Φ (Algebra.TensorProduct.congr ψ AlgEquiv.refl (Algebra.TensorProduct.comm K L
            (K ⊗[N] N₁) (tensorCancelEquiv N K N₁ L (x ⊗ₜ[N] (1 : L))))) i))) = x ⊗ₜ[N] (1 : F)
      rw [tensorCancelEquiv_tmul, Algebra.TensorProduct.comm_tmul, e3, e4, e5,
        Algebra.TensorProduct.comm_tmul, e7])

end Chain

section Fraction

/-- A localization of a domain which is a field is a fraction field of the domain. -/
theorem isFractionRing_of_isLocalization_of_isField {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] (hB : IsField B) :
    IsFractionRing A B := by
  letI := hB.toField
  have hS : S ≤ nonZeroDivisors A := fun x hx ↦ mem_nonZeroDivisors_of_ne_zero fun h0 ↦ by
    have hu : IsUnit (algebraMap A B x) := IsLocalization.map_units B ⟨x, hx⟩
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  have hinj := IsLocalization.injective B hS
  refine IsLocalization.of_le S _ hS fun r hr ↦ IsUnit.mk0 _ fun h ↦
    nonZeroDivisors.ne_zero hr (hinj ?_)
  rw [h, map_zero]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The function field of a descended étale neighbourhood.** Let `N₁` be an étale domain over
a domain `A` with fraction field `K`, `𝔫` a prime of `N₁`, and `B → C` with `K = Frac B` and
`(N₁)_𝔫 ≅ C` compatibly with `A → B`. If `K ⊗_B C` is a field, it is `K`-isomorphic to the
generic fibre `K ⊗_A N₁` (both are fraction fields of `(N₁)_𝔫 ≅ C`). -/
theorem nonempty_tensor_algEquiv_of_localization_equiv {A K B C N₁ : Type*} [CommRing A]
    [IsDomain A] [CommRing K] [Algebra A K] [IsFractionRing A K] [CommRing B] [Algebra A B]
    [Algebra B K] [IsScalarTower A B K] [IsFractionRing B K] [CommRing C] [Algebra B C]
    [CommRing N₁] [IsDomain N₁] [Algebra A N₁] [Algebra.Etale A N₁] (𝔫 : Ideal N₁) [𝔫.IsPrime]
    (e : Localization.AtPrime 𝔫 ≃+* C)
    (he : ∀ a : A, e (algebraMap N₁ _ (algebraMap A N₁ a)) = algebraMap B C (algebraMap A B a))
    (hC : IsField (K ⊗[B] C)) : Nonempty (K ⊗[A] N₁ ≃ₐ[K] K ⊗[B] C) := by
  -- the generic fibre of `N₁` is a field, hence a fraction field of `N₁` and of `(N₁)_𝔫`
  let φ : K ⊗[A] N₁ ≃ₐ[A] N₁ ⊗[A] FractionRing A :=
    (Algebra.TensorProduct.comm A K N₁).trans
      (Algebra.TensorProduct.congr AlgEquiv.refl (FractionRing.algEquiv A K).symm)
  have hG : IsField (K ⊗[A] N₁) :=
    MulEquiv.isField (EtaleDescent.isField_tensor_fractionRing A N₁) φ.toRingEquiv.toMulEquiv
  haveI : IsFractionRing N₁ (K ⊗[A] N₁) :=
    isFractionRing_of_isLocalization_of_isField
      (Algebra.algebraMapSubmonoid N₁ (nonZeroDivisors A)) hG
  have hu : ∀ t : 𝔫.primeCompl, IsUnit (algebraMap N₁ (K ⊗[A] N₁) t) := fun t ↦
    IsLocalization.map_units (M := nonZeroDivisors N₁) (K ⊗[A] N₁)
      ⟨t, mem_nonZeroDivisors_of_ne_zero fun h ↦ t.2 (by rw [h]; exact 𝔫.zero_mem)⟩
  letI : Algebra (Localization.AtPrime 𝔫) (K ⊗[A] N₁) :=
    (IsLocalization.lift (M := 𝔫.primeCompl) (S := Localization.AtPrime 𝔫) hu).toAlgebra
  haveI : IsScalarTower N₁ (Localization.AtPrime 𝔫) (K ⊗[A] N₁) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IsLocalization.lift_eq (S := Localization.AtPrime 𝔫) hu x).symm
  haveI : IsFractionRing (Localization.AtPrime 𝔫) (K ⊗[A] N₁) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔫.primeCompl _ _
  -- `K ⊗_B C` is a fraction field of `C`
  haveI : IsDomain (Localization.AtPrime 𝔫) :=
    IsLocalization.isDomain_of_atPrime (Localization.AtPrime 𝔫) 𝔫
  haveI : IsDomain C := Function.Injective.isDomain (e.symm : C ≃+* Localization.AtPrime 𝔫)
    e.symm.injective
  haveI : IsFractionRing C (K ⊗[B] C) :=
    isFractionRing_of_isLocalization_of_isField
      (Algebra.algebraMapSubmonoid C (nonZeroDivisors B)) hC
  -- the isomorphism of fraction fields induced by `e`
  let Θ : K ⊗[A] N₁ ≃+* K ⊗[B] C := IsFractionRing.ringEquivOfRingEquiv e
  have key : Θ.toRingHom.comp (algebraMap K (K ⊗[A] N₁)) = algebraMap K (K ⊗[B] C) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a ↦ ?_)
    change Θ (algebraMap K (K ⊗[A] N₁) (algebraMap A K a)) =
      algebraMap K (K ⊗[B] C) (algebraMap A K a)
    have l1 : algebraMap K (K ⊗[A] N₁) (algebraMap A K a) =
        algebraMap N₁ (K ⊗[A] N₁) (algebraMap A N₁ a) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_one_eq_one_tmul]
      rfl
    have l2 : algebraMap K (K ⊗[B] C) (algebraMap A K a) =
        algebraMap C (K ⊗[B] C) (algebraMap B C (algebraMap A B a)) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        IsScalarTower.algebraMap_apply A B K, Algebra.TensorProduct.tmul_one_eq_one_tmul]
      rfl
    rw [l1, l2, IsScalarTower.algebraMap_apply N₁ (Localization.AtPrime 𝔫) (K ⊗[A] N₁),
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, he]
  exact ⟨AlgEquiv.ofRingEquiv (f := Θ) fun k ↦ RingHom.congr_fun key k⟩

end Fraction

namespace Node

variable {O : Type u} [CommRing O] [IsDomain O]

local notation "K" => FractionRing O

omit [IsDomain O] in
open LaurentPolynomial in
/-- The Kummer map `u ↦ w ^ m` followed by `w ↦ T ^ k` is `u ↦ T ^ (k m)`. -/
lemma laurent_comp_kummer_pow (c : O) (k m : ℕ) :
    (laurent c k).comp (kummer c m) = laurent (c ^ m) (k * m) := by
  refine algHom_ext ?_ ?_
  · rw [AlgHom.comp_apply, kummer_u, map_pow, laurent_u, laurent_u, T_pow]
    congr 1
    push_cast
    ring
  · rw [AlgHom.comp_apply, kummer_v, map_pow, laurent_v, laurent_v, mul_pow, T_pow,
      map_pow (algebraMap O _), map_pow LaurentPolynomial.C]
    congr 2
    push_cast
    ring

/-- `Node.toRatFunc` composed with the Kummer map. -/
lemma toRatFunc_comp_kummer_pow (c : O) (k m : ℕ) :
    (toRatFunc c k).comp (kummer c m).toRingHom = toRatFunc (c ^ m) (k * m) := by
  rw [toRatFunc, toRatFunc, ← laurent_comp_kummer_pow]
  rfl

/-- `Node.toRatFunc` is compatible with `Node.congr`. -/
lemma toRatFunc_congr {a b : O} (h : a = b) {k k' : ℕ} (hk : k = k') (x : Node O a) :
    toRatFunc b k' (Node.congr h x) = toRatFunc a k x := by
  subst h hk
  rfl

/-- `K(T ^ M)(T ^ n) = K(T ^ n)` inside `K(T)` for `n e = M`. -/
theorem restrictScalars_adjoin_pow {M n e : ℕ} (h : n * e = M) :
    IntermediateField.restrictScalars K
        ((K⟮(RatFunc.X : RatFunc K) ^ M⟯)⟮(RatFunc.X : RatFunc K) ^ n⟯) =
      K⟮(RatFunc.X : RatFunc K) ^ n⟯ := by
  rw [IntermediateField.restrictScalars_adjoin]
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    rintro t (ht | rfl)
    · have hle : K⟮(RatFunc.X : RatFunc K) ^ M⟯ ≤ K⟮(RatFunc.X : RatFunc K) ^ n⟯ := by
        rw [IntermediateField.adjoin_simple_le_iff, ← h, pow_mul]
        exact pow_mem (IntermediateField.mem_adjoin_simple_self K _) e
      exact hle ht
    · exact IntermediateField.mem_adjoin_simple_self K _
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin K _ (Set.mem_union_right _ rfl)

/-- The identification `K(T ^ M)(T ^ n) = K(T ^ n)` of subfields of `K(T)`, for `n e = M`. -/
noncomputable def adjoinPowEquiv {M n e : ℕ} (h : n * e = M) :
    (K⟮(RatFunc.X : RatFunc K) ^ M⟯)⟮(RatFunc.X : RatFunc K) ^ n⟯ ≃+*
      K⟮(RatFunc.X : RatFunc K) ^ n⟯ where
  toFun x := ⟨x.1, (SetLike.ext_iff.mp (restrictScalars_adjoin_pow h) x.1).mp x.2⟩
  invFun y := ⟨y.1, (SetLike.ext_iff.mp (restrictScalars_adjoin_pow h) y.1).mpr y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

attribute [local instance] Node.adjoinPowAlgebra

/-- `K(T ^ M)(T ^ n) ≅ Frac (Node O (s ^ n))` (`T ^ n ↦ w`), for `n e = M`. -/
noncomputable def adjoinPowFieldEquiv {s : O} (hs : s ≠ 0) {M n e : ℕ} (hn : 0 < n)
    (h : n * e = M) :
    (K⟮(RatFunc.X : RatFunc K) ^ M⟯)⟮(RatFunc.X : RatFunc K) ^ n⟯ ≃+* KummerField (s ^ n) e :=
  haveI := isFractionRing_adjoin_pow hs hn
  haveI := Node.isDomain (pow_ne_zero n hs)
  (adjoinPowEquiv h).trans
    (FractionRing.algEquiv (Node O (s ^ n)) K⟮(RatFunc.X : RatFunc K) ^ n⟯).symm.toRingEquiv

/-- `Node.adjoinPowFieldEquiv` is compatible with the maps from `Node O (s ^ M)`: on
`K(T ^ M)` through `u ↦ T ^ M`, on `Frac (Node O (s ^ n))` through the Kummer map
`u ↦ w ^ e` (after `Node.congr` along `s ^ M = (s ^ n) ^ e`). -/
theorem adjoinPowFieldEquiv_algebraMap {s : O} (hs : s ≠ 0) {M n e : ℕ} (hn : 0 < n)
    (h : n * e = M) (hc : s ^ M = (s ^ n) ^ e) (x : Node O (s ^ M)) :
    adjoinPowFieldEquiv hs hn h (algebraMap K⟮(RatFunc.X : RatFunc K) ^ M⟯
      ((K⟮(RatFunc.X : RatFunc K) ^ M⟯)⟮(RatFunc.X : RatFunc K) ^ n⟯) (toAdjoinPow s M x)) =
      algebraMap (Node O (s ^ n)) (FractionRing (Node O (s ^ n)))
        (kummer (s ^ n) e (Node.congr hc x)) := by
  haveI := isFractionRing_adjoin_pow hs hn
  haveI := Node.isDomain (pow_ne_zero n hs)
  change (FractionRing.algEquiv (Node O (s ^ n))
    K⟮(RatFunc.X : RatFunc K) ^ n⟯).symm (adjoinPowEquiv (O := O) h _) = _
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.commutes]
  apply Subtype.ext
  change toRatFunc (s ^ M) M x = toRatFunc (s ^ n) n (kummer (s ^ n) e (Node.congr hc x))
  rw [← toRatFunc_congr hc h.symm x]
  exact (RingHom.congr_fun (toRatFunc_comp_kummer_pow (s ^ n) n e) _).symm

end Node

namespace NodeCover

open Node

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {s : O} {M : ℕ}
  [NeZero M] [(closedPoint s (s ^ M)).IsPrime]

local notation "K" => FractionRing O
local notation "R_M" => Localization.AtPrime (closedPoint s (s ^ M))
local notation "R_1" => Localization.AtPrime (closedPoint s s)
local notation "𝕂" => K⟮(RatFunc.X : RatFunc K) ^ M⟯

attribute [local instance] Node.adjoinPowAlgebra

set_option maxHeartbeats 1000000 in
-- The many tensor product, localization and intermediate field structures make this slow.
/-- **Tame covers of the node chart are Kummer** (MR12 T2 S4, step C). Let `O` be a discrete
valuation ring with uniformizer `s`, `M = q M'`, `K_M = K(T ^ M)` the function field of the node
chart `N = Node O (s ^ M)` (`u ↦ T ^ M`, `v ↦ s ^ M / T ^ M`), containing a primitive `M'`-th
root of unity, and `L / K_M` finite Galois of degree prime to `q` whose normalisation `B` over the
local ring `R_M` of the closed point is unramified over the punctured spectrum. Then `L` is
Kummer at the closed point of `N`: étale-locally it is a product of Kummer covers
`u = w ^ e`, `v = z ^ e` of the node, `e ∣ M'`. -/
theorem isKummerAt_node (hs : Irreducible s) {q M' : ℕ} (hqM : q * M' = M) (hq : 0 < q)
    (hM' : 0 < M') {ζ : 𝕂} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra 𝕂 L] [FiniteDimensional 𝕂 L] [IsGalois 𝕂 L]
    (hL : (finrank 𝕂 L).Coprime q) [Algebra (Node O (s ^ M)) L]
    [IsScalarTower (Node O (s ^ M)) 𝕂 L] [Algebra R_M L] [IsScalarTower (Node O (s ^ M)) R_M L]
    (B : Type u) [CommRing B] [Algebra R_M B] [Algebra B L] [IsScalarTower R_M B L]
    [IsIntegralClosure B R_M L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap R_M B) ≠ maximalIdeal R_M →
      Algebra.IsUnramifiedAt R_M Q) :
    IsKummerAt s M (u (s ^ M)) (v (s ^ M)) L (closedPoint s (s ^ M)) := by
  classical
  have hs0 : s ≠ 0 := hs.ne_zero
  have hM : 0 < M := Nat.pos_of_neZero M
  haveI : (Ideal.span {s}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hs
  haveI : (closedPoint s s).IsPrime := (isMaximal_closedPoint s (dvd_refl s)).isPrime
  haveI : IsDomain (Node O (s ^ M)) := Node.isDomain (pow_ne_zero M hs0)
  haveI : IsIntegrallyClosed (Node O (s ^ M)) := Node.isIntegrallyClosed (pow_ne_zero M hs0)
  -- the fraction fields `K(T ^ M)` of `N` and `R_M`, and `K(T)` of `R_1`
  letI : Algebra R_M 𝕂 := (localToAdjoinPow s M hs0).toAlgebra
  haveI : IsFractionRing R_M 𝕂 := isFractionRing_localToAdjoinPow s M hs0
  haveI : IsFractionRing (Node O (s ^ M)) 𝕂 := isFractionRing_adjoin_pow hs0 hM
  haveI : IsScalarTower (Node O (s ^ M)) R_M 𝕂 := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.lift_eq (S := R_M) (toAdjoinPow_isUnit s M hs0) x).symm
  letI := localKummerAlgebra s M
  letI : Algebra R_1 (RatFunc K) := (localToRatFunc s hs0).toAlgebra
  haveI : IsFractionRing R_1 (RatFunc K) := isFractionRing_localToRatFunc s hs0
  letI : Algebra R_M (RatFunc K) :=
    ((algebraMap 𝕂 (RatFunc K)).comp (localToAdjoinPow s M hs0)).toAlgebra
  obtain ⟨h₁, h₂⟩ := isScalarTower_localToRatFunc s M hs0
  haveI : IsScalarTower R_M 𝕂 L := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext
      (closedPoint s (s ^ M)).primeCompl (RingHom.ext fun x ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply (Node O (s ^ M)) R_M L x,
      ← IsScalarTower.algebraMap_apply (Node O (s ^ M)) R_M 𝕂 x,
      ← IsScalarTower.algebraMap_apply (Node O (s ^ M)) 𝕂 L x]
  -- "S4-local": the splitting over an étale neighbourhood of the closed point of `R_M`
  obtain ⟨R', _, _, _, P, _, hP, E, _, _, ⟨φ⟩, e, he, r, ⟨Φ⟩⟩ :=
    exists_etale_tensor_algEquiv_pi hs hqM hq hM' 𝕂 (RatFunc K) (X := RatFunc.X)
      (x := ⟨RatFunc.X ^ M, mem_adjoin_simple_self K _⟩) rfl (Node.adjoin_X_eq_top (O := O) M)
      (Node.finrank_adjoin_X_pow (O := O) M) hζ L hL B hunr
  obtain ⟨n, hn⟩ : ∃ n, q * (M' / e) = n := ⟨_, rfl⟩
  rw [hn] at Φ
  have hne : n * e = M := by rw [← hn, mul_assoc, Nat.div_mul_cancel he, hqM]
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he hM'
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h ↦ NeZero.ne M (by rw [← hne, h, zero_mul])
  have hc : s ^ M = (s ^ n) ^ e := by rw [← pow_mul, hne]
  -- descent to an étale domain `N₁` over the node chart
  obtain ⟨N₁, _, _, _, _, 𝔫, _, h𝔫, eL, heL⟩ :=
    EtaleDescent.exists_etale_isDomain_localization_equiv (closedPoint s (s ^ M)) P
  have h𝔫' : 𝔫.comap (algebraMap (Node O (s ^ M)) N₁) = closedPoint s (s ^ M) := by
    have h1 : P.comap (algebraMap R_M R') = maximalIdeal R_M := hP.over.symm
    rw [h𝔫, ← Ideal.comap_comap, h1]
    exact Localization.AtPrime.under_maximalIdeal
  -- the generic fibre of `N₁` is the function field `E` of the neighbourhood
  have hEfield : IsField (𝕂 ⊗[R_M] Localization.AtPrime P) :=
    MulEquiv.isField (Field.toIsField E) φ.toRingEquiv.toMulEquiv
  obtain ⟨θ⟩ := nonempty_tensor_algEquiv_of_localization_equiv (A := Node O (s ^ M))
    (B := R_M) (C := Localization.AtPrime P) (N₁ := N₁) 𝔫 eL (fun a ↦ by
      rw [← IsScalarTower.algebraMap_apply (Node O (s ^ M)) N₁ (Localization.AtPrime 𝔫) a, heL,
        IsScalarTower.algebraMap_apply R_M R' (Localization.AtPrime P)]) hEfield
  -- the splitting of `N₁ ⊗_N L`
  letI : Algebra (Node O (s ^ M)) ((𝕂)⟮(RatFunc.X : RatFunc K) ^ n⟯) :=
    ((algebraMap 𝕂 ((𝕂)⟮(RatFunc.X : RatFunc K) ^ n⟯)).comp
      (algebraMap (Node O (s ^ M)) 𝕂)).toAlgebra
  haveI : IsScalarTower (Node O (s ^ M)) 𝕂 ((𝕂)⟮(RatFunc.X : RatFunc K) ^ n⟯) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let Ψ₁ := tensorEquivPiOfEquiv (θ.trans φ) Φ
  -- the node chart `Node O ((s ^ n) ^ e) → N₁`
  letI algO : Algebra O N₁ := ((algebraMap (Node O (s ^ M)) N₁).comp
    (algebraMap O (Node O (s ^ M)))).toAlgebra
  haveI : IsScalarTower O (Node O (s ^ M)) N₁ := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨u₁, hu₁⟩ : ∃ y, y = algebraMap (Node O (s ^ M)) N₁ (u (s ^ M)) := ⟨_, rfl⟩
  obtain ⟨v₁, hv₁⟩ : ∃ y, y = algebraMap (Node O (s ^ M)) N₁ (v (s ^ M)) := ⟨_, rfl⟩
  have huv : u₁ * v₁ = algebraMap O N₁ (s ^ M) := by
    rw [hu₁, hv₁, ← map_mul, u_mul_v]
    rfl
  have huv' : u₁ * v₁ = algebraMap O N₁ ((s ^ n) ^ e) := by rw [← hc]; exact huv
  have hlift : Node.lift u₁ v₁ huv = IsScalarTower.toAlgHom O (Node O (s ^ M)) N₁ :=
    Node.algHom_ext (by rw [Node.lift_u, hu₁]; rfl) (by rw [Node.lift_v, hv₁]; rfl)
  have hEt : (Node.lift u₁ v₁ huv).toRingHom.Etale := by
    rw [hlift]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hu𝔫 : u₁ ∈ 𝔫 := by
    have := u_mem_closedPoint (a := s ^ M) s
    rw [← h𝔫'] at this
    rw [hu₁]
    exact this
  have hv𝔫 : v₁ ∈ 𝔫 := by
    have := v_mem_closedPoint (a := s ^ M) s
    rw [← h𝔫'] at this
    rw [hv₁]
    exact this
  letI : Algebra (Node O ((s ^ n) ^ e)) N₁ := nodeAlgebra N₁ (s ^ n) e huv'
  letI : Algebra (Node O (s ^ M)) (Node O ((s ^ n) ^ e)) :=
    (Node.congr hc).toAlgHom.toRingHom.toAlgebra
  have hN' : (Node.lift u₁ v₁ huv').comp (Node.congr hc).toAlgHom =
      IsScalarTower.toAlgHom O (Node O (s ^ M)) N₁ := by
    refine Node.algHom_ext ?_ ?_
    · change Node.lift u₁ v₁ huv' (Node.congr hc (u (s ^ M))) = _
      rw [Node.congr_u, Node.lift_u, hu₁]
      rfl
    · change Node.lift u₁ v₁ huv' (Node.congr hc (v (s ^ M))) = _
      rw [Node.congr_v, Node.lift_v, hv₁]
      rfl
  haveI : IsScalarTower (Node O (s ^ M)) (Node O ((s ^ n) ^ e)) N₁ :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (DFunLike.congr_fun hN' x).symm
  letI : Algebra (Node O (s ^ M)) (KummerField (s ^ n) e) :=
    ((algebraMap (Node O ((s ^ n) ^ e)) (KummerField (s ^ n) e)).comp
      (algebraMap (Node O (s ^ M)) (Node O ((s ^ n) ^ e)))).toAlgebra
  haveI : IsScalarTower (Node O (s ^ M)) (Node O ((s ^ n) ^ e)) (KummerField (s ^ n) e) :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- the factors: `K(T ^ M)(T ^ n) ≅ Frac (Node O (s ^ n))` over `N`
  have hKF : ∀ y : Node O ((s ^ n) ^ e), algebraMap (Node O ((s ^ n) ^ e))
      (KummerField (s ^ n) e) y =
        algebraMap (Node O (s ^ n)) (FractionRing (Node O (s ^ n))) (kummer (s ^ n) e y) :=
    fun y ↦ IsScalarTower.algebraMap_apply (Node O ((s ^ n) ^ e)) (KNode (s ^ n) e)
      (KummerField (s ^ n) e) y
  let χ : ((𝕂)⟮(RatFunc.X : RatFunc K) ^ n⟯) ≃ₐ[Node O (s ^ M)] KummerField (s ^ n) e :=
    AlgEquiv.ofRingEquiv (f := adjoinPowFieldEquiv hs0 hn0 hne) fun x ↦
      (adjoinPowFieldEquiv_algebraMap hs0 hn0 hne hc x).trans (hKF _).symm
  have hsurj : Function.Surjective
      (algebraMap (Node O (s ^ M)) (Node O ((s ^ n) ^ e))) := (Node.congr hc).surjective
  refine ⟨N₁, inferInstance, inferInstance, inferInstance, 𝔫, inferInstance, h𝔫', u₁, v₁, huv,
    hEt, hu𝔫, hv𝔫, ⟨1, 1, isUnit_one, isUnit_one, by rw [one_mul, hu₁], by rw [one_mul, hv₁]⟩,
    r, fun _ ↦ n, fun _ ↦ e, fun _ ↦ he0, fun _ ↦ hne, ⟨Ψ₁.trans (AlgEquiv.piCongrRight fun _ ↦
      (Algebra.TensorProduct.congr AlgEquiv.refl χ).trans (tensorEquivOfSurjective hsurj))⟩⟩

end NodeCover

end SemistableReduction
