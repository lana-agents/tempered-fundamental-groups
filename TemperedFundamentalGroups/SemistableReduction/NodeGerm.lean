/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeDescent
import TemperedFundamentalGroups.SemistableReduction.NodeLemma

/-!
# Exact node coordinates at split nodes (W8′, XL1)

Blueprint §9.7 (XL1). Let `A` be a domain of finite type over a DVR `O` (the sections of an
affine open of a model), `𝔭` a point, and suppose that `A` is étale-locally at `𝔭` the singular
point of the node `O[u, v] ⧸ (u v - ϖ ^ n)`, through a split chart (residue field that of `O`),
and that the special fibre of `A_𝔭` has two distinct minimal primes (no loops). Then the local
ring `A_𝔭` has **exact node coordinates** `u v = ϖ ^ n` (`exists_exact_node_of_split`): an
ordinary double point with maximal ideal `(ϖ, u, v)` and residue field that of `O`, whose
coordinates differ from those of the étale chart by units.
-/

universe u

open IsLocalRing

namespace SemistableReduction

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **Exact node coordinates on the Zariski local ring at a split node without loops.** -/
theorem exists_exact_node_of_split {ϖ : O} (hϖ : Irreducible ϖ) {n : ℕ} (hn : 1 ≤ n)
    {A : Type u} [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A]
    [FaithfulSMul O A] (𝔭 : Ideal A) [𝔭.IsPrime]
    {C : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] [Algebra (Node O (ϖ ^ n)) C]
    [Algebra.Etale (Node O (ϖ ^ n)) C] [Algebra O C] [IsScalarTower O A C]
    [IsScalarTower O (Node O (ϖ ^ n)) C] (𝔮 : Ideal C) [𝔮.IsPrime]
    (hc : 𝔮.comap (algebraMap A C) = 𝔭)
    (hu : algebraMap _ C (Node.u (ϖ ^ n)) ∈ 𝔮) (hv : algebraMap _ C (Node.v (ϖ ^ n)) ∈ 𝔮)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔮).comp (algebraMap O C)))
    (P₁ P₂ : Ideal (Localization.AtPrime 𝔭)) [P₁.IsPrime] [P₂.IsPrime]
    (hP₁ : algebraMap O _ ϖ ∈ P₁) (hP₂ : algebraMap O _ ϖ ∈ P₂)
    (hmin₁ : ∀ Q : Ideal (Localization.AtPrime 𝔭), Q.IsPrime → algebraMap O _ ϖ ∈ Q → Q ≤ P₁ →
      Q = P₁)
    (hmin₂ : ∀ Q : Ideal (Localization.AtPrime 𝔭), Q.IsPrime → algebraMap O _ ϖ ∈ Q → Q ≤ P₂ →
      Q = P₂)
    (hne : P₁ ≠ P₂) :
    ∃ (u v : Localization.AtPrime 𝔭) (𝔔₁ 𝔔₂ : Ideal (Localization.AtPrime 𝔭)),
      u * v = algebraMap O _ ϖ ^ n ∧ IsOrdinaryDoublePoint ϖ u v 𝔔₁ 𝔔₂ ∧
      (∃ ε ε' : (Localization.AtPrime 𝔮)ˣ,
        Localization.localRingHom 𝔭 𝔮 (algebraMap A C) hc.symm u =
          ε * algebraMap _ _ (Node.u (ϖ ^ n)) ∧
        Localization.localRingHom 𝔭 𝔮 (algebraMap A C) hc.symm v =
          ε' * algebraMap _ _ (Node.v (ϖ ^ n))) := by
  classical
  let N := Node O (ϖ ^ n)
  let D := Localization.AtPrime 𝔭
  let E := Localization.AtPrime 𝔮
  have hϖn : ϖ ^ n ≠ 0 := pow_ne_zero n hϖ.ne_zero
  haveI : IsDomain N := Node.isDomain hϖn
  haveI : IsIntegrallyClosed N := Node.isIntegrallyClosed hϖn
  -- the étale chart is an ordinary double point
  have hE := isOrdinaryDoublePoint_of_etale hϖ hn 𝔮 hu hv hres
  haveI : IsDomain E := isDomain_localization_of_etale N 𝔮
  haveI : IsIntegrallyClosed E := isIntegrallyClosed_localization_of_etale N 𝔮
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  haveI : Algebra.FiniteType A C := inferInstance
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  haveI : IsNoetherianRing E := IsLocalization.isNoetherianRing 𝔮.primeCompl E inferInstance
  haveI : IsNoetherianRing D := IsLocalization.isNoetherianRing 𝔭.primeCompl D inferInstance
  -- the local map `D → E`
  let φ : D →+* E := Localization.localRingHom 𝔭 𝔮 (algebraMap A C) hc.symm
  letI : Algebra D E := φ.toAlgebra
  have hφ : ∀ a : A, algebraMap D E (algebraMap A D a) = algebraMap C E (algebraMap A C a) :=
    Localization.localRingHom_to_map _ _ _ _
  haveI : IsScalarTower A D E := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [hφ, ← IsScalarTower.algebraMap_apply A C E]
  haveI : IsScalarTower O D E := IsScalarTower.of_algebraMap_eq fun o ↦ by
    rw [IsScalarTower.algebraMap_apply O A D o, ← IsScalarTower.algebraMap_apply A D E,
      IsScalarTower.algebraMap_apply A C E (algebraMap O A o),
      ← IsScalarTower.algebraMap_apply O A C, ← IsScalarTower.algebraMap_apply O C E]
  haveI : Module.Flat D E := by
    rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.localRingHom
      (RingHom.flat_algebraMap_iff.mpr inferInstance) 𝔮 𝔭 hc.symm
  haveI : IsLocalHom (algebraMap D E) := Localization.isLocalHom_localRingHom _ _ _ _
  haveI : Algebra.FormallyUnramified C E := .of_isLocalization 𝔮.primeCompl
  haveI : Algebra.FormallyUnramified A E := .comp A C E
  haveI : Algebra.FormallyUnramified D E := .of_restrictScalars A D E
  haveI : Algebra.EssFiniteType C E := .of_isLocalization E 𝔮.primeCompl
  haveI : Algebra.EssFiniteType A E := .comp A C E
  haveI : Algebra.EssFiniteType D E := .of_comp A D E
  have hϖ0 : algebraMap O E ϖ ≠ 0 := by
    haveI : Module.FaithfullyFlat D E := Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hDE : Function.Injective (algebraMap D E) :=
      (FaithfulSMul.algebraMap_injective D E)
    have hAD : Function.Injective (algebraMap A D) :=
      IsLocalization.injective D 𝔭.primeCompl_le_nonZeroDivisors
    rw [IsScalarTower.algebraMap_apply O D E, IsScalarTower.algebraMap_apply O A D]
    exact fun h ↦ hϖ.ne_zero ((FaithfulSMul.algebraMap_injective O A)
      (hAD (hDE (by rw [h, map_zero, map_zero, map_zero]))))
  have huvE : algebraMap N E (Node.u (ϖ ^ n)) * algebraMap N E (Node.v (ϖ ^ n)) =
      algebraMap O E ϖ ^ n := by
    rw [← map_mul, Node.u_mul_v, IsScalarTower.algebraMap_apply N C E,
      ← IsScalarTower.algebraMap_apply O N C, ← IsScalarTower.algebraMap_apply O C E, map_pow]
  -- descent and exact coordinates
  obtain ⟨u', v', hD, hu', hv'⟩ := hE.descent hn huvE P₁ P₂ hP₁ hP₂ hmin₁ hmin₂ hne
  obtain ⟨u₀, v₀, huv₀, hmax₀, hu₀, ⟨ε, hε⟩, ⟨ε', hε'⟩⟩ :=
    IsOrdinaryDoublePoint.exists_node_of_flat hϖ hϖ0 hn huvE hE hD hu'
  have hu₀₁ : u₀ ∉ (Ideal.span {algebraMap O E ϖ, algebraMap N E (Node.v (ϖ ^ n))}).comap
      (algebraMap D E) := fun h ↦ by
    haveI := hD.isPrime₁
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu₀
    have h1 : u₀ - u' ∈ (Ideal.span {algebraMap O E ϖ,
        algebraMap N E (Node.v (ϖ ^ n))}).comap (algebraMap D E) := by
      rw [← ha]; exact Ideal.mul_mem_left _ _ hD.mem₁
    have := sub_mem h h1
    rw [sub_sub_cancel] at this
    exact hD.notMem₁ this
  have hv₀₂ : v₀ ∉ (Ideal.span {algebraMap O E ϖ, algebraMap N E (Node.u (ϖ ^ n))}).comap
      (algebraMap D E) := fun h ↦ by
    rw [Ideal.mem_comap, hε'] at h
    haveI := hE.isPrime₂
    exact hE.notMem₂ ((Ideal.mul_mem_left _ (↑ε'⁻¹ : E) h) |> fun h' ↦ by
      rwa [← mul_assoc, Units.inv_mul, one_mul] at h')
  refine ⟨u₀, v₀, (Ideal.span {algebraMap O E ϖ, algebraMap N E (Node.v (ϖ ^ n))}).comap
    (algebraMap D E), (Ideal.span {algebraMap O E ϖ, algebraMap N E (Node.u (ϖ ^ n))}).comap
    (algebraMap D E), huv₀, ?_, ε, ε', hε, hε'⟩
  exact
    { hD with
      maximalIdeal_eq := hmax₀
      mul_mem := Ideal.mem_span_singleton'.mpr ⟨algebraMap O D ϖ ^ (n - 1), by
        rw [huv₀, ← pow_succ, Nat.sub_add_cancel hn]⟩
      notMem₁ := hu₀₁
      notMem₂ := hv₀₂ }

/-- **The Zariski local ring at a node is flat (indeed essentially étale) over the node** via
exact node coordinates `u v = ϖ ^ n` (XL1 (h)). -/
theorem flat_node_of_isOrdinaryDoublePoint {ϖ : O} (hϖ : Irreducible ϖ) {n : ℕ}
    {B : Type u} [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    [FaithfulSMul O B] (𝔭 : Ideal B) [𝔭.IsPrime] {u v : Localization.AtPrime 𝔭}
    (huv : u * v = algebraMap O _ (ϖ ^ n)) {𝔔₁ 𝔔₂ : Ideal (Localization.AtPrime 𝔭)}
    (H : IsOrdinaryDoublePoint ϖ u v 𝔔₁ 𝔔₂) :
    letI := (Node.lift u v huv).toRingHom.toAlgebra
    Module.Flat (Node O (ϖ ^ n)) (Localization.AtPrime 𝔭) := by
  classical
  let D := Localization.AtPrime 𝔭
  let ιD := algebraMap B D
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  haveI : IsNoetherianRing D := IsLocalization.isNoetherianRing 𝔭.primeCompl D inferInstance
  have hιD : Function.Injective ιD :=
    IsLocalization.injective D 𝔭.primeCompl_le_nonZeroDivisors
  have hOB : Function.Injective (algebraMap O B) := FaithfulSMul.algebraMap_injective O B
  have hϖ0 : algebraMap O D ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply O B D]
    exact fun h ↦ hϖ.ne_zero (hOB (hιD (by rw [h, map_zero, map_zero])))
  have hmaxD : ∀ z : B, z ∉ 𝔭 → ιD z ∉ maximalIdeal D := fun z hz h ↦
    h (IsLocalization.map_units D (⟨z, hz⟩ : 𝔭.primeCompl))
  -- a common denominator `t`
  obtain ⟨⟨t, ht⟩, htint⟩ := IsLocalization.exist_integer_multiples_of_finset 𝔭.primeCompl
    ({u, v} : Finset D)
  have hpre : ∀ z ∈ ({u, v} : Finset D), ∃ b : B, ιD b = ιD t * z := fun z hz ↦ by
    obtain ⟨b, hb⟩ := htint z hz
    exact ⟨b, by rw [hb, Algebra.smul_def]⟩
  let C₀ := Localization.Away t
  have htD : IsUnit (ιD t) := IsLocalization.map_units D (⟨t, ht⟩ : 𝔭.primeCompl)
  let φ₀ : C₀ →+* D := IsLocalization.Away.lift t htD
  have hφ₀ : ∀ b, φ₀ (algebraMap B C₀ b) = ιD b := fun b ↦ IsLocalization.lift_eq _ b
  have hmk : ∀ (b : B) (m : Submonoid.powers t),
      φ₀ (IsLocalization.mk' C₀ b m) * ιD m = ιD b := fun b m ↦ by
    rw [← hφ₀, ← hφ₀, ← map_mul, IsLocalization.mk'_spec]
  have hφ₀inj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) z
    have h1 := hmk b m
    simp only at hz h1
    rw [hz, zero_mul] at h1
    have hb : b = 0 := hιD (by rw [← h1, map_zero])
    simp [hb]
  have hlift : ∀ z ∈ ({u, v} : Finset D), ∃ z₀ : C₀, φ₀ z₀ = z := by
    intro z hz
    obtain ⟨b, hb⟩ := hpre z hz
    refine ⟨IsLocalization.mk' C₀ b (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t), ?_⟩
    have h1 := hmk b ⟨t, Submonoid.mem_powers t⟩
    simp only at h1
    rw [hb, mul_comm] at h1
    exact (htD.mul_left_cancel h1)
  obtain ⟨u₀, hu₀⟩ := hlift u (by simp)
  obtain ⟨v₀, hv₀⟩ := hlift v (by simp)
  have hφO : ∀ o, φ₀ (algebraMap O C₀ o) = algebraMap O D o := fun o ↦ by
    rw [IsScalarTower.algebraMap_apply O B C₀, hφ₀, ← IsScalarTower.algebraMap_apply]
  have huv₀ : u₀ * v₀ = algebraMap O C₀ (ϖ ^ n) := hφ₀inj (by rw [map_mul, hu₀, hv₀, hφO, huv])
  -- `C₀` over the node
  have hϖn : ϖ ^ n ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  haveI : IsDomain (Node O (ϖ ^ n)) := Node.isDomain hϖn
  haveI : IsIntegrallyClosed (Node O (ϖ ^ n)) := Node.isIntegrallyClosed hϖn
  have ht0 : t ≠ 0 := fun h ↦ ht (h ▸ zero_mem 𝔭)
  haveI : IsDomain C₀ := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)
  let χ : Node O (ϖ ^ n) →ₐ[O] C₀ := Node.lift u₀ v₀ huv₀
  letI : Algebra (Node O (ϖ ^ n)) C₀ := χ.toRingHom.toAlgebra
  haveI : IsScalarTower O (Node O (ϖ ^ n)) C₀ :=
    IsScalarTower.of_algebraMap_eq fun o ↦ (χ.commutes o).symm
  let φ₀A : C₀ →ₐ[O] D := { φ₀ with commutes' := hφO }
  have hcomp : φ₀A.comp χ = Node.lift u v huv :=
    Node.algHom_ext (by simp [χ, φ₀A, hu₀]) (by simp [χ, φ₀A, hv₀])
  have hχinj : Function.Injective (algebraMap (Node O (ϖ ^ n)) C₀) := by
    haveI := H.isPrime₁
    have hinjD := Node.lift_injective hϖn huv
      (fun P hP ↦ H.transcendental_of_irreducible hϖ hϖ0 H.isDiscreteValuationRing_quotient.2 hP)
    intro a b hab
    apply hinjD
    rw [← hcomp]
    simp only [AlgHom.comp_apply]
    exact congrArg φ₀A hab
  haveI : Algebra.FiniteType B C₀ :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers t) C₀
  haveI : Algebra.FiniteType O C₀ := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  haveI : Algebra.FiniteType (Node O (ϖ ^ n)) C₀ :=
    .of_restrictScalars_finiteType O (Node O (ϖ ^ n)) C₀
  -- the point `P` of `C₀` and `D = (C₀)_P`
  letI : Algebra C₀ D := φ₀.toAlgebra
  haveI : IsScalarTower B C₀ D := IsScalarTower.of_algebraMap_eq fun b ↦ (hφ₀ b).symm
  let P : Ideal C₀ := (maximalIdeal D).comap (algebraMap C₀ D)
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  haveI : IsLocalization P.primeCompl D := by
    rw [isLocalization_iff]
    refine ⟨fun y ↦ ?_, fun z ↦ ?_, fun {a b} hab ↦ ⟨1, by rw [hφ₀inj hab]⟩⟩
    · by_contra h
      exact y.2 ((mem_maximalIdeal _).mpr h)
    · obtain ⟨⟨b, m⟩, hbm⟩ := IsLocalization.surj 𝔭.primeCompl z
      refine ⟨⟨algebraMap B C₀ b, algebraMap B C₀ m, ?_⟩, ?_⟩
      · change algebraMap C₀ D (algebraMap B C₀ m) ∉ maximalIdeal D
        rw [← IsScalarTower.algebraMap_apply]
        exact hmaxD m m.2
      · simp only
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        exact hbm
  -- unramified at `P` over the node
  let N := Node O (ϖ ^ n)
  letI iND : Algebra N D := ((algebraMap C₀ D).comp (algebraMap N C₀)).toAlgebra
  haveI : IsScalarTower N C₀ D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hND : ∀ z, algebraMap N D z = φ₀ (χ z) := fun _ ↦ rfl
  haveI : Algebra.EssFiniteType C₀ D := .of_isLocalization D P.primeCompl
  haveI : Algebra.EssFiniteType N D := .comp N C₀ D
  have hunrD : Algebra.FormallyUnramified N D := by
    refine formallyUnramified_of_map_maximalIdeal ?_ fun z ↦ ?_
    · refine le_antisymm ?_ Ideal.map_comap_le
      have hmem : ∀ w : N, algebraMap N D w ∈ maximalIdeal D →
          algebraMap N D w ∈ Ideal.map (algebraMap N D)
            ((maximalIdeal D).comap (algebraMap N D)) :=
        fun w hw ↦ Ideal.mem_map_of_mem _ hw
      have hu' : algebraMap N D (Node.u (ϖ ^ n)) = u := by
        rw [hND]; simp [χ, hu₀]
      have hv' : algebraMap N D (Node.v (ϖ ^ n)) = v := by
        rw [hND]; simp [χ, hv₀]
      have hp' : algebraMap N D (algebraMap O N ϖ) = algebraMap O D ϖ := by
        rw [hND, AlgHom.commutes, hφO]
      have hmaxu : u ∈ maximalIdeal D := by
        rw [H.maximalIdeal_eq]
        exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      have hmaxv : v ∈ maximalIdeal D := by
        rw [H.maximalIdeal_eq]; exact Ideal.subset_span (by simp)
      have hmaxp : algebraMap O D ϖ ∈ maximalIdeal D := by
        rw [H.maximalIdeal_eq]; exact Ideal.subset_span (Set.mem_insert _ _)
      calc maximalIdeal D = Ideal.span {algebraMap O D ϖ, u, v} := H.maximalIdeal_eq
        _ ≤ _ := by
          rw [Ideal.span_le]
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hz | hz | hz <;> rw [hz]
          · rw [← hp'] at hmaxp ⊢; exact hmem _ hmaxp
          · rw [← hu'] at hmaxu ⊢; exact hmem _ hmaxu
          · rw [← hv'] at hmaxv ⊢; exact hmem _ hmaxv
    · obtain ⟨o, ho⟩ := H.residue z
      refine ⟨algebraMap O N o, ?_⟩
      rwa [hND, AlgHom.commutes, hφO]
  let e : Localization.AtPrime P ≃ₐ[C₀] D := IsLocalization.algEquiv P.primeCompl _ _
  haveI : Algebra.IsUnramifiedAt N P :=
    Algebra.FormallyUnramified.of_equiv (e.symm.restrictScalars N)
  have hflat : Module.Flat N (Localization.AtPrime P) :=
    (isEtaleAt_and_flat_of_isUnramifiedAt hχinj P).2
  have hflatD : Module.Flat N D :=
    Module.Flat.of_linearEquiv (e.symm.restrictScalars N).toLinearEquiv
  -- the two `N`-algebra structures on `D` agree
  have hEq : (Node.lift u v huv).toRingHom = algebraMap N D := by
    rw [← hcomp]; rfl
  have hinst : (Node.lift u v huv).toRingHom.toAlgebra = iND := by
    rw [hEq]; exact Algebra.algebra_ext _ _ fun _ ↦ rfl
  convert hflatD

end SemistableReduction
