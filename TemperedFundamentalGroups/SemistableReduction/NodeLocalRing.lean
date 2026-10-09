/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeDeformation
import TemperedFundamentalGroups.SemistableReduction.EtaleLocalDomain
import TemperedFundamentalGroups.SemistableReduction.NodeSmooth

/-!
# Local rings of étale neighbourhoods of a node (W8′, XL1)

Blueprint §9.7 (XL1). Let `C` be étale over the node `N = O[u, v] ⧸ (u v - ϖ ^ n)` (`O` a DVR,
`n ≥ 1`) and `𝔮` a point of `C` over the singular point with residue field that of `O`. Then the
local ring `E = C_𝔮` is an ordinary double point over `O` in the sense of `IsOrdinaryDoublePoint`
(with coordinates the images of `u, v`, branches `(ϖ, v)` and `(ϖ, u)`):

* local rings of étale algebras over normal domains are normal (`isIntegrallyClosed_of_etale`,
  from `EtaleLocalDomain`);
* localization commutes with quotients (`isLocalization_quotient`), so `E ⧸ (ϖ, u)` is a local
  ring of the étale `N ⧸ (ϖ, u) ≅ (O ⧸ ϖ)[v]`-algebra `C ⧸ (ϖ, u)`, hence a domain in which `v`
  is not zero;
* the maximal ideal is `(ϖ, u, v)` since `C` is unramified over `N`.
-/

open IsLocalRing TensorProduct

namespace SemistableReduction

section Normal

variable {R A : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A]
  [Algebra R A] [Algebra.Etale R A] (Q : Ideal A) [Q.IsPrime]

variable (R) in
include R in
/-- **Local rings of étale algebras over normal domains are normal.** -/
theorem isIntegrallyClosed_localization_of_etale :
    IsIntegrallyClosed (Localization.AtPrime Q) := by
  haveI := isDomain_localization_of_etale R Q
  let D := Localization.AtPrime Q
  let K := FractionRing R
  letI := (isField_tensor_fractionRing R Q).toField
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D (nonZeroDivisors R)) (D ⊗[R] K) :=
    IsLocalization.tensor (S := D) K (nonZeroDivisors R)
  have hinj := includeLeft_injective_fractionRing (R := R) Q
  haveI : IsFractionRing D (D ⊗[R] K) := by
    refine IsLocalization.of_le (Algebra.algebraMapSubmonoid D (nonZeroDivisors R)) _
      (fun _ ⟨r, hr, e⟩ ↦ e ▸ ?_) fun d hd ↦ ?_
    · rw [mem_nonZeroDivisors_iff_ne_zero]
      intro h0
      have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := D) hr
      apply one_ne_zero (α := D)
      apply hreg
      simp only [Algebra.smul_def, mul_one, mul_zero]
      exact h0
    · refine IsUnit.mk0 _ fun h0 ↦ nonZeroDivisors.ne_zero hd (hinj ?_)
      rw [map_zero]; exact h0
  rw [isIntegrallyClosed_iff (D ⊗[R] K)]
  intro x hx
  obtain ⟨d, hd⟩ := exists_eq_tmul_one_of_isIntegral Q hx
  exact ⟨d, hd⟩

end Normal

section Quotient

variable {C E : Type*} [CommRing C] [CommRing E] [Algebra C E] (M : Submonoid C)
  [IsLocalization M E] (I : Ideal C)

/-- **Localization commutes with quotients**: `E ⧸ I E` is the localization of `C ⧸ I` at the
image of `M`. -/
theorem isLocalization_quotient :
    letI : Algebra (C ⧸ I) (E ⧸ I.map (algebraMap C E)) :=
      (Ideal.quotientMap _ (algebraMap C E) Ideal.le_comap_map).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I)) (E ⧸ I.map (algebraMap C E)) := by
  letI : Algebra (C ⧸ I) (E ⧸ I.map (algebraMap C E)) :=
    (Ideal.quotientMap _ (algebraMap C E) Ideal.le_comap_map).toAlgebra
  have halg : ∀ c : C, algebraMap (C ⧸ I) (E ⧸ I.map (algebraMap C E)) (Ideal.Quotient.mk I c) =
      Ideal.Quotient.mk _ (algebraMap C E c) := fun _ ↦ rfl
  rw [isLocalization_iff]
  refine ⟨?_, fun z ↦ ?_, fun {a b} hab ↦ ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    rw [halg]
    exact (IsLocalization.map_units E (⟨m, hm⟩ : M)).map _
  · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨c, m⟩, hcm⟩ := IsLocalization.surj M z
    refine ⟨⟨Ideal.Quotient.mk I c, ⟨_, m, m.2, rfl⟩⟩, ?_⟩
    simp only [halg]
    rw [← map_mul, hcm]
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [halg, halg, Ideal.Quotient.eq, ← map_sub,
      IsLocalization.mem_map_algebraMap_iff M] at hab
    obtain ⟨⟨i, m⟩, him⟩ := hab
    simp only at him
    rw [← map_mul, ← sub_eq_zero, ← map_sub, IsLocalization.map_eq_zero_iff M] at him
    obtain ⟨m', hm'⟩ := him
    refine ⟨⟨_, m' * m, (m' * m).2, rfl⟩, ?_⟩
    simp only
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
    have : (m' : C) * m * (a - b) = m' * i := by linear_combination hm'
    rw [this]
    exact Ideal.mul_mem_left _ _ i.2

end Quotient

section BranchQuotient

variable {N C : Type*} [CommRing N] [CommRing C] [Algebra N C] [Algebra.Etale N C] (I : Ideal N)
  [IsDomain (N ⧸ I)] [IsIntegrallyClosed (N ⧸ I)] (𝔮 : Ideal C) [𝔮.IsPrime]

/-- **Branch quotients of local rings of étale algebras**: if `N ⧸ I` is a normal domain and
`I C ⊆ 𝔮`, then `I C_𝔮` is a prime ideal of `C_𝔮`, and elements of `N` outside `I` stay outside
it. -/
theorem isPrime_map_localization_of_etale (hI : I.map (algebraMap N C) ≤ 𝔮) :
    (I.map (algebraMap N (Localization.AtPrime 𝔮))).IsPrime ∧
      ∀ a : N, a ∉ I → algebraMap N (Localization.AtPrime 𝔮) a ∉
        I.map (algebraMap N (Localization.AtPrime 𝔮)) := by
  let E := Localization.AtPrime 𝔮
  let IC := I.map (algebraMap N C)
  let A := C ⧸ IC
  haveI : Algebra.Etale (N ⧸ I) A :=
    .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm
  let Q : Ideal A := 𝔮.map (Ideal.Quotient.mk IC)
  have hQ : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hI)
  have hQc : ∀ c : C, Ideal.Quotient.mk IC c ∈ Q ↔ c ∈ 𝔮 := fun c ↦ by
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · rintro ⟨c', hc', e⟩
      rw [Ideal.Quotient.eq] at e
      have := add_mem hc' (hI (by simpa using neg_mem e : c - c' ∈ IC))
      simpa using this
    · intro hc; exact ⟨c, hc, rfl⟩
  haveI := isDomain_localization_of_etale (N ⧸ I) Q
  -- `E ⧸ I E` is the localization of `A` at `Q`
  have hIE : I.map (algebraMap N E) = IC.map (algebraMap C E) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  letI : Algebra A (E ⧸ IC.map (algebraMap C E)) :=
    (Ideal.quotientMap _ (algebraMap C E) Ideal.le_comap_map).toAlgebra
  haveI hloc := isLocalization_quotient 𝔮.primeCompl IC (E := E)
  have hsub : 𝔮.primeCompl.map (Ideal.Quotient.mk IC) = Q.primeCompl := by
    ext z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨c', hc', e⟩
      rw [← e, hQc]; exact hc'
    · intro hc
      exact ⟨c, by rwa [hQc] at hc, rfl⟩
  rw [hsub] at hloc
  let e : Localization.AtPrime Q ≃ₐ[A] E ⧸ IC.map (algebraMap C E) :=
    IsLocalization.algEquiv Q.primeCompl _ _
  haveI : IsDomain (E ⧸ IC.map (algebraMap C E)) := e.toRingEquiv.symm.injective.isDomain _
  refine ⟨?_, fun a ha h ↦ ?_⟩
  · rw [hIE]; exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  · -- flatness of `A_Q` over `N ⧸ I`
    have hmk : Ideal.Quotient.mk I a ∈ nonZeroDivisors (N ⧸ I) := by
      rw [mem_nonZeroDivisors_iff_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
    haveI : Module.Flat (N ⧸ I) (Localization.AtPrime Q) :=
      Module.Flat.trans (N ⧸ I) A (Localization.AtPrime Q)
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
      (M := Localization.AtPrime Q) hmk
    apply one_ne_zero (α := Localization.AtPrime Q)
    apply hreg
    simp only [Algebra.smul_def, mul_one, mul_zero]
    apply e.injective
    rw [map_zero, IsScalarTower.algebraMap_apply (N ⧸ I) A (Localization.AtPrime Q),
      AlgEquiv.commutes]
    change Ideal.Quotient.mk _ (algebraMap C E (algebraMap N C a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← IsScalarTower.algebraMap_apply, ← hIE]
    exact h

end BranchQuotient

section NodeQuotientU

variable {O : Type*} [CommRing O] (ϖ : O) {n : ℕ} (hn : 1 ≤ n)

/-- The ideal `(ϖ, u)` of the node. -/
noncomputable def Node.idealU : Ideal (Node O (ϖ ^ n)) :=
  Ideal.span {algebraMap O (Node O (ϖ ^ n)) ϖ, Node.u (ϖ ^ n)}

include hn in
/-- The map `O[u, v] ⧸ (u v - ϖ ^ n) → (O ⧸ ϖ)[v]`, `u ↦ 0`. -/
noncomputable def Node.toPolyU : Node O (ϖ ^ n) →ₐ[O] Polynomial (O ⧸ Ideal.span {ϖ}) :=
  Node.lift 0 Polynomial.X (by
    rw [zero_mul, IsScalarTower.algebraMap_apply O (O ⧸ Ideal.span {ϖ}), map_pow,
      Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ),
      zero_pow (by omega), map_zero])

lemma Node.toPolyU_u : Node.toPolyU ϖ hn (Node.u (ϖ ^ n)) = 0 := Node.lift_u ..

lemma Node.toPolyU_v : Node.toPolyU ϖ hn (Node.v (ϖ ^ n)) = Polynomial.X := Node.lift_v ..

lemma Node.idealU_le_ker : Node.idealU (n := n) ϖ ≤ RingHom.ker (Node.toPolyU ϖ hn) := by
  rw [Node.idealU, Ideal.span_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply O (O ⧸ Ideal.span {ϖ}), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), map_zero]
  · simp [Node.toPolyU_u]

/-- `N ⧸ (ϖ, u) ≅ (O ⧸ ϖ)[v]`. -/
noncomputable def Node.quotUEquiv :
    (Node O (ϖ ^ n) ⧸ Node.idealU (n := n) ϖ) ≃+* Polynomial (O ⧸ Ideal.span {ϖ}) := by
  let I := Node.idealU (n := n) ϖ
  let φ : (Node O (ϖ ^ n) ⧸ I) →+* Polynomial (O ⧸ Ideal.span {ϖ}) :=
    Ideal.Quotient.lift I (Node.toPolyU ϖ hn).toRingHom (Node.idealU_le_ker ϖ hn)
  have hϖI : algebraMap O (Node O (ϖ ^ n)) ϖ ∈ I := Ideal.subset_span (by simp)
  let σ : (O ⧸ Ideal.span {ϖ}) →+* (Node O (ϖ ^ n) ⧸ I) :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (algebraMap O _)) (by
      intro o ho
      obtain ⟨o', rfl⟩ := Ideal.mem_span_singleton'.mp ho
      rw [RingHom.comp_apply, map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ hϖI)
  let ψ : Polynomial (O ⧸ Ideal.span {ϖ}) →+* (Node O (ϖ ^ n) ⧸ I) :=
    Polynomial.eval₂RingHom σ (Ideal.Quotient.mk I (Node.v (ϖ ^ n)))
  have hφ : ∀ z, φ (Ideal.Quotient.mk I z) = Node.toPolyU ϖ hn z := fun _ ↦ rfl
  have hψC : ∀ o : O, ψ (Polynomial.C (Ideal.Quotient.mk _ o)) =
      Ideal.Quotient.mk I (algebraMap O _ o) := fun o ↦ by
    simp [ψ, σ]
  have hψX : ψ Polynomial.X = Ideal.Quotient.mk I (Node.v (ϖ ^ n)) := by simp [ψ]
  refine RingEquiv.ofRingHom φ ψ ?_ ?_
  · refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [hψC, hφ, AlgHom.commutes, Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [hψX, hφ, Node.toPolyU_v]
  · refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext
      (fun o ↦ ?_) (fun i ↦ ?_)))
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      change ψ (φ (Ideal.Quotient.mk I (algebraMap O _ o))) = Ideal.Quotient.mk I (algebraMap O _ o)
      rw [hφ, AlgHom.commutes, Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq, hψC]
    · fin_cases i
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
        change ψ (φ (Ideal.Quotient.mk I (Node.u (ϖ ^ n)))) = Ideal.Quotient.mk I (Node.u (ϖ ^ n))
        rw [hφ, Node.toPolyU_u, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
        change ψ (φ (Ideal.Quotient.mk I (Node.v (ϖ ^ n)))) = Ideal.Quotient.mk I (Node.v (ϖ ^ n))
        rw [hφ, Node.toPolyU_v, hψX]

end NodeQuotientU

section EtaleNode

variable {O : Type*} [CommRing O] {ϖ : O} {n : ℕ}

/-- Every element of the node is a constant modulo `(u, v)`. -/
lemma Node.exists_sub_algebraMap_mem_span (z : Node O (ϖ ^ n)) :
    ∃ o : O, z - algebraMap O _ o ∈ Ideal.span {Node.u (ϖ ^ n), Node.v (ϖ ^ n)} := by
  have hz : z ∈ Submodule.span O (Set.range (Node.monomial (ϖ ^ n))) := by
    rw [Node.span_eq_top]; exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    rcases s with i | j
    · rcases i with _ | i
      · exact ⟨1, by simp [Node.monomial]⟩
      · refine ⟨0, ?_⟩
        simp only [Node.monomial, Sum.elim_inl, map_zero, sub_zero, pow_succ]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · refine ⟨0, ?_⟩
      simp only [Node.monomial, Sum.elim_inr, map_zero, sub_zero, pow_succ]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add]; convert add_mem ha hb using 1; ring⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨r * a, ?_⟩
    have := Ideal.mul_mem_left _ (algebraMap O (Node O (ϖ ^ n)) r) ha
    have hs : r • x = algebraMap O (Node O (ϖ ^ n)) r * x := Algebra.smul_def r x
    rw [hs, map_mul]
    convert this using 1; ring

/-- The ideal `(ϖ, v)` of the node. -/
noncomputable def Node.idealV (ϖ : O) : Ideal (Node O (ϖ ^ n)) :=
  Ideal.span {algebraMap O (Node O (ϖ ^ n)) ϖ, Node.v (ϖ ^ n)}

/-- The swap `u ↔ v` as a ring automorphism of the node. -/
noncomputable def Node.swapEquiv (ϖ : O) (n : ℕ) : Node O (ϖ ^ n) ≃+* Node O (ϖ ^ n) :=
  (AlgEquiv.ofAlgHom (Node.swap (ϖ ^ n)) (Node.swap (ϖ ^ n)) (Node.swap_swap _)
    (Node.swap_swap _)).toRingEquiv

lemma Node.idealV_eq_map (ϖ : O) :
    Node.idealV (n := n) ϖ = (Node.idealU (n := n) ϖ).map (Node.swapEquiv ϖ n) := by
  have h1 : Node.swapEquiv ϖ n (algebraMap O _ ϖ) = algebraMap O (Node O (ϖ ^ n)) ϖ :=
    (Node.swap (ϖ ^ n)).commutes ϖ
  have h2 : Node.swapEquiv ϖ n (Node.u (ϖ ^ n)) = Node.v (ϖ ^ n) := Node.swap_u _
  rw [Node.idealV, Node.idealU, Ideal.map_span, Set.image_pair]
  rw [h1, h2]

variable [IsDomain O] [IsDiscreteValuationRing O]

/-- **The local ring of an étale neighbourhood of the singular point of a node is an ordinary
double point** (with residue field that of `O`). -/
theorem isOrdinaryDoublePoint_of_etale (hϖ : Irreducible ϖ) (hn : 1 ≤ n) {C : Type*} [CommRing C]
    [Algebra (Node O (ϖ ^ n)) C] [Algebra.Etale (Node O (ϖ ^ n)) C] [Algebra O C]
    [IsScalarTower O (Node O (ϖ ^ n)) C] (𝔮 : Ideal C) [𝔮.IsPrime]
    (hu : algebraMap _ C (Node.u (ϖ ^ n)) ∈ 𝔮) (hv : algebraMap _ C (Node.v (ϖ ^ n)) ∈ 𝔮)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔮).comp (algebraMap O C))) :
    IsOrdinaryDoublePoint ϖ
      (algebraMap _ (Localization.AtPrime 𝔮) (Node.u (ϖ ^ n)))
      (algebraMap _ (Localization.AtPrime 𝔮) (Node.v (ϖ ^ n)))
      (Ideal.span {algebraMap O (Localization.AtPrime 𝔮) ϖ,
        algebraMap _ (Localization.AtPrime 𝔮) (Node.v (ϖ ^ n))})
      (Ideal.span {algebraMap O (Localization.AtPrime 𝔮) ϖ,
        algebraMap _ (Localization.AtPrime 𝔮) (Node.u (ϖ ^ n))}) := by
  classical
  let N := Node O (ϖ ^ n)
  let E := Localization.AtPrime 𝔮
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  haveI : IsDomain N := Node.isDomain (pow_ne_zero n hϖ0)
  haveI hmaxO : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  -- the two branch quotients of the node are `(O ⧸ ϖ)[X]`
  let eU := Node.quotUEquiv ϖ hn
  haveI : IsDomain (N ⧸ Node.idealU (n := n) ϖ) := eU.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed (N ⧸ Node.idealU (n := n) ϖ) := IsIntegrallyClosed.of_equiv eU.symm
  let eV : (N ⧸ Node.idealV (n := n) ϖ) ≃+* Polynomial (O ⧸ Ideal.span {ϖ}) :=
    (Ideal.quotientEquiv _ _ (Node.swapEquiv ϖ n) (Node.idealV_eq_map ϖ)).symm.trans eU
  haveI : IsDomain (N ⧸ Node.idealV (n := n) ϖ) := eV.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed (N ⧸ Node.idealV (n := n) ϖ) := IsIntegrallyClosed.of_equiv eV.symm
  -- facts in `C`
  set pN := algebraMap O N ϖ with hpN
  set uN := Node.u (ϖ ^ n)
  set vN := Node.v (ϖ ^ n)
  have huvN : uN * vN = pN ^ n := by rw [Node.u_mul_v, map_pow]
  have hϖ𝔮 : algebraMap N C pN ∈ 𝔮 := by
    have : algebraMap N C (uN * vN) ∈ 𝔮 := by rw [map_mul]; exact Ideal.mul_mem_right _ _ hu
    rw [huvN, map_pow] at this
    exact ‹𝔮.IsPrime›.mem_of_pow_mem _ this
  have hO𝔮 : ∀ o : O, algebraMap O C o ∈ 𝔮 → ϖ ∣ o := by
    intro o ho
    by_contra hdiv
    have hunit : IsUnit o := by
      by_contra hnu
      have hm : o ∈ maximalIdeal O := (mem_maximalIdeal o).mpr hnu
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ] at hm
      exact hdiv (Ideal.mem_span_singleton.mp hm)
    exact ‹𝔮.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem _ ho (hunit.map _))
  have hUle : (Node.idealU (n := n) ϖ).map (algebraMap N C) ≤ 𝔮 := by
    rw [Node.idealU, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hϖ𝔮
    · exact hu
  have hVle : (Node.idealV (n := n) ϖ).map (algebraMap N C) ≤ 𝔮 := by
    rw [Node.idealV, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hϖ𝔮
    · exact hv
  have hvU : vN ∉ Node.idealU (n := n) ϖ := by
    intro h
    have := Node.idealU_le_ker ϖ hn h
    rw [RingHom.mem_ker] at this
    simp [vN, Node.toPolyU_v] at this
  have huV : uN ∉ Node.idealV (n := n) ϖ := by
    intro h
    rw [Node.idealV_eq_map] at h
    obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_of_equiv _ _).mp h
    have : x = vN := by
      apply (Node.swapEquiv ϖ n).injective
      rw [hxe]
      exact (Node.swap_v _).symm
    rw [this] at hx
    exact hvU hx
  obtain ⟨hpU, hvU'⟩ := isPrime_map_localization_of_etale (Node.idealU (n := n) ϖ) 𝔮 hUle
  obtain ⟨hpV, huV'⟩ := isPrime_map_localization_of_etale (Node.idealV (n := n) ϖ) 𝔮 hVle
  -- images in `E`
  have hpE : algebraMap N E pN = algebraMap O E ϖ := by
    rw [IsScalarTower.algebraMap_apply N C E, ← IsScalarTower.algebraMap_apply O N C,
      ← IsScalarTower.algebraMap_apply O C E]
  have hUE : Ideal.span {algebraMap O E ϖ, algebraMap N E uN} =
      (Node.idealU (n := n) ϖ).map (algebraMap N E) := by
    rw [Node.idealU, Ideal.map_span, Set.image_pair, ← hpN, hpE]
  have hVE : Ideal.span {algebraMap O E ϖ, algebraMap N E vN} =
      (Node.idealV (n := n) ϖ).map (algebraMap N E) := by
    rw [Node.idealV, Ideal.map_span, Set.image_pair, ← hpN, hpE]
  have huvE : algebraMap N E uN * algebraMap N E vN = algebraMap O E ϖ ^ n := by
    rw [← map_mul, huvN, map_pow, hpE]
  -- the maximal ideal: `C` is unramified over `N`
  have hmax : maximalIdeal E = Ideal.span {algebraMap O E ϖ, algebraMap N E uN,
      algebraMap N E vN} := by
    let 𝔫 := 𝔮.comap (algebraMap N C)
    have h𝔫 : 𝔫 = Ideal.span {pN, uN, vN} := by
      apply le_antisymm
      · intro z hz
        obtain ⟨o, ho⟩ := Node.exists_sub_algebraMap_mem_span z
        have hspan : Ideal.span {uN, vN} ≤ Ideal.span {pN, uN, vN} :=
          Ideal.span_mono (by
            intro w hw
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
            tauto)
        have hsp𝔫 : Ideal.span {uN, vN} ≤ 𝔫 := by
          rw [Ideal.span_le]; intro w hw
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl
          · exact hu
          · exact hv
        have hoN : algebraMap O N o ∈ 𝔫 := by
          have := sub_mem hz (hsp𝔫 ho)
          rwa [sub_sub_cancel] at this
        have hoC : algebraMap O C o ∈ 𝔮 := by
          rw [IsScalarTower.algebraMap_apply O N C]; exact hoN
        obtain ⟨o', rfl⟩ := hO𝔮 o hoC
        have : z = (z - algebraMap O N (ϖ * o')) + algebraMap O N o' * pN := by
          rw [map_mul, hpN]; ring
        rw [this]
        exact add_mem (hspan ho) (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      · rw [Ideal.span_le]
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl
        · exact hϖ𝔮
        · exact hu
        · exact hv
    haveI : Algebra.FormallyUnramified C E := .of_isLocalization 𝔮.primeCompl
    haveI : Algebra.IsUnramifiedAt N 𝔮 := Algebra.FormallyUnramified.comp N C E
    letI := Localization.AtPrime.algebraOfLiesOver 𝔫 𝔮
    obtain ⟨-, hmap⟩ := (Algebra.isUnramifiedAt_iff_map_eq N 𝔫 𝔮).mp inferInstance
    rw [← hmap, h𝔫, Ideal.map_span]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, ← hpE]
    rfl
  have hspan_le : ∀ {I : Ideal E} {a b : E}, a ∈ I → b ∈ I → Ideal.span {a, b} ≤ I :=
    fun ha hb ↦ by
      rw [Ideal.span_le]; intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ha
      · exact hb
  have hred : ∀ (a b : E), a * b = algebraMap O E ϖ ^ n → ∀ z ∈ Ideal.span {algebraMap O E ϖ, b},
      a ^ n * z ∈ Ideal.span {algebraMap O E ϖ} := by
    intro a b hab z hz
    obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hz
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine Ideal.mem_span_singleton'.mpr ⟨α * a ^ n + β * a ^ k * algebraMap O E ϖ ^ k, ?_⟩
    have : a ^ n * b = a ^ k * algebraMap O E ϖ ^ n := by
      rw [hk, pow_succ, mul_assoc, hab, hk]
    rw [hk] at this ⊢
    linear_combination (-β) * this
  refine
    { maximalIdeal_eq := hmax
      residue := fun z ↦ ?_
      mul_mem := ?_
      isPrime₁ := hVE ▸ hpV
      isPrime₂ := hUE ▸ hpU
      mem₁ := Ideal.subset_span (Set.mem_insert _ _)
      mem₂ := Ideal.subset_span (Set.mem_insert _ _)
      notMem₁ := hVE ▸ huV' uN huV
      notMem₂ := hUE ▸ hvU' vN hvU
      reduced₁ := fun z hz ↦ ⟨_, fun h ↦ (hVE ▸ huV' uN huV)
        ((hVE ▸ hpV).mem_of_pow_mem n h), hred _ _ huvE z hz⟩
      reduced₂ := fun z hz ↦ ⟨_, fun h ↦ (hUE ▸ hvU' vN hvU)
        ((hUE ▸ hpU).mem_of_pow_mem n h), hred _ _ (by rw [mul_comm]; exact huvE) z hz⟩
      branches := fun 𝔔 h𝔔 hϖ𝔔 ↦ ?_ }
  · -- residue field
    obtain ⟨⟨c, t⟩, hz⟩ := IsLocalization.surj 𝔮.primeCompl z
    obtain ⟨oc, hoc⟩ := hres (Ideal.Quotient.mk 𝔮 c)
    obtain ⟨ot, hot⟩ := hres (Ideal.Quotient.mk 𝔮 t)
    simp only [RingHom.coe_comp, Function.comp_apply] at hoc hot
    rw [Ideal.Quotient.eq] at hoc hot
    have hϖC : algebraMap O C ϖ ∈ 𝔮 := by
      rw [IsScalarTower.algebraMap_apply O N C]; exact hϖ𝔮
    have hotu : IsUnit ot := by
      by_contra hnu
      have hm : ot ∈ maximalIdeal O := (mem_maximalIdeal ot).mpr hnu
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ] at hm
      obtain ⟨o', rfl⟩ := Ideal.mem_span_singleton'.mp hm
      have h1 : algebraMap O C (o' * ϖ) ∈ 𝔮 := by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ hϖC
      exact t.2 (by have := add_mem h1 (neg_mem hot); simpa using this)
    refine ⟨oc * ↑hotu.unit⁻¹, ?_⟩
    have htE : IsUnit (algebraMap C E t) := IsLocalization.map_units E t
    have key : (z - algebraMap O E (oc * ↑hotu.unit⁻¹)) * algebraMap C E t ∈ maximalIdeal E := by
      have hdiff : c - algebraMap O C (oc * ↑hotu.unit⁻¹) * t ∈ 𝔮 := by
        have e1 : algebraMap O C (oc * ↑hotu.unit⁻¹) * algebraMap O C ot = algebraMap O C oc := by
          rw [← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]
        have : c - algebraMap O C (oc * ↑hotu.unit⁻¹) * t =
            -(algebraMap O C oc - c) + algebraMap O C (oc * ↑hotu.unit⁻¹) *
              (algebraMap O C ot - t) := by
          linear_combination -e1
        rw [this]
        exact add_mem (neg_mem hoc) (Ideal.mul_mem_left _ _ hot)
      have := Ideal.mem_map_of_mem (algebraMap C E) hdiff
      rw [Localization.AtPrime.map_eq_maximalIdeal] at this
      convert this using 1
      simp only at hz
      rw [map_sub, ← hz, map_mul (algebraMap C E), ← IsScalarTower.algebraMap_apply O C E,
        map_mul]
      ring
    have := Ideal.mul_mem_right (↑htE.unit⁻¹) _ key
    rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at this
  · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap O E ϖ ^ k, ?_⟩
    rw [huvE, hk, pow_succ]
  · have : algebraMap N E uN * algebraMap N E vN ∈ 𝔔 := by
      rw [huvE]; exact Ideal.pow_mem_of_mem _ hϖ𝔔 _ (by omega)
    rcases h𝔔.mem_or_mem this with h | h
    · exact Or.inr (hspan_le hϖ𝔔 h)
    · exact Or.inl (hspan_le hϖ𝔔 h)

end EtaleNode

end SemistableReduction
