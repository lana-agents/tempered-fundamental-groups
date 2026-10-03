/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeGerm
import TemperedFundamentalGroups.SemistableReduction.SplitChart
import TemperedFundamentalGroups.SemistableReduction.TrdegOne
import TemperedFundamentalGroups.SemistableReduction.MonomialUnique

/-!
# Node germs inside the function field (W8′, XL1)

Blueprint §9.7 (XL1). Let `A` be a domain of finite type over a DVR `O ⊆ K`, embedded into a
function field `L ⊇ K` of a curve (`ι : A → L`, with fraction field `L`), `𝔭` a split node point
of `A` (`IsSplitNodeAt`) of thickness `n ≥ 1` on two distinct components (two distinct minimal
primes over `ϖ` inside `𝔭`). Then the image `P ⊆ L` of the local ring `A_𝔭` is a node germ
`NodeGerm O ϖ P u v n` for exact coordinates `u v = ϖ ^ n` (`exists_nodeGerm_of_split`): a local
ring with `ϖ, u, v` in its maximal ideal, `u` transcendental over `K`, flat over the node
`O[u, v] ⧸ (u v - ϖ ^ n)` via `(u, v)`; the coordinates are fractions `a / s` of elements of `A`
with a common denominator `s ∉ 𝔭`.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [IsDiscreteValuationRing O]

/-- **Node germs at split nodes without loops** (XL1). -/
theorem exists_nodeGerm_of_split {ϖ : O} (hϖ : Irreducible ϖ) {n : ℕ} (hn : 1 ≤ n)
    {A : Type u} [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A]
    (ι : A →+* L) (hι : Function.Injective ι)
    (hιO : ∀ o : O, ι (algebraMap O A o) = algebraMap K L (o : K))
    (hfrac : ∀ f : L, ∃ a b : A, ι b ≠ 0 ∧ f = ι a / ι b)
    {x : L} (hx : Transcendental K x) (halg : Algebra.IsAlgebraic (Algebra.adjoin K {x}) L)
    (𝔭 : Ideal A) [𝔭.IsPrime] (hsplit : IsSplitNodeAt ϖ n 𝔭)
    (P₁ P₂ : Ideal A) [P₁.IsPrime] [P₂.IsPrime]
    (hP₁ : algebraMap O A ϖ ∈ P₁) (hP₂ : algebraMap O A ϖ ∈ P₂) (hle₁ : P₁ ≤ 𝔭) (hle₂ : P₂ ≤ 𝔭)
    (hmin₁ : ∀ Q : Ideal A, Q.IsPrime → algebraMap O A ϖ ∈ Q → Q ≤ P₁ → Q = P₁)
    (hmin₂ : ∀ Q : Ideal A, Q.IsPrime → algebraMap O A ϖ ∈ Q → Q ≤ P₂ → Q = P₂)
    (hne : P₁ ≠ P₂) :
    ∃ (P : Subring L) (u v : L) (h : NodeGerm O ϖ P u v n),
      (P : Set L) = {f | ∃ a b : A, b ∉ 𝔭 ∧ f = ι a / ι b} ∧
      (∃ _ : IsLocalRing P, (⟨_, h.algebraMap_mem ϖ⟩ : P) ∈ maximalIdeal P ∧
        (⟨u, h.u_mem⟩ : P) ∈ maximalIdeal P ∧ (⟨v, h.v_mem⟩ : P) ∈ maximalIdeal P) ∧
      Transcendental K u ∧
      (∃ φ : Node O (ϖ ^ n) →+* P, (letI := φ.toAlgebra; Module.Flat (Node O (ϖ ^ n)) P) ∧
        (∀ b, (φ b : L) ∈
          Subring.closure (Set.range (fun o : O ↦ algebraMap K L (o : K)) ∪ {u, v})) ∧
        (∀ o : O, (φ (algebraMap O _ o) : L) = algebraMap K L (o : K)) ∧
        (φ (Node.u _) : L) = u ∧ (φ (Node.v _) : L) = v) ∧
      (∃ a b s : A, s ∉ 𝔭 ∧ u = ι a / ι s ∧ v = ι b / ι s) := by
  classical
  -- the étale chart
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hc, hO, hu, hv, hres⟩ := hsplit
  letI : Algebra A C := g.toAlgebra
  letI : Algebra (Node O (ϖ ^ n)) C := f.toAlgebra
  letI : Algebra O C := (g.comp (algebraMap O A)).toAlgebra
  haveI : Algebra.Etale A C := RingHom.etale_algebraMap.mp hg
  haveI : Algebra.Etale (Node O (ϖ ^ n)) C := RingHom.etale_algebraMap.mp hf
  haveI : IsScalarTower O A C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower O (Node O (ϖ ^ n)) C := by
    have := @IsScalarTower.of_algebraMap_eq O (Node O (ϖ ^ n)) C _ _ _ _ _ _ fun o ↦ by
      change g (algebraMap O A o) = f (algebraMap O _ o)
      rw [← RingHom.comp_apply, ← hO, RingHom.comp_apply]
    exact this
  haveI : FaithfulSMul O A := (faithfulSMul_iff_algebraMap_injective O A).mpr fun o o' h ↦ by
    have := congrArg ι h
    rw [hιO, hιO] at this
    exact Subtype.ext ((algebraMap K L).injective this)
  haveI := h𝔮
  -- the local ring and its two branches
  let D := Localization.AtPrime 𝔭
  have hdisj : ∀ Q : Ideal A, Q ≤ 𝔭 → Disjoint (𝔭.primeCompl : Set A) Q := fun Q hQ ↦ by
    rw [Set.disjoint_left]; intro z hz hzQ; exact hz (hQ hzQ)
  have hQprime : ∀ Q : Ideal A, Q.IsPrime → Q ≤ 𝔭 → (Q.map (algebraMap A D)).IsPrime :=
    fun Q hQ hle ↦ IsLocalization.isPrime_of_isPrime_disjoint _ D Q hQ (hdisj Q hle)
  have hQcomap : ∀ Q : Ideal A, Q.IsPrime → Q ≤ 𝔭 →
      (Q.map (algebraMap A D)).comap (algebraMap A D) = Q :=
    fun Q hQ hle ↦ IsLocalization.under_map_of_isPrime_disjoint _ D hQ (hdisj Q hle)
  have hϖD : ∀ Q : Ideal A, algebraMap O A ϖ ∈ Q → algebraMap O D ϖ ∈ Q.map (algebraMap A D) :=
    fun Q hQ ↦ by
      rw [IsScalarTower.algebraMap_apply O A D]; exact Ideal.mem_map_of_mem _ hQ
  have hminD : ∀ Q : Ideal A, Q.IsPrime → Q ≤ 𝔭 →
      (∀ Q' : Ideal A, Q'.IsPrime → algebraMap O A ϖ ∈ Q' → Q' ≤ Q → Q' = Q) →
      ∀ Q' : Ideal D, Q'.IsPrime → algebraMap O D ϖ ∈ Q' → Q' ≤ Q.map (algebraMap A D) →
        Q' = Q.map (algebraMap A D) := by
    intro Q hQ hle hmin Q' hQ' hϖQ' hQ'le
    have h1 : Q'.comap (algebraMap A D) = Q := by
      refine hmin _ (Ideal.comap_isPrime _ _) ?_ ?_
      · rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hϖQ'
      · rw [← hQcomap Q hQ hle]; exact Ideal.comap_mono hQ'le
    rw [← h1, IsLocalization.map_under 𝔭.primeCompl D]
  haveI := hQprime P₁ inferInstance hle₁
  haveI := hQprime P₂ inferInstance hle₂
  have hneD : P₁.map (algebraMap A D) ≠ P₂.map (algebraMap A D) := fun h ↦ hne (by
    rw [← hQcomap P₁ inferInstance hle₁, h, hQcomap P₂ inferInstance hle₂])
  obtain ⟨u, v, 𝔔₁, 𝔔₂, huv, H, -⟩ := exists_exact_node_of_split hϖ hn 𝔭 𝔮 hc hu hv hres
    _ _ (hϖD P₁ hP₁) (hϖD P₂ hP₂) (hminD P₁ inferInstance hle₁ hmin₁)
    (hminD P₂ inferInstance hle₂ hmin₂) hneD
  haveI := H.isPrime₁
  haveI := H.isPrime₂
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  -- the embedding of the local ring into `L`
  have hιs : ∀ s ∈ 𝔭.primeCompl, ι s ≠ 0 := fun s hs h0 ↦
    hs (by rw [show s = 0 from hι (by rw [h0, map_zero])]; exact zero_mem 𝔭)
  let ιD : D →+* L := IsLocalization.lift (M := 𝔭.primeCompl) (S := D)
    (fun s : 𝔭.primeCompl ↦ isUnit_iff_ne_zero.mpr (hιs s.1 s.2))
  have hιD : ∀ a, ιD (algebraMap A D a) = ι a := IsLocalization.lift_eq _
  have hιDmk : ∀ (a : A) (s : 𝔭.primeCompl), ιD (IsLocalization.mk' D a s) = ι a / ι s := by
    intro a s
    rw [eq_div_iff (hιs s.1 s.2), ← hιD, ← map_mul, IsLocalization.mk'_spec, hιD]
  have hιDinj : Function.Injective ιD := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
    rw [hιDmk, div_eq_zero_iff, or_iff_left (hιs s.1 s.2), ← map_zero ι] at hz
    rw [hι hz]; exact IsLocalization.mk'_zero _
  have hιDO : ∀ o : O, ιD (algebraMap O D o) = algebraMap K L (o : K) := fun o ↦ by
    rw [IsScalarTower.algebraMap_apply O A D, hιD, hιO]
  let P : Subring L := ιD.range
  have hmemP : ∀ d, ιD d ∈ P := fun d ↦ ⟨d, rfl⟩
  have hϖ0 : algebraMap O D ϖ ≠ 0 := fun h ↦ by
    have := congrArg ιD h
    rw [hιDO, map_zero, map_eq_zero_iff _ (algebraMap K L).injective] at this
    exact hϖ.ne_zero (Subtype.ext this)
  -- `u` is transcendental
  have htr : Transcendental K (ιD u) := by
    rintro ⟨q, hq0, hq⟩
    letI : Algebra O L := ((algebraMap K L).comp (algebraMap O K)).toAlgebra
    haveI : IsScalarTower O K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let q' := IsLocalization.integerNormalization (nonZeroDivisors O) q
    have hq' : aeval (ιD u) q' = 0 := IsLocalization.integerNormalization_aeval_eq_zero _ q hq
    have hq'0 : q' ≠ 0 := by
      rwa [ne_eq, IsLocalization.integerNormalization_eq_zero_iff le_rfl]
    let ιDA : D →ₐ[O] L := { ιD with commutes' := hιDO }
    have : aeval u q' = 0 := by
      apply hιDinj
      rw [map_zero]
      change ιDA (aeval u q') = 0
      rw [← Polynomial.aeval_algHom_apply]
      exact hq'
    exact hq'0 (H.transcendental_of_irreducible hϖ hϖ0 H.isDiscreteValuationRing_quotient.2 this)
  have halgu := isAlgebraic_adjoin_of_transcendental hx halg htr
  -- the node germ
  have hmax3 : ∀ z ∈ maximalIdeal D, ∃ a b c : D,
      z = algebraMap O D ϖ * a + u * b + v * c := by
    intro z hz
    rw [H.maximalIdeal_eq, Ideal.mem_span_insert] at hz
    obtain ⟨a, w, hw, rfl⟩ := hz
    obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.mp hw
    exact ⟨a, b, c, by ring⟩
  have hG : NodeGerm O ϖ P (ιD u) (ιD v) n :=
    { algebraMap_mem := fun o ↦ hιDO o ▸ hmemP _
      u_mem := hmemP u
      v_mem := hmemP v
      mul_eq := by rw [← map_mul, huv, map_pow, hιDO]
      gen := by
        rintro _ ⟨d, rfl⟩
        obtain ⟨o, ho⟩ := H.residue d
        obtain ⟨a, b, c, habc⟩ := hmax3 _ ho
        refine ⟨o, ιD a, hmemP a, ιD b, hmemP b, ιD c, hmemP c, ?_⟩
        have hd : d = algebraMap O D o + (algebraMap O D ϖ * a + u * b + v * c) := by
          rw [← habc]; ring
        rw [hd]
        simp only [map_add, map_mul, hιDO]
        ring
      frac := by
        intro f
        obtain ⟨a, b, hb, rfl⟩ := hfrac f
        exact ⟨ι a, hιD a ▸ hmemP _, ι b, hιD b ▸ hmemP _, hb, rfl⟩
      alg := fun f _ hf ↦ exists_relation_of_transcendental halgu hf }
  -- `P ≅ D`
  let e : D ≃+* P := RingEquiv.ofBijective ιD.rangeRestrict
    ⟨fun a b h ↦ hιDinj (congrArg Subtype.val h), ιD.rangeRestrict_surjective⟩
  have he : ∀ d, (e d : L) = ιD d := fun _ ↦ rfl
  haveI hPloc : IsLocalRing P := IsLocalRing.of_surjective' e.toRingHom e.surjective
  have hmaxP : ∀ d ∈ maximalIdeal D, ∀ hd : ιD d ∈ P, (⟨ιD d, hd⟩ : P) ∈ maximalIdeal P := by
    intro d hd hd'
    rw [mem_maximalIdeal, mem_nonunits_iff] at hd ⊢
    have : (⟨ιD d, hd'⟩ : P) = e d := Subtype.ext rfl
    rw [this, isUnit_map_iff]
    exact hd
  have hspan : ∀ z ∈ ({algebraMap O D ϖ, u, v} : Set D), z ∈ maximalIdeal D := fun z hz ↦ by
    rw [H.maximalIdeal_eq]; exact Ideal.subset_span hz
  -- flatness over the node
  have huv' : u * v = algebraMap O D (ϖ ^ n) := by rw [map_pow]; exact huv
  let lamD : Node O (ϖ ^ n) →ₐ[O] D := Node.lift u v huv'
  let φ : Node O (ϖ ^ n) →+* P := e.toRingHom.comp lamD.toRingHom
  have hφ : ∀ b, (φ b : L) = ιD (lamD b) := fun _ ↦ rfl
  have hflat : letI := φ.toAlgebra; Module.Flat (Node O (ϖ ^ n)) P := by
    letI : Algebra (Node O (ϖ ^ n)) D := lamD.toRingHom.toAlgebra
    letI : Algebra (Node O (ϖ ^ n)) P := φ.toAlgebra
    haveI : Module.Flat (Node O (ϖ ^ n)) D := flat_node_of_isOrdinaryDoublePoint hϖ 𝔭 huv' H
    exact Module.Flat.of_linearEquiv
      (AlgEquiv.ofRingEquiv (f := e) (fun _ ↦ rfl)).toLinearEquiv.symm
  refine ⟨P, ιD u, ιD v, hG, ?_, ⟨hPloc, ?_, ?_, ?_⟩, htr, ⟨φ, hflat, ?_, ?_, ?_, ?_⟩, ?_⟩
  · ext f
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl d
      exact ⟨a, s, s.2, hιDmk a s⟩
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨IsLocalization.mk' D a (⟨b, hb⟩ : 𝔭.primeCompl), hιDmk a ⟨b, hb⟩⟩
  · have : algebraMap K L (ϖ : K) = ιD (algebraMap O D ϖ) := (hιDO ϖ).symm
    simp only [this]
    exact hmaxP _ (hspan _ (by simp)) _
  · exact hmaxP _ (hspan _ (by simp)) _
  · exact hmaxP _ (hspan _ (by simp)) _
  · intro b
    have hb : b ∈ Algebra.adjoin O {Node.u (ϖ ^ n), Node.v (ϖ ^ n)} := by
      rw [Node.adjoin_u_v]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · rw [hφ, Node.lift_u]
        exact Subring.subset_closure (Or.inr (by simp))
      · rw [hφ]
        change ιD (Node.lift u v huv' (Node.v _)) ∈ _
        rw [Node.lift_v]
        exact Subring.subset_closure (Or.inr (by simp))
    | algebraMap o =>
      rw [hφ, AlgHom.commutes, hιDO]
      exact Subring.subset_closure (Or.inl ⟨o, rfl⟩)
    | add _ _ _ _ h₁ h₂ => rw [map_add, Subring.coe_add]; exact add_mem h₁ h₂
    | mul _ _ _ _ h₁ h₂ => rw [map_mul, Subring.coe_mul]; exact mul_mem h₁ h₂
  · intro o
    rw [hφ, AlgHom.commutes, hιDO]
  · rw [hφ]; change ιD (Node.lift u v huv' (Node.u _)) = _; rw [Node.lift_u]
  · rw [hφ]; change ιD (Node.lift u v huv' (Node.v _)) = _; rw [Node.lift_v]
  · obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl u
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl v
    have hs := hιs s.1 s.2
    have ht := hιs t.1 t.2
    refine ⟨a * t, b * s, s * t, (s * t).2, ?_, ?_⟩
    · rw [hιDmk, map_mul, map_mul, mul_div_mul_right _ _ ht]
    · rw [hιDmk, map_mul, map_mul, mul_comm (ι s.1), mul_div_mul_right _ _ hs]

end SemistableReduction
