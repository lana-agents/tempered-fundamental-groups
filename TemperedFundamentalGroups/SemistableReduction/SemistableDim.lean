/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LocalModel
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Semistable algebras have special fibres of dimension at most one

Let `O` be a discrete valuation ring with uniformizer `ϖ` and `A` an `O`-algebra which is
semistable at a prime `𝔭₀` (étale-locally a node `O[u,v]/(uv - ϖⁿ)` or the affine line `O[X]`).
Then there is no chain `𝔭₂ < 𝔭₁ < 𝔭₀` of primes containing `ϖ`
(`SemistableReduction.IsSemistableAt.not_chain`).

* The local models: `dim M/(ϖ) ≤ 1` for `M = O[X]` and `M = Node O (ϖ ^ n)`
  (`ringKrullDim_polynomial_quotient_le`, `ringKrullDim_node_quotient_le`).
* The transfer along a common étale neighbourhood `A → C ← M`: going down for the flat map
  `A → C` lifts the chain to `C`; incomparability for the quasi-finite map `M → C` keeps it
  strict on `M`.
-/

universe u

open Polynomial nonZeroDivisors

namespace SemistableReduction

/-- Three strictly increasing elements give Krull dimension at least two. -/
lemma two_le_krullDim {α : Type*} [Preorder α] {a b c : α} (h₁ : a < b) (h₂ : b < c) :
    (2 : WithBot ℕ∞) ≤ Order.krullDim α :=
  Order.LTSeries.length_le_krullDim
    ((((RelSeries.singleton _ a : LTSeries α).snoc b h₁).snoc c h₂ : LTSeries α))

/-- **No chain of length two in a ring of dimension one modulo `m`.** -/
lemma not_chain_of_ringKrullDim_quotient_le {M : Type*} [CommRing M] (m : M)
    (hM : ringKrullDim (M ⧸ Ideal.span {m}) ≤ 1) {𝔫₀ 𝔫₁ 𝔫₂ : Ideal M} [𝔫₀.IsPrime]
    [𝔫₁.IsPrime] [𝔫₂.IsPrime] (h₁ : 𝔫₁ < 𝔫₀) (h₂ : 𝔫₂ < 𝔫₁) (hm : m ∈ 𝔫₂) : False := by
  rw [ringKrullDim_quotient] at hM
  have hz : ∀ (𝔫 : Ideal M) [𝔫.IsPrime], 𝔫₂ ≤ 𝔫 →
      (⟨𝔫, inferInstance⟩ : PrimeSpectrum M) ∈ PrimeSpectrum.zeroLocus (Ideal.span {m}) :=
    fun 𝔫 _ h ↦ by
      simpa [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] using h hm
  have := two_le_krullDim
    (α := PrimeSpectrum.zeroLocus (R := M) (Ideal.span {m}))
    (a := ⟨_, hz 𝔫₂ le_rfl⟩) (b := ⟨_, hz 𝔫₁ h₂.le⟩) (c := ⟨_, hz 𝔫₀ (h₂.le.trans h₁.le)⟩)
    (show 𝔫₂ < 𝔫₁ from h₂) (show 𝔫₁ < 𝔫₀ from h₁)
  have h21 := this.trans hM
  exact absurd h21 (by decide)

/-- Cancel `+ 1` in `WithBot ℕ∞`. -/
lemma le_of_add_one_le_add_one {x : WithBot ℕ∞} {k : ℕ} (h : x + 1 ≤ (k : WithBot ℕ∞) + 1) :
    x ≤ k := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd h (by norm_cast)
    | coe m =>
      have : m + 1 ≤ k + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : m ≤ k)

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

/-- `dim O[X]/(ϖ) ≤ 1`. -/
lemma ringKrullDim_polynomial_quotient_le (hϖ : ϖ ≠ 0) :
    ringKrullDim (O[X] ⧸ Ideal.span {algebraMap O O[X] ϖ}) ≤ 1 := by
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (r := algebraMap O O[X] ϖ) (mem_nonZeroDivisors_of_ne_zero (by simpa using hϖ))
  rw [Polynomial.ringKrullDim_of_isNoetherianRing,
    IsDiscreteValuationRing.ringKrullDim_eq_one (R := O)] at h
  exact le_of_add_one_le_add_one (k := 1) (h.trans_eq (by norm_num))

/-- `dim O[u,v]/(ϖ) ≤ 2`. -/
private lemma ringKrullDim_mv_quotient_le (hϖ : ϖ ≠ 0) :
    ringKrullDim (MvPolynomial (Fin 2) O ⧸ Ideal.span {MvPolynomial.C ϖ}) ≤ 2 := by
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (r := (MvPolynomial.C ϖ : MvPolynomial (Fin 2) O))
    (mem_nonZeroDivisors_of_ne_zero (by simpa using hϖ))
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsDiscreteValuationRing.ringKrullDim_eq_one (R := O)] at h
  exact le_of_add_one_le_add_one (k := 2) (h.trans_eq (by simp; norm_num))

/-- `O[u,v]/(ϖ)` is a domain. -/
private lemma isDomain_quotient_C (hϖ : Irreducible ϖ) :
    IsDomain (MvPolynomial (Fin 2) O ⧸
      Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin 2) O)}) := by
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  have e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin 2) (Ideal.span {ϖ})
  rw [Ideal.map_span, Set.image_singleton] at e
  exact MulEquiv.isDomain _ e.symm.toMulEquiv

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The node equation is nonzero modulo `ϖ`. -/
private lemma node_eq_notMem (hϖ : Irreducible ϖ) (n : ℕ) :
    (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (ϖ ^ n) : MvPolynomial (Fin 2) O) ∉
      Ideal.span {MvPolynomial.C ϖ} := by
  intro h
  have h' : (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (ϖ ^ n) :
      MvPolynomial (Fin 2) O) ∈ (Ideal.span {ϖ}).map MvPolynomial.C := by
    rwa [Ideal.map_span, Set.image_singleton]
  rw [MvPolynomial.mem_map_C_iff] at h'
  have := h' (Finsupp.single 0 1 + Finsupp.single 1 1)
  have hc : (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (ϖ ^ n) :
      MvPolynomial (Fin 2) O).coeff (Finsupp.single 0 1 + Finsupp.single 1 1) = 1 := by
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, MvPolynomial.X, MvPolynomial.X,
      MvPolynomial.monomial_mul, MvPolynomial.coeff_monomial, if_pos rfl, if_neg]
    · simp
    · intro h0
      have := congrArg (fun f ↦ f 0) h0
      simp at this
  rw [hc, Ideal.mem_span_singleton] at this
  exact hϖ.not_isUnit (isUnit_of_dvd_one this)

/-- `dim (O[u,v]/(uv - ϖⁿ))/(ϖ) ≤ 1`. -/
lemma ringKrullDim_node_quotient_le (hϖ : Irreducible ϖ) (n : ℕ) :
    ringKrullDim (Node O (ϖ ^ n) ⧸ Ideal.span {algebraMap O (Node O (ϖ ^ n)) ϖ}) ≤ 1 := by
  set I := Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin 2) O)}
  set h : MvPolynomial (Fin 2) O := MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (ϖ ^ n)
  haveI := isDomain_quotient_C hϖ
  set h' : MvPolynomial (Fin 2) O ⧸ I := Ideal.Quotient.mk I h
  have hh' : h' ∈ (MvPolynomial (Fin 2) O ⧸ I)⁰ :=
    mem_nonZeroDivisors_of_ne_zero
      (fun e ↦ node_eq_notMem hϖ n (Ideal.Quotient.eq_zero_iff_mem.1 e))
  -- the surjection `(O[u,v]/(ϖ))/(h) → Node/(ϖ)`
  let q₀ : MvPolynomial (Fin 2) O →+* Node O (ϖ ^ n) ⧸
      Ideal.span {algebraMap O (Node O (ϖ ^ n)) ϖ} :=
    (Ideal.Quotient.mk _).comp (Ideal.Quotient.mk _)
  have hq₀ : Function.Surjective q₀ :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hI : I ≤ RingHom.ker q₀ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  let q₁ := Ideal.Quotient.lift I q₀ hI
  have hq₁ : Function.Surjective q₁ := Ideal.Quotient.lift_surjective_of_surjective I hI hq₀
  have hh : Ideal.span {h'} ≤ RingHom.ker q₁ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change q₀ h = 0
    simp only [q₀, RingHom.comp_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
  let q₂ := Ideal.Quotient.lift (Ideal.span {h'}) q₁ hh
  have hq₂ : Function.Surjective q₂ :=
    Ideal.Quotient.lift_surjective_of_surjective _ hh hq₁
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hh'
  exact (ringKrullDim_le_of_surjective q₂ hq₂).trans (le_of_add_one_le_add_one (k := 1)
    (h1.trans ((ringKrullDim_mv_quotient_le hϖ.ne_zero).trans_eq (by norm_num))))

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Going down along an étale map**: a chain `𝔭₂ < 𝔭₁ < 𝔭₀` below `g⁻¹ 𝔮 = 𝔭₀` lifts to a
chain `𝔮₂ < 𝔮₁ < 𝔮`. -/
lemma exists_chain_of_etale {A C : Type*} [CommRing A] [CommRing C] {g : A →+* C} (hg : g.Etale)
    {𝔮 : Ideal C} [𝔮.IsPrime] {𝔭₀ 𝔭₁ 𝔭₂ : Ideal A} [𝔭₀.IsPrime] [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (h𝔮 : 𝔮.comap g = 𝔭₀) (h₁ : 𝔭₁ < 𝔭₀) (h₂ : 𝔭₂ < 𝔭₁) :
    ∃ (𝔮₁ 𝔮₂ : Ideal C), 𝔮₁.IsPrime ∧ 𝔮₂.IsPrime ∧ 𝔮₁ < 𝔮 ∧ 𝔮₂ < 𝔮₁ ∧ 𝔮₁.comap g = 𝔭₁ ∧
      𝔮₂.comap g = 𝔭₂ := by
  letI : Algebra A C := g.toAlgebra
  haveI : Algebra.Etale A C := RingHom.etale_algebraMap.1 hg
  haveI : 𝔮.LiesOver 𝔭₀ := ⟨h𝔮.symm⟩
  obtain ⟨𝔮₁, h𝔮₁, _, _⟩ := Ideal.exists_ideal_lt_liesOver_of_lt 𝔮 h₁
  obtain ⟨𝔮₂, h𝔮₂, _, _⟩ := Ideal.exists_ideal_lt_liesOver_of_lt 𝔮₁ h₂
  exact ⟨𝔮₁, 𝔮₂, inferInstance, inferInstance, h𝔮₁, h𝔮₂, (Ideal.LiesOver.over).symm,
    (Ideal.LiesOver.over).symm⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Incomparability along an étale map**: comaps of a strict inclusion of primes stay strict. -/
lemma comap_lt_comap_of_etale {M C : Type*} [CommRing M] [CommRing C] {f : M →+* C}
    (hf : f.Etale) {𝔮 𝔮' : Ideal C} [𝔮.IsPrime] [𝔮'.IsPrime] (h : 𝔮 < 𝔮') :
    𝔮.comap f < 𝔮'.comap f := by
  letI : Algebra M C := f.toAlgebra
  haveI : Algebra.Etale M C := RingHom.etale_algebraMap.1 hf
  refine lt_of_le_of_ne (Ideal.comap_mono h.le) fun e ↦ h.ne ?_
  exact Algebra.QuasiFinite.eq_of_le_of_under_eq 𝔮 𝔮' h.le e

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Chains transfer along étale neighbourhoods**: if `A` is étale-locally `M` at `𝔭₀` and
`dim M/(ϖ) ≤ 1`, there is no chain `𝔭₂ < 𝔭₁ < 𝔭₀` of primes containing `ϖ`. -/
theorem IsEtaleLocallyAt.not_chain {M : Type u} [CommRing M] [Algebra O M]
    (hM : ringKrullDim (M ⧸ Ideal.span {algebraMap O M ϖ}) ≤ 1) {A : Type u} [CommRing A]
    [Algebra O A] {𝔭₀ 𝔭₁ 𝔭₂ : Ideal A} [𝔭₀.IsPrime] [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (h : IsEtaleLocallyAt O M 𝔭₀) (h₁ : 𝔭₁ < 𝔭₀) (h₂ : 𝔭₂ < 𝔭₁)
    (hm : algebraMap O A ϖ ∈ 𝔭₂) : False := by
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hg𝔮, hfg⟩ := h
  obtain ⟨𝔮₁, 𝔮₂, _, _, h𝔮₁, h𝔮₂, -, hc₂⟩ := exists_chain_of_etale hg hg𝔮 h₁ h₂
  refine not_chain_of_ringKrullDim_quotient_le (algebraMap O M ϖ) hM
    (comap_lt_comap_of_etale hf h𝔮₁) (comap_lt_comap_of_etale hf h𝔮₂) ?_
  rw [Ideal.mem_comap, ← RingHom.comp_apply, hfg, RingHom.comp_apply, ← Ideal.mem_comap, hc₂]
  exact hm

/-- **Semistable algebras have one-dimensional special fibres**: if `A` is semistable at `𝔭₀`,
there is no chain `𝔭₂ < 𝔭₁ < 𝔭₀` of primes containing `ϖ`. -/
theorem IsSemistableAt.not_chain (hϖ : Irreducible ϖ) {A : Type u} [CommRing A] [Algebra O A]
    {𝔭₀ 𝔭₁ 𝔭₂ : Ideal A} [𝔭₀.IsPrime] [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (h : IsSemistableAt ϖ 𝔭₀) (h₁ : 𝔭₁ < 𝔭₀) (h₂ : 𝔭₂ < 𝔭₁)
    (hm : algebraMap O A ϖ ∈ 𝔭₂) : False := by
  rcases h with ⟨n, h⟩ | h
  · exact h.not_chain (ringKrullDim_node_quotient_le hϖ n) h₁ h₂ hm
  · exact h.not_chain (ringKrullDim_polynomial_quotient_le hϖ.ne_zero) h₁ h₂ hm

end SemistableReduction
