/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization
import TemperedFundamentalGroups.SemistableReduction.Inertia

/-!
# Galois reduction: quotient charts, conjugate extensions, decomposition groups

Blueprint §9.10, layer L1 (A1–A5). Let `L / F` be a field extension and `A ⊆ F` a subring.

* `mem_normChart_iff`: `x ∈ normChart L A` (the integral closure of `A` in `L`) iff `x` is a root
  of a monic polynomial over `F` with coefficients in `A`.
* **A2 (quotient charts)** `algebraMap_mem_normChart_iff`: for a tower `F ⊆ E ⊆ L`, the chart of
  the normalization in `E` is the preimage of the chart of the normalization in `L`;
  `algEquiv_mem_normChart_iff`: the chart in `L` is stable under `Aut(L / F)`;
  `mem_normChart_iff_forall_algEquiv` (Galois case): its fixed elements are those of `A`, if `A`
  is integrally closed in `F` (`normChart_self_le_of_valuationSubring` for valuation subrings).
* **A1 (transitivity)** `exists_smul_eq`: for `L / F` finite Galois, two valuation subrings of `L`
  with the same restriction to `F` are conjugate under `Gal(L / F)`. Proof: the integral closure
  `D` of `W = W₁ ∩ F` carries the Galois action with invariants `W` (`Algebra.IsInvariant`), the
  centres of `W₁`, `W₂` on `D` are conjugate (Mathlib's
  `Algebra.IsInvariant.exists_smul_of_under_eq`), and a valuation subring over `W` is the
  localization of `D` at its centre (Prüfer, `localAt_normChart_eq`), which depends only on the
  centre (`localAt_congr`).
* **A2 (fibres)** `comap_fixedField_eq_iff`: two valuation subrings of `L` have the same
  restriction to the fixed field of `H` iff they are `H`-conjugate.
* **A3 (decomposition groups)** `valuation_apply_eq`: an automorphism `σ` of finite order with
  `σ • W = W` preserves the valuation of `W` (if `W(σ x) < W(x)`, then `y = σ x / x` lies in the
  maximal ideal together with all `σⁱ y`, but `∏_{i < n} σⁱ y = σⁿ x / x = 1`);
  `decompositionGroup`, `decompositionField`, `valuation_decompositionField_apply` (the
  hypothesis `hσ` of `Inertia` over the decomposition field).
* **A4** `inertia_eq_top`: with algebraically closed residue field the inertia group is
  everything; `isPGroup_of_isAlgClosed`, `isPGroup_decompositionGroup`: with divisible values
  (`exists_pow_eq_of_divisible` moves divisibility up finite extensions) and roots of unity the
  decomposition group is a `p`-group (D2) — the case of a type-4 point of `C(x)`.
* **A5** `exists_kummer_generator`: a Galois step of prime degree `p` with `ζ_p` in the base is
  `K(α)`, `α ^ p ∈ K` (Mathlib's `exists_root_adjoin_eq_top_of_isCyclic`).
-/

open Polynomial
open scoped Pointwise

namespace SemistableReduction

namespace GaloisReduction

/-! ### Charts of normalizations -/

section Chart

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- Integrality over the image of a subring `A ⊆ F`, in terms of polynomials over `F`. -/
theorem mem_normChart_iff (A : Subring F) {x : L} :
    x ∈ normChart L A ↔ ∃ P : F[X], P.Monic ∧ (∀ i, P.coeff i ∈ A) ∧ aeval x P = 0 := by
  set A' := A.map (algebraMap F L)
  change IsIntegral A' x ↔ _
  constructor
  · rintro ⟨q, hq, hqx⟩
    have hlifts : q.map A'.subtype ∈ lifts (algebraMap F L) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      obtain ⟨a, -, ha⟩ := (q.coeff n).2
      exact ⟨a, by rw [coeff_map]; exact ha⟩
    obtain ⟨P, hPmap, -, hP⟩ := lifts_and_natDegree_eq_and_monic hlifts (hq.map _)
    refine ⟨P, hP, fun i ↦ ?_, ?_⟩
    · obtain ⟨a, ha, hfa⟩ := (q.coeff i).2
      have h : algebraMap F L (P.coeff i) = algebraMap F L a := by
        rw [hfa, ← coeff_map, hPmap, coeff_map]
        rfl
      rw [(algebraMap F L).injective h]
      exact ha
    · rw [aeval_def, ← eval_map, hPmap, eval_map]
      exact hqx
  · rintro ⟨P, hP, hPA, hPx⟩
    have hc : (↑(P.map (algebraMap F L)).coeffs : Set L) ⊆ A' := by
      intro c hc
      obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hc
      rw [coeff_map]
      exact ⟨_, hPA n, rfl⟩
    refine ⟨(P.map (algebraMap F L)).toSubring A' hc,
      (monic_toSubring _ _ _).2 (hP.map _), ?_⟩
    rw [← eval_map]
    change eval x (((P.map (algebraMap F L)).toSubring A' hc).map A'.subtype) = 0
    rw [map_toSubring, eval_map, ← aeval_def]
    exact hPx

/-- **A2.** For a tower `F ⊆ E ⊆ L`, the chart of the normalization in `E` is the preimage of
the chart of the normalization in `L`. -/
theorem algebraMap_mem_normChart_iff {E : Type*} [Field E] [Algebra F E] [Algebra E L]
    [IsScalarTower F E L] (A : Subring F) {x : E} :
    algebraMap E L x ∈ normChart L A ↔ x ∈ normChart E A := by
  simp_rw [mem_normChart_iff, aeval_algebraMap_apply, map_eq_zero_iff _
    (algebraMap E L).injective]

/-- **A2.** The chart of the normalization in `L` is stable under `Aut(L / F)`. -/
theorem algEquiv_mem_normChart_iff (σ : L ≃ₐ[F] L) (A : Subring F) {x : L} :
    σ x ∈ normChart L A ↔ x ∈ normChart L A := by
  simp_rw [mem_normChart_iff, aeval_algEquiv, AlgHom.coe_comp, Function.comp_apply,
    AlgEquiv.coe_toAlgHom, map_eq_zero_iff _ σ.injective]

/-- A valuation subring is integrally closed: its normalization in `F` itself is contained in
it. -/
theorem normChart_self_le_of_valuationSubring (W : ValuationSubring F) :
    normChart F W.toSubring ≤ W.toSubring := by
  have hW : W.comap (algebraMap F F) = W := by
    ext x
    rfl
  exact (normChart_le_iff (F' := F) W.toSubring W).2 hW.ge

/-- **A2, Galois case.** If `L / F` is Galois and `A` is integrally closed in `F`, the elements of
the chart of the normalization in `L` fixed by `Gal(L / F)` are the elements of `A`. -/
theorem mem_normChart_iff_forall_algEquiv [FiniteDimensional F L] [IsGalois F L]
    {A : Subring F} (hA : normChart F A ≤ A) {x : L} :
    (x ∈ normChart L A ∧ ∀ σ : L ≃ₐ[F] L, σ x = x) ↔ x ∈ A.map (algebraMap F L) := by
  constructor
  · rintro ⟨hx, hfix⟩
    obtain ⟨a, rfl⟩ := (IsGalois.mem_bot_iff_fixed (F := F) x).2 hfix
    refine ⟨a, hA ?_, rfl⟩
    rwa [← algebraMap_mem_normChart_iff (E := F) (L := L)]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨map_le_normChart A ⟨a, ha, rfl⟩, fun σ ↦ σ.commutes a⟩

end Chart

/-! ### A1: conjugacy of extensions -/

section Transitivity

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- The local ring of a subring at a valuation subring depends only on the valuation-one elements
of the subring. -/
lemma localAt_congr {A : Subring L} {W W' : ValuationSubring L}
    (h : ∀ s ∈ A, W.valuation s = 1 ↔ W'.valuation s = 1) : localAt A W = localAt A W' := by
  ext x
  simp only [mem_localAt]
  constructor
  · rintro ⟨s, hs, hsW, hxs⟩
    exact ⟨s, hs, (h s hs).1 hsW, hxs⟩
  · rintro ⟨s, hs, hsW, hxs⟩
    exact ⟨s, hs, (h s hs).2 hsW, hxs⟩

/-- The valuation of a valuation subring is `< 1` iff the element lies in it and is not a unit
of it. -/
lemma valuation_lt_one_iff_mem (V : ValuationSubring L) (y : L) :
    V.valuation y < 1 ↔ y ∈ V ∧ (y ≠ 0 → y⁻¹ ∉ V) := by
  rw [lt_iff_le_and_ne, V.valuation_le_one_iff, Ne, valuation_eq_one_iff_mem_and_inv_mem]
  tauto

lemma valuation_comap_lt_one_iff (V : ValuationSubring L) (a : F) :
    (V.comap (algebraMap F L)).valuation a < 1 ↔ V.valuation (algebraMap F L a) < 1 := by
  rw [valuation_lt_one_iff_mem, valuation_lt_one_iff_mem, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, map_inv₀, Ne, Ne, map_eq_zero_iff _ (algebraMap F L).injective]

lemma valuation_smul_lt_one_iff (σ : L ≃ₐ[F] L) (V : ValuationSubring L) (y : L) :
    (σ • V).valuation y < 1 ↔ V.valuation (σ⁻¹ y) < 1 := by
  rw [valuation_lt_one_iff_mem, valuation_lt_one_iff_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.smul_def,
    map_inv₀, Ne, Ne, map_eq_zero_iff _ (σ⁻¹).injective]

/-- The Galois action on the chart of the normalization. -/
@[implicit_reducible]
def chartAction (A : Subring F) : MulSemiringAction (L ≃ₐ[F] L) (normChart L A) where
  smul σ x := ⟨σ x, (algEquiv_mem_normChart_iff σ A).2 x.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := Subtype.ext (map_zero _)
  smul_add _ _ _ := Subtype.ext (map_add _ _ _)
  smul_one _ := Subtype.ext (map_one _)
  smul_mul _ _ _ := Subtype.ext (map_mul _ _ _)

/-- The structure map `A → normChart L A`. -/
@[implicit_reducible]
noncomputable def chartAlgebra (A : Subring F) : Algebra A (normChart L A) :=
  (((algebraMap F L).comp A.subtype).codRestrict (normChart L A)
    fun a ↦ map_le_normChart A ⟨a, a.2, rfl⟩).toAlgebra

/-- The centre of a valuation subring `W ⊇ D` on `D`. -/
def centre {D : Subring L} (W : ValuationSubring L) (h : D ≤ W.toSubring) : Ideal D :=
  (IsLocalRing.maximalIdeal W).comap (Subring.inclusion h)

instance {D : Subring L} (W : ValuationSubring L) (h : D ≤ W.toSubring) :
    (centre W h).IsPrime :=
  Ideal.comap_isPrime _ _

lemma mem_centre_iff {D : Subring L} {W : ValuationSubring L} (h : D ≤ W.toSubring) (d : D) :
    d ∈ centre W h ↔ W.valuation d < 1 :=
  ValuationSubring.valuation_lt_one_iff W (Subring.inclusion h d)

variable [FiniteDimensional F L] [IsGalois F L]

/-- **A1.** For `L / F` finite Galois, two valuation subrings of `L` with the same restriction to
`F` are conjugate under `Gal(L / F)`. -/
theorem exists_smul_eq (W₁ W₂ : ValuationSubring L)
    (h : W₁.comap (algebraMap F L) = W₂.comap (algebraMap F L)) :
    ∃ σ : L ≃ₐ[F] L, σ • W₁ = W₂ := by
  classical
  set W := W₁.comap (algebraMap F L)
  set D := normChart L W.toSubring
  have hD₁ : D ≤ W₁.toSubring := (normChart_le_iff _ _).2 le_rfl
  have hD₂ : D ≤ W₂.toSubring := (normChart_le_iff _ _).2 h.le
  letI := chartAction (L := L) W.toSubring
  letI := chartAlgebra (L := L) W.toSubring
  have hcomm : SMulCommClass (L ≃ₐ[F] L) W D := by
    refine ⟨fun σ a d ↦ Subtype.ext ?_⟩
    change σ (algebraMap F L a * d) = algebraMap F L a * σ d
    rw [map_mul, AlgEquiv.commutes]
  have hinv : Algebra.IsInvariant W D (L ≃ₐ[F] L) := by
    refine ⟨fun d hd ↦ ?_⟩
    have hfix : ∀ σ : L ≃ₐ[F] L, σ d = d := fun σ ↦ congrArg Subtype.val (hd σ)
    obtain ⟨a, ha, had⟩ := (mem_normChart_iff_forall_algEquiv
      (normChart_self_le_of_valuationSubring W)).1 ⟨d.2, hfix⟩
    exact ⟨⟨a, ha⟩, Subtype.ext had⟩
  have hunder : (centre W₁ hD₁).under W = (centre W₂ hD₂).under W := by
    ext ⟨a, ha⟩
    simp only [Ideal.mem_comap, mem_centre_iff]
    change W₁.valuation (algebraMap F L a) < 1 ↔ W₂.valuation (algebraMap F L a) < 1
    rw [← valuation_comap_lt_one_iff, ← valuation_comap_lt_one_iff]
    exact h ▸ Iff.rfl
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq W D (L ≃ₐ[F] L)
    (centre W₁ hD₁) (centre W₂ hD₂) hunder
  refine ⟨σ, ?_⟩
  have hV : (σ • W₁).comap (algebraMap F L) = W := by
    ext a
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, AlgEquiv.commutes, ← ValuationSubring.mem_comap]
  have hDV : D ≤ (σ • W₁).toSubring := (normChart_le_iff _ _).2 hV.ge
  have key : ∀ s ∈ D, (σ • W₁).valuation s = 1 ↔ W₂.valuation s = 1 := by
    intro s hs
    have h₁ : (σ • W₁).valuation s ≤ 1 := ((σ • W₁).valuation_le_one_iff s).2 (hDV hs)
    have h₂ : W₂.valuation s ≤ 1 := (W₂.valuation_le_one_iff s).2 (hD₂ hs)
    rw [← not_iff_not, ← Ne, ← Ne, h₁.lt_iff_ne.symm, h₂.lt_iff_ne.symm,
      valuation_smul_lt_one_iff, ← mem_centre_iff hD₂ ⟨s, hs⟩, hσ,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centre_iff]
    rfl
  have e₁ := localAt_normChart_eq (F' := L) W (σ • W₁) hV.ge
  have e₂ := localAt_normChart_eq (F' := L) W W₂ h.le
  apply ValuationSubring.toSubring_injective
  rw [← e₁, ← e₂]
  exact localAt_congr key

/-- **A2 (fibres of the quotient).** Two valuation subrings of `L` restrict to the same valuation
subring of the fixed field of `H ≤ Gal(L / F)` iff they are conjugate under `H`. -/
theorem comap_fixedField_eq_iff (H : Subgroup (L ≃ₐ[F] L)) (W₁ W₂ : ValuationSubring L) :
    W₁.comap (algebraMap (IntermediateField.fixedField H) L) =
        W₂.comap (algebraMap (IntermediateField.fixedField H) L) ↔
      ∃ σ ∈ H, σ • W₁ = W₂ := by
  set E := IntermediateField.fixedField H
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := exists_smul_eq (F := E) W₁ W₂ h
    refine ⟨τ.restrictScalars F, ?_, ?_⟩
    · rw [← IntermediateField.fixingSubgroup_fixedField H,
        IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact τ.commutes ⟨x, hx⟩
    · rw [← hτ]
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
  · rintro ⟨σ, hσ, rfl⟩
    ext ⟨x, hx⟩
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    change _ ↔ σ⁻¹ x ∈ W₁
    rw [(IntermediateField.mem_fixedField_iff H x).1 hx σ⁻¹ (inv_mem hσ)]
    rfl

end Transitivity

/-! ### A3: decomposition groups preserve the valuation -/

section Decomposition

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- An automorphism stabilizing `W` preserves its maximal ideal. -/
lemma valuation_apply_lt_one_iff {σ : L ≃ₐ[F] L} {W : ValuationSubring L} (hσ : σ • W = W)
    (y : L) : W.valuation (σ y) < 1 ↔ W.valuation y < 1 := by
  have h := valuation_smul_lt_one_iff σ W (σ y)
  rw [hσ] at h
  rw [h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

/-- The orbit product of `σ x / x` over the powers `σⁱ`, `i < n`, telescopes to `σⁿ x / x`. -/
lemma prod_pow_apply_mul (σ : L ≃ₐ[F] L) {x : L} (hx : x ≠ 0) (n : ℕ) :
    (∏ i ∈ Finset.range n, (σ ^ i) (σ x / x)) * x = (σ ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, mul_right_comm, ih, map_div₀, pow_succ, AlgEquiv.mul_apply,
      mul_div_cancel₀ _ ((map_ne_zero (σ ^ n)).2 hx)]

/-- **A3.** An automorphism `σ` of finite order with `σ • W = W` preserves the valuation of `W`.
-/
theorem valuation_apply_eq {σ : L ≃ₐ[F] L} (hfin : IsOfFinOrder σ) {W : ValuationSubring L}
    (hσ : σ • W = W) (x : L) : W.valuation (σ x) = W.valuation x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  set n := orderOf σ
  have hn : 0 < n := hfin.orderOf_pos
  set y := σ x / x
  have hprod : ∏ i ∈ Finset.range n, (σ ^ i) y = 1 := by
    have h := prod_pow_apply_mul σ hx n
    rw [pow_orderOf_eq_one, AlgEquiv.one_apply] at h
    exact (mul_eq_right₀ hx).1 h
  -- the orbit product of an element of the maximal ideal lies in the maximal ideal
  have key : ∀ z : L, W.valuation z < 1 → ∀ m : ℕ,
      W.valuation (∏ i ∈ Finset.range (m + 1), (σ ^ i) z) < 1 := by
    intro z hz m
    have hpow : ∀ i : ℕ, W.valuation ((σ ^ i) z) < 1 := by
      intro i
      induction i with
      | zero => simpa using hz
      | succ i ih =>
        rw [pow_succ', AlgEquiv.mul_apply, valuation_apply_lt_one_iff hσ]
        exact ih
    induction m with
    | zero => simpa using hpow 0
    | succ m ih =>
      rw [Finset.prod_range_succ, map_mul]
      exact (mul_le_mul_left ih.le _).trans_lt (by rw [one_mul]; exact hpow (m + 1))
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases lt_trichotomy (W.valuation (σ x)) (W.valuation x) with hlt | heq | hgt
  · exfalso
    have hy : W.valuation y < 1 := by
      rw [map_div₀, div_lt_one₀ ((Valuation.pos_iff _).2 hx)]
      exact hlt
    have := key y hy m
    rw [← hm, hprod, map_one] at this
    exact lt_irrefl _ this
  · exact heq
  · exfalso
    have hσx : σ x ≠ 0 := (map_ne_zero σ).2 hx
    have hy : W.valuation y⁻¹ < 1 := by
      rw [map_inv₀, map_div₀, inv_div, div_lt_one₀ ((Valuation.pos_iff _).2 hσx)]
      exact hgt
    have := key y⁻¹ hy m
    simp_rw [map_inv₀] at this
    rw [Finset.prod_inv_distrib, ← hm, hprod, inv_one, map_one] at this
    exact lt_irrefl _ this

end Decomposition

/-! ### A4: residually algebraically closed points -/

section PGroup

open FundamentalInequality IsLocalRing

variable {M N : Type*} [Field M] [Field N] [Algebra M N]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  {u : Valuation M Γ₀} {w : Valuation N Γ₁} [u.HasExtension w]
  (hσ : ∀ (σ : N ≃ₐ[M] N) (x : N), w (σ x) = w x) [FiniteDimensional M N]

/-- **A4.** If the residue field of `u` is algebraically closed, the inertia group is the whole
automorphism group: the residue extension is finite, hence trivial. -/
theorem inertia_eq_top [IsAlgClosed (ResidueField u.valuationSubring)] :
    inertia u hσ = ⊤ := by
  have := finite_residueField (v := u) (w := w)
  refine eq_top_iff.2 fun σ _ ↦ (MonoidHom.mem_ker).2 (AlgEquiv.ext fun y ↦ ?_)
  obtain ⟨a, rfl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ResidueField u.valuationSubring) (K := ResidueField w.valuationSubring)).2 y
  exact (AlgEquiv.commutes _ a)

/-- **A4.** Divisibility of the values goes up finite extensions: if every value of `K` has
`n`-th roots among the values of `K`, the same holds for every finite extension `N / K`. -/
theorem exists_pow_eq_of_divisible {K : Type*} [Field K] [Algebra K N] [FiniteDimensional K N]
    {v : Valuation K Γ₀} [v.HasExtension w]
    (hdiv : ∀ (c : K) (n : ℕ), 0 < n → ∃ d : K, v d ^ n = v c) (c : N) (n : ℕ) (hn : 0 < n) :
    ∃ d : K, w (algebraMap K N d) ^ n = w c := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, by rw [map_zero, map_zero, zero_pow hn.ne']⟩
  obtain ⟨m, hm, c₀, -, hc₀⟩ :=
    exists_pow_valuation_eq w (Algebra.IsIntegral.isIntegral (R := K) c) hc
  obtain ⟨d, hd⟩ := hdiv c₀ (n * m) (Nat.mul_pos hn hm)
  refine ⟨d, (pow_left_inj₀ zero_le zero_le hm.ne').1 ?_⟩
  rw [hc₀, ← pow_mul, ← map_pow, ← map_pow, Valuation.HasExtension.val_map_eq_iff (vR := v),
    map_pow, hd]

include hσ in
/-- **A4.** At a point with algebraically closed residue field, divisible value group and enough
roots of unity, the whole automorphism group (= the decomposition group, when `M` is the
decomposition field) is a `p`-group, `p = char κ_u`. -/
theorem isPGroup_of_isAlgClosed [IsAlgClosed (ResidueField u.valuationSubring)]
    (hdiv : ∀ (c : M) (n : ℕ), 0 < n → ∃ d : M, u d ^ n = u c)
    (hμ : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ResidueField u.valuationSubring) ≠ 0 →
      ∃ ζ : M, IsPrimitiveRoot ζ ℓ) :
    IsPGroup (ringChar (ResidueField u.valuationSubring)) (N ≃ₐ[M] N) := by
  have h := isPGroup_inertia hσ hdiv hμ
  rw [inertia_eq_top hσ] at h
  exact h.of_equiv Subgroup.topEquiv

end PGroup

/-! ### Decomposition groups of valuation subrings -/

section DecompositionGroup

open FundamentalInequality IsLocalRing

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]

variable (F) in
/-- The **decomposition group** of a valuation subring `W` of `L`: its stabilizer in
`Aut(L / F)`. -/
abbrev decompositionGroup (W : ValuationSubring L) : Subgroup (L ≃ₐ[F] L) :=
  MulAction.stabilizer (L ≃ₐ[F] L) W

variable (F) in
/-- The **decomposition field** of `W`: the fixed field of the decomposition group. -/
abbrev decompositionField (W : ValuationSubring L) : IntermediateField F L :=
  IntermediateField.fixedField (decompositionGroup F W)

/-- The automorphisms over the decomposition field are exactly the decomposition group. -/
lemma restrictScalars_mem_decompositionGroup [IsGalois F L] {W : ValuationSubring L}
    (σ : L ≃ₐ[decompositionField F W] L) :
    σ.restrictScalars F ∈ decompositionGroup F W := by
  rw [← IntermediateField.fixingSubgroup_fixedField (decompositionGroup F W),
    IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact σ.commutes ⟨x, hx⟩

/-- **A3** over the decomposition field: its automorphisms preserve the valuation of `W` (the
hypothesis `hσ` of `Inertia`). -/
theorem valuation_decompositionField_apply [IsGalois F L] (W : ValuationSubring L)
    (σ : L ≃ₐ[decompositionField F W] L) (x : L) : W.valuation (σ x) = W.valuation x :=
  valuation_apply_eq (isOfFinOrder_of_finite (σ.restrictScalars F))
    (MulAction.mem_stabilizer_iff.1 (restrictScalars_mem_decompositionGroup σ)) x

/-- **A4** for valuation subrings: if the restriction `u` of `W` to the decomposition field has
algebraically closed residue field, divisible values and the relevant roots of unity, the
decomposition group of `W` is a `p`-group, `p = char κ_u`. -/
theorem isPGroup_decompositionGroup [IsGalois F L] (W : ValuationSubring L)
    [IsAlgClosed (ResidueField
      (W.valuation.comap (algebraMap (decompositionField F W) L)).valuationSubring)]
    (hdiv : ∀ (c : decompositionField F W) (n : ℕ), 0 < n → ∃ d : decompositionField F W,
      W.valuation (algebraMap _ L d) ^ n = W.valuation (algebraMap _ L c))
    (hμ : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ResidueField
      (W.valuation.comap (algebraMap (decompositionField F W) L)).valuationSubring) ≠ 0 →
      ∃ ζ : decompositionField F W, IsPrimitiveRoot ζ ℓ) :
    IsPGroup (ringChar (ResidueField
      (W.valuation.comap (algebraMap (decompositionField F W) L)).valuationSubring))
      (decompositionGroup F W) := by
  set E := decompositionField F W
  have h := isPGroup_of_isAlgClosed (u := W.valuation.comap (algebraMap E L)) (w := W.valuation)
    (valuation_decompositionField_apply W) hdiv hμ
  refine h.of_equiv ((IntermediateField.fixingSubgroupEquiv E).symm.trans
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField _)))

end DecompositionGroup

/-! ### A5: the Kummer steps -/

section Kummer

/-- **A5.** A Galois extension `L / K` of prime degree `p` with a primitive `p`-th root of unity
in `K` is a Kummer extension: `L = K(α)` with `α ^ p ∈ K`. Applied to the steps of a D4 chain
(`PGroupChain.exists_chain`) in a decomposition group. -/
theorem exists_kummer_generator {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {p : ℕ} [hp : Fact p.Prime]
    (hdeg : Module.finrank K L = p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ∃ α : L, α ^ p ∈ Set.range (algebraMap K L) ∧ IntermediateField.adjoin K {α} = ⊤ := by
  have hcard : Nat.card Gal(L/K) = p := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  haveI : IsCyclic Gal(L/K) := isCyclic_of_prime_card hcard
  have hK : (primitiveRoots (Module.finrank K L) K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by rw [hdeg]; exact hp.out.pos)).2 (hdeg ▸ hζ)⟩
  obtain ⟨α, hα, hadj⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hK
  exact ⟨α, hdeg ▸ hα, hadj⟩

end Kummer

end GaloisReduction

end SemistableReduction
