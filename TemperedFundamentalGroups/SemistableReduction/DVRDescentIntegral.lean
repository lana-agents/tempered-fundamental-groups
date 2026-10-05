/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentLocal
import TemperedFundamentalGroups.SemistableReduction.IntegralDescent

/-!
# The node chart over `O_C` meets `E(x)` in the node chart over `O_E` (O1, step (E))

Blueprint §9.12, O1 (the maximum principle over `E`).

* `GaussTube.exists_mul_pow_eq` and `GaussTube.gaussRat_le_one_of_mem`: elements of the node
  chart `O_C[x, c/x]` are Laurent polynomials with Gauss values `≤ 1` at the radii `1` and `|c|`;
* `DVRDescent.mem_nodeRing_of_map`: an element of `E(x)` whose image lies in `O_C[x, φ c/x]` lies
  in `O_E[x, c/x]` (Laurent, and the Gauss valuations of `E(x)` are restrictions, D1).
-/

open NNReal Polynomial

namespace SemistableReduction

namespace GaussTube

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- Elements of the node chart are Laurent polynomials. -/
theorem exists_mul_pow_eq {c : C} {a : RatFunc C} (ha : a ∈ nodeRing c) :
    ∃ (k : ℕ) (Q : C[X]), a * RatFunc.X ^ k = algebraMap C[X] (RatFunc C) Q := by
  induction ha using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨e, -, rfl⟩ | hz
    · exact ⟨0, Polynomial.C e, by simp⟩
    · rcases hz with rfl | hz
      · exact ⟨0, Polynomial.X, by simp⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨1, Polynomial.C c, ?_⟩
        rw [pow_one, div_mul_cancel₀ _ RatFunc.X_ne_zero,
          IsScalarTower.algebraMap_apply C C[X] (RatFunc C), Polynomial.algebraMap_eq]
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, P, hP⟩ := ha
    obtain ⟨l, Q, hQ⟩ := hb
    refine ⟨k + l, P * Polynomial.X ^ l + Q * Polynomial.X ^ k, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hP, ← hQ, RatFunc.algebraMap_X]
    ring
  | neg a _ ha =>
    obtain ⟨k, P, hP⟩ := ha
    exact ⟨k, -P, by rw [map_neg, ← hP]; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, P, hP⟩ := ha
    obtain ⟨l, Q, hQ⟩ := hb
    exact ⟨k + l, P * Q, by rw [map_mul, ← hP, ← hQ]; ring⟩

/-- Elements of the node chart have Gauss values `≤ 1` at every radius in `[|c|, 1]`. -/
theorem gaussRat_le_one_of_mem {c : C} {a : RatFunc C} (ha : a ∈ nodeRing c) {s : ℝ≥0ˣ}
    (hs1 : (s : ℝ≥0) ≤ 1) (hcs : ‖c‖₊ ≤ s) : w s a ≤ 1 := by
  induction ha using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨e, he, rfl⟩ | hz
    · rw [gaussRat_C]
      exact he
    · rcases hz with rfl | hz
      · rw [AnnulusUnit.gaussRat_X]; exact hs1
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        rw [map_div₀, gaussRat_C, AnnulusUnit.gaussRat_X]
        exact div_le_one_of_le₀ hcs zero_le
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  | neg a _ ha => rwa [Valuation.map_neg]
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_le_one' ha hb

end GaussTube

/-- A rational function whose image is a polynomial is a polynomial. -/
theorem exists_eq_algebraMap_of_ratFuncMap {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    {f : RatFunc K} {Q : L[X]} (h : ratFuncMap φ f = algebraMap L[X] (RatFunc L) Q) :
    ∃ P : K[X], f = algebraMap K[X] (RatFunc K) P := by
  have hden : algebraMap L[X] (RatFunc L) (f.denom.map φ) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective L[X] (RatFunc L))]
    exact (f.monic_denom.map φ).ne_zero
  rw [← RatFunc.num_div_denom f, map_div₀, ratFuncMap_algebraMap, ratFuncMap_algebraMap,
    div_eq_iff hden, ← map_mul] at h
  have h' := IsFractionRing.injective L[X] (RatFunc L) h
  have hdvd : f.denom ∣ f.num := by
    rw [← Polynomial.map_dvd_map φ φ.injective f.monic_denom, h']
    exact dvd_mul_left _ _
  obtain ⟨P, hP⟩ := hdvd
  refine ⟨P, ?_⟩
  rw [← RatFunc.num_div_denom f, hP, map_mul, mul_div_cancel_left₀]
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))]
  exact f.monic_denom.ne_zero

namespace DVRDescent

open GaussTube

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}

omit [IsUltrametricDist C] [IsUltrametricDist E] in
lemma ratFuncMap_X : ratFuncMap φ RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratFuncMap_algebraMap, Polynomial.map_X, RatFunc.algebraMap_X]

/-- **`O_C[x, φ c/x] ∩ E(x) = O_E[x, c/x]`.** -/
theorem mem_nodeRing_of_map (hφ : ∀ e, ‖φ e‖ = ‖e‖) {c : E} (hc0 : c ≠ 0) (hc1 : ‖c‖ ≤ 1)
    {a : RatFunc E}
    (ha : ratFuncMap φ a ∈ nodeRing (φ c)) : a ∈ nodeRing c := by
  obtain ⟨k, Q, hQ⟩ := exists_mul_pow_eq ha
  have hQ' : ratFuncMap φ (a * RatFunc.X ^ k) = algebraMap C[X] (RatFunc C) Q := by
    rw [map_mul, map_pow, ratFuncMap_X, hQ]
  obtain ⟨P, hP⟩ := exists_eq_algebraMap_of_ratFuncMap φ hQ'
  have hval : ∀ s : ℝ≥0ˣ, gaussRat (NormedField.valuation (K := E)) 0 s a =
      gaussRat (NormedField.valuation (K := C)) 0 s (ratFuncMap φ a) := by
    intro s
    have := gaussRat_comap φ (NormedField.valuation (K := C)) (0 : E) s
    rw [map_zero] at this
    rw [← vE_eq φ hφ, ← this, Valuation.comap_apply]
  have hcn : ‖φ c‖₊ = ‖c‖₊ := by ext; simp [hφ]
  refine mem_nodeRing_of_mul_pow hc0 hP ?_ ?_
  · rw [hval]
    exact gaussRat_le_one_of_mem ha le_rfl (by
      rw [Units.val_one, hcn]
      exact_mod_cast hc1)
  · rw [hval]
    exact gaussRat_le_one_of_mem ha (by
      change ‖c‖₊ ≤ 1
      exact_mod_cast hc1) (by simp [hcn])

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  {χ : F₀ →+* F'}

omit [IsUltrametricDist C] [IsUltrametricDist E] [FiniteDimensional (RatFunc C) F']
  [FiniteDimensional (RatFunc E) F₀] in
lemma aeval_map_χ (hχ : IsCompat φ χ) (y : F₀) (P : (RatFunc E)[X]) :
    aeval (χ y) (P.map (ratFuncMap φ)) = χ (aeval y P) := by
  rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
  congr 1
  ext f
  exact (hχ f).symm

omit [IsUltrametricDist C] [IsUltrametricDist E] in
/-- **Minimal polynomials are preserved** when `F' = C(x)·χ(F₀)` and `[F₀ : E(x)] = [F' : C(x)]`. -/
theorem minpoly_χ_eq (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤) (y : F₀) :
    minpoly (RatFunc C) (χ y) = (minpoly (RatFunc E) y).map (ratFuncMap φ) := by
  classical
  set p := minpoly (RatFunc E) y
  have hyi : IsIntegral (RatFunc E) y := Algebra.IsIntegral.isIntegral y
  have hχyi : IsIntegral (RatFunc C) (χ y) := Algebra.IsIntegral.isIntegral _
  have hp : p.Monic := minpoly.monic hyi
  have hdvd : minpoly (RatFunc C) (χ y) ∣ p.map (ratFuncMap φ) :=
    minpoly.dvd _ _ (by rw [aeval_map_χ hχ, minpoly.aeval, map_zero])
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hχyi) (hp.map _) hdvd
    ?_).symm
  rw [natDegree_map]
  -- degree count
  set K₀ := IntermediateField.adjoin (RatFunc E) {y}
  set K₁ := IntermediateField.adjoin (RatFunc C) {χ y}
  have h₀ := Module.finrank_mul_finrank (RatFunc E) K₀ F₀
  have h₁ := Module.finrank_mul_finrank (RatFunc C) K₁ F'
  rw [IntermediateField.adjoin.finrank hyi] at h₀
  rw [IntermediateField.adjoin.finrank hχyi] at h₁
  -- `F'` is spanned over `K₁` by the image of a `K₀`-basis of `F₀`
  let b := Module.finBasis K₀ F₀
  have hχK : ∀ z : K₀, χ z ∈ K₁ := by
    rintro ⟨z, hz⟩
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff _ z).mp hz
    change χ (aeval y r / aeval y s) ∈ K₁
    rw [map_div₀, ← aeval_map_χ hχ, ← aeval_map_χ hχ]
    have hm : ∀ q : (RatFunc C)[X], aeval (χ y) q ∈ K₁ := fun q ↦ by
      rw [show χ y = ((⟨χ y, IntermediateField.mem_adjoin_simple_self _ _⟩ : K₁) : F') from rfl,
        IntermediateField.aeval_coe]
      exact Subtype.coe_prop _
    exact K₁.div_mem (hm _) (hm _)
  have hχmem : ∀ f : F₀, χ f ∈ Submodule.span K₁ (Set.range fun i ↦ χ (b i)) := by
    intro f
    rw [← b.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    have : χ (b.repr f j • b j) = (⟨χ (b.repr f j), hχK _⟩ : K₁) • χ (b j) := by
      rw [Algebra.smul_def, map_mul]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hspan : Submodule.span K₁ (Set.range fun i ↦ χ (b i)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Algebra.adjoin (RatFunc C) {χ θ₀} := hθ ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨P, rfl⟩ := hz
    change aeval (χ θ₀) P ∈ _
    rw [aeval_eq_sum_range]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hc : (algebraMap (RatFunc C) F' (P.coeff i)) ∈ K₁ := K₁.algebraMap_mem _
    have : P.coeff i • χ θ₀ ^ i = (⟨_, hc⟩ : K₁) • χ (θ₀ ^ i) := by
      rw [map_pow, Algebra.smul_def, Algebra.smul_def]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (hχmem _)
  have hle : Module.finrank K₁ F' ≤ Module.finrank K₀ F₀ := by
    rw [← finrank_top K₁ F', ← hspan]
    refine (finrank_span_le_card _).trans ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  have hpos : 0 < Module.finrank K₀ F₀ := Module.finrank_pos
  rw [hdeg] at h₀
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc p.natDegree * Module.finrank K₀ F₀ = (minpoly (RatFunc C) (χ y)).natDegree *
        Module.finrank K₁ F' := h₀.trans h₁.symm
    _ ≤ _ := Nat.mul_le_mul_left _ hle

/-- **Integrality descends**: an element of `F₀` whose image is integral over `O_C[x, φ c/x]` is
integral over `O_E[x, c/x]`. -/
theorem isIntegral_of_χ (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤) {c : E} (hc0 : c ≠ 0)
    (hc1 : ‖c‖ ≤ 1) {y : F₀} (hy : IsIntegral (nodeRing (φ c)) (χ y)) :
    IsIntegral (nodeRing c) y := by
  have hφc0 : φ c ≠ 0 := by simpa using hc0
  have hφc1 : ‖φ c‖ ≤ 1 := by rw [hφ]; exact hc1
  haveI := isIntegrallyClosed_nodeRing hφc0 hφc1
  haveI := isFractionRing_nodeRing (φ c)
  exact isIntegral_of_isIntegral_map (ratFuncMap φ) χ (nodeRing c) (nodeRing (φ c))
    (fun z hz ↦ mem_nodeRing_of_map hφ hc0 hc1 hz) (minpoly_χ_eq hχ hdeg hθ y) hy

/-- **`B_E = R' ∩ F₀`**: an element of `F₀` mapping into `Rint (φ c) F'` lies in `BE F₀ c`. -/
theorem mem_BE_of_χ (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤) {c : E} (hc0 : c ≠ 0)
    (hc1 : ‖c‖ ≤ 1) {y : F₀} (hy : χ y ∈ Rint (φ c) F') : y ∈ BE F₀ c :=
  isIntegral_of_χ hφ hχ hdeg hθ hc0 hc1 hy

end DVRDescent

end SemistableReduction
