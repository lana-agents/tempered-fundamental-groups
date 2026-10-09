/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentResidue
import TemperedFundamentalGroups.SemistableReduction.FundamentalInequalitySum

/-!
# `e = 1` and linear disjointness at the vertices over `E` (O1, S7.9 (ii))

Blueprint §9.12, O1. In the setting of `DVRDescentSetting` with `[F₀ : E(x)] = [F' : C(x)]`,
suppose that restriction to `F₀` is injective on the extensions `W ∈ Ext C F'` of the outer Gauss
point (D3c) and that every `κ(W)` is generated over `𝓀` by the residues over `E` (`resE`, D3d).
Then the count `Σ_W e(W|F₀) f(W|F₀) ≤ [F₀ : E(x)] = [F' : C(x)] = Σ_W f(W)` (the fundamental
inequality over `E(x)`, `LocalGlobal.finsum_ramificationIdx_mul_inertiaDeg_le`, and W4 over `C`
with `e = 1`) with `f(W) ≤ f(W|F₀)` (generation) forces, at every `W`:

* **`exists_valuation_eq`** (`e = 1`): the values of `W` on `χ(F₀)` are values of `E`;
* **`linDisj_resE`**: `resE χ W` is linearly disjoint from `𝓀` over the residue field `κ_E`
  (`f(W|F₀) = f(W)` and generation).

Auxiliary: `span_eq_top_of_adjoin`, `finrank_le_of_adjoin`, `eq_zero_of_finrank_eq` (generation
and degrees of residue fields), `eq_zero_of_linearIndependent` (`k` and `kv(x)` are linearly
disjoint over `kv` inside `k(x)`), `finsum_le_finrankE` (the fundamental inequality over `E(x)`),
`restrictExt` (restriction of vertices), `ramificationIdx_eq_one_and_inertiaDeg_eq` (the count).
-/

open NNReal Polynomial IsLocalRing Valuation

namespace SemistableReduction

namespace DVRDescent

open GaussTube FundamentalInequality GaussStability GaussFibre

universe u

/-! ### Generation and degrees of residue fields -/

section Generation

variable {K₀ K₁ M₀ L k : Type*} [Field K₀] [Field K₁] [Field M₀] [Field L] [Field k]
  [Algebra K₀ M₀] [FiniteDimensional K₀ M₀] [Algebra K₁ L] [Algebra k K₁] [Algebra k L]
  [IsScalarTower k K₁ L] (ιK : K₀ →+* K₁) (ιM : M₀ →+* L)
  (hcomm : ∀ x, ιM (algebraMap K₀ M₀ x) = algebraMap K₁ L (ιK x))

include hcomm in
/-- A `K₀`-basis of `M₀` spans `L` over `K₁` if the image of `M₀` generates `L` over `k`. -/
theorem span_eq_top_of_adjoin {ι : Type*} (b : Module.Basis ι K₀ M₀)
    (hgen : IntermediateField.adjoin k (Set.range ιM) = ⊤) :
    Submodule.span K₁ (Set.range (ιM ∘ b)) = ⊤ := by
  classical
  haveI : Finite ι := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite ι
  set V := Submodule.span K₁ (Set.range (ιM ∘ b))
  have hM : ∀ m, ιM m ∈ V := by
    intro m
    rw [← b.sum_repr m, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul, hcomm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have halg : ∀ x ∈ Set.range ιM, IsAlgebraic K₁ x := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨p, hp0, hp⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := K₀) m)
    refine ⟨p.map ιK, (Polynomial.map_ne_zero_iff ιK.injective).mpr hp0, ?_⟩
    have : aeval (ιM m) (p.map ιK) = ιM (aeval m p) := by
      have hc : (algebraMap K₁ L).comp ιK = ιM.comp (algebraMap K₀ M₀) :=
        RingHom.ext fun x ↦ (hcomm x).symm
      rw [aeval_def, eval₂_map, hc, ← hom_eval₂, ← aeval_def]
    rw [this, hp, map_zero]
  set T := IntermediateField.adjoin K₁ (Set.range ιM)
  have hTV : ∀ x ∈ T, x ∈ V := by
    intro x hx
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg] at hx
    have hle : (Algebra.adjoin K₁ (Set.range ιM)).toSubmodule ≤ V := by
      rw [Algebra.adjoin_eq_span, Submodule.span_le]
      intro y hy
      have hsub : Submonoid.closure (Set.range ιM) ≤ MonoidHom.mrange (ιM : M₀ →* L) :=
        Submonoid.closure_le.mpr (by rintro _ ⟨m, rfl⟩; exact ⟨m, rfl⟩)
      obtain ⟨m, rfl⟩ := hsub hy
      exact hM m
    exact hle hx
  have hkT : IntermediateField.adjoin k (Set.range ιM) ≤ T.restrictScalars k := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    exact IntermediateField.subset_adjoin K₁ _ hx
  rw [hgen, top_le_iff] at hkT
  rw [eq_top_iff]
  intro x _
  apply hTV
  have : x ∈ T.restrictScalars k := by rw [hkT]; trivial
  exact this

include hcomm in
/-- `[L : K₁] ≤ [M₀ : K₀]` if the image of `M₀` generates `L` over `k ⊆ K₁`. -/
theorem finrank_le_of_adjoin (hgen : IntermediateField.adjoin k (Set.range ιM) = ⊤) :
    Module.finrank K₁ L ≤ Module.finrank K₀ M₀ := by
  let b := Module.finBasis K₀ M₀
  have h := finrank_range_le_card (R := K₁) (ιM ∘ b)
  rw [Set.finrank, span_eq_top_of_adjoin ιK ιM hcomm b hgen, finrank_top, Fintype.card_fin] at h
  exact h

include hcomm in
/-- If moreover `[L : K₁] = [M₀ : K₀]`, `K₀`-independent elements of `M₀` stay independent over
`K₁` after `ιM`, against `k`-combinations whose coefficients are independent over the image of
`K₀`: `M₀` and `K₁` are linearly disjoint over `K₀`. -/
theorem eq_zero_of_finrank_eq (hgen : IntermediateField.adjoin k (Set.range ιM) = ⊤)
    (heq : Module.finrank K₁ L = Module.finrank K₀ M₀) {m : ℕ} (β : Fin m → k)
    (hLD : ∀ c : Fin m → K₀, ∑ l, algebraMap k K₁ (β l) * ιK (c l) = 0 → c = 0)
    (z : Fin m → M₀) (hz : ∑ l, algebraMap k L (β l) * ιM (z l) = 0) : z = 0 := by
  classical
  let b := Module.finBasis K₀ M₀
  have hli : LinearIndependent K₁ (ιM ∘ b) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank
      (span_eq_top_of_adjoin ιK ιM hcomm b hgen).ge (by rw [Fintype.card_fin, heq])
  set c : Fin m → Fin (Module.finrank K₀ M₀) → K₀ := fun l i ↦ b.repr (z l) i
  have hzc : ∀ l, ιM (z l) = ∑ i, algebraMap K₁ L (ιK (c l i)) * ιM (b i) := by
    intro l
    conv_lhs => rw [← b.sum_repr (z l)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul, hcomm]
  have hsum : ∑ i, (∑ l, algebraMap k K₁ (β l) * ιK (c l i)) • (ιM ∘ b) i = 0 := by
    rw [← hz]
    simp only [Function.comp_apply, Algebra.smul_def, map_sum, map_mul, Finset.sum_mul, hzc,
      Finset.mul_sum, ← IsScalarTower.algebraMap_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hcoef := Fintype.linearIndependent_iff.mp hli _ hsum
  have hc0 : ∀ i, (fun l ↦ c l i) = 0 := fun i ↦ hLD _ (hcoef i)
  funext l
  rw [← b.sum_repr (z l)]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have := congrFun (hc0 i) l
  simp only [Pi.zero_apply] at this
  change c l i • b i = 0
  rw [this, zero_smul]

end Generation

/-! ### Linear disjointness of the constants and a rational function field -/

section RatFuncDisjoint

variable {kv K₀ k K₁ : Type*} [Field kv] [Field K₀] [Field k] [Field K₁] [Algebra kv K₀]
  [Algebra k K₁] (ψ : kv →+* k) (ιK : K₀ →+* K₁)
  (hcomm : ∀ a, ιK (algebraMap kv K₀ a) = algebraMap k K₁ (ψ a)) {x₀ : K₀}
  (hx₀ : IntermediateField.adjoin kv {x₀} = ⊤) (hx₁ : Transcendental k (ιK x₀))

include hcomm hx₀ hx₁ in
/-- **`k` and `kv(x)` are linearly disjoint over `kv` inside `k(x)`**: `kv`-independent elements
of `k` stay independent over `kv(x₀)` (`x₀` generating, its image transcendental over `k`). -/
theorem eq_zero_of_linearIndependent {m : ℕ} (β : Fin m → k)
    (hβ : ∀ a : Fin m → kv, ∑ l, ψ (a l) * β l = 0 → a = 0)
    (c : Fin m → K₀) (hc : ∑ l, algebraMap k K₁ (β l) * ιK (c l) = 0) : c = 0 := by
  classical
  -- `c l = r(x₀) / s(x₀)`
  have hfrac : ∀ l, ∃ r s : kv[X], aeval x₀ s ≠ 0 ∧ c l * aeval x₀ s = aeval x₀ r := by
    intro l
    have hl : c l ∈ IntermediateField.adjoin kv {x₀} := by rw [hx₀]; trivial
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff kv (c l)).mp hl
    by_cases hs : aeval x₀ s = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [hrs, hs, div_zero, zero_mul, map_zero]
    · exact ⟨r, s, hs, by rw [hrs, div_mul_cancel₀ _ hs]⟩
  choose r s hs hrs using hfrac
  set p : Fin m → kv[X] := fun l ↦ r l * ∏ l' ∈ Finset.univ.erase l, s l'
  have hD : aeval x₀ (∏ l, s l) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun l _ ↦ hs l
  have hp : ∀ l, c l * aeval x₀ (∏ l, s l) = aeval x₀ (p l) := by
    intro l
    rw [← Finset.mul_prod_erase _ s (Finset.mem_univ l), map_mul, ← mul_assoc, hrs]
    simp only [p, map_mul]
  -- the image of a polynomial in `x₀`
  have himg : ∀ q : kv[X], ιK (aeval x₀ q) = aeval (ιK x₀) (q.map ψ) := by
    intro q
    have hc : ιK.comp (algebraMap kv K₀) = (algebraMap k K₁).comp ψ :=
      RingHom.ext hcomm
    rw [aeval_def, aeval_def, eval₂_map, ← hc, hom_eval₂]
  -- the polynomial relation over `k`
  set Q : k[X] := ∑ l, Polynomial.C (β l) * (p l).map ψ
  have hQ : aeval (ιK x₀) Q = 0 := by
    have := congrArg (· * ιK (aeval x₀ (∏ l, s l))) hc
    simp only [zero_mul, Finset.sum_mul] at this
    rw [← this]
    simp only [Q, map_sum, map_mul, aeval_C]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [mul_assoc, ← map_mul, hp, himg]
  have hQ0 : Q = 0 := by
    by_contra h
    exact hx₁ ⟨Q, h, hQ⟩
  -- coefficientwise
  have hcoeff : ∀ l n, (p l).coeff n = 0 := by
    intro l n
    have h := congrArg (fun q : k[X] ↦ q.coeff n) hQ0
    simp only [Q, finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at h
    have := hβ (fun l ↦ (p l).coeff n) (by
      rw [← h]; exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _)
    exact congrFun this l
  funext l
  have hpl : p l = 0 := Polynomial.ext fun n ↦ by rw [hcoeff, coeff_zero]
  have := hp l
  rw [hpl, map_zero] at this
  exact (mul_eq_zero.mp this).resolve_right hD

end RatFuncDisjoint

/-! ### The count over `E(x)` -/

section CountE

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  [Algebra.IsSeparable (RatFunc E) F₀]

/-- There are only finitely many extensions of `w_{0,1}` over `E`. -/
lemma finite_extE : Finite (Ext E F₀) := by
  haveI : Fact (DenseRange (algebraMap (GaussField (0 : E) 1)
      (UniformSpace.Completion (GaussField (0 : E) 1)))) :=
    ⟨DenseCompletion.denseRange_algebraMap_completion _⟩
  haveI := LocalGlobal.finite_extension (F := GaussField (0 : E) 1) (F' := F₀)
    (UniformSpace.Completion (GaussField (0 : E) 1))
  exact Finite.of_equiv _ gaussExtensionEquiv.symm

/-- **The fundamental inequality over `E(x)`**: `Σ_w e(w) f(w) ≤ [F₀ : E(x)]`. -/
lemma finsum_le_finrankE :
    ∑ᶠ w : Ext E F₀, ramificationIdx (RatFunc E) w.1 * inertiaDeg (gauss1 E) w.1 ≤
      Module.finrank (RatFunc E) F₀ := by
  have h := LocalGlobal.finsum_ramificationIdx_mul_inertiaDeg_le
    (F := GaussField (0 : E) 1) (F' := F₀)
  have hdeg : Module.finrank (GaussField (0 : E) 1) F₀ = Module.finrank (RatFunc E) F₀ :=
    Algebra.finrank_eq_of_equiv_equiv (WithAbs.equiv _) (RingEquiv.refl F₀) (by ext; rfl)
  rw [← hdeg]
  refine le_of_eq_of_le ?_ h
  rw [← finsum_comp_equiv gaussExtensionEquiv]
  refine finsum_congr fun w ↦ ?_
  rw [inertiaDeg_gaussField, ← ramificationIdx_gaussField (a := (0 : E)) (r := 1)]
  rfl

end CountE

/-! ### Restricting vertices and residue fields to `E` -/

section Restrict

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* F'} (hχ : IsCompat φ χ)

omit [IsUltrametricDist C] [IsUltrametricDist E] in
include hφ in
lemma nnnorm_map (e : E) : ‖φ e‖₊ = ‖e‖₊ := NNReal.eq (hφ e)

include hφ in
/-- `w_{0,1}` over `C` restricts to `w_{0,1}` over `E`. -/
lemma gauss1_comap : (gauss1 C).comap (ratFuncMap φ) = gauss1 E := by
  have := gaussRat_comap φ (NormedField.valuation (K := C)) (0 : E) 1
  rw [map_zero] at this
  rw [gauss1, this]
  change gaussRat (vE φ) 0 1 = _
  rw [vE_eq φ hφ]

include hφ in
lemma gauss1_ratFuncMap (f : RatFunc E) : gauss1 C (ratFuncMap φ f) = gauss1 E f := by
  rw [← comap_apply, gauss1_comap hφ]

include hφ hχ in
/-- The restriction of an extension of `w_{0,1}` to `F₀`. -/
lemma restrict_comap (W : Ext C F') :
    (W.1.comap χ).comap (algebraMap (RatFunc E) F₀) = gaussRat (NormedField.valuation (K := E))
      0 1 := by
  ext f
  rw [comap_apply, comap_apply, hχ f, valuation_algebraMap, gauss1_ratFuncMap hφ]

/-- The restriction of an extension of `w_{0,1}` to `F₀`, an extension over `E`. -/
noncomputable def restrictExt (W : Ext C F') : Ext E F₀ := ⟨W.1.comap χ, restrict_comap hφ hχ W⟩

lemma restrictExt_apply (W : Ext C F') (f : F₀) :
    (restrictExt hφ hχ W).1 f = W.1 (χ f) := rfl

/-- `O_E → O_C`, for the norm valuations. -/
noncomputable def intMap :
    (NormedField.valuation (K := E)).valuationSubring →+*
      (NormedField.valuation (K := C)).valuationSubring :=
  (φ.comp (NormedField.valuation (K := E)).valuationSubring.subtype).codRestrict _ fun a ↦ by
    have := a.2
    rw [mem_valuationSubring_iff, NormedField.valuation_apply] at this ⊢
    simp only [RingHom.coe_comp, Function.comp_apply, ValuationSubring.coe_subtype]
    rwa [nnnorm_map hφ]

instance : IsLocalHom (intMap hφ) := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one] at ha ⊢
  change NormedField.valuation (φ a) = 1 at ha
  rwa [NormedField.valuation_apply, nnnorm_map hφ, ← NormedField.valuation_apply] at ha

/-- `O_{w_{0,1}} → O_{w_{0,1}}` over `ratFuncMap φ`. -/
noncomputable def gaussMap : (gauss1 E).valuationSubring →+* (gauss1 C).valuationSubring :=
  ((ratFuncMap φ).comp (gauss1 E).valuationSubring.subtype).codRestrict _ fun a ↦ by
    have := a.2
    rw [mem_valuationSubring_iff] at this ⊢
    simp only [RingHom.coe_comp, Function.comp_apply, ValuationSubring.coe_subtype]
    rwa [gauss1_ratFuncMap hφ]

instance : IsLocalHom (gaussMap hφ) := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one] at ha ⊢
  change gauss1 C (ratFuncMap φ a) = 1 at ha
  rwa [gauss1_ratFuncMap hφ] at ha

/-- `O_{W|F₀} → O_W` over `χ`. -/
noncomputable def wMap (W : Ext C F') :
    (restrictExt hφ hχ W).1.valuationSubring →+* W.1.valuationSubring :=
  (χ.comp (restrictExt hφ hχ W).1.valuationSubring.subtype).codRestrict _ fun a ↦ a.2

instance (W : Ext C F') : IsLocalHom (wMap hφ hχ W) := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one] at ha ⊢
  exact ha

local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "kv" =>
  ResidueField (Valuation.valuationSubring (NormedField.valuation (K := E)))
local notation "K₀" => ResidueField (Valuation.valuationSubring (gauss1 E))
local notation "K₁" => ResidueField (Valuation.valuationSubring (gauss1 C))

/-- The residue map `κ_E → 𝓀`. -/
noncomputable abbrev ψ : kv →+* 𝓀 := ResidueField.map (intMap hφ)

/-- The residue map `κ_E(x̄) → 𝓀(x̄)`. -/
noncomputable abbrev ιK : K₀ →+* K₁ := ResidueField.map (gaussMap hφ)

/-- The residue map `κ(W|F₀) → κ(W)`. -/
noncomputable abbrev ιM (W : Ext C F') :
    ResidueField (restrictExt hφ hχ W).1.valuationSubring →+* ResidueField W.1.valuationSubring :=
  ResidueField.map (wMap hφ hχ W)

lemma ιK_algebraMap (a : kv) : ιK hφ (algebraMap kv K₀ a) = algebraMap 𝓀 K₁ (ψ hφ a) := by
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [HasExtension.algebraMap_residue_eq_residue_algebraMap, ResidueField.map_residue,
    ResidueField.map_residue, HasExtension.algebraMap_residue_eq_residue_algebraMap]
  congr 1
  apply Subtype.ext
  change ratFuncMap φ (algebraMap E (RatFunc E) a) = algebraMap C (RatFunc C) (φ a)
  rw [ratFuncMap_algebraMap_C]

lemma ιM_algebraMap (W : Ext C F') (x : K₀) :
    ιM hφ hχ W (algebraMap K₀ (ResidueField (restrictExt hφ hχ W).1.valuationSubring) x) =
      algebraMap K₁ (ResidueField W.1.valuationSubring) (ιK hφ x) := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [HasExtension.algebraMap_residue_eq_residue_algebraMap, ResidueField.map_residue,
    ResidueField.map_residue, HasExtension.algebraMap_residue_eq_residue_algebraMap]
  congr 1
  apply Subtype.ext
  change χ (algebraMap (RatFunc E) F₀ x) = algebraMap (RatFunc C) F' (ratFuncMap φ x)
  rw [hχ]

/-- The residue of `x` over `E`. -/
noncomputable abbrev xbar₀ : K₀ :=
  residue _ (gaussGen (NormedField.valuation (K := E)) 0 1 (c := 1) (by simp))

/-- The residue of `x` over `C`. -/
noncomputable abbrev xbar₁ : K₁ :=
  residue _ (gaussGen (NormedField.valuation (K := C)) 0 1 (c := 1) (by simp))

lemma ιK_xbar : ιK hφ xbar₀ = xbar₁ := by
  rw [ResidueField.map_residue]
  congr 1
  apply Subtype.ext
  change ratFuncMap φ (algebraMap E[X] (RatFunc E) (gaussLin 0 1)) =
    algebraMap C[X] (RatFunc C) (gaussLin 0 1)
  rw [ratFuncMap_algebraMap]
  simp [gaussLin]

/-- `O_E` for the norm valuation is `O_E` for the restricted valuation. -/
noncomputable def tauMap :
    (NormedField.valuation (K := E)).valuationSubring →+* (vE φ).valuationSubring :=
  ((NormedField.valuation (K := E)).valuationSubring.subtype).codRestrict _ fun a ↦ by
    have := a.2
    rw [mem_valuationSubring_iff] at this ⊢
    rwa [vE_eq φ hφ]

instance : IsLocalHom (tauMap hφ) := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one] at ha ⊢
  change vE φ a = 1 at ha
  rwa [vE_eq φ hφ] at ha

/-- `κ_E` for the norm valuation is `κ_E` for the restricted valuation. -/
noncomputable abbrev τ : kv →+* kE φ := ResidueField.map (tauMap hφ)

lemma kE_τ (a : kv) : ResidueField.map (integersMap φ) (τ hφ a) = ψ hφ a := by
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
  rfl

lemma mem_resE_iff (W : Ext C F') (z : ResidueField W.1.valuationSubring) :
    z ∈ resE χ W ↔ ∃ m, ιM hφ hχ W m = z := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨residue _ ⟨f, hf⟩, ?_⟩
    rw [ResidueField.map_residue, red_of_le (w := W) hf]
    rfl
  · rintro ⟨m, rfl⟩
    obtain ⟨⟨f, hf⟩, rfl⟩ := residue_surjective m
    refine ⟨f, hf, ?_⟩
    rw [ResidueField.map_residue, red_of_le (w := W) hf]
    rfl

end Restrict

/-! ### `e = 1` and linear disjointness -/

section Main

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  [Algebra.IsSeparable (RatFunc E) F₀] {χ : F₀ →+* F'} (hχ : IsCompat φ χ)
  (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
  (hinj : ∀ W W' : Ext C F', W.1.comap χ = W'.1.comap χ → W = W')
  (hgen : ∀ W : Ext C F', IntermediateField.adjoin (ResidueField (HenselComplete.integers C))
    (resE χ W : Set (ResidueField W.1.valuationSubring)) = ⊤)

local notation "𝓀" => ResidueField (HenselComplete.integers C)

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc E) F₀] in
include hφ hχ hgen in
/-- `f(W) ≤ f(W|F₀)` (generation). -/
lemma inertiaDeg_le (W : Ext C F') :
    inertiaDeg (gauss1 C) W.1 ≤ inertiaDeg (gauss1 E) (restrictExt hφ hχ W).1 := by
  haveI := finite_residueField (v := gauss1 E) (w := (restrictExt hφ hχ W).1)
  refine finrank_le_of_adjoin (k := 𝓀) (ιK hφ) (ιM hφ hχ W) (ιM_algebraMap hφ hχ W) ?_
  rw [← hgen W]
  congr 1
  ext z
  rw [Set.mem_range, SetLike.mem_coe, mem_resE_iff hφ hχ]

include hp hp1 hφ hχ hdeg hinj hgen in
/-- **The count**: `e(W|F₀) = 1` and `f(W|F₀) = f(W)` at every vertex. -/
theorem ramificationIdx_eq_one_and_inertiaDeg_eq (W : Ext C F') :
    ramificationIdx (RatFunc E) (restrictExt hφ hχ W).1 = 1 ∧
      inertiaDeg (gauss1 E) (restrictExt hφ hχ W).1 = inertiaDeg (gauss1 C) W.1 := by
  classical
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  haveI : Fintype (Ext C F') := Fintype.ofFinite _
  haveI : Finite (Ext E F₀) := finite_extE
  haveI : Fintype (Ext E F₀) := Fintype.ofFinite _
  set h : Ext E F₀ → ℕ := fun w ↦ ramificationIdx (RatFunc E) w.1 * inertiaDeg (gauss1 E) w.1
  have hinj' : Function.Injective (restrictExt hφ hχ (F₀ := F₀) (F' := F')) := fun W W' hWW' ↦
    hinj W W' (congrArg Subtype.val hWW')
  have hle : ∑ W : Ext C F', h (restrictExt hφ hχ W) ≤ Module.finrank (RatFunc E) F₀ := by
    rw [← Finset.sum_image (fun W _ W' _ hWW' ↦ hinj' hWW')]
    calc _ ≤ ∑ w : Ext E F₀, h w :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ Nat.zero_le _
      _ = ∑ᶠ w : Ext E F₀, h w := (finsum_eq_sum_of_fintype _).symm
      _ ≤ _ := finsum_le_finrankE
  have hsum : ∑ W : Ext C F', inertiaDeg (gauss1 C) W.1 = Module.finrank (RatFunc E) F₀ := by
    rw [hdeg]; exact sum_inertiaDeg_eq hp hp1
  have key := eq_one_and_eq_of_sum_le Finset.univ
    (fun W ↦ ramificationIdx (RatFunc E) (restrictExt hφ hχ W).1)
    (fun W ↦ inertiaDeg (gauss1 E) (restrictExt hφ hχ W).1)
    (fun W ↦ inertiaDeg (gauss1 C) W.1) hle hsum
    (fun W _ ↦ inertiaDeg_le hφ hχ hgen W)
    (fun W _ ↦ Nat.one_le_iff_ne_zero.mpr (ramificationIdx_ne_zero _))
    (fun W _ ↦ by
      haveI := finite_residueField (v := gauss1 C) (w := W.1)
      exact Module.finrank_pos)
    W (Finset.mem_univ W)
  exact key

include hp hp1 hφ hχ hdeg hinj hgen

/-- **`e = 1` over `E`**: the values of a vertex `W` on `χ(F₀)` are values of `E`. -/
theorem exists_valuation_eq (W : Ext C F') (f : F₀) : ∃ e : E, W.1 (χ f) = vE φ e := by
  obtain ⟨he, -⟩ := ramificationIdx_eq_one_and_inertiaDeg_eq hp hp1 hφ hχ hdeg hinj hgen W
  obtain ⟨c, hc⟩ := exists_valuation_eq_norm he f
  refine ⟨c, ?_⟩
  rw [← restrictExt_apply hφ hχ, hc, vE, comap_apply, NormedField.valuation_apply,
    nnnorm_map hφ]

/-- **Linear disjointness over `E`**: the residues over `E` at `W` are linearly disjoint from `𝓀`
over `κ_E`. -/
theorem linDisj_resE (W : Ext C F') :
    letI := kEAlgebra φ
    ConstantDescent.LinDisj (kE φ) 𝓀 (resE χ W) := by
  letI := kEAlgebra φ
  intro m β z hβ hz hsum
  choose mm hmm using fun l ↦ (mem_resE_iff hφ hχ W (z l)).mp (hz l)
  obtain ⟨-, hf⟩ := ramificationIdx_eq_one_and_inertiaDeg_eq hp hp1 hφ hχ hdeg hinj hgen W
  haveI := finite_residueField (v := gauss1 E) (w := (restrictExt hφ hχ W).1)
  have hgen' : IntermediateField.adjoin 𝓀 (Set.range (ιM hφ hχ W)) = ⊤ := by
    rw [← hgen W]
    congr 1
    ext z
    rw [Set.mem_range, SetLike.mem_coe, mem_resE_iff hφ hχ]
  have hβ' : ∀ a : Fin m → ResidueField
      (Valuation.valuationSubring (NormedField.valuation (K := E))),
      ∑ l, ψ hφ (a l) * β l = 0 → a = 0 := by
    intro a ha
    have h0 := Fintype.linearIndependent_iff.mp hβ (fun l ↦ τ hφ (a l)) (by
      simp only [Algebra.smul_def]
      rw [← ha]
      exact Finset.sum_congr rfl fun l _ ↦ by rw [← kE_τ hφ]; rfl)
    funext l
    exact (map_eq_zero_iff _ (RingHom.injective _)).mp (h0 l)
  have hx₀ : IntermediateField.adjoin
      (ResidueField (Valuation.valuationSubring (NormedField.valuation (K := E)))) {xbar₀} = ⊤ :=
    adjoin_residue_gaussGen_eq_top (v := NormedField.valuation (K := E)) (a := 0) (r := 1) _
  have hx₁ : Transcendental 𝓀 (ιK hφ xbar₀) := by
    rw [ιK_xbar]
    exact transcendental_residue_gaussGen (v := NormedField.valuation (K := C)) (a := 0)
      (r := 1) _
  have hm := eq_zero_of_finrank_eq (k := 𝓀) (ιK hφ) (ιM hφ hχ W) (ιM_algebraMap hφ hχ W) hgen'
    hf.symm β (fun c hc ↦ eq_zero_of_linearIndependent (ψ hφ) (ιK hφ) (ιK_algebraMap hφ) hx₀ hx₁
      β hβ' c hc) mm (by rw [← hsum]; exact Finset.sum_congr rfl fun l _ ↦ by rw [hmm])
  intro l
  rw [← hmm l, hm, Pi.zero_apply, map_zero]

end Main

end DVRDescent

end SemistableReduction
