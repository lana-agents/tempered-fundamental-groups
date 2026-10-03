/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DiscCount
import TemperedFundamentalGroups.SemistableReduction.GaussLimit

/-!
# Splitting at a type-4 point

Blueprint §9.10, layer L2 (B3, B4).

* `LocalGlobal.exists_approx_idempotent`: for a factor `g`, some `x ∈ F'` is close to `1` in
  `K[X]/(g)` and close to `0` in all other `K[X]/(h)` (density of `F'` in `∏_h K[X]/(h)`,
  approximating the Chinese remainder idempotent of `g`);
* `LocalGlobal.norm_coeff_normPoly_le_one`: an element of value `≤ 1` at all extensions has
  characteristic polynomial with coefficients of norm `≤ 1` (product of the local ones).

Type-4 points (`IsTypeFour ξ`: a real valuation of `C(x)` extending the norm of the algebraically
closed `C` whose radius `ξ(x - a)` has no minimum, S8.0). For `b` deeper than `a`
(`ξ(x - b) < ξ(x - a)`), `ξ` lies in the open disc `|x - b| < |a - b|` (`isDiscVal`), the
residue class of the Gauss point `w_{a, ξ(x - a)}` containing `ξ`.

* `exists_nnnorm_eq`: values of polynomials at `ξ` are norms of elements of `C`;
  `gaussRat_eq_of_le`: Gauss valuations depend only on the closed disc;
  `algebraMap_mem_discRing_of_le`: polynomials of Gauss value `≤ 1` lie in the disc chart;
* **`exists_center_ne` (B3)**: two distinct extensions of `ξ` have distinct centres on the
  integral closure of the disc chart for all sufficiently small discs around `ξ` (idempotent
  approximation, a normalized polynomial multiple integral over `C[x]`, and S8.0
  `exists_forall_eq_gaussRat` for its characteristic polynomial);
* **`exists_center_eq`, `exists_center_injective` (B4)**: for all sufficiently small discs the
  centre map from the (finitely many, `finite_extensions`) extensions of `ξ` to the points over
  the residue point is bijective; by `DiscCount.discDegree_eq`, the disc degree of each point is
  then the local degree of the unique extension of `ξ` centred there. For `F'` Galois, the
  stabilizer of such a point is the decomposition group of that extension, a `p`-group
  (`GaloisReduction.isPGroup_decompositionGroup`).
-/

open Polynomial NNReal IntermediateField

namespace SemistableReduction

namespace LocalGlobal

open TubeCount

variable {F K F' : Type*} [NormedField F] [IsUltrametricDist F]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K]
  [Field F'] [Algebra F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
/-- The Chinese remainder idempotent of a factor `g`: a polynomial that is `1` at the root of `g`
and `0` at the roots of the other factors. -/
lemma exists_idempotent (g : Factor F K F') :
    ∃ t : K[X], aeval (root g.1) t = 1 ∧ ∀ h : Factor F K F', h ≠ g → aeval (root h.1) t = 0 := by
  classical
  set Pg := ∏ h ∈ (factors F K F').erase g.1, h
  have hcop : IsCoprime g.1 Pg := IsCoprime.prod_right fun h hh ↦
    isCoprime_of_mem_factors g.2 (Finset.mem_of_mem_erase hh) (Finset.ne_of_mem_erase hh).symm
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨v * Pg, ?_, fun h hne ↦ ?_⟩
  · have := congrArg (aeval (root g.1)) huv
    rwa [map_add, map_mul, map_mul, aeval_root, mul_zero, zero_add, map_one, ← map_mul] at this
  · have hmem : h.1 ∈ (factors F K F').erase g.1 :=
      Finset.mem_erase.2 ⟨fun e ↦ hne (Subtype.ext e), h.2⟩
    rw [map_mul, show Pg = h.1 * ∏ k ∈ ((factors F K F').erase g.1).erase h.1, k from
      (Finset.mul_prod_erase _ _ hmem).symm, map_mul, aeval_root, zero_mul, mul_zero]

omit [IsUltrametricDist F] in
/-- If `y` has value `≤ 1` at every extension, its characteristic polynomial has coefficients of
norm `≤ 1`. -/
theorem norm_coeff_normPoly_le_one [Infinite F] {y : F'}
    (hy : ∀ g : Factor F K F', ‖toLocal g y‖ ≤ 1) (i : ℕ) : ‖(normPoly F y).coeff i‖ ≤ 1 := by
  classical
  have hres := IsResOrder.prod (Finset.univ : Finset (Factor F K F'))
    (fun g ↦ normPoly K (toLocal g y)) _ fun g _ ↦ isResOrder_normPoly g.1 _ (hy g)
  rw [← normPoly_map_eq_prod] at hres
  have := hres.1 i
  rwa [coeff_map, norm_algebraMap'] at this

variable [hd : Fact (DenseRange (algebraMap F K))]

omit [IsUltrametricDist F] in
/-- **Idempotent approximation.** For a factor `g` there is `x ∈ F'` with
`‖toLocal g x - 1‖ < 1` and `‖toLocal h x‖ < 1` for every other factor `h`. -/
theorem exists_approx_idempotent (g : Factor F K F') :
    ∃ x : F', ‖toLocal g x - 1‖ < 1 ∧ ∀ h : Factor F K F', h ≠ g → ‖toLocal h x‖ < 1 := by
  classical
  obtain ⟨t, htg, hth⟩ := exists_idempotent g
  let Φ : (Fin (minpolyK F K F').natDegree → K) → ∀ h : Factor F K F', Local K h.1 :=
    fun c h ↦ sumPow (F := F) (K := K) (F' := F') (root h.1) c
  have hΦ : Continuous Φ := continuous_pi fun h ↦ continuous_sumPow _
  let target : ∀ h : Factor F K F', Local K h.1 := fun h ↦ if h = g then 1 else 0
  let U : Set (∀ h : Factor F K F', Local K h.1) :=
    Set.pi Set.univ fun h ↦ Metric.ball (target h) 1
  have hU : IsOpen (Φ ⁻¹' U) :=
    (isOpen_set_pi Set.finite_univ fun h _ ↦ Metric.isOpen_ball).preimage hΦ
  set c₀ := fun n : Fin (minpolyK F K F').natDegree ↦ (t %ₘ minpolyK F K F').coeff n
  have hc₀ : Φ c₀ ∈ U := by
    intro h _
    simp only [Φ, c₀, sumPow_modByMonic (aeval_root_minpolyK h)]
    by_cases hh : h = g
    · subst hh
      simp only [target, if_pos rfl, htg]
      exact Metric.mem_ball_self one_pos
    · simp only [target, if_neg hh, hth h hh]
      exact Metric.mem_ball_self one_pos
  obtain ⟨a, hmem⟩ := denseRange_piMap.exists_mem_open hU ⟨c₀, hc₀⟩
  refine ⟨∑ n, a n • (pb F F').gen ^ (n : ℕ), ?_, fun h hne ↦ ?_⟩
  · have := hmem g (Set.mem_univ _)
    simp only [target, if_pos rfl, Metric.mem_ball, dist_eq_norm] at this
    rw [toLocal_sum]
    exact this
  · have := hmem h (Set.mem_univ _)
    simp only [target, if_neg hne, Metric.mem_ball, dist_zero_right] at this
    rw [toLocal_sum]
    exact this

end LocalGlobal

/-! ### Type-4 points and their discs -/

namespace Splitting

open GaussLimit DiscCount LocalGlobal TubeCount DenseCompletion

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {ξ : Valuation (RatFunc C) ℝ≥0}

/-- A valuation of `C(x)` extending the norm of `C` without minimal radius: a type-4 point
(`GaussLimit.forall_ne_gaussRat`). -/
structure IsTypeFour (ξ : Valuation (RatFunc C) ℝ≥0) : Prop where
  map_C : ∀ c : C, ξ (algebraMap C (RatFunc C) c) = NormedField.valuation c
  no_min : ∀ a : C, ∃ b : C, radius ξ b < radius ξ a

omit [IsAlgClosed C] in
/-- Past a deeper centre `b`, the radius at `a` is a distance: `ξ(x - a) = |a - b|`. -/
lemma radius_eq_nnnorm (hξ : IsTypeFour ξ) {a b : C} (h : radius ξ b < radius ξ a) :
    radius ξ a = ‖b - a‖₊ := by
  have e := radius_eq_max hξ.map_C h.le
  rcases le_total (NormedField.valuation (b - a)) (radius ξ b) with hle | hle
  · rw [max_eq_right hle] at e
    exact absurd e (ne_of_gt h)
  · rw [max_eq_left hle] at e
    exact e

omit [IsAlgClosed C] in
lemma sub_ne_zero_of_radius_lt (hξ : IsTypeFour ξ) {a b : C} (h : radius ξ b < radius ξ a) :
    a - b ≠ 0 := by
  intro h0
  have := radius_eq_nnnorm hξ h
  rw [← neg_sub, h0, neg_zero, nnnorm_zero] at this
  exact radius_ne_zero ξ a this

omit [IsAlgClosed C] in
/-- **A type-4 point lies in the open disc `|x - b| < |a - b|`** whenever `b` is deeper than
`a`. -/
lemma isDiscVal (hξ : IsTypeFour ξ) {a b : C} (h : radius ξ b < radius ξ a) :
    IsDiscVal b (a - b) ξ := by
  refine ⟨fun c ↦ by rw [hξ.map_C]; rfl, ?_⟩
  have hc := sub_ne_zero_of_radius_lt hξ h
  rw [gaussCoord, gaussLin, map_mul, ratFunc_algebraMap_C, map_mul, hξ.map_C]
  change NormedField.valuation (a - b)⁻¹ * radius ξ b < 1
  rw [map_inv₀, NormedField.valuation_apply, ← nnnorm_neg, neg_sub, ← radius_eq_nnnorm hξ h,
    inv_mul_lt_one₀ ((zero_le).lt_of_ne (radius_ne_zero ξ a).symm)]
  exact h

/-- Gauss valuations only depend on the closed disc. -/
lemma gaussRat_eq_of_le {a b : C} {r : ℝ≥0ˣ} (h : NormedField.valuation (a - b) ≤ r) :
    gaussRat (NormedField.valuation (K := C)) a r =
      gaussRat (NormedField.valuation (K := C)) b r := by
  refine valuation_ratFunc_ext_of_linear (fun e ↦ by rw [gaussRat_algebraMap_C,
    gaussRat_algebraMap_C]) fun e ↦ ?_
  rw [gaussRat_algebraMap, gaussRat_algebraMap, gauss_X_sub_C, gauss_X_sub_C]
  set v := NormedField.valuation (K := C)
  have hsplit : b - e = (a - e) - (a - b) := by ring
  rcases le_or_gt (v (a - e)) r with hle | hlt
  · rw [max_eq_right hle, max_eq_right]
    rw [hsplit]
    exact (Valuation.map_sub _ _ _).trans (max_le hle h)
  · rw [max_eq_left hlt.le, max_eq_left, hsplit, Valuation.map_sub_eq_of_lt_left _
      (lt_of_le_of_lt h hlt)]
    rw [hsplit, Valuation.map_sub_eq_of_lt_left _ (lt_of_le_of_lt h hlt)]
    exact hlt.le

omit [IsAlgClosed C] in
/-- A polynomial of Gauss value `≤ 1` at `w_{b,|c|}` lies in the disc chart `O_C[(x - b)/c]`. -/
lemma algebraMap_mem_discRing_of_le {b c : C} (hc : c ≠ 0) {p : C[X]}
    (hp : gaussRat (NormedField.valuation (K := C)) b (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc))
      (algebraMap C[X] (RatFunc C) p) ≤ 1) :
    algebraMap C[X] (RatFunc C) p ∈ discRing b c := by
  have hcv : NormedField.valuation c = ((Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc) : ℝ≥0ˣ) : ℝ≥0) :=
    rfl
  have heval : aeval (gaussCoord b c) (p.comp (Polynomial.C c * X + Polynomial.C b)) =
      algebraMap C[X] (RatFunc C) p := by
    rw [aeval_comp, map_add, map_mul, aeval_C, aeval_C, aeval_X, ← X_eq_gaussCoord hc,
      RatFunc.aeval_X_left_eq_algebraMap]
  refine mem_polyChart_iff.2 ⟨_, ?_, heval⟩
  rw [← gaussRat_aeval_gaussLin hcv]
  change gaussRat _ b _ (aeval (gaussCoord b c) _) ≤ 1
  rwa [heval]

/-- At a type-4 point, the value of a nonzero polynomial is the norm of an element of `C`. -/
lemma exists_nnnorm_eq (hξ : IsTypeFour ξ) (p : C[X]) :
    ∃ γ : C, ‖γ‖₊ = ξ (algebraMap C[X] (RatFunc C) p) := by
  choose β hβ using hξ.no_min
  refine ⟨p.leadingCoeff * (p.roots.map fun α ↦ β α - α).prod, ?_⟩
  conv_rhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := p))]
  rw [map_mul, map_mul, ratFunc_algebraMap_C, hξ.map_C, nnnorm_mul, map_multiset_prod,
    map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  · change (nnnormHom : C →*₀ ℝ≥0) _ = _
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun α _ ↦ (radius_eq_nnnorm hξ (hβ α)).symm

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra.IsSeparable (RatFunc C) F'] in
/-- An extension of a type-4 point restricts to a disc valuation of every disc around it. -/
lemma isDiscVal_comap (hξ : IsTypeFour ξ) {ξ' : Valuation F' ℝ≥0}
    (h' : ξ'.comap (algebraMap (RatFunc C) F') = ξ) {a b : C} (h : radius ξ b < radius ξ a) :
    IsDiscVal b (a - b) (ξ'.comap (algebraMap (RatFunc C) F')) :=
  h' ▸ isDiscVal hξ h

instance (ν : DiscVal (C := C) a c) :
    Fact (DenseRange (@algebraMap (DiscField ν) (UniformSpace.Completion (DiscField ν)) _ _
      NormedAlgebra.toAlgebra)) :=
  ⟨UniformSpace.Completion.denseRange_coe⟩

/-- **B3: separation near a type-4 point.** Two distinct extensions `ξ₁ ≠ ξ₂` of a type-4 point
`ξ` have distinct centres on the integral closure of the disc chart of every sufficiently small
disc around `ξ`: there is `a₀` such that for `ξ(x - a) ≤ ξ(x - a₀)` and `b` deeper than `a`, the
centres of `ξ₁, ξ₂` on `R' = O_C[(x - b)/(a - b)]^{int}` differ.

Proof: an `x ∈ F'` close to the idempotent of `ξ₂` in the local factors
(`exists_approx_idempotent`), made integral over `C[x]` by a polynomial multiple normalized to
`ξ`-value `1` (`exists_nnnorm_eq`); its characteristic polynomial has polynomial coefficients of
`ξ`-value `≤ 1` (`norm_coeff_normPoly_le_one`), which by S8.0 (`exists_forall_eq_gaussRat`) are
integral over the disc chart for every small enough disc. -/
theorem exists_center_ne (hξ : IsTypeFour ξ) {ξ₁ ξ₂ : Valuation F' ℝ≥0}
    (h₁ : ξ₁.comap (algebraMap (RatFunc C) F') = ξ) (h₂ : ξ₂.comap (algebraMap (RatFunc C) F') = ξ)
    (hne : ξ₁ ≠ ξ₂) :
    ∃ a₀ : C, ∀ a b : C, radius ξ a ≤ radius ξ a₀ → ∀ hb : radius ξ b < radius ξ a,
      center (isDiscVal_comap hξ h₁ hb) ≠ center (isDiscVal_comap hξ h₂ hb) := by
  classical
  -- the normed field `(C(x), ξ)`
  obtain ⟨b₁, hb₁⟩ := hξ.no_min 0
  obtain ⟨D₁, hD₁⟩ : ∃ D : DiscVal b₁ (0 - b₁), D.val = ξ := ⟨⟨ξ, isDiscVal hξ hb₁⟩, rfl⟩
  have hext (ξ' : Valuation F' ℝ≥0) (h' : ξ'.comap (algebraMap (RatFunc C) F') = ξ) :
      ξ'.comap (algebraMap (DiscField D₁) F') = NormedField.valuation (K := DiscField D₁) := by
    refine Valuation.ext fun y ↦ ?_
    have := congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v y.ofAbs) h'
    simp only [Valuation.comap_apply] at this
    rw [Valuation.comap_apply, valuation_withAbs]
    exact this.trans (congrArg (fun v ↦ v y.ofAbs) hD₁.symm)
  obtain ⟨g₁, hg₁⟩ :=
    exists_eq_extValuation (K := UniformSpace.Completion (DiscField D₁)) ⟨ξ₁, hext ξ₁ h₁⟩
  obtain ⟨g₂, hg₂⟩ :=
    exists_eq_extValuation (K := UniformSpace.Completion (DiscField D₁)) ⟨ξ₂, hext ξ₂ h₂⟩
  have hg : g₁ ≠ g₂ := fun h ↦ hne (by
    have := congrArg extValuation h
    rw [hg₁, hg₂] at this
    exact this)
  -- the restriction of every extension to `C(x)` is `ξ`
  have hres (g : Factor (DiscField D₁) (UniformSpace.Completion (DiscField D₁)) F')
      (f : RatFunc C) :
      extValuation g (algebraMap (RatFunc C) F' f) = ξ f := by
    have := congrArg (fun v : Valuation (DiscField D₁) ℝ≥0 ↦ v (WithAbs.toAbs _ f))
      (extValuation_comap g)
    simp only [Valuation.comap_apply, valuation_withAbs] at this
    rw [← hD₁]
    exact this
  -- a separating element
  obtain ⟨x, hx2, hxo⟩ := exists_approx_idempotent (F := DiscField D₁)
    (K := UniformSpace.Completion (DiscField D₁)) (F' := F') g₂
  have hxle : ∀ g : Factor (DiscField D₁) (UniformSpace.Completion (DiscField D₁)) F',
      ‖toLocal g x‖ ≤ 1 := by
    intro g
    by_cases h : g = g₂
    · subst h
      exact ((norm_eq_of_norm_sub_lt (by rwa [norm_one])).trans norm_one).le
    · exact (hxo g h).le
  have hx₁ : extValuation g₁ x < 1 := by
    have := hxo g₁ hg
    rw [extValuation_apply, ← NNReal.coe_lt_one, coe_nnnorm]
    exact this
  have hx₂ : extValuation g₂ x = 1 := by
    rw [extValuation_apply]
    exact NNReal.eq ((norm_eq_of_norm_sub_lt (by rwa [norm_one])).trans norm_one)
  -- make it integral over `C[x]`
  letI : Algebra C[X] F' :=
    ((algebraMap (RatFunc C) F').comp (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := IsLocalization.isAlgebraic (RatFunc C) (nonZeroDivisors C[X])
  haveI := Algebra.IsAlgebraic.trans C[X] (RatFunc C) F'
  obtain ⟨d, hd0, hdint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := C[X]) x).exists_integral_multiple
  obtain ⟨γ, hγ⟩ := exists_nnnorm_eq hξ d
  have hξd : ξ (algebraMap C[X] (RatFunc C) d) ≠ 0 := by
    rw [Ne, map_eq_zero, IsFractionRing.to_map_eq_zero_iff]
    exact hd0
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero] at hγ
    exact hξd hγ.symm
  set lam : C[X] := Polynomial.C γ⁻¹ * d
  set z : F' := lam • x
  have hzint : IsIntegral C[X] z := by
    change IsIntegral C[X] ((Polynomial.C γ⁻¹ * d) • x)
    rw [mul_smul]
    exact hdint.smul _
  have hlam : ξ (algebraMap C[X] (RatFunc C) lam) = 1 := by
    rw [map_mul, map_mul, ratFunc_algebraMap_C, hξ.map_C, ← hγ]
    change ‖γ⁻¹‖₊ * ‖γ‖₊ = 1
    rw [nnnorm_inv, inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hγ0)]
  have hz (g : Factor (DiscField D₁) (UniformSpace.Completion (DiscField D₁)) F') :
      extValuation g z = extValuation g x := by
    change extValuation g (lam • x) = _
    rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply C[X] (RatFunc C) F', hres, hlam,
      one_mul]
  -- its characteristic polynomial over `C[x]`
  set P₀ : C[X][X] := minpoly C[X] z ^ Module.finrank (RatFunc C)⟮z⟯ F'
  have hP₀ : P₀.map (algebraMap C[X] (RatFunc C)) = normPoly (RatFunc C) z := by
    rw [Polynomial.map_pow, normPoly,
      minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc C) hzint]
  have hP₀m : P₀.Monic := (minpoly.monic hzint).pow _
  have hcoeff (i : ℕ) : ξ (algebraMap C[X] (RatFunc C) (P₀.coeff i)) ≤ 1 := by
    haveI : Infinite (DiscField D₁) :=
      Infinite.of_injective _ (algebraMap C (DiscField D₁)).injective
    haveI : Infinite (RatFunc C) :=
      Infinite.of_injective _ (algebraMap C (RatFunc C)).injective
    have hle := norm_coeff_normPoly_le_one (F := DiscField D₁)
      (K := UniformSpace.Completion (DiscField D₁)) (F' := F') (y := z)
      (fun g ↦ by
        have h1 : ‖toLocal g z‖₊ = ‖toLocal g x‖₊ := by
          rw [← extValuation_apply, ← extValuation_apply, hz]
        rw [← coe_nnnorm, h1, coe_nnnorm]
        exact hxle g) i
    have hmap := normPoly_map_ringEquiv (WithAbs.equiv D₁.val.toAbsoluteValue).symm
      (F₂ := DiscField D₁) (by ext; rfl) z
    rw [← hmap, coeff_map, ← hP₀, coeff_map, WithAbs.norm_eq_apply_ofAbs] at hle
    rw [← hD₁]
    exact_mod_cast hle
  -- thresholds from S8.0
  choose A hA using fun i : ℕ ↦ exists_forall_eq_gaussRat hξ.map_C (P₀.coeff i)
  obtain ⟨i₀, -, hi₀⟩ := (Finset.range (P₀.natDegree + 1)).exists_min_image
    (fun i ↦ radius ξ (A i)) ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
  refine ⟨A i₀, fun a b ha hb heq ↦ ?_⟩
  have hab := sub_ne_zero_of_radius_lt hξ hb
  -- all coefficients lie in the disc chart
  have hmem (i : ℕ) : algebraMap C[X] (RatFunc C) (P₀.coeff i) ∈ discRing b (a - b) := by
    by_cases hi : i ≤ P₀.natDegree
    · refine algebraMap_mem_discRing_of_le hab ?_
      have hrad : radius ξ a ≤ radius ξ (A i) :=
        ha.trans (hi₀ i (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
      have hu : radiusUnit ξ a = Units.mk0 ‖a - b‖₊ (nnnorm_ne_zero_iff.2 hab) := by
        ext
        rw [val_radiusUnit, Units.val_mk0, radius_eq_nnnorm hξ hb, ← nnnorm_neg, neg_sub]
      rw [← gaussRat_eq_of_le (a := a) (b := b) (r := Units.mk0 ‖a - b‖₊ _) le_rfl, ← hu,
        ← hA i a hrad]
      exact hcoeff i
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero]
      exact Subring.zero_mem _
  -- `z` is integral over the disc chart
  have hc : (↑(P₀.map (algebraMap C[X] (RatFunc C))).coeffs : Set (RatFunc C)) ⊆
      discRing b (a - b) := by
    intro f hf
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hf
    rw [coeff_map]
    exact hmem n
  have hzD : IsIntegral (discRing b (a - b)) z := by
    refine ⟨(P₀.map (algebraMap C[X] (RatFunc C))).toSubring _ hc,
      (monic_toSubring _ _ _).2 (hP₀m.map _), ?_⟩
    rw [show algebraMap (discRing b (a - b)) F' =
      (algebraMap (RatFunc C) F').comp (discRing b (a - b)).subtype from rfl, ← eval₂_map,
      map_toSubring, ← aeval_def, hP₀, normPoly, map_pow]
    change aeval z (minpoly (RatFunc C) z) ^ _ = 0
    rw [minpoly.aeval, zero_pow Module.finrank_pos.ne']
  -- the centres differ
  have hz₁ : (⟨z, hzD⟩ : DRint b (a - b) F') ∈ center (isDiscVal_comap hξ h₁ hb) := by
    rw [mem_center_iff]
    change ξ₁ z < 1
    rw [show ξ₁ = extValuation g₁ from hg₁.symm, hz]
    exact hx₁
  have hz₂ : (⟨z, hzD⟩ : DRint b (a - b) F') ∉ center (isDiscVal_comap hξ h₂ hb) := by
    rw [mem_center_iff, not_lt]
    change 1 ≤ ξ₂ z
    rw [show ξ₂ = extValuation g₂ from hg₂.symm, hz, hx₂]
  exact hz₂ (heq ▸ hz₁)

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- The extension of a disc valuation `ν` attached to a factor restricts to `ν`. -/
lemma comap_extValuation {a c : C} (ν : DiscVal a c)
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F') :
    (extValuation g).comap (algebraMap (RatFunc C) F') = ν.val := by
  refine Valuation.ext fun f ↦ ?_
  have := congrArg (fun v : Valuation (DiscField ν) ℝ≥0 ↦ v (WithAbs.toAbs _ f))
    (extValuation_comap g)
  simp only [Valuation.comap_apply, valuation_withAbs] at this
  rw [Valuation.comap_apply]
  exact this

omit [IsAlgClosed C] in
/-- **B4, surjectivity.** Every point over the residue point of a disc around a type-4 point `ξ`
is the centre of an extension of `ξ` (B4a at `ν = ξ`). -/
theorem exists_center_eq (hξ : IsTypeFour ξ) {a b : C} (hb : radius ξ b < radius ξ a)
    (P' : Ideal (DRint b (a - b) F')) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing b (a - b)) (DRint b (a - b) F')) = discIdeal b (a - b)) :
    ∃ (ξ' : Valuation F' ℝ≥0) (h' : ξ'.comap (algebraMap (RatFunc C) F') = ξ),
      center (isDiscVal_comap hξ h' hb) = P' := by
  classical
  obtain ⟨ν, hν⟩ : ∃ ν : DiscVal b (a - b), ν.val = ξ := ⟨⟨ξ, isDiscVal hξ hb⟩, rfl⟩
  have hpos := discDegree_pos (sub_ne_zero_of_radius_lt hξ hb) ν P' hP'
  rw [discDegree, Finset.sum_pos_iff] at hpos
  obtain ⟨g, hg, -⟩ := hpos
  exact ⟨extValuation g, (comap_extValuation ν g).trans hν, (Finset.mem_filter.1 hg).2⟩

omit [IsAlgClosed C] in
/-- The extensions of a type-4 point form a finite set. -/
lemma finite_extensions (hξ : IsTypeFour ξ) :
    Finite {ξ' : Valuation F' ℝ≥0 // ξ'.comap (algebraMap (RatFunc C) F') = ξ} := by
  obtain ⟨b₁, hb₁⟩ := hξ.no_min 0
  obtain ⟨D₁, hD₁⟩ : ∃ D : DiscVal b₁ (0 - b₁), D.val = ξ := ⟨⟨ξ, isDiscVal hξ hb₁⟩, rfl⟩
  have hext (ξ' : Valuation F' ℝ≥0) (h' : ξ'.comap (algebraMap (RatFunc C) F') = ξ) :
      ξ'.comap (algebraMap (DiscField D₁) F') = NormedField.valuation (K := DiscField D₁) := by
    refine Valuation.ext fun y ↦ ?_
    have := congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v y.ofAbs) h'
    simp only [Valuation.comap_apply] at this
    rw [Valuation.comap_apply, valuation_withAbs]
    exact this.trans (congrArg (fun v ↦ v y.ofAbs) hD₁.symm)
  have hfin := finite_extension (UniformSpace.Completion (DiscField D₁)) (F := DiscField D₁)
    (F' := F')
  refine @Finite.of_injective _ (Extension (DiscField D₁) F') hfin
    (fun ξ' ↦ ⟨ξ'.1, hext ξ'.1 ξ'.2⟩) fun x y h ↦ Subtype.ext ?_
  have := congrArg Subtype.val h
  exact this

/-- **B4, injectivity (splitting).** For all sufficiently small discs around a type-4 point `ξ`,
distinct extensions of `ξ` have distinct centres; together with `exists_center_eq`, the
extensions of `ξ` are in bijection with the points over the residue point, and the disc degree
of each point is the local degree of the extension centred there. -/
theorem exists_center_injective (hξ : IsTypeFour ξ) :
    ∃ a₀ : C, ∀ a b : C, radius ξ a ≤ radius ξ a₀ → ∀ hb : radius ξ b < radius ξ a,
      ∀ (ξ₁ ξ₂ : Valuation F' ℝ≥0) (h₁ : ξ₁.comap (algebraMap (RatFunc C) F') = ξ)
        (h₂ : ξ₂.comap (algebraMap (RatFunc C) F') = ξ),
        center (isDiscVal_comap hξ h₁ hb) = center (isDiscVal_comap hξ h₂ hb) → ξ₁ = ξ₂ := by
  classical
  set E := {ξ' : Valuation F' ℝ≥0 // ξ'.comap (algebraMap (RatFunc C) F') = ξ}
  haveI := finite_extensions (F' := F') hξ
  haveI : Fintype E := Fintype.ofFinite E
  have hpair (p : E × E) : ∃ a₀ : C, p.1 ≠ p.2 → ∀ a b : C, radius ξ a ≤ radius ξ a₀ →
      ∀ hb : radius ξ b < radius ξ a,
        center (isDiscVal_comap hξ p.1.2 hb) ≠ center (isDiscVal_comap hξ p.2.2 hb) := by
    by_cases h : p.1 = p.2
    · exact ⟨0, fun hne ↦ absurd h hne⟩
    · obtain ⟨a₀, ha₀⟩ := exists_center_ne hξ p.1.2 p.2.2 fun e ↦ h (Subtype.ext e)
      exact ⟨a₀, fun _ ↦ ha₀⟩
  choose A hA using hpair
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : C, ∀ p : E × E, radius ξ a₀ ≤ radius ξ (A p) := by
    rcases isEmpty_or_nonempty (E × E) with hE | hE
    · exact ⟨0, fun p ↦ hE.elim p⟩
    · obtain ⟨p₀, -, hp₀⟩ := Finset.univ.exists_min_image (fun p : E × E ↦ radius ξ (A p))
        Finset.univ_nonempty
      exact ⟨A p₀, fun p ↦ hp₀ p (Finset.mem_univ p)⟩
  refine ⟨a₀, fun a b ha hb ξ₁ ξ₂ h₁ h₂ heq ↦ ?_⟩
  by_contra hne
  exact hA (⟨ξ₁, h₁⟩, ⟨ξ₂, h₂⟩) (fun e ↦ hne (congrArg Subtype.val e)) a b
    (ha.trans (ha₀ _)) hb heq

end Splitting

end SemistableReduction
