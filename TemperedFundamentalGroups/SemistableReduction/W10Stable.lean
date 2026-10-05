/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussDescent
import TemperedFundamentalGroups.SemistableReduction.ProjModel

/-!
# Stability of normalized models under semilinear isomorphisms

Blueprint §9.7a (W10 assembly, the action on the models).

* **(a)** `points_comap_normalization`: let `φ : F₁' ≃+* F₂'` lie over `ψ : F ≃+* F`, and let
  `M₁, M₂` be models of `F` such that the `ψ`-preimage of every chart of `M₂` is locally (at every
  valuation ring containing it) equivalent to a chart of `M₁` (`LocallyCovers`). Then `φ` pulls
  back points of the normalization of `M₂` in `F₂'` to points of the normalization of `M₁` in
  `F₁'`.
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel

namespace W10Stable

section LocalAt

variable {L : Type*} [Field L]

/-- Mutually locally contained subrings have the same local ring. -/
lemma localAt_eq_of_le_localAt {A B : Subring L} {W : ValuationSubring L}
    (hAB : A ≤ localAt B W) (hBA : B ≤ localAt A W) : localAt A W = localAt B W := by
  have hA : localAt (localAt A W) W = localAt A W := localAt_eq_of_le le_localAt le_rfl
  have hB : localAt (localAt B W) W = localAt B W := localAt_eq_of_le le_localAt le_rfl
  refine le_antisymm ?_ ?_
  · rw [← hB]; exact localAt_mono hAB
  · rw [← hA]; exact localAt_mono hBA

variable {L' : Type*} [Field L']

/-- Local rings are transported by ring isomorphisms. -/
lemma comap_localAt (φ : L' ≃+* L) (A : Subring L) (W : ValuationSubring L) :
    (localAt A W).comap (φ : L' →+* L) = localAt (A.comap (φ : L' →+* L)) (W.comap φ) := by
  have hv (t : L') : (W.comap (φ : L' →+* L)).valuation t = 1 ↔ W.valuation (φ t) = 1 := by
    rw [valuation_eq_one_iff_mem_and_inv_mem,
      valuation_eq_one_iff_mem_and_inv_mem, ValuationSubring.mem_comap,
      ValuationSubring.mem_comap, map_inv₀, Ne, Ne, map_eq_zero_iff _ φ.injective]
    rfl
  ext x
  simp only [Subring.mem_comap, mem_localAt]
  constructor
  · rintro ⟨s, hs, hsW, hxs⟩
    refine ⟨φ.symm s, by simpa using hs, (hv _).2 (by simpa using hsW), ?_⟩
    simpa [map_mul] using hxs
  · rintro ⟨t, ht, htW, hxt⟩
    exact ⟨φ t, ht, (hv t).1 htW, by simpa [map_mul] using hxt⟩

/-- Integral closures are transported by ring isomorphisms. -/
lemma comap_integralClosure (φ : L' ≃+* L) (S : Subring L) :
    (integralClosure S L).toSubring.comap (φ : L' →+* L) =
      (integralClosure (S.comap (φ : L' →+* L)) L').toSubring := by
  ext x
  simp only [Subring.mem_comap, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  constructor
  · intro hx
    have := IsIntegral.map_of_comp_eq ((φ.symm : L →+* L').restrict S (S.comap (φ : L' →+* L))
      fun y hy ↦ by simpa using hy) (φ.symm : L →+* L') (RingHom.ext fun _ ↦ rfl) hx
    simpa using this
  · intro hx
    exact IsIntegral.map_of_comp_eq ((φ : L' →+* L).restrict (S.comap (φ : L' →+* L)) S
      fun _ hy ↦ hy) (φ : L' →+* L) (RingHom.ext fun _ ↦ rfl) hx

end LocalAt

section Normalization

variable {F F₁ F₂ : Type*} [Field F] [Field F₁] [Field F₂] [Algebra F F₁] [Algebra F F₂]
  (ψ : F ≃+* F) (φ : F₁ ≃+* F₂) (hφ : ∀ x, φ (algebraMap F F₁ x) = algebraMap F F₂ (ψ x))

include hφ in
lemma comap_map_algebraMap (A : Subring F) :
    (A.map (algebraMap F F₂)).comap (φ : F₁ →+* F₂) =
      (A.comap (ψ : F →+* F)).map (algebraMap F F₁) := by
  ext y
  simp only [Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨a, ha, hay⟩
    refine ⟨ψ.symm a, by simpa using ha, φ.injective ?_⟩
    rw [hφ, RingEquiv.apply_symm_apply, hay]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨ψ b, hb, (hφ b).symm⟩

include hφ in
/-- Integral closures of charts are transported by `φ`. -/
lemma comap_normChart (A : Subring F) :
    (normChart F₂ A).comap (φ : F₁ →+* F₂) = normChart F₁ (A.comap (ψ : F →+* F)) := by
  rw [normChart, normChart, comap_integralClosure, comap_map_algebraMap ψ φ hφ]

end Normalization

section Points

variable {K F F₁ F₂ : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Algebra K F]
  [Algebra K F₁] [Algebra K F₂] [Algebra F F₁] [Algebra F F₂] [IsScalarTower K F F₁]
  [IsScalarTower K F F₂] {O : ValuationSubring K}

/-- The `ψ`-preimage of every chart of `M₂` is, at every valuation ring containing it, locally
equivalent to a chart of `M₁` contained in it. -/
def LocallyCovers (M₁ M₂ : ZariskiModel (baseRing F O)) (ψ : F ≃+* F) : Prop :=
  ∀ A ∈ M₂.charts, ∀ W : ValuationSubring F, A.comap (ψ : F →+* F) ≤ W.toSubring →
    ∃ A' ∈ M₁.charts, A' ≤ W.toSubring ∧ A' ≤ localAt (A.comap (ψ : F →+* F)) W ∧
      A.comap (ψ : F →+* F) ≤ localAt A' W

omit [Algebra K F₁] [IsScalarTower K F F₁] in
/-- Local containment of charts passes to their integral closures. -/
lemma normChart_le_localAt {A B : Subring F} {W' : ValuationSubring F₁}
    (h : B ≤ localAt A (W'.comap (algebraMap F F₁))) :
    normChart F₁ B ≤ localAt (normChart F₁ A) W' :=
  integralClosure_le_localAt ((subring_map_mono h _).trans (map_localAt_le A W'))

/-- **(a)** `φ` pulls back points of the normalization of `M₂` in `F₂` to points of the
normalization of `M₁` in `F₁`. -/
theorem points_comap_normalization {M₁ M₂ : ZariskiModel (baseRing F O)} (ψ : F ≃+* F)
    (φ : F₁ ≃+* F₂) (hφ : ∀ x, φ (algebraMap F F₁ x) = algebraMap F F₂ (ψ x))
    (h : LocallyCovers M₁ M₂ ψ) :
    ∀ Q ∈ (M₂.normalization F₂).points,
      Q.comap (φ : F₁ →+* F₂) ∈ (M₁.normalization F₁).points := by
  rintro _ ⟨C, hC, W', hCW', rfl⟩
  obtain ⟨A, hA, rfl⟩ := mem_normalization_charts.1 hC
  rw [comap_localAt, comap_normChart ψ φ hφ]
  set W₁ := W'.comap (φ : F₁ →+* F₂)
  have hA1 : normChart F₁ (A.comap (ψ : F →+* F)) ≤ W₁.toSubring := by
    rw [← comap_normChart ψ φ hφ]
    exact fun x hx ↦ hCW' hx
  have hAW := (normChart_le_iff _ _).1 hA1
  obtain ⟨A', hA', hA'W, h1, h2⟩ := h A hA _ hAW
  refine ⟨normChart F₁ A', mem_normalization_charts.2 ⟨A', hA', rfl⟩, W₁,
    (normChart_le_iff _ _).2 hA'W, ?_⟩
  exact localAt_eq_of_le_localAt (normChart_le_localAt h1) (normChart_le_localAt h2)

/-- Every point of a model contains a chart. -/
lemma exists_chart_le_of_mem_points {R : Subring F₁} {M : ZariskiModel R} {Q : Subring F₁}
    (hQ : Q ∈ M.points) : ∃ C ∈ M.charts, C ≤ Q := by
  obtain ⟨C, hC, W, -, rfl⟩ := hQ
  exact ⟨C, hC, le_localAt⟩

/-- **(a)**, in the form "a chart of the source maps into every point of the target". -/
theorem exists_chart_map_le {M₁ M₂ : ZariskiModel (baseRing F O)} (ψ : F ≃+* F)
    (φ : F₁ ≃+* F₂) (hφ : ∀ x, φ (algebraMap F F₁ x) = algebraMap F F₂ (ψ x))
    (h : LocallyCovers M₁ M₂ ψ) {Q : Subring F₂} (hQ : Q ∈ (M₂.normalization F₂).points) :
    ∃ C ∈ (M₁.normalization F₁).charts, ∀ y ∈ C, φ y ∈ Q := by
  obtain ⟨C, hC, hCQ⟩ := exists_chart_le_of_mem_points
    (points_comap_normalization ψ φ hφ h Q hQ)
  exact ⟨C, hC, fun y hy ↦ hCQ hy⟩

end Points

section Line

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

local notation "⟪" k "⟫" => algebraMap K F k

lemma base_mem {b : K} (hb : v b ≤ 1) : ⟪b⟫ ∈ baseRing F v.valuationSubring :=
  algebraMap_mem_baseRing ((Valuation.mem_valuationSubring_iff _ _).2 hb)

lemma polyChart_add {b : K} (hb : v b ≤ 1) (y : F) : polyChart v (y + ⟪b⟫) = polyChart v y := by
  apply le_antisymm
  · exact polyChart_le (baseRing_le_polyChart _)
      (add_mem (self_mem_polyChart y) (baseRing_le_polyChart _ (base_mem hb)))
  · refine polyChart_le (baseRing_le_polyChart _) ?_
    have := sub_mem (self_mem_polyChart (v := v) (y + ⟪b⟫))
      (baseRing_le_polyChart _ (base_mem (F := F) hb))
    simpa using this

/-- Affine changes of coordinate over `O` do not change the chart `O[y]`. -/
lemma polyChart_affine {e b : K} (he : v e = 1) (hb : v b ≤ 1) (y : F) :
    polyChart v (⟪e⟫ * y + ⟪b⟫) = polyChart v y := by
  rw [polyChart_add hb, polyChart_mul_unit he]

lemma inv_chart_le_localAt {e b : K} (he : v e = 1) (hb : v b ≤ 1) {y y' : F}
    (hy' : y' = ⟪e⟫ * y + ⟪b⟫) {W : ValuationSubring F}
    (hbase : baseRing F v.valuationSubring ≤ W.toSubring) (hyW : y ∉ W) (hy'W : y' ∉ W) :
    polyChart v y'⁻¹ ≤ localAt (polyChart v y⁻¹) W := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hy0 : y ≠ 0 := by rintro rfl; exact hyW (zero_mem _)
  have hy'0 : y' ≠ 0 := by rintro rfl; exact hy'W (zero_mem _)
  have hyi : y⁻¹ ∈ W := (W.mem_or_inv_mem y).resolve_left hyW
  have hy'i : y'⁻¹ ∈ W := (W.mem_or_inv_mem y').resolve_left hy'W
  have hei : v e⁻¹ ≤ 1 := by rw [map_inv₀, he, inv_one]
  set s := ⟪e⟫ + ⟪b⟫ * y⁻¹ with hsdef
  have hsP : s ∈ polyChart v y⁻¹ :=
    add_mem (baseRing_le_polyChart _ (base_mem he.le))
      (mul_mem (baseRing_le_polyChart _ (base_mem hb)) (self_mem_polyChart _))
  have hs : s = y' * y⁻¹ := by
    rw [hy', hsdef]
    field_simp
  have hsinv : s⁻¹ = ⟪e⁻¹⟫ * (1 - ⟪b⟫ * y'⁻¹) := by
    rw [hs, mul_inv, inv_inv, map_inv₀]
    have he' : ⟪e⟫ ≠ 0 := by simpa using he0
    have hy : y = ⟪e⟫⁻¹ * (y' - ⟪b⟫) := by rw [hy']; field_simp; ring
    rw [hy]
    field_simp
  have hsv : W.valuation s = 1 := by
    rw [valuation_eq_one_iff_mem_and_inv_mem]
    refine ⟨by rw [hs]; exact mul_ne_zero hy'0 (inv_ne_zero hy0),
      polyChart_le hbase hyi hsP, ?_⟩
    rw [hsinv]
    exact mul_mem (hbase (base_mem hei))
      (sub_mem (one_mem _) (mul_mem (hbase (base_mem hb)) hy'i))
  refine polyChart_le ((baseRing_le_polyChart _).trans le_localAt) ?_
  refine mem_localAt.2 ⟨s, hsP, hsv, ?_⟩
  rw [hs, ← mul_assoc, inv_mul_cancel₀ hy'0, one_mul]
  exact self_mem_polyChart _

/-- **Lines with affinely related coordinates are locally equivalent.** -/
theorem line_locallyCovers {e b : K} (he : v e = 1) (hb : v b ≤ 1) (y : F)
    {W : ValuationSubring F} {A : Subring F} (hA : A ∈ (line v y).charts) (hAW : A ≤ W.toSubring) :
    ∃ A'' ∈ (line v (⟪e⟫ * y + ⟪b⟫)).charts, A'' ≤ W.toSubring ∧ A'' ≤ localAt A W ∧
      A ≤ localAt A'' W := by
  set y' := ⟪e⟫ * y + ⟪b⟫ with hy'
  have hP : polyChart v y' = polyChart v y := polyChart_affine he hb y
  have hbase : baseRing F v.valuationSubring ≤ W.toSubring := (line v y).le_chart A hA |>.trans hAW
  rcases mem_line_charts.1 hA with rfl | rfl
  · exact ⟨_, mem_line_charts.2 (.inl rfl), hP ▸ hAW, hP ▸ le_localAt, hP ▸ le_localAt⟩
  · have hyi : y⁻¹ ∈ W := hAW (self_mem_polyChart _)
    by_cases hyW : y ∈ W
    · refine ⟨_, mem_line_charts.2 (.inl rfl), hP ▸ polyChart_le hbase hyW, ?_, ?_⟩
      · rw [hP]
        refine polyChart_le ((baseRing_le_polyChart _).trans le_localAt) ?_
        rcases eq_or_ne y 0 with h0 | h0
        · rw [h0]; exact zero_mem _
        · have hv : W.valuation y⁻¹ = 1 := by
            rw [valuation_eq_one_iff_mem_and_inv_mem, inv_inv]
            exact ⟨inv_ne_zero h0, hyi, hyW⟩
          simpa using inv_mem_localAt (self_mem_polyChart (v := v) y⁻¹) hv
      · rw [hP]
        refine polyChart_le ((baseRing_le_polyChart _).trans le_localAt) ?_
        rcases eq_or_ne y 0 with h0 | h0
        · rw [h0, inv_zero]; exact zero_mem _
        · have hv : W.valuation y = 1 := by
            rw [valuation_eq_one_iff_mem_and_inv_mem]
            exact ⟨h0, hyW, hyi⟩
          exact inv_mem_localAt (self_mem_polyChart (v := v) y) hv
    · have he0 : e ≠ 0 := by rintro rfl; simp at he
      have hei : v e⁻¹ = 1 := by rw [map_inv₀, he, inv_one]
      have hbi : v (-(e⁻¹ * b)) ≤ 1 := by
        rw [Valuation.map_neg, map_mul, hei, one_mul]; exact hb
      have hy : y = ⟪e⁻¹⟫ * y' + ⟪-(e⁻¹ * b)⟫ := by
        have he' : ⟪e⟫ ≠ 0 := by simpa using he0
        rw [hy', map_neg, map_mul, map_inv₀]
        field_simp
        ring
      have hy'W : y' ∉ W := by
        intro h
        apply hyW
        rw [hy]
        exact add_mem (mul_mem (hbase (base_mem hei.le)) h) (hbase (base_mem hbi))
      have hy'i : y'⁻¹ ∈ W := (W.mem_or_inv_mem y').resolve_left hy'W
      exact ⟨_, mem_line_charts.2 (.inr rfl), polyChart_le hbase hy'i,
        inv_chart_le_localAt he hb hy' hbase hyW hy'W,
        inv_chart_le_localAt hei hbi hy hbase hy'W hyW⟩

variable {ι : Type*} [Fintype ι]

/-- **Joins of locally equivalent lines are locally equivalent** (after a permutation `μ`). -/
theorem lines_locallyCovers (y z : ι → F) (μ : ι ≃ ι)
    (hloc : ∀ j {W : ValuationSubring F} {A : Subring F}, A ∈ (line v (y j)).charts →
      A ≤ W.toSubring → ∃ A'' ∈ (line v (z (μ j))).charts, A'' ≤ W.toSubring ∧
        A'' ≤ localAt A W ∧ A ≤ localAt A'' W)
    {W : ValuationSubring F} {A : Subring F} (hA : A ∈ (lines v y).charts)
    (hAW : A ≤ W.toSubring) :
    ∃ A' ∈ (lines v z).charts, A' ≤ W.toSubring ∧ A' ≤ localAt A W ∧ A ≤ localAt A' W := by
  obtain ⟨f, hf, rfl⟩ := mem_iJoin_charts.1 hA
  set R := baseRing F v.valuationSubring
  have hfA : ∀ j, f j ≤ R ⊔ ⨆ i, f i := fun j ↦ (le_iSup f j).trans le_sup_right
  choose A'' hA'' hA''W h1 h2 using fun j ↦ hloc j (hf j) ((hfA j).trans hAW)
  let g : ι → Subring F := fun i ↦ A'' (μ.symm i)
  have hg : ∀ i, g i ∈ (line v (z i)).charts := fun i ↦ by
    have := hA'' (μ.symm i)
    rwa [μ.apply_symm_apply] at this
  have hgj : ∀ j, A'' j ≤ R ⊔ ⨆ i, g i := fun j ↦ by
    have : A'' j = g (μ j) := by simp [g]
    rw [this]
    exact (le_iSup g (μ j)).trans le_sup_right
  refine ⟨R ⊔ ⨆ i, g i, mem_iJoin_charts.2 ⟨g, hg, rfl⟩, ?_, ?_, ?_⟩
  · exact sup_le (le_sup_left.trans hAW) (iSup_le fun i ↦ hA''W _)
  · exact sup_le (le_sup_left.trans le_localAt)
      (iSup_le fun i ↦ (h1 _).trans (localAt_mono (hfA _)))
  · exact sup_le (le_sup_left.trans le_localAt)
      (iSup_le fun j ↦ (h2 j).trans (localAt_mono (hgj j)))

/-- A ring automorphism preserving the base ring maps `O[y]` to `O[χ y]`. -/
lemma map_polyChart (χ : F ≃+* F)
    (hχ : (baseRing F v.valuationSubring).map (χ : F →+* F) = baseRing F v.valuationSubring)
    (y : F) : (polyChart v y).map (χ : F →+* F) = polyChart v (χ y) := by
  rw [polyChart, polyChart, RingHom.map_closure, Set.image_union, Set.image_singleton,
    ← Subring.coe_map, hχ]
  rfl

/-- A ring automorphism preserving the base ring maps charts of `lines v z` to charts of
`lines v (χ ∘ z)`. -/
lemma map_mem_lines_charts (χ : F ≃+* F)
    (hχ : (baseRing F v.valuationSubring).map (χ : F →+* F) = baseRing F v.valuationSubring)
    (z : ι → F) {A : Subring F} (hA : A ∈ (lines v z).charts) :
    A.map (χ : F →+* F) ∈ (lines v fun i ↦ χ (z i)).charts := by
  obtain ⟨f, hf, rfl⟩ := mem_iJoin_charts.1 hA
  refine mem_iJoin_charts.2 ⟨fun i ↦ (f i).map (χ : F →+* F), fun i ↦ ?_, ?_⟩
  · dsimp only
    rcases mem_line_charts.1 (hf i) with h | h <;> rw [h, map_polyChart χ hχ]
    · exact mem_line_charts.2 (.inl rfl)
    · rw [map_inv₀]; exact mem_line_charts.2 (.inr rfl)
  · rw [Subring.map_sup, Subring.map_iSup, hχ]

end Line

section Gauss

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

lemma ratFuncMap_comp (σ τ : K ≃+* K) :
    (ratFuncMap (σ : K →+* K)).comp (ratFuncMap (τ : K →+* K)) =
      ratFuncMap ((τ.trans σ : K ≃+* K) : K →+* K) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors K[X]) (RingHom.ext fun p ↦ ?_)
  simp only [RingHom.comp_apply, ratFuncMap_algebraMap, Polynomial.map_map]
  rfl

/-- `ratFuncMap σ` as a ring automorphism of `K(X)`. -/
noncomputable def ratFuncEquiv (σ : K ≃+* K) : RatFunc K ≃+* RatFunc K :=
  RingEquiv.ofRingHom (ratFuncMap (σ : K →+* K)) (ratFuncMap (σ.symm : K →+* K))
    (by rw [ratFuncMap_comp, RingEquiv.symm_trans_self]
        refine IsLocalization.ringHom_ext (nonZeroDivisors K[X]) (RingHom.ext fun p ↦ ?_)
        simp [ratFuncMap_algebraMap])
    (by rw [ratFuncMap_comp, RingEquiv.self_trans_symm]
        refine IsLocalization.ringHom_ext (nonZeroDivisors K[X]) (RingHom.ext fun p ↦ ?_)
        simp [ratFuncMap_algebraMap])

lemma ratFuncEquiv_apply (σ : K ≃+* K) (φ : RatFunc K) :
    ratFuncEquiv σ φ = ratFuncMap (σ : K →+* K) φ := rfl

lemma ratFuncEquiv_symm_apply (σ : K ≃+* K) (φ : RatFunc K) :
    (ratFuncEquiv σ).symm φ = ratFuncMap (σ.symm : K →+* K) φ := rfl

lemma ratFuncMap_algebraMap_K (τ : K ≃+* K) (k : K) :
    ratFuncMap (τ : K →+* K) (algebraMap K (RatFunc K) k) = algebraMap K (RatFunc K) (τ k) := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), ratFuncMap_algebraMap,
    IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
  simp

lemma map_baseRing_ratFuncMap (τ : K ≃+* K) (hτ : ∀ x, v (τ x) = v x) :
    (baseRing (RatFunc K) v.valuationSubring).map (ratFuncMap (τ : K →+* K)) =
      baseRing (RatFunc K) v.valuationSubring := by
  ext x
  simp only [baseRing, Subring.mem_map, ValuationSubring.mem_toSubring,
    Valuation.mem_valuationSubring_iff]
  constructor
  · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
    exact ⟨τ o, by rwa [hτ], (ratFuncMap_algebraMap_K τ o).symm⟩
  · rintro ⟨o, ho, rfl⟩
    refine ⟨_, ⟨τ.symm o, ?_, rfl⟩, ?_⟩
    · rwa [← hτ, RingEquiv.apply_symm_apply]
    · rw [ratFuncMap_algebraMap_K, RingEquiv.apply_symm_apply]

lemma ratFuncMap_gaussCoord (τ : K ≃+* K) (a c : K) :
    ratFuncMap (τ : K →+* K) (gaussCoord a c) = gaussCoord (τ a) (τ c) := by
  rw [gaussCoord, gaussCoord, ratFuncMap_algebraMap, gaussLin, gaussLin]
  simp [Polynomial.map_mul, Polynomial.map_sub]

lemma gaussCoord_eq_affine {a c a' c' : K} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    gaussCoord a' c' = algebraMap K (RatFunc K) (c / c') * gaussCoord a c +
      algebraMap K (RatFunc K) ((a - a') / c') := by
  have e (b : K) : algebraMap K[X] (RatFunc K) (C b) = algebraMap K (RatFunc K) b := by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  have h1 : algebraMap K (RatFunc K) c ≠ 0 := by simpa using hc
  have h2 : algebraMap K (RatFunc K) c' ≠ 0 := by simpa using hc'
  simp only [gaussCoord, gaussLin, map_mul, map_sub, e, RatFunc.algebraMap_X, map_div₀,
    map_inv₀]
  field_simp
  ring

/-- **(b) Stability of a Gauss tree model.** If `σ` is an isometric automorphism of `K` permuting
the discs of a reduced family `(a, c)` (every disc `σ D(a i, |c i|)` is a disc of the family), then
`ratFuncMap σ` preserves the tree model `gaussJoinModel v a c` up to local equivalence of charts.
-/
theorem locallyCovers_gaussJoinModel {ι : Type*} [Fintype ι] (σ : K ≃+* K)
    (hσ : ∀ x, v (σ x) = v x) {a c : ι → K} (hc : ∀ i, c i ≠ 0)
    (hred : GaussTree.IsReduced v a c)
    (hstab : ∀ i, ∃ i', v (σ (c i)) = v (c i') ∧ v (σ (a i) - a i') ≤ v (c i')) :
    LocallyCovers (gaussJoinModel v a c) (gaussJoinModel v a c) (ratFuncEquiv σ) := by
  intro A hA W hAW
  set ψ := ratFuncEquiv σ
  have hτ : ∀ x, v (σ.symm x) = v x := fun x ↦ by rw [← hσ, RingEquiv.apply_symm_apply]
  have hχ : (baseRing (RatFunc K) v.valuationSubring).map (ψ.symm : RatFunc K →+* RatFunc K) =
      baseRing (RatFunc K) v.valuationSubring := map_baseRing_ratFuncMap σ.symm hτ
  rw [Subring.comap_equiv_eq_map_symm] at hAW ⊢
  have hA' := map_mem_lines_charts ψ.symm hχ _ hA
  choose π hπ1 hπ2 using hstab
  have hπinj : Function.Injective π := by
    intro i i' h
    have hc' : v (c i) = v (c i') := by rw [← hσ, hπ1, h, ← hπ1, hσ]
    have ha : v (a i - a i') ≤ v (c i) := by
      rw [← hσ, map_sub]
      calc v (σ (a i) - σ (a i')) = v ((σ (a i) - a (π i)) - (σ (a i') - a (π i'))) := by
            rw [h]; ring_nf
        _ ≤ max (v (σ (a i) - a (π i))) (v (σ (a i') - a (π i'))) := Valuation.map_sub _ _ _
        _ ≤ v (c (π i)) := max_le (hπ2 i) (h ▸ hπ2 i')
        _ = v (c i) := by rw [← hπ1, hσ]
    refine hred i i' ⟨hc'.le, hc' ▸ ha⟩ ⟨hc'.ge, ?_⟩
    rw [← Valuation.map_neg, neg_sub]
    exact ha
  have hπbij : Function.Bijective π := Finite.injective_iff_bijective.1 hπinj
  let μ : ι ≃ ι := (Equiv.ofBijective π hπbij).symm
  have hπμ : ∀ j, π (μ j) = j := fun j ↦ (Equiv.ofBijective π hπbij).apply_symm_apply j
  refine lines_locallyCovers (y := fun j ↦ ψ.symm (gaussCoord (a j) (c j)))
    (z := fun i ↦ gaussCoord (a i) (c i)) μ (fun j W A hA hAW ↦ ?_) hA' hAW
  have hy : ψ.symm (gaussCoord (a j) (c j)) = gaussCoord (σ.symm (a j)) (σ.symm (c j)) :=
    ratFuncMap_gaussCoord σ.symm _ _
  set i := μ j
  have hcj : σ.symm (c j) ≠ 0 := by simpa using hc j
  have hci : v (c i) = v (σ.symm (c j)) := by rw [hτ, ← hπμ j, ← hπ1, hσ]
  have hci0 : v (c i) ≠ 0 := by simpa using hc i
  have hai : v (σ.symm (a j) - a i) ≤ v (c i) := by
    rw [← hσ, map_sub, RingEquiv.apply_symm_apply, ← Valuation.map_neg, neg_sub, hci, hτ,
      ← hπμ j]
    exact hπ2 i
  have hz := gaussCoord_eq_affine (a := σ.symm (a j)) (a' := a i) hcj (hc i)
  have he : v (σ.symm (c j) / c i) = 1 := by rw [map_div₀, ← hci, div_self hci0]
  have hb : v ((σ.symm (a j) - a i) / c i) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ hai zero_le
  rw [hz]
  rw [hy] at hA
  exact line_locallyCovers he hb _ hA hAW

end Gauss

section Combined

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
  [Algebra (RatFunc K) F₁] [Algebra (RatFunc K) F₂] [IsScalarTower K (RatFunc K) F₁]
  [IsScalarTower K (RatFunc K) F₂]
  {ι : Type*} [Fintype ι] (σ : K ≃+* K) (hσ : ∀ x, v (σ x) = v x) {a c : ι → K}
  (hc : ∀ i, c i ≠ 0) (hred : GaussTree.IsReduced v a c)
  (hstab : ∀ i, ∃ i', v (σ (c i)) = v (c i') ∧ v (σ (a i) - a i') ≤ v (c i'))
  (φ : F₁ ≃+* F₂)
  (hφ : ∀ x, φ (algebraMap (RatFunc K) F₁ x) = algebraMap (RatFunc K) F₂ (ratFuncMap σ x))

include hσ hc hred hstab hφ in
/-- **(a) + (b)**: a field isomorphism `φ` over `ratFuncMap σ` pulls back points of the
normalization of the tree model in `F₂` to points of its normalization in `F₁`. -/
theorem points_comap_gaussJoinModel :
    ∀ Q ∈ ((gaussJoinModel v a c).normalization F₂).points,
      Q.comap (φ : F₁ →+* F₂) ∈ ((gaussJoinModel v a c).normalization F₁).points :=
  points_comap_normalization (ratFuncEquiv σ) φ hφ
    (locallyCovers_gaussJoinModel σ hσ hc hred hstab)

include hσ hc hred hstab hφ in
/-- **(a) + (b)** for projective models with the points of the normalized tree model (M9c, the
form of `hact` in `W10Assembly`): for every point `Q` of the model of `F₂` some chart of the model
of `F₁` maps into `Q`. -/
theorem exists_projChart_map_le {R₁ : Subring F₁} {R₂ : Subring F₂} {n₁ n₂ : ℕ}
    {g₁ : Fin (n₁ + 1) → F₁} {g₂ : Fin (n₂ + 1) → F₂}
    (hp₁ : (projModel R₁ g₁).points = ((gaussJoinModel v a c).normalization F₁).points)
    (hp₂ : (projModel R₂ g₂).points = ((gaussJoinModel v a c).normalization F₂).points) :
    ∀ Q ∈ (projModel R₂ g₂).points, ∃ i, ∀ y ∈ projChart R₁ g₁ i, φ y ∈ Q := by
  intro Q hQ
  rw [hp₂] at hQ
  have h := points_comap_gaussJoinModel σ hσ hc hred hstab φ hφ Q hQ
  rw [← hp₁] at h
  obtain ⟨C, hC, hCQ⟩ := exists_chart_le_of_mem_points h
  obtain ⟨i, rfl⟩ := mem_projModel_charts.1 hC
  exact ⟨i, fun y hy ↦ hCQ hy⟩

end Combined

end W10Stable

end SemistableReduction
