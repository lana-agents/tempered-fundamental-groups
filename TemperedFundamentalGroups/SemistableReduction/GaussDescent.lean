/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussTreeSemistable

/-!
# Descent of Gauss data and of the tree of projective lines

Blueprint §9.8 (W9), layers D1 and D2. Let `φ : K → L` be an embedding of fields (e.g. a finite
extension `K'` of the base field inside an algebraically closed `C`) and `v` a valuation on `L`,
restricting to `v.comap φ` on `K`.

* **D1 (Gauss data descend).** `ratFuncMap φ : K(X) → L(X)` maps the Gauss coordinate
  `(X - a)/c` to `(X - φ a)/φ c` (`ratFuncMap_gaussCoord`), and the Gauss valuation `w_{φ a, r}`
  of `L(X)` restricts to the Gauss valuation `w_{a, r}` of `K(X)` for `v.comap φ`
  (`gaussRat_comap`, `comap_valuationSubring_gaussRat`). For `L/K` algebraic, finitely many
  centres and radii `a i, c i ∈ L` lie in a finite subextension (`exists_gaussDescent`).
* **D2 (the tree model descends).** The base change `ZariskiModel.baseChange` of a Zariski model
  (charts `R ⊔ ψ(A)`, the images of `O_K-charts ⊗ O_L`) of `gaussJoinModel` over `K` is
  `gaussJoinModel` over `L` (`gaussJoinModel_baseChange`); convexity and reducedness of the family
  descend (`isConvex_comap_iff`, `isReduced_comap_iff`). Over a discrete valuation ring with
  uniformizer `ϖ` the tree model of any convex reduced family is semistable for `ϖ`
  (`gaussJoinModel_isSemistable_of_isDiscreteValuationRing`): the radii are rescaled by units to
  powers of `ϖ`, which does not change the model (`gaussJoinModel_mul_unit`).
-/

universe u

open Polynomial

namespace SemistableReduction

/-! ### D1: the map `K(X) → L(X)` and Gauss valuations -/

section RatFuncMap

variable {K L : Type*} [Field K] [Field L] (φ : K →+* L)

/-- The embedding `K(X) → L(X)`, `X ↦ X`, induced by a field embedding `φ : K → L`. -/
noncomputable def ratFuncMap : RatFunc K →+* RatFunc L :=
  RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective φ φ.injective))

@[simp]
lemma ratFuncMap_algebraMap (p : K[X]) :
    ratFuncMap φ (algebraMap K[X] (RatFunc K) p) = algebraMap L[X] (RatFunc L) (p.map φ) := by
  have := RatFunc.map_apply_div (Polynomial.mapRingHom φ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective φ φ.injective)) p 1
  simp only [map_one, div_one] at this
  exact this

@[simp]
lemma ratFuncMap_algebraMap_C (k : K) :
    ratFuncMap φ (algebraMap K (RatFunc K) k) = algebraMap L (RatFunc L) (φ k) := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), ratFuncMap_algebraMap,
    Polynomial.algebraMap_eq, map_C, IsScalarTower.algebraMap_apply L L[X] (RatFunc L),
    Polynomial.algebraMap_eq]

lemma ratFuncMap_comp_algebraMap :
    (ratFuncMap φ).comp (algebraMap K (RatFunc K)) = (algebraMap L (RatFunc L)).comp φ :=
  RingHom.ext fun k ↦ ratFuncMap_algebraMap_C φ k

lemma ratFuncMap_injective : Function.Injective (ratFuncMap φ) :=
  (ratFuncMap φ).injective

/-- The Gauss coordinate `(X - a)/c` maps to `(X - φ a)/φ c`. -/
@[simp]
lemma ratFuncMap_gaussCoord (a c : K) :
    ratFuncMap φ (gaussCoord a c) = gaussCoord (φ a) (φ c) := by
  rw [gaussCoord, gaussCoord, ratFuncMap_algebraMap]
  congr 1
  simp [gaussLin, Polynomial.map_mul, Polynomial.map_sub]

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

lemma comap_valuationSubring (v : Valuation L Γ₀) :
    (v.comap φ).valuationSubring = v.valuationSubring.comap φ := by
  ext x
  simp

lemma Gauss.sup_map (r : Γ₀ˣ) (p : K[X]) :
    Gauss.sup v r (p.map φ) = Gauss.sup (v.comap φ) r p := by
  have hterm (i : ℕ) : Gauss.term v r (p.map φ) i = Gauss.term (v.comap φ) r p i := by
    simp [Gauss.term, coeff_map]
  apply le_antisymm
  · rw [Gauss.sup_le_iff]
    intro i
    rw [hterm]
    exact Gauss.term_le_sup _ _
  · rw [Gauss.sup_le_iff]
    intro i
    rw [← hterm]
    exact Gauss.term_le_sup _ _

lemma gauss_map (a : K) (r : Γ₀ˣ) (p : K[X]) :
    gauss v (φ a) r (p.map φ) = gauss (v.comap φ) a r p := by
  rw [gauss_apply, gauss_apply, ← map_taylor, Gauss.sup_map]

/-- **(W9, D1)** The Gauss valuation `w_{φ a, r}` of `L(X)` restricts to the Gauss valuation
`w_{a, r}` of `K(X)` for the restricted valuation `v.comap φ`. -/
theorem gaussRat_comap (a : K) (r : Γ₀ˣ) :
    (gaussRat v (φ a) r).comap (ratFuncMap φ) = gaussRat (v.comap φ) a r := by
  ext x
  induction x using RatFunc.induction_on with
  | f p q hq =>
    rw [Valuation.comap_apply, map_div₀, map_div₀, ratFuncMap_algebraMap, ratFuncMap_algebraMap,
      map_div₀, gaussRat_algebraMap, gaussRat_algebraMap, gaussRat_algebraMap,
      gaussRat_algebraMap, gauss_map, gauss_map]

/-- The valuation ring of `w_{φ a, r}` lies over that of `w_{a, r}`. -/
theorem comap_valuationSubring_gaussRat (a : K) (r : Γ₀ˣ) :
    (gaussRat v (φ a) r).valuationSubring.comap (ratFuncMap φ) =
      (gaussRat (v.comap φ) a r).valuationSubring := by
  rw [← gaussRat_comap, comap_valuationSubring]

/-- **(W9, D1) Residue fields.** Under the local map `O_{w'} → O_w` induced by `ratFuncMap φ`
(`w' = w_{a, r}` on `K(X)` for `v.comap φ`, `w = w_{φ a, r}` on `L(X)`), the residue `x̄'` of the
Gauss coordinate `(X - a)/c` maps to the residue `x̄` of `(X - φ a)/φ c`. -/
theorem residue_gaussGen_map {a c : K} {r : Γ₀ˣ} (hc : v (φ c) = r) :
    letI := (ratFuncMap φ).toAlgebra
    letI := residueAlgebra (comap_valuationSubring_gaussRat φ v a r)
    algebraMap (IsLocalRing.ResidueField (gaussRat (v.comap φ) a r).valuationSubring)
        (IsLocalRing.ResidueField (gaussRat v (φ a) r).valuationSubring)
        (IsLocalRing.residue _ (gaussGen (v.comap φ) a r (c := c)
          (by rw [Valuation.comap_apply]; exact hc))) =
      IsLocalRing.residue _ (gaussGen v (φ a) r hc) := by
  letI := (ratFuncMap φ).toAlgebra
  letI := residueAlgebra (comap_valuationSubring_gaussRat φ v a r)
  change IsLocalRing.ResidueField.map _ _ = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 1
  refine Subtype.ext ?_
  rw [coe_toVal, coe_gaussGen, coe_gaussGen]
  change ratFuncMap φ _ = _
  rw [ratFuncMap_algebraMap]
  congr 1
  simp [gaussLin, Polynomial.map_mul, Polynomial.map_sub]

/-- **(W9, D1) The residue field over `L` is generated by the residue field over `K`**: the
residue field `κ(w) = κ(v)(x̄)` of `w_{φ a, r}` is generated over `κ(v)` by the image of the
residue `x̄'` of the Gauss coordinate of `w_{a, r}` (whose residue field is `κ(v|_K)(x̄')`). -/
theorem adjoin_residue_gaussGen_map_eq_top {a c : K} {r : Γ₀ˣ} (hc : v (φ c) = r) :
    letI := (ratFuncMap φ).toAlgebra
    letI := residueAlgebra (comap_valuationSubring_gaussRat φ v a r)
    IntermediateField.adjoin (IsLocalRing.ResidueField v.valuationSubring)
      {algebraMap (IsLocalRing.ResidueField (gaussRat (v.comap φ) a r).valuationSubring)
        (IsLocalRing.ResidueField (gaussRat v (φ a) r).valuationSubring)
        (IsLocalRing.residue _ (gaussGen (v.comap φ) a r (c := c)
          (by rw [Valuation.comap_apply]; exact hc)))} = ⊤ := by
  rw [residue_gaussGen_map φ v hc]
  exact adjoin_residue_gaussGen_eq_top hc

end RatFuncMap

/-- **(W9, D1) Gauss data descend to a finite subextension.** For `C/K` algebraic and finitely
many centres `a i` and radii `c i` in `C`, there is a finite subextension `E` of `C/K` containing
them. -/
theorem exists_gaussDescent {K C : Type*} [Field K] [Field C] [Algebra K C]
    [Algebra.IsAlgebraic K C] {ι : Type*} [Finite ι] (a c : ι → C) :
    ∃ E : IntermediateField K C, FiniteDimensional K E ∧ ∃ a' c' : ι → E,
      (∀ i, algebraMap E C (a' i) = a i) ∧ ∀ i, algebraMap E C (c' i) = c i := by
  set S : Set C := Set.range a ∪ Set.range c
  have hS : S.Finite := (Set.finite_range a).union (Set.finite_range c)
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin K S,
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x,
    fun i ↦ ⟨a i, IntermediateField.subset_adjoin K S (Or.inl ⟨i, rfl⟩)⟩,
    fun i ↦ ⟨c i, IntermediateField.subset_adjoin K S (Or.inr ⟨i, rfl⟩)⟩,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

/-! ### D2: base change of Zariski models -/

namespace ZariskiModel

variable {F' F : Type*} [Field F'] [Field F] {R' : Subring F'}

open scoped Classical in
/-- The **base change** of a Zariski model of `F'` over `R'` along `ψ : F' → F` to the base
`R ⊆ F`: its charts are the subrings `R ⊔ ψ(A)` generated by `R` and the image of a chart `A`
(the image of `A ⊗_{R'} R → F`). -/
noncomputable def baseChange (ψ : F' →+* F) (R : Subring F) (M : ZariskiModel R') :
    ZariskiModel R where
  charts := M.charts.image fun A ↦ R ⊔ A.map ψ
  le_chart A hA := by
    obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hA
    exact le_sup_left

variable {ψ : F' →+* F} {R : Subring F} {M : ZariskiModel R'}

/-- Zariski models with the same charts are equal. -/
lemma ext_charts {M₁ M₂ : ZariskiModel R} (h : M₁.charts = M₂.charts) : M₁ = M₂ := by
  cases M₁
  cases M₂
  simp only at h
  subst h
  rfl

lemma mem_baseChange_charts {A : Subring F} :
    A ∈ (M.baseChange ψ R).charts ↔ ∃ B ∈ M.charts, A = R ⊔ B.map ψ := by
  classical
  simp only [baseChange, Finset.mem_image]
  exact ⟨fun ⟨B, hB, h⟩ ↦ ⟨B, hB, h.symm⟩, fun ⟨B, hB, h⟩ ↦ ⟨B, hB, h.symm⟩⟩

/-- Base change commutes with joins. -/
theorem iJoin_baseChange {ι : Type*} [Fintype ι] (hR : R'.map ψ ≤ R)
    (M : ι → ZariskiModel R') :
    (iJoin M).baseChange ψ R = iJoin fun i ↦ (M i).baseChange ψ R := by
  have key (f : ι → Subring F') :
      R ⊔ (R' ⊔ ⨆ i, f i).map ψ = R ⊔ ⨆ i, (R ⊔ (f i).map ψ) := by
    rw [Subring.map_sup, Subring.map_iSup]
    apply le_antisymm
    · refine sup_le le_sup_left (sup_le (hR.trans le_sup_left) (iSup_le fun i ↦ ?_))
      exact le_sup_right.trans ((le_iSup (fun i ↦ R ⊔ (f i).map ψ) i).trans le_sup_right)
    · refine sup_le le_sup_left (iSup_le fun i ↦ sup_le le_sup_left ?_)
      exact (le_iSup (fun i ↦ (f i).map ψ) i).trans (le_sup_right.trans le_sup_right)
  refine ext_charts ?_
  ext A
  rw [mem_baseChange_charts, mem_iJoin_charts]
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨f, hf, rfl⟩ := mem_iJoin_charts.1 hB
    exact ⟨fun i ↦ R ⊔ (f i).map ψ, fun i ↦ mem_baseChange_charts.2 ⟨f i, hf i, rfl⟩, key f⟩
  · rintro ⟨g, hg, rfl⟩
    choose f hf hfg using fun i ↦ mem_baseChange_charts.1 (hg i)
    refine ⟨R' ⊔ ⨆ i, f i, mem_iJoin_charts.2 ⟨f, hf, rfl⟩, ?_⟩
    rw [key f]
    simp only [hfg]

end ZariskiModel

/-! ### D2: the tree of lines descends -/

section Lines

variable {K' K F' F : Type*} [Field K'] [Field K] [Field F'] [Field F] [Algebra K' F']
  [Algebra K F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}
  {φ : K' →+* K} {ψ : F' →+* F} (hψ : ∀ k, ψ (algebraMap K' F' k) = algebraMap K F (φ k))

include hψ

lemma map_baseRing_le :
    (baseRing F' (v.comap φ).valuationSubring).map ψ ≤ baseRing F v.valuationSubring := by
  rintro _ ⟨_, ⟨o, ho, rfl⟩, rfl⟩
  exact ⟨φ o, by simpa using ho, (hψ o).symm⟩

/-- The chart `O[ψ y]` is generated by `O` and the image of `O'[y]`. -/
theorem sup_map_polyChart (y : F') :
    baseRing F v.valuationSubring ⊔ (polyChart (v.comap φ) y).map ψ = polyChart v (ψ y) := by
  apply le_antisymm
  · refine sup_le (baseRing_le_polyChart _) (Subring.map_le_iff_le_comap.2 ?_)
    refine polyChart_le (fun x hx ↦ ?_) (self_mem_polyChart _)
    exact baseRing_le_polyChart _ (map_baseRing_le hψ ⟨x, hx, rfl⟩)
  · exact polyChart_le le_sup_left
      (le_sup_right (a := baseRing F v.valuationSubring)
        ⟨y, self_mem_polyChart y, rfl⟩)

namespace ZariskiModel

/-- The line `ℙ¹_{O'}` with coordinate `y` base-changes to the line `ℙ¹_O` with coordinate
`ψ y`. -/
theorem line_baseChange (y : F') :
    (line (v.comap φ) y).baseChange ψ (baseRing F v.valuationSubring) = line v (ψ y) := by
  refine ext_charts (Finset.ext fun A ↦ ?_)
  rw [mem_baseChange_charts, mem_line_charts]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rcases mem_line_charts.1 hB with rfl | rfl
    · exact Or.inl (sup_map_polyChart hψ y)
    · exact Or.inr (by rw [sup_map_polyChart hψ, map_inv₀])
  · rintro (rfl | rfl)
    · exact ⟨_, mem_line_charts.2 (Or.inl rfl), (sup_map_polyChart hψ y).symm⟩
    · exact ⟨_, mem_line_charts.2 (Or.inr rfl), by rw [sup_map_polyChart hψ, map_inv₀]⟩

/-- Joins of lines base-change to joins of lines. -/
theorem lines_baseChange {ι : Type*} [Fintype ι] (y : ι → F') :
    (lines (v.comap φ) y).baseChange ψ (baseRing F v.valuationSubring) =
      lines v fun i ↦ ψ (y i) := by
  rw [lines, iJoin_baseChange (map_baseRing_le hψ)]
  simp only [line_baseChange hψ]
  rfl

end ZariskiModel

end Lines

section TreeDescent

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L) {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀) {ι : Type*}

/-- **(W9, D2) The tree of lines descends.** The base change along `K(X) → L(X)` of the join model
of the Gauss valuations `w_{a i, |c i|}` over `O_K = O_L ∩ K` is the join model of the Gauss
valuations `w_{φ (a i), |φ (c i)|}` over `O_L`. -/
theorem gaussJoinModel_baseChange [Fintype ι] (a c : ι → K) :
    (gaussJoinModel (v.comap φ) a c).baseChange (ratFuncMap φ)
        (baseRing (RatFunc L) v.valuationSubring) =
      gaussJoinModel v (fun i ↦ φ (a i)) (fun i ↦ φ (c i)) := by
  rw [gaussJoinModel, ZariskiModel.lines_baseChange (ratFuncMap_algebraMap_C φ)]
  simp only [ratFuncMap_gaussCoord]
  rfl

variable {φ v} {a c : ι → K}

lemma discLE_comap_iff {i j : ι} :
    GaussTree.DiscLE (v.comap φ) a c i j ↔
      GaussTree.DiscLE v (fun i ↦ φ (a i)) (fun i ↦ φ (c i)) i j := by
  simp [GaussTree.DiscLE]

/-- Convexity of a family of discs descends. -/
lemma isConvex_comap_iff :
    GaussTree.IsConvex (v.comap φ) a c ↔
      GaussTree.IsConvex v (fun i ↦ φ (a i)) (fun i ↦ φ (c i)) := by
  simp [GaussTree.IsConvex, discLE_comap_iff]

/-- Reducedness of a family of discs descends. -/
lemma isReduced_comap_iff :
    GaussTree.IsReduced (v.comap φ) a c ↔
      GaussTree.IsReduced v (fun i ↦ φ (a i)) (fun i ↦ φ (c i)) := by
  simp only [GaussTree.IsReduced, discLE_comap_iff]

end TreeDescent

/-! ### D2: semistability over a discrete valuation ring -/

section Discrete

open ZariskiModel GaussTree

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

lemma valuation_coe_unit (e : v.valuationSubringˣ) : v ((e : v.valuationSubring) : K) = 1 := by
  have h : ((e : v.valuationSubring) : K) * ((e⁻¹ : v.valuationSubringˣ) : v.valuationSubring) =
      1 := congrArg Subtype.val e.mul_inv
  refine eq_one_of_mul_eq_one
    ((Valuation.mem_valuationSubring_iff _ _).1 (e : v.valuationSubring).property)
    ((Valuation.mem_valuationSubring_iff _ _).1
      ((e⁻¹ : v.valuationSubringˣ) : v.valuationSubring).property) ?_
  rw [← map_mul, h, map_one]

/-- Rescaling a coordinate by a unit of `O` does not change the chart `O[y]`. -/
lemma polyChart_mul_unit {e : K} (he : v e = 1) (y : F) :
    polyChart v (algebraMap K F e * y) = polyChart v y := by
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have heO : e ∈ v.valuationSubring := (Valuation.mem_valuationSubring_iff _ _).2 he.le
  have heO' : e⁻¹ ∈ v.valuationSubring :=
    (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, he, inv_one])
  apply le_antisymm
  · exact polyChart_le (baseRing_le_polyChart _)
      (mul_mem (baseRing_le_polyChart _ (algebraMap_mem_baseRing heO)) (self_mem_polyChart y))
  · refine polyChart_le (baseRing_le_polyChart _) ?_
    have hy : y = algebraMap K F e⁻¹ * (algebraMap K F e * y) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ he0, map_one, one_mul]
    have hmem : algebraMap K F e⁻¹ * (algebraMap K F e * y) ∈ polyChart v (algebraMap K F e * y) :=
      mul_mem (baseRing_le_polyChart _ (algebraMap_mem_baseRing heO')) (self_mem_polyChart _)
    rwa [← hy] at hmem

/-- Rescaling the coordinate of `ℙ¹_O` by a unit of `O` does not change the model. -/
lemma line_mul_unit {e : K} (he : v e = 1) (y : F) :
    line v (algebraMap K F e * y) = line v y := by
  have he' : v e⁻¹ = 1 := by rw [map_inv₀, he, inv_one]
  have h₂ : polyChart v (algebraMap K F e * y)⁻¹ = polyChart v y⁻¹ := by
    rw [mul_inv, ← map_inv₀, polyChart_mul_unit he']
  refine ext_charts (Finset.ext fun A ↦ ?_)
  rw [mem_line_charts, mem_line_charts, polyChart_mul_unit he, h₂]

lemma gaussCoord_mul (a e c : K) :
    gaussCoord a (e * c) = algebraMap K (RatFunc K) e⁻¹ * gaussCoord a c := by
  rw [gaussCoord, gaussCoord, gaussLin, gaussLin, mul_inv, C_mul, mul_assoc, map_mul,
    IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]

/-- Rescaling the radii `c i` by units of `O` does not change the tree model. -/
theorem gaussJoinModel_mul_unit {ι : Type*} [Fintype ι] (a c e : ι → K) (he : ∀ i, v (e i) = 1) :
    gaussJoinModel v a (fun i ↦ e i * c i) = gaussJoinModel v a c := by
  simp only [gaussJoinModel, lines]
  congr 1
  funext i
  rw [gaussCoord_mul, line_mul_unit (by rw [map_inv₀, he i, inv_one])]

variable [IsDiscreteValuationRing v.valuationSubring] {ϖ : v.valuationSubring}

omit [IsDiscreteValuationRing v.valuationSubring] in
lemma coe_uniformizer_ne_zero (hϖ : Irreducible ϖ) : (ϖ : K) ≠ 0 := fun h ↦
  hϖ.ne_zero (Subtype.ext h)

omit [IsDiscreteValuationRing v.valuationSubring] in
lemma valuation_uniformizer_lt_one (hϖ : Irreducible ϖ) : v (ϖ : K) < 1 := by
  refine lt_of_le_of_ne ((Valuation.mem_valuationSubring_iff _ _).1 ϖ.2) fun h ↦ ?_
  exact hϖ.not_isUnit ((Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one.2 h)

omit [IsDiscreteValuationRing v.valuationSubring] in
lemma valuation_zpow_le_one_iff (hϖ : Irreducible ϖ) (n : ℤ) :
    v ((ϖ : K) ^ n) ≤ 1 ↔ 0 ≤ n := by
  rw [map_zpow₀]
  exact zpow_le_one_iff_right_of_lt_one₀
    (zero_lt_iff.2 ((v.ne_zero_iff).2 (coe_uniformizer_ne_zero hϖ)))
    (valuation_uniformizer_lt_one hϖ)

/-- Every nonzero element of `K` is a unit of `O` times an integral power of the uniformizer. -/
lemma exists_valuation_div_zpow_eq_one (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃ n : ℤ, v (x / (ϖ : K) ^ n) = 1 := by
  have hvx : v x ≠ 0 := (v.ne_zero_iff).2 hx
  rcases le_or_gt (v x) 1 with h | h
  · have hx' : (⟨x, h⟩ : v.valuationSubring) ≠ 0 := fun h0 ↦ hx (congrArg Subtype.val h0)
    obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' hϖ
    have hv : v x = v (ϖ : K) ^ n := by
      have := congrArg (fun y : v.valuationSubring ↦ v (y : K)) he
      simpa [valuation_coe_unit] using this
    refine ⟨n, ?_⟩
    rw [map_div₀, map_zpow₀, zpow_natCast, hv,
      div_self (pow_ne_zero _ ((v.ne_zero_iff).2 (coe_uniformizer_ne_zero hϖ)))]
  · have hinv : v x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact (inv_lt_one_of_one_lt₀ h).le
    have hx' : (⟨x⁻¹, hinv⟩ : v.valuationSubring) ≠ 0 := fun h0 ↦
      inv_ne_zero hx (congrArg Subtype.val h0)
    obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' hϖ
    have hv : v x⁻¹ = v (ϖ : K) ^ n := by
      have := congrArg (fun y : v.valuationSubring ↦ v (y : K)) he
      simpa [valuation_coe_unit] using this
    refine ⟨-(n : ℤ), ?_⟩
    rw [map_div₀, map_zpow₀, zpow_neg, zpow_natCast, div_inv_eq_mul, ← hv, map_inv₀,
      mul_inv_cancel₀ hvx]

/-- **A discrete valuation ring has rank one**: the only overrings in `K` are `O` and `K`. -/
theorem eq_or_eq_top_of_le (hϖ : Irreducible ϖ) (O' : ValuationSubring K)
    (h : v.valuationSubring ≤ O') : O' = v.valuationSubring ∨ O' = ⊤ := by
  by_cases h' : O' ≤ v.valuationSubring
  · exact Or.inl (le_antisymm h' h)
  right
  obtain ⟨x, hxO', hxO⟩ := SetLike.not_le_iff_exists.1 h'
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxO (zero_mem _)
  have h0 := coe_uniformizer_ne_zero hϖ
  obtain ⟨n, hn⟩ := exists_valuation_div_zpow_eq_one hϖ hx0
  have hmemO {y : K} (hy : v y ≤ 1) : y ∈ O' := h ((Valuation.mem_valuationSubring_iff _ _).2 hy)
  have hn0 : n < 0 := by
    by_contra hn0
    refine hxO ((Valuation.mem_valuationSubring_iff _ _).2 ?_)
    have hx : x = x / (ϖ : K) ^ n * (ϖ : K) ^ n := by
      rw [div_mul_cancel₀ _ (zpow_ne_zero _ h0)]
    rw [hx, map_mul, hn, one_mul]
    exact (valuation_zpow_le_one_iff hϖ n).2 (not_lt.1 hn0)
  have hinv : (ϖ : K)⁻¹ ∈ O' := by
    have hx : (ϖ : K)⁻¹ = x * (x / (ϖ : K) ^ n)⁻¹ * (ϖ : K) ^ (-n - 1) := by
      rw [inv_div, mul_div_assoc', mul_div_cancel_left₀ _ hx0, ← zpow_add₀ h0,
        show n + (-n - 1) = -1 by ring, zpow_neg_one]
    rw [hx]
    refine mul_mem (mul_mem hxO' (hmemO (by rw [map_inv₀, hn, inv_one]))) (hmemO ?_)
    exact (valuation_zpow_le_one_iff hϖ _).2 (by omega)
  refine eq_top_iff.2 fun y _ ↦ ?_
  rcases eq_or_ne y 0 with rfl | hy0
  · exact zero_mem _
  obtain ⟨m, hm⟩ := exists_valuation_div_zpow_eq_one hϖ hy0
  have hy : y = y / (ϖ : K) ^ m * (ϖ : K) ^ m := by rw [div_mul_cancel₀ _ (zpow_ne_zero _ h0)]
  rw [hy]
  refine mul_mem (hmemO hm.le) ?_
  rcases le_or_gt 0 m with hm0 | hm0
  · exact hmemO ((valuation_zpow_le_one_iff hϖ m).2 hm0)
  · have : (ϖ : K) ^ m = ((ϖ : K)⁻¹) ^ (-m).toNat := by
      rw [inv_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_neg, neg_neg]
    rw [this]
    exact pow_mem hinv _

/-- **(W9, D2) The tree of lines over a discrete valuation ring is semistable.** For a convex
reduced nonempty finite family of Gauss valuations `w_{a i, |c i|}` of `K(X)` over a discrete
valuation ring `O` with uniformizer `ϖ`, every chart of `gaussJoinModel v a c` (with any
`O`-algebra structure compatible with `K(X)`) is semistable for `ϖ`: rescaling the radii by units
of `O` (`gaussJoinModel_mul_unit`) makes them powers of `ϖ`, so the node charts become
`O[u, ϖⁿ/u]` (`gaussJoinModel_isSemistable`). -/
theorem gaussJoinModel_isSemistable_of_isDiscreteValuationRing (hϖ : Irreducible ϖ)
    {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → K} (hc : ∀ i, c i ≠ 0)
    (hconv : IsConvex v a c) (hred : IsReduced v a c) {C : Subring (RatFunc K)}
    (hC : C ∈ (gaussJoinModel v a c).charts) [Algebra v.valuationSubring C]
    (hCc : ∀ o, ((algebraMap v.valuationSubring C o : C) : RatFunc K) =
      algebraMap v.valuationSubring (RatFunc K) o) :
    IsSemistable ϖ C := by
  have h0 := coe_uniformizer_ne_zero hϖ
  choose n hn using fun i ↦ exists_valuation_div_zpow_eq_one hϖ (hc i)
  set c' : ι → K := fun i ↦ (ϖ : K) ^ n i with hc'
  have hc'0 (i : ι) : c' i ≠ 0 := zpow_ne_zero _ h0
  have hvc (i : ι) : v (c' i) = v (c i) := by
    have := hn i
    rw [map_div₀, div_eq_one_iff_eq ((v.ne_zero_iff).2 (zpow_ne_zero _ h0))] at this
    exact this.symm
  have hcu : c = fun i ↦ c i / c' i * c' i := funext fun i ↦ (div_mul_cancel₀ _ (hc'0 i)).symm
  rw [hcu, gaussJoinModel_mul_unit a c' _ hn] at hC
  have hdisc (i j : ι) : DiscLE v a c' i j ↔ DiscLE v a c i j := by
    rw [DiscLE, DiscLE, hvc, hvc]
  have hconv' : IsConvex v a c' := by
    intro i j
    obtain ⟨k, hik, hjk, hk⟩ := hconv i j
    exact ⟨k, (hdisc i k).2 hik, (hdisc j k).2 hjk, by rw [hvc, hvc, hvc]; exact hk⟩
  have hred' : IsReduced v a c' := fun i j hij hji ↦
    hred i j ((hdisc i j).1 hij) ((hdisc j i).1 hji)
  refine gaussJoinModel_isSemistable hc'0 hconv' hred' (eq_or_eq_top_of_le hϖ) ?_ hC hCc
  intro j m hjm _
  have hle : 0 ≤ n j - n m := by
    rw [← valuation_zpow_le_one_iff hϖ, zpow_sub₀ h0, map_div₀,
      div_le_one₀ (zero_lt_iff.2 ((v.ne_zero_iff).2 (zpow_ne_zero _ h0)))]
    exact hjm.1
  refine ⟨(n j - n m).toNat, ?_⟩
  push_cast
  rw [← zpow_natCast, Int.toNat_of_nonneg hle, zpow_sub₀ h0]

end Discrete

/-! ### D1 + D2 packaged -/

/-- **(W9, D1 + D2) The tree model descends to a finite subextension.** Let `C/K` be algebraic, `v`
a valuation on `C` and `w_{a i, r i}` (`v (c i) = r i`) finitely many Gauss valuations of `C(X)`.
There is a finite subextension `E` of `C/K` and centres and radii `a' i, c' i ∈ E` over `a i, c i`
such that the tree model `gaussJoinModel` over `O_E = O_C ∩ E` base-changes to the tree model over
`O_C`, the radii are the same, and each `w_{a i, r i}` restricts to `w_{a' i, r i}` on `E(X)`. -/
theorem exists_gaussJoinModel_descent {K C : Type u} [Field K] [Field C] [Algebra K C]
    [Algebra.IsAlgebraic K C] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation C Γ₀) {ι : Type*} [Fintype ι] (a c : ι → C) {r : ι → Γ₀ˣ}
    (hc : ∀ i, v (c i) = r i) :
    ∃ E : IntermediateField K C, FiniteDimensional K E ∧ ∃ a' c' : ι → E,
      (gaussJoinModel (v.comap (algebraMap E C)) a' c').baseChange (ratFuncMap (algebraMap E C))
          (baseRing (RatFunc C) v.valuationSubring) = gaussJoinModel v a c ∧
      (∀ i, v.comap (algebraMap E C) (c' i) = r i) ∧
      ∀ i, (gaussRat v (a i) (r i)).valuationSubring.comap (ratFuncMap (algebraMap E C)) =
        (gaussRat (v.comap (algebraMap E C)) (a' i) (r i)).valuationSubring := by
  obtain ⟨E, hE, a', c', ha, hc'⟩ := exists_gaussDescent (K := K) a c
  obtain rfl : a = fun i ↦ algebraMap E C (a' i) := funext fun i ↦ (ha i).symm
  obtain rfl : c = fun i ↦ algebraMap E C (c' i) := funext fun i ↦ (hc' i).symm
  exact ⟨E, hE, a', c', gaussJoinModel_baseChange _ v a' c', fun i ↦ by simpa using hc i,
    fun i ↦ comap_valuationSubring_gaussRat _ v (a' i) (r i)⟩

end SemistableReduction
