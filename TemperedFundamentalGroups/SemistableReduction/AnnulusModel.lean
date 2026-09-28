/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization
import TemperedFundamentalGroups.SemistableReduction.NodeNormal
import TemperedFundamentalGroups.SemistableReduction.LocalModel

/-!
# The model of an annulus: two `ℙ¹`s meeting in a node

Blueprint §9.6 (W5), layer M7 (first case). Let `y` be a Gauss coordinate of `w₁` (radius `1`)
and `z = y / c` one of `w₂` (`c ∈ K`, `c ≠ 0`; for `v(c) < 1` the disc of `w₂` is strictly smaller).
The **annulus model** `ZariskiModel.annulus v y c` has the three charts

* `O[y⁻¹]` (the component of `w₁` near `∞`),
* `O[y, c / y]`, the **node** (`nodeChart`),
* `O[z]` (the component of `w₂` near `0`).

It is proper and separated (`annulus_isProper`, `annulus_isSeparated`), of finite type, and its
vertex set is `{O_{w₁}, O_{w₂}}` (`annulus_vertexSet`). With an `O`-algebra structure on `F`:

* `range_nodeLift`, `nodeLift_injective`: `O[y, c/y]` is the image of an injective `O`-algebra map
  from `Node O c = O[u, v] ⧸ (u v - c)` (`u ↦ y`, `v ↦ c / y`), through `Node.laurent` and the
  evaluation `T ↦ y` of Laurent polynomials, injective since `y` is transcendental;
* `range_aeval`, `aeval_injective'`: `O[z] ≅ O[X]`.

So the annulus model is the semistable model of the closed annulus `|c| ≤ |y| ≤ 1`: two
projective lines over `k` meeting in a node of thickness `c`; for `c = ϖ ^ n` every chart is
semistable in the sense of `LocalModel.lean` (`annulus_isSemistable`). For `K(X)`:
`gaussAnnulusModel v a c₁ c₂` with vertex set `{O_{w_{a,r₁}}, O_{w_{a,r₂}}}`
(`gaussAnnulusModel_vertexSet`) and semistable charts (`gaussAnnulusModel_isSemistable`).
-/

universe u

open Polynomial

namespace SemistableReduction

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

variable (v) in
/-- The node chart `O[y, c / y]`. -/
def nodeChart (y : F) (c : K) : Subring F :=
  Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ {y, algebraMap K F c / y})

/-- A subring generated over the base by `S` lies in `localAt A W` as soon as the base lies in `A`
and `S` in `localAt A W`. -/
lemma closure_le_localAt {R A : Subring F} {W : ValuationSubring F} {S : Set F} (hR : R ≤ A)
    (hS : ∀ s ∈ S, s ∈ localAt A W) : Subring.closure ((R : Set F) ∪ S) ≤ localAt A W :=
  Subring.closure_le.2 (Set.union_subset (fun _ hx ↦ le_localAt (hR hx)) hS)

lemma valuation_eq_one_of_mem_of_inv_mem {W : ValuationSubring F} {x : F} (hx0 : x ≠ 0)
    (hx : x ∈ W) (hinv : x⁻¹ ∈ W) : W.valuation x = 1 :=
  (valuation_eq_one_iff_mem_and_inv_mem W).2 ⟨hx0, hx, hinv⟩

lemma eq_one_of_mul_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (hab : a * b = 1) : a = 1 := by
  refine le_antisymm ha (not_lt.1 fun hlt ↦ ?_)
  have : a * b < 1 := mul_lt_one_of_lt_of_le hlt hb
  rw [hab] at this
  exact lt_irrefl _ this

namespace ZariskiModel

open scoped Classical in
variable (v) in
/-- The **annulus model**: charts `O[y⁻¹]`, `O[y, c / y]` and `O[y / c]`. -/
noncomputable def annulus (y : F) (c : K) : ZariskiModel (baseRing F v.valuationSubring) where
  charts := {polyChart v y⁻¹, nodeChart v y c, polyChart v (y / algebraMap K F c)}
  le_chart A hA := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact baseRing_le_polyChart _
    · exact fun x hx ↦ Subring.subset_closure (Or.inl hx)
    · exact baseRing_le_polyChart _

variable {y : F} {c : K}

lemma mem_annulus_charts {A : Subring F} : A ∈ (annulus v y c).charts ↔
    A = polyChart v y⁻¹ ∨ A = nodeChart v y c ∨ A = polyChart v (y / algebraMap K F c) := by
  classical
  simp [annulus]

lemma baseRing_le_nodeChart : baseRing F v.valuationSubring ≤ nodeChart v y c :=
  fun _ hx ↦ Subring.subset_closure (Or.inl hx)

lemma self_mem_nodeChart : y ∈ nodeChart v y c :=
  Subring.subset_closure (Or.inr (Set.mem_insert _ _))

lemma div_mem_nodeChart : algebraMap K F c / y ∈ nodeChart v y c :=
  Subring.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

lemma nodeChart_le {A : Subring F} (hR : baseRing F v.valuationSubring ≤ A) (hy : y ∈ A)
    (hc : algebraMap K F c / y ∈ A) : nodeChart v y c ≤ A :=
  Subring.closure_le.2 (Set.union_subset hR (Set.insert_subset hy (Set.singleton_subset_iff.2 hc)))

lemma algebraMap_mem_baseRing' (hcO : v c ≤ 1) :
    algebraMap K F c ∈ baseRing F v.valuationSubring :=
  algebraMap_mem_baseRing hcO

/-- The annulus model is proper. -/
theorem annulus_isProper : (annulus v y c).IsProper := by
  intro W hW
  rcases W.mem_or_inv_mem y with hy | hy
  · rcases W.mem_or_inv_mem (y / algebraMap K F c) with hz | hz
    · exact ⟨_, mem_annulus_charts.2 (.inr (.inr rfl)), polyChart_le hW hz⟩
    · refine ⟨_, mem_annulus_charts.2 (.inr (.inl rfl)), nodeChart_le hW hy ?_⟩
      rwa [inv_div] at hz
  · exact ⟨_, mem_annulus_charts.2 (.inl rfl), polyChart_le hW hy⟩

theorem annulus_isFiniteType : (annulus v y c).IsFiniteType := by
  classical
  intro A hA
  rcases mem_annulus_charts.1 hA with rfl | rfl | rfl
  · exact ⟨{y⁻¹}, by simp [polyChart]⟩
  · exact ⟨{y, algebraMap K F c / y}, by simp [nodeChart]⟩
  · exact ⟨{y / algebraMap K F c}, by simp [polyChart]⟩

/-- The annulus model is separated. -/
theorem annulus_isSeparated (hy0 : y ≠ 0) (hc0 : c ≠ 0) (hcO : v c ≤ 1) :
    (annulus v y c).IsSeparated := by
  set R := baseRing F v.valuationSubring
  set γ := algebraMap K F c
  have hγ0 : γ ≠ 0 := by simpa [γ] using hc0
  have hγR : γ ∈ R := algebraMap_mem_baseRing hcO
  set z := y / γ
  have hz0 : z ≠ 0 := div_ne_zero hy0 hγ0
  set Y := polyChart v y⁻¹
  set N := nodeChart v y c
  set Z := polyChart v z
  have hRY : R ≤ Y := baseRing_le_polyChart _
  have hRN : R ≤ N := baseRing_le_nodeChart
  have hRZ : R ≤ Z := baseRing_le_polyChart _
  have hyY : y⁻¹ ∈ Y := self_mem_polyChart _
  have hyN : y ∈ N := self_mem_nodeChart
  have hγN : γ / y ∈ N := div_mem_nodeChart
  have hzZ : z ∈ Z := self_mem_polyChart _
  have hzinv : z⁻¹ = γ / y := inv_div y γ
  have hyz : y = γ * z := by simp only [z]; field_simp
  have hNgen : ∀ {A : Subring F} {W : ValuationSubring F}, R ≤ A → y ∈ localAt A W →
      γ / y ∈ localAt A W → N ≤ localAt A W := fun hR h₁ h₂ ↦
    closure_le_localAt hR fun s hs ↦ by
      rcases hs with rfl | hs
      · exact h₁
      · rw [Set.mem_singleton_iff.1 hs]; exact h₂
  have hYgen : ∀ {A : Subring F} {W : ValuationSubring F}, R ≤ A → y⁻¹ ∈ localAt A W →
      Y ≤ localAt A W := fun hR h ↦
    closure_le_localAt hR fun s hs ↦ by rw [Set.mem_singleton_iff.1 hs]; exact h
  have hZgen : ∀ {A : Subring F} {W : ValuationSubring F}, R ≤ A → z ∈ localAt A W →
      Z ≤ localAt A W := fun hR h ↦
    closure_le_localAt hR fun s hs ↦ by rw [Set.mem_singleton_iff.1 hs]; exact h
  -- `Y` and `N`
  have hYN : ∀ W : ValuationSubring F, Y ≤ W.toSubring → N ≤ W.toSubring →
      N ≤ localAt Y W ∧ Y ≤ localAt N W := by
    intro W hYW hNW
    have hy1 : W.valuation y = 1 :=
      valuation_eq_one_of_mem_of_inv_mem hy0 (hNW hyN) (hYW hyY)
    have hy1' : W.valuation y⁻¹ = 1 := by rw [map_inv₀, hy1, inv_one]
    refine ⟨hNgen hRY ?_ ?_, hYgen hRN (inv_mem_localAt hyN hy1)⟩
    · simpa using inv_mem_localAt hyY hy1'
    · rw [div_eq_mul_inv]
      exact le_localAt (Y.mul_mem (hRY hγR) hyY)
  -- `Z` and `N`
  have hZN : ∀ W : ValuationSubring F, Z ≤ W.toSubring → N ≤ W.toSubring →
      N ≤ localAt Z W ∧ Z ≤ localAt N W := by
    intro W hZW hNW
    have hz1 : W.valuation z = 1 :=
      valuation_eq_one_of_mem_of_inv_mem hz0 (hZW hzZ) (hzinv ▸ hNW hγN)
    have hz1' : W.valuation (γ / y) = 1 := by rw [← hzinv, map_inv₀, hz1, inv_one]
    refine ⟨hNgen hRZ ?_ ?_, hZgen hRN ?_⟩
    · rw [hyz]
      exact le_localAt (Z.mul_mem (hRZ hγR) hzZ)
    · rw [← hzinv]
      exact inv_mem_localAt hzZ hz1
    · simpa [hzinv] using inv_mem_localAt hγN hz1'
  -- `Y` and `Z`
  have hYZ : ∀ W : ValuationSubring F, Y ≤ W.toSubring → Z ≤ W.toSubring →
      Z ≤ localAt Y W ∧ Y ≤ localAt Z W := by
    intro W hYW hZW
    have hγW : W.valuation γ ≤ 1 := (W.valuation_le_one_iff _).2 (hYW (hRY hγR))
    have hzW : W.valuation z ≤ 1 := (W.valuation_le_one_iff _).2 (hZW hzZ)
    have hyW : W.valuation y ≤ 1 := by
      rw [hyz, map_mul]
      exact mul_le_one' hγW hzW
    have hy1 : W.valuation y = 1 := by
      refine le_antisymm hyW ?_
      have h := (W.valuation_le_one_iff _).2 (hYW hyY)
      rw [map_inv₀] at h
      exact one_le_of_inv_le_one (by simpa using hy0) h
    have hprod : W.valuation γ * W.valuation z = 1 := by rw [← map_mul, ← hyz, hy1]
    have hγ1 : W.valuation γ = 1 := eq_one_of_mul_eq_one hγW hzW hprod
    have hz1 : W.valuation z = 1 := by rw [hγ1, one_mul] at hprod; exact hprod
    have hy1' : W.valuation y⁻¹ = 1 := by rw [map_inv₀, hy1, inv_one]
    refine ⟨hZgen hRY ?_, hYgen hRZ ?_⟩
    · have : z = y⁻¹⁻¹ * γ⁻¹ := by simp only [z, inv_inv, div_eq_mul_inv]
      rw [this]
      exact Subring.mul_mem _ (inv_mem_localAt hyY hy1') (inv_mem_localAt (hRY hγR) hγ1)
    · have : y⁻¹ = γ⁻¹ * z⁻¹ := by rw [hyz, mul_inv]
      rw [this]
      exact Subring.mul_mem _ (inv_mem_localAt (hRZ hγR) hγ1) (inv_mem_localAt hzZ hz1)
  intro A hA B hB W hAW hBW
  rcases mem_annulus_charts.1 hA with rfl | rfl | rfl <;>
    rcases mem_annulus_charts.1 hB with rfl | rfl | rfl
  · exact le_localAt
  · exact (hYN W hAW hBW).1
  · exact (hYZ W hAW hBW).1
  · exact (hYN W hBW hAW).2
  · exact le_localAt
  · exact (hZN W hBW hAW).2
  · exact (hYZ W hBW hAW).2
  · exact (hZN W hAW hBW).1
  · exact le_localAt

variable {w₁ w₂ : Valuation F Γ₀}

/-- **The vertex set of the annulus model is `{O_{w₁}, O_{w₂}}`.** -/
theorem annulus_vertexSet (h₁ : IsGaussCoord v w₁ y)
    (h₂ : IsGaussCoord v w₂ (y / algebraMap K F c)) :
    (annulus v y c).vertexSet = {w₁.valuationSubring, w₂.valuationSubring} := by
  ext W
  constructor
  · intro hWv
    obtain ⟨A, hA, -, hloc⟩ := exists_localAt_eq_of_mem_vertexSet hWv
    rcases mem_annulus_charts.1 hA with rfl | rfl | rfl
    · obtain ⟨s, hs, hst⟩ := exists_isResidueTranscendental_of_localAt_eq hWv.1 hloc hWv.2.1
      rw [Set.mem_singleton_iff.1 hs] at hst
      exact .inl (h₁.inv.eq_of_isResidueTranscendental hWv.1 hst)
    · obtain ⟨s, hs, hst⟩ := exists_isResidueTranscendental_of_localAt_eq hWv.1 hloc hWv.2.1
      rcases hs with rfl | hs
      · exact .inl (h₁.eq_of_isResidueTranscendental hWv.1 hst)
      · rw [Set.mem_singleton_iff.1 hs, ← inv_div] at hst
        exact .inr (h₂.inv.eq_of_isResidueTranscendental hWv.1 hst)
    · obtain ⟨s, hs, hst⟩ := exists_isResidueTranscendental_of_localAt_eq hWv.1 hloc hWv.2.1
      rw [Set.mem_singleton_iff.1 hs] at hst
      exact .inr (h₂.eq_of_isResidueTranscendental hWv.1 hst)
  · rintro (rfl | rfl)
    · exact mem_vertexSet_of_localAt_eq h₁.comap_valuationSubring
        ⟨y⁻¹, h₁.inv.isResidueTranscendental⟩ (mem_annulus_charts.2 (.inl rfl))
        h₁.inv.polyChart_le_valuationSubring h₁.inv.localAt_polyChart
    · exact mem_vertexSet_of_localAt_eq h₂.comap_valuationSubring
        ⟨_, h₂.isResidueTranscendental⟩ (mem_annulus_charts.2 (.inr (.inr rfl)))
        h₂.polyChart_le_valuationSubring h₂.localAt_polyChart

/-! ### The charts as abstract rings -/

section Iso

local notation "𝒪" => v.valuationSubring

variable [Algebra v.valuationSubring F] [IsScalarTower v.valuationSubring K F]

omit [IsScalarTower v.valuationSubring K F] in
lemma range_algebraMap_eq_baseRing [IsScalarTower v.valuationSubring K F] :
    Set.range (algebraMap v.valuationSubring F) = baseRing F v.valuationSubring := by
  ext x
  constructor
  · rintro ⟨o, rfl⟩
    exact ⟨o, o.2, (IsScalarTower.algebraMap_apply v.valuationSubring K F o).symm⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨⟨o, ho⟩, IsScalarTower.algebraMap_apply v.valuationSubring K F ⟨o, ho⟩⟩

lemma toSubring_adjoin (S : Set F) :
    (Algebra.adjoin v.valuationSubring S).toSubring =
      Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ S) := by
  rw [Algebra.adjoin_eq_ring_closure, range_algebraMap_eq_baseRing]

variable {y : F} {c : K}

/-- `O[z]` is the image of `O[X]` under `X ↦ z`. -/
lemma range_aeval (z : F) :
    (aeval (R := v.valuationSubring) z).range.toSubring = polyChart v z := by
  rw [← Algebra.adjoin_singleton_eq_range_aeval, toSubring_adjoin]
  rfl

/-- `O[X] → O[z]`, `X ↦ z`, is injective for a Gauss coordinate `z`. -/
lemma aeval_injective' {w : Valuation F Γ₀} {z : F} (h : IsGaussCoord v w z) :
    Function.Injective (aeval (R := v.valuationSubring) z) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  rw [← aeval_map_algebraMap K, h.aeval_eq_zero_iff] at hP
  exact Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective v.valuationSubring K)
    (hP.trans (Polynomial.map_zero _).symm)

/-- `c` as an element of `O`. -/
def elemO (hcO : v c ≤ 1) : v.valuationSubring := ⟨c, hcO⟩

lemma nodeLift_mul (hy0 : y ≠ 0) (hcO : v c ≤ 1) :
    y * (algebraMap K F c / y) = algebraMap v.valuationSubring F (elemO hcO) := by
  rw [mul_div_cancel₀ _ hy0, IsScalarTower.algebraMap_apply v.valuationSubring K F]
  rfl

/-- The `O`-algebra map `Node O c → F`, `u ↦ y`, `v ↦ c / y`. -/
noncomputable def nodeLift (hy0 : y ≠ 0) (hcO : v c ≤ 1) :
    Node v.valuationSubring (elemO hcO) →ₐ[v.valuationSubring] F :=
  Node.lift y (algebraMap K F c / y) (nodeLift_mul hy0 hcO)

/-- **The node chart is the image of the node.** -/
theorem range_nodeLift (hy0 : y ≠ 0) (hcO : v c ≤ 1) :
    (nodeLift hy0 hcO).range.toSubring = nodeChart v y c := by
  rw [← Algebra.map_top, ← Node.adjoin_u_v, AlgHom.map_adjoin, Set.image_pair, nodeLift,
    Node.lift_u, Node.lift_v, toSubring_adjoin]
  rfl

open LaurentPolynomial in
/-- **The node chart is isomorphic to the node** `O[u, v] ⧸ (u v - c)`: the map `u ↦ y`,
`v ↦ c / y` is injective for a Gauss coordinate `y` and `c ≠ 0`. -/
theorem nodeLift_injective {w : Valuation F Γ₀} (h : IsGaussCoord v w y) (hc0 : c ≠ 0)
    (hcO : v c ≤ 1) : Function.Injective (nodeLift h.ne_zero hcO) := by
  set K' := FractionRing 𝒪
  have hO : Function.Injective (algebraMap 𝒪 K) := FaithfulSMul.algebraMap_injective 𝒪 K
  set ψ : K' →+* K := IsFractionRing.lift hO
  set φ : K' →+* F := (algebraMap K F).comp ψ
  have hφ (o : 𝒪) : φ (algebraMap 𝒪 K' o) = algebraMap 𝒪 F o := by
    simp only [φ, ψ, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    exact (IsScalarTower.algebraMap_apply 𝒪 K F o).symm
  set u : Fˣ := Units.mk0 y h.ne_zero
  set ε : K'[T;T⁻¹] →+* F := LaurentPolynomial.eval₂ φ u
  -- `ε` is injective
  have hε : Function.Injective ε := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    obtain ⟨n, f', hf'⟩ := exists_T_pow f
    have h0 : Polynomial.eval₂ φ y f' = 0 := by
      have := congrArg ε hf'
      rw [map_mul, hf, zero_mul, eval₂_toLaurent] at this
      exact this
    have h1 : aeval y (f'.map ψ) = 0 := by
      rw [aeval_def, eval₂_map]
      exact h0
    rw [h.aeval_eq_zero_iff] at h1
    have h2 : f' = 0 :=
      Polynomial.map_injective ψ ψ.injective (h1.trans (Polynomial.map_zero _).symm)
    rw [h2, map_zero] at hf'
    exact ((isUnit_T (n : ℤ)).mul_left_eq_zero).1 hf'.symm
  -- `ε` as an `𝒪`-algebra map
  let ε' : K'[T;T⁻¹] →ₐ[𝒪] F :=
    { ε with
      commutes' := fun o ↦ by
        change ε (algebraMap 𝒪 K'[T;T⁻¹] o) = _
        rw [LaurentPolynomial.algebraMap_apply, LaurentPolynomial.eval₂_C, hφ] }
  have hc' : elemO hcO ≠ 0 := fun h0 ↦ hc0 (congrArg Subtype.val h0)
  have heq : nodeLift h.ne_zero hcO = ε'.comp (Node.laurent (elemO hcO) 1) := by
    refine Node.algHom_ext ?_ ?_
    · rw [AlgHom.comp_apply, Node.laurent_u]
      change Node.lift _ _ _ (Node.u _) = ε (T ((1 : ℕ) : ℤ))
      rw [Node.lift_u]
      rw [eval₂_T_n, pow_one]
      rfl
    · rw [AlgHom.comp_apply, Node.laurent_v]
      change Node.lift _ _ _ (Node.v _) = _
      rw [Node.lift_v]
      change algebraMap K F c / y =
        ε (LaurentPolynomial.C (algebraMap 𝒪 K' (elemO hcO)) * T (-((1 : ℕ) : ℤ)))
      rw [eval₂_C_mul_T_neg_n, hφ, pow_one, div_eq_mul_inv]
      congr 1
      exact (IsScalarTower.algebraMap_apply 𝒪 K F (elemO hcO)).symm
  rw [heq]
  exact hε.comp (Node.laurent_injective hc' one_pos)

/-- The node chart is integrally closed (as a ring): it is isomorphic to the node, which is
normal (`Node.isIntegrallyClosed`). -/
theorem isIntegrallyClosed_nodeChart {w : Valuation F Γ₀} (h : IsGaussCoord v w y)
    (hc0 : c ≠ 0) (hcO : v c ≤ 1) : IsIntegrallyClosed (nodeChart v y c) := by
  have hc' : elemO hcO ≠ 0 := fun h0 ↦ hc0 (congrArg Subtype.val h0)
  have := Node.isIntegrallyClosed hc'
  let e : Node v.valuationSubring (elemO hcO) ≃+* (nodeLift h.ne_zero hcO).range :=
    (AlgEquiv.ofInjective _ (nodeLift_injective h hc0 hcO)).toRingEquiv
  have hr : (nodeLift h.ne_zero hcO).range.toSubring = nodeChart v y c := range_nodeLift _ _
  have : IsIntegrallyClosed (nodeLift h.ne_zero hcO).range := IsIntegrallyClosed.of_equiv e
  rw [← hr]
  exact this

/-! ### Semistability of the charts -/

/-- The `O`-algebra structure of a chart containing the base ring. -/
noncomputable abbrev chartAlgebra {A : Subring F} (hA : baseRing F 𝒪 ≤ A) : Algebra 𝒪 A :=
  ((algebraMap 𝒪 F).codRestrict A fun o ↦ hA (by
    rw [IsScalarTower.algebraMap_apply 𝒪 K F]
    exact ⟨o, o.2, rfl⟩)).toAlgebra

/-- A subalgebra with underlying subring `A` is isomorphic to `A`, for any `O`-algebra structure
on `A` compatible with the inclusion into `F`. -/
def equivChart (S : Subalgebra 𝒪 F) {A : Subring F} [Algebra 𝒪 A]
    (hcomp : ∀ o, ((algebraMap 𝒪 A o : A) : F) = algebraMap 𝒪 F o) (h : S.toSubring = A) :
    S ≃ₐ[𝒪] A where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, by rw [← Subalgebra.mem_toSubring, h]; exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' o := Subtype.ext (hcomp o).symm

omit [IsScalarTower (↥v.valuationSubring) K F] in
lemma chartAlgebra_algebraMap [IsScalarTower 𝒪 K F] {A : Subring F} (hA : baseRing F 𝒪 ≤ A)
    (o : 𝒪) :
    letI := chartAlgebra hA
    ((algebraMap 𝒪 A o : A) : F) = algebraMap 𝒪 F o :=
  rfl

/-- Semistability transports along isomorphisms of `O`-algebras. -/
lemma isSemistable_of_algEquiv {ϖ : 𝒪} {M A : Type u} [CommRing M] [Algebra 𝒪 M] [CommRing A]
    [Algebra 𝒪 A] (e : M ≃ₐ[𝒪] A) (h : IsSemistable ϖ M) : IsSemistable ϖ A :=
  h.of_etale e.toAlgHom (RingHom.Etale.of_bijective e.bijective)

variable {w₁ w₂ : Valuation F Γ₀}

/-- **The annulus model is semistable** (for `c = ϖ ^ n`): its charts, with any `O`-algebra
structure compatible with `F` (e.g. `chartAlgebra`), are `O`-isomorphic to the affine line `O[X]`
and to the node `O[u, v] ⧸ (u v - ϖ ^ n)`. -/
theorem annulus_isSemistable (h₁ : IsGaussCoord v w₁ y)
    (h₂ : IsGaussCoord v w₂ (y / algebraMap K F c)) {ϖ : 𝒪} {n : ℕ}
    (hc : c = ((ϖ ^ n : 𝒪) : K)) (hc0 : c ≠ 0) {A : Subring F}
    (hA : A ∈ (annulus v y c).charts) [Algebra 𝒪 A]
    (hcomp : ∀ o, ((algebraMap 𝒪 A o : A) : F) = algebraMap 𝒪 F o) :
    IsSemistable ϖ A := by
  have hcO : v c ≤ 1 := by rw [hc]; exact (ϖ ^ n).2
  rcases mem_annulus_charts.1 hA with rfl | rfl | rfl
  · exact isSemistable_of_algEquiv
      ((AlgEquiv.ofInjective _ (aeval_injective' h₁.inv)).trans
        (equivChart _ hcomp (range_aeval _))) IsSemistable.polynomial
  · have he : elemO hcO = ϖ ^ n := Subtype.ext hc
    have hN : IsSemistable ϖ (Node 𝒪 (elemO hcO)) := by
      rw [he]
      exact IsSemistable.node n
    exact isSemistable_of_algEquiv
      ((AlgEquiv.ofInjective _ (nodeLift_injective h₁ hc0 hcO)).trans
        (equivChart _ hcomp (range_nodeLift _ _))) hN
  · exact isSemistable_of_algEquiv
      ((AlgEquiv.ofInjective _ (aeval_injective' h₂)).trans
        (equivChart _ hcomp (range_aeval _))) IsSemistable.polynomial

end Iso

end ZariskiModel

/-! ### Two concentric Gauss valuations of `K(X)` -/

section RatFunc

variable {a c₁ c₂ : K} {r₁ r₂ : Γ₀ˣ}

lemma gaussCoord_div (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) :
    gaussCoord a c₁ / algebraMap K (RatFunc K) (c₂ / c₁) = gaussCoord a c₂ := by
  have e (b : K) : algebraMap K[X] (RatFunc K) (Polynomial.C b) = algebraMap K (RatFunc K) b := by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  have h₁ : algebraMap K (RatFunc K) c₁ ≠ 0 := by simpa using hc₁
  have h₂ : algebraMap K (RatFunc K) c₂ ≠ 0 := by simpa using hc₂
  simp only [gaussCoord, gaussLin, map_mul, map_sub, e, map_div₀, map_inv₀]
  field_simp

variable (v) in
/-- The annulus model of `K(X)` for the Gauss valuations `w_{a, r₁}` and `w_{a, r₂}`
(`v(cᵢ) = rᵢ`): charts `O[t₁⁻¹]`, `O[t₁, (c₂/c₁)/t₁]`, `O[t₂]`, `tᵢ = (X - a)/cᵢ`. -/
noncomputable def gaussAnnulusModel (a c₁ c₂ : K) :
    ZariskiModel (baseRing (RatFunc K) v.valuationSubring) :=
  ZariskiModel.annulus v (gaussCoord a c₁) (c₂ / c₁)

theorem gaussAnnulusModel_isProper : (gaussAnnulusModel v a c₁ c₂).IsProper :=
  ZariskiModel.annulus_isProper

theorem gaussAnnulusModel_isSeparated (hc₁ : v c₁ = r₁) (hc₂ : v c₂ = r₂) (hr : r₂ ≤ r₁) :
    (gaussAnnulusModel v a c₁ c₂).IsSeparated := by
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    exact r₁.ne_zero (by simp [← hc₁])
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    exact r₂.ne_zero (by simp [← hc₂])
  refine ZariskiModel.annulus_isSeparated (isGaussCoord_gaussCoord hc₁).ne_zero
    (div_ne_zero hc₂0 hc₁0) ?_
  rw [map_div₀, hc₁, hc₂]
  exact (div_le_one₀ (zero_lt_iff.2 r₁.ne_zero)).2 (Units.val_le_val.2 hr)

/-- **(iii) for two concentric discs:** the vertex set of the annulus model of `K(X)` is
`{O_{w_{a, r₁}}, O_{w_{a, r₂}}}`. -/
theorem gaussAnnulusModel_vertexSet (hc₁ : v c₁ = r₁) (hc₂ : v c₂ = r₂) :
    (gaussAnnulusModel v a c₁ c₂).vertexSet =
      {(gaussRat v a r₁).valuationSubring, (gaussRat v a r₂).valuationSubring} := by
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    exact r₁.ne_zero (by simp [← hc₁])
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    exact r₂.ne_zero (by simp [← hc₂])
  refine ZariskiModel.annulus_vertexSet (isGaussCoord_gaussCoord hc₁) ?_
  rw [gaussCoord_div hc₁0 hc₂0]
  exact isGaussCoord_gaussCoord hc₂

/-- **The annulus model of `K(X)` is semistable** when `c₂ / c₁ = ϖ ^ n`. -/
theorem gaussAnnulusModel_isSemistable (hc₁ : v c₁ = r₁) (hc₂ : v c₂ = r₂)
    {ϖ : v.valuationSubring} {n : ℕ} (hc : c₂ / c₁ = ((ϖ ^ n : v.valuationSubring) : K))
    {A : Subring (RatFunc K)} (hA : A ∈ (gaussAnnulusModel v a c₁ c₂).charts)
    [Algebra v.valuationSubring A]
    (hcomp : ∀ o, ((algebraMap v.valuationSubring A o : A) : RatFunc K) =
      algebraMap v.valuationSubring (RatFunc K) o) :
    IsSemistable ϖ A := by
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    exact r₁.ne_zero (by simp [← hc₁])
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    exact r₂.ne_zero (by simp [← hc₂])
  refine ZariskiModel.annulus_isSemistable (w₂ := gaussRat v a r₂) (isGaussCoord_gaussCoord hc₁)
    ?_ hc
    (div_ne_zero hc₂0 hc₁0) hA hcomp
  rw [gaussCoord_div hc₁0 hc₂0]
  exact isGaussCoord_gaussCoord hc₂

end RatFunc

end SemistableReduction
