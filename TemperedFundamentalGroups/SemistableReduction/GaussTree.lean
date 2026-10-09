/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.AnnulusModel

/-!
# The tree of projective lines of a convex set of Gauss points

Blueprint §9.6 (W5), layer M7b. Let `x ∈ F` and `a, c : ι → K` (`c i ≠ 0`), with coordinates
`t i = (x - a i) / c i` (for `F = K(X)`, `x = X`: the Gauss coordinates of the Gauss valuations
`w_{a i, |c i|}`, i.e. of the closed discs `D i = D(a i, |c i|)`). The discs are ordered by
inclusion (`DiscLE`); the family is **convex** if any two discs are contained in a member of the
family of radius at most `max(|c i|, |c j|, |a i - a j|)` (closure under joins of the Berkovich
tree), and **reduced** if distinct indices give distinct discs.

For a convex reduced nonempty family over a valuation ring `O` of rank at most one, every point of
the join model `ZariskiModel.lines v t` is the point of a line chart or of a node chart
(`center_lines_eq`): for a valuation subring `W ⊇ O` of `F`, the local ring of the join model at
the center of `W` is `localAt B W` for `B` one of

* `O[t i]` or `O[(t ρ)⁻¹]` (`ρ` the root: a smooth point of a component),
* `O[u, c' / u]` with `u = (x - a j) / c m`, `c' = c j / c m`, for a disc `D j ⊊ D m` (a node,
  the local model of the annulus between `D j` and `D m`, `AnnulusModel`).

The proof locates the center of `W`: `m` is the smallest disc containing `W` (the discs containing
`W` form a chain, `discLE_or_discLE_of_mem`), and the center is a node if `W` specializes into
the residue disc of a child `j` of `m` (chosen of maximal radius; convexity shows that every disc
below `m` in that residue disc lies below `j`). All the other coordinates are then units or
inverses of units in the local ring of `B` (explicit affine relations between the coordinates).
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel

namespace GaussTree

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

local notation "⟪" k "⟫" => algebraMap K F k

/-- The coordinate `(x - a) / c`. -/
def coord (x : F) (a c : K) : F :=
  (x - ⟪a⟫) / ⟪c⟫

section Identities

variable {x : F} {a a' c c' : K}

lemma coord_eq_mul_add (hc : c ≠ 0) (hc' : c' ≠ 0) :
    coord x a' c' = ⟪c / c'⟫ * coord x a c + ⟪(a - a') / c'⟫ := by
  have h₁ : ⟪c⟫ ≠ 0 := by simpa using hc
  have h₂ : ⟪c'⟫ ≠ 0 := by simpa using hc'
  simp only [coord, map_div₀, map_sub]
  field_simp
  ring

lemma coord_sub (hc : c ≠ 0) (hc' : c' ≠ 0) :
    coord x a' c' - ⟪(a - a') / c'⟫ = ⟪c / c'⟫ * coord x a c := by
  rw [coord_eq_mul_add hc hc', add_sub_cancel_right]

lemma coord_sub_eq_coord (hc' : c' ≠ 0) :
    coord x a' c' - ⟪(a - a') / c'⟫ = coord x a c' := by
  have h₂ : ⟪c'⟫ ≠ 0 := by simpa using hc'
  simp only [coord, map_div₀, map_sub]
  field_simp
  ring

lemma coord_relation (hc : c ≠ 0) (hc' : c' ≠ 0) (he : a - a' ≠ 0) :
    ⟪c' / (a - a')⟫ * coord x a' c' - ⟪c / (a - a')⟫ * coord x a c = 1 := by
  have h₁ : ⟪c⟫ ≠ 0 := by simpa using hc
  have h₂ : ⟪c'⟫ ≠ 0 := by simpa using hc'
  have h₃ : ⟪a⟫ - ⟪a'⟫ ≠ 0 := by
    rw [← map_sub]
    exact (map_ne_zero_iff _ (algebraMap K F).injective).2 he
  simp only [coord, map_div₀, map_sub]
  field_simp
  ring

lemma div_coord_eq_inv (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ⟪c / c'⟫ / coord x a c' = (coord x a c)⁻¹ := by
  have h₁ : ⟪c⟫ ≠ 0 := by simpa using hc
  have h₂ : ⟪c'⟫ ≠ 0 := by simpa using hc'
  simp only [coord, map_div₀]
  rcases eq_or_ne (x - ⟪a⟫) 0 with h | h
  · simp [h]
  · field_simp

end Identities

/-! ### Valuations of constants -/

section Constants

variable {W : ValuationSubring F}

lemma algebraMap_mem_iff (hW : W.comap (algebraMap K F) = v.valuationSubring) {k : K} :
    ⟪k⟫ ∈ W ↔ v k ≤ 1 := by
  rw [← ValuationSubring.mem_comap, hW, Valuation.mem_valuationSubring_iff]

lemma valuation_algebraMap_le_one_iff (hW : W.comap (algebraMap K F) = v.valuationSubring)
    {k : K} : W.valuation ⟪k⟫ ≤ 1 ↔ v k ≤ 1 := by
  rw [W.valuation_le_one_iff, algebraMap_mem_iff hW]

lemma valuation_algebraMap_lt_one_iff (hW : W.comap (algebraMap K F) = v.valuationSubring)
    {k : K} : W.valuation ⟪k⟫ < 1 ↔ v k < 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  constructor
  · intro h
    refine lt_of_le_of_ne ((valuation_algebraMap_le_one_iff hW).1 h.le) fun h1 ↦ ?_
    have := valuation_eq_one_of_comap_eq hW hk (show k ∈ v.valuationSubring from h1.le)
      (show v k⁻¹ ≤ 1 by rw [map_inv₀, h1, inv_one])
    exact (lt_irrefl _ (this ▸ h))
  · intro h
    refine valuation_lt_one_of_comap_eq hW (show v k ≤ 1 from h.le) ?_
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, not_le]
    exact one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 (by simpa using hk), h⟩

end Constants

/-! ### Discs -/

section Discs

variable (v) {ι : Type*} (a c : ι → K)

/-- The disc `D(a i, |c i|)` is contained in `D(a j, |c j|)`. -/
def DiscLE (i j : ι) : Prop :=
  v (c i) ≤ v (c j) ∧ v (a i - a j) ≤ v (c j)

variable {v a c}

lemma DiscLE.refl (i : ι) : DiscLE v a c i i := ⟨le_rfl, by simp⟩

lemma DiscLE.trans {i j k : ι} (hij : DiscLE v a c i j) (hjk : DiscLE v a c j k) :
    DiscLE v a c i k := by
  refine ⟨hij.1.trans hjk.1, ?_⟩
  calc v (a i - a k) = v ((a i - a j) + (a j - a k)) := by ring_nf
    _ ≤ max (v (a i - a j)) (v (a j - a k)) := v.map_add _ _
    _ ≤ v (c k) := max_le (hij.2.trans hjk.1) hjk.2

lemma DiscLE.div_le_one {i j : ι} (h : DiscLE v a c i j) (hc : ∀ i, c i ≠ 0) :
    v (c i / c j) ≤ 1 ∧ v ((a i - a j) / c j) ≤ 1 := by
  have hpos : 0 < v (c j) := zero_lt_iff.2 (by simpa using hc j)
  rw [map_div₀, map_div₀, div_le_one₀ hpos, div_le_one₀ hpos]
  exact h

/-- Incomparable discs are far apart. -/
lemma lt_of_not_discLE {i j : ι} (h₁ : ¬DiscLE v a c i j) (h₂ : ¬DiscLE v a c j i) :
    v (c j) < v (a i - a j) ∧ v (c i) < v (a i - a j) := by
  have hsw : v (a j - a i) = v (a i - a j) := Valuation.map_sub_swap _ _ _
  constructor
  · by_contra hle
    push Not at hle
    rcases le_total (v (c i)) (v (c j)) with h | h
    · exact h₁ ⟨h, hle⟩
    · exact h₂ ⟨h, hsw ▸ hle.trans h⟩
  · by_contra hle
    push Not at hle
    rcases le_total (v (c j)) (v (c i)) with h | h
    · exact h₂ ⟨h, hsw ▸ hle⟩
    · exact h₁ ⟨h, hle.trans h⟩

end Discs

/-! ### Membership in local rings -/

section LocalRing

variable {x : F} {B : Subring F} {W : ValuationSubring F}
  (hRB : baseRing F v.valuationSubring ≤ B)

include hRB in
lemma algebraMap_mem_of_le_one {k : K} (hk : v k ≤ 1) : ⟪k⟫ ∈ B :=
  hRB (algebraMap_mem_baseRing hk)

/-- (L1) An affine function of a coordinate with coefficients in the local ring. -/
lemma coord_mem_localAt {a a' c c' : K} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hm : coord x a c ∈ localAt B W) (hγ : ⟪c / c'⟫ ∈ localAt B W)
    (hδ : ⟪(a - a') / c'⟫ ∈ localAt B W) : coord x a' c' ∈ localAt B W := by
  rw [coord_eq_mul_add hc hc']
  exact Subring.add_mem _ (Subring.mul_mem _ hγ hm) hδ

include hRB in
/-- (L2) The inverse of the coordinate of a disc incomparable with a disc `D(a, c)` whose
coordinate lies in `B` and in `W` (`W ∩ K = O`). -/
lemma inv_coord_mem_localAt_of_far {a a' c c' : K} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hW : W.comap (algebraMap K F) = v.valuationSubring) (hm : coord x a c ∈ B)
    (hmW : coord x a c ∈ W) (hfar : v c < v (a' - a)) (hfar' : v c' < v (a' - a)) :
    (coord x a' c')⁻¹ ∈ localAt B W := by
  have he : a' - a ≠ 0 := by
    rintro h
    rw [h, map_zero] at hfar
    exact not_lt_zero hfar
  have hepos : 0 < v (a' - a) := zero_lt_iff.2 ((v.ne_zero_iff).2 he)
  have h₁ : v (c / (a' - a)) < 1 := by rw [map_div₀, div_lt_one₀ hepos]; exact hfar
  have h₂ : v (c' / (a' - a)) ≤ 1 := by rw [map_div₀, div_le_one₀ hepos]; exact hfar'.le
  set s := ⟪c / (a' - a)⟫ * coord x a c - 1
  have hrel := coord_relation (x := x) hc' hc he
  have hsB : s ∈ B := B.sub_mem (B.mul_mem (algebraMap_mem_of_le_one hRB h₁.le) hm) B.one_mem
  have hsW : W.valuation s = 1 := by
    have hsmall : W.valuation (⟪c / (a' - a)⟫ * coord x a c) < 1 := by
      rw [map_mul]
      exact mul_lt_one_of_lt_of_le ((valuation_algebraMap_lt_one_iff hW).2 h₁)
        ((W.valuation_le_one_iff _).2 hmW)
    rw [Valuation.map_sub_eq_of_lt_right _ (by rwa [map_one])]
    exact map_one _
  have hs0 : s ≠ 0 := by
    rintro h
    rw [h, map_zero] at hsW
    exact zero_ne_one hsW
  have hγ0 : ⟪c' / (a' - a)⟫ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K F).injective]
    exact div_ne_zero hc' he
  have heq : (coord x a' c')⁻¹ = ⟪c' / (a' - a)⟫ * s⁻¹ := by
    have : ⟪c' / (a' - a)⟫ * coord x a' c' = s := by
      simp only [s]
      linear_combination (-1 : F) * hrel
    rw [← this, mul_inv, ← mul_assoc, mul_inv_cancel₀ hγ0, one_mul]
  rw [heq]
  exact Subring.mul_mem _ (le_localAt (algebraMap_mem_of_le_one hRB h₂))
    (inv_mem_localAt hsB hsW)

include hRB in
/-- (L3) The inverse of the coordinate of a disc `D(a', c') ⊆ D(a, c)` when the center of `W`
is not in the residue disc of `a'` (`t - δ` is a `W`-unit). -/
lemma inv_coord_mem_localAt_of_unit {a a' c c' : K} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hm : coord x a c ∈ B) (hγ : v (c' / c) ≤ 1) (hδ : v ((a' - a) / c) ≤ 1)
    (hunit : W.valuation (coord x a c - ⟪(a' - a) / c⟫) = 1) :
    (coord x a' c')⁻¹ ∈ localAt B W := by
  set s := coord x a c - ⟪(a' - a) / c⟫
  have hsB : s ∈ B := B.sub_mem hm (algebraMap_mem_of_le_one hRB hδ)
  have hs : s = ⟪c' / c⟫ * coord x a' c' := coord_sub hc' hc
  have hs0 : s ≠ 0 := by
    rintro h
    rw [h, map_zero] at hunit
    exact zero_ne_one hunit
  have hγ0 : ⟪c' / c⟫ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K F).injective]
    exact div_ne_zero hc' hc
  have heq : (coord x a' c')⁻¹ = ⟪c' / c⟫ * s⁻¹ := by
    rw [hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ hγ0, one_mul]
  rw [heq]
  exact Subring.mul_mem _ (le_localAt (algebraMap_mem_of_le_one hRB hγ))
    (inv_mem_localAt hsB hunit)

/-- (L4) The inverse of the coordinate of a disc contained in a disc `D(a, c)` whose coordinate is
not in `W` and has its inverse in `B`. -/
lemma inv_coord_mem_localAt_of_inv {a a' c c' : K} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hj : (coord x a c)⁻¹ ∈ B) (hjW : coord x a c ∉ W) (hγ : ⟪c' / c⟫ ∈ localAt B W)
    (hδ : ⟪(a' - a) / c⟫ ∈ localAt B W) (hδW : ⟪(a' - a) / c⟫ ∈ W) :
    (coord x a' c')⁻¹ ∈ localAt B W := by
  set t := coord x a c
  have ht0 : t ≠ 0 := by
    rintro h
    exact hjW (h ▸ W.zero_mem)
  have htinv : W.valuation t⁻¹ < 1 := by
    have h := W.mem_or_inv_mem t
    have hinvW : t⁻¹ ∈ W := h.resolve_left hjW
    refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 hinvW) fun h1 ↦ hjW ?_
    rw [← W.valuation_le_one_iff]
    rw [map_inv₀] at h1
    rw [inv_eq_one.1 h1]
  set s := 1 - ⟪(a' - a) / c⟫ * t⁻¹
  have hsL : s ∈ localAt B W :=
    Subring.sub_mem _ (Subring.one_mem _) (Subring.mul_mem _ hδ (le_localAt hj))
  have hsW : W.valuation s = 1 := by
    have hsmall : W.valuation (⟪(a' - a) / c⟫ * t⁻¹) < 1 := by
      rw [map_mul]
      rw [mul_comm]
      exact mul_lt_one_of_lt_of_le htinv ((W.valuation_le_one_iff _).2 hδW)
    rw [Valuation.map_one_sub_of_lt _ hsmall]
  have hs0 : s ≠ 0 := by
    rintro h
    rw [h, map_zero] at hsW
    exact zero_ne_one hsW
  have hrel : t = ⟪c' / c⟫ * coord x a' c' + ⟪(a' - a) / c⟫ := coord_eq_mul_add hc' hc
  have hγ0 : ⟪c' / c⟫ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K F).injective]
    exact div_ne_zero hc' hc
  have hts : t * s = t - ⟪(a' - a) / c⟫ := by
    simp only [s]
    field_simp
  have hkey : ⟪c' / c⟫ * coord x a' c' = t * s := by
    rw [hts, hrel]
    ring
  have hu0 : coord x a' c' ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hkey
    exact mul_ne_zero ht0 hs0 hkey.symm
  have heq : (coord x a' c')⁻¹ = ⟪c' / c⟫ * t⁻¹ * s⁻¹ := by
    field_simp
    rw [← hkey, mul_comm]
  rw [heq]
  exact Subring.mul_mem _ (Subring.mul_mem _ hγ (le_localAt hj))
    (inv_mem_localAt_of_mem hsL hsW)

/-- (L5) Discs whose coordinates lie in `W` (with `W ∩ K = O`) are comparable. -/
lemma discLE_or_discLE_of_mem {ι : Type*} {a c : ι → K} (hc : ∀ i, c i ≠ 0)
    (hW : W.comap (algebraMap K F) = v.valuationSubring) {i j : ι}
    (hi : coord x (a i) (c i) ∈ W) (hj : coord x (a j) (c j) ∈ W) :
    DiscLE v a c i j ∨ DiscLE v a c j i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hlt₁, hlt₂⟩ := lt_of_not_discLE hcon.1 hcon.2
  have he : a i - a j ≠ 0 := by
    rintro h
    rw [h, map_zero] at hlt₁
    exact not_lt_zero hlt₁
  have hepos : 0 < v (a i - a j) := zero_lt_iff.2 ((v.ne_zero_iff).2 he)
  have hrel := coord_relation (x := x) (hc i) (hc j) he
  have h₁ : W.valuation ⟪c j / (a i - a j)⟫ < 1 := by
    rw [valuation_algebraMap_lt_one_iff hW, map_div₀, div_lt_one₀ hepos]
    exact hlt₁
  have h₂ : W.valuation ⟪c i / (a i - a j)⟫ < 1 := by
    rw [valuation_algebraMap_lt_one_iff hW, map_div₀, div_lt_one₀ hepos]
    exact hlt₂
  have : W.valuation (1 : F) < 1 := by
    rw [← hrel]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_) <;> rw [map_mul]
    · exact mul_lt_one_of_lt_of_le h₁ ((W.valuation_le_one_iff _).2 hj)
    · exact mul_lt_one_of_lt_of_le h₂ ((W.valuation_le_one_iff _).2 hi)
  rw [map_one] at this
  exact lt_irrefl _ this

end LocalRing

/-! ### Convex families of discs -/

section Tree

variable (v) {ι : Type*} (a c : ι → K)

/-- The family of discs is **convex**: any two discs lie in a member of the family of radius at
most `max(|c i|, |c j|, |a i - a j|)` (closure under joins in the Berkovich tree). -/
def IsConvex : Prop :=
  ∀ i j, ∃ k, DiscLE v a c i k ∧ DiscLE v a c j k ∧
    v (c k) ≤ max (max (v (c i)) (v (c j))) (v (a i - a j))

/-- The family is **reduced**: distinct indices give distinct discs. -/
def IsReduced : Prop :=
  ∀ i j, DiscLE v a c i j → DiscLE v a c j i → i = j

variable {v a c}

lemma discLE_symm_of_eq {i j : ι} (h : DiscLE v a c i j) (he : v (c i) = v (c j)) :
    DiscLE v a c j i :=
  ⟨he.ge, by rw [Valuation.map_sub_swap, he]; exact h.2⟩

/-- A convex reduced nonempty finite family has a root containing all discs. -/
lemma exists_root [Finite ι] [Nonempty ι] (hconv : IsConvex v a c) (hred : IsReduced v a c) :
    ∃ ρ, ∀ i, DiscLE v a c i ρ := by
  obtain ⟨ρ, hρ⟩ := Finite.exists_max fun i ↦ v (c i)
  refine ⟨ρ, fun i ↦ ?_⟩
  obtain ⟨k, hik, hρk, -⟩ := hconv i ρ
  have he : v (c ρ) = v (c k) := le_antisymm hρk.1 (hρ k)
  rw [hred ρ k hρk (discLE_symm_of_eq hρk he)]
  exact hik

variable {x : F} {W : ValuationSubring F}

/-- The generator of the join chart contained in `W`: `t i` or `(t i)⁻¹`. -/
noncomputable def gen (x : F) (a c : ι → K) (W : ValuationSubring F) (i : ι) : F :=
  open scoped Classical in if (coord x (a i) (c i)) ∈ W then coord x (a i) (c i)
    else (coord x (a i) (c i))⁻¹

variable (v x a c W) in
/-- The chart of the join model contained in `W`. -/
noncomputable def joinChart : Subring F :=
  open scoped Classical in
  baseRing F v.valuationSubring ⊔ ⨆ i, if (coord x (a i) (c i)) ∈ W then
    polyChart v (coord x (a i) (c i))
    else polyChart v (coord x (a i) (c i))⁻¹

/-- The "convexity step": among the discs below `m` in the residue disc of the center of `W`, the
one of maximal radius contains all others. -/
lemma discLE_of_residue {m i j : ι} (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hc : ∀ i, c i ≠ 0) (hW : W.comap (algebraMap K F) = v.valuationSubring)
    (him : DiscLE v a c i m) (hi : i ≠ m)
    (hiW : W.valuation ((coord x (a m) (c m)) - ⟪(a i - a m) / c m⟫) < 1)
    (hjm : DiscLE v a c j m) (hj : j ≠ m)
    (hjW : W.valuation ((coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫) < 1)
    (hjmax : ∀ k, DiscLE v a c k m → k ≠ m →
      W.valuation ((coord x (a m) (c m)) - ⟪(a k - a m) / c m⟫) < 1 → v (c k) ≤ v (c j)) :
    DiscLE v a c i j := by
  have hcm : 0 < v (c m) := zero_lt_iff.2 ((v.ne_zero_iff).2 (hc m))
  have hvi : v (c i) < v (c m) :=
    lt_of_le_of_ne him.1 fun he ↦ hi (hred i m him (discLE_symm_of_eq him he))
  have hvj : v (c j) < v (c m) :=
    lt_of_le_of_ne hjm.1 fun he ↦ hj (hred j m hjm (discLE_symm_of_eq hjm he))
  have hij : v (a i - a j) < v (c m) := by
    have h : W.valuation ⟪(a j - a m) / c m - (a i - a m) / c m⟫ < 1 := by
      have : ⟪(a j - a m) / c m - (a i - a m) / c m⟫ =
          ((coord x (a m) (c m)) - ⟪(a i - a m) / c m⟫) -
            ((coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫) := by
        rw [map_sub]; ring
      rw [this]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hiW hjW)
    rw [valuation_algebraMap_lt_one_iff hW, ← sub_div, map_div₀, div_lt_one₀ hcm,
      show a j - a m - (a i - a m) = a j - a i by ring, Valuation.map_sub_swap] at h
    exact h
  obtain ⟨k, hik, hjk, hk⟩ := hconv i j
  have hkm : v (c k) < v (c m) := lt_of_le_of_lt hk (max_lt (max_lt hvi hvj) hij)
  have hjk' : v (a j - a k) ≤ v (c k) := hjk.2
  have hkm' : DiscLE v a c k m := by
    refine ⟨hkm.le, ?_⟩
    calc v (a k - a m) = v ((a j - a m) - (a j - a k)) := by ring_nf
      _ ≤ max (v (a j - a m)) (v (a j - a k)) := Valuation.map_sub _ _ _
      _ ≤ v (c m) := max_le hjm.2 (hjk'.trans hkm.le)
  have hkne : k ≠ m := by
    rintro rfl
    exact lt_irrefl _ hkm
  have hkW : W.valuation ((coord x (a m) (c m)) - ⟪(a k - a m) / c m⟫) < 1 := by
    have hsplit : (coord x (a m) (c m)) - ⟪(a k - a m) / c m⟫ =
        ((coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫) + ⟪(a j - a k) / c m⟫ := by
      rw [show (a k - a m) / c m = (a j - a m) / c m - (a j - a k) / c m by
        rw [div_sub_div_same]; ring_nf, map_sub]
      ring
    have hsmall : W.valuation ⟪(a j - a k) / c m⟫ < 1 := by
      rw [valuation_algebraMap_lt_one_iff hW, map_div₀, div_lt_one₀ hcm]
      exact lt_of_le_of_lt hjk' hkm
    rw [hsplit]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hjW hsmall)
  have hkj : v (c k) ≤ v (c j) := hjmax k hkm' hkne hkW
  have hjk_eq : j = k := hred j k hjk (discLE_symm_of_eq hjk (le_antisymm hjk.1 hkj))
  subst hjk_eq
  exact hik

variable (v x a c) in
/-- The **standard charts**: the line charts `O[t i]`, `O[(t i)⁻¹]` (`≅ O[X]`) and the node charts
`O[u, c' / u]`, `u = (x - a j) / c m`, `c' = c j / c m`, for `D j ⊊ D m` (`≅ Node O c'`). -/
def IsStandardChart (B : Subring F) : Prop :=
  (∃ i, B = polyChart v (coord x (a i) (c i))) ∨ (∃ i, B = polyChart v (coord x (a i) (c i))⁻¹) ∨
    ∃ j m, DiscLE v a c j m ∧ j ≠ m ∧ B = nodeChart v (coord x (a j) (c m)) (c j / c m)

lemma gen_of_mem {i : ι} (h : (coord x (a i) (c i)) ∈ W) : gen x a c W i = coord x (a i) (c i) := by
  classical
  simp [gen, h]

lemma gen_of_notMem {i : ι} (h : (coord x (a i) (c i)) ∉ W) :
    gen x a c W i = (coord x (a i) (c i))⁻¹ := by
  classical
  simp [gen, h]

lemma mem_joinChart_of_mem {i : ι} (h : (coord x (a i) (c i)) ∈ W) :
    (coord x (a i) (c i)) ∈ joinChart v a c x W := by
  classical
  refine (le_iSup (fun i ↦ if (coord x (a i) (c i)) ∈ W then polyChart v (coord x (a i) (c i))
    else polyChart v (coord x (a i) (c i))⁻¹) i
    |>.trans le_sup_right) ?_
  simp only [h, if_true]
  exact self_mem_polyChart _

lemma inv_mem_joinChart_of_notMem {i : ι} (h : (coord x (a i) (c i)) ∉ W) :
    (coord x (a i) (c i))⁻¹ ∈ joinChart v a c x W := by
  classical
  refine (le_iSup (fun i ↦ if (coord x (a i) (c i)) ∈ W then polyChart v (coord x (a i) (c i))
    else polyChart v (coord x (a i) (c i))⁻¹) i
    |>.trans le_sup_right) ?_
  simp only [h, if_false]
  exact self_mem_polyChart _

lemma baseRing_le_joinChart : baseRing F v.valuationSubring ≤ joinChart v a c x W :=
  le_sup_left

lemma joinChart_le (hW : baseRing F v.valuationSubring ≤ W.toSubring) :
    joinChart v a c x W ≤ W.toSubring := by
  classical
  refine sup_le hW (iSup_le fun i ↦ ?_)
  split_ifs with h
  · exact polyChart_le hW h
  · exact polyChart_le hW ((W.mem_or_inv_mem _).resolve_left h)

/-- The local ring of the join chart is that of `B` as soon as `B` lies in the join chart and the
generators of the join chart lie in the local ring of `B`. -/
lemma localAt_joinChart_eq {B : Subring F} (hRB : baseRing F v.valuationSubring ≤ B)
    (hBC : B ≤ joinChart v a c x W) (hgen : ∀ i, gen x a c W i ∈ localAt B W) :
    localAt (joinChart v a c x W) W = localAt B W := by
  classical
  refine localAt_eq_of_le hBC (sup_le (hRB.trans le_localAt) (iSup_le fun i ↦ ?_))
  have h := hgen i
  split_ifs with hi
  · rw [gen_of_mem hi] at h
    exact polyChart_le (hRB.trans le_localAt) h
  · rw [gen_of_notMem hi] at h
    exact polyChart_le (hRB.trans le_localAt) h

omit [LinearOrderedCommGroupWithZero Γ₀] in
lemma algebraMap_mem_localAt_of_forall {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} {B : Subring F} (hRB : baseRing F v.valuationSubring ≤ B)
    (hK : ∀ k : K, ⟪k⟫ ∈ W) (k : K) : ⟪k⟫ ∈ localAt B W := by
  by_cases hk : v k ≤ 1
  · exact le_localAt (algebraMap_mem_of_le_one hRB hk)
  · have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
    have hinv : v k⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (not_le.1 hk).le
    have hs : ⟪k⁻¹⟫ ∈ B := algebraMap_mem_of_le_one hRB hinv
    have hs1 : W.valuation ⟪k⁻¹⟫ = 1 :=
      valuation_eq_one_of_mem_of_inv_mem (by simpa using hk0) (hK _)
        (by rw [← map_inv₀, inv_inv]; exact hK k)
    have := inv_mem_localAt hs hs1
    rwa [← map_inv₀, inv_inv] at this

/-- **(M7b) Every point of the join model of a convex family of discs is standard**: for a
valuation subring `W ⊇ O` of `F` (`O` of rank at most one), the local ring of the join chart at
the center of `W` is `localAt B W` for a standard chart `B ⊆ W` (a line chart or a node chart). -/
theorem exists_standard_localAt_eq [Finite ι] [Nonempty ι] (hc : ∀ i, c i ≠ 0)
    (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hrank : ∀ O' : ValuationSubring K, v.valuationSubring ≤ O' →
      O' = v.valuationSubring ∨ O' = ⊤)
    (hW : baseRing F v.valuationSubring ≤ W.toSubring) :
    ∃ B, IsStandardChart v a c x B ∧ B ≤ W.toSubring ∧ B ≤ joinChart v a c x W ∧
      localAt (joinChart v a c x W) W = localAt B W := by
  classical
  haveI := Fintype.ofFinite ι
  set R := baseRing F v.valuationSubring
  obtain ⟨ρ, hρ⟩ := exists_root hconv hred
  have hRC : R ≤ joinChart v a c x W := baseRing_le_joinChart
  have hK1 {i j : ι} (h : DiscLE v a c i j) {B : Subring F} (hRB : R ≤ B) :
      ⟪c i / c j⟫ ∈ B ∧ ⟪(a i - a j) / c j⟫ ∈ B :=
    ⟨algebraMap_mem_of_le_one hRB (h.div_le_one hc).1,
      algebraMap_mem_of_le_one hRB (h.div_le_one hc).2⟩
  rcases hrank _ (baseRing_le_iff.1 hW) with hWO | hWK
  · by_cases hI : ∃ i, (coord x (a i) (c i)) ∈ W
    · obtain ⟨m, hmW, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter fun i ↦ (coord x (a i) (c i)) ∈ W) (fun i ↦ v (c i))
        (by obtain ⟨i, hi⟩ := hI; exact ⟨i, by simpa using hi⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmW hmin
      have hbelow : ∀ i, (coord x (a i) (c i)) ∈ W → DiscLE v a c m i := by
        intro i hi
        rcases discLE_or_discLE_of_mem hc hWO hmW hi with h | h
        · exact h
        · exact discLE_symm_of_eq h (le_antisymm h.1 (hmin i hi))
      have habove : ∀ i, DiscLE v a c m i → (coord x (a i) (c i)) ∈ W := by
        intro i h
        rw [coord_eq_mul_add (a := a m) (hc m) (hc i)]
        obtain ⟨h₁, h₂⟩ := hK1 h hW
        exact W.add_mem _ _ (W.mul_mem _ _ h₁ hmW) h₂
      have hδW (i : ι) (h : DiscLE v a c i m) : ⟪(a i - a m) / c m⟫ ∈ W := (hK1 h hW).2
      have hunit (i : ι) (h : DiscLE v a c i m)
          (hn : ¬W.valuation ((coord x (a m) (c m)) - ⟪(a i - a m) / c m⟫) < 1) :
          W.valuation ((coord x (a m) (c m)) - ⟪(a i - a m) / c m⟫) = 1 :=
        le_antisymm ((W.valuation_le_one_iff _).2 (sub_mem hmW (hδW i h))) (not_lt.1 hn)
      by_cases hS : ∃ j, DiscLE v a c j m ∧ j ≠ m ∧
          W.valuation ((coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫) < 1
      · obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image
          (Finset.univ.filter fun j ↦ DiscLE v a c j m ∧ j ≠ m ∧
            W.valuation ((coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫) < 1) (fun j ↦ v (c j))
          (by obtain ⟨j, hj⟩ := hS; exact ⟨j, by simpa using hj⟩)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjS hjmax
        obtain ⟨hjm, hjne, hjres⟩ := hjS
        set u := coord x (a j) (c m)
        set N := nodeChart v u (c j / c m)
        have hRN : R ≤ N := baseRing_le_nodeChart
        have hu : u = (coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫ :=
          (coord_sub_eq_coord (hc m)).symm
        have hdiv : ⟪c j / c m⟫ / u = (coord x (a j) (c j))⁻¹ := div_coord_eq_inv (hc j) (hc m)
        have htmN : (coord x (a m) (c m)) ∈ N := by
          have : (coord x (a m) (c m)) = u + ⟪(a j - a m) / c m⟫ := by rw [hu]; ring
          rw [this]
          exact N.add_mem self_mem_nodeChart (hK1 hjm hRN).2
        have htjN : (coord x (a j) (c j))⁻¹ ∈ N := hdiv ▸ div_mem_nodeChart
        have hjW : (coord x (a j) (c j)) ∉ W := fun h ↦ hjne (hred j m hjm (hbelow j h))
        refine ⟨N, .inr (.inr ⟨j, m, hjm, hjne, rfl⟩), ?_, ?_, localAt_joinChart_eq hRN ?_ ?_⟩
        · refine nodeChart_le hW (hu ▸ sub_mem hmW (hδW j hjm)) (hdiv ▸ ?_)
          exact (W.mem_or_inv_mem _).resolve_left hjW
        · exact nodeChart_le hRC (hu ▸ Subring.sub_mem _ (mem_joinChart_of_mem hmW)
            (hRC (hK1 hjm le_rfl).2)) (hdiv ▸ inv_mem_joinChart_of_notMem hjW)
        · exact nodeChart_le hRC (hu ▸ Subring.sub_mem _ (mem_joinChart_of_mem hmW)
            (hRC (hK1 hjm le_rfl).2)) (hdiv ▸ inv_mem_joinChart_of_notMem hjW)
        · intro i
          by_cases hi : (coord x (a i) (c i)) ∈ W
          · rw [gen_of_mem hi]
            obtain ⟨h₁, h₂⟩ := hK1 (hbelow i hi) hRN
            exact coord_mem_localAt (hc m) (hc i) (le_localAt htmN) (le_localAt h₁)
              (le_localAt h₂)
          · rw [gen_of_notMem hi]
            have hmi : ¬DiscLE v a c m i := fun h ↦ hi (habove i h)
            by_cases him : DiscLE v a c i m
            · by_cases hiS : W.valuation ((coord x (a m) (c m)) - ⟪(a i - a m) / c m⟫) < 1
              · have hine : i ≠ m := by
                  rintro rfl
                  exact hi hmW
                have hij : DiscLE v a c i j := discLE_of_residue hconv hred hc hWO him hine hiS
                  hjm hjne hjres fun k hk hkne hkW ↦ hjmax k ⟨hk, hkne, hkW⟩
                obtain ⟨h₁, h₂⟩ := hK1 hij hRN
                exact inv_coord_mem_localAt_of_inv (hc j) (hc i) htjN hjW (le_localAt h₁)
                  (le_localAt h₂) (hK1 hij hW).2
              · exact inv_coord_mem_localAt_of_unit hRN (hc m) (hc i) htmN
                  (him.div_le_one hc).1 (him.div_le_one hc).2 (hunit i him hiS)
            · obtain ⟨hfar, hfar'⟩ := lt_of_not_discLE him hmi
              exact inv_coord_mem_localAt_of_far hRN (hc m) (hc i) hWO htmN hmW hfar hfar'
      · push Not at hS
        set P := polyChart v (coord x (a m) (c m))
        have hRP : R ≤ P := baseRing_le_polyChart _
        have htmP : (coord x (a m) (c m)) ∈ P := self_mem_polyChart _
        refine ⟨P, .inl ⟨m, rfl⟩, polyChart_le hW hmW, polyChart_le hRC
          (mem_joinChart_of_mem hmW), localAt_joinChart_eq hRP
          (polyChart_le hRC (mem_joinChart_of_mem hmW)) fun i ↦ ?_⟩
        by_cases hi : (coord x (a i) (c i)) ∈ W
        · rw [gen_of_mem hi]
          obtain ⟨h₁, h₂⟩ := hK1 (hbelow i hi) hRP
          exact coord_mem_localAt (hc m) (hc i) (le_localAt htmP) (le_localAt h₁)
            (le_localAt h₂)
        · rw [gen_of_notMem hi]
          have hmi : ¬DiscLE v a c m i := fun h ↦ hi (habove i h)
          by_cases him : DiscLE v a c i m
          · have hine : i ≠ m := by
              rintro rfl
              exact hi hmW
            exact inv_coord_mem_localAt_of_unit hRP (hc m) (hc i) htmP
              (him.div_le_one hc).1 (him.div_le_one hc).2
              (hunit i him (not_lt.2 (hS i him hine)))
          · obtain ⟨hfar, hfar'⟩ := lt_of_not_discLE him hmi
            exact inv_coord_mem_localAt_of_far hRP (hc m) (hc i) hWO htmP hmW hfar hfar'
    · push Not at hI
      set P := polyChart v (coord x (a ρ) (c ρ))⁻¹
      have hRP : R ≤ P := baseRing_le_polyChart _
      have hρP : (coord x (a ρ) (c ρ))⁻¹ ∈ P := self_mem_polyChart _
      refine ⟨P, .inr (.inl ⟨ρ, rfl⟩), polyChart_le hW ((W.mem_or_inv_mem _).resolve_left
        (hI ρ)), polyChart_le hRC (inv_mem_joinChart_of_notMem (hI ρ)),
        localAt_joinChart_eq hRP (polyChart_le hRC (inv_mem_joinChart_of_notMem (hI ρ)))
        fun i ↦ ?_⟩
      rw [gen_of_notMem (hI i)]
      obtain ⟨h₁, h₂⟩ := hK1 (hρ i) hRP
      exact inv_coord_mem_localAt_of_inv (hc ρ) (hc i) hρP (hI ρ) (le_localAt h₁) (le_localAt h₂)
        (hK1 (hρ i) hW).2
  · -- the generic fibre: `W ⊇ K`
    have hK : ∀ k : K, ⟪k⟫ ∈ W := fun k ↦ by
      have : k ∈ W.comap (algebraMap K F) := by rw [hWK]; exact ValuationSubring.mem_top k
      exact this
    by_cases hρW : (coord x (a ρ) (c ρ)) ∈ W
    · have hall : ∀ i, (coord x (a i) (c i)) ∈ W := fun i ↦ by
        rw [coord_eq_mul_add (a := a ρ) (hc ρ) (hc i)]
        exact W.add_mem _ _ (W.mul_mem _ _ (hK _) hρW) (hK _)
      set P := polyChart v (coord x (a ρ) (c ρ))
      have hRP : R ≤ P := baseRing_le_polyChart _
      refine ⟨P, .inl ⟨ρ, rfl⟩, polyChart_le hW hρW, polyChart_le hRC
        (mem_joinChart_of_mem hρW), localAt_joinChart_eq hRP
        (polyChart_le hRC (mem_joinChart_of_mem hρW)) fun i ↦ ?_⟩
      rw [gen_of_mem (hall i)]
      exact coord_mem_localAt (hc ρ) (hc i) (le_localAt (self_mem_polyChart _))
        (algebraMap_mem_localAt_of_forall hRP hK _) (algebraMap_mem_localAt_of_forall hRP hK _)
    · have hnone : ∀ i, (coord x (a i) (c i)) ∉ W := fun i hi ↦ hρW (by
        rw [coord_eq_mul_add (a := a i) (hc i) (hc ρ)]
        exact W.add_mem _ _ (W.mul_mem _ _ (hK _) hi) (hK _))
      set P := polyChart v (coord x (a ρ) (c ρ))⁻¹
      have hRP : R ≤ P := baseRing_le_polyChart _
      refine ⟨P, .inr (.inl ⟨ρ, rfl⟩), polyChart_le hW ((W.mem_or_inv_mem _).resolve_left hρW),
        polyChart_le hRC (inv_mem_joinChart_of_notMem hρW), localAt_joinChart_eq hRP
        (polyChart_le hRC (inv_mem_joinChart_of_notMem hρW)) fun i ↦ ?_⟩
      rw [gen_of_notMem (hnone i)]
      exact inv_coord_mem_localAt_of_inv (hc ρ) (hc i) (self_mem_polyChart _) hρW
        (algebraMap_mem_localAt_of_forall hRP hK _) (algebraMap_mem_localAt_of_forall hRP hK _)
        (hK _)

variable (x) in
/-- **(M7b) The points of the join model** `ZariskiModel.lines v t` of a convex reduced family
of discs over a valuation ring of rank at most one: the specialization of every valuation subring
`W ⊇ O` of `F` is the local ring at the center of `W` of a standard chart `B ⊆ W`. -/
theorem center_lines_eq [Fintype ι] [Nonempty ι] (hc : ∀ i, c i ≠ 0)
    (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hrank : ∀ O' : ValuationSubring K, v.valuationSubring ≤ O' →
      O' = v.valuationSubring ∨ O' = ⊤)
    (hW : baseRing F v.valuationSubring ≤ W.toSubring) :
    ∃ B, IsStandardChart v a c x B ∧ B ≤ W.toSubring ∧
      (ZariskiModel.lines v fun i ↦ coord x (a i) (c i)).center lines_isProper W hW =
        localAt B W := by
  classical
  obtain ⟨B, hB, hBW, -, hloc⟩ := exists_standard_localAt_eq (x := x) hc hconv hred hrank hW
  refine ⟨B, hB, hBW, ?_⟩
  have hmem : joinChart v a c x W ∈ (ZariskiModel.lines v fun i ↦ coord x (a i) (c i)).charts := by
    refine mem_iJoin_charts.2 ⟨_, fun i ↦ ?_, rfl⟩
    split_ifs
    · exact mem_line_charts.2 (.inl rfl)
    · exact mem_line_charts.2 (.inr rfl)
  rw [center_eq lines_isProper lines_isSeparated hW hmem (joinChart_le hW), hloc]

end Tree

end GaussTree

/-! ### Convex families of Gauss valuations of `K(X)` -/

section RatFunc

open GaussTree

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

lemma gaussCoord_eq_coord {a c : K} (hc : c ≠ 0) :
    gaussCoord a c = coord (RatFunc.X : RatFunc K) a c := by
  have e (b : K) : algebraMap K[X] (RatFunc K) (Polynomial.C b) =
      algebraMap K (RatFunc K) b := by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  have h : algebraMap K (RatFunc K) c ≠ 0 := by simpa using hc
  rw [gaussCoord, gaussLin, coord, map_mul, map_sub, e, e, RatFunc.algebraMap_X, map_inv₀,
    div_eq_inv_mul]

/-- **(W5 (iii): the tree of `ℙ¹`s.)** For a convex reduced nonempty finite family of Gauss
valuations `w_{a i, |c i|}` of `K(X)` over a valuation ring of rank at most one, every point of
`gaussJoinModel v a c` (whose vertex set is the family, `gaussJoinModel_vertexSet`) is the point
of a standard chart: `O[(X - a i)/c i]`, `O[c ρ/(X - a ρ)]` (both `≅ O[X]`, `aeval_injective'`)
or a node chart `O[u, (c j/c m)/u]`, `u = (X - a j)/c m`, `D j ⊊ D m` (`≅ Node O (c j / c m)`,
`nodeLift_injective`; semistable for `c j / c m = ϖ ^ n`, `annulus_isSemistable`). -/
theorem gaussJoinModel_center_eq {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → K}
    (hc : ∀ i, c i ≠ 0) (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hrank : ∀ O' : ValuationSubring K, v.valuationSubring ≤ O' →
      O' = v.valuationSubring ∨ O' = ⊤)
    {W : ValuationSubring (RatFunc K)}
    (hW : baseRing (RatFunc K) v.valuationSubring ≤ W.toSubring) :
    ∃ B, IsStandardChart v a c (RatFunc.X : RatFunc K) B ∧ B ≤ W.toSubring ∧
      (gaussJoinModel v a c).center gaussJoinModel_isProper W hW = localAt B W := by
  have h : (gaussJoinModel v a c) = ZariskiModel.lines v fun i ↦
      coord (RatFunc.X : RatFunc K) (a i) (c i) := by
    simp only [gaussJoinModel, gaussCoord_eq_coord (hc _)]
  obtain ⟨B, hB, hBW, hcen⟩ := center_lines_eq (RatFunc.X : RatFunc K) hc hconv hred hrank hW
  refine ⟨B, hB, hBW, ?_⟩
  rw [← hcen]
  congr 1

end RatFunc

end SemistableReduction
