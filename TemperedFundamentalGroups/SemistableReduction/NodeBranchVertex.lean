/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.AnnulusModel
import TemperedFundamentalGroups.SemistableReduction.MonomialExists
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization
import TemperedFundamentalGroups.SemistableReduction.UnfoldedVertex
import TemperedFundamentalGroups.SemistableReduction.DiscLimit
import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
# Branch valuations through the node of a normalized node chart (StrongComponentA (a))

Let `y` be a Gauss coordinate of `w` over `v` (`IsGaussCoord v w y`), `c ∈ K` with `v(c) < 1`,
`S = O[y, c/y]` the node chart and `T` its integral closure in a field `F₀ ⊇ F`. For a valuation
subring `W` of `F₀` containing `T` with `y, c/y ∈ 𝔪_W` (its center lies over the node), there is a
valuation subring `V` of `F₀` containing the local ring `localAt T W` and lying over `O_w`
(`exists_valuationSubring_branch`). So the germs at the node are contained in a branch over each of
the two Gauss valuations of the node.

* `exists_decomp_nodeChart`: every `s ∈ O[y, c/y]` is `o + y A + (c/y) B` with `o ∈ O`,
  `A ∈ O[y]`, `B ∈ O[y, c/y]`;
* `valuation_lt_one_of_gauss`: the center of `w` on `S` lies in the node;
* going down for the integral extension `S ⊆ T` of the integrally closed `S`
  (`isIntegrallyClosed_nodeChart`) gives a prime of `T` over the center of `w` inside the center of
  `W`; a valuation subring dominating it restricts to `O_w` (a valuation ring is maximal for
  domination, and `O_w` is the local ring of `O[y]` at its center, `localAt_polyChart`).
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

/-- **Decomposition in the node chart**: `s = o + y A + (c/y) B`. -/
lemma exists_decomp_nodeChart {y : F} {c : K} {s : F} (hs : s ∈ nodeChart v y c) :
    ∃ o ∈ baseRing F v.valuationSubring, ∃ A ∈ polyChart v y, ∃ B ∈ nodeChart v y c,
      s = o + y * A + (algebraMap K F c / y) * B := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 0, zero_mem _, 0, zero_mem _, by ring⟩
    · rcases hx with rfl | rfl
      · exact ⟨0, zero_mem _, 1, one_mem _, 0, zero_mem _, by ring⟩
      · exact ⟨0, zero_mem _, 0, zero_mem _, 1, one_mem _, by ring⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, 0, zero_mem _, by ring⟩
  | one => exact ⟨1, one_mem _, 0, zero_mem _, 0, zero_mem _, by ring⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨o, ho, A, hA, B, hB, rfl⟩ := hx
    obtain ⟨o', ho', A', hA', B', hB', rfl⟩ := hx'
    exact ⟨o + o', add_mem ho ho', A + A', add_mem hA hA', B + B', add_mem hB hB', by ring⟩
  | neg x _ hx =>
    obtain ⟨o, ho, A, hA, B, hB, rfl⟩ := hx
    exact ⟨-o, neg_mem ho, -A, neg_mem hA, -B, neg_mem hB, by ring⟩
  | mul x x' _ hx'm hx hx' =>
    obtain ⟨o, ho, A, hA, B, hB, rfl⟩ := hx
    obtain ⟨o', ho', A', hA', B', hB', e⟩ := hx'
    have hPN : polyChart v y ≤ nodeChart v y c := polyChart_le baseRing_le_nodeChart
      self_mem_nodeChart
    have hoP : ∀ {o}, o ∈ baseRing F v.valuationSubring → o ∈ polyChart v y :=
      fun h ↦ baseRing_le_polyChart y h
    refine ⟨o * o', mul_mem ho ho', A * o' + o * A' + y * (A * A'),
      add_mem (add_mem (mul_mem hA (hoP ho')) (mul_mem (hoP ho) hA'))
        (mul_mem (self_mem_polyChart y) (mul_mem hA hA')),
      B * x' + o * B' + y * (A * B'),
      add_mem (add_mem (mul_mem hB hx'm) (mul_mem (baseRing_le_nodeChart ho) hB'))
        (mul_mem self_mem_nodeChart (mul_mem (hPN hA) hB')), ?_⟩
    rw [e]
    ring

variable {w : Valuation F Γ₀} {y : F}

/-- The node chart lies in the Gauss valuation ring of `y` (for `v(c) ≤ 1`). -/
lemma IsGaussCoord.nodeChart_le_valuationSubring (h : IsGaussCoord v w y) {c : K}
    (hc : v c ≤ 1) : nodeChart v y c ≤ w.valuationSubring.toSubring := by
  refine nodeChart_le (h.polyChart_le_valuationSubring.trans' (baseRing_le_polyChart y))
    (h.polyChart_le_valuationSubring (self_mem_polyChart y)) ?_
  change w (algebraMap K F c / y) ≤ 1
  rw [map_div₀, h.valuation_algebraMap, h.valuation_self, div_one]
  exact hc

/-- **The center of `w` on `O[y, c/y]` lies in the node**: for a ring map `ι : F → F₀` and a
valuation subring `W₀` of `F₀` with `O[y, c/y] ⊆ ι⁻¹ W₀`, `y, c/y ∈ 𝔪_{W₀}` and `𝔪_O ⊆ 𝔪_{W₀}`,
every `s` of the chart with `w(s) < 1` has `W₀(ι s) < 1`. -/
lemma IsGaussCoord.valuation_lt_one_of_lt_one (h : IsGaussCoord v w y) {c : K} (hc : v c < 1)
    {F₀ : Type*} [Field F₀] (ι : F →+* F₀) (W₀ : ValuationSubring F₀)
    (hSW : ∀ s ∈ nodeChart v y c, W₀.valuation (ι s) ≤ 1)
    (hO : ∀ o : K, v o < 1 → W₀.valuation (ι (algebraMap K F o)) < 1)
    (hy : W₀.valuation (ι y) < 1) (hcy : W₀.valuation (ι (algebraMap K F c / y)) < 1)
    {s : F} (hs : s ∈ nodeChart v y c) (hws : w s < 1) : W₀.valuation (ι s) < 1 := by
  obtain ⟨o, ho, A, hA, B, hB, rfl⟩ := exists_decomp_nodeChart hs
  obtain ⟨o₀, ho₀, rfl⟩ := ho
  obtain ⟨Q, hQ, rfl⟩ := mem_polyChart_iff.1 hA
  have hBw : w B ≤ 1 := h.nodeChart_le_valuationSubring hc.le hB
  -- `v(o₀) < 1`
  have hcyw : w (algebraMap K F c / y * B) < 1 := by
    rw [map_mul, map_div₀, h.valuation_algebraMap, h.valuation_self, div_one]
    exact mul_lt_one_of_lt_of_le hc hBw
  have h1 : w (algebraMap K F o₀ + y * aeval y Q) < 1 := by
    have e : algebraMap K F o₀ + y * aeval y Q =
        (algebraMap K F o₀ + y * aeval y Q + algebraMap K F c / y * B) -
          algebraMap K F c / y * B := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt hws hcyw)
  have h2 : algebraMap K F o₀ + y * aeval y Q = aeval y (C o₀ + X * Q) := by
    simp [aeval_def, eval₂_add, eval₂_mul]
  have hvo : v o₀ < 1 := by
    rw [h2, h.eq_sup] at h1
    refine lt_of_le_of_lt ?_ h1
    have := Gauss.term_le_sup (v := v) (r := 1) (C o₀ + X * Q) 0
    simpa [Gauss.term] using this
  -- the estimate at `W₀`
  have hA1 : W₀.valuation (ι (aeval y Q)) ≤ 1 :=
    hSW _ (polyChart_le baseRing_le_nodeChart self_mem_nodeChart hA)
  have hB1 : W₀.valuation (ι B) ≤ 1 := hSW _ hB
  rw [map_add ι, map_add ι, map_mul ι, map_mul ι]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt
    ((Valuation.map_add _ _ _).trans_lt (max_lt (hO o₀ hvo) ?_)) ?_)
  · rw [map_mul]; exact mul_lt_one_of_lt_of_le hy hA1
  · rw [map_mul]; exact mul_lt_one_of_lt_of_le hcy hB1

/-- Elements of a valuation subring with valuation `1` have inverse in it. -/
private lemma valuation_inv_of_not_mem {F₀ : Type*} [Field F₀] (V : ValuationSubring F₀) {x : F₀}
    (hx : x ∉ V) : V.valuation x⁻¹ < 1 := by
  have hx0 : x ≠ 0 := fun h0 ↦ hx (h0 ▸ V.zero_mem)
  have hinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hx
  refine lt_of_le_of_ne ((V.valuation_le_one_iff _).2 hinv) fun h1 ↦ hx ?_
  have : V.valuation x = 1 := by
    rw [map_inv₀, inv_eq_one] at h1; exact h1
  exact (V.valuation_le_one_iff _).1 this.le

/-- **A branch through the node over the Gauss valuation of `y`**: for a valuation subring `W` of
`F₀ ⊇ F` containing the integral closure `T` of `O[y, c/y]`, over `O`, with `y, c/y ∈ 𝔪_W`, there is
a valuation subring `V ⊇ localAt T W` of `F₀` lying over `O_w`. -/
theorem IsGaussCoord.exists_valuationSubring_branch (h : IsGaussCoord v w y) {c : K} (hc0 : c ≠ 0)
    (hc : v c < 1) {F₀ : Type u} [Field F₀] [Algebra F F₀] {W : ValuationSubring F₀}
    (hTW : normChart F₀ (nodeChart v y c) ≤ W.toSubring)
    (hW : (W.comap (algebraMap F F₀)).comap (algebraMap K F) = v.valuationSubring)
    (hy : W.valuation (algebraMap F F₀ y) < 1)
    (hcy : W.valuation (algebraMap F F₀ (algebraMap K F c / y)) < 1) :
    ∃ V : ValuationSubring F₀, localAt (normChart F₀ (nodeChart v y c)) W ≤ V.toSubring ∧
      V.comap (algebraMap F F₀) = w.valuationSubring := by
  classical
  set S := nodeChart v y c with hSdef
  set T := normChart F₀ S with hTdef
  have hST : ∀ s ∈ S, algebraMap F F₀ s ∈ T := fun s hs ↦ map_le_normChart S ⟨s, hs, rfl⟩
  let φ : S →+* T := ((algebraMap F F₀).comp S.subtype).codRestrict T (fun s ↦ hST s s.2)
  letI : Algebra S T := φ.toAlgebra
  have hφ : ∀ s : S, ((algebraMap S T s : T) : F₀) = algebraMap F F₀ s := fun _ ↦ rfl
  haveI : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).2 fun a b hab ↦
    Subtype.ext ((algebraMap F F₀).injective (by
      rw [← hφ, ← hφ, hab]))
  haveI : Algebra.IsIntegral S T := by
    constructor
    intro t
    set R' := S.map (algebraMap F F₀)
    have ht : IsIntegral R' (t : F₀) := t.2
    obtain ⟨p, hpm, hp⟩ := ht
    let e : S ≃+* R' := S.equivMapOfInjective (algebraMap F F₀) (algebraMap F F₀).injective
    refine ⟨p.map e.symm.toRingHom, hpm.map _, Subtype.val_injective ?_⟩
    have h1 : T.subtype.comp (algebraMap S T) = R'.subtype.comp e.toRingHom := by
      ext s; rfl
    change T.subtype (eval₂ (algebraMap S T) t _) = T.subtype 0
    have h2 : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by ext r; simp
    rw [hom_eval₂, h1, eval₂_map, RingHom.comp_assoc, h2, RingHom.comp_id, map_zero]
    exact hp
  letI : Algebra v.valuationSubring F :=
    ((algebraMap K F).comp v.valuationSubring.subtype).toAlgebra
  haveI : IsScalarTower v.valuationSubring K F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsIntegrallyClosed S := isIntegrallyClosed_nodeChart h hc0 hc.le
  -- the primes
  have hSw := h.nodeChart_le_valuationSubring hc.le
  set QW := centerIdeal T W hTW
  set q := QW.comap (algebraMap S T)
  haveI : QW.LiesOver q := ⟨rfl⟩
  set pm := centerIdeal S w.valuationSubring hSw
  have hwlt : ∀ x : F, w.valuationSubring.valuation x < 1 ↔ w x < 1 := fun x ↦
    ((Valuation.isEquiv_valuation_valuationSubring w).lt_one_iff_lt_one).symm
  have hO : ∀ o : K, v o < 1 → W.valuation (algebraMap F F₀ (algebraMap K F o)) < 1 := by
    intro o ho
    have hoO : o ∈ v.valuationSubring := (Valuation.mem_valuationSubring_iff _ _).2 ho.le
    have hmem : algebraMap F F₀ (algebraMap K F o) ∈ W := by
      have : o ∈ (W.comap (algebraMap F F₀)).comap (algebraMap K F) := hW ▸ hoO
      exact this
    refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 hmem) fun h1 ↦ ?_
    have ho0 : o ≠ 0 := by rintro rfl; simp at h1
    have hinv : (algebraMap F F₀ (algebraMap K F o))⁻¹ ∈ W := by
      rw [← W.valuation_le_one_iff, map_inv₀, h1, inv_one]
    have : o⁻¹ ∈ v.valuationSubring := by
      rw [← hW]; change algebraMap F F₀ (algebraMap K F o⁻¹) ∈ W
      rwa [map_inv₀, map_inv₀]
    have h2 := (Valuation.mem_valuationSubring_iff _ _).1 this
    rw [map_inv₀] at h2
    exact absurd ho (not_lt.2
      ((inv_le_one₀ (pos_iff_ne_zero.2 ((_root_.map_ne_zero v).2 ho0))).1 h2))
  have hle : pm ≤ q := by
    intro s hs
    rw [mem_centerIdeal_iff, hwlt] at hs
    rw [Ideal.mem_comap, mem_centerIdeal_iff, hφ]
    exact h.valuation_lt_one_of_lt_one hc (algebraMap F F₀) W
      (fun s hs ↦ (W.valuation_le_one_iff _).2 (hTW (hST s hs))) hO hy hcy s.2 hs
  obtain ⟨P, hPQ, hPprime, hPlies⟩ := Ideal.exists_ideal_le_liesOver_of_le QW (p := pm) (q := q) hle
  obtain ⟨V, hTV, hVlt, hVeq⟩ := exists_valuationSubring_of_isPrime T P
  have hV1 : ∀ s ∈ S, V.valuation (algebraMap F F₀ s) ≤ 1 := fun s hs ↦
    (V.valuation_le_one_iff _).2 (hTV (hST s hs))
  have key : ∀ s (hs : s ∈ S), V.valuation (algebraMap F F₀ s) < 1 ↔
      w.valuationSubring.valuation s < 1 := by
    intro s hs
    have hpm : (⟨s, hs⟩ : S) ∈ pm ↔ algebraMap S T ⟨s, hs⟩ ∈ P := by
      rw [hPlies.over]; rfl
    rw [← mem_centerIdeal_iff hSw ⟨s, hs⟩, hpm]
    constructor
    · intro hlt
      by_contra hP
      have := hVeq _ hP
      rw [hφ] at this
      rw [this] at hlt
      exact lt_irrefl _ hlt
    · intro hP
      have := hVlt _ hP
      rwa [hφ] at this
  have hloc := h.localAt_polyChart
  have hPS : polyChart v y ≤ S := polyChart_le baseRing_le_nodeChart self_mem_nodeChart
  refine ⟨V, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hsT, hsW, hxs⟩ := mem_localAt.1 hx
    have hsP : (⟨s, hsT⟩ : T) ∉ P := fun hP ↦ by
      have := (mem_centerIdeal_iff hTW ⟨s, hsT⟩).1 (hPQ hP)
      rw [hsW] at this
      exact lt_irrefl _ this
    have hVs : V.valuation s = 1 := hVeq _ hsP
    have hVxs : V.valuation (x * s) ≤ 1 := (V.valuation_le_one_iff _).2 (hTV hxs)
    rw [map_mul, hVs, mul_one] at hVxs
    exact (V.valuation_le_one_iff _).1 hVxs
  · have hunit : ∀ s ∈ polyChart v y, w.valuationSubring.valuation s = 1 →
        V.valuation (algebraMap F F₀ s) = 1 := by
      intro s hs hs1
      refine le_antisymm (hV1 s (hPS hs)) (not_lt.1 fun hlt ↦ ?_)
      rw [key s (hPS hs), hs1] at hlt
      exact lt_irrefl _ hlt
    ext x
    rw [ValuationSubring.mem_comap]
    constructor
    · intro hx
      by_contra hxw
      have hinv := valuation_inv_of_not_mem _ hxw
      have hxi : x⁻¹ ∈ localAt (polyChart v y) w.valuationSubring := by
        rw [hloc]; exact (w.valuationSubring.valuation_le_one_iff _).1 hinv.le
      obtain ⟨s, hs, hsw, hxs⟩ := mem_localAt.1 hxi
      have h1 : w.valuationSubring.valuation (x⁻¹ * s) < 1 := by
        rw [map_mul, hsw, mul_one]; exact hinv
      have h2 := (key _ (hPS hxs)).2 h1
      rw [map_mul, map_mul, hunit s hs hsw, mul_one, map_inv₀, map_inv₀] at h2
      have h3 := (V.valuation_le_one_iff _).2 hx
      have hx0' : x ≠ 0 := fun e ↦ hxw (e ▸ w.valuationSubring.zero_mem)
      have hx0 : V.valuation (algebraMap F F₀ x) ≠ 0 :=
        (_root_.map_ne_zero _).2 ((_root_.map_ne_zero _).2 hx0')
      exact absurd h3 (not_le.2 ((inv_lt_one₀ (pos_iff_ne_zero.2 hx0)).1 h2))
    · intro hx
      have hxl : x ∈ localAt (polyChart v y) w.valuationSubring := by rw [hloc]; exact hx
      obtain ⟨s, hs, hsw, hxs⟩ := mem_localAt.1 hxl
      have h1 := hV1 _ (hPS hxs)
      rw [map_mul, map_mul, hunit s hs hsw, mul_one] at h1
      exact (V.valuation_le_one_iff _).1 h1

section Edge

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

local notation "⟪" k "⟫" => algebraMap K (RatFunc K) k

/-- **The thickness of a node is in `𝔪_O`**: if `y, c/y ∈ 𝔪_W` for a valuation subring `W` of
`F₀` over `O`, then `v(c) < 1`. -/
lemma valuation_lt_one_of_node {y : RatFunc K} (hy0 : y ≠ 0) {c' : K} (hc'0 : c' ≠ 0)
    {F₀ : Type u} [Field F₀] [Algebra (RatFunc K) F₀] {W : ValuationSubring F₀}
    (hW : (W.comap (algebraMap (RatFunc K) F₀)).comap (algebraMap K (RatFunc K)) =
      v.valuationSubring)
    (hy : W.valuation (algebraMap (RatFunc K) F₀ y) < 1)
    (hcy : W.valuation (algebraMap (RatFunc K) F₀ (⟪c'⟫ / y)) < 1) : v c' < 1 := by
  have hWc : W.valuation (algebraMap (RatFunc K) F₀ ⟪c'⟫) < 1 := by
    have e : ⟪c'⟫ = y * (⟪c'⟫ / y) := by field_simp
    rw [e, map_mul, map_mul]
    exact mul_lt_one_of_lt_of_le hy (le_of_lt hcy)
  by_contra hge
  push Not at hge
  have hinv : c'⁻¹ ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hge
  have hmem : algebraMap (RatFunc K) F₀ ⟪c'⁻¹⟫ ∈ W := by
    have : c'⁻¹ ∈ (W.comap (algebraMap (RatFunc K) F₀)).comap (algebraMap K (RatFunc K)) :=
      hW ▸ hinv
    exact this
  have h1 := (W.valuation_le_one_iff _).2 hmem
  rw [map_inv₀, map_inv₀, map_inv₀] at h1
  have h0 : W.valuation (algebraMap (RatFunc K) F₀ ⟪c'⟫) ≠ 0 := by
    simp [hc'0]
  exact absurd h1 (not_le.2 ((one_lt_inv₀ (pos_iff_ne_zero.2 h0)).2 hWc))

open GaussTree in
/-- **Both branches through an edge node.** For the edge chart `O[t, c'/t]`, `t = (X - a j)/c m`,
`c' = c j / c m`, its integral closure `T` in `F₀` and a valuation
subring `W ⊇ T` of `F₀` over `O` with `t, c'/t ∈ 𝔪_W`, the local ring `localAt T W` lies in a
valuation subring over the Gauss valuation `w_{a j, |c m|}` (the disc `m` when `D j ⊆ D m`), and
in one over that of the disc `j`. -/
theorem exists_branches_edge {ι : Type*} {a c : ι → K} {j m : ι} (hcj : c j ≠ 0) (hcm : c m ≠ 0)
    {F₀ : Type u} [Field F₀] [Algebra (RatFunc K) F₀]
    {W : ValuationSubring F₀}
    (hTW : normChart F₀ (nodeChart v (coord (RatFunc.X : RatFunc K) (a j) (c m)) (c j / c m)) ≤
      W.toSubring)
    (hW : (W.comap (algebraMap (RatFunc K) F₀)).comap (algebraMap K (RatFunc K)) =
      v.valuationSubring)
    (hy : W.valuation (algebraMap (RatFunc K) F₀ (coord (RatFunc.X : RatFunc K) (a j) (c m))) < 1)
    (hcy : W.valuation (algebraMap (RatFunc K) F₀
      (⟪c j / c m⟫ / coord (RatFunc.X : RatFunc K) (a j) (c m))) < 1) :
    (∃ V : ValuationSubring F₀,
      localAt (normChart F₀
        (nodeChart v (coord (RatFunc.X : RatFunc K) (a j) (c m)) (c j / c m))) W ≤
        V.toSubring ∧ V.comap (algebraMap (RatFunc K) F₀) =
          (gaussRat v (a j) (Units.mk0 (v (c m)) ((v.ne_zero_iff).2 hcm))).valuationSubring) ∧
    (∃ V : ValuationSubring F₀,
      localAt (normChart F₀
        (nodeChart v (coord (RatFunc.X : RatFunc K) (a j) (c m)) (c j / c m))) W ≤
        V.toSubring ∧ V.comap (algebraMap (RatFunc K) F₀) =
          (gaussRat v (a j) (Units.mk0 (v (c j)) ((v.ne_zero_iff).2 hcj))).valuationSubring) := by
  set y := coord (RatFunc.X : RatFunc K) (a j) (c m) with hydef
  set c' := c j / c m with hc'def
  have hc'0 : c' ≠ 0 := div_ne_zero hcj hcm
  have hgm := isGaussCoord_coord (v := v) (a := a j) hcm
  have hy0 : y ≠ 0 := hgm.ne_zero
  have hc' : v c' < 1 := valuation_lt_one_of_node hy0 hc'0 hW hy hcy
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hV, hVc⟩ := hgm.exists_valuationSubring_branch hc'0 hc' hTW hW hy hcy
    exact ⟨V, hV, hVc⟩
  · -- the other branch: `c'/y = ((X - a j)/c j)⁻¹`
    have hgj := (isGaussCoord_coord (v := v) (a := a j) hcj).inv
    have e : (coord (RatFunc.X : RatFunc K) (a j) (c j))⁻¹ = ⟪c'⟫ / y := by
      simp only [hydef, hc'def, coord, map_div₀]
      have : (RatFunc.X - ⟪a j⟫ : RatFunc K) ≠ 0 := by
        have := hgm.ne_zero
        simp only [coord] at this
        exact (div_ne_zero_iff.1 this).1
      have : (⟪c m⟫ : RatFunc K) ≠ 0 := by simpa using hcm
      field_simp
    rw [e] at hgj
    have hS : nodeChart v (⟪c'⟫ / y) c' = nodeChart v y c' := nodeChart_div hy0 hc'0
    have hcy' : W.valuation (algebraMap (RatFunc K) F₀ (⟪c'⟫ / (⟪c'⟫ / y))) < 1 := by
      have : ⟪c'⟫ / (⟪c'⟫ / y) = y := by
        have : (⟪c'⟫ : RatFunc K) ≠ 0 := by simpa using hc'0
        field_simp
      rw [this]; exact hy
    rw [← hS] at hTW ⊢
    obtain ⟨V, hV, hVc⟩ := hgj.exists_valuationSubring_branch hc'0 hc' hTW hW hcy hcy'
    exact ⟨V, hV, hVc⟩

end Edge

end SemistableReduction
