/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourGood
import TemperedFundamentalGroups.SemistableReduction.TypeFourInterfaces
import TemperedFundamentalGroups.SemistableReduction.Splitting
import TemperedFundamentalGroups.SemistableReduction.DiscLimit
import TemperedFundamentalGroups.SemistableReduction.TypeOneGerm

/-!
# Goodness near type-4 points: the assembly (leaf T4)

Blueprint §9.12, leaf T4 (`S8A.TypeFourGoodFor`). A nested sequence of open balls
`Bₙ = ball aₙ ‖cₙ‖` with empty intersection defines a limit valuation `ξ` of `C(x)`
(`DiscLimit.limitVal`), a type-4 point or a point of `Ĉ ∖ C` (`Splitting.IsTypeFour`). The proof
of `TypeFourGoodFor` splits into two statements about an extension `ξ'` of `ξ` to `F`:

* **`TypeFour.UnifFor`** (valued fields, local uniformization at `ξ`): for `F / C(x)` Galois there
  is `s ∈ F` such that `C(s)` is dense in `(F, ξ')` (`CoordDense`). For a point of `Ĉ ∖ C` one can
  take `s = x` (the completion is `Ĉ`, algebraically closed); at a type-4 point it is the Kummer
  tower over the decomposition field (Temkin's uniformization of type-4 fields, §9.10 fallback).
* **`TypeFour.CoreGFor`** (geometry): if `C(s)` is dense in `(F, ξ')`, the centre of `ξ'` on the
  chart of `Bₙ` is a smooth point for all large `n` (in the coordinate `s` the centre is a sheet by
  B4 and smooth by `SheetSmooth`; then `ChartTransfer` back to `x`).

Here (`S8A.typeFourGoodFor_of_galois`): for `F` Galois, `UnifFor` and `CoreGFor` give
`TypeFourGoodFor` (every point over the residue point of `Bₙ` is the centre of one of the finitely
many extensions of `ξ`, B4a).
-/

open Metric Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open DiscCount SmoothVertex AffineTwist LocalGlobal DenseCompletion

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

variable (C) in
/-- **`C(s)` is dense in `(K, ξ)`**: every `y ∈ K` is approximated by rational functions of `s`. -/
def CoordDense {K : Type*} [Field K] [Algebra C K] (ξ : Valuation K ℝ≥0) (s : K) : Prop :=
  ∀ y : K, ∀ ε : ℝ≥0, 0 < ε → ∃ P Q : C[X], aeval s Q ≠ 0 ∧ ξ (y - aeval s P / aeval s Q) < ε

variable (C) (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

/-- **Local uniformization at type-4 points** (valued fields): every extension `ξ'` to `F` of a
type-4 point (or a point of `Ĉ ∖ C`) admits a topological generator: some `s ∈ F` with `C(s)`
dense in `(F, ξ')`. -/
def UnifFor : Prop :=
  ∀ ξ' : Valuation F ℝ≥0, (∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊) →
    Splitting.IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F)) → ∃ s : F, CoordDense C ξ' s

/-- **Smoothness from a topological generator** (geometry): let `Bₙ = ball aₙ ‖cₙ‖` be nested
open balls with empty intersection and `ξ'` a valuation of `F` extending the norm of `C` and lying
in every `Bₙ`. If `C(s)` is dense in `(F, ξ')`, then for all large `n` the centre of `ξ'` on the
normalized chart of `Bₙ` (a maximal ideal over the residue point all of whose elements have
`ξ'`-value `< 1`) is a smooth point. -/
def CoreGFor : Prop :=
  ∀ (a c : ℕ → C) (hc : ∀ n, c n ≠ 0),
    (∀ n, ball (a (n + 1)) ‖c (n + 1)‖ ⊆ ball (a n) ‖c n‖) → (⋂ n, ball (a n) ‖c n‖) = ∅ →
    ∀ ξ' : Valuation F ℝ≥0, (∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊) →
    (∀ n, ξ' (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) (a n))) <
      ‖c n‖₊) →
    ∀ s : F, CoordDense C ξ' s → ∃ N, ∀ n ≥ N,
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff (a n) (c n) (hc n) F)), P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff (a n) (c n) (hc n) F))) =
          discIdeal (0 : C) 1 →
        (∀ y ∈ P', ξ' ((toAff (hc n)).symm (y : Aff (a n) (c n) (hc n) F)) < 1) →
        IsDiscSmooth P'

/-! ### The limit of nested balls with empty intersection -/

section Limit

variable {C}
variable {a c : ℕ → C} (hc : ∀ n, c n ≠ 0)
  (hnest : ∀ n, ball (a (n + 1)) ‖c (n + 1)‖ ⊆ ball (a n) ‖c n‖)
  (hempty : (⋂ n, ball (a n) ‖c n‖) = ∅)

omit [IsUltrametricDist C] [IsAlgClosed C] in
include hc hnest in
lemma norm_sub_succ_lt (n : ℕ) : ‖a (n + 1) - a n‖ < ‖c n‖ := by
  have := hnest n (mem_ball_self (norm_pos_iff.2 (hc (n + 1))))
  rwa [mem_ball, dist_eq_norm] at this

omit [IsAlgClosed C] in
include hc hnest in
lemma norm_succ_le (n : ℕ) : ‖c (n + 1)‖ ≤ ‖c n‖ := by
  by_contra! h
  have hz : a (n + 1) + c n ∈ ball (a (n + 1)) ‖c (n + 1)‖ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact h
  have h1 := norm_sub_succ_lt hc hnest n
  have := hnest n hz
  rw [mem_ball, dist_eq_norm, show a (n + 1) + c n - a n = c n + (a (n + 1) - a n) by ring,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le] at this
  exact lt_irrefl _ this

omit [IsUltrametricDist C] [IsAlgClosed C] in
include hnest in
lemma ball_subset_of_le {m n : ℕ} (hmn : m ≤ n) : ball (a n) ‖c n‖ ⊆ ball (a m) ‖c m‖ := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (hnest n).trans ih

omit [IsAlgClosed C] in
include hc hnest in
lemma norm_le_of_le {m n : ℕ} (hmn : m ≤ n) : ‖c n‖ ≤ ‖c m‖ := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (norm_succ_le hc hnest n).trans ih

omit [IsUltrametricDist C] [IsAlgClosed C] in
include hc hnest in
lemma norm_sub_lt_of_le {m n : ℕ} (hmn : m ≤ n) : ‖a n - a m‖ < ‖c m‖ := by
  have := ball_subset_of_le hnest hmn (mem_ball_self (norm_pos_iff.2 (hc n)))
  rwa [mem_ball, dist_eq_norm] at this

omit [IsUltrametricDist C] [IsAlgClosed C] in
include hc hnest hempty in
/-- The radii do not stabilize. -/
lemma exists_norm_lt (n : ℕ) : ∃ m, n ≤ m ∧ ‖c m‖ < ‖c n‖ := by
  by_contra! h
  have hmem : a n ∈ ⋂ m, ball (a m) ‖c m‖ := by
    refine Set.mem_iInter.2 fun m ↦ ?_
    rcases le_total m n with hmn | hnm
    · exact ball_subset_of_le hnest hmn (mem_ball_self (norm_pos_iff.2 (hc n)))
    · rw [mem_ball, dist_eq_norm, ← norm_neg, neg_sub]
      exact (norm_sub_lt_of_le hc hnest hnm).trans_le (h m hnm)
  rw [hempty] at hmem
  exact hmem

omit [IsAlgClosed C] in
include hc hnest hempty in
lemma exists_norm_lt_norm_sub (b : C) : ∃ m, ‖c m‖ < ‖b - a m‖ := by
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, b ∉ ball (a m₀) ‖c m₀‖ := by
    by_contra! h
    have : b ∈ ⋂ m, ball (a m) ‖c m‖ := Set.mem_iInter.2 h
    rw [hempty] at this
    exact this
  rw [mem_ball, dist_eq_norm, not_lt] at hm₀
  obtain ⟨m, hm, hlt⟩ := exists_norm_lt hc hnest hempty m₀
  refine ⟨m, ?_⟩
  have h1 := norm_sub_lt_of_le hc hnest hm
  rw [show b - a m = (b - a m₀) + -(a m - a m₀) by ring,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact
      (h1.trans_le hm₀).ne'), norm_neg, max_eq_left (h1.trans_le hm₀).le]
  exact hlt.trans_le hm₀

/-- The radii as units. -/
noncomputable def radU (n : ℕ) : ℝ≥0ˣ := Units.mk0 ‖c n‖₊ (nnnorm_ne_zero_iff.2 (hc n))

omit [IsAlgClosed C] in
include hnest in
lemma isNested : DiscLimit.IsNested (NormedField.valuation (K := C)) a (radU hc) where
  radius_succ_le n := by
    change ‖c (n + 1)‖₊ ≤ ‖c n‖₊
    exact_mod_cast norm_succ_le hc hnest n
  center_succ_le n := by
    rw [NormedField.valuation_apply]
    change ‖a (n + 1) - a n‖₊ ≤ ‖c n‖₊
    exact_mod_cast (norm_sub_succ_lt hc hnest n).le

omit [IsAlgClosed C] in
include hnest hempty in
lemma noCommonPoint : DiscLimit.NoCommonPoint (NormedField.valuation (K := C)) a (radU hc) :=
  fun b ↦ by
    obtain ⟨m, hm⟩ := exists_norm_lt_norm_sub hc hnest hempty b
    refine ⟨m, ?_⟩
    rw [NormedField.valuation_apply]
    change ‖c m‖₊ < ‖b - a m‖₊
    exact_mod_cast hm

/-- **The limit valuation** of the nested balls. -/
noncomputable def limXi : Valuation (RatFunc C) ℝ≥0 :=
  DiscLimit.limitVal (isNested hc hnest) (noCommonPoint hc hnest hempty)

lemma limXi_algebraMap (b : C) :
    limXi hc hnest hempty (algebraMap C (RatFunc C) b) = ‖b‖₊ :=
  DiscLimit.limitVal_algebraMap _ _ b

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma lin_eq (b : C) : DiscLimit.lin b = RatFunc.X - algebraMap C (RatFunc C) b := by
  rw [DiscLimit.lin, map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C]

/-- The limit lies in every open ball. -/
lemma limXi_lt (n : ℕ) :
    limXi hc hnest hempty (RatFunc.X - algebraMap C (RatFunc C) (a n)) < ‖c n‖₊ := by
  obtain ⟨m, hm, hlt⟩ := exists_norm_lt hc hnest hempty n
  have h1 : limXi hc hnest hempty (RatFunc.X - algebraMap C (RatFunc C) (a m)) ≤ ‖c m‖₊ := by
    rw [← lin_eq]
    exact DiscLimit.limitVal_lin_le _ _ m
  have h2 := norm_sub_lt_of_le hc hnest hm
  rw [show RatFunc.X - algebraMap C (RatFunc C) (a n) =
      (RatFunc.X - algebraMap C (RatFunc C) (a m)) + algebraMap C (RatFunc C) (a m - a n) by
    rw [map_sub]; ring]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt (h1.trans_lt ?_) ?_)
  · exact_mod_cast hlt
  · rw [limXi_algebraMap]
    exact_mod_cast h2

/-- The limit is a type-4 point (or a point of `Ĉ ∖ C`). -/
lemma isTypeFour_limXi : Splitting.IsTypeFour (limXi hc hnest hempty) where
  map_C b := by rw [limXi_algebraMap, NormedField.valuation_apply]
  no_min b := by
    obtain ⟨m, hm⟩ := exists_norm_lt_norm_sub hc hnest hempty b
    refine ⟨a m, ?_⟩
    have h1 : GaussLimit.radius (limXi hc hnest hempty) (a m) ≤ ‖c m‖₊ :=
      DiscLimit.limitVal_lin_le _ _ m
    have h2 : GaussLimit.radius (limXi hc hnest hempty) b = ‖b - a m‖₊ := by
      have := DiscLimit.limitVal_lin (isNested hc hnest) (noCommonPoint hc hnest hempty)
        (b := b) (m := m) (by
          rw [NormedField.valuation_apply]; change ‖c m‖₊ < ‖b - a m‖₊; exact_mod_cast hm)
      rw [NormedField.valuation_apply] at this
      exact this
    rw [h2]
    exact h1.trans_lt (by exact_mod_cast hm)

end Limit

/-! ### Assembly for Galois `F` -/

section Assembly

variable {C} {F}

omit [IsAlgClosed C] in
/-- The twisted valuation `φ ↦ ξ (aff a c φ)` of a valuation lying in `ball a ‖c‖` is a disc
valuation of the open unit disc. -/
lemma isDiscVal_twist {ξ : Valuation (RatFunc C) ℝ≥0}
    (hC : ∀ b : C, ξ (algebraMap C (RatFunc C) b) = ‖b‖₊) {a c : C} (hc : c ≠ 0)
    (hlt : ξ (RatFunc.X - algebraMap C (RatFunc C) a) < ‖c‖₊) :
    IsDiscVal (0 : C) 1 (ξ.comap (aff a c hc).toRingEquiv.toRingHom) where
  map_C b := by
    change ξ (aff a c hc (algebraMap C (RatFunc C) b)) = _
    rw [AlgEquiv.commutes, hC]
  X_lt_one := by
    change ξ (aff a c hc (gaussCoord (0 : C) 1)) < 1
    rw [gaussCoord_zero_one, aff_apply, affHom_X, gaussCoord_eq, map_mul, hC, nnnorm_inv]
    rw [inv_mul_lt_one₀ (nnnorm_pos.2 hc)]
    exact hlt

variable [CharZero C]

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
/-- **Every point over the residue point is a centre** (B4a): a maximal ideal of the chart of
`ball a ‖c‖` over the residue point is the centre of an extension of every disc valuation lying in
the ball. -/
theorem exists_ext_centre {ξ : Valuation (RatFunc C) ℝ≥0}
    (hC : ∀ b : C, ξ (algebraMap C (RatFunc C) b) = ‖b‖₊) {a c : C} (hc : c ≠ 0)
    (hlt : ξ (RatFunc.X - algebraMap C (RatFunc C) a) < ‖c‖₊)
    (P' : Ideal (DRint (0 : C) 1 (Aff a c hc F))) (hP' : P'.IsMaximal)
    (hcen : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff a c hc F))) =
      discIdeal (0 : C) 1) :
    ∃ ξ' : Valuation F ℝ≥0, ξ'.comap (algebraMap (RatFunc C) F) = ξ ∧
      ∀ y ∈ P', ξ' ((toAff hc).symm (y : Aff a c hc F)) < 1 := by
  classical
  haveI := hP'
  haveI : Algebra.IsSeparable (RatFunc C) (Aff a c hc F) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨ν, hν⟩ : ∃ ν : DiscVal (0 : C) 1,
      ν.val = ξ.comap (aff a c hc).toRingEquiv.toRingHom := ⟨⟨_, isDiscVal_twist hC hc hlt⟩, rfl⟩
  have hpos := discDegree_pos one_ne_zero ν P' hcen
  rw [discDegree, Finset.sum_pos_iff] at hpos
  obtain ⟨g, hg, -⟩ := hpos
  have hgc := (Finset.mem_filter.1 hg).2
  refine ⟨(extValuation g).comap (toAff hc).toRingHom, ?_, fun y hy ↦ ?_⟩
  · refine Valuation.ext fun φ ↦ ?_
    have h := congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v ((aff a c hc).symm φ))
      (Splitting.comap_extValuation ν g)
    simp only [Valuation.comap_apply] at h
    rw [Valuation.comap_apply, Valuation.comap_apply]
    change extValuation g (toAff hc (algebraMap (RatFunc C) F φ)) = ξ φ
    have : toAff hc (algebraMap (RatFunc C) F φ) =
        algebraMap (RatFunc C) (Aff a c hc F) ((aff a c hc).symm φ) := by
      rw [algebraMap_aff_apply, AlgEquiv.apply_symm_apply]
    rw [this, h, hν]
    change ξ (aff a c hc ((aff a c hc).symm φ)) = ξ φ
    rw [AlgEquiv.apply_symm_apply]
  · rw [← hgc, mem_center_iff] at hy
    exact hy

/-- **`TypeFourGoodFor` for Galois `F`** from local uniformization and the geometric comparison. -/
theorem typeFourGoodFor_of_galois [IsGalois (RatFunc C) F] (hU : UnifFor C F)
    (hG : CoreGFor C F) : S8A.TypeFourGoodFor C F := by
  intro a c hc hnest hempty
  set ξ := limXi hc hnest hempty
  have hξ4 := isTypeFour_limXi hc hnest hempty
  have hlt := limXi_lt hc hnest hempty
  have hC := limXi_algebraMap hc hnest hempty
  set E := {ξ' : Valuation F ℝ≥0 // ξ'.comap (algebraMap (RatFunc C) F) = ξ}
  haveI : Finite E := Splitting.finite_extensions hξ4
  have hN : ∀ ξ' : E, ∃ N, ∀ n ≥ N,
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff (a n) (c n) (hc n) F)), P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff (a n) (c n) (hc n) F))) =
          discIdeal (0 : C) 1 →
        (∀ y ∈ P', ξ'.1 ((toAff (hc n)).symm (y : Aff (a n) (c n) (hc n) F)) < 1) →
        IsDiscSmooth P' := by
    intro ξ'
    have hval : ∀ φ, ξ'.1 (algebraMap (RatFunc C) F φ) = ξ φ := fun φ ↦ by
      rw [← Valuation.comap_apply, ξ'.2]
    have hconst : ∀ b : C, ξ'.1 (algebraMap C F b) = ‖b‖₊ := fun b ↦ by
      rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, hval, hC]
    obtain ⟨s, hs⟩ := hU ξ'.1 hconst (by rw [ξ'.2]; exact hξ4)
    exact hG a c hc hnest hempty ξ'.1 hconst (fun n ↦ by rw [hval]; exact hlt n) s hs
  choose N hN using hN
  obtain ⟨N₀, hN₀⟩ := Finite.exists_le N
  refine ⟨N₀, fun P' hP' hcen ↦ ?_⟩
  obtain ⟨ξ', hξ', hy⟩ := exists_ext_centre hC (hc N₀) (hlt N₀) P' hP' hcen
  exact hN ⟨ξ', hξ'⟩ N₀ (hN₀ _) P' hP' hcen hy

universe v

/-- **`TypeFourGoodFor`** for every `F` from local uniformization and the geometric comparison
for its Galois closure, and A6 (descent of smooth points along the Galois closure). -/
theorem typeFourGoodFor_of {F : Type v} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
    (hU : ∀ (L : Type v) [Field L] [Algebra (RatFunc C) L] [Algebra C L]
      [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
      [IsGalois (RatFunc C) L], UnifFor C L)
    (hG : ∀ (L : Type v) [Field L] [Algebra (RatFunc C) L] [Algebra C L]
      [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
      [IsGalois (RatFunc C) L], CoreGFor C L)
    (hA6 : ∀ (L : Type v) [Field L] [Algebra (RatFunc C) L] [Algebra F L]
      [IsScalarTower (RatFunc C) F L] [Algebra C L] [IsScalarTower C (RatFunc C) L]
      [FiniteDimensional (RatFunc C) L] [IsGalois F L], ClassicalSmooth.A6For C F L) :
    S8A.TypeFourGoodFor C F := by
  haveI : IsAlgClosure (RatFunc C) (AlgebraicClosure F) :=
    IsAlgClosure.ofAlgebraic (RatFunc C) F (AlgebraicClosure F)
  let L := IntermediateField.normalClosure (RatFunc C) F (AlgebraicClosure F)
  letI : Algebra C L := ((algebraMap (RatFunc C) L).comp (algebraMap C (RatFunc C))).toAlgebra
  haveI : IsScalarTower C (RatFunc C) L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsGalois F L := IsGalois.tower_top_of_isGalois (RatFunc C) F L
  have hL := typeFourGoodFor_of_galois (hU L) (hG L)
  intro a c hc hnest hempty
  obtain ⟨n, hn⟩ := hL a c hc hnest hempty
  refine ⟨n, fun P' hP' hcen ↦ hA6 L (a n) (c n) (hc n) P' hP' hcen fun P'' hP'' hP''P ↦
    hn P'' hP'' ?_⟩
  rw [← hcen, ← hP''P, Ideal.comap_comap]
  rfl

end Assembly

end TypeFour

end SemistableReduction
