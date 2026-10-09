/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TreeNode

/-!
# The δ-count for a Gauss tree

Blueprint §9.9, S7.5–S7.6. Let `T` be tree data for a function field `F / C` with coordinate `x₀`,
`S` the vertex set (all extensions of the Gauss points of the tree) and `D_m = m Σⱼ (x₀ - bⱼ)₀`.

* `degree_zeroDiv_sub`: `deg (t - β)₀ = [κ : k(t)]`;
* `sum_finrank_eq`: `Σ_{W over i} [κ(W) : k(x̄ᵢ)] = [F : C(x₀)]` (W4 in the vertex coordinate).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

open FundamentalInequality GaussStability GaussFibre GaussTube

section Degree

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ]

lemma adjoin_affine_eq {t : κ} {α β : k} (hα : α ≠ 0) :
    k⟮algebraMap k κ α * t + algebraMap k κ β⟯ = k⟮t⟯ := by
  refine le_antisymm (IntermediateField.adjoin_simple_le_iff.2 ?_)
    (IntermediateField.adjoin_simple_le_iff.2 ?_)
  · exact add_mem (mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self k t)) (IntermediateField.algebraMap_mem _ _)
  · have ht : t = algebraMap k κ α⁻¹ * (algebraMap k κ α * t + algebraMap k κ β) -
        algebraMap k κ (β / α) := by
      have : algebraMap k κ α ≠ 0 := by simpa using hα
      rw [map_inv₀, map_div₀]
      field_simp
      ring
    have hmem : algebraMap k κ α⁻¹ * (algebraMap k κ α * t + algebraMap k κ β) -
        algebraMap k κ (β / α) ∈ k⟮algebraMap k κ α * t + algebraMap k κ β⟯ :=
      sub_mem (mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.mem_adjoin_simple_self k _)) (IntermediateField.algebraMap_mem _ _)
    rwa [← ht] at hmem

variable [IsAlgClosed k] [IsCurveFunctionField k κ]

/-- The degree of the divisor of zeros of `t - β` is `[κ : k(t)]`. -/
lemma degree_zeroDiv_sub {t : κ} (ht : Transcendental k t) (β : k) :
    (zeroDiv k (t - algebraMap k κ β)).degree = Module.finrank k⟮t⟯ κ := by
  have hne : (t - algebraMap k κ β)⁻¹ ∉ (algebraMap k κ).range := by
    rintro ⟨c, hc⟩
    apply ht
    have : t = (algebraMap k κ c)⁻¹ + algebraMap k κ β := by rw [hc, inv_inv]; ring
    rw [this, ← map_inv₀]
    exact (isAlgebraic_algebraMap _).add (isAlgebraic_algebraMap _)
  rw [zeroDiv, degree_poleDivisor hne, adjoin_inv_eq,
    show t - algebraMap k κ β = algebraMap k κ 1 * t + algebraMap k κ (-β) by
      rw [map_one, one_mul, _root_.map_neg, sub_eq_add_neg],
    adjoin_affine_eq one_ne_zero]

end Degree

section Coordinate

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra C F] [IsCurveFunctionField C F]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

omit [IsAlgClosed C] [IsCurveFunctionField C F] in
/-- The reduction of a coordinate is transcendental at a valuation over its Gauss point. -/
lemma TypeTwo.transcendental_red_of_isOver {t : F} (ht : Transcendental C t) {W : TypeTwo C F}
    (hW : IsOver ht W) : Transcendental 𝓀 (W.red t) := by
  letI : Algebra (RatFunc C) F := (coordAlgHom ht).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom ht).commutes c).symm
  have hxF : xF C F = t := xF_coord ht
  have := transcendental_red_x (⟨W.val, hW⟩ : Ext C F)
  rw [hxF] at this
  exact this

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **W4 in a coordinate**: `Σ_{W over t} [κ(W) : k(t̄)] = [F : C(t)]`. -/
lemma sum_finrank_eq {t : F} (ht : Transcendental C t) :
    ∑ W ∈ (finite_isOver hp hp1 ht).toFinset,
      Module.finrank 𝓀⟮W.red t⟯ (ResidueField W.val.valuationSubring) =
        Module.finrank C⟮t⟯ F := by
  classical
  letI : Algebra (RatFunc C) F := (coordAlgHom ht).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom ht).commutes c).symm
  have hxF : xF C F = t := xF_coord ht
  haveI := finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ ht)
  haveI : Finite (Ext C F) := finite_ext (F := F) hp hp1
  letI : Fintype (Ext C F) := Fintype.ofFinite _
  have hsum := sum_inertiaDeg_eq (F := F) hp hp1
  have h1 : Module.finrank C⟮t⟯ F = Module.finrank (RatFunc C) F := by
    rw [← finrank_adjoin_xF, hxF]
  rw [h1, ← hsum]
  symm
  refine Finset.sum_bij (fun v _ ↦ TypeTwo.ofComap ht v.1 v.2) (fun v _ ↦ ?_)
    (fun v _ v' _ h ↦ Subtype.ext (congrArg TypeTwo.val h)) (fun W hW ↦ ?_) fun v _ ↦ ?_
  · rw [Set.Finite.mem_toFinset]
    exact TypeTwo.isOver_ofComap ht v.1 v.2
  · rw [Set.Finite.mem_toFinset] at hW
    exact ⟨⟨W.val, hW⟩, Finset.mem_univ _, rfl⟩
  · rw [← finrank_adjoin_red_x v, hxF]
    rfl

end Coordinate

namespace TreeCount

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {F : Type*} [Field F] [Algebra C F] [IsCurveFunctionField C F]
  (T : TreeData C) {x₀ : F} (hx₀ : Transcendental C x₀)
  {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Vertex

/-- The vertex under an element of the vertex set. -/
noncomputable def TreeData.vtx (W : TreeData.S T hx₀ hp hp1) : T.ι :=
  Classical.choose ((T.mem_S hx₀ hp hp1 W.1).1 W.2)

lemma TreeData.isOver_vtx (W : TreeData.S T hx₀ hp hp1) :
    IsOver (T.hvc hx₀ (T.vtx hx₀ hp hp1 W)) W.1 :=
  Classical.choose_spec ((T.mem_S hx₀ hp hp1 W.1).1 W.2)

lemma TreeData.vtx_eq {W : TreeData.S T hx₀ hp hp1} {i : T.ι} (h : IsOver (T.hvc hx₀ i) W.1) :
    T.vtx hx₀ hp hp1 W = i :=
  T.eq_of_isOver hx₀ (T.isOver_vtx hx₀ hp hp1 W) h

/-- The divisor `D̄_{m,W} = m (x̄ᵢ - β̄ᵢ)₀` on the residue curve of `W` over the vertex `i`. -/
noncomputable def TreeData.Db (m : ℕ) (W : TreeData.S T hx₀ hp hp1) :
    CurveDivisor 𝓀 (Kappa (TreeData.S T hx₀ hp hp1) W) :=
  m • zeroDiv 𝓀 (W.1.red (T.vc x₀ (T.vtx hx₀ hp hp1 W)) -
    algebraMap 𝓀 _ (T.βbar (T.vtx hx₀ hp hp1 W)))

lemma TreeData.Db_nonneg (m : ℕ) (W : TreeData.S T hx₀ hp hp1) (Q) :
    0 ≤ T.Db hx₀ hp hp1 m W Q := by
  rw [TreeData.Db, Finsupp.smul_apply, zeroDiv, poleDivisor_apply]
  positivity

lemma TreeData.degree_Db (m : ℕ) (W : TreeData.S T hx₀ hp hp1) :
    (T.Db hx₀ hp hp1 m W).degree = m * Module.finrank 𝓀⟮W.1.red (T.vc x₀ (T.vtx hx₀ hp hp1 W))⟯
      (ResidueField W.1.val.valuationSubring) := by
  rw [TreeData.Db, map_nsmul, degree_zeroDiv_sub
    (TypeTwo.transcendental_red_of_isOver (T.hvc hx₀ _) (T.isOver_vtx hx₀ hp hp1 W)),
    nsmul_eq_mul]

lemma TreeData.le_degree_Db (m : ℕ) (W : TreeData.S T hx₀ hp hp1) :
    (m : ℤ) ≤ (T.Db hx₀ hp hp1 m W).degree := by
  rw [T.degree_Db]
  haveI := IsCurveFunctionField.finiteDimensional_adjoin
    (TypeTwo.transcendental_red_of_isOver (T.hvc hx₀ _) (T.isOver_vtx hx₀ hp hp1 W))
  have h1 : 1 ≤ Module.finrank 𝓀⟮W.1.red (T.vc x₀ (T.vtx hx₀ hp hp1 W))⟯
      (ResidueField W.1.val.valuationSubring) := Module.finrank_pos
  have h1' : (1 : ℤ) ≤ (Module.finrank 𝓀⟮W.1.red (T.vc x₀ (T.vtx hx₀ hp hp1 W))⟯
      (ResidueField W.1.val.valuationSubring) : ℤ) := by exact_mod_cast h1
  nlinarith [Int.natCast_nonneg m]

/-- **The degree identity**: `Σ_W deg D̄_{m,W} = deg D_m`. -/
theorem TreeData.sum_degree_Db (m : ℕ) :
    ∑ W, (T.Db hx₀ hp hp1 m W).degree = (T.D x₀ m).degree := by
  classical
  set S := TreeData.S T hx₀ hp hp1
  set N := Module.finrank C⟮x₀⟯ F
  -- the right side
  have hD : (T.D x₀ m).degree = m * ∑ _j : T.ι, (N : ℤ) := by
    rw [TreeData.D, map_nsmul, map_sum, nsmul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ degree_zeroDiv_sub hx₀ (T.b j)
  rw [hD]
  -- the left side, vertex by vertex
  set G : TypeTwo C F → ℕ := fun W ↦ if h : W ∈ S then
    Module.finrank 𝓀⟮W.red (T.vc x₀ (T.vtx hx₀ hp hp1 ⟨W, h⟩))⟯
      (ResidueField W.val.valuationSubring) else 0
  have hL : ∑ W : S, (T.Db hx₀ hp hp1 m W).degree = m * ∑ W ∈ S, (G W : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun W _ ↦ ?_
    rw [T.degree_Db]
    simp [G, W.2]
  rw [hL]
  congr 1
  have hS : S = Finset.univ.biUnion fun i ↦ (finite_isOver hp hp1 (T.hvc hx₀ i)).toFinset := rfl
  have hdisj : (↑(Finset.univ : Finset T.ι) : Set T.ι).PairwiseDisjoint
      fun i ↦ (finite_isOver hp hp1 (T.hvc hx₀ i)).toFinset := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro W hi hj
    rw [Set.Finite.mem_toFinset] at hi hj
    exact hij (T.eq_of_isOver hx₀ hi hj)
  rw [hS, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsum := sum_finrank_eq hp hp1 (T.hvc hx₀ i)
  have hN : Module.finrank C⟮T.vc x₀ i⟯ F = N := by
    have : T.vc x₀ i = algebraMap C F (T.c i)⁻¹ * x₀ + algebraMap C F (-(T.a i / T.c i)) := by
      have : algebraMap C F (T.c i) ≠ 0 := by simpa using T.hc i
      simp only [TreeData.vc, vcoord, map_inv₀, _root_.map_neg, map_div₀]
      field_simp
      ring
    rw [this, adjoin_affine_eq (inv_ne_zero (T.hc i))]
  rw [← hN, ← hsum]
  push_cast
  refine Finset.sum_congr rfl fun W hW ↦ ?_
  rw [Set.Finite.mem_toFinset] at hW
  have hWS : W ∈ S := (T.mem_S hx₀ hp hp1 W).2 ⟨i, hW⟩
  simp only [G, dif_pos hWS]
  rw [T.vtx_eq hx₀ hp hp1 (W := ⟨W, hWS⟩) hW]

end Vertex

section Reduction

omit [IsAlgClosed C] [CharZero C] [IsCurveFunctionField C F] in
/-- The reduction of an edge coordinate at the parent is regular where the vertex coordinate is. -/
lemma red_ec_mem {e : T.E} {W : TypeTwo C F} (hW : IsOver (T.hvc hx₀ (T.par e)) W)
    {Q : CurvePlace 𝓀 (ResidueField W.val.valuationSubring)}
    (hQ : W.red (T.vc x₀ (T.par e)) ∈ Q.V) : W.red (T.ec x₀ e) ∈ Q.V := by
  have hδ : ‖-((T.a (T.chi e) - T.a (T.par e)) / T.c (T.par e))‖ ≤ 1 := by
    rw [norm_neg, norm_div, div_le_one (norm_pos_iff.2 (T.hc _))]
    exact T.hedge_a e
  rw [T.ec_eq (x₀ := x₀) e, map_one, one_mul, TypeTwo.red_add (by rw [hW.valuation_self])
    (by rw [TypeTwo.valuation_algebraMap]; exact_mod_cast hδ), TypeTwo.red_algebraMap _ hδ]
  exact add_mem hQ (Q.algebraMap_mem _)

include hp hp1 in
/-- **(H2) The reductions of `L(D_m)°` lie in `Π_W L(D̄_{m,W})`.** -/
theorem TreeData.redVec_mem (m : ℕ) {f : F} (hf : f ∈ rrSpace (T.D x₀ m))
    (hn : mnorm (TreeData.S T hx₀ hp hp1) f ≤ 1) :
    redVec (TreeData.S T hx₀ hp hp1) f ∈ DeltaCount.piRR 𝓀 (Kappa (TreeData.S T hx₀ hp hp1))
      (T.Db hx₀ hp hp1 m) := by
  have hn' (i : T.ι) (W : TypeTwo C F) (h : IsOver (T.hvc hx₀ i) W) : W.val f ≤ 1 :=
    (le_mnorm ((T.mem_S hx₀ hp hp1 W).2 ⟨i, h⟩) f).trans hn
  intro W _ Q
  change Q.valuation (W.1.red f) ≤ exp (T.Db hx₀ hp hp1 m W Q)
  set i := T.vtx hx₀ hp hp1 W
  have hW := T.isOver_vtx hx₀ hp hp1 W
  have hexp1 : (1 : ℤᵐ⁰) ≤ exp (T.Db hx₀ hp hp1 m W Q) := by
    rw [← exp_zero, exp_le_exp]; exact T.Db_nonneg hx₀ hp hp1 m W Q
  by_cases hQ : W.1.red (T.vc x₀ i) ∈ Q.V
  · by_cases hE : ∃ e, T.par e = i ∧ Q.valuation (W.1.red (T.ec x₀ e)) < 1
    · obtain ⟨e, he, hlt⟩ := hE
      have hW' : IsOver (T.hvc hx₀ (T.par e)) W.1 := he ▸ hW
      exact (Q.valuation_le_one_iff.2 (red_mem_V_par T hx₀ hp hp1 hf hn' hW' Q hlt)).trans hexp1
    · push Not at hE
      refine valuation_red_le_affine T hx₀ hp hp1 hf (hn' i) hW Q hQ fun e he ↦ ?_
      have hW' : IsOver (T.hvc hx₀ (T.par e)) W.1 := he ▸ hW
      have hmem := red_ec_mem T hx₀ hW' (Q := Q) (he ▸ hQ)
      have h1 : Q.valuation (W.1.red (T.ec x₀ e)) = 1 :=
        le_antisymm (Q.valuation_le_one_iff.2 hmem) (hE e he)
      refine Q.valuation_le_one_iff.1 ?_
      rw [map_inv₀, h1, inv_one]
  · by_cases hroot : ∀ e, T.chi e ≠ i
    · exact (valuation_red_le_root T hx₀ hp hp1 hf hroot (hn' i) hW Q hQ).trans hexp1
    · push Not at hroot
      obtain ⟨e, he⟩ := hroot
      have hW' : IsOver (T.hvc hx₀ (T.chi e)) W.1 := he ▸ hW
      have hvc1 : W.1.val (T.vc x₀ (T.chi e)) = 1 := hW'.valuation_self
      have hlt : Q.valuation (W.1.red (algebraMap C F (T.ce e) / T.ec x₀ e)) < 1 := by
        rw [T.inner_eq (x₀ := x₀) e, TypeTwo.red_inv hvc1, map_inv₀]
        have hQ' : W.1.red (T.vc x₀ (T.chi e)) ∉ Q.V := he ▸ hQ
        have h2 := Q.valuation_le_one_iff.2 ((Q.V.mem_or_inv_mem _).resolve_left hQ')
        rw [map_inv₀] at h2
        refine lt_of_le_of_ne h2 fun h1 ↦ hQ' ?_
        rw [← Q.valuation_le_one_iff, ← inv_inv (Q.valuation _), h1, inv_one]
      exact (Q.valuation_le_one_iff.2 (red_mem_V_chi T hx₀ hp hp1 hf hn' hW' Q hlt)).trans hexp1

end Reduction

end TreeCount

end SemistableReduction
