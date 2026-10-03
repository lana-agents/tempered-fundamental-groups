/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TreeCount
import TemperedFundamentalGroups.SemistableReduction.NodePoints

/-!
# The node points of a Gauss tree

Blueprint §9.9, S7.5–S7.6. For tree data `T` with coordinate `x₀`, every edge `e` has a node chart
`O_C[x_e, c_e/x_e]` (`x_e = (x₀ - a_{χ e}) / c_{π e}`, `c_e = c_{χ e} / c_{π e}`) and its integral
closure `R'_e` in `F`.

* `TreeData.NP e`: the node points of `e`, the points of `R'_e` with an outer branch;
* `TreeData.Sp ⟨e, P'⟩`: the branches through `P'` (outer and inner, as branches of the vertex
  set `S`);
* `TreeData.Oc ⟨e, P'⟩`: the condition space at `P'`, the vectors which are a fraction of `R'_e`
  with denominator outside `P'` at all branches through `P'`.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability GaussFibre GaussTube DeltaCount PlaceNorm

namespace TreeCount

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {F : Type*} [Field F] [Algebra C F] [IsCurveFunctionField C F]
  (T : TreeData C) {x₀ : F} (hx₀ : Transcendental C x₀)
  {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

attribute [local instance] DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Edge

/-- The `C(X)`-algebra structure of the edge `e` (`X ↦ x_e`). -/
noncomputable abbrev TreeData.edgeAlg (e : T.E) : Algebra (RatFunc C) F :=
  (coordAlgHom (T.hec hx₀ e)).toRingHom.toAlgebra

omit [IsAlgClosed C] [CharZero C] [IsCurveFunctionField C F] in
lemma TreeData.edgeTower (e : T.E) :
    letI := T.edgeAlg hx₀ e
    IsScalarTower C (RatFunc C) F :=
  letI := T.edgeAlg hx₀ e
  IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom (T.hec hx₀ e)).commutes c).symm

lemma TreeData.edgeFin (e : T.E) :
    letI := T.edgeAlg hx₀ e
    FiniteDimensional (RatFunc C) F := by
  letI := T.edgeAlg hx₀ e
  haveI := T.edgeTower hx₀ e
  have hxF : xF C F = T.ec x₀ e := xF_coord (T.hec hx₀ e)
  exact finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ T.hec hx₀ e)

omit [CharZero C] [IsCurveFunctionField C F] in
lemma TreeData.algebraMap_inv (e : T.E) :
    letI := T.edgeAlg hx₀ e
    (algebraMap (RatFunc C) (Inv (T.ce e) (T.ce_ne_zero e) F) :
      RatFunc C →+* Inv (T.ce e) (T.ce_ne_zero e) F) =
        (coordAlgHom (T.hinner hx₀ e)).toRingHom := by
  letI := T.edgeAlg hx₀ e
  haveI := T.edgeTower hx₀ e
  rw [← coordAlgHom_comp_inv (T.hec hx₀ e) (T.ce_ne_zero e) (T.hinner hx₀ e)]
  rfl

include hp hp1 in
lemma TreeData.finite_outerBranch (e : T.E) :
    letI := T.edgeAlg hx₀ e
    haveI := T.edgeTower hx₀ e
    haveI := T.edgeFin hx₀ e
    Finite (OuterBranch C F) := by
  letI := T.edgeAlg hx₀ e
  haveI := T.edgeTower hx₀ e
  haveI := T.edgeFin hx₀ e
  haveI : Finite (Ext C F) := finite_ext hp hp1
  infer_instance

include hp hp1 in
lemma TreeData.finite_innerBranch (e : T.E) :
    letI := T.edgeAlg hx₀ e
    haveI := T.edgeTower hx₀ e
    haveI := T.edgeFin hx₀ e
    Finite (OuterBranch C (Inv (T.ce e) (T.ce_ne_zero e) F)) := by
  letI := T.edgeAlg hx₀ e
  haveI := T.edgeTower hx₀ e
  haveI := T.edgeFin hx₀ e
  haveI : Finite (Ext C (Inv (T.ce e) (T.ce_ne_zero e) F)) := finite_ext hp hp1
  infer_instance

/-- The node points of the edge `e`: the points of `R'_e` through which an outer branch passes. -/
noncomputable def TreeData.NP (e : T.E) :
    Finset (letI := T.edgeAlg hx₀ e; Ideal (Rint (T.ce e) F)) :=
  letI := T.edgeAlg hx₀ e
  haveI := T.edgeTower hx₀ e
  haveI := T.edgeFin hx₀ e
  haveI := T.finite_outerBranch hx₀ hp hp1 e
  (Set.finite_range fun b : OuterBranch C F ↦ placeIdeal (T.norm_ce_lt_one e) b.1 b.2.2).toFinset

/-- The node points of the tree. -/
abbrev TreeData.Pt : Type _ := Σ e : T.E, T.NP hx₀ hp hp1 e

/-- An outer branch of the edge `e` as a branch of the vertex set. -/
noncomputable def TreeData.outBr (e : T.E) :
    (letI := T.edgeAlg hx₀ e
     haveI := T.edgeTower hx₀ e
     haveI := T.edgeFin hx₀ e
     OuterBranch C F) → Branch 𝓀 (Kappa (T.S hx₀ hp hp1)) :=
  letI := T.edgeAlg hx₀ e
  haveI := T.edgeTower hx₀ e
  haveI := T.edgeFin hx₀ e
  fun b ↦ ⟨⟨TypeTwo.ofComap (T.hec hx₀ e) b.1.1 b.1.2, (T.mem_S hx₀ hp hp1 _).2
    ⟨T.par e, (T.isOver_ec_iff hx₀ e _).2 (TypeTwo.isOver_ofComap _ _ _)⟩⟩, b.2.1⟩

/-- An inner branch of the edge `e` as a branch of the vertex set. -/
noncomputable def TreeData.inBr (e : T.E) :
    (letI := T.edgeAlg hx₀ e
     haveI := T.edgeTower hx₀ e
     haveI := T.edgeFin hx₀ e
     OuterBranch C (Inv (T.ce e) (T.ce_ne_zero e) F)) → Branch 𝓀 (Kappa (T.S hx₀ hp hp1)) :=
  letI := T.edgeAlg hx₀ e
  haveI := T.edgeTower hx₀ e
  haveI := T.edgeFin hx₀ e
  fun b ↦ ⟨⟨TypeTwo.ofComap (T.hinner hx₀ e) (b.1.1 : Valuation F ℝ≥0)
    (by rw [← T.algebraMap_inv hx₀ e]; exact b.1.2), (T.mem_S hx₀ hp hp1 _).2
    ⟨T.chi e, (T.isOver_inner_iff hx₀ e _).2 (TypeTwo.isOver_ofComap _ _ _)⟩⟩, b.2.1⟩

/-- The branches through a node point. -/
noncomputable def TreeData.Sp (P : T.Pt hx₀ hp hp1) : Finset (Branch 𝓀 (Kappa (T.S hx₀ hp hp1))) :=
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  haveI := T.finite_outerBranch hx₀ hp hp1 P.1
  haveI := T.finite_innerBranch hx₀ hp hp1 P.1
  (((Set.toFinite (outerBranches (T.norm_ce_lt_one P.1) P.2.1)).image
    (T.outBr hx₀ hp hp1 P.1)).union ((Set.toFinite (innerBranches (T.norm_ce_lt_one P.1)
      (T.ce_ne_zero P.1) P.2.1)).image (T.inBr hx₀ hp hp1 P.1))).toFinset

end Edge

section Unit

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ] (Q : CurvePlace k κ)

lemma _root_.SemistableReduction.CurvePlace.inv_mem_of_res_ne_zero {y : κ} (hy : y ∈ Q.V)
    (h0 : Q.res y ≠ 0) : y⁻¹ ∈ Q.V := by
  have hy1 : Q.valuation y = 1 := by
    refine le_antisymm (Q.valuation_le_one_iff.2 hy) (not_lt.1 fun h ↦ h0 ?_)
    exact Q.res_eq_zero_of_lt_one h
  refine Q.valuation_le_one_iff.1 ?_
  rw [map_inv₀, hy1, inv_one]

lemma _root_.SemistableReduction.CurvePlace.res_inv {y : κ} (hy : y ∈ Q.V) (h0 : Q.res y ≠ 0) :
    Q.res y⁻¹ = (Q.res y)⁻¹ := by
  have hy0 : y ≠ 0 := fun h ↦ h0 (by rw [h, Q.res_zero])
  have h := Q.res_mul hy (Q.inv_mem_of_res_ne_zero hy h0)
  rw [mul_inv_cancel₀ hy0, Q.res_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

end Unit

section Spec

/-- Every node point has an outer branch. -/
lemma TreeData.exists_outer (P : T.Pt hx₀ hp hp1) :
    letI := T.edgeAlg hx₀ P.1
    haveI := T.edgeTower hx₀ P.1
    haveI := T.edgeFin hx₀ P.1
    ∃ b₀ : OuterBranch C F, b₀ ∈ outerBranches (T.norm_ce_lt_one P.1) P.2.1 := by
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  obtain ⟨e, P', hP'⟩ := P
  simp only [TreeData.NP, Set.Finite.mem_toFinset, Set.mem_range] at hP'
  obtain ⟨b₀, hb₀⟩ := hP'
  exact ⟨b₀, hb₀⟩

/-- Node points are maximal ideals. -/
lemma TreeData.isMaximal (P : T.Pt hx₀ hp hp1) : P.2.1.IsMaximal := by
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  obtain ⟨b₀, hb₀⟩ := T.exists_outer hx₀ hp hp1 P
  rw [← show placeIdeal (T.norm_ce_lt_one P.1) b₀.1 b₀.2.2 = P.2.1 from hb₀]
  exact placeIdeal_isMaximal _ _ _

omit [IsAlgClosed C] [CharZero C] [IsCurveFunctionField C F] in
lemma TreeData.coe_constR (e : T.E) (κ : HenselComplete.integers C) :
    letI := T.edgeAlg hx₀ e
    ((constR (T.ce e) κ : Rint (T.ce e) F) : F) = algebraMap C F κ :=
  (coordAlgHom (T.hec hx₀ e)).commutes _

/-- **The branches through a node point**: elements of `R'_e` are regular at all of them, with the
residue map of any outer branch through the point. -/
theorem TreeData.branch_spec (P : T.Pt hx₀ hp hp1) {β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))}
    (hβ : β ∈ T.Sp hx₀ hp hp1 P) :
    letI := T.edgeAlg hx₀ P.1
    haveI := T.edgeTower hx₀ P.1
    haveI := T.edgeFin hx₀ P.1
    ∀ b₀ : OuterBranch C F, b₀ ∈ outerBranches (T.norm_ce_lt_one P.1) P.2.1 →
      ∀ r : Rint (T.ce P.1) F, β.1.1.val (r : F) ≤ 1 ∧ β.1.1.red (r : F) ∈ β.2.V ∧
        β.2.res (β.1.1.red (r : F)) = placeHom (T.norm_ce_lt_one P.1) b₀.1 b₀.2.2 r := by
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  intro b₀ hb₀ r
  have hc := T.norm_ce_lt_one P.1
  have hc0 := T.ce_ne_zero P.1
  simp only [TreeData.Sp, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image] at hβ
  rcases hβ with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
  · exact ⟨valuation_le_one_R hc b.1 r, red_mem_V hc b.1 r b.2.2,
      congrArg (· r) (placeHom_eq_of_mem_outer hc hb hb₀)⟩
  · exact ⟨valuation_le_one_R hc b.1 (rintEquiv hc0 r), red_mem_V hc b.1 (rintEquiv hc0 r) b.2.2,
      congrArg (· r) (placeHom_rintEquiv_eq_of_mem_inner hc hc0 hb₀ hb)⟩

/-- The reduction of an element outside a node point is a unit at the branches through it. -/
theorem TreeData.red_ne_zero_of_notMem (P : T.Pt hx₀ hp hp1) {β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))}
    (hβ : β ∈ T.Sp hx₀ hp hp1 P) {s : letI := T.edgeAlg hx₀ P.1; Rint (T.ce P.1) F}
    (hs : s ∉ P.2.1) : β.1.1.red (s : F) ∈ β.2.V ∧ β.2.res (β.1.1.red (s : F)) ≠ 0 := by
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  obtain ⟨b₀, hb₀⟩ := T.exists_outer hx₀ hp hp1 P
  obtain ⟨-, h1, h2⟩ := T.branch_spec hx₀ hp hp1 P hβ b₀ hb₀ s
  refine ⟨h1, fun h ↦ hs ?_⟩
  rw [← show placeIdeal (T.norm_ce_lt_one P.1) b₀.1 b₀.2.2 = P.2.1 from hb₀]
  exact (RingHom.mem_ker).2 (h2 ▸ h)

end Spec

section Condition

lemma TreeData.red_ne_zero' (P : T.Pt hx₀ hp hp1) {β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))}
    (hβ : β ∈ T.Sp hx₀ hp hp1 P) {s : letI := T.edgeAlg hx₀ P.1; Rint (T.ce P.1) F}
    (hs : s ∉ P.2.1) : β.1.1.red (s : F) ≠ 0 := by
  intro h
  have := (T.red_ne_zero_of_notMem hx₀ hp hp1 P hβ hs).2
  rw [h, β.2.res_zero] at this
  exact this rfl

/-- **The condition space** at a node point `P'`: the vectors which, at all branches through `P'`,
are a fraction `y / s` of `R'_e` with `s ∉ P'`. -/
noncomputable def TreeData.Oc (P : T.Pt hx₀ hp hp1) :
    Submodule 𝓀 (Π W : T.S hx₀ hp hp1, Kappa (T.S hx₀ hp hp1) W) where
  carrier := {a | letI := T.edgeAlg hx₀ P.1
    ∃ y s : Rint (T.ce P.1) F, s ∉ P.2.1 ∧
      ∀ β ∈ T.Sp hx₀ hp hp1 P, a β.1 * β.1.1.red (s : F) = β.1.1.red (y : F)}
  zero_mem' := by
    letI := T.edgeAlg hx₀ P.1
    haveI := (T.isMaximal hx₀ hp hp1 P).ne_top
    refine ⟨0, 1, (Ideal.ne_top_iff_one _).1 this, fun β _ ↦ ?_⟩
    simp [TypeTwo.red_zero]
  add_mem' := by
    letI := T.edgeAlg hx₀ P.1
    haveI := T.edgeTower hx₀ P.1
    haveI := T.edgeFin hx₀ P.1
    rintro a a' ⟨y, s, hs, h⟩ ⟨y', s', hs', h'⟩
    haveI := (T.isMaximal hx₀ hp hp1 P).isPrime
    obtain ⟨b₀, hb₀⟩ := T.exists_outer hx₀ hp hp1 P
    refine ⟨y * s' + y' * s, s * s', fun hm ↦ (Ideal.IsPrime.mem_or_mem this hm).elim hs hs',
      fun β hβ ↦ ?_⟩
    have hv (r : Rint (T.ce P.1) F) := (T.branch_spec hx₀ hp hp1 P hβ b₀ hb₀ r).1
    have hm (r r' : Rint (T.ce P.1) F) :
        β.1.1.red ((r * r' : Rint (T.ce P.1) F) : F) = β.1.1.red r * β.1.1.red r' :=
      TypeTwo.red_mul (hv r) (hv r')
    have ha (r r' : Rint (T.ce P.1) F) :
        β.1.1.red ((r + r' : Rint (T.ce P.1) F) : F) = β.1.1.red r + β.1.1.red r' :=
      TypeTwo.red_add (hv r) (hv r')
    rw [Pi.add_apply, hm, ha, hm, hm, ← h β hβ, ← h' β hβ]
    ring
  smul_mem' := by
    letI := T.edgeAlg hx₀ P.1
    haveI := T.edgeTower hx₀ P.1
    haveI := T.edgeFin hx₀ P.1
    rintro c a ⟨y, s, hs, h⟩
    obtain ⟨κ, rfl⟩ := residue_surjective c
    obtain ⟨b₀, hb₀⟩ := T.exists_outer hx₀ hp hp1 P
    refine ⟨constR (T.ce P.1) κ * y, s, hs, fun β hβ ↦ ?_⟩
    have hv (r : Rint (T.ce P.1) F) := (T.branch_spec hx₀ hp hp1 P hβ b₀ hb₀ r).1
    have hκ : ‖(κ : C)‖ ≤ 1 := (HenselComplete.mem_integers_iff _).1 κ.2
    simp only [Subalgebra.coe_mul, Pi.smul_apply, Algebra.smul_def]
    rw [TypeTwo.red_mul (hv _) (hv y), T.coe_constR hx₀ P.1 κ, TypeTwo.red_algebraMap _ hκ,
      ← h β hβ, mul_assoc]

/-- The condition space consists of vectors regular at the branches with equal residues. -/
theorem TreeData.Oc_le_eqRes (P : T.Pt hx₀ hp hp1) :
    T.Oc hx₀ hp hp1 P ≤ eqRes 𝓀 (Kappa (T.S hx₀ hp hp1)) (T.Sp hx₀ hp hp1 P) := by
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  rintro a ⟨y, s, hs, h⟩
  obtain ⟨b₀, hb₀⟩ := T.exists_outer hx₀ hp hp1 P
  have hfrac (β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))) (hβ : β ∈ T.Sp hx₀ hp hp1 P) :
      a β.1 ∈ β.2.V ∧ β.2.res (a β.1) = placeHom (T.norm_ce_lt_one P.1) b₀.1 b₀.2.2 y /
        placeHom (T.norm_ce_lt_one P.1) b₀.1 b₀.2.2 s := by
    have hy := T.branch_spec hx₀ hp hp1 P hβ b₀ hb₀ y
    have hs' := T.branch_spec hx₀ hp hp1 P hβ b₀ hb₀ s
    have hy1 := hy.2.1
    have hy2 := hy.2.2
    have hs1 := hs'.2.1
    have hs2 := hs'.2.2
    have hs0 := (T.red_ne_zero_of_notMem hx₀ hp hp1 P hβ hs).2
    have ha : a β.1 = β.1.1.red (y : F) * (β.1.1.red (s : F))⁻¹ := by
      rw [← h β hβ, mul_inv_cancel_right₀ (T.red_ne_zero' hx₀ hp hp1 P hβ hs)]
    have hinv : (β.1.1.red (s : F))⁻¹ ∈ β.2.V := β.2.inv_mem_of_res_ne_zero hs1 hs0
    refine ⟨by rw [ha]; exact mul_mem hy1 hinv, ?_⟩
    have e1 : β.2.res (a β.1) = β.2.res (β.1.1.red (y : F)) * (β.2.res (β.1.1.red (s : F)))⁻¹ := by
      rw [ha, β.2.res_mul hy1 hinv, β.2.res_inv hs1 hs0]
    exact e1.trans ((congrArg₂ (· * ·) hy2 (congrArg (·⁻¹) hs2)).trans (div_eq_mul_inv _ _).symm)
  exact ⟨fun β hβ ↦ (hfrac β hβ).1, fun β hβ β' hβ' ↦ (hfrac β hβ).2.trans (hfrac β' hβ').2.symm⟩

end Condition

end TreeCount

end SemistableReduction
