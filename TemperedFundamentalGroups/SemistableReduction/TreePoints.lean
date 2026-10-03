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

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Edge

/-- The `C(X)`-algebra structure of the edge `e` (`X ↦ x_e`). -/
noncomputable abbrev TreeData.edgeAlg (e : T.E) : Algebra (RatFunc C) F :=
  (coordAlgHom (T.hec hx₀ e)).toRingHom.toAlgebra

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [IsCurveFunctionField C F] in
lemma TreeData.edgeTower (e : T.E) :
    letI := T.edgeAlg hx₀ e
    IsScalarTower C (RatFunc C) F :=
  letI := T.edgeAlg hx₀ e
  IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom (T.hec hx₀ e)).commutes c).symm

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] in
lemma TreeData.edgeFin (e : T.E) :
    letI := T.edgeAlg hx₀ e
    FiniteDimensional (RatFunc C) F := by
  letI := T.edgeAlg hx₀ e
  haveI := T.edgeTower hx₀ e
  have hxF : xF C F = T.ec x₀ e := xF_coord (T.hec hx₀ e)
  exact finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ T.hec hx₀ e)

omit [IsUltrametricDist C] [CharZero C] [IsCurveFunctionField C F] in
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

omit [CharZero C] in
lemma TreeData.inner_comap (e : T.E) :
    letI := T.edgeAlg hx₀ e
    haveI := T.edgeTower hx₀ e
    haveI := T.edgeFin hx₀ e
    ∀ b : OuterBranch C (Inv (T.ce e) (T.ce_ne_zero e) F),
      (b.1.1 : Valuation F ℝ≥0).comap (coordAlgHom (T.hinner hx₀ e)).toRingHom = gauss1 C := by
  intro b
  rw [← T.algebraMap_inv hx₀ e]
  exact b.1.2

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
    (T.inner_comap hx₀ e b), (T.mem_S hx₀ hp hp1 _).2
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

section Structure

lemma _root_.SemistableReduction.CurvePlace.valuation_algebraMap_eq_one' {k κ : Type*} [Field k]
    [Field κ] [Algebra k κ] [IsAlgClosed k] [IsCurveFunctionField k κ] (Q : CurvePlace k κ)
    {c : k} (hc : c ≠ 0) : Q.valuation (algebraMap k κ c) = 1 := by
  have h1 := Q.valuation_algebraMap_le_one c
  have h2 := Q.valuation_algebraMap_le_one c⁻¹
  rw [map_inv₀, map_inv₀] at h2
  have h0 : Q.valuation (algebraMap k κ c) ≠ 0 := by simpa using hc
  refine le_antisymm h1 ?_
  have := mul_le_mul_right h2 (Q.valuation (algebraMap k κ c))
  rwa [mul_inv_cancel₀ h0, mul_one] at this

/-- The branches through a node point of `e`: outer ones (over the parent, zeros of `x̄_e`) and
inner ones (over the child, zeros of `(c_e/x_e)‾`). -/
theorem TreeData.Sp_cases (P : T.Pt hx₀ hp hp1) {β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))}
    (hβ : β ∈ T.Sp hx₀ hp hp1 P) :
    (IsOver (T.hvc hx₀ (T.par P.1)) β.1.1 ∧ β.2.valuation (β.1.1.red (T.ec x₀ P.1)) < 1) ∨
    (IsOver (T.hvc hx₀ (T.chi P.1)) β.1.1 ∧
      β.2.valuation (β.1.1.red (algebraMap C F (T.ce P.1) / T.ec x₀ P.1)) < 1) := by
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  simp only [TreeData.Sp, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image] at hβ
  rcases hβ with ⟨b, -, rfl⟩ | ⟨b, -, rfl⟩
  · refine Or.inl ⟨(T.isOver_ec_iff hx₀ _ _).2 (TypeTwo.isOver_ofComap _ _ b.1.2), ?_⟩
    have h := valuation_x_lt_one b.2.2
    have hx : xF C F = T.ec x₀ P.1 := xF_coord (T.hec hx₀ P.1)
    exact (congrArg (fun t ↦ b.2.1.valuation (red C t b.1)) hx.symm).trans_lt h
  · refine Or.inr ⟨(T.isOver_inner_iff hx₀ _ _).2 (TypeTwo.isOver_ofComap (T.hinner hx₀ P.1) _
      (T.inner_comap hx₀ P.1 b)), ?_⟩
    have hxI : xF C (Inv (T.ce P.1) (T.ce_ne_zero P.1) F) =
        algebraMap C F (T.ce P.1) / T.ec x₀ P.1 := by
      change algebraMap (RatFunc C) (Inv (T.ce P.1) (T.ce_ne_zero P.1) F) RatFunc.X = _
      rw [T.algebraMap_inv hx₀ P.1]
      exact coordAlgHom_X (T.hinner hx₀ P.1)
    have h := valuation_x_lt_one b.2.2
    exact (congrArg (fun t ↦ b.2.1.valuation (red C t b.1)) hxI.symm).trans_lt h

omit [CharZero C] in
/-- At an outer branch, the vertex coordinate is regular. -/
lemma red_vc_mem_of_outer {e : T.E} {W : TypeTwo C F} (hW : IsOver (T.hvc hx₀ (T.par e)) W)
    {Q : CurvePlace 𝓀 (ResidueField W.val.valuationSubring)}
    (hQ : Q.valuation (W.red (T.ec x₀ e)) < 1) : W.red (T.vc x₀ (T.par e)) ∈ Q.V := by
  have hδ : ‖-((T.a (T.chi e) - T.a (T.par e)) / T.c (T.par e))‖ ≤ 1 := by
    rw [norm_neg, norm_div, div_le_one (norm_pos_iff.2 (T.hc _))]
    exact T.hedge_a e
  have hec := T.ec_eq (x₀ := x₀) e
  rw [map_one, one_mul] at hec
  have h1 : W.red (T.ec x₀ e) = W.red (T.vc x₀ (T.par e)) + algebraMap 𝓀 _ (residue _
      ⟨_, (HenselComplete.mem_integers_iff _).2 hδ⟩) := by
    rw [hec, TypeTwo.red_add (by rw [hW.valuation_self])
      (by rw [TypeTwo.valuation_algebraMap]; exact_mod_cast hδ), TypeTwo.red_algebraMap _ hδ]
  have h2 : W.red (T.vc x₀ (T.par e)) = W.red (T.ec x₀ e) - algebraMap 𝓀 _ (residue _
      ⟨_, (HenselComplete.mem_integers_iff _).2 hδ⟩) := by rw [h1]; ring
  rw [h2]
  exact sub_mem (Q.valuation_le_one_iff.1 hQ.le) (Q.algebraMap_mem _)

omit [CharZero C] in
/-- At an inner branch, the vertex coordinate has a pole. -/
lemma red_vc_notMem_of_inner {e : T.E} {W : TypeTwo C F} (hW : IsOver (T.hvc hx₀ (T.chi e)) W)
    {Q : CurvePlace 𝓀 (ResidueField W.val.valuationSubring)}
    (hQ : Q.valuation (W.red (algebraMap C F (T.ce e) / T.ec x₀ e)) < 1) :
    W.red (T.vc x₀ (T.chi e)) ∉ Q.V := by
  intro hmem
  rw [T.inner_eq (x₀ := x₀) e, TypeTwo.red_inv hW.valuation_self, map_inv₀] at hQ
  have h0 : W.red (T.vc x₀ (T.chi e)) ≠ 0 := TypeTwo.red_ne_zero hW.valuation_self
  have h1 := Q.valuation_le_one_iff.2 hmem
  have := mul_lt_one_of_nonneg_of_lt_one_left zero_le hQ h1
  rw [inv_mul_cancel₀ ((Valuation.ne_zero_iff _).2 h0)] at this
  exact lt_irrefl _ this

/-- Membership in a node point is read off at any branch through it. -/
theorem TreeData.mem_iff (P : T.Pt hx₀ hp hp1) {β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))}
    (hβ : β ∈ T.Sp hx₀ hp hp1 P) (r : letI := T.edgeAlg hx₀ P.1; Rint (T.ce P.1) F) :
    r ∈ P.2.1 ↔ β.2.res (β.1.1.red (r : F)) = 0 := by
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  obtain ⟨b₀, hb₀⟩ := T.exists_outer hx₀ hp hp1 P
  have h := T.branch_spec hx₀ hp hp1 P hβ b₀ hb₀ r
  have h2 := h.2.2
  have hb₀' : placeIdeal (T.norm_ce_lt_one P.1) b₀.1 b₀.2.2 = P.2.1 := hb₀
  exact ((Iff.of_eq (congrArg (r ∈ ·) hb₀'.symm)).trans RingHom.mem_ker).trans
    (Eq.congr_left h2).symm

/-- Every node point has a branch. -/
theorem TreeData.Sp_nonempty (P : T.Pt hx₀ hp hp1) : (T.Sp hx₀ hp hp1 P).Nonempty := by
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  obtain ⟨b₀, hb₀⟩ := T.exists_outer hx₀ hp hp1 P
  refine ⟨T.outBr hx₀ hp hp1 P.1 b₀, ?_⟩
  simp only [TreeData.Sp, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image]
  exact Or.inl ⟨b₀, hb₀, rfl⟩

/-- Distinct node points have disjoint branch sets. -/
theorem TreeData.Sp_disjoint (P Q : T.Pt hx₀ hp hp1) (hPQ : P ≠ Q) :
    Disjoint (T.Sp hx₀ hp hp1 P) (T.Sp hx₀ hp hp1 Q) := by
  rw [Finset.disjoint_left]
  intro β hP hQ
  apply hPQ
  have he : P.1 = Q.1 := by
    rcases T.Sp_cases hx₀ hp hp1 P hP with ⟨hW, hv⟩ | ⟨hW, hv⟩ <;>
      rcases T.Sp_cases hx₀ hp hp1 Q hQ with ⟨hW', hv'⟩ | ⟨hW', hv'⟩
    · have hpar := T.eq_of_isOver hx₀ hW hW'
      by_contra hne
      have hdir := T.hdir _ _ hpar hne
      set γ : C := (T.a (T.chi Q.1) - T.a (T.chi P.1)) / T.c (T.par P.1)
      have hγ : ‖γ‖ = 1 := by
        rw [norm_div, norm_sub_rev, hdir, div_self (norm_ne_zero_iff.2 (T.hc _))]
      have hdiff : T.ec x₀ P.1 - T.ec x₀ Q.1 = algebraMap C F γ := by
        have hc : algebraMap C F (T.c (T.par P.1)) ≠ 0 := by simpa using T.hc _
        simp only [TreeData.ec, vcoord, γ, ← hpar, map_div₀, _root_.map_sub]
        field_simp
        ring
      have h1 : β.1.1.val (T.ec x₀ P.1) ≤ 1 :=
        ((T.isOver_ec_iff hx₀ _ _).1 hW).valuation_self.le
      have h2 : β.1.1.val (T.ec x₀ Q.1) ≤ 1 :=
        ((T.isOver_ec_iff hx₀ _ _).1 hW').valuation_self.le
      have hred := TypeTwo.red_sub (W := β.1.1) h1 h2
      rw [hdiff, TypeTwo.red_algebraMap _ hγ.le] at hred
      have hlt : β.2.valuation (β.1.1.red (T.ec x₀ P.1) - β.1.1.red (T.ec x₀ Q.1)) < 1 :=
        (Valuation.map_sub _ _ _).trans_lt (max_lt hv hv')
      rw [← hred, β.2.valuation_algebraMap_eq_one' (residue_ne_zero_of_norm_eq_one hγ)] at hlt
      exact lt_irrefl _ hlt
    · exfalso
      have hi := T.eq_of_isOver hx₀ hW hW'
      have h1 := red_vc_mem_of_outer T hx₀ hW hv
      rw [hi] at h1
      exact red_vc_notMem_of_inner T hx₀ hW' hv' h1
    · exfalso
      have hi := T.eq_of_isOver hx₀ hW' hW
      have h1 := red_vc_mem_of_outer T hx₀ hW' hv'
      rw [hi] at h1
      exact red_vc_notMem_of_inner T hx₀ hW hv h1
    · exact T.hchi _ _ (T.eq_of_isOver hx₀ hW hW')
  obtain ⟨e, P', hP'⟩ := P
  obtain ⟨e', Q', hQ'⟩ := Q
  simp only at he
  subst he
  have : P' = Q' := Ideal.ext fun r ↦
    (T.mem_iff hx₀ hp hp1 ⟨e, P', hP'⟩ hP r).trans (T.mem_iff hx₀ hp hp1 ⟨e, Q', hQ'⟩ hQ r).symm
  subst this
  rfl

end Structure

section Zero

omit [IsAlgClosed C] [CharZero C] [IsCurveFunctionField C F] in
lemma red_ec_eq {e : T.E} {W : TypeTwo C F} (hW : IsOver (T.hvc hx₀ (T.par e)) W)
    (hδ : ‖-((T.a (T.chi e) - T.a (T.par e)) / T.c (T.par e))‖ ≤ 1) :
    W.red (T.ec x₀ e) = W.red (T.vc x₀ (T.par e)) + algebraMap 𝓀 _ (residue _
      ⟨_, (HenselComplete.mem_integers_iff _).2 hδ⟩) := by
  have hec := T.ec_eq (x₀ := x₀) e
  rw [map_one, one_mul] at hec
  rw [hec, TypeTwo.red_add (by rw [hW.valuation_self])
    (by rw [TypeTwo.valuation_algebraMap]; exact_mod_cast hδ), TypeTwo.red_algebraMap _ hδ]

/-- **The divisors `D̄_{m,W}` vanish at the branches through node points.** -/
theorem TreeData.Db_branch (m : ℕ) (P : T.Pt hx₀ hp hp1)
    {β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))} (hβ : β ∈ T.Sp hx₀ hp hp1 P) :
    T.Db hx₀ hp hp1 m β.1 β.2 = 0 := by
  suffices h : (β.1.1.red (T.vc x₀ (T.vtx hx₀ hp hp1 β.1)) -
      algebraMap 𝓀 _ (T.βbar (T.vtx hx₀ hp hp1 β.1)))⁻¹ ∈ β.2.V by
    rw [TreeData.Db, Finsupp.smul_apply, zeroDiv, poleDivisor_apply,
      (β.2.poleOrder_eq_zero_iff).2 h]
    simp
  rcases T.Sp_cases hx₀ hp hp1 P hβ with ⟨hW, hv⟩ | ⟨hW, hv⟩
  · rw [T.vtx_eq hx₀ hp hp1 hW]
    set t := β.1.1.red (T.vc x₀ (T.par P.1)) - algebraMap 𝓀 _ (T.βbar (T.par P.1))
    by_contra hinv
    have ht0 : t ≠ 0 := fun h ↦ hinv (by rw [h, inv_zero]; exact zero_mem _)
    have hlt : β.2.valuation t < 1 := by
      have h1 : ¬ β.2.valuation t⁻¹ ≤ 1 := fun h ↦ hinv (β.2.valuation_le_one_iff.1 h)
      rw [map_inv₀, not_le] at h1
      have h0 : β.2.valuation t ≠ 0 := (Valuation.ne_zero_iff _).2 ht0
      by_contra h2
      rw [not_lt] at h2
      exact absurd (inv_le_one_of_one_le₀ h2) (not_le.2 h1)
    have hδ : ‖-((T.a (T.chi P.1) - T.a (T.par P.1)) / T.c (T.par P.1))‖ ≤ 1 := by
      rw [norm_neg, norm_div, div_le_one (norm_pos_iff.2 (T.hc _))]
      exact T.hedge_a _
    set γ : C := T.β (T.par P.1) - (T.a (T.chi P.1) - T.a (T.par P.1)) / T.c (T.par P.1)
    have hγ : ‖γ‖ = 1 := by
      have : γ = (T.b (T.par P.1) - T.a (T.chi P.1)) / T.c (T.par P.1) := by
        simp only [γ, TreeData.β]
        field_simp [T.hc (T.par P.1)]
        ring
      rw [this, norm_div, T.hb_free, div_self (norm_ne_zero_iff.2 (T.hc _))]
    have hdiff : β.1.1.red (T.ec x₀ P.1) - t = algebraMap 𝓀 _ (residue _
        ⟨γ, (HenselComplete.mem_integers_iff _).2 hγ.le⟩) := by
      rw [red_ec_eq T hx₀ hW hδ]
      simp only [t, TreeData.βbar]
      rw [add_sub_sub_cancel, ← map_add, ← map_add]
      congr 2
      apply Subtype.ext
      simp only [γ, AddMemClass.mk_add_mk]
      ring
    have hlt' : β.2.valuation (β.1.1.red (T.ec x₀ P.1) - t) < 1 :=
      (Valuation.map_sub _ _ _).trans_lt (max_lt hv hlt)
    rw [hdiff, β.2.valuation_algebraMap_eq_one' (residue_ne_zero_of_norm_eq_one hγ)] at hlt'
    exact lt_irrefl _ hlt'
  · rw [T.vtx_eq hx₀ hp hp1 hW]
    have hnot := red_vc_notMem_of_inner T hx₀ hW hv
    refine (β.2.V.mem_or_inv_mem _).resolve_left fun h ↦ hnot ?_
    have : β.1.1.red (T.vc x₀ (T.chi P.1)) = (β.1.1.red (T.vc x₀ (T.chi P.1)) -
        algebraMap 𝓀 _ (T.βbar (T.chi P.1))) + algebraMap 𝓀 _ (T.βbar (T.chi P.1)) := by ring
    rw [this]
    exact add_mem h (β.2.algebraMap_mem _)

end Zero

section Twist

/-- The twist of the edge `e` is a unit at every branch through a node point of `e`. -/
theorem TreeData.res_twist_ne_zero (m : ℕ) (P : T.Pt hx₀ hp hp1)
    {β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))} (hβ : β ∈ T.Sp hx₀ hp hp1 P) :
    β.1.1.val (∏ j, T.mu x₀ P.1 j ^ m) = 1 ∧
      β.1.1.red (∏ j, T.mu x₀ P.1 j ^ m) ∈ β.2.V ∧
      β.2.res (β.1.1.red (∏ j, T.mu x₀ P.1 j ^ m)) ≠ 0 := by
  have key : (∀ j, β.1.1.val (T.mu x₀ P.1 j) = 1) ∧
      ∀ j, β.1.1.red (T.mu x₀ P.1 j) ∈ β.2.V ∧ β.2.res (β.1.1.red (T.mu x₀ P.1 j)) ≠ 0 := by
    rcases T.Sp_cases hx₀ hp hp1 P hβ with ⟨hW, hv⟩ | ⟨hW, hv⟩
    · exact ⟨valuation_mu_par T hx₀ hW, res_red_mu_par T hx₀ hW β.2 hv⟩
    · exact ⟨valuation_mu_chi T hx₀ hW, res_red_mu_chi T hx₀ hW β.2 hv⟩
  have hv1 : β.1.1.val (∏ j, T.mu x₀ P.1 j ^ m) = 1 := by
    simp only [map_prod, map_pow, key.1, one_pow, Finset.prod_const_one]
  refine ⟨hv1, ?_⟩
  have hu := res_prod_ne_zero β.2 Finset.univ (fun j ↦ β.1.1.red (T.mu x₀ P.1 j ^ m)) fun j _ ↦ by
    rw [TypeTwo.red_pow (key.1 j).le]
    exact res_pow_ne_zero β.2 (key.2 j).1 (key.2 j).2 m
  rwa [TypeTwo.red_prod _ _ fun j _ ↦ by rw [map_pow, key.1 j, one_pow]]

omit [IsUltrametricDist C] [CharZero C] in
lemma TreeData.one_mem_rrSpace (m : ℕ) : (1 : F) ∈ rrSpace (T.D x₀ m) := by
  intro Q
  rw [map_one, ← exp_zero, exp_le_exp]
  have : 0 ≤ T.D x₀ m :=
    nsmul_nonneg (Finset.sum_nonneg fun j _ ↦ poleDivisor_nonneg _) m
  exact this Q

/-- **(H3) The reductions of `L(D_m)°` satisfy the conditions at every node point**: `f = (f h)/h`
with the twist `h ∉ P'` and `f h ∈ R'_e`. -/
theorem TreeData.redVec_mem_Oc (m : ℕ) {f : F} (hf : f ∈ rrSpace (T.D x₀ m))
    (hn : mnorm (T.S hx₀ hp hp1) f ≤ 1) (P : T.Pt hx₀ hp hp1) :
    redVec (T.S hx₀ hp hp1) f ∈ T.Oc hx₀ hp hp1 P := by
  letI := T.edgeAlg hx₀ P.1
  haveI := T.edgeTower hx₀ P.1
  haveI := T.edgeFin hx₀ P.1
  have hn' (i : T.ι) (W : TypeTwo C F) (h : IsOver (T.hvc hx₀ i) W) : W.val f ≤ 1 :=
    (le_mnorm ((T.mem_S hx₀ hp hp1 W).2 ⟨i, h⟩) f).trans hn
  have hn1 (i : T.ι) (W : TypeTwo C F) (_ : IsOver (T.hvc hx₀ i) W) : W.val (1 : F) ≤ 1 := by
    simp
  have hy := isIntegral_twist T hx₀ hp hp1 hf hn' P.1
  have hs := isIntegral_twist T hx₀ hp hp1 (T.one_mem_rrSpace (x₀ := x₀) m) hn1 P.1
  set h := ∏ j, T.mu x₀ P.1 j ^ m
  have hs' : IsIntegral (nodeRing (T.ce P.1)) h := by simpa only [one_mul] using hs
  obtain ⟨β₀, hβ₀⟩ := T.Sp_nonempty hx₀ hp hp1 P
  refine ⟨⟨f * h, hy⟩, ⟨h, hs'⟩, fun hmem ↦ ?_, fun β hβ ↦ ?_⟩
  · have := (T.mem_iff hx₀ hp hp1 P hβ₀ ⟨h, hs'⟩).1 hmem
    exact (T.res_twist_ne_zero hx₀ hp hp1 m P hβ₀).2.2 this
  · have hf1 : β.1.1.val f ≤ 1 := (le_mnorm β.1.2 f).trans hn
    have hh1 := (T.res_twist_ne_zero hx₀ hp hp1 m P hβ).1
    exact (TypeTwo.red_mul hf1 hh1.le).symm

end Twist

section Count

/-- **The δ-count for a Gauss tree** (S7.6, `b₁` form):
`Σ_W g(κ(W)) + Σ_{P'} (r_{P'} - 1) ≤ g(F) + #S - 1`, the sum over all node points `P'` of all
edges, `r_{P'}` the number of branches through `P'`. -/
theorem TreeData.delta_count :
    (∑ W : T.S hx₀ hp hp1, (genus 𝓀 (Kappa (T.S hx₀ hp hp1) W) : ℤ)) +
      ∑ P : T.Pt hx₀ hp hp1, (((T.Sp hx₀ hp hp1 P).card : ℤ) - 1) ≤
        genus C F + (T.S hx₀ hp hp1).card - 1 :=
  sum_genus_add_sum_card_sub_one_le hp hp1 (T.vc x₀) (T.hvc hx₀) (T.S hx₀ hp hp1)
    (T.mem_S hx₀ hp hp1) (T.D x₀) (T.Db hx₀ hp hp1) (T.sum_degree_Db hx₀ hp hp1)
    (T.le_degree_Db hx₀ hp hp1) (fun m _ hf hn ↦ T.redVec_mem hx₀ hp hp1 m hf hn)
    (T.Sp hx₀ hp hp1) (T.Sp_disjoint hx₀ hp hp1) (fun m P _ hβ ↦ T.Db_branch hx₀ hp hp1 m P hβ)
    (T.Oc hx₀ hp hp1) (fun m _ hf hn P ↦ T.redVec_mem_Oc hx₀ hp hp1 m hf hn P)
    (T.Oc_le_eqRes hx₀ hp hp1) (T.Sp_nonempty hx₀ hp hp1)

/-- **The reverse inequality gives the jets** (S7.6 with S8 or S7⁺): if
`g(F) + #S - 1 ≤ Σ_W g(κ(W)) + Σ_{P'} (r_{P'} - 1)`, then at every node point and every jet order
`M ≥ 1`, every vector regular at the branches with equal residues there is, up to order `M` at the
branches, a fraction `y / s` of `R'_e` with `s ∉ P'`. -/
theorem TreeData.jets_of_le
    (hS8 : genus C F + (T.S hx₀ hp hp1).card - 1 ≤
      (∑ W : T.S hx₀ hp hp1, (genus 𝓀 (Kappa (T.S hx₀ hp hp1) W) : ℤ)) +
        ∑ P : T.Pt hx₀ hp hp1, (((T.Sp hx₀ hp hp1 P).card : ℤ) - 1))
    (P : T.Pt hx₀ hp hp1) {M : ℕ} (hM : 1 ≤ M) :
    eqRes 𝓀 (Kappa (T.S hx₀ hp hp1)) (T.Sp hx₀ hp hp1 P) ≤
      T.Oc hx₀ hp hp1 P ⊔ jetKer 𝓀 (Kappa (T.S hx₀ hp hp1)) M (T.Sp hx₀ hp hp1 P) :=
  eqRes_le_sup_jetKer hp hp1 (T.vc x₀) (T.hvc hx₀) (T.S hx₀ hp hp1)
    (T.mem_S hx₀ hp hp1) (T.D x₀) (T.Db hx₀ hp hp1) (T.sum_degree_Db hx₀ hp hp1)
    (T.le_degree_Db hx₀ hp hp1) (fun m _ hf hn ↦ T.redVec_mem hx₀ hp hp1 m hf hn)
    (T.Sp hx₀ hp hp1) (T.Sp_disjoint hx₀ hp hp1) (fun m P _ hβ ↦ T.Db_branch hx₀ hp hp1 m P hβ)
    (T.Oc hx₀ hp hp1) (fun m _ hf hn P ↦ T.redVec_mem_Oc hx₀ hp hp1 m hf hn P)
    (T.Oc_le_eqRes hx₀ hp hp1) (T.Sp_nonempty hx₀ hp hp1) hS8 P hM

end Count

section ODP

set_option maxHeartbeats 400000 in
-- comparing the inner branch with its image in the vertex set unfolds the twisted structure
/-- **Ordinary double points from the reverse inequality** (S7.6 ⇒ the hypothesis of
`GaussTube.isNodeODP_of_jets`): under `g(F) + #S - 1 ≤ Σ_W g(κ(W)) + Σ_{P'} (r_{P'} - 1)`, every
point of the normalized node chart of an edge with exactly one outer and one inner branch is an
ordinary double point. -/
theorem TreeData.isNodeODP_of_le
    (hS8 : genus C F + (T.S hx₀ hp hp1).card - 1 ≤
      (∑ W : T.S hx₀ hp hp1, (genus 𝓀 (Kappa (T.S hx₀ hp hp1) W) : ℤ)) +
        ∑ P : T.Pt hx₀ hp hp1, (((T.Sp hx₀ hp hp1 P).card : ℤ) - 1)) (e : T.E) :
    letI := T.edgeAlg hx₀ e
    haveI := T.edgeTower hx₀ e
    haveI := T.edgeFin hx₀ e
    ∀ (P' : Ideal (Rint (T.ce e) F)) (b₁ : OuterBranch C F)
      (b₂ : OuterBranch C (Inv (T.ce e) (T.ce_ne_zero e) F)),
      outerBranches (T.norm_ce_lt_one e) P' = {b₁} →
      innerBranches (T.norm_ce_lt_one e) (T.ce_ne_zero e) P' = {b₂} →
      IsNodeODP (T.norm_ce_lt_one e) (T.ce_ne_zero e) P' := by
  classical
  letI := T.edgeAlg hx₀ e
  haveI := T.edgeTower hx₀ e
  haveI := T.edgeFin hx₀ e
  intro P' b₁ b₂ h₁ h₂
  have hc := T.norm_ce_lt_one e
  have hc0 := T.ce_ne_zero e
  have hb₁ : b₁ ∈ outerBranches hc P' := by rw [h₁]; rfl
  have hb₂ : b₂ ∈ innerBranches hc hc0 P' := by rw [h₂]; rfl
  have hmem : P' ∈ T.NP hx₀ hp hp1 e := by
    simp only [TreeData.NP, Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨b₁, hb₁⟩
  set P : T.Pt hx₀ hp hp1 := ⟨e, ⟨P', hmem⟩⟩
  set β₁ := T.outBr hx₀ hp hp1 e b₁
  set β₂ := T.inBr hx₀ hp hp1 e b₂
  have hβ₁ : β₁ ∈ T.Sp hx₀ hp hp1 P := by
    simp only [TreeData.Sp, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image]
    exact Or.inl ⟨b₁, hb₁, rfl⟩
  have hβ₂ : β₂ ∈ T.Sp hx₀ hp hp1 P := by
    simp only [TreeData.Sp, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image]
    exact Or.inr ⟨b₂, hb₂, rfl⟩
  have hSp (β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))) (hβ : β ∈ T.Sp hx₀ hp hp1 P) :
      β = β₁ ∨ β = β₂ := by
    simp only [TreeData.Sp, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_image] at hβ
    rcases hβ with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · change b ∈ outerBranches hc P' at hb
      rw [h₁, Set.mem_singleton_iff] at hb
      exact Or.inl (by rw [hb])
    · change b ∈ innerBranches hc hc0 P' at hb
      rw [h₂, Set.mem_singleton_iff] at hb
      exact Or.inr (by rw [hb])
  -- the two vertices are distinct
  have hW₁ : IsOver (T.hvc hx₀ (T.par e)) β₁.1.1 :=
    (T.isOver_ec_iff hx₀ _ _).2 (TypeTwo.isOver_ofComap _ _ b₁.1.2)
  have hW₂ : IsOver (T.hvc hx₀ (T.chi e)) β₂.1.1 :=
    (T.isOver_inner_iff hx₀ _ _).2 (TypeTwo.isOver_ofComap _ _ (T.inner_comap hx₀ e b₂))
  have hne : β₁.1 ≠ β₂.1 := by
    intro h
    rw [h] at hW₁
    have := T.eq_of_isOver hx₀ hW₁ hW₂
    have h2 := T.hedge_c e
    rw [this] at h2
    exact lt_irrefl _ h2
  refine isNodeODP_of_jets hc hc0 hp hp1 h₁ h₂ fun a ha b hb hab M ↦ ?_
  set z : Π W : T.S hx₀ hp hp1, Kappa (T.S hx₀ hp hp1) W :=
    Pi.single β₁.1 (a : Kappa (T.S hx₀ hp hp1) β₁.1) +
      Pi.single β₂.1 (b : Kappa (T.S hx₀ hp hp1) β₂.1)
  have hz₁ : z β₁.1 = a := by simp [z, hne]
  have hz₂ : z β₂.1 = b := by simp [z, hne.symm]
  have hzeq : z ∈ eqRes 𝓀 (Kappa (T.S hx₀ hp hp1)) (T.Sp hx₀ hp hp1 P) := by
    have hreg (β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))) (hβ : β ∈ T.Sp hx₀ hp hp1 P) :
        z β.1 ∈ β.2.V ∧ β.2.res (z β.1) = b₁.2.1.res a := by
      rcases hSp β hβ with rfl | rfl
      · refine ⟨?_, ?_⟩
        · rw [hz₁]; exact ha
        · rw [hz₁]; rfl
      · refine ⟨?_, ?_⟩
        · rw [hz₂]; exact hb
        · rw [hz₂]; exact hab.symm
    exact ⟨fun β hβ ↦ (hreg β hβ).1, fun β hβ β' hβ' ↦ (hreg β hβ).2.trans (hreg β' hβ').2.symm⟩
  obtain ⟨o, ho, j, hj, hoj⟩ := Submodule.mem_sup.1
    (T.jets_of_le hx₀ hp hp1 hS8 P (M := M + 1) (by omega) hzeq)
  obtain ⟨y, s, hs, hys⟩ := ho
  have hfrac (β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))) (hβ : β ∈ T.Sp hx₀ hp hp1 P) :
      β.1.1.red (y : F) / β.1.1.red (s : F) - z β.1 = -j β.1 := by
    rw [← hys β hβ, mul_div_cancel_right₀ _ (T.red_ne_zero' hx₀ hp hp1 P hβ hs), ← hoj,
      Pi.add_apply]
    ring
  have hval (β : Branch 𝓀 (Kappa (T.S hx₀ hp hp1))) (hβ : β ∈ T.Sp hx₀ hp hp1 P) :
      β.2.valuation (β.1.1.red (y : F) / β.1.1.red (s : F) - z β.1) ≤ exp (-(M : ℤ)) := by
    rw [hfrac β hβ, Valuation.map_neg]
    refine (hj β hβ).trans (exp_le_exp.2 ?_)
    push_cast
    omega
  refine ⟨y, s, hs, ?_, ?_⟩
  · have := hval β₁ hβ₁
    rw [hz₁] at this
    exact this
  · have := hval β₂ hβ₂
    rw [hz₂] at this
    exact this

end ODP

end TreeCount

end SemistableReduction
