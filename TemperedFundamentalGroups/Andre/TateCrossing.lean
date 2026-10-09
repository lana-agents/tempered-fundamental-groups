/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateCrossingWalk
import TemperedFundamentalGroups.Andre.FunctionFieldFinite
import TemperedFundamentalGroups.SemistableReduction.CrossingX1

/-!
# `HarmonicTate` from `CrossingX1` (Blueprint §10.3.8)

For a member `Q` (with W-model data `D = Q.D`) and `a : Q.U ⟶ X₀`, the model map
`Q.tateψ : D.c' ⟶ tgtModel T` (the Tate model as the projective model of the function field
`L₂ = TateField` of the Tate curve) satisfies the hypotheses of `Statement.CrossingX1`:

* `L₂ ⊆ L₁ = D.L₁` through `TateNormal.toField` (`X ↦ x/π`, `Y ↦ y/π`) (`L₁ / L₂` is finite,
  `finiteDimensional_toF`, though `CrossingX1` no longer needs it);
* the generic points are compatible (`TateNormal.toModel_comp_modelIso`, naturality of `toModel`);
* the generic point of `tgtModel T` is dominant;

(`Pres.crossing_tate`). With the node germs at `p` and `q` (`TateNormal.nodeGerm_p`, `nodeGerm_q`)
and, for `b₆` a unit, the components `C` and `E` of the special fibre, this gives
`Pres.HarmonicTate T {E} a` (`Pres.harmonicTate_of_crossingX1`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open SemistableReduction.ProjScheme

namespace TemperedFundamentalGroups

noncomputable section

open TempObj CurveConfig TateObject

attribute [local instance] TateNormal.algK

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] {x : R}
  (T : TateObject.Data O R) [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))]

namespace Pres

variable {Y : TempObj O R A} (Q : Pres x Y)

/-- `R → L₁`, through the ring of the level. -/
def rhoL : R →+* Q.D.L₁ := (algebraMap Q.Lv.L.B Q.D.L₁).comp (algebraMap R Q.Lv.L.B)

omit [IsDiscreteValuationRing O] [IsReduced R] [Subsingleton A] in
lemma rhoL_injective [IsDomain R] : Function.Injective Q.rhoL := by
  haveI := Q.D.isDomain
  haveI := Q.Lv.L.etale
  haveI := Q.Lv.L.finite
  rw [rhoL, RingHom.coe_comp]
  exact (IsFractionRing.injective Q.Lv.L.B Q.D.L₁).comp algebraMap_injective_of_flat

omit [IsDiscreteValuationRing O] [IsReduced R] [Subsingleton A] in
lemma algKL_eq : @algebraMap K Q.D.L₁ _ _ Q.D.algKL = Q.rhoL.comp (algebraMap K R) := rfl

omit [IsDiscreteValuationRing O] [IsReduced R] [Subsingleton A]
  [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))] in
lemma equation_rhoL : Q.rhoL T.y ^ 2 + Q.rhoL T.x * Q.rhoL T.y = Q.rhoL T.x ^ 3 +
    ((@algebraMap K Q.D.L₁ _ _ Q.D.algKL).comp O.subtype) (T.π ^ 2 * T.b₄) * Q.rhoL T.x +
    ((@algebraMap K Q.D.L₁ _ _ Q.D.algKL).comp O.subtype) (T.π ^ 2 * T.b₆) := by
  have := congrArg Q.rhoL T.equation
  simp only [map_add, map_mul, map_pow] at this
  rw [algKL_eq]
  simpa using this

omit [IsDiscreteValuationRing O] [IsReduced R] [Subsingleton A]
  [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))] in
lemma transcendental_rhoL [IsDomain R] (hx : Transcendental K T.x) :
    letI := (@algebraMap K Q.D.L₁ _ _ Q.D.algKL).toAlgebra
    Transcendental K (Q.rhoL T.x) := by
  letI := Q.D.algKL
  let f : R →ₐ[K] Q.D.L₁ := { Q.rhoL with commutes' := fun _ => rfl }
  intro h
  exact hx ((isAlgebraic_algHom_iff f (Q.rhoL_injective)).1 h)

omit [IsDiscreteValuationRing O] [IsReduced R] [Subsingleton A]
  [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))] in
lemma algKL_π_ne_zero : @algebraMap K Q.D.L₁ _ _ Q.D.algKL (T.π : K) ≠ 0 :=
  (map_ne_zero _).2 fun h => T.π_ne_zero (Subtype.ext h)

/-- The embedding of the function field of the Tate curve into `L₁`. -/
abbrev toF [IsDomain R] (hx : Transcendental K T.x) :
    TateNormal.TateField T.π T.b₄ T.b₆ →+* Q.D.L₁ :=
  TateNormal.toField T.π T.b₄ T.b₆ (@algebraMap K Q.D.L₁ _ _ Q.D.algKL)
    (Q.algKL_π_ne_zero T) (Q.equation_rhoL T) (Q.transcendental_rhoL T hx)

section Crossing

variable [Algebra.Smooth K R] [IsDomain R]

omit [IsReduced R] [Subsingleton A] in
/-- `L₁` is finite over the function field of the Tate curve. -/
theorem finiteDimensional_toF (hx : Transcendental K T.x) :
    letI := (Q.toF T hx).toAlgebra
    FiniteDimensional (TateNormal.TateField T.π T.b₄ T.b₆) Q.D.L₁ := by
  set F := TateNormal.TateField T.π T.b₄ T.b₆
  letI : Algebra K Q.D.L₁ := Q.D.algKL
  haveI : IsScalarTower K Q.D.K' Q.D.L₁ := Q.D.isScalarTower_K
  set φ := Q.toF T hx
  letI : Algebra F Q.D.L₁ := φ.toAlgebra
  haveI : IsScalarTower K F Q.D.L₁ := IsScalarTower.of_algebraMap_eq fun k =>
    (RingHom.congr_fun (TateNormal.toField_comp_algK T.π T.b₄ T.b₆ _
      (Q.algKL_π_ne_zero T) (Q.equation_rhoL T) (Q.transcendental_rhoL T hx)) k).symm
  obtain ⟨hu, ι, _, _, a', b', hW, -⟩ := Q.D.wmodel
  haveI := Q.D.isDomain
  haveI := Q.Lv.L.finite
  haveI : Algebra.FiniteType K Q.Lv.L.B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K R) inferInstance
  haveI : IsScalarTower K Q.Lv.L.B Q.D.L₁ :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := Q.Lv.L.B) (A := Q.D.L₁) fun k => by
      rw [IsScalarTower.algebraMap_apply K R Q.Lv.L.B]
      rfl
  have ht : Transcendental K (algebraMap F Q.D.L₁ (TateNormal.aL T.π T.b₄ T.b₆)) := fun h =>
    TateNormal.transcendental_aL T.π T.b₄ T.b₆
      ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K F Q.D.L₁) φ.injective).1 h)
  exact finiteDimensional_of_transcendental (K' := Q.D.K') hu hW.1 _ ht (B := Q.Lv.L.B)

set_option maxHeartbeats 1600000 in
-- the final type check unfolds the level maps of `Q.U` and `Q` (definitionally equal)
omit [Algebra.Smooth K R] in
/-- **The generic points are compatible**: `j₁ ≫ ψ = Spec (L₁ ← L₂) ≫ j₂`. -/
theorem tateψ_generic (hx : Transcendental K T.x) (a : Q.U ⟶ X₀ (A := A) T) :
    Q.D.j₁ ≫ Q.tateψ T a = Spec.map (CommRingCat.ofHom (Q.toF T hx)) ≫
      genericPt O (TateNormal.hcoords T.π T.b₄ T.b₆ T.π_ne_zero) := by
  let F := TateNormal.TateField T.π T.b₄ T.b₆
  let φ := Q.toF T hx
  let g₁ : (X₀ (A := A) T).Lv.L.B →+* Q.D.L₁ :=
    (algebraMap Q.Lv.L.B Q.D.L₁).comp a.φ.f.toRingHom
  have hL : Q.D.j₁ ≫ Q.tateψ T a =
      (Spec.map (CommRingCat.ofHom g₁) ≫ (X₀ (A := A) T).Lv.j) ≫ (tIso (A := A) T).hom := by
    rw [Q.D.hj]
    simp only [tateψ, Category.assoc, Iso.hom_inv_id_assoc]
    have h1 : Q.Lv.j ≫ a.ψ ≫ (tIso (A := A) T).hom =
        (Spec.map (CommRingCat.ofHom (a.φ.f : (X₀ (A := A) T).Lv.L.B →+* Q.U.Lv.L.B)) ≫
          (X₀ (A := A) T).Lv.j) ≫ (tIso (A := A) T).hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) a.j_ψ)
    rw [h1]
    simp only [Category.assoc]
    exact (Spec.map_comp_assoc _ _ _).symm
  let lsm := levelStructureMap O R A (unitLevel R A)
  have hg₁ : ∀ r : R, g₁ (algebraMap R _ r) = Q.rhoL r := fun r => by
    change algebraMap Q.Lv.L.B Q.D.L₁ (a.φ.f (algebraMap R _ r)) = _
    rw [a.φ.f.commutes]
    rfl
  have hψπ := Q.algKL_π_ne_zero T
  have hφ₁ : g₁.comp lsm = (@algebraMap K Q.D.L₁ _ _ Q.D.algKL).comp O.subtype :=
    RingHom.ext fun o => hg₁ _
  have hφ₂ : φ.comp (algebraMap O F) = (@algebraMap K Q.D.L₁ _ _ Q.D.algKL).comp O.subtype :=
    RingHom.ext fun o => TateNormal.toField_algebraMap_O T.π T.b₄ T.b₆ _ (Q.algKL_π_ne_zero T)
      (Q.equation_rhoL T) (Q.transcendental_rhoL T hx) o
  have hx₂ : φ (algebraMap O F T.π * TateNormal.aL T.π T.b₄ T.b₆) = Q.rhoL T.x := by
    rw [map_mul, TateNormal.toField_algebraMap_O, TateNormal.toField_aL, mul_div_cancel₀ _ hψπ]
  have hy₂ : φ (algebraMap O F T.π * TateNormal.bL T.π T.b₄ T.b₆) = Q.rhoL T.y := by
    rw [map_mul, TateNormal.toField_algebraMap_O, TateNormal.toField_bL, mul_div_cancel₀ _ hψπ]
  have heq₁ : g₁ (algebraMap R _ T.y) ^ 2 + g₁ (algebraMap R _ T.x) * g₁ (algebraMap R _ T.y) =
      g₁ (algebraMap R _ T.x) ^ 3 + (g₁.comp lsm) (T.π ^ 2 * T.b₄) * g₁ (algebraMap R _ T.x) +
      (g₁.comp lsm) (T.π ^ 2 * T.b₆) := by
    rw [hg₁, hg₁, hφ₁]
    exact Q.equation_rhoL T
  have hπ₁ : IsUnit ((g₁.comp lsm) T.π) := by
    rw [hφ₁]; exact isUnit_iff_ne_zero.2 hψπ
  have heq₂ : φ (algebraMap O F T.π * TateNormal.bL T.π T.b₄ T.b₆) ^ 2 +
      φ (algebraMap O F T.π * TateNormal.aL T.π T.b₄ T.b₆) *
        φ (algebraMap O F T.π * TateNormal.bL T.π T.b₄ T.b₆) =
      φ (algebraMap O F T.π * TateNormal.aL T.π T.b₄ T.b₆) ^ 3 +
        (φ.comp (algebraMap O F)) (T.π ^ 2 * T.b₄) *
          φ (algebraMap O F T.π * TateNormal.aL T.π T.b₄ T.b₆) +
        (φ.comp (algebraMap O F)) (T.π ^ 2 * T.b₆) := by
    rw [hx₂, hy₂, hφ₂]
    exact Q.equation_rhoL T
  have hπ₂ : IsUnit ((φ.comp (algebraMap O F)) T.π) := by
    rw [hφ₂]; exact isUnit_iff_ne_zero.2 hψπ
  have hL2 : Spec.map (CommRingCat.ofHom g₁) ≫ (X₀ (A := A) T).Lv.j =
      TateModel.toModel T.π T.b₄ T.b₆ (g₁.comp lsm) heq₁ hπ₁ :=
    TateModel.SpecMap_toModel T.π T.b₄ T.b₆ lsm _ _ g₁ (T.equation_B (A := A))
      (T.isUnit_π (A := A)) heq₁ hπ₁
  have hR : Spec.map (CommRingCat.ofHom φ) ≫
      genericPt O (TateNormal.hcoords T.π T.b₄ T.b₆ T.π_ne_zero) =
      TateModel.toModel T.π T.b₄ T.b₆ (φ.comp (algebraMap O F)) heq₂ hπ₂ ≫
        (tIso (A := A) T).hom := by
    rw [← TateNormal.toModel_comp_modelIso T.π T.b₄ T.b₆ T.π_ne_zero, ← Category.assoc]
    congr 1
    exact TateModel.SpecMap_toModel T.π T.b₄ T.b₆ (algebraMap O F) _ _ φ
      (TateNormal.equation_L T.π T.b₄ T.b₆)
      (TateNormal.isUnit_algebraMap_π T.π T.b₄ T.b₆ T.π_ne_zero) heq₂ hπ₂
  rw [hL, hL2, hR]
  congr 1
  exact TateNormal.toModel_congr (hφ₁.trans hφ₂.symm) ((hg₁ _).trans hx₂.symm)
    ((hg₁ _).trans hy₂.symm) _ _ _ _

variable [CharZero K] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

omit [Algebra.Smooth K R] in
/-- **`CrossingX1` for the model map of a member to the Tate model.** -/
theorem crossing_tate (hC : SemistableReduction.Statement.CrossingX1S.{u})
    (hx : Transcendental K T.x) {ϖ : O} (hϖ : Irreducible ϖ) (a : Q.U ⟶ X₀ (A := A) T)
    (y' : (tgtModel T).scheme) (w₁' w₂' : Set (tgtModel T).scheme)
    (hw₁ : w₁' ∈ SemistableReduction.ModelCode.components (tgtModel T))
    (hw₂ : w₂' ∈ SemistableReduction.ModelCode.components (tgtModel T)) (hne : w₁' ≠ w₂')
    (hy₁ : y' ∈ w₁') (hy₂ : y' ∈ w₂')
    (hG : ∃ (P : Subring (TateNormal.TateField T.π T.b₄ T.b₆))
      (u v : TateNormal.TateField T.π T.b₄ T.b₆) (n : ℕ),
      (P : Set (TateNormal.TateField T.π T.b₄ T.b₆)) =
        SemistableReduction.ModelCode.germs (tgtModel T)
          (genericPt O (TateNormal.hcoords T.π T.b₄ T.b₆ T.π_ne_zero)) y' ∧
      _root_.SemistableReduction.NodeGerm O ϖ P u v n ∧ (∀ w ∈ P, u * w ≠ 1) ∧
        (∀ w ∈ P, v * w ≠ 1))
    (v : Set Q.D.c'.scheme) (hv : v ∈ SemistableReduction.ModelCode.components Q.D.c')
    (hψv : Q.tateψ T a '' v = w₁') :
    ∃ w : SemistableReduction.ModelCode.Walk Q.D.c', w.v 0 = v ∧ w.Crosses (Q.tateψ T a) y' ∧
      Q.tateψ T a '' w.v (Fin.last w.k) = w₂' := by
  set F := TateNormal.TateField T.π T.b₄ T.b₆
  set hf := TateNormal.hcoords T.π T.b₄ T.b₆ T.π_ne_zero
  letI : Algebra K Q.D.L₁ := Q.D.algKL
  haveI : IsScalarTower K Q.D.K' Q.D.L₁ := Q.D.isScalarTower_K
  set φ := Q.toF T hx
  letI : Algebra F Q.D.L₁ := φ.toAlgebra
  haveI : IsScalarTower K F Q.D.L₁ := IsScalarTower.of_algebraMap_eq fun k =>
    (RingHom.congr_fun (TateNormal.toField_comp_algK T.π T.b₄ T.b₆ _
      (Q.algKL_π_ne_zero T) (Q.equation_rhoL T) (Q.transcendental_rhoL T hx)) k).symm
  have h₂ : O.comap (algebraMap K K) = O := by
    ext y
    simp
  have hto : Q.tateψ T a ≫ (tgtModel T).toSpec ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap K K).restrict O O (fun y hy ↦ by rw [← h₂] at hy; exact hy))) =
      Q.D.c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K Q.D.K').restrict O Q.D.O'
        (fun y hy ↦ by rw [← Q.D.hO'] at hy; exact hy))) := by
    have hid : CommRingCat.ofHom ((algebraMap K K).restrict O O
        (fun y hy ↦ by rw [← h₂] at hy; exact hy)) = 𝟙 _ := by
      ext y
      rfl
    rw [hid, Spec.map_id, Category.comp_id, ← Q.D.toSpec_e_inv]
    simp only [tateψ, Category.assoc]
    rw [tIso_toSpec]
    exact congrArg (Q.D.e.inv ≫ ·) a.ψ_toSpec
  exact hC K O Q.D.K' K Q.D.O' O Q.D.hO' h₂ Q.D.ϖ' ϖ Q.D.hϖ' hϖ Q.D.L₁ F Q.D.xL Q.D.c'
    (tgtModel T) (Q.tateψ T a) Q.D.j₁ (genericPt O hf) Q.D.wmodel (Q.tateψ_generic T hx a) hto
    Q.D.split Q.D.noLoops (isDominant_genericPt hf).denseRange y' w₁' w₂' hw₁
    hw₂ hne hy₁ hy₂ hG v hv hψv

omit [Algebra.Smooth K R] in
/-- **`HarmonicTate` from `CrossingX1`** when `b₆` is a unit (the special fibre of the Tate model
is the 2-gon `C ∪ E` with nodes `p`, `q`). -/
theorem harmonicTate_of_crossingX1 (hC : SemistableReduction.Statement.CrossingX1S.{u})
    (hb : IsUnit T.b₆) (hx : Transcendental K T.x) {ϖ : O} (hϖ : Irreducible ϖ)
    (a : Q.U ⟶ X₀ (A := A) T) : Q.HarmonicTate T {(decomp (A := A) T).E} a := by
  have hCc := mem_irreducibleComponents_C (A := A) T
  have hEc := mem_irreducibleComponents_E (A := A) T hb
  obtain ⟨hCp, -, hpq, -⟩ := decomp_spec (A := A) T
  have hCE : (decomp (A := A) T).C ≠ (decomp (A := A) T).E := by
    obtain ⟨zC, hC', hE⟩ := TateModel.exists_closure_eq_Cset (b₄ := T.b₄) (b₆ := T.b₆) T.π_mem
    intro h
    apply hE
    change zC ∈ (decomp (A := A) T).E
    rw [← h]
    change zC ∈ TateModel.Cset T.π T.b₄ T.b₆
    rw [← hC']
    exact subset_closure rfl
  have hpC := TateModel.pZ_mem_Cset (b₄ := T.b₄) (b₆ := T.b₆) T.π_mem
  have hpE := TateModel.pZ_mem_Eset (b₄ := T.b₄) (b₆ := T.b₆) T.π_mem
  have hqC := TateModel.qZ_mem_Cset (b₄ := T.b₄) (b₆ := T.b₆) T.π_mem
  have hqE := TateModel.qZ_mem_Eset (b₄ := T.b₄) (b₆ := T.b₆) T.π_mem
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨w, hw0, hcross, hlast⟩ := Q.crossing_tate T hC hx hϖ a
      (tpt (A := A) T (TateModel.pZ T.π T.b₄ T.b₆ T.π_mem)) (tSet (A := A) T (decomp (A := A) T).C)
      (tSet (A := A) T (decomp (A := A) T).E) (tSet_mem T hCc) (tSet_mem T hEc)
      ((tSet_injective T).ne hCE) ⟨_, hpC, rfl⟩ ⟨_, hpE, rfl⟩
      (TateNormal.nodeGerm_p T.π_ne_zero T.π_mem hϖ) (Q.D.compSet i.1) (Q.D.compSet_mem i.2)
      (by rw [Q.tateψ_image_compSet T a]; exact congrArg _ hi)
    obtain ⟨L, hL, hpL, hlastL⟩ := Q.exists_incWalk_of_crosses T a w i hw0 hcross
    refine ⟨L, hL, fun p hp => ?_, ?_⟩
    · rw [tpt_injective T (hpL p hp), hCp]
      rfl
    · rw [hlast] at hlastL
      exact (tSet_injective T hlastL).symm
  · have hi' : specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i =
        (decomp (A := A) T).E := hi
    obtain ⟨w, hw0, hcross, hlast⟩ := Q.crossing_tate T hC hx hϖ a
      (tpt (A := A) T (TateModel.qZ T.π T.b₄ T.b₆ T.π_mem)) (tSet (A := A) T (decomp (A := A) T).E)
      (tSet (A := A) T (decomp (A := A) T).C) (tSet_mem T hEc) (tSet_mem T hCc)
      ((tSet_injective T).ne hCE.symm) ⟨_, hqE, rfl⟩ ⟨_, hqC, rfl⟩
      (TateNormal.nodeGerm_q T.π_ne_zero T.π_mem hϖ) (Q.D.compSet i.1) (Q.D.compSet_mem i.2)
      (by rw [Q.tateψ_image_compSet T a]; exact congrArg _ hi')
    obtain ⟨L, hL, hpL, hlastL⟩ := Q.exists_incWalk_of_crosses T a w i hw0 hcross
    refine ⟨L, hL, fun p hp => ?_, ?_⟩
    · rw [tpt_injective T (hpL p hp), hCp]
      exact fun h => hpq (Set.mem_singleton_iff.1 h).symm
    · rw [hlast] at hlastL
      exact (tSet_injective T hlastL).symm

end Crossing

end Pres

end

end TemperedFundamentalGroups
