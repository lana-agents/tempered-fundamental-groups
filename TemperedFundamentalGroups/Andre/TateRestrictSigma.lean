/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictModel
import TemperedFundamentalGroups.SemistableReduction.W10Local

/-!
# The involution of the Tate model over `O'` (Blueprint §10.3.8, `v(q) = 1`, B3c)

Let `σ` be an involutive ring automorphism of `O'` with `σ π = -π`, `σ b₄ = b₄`, `σ b₆ = b₆`.
Then `X ↦ -X`, `Y ↦ -Y` with `σ` on coefficients preserves `f = Y² + XY - (π X³ + π b₄ X + b₆)`:

* `σT`: the induced involution of `O'[X][Y]/(f)`, and `σL` of the Tate function field;
* `σL (x/π) = -x/π`, `σL (y/π) = -y/π`, so `σL` maps every chart `O'[g_k/g_j]` of the projective
  model into itself (`locallyDominates_σL`);
* `ρ'`: the induced (`σ`-semilinear) involution of `projModelCode O' (coords)`, lying over
  `Spec σ` (`ρ'_toSpec`), with `genericPt ≫ ρ' = Spec σL ≫ genericPt`.
-/

universe u

open CategoryTheory AlgebraicGeometry Polynomial SemistableReduction.ProjScheme

namespace TemperedFundamentalGroups.TateRestrict

noncomputable section

variable {K' : Type u} [Field K'] {O' : ValuationSubring K'} (π b₄ b₆ : O')
  (σ : O' →+* O') (hσπ : σ π = -π) (hσ4 : σ b₄ = b₄) (hσ6 : σ b₆ = b₆)

local notation "L" => TateNormal.TateField π b₄ b₆
local notation "TR" => TateNormal.TateRing π b₄ b₆

/-- `O'[X] → O'[X][Y]/(f)`, `X ↦ -X` with `σ` on coefficients. -/
def σX : O'[X] →+* TR :=
  (AdjoinRoot.of _).comp (eval₂RingHom (C.comp σ) (-X))

include hσπ hσ4 hσ6 in
lemma eval₂_cpoly_σ : (TateNormal.cpoly π b₄ b₆).eval₂ (C.comp σ) (-X) =
    TateNormal.cpoly π b₄ b₆ := by
  rw [TateNormal.cpoly, eval₂_add, eval₂_add, eval₂_mul, eval₂_mul, eval₂_C, eval₂_C, eval₂_C,
    eval₂_X_pow, eval₂_X, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, map_mul,
    hσπ, hσ4, hσ6]
  simp only [C_neg, C_mul]
  ring

include hσπ hσ4 hσ6 in
lemma σX_cpoly : σX π b₄ b₆ σ (TateNormal.cpoly π b₄ b₆) =
    AdjoinRoot.of _ (TateNormal.cpoly π b₄ b₆) := by
  rw [σX, RingHom.comp_apply, coe_eval₂RingHom, eval₂_cpoly_σ π b₄ b₆ σ hσπ hσ4 hσ6]

include hσπ hσ4 hσ6 in
lemma eval₂_fpoly_σ : (TateNormal.fpoly π b₄ b₆).eval₂ (σX π b₄ b₆ σ) (-TateNormal.bA π b₄ b₆) =
    0 := by
  rw [TateNormal.eval₂_fpoly, σX_cpoly π b₄ b₆ σ hσπ hσ4 hσ6]
  have h0 : (TateNormal.fpoly π b₄ b₆).eval₂ (AdjoinRoot.of _) (TateNormal.bA π b₄ b₆) = 0 :=
    AdjoinRoot.eval₂_root _
  rw [TateNormal.eval₂_fpoly] at h0
  have hX : σX π b₄ b₆ σ X = -AdjoinRoot.of _ X := by simp [σX]
  rw [hX]
  linear_combination h0

/-- **The involution of `O'[X][Y]/(f)`**: `X ↦ -X`, `Y ↦ -Y`, `σ` on coefficients. -/
def σT : TR →+* TR :=
  AdjoinRoot.lift (σX π b₄ b₆ σ) (-TateNormal.bA π b₄ b₆) (eval₂_fpoly_σ π b₄ b₆ σ hσπ hσ4 hσ6)

lemma σT_of (p : O'[X]) : σT π b₄ b₆ σ hσπ hσ4 hσ6 (AdjoinRoot.of _ p) = σX π b₄ b₆ σ p :=
  AdjoinRoot.lift_of _

lemma σT_root : σT π b₄ b₆ σ hσπ hσ4 hσ6 (TateNormal.bA π b₄ b₆) = -TateNormal.bA π b₄ b₆ :=
  AdjoinRoot.lift_root _

lemma σT_algebraMap (o : O') :
    σT π b₄ b₆ σ hσπ hσ4 hσ6 (algebraMap O' TR o) = algebraMap O' TR (σ o) := by
  rw [IsScalarTower.algebraMap_apply O' O'[X] TR, AdjoinRoot.algebraMap_eq, σT_of]
  simp [σX, IsScalarTower.algebraMap_apply O' O'[X] TR, AdjoinRoot.algebraMap_eq]

lemma σT_X : σT π b₄ b₆ σ hσπ hσ4 hσ6 (AdjoinRoot.of _ X) = -AdjoinRoot.of _ X := by
  rw [σT_of]; simp [σX]

variable (hσσ : ∀ o, σ (σ o) = o)

include hσσ in
lemma σT_σT (r : TR) : σT π b₄ b₆ σ hσπ hσ4 hσ6 (σT π b₄ b₆ σ hσπ hσ4 hσ6 r) = r := by
  have : (σT π b₄ b₆ σ hσπ hσ4 hσ6).comp (σT π b₄ b₆ σ hσπ hσ4 hσ6) = RingHom.id TR := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · refine Polynomial.ringHom_ext (fun o ↦ ?_) ?_
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        have e : (AdjoinRoot.of (TateNormal.fpoly π b₄ b₆)) (C o) = algebraMap O' TR o := by
          rw [IsScalarTower.algebraMap_apply O' O'[X] TR, AdjoinRoot.algebraMap_eq]; rfl
        rw [e, σT_algebraMap, σT_algebraMap, hσσ]
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [σT_X, map_neg, σT_X, neg_neg]
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [σT_root, map_neg, σT_root, neg_neg]
  exact RingHom.congr_fun this r

include hσσ in
lemma σT_injective : Function.Injective (σT π b₄ b₆ σ hσπ hσ4 hσ6) :=
  Function.LeftInverse.injective (σT_σT π b₄ b₆ σ hσπ hσ4 hσ6 hσσ)

variable [IsDiscreteValuationRing O'] [Fact (Squarefree (TateNormal.dpoly π b₄ b₆))]

/-- **The involution of the Tate function field.** -/
def σL : L →+* L :=
  IsFractionRing.lift (A := TR) (g := (algebraMap TR L).comp (σT π b₄ b₆ σ hσπ hσ4 hσ6))
    ((IsFractionRing.injective TR L).comp (σT_injective π b₄ b₆ σ hσπ hσ4 hσ6 hσσ))

lemma σL_algebraMap (r : TR) :
    σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ (algebraMap TR L r) =
      algebraMap TR L (σT π b₄ b₆ σ hσπ hσ4 hσ6 r) :=
  IsFractionRing.lift_algebraMap _ _

lemma σL_σL (z : L) : σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ z) = z := by
  have : (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ).comp (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ) = RingHom.id L := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors TR) (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [σL_algebraMap, σL_algebraMap, σT_σT π b₄ b₆ σ hσπ hσ4 hσ6 hσσ]
  exact RingHom.congr_fun this z

lemma σL_algebraMap_O (o : O') :
    σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ (algebraMap O' L o) = algebraMap O' L (σ o) := by
  rw [IsScalarTower.algebraMap_apply O' TR L, σL_algebraMap, σT_algebraMap,
    ← IsScalarTower.algebraMap_apply]

lemma σL_coords (i : Fin (2 + 1)) :
    σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ (TateNormal.coords π b₄ b₆ i) =
      (if i = 2 then 1 else -1) * TateNormal.coords π b₄ b₆ i := by
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, TateNormal.coords, Matrix.cons_val_zero,
      Fin.reduceEq, ↓reduceIte, neg_mul, one_mul]
    change σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ (algebraMap O'[X] L X) = _
    rw [IsScalarTower.algebraMap_apply O'[X] TR L, σL_algebraMap, AdjoinRoot.algebraMap_eq,
      σT_X, map_neg, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  · simp only [Fin.mk_one, Fin.isValue, TateNormal.coords, Matrix.cons_val_one,
      Matrix.cons_val_zero, Fin.reduceEq, ↓reduceIte, neg_mul, one_mul]
    rw [σL_algebraMap, σT_root, map_neg]
  · simp [TateNormal.coords]

/-! ### The involution of the projective model -/

local notation "Rb" => TateNormal.baseRing π b₄ b₆
local notation "g" => TateNormal.coords π b₄ b₆

lemma σL_mem_chart (j : Fin (2 + 1)) {y : L} (hy : y ∈ SemistableReduction.projChart Rb g j) :
    σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ y ∈ SemistableReduction.projChart Rb g j := by
  have hle : (SemistableReduction.projChart Rb g j).map (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ) ≤
      SemistableReduction.projChart Rb g j := by
    rw [SemistableReduction.projChart, RingHom.map_closure, Subring.closure_le, Set.image_union]
    refine Set.union_subset ?_ ?_
    · rintro _ ⟨_, ⟨o, rfl⟩, rfl⟩
      rw [σL_algebraMap_O]
      exact SemistableReduction.base_le_projChart j ⟨σ o, rfl⟩
    · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      rw [map_div₀, σL_coords, σL_coords]
      have hk := SemistableReduction.div_mem_projChart (R := Rb) (f := g) j k
      split_ifs <;> simp only [one_mul, neg_mul, one_mul, div_neg, neg_div, neg_neg] <;>
        first | exact hk | exact neg_mem hk
  exact hle ⟨y, hy, rfl⟩

lemma locallyDominates_σL (j : Fin (2 + 1)) :
    SemistableReduction.ProjScheme.LocallyDominates Rb (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ)
      (SemistableReduction.projChart Rb g j).subtype g := by
  intro 𝔮
  refine ⟨j, 1, 𝔮.isPrime.one_notMem, fun y hy ↦
    ⟨⟨_, σL_mem_chart π b₄ b₆ σ hσπ hσ4 hσ6 hσσ j hy⟩, 0, by simp⟩⟩

variable (hπ0 : π ≠ 0)

/-- **The involution `ρ'` of the projective Tate model over `O'`** (`σ`-semilinear). -/
def ρ' : (projModelCode O' (TateNormal.hcoords π b₄ b₆ hπ0)).scheme ⟶
    (projModelCode O' (TateNormal.hcoords π b₄ b₆ hπ0)).scheme :=
  homOfLocalProj rfl rfl (TateNormal.hcoords π b₄ b₆ hπ0) (TateNormal.hcoords π b₄ b₆ hπ0)
    (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ) (locallyDominates_σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ)

lemma genericPt_ρ' :
    genericPt O' (TateNormal.hcoords π b₄ b₆ hπ0) ≫ ρ' π b₄ b₆ σ hσπ hσ4 hσ6 hσσ hπ0 =
      Spec.map (CommRingCat.ofHom (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ)) ≫
        genericPt O' (TateNormal.hcoords π b₄ b₆ hπ0) :=
  genericPt_comp_homOfLocalProj _ _ _ _ _ _

lemma ρ'_ρ' : ρ' π b₄ b₆ σ hσπ hσ4 hσ6 hσσ hπ0 ≫ ρ' π b₄ b₆ σ hσπ hσ4 hσ6 hσσ hπ0 = 𝟙 _ := by
  refine hom_ext_genericPt (TateNormal.hcoords π b₄ b₆ hπ0) ?_
  rw [reassoc_of% genericPt_ρ', genericPt_ρ', ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    Category.comp_id]
  have : (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ).comp (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ) = RingHom.id L :=
    RingHom.ext (σL_σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ)
  rw [this]
  change Spec.map (𝟙 _) ≫ _ = _
  rw [Spec.map_id, Category.id_comp]

lemma ρ'_toSpec : ρ' π b₄ b₆ σ hσπ hσ4 hσ6 hσσ hπ0 ≫
      (projModelCode O' (TateNormal.hcoords π b₄ b₆ hπ0)).toSpec =
    (projModelCode O' (TateNormal.hcoords π b₄ b₆ hπ0)).toSpec ≫
      Spec.map (CommRingCat.ofHom σ) :=
  homOfLocalProj_toSpec _ _ _ _ _ _ σ (RingHom.ext (σL_algebraMap_O π b₄ b₆ σ hσπ hσ4 hσ6 hσσ))

/-- The involution of the chart `w = 1`. -/
def σChart : TateNormal.chart π b₄ b₆ 2 →+* TateNormal.chart π b₄ b₆ 2 :=
  (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ).restrict _ _ fun _ hy ↦ σL_mem_chart π b₄ b₆ σ hσπ hσ4 hσ6 hσσ 2 hy

lemma chartι_ρ' :
    chartι Rb rfl (TateNormal.hcoords π b₄ b₆ hπ0) 2 ≫ ρ' π b₄ b₆ σ hσπ hσ4 hσ6 hσσ hπ0 =
      Spec.map (CommRingCat.ofHom (σChart π b₄ b₆ σ hσπ hσ4 hσ6 hσσ)) ≫
        chartι Rb rfl (TateNormal.hcoords π b₄ b₆ hπ0) 2 := by
  rw [ρ', chartι_homOfLocalProj, chartLocal]
  refine (eq_homOfLocal _ _ _ _ _ ?_).symm
  have e : (TateNormal.chart π b₄ b₆ 2).subtype.comp (σChart π b₄ b₆ σ hσπ hσ4 hσ6 hσσ) =
      (σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ).comp (TateNormal.chart π b₄ b₆ 2).subtype :=
    RingHom.ext fun _ ↦ rfl
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_comp,
    Spec.map_comp_assoc, ← genericPt_eq_chartι]

/-! ### Compatibility with the point `Spec T ⟶` (model) -/

variable {T : Type u} [CommRing T] (φ : O' →+* T) {x y : T}
  (heq : y ^ 2 + x * y = x ^ 3 + φ (π ^ 2 * b₄) * x + φ (π ^ 2 * b₆)) (hπ : IsUnit (φ π))
  (σB : T →+* T) (hσB : ∀ o, σB (φ o) = φ (σ o)) (hσx : σB x = x) (hσy : σB y = y)

omit [IsDiscreteValuationRing O'] [Fact (Squarefree (TateNormal.dpoly π b₄ b₆))] in
include hσB hσx hσy in
lemma tateHomR_σT : (TateNormal.tateHomR π b₄ b₆ φ heq hπ).comp (σT π b₄ b₆ σ hσπ hσ4 hσ6) =
    σB.comp (TateNormal.tateHomR π b₄ b₆ φ heq hπ) := by
  have hv : σB ↑hπ.unit⁻¹ = -↑hπ.unit⁻¹ := by
    have h1 : σB (φ π) * σB ↑hπ.unit⁻¹ = 1 := by rw [← map_mul, hπ.mul_val_inv, map_one]
    rw [hσB, hσπ, map_neg] at h1
    have h2 : φ π * ↑hπ.unit⁻¹ = 1 := hπ.mul_val_inv
    calc σB ↑hπ.unit⁻¹ = σB ↑hπ.unit⁻¹ * (φ π * ↑hπ.unit⁻¹) := by rw [h2, mul_one]
      _ = -(↑hπ.unit⁻¹ * (-φ π * σB ↑hπ.unit⁻¹)) := by ring
      _ = -↑hπ.unit⁻¹ := by rw [h1, mul_one]
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext (fun o ↦ ?_) ?_
    · simp only [RingHom.comp_apply]
      have e : (AdjoinRoot.of (TateNormal.fpoly π b₄ b₆)) (C o) = algebraMap O' TR o := by
        rw [IsScalarTower.algebraMap_apply O' O'[X] TR, AdjoinRoot.algebraMap_eq]; rfl
      rw [e, σT_algebraMap, TateNormal.tateHomR_C, TateNormal.tateHomR_C, hσB]
    · simp only [RingHom.comp_apply]
      rw [σT_X, map_neg, TateNormal.tateHomR, AdjoinRoot.lift_of]
      simp only [coe_eval₂RingHom, eval₂_X, map_mul, hσx, hv]
      ring
  · simp only [RingHom.comp_apply]
    rw [σT_root, map_neg, TateNormal.tateHomR, AdjoinRoot.lift_root, map_mul, hσy, hv]
    ring

include hσB hσx hσy in
lemma chartHomR_σChart :
    (TateNormal.chartHomR π b₄ b₆ φ heq hπ).comp (σChart π b₄ b₆ σ hσπ hσ4 hσ6 hσσ) =
      σB.comp (TateNormal.chartHomR π b₄ b₆ φ heq hπ) := by
  refine RingHom.ext fun z ↦ ?_
  obtain ⟨r, rfl⟩ := (TateNormal.chartTwoEquiv π b₄ b₆).surjective z
  have h1 : σChart π b₄ b₆ σ hσπ hσ4 hσ6 hσσ (TateNormal.chartTwoEquiv π b₄ b₆ r) =
      TateNormal.chartTwoEquiv π b₄ b₆ (σT π b₄ b₆ σ hσπ hσ4 hσ6 r) := by
    apply Subtype.ext
    change σL π b₄ b₆ σ hσπ hσ4 hσ6 hσσ ((TateNormal.chartTwoEquiv π b₄ b₆ r :
      TateNormal.chart π b₄ b₆ 2) : L) = _
    rw [TateNormal.chartTwoEquiv_apply, TateNormal.chartTwoEquiv_apply, σL_algebraMap]
  have h2 : ∀ s, TateNormal.chartHomR π b₄ b₆ φ heq hπ (TateNormal.chartTwoEquiv π b₄ b₆ s) =
      TateNormal.tateHomR π b₄ b₆ φ heq hπ s := fun s ↦ by
    simp [TateNormal.chartHomR]
  rw [RingHom.comp_apply, RingHom.comp_apply, h1, h2, h2]
  exact RingHom.congr_fun (tateHomR_σT π b₄ b₆ σ hσπ hσ4 hσ6 φ heq hπ σB hσB hσx hσy) r

include hσB hσx hσy in
/-- **The point `Spec T ⟶` (model) is equivariant.** -/
lemma SpecMap_σB_jChart :
    Spec.map (CommRingCat.ofHom σB) ≫ TateNormal.jChart π b₄ b₆ φ heq hπ hπ0 =
      TateNormal.jChart π b₄ b₆ φ heq hπ hπ0 ≫ ρ' π b₄ b₆ σ hσπ hσ4 hσ6 hσσ hπ0 := by
  rw [TateNormal.jChart, Category.assoc, chartι_ρ', ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    chartHomR_σChart π b₄ b₆ σ hσπ hσ4 hσ6 hσσ φ heq hπ σB hσB hσx hσy]

end

end TemperedFundamentalGroups.TateRestrict
