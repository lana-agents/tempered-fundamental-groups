/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateFourGonObject
import TemperedFundamentalGroups.Tempered.CoverImage
import TemperedFundamentalGroups.Andre.TateNatural

/-!
# The `ℤ`-covering of the Tate curve dominates the double cover `E_{q²} → E_q`

Let `T` be Tate data of `E_q` on `R` (`TateObject.Data`, `π = s`, `s² = q`) and `R'` a finite étale
`R`-algebra (in the application the coordinate ring of `E_{q²} ∖ {O, T₂}` over `E_q ∖ {O}`) with
elements `x₁, y₁, x₂, y₂` (the points `P` and `P + T₂` of `E_{q²}`) satisfying the equations of the
`4`-gon model and Vélu's formulas (`FourGon.Input`). This file constructs (TFGD-plan, "Run 4"):

* the level `(R', 1)` with the `4`-gon model `FourGon.model` and `j = [x₁ : y₁ : x₂ : y₂ : π]`;
* the object `Z` with the `ℤ`-covering of the `4`-gon (`FourGon.decomp`);
* `a : Z ⟶ X₀` (the model map `FourGon.ψ` and `(z, n) ↦ (ψ z, 2n + κ z + c)`) and
  `b : Z ⟶ coverObj R'`, a point `z₀` over both base points, and **`a` is injective on fibres**
  when the two `R`-points of `R'` over a geometric point differ by the deck involution
  (`(x₁, y₁) ↔ (x₂, y₂)`), which swaps the halves of the `4`-gon.

Main result: **`FourGon.exists_object`**, the input of `piY_le_range_of_hom` (iut).
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial Pi1.Orbifold
open SemistableReduction.LinearProjectionN

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

namespace FourGon

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

set_option hygiene false in
local notation "R5" => MvPolynomial (Fin (4 + 1)) O

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A] [Subsingleton A]
  [MulSemiringAction A R] [SMulCommClass A K R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  [Algebra.Etale R R'] [Module.Finite R R']

variable (O R') in
/-- **The input data**: the Tate data `π, b₄', b₆'` of `E_{q²}` (same `π`), the constants
`ε = x_T / π`, `γ = C_T / π²`, `κ = c_y / π` and the coordinates `(x₁, y₁)`, `(x₂, y₂)` of the
points `P`, `P + T₂` of `E_{q²}` in `R'`, with the equations of the `4`-gon model, Vélu's formulas
`x = x₁ + x₂ − x_T`, `y = y₁ + y₂ + c_y`, and the valuations of the constants. -/
structure Input (T : TateObject.Data O R) where
  b₄' : O
  b₆' : O
  ε : O
  γ : O
  κ : O
  x₁ : R'
  y₁ : R'
  x₂ : R'
  y₂ : R'
  eq₁ : y₁ ^ 2 + x₁ * y₁ = x₁ ^ 3 + algebraMap K R' ((T.π : K) ^ 2 * b₄') * x₁ +
    algebraMap K R' ((T.π : K) ^ 2 * b₆')
  eq₂ : y₂ ^ 2 + x₂ * y₂ = x₂ ^ 3 + algebraMap K R' ((T.π : K) ^ 2 * b₄') * x₂ +
    algebraMap K R' ((T.π : K) ^ 2 * b₆')
  q₃ : (x₁ - algebraMap K R' ((T.π : K) * ε)) * (x₂ - algebraMap K R' ((T.π : K) * ε)) =
    algebraMap K R' ((T.π : K) ^ 2 * γ)
  q₄ : (2 * y₂ + x₂) * (x₁ - algebraMap K R' ((T.π : K) * ε)) +
    (2 * y₁ + x₁) * (x₂ - algebraMap K R' ((T.π : K) * ε)) = 0
  q₅ : (2 * y₁ + x₁) * (2 * y₂ + x₂) + algebraMap K R' ((T.π : K) ^ 2 * γ) *
    (4 * (x₁ + x₂) + algebraMap K R' (4 * (T.π : K) * ε + 1)) = 0
  vx : algebraMap R R' T.x = x₁ + x₂ - algebraMap K R' ((T.π : K) * ε)
  vy : algebraMap R R' T.y = y₁ + y₂ + algebraMap K R' ((T.π : K) * κ)
  b₆'_mem : b₆' ∈ IsLocalRing.maximalIdeal O
  ε_mem : ε ∈ IsLocalRing.maximalIdeal O
  γ_unit : IsUnit γ
  two_unit : IsUnit (2 : O)

variable {T : TateObject.Data O R} (I : Input O R' T)

/-! ### The coordinates -/

/-- The structure of `O`-algebra on `R'`. -/
abbrev algR' : Algebra O R' := ((algebraMap K R').comp O.subtype).toAlgebra

attribute [local instance] algR'

lemma algebraMap_O_R' (o : O) : algebraMap O R' o = algebraMap K R' (o : K) := rfl

/-- The coordinates `(x₁, y₁, x₂, y₂, π)` in `R'`. -/
def gR : Fin (4 + 1) → R' := ![I.x₁, I.y₁, I.x₂, I.y₂, algebraMap K R' (T.π : K)]

lemma isUnit_π_R' : IsUnit (algebraMap K R' (T.π : K)) :=
  ((isUnit_iff_ne_zero.2 fun h => T.π_ne_zero (Subtype.ext h)).map (algebraMap K R'))

@[simp] lemma gR_0 : gR I 0 = I.x₁ := rfl
@[simp] lemma gR_1 : gR I 1 = I.y₁ := rfl
@[simp] lemma gR_2 : gR I 2 = I.x₂ := rfl
@[simp] lemma gR_3 : gR I 3 = I.y₂ := rfl
@[simp] lemma gR_4 : gR I 4 = algebraMap K R' (T.π : K) := rfl

lemma ℓψ_0 (ε κ : O) : ℓψ ε κ 0 = X 0 + X 2 - C ε * X 4 := rfl
lemma ℓψ_1 (ε κ : O) : ℓψ ε κ 1 = X 1 + X 3 + C κ * X 4 := rfl
lemma ℓψ_2 (ε κ : O) : ℓψ ε κ 2 = X 4 := rfl

lemma aeval_cub₁ : aeval (gR I) (cub T.π I.b₄' I.b₆' 0 1) = 0 := by
  have h := I.eq₁
  simp only [cub, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_O_R', gR_0,
    gR_1, gR_4]
  push_cast at h ⊢
  try simp only [map_mul, map_pow] at h ⊢
  linear_combination algebraMap K R' (T.π : K) * h

lemma aeval_cub₂ : aeval (gR I) (cub T.π I.b₄' I.b₆' 2 3) = 0 := by
  have h := I.eq₂
  simp only [cub, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_O_R', gR_2,
    gR_3, gR_4]
  push_cast at h ⊢
  try simp only [map_mul, map_pow] at h ⊢
  linear_combination algebraMap K R' (T.π : K) * h

lemma aeval_Q₃ : aeval (gR I) (Q₃ I.ε I.γ) = 0 := by
  have h := I.q₃
  simp only [Q₃, map_sub, map_mul, map_pow, aeval_X, aeval_C, algebraMap_O_R', gR_0, gR_2, gR_4]
  push_cast at h ⊢
  try simp only [map_mul, map_pow] at h ⊢
  linear_combination h

lemma aeval_Q₄ : aeval (gR I) (Q₄ I.ε) = 0 := by
  have h := I.q₄
  simp only [Q₄, map_sub, map_add, map_mul, map_ofNat, aeval_X, aeval_C, algebraMap_O_R', gR_0,
    gR_1, gR_2, gR_3, gR_4]
  push_cast at h ⊢
  try simp only [map_mul, map_pow] at h ⊢
  linear_combination h

lemma aeval_Q₅ : aeval (gR I) (Q₅ T.π I.ε I.γ) = 0 := by
  have h := I.q₅
  simp only [Q₅, map_add, map_mul, map_pow, map_ofNat, aeval_X, aeval_C,
    algebraMap_O_R', gR_0, gR_1, gR_2, gR_3, gR_4]
  push_cast at h ⊢
  try simp only [map_ofNat] at h ⊢
  linear_combination h

lemma aeval_ℓψ : (fun j => aeval (gR I) (ℓψ I.ε I.κ j)) =
    ![algebraMap R R' T.x, algebraMap R R' T.y, algebraMap K R' (T.π : K)] := by
  funext j
  fin_cases j
  · change aeval (gR I) (X 0 + X 2 - C I.ε * X 4 : R5) = algebraMap R R' T.x
    rw [I.vx]
    simp only [map_sub, map_add, map_mul, aeval_X, aeval_C, algebraMap_O_R', gR_0, gR_2, gR_4]
    ring
  · change aeval (gR I) (X 1 + X 3 + C I.κ * X 4 : R5) = algebraMap R R' T.y
    rw [I.vy]
    simp only [map_add, map_mul, aeval_X, aeval_C, algebraMap_O_R', gR_1, gR_3, gR_4]
    ring
  · change aeval (gR I) (X 4 : R5) = algebraMap K R' (T.π : K)
    rw [aeval_X, gR_4]

lemma aeval_Fℓ : aeval (gR I) (Fℓ T.π T.b₄ T.b₆ I.ε I.κ) = 0 := by
  rw [Fℓ, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, aeval_ℓψ I]
  have h := congrArg (algebraMap R R') T.equation
  simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at h
  simp only [TateModel.F, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_O_R',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  try simp only [map_mul, map_pow] at h ⊢
  linear_combination algebraMap K R' (T.π : K) * h

/-! ### Homogeneity of the equations -/

lemma isHomogeneous_cub (π b₄ b₆ : O) (a b : Fin (4 + 1)) :
    (cub π b₄ b₆ a b).IsHomogeneous 3 := by
  unfold cub
  refine ((((((isHomogeneous_X_pow _ _).mul (isHomogeneous_X _ _)).add
    (((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X _ _))).sub
    (isHomogeneous_C_mul_X_pow _ _ _)).sub ?_).sub (isHomogeneous_C_mul_X_pow _ _ _))
  exact ((isHomogeneous_C _ _).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X_pow _ _)

lemma isHomogeneous_lin (a b : Fin (4 + 1)) (e : O) : (X a - C e * X b : R5).IsHomogeneous 1 :=
  (isHomogeneous_X _ _).sub ((isHomogeneous_C _ _).mul (isHomogeneous_X _ _))

lemma isHomogeneous_two_add (a b : Fin (4 + 1)) : (2 * X a + X b : R5).IsHomogeneous 1 := by
  rw [show (2 : R5) = C 2 from (map_ofNat C 2).symm]
  exact ((isHomogeneous_C _ _).mul (isHomogeneous_X _ _)).add (isHomogeneous_X _ _)

lemma isHomogeneous_Q₃ (ε γ : O) : (Q₃ ε γ : R5).IsHomogeneous 2 :=
  ((isHomogeneous_lin 0 4 ε).mul (isHomogeneous_lin 2 4 ε)).sub (isHomogeneous_C_mul_X_pow _ _ _)

lemma isHomogeneous_Q₄ (ε : O) : (Q₄ ε : R5).IsHomogeneous 2 :=
  ((isHomogeneous_two_add 3 2).mul (isHomogeneous_lin 0 4 ε)).add
    ((isHomogeneous_two_add 1 0).mul (isHomogeneous_lin 2 4 ε))

lemma isHomogeneous_Q₅ (π ε γ : O) : (Q₅ π ε γ : R5).IsHomogeneous 2 :=
  ((isHomogeneous_two_add 1 0).mul (isHomogeneous_two_add 3 2)).add
    ((isHomogeneous_C _ _).mul ((((isHomogeneous_C _ _).mul (isHomogeneous_X _ _)).mul
      ((isHomogeneous_X _ _).add (isHomogeneous_X _ _))).add (isHomogeneous_C_mul_X_pow _ _ _)))

lemma Fℓ_mem (π b₄ b₆ ε κ : O) :
    Fℓ π b₄ b₆ ε κ ∈ MvPolynomial.homogeneousSubmodule (Fin (4 + 1)) O 3 :=
  (linHom (ℓψ ε κ) (ℓψ_mem ε κ)).map_mem
    ((mem_homogeneousSubmodule _ _).2 (TateModel.isHomogeneous_F π b₄ b₆))

/-! ### The level `(R', 1)` with the `4`-gon model -/

variable (R A R') in
/-- The coded ring of the cover. -/
abbrev Bc : Type u := (coverEt R A R').level.B

/-- The structure of `O`-algebra on the coded ring. -/
abbrev algB : Algebra O (Bc R A R') := (levelStructureMap O R A (coverEt R A R').level).toAlgebra

attribute [local instance] algB

variable (O R A) in
/-- `R' ≅ B` as `O`-algebras. -/
def eB : R' →ₐ[O] Bc R A R' :=
  { (coverE R A R').symm.toRingEquiv.toRingHom with
    commutes' := fun o => by
      change (coverE R A R').symm (algebraMap K R' (o : K)) =
        algebraMap R _ (algebraMap K R (o : K))
      rw [IsScalarTower.algebraMap_apply K R R', AlgEquiv.commutes] }

lemma eB_apply (r : R') : eB O R A r = (coverE R A R').symm r := rfl

variable (A) in
/-- The coordinates in the coded ring. -/
def gB : Fin (4 + 1) → Bc R A R' := fun i => eB O R A (gR I i)

lemma aeval_gB (r : R5) : aeval (gB A I) r = eB O R A (aeval (gR I) r) := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

lemma isUnit_gB4 : IsUnit (aeval (gB A I) (X 4 : R5)) := by
  rw [aeval_X]
  exact (isUnit_π_R' (T := T) (R' := R')).map (eB O R A)

variable (A) in
/-- **The point `[x₁ : y₁ : x₂ : y₂ : π] : Spec B ⟶ ℙ⁴_O`.** -/
def j0 : Spec (CommRingCat.of (Bc R A R')) ⟶ projSpace O 4 :=
  ptT (gB A I) (X 4) (isUnit_gB4 I) (X_mem' 4) one_pos

lemma j0_toSpec : j0 A I ≫ projSpace.toSpec O 4 =
    Spec.map (CommRingCat.ofHom (levelStructureMap O R A (coverEt R A R').level)) :=
  ptT_toSpec _ _ _ _ _

lemma relsF_j0 (x : Spec (CommRingCat.of (Bc R A R'))) :
    RelsF T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ (j0 A I x).asHomogeneousIdeal.toIdeal := by
  have key : ∀ (r : R5) (e : ℕ), r.IsHomogeneous e → 0 < e → aeval (gR I) r = 0 →
      r ∈ (j0 A I x).asHomogeneousIdeal := fun r e hr he h0 => by
    refine (mem_ptT_iff (gB A I) (isUnit_gB4 I) (X_mem' 4) one_pos x
      ((mem_homogeneousSubmodule _ _).2 hr) he).2 ?_
    rw [aeval_gB, h0, map_zero]
    exact zero_mem _
  exact ⟨⟨key _ 3 (isHomogeneous_cub _ _ _ _ _) three_pos (aeval_cub₁ I),
    key _ 3 (isHomogeneous_cub _ _ _ _ _) three_pos (aeval_cub₂ I),
    key _ 2 (isHomogeneous_Q₃ _ _) two_pos (aeval_Q₃ I),
    key _ 2 (isHomogeneous_Q₄ _) two_pos (aeval_Q₄ I),
    key _ 2 (isHomogeneous_Q₅ _ _ _) two_pos (aeval_Q₅ I)⟩,
    key _ 3 ((mem_homogeneousSubmodule _ _).1 (Fℓ_mem _ _ _ _ _)) three_pos (aeval_Fℓ I)⟩

variable [IsReduced R']

instance : IsReduced (Bc R A R') :=
  isReduced_of_injective (coverE R A R').toRingEquiv.toRingHom (coverE R A R').injective

instance : QuasiCompact (j0 A I) := by
  have : QuasiCompact (j0 A I ≫ projSpace.toSpec O 4) := by
    rw [j0_toSpec]
    infer_instance
  exact .of_comp _ (projSpace.toSpec O 4)

lemma modelIdeal_le_ker_j0 :
    modelIdeal T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ ≤ (j0 A I).ker := by
  refine le_trans ?_ (TateModel.radical_ker_le _)
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
  change (↑((j0 A I).ker.support) : Set (projSpace O 4)) ⊆ _
  rw [Scheme.Hom.support_ker]
  refine (relSet T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ).isClosed.closure_subset_iff.2 ?_
  rintro _ ⟨x, rfl⟩
  exact relsF_j0 I x

variable (A) in
/-- **The map `j : Spec B ⟶ model`.** -/
def jm : Spec (CommRingCat.of (Bc R A R')) ⟶
    (modelIdeal T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ).subscheme :=
  (j0 A I).toImage ≫ Scheme.IdealSheafData.inclusion (modelIdeal_le_ker_j0 I)

lemma jm_ιm : jm A I ≫ ιm T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ = j0 A I := by
  rw [jm, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]

lemma coverH_eq_one (g : (coverEt R A R').level.H) : g = 1 := by
  have h := (coverEt R A R').eq_act_of_mem g.2
  exact Subtype.ext (h.trans (MonoidHom.one_apply _))

variable (A) in
/-- **The level `(R', 1)` with the `4`-gon model.** -/
def level : Level O R A where
  L := (coverEt R A R').level
  c := model T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ
  j := jm A I
  j_toSpec := by
    change jm A I ≫ ιm _ _ _ _ _ _ _ _ ≫ projSpace.toSpec O 4 = _
    rw [← Category.assoc, jm_ιm, j0_toSpec]
  ρ := 1
  ρ_toSpec _ := Category.id_comp _
  ρ_j g := by
    rw [coverH_eq_one g, MonoidHom.one_apply]
    change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    convert Category.id_comp _
    rw [← Spec.map_id]
    rfl

lemma level_ρs (g : (level A I).L.H) : (level A I).ρs g = 1 := by
  rw [coverH_eq_one g]
  exact map_one _

/-! ### The special fibre: the `4`-gon over the `2`-gon -/

/-- The special fibre in `ℙ⁴`. -/
def ιZ (z : (level A I).Z) : projSpace O 4 := ιm T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ z.1

/-- The prime of `O[X₀, …, X₄]` of a point of the special fibre. -/
abbrev Pz (z : (level A I).Z) : Ideal R5 := pt (RingHom.id R5) (ιZ I) z

lemma mem_Pz {z : (level A I).Z} {r : R5} : r ∈ Pz I z ↔ r ∈ (ιZ I z).asHomogeneousIdeal :=
  Iff.rfl

lemma continuous_ιZ : Continuous (ιZ (A := A) I) :=
  (ιm _ _ _ _ _ _ _ _).continuous.comp continuous_subtype_val

lemma special_ιZ (z : (level A I).Z) (c : O) (hc : c ∈ IsLocalRing.maximalIdeal O) :
    C c ∈ (ιZ I z).asHomogeneousIdeal :=
  (mem_specialFibre_projSpace_iff (ιZ I z)).1 z.2 c hc

/-- The hypotheses of `FourGon.decomp`. -/
lemma hyp : Hyp (π := T.π) (b₄ := I.b₄') (b₆ := I.b₆') (ε := I.ε) (γ := I.γ) (ιZ (A := A) I)
    (RingHom.id R5) where
  continuous := continuous_ιZ I
  rels z := (relsF_ιm T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ z.1).1
  special z c hc := special_ιZ I z c hc
  nonvanish _ := exists_X_notMem _
  π_mem := T.π_mem
  b₆_mem := I.b₆'_mem
  ε_mem := I.ε_mem
  two := I.two_unit
  γ_unit := I.γ_unit

variable (A) in
/-- **The decomposition of the special fibre into the halves of the `4`-gon.** -/
def D' : TateCovering.Decomp (level A I).Z :=
  decomp T.π I.b₄' I.b₆' I.ε I.γ (ιZ (A := A) I) (RingHom.id R5) (hyp I)

lemma relsZ (z : (level A I).Z) : Rels T.π I.b₄' I.b₆' I.ε I.γ (Pz I z) := (hyp I).rels z
lemma hεZ (z : (level A I).Z) : C I.ε ∈ Pz I z := special_ιZ I z _ I.ε_mem
lemma hπZ (z : (level A I).Z) : C T.π ∈ Pz I z := special_ιZ I z _ T.π_mem
lemma hbZ (z : (level A I).Z) : C I.b₆' ∈ Pz I z := special_ιZ I z _ I.b₆'_mem
lemma hXZ (z : (level A I).Z) : ∃ i, (X i : R5) ∉ Pz I z := exists_X_notMem _

variable (A) in
/-- The model map on special fibres. -/
def ψs : (level A I).Z → (TateObject.level (A := A) T).Z :=
  specialFibreMap (ψ T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ I.two_unit)
    (ψ_toSpec T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ I.two_unit)

lemma continuous_ψs : Continuous (ψs A I) := continuous_specialFibreMap _ _

lemma mem_ψs_iff (z : (level A I).Z) {g : MvPolynomial (Fin (2 + 1)) O} {d : ℕ}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) O d) (hd : 0 < d) :
    g ∈ (TateModel.ιZ T.π T.b₄ T.b₆ (ψs A I z)).asHomogeneousIdeal ↔
      aeval (ℓψ I.ε I.κ) g ∈ Pz I z :=
  mem_ψ_iff T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ I.two_unit hg hd z.1

lemma X_mem_ψs_iff (z : (level A I).Z) (k : Fin (2 + 1)) :
    (X k : MvPolynomial (Fin (2 + 1)) O) ∈
      (TateModel.ιZ T.π T.b₄ T.b₆ (ψs A I z)).asHomogeneousIdeal ↔
      ℓψ I.ε I.κ k ∈ Pz I z := by
  rw [mem_ψs_iff I z ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X O k)) one_pos, aeval_X]

/-- `ψ z ∈ C ↔ X₄ = 0`. -/
lemma ψs_mem_C (z : (level A I).Z) :
    ψs A I z ∈ (TateObject.decomp (A := A) T).C ↔ (X 4 : R5) ∈ Pz I z :=
  X_mem_ψs_iff I z 2

lemma ℓ1_iff {P : Ideal R5} (h4 : (X 4 : R5) ∈ P) :
    ℓψ I.ε I.κ 1 ∈ P ↔ X 1 + X 3 ∈ P := by
  have e : ℓψ I.ε I.κ 1 = X 1 + X 3 + C I.κ * X 4 := rfl
  rw [e]
  exact ⟨fun h => sub_mem' h (P.mul_mem_left _ h4), fun h => P.add_mem h (P.mul_mem_left _ h4)⟩

/-- `ψ z = p ↔ z ∈ ψ⁻¹(p)`. -/
lemma ψs_mem_Cp (z : (level A I).Z) :
    ψs A I z ∈ (TateObject.decomp (A := A) T).Cp ↔ Np (Pz I z) := by
  change (X 2 : MvPolynomial (Fin (2 + 1)) O) ∈ _ ∧ (X 1 : MvPolynomial (Fin (2 + 1)) O) ∈ _ ↔ _
  rw [X_mem_ψs_iff, X_mem_ψs_iff]
  exact ⟨fun ⟨h4, h1⟩ => ⟨h4, (ℓ1_iff I h4).1 h1⟩, fun ⟨h4, h1⟩ => ⟨h4, (ℓ1_iff I h4).2 h1⟩⟩

/-- **`ψ⁻¹(q) = Cp ∪ Cq`.** -/
lemma ψs_mem_Cq (z : (level A I).Z) :
    ψs A I z ∈ (TateObject.decomp (A := A) T).Cq ↔ MemCp (Pz I z) ∨ MemCq (Pz I z) := by
  change (X 2 : MvPolynomial (Fin (2 + 1)) O) ∈ _ ∧ (X 0 + X 1 : MvPolynomial (Fin (2 + 1)) O) ∈ _
    ↔ _
  rw [X_mem_ψs_iff, mem_ψs_iff I z ((mem_homogeneousSubmodule _ _).2
    ((isHomogeneous_X O 0).add (isHomogeneous_X O 1))) one_pos]
  rw [← x4_x0123_iff (relsZ I z) (hπZ I z) (hbZ I z) (hεZ I z) I.two_unit I.γ_unit]
  have e : aeval (ℓψ I.ε I.κ) (X 0 + X 1 : MvPolynomial (Fin (2 + 1)) O) =
      X 0 + X 1 + (X 2 + X 3) + C (I.κ - I.ε) * X 4 := by
    simp only [map_add, aeval_X, ℓψ, map_sub, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [e]
  refine and_congr_right fun h4 => ?_
  exact ⟨fun h => sub_mem' h ((Pz I z).mul_mem_left _ h4),
    fun h => (Pz I z).add_mem h ((Pz I z).mul_mem_left _ h4)⟩

lemma shift_ψs (z : (level A I).Z) :
    (TateObject.decomp (A := A) T).shift (ψs A I z) = shiftC (Pz I z) := by
  unfold shiftC
  split_ifs with h
  · exact TateCovering.Decomp.shift_of_mem _ ((ψs_mem_C I z).2 h)
  · exact TateCovering.Decomp.shift_of_notMem _ fun h' => h ((ψs_mem_C I z).1 h')

lemma shift_D' (z : (level A I).Z) : (D' A I).shift z = shiftA (Pz I z) := rfl

lemma isClosed_pt (r : R5) : IsClosed {z : (level A I).Z | r ∈ Pz I z} :=
  isClosed_setOf_pt (continuous_ιZ I) r

lemma isClosed_Lc : IsClosed {z : (level A I).Z | Lc (Pz I z)} :=
  (isClosed_pt I _).inter ((isClosed_pt I _).inter (isClosed_pt I _))
lemma isClosed_Gp : IsClosed {z : (level A I).Z | Gp (Pz I z)} :=
  (isClosed_pt I _).inter (isClosed_pt I _)
lemma isClosed_Lb : IsClosed {z : (level A I).Z | Lb (Pz I z)} :=
  (isClosed_pt I _).inter ((isClosed_pt I _).inter (isClosed_pt I _))
lemma isClosed_Gm : IsClosed {z : (level A I).Z | Gm (Pz I z)} :=
  (isClosed_pt I _).inter (isClosed_pt I _)

variable (A) in
/-- The four lines as a family of closed sets. -/
def lines : Fin 4 → Set (level A I).Z :=
  ![{z | Lc (Pz I z)}, {z | Gp (Pz I z)}, {z | Lb (Pz I z)}, {z | Gm (Pz I z)}]

lemma isClosed_lines (i : Fin 4) : IsClosed (lines A I i) := by
  fin_cases i
  exacts [isClosed_Lc I, isClosed_Gp I, isClosed_Lb I, isClosed_Gm I]

lemma lines_cover (z : (level A I).Z) : ∃ i, z ∈ lines A I i := by
  rcases mem_pieces (relsZ I z) (hπZ I z) (hbZ I z) (hεZ I z) I.two_unit I.γ_unit with
    h | h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]

/-- The parity function on the special fibre. -/
def κZ (z : (level A I).Z) : ℤ := κf (Pz I z)

lemma isOpen_compl_pt {S : Set (level A I).Z} (h : IsClosed S) : IsOpen Sᶜ := h.isOpen_compl

lemma h2Z (v : ℤ) : IsOpen {z | ψs A I z ∉ (TateObject.decomp (A := A) T).Cq ∧ κZ I z = v} := by
  refine isOpen_level_of_pieces (U := {z | ψs A I z ∉ (TateObject.decomp (A := A) T).Cq})
    ((TateObject.decomp (A := A) T).isClosed_Cq.preimage (continuous_ψs I)).isOpen_compl
    ![(D' A I).C, (D' A I).E] (fun i => by fin_cases i; exacts [(D' A I).isClosed_C,
      (D' A I).isClosed_E]) (fun z _ => ?_) (κZ I) ![1, 0] (fun i z hz hzi => ?_) v
  · rcases (Set.ext_iff.1 (D' A I).union z).2 trivial with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  · have hz' : ¬ (MemCp (Pz I z) ∨ MemCq (Pz I z)) := fun h => hz ((ψs_mem_Cq I z).2 h)
    push Not at hz'
    have key := κf_of_not (relsZ I z) (hπZ I z) (hbZ I z) (hεZ I z) I.two_unit I.γ_unit
      (hXZ I z) hz'.1 hz'.2
    have hAB : ¬ (MemA (Pz I z) ∧ MemB (Pz I z)) := fun ⟨hA, hB⟩ =>
      (memA_memB (relsZ I z) (hεZ I z) I.γ_unit (hXZ I z) hA hB).elim hz'.1 hz'.2
    fin_cases i
    · exact key.1.2 fun hB => hAB ⟨hzi, hB⟩
    · exact key.2.2 fun hA => hAB ⟨hA, hzi⟩

lemma h3Z (v : ℤ) : IsOpen {z | z ∉ (D' A I).Cq ∧ ψs A I z ∉ (TateObject.decomp (A := A) T).Cp ∧
    κZ I z - (TateObject.decomp (A := A) T).shift (ψs A I z) = v} := by
  have := isOpen_level_of_pieces
    (U := {z | z ∉ (D' A I).Cq ∧ ψs A I z ∉ (TateObject.decomp (A := A) T).Cp})
    ((D' A I).isClosed_Cq.isOpen_compl.inter
      ((TateObject.decomp (A := A) T).isClosed_Cp.preimage (continuous_ψs I)).isOpen_compl)
    (lines A I) (isClosed_lines I) (fun z _ => lines_cover I z)
    (fun z => κZ I z - (TateObject.decomp (A := A) T).shift (ψs A I z)) ![1, 0, 0, -1]
    (fun i z hz hzi => by
      have hq : ¬ MemCq (Pz I z) := hz.1
      have hn : ¬ Np (Pz I z) := fun h => hz.2 ((ψs_mem_Cp I z).2 h)
      have key := κ_sub_shiftC (relsZ I z) (hεZ I z) I.γ_unit (hXZ I z) hq hn
      rw [shift_ψs]
      fin_cases i
      exacts [key.1 hzi, key.2.1 hzi, key.2.2.1 hzi, key.2.2.2 hzi]) v
  convert this using 1
  ext z
  simp only [Set.mem_setOf_eq, and_assoc]

lemma h4Z (v : ℤ) : IsOpen {z | z ∉ (D' A I).Cp ∧ ψs A I z ∉ (TateObject.decomp (A := A) T).Cp ∧
    2 * (D' A I).shift z + κZ I z - (TateObject.decomp (A := A) T).shift (ψs A I z) = v} := by
  have := isOpen_level_of_pieces
    (U := {z | z ∉ (D' A I).Cp ∧ ψs A I z ∉ (TateObject.decomp (A := A) T).Cp})
    ((D' A I).isClosed_Cp.isOpen_compl.inter
      ((TateObject.decomp (A := A) T).isClosed_Cp.preimage (continuous_ψs I)).isOpen_compl)
    (lines A I) (isClosed_lines I) (fun z _ => lines_cover I z)
    (fun z => 2 * (D' A I).shift z + κZ I z - (TateObject.decomp (A := A) T).shift (ψs A I z))
    ![1, 0, 2, 1]
    (fun i z hz hzi => by
      have hp : ¬ MemCp (Pz I z) := hz.1
      have hn : ¬ Np (Pz I z) := fun h => hz.2 ((ψs_mem_Cp I z).2 h)
      have key := two_shiftA_add_κ_sub_shiftC (relsZ I z) (hεZ I z) I.γ_unit (hXZ I z) hp hn
      rw [shift_ψs, shift_D']
      fin_cases i
      exacts [key.1 hzi, key.2.1 hzi, key.2.2.1 hzi, key.2.2.2 hzi]) v
  convert this using 1
  ext z
  simp only [Set.mem_setOf_eq, and_assoc]

/-- **The map of `ℤ`-coverings** `(z, n) ↦ (ψ z, 2n + κ z + c)`. -/
lemma continuous_mapTwo_Z (c : ℤ) :
    Continuous (TateCovering.Decomp.mapTwo (D' A I) (TateObject.decomp (A := A) T) (ψs A I)
      (κZ I) c) :=
  TateCovering.Decomp.continuous_mapTwo (continuous_ψs I) _ c
    (fun z hz hq => hz ((ψs_mem_Cq I z).2 (Or.inr hq))) (h2Z I) (h3Z I) (h4Z I)

/-! ### `Spec`-points through charts -/

lemma awayLift_congr {S S' : Type*} [CommRing S] [CommRing S'] {f g : S →+* S'} (h : f = g)
    (r : S) (hf : IsUnit (f r)) (hg : IsUnit (g r)) :
    Localization.awayLift f r hf = Localization.awayLift g r hg := by
  subst h
  rfl

lemma ptT_congr_c {Tr : Type u} [CommRing Tr] [Algebra O Tr] {m : ℕ}
    {c c' : Fin (m + 1) → Tr} (h : c = c') (s : MvPolynomial (Fin (m + 1)) O)
    (hs : IsUnit (aeval c s)) (hs' : IsUnit (aeval c' s)) {d : ℕ}
    (hsd : s ∈ MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O d) (hd : 0 < d) :
    ptT c s hs hsd hd = ptT c' s hs' hsd hd := by
  subst h
  rfl

/-- **The Tate point `[x : y : π]` is `ptT`** through the chart `w ≠ 0`. -/
lemma toProj_eq_ptT {Tr : Type u} [CommRing Tr] [Algebra O Tr] (π : O) (x y : Tr)
    (hπ : IsUnit (algebraMap O Tr π))
    (hu : IsUnit (aeval ![x, y, algebraMap O Tr π] (X 2 : MvPolynomial (Fin (2 + 1)) O))) :
    TateModel.toProj π (algebraMap O Tr) x y hπ =
      ptT ![x, y, algebraMap O Tr π] (X 2) hu (X_mem' 2) one_pos := by
  have hev : (Scheme.ΓSpecIso (CommRingCat.of Tr)).hom.hom.comp
      (TateModel.evalΓ π (algebraMap O Tr) x y) =
      (aeval ![x, y, algebraMap O Tr π]).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun o => ?_) (fun i => ?_)
    · simp [TateModel.evalΓ, TateModel.evalPt]
    · simp [TateModel.evalΓ, TateModel.evalPt]
  have hu1 : IsUnit (TateModel.evalΓ π (algebraMap O Tr) x y (X 2)) := by
    simp only [TateModel.evalΓ, TateModel.evalPt, RingHom.comp_apply, eval₂Hom_X']
    exact hπ.map _
  have hu1' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of Tr)).hom.hom
      (TateModel.evalΓ π (algebraMap O Tr) x y (X 2))) := hu1.map _
  rw [TateModel.toProj, Proj.fromOfGlobalSections_Spec_eq _ _ _ one_pos (X_mem' 2) hu1 hu1', ptT,
    awayEvalT, awayLift_congr hev]

/-! ### The swap of the two halves -/

/-- The permutation `(0 2)(1 3)` of the coordinates (translation by `T₂`). -/
def e5 : Fin (4 + 1) → Fin (4 + 1) := ![2, 3, 0, 1, 4]

lemma e5_e5 (i : Fin (4 + 1)) : e5 (e5 i) = i := by
  fin_cases i <;> rfl

/-- The linear forms of the swap. -/
def ℓsw : Fin (4 + 1) → R5 := fun i => X (e5 i)

lemma ℓsw_mem (i : Fin (4 + 1)) : ℓsw i ∈ MvPolynomial.homogeneousSubmodule (Fin (4 + 1)) O 1 :=
  X_mem' _

lemma hcov_sw (y : projSpace O 4) :
    ∃ k, (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (4 + 1)) O))) y ∈
    D (ℓsw (O := O)) ℓsw_mem k := by
  obtain ⟨i, hi⟩ := exists_X_notMem y
  refine ⟨e5 i, ?_⟩
  change linHom ℓsw ℓsw_mem (X (e5 i)) ∉ y.asHomogeneousIdeal
  rwa [linHom_apply, aeval_X, ℓsw, e5_e5]

variable (O) in
/-- **The swap `ρ̃ : ℙ⁴ ⟶ ℙ⁴`.** -/
def ρsw : projSpace O 4 ⟶ projSpace O 4 :=
  proj (ℓsw (O := O)) ℓsw_mem (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (4 + 1)) O))) hcov_sw

lemma ρsw_toSpec : ρsw O ≫ projSpace.toSpec O 4 = projSpace.toSpec O 4 :=
  (proj_toSpec _ _ _ _).trans (Category.id_comp _)

lemma mem_ρsw_iff (y : projSpace O 4) {r : R5} {d : ℕ}
    (hr : r ∈ MvPolynomial.homogeneousSubmodule (Fin (4 + 1)) O d) (hd : 0 < d) :
    r ∈ (ρsw O y).asHomogeneousIdeal ↔ rename e5 r ∈ y.asHomogeneousIdeal := by
  have h := mem_proj_iff (ℓ := ℓsw (O := O)) hcov_sw hr hd y
  have e : aeval (ℓsw (O := O)) r = rename e5 r := by
    rw [rename_eq_aeval]
    rfl
  rw [e] at h
  exact h

lemma ptT_ρsw {Tr : Type u} [CommRing Tr] [Algebra O Tr] (c : Fin (4 + 1) → Tr)
    (hc : IsUnit (aeval c (X 4 : R5))) (hc' : IsUnit (aeval (c ∘ e5) (X 4 : R5))) :
    ptT c (X 4) hc (X_mem' 4) one_pos ≫ ρsw O = ptT (c ∘ e5) (X 4) hc' (X_mem' 4) one_pos := by
  have hk : IsUnit (aeval c (linHom (ℓsw (O := O)) ℓsw_mem (X (4 : Fin (4 + 1))))) := by
    rwa [linHom_apply, aeval_X]
  have hk' : IsUnit (aeval (fun j => aeval c (ℓsw (O := O) j)) (X (4 : Fin (4 + 1)) : R5)) := by
    simpa [ℓsw, e5] using hc
  have h := comp_proj_of_eq_ptT (ℓsw (O := O)) ℓsw_mem hcov_sw
    (ptT c (X 4) hc (X_mem' 4) one_pos) c 4
    hk (𝟙 _) ((Category.comp_id _).trans ((ptT_eq c hc hk _ _ one_pos).trans
      (Category.id_comp _).symm)) hk'
  refine h.trans ((Category.id_comp _).trans ?_)
  exact ptT_congr_c (funext fun j => by simp [ℓsw]) _ _ _ _ _

/-- The swap exchanges the halves: on primes related by `rename e5`. -/
lemma κf_swap {P P' : Ideal R5} [P.IsPrime]
    (hlin : ∀ r : R5, r.IsHomogeneous 1 → (r ∈ P' ↔ rename e5 r ∈ P))
    (hR : Rels T.π I.b₄' I.b₆' I.ε I.γ P) (hπ : C T.π ∈ P) (hb : C I.b₆' ∈ P) (hε : C I.ε ∈ P)
    (hX : ∃ i, (X i : R5) ∉ P) : κf P' + κf P = 1 := by
  have hX1 : ∀ i, (X i : R5) ∈ P' ↔ X (e5 i) ∈ P := fun i => by
    rw [hlin _ (isHomogeneous_X _ _), rename_X]
  have hX2 : ∀ i j, (X i + X j : R5) ∈ P' ↔ X (e5 i) + X (e5 j) ∈ P := fun i j => by
    rw [hlin _ ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)), map_add, rename_X, rename_X]
  have hA : MemA P' ↔ MemB P := by
    simp only [MemA, MemB, Lc, Gp, Lb, Gm, hX1, hX2, e5, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    tauto
  have hCp : MemCp P' ↔ MemCq P := by
    simp only [MemCp, MemCq, hX1, hX2, e5, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
  have hAB := memA_or_memB hR hπ hb hε I.two_unit I.γ_unit
  have hiff := memA_and_memB_iff hR hε I.γ_unit hX
  have hdisj := not_memCp_and_memCq (P := P) hX
  unfold κf
  rw [hA, hCp]
  have key : (MemB P ∧ ¬ MemCq P) ↔ ¬ (MemA P ∧ ¬ MemCp P) := by
    constructor
    · rintro ⟨hB, hq⟩ ⟨hA', hp⟩
      exact (hiff.1 ⟨hA', hB⟩).elim hp hq
    · intro h
      rcases hAB with hA' | hB'
      · have hp : MemCp P := by_contra fun hp => h ⟨hA', hp⟩
        exact ⟨(hiff.2 (Or.inl hp)).2, fun hq => hdisj ⟨hp, hq⟩⟩
      · exact ⟨hB', fun hq => h ⟨(hiff.2 (Or.inr hq)).1, fun hp => hdisj ⟨hp, hq⟩⟩⟩
  by_cases h1 : MemA P ∧ ¬ MemCp P
  · rw [if_neg (fun h => key.1 h h1), if_pos h1]
    norm_num
  · rw [if_pos (key.2 h1), if_neg h1]
    norm_num

/-! ### The object `Z` and the morphisms to `X₀` and to the cover -/

variable (A) in
/-- **The object `Z`**: the `ℤ`-covering of the `4`-gon over the level `(R', 1)`. -/
def Zobj : TempObj O R A where
  Lv := level A I
  P := (D' A I).toCode _ (level_ρs I)

variable (A) in
/-- The level morphism `(R', 1) ⟶ (R, 1)`. -/
def levelToUnit : (coverEt R A R').level ⟶ TateObject.unitLevel R A where
  f := (Algebra.ofId R _).comp (TateObject.unitEquiv R).toAlgHom
  r := 1
  r_a _ := Subsingleton.elim _ _
  f_σ g y := by
    rw [coverH_eq_one g]
    rfl

lemma levelStructureMap_unit (o : O) : (levelToUnit A).f
    (levelStructureMap O R A (TateObject.unitLevel R A) o) = algebraMap O (Bc R A R') o := by
  exact AlgHom.commutes (levelToUnit A).f (algebraMap K R (o : K))

lemma aeval_gB_ℓψ : (fun j => aeval (gB A I) (ℓψ I.ε I.κ j)) =
    ![algebraMap R (Bc R A R') T.x, algebraMap R (Bc R A R') T.y,
      algebraMap O (Bc R A R') T.π] := by
  have h := aeval_ℓψ I
  funext j
  rw [aeval_gB]
  have hj := congrFun h j
  rw [hj]
  fin_cases j
  · exact (AlgEquiv.commutes _ _)
  · exact (AlgEquiv.commutes _ _)
  · exact (eB O R A).commutes T.π

lemma jm_ψ :
    jm A I ≫ ψ T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ I.two_unit =
      Spec.map (CommRingCat.ofHom ((levelToUnit (R := R) (R' := R') A).f :
        (TateObject.unitLevel R A).B →+* (Bc R A R'))) ≫
        TateModel.toModel T.π T.b₄ T.b₆ (levelStructureMap O R A (TateObject.unitLevel R A))
          (T.equation_B (A := A)) (T.isUnit_π (A := A)) := by
  rw [← cancel_mono (TateModel.ι T.π T.b₄ T.b₆), Category.assoc, ψ_ι, Category.assoc,
    TateModel.toModel_ι, TateModel.SpecMap_toProj]
  swap
  · exact (T.isUnit_π (A := A)).map ((levelToUnit (R := R) (R' := R') A).f :
      (TateObject.unitLevel R A).B →+* Bc R A R')
  have hk : IsUnit (aeval (gB A I) (linHom (ℓψ I.ε I.κ) (ℓψ_mem I.ε I.κ) (X 2))) := by
    rw [linHom_apply, aeval_X]
    exact isUnit_gB4 I
  have hk' : IsUnit (aeval (fun j => aeval (gB A I) (ℓψ I.ε I.κ j))
      (X 2 : MvPolynomial (Fin (2 + 1)) O)) := by
    rw [aeval_X]
    exact isUnit_gB4 I
  have h := comp_proj_of_eq_ptT (ℓψ I.ε I.κ) (ℓψ_mem I.ε I.κ)
    (hcov T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ I.two_unit) (jm A I) (gB A I) 2 hk (𝟙 _)
    ((jm_ιm I).trans ((ptT_eq (gB A I) (isUnit_gB4 I) hk (X_mem' 4) _ one_pos).trans
      (Category.id_comp _).symm)) hk'
  refine h.trans ((Category.id_comp _).trans ?_)
  have hπ : IsUnit (algebraMap O (Bc R A R') T.π) := by
    rw [← (eB O R A).commutes T.π]
    exact (isUnit_π_R' (T := T) (R' := R')).map _
  have e1 : ((levelToUnit (R := R) (R' := R') A).f :
      (TateObject.unitLevel R A).B →+* Bc R A R').comp
      (levelStructureMap O R A (TateObject.unitLevel R A)) = algebraMap O (Bc R A R') :=
    RingHom.ext fun o => levelStructureMap_unit (A := A) (R := R) (R' := R') o
  have e2 : (levelToUnit A).f (algebraMap R (TateObject.unitLevel R A).B T.x) =
      algebraMap R (Bc R A R') T.x := AlgHom.commutes _ _
  have e3 : (levelToUnit A).f (algebraMap R (TateObject.unitLevel R A).B T.y) =
      algebraMap R (Bc R A R') T.y := AlgHom.commutes _ _
  have key : ∀ (φ : O →+* Bc R A R') (x y : Bc R A R') (hφ : φ = algebraMap O _)
      (hx : x = algebraMap R (Bc R A R') T.x) (hy : y = algebraMap R (Bc R A R') T.y) hπ',
      TateModel.toProj T.π φ x y hπ' = ptT (fun j => aeval (gB A I) (ℓψ I.ε I.κ j)) (X 2) hk'
        (X_mem' 2) one_pos := by
    rintro _ _ _ rfl rfl rfl hπ'
    rw [toProj_eq_ptT T.π _ _ hπ (by rw [aeval_X]; exact hπ)]
    exact ptT_congr_c (aeval_gB_ℓψ I).symm _ _ _ _ _
  exact (key _ _ _ e1 e2 e3 (by rw [e1]; exact hπ)).symm

variable (A) in
/-- The coded map of coverings `(z, n) ↦ (ψ z, 2n + κ z + c)`. -/
def hA (c : ℤ) : (Zobj A I).P.carrier → (TateObject.X₀ (A := A) T).P.carrier := fun x =>
  (TateObject.decomp (A := A) T).codeEquiv.symm
    (TateCovering.Decomp.mapTwo (D' A I) (TateObject.decomp (A := A) T) (ψs A I) (κZ I) c
      ((D' A I).codeEquiv x))

lemma continuous_hA (c : ℤ) : Continuous (hA A I c) := by
  letI := (D' A I).codeTop
  letI := (TateObject.decomp (A := A) T).codeTop
  exact (TateObject.decomp (A := A) T).codeHomeomorph.symm.continuous.comp
    ((continuous_mapTwo_Z I c).comp (D' A I).codeHomeomorph.continuous)

variable (A) in
/-- **The morphism `a : Z ⟶ X₀`.** -/
def aHom (c : ℤ) : Zobj A I ⟶ TateObject.X₀ (A := A) T where
  φ := levelToUnit A
  ψ := ψ T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ I.two_unit
  ψ_toSpec := ψ_toSpec _ _ _ _ _ _ _ _ _
  j_ψ := jm_ψ I
  h := hA A I c
  continuous_h := continuous_hA I c
  fst_h _ := rfl
  h_act g x := by
    rw [coverH_eq_one g]
    rfl

/-- The model map to the trivial model. -/
abbrev ψb : (model T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ).scheme ⟶
    (ModelCode.trivial O).scheme :=
  (model T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ).toSpec ≫ inv (ModelCode.trivial O).toSpec

lemma ψb_toSpec : ψb I ≫ (ModelCode.trivial O).toSpec =
    (model T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ).toSpec := by
  simp

variable (A) in
/-- **The morphism `b : Z ⟶ coverObj R'`.** -/
def bHom : Zobj A I ⟶ coverObj O R A R' where
  φ := 𝟙 _
  ψ := ψb I
  ψ_toSpec := ψb_toSpec I
  j_ψ := by
    change (level A I).j ≫ (level A I).c.toSpec ≫ _ = _ ≫
      (Spec.map (CommRingCat.ofHom (levelStructureMap O R A (coverEt R A R').level)) ≫ _)
    rw [← Category.assoc, (level A I).j_toSpec]
    erw [TempObj.spec_map_id_f, Category.id_comp]
    rfl
  h x := ⟨(specialFibreMap (ψb I) (ψb_toSpec I) x.1.1, 0), Set.mem_univ _, Nat.zero_lt_one⟩
  continuous_h := by
    apply Continuous.subtype_mk
    exact ((continuous_specialFibreMap _ _).comp (Zobj A I).P.continuous_proj).prodMk
      continuous_const
  fst_h _ := rfl
  h_act g x := by
    rw [coverH_eq_one g]
    exact (TempObj.coverObj_act_one _).symm

/-! ### Fibres -/

section Fibre

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- The structure of `O`-algebra on `Ω`. -/
abbrev algΩ : Algebra O Ω := (valToField O).toAlgebra

attribute [local instance] algΩ

/-- A geometric point as a map of `O`-algebras. -/
def tO (t : Bc R A R' →ₐ[R] Ω) : Bc R A R' →ₐ[O] Ω :=
  { (t : Bc R A R' →+* Ω) with
    commutes' := fun o => by
      change t (algebraMap R _ (algebraMap K R (o : K))) = algebraMap K Ω (o : K)
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }

lemma point_ιm (t : Bc R A R' →ₐ[R] Ω)
    (hu : IsUnit (aeval (fun i => t (gB A I i)) (X 4 : R5))) :
    (level A I).point t ≫ ιm T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ =
      ptT (fun i => t (gB A I i)) (X 4) hu (X_mem' 4) one_pos := by
  rw [Level.point, Category.assoc]
  change _ ≫ jm A I ≫ _ = _
  rw [jm_ιm, j0]
  exact SpecMap_ptT (tO t) (gB A I) (X 4) _ hu _ _

lemma isUnit_tgB4 (t : Bc R A R' →ₐ[R] Ω) :
    IsUnit (aeval (fun i => t (gB A I i)) (X 4 : R5)) := by
  rw [aeval_X]
  have := isUnit_gB4 (A := A) I
  rw [aeval_X] at this
  exact this.map t

lemma sp_eq_of_eq {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of O)} [UniversallyClosed f]
    [IsSeparated f] {x x' : Spec (CommRingCat.of Ω) ⟶ X} (e : x = x') (hx hx') :
    sp f V hV x hx = sp f V hV x' hx' := by
  subst e
  rfl

/-- **The deck involution swaps the specialisations.** -/
lemma sp_swap (t t' : Bc R A R' →ₐ[R] Ω) (h : ∀ i, t' (gB A I i) = t (gB A I (e5 i))) :
    ιZ I ((level A I).sp V hV t') = ρsw O (ιZ I ((level A I).sp V hV t)) := by
  have hpt : (level A I).point t' ≫ ιm T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ =
      ((level A I).point t ≫ ιm T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ) ≫ ρsw O := by
    rw [point_ιm I t' (isUnit_tgB4 I t'), point_ιm I t (isUnit_tgB4 I t)]
    refine Eq.trans ?_ (ptT_ρsw _ (isUnit_tgB4 I t) ?_).symm
    · exact ptT_congr_c (funext h) _ _ _ _ _
    · simpa [e5] using isUnit_tgB4 (A := A) I t
  have e1 := coe_sp_comp (hV := hV) (f := (level A I).c.toSpec) (f' := projSpace.toSpec O 4)
    (ιm T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ) rfl ((level A I).point t')
    ((level A I).point_toSpec t')
  have e2 := coe_sp_comp (hV := hV) (f := (level A I).c.toSpec) (f' := projSpace.toSpec O 4)
    (ιm T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ) rfl ((level A I).point t)
    ((level A I).point_toSpec t)
  have e3 := coe_sp_comp (hV := hV) (f := projSpace.toSpec O 4) (f' := projSpace.toSpec O 4)
    (ρsw O) ρsw_toSpec ((level A I).point t ≫ ιm T.π T.b₄ T.b₆ I.b₄' I.b₆' I.ε I.γ I.κ)
    (by rw [Category.assoc]; exact (level A I).point_toSpec t)
  refine e1.symm.trans (Eq.trans ?_ (e3.trans (congrArg (ρsw O) e2)))
  exact congrArg Subtype.val (sp_eq_of_eq V hV hpt _ _)

lemma κZ_swap (t t' : Bc R A R' →ₐ[R] Ω) (h : ∀ i, t' (gB A I i) = t (gB A I (e5 i))) :
    κZ I ((level A I).sp V hV t') + κZ I ((level A I).sp V hV t) = 1 := by
  set z := (level A I).sp V hV t
  refine κf_swap I (P := Pz I z) (fun r hr => ?_) (relsZ I z) (hπZ I z) (hbZ I z) (hεZ I z)
    (hXZ I z)
  change r ∈ (ιZ I _).asHomogeneousIdeal ↔ _
  rw [sp_swap I V hV t t' h, mem_ρsw_iff _ ((mem_homogeneousSubmodule _ _).2 hr) one_pos]
  rfl

variable (R A R' Ω) in
/-- The base point of the cover. -/
abbrev t₀ : Bc R A R' →ₐ[R] Ω := coverPt R A R' Ω

variable (A) in
/-- The constant normalising the labels at the base point. -/
def c₀ : ℤ := -κZ I ((level A I).sp V hV (t₀ R A R' Ω))

variable (A) in
/-- **The base point of `Z`.** -/
def z₀ : (tempFibre O R A V hV).obj (Zobj A I) :=
  Quotient.mk _ ⟨(t₀ R A R' Ω, (D' A I).codeEquiv.symm ⟨(level A I).sp V hV (t₀ R A R' Ω), 0⟩),
    rfl⟩

lemma intEquivNat_zero : Equiv.intEquivNat 0 = 0 := rfl

lemma map_aHom_z₀ :
    (tempFibre O R A V hV).map (aHom A I (c₀ A I V hV)) (z₀ A I V hV) =
      TateObject.basePoint (A := A) T V hV := by
  change Quotient.mk _ (TempObj.preMap V hV (aHom A I (c₀ A I V hV)) _) = Quotient.mk _ _
  congr 1
  apply Subtype.ext
  refine Prod.ext ((TateObject.subsingleton_fibre (A := A)).elim _ _) ?_
  change hA A I (c₀ A I V hV) _ = _
  simp only [hA, Equiv.apply_symm_apply, TateCovering.Decomp.mapTwo, c₀, mul_zero, zero_add,
    add_neg_cancel]
  have hψ := TempObj.ψ_sp V hV (aHom A I (c₀ A I V hV)) (t₀ R A R' Ω)
  have ht : (t₀ R A R' Ω).comp (aHom A I (c₀ A I V hV)).φ.f =
      (Algebra.ofId R Ω).comp (TateObject.unitEquiv R).toAlgHom :=
    (TateObject.subsingleton_fibre (A := A)).elim _ _
  apply Subtype.ext
  refine Prod.ext (Subtype.ext (hψ.trans ?_)) intEquivNat_zero
  exact congrArg (fun t => ((TateObject.X₀ (A := A) T).Lv.sp V hV t :
    (TateObject.X₀ (A := A) T).Lv.c.scheme)) ht

lemma map_bHom_z₀ :
    (tempFibre O R A V hV).map (bHom A I) (z₀ A I V hV) = coverFibrePt V hV := by
  apply (etaleToTempFibreEquiv O R A V hV (coverEt R A R')).injective
  rw [coverFibrePt, Equiv.apply_symm_apply]
  rfl

/-- **`a` is injective on fibres** when the two `R`-points of `R'` over a geometric point differ
by the deck involution. -/
theorem injective_aHom (c : ℤ)
    (hfib : ∀ τ τ' : R' →ₐ[R] Ω, τ' = τ ∨
      (τ' I.x₁ = τ I.x₂ ∧ τ' I.y₁ = τ I.y₂ ∧ τ' I.x₂ = τ I.x₁ ∧ τ' I.y₂ = τ I.y₁)) :
    Function.Injective ((tempFibre O R A V hV).map (aHom A I c)) := by
  intro z z' hzz
  induction z using Quotient.inductionOn with | h q => ?_
  induction z' using Quotient.inductionOn with | h q' => ?_
  change Quotient.mk _ (TempObj.preMap V hV (aHom A I c) q) =
    Quotient.mk _ (TempObj.preMap V hV (aHom A I c) q') at hzz
  obtain ⟨g, hg⟩ := Quotient.exact hzz
  have hg1 : g = 1 := Subtype.ext (TateObject.unitLevel_H_eq_one (A := A) g.1)
  have hg' : TempObj.preMap V hV (aHom A I c) q' = TempObj.preMap V hV (aHom A I c) q := by
    rw [hg1] at hg
    exact (one_smul _ _).symm.trans hg
  have h2 : hA A I c q'.1.2 = hA A I c q.1.2 := congrArg (fun r => r.1.2) hg'
  have h3 := (TateObject.decomp (A := A) T).codeEquiv.symm.injective h2
  -- the points of the covering spaces
  set y := (D' A I).codeEquiv q.1.2 with hy
  set y' := (D' A I).codeEquiv q'.1.2 with hy'
  have hpt : y.pt = (level A I).sp V hV q.1.1 := Subtype.ext q.2
  have hpt' : y'.pt = (level A I).sp V hV q'.1.1 := Subtype.ext q'.2
  have hn : 2 * y'.n + κZ I y'.pt + c = 2 * y.n + κZ I y.pt + c :=
    congrArg TateCovering.Decomp.Space.n h3
  let τ : R' →ₐ[R] Ω := q.1.1.comp (coverE R A R').symm.toAlgHom
  let τ' : R' →ₐ[R] Ω := q'.1.1.comp (coverE R A R').symm.toAlgHom
  rcases hfib τ τ' with he | ⟨h1, h2, h3, h4⟩
  · have ht : q'.1.1 = q.1.1 := by
      ext b
      have := congrArg (fun φ : R' →ₐ[R] Ω => φ (coverE R A R' b)) he
      change q'.1.1 ((coverE R A R').symm (coverE R A R' b)) =
        q.1.1 ((coverE R A R').symm (coverE R A R' b)) at this
      rwa [AlgEquiv.symm_apply_apply] at this
    have hyy : y' = y := by
      have hp : y'.pt = y.pt := by rw [hpt, hpt', ht]
      exact TateCovering.Decomp.Space.ext hp (by rw [hp] at hn; omega)
    have : q'.1.2 = q.1.2 := (D' A I).codeEquiv.injective hyy
    exact (congrArg (Quotient.mk _) (Subtype.ext (Prod.ext ht this))).symm
  · exfalso
    have hsw : ∀ i, q'.1.1 (gB A I i) = q.1.1 (gB A I (e5 i)) := fun i => by
      fin_cases i
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · have e : gB A I 4 = algebraMap R (Bc R A R') (algebraMap K R (T.π : K)) :=
          (eB O R A).commutes T.π
        change q'.1.1 (gB A I 4) = q.1.1 (gB A I 4)
        rw [e]
        exact (q'.1.1.commutes _).trans (q.1.1.commutes _).symm
    have hκ := κZ_swap I V hV q.1.1 q'.1.1 hsw
    rw [← hpt, ← hpt'] at hκ
    omega

/-- **The object of `piY_le_range_of_hom`**: an object `Z` with morphisms to `X₀` (injective on
fibres) and to the cover `Spec R' → Spec R`, and a point over both base points. -/
theorem exists_object
    (hfib : ∀ τ τ' : R' →ₐ[R] Ω, τ' = τ ∨
      (τ' I.x₁ = τ I.x₂ ∧ τ' I.y₁ = τ I.y₂ ∧ τ' I.x₂ = τ I.x₁ ∧ τ' I.y₂ = τ I.y₁)) :
    ∃ (Z : TempObj O R A) (a : Z ⟶ TateObject.X₀ (A := A) T) (b : Z ⟶ coverObj O R A R')
      (z₀ : (tempFibre O R A V hV).obj Z),
      (tempFibre O R A V hV).map a z₀ = TateObject.basePoint (A := A) T V hV ∧
      (tempFibre O R A V hV).map b z₀ = coverFibrePt V hV ∧
      Function.Injective ((tempFibre O R A V hV).map a) :=
  ⟨Zobj A I, aHom A I (c₀ A I V hV), bHom A I, z₀ A I V hV, map_aHom_z₀ I V hV, map_bHom_z₀ I V hV,
    injective_aHom I V hV _ hfib⟩

end Fibre

end

end FourGon

end TemperedFundamentalGroups
