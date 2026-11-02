/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateNGonObject
import TemperedFundamentalGroups.Andre.TateFourGonCover

/-!
# The `ℤ`-covering of the Tate curve dominates the cyclic cover `E_{q^N} → E_q`

Let `T` be Tate data of `E_q` on `R` (`TateObject.Data`, `π = s`, `s² = q`), `N ≥ 3`, and `R'` a
finite étale `R`-algebra (in the application the coordinate ring of the level `K(E_{q^N})`) with
elements `x_k, y_k` (`k ∈ ℤ/N`, the points `P(q^k u)` of `E_{q^N}`) satisfying the equations of the
`2N`-gon model and Vélu's formulas (`NGon.Input`). This file constructs (TFGD-plan, "Run 6/7"):

* the level `(R', 1)` with the `2N`-gon model `NGon.model` and `j = [x_0 : y_0 : … : π]`;
* the object `Z` with the `ℤ`-covering of the `2N`-gon (`NGon.decomp`);
* `a : Z ⟶ X₀` (the model map `NGon.ψ` and `(z, n) ↦ (ψ z, N n + κ z + c)`, `κ z ≡ i` on the
  piece `A_i`) and `b : Z ⟶ coverObj R'`, a point `z₀` over both base points, and **`a` is
  injective on fibres** when two `R`-points of `R'` over a geometric point differ by a cyclic
  shift of the blocks (the deck group `ℤ/N`, translation by `T`), which shifts the pieces.

Main result: **`NGon.exists_object`**, the input of `piY_le_range_of_hom` (iut).
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial Pi1.Orbifold
open SemistableReduction.LinearProjectionN

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

namespace NGon

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A] [Subsingleton A]
  [MulSemiringAction A R] [SMulCommClass A K R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  [Algebra.Etale R R'] [Module.Finite R R'] {N : ℕ} [NeZero N]

set_option hygiene false in
local notation "RN" => MvPolynomial (Fin (2 * N + 1)) O

variable (O R' N) in
/-- **The input data**: the Tate data `b₄', b₆'` of `E_{q^N}` (same `π`), the coefficients of the
model equations, and the coordinates `x_k, y_k ∈ R'` with the model equations (in the affine
coordinates `[x : y : π]`), Vélu's formulas `x = Σ x_k − π ε`, `y = Σ y_k + π κ`, and the
reduction hypotheses `NGon.Good`. -/
structure Input (T : TateObject.Data O R) where
  b₄' : O
  b₆' : O
  cP : Fin 3 → ZMod N → Fin 3 → Fin 3 → O
  e : ZMod N → O
  g : ZMod N → O
  ε : O
  κ : O
  x : ZMod N → R'
  y : ZMod N → R'
  eq : ∀ k, y k ^ 2 + x k * y k = x k ^ 3 + algebraMap K R' ((T.π : K) ^ 2 * b₄') * x k +
    algebraMap K R' ((T.π : K) ^ 2 * b₆')
  pair : ∀ (i : Fin 3) (d k : ZMod N), d ≠ 0 →
    ∑ a, ∑ b, algebraMap K R' (cP i d a b : K) * ![algebraMap K R' (T.π : K), x k, y k] a *
      ![algebraMap K R' (T.π : K), x (k + d), y (k + d)] b = 0
  gam : ∀ d : ZMod N, d ≠ 0 →
    ∑ k, (x k - algebraMap K R' ((T.π : K) * e d)) * (x (k + d) - algebraMap K R' ((T.π : K) * e d))
      = algebraMap K R' ((T.π : K) ^ 2 * g d)
  vx : algebraMap R R' T.x = ∑ k, x k - algebraMap K R' ((T.π : K) * ε)
  vy : algebraMap R R' T.y = ∑ k, y k + algebraMap K R' ((T.π : K) * κ)
  good : Good (⟨T.π, T.b₄, T.b₆, b₄', b₆', cP, e, g, ε, κ⟩ : Coeffs O N)

variable {T : TateObject.Data O R} (I : Input O R' N T)

/-- The coefficients of the model. -/
def co : Coeffs O N := ⟨T.π, T.b₄, T.b₆, I.b₄', I.b₆', I.cP, I.e, I.g, I.ε, I.κ⟩

attribute [local instance] FourGon.algR'

/-! ### The coordinates -/

/-- The coordinates `(x_0, y_0, …, x_{N−1}, y_{N−1}, π)` in `R'`. -/
def gR : Fin (2 * N + 1) → R' := fun j =>
  if j.val = 2 * N then algebraMap K R' (T.π : K)
  else if j.val % 2 = 0 then I.x ((j.val / 2 : ℕ) : ZMod N) else I.y ((j.val / 2 : ℕ) : ZMod N)

@[simp] lemma gR_ix (k : ZMod N) : gR I (ix k) = I.x k := by
  have := ZMod.val_lt k
  simp only [gR, ix]
  rw [if_neg (by omega), if_pos (by omega), show 2 * k.val / 2 = k.val by omega,
    ZMod.natCast_zmod_val]

@[simp] lemma gR_iy (k : ZMod N) : gR I (iy k) = I.y k := by
  have := ZMod.val_lt k
  simp only [gR, iy]
  rw [if_neg (by omega), if_neg (by omega), show (2 * k.val + 1) / 2 = k.val by omega,
    ZMod.natCast_zmod_val]

@[simp] lemma gR_iw : gR (T := T) I (iw N) = algebraMap K R' (T.π : K) := by
  simp [gR, iw]

lemma aeval_vA (k : ZMod N) (a : Fin 3) :
    aeval (gR I) (vA (O := O) k a) = ![algebraMap K R' (T.π : K), I.x k, I.y k] a := by
  fin_cases a <;> simp [vA]

lemma aeval_cub (k : ZMod N) : aeval (gR I) (cub T.π I.b₄' I.b₆' k : RN) = 0 := by
  have h := I.eq k
  simp only [cub, xx, yy, ww, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    FourGon.algebraMap_O_R', gR_ix, gR_iy, gR_iw]
  push_cast at h ⊢
  try simp only [map_mul, map_pow] at h ⊢
  linear_combination algebraMap K R' (T.π : K) * h

lemma aeval_bil (i : Fin 3) {d : ZMod N} (hd : d ≠ 0) (k : ZMod N) :
    aeval (gR I) (bil (I.cP i d) k d : RN) = 0 := by
  simp only [bil, map_sum, map_mul, aeval_C, aeval_vA, FourGon.algebraMap_O_R']
  exact I.pair i d k hd

lemma aeval_gam {d : ZMod N} (hd : d ≠ 0) : aeval (gR I) (gam (I.e d) (I.g d) d : RN) = 0 := by
  have hl : ∀ k, aeval (gR I) (xx k - C (I.e d) * ww O N : RN) =
      I.x k - algebraMap K R' ((T.π : K) * I.e d) := fun k => by
    simp only [xx, ww, map_sub, map_mul, aeval_X, aeval_C, FourGon.algebraMap_O_R', gR_ix, gR_iw]
    ring
  have hw : aeval (gR I) (C (I.g d) * ww O N ^ 2 : RN) =
      algebraMap K R' ((T.π : K) ^ 2 * I.g d) := by
    simp only [ww, map_mul, map_pow, aeval_X, aeval_C, FourGon.algebraMap_O_R', gR_iw]
    ring
  rw [gam, map_sub, map_sum, hw, Finset.sum_congr rfl fun k _ => by rw [map_mul, hl, hl],
    I.gam d hd, sub_self]

lemma aeval_ℓψ : (fun j => aeval (gR I) (ℓψ (N := N) I.ε I.κ j)) =
    ![algebraMap R R' T.x, algebraMap R R' T.y, algebraMap K R' (T.π : K)] := by
  funext j
  fin_cases j
  · change aeval (gR I) (∑ k : ZMod N, xx k - C I.ε * ww O N : RN) = algebraMap R R' T.x
    rw [I.vx]
    simp only [xx, ww, map_sub, map_sum, map_mul, aeval_X, aeval_C, FourGon.algebraMap_O_R',
      gR_ix, gR_iw]
    ring
  · change aeval (gR I) (∑ k : ZMod N, yy k + C I.κ * ww O N : RN) = algebraMap R R' T.y
    rw [I.vy]
    simp only [yy, ww, map_add, map_sum, map_mul, aeval_X, aeval_C, FourGon.algebraMap_O_R',
      gR_iy, gR_iw]
    ring
  · change aeval (gR I) (ww O N : RN) = algebraMap K R' (T.π : K)
    rw [aeval_X, gR_iw]

lemma aeval_Fℓ : aeval (gR I) (Fℓ (co I) : RN) = 0 := by
  rw [Fℓ, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  change aeval (fun j => aeval (gR I) (ℓψ (N := N) I.ε I.κ j)) _ = 0
  rw [aeval_ℓψ I]
  have h := congrArg (algebraMap R R') T.equation
  simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at h
  simp only [co, TateModel.F, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    FourGon.algebraMap_O_R', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  try simp only [map_mul, map_pow] at h ⊢
  linear_combination algebraMap K R' (T.π : K) * h

/-! ### Homogeneity of the equations -/

lemma isHomogeneous_vA (k : ZMod N) (a : Fin 3) : (vA (O := O) k a).IsHomogeneous 1 := by
  fin_cases a <;> exact isHomogeneous_X _ _

lemma isHomogeneous_cub (π b₄ b₆ : O) (k : ZMod N) : (cub π b₄ b₆ k : RN).IsHomogeneous 3 := by
  unfold cub
  refine ((((((isHomogeneous_X_pow _ _).mul (isHomogeneous_X _ _)).add
    (((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X _ _))).sub
    (isHomogeneous_C_mul_X_pow _ _ _)).sub ?_).sub (isHomogeneous_C_mul_X_pow _ _ _))
  exact ((isHomogeneous_C _ _).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X_pow _ _)

lemma isHomogeneous_bil (c : Fin 3 → Fin 3 → O) (k d : ZMod N) :
    (bil c k d : RN).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => by
    simpa using ((isHomogeneous_C _ (c a b)).mul (isHomogeneous_vA k a)).mul
      (isHomogeneous_vA (k + d) b)

lemma isHomogeneous_gam (e g : O) (d : ZMod N) : (gam e g d : RN).IsHomogeneous 2 := by
  have hl : ∀ k : ZMod N, (xx k - C e * ww O N : RN).IsHomogeneous 1 := fun k =>
    (isHomogeneous_X _ _).sub (by simpa using (isHomogeneous_C _ e).mul (isHomogeneous_X _ _))
  exact (IsHomogeneous.sum _ _ _ fun k _ => (hl k).mul (hl (k + d))).sub
    (isHomogeneous_C_mul_X_pow _ _ _)

lemma Fℓ_mem (D : Coeffs O N) : Fℓ D ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * N + 1)) O 3 :=
  (linHom (ℓψ D.ε D.κ) (ℓψ_mem D.ε D.κ)).map_mem
    ((mem_homogeneousSubmodule _ _).2 (TateModel.isHomogeneous_F D.π D.b₄ D.b₆))

/-! ### The level `(R', 1)` with the `2N`-gon model -/

attribute [local instance] FourGon.algB

variable (A) in
/-- The coordinates in the coded ring. -/
def gB : Fin (2 * N + 1) → FourGon.Bc R A R' := fun i => FourGon.eB O R A (gR I i)

lemma aeval_gB (r : RN) : aeval (gB A I) r = FourGon.eB O R A (aeval (gR I) r) := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

lemma isUnit_gBw : IsUnit (aeval (gB A I) (ww O N : RN)) := by
  rw [aeval_X]
  change IsUnit (FourGon.eB O R A (gR I (iw N)))
  rw [gR_iw]
  exact (FourGon.isUnit_π_R' (T := T) (R' := R')).map (FourGon.eB O R A)

variable (A) in
/-- **The point `[x_0 : y_0 : … : π] : Spec B ⟶ ℙ^{2N}_O`.** -/
def j0 : Spec (CommRingCat.of (FourGon.Bc R A R')) ⟶ projSpace O (2 * N) :=
  ptT (gB A I) (ww O N) (isUnit_gBw I) (X_mem' (iw N)) one_pos

lemma j0_toSpec : j0 A I ≫ projSpace.toSpec O (2 * N) =
    Spec.map (CommRingCat.ofHom (levelStructureMap O R A (coverEt R A R').level)) :=
  ptT_toSpec _ _ _ _ _

lemma rels_j0 (x : Spec (CommRingCat.of (FourGon.Bc R A R'))) :
    Rels (co I) (j0 A I x).asHomogeneousIdeal.toIdeal := by
  have key : ∀ (r : RN) (e : ℕ), r.IsHomogeneous e → 0 < e → aeval (gR I) r = 0 →
      r ∈ (j0 A I x).asHomogeneousIdeal := fun r e hr he h0 => by
    refine (mem_ptT_iff (gB A I) (isUnit_gBw I) (X_mem' (iw N)) one_pos x
      ((mem_homogeneousSubmodule _ _).2 hr) he).2 ?_
    rw [aeval_gB, h0, map_zero]
    exact zero_mem _
  rintro r (((⟨k, rfl⟩ | ⟨i, d, k, hd, rfl⟩) | ⟨d, hd, rfl⟩) | rfl)
  · exact key _ 3 (isHomogeneous_cub _ _ _ _) three_pos (aeval_cub I k)
  · exact key _ 2 (isHomogeneous_bil _ _ _) two_pos (aeval_bil I i hd k)
  · exact key _ 2 (isHomogeneous_gam _ _ _) two_pos (aeval_gam I hd)
  · exact key _ 3 ((mem_homogeneousSubmodule _ _).1 (Fℓ_mem _)) three_pos (aeval_Fℓ I)

variable [IsReduced R']

instance : QuasiCompact (j0 A I) := by
  have : QuasiCompact (j0 A I ≫ projSpace.toSpec O (2 * N)) := by
    rw [j0_toSpec]
    infer_instance
  exact .of_comp _ (projSpace.toSpec O (2 * N))

lemma modelIdeal_le_ker_j0 : modelIdeal (co I) ≤ (j0 A I).ker := by
  refine le_trans ?_ (TateModel.radical_ker_le _)
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
  change (↑((j0 A I).ker.support) : Set (projSpace O (2 * N))) ⊆ _
  rw [Scheme.Hom.support_ker]
  refine (relSet (co I)).isClosed.closure_subset_iff.2 ?_
  rintro _ ⟨x, rfl⟩
  exact rels_j0 I x

variable (A) in
/-- **The map `j : Spec B ⟶ model`.** -/
def jm : Spec (CommRingCat.of (FourGon.Bc R A R')) ⟶ (modelIdeal (co I)).subscheme :=
  (j0 A I).toImage ≫ Scheme.IdealSheafData.inclusion (modelIdeal_le_ker_j0 I)

lemma jm_ιm : jm A I ≫ ιm (co I) = j0 A I := by
  rw [jm, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]

variable (A) in
/-- **The level `(R', 1)` with the `2N`-gon model.** -/
def level : Level O R A where
  L := (coverEt R A R').level
  c := model (co I)
  j := jm A I
  j_toSpec := by
    change jm A I ≫ ιm (co I) ≫ projSpace.toSpec O (2 * N) = _
    rw [← Category.assoc, jm_ιm, j0_toSpec]
  ρ := 1
  ρ_toSpec _ := Category.id_comp _
  ρ_j g := by
    rw [FourGon.coverH_eq_one g, MonoidHom.one_apply]
    change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    convert Category.id_comp _
    rw [← Spec.map_id]
    rfl

lemma level_ρs (g : (level A I).L.H) : (level A I).ρs g = 1 := by
  rw [FourGon.coverH_eq_one g]
  exact map_one _

/-! ### The special fibre: the `2N`-gon over the `2`-gon -/

/-- The special fibre in `ℙ^{2N}`. -/
def ιZ (z : (level A I).Z) : projSpace O (2 * N) := ιm (co I) z.1

/-- The prime of `O[X_0, …, X_{2N}]` of a point of the special fibre. -/
abbrev Pz (z : (level A I).Z) : Ideal RN := pt (ιZ I) z

lemma continuous_ιZ : Continuous (ιZ (A := A) I) :=
  (ιm (co I)).continuous.comp continuous_subtype_val

lemma special_ιZ (z : (level A I).Z) (c : O) (hc : c ∈ IsLocalRing.maximalIdeal O) :
    C c ∈ Pz I z :=
  (mem_specialFibre_projSpace_iff (ιZ I z)).1 z.2 c hc

lemma relsZ (z : (level A I).Z) : Rels (co I) (Pz I z) := rels_ιm (co I) z.1

lemma goodI : Good (co I) := I.good

include I in
lemma hN3 : 3 ≤ N := (goodI I).2.1

lemma redZ (z : (level A I).Z) : Red (I.g 1) (Pz I z) :=
  red_of_rels (goodI I).1 (hN3 I) (special_ιZ I z) (relsZ I z)

lemma hγ1 : IsUnit (I.g 1) := (goodI I).2.2.1

lemma hXZ (z : (level A I).Z) : ∃ j, (X j : RN) ∉ Pz I z := exists_X_notMem _

variable (A) in
/-- **The decomposition of the special fibre into `A_0` and `A_1 ∪ … ∪ A_{N−1}`.** -/
def D' : TateCovering.Decomp (level A I).Z :=
  decomp N (γ := I.g 1) (ι := ιZ (A := A) I) (continuous_ιZ I) (redZ I) (hγ1 I) (hN3 I) (hXZ I)

variable (A) in
/-- The model map on special fibres. -/
def ψs : (level A I).Z → (TateObject.level (A := A) T).Z :=
  specialFibreMap (ψ (D := co I) (goodI I)) (ψ_toSpec (D := co I) (goodI I))

lemma continuous_ψs : Continuous (ψs A I) := continuous_specialFibreMap _ _

lemma mem_ψs_iff (z : (level A I).Z) {g : MvPolynomial (Fin (2 + 1)) O} {d : ℕ}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) O d) (hd : 0 < d) :
    g ∈ (TateModel.ιZ T.π T.b₄ T.b₆ (ψs A I z)).asHomogeneousIdeal ↔
      aeval (ℓψ (N := N) I.ε I.κ) g ∈ Pz I z :=
  mem_ψ_iff (D := co I) (goodI I) hg hd z.1

lemma X_mem_ψs_iff (z : (level A I).Z) (k : Fin (2 + 1)) :
    (X k : MvPolynomial (Fin (2 + 1)) O) ∈
      (TateModel.ιZ T.π T.b₄ T.b₆ (ψs A I z)).asHomogeneousIdeal ↔
      ℓψ (N := N) I.ε I.κ k ∈ Pz I z := by
  rw [mem_ψs_iff I z ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X O k)) one_pos, aeval_X]

/-- `ψ z ∈ C ↔ W = 0`. -/
lemma ψs_mem_C (z : (level A I).Z) :
    ψs A I z ∈ (TateObject.decomp (A := A) T).C ↔ ww O N ∈ Pz I z :=
  X_mem_ψs_iff I z 2

/-- The fibre `ψ⁻¹(p)`: `W = Σ y_k = 0`. -/
def Np (P : Ideal RN) : Prop := ww O N ∈ P ∧ ∑ k : ZMod N, yy k ∈ P

lemma lin_iff {P : Ideal RN} (hw : ww O N ∈ P) (a : RN) (c : O) :
    a + C c * ww O N ∈ P ↔ a ∈ P :=
  ⟨fun h => sub_mem_left h (P.mul_mem_left _ hw), fun h => P.add_mem h (P.mul_mem_left _ hw)⟩

lemma ψs_mem_Cp (z : (level A I).Z) :
    ψs A I z ∈ (TateObject.decomp (A := A) T).Cp ↔ Np (Pz I z) := by
  change (X 2 : MvPolynomial (Fin (2 + 1)) O) ∈ _ ∧ (X 1 : MvPolynomial (Fin (2 + 1)) O) ∈ _ ↔ _
  rw [X_mem_ψs_iff, X_mem_ψs_iff]
  refine ⟨fun ⟨h4, h1⟩ => ⟨h4, (lin_iff h4 _ _).1 h1⟩, fun ⟨h4, h1⟩ => ⟨h4, (lin_iff h4 _ _).2 h1⟩⟩

section Pieces

variable {P : Ideal RN} [hP : P.IsPrime] {γ : O}

omit hP in
lemma sum_add_sum (f g : ZMod N → RN) : ∑ k, f k + ∑ k, g k = ∑ k, (f k + g k) :=
  (Finset.sum_add_distrib).symm

/-- **`ψ⁻¹(q)` is the set of nodes.** -/
lemma nq_iff (hR : Red γ P) (hγ : IsUnit γ) (hN : 3 ≤ N) (hX : ∃ j, (X j : RN) ∉ P) :
    (ww O N ∈ P ∧ ∑ k : ZMod N, xx k + ∑ k : ZMod N, yy k ∈ P) ↔ ∃ i, Nd i P := by
  rw [sum_add_sum]
  constructor
  · rintro ⟨hw, hs⟩
    obtain ⟨i, hL | hG⟩ := mem_pieces hR hγ hN hX
    · refine ⟨i, hw, hL.2, ?_⟩
      have := sum_sub_mem (f := fun k => xx k + yy k) i fun k hk =>
        P.add_mem (hL.2 k hk).1 (hL.2 k hk).2
      have := P.sub_mem hs this
      rwa [sub_sub_cancel] at this
    · -- `x_{i−1} x_i = 0` from `Γ_1`
      have hi1 : i - 1 + 1 = i := sub_add_cancel i 1
      have hg := hR.gam1
      have hsum : ∑ k : ZMod N, xx k * xx (k + 1) ∈ P := by
        have := P.add_mem hg (P.mul_mem_left (C γ) (P.pow_mem_of_mem hw 2 two_pos))
        rwa [sub_add_cancel] at this
      have hone : (1 : ZMod N).val = 1 := by
        haveI : Fact (1 < N) := ⟨by omega⟩
        exact ZMod.val_one N
      have := gam_sum_sub_mem (P := P) (i := i - 1) (d := 1) (by omega) (by omega)
        fun k hk1 hk2 => hG.1 k hk1 (by rwa [hi1] at hk2)
      have hprod : xx (i - 1) * xx (i - 1 + 1) ∈ P := by
        have := P.sub_mem hsum this
        rwa [sub_sub_cancel] at this
      rw [hi1] at hprod
      have hne : i - 1 ≠ i := fun e => by
        haveI : Fact (1 < N) := ⟨by omega⟩
        exact one_ne_zero (by linear_combination -e : (1 : ZMod N) = 0)
      -- the sum `Σ (x_k + y_k)` is `(x_{i−1} + y_{i−1}) + (x_i + y_i)`
      have hxi : xx i ∈ P := by
        have h1 := sum_sub_mem (f := fun k => xx k + yy k) i fun k hk => by
          by_cases hk' : k = i - 1
          · subst hk'; exact hG.2.1
          · exact P.add_mem (hG.1 k hk' hk).1 (hG.1 k hk' hk).2
        have := P.sub_mem hs h1
        rw [sub_sub_cancel] at this
        exact sub_mem_left this hG.2.2
      refine ⟨i - 1, hw, fun k hk => ?_, hG.2.1⟩
      by_cases hki : k = i
      · subst hki
        exact ⟨hxi, hG.2.2⟩
      · exact hG.1 k hk hki
  · rintro ⟨i, hw, hZ, hi⟩
    refine ⟨hw, ?_⟩
    have := sum_sub_mem (f := fun k => xx k + yy k) i fun k hk => P.add_mem (hZ k hk).1 (hZ k hk).2
    have := P.add_mem this hi
    rwa [sub_add_cancel] at this

/-- On `G_i`, `W = 0` gives the node `c_{i−1}` or a point of `ψ⁻¹(p)`. -/
lemma G_w (hR : Red γ P) (hN : 3 ≤ N) {i : ZMod N} (hG : G i P) (hw : ww O N ∈ P)
    (hn : ¬ Np P) : Nd (i - 1) P := by
  have hi1 : i - 1 + 1 = i := sub_add_cancel i 1
  have hsum : ∑ k : ZMod N, xx k * xx (k + 1) ∈ P := by
    have := P.add_mem hR.gam1 (P.mul_mem_left (C γ) (P.pow_mem_of_mem hw 2 two_pos))
    rwa [sub_add_cancel] at this
  have hone : (1 : ZMod N).val = 1 := by
    haveI : Fact (1 < N) := ⟨by omega⟩
    exact ZMod.val_one N
  have := gam_sum_sub_mem (P := P) (i := i - 1) (d := 1) (by omega) (by omega)
    fun k hk1 hk2 => hG.1 k hk1 (by rwa [hi1] at hk2)
  have hprod : xx (i - 1) * xx (i - 1 + 1) ∈ P := by
    have := P.sub_mem hsum this
    rwa [sub_sub_cancel] at this
  rw [hi1] at hprod
  rcases hP.mem_or_mem hprod with h | h
  · exfalso
    refine hn ⟨hw, ?_⟩
    have hy : yy (i - 1) ∈ P := sub_mem_right hG.2.1 h
    have := sum_sub_mem (f := fun k => yy k) i fun k hk => by
      by_cases hk' : k = i - 1
      · subst hk'; exact hy
      · exact (hG.1 k hk' hk).2
    have := P.add_mem this hG.2.2
    rwa [sub_add_cancel] at this
  · refine ⟨hw, fun k hk => ?_, hG.2.1⟩
    by_cases hki : k = i
    · subst hki
      exact ⟨h, hG.2.2⟩
    · exact hG.1 k hk hki

open Classical in
/-- The index of the piece `A_i ∖ c_{i−1}` containing a point. -/
def idx (P : Ideal RN) : ZMod N := if h : ∃ i, NGon.A i P ∧ ¬ Nd (i - 1) P then h.choose else 0

lemma idx_eq (hR : Red γ P) (hγ : IsUnit γ) (hX : ∃ j, (X j : RN) ∉ P) {i : ZMod N}
    (hA : NGon.A i P) (hn : ¬ Nd (i - 1) P) : idx P = i := by
  have h : ∃ i, NGon.A i P ∧ ¬ Nd (i - 1) P := ⟨i, hA, hn⟩
  rw [idx, dif_pos h]
  obtain ⟨hA', hn'⟩ := h.choose_spec
  by_contra hne
  rcases memA_memA hR hγ hX hne hA' hA with ⟨e, hd⟩ | ⟨e, hd⟩
  · exact hn (by rw [e, add_sub_cancel_right]; exact hd)
  · exact hn' (by rw [e, add_sub_cancel_right]; exact hd)

lemma exists_A (hR : Red γ P) (hγ : IsUnit γ) (hN : 3 ≤ N) (hX : ∃ j, (X j : RN) ∉ P) :
    ∃ i, NGon.A i P ∧ ¬ Nd (i - 1) P := by
  obtain ⟨i, hi⟩ := mem_pieces hR hγ hN hX
  by_cases hn : Nd (i - 1) P
  · refine ⟨i - 1, (Nd_A hN hn).1, fun h' => ?_⟩
    have hne : i - 1 - 1 ≠ i - 1 := fun e => by
      haveI : Fact (1 < N) := ⟨by omega⟩
      exact one_ne_zero (by linear_combination -e : (1 : ZMod N) = 0)
    exact Nd_disjoint hX hne h' hn
  · exact ⟨i, hi, hn⟩

lemma idx_spec (hR : Red γ P) (hγ : IsUnit γ) (hN : 3 ≤ N) (hX : ∃ j, (X j : RN) ∉ P) :
    NGon.A (idx P) P ∧ ¬ Nd (idx P - 1) P := by
  obtain ⟨i, hA, hn⟩ := exists_A hR hγ hN hX
  rw [idx_eq hR hγ hX hA hn]
  exact ⟨hA, hn⟩

lemma idx_L (hR : Red γ P) (hγ : IsUnit γ) (hN : 3 ≤ N) (hX : ∃ j, (X j : RN) ∉ P)
    {i : ZMod N} (hL : L i P) : idx P = i := by
  refine idx_eq hR hγ hX (Or.inl hL) fun hn => all_false hX (fun k => ?_) hL.1
  by_cases hk : k = i
  · subst hk
    have hne : k ≠ k - 1 := fun e => by
      haveI : Fact (1 < N) := ⟨by omega⟩
      exact one_ne_zero (by linear_combination e : (1 : ZMod N) = 0)
    exact hn.2.1 k hne
  · exact hL.2 k hk

lemma idx_Nd (hR : Red γ P) (hγ : IsUnit γ) (hN : 3 ≤ N) (hX : ∃ j, (X j : RN) ∉ P)
    {i : ZMod N} (hn : Nd i P) : idx P = i := by
  refine idx_eq hR hγ hX (Nd_A hN hn).1 fun h' => ?_
  have hne : i - 1 ≠ i := fun e => by
    haveI : Fact (1 < N) := ⟨by omega⟩
    exact one_ne_zero (by linear_combination -e : (1 : ZMod N) = 0)
  exact Nd_disjoint hX hne h' hn

lemma idx_G (hR : Red γ P) (hγ : IsUnit γ) (hX : ∃ j, (X j : RN) ∉ P)
    {i : ZMod N} (hG : G i P) (hw : ww O N ∉ P) : idx P = i :=
  idx_eq hR hγ hX (Or.inr hG) fun hn => hw hn.1

end Pieces

/-- The label `i.val − N [i ≠ 0]` of the piece `A_i`. -/
def lab (i : ZMod N) : ℤ := i.val - N * (if i = 0 then 0 else 1)

lemma lab_sub_one (hN : 3 ≤ N) {i : ZMod N} (hi : i ≠ 1) : lab (i - 1) = lab i - 1 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hv1 : (1 : ZMod N).val = 1 := ZMod.val_one N
  by_cases h0 : i = 0
  · subst h0
    have h1 : (0 - 1 : ZMod N) ≠ 0 := by rw [zero_sub, neg_ne_zero]; exact one_ne_zero
    have hv : (0 - 1 : ZMod N).val = N - 1 := by
      rw [zero_sub, ZMod.val_neg_of_ne_zero, hv1]
    unfold lab
    rw [if_neg h1, if_pos rfl, hv, ZMod.val_zero]
    push_cast [show 1 ≤ N by omega]
    ring
  · have h1 : i - 1 ≠ 0 := sub_ne_zero.2 hi
    have hpos : 1 ≤ i.val := Nat.one_le_iff_ne_zero.2 fun h => h0 ((ZMod.val_eq_zero i).1 h)
    have hv : (i - 1).val = i.val - 1 := by
      rw [ZMod.val_sub (by rw [hv1]; exact hpos), hv1]
    unfold lab
    rw [if_neg h1, if_neg h0, hv]
    push_cast [hpos]
    ring

lemma lab_cast (i : ZMod N) : ((lab i : ℤ) : ZMod N) = i := by
  simp [lab]

/-- The sheet function `κ = lab ∘ idx` on the special fibre. -/
def κZ (z : (level A I).Z) : ℤ := lab (idx (Pz I z))

open Classical in
/-- The shift of the `2`-gon decomposition pulled back: `0` on `W = 0`, `1` elsewhere. -/
def shiftC (P : Ideal RN) : ℤ := if ww O N ∈ P then 0 else 1

lemma shift_ψs (z : (level A I).Z) :
    (TateObject.decomp (A := A) T).shift (ψs A I z) = shiftC (Pz I z) := by
  unfold shiftC
  split_ifs with h
  · exact TateCovering.Decomp.shift_of_mem _ ((ψs_mem_C I z).2 h)
  · exact TateCovering.Decomp.shift_of_notMem _ fun h' => h ((ψs_mem_C I z).1 h')

lemma ψs_mem_Cq (z : (level A I).Z) :
    ψs A I z ∈ (TateObject.decomp (A := A) T).Cq ↔ ∃ i, Nd i (Pz I z) := by
  change (X 2 : MvPolynomial (Fin (2 + 1)) O) ∈ _ ∧ (X 0 + X 1 : MvPolynomial (Fin (2 + 1)) O) ∈ _
    ↔ _
  rw [X_mem_ψs_iff, mem_ψs_iff I z ((mem_homogeneousSubmodule _ _).2
    ((isHomogeneous_X O 0).add (isHomogeneous_X O 1))) one_pos]
  rw [← nq_iff (redZ I z) (hγ1 I) (hN3 I) (hXZ I z)]
  have e : aeval (ℓψ (N := N) I.ε I.κ) (X 0 + X 1 : MvPolynomial (Fin (2 + 1)) O) =
      ∑ k : ZMod N, xx k + ∑ k : ZMod N, yy k + C (I.κ - I.ε) * ww O N := by
    simp only [map_add, aeval_X, ℓψ, map_sub, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [e]
  exact and_congr_right fun h4 => lin_iff h4 _ _

variable (A) in
/-- The pieces `L_i` and `G_i`. -/
def pieces : ZMod N ⊕ ZMod N → Set (level A I).Z
  | .inl i => {z | L i (Pz I z)}
  | .inr i => {z | G i (Pz I z)}

lemma isClosed_pieces (j : ZMod N ⊕ ZMod N) : IsClosed (pieces A I j) := by
  rcases j with i | i
  exacts [isClosed_L (continuous_ιZ I) i, isClosed_G (continuous_ιZ I) i]

lemma pieces_cover (z : (level A I).Z) : ∃ j, z ∈ pieces A I j := by
  obtain ⟨i, h | h⟩ := mem_pieces (redZ I z) (hγ1 I) (hN3 I) (hXZ I z)
  exacts [⟨.inl i, h⟩, ⟨.inr i, h⟩]

lemma h2Z (v : ℤ) : IsOpen {z | ψs A I z ∉ (TateObject.decomp (A := A) T).Cq ∧ κZ I z = v} := by
  refine isOpen_level_of_pieces (U := {z | ψs A I z ∉ (TateObject.decomp (A := A) T).Cq})
    ((TateObject.decomp (A := A) T).isClosed_Cq.preimage (continuous_ψs I)).isOpen_compl
    (fun i => {z | NGon.A i (Pz I z)}) (fun i => isClosed_A (continuous_ιZ I) i) (fun z _ => ?_)
    (κZ I) lab (fun i z hz hzi => ?_) v
  · obtain ⟨i, h⟩ := mem_pieces (redZ I z) (hγ1 I) (hN3 I) (hXZ I z)
    exact ⟨i, h⟩
  · have hn : ¬ Nd (i - 1) (Pz I z) := fun h => hz ((ψs_mem_Cq I z).2 ⟨_, h⟩)
    change lab (idx (Pz I z)) = lab i
    rw [idx_eq (redZ I z) (hγ1 I) (hXZ I z) hzi hn]

lemma h3Z (v : ℤ) : IsOpen {z | z ∉ (D' A I).Cq ∧ ψs A I z ∉ (TateObject.decomp (A := A) T).Cp ∧
    κZ I z - (TateObject.decomp (A := A) T).shift (ψs A I z) = v} := by
  have := isOpen_level_of_pieces
    (U := {z | z ∉ (D' A I).Cq ∧ ψs A I z ∉ (TateObject.decomp (A := A) T).Cp})
    ((D' A I).isClosed_Cq.isOpen_compl.inter
      ((TateObject.decomp (A := A) T).isClosed_Cp.preimage (continuous_ψs I)).isOpen_compl)
    (pieces A I) (isClosed_pieces I) (fun z _ => pieces_cover I z)
    (fun z => κZ I z - (TateObject.decomp (A := A) T).shift (ψs A I z))
    (fun | .inl i => lab i | .inr i => lab i - 1)
    (fun j z hz hzj => by
      have hq : ¬ Nd 0 (Pz I z) := hz.1
      have hn : ¬ Np (Pz I z) := fun h => hz.2 ((ψs_mem_Cp I z).2 h)
      rw [shift_ψs]
      rcases j with i | i
      · change lab (idx (Pz I z)) - shiftC (Pz I z) = lab i
        rw [idx_L (redZ I z) (hγ1 I) (hN3 I) (hXZ I z) hzj, shiftC, if_pos hzj.1, sub_zero]
      · change lab (idx (Pz I z)) - shiftC (Pz I z) = lab i - 1
        by_cases hw : ww O N ∈ Pz I z
        · have hd := G_w (redZ I z) (hN3 I) hzj hw hn
          have hi : i ≠ 1 := fun e => hq (by rw [e, sub_self] at hd; exact hd)
          rw [idx_Nd (redZ I z) (hγ1 I) (hN3 I) (hXZ I z) hd, shiftC, if_pos hw, sub_zero,
            lab_sub_one (hN3 I) hi]
        · rw [idx_G (redZ I z) (hγ1 I) (hXZ I z) hzj hw, shiftC, if_neg hw]) v
  convert this using 1
  ext z
  simp only [Set.mem_setOf_eq, and_assoc]

open Classical in
lemma shift_D' (z : (level A I).Z) :
    (D' A I).shift z = if NGon.A 0 (Pz I z) then 0 else 1 := rfl

/-- Off `c_{N−1}`, `N shift + κ = idx`. -/
lemma N_shift_add_κ (z : (level A I).Z) (hz : ¬ Nd (-1) (Pz I z)) :
    (N : ℤ) * (D' A I).shift z + κZ I z = (idx (Pz I z)).val := by
  have hs := idx_spec (redZ I z) (hγ1 I) (hN3 I) (hXZ I z)
  rw [shift_D']
  unfold κZ lab
  by_cases h0 : idx (Pz I z) = 0
  · rw [h0] at hs ⊢
    simp [hs.1]
  · have hA0 : ¬ NGon.A 0 (Pz I z) := fun hA0 => by
      rcases memA_memA (redZ I z) (hγ1 I) (hXZ I z) h0 hs.1 hA0 with ⟨e, hd⟩ | ⟨-, hd⟩
      · have he : idx (Pz I z) = -1 := eq_neg_of_add_eq_zero_left e.symm
        rw [he] at hd
        exact hz hd
      · exact h0 (idx_Nd (redZ I z) (hγ1 I) (hN3 I) (hXZ I z) hd)
    simp [hA0, h0]


lemma h4Z (v : ℤ) : IsOpen {z | z ∉ (D' A I).Cp ∧ ψs A I z ∉ (TateObject.decomp (A := A) T).Cp ∧
    (N : ℤ) * (D' A I).shift z + κZ I z - (TateObject.decomp (A := A) T).shift (ψs A I z) = v} := by
  have := isOpen_level_of_pieces
    (U := {z | z ∉ (D' A I).Cp ∧ ψs A I z ∉ (TateObject.decomp (A := A) T).Cp})
    ((D' A I).isClosed_Cp.isOpen_compl.inter
      ((TateObject.decomp (A := A) T).isClosed_Cp.preimage (continuous_ψs I)).isOpen_compl)
    (pieces A I) (isClosed_pieces I) (fun z _ => pieces_cover I z)
    (fun z => (N : ℤ) * (D' A I).shift z + κZ I z -
      (TateObject.decomp (A := A) T).shift (ψs A I z))
    (fun | .inl i => (i.val : ℤ) | .inr i => (i.val : ℤ) - 1)
    (fun j z hz hzj => by
      have hp : ¬ Nd (-1) (Pz I z) := hz.1
      have hn : ¬ Np (Pz I z) := fun h => hz.2 ((ψs_mem_Cp I z).2 h)
      change (N : ℤ) * (D' A I).shift z + κZ I z -
        (TateObject.decomp (A := A) T).shift (ψs A I z) = _
      rw [shift_ψs, N_shift_add_κ I z hp]
      rcases j with i | i
      · change ((idx (Pz I z)).val : ℤ) - shiftC (Pz I z) = i.val
        rw [idx_L (redZ I z) (hγ1 I) (hN3 I) (hXZ I z) hzj, shiftC, if_pos hzj.1, sub_zero]
      · change ((idx (Pz I z)).val : ℤ) - shiftC (Pz I z) = i.val - 1
        by_cases hw : ww O N ∈ Pz I z
        · have hd := G_w (redZ I z) (hN3 I) hzj hw hn
          have hi : i ≠ 0 := fun e => hp (by rw [e, zero_sub] at hd; exact hd)
          rw [idx_Nd (redZ I z) (hγ1 I) (hN3 I) (hXZ I z) hd, shiftC, if_pos hw, sub_zero]
          haveI : Fact (1 < N) := ⟨by have := hN3 I; omega⟩
          have hpos : 1 ≤ i.val := Nat.one_le_iff_ne_zero.2 fun h => hi ((ZMod.val_eq_zero i).1 h)
          rw [ZMod.val_sub (by rw [ZMod.val_one]; exact hpos), ZMod.val_one]
          push_cast [hpos]
          ring
        · rw [idx_G (redZ I z) (hγ1 I) (hXZ I z) hzj hw, shiftC, if_neg hw]) v
  convert this using 1
  ext z
  simp only [Set.mem_setOf_eq, and_assoc]

/-- **The map of `ℤ`-coverings** `(z, n) ↦ (ψ z, N n + κ z + c)`. -/
lemma continuous_mapN_Z (c : ℤ) :
    Continuous (TateCovering.Decomp.mapN (D' A I) (TateObject.decomp (A := A) T) (ψs A I) N
      (κZ I) c) :=
  TateCovering.Decomp.continuous_mapN (continuous_ψs I) _ _ c
    (fun z hz hq => hz ((ψs_mem_Cq I z).2 ⟨0, hq⟩)) (h2Z I) (h3Z I) (h4Z I)

/-! ### The cyclic shift of the blocks -/

/-- The cyclic shift `B_k ↦ B_{k+m}` of the coordinates. -/
def sh (m : ZMod N) (j : Fin (2 * N + 1)) : Fin (2 * N + 1) :=
  if j.val = 2 * N then j
  else if j.val % 2 = 0 then ix (((j.val / 2 : ℕ) : ZMod N) + m)
  else iy (((j.val / 2 : ℕ) : ZMod N) + m)

lemma ix_val (k : ZMod N) : (ix k).val = 2 * k.val := rfl

lemma iy_val (k : ZMod N) : (iy k).val = 2 * k.val + 1 := rfl

@[simp] lemma sh_ix (m k : ZMod N) : sh m (ix k) = ix (k + m) := by
  have := ZMod.val_lt k
  have hk : (((ix k).val / 2 : ℕ) : ZMod N) = k := by
    rw [ix_val, show 2 * k.val / 2 = k.val by omega, ZMod.natCast_zmod_val]
  unfold sh
  rw [if_neg (by rw [ix_val]; omega), if_pos (by rw [ix_val]; omega), hk]

@[simp] lemma sh_iy (m k : ZMod N) : sh m (iy k) = iy (k + m) := by
  have := ZMod.val_lt k
  have hk : (((iy k).val / 2 : ℕ) : ZMod N) = k := by
    rw [iy_val, show (2 * k.val + 1) / 2 = k.val by omega, ZMod.natCast_zmod_val]
  unfold sh
  rw [if_neg (by rw [iy_val]; omega), if_neg (by rw [iy_val]; omega), hk]

@[simp] lemma sh_iw (m : ZMod N) : sh m (iw N) = iw N := by
  unfold sh
  exact if_pos rfl

lemma sh_sh (m : ZMod N) (j : Fin (2 * N + 1)) : sh m (sh (-m) j) = j := by
  rcases idx_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩ | rfl
  · rw [sh_ix, sh_ix, neg_add_cancel_right]
  · rw [sh_iy, sh_iy, neg_add_cancel_right]
  · rw [sh_iw, sh_iw]

/-- The linear forms of the shift. -/
def ℓsh (m : ZMod N) : Fin (2 * N + 1) → RN := fun j => X (sh m j)

lemma ℓsh_mem (m : ZMod N) (j : Fin (2 * N + 1)) :
    ℓsh (O := O) m j ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * N + 1)) O 1 :=
  X_mem' _

lemma hcov_sh (m : ZMod N) (y : projSpace O (2 * N)) :
    ∃ k, (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (2 * N + 1)) O))) y ∈
    SemistableReduction.LinearProjectionN.D (ℓsh (O := O) m) (ℓsh_mem m) k := by
  obtain ⟨i, hi⟩ := exists_X_notMem y
  refine ⟨sh (-m) i, ?_⟩
  change linHom (ℓsh m) (ℓsh_mem m) (X (sh (-m) i)) ∉ y.asHomogeneousIdeal
  rwa [linHom_apply, aeval_X, ℓsh, sh_sh]

variable (O) in
/-- **The shift `ρ_m : ℙ^{2N} ⟶ ℙ^{2N}`.** -/
def ρsh (m : ZMod N) : projSpace O (2 * N) ⟶ projSpace O (2 * N) :=
  proj (ℓsh (O := O) m) (ℓsh_mem m)
    (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (2 * N + 1)) O))) (hcov_sh m)

lemma ρsh_toSpec (m : ZMod N) :
    ρsh O m ≫ projSpace.toSpec O (2 * N) = projSpace.toSpec O (2 * N) :=
  (proj_toSpec _ _ _ _).trans (Category.id_comp _)

lemma mem_ρsh_iff (m : ZMod N) (y : projSpace O (2 * N)) {r : RN} {d : ℕ}
    (hr : r ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * N + 1)) O d) (hd : 0 < d) :
    r ∈ (ρsh O m y).asHomogeneousIdeal ↔ rename (sh m) r ∈ y.asHomogeneousIdeal := by
  have h := mem_proj_iff (ℓ := ℓsh (O := O) m) (hcov_sh m) hr hd y
  have e : aeval (ℓsh (O := O) m) r = rename (sh m) r := by
    rw [rename_eq_aeval]
    rfl
  rw [e] at h
  exact h

lemma ptT_ρsh {Tr : Type u} [CommRing Tr] [Algebra O Tr] (m : ZMod N)
    (c : Fin (2 * N + 1) → Tr) (hc : IsUnit (aeval c (ww O N : RN)))
    (hc' : IsUnit (aeval (c ∘ sh m) (ww O N : RN))) :
    ptT c (ww O N) hc (X_mem' (iw N)) one_pos ≫ ρsh O m =
      ptT (c ∘ sh m) (ww O N) hc' (X_mem' (iw N)) one_pos := by
  have hk : IsUnit (aeval c (linHom (ℓsh (O := O) m) (ℓsh_mem m) (X (iw N)))) := by
    rwa [linHom_apply, aeval_X, ℓsh, sh_iw]
  have hk' : IsUnit (aeval (fun j => aeval c (ℓsh (O := O) m j)) (X (iw N) : RN)) := by
    simpa [ℓsh] using hc
  have h := comp_proj_of_eq_ptT (ℓsh (O := O) m) (ℓsh_mem m) (hcov_sh m)
    (ptT c (ww O N) hc (X_mem' (iw N)) one_pos) c (iw N)
    hk (𝟙 _) ((Category.comp_id _).trans ((ptT_eq c hc hk _ _ one_pos).trans
      (Category.id_comp _).symm)) hk'
  refine h.trans ((Category.id_comp _).trans ?_)
  exact FourGon.ptT_congr_c (funext fun j => by simp [ℓsh]) _ _ _ _ _

section ShiftPrimes

variable {P P' : Ideal RN} (m : ZMod N)
  (hlin : ∀ r : RN, r.IsHomogeneous 1 → (r ∈ P' ↔ rename (sh m) r ∈ P))
include hlin

lemma shX (j : Fin (2 * N + 1)) : (X j : RN) ∈ P' ↔ X (sh m j) ∈ P := by
  rw [hlin _ (isHomogeneous_X _ _), rename_X]

lemma shxy (k : ZMod N) : xx k + yy k ∈ P' ↔ xx (k + m) + yy (k + m) ∈ P := by
  rw [hlin _ ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)), map_add, rename_X, rename_X,
    sh_ix, sh_iy]

lemma shZ0 (k : ZMod N) : Z0 k P' ↔ Z0 (k + m) P := by
  unfold Z0
  rw [shX m hlin, shX m hlin, sh_ix, sh_iy]

lemma shW : ww O N ∈ P' ↔ ww O N ∈ P := by
  rw [shX m hlin, sh_iw]

lemma sh_forall (i : ZMod N) :
    (∀ k, k ≠ i → Z0 k P') ↔ (∀ k, k ≠ i + m → Z0 k P) := by
  constructor
  · intro h k hk
    have := (shZ0 m hlin (k - m)).1 (h (k - m) fun e => hk (by linear_combination e))
    rwa [sub_add_cancel] at this
  · intro h k hk
    exact (shZ0 m hlin k).2 (h (k + m) fun e => hk (add_right_cancel e))

lemma shL (i : ZMod N) : L i P' ↔ L (i + m) P := by
  unfold L
  rw [shW m hlin, sh_forall m hlin]

lemma shG (i : ZMod N) : G i P' ↔ G (i + m) P := by
  unfold G
  have e1 : ∀ k, xx k + yy k ∈ P' ↔ xx (k + m) + yy (k + m) ∈ P := shxy m hlin
  have e2 : yy i ∈ P' ↔ yy (i + m) ∈ P := by rw [shX m hlin, sh_iy]
  rw [e1, e2, show i - 1 + m = i + m - 1 by ring]
  refine and_congr_left fun _ => ⟨fun h k hk1 hk2 => ?_, fun h k hk1 hk2 => ?_⟩
  · have := (shZ0 m hlin (k - m)).1 (h (k - m) (fun e => hk1 (by linear_combination e))
      (fun e => hk2 (by linear_combination e)))
    rwa [sub_add_cancel] at this
  · exact (shZ0 m hlin k).2 (h (k + m) (fun e => hk1 (by linear_combination e))
      (fun e => hk2 (by linear_combination e)))

lemma shA (i : ZMod N) : NGon.A i P' ↔ NGon.A (i + m) P := by
  unfold A
  rw [shL m hlin, shG m hlin]

lemma shNd (i : ZMod N) : Nd i P' ↔ Nd (i + m) P := by
  unfold Nd
  rw [shW m hlin, sh_forall m hlin, shxy m hlin]

end ShiftPrimes

lemma idx_sh {P P' : Ideal RN} [P.IsPrime] [P'.IsPrime] (m : ZMod N)
    (hlin : ∀ r : RN, r.IsHomogeneous 1 → (r ∈ P' ↔ rename (sh m) r ∈ P)) {γ : O}
    (hR : Red γ P) (hR' : Red γ P') (hγ : IsUnit γ) (hN : 3 ≤ N) (hX : ∃ j, (X j : RN) ∉ P)
    (hX' : ∃ j, (X j : RN) ∉ P') : idx P' = idx P - m := by
  obtain ⟨hA, hn⟩ := idx_spec hR hγ hN hX
  refine idx_eq hR' hγ hX' ((shA m hlin _).2 (by rwa [sub_add_cancel])) fun h => hn ?_
  have := (shNd m hlin _).1 h
  rwa [show idx P - m - 1 + m = idx P - 1 by ring] at this

/-! ### The object `Z` and the morphisms to `X₀` and to the cover -/

variable (A) in
/-- **The object `Z`**: the `ℤ`-covering of the `2N`-gon over the level `(R', 1)`. -/
def Zobj : TempObj O R A where
  Lv := level A I
  P := (D' A I).toCode _ (level_ρs I)

lemma aeval_gB_ℓψ : (fun j => aeval (gB A I) (ℓψ (N := N) I.ε I.κ j)) =
    ![algebraMap R (FourGon.Bc R A R') T.x, algebraMap R (FourGon.Bc R A R') T.y,
      algebraMap O (FourGon.Bc R A R') T.π] := by
  have h := aeval_ℓψ I
  funext j
  rw [aeval_gB]
  have hj := congrFun h j
  rw [hj]
  fin_cases j
  · exact (AlgEquiv.commutes _ _)
  · exact (AlgEquiv.commutes _ _)
  · exact (FourGon.eB O R A).commutes T.π

lemma jm_ψ :
    jm A I ≫ ψ (D := co I) (goodI I) =
      Spec.map (CommRingCat.ofHom ((FourGon.levelToUnit (R := R) (R' := R') A).f :
        (TateObject.unitLevel R A).B →+* (FourGon.Bc R A R'))) ≫
        TateModel.toModel T.π T.b₄ T.b₆ (levelStructureMap O R A (TateObject.unitLevel R A))
          (T.equation_B (A := A)) (T.isUnit_π (A := A)) := by
  have hψι : ψ (D := co I) (goodI I) ≫ TateModel.ι T.π T.b₄ T.b₆ = ψ₀ (D := co I) (goodI I) :=
    ψ_ι (goodI I)
  refine (cancel_mono (TateModel.ι T.π T.b₄ T.b₆)).1 ?_
  refine (Category.assoc _ _ _).trans ((congrArg (jm A I ≫ ·) hψι).trans ?_)
  rw [Category.assoc, TateModel.toModel_ι, TateModel.SpecMap_toProj]
  swap
  · exact (T.isUnit_π (A := A)).map ((FourGon.levelToUnit (R := R) (R' := R') A).f :
      (TateObject.unitLevel R A).B →+* FourGon.Bc R A R')
  have hk : IsUnit (aeval (gB A I) (linHom (ℓψ (N := N) I.ε I.κ) (ℓψ_mem I.ε I.κ) (X 2))) := by
    rw [linHom_apply, aeval_X]
    exact isUnit_gBw I
  have hk' : IsUnit (aeval (fun j => aeval (gB A I) (ℓψ (N := N) I.ε I.κ j))
      (X 2 : MvPolynomial (Fin (2 + 1)) O)) := by
    rw [aeval_X]
    exact isUnit_gBw I
  have h := comp_proj_of_eq_ptT (ℓψ (N := N) I.ε I.κ) (ℓψ_mem I.ε I.κ)
    (hcov (D := co I) (goodI I)) (jm A I) (gB A I) 2 hk (𝟙 _)
    ((jm_ιm I).trans ((ptT_eq (gB A I) (isUnit_gBw I) hk (X_mem' (iw N)) _ one_pos).trans
      (Category.id_comp _).symm)) hk'
  refine h.trans ((Category.id_comp _).trans ?_)
  have hπ : IsUnit (algebraMap O (FourGon.Bc R A R') T.π) := by
    rw [← (FourGon.eB O R A).commutes T.π]
    exact (FourGon.isUnit_π_R' (T := T) (R' := R')).map _
  have e1 : ((FourGon.levelToUnit (R := R) (R' := R') A).f :
      (TateObject.unitLevel R A).B →+* FourGon.Bc R A R').comp
      (levelStructureMap O R A (TateObject.unitLevel R A)) = algebraMap O (FourGon.Bc R A R') :=
    RingHom.ext fun o => FourGon.levelStructureMap_unit (A := A) (R := R) (R' := R') o
  have e2 : (FourGon.levelToUnit A).f (algebraMap R (TateObject.unitLevel R A).B T.x) =
      algebraMap R (FourGon.Bc R A R') T.x := AlgHom.commutes _ _
  have e3 : (FourGon.levelToUnit A).f (algebraMap R (TateObject.unitLevel R A).B T.y) =
      algebraMap R (FourGon.Bc R A R') T.y := AlgHom.commutes _ _
  have key : ∀ (φ : O →+* FourGon.Bc R A R') (x y : FourGon.Bc R A R')
      (hφ : φ = algebraMap O _)
      (hx : x = algebraMap R (FourGon.Bc R A R') T.x)
      (hy : y = algebraMap R (FourGon.Bc R A R') T.y) hπ',
      TateModel.toProj T.π φ x y hπ' = ptT (fun j => aeval (gB A I) (ℓψ (N := N) I.ε I.κ j))
        (X 2) hk' (X_mem' 2) one_pos := by
    rintro _ _ _ rfl rfl rfl hπ'
    rw [FourGon.toProj_eq_ptT T.π _ _ hπ (by rw [aeval_X]; exact hπ)]
    exact FourGon.ptT_congr_c (aeval_gB_ℓψ I).symm _ _ _ _ _
  exact (key _ _ _ e1 e2 e3 (by rw [e1]; exact hπ)).symm

variable (A) in
/-- The coded map of coverings `(z, n) ↦ (ψ z, N n + κ z + c)`. -/
def hA (c : ℤ) : (Zobj A I).P.carrier → (TateObject.X₀ (A := A) T).P.carrier := fun x =>
  (TateObject.decomp (A := A) T).codeEquiv.symm
    (TateCovering.Decomp.mapN (D' A I) (TateObject.decomp (A := A) T) (ψs A I) N (κZ I) c
      ((D' A I).codeEquiv x))

lemma continuous_hA (c : ℤ) : Continuous (hA A I c) := by
  letI := (D' A I).codeTop
  letI := (TateObject.decomp (A := A) T).codeTop
  exact (TateObject.decomp (A := A) T).codeHomeomorph.symm.continuous.comp
    ((continuous_mapN_Z I c).comp (D' A I).codeHomeomorph.continuous)

variable (A) in
/-- **The morphism `a : Z ⟶ X₀`.** -/
def aHom (c : ℤ) : Zobj A I ⟶ TateObject.X₀ (A := A) T where
  φ := FourGon.levelToUnit A
  ψ := ψ (D := co I) (goodI I)
  ψ_toSpec := ψ_toSpec (D := co I) (goodI I)
  j_ψ := jm_ψ I
  h := hA A I c
  continuous_h := continuous_hA I c
  fst_h _ := rfl
  h_act g x := by
    rw [FourGon.coverH_eq_one g]
    rfl

/-- The model map to the trivial model. -/
abbrev ψb : (model (co I)).scheme ⟶ (ModelCode.trivial O).scheme :=
  (model (co I)).toSpec ≫ inv (ModelCode.trivial O).toSpec

lemma ψb_toSpec : ψb I ≫ (ModelCode.trivial O).toSpec = (model (co I)).toSpec := by
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
    rw [FourGon.coverH_eq_one g]
    exact (TempObj.coverObj_act_one _).symm

/-! ### Fibres -/

section Fibre

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

attribute [local instance] FourGon.algΩ

lemma point_ιm (t : FourGon.Bc R A R' →ₐ[R] Ω)
    (hu : IsUnit (aeval (fun i => t (gB A I i)) (ww O N : RN))) :
    (level A I).point t ≫ ιm (co I) =
      ptT (fun i => t (gB A I i)) (ww O N) hu (X_mem' (iw N)) one_pos := by
  rw [Level.point, Category.assoc]
  change _ ≫ jm A I ≫ _ = _
  rw [jm_ιm, j0]
  exact SpecMap_ptT (FourGon.tO t) (gB A I) (ww O N) _ hu _ _

lemma isUnit_tgBw (t : FourGon.Bc R A R' →ₐ[R] Ω) :
    IsUnit (aeval (fun i => t (gB A I i)) (ww O N : RN)) := by
  rw [aeval_X]
  have := isUnit_gBw (A := A) I
  rw [aeval_X] at this
  exact this.map t

/-- **The deck shift shifts the specialisations.** -/
lemma sp_shift (m : ZMod N) (t t' : FourGon.Bc R A R' →ₐ[R] Ω)
    (h : ∀ i, t' (gB A I i) = t (gB A I (sh m i))) :
    ιZ I ((level A I).sp V hV t') = ρsh O m (ιZ I ((level A I).sp V hV t)) := by
  have hpt : (level A I).point t' ≫ ιm (co I) =
      ((level A I).point t ≫ ιm (co I)) ≫ ρsh O m := by
    rw [point_ιm I t' (isUnit_tgBw I t'), point_ιm I t (isUnit_tgBw I t)]
    refine Eq.trans ?_ (ptT_ρsh m _ (isUnit_tgBw I t) ?_).symm
    · exact FourGon.ptT_congr_c (funext h) _ _ _ _ _
    · simpa using isUnit_tgBw (A := A) I t
  have e1 := coe_sp_comp (hV := hV) (f := (level A I).c.toSpec)
    (f' := projSpace.toSpec O (2 * N)) (ιm (co I)) rfl ((level A I).point t')
    ((level A I).point_toSpec t')
  have e2 := coe_sp_comp (hV := hV) (f := (level A I).c.toSpec)
    (f' := projSpace.toSpec O (2 * N)) (ιm (co I)) rfl ((level A I).point t)
    ((level A I).point_toSpec t)
  have e3 := coe_sp_comp (hV := hV) (f := projSpace.toSpec O (2 * N))
    (f' := projSpace.toSpec O (2 * N)) (ρsh O m) (ρsh_toSpec m)
    ((level A I).point t ≫ ιm (co I))
    (by rw [Category.assoc]; exact (level A I).point_toSpec t)
  refine e1.symm.trans (Eq.trans ?_ (e3.trans (congrArg (ρsh O m) e2)))
  exact congrArg Subtype.val (FourGon.sp_eq_of_eq V hV hpt _ _)

lemma idx_spZ (m : ZMod N) (t t' : FourGon.Bc R A R' →ₐ[R] Ω)
    (h : ∀ i, t' (gB A I i) = t (gB A I (sh m i))) :
    idx (Pz I ((level A I).sp V hV t')) = idx (Pz I ((level A I).sp V hV t)) - m := by
  set z := (level A I).sp V hV t
  set z' := (level A I).sp V hV t'
  refine idx_sh m (fun r hr => ?_) (redZ I z) (redZ I z') (hγ1 I) (hN3 I) (hXZ I z) (hXZ I z')
  change r ∈ (ιZ I z').asHomogeneousIdeal ↔ _
  rw [sp_shift I V hV m t t' h, mem_ρsh_iff _ _ ((mem_homogeneousSubmodule _ _).2 hr) one_pos]
  rfl

variable (R A R' Ω) in
/-- The base point of the cover. -/
abbrev t₀ : FourGon.Bc R A R' →ₐ[R] Ω := coverPt R A R' Ω

variable (A) in
/-- The constant normalising the labels at the base point. -/
def c₀ : ℤ := -κZ I ((level A I).sp V hV (t₀ R A R' Ω))

variable (A) in
/-- **The base point of `Z`.** -/
def z₀ : (tempFibre O R A V hV).obj (Zobj A I) :=
  Quotient.mk _ ⟨(t₀ R A R' Ω, (D' A I).codeEquiv.symm ⟨(level A I).sp V hV (t₀ R A R' Ω), 0⟩),
    rfl⟩

lemma map_aHom_z₀ :
    (tempFibre O R A V hV).map (aHom A I (c₀ A I V hV)) (z₀ A I V hV) =
      TateObject.basePoint (A := A) T V hV := by
  change Quotient.mk _ (TempObj.preMap V hV (aHom A I (c₀ A I V hV)) _) = Quotient.mk _ _
  congr 1
  apply Subtype.ext
  refine Prod.ext ((TateObject.subsingleton_fibre (A := A)).elim _ _) ?_
  change hA A I (c₀ A I V hV) _ = _
  simp only [hA, Equiv.apply_symm_apply, TateCovering.Decomp.mapN, c₀, mul_zero, zero_add,
    add_neg_cancel]
  have hψ := TempObj.ψ_sp V hV (aHom A I (c₀ A I V hV)) (t₀ R A R' Ω)
  have ht : (t₀ R A R' Ω).comp (aHom A I (c₀ A I V hV)).φ.f =
      (Algebra.ofId R Ω).comp (TateObject.unitEquiv R).toAlgHom :=
    (TateObject.subsingleton_fibre (A := A)).elim _ _
  apply Subtype.ext
  refine Prod.ext (Subtype.ext (hψ.trans ?_)) FourGon.intEquivNat_zero
  exact congrArg (fun t => ((TateObject.X₀ (A := A) T).Lv.sp V hV t :
    (TateObject.X₀ (A := A) T).Lv.c.scheme)) ht

lemma map_bHom_z₀ :
    (tempFibre O R A V hV).map (bHom A I) (z₀ A I V hV) = coverFibrePt V hV := by
  apply (etaleToTempFibreEquiv O R A V hV (coverEt R A R')).injective
  rw [coverFibrePt, Equiv.apply_symm_apply]
  rfl

lemma gB_sh (τ τ' : FourGon.Bc R A R' →ₐ[R] Ω) (m : ZMod N)
    (hx : ∀ k, τ' (gB A I (ix k)) = τ (gB A I (ix (k + m))))
    (hy : ∀ k, τ' (gB A I (iy k)) = τ (gB A I (iy (k + m)))) :
    ∀ j, τ' (gB A I j) = τ (gB A I (sh m j)) := fun j => by
  rcases idx_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩ | rfl
  · rw [sh_ix]; exact hx k
  · rw [sh_iy]; exact hy k
  · rw [sh_iw]
    have e : gB A I (iw N) = algebraMap R (FourGon.Bc R A R') (algebraMap K R (T.π : K)) := by
      change FourGon.eB O R A (gR I (iw N)) = _
      rw [gR_iw]
      exact (FourGon.eB O R A).commutes T.π
    rw [e]
    exact (τ'.commutes _).trans (τ.commutes _).symm

/-- **`a` is injective on fibres** when two `R`-points of `R'` over a geometric point differ by a
cyclic shift of the blocks. -/
theorem injective_aHom (c : ℤ)
    (hfib : ∀ τ τ' : R' →ₐ[R] Ω, τ' = τ ∨ ∃ m : ZMod N, m ≠ 0 ∧
      ∀ k, τ' (I.x k) = τ (I.x (k + m)) ∧ τ' (I.y k) = τ (I.y (k + m))) :
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
  set y := (D' A I).codeEquiv q.1.2 with hy
  set y' := (D' A I).codeEquiv q'.1.2 with hy'
  have hpt : y.pt = (level A I).sp V hV q.1.1 := Subtype.ext q.2
  have hpt' : y'.pt = (level A I).sp V hV q'.1.1 := Subtype.ext q'.2
  have hn : (N : ℤ) * y'.n + κZ I y'.pt + c = N * y.n + κZ I y.pt + c :=
    congrArg TateCovering.Decomp.Space.n h3
  let τ : R' →ₐ[R] Ω := q.1.1.comp (coverE R A R').symm.toAlgHom
  let τ' : R' →ₐ[R] Ω := q'.1.1.comp (coverE R A R').symm.toAlgHom
  rcases hfib τ τ' with he | ⟨m, hm, hsh⟩
  · have ht : q'.1.1 = q.1.1 := by
      ext b
      have := congrArg (fun φ : R' →ₐ[R] Ω => φ (coverE R A R' b)) he
      change q'.1.1 ((coverE R A R').symm (coverE R A R' b)) =
        q.1.1 ((coverE R A R').symm (coverE R A R' b)) at this
      rwa [AlgEquiv.symm_apply_apply] at this
    have hyy : y' = y := by
      have hp : y'.pt = y.pt := by rw [hpt, hpt', ht]
      refine TateCovering.Decomp.Space.ext hp ?_
      rw [hp] at hn
      have hN0 : (N : ℤ) ≠ 0 := by have := NeZero.ne N; exact_mod_cast this
      exact mul_left_cancel₀ hN0 (by linarith)
    have : q'.1.2 = q.1.2 := (D' A I).codeEquiv.injective hyy
    exact (congrArg (Quotient.mk _) (Subtype.ext (Prod.ext ht this))).symm
  · exfalso
    have hs := gB_sh I q.1.1 q'.1.1 m (fun k => by simp only [gB, gR_ix]; exact (hsh k).1)
      (fun k => by simp only [gB, gR_iy]; exact (hsh k).2)
    have hi := idx_spZ I V hV m q.1.1 q'.1.1 hs
    rw [← hpt, ← hpt'] at hi
    have hc := congrArg (fun n : ℤ => (n : ZMod N)) hn
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
      zero_add, κZ, lab_cast] at hc
    have hc' : idx (Pz I y'.pt) = idx (Pz I y.pt) := add_right_cancel hc
    rw [hi] at hc'
    exact hm (by simpa using hc')

/-- **The object of `piY_le_range_of_hom`**: an object `Z` with morphisms to `X₀` (injective on
fibres) and to the cover `Spec R' → Spec R`, and a point over both base points. -/
theorem exists_object
    (hfib : ∀ τ τ' : R' →ₐ[R] Ω, τ' = τ ∨ ∃ m : ZMod N, m ≠ 0 ∧
      ∀ k, τ' (I.x k) = τ (I.x (k + m)) ∧ τ' (I.y k) = τ (I.y (k + m))) :
    ∃ (Z : TempObj O R A) (a : Z ⟶ TateObject.X₀ (A := A) T) (b : Z ⟶ coverObj O R A R')
      (z₀ : (tempFibre O R A V hV).obj Z),
      (tempFibre O R A V hV).map a z₀ = TateObject.basePoint (A := A) T V hV ∧
      (tempFibre O R A V hV).map b z₀ = coverFibrePt V hV ∧
      Function.Injective ((tempFibre O R A V hV).map a) :=
  ⟨Zobj A I, aHom A I (c₀ A I V hV), bHom A I, z₀ A I V hV, map_aHom_z₀ I V hV,
    map_bHom_z₀ I V hV, injective_aHom I V hV _ hfib⟩

end Fibre

end

end NGon

end TemperedFundamentalGroups
