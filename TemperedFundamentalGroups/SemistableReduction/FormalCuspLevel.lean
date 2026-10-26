/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalLevelCompat
import TemperedFundamentalGroups.SemistableReduction.FormalCuspNode
import TemperedFundamentalGroups.SemistableReduction.FormalCuspEtale

/-!
# The formal cusp form at a marked point at every level (MR12 T2 S6, step G2c)

Let `R` be a chart (an `O`-algebra) with the coordinate `s` at the marked points, `B` an
`R`-algebra (the normalisation of the chart in a cover), and `D` a local formal cusp form of the
special fibre at a marked point `𝔪` (`FormalKummer.PointCuspFormData`:
`Ψ : R̄^_𝔪 ⊗_{R̄} C ≅ ∏ᵢ R̄^_𝔪[y]/(y^{dᵢ} − s̄)`). For an `R`-algebra `T'` with a reduction map
`red : T' → R̄^_𝔪` (e.g. the completion of a level `R/ϖᵏ⁺¹R` at a point over `𝔪`, with
`FormalLevel.redHat`), a **level form** of `D` (`FormalCuspLevel.LevelPointForm`) is an isomorphism

  `T' ⊗_R B ≃ₐ[T'] ∏ᵢ T'[y]/(y^{dᵢ} − s)`

whose reduction along `red` (`adjMap`) is `Ψ` on the elements `1 ⊗ b`.

* **`FormalCuspLevel.levelCuspForm`**: at the cusp, where `D` comes from the chosen étale-local
  Kummer data `CN : FormalKummer.CuspNormAtData` (`pointCuspFormDataOf`), the level form is the base
  change of the splitting `CN.Φ` along the canonical map `FormalLevel.hatLift r : N₁ → T'`;
  `levelCuspForm_compat`: its reduction is `Ψ` as soon as `red ∘ hatLift r` is the special-fibre
  map `hatCₐ` (true for `FormalLevel.redHat`, by uniqueness of formally étale lifts,
  `redHat_hatLift_cusp`).
* `kpolyTensorEquivO`: `T ⊗_{O[X]} O[y] ≅ T[y]/(y^d − X)` (`X ↦ y^d`), the `O`-version of
  `FormalKummer.kpolyTensorEquiv`; `adjMap`: the map of `S[y]/(yⁿ − a)` induced by `g : S → S'`.
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

namespace FormalCuspLevel

noncomputable section

/-! ### Maps of `S[y]/(yⁿ − a)` -/

section AdjMap

variable {S S' S'' : Type*} [CommRing S] [CommRing S'] [CommRing S'']

/-- The map `S[y]/(yⁿ − a) → S'[y]/(yⁿ − b)` induced by `g : S → S'` with `g a = b`. -/
def adjMap (g : S →+* S') (n : ℕ) {a : S} {b : S'} (hab : g a = b) :
    AdjoinRoot (X ^ n - C a) →+* AdjoinRoot (X ^ n - C b) :=
  Ideal.quotientMap _ (mapRingHom g) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
      coe_mapRingHom, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, hab]
    exact Ideal.mem_span_singleton_self _)

lemma adjMap_mk (g : S →+* S') (n : ℕ) {a : S} {b : S'} (hab : g a = b) (p : S[X]) :
    adjMap g n hab (AdjoinRoot.mk _ p) = AdjoinRoot.mk _ (p.map g) :=
  Ideal.quotientMap_mk

lemma adjMap_of (g : S →+* S') (n : ℕ) {a : S} {b : S'} (hab : g a = b) (x : S) :
    adjMap g n hab (AdjoinRoot.of _ x) = AdjoinRoot.of _ (g x) := by
  change adjMap g n hab (AdjoinRoot.mk _ (C x)) = AdjoinRoot.mk _ (C (g x))
  rw [adjMap_mk, Polynomial.map_C]

lemma adjMap_root (g : S →+* S') (n : ℕ) {a : S} {b : S'} (hab : g a = b) :
    adjMap g n hab (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  change adjMap g n hab (AdjoinRoot.mk _ X) = AdjoinRoot.mk _ X
  rw [adjMap_mk, Polynomial.map_X]

lemma adjMap_adjMap (g : S →+* S') (g' : S' →+* S'') (n : ℕ) {a : S} {b : S'} {c : S''}
    (hab : g a = b) (hbc : g' b = c) (z : AdjoinRoot (X ^ n - C a)) :
    adjMap g' n hbc (adjMap g n hab z) =
      adjMap (g'.comp g) n (by rw [RingHom.comp_apply, hab, hbc]) z := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [adjMap_mk, adjMap_mk, adjMap_mk, Polynomial.map_map]

lemma adjMap_congr {g₁ g₂ : S →+* S'} (h : g₁ = g₂) (n : ℕ) {a : S} {b : S'}
    (h₁ : g₁ a = b) (h₂ : g₂ a = b) : adjMap g₁ n h₁ = adjMap g₂ n h₂ := by
  subst h; rfl

lemma adjoinPowEquiv_eq (e : S ≃+* S') (n : ℕ) {a : S} {b : S'} (hab : e a = b)
    (z : AdjoinRoot (X ^ n - C a)) :
    FormalKummer.adjoinPowEquiv e n hab z = adjMap (e : S →+* S') n hab z := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [adjMap_mk]
  exact Ideal.quotientEquiv_mk _ _ _ _ p

lemma adjoinPowEquiv_symm_eq (e : S ≃+* S') (n : ℕ) {a : S} {b : S'} (hab : e a = b)
    (z : AdjoinRoot (X ^ n - C b)) :
    (FormalKummer.adjoinPowEquiv e n hab).symm z =
      adjMap (e.symm : S' →+* S) n (by rw [← hab]; exact e.symm_apply_apply a) z := by
  rw [RingEquiv.symm_apply_eq, adjoinPowEquiv_eq, adjMap_adjMap]
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [adjMap_mk, show ((e : S →+* S').comp (e.symm : S' →+* S)) = RingHom.id S' from
    RingHom.ext fun x ↦ e.apply_symm_apply x, Polynomial.map_id]

lemma adjoinPowCongr_eq {T : Type*} [CommRing T] (n : ℕ) {a b : T} (h : a = b)
    (z : AdjoinRoot (X ^ n - C a)) :
    FormalKummer.adjoinPowCongr n h z = adjMap (RingHom.id T) n h z :=
  adjoinPowEquiv_eq (RingEquiv.refl T) n h z

end AdjMap

/-! ### `T ⊗_{O[X]} O[y] ≅ T[y]/(y^d − X)` -/

section KPolyTensor

open Cusp

variable {O : Type u} [CommRing O] {T : Type u} [CommRing T] [Algebra O[X] T] {d : ℕ}

local notation "τ" => algebraMap O[X] T X

local notation "AR" => AdjoinRoot (X ^ d - C τ)

/-- `O[y] → T[y]/(y^d − X)`, `y ↦ y`. -/
def kpolyToARO : KPoly O d →+* AR :=
  eval₂RingHom ((algebraMap T AR).comp ((algebraMap O[X] T).comp C)) (AdjoinRoot.root _)

omit [Algebra O[X] T] in
lemma root_powO [Algebra O[X] T] :
    (AdjoinRoot.root (X ^ d - C τ)) ^ d = algebraMap T AR τ := by
  have h := AdjoinRoot.eval₂_root (X ^ d - C τ)
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  rw [sub_eq_zero] at h
  exact h

/-- `kpolyToARO` as an `O[X]`-algebra map. -/
def kpolyToAROₐ : KPoly O d →ₐ[O[X]] AR :=
  { kpolyToARO with
    commutes' := fun p ↦ by
      change eval₂ ((algebraMap T AR).comp ((algebraMap O[X] T).comp C))
        (AdjoinRoot.root _) (expand O d p) = algebraMap O[X] AR p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add, eval₂_add, hp, hq, map_add]
      | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, expand_C, expand_X, eval₂_mul,
          eval₂_C, eval₂_pow, eval₂_X_pow, root_powO, map_mul, map_pow]
        simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply] }

lemma one_tmul_Y_powO : ((1 : T) ⊗ₜ[O[X]] (KPoly.Y : KPoly O d)) ^ d =
    algebraMap T (T ⊗[O[X]] KPoly O d) τ := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, KPoly.Y_pow, Algebra.algebraMap_eq_smul_one,
    ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  rfl

/-- `T[y]/(y^d − X) → T ⊗_{O[X]} O[y]`, `y ↦ 1 ⊗ y`. -/
def arToTensorO : AR →ₐ[T] T ⊗[O[X]] KPoly O d :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId T _) ((1 : T) ⊗ₜ KPoly.Y) (by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [one_tmul_Y_powO]
    exact sub_self _)

lemma arToTensorO_root : arToTensorO (AdjoinRoot.root (X ^ d - C τ)) =
    (1 : T) ⊗ₜ[O[X]] (KPoly.Y : KPoly O d) := AdjoinRoot.liftAlgHom_root ..

omit [Algebra O[X] T] in
lemma kpolyO_algebraMap_C (c : O) :
    algebraMap O[X] (KPoly O d) (C c) = algebraMap O (KPoly O d) c := by
  rw [KPoly.algebraMap_eq, expand_C]
  change C c = algebraMap O O[X] c
  rw [Polynomial.algebraMap_eq]

lemma arToTensorO_kpoly (b : KPoly O d) :
    arToTensorO (kpolyToARO b) = (1 : T) ⊗ₜ[O[X]] b := by
  have h : (arToTensorO (T := T) (d := d)).toRingHom.comp kpolyToARO =
      (Algebra.TensorProduct.includeRight (R := O[X]) (A := T)
        (B := KPoly O d)).toRingHom := by
    refine @Polynomial.ringHom_ext O _ _ _ _ _ (fun c ↦ ?_) ?_
    · change arToTensorO (eval₂ ((algebraMap T AR).comp ((algebraMap O[X] T).comp C))
        (AdjoinRoot.root _) (C c)) = (1 : T) ⊗ₜ[O[X]] (algebraMap O (KPoly O d) c)
      rw [eval₂_C, RingHom.comp_apply, RingHom.comp_apply, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one (R := O[X]) (A := T), Algebra.algebraMap_self,
        RingHom.id_apply, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
        kpolyO_algebraMap_C]
    · change arToTensorO (eval₂ ((algebraMap T AR).comp ((algebraMap O[X] T).comp C))
        (AdjoinRoot.root _) X) = (1 : T) ⊗ₜ[O[X]] (KPoly.Y : KPoly O d)
      rw [eval₂_X, arToTensorO_root]
  exact RingHom.congr_fun h b

/-- **`T ⊗_{O[X]} O[y] ≅ T[y]/(y^d − X)`** (`X ↦ y^d`). -/
def kpolyTensorEquivO : T ⊗[O[X]] KPoly O d ≃ₐ[T] AR :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId T AR) kpolyToAROₐ fun _ _ ↦ Commute.all _ _)
    arToTensorO
    (AdjoinRoot.algHom_ext (by
      simp only [AlgHom.coe_comp, Function.comp_apply, arToTensorO_root, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact Polynomial.eval₂_X _ _))
    (Algebra.TensorProduct.ext' fun a b ↦ by
      simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.lift_tmul,
        map_mul, AlgHom.coe_id, id_eq]
      change arToTensorO (algebraMap T AR a) * arToTensorO (kpolyToARO b) = _
      rw [AlgHom.commutes, arToTensorO_kpoly, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl)

lemma kpolyTensorEquivO_tmul (a : T) (b : KPoly O d) :
    kpolyTensorEquivO (a ⊗ₜ[O[X]] b) = AdjoinRoot.of _ a * kpolyToARO b := by
  simp only [kpolyTensorEquivO, AlgEquiv.ofAlgHom_apply, Algebra.TensorProduct.lift_tmul]
  rfl

end KPolyTensor

lemma kpolyTensorEquiv_tmul {k : Type u} [Field k] {T : Type u} [CommRing T] [Algebra k[X] T]
    {d : ℕ} (a : T) (b : Cusp.KPoly k d) :
    FormalKummer.kpolyTensorEquiv (a ⊗ₜ[k[X]] b) =
      AdjoinRoot.of _ a * FormalKummer.kpolyToAR b := by
  simp only [FormalKummer.kpolyTensorEquiv, AlgEquiv.ofAlgHom_apply,
    Algebra.TensorProduct.lift_tmul]
  rfl


/-! ### The special-fibre form at the cusp from chosen étale-local data -/

section CuspOf

open FormalKummer AdmissibleLift Cusp

attribute [local instance] algRN

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]

/-- The `O`-algebra structure of the étale neighbourhood of `CuspNormAtData` (through `R`). -/
abbrev cuspAlgO {s : R} {e : ℕ} {𝔪 : Ideal R} (D : CuspNormAtData O B s e 𝔪) :
    Algebra O D.N₁ :=
  ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra

attribute [local instance] cuspAlgO CuspNormAtData.polyAlg

instance cuspTowerOR {s : R} {e : ℕ} {𝔪 : Ideal R} (D : CuspNormAtData O B s e 𝔪) :
    IsScalarTower O R D.N₁ :=
  IsScalarTower.of_algebraMap_eq' rfl

instance cuspTowerOX {s : R} {e : ℕ} {𝔪 : Ideal R} (D : CuspNormAtData O B s e 𝔪) :
    IsScalarTower O O[X] D.N₁ :=
  D.tower

variable (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
  (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
  {s : R} {e : ℕ} (D : CuspNormAtData O B s e 𝔪)

omit hθ [𝔪.IsMaximal] in
include hJ in
lemma cHcomap : (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁)))).comap
    (algebraMap (Rs θ R) (Ns θ D.N₁)) = sIdeal (θ := θ) 𝔪 := by
  have hJ𝔫 : J θ (R := D.N₁) ≤ D.𝔫 := by
    rw [← J_N₁_eq θ R D.N₁, Ideal.map_le_iff_le_comap, D.comap_eq]
    exact hJ
  ext z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.mem_comap, algebraMap_RN, Ideal.mem_quotient_iff_mem hJ𝔫,
    Ideal.mem_quotient_iff_mem hJ, ← Ideal.mem_comap, D.comap_eq]

variable [IsSepClosed k]

include hJ hres in
lemma cHsurj0 : Function.Surjective ((Ideal.Quotient.mk D.𝔫).comp (algebraMap R D.N₁)) := by
  have hρ : Function.Surjective ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R))) := by
    intro z
    obtain ⟨o, ho⟩ := hres z
    refine ⟨θ o, ?_⟩
    rw [RingHom.comp_apply, QuadNodeTower.algK_θ, Ideal.Quotient.factor_mk]
    exact ho
  exact EtaleResidue.surjective_of_isSepClosed' 𝔪 D.𝔫 D.comap_eq
    ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R))) hρ

include hJ hres in
lemma cHsurj : Function.Surjective
    ((Ideal.Quotient.mk (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁))))).comp
      (algebraMap (Rs θ R) (Ns θ D.N₁))) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := cHsurj0 𝔪 hJ hres D (Ideal.Quotient.mk D.𝔫 z)
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  simp only [RingHom.comp_apply] at ha ⊢
  rw [Ideal.Quotient.eq] at ha ⊢
  rw [algebraMap_RN, ← map_sub]
  exact Ideal.mem_map_of_mem _ ha

/-- The map `N̄₁ → R̄^_𝔪` of the special-fibre cusp form `pointCuspFormDataOf`. -/
def toHatC : Ns θ D.N₁ →ₐ[Rs θ R] Tn θ 𝔪 :=
  toHat (sIdeal 𝔪) _ (cHcomap 𝔪 hJ D) (cHsurj 𝔪 hJ hres D)

/-- The special-fibre cusp form of `pointCuspFormDataOf` is `cuspEquiv` along `toHatC`. -/
lemma pointCuspFormDataOf_Ψ :
    (pointCuspFormDataOf 𝔪 hJ hres D).Ψ =
      FormalKummer.cuspEquiv (sIdeal 𝔪) _ (cHcomap 𝔪 hJ D) (cHsurj 𝔪 hJ hres D) D.hX D.Φ :=
  rfl

/-- The special-fibre cusp form of `pointCuspFormDataOf` on `1 ⊗ c`, unfolded. -/
lemma pointCuspFormDataOf_Ψ_apply (c : Cs θ R B) (i : Fin D.r) :
    letI := cuspBarAlg θ D.N₁
    letI := sAlg (sIdeal (θ := θ) 𝔪) s
    (pointCuspFormDataOf 𝔪 hJ hres D).Ψ ((1 : Tn θ 𝔪) ⊗ₜ c) i =
      adjoinPowCongr (D.d i) (by
        change algebraMap (Rs θ R) _ (sBar θ s X) = _
        simp [sBar])
        (kpolyTensorEquiv (baseChangeEquiv (A := fun _ : Fin D.r ↦ k[X])
          (Bk := fun i ↦ KPoly k (D.d i)) (toHatC 𝔪 hJ hres D) (fun _ ↦ sBar θ s)
          (fun _ a ↦ cuspBar_eq D.hX a) (fun _ _ ↦ rfl) (cuspRedSplitEquiv D.Φ)
          ((1 : Tn θ 𝔪) ⊗ₜ c) i)) :=
  rfl

/-- `N₁ → N̄₁ → R̄^_𝔪` as an `R`-algebra map. -/
def hatCₐ : D.N₁ →ₐ[R] Tn θ 𝔪 :=
  { (toHatC 𝔪 hJ hres D).toRingHom.comp (Ideal.Quotient.mk (J θ (R := D.N₁))) with
    commutes' := fun a ↦ by
      change toHatC 𝔪 hJ hres D (algebraMap (Rs θ R) (Ns θ D.N₁) (Ideal.Quotient.mk _ a)) = _
      rw [AlgHom.commutes]
      rfl }

lemma hatCₐ_apply (z : D.N₁) :
    hatCₐ 𝔪 hJ hres D z = toHatC 𝔪 hJ hres D (Ideal.Quotient.mk _ z) := rfl

omit hθ [IsSepClosed k] [𝔪.IsMaximal] in
lemma le_comap_sIdeal' : 𝔪 ≤ (sIdeal (θ := θ) 𝔪).comap (algebraMap R (Rs θ R)) :=
  fun _ ha ↦ Ideal.mem_map_of_mem _ ha

/-- The residue map `N₁ → N₁/𝔫 ≅ R/𝔪 → R̄/𝔪̄` at the chosen point `𝔫` of `D`. -/
def resC : D.N₁ →ₐ[R] Rs θ R ⧸ sIdeal (θ := θ) 𝔪 :=
  FormalLevel.resMap D.comap_eq (cHsurj0 𝔪 hJ hres D) (le_comap_sIdeal' 𝔪)

lemma resHat_toHatC_eq_zero {w : D.N₁} (hw : w ∈ D.𝔫) :
    FormalLevel.resHat (sIdeal (θ := θ) 𝔪) (toHatC 𝔪 hJ hres D (Ideal.Quotient.mk _ w)) = 0 := by
  haveI := formallyEtale_Ns (θ := θ) (R := R) (N₁ := D.N₁)
  set E := CompletionEtale.equiv (sIdeal (θ := θ) 𝔪) _ (cHcomap 𝔪 hJ D) (cHsurj 𝔪 hJ hres D)
  have hE : ∀ Y, E.symm Y = CompletionEtale.inv _ _ (cHcomap 𝔪 hJ D)
      (cHsurj 𝔪 hJ hres D) Y := fun Y ↦ by
    rw [RingEquiv.symm_apply_eq]
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    rw [CompletionEtale.equiv_apply, CompletionMap.evalₐ_map,
      ← CompletionEtale.quotPowEquiv_apply (cHcomap 𝔪 hJ D) (cHsurj 𝔪 hJ hres D),
      CompletionEtale.evalₐ_inv, AlgEquiv.apply_symm_apply]
  have h1 : toHatC 𝔪 hJ hres D (Ideal.Quotient.mk _ w) = E.symm (algebraMap (Ns θ D.N₁)
      (AdicCompletion (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁)))) (Ns θ D.N₁))
      (Ideal.Quotient.mk _ w)) := rfl
  have hw' : (Ideal.Quotient.mk (J θ (R := D.N₁)) w) ∈
      (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁)))) ^ 1 := by
    rw [pow_one]; exact Ideal.mem_map_of_mem _ hw
  rw [h1, hE, FormalLevel.resHat, AlgHom.comp_apply, CompletionEtale.evalₐ_inv,
    AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, Algebra.algebraMap_self,
    RingHom.id_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hw', map_zero, map_zero]

/-- **`hatCₐ` is the canonical lift `FormalLevel.hatLift` of the residue map at `𝔫`.** -/
theorem hatCₐ_eq_hatLift :
    hatCₐ 𝔪 hJ hres D = FormalLevel.hatLift (resC 𝔪 hJ hres D) := by
  refine FormalLevel.hatLift_unique _ _ fun z ↦ ?_
  obtain ⟨a, ha⟩ := cHsurj0 𝔪 hJ hres D (Ideal.Quotient.mk D.𝔫 z)
  rw [RingHom.comp_apply, Ideal.Quotient.eq] at ha
  obtain ⟨w, hw, rfl⟩ : ∃ w ∈ D.𝔫, z = algebraMap R D.N₁ a - w := ⟨_, ha, by ring⟩
  have h2 : FormalLevel.resHat (sIdeal (θ := θ) 𝔪) (hatCₐ 𝔪 hJ hres D (algebraMap R D.N₁ a)) =
      resC 𝔪 hJ hres D (algebraMap R D.N₁ a) := by
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply R (Rs θ R),
      AlgHom.commutes]
    rfl
  have h3 : resC 𝔪 hJ hres D w = 0 := FormalLevel.resMap_eq_zero _ _ _ hw
  have h4 : FormalLevel.resHat (sIdeal (θ := θ) 𝔪) (hatCₐ 𝔪 hJ hres D w) = 0 :=
    resHat_toHatC_eq_zero 𝔪 hJ hres D hw
  rw [map_sub, map_sub, map_sub, h2, h3, h4]

end CuspOf

/-! ### The level form at the cusp -/

section LevelCusp

open FormalKummer AdmissibleLift Cusp

attribute [local instance] algRN cuspAlgO CuspNormAtData.polyAlg

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]
  {s : R} {e : ℕ} {𝔪 : Ideal R} (D : CuspNormAtData O B s e 𝔪)
  {T' : Type u} [CommRing T'] [Algebra R T']

/-- `T'` as an `O[X]`-algebra, `X ↦ s`. -/
abbrev tAlg (s : R) : Algebra O[X] T' := ((algebraMap R T').comp (aeval s).toRingHom).toAlgebra

omit hθ in
lemma algebraMap_poly_N₁ (a : O[X]) :
    algebraMap O[X] D.N₁ a = algebraMap R D.N₁ (aeval s a) := by
  have h := Polynomial.ringHom_ext (f := algebraMap O[X] D.N₁)
    (g := (algebraMap R D.N₁).comp (aeval s).toRingHom)
    (fun o ↦ by
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
        show (C o : O[X]) = algebraMap O O[X] o from rfl, ← IsScalarTower.algebraMap_apply]
      rfl)
    (by rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]; exact D.hX)
  exact RingHom.congr_fun h a

omit hθ in
lemma tAlg_X : letI := tAlg (T' := T') (O := O) s
    algebraMap O[X] T' X = algebraMap R T' s := by
  change algebraMap R T' (aeval s X) = _
  rw [aeval_X]

/-- **The level form at the cusp**: the base change of the chosen splitting `D.Φ` along a map
`g : N₁ → T'` (`g = FormalLevel.hatLift r` for a residue map `r`),
`T' ⊗_R B ≃ₐ[T'] ∏ᵢ T'[y]/(y^{dᵢ} − s)`. -/
def levelCuspΨ (g : D.N₁ →ₐ[R] T') :
    T' ⊗[R] B ≃ₐ[T'] ∀ i : Fin D.r, AdjoinRoot (X ^ D.d i - C (algebraMap R T' s)) :=
  letI := tAlg (T' := T') (O := O) s
  (baseChangeEquiv (A := fun _ : Fin D.r ↦ O[X]) (Bk := fun i ↦ KPoly O (D.d i)) g
    (fun _ ↦ (aeval s).toRingHom) (fun _ a ↦ algebraMap_poly_N₁ D a) (fun _ _ ↦ rfl) D.Φ).trans
    (AlgEquiv.piCongrRight fun i ↦ kpolyTensorEquivO.trans
      (adjoinPowCongr (D.d i) (tAlg_X (T' := T') (O := O) (s := s))))

end LevelCusp

/-! ### Level forms of a local formal cusp form -/

section LevelForm

open FormalKummer AdmissibleLift Cusp

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {B : Type u} [CommRing B] [Algebra R B]
  {𝔪 : Ideal R} {T' : Type u} [CommRing T'] [Algebra R T']

omit [Algebra R B] in
lemma red_s (red : T' →ₐ[R] Tn θ 𝔪) (s : R) :
    red (algebraMap R T' s) = algebraMap (Rs θ R) (Tn θ 𝔪) (Ideal.Quotient.mk _ s) := by
  rw [red.commutes]
  rfl

/-- **A level form of a local formal cusp form `D`** along a reduction map `red : T' → R̄^_𝔪`:
`Ψ : T' ⊗_R B ≃ ∏ᵢ T'[y]/(y^{dᵢ} − s)` reducing to `D.Ψ` on the elements `1 ⊗ b`. -/
structure LevelPointForm (red : T' →ₐ[R] Tn θ 𝔪) {s : R} {E : ℕ}
    (D : PointCuspFormData (θ := θ) (B := B) s E 𝔪) where
  /-- The level form. -/
  Ψ : T' ⊗[R] B ≃ₐ[T'] ∀ i : Fin D.r, AdjoinRoot (X ^ D.d i - C (algebraMap R T' s))
  compat : ∀ (b : B) (i : Fin D.r), adjMap red.toRingHom (D.d i) (red_s red s)
    (Ψ ((1 : T') ⊗ₜ b) i) = D.Ψ ((1 : Tn θ 𝔪) ⊗ₜ Ideal.Quotient.mk _ b) i

/-- Level forms are insensitive to the bound on the indices. -/
def LevelPointForm.mono {red : T' →ₐ[R] Tn θ 𝔪} {s : R} {E E' : ℕ} (hEE' : E ∣ E')
    {D : PointCuspFormData (θ := θ) (B := B) s E 𝔪} (L : LevelPointForm red D) :
    LevelPointForm red (D.mono hEE') :=
  ⟨L.Ψ, L.compat⟩

end LevelForm

section LevelCuspCompat

open FormalKummer AdmissibleLift Cusp

attribute [local instance] algRN cuspAlgO CuspNormAtData.polyAlg

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]

/-- `cuspSplitEquiv` on classes. -/
lemma cuspSplitEquiv_mk {N₁ : Type u} [CommRing N₁] [Algebra O N₁] [Algebra O[X] N₁]
    [IsScalarTower O O[X] N₁] {Y : Type u} [CommRing Y] [Algebra N₁ Y] {r : ℕ} {d : Fin r → ℕ}
    (Φ : Y ≃ₐ[N₁] ∀ i, CuspNormalFactor O (d i) N₁) (x : Y) (i : Fin r) :
    cuspSplitEquiv (θ := θ) Φ (Ideal.Quotient.mk _ x) i =
      FormalKummer.cuspFactorEquiv (Ideal.Quotient.mk _ (Φ x i)) := by
  change FormalKummer.cuspFactorEquiv
    (Ideal.quotEquivOfEq (KT_eq_cusp (θ := θ) (N₁ := N₁) (d := d i)).symm
    (Ideal.Quotient.mk ((J θ (R := N₁)).map (algebraMap N₁ (CuspNormalFactor O (d i) N₁)))
      (Φ x i))) = _
  rw [Ideal.quotEquivOfEq_mk]

/-- `cuspRedSplitEquiv` on pure tensors `ā ⊗ b̄`. -/
lemma cuspRedSplitEquiv_mk_tmul {N₁ : Type u} [CommRing N₁] [Algebra R N₁] [Algebra O N₁]
    [IsScalarTower O R N₁] [Algebra O[X] N₁] [IsScalarTower O O[X] N₁] {r : ℕ}
    {d : Fin r → ℕ} (Φ : N₁ ⊗[R] B ≃ₐ[N₁] ∀ i, CuspNormalFactor O (d i) N₁) (a : N₁) (b : B)
    (i : Fin r) :
    cuspRedSplitEquiv (θ := θ) Φ
        ((Ideal.Quotient.mk _ a : Ns θ N₁) ⊗ₜ (Ideal.Quotient.mk _ b : Cs θ R B)) i =
      FormalKummer.cuspFactorEquiv (Ideal.Quotient.mk _ (Φ (a ⊗ₜ b) i)) := by
  have h1 : (tensorQuot (θ := θ)).symm
      ((Ideal.Quotient.mk _ a : Ns θ N₁) ⊗ₜ (Ideal.Quotient.mk _ b : Cs θ R B)) =
        Ideal.Quotient.mk _ (a ⊗ₜ b) := by
    rw [RingEquiv.symm_apply_eq, tensorQuot_mk_tmul]
  simp only [cuspRedSplitEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, h1,
    Ideal.quotEquivOfEq_mk]
  exact cuspSplitEquiv_mk Φ _ i

variable {s : R} {T' : Type u} [CommRing T'] [Algebra R T'] {𝔪 : Ideal R}

/-- The reduction of `O[y] → T'[y]/(y^d − s)` along `red` is `O[y] → k[y] → R̄^_𝔪[y]/(y^d − s̄)`. -/
lemma adjMap_kpoly (red : T' →ₐ[R] Tn θ 𝔪) {d : ℕ} :
    letI := tAlg (T' := T') (O := O) s
    letI := sAlg (sIdeal (θ := θ) 𝔪) s
    ∀ (ha : (red.toRingHom.comp (RingHom.id T')) (algebraMap O[X] T' X) =
        algebraMap (Rs θ R) (Tn θ 𝔪) (Ideal.Quotient.mk _ s))
      (hb : (RingHom.id (Tn θ 𝔪)) (algebraMap k[X] (Tn θ 𝔪) X) =
        algebraMap (Rs θ R) (Tn θ 𝔪) (Ideal.Quotient.mk _ s)) (q : KPoly O d),
      adjMap (red.toRingHom.comp (RingHom.id T')) d ha (kpolyToARO q) =
        adjMap (RingHom.id (Tn θ 𝔪)) d hb (kpolyToAR (Polynomial.map θ q)) := by
  letI := tAlg (T' := T') (O := O) s
  letI := sAlg (sIdeal (θ := θ) 𝔪) s
  intro ha hb q
  have h := @Polynomial.ringHom_ext O _ _ _ ((adjMap _ d ha).comp kpolyToARO)
    ((adjMap _ d hb).comp ((kpolyToAR (T := Tn θ 𝔪) (d := d)).comp (mapRingHom θ)))
    (fun o ↦ by
      simp only [RingHom.comp_apply]
      change adjMap _ d ha (eval₂ _ _ (C o)) =
        adjMap _ d hb (eval₂ _ _ (Polynomial.map θ (C o)))
      rw [Polynomial.map_C]
      rw [eval₂_C, eval₂_C, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
        RingHom.comp_apply, AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq, adjMap_of,
        adjMap_of]
      congr 1
      change red (algebraMap R T' (aeval s (C o))) =
        algebraMap (Rs θ R) (Tn θ 𝔪) (sBar θ s (C (θ o)))
      rw [aeval_C, red.commutes, sBar, coe_eval₂RingHom, eval₂_C, QuadNodeTower.algK_θ]
      rfl)
    (by
      simp only [RingHom.comp_apply]
      change adjMap _ d ha (eval₂ _ _ X) = adjMap _ d hb (eval₂ _ _ (Polynomial.map θ X))
      rw [Polynomial.map_X]
      rw [eval₂_X, eval₂_X, adjMap_root, adjMap_root])
  exact RingHom.congr_fun h q

variable [IsSepClosed k] (𝔪) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
  (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
  {e : ℕ} (D : CuspNormAtData O B s e 𝔪)

/-- **Compatibility of the level form at the cusp with the special-fibre one**: if the reduction
`red` composed with `g : N₁ → T'` is the special-fibre map `hatCₐ`, then the reduction of
`levelCuspΨ g` on `1 ⊗ b` is the special-fibre cusp form `pointCuspFormDataOf` on `1 ⊗ b̄`. -/
theorem levelCuspΨ_compat (g : D.N₁ →ₐ[R] T') (red : T' →ₐ[R] Tn θ 𝔪)
    (hred : red.comp g = hatCₐ 𝔪 hJ hres D) (b : B) (i : Fin D.r) :
    adjMap red.toRingHom (D.d i) (red_s red s) (levelCuspΨ D g ((1 : T') ⊗ₜ b) i) =
      (pointCuspFormDataOf 𝔪 hJ hres D).Ψ ((1 : Tn θ 𝔪) ⊗ₜ Ideal.Quotient.mk _ b) i := by
  letI := tAlg (T' := T') (O := O) s
  letI := cuspBarAlg θ D.N₁
  letI := sAlg (sIdeal (θ := θ) 𝔪) s
  rw [pointCuspFormDataOf_Ψ_apply]
  simp only [levelCuspΨ, AlgEquiv.trans_apply, AlgEquiv.piCongrRight_apply,
    baseChangeEquiv_one_tmul]
  rw [← map_one (Ideal.Quotient.mk (J θ (R := D.N₁))), cuspRedSplitEquiv_mk_tmul,
    adjoinPowCongr_eq, adjoinPowCongr_eq, adjMap_adjMap]
  generalize D.Φ ((1 : D.N₁) ⊗ₜ b) i = w
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x q =>
    rw [FormalKummer.cuspFactorEquiv_mk_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, kpolyTensorEquivO_tmul, kpolyTensorEquiv_tmul, map_mul,
      map_mul, adjMap_of, adjMap_of]
    congr 1
    · congr 1
      exact DFunLike.congr_fun hred x
    · exact adjMap_kpoly red _ _ q

/-- **The level form at the cusp**: `levelCuspΨ` along `g`, as a `LevelPointForm` of the
special-fibre cusp form `pointCuspFormDataOf` (for `red ∘ g = hatCₐ`). -/
def levelCuspForm (g : D.N₁ →ₐ[R] T') (red : T' →ₐ[R] Tn θ 𝔪)
    (hred : red.comp g = hatCₐ 𝔪 hJ hres D) :
    LevelPointForm red (pointCuspFormDataOf 𝔪 hJ hres D) :=
  ⟨levelCuspΨ D g, levelCuspΨ_compat 𝔪 hJ hres D g red hred⟩

end LevelCuspCompat

section EtaleLift

variable {A X Y Z : Type*} [CommRing A] [CommRing X] [Algebra A X] [CommRing Y] [Algebra A Y]
  [CommRing Z] (I : Ideal A) {m : ℕ} (hI : I ^ m = ⊥)
  [Algebra.FormallyEtale A X] [Algebra.FormallyEtale A Y]
  (ρX : X →+* Z) (hρX : Function.Surjective ρX) (hkX : RingHom.ker ρX = I.map (algebraMap A X))
  (ρY : Y →+* Z) (hρY : Function.Surjective ρY) (hkY : RingHom.ker ρY = I.map (algebraMap A Y))
  (hc : ∀ a, ρX (algebraMap A X a) = ρY (algebraMap A Y a))

include hI hρX hkX hρY hkY hc in
/-- **Étale lifts of isomorphisms of reductions**: two formally étale `A`-algebras with
surjections `ρX`, `ρY` onto the same ring, with kernels `I X`, `I Y` (`I` nilpotent), are
isomorphic compatibly with `ρX`, `ρY`. -/
theorem exists_equiv_of_red : ∃ Φ : X ≃ₐ[A] Y, ∀ x, ρY (Φ x) = ρX x := by
  haveI : IsAdicComplete (I.map (algebraMap A X)) X :=
    CompleteFinite.isAdicComplete_of_pow_eq_bot _ (n := m)
      (by rw [← Ideal.map_pow, hI, Ideal.map_bot])
  haveI : IsAdicComplete (I.map (algebraMap A Y)) Y :=
    CompleteFinite.isAdicComplete_of_pow_eq_bot _ (n := m)
      (by rw [← Ideal.map_pow, hI, Ideal.map_bot])
  obtain ⟨eX, hX⟩ : ∃ eX : (X ⧸ I.map (algebraMap A X)) ≃+* Z,
      ∀ x, eX (Ideal.Quotient.mk _ x) = ρX x :=
    ⟨(Ideal.quotEquivOfEq hkX.symm).trans (RingHom.quotientKerEquivOfSurjective hρX), fun x ↦ by
      simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk]⟩
  obtain ⟨eY, hY⟩ : ∃ eY : (Y ⧸ I.map (algebraMap A Y)) ≃+* Z,
      ∀ y, eY (Ideal.Quotient.mk _ y) = ρY y :=
    ⟨(Ideal.quotEquivOfEq hkY.symm).trans (RingHom.quotientKerEquivOfSurjective hρY), fun y ↦ by
      simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk]⟩
  let E : (X ⧸ I.map (algebraMap A X)) ≃ₐ[A] (Y ⧸ I.map (algebraMap A Y)) :=
    AlgEquiv.ofRingEquiv (f := eX.trans eY.symm) fun a ↦ by
      rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq, ← Ideal.Quotient.mk_algebraMap,
        ← Ideal.Quotient.mk_algebraMap, hX, hY, hc]
  refine ⟨EtaleLift.algEquivOfQuot I E, fun x ↦ ?_⟩
  have h := congrArg (fun g ↦ g x) (EtaleLift.mkₐ_comp_algEquivOfQuot I E)
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom] at h
  rw [← hY, h]
  change eY ((eX.trans eY.symm) (Ideal.Quotient.mk _ x)) = _
  rw [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, hX]

end EtaleLift

section KerLemmas

/-- The kernel of `adjMap g` for surjective `g` is generated by `ker g`. -/
lemma ker_adjMap {S S' : Type*} [CommRing S] [CommRing S'] (g : S →+* S')
    (hg : Function.Surjective g) (n : ℕ) {a : S} {b : S'} (hab : g a = b) :
    RingHom.ker (adjMap g n hab) = (RingHom.ker g).map (AdjoinRoot.of (X ^ n - C a)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [RingHom.mem_ker, adjMap_mk, AdjoinRoot.mk_eq_zero] at hz
    obtain ⟨q', hq'⟩ := hz
    obtain ⟨q, rfl⟩ := Polynomial.map_surjective g hg q'
    have h1 : p - (X ^ n - C a) * q ∈ RingHom.ker (mapRingHom g) := by
      rw [RingHom.mem_ker, map_sub, map_mul]
      simp only [coe_mapRingHom]
      rw [hq', Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hab,
        sub_self]
    rw [Polynomial.ker_mapRingHom] at h1
    have h2 : AdjoinRoot.mk (X ^ n - C a) p = AdjoinRoot.mk _ (p - (X ^ n - C a) * q) := by
      rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero]
    rw [h2]
    have h3 := Ideal.mem_map_of_mem (AdjoinRoot.mk (X ^ n - C a)) h1
    rwa [Ideal.map_map] at h3
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, adjMap_of, RingHom.mem_ker.mp hx, map_zero]

lemma adjMap_surjective {S S' : Type*} [CommRing S] [CommRing S'] (g : S →+* S')
    (hg : Function.Surjective g) (n : ℕ) {a : S} {b : S'} (hab : g a = b) :
    Function.Surjective (adjMap g n hab) := by
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective g hg p
  exact ⟨AdjoinRoot.mk _ q, adjMap_mk _ _ _ _⟩

/-- An element of a finite product all of whose components lie in `I Yᵢ` lies in `I ∏ Yᵢ`. -/
lemma mem_map_pi {A : Type*} [CommRing A] {ι : Type*} [Finite ι]
    {Y : ι → Type*} [∀ i, CommRing (Y i)] [∀ i, Algebra A (Y i)] (I : Ideal A)
    (x : ∀ i, Y i) (hx : ∀ i, x i ∈ I.map (algebraMap A (Y i))) :
    x ∈ I.map (algebraMap A (∀ i, Y i)) := by
  classical
  haveI := Fintype.ofFinite ι
  have key : ∀ i, ∀ y ∈ I.map (algebraMap A (Y i)),
      Pi.single i y ∈ I.map (algebraMap A (∀ i, Y i)) := by
    intro i y hy
    have h1 : I.map (algebraMap A (Y i)) =
        (I.map (algebraMap A (∀ i, Y i))).map (Pi.evalRingHom Y i) := by
      rw [Ideal.map_map]
      rfl
    rw [h1, Ideal.mem_map_iff_of_surjective _ (fun z ↦ ⟨Pi.single i z, by simp⟩)] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    have h2 : Pi.single i (Pi.evalRingHom Y i y') = Pi.single i 1 * y' := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [h2]
    exact Ideal.mul_mem_left _ _ hy'
  rw [← Finset.univ_sum_single x]
  exact Ideal.sum_mem _ fun i _ ↦ key i _ (hx i)

end KerLemmas

/-! ### Assembling the level forms along the marked points -/

section Assemble

open FormalKummer AdmissibleLift Cusp FormalLevel

attribute [local instance] cuspAlgO

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
  (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j) {s : R} {E : ι → ℕ}
  (D : ∀ j, PointCuspFormData (θ := θ) (B := B) s (E j) (𝔪 j)) {fk : Rs θ R}
  (hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
  (hfk : ∀ j, fk ∈ sIdeal (θ := θ) (𝔪 j))
  (hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fk}).radical)
  (ψk : Polynomial k →ₐ[k] Admissible.Hat fk)
  (hψ : ψk X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s))
  {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra O R'] [IsScalarTower O R R']
  [IsNoetherianRing R'] [Algebra k (R' ⧸ J θ (R := R'))]
  (e : Rs θ R ≃ₐ[k] R' ⧸ J θ (R := R'))
  (he : ∀ r : R, e (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R R' r))
  {f : R'} (hfe : e fk = fbar θ f)
  {𝔪' : ι → Ideal R'} [∀ j, (𝔪' j).IsMaximal] (hinj : Function.Injective 𝔪')
  (hf : ∀ j, f ∈ 𝔪' j) (hrad : ⨅ j, 𝔪' j ≤ (Ideal.span {f}).radical)
  (hm : ∀ j, (𝔪' j).map (red θ e) ≤ sIdeal (θ := θ) (𝔪 j))
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]
  (Ψ : ∀ j, LevelPointForm (redHat 𝔪 e he hm j) (D j))
  (t : FormalPatchLevel.Hat f) (ht : t = algebraMap R (FormalPatchLevel.Hat f) s)
  (δ : (Σ j, Fin (D j).r) → FormalPatchLevel.Hat f)
  (hδ : ∀ p, δ p = CompletionProd.idem hinj hf hrad p.1)

/-- The base `R̂'_{𝔪' j} ≅ R̂'/(1 − δ_p)` of the factor `p = (j, i)`. -/
def baseIsoC (p : Σ j, Fin (D j).r) :
    AdicCompletion (𝔪' p.1) R' ≃+* CBase f (δ p) :=
  (CompletionProd.quotEquiv hinj hf hrad p.1).symm.trans (Ideal.quotEquivOfEq (by rw [hδ]))

omit hθ [IsSepClosed k] [IsNoetherianRing R] [∀ j, (𝔪 j).IsMaximal] [Algebra O R']
  [IsScalarTower O R R'] [Algebra k (R' ⧸ J θ (R := R'))]
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
include ht in
lemma baseIsoC_s (p : Σ j, Fin (D j).r) :
    baseIsoC 𝔪 D hinj hf hrad δ hδ p (algebraMap R (AdicCompletion (𝔪' p.1) R') s) =
      Ideal.Quotient.mk _ t := by
  have e2 : CompletionProd.quotEquiv hinj hf hrad p.1 (Ideal.Quotient.mk _ t) =
      algebraMap R (AdicCompletion (𝔪' p.1) R') s := by
    rw [ht]
    exact CompletionProd.quotEquiv_algebraMap hinj hf hrad p.1 (algebraMap R R' s)
  rw [baseIsoC, RingEquiv.trans_apply, ← e2, RingEquiv.symm_apply_apply,
    Ideal.quotEquivOfEq_mk]

/-- **The level piece** `R̂'_{𝔪' j}[y]/(y^d − s) ≅ (R̂'/(1 − δ_p))[y]/(y^d − t)`. -/
def pieceIsoC (p : Σ j, Fin (D j).r) :
    AdjoinRoot (X ^ (D p.1).d p.2 - C (algebraMap R (AdicCompletion (𝔪' p.1) R') s)) ≃+*
      CPiece f (δ p) t ((D p.1).d p.2) :=
  FormalKummer.adjoinPowEquiv (baseIsoC 𝔪 D hinj hf hrad δ hδ p) _
    (baseIsoC_s 𝔪 D hinj hf hrad t ht δ hδ p)

/-- **The level formal cusp form along the marked points**:
`R̂' ⊗_R B ≃ₐ[R̂'] ∏_{p = (j,i)} (R̂'/(1 − δ_p))[y]/(y^{d_p} − t)`, the cusp part of the lifted
formal model of the M2 lift, assembled from the level forms `Ψ j` at the points. -/
def levelCuspEquiv :
    FormalPatchLevel.Hat f ⊗[R] B ≃ₐ[FormalPatchLevel.Hat f]
      ∀ p : (Σ j, Fin (D j).r), CPiece f (δ p) t ((D p.1).d p.2) :=
  AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.congr (hatEquivR (R := R) hinj hf hrad) AlgEquiv.refl).trans
      (piLeftEquivR (R := R) (B := B) (𝔪' := 𝔪'))).toRingEquiv.trans
      ((RingEquiv.piCongrRight fun j ↦ (Ψ j).Ψ.toRingEquiv).trans
        ((RingEquiv.piCongrRight fun j ↦ RingEquiv.piCongrRight fun i ↦
          pieceIsoC 𝔪 D hinj hf hrad t ht δ hδ ⟨j, i⟩).trans
          (piCurryRingEquiv _)))) (by
    intro h
    funext p
    obtain ⟨j, i⟩ := p
    have h1 : (Ψ j).Ψ (hatEquivR (R := R) hinj hf hrad h j ⊗ₜ (1 : B)) =
        algebraMap (AdicCompletion (𝔪' j) R') _ (hatEquivR (R := R) hinj hf hrad h j) := by
      rw [← (Ψ j).Ψ.commutes]
      rfl
    have h2 : (CompletionProd.quotEquiv hinj hf hrad j).symm
        (hatEquivR (R := R) hinj hf hrad h j) = Ideal.Quotient.mk _ h := by
      refine (RingEquiv.symm_apply_eq _).mpr ?_
      rw [CompletionProd.quotEquiv_mk]
      rfl
    change pieceIsoC 𝔪 D hinj hf hrad t ht δ hδ ⟨j, i⟩
      ((Ψ j).Ψ (hatEquivR (R := R) hinj hf hrad h j ⊗ₜ (1 : B)) i) = _
    rw [h1, pieceIsoC, adjoinPowEquiv_eq, Pi.algebraMap_apply, AdjoinRoot.algebraMap_eq, adjMap_of,
      RingEquiv.coe_toRingHom, baseIsoC, RingEquiv.trans_apply, h2, Ideal.quotEquivOfEq_mk]
    rfl)

omit [IsSepClosed k] [IsNoetherianRing R] [∀ j, (𝔪 j).IsMaximal] [IsScalarTower O R R']
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **`levelCuspEquiv` on `1 ⊗ b`**: the level piece of the level form `Ψ j` on `1 ⊗ b`. -/
theorem levelCuspEquiv_one_tmul (b : B) (p : Σ j, Fin (D j).r) :
    levelCuspEquiv 𝔪 D e he hinj hf hrad hm Ψ t ht δ hδ ((1 : FormalPatchLevel.Hat f) ⊗ₜ b) p =
      pieceIsoC 𝔪 D hinj hf hrad t ht δ hδ p
        ((Ψ p.1).Ψ ((1 : AdicCompletion (𝔪' p.1) R') ⊗ₜ b) p.2) := by
  obtain ⟨j, i⟩ := p
  have h1 : hatEquivR (R := R) hinj hf hrad (1 : FormalPatchLevel.Hat f) j = 1 := by
    rw [map_one]; rfl
  change pieceIsoC 𝔪 D hinj hf hrad t ht δ hδ ⟨j, i⟩
    ((Ψ j).Ψ (hatEquivR (R := R) hinj hf hrad 1 j ⊗ₜ b) i) = _
  rw [h1]

omit [IsSepClosed k] in
/-- `cuspEquivOf` on `1 ⊗ c`. -/
lemma cuspEquivOf_one_tmul (c : Cs θ R B) (p : Σ j, Fin (D j).r) :
    cuspEquivOf 𝔪 hJ D hinjk hfk hradk ψk hψ ((1 : Admissible.Hat fk) ⊗ₜ c) p =
      (FormalKummer.cuspPieceEquiv hinjk hfk hradk ψk hψ p.1 ((D p.1).d p.2)).symm
        ((D p.1).Ψ ((1 : Tn θ (𝔪 p.1)) ⊗ₜ c) p.2) := by
  obtain ⟨j, i⟩ := p
  have h1 : FormalKummer.hatEquiv hinjk hfk hradk (1 : Admissible.Hat fk) j = 1 := by
    rw [map_one]; rfl
  change (FormalKummer.cuspPieceEquiv hinjk hfk hradk ψk hψ j ((D j).d i)).symm
    ((D j).Ψ (FormalKummer.hatEquiv hinjk hfk hradk 1 j ⊗ₜ c) i) = _
  rw [h1]

omit [IsSepClosed k] [∀ j, (𝔪 j).IsMaximal] [IsScalarTower O R R'] in
include he hm in
/-- **The reduction of the level bases**: `R̂'_{𝔪' j} ≅ R̂'/(1 − δ_p) → (R̂'/J)/(1 − Ê εⱼ) ≅
R̄^_{𝔪 j}` is `redHat`. -/
theorem quotEquiv_σc_baseIsoC (p : Σ j, Fin (D j).r)
    (hδψ : ψ θ f (δ p) = Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk p.1))
    (x : AdicCompletion (𝔪' p.1) R') :
    CompletionProd.quotEquiv hinjk hfk hradk p.1
      ((Admissible.baseEquiv (h := hfe) (CompletionProd.idem hinjk hfk hradk p.1)).symm
        (σc θ f (δ p) (Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk p.1)) hδψ
          (baseIsoC 𝔪 D hinj hf hrad δ hδ p x))) =
      redHat 𝔪 e he hm p.1 x := by
  obtain ⟨z, rfl⟩ := (CompletionProd.quotEquiv hinj hf hrad p.1).surjective x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  have h1 : baseIsoC 𝔪 D hinj hf hrad δ hδ p
      (CompletionProd.quotEquiv hinj hf hrad p.1 (Ideal.Quotient.mk _ w)) =
      Ideal.Quotient.mk _ w := by
    rw [baseIsoC, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
    exact Ideal.quotEquivOfEq_mk _ w
  rw [h1, σc_mk]
  change CompletionProd.quotEquiv hinjk hfk hradk p.1
      ((Ideal.quotientEquiv _ _ (Admissible.hatEquiv e hfe).toRingEquiv _).symm
        (Ideal.Quotient.mk _ (ψ θ f w))) = _
  rw [Ideal.quotientEquiv_symm_mk, CompletionProd.quotEquiv_mk, CompletionProd.quotEquiv_mk]
  change _ = CompletionMap.map (red θ e) (hm p.1) _
  rw [AlgEquiv.toRingEquiv_symm, AlgEquiv.coe_ringEquiv, Admissible.hatEquiv_symm,
    Admissible.hatEquiv_apply, CompletionQuot.ψ_eq_map, CompletionMap.map_comp,
    CompletionMap.map_comp, CompletionMap.map_comp]
  exact CompletionMap.map_congr (by ext; rfl) _ _ _

omit hθ [IsSepClosed k] [IsNoetherianRing R] [IsScalarTower O R R'] in
/-- `cuspEquiv` on representatives: reduce the coefficients. -/
lemma cuspEquiv_mk_mk' {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
    (δ t : FormalPatchLevel.Hat f) (δb : Admissible.Hat (fbar θ f)) (hδ : ψ θ f δ = δb)
    (ht : ψ θ f t = ψc X) (m : ℕ) (q : (CBase f δ)[X]) :
    AdmissibleLift.cuspEquiv θ f ψc δ t δb hδ ht m (Ideal.Quotient.mk _ (AdjoinRoot.mk _ q)) =
      AdjoinRoot.mk _ (q.map (σc θ f δ δb hδ)) := by
  rw [AdmissibleLift.cuspEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, AlgEquiv.coe_ringEquiv, AdjoinRoot.quotEquivQuotMap_apply_mk]
  erw [Ideal.quotientEquiv_mk]
  rw [Polynomial.mapEquiv_apply, Polynomial.map_map]
  congr 2

set_option maxHeartbeats 2000000 in
-- unifying the quotient ideals unfolds the completion isomorphism `hatEquiv`
omit [IsSepClosed k] [IsNoetherianRing R] [Algebra R R'] [IsScalarTower O R R']
  [IsNoetherianRing R'] in
lemma admCuspPieceEquiv_mk (δb : Admissible.Hat fk) (m : ℕ)
    (q : (Admissible.Hat fk ⧸ Ideal.span {1 - δb})[X]) :
    Admissible.cuspPieceEquiv (h := hfe) ψk δb m (AdjoinRoot.mk _ q) =
      AdjoinRoot.mk _ (q.map ((Admissible.baseEquiv (h := hfe) δb : _ ≃+* _) : _ →+* _)) := by
  rw [Admissible.cuspPieceEquiv]
  exact Ideal.quotientEquiv_mk _ _ _ _ q

set_option maxHeartbeats 1000000 in
-- the statement unfolds the transported cusp pieces
omit [IsSepClosed k] [∀ j, (𝔪 j).IsMaximal] [IsScalarTower O R R'] in
include he hm in
/-- **The reduction of the level pieces**: the reduction of `pieceIsoC p` is the transported
special-fibre piece of the reduction `adjMap redHat`. -/
theorem cuspEquiv_pieceIsoC (p : Σ j, Fin (D j).r)
    (hδψ : ψ θ f (δ p) = Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk p.1))
    (ht' : ψ θ f t = Admissible.ψT (h := hfe) ψk X)
    (z : AdjoinRoot (X ^ (D p.1).d p.2 - C (algebraMap R (AdicCompletion (𝔪' p.1) R') s))) :
    AdmissibleLift.cuspEquiv θ f (Admissible.ψT (h := hfe) ψk) (δ p) t
        (Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk p.1)) hδψ ht'
        ((D p.1).d p.2) (Ideal.Quotient.mk _ (pieceIsoC 𝔪 D hinj hf hrad t ht δ hδ p z)) =
      Admissible.cuspPieceEquiv (h := hfe) ψk (CompletionProd.idem hinjk hfk hradk p.1)
        ((D p.1).d p.2) ((FormalKummer.cuspPieceEquiv hinjk hfk hradk ψk hψ p.1
          ((D p.1).d p.2)).symm (adjMap (redHat 𝔪 e he hm p.1).toRingHom _ (red_s _ s) z)) := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [pieceIsoC, adjoinPowEquiv_eq, adjMap_mk, cuspEquiv_mk_mk', adjMap_mk,
    FormalKummer.cuspPieceEquiv, adjoinPowEquiv_symm_eq, adjMap_mk, admCuspPieceEquiv_mk,
    Polynomial.map_map, Polynomial.map_map, Polynomial.map_map]
  congr 2
  ext x
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← quotEquiv_σc_baseIsoC 𝔪 D hinjk hfk hradk e he hfe hinj hf hrad hm δ hδ p hδψ x]
  simp

set_option maxHeartbeats 1000000 in
-- the statement unfolds the transported cusp pieces
omit [IsSepClosed k] [IsScalarTower O R R'] in
include he hm in
/-- **Compatibility of the level formal cusp form with the special-fibre one** (S6 G2c): on
`1 ⊗ b`, the reduction (`AdmissibleLift.cuspEquiv`, for the covering transported to the level) of
the `p`-th component of `levelCuspEquiv` is the transported `p`-th component of
`cuspEquivOf (1 ⊗ b̄)`. -/
theorem levelCuspEquiv_compat (b : B) (p : Σ j, Fin (D j).r)
    (hδψ : ψ θ f (δ p) = Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk p.1))
    (ht' : ψ θ f t = Admissible.ψT (h := hfe) ψk X) :
    AdmissibleLift.cuspEquiv θ f (Admissible.ψT (h := hfe) ψk) (δ p) t
        (Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk p.1)) hδψ ht'
        ((D p.1).d p.2) (Ideal.Quotient.mk _ (levelCuspEquiv 𝔪 D e he hinj hf hrad hm Ψ t ht δ hδ
          ((1 : FormalPatchLevel.Hat f) ⊗ₜ b) p)) =
      Admissible.cuspPieceEquiv (h := hfe) ψk (CompletionProd.idem hinjk hfk hradk p.1)
        ((D p.1).d p.2) (cuspEquivOf 𝔪 hJ D hinjk hfk hradk ψk hψ
          ((1 : Admissible.Hat fk) ⊗ₜ Ideal.Quotient.mk _ b) p) := by
  rw [levelCuspEquiv_one_tmul, cuspEquiv_pieceIsoC 𝔪 D hinjk hfk hradk ψk hψ e he hfe hinj hf hrad
    hm t ht δ hδ p hδψ ht', (Ψ p.1).compat, cuspEquivOf_one_tmul]

omit [IsSepClosed k] [Fintype ι] [∀ j, (𝔪 j).IsMaximal] [IsScalarTower O R R'] in
include he hm in
/-- The reduction of the level completion at the `j`-th point is `σc` (the completion maps of the
M2 lift) under `R̂'_{𝔪' j} ≅ R̂'/(1 − εⱼ)`, `R̄^_{𝔪 j} ≅ (R̂'/J)/(1 − Ê εⱼ)`. -/
theorem quotEquiv_σc_point [Finite ι] (j : ι)
    (hεψ : ψ θ f (CompletionProd.idem hinj hf hrad j) =
      Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk j))
    (x : AdicCompletion (𝔪' j) R') :
    CompletionProd.quotEquiv hinjk hfk hradk j
      ((Admissible.baseEquiv (h := hfe) (CompletionProd.idem hinjk hfk hradk j)).symm
        (σc θ f (CompletionProd.idem hinj hf hrad j)
          (Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk j)) hεψ
          ((CompletionProd.quotEquiv hinj hf hrad j).symm x))) =
      redHat 𝔪 e he hm j x := by
  obtain ⟨z, rfl⟩ := (CompletionProd.quotEquiv hinj hf hrad j).surjective x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingEquiv.symm_apply_apply, σc_mk]
  change CompletionProd.quotEquiv hinjk hfk hradk j
      ((Ideal.quotientEquiv _ _ (Admissible.hatEquiv e hfe).toRingEquiv _).symm
        (Ideal.Quotient.mk _ (ψ θ f w))) = _
  rw [Ideal.quotientEquiv_symm_mk, CompletionProd.quotEquiv_mk, CompletionProd.quotEquiv_mk]
  change _ = CompletionMap.map (red θ e) (hm j) _
  rw [AlgEquiv.toRingEquiv_symm, AlgEquiv.coe_ringEquiv, Admissible.hatEquiv_symm,
    Admissible.hatEquiv_apply, CompletionQuot.ψ_eq_map, CompletionMap.map_comp,
    CompletionMap.map_comp, CompletionMap.map_comp]
  exact CompletionMap.map_congr (by ext; rfl) _ _ _

omit [IsSepClosed k] [Fintype ι] [∀ j, (𝔪 j).IsMaximal] [IsScalarTower O R R'] in
include he hm in
/-- **`redHat` is surjective with kernel `J R̂'_{𝔪' j}`.** -/
theorem redHat_surjective_ker [Finite ι] (j : ι)
    (hεψ : ψ θ f (CompletionProd.idem hinj hf hrad j) =
      Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk j)) :
    Function.Surjective (redHat 𝔪 e he hm j) ∧
      RingHom.ker (redHat 𝔪 e he hm j) =
        (J θ (R := R')).map (algebraMap R' (AdicCompletion (𝔪' j) R')) := by
  have h := quotEquiv_σc_point 𝔪 hinjk hfk hradk e he hfe hinj hf hrad hm j hεψ
  refine ⟨fun y ↦ ?_, ?_⟩
  · obtain ⟨z, hz⟩ := surjective_σc θ f (CompletionProd.idem hinj hf hrad j) _ hεψ
      (Admissible.baseEquiv (h := hfe) (CompletionProd.idem hinjk hfk hradk j)
        ((CompletionProd.quotEquiv hinjk hfk hradk j).symm y))
    refine ⟨CompletionProd.quotEquiv hinj hf hrad j z, ?_⟩
    rw [← h, RingEquiv.symm_apply_apply, hz, RingEquiv.symm_apply_apply,
      RingEquiv.apply_symm_apply]
  · ext x
    rw [RingHom.mem_ker, ← h, map_eq_zero_iff _ (RingEquiv.injective _),
      map_eq_zero_iff _ (RingEquiv.injective _), ← RingHom.mem_ker, ker_σc]
    constructor
    · intro hx
      have h2 := Ideal.mem_map_of_mem (CompletionProd.quotEquiv hinj hf hrad j).toRingHom hx
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
        Ideal.map_map] at h2
      convert h2 using 2
      exact RingHom.ext fun r ↦ (CompletionProd.quotEquiv_algebraMap hinj hf hrad j r).symm
    · intro hx
      have h2 := Ideal.mem_map_of_mem
        (CompletionProd.quotEquiv hinj hf hrad j).symm.toRingHom hx
      rw [Ideal.map_map] at h2
      convert h2 using 2
      · refine RingHom.ext fun r ↦ ?_
        change _ = (CompletionProd.quotEquiv hinj hf hrad j).symm
          (algebraMap R' (AdicCompletion (𝔪' j) R') r)
        rw [eq_comm, RingEquiv.symm_apply_eq, CompletionProd.quotEquiv_algebraMap]
      · rfl

/-! ### The level form at a point where the cover is étale -/

/-- `R̄^_𝔪 ⊗_{R̄} C ≅ R̄^_𝔪 ⊗_R B`. -/
def tensorCsEquiv (𝔪₀ : Ideal R) :
    Tn θ 𝔪₀ ⊗[Rs θ R] Cs θ R B ≃ₐ[Tn θ 𝔪₀] Tn θ 𝔪₀ ⊗[R] B :=
  (Algebra.TensorProduct.congr AlgEquiv.refl
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (J θ (R := R)))).trans
    (Algebra.TensorProduct.cancelBaseChange R (Rs θ R) (Tn θ 𝔪₀) (Tn θ 𝔪₀) B)

omit hθ [IsSepClosed k] [IsNoetherianRing R] in
lemma tensorCsEquiv_tmul (𝔪₀ : Ideal R) (x : Tn θ 𝔪₀) (b : B) :
    tensorCsEquiv (θ := θ) (B := B) 𝔪₀ (x ⊗ₜ Ideal.Quotient.mk _ b) = x ⊗ₜ b := by
  rw [tensorCsEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  erw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  rfl

omit hθ [IsSepClosed k] in
/-- `g ∉ 𝔪` is a unit in the completion `R̄^_𝔪`. -/
lemma isUnit_Tn (𝔪₀ : Ideal R) [𝔪₀.IsMaximal] (hJ₀ : J θ (R := R) ≤ 𝔪₀) {g : R}
    (hg : g ∉ 𝔪₀) : IsUnit (algebraMap R (Tn θ 𝔪₀) g) := by
  set I₀ := sIdeal (θ := θ) 𝔪₀ with hI₀
  haveI : I₀.IsMaximal := isMaximal_sIdeal 𝔪₀ hJ₀
  have fg : I₀.FG := IsNoetherian.noetherian I₀
  set 𝔪h := I₀.map (algebraMap (Rs θ R) (Tn θ 𝔪₀)) with h𝔪h
  haveI : IsAdicComplete 𝔪h (Tn θ 𝔪₀) := AdicCompletion.isAdicComplete_self I₀ fg
  haveI : 𝔪h.IsMaximal := AdicCompletion.isMaximal_map_of_le I₀ I₀ le_rfl fg
  have hev (x : Rs θ R) : AdicCompletion.evalOneₐ I₀ (algebraMap _ (Tn θ 𝔪₀) x) =
      Ideal.Quotient.mk I₀ x :=
    RingHom.congr_fun (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk I₀) x
  have hmem (t : Tn θ 𝔪₀) : t ∈ 𝔪h ↔ AdicCompletion.evalOneₐ I₀ t = 0 := by
    rw [h𝔪h, ← AdicCompletion.ker_evalOneₐ_eq_map I₀ fg, RingHom.mem_ker]
    rfl
  haveI := isLocalRing_of_isAdicComplete_maximal 𝔪h
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.eq_maximalIdeal ‹𝔪h.IsMaximal›, hmem,
    IsScalarTower.algebraMap_apply R (Rs θ R) (Tn θ 𝔪₀), hev, Ideal.Quotient.eq_zero_iff_mem,
    hI₀]
  change Ideal.Quotient.mk _ g ∉ sIdeal (θ := θ) 𝔪₀
  rw [sIdeal, Ideal.mem_quotient_iff_mem hJ₀]
  exact hg

/-- The reduction `R̂'_{𝔪' j} ⊗_R B → R̄^_{𝔪 j} ⊗_R B ≅ R̄^_{𝔪 j} ⊗_{R̄} C ≅ ∏ᵢ` (the special-fibre
form `D j`). -/
def ρXe (j : ι) : AdicCompletion (𝔪' j) R' ⊗[R] B →+*
    ∀ i : Fin (D j).r, AdjoinRoot (X ^ (D j).d i -
      C (algebraMap (Rs θ R) (Tn θ (𝔪 j)) (Ideal.Quotient.mk _ s))) :=
  (D j).Ψ.toAlgHom.toRingHom.comp
    ((tensorCsEquiv (θ := θ) (B := B) (𝔪 j)).symm.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.map (redHat 𝔪 e he hm j) (AlgHom.id R B)).toRingHom)

/-- The reduction `∏ᵢ R̂'_{𝔪' j}[y]/(y^{dᵢ} − s) → ∏ᵢ R̄^_{𝔪 j}[y]/(y^{dᵢ} − s̄)`. -/
def ρYe (j : ι) : (∀ i : Fin (D j).r,
      AdjoinRoot (X ^ (D j).d i - C (algebraMap R (AdicCompletion (𝔪' j) R') s))) →+*
    ∀ i : Fin (D j).r, AdjoinRoot (X ^ (D j).d i -
      C (algebraMap (Rs θ R) (Tn θ (𝔪 j)) (Ideal.Quotient.mk _ s))) :=
  RingHom.pi fun i ↦ (adjMap (redHat 𝔪 e he hm j).toRingHom ((D j).d i) (red_s _ s)).comp
    (Pi.evalRingHom _ i)

omit [IsSepClosed k] [IsNoetherianRing R] [Fintype ι] [DecidableEq ι] [∀ j, (𝔪 j).IsMaximal]
  [IsScalarTower O R R'] [IsNoetherianRing R'] [∀ j, (𝔪' j).IsMaximal]
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
lemma ρXe_one_tmul (j : ι) (b : B) :
    ρXe 𝔪 D e he hm j ((1 : AdicCompletion (𝔪' j) R') ⊗ₜ b) =
      (D j).Ψ ((1 : Tn θ (𝔪 j)) ⊗ₜ Ideal.Quotient.mk _ b) := by
  change (D j).Ψ ((tensorCsEquiv (θ := θ) (B := B) (𝔪 j)).symm
    (Algebra.TensorProduct.map (redHat 𝔪 e he hm j) (AlgHom.id R B)
      ((1 : AdicCompletion (𝔪' j) R') ⊗ₜ b))) = _
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  congr 1
  rw [AlgEquiv.symm_apply_eq, tensorCsEquiv_tmul]

omit [IsSepClosed k] [Fintype ι] [IsScalarTower O R R'] in
include he hm hJ in
/-- **The level form at a point where the cover is étale** (all indices `1`): the étale lift
(`exists_equiv_of_red`) of the special-fibre form `D j`, for `(R' ⊗_R B)_g` formally étale over
the level `R'`, `g ∉ 𝔪 j`, and `J` nilpotent on `R'`. -/
theorem exists_levelEtale [Finite ι] (j : ι)
    (hεψ : ψ θ f (CompletionProd.idem hinj hf hrad j) =
      Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk j))
    (hd1 : ∀ i, (D j).d i = 1) {g : R} (hg : g ∉ 𝔪 j)
    [Algebra.FormallyEtale R' (Localization.Away (algebraMap R' (R' ⊗[R] B) (algebraMap R R' g)))]
    {m : ℕ} (hJm : J θ (R := R') ^ m = ⊥) :
    ∃ Φ : AdicCompletion (𝔪' j) R' ⊗[R] B ≃ₐ[AdicCompletion (𝔪' j) R']
        (∀ i : Fin (D j).r,
          AdjoinRoot (X ^ (D j).d i - C (algebraMap R (AdicCompletion (𝔪' j) R') s))),
      ∀ x, ρYe 𝔪 D e he hm j (Φ x) = ρXe 𝔪 D e he hm j x := by
  obtain ⟨hsurj, hker⟩ := redHat_surjective_ker 𝔪 hinjk hfk hradk e he hfe hinj hf hrad hm j hεψ
  set T' := AdicCompletion (𝔪' j) R'
  set I := RingHom.ker (redHat 𝔪 e he hm j)
  have hI : I ^ m = ⊥ := by
    rw [hker, ← Ideal.map_pow, hJm, Ideal.map_bot]
  -- `g` is a unit in `T'`
  have hgu : IsUnit (algebraMap R T' g) := by
    obtain ⟨w, hw⟩ := isUnit_Tn (𝔪 j) (hJ j) hg
    obtain ⟨y, hy⟩ := hsurj (↑w⁻¹)
    have hn : algebraMap R T' g * y - 1 ∈ I := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, AlgHom.commutes, hy, ← hw, Units.mul_inv,
        sub_self]
    have hnil : IsNilpotent (algebraMap R T' g * y - 1) := by
      refine ⟨m, ?_⟩
      have := Ideal.pow_mem_pow hn m
      rwa [hI, Ideal.mem_bot] at this
    have h1 : IsUnit (algebraMap R T' g * y) := by
      have := hnil.isUnit_add_one
      rwa [sub_add_cancel] at this
    exact isUnit_of_mul_isUnit_left h1
  have hgu' : IsUnit (algebraMap R' T' (algebraMap R R' g)) := by
    rwa [← IsScalarTower.algebraMap_apply]
  haveI : Algebra.FormallyEtale T' (T' ⊗[R] B) :=
    .of_equiv ((Algebra.TensorProduct.cancelBaseChange R R' T' T' B).symm.trans
      (tensorAwayEquiv _ hgu')).symm
  haveI : ∀ i, Algebra.FormallyEtale T'
      (AdjoinRoot (X ^ (D j).d i - C (algebraMap R T' s))) := fun i ↦
    .of_equiv ((Ideal.quotientEquivAlgOfEq T' (by rw [hd1 i])).trans
      (adjoinLinEquiv (algebraMap R T' s))).symm
  haveI : Algebra.FormallyEtale T'
      (∀ i : Fin (D j).r, AdjoinRoot (X ^ (D j).d i - C (algebraMap R T' s))) :=
    (Algebra.FormallyEtale.pi_iff _).2 inferInstance
  refine exists_equiv_of_red I hI (ρXe 𝔪 D e he hm j) ?_ ?_ (ρYe 𝔪 D e he hm j) ?_ ?_ ?_
  · exact (D j).Ψ.surjective.comp ((tensorCsEquiv (θ := θ) (B := B) (𝔪 j)).symm.surjective.comp
      (Algebra.TensorProduct.map_surjective _ _ hsurj fun b ↦ ⟨b, rfl⟩))
  · rw [ρXe, RingHom.ker_comp_of_injective _ (D j).Ψ.injective,
      RingHom.ker_comp_of_injective _ (tensorCsEquiv (θ := θ) (B := B) (𝔪 j)).symm.injective]
    exact Algebra.TensorProduct.rTensor_ker _ hsurj
  · intro z
    refine ⟨fun i ↦ (adjMap_surjective _ hsurj ((D j).d i) (red_s _ s) (z i)).choose,
      funext fun i ↦ ?_⟩
    exact (adjMap_surjective _ hsurj ((D j).d i) (red_s _ s) (z i)).choose_spec
  · ext y
    constructor
    · intro hy
      refine mem_map_pi I y fun i ↦ ?_
      have h1 : adjMap (redHat 𝔪 e he hm j).toRingHom ((D j).d i) (red_s _ s) (y i) = 0 :=
        congrFun (RingHom.mem_ker.mp hy) i
      rw [← RingHom.mem_ker, ker_adjMap _ hsurj] at h1
      exact h1
    · intro hy
      refine (Ideal.map_le_iff_le_comap.mpr ?_) hy
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      funext i
      change adjMap (redHat 𝔪 e he hm j).toRingHom ((D j).d i) (red_s _ s)
        (algebraMap (AdicCompletion (𝔪' j) R')
          (AdjoinRoot (X ^ (D j).d i - C (algebraMap R (AdicCompletion (𝔪' j) R') s))) a) = 0
      rw [AdjoinRoot.algebraMap_eq, adjMap_of, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        RingHom.mem_ker.mp ha, map_zero]
  · intro a
    have h1 : (Algebra.TensorProduct.map (redHat 𝔪 e he hm j) (AlgHom.id R B))
        (algebraMap T' (T' ⊗[R] B) a) =
        algebraMap (Tn θ (𝔪 j)) (Tn θ (𝔪 j) ⊗[R] B) (redHat 𝔪 e he hm j a) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.map_tmul, map_one]
      rfl
    change (D j).Ψ ((tensorCsEquiv (θ := θ) (B := B) (𝔪 j)).symm
      (Algebra.TensorProduct.map (redHat 𝔪 e he hm j) (AlgHom.id R B)
        (algebraMap T' (T' ⊗[R] B) a))) = _
    rw [h1, AlgEquiv.commutes, AlgEquiv.commutes]
    funext i
    change AdjoinRoot.of _ (redHat 𝔪 e he hm j a) = adjMap (redHat 𝔪 e he hm j).toRingHom
      ((D j).d i) (red_s _ s) (algebraMap (AdicCompletion (𝔪' j) R')
        (AdjoinRoot (X ^ (D j).d i - C (algebraMap R (AdicCompletion (𝔪' j) R') s))) a)
    rw [AdjoinRoot.algebraMap_eq, adjMap_of]
    rfl

/-- **The level form at a point where the cover is étale**, as a `LevelPointForm`. -/
def levelEtaleForm (j : ι)
    (hεψ : ψ θ f (CompletionProd.idem hinj hf hrad j) =
      Admissible.hatEquiv e hfe (CompletionProd.idem hinjk hfk hradk j))
    (hd1 : ∀ i, (D j).d i = 1) {g : R} (hg : g ∉ 𝔪 j)
    [Algebra.FormallyEtale R' (Localization.Away (algebraMap R' (R' ⊗[R] B) (algebraMap R R' g)))]
    {m : ℕ} (hJm : J θ (R := R') ^ m = ⊥) :
    LevelPointForm (redHat 𝔪 e he hm j) (D j) :=
  ⟨(exists_levelEtale 𝔪 hJ D hinjk hfk hradk e he hfe hinj hf hrad hm j hεψ hd1 hg hJm).choose,
    fun b i ↦ by
      have h1 := congrFun ((exists_levelEtale 𝔪 hJ D hinjk hfk hradk e he hfe hinj hf hrad hm j
        hεψ hd1 hg hJm).choose_spec ((1 : AdicCompletion (𝔪' j) R') ⊗ₜ b)) i
      rw [ρXe_one_tmul] at h1
      exact h1⟩

omit [IsNoetherianRing R] [Fintype ι] [DecidableEq ι] [IsScalarTower O R R']
  [IsNoetherianRing R'] [∀ j, (𝔪' j).IsMaximal] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- The reduction of the level lift `hatLift r` at the cusp is the special-fibre map `hatCₐ`
(the hypothesis of `levelCuspForm` for `red = redHat`). -/
theorem redHat_hatLift_cusp (j : ι) {E' : ℕ} (CN : CuspNormAtData O B s E' (𝔪 j))
    (hres : Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
    (r : CN.N₁ →ₐ[R] R' ⧸ 𝔪' j) (hr : ∀ z ∈ CN.𝔫, r z = 0) :
    (redHat 𝔪 e he hm j).comp (hatLift r) = hatCₐ (𝔪 j) (hJ j) hres CN := by
  refine hatHom_ext (cHsurj0 (𝔪 j) (hJ j) hres CN) _ _ (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · change resHat _ (CompletionMap.map (red θ e) (hm j) (hatLift r z)) = 0
    rw [resHat_map, resHat_hatLift, hr z hz, map_zero]
  · rw [hatCₐ_eq_hatLift, resHat_hatLift]
    exact resMap_eq_zero _ _ _ hz

end Assemble

end

end FormalCuspLevel

end SemistableReduction
