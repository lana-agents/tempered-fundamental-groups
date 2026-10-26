/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalCuspReduce
import TemperedFundamentalGroups.SemistableReduction.FormalCuspAssemble
import TemperedFundamentalGroups.SemistableReduction.FormalKummerChart
import TemperedFundamentalGroups.SemistableReduction.CuspTame

/-!
# The formal cusp form of the special fibre at a marked point (MR12 T2 S5.5, local step)

Let `R` be an `O`-algebra (a chart), `s ∈ R` the coordinate at the marked points, `B` an
`R`-algebra (the normalisation of the chart in a cover), `R̄ = R/J`, `C = B/JB`. Suppose that over
an étale `R`-algebra `N₁` with a prime `𝔫` over the marked point `𝔪`, with an `O[X]`-algebra
structure `X ↦ s`, `N₁ ⊗_R B ≅ ∏ᵢ N₁ ⊗_{O[X]} O[y]` (`X ↦ y ^ dᵢ`), and that the residue field
extension at `𝔫` is trivial. Then (**`FormalKummer.cuspEquiv`**)

  `R̂_𝔪 ⊗_{R̄} C ≅ ∏ᵢ R̂_𝔪[y]/(y ^ dᵢ − s̄)`

as `R̂_𝔪`-algebras: the reduced splitting (`cuspRedSplitEquiv`), base changed along
`N̄₁ → R̂_𝔪` (`toHat`, `baseChangeEquiv`), and `T ⊗_{k[X]} k[y] ≅ T[y]/(y ^ d − X)`
(`kpolyTensorEquiv`).
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

open AdmissibleLift Cusp

namespace FormalKummer

noncomputable section

/-! ### `T ⊗_{k[X]} k[y] ≅ T[y]/(y ^ d − X)` -/

section KPolyTensor

variable {k : Type u} [Field k] {T : Type u} [CommRing T] [Algebra k[X] T] {d : ℕ}

local notation "τ" => algebraMap k[X] T X

local notation "AR" => AdjoinRoot (X ^ d - C τ)

/-- `k[y] → T[y]/(y ^ d − X)`, `y ↦ y`. -/
def kpolyToAR : KPoly k d →+* AR :=
  eval₂RingHom ((algebraMap T AR).comp ((algebraMap k[X] T).comp C)) (AdjoinRoot.root _)

lemma root_pow : (AdjoinRoot.root (X ^ d - C τ)) ^ d = algebraMap T AR τ := by
  have h := AdjoinRoot.eval₂_root (X ^ d - C τ)
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  rw [sub_eq_zero] at h
  exact h

/-- `kpolyToAR` as a `k[X]`-algebra map. -/
def kpolyToARₐ : KPoly k d →ₐ[k[X]] AR :=
  { kpolyToAR with
    commutes' := fun p ↦ by
      change eval₂ ((algebraMap T AR).comp ((algebraMap k[X] T).comp C))
        (AdjoinRoot.root _) (expand k d p) = algebraMap k[X] AR p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add, eval₂_add, hp, hq, map_add]
      | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, expand_C, expand_X, eval₂_mul,
          eval₂_C, eval₂_pow, eval₂_X_pow, root_pow,
          map_mul, map_pow]
        simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply] }

lemma one_tmul_Y_pow : ((1 : T) ⊗ₜ[k[X]] (KPoly.Y : KPoly k d)) ^ d =
    algebraMap T (T ⊗[k[X]] KPoly k d) τ := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, KPoly.Y_pow, Algebra.algebraMap_eq_smul_one,
    ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  rfl

/-- `T[y]/(y ^ d − X) → T ⊗_{k[X]} k[y]`, `y ↦ 1 ⊗ y`. -/
def arToTensor : AR →ₐ[T] T ⊗[k[X]] KPoly k d :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId T _) ((1 : T) ⊗ₜ KPoly.Y) (by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [one_tmul_Y_pow]
    exact sub_self _)

lemma arToTensor_root : arToTensor (AdjoinRoot.root (X ^ d - C τ)) =
    (1 : T) ⊗ₜ[k[X]] (KPoly.Y : KPoly k d) := AdjoinRoot.liftAlgHom_root ..

lemma kpoly_algebraMap_C (c : k) :
    algebraMap k[X] (KPoly k d) (C c) = algebraMap k (KPoly k d) c := by
  rw [KPoly.algebraMap_eq, expand_C]
  change C c = algebraMap k k[X] c
  rw [Polynomial.algebraMap_eq]

lemma arToTensor_kpoly (b : KPoly k d) :
    arToTensor (kpolyToAR b) = (1 : T) ⊗ₜ[k[X]] b := by
  have h : (arToTensor (T := T) (d := d)).toRingHom.comp kpolyToAR =
      (Algebra.TensorProduct.includeRight (R := k[X]) (A := T)
        (B := KPoly k d)).toRingHom := by
    refine @Polynomial.ringHom_ext k _ _ _ _ _ (fun c ↦ ?_) ?_
    · change arToTensor (eval₂ ((algebraMap T AR).comp ((algebraMap k[X] T).comp C))
        (AdjoinRoot.root _) (C c)) = (1 : T) ⊗ₜ[k[X]] (algebraMap k (KPoly k d) c)
      rw [eval₂_C, RingHom.comp_apply, RingHom.comp_apply, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one (R := k[X]) (A := T), Algebra.algebraMap_self,
        RingHom.id_apply, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
        kpoly_algebraMap_C]
    · change arToTensor (eval₂ ((algebraMap T AR).comp ((algebraMap k[X] T).comp C))
        (AdjoinRoot.root _) X) = (1 : T) ⊗ₜ[k[X]] (KPoly.Y : KPoly k d)
      rw [eval₂_X, arToTensor_root]
  exact RingHom.congr_fun h b

/-- **`T ⊗_{k[X]} k[y] ≅ T[y]/(y ^ d − X)`** (`X ↦ y ^ d`). -/
def kpolyTensorEquiv : T ⊗[k[X]] KPoly k d ≃ₐ[T] AR :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId T AR) kpolyToARₐ fun _ _ ↦ Commute.all _ _)
    arToTensor
    (AdjoinRoot.algHom_ext (by
      simp only [AlgHom.coe_comp, Function.comp_apply, arToTensor_root, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact Polynomial.eval₂_X _ _))
    (Algebra.TensorProduct.ext' fun a b ↦ by
      simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.lift_tmul,
        map_mul, AlgHom.coe_id, id_eq]
      change arToTensor (algebraMap T AR a) * arToTensor (kpolyToAR b) = _
      rw [AlgHom.commutes, arToTensor_kpoly, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl)

lemma kpolyTensorEquiv_tmul_one (a : T) :
    kpolyTensorEquiv (a ⊗ₜ[k[X]] (1 : KPoly k d)) = AdjoinRoot.of _ a := by
  simp [kpolyTensorEquiv, AlgEquiv.ofAlgHom_apply, Algebra.ofId_apply]

end KPolyTensor

/-- `T[y]/(yⁿ − a) ≅ T[y]/(yⁿ − b)` for `a = b`, over `T`. -/
def adjoinPowCongr {T : Type u} [CommRing T] (n : ℕ) {a b : T} (h : a = b) :
    AdjoinRoot (X ^ n - C a) ≃ₐ[T] AdjoinRoot (X ^ n - C b) :=
  AlgEquiv.ofRingEquiv (f := adjoinPowEquiv (RingEquiv.refl T) n h) fun x ↦ by
    change adjoinPowEquiv (RingEquiv.refl T) n h (AdjoinRoot.of _ x) = AdjoinRoot.of _ x
    rw [adjoinPowEquiv_of]
    rfl

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]

attribute [local instance] algRN

section CuspNode

variable {N₁ : Type u} [CommRing N₁] [Algebra R N₁] [Algebra O N₁] [IsScalarTower O R N₁]
  [Algebra O[X] N₁] [IsScalarTower O O[X] N₁] {r : ℕ} {d : Fin r → ℕ}

/-- **The reduced cusp splitting** `N̄₁ ⊗_{R̄} C ≅ ∏ᵢ N̄₁ ⊗_{k[X]} k[y]`. -/
def cuspRedSplitEquiv (Φ : N₁ ⊗[R] B ≃ₐ[N₁] ∀ i, CuspNormalFactor O (d i) N₁) :
    Ns θ N₁ ⊗[Rs θ R] Cs θ R B ≃ₐ[Ns θ N₁] ∀ i, RedCusp θ N₁ (d i) :=
  AlgEquiv.ofRingEquiv (f := (tensorQuot (θ := θ)).symm.trans
    ((Ideal.quotEquivOfEq (KT_eq_JX (θ := θ) (R := R) (N₁ := N₁) (B := B))).trans
      (cuspSplitEquiv Φ))) (by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h1 : (tensorQuot (θ := θ)).symm (algebraMap (Ns θ N₁) (Ns θ N₁ ⊗[Rs θ R] Cs θ R B)
        (Ideal.Quotient.mk _ a)) = Ideal.Quotient.mk _ (a ⊗ₜ (1 : B)) := by
      rw [RingEquiv.symm_apply_eq, tensorQuot_mk_tmul, map_one]
      rfl
    simp only [RingEquiv.trans_apply]
    rw [h1, Ideal.quotEquivOfEq_mk]
    funext i
    exact cuspSplitEquiv_algebraMap Φ a i)

variable (θ) in
/-- `k[X] → R̄`, `X ↦ s̄`. -/
def sBar (s : R) : k[X] →+* Rs θ R :=
  eval₂RingHom (algebraMap k (Rs θ R)) (Ideal.Quotient.mk _ s)

omit [IsScalarTower O O[X] N₁] in
lemma cuspBar_eq {s : R} (hs : algebraMap O[X] N₁ X = algebraMap R N₁ s) (a : k[X]) :
    cuspBar θ N₁ a = algebraMap (Rs θ R) (Ns θ N₁) (sBar θ s a) := by
  have := Polynomial.ringHom_ext (f := cuspBar θ N₁)
    (g := (algebraMap (Rs θ R) (Ns θ N₁)).comp (sBar θ s))
    (fun c ↦ by
      obtain ⟨o, rfl⟩ := hθ.out c
      simp only [cuspBar, sBar, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C,
        QuadNodeTower.algK_θ, algebraMap_RN]
      rw [← IsScalarTower.algebraMap_apply])
    (by
      simp only [cuspBar, sBar, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, algebraMap_RN]
      rw [hs])
  exact RingHom.congr_fun this a

variable (𝔪s : Ideal (Rs θ R)) (𝔫s : Ideal (Ns θ N₁))
  (hcomap : 𝔫s.comap (algebraMap (Rs θ R) (Ns θ N₁)) = 𝔪s)
  (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫s).comp (algebraMap (Rs θ R) (Ns θ N₁))))

/-- The `k[X]`-algebra structure `X ↦ s̄` on the completion. -/
abbrev sAlg (s : R) : Algebra k[X] (AdicCompletion 𝔪s (Rs θ R)) :=
  ((algebraMap (Rs θ R) (AdicCompletion 𝔪s (Rs θ R))).comp (sBar θ s)).toAlgebra

/-- **The formal cusp form of the special fibre at a marked point**:
`R̂_𝔪 ⊗_{R̄} C ≅ ∏ᵢ R̂_𝔪[y]/(y ^ dᵢ − s̄)`. -/
def cuspEquiv [Algebra.FormallyEtale R N₁] {s : R}
    (hs : algebraMap O[X] N₁ X = algebraMap R N₁ s)
    (Φ : N₁ ⊗[R] B ≃ₐ[N₁] ∀ i, CuspNormalFactor O (d i) N₁) :
    AdicCompletion 𝔪s (Rs θ R) ⊗[Rs θ R] Cs θ R B ≃ₐ[AdicCompletion 𝔪s (Rs θ R)]
      ∀ i, AdjoinRoot (X ^ d i - C (algebraMap (Rs θ R) (AdicCompletion 𝔪s (Rs θ R))
        (Ideal.Quotient.mk _ s))) :=
  letI := cuspBarAlg θ N₁
  letI := sAlg 𝔪s s
  (baseChangeEquiv (A := fun _ : Fin r ↦ k[X]) (Bk := fun i ↦ KPoly k (d i))
    (toHat 𝔪s 𝔫s hcomap hsurj) (fun _ ↦ sBar θ s) (fun _ a ↦ cuspBar_eq hs a)
    (fun _ _ ↦ rfl) (cuspRedSplitEquiv Φ)).trans
    (AlgEquiv.piCongrRight fun i ↦ kpolyTensorEquiv.trans (adjoinPowCongr (d i) (by
      change algebraMap (Rs θ R) _ (sBar θ s X) = _
      simp [sBar])))

end CuspNode

/-- The local formal cusp form at a point `𝔪` of the special fibre: `R̂_𝔪 ⊗_{R̄} C` is a product of
`R̂_𝔪[y]/(y ^ dᵢ − s̄)`, `0 < dᵢ ∣ e`. -/
def PointCuspForm (s : R) (e : ℕ) (𝔪 : Ideal R) : Prop :=
  ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, 0 < d i) ∧ (∀ i, d i ∣ e) ∧
    Nonempty (Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B ≃ₐ[Tn θ 𝔪]
      ∀ i, AdjoinRoot (X ^ d i - C (algebraMap (Rs θ R) (Tn θ 𝔪) (Ideal.Quotient.mk _ s))))

/-- **The local formal cusp form as data** (refactor R1): the indices `dᵢ ∣ e` and the
isomorphism `Ψ : R̂_𝔪 ⊗_{R̄} C ≅ ∏ᵢ R̂_𝔪[y]/(y ^ dᵢ − s̄)`. -/
structure PointCuspFormData (s : R) (e : ℕ) (𝔪 : Ideal R) where
  /-- The number of factors. -/
  r : ℕ
  /-- The ramification indices. -/
  d : Fin r → ℕ
  hd : ∀ i, 0 < d i
  hde : ∀ i, d i ∣ e
  /-- The local formal cusp form. -/
  Ψ : Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B ≃ₐ[Tn θ 𝔪]
    ∀ i, AdjoinRoot (X ^ d i - C (algebraMap (Rs θ R) (Tn θ 𝔪) (Ideal.Quotient.mk _ s)))

/-- Chosen data of a local formal cusp form. -/
def PointCuspFormData.ofPointCuspForm {s : R} {e : ℕ} {𝔪 : Ideal R}
    (h : PointCuspForm (θ := θ) (B := B) s e 𝔪) : PointCuspFormData (θ := θ) (B := B) s e 𝔪 :=
  Classical.choice (by
    obtain ⟨r, d, hd, hde, ⟨Ψ⟩⟩ := h
    exact ⟨⟨r, d, hd, hde, Ψ⟩⟩)

omit hθ in
lemma PointCuspFormData.pointCuspForm {s : R} {e : ℕ} {𝔪 : Ideal R}
    (D : PointCuspFormData (θ := θ) (B := B) s e 𝔪) : PointCuspForm (θ := θ) (B := B) s e 𝔪 :=
  ⟨D.r, D.d, D.hd, D.hde, ⟨D.Ψ⟩⟩

/-- Weakening the bound on the indices. -/
def PointCuspFormData.mono {s : R} {e e' : ℕ} (hee' : e ∣ e') {𝔪 : Ideal R}
    (D : PointCuspFormData (θ := θ) (B := B) s e 𝔪) : PointCuspFormData (θ := θ) (B := B) s e' 𝔪 :=
  { D with hde := fun i ↦ (D.hde i).trans hee' }

/-- **The data of `IsCuspNormAt` as a type** (refactor R1): an étale neighbourhood `N₁ ⊇ 𝔫` of
`𝔪`, an étale cusp chart `O[X] → N₁`, `X ↦ s`, and the splitting `Φ` of `N₁ ⊗_R B` into
normalised cusp Kummer factors. -/
structure CuspNormAtData (O : Type u) [CommRing O] {R : Type u} [CommRing R] [Algebra O R]
    (B : Type u) [CommRing B] [Algebra R B] (s : R) (e : ℕ) (𝔪 : Ideal R) where
  /-- The étale neighbourhood. -/
  N₁ : Type u
  [commRing : CommRing N₁]
  [algebra : Algebra R N₁]
  [etale : Algebra.Etale R N₁]
  /-- The point of `N₁` over `𝔪`. -/
  𝔫 : Ideal N₁
  [isPrime : 𝔫.IsPrime]
  comap_eq : 𝔫.comap (algebraMap R N₁) = 𝔪
  /-- The cusp chart. -/
  polyAlg : Algebra O[X] N₁
  tower : letI : Algebra O N₁ := ((algebraMap R N₁).comp (algebraMap O R)).toAlgebra
    letI := polyAlg
    IsScalarTower O O[X] N₁
  hX : letI := polyAlg
    algebraMap O[X] N₁ X = algebraMap R N₁ s
  /-- The number of factors. -/
  r : ℕ
  /-- The ramification indices. -/
  d : Fin r → ℕ
  hd : ∀ i, 0 < d i
  hde : ∀ i, d i ∣ e
  /-- The splitting. -/
  Φ : letI : Algebra O N₁ := ((algebraMap R N₁).comp (algebraMap O R)).toAlgebra
    letI := polyAlg
    N₁ ⊗[R] B ≃ₐ[N₁] ∀ i, CuspNormalFactor O (d i) N₁

attribute [instance] CuspNormAtData.commRing CuspNormAtData.algebra CuspNormAtData.etale
  CuspNormAtData.isPrime

/-- **The chosen data of `IsCuspNormAt`.** -/
def CuspNormAtData.ofIsCuspNormAt {s : R} {e : ℕ} {𝔪 : Ideal R} (h : IsCuspNormAt O e s B 𝔪) :
    CuspNormAtData O B s e 𝔪 :=
  Classical.choice (by
    obtain ⟨N₁, _, _, _, 𝔫, _, h𝔫, hdata⟩ := h
    letI : Algebra O N₁ := ((algebraMap R N₁).comp (algebraMap O R)).toAlgebra
    obtain ⟨palg, hT, hX, -, -, r, d, hd, hde, ⟨Φ⟩⟩ := hdata
    exact ⟨{ N₁ := N₁, 𝔫 := 𝔫, comap_eq := h𝔫, polyAlg := palg, tower := hT, hX := hX, r := r,
             d := d, hd := hd, hde := hde, Φ := Φ }⟩)

/-- **The local formal cusp form at a marked point with separably closed residue field**, defined
from the data `D` (`cuspEquiv` for the splitting `D.Φ`). -/
def pointCuspFormDataOf [IsSepClosed k] {s : R} {e : ℕ}
    (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
    (D : CuspNormAtData O B s e 𝔪) : PointCuspFormData (θ := θ) (B := B) s e 𝔪 :=
  letI : Algebra O D.N₁ := ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra
  haveI : IsScalarTower O R D.N₁ := IsScalarTower.of_algebraMap_eq' rfl
  letI := D.polyAlg
  haveI : IsScalarTower O O[X] D.N₁ := D.tower
  have hJ𝔫 : J θ (R := D.N₁) ≤ D.𝔫 := by
    rw [← J_N₁_eq θ R D.N₁, Ideal.map_le_iff_le_comap, D.comap_eq]
    exact hJ
  have hcomap : (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁)))).comap
      (algebraMap (Rs θ R) (Ns θ D.N₁)) = sIdeal (θ := θ) 𝔪 := by
    ext z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.mem_comap, algebraMap_RN, Ideal.mem_quotient_iff_mem hJ𝔫,
      Ideal.mem_quotient_iff_mem hJ, ← Ideal.mem_comap, D.comap_eq]
  have hρ : Function.Surjective ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R))) := by
    intro z
    obtain ⟨o, ho⟩ := hres z
    refine ⟨θ o, ?_⟩
    rw [RingHom.comp_apply, QuadNodeTower.algK_θ, Ideal.Quotient.factor_mk]
    exact ho
  have hsurj0 := EtaleResidue.surjective_of_isSepClosed' 𝔪 D.𝔫 D.comap_eq
    ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R))) hρ
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁))))).comp
        (algebraMap (Rs θ R) (Ns θ D.N₁))) := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hsurj0 (Ideal.Quotient.mk D.𝔫 z)
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    simp only [RingHom.comp_apply] at ha ⊢
    rw [Ideal.Quotient.eq] at ha ⊢
    rw [algebraMap_RN, ← map_sub]
    exact Ideal.mem_map_of_mem _ ha
  { r := D.r, d := D.d, hd := D.hd, hde := D.hde,
    Ψ := cuspEquiv (sIdeal 𝔪) _ hcomap hsurj D.hX D.Φ }

/-- **The local formal cusp form at a marked point with separably closed residue field**, from
the normalisation-level tame cusp predicate. -/
theorem pointCuspForm_of_isCuspNormAt [IsSepClosed k] {s : R} {e : ℕ}
    (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
    (h : IsCuspNormAt O e s B 𝔪) : PointCuspForm (θ := θ) (B := B) s e 𝔪 :=
  (pointCuspFormDataOf 𝔪 hJ hres (CuspNormAtData.ofIsCuspNormAt h)).pointCuspForm

/-- **The formal cusp form of the special fibre of a chart along its marked points**, defined
from chosen local data `D j` (`assembleCuspEquiv`; refactor R1). -/
def cuspEquivOf [IsNoetherianRing R] {s : R} {ι : Type} [Fintype ι] [DecidableEq ι]
    {e : ι → ℕ} (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal] (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
    (D : ∀ j, PointCuspFormData (θ := θ) (B := B) s (e j) (𝔪 j)) {f : Rs θ R}
    (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
    (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
    (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
    (ψ : Polynomial k →ₐ[k] Admissible.Hat f)
    (hψ : ψ X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s)) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    Admissible.Hat f ⊗[Rs θ R] Cs θ R B ≃ₐ[Admissible.Hat f]
      ∀ p : (Σ j, Fin (D j).r), Admissible.CuspPiece ψ
        (CompletionProd.idem hinj hf hrad p.1) ((D p.1).d p.2) :=
  haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  assembleCuspEquiv (r := fun j ↦ (D j).r) (d := fun j ↦ (D j).d) hinj hf hrad ψ hψ
    fun j ↦ (D j).Ψ

/-- **The formal cusp form of the special fibre of a chart along its marked points**: if the zero
set of `f̄` on the special fibre consists of the points `𝔪ⱼ` and at each of them the local formal
cusp form holds (`PointCuspForm`, e.g. `pointCuspForm_of_isCuspNormAt`), then
`R̂ ⊗_{R̄} C ≅ ∏_{(j, i)} Admissible.CuspPiece ψ εⱼ dⱼᵢ` for any formal coordinate `ψ` with
`ψ X = s̄`: the cusp part of the `kummer` field of `Admissible.Covering`. -/
theorem exists_cusp [IsNoetherianRing R] {s : R} {e : ℕ} {ι : Type} [Finite ι] [DecidableEq ι]
    (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal] (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
    (hloc : ∀ j, PointCuspForm (θ := θ) (B := B) s e (𝔪 j)) {f : Rs θ R}
    (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
    (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
    (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
    (ψ : Polynomial k →ₐ[k] Admissible.Hat f)
    (hψ : ψ X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s)) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    ∃ (r : ι → ℕ) (d : ∀ j, Fin (r j) → ℕ), (∀ j i, 0 < d j i) ∧ (∀ j i, d j i ∣ e) ∧
      Nonempty (Admissible.Hat f ⊗[Rs θ R] Cs θ R B ≃ₐ[Admissible.Hat f]
        ∀ p : (Σ j, Fin (r j)), Admissible.CuspPiece ψ
          (CompletionProd.idem hinj hf hrad p.1) (d p.1 p.2)) := by
  haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  haveI := Fintype.ofFinite ι
  choose r d hd hde Ψ using hloc
  exact ⟨r, d, hd, hde, ⟨assembleCuspEquiv hinj hf hrad ψ hψ fun j ↦ (Ψ j).some⟩⟩

end

end FormalKummer

end SemistableReduction
