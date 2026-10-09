/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Action
import TemperedFundamentalGroups.Setup.SmoothNormal

/-!
# Comparison of the function fields of a cover under extension of constants

Blueprint §9.7a (W10 assembly, step 2). In the setting of `W10Fields` (`A` finite torsion-free over
`K[X]`, `M / K` a field extension):

* **(1)** `tensorEquiv : M ⊗[K] A ≃ₐ[M] BX K M A` (`BX = M[X] ⊗[K[X]] A` is a base change of `A`
  along `K → M`, `isPushout_BX`), compatible with the actions (`tensorEquiv_congr`);
* **(2)** if `A` is smooth over `K`, then `BX` is reduced (`isReduced_BX`) and integrally closed in
  `LX` (`isIntegrallyClosedIn_BX`) (`SmoothNormal`);
* **(3)** for `K ⊆ E ⊆ C`: `LX_C = C(X) ⊗_{E(X)} LX_E` (`isPushout_compare`, from
  `LX = M(X) ⊗_{K[X]} A`, `isPushout_LX`); every element of `LX_C` (`exists_finset_LX`), resp.
  every finite subset of a component (`exists_finset_range_compMap`), is defined over every `E`
  containing a finite set of constants; and for `E` containing a suitable finite set of constants
  the contraction `contrMax` of maximal ideals is bijective and `C(X) ⊗_{E(X)} Comp_E ≃ Comp_C`
  (`compBaseChange`), so the degrees agree (`exists_finset_compare`,
  `exists_finset_compare_of_smooth`). The abstract part (`ReducedBaseChange`): for a base change
  `L' = F' ⊗_F L` of finite reduced algebras over fields such that the primitive idempotents of
  `L'` come from `L`, contraction is bijective and `F' ⊗_F (L ⧸ 𝔪) ≃ L' ⧸ 𝔪'` (by counting
  degrees).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace W10Fields

attribute [local instance] polyAlgebra

section Tensor

variable (K : Type u) [Field K] (M : Type u) [Field M] [Algebra K M]
  (A : Type u) [CommRing A] [Algebra K[X] A]

namespace BX

/-- `M → M ⊗_K A`. -/
noncomputable instance algebraM : Algebra M (BX K M A) :=
  ((algebraMap M[X] (BX K M A)).comp Polynomial.C).toAlgebra

noncomputable instance algebraK : Algebra K (BX K M A) :=
  ((algebraMap M (BX K M A)).comp (algebraMap K M)).toAlgebra

noncomputable instance algebraKX : Algebra K[X] (BX K M A) :=
  inferInstanceAs (Algebra K[X] (M[X] ⊗[K[X]] A))

noncomputable instance algebraA : Algebra A (BX K M A) :=
  Algebra.TensorProduct.rightAlgebra

lemma algebraMap_A (a : A) : algebraMap A (BX K M A) a = ofA K M A a := rfl

lemma algebraMap_M (m : M) : algebraMap M (BX K M A) m = algebraMap M[X] (BX K M A) (C m) := rfl

instance : IsScalarTower M M[X] (BX K M A) := .of_algebraMap_eq' rfl

instance : IsScalarTower K M (BX K M A) := .of_algebraMap_eq' rfl

instance : IsScalarTower K[X] M[X] (BX K M A) :=
  inferInstanceAs (IsScalarTower K[X] M[X] (M[X] ⊗[K[X]] A))

instance : IsScalarTower K[X] A (BX K M A) :=
  Algebra.TensorProduct.right_isScalarTower

instance : IsScalarTower K M[X] (BX K M A) := .of_algebraMap_eq fun k ↦ by
  rw [Polynomial.algebraMap_apply]
  rfl

variable [Algebra K A] [IsScalarTower K K[X] A]

instance : IsScalarTower K A (BX K M A) := .of_algebraMap_eq fun k ↦ by
  rw [IsScalarTower.algebraMap_apply K K[X] A, ← IsScalarTower.algebraMap_apply K[X] A (BX K M A),
    IsScalarTower.algebraMap_apply K[X] M[X] (BX K M A)]
  change _ = algebraMap M[X] (BX K M A) ((C k).map (algebraMap K M))
  rw [Polynomial.map_C]
  rfl

end BX

variable [Algebra K A] [IsScalarTower K K[X] A]

/-- **`M ⊗_K A` is `M[X] ⊗_{K[X]} A`.** -/
instance isPushout_BX : Algebra.IsPushout K M A (BX K M A) := by
  haveI : Algebra.IsPushout K[X] A M[X] (BX K M A) :=
    TensorProduct.isPushout' (R := K[X]) (S := M[X]) (T := A)
  haveI : Algebra.IsPushout K K[X] M M[X] := inferInstance
  exact Algebra.IsPushout.symm
    ((Algebra.IsPushout.comp_iff K K[X] M (S' := M[X]) (T := A) (T' := BX K M A)).2 inferInstance)

/-- **(1)** `M ⊗_K A ≃ M[X] ⊗_{K[X]} A`. -/
noncomputable def tensorEquiv : M ⊗[K] A ≃ₐ[M] BX K M A :=
  Algebra.IsPushout.equiv K M A (BX K M A)

variable {K M A}

lemma tensorEquiv_tmul (m : M) (a : A) :
    tensorEquiv K M A (m ⊗ₜ a) = algebraMap M[X] (BX K M A) (C m) * BX.ofA K M A a :=
  Algebra.IsPushout.equiv_tmul (R := K) (S := M) (R' := A) (S' := BX K M A) m a

lemma tensorEquiv_one_tmul (a : A) : tensorEquiv K M A (1 ⊗ₜ a) = BX.ofA K M A a := by
  rw [tensorEquiv_tmul, map_one, map_one, one_mul]

lemma tensorEquiv_tmul_one (m : M) :
    tensorEquiv K M A (m ⊗ₜ 1) = algebraMap M[X] (BX K M A) (C m) := by
  rw [tensorEquiv_tmul, map_one, mul_one]

/-- **(1)** `tensorEquiv` intertwines the actions of `(τ, g)`. -/
theorem tensorEquiv_congr (τ : M ≃ₐ[K] M) (g : A ≃ₐ[K[X]] A) (x : M ⊗[K] A) :
    tensorEquiv K M A (Algebra.TensorProduct.congr τ (g.restrictScalars K) x) =
      bxEquiv K M A τ g (tensorEquiv K M A x) := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul m a =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, tensorEquiv_tmul,
      tensorEquiv_tmul, map_mul, bxEquiv_algebraMap, bxEquiv_ofA, Polynomial.map_C]
    rfl

end Tensor

section Smooth

variable (K : Type u) [Field K] (M : Type u) [Field M] [Algebra K M]
  (A : Type u) [CommRing A] [Algebra K[X] A] [Algebra K A] [IsScalarTower K K[X] A]
  [Algebra.Smooth K A]

instance smooth_BX : Algebra.Smooth M (BX K M A) :=
  Algebra.Smooth.of_equiv (tensorEquiv K M A)

/-- **(2)** If `A` is smooth over `K`, then `M ⊗_K A` is reduced. -/
theorem isReduced_BX : IsReduced (BX K M A) :=
  TemperedFundamentalGroups.SmoothNormal.isReduced_of_smooth M (BX K M A)

/-- **(2)** If `A` is smooth over `K`, then `M ⊗_K A` is integrally closed in `LX`. -/
theorem isIntegrallyClosedIn_BX [Module.Finite K[X] A] [Module.IsTorsionFree K[X] A] :
    IsIntegrallyClosedIn (BX K M A) (LX K M A) :=
  TemperedFundamentalGroups.SmoothNormal.isIntegrallyClosedIn_of_smooth M _
    (algebraMapSubmonoid_le K M A)

end Smooth

end W10Fields

/-! ### Components under base change of a finite reduced algebra -/

namespace ReducedArtinian

variable {L : Type*} [CommRing L] [IsArtinianRing L] [IsReduced L]

instance (𝔪 : MaximalSpectrum L) : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal

open scoped Classical in
/-- The primitive idempotent of the component `𝔪` of a reduced artinian ring. -/
noncomputable def idem (𝔪 : MaximalSpectrum L) : L :=
  (IsArtinianRing.equivPi L).symm (Pi.single 𝔪 1)

open scoped Classical in
lemma mk_idem (𝔪 𝔫 : MaximalSpectrum L) :
    Ideal.Quotient.mk 𝔫.asIdeal (idem 𝔪) = if 𝔫 = 𝔪 then 1 else 0 := by
  have := IsArtinianRing.equivPi_apply L (idem 𝔪) 𝔫
  rw [idem, AlgEquiv.apply_symm_apply] at this
  rw [idem, ← this]
  split_ifs with h
  · subst h; exact Pi.single_eq_same (M := fun 𝔪 : MaximalSpectrum L ↦ L ⧸ 𝔪.asIdeal) _ _
  · exact Pi.single_eq_of_ne (M := fun 𝔪 : MaximalSpectrum L ↦ L ⧸ 𝔪.asIdeal) h _

end ReducedArtinian

namespace ReducedBaseChange

variable {F F' L L' : Type*} [Field F] [Field F'] [CommRing L] [CommRing L'] [Algebra F F']
  [Algebra F L] [Algebra F' L'] [Algebra L L'] [Algebra F L'] [IsScalarTower F L L']
  [IsScalarTower F F' L'] [Algebra.IsPushout F F' L L'] [Module.Finite F L] [Module.Finite F' L']
  [IsArtinianRing L] [IsArtinianRing L']

instance (𝔪 : MaximalSpectrum L) : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal

variable (L L') in
/-- The contraction of a maximal ideal of `L'` (a maximal ideal: `L` is artinian). -/
def contr (𝔪' : MaximalSpectrum L') : MaximalSpectrum L :=
  ⟨𝔪'.asIdeal.comap (algebraMap L L'), IsArtinianRing.isMaximal_of_isPrime _⟩

omit [IsArtinianRing L'] in
lemma contr_asIdeal (𝔪' : MaximalSpectrum L') :
    (contr L L' 𝔪').asIdeal = 𝔪'.asIdeal.comap (algebraMap L L') := rfl

variable (F L L') in
/-- `L ⧸ 𝔪 → L' ⧸ 𝔪'` for `𝔪 = 𝔪' ∩ L`. -/
noncomputable def quotMap (𝔪' : MaximalSpectrum L') :
    L ⧸ (contr L L' 𝔪').asIdeal →ₐ[F] L' ⧸ 𝔪'.asIdeal :=
  Ideal.quotientMapₐ 𝔪'.asIdeal (IsScalarTower.toAlgHom F L L') le_rfl

omit [Module.Finite F L] [IsArtinianRing L'] in
lemma quotMap_mk (𝔪' : MaximalSpectrum L') (x : L) :
    quotMap F L L' 𝔪' (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap L L' x) := rfl

omit [Algebra.IsPushout F F' L L'] [Module.Finite F L] [Module.Finite F' L']
  [IsArtinianRing L'] in
/-- `L ⧸ 𝔪 → L' ⧸ 𝔪'` is semilinear over `F → F'`. -/
lemma quotMap_algebraMap (𝔪' : MaximalSpectrum L') (φ : F) :
    quotMap F L L' 𝔪' (algebraMap F _ φ) = algebraMap F' _ (algebraMap F F' φ) := by
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

variable (F F' L L') in
/-- `F' ⊗_F (L ⧸ 𝔪) → L' ⧸ 𝔪'`. -/
noncomputable def baseChangeMap (𝔪' : MaximalSpectrum L') :
    F' ⊗[F] (L ⧸ (contr L L' 𝔪').asIdeal) →ₐ[F'] L' ⧸ 𝔪'.asIdeal :=
  Algebra.TensorProduct.lift (Algebra.ofId F' _) (quotMap F L L' 𝔪') fun _ _ ↦ Commute.all _ _

omit [Module.Finite F L] [Module.Finite F' L'] [IsArtinianRing L'] in
lemma baseChangeMap_surjective (𝔪' : MaximalSpectrum L') :
    Function.Surjective (baseChangeMap F F' L L' 𝔪') := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨w, rfl⟩ := (Algebra.IsPushout.equiv F F' L L').surjective y
  induction w with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, map_add, map_add]⟩
  | tmul φ l =>
    refine ⟨φ ⊗ₜ Ideal.Quotient.mk _ l, ?_⟩
    rw [baseChangeMap, Algebra.TensorProduct.lift_tmul, Algebra.IsPushout.equiv_tmul, map_mul,
      quotMap_mk]
    rfl

variable [IsReduced L] [IsReduced L']
  (H : ∀ 𝔪' : MaximalSpectrum L', ReducedArtinian.idem 𝔪' ∈ (algebraMap L L').range)

include H in
omit [IsReduced L] in
lemma contr_injective : Function.Injective (contr L L') := by
  classical
  intro 𝔪₁ 𝔪₂ h
  by_contra hne
  obtain ⟨x, hx⟩ := H 𝔪₁
  have h1 : x ∉ (contr L L' 𝔪₁).asIdeal := by
    rw [contr_asIdeal, Ideal.mem_comap, hx, ← Ideal.Quotient.eq_zero_iff_mem,
      ReducedArtinian.mk_idem, if_pos rfl]
    exact one_ne_zero
  have h2 : x ∈ (contr L L' 𝔪₂).asIdeal := by
    rw [contr_asIdeal, Ideal.mem_comap, hx, ← Ideal.Quotient.eq_zero_iff_mem,
      ReducedArtinian.mk_idem, if_neg (Ne.symm hne)]
  exact h1 (h ▸ h2)

omit [IsReduced L] [IsReduced L'] [Module.Finite F' L'] [IsArtinianRing L'] in
lemma finrank_quot_le (𝔪' : MaximalSpectrum L') :
    Module.finrank F' (L' ⧸ 𝔪'.asIdeal) ≤ Module.finrank F (L ⧸ (contr L L' 𝔪').asIdeal) := by
  have := LinearMap.finrank_le_finrank_of_surjective
    (f := (baseChangeMap F F' L L' 𝔪').toLinearMap) (baseChangeMap_surjective 𝔪')
  rwa [Module.finrank_baseChange] at this

include H in
theorem key : Function.Surjective (contr L L') ∧ ∀ 𝔪' : MaximalSpectrum L',
    Module.finrank F' (L' ⧸ 𝔪'.asIdeal) = Module.finrank F (L ⧸ (contr L L' 𝔪').asIdeal) := by
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum L)
  haveI := Fintype.ofFinite (MaximalSpectrum L')
  set d := fun 𝔪' : MaximalSpectrum L' ↦ Module.finrank F' (L' ⧸ 𝔪'.asIdeal) with hd
  set δ := fun 𝔪 : MaximalSpectrum L ↦ Module.finrank F (L ⧸ 𝔪.asIdeal) with hδ
  have hfinL : Module.finrank F L = ∑ 𝔪, δ 𝔪 := by
    rw [((IsArtinianRing.equivPi L).restrictScalars F).toLinearEquiv.finrank_eq,
      Module.finrank_pi_fintype]
  have hfinL' : Module.finrank F' L' = ∑ 𝔪', d 𝔪' := by
    rw [((IsArtinianRing.equivPi L').restrictScalars F').toLinearEquiv.finrank_eq,
      Module.finrank_pi_fintype]
  have hbc : Module.finrank F' L' = Module.finrank F L := by
    rw [← (Algebra.IsPushout.equiv F F' L L').toLinearEquiv.finrank_eq, Module.finrank_baseChange]
  have hle : ∀ 𝔪', d 𝔪' ≤ δ (contr L L' 𝔪') := finrank_quot_le
  have hpos : ∀ 𝔪, 0 < δ 𝔪 := fun 𝔪 ↦ Module.finrank_pos
  have himg : ∑ 𝔪', δ (contr L L' 𝔪') = ∑ 𝔪 ∈ Finset.univ.image (contr L L'), δ 𝔪 :=
    (Finset.sum_image fun x _ y _ h ↦ contr_injective H h).symm
  have hsub : ∑ 𝔪 ∈ Finset.univ.image (contr L L'), δ 𝔪 ≤ ∑ 𝔪, δ 𝔪 :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hchain : ∑ 𝔪', d 𝔪' ≤ ∑ 𝔪', δ (contr L L' 𝔪') := Finset.sum_le_sum fun i _ ↦ hle i
  have htot : ∑ 𝔪', d 𝔪' = ∑ 𝔪, δ 𝔪 := by rw [← hfinL', ← hfinL, hbc]
  refine ⟨fun 𝔪 ↦ ?_, ?_⟩
  · by_contra hn
    push Not at hn
    have : ∑ 𝔪 ∈ Finset.univ.image (contr L L'), δ 𝔪 < ∑ 𝔪, δ 𝔪 :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ 𝔪) (by simpa using hn)
        (hpos 𝔪) (fun _ _ _ ↦ Nat.zero_le _)
    omega
  · have heq : ∑ 𝔪', d 𝔪' = ∑ 𝔪', δ (contr L L' 𝔪') := by omega
    intro 𝔪'
    exact (Finset.sum_eq_sum_iff_of_le fun i _ ↦ hle i).1 heq 𝔪' (Finset.mem_univ _)

variable (F F') in
include F F' H in
/-- **(i)** Contraction is a bijection between the maximal ideals. -/
theorem contr_bijective : Function.Bijective (contr L L') :=
  ⟨contr_injective H, (key (F := F) (F' := F') H).1⟩

include H in
/-- **(ii)** Corresponding components have the same degree. -/
theorem finrank_quot_eq (𝔪' : MaximalSpectrum L') :
    Module.finrank F (L ⧸ (contr L L' 𝔪').asIdeal) = Module.finrank F' (L' ⧸ 𝔪'.asIdeal) :=
  ((key (F := F) (F' := F') H).2 𝔪').symm

include H in
/-- **(ii)** `F' ⊗_F (L ⧸ 𝔪) → L' ⧸ 𝔪'` is bijective. -/
theorem baseChangeMap_bijective (𝔪' : MaximalSpectrum L') :
    Function.Bijective (baseChangeMap F F' L L' 𝔪') := by
  refine ⟨?_, baseChangeMap_surjective 𝔪'⟩
  have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (baseChangeMap F F' L L' 𝔪').toLinearMap) (by
      rw [Module.finrank_baseChange, finrank_quot_eq (F := F) (F' := F') H])).2
        (baseChangeMap_surjective 𝔪')
  exact this

/-- **(ii)** `F' ⊗_F (L ⧸ 𝔪) ≃ L' ⧸ 𝔪'`. -/
noncomputable def baseChangeEquiv (𝔪' : MaximalSpectrum L') :
    F' ⊗[F] (L ⧸ (contr L L' 𝔪').asIdeal) ≃ₐ[F'] L' ⧸ 𝔪'.asIdeal :=
  AlgEquiv.ofBijective _ (baseChangeMap_bijective H 𝔪')

end ReducedBaseChange


namespace W10Fields

attribute [local instance] polyAlgebra

section LXPushout

variable (K : Type u) [Field K] (M : Type u) [Field M] [Algebra K M]
  (A : Type u) [CommRing A] [Algebra K[X] A]

namespace LX

noncomputable instance algebraKX : Algebra K[X] (LX K M A) :=
  inferInstanceAs (Algebra K[X] (RatFunc M ⊗[M[X]] BX K M A))

noncomputable instance algebraA : Algebra A (LX K M A) :=
  ((algebraMap (BX K M A) (LX K M A)).comp (algebraMap A (BX K M A))).toAlgebra

instance : IsScalarTower A (BX K M A) (LX K M A) := .of_algebraMap_eq' rfl

instance : IsScalarTower K[X] (RatFunc M) (LX K M A) :=
  inferInstanceAs (IsScalarTower K[X] (RatFunc M) (RatFunc M ⊗[M[X]] BX K M A))

instance : IsScalarTower K[X] M[X] (LX K M A) := .of_algebraMap_eq fun p ↦ by
  rw [IsScalarTower.algebraMap_apply K[X] (RatFunc M) (LX K M A),
    IsScalarTower.algebraMap_apply M[X] (RatFunc M) (LX K M A)]
  rfl

instance : IsScalarTower K[X] (BX K M A) (LX K M A) := .of_algebraMap_eq fun p ↦ by
  rw [IsScalarTower.algebraMap_apply K[X] M[X] (LX K M A),
    IsScalarTower.algebraMap_apply K[X] M[X] (BX K M A),
    ← IsScalarTower.algebraMap_apply M[X] (BX K M A) (LX K M A)]

instance : IsScalarTower K[X] A (LX K M A) := .of_algebraMap_eq fun p ↦ by
  rw [IsScalarTower.algebraMap_apply K[X] (BX K M A) (LX K M A),
    IsScalarTower.algebraMap_apply K[X] A (BX K M A),
    ← IsScalarTower.algebraMap_apply A (BX K M A) (LX K M A)]

end LX

/-- **`LX = M(X) ⊗_{K[X]} A`.** -/
instance isPushout_LX : Algebra.IsPushout K[X] (RatFunc M) A (LX K M A) := by
  haveI : Algebra.IsPushout K[X] M[X] A (BX K M A) :=
    TensorProduct.isPushout (R := K[X]) (S := M[X]) (T := A)
  haveI : Algebra.IsPushout M[X] (RatFunc M) (BX K M A) (LX K M A) :=
    TensorProduct.isPushout (R := M[X]) (S := RatFunc M) (T := BX K M A)
  exact (Algebra.IsPushout.comp_iff K[X] M[X] A (S' := BX K M A) (T := RatFunc M)
    (T' := LX K M A)).2 inferInstance

end LXPushout

section Compare

variable (K : Type u) [Field K] {C : Type u} [Field C] [Algebra K C] (E : IntermediateField K C)
  (A : Type u) [CommRing A] [Algebra K[X] A]

/-- `E(X) → C(X)`. -/
noncomputable abbrev ratFuncAlgebra : Algebra (RatFunc E) (RatFunc C) :=
  (ratFuncMap (algebraMap E C)).toAlgebra

attribute [local instance] ratFuncAlgebra

instance : IsScalarTower K[X] (RatFunc E) (RatFunc C) := .of_algebraMap_eq fun p ↦ by
  change algebraMap C[X] (RatFunc C) (p.map (algebraMap K C)) =
    ratFuncMap (algebraMap E C) (algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)))
  rw [ratFuncMap_algebraMap, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- `LX_E → LX_C` as an algebra. -/
noncomputable abbrev lxAlgebra : Algebra (LX K E A) (LX K C A) := (lxMap K E A C).toAlgebra

/-- `E(X) → LX_C`. -/
noncomputable abbrev ratFuncLXAlgebra : Algebra (RatFunc E) (LX K C A) :=
  ((algebraMap (RatFunc C) (LX K C A)).comp (algebraMap (RatFunc E) (RatFunc C))).toAlgebra

attribute [local instance] lxAlgebra ratFuncLXAlgebra

instance : IsScalarTower (RatFunc E) (RatFunc C) (LX K C A) := .of_algebraMap_eq' rfl

instance : IsScalarTower (RatFunc E) (LX K E A) (LX K C A) := .of_algebraMap_eq fun φ ↦
  (lxMap_algebraMap_ratFunc φ).symm

instance : IsScalarTower A (LX K E A) (LX K C A) := .of_algebraMap_eq fun a ↦ by
  change _ = lxMap K E A C (algebraMap (BX K E A) (LX K E A) (algebraMap A (BX K E A) a))
  rw [lxMap_algebraMap]
  exact congrArg (algebraMap (BX K C A) (LX K C A)) (bxMap_ofA K A a).symm

instance : IsScalarTower K[X] (LX K E A) (LX K C A) := .of_algebraMap_eq fun p ↦ by
  rw [IsScalarTower.algebraMap_apply K[X] A (LX K E A),
    ← IsScalarTower.algebraMap_apply A (LX K E A) (LX K C A),
    ← IsScalarTower.algebraMap_apply K[X] A (LX K C A)]

/-- **`LX_C = C(X) ⊗_{E(X)} LX_E`.** -/
instance isPushout_compare :
    Algebra.IsPushout (RatFunc E) (RatFunc C) (LX K E A) (LX K C A) :=
  (Algebra.IsPushout.comp_iff K[X] (RatFunc E) A (S' := LX K E A) (T := RatFunc C)
    (T' := LX K C A)).1 inferInstance

variable {K} in
/-- Every rational function over `C` is defined over every `E` containing a finite set of
constants. -/
lemma exists_finset_ratFunc (φ : RatFunc C) :
    ∃ S : Finset C, ∀ E : IntermediateField K C, (S : Set C) ⊆ E →
      ∃ ψ : RatFunc E, ratFuncMap (algebraMap E C) ψ = φ := by
  classical
  refine ⟨φ.num.coeffs ∪ φ.denom.coeffs, fun E hE ↦ ?_⟩
  have hlift (p : C[X]) (hp : (p.coeffs : Set C) ⊆ E) : ∃ q : E[X], q.map (algebraMap E C) = p := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h : p.coeff n = 0
    · exact ⟨0, by rw [h, map_zero]⟩
    · exact ⟨⟨p.coeff n, hp (Polynomial.coeff_mem_coeffs h)⟩, rfl⟩
  obtain ⟨n, hn⟩ := hlift φ.num fun x hx ↦ hE (Finset.mem_union_left _ hx)
  obtain ⟨d, hd⟩ := hlift φ.denom fun x hx ↦ hE (Finset.mem_union_right _ hx)
  refine ⟨algebraMap E[X] (RatFunc E) n / algebraMap E[X] (RatFunc E) d, ?_⟩
  rw [map_div₀, ratFuncMap_algebraMap, ratFuncMap_algebraMap, hn, hd, RatFunc.num_div_denom]

variable {K A} in
/-- **Descent of elements**: every element of `LX_C` comes from `LX_E` for every `E` containing a
finite set of constants. -/
lemma exists_finset_LX (y : LX K C A) :
    ∃ S : Finset C, ∀ E : IntermediateField K C, (S : Set C) ⊆ E →
      y ∈ (algebraMap (LX K E A) (LX K C A)).range := by
  classical
  obtain ⟨w, rfl⟩ := (Algebra.IsPushout.equiv K[X] (RatFunc C) A (LX K C A)).surjective y
  induction w with
  | zero => exact ⟨∅, fun E _ ↦ by rw [map_zero]; exact zero_mem _⟩
  | add x y hx hy =>
    obtain ⟨S₁, h₁⟩ := hx
    obtain ⟨S₂, h₂⟩ := hy
    refine ⟨S₁ ∪ S₂, fun E hE ↦ ?_⟩
    rw [map_add]
    exact add_mem (h₁ E fun x hx ↦ hE (Finset.mem_union_left _ hx))
      (h₂ E fun x hx ↦ hE (Finset.mem_union_right _ hx))
  | tmul φ a =>
    obtain ⟨S, hS⟩ := exists_finset_ratFunc (K := K) φ
    refine ⟨S, fun E hE ↦ ?_⟩
    obtain ⟨ψ, rfl⟩ := hS E hE
    rw [Algebra.IsPushout.equiv_tmul]
    refine mul_mem ⟨algebraMap (RatFunc E) (LX K E A) ψ, ?_⟩ ⟨algebraMap A (LX K E A) a, ?_⟩
    · rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (RatFunc E)
        (RatFunc C) (LX K C A)]
      rfl
    · rw [← IsScalarTower.algebraMap_apply]

variable [Module.Finite K[X] A]

lemma contrMax_eq (𝔪' : MaximalSpectrum (LX K C A)) :
    contrMax K E A C 𝔪' = ReducedBaseChange.contr (LX K E A) (LX K C A) 𝔪' := rfl

variable {E} in
/-- The map of components is semilinear over `ratFuncMap`. -/
lemma compMap_algebraMap (𝔪' : MaximalSpectrum (LX K C A)) (φ : RatFunc E) :
    compMap K E A C 𝔪' (algebraMap (RatFunc E) _ φ) =
      algebraMap (RatFunc C) _ (ratFuncMap (algebraMap E C) φ) :=
  ReducedBaseChange.quotMap_algebraMap (F := RatFunc E) (F' := RatFunc C) (L := LX K E A)
    (L' := LX K C A) 𝔪' φ

/-- `C(X) ⊗_{E(X)} Comp_E (𝔪' ∩ LX_E) → Comp_C 𝔪'`, `r ⊗ y ↦ r · compMap y`. -/
noncomputable def compBaseChange (𝔪' : MaximalSpectrum (LX K C A)) :
    RatFunc C ⊗[RatFunc E] Comp K E A (contrMax K E A C 𝔪') →ₐ[RatFunc C] Comp K C A 𝔪' :=
  ReducedBaseChange.baseChangeMap (RatFunc E) (RatFunc C) (LX K E A) (LX K C A) 𝔪'

variable {E} in
lemma compBaseChange_tmul (𝔪' : MaximalSpectrum (LX K C A)) (r : RatFunc C)
    (y : Comp K E A (contrMax K E A C 𝔪')) :
    compBaseChange K E A 𝔪' (r ⊗ₜ y) = algebraMap (RatFunc C) _ r * compMap K E A C 𝔪' y := by
  rfl

variable {K A} in
/-- Every finite set of elements of a component `Comp_C 𝔪'` lies in the image of `Comp_E` for
every `E` containing a finite set of constants. -/
lemma exists_finset_range_compMap (𝔪' : MaximalSpectrum (LX K C A))
    (T : Finset (Comp K C A 𝔪')) :
    ∃ S : Finset C, ∀ E : IntermediateField K C, (S : Set C) ⊆ E →
      ∀ t ∈ T, t ∈ (compMap K E A C 𝔪').range := by
  classical
  choose y hy using fun t : Comp K C A 𝔪' ↦ Ideal.Quotient.mk_surjective t
  choose S hS using fun t : Comp K C A 𝔪' ↦ exists_finset_LX (K := K) (A := A) (y t)
  refine ⟨T.biUnion S, fun E hE t ht ↦ ?_⟩
  obtain ⟨x, hx⟩ := hS t E fun c hc ↦ hE (Finset.mem_biUnion.2 ⟨t, ht, hc⟩)
  exact ⟨Ideal.Quotient.mk _ x, by rw [compMap_mk, ← hy t]; exact congrArg _ hx⟩

/-- **(3) Comparison of the components.** There is a finite set `S` of constants such that for
every intermediate field `S ⊆ E ⊆ C` (with `E ⊗_K A` reduced): contraction of maximal ideals
`contrMax : MaxSpec LX_C → MaxSpec LX_E` is bijective (i), and for corresponding components
`C(X) ⊗_{E(X)} Comp_E 𝔪 → Comp_C 𝔪'` (`compBaseChange`, `r ⊗ y ↦ r · compMap y`) is bijective;
in particular the degrees agree (ii). -/
theorem exists_finset_compare [IsReduced (BX K C A)] :
    ∃ S : Finset C, ∀ E : IntermediateField K C, (S : Set C) ⊆ E → IsReduced (BX K E A) →
      Function.Bijective (contrMax K E A C) ∧
      ∀ 𝔪' : MaximalSpectrum (LX K C A), Function.Bijective (compBaseChange K E A 𝔪') ∧
        Module.finrank (RatFunc E) (Comp K E A (contrMax K E A C 𝔪')) =
          Module.finrank (RatFunc C) (Comp K C A 𝔪') := by
  classical
  haveI := isReduced_LX K C A
  haveI := Fintype.ofFinite (MaximalSpectrum (LX K C A))
  choose S hS using fun 𝔪' : MaximalSpectrum (LX K C A) ↦
    exists_finset_LX (K := K) (A := A) (ReducedArtinian.idem 𝔪')
  refine ⟨Finset.univ.biUnion S, fun E hE hred ↦ ?_⟩
  haveI := hred
  haveI := isReduced_LX K E A
  have H : ∀ 𝔪', ReducedArtinian.idem 𝔪' ∈ (algebraMap (LX K E A) (LX K C A)).range :=
    fun 𝔪' ↦ hS 𝔪' E fun x hx ↦ hE (Finset.mem_biUnion.2 ⟨𝔪', Finset.mem_univ _, hx⟩)
  exact ⟨ReducedBaseChange.contr_bijective (RatFunc E) (RatFunc C) H, fun 𝔪' ↦
    ⟨ReducedBaseChange.baseChangeMap_bijective H 𝔪', ReducedBaseChange.finrank_quot_eq H 𝔪'⟩⟩

/-- **(3)** for `A` smooth over `K`. -/
theorem exists_finset_compare_of_smooth [Algebra K A] [IsScalarTower K K[X] A]
    [Algebra.Smooth K A] :
    ∃ S : Finset C, ∀ E : IntermediateField K C, (S : Set C) ⊆ E →
      Function.Bijective (contrMax K E A C) ∧
      ∀ 𝔪' : MaximalSpectrum (LX K C A), Function.Bijective (compBaseChange K E A 𝔪') ∧
        Module.finrank (RatFunc E) (Comp K E A (contrMax K E A C 𝔪')) =
          Module.finrank (RatFunc C) (Comp K C A 𝔪') := by
  haveI := isReduced_BX K C A
  obtain ⟨S, hS⟩ := exists_finset_compare K (C := C) A
  exact ⟨S, fun E hE ↦ hS E hE (isReduced_BX K E A)⟩

end Compare

end W10Fields

end SemistableReduction
