/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Assembly

/-!
# Coordinates of the given models on the components

Blueprint §9.7a (W10 assembly, `hdata` without the domination). For a model `c₀` over `O` and
`j₀ : Spec B ⟶ c₀` over `O`:

* `exists_coordsK`: on every component `CompB 𝔫` of `B` over `K(X)` there are homogeneous
  coordinates `f` (nonzero) with a morphism `projModelCode O f ⟶ c₀` restricting to
  `Spec (CompB 𝔫) ⟶ Spec B ⟶ c₀` on the generic point, over `O` (T4,
  `exists_closedImmersion_projModelCode`);
* `coordsE`: for a field `E ⊇ K`, their images in the components of `E ⊗_K B` (via `compBMap`)
  with the induced morphisms, compatible with `compPt` and over `O` — the `hdata` input of
  `strongA_body_of_data` apart from the local domination.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits Polynomial TensorProduct

namespace SemistableReduction

namespace W10Assembly

open TemperedFundamentalGroups W10Fields ProjScheme

attribute [local instance] polyAlgebra

variable {K : Type u} [Field K] (O : ValuationSubring K)
  {B : Type u} [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B]
  [Algebra K B] [IsScalarTower K K[X] B]
  (c₀ : ModelCode O) (j₀ : Spec (CommRingCat.of B) ⟶ c₀.scheme)
  (hj₀ : j₀ ≫ c₀.toSpec = Spec.map (CommRingCat.ofHom ((algebraMap K B).comp O.subtype)))

/-- The `O`-algebra structure of a component over `K`. -/
noncomputable abbrev compBAlgO (𝔫 : MaximalSpectrum (LB K B)) : Algebra O (CompB K B 𝔫) :=
  ((algebraMap K (CompB K B 𝔫)).comp O.subtype).toAlgebra

attribute [local instance] compBAlgO compAlgO

/-- `B → CompB 𝔫`. -/
noncomputable def toCompB (𝔫 : MaximalSpectrum (LB K B)) : B →+* CompB K B 𝔫 :=
  (Ideal.Quotient.mk 𝔫.asIdeal).comp (algebraMap B (LB K B))

omit [Module.Finite K[X] B] in
lemma toCompB_algebraMap (𝔫 : MaximalSpectrum (LB K B)) (k : K) :
    toCompB 𝔫 (algebraMap K B k) = algebraMap K (CompB K B 𝔫) k := by
  change Ideal.Quotient.mk _ (algebraMap B (LB K B) (algebraMap K B k)) =
    Ideal.Quotient.mk _ (algebraMap K (LB K B) k)
  congr 1
  rw [IsScalarTower.algebraMap_apply K K[X] B, ← IsScalarTower.algebraMap_apply K[X] B (LB K B),
    IsScalarTower.algebraMap_apply K[X] (RatFunc K) (LB K B),
    IsScalarTower.algebraMap_apply K (RatFunc K) (LB K B), ← IsScalarTower.algebraMap_apply K K[X]]

omit [Module.Finite K[X] B] in
include hj₀ in
/-- **Coordinates over `K`.** -/
theorem exists_coordsK (𝔫 : MaximalSpectrum (LB K B)) :
    ∃ (n : ℕ) (f : Fin (n + 1) → CompB K B 𝔫) (hf : ∀ i, f i ≠ 0)
      (ι : (projModelCode O hf).scheme ⟶ c₀.scheme),
      genericPt O hf ≫ ι = Spec.map (CommRingCat.ofHom (toCompB 𝔫)) ≫ j₀ ∧
      ι ≫ c₀.toSpec = (projModelCode O hf).toSpec := by
  obtain ⟨n, f, hf, ι, -, h₁, h₂⟩ := exists_closedImmersion_projModelCode c₀
    (Spec.map (CommRingCat.ofHom (toCompB 𝔫)) ≫ j₀) (by
      rw [Category.assoc, hj₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext o
      exact toCompB_algebraMap 𝔫 o)
  exact ⟨n, f, hf, ι, h₁, h₂⟩

section E

variable {E : Type u} [Field E] [Algebra K E]

omit [Algebra K B] [IsScalarTower K K[X] B] in
lemma compBMap_algebraMap_K (𝔪 : MaximalSpectrum (LX K E B)) (k : K) :
    compBMap K E B 𝔪 (algebraMap K (CompB K B (contrB K E B 𝔪)) k) =
      algebraMap E (Comp K E B 𝔪) (algebraMap K E k) := by
  change Ideal.Quotient.mk _ (lbMap K E B (algebraMap K (LB K B) k)) =
    Ideal.Quotient.mk _ (algebraMap E (LX K E B) (algebraMap K E k))
  congr 1
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) (LB K B), lbMap_algebraMap_ratFunc,
    ratFuncMap_algebraMap_C, ← IsScalarTower.algebraMap_apply]

omit [Algebra K B] [IsScalarTower K K[X] B] in
lemma compBMap_comp_algebraMap (𝔪 : MaximalSpectrum (LX K E B)) :
    (compBMap K E B 𝔪).comp (algebraMap O (CompB K B (contrB K E B 𝔪))) =
      algebraMap O (Comp K E B 𝔪) :=
  RingHom.ext fun o ↦ compBMap_algebraMap_K 𝔪 o

lemma compBMap_toCompB (𝔪 : MaximalSpectrum (LX K E B)) (b : B) :
    compBMap K E B 𝔪 (toCompB (contrB K E B 𝔪) b) =
      ψ (K := K) (B := B) (E := E) (1 ⊗ₜ b) 𝔪 := by
  change Ideal.Quotient.mk _ (lbMap K E B (algebraMap B (LB K B) b)) =
    Ideal.Quotient.mk _ (algebraMap (BX K E B) (LX K E B) (tensorEquiv K E B (1 ⊗ₜ b)))
  rw [lbMap_algebraMap, tensorEquiv_one_tmul]

variable {n : MaximalSpectrum (LB K B) → ℕ} {f : ∀ 𝔫, Fin (n 𝔫 + 1) → CompB K B 𝔫}
  (hf : ∀ 𝔫 i, f 𝔫 i ≠ 0) (ι : ∀ 𝔫, (projModelCode O (hf 𝔫)).scheme ⟶ c₀.scheme)

/-- The coordinates on the components of `E ⊗_K B`. -/
noncomputable def fE (𝔪 : MaximalSpectrum (LX K E B)) :
    Fin (n (contrB K E B 𝔪) + 1) → Comp K E B 𝔪 :=
  fun i ↦ compBMap K E B 𝔪 (f _ i)

omit [Algebra K B] [IsScalarTower K K[X] B] in
include hf in
lemma fE_ne_zero (𝔪 : MaximalSpectrum (LX K E B)) (i : Fin (n (contrB K E B 𝔪) + 1)) :
    fE (f := f) 𝔪 i ≠ 0 :=
  (_root_.map_ne_zero _).2 (hf _ i)

omit [Algebra K B] [IsScalarTower K K[X] B] in
lemma dominates_fE (𝔪 : MaximalSpectrum (LX K E B)) :
    Dominates (algebraMap O (CompB K B (contrB K E B 𝔪))).range
      (algebraMap O (Comp K E B 𝔪)).range (compBMap K E B 𝔪) (f (contrB K E B 𝔪))
      (fE (f := f) 𝔪) := by
  refine dominates_of_forall _ _ (fun y ⟨o, ho⟩ ↦ ⟨o, ?_⟩) fun j ↦ ⟨j, fun k ↦ ?_⟩
  · rw [← ho, ← RingHom.comp_apply, compBMap_comp_algebraMap]
  · rw [map_div₀]
    exact div_mem_projChart j k

/-- The morphisms `projModelCode O (fE 𝔪) ⟶ c₀`. -/
noncomputable def ιE (𝔪 : MaximalSpectrum (LX K E B)) :
    (projModelCode O (fE_ne_zero hf 𝔪)).scheme ⟶ c₀.scheme :=
  homOfDominates rfl rfl (hf _) (fE_ne_zero hf 𝔪) (compBMap K E B 𝔪) (dominates_fE O 𝔪) ≫
    ι (contrB K E B 𝔪)

variable (hι : ∀ 𝔫, genericPt O (hf 𝔫) ≫ ι 𝔫 = Spec.map (CommRingCat.ofHom (toCompB 𝔫)) ≫ j₀)
  (hιO : ∀ 𝔫, ι 𝔫 ≫ c₀.toSpec = (projModelCode O (hf 𝔫)).toSpec)

include hι in
theorem genericPt_ιE (𝔪 : MaximalSpectrum (LX K E B)) :
    genericPt O (fE_ne_zero hf 𝔪) ≫ ιE O c₀ hf ι 𝔪 = compPt O c₀ j₀ 𝔪 := by
  rw [ιE, reassoc_of% genericPt_comp_homOfDominates, hι, compPt, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp]
  congr 3
  ext b
  exact compBMap_toCompB 𝔪 b

omit [Algebra K B] [IsScalarTower K K[X] B] in
include hιO in
theorem ιE_toSpec (𝔪 : MaximalSpectrum (LX K E B)) :
    ιE O c₀ hf ι 𝔪 ≫ c₀.toSpec = (projModelCode O (fE_ne_zero hf 𝔪)).toSpec := by
  rw [ιE, Category.assoc, hιO, homOfDominates_toSpec_self _ _ _ _ _ _
    (compBMap_comp_algebraMap O 𝔪)]

end E

end W10Assembly

end SemistableReduction
