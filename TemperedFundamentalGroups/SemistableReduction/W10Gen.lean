/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Gal

/-!
# Generators of the components defined over `K`

Blueprint §9.7a (W10 assembly). For a field extension `M / K`:

* `adjoin_range_lbMap`: `LX K M B` is generated as an `M(X)`-algebra by the image of `B`;
* `exists_generators_comp`: every component `Comp K M B 𝔪` is generated as an `M(X)`-algebra by
  finitely many elements of the image of `CompB K B (contrB 𝔪)` (`compBMap`);
* `range_compBMap_le_range_compMap`: for `K ⊆ E ⊆ C`, the image of the `K`-component in a
  `C`-component lies in the image of the `E`-component.
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace W10Gen

open W10Fields

attribute [local instance] polyAlgebra

variable (K : Type u) [Field K] (B : Type u) [CommRing B] [Algebra K[X] B]
  (M : Type u) [Field M] [Algebra K M]

/-- `LX K M B` is generated over `M(X)` by the image of `B`. -/
theorem adjoin_range_lbMap :
    Algebra.adjoin (RatFunc M)
      (Set.range fun b : B ↦ lbMap K M B (algebraMap B (LB K B) b)) = ⊤ := by
  set S := Algebra.adjoin (RatFunc M)
    (Set.range fun b : B ↦ lbMap K M B (algebraMap B (LB K B) b))
  let φ : M[X] ⊗[K[X]] B →+* LX K M B := algebraMap (BX K M B) (LX K M B)
  have hB : ∀ y : M[X] ⊗[K[X]] B, φ y ∈ S := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul p b =>
      have h1 : (p ⊗ₜ b : M[X] ⊗[K[X]] B) = (p ⊗ₜ 1 : M[X] ⊗[K[X]] B) * (1 ⊗ₜ b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h1, map_mul]
      have h2 : φ (p ⊗ₜ 1) = algebraMap (RatFunc M) (LX K M B) (algebraMap M[X] (RatFunc M) p) := by
        rw [← IsScalarTower.algebraMap_apply M[X] (RatFunc M) (LX K M B),
          IsScalarTower.algebraMap_apply M[X] (BX K M B) (LX K M B)]
        rfl
      rw [h2]
      refine mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin ⟨b, ?_⟩)
      exact lbMap_algebraMap K M B b
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul φ y =>
    have h0 : (φ ⊗ₜ y : RatFunc M ⊗[M[X]] BX K M B) =
        (φ ⊗ₜ (1 : BX K M B)) * ((1 : RatFunc M) ⊗ₜ y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h0]
    exact mul_mem (Subalgebra.algebraMap_mem S φ) (hB y)

variable [Module.Finite K[X] B]

lemma compBMap_algebraMap (𝔪 : MaximalSpectrum (LX K M B)) (r : RatFunc K) :
    compBMap K M B 𝔪 (algebraMap (RatFunc K) _ r) =
      algebraMap (RatFunc M) _ (ratFuncMap (algebraMap K M) r) := by
  change Ideal.Quotient.mk _ (lbMap K M B (algebraMap (RatFunc K) (LB K B) r)) =
    Ideal.Quotient.mk _ (algebraMap (RatFunc M) (LX K M B) _)
  rw [lbMap_algebraMap_ratFunc]

/-- **Generators of a component over `K`.** -/
theorem exists_generators_comp (𝔪 : MaximalSpectrum (LX K M B)) :
    ∃ T : Finset (Comp K M B 𝔪), Algebra.adjoin (RatFunc M) (T : Set (Comp K M B 𝔪)) = ⊤ ∧
      ∀ t ∈ T, ∃ y : CompB K B (contrB K M B 𝔪), compBMap K M B 𝔪 y = t := by
  classical
  set 𝔫 := contrB K M B 𝔪
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := RatFunc K) (M := CompB K B 𝔫)
  refine ⟨s.image (compBMap K M B 𝔪), ?_, fun t ht ↦ ?_⟩
  · set S := Algebra.adjoin (RatFunc M) ((s.image (compBMap K M B 𝔪) : Finset _) :
      Set (Comp K M B 𝔪))
    -- the image of `compBMap` lies in `S`
    have himg : ∀ y : CompB K B 𝔫, compBMap K M B 𝔪 y ∈ S := by
      intro y
      have hy : y ∈ Submodule.span (RatFunc K) (s : Set (CompB K B 𝔫)) := by rw [hs]; trivial
      induction hy using Submodule.span_induction with
      | mem z hz =>
        exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hz))
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul r z _ hz =>
        rw [Algebra.smul_def, map_mul, compBMap_algebraMap]
        exact mul_mem (Subalgebra.algebraMap_mem _ _) hz
    rw [eq_top_iff]
    rintro x -
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx : x ∈ Algebra.adjoin (RatFunc M)
        (Set.range fun b : B ↦ lbMap K M B (algebraMap B (LB K B) b)) := by
      rw [adjoin_range_lbMap]; trivial
    let q := (Ideal.Quotient.mkₐ (RatFunc M) 𝔪.asIdeal)
    have : q x ∈ (Algebra.adjoin (RatFunc M)
        (Set.range fun b : B ↦ lbMap K M B (algebraMap B (LB K B) b))).map q :=
      ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin] at this
    refine (Algebra.adjoin_le ?_) this
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact himg (Ideal.Quotient.mk _ (algebraMap B (LB K B) b))
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨y, rfl⟩

/-- **Images along `K ⊆ E ⊆ C`.** -/
theorem range_compBMap_le_range_compMap
    (E : IntermediateField K (AlgebraicClosure K))
    (𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B)) :
    Set.range (compBMap K (AlgebraicClosure K) B 𝔪') ⊆
      Set.range (compMap K E B (AlgebraicClosure K) 𝔪') := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ (lbMap K E B y), W10Gal.compMap_mk_lbMap B E 𝔪' y⟩

end W10Gen

end SemistableReduction
