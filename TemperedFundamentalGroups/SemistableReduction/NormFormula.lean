/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LocalGlobal

/-!
# The norm formula: the norm is the product of the local norms

Blueprint §9.9, W7 layer S2. In the setting of `SemistableReduction.LocalGlobal` (`F` a
non-archimedean normed field, `K ⊇ F` complete with `F` dense, `F' / F` finite separable,
`minpoly α = ∏ g` over `K`, `toLocal g : F' → Local K g = K[X]/(g)`):

* `algebraMap_norm_eq_prod`: `N_{F'/F}(y) = ∏_g N_{Local K g / K}(toLocal g y)` in `K`
  (the `F`-embeddings of `F'` into an algebraic closure of `K` are the `K`-embeddings of the
  `Local K g`, composed with `toLocal g`: `embeddingsEquiv`);
* `norm_algebraNorm_local`: in the complete field `Local K g` (spectral norm),
  `‖N_{Local/K}(z)‖ = ‖z‖ ^ deg g`;
* **`norm_algebraMap_norm_eq_prod`**: `‖N_{F'/F}(y)‖ = ∏_g extValuation g (y) ^ deg g`, i.e.
  `|N(y)| = ∏_{w ∣ v} w(y)^{[\hat F'_w : \hat F]}`. Over a Gauss point of `C(x)` with W4
  (`e = 1`, `[\hat F'_w : \hat F] = f(w)`) this is `w_s(N y) = ∏_{w' ∣ w_s} w'(y)^{f(w')}`, which
  is piecewise monomial in `s` (`AnnulusUnit`).
-/

open Polynomial NNReal IntermediateField

namespace SemistableReduction

namespace LocalGlobal

variable {F K F' : Type*} [NormedField F] [IsUltrametricDist F]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K]
  [Field F'] [Algebra F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma separable_minpolyK : (minpolyK F K F').Separable :=
  Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F (pb F F').gen)

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma separable_factor (g : Factor F K F') : g.1.Separable :=
  separable_minpolyK.of_dvd (dvd_of_mem_factors g.2)

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma ne_zero_factor (g : Factor F K F') : g.1 ≠ 0 := (irreducible_of_mem_factors g.2).ne_zero

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma adjoin_root_eq_top (g : Factor F K F') :
    IntermediateField.adjoin K {root g.1} = (⊤ : IntermediateField K (Local K g.1)) := by
  refine eq_top_iff.2 fun y _ ↦ IntermediateField.algebra_adjoin_le_adjoin K _ ?_
  have : Algebra.adjoin K ({root g.1} : Set (Local K g.1)) = ⊤ :=
    AdjoinRoot.adjoinRoot_eq_top (f := g.1)
  rw [this]
  trivial

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
instance isSeparable_local (g : Factor F K F') : Algebra.IsSeparable K (Local K g.1) := by
  have hroot : IsSeparable K (root g.1) :=
    (separable_factor g).of_dvd (minpoly.dvd K _ (aeval_root g.1))
  have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (Local K g.1)).2 hroot
  exact Algebra.IsSeparable.of_algHom K _
    ((IntermediateField.equivOfEq (adjoin_root_eq_top g)).trans
      IntermediateField.topEquiv).symm.toAlgHom

variable (E : Type*) [Field E] [Algebra K E] [Algebra F E] [IsScalarTower F K E]

/-- An `F`-embedding of `F'` from a factor `g` and a `K`-embedding of `Local K g`. -/
noncomputable def embeddingOf (p : Σ g : Factor F K F', Local K g.1 →ₐ[K] E) : F' →ₐ[F] E :=
  (p.2.restrictScalars F).comp (toLocal p.1)

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma embeddingOf_gen (p : Σ g : Factor F K F', Local K g.1 →ₐ[K] E) :
    embeddingOf E p (pb F F').gen = p.2 (root p.1.1) := by
  simp [embeddingOf, toLocal_gen]

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma embeddingOf_injective : Function.Injective (embeddingOf (F := F) (K := K) (F' := F') E) := by
  rintro ⟨g, τ⟩ ⟨h, τ'⟩ hgh
  have h1 := congrArg (fun σ : F' →ₐ[F] E ↦ σ (pb F F').gen) hgh
  simp only [embeddingOf_gen] at h1
  have hg : aeval (τ (root g.1)) g.1 = 0 := by rw [aeval_algHom_apply, aeval_root, map_zero]
  have hh : aeval (τ' (root h.1)) h.1 = 0 := by rw [aeval_algHom_apply, aeval_root, map_zero]
  obtain rfl : g = h := by
    by_contra hne
    obtain ⟨a, b, hab⟩ := isCoprime_of_mem_factors g.2 h.2 (fun e ↦ hne (Subtype.ext e))
    have := congrArg (aeval (τ (root g.1))) hab
    rw [map_add, map_mul, map_mul, hg, h1, hh, map_one] at this
    simp at this
  obtain rfl : τ = τ' := AdjoinRoot.algHom_ext h1
  rfl

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma embeddingOf_bijective [IsAlgClosed E] :
    Function.Bijective (embeddingOf (F := F) (K := K) (F' := F') E) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨embeddingOf_injective E, ?_⟩
  rw [Fintype.card_sigma, AlgHom.card]
  simp_rw [AlgHom.card, finrank_local]
  rw [← sum_natDegree_factors (F := F) (K := K) (F' := F')]
  exact (Finset.sum_coe_sort (factors F K F') (fun g ↦ g.natDegree))

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
/-- **The norm is the product of the local norms**: `N_{F'/F}(y) = ∏_g N_{K[X]/(g) / K}(y)`. -/
theorem algebraMap_norm_eq_prod (y : F') :
    algebraMap F K (Algebra.norm F y) = ∏ g : Factor F K F', Algebra.norm K (toLocal g y) := by
  classical
  set E := AlgebraicClosure K
  refine (algebraMap K E).injective ?_
  rw [← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_embeddings F E y, map_prod]
  simp_rw [Algebra.norm_eq_prod_embeddings K E]
  rw [← (embeddingOf_bijective (F := F) (K := K) (F' := F') E).prod_comp, Fintype.prod_sigma]
  rfl

omit [IsUltrametricDist F] in
/-- In the complete field `Local K g` with the spectral norm, `‖N(z)‖ = ‖z‖ ^ deg g`. -/
theorem norm_algebraNorm_local (g : Factor F K F') (z : Local K g.1) :
    ‖Algebra.norm K z‖ = ‖z‖ ^ g.1.natDegree := by
  have hz := Algebra.IsSeparable.isIntegral K z
  set d := (minpoly K z).natDegree
  have hd0 : 0 < d := minpoly.natDegree_pos hz
  have hdeg : g.1.natDegree = d * Module.finrank K⟮z⟯ (Local K g.1) := by
    rw [← finrank_local, ← Module.finrank_mul_finrank K K⟮z⟯ (Local K g.1),
      IntermediateField.adjoin.finrank hz]
  rw [Algebra.norm_eq_norm_adjoin K z, ← IntermediateField.adjoin.powerBasis_gen hz,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hz,
    IntermediateField.minpoly_gen, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_local, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, hdeg, pow_mul,
    ← Real.rpow_natCast (‖(minpoly K z).coeff 0‖ ^ (1 / (d : ℝ))) d,
    ← Real.rpow_mul (norm_nonneg _), one_div,
    inv_mul_cancel₀ (by exact_mod_cast hd0.ne'), Real.rpow_one]

omit [IsUltrametricDist F] in
/-- **The norm formula**: `‖N_{F'/F}(y)‖ = ∏_{w ∣ v} w(y) ^ [\hat F'_w : \hat F]`, the product over
the factors `g` (= the extensions `extValuation g` of the norm of `F`, B3). -/
theorem norm_algebraMap_norm_eq_prod (y : F') :
    ‖algebraMap F K (Algebra.norm F y)‖₊ =
      ∏ g : Factor F K F', extValuation g y ^ g.1.natDegree := by
  rw [algebraMap_norm_eq_prod, nnnorm_prod]
  refine Finset.prod_congr rfl fun g _ ↦ ?_
  rw [extValuation_apply]
  exact NNReal.eq (by push_cast; exact norm_algebraNorm_local g _)

end LocalGlobal

end SemistableReduction
