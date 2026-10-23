/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.CurveTower
import TemperedFundamentalGroups.Tempered.Comparison
import TemperedFundamentalGroups.Tempered.EtaleInvolution

/-!
# Levels of André's tower containing a root of a constant (Blueprint §12.8, M2.6)

For a nonzero constant `c ∈ K` and `ℓ ≥ 1`, every pointed member `q₀` of `galW` is dominated by a
pointed member `p` whose level ring contains an `ℓ`-th root of `c`
(**`exists_ptGal_pow_eq`**): the finite étale `R`-algebra `R ⊗_K E`, `E = K[X]/(q)` for an
irreducible factor `q` of `X^ℓ − c`, is a tempered covering (trivial model) and `galW` is
dominating.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Polynomial

namespace TemperedFundamentalGroups

noncomputable section

open GaloisLimit TempObj

section RootAlgebra

variable {K : Type u} [Field K] (ℓ : ℕ) (c : K)

/-- An irreducible factor of `X^ℓ − c`. -/
abbrev rootPoly : K[X] := factor (X ^ ℓ - C c)

/-- The field `K[X]/(q)` for an irreducible factor `q` of `X^ℓ − c`. -/
abbrev RootField : Type u := AdjoinRoot (rootPoly ℓ c)

variable {ℓ} (hℓ : ℓ ≠ 0)
include hℓ

lemma rootPoly_dvd : rootPoly ℓ c ∣ X ^ ℓ - C c := factor_dvd_of_not_isUnit
  (fun h ↦ by
    have := degree_eq_zero_of_isUnit h
    rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hℓ)] at this
    exact hℓ (by exact_mod_cast this))

lemma root_pow_eq : (AdjoinRoot.root (rootPoly ℓ c)) ^ ℓ =
    algebraMap K (RootField ℓ c) c := by
  obtain ⟨g, hg⟩ := rootPoly_dvd c hℓ
  have h := congrArg (aeval (AdjoinRoot.root (rootPoly ℓ c))) hg
  have h0 : aeval (AdjoinRoot.root (rootPoly ℓ c)) (rootPoly ℓ c) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [map_mul, h0, zero_mul, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

omit hℓ in
instance fact_irreducible_rootPoly : Fact (Irreducible (rootPoly ℓ c)) :=
  ⟨irreducible_factor _⟩

end RootAlgebra

section Obj

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A] [SMulCommClass A K R]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

variable (R) in
/-- The finite étale `R`-algebra `R ⊗_K E` adjoining a root of `X^ℓ − c`. -/
abbrev RootAlg (ℓ : ℕ) (c : K) : Type u := TensorProduct K R (RootField ℓ c)

omit [CharZero K] [Algebra.Smooth K R] [IsDomain R] in
lemma finite_rootAlg (ℓ : ℕ) (c : K) : Module.Finite R (RootAlg R ℓ c) := by
  haveI : Module.Finite K (RootField ℓ c) :=
    (AdjoinRoot.powerBasis (irreducible_factor (X ^ ℓ - C c)).ne_zero).finite
  infer_instance

omit [Algebra.Smooth K R] [IsDomain R] in
lemma etale_rootAlg (ℓ : ℕ) (c : K) : Algebra.Etale R (RootAlg R ℓ c) := by
  haveI : Module.Finite K (RootField ℓ c) :=
    (AdjoinRoot.powerBasis (irreducible_factor (X ^ ℓ - C c)).ne_zero).finite
  haveI : Algebra.FormallyEtale K (RootField ℓ c) :=
    Algebra.FormallyEtale.of_isSeparable K (RootField ℓ c)
  haveI : Algebra.FinitePresentation K (RootField ℓ c) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Etale K (RootField ℓ c) := ⟨inferInstance, inferInstance⟩
  infer_instance

variable (O A) in
/-- The tempered covering (trivial model) of `R ⊗_K E`. -/
abbrev rootObj (ℓ : ℕ) (c : K) : TempObj O R A :=
  (etaleToTemp O R A).obj
    (EtaleInvolution.etObj A (RootAlg R ℓ c) (etale_rootAlg ℓ c) (finite_rootAlg ℓ c))

omit [CharZero K] [Algebra.Smooth K R] [IsDomain R] in
/-- A geometric point of `R ⊗_K E`. -/
lemma nonempty_rootAlg_algHom (ℓ : ℕ) (c : K) :
    Nonempty (RootAlg R ℓ c →ₐ[R] Ω) := by
  have hdeg : (rootPoly ℓ c).map (algebraMap K Ω) ≠ 0 ∧
      ((rootPoly ℓ c).map (algebraMap K Ω)).degree ≠ 0 := by
    refine ⟨Polynomial.map_ne_zero (irreducible_factor _).ne_zero, ?_⟩
    rw [degree_map]
    exact (degree_pos_of_irreducible (irreducible_factor _)).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg.2
  have hz' : aeval z (rootPoly ℓ c) = 0 := by
    rwa [Polynomial.IsRoot, eval_map_algebraMap] at hz
  let g : RootField ℓ c →ₐ[K] Ω := AdjoinRoot.liftAlgHom _ (Algebra.ofId K Ω) z hz'
  exact ⟨Algebra.TensorProduct.lift (Algebra.ofId R Ω) g fun _ _ ↦ Commute.all _ _⟩

include hp in
/-- **Levels containing an `ℓ`-th root of a constant**: every pointed member `q₀` of `galW` is
dominated by a pointed member whose level ring contains an `ℓ`-th root of `c`. -/
theorem exists_ptGal_pow_eq (q₀ : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (c : K) :
    ∃ (p : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : p ⟶ q₀)
      (α : (curveData V hV hR p).Lv.L.B),
      α ^ ℓ = algebraMap R _ (algebraMap K R c) := by
  obtain ⟨t⟩ := nonempty_rootAlg_algHom (R := R) (Ω := Ω) ℓ c
  let X := rootObj (R := R) O A ℓ c
  let x : (tempFibre O R A V hV).obj X :=
    (etaleToTempFibreEquiv O R A V hV _).symm
      (t.comp (EtaleInvolution.etEquiv A (RootAlg R ℓ c) (etale_rootAlg ℓ c)
        (finite_rootAlg ℓ c)).toAlgHom)
  obtain ⟨G, hG, g, f, hf⟩ := (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.1 2
    ![⟨X, x⟩, ⟨q₀.G, q₀.g⟩]
  let p : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) := ⟨G, hG, g⟩
  refine ⟨p, ⟨_, ⟨f 1, rfl⟩, hf 1⟩, ?_⟩
  let m := (curveData V hV hR p).e.inv ≫ f 0
  let e := EtaleInvolution.etEquiv A (RootAlg R ℓ c) (etale_rootAlg ℓ c) (finite_rootAlg ℓ c)
  refine ⟨m.φ.f (e.symm (1 ⊗ₜ AdjoinRoot.root (rootPoly ℓ c))), ?_⟩
  have hy : (1 ⊗ₜ[K] AdjoinRoot.root (rootPoly ℓ c) : RootAlg R ℓ c) ^ ℓ =
      algebraMap R (RootAlg R ℓ c) (algebraMap K R c) := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow, root_pow_eq c hℓ,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one c,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_self_apply,
      Algebra.algebraMap_eq_smul_one]
  have h1 := congrArg (fun y ↦ m.φ.f (e.symm y)) hy
  simp only [map_pow, AlgEquiv.commutes] at h1
  exact (map_pow m.φ.f _ ℓ).symm.trans (h1.trans (m.φ.f.commutes _))

end Obj

end

end TemperedFundamentalGroups
