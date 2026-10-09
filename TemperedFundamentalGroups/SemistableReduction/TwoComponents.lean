/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Statement
import TemperedFundamentalGroups.SemistableReduction.NoLoopsPrimes
import TemperedFundamentalGroups.SemistableReduction.EtaleLocalDomain

/-!
# Points on two components are nodes (geometric input for B5)

The dual graph of a model `c` (`DualGraph.lean`) has as edges the **node points**
(`ModelCode.IsNodePt`: points of the special fibre which are not smooth, i.e. not étale-locally
the affine line `O[u]`), while the universal covering of the special fibre
(`TemperedFundamentalGroups.universalCovering`, built from `curveConfig`) branches at the
**special points**: the points lying on two distinct irreducible components. Theorem B (B5)
needs that these agree, i.e. that a smooth point lies on only one component.

`Statement.NodeOfTwoComponents` is this fact for semistable models over discrete valuation
rings. It is a statement of local commutative algebra (Blueprint §9.7, XL10, second half): at a
smooth point `y`, `c` is étale-locally `O[u]`, so the local ring of the special fibre at `y` has
an étale local neighbourhood which is a localization of `κ[u]`, a domain; flat local maps satisfy
going down, so the minimal primes of the local ring of the special fibre at `y` (the components
through `y`) inject into those of the neighbourhood, of which there is one. 
It is proved here (`nodeOfTwoComponents`):
* `SemistableReduction.exists_least_prime_of_etale_polynomial`: for `f : O[u] → C` étale and a
  prime `𝔮` of `C` over the maximal ideal of `O`, the primes of `C` inside `𝔮` over the special
  fibre have a least element (the special fibre `κ[u] ⊗_{O[u]} C` is étale over the normal domain
  `κ[u]`, so its local rings are domains, `isDomain_localization_of_etale`);
* étale maps are flat, hence have going down: the two minimal primes of the special fibre inside
  the prime of `y` (`ModelCode.exists_minimal_primes_of_mem`) lift into `𝔮`, so both contain the
  contraction of the least prime of `C`, and by minimality they agree.
Semistability is not needed: the statement holds for every model over a DVR.
-/

universe u

open Polynomial TensorProduct CategoryTheory AlgebraicGeometry

namespace SemistableReduction

/-- In a local ring of an étale algebra over a normal domain, the zero ideal is prime: the
primes contained in a given prime `Q` have a least element. -/
theorem exists_least_prime_of_etale (B : Type*) {E : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [CommRing E] [Algebra B E] [Algebra.Etale B E] (Q : Ideal E)
    [Q.IsPrime] :
    ∃ P₀ : Ideal E, P₀.IsPrime ∧ P₀ ≤ Q ∧ ∀ R : Ideal E, R.IsPrime → R ≤ Q → P₀ ≤ R := by
  haveI := isDomain_localization_of_etale B Q
  refine ⟨(⊥ : Ideal (Localization.AtPrime Q)).comap (algebraMap E _),
    Ideal.comap_isPrime _ _, ?_, fun R hR hRQ ↦ ?_⟩
  · calc _ ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
          (algebraMap E (Localization.AtPrime Q)) := Ideal.comap_mono bot_le
      _ = Q := Localization.AtPrime.under_maximalIdeal (I := Q)
  · have hdisj : Disjoint (Q.primeCompl : Set E) R := by
      rw [Set.disjoint_left]
      intro x hx hxR
      exact hx (hRQ hxR)
    calc _ ≤ (R.map (algebraMap E (Localization.AtPrime Q))).comap
          (algebraMap E (Localization.AtPrime Q)) := Ideal.comap_mono bot_le
      _ = R := IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl
          (Localization.AtPrime Q) hR hdisj

/-- **The special fibre of an étale neighbourhood of `O[u]` is locally irreducible.** If
`f : O[u] → C` is étale and `𝔮` is a prime of `C` over the maximal ideal `𝔪` of `O` (a point of the
special fibre), the primes of `C` inside `𝔮` and over `𝔪` have a least element: the special fibre
`κ[u] ⊗_{O[u]} C` is étale over the normal domain `κ[u]`, so its local ring at `𝔮` is a domain. -/
theorem exists_least_prime_of_etale_polynomial {O C : Type u} [CommRing O] [CommRing C]
    (𝔪 : Ideal O) [𝔪.IsMaximal] (f : O[X] →+* C) (hf : f.Etale) (𝔮 : Ideal C) [𝔮.IsPrime]
    (h𝔮 : 𝔪 ≤ 𝔮.comap (f.comp (algebraMap O O[X]))) :
    ∃ q₀ : Ideal C, q₀.IsPrime ∧ q₀ ≤ 𝔮 ∧ 𝔪 ≤ q₀.comap (f.comp (algebraMap O O[X])) ∧
      ∀ q : Ideal C, q.IsPrime → q ≤ 𝔮 → 𝔪 ≤ q.comap (f.comp (algebraMap O O[X])) → q₀ ≤ q := by
  letI : Algebra O[X] C := f.toAlgebra
  haveI : Algebra.Etale O[X] C := hf
  letI : Field (O ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  set φ : O[X] →+* (O ⧸ 𝔪)[X] := Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪) with hφ
  letI : Algebra O[X] (O ⧸ 𝔪)[X] := φ.toAlgebra
  have hφs : Function.Surjective (algebraMap O[X] (O ⧸ 𝔪)[X]) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  let Dt := (O ⧸ 𝔪)[X] ⊗[O[X]] C
  let ρ : C →+* Dt := (Algebra.TensorProduct.includeRight : C →ₐ[O[X]] Dt).toRingHom
  have hρ : Function.Surjective ρ := Algebra.TensorProduct.includeRight_surjective C hφs
  -- every prime of `C` over the special fibre comes from `Dt`
  have lift : ∀ q : Ideal C, q.IsPrime → 𝔪 ≤ q.comap (f.comp (algebraMap O O[X])) →
      ∃ R : Ideal Dt, R.IsPrime ∧ R.comap ρ = q := by
    intro q hq hm
    have hker : RingHom.ker φ ≤ q.comap f := by
      rw [hφ, Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_le_iff_le_comap,
        Ideal.comap_comap]
      exact hm
    haveI : (q.comap f).IsPrime := Ideal.comap_isPrime f q
    haveI hP : ((q.comap f).map φ).IsPrime := Ideal.map_isPrime_of_surjective hφs hker
    have hcomap : ((q.comap f).map φ).comap (algebraMap O[X] (O ⧸ 𝔪)[X]) =
        q.comap (algebraMap O[X] C) := by
      change ((q.comap f).map φ).comap φ = q.comap f
      rw [Ideal.comap_map_of_surjective φ hφs, sup_eq_left]
      exact le_trans (Ideal.comap_mono bot_le) hker
    obtain ⟨R, hR, -, hR₂⟩ := exists_isPrime_tensorProduct _ q hcomap
    exact ⟨R, hR, hR₂⟩
  obtain ⟨QD, hQD, hQDq⟩ := lift 𝔮 inferInstance h𝔮
  obtain ⟨P₀, hP₀, hP₀le, hP₀min⟩ := @exists_least_prime_of_etale ((O ⧸ 𝔪)[X]) Dt _ _ _
    Algebra.TensorProduct.instCommRing _ _ QD hQD
  let q₀ : Ideal C := P₀.comap ρ
  have hmapR : ∀ R : Ideal Dt, R = (R.comap ρ).map ρ := fun R ↦
    (Ideal.map_comap_of_surjective ρ hρ R).symm
  refine ⟨q₀, Ideal.comap_isPrime _ _, ?_, ?_, ?_⟩
  · rw [← hQDq]; exact Ideal.comap_mono hP₀le
  · intro m hm
    simp only [Ideal.mem_comap, q₀]
    have : ρ (f (algebraMap O O[X] m)) = 0 := by
      change (1 : (O ⧸ 𝔪)[X]) ⊗ₜ[O[X]] (algebraMap O[X] C (algebraMap O O[X] m)) = 0
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      have : algebraMap O[X] (O ⧸ 𝔪)[X] (algebraMap O O[X] m) = 0 := by
        change φ (Polynomial.C m) = 0
        rw [hφ, Polynomial.coe_mapRingHom, Polynomial.map_C,
          Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
      rw [this, TensorProduct.zero_tmul]
    rw [RingHom.comp_apply, this]
    exact zero_mem _
  · intro q hq hqle hm
    obtain ⟨R, hR, hRq⟩ := lift q hq hm
    have hRle : R ≤ QD := by
      rw [hmapR R, hmapR QD, hRq, hQDq]; exact Ideal.map_mono hqle
    rw [← hRq]
    exact Ideal.comap_mono (hP₀min R hR hRle)

end SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction

/-- **Points on two components are nodes**: for a semistable projective model `c` over a
discrete valuation ring, every point of the special fibre lying on two distinct irreducible
components of the special fibre is a node point (equivalently: a smooth point lies on exactly
one component). -/
def Statement.NodeOfTwoComponents : Prop :=
  ∀ (K' : Type u) [Field K'] (O' : ValuationSubring K') [IsDiscreteValuationRing O'] (ϖ' : O'),
    Irreducible ϖ' → ∀ c : TemperedFundamentalGroups.ModelCode O',
    ModelCode.IsSemistable ϖ' c → ∀ (y : c.scheme), ∀ v ∈ ModelCode.components c,
    ∀ w ∈ ModelCode.components c, v ≠ w → y ∈ v → y ∈ w → ModelCode.IsNodePt c y

/-- **Points on two components are nodes** (for every model over a DVR, semistable or not). -/
theorem nodeOfTwoComponents : Statement.NodeOfTwoComponents := by
  intro K' _ O' _ ϖ hϖ c _ y v hv w hw hvw hyv hyw
  refine ⟨hv.2.1 hyv, fun hsm ↦ ?_⟩
  obtain ⟨U, hU, hyU, hloc⟩ := hsm
  letI := ModelCode.sectionsAlgebra c U
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp⟩ := hloc
  obtain ⟨P₁, P₂, hp₁, hp₂, hϖ₁, hϖ₂, hle₁, hle₂, hmin₁, hmin₂, hne⟩ :=
    ModelCode.exists_minimal_primes_of_mem hϖ hv hw hvw hyv hyw hU hyU
  set 𝔭 := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
  have hmax : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  -- a prime of `Γ(U)` contains `ϖ` iff it lies over the maximal ideal of `O'`
  have hm : ∀ P : Ideal Γ(c.scheme, U), algebraMap O' _ ϖ ∈ P →
      IsLocalRing.maximalIdeal O' ≤ P.comap (algebraMap O' _) := by
    intro P hP
    rw [hmax, Ideal.span_le, Set.singleton_subset_iff]
    exact hP
  have hcomp' : ∀ Q : Ideal C, Q.comap (f.comp (algebraMap O' O'[X])) =
      (Q.comap g).comap (algebraMap O' _) := by
    intro Q
    rw [hcomp, Ideal.comap_comap]
  have hy : algebraMap O' Γ(c.scheme, U) ϖ ∈ 𝔭 := by
    rw [← ModelCode.mem_Z_iff hϖ hU hyU]
    exact hv.2.1 hyv
  obtain ⟨q₀, hq₀, -, hq₀m, hq₀min⟩ :=
    _root_.SemistableReduction.exists_least_prime_of_etale_polynomial
      (IsLocalRing.maximalIdeal O') f hf 𝔮 (by rw [hcomp', hcomap]; exact hm _ hy)
  -- going down along the flat map `g`
  letI : Algebra Γ(c.scheme, U) C := g.toAlgebra
  haveI : Algebra.Etale Γ(c.scheme, U) C := hg
  haveI : 𝔮.LiesOver 𝔭 := ⟨hcomap.symm⟩
  have key : ∀ P : Ideal Γ(c.scheme, U), P.IsPrime → algebraMap O' _ ϖ ∈ P → P ≤ 𝔭 →
      (∀ Q : Ideal Γ(c.scheme, U), Q.IsPrime → algebraMap O' _ ϖ ∈ Q → Q ≤ P → Q = P) →
      q₀.comap g = P := by
    intro P hP hϖP hP𝔭 hminP
    obtain ⟨Q, hQ𝔮, hQ, hQP⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P) 𝔮 hP𝔭
    have hQP' : Q.comap g = P := hQP.over.symm
    have hQm : IsLocalRing.maximalIdeal O' ≤ Q.comap (f.comp (algebraMap O' O'[X])) := by
      rw [hcomp', hQP']; exact hm P hϖP
    refine hminP _ (Ideal.comap_isPrime g q₀) ?_ ?_
    · have : ϖ ∈ IsLocalRing.maximalIdeal O' := by
        rw [hmax]; exact Ideal.subset_span rfl
      have := hq₀m this
      rwa [hcomp'] at this
    · rw [← hQP']; exact Ideal.comap_mono (hq₀min Q hQ hQ𝔮 hQm)
  exact hne ((key P₁ hp₁ hϖ₁ hle₁ hmin₁).symm.trans (key P₂ hp₂ hϖ₂ hle₂ hmin₂))

end TemperedFundamentalGroups.SemistableReduction
