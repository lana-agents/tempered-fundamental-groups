/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Setup.NoetherLine

/-!
# Equivariant Noether normalization for one-dimensional algebras

Let `R` be a finitely generated algebra of Krull dimension one over a field `K`, with an
action of a finite group `G` by `K`-algebra automorphisms. Then there is a `G`-invariant
`x : R` such that `K[X] → R`, `X ↦ x` is finite.

Proof: choose `y` with `K[y] → R` finite (`exists_finite_aeval`); the coefficients of the orbit
polynomial `∏_g (T - g • y)` are `G`-invariant and generate a finitely generated `K`-subalgebra
`S ⊆ R^G` over which `R` is integral, hence `S` has Krull dimension one; Noether normalization
of `S` gives the desired `x`.
-/

universe u

open Polynomial TemperedFundamentalGroups.NoetherLine

/-- A finitely generated algebra of Krull dimension one over a field, with an action of a finite
group by algebra automorphisms, is finite over a polynomial ring in one invariant variable. -/
theorem exists_finite_aeval_invariant {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] {G : Type u} [Group G] [Finite G] [MulSemiringAction G R]
    [SMulCommClass G K R] (hR : ringKrullDim R = 1) :
    ∃ x : R, (∀ g : G, g • x = x) ∧ (Polynomial.aeval (R := K) x).toRingHom.Finite := by
  have : Nontrivial R := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    simp [ringKrullDim_eq_bot_of_subsingleton] at hR
  have := Fintype.ofFinite G
  obtain ⟨y, hy⟩ := exists_finite_aeval (K := K) hR
  set p : R[X] := prodXSubSMul G R y
  set S : Subalgebra K R := Algebra.adjoin K (p.coeffs : Set R)
  -- `S` consists of invariants
  have hSinv : ∀ s ∈ S, ∀ g : G, g • s = s := by
    intro s hs g
    have hle : S ≤ AlgHom.equalizer (MulSemiringAction.toAlgHom K R g) (AlgHom.id K R) := by
      refine Algebra.adjoin_le fun c hc ↦ ?_
      obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact prodXSubSMul.coeff G R y g n
    exact hle hs
  -- `S` is finitely generated
  have : Algebra.FiniteType K S :=
    (Subalgebra.fg_iff_finiteType S).mp (Subalgebra.fg_adjoin_finset _)
  -- `y` is integral over `S`
  have hyS : IsIntegral S y := by
    have hlifts : p ∈ Polynomial.lifts (algebraMap S R) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      refine ⟨⟨p.coeff n, ?_⟩, rfl⟩
      by_cases h : p.coeff n = 0
      · rw [h]; exact S.zero_mem
      · exact Algebra.subset_adjoin (Polynomial.coeff_mem_coeffs h)
    obtain ⟨q, hq, -, hqm⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic hlifts (prodXSubSMul.monic G R y)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq]
    exact prodXSubSMul.eval G R y
  -- `R` is integral over `S`
  have hint : (algebraMap S R).IsIntegral := by
    let A := integralClosure S R
    have hyA : y ∈ A := hyS
    let φ : K[X] →+* A :=
      ((Polynomial.aeval (R := K) y).toRingHom).codRestrict A.toSubring fun f ↦ by
        induction f using Polynomial.induction_on with
        | C a =>
          simpa using A.algebraMap_mem (algebraMap K S a)
        | add f g hf hg => simpa using A.add_mem hf hg
        | monomial n a _ =>
          simpa [pow_succ, mul_assoc] using
            A.mul_mem (A.mul_mem (A.algebraMap_mem (algebraMap K S a)) (A.pow_mem hyA n)) hyA
    have h1 : (algebraMap A R).IsIntegral := by
      refine RingHom.IsIntegral.tower_top φ (algebraMap A R) ?_
      have : (algebraMap A R).comp φ = (Polynomial.aeval (R := K) y).toRingHom := rfl
      rw [this]
      exact hy.to_isIntegral
    have h2 : (algebraMap S A).IsIntegral := Algebra.IsIntegral.isIntegral
    exact RingHom.IsIntegral.trans (algebraMap S A) (algebraMap A R) h2 h1
  have : Algebra.IsIntegral S R := ⟨hint⟩
  -- `S` has Krull dimension one
  have hS : ringKrullDim S = 1 := by
    have hinj : Function.Injective (algebraMap S R) := Subtype.val_injective
    exact le_antisymm (hR ▸ ringKrullDim_le_of_isIntegral hinj)
      (hR ▸ ringKrullDim_le_of_isIntegral' (A := S) (B := R))
  obtain ⟨x, hx⟩ := exists_finite_aeval (K := K) hS
  refine ⟨x, hSinv x x.2, ?_⟩
  have hcomp : (Polynomial.aeval (R := K) (x : R)).toRingHom =
      (algebraMap S R).comp (Polynomial.aeval (R := K) x).toRingHom := by
    ext f
    · simp
    · simp
  rw [hcomp]
  refine RingHom.IsIntegral.to_finite (RingHom.IsIntegral.trans _ _ hx.to_isIntegral hint) ?_
  rw [← hcomp]
  refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap K K[X]) ?_
  have : (Polynomial.aeval (R := K) (x : R)).toRingHom.comp (algebraMap K K[X]) =
      algebraMap K R := by ext; simp
  rw [this]
  exact RingHom.finiteType_algebraMap.mpr inferInstance
