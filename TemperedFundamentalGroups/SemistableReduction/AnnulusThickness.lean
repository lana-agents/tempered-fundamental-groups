/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.AnnulusAt

/-!
# Thickness scaling at annulus points (W8′)

Blueprint §9.7. If the base node coordinates `x, y` (`x y = ϖ ^ N`) are, at a point `𝔭` of a
cover, of the form `x = ε u' ^ d`, `y = ε' v' ^ d` in an étale node chart `O[u', v'] ⧸ (u' v' - ϖ ^ n)`
at its singular point (`IsAnnulusAt ϖ x y d 𝔭`), then `N = d n`: the thickness of the base node is
the local degree times the thickness of the node above it (`IsAnnulusAt.thickness_eq`). This is
the length scaling of the map of metrized dual graphs.
-/

universe u

namespace SemistableReduction

variable {O : Type u} [CommRing O]

namespace Node

/-- `O → O[u, v] ⧸ (u v - a)` is injective for a domain `O` and `a ≠ 0`. -/
theorem algebraMap_injective [IsDomain O] {a : O} (ha : a ≠ 0) :
    Function.Injective (algebraMap O (Node O a)) := by
  rw [injective_iff_map_eq_zero]
  intro o ho
  have h := congrArg (fun p ↦ (laurent a 1 p).coeff 0) ho
  simp only [AlgHom.commutes, map_zero, LaurentPolynomial.algebraMap_apply,
    LaurentPolynomial.C_apply, if_pos rfl] at h
  exact (FaithfulSMul.algebraMap_injective O (FractionRing O)) (h.trans (map_zero _).symm)

end Node

/-- In an étale neighbourhood of a node over a domain, the images of nonzero elements of `O` are
nonzerodivisors. -/
theorem isSMulRegular_of_etale [IsDomain O] {a : O} (ha : a ≠ 0) {C : Type u} [CommRing C]
    {f : Node O a →+* C} (hf : f.Etale) {o : O} (ho : o ≠ 0) :
    IsSMulRegular C (f (algebraMap O (Node O a) o)) := by
  haveI := Node.isDomain ha
  letI := f.toAlgebra
  haveI : Module.Flat (Node O a) C := (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1
  have hr : IsSMulRegular (Node O a) (algebraMap O (Node O a) o) :=
    (IsRegular.of_ne_zero ((map_ne_zero_iff _ (Node.algebraMap_injective ha)).mpr ho)).isSMulRegular
  exact hr.of_flat

variable [IsDomain O] {ϖ : O} {B : Type u} [CommRing B] [Algebra O B]

/-- **Thickness scaling.** At an annulus point with base node coordinates `x y = ϖ ^ N`, the
cover is étale-locally a node of thickness `n ≥ 1` with `N = d n`. -/
theorem IsAnnulusAt.thickness_eq (hϖ : ϖ ≠ 0) {x y : B} {d N : ℕ} {𝔭 : Ideal B}
    (hxy : x * y = algebraMap O B (ϖ ^ N)) (h : IsAnnulusAt ϖ x y d 𝔭) :
    ∃ n, 0 < n ∧ IsEtaleLocallyAt O (Node O (ϖ ^ n)) 𝔭 ∧ N = d * n := by
  obtain ⟨n, C, _, g, f, 𝔮, hg, hf, h𝔮, hc, hO, hu, hv, ε, ε', hx, hy⟩ := h
  have hO' : ∀ o : O, g (algebraMap O B o) = f (algebraMap O (Node O (ϖ ^ n)) o) := fun o ↦
    (congrArg (fun φ : O →+* C ↦ φ o) hO).symm
  set a := f (algebraMap O (Node O (ϖ ^ n)) ϖ) with ha
  have hpow : ∀ k, f (algebraMap O (Node O (ϖ ^ n)) (ϖ ^ k)) = a ^ k := fun k ↦ by
    rw [map_pow (algebraMap O (Node O (ϖ ^ n))) ϖ k, map_pow f]
  -- the relation `a ^ N = ε ε' a ^ (n d)` in `C`
  have hrel : a ^ N = ↑(ε * ε') * a ^ (n * d) := by
    rw [← hpow, ← hO', ← hxy, map_mul, hx, hy, pow_mul, ← hpow, ← Node.u_mul_v, map_mul,
      mul_pow, Units.val_mul]
    ring
  -- `n ≥ 1` and `a ∈ 𝔮`
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      apply h𝔮.ne_top
      rw [Ideal.eq_top_iff_one]
      have : f (Node.u (ϖ ^ 0)) * f (Node.v (ϖ ^ 0)) = 1 := by
        rw [← map_mul, Node.u_mul_v]
        exact (hpow 0).trans (pow_zero a)
      rw [← this]
      exact Ideal.mul_mem_right _ _ hu
    · exact hn
  have ha𝔮 : a ∈ 𝔮 := by
    refine h𝔮.mem_of_pow_mem n ?_
    rw [← hpow, ← Node.u_mul_v, map_mul]
    exact Ideal.mul_mem_right _ _ hu
  have hreg : ∀ k, ∀ s ∉ 𝔮, s * a ^ k ≠ 0 := by
    intro k s hs hsa
    have := (isSMulRegular_of_etale (pow_ne_zero n hϖ) hf (pow_ne_zero k hϖ))
    rw [hpow] at this
    apply hs
    have h0 : a ^ k • s = a ^ k • 0 := by rw [smul_eq_mul, mul_comm, hsa, smul_zero]
    rw [this h0]
    exact 𝔮.zero_mem
  have hunit : ∀ e : Cˣ, (e : C) ∉ 𝔮 := fun e he ↦
    h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ he e.isUnit)
  refine ⟨n, hn, ⟨C, inferInstance, g, f, 𝔮, hg, hf, h𝔮, hc, hO⟩, ?_⟩
  rcases lt_trichotomy N (d * n) with hlt | heq | hgt
  · exfalso
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    have hkN : k + 1 + N = n * d := by rw [mul_comm]; omega
    have h1 : (1 - ↑(ε * ε') * a ^ (k + 1)) * a ^ N = 0 := by
      rw [sub_mul, one_mul, mul_assoc, ← pow_add, hkN, ← hrel, sub_self]
    refine hreg N _ ?_ h1
    intro hmem
    apply h𝔮.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : C) = (1 - ↑(ε * ε') * a ^ (k + 1)) + ↑(ε * ε') * a ^ (k + 1) := by ring
    rw [this]
    exact Ideal.add_mem _ hmem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ha𝔮 _ k.succ_pos))
  · exact heq
  · exfalso
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
    have hkN : k + 1 + n * d = N := by rw [mul_comm]; omega
    have h1 : (a ^ (k + 1) - ↑(ε * ε')) * a ^ (n * d) = 0 := by
      rw [sub_mul, ← pow_add, hkN, hrel, sub_self]
    refine hreg (n * d) _ ?_ h1
    intro hmem
    apply hunit (ε * ε')
    have : (↑(ε * ε') : C) = a ^ (k + 1) - (a ^ (k + 1) - ↑(ε * ε')) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.pow_mem_of_mem _ ha𝔮 _ k.succ_pos) hmem

end SemistableReduction
