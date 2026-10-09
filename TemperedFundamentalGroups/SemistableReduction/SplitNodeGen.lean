/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SplitNode
import TemperedFundamentalGroups.SemistableReduction.SmoothLemma

/-!
# Generization of split semistability

Blueprint §10.3.8. `IsSplitSemistableAt.of_le`: a generization of a split node is the node itself
(étale maps are quasi-finite, `Algebra.QuasiFinite.eq_of_le_of_under_eq`) or étale-locally `O[X]`
(one of `u, v` is a unit there, `Node.isEtaleLocallyAt_of_u_notMem`);
`IsSplitSemistableAt.of_le_of_notMem`: generic-fibre generizations are étale-locally `O[X]`.
-/

universe u

open Polynomial IsLocalRing

namespace SemistableReduction

variable {O : Type u} [CommRing O] {ϖ : O} {A : Type u} [CommRing A] [Algebra O A]

namespace IsSplitSemistableAt

/-- From a split node at `𝔮` of the neighbourhood: at a generization `𝔮'` of `𝔮` either the
neighbourhood is étale-locally `O[X]` (one of `u, v` is a unit) or `𝔮' = 𝔮`. -/
private lemma generize [IsLocalRing O] (hϖ : maximalIdeal O ≤ Ideal.span {ϖ}) {n : ℕ}
    {C : Type u} [CommRing C] {g : A →+* C} {f : Node O (ϖ ^ n) →+* C} (hg : g.Etale)
    (hf : f.Etale) (hO : f.comp (algebraMap O (Node O (ϖ ^ n))) = g.comp (algebraMap O A))
    {𝔮 𝔮' : Ideal C} [𝔮.IsPrime] [𝔮'.IsPrime] (hle : 𝔮' ≤ 𝔮) :
    IsEtaleLocallyAt O O[X] (𝔮'.comap g) ∨ 𝔮' = 𝔮 := by
  by_cases huv : f (Node.u (ϖ ^ n)) ∈ 𝔮' ∧ f (Node.v (ϖ ^ n)) ∈ 𝔮'
  · right
    letI : Algebra (Node O (ϖ ^ n)) C := f.toAlgebra
    haveI : Algebra.Etale (Node O (ϖ ^ n)) C := hf
    refine Algebra.QuasiFinite.eq_of_le_of_under_eq (R := Node O (ϖ ^ n)) 𝔮' 𝔮 hle ?_
    refine le_antisymm (Ideal.comap_mono hle) fun x hx ↦ ?_
    change f x ∈ 𝔮 at hx
    change f x ∈ 𝔮'
    obtain ⟨o, ho⟩ := Node.exists_sub_mem_span x
    have hspan : ∀ y ∈ Ideal.span {Node.u (ϖ ^ n), Node.v (ϖ ^ n)}, f y ∈ 𝔮' := by
      intro y hy
      have : Ideal.span {Node.u (ϖ ^ n), Node.v (ϖ ^ n)} ≤ 𝔮'.comap f := by
        rw [Ideal.span_le]
        rintro z (rfl | rfl)
        · exact huv.1
        · exact huv.2
      exact this hy
    have h1 := hspan _ ho
    rw [map_sub] at h1
    have hfo : f (algebraMap O _ o) = g (algebraMap O A o) := by
      rw [← RingHom.comp_apply, hO, RingHom.comp_apply]
    rw [hfo] at h1
    suffices g (algebraMap O A o) ∈ 𝔮' by simpa using 𝔮'.add_mem h1 this
    by_cases hunit : IsUnit o
    · exfalso
      have h2 := 𝔮.sub_mem hx (hle (hspan _ ho))
      rw [map_sub, hfo, sub_sub_cancel] at h2
      exact ‹𝔮.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 ((hunit.map _).map _))
    · obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hϖ ((mem_maximalIdeal _).2 hunit))
      rw [← hr, map_mul, map_mul]
      exact Ideal.mul_mem_left _ _ (IsSplitNodePt.mem_of_u_v_mem hO huv.2)
  · left
    letI : Algebra O C := (g.comp (algebraMap O A)).toAlgebra
    let fA : Node O (ϖ ^ n) →ₐ[O] C :=
      { f with commutes' := fun o ↦ congrArg (fun φ : O →+* C ↦ φ o) hO }
    let gA : A →ₐ[O] C := { g with commutes' := fun _ ↦ rfl }
    have h₀ : IsEtaleLocallyAt O O[X] (𝔮'.comap fA.toRingHom) := by
      rcases not_and_or.1 huv with h | h
      · exact Node.isEtaleLocallyAt_of_u_notMem _ h
      · exact Node.isEtaleLocallyAt_of_v_notMem _ h
    exact (IsEtaleLocallyAt.of_etale fA hf 𝔮' h₀).of_etale_of_comap gA hg

/-- **Generization** of split semistability. -/
theorem of_le [IsLocalRing O] (hϖ : maximalIdeal O ≤ Ideal.span {ϖ}) {𝔭 𝔭' : Ideal A}
    [𝔭'.IsPrime] (h : IsSplitSemistableAt ϖ 𝔭) (hle : 𝔭' ≤ 𝔭) : IsSplitSemistableAt ϖ 𝔭' := by
  rcases h with h | h
  · exact .inl (h.of_le hle)
  obtain ⟨n, C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp, hu, hv, hs⟩ := h
  letI : Algebra A C := g.toAlgebra
  haveI : Algebra.Etale A C := hg
  haveI : 𝔭.IsPrime := hcomap ▸ Ideal.comap_isPrime g 𝔮
  haveI : 𝔮.LiesOver 𝔭 := ⟨hcomap.symm⟩
  obtain ⟨𝔮', hle', h𝔮', hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭') (q := 𝔭) 𝔮 hle
  have h𝔭' : 𝔮'.comap g = 𝔭' := hlies.over.symm
  rcases generize hϖ hg hf hcomp hle' with h' | h'
  · exact .inl (h𝔭' ▸ h')
  · subst h'
    exact .inr ⟨n, C, inferInstance, g, f, 𝔮', hg, hf, h𝔮', h𝔭', hcomp, hu, hv, hs⟩

/-- **Generization to the generic fibre**: at a generization not containing `ϖ`, a split
semistable point is étale-locally `O[X]`. -/
theorem of_le_of_notMem [IsLocalRing O] (hϖ : maximalIdeal O ≤ Ideal.span {ϖ})
    {𝔭 𝔭' : Ideal A} [𝔭'.IsPrime] (h : IsSplitSemistableAt ϖ 𝔭) (hle : 𝔭' ≤ 𝔭)
    (hϖ' : algebraMap O A ϖ ∉ 𝔭') : IsEtaleLocallyAt O O[X] 𝔭' := by
  rcases h.of_le hϖ hle with h | h
  · exact h
  · exact absurd h.algebraMap_mem hϖ'

end IsSplitSemistableAt

end SemistableReduction
