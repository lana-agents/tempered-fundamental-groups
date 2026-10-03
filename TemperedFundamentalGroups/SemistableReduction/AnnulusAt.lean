/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LocalModel

/-!
# The W7 → W8 interface at nodes: `IsAnnulusAt`

Blueprint §9.9 (interface correction). In the wild case the normalization of a node of the
base model in a cover is in general **not** a Kummer extension `T^d = ε u` of the base node
(`x = u^p + p u` over `{|p|^{p/(p-1)} < |x| < 1}`: the different is not constant along the
segment), so W7 delivers the node itself:

* `IsAnnulusAt ϖ x y d 𝔭`: the `O`-algebra `B` (a chart of the normalization) is, at the prime
  `𝔭`, étale-locally the node `Node O (ϖ ^ n) = O[u', v'] ⧸ (u' v' - ϖ ^ n)` at its singular
  point, and in the common étale neighbourhood the base node coordinates `x, y ∈ B` are
  `ε · u'^d`, `ε' · v'^d` with `ε, ε'` units (`d` is the multiplicity of the map of dual graphs
  along the edge, W8′).
* `IsAnnulusAt.isSemistableAt`: in particular `B` is semistable at `𝔭`
  (`LocalModel.IsSemistableAt`).
-/

universe u

namespace SemistableReduction

variable {O : Type u} [CommRing O] {B : Type u} [CommRing B] [Algebra O B]

/-- **`B` is an annulus over the node at `𝔭`, with base node coordinates `x, y` (pulled back to
`B`, `x y = ϖ ^ N`) of multiplicity `d`**: there are `n`, a common étale neighbourhood `C` of
`𝔭 ∈ Spec B` and of the singular point of `Spec (Node O (ϖ ^ n))` (as in `IsEtaleLocallyAt`,
with `u', v' ∈ 𝔮`), and units `ε, ε'` of `C` with `x = ε · u'^d` and `y = ε' · v'^d` in `C`,
`u', v'` the node coordinates. -/
def IsAnnulusAt (ϖ : O) (x y : B) (d : ℕ) (𝔭 : Ideal B) : Prop :=
  ∃ (n : ℕ) (C : Type u) (_ : CommRing C) (g : B →+* C) (f : Node O (ϖ ^ n) →+* C)
    (𝔮 : Ideal C), g.Etale ∧ f.Etale ∧ 𝔮.IsPrime ∧ 𝔮.comap g = 𝔭 ∧
      f.comp (algebraMap O (Node O (ϖ ^ n))) = g.comp (algebraMap O B) ∧
      f (Node.u (ϖ ^ n)) ∈ 𝔮 ∧ f (Node.v (ϖ ^ n)) ∈ 𝔮 ∧
      ∃ ε ε' : Cˣ, g x = ε * f (Node.u (ϖ ^ n)) ^ d ∧ g y = ε' * f (Node.v (ϖ ^ n)) ^ d

namespace IsAnnulusAt

variable {ϖ : O} {x y : B} {d : ℕ} {𝔭 : Ideal B}

/-- An annulus point is étale-locally a node. -/
theorem isEtaleLocallyAt (h : IsAnnulusAt ϖ x y d 𝔭) :
    ∃ n : ℕ, IsEtaleLocallyAt O (Node O (ϖ ^ n)) 𝔭 := by
  obtain ⟨n, C, _, g, f, 𝔮, hg, hf, h𝔮, hc, hO, -⟩ := h
  exact ⟨n, C, inferInstance, g, f, 𝔮, hg, hf, h𝔮, hc, hO⟩

/-- An annulus point is a semistable point. -/
theorem isSemistableAt (h : IsAnnulusAt ϖ x y d 𝔭) : IsSemistableAt ϖ 𝔭 :=
  Or.inl h.isEtaleLocallyAt

end IsAnnulusAt

end SemistableReduction
