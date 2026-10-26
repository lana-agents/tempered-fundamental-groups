/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerChart
import TemperedFundamentalGroups.SemistableReduction.AdmissibleCovering

/-!
# The admissible covering of the special fibre defined by a normalisation (MR12 T2 S5/S6)

For a chart `R` over `O` with node coordinates `x y = ϖⁿ`, an `R`-algebra `B` (the normalisation of
the chart in a tame cover) and chosen Kummer data `D j` at the nodes (`KummerNormAtData`), the
special fibre `C = B/JB` is an admissible covering of the special fibre of the chart
(`Admissible.Covering`) once it is finite and étale off the nodes:
**`FormalKummer.covOf`**, with Kummer factors indexed by `Σ j, Fin (D j).r`, idempotents
`CompletionProd.idem`, indices `dⱼᵢ`, no marked points, and `kummer` the formal Kummer form
`kummerEquivOf` (`covOf_C`, `covOf_kummer` are `rfl`). Stating the coverings of the Tate charts
through `covOf` lets S6 compare their `kummer` fields with the level formal Kummer forms
generically.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalKummer

noncomputable section

open KummerEtale AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ϖ : O} {n M' : ℕ} {x y : R}

/-- **The admissible covering of the special fibre defined by `B`** (see the module docstring). -/
def covOf (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
    {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
    (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
    (hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
    (D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j)) {f : Rs θ R}
    (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
    (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
    (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
    (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
    (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
    (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y))
    (ψ : Polynomial k →ₐ[k] Admissible.Hat f)
    (hfin : Module.Finite (Rs θ R) (Cs θ R B))
    (het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) f).Etale)
    (hk : ∀ j i, ((D j).d i : k) ≠ 0) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    Admissible.Covering φ ψ :=
  haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  { C := Cs θ R B
    finite := hfin
    etale := het
    ι := Σ j, Fin (D j).r
    idem := fun p ↦ CompletionProd.idem hinj hf hrad p.1
    isIdempotentElem_idem := fun p ↦ CompletionProd.isIdempotentElem_idem hinj hf hrad p.1
    e := fun p ↦ (D p.1).d p.2
    e_pos := fun p ↦ (D p.1).hd p.2
    e_ne_zero := fun p ↦ hk p.1 p.2
    κ := Empty
    cidem := Empty.elim
    isIdempotentElem_cidem := fun i ↦ i.elim
    ce := Empty.elim
    ce_pos := fun i ↦ i.elim
    ce_ne_zero := fun i ↦ i.elim
    kummer := (kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv).trans
      AlgEquiv.prodUnique.symm }

end

end FormalKummer

end SemistableReduction
