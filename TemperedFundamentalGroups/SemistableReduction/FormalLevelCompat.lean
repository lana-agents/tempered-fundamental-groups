/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalLevelAssemble

/-!
# Reduction of the level formal Kummer forms (MR12 T2 S6, step G2, compatibility)

The reduction `AdmissibleLift.pieceEquiv : N/K ≃ KummerPiece` of a lifted Kummer factor
`N = (R̂/(1 − ε̃)) ⊗_{O[u,v]/(uv − π^e)} O[s,t]/(st − π)` of the M2 lift, composed with a tensor map
`g ⊗ id : N' ⊗ O[s,t]/(st − π) → N`, is the reduction map `FormalLevel.redTensorMap` of `σ ∘ g`
(**`AdmissibleLift.pieceEquiv_mk_map`**). Applied to the level formal Kummer forms
(`FormalLevel.levelEquiv`, base changes of the chosen splittings `Φ`), this reduces the comparison
of the level-`n` forms with the formal Kummer form of the special fibre (the `kummer` field of the
covering, `FormalKummer.kummerEquivOf`) to the equality of maps `N₁ → R̂'` out of the étale
neighbourhoods, which holds by `FormalLevel.hatLift_unique`.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace AdmissibleLift

noncomputable section

open KummerEtale

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] (f : R) [Algebra k (R ⧸ J θ)]
  (φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)) {π : O} {e : ℕ} (he : 0 < e)
  (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)
  (εb : Admissible.Hat (fbar θ f)) (hε : ψ θ f ε = εb)
  (hθ : Function.Surjective θ) (hπ : θ π = 0)
  (hχ : ∀ a, ψ θ f (χ a) = φ (Admissible.nodeCongr he (Node.baseMap θ (hA hπ) a)))

include hχ in
lemma σ_algebraMap_A (a : A π e) :
    σ θ f φ he χ ε εb hε (algebraMap (A π e) (LPiece f χ ε) a) =
      algebraMap (A (0 : k) e) (Admissible.PieceBase φ εb he)
        (Node.baseMap θ (FormalKummer.θ_pow (d := e) hπ) a) := by
  rw [LPiece.algebraMap_A, σ_mk, hχ]
  rfl

/-- **The reduction of a tensor map into a lifted Kummer factor**: for an
`O[u,v]/(uv − π^e)`-algebra
map `g : N' → R̂/(1 − ε̃)`, `pieceEquiv ∘ (g ⊗ id)` is the reduction map of `σ ∘ g`. -/
theorem pieceEquiv_mk_map [IsNoetherianRing R] {N' : Type u} [CommRing N']
    [Algebra (A π e) N'] (g : N' →ₐ[A π e] LPiece f χ ε) (z : N' ⊗[A π e] KNode π e) :
    pieceEquiv f φ he χ ε εb hε hθ hπ hχ (Ideal.Quotient.mk _
      (Algebra.TensorProduct.map g (FormalLevel.knodeEquiv π e).toAlgHom z)) =
      FormalLevel.redTensorMap θ hπ ((σ θ f φ he χ ε εb hε).comp g.toRingHom) (fun a ↦ by
        rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
        exact σ_algebraMap_A f φ he χ ε εb hε hπ hχ a) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    rw [Algebra.TensorProduct.map_tmul, pieceEquiv_mk_tmul, FormalLevel.redTensorMap_tmul]
    rfl
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw, map_add]

end

end AdmissibleLift

end SemistableReduction
