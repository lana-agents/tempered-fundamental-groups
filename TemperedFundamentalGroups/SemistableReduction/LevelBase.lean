/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelStep

/-!
# Consecutive levels with a common base covering (Blueprint §12.8, M2.3 (e'))

To patch one admissible covering at every level of a model, the coverings of the special fibres
`R_n/J_n` of the level charts are all transported from one covering `cov₀` of a fixed special
fibre `R₀` along isomorphisms `e_n : R₀ ≃ R_n/J_n` (`Admissible.Covering.transport`); they then
share the algebra, the index sets and the ramification indices definitionally. This file restates
the comparisons of `LevelStep` for two consecutive levels `R → R'` with coverings
`cov₀.transport e₁`, `cov₀.transport e₂`, `e₂ ∘ e₁⁻¹` induced by `q : R → R'` (`he`):

* `LevelStep.square_base`: `ψ_{R'} ∘ ψ_q = Ê₂ ∘ Ê₁⁻¹ ∘ ψ_R` (from `LevelStep.square` and
  `Admissible.hatEquiv_trans`, `hatEquiv_symm`);
* `hε_base`, `hχ_base`, `eq_idem_base`: reductions of lift data are lift data;
* **`pieceEquiv_ρ_base`**, **`cuspEquiv_ρc_base`**: the reduction equivalences of the Kummer and
  cusp factors at the two levels commute with `ρ`, `ρc` and the transport isomorphisms.
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

open KummerEtale AdmissibleLift

namespace LevelStep

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {R' : Type u} [CommRing R'] [Algebra O R']
  [Algebra R R'] (f : R)
  [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {e₁ : R₀ ≃ₐ[k] (R ⧸ J θ (R := R))} {e₂ : R₀ ≃ₐ[k] (R' ⧸ J θ (R := R'))}
  (h₁ : e₁ f₀ = fbar θ f)
  (he : ∀ r : R, e₂ (e₁.symm (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (algebraMap R R' r))

include h₁ he in
lemma h₂ : e₂ f₀ = fbar θ (f' (R' := R') f) := by
  change e₂ f₀ = Ideal.Quotient.mk _ (algebraMap R R' f)
  rw [← he f, show Ideal.Quotient.mk (J θ (R := R)) f = e₁ f₀ from h₁.symm,
    AlgEquiv.symm_apply_apply]

/-! ### The completion square -/

include h₁ he in
/-- **The completion maps of consecutive levels and the base**: `ψ_{R'} ∘ ψ_q = Ê₂ ∘ Ê₁⁻¹ ∘ ψ_R`. -/
theorem square_base (x : FormalPatchLevel.Hat f) :
    ψ θ (f' (R' := R') f) (KummerReduce.ψI f x) =
      Admissible.hatEquiv e₂ (h₂ f h₁ he) ((Admissible.hatEquiv e₁ h₁).symm (ψ θ f x)) := by
  rw [square (e := e₁.symm.trans e₂) f he, Admissible.hatEquiv_symm,
    ← Admissible.hatEquiv_trans]

/-! ### Lift data -/

variable {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}

include h₁ he in
lemma hε_base {ε : FormalPatchLevel.Hat f} {ε₀ : Admissible.Hat f₀}
    (hε : ψ θ f ε = Admissible.hatEquiv e₁ h₁ ε₀) :
    ψ θ (f' (R' := R') f) (KummerReduce.ψI f ε) = Admissible.hatEquiv e₂ (h₂ f h₁ he) ε₀ := by
  rw [square_base f h₁ he, hε, AlgEquiv.symm_apply_apply]

include h₁ he in
lemma hχ_base {π : O} {n : ℕ} (hn : 0 < n) (hπ : θ π = 0)
    {χ : A π n →ₐ[O] FormalPatchLevel.Hat f}
    (hχ : ∀ a, ψ θ f (χ a) =
      Admissible.φT (h := h₁) φ₀ (Admissible.nodeCongr hn (Node.baseMap θ (hA hπ) a)))
    (a : A π n) :
    ψ θ (f' (R' := R') f) (KummerReduce.ψI f (χ a)) =
      Admissible.φT (h := h₂ f h₁ he) φ₀
        (Admissible.nodeCongr hn (Node.baseMap θ (hA hπ) a)) := by
  rw [square_base f h₁ he, hχ]
  change Admissible.hatEquiv e₂ _ ((Admissible.hatEquiv e₁ h₁).symm
    (Admissible.hatEquiv e₁ h₁ _)) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- **Lifted idempotents at consecutive levels are compatible** (base form). -/
theorem eq_idem_base [IsNoetherianRing R'] {m : ℕ} (hJ : J θ (R := R') ^ m = ⊥)
    {ε : FormalPatchLevel.Hat f} (hεi : IsIdempotentElem ε) {ε₀ : Admissible.Hat f₀}
    (hε : ψ θ f ε = Admissible.hatEquiv e₁ h₁ ε₀) {ε' : FormalPatchLevel.Hat (f' (R' := R') f)}
    (hεi' : IsIdempotentElem ε')
    (hε' : ψ θ (f' (R' := R') f) ε' = Admissible.hatEquiv e₂ (h₂ f h₁ he) ε₀) :
    KummerReduce.ψI f ε = ε' := by
  refine eq_of_isNilpotent_sub_of_isIdempotentElem (hεi.map _) hεi' ?_
  refine isNilpotent_of_mem_ker_ψ θ hJ ?_
  rw [RingHom.mem_ker, map_sub, hε_base f h₁ he hε, hε', sub_self]

/-! ### The transport isomorphisms on representatives -/

omit [Algebra k (R' ⧸ J θ (R := R'))] in
lemma baseEquiv_symm_mk (ε₀ : Admissible.Hat f₀) (x : Admissible.Hat (fbar θ f)) :
    (Admissible.baseEquiv (h := h₁) ε₀).symm (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ ((Admissible.hatEquiv e₁ h₁).symm x) := by
  rw [RingEquiv.symm_apply_eq, Admissible.baseEquiv_mk, AlgEquiv.apply_symm_apply]

omit [Algebra k (R' ⧸ J θ (R := R'))] in
lemma kummerPieceEquiv_tmul (ε₀ : Admissible.Hat f₀) {n : ℕ} (hn : 0 < n)
    (s : Admissible.PieceBase φ₀ ε₀ hn) (b : B (0 : k)) :
    Admissible.kummerPieceEquiv (h := h₁) φ₀ ε₀ hn
        (s ⊗ₜ[A (0 : k) n] b : Admissible.KummerPiece φ₀ ε₀ hn) =
      (Admissible.baseEquiv (h := h₁) ε₀ s ⊗ₜ[A (0 : k) n] b :
        Admissible.KummerPiece (Admissible.φT (h := h₁) φ₀) (Admissible.hatEquiv e₁ h₁ ε₀) hn) :=
  rfl

omit [Algebra k (R' ⧸ J θ (R := R'))] in
lemma kummerPieceEquiv_symm_tmul (ε₀ : Admissible.Hat f₀) {n : ℕ} (hn : 0 < n)
    (s : Admissible.PieceBase (Admissible.φT (h := h₁) φ₀) (Admissible.hatEquiv e₁ h₁ ε₀) hn)
    (b : B (0 : k)) :
    (Admissible.kummerPieceEquiv (h := h₁) φ₀ ε₀ hn).symm
        (s ⊗ₜ[A (0 : k) n] b :
          Admissible.KummerPiece (Admissible.φT (h := h₁) φ₀) (Admissible.hatEquiv e₁ h₁ ε₀) hn) =
      ((Admissible.baseEquiv (h := h₁) ε₀).symm s ⊗ₜ[A (0 : k) n] b :
        Admissible.KummerPiece φ₀ ε₀ hn) := by
  rw [RingEquiv.symm_apply_eq, kummerPieceEquiv_tmul, RingEquiv.apply_symm_apply]

/-! ### Kummer factors -/

section Kummer

variable [IsNoetherianRing R] [IsNoetherianRing R'] (hθ : Function.Surjective θ)
  {π : O} {n : ℕ} (hn : 0 < n) (hπ : θ π = 0) (ε₀ : Admissible.Hat f₀)
  (χ : A π n →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)
  (hε : ψ θ f ε = Admissible.hatEquiv e₁ h₁ ε₀)
  (hχ : ∀ a, ψ θ f (χ a) =
    Admissible.φT (h := h₁) φ₀ (Admissible.nodeCongr hn (Node.baseMap θ (hA hπ) a)))
  (χ' : A π n →ₐ[O] FormalPatchLevel.Hat (f' (R' := R') f))
  (ε' : FormalPatchLevel.Hat (f' (R' := R') f))
  (hε' : ψ θ (f' (R' := R') f) ε' = Admissible.hatEquiv e₂ (h₂ f h₁ he) ε₀)
  (hχ' : ∀ a, ψ θ (f' (R' := R') f) (χ' a) =
    Admissible.φT (h := h₂ f h₁ he) φ₀ (Admissible.nodeCongr hn (Node.baseMap θ (hA hπ) a)))
  (hχχ : ∀ a, KummerReduce.ψI f (χ a) = χ' a) (hεε : KummerReduce.ψI f ε = ε')

omit [IsNoetherianRing R] [IsNoetherianRing R'] in
include he in
lemma σ_σI_base (s : LPiece f χ ε) :
    σ θ (f' (R' := R') f) (Admissible.φT (h := h₂ f h₁ he) φ₀) hn χ' ε'
        (Admissible.hatEquiv e₂ (h₂ f h₁ he) ε₀) hε' (KummerReduce.σI χ ε χ' ε' hχχ hεε s) =
      Admissible.baseEquiv (h := h₂ f h₁ he) ε₀ ((Admissible.baseEquiv (h := h₁) ε₀).symm
        (σ θ f (Admissible.φT (h := h₁) φ₀) hn χ ε (Admissible.hatEquiv e₁ h₁ ε₀) hε s)) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [KummerReduce.σI_mk, σ_mk, σ_mk, baseEquiv_symm_mk, Admissible.baseEquiv_mk,
    square_base f h₁ he]

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for `map_add` on the large `RingEquiv`s times out at the default limit
/-- **The reduction equivalences of a Kummer factor at consecutive levels are compatible** (base
form). -/
theorem pieceEquiv_ρ_base (x : N f χ ε) :
    pieceEquiv (f' (R' := R') f) (Admissible.φT (h := h₂ f h₁ he) φ₀) hn χ' ε'
        (Admissible.hatEquiv e₂ (h₂ f h₁ he) ε₀) hε' hθ hπ hχ'
        (Ideal.Quotient.mk _ (KummerReduce.ρ χ ε χ' ε' hχχ hεε x)) =
      Admissible.kummerPieceEquiv (h := h₂ f h₁ he) φ₀ ε₀ hn
        ((Admissible.kummerPieceEquiv (h := h₁) φ₀ ε₀ hn).symm
          (pieceEquiv f (Admissible.φT (h := h₁) φ₀) hn χ ε (Admissible.hatEquiv e₁ h₁ ε₀) hε hθ
            hπ hχ (Ideal.Quotient.mk _ x))) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s b =>
    rw [KummerReduce.ρ_tmul, pieceEquiv_mk_tmul, pieceEquiv_mk_tmul,
      σ_σI_base f h₁ he hn ε₀ χ ε hε χ' ε' hε' hχχ hεε, kummerPieceEquiv_symm_tmul,
      kummerPieceEquiv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Kummer

/-! ### Cusp factors -/

section Cusp

variable [IsNoetherianRing R] [IsNoetherianRing R'] (δ₀ : Admissible.Hat f₀)
  (δ t : FormalPatchLevel.Hat f) (hδ : ψ θ f δ = Admissible.hatEquiv e₁ h₁ δ₀)
  (ht : ψ θ f t = Admissible.ψT (h := h₁) ψ₀ X) (m : ℕ)
  (δ' t' : FormalPatchLevel.Hat (f' (R' := R') f))
  (hδ' : ψ θ (f' (R' := R') f) δ' = Admissible.hatEquiv e₂ (h₂ f h₁ he) δ₀)
  (ht' : ψ θ (f' (R' := R') f) t' = Admissible.ψT (h := h₂ f h₁ he) ψ₀ X)
  (hδδ : KummerReduce.ψI f δ = δ') (htt : KummerReduce.ψI f t = t')

omit [IsNoetherianRing R] [IsNoetherianRing R'] in
include he in
lemma σc_σb_base (y : CBase f δ) :
    σc θ (f' (R' := R') f) δ' (Admissible.hatEquiv e₂ (h₂ f h₁ he) δ₀) hδ'
        (KummerReduce.σb δ δ' hδδ y) =
      Admissible.baseEquiv (h := h₂ f h₁ he) δ₀ ((Admissible.baseEquiv (h := h₁) δ₀).symm
        (σc θ f δ (Admissible.hatEquiv e₁ h₁ δ₀) hδ y)) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [KummerReduce.σb_mk, σc_mk, σc_mk, baseEquiv_symm_mk, Admissible.baseEquiv_mk,
    square_base f h₁ he]

set_option maxHeartbeats 2000000 in
-- unifying the quotient ideals unfolds the completion isomorphism `hatEquiv`
omit [IsNoetherianRing R] [IsNoetherianRing R'] [Algebra k (R' ⧸ J θ (R := R'))] in
lemma cuspPieceEquiv_mk_base (q : (Admissible.Hat f₀ ⧸ Ideal.span {1 - δ₀})[X]) :
    Admissible.cuspPieceEquiv (h := h₁) ψ₀ δ₀ m (AdjoinRoot.mk _ q) =
      AdjoinRoot.mk _ (q.map (Admissible.baseEquiv (h := h₁) δ₀).toRingHom) := by
  rw [Admissible.cuspPieceEquiv]
  exact Ideal.quotientEquiv_mk _ _ _ _ q

set_option maxHeartbeats 2000000 in
-- unifying the quotient ideals unfolds the completion isomorphism `hatEquiv`
/-- **The reduction equivalences of a cusp factor at consecutive levels are compatible** (base
form). -/
theorem cuspEquiv_ρc_base (x : CPiece f δ t m) :
    cuspEquiv θ (f' (R' := R') f) (Admissible.ψT (h := h₂ f h₁ he) ψ₀) δ' t'
        (Admissible.hatEquiv e₂ (h₂ f h₁ he) δ₀) hδ' ht' m
        (Ideal.Quotient.mk _ (KummerReduce.ρc δ δ' hδδ t t' htt m x)) =
      Admissible.cuspPieceEquiv (h := h₂ f h₁ he) ψ₀ δ₀ m
        ((Admissible.cuspPieceEquiv (h := h₁) ψ₀ δ₀ m).symm
          (cuspEquiv θ f (Admissible.ψT (h := h₁) ψ₀) δ t (Admissible.hatEquiv e₁ h₁ δ₀) hδ ht m
            (Ideal.Quotient.mk _ x))) := by
  have hc : (σc θ (f' (R' := R') f) δ' (Admissible.hatEquiv e₂ (h₂ f h₁ he) δ₀) hδ').comp
      (KummerReduce.σb δ δ' hδδ) =
      (Admissible.baseEquiv (h := h₂ f h₁ he) δ₀).toRingHom.comp
        ((Admissible.baseEquiv (h := h₁) δ₀).symm.toRingHom.comp
          (σc θ f δ (Admissible.hatEquiv e₁ h₁ δ₀) hδ)) :=
    RingHom.ext fun y ↦ σc_σb_base f h₁ he δ₀ δ hδ δ' hδ' hδδ y
  have hid : (Admissible.baseEquiv (h := h₁) δ₀).toRingHom.comp
      ((Admissible.baseEquiv (h := h₁) δ₀).symm.toRingHom.comp
        (σc θ f δ (Admissible.hatEquiv e₁ h₁ δ₀) hδ)) =
      σc θ f δ (Admissible.hatEquiv e₁ h₁ δ₀) hδ :=
    RingHom.ext fun y ↦ (Admissible.baseEquiv (h := h₁) δ₀).apply_symm_apply _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have h1 := KummerReduce.ρc_mk δ δ' hδδ t t' htt m p
  have h2 := cuspEquiv_mk_mk f δ t (Admissible.hatEquiv e₁ h₁ δ₀) hδ ht m p
  have h3 := cuspEquiv_mk_mk (f' (R' := R') f) δ' t' (Admissible.hatEquiv e₂ (h₂ f h₁ he) δ₀)
    hδ' ht' m (p.map (KummerReduce.σb δ δ' hδδ))
  set w := p.map ((Admissible.baseEquiv (h := h₁) δ₀).symm.toRingHom.comp
    (σc θ f δ (Admissible.hatEquiv e₁ h₁ δ₀) hδ))
  have h4 : (Admissible.cuspPieceEquiv (h := h₁) ψ₀ δ₀ m).symm
      (AdjoinRoot.mk _ (p.map (σc θ f δ (Admissible.hatEquiv e₁ h₁ δ₀) hδ))) =
      AdjoinRoot.mk _ w := by
    rw [RingEquiv.symm_apply_eq, cuspPieceEquiv_mk_base f h₁ δ₀ m w, Polynomial.map_map, hid]
  refine (congrArg (fun z ↦ cuspEquiv θ (f' (R' := R') f) (Admissible.ψT (h := h₂ f h₁ he) ψ₀)
    δ' t' (Admissible.hatEquiv e₂ (h₂ f h₁ he) δ₀) hδ' ht' m (Ideal.Quotient.mk _ z)) h1).trans ?_
  refine h3.trans ?_
  rw [h2, h4, cuspPieceEquiv_mk_base (f' (R' := R') f) (h₂ f h₁ he) δ₀ m w, Polynomial.map_map,
    Polynomial.map_map, hc]

end Cusp

end

end LevelStep

end SemistableReduction
