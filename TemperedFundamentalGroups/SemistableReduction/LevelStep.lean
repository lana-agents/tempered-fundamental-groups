/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerReduce
import TemperedFundamentalGroups.SemistableReduction.CoveringTransport

/-!
# Special fibres of consecutive levels (Blueprint §12.8, M2.3 (e'))

Setting: a chart `R` over `O` (level `n + 1`), an `R`-algebra `R'` over `O` (level `n`) with
surjective structure map `q`, `f ∈ R`, `θ : O → k`, the special fibres `R/J` and `R'/J'`
(`J = (ker θ) R`, `J' = (ker θ) R'`) and a `k`-algebra isomorphism `e : R/J ≃ R'/J'` induced by `q`
(`he : e (r mod J) = q r mod J'`). An admissible covering `cov` of the special fibre of `R` is
transported to `R'` (`Admissible.Covering.transport`, along `e`, with `e f̄ = q f mod J'`).

* **`LevelStep.square`**: the completion maps commute,
  `ψ_{R'} ∘ ψ_q = Ê ∘ ψ_R : R̂ → (R'/J')^∧` (all are `CompletionMap.map` of the same composite
  `R → R'/J'`);
* consequently the reduction `ψ_q ∘ χ`, `ψ_q ε̃` of level-`(n+1)` lift data satisfies the lift
  conditions for the transported covering (`hε_reduce`, `hχ_reduce`), and lifted idempotents at
  the two levels are automatically compatible (`eq_idem`: idempotents congruent modulo a nilpotent
  ideal are equal, Stacks 00J9 via Mathlib `eq_of_isNilpotent_sub_of_isIdempotentElem`);
* **`LevelStep.pieceEquiv_ρ`**, **`LevelStep.cuspEquiv_ρc`**: the reduction equivalences of the
  Kummer and cusp factors (`AdmissibleLift.pieceEquiv`, `AdmissibleLift.cuspEquiv`) at the two
  levels are compatible with the reductions `KummerReduce.ρ`, `KummerReduce.ρc` and the transport
  isomorphisms `Admissible.kummerPieceEquiv`, `Admissible.cuspPieceEquiv`.
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
  {e : (R ⧸ J θ (R := R)) ≃ₐ[k] (R' ⧸ J θ (R := R'))}
  (he : ∀ r : R, e (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R R' r))

/-- The image of `f` in `R'`. -/
abbrev f' : R' := KummerReduce.f' (R' := R') f

/-! ### The completion square -/

include he in
/-- **The completion maps of consecutive levels commute with the special-fibre isomorphism.** -/
theorem square (x : FormalPatchLevel.Hat f) :
    ψ θ (f' (R' := R') f) (KummerReduce.ψI f x) = Admissible.hatEquiv e (he f) (ψ θ f x) := by
  have h1 : ψ θ (f' (R' := R') f) (KummerReduce.ψI f x) =
      CompletionMap.map (Ideal.Quotient.mk (J θ (R := R'))) (map_span_f θ (f' (R' := R') f)).le
        (CompletionMap.map (algebraMap R R') (CompletionSurj.map_le f) x) :=
    CompletionSurj.quot_eq_map _ _ _ _ _
  have h2 : Admissible.hatEquiv e (he f) (ψ θ f x) =
      CompletionMap.map (e.toRingEquiv : (R ⧸ J θ (R := R)) →+* (R' ⧸ J θ (R := R')))
        (Admissible.map_span_e e (he f)).le
        (CompletionMap.map (Ideal.Quotient.mk (J θ (R := R))) (map_span_f θ f).le x) := by
    rw [← CompletionSurj.quot_eq_map]
    rfl
  rw [h1, h2, CompletionMap.map_comp, CompletionMap.map_comp]
  refine CompletionSurj.map_congr ?_ _ _ x
  ext r
  exact (he r).symm

/-! ### Lift data at consecutive levels -/

variable {φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}

include he in
/-- The reduction of a lifted idempotent lifts the transported idempotent. -/
lemma hε_reduce {ε : FormalPatchLevel.Hat f} {εb : Admissible.Hat (fbar θ f)}
    (hε : ψ θ f ε = εb) :
    ψ θ (f' (R' := R') f) (KummerReduce.ψI f ε) = Admissible.hatEquiv e (he f) εb := by
  rw [square f he, hε]

include he in
/-- The reduction of lifted node coordinates lifts the transported node coordinates. -/
lemma hχ_reduce {π : O} {n : ℕ} (hn : 0 < n) (hπ : θ π = 0)
    {χ : A π n →ₐ[O] FormalPatchLevel.Hat f}
    (hχ : ∀ a, ψ θ f (χ a) = φ (Admissible.nodeCongr hn (Node.baseMap θ (hA hπ) a))) (a : A π n) :
    ψ θ (f' (R' := R') f) (KummerReduce.ψI f (χ a)) =
      Admissible.φT (h := he f) φ (Admissible.nodeCongr hn (Node.baseMap θ (hA hπ) a)) := by
  rw [square f he, hχ]
  rfl

/-- **Lifted idempotents at consecutive levels are compatible**: an idempotent of `R'^∧` lifting
the transported idempotent is the reduction of any idempotent of `R̂` lifting the original one
(`J' R'^∧` is nilpotent). -/
theorem eq_idem [IsNoetherianRing R'] {m : ℕ} (hJ : J θ (R := R') ^ m = ⊥)
    {ε : FormalPatchLevel.Hat f} (hεi : IsIdempotentElem ε) {εb : Admissible.Hat (fbar θ f)}
    (hε : ψ θ f ε = εb) {ε' : FormalPatchLevel.Hat (f' (R' := R') f)}
    (hεi' : IsIdempotentElem ε')
    (hε' : ψ θ (f' (R' := R') f) ε' = Admissible.hatEquiv e (he f) εb) :
    KummerReduce.ψI f ε = ε' := by
  refine eq_of_isNilpotent_sub_of_isIdempotentElem (hεi.map _) hεi' ?_
  refine isNilpotent_of_mem_ker_ψ θ hJ ?_
  rw [RingHom.mem_ker, map_sub, hε_reduce f he hε, hε', sub_self]

/-! ### Compatibility of the reduction equivalences -/

section Kummer

variable [IsNoetherianRing R] [IsNoetherianRing R'] (hθ : Function.Surjective θ)
  {π : O} {n : ℕ} (hn : 0 < n) (hπ : θ π = 0)
  (χ : A π n →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)
  (εb : Admissible.Hat (fbar θ f)) (hε : ψ θ f ε = εb)
  (hχ : ∀ a, ψ θ f (χ a) = φ (Admissible.nodeCongr hn (Node.baseMap θ (hA hπ) a)))
  (χ' : A π n →ₐ[O] FormalPatchLevel.Hat (f' (R' := R') f))
  (ε' : FormalPatchLevel.Hat (f' (R' := R') f))
  (hε' : ψ θ (f' (R' := R') f) ε' = Admissible.hatEquiv e (he f) εb)
  (hχ' : ∀ a, ψ θ (f' (R' := R') f) (χ' a) =
    Admissible.φT (h := he f) φ (Admissible.nodeCongr hn (Node.baseMap θ (hA hπ) a)))
  (hχχ : ∀ a, KummerReduce.ψI f (χ a) = χ' a) (hεε : KummerReduce.ψI f ε = ε')

omit [IsNoetherianRing R] [IsNoetherianRing R'] in
include he in
lemma σ_σI (s : LPiece f χ ε) :
    σ θ (f' (R' := R') f) (Admissible.φT (h := he f) φ) hn χ' ε'
        (Admissible.hatEquiv e (he f) εb) hε' (KummerReduce.σI χ ε χ' ε' hχχ hεε s) =
      Admissible.baseEquiv (h := he f) εb (σ θ f φ hn χ ε εb hε s) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [KummerReduce.σI_mk, σ_mk, σ_mk, Admissible.baseEquiv_mk, square f he]

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for `map_add` on the large `RingEquiv`s times out at the default limit
/-- **The reduction equivalences of a Kummer factor at consecutive levels are compatible.** -/
theorem pieceEquiv_ρ (x : N f χ ε) :
    pieceEquiv (f' (R' := R') f) (Admissible.φT (h := he f) φ) hn χ' ε'
        (Admissible.hatEquiv e (he f) εb) hε' hθ hπ hχ'
        (Ideal.Quotient.mk _ (KummerReduce.ρ χ ε χ' ε' hχχ hεε x)) =
      Admissible.kummerPieceEquiv (h := he f) φ εb hn
        (pieceEquiv f φ hn χ ε εb hε hθ hπ hχ (Ideal.Quotient.mk _ x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s b =>
    rw [KummerReduce.ρ_tmul, pieceEquiv_mk_tmul, pieceEquiv_mk_tmul, σ_σI f he]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Kummer

section Cusp

variable [IsNoetherianRing R] [IsNoetherianRing R']
  (δ t : FormalPatchLevel.Hat f) (δb : Admissible.Hat (fbar θ f)) (hδ : ψ θ f δ = δb)
  (ht : ψ θ f t = ψc X) (m : ℕ)
  (δ' t' : FormalPatchLevel.Hat (f' (R' := R') f))
  (hδ' : ψ θ (f' (R' := R') f) δ' = Admissible.hatEquiv e (he f) δb)
  (ht' : ψ θ (f' (R' := R') f) t' = Admissible.ψT (h := he f) ψc X)
  (hδδ : KummerReduce.ψI f δ = δ') (htt : KummerReduce.ψI f t = t')

/-- `cuspEquiv` on representatives: reduce the coefficients. -/
lemma cuspEquiv_mk_mk (p : (CBase f δ)[X]) :
    cuspEquiv θ f ψc δ t δb hδ ht m (Ideal.Quotient.mk _ (AdjoinRoot.mk _ p)) =
      AdjoinRoot.mk _ (p.map (σc θ f δ δb hδ)) := by
  rw [cuspEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    AlgEquiv.coe_ringEquiv, AdjoinRoot.quotEquivQuotMap_apply_mk]
  erw [Ideal.quotientEquiv_mk]
  rw [Polynomial.mapEquiv_apply, Polynomial.map_map]
  congr 2

omit [IsNoetherianRing R] [IsNoetherianRing R'] in
include he in
lemma σc_σb (y : CBase f δ) :
    σc θ (f' (R' := R') f) δ' (Admissible.hatEquiv e (he f) δb) hδ'
        (KummerReduce.σb δ δ' hδδ y) =
      Admissible.baseEquiv (h := he f) δb (σc θ f δ δb hδ y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [KummerReduce.σb_mk, σc_mk, σc_mk, Admissible.baseEquiv_mk, square f he]

set_option maxHeartbeats 2000000 in
-- unifying the quotient ideals unfolds the completion isomorphism `hatEquiv`
omit [IsNoetherianRing R] [IsNoetherianRing R'] in
lemma cuspPieceEquiv_mk (q : (Admissible.Hat (fbar θ f) ⧸ Ideal.span {1 - δb})[X]) :
    Admissible.cuspPieceEquiv (h := he f) ψc δb m (AdjoinRoot.mk _ q) =
      AdjoinRoot.mk _ (q.map ((Admissible.baseEquiv (h := he f) δb : _ ≃+* _) : _ →+* _)) := by
  rw [Admissible.cuspPieceEquiv]
  exact Ideal.quotientEquiv_mk _ _ _ _ q

set_option maxHeartbeats 2000000 in
-- unifying the quotient ideals unfolds the completion isomorphism `hatEquiv`
/-- **The reduction equivalences of a cusp factor at consecutive levels are compatible.** -/
theorem cuspEquiv_ρc (x : CPiece f δ t m) :
    cuspEquiv θ (f' (R' := R') f) (Admissible.ψT (h := he f) ψc) δ' t'
        (Admissible.hatEquiv e (he f) δb) hδ' ht' m
        (Ideal.Quotient.mk _ (KummerReduce.ρc δ δ' hδδ t t' htt m x)) =
      Admissible.cuspPieceEquiv (h := he f) ψc δb m
        (cuspEquiv θ f ψc δ t δb hδ ht m (Ideal.Quotient.mk _ x)) := by
  have hc : (σc θ (f' (R' := R') f) δ' (Admissible.hatEquiv e (he f) δb) hδ').comp
      (KummerReduce.σb δ δ' hδδ) =
      ((Admissible.baseEquiv (h := he f) δb : _ ≃+* _) : _ →+* _).comp (σc θ f δ δb hδ) :=
    RingHom.ext fun y ↦ σc_σb f he δ δb hδ δ' hδ' hδδ y
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have h1 := KummerReduce.ρc_mk δ δ' hδδ t t' htt m p
  have h2 := cuspEquiv_mk_mk f δ t δb hδ ht m p
  have h3 := cuspEquiv_mk_mk (f' (R' := R') f) δ' t' (Admissible.hatEquiv e (he f) δb) hδ' ht' m
    (p.map (KummerReduce.σb δ δ' hδδ))
  have h4 : (p.map (KummerReduce.σb δ δ' hδδ)).map
      (σc θ (f' (R' := R') f) δ' (Admissible.hatEquiv e (he f) δb) hδ') =
      (p.map (σc θ f δ δb hδ)).map ((Admissible.baseEquiv (h := he f) δb : _ ≃+* _) : _ →+* _) := by
    rw [Polynomial.map_map, Polynomial.map_map, hc]
  refine (congrArg (fun z ↦ cuspEquiv θ (f' (R' := R') f) (Admissible.ψT (h := he f) ψc) δ' t'
    (Admissible.hatEquiv e (he f) δb) hδ' ht' m (Ideal.Quotient.mk _ z)) h1).trans ?_
  refine h3.trans ?_
  rw [h4, h2, cuspPieceEquiv_mk]

end Cusp

end

end LevelStep

end SemistableReduction
