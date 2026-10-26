/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerAssemble

/-!
# Assembling the formal cusp form along `V(f)` (MR12 T2 S5.5, assembly)

Let `R` be a Noetherian `k`-algebra (the special fibre of a chart), `f ∈ R` whose zero set `V(f)`
consists of finitely many maximal ideals `𝔪ⱼ` (the marked points), `ψ : k[X] → R̂` the formal
coordinate at the marked points with `ψ X = s` (`s ∈ R`), and `C` an `R`-algebra. Suppose that
at every marked point `R̂_{𝔪ⱼ} ⊗_R C ≅ ∏ᵢ R̂_{𝔪ⱼ}[t']/(t'^{dⱼᵢ} − s)`. Then
(**`FormalKummer.assembleCuspEquiv`**)

  `R̂ ⊗_R C ≅ ∏_{(j, i)} (R̂/(1 − εⱼ))[t']/(t'^{dⱼᵢ} − ψ X)`

as `R̂`-algebras (`εⱼ` the idempotents of the points, `CompletionProd.idem`): the right side is
`∏ Admissible.CuspPiece ψ εⱼ dⱼᵢ`, the cusp part of the formally Kummer condition of an admissible
covering. The proof is that of `FormalKummer.assembleEquiv`, with the cusp factors
`AdjoinRoot (X ^ e - C a)` transported along `R̂/(1 − εⱼ) ≅ R̂_{𝔪ⱼ}` (`adjoinPowEquiv`).
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

namespace FormalKummer

noncomputable section

/-- A ring isomorphism `S ≅ S'` with `a ↦ b` induces `S[t]/(tⁿ − a) ≅ S'[t]/(tⁿ − b)`. -/
def adjoinPowEquiv {S S' : Type*} [CommRing S] [CommRing S'] (e : S ≃+* S') (n : ℕ) {a : S}
    {b : S'} (hab : e a = b) : AdjoinRoot (X ^ n - C a) ≃+* AdjoinRoot (X ^ n - C b) :=
  Ideal.quotientEquiv _ _ (Polynomial.mapEquiv e) (by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    change _ = {Polynomial.map (e : S →+* S') (X ^ n - C a)}
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    simp [hab])

lemma adjoinPowEquiv_of {S S' : Type*} [CommRing S] [CommRing S'] (e : S ≃+* S') (n : ℕ) {a : S}
    {b : S'} (hab : e a = b) (x : S) :
    adjoinPowEquiv e n hab (AdjoinRoot.of _ x) = AdjoinRoot.of _ (e x) := by
  change Ideal.quotientEquiv _ _ _ _ (Ideal.Quotient.mk _ (C x)) = Ideal.Quotient.mk _ (C (e x))
  rw [Ideal.quotientEquiv_mk]
  change Ideal.Quotient.mk _ (Polynomial.map (e : S →+* S') (C x)) = _
  rw [Polynomial.map_C]
  rfl

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
  {f : R} {ι : Type} [Finite ι] [DecidableEq ι] {𝔪 : ι → Ideal R} [∀ j, (𝔪 j).IsMaximal]
  (hinj : Function.Injective 𝔪) (hf : ∀ j, f ∈ 𝔪 j)
  (hrad : ⨅ j, 𝔪 j ≤ (Ideal.span {f}).radical)
  (ψ : Polynomial k →ₐ[k] Admissible.Hat f) {s : R} (hψ : ψ X = algebraMap R _ s)

variable (𝔪 s) in
/-- The local cusp factor `R̂_{𝔪ⱼ}[t']/(t'^e − s)`. -/
abbrev CuspLoc (j : ι) (e : ℕ) : Type u :=
  AdjoinRoot (X ^ e - C (algebraMap R (T 𝔪 j) s))

include hψ in
lemma quotEquiv_ψ (j : ι) :
    CompletionProd.quotEquiv hinj hf hrad j (Ideal.Quotient.mk _ (ψ X)) =
      algebraMap R (T 𝔪 j) s := by
  rw [hψ, Ideal.Quotient.mk_algebraMap, CompletionProd.quotEquiv_algebraMap]

/-- `R̂/(1 − εⱼ)[t']/(t'^e − ψ X) ≅ R̂_{𝔪ⱼ}[t']/(t'^e − s)`. -/
def cuspPieceEquiv (j : ι) (e : ℕ) :
    Admissible.CuspPiece ψ (CompletionProd.idem hinj hf hrad j) e ≃+* CuspLoc 𝔪 s j e :=
  adjoinPowEquiv (CompletionProd.quotEquiv hinj hf hrad j) e (quotEquiv_ψ hinj hf hrad ψ hψ j)

variable {C : Type u} [CommRing C] [Algebra R C] {r : ι → ℕ} {d : ∀ j, Fin (r j) → ℕ}

/-- **The formal cusp form along `V(f)`**, assembled from the formal cusp forms at the points. -/
def assembleCuspEquiv [Fintype ι]
    (Ψ : ∀ j, T 𝔪 j ⊗[R] C ≃ₐ[T 𝔪 j] ∀ i : Fin (r j), CuspLoc 𝔪 s j (d j i)) :
    Admissible.Hat f ⊗[R] C ≃ₐ[Admissible.Hat f]
      ∀ p : (Σ j, Fin (r j)), Admissible.CuspPiece ψ (CompletionProd.idem hinj hf hrad p.1)
        (d p.1 p.2) :=
  AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.congr (hatEquiv hinj hf hrad) AlgEquiv.refl).trans
      piLeftEquiv).toRingEquiv.trans
      ((RingEquiv.piCongrRight fun j ↦ (Ψ j).toRingEquiv).trans
        ((RingEquiv.piCongrRight fun j ↦ RingEquiv.piCongrRight fun i ↦
          (cuspPieceEquiv hinj hf hrad ψ hψ j (d j i)).symm).trans
          (piCurryRingEquiv _)))) (by
    intro h
    funext p
    obtain ⟨j, i⟩ := p
    have h1 : (Ψ j) (hatEquiv hinj hf hrad h j ⊗ₜ (1 : C)) =
        algebraMap (T 𝔪 j) _ (hatEquiv hinj hf hrad h j) := by
      rw [← (Ψ j).commutes]
      rfl
    have h2 : CompletionProd.quotEquiv hinj hf hrad j (Ideal.Quotient.mk _ h) =
        hatEquiv hinj hf hrad h j := by
      rw [CompletionProd.quotEquiv_mk]
      rfl
    change (cuspPieceEquiv hinj hf hrad ψ hψ j (d j i)).symm
      ((Ψ j) (hatEquiv hinj hf hrad h j ⊗ₜ (1 : C)) i) = _
    rw [h1]
    refine (RingEquiv.symm_apply_eq _).mpr ?_
    change AdjoinRoot.of _ (hatEquiv hinj hf hrad h j) = adjoinPowEquiv _ _ _
      (AdjoinRoot.of _ (Ideal.Quotient.mk _ h))
    rw [adjoinPowEquiv_of, h2])

end

end FormalKummer

end SemistableReduction
