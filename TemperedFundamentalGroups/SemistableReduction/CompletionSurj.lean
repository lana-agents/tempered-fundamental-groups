/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CompletionMap
import TemperedFundamentalGroups.SemistableReduction.CompletionQuot

/-!
# Completion along a surjection (Blueprint §12.8, M2.3 (e'))

The levels of the formal patching live over the charts `R_n` of the model modulo `ϖⁿ`, related by
surjections `R_{n+1} → R_n` (not by literal quotient maps). For a surjective ring map
`q : R → R'` (an `R`-algebra `R'` with surjective structure map) and `f ∈ R`, the completion map
`CompletionSurj.ψ : R^∧_f → R'^∧_{q f}` (`CompletionMap.map q`) is

* **surjective** (`surjective_ψ`) and
* has kernel `(ker q) R̂` (**`ker_ψ`**, for `R` Noetherian),

by comparison with the quotient case `CompletionQuot.ψ` (Stacks, Tag 00MA = Lemma 10.97.1 (2), (3))
through the isomorphism `R/ker q ≅ R'` and the induced isomorphism of completions
(`CompletionMap.equiv`).
-/

universe u

namespace SemistableReduction

namespace CompletionSurj

noncomputable section

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R'] (f : R)

/-- The image `q f` of `f` in `R'`. -/
abbrev fq : R' := algebraMap R R' f

/-- The completion `R'^∧` of `R'` along `q f`. -/
abbrev H' : Type u := AdicCompletion (Ideal.span {fq (R' := R') f}) R'

lemma map_le : (Ideal.span {f}).map (algebraMap R R') ≤ Ideal.span {fq (R' := R') f} := by
  rw [Ideal.map_span, Set.image_singleton]

/-- **The completion map** `ψ : R̂ → R'^∧` along `q : R → R'`. -/
def ψ : AdicCompletion (Ideal.span {f}) R →ₐ[R] H' (R' := R') f :=
  { CompletionMap.map (algebraMap R R') (map_le f) with
    commutes' := fun r ↦ by
      change CompletionMap.map _ _ (algebraMap R _ r) = _
      rw [CompletionMap.map_algebraMap, ← IsScalarTower.algebraMap_apply] }

lemma ψ_apply (x : AdicCompletion (Ideal.span {f}) R) :
    ψ (R' := R') f x = CompletionMap.map (algebraMap R R') (map_le f) x := rfl

lemma evalₐ_ψ (n : ℕ) (x : AdicCompletion (Ideal.span {f}) R) :
    AdicCompletion.evalₐ _ n (ψ (R' := R') f x) =
      Ideal.quotientMap _ (algebraMap R R') (CompletionMap.le_comap _ (map_le f) n)
        (AdicCompletion.evalₐ _ n x) :=
  CompletionMap.evalₐ_map ..

lemma ψ_algebraMap (r : R) :
    ψ (R' := R') f (algebraMap R _ r) = algebraMap R' (H' (R' := R') f) (algebraMap R R' r) :=
  CompletionMap.map_algebraMap ..

/-! ### Comparison with the quotient case -/

variable {f}

/-- The kernel `K = ker q`. -/
abbrev K : Ideal R := RingHom.ker (algebraMap R R')

variable (hq : Function.Surjective (algebraMap R R'))

/-- `R/ker q ≅ R'`. -/
abbrev qe : (R ⧸ K (R' := R')) ≃+* R' := RingHom.quotientKerEquivOfSurjective hq

lemma map_span_mk : (Ideal.span {f}).map (Ideal.Quotient.mk (K (R' := R'))) =
    Ideal.span {Ideal.Quotient.mk (K (R' := R')) f} := by
  rw [Ideal.map_span, Set.image_singleton]

lemma map_span_eq : (Ideal.span {Ideal.Quotient.mk (K (R' := R')) f}).map
    ((qe hq : R ⧸ K (R' := R') ≃+* R') : R ⧸ K (R' := R') →+* R') =
      Ideal.span {fq (R' := R') f} := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

omit [Algebra R R'] in
/-- The quotient completion map `CompletionQuot.ψ` is the completion map of the quotient map. -/
lemma quot_eq_map (I J : Ideal R) (I' : Ideal (R ⧸ J)) (hI : I.map (Ideal.Quotient.mk J) = I')
    (x : AdicCompletion I R) :
    CompletionQuot.ψ I J I' hI x = CompletionMap.map (Ideal.Quotient.mk J) hI.le x := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [CompletionQuot.ψ, AdicCompletion.evalₐ_liftAlgHom, CompletionMap.evalₐ_map]
  rfl

omit [Algebra R R'] in
lemma map_congr {I₁ : Ideal R} {I₂ : Ideal R'} {g g' : R →+* R'} (hg : g = g')
    (h : I₁.map g ≤ I₂) (h' : I₁.map g' ≤ I₂) (x : AdicCompletion I₁ R) :
    CompletionMap.map g h x = CompletionMap.map g' h' x := by
  subst hg
  rfl

/-- `ψ` factors as the quotient completion map followed by an isomorphism of completions. -/
lemma ψ_eq (x : AdicCompletion (Ideal.span {f}) R) :
    ψ (R' := R') f x = CompletionMap.equiv (qe hq) (map_span_eq hq)
      (CompletionQuot.ψ (Ideal.span {f}) (K (R' := R')) _ map_span_mk x) := by
  rw [quot_eq_map, CompletionMap.equiv_apply, CompletionMap.map_comp, ψ_apply]
  refine map_congr ?_ _ _ x
  ext r
  rfl

include hq in
/-- **The completion map along a surjection is surjective.** -/
theorem surjective_ψ : Function.Surjective (ψ (R' := R') f) := by
  intro y
  obtain ⟨x, hx⟩ := CompletionQuot.surjective_ψ (Ideal.span {f}) (K (R' := R')) _ map_span_mk
    ((CompletionMap.equiv (qe hq) (map_span_eq hq)).symm y)
  exact ⟨x, by rw [ψ_eq hq, hx, RingEquiv.apply_symm_apply]⟩

include hq in
/-- **The kernel of the completion map along a surjection `q` is `(ker q) R̂`.** -/
theorem ker_ψ [IsNoetherianRing R] :
    RingHom.ker (ψ (R' := R') f) =
      (K (R' := R')).map (algebraMap R (AdicCompletion (Ideal.span {f}) R)) := by
  ext x
  rw [RingHom.mem_ker, ψ_eq hq, map_eq_zero_iff _ (RingEquiv.injective _), ← RingHom.mem_ker,
    CompletionQuot.ker_ψ]

end

end CompletionSurj

end SemistableReduction
