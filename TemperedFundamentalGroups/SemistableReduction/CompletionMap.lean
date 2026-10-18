/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Functoriality of adic completions of rings (Blueprint §12.8, M2.3, levels)

For a ring map `g : R₁ → R₂` with `g(I₁) ⊆ I₂`, the induced map of adic completions
`CompletionMap.map g h : R₁^∧_{I₁} → R₂^∧_{I₂}` (levelwise `R₁/I₁ⁿ → R₂/I₂ⁿ`, assembled by
Mathlib's `AdicCompletion.liftRingHom`), with `map_algebraMap`, `map_comp`, `map_id`, and for a
ring isomorphism `e` with `e(I₁) = I₂` the ring isomorphism **`CompletionMap.equiv e h`** of the
completions.

Use: the special fibres `R_n/J_n` of the level-`n` charts are different (isomorphic) rings; to
compare the level-`n` patchings of one admissible covering of the special fibre
(`Admissible.Covering`, whose Kummer factors live over the completion `(R/J)^∧`), the covering is
transported along these isomorphisms, which needs the induced isomorphisms of completions.
-/

universe u v w

namespace SemistableReduction

namespace CompletionMap

noncomputable section

variable {R₁ : Type u} [CommRing R₁] {R₂ : Type v} [CommRing R₂] {R₃ : Type w} [CommRing R₃]
  {I₁ : Ideal R₁} {I₂ : Ideal R₂} {I₃ : Ideal R₃}

lemma le_comap (g : R₁ →+* R₂) (h : I₁.map g ≤ I₂) (n : ℕ) : I₁ ^ n ≤ (I₂ ^ n).comap g := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono h n

/-- Level `n` of the completion map: `R₁^∧ → R₁/I₁ⁿ → R₂/I₂ⁿ`. -/
def lev (g : R₁ →+* R₂) (h : I₁.map g ≤ I₂) (n : ℕ) : AdicCompletion I₁ R₁ →+* R₂ ⧸ I₂ ^ n :=
  (Ideal.quotientMap (I₂ ^ n) g (le_comap g h n)).comp (AdicCompletion.evalₐ I₁ n).toRingHom

lemma lev_compat (g : R₁ →+* R₂) (h : I₁.map g ≤ I₂) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I₂ hle).comp (lev g h n) = lev g h m := by
  ext x
  induction x using AdicCompletion.induction_on with
  | h a =>
    simp only [RingHom.comp_apply, lev, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
    have ha := AdicCompletion.AdicCauchySequence.mk_eq_mk hle a
    rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at ha
    exact le_comap g h m (by simpa using ha)

/-- **The completion map** `R₁^∧_{I₁} → R₂^∧_{I₂}` induced by `g`. -/
def map (g : R₁ →+* R₂) (h : I₁.map g ≤ I₂) : AdicCompletion I₁ R₁ →+* AdicCompletion I₂ R₂ :=
  AdicCompletion.liftRingHom I₂ (lev g h) (lev_compat g h)

lemma evalₐ_map (g : R₁ →+* R₂) (h : I₁.map g ≤ I₂) (n : ℕ) (x : AdicCompletion I₁ R₁) :
    AdicCompletion.evalₐ I₂ n (map g h x) =
      Ideal.quotientMap (I₂ ^ n) g (le_comap g h n) (AdicCompletion.evalₐ I₁ n x) :=
  AdicCompletion.evalₐ_liftRingHom ..

lemma map_algebraMap (g : R₁ →+* R₂) (h : I₁.map g ≤ I₂) (r : R₁) :
    map g h (algebraMap R₁ (AdicCompletion I₁ R₁) r) = algebraMap R₂ _ (g r) := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_map, AlgHom.commutes, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk]

lemma map_comp (g : R₁ →+* R₂) (h : I₁.map g ≤ I₂) (g' : R₂ →+* R₃) (h' : I₂.map g' ≤ I₃)
    (x : AdicCompletion I₁ R₁) :
    map g' h' (map g h x) =
      map (g'.comp g) (by rw [← Ideal.map_map]; exact (Ideal.map_mono h).trans h') x := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_map, evalₐ_map, evalₐ_map]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I₁ n x)
  rw [← hr, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, RingHom.comp_apply]

lemma map_eq_self (g : R₁ →+* R₁) (hg : ∀ r, g r = r) (h : I₁.map g ≤ I₁)
    (x : AdicCompletion I₁ R₁) : map g h x = x := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_map]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I₁ n x)
  rw [← hr, Ideal.quotientMap_mk, hg]

/-- **The isomorphism of completions** induced by a ring isomorphism `e` with `e(I₁) = I₂`. -/
def equiv (e : R₁ ≃+* R₂) (h : I₁.map (e : R₁ →+* R₂) = I₂) :
    AdicCompletion I₁ R₁ ≃+* AdicCompletion I₂ R₂ where
  __ := map (e : R₁ →+* R₂) h.le
  invFun := map (e.symm : R₂ →+* R₁) (by
    rw [← h, Ideal.map_map, RingEquiv.symm_comp, Ideal.map_id])
  left_inv x := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [map_comp]
    exact map_eq_self _ (fun r ↦ e.symm_apply_apply r) _ x
  right_inv x := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [map_comp]
    exact map_eq_self _ (fun r ↦ e.apply_symm_apply r) _ x

lemma equiv_apply (e : R₁ ≃+* R₂) (h : I₁.map (e : R₁ →+* R₂) = I₂) (x : AdicCompletion I₁ R₁) :
    equiv e h x = map (e : R₁ →+* R₂) h.le x := rfl

lemma equiv_algebraMap (e : R₁ ≃+* R₂) (h : I₁.map (e : R₁ →+* R₂) = I₂) (r : R₁) :
    equiv e h (algebraMap R₁ _ r) = algebraMap R₂ _ (e r) :=
  map_algebraMap _ _ r

end

end CompletionMap

end SemistableReduction
