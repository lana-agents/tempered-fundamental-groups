/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# Completion commutes with quotients (Blueprint §12.8, M2.3 (d'), step κ1)

For a Noetherian ring `R`, ideals `I, J ⊆ R` and `I' = I·(R/J)`, the completion map
`ψ : R̂ = R^∧_I → (R/J)^∧_{I'}` (`CompletionQuot.ψ`, induced levelwise by `R/Iⁿ → (R/J)/I'ⁿ`) is

* **surjective** (`CompletionQuot.surjective_ψ`), and
* has kernel `J R̂` (**`CompletionQuot.ker_ψ`**),

so `R̂/JR̂ ≅ (R/J)^∧` (Stacks, Tag 00MA = Lemma 10.97.1 (2), (3): for `R` Noetherian, `I`-adic
completion is exact on finite modules and `M^∧ = M ⊗_R R^∧`). Proof: `ψ` is, up to the
levelwise identification of `I^n·(R/J)` (as an `R`-submodule) with `I'^n·(R/J)` (as an
`R/J`-submodule) (`CompletionQuot.e`),
the map `AdicCompletion.map I (R → R/J)`; Mathlib's `AdicCompletion.map_surjective`,
`AdicCompletion.map_exact` (applied to `J → R → R/J`) and `AdicCompletion.ofTensorProduct` (the
image of `J^∧ = R̂ ⊗_R J` in `R̂` is `JR̂`) give the claims.

These are the hypotheses of `TensorQuotBase.equiv` with `S = R̂`, `S' = (R/J)^∧`.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace CompletionQuot

noncomputable section

variable {R : Type u} [CommRing R] (I J : Ideal R) (I' : Ideal (R ⧸ J))
  (hI : I.map (Ideal.Quotient.mk J) = I')

include hI in
lemma pow_smul_eq (n : ℕ) : (I ^ n • ⊤ : Submodule R (R ⧸ J)) =
    (I' ^ n • (⊤ : Submodule (R ⧸ J) (R ⧸ J))).restrictScalars R := by
  rw [← hI, ← Ideal.map_pow, ← Ideal.Quotient.algebraMap_eq, Submodule.restrictScalars_map_smul_eq,
    Submodule.restrictScalars_top]

/-- The levelwise identification `(R/J)/(Iⁿ·(R/J)) ≃ (R/J)/(I'ⁿ·(R/J))`. -/
def t (n : ℕ) : ((R ⧸ J) ⧸ (I ^ n • ⊤ : Submodule R (R ⧸ J))) ≃
    ((R ⧸ J) ⧸ (I' ^ n • (⊤ : Submodule (R ⧸ J) (R ⧸ J)))) :=
  ((Submodule.quotEquivOfEq _ _ (pow_smul_eq I J I' hI n)).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)).toEquiv

lemma t_mk (n : ℕ) (x : R ⧸ J) :
    t I J I' hI n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

lemma t_symm_mk (n : ℕ) (x : R ⧸ J) :
    (t I J I' hI n).symm (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

/-- The completion of `R/J` as an `R`-module is the completion of `R/J` as a ring. -/
def e : AdicCompletion I (R ⧸ J) ≃ AdicCompletion I' (R ⧸ J) where
  toFun x := ⟨fun n ↦ t I J I' hI n (x.val n), fun {m n} hmn ↦ by
    have hx : AdicCompletion.transitionMap I (R ⧸ J) hmn (x.val n) = x.val m := x.prop hmn
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    change AdicCompletion.transitionMap I' (R ⧸ J) hmn (t I J I' hI n (x.val n)) =
      t I J I' hI m (x.val m)
    rw [← hx, ← hz]
    rfl⟩
  invFun y := ⟨fun n ↦ (t I J I' hI n).symm (y.val n), fun {m n} hmn ↦ by
    have hy : AdicCompletion.transitionMap I' (R ⧸ J) hmn (y.val n) = y.val m := y.prop hmn
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (y.val n)
    change AdicCompletion.transitionMap I (R ⧸ J) hmn ((t I J I' hI n).symm (y.val n)) =
      (t I J I' hI m).symm (y.val m)
    rw [← hy, ← hz]
    rfl⟩
  left_inv x := by
    ext n
    exact (t I J I' hI n).symm_apply_apply _
  right_inv y := by
    ext n
    exact (t I J I' hI n).apply_symm_apply _

lemma e_val (x : AdicCompletion I (R ⧸ J)) (n : ℕ) :
    (e I J I' hI x).val n = t I J I' hI n (x.val n) := rfl

lemma e_zero : e I J I' hI 0 = 0 := by
  ext n
  rw [e_val]
  rfl

include hI in
lemma le_comap (n : ℕ) : I ^ n ≤ (I' ^ n).comap (Ideal.Quotient.mkₐ R J) := by
  rw [← Ideal.map_le_iff_le_comap, ← hI, ← Ideal.map_pow]
  rfl

/-- Level `n` of `ψ`: `R̂ → R/Iⁿ → (R/J)/I'ⁿ`. -/
def lev (n : ℕ) : AdicCompletion I R →ₐ[R] (R ⧸ J) ⧸ I' ^ n :=
  (Ideal.quotientMapₐ (I' ^ n) (Ideal.Quotient.mkₐ R J) (le_comap I J I' hI n)).comp
    (AdicCompletion.evalₐ I n)

lemma lev_mk (n : ℕ) (a : AdicCompletion.AdicCauchySequence I R) :
    lev I J I' hI n (AdicCompletion.mk I R a) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk J (a n)) := by
  simp [lev, AdicCompletion.evalₐ_mk]

lemma lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (lev I J I' hI n) =
      lev I J I' hI m := by
  ext x
  induction x using AdicCompletion.induction_on with
  | h a =>
    simp only [AlgHom.comp_apply, lev_mk]
    rw [Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
    have h := AdicCompletion.AdicCauchySequence.mk_eq_mk hle a
    rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at h
    exact le_comap I J I' hI m (by simpa using h)

/-- **The completion map `ψ : R̂ → (R/J)^∧`.** -/
def ψ : AdicCompletion I R →ₐ[R] AdicCompletion I' (R ⧸ J) :=
  AdicCompletion.liftAlgHom I' (lev I J I' hI) (lev_compat I J I' hI)

lemma ψ_eq (x : AdicCompletion I R) :
    ψ I J I' hI x = e I J I' hI (AdicCompletion.map I (Submodule.mkQ J) x) := by
  induction x using AdicCompletion.induction_on with
  | h a =>
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    rw [ψ, AdicCompletion.evalₐ_liftAlgHom, lev_mk]
    rfl

include hI in
/-- **`ψ` is surjective.** -/
theorem surjective_ψ : Function.Surjective (ψ I J I' hI) := by
  intro y
  obtain ⟨x, hx⟩ := AdicCompletion.map_surjective I (Submodule.mkQ_surjective J)
    ((e I J I' hI).symm y)
  exact ⟨x, by rw [ψ_eq, hx, Equiv.apply_symm_apply]⟩

variable [IsNoetherianRing R]

/-- The image of `J^∧ → R̂` is `J R̂`. -/
lemma range_map_subtype :
    (LinearMap.range (AdicCompletion.map I J.subtype) : Set (AdicCompletion I R)) =
      (J.map (algebraMap R (AdicCompletion I R)) : Set (AdicCompletion I R)) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I J).2 z
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r j =>
      rw [AdicCompletion.ofTensorProduct_tmul, LinearMap.map_smul, AdicCompletion.map_of]
      exact Submodule.smul_mem _ r (Ideal.mem_map_of_mem (algebraMap R (AdicCompletion I R)) j.2)
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact Ideal.add_mem _ h₁ h₂
  · intro x hx
    have : J.map (algebraMap R (AdicCompletion I R)) ≤
        LinearMap.range (AdicCompletion.map I J.subtype) := by
      rw [Ideal.map, Ideal.span_le]
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨AdicCompletion.of I J ⟨j, hj⟩, by rw [AdicCompletion.map_of]; rfl⟩
    exact this hx

include hI in
/-- **The kernel of `ψ` is `J R̂`.** -/
theorem ker_ψ : RingHom.ker (ψ I J I' hI) = J.map (algebraMap R (AdicCompletion I R)) := by
  have hex := AdicCompletion.map_exact (I := I) (f := J.subtype) (g := Submodule.mkQ J)
    (Submodule.injective_subtype J) (LinearMap.exact_subtype_mkQ J) (Submodule.mkQ_surjective J)
  ext x
  rw [RingHom.mem_ker, ψ_eq, ← SetLike.mem_coe,
    ← range_map_subtype I J, SetLike.mem_coe, LinearMap.mem_range, ← Set.mem_range, ← hex x,
    ← e_zero I J I' hI, (e I J I' hI).injective.eq_iff]

end

end CompletionQuot

end SemistableReduction
