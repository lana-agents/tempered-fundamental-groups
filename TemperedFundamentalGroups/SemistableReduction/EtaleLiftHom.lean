/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Etale.Basic

/-!
# Lifting morphisms out of étale algebras to complete targets (Blueprint §12.8, M2.2)

Let `A` be a formally étale `R`-algebra and `S` an `R`-algebra which is `J`-adically complete for
an ideal `J ⊆ S`. Then every `R`-algebra map `A → S/J` lifts uniquely to `A → S`:
**`EtaleLift.homEquiv : (A →ₐ[R] S) ≃ (A →ₐ[R] S ⧸ J)`**. The lifts to `S/J^{n+1}` exist and are
unique because the kernel of `S/J^{n+1} → S/J` is nilpotent (Mathlib's
`Algebra.FormallySmooth.liftOfSurjective`, `Algebra.FormallyUnramified.lift_unique'`); they are
compatible by uniqueness and assemble by completeness (`IsAdicComplete.liftAlgHom`). This is the
infinitesimal lifting property defining formal étaleness (Stacks, Definition 10.150.1,
Tag 00UQ), passed to the limit over the thickenings `S/J^{n+1}`.

Consequently two formally étale `R`-algebras `B`, `B'`, complete along `I`, with an isomorphism
`B/IB ≅ B'/IB'` are isomorphic by a unique isomorphism lifting it
(**`EtaleLift.algEquivOfQuot`**). This is the uniqueness half of M2.2 for *arbitrary* finite
étale algebras, generalizing the monogenic case `SemistableReduction.EtaleLift.equivOfLift`; it
is what the formal patching (M2.3) needs on the overlaps of an affine cover.
-/

namespace SemistableReduction

namespace EtaleLift

variable {R A S : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]
  (J : Ideal S)

lemma pow_succ_le (n : ℕ) : J ^ (n + 1) ≤ J := Ideal.pow_le_self (Nat.succ_ne_zero n)

/-- The kernel of `S/J^{n+1} → S/J` is nilpotent. -/
lemma isNilpotent_ker_factor (n : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factorₐ R (pow_succ_le J n) :
      S ⧸ J ^ (n + 1) →+* S ⧸ J)) := by
  refine ⟨n + 1, ?_⟩
  have hker : RingHom.ker (Ideal.Quotient.factorₐ R (pow_succ_le J n) :
      S ⧸ J ^ (n + 1) →+* S ⧸ J) = J.map (Ideal.Quotient.mk (J ^ (n + 1))) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · intro hx
      exact ⟨x, (Ideal.Quotient.eq_zero_iff_mem).1 hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx]
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hy
  rw [hker, ← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]

lemma factorₐ_comp_factorₐ {I₁ I₂ I₃ : Ideal S} (h₁₂ : I₁ ≤ I₂) (h₂₃ : I₂ ≤ I₃) :
    (Ideal.Quotient.factorₐ R h₂₃).comp (Ideal.Quotient.factorₐ R h₁₂) =
      Ideal.Quotient.factorₐ R (h₁₂.trans h₂₃) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable [Algebra.FormallyEtale R A] (g₀ : A →ₐ[R] S ⧸ J)

/-- The lift of `g₀` to `S/J^{n+1}`. -/
noncomputable def liftSucc (n : ℕ) : A →ₐ[R] S ⧸ J ^ (n + 1) :=
  Algebra.FormallySmooth.liftOfSurjective g₀ (Ideal.Quotient.factorₐ R (pow_succ_le J n))
    (Ideal.Quotient.factor_surjective (pow_succ_le J n)) (isNilpotent_ker_factor J n)

lemma factorₐ_comp_liftSucc (n : ℕ) :
    (Ideal.Quotient.factorₐ R (pow_succ_le J n)).comp (liftSucc J g₀ n) = g₀ := by
  unfold liftSucc
  exact Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _

/-- **Uniqueness of the lifts**: two maps to `S/J^{n+1}` with the same reduction modulo `J`
agree. -/
lemma eq_of_comp_eq (n : ℕ) {g₁ g₂ : A →ₐ[R] S ⧸ J ^ (n + 1)}
    (h : (Ideal.Quotient.factorₐ R (pow_succ_le J n)).comp g₁ =
      (Ideal.Quotient.factorₐ R (pow_succ_le J n)).comp g₂) : g₁ = g₂ :=
  Algebra.FormallyUnramified.lift_unique' _ (isNilpotent_ker_factor J n) g₁ g₂ h

lemma factorₐ_comp_liftSucc_of_le {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn))).comp
      (liftSucc J g₀ n) = liftSucc J g₀ m := by
  refine eq_of_comp_eq J m ?_
  rw [← AlgHom.comp_assoc, factorₐ_comp_factorₐ, factorₐ_comp_liftSucc, factorₐ_comp_liftSucc]

/-- The compatible family of lifts to `S/Jⁿ`. -/
noncomputable def liftPow (n : ℕ) : A →ₐ[R] S ⧸ J ^ n :=
  (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (liftSucc J g₀ n)

lemma liftPow_compat {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (liftPow J g₀ n) =
      liftPow J g₀ m := by
  rw [liftPow, liftPow, ← AlgHom.comp_assoc, factorₐ_comp_factorₐ,
    ← factorₐ_comp_liftSucc_of_le J g₀ hmn, ← AlgHom.comp_assoc, factorₐ_comp_factorₐ]

variable [IsAdicComplete J S]

/-- **The lift of `g₀ : A → S/J` to `A → S`.** -/
noncomputable def lift : A →ₐ[R] S :=
  IsAdicComplete.liftAlgHom J (liftPow J g₀) (fun hle ↦ liftPow_compat J g₀ hle)

lemma mkₐ_comp_lift : (Ideal.Quotient.mkₐ R J).comp (lift J g₀) = g₀ := by
  have h1 := IsAdicComplete.mkₐ_comp_liftAlgHom J (liftPow J g₀)
    (fun hle ↦ liftPow_compat J g₀ hle) 1
  have e : (Ideal.Quotient.mkₐ R J) =
      (Ideal.Quotient.factorₐ R (pow_succ_le J 0)).comp (Ideal.Quotient.mkₐ R (J ^ 1)) := by
    ext x; rfl
  rw [e, AlgHom.comp_assoc]
  change (Ideal.Quotient.factorₐ R (pow_succ_le J 0)).comp
    ((Ideal.Quotient.mkₐ R (J ^ 1)).comp (IsAdicComplete.liftAlgHom J (liftPow J g₀) _)) = g₀
  rw [h1, liftPow, ← AlgHom.comp_assoc, factorₐ_comp_factorₐ]
  exact factorₐ_comp_liftSucc J g₀ 1

/-- **Uniqueness**: maps `A → S` agreeing modulo `J` are equal. -/
lemma ext_of_comp_eq {g₁ g₂ : A →ₐ[R] S}
    (h : (Ideal.Quotient.mkₐ R J).comp g₁ = (Ideal.Quotient.mkₐ R J).comp g₂) : g₁ = g₂ := by
  refine IsAdicComplete.algHom_ext J fun n ↦ ?_
  cases n with
  | zero =>
    ext x
    have : Subsingleton (S ⧸ J ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    refine eq_of_comp_eq J n ?_
    have e : (Ideal.Quotient.factorₐ R (pow_succ_le J n)).comp
        (Ideal.Quotient.mkₐ R (J ^ (n + 1))) = Ideal.Quotient.mkₐ R J := by
      ext x; rfl
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, e, h]

/-- **Morphisms out of a formally étale algebra into a complete algebra are determined by, and
exist for, their reductions** (the lifting property of Stacks, Tag 00UQ, in the limit). -/
noncomputable def homEquiv : (A →ₐ[R] S) ≃ (A →ₐ[R] S ⧸ J) where
  toFun g := (Ideal.Quotient.mkₐ R J).comp g
  invFun g₀ := lift J g₀
  left_inv g := by
    change lift J ((Ideal.Quotient.mkₐ R J).comp g) = g
    exact ext_of_comp_eq J (mkₐ_comp_lift J _)
  right_inv g₀ := by
    change (Ideal.Quotient.mkₐ R J).comp (lift J g₀) = g₀
    exact mkₐ_comp_lift J g₀

section Equiv

variable {B B' : Type*} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
  [Algebra.FormallyEtale R B] [Algebra.FormallyEtale R B'] (I : Ideal R)
  [IsAdicComplete (I.map (algebraMap R B)) B] [IsAdicComplete (I.map (algebraMap R B')) B']

/-- The lift of a map of reductions `B/IB → B'/IB'`. -/
noncomputable def liftQuot (e : B ⧸ I.map (algebraMap R B) →ₐ[R] B' ⧸ I.map (algebraMap R B')) :
    B →ₐ[R] B' :=
  lift (I.map (algebraMap R B')) (e.comp (Ideal.Quotient.mkₐ R _))

omit [Algebra.FormallyEtale R B'] [IsAdicComplete (I.map (algebraMap R B)) B] in
lemma mkₐ_comp_liftQuot (e : B ⧸ I.map (algebraMap R B) →ₐ[R] B' ⧸ I.map (algebraMap R B')) :
    (Ideal.Quotient.mkₐ R _).comp (liftQuot I e) = e.comp (Ideal.Quotient.mkₐ R _) :=
  mkₐ_comp_lift _ _

lemma liftQuot_comp_liftQuot
    (e : B ⧸ I.map (algebraMap R B) →ₐ[R] B' ⧸ I.map (algebraMap R B'))
    (e' : B' ⧸ I.map (algebraMap R B') →ₐ[R] B ⧸ I.map (algebraMap R B))
    (h : e'.comp e = AlgHom.id R _) :
    (liftQuot I e').comp (liftQuot I e) = AlgHom.id R B := by
  refine ext_of_comp_eq (I.map (algebraMap R B)) ?_
  rw [← AlgHom.comp_assoc, mkₐ_comp_liftQuot, AlgHom.comp_assoc, mkₐ_comp_liftQuot,
    ← AlgHom.comp_assoc, h, AlgHom.id_comp, AlgHom.comp_id]

/-- **Uniqueness of étale lifts**: two formally étale `R`-algebras, complete along `I`, with
isomorphic reductions modulo `I` are isomorphic, by an isomorphism lifting the given one
(`mkₐ_comp_algEquivOfQuot`), which is unique (`ext_of_comp_eq`). -/
noncomputable def algEquivOfQuot
    (e : (B ⧸ I.map (algebraMap R B)) ≃ₐ[R] (B' ⧸ I.map (algebraMap R B'))) : B ≃ₐ[R] B' :=
  AlgEquiv.ofAlgHom (liftQuot I e.toAlgHom) (liftQuot I e.symm.toAlgHom)
    (liftQuot_comp_liftQuot I _ _ (by ext x; exact e.apply_symm_apply x))
    (liftQuot_comp_liftQuot I _ _ (by ext x; exact e.symm_apply_apply x))

lemma mkₐ_comp_algEquivOfQuot
    (e : (B ⧸ I.map (algebraMap R B)) ≃ₐ[R] (B' ⧸ I.map (algebraMap R B'))) :
    (Ideal.Quotient.mkₐ R _).comp (algEquivOfQuot I e).toAlgHom =
      e.toAlgHom.comp (Ideal.Quotient.mkₐ R _) :=
  mkₐ_comp_liftQuot I _

end Equiv

end EtaleLift

end SemistableReduction
