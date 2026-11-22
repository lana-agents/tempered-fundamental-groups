/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.SplitAfterExtension

/-!
# Splitting a complete semilocal ring into local factors (S6, splitting)

Let `D` be a commutative ring which is `J`-adically complete for an ideal `J` with `D ⧸ J`
Artinian, and with finitely many maximal ideals. Then (**`exists_idempotents_maximalSpectrum`**)
there are complete orthogonal idempotents `ε_Q` (`Q` maximal) with `ε_Q ∈ Q'` iff `Q ≠ Q'`: the
idempotents of `D ⧸ Jac(D) ≅ ∏_Q D ⧸ Q` (Chinese remainder theorem) lift along the nil ideal
`Jac(D)/J` of the Artinian ring `D ⧸ J` and then along the complete ideal `J` (Hensel), and
lifted idempotents stay complete orthogonal since `J ⊆ Jac(D)`.

For such an idempotent the factor `D ⧸ (1 − ε_Q)` is local with maximal ideal the image of `Q`
(**`isLocalRing_quotient_one_sub`**, **`maximalIdeal_quotient_one_sub`**).
-/

open IsLocalRing

namespace SemistableReduction

namespace FormalKummer

section Idempotents

variable {D : Type*} [CommRing D]

/-- An idempotent in the Jacobson radical vanishes. -/
theorem eq_zero_of_isIdempotentElem_of_mem_jacobson {x : D} (hx : IsIdempotentElem x)
    (h : x ∈ (⊥ : Ideal D).jacobson) : x = 0 := by
  have hu : IsUnit (x * (-1) + 1) := Ideal.mem_jacobson_bot.mp h (-1)
  have h0 : x * (x * (-1) + 1) = 0 := by
    have := hx.eq
    linear_combination -this
  exact (hu.mul_left_eq_zero).mp h0

/-- Idempotents whose reductions modulo an ideal inside the Jacobson radical are complete
orthogonal are complete orthogonal. -/
theorem completeOrthogonalIdempotents_of_quot {J : Ideal D} (hJ : J ≤ (⊥ : Ideal D).jacobson)
    {ι : Type*} [Fintype ι] (ε : ι → D) (hε : ∀ i, IsIdempotentElem (ε i))
    (h : CompleteOrthogonalIdempotents (Ideal.Quotient.mk J ∘ ε)) :
    CompleteOrthogonalIdempotents ε := by
  have hortho : OrthogonalIdempotents ε := by
    refine ⟨hε, fun i j hij ↦ ?_⟩
    refine eq_zero_of_isIdempotentElem_of_mem_jacobson ((hε i).mul (hε j)) (hJ ?_)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact h.ortho hij
  refine ⟨hortho, ?_⟩
  have hsum : IsIdempotentElem (∑ i, ε i) := hortho.isIdempotentElem_sum
  have h1 := eq_zero_of_isIdempotentElem_of_mem_jacobson hsum.one_sub (hJ ?_)
  · exact (sub_eq_zero.mp h1).symm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_sum]
  have := h.complete
  simp only [Function.comp_apply] at this
  rw [this, sub_self]

/-- **Idempotents separating the maximal ideals** of a complete semilocal ring. -/
theorem exists_idempotents_maximalSpectrum (J : Ideal D) [IsAdicComplete J D]
    [IsArtinianRing (D ⧸ J)] [Fintype (MaximalSpectrum D)] :
    ∃ ε : MaximalSpectrum D → D, CompleteOrthogonalIdempotents ε ∧
      ∀ Q Q' : MaximalSpectrum D, ε Q ∈ Q'.asIdeal ↔ Q ≠ Q' := by
  classical
  have hJ : J ≤ (⊥ : Ideal D).jacobson := IsAdicComplete.le_jacobson_bot J
  set K : Ideal D := ⨅ Q : MaximalSpectrum D, Q.asIdeal with hK
  let χ := Ideal.quotientInfRingEquivPiQuotient (fun Q : MaximalSpectrum D ↦ Q.asIdeal)
    fun _ _ h ↦ MaximalSpectrum.isCoprime_of_ne h
  have hχ (x : D) (Q' : MaximalSpectrum D) :
      χ (Ideal.Quotient.mk K x) Q' = Ideal.Quotient.mk Q'.asIdeal x := rfl
  let f : MaximalSpectrum D → D ⧸ K := fun Q ↦ χ.symm (Pi.single Q 1)
  have hf : CompleteOrthogonalIdempotents f :=
    (CompleteOrthogonalIdempotents.single (fun Q : MaximalSpectrum D ↦ D ⧸ Q.asIdeal)).map
      χ.symm.toRingHom
  have hJK : J ≤ K := by
    intro x hx
    rw [hK, Ideal.mem_iInf]
    intro Q
    exact Ideal.mem_sInf.mp (hJ hx) ⟨bot_le, Q.isMaximal⟩
  let φ : D ⧸ J →+* D ⧸ K := Ideal.Quotient.factor hJK
  have hφ : Function.Surjective φ := Ideal.Quotient.factor_surjective hJK
  have hker : ∀ x ∈ RingHom.ker φ, IsNilpotent x := by
    intro x hx
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hd : d ∈ K := by
      rw [RingHom.mem_ker] at hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    haveI : P.IsPrime := hP
    haveI : P.IsMaximal := IsArtinianRing.isMaximal_of_isPrime P
    have hPm : (P.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    rw [hK, Ideal.mem_iInf] at hd
    exact hd ⟨P.comap (Ideal.Quotient.mk J), hPm⟩
  obtain ⟨ē, hē, hēf⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker φ hker hf
    fun Q ↦ hφ (f Q)
  choose ε hε hεē using fun Q ↦
    SplitAfterExtension.exists_isIdempotentElem_lift J (ē Q) (hē.idem Q)
  have hε' : CompleteOrthogonalIdempotents ε :=
    completeOrthogonalIdempotents_of_quot hJ ε hε (by
      have : Ideal.Quotient.mk J ∘ ε = ē := funext hεē
      rw [this]
      exact hē)
  refine ⟨ε, hε', fun Q Q' ↦ ?_⟩
  have h1 : Ideal.Quotient.mk K (ε Q) = f Q := by
    rw [← congr_fun hēf Q, Function.comp_apply, ← hεē Q]
    rfl
  have h2 : Ideal.Quotient.mk Q'.asIdeal (ε Q) = (Pi.single Q 1 : ∀ Q, D ⧸ Q.asIdeal) Q' := by
    rw [← hχ, h1]
    simp [f]
  rw [← Ideal.Quotient.eq_zero_iff_mem, h2]
  by_cases hQ : Q = Q'
  · subst hQ
    simp
  · simp [Ne.symm hQ, hQ]

/-- The maximal ideal `Q` contains `1 − ε` if `ε ∉ Q`. -/
theorem one_sub_mem_of_notMem {ε : D} (hε : IsIdempotentElem ε) {Q : Ideal D} [Q.IsPrime]
    (hQ : ε ∉ Q) : 1 - ε ∈ Q := by
  have : (1 - ε) * ε ∈ Q := by
    rw [sub_mul, one_mul, hε.eq, sub_self]
    exact Q.zero_mem
  exact (Ideal.IsPrime.mem_or_mem ‹_› this).resolve_right hQ

variable {ε : D} (hε : IsIdempotentElem ε) (Q : Ideal D) [Q.IsMaximal] (hQ : ε ∉ Q)
  (huniq : ∀ Q' : Ideal D, Q'.IsMaximal → ε ∉ Q' → Q' = Q)
include hε hQ

/-- The image of `Q` in `D ⧸ (1 − ε)` is maximal. -/
theorem isMaximal_map_quotient_one_sub :
    (Q.map (Ideal.Quotient.mk (Ideal.span {1 - ε}))).IsMaximal := by
  have hle : Ideal.span {1 - ε} ≤ Q := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact one_sub_mem_of_notMem hε hQ
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    ‹Q.IsMaximal›).resolve_left fun h ↦ ?_
  have h1 : Ideal.Quotient.mk (Ideal.span {1 - ε}) 1 ∈
      Q.map (Ideal.Quotient.mk (Ideal.span {1 - ε})) := by
    rw [h]
    exact Submodule.mem_top
  rw [Ideal.mem_quotient_iff_mem hle] at h1
  exact (Ideal.IsMaximal.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr h1)

include huniq

/-- **The factor `D ⧸ (1 − ε)` is local** if `Q` is the only maximal ideal avoiding `ε`. -/
theorem isLocalRing_quotient_one_sub : IsLocalRing (D ⧸ Ideal.span {1 - ε}) := by
  haveI := isMaximal_map_quotient_one_sub hε Q hQ
  refine .of_unique_max_ideal ⟨_, this, fun M hM ↦ ?_⟩
  haveI : (M.comap (Ideal.Quotient.mk (Ideal.span {1 - ε}))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hεM : ε ∉ M.comap (Ideal.Quotient.mk (Ideal.span {1 - ε})) := by
    intro h
    rw [Ideal.mem_comap] at h
    have h0 : Ideal.Quotient.mk (Ideal.span {1 - ε}) (1 - ε) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    have h1 : (1 : D ⧸ Ideal.span {1 - ε}) ∈ M := by
      have : (1 : D ⧸ Ideal.span {1 - ε}) =
          Ideal.Quotient.mk _ (1 - ε) + Ideal.Quotient.mk _ ε := by
        rw [← map_add, sub_add_cancel, map_one]
      rw [this, h0, zero_add]
      exact h
    exact (Ideal.IsMaximal.ne_top hM) ((Ideal.eq_top_iff_one _).mpr h1)
  rw [← huniq _ inferInstance hεM, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

omit huniq in
/-- The maximal ideal of the factor `D ⧸ (1 − ε)` is the image of `Q`. -/
theorem maximalIdeal_quotient_one_sub [IsLocalRing (D ⧸ Ideal.span {1 - ε})] :
    maximalIdeal (D ⧸ Ideal.span {1 - ε}) = Q.map (Ideal.Quotient.mk (Ideal.span {1 - ε})) :=
  haveI := isMaximal_map_quotient_one_sub hε Q hQ
  (eq_maximalIdeal this).symm

end Idempotents

end FormalKummer

end SemistableReduction
