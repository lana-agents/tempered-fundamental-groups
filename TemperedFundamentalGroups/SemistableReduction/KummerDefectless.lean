/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.InertiallyGenerated

/-!
# Galois extensions of degree `p` of inertially generated fields are defectless

Blueprint §9.4, F5 (Kuhlmann, *Elimination of ramification I*, Proposition 5.1 (DP) in the
residue-transcendental mixed characteristic case). Let `C` be an algebraically closed
non-archimedean field of characteristic `0` with `‖p‖ < 1`, and `M ⊇ C` complete and inertially
generated (`InertiallyGenerated.IsInertiallyGenerated`). Every Galois extension `E / M` of
degree `p` is defectless: `e(w | M) · f(w | M) = [E : M]` for any valuation `w` on `E` extending
the norm valuation of `M` (`defectless_of_isGalois`); in fact `e = 1` and `f = p`.

Proof: `ζ_p ∈ C ⊆ M`, so `E = M(α)` with `α ^ p = a ∈ M` (Kummer theory, cyclic Galois group of
prime order); `a` is not a `p`-th power in `M` (otherwise `α ∈ M`, as all `p`-th roots of unity of
`E` lie in `M`). `M` carries a lifted Frobenius-closed basis (F2), so the Kummer normal form
(F4) gives `f ≥ p`.
-/

open Polynomial

namespace SemistableReduction

open KummerNormalForm InertiallyGenerated IntermediateField

namespace KummerDefectless

variable {C M : Type*} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
  [NormedField M] [IsUltrametricDist M] [CompleteSpace M] [NormedAlgebra C M]
  {E : Type*} [Field E] [Algebra M E]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (w : Valuation E Γ) [(NormedField.valuation (K := M)).HasExtension w]

/-- **F5 (DP), mixed characteristic.** A Galois extension `E / M` of degree `p` of an inertially
generated `M` is unramified-defectless: `e(w | M) = 1` and `f(w | M) = [E : M] = p`. -/
theorem ramificationIdx_eq_one_and_inertiaDeg_eq {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    {z : M} (hM : IsInertiallyGenerated C z) [IsGalois M E] (hdeg : Module.finrank M E = p) :
    FundamentalInequality.ramificationIdx M w = 1 ∧
      FundamentalInequality.inertiaDeg (NormedField.valuation (K := M)) w =
        Module.finrank M E := by
  haveI := Fact.mk hp
  haveI : FiniteDimensional M E :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact hp.pos)
  obtain ⟨L⟩ := nonempty_liftedFrobeniusBasis (M := M) hp hp1 hM
  have hpM1 : ‖(p : M)‖ < 1 := by rwa [LiftedFrobeniusBasis.norm_natCast_eq (C := C)]
  have hpM0 : (p : M) ≠ 0 := by
    rw [← map_natCast (algebraMap C M)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.ne_zero)
  -- a primitive `p`-th root of unity in `M`
  haveI : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  have hζM : IsPrimitiveRoot (algebraMap C M ζ) p :=
    hζ.map_of_injective (algebraMap C M).injective
  -- Kummer theory
  haveI : IsCyclic Gal(E/M) := isCyclic_of_prime_card (p := p)
    (by rw [IsGalois.card_aut_eq_finrank, hdeg])
  obtain ⟨α, ⟨a, ha⟩, hαtop⟩ := exists_root_adjoin_eq_top_of_isCyclic M E
    ⟨algebraMap C M ζ, (mem_primitiveRoots (by rw [hdeg]; exact hp.pos)).2 (hdeg ▸ hζM)⟩
  rw [hdeg] at ha
  have hbot : ∀ y ∈ Set.range (algebraMap M E), α ≠ y := by
    rintro _ ⟨b, rfl⟩ h
    have : M⟮α⟯ = ⊥ := by
      rw [h]
      exact adjoin_simple_eq_bot_iff.2 (IntermediateField.algebraMap_mem _ b)
    rw [this] at hαtop
    have h1 := congrArg (fun K : IntermediateField M E ↦ Module.finrank M K) hαtop
    simp only [IntermediateField.finrank_bot, IntermediateField.finrank_top'] at h1
    rw [← h1] at hdeg
    exact hp.one_lt.ne hdeg
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, pow_eq_zero_iff hp.ne_zero] at ha
    exact hbot 0 ⟨0, map_zero _⟩ ha
  have hapow : ∀ y : M, y ^ p ≠ a := by
    intro y hy
    have hy0 : algebraMap M E y ≠ 0 := by
      intro h
      rw [(_root_.map_eq_zero_iff _ (algebraMap M E).injective).1 h, zero_pow hp.ne_zero] at hy
      exact ha0 hy.symm
    have hζE : IsPrimitiveRoot (algebraMap M E (algebraMap C M ζ)) p :=
      hζM.map_of_injective (algebraMap M E).injective
    have hroot : (α / algebraMap M E y) ^ p = 1 := by
      rw [div_pow, ← map_pow, hy, ha, div_self (pow_ne_zero _ (hbot 0 ⟨0, map_zero _⟩))]
    obtain ⟨i, -, hi⟩ := hζE.eq_pow_of_pow_eq_one hroot
    apply hbot (algebraMap M E (y * algebraMap C M ζ ^ i)) ⟨_, rfl⟩
    rw [_root_.map_mul, _root_.map_pow, hi, mul_div_cancel₀ _ hy0]
  have hα : α ^ p = algebraMap M E a := ha.symm
  obtain ⟨he, hf, -⟩ := LiftedFrobeniusBasis.defectless_of_pow_eq w L hp hpM0 hpM1 hα ha0 hapow
    hdeg.le
  exact ⟨he, hf⟩

/-- **F5 (DP), mixed characteristic**: every Galois extension of degree `p` of an inertially
generated field is defectless. -/
theorem defectless_of_isGalois {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) {z : M}
    (hM : IsInertiallyGenerated C z) [IsGalois M E] (hdeg : Module.finrank M E = p) :
    FundamentalInequality.ramificationIdx M w *
        FundamentalInequality.inertiaDeg (NormedField.valuation (K := M)) w =
      Module.finrank M E := by
  obtain ⟨he, hf⟩ := ramificationIdx_eq_one_and_inertiaDeg_eq w hp hp1 hM hdeg
  rw [he, hf, one_mul]

end KummerDefectless

end SemistableReduction
