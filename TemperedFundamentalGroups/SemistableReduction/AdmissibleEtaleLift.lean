/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Finite
import TemperedFundamentalGroups.SemistableReduction.EtaleLiftExists

/-!
# Lifting a covering of the special fibre over `D(f)` (Blueprint §12.8, M2.3 at one level)

Setting: a Noetherian ring `R` with a nilpotent ideal `J` (`Jⁿ = 0`, e.g. `J = ϖR` for the
level-`n` chart), `f ∈ R`, and an `R/J`-algebra `C` (the covering of the special fibre) which is
finite over `R/J` and étale over `D(f̄)`.

**`AwayLift.exists_lift`**: there is an `R`-algebra `P` which is formally étale over `R`, in which
`f` is a unit, which is finite over `R_f` in the form `∀ p, ∃ k, f^k p ∈ R·s` (the hypothesis `hP`
of `FormalPatchLevel.finite_patch`), with `P/JP ≃ C_f` as `R`-algebras — the input `P`, `σP` of
`AdmissibleLift.patch_spec`.

Proof: `R_f/J R_f ≅ (R/J)_{f̄}` (localization commutes with quotients, Mathlib instance
`IsLocalization (algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I.map _)`), so `C_f` is a finite étale
`R_f/J R_f`-algebra (`RingHom.Etale` and `RingHom.Finite` of `Localization.awayMap`, composed with
the isomorphism), and `EtaleLiftExists.exists_finite_etale_lift_of_pow_eq_bot` over `R_f` (with
`(J R_f)ⁿ = 0`) gives `P`.
-/

universe u

namespace SemistableReduction

namespace AwayLift

noncomputable section

variable {R : Type u} [CommRing R] (J : Ideal R) (f : R)

/-- `R_f`. -/
abbrev Rf : Type u := Localization.Away f

/-- `J R_f`. -/
abbrev Jf : Ideal (Rf f) := J.map (algebraMap R (Rf f))

/-- The image `f̄` of `f` in `R/J`. -/
abbrev fb : R ⧸ J := Ideal.Quotient.mk J f

instance isLocalization_quot : IsLocalization.Away (fb J f) (Rf f ⧸ Jf J f) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ J) (Submonoid.powers f))
      (Rf f ⧸ Jf J f) := inferInstance
  unfold IsLocalization.Away
  convert this using 1
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  rfl

/-- `R_f/J R_f ≃ (R/J)_{f̄}`. -/
def quotEquiv : (Rf f ⧸ Jf J f) ≃ₐ[R ⧸ J] Localization.Away (fb J f) :=
  IsLocalization.algEquiv (Submonoid.powers (fb J f)) _ _

variable {C : Type u} [CommRing C] [Algebra (R ⧸ J) C]

/-- The structure map `R_f/J R_f → C_f`. -/
def g : (Rf f ⧸ Jf J f) →+* Localization.Away (algebraMap (R ⧸ J) C (fb J f)) :=
  (Localization.awayMap (algebraMap (R ⧸ J) C) (fb J f)).comp (quotEquiv J f).toRingHom

lemma g_etale (hC : (Localization.awayMap (algebraMap (R ⧸ J) C) (fb J f)).Etale) :
    (g J f (C := C)).Etale :=
  RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (quotEquiv J f).bijective) hC

lemma g_finite [Module.Finite (R ⧸ J) C] : (g J f (C := C)).Finite := by
  refine RingHom.finite_stableUnderComposition _ _
    (RingHom.Finite.of_surjective _ (quotEquiv J f).surjective) ?_
  exact RingHom.localization_away_map_finite (R ⧸ J) C _ _ (algebraMap (R ⧸ J) C) (fb J f)
    (RingHom.finite_algebraMap.mpr inferInstance)

lemma g_mk_algebraMap (r : R) :
    g J f (C := C) (Ideal.Quotient.mk _ (algebraMap R (Rf f) r)) =
      algebraMap C _ (algebraMap (R ⧸ J) C (Ideal.Quotient.mk J r)) := by
  have h1 : (Ideal.Quotient.mk (Jf J f) (algebraMap R (Rf f) r)) =
      algebraMap (R ⧸ J) (Rf f ⧸ Jf J f) (Ideal.Quotient.mk J r) := rfl
  rw [g, RingHom.comp_apply, h1]
  change Localization.awayMap _ _ ((quotEquiv J f) _) = _
  rw [AlgEquiv.commutes, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

/-- **Finiteness over `R_f` in the form needed by `FormalPatchLevel.finite_patch`.** -/
lemma exists_finset_of_finite {P : Type u} [CommRing P] [Algebra R P] [Algebra (Rf f) P]
    [IsScalarTower R (Rf f) P] [Module.Finite (Rf f) P] :
    ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Rf f) (M := P)
  refine ⟨s, fun p ↦ ?_⟩
  have hp : p ∈ Submodule.span (Rf f) (s : Set P) := hs ▸ Submodule.mem_top
  induction hp using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add, pow_add, mul_comm, mul_smul, mul_comm, mul_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨⟨r, ⟨_, m, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers f) c
    refine ⟨a + m, ?_⟩
    have hc : f ^ m • c = algebraMap R (Rf f) r := by
      rw [Algebra.smul_def, mul_comm]
      exact hr
    have key : f ^ (a + m) • (c • x) = r • (f ^ a • x) := by
      calc f ^ (a + m) • (c • x) = f ^ a • (f ^ m • (c • x)) := by rw [pow_add, mul_smul]
        _ = f ^ a • ((f ^ m • c) • x) := by rw [smul_assoc]
        _ = f ^ a • (r • x) := by rw [hc, algebraMap_smul]
        _ = r • (f ^ a • x) := smul_comm _ _ _
    rw [key]
    exact Submodule.smul_mem _ _ ha

variable [Algebra R C] [IsScalarTower R (R ⧸ J) C]

/-- **Lifting the covering over `D(f)`**: a formally étale `R`-algebra `P`, finite over `R_f`,
with `P/JP ≃ C_f`. -/
theorem exists_lift [IsNoetherianRing R] {n : ℕ} (hJ : J ^ n = ⊥) [Module.Finite (R ⧸ J) C]
    (hC : (Localization.awayMap (algebraMap (R ⧸ J) C) (fb J f)).Etale) :
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra R P), Algebra.FormallyEtale R P ∧
      IsUnit (algebraMap R P f) ∧
      (∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P)) ∧
      Nonempty ((P ⧸ J.map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R C f)) := by
  have hfC : algebraMap R C f = algebraMap (R ⧸ J) C (fb J f) :=
    IsScalarTower.algebraMap_apply R (R ⧸ J) C f
  let S₀ := Localization.Away (algebraMap (R ⧸ J) C (fb J f))
  letI : Algebra (Rf f ⧸ Jf J f) S₀ := (g J f).toAlgebra
  letI : Algebra (Rf f) S₀ := ((g J f).comp (Ideal.Quotient.mk _)).toAlgebra
  haveI : IsScalarTower (Rf f) (Rf f ⧸ Jf J f) S₀ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.Etale (Rf f ⧸ Jf J f) S₀ := g_etale J f hC
  haveI : Module.Finite (Rf f ⧸ Jf J f) S₀ := g_finite J f
  haveI : IsNoetherianRing (Rf f) := IsLocalization.isNoetherianRing (Submonoid.powers f) _
    inferInstance
  have hJf : Jf J f ^ n = ⊥ := by rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  obtain ⟨P, _, _, hfin, het, ⟨σ⟩⟩ :=
    EtaleLiftExists.exists_finite_etale_lift_of_pow_eq_bot (Jf J f) hJf S₀
  letI : Algebra R P := Algebra.compHom P (algebraMap R (Rf f))
  haveI : IsScalarTower R (Rf f) P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.FormallyEtale R (Rf f) := Algebra.FormallyEtale.of_isLocalization
    (Submonoid.powers f)
  haveI : Algebra.FormallyEtale R P := Algebra.FormallyEtale.comp R (Rf f) P
  -- the `R`-algebra structure of `S₀` (as a localization of `C`) agrees with the one through `R_f`
  haveI : IsScalarTower R (Rf f) S₀ := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R C S₀]
    change _ = g J f (Ideal.Quotient.mk _ (algebraMap R _ r))
    rw [g_mk_algebraMap, IsScalarTower.algebraMap_apply R (R ⧸ J) C]
    rfl
  have hideal : J.map (algebraMap R P) = (Jf J f).map (algebraMap (Rf f) P) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine ⟨P, inferInstance, inferInstance, inferInstance, ?_,
    exists_finset_of_finite f, ⟨?_⟩⟩
  · rw [IsScalarTower.algebraMap_apply R (Rf f) P]
    exact (IsLocalization.Away.algebraMap_isUnit f).map _
  · rw [hfC]
    exact (Ideal.quotientEquivAlgOfEq R hideal).trans (σ.restrictScalars R)

end

end AwayLift

end SemistableReduction
