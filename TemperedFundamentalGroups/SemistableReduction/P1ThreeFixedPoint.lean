/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeHomSpecial
import TemperedFundamentalGroups.SemistableReduction.FixedSpecialPoint

/-!
# Stabilisers of generic points fix their reductions (MR13 "A2⁻", `ℙ¹ ∖ {0, 1, ā}`)

For a datum `D` of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` with an action `act : G → D.Hom D` and an
algebraization `L` of its lift, `G` acts on the cusp chart `B₀` by `O`-algebra maps
(**`Datum.ring0AlgHom`**, `B₀` an `O`-algebra through `const0`, `algO0`).
**`Datum.exists_fixed_special_point`**: for an `O`-algebra map `χ : B₀ → F` to a field with
`O → F` injective and `χ(X) = 0` (`χ` a point of the generic fibre over a cusp; `χ(B₀)` is then
integral over `O`, **`isIntegral_of_X0`**), there is a maximal ideal `𝔪` of `C0` (a special
point) containing the reductions of `ker χ`, such that every `g` with `χ ∘ (act g) = χ` fixes `𝔪`
under `(act g).φ0` (through `specialFibreEquiv0_algMap`).

With `χ` the residue map at a place `W` over a cusp, the inertia group of `W` (acting
trivially on the residue field) lies in the stabiliser of the special point `𝔪`: the inclusion
"A2⁻" used for Route B's B4′ (MR13-plan, run 16).
-/

universe u

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower ProjectiveLine Polynomial

noncomputable section

/-- The first chart of a chart algebra as an `O`-algebra (through `const0`). -/
@[reducible] def algO0 {O : Type u} [CommRing O] {N : ChartModule O} (B : ChartModule.AlgStr N) :
    Algebra O B.Ring0 :=
  B.const0.toAlgebra

/-- **A point of the first chart over `X = 0` is integral over `O`**: if `χ : B₀ → F` is
`O`-linear (on `const0`) and kills `X`, then every `χ b` is integral over `O` (`B₀` finite over
`O[X]`). -/
theorem isIntegral_of_X0 {O : Type u} [CommRing O] {N : ChartModule O}
    [Module.Finite O[X] (Module.AEval' N.x0)] (B : ChartModule.AlgStr N) {F : Type*} [Field F]
    [Algebra O F] (χ : B.Ring0 →+* F) (hχO : ∀ o, χ (B.const0 o) = algebraMap O F o)
    (hχX : χ B.X0 = 0) (b : B.Ring0) : IsIntegral O (χ b) := by
  letI := B.polyHom0.toAlgebra
  haveI := B.finite_polyHom0
  have hc : χ.comp B.const0 = algebraMap O F := RingHom.ext hχO
  have hpoly : χ.comp (algebraMap O[X] B.Ring0) =
      (algebraMap O F).comp (Polynomial.evalRingHom 0) := RingHom.ext fun p ↦ by
    change χ (Polynomial.eval₂ B.const0 B.X0 p) = algebraMap O F (p.eval 0)
    rw [Polynomial.hom_eval₂, hχX, Polynomial.eval₂_at_zero, hc,
      ← Polynomial.coeff_zero_eq_eval_zero]
  obtain ⟨p, hp, hpb⟩ := (Algebra.IsIntegral.isIntegral (R := O[X]) b)
  refine ⟨p.map (Polynomial.evalRingHom 0), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, ← hpoly, ← Polynomial.hom_eval₂, hpb, map_zero]

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

namespace Datum

variable (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {D : Datum O θ a} [IsAdicComplete (Ideal.span {ϖ}) O]
  {G : Type*} (act : G → D.Hom D)
  (L : AdicChartAlgSystem.Algebraization (systemD hϖ hker hO D))

/-- **`act g` on the cusp chart `B₀` of the lift, as a map of `O`-algebras.** -/
def ring0AlgHom (g : G) : letI := algO0 L.B; L.B.Ring0 →ₐ[O] L.B.Ring0 :=
  letI := algO0 L.B
  { (isHom_algMap hϖ hker ha0 ha1 hO (act g) L L).ringHom0 with
    commutes' := fun o ↦ (isHom_algMap hϖ hker ha0 ha1 hO (act g) L L).ringHom0_const0 o }

lemma ring0AlgHom_apply (g : G) (b : L.B.Ring0) :
    ring0AlgHom hϖ hker ha0 ha1 hO act L g b =
      (isHom_algMap hϖ hker ha0 ha1 hO (act g) L L).ringHom0 b :=
  rfl

/-- **The special point under a point of the generic fibre is fixed by the stabiliser of the
point** ("A2⁻"): for an `O`-linear `χ : B₀ → F` killing `X` (a point over a cusp; `O → F`
injective) there is a maximal ideal `𝔪` of `C0` containing the reductions of `ker χ` and fixed by
`(act g).φ0` whenever `χ ∘ (act g) = χ` on `B₀`. -/
theorem exists_fixed_special_point [(Ideal.span {ϖ}).IsMaximal] {F : Type*} [Field F]
    [Algebra O F] (hF : Function.Injective (algebraMap O F)) (χ : L.B.Ring0 →+* F)
    (hχO : ∀ o, χ (L.B.const0 o) = algebraMap O F o) (hχX : χ L.B.X0 = 0) :
    ∃ 𝔪 : Ideal D.S0.C0, 𝔪.IsMaximal ∧
      (∀ b, χ b = 0 → specialFibreEquiv0 D.Sp hϖ hker D.S0 D.om hO L.hα L.hB
        (Ideal.Quotient.mk _ b) ∈ 𝔪) ∧
      ∀ g, (∀ b, χ ((isHom_algMap hϖ hker ha0 ha1 hO (act g) L L).ringHom0 b) = χ b) →
        𝔪.comap (act g).φ0 = 𝔪 := by
  letI := algO0 L.B
  let χA : L.B.Ring0 →ₐ[O] F := { χ with commutes' := hχO }
  haveI : Algebra.IsIntegral O χA.range := ⟨fun ⟨y, b, hb⟩ ↦
    (isIntegral_algHom_iff χA.range.val Subtype.val_injective).1 (by
      change IsIntegral O y
      rw [← hb]
      exact isIntegral_of_X0 L.B χ hχO hχX b)⟩
  obtain ⟨𝔭, h𝔭max, h𝔭O, hkerχ, hfix⟩ := FixedSpecialPoint.exists_maximal_fixed χA
    (Ideal.span {ϖ}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hF]
      exact bot_le)
  have hϖ𝔭 : Ideal.span {L.B.const0 ϖ} ≤ 𝔭 := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : ϖ ∈ 𝔭.comap (algebraMap O L.B.Ring0) := by
      rw [h𝔭O]; exact Ideal.mem_span_singleton_self ϖ
    exact this
  letI := Ideal.Quotient.field 𝔭
  let e := specialFibreEquiv0 D.Sp hϖ hker D.S0 D.om hO L.hα L.hB
  let φ : D.S0.C0 →+* L.B.Ring0 ⧸ 𝔭 :=
    (Ideal.Quotient.factor hϖ𝔭).comp e.symm.toRingHom
  have hφ : Function.Surjective φ := fun z ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨e (Ideal.Quotient.mk _ b), by
      change Ideal.Quotient.factor hϖ𝔭 (e.symm (e _)) = _
      rw [RingEquiv.symm_apply_apply]
      rfl⟩
  have hmem : ∀ b, e (Ideal.Quotient.mk _ b) ∈ RingHom.ker φ ↔ b ∈ 𝔭 := fun b ↦ by
    rw [RingHom.mem_ker]
    change Ideal.Quotient.factor hϖ𝔭 (e.symm (e _)) = 0 ↔ _
    rw [RingEquiv.symm_apply_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨RingHom.ker φ, RingHom.ker_isMaximal_of_surjective φ hφ,
    fun b hb ↦ (hmem b).2 (hkerχ hb), fun g hg ↦ ?_⟩
  have hgA : χA.comp (ring0AlgHom hϖ hker ha0 ha1 hO act L g) = χA :=
    AlgHom.ext fun b ↦ hg b
  ext c
  obtain ⟨y, rfl⟩ := e.surjective c
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.mem_comap, ← specialFibreEquiv0_algMap hϖ hker ha0 ha1 hO (act g) L L b, hmem, hmem]
  exact Ideal.ext_iff.1 (hfix _ hgA) b

end Datum

end

end P1Three

end SemistableReduction
