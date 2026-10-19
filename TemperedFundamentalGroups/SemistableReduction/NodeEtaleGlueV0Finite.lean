/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0

/-!
# Finiteness of the chart modules of the glued two-chart rings (Blueprint §12.8, M2.3 (f))

For `V : NodeEtaleGlue.Overlap I`, the chart modules of the two-chart rings `V.twoChart n` are
finite over `O[X]` (the finiteness hypotheses `hfin0`, `hfin1` of `TwoChartTower.systemShift`):

* generic: `AwaySpan.Gen a M` (`M` is generated over `S[1/a]` by finitely many elements),
  `AwaySpan.finite_of_gen`, `AwaySpan.gen_of_finite` (a finite module over a ring `R` whose
  elements are fractions `s / aᵏ`), `AwaySpan.gen_of_surjective`, `AwaySpan.finite_aeval_of_finite`
  (transitivity over `O[X]`), **`ZariskiTwo.finite_glued_of_gen`**;
* `Overlap.finite_Y`: `Y n` is finite over `B0`; `Overlap.finite_R0`: `R0 n` is finite over `B0'`;
* **`Overlap.finite1`**, **`Overlap.finite0`**: the chart modules are finite over `O[X]`.
-/

universe u

open Polynomial

namespace SemistableReduction

noncomputable section

namespace AwaySpan

variable {S : Type u} [CommRing S] (a : S) (M : Type u) [AddCommGroup M] [Module S M]

/-- `M` is generated over `S[1/a]` by finitely many elements. -/
def Gen : Prop := ∃ s : Finset M, ∀ m : M, ∃ k : ℕ, a ^ k • m ∈ Submodule.span S (s : Set M)

variable {a M}

/-- A module over `S[1/a]` generated over `S[1/a]` by finitely many elements is finite. -/
lemma finite_of_gen [Module (Localization.Away a) M] [IsScalarTower S (Localization.Away a) M]
    (h : Gen a M) : Module.Finite (Localization.Away a) M := by
  obtain ⟨s, hs⟩ := h
  refine ⟨⟨s, eq_top_iff.mpr fun m _ ↦ ?_⟩⟩
  obtain ⟨k, hk⟩ := hs m
  have h1 : a ^ k • m ∈ Submodule.span (Localization.Away a) (s : Set M) :=
    Submodule.span_le_restrictScalars S _ _ hk
  have hu : IsUnit (algebraMap S (Localization.Away a) (a ^ k)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit a).pow k
  obtain ⟨u, hu⟩ := hu
  have e : m = (↑u⁻¹ : Localization.Away a) • a ^ k • m := by
    rw [← algebraMap_smul (Localization.Away a) (a ^ k) m, smul_smul, ← hu, Units.inv_mul,
      one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ h1

/-- A finite module over a ring `R` whose elements are fractions `s / aᵏ` (`s ∈ S`). -/
lemma gen_of_finite {R : Type u} [CommRing R] [Algebra S R] [Module R M] [IsScalarTower S R M]
    (hR : ∀ r : R, ∃ (k : ℕ) (s : S), algebraMap S R a ^ k * r = algebraMap S R s)
    [Module.Finite R M] : Gen a M := by
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R) (M := M)
  let P : Submodule R M :=
    { carrier := {m | ∃ k : ℕ, a ^ k • m ∈ Submodule.span S (t : Set M)}
      add_mem' := by
        rintro x y ⟨k, hk⟩ ⟨l, hl⟩
        refine ⟨k + l, ?_⟩
        have e1 : a ^ (k + l) • x = a ^ l • a ^ k • x := by rw [pow_add, mul_comm, mul_smul]
        have e2 : a ^ (k + l) • y = a ^ k • a ^ l • y := by rw [pow_add, mul_smul]
        rw [smul_add, e1, e2]
        exact add_mem (Submodule.smul_mem _ _ hk) (Submodule.smul_mem _ _ hl)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r x ⟨k, hk⟩
        obtain ⟨j, s, hs⟩ := hR r
        refine ⟨j + k, ?_⟩
        have e : a ^ (j + k) • r • x = s • a ^ k • x := by
          rw [pow_add, mul_comm, mul_smul, ← smul_assoc (a ^ j) r x, Algebra.smul_def, map_pow,
            hs, algebraMap_smul]
          exact smul_comm _ _ _
        change a ^ (j + k) • r • x ∈ _
        rw [e]
        exact Submodule.smul_mem _ _ hk }
  have hP : (⊤ : Submodule R M) ≤ P := by
    rw [← ht, Submodule.span_le]
    intro x hx
    exact ⟨0, by simpa using Submodule.subset_span hx⟩
  exact ⟨t, fun m ↦ hP Submodule.mem_top⟩

/-- Generation over `S[1/a]` from generation over a quotient `B` of `S`. -/
lemma gen_of_surjective {B : Type u} [CommRing B] [Algebra S B] [Module B M]
    [IsScalarTower S B M] (hsurj : Function.Surjective (algebraMap S B))
    (h : ∃ s : Finset M, ∀ m : M, ∃ k : ℕ,
      algebraMap S B a ^ k • m ∈ Submodule.span B (s : Set M)) : Gen a M := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun m ↦ ?_⟩
  obtain ⟨k, hk⟩ := hs m
  refine ⟨k, ?_⟩
  rw [← map_pow, algebraMap_smul] at hk
  rw [← Submodule.restrictScalars_span S B hsurj]
  exact hk

/-- **Transitivity over `O[X]`**: if `S` is finite over `O[X]` via `X ↦ x` and `T` is finite over
`S`, then `T` is finite over `O[X]` via `X ↦ x`. -/
lemma finite_aeval_of_finite {O S T : Type u} [CommRing O] [CommRing S] [CommRing T]
    [Algebra O S] [Algebra O T] [Algebra S T] [IsScalarTower O S T] (x : S)
    (hS : letI := (Polynomial.aeval x : O[X] →ₐ[O] S).toRingHom.toAlgebra; Module.Finite O[X] S)
    [Module.Finite S T] :
    letI := (Polynomial.aeval (algebraMap S T x) : O[X] →ₐ[O] T).toRingHom.toAlgebra
    Module.Finite O[X] T := by
  letI := (Polynomial.aeval x : O[X] →ₐ[O] S).toRingHom.toAlgebra
  letI := (Polynomial.aeval (algebraMap S T x) : O[X] →ₐ[O] T).toRingHom.toAlgebra
  haveI : IsScalarTower O[X] S T :=
    IsScalarTower.of_algebraMap_eq fun p ↦ Polynomial.aeval_algebraMap_apply T x p
  exact Module.Finite.trans S T

end AwaySpan

section Glued

open ZariskiTwo

variable {R : Type u} [CommRing R] (a b : R)
  {Ba Bb Bab : Type u} [CommRing Ba] [CommRing Bb] [CommRing Bab]
  [Algebra R Ba] [Algebra R Bb] [Algebra R Bab]
  {ρa : Ba →ₐ[R] Bab} {ρb : Bb →ₐ[R] Bab}

/-- **Finiteness of the glued algebra** if `a, b` generate the unit ideal, are units on the pieces
and the pieces are finitely generated over `R[1/a]`, `R[1/b]` (`finite_glued`). -/
theorem _root_.ZariskiTwo.finite_glued_of_gen (hab : Ideal.span {a, b} = ⊤)
    [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
    [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap]
    (ha : IsUnit (algebraMap R Ba a)) (hb : IsUnit (algebraMap R Bb b))
    (hBa : AwaySpan.Gen a Ba) (hBb : AwaySpan.Gen b Bb) :
    Module.Finite R (glued ρa ρb) := by
  letI : Algebra (Localization.Away a) Ba :=
    (IsLocalization.Away.lift a (S := Localization.Away a) ha).toAlgebra
  haveI : IsScalarTower R (Localization.Away a) Ba :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (IsLocalization.Away.lift_eq a ha r).symm
  letI : Algebra (Localization.Away b) Bb :=
    (IsLocalization.Away.lift b (S := Localization.Away b) hb).toAlgebra
  haveI : IsScalarTower R (Localization.Away b) Bb :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (IsLocalization.Away.lift_eq b hb r).symm
  exact finite_glued a b hab (AwaySpan.finite_of_gen hBa) (AwaySpan.finite_of_gen hBb)

end Glued

open KummerEtale AdmissibleLift LevelTower

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}

namespace Overlap

variable {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (m : ℕ)

include V hO in
/-- **`Y n` is finite over the chart `B0`.** -/
theorem finite_Y : Module.Finite I.B0 (I.Y hθ m) := by
  letI := alg0G I.T hθ I.B I.B0 m
  letI := alg0 I.B I.B0 m (I.E m)
  letI := alg0 I.B I.B0 m (EtaleOverlap.Bab (I.a m) (I.E m))
  haveI := locFst I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv
    I.hJB I.B0 (fun _ ↦ rfl) m
  haveI := locSnd I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
    I.hdiv I.hbb I.hJB I.B0 (fun _ ↦ rfl) m
  refine ZariskiTwo.finite_glued_of_gen I.a0 I.b0 I.hab
    (isUnit_a0 I.T hθ I.B I.a I.B0 (fun _ ↦ rfl) m) (I.hbE m) ?_ ?_
  · letI : Algebra I.B0 (I.R m) := alg0 I.B I.B0 m (I.R m)
    haveI : IsScalarTower I.B0 (I.R m) (I.T.G hθ m) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    haveI := (I.T.spec hθ hO m).1
    refine AwaySpan.gen_of_finite (R := I.R m) fun r ↦ ?_
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap I.B0 (I.B m) I.a0)) r
    obtain ⟨s, rfl⟩ := V.surjB m b
    refine ⟨k, s, ?_⟩
    change (algebraMap (I.B m) (I.R m) (algebraMap I.B0 (I.B m) I.a0)) ^ k * r =
      algebraMap (I.B m) (I.R m) (algebraMap I.B0 (I.B m) s)
    rw [← map_pow, mul_comm]
    exact hb
  · haveI : IsScalarTower I.B0 (I.B m) (I.E m) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact AwaySpan.gen_of_surjective (V.surjB m) (V.hfinE m)

include hO in
/-- `Q n = Y n[1/x₁]` is finite over the overlap `W0 = B0[1/x₁]`. -/
theorem finite_Q : letI := V.algW0Q hθ m; Module.Finite V.W0 (V.Q hθ m) := by
  letI := V.algW0Q hθ m
  haveI := V.hW0
  haveI := V.finite_Y hθ hO m
  haveI : IsScalarTower I.B0 V.W0 (V.Q hθ m) :=
    IsScalarTower.of_algebraMap_eq fun b ↦ (V.algW0Q_algebraMap hθ m b).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (I.Y hθ m) (Submonoid.powers V.x1))
      (V.Q hθ m) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact Localization.isLocalization
  exact Module.Finite.of_isLocalization I.B0 (I.Y hθ m) (Submonoid.powers V.x1)

include hO in
/-- `Q n` is finitely generated over `B0'[1/x₀]`. -/
theorem gen_Q : letI := V.alg0'Q hθ m; AwaySpan.Gen V.x0 (V.Q hθ m) := by
  letI := V.algW0Q hθ m
  letI := V.alg0'Q hθ m
  haveI := V.hW0'
  haveI := V.finite_Q hθ hO m
  haveI : IsScalarTower V.B0' V.W0 (V.Q hθ m) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine AwaySpan.gen_of_finite (R := V.W0) fun w ↦ ?_
  obtain ⟨⟨s, ⟨_, k, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers V.x0) w
  refine ⟨k, s, ?_⟩
  rw [← map_pow, mul_comm]
  exact hs

include hO in
/-- **`R0 n = Q n ×_{M n} P0 n` is finite over the chart `B0'`.** -/
theorem finite_R0 : letI := V.alg0'Q hθ m; letI := V.alg0'E m; letI := V.alg0'M m
    Module.Finite V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO m) (V.ρ0b m)) := by
  letI := V.alg0'Q hθ m
  letI := V.alg0'E m
  letI := V.alg0'M m
  have hx : IsUnit (algebraMap V.B0' (V.Q hθ m) V.x0) := IsUnit.of_mul_eq_one _ (V.hxy hθ m)
  haveI := ZariskiTwo.isLocalizedModule_fst V.x0 (ρa := V.ρ0a hθ hO m) hx (V.isLocalization_ρ0b m)
  haveI := ZariskiTwo.isLocalizedModule_snd V.c0 (ρb := V.ρ0b m) (V.P0.hcP m)
    (V.isLocalization_ρ0a' hθ hO m)
  haveI : IsScalarTower V.B0' (V.B' m) (V.P0.P m) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact ZariskiTwo.finite_glued_of_gen V.x0 V.c0 V.hxc hx (V.P0.hcP m) (V.gen_Q hθ hO m)
    (AwaySpan.gen_of_surjective (V.surjB' m) (V.P0.hfinP m))

include hO in
/-- **The chart module of `twoChart` on `U₁` is finite over `O[X]`.** -/
theorem finite1 : Module.Finite (Polynomial O)
    (Module.AEval' (V.twoChart hθ hO m).chartModule.x1) := by
  letI := V.algOB0
  letI := V.algOY hθ m
  haveI : IsScalarTower O I.B0 (I.Y hθ m) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := V.finite_Y hθ hO m
  exact TwoChartGlue.finite_aeval_mulLeft (A := O) (algebraMap I.B0 (I.Y hθ m) V.x1)
    (AwaySpan.finite_aeval_of_finite V.x1 V.finB0)

/-- **The chart module of `twoChart` on `U₀` is finite over `O[X]`.** -/
theorem finite0 : Module.Finite (Polynomial O)
    (Module.AEval' (V.twoChart hθ hO m).chartModule.x0) := by
  letI := V.alg0'Q hθ m
  letI := V.algOQ hθ m
  haveI := V.towerOQ hθ m
  letI := V.alg0'E m
  haveI := V.towerOE m
  letI := V.alg0'M m
  haveI := V.towerOM m
  haveI := V.finite_R0 hθ hO m
  exact TwoChartGlue.finite_aeval_mulLeft (A := O)
    (algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO m) (V.ρ0b m)) V.x0)
    (AwaySpan.finite_aeval_of_finite V.x0 V.finB0')

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
