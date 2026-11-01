/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormAlgebraization

/-!
# Hypotheses of `Overlap.exists_iso_of_levels` from generators and witnesses (MR12 T2 S6, G5)

* `ker_mk_map`: the kernel of `B → B/(I·A)·B` is `I·B`;
* **`NodeEtaleGlue.Overlap.hρ_of_fst`**: the compatibility hypothesis `hρ` of `Overlap.βOf` from
  the first components of the identifications `e0 n` (e.g. `φQn_mul_pow` for `levelEquiv0X`);
* **`NodeEtaleGlue.Overlap.hω2_of_mk`**: common witnesses of `ωn'`, `ωn` (the hypothesis of
  `Overlap.f0_levelEquiv0X`) from witnesses on generators;
* **`NodeEtaleGlue.Overlap.exists_iso_of_levels'`**: `exists_iso_of_levels` for an algebraization
  of a system `S` equal to `V.system` (an equation at the top level, for named abbreviations).
-/

universe u

open Polynomial

namespace SemistableReduction

open ProjectiveLine ProjectiveLine.ChartModule

noncomputable section

/-- The kernel of `B → B/(I·A)·B` is `I·B`. -/
lemma ker_mk_map {O A B : Type u} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra A B] (I : Ideal O) :
    RingHom.ker (Ideal.Quotient.mk ((I.map (algebraMap O A)).map (algebraMap A B))) =
      I.map ((algebraMap A B).comp (algebraMap O A)) := by
  rw [Ideal.mk_ker, Ideal.map_map]

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (P : TwoChartRings O)

section Charts

variable {X1 : ℕ → Type u} [∀ n, CommRing (X1 n)] [∀ n, Algebra I.B0 (X1 n)]
  {μ1 : ∀ n, X1 (n + 1) →+* X1 n} (e1 : I.LevelEquivFam hθ hO X1 μ1)
  (q1 : ∀ n, P.R1 →+* X1 n)
  (hq1O : ∀ n o, q1 n (algebraMap O P.R1 o) =
    algebraMap I.B0 (X1 n) (letI := V.algOB0; algebraMap O I.B0 o))

variable {X0 : ℕ → Type u} [∀ n, CommRing (X0 n)] [∀ n, Algebra V.B0' (X0 n)]
  (e0 : ∀ n, letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    X0 n ≃ₐ[V.B0'] ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n))
  (q0 : ∀ n, P.R0 →+* X0 n)
  (hq0O : ∀ n o, q0 n (algebraMap O P.R0 o) = algebraMap V.B0' (X0 n) (algebraMap O V.B0' o))

/-- **The hypothesis `hρ` of `βOf` from the first components of `e0`**: if
`ρ0 a · ρ1(y)ᵏ = ρ1 m` in `P` implies `fst (e0 (q0 a)) · x₁ᵏ = e1 (q1 m)` in `Q n`. -/
theorem hρ_of_fst (H : ∀ n a m (k : ℕ), P.ρ0 a * P.ρ1 P.y ^ k = P.ρ1 m →
    letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    ZariskiTwo.fst (V.ρ0a hθ hO n) (V.ρ0b n) (e0 n (q0 n a)) *
        algebraMap I.B0 (V.Q hθ n) V.x1 ^ k =
      algebraMap (I.Y hθ n) (V.Q hθ n) (e1.equiv n (q1 n m))) (n : ℕ) (a : P.R0) (m : P.R1)
    (k : ℕ) (h : P.ρ0 a * P.ρ1 P.y ^ k = P.ρ1 m) :
    (V.twoChart hθ hO n).ρ0 (V.f0Of hθ hO P e0 q0 hq0O n a) *
        (V.twoChart hθ hO n).ρ1 (V.twoChart hθ hO n).y ^ k =
      (V.twoChart hθ hO n).ρ1 (V.f1Of hθ hO P e1 q1 hq1O n m) := by
  have e := H n a m k h
  rw [IsScalarTower.algebraMap_apply I.B0 (I.Y hθ n) (V.Q hθ n)] at e
  exact e

variable (hx : ∀ n, q0 n P.x = algebraMap V.B0' (X0 n) V.x0)
  (hy : ∀ n, q1 n P.y = algebraMap I.B0 (X1 n) V.x1)

variable (hρ : ∀ n a m (k : ℕ), P.ρ0 a * P.ρ1 P.y ^ k = P.ρ1 m →
    (V.twoChart hθ hO n).ρ0 (V.f0Of hθ hO P e0 q0 hq0O n a) *
        (V.twoChart hθ hO n).ρ1 (V.twoChart hθ hO n).y ^ k =
      (V.twoChart hθ hO n).ρ1 (V.f1Of hθ hO P e1 q1 hq1O n m))
  {μ0 : ∀ n, X0 (n + 1) →+* X0 n}
  (he0 : ∀ n x, V.f0 hθ hO n (e0 (n + 1) x) = e0 n (μ0 n x))
  (hμ0 : ∀ n r, μ0 n (q0 (n + 1) r) = q0 n r) (hμ1 : ∀ n r, μ1 n (q1 (n + 1) r) = q1 n r)

include e1 hq1O hq0O hx hy hρ he0 hμ0 hμ1 in
/-- **`exists_iso_of_levels` for an algebraization of a system `S = V.system`.** -/
theorem exists_iso_of_levels' [IsNoetherianRing O] [IsAdicComplete (Ideal.span {V.ϖ}) O]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
    (hs0 : ∀ n, Function.Surjective (q0 n)) (hs1 : ∀ n, Function.Surjective (q1 n))
    (hk0 : ∀ n, RingHom.ker (q0 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R0))
    (hk1 : ∀ n, RingHom.ker (q1 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R1))
    {S : AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ hO = S)
    {N : ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)]
    {α : ∀ n, Hom N (S.M n)} {B : AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m)
    (hB : ∀ n, B.IsHom (S.alg n) (α n)) :
    ∃ (γ : Hom P.chartModule N) (δ : Hom N P.chartModule), γ.comp δ = Hom.id N ∧
      δ.comp γ = Hom.id P.chartModule ∧ P.algStr.IsHom B γ ∧ B.IsHom P.algStr δ := by
  subst hS
  obtain ⟨γ, δ, h1, h2, -, -, h3, h4⟩ := V.exists_iso_of_levels hθ hO P e1 q1 hq1O e0 q0 hq0O hx hy
    hρ he0 hμ0 hμ1 hs0 hs1 hk0 hk1 hα hαc hB
  exact ⟨γ, δ, h1, h2, h3, h4⟩

end Charts

section Witness

variable {X1 X0 X1' X0' : Type u} [CommRing X1] [Algebra I.B0 X1] [CommRing X0] [Algebra V.B0' X0]
  [CommRing X1'] [Algebra I.B0 X1'] [CommRing X0'] [Algebra V.B0' X0']
  (ωn : haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0) V.x0
    letI := awayAlg (W := V.W0) (C := X1) V.x1
    Localization.Away (algebraMap V.B0' X0 V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 X1 V.x1))
  (ωn' : haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0') V.x0
    letI := awayAlg (W := V.W0) (C := X1') V.x1
    Localization.Away (algebraMap V.B0' X0' V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 X1' V.x1))
  (μ1 : X1' →+* X1) (μ0 : X0' →+* X0)

/-- **Common witnesses of `ωn'`, `ωn` from generators** (the hypothesis `hω2` of
`f0_levelEquiv0X`). -/
theorem hω2_of_mk {Z Z1 : Type u} (q0 : Z → X0') (hq0 : Function.Surjective q0) (q1 : Z1 → X1')
    (H : ∀ b : Z, ∃ (y : Z1) (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0') V.x0
        letI := awayAlg (W := V.W0) (C := X1') V.x1
        ωn' (algebraMap X0' _ (q0 b)) *
          algebraMap X1' (Localization.Away (algebraMap I.B0 X1' V.x1))
            (algebraMap I.B0 X1' V.x1) ^ k = algebraMap X1' _ (q1 y)) ∧
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0) V.x0
        letI := awayAlg (W := V.W0) (C := X1) V.x1
        ωn (algebraMap X0 _ (μ0 (q0 b))) *
          algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1))
            (algebraMap I.B0 X1 V.x1) ^ k = algebraMap X1 _ (μ1 (q1 y)))) :
    ∀ x : X0', ∃ (y : X1') (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0') V.x0
        letI := awayAlg (W := V.W0) (C := X1') V.x1
        ωn' (algebraMap X0' _ x) *
          algebraMap X1' (Localization.Away (algebraMap I.B0 X1' V.x1))
            (algebraMap I.B0 X1' V.x1) ^ k = algebraMap X1' _ y) ∧
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0) V.x0
        letI := awayAlg (W := V.W0) (C := X1) V.x1
        ωn (algebraMap X0 _ (μ0 x)) *
          algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1))
            (algebraMap I.B0 X1 V.x1) ^ k = algebraMap X1 _ (μ1 y)) := by
  intro x
  obtain ⟨b, rfl⟩ := hq0 x
  obtain ⟨y, k, h⟩ := H b
  exact ⟨q1 y, k, h⟩

end Witness

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
