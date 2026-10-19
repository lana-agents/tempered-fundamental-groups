/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.PowFlatGlue
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0

/-!
# `ϖ`-purity of the two-chart rings of the glued coverings (Blueprint §12.8, M2.4, step 3f)

For `V : NodeEtaleGlue.Overlap I` (a domain `O`, `ϖ = V.ϖ ≠ 0`, nonzero deformation parameters,
`I.T.I n = (ϖⁿ⁺¹)`), from `PowFlat ϖ (n+1)` of the base chart level `I.B n` (Noetherian) and of
the piece `V.P0.P n` over `D(c₀)`:

* `PowFlat.overlap_Y` (`Y n` over `O` via `algOY`), `overlap_Q` (`Q n = Y n[1/x₁]`),
  `overlap_R0` (`Q n ×_{M n} P0 n`, glued along `D(x₀) ∪ D(c₀)`);
* **`PowFlat.twoChart_R0`, `twoChart_R1`, `twoChart_R01`**: the rings of `V.twoChart n`.
-/

universe u

namespace SemistableReduction

namespace PowFlat

open NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

/-- `ϖⁿ⁺¹ = 0` on the base chart levels. -/
lemma overlap_hw : algebraMap O (I.B n) V.ϖ ^ (n + 1) = 0 := by
  have h := V.killB n
  rw [Ideal.map_eq_bot_iff_le_ker] at h
  rw [← map_pow]
  exact h (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)

include hO in
/-- **The covering over the first chart** at level `n` (`Y n` over `O` through `B0`). -/
theorem overlap_Y [IsDomain O] [IsNoetherianRing (I.B n)] (hπ : ∀ j, πL j ≠ 0) (hϖ : V.ϖ ≠ 0)
    (hB : PowFlat V.ϖ (n + 1) (I.B n)) (hI : I.T.I n = Ideal.span {V.ϖ ^ (n + 1)}) :
    @PowFlat O _ V.ϖ (n + 1) (I.Y hθ n) _ (V.algOY hθ n).toModule := by
  letI := V.algOB0
  have h := input_Y I hθ hO hB (overlap_hw V n) hπ hϖ hI (V.hfinE n) (w := algebraMap O I.B0 V.ϖ)
    (V.hOB0B n V.ϖ)
  exact @of_addEquiv (n + 1) O _ V.ϖ (I.Y hθ n) _ (V.algOY hθ n).toModule I.B0 _ _ (I.Y hθ n) _
    Algebra.toModule (AddEquiv.refl _) (fun _ ↦ rfl) h

include hO in
/-- **The covering over the overlap** `Q n = Y n[1/x₁]` at level `n` (over `O` through `B0'`). -/
theorem overlap_Q [IsDomain O] [IsNoetherianRing (I.B n)] (hπ : ∀ j, πL j ≠ 0) (hϖ : V.ϖ ≠ 0)
    (hB : PowFlat V.ϖ (n + 1) (I.B n)) (hI : I.T.I n = Ideal.span {V.ϖ ^ (n + 1)}) :
    letI := V.algOQ hθ n
    PowFlat V.ϖ (n + 1) (V.Q hθ n) := by
  letI := V.algOB0
  have h := input_Y I hθ hO hB (overlap_hw V n) hπ hϖ hI (V.hfinE n) (w := algebraMap O I.B0 V.ϖ)
    (V.hOB0B n V.ϖ)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (I.Y hθ n) (Submonoid.powers V.x1))
      (V.Q hθ n) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  have hQ : PowFlat (algebraMap O I.B0 V.ϖ) (n + 1) (V.Q hθ n) :=
    localization h (Submonoid.powers V.x1)
  letI := V.algOQ hθ n
  refine of_addEquiv (AddEquiv.refl _) (fun q ↦ ?_) hQ
  letI := V.algW0Q hθ n
  rw [AddEquiv.refl_apply, AddEquiv.refl_apply, Algebra.smul_def, Algebra.smul_def]
  congr 1
  change algebraMap V.W0 (V.Q hθ n) (algebraMap V.B0' V.W0 (algebraMap O V.B0' V.ϖ)) = _
  rw [← IsScalarTower.algebraMap_apply O V.B0' V.W0, IsScalarTower.algebraMap_apply O I.B0 V.W0,
    V.algW0Q_algebraMap hθ n]

include hO in
/-- **The covering over the second chart** at level `n`: `R0 n = Q n ×_{M n} P0 n` (as a
`B0'`-module), glued along `D(x₀) ∪ D(c₀)`. -/
theorem overlap_R0 [IsDomain O] [IsNoetherianRing (I.B n)] (hπ : ∀ j, πL j ≠ 0) (hϖ : V.ϖ ≠ 0)
    (hB : PowFlat V.ϖ (n + 1) (I.B n)) (hI : I.T.I n = Ideal.span {V.ϖ ^ (n + 1)})
    (hP0 : PowFlat V.ϖ (n + 1) (V.P0.P n)) :
    letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    PowFlat (algebraMap O V.B0' V.ϖ) (n + 1)
      (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) := by
  have hQ := overlap_Q V hθ hO n hπ hϖ hB hI
  letI := V.alg0'Q hθ n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  letI := V.alg0'E n
  haveI := V.towerOE n
  letI := V.alg0'M n
  refine glued V.x0 V.c0 V.hxc (IsUnit.of_mul_eq_one _ (V.hxy hθ n)) (V.isLocalization_ρ0b n)
    (V.P0.hcP n) (V.isLocalization_ρ0a' hθ hO n) (algebraMap_of hQ) (algebraMap_of hP0)

include hO in
/-- **The chart rings of the covering at level `n`** (`Overlap.twoChart`): the sections `R0`
over the chart `U₀` are `PowFlat ϖ (n+1)`. -/
theorem twoChart_R0 [IsDomain O] [IsNoetherianRing (I.B n)] (hπ : ∀ j, πL j ≠ 0) (hϖ : V.ϖ ≠ 0)
    (hB : PowFlat V.ϖ (n + 1) (I.B n)) (hI : I.T.I n = Ideal.span {V.ϖ ^ (n + 1)})
    (hP0 : PowFlat V.ϖ (n + 1) (V.P0.P n)) :
    PowFlat V.ϖ (n + 1) (V.twoChart hθ hO n).R0 := by
  have h := overlap_R0 V hθ hO n hπ hϖ hB hI hP0
  letI := V.alg0'Q hθ n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  letI := V.alg0'E n
  haveI := V.towerOE n
  letI := V.alg0'M n
  haveI := V.towerOM n
  have h2 : PowFlat V.ϖ (n + 1) (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) :=
    of_algebraMap (R := V.B0') h
  exact h2

include hO in
/-- **The chart rings of the covering at level `n`**: the sections `R1 = Y n` over `U₁`. -/
theorem twoChart_R1 [IsDomain O] [IsNoetherianRing (I.B n)] (hπ : ∀ j, πL j ≠ 0) (hϖ : V.ϖ ≠ 0)
    (hB : PowFlat V.ϖ (n + 1) (I.B n)) (hI : I.T.I n = Ideal.span {V.ϖ ^ (n + 1)}) :
    PowFlat V.ϖ (n + 1) (V.twoChart hθ hO n).R1 :=
  overlap_Y V hθ hO n hπ hϖ hB hI

include hO in
/-- **The chart rings of the covering at level `n`**: the sections `R01 = Q n` over the
overlap. -/
theorem twoChart_R01 [IsDomain O] [IsNoetherianRing (I.B n)] (hπ : ∀ j, πL j ≠ 0)
    (hϖ : V.ϖ ≠ 0) (hB : PowFlat V.ϖ (n + 1) (I.B n))
    (hI : I.T.I n = Ideal.span {V.ϖ ^ (n + 1)}) :
    PowFlat V.ϖ (n + 1) (V.twoChart hθ hO n).R01 :=
  overlap_Q V hθ hO n hπ hϖ hB hI

end PowFlat

end SemistableReduction
