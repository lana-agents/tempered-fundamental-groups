/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleTower
import TemperedFundamentalGroups.SemistableReduction.TateTwoChart

/-!
# The étale piece of the Tate coverings over `D(1 + h) ⊆ V₀` (Blueprint §12.8, M2.3 (f))

The chart `V₀ = Spec T0` of the Tate model over `U₀` is covered by `D(h) ⊆ V₁` and `D(1 + h)`;
the latter contains `V₀ ∖ V₁ = {u = 0}` and misses the node `q = (h = −1, z = 0)`. For a covering
étale outside the nodes, the piece over `D(1 + h)` is an étale lift of the special-fibre covering:

* `EtaleTower.Special θ T b`: a special-fibre covering of a chart `T`, finite over `T/J` and étale
  over `D(b̄)`, with `EtaleTower.Special.lift` (the lifts `EtaleTower.lift` at all levels),
  `succ` (the successor maps), **`surjective_succ'`**, **`ker_succ'`** (kernel `ϖⁿ⁺¹`);
* **`TateGlue0.Special0`**: the special-fibre covering over `V₀`, finite over `T0/J`, étale over
  `D(1 + h̄)` (scope: étale outside the nodes; a covering ramified at the cusp `[0:1:0]` needs a
  formal cusp patch instead);
* **`TateGlue0.E0 n`**: its étale lifts over `D(1 + h)` at level `n`, with successor maps
  `TateGlue0.sE0 n` (surjective, kernel `ϖⁿ⁺¹ E0 (n+1)`).

The comparison with the covering over `V₁` on the overlap is `TateGlue0Overlap` (to do).
-/

universe u

namespace SemistableReduction

namespace EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k) {ϖ : O}
  (T : Type u) [CommRing T] [Algebra O T] (b : T)

/-- **A special-fibre covering of the chart `T`, étale over `D(b̄)`**: a finite `T/J`-algebra
`C` whose localization away from `b̄` is étale. -/
structure Special where
  C : Type u
  [commRing : CommRing C]
  [algebra : Algebra (Ts θ T) C]
  finite : Module.Finite (Ts θ T) C
  etale : (Localization.awayMap (algebraMap (Ts θ T) C) (Ideal.Quotient.mk _ b)).Etale

attribute [instance] Special.commRing Special.algebra

namespace Special

variable {θ T b} (S : Special θ T b) (hϖ : θ ϖ = 0) [IsNoetherianRing T]
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ})

/-- **The étale lifts of a special-fibre covering** (`EtaleTower.lift`). -/
def lift (n : ℕ) : Lift T hϖ S.C b n :=
  haveI := S.finite
  EtaleTower.lift T hϖ S.C b hker S.etale n

/-- The successor maps of the lifts. -/
def succ (n : ℕ) : (S.lift hϖ hker (n + 1)).E →+* (S.lift hϖ hker n).E :=
  letI := algE T hϖ S.C b (S.lift hϖ hker n)
  (EtaleTower.succ T hϖ S.C b hker (S.lift hϖ hker (n + 1)) (S.lift hϖ hker n) :
    (S.lift hϖ hker (n + 1)).E →+* _)

lemma succ_algebraMap (n : ℕ) (x : Tn ϖ T (n + 1)) :
    S.succ hϖ hker n (algebraMap _ (S.lift hϖ hker (n + 1)).E x) =
      algebraMap (Tn ϖ T n) _ (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n) x) :=
  letI := algE T hϖ S.C b (S.lift hϖ hker n)
  (EtaleTower.succ T hϖ S.C b hker (S.lift hϖ hker (n + 1)) (S.lift hϖ hker n)).commutes x

lemma σ_succ' (n : ℕ) (x : (S.lift hϖ hker (n + 1)).E) :
    (letI := algC T hϖ S.C n;
      (S.lift hϖ hker n).σ (Ideal.Quotient.mk _ (S.succ hϖ hker n x))) =
      (letI := algC T hϖ S.C (n + 1);
        (S.lift hϖ hker (n + 1)).σ (Ideal.Quotient.mk _ x)) :=
  EtaleTower.σ_succ T hϖ S.C b hker _ _ x

/-- The successor maps are surjective. -/
theorem surjective_succ' (n : ℕ) : Function.Surjective (S.succ hϖ hker n) := by
  letI := algE T hϖ S.C b (S.lift hϖ hker n)
  exact EtaleTower.surjective_succ T hϖ S.C b hker _ _

/-- **The kernel of the successor map is `ϖⁿ⁺¹ E (n+1)`.** -/
theorem ker_succ' (n : ℕ) : RingHom.ker (S.succ hϖ hker n) =
    ((Iv ϖ n).map (algebraMap O T)).map
      ((algebraMap (Tn ϖ T (n + 1)) (S.lift hϖ hker (n + 1)).E).comp
        (algebraMap T (Tn ϖ T (n + 1)))) :=
  ker_succ_base T hϖ S.C b hker _ _

end Special

end

end EtaleTower

namespace TateGlue0

open TateTwoChart

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k) (ϖ π b₄ t κ : O)

/-- The special fibre `T0/J` of the chart over `U₀`. -/
abbrev T0s : Type u := EtaleTower.Ts θ (T0 π b₄ t κ)

/-- The level charts over `U₀`. -/
abbrev B (n : ℕ) : Type u := EtaleTower.Tn ϖ (T0 π b₄ t κ) n

/-- The basic open `D(1 + h)` of `V₀`. -/
abbrev c0 : T0 π b₄ t κ := 1 + h0 π b₄ t κ

/-- **The special-fibre covering over `V₀`**, finite over `T0/J` and étale over `D(1 + h̄)`
(scope: coverings étale outside the nodes, see the module docstring). -/
abbrev Special0 : Type (u + 1) := EtaleTower.Special θ (T0 π b₄ t κ) (c0 π b₄ t κ)

variable [IsNoetherianRing O]

instance isNoetherianRing_T0 : IsNoetherianRing (T0 π b₄ t κ) :=
  Ideal.Quotient.isNoetherianRing _

variable {θ ϖ π b₄ t κ} (Sp0 : Special0 θ π b₄ t κ) (hϖ : θ ϖ = 0)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ})

/-- **The étale lifts over `D(1 + h)`** at level `n`. -/
abbrev E0 (n : ℕ) : EtaleTower.Lift (T0 π b₄ t κ) hϖ Sp0.C (c0 π b₄ t κ) n :=
  Sp0.lift hϖ hker n

/-- The successor maps `E0 (n+1) → E0 n`. -/
abbrev sE0 (n : ℕ) : (E0 Sp0 hϖ hker (n + 1)).E →+* (E0 Sp0 hϖ hker n).E := Sp0.succ hϖ hker n

/-- The successor maps are surjective. -/
theorem surjective_sE0 (n : ℕ) : Function.Surjective (sE0 Sp0 hϖ hker n) :=
  Sp0.surjective_succ' hϖ hker n

/-- **The kernel of `E0 (n+1) → E0 n` is `ϖⁿ⁺¹ E0 (n+1)`.** -/
theorem ker_sE0 (n : ℕ) : RingHom.ker (sE0 Sp0 hϖ hker n) =
    ((EtaleTower.Iv ϖ n).map (algebraMap O (T0 π b₄ t κ))).map
      ((algebraMap (B ϖ π b₄ t κ (n + 1)) (E0 Sp0 hϖ hker (n + 1)).E).comp
        (algebraMap (T0 π b₄ t κ) (B ϖ π b₄ t κ (n + 1)))) :=
  Sp0.ker_succ' hϖ hker n

end

end TateGlue0

end SemistableReduction
