/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelTowerMk
import TemperedFundamentalGroups.SemistableReduction.TowerSystem

/-!
# The inverse system of patched algebras (Blueprint §12.8, M2.3 → M2.4)

For tower data `T : LevelTower.Data R cov₀ πL` whose level charts satisfy
`ker (R (n+1) → R n) = I^{n+1} R (n+1)` and `I^{n+1} R n = 0` for an ideal `I` of `O`
(Tate case: `I = (ϖ)`, `R n = R̄/ϖⁿ⁺¹R̄`):

* `LevelTower.Data.aG n : O → G n`, compatible with the transition maps (`tr_comp_aG`);
* **`LevelTower.Data.trLe h : G n →+* G m`** for `m ≤ n` (`TowerSystem.trLe`), with `trLe_comp`,
  **`surjective_trLe`** and **`ker_trLe`**: the kernel is `I^{m+1} G n` — the transition maps of an
  adic system (up to the index shift `n ↦ n + 1`).
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift

noncomputable section

namespace LevelTower.Data

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (T : Data (θ := θ) R cov₀ πL) (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- The structure map `O → G n`. -/
abbrev aG (n : ℕ) : O →+* T.G hθ n :=
  (algebraMap (R n) (T.G hθ n)).comp (algebraMap O (R n))

lemma tr_comp_aG (n : ℕ) : (T.tr hθ hO n).comp (T.aG hθ (n + 1)) = T.aG hθ n :=
  RingHom.ext fun o ↦ by
    simp only [RingHom.comp_apply]
    rw [tr_algebraMap]
    exact congrArg _ (IsScalarTower.algebraMap_apply O (R (n + 1)) (R n) o).symm

/-- **The transition map** `G n → G m` for `m ≤ n`. -/
abbrev trLe {m n : ℕ} (h : m ≤ n) : T.G hθ n →+* T.G hθ m :=
  TowerSystem.trLe (G := T.G hθ) (T.tr hθ hO) h

lemma trLe_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    (T.trLe hθ hO h₁).comp (T.trLe hθ hO h₂) = T.trLe hθ hO (h₁.trans h₂) :=
  TowerSystem.trLe_comp _ h₁ h₂

lemma trLe_self_succ (n : ℕ) : T.trLe hθ hO (Nat.le_succ n) = T.tr hθ hO n :=
  TowerSystem.trLe_self_succ _ n

/-- The transition maps are surjective. -/
theorem surjective_trLe {m n : ℕ} (h : m ≤ n) : Function.Surjective (T.trLe hθ hO h) :=
  TowerSystem.surjective_trLe _ (T.surjective_tr hθ hO) h

/-- **The kernel of the transition map** `G n → G m` is `I^{m+1} G n` if
`ker (R (k+1) → R k) = I^{k+1} R (k+1)` and `I^{k+1} R k = 0`. -/
theorem ker_trLe {I : Ideal O}
    (hker : ∀ n, RingHom.ker (algebraMap (R (n + 1)) (R n)) =
      (I ^ (n + 1)).map (algebraMap O (R (n + 1))))
    (hkill : ∀ n, (I ^ (n + 1)).map (algebraMap O (R n)) = ⊥) {m n : ℕ} (h : m ≤ n) :
    RingHom.ker (T.trLe hθ hO h) = (I ^ (m + 1)).map (T.aG hθ n) := by
  refine TowerSystem.ker_trLe (T.aG hθ) (T.tr_comp_aG hθ hO) (T.surjective_tr hθ hO)
    (fun n ↦ T.ker_tr_of hθ hO (hker n)) (fun n ↦ ?_) h
  rw [← Ideal.map_map, hkill n, Ideal.map_bot]

end LevelTower.Data

end

end SemistableReduction
