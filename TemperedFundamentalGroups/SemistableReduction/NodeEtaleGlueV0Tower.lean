/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Succ
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Finite
import TemperedFundamentalGroups.SemistableReduction.TwoChartTower
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoMap

/-!
# The tower of two-chart rings of a covering (Blueprint §12.8, M2.3 (f), tower)

For `V : NodeEtaleGlue.Overlap I` (the restriction maps `ψ n : Y n → M n` commute with the
successor maps, `Overlap.ψ_succ`):

* `Overlap.qmap n : Q (n+1) → Q n` (the localization of `Ymap n` away from `x₁`), surjective with
  kernel `ϖⁿ⁺¹` (`surjective_qmap`, `ker_qmap`);
* `Overlap.sP'`, `sM'`, `qmap'`: the successor maps as maps of `B0'`-algebras;
* **`Overlap.f0 n`**: the successor map of the sections over `V₀` (`ZariskiTwo.map`);
* **`Overlap.succ n : TwoChartMap (twoChart (n+1)) (twoChart n)`**, surjective with kernels
  `ϖⁿ⁺¹` (`surjective_f0`, `ker_f0'`, `ker_f1`), levels killed by `ϖⁿ⁺¹` (`kill0`, `kill1`);
* **`Overlap.system`**: the adic system of chart algebras (`TwoChartTower.systemShift`), and
  **`Overlap.exists_algebraization`**: a coherent chart algebra on `ℙ¹_O` with these reductions.
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

/-! ### The successor maps of `Q n = Y n[1/x₁]` -/

lemma away_Ymap_x1 :
    IsLocalization.Away (I.Ymap hθ hO n (algebraMap I.B0 (I.Y hθ (n + 1)) V.x1)) (V.Q hθ n) := by
  rw [AlgHom.commutes]
  exact Localization.isLocalization

/-- **The successor map `Q (n+1) → Q n`**: `Ymap n` localized away from `x₁`. -/
def qmap : V.Q hθ (n + 1) →ₐ[I.B0] V.Q hθ n :=
  haveI := V.away_Ymap_x1 hθ hO n
  IsLocalization.Away.mapₐ (V.Q hθ (n + 1)) (V.Q hθ n) (I.Ymap hθ hO n)
    (algebraMap I.B0 (I.Y hθ (n + 1)) V.x1)

lemma qmap_algebraMap (y : I.Y hθ (n + 1)) :
    V.qmap hθ hO n (algebraMap (I.Y hθ (n + 1)) (V.Q hθ (n + 1)) y) =
      algebraMap (I.Y hθ n) (V.Q hθ n) (I.Ymap hθ hO n y) := by
  haveI := V.away_Ymap_x1 hθ hO n
  rw [qmap, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

/-- **The successor maps of `Q` are surjective.** -/
theorem surjective_qmap : Function.Surjective (V.qmap hθ hO n) := by
  haveI := V.away_Ymap_x1 hθ hO n
  exact IsLocalization.Away.mapₐ_surjective_of_surjective _ (I.surjective_Ymap hθ hO n)

/-- **The kernel of the successor map of `Q` is `K n · Q (n+1)`.** -/
theorem ker_qmap : RingHom.ker (V.qmap hθ hO n) =
    (I.K n).map (algebraMap I.B0 (V.Q hθ (n + 1))) := by
  haveI := V.away_Ymap_x1 hθ hO n
  have h := IsLocalization.ker_map (M := Submonoid.powers (algebraMap I.B0 (I.Y hθ (n + 1)) V.x1))
    (S := V.Q hθ (n + 1)) (Q := V.Q hθ n)
    (T := Submonoid.powers (I.Ymap hθ hO n (algebraMap I.B0 (I.Y hθ (n + 1)) V.x1)))
    (g := (I.Ymap hθ hO n : I.Y hθ (n + 1) →+* I.Y hθ n)) (Submonoid.map_powers _ _)
  rw [IsScalarTower.algebraMap_eq I.B0 (I.Y hθ (n + 1)) (V.Q hθ (n + 1)), ← Ideal.map_map,
    ← I.ker_Ymap hθ hO n]
  exact h

lemma qmap_W0 (w : V.W0) : V.qmap hθ hO n (letI := V.algW0Q hθ (n + 1)
    algebraMap V.W0 (V.Q hθ (n + 1)) w) =
      (letI := V.algW0Q hθ n; algebraMap V.W0 (V.Q hθ n) w) := by
  letI := V.algW0Q hθ (n + 1)
  letI := V.algW0Q hθ n
  haveI := V.hW0
  have : ((V.qmap hθ hO n : V.Q hθ (n + 1) →+* V.Q hθ n)).comp
      (algebraMap V.W0 (V.Q hθ (n + 1))) = algebraMap V.W0 (V.Q hθ n) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers V.x1) (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [V.algW0Q_algebraMap hθ (n + 1), V.algW0Q_algebraMap hθ n, AlgHom.commutes]
  exact RingHom.congr_fun this w

/-! ### The successor maps over `B0'` -/

/-- `qmap` as a map of `B0'`-algebras. -/
def qmap' : letI := V.alg0'Q hθ (n + 1); letI := V.alg0'Q hθ n
    V.Q hθ (n + 1) →ₐ[V.B0'] V.Q hθ n :=
  letI := V.alg0'Q hθ (n + 1)
  letI := V.alg0'Q hθ n
  { (V.qmap hθ hO n : V.Q hθ (n + 1) →+* V.Q hθ n) with
    commutes' := fun y ↦ V.qmap_W0 hθ hO n (algebraMap V.B0' V.W0 y) }

/-- `sP` as a map of `B0'`-algebras. -/
def sP' : letI := V.alg0'E (n + 1); letI := V.alg0'E n; V.P0.P (n + 1) →ₐ[V.B0'] V.P0.P n :=
  letI := V.alg0'E (n + 1)
  letI := V.alg0'E n
  { V.P0.sP n with
    commutes' := fun y ↦ by
      change V.P0.sP n (algebraMap (V.B' (n + 1)) _ (algebraMap V.B0' (V.B' (n + 1)) y)) =
        algebraMap (V.B' n) _ (algebraMap V.B0' (V.B' n) y)
      rw [V.P0.hsP, ← IsScalarTower.algebraMap_apply V.B0' (V.B' (n + 1)) (V.B' n)] }

/-- `sM` as a map of `B0'`-algebras. -/
def sM' : letI := V.alg0'M (n + 1); letI := V.alg0'M n; V.M (n + 1) →ₐ[V.B0'] V.M n :=
  letI := V.alg0'M (n + 1)
  letI := V.alg0'M n
  { V.sM n with
    commutes' := fun y ↦ by
      change V.sM n (algebraMap (V.B' (n + 1)) _ (algebraMap V.B0' (V.B' (n + 1)) y)) =
        algebraMap (V.B' n) _ (algebraMap V.B0' (V.B' n) y)
      rw [IsScalarTower.algebraMap_apply (V.B' (n + 1)) (V.P0.P (n + 1)) (V.M (n + 1)),
        sM_algebraMap, V.P0.hsP, ← IsScalarTower.algebraMap_apply V.B0' (V.B' (n + 1)) (V.B' n),
        ← IsScalarTower.algebraMap_apply (V.B' n) (V.P0.P n) (V.M n)] }

/-! ### Compatibility with the restriction maps -/

lemma ρ0aR_succ (q : V.Q hθ (n + 1)) :
    V.ρ0aR hθ hO n (V.qmap hθ hO n q) = V.sM n (V.ρ0aR hθ hO (n + 1) q) := by
  have : (V.ρ0aR hθ hO n).comp (V.qmap hθ hO n : V.Q hθ (n + 1) →+* V.Q hθ n) =
      (V.sM n).comp (V.ρ0aR hθ hO (n + 1)) := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (algebraMap I.B0 (I.Y hθ (n + 1)) V.x1)) (RingHom.ext fun y ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [qmap_algebraMap, ρ0aR_algebraMap, ρ0aR_algebraMap, V.ψ_succ _ hθ hO]
  exact RingHom.congr_fun this q

lemma ρ0b_succ (e : V.P0.P (n + 1)) : V.ρ0b n (V.P0.sP n e) = V.sM n (V.ρ0b (n + 1) e) :=
  (V.sM_algebraMap n e).symm

/-- **The successor map of the sections over `V₀`** (`ZariskiTwo.map` over `B0'`). -/
def f0 : letI := V.alg0'Q hθ (n + 1); letI := V.alg0'Q hθ n
    letI := V.alg0'E (n + 1); letI := V.alg0'E n
    letI := V.alg0'M (n + 1); letI := V.alg0'M n
    ZariskiTwo.glued (V.ρ0a hθ hO (n + 1)) (V.ρ0b (n + 1)) →ₐ[V.B0']
      ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n) :=
  letI := V.alg0'Q hθ (n + 1)
  letI := V.alg0'Q hθ n
  letI := V.alg0'E (n + 1)
  letI := V.alg0'E n
  letI := V.alg0'M (n + 1)
  letI := V.alg0'M n
  ZariskiTwo.map (V.qmap' hθ hO n) (V.sP' n) (V.sM' n)
    (fun q ↦ V.ρ0aR_succ hθ hO n q) (fun e ↦ V.ρ0b_succ n e)

lemma towerOY (m : ℕ) : letI := V.algOB0; letI := V.algOY hθ m
    IsScalarTower O I.B0 (I.Y hθ m) :=
  letI := V.algOB0
  letI := V.algOY hθ m
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- **The successor maps of the two-chart rings of the covering.** -/
def succ : TwoChartMap (A := O) (V.twoChart hθ hO (n + 1)) (V.twoChart hθ hO n) := by
  letI := V.alg0'Q hθ (n + 1)
  letI := V.alg0'Q hθ n
  letI := V.algOQ hθ (n + 1)
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ (n + 1)
  haveI := V.towerOQ hθ n
  letI := V.alg0'E (n + 1)
  letI := V.alg0'E n
  haveI := V.towerOE (n + 1)
  haveI := V.towerOE n
  letI := V.alg0'M (n + 1)
  letI := V.alg0'M n
  haveI := V.towerOM (n + 1)
  haveI := V.towerOM n
  letI := V.algOY hθ (n + 1)
  letI := V.algOY hθ n
  letI := V.algOB0
  haveI := V.towerOY hθ (n + 1)
  haveI := V.towerOY hθ n
  exact
    { f0 := (V.f0 hθ hO n).restrictScalars O
      f1 := (I.Ymap hθ hO n).restrictScalars O
      f01 := (V.qmap' hθ hO n).restrictScalars O
      hx := (V.f0 hθ hO n).commutes V.x0
      hy := (I.Ymap hθ hO n).commutes V.x1
      hu := (V.qmap' hθ hO n).commutes V.x0
      h0 := fun _ ↦ rfl
      h1 := fun y ↦ V.qmap_algebraMap hθ hO n y }

/-! ### The levels are killed by `ϖⁿ⁺¹` -/

lemma algebraMap_B_eq_zero (m : ℕ) {o : O} (ho : o ∈ Ideal.span {V.ϖ} ^ (m + 1)) :
    algebraMap O (I.B m) o = 0 := by
  have h := Ideal.mem_map_of_mem (algebraMap O (I.B m)) ho
  rw [V.killB m] at h
  exact Ideal.mem_bot.mp h

lemma algebraMap_B'_eq_zero (m : ℕ) {o : O} (ho : o ∈ Ideal.span {V.ϖ} ^ (m + 1)) :
    algebraMap O (V.B' m) o = 0 := by
  have h := Ideal.mem_map_of_mem (algebraMap O (V.B' m)) ho
  rw [V.killB' m] at h
  exact Ideal.mem_bot.mp h

lemma algebraMap_Y_eq_zero (m : ℕ) {o : O} (ho : o ∈ Ideal.span {V.ϖ} ^ (m + 1)) :
    (letI := V.algOY hθ m; algebraMap O (I.Y hθ m) o) = 0 := by
  have hB : algebraMap I.B0 (I.B m) (letI := V.algOB0; algebraMap O I.B0 o) = 0 := by
    rw [V.hOB0B, V.algebraMap_B_eq_zero m ho]
  have hG : (letI := alg0G I.T hθ I.B I.B0 m
      algebraMap I.B0 (I.T.G hθ m) (letI := V.algOB0; algebraMap O I.B0 o)) = 0 := by
    letI := algBG I.T hθ I.B m
    change algebraMap (I.B m) (I.T.G hθ m) _ = 0
    rw [hB, map_zero]
  have hE : (letI := alg0 I.B I.B0 m (I.E m)
      algebraMap I.B0 (I.E m) (letI := V.algOB0; algebraMap O I.B0 o)) = 0 := by
    change algebraMap (I.B m) (I.E m) _ = 0
    rw [hB, map_zero]
  exact Subtype.ext (Prod.ext hG hE)

lemma algOQ_apply (m : ℕ) (o : O) : (letI := V.algOQ hθ m; algebraMap O (V.Q hθ m) o) =
    algebraMap (I.Y hθ m) (V.Q hθ m) (letI := V.algOY hθ m; algebraMap O (I.Y hθ m) o) := by
  letI := V.algW0Q hθ m
  letI := V.algOB0
  change algebraMap V.W0 (V.Q hθ m) (algebraMap V.B0' V.W0 (algebraMap O V.B0' o)) =
    algebraMap (I.Y hθ m) (V.Q hθ m) (algebraMap I.B0 (I.Y hθ m) (algebraMap O I.B0 o))
  rw [← IsScalarTower.algebraMap_apply O V.B0' V.W0, IsScalarTower.algebraMap_apply O I.B0 V.W0,
    V.algW0Q_algebraMap, IsScalarTower.algebraMap_apply I.B0 (I.Y hθ m) (V.Q hθ m)]

/-- **The sections over `U₀` at level `m` are killed by `ϖᵐ⁺¹`.** -/
theorem kill0 (m : ℕ) :
    (Ideal.span {V.ϖ} ^ (m + 1)).map (algebraMap O (V.twoChart hθ hO m).R0) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro o ho
  rw [RingHom.mem_ker]
  letI := V.algOQ hθ m
  letI := V.alg0'E m
  have h1 : algebraMap O (V.Q hθ m) o = 0 := by
    rw [V.algOQ_apply hθ m, V.algebraMap_Y_eq_zero hθ m ho, map_zero]
  have h2 : algebraMap O (V.P0.P m) o = 0 := by
    rw [IsScalarTower.algebraMap_apply O (V.B' m) (V.P0.P m), V.algebraMap_B'_eq_zero m ho,
      map_zero]
  exact Subtype.ext (Prod.ext h1 h2)

/-- **The sections over `U₁` at level `m` are killed by `ϖᵐ⁺¹`.** -/
theorem kill1 (m : ℕ) :
    (Ideal.span {V.ϖ} ^ (m + 1)).map (algebraMap O (V.twoChart hθ hO m).R1) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro o ho
  exact V.algebraMap_Y_eq_zero hθ m ho

/-! ### Surjectivity and kernels of the successor maps -/

lemma fstLM (m : ℕ) : letI := V.alg0'Q hθ m; letI := V.alg0'E m; letI := V.alg0'M m
    IsLocalizedModule (Submonoid.powers V.x0)
      (ZariskiTwo.fst (V.ρ0a hθ hO m) (V.ρ0b m)).toLinearMap :=
  letI := V.alg0'Q hθ m
  letI := V.alg0'E m
  letI := V.alg0'M m
  ZariskiTwo.isLocalizedModule_fst V.x0 (IsUnit.of_mul_eq_one _ (V.hxy hθ m))
    (V.isLocalization_ρ0b m)

lemma sndLM (m : ℕ) : letI := V.alg0'Q hθ m; letI := V.alg0'E m; letI := V.alg0'M m
    IsLocalizedModule (Submonoid.powers V.c0)
      (ZariskiTwo.snd (V.ρ0a hθ hO m) (V.ρ0b m)).toLinearMap :=
  letI := V.alg0'Q hθ m
  letI := V.alg0'E m
  letI := V.alg0'M m
  ZariskiTwo.isLocalizedModule_snd V.c0 (V.P0.hcP m) (V.isLocalization_ρ0a' hθ hO m)

/-- The ideal `ϖⁿ⁺¹` of the second chart. -/
abbrev K' : Ideal V.B0' := (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O V.B0')

lemma ker_qmap' : letI := V.alg0'Q hθ (n + 1); letI := V.alg0'Q hθ n
    RingHom.ker (V.qmap' hθ hO n) = (V.K' n).map (algebraMap V.B0' (V.Q hθ (n + 1))) := by
  letI := V.alg0'Q hθ (n + 1)
  letI := V.alg0'Q hθ n
  letI := V.algOB0
  change RingHom.ker (V.qmap hθ hO n) = _
  rw [ker_qmap, V.hK, Ideal.map_map, Ideal.map_map]
  congr 1
  ext o
  exact (V.algOQ_apply hθ (n + 1) o).symm

lemma ker_sP' : letI := V.alg0'E (n + 1); letI := V.alg0'E n
    RingHom.ker (V.sP' n) = (V.K' n).map (algebraMap V.B0' (V.P0.P (n + 1))) := by
  letI := V.alg0'E (n + 1)
  letI := V.alg0'E n
  haveI := V.towerOE (n + 1)
  change RingHom.ker (V.P0.sP n) = _
  rw [V.P0.hkP, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **The successor maps over `V₀` are surjective.** -/
theorem surjective_f0 : Function.Surjective (V.f0 hθ hO n) := by
  letI := V.alg0'Q hθ (n + 1)
  letI := V.alg0'Q hθ n
  letI := V.alg0'E (n + 1)
  letI := V.alg0'E n
  letI := V.alg0'M (n + 1)
  letI := V.alg0'M n
  haveI := V.fstLM hθ hO (n + 1)
  haveI := V.sndLM hθ hO (n + 1)
  haveI := V.fstLM hθ hO n
  haveI := V.sndLM hθ hO n
  exact ZariskiTwo.surjective_map V.x0 V.c0 (V.qmap' hθ hO n) (V.sP' n) (V.sM' n) _ _ (V.K' n)
    V.hxc (V.surjective_qmap hθ hO n) (V.P0.hsPs n) (V.ker_qmap' hθ hO n) (V.ker_sP' n)

/-- **The kernel of the successor map over `V₀` is `ϖⁿ⁺¹`.** -/
theorem ker_f0 : letI := V.alg0'Q hθ (n + 1); letI := V.alg0'E (n + 1); letI := V.alg0'M (n + 1)
    RingHom.ker (V.f0 hθ hO n) = (V.K' n).map (algebraMap V.B0'
      (ZariskiTwo.glued (V.ρ0a hθ hO (n + 1)) (V.ρ0b (n + 1)))) := by
  letI := V.alg0'Q hθ (n + 1)
  letI := V.alg0'Q hθ n
  letI := V.alg0'E (n + 1)
  letI := V.alg0'E n
  letI := V.alg0'M (n + 1)
  letI := V.alg0'M n
  haveI := V.fstLM hθ hO (n + 1)
  haveI := V.sndLM hθ hO (n + 1)
  haveI := V.fstLM hθ hO n
  haveI := V.sndLM hθ hO n
  exact ZariskiTwo.ker_map V.x0 V.c0 (V.qmap' hθ hO n) (V.sP' n) (V.sM' n) _ _ (V.K' n)
    V.hxc (V.surjective_qmap hθ hO n) (V.P0.hsPs n) (V.ker_qmap' hθ hO n) (V.ker_sP' n)

/-- **The kernel of the successor map over `V₁` is `ϖⁿ⁺¹`.** -/
theorem ker_f1 : RingHom.ker (V.succ hθ hO n).f1 =
    (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O (V.twoChart hθ hO (n + 1)).R1) := by
  letI := V.algOB0
  change RingHom.ker (I.Ymap hθ hO n) = _
  rw [I.ker_Ymap hθ hO n, V.hK, Ideal.map_map]
  rfl

lemma ker_f0' : RingHom.ker (V.succ hθ hO n).f0 =
    (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O (V.twoChart hθ hO (n + 1)).R0) := by
  letI := V.alg0'Q hθ (n + 1)
  letI := V.alg0'E (n + 1)
  letI := V.alg0'M (n + 1)
  letI := V.algOQ hθ (n + 1)
  haveI := V.towerOQ hθ (n + 1)
  haveI := V.towerOE (n + 1)
  have h := V.ker_f0 hθ hO n
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  exact h

/-- **The adic system of chart algebras of the covering** (`TwoChartTower.systemShift`): level
`n + 1` is `twoChart n`, the covering modulo `ϖⁿ⁺¹`. -/
def system : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ}) :=
  TwoChartTower.systemShift _ (fun n ↦ V.twoChart hθ hO n) (fun n ↦ V.succ hθ hO n)
    (fun n ↦ V.surjective_f0 hθ hO n) (fun n ↦ I.surjective_Ymap hθ hO n)
    (fun n ↦ V.ker_f0' hθ hO n) (fun n ↦ V.ker_f1 hθ hO n) (V.kill0 hθ hO) (V.kill1 hθ hO)
    (fun n ↦ V.finite0 hθ hO n) (fun n ↦ V.finite1 hθ hO n)

/-- **Algebraization of the covering** (Grothendieck existence for coherent algebras on `ℙ¹_O`,
`ProjectiveLine.AdicChartAlgSystem.exists_algebraization`): a coherent chart algebra over `ℙ¹_O`
whose reductions modulo `ϖⁿ` are the levels of the covering. -/
theorem exists_algebraization [IsNoetherianRing O] [IsAdicComplete (Ideal.span {V.ϖ}) O] :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite (Polynomial O) (Module.AEval' N.x0))
      (_ : Module.Finite (Polynomial O) (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N ((V.system hθ hO).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n), ((V.system hθ hO).tr h).comp (α n) = α m) ∧
      ∀ n, B.IsHom ((V.system hθ hO).alg n) (α n) :=
  (V.system hθ hO).exists_algebraization

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
