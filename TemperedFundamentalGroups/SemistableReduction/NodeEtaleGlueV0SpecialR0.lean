/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueOverlapSpecial
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Special

/-!
# The bottom level of the covering over the second chart (Blueprint §12.8, M2.5 (b))

In the setting of `NodeEtaleGlue.Overlap` (the covering over `V₀ = Spec B0'` glued from
`Q n = Y n[1/x₁]` and the piece `P0 n` over `D(c₀)` along `M n = P0 n[1/x₀]`), at a level where
`J = 0` on the base charts:

* `NodeEtaleGlue.Piece0.Bottom`: the input from the piece — an identification of `P0 n` with
  `C0[1/c̄₀]` compatible with `ℓ0` (instances: `Piece0.bottomOfEtale` for the étale lifts);
* **`NodeEtaleGlue.Overlap.r0Equiv`**: `C0 ≃+* R0 n = Q n ×_{M n} P0 n` — the covering over `V₀`
  at the bottom level is the given covering `C0` (components `C0 → C0[1/x̄₀] ≃ω C1[1/x̄₁] ≃ Q n`
  and `C0 → P0 n`; they agree on `M n` because both reduce to `ℓ0`, `Input.mk_ψ_yEquiv`).
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Piece0

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}

/-- **A bottom identification of a piece** at level `n`: a map `C0 → P n` over `B' n` which is
a localization away from `c̄₀` and reduces to `ℓ0` on the overlap. -/
structure Bottom (P : Piece0 θ B' qB' C0 x0 c0 x0s c0s ϖ) (n : ℕ) where
  /-- the map `C0 → P n` -/
  toP : C0 →+* P.P n
  hP : ∀ y : B' n, toP (algebraMap Bs' C0 (qB' n y)) = algebraMap (B' n) (P.P n) y
  hloc : letI := toP.toAlgebra; IsLocalization.Away (algebraMap Bs' C0 c0s) (P.P n)
  hℓ : ∀ c, Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' n)) (Loc0 (B' n) (P.P n) x0))
    (algebraMap (P.P n) (Loc0 (B' n) (P.P n) x0) (toP c)) = P.ℓ0 n c

variable [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)] [∀ n, IsScalarTower O (B' (n + 1)) (B' n)]
  (E0 : ℕ → Type u) [∀ n, CommRing (E0 n)] [∀ n, Algebra (B' n) (E0 n)] [∀ n, Algebra O (E0 n)]
  [∀ n, IsScalarTower O (B' n) (E0 n)] [∀ n, Algebra.FormallyEtale (B' n) (E0 n)]
  (σE0 : ∀ n, letI := ((algebraMap Bs' C0).comp (qB' n)).toAlgebra
    (E0 n ⧸ EtaleNil.JB (J θ (R := B' n)) (E0 n)) ≃ₐ[B' n]
      Localization.Away (algebraMap Bs' C0 c0s))
  (hcE0 : ∀ n, IsUnit (algebraMap (B' n) (E0 n) (algebraMap B0' (B' n) c0)))
  (hfinE0 : ∀ n, ∃ s : Finset (E0 n), ∀ p : E0 n, ∃ k : ℕ,
    algebraMap B0' (B' n) c0 ^ k • p ∈ Submodule.span (B' n) (s : Set (E0 n)))
  (hx0 : ∀ n, qB' n (algebraMap B0' (B' n) x0) = x0s)
  (sE0 : ∀ n, E0 (n + 1) →+* E0 n)
  (hsE0 : ∀ n (x : B' (n + 1)), sE0 n (algebraMap (B' (n + 1)) (E0 (n + 1)) x) =
    algebraMap (B' n) (E0 n) (algebraMap (B' (n + 1)) (B' n) x))
  (hσE0 : ∀ n (x : E0 (n + 1)), σE0 n (Ideal.Quotient.mk _ (sE0 n x)) =
    σE0 (n + 1) (Ideal.Quotient.mk _ x))
  (hsE0s : ∀ n, Function.Surjective (sE0 n))
  (hkE0 : ∀ n, RingHom.ker (sE0 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (E0 (n + 1))))
  {n : ℕ} (hJ0 : J θ (R := B' n) = ⊥)

/-- **The bottom identification of the étale piece** (`J = 0`): `C0 → C0[1/c̄₀] ≃ E0/J = E0`. -/
def bottomOfEtale : (ofEtale E0 σE0 hcE0 hfinE0 hx0 sE0 hsE0 hσE0 hsE0s hkE0).Bottom n := by
  letI := ((algebraMap Bs' C0).comp (qB' n)).toAlgebra
  let g : C0 →ₐ[B' n] E0 n :=
    ((FormalPatchLevel.quotEquivOfEqBot hJ0 (B' n) (E0 n)).toAlgHom.comp
      (σE0 n).symm.toAlgHom).comp
      (IsScalarTower.toAlgHom (B' n) C0 (Localization.Away (algebraMap Bs' C0 c0s)))
  have hl : letI := (g : C0 →+* E0 n).toAlgebra
      IsLocalization.Away (algebraMap Bs' C0 c0s) (E0 n) := by
    letI := (g : C0 →+* E0 n).toAlgebra
    have e : Localization.Away (algebraMap Bs' C0 c0s) ≃ₐ[C0] E0 n := AlgEquiv.ofRingEquiv
      (f := ((σE0 n).symm.trans (FormalPatchLevel.quotEquivOfEqBot hJ0 (B' n) (E0 n))).toRingEquiv)
      fun _ ↦ rfl
    exact IsLocalization.isLocalization_of_algEquiv
      (Submonoid.powers (algebraMap Bs' C0 c0s)) e
  refine
    { toP := (g : C0 →+* E0 n)
      hP := fun y ↦ g.commutes y
      hloc := hl
      hℓ := fun c ↦ ?_ }
  · change _ = EtaleNil.red (J θ (R := B' n))
      (IsScalarTower.toAlgHom (B' n) (E0 n) (Loc0 (B' n) (E0 n) x0))
      ((σE0 n).symm (algebraMap C0 (Localization.Away (algebraMap Bs' C0 c0s)) c))
    rw [← FormalPatchLevel.mk_quotEquivOfEqBot (S := B' n) hJ0
      ((σE0 n).symm (algebraMap C0 (Localization.Away (algebraMap Bs' C0 c0s)) c)),
      EtaleNil.red_mk]
    rfl

end Piece0


namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ} (hJ0 : J θ (R := I.B n) = ⊥)
  (bot : V.P0.Bottom n)

/-- `C0` over `B0'` (through `B0' → B' n → Bs'`). -/
@[reducible] def algC0' (n : ℕ) : Algebra V.B0' V.C0 :=
  ((algebraMap V.Bs' V.C0).comp ((V.qB' n).comp (algebraMap V.B0' (V.B' n)))).toAlgebra

/-- **`C1[1/x̄₁] ≃ Q n = Y n[1/x₁]`**, the localization of `Input.yEquiv`. -/
def eQ : Localization.Away (algebraMap I.Bs I.C1 V.x1s) ≃+* V.Q hθ n :=
  letI := I.algC10 n
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (algebraMap I.Bs I.C1 V.x1s))
    (T := Submonoid.powers (algebraMap I.B0 (I.Y hθ n) V.x1)) _ _
    (I.yEquiv hθ hO hJ0).toRingEquiv (by
      rw [Submonoid.map_powers]
      congr 1
      change I.yEquiv hθ hO hJ0 (algebraMap I.Bs I.C1 V.x1s) = _
      rw [← V.hx1 n]
      exact (I.yEquiv hθ hO hJ0).commutes V.x1)

lemma eQ_algebraMap (c : I.C1) :
    V.eQ hθ hO hJ0 (algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s)) c) =
      algebraMap (I.Y hθ n) (V.Q hθ n) (I.yEquiv hθ hO hJ0 c) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ _

lemma eQ_W0 (w : V.W0) :
    V.eQ hθ hO hJ0 (algebraMap V.Ws (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
      (V.qW n (algebraMap V.W0 (V.W n) w))) =
      (letI := V.algW0Q hθ n; algebraMap V.W0 (V.Q hθ n) w) := by
  letI := V.algW0Q hθ n
  letI := I.algC10 n
  haveI := V.hW0
  have h : ((V.eQ hθ hO hJ0).toRingHom.comp
      ((algebraMap V.Ws (Localization.Away (algebraMap I.Bs I.C1 V.x1s))).comp
        ((V.qW n).comp (algebraMap V.W0 (V.W n))))) = algebraMap V.W0 (V.Q hθ n) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers V.x1) (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [V.hWB n, V.hq1 n, ← IsScalarTower.algebraMap_apply I.Bs V.Ws,
      IsScalarTower.algebraMap_apply I.Bs I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s)),
      eQ_algebraMap]
    have e1 : I.yEquiv hθ hO hJ0 (algebraMap I.Bs I.C1 (I.qB n (algebraMap I.B0 (I.B n) b))) =
        algebraMap I.B0 (I.Y hθ n) b := (I.yEquiv hθ hO hJ0).commutes b
    rw [e1, ← IsScalarTower.algebraMap_apply, V.algW0Q_algebraMap hθ n]
  exact RingHom.congr_fun h w

/-- `C0 → C0[1/x̄₀] ≃ω C1[1/x̄₁] ≃ Q n`. -/
def φQ : letI := V.algC0' n; letI := V.alg0'Q hθ n; V.C0 →ₐ[V.B0'] V.Q hθ n :=
  letI := V.algC0' n
  letI := V.alg0'Q hθ n
  { (V.eQ hθ hO hJ0).toRingHom.comp (V.ω.toRingEquiv.toRingHom.comp
      (algebraMap V.C0 (Localization.Away (algebraMap V.Bs' V.C0 V.x0s)))) with
    commutes' := fun y ↦ by
      letI := V.algW0Q hθ n
      change V.eQ hθ hO hJ0 (V.ω (algebraMap V.C0 _ (algebraMap V.Bs' V.C0
        (V.qB' n (algebraMap V.B0' (V.B' n) y))))) =
          algebraMap V.W0 (V.Q hθ n) (algebraMap V.B0' V.W0 y)
      have e1 := IsScalarTower.algebraMap_apply V.Bs' V.C0
        (Localization.Away (algebraMap V.Bs' V.C0 V.x0s)) (V.qB' n (algebraMap V.B0' (V.B' n) y))
      have e2 := IsScalarTower.algebraMap_apply V.Bs' V.Ws
        (Localization.Away (algebraMap V.Bs' V.C0 V.x0s)) (V.qB' n (algebraMap V.B0' (V.B' n) y))
      rw [← e1, e2, ← V.hq0 n, ← V.hWB' n, AlgEquiv.commutes, eQ_W0] }

/-- `C0 → P0 n` (the bottom identification of the piece). -/
def φP : letI := V.algC0' n; letI := V.alg0'E n; V.C0 →ₐ[V.B0'] V.P0.P n :=
  letI := V.algC0' n
  letI := V.alg0'E n
  { bot.toP with commutes' := fun y ↦ bot.hP (algebraMap V.B0' (V.B' n) y) }

/-- `Q n → M n → M n/J` on `C1[1/x̄₁] ≃ Q n` is `ℓ1 = ℓx ∘ ω⁻¹` (the special-fibre map of the
piece, through `ω`): both are determined on `C1`, where they are `γM` (`Input.mk_ψ_yEquiv`). -/
lemma mk_ρ0aR_eQ (d : Localization.Away (algebraMap I.Bs I.C1 V.x1s)) :
    letI := V.algBM n
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (V.M n))
        (V.ρ0aR hθ hO n (V.eQ hθ hO hJ0 d)) =
      Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0)
          (V.hWn0 n) (V.P0.P n) (Bn := I.B n))
        (OverlapPiece.ℓ1 (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0) (V.P0.P n) V.x1s V.x0s
          V.c0s V.ω (V.P0.ℓ0 n) (V.P0.hℓ0loc n) d) := by
  letI := V.algBM n
  letI := V.alg0M n
  haveI := V.formallyEtale_M n
  haveI := V.tower0M n
  have h : (Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (V.M n))).comp
      ((V.ρ0aR hθ hO n).comp (V.eQ hθ hO hJ0).toRingHom) =
      (Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0)
          (V.hWn0 n) (V.P0.P n) (Bn := I.B n))).toRingHom.comp
        (OverlapPiece.ℓ1 (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0) (V.P0.P n) V.x1s V.x0s
          V.c0s V.ω (V.P0.ℓ0 n) (V.P0.hℓ0loc n)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap I.Bs I.C1 V.x1s))
      (RingHom.ext fun c ↦ ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [eQ_algebraMap, ρ0aR_algebraMap]
    exact I.mk_ψ_yEquiv hθ hO n V.g (V.hfg n) (V.γM n) (V.isLocalization_γM n) hJ0 c
  exact RingHom.congr_fun h d

/-- **The two components agree on the overlap** `M n`. -/
lemma φQ_compat (c : V.C0) : V.ρ0a hθ hO n (V.φQ hθ hO hJ0 c) = V.ρ0b n (V.φP bot c) := by
  letI := V.algBM n
  apply I.mk_injective_of_eq_bot n hJ0 (V.M n)
  change Ideal.Quotient.mk _ (V.ρ0aR hθ hO n (V.eQ hθ hO hJ0
      (V.ω (algebraMap V.C0 (Localization.Away (algebraMap V.Bs' V.C0 V.x0s)) c)))) =
    Ideal.Quotient.mk _ (algebraMap (V.P0.P n) (V.M n) (bot.toP c))
  rw [mk_ρ0aR_eQ]
  have e : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (V.M n))
      (algebraMap (V.P0.P n) (V.M n) (bot.toP c)) =
      Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0)
          (V.hWn0 n) (V.P0.P n) (Bn := I.B n))
        (Ideal.Quotient.mk _ (algebraMap (V.P0.P n) (V.M n) (bot.toP c))) := rfl
  rw [e, bot.hℓ c]
  congr 1
  change OverlapPiece.ℓx (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0) (V.P0.P n) V.x0s V.c0s
    (V.P0.ℓ0 n) (V.P0.hℓ0loc n) (V.ω.symm (V.ω (algebraMap V.C0 _ c))) = _
  rw [AlgEquiv.symm_apply_apply, OverlapPiece.ℓx_algebraMap]

/-- `φQ` is a localization away from `x₀`. -/
lemma isLocalizedModule_φQ : letI := V.algC0' n; letI := V.alg0'Q hθ n
    IsLocalizedModule (Submonoid.powers V.x0) (V.φQ hθ hO hJ0).toLinearMap := by
  letI := V.algC0' n
  letI := V.alg0'Q hθ n
  refine ZariskiTwo.isLocalizedModule_of_away V.x0 _ ?_
  letI := (V.φQ hθ hO hJ0).toRingHom.toAlgebra
  have e : Localization.Away (algebraMap V.Bs' V.C0 V.x0s) ≃ₐ[V.C0] V.Q hθ n :=
    AlgEquiv.ofRingEquiv (f := V.ω.toRingEquiv.trans (V.eQ hθ hO hJ0)) fun _ ↦ rfl
  have h := IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (algebraMap V.Bs' V.C0 V.x0s)) e
  have hx : algebraMap V.B0' V.C0 V.x0 = algebraMap V.Bs' V.C0 V.x0s := by
    rw [← V.hx0 n]
    rfl
  rw [hx]
  exact h

/-- `φP` is a localization away from `c₀`. -/
lemma isLocalizedModule_φP : letI := V.algC0' n; letI := V.alg0'E n
    IsLocalizedModule (Submonoid.powers V.c0) (V.φP bot).toLinearMap := by
  letI := V.algC0' n
  letI := V.alg0'E n
  refine ZariskiTwo.isLocalizedModule_of_away V.c0 _ ?_
  have hc : algebraMap V.B0' V.C0 V.c0 = algebraMap V.Bs' V.C0 V.c0s := by
    rw [← V.hc0 n]
    rfl
  rw [hc]
  exact bot.hloc

/-- **The covering over `V₀` at a level with `J = 0` is the given covering `C0`**:
`C0 ≃ₐ[B0'] R0 n = Q n ×_{M n} P0 n`. -/
def r0Equiv : letI := V.algC0' n; letI := V.alg0'Q hθ n; letI := V.alg0'E n
    letI := V.alg0'M n
    V.C0 ≃ₐ[V.B0'] ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n) := by
  letI := V.algC0' n
  letI := V.alg0'Q hθ n
  letI := V.alg0'E n
  letI := V.alg0'M n
  haveI := V.fstLM hθ hO n
  haveI := V.sndLM hθ hO n
  haveI := V.isLocalizedModule_φQ hθ hO hJ0
  haveI := V.isLocalizedModule_φP bot
  exact ZariskiTwo.liftEquiv V.x0 V.c0 V.hxc (V.φQ hθ hO hJ0) (V.φP bot)
    (V.φQ_compat hθ hO hJ0 bot)

/-- `r0Equiv` as a ring isomorphism onto the first two-chart ring of the covering. -/
def r0Equiv' : V.C0 ≃+* (V.twoChart hθ hO n).R0 :=
  letI := V.algC0' n
  (V.r0Equiv hθ hO hJ0 bot).toRingEquiv

/-- **The special fibre of the algebraized covering, first chart** (generic): for a flat
algebraization `(N, B, α)` of `S = V.system` with `J = 0` on the bottom base chart `B 0` and a
bottom identification of the piece over `D(c₀)`, `B₀ ⧸ (ϖ) ≃ C0`. -/
def specialFibreEquiv0
    {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ hO = S)
    {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N (S.M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n)) (hJ0 : J θ (R := I.B 0) = ⊥) (bot : V.P0.Bottom 0) :
    B.Ring0 ⧸ Ideal.span {B.const0 V.ϖ} ≃+* V.C0 := by
  subst hS
  exact (TwoChartTower.specialFibreEquiv0 (E := fun n ↦ V.twoChart hθ hO n) hα hB).trans
    (V.r0Equiv' hθ hO hJ0 bot).symm

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
