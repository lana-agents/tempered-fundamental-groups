/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleLevelLift

/-!
# The levels of an étale cover are compatible with the successor maps (MR12 S6, G1)

Setting of `EtaleLevelLift`: a chart `T` over `O`, levels `Tn n = T/ϖⁿ⁺¹T`, a `T`-algebra `B`
with levels `Pn n = (B/ϖⁿ⁺¹B)[1/b]`, identified with any étale lift of `B/JB` over `D(b)` at
level `n` by `levelEquiv`.

* **`EtaleTower.Lift.equiv_succ`**: the successor maps of towers of étale lifts are natural in the
  lifts: `equiv ∘ succ = succ ∘ equiv`.
* `EtaleTower.levelSucc`: the transition map `Pn (n + 1) → Pn n`; **`levelSucc_eq_succ`**: it is the
  successor map of the lifts `levelLift`.
* **`EtaleTower.levelEquiv_levelSucc`**: `levelEquiv ∘ levelSucc = succ ∘ levelEquiv` for any
  towers of lifts (e.g. `EtaleTower.lift`), i.e. the levels of `B` form, with their transition
  maps, the tower of étale lifts used by the M2 lift.

All maps are the unique maps out of formally étale algebras with given reduction modulo the
nilpotent `J` (`EtaleNil.ext`).
-/

universe u

namespace SemistableReduction

open AdmissibleLift

namespace EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {ϖ : O}
  {T : Type u} [CommRing T] [Algebra O T] {hϖ : θ ϖ = 0}
  {C : Type u} [CommRing C] [Algebra (Ts θ T) C] {b : T}

namespace Lift

variable (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) {n : ℕ}

/-- **The successor maps are natural in the lifts**: for lifts `L₁', L₂'` at level `n + 1` and
`L₁, L₂` at level `n`, `equiv ∘ succ = succ ∘ equiv` (both are maps out of the formally étale
`L₁'.E` agreeing modulo the nilpotent `J`). -/
lemma equiv_succ (L₁' L₂' : Lift T hϖ C b (n + 1)) (L₁ L₂ : Lift T hϖ C b n) (x : L₁'.E) :
    equiv hker L₁ L₂ (succ T hϖ C b hker L₁' L₁ x) =
      succ T hϖ C b hker L₂' L₂ (equiv hker L₁' L₂' x) := by
  letI := algE T hϖ C b L₁
  letI := algE T hϖ C b L₂
  haveI := isScalarTower_E T hϖ C b L₁
  haveI := isScalarTower_E T hϖ C b L₂
  letI := algC T hϖ C n
  letI := algC T hϖ C (n + 1)
  let φ : L₁'.E →ₐ[Tn ϖ T (n + 1)] L₂.E :=
    ((equiv hker L₁ L₂).toAlgHom.restrictScalars (Tn ϖ T (n + 1))).comp
      (succ T hϖ C b hker L₁' L₁)
  let ψ : L₁'.E →ₐ[Tn ϖ T (n + 1)] L₂.E :=
    (succ T hϖ C b hker L₂' L₂).comp
      ((equiv hker L₁' L₂').toAlgHom)
  have h : φ = ψ := by
    refine EtaleNil.ext (J θ (R := Tn ϖ T (n + 1))) (hJ hker (n + 1)) fun y ↦ ?_
    have e : JE θ ϖ T (n + 1) L₂.E = JE θ ϖ T n L₂.E := JE_succ (θ := θ) (ϖ := ϖ) T n L₂.E
    change Ideal.Quotient.mk (JE θ ϖ T (n + 1) L₂.E) (φ y) =
      Ideal.Quotient.mk (JE θ ϖ T (n + 1) L₂.E) (ψ y)
    rw [Ideal.Quotient.eq, e, ← Ideal.Quotient.eq]
    apply L₂.σ.injective
    change L₂.σ (Ideal.Quotient.mk _ (equiv hker L₁ L₂ (succ T hϖ C b hker L₁' L₁ y))) =
      L₂.σ (Ideal.Quotient.mk _ (succ T hϖ C b hker L₂' L₂ (equiv hker L₁' L₂' y)))
    rw [σ_equiv, σ_succ, σ_succ, σ_equiv]
  exact congrArg (fun g ↦ g x) h

end Lift

/-! ### The transition maps of the levels -/

section LevelSucc

variable {B : Type u} [CommRing B] [Algebra T B]

omit [Algebra (Ts θ T) C] in
lemma In_succ_le (n : ℕ) :
    (In ϖ T (n + 1)).map (algebraMap T B) ≤ (In ϖ T n).map (algebraMap T B) :=
  Ideal.map_mono (Ideal.map_mono (Iv_le n))

variable (b B) in
/-- **The transition map `Pn (n + 1) → Pn n`** of the levels `(B/ϖⁿ⁺¹B)[1/b]`. -/
def levelSucc (n : ℕ) : Pn ϖ T B b (n + 1) →+* Pn ϖ T B b n :=
  IsLocalization.map (M := Submonoid.powers (Ideal.Quotient.mk
      ((In ϖ T (n + 1)).map (algebraMap T B)) (algebraMap T B b)))
    (T := Submonoid.powers (Ideal.Quotient.mk ((In ϖ T n).map (algebraMap T B))
      (algebraMap T B b)))
    (Pn ϖ T B b n) (Ideal.Quotient.factor (In_succ_le n))
    (Submonoid.powers_le.2 (by
      rw [Submonoid.mem_comap, Ideal.Quotient.factor_mk]
      exact Submonoid.mem_powers _))

omit [Algebra (Ts θ T) C] in
lemma levelSucc_mk (n : ℕ) (x : B) :
    levelSucc b B n (algebraMap (B ⧸ (In ϖ T (n + 1)).map (algebraMap T B))
      (Pn ϖ T B b (n + 1)) (Ideal.Quotient.mk _ x)) =
      algebraMap (B ⧸ (In ϖ T n).map (algebraMap T B)) (Pn ϖ T B b n)
        (Ideal.Quotient.mk _ x) :=
  IsLocalization.map_eq _ _

variable (hϖ)

omit [Algebra (Ts θ T) C] in
/-- **`levelSucc` is compatible with the identifications `levelσ`.** -/
lemma levelσ_levelSucc (n : ℕ) (p : Pn ϖ T B b (n + 1)) :
    letI := algC T hϖ (CB θ T B) n
    letI := algC T hϖ (CB θ T B) (n + 1)
    levelσ hϖ b B n (Ideal.Quotient.mk _ (levelSucc b B n p)) =
      levelσ hϖ b B (n + 1) (Ideal.Quotient.mk _ p) := by
  letI := algC T hϖ (CB θ T B) n
  letI := algC T hϖ (CB θ T B) (n + 1)
  have h : ((levelσ hϖ b B n).toRingHom.comp
      ((Ideal.Quotient.mk (JE θ ϖ T n (Pn ϖ T B b n))).comp (levelSucc b B n))) =
      (levelσ hϖ b B (n + 1)).toRingHom.comp
        (Ideal.Quotient.mk (JE θ ϖ T (n + 1) (Pn ϖ T B b (n + 1)))) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk
      ((In ϖ T (n + 1)).map (algebraMap T B)) (algebraMap T B b))) ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [levelSucc_mk]
    exact (levelσ_mk hϖ b B n x).trans (levelσ_mk hϖ b B (n + 1) x).symm
  exact congrArg (fun g ↦ g p) h

omit [Algebra (Ts θ T) C] in
variable (b B) in
/-- `levelSucc` as a map of `Tn (n + 1)`-algebras. -/
def levelSuccₐ (n : ℕ) :
    letI : Algebra (Tn ϖ T (n + 1)) (Pn ϖ T B b n) :=
      ((algebraMap (Tn ϖ T n) (Pn ϖ T B b n)).comp
        (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n))).toAlgebra
    Pn ϖ T B b (n + 1) →ₐ[Tn ϖ T (n + 1)] Pn ϖ T B b n :=
  letI : Algebra (Tn ϖ T (n + 1)) (Pn ϖ T B b n) :=
    ((algebraMap (Tn ϖ T n) (Pn ϖ T B b n)).comp
      (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n))).toAlgebra
  { levelSucc b B n with
    commutes' := fun t ↦ by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
      exact levelSucc_mk n (algebraMap T B s) }

variable (hker : RingHom.ker θ ≤ Ideal.span {ϖ})

/-- **The transition maps of the levels are the successor maps of the étale lifts**:
`levelSucc = succ (levelLift (n + 1)) (levelLift n)`. -/
theorem levelSucc_eq_succ [Module.Finite T B] (n : ℕ)
    [Algebra.FormallyEtale (Tn ϖ T (n + 1)) (Pn ϖ T B b (n + 1))]
    [Algebra.FormallyEtale (Tn ϖ T n) (Pn ϖ T B b n)] (p : Pn ϖ T B b (n + 1)) :
    levelSucc b B n p =
      succ T hϖ (CB θ T B) b hker (levelLift hϖ b (n + 1)) (levelLift hϖ b n) p := by
  letI : Algebra (Tn ϖ T (n + 1)) (Pn ϖ T B b n) :=
    ((algebraMap (Tn ϖ T n) (Pn ϖ T B b n)).comp
      (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n))).toAlgebra
  letI := algC T hϖ (CB θ T B) n
  letI := algC T hϖ (CB θ T B) (n + 1)
  have h : levelSuccₐ b B n =
      succ T hϖ (CB θ T B) b hker (levelLift hϖ b (n + 1)) (levelLift hϖ b n) := by
    refine EtaleNil.ext (J θ (R := Tn ϖ T (n + 1))) (hJ hker (n + 1)) fun y ↦ ?_
    have e : JE θ ϖ T (n + 1) (Pn ϖ T B b n) = JE θ ϖ T n (Pn ϖ T B b n) :=
      JE_succ (θ := θ) (ϖ := ϖ) T n (Pn ϖ T B b n)
    change Ideal.Quotient.mk (JE θ ϖ T (n + 1) (Pn ϖ T B b n)) (levelSucc b B n y) =
      Ideal.Quotient.mk (JE θ ϖ T (n + 1) (Pn ϖ T B b n))
        (succ T hϖ (CB θ T B) b hker (levelLift hϖ b (n + 1)) (levelLift hϖ b n) y)
    rw [Ideal.Quotient.eq, e, ← Ideal.Quotient.eq]
    apply (levelσ hϖ b B n).injective
    rw [levelσ_levelSucc]
    exact (σ_succ T hϖ (CB θ T B) b hker (levelLift hϖ b (n + 1)) (levelLift hϖ b n) y).symm
  exact congrArg (fun g ↦ g p) h

/-- **`levelEquiv` is compatible with the transition maps**: for étale lifts `L'`, `L` at the
levels `n + 1`, `n`, `levelEquiv ∘ levelSucc = succ ∘ levelEquiv`. -/
theorem levelEquiv_levelSucc [Module.Finite T B] (n : ℕ)
    [Algebra.FormallyEtale (Tn ϖ T (n + 1)) (Pn ϖ T B b (n + 1))]
    [Algebra.FormallyEtale (Tn ϖ T n) (Pn ϖ T B b n)]
    (L' : Lift T hϖ (CB θ T B) b (n + 1)) (L : Lift T hϖ (CB θ T B) b n)
    (p : Pn ϖ T B b (n + 1)) :
    levelEquiv hϖ b hker n L (levelSucc b B n p) =
      succ T hϖ (CB θ T B) b hker L' L (levelEquiv hϖ b hker (n + 1) L' p) := by
  rw [levelSucc_eq_succ hϖ hker n p]
  exact Lift.equiv_succ hker (levelLift hϖ b (n + 1)) L' (levelLift hϖ b n) L p

end LevelSucc

end

end EtaleTower

end SemistableReduction
