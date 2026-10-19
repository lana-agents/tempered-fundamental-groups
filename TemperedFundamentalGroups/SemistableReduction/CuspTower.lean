/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.QuadNodeTower
import TemperedFundamentalGroups.SemistableReduction.EtaleTower

/-!
# The tower of patched algebras of a chart without nodes (Blueprint §12.8, M2.3, cusps)

For a Noetherian `O`-algebra `T` (a chart of a model, away from the nodes) with levels
`Tn n = T/ϖⁿ⁺¹T` (`EtaleTower.Tn`) and a coordinate `s ∈ T` whose zero locus on the special fibre
consists of marked points, an admissible covering `cov₀` of the special fibre `Ts = T/J`
**without nodes** (`IsEmpty cov₀.ι`) and with cusp factors `X^e = t` over the marked points
(tame ramification, [Mzk1] §3.9 (1′A)) has a tower of patched algebras (`LevelTower.Data`):

* `CuspTower.eqv n : Ts ≃ₐ[k] Tn n/J` (`EtaleTower.qbar`), compatible with `s` (`hfe`) and with the
  surjections (`he`);
* the coordinate at the marked points `tn n` (image of `τ ∈ T`, `ht`, `hct`);
* `hreg` from the regularity of `s` on the levels (the completions are flat over the Noetherian
  levels, `AdicCompletion.flat_of_isNoetherian`);
* **`CuspTower.tower`**: the tower data; the Kummer data are vacuous.
-/

universe u

namespace SemistableReduction

open AdmissibleLift EtaleTower

noncomputable section

namespace CuspTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} (T : Type u) [CommRing T] [Algebra O T]
  (hϖ : θ ϖ = 0)

/-- `Ts ≃ Tn n/J` as rings. -/
def eqvR (n : ℕ) : Ts θ T ≃+* (Tn ϖ T n ⧸ J θ (R := Tn ϖ T n)) :=
  (RingEquiv.ofBijective (qbar T hϖ n) (qbar_bijective T hϖ n)).symm

omit hθ in
lemma eqvR_mk (n : ℕ) (x : T) :
    eqvR T hϖ n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x) :=
  (RingEquiv.ofBijective (qbar T hϖ n) (qbar_bijective T hϖ n)).symm_apply_eq.mpr rfl

/-- **`Ts ≃ₐ[k] Tn n/J`.** -/
def eqv (n : ℕ) : Ts θ T ≃ₐ[k] (Tn ϖ T n ⧸ J θ (R := Tn ϖ T n)) :=
  AlgEquiv.ofRingEquiv (f := eqvR T hϖ n) fun c ↦ by
    obtain ⟨o, rfl⟩ := hθ.out c
    rw [QuadNodeTower.algK_θ, QuadNodeTower.algK_θ, eqvR_mk]
    rfl

lemma eqv_mk (n : ℕ) (x : T) :
    eqv T hϖ n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x) :=
  eqvR_mk T hϖ n x

variable (s τ : T)

/-- The coordinate `s` at level `n`. -/
abbrev fn (n : ℕ) : Tn ϖ T n := Ideal.Quotient.mk _ s

lemma hfe (n : ℕ) : eqv T hϖ n (fbar θ s) = fbar θ (fn (ϖ := ϖ) T s n) :=
  eqv_mk T hϖ n s

lemma he (n : ℕ) (r : Tn ϖ T (n + 1)) :
    eqv T hϖ n ((eqv T hϖ (n + 1)).symm (Ideal.Quotient.mk _ r)) =
      Ideal.Quotient.mk _ (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n) r) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [show (Ideal.Quotient.mk (J θ) (Ideal.Quotient.mk _ x) :
      Tn ϖ T (n + 1) ⧸ J θ) = eqv T hϖ (n + 1) (Ideal.Quotient.mk _ x) from
    (eqv_mk T hϖ (n + 1) x).symm, AlgEquiv.symm_apply_apply, eqv_mk]
  rfl

/-- The coordinate at the marked points of the special fibre, `X ↦ τ̄`. -/
abbrev ψb : Polynomial k →ₐ[k] Admissible.Hat (fbar θ s) :=
  Polynomial.aeval (algebraMap (Ts θ T) (Admissible.Hat (fbar θ s)) (Ideal.Quotient.mk _ τ))

/-- The coordinate at the marked points at level `n`. -/
abbrev tn (n : ℕ) : FormalPatchLevel.Hat (fn (ϖ := ϖ) T s n) :=
  algebraMap (Tn ϖ T n) _ (Ideal.Quotient.mk _ τ)

lemma ht (n : ℕ) : ψ θ (fn (ϖ := ϖ) T s n) (tn (ϖ := ϖ) T s τ n) =
    Admissible.ψT (h := hfe T hϖ s n) (ψb (θ := θ) T s τ) Polynomial.X := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (Tn ϖ T n) (Tn ϖ T n ⧸ J θ),
    AlgHom.comp_apply, Polynomial.aeval_X, AlgEquiv.coe_toAlgHom,
    Admissible.hatEquiv_algebraMap, eqv_mk]
  rfl

omit hθ in
lemma hct (n : ℕ) : LevelStep.ψ₂ (fn (ϖ := ϖ) T s (n + 1)) (fn (ϖ := ϖ) T s n) rfl
    (tn (ϖ := ϖ) T s τ (n + 1)) = tn (ϖ := ϖ) T s τ n := by
  rw [LevelStep.ψ₂_algebraMap]
  rfl

variable [IsNoetherianRing T]

omit hθ in
/-- `s` is regular on the completions if it is regular on the levels. -/
lemma hreg (hs : ∀ n, IsSMulRegular (Tn ϖ T n) (fn (ϖ := ϖ) T s n)) (n : ℕ)
    (y : FormalPatchLevel.Hat (fn (ϖ := ϖ) T s n))
    (hy : algebraMap (Tn ϖ T n) _ (fn (ϖ := ϖ) T s n) * y = 0) : y = 0 := by
  have h := (hs n).of_flat (S := FormalPatchLevel.Hat (fn (ϖ := ϖ) T s n))
  refine h ?_
  change _ * y = _ * 0
  rw [hy, mul_zero]

variable {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ s)}
  (cov₀ : Admissible.Covering φ₀ (ψb (θ := θ) T s τ)) [IsEmpty cov₀.ι] (π' : cov₀.ι → O)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  (hs : ∀ n, IsSMulRegular (Tn ϖ T n) (fn (ϖ := ϖ) T s n))

/-- **The tower of patched algebras of a covering without nodes**: cusp factors along the
coordinate `s` at the levels `Tn n = T/ϖⁿ⁺¹T`. -/
def tower : LevelTower.Data (θ := θ) (Tn ϖ T) cov₀ π' where
  f := fn T s
  e := eqv T hϖ
  hfe := hfe T hϖ s
  hπ := fun j ↦ isEmptyElim j
  χ := fun _ j ↦ isEmptyElim j
  hχ := fun _ j ↦ isEmptyElim j
  t := tn T s τ
  ht := ht T hϖ s τ
  m := fun n ↦ n + 1
  hJ := EtaleTower.hJ hker
  I := EtaleTower.Iv ϖ
  hflat := fun _ j ↦ isEmptyElim j
  hfχ := fun _ j ↦ isEmptyElim j
  hreg := hreg T s hs
  hq := surjective_succ_T T
  hf := fun _ ↦ rfl
  he := he T hϖ
  hcχ := fun _ j ↦ isEmptyElim j
  hct := hct T s τ

end CuspTower

end

end SemistableReduction
