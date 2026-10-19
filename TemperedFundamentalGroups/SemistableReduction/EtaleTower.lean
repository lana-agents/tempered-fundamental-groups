/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleNilStep
import TemperedFundamentalGroups.SemistableReduction.AdmissibleEtaleLift
import TemperedFundamentalGroups.SemistableReduction.AdmissibleLift

/-!
# Towers of étale lifts of a special-fibre covering over a basic open (Blueprint §12.8, M2.3 (f))

Setting: `θ : O → k` onto a field, `ϖ ∈ ker θ` with `ker θ ⊆ (ϖ)`, a Noetherian `O`-algebra `T`
(a chart), its levels `Tn n = T/ϖⁿ⁺¹T` and its special fibre `Ts = T/(ker θ)T`; a `Ts`-algebra
`C` (a covering of the special fibre of the chart) which is finite over `Ts` and étale over the
basic open `D(b̄)` (`b ∈ T`).

* `EtaleTower.q n : Tn n → Ts`, surjective with kernel `J = (ker θ) Tn n` (`ker_q`), nilpotent
  (`hJ`); `C` is a `Tn n`-algebra through `q n` (`algC`);
* **`EtaleTower.lift n`**: a formally étale `Tn n`-algebra `E`, in which `b` is a unit, finite over
  `(Tn n)[1/b]` (`hfin`), with `σ : E/JE ≃ C[1/b̄]` (`AwayLift.exists_lift`, the choice at level
  `n`);
* **`EtaleTower.succ n : E (n+1) → E n`**: the unique lift compatible with the `σ`
  (`σ_succ`), **surjective with kernel `ϖⁿ⁺¹ E (n+1)`** (`surjective_succ`, `ker_succ`,
  `ker_succ_base`; `EtaleNil.surjective_of_red`, `EtaleNil.ker_of_red`).

This is the étale part of the level-`n` coverings away from the nodes and the marked points.
-/

universe u

namespace SemistableReduction

open AdmissibleLift

namespace EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {ϖ : O}
  (T : Type u) [CommRing T] [Algebra O T]

variable (ϖ) in
/-- The ideal `ϖⁿ⁺¹` of `O`. -/
abbrev Iv (n : ℕ) : Ideal O := Ideal.span {ϖ} ^ (n + 1)

variable (ϖ) in
/-- **The level `n`** of the chart: `T/ϖⁿ⁺¹T`. -/
abbrev Tn (n : ℕ) : Type u := T ⧸ (Iv ϖ n).map (algebraMap O T)

variable (θ) in
/-- **The special fibre** of the chart: `T/(ker θ)T`. -/
abbrev Ts : Type u := T ⧸ J θ (R := T)

lemma Iv_le (n : ℕ) : Iv ϖ (n + 1) ≤ Iv ϖ n := Ideal.pow_le_pow_right (Nat.le_succ _)

lemma map_Iv_le (n : ℕ) :
    (Iv ϖ (n + 1)).map (algebraMap O T) ≤ (Iv ϖ n).map (algebraMap O T) :=
  Ideal.map_mono (Iv_le n)

/-- The surjection `Tn (n+1) → Tn n`. -/
instance algSucc (n : ℕ) : Algebra (Tn ϖ T (n + 1)) (Tn ϖ T n) :=
  (Ideal.Quotient.factor (map_Iv_le T n)).toAlgebra

instance (n : ℕ) : IsScalarTower O (Tn ϖ T (n + 1)) (Tn ϖ T n) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

lemma algebraMap_succ_mk (n : ℕ) (x : T) :
    algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n) (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

lemma surjective_succ_T (n : ℕ) :
    Function.Surjective (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n)) :=
  Ideal.Quotient.factor_surjective (map_Iv_le T n)

/-- The kernel of `Tn (n+1) → Tn n` is `ϖⁿ⁺¹ Tn (n+1)`. -/
lemma ker_succ_T (n : ℕ) : RingHom.ker (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n)) =
    (Iv ϖ n).map (algebraMap O (Tn ϖ T (n + 1))) := by
  change RingHom.ker (Ideal.Quotient.factor (map_Iv_le T n)) = _
  rw [Ideal.Quotient.factor_ker, Ideal.map_map]
  rfl

/-- `ϖⁿ⁺¹` kills `Tn n`. -/
lemma kill (n : ℕ) : (Iv ϖ n).map (algebraMap O (Tn ϖ T n)) = ⊥ := by
  rw [show algebraMap O (Tn ϖ T n) = (Ideal.Quotient.mk _).comp (algebraMap O T) from rfl,
    ← Ideal.map_map]
  exact Ideal.map_quotient_self _

variable {T}

/-- `J` is nilpotent at level `n` if `ker θ ⊆ (ϖ)`. -/
lemma hJ (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) (n : ℕ) :
    J θ (R := Tn ϖ T n) ^ (n + 1) = ⊥ := by
  rw [J, ← Ideal.map_pow, eq_bot_iff]
  refine (Ideal.map_mono (Ideal.pow_right_mono hker (n + 1))).trans ?_
  rw [kill T n]

variable (T)
variable (hϖ : θ ϖ = 0)
include hϖ

lemma Iv_le_ker (n : ℕ) : Iv ϖ n ≤ RingHom.ker θ := by
  refine (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
  exact hϖ

/-- **The reduction `Tn n → Ts`**. -/
def q (n : ℕ) : Tn ϖ T n →+* Ts θ T :=
  Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun _ hx ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.map_mono (Iv_le_ker hϖ n) hx)

lemma q_mk (n : ℕ) (x : T) : q T hϖ n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

lemma q_surjective (n : ℕ) : Function.Surjective (q T hϖ n) := fun y ↦ by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

lemma q_succ (n : ℕ) (x : Tn ϖ T (n + 1)) :
    q T hϖ n (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n) x) = q T hϖ (n + 1) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [algebraMap_succ_mk, q_mk, q_mk]

/-- **The kernel of `Tn n → Ts` is `J`.** -/
lemma ker_q (n : ℕ) : RingHom.ker (q T hϖ n) = J θ (R := Tn ϖ T n) := by
  rw [q, Ideal.ker_quotient_lift, Ideal.mk_ker, J, J, Ideal.map_map]
  rfl

/-- `Tn n/J → Ts`. -/
def qbar (n : ℕ) : (Tn ϖ T n ⧸ J θ (R := Tn ϖ T n)) →+* Ts θ T :=
  Ideal.Quotient.lift _ (q T hϖ n) fun _ hx ↦ by rwa [← RingHom.mem_ker, ker_q]

lemma qbar_bijective (n : ℕ) : Function.Bijective (qbar T hϖ n) := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq, ← ker_q T hϖ n, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hxy
  · obtain ⟨x, rfl⟩ := q_surjective T hϖ n y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩

/-! ### The special-fibre covering as an algebra over the levels -/

variable (C : Type u) [CommRing C] [Algebra (Ts θ T) C]

/-- `C` as a `Tn n`-algebra (through `q n`). -/
@[reducible] def algC (n : ℕ) : Algebra (Tn ϖ T n) C :=
  ((algebraMap (Ts θ T) C).comp (q T hϖ n)).toAlgebra

/-- `C` as a `Tn n/J`-algebra (through `q̄ n`). -/
@[reducible] def algCbar (n : ℕ) : Algebra (Tn ϖ T n ⧸ J θ (R := Tn ϖ T n)) C :=
  ((algebraMap (Ts θ T) C).comp (qbar T hϖ n)).toAlgebra

lemma isScalarTower_C (n : ℕ) :
    letI := algC T hϖ C n
    letI := algCbar T hϖ C n
    IsScalarTower (Tn ϖ T n) (Tn ϖ T n ⧸ J θ (R := Tn ϖ T n)) C :=
  letI := algC T hϖ C n
  letI := algCbar T hϖ C n
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

lemma finite_C [Module.Finite (Ts θ T) C] (n : ℕ) :
    letI := algCbar T hϖ C n
    Module.Finite (Tn ϖ T n ⧸ J θ (R := Tn ϖ T n)) C := by
  letI := algCbar T hϖ C n
  have h : (algebraMap (Tn ϖ T n ⧸ J θ (R := Tn ϖ T n)) C).Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance)
      (RingHom.Finite.of_surjective _ (qbar_bijective T hϖ n).2)
  exact RingHom.finite_algebraMap.mp h

omit hϖ in
/-- `awayMap` of a bijective ring map is bijective. -/
lemma awayMap_bijective {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    (hg : Function.Bijective g) (r : R) : Function.Bijective (Localization.awayMap g r) := by
  refine ⟨Localization.awayMap_injective_iff.mpr fun a ha ↦ ⟨0, ?_⟩,
    Localization.awayMap_surjective_iff.mpr fun a ↦ ?_⟩
  · rw [pow_zero, one_mul]
    exact hg.1 (ha.trans (map_zero g).symm)
  · obtain ⟨b, rfl⟩ := hg.2 a
    exact ⟨b, 0, by rw [pow_zero, one_mul]⟩

variable (b : T)

lemma etale_C (hC : (Localization.awayMap (algebraMap (Ts θ T) C)
    (Ideal.Quotient.mk _ b)).Etale) (n : ℕ) :
    letI := algCbar T hϖ C n
    (Localization.awayMap (algebraMap (Tn ϖ T n ⧸ J θ (R := Tn ϖ T n)) C)
      (AwayLift.fb (J θ) (Ideal.Quotient.mk _ b))).Etale := by
  letI := algCbar T hϖ C n
  set x : Tn ϖ T n ⧸ J θ (R := Tn ϖ T n) := AwayLift.fb (J θ) (Ideal.Quotient.mk _ b)
  have hx : qbar T hϖ n x = Ideal.Quotient.mk _ b := rfl
  have hC' : (Localization.awayMap (algebraMap (Ts θ T) C) (qbar T hϖ n x)).Etale := hC
  have heq : Localization.awayMap (algebraMap (Tn ϖ T n ⧸ J θ (R := Tn ϖ T n)) C) x =
      (Localization.awayMap (algebraMap (Ts θ T) C) (qbar T hϖ n x)).comp
        (Localization.awayMap (qbar T hϖ n) x) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers x) (RingHom.ext fun y ↦ ?_)
    simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  rw [heq]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (awayMap_bijective _ (qbar_bijective T hϖ n) x)) hC'

/-! ### The étale lifts at each level -/

variable [IsNoetherianRing T] (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [Module.Finite (Ts θ T) C]
  (hC : (Localization.awayMap (algebraMap (Ts θ T) C) (Ideal.Quotient.mk _ b)).Etale)

omit hϖ in
instance (n : ℕ) : IsNoetherianRing (Tn ϖ T n) := Ideal.Quotient.isNoetherianRing _

omit hϖ in
variable (θ) in
/-- The special-fibre covering over `D(b̄)`: `C[1/b̄]`. -/
abbrev Cb : Type u := Localization.Away (algebraMap (Ts θ T) C (Ideal.Quotient.mk _ b))

omit hϖ in
variable (θ ϖ) in
/-- The ideal `J E` of a `Tn n`-algebra `E`. -/
abbrev JE (n : ℕ) (E : Type u) [CommRing E] [Algebra (Tn ϖ T n) E] : Ideal E :=
  EtaleNil.JB (J θ (R := Tn ϖ T n)) E

include hker hC in
lemma exists_lift (n : ℕ) :
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra (Tn ϖ T n) P),
      Algebra.FormallyEtale (Tn ϖ T n) P ∧
      IsUnit (algebraMap (Tn ϖ T n) P (Ideal.Quotient.mk _ b)) ∧
      (∃ s : Finset P, ∀ p : P, ∃ k : ℕ,
        (Ideal.Quotient.mk _ b : Tn ϖ T n) ^ k • p ∈ Submodule.span (Tn ϖ T n) (s : Set P)) ∧
      Nonempty (letI := algC T hϖ C n; (P ⧸ JE θ ϖ T n P) ≃ₐ[Tn ϖ T n] Cb θ T C b) := by
  letI := algC T hϖ C n
  letI := algCbar T hϖ C n
  haveI := isScalarTower_C T hϖ C n
  haveI := finite_C T hϖ C n
  exact AwayLift.exists_lift (J θ) (Ideal.Quotient.mk _ b) (hJ hker n) (etale_C T hϖ C b hC n)

/-- **An étale lift of `C` over `D(b)` at level `n`**: a formally étale `Tn n`-algebra `E` in
which `b` is a unit, finite over `(Tn n)[1/b]`, with `σ : E/JE ≃ C[1/b̄]`. -/
structure Lift (n : ℕ) where
  E : Type u
  [commRing : CommRing E]
  [algebra : Algebra (Tn ϖ T n) E]
  [etale : Algebra.FormallyEtale (Tn ϖ T n) E]
  σ : letI := algC T hϖ C n; (E ⧸ JE θ ϖ T n E) ≃ₐ[Tn ϖ T n] Cb θ T C b
  hb : IsUnit (algebraMap (Tn ϖ T n) E (Ideal.Quotient.mk _ b))
  hfin : ∃ s : Finset E, ∀ p : E, ∃ k : ℕ,
    (Ideal.Quotient.mk _ b : Tn ϖ T n) ^ k • p ∈ Submodule.span (Tn ϖ T n) (s : Set E)

attribute [instance] Lift.commRing Lift.algebra Lift.etale

/-- **The chosen étale lift at level `n`.** -/
def lift (n : ℕ) : Lift T hϖ C b n where
  E := (exists_lift T hϖ C b hker hC n).choose
  commRing := (exists_lift T hϖ C b hker hC n).choose_spec.choose
  algebra := (exists_lift T hϖ C b hker hC n).choose_spec.choose_spec.choose
  etale := (exists_lift T hϖ C b hker hC n).choose_spec.choose_spec.choose_spec.1
  σ := (exists_lift T hϖ C b hker hC n).choose_spec.choose_spec.choose_spec.2.2.2.some
  hb := (exists_lift T hϖ C b hker hC n).choose_spec.choose_spec.choose_spec.2.1
  hfin := (exists_lift T hϖ C b hker hC n).choose_spec.choose_spec.choose_spec.2.2.1

/-- The level-`n` lift as an algebra over `Tn (n+1)`. -/
@[reducible] def algE {n : ℕ} (L : Lift T hϖ C b n) : Algebra (Tn ϖ T (n + 1)) L.E :=
  ((algebraMap (Tn ϖ T n) L.E).comp (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n))).toAlgebra

omit [IsNoetherianRing T] [Module.Finite (Ts θ T) C] in
lemma isScalarTower_E {n : ℕ} (L : Lift T hϖ C b n) :
    letI := algE T hϖ C b L
    IsScalarTower (Tn ϖ T (n + 1)) (Tn ϖ T n) L.E :=
  letI := algE T hϖ C b L
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

omit hϖ [IsNoetherianRing T] [Module.Finite (Ts θ T) C] in
lemma JE_succ (n : ℕ) (E : Type u) [CommRing E] [Algebra (Tn ϖ T n) E] :
    letI : Algebra (Tn ϖ T (n + 1)) E :=
      ((algebraMap (Tn ϖ T n) E).comp (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n))).toAlgebra
    JE θ ϖ T (n + 1) E = JE θ ϖ T n E := by
  letI : Algebra (Tn ϖ T (n + 1)) E :=
    ((algebraMap (Tn ϖ T n) E).comp (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n))).toAlgebra
  rw [JE, JE, EtaleNil.JB, EtaleNil.JB, J, J, Ideal.map_map, Ideal.map_map,
    show algebraMap (Tn ϖ T (n + 1)) E =
      (algebraMap (Tn ϖ T n) E).comp (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n)) from rfl,
    RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

omit [IsNoetherianRing T] [Module.Finite (Ts θ T) C] in
lemma algebraMap_Cb_succ (n : ℕ) (x : Tn ϖ T (n + 1)) :
    (letI := algC T hϖ C (n + 1); algebraMap (Tn ϖ T (n + 1)) (Cb θ T C b) x) =
      (letI := algC T hϖ C n;
        algebraMap (Tn ϖ T n) (Cb θ T C b) (algebraMap (Tn ϖ T (n + 1)) (Tn ϖ T n) x)) := by
  letI := algC T hϖ C (n + 1)
  letI := algC T hϖ C n
  rw [IsScalarTower.algebraMap_apply (Tn ϖ T (n + 1)) C (Cb θ T C b),
    IsScalarTower.algebraMap_apply (Tn ϖ T n) C (Cb θ T C b)]
  exact congrArg (algebraMap C (Cb θ T C b))
    (congrArg (algebraMap (Ts θ T) C) (q_succ T hϖ n x).symm)

/-- The reduction `E (n+1) → E n/J` of the successor map: `σ_n⁻¹ ∘ σ_{n+1}`. -/
def succ₀ {n : ℕ} (L' : Lift T hϖ C b (n + 1)) (L : Lift T hϖ C b n) :
    letI := algE T hϖ C b L
    L'.E →ₐ[Tn ϖ T (n + 1)] L.E ⧸ JE θ ϖ T (n + 1) L.E :=
  letI := algE T hϖ C b L
  letI := algC T hϖ C n
  letI := algC T hϖ C (n + 1)
  { toRingHom :=
      (Ideal.quotientEquivAlgOfEq (Tn ϖ T n)
        (JE_succ (θ := θ) (ϖ := ϖ) T n L.E)).symm.toRingHom.comp
      (L.σ.symm.toRingHom.comp (L'.σ.toRingHom.comp (Ideal.Quotient.mk _)))
    commutes' := fun r ↦ by
      change (Ideal.quotientEquivAlgOfEq (Tn ϖ T n) (JE_succ (θ := θ) (ϖ := ϖ) T n L.E)).symm
        (L.σ.symm (L'.σ (Ideal.Quotient.mk _ (algebraMap _ L'.E r)))) = _
      rw [Ideal.Quotient.mk_algebraMap, AlgEquiv.commutes, algebraMap_Cb_succ T hϖ C b,
        AlgEquiv.commutes, ← Ideal.Quotient.mk_algebraMap, Ideal.quotientEquivAlgOfEq_symm,
        Ideal.quotientEquivAlgOfEq_mk]
      rfl }

omit [IsNoetherianRing T] [Module.Finite (Ts θ T) C] in
lemma succ₀_apply {n : ℕ} (L' : Lift T hϖ C b (n + 1)) (L : Lift T hϖ C b n) (x : L'.E) :
    letI := algE T hϖ C b L
    letI := algC T hϖ C n
    letI := algC T hϖ C (n + 1)
    (Ideal.quotientEquivAlgOfEq (Tn ϖ T n) (JE_succ (θ := θ) (ϖ := ϖ) T n L.E))
      (succ₀ T hϖ C b L' L x) = L.σ.symm (L'.σ (Ideal.Quotient.mk _ x)) := by
  letI := algE T hϖ C b L
  letI := algC T hϖ C n
  letI := algC T hϖ C (n + 1)
  exact AlgEquiv.apply_symm_apply _ _

/-- **The successor map** `E (n+1) → E n` of a tower of étale lifts: the lift of `σ_n⁻¹ ∘ σ_{n+1}`
(`EtaleNil.lift`). -/
def succ {n : ℕ} (L' : Lift T hϖ C b (n + 1)) (L : Lift T hϖ C b n) :
    letI := algE T hϖ C b L
    L'.E →ₐ[Tn ϖ T (n + 1)] L.E :=
  letI := algE T hϖ C b L
  EtaleNil.lift (J θ (R := Tn ϖ T (n + 1))) (hJ hker (n + 1)) (succ₀ T hϖ C b L' L)

omit [IsNoetherianRing T] [Module.Finite (Ts θ T) C] in
/-- **The successor map is compatible with the identifications `σ`.** -/
lemma σ_succ {n : ℕ} (L' : Lift T hϖ C b (n + 1)) (L : Lift T hϖ C b n) (x : L'.E) :
    letI := algC T hϖ C n
    letI := algC T hϖ C (n + 1)
    L.σ (Ideal.Quotient.mk _ (succ T hϖ C b hker L' L x)) = L'.σ (Ideal.Quotient.mk _ x) := by
  letI := algE T hϖ C b L
  letI := algC T hϖ C n
  letI := algC T hϖ C (n + 1)
  have h := EtaleNil.mk_lift (J θ (R := Tn ϖ T (n + 1))) (hJ hker (n + 1)) (succ₀ T hϖ C b L' L) x
  have h2 := congrArg (Ideal.quotientEquivAlgOfEq (Tn ϖ T n) (JE_succ (θ := θ) (ϖ := ϖ) T n L.E)) h
  rw [succ₀_apply, Ideal.quotientEquivAlgOfEq_mk] at h2
  change L.σ (Ideal.Quotient.mk _ (succ T hϖ C b hker L' L x)) = _
  rw [show succ T hϖ C b hker L' L x = EtaleNil.lift (J θ (R := Tn ϖ T (n + 1)))
    (hJ hker (n + 1)) (succ₀ T hϖ C b L' L) x from rfl, h2, AlgEquiv.apply_symm_apply]

omit [IsNoetherianRing T] [Module.Finite (Ts θ T) C] in
/-- **The successor map is surjective.** -/
theorem surjective_succ {n : ℕ} (L' : Lift T hϖ C b (n + 1)) (L : Lift T hϖ C b n) :
    Function.Surjective (succ T hϖ C b hker L' L) := by
  letI := algE T hϖ C b L
  haveI := isScalarTower_E T hϖ C b L
  letI := algC T hϖ C n
  letI := algC T hϖ C (n + 1)
  refine EtaleNil.surjective_of_red (surjective_succ_T T n) (J θ (R := Tn ϖ T (n + 1)))
    (m := n + 1) ?_ (succ T hϖ C b hker L' L) (fun y ↦ ?_) (fun x hx ↦ ?_)
  · rw [J, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hJ hker n
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (L'.σ.symm (L.σ (Ideal.Quotient.mk _ y)))
    refine ⟨x, ?_⟩
    rw [Ideal.Quotient.eq]
    change _ ∈ JE θ ϖ T (n + 1) L.E
    rw [JE_succ (θ := θ) (ϖ := ϖ) T n L.E, ← Ideal.Quotient.eq]
    apply L.σ.injective
    rw [σ_succ, hx, AlgEquiv.apply_symm_apply]
  · change _ ∈ JE θ ϖ T (n + 1) L.E at hx
    rw [JE_succ (θ := θ) (ϖ := ϖ) T n L.E] at hx
    have h := σ_succ T hϖ C b hker L' L x
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero, eq_comm,
      map_eq_zero_iff _ L'.σ.injective] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h

omit [IsNoetherianRing T] [Module.Finite (Ts θ T) C] in
/-- **The kernel of the successor map is `ϖⁿ⁺¹ E (n+1)`.** -/
theorem ker_succ {n : ℕ} (L' : Lift T hϖ C b (n + 1)) (L : Lift T hϖ C b n) :
    RingHom.ker (succ T hϖ C b hker L' L) =
      ((Iv ϖ n).map (algebraMap O (Tn ϖ T (n + 1)))).map (algebraMap (Tn ϖ T (n + 1)) L'.E) := by
  letI := algE T hϖ C b L
  haveI := isScalarTower_E T hϖ C b L
  letI := algC T hϖ C n
  letI := algC T hϖ C (n + 1)
  rw [← ker_succ_T T n]
  refine EtaleNil.ker_of_red (surjective_succ_T T n) (J θ (R := Tn ϖ T (n + 1)))
    (m := n + 1) ?_ (succ T hϖ C b hker L' L) (fun y ↦ ?_) (fun x hx ↦ ?_)
  · rw [J, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hJ hker n
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (L'.σ.symm (L.σ (Ideal.Quotient.mk _ y)))
    refine ⟨x, ?_⟩
    rw [Ideal.Quotient.eq]
    change _ ∈ JE θ ϖ T (n + 1) L.E
    rw [JE_succ (θ := θ) (ϖ := ϖ) T n L.E, ← Ideal.Quotient.eq]
    apply L.σ.injective
    rw [σ_succ, hx, AlgEquiv.apply_symm_apply]
  · change _ ∈ JE θ ϖ T (n + 1) L.E at hx
    rw [JE_succ (θ := θ) (ϖ := ϖ) T n L.E] at hx
    have h := σ_succ T hϖ C b hker L' L x
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero, eq_comm,
      map_eq_zero_iff _ L'.σ.injective] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h

omit [IsNoetherianRing T] [Module.Finite (Ts θ T) C] in
/-- The kernel of the successor map as the extension of the ideal `ϖⁿ⁺¹ T` of the chart. -/
theorem ker_succ_base {n : ℕ} (L' : Lift T hϖ C b (n + 1)) (L : Lift T hϖ C b n) :
    RingHom.ker (succ T hϖ C b hker L' L) =
      ((Iv ϖ n).map (algebraMap O T)).map
        ((algebraMap (Tn ϖ T (n + 1)) L'.E).comp (algebraMap T (Tn ϖ T (n + 1)))) := by
  rw [ker_succ, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq O T (Tn ϖ T (n + 1))]

end

end EtaleTower

end SemistableReduction
