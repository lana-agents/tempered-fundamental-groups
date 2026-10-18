/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlap

/-!
# The special-fibre map of a node patch and an étale piece (Blueprint §12.8, M2.3 (f))

The last input of `EtaleOverlap.isLocalization_ρa` is a map of special fibres
`χ̄ : P/JP → Bab/J` which is a localization away from `b`. It comes from the special-fibre
covering: in the setting of `EtaleOverlap` (`A = R[1/a]`, `P` over `A`, `E` over `R` with `b` a
unit, `Bab = E[1/a]`), let

* `C1` be an `R`-algebra (the special-fibre covering over the chart), `Cc` an `A`-algebra (the
  covering on the node chart) and `ι : C1 → Cc` a localization
  away from `a`;
* `σP : P/JP ≃ Cc[1/f]` (the étale part of the node patch) and `σE : E/JE ≃ C1[1/b]` (the étale
  piece), and `f ∣ bᵏ` in `A`.

Then **`OverlapFibre.χ`** `= μ ∘ σP`, where `μ : Cc[1/f] → Bab/J` is induced by
`C1 → C1[1/b] ≃ E/JE → Bab/J`, and **`OverlapFibre.isLocalization_χ`**: `χ` is a localization
away from `b`. Generic localization facts: `away_of_mul` (`S = R[1/x]`, `T = R[1/(x y)]` ⇒
`T = S[1/y]`) and `away_mul_of_isUnit`.
-/

universe u

namespace SemistableReduction

namespace OverlapFibre

noncomputable section

/-! ### Localization facts -/

section Loc

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- **`R[1/(x y)] = R[1/x][1/y]`** for any `R[1/x] → R[1/(x y)]` over `R`. -/
theorem away_of_mul [Algebra S T] [IsScalarTower R S T] (x y : R) [IsLocalization.Away x S]
    [IsLocalization.Away (x * y) T] : IsLocalization.Away (algebraMap R S y) T := by
  let e : Localization.Away (algebraMap R S y) ≃ₐ[R] T :=
    IsLocalization.algEquiv (Submonoid.powers (x * y)) _ T
  have hS : ∀ s : S, e (algebraMap S _ s) = algebraMap S T s := fun s ↦ by
    haveI := IsLocalization.algHom_subsingleton (R := R) (S := S) (P := T) (Submonoid.powers x)
    have : (e.toAlgHom.comp (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S y)))) =
        IsScalarTower.toAlgHom R S T := Subsingleton.elim _ _
    exact AlgHom.congr_fun this s
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap R S y))
    { e with commutes' := hS }

/-- A localization away from `y` is a localization away from `x y` if `x` is a unit in it. -/
theorem away_mul_of_isUnit (x y : R) [IsLocalization.Away y T] (hx : IsUnit (algebraMap R T x)) :
    IsLocalization.Away (x * y) T := by
  have hy : IsUnit (algebraMap R T y) := IsLocalization.Away.algebraMap_isUnit y
  set N : Submonoid R := Submonoid.powers x ⊔ Submonoid.powers y
  have hu : ∀ r ∈ N, IsUnit (algebraMap R T r) := fun r hr ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.mp hr
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    rw [map_mul, map_pow, map_pow]
    exact (hx.pow i).mul (hy.pow j)
  have hN : IsLocalization N T :=
    IsLocalization.of_le (Submonoid.powers y) N le_sup_right hu
  have hle : Submonoid.powers (x * y) ≤ N := by
    rintro _ ⟨i, rfl⟩
    change (x * y) ^ i ∈ N
    rw [mul_pow]
    exact Submonoid.mul_mem _ (Submonoid.mem_sup_left ⟨i, rfl⟩)
      (Submonoid.mem_sup_right ⟨i, rfl⟩)
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers (x * y)) N hle
    fun r hr ↦ ?_).mpr hN
  obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.mp hr
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  refine ⟨(x * y) ^ (i + j), ⟨_, rfl⟩, ?_⟩
  rw [mul_pow, pow_add, pow_add]
  exact mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_left _ _)

end Loc

/-! ### The special-fibre map -/

variable {R : Type u} [CommRing R] (J : Ideal R) (a b : R)
  {A : Type u} [CommRing A] [Algebra R A]
  {P : Type u} [CommRing P] [Algebra R P]
  {E : Type u} [CommRing E] [Algebra R E]
  {C1 : Type u} [CommRing C1] [Algebra R C1]
  {Cc : Type u} [CommRing Cc] [Algebra A Cc] [Algebra R Cc] [IsScalarTower R A Cc]
  (ι : C1 →ₐ[R] Cc) (f : A)
  (σP : (P ⧸ EtaleNil.JB J P) ≃ₐ[R] Localization.Away (algebraMap A Cc f))
  (σE : (E ⧸ EtaleNil.JB J E) ≃ₐ[R] Localization.Away (algebraMap R C1 b))

/-- The special fibre `Bab/J` of the overlap. -/
abbrev Z (E : Type u) [CommRing E] [Algebra R E] : Type u :=
  EtaleOverlap.Bab a E ⧸ EtaleNil.JB J (EtaleOverlap.Bab a E)

/-- `E/JE → Bab/J`. -/
abbrev redE : (E ⧸ EtaleNil.JB J E) →ₐ[R] Z J a E :=
  EtaleNil.red J (IsScalarTower.toAlgHom R E (EtaleOverlap.Bab a E))

/-- `C1 → C1[1/b] ≃ E/JE → Bab/J`. -/
def γ1 : C1 →ₐ[R] Z J a E :=
  (redE J a).comp (σE.symm.toAlgHom.comp (IsScalarTower.toAlgHom R C1 _))

lemma isUnit_a : IsUnit (algebraMap R (Z J a E) a) := by
  rw [IsScalarTower.algebraMap_apply R (EtaleOverlap.Bab a E) (Z J a E),
    IsScalarTower.algebraMap_apply R E (EtaleOverlap.Bab a E)]
  exact (IsLocalization.Away.algebraMap_isUnit _).map _

variable (hι : letI := (ι : C1 →+* Cc).toAlgebra; IsLocalization.Away (algebraMap R C1 a) Cc)

/-- `Cc = C1[1/a] → Bab/J`. -/
def γc : Cc →+* Z J a E :=
  letI := (ι : C1 →+* Cc).toAlgebra
  haveI := hι
  IsLocalization.Away.lift (algebraMap R C1 a) (g := (γ1 J a b σE : C1 →+* Z J a E))
    (by rw [RingHom.coe_coe, AlgHom.commutes]; exact isUnit_a J a)

lemma γc_ι (c : C1) : γc J a b ι σE hι (ι c) = γ1 J a b σE c :=
  letI := (ι : C1 →+* Cc).toAlgebra
  haveI := hι
  IsLocalization.Away.lift_eq (algebraMap R C1 a) _ c

lemma γc_algebraMap (r : R) : γc J a b ι σE hι (algebraMap R Cc r) = algebraMap R (Z J a E) r := by
  rw [← ι.commutes, γc_ι, AlgHom.commutes]

variable (hb : IsUnit (algebraMap R E b)) {k : ℕ} (hdiv : f ∣ algebraMap R A b ^ k)
include hb hdiv

lemma isUnit_f : IsUnit (γc J a b ι σE hι (algebraMap A Cc f)) := by
  have hbZ : IsUnit (algebraMap R (Z J a E) b) := by
    rw [IsScalarTower.algebraMap_apply R E (Z J a E)]
    exact hb.map _
  obtain ⟨c, hc⟩ := hdiv
  have h := congrArg (fun x ↦ γc J a b ι σE hι (algebraMap A Cc x)) hc
  simp only [map_mul, map_pow] at h
  rw [← IsScalarTower.algebraMap_apply, γc_algebraMap] at h
  exact isUnit_of_mul_isUnit_left (h ▸ hbZ.pow k)

/-- `μ : Cc[1/f] → Bab/J`. -/
def μ : Localization.Away (algebraMap A Cc f) →+* Z J a E :=
  IsLocalization.Away.lift (algebraMap A Cc f) (isUnit_f J a b ι f σE hι hb hdiv)

lemma μ_algebraMap (c : Cc) :
    μ J a b ι f σE hι hb hdiv (algebraMap Cc _ c) = γc J a b ι σE hι c :=
  IsLocalization.Away.lift_eq _ _ c

/-- **The special-fibre map** `χ̄ = μ ∘ σP : P/JP → Bab/J`. -/
def χ : (P ⧸ EtaleNil.JB J P) →ₐ[R] Z J a E where
  toRingHom := (μ J a b ι f σE hι hb hdiv).comp σP.toAlgHom.toRingHom
  commutes' r := by
    change μ J a b ι f σE hι hb hdiv (σP (algebraMap R _ r)) = _
    rw [AlgEquiv.commutes,
      IsScalarTower.algebraMap_apply R Cc (Localization.Away (algebraMap A Cc f)) r,
      μ_algebraMap, γc_algebraMap]

/-- **The special-fibre map is a localization away from `b`.** -/
theorem isLocalization_χ :
    letI := (χ J a b ι f σP σE hι hb hdiv).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (P ⧸ EtaleNil.JB J P) b) (Z J a E) := by
  set Lb := Localization.Away (algebraMap R C1 b)
  set Lf := Localization.Away (algebraMap A Cc f)
  -- (i) `C1 → Bab/J` is a localization away from `b a`
  letI aLZ : Algebra Lb (Z J a E) :=
    ((redE J a).toRingHom.comp σE.symm.toAlgHom.toRingHom).toAlgebra
  letI aC1Z : Algebra C1 (Z J a E) := (γ1 J a b σE : C1 →+* Z J a E).toAlgebra
  haveI : IsScalarTower C1 Lb (Z J a E) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI hEZ : letI := (redE J a (E := E)).toRingHom.toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (EtaleNil.JB J E) (algebraMap R E a)) (Z J a E) :=
    EtaleNil.isLocalization_red J (algebraMap R E a)
  haveI hLZ : IsLocalization.Away (algebraMap C1 Lb (algebraMap R C1 a)) (Z J a E) := by
    letI := (redE J a (E := E)).toRingHom.toAlgebra
    have h := IsLocalization.isLocalization_of_base_ringEquiv
      (Submonoid.powers (Ideal.Quotient.mk (EtaleNil.JB J E) (algebraMap R E a))) (Z J a E)
      σE.toRingEquiv
    have e1 : σE.toRingEquiv (Ideal.Quotient.mk _ (algebraMap R E a)) =
        algebraMap C1 Lb (algebraMap R C1 a) := by
      rw [← IsScalarTower.algebraMap_apply]
      change σE (algebraMap R _ a) = _
      rw [AlgEquiv.commutes]
    rw [Submonoid.map_powers, e1] at h
    exact h
  haveI h1 : IsLocalization.Away (algebraMap R C1 a * algebraMap R C1 b) (Z J a E) :=
    IsLocalization.Away.mul Lb (Z J a E) (algebraMap R C1 b) (algebraMap R C1 a)
  -- (ii) `Cc → Bab/J` is a localization away from `b`
  letI aC1Cc : Algebra C1 Cc := (ι : C1 →+* Cc).toAlgebra
  haveI : IsLocalization.Away (algebraMap R C1 a) Cc := hι
  letI aCcZ : Algebra Cc (Z J a E) := (γc J a b ι σE hι).toAlgebra
  haveI : IsScalarTower C1 Cc (Z J a E) := IsScalarTower.of_algebraMap_eq fun c ↦
    (γc_ι J a b ι σE hι c).symm
  have h2 : IsLocalization.Away (algebraMap C1 Cc (algebraMap R C1 b)) (Z J a E) :=
    away_of_mul (S := Cc) (algebraMap R C1 a) (algebraMap R C1 b)
  have hbC : algebraMap C1 Cc (algebraMap R C1 b) = algebraMap R Cc b := ι.commutes b
  rw [hbC] at h2
  -- (iii) `Cc[1/f] → Bab/J` is a localization away from `b`
  letI aLfZ : Algebra Lf (Z J a E) := (μ J a b ι f σE hι hb hdiv).toAlgebra
  haveI : IsScalarTower Cc Lf (Z J a E) := IsScalarTower.of_algebraMap_eq fun c ↦
    (μ_algebraMap J a b ι f σE hι hb hdiv c).symm
  have hfu : IsUnit (algebraMap Cc (Z J a E) (algebraMap A Cc f)) :=
    isUnit_f J a b ι f σE hι hb hdiv
  haveI : IsLocalization.Away (algebraMap A Cc f * algebraMap R Cc b) (Z J a E) :=
    away_mul_of_isUnit _ _ hfu
  have h3 : IsLocalization.Away (algebraMap Cc Lf (algebraMap R Cc b)) (Z J a E) :=
    away_of_mul (S := Lf) (algebraMap A Cc f) (algebraMap R Cc b)
  -- (iv) transport along `σP`
  have h4 := IsLocalization.isLocalization_of_base_ringEquiv
    (Submonoid.powers (algebraMap Cc Lf (algebraMap R Cc b))) (Z J a E) σP.symm.toRingEquiv
  have e4 : σP.symm.toRingEquiv (algebraMap Cc Lf (algebraMap R Cc b)) =
      algebraMap R (P ⧸ EtaleNil.JB J P) b := by
    rw [← IsScalarTower.algebraMap_apply]
    exact σP.symm.commutes b
  rw [Submonoid.map_powers, e4] at h4
  exact h4

end

end OverlapFibre

end SemistableReduction
