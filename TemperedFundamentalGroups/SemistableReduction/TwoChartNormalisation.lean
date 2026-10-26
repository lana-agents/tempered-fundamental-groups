/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KaehlerAlgStr
import TemperedFundamentalGroups.SemistableReduction.TwoChartTower
import TemperedFundamentalGroups.SemistableReduction.TwoChartGlue

/-!
# The normalisation of two-chart rings in a field (Blueprint §12.8, M2.5)

Let `D` be two-chart rings over `A` (a model of `ℙ¹`-type over `A`, charts `D.R0`, `D.R1`,
overlap `D.R01`), `L` a field receiving the three rings compatibly with the restrictions, and
`B₀`, `B₁` the integral closures of `D.R0`, `D.R1` in `L`. Then:

* **`TwoChartNorm.twoChart`**: `(B₀, B₁)` are two-chart rings, with overlap the integral closure
  of `D.R01` in `L` (which is both `B₀[1/x]` and `B₁[1/y]`: `IsIntegral.exists_multiple_integral_of_
  isLocalization`, as `D.R01 = D.R0[1/x] = D.R1[1/y]`), coordinates the images of `x`, `y`, `u`;
* **`TwoChartNorm.toNorm`**: the structure map `D → (B₀, B₁)` of two-chart rings;
* **`TwoChartNorm.finite_x0`**, **`finite_x1`**: the charts of the normalisation are finite over
  `A[X]` if those of `D` are and `B₀`, `B₁` are finite over `D.R0`, `D.R1` (the coherence input of
  `AdicChartAlgSystem.exists_iso_of_algebraization`).
-/

universe u

open Polynomial

namespace SemistableReduction

open ProjectiveLine

namespace TwoChartNorm

noncomputable section

variable {A : Type u} [CommRing A] (D : TwoChartRings A) (L : Type u) [Field L]
  [Algebra D.R01 L]
  (B₀ B₁ : Type u) [CommRing B₀] [CommRing B₁] [Algebra D.R0 L] [Algebra D.R1 L]
  [Algebra D.R0 B₀] [Algebra B₀ L] [IsScalarTower D.R0 B₀ L]
  [Algebra D.R1 B₁] [Algebra B₁ L] [IsScalarTower D.R1 B₁ L]

/-- The `A`-algebra structure of `B₀` through `D.R0`. -/
abbrev alg0 : Algebra A B₀ := ((algebraMap D.R0 B₀).comp (algebraMap A D.R0)).toAlgebra

/-- The `A`-algebra structure of `B₁` through `D.R1`. -/
abbrev alg1 : Algebra A B₁ := ((algebraMap D.R1 B₁).comp (algebraMap A D.R1)).toAlgebra

/-- The `A`-algebra structure of the integral closure of `D.R01` in `L` through `D.R01`. -/
abbrev alg01 : Algebra A (integralClosure D.R01 L) :=
  ((algebraMap D.R01 (integralClosure D.R01 L)).comp (algebraMap A D.R01)).toAlgebra

variable {D L}
  (h0L : ∀ a, algebraMap D.R01 L (D.ρ0 a) = algebraMap D.R0 L a)
  (h1L : ∀ a, algebraMap D.R01 L (D.ρ1 a) = algebraMap D.R1 L a)
  [IsIntegralClosure B₀ D.R0 L] [IsIntegralClosure B₁ D.R1 L]

omit [Algebra D.R1 L] [Algebra D.R0 B₀] [IsScalarTower D.R0 B₀ L] in
include h0L in
lemma isIntegral0 (b : B₀) : IsIntegral D.R01 (algebraMap B₀ L b) :=
  IsIntegral.map_of_comp_eq (ψ := RingHom.id L) D.ρ0.toRingHom
    (RingHom.ext fun a ↦ h0L a) ((IsIntegralClosure.isIntegral_iff (A := B₀)).mpr ⟨b, rfl⟩)

omit [Algebra D.R0 L] [Algebra D.R1 B₁] [IsScalarTower D.R1 B₁ L] in
include h1L in
lemma isIntegral1 (b : B₁) : IsIntegral D.R01 (algebraMap B₁ L b) :=
  IsIntegral.map_of_comp_eq (ψ := RingHom.id L) D.ρ1.toRingHom
    (RingHom.ext fun a ↦ h1L a) ((IsIntegralClosure.isIntegral_iff (A := B₁)).mpr ⟨b, rfl⟩)

/-- The restriction `B₀ → B₀[1/x]` (the integral closure of `D.R01` in `L`). -/
def rho0 : B₀ →+* integralClosure D.R01 L :=
  (algebraMap B₀ L).codRestrict (integralClosure D.R01 L) (isIntegral0 B₀ h0L)

/-- The restriction `B₁ → B₁[1/y]` (the integral closure of `D.R01` in `L`). -/
def rho1 : B₁ →+* integralClosure D.R01 L :=
  (algebraMap B₁ L).codRestrict (integralClosure D.R01 L) (isIntegral1 B₁ h1L)

omit [Algebra D.R1 L] [Algebra D.R0 B₀] [IsScalarTower D.R0 B₀ L] in
lemma coe_rho0 (b : B₀) : (rho0 B₀ h0L b : L) = algebraMap B₀ L b := rfl

omit [Algebra D.R0 L] [Algebra D.R1 B₁] [IsScalarTower D.R1 B₁ L] in
lemma coe_rho1 (b : B₁) : (rho1 B₁ h1L b : L) = algebraMap B₁ L b := rfl

variable (D L) in
/-- The unit `u` in the integral closure of `D.R01`. -/
def unit : (integralClosure D.R01 L)ˣ :=
  Units.map (algebraMap D.R01 (integralClosure D.R01 L)).toMonoidHom D.u

omit [Algebra D.R0 L] [Algebra D.R1 L] in
variable (D L) in
lemma coe_unit : ((unit D L : integralClosure D.R01 L) : L) = algebraMap D.R01 L D.u := rfl

omit [Algebra D.R0 L] [Algebra D.R1 L] in
variable (D L) in
lemma coe_unit_inv :
    ((↑(unit D L)⁻¹ : integralClosure D.R01 L) : L) = algebraMap D.R01 L ↑D.u⁻¹ := rfl

omit [Algebra D.R1 L] [Algebra D.R0 B₀] [IsScalarTower D.R0 B₀ L] in
include h0L in
lemma exists0 (z : integralClosure D.R01 L) :
    ∃ (m : B₀) (k : ℕ), ((unit D L : integralClosure D.R01 L)) ^ k * z = rho0 B₀ h0L m := by
  letI : Algebra D.R0 D.R01 := D.ρ0.toRingHom.toAlgebra
  haveI : IsLocalization.Away D.x D.R01 := D.isLocalization_ρ0
  haveI : IsScalarTower D.R0 D.R01 L := IsScalarTower.of_algebraMap_eq fun a ↦ (h0L a).symm
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Submonoid.powers D.x) (Rₘ := D.R01) (z : L) z.2
  obtain ⟨m, hm⟩ := (IsIntegralClosure.isIntegral_iff (A := B₀)).mp hk
  refine ⟨m, k, Subtype.ext ?_⟩
  rw [coe_rho0 B₀ h0L, hm, Submonoid.smul_def, Algebra.smul_def]
  change (algebraMap D.R01 L D.u) ^ k * (z : L) = _
  rw [map_pow, ← h0L, D.ρ0_x]

omit [Algebra D.R0 L] [Algebra D.R1 B₁] [IsScalarTower D.R1 B₁ L] in
include h1L in
lemma exists1 (z : integralClosure D.R01 L) :
    ∃ (m : B₁) (k : ℕ), ((↑(unit D L)⁻¹ : integralClosure D.R01 L)) ^ k * z = rho1 B₁ h1L m := by
  letI : Algebra D.R1 D.R01 := D.ρ1.toRingHom.toAlgebra
  haveI : IsLocalization.Away D.y D.R01 := D.isLocalization_ρ1
  haveI : IsScalarTower D.R1 D.R01 L := IsScalarTower.of_algebraMap_eq fun a ↦ (h1L a).symm
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Submonoid.powers D.y) (Rₘ := D.R01) (z : L) z.2
  obtain ⟨m, hm⟩ := (IsIntegralClosure.isIntegral_iff (A := B₁)).mp hk
  refine ⟨m, k, Subtype.ext ?_⟩
  rw [coe_rho1 B₁ h1L, hm, Submonoid.smul_def, Algebra.smul_def]
  change (algebraMap D.R01 L ↑D.u⁻¹) ^ k * (z : L) = _
  rw [map_pow, ← h1L, D.ρ1_y]

/-- `rho0` as an `A`-algebra map. -/
def rho0A : letI := alg0 D B₀; letI := alg01 D L; B₀ →ₐ[A] integralClosure D.R01 L :=
  letI := alg0 D B₀
  letI := alg01 D L
  { rho0 B₀ h0L with
    commutes' := fun a ↦ Subtype.ext (by
      change algebraMap B₀ L (algebraMap D.R0 B₀ (algebraMap A D.R0 a)) =
        algebraMap D.R01 L (algebraMap A D.R01 a)
      rw [← IsScalarTower.algebraMap_apply, ← h0L, AlgHom.commutes]) }

/-- `rho1` as an `A`-algebra map. -/
def rho1A : letI := alg1 D B₁; letI := alg01 D L; B₁ →ₐ[A] integralClosure D.R01 L :=
  letI := alg1 D B₁
  letI := alg01 D L
  { rho1 B₁ h1L with
    commutes' := fun a ↦ Subtype.ext (by
      change algebraMap B₁ L (algebraMap D.R1 B₁ (algebraMap A D.R1 a)) =
        algebraMap D.R01 L (algebraMap A D.R01 a)
      rw [← IsScalarTower.algebraMap_apply, ← h1L, AlgHom.commutes]) }

/-- **The normalisation of two-chart rings in a field**: `(B₀, B₁)` with overlap the integral
closure of `D.R01` in `L`. -/
def twoChart : TwoChartRings A where
  R0 := B₀
  R1 := B₁
  R01 := integralClosure D.R01 L
  x := algebraMap D.R0 B₀ D.x
  y := algebraMap D.R1 B₁ D.y
  u := unit D L
  aR0 := alg0 D B₀
  aR1 := alg1 D B₁
  aR01 := alg01 D L
  ρ0 := rho0A B₀ h0L
  ρ1 := rho1A B₁ h1L
  ρ0_x := Subtype.ext (by
    change algebraMap B₀ L (algebraMap D.R0 B₀ D.x) = _
    rw [coe_unit, ← IsScalarTower.algebraMap_apply, ← h0L, D.ρ0_x])
  ρ1_y := Subtype.ext (by
    change algebraMap B₁ L (algebraMap D.R1 B₁ D.y) = _
    rw [coe_unit_inv, ← IsScalarTower.algebraMap_apply, ← h1L, D.ρ1_y])
  exists0 := exists0 B₀ h0L
  ker0 m hm := ⟨0, by
    rw [pow_zero, one_mul]
    refine IsIntegralClosure.algebraMap_injective B₀ D.R0 L ?_
    exact (congrArg Subtype.val hm).trans (map_zero _).symm⟩
  exists1 := exists1 B₁ h1L
  ker1 m hm := ⟨0, by
    rw [pow_zero, one_mul]
    refine IsIntegralClosure.algebraMap_injective B₁ D.R1 L ?_
    exact (congrArg Subtype.val hm).trans (map_zero _).symm⟩

/-- **The structure map** `D → (B₀, B₁)` of two-chart rings. -/
def toNorm : TwoChartMap D (twoChart B₀ B₁ h0L h1L) where
  f0 := { algebraMap D.R0 B₀ with commutes' := fun _ ↦ rfl }
  f1 := { algebraMap D.R1 B₁ with commutes' := fun _ ↦ rfl }
  f01 := { algebraMap D.R01 (integralClosure D.R01 L) with commutes' := fun _ ↦ rfl }
  hx := rfl
  hy := rfl
  hu := rfl
  h0 a := Subtype.ext (by
    change algebraMap D.R01 L (D.ρ0 a) = algebraMap B₀ L (algebraMap D.R0 B₀ a)
    rw [h0L, ← IsScalarTower.algebraMap_apply])
  h1 a := Subtype.ext (by
    change algebraMap D.R01 L (D.ρ1 a) = algebraMap B₁ L (algebraMap D.R1 B₁ a)
    rw [h1L, ← IsScalarTower.algebraMap_apply])

lemma toNorm_f0 (a : D.R0) : (toNorm B₀ B₁ h0L h1L).f0 a = algebraMap D.R0 B₀ a := rfl

lemma toNorm_f1 (a : D.R1) : (toNorm B₀ B₁ h0L h1L).f1 a = algebraMap D.R1 B₁ a := rfl

lemma toNorm_f01 (a : D.R01) :
    Subtype.val (p := (· ∈ integralClosure D.R01 L)) ((toNorm B₀ B₁ h0L h1L).f01 a) =
      algebraMap D.R01 L a :=
  rfl

/-- `aeval (algebraMap R B x) = algebraMap R B ∘ aeval x`. -/
lemma aeval_algebraMap_eq {R B : Type u} [CommRing R] [Algebra A R] [CommRing B] [Algebra R B]
    (x : R) :
    letI : Algebra A B := ((algebraMap R B).comp (algebraMap A R)).toAlgebra
    (Polynomial.aeval (algebraMap R B x) : A[X] →ₐ[A] B).toRingHom =
      (algebraMap R B).comp (Polynomial.aeval x : A[X] →ₐ[A] R).toRingHom := by
  letI : Algebra A B := ((algebraMap R B).comp (algebraMap A R)).toAlgebra
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · change Polynomial.aeval (algebraMap R B x) (Polynomial.C a) =
      algebraMap R B (Polynomial.aeval x (Polynomial.C a))
    rw [Polynomial.aeval_C, Polynomial.aeval_C]
    rfl
  · change Polynomial.aeval (algebraMap R B x) Polynomial.X =
      algebraMap R B (Polynomial.aeval x Polynomial.X)
    rw [Polynomial.aeval_X, Polynomial.aeval_X]

/-- A finite algebra over a ring finite over `A[X]` (`X ↦ x`) is finite over `A[X]`
(`X ↦ x`). -/
lemma finite_aeval_algebraMap {R B : Type u} [CommRing R] [Algebra A R] [CommRing B]
    [Algebra R B] [Module.Finite R B] (x : R)
    (hx : letI := (Polynomial.aeval x : A[X] →ₐ[A] R).toRingHom.toAlgebra; Module.Finite A[X] R) :
    letI : Algebra A B := ((algebraMap R B).comp (algebraMap A R)).toAlgebra
    Module.Finite A[X] (Module.AEval' (LinearMap.mulLeft A (algebraMap R B x))) := by
  letI : Algebra A B := ((algebraMap R B).comp (algebraMap A R)).toAlgebra
  refine TwoChartGlue.finite_aeval_mulLeft _ ?_
  change RingHom.Finite _
  rw [aeval_algebraMap_eq]
  exact RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance) hx

/-- **The first chart of the normalisation is finite over `A[X]`.** -/
theorem finite_x0 [Module.Finite D.R0 B₀]
    (hx : letI := (Polynomial.aeval D.x : A[X] →ₐ[A] D.R0).toRingHom.toAlgebra;
      Module.Finite A[X] D.R0) :
    Module.Finite A[X] (Module.AEval' (twoChart B₀ B₁ h0L h1L).chartModule.x0) :=
  finite_aeval_algebraMap (R := D.R0) (B := B₀) D.x hx

/-- **The second chart of the normalisation is finite over `A[X]`.** -/
theorem finite_x1 [Module.Finite D.R1 B₁]
    (hy : letI := (Polynomial.aeval D.y : A[X] →ₐ[A] D.R1).toRingHom.toAlgebra;
      Module.Finite A[X] D.R1) :
    Module.Finite A[X] (Module.AEval' (twoChart B₀ B₁ h0L h1L).chartModule.x1) :=
  finite_aeval_algebraMap (R := D.R1) (B := B₁) D.y hy

/-! ### Finiteness of the normalisation over the charts -/

omit [Algebra D.R1 L] in
lemma rho0_algebraMap (r : D.R0) :
    rho0 B₀ h0L (algebraMap D.R0 B₀ r) = algebraMap D.R01 (integralClosure D.R01 L) (D.ρ0 r) :=
  Subtype.ext (by
    change algebraMap B₀ L (algebraMap D.R0 B₀ r) = algebraMap D.R01 L (D.ρ0 r)
    rw [h0L, ← IsScalarTower.algebraMap_apply])

omit [Algebra D.R0 L] in
lemma rho1_algebraMap (r : D.R1) :
    rho1 B₁ h1L (algebraMap D.R1 B₁ r) = algebraMap D.R01 (integralClosure D.R01 L) (D.ρ1 r) :=
  Subtype.ext (by
    change algebraMap B₁ L (algebraMap D.R1 B₁ r) = algebraMap D.R01 L (D.ρ1 r)
    rw [h1L, ← IsScalarTower.algebraMap_apply])

omit [Algebra D.R0 L] in
include h1L in
/-- **The overlap of the normalisation is finite over `D.R01`** if `B₁` is finite over
`D.R1`: it is `B₁[1/y]`. -/
theorem finite_overlap [Module.Finite D.R1 B₁] :
    Module.Finite D.R01 (integralClosure D.R01 L) := by
  classical
  obtain ⟨k, t, ht⟩ := Module.Finite.exists_fin (R := D.R1) (M := B₁)
  refine ⟨⟨Finset.univ.image (fun i ↦ rho1 B₁ h1L (t i)), eq_top_iff.2 fun z _ ↦ ?_⟩⟩
  obtain ⟨m, k', hm⟩ := exists1 B₁ h1L z
  have hmt : m ∈ Submodule.span D.R1 (Set.range t) := ht ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmt
  have hz : z = ∑ i, ((D.u : D.R01) ^ k' * D.ρ1 (c i)) • rho1 B₁ h1L (t i) := by
    have h1 : z = ((unit D L : integralClosure D.R01 L)) ^ k' *
        (((↑(unit D L)⁻¹ : integralClosure D.R01 L)) ^ k' * z) := by
      rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
    rw [h1, hm, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul, rho1_algebraMap B₁ h1L, Algebra.smul_def, map_mul, map_pow,
      mul_assoc]
    rfl
  rw [hz]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

end

end TwoChartNorm

/-! ### Finiteness from two localizations -/

namespace FiniteAway

/-- **A power multiple of every element lies in a finitely generated submodule** if the
localization away from `f` is finite: for a ring map `φ : B → B_f` which is a localization away from
`f ∈ R` (over `R → R_f = R[1/f]`) with `B_f` finite over `R_f`, there is a finite `s ⊆ B` with
`fⁿ b ∈ span_R s` for every `b` and some `n`. -/
theorem exists_finset_pow_smul_mem {R B Rf Bf : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing Rf] [CommRing Bf] [Algebra R Rf] [Algebra Rf Bf] (f : R)
    [IsLocalization.Away f Rf] [Module.Finite Rf Bf] (φ : B →+* Bf)
    (hφ : ∀ r, φ (algebraMap R B r) = algebraMap Rf Bf (algebraMap R Rf r))
    (hsurj : ∀ z, ∃ (b : B) (n : ℕ), algebraMap Rf Bf (algebraMap R Rf f) ^ n * z = φ b)
    (hker : ∀ b, φ b = 0 → ∃ n : ℕ, algebraMap R B f ^ n * b = 0) :
    ∃ s : Finset B, ∀ b, ∃ n : ℕ, f ^ n • b ∈ Submodule.span R (s : Set B) := by
  classical
  obtain ⟨k, t, ht⟩ := Module.Finite.exists_fin (R := Rf) (M := Bf)
  choose g n hg using fun i ↦ hsurj (t i)
  let N := ∑ i, n i
  let s' : Fin k → B := fun i ↦ algebraMap R B f ^ (N - n i) * g i
  have hs' : ∀ i, φ (s' i) = algebraMap Rf Bf (algebraMap R Rf f) ^ N * t i := fun i ↦ by
    have hle : n i ≤ N := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (n j)) (Finset.mem_univ i)
    simp only [s', map_mul, map_pow, hφ, ← hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  refine ⟨Finset.univ.image s', fun b ↦ ?_⟩
  have hb : φ b ∈ Submodule.span Rf (Set.range t) := ht ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hb
  obtain ⟨⟨_, j, rfl⟩, hj⟩ :=
    IsLocalization.exist_integer_multiples (Submonoid.powers f) Finset.univ c
  choose a ha using fun i ↦ hj i (Finset.mem_univ i)
  have key : φ (algebraMap R B f ^ (j + N) * b - ∑ i, algebraMap R B (a i) * s' i) = 0 := by
    rw [map_sub, map_sum, map_mul, map_pow, hφ, ← hc, Finset.mul_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hai : algebraMap R Rf (a i) = algebraMap R Rf (f ^ j) * c i := by
      rw [ha i, Algebra.smul_def]
    rw [map_mul, hφ, hai, hs' i, Algebra.smul_def, map_mul]
    simp only [map_pow, pow_add]
    ring
  obtain ⟨m, hm⟩ := hker _ key
  refine ⟨m + (j + N), ?_⟩
  have hsum : f ^ (m + (j + N)) • b = ∑ i, (f ^ m * a i) • s' i := by
    simp only [Algebra.smul_def, map_mul, map_pow]
    rw [← sub_eq_zero, pow_add, ← Finset.sum_congr rfl fun i _ ↦ (mul_assoc _ _ _).symm,
      ← Finset.mul_sum]
    linear_combination hm
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

/-- **Finiteness from two localizations**: `B` is finite over `R` if there are `x, c ∈ R`
generating the unit ideal and finite sets `s, s' ⊆ B` with `xⁿ b ∈ span s`, `cⁿ b ∈ span s'`
for every `b`. -/
theorem finite_of_pair {R B : Type*} [CommRing R] [CommRing B] [Module R B] (x c : R)
    (hxc : Ideal.span {x, c} = ⊤)
    (hx : ∃ s : Finset B, ∀ b, ∃ n : ℕ, x ^ n • b ∈ Submodule.span R (s : Set B))
    (hc : ∃ s : Finset B, ∀ b, ∃ n : ℕ, c ^ n • b ∈ Submodule.span R (s : Set B)) :
    Module.Finite R B := by
  classical
  obtain ⟨s, hs⟩ := hx
  obtain ⟨s', hs'⟩ := hc
  refine ⟨⟨s ∪ s', eq_top_iff.2 fun b _ ↦ ?_⟩⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ {x, c} hxc b fun ⟨r, hr⟩ ↦ ?_
  rcases hr with rfl | hr
  · obtain ⟨n, hn⟩ := hs b
    exact ⟨n, Submodule.span_mono (by simp) hn⟩
  · rw [Set.mem_singleton_iff] at hr
    subst hr
    obtain ⟨n, hn⟩ := hs' b
    exact ⟨n, Submodule.span_mono (by simp) hn⟩

end FiniteAway

namespace TwoChartNorm

noncomputable section

variable {A : Type u} [CommRing A] {D : TwoChartRings A} {L : Type u} [Field L]
  [Algebra D.R01 L] (B₀ B₁ : Type u) [CommRing B₀] [CommRing B₁] [Algebra D.R0 L] [Algebra D.R1 L]
  [Algebra D.R0 B₀] [Algebra B₀ L] [IsScalarTower D.R0 B₀ L]
  [Algebra D.R1 B₁] [Algebra B₁ L] [IsScalarTower D.R1 B₁ L]
  (h0L : ∀ a, algebraMap D.R01 L (D.ρ0 a) = algebraMap D.R0 L a)
  (h1L : ∀ a, algebraMap D.R01 L (D.ρ1 a) = algebraMap D.R1 L a)
  [IsIntegralClosure B₀ D.R0 L] [IsIntegralClosure B₁ D.R1 L]

include h0L h1L in
/-- **The normalisation of the first chart is finite** if that of the second chart is and the
normalisation is finite over a localization `D.R0[1/c]` with `(x, c) = (1)` (the remaining part
of `Spec D.R0`). -/
theorem finite_B₀ [Module.Finite D.R1 B₁] (c : D.R0) (hxc : Ideal.span {D.x, c} = ⊤)
    {Rc Bc : Type*} [CommRing Rc] [CommRing Bc] [Algebra D.R0 Rc] (hRc : IsLocalization.Away c Rc)
    [Algebra Rc Bc] [Module.Finite Rc Bc] [Algebra B₀ Bc]
    (hBc0 : IsLocalization.Away (algebraMap D.R0 B₀ c) Bc)
    (hBc : ∀ r, algebraMap B₀ Bc (algebraMap D.R0 B₀ r) = algebraMap Rc Bc (algebraMap D.R0 Rc r)) :
    Module.Finite D.R0 B₀ := by
  haveI := hRc
  haveI := hBc0
  refine FiniteAway.finite_of_pair D.x c hxc ?_ ?_
  · letI : Algebra D.R0 D.R01 := D.ρ0.toRingHom.toAlgebra
    haveI : IsLocalization.Away D.x D.R01 := D.isLocalization_ρ0
    haveI := finite_overlap B₁ h1L
    refine FiniteAway.exists_finset_pow_smul_mem (Rf := D.R01)
      (Bf := integralClosure D.R01 L) D.x (rho0 B₀ h0L) (rho0_algebraMap B₀ h0L)
      (fun z ↦ ?_) (fun b hb ↦ ⟨0, ?_⟩)
    · obtain ⟨m, k, hm⟩ := exists0 B₀ h0L z
      refine ⟨m, k, ?_⟩
      rw [← hm]
      congr 2
      change algebraMap D.R01 _ (D.ρ0 D.x) = algebraMap D.R01 _ D.u
      rw [D.ρ0_x]
    · rw [pow_zero, one_mul]
      refine IsIntegralClosure.algebraMap_injective B₀ D.R0 L ?_
      exact (congrArg Subtype.val hb).trans (map_zero _).symm
  · refine FiniteAway.exists_finset_pow_smul_mem (Rf := Rc) (Bf := Bc) c (algebraMap B₀ Bc) hBc
      (fun z ↦ ?_) (fun b hb ↦ ?_)
    · obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hb⟩ :=
        IsLocalization.surj (Submonoid.powers (algebraMap D.R0 B₀ c)) z
      refine ⟨b, n, ?_⟩
      rw [← hb, ← hBc, ← map_pow, mul_comm]
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap D.R0 B₀ c)) Bc b).1 hb
      exact ⟨n, hn⟩

end

end TwoChartNorm

end SemistableReduction
