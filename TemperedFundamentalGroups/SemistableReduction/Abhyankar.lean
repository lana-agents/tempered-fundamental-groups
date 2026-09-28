/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.AbhyankarLocal
import TemperedFundamentalGroups.SemistableReduction.RootOfUniformizer

/-!
# Abhyankar's lemma for a discrete valuation ring

Blueprint §9.2. Let `O` be a DVR with fraction field `K` and uniformizer `ϖ`, `L / K` a finite
separable extension and `B` the integral closure of `O` in `L`. Suppose `L / K` is tamely
ramified at every maximal ideal `𝔓` of `B`: `e(𝔓) ∣ e` for some `e` invertible in `O` and
`B ⧸ 𝔓` is separable over `O ⧸ 𝔪`. Let `F` be a field generated over `L` by an element `y` with
`y ^ e = ϖ` (e.g. a factor of `L ⊗_K K'`, `K' = K(ϖ ^ (1 / e))`), and `B'` the integral closure of
`O` in `F` (equivalently of `O' = O[y]`). Then every maximal ideal `𝔔` of `B'` is unramified over
`O'`:

* `Abhyankar.maximalIdeal_atPrime_eq_span`: `y` generates the maximal ideal of `B'_𝔔`;
* `Abhyankar.isSeparable_quotient`: `B' ⧸ 𝔔` is separable over `O ⧸ 𝔪`;
* `Abhyankar.isUnramifiedAt`: with `O' = O[Y] ⧸ (Y ^ e - ϖ)` (a DVR with uniformizer `Y`,
  `SemistableReduction/RootOfUniformizer`) acting on `B'` by `Y ↦ y`, `B'` is unramified over `O'`
  at `𝔔` in Mathlib's sense (`Algebra.IsUnramifiedAt`);
* `Abhyankar.ramificationIdx_eq_one`: `e(𝔔 | O') = 1`.

Tameness is phrased with Mathlib's `Ideal.ramificationIdx` and `Ideal.LiesOver`: the hypothesis
`htame` asks, for every prime `𝔓` of `B` over the maximal ideal `𝔪` of `O`, that
`𝔓.ramificationIdx O ∣ e` and that `B ⧸ 𝔓` be separable over `O ⧸ 𝔪`; `e` is a unit of `O`
(equivalently, nonzero in the residue field).

The proof does not pass to the henselization: at `𝔔` over `𝔓`, write `ϖ = u π ^ n` in the DVR
`R = B_𝔓` (`n = e(𝔓)`) and apply the local Kummer step
`maximalIdeal_eq_span_and_isSeparable_of_pow_eq`
(`SemistableReduction/AbhyankarLocal`) to `R → S = B'_𝔔`.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

namespace Abhyankar

/-- `y` with `y ^ e = ϖ` (`e ≠ 0`) is integral over `O`. -/
lemma isIntegral_y {O F : Type*} [CommRing O] [CommRing F] [Algebra O F] {ϖ : O} {e : ℕ}
    (he : e ≠ 0) {y : F} (hy : y ^ e = algebraMap O F ϖ) : IsIntegral O y :=
  ⟨X ^ e - C ϖ, monic_X_pow_sub_C _ he, by simp [eval₂_sub, hy, Algebra.algebraMap_eq_smul_one]⟩

/-- `y` with `y ^ e = ϖ` is separable over `L` when `e` is invertible in `O`. -/
lemma isSeparable_y {O L F : Type*} [CommRing O] [Field L] [Field F] [Algebra O L] [Algebra L F]
    [Algebra O F] [IsScalarTower O L F] {ϖ : O} (hϖ : algebraMap O L ϖ ≠ 0) {e : ℕ}
    (he : IsUnit (e : O)) {y : F} (hy : y ^ e = algebraMap O F ϖ) : IsSeparable L y := by
  have heL : (e : L) ≠ 0 := by
    have := he.map (algebraMap O L)
    rw [map_natCast] at this
    exact this.ne_zero
  refine (separable_X_pow_sub_C _ heL hϖ).of_dvd (minpoly.dvd _ _ ?_)
  simp [← IsScalarTower.algebraMap_apply, hy]

/-- If `F = L[y]` with `y` separable over `L`, then `F / L` is finite and separable. -/
lemma finite_and_isSeparable {L F : Type*} [Field L] [Field F] [Algebra L F] {y : F}
    (hsep : IsSeparable L y) (hF : Algebra.adjoin L {y} = ⊤) :
    FiniteDimensional L F ∧ Algebra.IsSeparable L F := by
  have hint : IsIntegral L y := hsep.isIntegral
  have htop : IntermediateField.adjoin L {y} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin L {y} := by rw [hF]; trivial
    exact IntermediateField.algebra_adjoin_le_adjoin L {y} hx
  haveI := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable L F).2 hsep
  refine ⟨?_, ⟨fun x ↦ IntermediateField.isSeparable_of_mem_isSeparable L F
    (L := IntermediateField.adjoin L {y}) (by rw [htop]; trivial)⟩⟩
  have hfg := hint.fg_adjoin_singleton
  rw [hF, Algebra.top_toSubmodule] at hfg
  exact Module.finite_def.2 hfg

/-- Clearing denominators: if `F = L[y]` and `L = Frac B`, every `w ∈ F` satisfies
`c w = P(y)` for some nonzero `c ∈ B` and `P ∈ B[X]`. -/
lemma exists_mul_eq_aeval {B L F : Type*} [CommRing B] [IsDomain B] [Field L] [Field F]
    [Algebra B L] [IsFractionRing B L] [Algebra L F] {y : F} (hF : Algebra.adjoin L {y} = ⊤)
    (w : F) :
    ∃ c : B, c ≠ 0 ∧ ∃ P : B[X],
      algebraMap L F (algebraMap B L c) * w = aeval y (P.map (algebraMap B L)) := by
  have hw : w ∈ Algebra.adjoin L {y} := by rw [hF]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hw
  obtain ⟨Q, rfl⟩ := hw
  obtain ⟨b, hb, hbQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors B) Q
  refine ⟨b, nonZeroDivisors.ne_zero hb,
    IsLocalization.integerNormalization (nonZeroDivisors B) Q, ?_⟩
  rw [hbQ, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply B L L[X],
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, aeval_C]
  rfl

section Main

variable {O K L F B B' : Type*}
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra O L] [IsScalarTower O K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing B] [IsDomain B] [Algebra O B] [Algebra B L] [IsScalarTower O B L]
  [IsIntegralClosure B O L]
  [Field F] [Algebra K F] [Algebra L F] [Algebra O F] [IsScalarTower K L F] [IsScalarTower O L F]
  [CommRing B'] [IsDomain B'] [Algebra O B'] [Algebra B' F] [IsScalarTower O B' F]
  [IsIntegralClosure B' O F]

include K L B in
/-- **Abhyankar's lemma** (both conclusions). If `L / K` is tame at every maximal ideal of `B`
with ramification indices dividing `e`, `F = L[y]` with `y ^ e = ϖ`, `B'` is the integral closure
of `O` in `F`, `𝔔` is a maximal ideal of `B'` and `yB' ∈ B'` is `y`, then `yB'` generates the
maximal ideal of `B'_𝔔` and `B' ⧸ 𝔔` is separable over `O ⧸ 𝔪`. -/
theorem maximalIdeal_atPrime_eq_span_and_isSeparable {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ}
    (he : IsUnit (e : O)) {y : F}
    (hy : y ^ e = algebraMap O F ϖ) (hF : Algebra.adjoin L {y} = ⊤)
    (htame : ∀ (𝔓 : Ideal B) [𝔓.IsPrime] [𝔓.LiesOver (maximalIdeal O)],
      𝔓.ramificationIdx O ∣ e ∧ Algebra.IsSeparable (O ⧸ maximalIdeal O) (B ⧸ 𝔓))
    (𝔔 : Ideal B') [𝔔.IsPrime] [𝔔.LiesOver (maximalIdeal O)] (yB' : B')
    (hyB' : algebraMap B' F yB' = y) :
    maximalIdeal (Localization.AtPrime 𝔔) =
        Ideal.span {algebraMap B' (Localization.AtPrime 𝔔) yB'} ∧
      Algebra.IsSeparable (O ⧸ maximalIdeal O) (B' ⧸ 𝔔) := by
  classical
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  -- injectivity of the structure maps
  have hOL : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  have hOF : Function.Injective (algebraMap O F) := by
    rw [IsScalarTower.algebraMap_eq O L F]
    exact (algebraMap L F).injective.comp hOL
  have hOB' : Function.Injective (algebraMap O B') := by
    refine fun a b h ↦ hOF ?_
    rw [IsScalarTower.algebraMap_apply O B' F, h, ← IsScalarTower.algebraMap_apply]
  have hOB : Function.Injective (algebraMap O B) := by
    refine fun a b h ↦ hOL ?_
    rw [IsScalarTower.algebraMap_apply O B L, h, ← IsScalarTower.algebraMap_apply]
  have hϖL : algebraMap O L ϖ ≠ 0 := fun h ↦ hϖ.ne_zero (hOL (h.trans (map_zero _).symm))
  -- `F / K` is finite separable; `B` and `B'` are Dedekind
  obtain ⟨hfin, hsep⟩ := finite_and_isSeparable (isSeparable_y hϖL he hy) hF
  haveI : IsScalarTower O K F := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply O L F, IsScalarTower.algebraMap_apply O K L,
      ← IsScalarTower.algebraMap_apply K L F]
  haveI : FiniteDimensional K F := Module.Finite.trans L F
  haveI : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K L F
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain O K L B
  haveI : IsDedekindDomain B' := IsIntegralClosure.isDedekindDomain O K F B'
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension O K L B
  -- the map `B → B'`
  letI : Algebra B F := ((algebraMap L F).comp (algebraMap B L)).toAlgebra
  haveI : IsScalarTower B L F := .of_algebraMap_eq' rfl
  haveI : IsScalarTower O B F := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply O L F, IsScalarTower.algebraMap_apply O B L]
    rfl
  haveI : Algebra.IsIntegral O B := IsIntegralClosure.isIntegral_algebra O L
  let φ : B →ₐ[O] B' := IsIntegralClosure.lift O B' F
  letI : Algebra B B' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower O B B' := .of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  haveI : IsScalarTower B B' F := .of_algebraMap_eq fun x ↦
    (IsIntegralClosure.algebraMap_lift O B' F x).symm
  -- the primes
  set 𝔓 : Ideal B := 𝔔.under B
  haveI : 𝔓.LiesOver (maximalIdeal O) := Ideal.under_liesOver_of_liesOver B 𝔔 (maximalIdeal O)
  have hmax0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have h𝔔0 : 𝔔 ≠ ⊥ := by
    rintro h
    apply hmax0
    rw [Ideal.over_def 𝔔 (maximalIdeal O), h]
    exact Ideal.comap_bot_of_injective _ hOB'
  have h𝔓0 : 𝔓 ≠ ⊥ := by
    rintro h
    apply hmax0
    rw [Ideal.over_def 𝔓 (maximalIdeal O), h]
    exact Ideal.comap_bot_of_injective _ hOB
  -- the local rings `R = B_𝔓 → S = B'_𝔔`
  let R := Localization.AtPrime 𝔓
  let S := Localization.AtPrime 𝔔
  haveI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B h𝔓0 R
  haveI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B' h𝔔0 S
  letI : Algebra R S := Localization.AtPrime.algebraOfLiesOver 𝔓 𝔔
  haveI : IsLocalHom (algebraMap R S) := Localization.isLocalHom_localRingHom _ _ _ _
  haveI : IsLocalHom (algebraMap O R) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have ha' : algebraMap O B a ∈ 𝔓 := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def 𝔓 (maximalIdeal O)]
      exact hna
    rw [IsScalarTower.algebraMap_apply O B R] at ha
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R 𝔓 _).2 ha' ha
  have hBR : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R 𝔓.primeCompl_le_nonZeroDivisors
  have hB'S : Function.Injective (algebraMap B' S) :=
    IsLocalization.injective S 𝔔.primeCompl_le_nonZeroDivisors
  have hOR : Function.Injective (algebraMap O R) := by
    rw [IsScalarTower.algebraMap_eq O B R]
    exact hBR.comp hOB
  have hOS : Function.Injective (algebraMap O S) := by
    rw [IsScalarTower.algebraMap_eq O B' S]
    exact hB'S.comp hOB'
  have hRS : Function.Injective (algebraMap R S) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hker : RingHom.ker (algebraMap R S) ≠ ⊥ := fun h ↦ hr0 (by
      have h' : r ∈ RingHom.ker (algebraMap R S) := hr
      rwa [h, Ideal.mem_bot] at h')
    have hker' : RingHom.ker (algebraMap R S) = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime _).isMaximal hker)
    have hϖR : algebraMap O R ϖ ∈ maximalIdeal R :=
      (map_mem_nonunits_iff _ _).2 hϖ.not_isUnit
    rw [← hker', RingHom.mem_ker, ← IsScalarTower.algebraMap_apply] at hϖR
    exact hϖ.ne_zero (hOS (hϖR.trans (map_zero _).symm))
  -- `y` in `S`
  set yS : S := algebraMap B' S yB'
  have hyB'e : yB' ^ e = algebraMap O B' ϖ := by
    apply IsIntegralClosure.algebraMap_injective B' O F
    rw [map_pow, hyB', hy, ← IsScalarTower.algebraMap_apply]
  have hyS : yS ^ e = algebraMap O S ϖ := by
    rw [← map_pow, hyB'e, ← IsScalarTower.algebraMap_apply]
  -- the ramification index of `𝔓`
  have hn : IsDiscreteValuationRing.addVal R (algebraMap O R ϖ) = (𝔓.ramificationIdx O : ℕ∞) :=
    (RootOfUniformizer.ramificationIdx_eq_addVal 𝔓 hϖ (Ideal.over_def 𝔓 (maximalIdeal O)).symm
      (fun h ↦ hϖ.ne_zero (hOR (h.trans (map_zero _).symm)))).symm
  obtain ⟨hne, hsep𝔓⟩ := htame 𝔓
  -- `S` is generated by `R[y]` up to denominators
  have hgen : ∀ x : S, ∃ b : R, b ≠ 0 ∧ algebraMap R S b * x ∈ Algebra.adjoin R {yS} := by
    intro x
    obtain ⟨⟨β, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl x
    have hs0 : algebraMap B' F s ≠ 0 := by
      rw [map_ne_zero_iff _ (IsIntegralClosure.algebraMap_injective B' O F)]
      rintro h
      exact s.2 (h ▸ 𝔔.zero_mem)
    obtain ⟨c, hc0, P, hP⟩ :=
      exists_mul_eq_aeval (B := B) hF (algebraMap B' F β * (algebraMap B' F s)⁻¹)
    have hB' : algebraMap B B' c * β = s * aeval yB' P := by
      apply IsIntegralClosure.algebraMap_injective B' O F
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B L F,
        ← aeval_algebraMap_apply, hyB', ← aeval_map_algebraMap L, ← hP]
      field_simp
    refine ⟨algebraMap B R c, (map_ne_zero_iff _ hBR).2 hc0, ?_⟩
    have h1 : algebraMap R S (algebraMap B R c) * IsLocalization.mk' S β s =
        algebraMap B' S (aeval yB' P) := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B B' S,
        IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, hB', map_mul,
        mul_comm]
    rw [h1, ← aeval_algebraMap_apply, ← aeval_map_algebraMap R]
    exact aeval_mem_adjoin_singleton R yS
  obtain ⟨hmaxS, hsepRS⟩ := maximalIdeal_eq_span_and_isSeparable_of_pow_eq hϖ he hn hne hOR hRS
    hyS hgen
  refine ⟨hmaxS, ?_⟩
  -- separability of the residue field extension
  haveI : 𝔔.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔔0
  haveI : 𝔓.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔓0
  haveI : Algebra.IsSeparable (B ⧸ 𝔓) (B' ⧸ 𝔔) :=
    Algebra.isSeparable_residueField_iff.1 hsepRS
  letI := Ideal.Quotient.field (maximalIdeal O)
  letI := Ideal.Quotient.field 𝔓
  letI := Ideal.Quotient.field 𝔔
  haveI : IsScalarTower (O ⧸ maximalIdeal O) (B ⧸ 𝔓) (B' ⧸ 𝔔) := .of_algebraMap_eq fun x ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.trans (O ⧸ maximalIdeal O) (B ⧸ 𝔓) (B' ⧸ 𝔔)

include K L B in
/-- **Abhyankar's lemma: no ramification over `O[y]`.** In the situation of
`maximalIdeal_atPrime_eq_span_and_isSeparable`, `y` generates the maximal ideal of `B'_𝔔`. -/
theorem maximalIdeal_atPrime_eq_span {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (he : IsUnit (e : O))
    {y : F}
    (hy : y ^ e = algebraMap O F ϖ) (hF : Algebra.adjoin L {y} = ⊤)
    (htame : ∀ (𝔓 : Ideal B) [𝔓.IsPrime] [𝔓.LiesOver (maximalIdeal O)],
      𝔓.ramificationIdx O ∣ e ∧ Algebra.IsSeparable (O ⧸ maximalIdeal O) (B ⧸ 𝔓))
    (𝔔 : Ideal B') [𝔔.IsPrime] [𝔔.LiesOver (maximalIdeal O)] (yB' : B')
    (hyB' : algebraMap B' F yB' = y) :
    maximalIdeal (Localization.AtPrime 𝔔) =
      Ideal.span {algebraMap B' (Localization.AtPrime 𝔔) yB'} :=
  (maximalIdeal_atPrime_eq_span_and_isSeparable (K := K) hϖ he hy hF htame 𝔔 yB' hyB').1

include K L B in
/-- **Abhyankar's lemma: separable residue fields.** In the situation of
`maximalIdeal_atPrime_eq_span_and_isSeparable`, `B' ⧸ 𝔔` is separable over `O ⧸ 𝔪`. -/
theorem isSeparable_quotient {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (he : IsUnit (e : O)) {y : F}
    (hy : y ^ e = algebraMap O F ϖ) (hF : Algebra.adjoin L {y} = ⊤)
    (htame : ∀ (𝔓 : Ideal B) [𝔓.IsPrime] [𝔓.LiesOver (maximalIdeal O)],
      𝔓.ramificationIdx O ∣ e ∧ Algebra.IsSeparable (O ⧸ maximalIdeal O) (B ⧸ 𝔓))
    (𝔔 : Ideal B') [𝔔.IsPrime] [𝔔.LiesOver (maximalIdeal O)] :
    Algebra.IsSeparable (O ⧸ maximalIdeal O) (B' ⧸ 𝔔) := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  exact (maximalIdeal_atPrime_eq_span_and_isSeparable (K := K) hϖ he hy hF htame 𝔔
    (IsIntegralClosure.mk' B' y (isIntegral_y he0 hy)) (IsIntegralClosure.algebraMap_mk' _ _ _)).2

end Main

section Unramified

/-- The `O[Y] ⧸ (Y ^ e - ϖ)`-algebra structure on an `O`-algebra `A` with `Y ↦ a`, for
`a ^ e = ϖ`. -/
@[implicit_reducible]
noncomputable def rootAlgebra {O A : Type*} [CommRing O] [CommRing A] [Algebra O A] {ϖ : O}
    {e : ℕ} (a : A) (ha : a ^ e = algebraMap O A ϖ) : Algebra (RootOfUniformizer.Ring ϖ e) A :=
  (AdjoinRoot.liftAlgHom _ (Algebra.ofId O A) a (by simp [ha])).toRingHom.toAlgebra

lemma rootAlgebra_isScalarTower {O A : Type*} [CommRing O] [CommRing A] [Algebra O A] {ϖ : O}
    {e : ℕ} (a : A) (ha : a ^ e = algebraMap O A ϖ) :
    letI := rootAlgebra a ha
    IsScalarTower O (RootOfUniformizer.Ring ϖ e) A :=
  letI := rootAlgebra a ha
  .of_algebraMap_eq fun x ↦
    ((AdjoinRoot.liftAlgHom _ (Algebra.ofId O A) a (by simp [ha])).commutes x).symm

lemma rootAlgebra_algebraMap_root {O A : Type*} [CommRing O] [CommRing A] [Algebra O A] {ϖ : O}
    {e : ℕ} (a : A) (ha : a ^ e = algebraMap O A ϖ) :
    letI := rootAlgebra a ha
    algebraMap (RootOfUniformizer.Ring ϖ e) A (AdjoinRoot.root _) = a :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

variable {O K L F B B' : Type*}
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra O L] [IsScalarTower O K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing B] [IsDomain B] [Algebra O B] [Algebra B L] [IsScalarTower O B L]
  [IsIntegralClosure B O L]
  [Field F] [Algebra K F] [Algebra L F] [Algebra O F] [IsScalarTower K L F] [IsScalarTower O L F]
  [CommRing B'] [IsDomain B'] [Algebra O B'] [Algebra B' F] [IsScalarTower O B' F]
  [IsIntegralClosure B' O F]

omit [IsDomain B'] in
include K L in
/-- In the situation of Abhyankar's lemma, `B'` is finite over `O`. -/
lemma finite_integralClosure {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (he : IsUnit (e : O)) {y : F}
    (hy : y ^ e = algebraMap O F ϖ) (hF : Algebra.adjoin L {y} = ⊤) : Module.Finite O B' := by
  have hOL : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  have hϖL : algebraMap O L ϖ ≠ 0 := fun h ↦ hϖ.ne_zero (hOL (h.trans (map_zero _).symm))
  obtain ⟨hfin, hsepLF⟩ := finite_and_isSeparable (isSeparable_y hϖL he hy) hF
  haveI : IsScalarTower O K F := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply O L F, IsScalarTower.algebraMap_apply O K L,
      ← IsScalarTower.algebraMap_apply K L F]
  haveI : FiniteDimensional K F := Module.Finite.trans L F
  haveI : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K L F
  exact IsIntegralClosure.finite O K F B'

include K L B in
/-- **Abhyankar's lemma for a DVR.** Let `O` be a DVR with uniformizer `ϖ`, `L / K` a finite
separable extension of its fraction field, `B` the integral closure of `O` in `L`, and suppose
`L / K` is tamely ramified at every maximal ideal `𝔓` of `B` with `e(𝔓) ∣ e`, `e` invertible in
`O`. Let `F = L[y]` be a field with `y ^ e = ϖ`, `B'` the integral closure of `O` in `F`, and
`O' = O[Y] ⧸ (Y ^ e - ϖ)` acting on `B'` by `Y ↦ y`. Then `B'` is unramified over `O'` at every
maximal ideal `𝔔`. -/
theorem isUnramifiedAt {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (he : IsUnit (e : O)) (yB' : B')
    (hyB' : yB' ^ e = algebraMap O B' ϖ) (hF : Algebra.adjoin L {algebraMap B' F yB'} = ⊤)
    (htame : ∀ (𝔓 : Ideal B) [𝔓.IsPrime] [𝔓.LiesOver (maximalIdeal O)],
      𝔓.ramificationIdx O ∣ e ∧ Algebra.IsSeparable (O ⧸ maximalIdeal O) (B ⧸ 𝔓))
    (𝔔 : Ideal B') [𝔔.IsPrime] [𝔔.LiesOver (maximalIdeal O)] :
    letI := rootAlgebra yB' hyB'
    Algebra.IsUnramifiedAt (RootOfUniformizer.Ring ϖ e) 𝔔 := by
  letI := rootAlgebra yB' hyB'
  haveI := rootAlgebra_isScalarTower yB' hyB'
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at he)
  letI := RootOfUniformizer.isDomain hϖ he0
  letI := RootOfUniformizer.isLocalRing hϖ he0
  haveI := RootOfUniformizer.isLocalHom (ϖ := ϖ) he0
  set O' := RootOfUniformizer.Ring ϖ e
  set S := Localization.AtPrime 𝔔
  have hy : (algebraMap B' F yB') ^ e = algebraMap O F ϖ := by
    rw [← map_pow, hyB', ← IsScalarTower.algebraMap_apply]
  obtain ⟨hmax, hsep⟩ :=
    maximalIdeal_atPrime_eq_span_and_isSeparable (K := K) hϖ he hy hF htame 𝔔 yB' rfl
  haveI : IsScalarTower O O' S := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply O B' S, IsScalarTower.algebraMap_apply O O' B',
      ← IsScalarTower.algebraMap_apply O' B' S]
  have hroot : algebraMap O' S (AdjoinRoot.root _) = algebraMap B' S yB' := by
    rw [IsScalarTower.algebraMap_apply O' B' S, rootAlgebra_algebraMap_root]
  have hmap : (maximalIdeal O').map (algebraMap O' S) = maximalIdeal S := by
    rw [RootOfUniformizer.maximalIdeal_eq hϖ he0, Ideal.map_span, Set.image_singleton, hroot,
      hmax]
  haveI : IsLocalHom (algebraMap O' S) := by
    refine ⟨fun x hx ↦ ?_⟩
    by_contra hnx
    have : algebraMap O' S x ∈ maximalIdeal S := by
      rw [← hmap]
      exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal x).2 hnx)
    exact (mem_maximalIdeal _).1 this hx
  -- finiteness
  haveI : Module.Finite O B' := finite_integralClosure (K := K) (L := L) hϖ he hy hF
  haveI : Algebra.FiniteType O' B' := Algebra.FiniteType.of_restrictScalars_finiteType O O' B'
  -- separability of the residue field extension
  haveI : Algebra.IsIntegral O B' := IsIntegralClosure.isIntegral_algebra O F
  haveI : 𝔔.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) 𝔔
    (by rw [← Ideal.under_def, ← Ideal.over_def 𝔔 (maximalIdeal O)]; infer_instance)
  haveI : IsLocalHom (algebraMap O S) := by
    rw [IsScalarTower.algebraMap_eq O O' S]
    infer_instance
  letI := Ideal.Quotient.field (maximalIdeal O)
  have hsepS : Algebra.IsSeparable (ResidueField O) (ResidueField S) := by
    refine Algebra.IsSeparable.of_equiv_equiv (A₁ := O ⧸ maximalIdeal O) (B₁ := B' ⧸ 𝔔)
      (RingEquiv.refl _)
      (RingEquiv.ofBijective _ 𝔔.bijective_algebraMap_quotient_residueField) ?_
    ext x
    rfl
  haveI := Algebra.isSeparable_tower_top_of_isSeparable (ResidueField O) (ResidueField O')
    (ResidueField S)
  exact Algebra.FormallyUnramified.of_map_maximalIdeal (R := O') (S := S) hmap

include K L B in
/-- **Abhyankar's lemma: ramification indices.** In the situation of `isUnramifiedAt`, every
maximal ideal `𝔔` of `B'` has ramification index `e(𝔔 | O') = 1` over
`O' = O[Y] ⧸ (Y ^ e - ϖ)`. -/
theorem ramificationIdx_eq_one {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (he : IsUnit (e : O))
    (yB' : B') (hyB' : yB' ^ e = algebraMap O B' ϖ)
    (hF : Algebra.adjoin L {algebraMap B' F yB'} = ⊤)
    (htame : ∀ (𝔓 : Ideal B) [𝔓.IsPrime] [𝔓.LiesOver (maximalIdeal O)],
      𝔓.ramificationIdx O ∣ e ∧ Algebra.IsSeparable (O ⧸ maximalIdeal O) (B ⧸ 𝔓))
    (𝔔 : Ideal B') [𝔔.IsPrime] [𝔔.LiesOver (maximalIdeal O)] :
    letI := rootAlgebra yB' hyB'
    𝔔.ramificationIdx (RootOfUniformizer.Ring ϖ e) = 1 := by
  letI := rootAlgebra yB' hyB'
  haveI := rootAlgebra_isScalarTower yB' hyB'
  have hy : (algebraMap B' F yB') ^ e = algebraMap O F ϖ := by
    rw [← map_pow, hyB', ← IsScalarTower.algebraMap_apply]
  haveI : Module.Finite O B' := finite_integralClosure (K := K) (L := L) hϖ he hy hF
  haveI : Algebra.FiniteType (RootOfUniformizer.Ring ϖ e) B' :=
    Algebra.FiniteType.of_restrictScalars_finiteType O _ B'
  haveI := isUnramifiedAt (K := K) hϖ he yB' hyB' hF htame 𝔔
  exact Ideal.ramificationIdx_eq_one 𝔔 _

end Unramified

end Abhyankar

end SemistableReduction
