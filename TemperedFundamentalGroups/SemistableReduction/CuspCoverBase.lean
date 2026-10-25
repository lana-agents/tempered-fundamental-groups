/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerNodeChart

/-!
# The cusp chart and its Kummer covers (MR12 T2 S3, base)

Let `O` be a discrete valuation ring with fraction field `K` and uniformizer `ϖ`. The **cusp
chart** is `O[t]` (`Polynomial O`) with the **cusp point** `𝔪 = (ϖ, t)` (`Cusp.cuspIdeal`, the
polynomials with constant term in the maximal ideal of `O`), the horizontal divisor being
`t = 0`. Its local ring `R = O[t]_𝔪` is a two-dimensional regular local ring:
`𝔪 R = (t, ϖ)` (`Cusp.maximalIdeal_loc_eq_span`), `t` is prime (`Cusp.prime_t`) and
`ϖ ∉ (t)` (`Cusp.C_notMem_span_t`); every other prime has height `≤ 1`
(`Cusp.height_le_one_of_ne_maximalIdeal`).

The **Kummer cover** of index `e` is `O[t] → O[t']`, `t ↦ t' ^ e` (`Cusp.KPoly O e`, a type
synonym of `O[X]` carrying the `O[X]`-algebra structure `Polynomial.expand O e`). On local rings
it gives `R → R_e = O[t']_{(ϖ, t')}` (`Cusp.localKummerAlgebra`), which is local, finite
(`Cusp.localKummer_finite`: the cusp point is the only prime over the cusp point) and induces an
isomorphism of residue fields (`Cusp.residueField_map_localKummer_bijective`). The function
fields are `K(T ^ e) ⊆ K(T)` (`Cusp.isFractionRing_adjoinPow`, `Cusp.isFractionRing_ratFunc`,
`f ↦ f(T ^ e)` resp. `f ↦ f(T)`, `Cusp.toRatFunc`), compatibly with the Kummer map
(`Cusp.isScalarTower_loc`).

This is the cusp analogue of `NodeCoverBase` (the node `u v = s ^ M` and its Kummer map onto the
regular node).
-/

open Polynomial IsLocalRing IntermediateField Module

universe u

namespace SemistableReduction.Cusp

section CuspIdeal

variable (O : Type u) [CommRing O] [IsLocalRing O]

/-- The **cusp point** `(𝔪_O, t)` of the cusp chart `O[t]`: the polynomials whose constant term
lies in the maximal ideal of `O`. -/
noncomputable def cuspIdeal : Ideal O[X] := (maximalIdeal O).comap (constantCoeff : O[X] →+* O)

instance cuspIdeal_isMaximal : (cuspIdeal O).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ constantCoeff_surjective

variable {O}

lemma mem_cuspIdeal {f : O[X]} : f ∈ cuspIdeal O ↔ f.coeff 0 ∈ maximalIdeal O :=
  Iff.rfl

lemma X_mem_cuspIdeal : (X : O[X]) ∈ cuspIdeal O := by
  rw [mem_cuspIdeal, coeff_X_zero]
  exact zero_mem _

lemma C_mem_cuspIdeal {a : O} : C a ∈ cuspIdeal O ↔ a ∈ maximalIdeal O := by
  rw [mem_cuspIdeal, coeff_C_zero]

/-- `𝔪 = (t, ϖ)`. -/
lemma cuspIdeal_eq_span {ϖ : O} (hϖ : maximalIdeal O = Ideal.span {ϖ}) :
    cuspIdeal O = Ideal.span {X, C ϖ} := by
  refine le_antisymm (fun f hf ↦ ?_) ?_
  · rw [mem_cuspIdeal, hϖ, Ideal.mem_span_singleton] at hf
    obtain ⟨a, ha⟩ := hf
    obtain ⟨g, hg⟩ := X_dvd_sub_C (p := f)
    have : f = X * g + C ϖ * C a := by
      rw [← C_mul, ← ha, ← hg]
      ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    rintro f (rfl | rfl)
    · exact X_mem_cuspIdeal
    · rw [SetLike.mem_coe, C_mem_cuspIdeal, hϖ]
      exact Ideal.mem_span_singleton_self ϖ

/-- The Kummer map `t ↦ t ^ e` preserves the cusp point. -/
lemma comap_expand_cuspIdeal {e : ℕ} (he : 0 < e) :
    (cuspIdeal O).comap (expand O e) = cuspIdeal O := by
  ext f
  rw [Ideal.mem_comap, mem_cuspIdeal, mem_cuspIdeal, coeff_expand he]
  simp

lemma span_X_le_cuspIdeal : Ideal.span {(X : O[X])} ≤ cuspIdeal O :=
  Ideal.span_le.mpr (by simpa using X_mem_cuspIdeal)

lemma disjoint_primeCompl_span_X :
    Disjoint ((cuspIdeal O).primeCompl : Set O[X]) (Ideal.span {(X : O[X])}) :=
  Set.disjoint_left.mpr fun _ hf hX ↦ hf (span_X_le_cuspIdeal hX)

end CuspIdeal

section Local

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

local notation "R" => Localization.AtPrime (cuspIdeal O)

lemma span_X_isPrime : (Ideal.span {(X : O[X])}).IsPrime :=
  (Ideal.span_singleton_prime X_ne_zero).mpr prime_X

/-- `R = O[t]_{(ϖ, t)}` is Noetherian. -/
theorem isNoetherianRing_loc : IsNoetherianRing R :=
  IsLocalization.isNoetherianRing (cuspIdeal O).primeCompl R inferInstance

/-- `R = O[t]_{(ϖ, t)}` is integrally closed. -/
theorem isIntegrallyClosed_loc : IsIntegrallyClosed R :=
  isIntegrallyClosed_of_isLocalization R (cuspIdeal O).primeCompl
    (cuspIdeal O).primeCompl_le_nonZeroDivisors

lemma algebraMap_loc_injective : Function.Injective (algebraMap O[X] R) :=
  IsLocalization.injective R (cuspIdeal O).primeCompl_le_nonZeroDivisors

variable {O}

/-- `𝔪 R = (t, ϖ)`. -/
theorem maximalIdeal_loc_eq_span {ϖ : O} (hϖ : Irreducible ϖ) :
    maximalIdeal R = Ideal.span {algebraMap O[X] R X, algebraMap O[X] R (C ϖ)} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal,
    congrArg (Ideal.map (algebraMap O[X] R)) (cuspIdeal_eq_span hϖ.maximalIdeal_eq),
    Ideal.map_span, Set.image_pair]

variable (O) in
/-- The horizontal divisor `t = 0` of `R`. -/
lemma map_span_X : (Ideal.span {(X : O[X])}).map (algebraMap O[X] R) =
    Ideal.span {algebraMap O[X] R X} := by
  rw [Ideal.map_span, Set.image_singleton]

variable (O) in
/-- `t` is a prime element of `R`. -/
theorem prime_t : Prime (algebraMap O[X] R X) := by
  have h := IsLocalization.isPrime_of_isPrime_disjoint (cuspIdeal O).primeCompl R _
    (span_X_isPrime O) disjoint_primeCompl_span_X
  rw [map_span_X] at h
  refine (Ideal.span_singleton_prime fun h0 ↦ (X_ne_zero : (X : O[X]) ≠ 0) ?_).mp h
  exact algebraMap_loc_injective O (h0.trans (map_zero _).symm)

variable (O) in
/-- The divisor `t = 0` of `R` lies over `t = 0` of `O[t]`. -/
lemma comap_span_t : (Ideal.span {algebraMap O[X] R X}).comap (algebraMap O[X] R) =
    Ideal.span {(X : O[X])} := by
  rw [← map_span_X]
  exact IsLocalization.under_map_of_isPrime_disjoint (cuspIdeal O).primeCompl R
    (span_X_isPrime O) disjoint_primeCompl_span_X

/-- `ϖ ∉ (t)` in `R`. -/
theorem C_notMem_span_t {ϖ : O} (hϖ : ϖ ≠ 0) :
    algebraMap O[X] R (C ϖ) ∉ Ideal.span {algebraMap O[X] R X} := by
  intro h
  rw [← Ideal.mem_comap, comap_span_t, Ideal.mem_span_singleton, X_dvd_iff, coeff_C_zero] at h
  exact hϖ h

/-- The closed point of `R` has height at most two. -/
theorem height_maximalIdeal_loc_le_two {ϖ : O} (hϖ : Irreducible ϖ) :
    (maximalIdeal R).height ≤ 2 := by
  classical
  have := isNoetherianRing_loc O
  have hmin : maximalIdeal R ∈ (Ideal.span ↑({algebraMap O[X] R X, algebraMap O[X] R (C ϖ)} :
      Finset R)).minimalPrimes := by
    rw [Finset.coe_insert, Finset.coe_singleton, ← maximalIdeal_loc_eq_span hϖ,
      Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans
    (by exact_mod_cast Finset.card_le_two)

/-- A prime of `R` other than the closed point has height at most one. -/
theorem height_le_one_of_ne_maximalIdeal {ϖ : O} (hϖ : Irreducible ϖ) (𝔭 : Ideal R) [𝔭.IsPrime]
    (h : 𝔭 ≠ maximalIdeal R) : 𝔭.height ≤ 1 := by
  have := isNoetherianRing_loc O
  have hlt : 𝔭 < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) h
  have h1 := (Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans
    (height_maximalIdeal_loc_le_two hϖ)
  by_contra hc
  have : (2 : ℕ∞) ≤ 𝔭.height := Order.add_one_le_of_lt (not_le.mp hc)
  have : (3 : ℕ∞) ≤ 2 := by
    calc (3 : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ 𝔭.height + 1 := by gcongr
      _ ≤ 2 := h1
  norm_num at this

end Local

/-! ### The Kummer cover `t ↦ t' ^ e` -/

/-- The cusp chart `O[t']`, as an algebra over `O[t]` via the Kummer map `t ↦ t' ^ e`
(`Polynomial.expand O e`). -/
def KPoly (O : Type u) [CommRing O] (_e : ℕ) : Type u := O[X]

namespace KPoly

variable {O : Type u} [CommRing O] {e : ℕ}

noncomputable instance : CommRing (KPoly O e) := inferInstanceAs (CommRing O[X])

noncomputable instance : Algebra O (KPoly O e) := inferInstanceAs (Algebra O O[X])

noncomputable instance kummerAlgebra : Algebra O[X] (KPoly O e) :=
  (expand O e).toRingHom.toAlgebra

instance [IsDomain O] : IsDomain (KPoly O e) := inferInstanceAs (IsDomain O[X])

instance : IsScalarTower O O[X] (KPoly O e) :=
  IsScalarTower.of_algebraMap_eq fun a ↦ ((expand O e).commutes a).symm

lemma algebraMap_eq (f : O[X]) : algebraMap O[X] (KPoly O e) f = expand O e f := rfl

/-- The coordinate `t'` of the Kummer cover. -/
noncomputable def Y : KPoly O e := (X : O[X])

lemma Y_pow : (Y : KPoly O e) ^ e = algebraMap O[X] (KPoly O e) X := by
  change (X : O[X]) ^ e = expand O e X
  rw [expand_X]

lemma algebraMap_C (a : O) : algebraMap O[X] (KPoly O e) (C a) = (C a : O[X]) := by
  rw [algebraMap_eq, expand_C]

lemma adjoin_Y : Algebra.adjoin O[X] {(Y : KPoly O e)} = ⊤ := by
  rw [eq_top_iff]
  rintro (p : O[X]) -
  induction p using Polynomial.induction_on with
  | C a =>
    rw [show ((C a : O[X]) : KPoly O e) = algebraMap O[X] (KPoly O e) (C a) from
      (algebraMap_C a).symm]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact add_mem hp hq
  | monomial n a h =>
    have e1 : (C a * X ^ (n + 1) : O[X]) = C a * X ^ n * X := by ring
    rw [e1]
    exact mul_mem h (Algebra.subset_adjoin rfl)

instance finite [NeZero e] : Module.Finite O[X] (KPoly O e) := by
  have h := fg_adjoin_of_finite (R := O[X]) (Set.toFinite {(Y : KPoly O e)}) (by
    rintro x rfl
    refine ⟨Polynomial.X ^ e - Polynomial.C (X : O[X]), monic_X_pow_sub_C _ (NeZero.ne e), ?_⟩
    simp [eval₂_sub, Y_pow])
  rw [adjoin_Y, Algebra.top_toSubmodule] at h
  exact ⟨h⟩

variable (O e) in
/-- The cusp point `(ϖ, t')` of the Kummer cover. -/
noncomputable def ideal [IsLocalRing O] : Ideal (KPoly O e) := cuspIdeal O

instance [IsLocalRing O] : (ideal O e).IsMaximal := cuspIdeal_isMaximal O

instance [IsLocalRing O] [NeZero e] : (ideal O e).LiesOver (cuspIdeal O) :=
  ⟨(comap_expand_cuspIdeal (Nat.pos_of_neZero e)).symm⟩

/-- The cusp point is the only prime of the Kummer cover over the cusp point. -/
theorem primesOver_cuspIdeal [IsLocalRing O] [NeZero e] :
    (cuspIdeal O).primesOver (KPoly O e) = {ideal O e} := by
  ext Q
  simp only [Ideal.primesOver, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hQ, hQo⟩
    have hmem : ∀ f : O[X], f ∈ cuspIdeal O → algebraMap O[X] (KPoly O e) f ∈ Q := by
      intro f hf
      rw [hQo.over] at hf
      exact hf
    have hY : (Y : KPoly O e) ∈ Q :=
      hQ.mem_of_pow_mem e (Y_pow (O := O) ▸ hmem X X_mem_cuspIdeal)
    have hle : ideal O e ≤ Q := by
      intro (f : O[X]) hf
      obtain ⟨g, hg⟩ := X_dvd_sub_C (p := f)
      have hf0 : f = X * g + C (f.coeff 0) := by
        rw [← hg]
        ring
      have hf' : (show KPoly O e from f) = (Y : KPoly O e) * (show KPoly O e from g) +
          algebraMap O[X] (KPoly O e) (C (f.coeff 0)) := by
        rw [algebraMap_C]
        exact hf0
      rw [hf']
      exact add_mem (Q.mul_mem_right _ hY) (hmem _ (C_mem_cuspIdeal.mpr hf))
    exact ((Ideal.IsMaximal.eq_of_le inferInstance hQ.ne_top hle)).symm
  · rintro rfl
    exact ⟨inferInstance, inferInstance⟩

end KPoly

section LocalKummer

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : ℕ) [NeZero e]

local notation "R" => Localization.AtPrime (cuspIdeal O)
local notation "R_e" => Localization.AtPrime (KPoly.ideal O e)

/-- The local Kummer map `R → R_e`, `t ↦ t' ^ e`, as an algebra. Not an instance. -/
noncomputable abbrev localKummerAlgebra : Algebra R R_e :=
  Localization.AtPrime.algebraOfLiesOver (cuspIdeal O) (KPoly.ideal O e)

attribute [local instance] localKummerAlgebra

lemma localKummer_algebraMap (f : O[X]) :
    algebraMap R R_e (algebraMap O[X] R f) =
      algebraMap (KPoly O e) R_e (algebraMap O[X] (KPoly O e) f) :=
  Localization.localRingHom_to_map _ _ _ _ f

lemma localKummer_algebraMap_O (c : O) :
    algebraMap R R_e (algebraMap O R c) = algebraMap O R_e c := by
  rw [IsScalarTower.algebraMap_apply O O[X] R, localKummer_algebraMap,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

instance isLocalHom_localKummer : IsLocalHom (algebraMap R R_e) :=
  Localization.isLocalHom_localRingHom _ _ _ _

/-- `R_e` is a finite `R`-module. -/
theorem localKummer_finite : Module.Finite R R_e :=
  Localization.finite_of_primesOver_eq_singleton KPoly.primesOver_cuspIdeal

instance localKummer_isIntegral : Algebra.IsIntegral R R_e :=
  have := localKummer_finite O e
  Algebra.IsIntegral.of_finite _ _

omit [NeZero e] in
/-- Every element of `O[t']` has the residue of a constant in `R_e`. -/
lemma exists_residue_eq (x : KPoly O e) : ∃ c : O,
    IsLocalRing.residue R_e (algebraMap _ R_e x) =
      IsLocalRing.residue R_e (algebraMap O R_e c) := by
  refine ⟨(show O[X] from x).coeff 0, ?_⟩
  rw [← sub_eq_zero, ← map_sub, IsScalarTower.algebraMap_apply O (KPoly O e) R_e, ← map_sub,
    residue_eq_zero_iff, ← Localization.AtPrime.map_eq_maximalIdeal]
  refine Ideal.mem_map_of_mem _ ?_
  change (show O[X] from x) - C ((show O[X] from x).coeff 0) ∈ cuspIdeal O
  obtain ⟨g, hg⟩ := X_dvd_sub_C (p := (show O[X] from x))
  rw [hg]
  exact Ideal.mul_mem_right _ _ X_mem_cuspIdeal

/-- The local Kummer map induces an isomorphism of residue fields (both are `O ⧸ ϖ`). -/
theorem residueField_map_localKummer_bijective :
    Function.Bijective (ResidueField.map (algebraMap R R_e)) := by
  refine ⟨(ResidueField.map (algebraMap R R_e)).injective, fun y ↦ ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective (KPoly.ideal O e).primeCompl y
  obtain ⟨c, hc⟩ := exists_residue_eq O e x
  obtain ⟨d, hd⟩ := exists_residue_eq O e (t : KPoly O e)
  have ht : IsLocalRing.residue R_e (algebraMap _ R_e (t : KPoly O e)) ≠ 0 := by
    rw [Ne, residue_eq_zero_iff]
    exact fun h ↦ (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h))
      (IsLocalization.map_units R_e t)
  refine ⟨IsLocalRing.residue R (algebraMap O R c) / IsLocalRing.residue R (algebraMap O R d), ?_⟩
  rw [map_div₀, ResidueField.map_residue, ResidueField.map_residue, localKummer_algebraMap_O,
    localKummer_algebraMap_O, ← hc, ← hd, div_eq_iff ht, ← map_mul, IsLocalization.mk'_spec]

end LocalKummer

/-! ### Function fields -/

section Fraction

/-- A fraction field of a domain is a fraction field of its localization at a prime. -/
noncomputable def locLift {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
    (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F] : Localization.AtPrime p →+* F :=
  IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p) (g := algebraMap A F)
    fun y ↦ IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (p.primeCompl_le_nonZeroDivisors y.2))

lemma locLift_algebraMap {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
    (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F] (a : A) :
    locLift p F (algebraMap A _ a) = algebraMap A F a :=
  IsLocalization.lift_eq _ a

theorem isFractionRing_locLift {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
    (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F] :
    letI := (locLift p F).toAlgebra
    IsScalarTower A (Localization.AtPrime p) F ∧ IsFractionRing (Localization.AtPrime p) F := by
  letI := (locLift p F).toAlgebra
  have : IsScalarTower A (Localization.AtPrime p) F :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (locLift_algebraMap p F a).symm
  exact ⟨this, IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl _ _⟩

variable (O : Type u) [CommRing O] [IsDomain O]

local notation "K" => FractionRing O

/-- `O[t] → K(T)`, `f ↦ f(T ^ n)`. -/
noncomputable def toRatFunc (n : ℕ) : O[X] →+* RatFunc K :=
  (algebraMap K[X] (RatFunc K)).comp ((expand K n).toRingHom.comp (mapRingHom (algebraMap O K)))

variable {O}

lemma toRatFunc_apply (n : ℕ) (f : O[X]) :
    toRatFunc O n f = algebraMap K[X] (RatFunc K) (expand K n (f.map (algebraMap O K))) := rfl

lemma algebraMap_expand (n : ℕ) (g : K[X]) :
    algebraMap K[X] (RatFunc K) (expand K n g) = aeval ((RatFunc.X : RatFunc K) ^ n) g := by
  have h1 : expand K n g = aeval (X ^ n : K[X]) g := by
    rw [coe_expand, aeval_def, algebraMap_eq]
  rw [h1, ← RatFunc.algebraMap_X, ← map_pow]
  exact (aeval_algHom_apply (IsScalarTower.toAlgHom K K[X] (RatFunc K)) _ g).symm

lemma toRatFunc_eq_aeval (n : ℕ) (f : O[X]) :
    toRatFunc O n f = aeval ((RatFunc.X : RatFunc K) ^ n) (f.map (algebraMap O K)) :=
  algebraMap_expand n _

lemma toRatFunc_injective {n : ℕ} (hn : 0 < n) : Function.Injective (toRatFunc O n) :=
  (RatFunc.algebraMap_injective K).comp ((expand_injective hn).comp
    (map_injective _ (IsFractionRing.injective O K)))

lemma toRatFunc_X (n : ℕ) : toRatFunc O n X = RatFunc.X ^ n := by
  rw [toRatFunc_eq_aeval, map_X, aeval_X]

lemma toRatFunc_C (n : ℕ) (a : O) :
    toRatFunc O n (C a) = algebraMap K (RatFunc K) (algebraMap O K a) := by
  rw [toRatFunc_eq_aeval, map_C, aeval_C]

lemma toRatFunc_expand (n m : ℕ) (f : O[X]) :
    toRatFunc O n (expand O m f) = toRatFunc O (m * n) f := by
  rw [toRatFunc_apply, toRatFunc_apply, map_expand, mul_comm m n, expand_mul]

lemma toRatFunc_mem (n : ℕ) (f : O[X]) :
    toRatFunc O n f ∈ K⟮(RatFunc.X : RatFunc K) ^ n⟯ := by
  rw [toRatFunc_eq_aeval]
  exact IntermediateField.algebra_adjoin_le_adjoin K _ (aeval_mem_adjoin_singleton K _)

variable (O) in
/-- `O[t] → K(T ^ n)`, `f ↦ f(T ^ n)`. -/
noncomputable def toAdjoinPow (n : ℕ) : O[X] →+* K⟮(RatFunc.X : RatFunc K) ^ n⟯ :=
  (toRatFunc O n).codRestrict _ (toRatFunc_mem n)

@[simp] lemma coe_toAdjoinPow (n : ℕ) (f : O[X]) :
    (toAdjoinPow O n f : RatFunc K) = toRatFunc O n f := rfl

/-- Clearing denominators: `p (T ^ n)` is a quotient of values of `toRatFunc O n`. -/
lemma exists_aeval_eq_div (n : ℕ) (p : K[X]) :
    ∃ x y : O[X], aeval ((RatFunc.X : RatFunc K) ^ n) p = toRatFunc O n x / toRatFunc O n y := by
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) p
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors O) p, C b, ?_⟩
  have hb0 : algebraMap K (RatFunc K) (algebraMap O K b) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap K (RatFunc K)).injective,
      map_ne_zero_iff _ (IsFractionRing.injective O K)]
    exact nonZeroDivisors.ne_zero hb
  rw [toRatFunc_eq_aeval, hq, toRatFunc_C, Algebra.smul_def, map_mul,
    Polynomial.algebraMap_apply, aeval_C, mul_div_cancel_left₀ _ hb0]

variable (O) in
/-- `K(T ^ n)` as an algebra over `O[t]` via `t ↦ T ^ n`. Not an instance. -/
noncomputable abbrev adjoinPowAlgebra (n : ℕ) : Algebra O[X] K⟮(RatFunc.X : RatFunc K) ^ n⟯ :=
  (toAdjoinPow O n).toAlgebra

/-- **`K(T ^ n)` is the fraction field of `O[t]`** via `t ↦ T ^ n`. -/
theorem isFractionRing_adjoinPow {n : ℕ} (hn : 0 < n) :
    letI := adjoinPowAlgebra O n
    IsFractionRing O[X] K⟮(RatFunc.X : RatFunc K) ^ n⟯ := by
  letI := adjoinPowAlgebra O n
  have hinj : Function.Injective (toAdjoinPow O n) := fun x y h ↦
    toRatFunc_injective hn (congr_arg Subtype.val h)
  have : FaithfulSMul O[X] K⟮(RatFunc.X : RatFunc K) ^ n⟯ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨r, s, hrs⟩ := (mem_adjoin_simple_iff K (z : RatFunc K)).mp z.2
  obtain ⟨x₁, y₁, h₁⟩ := exists_aeval_eq_div (O := O) n r
  obtain ⟨x₂, y₂, h₂⟩ := exists_aeval_eq_div (O := O) n s
  refine ⟨x₁ * y₂, y₁ * x₂, Subtype.ext ?_⟩
  change (z : RatFunc K) = toRatFunc O n (x₁ * y₂) / toRatFunc O n (y₁ * x₂)
  rw [hrs, h₁, h₂, map_mul, map_mul, div_div_div_eq]

variable (O) in
/-- `K(T)` as an algebra over `O[t]` via `t ↦ T`. Not an instance. -/
noncomputable abbrev ratFuncAlgebra : Algebra O[X] (RatFunc K) := (toRatFunc O 1).toAlgebra

/-- **`K(T)` is the fraction field of `O[t]`** via `t ↦ T`. -/
theorem isFractionRing_ratFunc :
    letI := ratFuncAlgebra O
    IsFractionRing O[X] (RatFunc K) := by
  letI := ratFuncAlgebra O
  have : FaithfulSMul O[X] (RatFunc K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (toRatFunc_injective one_pos)
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨x₁, y₁, h₁⟩ := exists_aeval_eq_div (O := O) 1 z.num
  obtain ⟨x₂, y₂, h₂⟩ := exists_aeval_eq_div (O := O) 1 z.denom
  refine ⟨x₁ * y₂, y₁ * x₂, ?_⟩
  rw [pow_one, RatFunc.aeval_X_left_eq_algebraMap] at h₁ h₂
  change z = toRatFunc O 1 (x₁ * y₂) / toRatFunc O 1 (y₁ * x₂)
  rw [← RatFunc.num_div_denom z, h₁, h₂, map_mul, map_mul, div_div_div_eq]

end Fraction

section LocalFraction

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : ℕ) [NeZero e]

local notation "K" => FractionRing O
local notation "R" => Localization.AtPrime (cuspIdeal O)
local notation "R_e" => Localization.AtPrime (KPoly.ideal O e)
local notation "𝕂" => K⟮(RatFunc.X : RatFunc K) ^ e⟯

/-- `K(T ^ e)` as an algebra over `R` (`t ↦ T ^ e`). Not an instance. -/
noncomputable abbrev locAdjoinPowAlgebra : Algebra R 𝕂 :=
  letI := adjoinPowAlgebra O e
  haveI := isFractionRing_adjoinPow (O := O) (Nat.pos_of_neZero e)
  (locLift (cuspIdeal O) 𝕂).toAlgebra

/-- `K(T)` as an algebra over `O[t']` (`t' ↦ T`). Not an instance. -/
noncomputable abbrev kPolyRatFuncAlgebra : Algebra (KPoly O e) (RatFunc K) := ratFuncAlgebra O

/-- `K(T)` as an algebra over `R_e` (`t' ↦ T`). Not an instance. -/
noncomputable abbrev locRatFuncAlgebra : Algebra R_e (RatFunc K) :=
  letI := kPolyRatFuncAlgebra O e
  haveI : IsFractionRing (KPoly O e) (RatFunc K) := isFractionRing_ratFunc (O := O)
  (locLift (KPoly.ideal O e) (RatFunc K)).toAlgebra

/-- `K(T)` as an algebra over `R` through `K(T ^ e)`. Not an instance. -/
noncomputable abbrev locRatFuncAlgebra' : Algebra R (RatFunc K) :=
  letI := locAdjoinPowAlgebra O e
  ((algebraMap 𝕂 (RatFunc K)).comp (algebraMap R 𝕂)).toAlgebra

attribute [local instance 2000] adjoinPowAlgebra locAdjoinPowAlgebra kPolyRatFuncAlgebra
  locRatFuncAlgebra localKummerAlgebra

lemma algebraMap_loc_adjoinPow (f : O[X]) :
    algebraMap R 𝕂 (algebraMap O[X] R f) = toAdjoinPow O e f :=
  haveI := isFractionRing_adjoinPow (O := O) (Nat.pos_of_neZero e)
  locLift_algebraMap _ _ f

omit [NeZero e] in
lemma algebraMap_locE_ratFunc (f : KPoly O e) :
    algebraMap R_e (RatFunc K) (algebraMap (KPoly O e) R_e f) = toRatFunc O 1 f :=
  haveI : IsFractionRing (KPoly O e) (RatFunc K) := isFractionRing_ratFunc (O := O)
  locLift_algebraMap _ _ f

/-- `K(T ^ e)` is the fraction field of `R`. -/
theorem isFractionRing_loc_adjoinPow :
    letI := locAdjoinPowAlgebra O e
    IsFractionRing R 𝕂 :=
  haveI := isFractionRing_adjoinPow (O := O) (Nat.pos_of_neZero e)
  (isFractionRing_locLift (cuspIdeal O) 𝕂).2

theorem isScalarTower_poly_loc_adjoinPow :
    letI := locAdjoinPowAlgebra O e
    IsScalarTower O[X] R 𝕂 :=
  haveI := isFractionRing_adjoinPow (O := O) (Nat.pos_of_neZero e)
  (isFractionRing_locLift (cuspIdeal O) 𝕂).1

omit [NeZero e] in
/-- `K(T)` is the fraction field of `R_e`. -/
theorem isFractionRing_locE : IsFractionRing R_e (RatFunc K) :=
  haveI : IsFractionRing (KPoly O e) (RatFunc K) := isFractionRing_ratFunc (O := O)
  (isFractionRing_locLift (KPoly.ideal O e) (RatFunc K)).2

theorem isScalarTower_loc_adjoinPow_ratFunc :
    letI := locAdjoinPowAlgebra O e
    letI := locRatFuncAlgebra' O e
    IsScalarTower R 𝕂 (RatFunc K) :=
  letI := locAdjoinPowAlgebra O e
  letI := locRatFuncAlgebra' O e
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The function fields are compatible with the Kummer map: `R → R_e → K(T)` is
`R → K(T ^ e) ⊆ K(T)`. -/
theorem isScalarTower_loc :
    letI := locRatFuncAlgebra' O e
    IsScalarTower R R_e (RatFunc K) := by
  letI := locRatFuncAlgebra' O e
  refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext (cuspIdeal O).primeCompl
    (RingHom.ext fun f ↦ ?_))
  simp only [RingHom.comp_apply]
  rw [localKummer_algebraMap, algebraMap_locE_ratFunc]
  change algebraMap 𝕂 (RatFunc K) (algebraMap R 𝕂 (algebraMap O[X] R f)) = _
  rw [algebraMap_loc_adjoinPow]
  change toRatFunc O e f = toRatFunc O 1 (expand O e f)
  rw [toRatFunc_expand, mul_one]

/-- The local Kummer map `R → R_e` is injective. -/
theorem localKummer_injective : Function.Injective (algebraMap R R_e) := by
  letI := locAdjoinPowAlgebra O e
  letI := locRatFuncAlgebra' O e
  have := isFractionRing_loc_adjoinPow O e
  have := isScalarTower_loc O e
  have := isScalarTower_loc_adjoinPow_ratFunc O e
  have h : Function.Injective (algebraMap R (RatFunc K)) :=
    (algebraMap 𝕂 (RatFunc K)).injective.comp (IsFractionRing.injective R 𝕂)
  rw [IsScalarTower.algebraMap_eq R R_e (RatFunc K), RingHom.coe_comp] at h
  exact h.of_comp

end LocalFraction

end SemistableReduction.Cusp
