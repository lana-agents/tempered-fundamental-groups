/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussModel

/-!
# Normalization of Zariski models in algebraic extensions

Blueprint §9.6 (W5), layer M6. For a Zariski model `M` of `F` over `O` and an algebraic extension
`F'/F`, the **normalization** `M.normalization F'` has as charts the integral closures in `F'` of
the charts of `M`.

* `integralClosure_le_localAt`: if `B ≤ localAt A W` then the integral closure of `B` lies in the
  local ring of the integral closure of `A` at the center of `W` (clear the denominators of an
  integral equation, `Polynomial.scaleRoots`); `map_localAt_le`: local rings map to local rings.
* `mem_or_inv_mem_localAt` (**Kaplansky**): if `D ⊆ W` is integrally closed and `u` is a root of a
  polynomial with coefficients in the local ring `B = localAt D W`, one of which is a `W`-unit,
  then `u ∈ B` or `u⁻¹ ∈ B` (induction on the degree via `a_n u ∈ B`).
* `localAt_integralClosure_eq`: for a valuation subring `W` of `F` and `W' ⊇ W` of `F'` (`F'/F`
  algebraic), the localization of the integral closure of `W` at the center of `W'` is `W'` (the
  integral closure of a valuation ring is a Prüfer ring).
* `normalization_isProper`, `normalization_isSeparated`, `normalization_isNormal`.
* `lines_normalization_vertexSet` (**W5 (ii) in the form used downstream**): for Gauss
  coordinates `y i` of valuations `w i` of `F` and `F'/F` algebraic, the vertex set of the
  normalization of the join of the lines `ℙ¹_O` with coordinates `y i` is the set of valuation
  subrings of `F'` lying over some `O_{w i}`; `gaussJoinModel_normalization_vertexSet` for Gauss
  valuations `w_{a i, r i}` of `K(X)`.

Finite type of the normalization is not addressed (it needs the finiteness of integral closures,
available in Mathlib for integrally closed noetherian charts and separable extensions).
-/

open Polynomial

namespace SemistableReduction

/-! ### Integral closures and local rings -/

section Integral

variable {L : Type*} [Field L]

/-- A valuation subring `W` satisfies `W(x) = 1` iff `x ≠ 0`, `x ∈ W` and `x⁻¹ ∈ W`. -/
lemma valuation_eq_one_iff_mem_and_inv_mem (W : ValuationSubring L) {x : L} :
    W.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ W ∧ x⁻¹ ∈ W := by
  constructor
  · intro h
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h
    refine ⟨hx0, (W.valuation_le_one_iff x).1 h.le, (W.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, h, inv_one]
  · rintro ⟨hx0, hx, hinv⟩
    rw [← W.valuation_le_one_iff] at hx hinv
    rw [map_inv₀] at hinv
    exact le_antisymm hx (one_le_of_inv_le_one (by simpa using hx0) hinv)

/-- **Integral closure and local rings.** If `B ≤ localAt A W`, then the integral closure of `B`
lies in the local ring of the integral closure of `A` at the center of `W`. -/
theorem integralClosure_le_localAt {A B : Subring L} {W : ValuationSubring L}
    (hB : B ≤ localAt A W) :
    (integralClosure B L).toSubring ≤ localAt (integralClosure A L).toSubring W := by
  classical
  intro x hx
  obtain ⟨p, hpm, hp⟩ := hx
  set n := p.natDegree
  have hc (i : ℕ) : ((p.coeff i : B) : L) ∈ localAt A W := hB (p.coeff i).2
  choose s hsA hsW hcs using hc
  set t := ∏ i ∈ Finset.range n, s i
  have htA : t ∈ A := Subring.prod_mem _ fun i _ ↦ hsA i
  have htW : W.valuation t = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun i _ ↦ hsW i
  have hct (i : ℕ) (hi : i < n) : ((p.coeff i : B) : L) * t ∈ A := by
    have ht : t = s i * ∏ j ∈ (Finset.range n).erase i, s j :=
      (Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi)).symm
    rw [ht, ← mul_assoc]
    exact A.mul_mem (hcs i) (Subring.prod_mem _ fun j _ ↦ hsA j)
  set P := p.map (algebraMap B L)
  have hPm : P.Monic := hpm.map _
  have hPn : P.natDegree = n := hpm.natDegree_map _
  have hlift : scaleRoots P t ∈ lifts (algebraMap A L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots, hPn]
    rcases lt_trichotomy i n with hi | rfl | hi
    · obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
      rw [hk, pow_succ', ← mul_assoc, coeff_map]
      exact ⟨⟨_, A.mul_mem (hct i hi) (A.pow_mem htA k)⟩, rfl⟩
    · rw [Nat.sub_self, pow_zero, mul_one, ← hPn, hPm.coeff_natDegree]
      exact ⟨1, map_one _⟩
    · rw [coeff_eq_zero_of_natDegree_lt (hPn.symm ▸ hi), zero_mul]
      exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).2 hPm)
  have hroot : eval₂ (algebraMap A L) (t * x) q = 0 := by
    rw [← eval_map, hq, eval, ← RingHom.id_apply t]
    refine scaleRoots_eval₂_eq_zero (RingHom.id L) ?_
    rw [eval₂_map]
    exact hp
  refine ⟨t, isIntegral_algebraMap (x := (⟨t, htA⟩ : A)), htW, ?_⟩
  rw [mul_comm]
  exact ⟨q, hqm, hroot⟩

/-- In `localAt A W`, the elements with `W`-valuation `1` are invertible. -/
lemma inv_mem_localAt_of_mem {A : Subring L} {W : ValuationSubring L} {b : L}
    (hb : b ∈ localAt A W) (hbW : W.valuation b = 1) : b⁻¹ ∈ localAt A W := by
  obtain ⟨s, hs, hsW, hbs⟩ := hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hbW
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hsW
  have : b⁻¹ = s * (b * s)⁻¹ := by field_simp
  rw [this]
  refine Subring.mul_mem _ (le_localAt hs) (inv_mem_localAt hbs ?_)
  rw [map_mul, hbW, hsW, one_mul]

/-- The local ring of an integrally closed subring at the center of `W` is integrally closed. -/
lemma isIntegral_mem_localAt {D : Subring L} {W : ValuationSubring L}
    (hD : ∀ x : L, IsIntegral D x → x ∈ D) {x : L} (hx : IsIntegral (localAt D W) x) :
    x ∈ localAt D W := by
  have h := integralClosure_le_localAt (A := D) (B := localAt D W) le_rfl hx
  have hDD : (integralClosure D L).toSubring = D :=
    le_antisymm (fun y hy ↦ hD y hy) fun y hy ↦ isIntegral_algebraMap (x := (⟨y, hy⟩ : D))
  rwa [hDD] at h

/-- **Kaplansky's lemma** (for the local ring `B = localAt D W` of an integrally closed `D ⊆ W`): a
root `u` of a polynomial with coefficients in `B`, one of which is a `W`-unit, satisfies `u ∈ B`
or `u⁻¹ ∈ B`. -/
theorem mem_or_inv_mem_localAt {D : Subring L} {W : ValuationSubring L}
    (hDW : D ≤ W.toSubring) (hD : ∀ x : L, IsIntegral D x → x ∈ D) (u : L) :
    ∀ (n : ℕ) (P : L[X]), P.natDegree = n → (∀ i, P.coeff i ∈ localAt D W) →
      (∃ i, W.valuation (P.coeff i) = 1) → P.eval u = 0 →
        u ∈ localAt D W ∨ u⁻¹ ∈ localAt D W := by
  set B := localAt D W
  have hBW : B ≤ W.toSubring := localAt_le hDW
  have hle (b : L) (hb : b ∈ B) : W.valuation b ≤ 1 := (W.valuation_le_one_iff b).2 (hBW hb)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hPB ⟨i₀, hi₀⟩ hPu
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hi₀
  have hi₀n : i₀ ≤ n := by
    rw [← hn]
    refine le_natDegree_of_ne_zero fun h ↦ ?_
    rw [h] at hi₀
    simp at hi₀
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · rw [Nat.le_zero.1 hi₀n] at hi₀
    rw [eq_C_of_natDegree_eq_zero hn, eval_C] at hPu
    rw [hPu] at hi₀
    simp at hi₀
  -- `v = a u ∈ B`, where `a` is the leading coefficient
  set a := P.leadingCoeff
  have ha0 : a ≠ 0 := leadingCoeff_ne_zero.2 hP0
  have haB : a ∈ B := hPB _
  have hvB : a * u ∈ B := by
    have hlift : P ∈ lifts (algebraMap B L) := by
      rw [lifts_iff_coeff_lifts]
      exact fun i ↦ ⟨⟨_, hPB i⟩, rfl⟩
    obtain ⟨p, hp⟩ := mem_lifts P |>.1 hlift
    have hpu : aeval u p = 0 := by rw [aeval_def, eval₂_eq_eval_map, hp, hPu]
    have hint := isIntegral_leadingCoeff_smul p u hpu
    have hlc : ((p.leadingCoeff : B) : L) = a := by
      change _ = P.leadingCoeff
      rw [← hp, leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective B L)]
      rfl
    rw [Algebra.smul_def, show algebraMap B L p.leadingCoeff = a from hlc] at hint
    exact isIntegral_mem_localAt hD hint
  set v := a * u
  set Q := P.eraseLead + C v * X ^ (n - 1)
  have hQu : Q.eval u = 0 := by
    have hsplit := P.eraseLead_add_C_mul_X_pow
    have h1 : P.eraseLead.eval u = P.eval u - a * u ^ n := by
      have := congrArg (eval u) hsplit
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, hn] at this
      rw [← this]
      ring
    have h2 : u ^ n = u * u ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    simp only [Q, eval_add, h1, eval_mul, eval_C, eval_pow, eval_X, hPu, v, h2]
    ring
  have hQcoeff (i : ℕ) : Q.coeff i = (if i = n then 0 else P.coeff i) +
      (if i = n - 1 then v else 0) := by
    simp only [Q, coeff_add, eraseLead_coeff, coeff_C_mul_X_pow, hn]
  have hQB (i : ℕ) : Q.coeff i ∈ B := by
    rw [hQcoeff]
    refine B.add_mem ?_ ?_
    · split_ifs
      · exact B.zero_mem
      · exact hPB i
    · split_ifs
      · exact hvB
      · exact B.zero_mem
  have hQdeg : Q.natDegree < n := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (hn ▸ eraseLead_natDegree_le P) (by omega)
    · exact lt_of_le_of_lt (natDegree_C_mul_X_pow_le v _) (by omega)
  by_cases hQunit : ∃ i, W.valuation (Q.coeff i) = 1
  · exact ih _ hQdeg Q rfl hQB hQunit hQu
  push Not at hQunit
  rcases eq_or_ne i₀ n with rfl | hi₀ne
  · -- the leading coefficient is a unit: `u = a⁻¹ v`
    left
    have ha1 : W.valuation a = 1 := by rwa [← hn] at hi₀
    have : u = a⁻¹ * v := by simp only [v]; field_simp
    rw [this]
    exact B.mul_mem (inv_mem_localAt_of_mem haB ha1) hvB
  · have hi₀' : i₀ = n - 1 := by
      by_contra hne
      have := hQunit i₀
      rw [hQcoeff, if_neg hi₀ne, if_neg hne, add_zero] at this
      exact this hi₀
    subst hi₀'
    -- `P.coeff (n - 1)` is a unit and `P.coeff (n - 1) + v` is not, so `v` is a unit
    have hsum : W.valuation (P.coeff (n - 1) + v) < 1 := by
      have h := hQunit (n - 1)
      rw [hQcoeff, if_neg hi₀ne, if_pos rfl] at h
      exact lt_of_le_of_ne (hle _ (B.add_mem (hPB _) hvB)) h
    have hv1 : W.valuation v = 1 := by
      have : v = (P.coeff (n - 1) + v) - P.coeff (n - 1) := by ring
      rw [this, Valuation.map_sub_eq_of_lt_right _ (hi₀ ▸ hsum)]
      exact hi₀
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp [v] at hv1
    right
    have : u⁻¹ = a * v⁻¹ := by simp only [v]; field_simp
    rw [this]
    exact B.mul_mem haB (inv_mem_localAt_of_mem hvB hv1)

end Integral

/-! ### Extensions of valuation rings -/

section Extension

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F']

lemma valuation_comap_eq_one_iff (W' : ValuationSubring F') {x : F} :
    (W'.comap (algebraMap F F')).valuation x = 1 ↔ W'.valuation (algebraMap F F' x) = 1 := by
  rw [valuation_eq_one_iff_mem_and_inv_mem, valuation_eq_one_iff_mem_and_inv_mem,
    ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, Ne, Ne,
    map_eq_zero_iff _ (algebraMap F F').injective]

/-- Local rings at centers map to local rings at centers. -/
lemma map_localAt_le (A : Subring F) (W' : ValuationSubring F') :
    (localAt A (W'.comap (algebraMap F F'))).map (algebraMap F F') ≤
      localAt (A.map (algebraMap F F')) W' := by
  rintro _ ⟨x, ⟨s, hs, hsW, hxs⟩, rfl⟩
  exact ⟨algebraMap F F' s, ⟨s, hs, rfl⟩, (valuation_comap_eq_one_iff W').1 hsW,
    ⟨x * s, hxs, map_mul _ _ _⟩⟩

/-- The integral closure in `F'` of a subring of `F`. -/
noncomputable def normChart (F' : Type*) [Field F'] [Algebra F F'] (A : Subring F) :
    Subring F' :=
  (integralClosure (A.map (algebraMap F F')) F').toSubring

lemma map_le_normChart (A : Subring F) : A.map (algebraMap F F') ≤ normChart F' A :=
  fun x hx ↦ isIntegral_algebraMap (x := (⟨x, hx⟩ : A.map (algebraMap F F')))

lemma normChart_isIntegral (A : Subring F) {x : F'} (hx : IsIntegral (normChart F' A) x) :
    x ∈ normChart F' A :=
  (Subring.isIntegrallyClosedIn_iff).1
    (inferInstanceAs (IsIntegrallyClosedIn
      (integralClosure (A.map (algebraMap F F')) F').toSubring F')) hx

lemma normChart_le_iff (A : Subring F) (W' : ValuationSubring F') :
    normChart F' A ≤ W'.toSubring ↔ A ≤ (W'.comap (algebraMap F F')).toSubring := by
  have : IsIntegrallyClosedIn W'.toSubring F' := inferInstanceAs (IsIntegrallyClosedIn W' F')
  rw [normChart, Subring.integralClosure_subring_le_iff]
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h hx

/-- **The integral closure of a valuation ring is Prüfer**: for a valuation subring `W` of `F`,
`F'/F` algebraic and a valuation subring `W'` of `F'` containing `W`, the local ring of the
integral closure of `W` in `F'` at the center of `W'` is `W'`. -/
theorem localAt_normChart_eq [Algebra.IsAlgebraic F F'] (W : ValuationSubring F)
    (W' : ValuationSubring F') (h : W ≤ W'.comap (algebraMap F F')) :
    localAt (normChart F' W.toSubring) W' = W'.toSubring := by
  classical
  set D := normChart F' W.toSubring
  have hDW : D ≤ W'.toSubring := (normChart_le_iff _ _).2 h
  refine le_antisymm (localAt_le hDW) fun x hx ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · exact Subring.zero_mem _
  set g := minpoly F x
  have hg0 : g ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
  obtain ⟨i₀, hi₀, hmax⟩ := g.support.exists_max_image (fun i ↦ W.valuation (g.coeff i))
    (nonempty_support_iff.2 hg0)
  have hgi₀ : g.coeff i₀ ≠ 0 := mem_support_iff.1 hi₀
  set c := (g.coeff i₀)⁻¹
  have hcg (i : ℕ) : c * g.coeff i ∈ W := by
    rw [← W.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hi : i ∈ g.support
    · exact (inv_mul_le_one₀ (zero_lt_iff.2 ((W.valuation.ne_zero_iff).2 hgi₀))).2 (hmax i hi)
    · rw [notMem_support_iff.1 hi, map_zero, mul_zero]
      exact zero_le
  set P := (C c * g).map (algebraMap F F')
  have hPB (i : ℕ) : P.coeff i ∈ localAt D W' := by
    rw [coeff_map, coeff_C_mul]
    exact le_localAt (map_le_normChart _ ⟨_, hcg i, rfl⟩)
  have hPunit : W'.valuation (P.coeff i₀) = 1 := by
    rw [coeff_map, coeff_C_mul, inv_mul_cancel₀ hgi₀, map_one, map_one]
  have hPx : P.eval x = 0 := by
    rw [eval_map, ← aeval_def, map_mul, aeval_C, minpoly.aeval, mul_zero]
  have hD : ∀ y : F', IsIntegral D y → y ∈ D := fun y hy ↦ normChart_isIntegral _ hy
  rcases mem_or_inv_mem_localAt hDW hD x _ P rfl hPB ⟨i₀, hPunit⟩ hPx with h' | h'
  · exact h'
  · have hxinv : W'.valuation x⁻¹ = 1 := by
      rw [valuation_eq_one_iff_mem_and_inv_mem, inv_inv]
      exact ⟨inv_ne_zero hx0, localAt_le hDW h', hx⟩
    simpa using inv_mem_localAt_of_mem h' hxinv

end Extension

/-! ### The normalization of a model -/

section Normalization

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] {O : ValuationSubring K}

omit [Algebra F F'] in
lemma subring_map_mono {A B : Subring F} (h : A ≤ B) (f : F →+* F') : A.map f ≤ B.map f := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

lemma map_baseRing : (baseRing F O).map (algebraMap F F') = baseRing F' O := by
  rw [baseRing, baseRing, Subring.map_map, ← IsScalarTower.algebraMap_eq]

lemma comap_comap_algebraMap (W' : ValuationSubring F') :
    (W'.comap (algebraMap F F')).comap (algebraMap K F) = W'.comap (algebraMap K F') := by
  rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]

variable (F') in
open scoped Classical in
/-- The **normalization** of a Zariski model of `F` in an extension `F'`: the charts are the
integral closures in `F'` of the charts. -/
noncomputable def ZariskiModel.normalization (M : ZariskiModel (baseRing F O)) :
    ZariskiModel (baseRing F' O) where
  charts := M.charts.image (normChart F')
  le_chart C hC := by
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hC
    rw [← map_baseRing (F := F)]
    exact (subring_map_mono (M.le_chart A hA) _).trans (map_le_normChart A)

namespace ZariskiModel

variable {M : ZariskiModel (baseRing F O)}

lemma mem_normalization_charts {C : Subring F'} :
    C ∈ (M.normalization F').charts ↔ ∃ A ∈ M.charts, normChart F' A = C := by
  classical
  simp [normalization]

lemma baseRing_le_comap {W' : ValuationSubring F'} (hW' : baseRing F' O ≤ W'.toSubring) :
    baseRing F O ≤ (W'.comap (algebraMap F F')).toSubring := by
  rintro _ ⟨o, ho, rfl⟩
  change algebraMap F F' (algebraMap K F o) ∈ W'
  rw [← IsScalarTower.algebraMap_apply]
  exact hW' ⟨o, ho, rfl⟩

/-- The normalization of a proper model is proper. -/
theorem normalization_isProper (hM : M.IsProper) : (M.normalization F').IsProper := by
  intro W' hW'
  obtain ⟨A, hA, hAW⟩ := hM _ (baseRing_le_comap hW')
  exact ⟨_, mem_normalization_charts.2 ⟨A, hA, rfl⟩, (normChart_le_iff A W').2 hAW⟩

/-- The normalization of a separated model is separated. -/
theorem normalization_isSeparated (hs : M.IsSeparated) : (M.normalization F').IsSeparated := by
  intro C hC C' hC' W' hCW hC'W
  obtain ⟨A, hA, rfl⟩ := mem_normalization_charts.1 hC
  obtain ⟨B, hB, rfl⟩ := mem_normalization_charts.1 hC'
  have hAW := (normChart_le_iff A W').1 hCW
  have hBW := (normChart_le_iff B W').1 hC'W
  have h₁ : B.map (algebraMap F F') ≤ localAt (A.map (algebraMap F F')) W' :=
    (subring_map_mono (hs A hA B hB _ hAW hBW) _).trans (map_localAt_le A W')
  exact integralClosure_le_localAt h₁

/-- The normalization is normal. -/
theorem normalization_isNormal : (M.normalization F').IsNormal := by
  intro C hC x hx
  obtain ⟨A, -, rfl⟩ := mem_normalization_charts.1 hC
  exact normChart_isIntegral A hx

end ZariskiModel

end Normalization

/-! ### Normalizations of joins of lines -/

section Lines

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

omit [Algebra K F'] [IsScalarTower K F F'] in
lemma isResidueTranscendental_comap_iff {O : ValuationSubring K} {W' : ValuationSubring F'}
    [Algebra K F'] [IsScalarTower K F F'] {z : F} :
    IsResidueTranscendental O W' (algebraMap F F' z) ↔
      IsResidueTranscendental O (W'.comap (algebraMap F F')) z := by
  unfold IsResidueTranscendental
  rw [ValuationSubring.mem_comap]
  refine and_congr_right fun _ ↦ forall_congr' fun P ↦ imp_congr_right fun _ ↦ ?_
  rw [aeval_algebraMap_apply, valuation_comap_eq_one_iff]

open ZariskiModel in
/-- **W5 (ii), normalization form.** Let `y i` be Gauss coordinates of valuations `w i` of `F`
over `v`, and `F'/F` algebraic. The normalization in `F'` of the join of the lines `ℙ¹_O` with
coordinates `y i` is a proper separated normal model of `F'` whose vertex set is exactly the set
of valuation subrings of `F'` lying over one of the `O_{w i}`. -/
theorem lines_normalization_vertexSet [Algebra.IsAlgebraic F F'] {ι : Type*} [Fintype ι]
    {y : ι → F} {w : ι → Valuation F Γ₀} (h : ∀ i, IsGaussCoord v (w i) (y i)) :
    ((lines v y).normalization F').vertexSet =
      {W' | ∃ i, W'.comap (algebraMap F F') = (w i).valuationSubring} := by
  classical
  set R := baseRing F v.valuationSubring
  ext W'
  constructor
  · intro hW'
    obtain ⟨C, hC, -, hloc⟩ := exists_localAt_eq_of_mem_vertexSet hW'
    obtain ⟨A, hA, rfl⟩ := mem_normalization_charts.1 hC
    obtain ⟨f, hf, rfl⟩ := mem_iJoin_charts.1 hA
    choose z hz hfz using fun i ↦ exists_eq_polyChart_of_mem_line_charts (hf i)
    have hA' : R ⊔ ⨆ i, f i = Subring.closure ((R : Set F) ∪ ⋃ i, {z i}) := by
      rw [closure_union_iUnion]
      simp_rw [hfz]
      rfl
    set S' : Set F' := ⋃ i, {algebraMap F F' (z i)}
    have hmap : (R ⊔ ⨆ i, f i).map (algebraMap F F') =
        Subring.closure ((baseRing F' v.valuationSubring : Set F') ∪ S') := by
      rw [hA', RingHom.map_closure, Set.image_union, Set.image_iUnion]
      simp_rw [Set.image_singleton]
      congr 2
      rw [← map_baseRing (F := F), Subring.coe_map]
    have hC' : ∀ x ∈ normChart F' (R ⊔ ⨆ i, f i),
        IsIntegral (Subring.closure ((baseRing F' v.valuationSubring : Set F') ∪ S')) x := by
      intro x hx
      rw [normChart, hmap] at hx
      exact hx
    have hAC : Subring.closure ((baseRing F' v.valuationSubring : Set F') ∪ S') ≤
        normChart F' (R ⊔ ⨆ i, f i) := hmap ▸ map_le_normChart _
    obtain ⟨s, hs, hst⟩ :=
      exists_isResidueTranscendental_of_localAt_eq_of_isIntegral hW'.1 hAC hC' hloc hW'.2.1
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hs
    rw [Set.mem_singleton_iff] at hi
    subst hi
    rw [isResidueTranscendental_comap_iff] at hst
    have hWO : (W'.comap (algebraMap F F')).comap (algebraMap K F) = v.valuationSubring := by
      rw [comap_comap_algebraMap]
      exact hW'.1
    refine ⟨i, ?_⟩
    rcases hz i with he | he <;> rw [he] at hst
    · exact (h i).eq_of_isResidueTranscendental hWO hst
    · exact (h i).inv.eq_of_isResidueTranscendental hWO hst
  · rintro ⟨i, hi⟩
    set Wi := (w i).valuationSubring
    have hR : R ≤ Wi.toSubring := baseRing_le_iff.2 (h i).comap_valuationSubring.ge
    let f : ι → Subring F := fun j ↦
      if y j ∈ Wi then polyChart v (y j) else polyChart v (y j)⁻¹
    have hfc (j : ι) : f j ∈ (line v (y j)).charts := by
      simp only [f]
      split_ifs
      · exact mem_line_charts.2 (.inl rfl)
      · exact mem_line_charts.2 (.inr rfl)
    have hfW (j : ι) : f j ≤ Wi.toSubring := by
      simp only [f]
      split_ifs with hj
      · exact polyChart_le hR hj
      · exact polyChart_le hR ((Wi.mem_or_inv_mem _).resolve_left hj)
    have hyi : y i ∈ Wi := show w i (y i) ≤ 1 by rw [(h i).valuation_self]
    have hfi : f i = polyChart v (y i) := if_pos hyi
    set A := R ⊔ ⨆ j, f j
    have hAW : A ≤ Wi.toSubring := sup_le hR (iSup_le hfW)
    have hiA : polyChart v (y i) ≤ A := hfi ▸ (le_iSup f i).trans le_sup_right
    have hlocA : localAt A Wi = Wi.toSubring :=
      le_antisymm (localAt_le hAW) ((h i).localAt_polyChart.symm.le.trans (localAt_mono hiA))
    have hAmem : A ∈ (lines v y).charts := mem_iJoin_charts.2 ⟨f, hfc, rfl⟩
    have hCmem : normChart F' A ∈ ((lines v y).normalization F').charts :=
      mem_normalization_charts.2 ⟨A, hAmem, rfl⟩
    have hCW : normChart F' A ≤ W'.toSubring := (normChart_le_iff A W').2 (hi ▸ hAW)
    have h₂ : Wi.toSubring.map (algebraMap F F') ≤ localAt (A.map (algebraMap F F')) W' := by
      have := map_localAt_le A W'
      rwa [hi, hlocA] at this
    have h₃ : normChart F' Wi.toSubring ≤ localAt (normChart F' A) W' :=
      integralClosure_le_localAt h₂
    have h₄ : normChart F' A ≤ normChart F' Wi.toSubring := by
      have : IsIntegrallyClosedIn (normChart F' Wi.toSubring) F' :=
        inferInstanceAs (IsIntegrallyClosedIn
          (integralClosure (Wi.toSubring.map (algebraMap F F')) F').toSubring F')
      rw [normChart, Subring.integralClosure_subring_le_iff]
      exact (subring_map_mono hAW _).trans (map_le_normChart _)
    have hloc : localAt (normChart F' A) W' = W'.toSubring := by
      rw [← localAt_eq_of_le h₄ h₃]
      exact localAt_normChart_eq Wi W' hi.ge
    have hW'O : W'.comap (algebraMap K F') = v.valuationSubring := by
      rw [← comap_comap_algebraMap (F := F), hi, (h i).comap_valuationSubring]
    have hT : IsTypeTwo v.valuationSubring W' :=
      ⟨algebraMap F F' (y i), isResidueTranscendental_comap_iff.2
        (hi ▸ (h i).isResidueTranscendental)⟩
    exact mem_vertexSet_of_localAt_eq hW'O hT hCmem hCW hloc

/-- **W5 (ii) for curves over `K(X)`.** For finitely many Gauss valuations `w_{a i, r i}` of `K(X)`
(`v(c i) = r i`) and an algebraic extension `F'/K(X)`, the normalization in `F'` of the join of the
models `ℙ¹_O` with coordinates `(X - a i) / c i` is a proper separated normal Zariski model of `F'`
whose vertex set is the set of valuation subrings of `F'` lying over one of the
`O_{w_{a i, r i}}`. -/
theorem gaussJoinModel_normalization_vertexSet {F' : Type*} [Field F'] [Algebra K F']
    [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F'] [Algebra.IsAlgebraic (RatFunc K) F']
    {ι : Type*} [Fintype ι] {a c : ι → K} {r : ι → Γ₀ˣ} (hc : ∀ i, v (c i) = r i) :
    ((gaussJoinModel v a c).normalization F').vertexSet =
      {W' | ∃ i, W'.comap (algebraMap (RatFunc K) F') =
        (gaussRat v (a i) (r i)).valuationSubring} :=
  lines_normalization_vertexSet fun i ↦ isGaussCoord_gaussCoord (hc i)

end Lines

end SemistableReduction
