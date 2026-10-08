/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerBase
import TemperedFundamentalGroups.SemistableReduction.AbhyankarLocal
import TemperedFundamentalGroups.SemistableReduction.GenusBetti
import TemperedFundamentalGroups.SemistableReduction.NodeRecognition

/-!
# Kummer base change kills the ramification at a classical point

Blueprint §9.12 O6.1f(i) (`ClassicalSmooth.KummerUnramFor`). For `F / C(x)` finite (`C`
algebraically closed of characteristic `0`), `a ∈ C`, `E = [F : C(x)]!` and `L = F(y)` with
`yᴱ = x - a` (`KummerField`, an irreducible factor of `Tᴱ - (x - a)`):

* `CurvePlace.valuation_eq_of_pow_eq` (**Abhyankar for places**): the local Kummer step
  `Abhyankar.maximalIdeal_eq_span_and_isSeparable_of_pow_eq` applied to the valuation rings of a
  place of `L` and its restrictions (`CurvePlace.comap`) to `F` and `C(x)`;
* `valuation_kummer_eq`: `y` is a uniformizer at every zero of `y` on `L` (the ramification
  indices over `x = a` are at most `[F : C(x)]`, hence divide `E`);
* `exists_unramDatum`: a function regular wherever `y` is, with residues of distinct reductions at
  the `[L : C(y)]` zeros of `y` (`CurvePlace.exists_separating`, Riemann–Roch), is an unramified
  datum (`UnramDatum`) for `L / C(y)` at `y = 0`;
* **`kummerUnramFor`**: `KummerUnramFor C F a` (with `L` in the universe of `F`).
-/

open Polynomial WithZero
open scoped IntermediateField

namespace SemistableReduction

namespace CurvePlace

open IsDiscreteValuationRing

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ]

lemma _root_.ValuationSubring.isUnit_iff_inv_mem {K : Type*} [Field K] (V : ValuationSubring K)
    (x : V) : IsUnit x ↔ (x : K) ≠ 0 ∧ (x : K)⁻¹ ∈ V := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun h ↦ ?_, ?_⟩
    · have := congrArg (fun z : V ↦ (z : K)) u.mul_inv
      simp only [MulMemClass.coe_mul, h, zero_mul, OneMemClass.coe_one] at this
      exact zero_ne_one this
    · have h := congrArg (fun z : V ↦ (z : K)) u.mul_inv
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
      rw [inv_eq_of_mul_eq_one_right h]
      exact (↑u⁻¹ : V).2
  · rintro ⟨h0, hinv⟩
    exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ h0))

variable [IsAlgClosed k] [IsCurveFunctionField k κ] (P : CurvePlace k κ)

lemma valuation_eq_one_of_isUnit {x : P.V} (hx : IsUnit x) : P.valuation (x : κ) = 1 := by
  obtain ⟨h0, hinv⟩ := (ValuationSubring.isUnit_iff_inv_mem P.V x).1 hx
  refine le_antisymm (P.valuation_le_one_iff.2 x.2) ?_
  have h := P.valuation_le_one_iff.2 hinv
  rw [map_inv₀] at h
  exact (inv_le_one₀ ((Valuation.pos_iff _).2 h0)).1 h

lemma mem_V_of_valuation_eq {π : κ} (hπ : P.valuation π = exp (-1)) : π ∈ P.V :=
  P.valuation_le_one_iff.1 (by rw [hπ, ← exp_zero, exp_le_exp]; norm_num)

/-- An element of valuation `exp (-1)` is a uniformizer. -/
lemma irreducible_of_valuation_eq {π : κ} (hπ : P.valuation π = exp (-1)) :
    Irreducible (⟨π, P.mem_V_of_valuation_eq hπ⟩ : P.V) := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  rw [irreducible_iff_uniformizer]
  ext z
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hz
    have hlt : P.valuation (z : κ) < 1 := by
      rw [P.valuation_lt_one_iff]
      exact (ValuationSubring.valuation_lt_one_iff P.V z).1 hz
    have hle : P.valuation (z : κ) ≤ exp (-1) := by
      have := WithZero.le_exp_of_lt_exp_add_one (by simpa using hlt :
        P.valuation (z : κ) < exp ((-1 : ℤ) + 1))
      exact this
    refine ⟨⟨(z : κ) / π, P.valuation_le_one_iff.1 ?_⟩, Subtype.ext ?_⟩
    · rw [map_div₀, hπ, div_le_one₀ (by simp)]
      exact hle
    · change (z : κ) = π * ((z : κ) / π)
      rw [mul_div_cancel₀ _ hπ0]
  · rintro ⟨w, rfl⟩
    rw [ValuationSubring.valuation_lt_one_iff, MulMemClass.coe_mul,
      ← P.valuation_lt_one_iff, map_mul]
    calc P.valuation π * P.valuation (w : κ) ≤ exp (-1) * 1 :=
          mul_le_mul' hπ.le (P.valuation_le_one_iff.2 w.2)
      _ < 1 := by rw [mul_one, ← exp_zero, exp_lt_exp]; norm_num

/-- The additive valuation of the DVR `P.V` is the normalized order. -/
lemma addVal_eq {x : P.V} {n : ℕ} (hx : P.valuation (x : κ) = exp (-(n : ℤ))) :
    addVal P.V x = n := by
  obtain ⟨π, hπ⟩ := P.exists_valuation_eq_exp_neg_one
  have hirr := P.irreducible_of_valuation_eq hπ
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [ZeroMemClass.coe_zero, map_zero] at hx
    exact exp_ne_zero hx.symm
  obtain ⟨m, u, hu⟩ := eq_unit_mul_pow_irreducible hx0 hirr
  have h1 := congrArg (fun z : P.V ↦ P.valuation (z : κ)) hu
  rw [hu, addVal_def' u hirr m]
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow,
    P.valuation_eq_one_of_isUnit u.isUnit, one_mul, hπ, ← exp_nsmul, hx] at h1
  have := exp_injective h1
  simp only [nsmul_eq_mul, mul_neg, mul_one, neg_inj] at this
  exact_mod_cast this.symm

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
/-- A root of a monic polynomial with coefficients of value `≤ 1` has value `≤ 1`. -/
lemma valuation_le_one_of_monic {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {K M : Type*}
    [Field K] [Field M] (v : Valuation M Γ) (φ : K →+* M) {p : K[X]} (hp : p.Monic) {m : M}
    (hm : p.eval₂ φ m = 0) (hc : ∀ i, v (φ (p.coeff i)) ≤ 1) : v m ≤ 1 := by
  by_contra! h
  set n := p.natDegree
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hm
  have hlt : v (∑ i ∈ Finset.range n, φ (p.coeff i) * m ^ i) < v m ^ n := by
    refine Valuation.map_sum_lt _ (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans h))) fun i hi ↦ ?_
    rw [map_mul, map_pow]
    calc v (φ (p.coeff i)) * v m ^ i ≤ 1 * v m ^ i := mul_le_mul_left (hc i) _
      _ < v m ^ n := by rw [one_mul]; exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  have heq : m ^ n = -∑ i ∈ Finset.range n, φ (p.coeff i) * m ^ i :=
    eq_neg_of_add_eq_zero_right hm
  have h2 : v m ^ n = v (∑ i ∈ Finset.range n, φ (p.coeff i) * m ^ i) := by
    rw [← map_pow, heq, Valuation.map_neg]
  rw [← h2] at hlt
  exact lt_irrefl _ hlt

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
/-- **Restriction of a place** along a field embedding `φ : K → κ` over `k` such that `κ` is
integral over `φ(K)`. -/
def comap {K : Type*} [Field K] [Algebra k K] (P : CurvePlace k κ) (φ : K →+* κ)
    (hφ : ∀ c : k, φ (algebraMap k K c) = algebraMap k κ c)
    (hint : ∀ m : κ, ∃ p : K[X], p.Monic ∧ p.eval₂ φ m = 0) : CurvePlace k K where
  V := P.V.comap φ
  algebraMap_mem c := by
    change φ (algebraMap k K c) ∈ P.V
    rw [hφ]
    exact P.algebraMap_mem c
  ne_top h := P.ne_top <| by
    refine eq_top_iff.2 fun m _ ↦ ?_
    obtain ⟨p, hp, hm⟩ := hint m
    have hc (i : ℕ) : φ (p.coeff i) ∈ P.V := by
      have : p.coeff i ∈ P.V.comap φ := by rw [h]; trivial
      exact this
    rw [← ValuationSubring.valuation_le_one_iff]
    exact valuation_le_one_of_monic P.V.valuation φ hp hm fun i ↦
      (ValuationSubring.valuation_le_one_iff _ _).2 (hc i)

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
lemma mem_comap_V {K : Type*} [Field K] [Algebra k K] (P : CurvePlace k κ) (φ : K →+* κ)
    (hφ : ∀ c : k, φ (algebraMap k K c) = algebraMap k κ c)
    (hint : ∀ m : κ, ∃ p : K[X], p.Monic ∧ p.eval₂ φ m = 0) (f : K) :
    f ∈ (P.comap φ hφ hint).V ↔ φ f ∈ P.V := Iff.rfl

omit [IsCurveFunctionField k κ] in
/-- **Abhyankar for places** (Kummer step). Let `P₀ → P₁ → P₂` be places of function fields
`K₀ ⊆ K₁ ⊆ K₂` over `k` (restrictions along `φ`, `ι`), `t` a uniformizer at `P₀` with
`v₁(t) = exp(-n)`, `n ∣ E`, `E` invertible, and `y ∈ O_{P₂}` with `yᴱ = t` such that `O_{P₂}` is
generated by `O_{P₁}[y]` up to denominators. Then `y` is a uniformizer at `P₂`. -/
theorem valuation_eq_of_pow_eq {K₀ K₁ : Type*} [Field K₀] [Field K₁] [Algebra k K₀]
    [Algebra k K₁] [IsCurveFunctionField k K₀] [IsCurveFunctionField k K₁]
    [IsCurveFunctionField k κ] (P₂ : CurvePlace k κ) (P₁ : CurvePlace k K₁)
    (P₀ : CurvePlace k K₀) (ι : K₁ →+* κ) (φ : K₀ →+* K₁) (h₁ : ∀ f, f ∈ P₁.V ↔ ι f ∈ P₂.V)
    (h₀ : ∀ f, f ∈ P₀.V ↔ φ f ∈ P₁.V) {t : K₀} (ht : P₀.valuation t = exp (-1)) {E n : ℕ}
    (hE : IsUnit (E : P₀.V)) (hn : P₁.valuation (φ t) = exp (-(n : ℤ))) (hnE : n ∣ E)
    {y : κ} (hy : y ∈ P₂.V) (hyE : y ^ E = ι (φ t))
    (hgen : ∀ z ∈ P₂.V, ∃ b ∈ P₁.V, b ≠ 0 ∧ ∃ q : K₁[X], (∀ i, q.coeff i ∈ P₁.V) ∧
      ι b * z = q.eval₂ ι y) :
    P₂.valuation y = exp (-1) := by
  classical
  let f₁ : P₀.V →+* P₁.V :=
    { toFun := fun z ↦ ⟨φ z, (h₀ z).1 z.2⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun z w ↦ Subtype.ext (map_mul φ (z : K₀) w)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun z w ↦ Subtype.ext (map_add φ (z : K₀) w) }
  let f₂ : P₁.V →+* P₂.V :=
    { toFun := fun z ↦ ⟨ι z, (h₁ z).1 z.2⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun z w ↦ Subtype.ext (map_mul ι (z : K₁) w)
      map_zero' := Subtype.ext (map_zero ι)
      map_add' := fun z w ↦ Subtype.ext (map_add ι (z : K₁) w) }
  letI : Algebra P₀.V P₁.V := f₁.toAlgebra
  letI : Algebra P₁.V P₂.V := f₂.toAlgebra
  letI : Algebra P₀.V P₂.V := (f₂.comp f₁).toAlgebra
  haveI : IsScalarTower P₀.V P₁.V P₂.V := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsLocalHom (algebraMap P₀.V P₁.V) := ⟨fun z hz ↦ by
    rw [ValuationSubring.isUnit_iff_inv_mem] at hz ⊢
    obtain ⟨h0, hinv⟩ := hz
    refine ⟨fun h ↦ h0 ?_, ?_⟩
    · change φ z = 0
      rw [h, map_zero]
    · rw [h₀, map_inv₀]
      exact hinv⟩
  haveI : IsLocalHom (algebraMap P₁.V P₂.V) := ⟨fun z hz ↦ by
    rw [ValuationSubring.isUnit_iff_inv_mem] at hz ⊢
    obtain ⟨h0, hinv⟩ := hz
    refine ⟨fun h ↦ h0 ?_, ?_⟩
    · change ι z = 0
      rw [h, map_zero]
    · rw [h₁, map_inv₀]
      exact hinv⟩
  have hinjO : Function.Injective (algebraMap P₀.V P₁.V) := fun z w h ↦
    Subtype.ext (φ.injective (congrArg Subtype.val h))
  have hinj : Function.Injective (algebraMap P₁.V P₂.V) := fun z w h ↦
    Subtype.ext (ι.injective (congrArg Subtype.val h))
  let ϖ : P₀.V := ⟨t, P₀.mem_V_of_valuation_eq ht⟩
  have hϖ : Irreducible ϖ := P₀.irreducible_of_valuation_eq ht
  have hyE' : (⟨y, hy⟩ : P₂.V) ^ E = algebraMap P₀.V P₂.V ϖ := Subtype.ext hyE
  have hn' : IsDiscreteValuationRing.addVal P₁.V (algebraMap P₀.V P₁.V ϖ) = n := P₁.addVal_eq hn
  have hgenS : ∀ z : P₂.V, ∃ b : P₁.V, b ≠ 0 ∧
      algebraMap P₁.V P₂.V b * z ∈ Algebra.adjoin P₁.V {(⟨y, hy⟩ : P₂.V)} := by
    intro z
    obtain ⟨b, hb, hb0, q, hq, hqz⟩ := hgen z z.2
    refine ⟨⟨b, hb⟩, fun h ↦ hb0 (congrArg Subtype.val h), ?_⟩
    have heq : algebraMap P₁.V P₂.V ⟨b, hb⟩ * z = ∑ i ∈ q.support,
        algebraMap P₁.V P₂.V ⟨q.coeff i, hq i⟩ * (⟨y, hy⟩ : P₂.V) ^ i := by
      apply Subtype.ext
      change ι b * (z : κ) = ((∑ i ∈ q.support, algebraMap P₁.V P₂.V ⟨q.coeff i, hq i⟩ *
        (⟨y, hy⟩ : P₂.V) ^ i : P₂.V) : κ)
      rw [hqz, eval₂_eq_sum, Polynomial.sum_def]
      push_cast
      rfl
    rw [heq]
    exact sum_mem fun i _ ↦ mul_mem (Subalgebra.algebraMap_mem _ _)
      (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) _)
  obtain ⟨hmax, -⟩ := Abhyankar.maximalIdeal_eq_span_and_isSeparable_of_pow_eq (O := P₀.V)
    (R := P₁.V) (S := P₂.V) (e := E) (n := n) (y := ⟨y, hy⟩) hϖ hE hn' hnE hinjO hinj hyE' hgenS
  -- a uniformizer of `P₂` is a multiple of `y`
  obtain ⟨π, hπ⟩ := P₂.exists_valuation_eq_exp_neg_one
  have hπV := P₂.mem_V_of_valuation_eq hπ
  have hπm : (⟨π, hπV⟩ : P₂.V) ∈ IsLocalRing.maximalIdeal P₂.V := by
    rw [ValuationSubring.valuation_lt_one_iff, ← P₂.valuation_lt_one_iff, hπ, ← exp_zero,
      exp_lt_exp]
    norm_num
  rw [hmax, Ideal.mem_span_singleton] at hπm
  obtain ⟨w, hw⟩ := hπm
  have h1 := congrArg (fun z : P₂.V ↦ P₂.valuation (z : κ)) hw
  simp only [MulMemClass.coe_mul, map_mul, hπ] at h1
  have hw1 : P₂.valuation (w : κ) ≤ 1 := P₂.valuation_le_one_iff.2 w.2
  have hy1 : P₂.valuation y ≤ 1 := P₂.valuation_le_one_iff.2 hy
  have hle : exp (-1) ≤ P₂.valuation y := by
    rw [h1]
    exact mul_le_of_le_one_right' hw1
  have hlt : P₂.valuation y < 1 := by
    have hm : (⟨y, hy⟩ : P₂.V) ∈ IsLocalRing.maximalIdeal P₂.V := by
      rw [hmax]
      exact Ideal.subset_span rfl
    rw [P₂.valuation_lt_one_iff]
    exact (ValuationSubring.valuation_lt_one_iff P₂.V _).1 hm
  refine le_antisymm ?_ hle
  exact WithZero.le_exp_of_lt_exp_add_one (by simpa using hlt)

omit [IsCurveFunctionField k κ] in
lemma res_pow' [IsCurveFunctionField k κ] (Q : CurvePlace k κ) {y : κ} (hy : y ∈ Q.V) (n : ℕ) :
    Q.res (y ^ n) = Q.res y ^ n := by
  induction n with
  | zero => simpa using Q.res_one
  | succ n ih => rw [pow_succ, Q.res_mul (pow_mem hy n) hy, ih, pow_succ]

omit [IsCurveFunctionField k κ] in
lemma res_sum [IsCurveFunctionField k κ] (Q : CurvePlace k κ) {ι : Type*} (s : Finset ι)
    (g : ι → κ) (hg : ∀ i ∈ s, g i ∈ Q.V) : Q.res (∑ i ∈ s, g i) = ∑ i ∈ s, Q.res (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Q.res_algebraMap (0 : k)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      Q.res_add (hg a (Finset.mem_insert_self a s))
        (sum_mem fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)]

omit [IsCurveFunctionField k κ] in
/-- **Separating functions with poles only at the poles of `t`**: for finitely many places `Z`
where `t` is regular and `R₀ ∈ Z`, some `f` regular wherever `t` is has a unit value at `R₀` and
vanishes at the other places of `Z` (Riemann–Roch, `exists_interpolating`). -/
theorem exists_separating [IsCurveFunctionField k κ] {t : κ}
    (ht : t ∉ (algebraMap k κ).range) (Z : Finset (CurvePlace k κ)) (hZ : ∀ R ∈ Z, t ∈ R.V)
    {R₀ : CurvePlace k κ} (hR₀ : R₀ ∈ Z) :
    ∃ f : κ, (∀ P : CurvePlace k κ, t ∈ P.V → f ∈ P.V) ∧ R₀.valuation f = 1 ∧
      ∀ R ∈ Z, R ≠ R₀ → R.valuation f < 1 := by
  classical
  obtain ⟨c, hc⟩ := exists_interpolating (k := k) (κ := κ)
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_of_notMem_range ht)
  set N : ℕ := (c + Z.card).toNat
  set D : CurveDivisor k κ := N • poleDivisor k t
  have hD0 (P : CurvePlace k κ) (hP : t ∈ P.V) : D P = 0 := by
    simp [D, poleDivisor_apply, (P.poleOrder_eq_zero_iff).2 hP]
  have hdeg : c + ((Z.erase R₀).card : ℤ) ≤ D.degree := by
    have h1 : D.degree = (N : ℤ) * (Module.finrank k⟮t⟯ κ : ℤ) := by
      simp only [D, map_nsmul, degree_poleDivisor ht, nsmul_eq_mul]
    have h2 : (1 : ℤ) ≤ Module.finrank k⟮t⟯ κ := by exact_mod_cast Module.finrank_pos
    have h3 : ((Z.erase R₀).card : ℤ) ≤ Z.card := by exact_mod_cast Finset.card_erase_le
    have h4 : c + Z.card ≤ N := Int.self_le_toNat _
    rw [h1]
    nlinarith
  obtain ⟨f, hf, hf0, hfS⟩ := hc D (Z.erase R₀) R₀ (Finset.notMem_erase R₀ Z) hdeg
  refine ⟨f, fun P hP ↦ P.valuation_le_one_iff.1 ?_, ?_, fun R hR hne ↦ ?_⟩
  · have := (mem_rrSpace.1 hf) P
    rwa [hD0 P hP, exp_zero] at this
  · rw [hf0, hD0 R₀ (hZ R₀ hR₀), exp_zero]
  · have := hfS R (Finset.mem_erase.2 ⟨hne, hR⟩)
    rwa [hD0 R (hZ R hR), exp_zero] at this

end CurvePlace

namespace ClassicalSmooth

section Kummer

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]

/-- The Kummer polynomial `Tᴱ - (x - a)` over `F`. -/
noncomputable def kummerPoly (E : ℕ) (a : C) : F[X] :=
  X ^ E - Polynomial.C (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) a))

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma kummerPoly_natDegree (E : ℕ) (a : C) : (kummerPoly F E a).natDegree = E := by
  rw [kummerPoly, natDegree_sub_C, natDegree_X_pow]

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma exists_irreducible_kummer {E : ℕ} (hE : 0 < E) (a : C) :
    ∃ g : F[X], Irreducible g ∧ g ∣ kummerPoly F E a := by
  refine WfDvdMonoid.exists_irreducible_factor (fun h ↦ ?_) fun h ↦ ?_
  · have := natDegree_eq_zero_of_isUnit h
    rw [kummerPoly_natDegree F] at this
    omega
  · have := kummerPoly_natDegree F E a
    rw [h, natDegree_zero] at this
    omega

/-- An irreducible factor of the Kummer polynomial. -/
noncomputable def kummerFactor {E : ℕ} (hE : 0 < E) (a : C) : F[X] :=
  (exists_irreducible_kummer F hE a).choose

instance {E : ℕ} (hE : 0 < E) (a : C) : Fact (Irreducible (kummerFactor F hE a)) :=
  ⟨(exists_irreducible_kummer F hE a).choose_spec.1⟩

/-- The Kummer field `L = F(y)`, `yᴱ = x - a`. -/
abbrev KummerField {E : ℕ} (hE : 0 < E) (a : C) : Type _ := AdjoinRoot (kummerFactor F hE a)

variable {F}

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma kummerFactor_ne_zero {E : ℕ} (hE : 0 < E) (a : C) : kummerFactor F hE a ≠ 0 :=
  (Fact.out : Irreducible (kummerFactor F hE a)).ne_zero

instance {E : ℕ} (hE : 0 < E) (a : C) : FiniteDimensional F (KummerField F hE a) :=
  (AdjoinRoot.powerBasis (kummerFactor_ne_zero hE a)).finite

/-- The Kummer root `y`. -/
noncomputable abbrev kummerRoot {E : ℕ} (hE : 0 < E) (a : C) : KummerField F hE a :=
  AdjoinRoot.root (kummerFactor F hE a)

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma kummerRoot_pow {E : ℕ} (hE : 0 < E) (a : C) :
    kummerRoot (F := F) hE a ^ E = algebraMap F (KummerField F hE a)
      (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) a)) := by
  have hdvd := (exists_irreducible_kummer F hE a).choose_spec.2
  obtain ⟨q, hq⟩ := hdvd
  have h : aeval (kummerRoot (F := F) hE a) (kummerPoly F E a) = 0 := by
    rw [hq, map_mul]
    change aeval (AdjoinRoot.root (kummerFactor F hE a)) (kummerFactor F hE a) * _ = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  rw [kummerPoly, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma adjoin_kummerRoot {E : ℕ} (hE : 0 < E) (a : C) :
    IntermediateField.adjoin F {kummerRoot (F := F) hE a} = ⊤ := by
  rw [← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra]
  refine eq_top_iff.2 ?_
  rw [← AdjoinRoot.adjoinRoot_eq_top]
  exact IntermediateField.algebra_adjoin_le_adjoin F _

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma transcendental_kummerRoot {E : ℕ} (hE : 0 < E) (a : C) :
    Transcendental C (kummerRoot (F := F) hE a) := by
  intro halg
  have h1 : IsAlgebraic C (kummerRoot (F := F) hE a ^ E) := halg.pow E
  rw [kummerRoot_pow, ← IsScalarTower.algebraMap_apply,
    isAlgebraic_algebraMap_iff (algebraMap (RatFunc C) (KummerField F hE a)).injective] at h1
  have h2 : IsAlgebraic C (RatFunc.X : RatFunc C) := by
    have := h1.add (isAlgebraic_algebraMap (R := C) (A := RatFunc C) a)
    simpa using this
  exact RatFunc.transcendental_X h2

end Kummer

section Unram

open CurvePlace PlaceNorm IsLocalRing GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma adjoin_sub_algebraMap_eq {K : Type*} [Field K] [Algebra C K] (x : K) (a : C) :
    IntermediateField.adjoin C {x - algebraMap C K a} = IntermediateField.adjoin C {x} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact sub_mem (IntermediateField.mem_adjoin_simple_self C x)
      (IntermediateField.algebraMap_mem _ a)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := add_mem (IntermediateField.mem_adjoin_simple_self C (x - algebraMap C K a))
      (IntermediateField.algebraMap_mem (IntermediateField.adjoin C {x - algebraMap C K a}) a)
    simpa using this

lemma _root_.SemistableReduction.CurvePlace.mem_zeros_iff_valuation_lt_one {k κ : Type*}
    [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k] [IsCurveFunctionField k κ]
    (P : CurvePlace k κ) {f : κ} (hf : f ≠ 0) : P ∈ zeros k f ↔ P.valuation f < 1 := by
  have h0 : P.valuation f ≠ 0 := (Valuation.ne_zero_iff _).2 hf
  rw [mem_zeros, ← P.valuation_le_one_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (pos_iff_ne_zero.2 h0)

variable [CharZero C] {L : Type*} [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra C L]
  [IsScalarTower C F L]

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] in
lemma xF_coord_eq {y : L} (hy : Transcendental C y) : xF C (Coord hy) = toCoord hy y := by
  change coordAlgHom hy RatFunc.X = y
  rw [← RatFunc.algebraMap_X, coordAlgHom_algebraMap, aeval_X]

omit [IsUltrametricDist C] in
/-- **Abhyankar at the places over `y = 0`** (Kummer base change): if `yᴱ = x - a` with every
ramification index over `x = a` (at most `[F : C(x)]`) dividing `E`, and `L = F[y]`, then `y` is a
uniformizer at every zero of `y`. -/
theorem valuation_kummer_eq {E : ℕ} (hE : ∀ k, 1 ≤ k → k ≤ Module.finrank (RatFunc C) F → k ∣ E)
    (hE0 : 0 < E) {a : C} {y : L} (hy : Transcendental C y)
    (hyE : y ^ E = algebraMap F L (algebraMap (RatFunc C) F
      (RatFunc.X - algebraMap C (RatFunc C) a)))
    (hgen : ∀ s : L, ∃ p : F[X], aeval y p = s) [IsCurveFunctionField C (Coord hy)]
    (R : CurvePlace C (Coord hy)) (hR : R ∈ zeros C (xF C (Coord hy))) :
    R.valuation (xF C (Coord hy)) = exp (-1) := by
  classical
  haveI : IsCurveFunctionField C F := GaussFibre.isCurveFunctionField_F
  have hxy := xF_coord_eq hy
  have hx0 : xF C (Coord hy) ≠ 0 := by
    rw [hxy]
    intro h
    have : y = 0 := (toCoord hy).injective (h.trans (map_zero _).symm)
    exact hy (this ▸ isAlgebraic_zero)
  have hRx : R.valuation (xF C (Coord hy)) < 1 := (R.mem_zeros_iff_valuation_lt_one hx0).1 hR
  -- the restrictions of `R` to `F` and to `C(x)`
  let ι : F →+* Coord hy := (toCoord hy).toRingHom.comp (algebraMap F L)
  have hι : ∀ c : C, ι (algebraMap C F c) = algebraMap C (Coord hy) c := fun c ↦ by
    change toCoord hy (algebraMap F L (algebraMap C F c)) = _
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  have hintι : ∀ m : Coord hy, ∃ p : F[X], p.Monic ∧ p.eval₂ ι m = 0 := fun m ↦ by
    refine ⟨minpoly F ((toCoord hy).symm m),
      minpoly.monic (Algebra.IsIntegral.isIntegral _), ?_⟩
    have h := Polynomial.hom_eval₂ (minpoly F ((toCoord hy).symm m)) (algebraMap F L)
      (toCoord hy).toRingHom ((toCoord hy).symm m)
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h
    change Polynomial.eval₂ ((toCoord hy).toRingHom.comp (algebraMap F L)) m _ = 0
    rw [RingEquiv.toRingHom_eq_coe, ← h, ← aeval_def, minpoly.aeval, map_zero]
  let Qf : CurvePlace C F := R.comap ι hι hintι
  let φ₀ := algebraMap (RatFunc C) F
  have hφ₀ : ∀ c : C, φ₀ (algebraMap C (RatFunc C) c) = algebraMap C F c := fun c ↦
    (IsScalarTower.algebraMap_apply C (RatFunc C) F c).symm
  have hint₀ : ∀ f : F, ∃ p : (RatFunc C)[X], p.Monic ∧ p.eval₂ φ₀ f = 0 := fun f ↦
    ⟨minpoly (RatFunc C) f, minpoly.monic (Algebra.IsIntegral.isIntegral _), minpoly.aeval _ _⟩
  let Q₀ : CurvePlace C (RatFunc C) := Qf.comap φ₀ hφ₀ hint₀
  set t : RatFunc C := RatFunc.X - algebraMap C (RatFunc C) a
  have hιt : ι (φ₀ t) = xF C (Coord hy) ^ E := by
    change toCoord hy (algebraMap F L (algebraMap (RatFunc C) F t)) = _
    rw [← hyE, hxy, map_pow]
  have ht0 : t ≠ 0 := by
    intro h
    have := congrArg (fun z ↦ ι (φ₀ z)) h
    simp only [map_zero, hιt] at this
    exact hx0 (pow_eq_zero_iff hE0.ne' |>.1 this)
  have htF0 : φ₀ t ≠ 0 := by simpa using ht0
  -- `Qf` and `Q₀` are zeros of `x - a`
  have hQf : Qf ∈ zeros C (φ₀ t) := by
    rw [mem_zeros]
    change ι (φ₀ t)⁻¹ ∉ R.V
    rw [map_inv₀, hιt, ← R.valuation_le_one_iff, map_inv₀, map_pow, not_le]
    exact one_lt_inv₀ (pow_pos ((Valuation.pos_iff _).2 hx0) _) |>.2
      (pow_lt_one₀ zero_le hRx hE0.ne')
  have hQ₀ : Q₀ ∈ zeros C t := by
    rw [mem_zeros]
    change φ₀ t⁻¹ ∉ Qf.V
    rw [map_inv₀]
    exact mem_zeros.1 hQf
  -- `x - a` is a uniformizer at `Q₀`
  have htr : t ∉ (algebraMap C (RatFunc C)).range := by
    rintro ⟨b, hb⟩
    have : (RatFunc.X : RatFunc C) = algebraMap C (RatFunc C) (b + a) := by
      rw [map_add, hb]; ring
    exact RatFunc.transcendental_X (this ▸ isAlgebraic_algebraMap (b + a))
  have hord₀ : ord t Q₀ = 1 := by
    have hsum := sum_ord htr
    rw [adjoin_sub_algebraMap_eq, RatFunc.adjoin_X, IntermediateField.finrank_top] at hsum
    have hle := Finset.single_le_sum (f := fun Q ↦ ord t Q) (fun _ _ ↦ Nat.zero_le _) hQ₀
    have := one_le_ord hQ₀
    omega
  have hQ₀t : Q₀.valuation t = exp (-1) := by
    rw [valuation_x hQ₀, hord₀]
    rfl
  -- the ramification index of `Qf` over `Q₀` divides `E`
  have hordf : 1 ≤ ord (φ₀ t) Qf ∧ ord (φ₀ t) Qf ≤ Module.finrank (RatFunc C) F := by
    refine ⟨one_le_ord hQf, ?_⟩
    have htFr : φ₀ t ∉ (algebraMap C F).range := by
      rintro ⟨b, hb⟩
      rw [← hφ₀] at hb
      exact htr ⟨b, (algebraMap (RatFunc C) F).injective hb⟩
    have hsum := sum_ord htFr
    have heq : φ₀ t = xF C F - algebraMap C F a := by
      simp only [φ₀, t, map_sub, xF, ← IsScalarTower.algebraMap_apply]
    rw [heq, adjoin_sub_algebraMap_eq, GaussFibre.finrank_adjoin_xF, ← heq] at hsum
    rw [← hsum]
    exact Finset.single_le_sum (f := fun Q ↦ ord (φ₀ t) Q) (fun _ _ ↦ Nat.zero_le _) hQf
  have he : IsUnit (E : Q₀.V) := by
    rw [ValuationSubring.isUnit_iff_inv_mem]
    have hEC : ((E : Q₀.V) : RatFunc C) = algebraMap C (RatFunc C) (E : C) := by simp
    have hE0' : (E : C) ≠ 0 := Nat.cast_ne_zero.2 hE0.ne'
    rw [hEC, ← map_inv₀]
    exact ⟨(_root_.map_ne_zero _).2 hE0', Q₀.algebraMap_mem _⟩
  have hyS : xF C (Coord hy) ∈ R.V := R.valuation_le_one_iff.1 hRx.le
  refine R.valuation_eq_of_pow_eq Qf Q₀ ι φ₀ (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) hQ₀t he
    (valuation_x hQf) (hE _ hordf.1 hordf.2) hyS hιt.symm fun z _ ↦ ?_
  obtain ⟨p, hp⟩ := hgen ((toCoord hy).symm z)
  have hden (f : F) : ∃ b ∈ Qf.V, b ≠ 0 ∧ b * f ∈ Qf.V := by
    by_cases hf : f ∈ Qf.V
    · exact ⟨1, one_mem _, one_ne_zero, by rw [one_mul]; exact hf⟩
    · have hf0 : f ≠ 0 := fun h ↦ hf (h ▸ zero_mem _)
      refine ⟨f⁻¹, (Qf.V.mem_or_inv_mem f).resolve_left hf, inv_ne_zero hf0, ?_⟩
      rw [inv_mul_cancel₀ hf0]
      exact one_mem _
  choose bi hbiV hbi0 hbi using hden
  set b : F := ∏ i ∈ p.support, bi (p.coeff i)
  have hbV : b ∈ Qf.V := prod_mem fun i _ ↦ hbiV _
  have hb0 : b ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hbi0 _
  have hbmem (i : ℕ) : b * p.coeff i ∈ Qf.V := by
    by_cases hi : i ∈ p.support
    · have : b = bi (p.coeff i) * ∏ j ∈ p.support.erase i, bi (p.coeff j) :=
        (Finset.mul_prod_erase _ _ hi).symm
      rw [this, mul_comm (bi (p.coeff i)), mul_assoc]
      exact mul_mem (prod_mem fun j _ ↦ hbiV _) (hbi _)
    · rw [notMem_support_iff.1 hi, mul_zero]
      exact zero_mem _
  refine ⟨b, hbV, hb0, Polynomial.C b * p, fun i ↦ by rw [coeff_C_mul]; exact hbmem i, ?_⟩
  rw [eval₂_mul, eval₂_C, hxy]
  congr 1
  have h := Polynomial.hom_eval₂ p (algebraMap F L) (toCoord hy).toRingHom y
  rw [← aeval_def, hp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] at h
  exact h

end Unram

section Datum

open CurvePlace PlaceNorm GaussFibre IsLocalRing

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G] [IsScalarTower C (RatFunc C) G]
  [FiniteDimensional (RatFunc C) G] [IsCurveFunctionField C G]

local notation "𝒪" => HenselComplete.integers C
local notation "𝓀" => ResidueField (HenselComplete.integers C)

omit [IsUltrametricDist C] [FiniteDimensional (RatFunc C) G] [IsScalarTower C (RatFunc C) G] in
lemma aeval_xF_mem (Q : CurvePlace C G) (hx : xF C G ∈ Q.V) (q : C[X]) :
    aeval (xF C G) q ∈ Q.V :=
  Q.valuation_le_one_iff.1 (valuation_aeval_le_one Q.valuation_algebraMap_le_one
    (Q.valuation_le_one_iff.2 hx) q)

/-- **An unramified datum from unramifiedness over `x = 0`**: if `x` is a uniformizer at every
zero of `x` on `G / C`, then a function regular wherever `x` is, with prescribed residues of
distinct reductions at the `[G : C(x)]` zeros of `x` (`exists_separating`), is an unramified
datum at `0`. -/
theorem exists_unramDatum (hun : ∀ R ∈ zeros C (xF C G), R.valuation (xF C G) = exp (-1)) :
    ∃ (θ : G) (n : ℕ) (γ : Fin n → 𝒪), UnramDatum C G 0 θ γ := by
  classical
  have htr : xF C G ∉ (algebraMap C G).range := xF_notMem_range
  -- the zeros of `x` are `[G : C(x)]` places
  have hcard : (zeros C (xF C G)).card = Module.finrank (RatFunc C) G := by
    have hsum := sum_ord htr
    rw [finrank_adjoin_xF] at hsum
    rw [← hsum, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun R hR ↦ ?_
    have h := valuation_x hR
    rw [hun R hR] at h
    have := exp_injective h
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = Module.finrank (RatFunc C) G := ⟨_, rfl⟩
  let e : Fin m ≃ zeros C (xF C G) :=
    ((zeros C (xF C G)).equivFin.trans (finCongr (hcard.trans hm.symm))).symm
  -- distinct residues
  let ι𝓀 : Fin m ↪ 𝓀 := Fin.valEmbedding.trans (Infinite.natEmbedding 𝓀)
  choose γ hγ using fun i ↦ residue_surjective (ι𝓀 i)
  have hZV : ∀ R ∈ zeros C (xF C G), xF C G ∈ R.V := fun R hR ↦
    R.valuation_le_one_iff.1 (valuation_x_lt_one hR).le
  choose f hfreg hf1 hf0 using fun i : Fin m ↦
    exists_separating htr (zeros C (xF C G)) hZV (e i).2
  have hfV (i j : Fin m) : f i ∈ (e j).1.V := hfreg i _ (hZV _ (e j).2)
  have hres_ne (i : Fin m) : (e i).1.res (f i) ≠ 0 := by
    intro h
    have := (e i).1.valuation_sub_res_lt_one (hfV i i)
    rw [h, map_zero, sub_zero, hf1] at this
    exact lt_irrefl 1 this
  have hres_zero (i j : Fin m) (hij : i ≠ j) : (e j).1.res (f i) = 0 :=
    (e j).1.res_eq_zero_of_lt_one
      (hf0 i _ (e j).2 fun h ↦ hij (e.injective (Subtype.ext h).symm))
  obtain ⟨θ, hθdef⟩ : ∃ θ : G, θ = ∑ i, algebraMap C G ((γ i : C) / (e i).1.res (f i)) * f i :=
    ⟨_, rfl⟩
  have hθV (P : CurvePlace C G) (hP : xF C G ∈ P.V) : θ ∈ P.V := by
    rw [hθdef]
    exact sum_mem fun i _ ↦ mul_mem (P.algebraMap_mem _) (hfreg i P hP)
  have hθres (j : Fin m) : (e j).1.res θ = γ j := by
    rw [hθdef, res_sum _ _ _ fun i _ ↦ mul_mem ((e j).1.algebraMap_mem _) (hfV i j),
      Finset.sum_eq_single j]
    · rw [(e j).1.res_mul ((e j).1.algebraMap_mem _) (hfV j j), (e j).1.res_algebraMap,
        div_mul_cancel₀ _ (hres_ne j)]
    · intro i _ hij
      rw [(e j).1.res_mul ((e j).1.algebraMap_mem _) (hfV i j), hres_zero i j hij, mul_zero]
    · simp
  -- `θ` is integral over `C[x]`
  have hint := CurveGenerators.isIntegral_of_forall_mem (k := C) (t := xF C G) hθV
  obtain ⟨P, hPm, hP⟩ := CurveGenerators.exists_monic_of_isIntegral hint
  letI : Algebra C[X] G :=
    ((algebraMap (RatFunc C) G).comp (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) G := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have halg (q : C[X]) : algebraMap C[X] G q = aeval (xF C G) q := (aeval_xF q).symm
  have hmap : (aeval (xF C G) : C[X] →ₐ[C] G).toRingHom = algebraMap C[X] G :=
    RingHom.ext fun q ↦ (halg q).symm
  rw [hmap] at hP
  have hθint : IsIntegral C[X] θ := ⟨P, hPm, hP⟩
  have hM : minpoly (RatFunc C) θ = (minpoly C[X] θ).map (algebraMap C[X] (RatFunc C)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc C) hθint
  have hMm : (minpoly C[X] θ).Monic := minpoly.monic hθint
  -- the reduction of the minimal polynomial at `x = 0`
  have hroot (j : Fin m) : ((minpoly C[X] θ).map (Polynomial.evalRingHom 0)).eval
      (γ j : C) = 0 := by
    have hxj := hZV _ (e j).2
    have hxlt : (e j).1.valuation (xF C G) < 1 := valuation_x_lt_one (e j).2
    have h0 := minpoly.aeval C[X] θ
    rw [aeval_eq_sum_range] at h0
    have hterm (k : ℕ) : (minpoly C[X] θ).coeff k • θ ^ k ∈ (e j).1.V := by
      rw [Algebra.smul_def, halg]
      exact mul_mem (aeval_xF_mem _ hxj _) (pow_mem (hθV _ hxj) _)
    have h1 := congrArg (e j).1.res h0
    rw [res_sum _ _ _ fun k _ ↦ hterm k, (e j).1.res_zero] at h1
    rw [eval_eq_sum_range, Monic.natDegree_map hMm]
    refine (Finset.sum_congr rfl fun k _ ↦ ?_).trans h1
    rw [Algebra.smul_def, halg, (e j).1.res_mul (aeval_xF_mem _ hxj _)
      (pow_mem (hθV _ hxj) _), (e j).1.res_aeval hxlt, coeff_map, Polynomial.coe_evalRingHom,
      ← coeff_zero_eq_eval_zero]
    congr 1
    rw [CurvePlace.res_pow' _ (hθV _ hxj), hθres]
  -- hence the reduction is `∏ⱼ (Y - γⱼ)`
  have hγinj : Function.Injective fun j ↦ (γ j : C) := fun i j h ↦ by
    have : γ i = γ j := Subtype.ext h
    have h2 := congrArg (residue 𝒪) this
    rw [hγ, hγ] at h2
    exact ι𝓀.injective h2
  set Mb := (minpoly C[X] θ).map (Polynomial.evalRingHom (0 : C))
  have hMbm : Mb.Monic := hMm.map _
  set s : Multiset C := Finset.univ.val.map fun j ↦ (γ j : C)
  have hs : s.Nodup := Multiset.Nodup.map hγinj Finset.univ.nodup
  have hsle : s ≤ Mb.roots := by
    rw [Multiset.le_iff_subset hs]
    intro z hz
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    exact (mem_roots hMbm.ne_zero).2 (hroot j)
  have hdvd := (Multiset.prod_X_sub_C_dvd_iff_le_roots hMbm.ne_zero s).2 hsle
  have hdegs : (s.map fun a ↦ X - Polynomial.C a).prod.natDegree = m := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin]
  have hdegM : Mb.natDegree ≤ m := by
    rw [Monic.natDegree_map hMm, hm]
    have h1 := minpoly.natDegree_le (A := RatFunc C) θ
    rwa [hM, Monic.natDegree_map hMm] at h1
  have hMb : Mb = (s.map fun a ↦ X - Polynomial.C a).prod :=
    eq_of_monic_of_dvd_of_natDegree_le (monic_multiset_prod_of_monic _ _ fun a _ ↦
      monic_X_sub_C a) hMbm hdvd (hdegs ▸ hdegM)
  have hP₀ : (P₀ γ).map (algebraMap 𝒪 C) = (s.map fun a ↦ X - Polynomial.C a).prod := by
    rw [P₀, Polynomial.map_prod, Multiset.map_map]
    simp only [Polynomial.map_sub, map_X, map_C]
    rfl
  refine ⟨θ, m, γ, ⟨hm, fun i j hij h ↦ hij (ι𝓀.injective (by rw [← hγ, ← hγ, h])),
    fun k ↦ ⟨(minpoly C[X] θ).coeff k, by rw [hM, coeff_map], ?_⟩⟩⟩
  rw [hP₀, ← hMb, coeff_map, Polynomial.coe_evalRingHom]

end Datum

section Main

universe u v

open CurvePlace PlaceNorm GaussFibre

/-- **Kummer base change kills the ramification at a classical point** (Blueprint §9.12
O6.1f(i)): for `E = [F : C(x)]!` and `L = F(y)`, `yᴱ = x - a` (an irreducible factor of
`Tᴱ - (x - a)`), `y` is a uniformizer at every zero of `y` (Abhyankar,
`valuation_kummer_eq`), so `L / C(y)` carries an unramified datum at `y = 0`
(`exists_unramDatum`). -/
theorem kummerUnramFor {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (F : Type v) [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] (a : C) :
    KummerUnramFor.{u, v, v} C F a := by
  have hE0 : 0 < (Module.finrank (RatFunc C) F).factorial := Nat.factorial_pos _
  have hy := transcendental_kummerRoot (F := F) hE0 a
  haveI : FiniteDimensional (RatFunc C) (KummerField F hE0 a) :=
    Module.Finite.trans F (KummerField F hE0 a)
  haveI : IsCurveFunctionField C (KummerField F hE0 a) := isCurveFunctionField_F
  haveI : IsCurveFunctionField C (Coord hy) :=
    inferInstanceAs (IsCurveFunctionField C (KummerField F hE0 a))
  haveI : FiniteDimensional (RatFunc C) (Coord hy) :=
    finiteDimensional_of_transcendental (by rw [xF_coord_eq]; exact hy)
  have hgen : ∀ s : KummerField F hE0 a, ∃ p : F[X], aeval (kummerRoot (F := F) hE0 a) p = s :=
    fun s ↦ AdjoinRoot.induction_on _ s fun p ↦ ⟨p, AdjoinRoot.aeval_eq p⟩
  have hun : ∀ R ∈ zeros C (xF C (Coord hy)), R.valuation (xF C (Coord hy)) = exp (-1) :=
    fun R hR ↦ valuation_kummer_eq (fun k hk1 hkN ↦ Nat.dvd_factorial hk1 hkN) hE0 hy
      (kummerRoot_pow hE0 a) hgen R hR
  obtain ⟨θ, n, γ, hU⟩ := exists_unramDatum (G := Coord hy) hun
  refine ⟨_, KummerField F hE0 a, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, kummerRoot hE0 a, hy, hE0, kummerRoot_pow hE0 a, adjoin_kummerRoot hE0 a,
    inferInstance, (toCoord hy).symm θ, n, γ, ?_⟩
  rw [RingEquiv.apply_symm_apply]
  exact hU

end Main

end ClassicalSmooth

end SemistableReduction
