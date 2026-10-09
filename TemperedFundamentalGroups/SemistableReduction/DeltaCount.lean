/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GenusBetti

/-!
# The abstract δ-count on a family of curves

Blueprint §9.9, S7.1–S7.3. Let `k` be algebraically closed and `κ j` (`j ∈ J`, finite) function
fields of one variable over `k`, the components of a (normalized) special fibre. A *branch* is a
pair `(j, Q)` of a component and a place of it.

* **S7.1** `CurvePlace.exists_jet`: for a divisor `D` of large degree vanishing on a finite set `S`
  of places, every family of targets `τ_Q ∈ O_Q` (`Q ∈ S`) is matched to order `M` by some
  `f ∈ L(D)`;
* `jetKer M S`, `regAt S`, `eqRes S`: the elements of `Π_j κ j` of order `≥ M` at all branches of
  `S`, regular at all branches of `S`, regular with equal residues at all branches of `S`;
* **S7.2** `finrank_add_sum_le`: let `R ⊆ Π_j L(D_j)` (`deg D_j ≫ 0`), and let *points* `p` be
  given by pairwise disjoint branch sets `S p` (where the `D_j` vanish) and condition spaces `O p`
  with `R ⊆ O p + K_{M,p}`. If the families `t p` of elements regular at `S p` are independent
  modulo `O p + K_{M,p}`, then `dim R + Σ_p #(t p) ≤ Σ_j ℓ(D_j)`;
* **S7.3** `exists_indep_of_le_eqRes`: if the condition space consists of elements with equal
  residues at the `r ≥ 1` branches of `S`, there are `r - 1` elements regular at `S`, independent
  modulo it plus `K_{M}` (`M ≥ 1`); i.e. `δ ≥ r - 1`.
-/

open WithZero

namespace SemistableReduction

namespace CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ]

/-- One step of the jet approximation: if `ord_Q e ≥ n` and `ord_Q g = n`, then subtracting
`res (e / g) · g` raises the order of `e` to `n + 1`. -/
lemma valuation_sub_res_mul_le (Q : CurvePlace k κ) {e g : κ} {n : ℤ}
    (he : Q.valuation e ≤ exp (-n)) (hg : Q.valuation g = exp (-n)) :
    Q.valuation (e - algebraMap k κ (Q.res (e / g)) * g) ≤ exp (-(n + 1)) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [map_zero] at hg
    exact exp_ne_zero hg.symm
  have hq : e / g ∈ Q.V := by
    refine Q.valuation_le_one_iff.1 ?_
    rw [map_div₀, hg, div_le_one₀ exp_pos]
    exact he
  have h1 := WithZero.le_exp_of_lt_exp_add_one (n := -1)
    (by simpa using Q.valuation_sub_res_lt_one hq)
  have : e - algebraMap k κ (Q.res (e / g)) * g = (e / g - algebraMap k κ (Q.res (e / g))) * g := by
    field_simp
  rw [this, map_mul, hg]
  calc Q.valuation (e / g - algebraMap k κ (Q.res (e / g))) * exp (-n) ≤ exp (-1) * exp (-n) := by
        gcongr
    _ = exp (-(n + 1)) := by rw [← exp_add]; ring_nf

/-- Elements of exact order `n` at `Q ∈ S` and of order `≥ M` at the other places of `S`
(R7, via `exists_interpolating`). -/
theorem exists_jet_basis : ∃ c : ℤ, ∀ (D : CurveDivisor k κ) (S : Finset (CurvePlace k κ))
    (M : ℕ), c + M * S.card ≤ D.degree → (∀ Q ∈ S, D Q = 0) → ∀ Q ∈ S, ∀ n ≤ M,
      ∃ f ∈ rrSpace D, Q.valuation f = exp (-(n : ℤ)) ∧
        ∀ Q' ∈ S, Q' ≠ Q → Q'.valuation f ≤ exp (-(M : ℤ)) := by
  classical
  obtain ⟨c, hc⟩ := exists_interpolating (k := k) (κ := κ)
  refine ⟨c, fun D S M hdeg hD Q hQ n hn ↦ ?_⟩
  set D' : CurveDivisor k κ := D - n • Finsupp.single Q 1 - M • sumPlaces (S.erase Q)
  have hcard : (S.erase Q).card + 1 = S.card := Finset.card_erase_add_one hQ
  have hdeg' : c + (∅ : Finset (CurvePlace k κ)).card ≤ D'.degree := by
    simp only [D', _root_.map_sub, map_nsmul, Finsupp.degree_single, degree_sumPlaces,
      Finset.card_empty, Nat.cast_zero, add_zero, nsmul_eq_mul, mul_one]
    have : (S.card : ℤ) = (S.erase Q).card + 1 := by exact_mod_cast hcard.symm
    rw [this] at hdeg
    nlinarith
  obtain ⟨f, hf, hfQ, -⟩ := hc D' ∅ Q (Finset.notMem_empty Q) hdeg'
  have hD'Q : D' Q = -(n : ℤ) := by
    simp [D', sumPlaces_apply, hD Q hQ]
  have hle : D' ≤ D := by
    intro P
    simp only [D', Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply, sumPlaces_apply,
      Finsupp.single_apply]
    have h1 : (0 : ℤ) ≤ n * (if Q = P then 1 else 0) := by split_ifs <;> simp
    have h2 : (0 : ℤ) ≤ M * (if P ∈ S.erase Q then 1 else 0) := by split_ifs <;> simp
    simp only [nsmul_eq_mul] at h1 h2 ⊢
    linarith
  refine ⟨f, rrSpace_mono hle hf, by rw [hfQ, hD'Q], fun Q' hQ' hne ↦ ?_⟩
  refine (hf Q').trans ?_
  rw [exp_le_exp]
  simp [D', sumPlaces_apply, hD Q' hQ', Finset.mem_erase, hne, hQ']

/-- **Jet interpolation** (S7.1): for `D` of large degree vanishing on `S`, every family of
targets `τ_Q ∈ O_Q` is approximated to order `M` at all `Q ∈ S` by some `f ∈ L(D)`. -/
theorem exists_jet : ∃ c : ℤ, ∀ (D : CurveDivisor k κ) (S : Finset (CurvePlace k κ))
    (M : ℕ), c + M * S.card ≤ D.degree → (∀ Q ∈ S, D Q = 0) →
      ∀ τ : CurvePlace k κ → κ, (∀ Q ∈ S, τ Q ∈ Q.V) →
        ∃ f ∈ rrSpace D, ∀ Q ∈ S, Q.valuation (f - τ Q) ≤ exp (-(M : ℤ)) := by
  classical
  obtain ⟨c, hc⟩ := exists_jet_basis (k := k) (κ := κ)
  refine ⟨c, fun D S M hdeg hD τ hτ ↦ ?_⟩
  suffices h : ∀ n ≤ M, ∃ f ∈ rrSpace D, ∀ Q ∈ S, Q.valuation (f - τ Q) ≤ exp (-(n : ℤ)) from
    h M le_rfl
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, zero_mem _, fun Q hQ ↦ ?_⟩
    rw [zero_sub, Valuation.map_neg, Nat.cast_zero, neg_zero, exp_zero]
    exact Q.valuation_le_one_iff.2 (hτ Q hQ)
  | succ n ih =>
    intro hn
    obtain ⟨f, hf, hfS⟩ := ih (Nat.le_of_succ_le hn)
    have hb (Q : CurvePlace k κ) : ∃ g : κ, Q ∈ S → g ∈ rrSpace D ∧
        Q.valuation g = exp (-(n : ℤ)) ∧ ∀ Q' ∈ S, Q' ≠ Q → Q'.valuation g ≤ exp (-(M : ℤ)) := by
      by_cases hQ : Q ∈ S
      · obtain ⟨g, hg⟩ := hc D S M hdeg hD Q hQ n (Nat.le_of_succ_le hn)
        exact ⟨g, fun _ ↦ hg⟩
      · exact ⟨0, fun h ↦ absurd h hQ⟩
    choose g hg using hb
    set a : CurvePlace k κ → k := fun Q ↦ Q.res ((τ Q - f) / g Q)
    refine ⟨f + ∑ Q ∈ S, algebraMap k κ (a Q) * g Q, add_mem hf (Submodule.sum_mem _
      fun Q hQ ↦ by rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hg Q hQ).1),
      fun Q hQ ↦ ?_⟩
    have hsplit : f + ∑ Q' ∈ S, algebraMap k κ (a Q') * g Q' - τ Q =
        -((τ Q - f) - algebraMap k κ (a Q) * g Q) +
          ∑ Q' ∈ S.erase Q, algebraMap k κ (a Q') * g Q' := by
      rw [← Finset.add_sum_erase S _ hQ]
      ring
    rw [hsplit]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_neg]
      have h1 : Q.valuation (τ Q - f) ≤ exp (-(n : ℤ)) := by
        rw [← Valuation.map_neg, neg_sub]
        exact hfS Q hQ
      have := Q.valuation_sub_res_mul_le h1 (hg Q hQ).2.1
      simpa [a] using this
    · refine Valuation.map_sum_le _ fun Q' hQ' ↦ ?_
      obtain ⟨hne, hQ'S⟩ := Finset.mem_erase.1 hQ'
      rw [map_mul]
      refine (mul_le_of_le_one_left' (Q.valuation_algebraMap_le_one _)).trans
        (((hg Q' hQ'S).2.2 Q hQ (Ne.symm hne)).trans ?_)
      rw [exp_le_exp]
      omega

end CurvePlace

namespace DeltaCount

variable {k : Type*} [Field k] {J : Type*} {κ : J → Type*} [∀ j, Field (κ j)]
  [∀ j, Algebra k (κ j)] [IsAlgClosed k] [∀ j, IsCurveFunctionField k (κ j)]

/-- A branch: a component together with a place of it. -/
abbrev Branch (k : Type*) [Field k] {J : Type*} (κ : J → Type*) [∀ j, Field (κ j)]
    [∀ j, Algebra k (κ j)] := Σ j : J, CurvePlace k (κ j)

variable (k κ) in
/-- The elements of order `≥ M` at all branches of `S`. -/
def jetKer (M : ℕ) (S : Finset (Branch k κ)) : Submodule k (Π j, κ j) where
  carrier := {a | ∀ b ∈ S, b.2.valuation (a b.1) ≤ exp (-(M : ℤ))}
  add_mem' ha hb b hbS := (Valuation.map_add _ _ _).trans (max_le (ha b hbS) (hb b hbS))
  zero_mem' b _ := by simp
  smul_mem' c a ha b hbS := by
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (b.2.valuation_algebraMap_le_one c)).trans (ha b hbS)

variable (k κ) in
/-- The elements regular at all branches of `S`. -/
def regAt (S : Finset (Branch k κ)) : Submodule k (Π j, κ j) where
  carrier := {a | ∀ b ∈ S, a b.1 ∈ b.2.V}
  add_mem' ha hb b hbS := add_mem (ha b hbS) (hb b hbS)
  zero_mem' b _ := zero_mem _
  smul_mem' c a ha b hbS := by
    simp only [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem (b.2.algebraMap_mem c) (ha b hbS)

lemma jetKer_le_regAt (M : ℕ) (S : Finset (Branch k κ)) : jetKer k κ M S ≤ regAt k κ S :=
  fun a ha b hbS ↦ b.2.valuation_le_one_iff.1 ((ha b hbS).trans (by
    rw [← exp_zero, exp_le_exp]; omega))

section Res

variable (k κ) in
/-- The elements regular at all branches of `S` with equal residues there. -/
def eqRes (S : Finset (Branch k κ)) : Submodule k (Π j, κ j) where
  carrier := {a | a ∈ regAt k κ S ∧ ∀ b ∈ S, ∀ b' ∈ S, b.2.res (a b.1) = b'.2.res (a b'.1)}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, fun b hb' b' hb'' ↦ by
    simp only [Pi.add_apply]
    rw [b.2.res_add (ha.1 b hb') (hb.1 b hb'), b'.2.res_add (ha.1 b' hb'') (hb.1 b' hb''),
      ha.2 b hb' b' hb'', hb.2 b hb' b' hb'']⟩
  zero_mem' := ⟨zero_mem _, fun b _ b' _ ↦ by simp [CurvePlace.res_zero]⟩
  smul_mem' c a ha := ⟨Submodule.smul_mem _ c ha.1, fun b hb b' hb' ↦ by
    simp only [Pi.smul_apply]
    rw [b.2.res_smul (ha.1 b hb), b'.2.res_smul (ha.1 b' hb'), ha.2 b hb b' hb']⟩

lemma jetKer_le_eqRes {M : ℕ} (hM : 1 ≤ M) (S : Finset (Branch k κ)) :
    jetKer k κ M S ≤ eqRes k κ S := by
  have h0 (a) (ha : a ∈ jetKer k κ M S) (b : Branch k κ) (hb : b ∈ S) : b.2.res (a b.1) = 0 :=
    b.2.res_eq_of_valuation_sub_lt_one (by
      rw [map_zero, sub_zero]
      exact (ha b hb).trans_lt (by rw [← exp_zero, exp_lt_exp]; omega))
  exact fun a ha ↦ ⟨jetKer_le_regAt M S ha, fun b hb b' hb' ↦ by rw [h0 a ha b hb, h0 a ha b' hb']⟩

/-- **`δ ≥ r - 1`** (S7.3): for a nonempty set `S` of `r` branches, there are `r - 1` elements
regular at `S` (indexed by `S ∖ {b₀}`) that are independent modulo every subspace of `eqRes S`. -/
theorem exists_indep_of_le_eqRes [DecidableEq (Branch k κ)]
    (S : Finset (Branch k κ)) (b₀ : Branch k κ) :
    ∃ t : S.erase b₀ → Π j, κ j, (∀ i, t i ∈ regAt k κ S) ∧ ∀ N : Submodule k (Π j, κ j),
      N ≤ eqRes k κ S → b₀ ∈ S → ∀ a : S.erase b₀ → k, ∑ i, a i • t i ∈ N → a = 0 := by
  classical
  -- `u b` is `≈ 1` at `b` and `≈ 0` at the other branches of `S` on the same component
  have hu (b : Branch k κ) : ∃ u : κ b.1, b.2.valuation (u - 1) < 1 ∧
      ∀ Q : CurvePlace k (κ b.1), (⟨b.1, Q⟩ : Branch k κ) ∈ S → Q ≠ b.2 → Q.valuation u < 1 := by
    obtain ⟨u, hu1, huS⟩ := b.2.exists_valuation_sub_one_lt_one
      (S.preimage (fun Q : CurvePlace k (κ b.1) ↦ (⟨b.1, Q⟩ : Branch k κ))
        fun _ _ _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.1 h).2)
      (fun _ ↦ exp (-1)) fun _ ↦ exp_ne_zero
    refine ⟨u, hu1, fun Q hQ hne ↦ (huS Q (Finset.mem_preimage.2 hQ) hne).trans_lt ?_⟩
    rw [← exp_zero, exp_lt_exp]
    omega
  choose u hu1 hu0 using hu
  have hu1' (b : Branch k κ) : b.2.res (u b) = 1 :=
    b.2.res_eq_of_valuation_sub_lt_one (by simpa using hu1 b)
  have hu0' (b : Branch k κ) (Q : CurvePlace k (κ b.1)) (hQ : (⟨b.1, Q⟩ : Branch k κ) ∈ S)
      (hne : Q ≠ b.2) : Q.res (u b) = 0 :=
    Q.res_eq_of_valuation_sub_lt_one (by simpa using hu0 b Q hQ hne)
  have humem (b : Branch k κ) : u b ∈ b.2.V := by
    have : u b = (u b - 1) + 1 := by ring
    rw [this]
    exact add_mem (b.2.valuation_le_one_iff.1 (hu1 b).le) (one_mem _)
  set t : S.erase b₀ → Π j, κ j := fun i ↦ Pi.single i.1.1 (u i.1)
  have hres (i : S.erase b₀) (b : Branch k κ) (hb : b ∈ S) :
      b.2.res (t i b.1) = if b = i.1 then 1 else 0 := by
    obtain ⟨⟨j, Q⟩, hi⟩ := i
    obtain ⟨j', Q'⟩ := b
    simp only [t]
    by_cases hj : j' = j
    · subst hj
      rw [Pi.single_eq_same]
      by_cases hQ : Q' = Q
      · subst hQ
        simpa using hu1' ⟨j', Q'⟩
      · simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, hQ, if_false]
        exact hu0' ⟨j', Q⟩ Q' hb hQ
    · rw [Pi.single_eq_of_ne hj, CurvePlace.res_zero]
      simp [hj]
  have hreg (i : S.erase b₀) : t i ∈ regAt k κ S := by
    intro b hb
    obtain ⟨⟨j, Q⟩, hi⟩ := i
    obtain ⟨j', Q'⟩ := b
    simp only [t]
    by_cases hj : j' = j
    · subst hj
      rw [Pi.single_eq_same]
      by_cases hQ : Q' = Q
      · subst hQ
        exact humem ⟨j', Q'⟩
      · exact Q'.valuation_le_one_iff.1 (hu0 ⟨j', Q⟩ Q' hb hQ).le
    · rw [Pi.single_eq_of_ne hj]
      exact zero_mem _
  refine ⟨t, hreg, fun N hN hb₀ a ha ↦ funext fun i ↦ ?_⟩
  obtain ⟨-, hseq⟩ := hN ha
  have hsum (b : Branch k κ) (hb : b ∈ S) (s : Finset (S.erase b₀)) :
      b.2.res ((∑ i ∈ s, a i • t i) b.1) = ∑ i ∈ s, a i * b.2.res (t i b.1) := by
    induction s using Finset.induction_on with
    | empty => simp [CurvePlace.res_zero]
    | insert x s hx ih =>
      have h1 : (a x • t x) b.1 ∈ b.2.V := Submodule.smul_mem _ _ (hreg x) b hb
      have h2 : (∑ i ∈ s, a i • t i) b.1 ∈ b.2.V :=
        Submodule.sum_mem (regAt k κ S) (fun i _ ↦ Submodule.smul_mem _ _ (hreg i)) b hb
      rw [Finset.sum_insert hx, Finset.sum_insert hx, Pi.add_apply, b.2.res_add h1 h2,
        Pi.smul_apply, b.2.res_smul (hreg x b hb), ih]
  have hi := Finset.mem_of_mem_erase i.2
  have h1 := hsum i.1 hi Finset.univ
  have h0 := hsum b₀ hb₀ Finset.univ
  have hb0 (i' : S.erase b₀) : b₀ ≠ i'.1 := fun h ↦ by
    have := i'.2
    rw [← h] at this
    exact (Finset.mem_erase.1 this).1 rfl
  simp only [hres _ _ hi, hres _ _ hb₀, hb0, if_false, mul_zero, Finset.sum_const_zero,
    mul_ite, mul_one] at h1 h0
  have hii (i' : S.erase b₀) : (i.1 = i'.1) ↔ (i' = i) :=
    ⟨fun h ↦ (Subtype.ext h).symm, fun h ↦ h ▸ rfl⟩
  simp only [hii, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  rw [Pi.zero_apply, ← h1, hseq _ hi b₀ hb₀, h0]

/-- `δ ≥ r - 1` in finset form: a set of `r - 1` elements regular at `S`, independent modulo every
subspace of `eqRes S`. -/
theorem exists_finset_indep_of_le_eqRes
    (S : Finset (Branch k κ)) {b₀ : Branch k κ} (hb₀ : b₀ ∈ S) :
    ∃ A : Finset (Π j, κ j), A.card = S.card - 1 ∧ (∀ y ∈ A, y ∈ regAt k κ S) ∧
      ∀ N : Submodule k (Π j, κ j), N ≤ eqRes k κ S → ∀ a : A → k, ∑ i, a i • (i : Π j, κ j) ∈ N →
        a = 0 := by
  classical
  obtain ⟨t, ht, hind⟩ := exists_indep_of_le_eqRes S b₀
  have hinj : Function.Injective t := by
    intro i i' h
    by_contra hne
    have := hind (eqRes k κ S) le_rfl hb₀ (Pi.single i 1 - Pi.single i' 1) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h, sub_self]
      exact zero_mem _)
    have h1 := congrFun this i
    simp [Ne.symm hne] at h1
  refine ⟨Finset.univ.image t, ?_, fun y hy ↦ ?_, fun N hN a ha ↦ ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe,
      Finset.card_erase_of_mem hb₀]
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact ht i
  · set e : S.erase b₀ → (Finset.univ.image t : Finset (Π j, κ j)) := fun i ↦
      ⟨t i, Finset.mem_image_of_mem t (Finset.mem_univ i)⟩
    have he : Function.Bijective e := ⟨fun i i' h ↦ hinj (congrArg Subtype.val h), fun y ↦ by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 y.2
      exact ⟨i, Subtype.ext hi⟩⟩
    have hsum : ∑ i, a i • (i : Π j, κ j) = ∑ i, (a ∘ e) i • t i :=
      (Fintype.sum_bijective e he _ _ fun _ ↦ rfl).symm
    rw [hsum] at ha
    have h0 := hind N hN hb₀ (a ∘ e) ha
    funext y
    obtain ⟨i, rfl⟩ := he.2 y
    exact congrFun h0 i

end Res

section Count

omit [IsAlgClosed k] in
/-- **Linear algebra of the count.** Let `R ≤ W` lie in the condition spaces `N p`, and let
`w p i ∈ W` agree with `t p i` modulo `K p ≤ N p` and lie in `K q` for `q ≠ p`. If the `t p` are
independent modulo `N p`, then `dim R + Σ_p #(T p) ≤ dim W`. -/
theorem finrank_add_sum_le_of_lift {U : Type*} [AddCommGroup U] [Module k U] {ι : Type*}
    [Fintype ι] {T : ι → Type*} [∀ p, Fintype (T p)] (W R : Submodule k U)
    [FiniteDimensional k W] (N K : ι → Submodule k U) (hK : ∀ p, K p ≤ N p)
    (hR : R ≤ W) (hRN : ∀ p, R ≤ N p) (t w : ∀ p, T p → U) (hw : ∀ p i, w p i ∈ W)
    (hwt : ∀ p i, w p i - t p i ∈ K p) (hwK : ∀ p q, q ≠ p → ∀ i, w q i ∈ K p)
    (ht : ∀ p, ∀ a : T p → k, ∑ i, a i • t p i ∈ N p → a = 0) :
    Module.finrank k R + ∑ p, Fintype.card (T p) ≤ Module.finrank k W := by
  classical
  set v : (Σ p, T p) → U := fun x ↦ w x.1 x.2
  have hkey (a : (Σ p, T p) → k) (ha : ∀ p, ∑ x, a x • v x ∈ N p) : a = 0 := by
    funext ⟨p, i⟩
    have hsplit : ∑ x, a x • v x = ∑ i, a ⟨p, i⟩ • t p i +
        (∑ i, a ⟨p, i⟩ • (w p i - t p i) +
          ∑ q ∈ Finset.univ.erase p, ∑ i, a ⟨q, i⟩ • w q i) := by
      rw [Fintype.sum_sigma, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
      simp only [v, smul_sub, Finset.sum_sub_distrib]
      abel
    have hK' : ∑ i, a ⟨p, i⟩ • (w p i - t p i) +
        ∑ q ∈ Finset.univ.erase p, ∑ i, a ⟨q, i⟩ • w q i ∈ K p :=
      add_mem (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hwt p i))
        (Submodule.sum_mem _ fun q hq ↦ Submodule.sum_mem _ fun i _ ↦
          Submodule.smul_mem _ _ (hwK p q (Finset.ne_of_mem_erase hq) i))
    have hmem : ∑ i, a ⟨p, i⟩ • t p i ∈ N p := by
      have := sub_mem (ha p) (hK p hK')
      rwa [hsplit, add_sub_cancel_right] at this
    exact congrFun (ht p (fun i ↦ a ⟨p, i⟩) hmem) i
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    exact congrFun (hkey a fun p ↦ by rw [ha]; exact zero_mem _)
  set S := Submodule.span k (Set.range v)
  have hS : Module.finrank k S = ∑ p, Fintype.card (T p) := by
    rw [finrank_span_eq_card hli, Fintype.card_sigma]
  have hinf : R ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyR, hyS⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hyS
    have := hkey a fun p ↦ hRN p hyR
    simp [this]
  have hle : R ⊔ S ≤ W :=
    sup_le hR (Submodule.span_le.2 (Set.range_subset_iff.2 fun x ↦ hw x.1 x.2))
  haveI : FiniteDimensional k R := Submodule.finiteDimensional_of_le hR
  haveI : FiniteDimensional k S := Submodule.finiteDimensional_of_le (le_sup_right.trans hle)
  have h := Submodule.finrank_sup_add_finrank_inf_eq R S
  haveI : FiniteDimensional k (R ⊔ S : Submodule k U) :=
    Submodule.finiteDimensional_of_le hle
  rw [hinf, finrank_bot, add_zero, hS] at h
  rw [← h]
  exact Submodule.finrank_mono hle

variable [Fintype J]

variable (k κ) in
/-- The product `Π_j L(D_j)` of Riemann–Roch spaces. -/
def piRR (D : ∀ j, CurveDivisor k (κ j)) : Submodule k (Π j, κ j) :=
  Submodule.pi Set.univ fun j ↦ rrSpace (D j)

/-- `piRR` is the product of the Riemann–Roch spaces. -/
noncomputable def piRREquiv (D : ∀ j, CurveDivisor k (κ j)) :
    piRR k κ D ≃ₗ[k] Π j, rrSpace (D j) where
  toFun x j := ⟨x.1 j, x.2 j trivial⟩
  invFun y := ⟨fun j ↦ (y j).1, fun j _ ↦ (y j).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype J] in
instance finiteDimensional_piRR [Finite J] (D : ∀ j, CurveDivisor k (κ j)) :
    FiniteDimensional k (piRR k κ D) :=
  LinearEquiv.finiteDimensional (piRREquiv D).symm

lemma finrank_piRR (D : ∀ j, CurveDivisor k (κ j)) :
    Module.finrank k (piRR k κ D) = ∑ j, ell (D j) := by
  rw [(piRREquiv D).finrank_eq, Module.finrank_pi_fintype]
  rfl

/-- **The abstract δ-count** (S7.2). There are constants `c j` such that: if `deg D_j ≥ c j +
M · Σ_p #(S p)`, the branch sets `S p` are pairwise disjoint with `D` vanishing there, `R ≤ Π_j
L(D_j)` lies in `O p + K_{M, p}` for all `p`, and `t p` are families of elements regular at `S p`,
independent modulo `O p + K_{M, p}`, then `dim R + Σ_p #(T p) ≤ Σ_j ℓ(D_j)`. -/
theorem finrank_add_sum_le {ι : Type*} [Fintype ι]
    (S : ι → Finset (Branch k κ)) {T : ι → Type*} [∀ p, Fintype (T p)] :
    ∃ c : J → ℤ, ∀ (D : ∀ j, CurveDivisor k (κ j)) (M : ℕ),
    (∀ j, c j + M * ∑ p, (S p).card ≤ (D j).degree) →
    (∀ p, ∀ b ∈ S p, D b.1 b.2 = 0) → (∀ p q, p ≠ q → Disjoint (S p) (S q)) →
    ∀ (O : ι → Submodule k (Π j, κ j)) (R : Submodule k (Π j, κ j)), R ≤ piRR k κ D →
    (∀ p, R ≤ O p ⊔ jetKer k κ M (S p)) →
    ∀ (t : ∀ p, T p → Π j, κ j),
    (∀ p i, t p i ∈ regAt k κ (S p)) →
    (∀ p, ∀ a : T p → k, ∑ i, a i • t p i ∈ O p ⊔ jetKer k κ M (S p) → a = 0) →
    Module.finrank k R + ∑ p, Fintype.card (T p) ≤ ∑ j, ell (D j) := by
  classical
  choose c hc using fun j ↦ CurvePlace.exists_jet (k := k) (κ := κ j)
  refine ⟨c, fun D M hdeg hD hdisj O R hR hRO t ht hind ↦ ?_⟩
  -- all branches on the component `j`
  set A : Finset (Branch k κ) := Finset.univ.biUnion S
  set B : (j : J) → Finset (CurvePlace k (κ j)) := fun j ↦
    A.preimage (fun Q : CurvePlace k (κ j) ↦ (⟨j, Q⟩ : Branch k κ))
      fun _ _ _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.1 h).2
  have hB (j : J) (Q : CurvePlace k (κ j)) : Q ∈ B j ↔ (⟨j, Q⟩ : Branch k κ) ∈ A :=
    Finset.mem_preimage
  have hBcard (j : J) : (B j).card ≤ ∑ p, (S p).card := by
    refine le_trans (Finset.card_le_card_of_injOn (fun Q ↦ (⟨j, Q⟩ : Branch k κ))
      (fun Q hQ ↦ (hB j Q).1 hQ) fun _ _ _ _ h ↦ eq_of_heq (Sigma.mk.inj h).2) ?_
    exact Finset.card_biUnion_le
  -- the owner of a branch
  have hlift (p : ι) (i : T p) : ∃ v ∈ piRR k κ D, v - t p i ∈ jetKer k κ M (S p) ∧
      ∀ q, q ≠ p → v ∈ jetKer k κ M (S q) := by
    have hj (j : J) := hc j (D j) (B j) M (le_trans (by
        have := hBcard j
        have : (M : ℤ) * (B j).card ≤ M * ∑ p, (S p).card := by
          exact_mod_cast Nat.mul_le_mul_left M this
        linarith) (hdeg j))
      (fun Q hQ ↦ by
        obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 ((hB j Q).1 hQ)
        exact hD q _ hq)
      (fun Q ↦ if (⟨j, Q⟩ : Branch k κ) ∈ S p then t p i j else 0)
      (fun Q hQ ↦ by
        split_ifs with h
        · exact ht p i _ h
        · exact zero_mem _)
    choose v hv hvQ using hj
    refine ⟨v, fun j _ ↦ hv j, fun b hb ↦ ?_, fun q hqp b hb ↦ ?_⟩
    · have hbA : b ∈ A := Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _, hb⟩
      have := hvQ b.1 b.2 ((hB b.1 b.2).2 hbA)
      simpa [hb] using this
    · have hbA : b ∈ A := Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, hb⟩
      have hbp : b ∉ S p := fun h ↦ Finset.disjoint_left.1 (hdisj q p hqp) hb h
      have := hvQ b.1 b.2 ((hB b.1 b.2).2 hbA)
      simpa [hbp] using this
  choose w hw hwt hwK using hlift
  rw [← finrank_piRR]
  exact finrank_add_sum_le_of_lift (piRR k κ D) R (fun p ↦ O p ⊔ jetKer k κ M (S p))
    (fun p ↦ jetKer k κ M (S p)) (fun p ↦ le_sup_right) hR hRO t w hw hwt
    (fun p q hqp i ↦ hwK q i p (Ne.symm hqp)) hind

end Count

end DeltaCount

end SemistableReduction
