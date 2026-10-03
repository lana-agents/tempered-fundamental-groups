/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussLimit
import TemperedFundamentalGroups.SemistableReduction.AnnulusUnit

/-!
# Limits of nested discs and germs of annuli

Blueprint §9.9, S8.1 (the limit construction of the compactness argument). Let `K` be an
algebraically closed field with a valuation `v` (any value group). A sequence of closed discs
`D(aₙ, rₙ) = {w : w(X - aₙ) ≤ rₙ}` is **nested** (`DiscLimit.IsNested`) if `r_{n+1} ≤ rₙ` and
`v(a_{n+1} - aₙ) ≤ rₙ`.

* `DiscLimit.limit`: a sequence of valuations which is eventually constant at every element has a
  limit valuation (S8.1a);
* **type 4** (S8.1b): if the discs have no common point in `K`, the Gauss values
  `w_{aₙ,rₙ}(f)` are eventually constant (`isEventuallyConst_gaussRat`); their limit `limitVal`
  extends `v`, lies in every disc (`limitVal_X_sub_C_le`), is the unique valuation extending `v`
  lying in every disc (`eq_limitVal`) and is not a Gauss valuation (`limitVal_ne_gaussRat`);
* **common point / type 1** (S8.1c): if `b` lies in every disc, then `w_{aₙ,rₙ} = w_{b,rₙ}`
  (`gaussRat_eq_of_le`); if moreover the radii tend to `0`, no valuation extending `v` lies in all
  discs (`not_forall_le_of_tendsto_zero`) and `w_{aₙ,rₙ}(p) = v(p(b))` for `n ≫ 0` whenever
  `p(b) ≠ 0` (`eventually_gaussRat_eq_eval`);
* **germs, types 3 and 5** (S8.1d): a nonzero rational function is monomial (`AnnulusUnit`, S1)
  on a one-sided interval of radii `(ρ, ρ')` above (`exists_isMonomialOn_above`) or below
  (`exists_isMonomialOn_below`) any radius `ρ`, and on a two-sided interval around `ρ` if `ρ` is not
  the absolute value of a zero or pole (`exists_isMonomialOn_around`), e.g. `ρ ∉ v(K)`.
-/

open Polynomial Filter

namespace SemistableReduction

namespace DiscLimit

/-! ### Eventual limits of valuations -/

section Limit

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A sequence of valuations is eventually constant at every element. -/
def IsEventuallyConst (w : ℕ → Valuation R Γ₀) : Prop :=
  ∀ f : R, ∃ N, ∀ n ≥ N, w n f = w N f

variable {w : ℕ → Valuation R Γ₀}

/-- An index from which on `w n f` is constant. -/
noncomputable def stab (h : IsEventuallyConst w) (f : R) : ℕ := (h f).choose

lemma eq_stab (h : IsEventuallyConst w) {f : R} {n : ℕ} (hn : stab h f ≤ n) :
    w n f = w (stab h f) f :=
  (h f).choose_spec n hn

/-- The limit of a sequence of valuations which is eventually constant at every element. -/
noncomputable def limit (h : IsEventuallyConst w) : Valuation R Γ₀ where
  toFun f := w (stab h f) f
  map_zero' := map_zero _
  map_one' := map_one _
  map_mul' f g := by
    have h1 := eq_stab h (le_max_left (stab h (f * g)) (max (stab h f) (stab h g)))
    have h2 := eq_stab h ((le_max_left (stab h f) (stab h g)).trans
      (le_max_right (stab h (f * g)) _))
    have h3 := eq_stab h ((le_max_right (stab h f) (stab h g)).trans
      (le_max_right (stab h (f * g)) _))
    rw [← h1, ← h2, ← h3, map_mul]
  map_add_le_max' f g := by
    have h1 := eq_stab h (le_max_left (stab h (f + g)) (max (stab h f) (stab h g)))
    have h2 := eq_stab h ((le_max_left (stab h f) (stab h g)).trans
      (le_max_right (stab h (f + g)) _))
    have h3 := eq_stab h ((le_max_right (stab h f) (stab h g)).trans
      (le_max_right (stab h (f + g)) _))
    rw [← h1, ← h2, ← h3]
    exact Valuation.map_add _ _ _

lemma limit_eq (h : IsEventuallyConst w) {f : R} {n : ℕ} (hn : stab h f ≤ n) :
    limit h f = w n f :=
  (eq_stab h hn).symm

/-- The limit agrees with `w n` at `f` for all large `n`. -/
lemma eventually_limit_eq (h : IsEventuallyConst w) (f : R) : ∀ᶠ n in atTop, limit h f = w n f :=
  eventually_atTop.2 ⟨stab h f, fun _ hn ↦ limit_eq h hn⟩

/-- A sequence of valuations which is eventually equal to some value at every element is
eventually constant at every element. -/
lemma isEventuallyConst_of_forall (hw : ∀ f, ∃ c, ∀ᶠ n in atTop, w n f = c) :
    IsEventuallyConst w := by
  intro f
  obtain ⟨c, hc⟩ := hw f
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  exact ⟨N, fun n hn ↦ by rw [hN n hn, hN N le_rfl]⟩

end Limit

/-! ### Nested discs -/

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

/-- The linear polynomial `X - b` as a rational function. -/
noncomputable abbrev lin (b : K) : RatFunc K := algebraMap K[X] (RatFunc K) (X - C b)

lemma gaussRat_lin (a b : K) (r : Γ₀ˣ) : gaussRat v a r (lin b) = max (v (a - b)) r := by
  rw [lin, gaussRat_algebraMap, gauss_X_sub_C]

/-- A sequence of closed discs `D(aₙ, rₙ)` is nested. -/
structure IsNested (v : Valuation K Γ₀) (a : ℕ → K) (r : ℕ → Γ₀ˣ) : Prop where
  radius_succ_le : ∀ n, (r (n + 1) : Γ₀) ≤ r n
  center_succ_le : ∀ n, v (a (n + 1) - a n) ≤ r n

variable {a : ℕ → K} {r : ℕ → Γ₀ˣ}

namespace IsNested

lemma radius_le (h : IsNested v a r) {m n : ℕ} (hmn : m ≤ n) : (r n : Γ₀) ≤ r m := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (h.radius_succ_le n).trans ih

lemma sub_le (h : IsNested v a r) {m n : ℕ} (hmn : m ≤ n) : v (a n - a m) ≤ r m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [show a (n + 1) - a m = (a (n + 1) - a n) + (a n - a m) by ring]
    exact (Valuation.map_add _ _ _).trans
      (max_le ((h.center_succ_le n).trans (h.radius_le hmn)) ih)

/-- If `b ∉ D(a_m, r_m)`, then `v(b - aₙ) = v(b - a_m)` for `n ≥ m`. -/
lemma val_sub_eq (h : IsNested v a r) {b : K} {m n : ℕ} (hmn : m ≤ n)
    (hb : (r m : Γ₀) < v (b - a m)) : v (b - a n) = v (b - a m) := by
  rw [show b - a n = (b - a m) + (a m - a n) by ring]
  refine Valuation.map_add_eq_of_lt_left _ ?_
  rw [← Valuation.map_neg, neg_sub]
  exact (h.sub_le hmn).trans_lt hb

/-- If `b ∉ D(a_m, r_m)`, then `w_{aₙ,rₙ}(X - b) = v(b - a_m)` for `n ≥ m`. -/
lemma gaussRat_lin_eq (h : IsNested v a r) {b : K} {m n : ℕ} (hmn : m ≤ n)
    (hb : (r m : Γ₀) < v (b - a m)) : gaussRat v (a n) (r n) (lin b) = v (b - a m) := by
  rw [gaussRat_lin, ← Valuation.map_neg, neg_sub, h.val_sub_eq hmn hb, max_eq_left]
  exact (h.radius_le hmn).trans hb.le

/-- The value of `X - aₙ` at a later Gauss point `w_{a_k, r_k}`, `k ≥ n`, is at most `rₙ`. -/
lemma gaussRat_lin_center_le (h : IsNested v a r) {n k : ℕ} (hnk : n ≤ k) :
    gaussRat v (a k) (r k) (lin (a n)) ≤ r n := by
  rw [gaussRat_lin]
  exact max_le (h.sub_le hnk) (h.radius_le hnk)

end IsNested

/-! ### Type 4: nested discs without a common point -/

section TypeFour

variable [IsAlgClosed K]

/-- The rational functions at which a sequence of valuations is eventually equal to some
value form a submonoid. -/
def evSubmonoid (w : ℕ → Valuation (RatFunc K) Γ₀) : Submonoid (RatFunc K) where
  carrier := {f | ∃ c, ∀ᶠ n in atTop, w n f = c}
  one_mem' := ⟨1, Eventually.of_forall fun n ↦ map_one _⟩
  mul_mem' := by
    rintro f g ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, (hc.and hd).mono fun n ⟨h1, h2⟩ ↦ by rw [map_mul, h1, h2]⟩

lemma algebraMap_mem_evSubmonoid {w : ℕ → Valuation (RatFunc K) Γ₀}
    (hC : ∀ c : K, algebraMap K (RatFunc K) c ∈ evSubmonoid w)
    (hlin : ∀ b : K, lin b ∈ evSubmonoid w) (p : K[X]) :
    algebraMap K[X] (RatFunc K) p ∈ evSubmonoid w := by
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := p)),
    map_mul, map_multiset_prod, ratFunc_algebraMap_C, Multiset.map_map]
  refine Submonoid.mul_mem _ (hC _) (Submonoid.multiset_prod_mem _ _ fun f hf ↦ ?_)
  obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hf
  exact hlin b

lemma mem_evSubmonoid {w : ℕ → Valuation (RatFunc K) Γ₀}
    (hC : ∀ c : K, algebraMap K (RatFunc K) c ∈ evSubmonoid w)
    (hlin : ∀ b : K, lin b ∈ evSubmonoid w) (f : RatFunc K) : f ∈ evSubmonoid w := by
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) f
  obtain ⟨c, hc⟩ := algebraMap_mem_evSubmonoid hC hlin p
  obtain ⟨d, hd⟩ := algebraMap_mem_evSubmonoid hC hlin q
  exact ⟨c / d, (hc.and hd).mono fun n ⟨h1, h2⟩ ↦ by rw [map_div₀, h1, h2]⟩

/-- The discs have no common point of `K`. -/
def NoCommonPoint (v : Valuation K Γ₀) (a : ℕ → K) (r : ℕ → Γ₀ˣ) : Prop :=
  ∀ b : K, ∃ m, (r m : Γ₀) < v (b - a m)

variable (h : IsNested v a r) (hempty : NoCommonPoint v a r)
include h hempty

/-- **Type 4.** For nested discs without a common point, the Gauss values `w_{aₙ,rₙ}(f)` are
eventually constant. -/
theorem isEventuallyConst_gaussRat :
    IsEventuallyConst fun n ↦ gaussRat v (a n) (r n) := by
  refine isEventuallyConst_of_forall fun f ↦ mem_evSubmonoid (fun c ↦ ?_) (fun b ↦ ?_) f
  · exact ⟨v c, Eventually.of_forall fun n ↦ by simp only [gaussRat_algebraMap_C]⟩
  · obtain ⟨m, hm⟩ := hempty b
    exact ⟨v (b - a m), eventually_atTop.2 ⟨m, fun n hn ↦ h.gaussRat_lin_eq hn hm⟩⟩

/-- **The type-4 limit valuation** of nested discs without a common point. -/
noncomputable def limitVal : Valuation (RatFunc K) Γ₀ :=
  limit (isEventuallyConst_gaussRat h hempty)

lemma eventually_limitVal_eq (f : RatFunc K) :
    ∀ᶠ n in atTop, limitVal h hempty f = gaussRat v (a n) (r n) f :=
  eventually_limit_eq _ f

/-- The limit valuation extends `v`. -/
lemma limitVal_algebraMap (c : K) : limitVal h hempty (algebraMap K (RatFunc K) c) = v c := by
  obtain ⟨n, hn⟩ := (eventually_limitVal_eq h hempty (algebraMap K (RatFunc K) c)).exists
  rw [hn, gaussRat_algebraMap_C]

/-- The value of `X - b` at the limit, for `b ∉ D(a_m, r_m)`. -/
lemma limitVal_lin {b : K} {m : ℕ} (hb : (r m : Γ₀) < v (b - a m)) :
    limitVal h hempty (lin b) = v (b - a m) := by
  obtain ⟨n, hn, hmn⟩ :=
    ((eventually_limitVal_eq h hempty (lin b)).and (eventually_ge_atTop m)).exists
  rw [hn, h.gaussRat_lin_eq hmn hb]

/-- The limit valuation lies in every disc. -/
lemma limitVal_lin_le (n : ℕ) : limitVal h hempty (lin (a n)) ≤ r n := by
  obtain ⟨k, hk, hnk⟩ :=
    ((eventually_limitVal_eq h hempty (lin (a n))).and (eventually_ge_atTop n)).exists
  rw [hk]
  exact h.gaussRat_lin_center_le hnk

/-- **Uniqueness**: the limit is the only valuation extending `v` that lies in every disc. -/
theorem eq_limitVal {w : Valuation (RatFunc K) Γ₀}
    (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c) (hle : ∀ n, w (lin (a n)) ≤ r n) :
    w = limitVal h hempty := by
  refine valuation_ratFunc_ext_of_linear (fun c ↦ by rw [hw, limitVal_algebraMap]) fun b ↦ ?_
  obtain ⟨m, hm⟩ := hempty b
  rw [limitVal_lin h hempty hm]
  show w (algebraMap K[X] (RatFunc K) (X - C b)) = _
  have hlt : w (lin (a m)) < w (algebraMap K (RatFunc K) (a m - b)) := by
    rw [hw, ← Valuation.map_neg (v := v), neg_sub]
    exact (hle m).trans_lt hm
  rw [GaussLimit.algebraMap_X_sub_C (a m) b, Valuation.map_add_eq_of_lt_right _ hlt, hw,
    ← Valuation.map_neg, neg_sub]

/-- The limit valuation is not a Gauss valuation (it is of type 4). -/
theorem limitVal_ne_gaussRat (c : K) (s : Γ₀ˣ) : limitVal h hempty ≠ gaussRat v c s := by
  intro heq
  obtain ⟨m, hm⟩ := hempty c
  have h1 := limitVal_lin_le h hempty m
  rw [heq, gaussRat_lin] at h1
  exact absurd ((le_max_left _ _).trans h1) (not_le.2 hm)

end TypeFour

/-! ### Discs with a common point; type 1 -/

section CommonPoint

variable [IsAlgClosed K]

/-- The Gauss valuation only depends on the disc: `w_{a,r} = w_{b,r}` if `v(b - a) ≤ r`. -/
theorem gaussRat_eq_of_le {a b : K} {s : Γ₀ˣ} (hab : v (b - a) ≤ s) :
    gaussRat v a s = gaussRat v b s := by
  refine valuation_ratFunc_ext_of_linear (fun c ↦ by simp only [gaussRat_algebraMap_C])
    fun c ↦ ?_
  change gaussRat v a s (lin c) = gaussRat v b s (lin c)
  rw [gaussRat_lin, gaussRat_lin]
  have hab' : v (a - b) ≤ s := by rwa [← Valuation.map_neg, neg_sub]
  refine le_antisymm (max_le ?_ (le_max_right _ _)) (max_le ?_ (le_max_right _ _))
  · rw [show a - c = (a - b) + (b - c) by ring]
    exact (Valuation.map_add _ _ _).trans (max_le (hab'.trans (le_max_right _ _))
      (le_max_left _ _))
  · rw [show b - c = (b - a) + (a - c) by ring]
    exact (Valuation.map_add _ _ _).trans (max_le (hab.trans (le_max_right _ _))
      (le_max_left _ _))

/-- If `b` lies in every disc, the Gauss points of the discs are centred at `b`. -/
lemma gaussRat_eq_of_mem {b : K} (hb : ∀ n, v (b - a n) ≤ r n) (n : ℕ) :
    gaussRat v (a n) (r n) = gaussRat v b (r n) :=
  gaussRat_eq_of_le (hb n)

/-- The radii tend to `0`: eventually below every unit. -/
def TendstoZero (r : ℕ → Γ₀ˣ) : Prop := ∀ γ : Γ₀ˣ, ∃ n, (r n : Γ₀) < γ

omit [IsAlgClosed K] in
/-- **Type 1**: if the radii tend to `0` and `b` lies in every disc, no valuation extending `v`
lies in every disc. -/
theorem not_forall_le_of_tendsto_zero (hr : TendstoZero r) {b : K}
    (hb : ∀ n, v (b - a n) ≤ r n) {w : Valuation (RatFunc K) Γ₀}
    (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c) : ¬ ∀ n, w (lin (a n)) ≤ r n := by
  intro hle
  have hne : w (lin b) ≠ 0 := by
    rw [Ne, map_eq_zero, IsFractionRing.to_map_eq_zero_iff]
    exact X_sub_C_ne_zero b
  obtain ⟨n, hn⟩ := hr (Units.mk0 _ hne)
  refine absurd hn (not_lt.2 ?_)
  change w (algebraMap K[X] (RatFunc K) (X - C b)) ≤ r n
  rw [GaussLimit.algebraMap_X_sub_C (a n) b]
  refine (Valuation.map_add _ _ _).trans (max_le (hle n) ?_)
  rw [hw, ← Valuation.map_neg, neg_sub]
  exact hb n

/-- **Type 1**: if the radii tend to `0` and `b` lies in every disc, then `w_{aₙ,rₙ}(p) = v(p(b))`
for `n ≫ 0`, for every polynomial `p` with `p(b) ≠ 0`: the limit is the classical point `b`. -/
theorem eventually_gaussRat_eq_eval (h : IsNested v a r) (hr : TendstoZero r) {b : K}
    (hb : ∀ n, v (b - a n) ≤ r n) {p : K[X]} (hp : p.eval b ≠ 0) :
    ∀ᶠ n in atTop, gaussRat v (a n) (r n) (algebraMap K[X] (RatFunc K) p) = v (p.eval b) := by
  let M : Submonoid K[X] :=
    { carrier := {q | ∀ᶠ n in atTop,
        gaussRat v (a n) (r n) (algebraMap K[X] (RatFunc K) q) = v (q.eval b)}
      one_mem' := Eventually.of_forall fun n ↦ by simp
      mul_mem' := fun {q₁ q₂} h₁ h₂ ↦ (h₁.and h₂).mono fun n ⟨e₁, e₂⟩ ↦ by
        rw [map_mul, map_mul, e₁, e₂, eval_mul, map_mul] }
  have hlin : ∀ α : K, α ≠ b → X - C α ∈ M := by
    intro α hα
    have hne : v (b - α) ≠ 0 := by simpa [sub_eq_zero] using hα.symm
    obtain ⟨m, hm⟩ := hr (Units.mk0 _ hne)
    refine eventually_atTop.2 ⟨m, fun n hn ↦ ?_⟩
    change gaussRat v (a n) (r n) (lin α) = _
    rw [gaussRat_eq_of_mem hb, gaussRat_lin, eval_sub, eval_X, eval_C, max_eq_left]
    exact (h.radius_le hn).trans hm.le
  have hC : ∀ c : K, C c ∈ M := fun c ↦ Eventually.of_forall fun n ↦ by
    rw [ratFunc_algebraMap_C, gaussRat_algebraMap_C, eval_C]
  have : p ∈ M := by
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := p))]
    refine M.mul_mem (hC _) (M.multiset_prod_mem _ fun q hq ↦ ?_)
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hq
    refine hlin α fun hαb ↦ hp ?_
    rw [← hαb]
    exact (mem_roots'.1 hα).2
  exact this

end CommonPoint

/-! ### Germs of annuli: types 3 and 5 -/

section Germ

variable [IsAlgClosed K]

open AnnulusUnit

/-- The absolute values of the zeros and poles of `φ`. -/
noncomputable def rootValues (v : Valuation K Γ₀) (φ : RatFunc K) : Finset Γ₀ := by
  classical exact (φ.num.roots + φ.denom.roots).toFinset.image v

omit [IsAlgClosed K] in
lemma mem_rootValues {φ : RatFunc K} {α : K} (hα : α ∈ φ.num.roots ∨ α ∈ φ.denom.roots) :
    v α ∈ rootValues v φ := by
  classical
  exact Finset.mem_image_of_mem _ (Multiset.mem_toFinset.2 (Multiset.mem_add.2 hα))

/-- A nonzero rational function is monomial on the open interval `(ρ₁, ρ₂)` of radii if none of
its zeros and poles has absolute value strictly between `ρ₁` and `ρ₂`. -/
theorem isMonomialOn_Ioo {φ : RatFunc K} (hφ : φ ≠ 0) {ρ₁ ρ₂ : Γ₀}
    (hroots : ∀ t ∈ rootValues v φ, t ≤ ρ₁ ∨ ρ₂ ≤ t) :
    IsMonomialOn v {s | ρ₁ < (s : Γ₀) ∧ (s : Γ₀) < ρ₂} φ := by
  refine isMonomialOn_of_roots hφ fun α hα ↦ ?_
  rcases hroots _ (mem_rootValues hα) with h | h
  · exact Or.inl fun s hs ↦ h.trans_lt hs.1
  · exact Or.inr fun s hs ↦ hs.2.trans_le h

/-- **Type 5 (outward germ)**: above any radius `ρ`, a nonzero rational function is monomial on
some interval `(ρ, ρ')`, `ρ' ≤ ρ₀`. -/
theorem exists_isMonomialOn_above {φ : RatFunc K} (hφ : φ ≠ 0) {ρ ρ₀ : Γ₀} (hρ : ρ < ρ₀) :
    ∃ ρ', ρ < ρ' ∧ ρ' ≤ ρ₀ ∧ IsMonomialOn v {s | ρ < (s : Γ₀) ∧ (s : Γ₀) < ρ'} φ := by
  classical
  let T := insert ρ₀ ((rootValues v φ).filter (ρ < ·))
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.min' hT, ?_, T.min'_le _ (Finset.mem_insert_self _ _), isMonomialOn_Ioo hφ
    fun t ht ↦ ?_⟩
  · rcases Finset.mem_insert.1 (T.min'_mem hT) with h | h
    · rw [h]; exact hρ
    · exact (Finset.mem_filter.1 h).2
  · by_cases hlt : ρ < t
    · exact Or.inr (T.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨ht, hlt⟩)))
    · exact Or.inl (not_lt.1 hlt)

/-- **Type 5 (inward germ)**: below any radius `ρ`, a nonzero rational function is monomial on
some interval `(ρ', ρ)`, `ρ₀ ≤ ρ'`. -/
theorem exists_isMonomialOn_below {φ : RatFunc K} (hφ : φ ≠ 0) {ρ ρ₀ : Γ₀} (hρ : ρ₀ < ρ) :
    ∃ ρ', ρ₀ ≤ ρ' ∧ ρ' < ρ ∧ IsMonomialOn v {s | ρ' < (s : Γ₀) ∧ (s : Γ₀) < ρ} φ := by
  classical
  let T := insert ρ₀ ((rootValues v φ).filter (· < ρ))
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.max' hT, T.le_max' _ (Finset.mem_insert_self _ _), ?_, isMonomialOn_Ioo hφ
    fun t ht ↦ ?_⟩
  · rcases Finset.mem_insert.1 (T.max'_mem hT) with h | h
    · rw [h]; exact hρ
    · exact (Finset.mem_filter.1 h).2
  · by_cases hlt : t < ρ
    · exact Or.inl (T.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨ht, hlt⟩)))
    · exact Or.inr (not_lt.1 hlt)

/-- **Type 3**: if no zero or pole of `φ ≠ 0` has absolute value `ρ` (e.g. `ρ ∉ v(K)`), then `φ`
is monomial on an interval `(ρ₁, ρ₂)` around `ρ`, inside any given `(ρ₀, ρ₀')`. -/
theorem exists_isMonomialOn_around {φ : RatFunc K} (hφ : φ ≠ 0) {ρ ρ₀ ρ₀' : Γ₀}
    (hρ₀ : ρ₀ < ρ) (hρ₀' : ρ < ρ₀') (hρ : ∀ α, (α ∈ φ.num.roots ∨ α ∈ φ.denom.roots) → v α ≠ ρ) :
    ∃ ρ₁ ρ₂, ρ₀ ≤ ρ₁ ∧ ρ₁ < ρ ∧ ρ < ρ₂ ∧ ρ₂ ≤ ρ₀' ∧
      IsMonomialOn v {s | ρ₁ < (s : Γ₀) ∧ (s : Γ₀) < ρ₂} φ := by
  classical
  let T₁ := insert ρ₀ ((rootValues v φ).filter (· < ρ))
  let T₂ := insert ρ₀' ((rootValues v φ).filter (ρ < ·))
  have h₁ : T₁.Nonempty := Finset.insert_nonempty _ _
  have h₂ : T₂.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T₁.max' h₁, T₂.min' h₂, T₁.le_max' _ (Finset.mem_insert_self _ _), ?_, ?_,
    T₂.min'_le _ (Finset.mem_insert_self _ _), isMonomialOn_Ioo hφ fun t ht ↦ ?_⟩
  · rcases Finset.mem_insert.1 (T₁.max'_mem h₁) with h | h
    · rw [h]; exact hρ₀
    · exact (Finset.mem_filter.1 h).2
  · rcases Finset.mem_insert.1 (T₂.min'_mem h₂) with h | h
    · rw [h]; exact hρ₀'
    · exact (Finset.mem_filter.1 h).2
  · have htρ : t ≠ ρ := by
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 ht
      rw [Multiset.mem_toFinset, Multiset.mem_add] at hα
      exact hρ α hα
    rcases lt_or_gt_of_ne htρ with hlt | hlt
    · exact Or.inl (T₁.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨ht, hlt⟩)))
    · exact Or.inr (T₂.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨ht, hlt⟩)))

end Germ

end DiscLimit

end SemistableReduction
