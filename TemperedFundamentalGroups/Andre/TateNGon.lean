/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateFourGon

/-!
# The `2N`-gon model of `E_{q^N}` over the `2`-gon model of `E_q`: its special fibre

Let `N ≥ 3`. The model of the level `K(E_{q^N})` lives in `ℙ^{2N}_O` with coordinates
`[B_0 : … : B_{N-1} : W]`, `B_k = (X_{2k}, X_{2k+1})` (the point `P_{q^N}(q^k u)` of `E_{q^N}` in
plain coordinates, `W = π`; TFGD-plan, "Run 6"). This file is generic: `O` is any commutative
ring and `P` a prime ideal of `O[X_0, …, X_{2N}]` (a point of the special fibre in the
application) containing the **reductions** of the model equations (`NGon.Red`):

* for `0 < d < N/2` ("A-type", translation by `dT`, `T` of order `N`): `(x_k + y_k) x_{k+d}`,
  `x_k y_{k+d}`, `y_k y_{k+d}`;
* for `2d = N` ("B-type", `dT` of order `2`): `x_k x_{k+d}`, `x_k y_{k+d} + y_k x_{k+d}`,
  `y_k y_{k+d}`;
* the cyclic quadrics `Γ_1 = Σ_k x_k x_{k+1} − γ W²` (`γ` a unit) and
  `Γ_d = Σ_k x_k x_{k+d}` for `2 ≤ d < N/2`.

Main results:

* `NGon.mem_pieces` (**source/sink argument**): `P` lies on a line
  `L_i = {W = 0, B_k = 0 for k ≠ i}` or on a conic
  `G_i = {B_k = 0 for k ∉ {i−1, i}, B_{i−1} = (a, −a), B_i = (b, 0)}`;
* `NGon.memA_memA`: the pieces `A_i = L_i ∪ G_i` meet only in the nodes
  `c_i = A_i ∩ A_{i+1} = {W = 0, B_k = 0 for k ≠ i, B_i = (1, −1)}`;
* `NGon.decomp`: the `TateCovering.Decomp` with `C = A_0`, `E = A_1 ∪ … ∪ A_{N−1}`,
  `Cp = c_{N−1}`, `Cq = c_0` of every space mapping continuously to such points of `ℙ^{2N}_O`
  (its `toCode` is the universal `ℤ`-chain of the `2N`-gon).
-/

universe u

open MvPolynomial

namespace TemperedFundamentalGroups

namespace NGon

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] {N : ℕ} [NeZero N]

/-! ### Coordinates -/

/-- The coordinate `x_k = X_{2k}`. -/
def ix (k : ZMod N) : Fin (2 * N + 1) := ⟨2 * k.val, by have := ZMod.val_lt k; omega⟩

/-- The coordinate `y_k = X_{2k+1}`. -/
def iy (k : ZMod N) : Fin (2 * N + 1) := ⟨2 * k.val + 1, by have := ZMod.val_lt k; omega⟩

variable (N) in
/-- The coordinate `W = X_{2N}`. -/
def iw : Fin (2 * N + 1) := ⟨2 * N, by omega⟩

lemma ix_injective : Function.Injective (ix (N := N)) := fun a b h => by
  have := congrArg Fin.val h
  simp only [ix] at this
  exact ZMod.val_injective N (by omega)

lemma iy_injective : Function.Injective (iy (N := N)) := fun a b h => by
  have := congrArg Fin.val h
  simp only [iy] at this
  exact ZMod.val_injective N (by omega)

lemma ix_ne_iy (a b : ZMod N) : ix a ≠ iy b := fun h => by
  have := congrArg Fin.val h
  simp only [ix, iy] at this
  omega

lemma ix_ne_iw (a : ZMod N) : ix a ≠ iw N := fun h => by
  have := congrArg Fin.val h
  have := ZMod.val_lt a
  simp only [ix, iw] at *
  omega

lemma iy_ne_iw (a : ZMod N) : iy a ≠ iw N := fun h => by
  have := congrArg Fin.val h
  have := ZMod.val_lt a
  simp only [iy, iw] at *
  omega

/-- Every coordinate is some `x_k`, some `y_k` or `W`. -/
lemma idx_cases (j : Fin (2 * N + 1)) : (∃ k, j = ix k) ∨ (∃ k, j = iy k) ∨ j = iw N := by
  by_cases hw : j.val = 2 * N
  · exact Or.inr (Or.inr (Fin.ext hw))
  · have hj := j.isLt
    have hlt : j.val / 2 < N := by omega
    have hv : ((j.val / 2 : ℕ) : ZMod N).val = j.val / 2 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    rcases Nat.mod_two_eq_zero_or_one j.val with h | h
    · exact Or.inl ⟨(j.val / 2 : ℕ), Fin.ext (by simp only [ix, hv]; omega)⟩
    · exact Or.inr (Or.inl ⟨(j.val / 2 : ℕ), Fin.ext (by simp only [iy, hv]; omega)⟩)

set_option hygiene false in
local notation "RN" => MvPolynomial (Fin (2 * N + 1)) O

/-- `x_k`. -/
abbrev xx (k : ZMod N) : RN := X (ix k)

/-- `y_k`. -/
abbrev yy (k : ZMod N) : RN := X (iy k)

variable (O N) in
/-- `W`. -/
abbrev ww : RN := X (iw N)

/-! ### The reduced equations -/

/-- **The reductions of the model equations** hold at `P` (see the module docstring). -/
structure Red (γ : O) (P : Ideal RN) : Prop where
  pairA : ∀ k d : ZMod N, 0 < d.val → 2 * d.val < N →
    (xx k + yy k) * xx (k + d) ∈ P ∧ xx k * yy (k + d) ∈ P ∧ yy k * yy (k + d) ∈ P
  pairB : ∀ k d : ZMod N, 2 * d.val = N →
    xx k * xx (k + d) ∈ P ∧ xx k * yy (k + d) + yy k * xx (k + d) ∈ P ∧ yy k * yy (k + d) ∈ P
  gam1 : ∑ k : ZMod N, xx k * xx (k + 1) - C γ * ww O N ^ 2 ∈ P
  gamD : ∀ d : ZMod N, 2 ≤ d.val → 2 * d.val < N → ∑ k : ZMod N, xx k * xx (k + d) ∈ P

/-! ### Blocks and pieces -/

/-- The block `B_k` vanishes. -/
def Z0 (k : ZMod N) (P : Ideal RN) : Prop := xx k ∈ P ∧ yy k ∈ P

/-- `B_k = (a, −a)`, `a ≠ 0`. -/
def FA (k : ZMod N) (P : Ideal RN) : Prop := xx k ∉ P ∧ xx k + yy k ∈ P

/-- `B_k = (b, 0)`, `b ≠ 0`. -/
def FB (k : ZMod N) (P : Ideal RN) : Prop := xx k ∉ P ∧ yy k ∈ P

/-- The line `L_i = {W = 0, B_k = 0 for k ≠ i}`. -/
def L (i : ZMod N) (P : Ideal RN) : Prop := ww O N ∈ P ∧ ∀ k, k ≠ i → Z0 k P

/-- The conic `G_i = {B_k = 0 for k ∉ {i−1, i}, B_{i−1} = (a, −a), B_i = (b, 0)}`. -/
def G (i : ZMod N) (P : Ideal RN) : Prop :=
  (∀ k, k ≠ i - 1 → k ≠ i → Z0 k P) ∧ xx (i - 1) + yy (i - 1) ∈ P ∧ yy i ∈ P

/-- The piece `A_i = L_i ∪ G_i`. -/
def A (i : ZMod N) (P : Ideal RN) : Prop := L i P ∨ G i P

/-- The node `c_i = A_i ∩ A_{i+1} = {W = 0, B_k = 0 for k ≠ i, B_i = (1, −1)}`. -/
def Nd (i : ZMod N) (P : Ideal RN) : Prop := ww O N ∈ P ∧ (∀ k, k ≠ i → Z0 k P) ∧ xx i + yy i ∈ P

section Points

variable {P : Ideal RN} [hP : P.IsPrime]

omit hP [NeZero N] in
lemma sub_mem_left {a b : RN} (h : a + b ∈ P) (hb : b ∈ P) : a ∈ P := by
  have := P.sub_mem h hb
  rwa [add_sub_cancel_right] at this

omit hP [NeZero N] in
lemma sub_mem_right {a b : RN} (h : a + b ∈ P) (ha : a ∈ P) : b ∈ P := by
  have := P.sub_mem h ha
  rwa [add_sub_cancel_left] at this

omit [NeZero N] in
/-- The A-type relations orient a pair of non-zero blocks. -/
lemma forms_of_A {x y x' y' : RN} (h1 : (x + y) * x' ∈ P) (h2 : x * y' ∈ P) (h3 : y * y' ∈ P)
    (hk : ¬ (x ∈ P ∧ y ∈ P)) (hk' : ¬ (x' ∈ P ∧ y' ∈ P)) :
    (x ∉ P ∧ x + y ∈ P) ∧ (x' ∉ P ∧ y' ∈ P) := by
  have hy' : y' ∈ P := by
    by_contra hy'
    exact hk ⟨(hP.mem_or_mem h2).resolve_right hy', (hP.mem_or_mem h3).resolve_right hy'⟩
  have hx' : x' ∉ P := fun h => hk' ⟨h, hy'⟩
  have hxy : x + y ∈ P := (hP.mem_or_mem h1).resolve_right hx'
  exact ⟨⟨fun hx => hk ⟨hx, sub_mem_right hxy hx⟩, hxy⟩, hx', hy'⟩

omit [NeZero N] in
/-- The B-type relations exclude a pair of non-zero blocks. -/
lemma false_of_B {x y x' y' : RN} (h1 : x * x' ∈ P) (h2 : x * y' + y * x' ∈ P)
    (h3 : y * y' ∈ P) (hk : ¬ (x ∈ P ∧ y ∈ P)) (hk' : ¬ (x' ∈ P ∧ y' ∈ P)) : False := by
  by_cases hx : x ∈ P
  · have hy : y ∉ P := fun hy => hk ⟨hx, hy⟩
    have hy' : y' ∈ P := (hP.mem_or_mem h3).resolve_left hy
    have : y * x' ∈ P := sub_mem_right h2 (P.mul_mem_right _ hx)
    exact hk' ⟨(hP.mem_or_mem this).resolve_left hy, hy'⟩
  · have hx' : x' ∈ P := (hP.mem_or_mem h1).resolve_left hx
    have hy' : y' ∉ P := fun hy' => hk' ⟨hx', hy'⟩
    have hy : y ∈ P := (hP.mem_or_mem h3).resolve_right hy'
    have : x * y' ∈ P := sub_mem_left h2 (P.mul_mem_right _ hy)
    exact ((hP.mem_or_mem this).resolve_left hx) |> hy'

omit hP in
lemma not_FA_FB {k : ZMod N} (ha : FA k P) (hb : FB k P) : False :=
  ha.1 (sub_mem_left ha.2 hb.2)

omit hP in
lemma FA_not_Z0 {k : ZMod N} (h : FA k P) : ¬ Z0 k P := fun h' => h.1 h'.1

omit hP in
lemma FB_not_Z0 {k : ZMod N} (h : FB k P) : ¬ Z0 k P := fun h' => h.1 h'.1

lemma val_neg_lt {d : ZMod N} (hd : d ≠ 0) (h : N < 2 * d.val) :
    2 * (-d).val < N ∧ 0 < (-d).val := by
  haveI : NeZero d := ⟨hd⟩
  rw [ZMod.val_neg_of_ne_zero]
  have := ZMod.val_lt d
  omega

omit [NeZero N] in
lemma val_pos_of_ne {d : ZMod N} (hd : d ≠ 0) : 0 < d.val := by
  rcases Nat.eq_zero_or_pos d.val with h | h
  · exact absurd ((ZMod.val_eq_zero d).1 h) hd
  · exact h

/-- **Two non-zero blocks**: one is `(a, −a)`, the other `(b, 0)`, at an A-type distance. -/
lemma pair_forms {γ : O} (hR : Red γ P) {i j : ZMod N} (hij : i ≠ j) (hi : ¬ Z0 i P)
    (hj : ¬ Z0 j P) :
    (FA i P ∧ FB j P ∧ ∃ d : ZMod N, j = i + d ∧ 0 < d.val ∧ 2 * d.val < N) ∨
      (FA j P ∧ FB i P ∧ ∃ d : ZMod N, i = j + d ∧ 0 < d.val ∧ 2 * d.val < N) := by
  have hd : j - i ≠ 0 := sub_ne_zero.2 hij.symm
  rcases lt_trichotomy (2 * (j - i).val) N with h | h | h
  · have hji : i + (j - i) = j := add_sub_cancel i j
    obtain ⟨h1, h2, h3⟩ := hR.pairA i (j - i) (val_pos_of_ne hd) h
    rw [hji] at h1 h2 h3
    obtain ⟨ha, hb⟩ := forms_of_A h1 h2 h3 hi hj
    exact Or.inl ⟨ha, hb, j - i, hji.symm, val_pos_of_ne hd, h⟩
  · have hji : i + (j - i) = j := add_sub_cancel i j
    obtain ⟨h1, h2, h3⟩ := hR.pairB i (j - i) h
    rw [hji] at h1 h2 h3
    exact (false_of_B h1 h2 h3 hi hj).elim
  · obtain ⟨h', hpos⟩ := val_neg_lt hd h
    have hij' : j + -(j - i) = i := by ring
    obtain ⟨h1, h2, h3⟩ := hR.pairA j (-(j - i)) hpos h'
    rw [hij'] at h1 h2 h3
    obtain ⟨ha, hb⟩ := forms_of_A h1 h2 h3 hj hi
    exact Or.inr ⟨ha, hb, -(j - i), hij'.symm, hpos, h'⟩

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- **No three non-zero blocks** (every vertex is a source or a sink, never both). -/
lemma three_false {γ : O} (hR : Red γ P) {i j l : ZMod N} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (hi : ¬ Z0 i P) (hj : ¬ Z0 j P) (hl : ¬ Z0 l P) : False := by
  have e1 := pair_forms hR hij hi hj
  have e2 := pair_forms hR hil hi hl
  have e3 := pair_forms hR hjl hj hl
  rcases e1 with ⟨a1, b1, -⟩ | ⟨a1, b1, -⟩ <;> rcases e2 with ⟨a2, b2, -⟩ | ⟨a2, b2, -⟩ <;>
    rcases e3 with ⟨a3, b3, -⟩ | ⟨a3, b3, -⟩
  all_goals first
    | exact not_FA_FB a1 b1 | exact not_FA_FB a1 b2 | exact not_FA_FB a1 b3
    | exact not_FA_FB a2 b1 | exact not_FA_FB a2 b2 | exact not_FA_FB a2 b3
    | exact not_FA_FB a3 b1 | exact not_FA_FB a3 b2 | exact not_FA_FB a3 b3

omit hP in
lemma all_false (hX : ∃ j, (X j : RN) ∉ P) (hZ : ∀ k, Z0 k P) (hw : ww O N ∈ P) : False := by
  obtain ⟨j, hj⟩ := hX
  rcases idx_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩ | rfl
  exacts [hj (hZ k).1, hj (hZ k).2, hj hw]

omit hP in
/-- A sum `Σ_k f k` is congruent to its `i`-th term when all others lie in `P`. -/
lemma sum_sub_mem {f : ZMod N → RN} (i : ZMod N) (h : ∀ k, k ≠ i → f k ∈ P) :
    ∑ k, f k - f i ∈ P := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
  exact P.sum_mem fun k hk => h k (Finset.ne_of_mem_erase hk)

lemma two_d_ne_zero {d : ZMod N} (hpos : 0 < d.val) (h : 2 * d.val < N) : d + d ≠ 0 := by
  intro h0
  have : ((2 * d.val : ℕ) : ZMod N) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_ofNat, two_mul, h0]
  rw [ZMod.natCast_eq_zero_iff] at this
  exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

omit hP in
/-- With exactly two non-zero blocks `B_i`, `B_{i+d}`, `Σ_k x_k x_{k+d} ≡ x_i x_{i+d}`. -/
lemma gam_sum_sub_mem {i d : ZMod N} (hpos : 0 < d.val) (h : 2 * d.val < N)
    (hZ : ∀ k, k ≠ i → k ≠ i + d → Z0 k P) :
    ∑ k, xx k * xx (k + d) - xx i * xx (i + d) ∈ P := by
  refine sum_sub_mem (f := fun k => xx k * xx (k + d)) i fun k hk => ?_
  by_cases hk' : k = i + d
  · subst hk'
    refine P.mul_mem_left _ (hZ _ ?_ ?_).1
    · intro e
      exact two_d_ne_zero hpos h (by
        have : i + d + d - i = 0 := by rw [e]; ring
        rw [← this]; ring)
    · intro e
      have : d = 0 := by
        have := congrArg (· - (i + d)) e
        simpa using this
      exact absurd ((ZMod.val_eq_zero d).2 this) (by omega)
  · exact P.mul_mem_right _ (hZ k hk hk').1

omit [NeZero N] in
lemma ne_add_one (hN : 3 ≤ N) (k : ZMod N) : k ≠ k + 1 := fun e => by
  haveI : Fact (1 < N) := ⟨by omega⟩
  exact one_ne_zero (by linear_combination -e : (1 : ZMod N) = 0)

/-- **Every point lies on one of the pieces `L_i`, `G_i`** (`N ≥ 3`, `γ` a unit). -/
theorem mem_pieces {γ : O} (hR : Red γ P) (hγ : IsUnit γ) (hN : 3 ≤ N)
    (hX : ∃ j, (X j : RN) ∉ P) : ∃ i, L i P ∨ G i P := by
  by_cases hS : ∃ i j, i ≠ j ∧ ¬ Z0 i P ∧ ¬ Z0 j P
  · obtain ⟨i, j, hij, hi, hj⟩ := hS
    -- reduce to an oriented pair `a → a + d`
    have key : ∀ a b : ZMod N, a ≠ b → ¬ Z0 a P → ¬ Z0 b P → FA a P → FB b P →
        ∀ d : ZMod N, b = a + d → 0 < d.val → 2 * d.val < N → ∃ i, L i P ∨ G i P := by
      intro a b hab ha hb hfa hfb d hd hpos hlt
      have hZ : ∀ k, k ≠ a → k ≠ b → Z0 k P := fun k hka hkb => by
        by_contra hk
        exact three_false hR hab (Ne.symm hka) (Ne.symm hkb) ha hb hk
      by_cases h1 : d.val = 1
      · have hd1 : d = 1 := by
          haveI : Fact (1 < N) := ⟨by omega⟩
          exact ZMod.val_injective N (h1.trans (ZMod.val_one N).symm)
        refine ⟨b, Or.inr ⟨fun k hk1 hk2 => hZ k ?_ hk2, ?_, hfb.2⟩⟩
        · rwa [hd, hd1, add_sub_cancel_right] at hk1
        · rw [hd, hd1, add_sub_cancel_right]
          exact hfa.2
      · exfalso
        have hsum := (hR.gamD d (by omega) hlt)
        have := gam_sum_sub_mem (P := P) hpos hlt (i := a) fun k hka hkb =>
          hZ k hka (hd ▸ hkb)
        have hprod : xx a * xx (a + d) ∈ P := by
          have := P.sub_mem hsum this
          rwa [sub_sub_cancel] at this
        rw [← hd] at hprod
        rcases hP.mem_or_mem hprod with h | h
        exacts [hfa.1 h, hfb.1 h]
    rcases pair_forms hR hij hi hj with ⟨ha, hb, d, hd, hpos, hlt⟩ | ⟨ha, hb, d, hd, hpos, hlt⟩
    · exact key i j hij hi hj ha hb d hd hpos hlt
    · exact key j i (Ne.symm hij) hj hi ha hb d hd hpos hlt
  · push Not at hS
    by_cases hw : ww O N ∈ P
    · by_cases h0 : ∀ k, Z0 k P
      · exact (all_false hX h0 hw).elim
      · push Not at h0
        obtain ⟨i, hi⟩ := h0
        exact ⟨i, Or.inl ⟨hw, fun k hk => by
          by_contra hk'
          exact hk' (hS i k (Ne.symm hk) hi)⟩⟩
    · exfalso
      have hne : ∀ k : ZMod N, k ≠ k + 1 := ne_add_one hN
      have hsum : ∑ k : ZMod N, xx k * xx (k + 1) ∈ P := P.sum_mem fun k _ => by
        by_cases hk : Z0 k P
        · exact P.mul_mem_right _ hk.1
        · have := hS k (k + 1) (hne k) hk
          exact P.mul_mem_left _ this.1
      have h2 : C γ * ww O N ^ 2 ∈ P := by
        have := P.sub_mem hsum hR.gam1
        rwa [sub_sub_cancel] at this
      rcases hP.mem_or_mem h2 with h | h
      · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hγ.map C))
      · exact hw (hP.mem_of_pow_mem 2 h)

/-! ### The pieces `A_i` and their intersections -/

omit hP in
lemma Nd_A (hN : 3 ≤ N) {i : ZMod N} (h : Nd i P) : A i P ∧ A (i + 1) P := by
  refine ⟨Or.inl ⟨h.1, h.2.1⟩, Or.inr ⟨fun k hk1 _ => h.2.1 k ?_, ?_, ?_⟩⟩
  · rwa [add_sub_cancel_right] at hk1
  · rw [add_sub_cancel_right]
    exact h.2.2
  · exact (h.2.1 (i + 1) (ne_add_one hN i).symm).2

/-- **Two different pieces meet only in a node.** -/
theorem memA_memA {γ : O} (hR : Red γ P) (hγ : IsUnit γ)
    (hX : ∃ j, (X j : RN) ∉ P) {i j : ZMod N} (hij : i ≠ j) (hi : A i P) (hj : A j P) :
    (j = i + 1 ∧ Nd i P) ∨ (i = j + 1 ∧ Nd j P) := by
  -- all blocks vanish and `W ∈ P` is impossible; all blocks vanish forces `W ∈ P`
  have allZ : (∀ k, Z0 k P) → False := fun hZ => by
    refine all_false hX hZ ?_
    have hsum : ∑ k : ZMod N, xx k * xx (k + 1) ∈ P :=
      P.sum_mem fun k _ => P.mul_mem_right _ (hZ k).1
    have h2 : C γ * ww O N ^ 2 ∈ P := by
      have := P.sub_mem hsum hR.gam1
      rwa [sub_sub_cancel] at this
    rcases hP.mem_or_mem h2 with h | h
    · exact (hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hγ.map C))).elim
    · exact hP.mem_of_pow_mem 2 h
  -- `L_a ∩ G_b`, `a ≠ b`
  have LG : ∀ a b : ZMod N, a ≠ b → L a P → G b P → b = a + 1 ∧ Nd a P := fun a b hab hL hG => by
    by_cases hb1 : a = b - 1
    · refine ⟨by rw [hb1]; ring, hL.1, hL.2, ?_⟩
      rw [hb1]
      exact hG.2.1
    · exfalso
      exact allZ fun k => by
        by_cases hk : k = a
        · subst hk
          exact hG.1 k hb1 hab
        · exact hL.2 k hk
  rcases hi with hLi | hGi <;> rcases hj with hLj | hGj
  · exfalso
    exact all_false hX (fun k => by
      by_cases hk : k = i
      · subst hk
        exact hLj.2 k hij
      · exact hLi.2 k hk) hLi.1
  · exact Or.inl (LG i j hij hLi hGj)
  · exact Or.inr (LG j i (Ne.symm hij) hLj hGi)
  · exfalso
    refine allZ fun k => ?_
    by_cases hk1 : k = i - 1
    · by_cases hk2 : k = j - 1
      · exact absurd (by rw [hk1] at hk2; simpa using hk2) hij
      · by_cases hk3 : k = j
        · -- `B_{i−1} = (a, −a)` and `B_j = (b, 0)` with `j = i − 1`
          subst hk3
          have hx : xx k ∈ P := by
            have := hGi.2.1
            rw [← hk1] at this
            exact sub_mem_left this hGj.2.2
          exact ⟨hx, hGj.2.2⟩
        · exact hGj.1 k hk2 hk3
    · by_cases hk2 : k = i
      · subst hk2
        by_cases hk3 : k = j - 1
        · have hy := hGi.2.2
          have hxy := hGj.2.1
          rw [← hk3] at hxy
          exact ⟨sub_mem_left hxy hy, hy⟩
        · by_cases hk4 : k = j
          · exact absurd hk4 hij
          · exact hGj.1 k hk3 hk4
      · exact hGi.1 k hk1 hk2

omit hP in
lemma Nd_disjoint (hX : ∃ j, (X j : RN) ∉ P) {i j : ZMod N} (hij : i ≠ j) (hi : Nd i P)
    (hj : Nd j P) : False :=
  all_false hX (fun k => by
    by_cases hk : k = i
    · subst hk
      exact hj.2.1 k hij
    · exact hi.2.1 k hk) hi.1

end Points

/-! ### The decomposition of a space of such points -/

section Space

variable {Z : Type*} [TopologicalSpace Z] {ι : Z → projSpace O (2 * N)}

/-- The prime of `O[X_0, …, X_{2N}]` of a point. -/
abbrev pt (ι : Z → projSpace O (2 * N)) (z : Z) : Ideal RN := (ι z).asHomogeneousIdeal.toIdeal

instance (z : Z) : (pt ι z).IsPrime := (ι z).isPrime

omit [NeZero N] in
lemma isClosed_mem (hι : Continuous ι) (g : RN) : IsClosed {z : Z | g ∈ pt ι z} :=
  FourGon.isClosed_setOf_mem (ι := ι) hι g

lemma isClosed_Z0 (hι : Continuous ι) (k : ZMod N) : IsClosed {z : Z | Z0 k (pt ι z)} :=
  (isClosed_mem hι _).inter (isClosed_mem hι _)

lemma isClosed_allZ0 (hι : Continuous ι) (p : ZMod N → Prop) :
    IsClosed {z : Z | ∀ k, p k → Z0 k (pt ι z)} := by
  have : {z : Z | ∀ k, p k → Z0 k (pt ι z)} = ⋂ k, ⋂ (_ : p k), {z | Z0 k (pt ι z)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  exact isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_Z0 hι k

lemma isClosed_L (hι : Continuous ι) (i : ZMod N) : IsClosed {z : Z | L i (pt ι z)} :=
  (isClosed_mem hι _).inter (isClosed_allZ0 hι (· ≠ i))

lemma isClosed_G (hι : Continuous ι) (i : ZMod N) : IsClosed {z : Z | G i (pt ι z)} := by
  have h := isClosed_allZ0 hι (fun k => k ≠ i - 1 ∧ k ≠ i)
  have e : {z : Z | ∀ k, (k ≠ i - 1 ∧ k ≠ i) → Z0 k (pt ι z)} =
      {z : Z | ∀ k, k ≠ i - 1 → k ≠ i → Z0 k (pt ι z)} := by
    ext z
    simp only [Set.mem_setOf_eq, and_imp]
  rw [e] at h
  exact h.inter ((isClosed_mem hι _).inter (isClosed_mem hι _))

lemma isClosed_A (hι : Continuous ι) (i : ZMod N) : IsClosed {z : Z | A i (pt ι z)} :=
  (isClosed_L hι i).union (isClosed_G hι i)

lemma isClosed_Nd (hι : Continuous ι) (i : ZMod N) : IsClosed {z : Z | Nd i (pt ι z)} :=
  (isClosed_mem hι _).inter ((isClosed_allZ0 hι (· ≠ i)).inter (isClosed_mem hι _))

lemma isClosed_E (hι : Continuous ι) : IsClosed {z : Z | ∃ i, i ≠ 0 ∧ A i (pt ι z)} := by
  have : {z : Z | ∃ i, i ≠ 0 ∧ A i (pt ι z)} =
      ⋃ i, ⋃ (_ : i ≠ (0 : ZMod N)), {z | A i (pt ι z)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => by
    by_cases hi : i = 0
    · simp only [hi, ne_eq, not_true_eq_false, Set.iUnion_of_empty, isClosed_empty]
    · simp only [hi, ne_eq, not_false_eq_true, Set.iUnion_true]
      exact isClosed_A hι i

variable (N γ ι) in
/-- **The special fibre of the `2N`-gon model as `A_0` and `A_1 ∪ … ∪ A_{N−1}`**, meeting in
the nodes `Cp = c_{N−1}`, `Cq = c_0`. -/
def decomp (hι : Continuous ι) (hR : ∀ z, Red γ (pt ι z)) (hγ : IsUnit γ) (hN : 3 ≤ N)
    (hX : ∀ z, ∃ j, (X j : RN) ∉ pt ι z) : TateCovering.Decomp Z where
  C := {z | A 0 (pt ι z)}
  E := {z | ∃ i, i ≠ 0 ∧ A i (pt ι z)}
  Cp := {z | Nd (-1) (pt ι z)}
  Cq := {z | Nd 0 (pt ι z)}
  isClosed_C := isClosed_A hι 0
  isClosed_E := isClosed_E hι
  isClosed_Cp := isClosed_Nd hι _
  isClosed_Cq := isClosed_Nd hι _
  union := Set.eq_univ_of_forall fun z => by
    obtain ⟨i, hi⟩ := mem_pieces (hR z) hγ hN (hX z)
    by_cases h0 : i = 0
    · subst h0
      exact Or.inl hi
    · exact Or.inr ⟨i, h0, hi⟩
  inter := by
    haveI : Fact (1 < N) := ⟨by omega⟩
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨h0, i, hi0, hi⟩
      rcases memA_memA (hR z) hγ (hX z) (Ne.symm hi0) h0 hi with ⟨e, h⟩ | ⟨e, h⟩
      · exact Or.inr h
      · have : i = -1 := by rw [eq_neg_iff_add_eq_zero, ← e]
        rw [this] at h
        exact Or.inl h
    · rintro (h | h)
      · have := Nd_A hN h
        rw [neg_add_cancel] at this
        exact ⟨this.2, -1, neg_ne_zero.2 one_ne_zero, this.1⟩
      · have := Nd_A hN h
        rw [zero_add] at this
        exact ⟨this.1, 1, one_ne_zero, this.2⟩
  disjoint := by
    haveI : Fact (1 < N) := ⟨by omega⟩
    rw [Set.disjoint_left]
    exact fun z h₁ h₂ => Nd_disjoint (hX z) (neg_ne_zero.2 one_ne_zero) h₁ h₂

end Space

end

end NGon

end TemperedFundamentalGroups
