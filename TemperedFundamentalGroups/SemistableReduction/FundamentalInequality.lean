/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The fundamental inequality for one extension of a valuation

Blueprint §9.4, layer A. Let `L / K` be a field extension, `w` a valuation on `L` and `v` a
valuation on `K` extended by `w` (`v.HasExtension w`). We define

* `valueGroup w : Subgroup Γ₁ˣ`, the values `w x` of nonzero `x : L`;
* `ramificationIdx K w`, the (relative) index of the values of `K` in the values of `L`
  (`0` if infinite);
* `inertiaDeg v w`, the degree of the residue field extension (`0` if infinite);

and prove the fundamental inequality `e · f ≤ [L : K]` (`ramificationIdx_mul_inertiaDeg_le`).
The key statement is `linearIndependent_mul`: if `x₁, …, x_f` lie in the valuation ring of `w`
with residues linearly independent over the residue field of `v`, and `π₁, …, π_e` have values
in pairwise distinct classes modulo the values of `K`, then the products `πⱼ xᵢ` are linearly
independent over `K`. It rests on `valuation_sum_eq_sup`: the valuation of
`Σ aᵢ xᵢ` (`aᵢ ∈ K`) is the maximum of the `v(aᵢ)`.
-/

open IsLocalRing Valuation

namespace SemistableReduction

namespace FundamentalInequality

section ValueGroup

variable {L : Type*} [Field L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- The value group of a valuation on a field: the values of the nonzero elements, as a subgroup
of `Γˣ`. -/
def valueGroup (w : Valuation L Γ) : Subgroup Γˣ where
  carrier := {g | ∃ x : L, w x = g}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by simp [hx, hy]⟩
  inv_mem' := by
    rintro _ ⟨x, hx⟩
    exact ⟨x⁻¹, by simp [hx]⟩

lemma mem_valueGroup_iff {w : Valuation L Γ} {g : Γˣ} : g ∈ valueGroup w ↔ ∃ x : L, w x = g :=
  Iff.rfl

lemma valuation_mem_valueGroup (w : Valuation L Γ) {x : L} (hx : x ≠ 0) :
    Units.mk0 (w x) ((Valuation.ne_zero_iff w).2 hx) ∈ valueGroup w :=
  ⟨x, rfl⟩

end ValueGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]

variable (K) in
/-- The ramification index `e(w | K)`: the index of the values of `K` in the values of `L`
(`0` if the index is infinite). -/
noncomputable def ramificationIdx (w : Valuation L Γ₁) : ℕ :=
  (valueGroup (w.comap (algebraMap K L))).relIndex (valueGroup w)

/-- The inertia degree `f(w | v)`: the degree of the residue field extension (`0` if infinite). -/
noncomputable def inertiaDeg (v : Valuation K Γ₀) (w : Valuation L Γ₁) [v.HasExtension w] : ℕ :=
  Module.finrank (ResidueField v.valuationSubring) (ResidueField w.valuationSubring)

lemma valueGroup_comap_le (w : Valuation L Γ₁) :
    valueGroup (w.comap (algebraMap K L)) ≤ valueGroup w := by
  rintro _ ⟨x, hx⟩
  exact ⟨algebraMap K L x, hx⟩

variable {v : Valuation K Γ₀} {w : Valuation L Γ₁} [v.HasExtension w]

local notation "O_v" => v.valuationSubring
local notation "O_w" => w.valuationSubring

/-- An element of the valuation ring has nonzero residue iff it has valuation `1`. -/
lemma residue_ne_zero_iff_valuation_eq_one (x : O_w) :
    residue O_w x ≠ 0 ↔ w x = 1 := by
  rw [residue_ne_zero_iff_isUnit,
    (Valuation.valuationSubring.integers w).isUnit_iff_valuation_eq_one]
  rfl

/-- If `x₁, …, x_n` lie in the valuation ring of `w` with residues linearly independent over
the residue field of `v`, then `w(Σ aᵢ xᵢ) = max_i w(aᵢ)` for all `aᵢ ∈ K`. -/
theorem valuation_sum_eq_sup {ι : Type*} {x : ι → O_w}
    (hx : LinearIndependent (ResidueField O_v) (fun i ↦ residue O_w (x i)))
    (s : Finset ι) (a : ι → K) :
    w (∑ i ∈ s, algebraMap K L (a i) * x i) = s.sup (fun i ↦ w (algebraMap K L (a i))) := by
  classical
  by_cases h0 : ∀ i ∈ s, a i = 0
  · rw [Finset.sum_eq_zero fun i hi ↦ by simp [h0 i hi], map_zero, eq_comm, ← bot_eq_zero,
      Finset.sup_eq_bot_iff]
    intro i hi
    simp [h0 i hi, bot_eq_zero]
  push Not at h0
  obtain ⟨i₀, hi₀s, hi₀⟩ := h0
  obtain ⟨j, hjs, hj⟩ := Finset.exists_max_image s (fun i ↦ w (algebraMap K L (a i))) ⟨i₀, hi₀s⟩
  have hsup : s.sup (fun i ↦ w (algebraMap K L (a i))) = w (algebraMap K L (a j)) :=
    le_antisymm (Finset.sup_le hj) (Finset.le_sup (f := fun i ↦ w (algebraMap K L (a i))) hjs)
  have haj : a j ≠ 0 := by
    intro haj
    have := hj i₀ hi₀s
    rw [haj, map_zero, map_zero, ← bot_eq_zero, le_bot_iff, bot_eq_zero,
      Valuation.zero_iff] at this
    exact hi₀ ((map_eq_zero_iff _ (algebraMap K L).injective).1 this)
  -- the normalized coefficients `bᵢ = aᵢ / aⱼ` are integral
  have hb (i : ι) (hi : i ∈ s) : v (a i / a j) ≤ 1 := by
    rw [← _root_.map_one v, ← HasExtension.val_map_le_iff (vR := v) (vA := w), map_one,
      map_one, map_div₀, map_div₀, div_le_one₀ ((Valuation.pos_iff w).2 ((map_ne_zero _).2 haj))]
    exact hj i hi
  let b : ι → O_v := fun i ↦ if hi : i ∈ s then ⟨a i / a j, hb i hi⟩ else 0
  have hbj : b j = 1 := by
    ext
    simp [b, hjs, haj]
  set y : O_w := ∑ i ∈ s, algebraMap O_v O_w (b i) * x i with hy
  have hsum : ∑ i ∈ s, algebraMap K L (a i) * x i = algebraMap K L (a j) * (y : L) := by
    rw [hy]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [HasExtension.coe_algebraMap_valuationSubring_eq]
    simp only [b, dif_pos hi]
    rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ haj]
  have hyres : residue O_w y ≠ 0 := by
    rw [hy, map_sum]
    intro hzero
    have := (linearIndependent_iff'.1 hx) s (fun i ↦ residue O_v (b i))
      (by
        rw [← hzero]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Algebra.smul_def, map_mul, HasExtension.algebraMap_residue_eq_residue_algebraMap]) j hjs
    rw [hbj, map_one] at this
    exact one_ne_zero this
  rw [hsum, map_mul, hsup, (residue_ne_zero_iff_valuation_eq_one y).1 hyres, mul_one]

/-- Residue-independent elements of the valuation ring are linearly independent over `K`. -/
theorem linearIndependent_of_residue {ι : Type*} {x : ι → O_w}
    (hx : LinearIndependent (ResidueField O_v) (fun i ↦ residue O_w (x i))) :
    LinearIndependent K (fun i ↦ (x i : L)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := valuation_sum_eq_sup hx s g
  simp_rw [← Algebra.smul_def] at h
  rw [hg, map_zero, eq_comm, ← bot_eq_zero, Finset.sup_eq_bot_iff] at h
  have := h i hi
  rwa [bot_eq_zero, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap K L).injective] at this

/-- The value of a combination `Σ aᵢ xᵢ` of residue-independent elements is the value of an
element of `K` (or `0`). -/
lemma exists_valuation_sum_eq {ι : Type*} {x : ι → O_w}
    (hx : LinearIndependent (ResidueField O_v) (fun i ↦ residue O_w (x i)))
    (s : Finset ι) (a : ι → K) :
    ∃ c : K, w (∑ i ∈ s, algebraMap K L (a i) * x i) = w (algebraMap K L c) := by
  classical
  rw [valuation_sum_eq_sup hx]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, by simp [bot_eq_zero]⟩
  obtain ⟨j, hjs, hj⟩ := Finset.exists_max_image s (fun i ↦ w (algebraMap K L (a i))) hs
  exact ⟨a j, le_antisymm (Finset.sup_le hj)
    (Finset.le_sup (f := fun i ↦ w (algebraMap K L (a i))) hjs)⟩

/-- **The fundamental inequality, linear-independence form.** If `x₁, …, x_f` lie in the
valuation ring of `w` with residues linearly independent over the residue field of `v`, and the
values of `π₁, …, π_e ∈ L ∖ 0` lie in pairwise distinct classes modulo the values of `K`, then the
products `πⱼ xᵢ` are linearly independent over `K`. -/
theorem linearIndependent_mul {ι J : Type*} {x : ι → O_w}
    (hx : LinearIndependent (ResidueField O_v) (fun i ↦ residue O_w (x i)))
    {π : J → L} (hπ0 : ∀ j, π j ≠ 0)
    (hπ : ∀ j j' (c : K), c ≠ 0 → w (π j) = w (algebraMap K L c) * w (π j') → j = j') :
    LinearIndependent K (fun p : J × ι ↦ π p.1 * x p.2) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg
  -- enlarge `s` to a product `t ×ˢ u`
  set t := s.image Prod.fst
  set u := s.image Prod.snd
  have hsub : s ⊆ t ×ˢ u := fun p hp ↦
    Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  set g' : J × ι → K := fun p ↦ if p ∈ s then g p else 0
  have hg' : ∑ p ∈ t ×ˢ u, g' p • (π p.1 * x p.2) = 0 := by
    rw [← hg, eq_comm]
    refine Finset.sum_subset_zero_on_sdiff hsub (fun p hp ↦ ?_) (fun p hp ↦ by simp [g', hp])
    simp [g', (Finset.mem_sdiff.1 hp).2]
  -- group the sum by `j`
  set y : J → L := fun j ↦ ∑ i ∈ u, algebraMap K L (g' (j, i)) * x i
  have hsum : ∑ j ∈ t, π j * y j = 0 := by
    rw [← hg', Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def]
    ring
  -- all `y j` vanish: otherwise the term of largest value dominates
  have hy : ∀ j ∈ t, y j = 0 := by
    by_contra! hne
    obtain ⟨j₁, hj₁t, hj₁⟩ := hne
    set t' := t.filter (fun j ↦ y j ≠ 0)
    obtain ⟨j, hjt', hj⟩ := Finset.exists_max_image t' (fun j ↦ w (π j * y j))
      ⟨j₁, Finset.mem_filter.2 ⟨hj₁t, hj₁⟩⟩
    obtain ⟨hjt, hjy⟩ := Finset.mem_filter.1 hjt'
    have hpos : w (π j * y j) ≠ 0 := by
      rw [ne_eq, Valuation.zero_iff]
      exact mul_ne_zero (hπ0 j) hjy
    have hlt : ∀ j' ∈ t.erase j, w (π j' * y j') < w (π j * y j) := by
      intro j' hj'
      obtain ⟨hj'j, hj't⟩ := Finset.mem_erase.1 hj'
      by_cases hy' : y j' = 0
      · rw [hy', mul_zero, map_zero]
        exact (Valuation.pos_iff w).2 (by simpa using hpos)
      refine lt_of_le_of_ne (hj j' (Finset.mem_filter.2 ⟨hj't, hy'⟩)) fun heq ↦ hj'j ?_
      obtain ⟨c, hc⟩ := exists_valuation_sum_eq hx u (fun i ↦ g' (j, i))
      obtain ⟨c', hc'⟩ := exists_valuation_sum_eq hx u (fun i ↦ g' (j', i))
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hjy ((Valuation.zero_iff w).1 (by simpa using hc))
      have hc'0 : c' ≠ 0 := by
        rintro rfl
        exact hy' ((Valuation.zero_iff w).1 (by simpa using hc'))
      refine hπ j' j (c / c') (div_ne_zero hc0 hc'0) ?_
      have hwc' : w (algebraMap K L c') ≠ 0 := by
        rw [ne_eq, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap K L).injective]
        exact hc'0
      have heq' : w (π j') * w (algebraMap K L c') = w (π j) * w (algebraMap K L c) := by
        have hc1 : w (y j) = w (algebraMap K L c) := hc
        have hc2 : w (y j') = w (algebraMap K L c') := hc'
        rw [← hc1, ← hc2, ← map_mul, ← map_mul]
        exact heq
      rw [map_div₀, map_div₀, div_mul_eq_mul_div, eq_div_iff hwc', heq', mul_comm]
    have hsplit := Finset.add_sum_erase t (fun j ↦ π j * y j) hjt
    rw [hsum] at hsplit
    have hrest : w (∑ j' ∈ t.erase j, π j' * y j') < w (π j * y j) :=
      Valuation.map_sum_lt w hpos hlt
    have := Valuation.map_add_eq_of_lt_right w hrest
    rw [add_comm, hsplit, map_zero] at this
    exact hpos this.symm
  -- hence all coefficients vanish
  intro p hp
  have hp' : p ∈ t ×ˢ u := hsub hp
  obtain ⟨hpt, hpu⟩ := Finset.mem_product.1 hp'
  have h1 := valuation_sum_eq_sup hx u (fun i ↦ g' (p.1, i))
  rw [show (∑ i ∈ u, algebraMap K L (g' (p.1, i)) * (x i : L)) = y p.1 from rfl, hy p.1 hpt,
    map_zero, eq_comm, ← bot_eq_zero, Finset.sup_eq_bot_iff] at h1
  have h2 := h1 p.2 hpu
  rw [bot_eq_zero, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap K L).injective] at h2
  simpa [g', hp] using h2

/-- **The fundamental inequality** for one extension of a valuation: `e(w | v) · f(w | v) ≤ [L : K]`
(if `e` or `f` is infinite, the corresponding factor is `0`). -/
theorem ramificationIdx_mul_inertiaDeg_le [FiniteDimensional K L] :
    ramificationIdx K w * inertiaDeg v w ≤ Module.finrank K L := by
  classical
  rcases Nat.eq_zero_or_pos (inertiaDeg v w) with hf | hf
  · simp [hf]
  rcases Nat.eq_zero_or_pos (ramificationIdx K w) with he | he
  · simp [he]
  have : Module.Finite (ResidueField O_v) (ResidueField O_w) := Module.finite_of_finrank_pos hf
  set b := Module.finBasis (ResidueField O_v) (ResidueField O_w)
  choose x hx using fun i ↦ IsLocalRing.residue_surjective (b i)
  have hxli : LinearIndependent (ResidueField O_v) (fun i ↦ residue O_w (x i)) := by
    simpa [hx] using b.linearIndependent
  set H := (valueGroup (w.comap (algebraMap K L))).subgroupOf (valueGroup w)
  have hH : H.index ≠ 0 := he.ne'
  have : H.FiniteIndex := ⟨hH⟩
  let Q := valueGroup w ⧸ H
  have : Fintype Q := Fintype.ofFinite Q
  choose π hπ using fun q : Q ↦ (q.out : valueGroup w).2
  have hπ0 (q : Q) : π q ≠ 0 := by
    intro h
    have := hπ q
    rw [h, map_zero] at this
    exact (Units.ne_zero _) this.symm
  have hli := linearIndependent_mul hxli hπ0 (fun q q' c hc h ↦ by
    rw [hπ, hπ] at h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    have hwc : w (algebraMap K L c) ≠ 0 := by
      rw [ne_eq, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap K L).injective]
      exact hc
    have hmem : Units.mk0 _ hwc ∈ valueGroup (w.comap (algebraMap K L)) := ⟨c, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    convert inv_mem hmem using 1
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    rw [h, mul_inv_rev, mul_comm, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul])
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin] at hcard
  convert hcard using 2
  · rw [ramificationIdx, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  · rfl

section Torsion

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₁] (w : Valuation L Γ₁)

/-- In a vanishing finite sum with a nonzero term, the maximal value is attained twice. -/
lemma exists_ne_valuation_eq_of_sum_eq_zero {ι : Type*} {s : Finset ι} {f : ι → L}
    (hs : ∑ i ∈ s, f i = 0) {i₀ : ι} (hi₀ : i₀ ∈ s) (hf : f i₀ ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ f i ≠ 0 ∧ w (f i) = w (f j) := by
  classical
  obtain ⟨i, his, hi⟩ := Finset.exists_max_image s (fun i ↦ w (f i)) ⟨i₀, hi₀⟩
  have hpos : w (f i) ≠ 0 := by
    intro h
    have := hi i₀ hi₀
    rw [h, ← bot_eq_zero, le_bot_iff, bot_eq_zero, Valuation.zero_iff] at this
    exact hf this
  by_contra! hne
  have hlt : ∀ j ∈ s.erase i, w (f j) < w (f i) := fun j hj ↦
    lt_of_le_of_ne (hi j (Finset.mem_of_mem_erase hj))
      fun h ↦ hne j (Finset.mem_of_mem_erase hj) i his (Finset.ne_of_mem_erase hj)
        (fun h0 ↦ hpos (by rw [← h, h0, map_zero])) h
  have hsplit := Finset.add_sum_erase s f his
  have := Valuation.map_add_eq_of_lt_right w (Valuation.map_sum_lt w hpos hlt)
  rw [add_comm, hsplit, hs, map_zero] at this
  exact hpos this.symm

/-- **Values of algebraic elements are torsion modulo the values of `K`**: if `x ≠ 0` is integral
over `K`, some power `w(x) ^ n`, `n ≥ 1`, is the value of an element of `K`. -/
theorem exists_pow_valuation_eq {x : L} (hx : IsIntegral K x) (hx0 : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : K, c ≠ 0 ∧ w x ^ n = w (algebraMap K L c) := by
  classical
  set P := minpoly K x
  have hP : aeval x P = 0 := minpoly.aeval K x
  rw [aeval_eq_sum_range] at hP
  set d := P.natDegree
  have hd : P.coeff d ≠ 0 := by
    rw [(minpoly.monic hx).coeff_natDegree]
    exact one_ne_zero
  have hwx : w x ≠ 0 := (Valuation.ne_zero_iff w).2 hx0
  obtain ⟨i, hi, j, hj, hij, hi0, heq⟩ := exists_ne_valuation_eq_of_sum_eq_zero w hP
    (Finset.self_mem_range_succ d) (by
      rw [Algebra.smul_def]
      exact mul_ne_zero ((_root_.map_ne_zero _).2 hd) (pow_ne_zero _ hx0))
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_pow, map_pow] at heq
  have hci : P.coeff i ≠ 0 := by
    intro h
    rw [Algebra.smul_def, h, map_zero, zero_mul] at hi0
    exact hi0 rfl
  have hcj : P.coeff j ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero, zero_mul, mul_eq_zero, Valuation.zero_iff,
      map_eq_zero_iff _ (algebraMap K L).injective] at heq
    exact heq.elim hci (fun h ↦ pow_ne_zero _ hwx h)
  have hwi : w (algebraMap K L (P.coeff i)) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap K L).injective]; exact hci
  have hwj : w (algebraMap K L (P.coeff j)) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap K L).injective]; exact hcj
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, P.coeff i / P.coeff j, div_ne_zero hci hcj, ?_⟩
    rw [← pow_sub_mul_pow (w x) hlt.le] at heq
    have h := mul_right_cancel₀ (pow_ne_zero i hwx) (heq.trans (mul_assoc _ _ _).symm)
    rw [map_div₀, map_div₀, eq_div_iff hwj, h, mul_comm]
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, P.coeff j / P.coeff i, div_ne_zero hcj hci, ?_⟩
    rw [← pow_sub_mul_pow (w x) hlt.le] at heq
    have h := mul_right_cancel₀ (pow_ne_zero j hwx) (heq.symm.trans (mul_assoc _ _ _).symm)
    rw [map_div₀, map_div₀, eq_div_iff hwi, h, mul_comm]

/-- **Divisible value group**: if the values of `K` form a divisible group and `L / K` is
algebraic, then `L` has the same values as `K`, i.e. `e(w | K) = 1`. -/
theorem ramificationIdx_eq_one_of_divisible [Algebra.IsAlgebraic K L]
    (hdiv : ∀ (c : K) (n : ℕ), 0 < n → ∃ d : K, w (algebraMap K L d) ^ n = w (algebraMap K L c)) :
    ramificationIdx K w = 1 := by
  refine Subgroup.relIndex_eq_one.2 ?_
  rintro g ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact g.ne_zero hx.symm
  obtain ⟨n, hn, c, -, hc⟩ :=
    exists_pow_valuation_eq w (Algebra.IsIntegral.isIntegral (R := K) x) hx0
  obtain ⟨d, hd⟩ := hdiv c n hn
  refine ⟨d, ?_⟩
  rw [comap_apply, ← hx]
  exact (pow_left_inj hn.ne').1 (hd.trans hc.symm)

/-- `ramificationIdx_eq_one_of_divisible`, with the divisibility hypothesis on a valuation `v` of
`K` extended by `w`. -/
theorem ramificationIdx_eq_one_of_divisible' {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} [v.HasExtension w] [Algebra.IsAlgebraic K L]
    (hdiv : ∀ (c : K) (n : ℕ), 0 < n → ∃ d : K, v d ^ n = v c) :
    ramificationIdx K w = 1 := by
  refine ramificationIdx_eq_one_of_divisible w fun c n hn ↦ ?_
  obtain ⟨d, hd⟩ := hdiv c n hn
  refine ⟨d, ?_⟩
  rw [← map_pow, ← map_pow, HasExtension.val_map_eq_iff (vR := v), map_pow, hd]

end Torsion

end FundamentalInequality

end SemistableReduction
