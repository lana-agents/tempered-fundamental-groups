/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ProjModel
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization

/-!
# Normalizations of projective Zariski models are projective (Blueprint §9.6, M9c)

Degree shifting between the charts of a projective model and explicit homogeneous coordinates
for the normalization of a projective model in a finite extension.
-/

open Polynomial

namespace SemistableReduction

/-! ### Shifting degrees between the charts of a projective model -/

section Shift

variable {L : Type*} [Field L]

/-- If `x` is integral over `A` (monic `p`, `p(x) = 0`), `r ∈ B` and all `p_i r ∈ B`, then `r x`
is integral over `B`. -/
lemma isIntegral_mul_of_coeff {A B : Subring L} {x r : L} {p : A[X]} (hpm : p.Monic)
    (hp : eval₂ (algebraMap A L) x p = 0) (hr : r ∈ B) (hc : ∀ i, (p.coeff i : L) * r ∈ B) :
    IsIntegral B (r * x) := by
  set n := p.natDegree
  set P := p.map (algebraMap A L)
  have hPm : P.Monic := hpm.map _
  have hPn : P.natDegree = n := hpm.natDegree_map _
  have hlift : scaleRoots P r ∈ lifts (algebraMap B L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots, hPn]
    rcases lt_trichotomy i n with hi | rfl | hi
    · obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
      rw [hk, pow_succ', ← mul_assoc, coeff_map]
      exact ⟨⟨_, B.mul_mem (hc i) (B.pow_mem hr k)⟩, rfl⟩
    · rw [Nat.sub_self, pow_zero, mul_one, ← hPn, hPm.coeff_natDegree]
      exact ⟨1, map_one _⟩
    · rw [coeff_eq_zero_of_natDegree_lt (hPn.symm ▸ hi), zero_mul]
      exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff r).2 hPm)
  refine ⟨q, hqm, ?_⟩
  rw [← eval_map, hq, eval, ← RingHom.id_apply r]
  refine scaleRoots_eval₂_eq_zero (RingHom.id L) ?_
  rw [eval₂_map]
  exact hp

variable {ι : Type*} {R : Subring L} {f : ι → L}

/-- Elements of the chart `R[f / f i]` become elements of `R[f / f j]` after multiplication by a
power of `f i / f j`. -/
lemma exists_mul_pow_mem_projChart (hf : ∀ i, f i ≠ 0) {i : ι} {x : L}
    (hx : x ∈ projChart R f i) : ∃ d : ℕ, ∀ j, x * (f i / f j) ^ d ∈ projChart R f j := by
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with hy | ⟨k, rfl⟩
    · exact ⟨0, fun j ↦ by simpa using base_le_projChart j hy⟩
    · refine ⟨1, fun j ↦ ?_⟩
      have : f k / f i * (f i / f j) ^ 1 = f k / f j := by
        field_simp [hf i, hf j]
      rw [this]
      exact div_mem_projChart j k
  | zero => exact ⟨0, fun j ↦ by simp⟩
  | one => exact ⟨0, fun j ↦ by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd⟩ := hy
    obtain ⟨e, he⟩ := hz
    refine ⟨d + e, fun j ↦ ?_⟩
    have hu := div_mem_projChart (R := R) (f := f) j i
    rw [add_mul, pow_add]
    refine add_mem ?_ ?_
    · rw [← mul_assoc]
      exact mul_mem (hd j) (pow_mem hu e)
    · rw [mul_comm ((f i / f j) ^ d), ← mul_assoc]
      exact mul_mem (he j) (pow_mem hu d)
  | neg y _ hy =>
    obtain ⟨d, hd⟩ := hy
    exact ⟨d, fun j ↦ by rw [neg_mul]; exact neg_mem (hd j)⟩
  | mul y z _ _ hy hz =>
    obtain ⟨d, hd⟩ := hy
    obtain ⟨e, he⟩ := hz
    refine ⟨d + e, fun j ↦ ?_⟩
    rw [pow_add, show y * z * ((f i / f j) ^ d * (f i / f j) ^ e) =
      (y * (f i / f j) ^ d) * (z * (f i / f j) ^ e) by ring]
    exact mul_mem (hd j) (he j)

lemma mul_pow_mem_projChart_of_le {i : ι} {x : L} {d e : ℕ} (hde : d ≤ e)
    {j : ι} (hx : x * (f i / f j) ^ d ∈ projChart R f j) :
    x * (f i / f j) ^ e ∈ projChart R f j := by
  have hu := div_mem_projChart (R := R) (f := f) j i
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  rw [pow_add, ← mul_assoc]
  exact mul_mem hx (pow_mem hu k)

end Shift

/-! ### Charts of the normalization -/

section Normalization

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] {ι : Type*} {R : Subring F}
  {f : ι → F}

/-- Elements of the normalization `B_i` of the chart `A_i = R[f / f i]` become elements of `B_j`
after multiplication by a power of `f i / f j`. -/
lemma exists_mul_pow_mem_normChart (hf : ∀ i, f i ≠ 0) {i : ι} {b : F'}
    (hb : b ∈ normChart F' (projChart R f i)) :
    ∃ e : ℕ, ∀ j, b * algebraMap F F' (f i / f j) ^ e ∈ normChart F' (projChart R f j) := by
  obtain ⟨p, hpm, hp⟩ := hb
  have hc (k : ℕ) : ∃ x ∈ projChart R f i, algebraMap F F' x = (p.coeff k : F') :=
    (p.coeff k).2
  choose x hx hxc using hc
  choose d hd using fun k ↦ exists_mul_pow_mem_projChart hf (hx k)
  refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), d k, fun j ↦ ?_⟩
  set e := ∑ k ∈ Finset.range (p.natDegree + 1), d k
  have hr : algebraMap F F' (f i / f j) ^ e ∈ (projChart R f j).map (algebraMap F F') :=
    ⟨(f i / f j) ^ e, pow_mem (div_mem_projChart j i) e, map_pow _ _ _⟩
  rw [mul_comm]
  refine isIntegral_mul_of_coeff hpm hp hr fun k ↦ ?_
  by_cases hk : k ≤ p.natDegree
  · rw [← hxc k, ← map_pow, ← map_mul]
    refine ⟨_, mul_pow_mem_projChart_of_le ?_ (hd k j), rfl⟩
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  · rw [p.coeff_eq_zero_of_natDegree_lt (not_le.1 hk)]
    simp

lemma algebraMap_ne_zero (hf : ∀ i, f i ≠ 0) (i : ι) : algebraMap F F' (f i) ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap F F').injective).2 (hf i)

lemma mem_normChart_of_mem {s : ι → Finset F'} (hs : ∀ j, normChart F' (projChart R f j) =
      Subring.closure (((projChart R f j).map (algebraMap F F') : Set F') ∪ s j))
    {i : ι} {b : F'} (hb : b ∈ s i) : b ∈ normChart F' (projChart R f i) := by
  rw [hs i]
  exact Subring.subset_closure (Or.inr hb)

variable [Fintype ι] (s : ι → Finset F')

open scoped Classical in
/-- The index set of the homogeneous coordinates of the normalization: the products
`f k f i ^ N` and `b f i ^ (N + 1)` for the nonzero generators `b ∈ s i` of the charts `B_i`. -/
abbrev NormIdx : Type _ := (ι × ι) ⊕ Σ i, ((s i).filter (· ≠ 0))

variable (R) in
open scoped Classical in
/-- The exponent `N`: the sum of the exponents of `exists_mul_pow_mem_normChart` for the
generators of the charts `B_i`. -/
noncomputable def normExp (hf : ∀ i, f i ≠ 0) : ℕ :=
  ∑ i, ∑ b ∈ (s i).attach, if h : (b : F') ∈ normChart F' (projChart R f i) then
    (exists_mul_pow_mem_normChart hf h).choose else 0

variable {s}

lemma le_normExp (hf : ∀ i, f i ≠ 0)
    (hs : ∀ j, normChart F' (projChart R f j) =
      Subring.closure (((projChart R f j).map (algebraMap F F') : Set F') ∪ s j))
    {i : ι} {b : F'} (hb : b ∈ s i) :
    ∃ e ≤ normExp R s hf, ∀ j, b * algebraMap F F' (f i / f j) ^ e ∈
      normChart F' (projChart R f j) := by
  classical
  have hbB := mem_normChart_of_mem hs hb
  refine ⟨(exists_mul_pow_mem_normChart hf hbB).choose, ?_,
    (exists_mul_pow_mem_normChart hf hbB).choose_spec⟩
  have h₁ : (exists_mul_pow_mem_normChart hf hbB).choose ≤
      ∑ b ∈ (s i).attach, if h : (b : F') ∈ normChart F' (projChart R f i) then
        (exists_mul_pow_mem_normChart hf h).choose else 0 := by
    have := Finset.single_le_sum (f := fun b : (s i) ↦
      if h : (b : F') ∈ normChart F' (projChart R f i) then
        (exists_mul_pow_mem_normChart hf h).choose else 0) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_attach _ ⟨b, hb⟩)
    simpa [hbB] using this
  refine h₁.trans ?_
  unfold normExp
  convert Finset.single_le_sum (f := fun i ↦ ∑ b ∈ (s i).attach,
    if h : (b : F') ∈ normChart F' (projChart R f i) then
      (exists_mul_pow_mem_normChart hf h).choose else 0) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)

variable (R s) in
open scoped Classical in
/-- **Homogeneous coordinates of the normalization** of the projective model of `f`. -/
noncomputable def normCoord (hf : ∀ i, f i ≠ 0) : NormIdx s → F'
  | .inl (k, i) => algebraMap F F' (f k) * algebraMap F F' (f i) ^ normExp R s hf
  | .inr ⟨i, b⟩ => (b : F') * algebraMap F F' (f i) ^ (normExp R s hf + 1)

variable (hf : ∀ i, f i ≠ 0)
  (hs : ∀ j, normChart F' (projChart R f j) =
    Subring.closure (((projChart R f j).map (algebraMap F F') : Set F') ∪ s j))

lemma normCoord_ne_zero (l : NormIdx s) : normCoord R s hf l ≠ 0 := by
  classical
  rcases l with ⟨k, i⟩ | ⟨i, b, hb⟩
  · exact mul_ne_zero (algebraMap_ne_zero (F' := F') hf k)
      (pow_ne_zero _ (algebraMap_ne_zero hf i))
  · exact mul_ne_zero (Finset.mem_filter.1 hb).2 (pow_ne_zero _ (algebraMap_ne_zero hf i))

lemma normCoord_diag (j : ι) :
    normCoord R s hf (.inl (j, j)) = algebraMap F F' (f j) ^ (normExp R s hf + 1) := by
  simp only [normCoord]
  ring

include hs in
/-- **The chart of the homogeneous coordinates `normCoord` at `f j ^ (N + 1)` is the
normalization `B_j` of the chart `R[f / f j]`.** -/
theorem projChart_normCoord (j : ι) :
    projChart (R.map (algebraMap F F')) (normCoord R s hf) (.inl (j, j)) =
      normChart F' (projChart R f j) := by
  classical
  set u : ι → F' := fun i ↦ algebraMap F F' (f i / f j)
  have hu (i : ι) : u i ∈ normChart F' (projChart R f j) :=
    map_le_normChart _ ⟨_, div_mem_projChart j i, rfl⟩
  have hj := algebraMap_ne_zero (F' := F') hf j
  apply le_antisymm
  · refine projChart_le ?_ fun l ↦ ?_
    · exact (subring_map_mono (base_le_projChart j) _).trans (map_le_normChart _)
    rw [normCoord_diag]
    rcases l with ⟨k, i⟩ | ⟨i, b, hb⟩
    · have : normCoord R s hf (.inl (k, i)) / algebraMap F F' (f j) ^ (normExp R s hf + 1) =
          u k * u i ^ normExp R s hf := by
        rw [div_eq_iff (pow_ne_zero _ hj)]
        simp only [normCoord, u, map_div₀, div_pow]
        field_simp
        ring
      rw [this]
      exact mul_mem (hu k) (pow_mem (hu i) _)
    · have hb' := (Finset.mem_filter.1 hb).1
      obtain ⟨e, he, hbe⟩ := le_normExp hf hs hb'
      have : normCoord R s hf (.inr ⟨i, b, hb⟩) / algebraMap F F' (f j) ^ (normExp R s hf + 1) =
          (b * u i ^ e) * u i ^ (normExp R s hf + 1 - e) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (he.trans (Nat.le_succ (normExp R s hf))),
          div_eq_iff (pow_ne_zero _ hj)]
        simp only [normCoord, u, map_div₀, div_pow]
        field_simp
      rw [this]
      exact mul_mem (hbe j) (pow_mem (hu i) _)
  · rw [hs j]
    refine Subring.closure_le.2 (Set.union_subset ?_ fun b hb ↦ ?_)
    · rintro _ ⟨x, hx, rfl⟩
      induction hx using Subring.closure_induction with
      | mem y hy =>
        rcases hy with hy | ⟨k, rfl⟩
        · exact base_le_projChart _ ⟨y, hy, rfl⟩
        · have e : algebraMap F F' (f k / f j) =
              normCoord R s hf (.inl (k, j)) / normCoord R s hf (.inl (j, j)) := by
            rw [normCoord_diag, eq_div_iff (pow_ne_zero _ hj)]
            simp only [normCoord, map_div₀, pow_succ]
            field_simp
          rw [e]
          exact div_mem_projChart _ _
      | zero => simp
      | one => simp
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | neg y _ hy => rw [map_neg]; exact neg_mem hy
      | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
    · rcases eq_or_ne b 0 with rfl | hb0
      · exact zero_mem _
      · have e : b = normCoord R s hf (.inr ⟨j, b, Finset.mem_filter.2 ⟨hb, hb0⟩⟩) /
            normCoord R s hf (.inl (j, j)) := by
          rw [normCoord_diag, eq_div_iff (pow_ne_zero _ hj)]
          rfl
        rw [e]
        exact div_mem_projChart _ _

end Normalization

end SemistableReduction
