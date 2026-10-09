/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerNormalForm

/-!
# Discretely valued coefficient fields in mixed characteristic

Blueprint §9.4, F1 (Kuhlmann, *Elimination of ramification I*, proof of Lemma 4.11). Let `F` be
a non-archimedean normed field with residue field `κ` (`KummerNormalForm.rd` is the residue
map on elements of norm `≤ 1`). For a subfield `K ⊆ F`:

* `residueSubfield K ⊆ κ`: the residues of the elements of `K` of norm `≤ 1`;
* `norm_sum_eq_sup'`: if `x₁, …, x_n` have norm `≤ 1` and residues linearly independent over
  `residueSubfield K`, then `‖Σ cᵢ xᵢ‖ = max ‖cᵢ‖` for `cᵢ ∈ K` (A1 for subfields);
* `IsDiscrete K π`: all nonzero elements of `K` have norm in `‖π‖ ^ ℤ`;
* `isDiscrete_adjoin_of_transcendental`, `isDiscrete_adjoin_of_root`: adjoining an element of
  norm `≤ 1` whose residue is transcendental over `residueSubfield K`, or a root of a monic
  polynomial over `K` whose residue has the same degree over `residueSubfield K`, preserves
  `IsDiscrete`.

**F1** (`exists_isDiscrete_residueSubfield_eq_top`): if `F` is algebraically closed of
characteristic `0` and `‖p‖ < 1`, there is a subfield `K₀ ⊆ F` with `‖K₀^×‖ ⊆ ‖p‖ ^ ℤ` and
residue field all of `κ`. Proof: Zorn's lemma on subfields with values in `‖p‖ ^ ℤ` (starting
from `ℚ`); a maximal one has full residue field, since a transcendental residue lifts by any
lift, and an algebraic residue `ā` lifts to a root of a lift of its minimal polynomial (which
exists in `F`: a monic polynomial with `‖g(a)‖ < 1` has a root within distance `< 1` of `a`,
`exists_root_norm_sub_lt_one`), both by A1 without changing the values.

Also `isAlgClosed_residueField`: the residue field of an algebraically closed non-archimedean
field is algebraically closed.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

open KummerNormalForm

namespace DiscreteCoefficients

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

local notation "𝒪" => HenselComplete.integers F

lemma rd_zero : rd (0 : F) = 0 := rd_eq_zero (by simp)

lemma rd_sub {x y : F} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : rd (x - y) = rd x - rd y := by
  rw [sub_eq_add_neg, rd_add hx (by rwa [norm_neg]), rd_neg, ← sub_eq_add_neg]

lemma rd_eq_of_norm_sub_lt_one {x y : F} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) :
    rd x = rd y := by
  rw [← sub_eq_zero, ← rd_sub hx hy]
  exact rd_eq_zero h

lemma rd_natCast (n : ℕ) : rd (n : F) = n := by
  rw [show (n : F) = ((n : 𝒪) : F) by simp, rd_coe, map_natCast]

lemma norm_eq_one_of_rd_ne_zero {x : F} (hx : ‖x‖ ≤ 1) (h : rd x ≠ 0) : ‖x‖ = 1 := by
  by_contra hne
  exact h (rd_eq_zero (lt_of_le_of_ne hx hne))

lemma rd_inv {x : F} (hx : ‖x‖ = 1) : rd x⁻¹ = (rd x)⁻¹ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h := rd_mul hx.le (by rw [norm_inv, hx, inv_one]) (x := x) (y := x⁻¹)
  rw [mul_inv_cancel₀ hx0, rd_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

section ResidueSubfield

/-- The residues of the elements of norm `≤ 1` of a subfield `K`. -/
def residueSubfield (K : Subfield F) : Subfield (ResidueField 𝒪) where
  carrier := {z | ∃ a ∈ K, ‖a‖ ≤ 1 ∧ rd a = z}
  zero_mem' := ⟨0, K.zero_mem, by simp, rd_zero⟩
  one_mem' := ⟨1, K.one_mem, by simp, rd_one⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, ha1, rfl⟩ ⟨b, hb, hb1, rfl⟩
    exact ⟨a + b, K.add_mem ha hb,
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 hb1), rd_add ha1 hb1⟩
  neg_mem' := by
    rintro _ ⟨a, ha, ha1, rfl⟩
    exact ⟨-a, K.neg_mem ha, by rwa [norm_neg], rd_neg a⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, ha1, rfl⟩ ⟨b, hb, hb1, rfl⟩
    exact ⟨a * b, K.mul_mem ha hb, by rw [norm_mul]; exact mul_le_one₀ ha1 (norm_nonneg _) hb1,
      rd_mul ha1 hb1⟩
  inv_mem' := by
    rintro _ ⟨a, ha, ha1, rfl⟩
    by_cases h0 : rd a = 0
    · exact ⟨0, K.zero_mem, by simp, by rw [h0, inv_zero, rd_zero]⟩
    · have ha' := norm_eq_one_of_rd_ne_zero ha1 h0
      exact ⟨a⁻¹, K.inv_mem ha, by rw [norm_inv, ha', inv_one], rd_inv ha'⟩

lemma mem_residueSubfield {K : Subfield F} {z : ResidueField 𝒪} :
    z ∈ residueSubfield K ↔ ∃ a ∈ K, ‖a‖ ≤ 1 ∧ rd a = z := Iff.rfl

lemma rd_mem_residueSubfield {K : Subfield F} {a : F} (ha : a ∈ K) (ha1 : ‖a‖ ≤ 1) :
    rd a ∈ residueSubfield K := ⟨a, ha, ha1, rfl⟩

lemma residueSubfield_mono {K K' : Subfield F} (h : K ≤ K') :
    residueSubfield K ≤ residueSubfield K' := by
  rintro _ ⟨a, ha, ha1, rfl⟩
  exact ⟨a, h ha, ha1, rfl⟩

/-- **A1 for subfields.** If `x₁, …, x_n` have norm `≤ 1` and residues linearly independent over
the residue field of `K`, then `‖Σ cᵢ xᵢ‖ = max ‖cᵢ‖` for `cᵢ ∈ K`. -/
theorem norm_sum_eq_sup' (K : Subfield F) {ι : Type*} {x : ι → F} (hx : ∀ i, ‖x i‖ ≤ 1)
    (hind : LinearIndependent (residueSubfield K) (fun i ↦ rd (x i))) {s : Finset ι}
    (hs : s.Nonempty) {c : ι → F} (hc : ∀ i ∈ s, c i ∈ K) :
    ‖∑ i ∈ s, c i * x i‖ = s.sup' hs fun i ↦ ‖c i‖ := by
  classical
  obtain ⟨j, hjs, hj⟩ := s.exists_mem_eq_sup' hs fun i ↦ ‖c i‖
  have hle : ∀ i ∈ s, ‖c i‖ ≤ ‖c j‖ := fun i hi ↦ hj ▸ s.le_sup' (fun i ↦ ‖c i‖) hi
  rw [hj]
  by_cases hcj : c j = 0
  · have h0 : ∀ i ∈ s, c i = 0 := fun i hi ↦ norm_eq_zero.1
      (le_antisymm ((hle i hi).trans (by rw [hcj, norm_zero])) (norm_nonneg _))
    rw [Finset.sum_eq_zero fun i hi ↦ by rw [h0 i hi, zero_mul], hcj, norm_zero]
  have hcjn : 0 < ‖c j‖ := norm_pos_iff.2 hcj
  have hq (i : ι) (hi : i ∈ s) : ‖c i / c j‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ (hle i hi) hcjn.le
  set y := ∑ i ∈ s, c i / c j * x i with hy
  have hsum : ∑ i ∈ s, c i * x i = c j * y := by
    rw [hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
  have hterm (i : ι) (hi : i ∈ s) : ‖c i / c j * x i‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ (hq i hi) (norm_nonneg _) (hx i)
  have hy1 : ‖y‖ ≤ 1 := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one hterm
  have hrdy : rd y = ∑ i ∈ s, rd (c i / c j) * rd (x i) := by
    rw [hy, rd_sum s _ hterm]
    exact Finset.sum_congr rfl fun i hi ↦ rd_mul (hq i hi) (hx i)
  have hy0 : rd y ≠ 0 := by
    intro h
    let g : ι → residueSubfield K := fun i ↦ if hi : i ∈ s then
      ⟨rd (c i / c j), ⟨c i / c j, K.div_mem (hc i hi) (hc j hjs), hq i hi, rfl⟩⟩ else 0
    have := (linearIndependent_iff'.1 hind) s g (by
      rw [← h, hrdy]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [g, dif_pos hi]
      rfl) j hjs
    have h1 : ((g j : residueSubfield K) : ResidueField 𝒪) = 1 := by
      simp only [g, dif_pos hjs, div_self hcj, rd_one]
    rw [this] at h1
    exact zero_ne_one h1
  rw [hsum, norm_mul, norm_eq_one_of_rd_ne_zero hy1 hy0, mul_one]

/-- Powers of a transcendental residue are linearly independent. -/
lemma linearIndependent_pow_of_transcendental {R L : Type*} [Field R] [Field L] [Algebra R L]
    {x : L} (hx : Transcendental R x) : LinearIndependent R fun i : ℕ ↦ x ^ i := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hp : aeval x (∑ j ∈ s, C (g j) * X ^ j) = 0 := by
    rw [← hg, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [_root_.map_mul, aeval_C, _root_.map_pow, aeval_X, Algebra.smul_def]
  have h := congrArg (fun q ↦ coeff q i) (transcendental_iff.1 hx _ hp)
  simpa [finsetSum_coeff, coeff_C_mul, coeff_X_pow, hi] using h

end ResidueSubfield

section Discrete

/-- All nonzero elements of `K` have norm in `‖π‖ ^ ℤ`. -/
def IsDiscrete (K : Subfield F) (π : F) : Prop :=
  ∀ x ∈ K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n

/-- `K(a)`, as a subfield of `F`. -/
noncomputable abbrev adjoin (K : Subfield F) (a : F) : Subfield F :=
  (IntermediateField.adjoin K {a}).toSubfield

omit [IsUltrametricDist F] in
lemma le_adjoin (K : Subfield F) (a : F) : K ≤ adjoin K a := fun x hx ↦
  (IntermediateField.adjoin K {a}).algebraMap_mem ⟨x, hx⟩

omit [IsUltrametricDist F] in
lemma mem_adjoin_self (K : Subfield F) (a : F) : a ∈ adjoin K a :=
  IntermediateField.mem_adjoin_simple_self K a

variable {π : F}

/-- The norm of a polynomial expression `Σ cᵢ aⁱ` with independent residues of the powers. -/
lemma norm_aeval_eq {K : Subfield F} (hK : IsDiscrete K π) {a : F} (ha : ‖a‖ ≤ 1) {n : ℕ}
    (hind : LinearIndependent (residueSubfield K) fun i : Fin n ↦ rd a ^ (i : ℕ))
    {r : K[X]} (hr : r.natDegree < n) (hr0 : r ≠ 0) :
    ∃ m : ℤ, ‖aeval a r‖ = ‖π‖ ^ m := by
  classical
  have hn : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) hr⟩⟩
  have hsum : aeval a r = ∑ i : Fin n, ((r.coeff i : K) : F) * a ^ (i : ℕ) := by
    rw [aeval_eq_sum_range' hr, ← Fin.sum_univ_eq_sum_range (fun i ↦ r.coeff i • a ^ i)]
    rfl
  have hxi : ∀ i : Fin n, ‖a ^ (i : ℕ)‖ ≤ 1 := fun i ↦ by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha
  have hind' : LinearIndependent (residueSubfield K) fun i : Fin n ↦ rd (a ^ (i : ℕ)) := by
    convert hind using 2 with i
    exact rd_pow ha _
  rw [hsum, norm_sum_eq_sup' K hxi hind' hn fun i _ ↦ (r.coeff i).2]
  obtain ⟨j, -, hj⟩ := Finset.univ.exists_mem_eq_sup' hn fun i : Fin n ↦ ‖((r.coeff i : K) : F)‖
  rw [hj]
  obtain ⟨k, hk⟩ : ∃ k, r.coeff k ≠ 0 := by
    by_contra! h
    exact hr0 (Polynomial.ext fun k ↦ by simpa using h k)
  have hkn : k < n := lt_of_le_of_lt (le_natDegree_of_ne_zero hk) hr
  have hj0 : ((r.coeff j : K) : F) ≠ 0 := by
    intro h0
    have := hj ▸ Finset.univ.le_sup' (fun i : Fin n ↦ ‖((r.coeff i : K) : F)‖)
      (Finset.mem_univ (⟨k, hkn⟩ : Fin n))
    rw [h0, norm_zero] at this
    exact hk (by exact_mod_cast norm_eq_zero.1 (le_antisymm this (norm_nonneg _)))
  exact hK _ (r.coeff j).2 hj0

/-- **Adjoining a lift of a transcendental residue** preserves discreteness. -/
theorem isDiscrete_adjoin_of_transcendental (hπ : π ≠ 0) {K : Subfield F} (hK : IsDiscrete K π)
    {a : F}
    (ha : ‖a‖ ≤ 1) (htr : Transcendental (residueSubfield K) (rd a)) :
    IsDiscrete (adjoin K a) π := by
  intro x hx hx0
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K x).1 hx
  have hind (n : ℕ) : LinearIndependent (residueSubfield K) fun i : Fin n ↦ rd a ^ (i : ℕ) :=
    (linearIndependent_pow_of_transcendental htr).comp _ Fin.val_injective
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hx0
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hx0
  obtain ⟨m₁, hm₁⟩ := norm_aeval_eq hK ha (hind (r.natDegree + 1)) (Nat.lt_succ_self _) hr0
  obtain ⟨m₂, hm₂⟩ := norm_aeval_eq hK ha (hind (s.natDegree + 1)) (Nat.lt_succ_self _) hs0
  exact ⟨m₁ - m₂, by rw [norm_div, hm₁, hm₂, zpow_sub₀ (norm_ne_zero_iff.2 hπ)]⟩

/-- **Adjoining a root** of a monic polynomial over `K` whose residue has the same degree over
`residueSubfield K` preserves discreteness. -/
theorem isDiscrete_adjoin_of_root {K : Subfield F} (hK : IsDiscrete K π) {b : F}
    (hb : ‖b‖ ≤ 1) {g : K[X]} (hg : g.Monic) (hgb : aeval b g = 0)
    (hind : LinearIndependent (residueSubfield K) fun i : Fin g.natDegree ↦ rd b ^ (i : ℕ)) :
    IsDiscrete (adjoin K b) π := by
  intro x hx hx0
  have hint : IsIntegral K b := ⟨g, hg, hgb⟩
  have hx' : x ∈ (IntermediateField.adjoin K {b}).toSubalgebra := hx
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨h, rfl⟩ := hx'
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [map_one] at hgb
    exact one_ne_zero hgb
  have hr : aeval b (h %ₘ g) = aeval b h := aeval_modByMonic_eq_self_of_root hgb
  have hr0 : h %ₘ g ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hr
    exact hx0 hr.symm
  obtain ⟨m, hm⟩ := norm_aeval_eq hK hb hind (natDegree_modByMonic_lt h hg hg1) hr0
  refine ⟨m, ?_⟩
  change ‖aeval b h‖ = _
  rw [← hr]
  exact hm

omit [IsUltrametricDist F] in
/-- In an algebraically closed field, a monic `g` with `‖g(a)‖ < 1` has a root `b` with
`‖b - a‖ < 1` (as `g(a) = Π (a - r)` over the roots `r`). -/
theorem exists_root_norm_sub_lt_one [IsAlgClosed F] {g : F[X]} (hg : g.Monic) {a : F}
    (h : ‖g.eval a‖ < 1) : ∃ b, g.eval b = 0 ∧ ‖b - a‖ < 1 := by
  by_contra! hall
  have key : ∀ S : Multiset F, (∀ r ∈ S, 1 ≤ ‖a - r‖) →
      1 ≤ ‖(S.map fun r ↦ a - r).prod‖ := by
    intro S
    induction S using Multiset.induction_on with
    | empty => simp
    | cons r S ih =>
      intro hS
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact one_le_mul_of_one_le_of_one_le (hS r (Multiset.mem_cons_self r S))
        (ih fun r' hr' ↦ hS r' (Multiset.mem_cons_of_mem hr'))
  have heq := (IsAlgClosed.splits g).eq_prod_roots_of_monic hg
  have h1 : 1 ≤ ‖g.eval a‖ := by
    rw [heq, eval_multiset_prod, Multiset.map_map]
    have hm : Multiset.map (eval a ∘ fun x ↦ X - C x) g.roots = g.roots.map fun r ↦ a - r :=
      Multiset.map_congr rfl fun r _ ↦ by simp
    rw [hm]
    exact key g.roots fun r hr ↦ by
      rw [norm_sub_rev]
      exact hall r ((mem_roots hg.ne_zero).1 hr)
  exact absurd h (not_lt.2 h1)

/-- The rationals have values in `‖p‖ ^ ℤ` if `‖p‖ < 1`. -/
theorem isDiscrete_bot [CharZero F] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : F)‖ < 1) :
    IsDiscrete (⊥ : Subfield F) (p : F) := by
  haveI := charP_residueField hp hp1
  have hp0 : ‖(p : F)‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  have hnat : ∀ m : ℕ, ¬p ∣ m → ‖(m : F)‖ = 1 := by
    intro m hm
    by_contra hne
    have hlt : ‖(m : F)‖ < 1 := lt_of_le_of_ne (IsUltrametricDist.norm_natCast_le_one F m) hne
    have := rd_eq_zero hlt
    rw [rd_natCast, CharP.cast_eq_zero_iff _ p] at this
    exact hm this
  have hint : ∀ n : ℤ, n ≠ 0 → ∃ e : ℕ, ‖(n : F)‖ = ‖(p : F)‖ ^ e := by
    intro n hn
    obtain ⟨e, m, hm, hnm⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hn) p hp.one_lt.ne'
    refine ⟨e, ?_⟩
    have habs : ‖(n : F)‖ = ‖((n.natAbs : ℕ) : F)‖ := by
      rcases Int.natAbs_eq n with h | h
      · conv_lhs => rw [h]
        rw [Int.cast_natCast]
      · conv_lhs => rw [h]
        rw [Int.cast_neg, norm_neg, Int.cast_natCast]
    rw [habs, hnm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hnat m hm, mul_one]
  intro x hx hx0
  obtain ⟨q, rfl⟩ : x ∈ (Rat.castHom F).fieldRange :=
    (bot_le : (⊥ : Subfield F) ≤ (Rat.castHom F).fieldRange) hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hx0
  obtain ⟨e₁, he₁⟩ := hint q.num (Rat.num_ne_zero.2 hq0)
  obtain ⟨e₂, he₂⟩ := hint q.den (by exact_mod_cast q.den_nz)
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  have hcast : Rat.castHom F q = (q.num : F) / ((q.den : ℕ) : F) := Rat.cast_def q
  rw [hcast, norm_div, he₁, show ‖((q.den : ℕ) : F)‖ = ‖(p : F)‖ ^ e₂ by
    rw [← he₂, Int.cast_natCast], zpow_sub₀ hp0, zpow_natCast, zpow_natCast]

/-- **F1: a discretely valued coefficient field.** If `F` is algebraically closed of
characteristic `0` and `‖p‖ < 1`, there is a subfield `K₀ ⊆ F` whose nonzero elements have
norms in `‖p‖ ^ ℤ` and whose residues exhaust the residue field of `F`. -/
theorem exists_isDiscrete_residueSubfield_eq_top [IsAlgClosed F] [CharZero F] {p : ℕ}
    (hp : p.Prime) (hp1 : ‖(p : F)‖ < 1) :
    ∃ K₀ : Subfield F, IsDiscrete K₀ (p : F) ∧ residueSubfield K₀ = ⊤ := by
  have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨K₀, -, hmax⟩ := zorn_le_nonempty₀ {K : Subfield F | IsDiscrete K (p : F)}
    (fun c hcS hc y hy ↦ ⟨sSup c, fun x hx hx0 ↦ by
      obtain ⟨K, hK, hxK⟩ := (Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hc.directedOn).1 hx
      exact hcS hK x hxK hx0, fun z hz ↦ le_sSup hz⟩) ⊥ (isDiscrete_bot hp hp1)
  have hK₀ : IsDiscrete K₀ (p : F) := hmax.prop
  refine ⟨K₀, hK₀, eq_top_iff.2 fun ā _ ↦ ?_⟩
  by_contra hā
  have key : ∀ a : F, ‖a‖ ≤ 1 → rd a = ā → IsDiscrete (adjoin K₀ a) (p : F) → False :=
    fun a ha1 hra hd ↦ hā ⟨a, hmax.le_of_ge hd (le_adjoin K₀ a) (mem_adjoin_self K₀ a), ha1, hra⟩
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective ā
  have ha₀1 : ‖(a₀ : F)‖ ≤ 1 := HenselComplete.norm_le_one a₀
  have ha₀rd : rd (a₀ : F) = ā := by rw [rd_coe, ha₀]
  by_cases htr : Transcendental (residueSubfield K₀) ā
  · exact key _ ha₀1 ha₀rd (isDiscrete_adjoin_of_transcendental hp0 hK₀ ha₀1 (ha₀rd ▸ htr))
  -- the algebraic case: lift the minimal polynomial and take a root near `a₀`
  have hint : IsIntegral (residueSubfield K₀) ā := (not_not.1 htr).isIntegral
  set R := residueSubfield K₀
  set n := (minpoly R ā).natDegree with hn
  have hlift : ∀ i, ∃ c ∈ K₀, ‖c‖ ≤ 1 ∧ rd c = ((minpoly R ā).coeff i : ResidueField 𝒪) :=
    fun i ↦ ((minpoly R ā).coeff i).2
  choose c hcK hc1 hcrd using hlift
  set g : K₀[X] := X ^ n + ∑ i : Fin n, C (⟨c i, hcK i⟩ : K₀) * X ^ (i : ℕ) with hg
  have hdeg : (∑ i : Fin n, C (⟨c i, hcK i⟩ : K₀) * X ^ (i : ℕ)).degree < (n : WithBot ℕ) :=
    degree_sum_fin_lt _
  have hgm : g.Monic := monic_X_pow_add hdeg
  have hgn : g.natDegree = n := by
    rw [hg, natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have heval (x : F) : (g.map (algebraMap K₀ F)).eval x =
      x ^ n + ∑ i : Fin n, c i * x ^ (i : ℕ) := by
    simp only [hg, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
      Polynomial.map_mul, map_C, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    rfl
  have hterm1 (x : F) (hx : ‖x‖ ≤ 1) (i : Fin n) : ‖c i * x ^ (i : ℕ)‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (hc1 i) (by positivity) (pow_le_one₀ (norm_nonneg _) hx)
  have hpow1 (x : F) (hx : ‖x‖ ≤ 1) : ‖x ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hx
  have hsum1 (x : F) (hx : ‖x‖ ≤ 1) : ‖∑ i : Fin n, c i * x ^ (i : ℕ)‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ hterm1 x hx i
  have hrd : rd ((g.map (algebraMap K₀ F)).eval (a₀ : F)) = 0 := by
    rw [heval, rd_add (hpow1 _ ha₀1) (hsum1 _ ha₀1), rd_pow ha₀1,
      rd_sum _ _ fun i _ ↦ hterm1 _ ha₀1 i, ha₀rd]
    have hterm : ∀ i : Fin n, rd (c i * (a₀ : F) ^ (i : ℕ)) =
        algebraMap R (ResidueField 𝒪) ((minpoly R ā).coeff i) * ā ^ (i : ℕ) := fun i ↦ by
      rw [rd_mul (hc1 i) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha₀1),
        rd_pow ha₀1, ha₀rd, hcrd]
      rfl
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i,
      Fin.sum_univ_eq_sum_range (fun i ↦ algebraMap R (ResidueField 𝒪)
        ((minpoly R ā).coeff i) * ā ^ i) n]
    have hmin := minpoly.aeval R ā
    rw [(minpoly.monic hint).as_sum] at hmin
    simp only [map_add, map_pow, aeval_X, map_sum, _root_.map_mul, aeval_C] at hmin
    exact hmin
  have hle : ‖(g.map (algebraMap K₀ F)).eval (a₀ : F)‖ ≤ 1 := by
    rw [heval]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hpow1 _ ha₀1) (hsum1 _ ha₀1))
  obtain ⟨b, hb0, hba⟩ := exists_root_norm_sub_lt_one (hgm.map _) ((rd_eq_zero_iff hle).1 hrd)
  have hb1 : ‖b‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (b - a₀) (a₀ : F)
    rw [sub_add_cancel] at this
    exact this.trans (max_le hba.le ha₀1)
  have hrdb : rd b = ā := (rd_eq_of_norm_sub_lt_one hb1 ha₀1 hba).trans ha₀rd
  have hgb : aeval b g = 0 := by
    rw [← eval_map_algebraMap]
    exact hb0
  have hind : LinearIndependent R fun i : Fin g.natDegree ↦ rd b ^ (i : ℕ) := by
    rw [hgn, hrdb]
    exact linearIndependent_pow ā
  exact key b hb1 hrdb (isDiscrete_adjoin_of_root hK₀ hb1 hgm hgb hind)

end Discrete

/-- The residue field of an algebraically closed non-archimedean field is algebraically
closed. -/
theorem isAlgClosed_residueField [IsAlgClosed F] : IsAlgClosed (ResidueField 𝒪) := by
  refine IsAlgClosed.of_exists_root _ fun q hq hirr ↦ ?_
  have hlifts : q ∈ lifts (residue 𝒪) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n ↦ IsLocalRing.residue_surjective _
  obtain ⟨Q, hQ, hQdeg, hQm⟩ := lifts_and_degree_eq_and_monic hlifts hq
  have hdeg : (Q.map (algebraMap 𝒪 F)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (fun _ _ h ↦ Subtype.ext h), hQdeg]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root _ hdeg
  have hint : IsIntegral 𝒪 b := ⟨Q, hQm, by rw [← eval_map]; exact hb⟩
  have hmem : b ∈ 𝒪 := (Valuation.valuationSubring.integers _).mem_of_integral hint
  refine ⟨residue 𝒪 ⟨b, hmem⟩, ?_⟩
  have h0 : Q.eval (⟨b, hmem⟩ : 𝒪) = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero, ← hb.eq_zero, eval_map]
    exact (eval₂_at_apply (algebraMap 𝒪 F) (⟨b, hmem⟩ : 𝒪) (p := Q)).symm
  rw [← hQ, eval_map, eval₂_at_apply, h0, map_zero]

end DiscreteCoefficients

end SemistableReduction
