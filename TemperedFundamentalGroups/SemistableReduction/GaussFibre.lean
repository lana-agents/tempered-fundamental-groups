/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussStability
import TemperedFundamentalGroups.SemistableReduction.WeakApproximation

/-!
# The fibre of a finite extension of `C(X)` over the Gauss point

Blueprint §9.5, G6.2–G6.3. Let `C` be a non-archimedean field, `w_{0,1} = gauss1 C` the Gauss
valuation of `C(X)` (`w(Σ cᵢ Xⁱ) = max ‖cᵢ‖`) and `F / C(X)` a finite extension. We study the
finitely many extensions `w ∈ Ext C F` of `w_{0,1}` to `F` (`GaussStability.GaussExtension`) and
the norm `gnorm C f = max_w w(f)`.

* `exists_gauss1_eq`: the values of `w_{0,1}` are norms of elements of `C`; if `e(w) = 1` the same
  holds for `w` (`exists_valuation_eq_norm`);
* `incomparable`: two distinct extensions with `e = 1` have incomparable valuation rings, so weak
  approximation applies (`SemistableReduction.WeakApproximation`);
* `gnorm`, with `gnorm_add_le`, `gnorm_mul_le`, `gnorm_algebraMap_mul`;
* **G6.3** `exists_orthonormal_basis`: if `e(w) = 1` for all `w` and `Σ_w f(w) = [F : C(X)]` (both
  are consequences of W4), then `F` has a `C(X)`-basis `b` with
  `gnorm C (Σ φᵢ bᵢ) = maxᵢ w_{0,1}(φᵢ)`: lift bases of the residue fields `κ(w) / k(x̄)` and
  separate
  the extensions by weak approximation.
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

variable (C) in
/-- The Gauss valuation `w_{0,1}` of `C(X)`. -/
noncomputable abbrev gauss1 : Valuation (RatFunc C) ℝ≥0 :=
  gaussRat (NormedField.valuation (K := C)) 0 1

lemma gauss1_algebraMap (Q : C[X]) :
    gauss1 C (algebraMap C[X] (RatFunc C) Q) = Gauss.sup (NormedField.valuation (K := C)) 1 Q := by
  rw [gaussRat_algebraMap, gauss_apply, taylor_zero]

lemma gauss1_algebraMap_C (c : C) : gauss1 C (algebraMap C (RatFunc C) c) = ‖c‖₊ := by
  rw [gaussRat_algebraMap_C, NormedField.valuation_apply]

lemma exists_sup_eq (Q : C[X]) :
    ∃ c : C, Gauss.sup (NormedField.valuation (K := C)) 1 Q = ‖c‖₊ := by
  obtain ⟨j, hj⟩ := Gauss.exists_term_eq_sup (v := NormedField.valuation (K := C)) (r := 1) Q
  refine ⟨Q.coeff j, ?_⟩
  rw [← hj, Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply]

/-- The values of `w_{0,1}` are norms of elements of `C`. -/
lemma exists_gauss1_eq (φ : RatFunc C) : ∃ c : C, gauss1 C φ = ‖c‖₊ := by
  obtain ⟨a, ha⟩ := exists_sup_eq φ.num
  obtain ⟨b, hb⟩ := exists_sup_eq φ.denom
  refine ⟨a / b, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom φ]
  rw [map_div₀, gauss1_algebraMap, gauss1_algebraMap, ha, hb, nnnorm_div]

variable (C) (F : Type*) [Field F] [Algebra (RatFunc C) F]

/-- The extensions of the Gauss valuation `w_{0,1}` to `F`. -/
abbrev Ext := GaussExtension (0 : C) (1 : ℝ≥0ˣ) F

variable {C F}

lemma valuation_algebraMap (w : Ext C F) (φ : RatFunc C) :
    w.1 (algebraMap (RatFunc C) F φ) = gauss1 C φ := by
  rw [← comap_apply, w.2]

lemma valuation_algebraMap_C (w : Ext C F) (c : C) :
    w.1 (algebraMap (RatFunc C) F (algebraMap C (RatFunc C) c)) = ‖c‖₊ := by
  rw [valuation_algebraMap, gauss1_algebraMap_C]

/-- If `e(w) = 1`, the values of `w` are norms of elements of `C`. -/
lemma exists_valuation_eq_norm {w : Ext C F} (he : ramificationIdx (RatFunc C) w.1 = 1)
    (f : F) : ∃ c : C, w.1 f = ‖c‖₊ := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, by simp⟩
  have hwf : w.1 f ≠ 0 := (Valuation.ne_zero_iff _).2 hf
  have hmem : Units.mk0 _ hwf ∈ valueGroup (w.1.comap (algebraMap (RatFunc C) F)) :=
    Subgroup.relIndex_eq_one.1 he ⟨f, rfl⟩
  obtain ⟨φ, hφ⟩ := hmem
  obtain ⟨c, hc⟩ := exists_gauss1_eq φ
  refine ⟨c, ?_⟩
  have : w.1 (algebraMap (RatFunc C) F φ) = w.1 f := by simpa using hφ
  rw [← this, valuation_algebraMap, hc]

/-- Two extensions with `e = 1` whose valuation rings are comparable are equal. -/
lemma eq_of_le {w w' : Ext C F} (he : ramificationIdx (RatFunc C) w.1 = 1)
    (h : ∀ a, w.1 a ≤ 1 → w'.1 a ≤ 1) : w = w' := by
  refine Subtype.ext (Valuation.ext fun f ↦ ?_)
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨c, hc⟩ := exists_valuation_eq_norm he f
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero, Valuation.zero_iff] at hc
    exact hf hc
  set γ := algebraMap (RatFunc C) F (algebraMap C (RatFunc C) c)
  have hγ0 : γ ≠ 0 := by simp [γ, hc0]
  have hγ : w.1 γ = ‖c‖₊ := valuation_algebraMap_C w c
  have hγ' : w'.1 γ = ‖c‖₊ := valuation_algebraMap_C w' c
  have hpos : (0 : ℝ≥0) < ‖c‖₊ := nnnorm_pos.2 hc0
  have h1 : w'.1 (f / γ) ≤ 1 := h _ (by rw [map_div₀, hc, hγ, div_self hpos.ne'])
  have h2 : w'.1 (γ / f) ≤ 1 := h _ (by rw [map_div₀, hc, hγ, div_self hpos.ne'])
  rw [map_div₀, hγ', div_le_one₀ hpos] at h1
  rw [map_div₀, hγ', div_le_one₀ ((Valuation.pos_iff _).2 hf)] at h2
  rw [hc]
  exact (le_antisymm h1 h2).symm

/-- Distinct extensions with `e = 1` are incomparable. -/
lemma incomparable (he : ∀ w : Ext C F, ramificationIdx (RatFunc C) w.1 = 1) {w w' : Ext C F}
    (h : w ≠ w') :
    WeakApproximation.Incomparable (fun w : Ext C F ↦ w.1) w w' := by
  refine ⟨?_, ?_⟩
  · by_contra! H
    exact h (eq_of_le (he w) H)
  · by_contra! H
    exact h (eq_of_le (he w') H).symm

section W4

variable [IsAlgClosed C]

/-- The values of `w_{0,1}` form a divisible group. -/
lemma gauss1_divisible (c : RatFunc C) (n : ℕ) (hn : 0 < n) :
    ∃ d : RatFunc C, gauss1 C d ^ n = gauss1 C c := by
  obtain ⟨a, ha⟩ := exists_gauss1_eq c
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hn
  exact ⟨algebraMap C (RatFunc C) b, by rw [gauss1_algebraMap_C, ha, ← hb, nnnorm_pow]⟩

/-- `e(w) = 1` for every extension of `w_{0,1}` (the value group of `C` is divisible). -/
lemma ramificationIdx_eq_one [FiniteDimensional (RatFunc C) F] (w : Ext C F) :
    ramificationIdx (RatFunc C) w.1 = 1 :=
  ramificationIdx_eq_one_of_divisible' w.1 (v := gauss1 C) gauss1_divisible

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [FiniteDimensional (RatFunc C) F]
include hp hp1

/-- **W4** for `w_{0,1}`: `Σ_w e(w) f(w) = [F : C(X)]`. -/
lemma finsum_eq_finrank :
    ∑ᶠ w : Ext C F, ramificationIdx (RatFunc C) w.1 * inertiaDeg (gauss1 C) w.1 =
      Module.finrank (RatFunc C) F :=
  finsum_ramificationIdx_mul_inertiaDeg_eq (a := 0) (c := 1) (by simp) hp hp1

/-- There are only finitely many extensions of `w_{0,1}`. -/
lemma finite_ext : Finite (Ext C F) := by
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  have hsupp : (Function.support fun w : Ext C F ↦
      ramificationIdx (RatFunc C) w.1 * inertiaDeg (gauss1 C) w.1).Infinite := by
    convert Set.infinite_univ (α := Ext C F)
    ext w
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    rw [ramificationIdx_eq_one, one_mul]
    haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
      (ResidueField w.1.valuationSubring) := finite_residueField
    exact Module.finrank_pos.ne'
  have h := finsum_eq_finrank (F := F) hp hp1
  rw [finsum_of_infinite_support hsupp] at h
  exact Module.finrank_pos.ne' h.symm

/-- **W4** for `w_{0,1}`, summed over the finite set of extensions: `Σ_w f(w) = [F : C(X)]`. -/
lemma sum_inertiaDeg_eq [Fintype (Ext C F)] :
    ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F := by
  rw [← finsum_eq_finrank hp hp1, finsum_eq_sum_of_fintype]
  simp [ramificationIdx_eq_one]

end W4

section Norm

variable [Fintype (Ext C F)]

variable (C) in
/-- The norm `‖f‖ = max_w w(f)` over the extensions of the Gauss valuation. -/
noncomputable def gnorm (f : F) : ℝ≥0 := Finset.univ.sup fun w : Ext C F ↦ w.1 f

lemma le_gnorm (w : Ext C F) (f : F) : w.1 f ≤ gnorm C f :=
  Finset.le_sup (f := fun w : Ext C F ↦ w.1 f) (Finset.mem_univ w)

lemma gnorm_le_iff {f : F} {r : ℝ≥0} : gnorm C f ≤ r ↔ ∀ w : Ext C F, w.1 f ≤ r := by
  simp [gnorm, Finset.sup_le_iff]

lemma gnorm_lt_iff {f : F} {r : ℝ≥0} (hr : 0 < r) :
    gnorm C f < r ↔ ∀ w : Ext C F, w.1 f < r := by
  simp [gnorm, Finset.sup_lt_iff hr]

@[simp]
lemma gnorm_zero : gnorm C (0 : F) = 0 := by
  simp [gnorm]

lemma gnorm_add_le (f g : F) : gnorm C (f + g) ≤ max (gnorm C f) (gnorm C g) :=
  gnorm_le_iff.2 fun w ↦ (Valuation.map_add _ _ _).trans
    (max_le_max (le_gnorm w f) (le_gnorm w g))

lemma gnorm_neg (f : F) : gnorm C (-f) = gnorm C f := by
  simp [gnorm]

lemma gnorm_sub_le (f g : F) : gnorm C (f - g) ≤ max (gnorm C f) (gnorm C g) := by
  rw [sub_eq_add_neg, ← gnorm_neg g]
  exact gnorm_add_le f (-g)

lemma gnorm_mul_le (f g : F) : gnorm C (f * g) ≤ gnorm C f * gnorm C g :=
  gnorm_le_iff.2 fun w ↦ by
    rw [map_mul]
    exact mul_le_mul' (le_gnorm w f) (le_gnorm w g)

lemma gnorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → F) :
    gnorm C (∑ i ∈ s, f i) ≤ s.sup fun i ↦ gnorm C (f i) :=
  gnorm_le_iff.2 fun w ↦ (Valuation.map_sum_le _ fun i hi ↦
    (le_gnorm w (f i)).trans (Finset.le_sup (f := fun i ↦ gnorm C (f i)) hi))

lemma gnorm_algebraMap_mul (φ : RatFunc C) (f : F) :
    gnorm C (algebraMap (RatFunc C) F φ * f) = gauss1 C φ * gnorm C f := by
  simp only [gnorm, map_mul, valuation_algebraMap]
  exact (Finset.mul_sup₀ _ _ _).symm

lemma gnorm_smul (φ : RatFunc C) (f : F) : gnorm C (φ • f) = gauss1 C φ * gnorm C f := by
  rw [Algebra.smul_def, gnorm_algebraMap_mul]

lemma gnorm_algebraMap [Nonempty (Ext C F)] (φ : RatFunc C) :
    gnorm C (algebraMap (RatFunc C) F φ) = gauss1 C φ := by
  simp [gnorm, valuation_algebraMap, Finset.sup_const Finset.univ_nonempty]

lemma gnorm_one [Nonempty (Ext C F)] : gnorm C (1 : F) = 1 := by
  simpa using gnorm_algebraMap (C := C) (F := F) 1

end Norm

section Orthonormal

variable [Fintype (Ext C F)] [FiniteDimensional (RatFunc C) F]

/-- The index type of the orthonormal basis: `Σ_w Fin (f(w))`. -/
abbrev OIndex (C F : Type*) [NontriviallyNormedField C] [IsUltrametricDist C] [Field F]
    [Algebra (RatFunc C) F] [Fintype (Ext C F)] : Type _ :=
  Σ w : Ext C F, Fin (inertiaDeg (gauss1 C) w.1)

/-- **G6.3** (orthonormal basis, with residues). If `e(w) = 1` for all extensions `w` of `w_{0,1}`
and `Σ_w f(w) = [F : C(X)]` (W4), then `F` has a `C(X)`-basis `b`, indexed by `Σ_w Fin f(w)`, with
`gnorm C (Σ φᵢ • bᵢ) = maxᵢ w_{0,1}(φᵢ)`; moreover `w(b_{(w', l)}) < 1` for `w ≠ w'`, and the
residues of the `b_{(w, l)}` at `w` form a `κ(w_{0,1})`-independent family. -/
theorem exists_orthonormal_basis'
    (he : ∀ w : Ext C F, ramificationIdx (RatFunc C) w.1 = 1)
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F) :
    ∃ b : Module.Basis (OIndex C F) (RatFunc C) F, (∀ φ : OIndex C F → RatFunc C,
      gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i)) ∧
      (∀ (i : OIndex C F) (w : Ext C F), w ≠ i.1 → w.1 (b i) < 1) ∧
      ∀ w : Ext C F, ∃ ℓ : Fin (inertiaDeg (gauss1 C) w.1) → w.1.valuationSubring,
        LinearIndependent (ResidueField (gauss1 C).valuationSubring)
          (fun l ↦ residue w.1.valuationSubring (ℓ l)) ∧
        ∀ l, w.1 (b ⟨w, l⟩ - ℓ l) < 1 := by
  classical
  -- bases of the residue fields and their lifts
  have hfin (w : Ext C F) : Module.Finite (ResidueField (gauss1 C).valuationSubring)
      (ResidueField w.1.valuationSubring) := finite_residueField
  let β (w : Ext C F) := Module.finBasisOfFinrankEq (ResidueField (gauss1 C).valuationSubring)
    (ResidueField w.1.valuationSubring) (n := inertiaDeg (gauss1 C) w.1) rfl
  choose ℓ hℓ using fun (w : Ext C F) (l : Fin (inertiaDeg (gauss1 C) w.1)) ↦
    residue_surjective (β w l)
  have hℓli (w : Ext C F) : LinearIndependent (ResidueField (gauss1 C).valuationSubring)
      (fun l ↦ residue w.1.valuationSubring (ℓ w l)) := by
    simpa [hℓ] using (β w).linearIndependent
  have hℓ1 (w : Ext C F) (l) : w.1 (ℓ w l) ≤ 1 := (ℓ w l).2
  -- separating elements
  have hsep (w : Ext C F) : ∃ z : F, w.1 (z - 1) < 1 ∧
      ∀ w' : Ext C F, w' ≠ w → ∀ l, w'.1 (z * ℓ w l) < 1 := by
    obtain ⟨u, hu, huS⟩ := WeakApproximation.exists_lt_one_and_one_lt
      (fun w : Ext C F ↦ w.1) w Finset.univ fun w' _ hw' ↦ incomparable he (Ne.symm hw')
    have hev : ∀ᶠ s : ℕ in Filter.atTop, ∀ w' : Ext C F, w' ≠ w →
        ∀ l, w'.1 (ℓ w l) < w'.1 u ^ s := by
      refine Filter.eventually_all.2 fun w' ↦ ?_
      by_cases hw' : w' = w
      · exact Filter.Eventually.of_forall fun _ h ↦ absurd hw' h
      refine (Filter.eventually_all.2 fun l ↦ ?_).mono fun s hs _ ↦ hs
      exact (tendsto_pow_atTop_atTop_of_one_lt
        (huS w' (Finset.mem_univ _) hw')).eventually_gt_atTop _
    obtain ⟨s, hs⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
    have hs0 : s ≠ 0 := by omega
    obtain ⟨h1, h2⟩ := WeakApproximation.valuation_inv_one_add_pow (fun w : Ext C F ↦ w.1) hu hs0
    refine ⟨(1 + u ^ s)⁻¹, h1.trans_lt (pow_lt_one₀ zero_le hu hs0), fun w' hw' l ↦ ?_⟩
    have hu' := huS w' (Finset.mem_univ _) hw'
    have hpos : 0 < w'.1 u ^ s := pow_pos (zero_lt_one.trans hu') s
    rw [map_mul, h2 w' hu', inv_mul_lt_iff₀ hpos, mul_one]
    exact hs.1 w' hw' l
  choose z hz1 hzsep using hsep
  have hz (w : Ext C F) : w.1 (z w) = 1 := by
    have : z w = (z w - 1) + 1 := by ring
    rw [this, Valuation.map_add_eq_of_lt_right, map_one]
    rw [map_one]
    exact hz1 w
  set b : OIndex C F → F := fun i ↦ z i.1 * ℓ i.1 i.2
  have hb1 (i : OIndex C F) : gnorm C (b i) ≤ 1 := gnorm_le_iff.2 fun w ↦ by
    by_cases hw : w = i.1
    · subst hw
      rw [map_mul, hz, one_mul]
      exact hℓ1 _ _
    · exact (hzsep i.1 w hw i.2).le
  -- the norm formula
  have key (φ : OIndex C F → RatFunc C) :
      gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i) := by
    refine le_antisymm ?_ ?_
    · refine (gnorm_sum_le _ _).trans (Finset.sup_le fun i _ ↦ ?_)
      rw [gnorm_smul]
      calc gauss1 C (φ i) * gnorm C (b i) ≤ gauss1 C (φ i) * 1 := by gcongr; exact hb1 i
        _ = gauss1 C (φ i) := mul_one _
        _ ≤ _ := Finset.le_sup (f := fun i ↦ gauss1 C (φ i)) (Finset.mem_univ i)
    · by_cases hall : ∀ i, φ i = 0
      · simp [hall]
      push Not at hall
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i ↦ gauss1 C (φ i))
        (by obtain ⟨i, _⟩ := hall; exact ⟨i, Finset.mem_univ i⟩)
      have hsup : (Finset.univ.sup fun i ↦ gauss1 C (φ i)) = gauss1 C (φ i₀) :=
        le_antisymm (Finset.sup_le fun i _ ↦ hi₀ i (Finset.mem_univ i))
          (Finset.le_sup (f := fun i ↦ gauss1 C (φ i)) (Finset.mem_univ i₀))
      set μ := gauss1 C (φ i₀)
      have hμ : 0 < μ := by
        obtain ⟨i, hi⟩ := hall
        exact ((Valuation.pos_iff _).2 hi).trans_le (hi₀ i (Finset.mem_univ i))
      rw [hsup]
      set w₀ := i₀.1
      -- the main part: the `w₀`-block without the separating factor
      set A := ∑ l, algebraMap (RatFunc C) F (φ ⟨w₀, l⟩) * (ℓ w₀ l : F)
      have hA : w₀.1 A = μ := by
        have := valuation_sum_eq_sup (hℓli w₀) Finset.univ (fun l ↦ φ ⟨w₀, l⟩)
        simp only [valuation_algebraMap] at this
        rw [this]
        refine le_antisymm (Finset.sup_le fun l _ ↦ hi₀ _ (Finset.mem_univ _)) ?_
        exact Finset.le_sup (f := fun l ↦ gauss1 C (φ ⟨w₀, l⟩)) (Finset.mem_univ i₀.2)
      set B := ∑ i, φ i • b i - A
      have hB : w₀.1 B < μ := by
        have hA' : A = ∑ i : OIndex C F, if i.1 = w₀ then
            algebraMap (RatFunc C) F (φ i) * (ℓ i.1 i.2 : F) else 0 := by
          rw [Fintype.sum_sigma, Finset.sum_eq_single w₀ (fun w _ hw ↦ by simp [hw])
            (by simp)]
          simp [A]
        have hsplit : B = ∑ i, (if i.1 = w₀ then
            algebraMap (RatFunc C) F (φ i) * ((z w₀ - 1) * ℓ i.1 i.2)
            else algebraMap (RatFunc C) F (φ i) * b i) := by
          simp only [B, hA', ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          split_ifs with hi
          · simp only [Algebra.smul_def, b, ← hi]
            ring
          · rw [sub_zero, Algebra.smul_def]
        rw [hsplit]
        refine Valuation.map_sum_lt _ hμ.ne' fun i _ ↦ ?_
        split_ifs with hi
        · rw [map_mul, map_mul, valuation_algebraMap, ← mul_assoc]
          calc gauss1 C (φ i) * w₀.1 (z w₀ - 1) * w₀.1 (ℓ i.1 i.2)
              ≤ gauss1 C (φ i) * w₀.1 (z w₀ - 1) := by
                refine mul_le_of_le_one_right' ?_
                rw [← hi]
                exact hℓ1 _ _
            _ < μ := by
                by_cases h0 : gauss1 C (φ i) = 0
                · rw [h0, zero_mul]
                  exact hμ
                · calc gauss1 C (φ i) * w₀.1 (z w₀ - 1) < gauss1 C (φ i) * 1 :=
                        mul_lt_mul_of_pos_left (hz1 w₀) (pos_iff_ne_zero.2 h0)
                    _ ≤ μ := by rw [mul_one]; exact hi₀ i (Finset.mem_univ i)
        · rw [map_mul, valuation_algebraMap]
          by_cases h0 : gauss1 C (φ i) = 0
          · rw [h0, zero_mul]
            exact hμ
          · calc gauss1 C (φ i) * w₀.1 (b i) < gauss1 C (φ i) * 1 :=
                  mul_lt_mul_of_pos_left (hzsep i.1 w₀ (Ne.symm hi) i.2) (pos_iff_ne_zero.2 h0)
              _ ≤ μ := by rw [mul_one]; exact hi₀ i (Finset.mem_univ i)
      have htot : ∑ i, φ i • b i = A + B := by simp [B]
      rw [← hA]
      refine le_trans (le_of_eq ?_) (le_gnorm w₀ _)
      rw [htot, Valuation.map_add_eq_of_lt_left _ (by rwa [hA])]
  -- linear independence and the basis
  have hli : LinearIndependent (RatFunc C) b := by
    rw [Fintype.linearIndependent_iff]
    intro φ hφ i
    have h := key φ
    rw [hφ, gnorm_zero] at h
    have hle := Finset.le_sup (f := fun i ↦ gauss1 C (φ i)) (Finset.mem_univ i)
    rw [← h, nonpos_iff_eq_zero, Valuation.zero_iff] at hle
    exact hle
  have hcard : Fintype.card (OIndex C F) = Module.finrank (RatFunc C) F := by
    rw [Fintype.card_sigma, ← hsum]
    simp
  have : Nonempty (OIndex C F) := by
    rw [← Fintype.card_pos_iff, hcard]
    exact Module.finrank_pos
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun φ ↦ ?_, fun i w hw ↦ ?_,
    fun w ↦ ⟨ℓ w, hℓli w, fun l ↦ ?_⟩⟩
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact key φ
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact hzsep i.1 w hw i.2
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    change w.1 (z w * ℓ w l - ℓ w l) < 1
    rw [show z w * (ℓ w l : F) - ℓ w l = (z w - 1) * ℓ w l by ring, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hz1 w) (hℓ1 w l)

/-- **G6.3** (orthonormal basis). If `e(w) = 1` for all extensions `w` of `w_{0,1}` and
`Σ_w f(w) = [F : C(X)]` (W4), then `F` has a `C(X)`-basis `b` with
`gnorm C (Σ φᵢ • bᵢ) = maxᵢ w_{0,1}(φᵢ)`. -/
theorem exists_orthonormal_basis
    (he : ∀ w : Ext C F, ramificationIdx (RatFunc C) w.1 = 1)
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F) :
    ∃ b : Module.Basis (OIndex C F) (RatFunc C) F, ∀ φ : OIndex C F → RatFunc C,
      gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i) :=
  (exists_orthonormal_basis' he hsum).imp fun _ h ↦ h.1

end Orthonormal

end GaussFibre

end SemistableReduction
