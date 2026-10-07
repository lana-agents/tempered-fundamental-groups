/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerSheet
import TemperedFundamentalGroups.SemistableReduction.NodeUpwardMain

/-!
# Laurent germs at a sheet over an annulus

Blueprint §9.10, L5(a) (the annulus analog of `DiscGerm`). Let `L / C(x)` be finite separable,
`R' = Rint c L` the integral closure of the node chart `O_C[x, c/x]` (`0 < |c| < 1`), and `P'` a
maximal ideal of `R'` over the node of **tube degree one**: at one (hence every) radius `s` of the
open segment `|c| < s < 1` exactly one extension of the Gauss point `w_{0,s}` is centred at `P'`,
and it has `e = f = 1` (a *sheet* of `L` over the annulus).

* `annVal d`: the Gauss point `w_{0,|d|}` as a disc valuation of the unit disc;
* `annFactor`, `annExt`: the factor (degree one) and the extension of `w_{0,|d|}` centred at `P'`;
* **`exists_laurent_approx`**: every `y ∈ R'` is approximated, at the sheet extensions of all
  radii simultaneously, by elements `φₙ` of the node chart (Laurent polynomials with integral
  coefficients), `annExt_d(y - φₙ) ≤ q_d^(2ⁿ)`, `q_d < 1` (traces of the idempotent iterates of a
  separating element, as in `DiscGerm.exists_germ`).
-/

open Polynomial NNReal

namespace SemistableReduction

namespace AnnulusGerm

open LocalGlobal DiscGerm DiscCount GaussTube GaussStability TubeCount FundamentalInequality
  DenseCompletion Filter Topology

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

/-- The radius `|d|` as a unit of `ℝ≥0` (normalized as in `gaussDiscVal` for the unit disc). -/
noncomputable def rad (d : C) (hd0 : d ≠ 0) : ℝ≥0ˣ :=
  Units.mk0 ‖d * 1‖₊ (nnnorm_ne_zero_iff.2 (mul_ne_zero hd0 one_ne_zero))

omit [IsUltrametricDist C] in
lemma coe_rad (d : C) (hd0 : d ≠ 0) : ((rad d hd0 : ℝ≥0ˣ) : ℝ≥0) = ‖d‖₊ := by
  simp [rad]

omit [IsUltrametricDist C] in
lemma rad_mem {c d : C} (hd0 : d ≠ 0) (hcd : ‖c‖ < ‖d‖) (hd1 : ‖d‖ < 1) :
    rad d hd0 ∈ segment c := by
  refine ⟨?_, ?_⟩ <;> rw [coe_rad]
  · exact_mod_cast hcd
  · exact_mod_cast hd1

lemma valuation_rad (d : C) (hd0 : d ≠ 0) :
    NormedField.valuation (d * 1) = ((rad d hd0 : ℝ≥0ˣ) : ℝ≥0) := by
  simp [rad, NormedField.valuation_apply]

/-- The Gauss point `w_{0,|d|}`, `0 < |d| < 1`, as a disc valuation of the unit disc. -/
noncomputable def annVal {d : C} (hd0 : d ≠ 0) (hd1 : ‖d‖ < 1) : DiscVal (0 : C) 1 :=
  gaussDiscVal one_ne_zero hd0 hd1

section Sheet

variable [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {L : Type*} [Field L] [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]

/-- Finitely many extensions of a Gauss point (as a local instance). -/
noncomputable local instance instFintypeGaussExt (r : ℝ≥0ˣ) :
    Fintype (GaussExtension (0 : C) r L) :=
  @Fintype.ofFinite _ (finite_gaussExtension 0 r)

variable {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0) (P' : Ideal (Rint c L)) [P'.IsMaximal]
  (hP' : P'.comap (algebraMap (nodeRing c) (Rint c L)) = tubeIdeal c)
  {d₀ : C} (hd₀0 : d₀ ≠ 0) (hcd₀ : ‖c‖ < ‖d₀‖) (hd₀1 : ‖d₀‖ < 1)
  (h1 : tubeDegree (rad_mem hd₀0 hcd₀ hd₀1) P' = 1)

include hp hp1 hc hc0 h1 in
/-- The tube degree is one at every radius of the open segment (in the value group). -/
lemma tubeDegree_eq_one {d : C} (hd0 : d ≠ 0) (hcd : ‖c‖ < ‖d‖) (hd1 : ‖d‖ < 1) :
    tubeDegree (rad_mem hd0 hcd hd1) P' = 1 := by
  rw [← h1]
  exact tubeDegree_eq hp hp1 hc hc0 (rad_mem hd0 hcd hd1) (rad_mem hd₀0 hcd₀ hd₀1)
    (valuation_rad d hd0) (valuation_rad d₀ hd₀0) P'

/-- The factors of the Gauss point `w_{0,|d|}`. -/
abbrev AFactor (d : C) (hd0 : d ≠ 0) : Type _ :=
  Factor (GaussField (0 : C) (rad d hd0)) (UniformSpace.Completion (GaussField (0 : C) (rad d hd0)))
    L

omit [IsAlgClosed C] [CharZero C] [Algebra.IsSeparable (RatFunc C) L] in
/-- `e · f ≥ 1`. -/
lemma one_le_ef {r : ℝ≥0ˣ} (w' : GaussExtension (0 : C) r L) :
    1 ≤ ramificationIdx (RatFunc C) w'.1 *
      inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 r) w'.1 :=
  Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (ramificationIdx_ne_zero _)
    (Nat.pos_iff_ne_zero.1 NormedTower.inertiaDeg_pos))

include hp hp1 hc hc0 h1 in
/-- **The factor centred at the sheet has degree one, and is the only one.** -/
lemma factor_of_center {d : C} (hd0 : d ≠ 0) (hcd : ‖c‖ < ‖d‖) (hd1 : ‖d‖ < 1)
    (g : AFactor (L := L) d hd0) (hg : center (rad_mem hd0 hcd hd1) (factorEquiv g) = P') :
    g.1.natDegree = 1 ∧ ∀ g' : AFactor (L := L) d hd0,
      center (rad_mem hd0 hcd hd1) (factorEquiv g') = P' → g' = g := by
  classical
  have hT := tubeDegree_eq_one hp hp1 hc hc0 P' hd₀0 hcd₀ hd₀1 h1 hd0 hcd hd1
  rw [tubeDegree] at hT
  have hdeg (g' : AFactor (L := L) d hd0) := natDegree_eq_ramificationIdx_mul_inertiaDeg hp hp1
    (valuation_rad d hd0) g'
  have hmem (g' : AFactor (L := L) d hd0)
      (hg' : center (rad_mem hd0 hcd hd1) (factorEquiv g') = P') :
      factorEquiv g' ∈ Finset.univ.filter (fun w' : GaussExtension (0 : C) (rad d hd0) L ↦
        center (rad_mem hd0 hcd hd1) w' = P') := Finset.mem_filter.2 ⟨Finset.mem_univ _, hg'⟩
  refine ⟨?_, fun g' hg' ↦ ?_⟩
  · rw [hdeg]
    have hle := Finset.single_le_sum (f := fun w' : GaussExtension (0 : C) (rad d hd0) L ↦
      ramificationIdx (RatFunc C) w'.1 *
        inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 (rad d hd0)) w'.1)
      (fun _ _ ↦ Nat.zero_le _) (hmem g hg)
    have := one_le_ef (factorEquiv g)
    omega
  · by_contra hne
    have hne' : factorEquiv g' ≠ factorEquiv g := fun h ↦ hne (factorEquiv.injective h)
    have hle := Finset.add_le_sum (f := fun w' : GaussExtension (0 : C) (rad d hd0) L ↦
      ramificationIdx (RatFunc C) w'.1 *
        inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 (rad d hd0)) w'.1)
      (fun _ _ ↦ Nat.zero_le _) (hmem g' hg') (hmem g hg) hne'
    have h₁ := one_le_ef (factorEquiv g)
    have h₂ := one_le_ef (factorEquiv g')
    omega

include hp hp1 hc hc0 hP' in
/-- Some factor of `w_{0,|d|}` is centred at the sheet. -/
lemma exists_factor_center {d : C} (hd0 : d ≠ 0) (hcd : ‖c‖ < ‖d‖) (hd1 : ‖d‖ < 1) :
    ∃ g : AFactor (L := L) d hd0, center (rad_mem hd0 hcd hd1) (factorEquiv g) = P' := by
  obtain ⟨w', hw'⟩ := exists_center_eq hp hp1 hc hc0 (rad_mem hd0 hcd hd1) (valuation_rad d hd0)
    P' hP'
  exact ⟨factorEquiv.symm w', by rw [Equiv.apply_symm_apply]; exact hw'⟩

include hp hp1 hc hc0 h1 in
/-- **Laurent approximation at the sheet** (L5(a)). Every `y ∈ R'` is approximated, at the factor
centred at the sheet of every Gauss point `w_{0,|d|}` of the open segment, by elements `φₙ` of the
node chart `O_C[x, c/x]`: `‖y - φₙ‖ ≤ q_d^(2ⁿ)` with `q_d < 1`. -/
theorem exists_laurent_approx (y : Rint c L) :
    ∃ φ : ℕ → nodeRing c, ∀ (d : C) (hd0 : d ≠ 0) (hcd : ‖c‖ < ‖d‖) (hd1 : ‖d‖ < 1),
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ g : AFactor (L := L) d hd0,
        center (rad_mem hd0 hcd hd1) (factorEquiv g) = P' → ∀ n,
          ‖toLocal g (algebraMap (RatFunc C) L (φ n : RatFunc C)) - toLocal g (y : L)‖ ≤
            q ^ (2 ^ n) := by
  classical
  -- Step 1: a separating element
  set T : Finset (Ideal (Rint c L)) :=
    (Finset.univ.image (center (rad_mem hd₀0 hcd₀ hd₀1) (F' := L))).erase P'
  obtain ⟨e, he1, heQ⟩ := exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    obtain ⟨w', -, rfl⟩ := Finset.mem_image.1 hQ
    exact ⟨center_isMaximal hc hc0 _ w', hne⟩
  have hcent : ∀ {d : C} (hd0 : d ≠ 0) (hcd : ‖c‖ < ‖d‖) (hd1 : ‖d‖ < 1)
      (w' : GaussExtension (0 : C) (rad d hd0) L),
      center (rad_mem hd0 hcd hd1) w' ≠ P' → center (rad_mem hd0 hcd hd1) w' ∈ T := by
    intro d hd0 hcd hd1 w' hne
    haveI := center_isMaximal hc hc0 (rad_mem hd0 hcd hd1) w'
    obtain ⟨w₀, hw₀⟩ := exists_center_eq hp hp1 hc hc0 (rad_mem hd₀0 hcd₀ hd₀1)
      (valuation_rad d₀ hd₀0) (center (rad_mem hd0 hcd hd1) w') (comap_center _ w')
    exact Finset.mem_erase.2 ⟨hne, Finset.mem_image.2 ⟨w₀, Finset.mem_univ _, hw₀⟩⟩
  -- Step 2: the traces of `Nⁿ(e) y` lie in the node chart
  set Nf : L → L := fun v ↦ 3 * v ^ 2 - 2 * v ^ 3
  have hεint : ∀ n, IsIntegral (nodeRing c) (Nf^[n] (e : L) * y) := by
    intro n
    have h := Idem.map_N_iterate (Rint c L).val.toRingHom e n
    have hmem : Nf^[n] (e : L) * y ∈ Rint c L := by
      rw [show Nf^[n] (e : L) = ((fun v : Rint c L ↦ 3 * v ^ 2 - 2 * v ^ 3)^[n] e : L)
        from h.symm]
      exact ((fun v : Rint c L ↦ 3 * v ^ 2 - 2 * v ^ 3)^[n] e * y).2
    exact hmem
  have hpmem : ∀ n, Algebra.trace (RatFunc C) L (Nf^[n] (e : L) * y) ∈ nodeRing c := by
    intro n
    haveI := isFractionRing_nodeRing c
    haveI := isIntegrallyClosed_nodeRing hc0 hc.le
    exact isIntegral_mem_of_isIntegrallyClosed (Algebra.isIntegral_trace (hεint n))
  refine ⟨fun n ↦ ⟨_, hpmem n⟩, fun d hd0 hcd hd1 ↦ ?_⟩
  -- Step 3: the closeness number at the radius `|d|`
  set hs := rad_mem hd0 hcd hd1
  set qq : ℝ≥0 := Finset.univ.sup fun g : AFactor (L := L) d hd0 ↦
    if center hs (factorEquiv g) = P' then ‖toLocal g (e : L) - 1‖₊ else ‖toLocal g (e : L)‖₊
  have hval (g : AFactor (L := L) d hd0) (z : L) : (factorEquiv g).1 z = ‖toLocal g z‖₊ := rfl
  have hqq1 : qq < 1 := by
    refine (Finset.sup_lt_iff zero_lt_one).2 fun g _ ↦ ?_
    split_ifs with hg
    · have : (e - 1 : Rint c L) ∈ center hs (factorEquiv g) := hg ▸ he1
      rw [GaussTube.mem_center_iff, hval] at this
      simpa using this
    · have : e ∈ center hs (factorEquiv g) := heQ _ (hcent hd0 hcd hd1 _ hg)
      rw [GaussTube.mem_center_iff, hval] at this
      exact this
  have hle (g : AFactor (L := L) d hd0) := Finset.le_sup (f := fun g : AFactor (L := L) d hd0 ↦
    if center hs (factorEquiv g) = P' then ‖toLocal g (e : L) - 1‖₊ else ‖toLocal g (e : L)‖₊)
    (Finset.mem_univ g)
  refine ⟨qq, qq.2, by exact_mod_cast hqq1, fun g hg n ↦ ?_⟩
  obtain ⟨hdeg, huniq⟩ := factor_of_center hp hp1 hc hc0 P' hd₀0 hcd₀ hd₀1 h1 hd0 hcd hd1 g hg
  have he₀ : ‖toLocal g (e : L) - 1‖ ≤ qq := by
    have := hle g
    simp only [hg, if_true] at this
    exact_mod_cast this
  have he : ∀ g' : AFactor (L := L) d hd0, g' ≠ g → ‖toLocal g' (e : L)‖ ≤ qq := by
    intro g' hg'
    have hc' : center hs (factorEquiv g') ≠ P' := fun h ↦ hg' (huniq g' h)
    have := hle g'
    simp only [hc', if_false] at this
    exact_mod_cast this
  have hy : ∀ g' : AFactor (L := L) d hd0, ‖toLocal g' (y : L)‖ ≤ 1 := by
    intro g'
    have := valuation_le_one_of_isIntegral hs (factorEquiv g') y.2
    rw [hval] at this
    exact_mod_cast this
  exact norm_trace_sub_le (annVal hd0 hd1) g hdeg (by exact_mod_cast hqq1.le) he₀ he hy n

end Sheet

end AnnulusGerm

end SemistableReduction
