/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussReduction
import TemperedFundamentalGroups.SemistableReduction.RiemannRoch

/-!
# The residue curves over the Gauss point

Blueprint §9.5, G6.2 and G6.5. Let `F / C(X)` be finite, `x ∈ F` the image of `X`, and `w` an
extension of the Gauss valuation `w_{0,1}` with residue field `κ(w)`.

* `red_aeval`: the reduction of `Q(x)` (`Q ∈ O_C[X]`) is `Q̄(x̄)`; `transcendental_red_x`: `x̄` is
  transcendental over the residue field `k` of `C`;
* `isCurveFunctionField`: `κ(w)` is a function field of one variable over `k`, and
  `finrank_adjoin_red_x`: `[κ(w) : k(x̄)] = f(w | w_{0,1})`;
* **G6.5** `red_mem_of_isIntegral`: if `F` has an orthonormal `C(X)`-basis (G6.3), `f ∈ F` is
  integral over `C[X]` and `‖f‖ ≤ 1`, then `f̄ ∈ κ(w)` lies in every valuation ring of `κ(w)`
  containing `k` and `x̄` (the minimal polynomial of `f` has coefficients in `C[X]`, bounded by `1`
  for the Gauss norm by comparison with the characteristic polynomial of the matrix of `f` in an
  orthonormal basis, so it reduces to a monic polynomial over `k[x̄]`).
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal IntermediateField

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable (C F) in
/-- The coordinate `x ∈ F`, the image of `X`. -/
noncomputable abbrev xF : F := algebraMap (RatFunc C) F RatFunc.X

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma gauss1_X : gauss1 C RatFunc.X = 1 := by
  rw [← RatFunc.algebraMap_X, gauss1_algebraMap, Gauss.sup_X, Units.val_one]

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma valuation_xF (w : Ext C F) : w.1 (xF C F) = 1 := by
  rw [valuation_algebraMap, gauss1_X]

omit [IsUltrametricDist C] in
lemma aeval_xF (Q : C[X]) :
    aeval (xF C F) Q = algebraMap (RatFunc C) F (algebraMap C[X] (RatFunc C) Q) := by
  rw [aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]

lemma valuation_aeval_xF (w : Ext C F) (Q : C[X]) :
    w.1 (aeval (xF C F) Q) = Gauss.sup (NormedField.valuation (K := C)) 1 Q := by
  rw [aeval_xF, valuation_algebraMap, gauss1_algebraMap]

section Red

variable {w : Ext C F}

lemma red_algebraMap_C (c : C) (hc : ‖c‖₊ ≤ 1) :
    red C (algebraMap C F c) w = algebraMap 𝓀 (ResidueField w.1.valuationSubring)
      (residue (HenselComplete.integers C) ⟨c, by simpa using hc⟩) := by
  have := red_smul (w := w) (f := 1) c hc (by simp)
  rwa [red_one, Algebra.smul_def, mul_one, Algebra.smul_def, mul_one] at this

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma red_pow {f : F} (hf : w.1 f ≤ 1) (n : ℕ) : red C (f ^ n) w = red C f w ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, red_mul (by rw [map_pow]; exact pow_le_one₀ zero_le hf) hf, ih, pow_succ]

/-- The reduction of `Q(t)` for `Q ∈ O_C[X]` and `w(t) ≤ 1` is `Q̄(t̄)`. -/
lemma red_aeval_of_le {t : F} (ht : w.1 t ≤ 1) (P : (HenselComplete.integers C)[X]) :
    red C (aeval t (P.map (algebraMap (HenselComplete.integers C) C))) w =
      aeval (red C t w) (P.map (residue (HenselComplete.integers C))) := by
  set n := P.natDegree + 1
  have h1 : (P.map (algebraMap (HenselComplete.integers C) C)).natDegree < n :=
    Nat.lt_succ_of_le (natDegree_map_le)
  have h2 : (P.map (residue (HenselComplete.integers C))).natDegree < n :=
    Nat.lt_succ_of_le (natDegree_map_le)
  have hc (i : ℕ) : ‖((P.coeff i : HenselComplete.integers C) : C)‖₊ ≤ 1 := by
    have := (HenselComplete.mem_integers_iff _).1 (P.coeff i).2
    exact_mod_cast this
  have hti (i : ℕ) : w.1 (t ^ i) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le ht
  have hterm (i : ℕ) : w.1 ((P.map (algebraMap (HenselComplete.integers C) C)).coeff i •
      t ^ i) ≤ 1 := by
    rw [coeff_map, Algebra.smul_def, map_mul, valuation_algebraMap_C']
    exact mul_le_one' (hc i) (hti i)
  rw [aeval_eq_sum_range' h1, aeval_eq_sum_range' h2, red_sum _ _ fun i _ ↦ hterm i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_map, coeff_map, show algebraMap (HenselComplete.integers C) C (P.coeff i) =
    (P.coeff i : C) from rfl, red_smul _ (hc i) (hti i), red_pow ht]

/-- The reduction of `Q(x)` for `Q ∈ O_C[X]` is `Q̄(x̄)`. -/
lemma red_aeval (P : (HenselComplete.integers C)[X]) :
    red C (aeval (xF C F) (P.map (algebraMap (HenselComplete.integers C) C))) w =
      aeval (red C (xF C F) w) (P.map (residue (HenselComplete.integers C))) :=
  red_aeval_of_le (valuation_xF w).le P

/-- If `w(t) ≤ 1` and `Q ∈ C[X]` has Gauss norm `≤ 1`, then `Q(t)` reduces into every valuation
ring of `κ(w)` containing `k` and `t̄`. -/
lemma red_aeval_mem {t : F} (ht : w.1 t ≤ 1) {Q : C[X]}
    (hQ : Gauss.sup (NormedField.valuation (K := C)) 1 Q ≤ 1)
    (V : ValuationSubring (ResidueField w.1.valuationSubring))
    (hk : ∀ c : 𝓀, algebraMap 𝓀 _ c ∈ V) (htV : red C t w ∈ V) :
    red C (aeval t Q) w ∈ V := by
  obtain ⟨P, hP⟩ := ValuationResidue.exists_map_eq (v := NormedField.valuation (K := C)) Q
    fun i ↦ by
      simpa [Gauss.term] using (Gauss.term_le_sup (v := NormedField.valuation (K := C))
        (r := 1) Q i).trans hQ
  rw [← hP, red_aeval_of_le ht, aeval_eq_sum_range]
  exact sum_mem fun i _ ↦ by
    rw [Algebra.smul_def]
    exact mul_mem (hk _) (pow_mem htV _)

/-- `x̄` is transcendental over `k`. -/
lemma transcendental_red_x (w : Ext C F) : Transcendental 𝓀 (red C (xF C F) w) := by
  rintro ⟨Pb, hPb, hroot⟩
  obtain ⟨P, rfl⟩ := map_surjective _ (residue_surjective (R := HenselComplete.integers C)) Pb
  have hsup := Gauss.sup_one_map_eq (v := NormedField.valuation (K := C)) P hPb
  have hw : w.1 (aeval (xF C F) (P.map (algebraMap (HenselComplete.integers C) C))) = 1 := by
    rw [valuation_aeval_xF]
    exact hsup
  have := (red_eq_zero_iff hw.le).1 (by rw [red_aeval]; exact hroot)
  exact this.ne hw

end Red

section Integral

variable [Fintype (Ext C F)] [FiniteDimensional (RatFunc C) F]
  {ι : Type*} [Fintype ι] {b : Module.Basis ι (RatFunc C) F}
  (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
include hb

omit [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma gnorm_eq_sup_repr (y : F) :
    gnorm C y = Finset.univ.sup fun i ↦ gauss1 C (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr y]
  exact hb _

omit [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma gauss1_repr_le (y : F) (i : ι) : gauss1 C (b.repr y i) ≤ gnorm C y := by
  rw [gnorm_eq_sup_repr hb]
  exact Finset.le_sup (f := fun i ↦ gauss1 C (b.repr y i)) (Finset.mem_univ i)

omit [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma gnorm_basis (i : ι) : gnorm C (b i) = 1 := by
  classical
  rw [gnorm_eq_sup_repr hb, b.repr_self]
  refine le_antisymm (Finset.sup_le fun j _ ↦ ?_) ?_
  · rw [Finsupp.single_apply]
    split_ifs <;> simp
  · simpa using Finset.le_sup (f := fun j ↦ gauss1 C (Finsupp.single i (1 : RatFunc C) j))
      (Finset.mem_univ i)

omit [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma gauss1_leftMulMatrix_le [DecidableEq ι] (f : F) (i j : ι) :
    gauss1 C (Algebra.leftMulMatrix b f i j) ≤ gnorm C f := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  refine (gauss1_repr_le hb _ _).trans ((gnorm_mul_le _ _).trans ?_)
  rw [gnorm_basis hb, mul_one]

omit [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma gauss1_charpoly_coeff_le [DecidableEq ι] {f : F} (hf : gnorm C f ≤ 1) (n : ℕ) :
    gauss1 C ((Algebra.leftMulMatrix b f).charpoly.coeff n) ≤ 1 := by
  set O := (gauss1 C).valuationSubring
  let M' : Matrix ι ι O := fun i j ↦
    ⟨Algebra.leftMulMatrix b f i j, (gauss1_leftMulMatrix_le hb f i j).trans hf⟩
  have hM : Algebra.leftMulMatrix b f = M'.map (algebraMap O (RatFunc C)) := by
    ext i j
    rfl
  rw [hM, Matrix.charpoly_map, coeff_map]
  exact (M'.charpoly.coeff n).2

omit hb in
omit [IsUltrametricDist C] [Algebra C F] [IsScalarTower C (RatFunc C) F] [Fintype (Ext C F)]
  [FiniteDimensional (RatFunc C) F] in
lemma aeval_charpoly_leftMulMatrix [DecidableEq ι] (f : F) :
    aeval f (Algebra.leftMulMatrix b f).charpoly = 0 := by
  apply Algebra.leftMulMatrix_injective b
  rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
/-- The minimal polynomial of `f` with `‖f‖ ≤ 1` has Gauss-integral coefficients (Gauss's lemma:
it divides the characteristic polynomial). -/
lemma gauss1_minpoly_coeff_le {f : F} (hf : gnorm C f ≤ 1) (n : ℕ) :
    gauss1 C ((minpoly (RatFunc C) f).coeff n) ≤ 1 := by
  classical
  set χ := (Algebra.leftMulMatrix b f).charpoly
  set μ := minpoly (RatFunc C) f
  have hint : IsIntegral (RatFunc C) f := Algebra.IsIntegral.isIntegral f
  obtain ⟨ν, hν⟩ := minpoly.dvd (RatFunc C) f (aeval_charpoly_leftMulMatrix (b := b) f)
  have hχm : χ.Monic := Matrix.charpoly_monic _
  have hμm : μ.Monic := minpoly.monic hint
  have hνm : ν.Monic := hμm.of_mul_monic_left (by rw [← hν]; exact Matrix.charpoly_monic _)
  have hsupχ : Gauss.sup (gauss1 C) 1 χ ≤ 1 := Gauss.sup_le_iff.2 fun i ↦ by
    simpa [Gauss.term] using gauss1_charpoly_coeff_le hb hf i
  have hsupν : 1 ≤ Gauss.sup (gauss1 C) 1 ν := by
    simpa [Gauss.term, hνm.leadingCoeff] using
      Gauss.term_le_sup (v := gauss1 C) (r := 1) ν ν.natDegree
  have hsupμ : Gauss.sup (gauss1 C) 1 μ ≤ 1 := by
    have h := Gauss.sup_mul (v := gauss1 C) (r := 1) μ ν
    rw [← hν] at h
    calc Gauss.sup (gauss1 C) 1 μ = Gauss.sup (gauss1 C) 1 μ * 1 := (mul_one _).symm
      _ ≤ Gauss.sup (gauss1 C) 1 μ * Gauss.sup (gauss1 C) 1 ν := by gcongr
      _ = Gauss.sup (gauss1 C) 1 χ := h.symm
      _ ≤ 1 := hsupχ
  simpa [Gauss.term] using (Gauss.term_le_sup (v := gauss1 C) (r := 1) μ n).trans hsupμ

omit hb in
omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [Fintype (Ext C F)]
  [FiniteDimensional (RatFunc C) F] in
/-- An element `f`, `w(f) ≤ 1`, which is a root of a monic polynomial over `C(X)` whose
coefficients are Gauss-integral and reduce into a valuation ring `V` of `κ(w)`, reduces into
`V` (valuation rings are integrally closed). -/
lemma red_mem_of_root {w : Ext C F} {f : F} (hfw : w.1 f ≤ 1) {μ : (RatFunc C)[X]}
    (hμm : μ.Monic) (hroot : aeval f μ = 0) (hcoeff : ∀ n, gauss1 C (μ.coeff n) ≤ 1)
    (V : ValuationSubring (ResidueField w.1.valuationSubring))
    (hredc : ∀ n, red C (algebraMap (RatFunc C) F (μ.coeff n)) w ∈ V) :
    red C f w ∈ V := by
  set μF := μ.map (algebraMap (RatFunc C) F)
  obtain ⟨Pw, hPw⟩ := ValuationResidue.exists_map_eq (v := w.1) μF fun n ↦ by
    rw [coeff_map, valuation_algebraMap]
    exact hcoeff n
  have hinj : Function.Injective (algebraMap w.1.valuationSubring F) := Subtype.val_injective
  have hPwm : Pw.Monic := by
    refine Polynomial.monic_of_injective hinj ?_
    rw [hPw]
    exact hμm.map _
  have hroot' : aeval (⟨f, hfw⟩ : w.1.valuationSubring) Pw = 0 := by
    apply hinj
    rw [map_zero, ← aeval_algebraMap_apply, ← aeval_map_algebraMap F, hPw]
    change aeval f μF = 0
    rw [aeval_map_algebraMap]
    exact hroot
  set Pb := Pw.map (residue w.1.valuationSubring)
  have hPbroot : aeval (red C f w) Pb = 0 := by
    rw [red_of_le hfw, Polynomial.coe_aeval_eq_eval, eval_map, eval₂_at_apply,
      ← Polynomial.coe_aeval_eq_eval, hroot', map_zero]
  have hPbm : Pb.Monic := hPwm.map _
  have hPbV : Pb ∈ Polynomial.lifts V.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨Pb.coeff n, ?_⟩, rfl⟩
    have hc : (Pw.coeff n : F) = algebraMap (RatFunc C) F (μ.coeff n) := by
      have := congrArg (fun P ↦ P.coeff n) hPw
      simpa [μF] using this
    have hle : w.1 (Pw.coeff n : F) ≤ 1 := (Pw.coeff n).2
    have : Pb.coeff n = red C (algebraMap (RatFunc C) F (μ.coeff n)) w := by
      rw [coeff_map, ← hc, red_of_le hle]
    rw [this]
    exact hredc n
  obtain ⟨q, hqmap, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hPbV hPbm
  have hintV : IsIntegral V (red C f w) := ⟨q, hqm, by
    rw [← Polynomial.aeval_def, ← hPbroot, ← hqmap]
    exact (aeval_map_algebraMap (ResidueField w.1.valuationSubring) _ q).symm⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintV
  rw [← hy]
  exact y.2

omit hb in
omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]
  [Fintype (Ext C F)] [FiniteDimensional (RatFunc C) F] in
/-- An element integral over `C[t] ⊆ F` is a root of a monic polynomial `P(t)[T]` with
`P ∈ C[X][T]`. -/
lemma exists_monic_of_isIntegral {t f : F} (hint : IsIntegral (Algebra.adjoin C {t}) f) :
    ∃ P : C[X][X], P.Monic ∧ aeval f (P.map (aeval t : C[X] →ₐ[C] F).toRingHom) = 0 := by
  obtain ⟨p, hpm, hp⟩ := hint
  have hsurj : Function.Surjective ((aeval t : C[X] →ₐ[C] F).rangeRestrict) :=
    AlgHom.rangeRestrict_surjective _
  have hrange : Algebra.adjoin C {t} = (aeval t : C[X] →ₐ[C] F).range :=
    Algebra.adjoin_singleton_eq_range_aeval C t
  set ψ : C[X] →+* Algebra.adjoin C {t} :=
    (Subalgebra.equivOfEq _ _ hrange.symm).toRingHom.comp
      (aeval t : C[X] →ₐ[C] F).rangeRestrict.toRingHom
  have hψ : Function.Surjective ψ :=
    (Subalgebra.equivOfEq _ _ hrange.symm).surjective.comp hsurj
  have hlift : p ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n ↦ hψ _
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  refine ⟨P, hPm, ?_⟩
  have hcomp : (Algebra.adjoin C {t}).val.toRingHom.comp ψ =
      (aeval t : C[X] →ₐ[C] F).toRingHom := by
    ext Q
    · simp [ψ]
    · simp [ψ]
  rw [← hcomp, ← Polynomial.map_map, hPmap]
  simpa [aeval_def, eval₂_map] using! hp

omit hb in
omit [IsUltrametricDist C] [Fintype (Ext C F)] in
/-- If `f` is integral over `C[x]`, the coefficients of its minimal polynomial over `C(X)` are
polynomials in `X`. -/
lemma exists_minpoly_coeff_eq' {f : F} (hint : IsIntegral (Algebra.adjoin C {xF C F}) f)
    (n : ℕ) : ∃ Q : C[X], algebraMap C[X] (RatFunc C) Q = (minpoly (RatFunc C) f).coeff n := by
  obtain ⟨P, hPm, hP⟩ := exists_monic_of_isIntegral hint
  have hdvd : minpoly (RatFunc C) f ∣ P.map (algebraMap C[X] (RatFunc C)) := by
    refine minpoly.dvd (RatFunc C) f ?_
    have hmap : P.map (aeval (xF C F) : C[X] →ₐ[C] F).toRingHom =
        (P.map (algebraMap C[X] (RatFunc C))).map (algebraMap (RatFunc C) F) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext fun Q ↦ aeval_xF Q
    rw [← hP, hmap]
    exact (aeval_map_algebraMap F f _).symm
  have := Polynomial.isIntegral_coeff_of_dvd _ _ hPm
    (minpoly.monic (Algebra.IsIntegral.isIntegral f)) hdvd n
  exact IsIntegrallyClosed.isIntegral_iff.1 this

/-- **G6.5** (reductions of integral elements, chart at `0`). If `f ∈ F` is integral over
`C[x]` with `‖f‖ ≤ 1`, then `f̄ ∈ κ(w)` lies in every valuation ring of `κ(w)` containing `k`
and `x̄`. -/
theorem red_mem_of_isIntegral {f : F} (hf : gnorm C f ≤ 1)
    (hint : IsIntegral (Algebra.adjoin C {xF C F}) f) (w : Ext C F)
    (V : ValuationSubring (ResidueField w.1.valuationSubring))
    (hk : ∀ c : 𝓀, algebraMap 𝓀 _ c ∈ V) (hx : red C (xF C F) w ∈ V) :
    red C f w ∈ V := by
  have hfw : w.1 f ≤ 1 := (le_gnorm w f).trans hf
  refine red_mem_of_root hfw (minpoly.monic (Algebra.IsIntegral.isIntegral f))
    (minpoly.aeval _ f) (gauss1_minpoly_coeff_le hb hf) V fun n ↦ ?_
  obtain ⟨Q, hQ⟩ := exists_minpoly_coeff_eq' hint n
  have hQ1 : Gauss.sup (NormedField.valuation (K := C)) 1 Q ≤ 1 := by
    rw [← gauss1_algebraMap, hQ]
    exact gauss1_minpoly_coeff_le hb hf n
  rw [← hQ, ← aeval_xF]
  exact red_aeval_mem (valuation_xF w).le hQ1 V hk hx

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma nonempty_ext_of_orthonormal : Nonempty (Ext C F) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hι : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have : Module.finrank (RatFunc C) F = 0 := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_eq_zero]
    exact Module.finrank_pos.ne' this
  obtain ⟨i⟩ := hι
  classical
  have := hb (Pi.single i 1)
  have h0 : gnorm C (∑ j, (Pi.single i (1 : RatFunc C) : ι → RatFunc C) j • b j) = 0 := by
    simp [gnorm, Finset.univ_eq_empty]
  rw [h0] at this
  have hle := Finset.le_sup (f := fun j ↦ gauss1 C ((Pi.single i (1 : RatFunc C) : ι → _) j))
    (Finset.mem_univ i)
  rw [← this] at hle
  simp at hle

end Integral

section Curve

variable (w : Ext C F)

instance isScalarTower_residue :
    IsScalarTower 𝓀 (ResidueField (gauss1 C).valuationSubring)
      (ResidueField w.1.valuationSubring) := by
  refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
  obtain ⟨c, rfl⟩ := residue_surjective c
  rw [HasExtension.algebraMap_residue_eq_residue_algebraMap,
    HasExtension.algebraMap_residue_eq_residue_algebraMap,
    HasExtension.algebraMap_residue_eq_residue_algebraMap]
  congr 1
  exact Subtype.ext (IsScalarTower.algebraMap_apply C (RatFunc C) F c)

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma gauss1_mem_X : RatFunc.X ∈ (gauss1 C).valuationSubring := by
  rw [Valuation.mem_valuationSubring_iff, gauss1_X]

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
/-- The residue field of `w_{0,1}` is generated over `k` by the residue `X̄` of `X`. -/
lemma adjoin_residue_X_eq_top :
    IntermediateField.adjoin 𝓀 {residue (gauss1 C).valuationSubring ⟨RatFunc.X, gauss1_mem_X⟩} =
      ⊤ := by
  have h := adjoin_residue_gaussGen_eq_top (v := NormedField.valuation (K := C)) (a := (0 : C))
    (r := 1) (c := 1) (by simp)
  convert h using 4
  apply Subtype.ext
  simp [coe_gaussGen, gaussLin]

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma algebraMap_residue_X :
    algebraMap (ResidueField (gauss1 C).valuationSubring) (ResidueField w.1.valuationSubring)
      (residue _ ⟨RatFunc.X, gauss1_mem_X⟩) = red C (xF C F) w := by
  rw [HasExtension.algebraMap_residue_eq_residue_algebraMap, red_of_le (valuation_xF w).le]
  rfl

/-- The image of the residue field of `w_{0,1}` in `κ(w)` is `k(x̄)`. -/
lemma mem_adjoin_red_x_iff (z : ResidueField w.1.valuationSubring) :
    z ∈ 𝓀⟮red C (xF C F) w⟯ ↔ ∃ y : ResidueField (gauss1 C).valuationSubring,
      algebraMap _ (ResidueField w.1.valuationSubring) y = z := by
  set φ := IsScalarTower.toAlgHom 𝓀 (ResidueField (gauss1 C).valuationSubring)
    (ResidueField w.1.valuationSubring)
  have h := IntermediateField.adjoin_map 𝓀
    {residue (gauss1 C).valuationSubring ⟨RatFunc.X, gauss1_mem_X⟩} φ
  rw [adjoin_residue_X_eq_top, Set.image_singleton, IsScalarTower.coe_toAlgHom',
    algebraMap_residue_X] at h
  rw [← h, IntermediateField.mem_map]
  simp [φ]

/-- `[κ(w) : k(x̄)] = f(w | w_{0,1})`. -/
lemma finrank_adjoin_red_x :
    Module.finrank 𝓀⟮red C (xF C F) w⟯ (ResidueField w.1.valuationSubring) =
      inertiaDeg (gauss1 C) w.1 := by
  set E := 𝓀⟮red C (xF C F) w⟯
  have hinj : Function.Injective (algebraMap (ResidueField (gauss1 C).valuationSubring)
      (ResidueField w.1.valuationSubring)) := RingHom.injective _
  let i : ResidueField (gauss1 C).valuationSubring ≃+* E :=
    RingEquiv.ofBijective ((algebraMap _ _ : _ →+* _).codRestrict E.toSubfield
      fun y ↦ (mem_adjoin_red_x_iff w _).2 ⟨y, rfl⟩)
      ⟨fun a b h ↦ hinj (congrArg Subtype.val h), fun z ↦ by
        obtain ⟨y, hy⟩ := (mem_adjoin_red_x_iff w z).1 z.2
        exact ⟨y, Subtype.ext hy⟩⟩
  exact (Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) (by ext; rfl)).symm

/-- The residue field `κ(w)` is a function field of one variable over `k`. -/
theorem isCurveFunctionField [FiniteDimensional (RatFunc C) F] :
    IsCurveFunctionField 𝓀 (ResidueField w.1.valuationSubring) := by
  have hfin : Module.Finite (ResidueField (gauss1 C).valuationSubring)
      (ResidueField w.1.valuationSubring) := finite_residueField
  have hpos : 0 < inertiaDeg (gauss1 C) w.1 := Module.finrank_pos
  refine ⟨⟨red C (xF C F) w, transcendental_red_x w, ?_⟩⟩
  exact Module.finite_of_finrank_pos (by rw [finrank_adjoin_red_x]; exact hpos)

end Curve

end GaussFibre

end SemistableReduction
