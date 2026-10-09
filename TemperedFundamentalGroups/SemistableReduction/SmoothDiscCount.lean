/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothDiscBase

/-!
# The disc count at a smooth point

Blueprint §9.12, O11 (D⇒), lemma (L). Let `P'` be a smooth point (`SmoothVertex.IsDiscSmooth`) of
the normalized disc chart `R' = DRint 0 1 G` over `(𝔪_C, x)`, with unique branch `(v, Q)`, and
`u ∈ P'` an element reducing to a uniformizer at `Q` such that `x` is integral over `O_C[u]`
(`SmoothDiscBase`). In the coordinate `u` the point `P'` has disc degree one.

* `natTrailingDegree_eq_sum`: the disc count (`DiscCount.sum_natDegree_eq_natTrailingDegree`)
  computed through the branches of the outer Gauss point (`GaussTube.map_lift_eq_prod`);
* `extCoord`, `comap_coord_eq_gauss1`, `mem_zeros_extCoord`: the branch `(v, Q)` as a branch of
  the coordinate `u`; `eq_of_ker`: it is the only branch of `u` through `P'`;
* **`exists_count`**: some `e ∈ P'` has reduced characteristic polynomial over `O_C[u]` of
  trailing degree `1`.
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace SmoothDisc

open FundamentalInequality GaussStability GaussFibre PlaceNorm GaussTube DiscCount SmoothVertex
  ClassicalSmooth TubeCount DiscGerm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

lemma rootMultiplicity_finsetProd {R ι : Type*} [CommRing R] [IsDomain R] (s : Finset ι)
    (f : ι → R[X]) (hf : ∀ i ∈ s, f i ≠ 0) (a : R) :
    rootMultiplicity a (∏ i ∈ s, f i) = ∑ i ∈ s, rootMultiplicity a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, f j ≠ 0 := fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, rootMultiplicity_mul, ih hs]
    exact mul_ne_zero (hf i (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.2 hs)

lemma rootMultiplicity_zero_X_sub_C_pow {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (r : R) (n : ℕ) :
    rootMultiplicity 0 ((X - Polynomial.C r) ^ n) = if r = 0 then n else 0 := by
  split_ifs with h
  · rw [h]
    exact rootMultiplicity_X_sub_C_pow _ _
  · refine rootMultiplicity_eq_zero fun hr ↦ h ?_
    rw [IsRoot, eval_pow, eval_sub, eval_X, eval_C, zero_sub] at hr
    exact neg_eq_zero.1 (eq_zero_of_pow_eq_zero hr)

section Trailing

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

lemma mem_discIdeal_iff_placeHom {c : C} (hc : ‖c‖ < 1) {s0 : ℝ≥0ˣ} (hs : s0 ∈ segment c)
    (hdisc : IsDiscVal (0 : C) 1 (gaussRat (NormedField.valuation (K := C)) 0 s0))
    (hle : discRing (0 : C) 1 ≤ nodeRing c) (v₀ : Ext C F)
    {Q₀ : CurvePlace 𝓀 (ResidueField v₀.1.valuationSubring)}
    (hQ₀ : Q₀ ∈ zeros 𝓀 (red C (xF C F) v₀)) (f : discRing (0 : C) 1) :
    f ∈ discIdeal (0 : C) 1 ↔
      placeHom hc v₀ hQ₀ (algebraMap (nodeRing c) (Rint c F) (Subring.inclusion hle f)) = 0 := by
  rw [← mem_tubeIdeal_iff_placeHom hc hs v₀ hQ₀, mem_tubeIdeal_iff _ hs, mem_discIdeal_iff hdisc,
    Subring.coe_inclusion]

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) [Fintype (Ext C F)]
include hp hp1

open Classical in
/-- **The disc count through the branches.** For `y ∈ R' = DRint 0 1 F` and a lift `P` of its
characteristic polynomial to `O_C[x]`, the trailing degree of `P mod (𝔪_C, x)` is the number of
branches `(v, Q)` (`Q` a zero of `x̄` on `κ(v)`) with `ȳ(Q) = 0`, counted with `ord_Q x̄`. -/
theorem natTrailingDegree_eq_sum (v₀ : Ext C F)
    {Q₀ : CurvePlace 𝓀 (ResidueField v₀.1.valuationSubring)}
    (hQ₀ : Q₀ ∈ zeros 𝓀 (red C (xF C F) v₀)) (y : DRint (0 : C) 1 F)
    (P : (discRing (0 : C) 1)[X])
    (hP : P.map (discRing (0 : C) 1).subtype = normPoly (RatFunc C) (y : F)) :
    (P.map (Ideal.Quotient.mk (discIdeal (0 : C) 1))).natTrailingDegree =
      ∑ v : Ext C F, ∑ Q ∈ zeros 𝓀 (red C (xF C F) v),
        if Q.res (red C (y : F) v) = 0 then ord (red C (xF C F) v) Q else 0 := by
  classical
  obtain ⟨c', hc'0, hc'1⟩ := NormedField.exists_norm_lt_one C
  have hc'0' : c' ≠ 0 := norm_pos_iff.1 hc'0
  set c : C := c' * c'
  have hcc' : ‖c‖ < ‖c'‖ := by
    rw [norm_mul]
    exact mul_lt_of_lt_one_left hc'0 hc'1
  have hc : ‖c‖ < 1 := hcc'.trans hc'1
  set s0 : ℝ≥0ˣ := Units.mk0 ‖c'‖₊ (nnnorm_ne_zero_iff.2 hc'0')
  have hs : s0 ∈ segment c := ⟨by exact_mod_cast hcc', by exact_mod_cast hc'1⟩
  have hdisc : IsDiscVal (0 : C) 1 (gaussRat (NormedField.valuation (K := C)) 0 s0) :=
    isDiscVal_gaussRat (a := (0 : C)) one_ne_zero hc'0' (by simpa using hc'1)
  have hle : discRing (0 : C) 1 ≤ nodeRing c := by
    change polyChart _ (gaussCoord (0 : C) 1) ≤ _
    rw [SmoothVertex.gaussCoord_zero_one]
    exact polyChart_le ZariskiModel.baseRing_le_nodeChart (X_mem_nodeRing c)
  have hiff : ∀ f : discRing (0 : C) 1, f ∈ discIdeal (0 : C) 1 ↔
      ((placeHom hc v₀ hQ₀).comp (algebraMap (nodeRing c) (Rint c F)))
        (Subring.inclusion hle f) = 0 :=
    mem_discIdeal_iff_placeHom hc hs hdisc hle v₀ hQ₀
  set yN : Rint c F :=
    ⟨(y : F), ExhaustGluing.isIntegral_of_subring_le hle y.2⟩
  set PN := P.map (Subring.inclusion hle)
  have hPN : PN.map (nodeRing c).subtype = normPoly (RatFunc C) (yN : F) := by
    have h2 : PN.map (nodeRing c).subtype = P.map (discRing (0 : C) 1).subtype := by
      ext i
      simp only [PN, coeff_map, Subring.subtype_apply, Subring.coe_inclusion]
    rw [h2]
    exact hP
  have hsupp : (P.map (Ideal.Quotient.mk (discIdeal (0 : C) 1))).natTrailingDegree =
      (PN.map ((placeHom hc v₀ hQ₀).comp
        (algebraMap (nodeRing c) (Rint c F)))).natTrailingDegree := by
    unfold natTrailingDegree trailingDegree
    congr 2
    ext i
    simp only [PN, mem_support_iff, coeff_map, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    rw [hiff]
  have hne : ∀ (v : Ext C F) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) (n : ℕ),
      ((X - Polynomial.C (Q.res (red C (y : F) v))) ^ n : 𝓀[X]) ≠ 0 :=
    fun v Q n ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  rw [hsupp, map_lift_eq_prod hp hp1 hc yN PN hPN v₀ hQ₀, ← rootMultiplicity_eq_natTrailingDegree',
    rootMultiplicity_finsetProd _ _ (fun v _ ↦ Finset.prod_ne_zero_iff.2 fun Q _ ↦ hne v Q _)]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [rootMultiplicity_finsetProd _ _ (fun Q _ ↦ hne v Q _)]
  refine Finset.sum_congr rfl fun Q _ ↦ ?_
  convert rootMultiplicity_zero_X_sub_C_pow (R := 𝓀) _ _

end Trailing

section Count

variable {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

variable {u : G} (hu : Transcendental C u)

omit [FiniteDimensional (RatFunc C) G] in
lemma comap_coord_eq_gauss1 (v : Ext C G) (hu1 : v.1 u ≤ 1)
    (hr : red C u v ∉ (algebraMap 𝓀 (ResidueField v.1.valuationSubring)).range) :
    (v.1 : Valuation (Coord hu) ℝ≥0).comap (algebraMap (RatFunc C) (Coord hu)) = gauss1 C := by
  have hC : ∀ c : C, (v.1 : Valuation (Coord hu) ℝ≥0) (algebraMap C (Coord hu) c) = ‖c‖₊ :=
    fun c ↦ valuation_algebraMap_C' v c
  refine comap_eq_gauss1_of_sub (F := Coord hu) (v.1 : Valuation (Coord hu) ℝ≥0) hC
    (by rw [xF_coord']; exact hu1) fun β hβ ↦ ?_
  rw [xF_coord']
  exact valuation_sub_eq_one v hu1 hr hβ

/-- An extension of `w_{0,1}` on `G` over which `u` is residually transcendental, viewed as an
extension of the Gauss point of the coordinate `u`. -/
noncomputable def extCoord (v : Ext C G)
    (h : (v.1 : Valuation (Coord hu) ℝ≥0).comap (algebraMap (RatFunc C) (Coord hu)) = gauss1 C) :
    Ext C (Coord hu) :=
  ⟨v.1, h⟩

lemma red_not_mem_range (v : Ext C G) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    {f : G} (hf : Q.valuation (red C f v) = exp (-1)) :
    red C f v ∉ (algebraMap 𝓀 (ResidueField v.1.valuationSubring)).range := by
  have hexp : (exp (-1) : ℤᵐ⁰) < 1 := by rw [← exp_zero, exp_lt_exp]; norm_num
  rintro ⟨k₀, hk₀⟩
  rw [← hk₀] at hf
  by_cases h0 : k₀ = 0
  · rw [h0, map_zero, map_zero] at hf
    exact exp_ne_zero hf.symm
  · rw [valuation_algebraMap_eq_one Q.valuation_algebraMap_le_one h0] at hf
    exact hexp.ne' hf

variable [FiniteDimensional (RatFunc C) (Coord hu)]

omit [FiniteDimensional (RatFunc C) (Coord hu)] [IsAlgClosed C] [IsScalarTower C (RatFunc C) G]
  [FiniteDimensional (RatFunc C) G] in
lemma red_xF_extCoord (v : Ext C G)
    (h : (v.1 : Valuation (Coord hu) ℝ≥0).comap (algebraMap (RatFunc C) (Coord hu)) = gauss1 C) :
    red C (xF C (Coord hu)) (extCoord hu v h) = red C u v := by
  rw [xF_coord']
  rfl

lemma mem_zeros_extCoord (v : Ext C G) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQu : Q.valuation (red C u v) = exp (-1))
    (h : (v.1 : Valuation (Coord hu) ℝ≥0).comap (algebraMap (RatFunc C) (Coord hu)) = gauss1 C) :
    Q ∈ zeros 𝓀 (red C (xF C (Coord hu)) (extCoord hu v h)) := by
  have hexp : (exp (-1) : ℤᵐ⁰) < 1 := by rw [← exp_zero, exp_lt_exp]; norm_num
  have hredH : red C (xF C (Coord hu)) (extCoord hu v h) = red C u v := by
    rw [xF_coord']
    rfl
  have hr := red_not_mem_range v hQu
  have hne : red C u v ≠ 0 := fun h0 ↦ hr ⟨0, by rw [h0, map_zero]⟩
  rw [hredH]
  refine (mem_zeros_iff_lt_one Q hne).2 ?_
  rw [hQu]
  exact hexp

variable (hx : IsIntegral (discRing (0 : C) 1) (toCoord hu (xF C G)))

/-- **Uniqueness of the branch through `P'` in the coordinate `u`.** If `(v, Q)` is the only
branch of `x` through `P'` and `u ∈ P'` is residually transcendental at `v`, then every branch
`(v'', Q'')` of `u` whose point is `P'` is `(v, Q)`. -/
lemma eq_of_ker (v : Ext C G) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G) v))
    (hb : ∀ b : OuterBranch C G, placeIdealD b.1 b.2.2 = placeIdealD v hQ → b = ⟨v, ⟨Q, hQ⟩⟩)
    {s : DRint (0 : C) 1 G} (hsu : (s : G) = u) (hsP : s ∈ placeIdealD v hQ)
    (h : (v.1 : Valuation (Coord hu) ℝ≥0).comap (algebraMap (RatFunc C) (Coord hu)) = gauss1 C)
    (v'' : Ext C (Coord hu)) {Q'' : CurvePlace 𝓀 (ResidueField v''.1.valuationSubring)}
    (hQ'' : Q'' ∈ zeros 𝓀 (red C (xF C (Coord hu)) v''))
    (hker : RingHom.ker (psi hu hx v'' hQ'') = placeIdealD v hQ) :
    (⟨v'', Q''⟩ : Σ v' : Ext C (Coord hu), CurvePlace 𝓀 (ResidueField v'.1.valuationSubring)) =
      ⟨extCoord hu v h, Q⟩ := by
  obtain ⟨hv, hQG, hpl⟩ := branch_of_ker hu hx v hQ hsu hsP v'' hQ'' hker
  have := hb ⟨⟨v''.1, hv⟩, ⟨Q'', hQG⟩⟩ hpl
  cases this
  rfl

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
include hp hp1 hx

/-- **The count**: let `(v, Q)` be the only branch through `P' = placeIdealD v hQ`, `s ∈ P'` with
`ord_Q s̄ = 1`, `u = s` and `x` integral over `O_C[u]`. Then some `e ∈ P'` has characteristic
polynomial over `O_C[u]` whose reduction modulo `(𝔪_C, u)` has trailing degree `1`. -/
theorem exists_count (v : Ext C G) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G) v))
    (hb : ∀ b : OuterBranch C G, placeIdealD b.1 b.2.2 = placeIdealD v hQ → b = ⟨v, ⟨Q, hQ⟩⟩)
    {s : DRint (0 : C) 1 G} (hsu : (s : G) = u) (hsQ : Q.valuation (redD v s) = exp (-1)) :
    ∃ e : DRint (0 : C) 1 G, e ∈ placeIdealD v hQ ∧
      ∀ P : (discRing (0 : C) 1)[X],
        P.map (discRing (0 : C) 1).subtype = normPoly (RatFunc C) (toCoord hu (e : G)) →
          (P.map (Ideal.Quotient.mk (discIdeal (0 : C) 1))).natTrailingDegree = 1 := by
  classical
  haveI : Finite (Ext C (Coord hu)) := finite_ext hp hp1
  letI : Fintype (Ext C (Coord hu)) := Fintype.ofFinite _
  set P' := placeIdealD v hQ
  haveI : P'.IsMaximal := placeIdealD_isMaximal v hQ
  have hexp : (exp (-1) : ℤᵐ⁰) < 1 := by rw [← exp_zero, exp_lt_exp]; norm_num
  have hsP : s ∈ P' := by
    rw [mem_placeIdealD_iff]
    exact Q.res_eq_zero_of_lt_one (hsQ ▸ hexp)
  -- the separating element
  set T : Finset (Ideal (DRint (0 : C) 1 G)) := (Finset.univ.biUnion fun v'' : Ext C (Coord hu) ↦
    (zeros 𝓀 (red C (xF C (Coord hu)) v'')).attach.image fun Q'' ↦
      RingHom.ker (psi hu hx v'' Q''.2)).erase P'
  obtain ⟨e₀, he1, heQ⟩ := exists_separating P' T fun M hM ↦ by
    obtain ⟨hne, hM⟩ := Finset.mem_erase.1 hM
    obtain ⟨v'', -, hM⟩ := Finset.mem_biUnion.1 hM
    obtain ⟨Q'', -, rfl⟩ := Finset.mem_image.1 hM
    exact ⟨ker_psi_isMaximal hu hx v'' Q''.2, hne⟩
  set e : DRint (0 : C) 1 G := 1 - e₀
  have heP : e ∈ P' := by
    have := neg_mem he1
    rwa [neg_sub] at this
  have key : ∀ (v'' : Ext C (Coord hu)) {Q'' : CurvePlace 𝓀 (ResidueField v''.1.valuationSubring)}
      (hQ'' : Q'' ∈ zeros 𝓀 (red C (xF C (Coord hu)) v'')),
      psi hu hx v'' hQ'' e = 0 → RingHom.ker (psi hu hx v'' hQ'') = P' := by
    intro v'' Q'' hQ'' h0
    by_contra hne
    have hmem : RingHom.ker (psi hu hx v'' hQ'') ∈ T :=
      Finset.mem_erase.2 ⟨hne, Finset.mem_biUnion.2 ⟨v'', Finset.mem_univ _,
        Finset.mem_image.2 ⟨⟨Q'', hQ''⟩, Finset.mem_attach _ _, rfl⟩⟩⟩
    have he₀ := heQ _ hmem
    rw [RingHom.mem_ker] at he₀
    rw [map_sub, map_one, he₀, sub_zero] at h0
    exact one_ne_zero h0
  -- the branch `(v, Q)` in the coordinate `u`
  have hsle : v.1 u ≤ 1 := hsu ▸ valuation_le_one_D v s
  have hQu : Q.valuation (red C u v) = exp (-1) := by rw [← hsu, ← redD_apply]; exact hsQ
  have hvH := comap_coord_eq_gauss1 hu v hsle (red_not_mem_range v hQu)
  have hQH := mem_zeros_extCoord hu v hQu hvH
  refine ⟨e, heP, fun P hP ↦ ?_⟩
  rw [natTrailingDegree_eq_sum hp hp1 (extCoord hu v hvH) hQH (incl hu hx e) P hP,
    Finset.sum_sigma']
  rw [Finset.sum_eq_single_of_mem (⟨extCoord hu v hvH, Q⟩ : Σ v' : Ext C (Coord hu),
      CurvePlace 𝓀 (ResidueField v'.1.valuationSubring))
    (Finset.mem_sigma.2 ⟨Finset.mem_univ _, hQH⟩)]
  · have hres : Q.res (red C (toCoord hu (e : G)) (extCoord hu v hvH)) = 0 :=
      (mem_placeIdealD_iff v hQ e).1 heP
    refine (if_pos hres).trans ?_
    have h1 := valuation_x hQH
    have hval : Q.valuation (red C (xF C (Coord hu)) (extCoord hu v hvH)) = exp (-1) := by
      exact (congrArg Q.valuation (red_xF_extCoord hu v hvH)).trans hQu
    have h2 := exp_injective (h1.symm.trans hval)
    simp only [neg_inj, Nat.cast_eq_one] at h2
    exact h2
  · rintro ⟨v'', Q''⟩ hmem hne
    have hQ'' : Q'' ∈ zeros 𝓀 (red C (xF C (Coord hu)) v'') := (Finset.mem_sigma.1 hmem).2
    refine if_neg fun h0 ↦ hne ?_
    exact eq_of_ker hu hx v hQ hb hsu hsP hvH v'' hQ'' (key v'' hQ'' h0)

end Count

end SmoothDisc
end SemistableReduction
