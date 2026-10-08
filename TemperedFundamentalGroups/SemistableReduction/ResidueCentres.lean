/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CurveDivisor
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization

/-!
# Finiteness of the residue-transcendental centres of a model (O9)

Blueprint §9.12, O9. For a Zariski model `Y` of finite type over a valuation subring `O ⊆ K`
of a function field of one variable `F / K`, there are only finitely many valuation subrings `W`
of `F` with `W ∩ K = O` whose center on `Y` has residue field transcendental over `κ(O)`
(`ZariskiModel.finite_residueTranscendental_centres`). No dimension theory is used:

* `exists_isResidueTranscendental_of_mem` (residue generation): if `W ⊇ R[s]` and some element of
  `R[s]` has transcendental residue, so does some generator `t ∈ s`;
* `valuation_aeval_eq_of_isResidueTranscendental` (Gauss formula): for such `t`,
  `W(p(t)) = max_i v(p_i)`, i.e. `W` restricts to the Gauss valuation of `t` on `K(t)`
  (`comap_adjoin_eq_of_isResidueTranscendental`);
* `finite_extensions`: a valuation subring has finitely many extensions to a finite extension
  (`F / K(t)` is finite, `IsCurveFunctionField.finiteDimensional_adjoin`).
-/

open Polynomial IsLocalRing IntermediateField

namespace SemistableReduction

/-! ### Extensions of a valuation subring to a finite extension -/

/-- A vector space in which linearly independent finite sets have at most `n` elements is
finite-dimensional. -/
lemma Module.finite_of_card_le {k M : Type*} [Field k] [AddCommGroup M] [Module k M] {n : ℕ}
    (h : ∀ s : Finset M, LinearIndependent k (fun i : s ↦ (i : M)) → s.card ≤ n) :
    Module.Finite k M := by
  have hle := linearIndependent_bounded_of_finset_linearIndependent_bounded h _
    (Module.Basis.ofVectorSpaceIndex.linearIndependent k M)
  haveI : Finite (Module.Basis.ofVectorSpaceIndex k M) :=
    Cardinal.lt_aleph0_iff_finite.1 (hle.trans_lt (Cardinal.natCast_lt_aleph0))
  exact Module.Finite.of_basis (Module.Basis.ofVectorSpace k M)

/-- **Finitely many extensions.** A valuation subring of `L` has only finitely many extensions to
a finite extension `F / L`: the extension `W` is the local ring of the integral closure `D` of
`V` at the center of `W` (Prüfer, `localAt_normChart_eq`), the centers are primes of `D` over
`𝔪_V`, and `D / 𝔪_V D` is a finite-dimensional algebra over the residue field (coefficients of a
linear relation can be normalized into `V` with a unit), hence Artinian. -/
theorem finite_extensions {L F : Type*} [Field L] [Field F] [Algebra L F] [FiniteDimensional L F]
    (V : ValuationSubring L) :
    {W : ValuationSubring F | W.comap (algebraMap L F) = V}.Finite := by
  classical
  set D := normChart F V.toSubring
  have hιD : ∀ v : V, algebraMap L F v ∈ D := fun v ↦ map_le_normChart _ ⟨v, v.2, rfl⟩
  let ι : V →+* D := RingHom.codRestrict ((algebraMap L F).comp V.subtype) D hιD
  letI : Algebra V D := ι.toAlgebra
  set I : Ideal D := (maximalIdeal V).map (algebraMap V D)
  letI : Algebra (ResidueField V) (D ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hsmul : ∀ (v : V) (d : D), algebraMap (ResidueField V) (D ⧸ I) (residue V v) *
      Ideal.Quotient.mk I d = Ideal.Quotient.mk I (ι v * d) := fun v d ↦ by
    rw [map_mul]; rfl
  -- `D / 𝔪 D` is finite-dimensional over the residue field
  haveI : Module.Finite (ResidueField V) (D ⧸ I) := by
    refine Module.finite_of_card_le (n := Module.finrank L F) fun s hs ↦ ?_
    choose d hd using fun t : s ↦ Ideal.Quotient.mk_surjective (I := I) (t : D ⧸ I)
    have hli : LinearIndependent L (fun t : s ↦ ((d t : D) : F)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      by_contra! hne
      obtain ⟨i₀, hi₀⟩ := hne
      haveI : Nonempty s := ⟨i₀⟩
      obtain ⟨j, -, hj⟩ := Finset.univ.exists_max_image (fun i ↦ V.valuation (g i))
        Finset.univ_nonempty
      have hgj : g j ≠ 0 := by
        intro h0
        have := hj i₀ (Finset.mem_univ _)
        rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
        exact hi₀ this
      have hb : ∀ i, g i / g j ∈ V := fun i ↦ by
        rw [← V.valuation_le_one_iff, map_div₀]
        exact div_le_one_of_le₀ (hj i (Finset.mem_univ _)) zero_le
      set b : s → V := fun i ↦ ⟨g i / g j, hb i⟩
      have hsumD : ∑ i, ι (b i) * d i = 0 := by
        have h1 : ∑ i, algebraMap L F (g i / g j) * ((d i : D) : F) = 0 := by
          have := congrArg ((g j)⁻¹ • ·) hg
          simp only [smul_zero, Finset.smul_sum, smul_smul] at this
          simpa [Algebra.smul_def, div_eq_inv_mul] using this
        apply Subtype.ext
        simpa [ι, b] using h1
      have hsumT : ∑ i, residue V (b i) • (i : D ⧸ I) = 0 := by
        have := congrArg (Ideal.Quotient.mk I) hsumD
        rw [map_sum, map_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Algebra.smul_def, ← hd i, hsmul]
      have := (Fintype.linearIndependent_iff.1 hs) _ hsumT j
      rw [residue_eq_zero_iff] at this
      apply this
      have : b j = 1 := Subtype.ext (by simp [b, div_self hgj])
      rw [this]
      exact isUnit_one
    have := hli.fintype_card_le_finrank
    simpa using this
  haveI : IsArtinianRing (D ⧸ I) := IsArtinianRing.of_finite (ResidueField V) (D ⧸ I)
  haveI : Algebra.IsAlgebraic L F := Algebra.IsAlgebraic.of_finite L F
  set S := {W : ValuationSubring F | W.comap (algebraMap L F) = V}
  have hDW : ∀ W : S, D ≤ W.1.toSubring := fun W ↦ (normChart_le_iff _ _).2 W.2.ge
  have hIW : ∀ W : S, I ≤ centerIdeal D W.1 (hDW W) := by
    intro W
    rw [Ideal.map_le_iff_le_comap]
    intro v hv
    rw [Ideal.mem_comap, mem_centerIdeal_iff]
    by_contra hge
    have h1 : W.1.valuation (algebraMap L F v) = 1 :=
      le_antisymm ((W.1.valuation_le_one_iff _).2 (hDW W (hιD v))) (not_lt.1 hge)
    apply hv
    rw [V.valuation_eq_one_iff]
    obtain ⟨h0, -, hinv⟩ := (valuation_eq_one_iff_mem_and_inv_mem W.1).1 h1
    have hinv' : (v : L)⁻¹ ∈ W.1.comap (algebraMap L F) := by
      rw [ValuationSubring.mem_comap, map_inv₀]
      exact hinv
    rw [W.2] at hinv'
    exact (valuation_eq_one_iff_mem_and_inv_mem V).2
      ⟨fun h ↦ h0 (by rw [h, map_zero]), v.2, hinv'⟩
  let Φ : S → PrimeSpectrum (D ⧸ I) := fun W ↦
    ⟨(centerIdeal D W.1 (hDW W)).map (Ideal.Quotient.mk I),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hIW W)⟩
  have hΦ : Function.Injective Φ := by
    intro W W' h
    have hc : centerIdeal D W.1 (hDW W) = centerIdeal D W'.1 (hDW W') := by
      have := congrArg (fun P : PrimeSpectrum (D ⧸ I) ↦ P.asIdeal.comap (Ideal.Quotient.mk I)) h
      simp only [Φ, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker] at this
      rwa [sup_eq_left.2 (hIW W), sup_eq_left.2 (hIW W')] at this
    have hl : localAt D W.1 = localAt D W'.1 := by
      ext x
      simp only [mem_localAt]
      refine exists_congr fun t ↦ ⟨fun ⟨ht, h1, h2⟩ ↦ ⟨ht, ?_, h2⟩, fun ⟨ht, h1, h2⟩ ↦ ⟨ht, ?_, h2⟩⟩
      · have := (valuation_eq_one_iff_notMem_centerIdeal (hDW W) ⟨t, ht⟩).1 h1
        rw [hc] at this
        exact (valuation_eq_one_iff_notMem_centerIdeal (hDW W') ⟨t, ht⟩).2 this
      · have := (valuation_eq_one_iff_notMem_centerIdeal (hDW W') ⟨t, ht⟩).1 h1
        rw [← hc] at this
        exact (valuation_eq_one_iff_notMem_centerIdeal (hDW W) ⟨t, ht⟩).2 this
    rw [localAt_normChart_eq V W.1 W.2.ge, localAt_normChart_eq V W'.1 W'.2.ge] at hl
    exact Subtype.ext (ValuationSubring.toSubring_injective hl)
  exact Set.finite_coe_iff.1 (Finite.of_injective Φ hΦ)


/-! ### Residue-transcendental elements -/

section Residue

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {O : ValuationSubring K}
  {W : ValuationSubring F}

/-- **Gauss formula.** If `W ∩ K = O` and `t` has transcendental residue, then `W(p(t))` is the
maximum `O`-value of the coefficients of `p`: the restriction of `W` to `K(t)` is the Gauss
valuation of `t`. -/
theorem valuation_aeval_eq_of_isResidueTranscendental {t : F}
    (ht : IsResidueTranscendental O W t) {p : K[X]} (hp : p ≠ 0) :
    ∃ j, (∀ i, O.valuation (p.coeff i) ≤ O.valuation (p.coeff j)) ∧ p.coeff j ≠ 0 ∧
      W.valuation (aeval t p) = W.valuation (algebraMap K F (p.coeff j)) := by
  obtain ⟨j, -, hj⟩ := (Finset.range (p.natDegree + 1)).exists_max_image
    (fun i ↦ O.valuation (p.coeff i)) ⟨0, by simp⟩
  have hj' : ∀ i, O.valuation (p.coeff i) ≤ O.valuation (p.coeff j) := fun i ↦ by
    by_cases hi : i ≤ p.natDegree
    · exact hj i (Finset.mem_range.2 (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero]
      exact zero_le
  have hcj : p.coeff j ≠ 0 := by
    intro h0
    apply hp
    ext i
    have := hj' i
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    simpa using this
  refine ⟨j, hj', hcj, ?_⟩
  set c := p.coeff j
  have hle : ∀ i, (C c⁻¹ * p).coeff i ∈ O := fun i ↦ by
    rw [coeff_C_mul, ← O.valuation_le_one_iff, map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hj' i) zero_le
  obtain ⟨P, hP⟩ : ∃ P : O[X], P.map (algebraMap O K) = C c⁻¹ * p := by
    rw [← mem_lifts, lifts_iff_coeff_lifts]
    exact fun n ↦ ⟨⟨_, hle n⟩, rfl⟩
  have hPj : P.coeff j = 1 := Subtype.ext (by
    have := congrArg (coeff · j) hP
    simp only [coeff_map, coeff_C_mul] at this
    change (algebraMap O K) (P.coeff j) = 1
    rw [this, inv_mul_cancel₀ hcj])
  have hres : P.map (residue O) ≠ 0 := fun h ↦ by
    have := congrArg (coeff · j) h
    simp [hPj] at this
  have h1 := ht.2 P hres
  rw [hP] at h1
  have : aeval t p = algebraMap K F c * aeval t (C c⁻¹ * p) := by
    rw [map_mul, aeval_C, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hcj, map_one, one_mul]
  rw [this, map_mul, h1, mul_one]

/-- A residue-transcendental `t` is transcendental over `K`. -/
lemma transcendental_of_isResidueTranscendental {t : F}
    (ht : IsResidueTranscendental O W t) : Transcendental K t := by
  rintro ⟨p, hp, h0⟩
  obtain ⟨j, -, hcj, hv⟩ := valuation_aeval_eq_of_isResidueTranscendental ht hp
  rw [h0, map_zero, eq_comm, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap K F).injective]
    at hv
  exact hcj hv

/-- On `K`, a valuation subring `W` with `W ∩ K = O` compares values as `O` does. -/
lemma valuation_algebraMap_le_iff (hW : W.comap (algebraMap K F) = O) {c d : K} (hd : d ≠ 0) :
    W.valuation (algebraMap K F c) ≤ W.valuation (algebraMap K F d) ↔
      O.valuation c ≤ O.valuation d := by
  have hd' : W.valuation (algebraMap K F d) ≠ 0 := by simpa using hd
  have hd'' : O.valuation d ≠ 0 := by simpa using hd
  rw [← div_le_one₀ (zero_lt_iff.2 hd'), ← div_le_one₀ (zero_lt_iff.2 hd''), ← map_div₀,
    ← map_div₀, ← map_div₀, W.valuation_le_one_iff, O.valuation_le_one_iff,
    ← ValuationSubring.mem_comap, hW]

/-- Membership of `p(t) / q(t)` in `W` depends only on `O` when `t` has transcendental
residue. -/
lemma mem_of_isResidueTranscendental {W' : ValuationSubring F}
    (hW : W.comap (algebraMap K F) = O) (hW' : W'.comap (algebraMap K F) = O) {t : F}
    (ht : IsResidueTranscendental O W t) (ht' : IsResidueTranscendental O W' t) (p q : K[X])
    (h : aeval t p / aeval t q ∈ W) : aeval t p / aeval t q ∈ W' := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  obtain ⟨jp, hjp, hcp, hvp⟩ := valuation_aeval_eq_of_isResidueTranscendental ht hp
  obtain ⟨jq, hjq, hcq, hvq⟩ := valuation_aeval_eq_of_isResidueTranscendental ht hq
  obtain ⟨jp', hjp', -, hvp'⟩ := valuation_aeval_eq_of_isResidueTranscendental ht' hp
  obtain ⟨jq', hjq', hcq', hvq'⟩ := valuation_aeval_eq_of_isResidueTranscendental ht' hq
  have hq0 : W.valuation (aeval t q) ≠ 0 := by rw [hvq]; simpa using hcq
  have hq0' : W'.valuation (aeval t q) ≠ 0 := by rw [hvq']; simpa using hcq'
  rw [← W.valuation_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 hq0), hvp, hvq,
    valuation_algebraMap_le_iff hW hcq] at h
  rw [← W'.valuation_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 hq0'), hvp', hvq',
    valuation_algebraMap_le_iff hW' hcq']
  calc O.valuation (p.coeff jp') ≤ O.valuation (p.coeff jp) := hjp jp'
    _ ≤ O.valuation (q.coeff jq) := h
    _ ≤ O.valuation (q.coeff jq') := hjq' jq

/-- Two valuation subrings over `O` in which `t` has transcendental residue agree on `K(t)`. -/
theorem comap_adjoin_eq_of_isResidueTranscendental {W' : ValuationSubring F}
    (hW : W.comap (algebraMap K F) = O) (hW' : W'.comap (algebraMap K F) = O) {t : F}
    (ht : IsResidueTranscendental O W t) (ht' : IsResidueTranscendental O W' t) :
    W.comap (algebraMap K⟮t⟯ F) = W'.comap (algebraMap K⟮t⟯ F) := by
  ext y
  simp only [ValuationSubring.mem_comap]
  obtain ⟨p, q, hpq⟩ := (mem_adjoin_simple_iff K (y : F)).1 y.2
  change (y : F) ∈ W ↔ (y : F) ∈ W'
  rw [hpq]
  exact ⟨mem_of_isResidueTranscendental hW hW' ht ht' p q,
    mem_of_isResidueTranscendental hW' hW ht' ht p q⟩

/-- **Residue generation.** If `W ∩ K = O`, `R[S] ⊆ W` and some `z ∈ R[S]` has residue
transcendental over `κ(O)`, then some `s ∈ S` does (the residues of `R[S]` lie in the field
generated over `κ(O)` by the residues of `S`). -/
theorem exists_isResidueTranscendental_of_mem (hW : W.comap (algebraMap K F) = O) {S : Set F}
    (hAW : Subring.closure ((baseRing F O : Set F) ∪ S) ≤ W.toSubring) {z : F}
    (hz : z ∈ Subring.closure ((baseRing F O : Set F) ∪ S))
    (hzt : IsResidueTranscendental O W z) : ∃ s ∈ S, IsResidueTranscendental O W s := by
  letI := residueAlgebra hW
  by_contra hcon
  push Not at hcon
  set L := algebraicClosure (ResidueField O) (ResidueField W)
  let T : Subring F := (L.toSubalgebra.toSubring.comap (residue W)).map W.subtype
  have hmemT {x : F} (hx : x ∈ W) (h : residue W ⟨x, hx⟩ ∈ L) : x ∈ T :=
    ⟨⟨x, hx⟩, h, rfl⟩
  have hTmem {x : F} (h : x ∈ T) : ∃ hx : x ∈ W, residue W ⟨x, hx⟩ ∈ L := by
    obtain ⟨y, hy, rfl⟩ := h
    exact ⟨y.2, hy⟩
  have hAT : Subring.closure ((baseRing F O : Set F) ∪ S) ≤ T := by
    refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨o, ho, rfl⟩
      refine hmemT (toVal hW ⟨o, ho⟩).2 ?_
      have : residue W (toVal hW ⟨o, ho⟩) =
          algebraMap (ResidueField O) (ResidueField W) (residue O ⟨o, ho⟩) :=
        (ResidueField.map_residue (toVal hW) _).symm
      rw [show (⟨algebraMap K F o, (toVal hW ⟨o, ho⟩).2⟩ : W) = toVal hW ⟨o, ho⟩ from rfl, this]
      exact L.algebraMap_mem _
    · intro s hs
      have hsW : s ∈ W := hAW (Subring.subset_closure (Or.inr hs))
      refine hmemT hsW ?_
      rw [mem_algebraicClosure_iff]
      by_contra htr
      exact hcon s hs ((isResidueTranscendental_iff hW hsW).2 htr)
  obtain ⟨hzW, hzL⟩ := hTmem (hAT hz)
  rw [mem_algebraicClosure_iff] at hzL
  exact (isResidueTranscendental_iff hW hzW).1 hzt hzL

end Residue

/-! ### The finiteness theorem -/

namespace ZariskiModel

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {O : ValuationSubring K}

/-- **O9: finitely many residue-transcendental centres.** For a Zariski model `Y` of finite type
over `O` of a function field of one variable `F / K`, only finitely many valuation subrings `W` of
`F` with `W ∩ K = O` contain a chart of `Y` with an element of transcendental residue (these are
the valuations dominating the local rings of `Y` at the generic points of the components of the
special fibre). Each of them restricts, on `K(t)` for a generator `t` of the chart, to the Gauss
valuation of `t` (`valuation_aeval_eq_of_isResidueTranscendental`). -/
theorem finite_residueTranscendental_centres [IsCurveFunctionField K F]
    {Y : ZariskiModel (baseRing F O)} (hYf : Y.IsFiniteType) :
    {W : ValuationSubring F | W.comap (algebraMap K F) = O ∧ ∃ B ∈ Y.charts,
      B ≤ W.toSubring ∧ ∃ z ∈ B, IsResidueTranscendental O W z}.Finite := by
  choose s hs using hYf
  set T : Set F := ⋃ A : Y.charts, ((s A.1 A.2 : Finset F) : Set F)
  have hT : T.Finite := Set.finite_iUnion fun A ↦ (s A.1 A.2).finite_toSet
  have hSt : ∀ t : F, {W : ValuationSubring F | W.comap (algebraMap K F) = O ∧
      IsResidueTranscendental O W t}.Finite := by
    intro t
    by_cases hne : ∃ W₀ : ValuationSubring F, W₀.comap (algebraMap K F) = O ∧
        IsResidueTranscendental O W₀ t
    · obtain ⟨W₀, hW₀, ht₀⟩ := hne
      haveI := IsCurveFunctionField.finiteDimensional_adjoin
        (transcendental_of_isResidueTranscendental ht₀)
      refine (finite_extensions (W₀.comap (algebraMap K⟮t⟯ F))).subset fun W ⟨hW, ht⟩ ↦ ?_
      exact comap_adjoin_eq_of_isResidueTranscendental hW hW₀ ht ht₀
    · push Not at hne
      convert Set.finite_empty
      ext W
      simpa using hne W
  refine (hT.biUnion fun t _ ↦ hSt t).subset ?_
  rintro W ⟨hW, B, hB, hBW, z, hz, hzt⟩
  rw [hs B hB] at hBW hz
  obtain ⟨t, ht, htr⟩ := exists_isResidueTranscendental_of_mem hW hBW hz hzt
  exact Set.mem_biUnion (Set.mem_iUnion.2 ⟨⟨B, hB⟩, ht⟩) ⟨hW, htr⟩

end ZariskiModel

end SemistableReduction
