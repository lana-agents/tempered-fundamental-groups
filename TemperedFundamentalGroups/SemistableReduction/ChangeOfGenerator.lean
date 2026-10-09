/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NoImmediate

/-!
# Finite extensions of `\widehat{C(z)}` are inertially generated

Blueprint §9.4, G2 (Kuhlmann, *Elimination of ramification I*, Lemma 2.9 and §5, mixed
characteristic). Let `C` be algebraically closed of characteristic `0` with `‖p‖ < 1`, `M ⊇ C`
complete and `z ∈ M` with `‖z‖ ≤ 1`, `z̄` transcendental over the residue field `k` of `C`, and
`M` finite over the closure `\widehat{C(z)}` of `C(z)`. Then `M` is inertially generated
(`exists_isInertiallyGenerated`).

* `exists_transcendental_isSeparable`: a finitely generated extension `κ` of transcendence degree
  one of a perfect field `k` is separable over `k(t)` for some `t` (Mathlib's separably generated
  extensions);
* `isAlgebraic_adjoin_of_isAlgebraic` (exchange): if `z'` is algebraic over `C(z)` and
  transcendental over `C`, then `z` is algebraic over `C(z')` (the algebraic matroid);
* `exists_isAlgebraic_adjoin_eq_top` (Krasner): `M = \widehat{C(z)}(θ)` for some `θ` algebraic
  over `C(z)` (approximate the minimal polynomial of a primitive element by a polynomial over
  `C(z)`, continuity of roots, Krasner's lemma); hence `C(z, θ)` is dense in `M`;
* **G2** `exists_isInertiallyGenerated`: choose `z' ∈ C(z, θ)` whose residue is a separating
  element of `κ_M / k`; `C(z, θ)` is algebraic over `C(z')`, so `M` is finite over
  `\widehat{C(z')}` (a finite extension of a complete field is closed), with separable residue
  field extension; G1' shows that it is unramified.
-/

open Polynomial IsLocalRing Valuation
open scoped IntermediateField

namespace SemistableReduction

open FundamentalInequality DenseCompletion KummerNormalForm DiscreteCoefficients
  InertiallyGenerated NormedTower NoImmediate

namespace ChangeOfGenerator

section Separating

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ]

/-- **Separating transcendence element.** If `κ` is finite over `k(t₀)`, `t₀` transcendental and
`k` perfect, then `κ` is separable over `k(t)` for some transcendental `t`. -/
theorem exists_transcendental_isSeparable [PerfectField k] {t₀ : κ} (ht₀ : Transcendental k t₀)
    [FiniteDimensional k⟮t₀⟯ κ] :
    ∃ t : κ, Transcendental k t ∧ Algebra.IsSeparable k⟮t⟯ κ := by
  haveI : Algebra.EssFiniteType k k⟮t₀⟯ := by
    rw [IntermediateField.essFiniteType_iff]
    exact ⟨{t₀}, by simp⟩
  haveI : Algebra.EssFiniteType k κ := Algebra.EssFiniteType.comp k k⟮t₀⟯ κ
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k κ
  -- `{t₀}` is a transcendence basis
  have hb : IsTranscendenceBasis k (fun _ : Unit ↦ t₀) := by
    refine (AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic
      ((algebraicIndependent_singleton_iff ()).2 ht₀)).2 ?_
    have : Set.range (fun _ : Unit ↦ t₀) = {t₀} := Set.range_const
    rw [this, ← IntermediateField.isAlgebraic_adjoin_iff_top]
    infer_instance
  have hcard := hs.lift_cardinalMk_eq hb
  simp only [Cardinal.mk_fintype, Fintype.card_unit, Nat.cast_one, Cardinal.lift_one,
    Cardinal.lift_eq_one, Fintype.card_coe, Nat.cast_eq_one] at hcard
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.1 hcard
  refine ⟨t, ?_, ?_⟩
  · exact hs.1.transcendental ⟨t, Finset.mem_singleton_self t⟩
  · rwa [Finset.coe_singleton] at hsep

end Separating

section Exchange

variable {C M : Type*} [Field C] [Field M] [Algebra C M]

lemma mem_matroid_closure_iff {s : Set M} {x : M} :
    x ∈ (AlgebraicIndependent.matroid C M).closure s ↔ IsAlgebraic (Algebra.adjoin C s) x := by
  rw [AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe, Subalgebra.mem_algebraicClosure]

lemma mem_matroid_closure_singleton_iff {z x : M} :
    x ∈ (AlgebraicIndependent.matroid C M).closure {z} ↔ IsAlgebraic C⟮z⟯ x := by
  rw [mem_matroid_closure_iff, IntermediateField.isAlgebraic_adjoin_iff]

/-- **Exchange.** If `z'` is algebraic over `C(z)` and transcendental over `C`, then `z` is
algebraic over `C(z')`. -/
theorem isAlgebraic_adjoin_of_isAlgebraic {z z' : M} (h : IsAlgebraic C⟮z⟯ z')
    (h' : Transcendental C z') : IsAlgebraic C⟮z'⟯ z := by
  have h1 : z' ∈ (AlgebraicIndependent.matroid C M).closure (insert z ∅) := by
    rw [← Set.singleton_def, mem_matroid_closure_singleton_iff]
    exact h
  have h2 : z' ∉ (AlgebraicIndependent.matroid C M).closure ∅ := by
    rw [mem_matroid_closure_iff, Algebra.adjoin_empty,
      Subalgebra.isAlgebraic_bot_iff (algebraMap C M).injective]
    exact h'
  have h3 := Matroid.mem_closure_insert h2 h1
  rwa [← Set.singleton_def, mem_matroid_closure_singleton_iff] at h3

/-- **Transitivity.** If `θ` is algebraic over `C(z)` and `z` over `C(z')`, then `θ` is
algebraic over `C(z')`. -/
theorem isAlgebraic_adjoin_trans {z z' θ : M} (h : IsAlgebraic C⟮z⟯ θ)
    (h' : IsAlgebraic C⟮z'⟯ z) : IsAlgebraic C⟮z'⟯ θ := by
  rw [← mem_matroid_closure_singleton_iff] at h h' ⊢
  refine Matroid.closure_subset_closure_of_subset_closure ?_ h
  rw [Set.singleton_subset_iff]
  exact h'

end Exchange

section Krasner

variable {C M : Type*} [NontriviallyNormedField C]
  [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M] [NormedAlgebra C M]
  [CharZero C]

/-- **Krasner.** If `M` is finite over `G = \widehat{C(z)}`, then `M = G(θ)` for some `θ`
algebraic over `C(z)`: approximate the minimal polynomial `P` of a primitive element by a monic
polynomial over the dense subfield `C(z)`; a root `b` of the approximation close to a root `a`
of `P` satisfies `G(a) ⊆ G(b)` (Krasner's lemma), hence `G(a) = G(b)` by degrees. -/
theorem exists_isAlgebraic_adjoin_eq_top (z : M) [FiniteDimensional (genField C z) M] :
    ∃ θ : M, IsAlgebraic C⟮z⟯ θ ∧ (genField C z)⟮θ⟯ = ⊤ := by
  classical
  set G := genField C z
  set z' : G := ⟨z, mem_genClosure_self z⟩
  set D := IntermediateField.adjoin C {z'}
  haveI : CharZero G := charZero_of_injective_algebraMap (algebraMap C G).injective
  have hD : DenseRange (algebraMap D G) := by
    intro y
    have : y ∈ genClosure C z' := by rw [genClosure_genField_eq_top]; trivial
    have hr : Set.range (algebraMap D G) = ((D.toSubfield : Subfield G) : Set G) := by
      ext x
      exact ⟨fun ⟨d, hd⟩ ↦ hd ▸ d.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
    rw [hr]
    exact this
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element G M
  have hint : IsIntegral G θ := IsIntegral.of_finite G θ
  set P := minpoly G θ with hP
  have hPm : P.Monic := minpoly.monic hint
  have hn0 : P.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  -- the algebraic closure of `M` with the spectral norm
  let L := AlgebraicClosure M
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField M L
  letI : NormedAlgebra M L := spectralNorm.normedAlgebra M L
  haveI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra M
  letI : NormedAlgebra G L :=
    { norm_smul_le := fun g x ↦ le_of_eq (by
        rw [Algebra.smul_def, norm_mul, IsScalarTower.algebraMap_apply G M L, norm_algebraMap',
          norm_algebraMap']) }
  haveI : Algebra.IsAlgebraic G L := Algebra.IsAlgebraic.trans G M L
  set a := algebraMap M L θ
  have ha : aeval a P = 0 := by rw [aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hmin : minpoly G a = P := minpoly.algebraMap_eq (algebraMap M L).injective θ
  have haint : IsIntegral G a := ⟨P, hPm, by rw [← aeval_def]; exact ha⟩
  -- `δ`: the distance from `a` to its other conjugates
  let S : Finset L := {x ∈ (P.rootSet L).toFinset | x ≠ a}
  let δ : ℝ := if hS : S.Nonempty then Finset.min' (S.image fun x ↦ ‖a - x‖)
      (Finset.image_nonempty.mpr hS) else 1
  have norm_sub_le : ∀ a' : L, IsConjRoot G a a' → a ≠ a' → δ ≤ ‖a - a'‖ := by
    intro a' conj ne
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · apply Finset.min'_le (S.image fun x ↦ ‖a - x‖) (‖a - a'‖)
      apply Finset.mem_image_of_mem
      simp only [Finset.mem_filter, Set.mem_toFinset, S]
      rw [← hmin, ← isConjRoot_iff_mem_minpoly_rootSet (haint)]
      exact ⟨conj, ne.symm⟩
    · simp only [ne_eq, Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff,
        Set.mem_toFinset, not_not, S] at hS
      rw [isConjRoot_iff_mem_minpoly_rootSet (haint),
        hmin] at conj
      exact (ne (hS conj).symm).elim
  have δpos : δ > 0 := by
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · simp only [gt_iff_lt, Finset.lt_min'_iff, Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      rintro a' ha'
      simp only [Finset.mem_filter, Set.mem_toFinset, S] at ha'
      rw [norm_pos_iff, sub_ne_zero]
      exact ha'.2.symm
    · linarith
  have hε : (δ / (max ‖a‖ 1)) ^ P.natDegree / (P.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hD hPm hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
    hε ha hPm (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [hn0]
    · positivity
  simp only [Polynomial.mem_roots', ne_eq, Polynomial.map_eq_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map_algebraMap] at hb
  set q := g.map (algebraMap D G)
  have hqm : q.Monic := gmon.map _
  have hbint : IsIntegral G b := ⟨q, hqm, by rw [← aeval_def]; exact hb.2⟩
  -- Krasner: `a ∈ G(b)`
  have haK : a ∈ G⟮b⟯ :=
    IsKrasner.krasner (hmin ▸ (minpoly.irreducible hint).separable)
      (hmin ▸ IsAlgClosed.splits _) hbint fun a' h1 h2 ↦ lt_of_lt_of_le hab (norm_sub_le a' h1 h2)
  have hle : G⟮a⟯ ≤ G⟮b⟯ := IntermediateField.adjoin_simple_le_iff.2 haK
  have hfb : Module.finrank G G⟮b⟯ ≤ Module.finrank G G⟮a⟯ := by
    rw [IntermediateField.adjoin.finrank hbint,
      IntermediateField.adjoin.finrank (haint), hmin]
    refine (natDegree_le_of_dvd (minpoly.dvd G b hb.2) hqm.ne_zero).trans ?_
    rw [gdeg]
    exact natDegree_map_le
  haveI := IntermediateField.adjoin.finiteDimensional hbint
  have heq : G⟮a⟯ = G⟮b⟯ := IntermediateField.eq_of_le_of_finrank_le hle hfb
  -- `G(a)` is the image of `M`
  set f := IsScalarTower.toAlgHom G M L
  have himg : ∀ x : M, G⟮x⟯.map f = G⟮f x⟯ := fun x ↦ by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
  have hbmem : b ∈ f.fieldRange := by
    rw [AlgHom.fieldRange_eq_map, ← hθ, himg θ]
    change b ∈ G⟮a⟯
    rw [heq]
    exact IntermediateField.mem_adjoin_simple_self G b
  obtain ⟨θ', rfl⟩ := hbmem
  refine ⟨θ', ?_, ?_⟩
  · -- `θ'` is algebraic over `C(z)`
    have hq0 : aeval θ' q = 0 := by
      apply (algebraMap M L).injective
      rw [map_zero, ← aeval_algebraMap_apply]
      exact hb.2
    have hmemz : ∀ d : D, ((d : G) : M) ∈ C⟮z⟯ := by
      intro d
      have hmap : D.map G.val = C⟮z⟯ := by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
        rfl
      rw [← hmap]
      exact ⟨d, d.2, rfl⟩
    let φ : D →+* C⟮z⟯ := RingHom.codRestrict ((algebraMap G M).comp (algebraMap D G)) C⟮z⟯ hmemz
    refine ⟨g.map φ, (gmon.map φ).ne_zero, ?_⟩
    rw [aeval_def, eval₂_map]
    rw [aeval_def, eval₂_map] at hq0
    exact hq0
  · apply IntermediateField.map_injective f
    rw [himg θ', ← hθ, himg θ]
    exact heq.symm

end Krasner

section Main

universe u

local notation "κ" X => ResidueField (HenselComplete.integers X)

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {M : Type u} [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra C M]

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [IsUltrametricDist M] [CompleteSpace M] in
/-- An element algebraic over `C(z')` is integral over `\widehat{C(z')}`. -/
lemma isIntegral_genField_of_isAlgebraic {z' x : M} (hx : IsAlgebraic C⟮z'⟯ x) :
    IsIntegral (genField C z') x := by
  let ψ : C⟮z'⟯ →+* genField C z' := RingHom.codRestrict (algebraMap C⟮z'⟯ M) (genField C z')
    fun y ↦ Subfield.le_topologicalClosure _ y.2
  obtain ⟨q, hq0, hq⟩ := hx
  refine IsAlgebraic.isIntegral ⟨q.map ψ, (Polynomial.map_ne_zero_iff ψ.injective).2 hq0, ?_⟩
  rw [aeval_def, eval₂_map]
  rw [aeval_def] at hq
  exact hq

include hp hp1

/-- **G2.** Let `M ⊇ C` be complete and `z ∈ M` with `‖z‖ ≤ 1`, `z̄` transcendental over the
residue field of `C` and `M` finite over the closure `\widehat{C(z)}` of `C(z)`. Then `M` is
inertially generated. -/
theorem exists_isInertiallyGenerated {z : M} (hz : ‖z‖ ≤ 1)
    (htr : Transcendental (κ C) (rd z)) [FiniteDimensional (genClosure C z) M] :
    ∃ z' : M, IsInertiallyGenerated C z' := by
  set G := genField C z
  haveI : FiniteDimensional G M := (finite_genField_iff z).2 inferInstance
  -- a separating element of the residue field
  haveI : IsAlgClosed (κ C) := isAlgClosed_residueField
  haveI : FiniteDimensional (κ C)⟮rd z⟯ (κ M) := by
    have h1 : Module.Finite (κ G) (κ M) :=
      finite_residueField (v := NormedField.valuation (K := G))
        (w := NormedField.valuation (K := M))
    have h2 := (finite_residue_genField_iff z).1 h1
    rw [residueSubfield_genClosure hz htr] at h2
    exact h2
  obtain ⟨t, htt, hsep⟩ := exists_transcendental_isSeparable htr
  obtain ⟨y₀, rfl⟩ := residue_surjective t
  -- Krasner: `M = G(θ)` with `θ` algebraic over `C(z)`
  obtain ⟨θ, hθalg, hθtop⟩ := exists_isAlgebraic_adjoin_eq_top (C := C) z
  -- `F = C(z, θ)` is dense in `M`
  set F := IntermediateField.adjoin C ({z, θ} : Set M) with hFdef
  have hdense : ∀ x : M, x ∈ closure (F : Set M) := by
    set S := F.toSubfield.topologicalClosure
    have hzF : (C⟮z⟯ : Set M) ⊆ F := IntermediateField.adjoin.mono C _ _ (by simp)
    have hGS : ∀ g : G, algebraMap G M g ∈ S := fun g ↦ closure_mono hzF g.2
    let S' := S.toIntermediateField hGS
    have hθS : θ ∈ S' :=
      Subfield.le_topologicalClosure _ (IntermediateField.subset_adjoin C _ (by simp))
    have htop : S' = ⊤ := by
      rw [eq_top_iff, ← hθtop]
      exact IntermediateField.adjoin_simple_le_iff.2 hθS
    intro x
    have : x ∈ S' := htop ▸ trivial
    exact this
  -- `z' ∈ F` close to the lift `y₀` of the separating element
  obtain ⟨z', hz'F, hdist⟩ := Metric.mem_closure_iff.1 (hdense y₀) 1 one_pos
  have hy01 : ‖(y₀ : M)‖ ≤ 1 := HenselComplete.norm_le_one y₀
  rw [dist_eq_norm] at hdist
  have hz'1 : ‖z'‖ ≤ 1 := by
    have : z' = (y₀ : M) + (z' - y₀) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hy01 (by rw [norm_sub_rev]; exact hdist.le))
  have hrd : rd z' = residue (HenselComplete.integers M) y₀ := by
    rw [← rd_coe]
    exact rd_eq_of_norm_sub_lt_one hz'1 hy01 (by rwa [norm_sub_rev])
  have htr' : Transcendental (κ C) (rd z') := hrd ▸ htt
  -- `F` is algebraic over `C(z')`
  have hz'C : Transcendental C z' := by
    intro halg
    haveI := IntermediateField.adjoin.finiteDimensional halg.isIntegral
    have hbot := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic C⟮z'⟯
    have hmem : z' ∈ (⊥ : IntermediateField C M) :=
      hbot ▸ IntermediateField.mem_adjoin_simple_self C z'
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hmem
    have hc1 : ‖c‖ ≤ 1 := by rw [← norm_algebraMap' M c, hc]; exact hz'1
    apply htr'
    rw [← hc, rd_algebraMap' hc1]
    exact isAlgebraic_algebraMap (rd c)
  have hFalg : ∀ x ∈ F, IsAlgebraic C⟮z⟯ x := by
    intro x hx
    have hF : F = (IntermediateField.adjoin C⟮z⟯ {θ}).restrictScalars C := by
      rw [IntermediateField.adjoin_adjoin_left, Set.singleton_union]
    haveI := IntermediateField.adjoin.finiteDimensional hθalg.isIntegral
    rw [hF] at hx
    have := Algebra.IsAlgebraic.isAlgebraic (R := C⟮z⟯)
      (⟨x, hx⟩ : IntermediateField.adjoin C⟮z⟯ {θ})
    exact this.algebraMap
  have hzalg : IsAlgebraic C⟮z'⟯ z := isAlgebraic_adjoin_of_isAlgebraic (hFalg z' hz'F) hz'C
  have hθalg' : IsAlgebraic C⟮z'⟯ θ := isAlgebraic_adjoin_trans hθalg hzalg
  -- `M` is finite over `L₁ = \widehat{C(z')}`
  set L₁ := genField C z'
  set E₁ := IntermediateField.adjoin L₁ ({z, θ} : Set M)
  haveI : FiniteDimensional L₁ E₁ := IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
    rcases hx with rfl | rfl
    · exact isIntegral_genField_of_isAlgebraic hzalg
    · exact isIntegral_genField_of_isAlgebraic hθalg'
  have hE₁closed : IsClosed (E₁ : Set M) := by
    haveI : CompleteSpace E₁ := FiniteDimensional.complete L₁ E₁
    exact (completeSpace_coe_iff_isComplete.1 this).isClosed
  have hFE : (F : Set M) ⊆ E₁ := by
    have : F ≤ E₁.restrictScalars C := by
      rw [IntermediateField.adjoin_le_iff]
      exact IntermediateField.subset_adjoin L₁ _
    exact this
  have hE₁top : E₁ = ⊤ := eq_top_iff.2 fun x _ ↦ closure_minimal hFE hE₁closed (hdense x)
  haveI : FiniteDimensional L₁ M := by
    have : FiniteDimensional L₁ (⊤ : IntermediateField L₁ M) := hE₁top ▸ inferInstance
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  -- conclusion by G1'
  have hxG := isGaussComplete_genField hz'1 htr'
  haveI : Algebra.IsSeparable (κ L₁) (κ M) := by
    rw [isSeparable_residue_genField_iff, residueSubfield_genClosure hz'1 htr', hrd]
    exact hsep
  have hf := inertiaDeg_eq_finrank_of_isSeparable hp hp1 hxG (B := M)
  refine ⟨z', hz'1, htr', (finite_genField_iff z').1 inferInstance,
    (finite_residue_genField_iff z').1 finite_residueField,
    (isSeparable_residue_genField_iff z').1 inferInstance, ?_⟩
  rw [← finrank_genField, ← inertiaDeg_genField, hf]

end Main

end ChangeOfGenerator

end SemistableReduction
