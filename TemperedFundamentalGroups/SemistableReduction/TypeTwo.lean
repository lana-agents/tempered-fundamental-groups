/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SharpGenus
import TemperedFundamentalGroups.SemistableReduction.AbhyankarInequality

/-!
# Type-2 valuations and the genus inequality

Blueprint §9.5, G6.1 and G6.9. Let `C` be complete, algebraically closed of characteristic `0`
with residue characteristic `p`, and `F / C` a function field of one variable. A **type-2
valuation** (`TypeTwo C F`) is a real valuation of `F` extending the norm of `C` whose residue
field is transcendental over the residue field `k` of `C`.

* `valuation_aeval_eq_sup`: if `y` has transcendental residue, then `w(Q(y))` is the Gauss norm of
  `Q` (A1);
* `TypeTwo.eq_of_le`: distinct type-2 valuations have incomparable valuation rings (their values
  are norms of `C`, W3);
* **G6.1** `exists_common_coordinate`: for finitely many type-2 valuations there is `x ∈ F` with
  transcendental residue for all of them; with the coordinate `x`, `F` is finite over `C(x)` and
  all of them extend the Gauss valuation `w_{0,1}`;
* **the genus inequality** `sum_genus_le`: `Σᵢ g(κ(wᵢ)) ≤ g(F)` for distinct type-2 `wᵢ`, and
  `card_le_genus`: at most `g(F)` type-2 valuations have residue curves of positive genus.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField nonZeroDivisors

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra C F]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Gauss

/-- **A1 for polynomials**: if the residue of `y` is transcendental over `k`, then
`w(Q(y)) = ‖Q‖_{Gauss}` for all `Q ∈ C[X]`. -/
theorem valuation_aeval_eq_sup (w : Valuation F ℝ≥0)
    (hw : w.comap (algebraMap C F) = NormedField.valuation (K := C))
    [(NormedField.valuation (K := C)).HasExtension w] {y : F} (hy : w y ≤ 1)
    (htr : Transcendental 𝓀 (residue w.valuationSubring ⟨y, hy⟩)) (Q : C[X]) :
    w (aeval y Q) = Gauss.sup (NormedField.valuation (K := C)) 1 Q := by
  classical
  set r := residue w.valuationSubring ⟨y, hy⟩
  set x : ℕ → w.valuationSubring := fun i ↦ ⟨y, hy⟩ ^ i
  have hli : LinearIndependent 𝓀 fun i ↦ residue w.valuationSubring (x i) := by
    have h := (Polynomial.basisMonomials 𝓀).linearIndependent.map'
      (aeval r : 𝓀[X] →ₐ[𝓀] _).toLinearMap
      (LinearMap.ker_eq_bot.2 (transcendental_iff_injective.1 htr))
    have hfun : (fun i ↦ residue w.valuationSubring (x i)) =
        (aeval r : 𝓀[X] →ₐ[𝓀] _).toLinearMap ∘ Polynomial.basisMonomials 𝓀 := by
      ext i
      simp [x, r]
    rw [hfun]
    exact h
  have hsum := valuation_sum_eq_sup (v := NormedField.valuation (K := C)) hli
    (Finset.range (Q.natDegree + 1)) Q.coeff
  have hQ : aeval y Q = ∑ i ∈ Finset.range (Q.natDegree + 1), algebraMap C F (Q.coeff i) *
      (x i : F) := by
    rw [aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [x, Algebra.smul_def]
  rw [hQ, hsum]
  have hval (c : C) : w (algebraMap C F c) = ‖c‖₊ := by
    rw [← comap_apply, hw, NormedField.valuation_apply]
  simp only [hval]
  refine le_antisymm (Finset.sup_le fun i hi ↦ ?_) (Gauss.sup_le_iff.2 fun i ↦ ?_)
  · have := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) Q i
    simpa [Gauss.term] using this
  · simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply]
    by_cases hi : i ≤ Q.natDegree
    · exact Finset.le_sup (f := fun i ↦ ‖Q.coeff i‖₊) (Finset.mem_range.2 (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), nnnorm_zero]
      exact zero_le

end Gauss

/-- A function field of one variable has transcendence degree `≤ 1`. -/
lemma IsCurveFunctionField.trdeg_le_one {k κ : Type*} [Field k] [Field κ] [Algebra k κ]
    [IsCurveFunctionField k κ] : Algebra.trdeg k κ ≤ 1 := by
  obtain ⟨x, hx, hfin⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
    (κ := κ)
  have hb : IsTranscendenceBasis k (fun _ : Unit ↦ x) := by
    refine (AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic
      ((algebraicIndependent_singleton_iff ()).2 hx)).2 ?_
    have : Set.range (fun _ : Unit ↦ x) = {x} := Set.range_const
    rw [this, ← IntermediateField.isAlgebraic_adjoin_iff_top]
    infer_instance
  haveI := hb.isAlgebraic
  have := Algebra.IsAlgebraic.trdeg_le_cardinalMk k (Set.range fun _ : Unit ↦ x)
  rw [Set.range_const, Cardinal.mk_singleton] at this
  exact this

variable (C F) in
/-- A **type-2 valuation** of `F`: a real valuation extending the norm of `C` whose residue field
is transcendental over the residue field `k` of `C`. -/
structure TypeTwo where
  /-- The valuation. -/
  val : Valuation F ℝ≥0
  comap_eq : val.comap (algebraMap C F) = NormedField.valuation (K := C)
  transcendental : letI := hasExtension_of_comap_eq comap_eq
    Algebra.Transcendental 𝓀 (ResidueField val.valuationSubring)

namespace TypeTwo

instance (w : TypeTwo C F) : (NormedField.valuation (K := C)).HasExtension w.val :=
  hasExtension_of_comap_eq w.comap_eq

instance (w : TypeTwo C F) : Algebra.Transcendental 𝓀 (ResidueField w.val.valuationSubring) :=
  w.transcendental

lemma val_injective : Function.Injective (TypeTwo.val : TypeTwo C F → _) := by
  rintro ⟨v, -, -⟩ ⟨v', -, -⟩ (rfl : v = v')
  rfl

lemma valuation_algebraMap (w : TypeTwo C F) (c : C) : w.val (algebraMap C F c) = ‖c‖₊ := by
  rw [← comap_apply, w.comap_eq, NormedField.valuation_apply]

end TypeTwo

namespace TypeTwo

variable [IsAlgClosed C] [IsCurveFunctionField C F]

/-- The values of a type-2 valuation are norms of elements of `C` (W3). -/
lemma exists_val_eq (w : TypeTwo C F) (f : F) : ∃ c : C, w.val f = ‖c‖₊ := by
  obtain ⟨c, hc⟩ := exists_eq_of_transcendental
    (v := NormedField.valuation (K := C)) (w := w.val) IsCurveFunctionField.trdeg_le_one
    w.transcendental f
  exact ⟨c, by rw [hc, valuation_algebraMap]⟩

/-- Two type-2 valuations with comparable valuation rings are equal. -/
lemma eq_of_le {w w' : TypeTwo C F} (h : ∀ a, w.val a ≤ 1 → w'.val a ≤ 1) : w = w' := by
  refine val_injective (Valuation.ext fun f ↦ ?_)
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨c, hc⟩ := exists_val_eq w f
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero, Valuation.zero_iff] at hc
    exact hf hc
  set γ := algebraMap C F c
  have hγ : w.val γ = ‖c‖₊ := valuation_algebraMap w c
  have hγ' : w'.val γ = ‖c‖₊ := valuation_algebraMap w' c
  have hpos : (0 : ℝ≥0) < ‖c‖₊ := nnnorm_pos.2 hc0
  have h1 : w'.val (f / γ) ≤ 1 := h _ (by rw [map_div₀, hc, hγ, div_self hpos.ne'])
  have h2 : w'.val (γ / f) ≤ 1 := h _ (by rw [map_div₀, hc, hγ, div_self hpos.ne'])
  rw [map_div₀, hγ', div_le_one₀ hpos] at h1
  rw [map_div₀, hγ', div_le_one₀ ((Valuation.pos_iff _).2 hf)] at h2
  rw [hc]
  exact (le_antisymm h1 h2).symm

lemma incomparable {w w' : TypeTwo C F} (h : w ≠ w') :
    WeakApproximation.Incomparable (fun w : TypeTwo C F ↦ w.val) w w' := by
  refine ⟨?_, ?_⟩
  · by_contra! H
    exact h (eq_of_le H)
  · by_contra! H
    exact h (eq_of_le H).symm

/-- **G6.1 (common coordinate)**: for finitely many type-2 valuations there is an element whose
residue is transcendental for all of them. -/
theorem exists_common_coordinate (S : Finset (TypeTwo C F)) :
    ∃ x : F, ∀ w ∈ S, ∃ hx : w.val x ≤ 1,
      Transcendental 𝓀 (residue w.val.valuationSubring ⟨x, hx⟩) := by
  classical
  have hy (w : TypeTwo C F) : ∃ y : w.val.valuationSubring,
      Transcendental 𝓀 (residue w.val.valuationSubring y) := by
    obtain ⟨r, hr⟩ := Algebra.transcendental_def.1 w.transcendental
    obtain ⟨y, rfl⟩ := residue_surjective r
    exact ⟨y, hr⟩
  choose y hy using hy
  have hsep (w : TypeTwo C F) : ∃ z : F, w.val (z - 1) < 1 ∧
      ∀ w' ∈ S, w' ≠ w → w'.val (z * y w) < 1 := by
    obtain ⟨u, hu, huS⟩ := WeakApproximation.exists_lt_one_and_one_lt
      (fun w : TypeTwo C F ↦ w.val) w S fun w' _ hw' ↦ incomparable (Ne.symm hw')
    have hev : ∀ᶠ s : ℕ in Filter.atTop, ∀ w' ∈ S, w' ≠ w →
        w'.val (y w : F) < w'.val u ^ s := by
      refine (Filter.eventually_all_finset S).2 fun w' hw'S ↦ ?_
      by_cases hw' : w' = w
      · exact Filter.Eventually.of_forall fun _ h ↦ absurd hw' h
      refine (tendsto_pow_atTop_atTop_of_one_lt (huS w' hw'S hw')).eventually_gt_atTop _
        |>.mono fun s hs _ ↦ hs
    obtain ⟨s, hs⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
    have hs0 : s ≠ 0 := by omega
    obtain ⟨h1, h2⟩ := WeakApproximation.valuation_inv_one_add_pow
      (fun w : TypeTwo C F ↦ w.val) hu hs0
    refine ⟨(1 + u ^ s)⁻¹, h1.trans_lt (pow_lt_one₀ zero_le hu hs0), fun w' hw'S hw' ↦ ?_⟩
    have hu' := huS w' hw'S hw'
    have hpos : 0 < w'.val u ^ s := pow_pos (zero_lt_one.trans hu') s
    rw [map_mul, h2 w' hu', inv_mul_lt_iff₀ hpos, mul_one]
    exact hs.1 w' hw'S hw'
  choose z hz1 hzsep using hsep
  refine ⟨∑ w ∈ S, z w * y w, fun w hw ↦ ?_⟩
  have hdiff : w.val (∑ w ∈ S, z w * y w - y w) < 1 := by
    rw [← Finset.add_sum_erase _ _ hw]
    have : z w * (y w : F) + ∑ v ∈ S.erase w, z v * y v - y w =
        (z w - 1) * y w + ∑ v ∈ S.erase w, z v * y v := by ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul]
      exact mul_lt_one_of_lt_of_le (hz1 w) (y w).2
    · exact Valuation.map_sum_lt' _ zero_lt_one fun v hv ↦
        hzsep v w hw (Finset.ne_of_mem_erase hv).symm
  have hx : w.val (∑ w ∈ S, z w * y w) ≤ 1 := by
    have : ∑ w ∈ S, z w * (y w : F) = (∑ w ∈ S, z w * y w - y w) + y w := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le hdiff.le (y w).2)
  refine ⟨hx, ?_⟩
  have heq : residue w.val.valuationSubring ⟨_, hx⟩ = residue w.val.valuationSubring (y w) := by
    rw [← sub_eq_zero, ← _root_.map_sub]
    refine (residue_eq_zero_iff _).2 ?_
    rw [Valuation.mem_maximalIdeal_iff]
    exact hdiff
  rw [heq]
  exact hy w

end TypeTwo

section Coordinate

/-- A coordinate `x` with transcendental residue at some type-2 valuation is transcendental. -/
lemma transcendental_of_residue (w : TypeTwo C F) {x : F} (hx : w.val x ≤ 1)
    (htr : Transcendental 𝓀 (residue w.val.valuationSubring ⟨x, hx⟩)) : Transcendental C x := by
  rintro ⟨Q, hQ, h⟩
  have := valuation_aeval_eq_sup w.val w.comap_eq hx htr Q
  rw [h, map_zero, eq_comm, Gauss.sup_eq_zero_iff] at this
  exact hQ this

omit [IsUltrametricDist C] in
lemma nonZeroDivisors_le_comap_aeval {x : F} (hx : Transcendental C x) :
    C[X]⁰ ≤ F⁰.comap (aeval x : C[X] →ₐ[C] F) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (transcendental_iff_injective.1 hx)

/-- The embedding `C(X) → F`, `X ↦ x`, for `x` transcendental. -/
noncomputable def coordAlgHom {x : F} (hx : Transcendental C x) : RatFunc C →ₐ[C] F :=
  RatFunc.liftAlgHom (aeval x) (nonZeroDivisors_le_comap_aeval hx)

omit [IsUltrametricDist C] in
lemma coordAlgHom_algebraMap {x : F} (hx : Transcendental C x) (P : C[X]) :
    coordAlgHom hx (algebraMap C[X] (RatFunc C) P) = aeval x P := by
  have := RatFunc.liftAlgHom_apply_div (aeval x) (nonZeroDivisors_le_comap_aeval hx) P 1
  simpa [coordAlgHom] using this

variable [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]

/-- With a coordinate `x = xF` whose residue is transcendental at `w`, the type-2 valuation `w`
extends the Gauss valuation `w_{0,1}` of `C(x)`. -/
lemma comap_eq_gauss1 (w : TypeTwo C F) (hx : w.val (xF C F) ≤ 1)
    (htr : Transcendental 𝓀 (residue w.val.valuationSubring ⟨xF C F, hx⟩)) :
    w.val.comap (algebraMap (RatFunc C) F) = gaussRat (NormedField.valuation (K := C)) 0 1 := by
  refine Valuation.ext fun φ ↦ ?_
  rw [comap_apply, ← RatFunc.num_div_denom φ, map_div₀, map_div₀, ← aeval_xF, ← aeval_xF,
    valuation_aeval_eq_sup w.val w.comap_eq hx htr, valuation_aeval_eq_sup w.val w.comap_eq hx htr]
  change _ = gauss1 C (algebraMap C[X] (RatFunc C) φ.num / algebraMap C[X] (RatFunc C) φ.denom)
  rw [map_div₀, gauss1_algebraMap, gauss1_algebraMap]

/-- The type-2 valuation `w` as an extension of the Gauss valuation. -/
def toExt (w : TypeTwo C F) (hx : w.val (xF C F) ≤ 1)
    (htr : Transcendental 𝓀 (residue w.val.valuationSubring ⟨xF C F, hx⟩)) : Ext C F :=
  ⟨w.val, comap_eq_gauss1 w hx htr⟩

omit [IsUltrametricDist C] in
lemma finiteDimensional_of_transcendental [IsCurveFunctionField C F]
    (hx : Transcendental C (xF C F)) : FiniteDimensional (RatFunc C) F := by
  haveI := IsCurveFunctionField.finiteDimensional_adjoin hx
  refine Module.finite_of_finrank_pos ?_
  rw [← finrank_adjoin_xF]
  exact Module.finrank_pos

end Coordinate

section Genus

/-- The residue field of an algebraically closed non-archimedean field is algebraically closed. -/
instance isAlgClosed_residueField_integers [IsAlgClosed C] : IsAlgClosed 𝓀 :=
  DiscreteCoefficients.isAlgClosed_residueField

variable [IsAlgClosed C] [IsCurveFunctionField C F]

omit [IsUltrametricDist C] [IsAlgClosed C] [IsCurveFunctionField C F] in
lemma xF_coord {x : F} (hx : Transcendental C x) :
    letI : Algebra (RatFunc C) F := (coordAlgHom hx).toRingHom.toAlgebra
    xF C F = x := by
  change coordAlgHom hx RatFunc.X = x
  rw [← RatFunc.algebraMap_X, coordAlgHom_algebraMap, aeval_X]

/-- With the coordinate of `exists_common_coordinate`, the type-2 valuations become extensions of
the Gauss valuation. -/
lemma exists_toExt (S : Finset (TypeTwo C F)) (hS : S.Nonempty) :
    ∃ (x : F) (hx : Transcendental C x),
      letI : Algebra (RatFunc C) F := (coordAlgHom hx).toRingHom.toAlgebra
      ∀ w ∈ S, ∃ h : w.val (xF C F) ≤ 1,
        Transcendental 𝓀 (residue w.val.valuationSubring ⟨xF C F, h⟩) := by
  obtain ⟨x, hx⟩ := TypeTwo.exists_common_coordinate S
  obtain ⟨w₀, hw₀⟩ := hS
  obtain ⟨h₀, htr₀⟩ := hx w₀ hw₀
  have hxt := transcendental_of_residue w₀ h₀ htr₀
  refine ⟨x, hxt, fun w hw ↦ ?_⟩
  letI : Algebra (RatFunc C) F := (coordAlgHom hxt).toRingHom.toAlgebra
  have hxF : xF C F = x := xF_coord hxt
  obtain ⟨h, htr⟩ := hx w hw
  have h' : w.val (xF C F) ≤ 1 := by rw [hxF]; exact h
  refine ⟨h', ?_⟩
  have : (⟨xF C F, h'⟩ : w.val.valuationSubring) = ⟨x, h⟩ := Subtype.ext hxF
  rw [this]
  exact htr

/-- The residue curve of a type-2 valuation is a function field of one variable over `k`. -/
instance TypeTwo.isCurveFunctionField (w : TypeTwo C F) :
    IsCurveFunctionField 𝓀 (ResidueField w.val.valuationSubring) := by
  obtain ⟨x, hxt, hx⟩ := exists_toExt {w} ⟨w, Finset.mem_singleton_self w⟩
  letI : Algebra (RatFunc C) F := (coordAlgHom hxt).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom hxt).commutes c).symm
  have hxF : xF C F = x := xF_coord hxt
  haveI := finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ hxt)
  obtain ⟨h, htr⟩ := hx w (Finset.mem_singleton_self w)
  exact GaussFibre.isCurveFunctionField (toExt w h htr)

variable [CharZero C] [CompleteSpace C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
include hp hp1

/-- **The genus reduction inequality** (W6): for finitely many distinct type-2 valuations
`w₁, …, w_n` of `F`, `Σᵢ g(κ(wᵢ)) ≤ g(F)`. -/
theorem TypeTwo.sum_genus_le (S : Finset (TypeTwo C F)) :
    (∑ w ∈ S, (genus 𝓀 (ResidueField w.val.valuationSubring) : ℤ)) ≤ genus C F := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  obtain ⟨x, hxt, hx⟩ := exists_toExt S hS
  letI : Algebra (RatFunc C) F := (coordAlgHom hxt).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom hxt).commutes c).symm
  have hxF : xF C F = x := xF_coord hxt
  haveI := finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ hxt)
  haveI : Finite (Ext C F) := finite_ext hp hp1
  letI : Fintype (Ext C F) := Fintype.ofFinite _
  have hsum := sum_inertiaDeg_eq (F := F) hp hp1
  obtain ⟨b, hb⟩ := exists_orthonormal_basis ramificationIdx_eq_one hsum
  have hmain := GaussFibre.sum_genus_le hb hsum
  haveI (v : Ext C F) := GaussFibre.isCurveFunctionField v
  choose h htr using hx
  set e : S → Ext C F := fun w ↦ toExt w.1 (h w.1 w.2) (htr w.1 w.2)
  have he : Function.Injective e := fun a b hab ↦
    Subtype.ext (TypeTwo.val_injective (congrArg Subtype.val hab))
  calc (∑ w ∈ S, (genus 𝓀 (ResidueField w.val.valuationSubring) : ℤ))
      = ∑ w : S, (genus 𝓀 (ResidueField w.1.val.valuationSubring) : ℤ) :=
        (Finset.sum_coe_sort S _).symm
    _ = ∑ v ∈ Finset.univ.image e, (genus 𝓀 (ResidueField v.1.valuationSubring) : ℤ) := by
        rw [Finset.sum_image fun a _ b _ hab ↦ he hab]
        rfl
    _ ≤ ∑ v : Ext C F, (genus 𝓀 (ResidueField v.1.valuationSubring) : ℤ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦
          Int.natCast_nonneg _
    _ ≤ genus C F := hmain

/-- **Finiteness of positive-genus residue curves**: at most `g(F)` type-2 valuations of `F`
have a residue curve of positive genus. -/
theorem TypeTwo.card_le_genus (S : Finset (TypeTwo C F))
    (hS : ∀ w ∈ S, 0 < genus 𝓀 (ResidueField w.val.valuationSubring)) :
    S.card ≤ genus C F := by
  have h := TypeTwo.sum_genus_le hp hp1 S
  have h1 : (S.card : ℤ) ≤ ∑ w ∈ S, (genus 𝓀 (ResidueField w.val.valuationSubring) : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_le_sum fun w hw ↦ by exact_mod_cast hS w hw
  exact_mod_cast h1.trans h

end Genus

end SemistableReduction
