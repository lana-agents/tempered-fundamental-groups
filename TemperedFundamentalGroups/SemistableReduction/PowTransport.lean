/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerBase

/-!
# Transport of smooth points along `x = t ^ E`

Blueprint §9.12 O6.1f(ii). Let `σ = powHom E : C(X) → C(X)`, `X ↦ X ^ E`. The Gauss values satisfy
`w_{0,r} ∘ σ = w_{0,r^E}` (`gaussRat_powHom`), and a valuation `μ` of `C(X)` with `μ ∘ σ = w_{0,1}`
is `w_{0,1}` (`eq_gauss1_of_comap_powHom`). For a field with two `C(X)`-structures related by `σ`
(`PowData`: `alg₁ = e ∘ alg₂ ∘ σ`), the normalized vertex charts coincide, extensions of `w_{0,1}`,
residue fields, branches and place ideals correspond, and smooth points over the residue point are
transported (`PowData.isDiscSmooth_comap`).
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal

namespace SemistableReduction

namespace ClassicalSmooth

open GaussFibre PlaceNorm

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

section Pow

variable (C) in
/-- `X ↦ X ^ E` on `C(X)`. -/
noncomputable def powHom (E : ℕ) (hE : 0 < E) : RatFunc C →ₐ[C] RatFunc C :=
  coordAlgHom (C := C) (F := RatFunc C) (x := RatFunc.X ^ E) (by
    intro halg
    have : IsAlgebraic C (RatFunc.X : RatFunc C) :=
      (halg.of_pow hE)
    exact RatFunc.transcendental_X this)

variable {E : ℕ} (hE : 0 < E)

omit [IsUltrametricDist C] in
lemma powHom_X : powHom C E hE RatFunc.X = RatFunc.X ^ E := coordAlgHom_X _

omit [IsUltrametricDist C] in
lemma powHom_algebraMap (p : C[X]) :
    powHom C E hE (algebraMap C[X] (RatFunc C) p) =
      algebraMap C[X] (RatFunc C) (p.comp (X ^ E)) := by
  rw [powHom, coordAlgHom_algebraMap, comp_eq_aeval, ← aeval_algebraMap_apply, map_pow,
    RatFunc.algebraMap_X]

include hE in
omit [IsUltrametricDist C] in
lemma gaussSup_X_pow_sub_C {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)
    (r : Γ₀ˣ) (b : C) : Gauss.sup v r (X ^ E - Polynomial.C b) = max (v b) ((r : Γ₀) ^ E) := by
  have hE0 : E ≠ 0 := hE.ne'
  apply le_antisymm
  · refine Gauss.sup_le_iff.2 fun i ↦ ?_
    rcases eq_or_ne i 0 with rfl | hi0
    · simp [Gauss.term, coeff_X_pow, Ne.symm hE0]
    rcases eq_or_ne i E with rfl | hiE
    · simp [Gauss.term, coeff_X_pow, coeff_C, hE0]
    · simp [Gauss.term, coeff_X_pow, coeff_C, hi0, hiE]
  · refine max_le ?_ ?_
    · have := Gauss.term_le_sup (v := v) (r := r) (X ^ E - Polynomial.C b) 0
      simpa [Gauss.term, coeff_X_pow, Ne.symm hE0] using this
    · have := Gauss.term_le_sup (v := v) (r := r) (X ^ E - Polynomial.C b) E
      simpa [Gauss.term, coeff_X_pow, coeff_C, hE0] using this

variable [IsAlgClosed C]

/-- `w_{0,r} ∘ σ = w_{0,r^E}`. -/
lemma gaussRat_powHom (r : ℝ≥0ˣ) :
    (gaussRat (NormedField.valuation (K := C)) 0 r).comap (powHom C E hE).toRingHom =
      gaussRat (NormedField.valuation (K := C)) 0 (r ^ E) := by
  refine valuation_ratFunc_ext_of_linear (fun c ↦ ?_) fun b ↦ ?_
  · simp only [comap_apply]
    change gaussRat _ 0 r (powHom C E hE (algebraMap C (RatFunc C) c)) = _
    rw [AlgHom.commutes, gaussRat_algebraMap_C, gaussRat_algebraMap_C]
  · simp only [comap_apply]
    change gaussRat _ 0 r (powHom C E hE (algebraMap C[X] (RatFunc C) (X - Polynomial.C b))) = _
    rw [powHom_algebraMap, gaussRat_algebraMap, gaussRat_algebraMap, gauss_X_sub_C, gauss_apply,
      taylor_zero, sub_comp, X_comp, C_comp, gaussSup_X_pow_sub_C hE, zero_sub,
      Valuation.map_neg, Units.val_pow_eq_pow_val]

/-- **A valuation over `w_{0,1}` along `σ` is `w_{0,1}`.** -/
lemma eq_gauss1_of_comap_powHom {μ : Valuation (RatFunc C) ℝ≥0}
    (hμ : μ.comap (powHom C E hE).toRingHom = gauss1 C) : μ = gauss1 C := by
  have hσ : ∀ φ, μ (powHom C E hE φ) = gauss1 C φ := fun φ ↦ by
    rw [← hμ]; rfl
  have hX : μ RatFunc.X = 1 := by
    have h := hσ RatFunc.X
    rw [powHom_X, map_pow, gauss1_X] at h
    exact (pow_eq_one_iff_of_nonneg zero_le hE.ne').1 h
  refine valuation_ratFunc_ext_of_linear (fun c ↦ ?_) fun b ↦ ?_
  · rw [← AlgHom.commutes (powHom C E hE) c, hσ, AlgHom.commutes]
  -- the factorization of `X ^ E - b ^ E`
  set m : ℝ≥0 := max ‖b‖₊ 1 with hm
  have hm0 : 0 < m := lt_of_lt_of_le one_pos (le_max_right _ _)
  set p : C[X] := X ^ E - Polynomial.C (b ^ E)
  have hpm : p.Monic := monic_X_pow_sub_C _ hE.ne'
  have hpdeg : p.natDegree = E := natDegree_X_pow_sub_C
  have hroots : Multiset.card p.roots = E := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hpdeg]
  have hprod : (p.roots.map fun r ↦ X - Polynomial.C r).prod = p :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm (by rw [hroots, hpdeg])
  have hle : ∀ r ∈ p.roots, μ (algebraMap C[X] (RatFunc C) (X - Polynomial.C r)) ≤ m := by
    intro r hr
    have hrE : r ^ E = b ^ E := by
      have := (mem_roots hpm.ne_zero).1 hr
      simpa [p, sub_eq_zero] using this
    have hrb : ‖r‖₊ = ‖b‖₊ := by
      have := congrArg nnnorm hrE
      rw [nnnorm_pow, nnnorm_pow] at this
      exact (pow_left_inj₀ zero_le zero_le hE.ne').1 this
    rw [_root_.map_sub, RatFunc.algebraMap_X]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [hX]; exact le_max_right _ _
    · rw [show (algebraMap C[X] (RatFunc C)) (Polynomial.C r) = algebraMap C (RatFunc C) r by
          rw [IsScalarTower.algebraMap_apply C C[X] (RatFunc C)]; rfl,
        ← AlgHom.commutes (powHom C E hE) r, hσ, gauss1_algebraMap_C, hrb]
      exact le_max_left _ _
  have htot : μ (algebraMap C[X] (RatFunc C) p) = m ^ E := by
    have : algebraMap C[X] (RatFunc C) p =
        powHom C E hE (algebraMap C[X] (RatFunc C) (X - Polynomial.C (b ^ E))) := by
      rw [powHom_algebraMap, sub_comp, X_comp, C_comp]
    rw [this, hσ, gauss1_algebraMap, sub_eq_add_neg, ← C_neg, Gauss.sup_X_add_C, Valuation.map_neg,
      NormedField.valuation_apply, nnnorm_pow, Units.val_one, hm,
      Monotone.map_max (pow_left_mono E), one_pow]
  have hgb : gauss1 C (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) = m := by
    rw [gauss1_algebraMap, sub_eq_add_neg, ← C_neg, Gauss.sup_X_add_C, Valuation.map_neg,
      NormedField.valuation_apply, Units.val_one]
  rw [hgb]
  have hb : b ∈ p.roots := (mem_roots hpm.ne_zero).2 (by simp [p])
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hb
  have hprodμ : μ (algebraMap C[X] (RatFunc C) p) =
      μ (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) *
        (rest.map fun r ↦ μ (algebraMap C[X] (RatFunc C) (X - Polynomial.C r))).prod := by
    conv_lhs => rw [← hprod, hrest]
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, map_mul, map_multiset_prod,
      map_multiset_prod μ, Multiset.map_map, Multiset.map_map]
    rfl
  have hcard : Multiset.card rest = E - 1 := by
    rw [← hroots, hrest, Multiset.card_cons]; rfl
  have hrestle : (rest.map fun r ↦ μ (algebraMap C[X] (RatFunc C) (X - Polynomial.C r))).prod ≤
      m ^ (E - 1) := by
    rw [← hcard, ← Multiset.card_map (fun r ↦ μ (algebraMap C[X] (RatFunc C) (X - Polynomial.C r)))]
    refine Multiset.prod_le_pow_card _ _ fun x hx ↦ ?_
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    exact hle r (by rw [hrest]; exact Multiset.mem_cons_of_mem hr)
  refine le_antisymm (hle b hb) (not_lt.1 fun hlt ↦ ?_)
  have : μ (algebraMap C[X] (RatFunc C) p) < m ^ E := by
    rw [hprodμ]
    calc _ ≤ μ (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) * m ^ (E - 1) :=
          mul_le_mul_right hrestle _
      _ < m * m ^ (E - 1) := mul_lt_mul_of_pos_right hlt (pow_pos hm0 _)
      _ = m ^ E := by rw [← pow_succ', Nat.sub_add_cancel hE]
  exact absurd htot this.ne

end Pow

section Data

variable [IsAlgClosed C]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable (C) in
/-- **Transport data along `x = t ^ E`**: `e : G₂ ≃+* G₁` with `alg₁ = e ∘ alg₂ ∘ σ`. -/
structure PowData (G₁ G₂ : Type*) [Field G₁] [Field G₂] [Algebra (RatFunc C) G₁]
    [Algebra (RatFunc C) G₂] where
  /-- The exponent. -/
  E : ℕ
  hE : 0 < E
  /-- The identification of the fields. -/
  e : G₂ ≃+* G₁
  he : ∀ φ, e (algebraMap (RatFunc C) G₂ (powHom C E hE φ)) = algebraMap (RatFunc C) G₁ φ

namespace PowData

variable {G₁ G₂ : Type*} [Field G₁] [Field G₂] [Algebra (RatFunc C) G₁] [Algebra (RatFunc C) G₂]
  (d : PowData C G₁ G₂)

lemma gauss1_powHom (φ : RatFunc C) : gauss1 C (powHom C d.E d.hE φ) = gauss1 C φ := by
  have := congrArg (fun w : Valuation (RatFunc C) ℝ≥0 ↦ w φ) (gaussRat_powHom d.hE (C := C) 1)
  simpa using this

/-- Transport of extensions of `w_{0,1}` from `G₂` to `G₁`. -/
noncomputable def extMap (v : Ext C G₂) : Ext C G₁ :=
  ⟨v.1.comap d.e.symm.toRingHom, Valuation.ext fun φ ↦ by
    change v.1 (d.e.symm (algebraMap (RatFunc C) G₁ φ)) = gauss1 C φ
    rw [← d.he, RingEquiv.symm_apply_apply, valuation_algebraMap, d.gauss1_powHom]⟩

/-- Transport of extensions of `w_{0,1}` from `G₁` to `G₂`. -/
noncomputable def extMap' (w : Ext C G₁) : Ext C G₂ :=
  ⟨w.1.comap d.e.toRingHom, eq_gauss1_of_comap_powHom d.hE (Valuation.ext fun φ ↦ by
    change w.1 (d.e (algebraMap (RatFunc C) G₂ (powHom C d.E d.hE φ))) = gauss1 C φ
    rw [d.he, valuation_algebraMap])⟩

lemma extMap_apply (v : Ext C G₂) (f : G₂) : (d.extMap v).1 (d.e f) = v.1 f := by
  change v.1 (d.e.symm (d.e f)) = _
  rw [RingEquiv.symm_apply_apply]

lemma extMap'_apply (w : Ext C G₁) (f : G₂) : (d.extMap' w).1 f = w.1 (d.e f) := rfl

lemma extMap_extMap' (w : Ext C G₁) : d.extMap (d.extMap' w) = w :=
  Subtype.ext (Valuation.ext fun f ↦ by
    change w.1 (d.e (d.e.symm f)) = w.1 f
    rw [RingEquiv.apply_symm_apply])

lemma extMap'_extMap (v : Ext C G₂) : d.extMap' (d.extMap v) = v :=
  Subtype.ext (Valuation.ext fun f ↦ by
    change v.1 (d.e.symm (d.e f)) = v.1 f
    rw [RingEquiv.symm_apply_apply])

/-- Transport of valuation rings. -/
def intMap (v : Ext C G₂) : v.1.valuationSubring ≃+* (d.extMap v).1.valuationSubring where
  toFun f := ⟨d.e f, by
    change (d.extMap v).1 (d.e f) ≤ 1
    rw [d.extMap_apply]; exact f.2⟩
  invFun f := ⟨d.e.symm f, by
    change v.1 (d.e.symm f) ≤ 1
    rw [← d.extMap_apply v, RingEquiv.apply_symm_apply]; exact f.2⟩
  left_inv f := Subtype.ext (d.e.symm_apply_apply _)
  right_inv f := Subtype.ext (d.e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul d.e _ _)
  map_add' _ _ := Subtype.ext (map_add d.e _ _)

/-- Transport of valuation rings, backwards. -/
def intMap' (w : Ext C G₁) : w.1.valuationSubring ≃+* (d.extMap' w).1.valuationSubring where
  toFun f := ⟨d.e.symm f, by
    change w.1 (d.e (d.e.symm f)) ≤ 1
    rw [RingEquiv.apply_symm_apply]; exact f.2⟩
  invFun f := ⟨d.e f, f.2⟩
  left_inv f := Subtype.ext (d.e.apply_symm_apply _)
  right_inv f := Subtype.ext (d.e.symm_apply_apply _)
  map_mul' _ _ := Subtype.ext (map_mul d.e.symm _ _)
  map_add' _ _ := Subtype.ext (map_add d.e.symm _ _)

/-- Transport of residue fields. -/
noncomputable def κmap (v : Ext C G₂) :
    ResidueField v.1.valuationSubring ≃+* ResidueField (d.extMap v).1.valuationSubring :=
  ResidueField.mapEquiv (d.intMap v)

/-- Transport of residue fields, backwards. -/
noncomputable def κmap' (w : Ext C G₁) :
    ResidueField w.1.valuationSubring ≃+* ResidueField (d.extMap' w).1.valuationSubring :=
  ResidueField.mapEquiv (d.intMap' w)

lemma red_map (v : Ext C G₂) (f : G₂) : red C (d.e f) (d.extMap v) = d.κmap v (red C f v) := by
  by_cases h : v.1 f ≤ 1
  · have h' : (d.extMap v).1 (d.e f) ≤ 1 := by rw [d.extMap_apply]; exact h
    rw [red_of_le h, red_of_le h', κmap, ResidueField.mapEquiv_apply, ResidueField.map_residue]
    rfl
  · have h' : ¬ (d.extMap v).1 (d.e f) ≤ 1 := by rw [d.extMap_apply]; exact h
    unfold red
    rw [dif_neg h, dif_neg h', map_zero]

lemma red_map' (w : Ext C G₁) (f : G₁) :
    red C (d.e.symm f) (d.extMap' w) = d.κmap' w (red C f w) := by
  have hv : (d.extMap' w).1 (d.e.symm f) = w.1 f := by
    rw [extMap'_apply, RingEquiv.apply_symm_apply]
  by_cases h : w.1 f ≤ 1
  · have h' : (d.extMap' w).1 (d.e.symm f) ≤ 1 := by rw [hv]; exact h
    rw [red_of_le h, red_of_le h', κmap', ResidueField.mapEquiv_apply, ResidueField.map_residue]
    rfl
  · have h' : ¬ (d.extMap' w).1 (d.e.symm f) ≤ 1 := by rw [hv]; exact h
    unfold red
    rw [dif_neg h, dif_neg h', map_zero]

section Constants

variable [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

omit [IsUltrametricDist
  C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma e_algebraMap_C (c : C) : d.e (algebraMap C G₂ c) = algebraMap C G₁ c := by
  rw [IsScalarTower.algebraMap_apply C (RatFunc C) G₂, ← AlgHom.commutes (powHom C d.E d.hE) c,
    d.he, ← IsScalarTower.algebraMap_apply]

omit [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma κmap_algebraMap (v : Ext C G₂) (k : 𝓀) :
    d.κmap v (algebraMap 𝓀 _ k) = algebraMap 𝓀 _ k := by
  obtain ⟨o, rfl⟩ := residue_surjective k
  have ho : ‖(o : C)‖₊ ≤ 1 := by exact_mod_cast HenselComplete.norm_le_one o
  rw [← red_algebraMap_C (w := v) _ ho, ← d.red_map, d.e_algebraMap_C, red_algebraMap_C _ ho]

omit [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma κmap'_algebraMap (w : Ext C G₁) (k : 𝓀) :
    d.κmap' w (algebraMap 𝓀 _ k) = algebraMap 𝓀 _ k := by
  obtain ⟨o, rfl⟩ := residue_surjective k
  have ho : ‖(o : C)‖₊ ≤ 1 := by exact_mod_cast HenselComplete.norm_le_one o
  have he' : d.e.symm (algebraMap C G₁ o) = algebraMap C G₂ o := by
    rw [RingEquiv.symm_apply_eq, d.e_algebraMap_C]
  rw [← red_algebraMap_C (w := w) _ ho, ← d.red_map', he', red_algebraMap_C _ ho]

/-- Transport of places. -/
noncomputable def placeMap (v : Ext C G₂)
    (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) :
    CurvePlace 𝓀 (ResidueField (d.extMap v).1.valuationSubring) where
  V := Q.V.comap (d.κmap v).symm.toRingHom
  algebraMap_mem c := by
    change (d.κmap v).symm (algebraMap 𝓀 _ c) ∈ Q.V
    rw [(RingEquiv.symm_apply_eq _).2 (d.κmap_algebraMap v c).symm]
    exact Q.algebraMap_mem _
  ne_top h := Q.ne_top (by
    ext z
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    have : d.κmap v z ∈ Q.V.comap (d.κmap v).symm.toRingHom := h ▸ trivial
    simpa using this)

/-- Transport of places, backwards. -/
noncomputable def placeMap' (w : Ext C G₁)
    (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)) :
    CurvePlace 𝓀 (ResidueField (d.extMap' w).1.valuationSubring) where
  V := Q.V.comap (d.κmap' w).symm.toRingHom
  algebraMap_mem c := by
    change (d.κmap' w).symm (algebraMap 𝓀 _ c) ∈ Q.V
    rw [(RingEquiv.symm_apply_eq _).2 (d.κmap'_algebraMap w c).symm]
    exact Q.algebraMap_mem _
  ne_top h := Q.ne_top (by
    ext z
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    have : d.κmap' w z ∈ Q.V.comap (d.κmap' w).symm.toRingHom := h ▸ trivial
    simpa using this)

omit [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma mem_placeMap {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    {z : ResidueField v.1.valuationSubring} : d.κmap v z ∈ (d.placeMap v Q).V ↔ z ∈ Q.V := by
  change (d.κmap v).symm (d.κmap v z) ∈ Q.V ↔ _
  rw [RingEquiv.symm_apply_apply]

omit [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma mem_placeMap' {w : Ext C G₁} {Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)}
    {z : ResidueField w.1.valuationSubring} : d.κmap' w z ∈ (d.placeMap' w Q).V ↔ z ∈ Q.V := by
  change (d.κmap' w).symm (d.κmap' w z) ∈ Q.V ↔ _
  rw [RingEquiv.symm_apply_apply]

lemma res_map_eq_zero_iff {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    {z : ResidueField v.1.valuationSubring} (hz : z ∈ Q.V) :
    (d.placeMap v Q).res (d.κmap v z) = 0 ↔ Q.res z = 0 := by
  rw [CurvePlace.res_eq_zero_iff _ ((d.mem_placeMap).2 hz), CurvePlace.res_eq_zero_iff _ hz,
    CurvePlace.valuation_lt_one_iff, CurvePlace.valuation_lt_one_iff,
    S8A.Transport.Data.valuation_lt_one_iff', S8A.Transport.Data.valuation_lt_one_iff',
    d.mem_placeMap, ← map_inv₀, d.mem_placeMap, Ne, (d.κmap v).map_eq_zero_iff]

/-- `z ^ E ∈ V` forces `z ∈ V` in a valuation subring. -/
lemma mem_of_pow_mem {K : Type*} [Field K] (V : ValuationSubring K) {z : K} {n : ℕ} (hn : 0 < n)
    (h : z ^ n ∈ V) : z ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le hn.ne').1 h

omit [IsAlgClosed
  C] [Algebra C
  G₁] [Algebra C
  G₂] [IsScalarTower C (RatFunc C)
  G₁] [IsScalarTower C (RatFunc C)
  G₂] [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
omit [IsUltrametricDist C] in
lemma xF_eq : xF C G₁ = d.e (xF C G₂ ^ d.E) := by
  rw [xF, ← d.he, powHom_X, map_pow]

lemma mem_zeros_map {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G₂) v)) :
    d.placeMap v Q ∈ zeros 𝓀 (red C (xF C G₁) (d.extMap v)) := by
  rw [mem_zeros] at hQ ⊢
  have hX1 : v.1 (xF C G₂) ≤ 1 := by rw [xF, valuation_algebraMap, gauss1_X]
  rw [d.xF_eq, d.red_map, red_pow hX1, ← map_inv₀, d.mem_placeMap, ← inv_pow]
  exact fun h ↦ hQ (mem_of_pow_mem _ d.hE h)

lemma mem_zeros_map' {w : Ext C G₁} {Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G₁) w)) :
    d.placeMap' w Q ∈ zeros 𝓀 (red C (xF C G₂) (d.extMap' w)) := by
  rw [mem_zeros] at hQ ⊢
  have hX1 : (d.extMap' w).1 (xF C G₂) ≤ 1 := by rw [xF, valuation_algebraMap, gauss1_X]
  intro hmem
  apply hQ
  have h1 : (red C (xF C G₂) (d.extMap' w) ^ d.E)⁻¹ ∈ (d.placeMap' w Q).V := by
    rw [← inv_pow]; exact pow_mem hmem _
  rw [← red_pow hX1, show xF C G₂ ^ d.E = d.e.symm (xF C G₁) by
    rw [d.xF_eq, RingEquiv.symm_apply_apply], d.red_map', ← map_inv₀, d.mem_placeMap'] at h1
  exact h1

/-- Transport of branches. -/
noncomputable def brMap (b : GaussTube.OuterBranch C G₂) : GaussTube.OuterBranch C G₁ :=
  ⟨d.extMap b.1, d.placeMap b.1 b.2.1, d.mem_zeros_map b.2.2⟩

/-- Transport of branches, backwards. -/
noncomputable def brMap' (b : GaussTube.OuterBranch C G₁) : GaussTube.OuterBranch C G₂ :=
  ⟨d.extMap' b.1, d.placeMap' b.1 b.2.1, d.mem_zeros_map' b.2.2⟩

lemma brMap_brMap' (b : GaussTube.OuterBranch C G₁) : d.brMap (d.brMap' b) = b := by
  refine S8A.Transport.outerBranch_ext (d.extMap_extMap' b.1) fun f _ ↦ ?_
  obtain ⟨w, Q, hQ⟩ := b
  change red C f (d.extMap (d.extMap' w)) ∈ (d.placeMap _ (d.placeMap' w Q)).V ↔
    red C f w ∈ Q.V
  rw [← d.e.apply_symm_apply f, d.red_map, d.mem_placeMap, d.red_map', d.mem_placeMap',
    RingEquiv.apply_symm_apply]

end Constants

section Charts

open DiscCount SmoothVertex

omit [IsAlgClosed C] in
lemma powHom_mem_discRing {φ : RatFunc C} (hφ : φ ∈ discRing (0 : C) 1) :
    powHom C d.E d.hE φ ∈ discRing (0 : C) 1 := by
  obtain ⟨Q, hQ, rfl⟩ := mem_discRing_iff.1 hφ
  refine mem_discRing_iff.2 ⟨Q.comp (X ^ d.E), ClassicalSmooth.gaussSup_le_one fun i ↦ ?_,
    (powHom_algebraMap d.hE Q).symm⟩
  rw [← expand_eq_comp_X_pow, coeff_expand d.hE]
  split_ifs
  · have := (Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) Q (i / d.E)).trans hQ
    rw [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply] at this
    exact_mod_cast this
  · simp

/-- `σ` on the vertex chart. -/
noncomputable def chartHom : discRing (0 : C) 1 →+* discRing (0 : C) 1 where
  toFun φ := ⟨powHom C d.E d.hE φ, d.powHom_mem_discRing φ.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

variable [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂]

omit [IsAlgClosed
  C] [Algebra C
  G₁] [Algebra C
  G₂] [IsScalarTower C (RatFunc C)
  G₁] [IsScalarTower C (RatFunc C)
  G₂] [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma isIntegral_symm {y : G₁} (hy : IsIntegral (discRing (0 : C) 1) y) :
    IsIntegral (discRing (0 : C) 1) (d.e.symm y) :=
  IsIntegral.map_of_comp_eq d.chartHom d.e.symm.toRingHom (RingHom.ext fun φ ↦ by
    change algebraMap (RatFunc C) G₂ (powHom C d.E d.hE φ) = d.e.symm (algebraMap (RatFunc C) G₁ φ)
    rw [← d.he, RingEquiv.symm_apply_apply]) hy

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma e_algebraMap_mem (φ : discRing (0 : C) 1) :
    d.e (algebraMap (RatFunc C) G₂ φ) ∈ integralClosure (discRing (0 : C) 1) G₁ := by
  obtain ⟨Q, hQ, hQφ⟩ := mem_discRing_iff.1 φ.2
  set τ := d.e (xF C G₂)
  have hτ : τ ∈ integralClosure (discRing (0 : C) 1) G₁ := by
    refine ⟨X ^ d.E - Polynomial.C (⟨RatFunc.X, X_mem_discRing⟩ : discRing (0 : C) 1),
      monic_X_pow_sub_C _ d.hE.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
    change τ ^ d.E = algebraMap (RatFunc C) G₁ RatFunc.X
    rw [← map_pow, ← d.xF_eq]
  have h1 : algebraMap (RatFunc C) G₂ (φ : RatFunc C) = aeval (xF C G₂) Q := by
    rw [← hQφ, ← RatFunc.aeval_X_left_eq_algebraMap]
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom C (RatFunc C) G₂)
      RatFunc.X Q).symm
  have h2 : d.e (aeval (xF C G₂) Q) = eval₂ (algebraMap C G₁) τ Q := by
    rw [aeval_def]
    have := hom_eval₂ Q (algebraMap C G₂) d.e.toRingHom (xF C G₂)
    refine this.trans ?_
    congr 1
    ext c
    exact d.e_algebraMap_C c
  rw [h1, h2, eval₂_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hτ _)
  have hc : ‖Q.coeff i‖₊ ≤ 1 := by
    have := (Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) Q i).trans hQ
    rwa [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply] at this
  have hmem : algebraMap C (RatFunc C) (Q.coeff i) ∈ discRing (0 : C) 1 :=
    mem_discRing_iff.2 ⟨Polynomial.C (Q.coeff i), ClassicalSmooth.gaussSup_le_one fun j ↦ by
      rw [coeff_C]
      split_ifs
      · exact_mod_cast hc
      · simp, RatFunc.algebraMap_C _⟩
  have := Subalgebra.algebraMap_mem (integralClosure (discRing (0 : C) 1) G₁)
    (⟨_, hmem⟩ : discRing (0 : C) 1)
  rwa [IsScalarTower.algebraMap_apply C (RatFunc C) G₁]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma isIntegral_e {y : G₂} (hy : IsIntegral (discRing (0 : C) 1) y) :
    IsIntegral (discRing (0 : C) 1) (d.e y) := by
  set S := integralClosure (discRing (0 : C) 1) G₁
  let φS : discRing (0 : C) 1 →+* S :=
    { toFun := fun φ ↦ ⟨d.e (algebraMap (RatFunc C) G₂ φ), d.e_algebraMap_mem φ⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b ↦ Subtype.ext (by simp) }
  have hS : IsIntegral S (d.e y) :=
    IsIntegral.map_of_comp_eq φS d.e.toRingHom (RingHom.ext fun φ ↦ rfl) hy
  exact isIntegral_trans _ hS

/-- The normalized vertex charts coincide. -/
noncomputable def icMap : DRint (0 : C) 1 G₂ ≃+* DRint (0 : C) 1 G₁ where
  toFun y := ⟨d.e y, d.isIntegral_e y.2⟩
  invFun y := ⟨d.e.symm y, d.isIntegral_symm y.2⟩
  left_inv _ := Subtype.ext (d.e.symm_apply_apply _)
  right_inv _ := Subtype.ext (d.e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul d.e _ _)
  map_add' _ _ := Subtype.ext (map_add d.e _ _)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma coe_icMap (y : DRint (0 : C) 1 G₂) : (d.icMap y : G₁) = d.e y := rfl

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma coe_icMap_symm (y : DRint (0 : C) 1 G₁) : (d.icMap.symm y : G₂) = d.e.symm y := rfl

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

omit [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma redD_icMap (v : Ext C G₂) (y : DRint (0 : C) 1 G₂) :
    redD (d.extMap v) (d.icMap y) = d.κmap v (redD v y) :=
  d.red_map v _

lemma mem_placeIdealD_map {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G₂) v)) (y : DRint (0 : C) 1 G₁) :
    y ∈ placeIdealD (d.extMap v) (d.mem_zeros_map hQ) ↔ d.icMap.symm y ∈ placeIdealD v hQ := by
  rw [mem_placeIdealD_iff, mem_placeIdealD_iff]
  conv_lhs => rw [← d.icMap.apply_symm_apply y, redD_icMap]
  exact d.res_map_eq_zero_iff (redD_mem_V v _ (xbar_mem_V v hQ))

lemma mem_placeIdealD_map' {w : Ext C G₁} {Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G₁) w)) (y : DRint (0 : C) 1 G₂) :
    y ∈ placeIdealD (d.extMap' w) (d.mem_zeros_map' hQ) ↔ d.icMap y ∈ placeIdealD w hQ := by
  rw [mem_placeIdealD_iff, mem_placeIdealD_iff]
  have hred : redD (d.extMap' w) y = d.κmap' w (redD w (d.icMap y)) := by
    rw [redD_apply, redD_apply, coe_icMap, ← d.red_map', RingEquiv.symm_apply_apply]
  rw [hred]
  have hz := redD_mem_V w (d.icMap y) (xbar_mem_V w hQ)
  rw [CurvePlace.res_eq_zero_iff _ ((d.mem_placeMap').2 hz), CurvePlace.res_eq_zero_iff _ hz,
    CurvePlace.valuation_lt_one_iff, CurvePlace.valuation_lt_one_iff,
    S8A.Transport.Data.valuation_lt_one_iff', S8A.Transport.Data.valuation_lt_one_iff',
    d.mem_placeMap', ← map_inv₀, d.mem_placeMap', Ne, (d.κmap' w).map_eq_zero_iff]

omit [IsAlgClosed C] [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂] in
/-- A prime of the vertex chart whose pull-back along `σ` is the residue ideal is the residue
ideal. -/
lemma eq_discIdeal_of_comap (𝔫 : Ideal (discRing (0 : C) 1)) [h𝔫 : 𝔫.IsPrime]
    (h : 𝔫.comap d.chartHom = discIdeal (0 : C) 1) : 𝔫 = discIdeal (0 : C) 1 := by
  refine ((discIdeal_isMaximal (a := (0 : C)) one_ne_zero).eq_of_le h𝔫.ne_top ?_).symm
  rintro f ⟨Q, hQ, hQa, hQ0⟩
  have hmem : ∀ g : discRing (0 : C) 1, g ∈ discIdeal (0 : C) 1 → d.chartHom g ∈ 𝔫 :=
    fun g hg ↦ by rw [← h] at hg; exact hg
  -- the constant term
  have hc₀ : algebraMap C (RatFunc C) (Q.coeff 0) ∈ discRing (0 : C) 1 :=
    mem_discRing_iff.2 ⟨Polynomial.C (Q.coeff 0), ClassicalSmooth.gaussSup_le_one fun j ↦ by
      rw [coeff_C]
      split_ifs
      · exact_mod_cast hQ 0
      · simp, RatFunc.algebraMap_C _⟩
  set c₀ : discRing (0 : C) 1 := ⟨_, hc₀⟩
  have hc₀I : c₀ ∈ discIdeal (0 : C) 1 :=
    ⟨Polynomial.C (Q.coeff 0), fun j ↦ by rw [coeff_C]; split_ifs <;> simp [hQ 0],
      by rw [aeval_C], by simpa using hQ0⟩
  have hc₀σ : d.chartHom c₀ = c₀ := Subtype.ext (AlgHom.commutes _ _)
  -- the coordinate
  set Xd : discRing (0 : C) 1 := ⟨RatFunc.X, X_mem_discRing⟩
  have hXI : Xd ∈ discIdeal (0 : C) 1 :=
    ⟨X, fun j ↦ by rw [coeff_X]; split_ifs <;> simp, by rw [aeval_X, gaussCoord_zero_one],
      by simp⟩
  have hXσ : d.chartHom Xd = Xd ^ d.E := Subtype.ext (powHom_X d.hE)
  have hX𝔫 : Xd ∈ 𝔫 := h𝔫.mem_of_pow_mem _ (hXσ ▸ hmem Xd hXI)
  -- the rest
  have hg : algebraMap C[X] (RatFunc C) Q.divX ∈ discRing (0 : C) 1 :=
    mem_discRing_iff.2 ⟨Q.divX, ClassicalSmooth.gaussSup_le_one fun j ↦ by
      rw [coeff_divX]; exact_mod_cast hQ _, rfl⟩
  have hf : f = c₀ + Xd * ⟨_, hg⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, c₀, Xd]
    have hC0 : algebraMap C (RatFunc C) (Q.coeff 0) =
        algebraMap C[X] (RatFunc C) (Polynomial.C (Q.coeff 0)) :=
      IsScalarTower.algebraMap_apply C C[X] (RatFunc C) _
    rw [← hQa, gaussCoord_zero_one, ← RatFunc.algebraMap_X, ← map_mul, hC0, ← map_add, add_comm,
      X_mul_divX_add, RatFunc.algebraMap_X, RatFunc.aeval_X_left_eq_algebraMap]
  rw [hf]
  exact 𝔫.add_mem (hc₀σ ▸ hmem c₀ hc₀I) (𝔫.mul_mem_right _ hX𝔫)

include d in
/-- **Smooth points are transported along `x = t ^ E`**: if every point of the vertex chart of
`G₂` over the residue point is smooth, so is every point of the vertex chart of `G₁`. -/
theorem isDiscSmooth_of_pow
    (h : ∀ P₂ : Ideal (DRint (0 : C) 1 G₂), P₂.IsMaximal →
      P₂.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₂)) = discIdeal (0 : C) 1 →
        IsDiscSmooth P₂)
    (P₁ : Ideal (DRint (0 : C) 1 G₁)) (hP₁ : P₁.IsMaximal)
    (hc₁ : P₁.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₁)) =
      discIdeal (0 : C) 1) : IsDiscSmooth P₁ := by
  set P₂ := P₁.comap d.icMap.toRingHom with hP₂def
  haveI : P₂.IsMaximal := Ideal.comap_isMaximal_of_surjective _ d.icMap.surjective
  have halg : ∀ φ : discRing (0 : C) 1, d.icMap (algebraMap (discRing (0 : C) 1)
      (DRint (0 : C) 1 G₂) (d.chartHom φ)) = algebraMap (discRing (0 : C) 1)
        (DRint (0 : C) 1 G₁) φ := fun φ ↦ Subtype.ext (d.he φ)
  have hc₂ : P₂.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₂)) =
      discIdeal (0 : C) 1 := by
    refine d.eq_discIdeal_of_comap _ ?_
    ext φ
    rw [Ideal.mem_comap, Ideal.mem_comap, hP₂def, Ideal.mem_comap, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, halg, ← Ideal.mem_comap, hc₁]
  obtain ⟨⟨v, Q, hQ⟩, hb, hjet⟩ := h P₂ inferInstance hc₂
  have hbP : placeIdealD v hQ = P₂ := by
    have : (⟨v, Q, hQ⟩ : GaussTube.OuterBranch C G₂) ∈ discBranches P₂ := by rw [hb]; rfl
    exact this
  refine ⟨d.brMap ⟨v, Q, hQ⟩, ?_, fun α hα ↦ ?_⟩
  · ext b₁
    constructor
    · intro hb₁
      have hb₁' : d.brMap' b₁ ∈ discBranches P₂ := by
        obtain ⟨w₁, Q₁, hQ₁⟩ := b₁
        change placeIdealD w₁ hQ₁ = P₁ at hb₁
        change placeIdealD (d.extMap' w₁) (d.mem_zeros_map' hQ₁) = P₂
        ext y
        rw [d.mem_placeIdealD_map' hQ₁, hb₁, hP₂def, Ideal.mem_comap]
        rfl
      rw [hb, Set.mem_singleton_iff] at hb₁'
      rw [Set.mem_singleton_iff, ← d.brMap_brMap' b₁, hb₁']
    · rintro rfl
      change placeIdealD (d.extMap v) (d.mem_zeros_map hQ) = P₁
      ext y
      rw [d.mem_placeIdealD_map hQ, hbP, hP₂def, Ideal.mem_comap]
      change d.icMap (d.icMap.symm y) ∈ P₁ ↔ y ∈ P₁
      rw [RingEquiv.apply_symm_apply]
  · obtain ⟨α₀, rfl⟩ := (d.κmap v).surjective α
    have hα0 : α₀ ∈ Q.V := (d.mem_placeMap (v := v) (Q := Q)).1 hα
    obtain ⟨y, s, hs, hys⟩ := hjet α₀ hα0
    refine ⟨d.icMap y, d.icMap s, hs, ?_⟩
    change redD (d.extMap v) (d.icMap y) = _ * redD (d.extMap v) (d.icMap s)
    rw [d.redD_icMap, d.redD_icMap, hys, map_mul]

end Charts

end PowData

end Data

end ClassicalSmooth

end SemistableReduction

