/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.AbhyankarInequality
import TemperedFundamentalGroups.SemistableReduction.GaussModel
import TemperedFundamentalGroups.SemistableReduction.VertexDescent
import TemperedFundamentalGroups.SemistableReduction.W7Statement

/-!
# Type-2 valuation subrings of `C(X)` are Gauss valuation rings

Blueprint §9.7a, step 3 (the discs `V₀` of the dominated models). Over an algebraically closed
field `K` with a valuation `v`, a valuation subring `W` of `K(X)` with `W ∩ K = O_v` whose residue
field is transcendental over that of `v` (`IsTypeTwo`) is the valuation ring of a Gauss valuation
`w_{a, |c|}` (`exists_eq_gaussRat_valuationSubring`). This is W2 + W3 (`GaussClassification`,
`AbhyankarInequality`) in the language of valuation subrings.
-/

universe u

open Polynomial IsLocalRing

namespace SemistableReduction

namespace W10Discs

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ₀ Γ₁ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  {v : Valuation K Γ₀} {w : Valuation L Γ₁} [v.HasExtension w]

open ValuationResidue in
/-- Transcendence of a residue, elementwise: the residue of `y` is transcendental over `κ(v)` iff
`w (P(y)) = 1` for every integral polynomial `P` with nonzero reduction. -/
lemma transcendental_residue_iff (y : w.valuationSubring) :
    Transcendental (ResidueField v.valuationSubring) (residue w.valuationSubring y) ↔
      ∀ P : v.valuationSubring[X], P.map (residue v.valuationSubring) ≠ 0 →
        w (aeval (y : L) (P.map (algebraMap v.valuationSubring K))) = 1 := by
  rw [transcendental_iff]
  constructor
  · intro h P hP
    rw [← coe_aeval, ← residue_ne_zero_iff, residue_aeval]
    exact fun h0 ↦ hP (h _ h0)
  · intro h p hp
    by_contra hp0
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (residue v.valuationSubring)
      residue_surjective p
    have := h P hp0
    rw [← coe_aeval, ← residue_ne_zero_iff, residue_aeval] at this
    exact this hp

section Classification

variable {K : Type*} [Field K] [IsAlgClosed K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {W : ValuationSubring (RatFunc K)}

/-- **Type-2 valuation subrings of `K(X)` are Gauss valuation rings** (`K` algebraically closed):
if `W ∩ K = O_v` and `W` is of type 2 over `O_v`, then `W = O_{w_{a, v(c)}}` for some `a` and
`c ≠ 0`. -/
theorem exists_eq_gaussRat_valuationSubring
    (hW : W.comap (algebraMap K (RatFunc K)) = v.valuationSubring)
    (hT : IsTypeTwo v.valuationSubring W) :
    ∃ (a c : K) (hc : c ≠ 0), W = (gaussRat v a
      (Units.mk0 (v c) ((Valuation.ne_zero_iff v).2 hc))).valuationSubring := by
  set w := W.valuation
  set v' := w.comap (algebraMap K (RatFunc K))
  haveI : v'.HasExtension w := ⟨Valuation.IsEquiv.refl⟩
  have hwW : w.valuationSubring = W := ValuationSubring.valuationSubring_valuation W
  have hv'O : v'.valuationSubring = v.valuationSubring := by
    rw [← hW]
    ext x
    change w (algebraMap K (RatFunc K) x) ≤ 1 ↔ algebraMap K (RatFunc K) x ∈ W
    exact W.valuation_le_one_iff _
  rw [← hv'O] at hT
  obtain ⟨z, hzW, hz⟩ := hT
  have hzw : z ∈ w.valuationSubring := by rw [hwW]; exact hzW
  have htr : Algebra.Transcendental (ResidueField v'.valuationSubring)
      (ResidueField w.valuationSubring) := by
    rw [Algebra.transcendental_def]
    refine ⟨residue w.valuationSubring ⟨z, hzw⟩, (transcendental_residue_iff _).2 fun P hP ↦ ?_⟩
    exact hz P hP
  have hΓ : ∀ f : RatFunc K, ∃ c : K, w f = v' c := fun f ↦
    exists_eq_of_transcendental trdeg_ratFunc.le htr f
  obtain ⟨a, c, hc0, hy, htr'⟩ :=
    exists_residue_gaussLin_transcendental (v := v') (w := w) (fun _ ↦ rfl) hΓ htr
  have hyRT : IsResidueTranscendental v'.valuationSubring W (gaussCoord a c) :=
    ⟨by rw [← hwW]; exact hy, fun P hP ↦ (transcendental_residue_iff ⟨_, hy⟩).1 htr' P hP⟩
  rw [hv'O] at hyRT
  exact ⟨a, c, hc0, (isGaussCoord_gaussCoord (v := v) (a := a) rfl).eq_of_isResidueTranscendental
    hW hyRT⟩

end Classification

section Restriction

open ZariskiModel

variable {K M F : Type*} [Field K] [Field M] [Field F] [Algebra K M] [Algebra M F] [Algebra K F]
  [IsScalarTower K M F] {O : ValuationSubring K} {W : ValuationSubring F}

lemma comap_comap_eq (hW : W.comap (algebraMap K F) = O) :
    (W.comap (algebraMap M F)).comap (algebraMap K M) = O := by
  rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hW]

/-- **Restrictions of type-2 valuation subrings along algebraic extensions are of type 2.** -/
theorem isTypeTwo_comap [Algebra.IsAlgebraic M F] (hW : W.comap (algebraMap K F) = O)
    (hT : IsTypeTwo O W) : IsTypeTwo O (W.comap (algebraMap M F)) := by
  set W' := W.comap (algebraMap M F)
  have hW' : W'.comap (algebraMap K M) = O := comap_comap_eq hW
  have hWW' : W.comap (algebraMap M F) = W' := rfl
  by_contra hnot
  letI A₁ := residueAlgebra hW'
  letI A₂ := residueAlgebra hWW'
  letI A₃ := residueAlgebra hW
  haveI : IsScalarTower (ResidueField O) (ResidueField W') (ResidueField W) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    obtain ⟨o, rfl⟩ := residue_surjective r
    change ResidueField.map (toVal hW) (residue O o) =
      ResidueField.map (toVal hWW') (ResidueField.map (toVal hW') (residue O o))
    rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
    congr 1
    exact Subtype.ext (by simp [IsScalarTower.algebraMap_apply K M F])
  haveI h₁ : Algebra.IsAlgebraic (ResidueField O) (ResidueField W') := by
    refine ⟨fun r ↦ ?_⟩
    obtain ⟨m, rfl⟩ := residue_surjective r
    by_contra hr
    exact hnot ⟨m, (isResidueTranscendental_iff hW' m.2).2 hr⟩
  haveI h₂ : Algebra.IsAlgebraic (ResidueField W') (ResidueField W) :=
    isAlgebraic_residueField hWW'
  haveI := Algebra.IsAlgebraic.trans (ResidueField O) (ResidueField W') (ResidueField W)
  obtain ⟨z, hz⟩ := hT
  exact ((isResidueTranscendental_iff hW hz.1).1 hz) (Algebra.IsAlgebraic.isAlgebraic _)

end Restriction

section Disc

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

lemma le_of_valuationSubring_le {a b c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : (gaussRat v a (Units.mk0 (v c) ((Valuation.ne_zero_iff v).2 hc))).valuationSubring ≤
      (gaussRat v b (Units.mk0 (v d) ((Valuation.ne_zero_iff v).2 hd))).valuationSubring) :
    max (v (b - a)) (v d) ≤ v c := by
  have hc' : v c ≠ 0 := (Valuation.ne_zero_iff v).2 hc
  set y : RatFunc K := algebraMap K (RatFunc K) c⁻¹ * algebraMap K[X] (RatFunc K) (X - C a)
  have hy : y ∈ (gaussRat v a (Units.mk0 (v c) hc')).valuationSubring := by
    change gaussRat v a _ y ≤ 1
    rw [map_mul, gaussRat_algebraMap_C, gaussRat_algebraMap, gauss_X_sub_C, sub_self,
      Valuation.map_zero, Units.val_mk0, max_eq_right zero_le, map_inv₀, inv_mul_cancel₀ hc']
  have := h hy
  change gaussRat v b _ y ≤ 1 at this
  rw [map_mul, gaussRat_algebraMap_C, gaussRat_algebraMap, gauss_X_sub_C, Units.val_mk0,
    map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 hc'), mul_one] at this
  exact this

/-- **Equal Gauss valuation rings have equal discs.** -/
lemma disc_eq_of_valuationSubring_eq {a b c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : (gaussRat v a (Units.mk0 (v c) ((Valuation.ne_zero_iff v).2 hc))).valuationSubring =
      (gaussRat v b (Units.mk0 (v d) ((Valuation.ne_zero_iff v).2 hd))).valuationSubring) :
    v c = v d ∧ v (a - b) ≤ v d := by
  have h₁ := le_of_valuationSubring_le hc hd h.le
  have h₂ := le_of_valuationSubring_le hd hc h.ge
  have hcd : v c = v d := le_antisymm (le_max_right _ _ |>.trans h₂) (le_max_right _ _ |>.trans h₁)
  exact ⟨hcd, (le_max_left _ _).trans h₂⟩

end Disc

section Transport

open ZariskiModel

variable {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
  {O : ValuationSubring K}

/-- The residue-transcendental centres on a set of charts. -/
def RT (O : ValuationSubring K) (charts : Set (Subring F₁)) : Set (ValuationSubring F₁) :=
  {W | W.comap (algebraMap K F₁) = O ∧ ∃ B ∈ charts, B ≤ W.toSubring ∧
    ∃ z ∈ B, IsResidueTranscendental O W z}

lemma valuation_eq_one_iff' (A : ValuationSubring F₁) (x : F₁) :
    A.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ A ∧ x⁻¹ ∈ A := by
  constructor
  · intro h
    have hx : x ≠ 0 := by rintro rfl; simp at h
    refine ⟨hx, (A.valuation_le_one_iff x).1 h.le, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, h, inv_one]
  · rintro ⟨hx, h₁, h₂⟩
    have a := (A.valuation_le_one_iff x).2 h₁
    have b := (A.valuation_le_one_iff _).2 h₂
    rw [map_inv₀] at b
    have h0 : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    refine le_antisymm a ?_
    calc (1 : _) = A.valuation x * (A.valuation x)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ A.valuation x * 1 := by gcongr
      _ = A.valuation x := mul_one _

variable (τ : K ≃+* K) (hτO : ∀ x, x ∈ O ↔ τ x ∈ O) (φ : F₁ ≃+* F₂)
  (hφ : ∀ k, φ (algebraMap K F₁ k) = algebraMap K F₂ (τ k))

/-- `τ` restricted to `O`. -/
def τO : O ≃+* O :=
  { toFun := fun o ↦ ⟨τ (o : K), (hτO o).1 o.2⟩
    invFun := fun o ↦ ⟨τ.symm (o : K), (hτO _).2 (by rw [τ.apply_symm_apply]; exact o.2)⟩
    left_inv := fun o ↦ Subtype.ext (τ.symm_apply_apply (o : K))
    right_inv := fun o ↦ Subtype.ext (τ.apply_symm_apply (o : K))
    map_mul' := fun a b ↦ Subtype.ext (map_mul τ (a : K) (b : K))
    map_add' := fun a b ↦ Subtype.ext (map_add τ (a : K) (b : K)) }

include hτO hφ in
/-- **Transport of residue-transcendental centres** along a semilinear field isomorphism. -/
theorem comap_mem_RT {charts₁ : Set (Subring F₁)} {charts₂ : Set (Subring F₂)}
    (hch : ∀ B ∈ charts₂, B.comap (φ : F₁ →+* F₂) ∈ charts₁) {W : ValuationSubring F₂}
    (hW : W ∈ RT O charts₂) : W.comap (φ : F₁ →+* F₂) ∈ RT O charts₁ := by
  obtain ⟨hWO, B, hB, hBW, z, hzB, hzW, hz⟩ := hW
  refine ⟨?_, B.comap (φ : F₁ →+* F₂), hch B hB, fun y hy ↦ hBW hy, φ.symm z, ?_, ?_, ?_⟩
  · ext x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    change φ (algebraMap K F₁ x) ∈ W ↔ x ∈ O
    rw [hφ, ← ValuationSubring.mem_comap, hWO, ← hτO]
  · change φ (φ.symm z) ∈ B
    rw [φ.apply_symm_apply]; exact hzB
  · change φ (φ.symm z) ∈ W
    rw [φ.apply_symm_apply]; exact hzW
  · intro P hP
    set P' : O[X] := P.map (τO τ hτO : O →+* O)
    have hP' : P'.map (IsLocalRing.residue O) ≠ 0 := by
      intro h0
      apply hP
      ext i
      have := congrArg (coeff · i) h0
      simp only [coeff_map, coeff_zero, P'] at this ⊢
      rw [IsLocalRing.residue_eq_zero_iff] at this ⊢
      intro hu
      exact this ((τO τ hτO).toRingHom.isUnit_map hu)
    have key := hz P' hP'
    rw [valuation_eq_one_iff'] at key ⊢
    have e₁ : ∀ (w : F₁) (Q : O[X]),
        aeval w (Q.map (algebraMap O K)) = eval₂ ((algebraMap K F₁).comp O.subtype) w Q :=
      fun w Q ↦ by rw [aeval_def, eval₂_map]; rfl
    have e₂ : ∀ (w : F₂) (Q : O[X]),
        aeval w (Q.map (algebraMap O K)) = eval₂ ((algebraMap K F₂).comp O.subtype) w Q :=
      fun w Q ↦ by rw [aeval_def, eval₂_map]; rfl
    have himg : φ (aeval (φ.symm z) (P.map (algebraMap O K))) =
        aeval z (P'.map (algebraMap O K)) := by
      rw [e₁, e₂]
      change (φ : F₁ →+* F₂) _ = _
      rw [hom_eval₂, RingEquiv.coe_toRingHom, φ.apply_symm_apply, eval₂_map]
      congr 1
      ext o
      change φ (algebraMap K F₁ (o : K)) = algebraMap K F₂ (τ (o : K))
      exact hφ _
    obtain ⟨h₀, h₁, h₂⟩ := key
    refine ⟨fun h ↦ h₀ ?_, ?_, ?_⟩
    · rw [← himg, h, map_zero]
    · change φ _ ∈ W
      rw [himg]; exact h₁
    · change φ _ ∈ W
      rw [map_inv₀, himg]; exact h₂

end Transport

section V0

open ZariskiModel

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {κ : Type*} [Finite κ] (F : κ → Type*) [∀ k, Field (F k)] [∀ k, Algebra (RatFunc C) (F k)]
  [∀ k, Algebra C (F k)] [∀ k, IsScalarTower C (RatFunc C) (F k)]
  [∀ k, FiniteDimensional (RatFunc C) (F k)] (charts : ∀ k, Set (Subring (F k)))

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

/-- The restrictions to `C(X)` of the residue-transcendental centres. -/
def S0 : Set (ValuationSubring (RatFunc C)) :=
  {V | ∃ k, ∃ W ∈ RT (ν).valuationSubring (charts k), V = W.comap (algebraMap (RatFunc C) (F k))}

omit [IsAlgClosed C] [∀ k, IsScalarTower C (RatFunc C) (F k)]
  [∀ k, FiniteDimensional (RatFunc C) (F k)] in
lemma S0_finite (hfin : ∀ k, (RT (ν).valuationSubring (charts k)).Finite) :
    (S0 (C := C) F charts).Finite := by
  have : S0 (C := C) F charts = ⋃ k, (fun W ↦ W.comap (algebraMap (RatFunc C) (F k))) ''
      (RT (ν).valuationSubring (charts k)) := by
    ext V; simp [S0, eq_comm]
  rw [this]
  exact Set.finite_iUnion fun k ↦ (hfin k).image _

omit [Finite κ] in
lemma exists_disc_of_mem_S0 {V : ValuationSubring (RatFunc C)} (hV : V ∈ S0 (C := C) F charts) :
    ∃ (a c : C) (hc : c ≠ 0), V = (gaussRat ν a
      (Units.mk0 (ν c) ((Valuation.ne_zero_iff ν).2 hc))).valuationSubring := by
  obtain ⟨k, W, ⟨hWO, B, -, hBW, z, -, hz⟩, rfl⟩ := hV
  haveI : Algebra.IsAlgebraic (RatFunc C) (F k) := Algebra.IsAlgebraic.of_finite _ _
  have hT : IsTypeTwo (ν).valuationSubring (W.comap (algebraMap (RatFunc C) (F k))) :=
    isTypeTwo_comap hWO ⟨z, hz⟩
  refine exists_eq_gaussRat_valuationSubring ?_ hT
  rw [comap_comap_eq hWO]

section Galois

variable {F charts} (τ : C ≃+* C) (hτ : ∀ z, ‖τ z‖ = ‖z‖) {π : κ → κ}
  (σ : ∀ k, F (π k) ≃+* F k)
  (hσ : ∀ k φ, σ k (algebraMap (RatFunc C) (F (π k)) φ) =
    algebraMap (RatFunc C) (F k) (ratFuncMap (τ : C →+* C) φ))
  (hch : ∀ k, ∀ B ∈ charts k, B.comap (σ k : F (π k) →+* F k) ∈ charts (π k))

omit [IsAlgClosed C] in
include hτ in
lemma valuation_comap_eq : (ν).comap (τ : C →+* C) = ν := by
  ext x
  rw [Valuation.comap_apply, NormedField.valuation_apply, NormedField.valuation_apply]
  rw [show ‖(τ : C →+* C) x‖₊ = ‖x‖₊ from NNReal.eq (hτ x)]

omit [Finite κ] [IsAlgClosed C] [∀ k, FiniteDimensional (RatFunc C) (F k)] in
include hτ hσ hch in
lemma comap_mem_S0 {V : ValuationSubring (RatFunc C)} (hV : V ∈ S0 (C := C) F charts) :
    V.comap (ratFuncMap (τ : C →+* C)) ∈ S0 (C := C) F charts := by
  obtain ⟨k, W, hW, rfl⟩ := hV
  have hτO : ∀ x, x ∈ (ν).valuationSubring ↔ τ x ∈ (ν).valuationSubring := fun x ↦ by
    simp only [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe,
      coe_nnnorm, NNReal.coe_one, hτ]
  have hφ : ∀ c, σ k (algebraMap C (F (π k)) c) = algebraMap C (F k) (τ c) := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) (F (π k)), hσ,
      IsScalarTower.algebraMap_apply C (RatFunc C) (F k), ratFuncMap_algebraMap_C]
    rfl
  refine ⟨π k, W.comap (σ k : F (π k) →+* F k),
    comap_mem_RT τ hτO (σ k) hφ (hch k) hW, ?_⟩
  ext φ
  simp only [ValuationSubring.mem_comap]
  change algebraMap (RatFunc C) (F k) (ratFuncMap (τ : C →+* C) φ) ∈ W ↔
    σ k (algebraMap (RatFunc C) (F (π k)) φ) ∈ W
  rw [hσ]

omit [IsAlgClosed C] in
include hτ in
lemma comap_gaussRat_valuationSubring (a : C) (r : NNRealˣ) :
    (gaussRat ν a r).valuationSubring.comap (ratFuncMap (τ : C →+* C)) =
      (gaussRat ν (τ.symm a) r).valuationSubring := by
  have := comap_valuationSubring_gaussRat (τ : C →+* C) ν (τ.symm a) r
  rwa [RingEquiv.coe_toRingHom, τ.apply_symm_apply, valuation_comap_eq τ hτ] at this

end Galois

/-- **The discs `V₀`**: the Gauss valuations under the residue-transcendental centres, a finite
family stable under the isometric automorphisms that transport the charts. -/
theorem exists_V0 (hfin : ∀ k, (RT (ν).valuationSubring (charts k)).Finite)
    (Gal : Set (C ≃+* C)) (hinv : ∀ τ ∈ Gal, τ.symm ∈ Gal) (hiso : ∀ τ ∈ Gal, ∀ z, ‖τ z‖ = ‖z‖)
    (htr : ∀ τ ∈ Gal, ∃ (π : κ → κ) (σ : ∀ k, F (π k) ≃+* F k),
      (∀ k φ, σ k (algebraMap (RatFunc C) (F (π k)) φ) =
        algebraMap (RatFunc C) (F k) (ratFuncMap (τ : C →+* C) φ)) ∧
      ∀ k, ∀ B ∈ charts k, B.comap (σ k : F (π k) →+* F k) ∈ charts (π k)) :
    ∃ (n : ℕ) (a₀ c₀ : Fin n → C) (hc₀ : ∀ i, c₀ i ≠ 0),
      (∀ k, ∀ W ∈ RT (ν).valuationSubring (charts k), ∃ i,
        W.comap (algebraMap (RatFunc C) (F k)) = (gaussRat ν (a₀ i)
          (Units.mk0 (ν (c₀ i)) ((Valuation.ne_zero_iff ν).2 (hc₀ i)))).valuationSubring) ∧
      ∀ τ ∈ Gal, W7.DiscsLE (fun i ↦ τ (a₀ i)) c₀ a₀ c₀ := by
  classical
  set S := S0 (C := C) F charts
  have hS := S0_finite F charts hfin
  set T := hS.toFinset
  set e := T.equivFin.symm
  have hmem : ∀ i, ((e i : ValuationSubring (RatFunc C))) ∈ S := fun i ↦
    hS.mem_toFinset.1 (e i).2
  choose a c hc hac using fun i ↦ exists_disc_of_mem_S0 F charts (hmem i)
  have hsurj : ∀ V ∈ S, ∃ i, V = e i := fun V hV ↦
    ⟨e.symm ⟨V, hS.mem_toFinset.2 hV⟩, by rw [Equiv.apply_symm_apply]⟩
  refine ⟨T.card, a, c, hc, fun k W hW ↦ ?_, fun τ hτ ↦ ?_⟩
  · obtain ⟨i, hi⟩ := hsurj _ ⟨k, W, hW, rfl⟩
    exact ⟨i, hi.trans (hac i)⟩
  · intro i
    obtain ⟨π, σ, hσ, hch⟩ := htr τ.symm (hinv τ hτ)
    have hV := comap_mem_S0 τ.symm (hiso _ (hinv τ hτ)) σ hσ hch (hac i ▸ hmem i)
    rw [comap_gaussRat_valuationSubring τ.symm (hiso _ (hinv τ hτ)), RingEquiv.symm_symm] at hV
    obtain ⟨j, hj⟩ := hsurj _ hV
    rw [hac j] at hj
    obtain ⟨h₁, h₂⟩ := disc_eq_of_valuationSubring_eq (hc i) (hc j) hj
    refine ⟨j, ?_, ?_⟩
    · rw [NormedField.valuation_apply, NormedField.valuation_apply] at h₁
      exact congrArg NNReal.toReal h₁.symm
    · rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe,
        coe_nnnorm, coe_nnnorm, ← norm_neg, neg_sub] at h₂
      exact h₂

end V0

end W10Discs

end SemistableReduction
