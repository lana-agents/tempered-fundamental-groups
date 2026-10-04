/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Main
import TemperedFundamentalGroups.SemistableReduction.Splitting

/-!
# Transport of branches and reductions (O6.5, core)

Blueprint §9.12, O6.5. Let `G₁, G₂` be finite extensions of `C(x)` and `e : G₂ ≃+* G₁` a ring
isomorphism which is semilinear over a ring automorphism `ψ` of `C(x)`
(`e (φ • y) = ψ φ • e y`), where `ψ` is semilinear over an isometric automorphism `τ` of `C`,
preserves the Gauss valuation `w_{0,1}`, and moves the coordinate by an affine map
`ψ⁻¹ x = α x + γ` (`|α| = 1`, `|γ| < 1`) — the data `Transport.Data`. Two instances are used:

* **change of representative** (`τ = id`): `G₂ = Aff a' c' F`, `G₁ = Aff a c F` for
  `‖c'‖ = ‖c‖`, `‖a - a'‖ < ‖c‖`, `e = id`;
* **semilinear automorphisms** (`ψ` acting on coefficients by `τ`): `e = σ`.

The core (this file) transports extensions of `w_{0,1}` (`extMap`), residue fields (`κmap`,
semilinear over the residue automorphism `τbar`), reductions (`red_map`), places (`placeMap`),
their residues (`res_map_eq_zero_iff`) and the zeros of `x̄` (`mem_zeros_map`).
-/

open IsLocalRing Valuation Metric
open scoped NNReal

namespace SemistableReduction

namespace S8A

namespace Transport

open GaussFibre GaussStability FundamentalInequality PlaceNorm

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Residue

variable (τ : C ≃+* C) (hτ : ∀ z, ‖τ z‖ = ‖z‖)

/-- An isometric automorphism of `C` acts on the ring of integers. -/
noncomputable def intEquiv : HenselComplete.integers C ≃+* HenselComplete.integers C where
  toFun o := ⟨τ o, (HenselComplete.mem_integers_iff _).2
    (by rw [hτ]; exact HenselComplete.norm_le_one o)⟩
  invFun o := ⟨τ.symm o, (HenselComplete.mem_integers_iff _).2
    (by rw [← hτ, RingEquiv.apply_symm_apply]; exact HenselComplete.norm_le_one o)⟩
  left_inv o := Subtype.ext (τ.symm_apply_apply _)
  right_inv o := Subtype.ext (τ.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul τ _ _)
  map_add' _ _ := Subtype.ext (map_add τ _ _)

/-- The residue automorphism of an isometric automorphism of `C`. -/
noncomputable def τbar : 𝓀 ≃+* 𝓀 := ResidueField.mapEquiv (intEquiv τ hτ)

omit [IsAlgClosed C] in
lemma τbar_residue (o : HenselComplete.integers C) :
    τbar τ hτ (residue _ o) = residue _ (intEquiv τ hτ o) := by
  simp [τbar, ResidueField.map_residue]

end Residue

variable (C) in
/-- **Transport data** between two finite extensions of `C(x)`. -/
structure Data (G₁ G₂ : Type*) [Field G₁] [Field G₂] [Algebra (RatFunc C) G₁]
    [Algebra (RatFunc C) G₂] where
  /-- The automorphism of the constants. -/
  τ : C ≃+* C
  hτ : ∀ z, ‖τ z‖ = ‖z‖
  /-- The automorphism of `C(x)`. -/
  ψ : RatFunc C ≃+* RatFunc C
  ψC : ∀ c, ψ (algebraMap C (RatFunc C) c) = algebraMap C (RatFunc C) (τ c)
  ψg : ∀ φ, gauss1 C (ψ φ) = gauss1 C φ
  /-- The linear coefficient of `ψ⁻¹ x`. -/
  α : C
  /-- The constant coefficient of `ψ⁻¹ x`. -/
  γ : C
  hα : ‖α‖ = 1
  hγ : ‖γ‖ < 1
  ψX : ψ.symm RatFunc.X = algebraMap C (RatFunc C) α * RatFunc.X + algebraMap C (RatFunc C) γ
  /-- The isomorphism of fields. -/
  e : G₂ ≃+* G₁
  he : ∀ φ, e (algebraMap (RatFunc C) G₂ φ) = algebraMap (RatFunc C) G₁ (ψ φ)

namespace Data

variable {G₁ G₂ : Type*} [Field G₁] [Field G₂] [Algebra (RatFunc C) G₁] [Algebra (RatFunc C) G₂]
  (d : Data C G₁ G₂)

omit [IsAlgClosed C] in
lemma symm_he (φ : RatFunc C) :
    d.e.symm (algebraMap (RatFunc C) G₁ φ) = algebraMap (RatFunc C) G₂ (d.ψ.symm φ) := by
  rw [← d.e.symm_apply_apply (algebraMap (RatFunc C) G₂ _), d.he, RingEquiv.apply_symm_apply]

/-- Transport of extensions of `w_{0,1}`. -/
noncomputable def extMap (v : Ext C G₂) : Ext C G₁ :=
  ⟨v.1.comap d.e.symm.toRingHom, Valuation.ext fun φ ↦ by
    change v.1 (d.e.symm (algebraMap (RatFunc C) G₁ φ)) = gauss1 C φ
    rw [d.symm_he, valuation_algebraMap, ← d.ψg, RingEquiv.apply_symm_apply]⟩

omit [IsAlgClosed C] in
lemma extMap_apply (v : Ext C G₂) (f : G₂) : (d.extMap v).1 (d.e f) = v.1 f := by
  change v.1 (d.e.symm (d.e f)) = _
  rw [RingEquiv.symm_apply_apply]

/-- Transport of valuation rings. -/
def intMap (v : Ext C G₂) : v.1.valuationSubring ≃+* (d.extMap v).1.valuationSubring where
  toFun f := ⟨d.e f, by
    change (d.extMap v).1 (d.e f) ≤ 1
    rw [d.extMap_apply]
    exact f.2⟩
  invFun f := ⟨d.e.symm f, by
    change v.1 (d.e.symm f) ≤ 1
    rw [← d.extMap_apply v, RingEquiv.apply_symm_apply]
    exact f.2⟩
  left_inv f := Subtype.ext (d.e.symm_apply_apply _)
  right_inv f := Subtype.ext (d.e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul d.e _ _)
  map_add' _ _ := Subtype.ext (map_add d.e _ _)

/-- Transport of residue fields. -/
noncomputable def κmap (v : Ext C G₂) :
    ResidueField v.1.valuationSubring ≃+* ResidueField (d.extMap v).1.valuationSubring :=
  ResidueField.mapEquiv (d.intMap v)

omit [IsAlgClosed C] in
/-- **Reductions are transported.** -/
lemma red_map (v : Ext C G₂) (f : G₂) : red C (d.e f) (d.extMap v) = d.κmap v (red C f v) := by
  by_cases h : v.1 f ≤ 1
  · have h' : (d.extMap v).1 (d.e f) ≤ 1 := by rw [d.extMap_apply]; exact h
    rw [red_of_le h, red_of_le h', κmap, ResidueField.mapEquiv_apply, ResidueField.map_residue]
    rfl
  · have h' : ¬ (d.extMap v).1 (d.e f) ≤ 1 := by rw [d.extMap_apply]; exact h
    unfold red
    rw [dif_neg h, dif_neg h', map_zero]

omit [IsAlgClosed C] in
/-- Every element of a residue field is a reduction. -/
lemma exists_red_eq (v : Ext C G₂) (z : ResidueField v.1.valuationSubring) :
    ∃ f : G₂, v.1 f ≤ 1 ∧ red C f v = z := by
  obtain ⟨⟨f, hf⟩, rfl⟩ := residue_surjective z
  exact ⟨f, hf, red_of_le hf⟩

section Constants

variable [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂]

attribute [local instance] isCurveFunctionField

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] in
lemma e_algebraMap_C (c : C) : d.e (algebraMap C G₂ c) = algebraMap C G₁ (d.τ c) := by
  rw [IsScalarTower.algebraMap_apply C (RatFunc C) G₂, d.he, d.ψC,
    ← IsScalarTower.algebraMap_apply]

omit [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] [IsAlgClosed C] in
/-- **The transport of residue fields is semilinear over the residue automorphism.** -/
lemma κmap_algebraMap (v : Ext C G₂) (k : 𝓀) :
    d.κmap v (algebraMap 𝓀 _ k) = algebraMap 𝓀 _ (τbar d.τ d.hτ k) := by
  obtain ⟨o, rfl⟩ := residue_surjective k
  have ho : ‖(o : C)‖₊ ≤ 1 := by exact_mod_cast HenselComplete.norm_le_one o
  have ho' : ‖d.τ (o : C)‖₊ ≤ 1 := by
    have : ‖d.τ (o : C)‖ ≤ 1 := by rw [d.hτ]; exact HenselComplete.norm_le_one o
    exact_mod_cast this
  have h1 : algebraMap 𝓀 (ResidueField v.1.valuationSubring) (residue _ o) =
      red C (algebraMap C G₂ (o : C)) v := (red_algebraMap_C (w := v) _ ho).symm
  rw [τbar_residue, h1, ← d.red_map, d.e_algebraMap_C, red_algebraMap_C _ ho']
  rfl

omit [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] [IsAlgClosed C] in
lemma κmap_symm_algebraMap (v : Ext C G₂) (k : 𝓀) :
    (d.κmap v).symm (algebraMap 𝓀 _ k) = algebraMap 𝓀 _ ((τbar d.τ d.hτ).symm k) := by
  rw [RingEquiv.symm_apply_eq, κmap_algebraMap, RingEquiv.apply_symm_apply]

attribute [local instance] DiscreteCoefficients.isAlgClosed_residueField

/-- **Transport of places.** -/
noncomputable def placeMap (v : Ext C G₂)
    (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) :
    CurvePlace 𝓀 (ResidueField (d.extMap v).1.valuationSubring) where
  V := Q.V.comap (d.κmap v).symm.toRingHom
  algebraMap_mem c := by
    change (d.κmap v).symm (algebraMap 𝓀 _ c) ∈ Q.V
    rw [κmap_symm_algebraMap]
    exact Q.algebraMap_mem _
  ne_top h := Q.ne_top (by
    ext z
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    have : d.κmap v z ∈ Q.V.comap (d.κmap v).symm.toRingHom := h ▸ trivial
    simpa using this)

omit [FiniteDimensional (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₂] [IsAlgClosed C] in
lemma mem_placeMap {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    {z : ResidueField v.1.valuationSubring} : d.κmap v z ∈ (d.placeMap v Q).V ↔ z ∈ Q.V := by
  change (d.κmap v).symm (d.κmap v z) ∈ Q.V ↔ _
  rw [RingEquiv.symm_apply_apply]

/-- Elements of the maximal ideal of a valuation subring. -/
lemma valuation_lt_one_iff' {L : Type*} [Field L] (W : ValuationSubring L) {z : L} :
    W.valuation z < 1 ↔ z ∈ W ∧ ¬ (z ≠ 0 ∧ z⁻¹ ∈ W) := by
  rw [lt_iff_le_and_ne, ValuationSubring.valuation_le_one_iff, Ne,
    valuation_eq_one_iff_mem_and_inv_mem]
  tauto

/-- **Residues are transported.** -/
lemma res_map_eq_zero_iff {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    {z : ResidueField v.1.valuationSubring} (hz : z ∈ Q.V) :
    (d.placeMap v Q).res (d.κmap v z) = 0 ↔ Q.res z = 0 := by
  rw [CurvePlace.res_eq_zero_iff _ ((d.mem_placeMap).2 hz), CurvePlace.res_eq_zero_iff _ hz,
    CurvePlace.valuation_lt_one_iff, CurvePlace.valuation_lt_one_iff, valuation_lt_one_iff',
    valuation_lt_one_iff', d.mem_placeMap, ← map_inv₀, d.mem_placeMap, Ne,
    (d.κmap v).map_eq_zero_iff]

/-- **The zeros of the coordinate are transported.** -/
lemma mem_zeros_map {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G₂) v)) :
    d.placeMap v Q ∈ zeros 𝓀 (red C (xF C G₁) (d.extMap v)) := by
  rw [mem_zeros] at hQ ⊢
  -- `x̄₁` is a unit multiple of the transport of `x̄₂`
  have hx : xF C G₁ = d.e (algebraMap (RatFunc C) G₂ (algebraMap C (RatFunc C) d.α) *
      xF C G₂ + algebraMap (RatFunc C) G₂ (algebraMap C (RatFunc C) d.γ)) := by
    rw [← map_mul, ← map_add, ← d.ψX, d.he, RingEquiv.apply_symm_apply]
  have hα1 : v.1 (algebraMap (RatFunc C) G₂ (algebraMap C (RatFunc C) d.α)) ≤ 1 := by
    rw [valuation_algebraMap_C]
    exact_mod_cast d.hα.le
  have hX1 : v.1 (xF C G₂) ≤ 1 := by
    rw [xF, valuation_algebraMap, gauss1_X]
  have hγ1 : v.1 (algebraMap (RatFunc C) G₂ (algebraMap C (RatFunc C) d.γ)) ≤ 1 := by
    rw [valuation_algebraMap_C]
    exact_mod_cast d.hγ.le
  have hαn : ‖d.α‖₊ ≤ 1 := by exact_mod_cast d.hα.le
  have hγn : ‖d.γ‖₊ ≤ 1 := by exact_mod_cast d.hγ.le
  have hred : red C (xF C G₁) (d.extMap v) = d.κmap v
      (algebraMap 𝓀 _ (residue _ ⟨d.α, by simpa using hαn⟩) * red C (xF C G₂) v) := by
    rw [hx, d.red_map, red_add (by rw [map_mul]; exact mul_le_one' hα1 hX1) hγ1,
      red_mul hα1 hX1, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      red_algebraMap_C _ hαn, red_algebraMap_C _ hγn]
    have h0 : residue (HenselComplete.integers C) ⟨d.γ, by simpa using hγn⟩ = 0 := by
      rw [residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
      exact d.hγ
    rw [h0, map_zero, add_zero]
  rw [hred, ← map_inv₀, d.mem_placeMap]
  intro hmem
  apply hQ
  have hu := Q.algebraMap_mem (residue (HenselComplete.integers C) ⟨d.α, by simpa using hαn⟩)
  have := mul_mem hu hmem
  rwa [mul_inv, ← mul_assoc, mul_inv_cancel₀, one_mul] at this
  rw [Ne, map_eq_zero_iff _ (algebraMap 𝓀 _).injective, residue_eq_zero_iff,
    HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
  exact fun h ↦ (lt_irrefl _ (d.hα ▸ h))

/-- Transport of branches. -/
noncomputable def brMap (b : GaussTube.OuterBranch C G₂) : GaussTube.OuterBranch C G₁ :=
  ⟨d.extMap b.1, d.placeMap b.1 b.2.1, d.mem_zeros_map b.2.2⟩

end Constants

/-- **The inverse transport data.** -/
noncomputable def symm : Data C G₂ G₁ where
  τ := d.τ.symm
  hτ z := by rw [← d.hτ, RingEquiv.apply_symm_apply]
  ψ := d.ψ.symm
  ψC c := by
    rw [RingEquiv.symm_apply_eq, d.ψC, RingEquiv.apply_symm_apply]
  ψg φ := by rw [← d.ψg, RingEquiv.apply_symm_apply]
  α := (d.τ d.α)⁻¹
  γ := -(d.τ d.γ / d.τ d.α)
  hα := by rw [norm_inv, d.hτ, d.hα, inv_one]
  hγ := by rw [norm_neg, norm_div, d.hτ, d.hτ, d.hα, div_one]; exact d.hγ
  ψX := by
    have hα0 : d.τ d.α ≠ 0 := by
      intro h
      have := d.hτ d.α
      rw [h, norm_zero, d.hα] at this
      exact zero_ne_one this
    have h := congrArg d.ψ d.ψX
    rw [RingEquiv.apply_symm_apply, map_add, map_mul, d.ψC, d.ψC] at h
    have hα' : algebraMap C (RatFunc C) (d.τ d.α) ≠ 0 := by simpa using hα0
    rw [RingEquiv.symm_symm, _root_.map_neg, map_div₀, map_inv₀]
    calc d.ψ RatFunc.X = (algebraMap C (RatFunc C) (d.τ d.α))⁻¹ *
          (algebraMap C (RatFunc C) (d.τ d.α) * d.ψ RatFunc.X +
            algebraMap C (RatFunc C) (d.τ d.γ)) -
          (algebraMap C (RatFunc C) (d.τ d.α))⁻¹ * algebraMap C (RatFunc C) (d.τ d.γ) := by
          field_simp
          ring
      _ = _ := by
          rw [← h]
          field_simp
          ring
  e := d.e.symm
  he φ := d.symm_he φ

/-- **Branches are determined by their valuation and the valuation ring of their place.** -/
lemma _root_.SemistableReduction.S8A.Transport.outerBranch_ext {G : Type*} [Field G]
    [Algebra (RatFunc C) G] [Algebra C G] [IsScalarTower C (RatFunc C) G]
    [FiniteDimensional (RatFunc C) G] {b b' : GaussTube.OuterBranch C G} (h1 : b.1 = b'.1)
    (h2 : ∀ f : G, b.1.1 f ≤ 1 → (red C f b.1 ∈ b.2.1.V ↔ red C f b'.1 ∈ b'.2.1.V)) : b = b' := by
  obtain ⟨v, Q, hQ⟩ := b
  obtain ⟨v', Q', hQ'⟩ := b'
  simp only at h1 h2
  subst h1
  have hQQ : Q = Q' := by
    ext z
    obtain ⟨⟨f, hf⟩, rfl⟩ := residue_surjective z
    have := h2 f hf
    rwa [red_of_le hf] at this
  subst hQQ
  rfl

section Constants

variable [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂]

omit [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂] [IsAlgClosed C] in
lemma extMap_symm_extMap (v : Ext C G₂) : d.symm.extMap (d.extMap v) = v :=
  Subtype.ext (Valuation.ext fun f ↦ by
    change v.1 (d.e.symm (d.e.symm.symm f)) = v.1 f
    rw [RingEquiv.symm_symm, RingEquiv.symm_apply_apply])

omit [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂] [IsAlgClosed C] in
lemma extMap_extMap_symm (v : Ext C G₁) : d.extMap (d.symm.extMap v) = v :=
  Subtype.ext (Valuation.ext fun f ↦ by
    change v.1 (d.e.symm.symm (d.e.symm f)) = v.1 f
    rw [RingEquiv.symm_symm, RingEquiv.apply_symm_apply])

/-- Round trip of branches. -/
lemma brMap_brMap_symm (b : GaussTube.OuterBranch C G₁) : d.brMap (d.symm.brMap b) = b := by
  refine outerBranch_ext (d.extMap_extMap_symm b.1) fun f _ ↦ ?_
  obtain ⟨v, Q, hQ⟩ := b
  change red C f (d.extMap (d.symm.extMap v)) ∈ (d.placeMap _ (d.symm.placeMap v Q)).V ↔
    red C f v ∈ Q.V
  rw [← d.e.apply_symm_apply f, d.red_map, d.mem_placeMap]
  change red C (d.symm.e f) (d.symm.extMap v) ∈ (d.symm.placeMap v Q).V ↔ _
  rw [d.symm.red_map, d.symm.mem_placeMap]
  change _ ↔ red C (d.e (d.e.symm f)) v ∈ Q.V
  rw [RingEquiv.apply_symm_apply]

/-- Round trip of branches. -/
lemma brMap_symm_brMap (b : GaussTube.OuterBranch C G₂) : d.symm.brMap (d.brMap b) = b := by
  refine outerBranch_ext (d.extMap_symm_extMap b.1) fun f _ ↦ ?_
  obtain ⟨v, Q, hQ⟩ := b
  change red C f (d.symm.extMap (d.extMap v)) ∈ (d.symm.placeMap _ (d.placeMap v Q)).V ↔
    red C f v ∈ Q.V
  rw [← d.e.symm_apply_apply f]
  change red C (d.symm.e (d.e f)) _ ∈ _ ↔ _
  rw [d.symm.red_map, d.symm.mem_placeMap, d.red_map, d.mem_placeMap]
  change _ ↔ red C (d.e.symm (d.e f)) v ∈ Q.V
  rw [RingEquiv.symm_apply_apply]

end Constants

/-! ### Charts -/

section Charts

variable {A₂ A₁ : Subring (RatFunc C)} (hA : ∀ φ, φ ∈ A₂ ↔ d.ψ φ ∈ A₁)

/-- `ψ` restricted to the charts. -/
noncomputable def chartHom : A₂ →+* A₁ where
  toFun φ := ⟨d.ψ φ, (hA φ).1 φ.2⟩
  map_one' := Subtype.ext (map_one d.ψ)
  map_mul' _ _ := Subtype.ext (map_mul d.ψ _ _)
  map_zero' := Subtype.ext (map_zero d.ψ)
  map_add' _ _ := Subtype.ext (map_add d.ψ _ _)

omit [IsAlgClosed C] in
include hA in
lemma isIntegral_e {y : G₂} (hy : IsIntegral A₂ y) : IsIntegral A₁ (d.e y) :=
  IsIntegral.map_of_comp_eq (d.chartHom hA) d.e.toRingHom
    (RingHom.ext fun φ ↦ (d.he φ).symm) hy

/-- **Transport of normalized charts.** -/
noncomputable def icMap : integralClosure A₂ G₂ →+* integralClosure A₁ G₁ where
  toFun y := ⟨d.e y, d.isIntegral_e hA y.2⟩
  map_one' := Subtype.ext (map_one d.e)
  map_mul' _ _ := Subtype.ext (map_mul d.e _ _)
  map_zero' := Subtype.ext (map_zero d.e)
  map_add' _ _ := Subtype.ext (map_add d.e _ _)

omit [IsAlgClosed C] in
lemma coe_icMap (y : integralClosure A₂ G₂) : (d.icMap hA y : G₁) = d.e y := rfl

omit [IsAlgClosed C] in
include hA in
lemma symm_hA : ∀ φ, φ ∈ A₁ ↔ d.symm.ψ φ ∈ A₂ := fun φ ↦ by
  change φ ∈ A₁ ↔ d.ψ.symm φ ∈ A₂
  rw [hA, RingEquiv.apply_symm_apply]

omit [IsAlgClosed C] in
lemma icMap_symm_icMap (y : integralClosure A₂ G₂) :
    d.symm.icMap (d.symm_hA hA) (d.icMap hA y) = y :=
  Subtype.ext (d.e.symm_apply_apply _)

omit [IsAlgClosed C] in
lemma icMap_icMap_symm (y : integralClosure A₁ G₁) :
    d.icMap hA (d.symm.icMap (d.symm_hA hA) y) = y :=
  Subtype.ext (d.e.apply_symm_apply _)

end Charts

/-! ### Smooth points of vertex charts -/

section Smooth

open DiscCount SmoothVertex

variable [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂]
  (hD : ∀ φ, φ ∈ discRing (0 : C) 1 ↔ d.ψ φ ∈ discRing (0 : C) 1)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

omit [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂] in
omit [IsAlgClosed C] in
lemma redD_icMap (v : Ext C G₂) (y : DRint (0 : C) 1 G₂) :
    redD (d.extMap v) (d.icMap hD y) = d.κmap v (redD v y) :=
  d.red_map v _

lemma mem_placeIdealD_map {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G₂) v)) (y : DRint (0 : C) 1 G₁) :
    y ∈ placeIdealD (d.extMap v) (d.mem_zeros_map hQ) ↔
      d.symm.icMap (d.symm_hA hD) y ∈ placeIdealD v hQ := by
  rw [mem_placeIdealD_iff, mem_placeIdealD_iff]
  conv_lhs => rw [← d.icMap_icMap_symm hD y, redD_icMap]
  exact d.res_map_eq_zero_iff (redD_mem_V v _ (xbar_mem_V v hQ))

/-- **Smooth points are transported.** -/
theorem isDiscSmooth_comap {P' : Ideal (DRint (0 : C) 1 G₂)} (h : IsDiscSmooth P') :
    IsDiscSmooth (P'.comap (d.symm.icMap (d.symm_hA hD))) := by
  obtain ⟨⟨v, Q, hQ⟩, hb, hjet⟩ := h
  have hbP : placeIdealD v hQ = P' := by
    have : (⟨v, Q, hQ⟩ : GaussTube.OuterBranch C G₂) ∈ discBranches P' := by rw [hb]; rfl
    exact this
  refine ⟨d.brMap ⟨v, Q, hQ⟩, ?_, fun α hα ↦ ?_⟩
  · ext b₁
    constructor
    · intro hb₁
      -- the back-transported branch passes through `P'`
      have hb₁' : d.symm.brMap b₁ ∈ discBranches P' := by
        obtain ⟨v₁, Q₁, hQ₁⟩ := b₁
        change placeIdealD v₁ hQ₁ = P'.comap _ at hb₁
        change placeIdealD (d.symm.extMap v₁) (d.symm.mem_zeros_map hQ₁) = P'
        ext y
        rw [d.symm.mem_placeIdealD_map (d.symm_hA hD) hQ₁, hb₁, Ideal.mem_comap]
        have : d.symm.icMap (d.symm_hA hD) (d.symm.symm.icMap (d.symm.symm_hA (d.symm_hA hD)) y)
            = y := Subtype.ext (d.e.symm_apply_apply _)
        rw [this]
      rw [hb, Set.mem_singleton_iff] at hb₁'
      rw [Set.mem_singleton_iff, ← d.brMap_brMap_symm b₁, hb₁']
    · rintro rfl
      change placeIdealD (d.extMap v) (d.mem_zeros_map hQ) = _
      ext y
      rw [d.mem_placeIdealD_map hD hQ, hbP, Ideal.mem_comap]
  · -- the jets
    obtain ⟨α₀, rfl⟩ := (d.κmap v).surjective α
    have hα0 : α₀ ∈ Q.V := (d.mem_placeMap (v := v) (Q := Q)).1 hα
    obtain ⟨y, s, hs, hys⟩ := hjet α₀ hα0
    refine ⟨d.icMap hD y, d.icMap hD s, ?_, ?_⟩
    · rw [Ideal.mem_comap, d.icMap_symm_icMap hD]
      exact hs
    · change redD (d.extMap v) (d.icMap hD y) = _ * redD (d.extMap v) (d.icMap hD s)
      rw [d.redD_icMap hD, d.redD_icMap hD, hys, map_mul]

end Smooth

/-! ### The vertex chart and its residue ideal are preserved -/

section DiscChart

open DiscCount

omit [IsAlgClosed C] in
lemma ψ_X : d.ψ RatFunc.X = algebraMap C (RatFunc C) d.symm.α * RatFunc.X +
    algebraMap C (RatFunc C) d.symm.γ := d.symm.ψX

omit [IsAlgClosed C] in
lemma ψ_mem_discRing {φ : RatFunc C} (hφ : φ ∈ discRing (0 : C) 1) :
    d.ψ φ ∈ discRing (0 : C) 1 := by
  have hbase : ∀ o : C, ‖o‖ ≤ 1 → algebraMap C (RatFunc C) o ∈ discRing (0 : C) 1 := fun o ho ↦
    algebraMap_mem_discRing ho
  have hX : RatFunc.X ∈ discRing (0 : C) 1 := SmoothVertex.X_mem_discRing
  rw [discRing, polyChart, SmoothVertex.gaussCoord_zero_one] at hφ
  induction hφ using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨o, ho, rfl⟩ | hz
    · rw [d.ψC]
      refine hbase _ ?_
      rw [d.hτ]
      exact (HenselComplete.mem_integers_iff _).1 ho
    · rw [Set.mem_singleton_iff.1 hz, d.ψ_X]
      refine add_mem (mul_mem (hbase _ d.symm.hα.le) hX) (hbase _ d.symm.hγ.le)
  | zero => simp
  | one => simp
  | add _ _ _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg _ _ ha => rw [_root_.map_neg]; exact neg_mem ha
  | mul _ _ _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

omit [IsAlgClosed C] in
lemma ψ_mem_discRing_iff (φ : RatFunc C) :
    φ ∈ discRing (0 : C) 1 ↔ d.ψ φ ∈ discRing (0 : C) 1 := by
  refine ⟨d.ψ_mem_discRing, fun h ↦ ?_⟩
  have := d.symm.ψ_mem_discRing h
  rwa [show d.symm.ψ (d.ψ φ) = φ from d.ψ.symm_apply_apply φ] at this

/-- A disc valuation of the open unit disc. -/
noncomputable def halfRad : ℝ≥0ˣ := Units.mk0 (1 / 2) (by norm_num)

omit [IsAlgClosed C] in
lemma isDiscVal_half : IsDiscVal (0 : C) 1 (gaussRat (NormedField.valuation (K := C)) 0 halfRad) :=
  ⟨fun c ↦ by rw [gaussRat_algebraMap_C, NormedField.valuation_apply], by
    rw [SmoothVertex.gaussCoord_zero_one, AnnulusUnit.gaussRat_X]
    change (1 / 2 : ℝ≥0) < 1
    norm_num⟩

omit [IsAlgClosed C] in
lemma isDiscVal_comp {ν : Valuation (RatFunc C) ℝ≥0} (hν : IsDiscVal (0 : C) 1 ν) :
    IsDiscVal (0 : C) 1 (ν.comap d.ψ.toRingHom) := by
  refine ⟨fun c ↦ ?_, ?_⟩
  · change ν (d.ψ (algebraMap C (RatFunc C) c)) = _
    rw [d.ψC, hν.map_C]
    exact NNReal.eq (by simpa using d.hτ c)
  · change ν (d.ψ (gaussCoord (0 : C) 1)) < 1
    rw [SmoothVertex.gaussCoord_zero_one, d.ψ_X]
    have hX := hν.X_lt_one
    rw [SmoothVertex.gaussCoord_zero_one] at hX
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul, hν.map_C]
      have : ‖d.symm.α‖₊ = 1 := by ext; exact d.symm.hα
      rw [this, one_mul]
      exact hX
    · rw [hν.map_C]
      exact_mod_cast d.symm.hγ

omit [IsAlgClosed C] in
lemma chartHom_mem_discIdeal_iff (φ : discRing (0 : C) 1) :
    d.chartHom d.ψ_mem_discRing_iff φ ∈ discIdeal (0 : C) 1 ↔ φ ∈ discIdeal (0 : C) 1 := by
  rw [mem_discIdeal_iff isDiscVal_half, mem_discIdeal_iff (d.isDiscVal_comp isDiscVal_half)]
  rfl

end DiscChart

section DiscGood

open DiscCount SmoothVertex

variable [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂]

include d in
/-- **Smoothness over the residue point `x̄ = 0` is transported.** -/
theorem discGoodAt_transport
    (h : ∀ P' : Ideal (DRint (0 : C) 1 G₂), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₂)) = discIdeal (0 : C) 1 →
        IsDiscSmooth P') :
    ∀ P' : Ideal (DRint (0 : C) 1 G₁), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₁)) = discIdeal (0 : C) 1 →
        IsDiscSmooth P' := by
  intro P₁ hmax hP₁
  have hD := d.ψ_mem_discRing_iff
  set P := P₁.comap (d.icMap hD)
  have hsurj : Function.Surjective (d.icMap hD) := fun y ↦ ⟨_, d.icMap_icMap_symm hD y⟩
  haveI : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hP : P.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₂)) =
      discIdeal (0 : C) 1 := by
    ext φ
    rw [Ideal.mem_comap, Ideal.mem_comap, ← d.chartHom_mem_discIdeal_iff, ← hP₁,
      Ideal.mem_comap]
    have : d.icMap hD (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₂) φ) =
        algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₁) (d.chartHom hD φ) :=
      Subtype.ext (d.he φ)
    rw [this]
  have := d.isDiscSmooth_comap hD (h P inferInstance hP)
  have hPP : P.comap (d.symm.icMap (d.symm_hA hD)) = P₁ := by
    ext y
    rw [Ideal.mem_comap, Ideal.mem_comap, d.icMap_icMap_symm]
  rwa [hPP] at this

end DiscGood

/-! ### Ordinary double points of node charts -/

section Node

open GaussTube

variable [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-- **Residues are transported** by the residue automorphism. -/
lemma res_placeMap {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    {z : ResidueField v.1.valuationSubring} (hz : z ∈ Q.V) :
    (d.placeMap v Q).res (d.κmap v z) = τbar d.τ d.hτ (Q.res z) := by
  refine CurvePlace.res_eq_of_valuation_sub_lt_one _ ?_
  have h := Q.valuation_sub_res_lt_one hz
  rw [CurvePlace.valuation_lt_one_iff, valuation_lt_one_iff'] at h ⊢
  rw [← d.κmap_algebraMap, ← _root_.map_sub, ← map_inv₀, d.mem_placeMap, d.mem_placeMap, Ne,
    (d.κmap v).map_eq_zero_iff]
  exact h

variable {c₂ c₁ : C} (hc₂ : ‖c₂‖ < 1) (hc₁ : ‖c₁‖ < 1)
  (hN : ∀ φ, φ ∈ nodeRing c₂ ↔ d.ψ φ ∈ nodeRing c₁)

lemma mem_placeIdeal_map {v : Ext C G₂} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C G₂) v)) (y : Rint c₁ G₁) :
    y ∈ placeIdeal hc₁ (d.extMap v) (d.mem_zeros_map hQ) ↔
      d.symm.icMap (d.symm_hA hN) y ∈ placeIdeal hc₂ v hQ := by
  rw [mem_placeIdeal_iff, mem_placeIdeal_iff]
  conv_lhs => rw [← d.icMap_icMap_symm hN y, coe_icMap, d.red_map]
  exact d.res_map_eq_zero_iff (red_mem_V hc₂ v _ hQ)

variable {hc₂0 : c₂ ≠ 0} {hc₁0 : c₁ ≠ 0}
  (d' : Data C (GaussTube.Inv c₁ hc₁0 G₁) (GaussTube.Inv c₂ hc₂0 G₂))
  (hN' : ∀ φ, φ ∈ nodeRing c₂ ↔ d'.ψ φ ∈ nodeRing c₁)
  (he' : ∀ y : G₂, d'.e (toInv hc₂0 y) = toInv hc₁0 (d.e y)) (hτ' : d'.τ = d.τ)

omit [IsAlgClosed C] [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂] in
include he' in
lemma rintEquiv_icMap (y : Rint c₂ G₂) :
    rintEquiv hc₁0 (d.icMap hN y) = d'.icMap hN' (rintEquiv hc₂0 y) :=
  Subtype.ext (he' y).symm

omit [IsAlgClosed C] [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂] in
include he' in
lemma rintEquiv_symm_icMap_symm (y : Rint c₁ (GaussTube.Inv c₁ hc₁0 G₁)) :
    (rintEquiv hc₂0).symm (d'.symm.icMap (d'.symm_hA hN') y) =
      d.symm.icMap (d.symm_hA hN) ((rintEquiv hc₁0).symm y) := by
  apply Subtype.ext
  change (toInv hc₂0).symm (d'.e.symm y) = d.e.symm ((toInv hc₁0).symm y)
  rw [RingEquiv.symm_apply_eq]
  apply d'.e.injective
  rw [RingEquiv.apply_symm_apply, he', RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in
-- the branch sets live in twisted fields; unfolding them is expensive
include he' hτ' hN' in
/-- **Ordinary double points are transported.** -/
theorem isNodeODP_comap {P' : Ideal (Rint c₂ G₂)} (h : IsNodeODP hc₂ hc₂0 P') :
    IsNodeODP hc₁ hc₁0 (P'.comap (d.symm.icMap (d.symm_hA hN))) := by
  obtain ⟨⟨v₁, Q₁, hQ₁⟩, ⟨w₂, Q₂, hQ₂⟩, hb₁, hb₂, hjet⟩ := h
  have hP₁ : placeIdeal hc₂ v₁ hQ₁ = P' := by
    have : (⟨v₁, Q₁, hQ₁⟩ : OuterBranch C G₂) ∈ outerBranches hc₂ P' := by rw [hb₁]; rfl
    exact this
  have hP₂ : placeIdeal hc₂ w₂ hQ₂ = P'.comap (rintEquiv hc₂0).symm.toRingHom := by
    have : (⟨w₂, Q₂, hQ₂⟩ : OuterBranch C (GaussTube.Inv c₂ hc₂0 G₂)) ∈
        innerBranches hc₂ hc₂0 P' := by
      rw [hb₂]; rfl
    exact this
  set P₁ := P'.comap (d.symm.icMap (d.symm_hA hN))
  refine ⟨d.brMap ⟨v₁, Q₁, hQ₁⟩, d'.brMap ⟨w₂, Q₂, hQ₂⟩, ?_, ?_, ?_⟩
  · -- the outer branch
    ext b
    constructor
    · intro hb
      have hb' : d.symm.brMap b ∈ outerBranches hc₂ P' := by
        obtain ⟨v, Q, hQ⟩ := b
        change placeIdeal hc₁ v hQ = P₁ at hb
        change placeIdeal hc₂ (d.symm.extMap v) (d.symm.mem_zeros_map hQ) = P'
        ext y
        rw [d.symm.mem_placeIdeal_map hc₁ hc₂ (d.symm_hA hN) hQ, hb, Ideal.mem_comap]
        have : d.symm.icMap (d.symm_hA hN)
            (d.symm.symm.icMap (d.symm.symm_hA (d.symm_hA hN)) y) = y :=
          Subtype.ext (d.e.symm_apply_apply _)
        rw [this]
      rw [hb₁, Set.mem_singleton_iff] at hb'
      rw [Set.mem_singleton_iff, ← d.brMap_brMap_symm b, hb']
    · rintro rfl
      change placeIdeal hc₁ (d.extMap v₁) (d.mem_zeros_map hQ₁) = P₁
      ext y
      rw [d.mem_placeIdeal_map hc₂ hc₁ hN hQ₁, hP₁, Ideal.mem_comap]
  · -- the inner branch
    ext b
    constructor
    · intro hb
      have hb' : d'.symm.brMap b ∈ innerBranches hc₂ hc₂0 P' := by
        obtain ⟨w, Q, hQ⟩ := b
        change placeIdeal hc₁ w hQ = P₁.comap (rintEquiv hc₁0).symm.toRingHom at hb
        change placeIdeal hc₂ (d'.symm.extMap w) (d'.symm.mem_zeros_map hQ) =
          P'.comap (rintEquiv hc₂0).symm.toRingHom
        ext y
        rw [d'.symm.mem_placeIdeal_map hc₁ hc₂ (d'.symm_hA hN') hQ, hb, Ideal.mem_comap,
          Ideal.mem_comap]
        have : d'.symm.icMap (d'.symm_hA hN')
            (d'.symm.symm.icMap (d'.symm.symm_hA (d'.symm_hA hN')) y) = y :=
          Subtype.ext (d'.e.symm_apply_apply _)
        change d.symm.icMap (d.symm_hA hN) ((rintEquiv hc₁0).symm
          (d'.symm.symm.icMap (d'.symm.symm_hA (d'.symm_hA hN')) y)) ∈ P' ↔
            (rintEquiv hc₂0).symm y ∈ P'
        rw [← d.rintEquiv_symm_icMap_symm hN d' hN' he', this]
      rw [hb₂, Set.mem_singleton_iff] at hb'
      rw [Set.mem_singleton_iff, ← d'.brMap_brMap_symm b, hb']
    · rintro rfl
      change placeIdeal hc₁ (d'.extMap w₂) (d'.mem_zeros_map hQ₂) =
        P₁.comap (rintEquiv hc₁0).symm.toRingHom
      ext y
      rw [d'.mem_placeIdeal_map hc₂ hc₁ hN' hQ₂, hP₂, Ideal.mem_comap, Ideal.mem_comap,
        Ideal.mem_comap]
      change (rintEquiv hc₂0).symm (d'.symm.icMap (d'.symm_hA hN') y) ∈ P' ↔
        d.symm.icMap (d.symm_hA hN) ((rintEquiv hc₁0).symm y) ∈ P'
      rw [d.rintEquiv_symm_icMap_symm hN d' hN' he']
  · -- the jets
    intro a ha b hb hab
    obtain ⟨a₀, rfl⟩ := (d.κmap v₁).surjective a
    obtain ⟨b₀, rfl⟩ := (d'.κmap w₂).surjective b
    have ha₀ : a₀ ∈ Q₁.V := (d.mem_placeMap (v := v₁) (Q := Q₁)).1 ha
    have hb₀ : b₀ ∈ Q₂.V := (d'.mem_placeMap (v := w₂) (Q := Q₂)).1 hb
    have hab₀ : Q₁.res a₀ = Q₂.res b₀ := by
      have := hab
      change (d.placeMap v₁ Q₁).res (d.κmap v₁ a₀) =
        (d'.placeMap w₂ Q₂).res (d'.κmap w₂ b₀) at this
      rw [d.res_placeMap ha₀, d'.res_placeMap hb₀] at this
      have h2 : τbar d'.τ d'.hτ = τbar d.τ d.hτ := by
        simp only [hτ']
      rw [h2] at this
      exact (τbar d.τ d.hτ).injective this
    obtain ⟨y, s, hs, hy₁, hy₂⟩ := hjet a₀ ha₀ b₀ hb₀ hab₀
    refine ⟨d.icMap hN y, d.icMap hN s, ?_, ?_, ?_⟩
    · rw [Ideal.mem_comap, d.icMap_symm_icMap hN]
      exact hs
    · change red C (d.e y) (d.extMap v₁) = d.κmap v₁ a₀ * red C (d.e s) (d.extMap v₁)
      rw [d.red_map, d.red_map]
      change d.κmap v₁ (redHom hc₂ v₁ y) = _ * d.κmap v₁ (redHom hc₂ v₁ s)
      rw [hy₁, map_mul]
    · change redHom hc₁ (d'.extMap w₂) (rintEquiv hc₁0 (d.icMap hN y)) =
        d'.κmap w₂ b₀ * redHom hc₁ (d'.extMap w₂) (rintEquiv hc₁0 (d.icMap hN s))
      rw [d.rintEquiv_icMap hN d' hN' he', d.rintEquiv_icMap hN d' hN' he']
      change red C (d'.e _) (d'.extMap w₂) = _ * red C (d'.e _) (d'.extMap w₂)
      rw [d'.red_map, d'.red_map]
      change d'.κmap w₂ (redHomInv hc₂ hc₂0 w₂ y) = _ * d'.κmap w₂ (redHomInv hc₂ hc₂0 w₂ s)
      rw [hy₂, map_mul]

end Node

end Data

/-! ### Change of representative -/

section Representative

open AffineTwist DiscCount

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

/-- **Transport data for a change of representative** `t' = (x - a')/c'` of the same open disc
`|x - a| < |c|`. -/
noncomputable def repData {a a' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0) (h1 : ‖c‖ = ‖c'‖)
    (h2 : ‖a - a'‖ < ‖c‖) : Data C (Aff a c hc F) (Aff a' c' hc' F) where
  τ := RingEquiv.refl C
  hτ _ := rfl
  ψ := ((aff a' c' hc').trans (aff a c hc).symm).toRingEquiv
  ψC c₀ := by
    change ((aff a' c' hc').trans (aff a c hc).symm) (algebraMap C (RatFunc C) c₀) = _
    rw [AlgEquiv.commutes]
    rfl
  ψg φ := by
    change gauss1 C ((aff a c hc).symm (aff a' c' hc' φ)) = gauss1 C φ
    rw [gauss1_aff_symm hc, ← gaussRat_aff (a := a') hc' φ]
    have hr : Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc) =
        Units.mk0 ‖c'‖₊ (nnnorm_ne_zero_iff.2 hc') := Units.ext (NNReal.eq (by simpa using h1))
    have hle : NormedField.valuation (a - a') ≤
        ((Units.mk0 ‖c'‖₊ (nnnorm_ne_zero_iff.2 hc') : ℝ≥0ˣ) : ℝ≥0) := by
      rw [NormedField.valuation_apply, Units.val_mk0]
      exact_mod_cast (show ‖a - a'‖ ≤ ‖c'‖ from h1 ▸ h2.le)
    rw [hr, Splitting.gaussRat_eq_of_le hle]
  α := c' / c
  γ := (a' - a) / c
  hα := by rw [norm_div, h1, div_self (norm_ne_zero_iff.2 hc')]
  hγ := by
    rw [norm_div, div_lt_one (norm_pos_iff.2 hc), norm_sub_rev]
    exact h2
  ψX := by
    change ((aff a c hc).trans (aff a' c' hc').symm) RatFunc.X = _
    apply (aff a' c' hc').injective
    change aff a' c' hc' ((aff a' c' hc').symm (aff a c hc RatFunc.X)) = _
    rw [AlgEquiv.apply_symm_apply, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes,
      aff_apply, aff_apply, affHom_X, affHom_X, gaussCoord_eq, gaussCoord_eq]
    have h0 : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
    have h0' : algebraMap C (RatFunc C) c' ≠ 0 := by simpa using hc'
    simp only [map_inv₀, map_div₀, _root_.map_sub]
    field_simp
    ring
  e := (toAff hc').symm.trans (toAff hc)
  he φ := by
    change toAff hc (algebraMap (RatFunc C) F (aff a' c' hc' φ)) =
      toAff hc (algebraMap (RatFunc C) F (aff a c hc ((aff a c hc).symm (aff a' c' hc' φ))))
    rw [AlgEquiv.apply_symm_apply]

/-- **Smoothness over an open disc does not depend on the representative.** -/
theorem discGood_of_ball_eq {a a' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ball a ‖c‖ = ball a' ‖c'‖) (h' : DiscGood F a' hc') : DiscGood F a hc := by
  obtain ⟨h1, h2⟩ := (BallTree.ball_eq_ball_iff' hc hc').1 h
  exact (repData (F := F) hc hc' h1 h2).discGoodAt_transport h'

theorem discGood_iff_of_ball_eq {a a' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ball a ‖c‖ = ball a' ‖c'‖) : DiscGood F a hc ↔ DiscGood F a' hc' :=
  ⟨discGood_of_ball_eq hc' hc h.symm, discGood_of_ball_eq hc hc' h⟩

/-- `BallGood` is `DiscGood` for any representative. -/
theorem ballGood_iff {a c : C} (hc : c ≠ 0) : BallGood F (ball a ‖c‖) ↔ DiscGood F a hc :=
  ⟨fun h ↦ h a c hc rfl, fun h _ _ hc' h' ↦ (discGood_iff_of_ball_eq hc hc' h').1 h⟩

end Representative

end Transport

end S8A

end SemistableReduction
