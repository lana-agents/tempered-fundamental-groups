/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Equivariance
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
open scoped NNReal Polynomial

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

omit [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂] in
omit [IsAlgClosed C] in
/-- `ψ` maps node charts to node charts as soon as it maps their generators. -/
lemma ψ_mem_nodeRing {c₂ c₁ : C} (hX : d.ψ RatFunc.X ∈ nodeRing c₁)
    (hY : d.ψ (algebraMap C (RatFunc C) c₂ / RatFunc.X) ∈ nodeRing c₁) {φ : RatFunc C}
    (hφ : φ ∈ nodeRing c₂) : d.ψ φ ∈ nodeRing c₁ := by
  rw [nodeRing, nodeChart] at hφ
  induction hφ using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨o, ho, rfl⟩ | hz
    · rw [d.ψC]
      refine algebraMap_mem_nodeRing ?_
      rw [d.hτ]
      exact (HenselComplete.mem_integers_iff _).1 ho
    · rcases hz with rfl | hz
      · exact hX
      · rw [Set.mem_singleton_iff.1 hz]
        exact hY
  | zero => simp
  | one => simp
  | add _ _ _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg _ _ ha => rw [_root_.map_neg]; exact neg_mem ha
  | mul _ _ _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

omit [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂] in
omit [IsAlgClosed C] in
lemma chartHom_mem_tubeIdeal_iff {s : ℝ≥0ˣ} (hs₂ : s ∈ segment c₂) (hs₁ : s ∈ segment c₁)
    (hws : ∀ φ, gaussRat (NormedField.valuation (K := C)) 0 s (d.ψ φ) =
      gaussRat (NormedField.valuation (K := C)) 0 s φ) (φ : nodeRing c₂) :
    d.chartHom hN φ ∈ tubeIdeal c₁ ↔ φ ∈ tubeIdeal c₂ := by
  rw [mem_tubeIdeal_iff _ hs₁, mem_tubeIdeal_iff _ hs₂]
  change gaussRat _ 0 s (d.ψ φ) < 1 ↔ _
  rw [hws]

include he' hτ' hN' hN in
/-- **Exhausting discs are transported.** -/
theorem exhausting_transport {s : ℝ≥0ˣ} (hs₂ : s ∈ segment c₂) (hs₁ : s ∈ segment c₁)
    (hws : ∀ φ, gaussRat (NormedField.valuation (K := C)) 0 s (d.ψ φ) =
      gaussRat (NormedField.valuation (K := C)) 0 s φ)
    (h : ∀ P' : Ideal (Rint c₂ G₂), P'.IsMaximal →
      P'.comap (algebraMap (nodeRing c₂) (Rint c₂ G₂)) = tubeIdeal c₂ → IsNodeODP hc₂ hc₂0 P') :
    ∀ P' : Ideal (Rint c₁ G₁), P'.IsMaximal →
      P'.comap (algebraMap (nodeRing c₁) (Rint c₁ G₁)) = tubeIdeal c₁ →
        IsNodeODP hc₁ hc₁0 P' := by
  intro P₁ hmax hP₁
  set P := P₁.comap (d.icMap hN)
  have hsurj : Function.Surjective (d.icMap hN) := fun y ↦ ⟨_, d.icMap_icMap_symm hN y⟩
  haveI : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hP : P.comap (algebraMap (nodeRing c₂) (Rint c₂ G₂)) = tubeIdeal c₂ := by
    ext φ
    rw [Ideal.mem_comap, Ideal.mem_comap, ← d.chartHom_mem_tubeIdeal_iff hN hs₂ hs₁ hws, ← hP₁,
      Ideal.mem_comap]
    have : d.icMap hN (algebraMap (nodeRing c₂) (Rint c₂ G₂) φ) =
        algebraMap (nodeRing c₁) (Rint c₁ G₁) (d.chartHom hN φ) :=
      Subtype.ext (d.he φ)
    rw [this]
  have := d.isNodeODP_comap hc₂ hc₁ hN d' hN' he' hτ' (h P inferInstance hP)
  have hPP : P.comap (d.symm.icMap (d.symm_hA hN)) = P₁ := by
    ext y
    rw [Ideal.mem_comap, Ideal.mem_comap, d.icMap_icMap_symm]
  rwa [hPP] at this

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

/-! ### Rescaling node charts -/

section Rescale

open GaussTube

lemma isExhausting_congr {a c₁ c₂ c₁' c₂' : C} (h1 : c₁ = c₂) (h2 : c₁' = c₂') (hc₁ : c₁ ≠ 0)
    (hc₂ : c₂ ≠ 0) (hc₁' : ‖c₁'‖ < 1) (hc₂' : ‖c₂'‖ < 1) (hc₁0' : c₁' ≠ 0) (hc₂0' : c₂' ≠ 0) :
    IsExhausting a hc₁ hc₁' hc₁0' F ↔ IsExhausting a hc₂ hc₂' hc₂0' F := by
  subst h1
  subst h2
  rfl

variable {a c c' l : C} (hc : c ≠ 0) (hl : ‖l‖ = 1)

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma ne_zero_of_norm_eq_one {l : C} (hl : ‖l‖ = 1) : l ≠ 0 := by
  rintro rfl
  simp at hl

/-- The rescaling data `t ↦ t / l` (outer side). -/
noncomputable def rescaleData :
    Data C (Aff a (c * l) (mul_ne_zero hc (ne_zero_of_norm_eq_one hl)) F)
    (Aff a c hc F) :=
  repData (F := F) (mul_ne_zero hc (ne_zero_of_norm_eq_one hl)) hc
    (by rw [norm_mul, hl, mul_one])
    (by
      rw [sub_self, norm_zero, norm_mul, hl, mul_one]
      exact norm_pos_iff.2 hc)

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] in
lemma rescaleData_ψ_X : (rescaleData (F := F) (a := a) hc hl).ψ RatFunc.X =
    algebraMap C (RatFunc C) l * RatFunc.X := by
  have hl0 := ne_zero_of_norm_eq_one hl
  change (aff a (c * l) (mul_ne_zero hc hl0)).symm (aff a c hc RatFunc.X) = _
  rw [AlgEquiv.symm_apply_eq, map_mul, AlgEquiv.commutes, aff_apply, aff_apply, affHom_X,
    affHom_X, gaussCoord_eq, gaussCoord_eq]
  have h0 : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
  have h0' : algebraMap C (RatFunc C) l ≠ 0 := by simpa using hl0
  simp only [map_inv₀, map_mul]
  field_simp

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] in
lemma rescaleData_symm_ψ_X : (rescaleData (F := F) (a := a) hc hl).ψ.symm RatFunc.X =
    algebraMap C (RatFunc C) l⁻¹ * RatFunc.X := by
  have hl0 := ne_zero_of_norm_eq_one hl
  rw [RingEquiv.symm_apply_eq, map_mul, (rescaleData hc hl).ψC, rescaleData_ψ_X]
  change _ = algebraMap C (RatFunc C) l⁻¹ * (algebraMap C (RatFunc C) l * RatFunc.X)
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hl0, map_one, one_mul]

variable {hc0' : c' ≠ 0}

omit [IsAlgClosed C] in
lemma aff_inv_rescale (φ : RatFunc C) :
    aff a c hc (GaussTube.inv hc0' φ) =
      aff a (c * l) (mul_ne_zero hc (ne_zero_of_norm_eq_one hl))
        (GaussTube.inv (div_ne_zero hc0' (ne_zero_of_norm_eq_one hl)) φ) := by
  have hl0 := ne_zero_of_norm_eq_one hl
  refine congrArg (fun f : RatFunc C →ₐ[C] RatFunc C ↦ f φ)
    (ratFunc_algHom_ext (φ := ((aff a c hc).toAlgHom.comp (GaussTube.inv hc0').toAlgHom))
    (ψ := ((aff a (c * l) (mul_ne_zero hc hl0)).toAlgHom.comp
      (GaussTube.inv (div_ne_zero hc0' hl0)).toAlgHom)) ?_)
  change aff a c hc (GaussTube.inv hc0' RatFunc.X) =
    aff a (c * l) (mul_ne_zero hc hl0) (GaussTube.inv (div_ne_zero hc0' hl0) RatFunc.X)
  rw [GaussTube.inv_apply, GaussTube.inv_apply, GaussTube.invHom_X, GaussTube.invHom_X,
    map_div₀, map_div₀, AlgEquiv.commutes, AlgEquiv.commutes, aff_apply, aff_apply, affHom_X,
    affHom_X, gaussCoord_eq, gaussCoord_eq]
  have h0 : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
  have h0' : algebraMap C (RatFunc C) l ≠ 0 := by simpa using hl0
  simp only [map_inv₀, map_mul, map_div₀]
  field_simp

/-- The rescaling data, inner side (the identity: both inversions give the coordinate `c'/t`). -/
noncomputable def rescaleDataInv :
    Data C (GaussTube.Inv (c' / l) (div_ne_zero hc0' (ne_zero_of_norm_eq_one hl))
      (Aff a (c * l) (mul_ne_zero hc (ne_zero_of_norm_eq_one hl)) F))
      (GaussTube.Inv c' hc0' (Aff a c hc F)) where
  τ := RingEquiv.refl C
  hτ _ := rfl
  ψ := RingEquiv.refl _
  ψC _ := rfl
  ψg _ := rfl
  α := 1
  γ := 0
  hα := norm_one
  hγ := by simp
  ψX := by simp
  e := (GaussTube.toInv hc0').symm.trans ((toAff hc).symm.trans
    ((toAff (mul_ne_zero hc (ne_zero_of_norm_eq_one hl))).trans
      (GaussTube.toInv (div_ne_zero hc0' (ne_zero_of_norm_eq_one hl)))))
  he φ := by
    change algebraMap (RatFunc C) F (aff a c hc (GaussTube.inv hc0' φ)) =
      algebraMap (RatFunc C) F (aff a (c * l) _ (GaussTube.inv _ φ))
    rw [aff_inv_rescale hc hl]

omit [IsAlgClosed C] in
lemma nodeRing_le {d₁ d₂ w : C} (hw : ‖w‖ ≤ 1) (hd : d₁ = w * d₂) : nodeRing d₁ ≤ nodeRing d₂ := by
  refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
  · exact fun z hz ↦ ZariskiModel.baseRing_le_nodeChart hz
  · rintro z (rfl | hz)
    · exact X_mem_nodeRing d₂
    · rw [Set.mem_singleton_iff.1 hz, hd, map_mul, mul_div_assoc]
      exact mul_mem (algebraMap_mem_nodeRing hw) (div_X_mem_nodeRing d₂)

omit [IsAlgClosed C] in
lemma nodeRing_eq {c₁ c₂ u : C} (hu : ‖u‖ = 1) (h : c₁ = u * c₂) : nodeRing c₁ = nodeRing c₂ := by
  have hu0 := ne_zero_of_norm_eq_one hu
  exact le_antisymm (nodeRing_le hu.le h) (nodeRing_le (w := u⁻¹)
    (by rw [norm_inv, hu, inv_one]) (by rw [h, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]))

set_option maxHeartbeats 1600000 in
-- unfolding the rescaling data
omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] in
lemma gaussRat_rescale (s : ℝ≥0ˣ) (φ : RatFunc C) :
    gaussRat (NormedField.valuation (K := C)) 0 s ((rescaleData (F := F) (a := a) hc hl).ψ φ) =
      gaussRat (NormedField.valuation (K := C)) 0 s φ := by
  have hl0 := ne_zero_of_norm_eq_one hl
  have h := valuation_ratFunc_ext_of_linear
    (w₁ := (gaussRat (NormedField.valuation (K := C)) 0 s).comap
      (rescaleData (F := F) (a := a) hc hl).ψ.toRingHom)
    (w₂ := gaussRat (NormedField.valuation (K := C)) 0 s) (fun e ↦ ?_) (fun b ↦ ?_)
  · exact congrArg (fun w : Valuation (RatFunc C) ℝ≥0 ↦ w φ) h
  · rw [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      (rescaleData (F := F) (a := a) hc hl).ψC]
    rfl
  · rw [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have hXb : algebraMap C[X] (RatFunc C) (Polynomial.X - Polynomial.C b) =
        RatFunc.X - algebraMap C (RatFunc C) b := by
      rw [_root_.map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C]
    have hlin : algebraMap C (RatFunc C) l * RatFunc.X - algebraMap C (RatFunc C) b =
        algebraMap C (RatFunc C) l *
          algebraMap C[X] (RatFunc C) (Polynomial.X - Polynomial.C (b / l)) := by
      rw [_root_.map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C, mul_sub, ← map_mul,
        mul_div_cancel₀ _ hl0]
    rw [hXb, _root_.map_sub, rescaleData_ψ_X, (rescaleData (F := F) (a := a) hc hl).ψC, ← hXb]
    change gaussRat _ 0 s (algebraMap C (RatFunc C) l * RatFunc.X -
      algebraMap C (RatFunc C) b) = _
    rw [hlin, map_mul, gaussRat_algebraMap_C, gaussRat_algebraMap, gaussRat_algebraMap,
      gauss_X_sub_C, gauss_X_sub_C, NormedField.valuation_apply, NormedField.valuation_apply,
      NormedField.valuation_apply, zero_sub, zero_sub, nnnorm_neg, nnnorm_neg, nnnorm_div]
    have : ‖l‖₊ = 1 := by ext; exact hl
    rw [this, one_mul, div_one]

/-- **Rescaling of node charts**: `O_C[t, c'/t]` (`t = (x - a)/c`) is also the node chart of
`t / l` with parameter `c' / l` (`|l| = 1`). -/
theorem isExhausting_of_rescale (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0)
    (h : IsExhausting a hc hc' hc0' F) :
    IsExhausting a (mul_ne_zero hc (ne_zero_of_norm_eq_one hl))
      (c' := c' / l) (by rw [norm_div, hl, div_one]; exact hc')
      (div_ne_zero hc0' (ne_zero_of_norm_eq_one hl)) F := by
  have hl0 := ne_zero_of_norm_eq_one hl
  set d := rescaleData (F := F) (a := a) hc hl
  have hl1 : ‖l‖ ≤ 1 := hl.le
  have hli : ‖l⁻¹‖ ≤ 1 := by rw [norm_inv, hl, inv_one]
  have hN : ∀ φ, φ ∈ nodeRing c' ↔ d.ψ φ ∈ nodeRing (c' / l) := by
    intro φ
    constructor
    · refine d.ψ_mem_nodeRing ?_ ?_
      · rw [rescaleData_ψ_X]
        exact mul_mem (algebraMap_mem_nodeRing hl1) (X_mem_nodeRing _)
      · rw [map_div₀, d.ψC, rescaleData_ψ_X]
        change algebraMap C (RatFunc C) c' / (algebraMap C (RatFunc C) l * RatFunc.X) ∈ _
        rw [div_mul_eq_div_div, ← map_div₀]
        exact div_X_mem_nodeRing _
    · intro hφ
      have := d.symm.ψ_mem_nodeRing (c₂ := c' / l) (c₁ := c') ?_ ?_ hφ
      · rwa [show d.symm.ψ (d.ψ φ) = φ from d.ψ.symm_apply_apply φ] at this
      · change d.ψ.symm RatFunc.X ∈ _
        rw [rescaleData_symm_ψ_X]
        exact mul_mem (algebraMap_mem_nodeRing hli) (X_mem_nodeRing _)
      · change d.ψ.symm (algebraMap C (RatFunc C) (c' / l) / RatFunc.X) ∈ _
        rw [map_div₀, rescaleData_symm_ψ_X]
        have : d.ψ.symm (algebraMap C (RatFunc C) (c' / l)) =
            algebraMap C (RatFunc C) (c' / l) := d.symm.ψC _
        have hcc : c' / l / l⁻¹ = c' := by field_simp
        rw [this, div_mul_eq_div_div, ← map_div₀, hcc]
        exact div_X_mem_nodeRing _
  have hN' : ∀ φ, φ ∈ nodeRing c' ↔
      (rescaleDataInv (F := F) (a := a) hc hl (hc0' := hc0')).ψ φ ∈ nodeRing (c' / l) := by
    intro φ
    change φ ∈ nodeRing c' ↔ φ ∈ nodeRing (c' / l)
    rw [nodeRing_eq (u := l⁻¹) (by rw [norm_inv, hl, inv_one]) (div_eq_inv_mul c' l)]
  -- a radius of the open segment
  obtain ⟨s, hs₂, hs₁⟩ : ∃ s : ℝ≥0ˣ, s ∈ segment c' ∧ s ∈ segment (c' / l) := by
    have hlt : (‖c'‖₊ : ℝ) < 1 := by simpa using hc'
    have h1 : ‖c'‖₊ < (‖c'‖₊ + 1) / 2 := by
      rw [← NNReal.coe_lt_coe]; push_cast; linarith
    have h2 : (‖c'‖₊ + 1) / 2 < 1 := by
      rw [← NNReal.coe_lt_coe]; push_cast; linarith
    have hn : ‖c' / l‖₊ = ‖c'‖₊ := by
      rw [nnnorm_div]
      have : ‖l‖₊ = 1 := by ext; exact hl
      rw [this, div_one]
    refine ⟨Units.mk0 ((‖c'‖₊ + 1) / 2) (by positivity), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [Units.val_mk0]
    · exact h1
    · exact h2
    · rw [hn]; exact h1
    · exact h2
  exact d.exhausting_transport hc' (by rw [norm_div, hl, div_one]; exact hc') hN
    (rescaleDataInv (F := F) (a := a) hc hl (hc0' := hc0')) hN' (fun _ ↦ rfl) rfl hs₂ hs₁
    (gaussRat_rescale hc hl s) h

/-- **Rescaling of node charts**, both directions. -/
theorem isExhausting_iff_of_rescale (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0) :
    IsExhausting a hc hc' hc0' F ↔
      IsExhausting a (mul_ne_zero hc (ne_zero_of_norm_eq_one hl))
        (c' := c' / l) (by rw [norm_div, hl, div_one]; exact hc')
        (div_ne_zero hc0' (ne_zero_of_norm_eq_one hl)) F := by
  have hl0 := ne_zero_of_norm_eq_one hl
  have hli : ‖l⁻¹‖ = 1 := by rw [norm_inv, hl, inv_one]
  refine ⟨isExhausting_of_rescale hc hl hc' hc0', fun h ↦ ?_⟩
  have := isExhausting_of_rescale (mul_ne_zero hc hl0) hli _ _ h
  exact (isExhausting_congr (by field_simp) (by field_simp) _ _ _ _ _ _).1 this

end Rescale

/-! ### Isomorphisms over `C(x)` -/

section Iso

open GaussTube

variable {G₁ G₂ : Type*} [Field G₁] [Field G₂] [Algebra (RatFunc C) G₁] [Algebra (RatFunc C) G₂]
  [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂]
  (e : G₂ ≃+* G₁) (he : ∀ φ, e (algebraMap (RatFunc C) G₂ φ) = algebraMap (RatFunc C) G₁ φ)

/-- Transport data of an isomorphism over `C(x)`. -/
noncomputable def idData : Data C G₁ G₂ where
  τ := RingEquiv.refl C
  hτ _ := rfl
  ψ := RingEquiv.refl _
  ψC _ := rfl
  ψg _ := rfl
  α := 1
  γ := 0
  hα := norm_one
  hγ := by simp
  ψX := by simp
  e := e
  he := he

/-- Transport data of an isomorphism over `C(x)`, on the inversions. -/
noncomputable def idDataInv {c : C} (hc0 : c ≠ 0) :
    Data C (GaussTube.Inv c hc0 G₁) (GaussTube.Inv c hc0 G₂) where
  τ := RingEquiv.refl C
  hτ _ := rfl
  ψ := RingEquiv.refl _
  ψC _ := rfl
  ψg _ := rfl
  α := 1
  γ := 0
  hα := norm_one
  hγ := by simp
  ψX := by simp
  e := (toInv hc0).symm.trans (e.trans (toInv hc0))
  he φ := by
    change toInv hc0 (e (algebraMap (RatFunc C) G₂ (GaussTube.inv hc0 φ))) =
      toInv hc0 (algebraMap (RatFunc C) G₁ (GaussTube.inv hc0 φ))
    rw [he]

include he in
/-- **Node points are invariant under isomorphisms over `C(x)`.** -/
theorem nodeODP_transport_id {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)
    (h : ∀ P' : Ideal (Rint c G₂), P'.IsMaximal →
      P'.comap (algebraMap (nodeRing c) (Rint c G₂)) = tubeIdeal c → IsNodeODP hc hc0 P') :
    ∀ P' : Ideal (Rint c G₁), P'.IsMaximal →
      P'.comap (algebraMap (nodeRing c) (Rint c G₁)) = tubeIdeal c → IsNodeODP hc hc0 P' := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0ˣ, s ∈ segment c := by
    have hlt : (‖c‖₊ : ℝ) < 1 := by simpa using hc
    refine ⟨Units.mk0 ((‖c‖₊ + 1) / 2) (by positivity), ?_, ?_⟩ <;> simp only [Units.val_mk0] <;>
      rw [← NNReal.coe_lt_coe] <;> push_cast <;> linarith
  exact (idData e he).exhausting_transport hc hc (fun _ ↦ Iff.rfl) (idDataInv e he hc0)
    (fun _ ↦ Iff.rfl) (fun _ ↦ rfl) rfl hs hs (fun _ ↦ rfl) h

end Iso

end Representative

/-! ### Semilinear automorphisms -/

section Semilinear

open GaussTube AffineTwist DiscCount

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma ratFuncMap_comp_apply (τ₁ τ₂ : C →+* C) (φ : RatFunc C) :
    ratFuncMap τ₂ (ratFuncMap τ₁ φ) = ratFuncMap (τ₂.comp τ₁) φ := by
  induction φ using RatFunc.induction_on with
  | f p q hq =>
    simp only [map_div₀, ratFuncMap_algebraMap, Polynomial.map_map]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma ratFuncMap_id (φ : RatFunc C) : ratFuncMap (RingHom.id C) φ = φ := by
  induction φ using RatFunc.induction_on with
  | f p q hq => rw [map_div₀, ratFuncMap_algebraMap, ratFuncMap_algebraMap, Polynomial.map_id,
      Polynomial.map_id]

/-- The automorphism of `C(x)` acting by `τ` on coefficients. -/
noncomputable def ratFuncEquiv (τ : C ≃+* C) : RatFunc C ≃+* RatFunc C :=
  RingEquiv.ofRingHom (ratFuncMap τ.toRingHom) (ratFuncMap τ.symm.toRingHom)
    (RingHom.ext fun φ ↦ by
      change ratFuncMap _ (ratFuncMap _ φ) = φ
      rw [ratFuncMap_comp_apply]
      convert ratFuncMap_id φ
      ext; simp)
    (RingHom.ext fun φ ↦ by
      change ratFuncMap _ (ratFuncMap _ φ) = φ
      rw [ratFuncMap_comp_apply]
      convert ratFuncMap_id φ
      ext; simp)

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma ratFuncEquiv_apply (τ : C ≃+* C) (φ : RatFunc C) :
    ratFuncEquiv τ φ = ratFuncMap τ.toRingHom φ := rfl

/-- A ring automorphism of `C(x)` acting by an isometry on `C` and fixing `x` preserves every
Gauss point `w_{0,s}`. -/
lemma gaussRat_zero_comp {τ : C ≃+* C} (hτ : ∀ z, ‖τ z‖ = ‖z‖) {ψ : RatFunc C ≃+* RatFunc C}
    (hψC : ∀ c, ψ (algebraMap C (RatFunc C) c) = algebraMap C (RatFunc C) (τ c))
    (hψX : ψ RatFunc.X = RatFunc.X) (s : ℝ≥0ˣ) (φ : RatFunc C) :
    gaussRat (NormedField.valuation (K := C)) 0 s (ψ φ) =
      gaussRat (NormedField.valuation (K := C)) 0 s φ := by
  have h := valuation_ratFunc_ext_of_linear
    (w₁ := (gaussRat (NormedField.valuation (K := C)) 0 s).comap ψ.toRingHom)
    (w₂ := gaussRat (NormedField.valuation (K := C)) 0 s) (fun e ↦ ?_) (fun b ↦ ?_)
  · exact congrArg (fun w : Valuation (RatFunc C) ℝ≥0 ↦ w φ) h
  · rw [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hψC,
      gaussRat_algebraMap_C, gaussRat_algebraMap_C, NormedField.valuation_apply,
      NormedField.valuation_apply]
    exact NNReal.eq (by simpa using hτ e)
  · rw [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have hXb : ∀ b' : C, algebraMap C[X] (RatFunc C) (Polynomial.X - Polynomial.C b') =
        RatFunc.X - algebraMap C (RatFunc C) b' := fun b' ↦ by
      rw [_root_.map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C]
    rw [hXb, _root_.map_sub, hψX, hψC, ← hXb (τ b), ← hXb b, gaussRat_algebraMap,
      gaussRat_algebraMap, gauss_X_sub_C, gauss_X_sub_C, NormedField.valuation_apply,
      NormedField.valuation_apply,
      zero_sub, zero_sub, nnnorm_neg, nnnorm_neg]
    congr 1
    exact NNReal.eq (by simpa using hτ b)

/-- Transport data from an automorphism of `C(x)` fixing `x`. -/
noncomputable def Data.mkX {G₁ G₂ : Type*} [Field G₁] [Field G₂] [Algebra (RatFunc C) G₁]
    [Algebra (RatFunc C) G₂] (τ : C ≃+* C) (hτ : ∀ z, ‖τ z‖ = ‖z‖) (ψ : RatFunc C ≃+* RatFunc C)
    (hψC : ∀ c, ψ (algebraMap C (RatFunc C) c) = algebraMap C (RatFunc C) (τ c))
    (hψX : ψ RatFunc.X = RatFunc.X) (e : G₂ ≃+* G₁)
    (he : ∀ φ, e (algebraMap (RatFunc C) G₂ φ) = algebraMap (RatFunc C) G₁ (ψ φ)) :
    Data C G₁ G₂ where
  τ := τ
  hτ := hτ
  ψ := ψ
  ψC := hψC
  ψg := gaussRat_zero_comp hτ hψC hψX 1
  α := 1
  γ := 0
  hα := norm_one
  hγ := by simp
  ψX := by
    rw [map_one, one_mul, map_zero, add_zero, RingEquiv.symm_apply_eq, hψX]
  e := e
  he := he

lemma Data.mkX_ψ {G₁ G₂ : Type*} [Field G₁] [Field G₂] [Algebra (RatFunc C) G₁]
    [Algebra (RatFunc C) G₂] (τ : C ≃+* C) (hτ : ∀ z, ‖τ z‖ = ‖z‖) (ψ : RatFunc C ≃+* RatFunc C)
    (hψC) (hψX) (e : G₂ ≃+* G₁) (he) :
    (Data.mkX (G₁ := G₁) (G₂ := G₂) τ hτ ψ hψC hψX e he).ψ = ψ := rfl

/-- Node charts are preserved by an automorphism fixing `x`. -/
lemma mem_nodeRing_iff_of_X {τ : C ≃+* C} (hτ : ∀ z, ‖τ z‖ = ‖z‖) {ψ : RatFunc C ≃+* RatFunc C}
    (hψC : ∀ c, ψ (algebraMap C (RatFunc C) c) = algebraMap C (RatFunc C) (τ c))
    (hψX : ψ RatFunc.X = RatFunc.X) (c : C) (φ : RatFunc C) :
    φ ∈ nodeRing c ↔ ψ φ ∈ nodeRing (τ c) := by
  set d := Data.mkX (G₁ := RatFunc C) (G₂ := RatFunc C) τ hτ ψ hψC hψX ψ (fun _ ↦ rfl)
  constructor
  · refine d.ψ_mem_nodeRing (c₂ := c) ?_ ?_
    · change ψ RatFunc.X ∈ _
      rw [hψX]; exact X_mem_nodeRing _
    · change ψ _ ∈ _
      rw [map_div₀, hψC, hψX]; exact div_X_mem_nodeRing _
  · intro h
    have hψX' : ψ.symm RatFunc.X = RatFunc.X := by rw [RingEquiv.symm_apply_eq, hψX]
    have := d.symm.ψ_mem_nodeRing (c₂ := τ c) (c₁ := c) ?_ ?_ h
    · rwa [show d.symm.ψ (ψ φ) = φ from ψ.symm_apply_apply φ] at this
    · change ψ.symm RatFunc.X ∈ _
      rw [hψX']; exact X_mem_nodeRing _
    · change ψ.symm _ ∈ _
      have : ψ.symm (algebraMap C (RatFunc C) (τ c)) = algebraMap C (RatFunc C) c := by
        rw [RingEquiv.symm_apply_eq, hψC]
      rw [map_div₀, this, hψX']; exact div_X_mem_nodeRing _

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  {τ : C ≃+* C} (hτ : ∀ z, ‖τ z‖ = ‖z‖) {σ : F ≃+* F} (hσ : IsSemilinear C F τ σ)

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma τ_ne_zero (τ : C ≃+* C) {c : C} (hc : c ≠ 0) : τ c ≠ 0 := by
  simpa using hc

/-- The automorphism of `C(x)` induced by `σ` in the coordinates `(x - a)/c` and
`(x - τ a)/τ c`. -/
noncomputable def affψ {a c : C} (hc : c ≠ 0) : RatFunc C ≃+* RatFunc C :=
  (aff a c hc).toRingEquiv.trans ((ratFuncEquiv τ).trans
    (aff (τ a) (τ c) (τ_ne_zero τ hc)).symm.toRingEquiv)

omit [IsAlgClosed C] in
lemma affψ_C {a c : C} (hc : c ≠ 0) (b : C) :
    affψ (τ := τ) (a := a) hc (algebraMap C (RatFunc C) b) = algebraMap C (RatFunc C) (τ b) := by
  change (aff (τ a) (τ c) (τ_ne_zero τ hc)).symm (ratFuncMap τ.toRingHom (aff a c hc _)) = _
  rw [AlgEquiv.commutes, ratFuncMap_algebraMap_C, AlgEquiv.symm_apply_eq, AlgEquiv.commutes]
  rfl

omit [IsAlgClosed C] in
lemma affψ_X {a c : C} (hc : c ≠ 0) : affψ (τ := τ) (a := a) hc RatFunc.X = RatFunc.X := by
  change (aff (τ a) (τ c) (τ_ne_zero τ hc)).symm (ratFuncMap τ.toRingHom (aff a c hc RatFunc.X)) = _
  rw [AlgEquiv.symm_apply_eq, aff_apply, aff_apply, affHom_X, affHom_X, ratFuncMap_gaussCoord]
  rfl

include hτ hσ in
/-- **Transport data of a semilinear automorphism** on the twisted vertex charts. -/
noncomputable def semData {a c : C} (hc : c ≠ 0) :
    Data C (Aff (τ a) (τ c) (τ_ne_zero τ hc) F) (Aff a c hc F) :=
  Data.mkX τ hτ (affψ (τ := τ) (a := a) hc) (affψ_C (τ := τ) (a := a) hc)
    (affψ_X (τ := τ) (a := a) hc)
    ((toAff hc).symm.trans (σ.trans (toAff (τ_ne_zero τ hc))))
    (fun φ ↦ by
      change toAff (τ_ne_zero τ hc) (σ (algebraMap (RatFunc C) F (aff a c hc φ))) =
        toAff (τ_ne_zero τ hc) (algebraMap (RatFunc C) F (aff (τ a) (τ c) (τ_ne_zero τ hc)
          ((aff (τ a) (τ c) (τ_ne_zero τ hc)).symm
          (ratFuncMap τ.toRingHom (aff a c hc φ)))))
      rw [hσ, AlgEquiv.apply_symm_apply])

include hτ hσ in
/-- **Smoothness over open discs is transported by semilinear automorphisms.** -/
theorem discGood_semilinear {a c : C} (hc : c ≠ 0) (h : DiscGood F a hc) :
    DiscGood F (τ a) (τ_ne_zero τ hc) :=
  (semData hτ hσ hc).discGoodAt_transport h

/-- The automorphism of `C(x)` induced by `σ` in the inverted coordinates `c'/t`. -/
noncomputable def invψ {a c c' : C} (hc : c ≠ 0) (hc0' : c' ≠ 0) : RatFunc C ≃+* RatFunc C :=
  (GaussTube.inv hc0').toRingEquiv.trans ((affψ (τ := τ) (a := a) hc).trans
    (GaussTube.inv (τ_ne_zero τ hc0')).symm.toRingEquiv)

omit [IsAlgClosed C] in
lemma invψ_C {a c c' : C} (hc : c ≠ 0) (hc0' : c' ≠ 0) (b : C) :
    invψ (τ := τ) (a := a) hc hc0' (algebraMap C (RatFunc C) b) =
      algebraMap C (RatFunc C) (τ b) := by
  change (GaussTube.inv (τ_ne_zero τ hc0')).symm
    (affψ (τ := τ) (a := a) hc (GaussTube.inv hc0' _)) = _
  rw [AlgEquiv.commutes, affψ_C (τ := τ) (a := a), AlgEquiv.symm_apply_eq, AlgEquiv.commutes]

omit [IsAlgClosed C] in
lemma invψ_X {a c c' : C} (hc : c ≠ 0) (hc0' : c' ≠ 0) :
    invψ (τ := τ) (a := a) hc hc0' RatFunc.X = RatFunc.X := by
  change (GaussTube.inv (τ_ne_zero τ hc0')).symm
    (affψ (τ := τ) (a := a) hc (GaussTube.inv hc0' RatFunc.X)) = _
  rw [AlgEquiv.symm_apply_eq, GaussTube.inv_apply, GaussTube.inv_apply, GaussTube.invHom_X,
    GaussTube.invHom_X, map_div₀, affψ_C (τ := τ) (a := a), affψ_X (τ := τ) (a := a)]

include hτ hσ in
/-- Transport data of a semilinear automorphism on the inverted twisted charts. -/
noncomputable def semDataInv {a c c' : C} (hc : c ≠ 0) (hc0' : c' ≠ 0) :
    Data C (GaussTube.Inv (τ c') (τ_ne_zero τ hc0') (Aff (τ a) (τ c) (τ_ne_zero τ hc) F))
      (GaussTube.Inv c' hc0' (Aff a c hc F)) :=
  Data.mkX τ hτ (invψ hc hc0') (invψ_C hc hc0') (invψ_X hc hc0')
    ((toInv hc0').symm.trans ((semData hτ hσ hc).e.trans (toInv (τ_ne_zero τ hc0'))))
    (fun φ ↦ by
      change toInv (τ_ne_zero τ hc0') ((semData hτ hσ hc).e (algebraMap (RatFunc C) (Aff a c hc F)
          (GaussTube.inv hc0' φ))) =
        toInv (τ_ne_zero τ hc0') (algebraMap (RatFunc C) (Aff (τ a) (τ c) (τ_ne_zero τ hc) F)
          (GaussTube.inv (τ_ne_zero τ hc0') ((GaussTube.inv (τ_ne_zero τ hc0')).symm
            (affψ (τ := τ) (a := a) hc (GaussTube.inv hc0' φ)))))
      rw [(semData hτ hσ hc).he, AlgEquiv.apply_symm_apply]
      rfl)

include hτ hσ in
/-- **Exhausting discs are transported by semilinear automorphisms.** -/
theorem isExhausting_semilinear {a c c' : C} (hc : c ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0)
    (h : IsExhausting a hc hc' hc0' F) :
    IsExhausting (τ a) (τ_ne_zero τ hc) (c' := τ c') (by rw [hτ]; exact hc')
      (τ_ne_zero τ hc0') F := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0ˣ, s ∈ segment c' := by
    have hlt : (‖c'‖₊ : ℝ) < 1 := by simpa using hc'
    refine ⟨Units.mk0 ((‖c'‖₊ + 1) / 2) (by positivity), ?_, ?_⟩ <;> simp only [Units.val_mk0] <;>
      rw [← NNReal.coe_lt_coe] <;> push_cast <;> linarith
  have hs' : s ∈ segment (τ c') := by
    have : ‖τ c'‖₊ = ‖c'‖₊ := NNReal.eq (by simpa using hτ c')
    exact ⟨this ▸ hs.1, hs.2⟩
  exact (semData hτ hσ hc).exhausting_transport hc' (by rw [hτ]; exact hc')
    (mem_nodeRing_iff_of_X hτ (affψ_C (τ := τ) (a := a) hc) (affψ_X (τ := τ) (a := a) hc) c')
    (semDataInv hτ hσ hc hc0')
    (mem_nodeRing_iff_of_X hτ (invψ_C hc hc0') (invψ_X hc hc0') c') (fun _ ↦ rfl) rfl hs hs'
    (gaussRat_zero_comp hτ (affψ_C (τ := τ) (a := a) hc) (affψ_X (τ := τ) (a := a) hc) s) h

lemma isExhausting_congr' {a₁ a₂ c₁ c₂ c₁' c₂' : C} (h0 : a₁ = a₂) (h1 : c₁ = c₂) (h2 : c₁' = c₂')
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₁' : ‖c₁'‖ < 1) (hc₂' : ‖c₂'‖ < 1) (hc₁0' : c₁' ≠ 0)
    (hc₂0' : c₂' ≠ 0) :
    IsExhausting a₁ hc₁ hc₁' hc₁0' F ↔ IsExhausting a₂ hc₂ hc₂' hc₂0' F := by
  subst h0 h1 h2
  rfl

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  [IsUltrametricDist C] [IsAlgClosed C] in
include hσ in
lemma isSemilinear_symm : IsSemilinear C F τ.symm σ.symm := fun φ ↦ by
  rw [RingEquiv.symm_apply_eq, hσ, ratFuncMap_comp_apply]
  congr 1
  convert (ratFuncMap_id φ).symm
  ext; simp

include hτ hσ in
lemma ballGood_image {B : Set C} (hB : BallGood F B) : BallGood F (τ '' B) := by
  intro a' c' hc' hB'
  have hτ' := norm_symm hτ
  have hBe : B = ball (τ.symm a') ‖c'‖ := by
    have := congrArg (img τ.symm) hB'
    rwa [img_ball hτ', show img τ.symm (τ '' B) = B from img_symm_img τ B] at this
  have h1 := discGood_semilinear hτ hσ hc' (hB _ _ hc' hBe)
  refine (discGood_iff_of_ball_eq (τ_ne_zero τ hc') hc' ?_).1 h1
  rw [RingEquiv.apply_symm_apply, hτ]

include hτ hσ in
lemma edgeGood_image {E G : Set C} (hEG : EdgeGood F E G) : EdgeGood F (τ '' E) (τ '' G) := by
  intro a c c' hc hc' hc0' hE hG
  have hτ' := norm_symm hτ
  have hsym : ∀ (D : Set C) (b r : C), τ '' D = closedBall b ‖r‖ →
      D = closedBall (τ.symm b) ‖τ.symm r‖ := fun D b r h ↦ by
    have := congrArg (img τ.symm) h
    rwa [img_closedBall hτ', show img τ.symm (τ '' D) = D from img_symm_img τ D, ← hτ' r]
      at this
  have h1 := hEG (τ.symm a) (τ.symm c) (τ.symm c') (τ_ne_zero τ.symm hc)
    (by rw [hτ']; exact hc') (τ_ne_zero τ.symm hc0') (by rw [hsym E a _ hE, map_mul])
    (hsym G a c hG)
  have h2 := isExhausting_semilinear hτ hσ _ _ _ h1
  exact (isExhausting_congr' (τ.apply_symm_apply a) (τ.apply_symm_apply c)
    (τ.apply_symm_apply c') _ _ _ _ _ _).1 h2

/-- **O6.5: `TransportFor`.** -/
theorem transportFor : TransportFor C F := by
  intro τ hτ σ hσ
  have hτ' := norm_symm hτ
  have hσ' := isSemilinear_symm hσ
  refine ⟨fun B ↦ ⟨fun h ↦ ?_, ballGood_image hτ hσ⟩, fun E G ↦ ⟨fun h ↦ ?_, edgeGood_image hτ hσ⟩⟩
  · have := ballGood_image hτ' hσ' h
    rwa [show τ.symm '' (τ '' B) = B from img_symm_img τ B] at this
  · have := edgeGood_image hτ' hσ' h
    rwa [show τ.symm '' (τ '' E) = E from img_symm_img τ E,
      show τ.symm '' (τ '' G) = G from img_symm_img τ G] at this

end Semilinear

end Transport

end S8A

end SemistableReduction
