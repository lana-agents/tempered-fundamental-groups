/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Transport

/-!
# Ordinary double points are invariant under the inversion `x ↦ c/x`

Blueprint §9.12 O6.1g. The inversion `x ↦ c/x` (`Inv c`) preserves the node chart
`O_C[x, c/x]` and exchanges the outer and the inner vertex. The inner branches of a point `P'` of
`Rint c G` are by definition the outer branches of the corresponding point of
`Rint c (Inv c G)`. Conversely, the inner branches of the latter are the outer branches of
`Inv c (Inv c G)`, which are transported to outer branches of `G` along the identity
(`S8A.Transport.Data` with `ψ = id`, `invInvData`).

* `NodeGood c G`: every point of `Rint c G` over the node is an ordinary double point;
  `AffineTwist.IsExhausting a c c' F` is `NodeGood c' (Aff a c F)`;
* **`isNodeODP_of_inv`**, **`nodeGood_of_inv`**: `NodeGood c (Inv c G) → NodeGood c G`.
-/

open IsLocalRing

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm S8A.Transport

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)

variable (c G) in
/-- Every point of `Rint c G` over the node is an ordinary double point. -/
def NodeGood (hc : ‖c‖ < 1) (hc0 : c ≠ 0) : Prop :=
  ∀ P' : Ideal (Rint c G), P'.IsMaximal →
    P'.comap (algebraMap (nodeRing c) (Rint c G)) = tubeIdeal c → IsNodeODP hc hc0 P'

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G]
  [FiniteDimensional (RatFunc C) G] in
lemma algebraMap_invInv (φ : RatFunc C) :
    (RingEquiv.refl G) (algebraMap (RatFunc C) (Inv c hc0 (Inv c hc0 G)) φ) =
      algebraMap (RatFunc C) G ((RingEquiv.refl (RatFunc C)) φ) := by
  change algebraMap (RatFunc C) G (inv hc0 (inv hc0 φ)) = _
  rw [inv_inv_apply]
  rfl

variable (G) in
/-- The identity `Inv c (Inv c G) → G` as transport data (`ψ = id`, `τ = id`). -/
noncomputable def invInvData : Data C G (Inv c hc0 (Inv c hc0 G)) where
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
  e := RingEquiv.refl G
  he := algebraMap_invInv hc0

omit [IsAlgClosed C] in
lemma τbar_refl (k : 𝓀) : τbar (RingEquiv.refl C) (fun _ ↦ rfl) k = k := by
  obtain ⟨o, rfl⟩ := residue_surjective k
  rw [τbar_residue]
  rfl

omit [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G]
  [FiniteDimensional (RatFunc C) G] in
lemma nodeRing_iff (φ : RatFunc C) :
    φ ∈ nodeRing c ↔ (invInvData G hc0).ψ φ ∈ nodeRing c := Iff.rfl

/-- Place ideals of node charts are transported (for the identity `Inv c (Inv c G) → G`). -/
lemma mem_placeIdeal_invInv {v : Ext C (Inv c hc0 (Inv c hc0 G))}
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Inv c hc0 (Inv c hc0 G))) v)) (y : Rint c G) :
    y ∈ placeIdeal hc ((invInvData G hc0).extMap v) ((invInvData G hc0).mem_zeros_map hQ) ↔
      (invInvData G hc0).symm.icMap ((invInvData G hc0).symm_hA (nodeRing_iff hc0)) y ∈
        placeIdeal hc v hQ := by
  rw [mem_placeIdeal_iff, mem_placeIdeal_iff]
  conv_lhs => rw [← (invInvData G hc0).icMap_icMap_symm (nodeRing_iff hc0) y,
    (invInvData G hc0).coe_icMap, (invInvData G hc0).red_map]
  exact (invInvData G hc0).res_map_eq_zero_iff (red_mem_V hc v _ hQ)

/-- Residues are transported (for the identity `Inv c (Inv c G) → G`). -/
lemma res_placeMap_invInv {v : Ext C (Inv c hc0 (Inv c hc0 G))}
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    {z : ResidueField v.1.valuationSubring} (hz : z ∈ Q.V) :
    ((invInvData G hc0).placeMap v Q).res ((invInvData G hc0).κmap v z) = Q.res z := by
  set d := invInvData G hc0
  refine CurvePlace.res_eq_of_valuation_sub_lt_one _ ?_
  have h := Q.valuation_sub_res_lt_one hz
  rw [CurvePlace.valuation_lt_one_iff, Data.valuation_lt_one_iff'] at h ⊢
  have hk : d.κmap v (algebraMap 𝓀 _ (Q.res z)) = algebraMap 𝓀 _ (Q.res z) := by
    rw [d.κmap_algebraMap]
    exact congrArg _ (τbar_refl (Q.res z))
  rw [← hk, ← _root_.map_sub, ← map_inv₀, d.mem_placeMap, d.mem_placeMap, Ne,
    (d.κmap v).map_eq_zero_iff]
  exact h

include hc in
/-- **Ordinary double points from the inversion**: if the point of `Rint c (Inv c G)`
corresponding to `P'` is an ordinary double point, so is `P'`. -/
theorem isNodeODP_of_inv {P' : Ideal (Rint c G)}
    (h : IsNodeODP hc hc0 (P'.comap (rintEquiv hc0).symm.toRingHom)) : IsNodeODP hc hc0 P' := by
  set d := invInvData G hc0
  have hN := nodeRing_iff (G := G) hc0
  obtain ⟨b₁', ⟨w, Q, hQ⟩, h₁, h₂, hfp⟩ := h
  -- membership in the comap of `P'` to `Rint c (Inv c (Inv c G))`
  have hmemP : ∀ y : Rint c (Inv c hc0 (Inv c hc0 G)),
      y ∈ (P'.comap (rintEquiv (F' := G) hc0).symm.toRingHom).comap
        (rintEquiv (F' := Inv c hc0 G) hc0).symm.toRingHom ↔
      d.icMap hN y ∈ P' := fun _ ↦ Iff.rfl
  -- placeIdeals correspond
  have hpl : ∀ (v : Ext C (Inv c hc0 (Inv c hc0 G)))
      {R : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
      (hR : R ∈ zeros 𝓀 (red C (xF C (Inv c hc0 (Inv c hc0 G))) v)),
      (placeIdeal hc (d.extMap v) (d.mem_zeros_map hR) = P' ↔
        placeIdeal hc v hR = (P'.comap (rintEquiv (F' := G) hc0).symm.toRingHom).comap
          (rintEquiv (F' := Inv c hc0 G) hc0).symm.toRingHom) := by
    intro v R hR
    constructor
    · intro hP
      ext y
      rw [hmemP, ← hP, mem_placeIdeal_invInv hc hc0 hR, d.icMap_symm_icMap]
    · intro hP
      ext y
      rw [mem_placeIdeal_invInv hc hc0 hR, hP, hmemP, d.icMap_icMap_symm]
  refine ⟨d.brMap ⟨w, Q, hQ⟩, b₁', ?_, h₁, ?_⟩
  · ext b
    rw [Set.mem_singleton_iff]
    constructor
    · intro hb
      have hb' : d.symm.brMap b ∈ innerBranches hc hc0
          (P'.comap (rintEquiv hc0).symm.toRingHom) := by
        obtain ⟨v, R, hR⟩ := b
        change placeIdeal hc (d.symm.extMap v) (d.symm.mem_zeros_map hR) = _
        rw [← hpl]
        have h3 : d.brMap (d.symm.brMap ⟨v, R, hR⟩) = ⟨v, R, hR⟩ := d.brMap_brMap_symm _
        have h4 : placeIdeal hc (d.brMap (d.symm.brMap ⟨v, R, hR⟩)).1
            (d.brMap (d.symm.brMap ⟨v, R, hR⟩)).2.2 = P' := by
          rw [h3]; exact hb
        exact h4
      rw [h₂, Set.mem_singleton_iff] at hb'
      rw [← d.brMap_brMap_symm b, hb']
    · rintro rfl
      have hb : (⟨w, Q, hQ⟩ : OuterBranch C (Inv c hc0 (Inv c hc0 G))) ∈
          innerBranches hc hc0 (P'.comap (rintEquiv hc0).symm.toRingHom) := by
        rw [h₂]; rfl
      change placeIdeal hc (d.extMap w) (d.mem_zeros_map hQ) = P'
      exact (hpl w hQ).2 hb
  · change ∀ a ∈ (d.placeMap w Q).V, ∀ b ∈ b₁'.2.1.V, (d.placeMap w Q).res a = b₁'.2.1.res b →
      ∃ y s : Rint c G, s ∉ P' ∧ redHom hc (d.extMap w) y = a * redHom hc (d.extMap w) s ∧
        redHomInv hc hc0 b₁'.1 y = b * redHomInv hc hc0 b₁'.1 s
    intro a ha b hb hab
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, a₀ = (d.κmap w).symm a := ⟨_, rfl⟩
    have haa : a = d.κmap w a₀ := by rw [ha₀, RingEquiv.apply_symm_apply]
    have ha' : a₀ ∈ Q.V := by
      rw [← d.mem_placeMap (Q := Q), ← haa]
      exact ha
    have hres : Q.res a₀ = b₁'.2.1.res b := by
      rw [← hab, haa, res_placeMap_invInv hc0 ha']
    obtain ⟨y, s, hs, hy₁, hy₂⟩ := hfp b hb a₀ ha' hres.symm
    refine ⟨(rintEquiv hc0).symm y, (rintEquiv hc0).symm s, hs, ?_, ?_⟩
    · have hr : ∀ z : Rint c (Inv c hc0 G),
          redHom hc (d.extMap w) ((rintEquiv hc0).symm z) =
            d.κmap w (redHomInv hc hc0 w z) := fun z ↦
        d.red_map w (toInv hc0 ((z : Rint c (Inv c hc0 G)) : Inv c hc0 G))
      rw [hr, hr, hy₂, map_mul, ← haa]
    · change redHom hc b₁'.1 (rintEquiv hc0 ((rintEquiv hc0).symm y)) =
        b * redHom hc b₁'.1 (rintEquiv hc0 ((rintEquiv hc0).symm s))
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact hy₁

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G]
  [FiniteDimensional (RatFunc C) G] in
lemma invRad_invRad (s : NNRealˣ) : invRad hc0 (invRad hc0 s) = s := by
  have hc' : (‖c‖₊ : NNReal) ≠ 0 := by simpa using hc0
  ext
  simp only [coe_invRad]
  rw [div_div_cancel₀ hc']

omit [Algebra C G] [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G] in
/-- The inversion preserves the node ideal. -/
lemma invNode_mem_tubeIdeal_iff (a : nodeRing c) :
    invNode hc0 a ∈ tubeIdeal c ↔ a ∈ tubeIdeal c := by
  constructor
  · intro h s hs
    have h' := h (invRad hc0 s) (invRad_mem_segment hc0 hs)
    rwa [coe_invNode, gaussRat_inv, invRad_invRad] at h'
  · intro h s hs
    rw [coe_invNode, gaussRat_inv]
    exact h _ (invRad_mem_segment hc0 hs)

include hc in
/-- `NodeGood c (Inv c G) → NodeGood c G`. -/
theorem nodeGood_of_inv (h : NodeGood (Inv c hc0 G) c hc hc0) : NodeGood G c hc hc0 := by
  intro P' hP' hcen
  haveI : (P'.comap (rintEquiv hc0).symm.toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (rintEquiv hc0).symm.surjective
  refine isNodeODP_of_inv hc hc0 (h _ inferInstance ?_)
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have he : (rintEquiv hc0).symm.toRingHom (algebraMap (nodeRing c) (Rint c (Inv c hc0 G)) a) =
      algebraMap (nodeRing c) (Rint c G) (invNode hc0 a) := rfl
  rw [he, ← Ideal.mem_comap, hcen, invNode_mem_tubeIdeal_iff]

end GaussTube

end SemistableReduction
