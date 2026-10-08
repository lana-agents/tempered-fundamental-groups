/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentNodeData
import TemperedFundamentalGroups.SemistableReduction.VertexDescent
import TemperedFundamentalGroups.SemistableReduction.ResidueDescent

/-!
# Choosing the discretely valued subfield (O1, step (G))

Blueprint §9.12, O1. For `F' / C(x)` defined over a complete discretely valued subfield
(`DefinedOverDVR`) and an ordinary double point `P'` of the normalized node chart over `C`
(`GaussTube.IsNodeODP`), we choose a large enough complete discretely valued `E ⊆ C` and verify
the hypotheses of `DVRDescent.nonempty_nodeData`, which gives the exact node data at `P'`
(**`exists_nodeData`**).
-/

open NNReal Polynomial IsLocalRing Valuation

namespace SemistableReduction

namespace DVRDescent

open GaussTube FundamentalInequality GaussStability GaussFibre ZariskiModel

universe u

section Vertices

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

local notation "𝓀" => ResidueField (HenselComplete.integers C)

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) F'] in
/-- The residue algebra of a vertex is the one of its extension structure. -/
lemma residueAlgebra_eq (W : Ext C F')
    (h : W.1.valuationSubring.comap (algebraMap C F') =
      (NormedField.valuation (K := C)).valuationSubring) :
    residueAlgebra h = (inferInstance : Algebra 𝓀 (ResidueField W.1.valuationSubring)) := by
  refine Algebra.algebra_ext _ _ fun r ↦ ?_
  obtain ⟨o, rfl⟩ := residue_surjective r
  rw [Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap]
  rfl

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) F'] in
lemma comap_algebraMap_C (W : Ext C F') :
    W.1.valuationSubring.comap (algebraMap C F') =
      (NormedField.valuation (K := C)).valuationSubring := by
  ext a
  simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
  rw [IsScalarTower.algebraMap_apply C (RatFunc C) F', valuation_algebraMap, gauss1_algebraMap_C,
    NormedField.valuation_apply]

omit [CharZero C] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- Vertices are determined by their valuation rings. -/
lemma ext_eq_of_valuationSubring_eq {W W' : Ext C F'}
    (h : W.1.valuationSubring = W'.1.valuationSubring) : W = W' := by
  refine eq_of_le (ramificationIdx_eq_one W) fun a ha ↦ ?_
  have : a ∈ W'.1.valuationSubring := h ▸ ((Valuation.mem_valuationSubring_iff _ _).mpr ha)
  exact (Valuation.mem_valuationSubring_iff _ _).mp this

include hp hp1 in
/-- **D3c + D3d for the outer vertices**: for a monotone directed family of subfields covering
`F'`, from some index on, restriction is injective on the vertices and the residue fields of the
vertices are generated over `𝓀` by residues of the subfield. -/
theorem exists_injOn_adjoin {J : Type*} [Nonempty J] [Preorder J] [IsDirectedOrder J]
    (Lf : J → Subfield F') (hmono : Monotone Lf) (hcov : ∀ y, ∃ j, y ∈ Lf j) :
    ∃ j, ∀ M : Subfield F', Lf j ≤ M →
      (∀ W W' : Ext C F', W.1.valuationSubring.comap M.subtype =
        W'.1.valuationSubring.comap M.subtype → W = W') ∧
      (∀ W : Ext C F', IntermediateField.adjoin 𝓀
        {z | ∃ y ∈ M, ∃ _ : W.1 y ≤ 1, red C y W = z} = ⊤) := by
  classical
  haveI := finite_ext (F := F') hp hp1
  set S : Set (ValuationSubring F') := Set.range fun W : Ext C F' ↦ W.1.valuationSubring
  have hS : S.Finite := Set.finite_range _
  obtain ⟨j₁, hj₁⟩ := exists_injOn_comap Lf hmono.directed_le hcov hS
  obtain ⟨j₂, hj₂⟩ := exists_adjoin_residue_eq_top (Ω := C) (L := F')
    (v := NormedField.valuation (K := C)) (ι := Unit) (a := fun _ ↦ 0) (c := fun _ ↦ 1)
    (r := fun _ ↦ 1) (fun _ ↦ by simp) hmono.directed_le hcov hS (by
      rintro _ ⟨W, rfl⟩
      refine ⟨(), ?_⟩
      ext a
      simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
      rw [valuation_algebraMap])
  obtain ⟨j, h₁, h₂⟩ := directed_of (· ≤ ·) j₁ j₂
  refine ⟨j, fun M hM ↦ ⟨fun W W' hWW' ↦ ?_, fun W ↦ ?_⟩⟩
  · apply ext_eq_of_valuationSubring_eq
    refine hj₁ ⟨W, rfl⟩ ⟨W', rfl⟩ ?_
    ext ⟨y, hy⟩
    have hyM : y ∈ M := hM (hmono h₁ hy)
    have := congrArg (fun V : ValuationSubring M ↦ (⟨y, hyM⟩ : M) ∈ V) hWW'
    exact Iff.of_eq this
  · have hgen := hj₂ _ ⟨W, rfl⟩ (comap_algebraMap_C W)
    rw [residueAlgebra_eq W (comap_algebraMap_C W)] at hgen
    rw [eq_top_iff, ← hgen]
    refine IntermediateField.adjoin.mono _ _ _ ?_
    rintro _ ⟨⟨y, hyW⟩, hy, rfl⟩
    exact ⟨y, hM (hmono h₂ hy), hyW, red_of_le hyW⟩

end Vertices

/-! ### Lifting the minimal polynomial of `θ` -/

lemma ratFuncMap_comp {K L M : Type*} [Field K] [Field L] [Field M] (φ : K →+* L)
    (ψ : L →+* M) : ratFuncMap (ψ.comp φ) = (ratFuncMap ψ).comp (ratFuncMap φ) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors K[X]) (RingHom.ext fun p ↦ ?_)
  simp only [RingHom.comp_apply, ratFuncMap_algebraMap, Polynomial.map_map]

/-- The minimal polynomial of `θ`, with coefficients in `K(x)`, lifts to a monic polynomial over
`E(x)` for `K ⊆ E`. -/
lemma exists_lift_minpoly {C : Type*} [Field C] {F' : Type*} [Field F'] [Algebra (RatFunc C) F']
    [FiniteDimensional (RatFunc C) F'] {K E : Subfield C} (hKE : K ≤ E) (θ : F')
    (hq : ∀ i, (minpoly (RatFunc C) θ).coeff i ∈ (ratFuncMap K.subtype).range) :
    ∃ qE : (RatFunc E)[X], qE.Monic ∧ qE.map (ratFuncMap E.subtype) = minpoly (RatFunc C) θ := by
  have hlift : minpoly (RatFunc C) θ ∈ Polynomial.lifts (ratFuncMap E.subtype) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    obtain ⟨g, hg⟩ := hq i
    refine ⟨ratFuncMap (Subfield.inclusion hKE) g, ?_⟩
    rw [← hg, ← RingHom.comp_apply, ← ratFuncMap_comp]
    rfl
  obtain ⟨qE, hqE, -, hm⟩ := lifts_and_natDegree_eq_and_monic hlift
    (minpoly.monic (Algebra.IsIntegral.isIntegral θ))
  exact ⟨qE, hm, hqE⟩

/-! ### The field `F₀ = E(x)(θ)` -/

section AdjoinRoot

variable {C : Type u} [NontriviallyNormedField C] {E : Type*} [NontriviallyNormedField E]
  (φ : E →+* C) {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  (θ : F') (qE : (RatFunc E)[X]) (hqm : qE.Monic)
  (hq : qE.map (ratFuncMap φ) = minpoly (RatFunc C) θ)

include hqm hq in
lemma irreducible_qE : Irreducible qE :=
  hqm.irreducible_of_irreducible_map (ratFuncMap φ) qE
    (hq ▸ minpoly.irreducible (Algebra.IsIntegral.isIntegral θ))

omit [FiniteDimensional (RatFunc C) F'] in
include hq in
lemma eval₂_qE : eval₂ ((algebraMap (RatFunc C) F').comp (ratFuncMap φ)) θ qE = 0 := by
  rw [← eval₂_map, hq, ← aeval_def, minpoly.aeval]

variable [Fact (Irreducible qE)]

/-- `χ : E(x)[T]/(q) → F'`, `T ↦ θ`. -/
noncomputable def χq : AdjoinRoot qE →+* F' :=
  AdjoinRoot.lift ((algebraMap (RatFunc C) F').comp (ratFuncMap φ)) θ (eval₂_qE φ θ qE hq)

omit [FiniteDimensional (RatFunc C) F'] in
lemma isCompat_χq : IsCompat φ (χq φ θ qE hq) := by
  intro f
  rw [AdjoinRoot.algebraMap_eq, χq, AdjoinRoot.lift_of]
  rfl

omit [FiniteDimensional (RatFunc C) F'] in
lemma χq_root : χq φ θ qE hq (AdjoinRoot.root qE) = θ := by
  rw [χq, AdjoinRoot.lift_root]

include hqm in
lemma finiteDimensional_qE : FiniteDimensional (RatFunc E) (AdjoinRoot qE) :=
  (AdjoinRoot.powerBasis hqm.ne_zero).finite

include hqm hq in
lemma finrank_qE (hθ : Algebra.adjoin (RatFunc C) {θ} = ⊤) :
    Module.finrank (RatFunc E) (AdjoinRoot qE) = Module.finrank (RatFunc C) F' := by
  rw [(AdjoinRoot.powerBasis hqm.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    ← natDegree_map_eq_of_injective (ratFuncMap φ).injective, hq]
  have hint : IsIntegral (RatFunc C) θ := Algebra.IsIntegral.isIntegral θ
  rw [← IntermediateField.adjoin.finrank hint]
  have htop : IntermediateField.adjoin (RatFunc C) {θ} = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ,
      IntermediateField.top_toSubalgebra]
  rw [htop, IntermediateField.finrank_top']

end AdjoinRoot

/-! ### The inversion over `E` -/

section Inversion

variable {C : Type u} [NontriviallyNormedField C] {E : Type*} [NontriviallyNormedField E]
  {φ : E →+* C} {c₀ : E} (hc₀ : c₀ ≠ 0) (hc : φ c₀ ≠ 0)

include hc₀ in
lemma ratFuncMap_inv (f : RatFunc E) :
    ratFuncMap φ (inv hc₀ f) = inv hc (ratFuncMap φ f) := by
  have h : (ratFuncMap φ).comp (inv hc₀).toRingEquiv.toRingHom =
      (inv hc).toRingEquiv.toRingHom.comp (ratFuncMap φ) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors E[X]) ?_
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · change ratFuncMap φ (inv hc₀ (algebraMap E[X] (RatFunc E) (Polynomial.C a))) =
        inv hc (ratFuncMap φ (algebraMap E[X] (RatFunc E) (Polynomial.C a)))
      rw [show algebraMap E[X] (RatFunc E) (Polynomial.C a) = algebraMap E (RatFunc E) a by
        rw [IsScalarTower.algebraMap_apply E E[X] (RatFunc E), Polynomial.algebraMap_eq],
        AlgEquiv.commutes, ratFuncMap_algebraMap_C, AlgEquiv.commutes]
    · change ratFuncMap φ (inv hc₀ (algebraMap E[X] (RatFunc E) Polynomial.X)) =
        inv hc (ratFuncMap φ (algebraMap E[X] (RatFunc E) Polynomial.X))
      rw [RatFunc.algebraMap_X, inv_apply, invHom_X, ratFuncMap_X, inv_apply, invHom_X, map_div₀,
        ratFuncMap_algebraMap_C, ratFuncMap_X]
  exact congrArg (fun g : RatFunc E →+* RatFunc C ↦ g f) h

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* F'}

/-- `χ` between the inverted fields. -/
noncomputable def χI (χ : F₀ →+* F') : Inv c₀ hc₀ F₀ →+* Inv (φ c₀) hc F' := χ

include hc₀ in
lemma isCompat_χI (hχ : IsCompat φ χ) : IsCompat φ (χI hc₀ hc χ) := by
  intro f
  change χ (algebraMap (RatFunc E) F₀ (inv hc₀ f)) =
    algebraMap (RatFunc C) F' (inv hc (ratFuncMap φ f))
  rw [hχ, ratFuncMap_inv hc₀ hc]

end Inversion

/-! ### The C-level data at an ordinary double point -/

section CData

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)

omit [IsAlgClosed C] [CharZero C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma xR_mem {P' : Ideal (Rint c F')}
    (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c) : xR c ∈ P' := by
  have : (⟨RatFunc.X, X_mem_nodeRing c⟩ : nodeRing c) ∈ tubeIdeal c := by
    intro s hs
    change gaussRat _ 0 s RatFunc.X < 1
    rw [AnnulusUnit.gaussRat_X]
    exact hs.2
  rw [← hP'] at this
  exact this

omit [IsAlgClosed C] [CharZero C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma yR_mem {P' : Ideal (Rint c F')}
    (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c) : yR c ∈ P' := by
  have : (⟨_, div_X_mem_nodeRing c⟩ : nodeRing c) ∈ tubeIdeal c := by
    intro s hs
    change gaussRat _ 0 s (algebraMap C (RatFunc C) c / RatFunc.X) < 1
    rw [map_div₀, gaussRat_C, AnnulusUnit.gaussRat_X, div_lt_one (Units.zero_lt s)]
    exact hs.1
  rw [← hP'] at this
  exact this

include hc0 in
omit [IsAlgClosed C] [CharZero C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma rintEquiv_symm_xR :
    (rintEquiv hc0).symm (xR c : Rint c (Inv c hc0 F')) = (yR c : Rint c F') := by
  rw [RingEquiv.symm_apply_eq, rintEquiv_yR]

omit [CharZero C] in
/-- The C-level data: the inner branch, its fibre-product clause and the points of the
branches. -/
theorem exists_cData {P' : Ideal (Rint c F')} [P'.IsMaximal]
    (hODP : IsNodeODP hc hc0 P') {b₁ : OuterBranch C F'} (hb₁ : outerBranches hc P' = {b₁}) :
    ∃ b₂ : OuterBranch C (Inv c hc0 F'), innerBranches hc hc0 P' = {b₂} ∧
      (∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b →
        ∃ y s : Rint c F', s ∉ P' ∧ redHom hc b₁.1 y = a * redHom hc b₁.1 s ∧
          redHomInv hc hc0 b₂.1 y = b * redHomInv hc hc0 b₂.1 s) ∧
      placeIdeal hc b₁.1 b₁.2.2 = P' ∧
      placeIdeal hc b₂.1 b₂.2.2 = P'.comap (rintEquiv hc0).symm.toRingHom := by
  obtain ⟨b₁', b₂, h₁, h₂, hfp⟩ := hODP
  have hb : b₁' = b₁ := by rw [h₁] at hb₁; exact Set.singleton_eq_singleton_iff.mp hb₁
  subst hb
  refine ⟨b₂, h₂, hfp, ?_, ?_⟩
  · have : b₁' ∈ outerBranches hc P' := by rw [h₁]; rfl
    exact this
  · have : b₂ ∈ innerBranches hc hc0 P' := by rw [h₂]; rfl
    exact this

include hp hp1 in
/-- **A killer of the other vertices**: an element outside `P'` reducing to `0` at every vertex
other than the two branch vertices. -/
theorem exists_killer {P' : Ideal (Rint c F')} [hP'm : P'.IsMaximal]
    (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c)
    {b₁ : OuterBranch C F'} (hb₁ : outerBranches hc P' = {b₁})
    {b₂ : OuterBranch C (Inv c hc0 F')} (hb₂ : innerBranches hc hc0 P' = {b₂}) :
    ∃ t₀ : Rint c F', t₀ ∉ P' ∧ (∀ v : Ext C F', v ≠ b₁.1 → redHom hc v t₀ = 0) ∧
      (∀ w : Ext C (Inv c hc0 F'), w ≠ b₂.1 → redHomInv hc hc0 w t₀ = 0) := by
  classical
  haveI := finite_ext (F := F') hp hp1
  haveI := finite_ext (F := Inv c hc0 F') hp hp1
  letI := Fintype.ofFinite (Ext C F')
  letI := Fintype.ofFinite (Ext C (Inv c hc0 F'))
  have hout : ∀ v : Ext C F', ∃ t : Rint c F', v ≠ b₁.1 → redHom hc v t = 0 ∧ t ∉ P' := by
    intro v
    by_cases hv : v = b₁.1
    · exact ⟨1, fun h ↦ (h hv).elim⟩
    obtain ⟨t, ht⟩ := exists_mem_ker_notMem hc v (xR_mem hP') fun Q hQ hQP ↦ hv (by
      have : (⟨v, Q, hQ⟩ : OuterBranch C F') ∈ outerBranches hc P' := hQP
      rw [hb₁, Set.mem_singleton_iff] at this
      rw [← this])
    exact ⟨t, fun _ ↦ ht⟩
  set P'' : Ideal (Rint c (Inv c hc0 F')) := P'.comap (rintEquiv hc0).symm.toRingHom
  haveI : P''.IsMaximal := Ideal.comap_isMaximal_of_surjective _ (rintEquiv hc0).symm.surjective
  have hxP'' : xR c ∈ P'' := by
    change (rintEquiv hc0).symm (xR c) ∈ P'
    rw [rintEquiv_symm_xR]
    exact yR_mem hP'
  have hin : ∀ w : Ext C (Inv c hc0 F'), ∃ t : Rint c F',
      w ≠ b₂.1 → redHomInv hc hc0 w t = 0 ∧ t ∉ P' := by
    intro w
    by_cases hw : w = b₂.1
    · exact ⟨1, fun h ↦ (h hw).elim⟩
    obtain ⟨t, ht₁, ht₂⟩ := exists_mem_ker_notMem hc w hxP'' fun Q hQ hQP ↦ hw (by
      have : (⟨w, Q, hQ⟩ : OuterBranch C (Inv c hc0 F')) ∈ innerBranches hc hc0 P' := hQP
      rw [hb₂, Set.mem_singleton_iff] at this
      rw [← this])
    refine ⟨(rintEquiv hc0).symm t, fun _ ↦ ⟨?_, ?_⟩⟩
    · change redHom hc w (rintEquiv hc0 ((rintEquiv hc0).symm t)) = 0
      rw [RingEquiv.apply_symm_apply]; exact ht₁
    · exact ht₂
  choose tv htv using hout
  choose tw htw using hin
  refine ⟨(∏ v ∈ Finset.univ.erase b₁.1, tv v) * ∏ w ∈ Finset.univ.erase b₂.1, tw w,
    ?_, fun v hv ↦ ?_, fun w hw ↦ ?_⟩
  · intro hmem
    rcases hP'm.isPrime.mem_or_mem hmem with h | h
    · obtain ⟨v, hv, h⟩ := (Ideal.IsPrime.prod_mem_iff).mp h
      exact (htv v (Finset.ne_of_mem_erase hv)).2 h
    · obtain ⟨w, hw, h⟩ := (Ideal.IsPrime.prod_mem_iff).mp h
      exact (htw w (Finset.ne_of_mem_erase hw)).2 h
  · rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)
      (htv v hv).1, zero_mul]
  · rw [map_mul, map_prod, map_prod, Finset.prod_eq_zero (s := Finset.univ.erase b₂.1)
      (Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩) (htw w hw).1, mul_zero]

set_option maxHeartbeats 800000 in
-- unifying residues of places of the inverted residue curves is elaboration-heavy
omit [CharZero C] in
/-- **Parameters of the two branches**: `y_u` vanishing on the inner branch and of order `1` on
the outer one, and symmetrically `y_v`. -/
theorem exists_params {P' : Ideal (Rint c F')} {b₁ : OuterBranch C F'}
    {b₂ : OuterBranch C (Inv c hc0 F')}
    (hfp : ∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b →
      ∃ y s : Rint c F', s ∉ P' ∧ redHom hc b₁.1 y = a * redHom hc b₁.1 s ∧
        redHomInv hc hc0 b₂.1 y = b * redHomInv hc hc0 b₂.1 s)
    (hP₁ : placeIdeal hc b₁.1 b₁.2.2 = P')
    (hP₂ : placeIdeal hc b₂.1 b₂.2.2 = P'.comap (rintEquiv hc0).symm.toRingHom) :
    (∃ yu : Rint c F', b₁.2.1.valuation (redHom hc b₁.1 yu) = WithZero.exp (-1) ∧
      redHomInv hc hc0 b₂.1 yu = 0) ∧
    (∃ yv : Rint c F', b₂.2.1.valuation (redHomInv hc hc0 b₂.1 yv) = WithZero.exp (-1) ∧
      redHom hc b₁.1 yv = 0) := by
  have hs₂ : ∀ s : Rint c F', s ∉ P' → b₂.2.1.valuation (redHomInv hc hc0 b₂.1 s) = 1 := by
    intro s hs
    refine Qval_one_of_notMem (F' := Inv c hc0 F') hc hP₂ (y := rintEquiv hc0 s) ?_
    change (rintEquiv hc0).symm (rintEquiv hc0 s) ∉ P'
    rwa [RingEquiv.symm_apply_apply]
  constructor
  · obtain ⟨π, hπ⟩ := b₁.2.1.exists_valuation_eq_exp_neg_one
    have hπV : π ∈ b₁.2.1.V := b₁.2.1.valuation_le_one_iff.mp (by
      rw [hπ]; exact (WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)).le)
    have hπr : b₁.2.1.res π = 0 := b₁.2.1.res_eq_zero_of_lt_one (by
      rw [hπ]; exact WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0))
    obtain ⟨y, s, hs, h₁, h₂⟩ := hfp π hπV (0 : ResidueField b₂.1.1.valuationSubring)
      b₂.2.1.V.zero_mem (by rw [hπr, CurvePlace.res_zero])
    refine ⟨y, ?_, by rw [h₂, zero_mul]⟩
    rw [h₁, map_mul, hπ, Qval_one_of_notMem hc hP₁ hs, mul_one]
  · obtain ⟨π, hπ⟩ := b₂.2.1.exists_valuation_eq_exp_neg_one
    have hπV : π ∈ b₂.2.1.V := b₂.2.1.valuation_le_one_iff.mp (by
      rw [hπ]; exact (WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)).le)
    have hπV' : b₂.2.1.V.valuation π < 1 := (CurvePlace.valuation_lt_one_iff _).mp (by
      rw [hπ]; exact WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0))
    obtain ⟨y, s, hs, h₁, h₂⟩ := hfp 0 b₁.2.1.V.zero_mem π hπV (by
      rw [CurvePlace.res_zero]
      exact (b₂.2.1.res_eq_zero_of_lt_one ((CurvePlace.valuation_lt_one_iff _).mpr hπV')).symm)
    refine ⟨y, ?_, by rw [h₁, zero_mul]⟩
    rw [h₂, map_mul, hπ, hs₂ s hs, mul_one]

end CData

/-! ### The family of subfields `E(x)(θ)` -/

section Family

variable {C : Type u} [NontriviallyNormedField C] {F' : Type*} [Field F']
  [Algebra (RatFunc C) F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F']

/-- The subfield of `F'` generated by `E`, `x` and `θ`. -/
noncomputable def famE (θ : F') (E : Subfield C) : Subfield F' :=
  Subfield.closure (algebraMap C F' '' (E : Set C) ∪ {xF C F', θ})

omit [IsScalarTower C (RatFunc C) F'] in
lemma famE_mono (θ : F') {E E' : Subfield C} (h : E ≤ E') : famE θ E ≤ famE θ E' :=
  Subfield.closure_mono (Set.union_subset_union_left _ (Set.image_mono h))

omit [IsScalarTower C (RatFunc C) F'] in
lemma xF_mem_famE (θ : F') (E : Subfield C) : xF C F' ∈ famE θ E :=
  Subfield.subset_closure (Set.mem_union_right _ (Set.mem_insert _ _))

omit [IsScalarTower C (RatFunc C) F'] in
lemma θ_mem_famE (θ : F') (E : Subfield C) : θ ∈ famE θ E :=
  Subfield.subset_closure (Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl))

omit [IsScalarTower C (RatFunc C) F'] in
lemma algebraMap_mem_famE (θ : F') {E : Subfield C} {e : C} (he : e ∈ E) :
    algebraMap C F' e ∈ famE θ E :=
  Subfield.subset_closure (Set.mem_union_left _ ⟨e, he, rfl⟩)

/-- Polynomials in `x` with coefficients in `S`. -/
lemma algebraMap_poly_mem (S : Subfield F') (P : C[X])
    (hP : ∀ i, algebraMap C F' (P.coeff i) ∈ S) (hx : xF C F' ∈ S) :
    algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) P) ∈ S := by
  rw [← aeval_xF, aeval_eq_sum_range]
  refine S.sum_mem fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact S.mul_mem (hP i) (S.pow_mem hx _)

/-- Rational functions with coefficients in `S`. -/
lemma algebraMap_ratFunc_mem (S : Subfield F') (f : RatFunc C)
    (hf : ∀ i, algebraMap C F' (f.num.coeff i) ∈ S ∧ algebraMap C F' (f.denom.coeff i) ∈ S)
    (hx : xF C F' ∈ S) : algebraMap (RatFunc C) F' f ∈ S := by
  rw [← RatFunc.num_div_denom f, map_div₀]
  exact S.div_mem (algebraMap_poly_mem S _ (fun i ↦ (hf i).1) hx)
    (algebraMap_poly_mem S _ (fun i ↦ (hf i).2) hx)

/-- **The family covers `F'`**: every element of `F' = C(x)(θ)` lies in `E(x)(θ)` for `E`
containing finitely many coefficients. -/
lemma exists_finset_mem_famE {θ : F'} (hθ : Algebra.adjoin (RatFunc C) {θ} = ⊤) (y : F') :
    ∃ T : Finset C, ∀ E : Subfield C, (T : Set C) ⊆ E → y ∈ famE θ E := by
  classical
  have hy : y ∈ Algebra.adjoin (RatFunc C) {θ} := by rw [hθ]; exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨P, rfl⟩ := hy
  refine ⟨(Finset.range (P.natDegree + 1)).biUnion fun i ↦
    (P.coeff i).num.coeffs ∪ (P.coeff i).denom.coeffs ∪ {0}, fun E hTE ↦ ?_⟩
  change aeval θ P ∈ _
  rw [aeval_eq_sum_range]
  refine Subfield.sum_mem _ fun i hi ↦ ?_
  rw [Algebra.smul_def]
  refine Subfield.mul_mem _ (algebraMap_ratFunc_mem _ _ (fun j ↦ ?_) (xF_mem_famE θ E))
    (Subfield.pow_mem _ (θ_mem_famE θ E) _)
  have hmem : ∀ q : C[X], q.coeffs ⊆ (P.coeff i).num.coeffs ∪ (P.coeff i).denom.coeffs ∪ {0} →
      algebraMap C F' (q.coeff j) ∈ famE θ E := by
    intro q hq
    refine algebraMap_mem_famE θ (hTE ?_)
    simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Set.mem_Iio,
      Finset.mem_coe]
    refine ⟨i, Finset.mem_range.mp hi, ?_⟩
    by_cases h0 : q.coeff j = 0
    · rw [h0]; simp
    · exact hq (Polynomial.coeff_mem_coeffs h0)
  exact ⟨hmem _ (fun z hz ↦ by simp [hz]), hmem _ (fun z hz ↦ by simp [hz])⟩


/-- `famE θ E ⊆ χ(F₀)` if `E` comes from `E'` and `θ ∈ χ(F₀)`. -/
lemma famE_le_fieldRange {E : Subfield C} {E' : Type*} [NontriviallyNormedField E']
    {φ : E' →+* C} (hφE : ∀ e ∈ E, ∃ e', φ e' = e) {F₀ : Type*} [Field F₀]
    [Algebra (RatFunc E') F₀] {χ : F₀ →+* F'} (hχ : IsCompat φ χ) {θ₀ : F₀} {θ : F'}
    (hθ₀ : χ θ₀ = θ) : famE θ E ≤ χ.fieldRange := by
  refine Subfield.closure_le.mpr ?_
  rintro _ (⟨e, he, rfl⟩ | h)
  · obtain ⟨e', rfl⟩ := hφE e he
    refine ⟨algebraMap (RatFunc E') F₀ (algebraMap E' (RatFunc E') e'), ?_⟩
    rw [hχ, ratFuncMap_algebraMap_C, ← IsScalarTower.algebraMap_apply]
  · rcases h with rfl | h
    · refine ⟨algebraMap (RatFunc E') F₀ RatFunc.X, ?_⟩
      rw [hχ, ratFuncMap_X]
    · rw [Set.mem_singleton_iff] at h
      exact ⟨θ₀, h ▸ hθ₀⟩

end Family

section Translate

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] {F₀ : Type*} [Field F₀] (χ : F₀ →+* F')

local notation "𝓀" => ResidueField (HenselComplete.integers C)

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma hinj_of_injOn
    (h : ∀ W W' : Ext C F', W.1.valuationSubring.comap χ.fieldRange.subtype =
      W'.1.valuationSubring.comap χ.fieldRange.subtype → W = W')
    (W W' : Ext C F') (hWW : W.1.comap χ = W'.1.comap χ) : W = W' := by
  refine h W W' ?_
  ext ⟨y, f, rfl⟩
  have := congrArg (fun v : Valuation F₀ ℝ≥0 ↦ v f ≤ 1) hWW
  simp only [Valuation.comap_apply] at this
  change W.1 (χ f) ≤ 1 ↔ W'.1 (χ f) ≤ 1
  rw [this]

lemma hgen_of_adjoin (W : Ext C F')
    (h : IntermediateField.adjoin 𝓀
      {z | ∃ y ∈ χ.fieldRange, ∃ _ : W.1 y ≤ 1, red C y W = z} = ⊤) :
    IntermediateField.adjoin 𝓀 (resE χ W : Set (ResidueField W.1.valuationSubring)) = ⊤ := by
  rw [← h]
  congr 1
  ext z
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨χ f, ⟨f, rfl⟩, hf, rfl⟩
  · rintro ⟨_, ⟨f, rfl⟩, hf, rfl⟩
    exact ⟨f, hf, rfl⟩

end Translate

/-! ### Rational residues -/

section Residues

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-- The residue map of a place, as a ring homomorphism on its valuation ring. -/
noncomputable def resHom {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
    [IsCurveFunctionField k κ] (Q : CurvePlace k κ) : Q.V.toSubring →+* k where
  toFun a := Q.res a
  map_one' := Q.res_one
  map_mul' a b := Q.res_mul a.2 b.2
  map_zero' := Q.res_zero
  map_add' a b := Q.res_add a.2 b.2

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* F'}

set_option maxHeartbeats 8000000 in
-- the residue bookkeeping is elaboration-heavy
/-- **The residues of `B_E` at `P'` lie in `κ_E`** (given rational residues of the spanning
elements). -/
theorem exists_residue_of_span (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ) {c₀ : E}
    (hc : ‖φ c₀‖ < 1) (hc0 : φ c₀ ≠ 0) {P' : Ideal (Rint (φ c₀) F')} {b₁ : OuterBranch C F'}
    {b₂ : OuterBranch C (Inv (φ c₀) hc0 F')} (hP₁ : placeIdeal hc b₁.1 b₁.2.2 = P')
    (hxP : xR (φ c₀) ∈ P') (hyP : yR (φ c₀) ∈ P')
    (ι : BE F₀ c₀ →+* Rint (φ c₀) F') (hι : ∀ b, (ι b : F') = χ b)
    (hLD₁ : letI := kEAlgebra φ; ConstantDescent.LinDisj (kE φ) 𝓀 (resE χ b₁.1))
    {N : ℕ} (r : Fin N → Rint (φ c₀) F')
    (hr : ∀ B : Subring (Rint (φ c₀) F'), (∀ j, r j ∈ B) → xR (φ c₀) ∈ B → yR (φ c₀) ∈ B →
      ∀ y, ConstantDescent.IsSpanned 𝓀 B (redHom hc b₁.1) (redHomInv hc hc0 b₂.1) y)
    (hrι : ∀ j, r j ∈ ι.range) (hxι : xR (φ c₀) ∈ ι.range) (hyι : yR (φ c₀) ∈ ι.range)
    (hκ : ∀ j, ∃ e : E, ∃ he : ‖e‖ ≤ 1, placeHom hc b₁.1 b₁.2.2 (r j) =
      residue _ (⟨φ e, (HenselComplete.mem_integers_iff _).2 (by rw [hφ]; exact he)⟩ :
        HenselComplete.integers C))
    (b : BE F₀ c₀) :
    letI := kEAlgebra φ
    ∃ t : kE φ, placeHom hc b₁.1 b₁.2.2 (ι b) = algebraMap (kE φ) 𝓀 t := by
  classical
  letI := kEAlgebra φ
  have hvE : ∀ e : (vE φ).valuationSubring, ‖(e : E)‖ ≤ 1 := fun e ↦ by
    have h : vE φ (e : E) ≤ 1 := e.2
    simp only [vE, Valuation.comap_apply, NormedField.valuation_apply] at h
    rw [← hφ]
    exact_mod_cast h
  have hres_e : ∀ e : (vE φ).valuationSubring, algebraMap (kE φ) 𝓀 (residue _ e) =
      residue _ (⟨φ e, (HenselComplete.mem_integers_iff _).2 (by rw [hφ]; exact hvE e)⟩ :
        HenselComplete.integers C) := fun e ↦ by
    change ResidueField.map (integersMap φ) (residue _ e) = _
    rw [ResidueField.map_residue]
    rfl
  -- constants
  have hconstR : ∀ e : (vE φ).valuationSubring, ∃ o, ι o = constR (φ c₀)
      (⟨φ e, (HenselComplete.mem_integers_iff _).2 (by rw [hφ]; exact hvE e)⟩ :
        HenselComplete.integers C) := fun e ↦ by
    refine ⟨algebraMap (nodeRing c₀) (BE F₀ c₀)
      ⟨algebraMap E (RatFunc E) e, algebraMap_mem_nodeRing (hvE e)⟩, Subtype.ext ?_⟩
    rw [hι]
    change χ (algebraMap (RatFunc E) F₀ (algebraMap E (RatFunc E) e)) = _
    rw [hχ, ratFuncMap_algebraMap_C]
    rfl
  have hplace_const : ∀ b' : HenselComplete.integers C,
      placeHom hc b₁.1 b₁.2.2 (constR (φ c₀) b') = residue _ b' := fun b' ↦ by
    rw [placeHom_apply, ← redHom_apply hc, redHom_constR, CurvePlace.res_algebraMap]
  obtain ⟨G, hG⟩ : ∃ G : Subring (Rint (φ c₀) F'), G = Subring.closure
      (Set.range r ∪ {xR (φ c₀), yR (φ c₀)} ∪
        Set.range fun e : (vE φ).valuationSubring ↦ constR (φ c₀)
          (⟨φ e, (HenselComplete.mem_integers_iff _).2 (by rw [hφ]; exact hvE e)⟩ :
            HenselComplete.integers C)) := ⟨_, rfl⟩
  have hGB : G ≤ ι.range := by
    rw [hG]
    refine Subring.closure_le.mpr ?_
    rintro _ ((⟨j, rfl⟩ | h) | ⟨e, rfl⟩)
    · exact hrι j
    · rcases h with rfl | h
      · exact hxι
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact hyι
    · obtain ⟨o, ho⟩ := hconstR e
      exact ⟨o, ho⟩
  -- rational residues on `G`
  let Rat : Subring (Rint (φ c₀) F') :=
    { carrier := {g | ∃ c : kE φ, placeHom hc b₁.1 b₁.2.2 g = algebraMap (kE φ) 𝓀 c}
      mul_mem' := by
        rintro _ _ ⟨a, ha⟩ ⟨b, hb⟩; exact ⟨a * b, by rw [map_mul, map_mul, ha, hb]⟩
      one_mem' := ⟨1, by rw [map_one, map_one]⟩
      add_mem' := by
        rintro _ _ ⟨a, ha⟩ ⟨b, hb⟩; exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
      neg_mem' := by rintro _ ⟨a, ha⟩; exact ⟨-a, by rw [_root_.map_neg, _root_.map_neg, ha]⟩ }
  have hzero : ∀ y ∈ P', placeHom hc b₁.1 b₁.2.2 y = algebraMap (kE φ) 𝓀 0 := fun y hy ↦ by
    rw [map_zero]; rw [← hP₁] at hy; exact hy
  have hGRat : G ≤ Rat := by
    rw [hG]
    refine Subring.closure_le.mpr ?_
    rintro _ ((⟨j, rfl⟩ | h) | ⟨e, rfl⟩)
    · obtain ⟨e, he, hej⟩ := hκ j
      refine ⟨residue _ (⟨e, ?_⟩ : (vE φ).valuationSubring), ?_⟩
      · change vE φ e ≤ 1
        rw [vE_eq φ hφ, NormedField.valuation_apply]; exact_mod_cast he
      · rw [hej, hres_e]
    · rcases h with rfl | h
      · exact ⟨0, hzero _ hxP⟩
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact ⟨0, hzero _ hyP⟩
    · exact ⟨residue _ e, by rw [hplace_const, hres_e]⟩
  have hM₁ : ∀ y ∈ ι.range, redHom hc b₁.1 y ∈ resE χ b₁.1 := by
    rintro _ ⟨b', rfl⟩
    refine ⟨b', ?_, ?_⟩
    · rw [← hι]; exact valuation_le_one_R hc b₁.1 _
    · rw [redHom_apply, hι]
  have hconst : ∀ c : kE φ, ∃ o ∈ ι.range, redHom hc b₁.1 o =
      algebraMap 𝓀 _ (algebraMap (kE φ) 𝓀 c) ∧
      redHomInv hc hc0 b₂.1 o = algebraMap 𝓀 _ (algebraMap (kE φ) 𝓀 c) := by
    intro c
    obtain ⟨e, rfl⟩ := residue_surjective c
    obtain ⟨o, ho⟩ := hconstR e
    refine ⟨ι o, ⟨o, rfl⟩, ?_, ?_⟩
    · rw [ho, redHom_constR, hres_e]
    · rw [ho, redHomInv_constR, hres_e]
  obtain ⟨c', hc'⟩ := ConstantDescent.exists_residue_eq_of_span (k₀ := kE φ) (k := 𝓀)
    (ρ₂ := redHomInv hc hc0 b₂.1) hM₁ hLD₁ hconst b₁.2.1.V.toSubring (resHom b₁.2.1)
    (fun y ↦ red_mem_V hc b₁.1 y b₁.2.2) (fun t ↦ b₁.2.1.algebraMap_mem t)
    (fun t ↦ b₁.2.1.res_algebraMap t) hGB (fun g hg ↦ hGRat hg)
    (hr G (fun j ↦ hG ▸ Subring.subset_closure (Or.inl (Or.inl ⟨j, rfl⟩)))
      (hG ▸ Subring.subset_closure (Or.inl (Or.inr (Set.mem_insert _ _))))
      (hG ▸ Subring.subset_closure (Or.inl (Or.inr (Set.mem_insert_of_mem _ rfl)))))
    ⟨b, rfl⟩
  exact ⟨c', hc'⟩

omit [IsAlgClosed C] [IsUltrametricDist E] in
/-- **The residue field of `C` is algebraic over `κ_E`** if `C` is algebraic over `E`. -/
theorem isAlgebraic_kE (φ : E →+* C) (halg : letI := φ.toAlgebra; Algebra.IsAlgebraic E C) :
    letI := kEAlgebra φ
    Algebra.IsAlgebraic (kE φ) 𝓀 := by
  letI := φ.toAlgebra
  have hV : (HenselComplete.integers C).comap (algebraMap E C) =
      (vE φ).valuationSubring := by
    ext e
    simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
    rfl
  have h := isAlgebraic_residueField (K := E) (Ω := C) hV
  have heq : residueAlgebra hV = kEAlgebra φ := by
    refine Algebra.algebra_ext _ _ fun r ↦ ?_
    obtain ⟨o, rfl⟩ := residue_surjective r
    change ResidueField.map (toVal hV) _ = ResidueField.map (integersMap φ) _
    rw [ResidueField.map_residue, ResidueField.map_residue]
    rfl
  rw [heq] at h
  exact h

end Residues

/-! ### The main theorem -/

section Main

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

set_option maxHeartbeats 4000000 in
-- the assembly instantiates the descent over the subfield `E` (many large terms)
include hp hp1 in
/-- **Exact node data at an ordinary double point** (O1): if `F'` is defined over a complete
discretely valued subfield of `C`, every ordinary double point `P'` over the node of the
normalized node chart carries exact node data. -/
theorem exists_nodeData (hdef : DefinedOverDVR C F') {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)
    (P' : Ideal (Rint c F')) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c)
    (hODP : IsNodeODP hc hc0 P') (b₁ : OuterBranch C F') (hb₁ : outerBranches hc P' = {b₁}) :
    Nonempty (NodeData hc P' b₁) := by
  classical
  obtain ⟨K, -, halgK, hfin, θ, hθ, hcoeff⟩ := hdef
  obtain ⟨b₂, hb₂, hfp, hP₁, hP₂⟩ := exists_cData hc hc0 hODP hb₁
  obtain ⟨t₀, ht₀, ht₀o, ht₀i⟩ := exists_killer hp hp1 hc hc0 hP' hb₁ hb₂
  obtain ⟨⟨yu, hyu₁, hyu₂⟩, ⟨yv, hyv₂, hyv₁⟩⟩ := exists_params hc hc0 hfp hP₁ hP₂
  obtain ⟨N, r, hr⟩ := exists_spanning hc hc0 b₁.1 b₂.1
  choose κ hκ using fun j ↦ residue_surjective (placeHom hc b₁.1 b₁.2.2 (r j))
  -- the family of subfields
  have hLmono : Monotone fun T : Finset C ↦ famE θ (Subfield.closure ((K : Set C) ∪ T)) :=
    fun T T' h ↦ famE_mono θ (Subfield.closure_mono
      (Set.union_subset_union_right _ (Finset.coe_subset.mpr h)))
  have hLcov : ∀ y : F', ∃ T : Finset C,
      y ∈ famE θ (Subfield.closure ((K : Set C) ∪ T)) := fun y ↦ by
    obtain ⟨T, hT⟩ := exists_finset_mem_famE hθ y
    exact ⟨T, hT _ (fun t ht ↦ Subfield.subset_closure (Or.inr ht))⟩
  obtain ⟨T₁, hT₁⟩ := exists_injOn_adjoin hp hp1 _ hLmono hLcov
  obtain ⟨T₂, hT₂⟩ := exists_injOn_adjoin (F' := Inv c hc0 F') hp hp1
    (fun T : Finset C ↦ (famE θ (Subfield.closure ((K : Set C) ∪ T)) : Subfield F'))
    hLmono hLcov
  -- the elements to descend
  obtain ⟨ys, hys⟩ : ∃ ys : Finset (Rint c F'),
      ys = {t₀, yu, yv, xR c, yR c} ∪ Finset.univ.image r := ⟨_, rfl⟩
  choose Ty hTy using fun y : Rint c F' ↦ hLcov (y : F')
  obtain ⟨T, hST, hEdvr⟩ := hfin (T₁ ∪ T₂ ∪ ys.biUnion Ty ∪ {c} ∪
    Finset.univ.image fun j ↦ (κ j : C))
  generalize hEdef : Subfield.closure ((K : Set C) ∪ T) = E at hST hEdvr
  have hKE : K ≤ E := fun k hk ↦ by rw [← hEdef]; exact Subfield.subset_closure (Or.inl hk)
  have hleE : ∀ T' : Finset C, (∀ t ∈ T', t ∈ T₁ ∪ T₂ ∪ ys.biUnion Ty ∪ {c} ∪
      Finset.univ.image fun j ↦ (κ j : C)) → Subfield.closure ((K : Set C) ∪ T') ≤ E := by
    intro T' hT'
    refine Subfield.closure_le.mpr (Set.union_subset (fun k hk ↦ hKE hk) fun t ht ↦ ?_)
    exact hST t (hT' t ht)
  have hcE : c ∈ E := hST c (by simp)
  -- the norm of `E` is nontrivial
  obtain ⟨hdvr, -⟩ := hEdvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    ((NormedField.valuation (K := C)).comap E.subtype).valuationSubring
  have hϖ1 : ‖((ϖ : E) : C)‖ < 1 := by
    have h := (Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one.not.mp
      hϖ.not_isUnit
    have h' : ((NormedField.valuation (K := C)).comap E.subtype) (ϖ : E) ≤ 1 := ϖ.2
    have := lt_of_le_of_ne h' h
    simpa [Valuation.comap_apply, NormedField.valuation_apply, ← NNReal.coe_lt_coe] using this
  have hϖ0 : (ϖ : E) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  letI : NontriviallyNormedField E :=
    { (inferInstance : NormedField E) with
      non_trivial := ⟨(ϖ : E)⁻¹, by
        change 1 < ‖((ϖ : E)⁻¹ : C)‖
        rw [norm_inv]
        exact one_lt_inv₀ (norm_pos_iff.mpr (by exact_mod_cast hϖ0)) |>.mpr hϖ1⟩ }
  have hφ : ∀ e : E, ‖E.subtype e‖ = ‖e‖ := fun _ ↦ rfl
  -- the field `F₀ = E(x)(θ)`
  obtain ⟨qE, hqm, hq⟩ := exists_lift_minpoly hKE θ hcoeff
  haveI : Fact (Irreducible qE) := ⟨irreducible_qE E.subtype θ qE hqm hq⟩
  haveI := finiteDimensional_qE qE hqm
  have hχ := isCompat_χq E.subtype θ qE hq
  have hdeg := finrank_qE E.subtype θ qE hqm hq hθ
  have hθ₀ : Algebra.adjoin (RatFunc C) {χq E.subtype θ qE hq (AdjoinRoot.root qE)} = ⊤ := by
    rw [χq_root]; exact hθ
  have hrange : famE θ E ≤ (χq E.subtype θ qE hq).fieldRange :=
    famE_le_fieldRange (fun e he ↦ ⟨⟨e, he⟩, rfl⟩) hχ (χq_root E.subtype θ qE hq)
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : E, E.subtype c₀ = c := ⟨⟨c, hcE⟩, rfl⟩
  have hc₀ : c₀ ≠ 0 := fun h ↦ hc0 (by rw [← hc₀def, h, map_zero])
  have hc₀1 : ‖c₀‖ ≤ 1 := by rw [← hφ, hc₀def]; exact hc.le
  -- `e = 1` and linear disjointness at the outer vertices
  have hM₁ : famE θ (Subfield.closure ((K : Set C) ∪ T₁)) ≤
      (χq E.subtype θ qE hq).fieldRange :=
    (famE_mono θ (hleE T₁ fun t ht ↦ by simp [ht])).trans hrange
  obtain ⟨hinj₁, hgen₁⟩ := hT₁ _ hM₁
  have hinj := hinj_of_injOn (χq E.subtype θ qE hq) hinj₁
  have hgen := fun W ↦ hgen_of_adjoin (χq E.subtype θ qE hq) W (hgen₁ W)
  have heo := exists_valuation_eq hp hp1 hφ hχ hdeg hinj hgen
  have hLD₁ : letI := kEAlgebra E.subtype
      ConstantDescent.LinDisj (kE E.subtype) 𝓀 (resE (χq E.subtype θ qE hq) b₁.1) :=
    linDisj_resE hp hp1 hφ hχ hdeg hinj hgen b₁.1
  subst hc₀def
  -- the inner vertices, through the inversion
  haveI : Algebra.IsSeparable (RatFunc E) (Inv c₀ hc₀ (AdjoinRoot qE)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hχI := isCompat_χI hc₀ hc0 hχ
  have hdegI : Module.finrank (RatFunc E) (Inv c₀ hc₀ (AdjoinRoot qE)) =
      Module.finrank (RatFunc C) (Inv (E.subtype c₀) hc0 F') := by
    rw [finrank_inv, finrank_inv, hdeg]
  have hM₂ : (famE θ (Subfield.closure ((K : Set C) ∪ T₂)) : Subfield F') ≤
      (χI hc₀ hc0 (χq E.subtype θ qE hq)).fieldRange :=
    (famE_mono θ (hleE T₂ fun t ht ↦ by simp [ht])).trans hrange
  obtain ⟨hinj₂, hgen₂⟩ := hT₂ _ hM₂
  have hinjI := hinj_of_injOn (χI hc₀ hc0 (χq E.subtype θ qE hq)) hinj₂
  have hgenI := fun W ↦ hgen_of_adjoin (χI hc₀ hc0 (χq E.subtype θ qE hq)) W (hgen₂ W)
  have heoI := exists_valuation_eq hp hp1 hφ hχI hdegI hinjI hgenI
  have hLD₂ : letI := kEAlgebra E.subtype
      ConstantDescent.LinDisj (kE E.subtype) 𝓀
        (resE (χI hc₀ hc0 (χq E.subtype θ qE hq)) b₂.1) :=
    linDisj_resE hp hp1 hφ hχI hdegI hinjI hgenI b₂.1
  -- descending the finitely many elements
  obtain ⟨ι, hιdef⟩ : ∃ ι : BE (AdjoinRoot qE) c₀ →+* Rint (E.subtype c₀) F',
      ι = ιB (χq E.subtype θ qE hq) hφ hχ c₀ := ⟨_, rfl⟩
  have hι : ∀ b, (ι b : F') = χq E.subtype θ qE hq b := fun b ↦ by rw [hιdef]; rfl
  have hdesc : ∀ y ∈ ys, ∃ b, ι b = y := by
    intro y hy
    have h1 : (y : F') ∈ famE θ E := famE_mono θ (hleE (Ty y) fun t ht ↦ by
      simp only [Finset.mem_union, Finset.mem_biUnion]
      exact Or.inl (Or.inl (Or.inr ⟨y, hy, ht⟩))) (hTy y)
    obtain ⟨f, hf⟩ := hrange h1
    have hfB : f ∈ BE (AdjoinRoot qE) c₀ :=
      mem_BE_of_χ hφ hχ hdeg hθ₀ hc₀ hc₀1 (by rw [hf]; exact y.2)
    exact ⟨⟨f, hfB⟩, Subtype.ext (by rw [hι]; exact hf)⟩
  have hmem5 : ∀ y ∈ ({t₀, yu, yv, xR (E.subtype c₀), yR (E.subtype c₀)} : Finset _),
      y ∈ ys := fun y hy ↦ by rw [hys]; exact Finset.mem_union_left _ hy
  have hin5 : ∀ {y}, y = t₀ ∨ y = yu ∨ y = yv ∨ y = xR (E.subtype c₀) ∨
      y = yR (E.subtype c₀) → y ∈ ys := fun h ↦ hmem5 _ (by
    simp only [Finset.mem_insert, Finset.mem_singleton]; exact h)
  obtain ⟨t₀', ht₀'⟩ := hdesc t₀ (hin5 (by tauto))
  obtain ⟨yu', hyu'⟩ := hdesc yu (hin5 (by tauto))
  obtain ⟨yv', hyv'⟩ := hdesc yv (hin5 (by tauto))
  have hxrange : xR (E.subtype c₀) ∈ ι.range := hdesc _ (hin5 (by tauto))
  have hyrange : yR (E.subtype c₀) ∈ ι.range := hdesc _ (hin5 (by tauto))
  have hrrange' : ∀ j, r j ∈ ι.range := fun j ↦ hdesc _
    (by rw [hys]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  haveI : IsDiscreteValuationRing (HenselComplete.integers E) := by
    have : HenselComplete.integers E =
        ((NormedField.valuation (K := C)).comap E.subtype).valuationSubring := by
      rw [← vE, vE_eq E.subtype hφ]
    rw [this]; exact hdvr
  refine nonempty_nodeData hp hp1 hφ hχ hdeg hθ₀ rfl hc hc0 hP' hODP hb₁ hb₂ ι hι ?_ ?_ ?_ ?_
    t₀' ?_ ?_ ?_ yu' ?_ ?_ yv' ?_ ?_ ?_ ?_ ?_
  · exact heo
  · exact fun v f ↦ heoI (toInvExt hc0 v) f
  · exact hLD₁
  · exact hLD₂
  · rw [ht₀']; exact ht₀
  · rw [ht₀']; exact ht₀o
  · rw [ht₀']; exact ht₀i
  · rw [hyu']; exact hyu₁
  · rw [hyu']; exact hyu₂
  · rw [hyv']; exact hyv₂
  · rw [hyv']; exact hyv₁
  · exact hr ι.range hrrange' hxrange hyrange
  · refine exists_residue_of_span hφ hχ hc hc0 hP₁ (xR_mem hP') (yR_mem hP') ι hι hLD₁ r hr
      hrrange' hxrange hyrange fun j ↦ ?_
    have hκE : (κ j : C) ∈ E := hST _ (by simp)
    refine ⟨⟨κ j, hκE⟩, (HenselComplete.mem_integers_iff _).1 (κ j).2, ?_⟩
    rw [← hκ j]
    rfl
  · refine isAlgebraic_kE E.subtype ⟨fun x ↦ ?_⟩
    obtain ⟨q, hq0, hqx⟩ := halgK.isAlgebraic x
    refine ⟨q.map (Subfield.inclusion hKE), (Polynomial.map_ne_zero_iff
      (Subfield.inclusion hKE).injective).mpr hq0, ?_⟩
    rw [aeval_def, eval₂_map]
    exact hqx

end Main

end DVRDescent

end SemistableReduction
