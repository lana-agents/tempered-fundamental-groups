/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentKernel
import TemperedFundamentalGroups.SemistableReduction.DVRDescentSpan
import TemperedFundamentalGroups.SemistableReduction.NodeDescentAlgebra

/-!
# Exact node data from an ordinary double point over `C` (O1, the local assembly)

Blueprint §9.12, O1. Given the descent data over a complete discretely valued `E ⊆ C` (the
integral closure `B_E` of the node chart over `O_E` in `F₀`, `e = 1` at all vertices, linear
disjointness at the two branch vertices, finitely many descended elements: a killer `t₀` of the
other vertices, parameters `y_u`, `y_v` of the two branches, the spanning of all reductions, and
rational residues), the local ring `D = (B_E)_𝔭` at `𝔭 = P' ∩ B_E` is an ordinary double point over
`O_E` (`isOrdinaryDoublePoint_of_fibreProduct`), so the node deformation
`IsOrdinaryDoublePoint.exists_node` gives exact coordinates `u v = ϖⁿ`, `x = ε u^d`, which are the
exact node data `GaussTube.NodeData` at `P'` (**`nonempty_nodeData`**).
-/

open NNReal Polynomial IsLocalRing Valuation WithZero

namespace SemistableReduction

namespace DVRDescent

open GaussTube FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm
  ConstantDescent

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* F'}

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Local

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ] (Q : CurvePlace k κ) (M : Subring κ)

/-- The local ring at a place of the subfield `M`: elements of `M` regular at `Q`. -/
def placeSub : Subring κ := Q.V.toSubring ⊓ M

variable {Q M}

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
lemma mem_placeSub {a : κ} : a ∈ placeSub Q M ↔ a ∈ Q.V ∧ a ∈ M := Iff.rfl

/-- The residue map on `placeSub`. -/
noncomputable def placeSubRes : placeSub Q M →+* k where
  toFun a := Q.res a
  map_one' := Q.res_one
  map_mul' a b := Q.res_mul a.2.1 b.2.1
  map_zero' := Q.res_zero
  map_add' a b := Q.res_add a.2.1 b.2.1

lemma placeSubRes_apply (a : placeSub Q M) : placeSubRes a = Q.res a := rfl

variable (Q) in
/-- The residue map on the valuation ring of a place. -/
noncomputable def placeRes : Q.V.toSubring →+* k where
  toFun a := Q.res a
  map_one' := Q.res_one
  map_mul' a b := Q.res_mul a.2 b.2
  map_zero' := Q.res_zero
  map_add' a b := Q.res_add a.2 b.2

lemma placeRes_apply (a : Q.V.toSubring) : placeRes Q a = Q.res a := rfl

lemma valuation_eq_one_of_res_ne_zero' {a : κ} (ha : a ∈ Q.V) (h : Q.res a ≠ 0) :
    Q.valuation a = 1 :=
  le_antisymm (Q.valuation_le_one_iff.2 ha) (not_lt.1 fun hlt ↦ h (Q.res_eq_zero_of_lt_one hlt))

variable (hM : ∀ a ∈ M, a⁻¹ ∈ M)
include hM

lemma isUnit_of_res_ne_zero {a : placeSub Q M} (h : placeSubRes a ≠ 0) : IsUnit a := by
  have hv := valuation_eq_one_of_res_ne_zero' a.2.1 h
  have ha0 : (a : κ) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hinv : (a : κ)⁻¹ ∈ placeSub Q M := by
    refine ⟨Q.valuation_le_one_iff.1 ?_, hM _ a.2.2⟩
    rw [map_inv₀, hv, inv_one]
  exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : placeSub Q M) (Subtype.ext (mul_inv_cancel₀ ha0))

theorem isLocalRing_placeSub : IsLocalRing (placeSub Q M) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  by_cases h : placeSubRes a = 0
  · right
    refine isUnit_of_res_ne_zero hM ?_
    rw [_root_.map_sub, map_one, h, sub_zero]
    exact one_ne_zero
  · exact Or.inl (isUnit_of_res_ne_zero hM h)

theorem placeSubRes_eq_zero_iff (a : placeSub Q M) :
    letI := isLocalRing_placeSub (Q := Q) hM
    placeSubRes a = 0 ↔ a ∈ maximalIdeal (placeSub Q M) := by
  letI := isLocalRing_placeSub (Q := Q) hM
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hu
    have := hu.map placeSubRes
    rw [h] at this
    exact not_isUnit_zero this
  · intro h
    by_contra h'
    exact h (isUnit_of_res_ne_zero hM h')

omit hM in
lemma res_ne_zero_of_valuation_eq_one {a : κ} (ha : a ∈ Q.V) (h : Q.valuation a = 1) :
    Q.res a ≠ 0 := by
  intro h0
  have := Q.valuation_sub_res_lt_one ha
  rw [h0, map_zero, sub_zero, h] at this
  exact lt_irrefl _ this

/-- A uniformizer generates the maximal ideal of `placeSub`. -/
theorem maximalIdeal_placeSub {t : placeSub Q M} (ht : Q.valuation (t : κ) = exp (-1)) :
    letI := isLocalRing_placeSub (Q := Q) hM
    maximalIdeal (placeSub Q M) = Ideal.span {t} := by
  letI := isLocalRing_placeSub (Q := Q) hM
  have ht0 : (t : κ) ≠ 0 := fun h ↦ by rw [h, map_zero] at ht; exact exp_ne_zero ht.symm
  refine le_antisymm (fun a ha ↦ ?_) ?_
  · rw [← placeSubRes_eq_zero_iff hM] at ha
    rw [Ideal.mem_span_singleton']
    by_cases ha0 : (a : κ) = 0
    · exact ⟨0, Subtype.ext (by rw [Subring.coe_mul, ha0]; simp)⟩
    have hlt : Q.valuation (a : κ) < 1 := by
      by_contra h
      exact res_ne_zero_of_valuation_eq_one a.2.1
        (le_antisymm (Q.valuation_le_one_iff.2 a.2.1) (not_lt.1 h)) ha
    obtain ⟨n, hn⟩ := ConductorLocal.valuation_le_exp_of_ne_zero Q ha0 a.2.1
    have hn1 : 1 ≤ n := by
      by_contra h
      have : n = 0 := by omega
      rw [hn, this] at hlt
      simp at hlt
    have hw : (a : κ) / t ∈ placeSub Q M := by
      refine ⟨Q.valuation_le_one_iff.1 ?_, ?_⟩
      · rw [map_div₀, hn, ht, div_le_one₀ exp_pos, exp_le_exp]
        omega
      · rw [div_eq_mul_inv]; exact M.mul_mem a.2.2 (hM _ t.2.2)
    refine ⟨⟨_, hw⟩, Subtype.ext ?_⟩
    change (a : κ) / t * t = a
    rw [div_mul_cancel₀ _ ht0]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ← placeSubRes_eq_zero_iff hM]
    exact Q.res_eq_zero_of_lt_one (by rw [ht, ← exp_zero, exp_lt_exp]; omega)

end Local

section ResE

variable {F'' : Type*} [Field F''] [Algebra (RatFunc C) F''] [Algebra C F'']
  [IsScalarTower C (RatFunc C) F''] {ψ : F₀ →+* F''}

omit [IsAlgClosed C] [Algebra C F''] [IsScalarTower C (RatFunc C) F''] in
/-- The residues over `E` form a field. -/
lemma resE_inv_mem {W : Ext C F''} {z : ResidueField W.1.valuationSubring} (hz : z ∈ resE ψ W) :
    z⁻¹ ∈ resE ψ W := by
  obtain ⟨f, hf, rfl⟩ := hz
  by_cases h0 : red C (ψ f) W = 0
  · rw [h0, inv_zero]; exact (resE ψ W).zero_mem
  have h1 : W.1 (ψ f) = 1 := le_antisymm hf (not_lt.1 fun hlt ↦ h0 ((red_eq_zero_iff hf).2 hlt))
  have hf0 : ψ f ≠ 0 := by intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
  have h2 : W.1 (ψ f⁻¹) = 1 := by rw [map_inv₀, map_inv₀, h1, inv_one]
  refine ⟨f⁻¹, h2.le, ?_⟩
  have h3 := red_mul (w := W) hf h2.le
  rw [← map_mul, mul_inv_cancel₀ (by simpa using hf0), map_one, red_one] at h3
  exact (eq_inv_of_mul_eq_one_right h3.symm)

end ResE

/-- `χ` into the inverted field. -/
noncomputable def χInv {c : C} (hc0 : c ≠ 0) (χ : F₀ →+* F') : F₀ →+* Inv c hc0 F' :=
  (toInv hc0).toRingHom.comp χ

section Branches

variable {c₀ : E} (hc : ‖φ c₀‖ < 1) (hc0 : φ c₀ ≠ 0) (ι : BE F₀ c₀ →+* Rint (φ c₀) F')
  (b₁ : OuterBranch C F') (b₂ : OuterBranch C (Inv (φ c₀) hc0 F'))

/-- The residue at the point of the inner branch, as a map on `R'`. -/
noncomputable def innerRes : Rint (φ c₀) F' →+* 𝓀 :=
  (placeHom hc b₂.1 b₂.2.2).comp (rintEquiv hc0).toRingHom

omit [IsUltrametricDist E] in
lemma innerRes_apply (y : Rint (φ c₀) F') :
    innerRes hc hc0 b₂ y = b₂.2.1.res (redHomInv hc hc0 b₂.1 y) := rfl

omit [IsUltrametricDist E] in
lemma innerRes_constR (κ : HenselComplete.integers C) :
    innerRes hc hc0 b₂ (constR (φ c₀) κ) = residue _ κ := by
  rw [innerRes_apply, redHomInv_constR, CurvePlace.res_algebraMap]

omit [IsUltrametricDist E] in
lemma placeHom_constR' (κ : HenselComplete.integers C) :
    placeHom hc b₁.1 b₁.2.2 (constR (φ c₀) κ) = residue _ κ := by
  rw [placeHom_apply, ← redHom_apply hc, redHom_constR, CurvePlace.res_algebraMap]

variable {ι} (hι : ∀ y, (ι y : F') = χ y)
include hι

lemma red_mem₁ (b : BE F₀ c₀) : redHom hc b₁.1 (ι b) ∈ placeSub b₁.2.1 (resE χ b₁.1) := by
  refine ⟨red_mem_V hc b₁.1 (ι b) b₁.2.2, (b : F₀), ?_, ?_⟩
  · rw [← hι]; exact valuation_le_one_R hc b₁.1 (ι b)
  · rw [redHom_apply, hι]

lemma red_mem₂ (b : BE F₀ c₀) :
    redHomInv hc hc0 b₂.1 (ι b) ∈ placeSub b₂.2.1 (resE (χInv hc0 χ) b₂.1) := by
  refine ⟨red_mem_V hc b₂.1 (rintEquiv hc0 (ι b)) b₂.2.2, (b : F₀), ?_, ?_⟩
  · have := valuation_le_one_R hc b₂.1 (rintEquiv hc0 (ι b))
    change b₂.1.1 (toInv hc0 ((ι b : Rint (φ c₀) F') : F')) ≤ 1 at this
    rw [hι] at this
    exact this
  · change red C (toInv hc0 (χ b)) b₂.1 = red C (toInv hc0 ((ι b : Rint (φ c₀) F') : F')) b₂.1
    rw [hι]

/-- The reduction of `B_E` at the outer branch. -/
noncomputable def phi₁ : BE F₀ c₀ →+* placeSub b₁.2.1 (resE χ b₁.1) :=
  ((redHom hc b₁.1).comp ι).codRestrict _ (red_mem₁ hc b₁ hι)

/-- The reduction of `B_E` at the inner branch. -/
noncomputable def phi₂ : BE F₀ c₀ →+* placeSub b₂.2.1 (resE (χInv hc0 χ) b₂.1) :=
  ((redHomInv hc hc0 b₂.1).comp ι).codRestrict _ (red_mem₂ hc hc0 b₂ hι)

lemma coe_phi₁ (b : BE F₀ c₀) :
    (phi₁ hc b₁ hι b : ResidueField b₁.1.1.valuationSubring) = redHom hc b₁.1 (ι b) := rfl

lemma coe_phi₂ (b : BE F₀ c₀) :
    (phi₂ hc hc0 b₂ hι b : ResidueField b₂.1.1.valuationSubring) = redHomInv hc hc0 b₂.1 (ι b) :=
  rfl

lemma placeSubRes_phi₁ (b : BE F₀ c₀) :
    placeSubRes (phi₁ hc b₁ hι b) = placeHom hc b₁.1 b₁.2.2 (ι b) := rfl

lemma placeSubRes_phi₂ (b : BE F₀ c₀) :
    placeSubRes (phi₂ hc hc0 b₂ hι b) = innerRes hc hc0 b₂ (ι b) := rfl

end Branches

section Points

variable {c₀ : E} (hc : ‖φ c₀‖ < 1) (hc0 : φ c₀ ≠ 0) {P' : Ideal (Rint (φ c₀) F')}
  [P'.IsMaximal] {b₁ : OuterBranch C F'} {b₂ : OuterBranch C (Inv (φ c₀) hc0 F')}

include hc in
omit [IsUltrametricDist E] [P'.IsMaximal] in
lemma placeIdeal_eq₁ (hb₁ : outerBranches hc P' = {b₁}) : placeIdeal hc b₁.1 b₁.2.2 = P' := by
  have : b₁ ∈ outerBranches hc P' := by rw [hb₁]; rfl
  exact this

omit [IsUltrametricDist E] [P'.IsMaximal] in
lemma notMem_iff₁ (hb₁ : outerBranches hc P' = {b₁}) (y : Rint (φ c₀) F') :
    y ∉ P' ↔ placeHom hc b₁.1 b₁.2.2 y ≠ 0 := by
  rw [← placeIdeal_eq₁ hc hb₁, placeIdeal, RingHom.mem_ker]

omit [IsUltrametricDist E] [P'.IsMaximal] in
lemma notMem_iff₂ (hb₂ : innerBranches hc hc0 P' = {b₂}) (y : Rint (φ c₀) F') :
    y ∉ P' ↔ innerRes hc hc0 b₂ y ≠ 0 := by
  have hP₂ : placeIdeal hc b₂.1 b₂.2.2 = P'.comap (rintEquiv hc0).symm.toRingHom := by
    have : b₂ ∈ innerBranches hc hc0 P' := by rw [hb₂]; rfl
    exact this
  have : y ∈ P' ↔ rintEquiv hc0 y ∈ placeIdeal hc b₂.1 b₂.2.2 := by
    rw [hP₂, Ideal.mem_comap]
    simp
  rw [this, placeIdeal, RingHom.mem_ker]
  rfl

omit [IsUltrametricDist E] [P'.IsMaximal] in
/-- **The two branches have the same residue map** on `R'`. -/
lemma placeHom_eq_innerRes (hb₁ : outerBranches hc P' = {b₁})
    (hb₂ : innerBranches hc hc0 P' = {b₂}) (y : Rint (φ c₀) F') :
    placeHom hc b₁.1 b₁.2.2 y = innerRes hc hc0 b₂ y := by
  obtain ⟨κ, hκ⟩ := exists_sub_constR_mem hc b₁ y
  have h1 : placeHom hc b₁.1 b₁.2.2 (y - constR (φ c₀) κ) = 0 := hκ
  have h2 : innerRes hc hc0 b₂ (y - constR (φ c₀) κ) = 0 := by
    have hm : y - constR (φ c₀) κ ∈ P' := placeIdeal_eq₁ hc hb₁ ▸ hκ
    by_contra h
    exact (notMem_iff₂ hc hc0 hb₂ _).mpr h hm
  rw [_root_.map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, placeHom_constR', innerRes_constR]

end Points

lemma isSpanned_swap {k R κ₁ κ₂ : Type*} [Field k] [CommRing R] [Field κ₁] [Field κ₂]
    [Algebra k κ₁] [Algebra k κ₂] {B : Subring R} {ρ₁ : R →+* κ₁} {ρ₂ : R →+* κ₂} {y : R}
    (h : IsSpanned k B ρ₁ ρ₂ y) : IsSpanned k B ρ₂ ρ₁ y := by
  obtain ⟨n, lam, b, hb, h₁, h₂⟩ := h
  exact ⟨n, lam, b, hb, h₂, h₁⟩

section Descent

variable {c₀ : E} (hc : ‖φ c₀‖ < 1) (hc0 : φ c₀ ≠ 0) {P' : Ideal (Rint (φ c₀) F')}
  [P'.IsMaximal] {b₁ : OuterBranch C F'} {b₂ : OuterBranch C (Inv (φ c₀) hc0 F')}
  {ι : BE F₀ c₀ →+* Rint (φ c₀) F'} (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
  (hι : ∀ y, (ι y : F') = χ y)

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
include hι hχ in
lemma ι_algebraMap (a : nodeRing c₀) :
    ((ι (algebraMap (nodeRing c₀) (BE F₀ c₀) a) : Rint (φ c₀) F') : F') =
      algebraMap (RatFunc C) F' (ratFuncMap φ a) := by
  rw [hι]
  exact hχ a

include hφ in
omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
lemma norm_le_one_of_mem {e : E} (he : e ∈ (vE φ).valuationSubring) : ‖e‖ ≤ 1 := by
  have h : vE φ e ≤ 1 := he
  rw [vE_eq φ hφ, NormedField.valuation_apply] at h
  exact_mod_cast h

/-- The constant `e ∈ O_E` as an element of `B_E`. -/
noncomputable def cstB (e : E) (he : ‖e‖ ≤ 1) : BE F₀ c₀ :=
  algebraMap (nodeRing c₀) (BE F₀ c₀) ⟨algebraMap E (RatFunc E) e, algebraMap_mem_nodeRing he⟩

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
include hι hχ hφ in
omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma ι_cstB (e : E) (he : ‖e‖ ≤ 1) :
    ι (cstB e he) =
      constR (φ c₀) ⟨φ e, (HenselComplete.mem_integers_iff _).2 (by rw [hφ]; exact he)⟩ := by
  apply Subtype.ext
  rw [cstB, ι_algebraMap hχ hι, ratFuncMap_algebraMap_C]
  rfl

/-- The `O_E`-algebra structure on `B_E` through the constants. -/
@[reducible] noncomputable def algO (c₀ : E) : Algebra (HenselComplete.integers E) (BE F₀ c₀) :=
  ((algebraMap (nodeRing c₀) (BE F₀ c₀)).comp
    (((algebraMap E (RatFunc E)).comp (HenselComplete.integers E).subtype).codRestrict _
      fun e ↦ algebraMap_mem_nodeRing ((HenselComplete.mem_integers_iff _).1 e.2))).toAlgebra

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
lemma algO_apply (c₀ : E) (o : HenselComplete.integers E) :
    letI := algO (F₀ := F₀) c₀
    algebraMap (HenselComplete.integers E) (BE F₀ c₀) o =
      cstB (o : E) ((HenselComplete.mem_integers_iff _).1 o.2) := rfl

include hc in
omit [IsUltrametricDist E] in
lemma redHomInv_toInvExt_eq_zero_iff (v : GaussExtension (0 : C) (invRad hc0 1) F')
    (y : Rint (φ c₀) F') :
    redHomInv hc hc0 (toInvExt hc0 v) y = 0 ↔ v.1 (y : F') < 1 := by
  have h := red_eq_zero_iff (valuation_le_one_R hc (toInvExt hc0 v) (rintEquiv hc0 y))
  change red C (toInv hc0 (y : F')) (toInvExt hc0 v) = 0 ↔ _
  refine h.trans ?_
  change (toInvExt hc0 v).1 (toInv hc0 (y : F')) < 1 ↔ _
  rw [toInvExt_apply]

include hc in
omit [IsUltrametricDist E] in
lemma redHom_eq_zero_iff (v : Ext C F') (y : Rint (φ c₀) F') :
    redHom hc v y = 0 ↔ v.1 (y : F') < 1 := by
  rw [redHom_apply, red_eq_zero_iff (valuation_le_one_R hc v y)]

include hι hχ hφ in
/-- The constants of `κ_E` lift to `B_E`. -/
lemma descent_const :
    letI := kEAlgebra φ
    ∀ t : kE φ, ∃ o ∈ ι.range, redHom hc b₁.1 o = algebraMap 𝓀 _ (algebraMap (kE φ) 𝓀 t) ∧
      redHomInv hc hc0 b₂.1 o = algebraMap 𝓀 _ (algebraMap (kE φ) 𝓀 t) := by
  letI := kEAlgebra φ
  intro t
  obtain ⟨e, rfl⟩ := residue_surjective t
  have he := norm_le_one_of_mem hφ e.2
  have ht : algebraMap (kE φ) 𝓀 (residue _ e) = residue (HenselComplete.integers C)
      ⟨φ e, (HenselComplete.mem_integers_iff _).2 (by rw [hφ]; exact he)⟩ := by
    change ResidueField.map (integersMap φ) (residue _ e) = _
    rw [ResidueField.map_residue]
    rfl
  refine ⟨ι (cstB (e : E) he), ⟨_, rfl⟩, ?_, ?_⟩
  · rw [ι_cstB hφ hχ hι, redHom_constR hc b₁.1, ht]
  · have h1 := ι_cstB (c₀ := c₀) (F₀ := F₀) hφ hχ hι (e : E) he
    have h2 := redHomInv_constR hc hc0 b₂.1
      ⟨φ e, (HenselComplete.mem_integers_iff _).2 (by rw [hφ]; exact he)⟩
    exact (congrArg (redHomInv hc hc0 b₂.1) h1).trans (h2.trans (congrArg _ ht.symm))

omit [IsUltrametricDist E] [P'.IsMaximal] in
/-- The fibre-product clause of `IsNodeODP` for the given branches. -/
lemma fp_of_isNodeODP (hb₁ : outerBranches hc P' = {b₁}) (hb₂ : innerBranches hc hc0 P' = {b₂})
    (hODP : IsNodeODP hc hc0 P') :
    ∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b →
      ∃ y s : Rint (φ c₀) F', s ∉ P' ∧ redHom hc b₁.1 y = a * redHom hc b₁.1 s ∧
        redHomInv hc hc0 b₂.1 y = b * redHomInv hc hc0 b₂.1 s := by
  obtain ⟨c₁, c₂, h₁, h₂, hfpC⟩ := hODP
  have e₁ : c₁ = b₁ := Set.singleton_injective (h₁.symm.trans hb₁)
  have e₂ : c₂ = b₂ := Set.singleton_injective (h₂.symm.trans hb₂)
  subst c₁ c₂
  intro a ha b hb hab
  obtain ⟨y, s, hs, h1, h2⟩ := hfpC a ha b hb hab
  exact ⟨y, s, (placeIdeal_eq₁ hc hb₁) ▸ hs, h1, h2⟩

omit [P'.IsMaximal] in
include hι hχ hφ in
/-- **Descent of the fibre product**: matching pairs on the branches over `E` are reached by
`B_E` localized at `P' ∩ B_E`. -/
lemma descent_fp (hb₁ : outerBranches hc P' = {b₁})
    (hfpC : ∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b →
      ∃ y s : Rint (φ c₀) F', s ∉ P' ∧ redHom hc b₁.1 y = a * redHom hc b₁.1 s ∧
        redHomInv hc hc0 b₂.1 y = b * redHomInv hc hc0 b₂.1 s)
    (hLD₁ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE χ b₁.1))
    (hLD₂ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE (χInv hc0 χ) b₂.1))
    (hspan : ∀ y, IsSpanned 𝓀 ι.range (redHom hc b₁.1) (redHomInv hc hc0 b₂.1) y)
    (a : placeSub b₁.2.1 (resE χ b₁.1)) (b : placeSub b₂.2.1 (resE (χInv hc0 χ) b₂.1))
    (hab : placeSubRes a = placeSubRes b) :
    ∃ y s : BE F₀ c₀, s ∉ P'.comap ι ∧ phi₁ hc b₁ hι y = a * phi₁ hc b₁ hι s ∧
      phi₂ hc hc0 b₂ hι y = b * phi₂ hc hc0 b₂ hι s := by
  letI := kEAlgebra φ
  have hab' : b₁.2.1.res (a : ResidueField b₁.1.1.valuationSubring) =
      b₂.2.1.res (b : ResidueField b₂.1.1.valuationSubring) := by
    exact (placeSubRes_apply a).symm.trans (hab.trans (placeSubRes_apply b))
  have ha1 := (mem_placeSub.1 a.2).1
  have hb1 := (mem_placeSub.1 b.2).1
  have hex := hfpC (a : ResidueField b₁.1.1.valuationSubring) ha1
    (b : ResidueField b₂.1.1.valuationSubring) hb1 hab'
  obtain ⟨y, hy⟩ := hex
  obtain ⟨s, hs⟩ := hy
  obtain ⟨hs, hy₁, hy₂⟩ := hs
  have hM₁ : ∀ z ∈ ι.range, redHom hc b₁.1 z ∈ resE χ b₁.1 := by
    rintro _ ⟨z, rfl⟩; exact (red_mem₁ hc b₁ hι z).2
  have hM₂ : ∀ z ∈ ι.range, redHomInv hc hc0 b₂.1 z ∈ resE (χInv hc0 χ) b₂.1 := by
    rintro _ ⟨z, rfl⟩; exact (red_mem₂ hc hc0 b₂ hι z).2
  have hsr : placeRes b₁.2.1 ⟨redHom hc b₁.1 s, red_mem_V hc b₁.1 s b₁.2.2⟩ ≠ 0 :=
    (notMem_iff₁ hc hb₁ s).mp hs
  have key := exists_fp_descent (k₀ := kE φ) (k := 𝓀) hM₁ hM₂ hLD₁ hLD₂
      (descent_const hc hc0 hφ hχ hι) b₁.2.1.V.toSubring (placeRes b₁.2.1)
      (fun z ↦ red_mem_V hc b₁.1 z b₁.2.2) (fun t ↦ b₁.2.1.algebraMap_mem t)
      (mem_placeSub.1 a.2).2 (mem_placeSub.1 b.2).2 (hspan y) (hspan s) hsr hy₁ hy₂
  obtain ⟨y', hy'⟩ := key
  obtain ⟨⟨yB, rfl⟩, hy'⟩ := hy'
  obtain ⟨s', hs'⟩ := hy'
  obtain ⟨⟨sB, rfl⟩, hs'⟩ := hs'
  obtain ⟨hs', e₁, e₂⟩ := hs'
  exact ⟨yB, sB, fun h ↦ (notMem_iff₁ hc hb₁ (ι sB)).mpr hs' h, Subtype.ext e₁, Subtype.ext e₂⟩

include hι hχ hφ in
/-- The residue of a constant of `O_E`. -/
lemma placeSubRes_phi₁_cstB (e : (vE φ).valuationSubring) :
    letI := kEAlgebra φ
    placeSubRes (phi₁ hc b₁ hι (cstB (e : E) (norm_le_one_of_mem hφ e.2))) =
      algebraMap (kE φ) 𝓀 (residue _ e) := by
  letI := kEAlgebra φ
  rw [placeSubRes_phi₁, ι_cstB hφ hχ hι, placeHom_constR']
  change _ = ResidueField.map (integersMap φ) (residue _ e)
  rw [ResidueField.map_residue]
  rfl

set_option maxHeartbeats 2000000 in
-- the branch types are elaboration-heavy
omit [P'.IsMaximal] in
include hι hχ hφ in
/-- **Residues over `E` at the outer branch are rational.** -/
lemma descent_res₁ (hb₁ : outerBranches hc P' = {b₁}) (hb₂ : innerBranches hc hc0 P' = {b₂})
    (hfpC : ∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b →
      ∃ y s : Rint (φ c₀) F', s ∉ P' ∧ redHom hc b₁.1 y = a * redHom hc b₁.1 s ∧
        redHomInv hc hc0 b₂.1 y = b * redHomInv hc hc0 b₂.1 s)
    (hLD₁ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE χ b₁.1))
    (hLD₂ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE (χInv hc0 χ) b₂.1))
    (hspan : ∀ y, IsSpanned 𝓀 ι.range (redHom hc b₁.1) (redHomInv hc hc0 b₂.1) y)
    (hres : letI := kEAlgebra φ; ∀ b : BE F₀ c₀, ∃ t : kE φ,
      placeHom hc b₁.1 b₁.2.2 (ι b) = algebraMap (kE φ) 𝓀 t)
    (halgk : letI := kEAlgebra φ; Algebra.IsAlgebraic (kE φ) 𝓀)
    (a : placeSub b₁.2.1 (resE χ b₁.1)) :
    ∃ (e : E) (he : ‖e‖ ≤ 1), placeSubRes (phi₁ hc b₁ hι (cstB e he)) = placeSubRes a := by
  letI := kEAlgebra φ
  have ha1 := (mem_placeSub.1 a.2).1
  have hlam : b₂.2.1.res (algebraMap 𝓀 (ResidueField b₂.1.1.valuationSubring) (placeSubRes a)) =
      b₁.2.1.res (a : ResidueField b₁.1.1.valuationSubring) :=
    (CurvePlace.res_algebraMap _ _).trans (placeSubRes_apply a)
  have hex := hfpC (a : ResidueField b₁.1.1.valuationSubring) ha1
    (algebraMap 𝓀 _ (placeSubRes a)) (b₂.2.1.algebraMap_mem _) hlam.symm
  obtain ⟨y, hy⟩ := hex
  obtain ⟨s, hs⟩ := hy
  obtain ⟨hs, hy₁, hy₂⟩ := hs
  have hM₁ : ∀ z ∈ ι.range, redHom hc b₁.1 z ∈ resE χ b₁.1 := by
    rintro _ ⟨z, rfl⟩; exact (red_mem₁ hc b₁ hι z).2
  have hM₂ : ∀ z ∈ ι.range, redHomInv hc hc0 b₂.1 z ∈ resE (χInv hc0 χ) b₂.1 := by
    rintro _ ⟨z, rfl⟩; exact (red_mem₂ hc hc0 b₂ hι z).2
  have hsr : placeRes b₁.2.1 ⟨redHom hc b₁.1 s, red_mem_V hc b₁.1 s b₁.2.2⟩ ≠ 0 :=
    (notMem_iff₁ hc hb₁ s).mp hs
  have hcomp : ∀ z, placeRes b₁.2.1 ⟨redHom hc b₁.1 z, red_mem_V hc b₁.1 z b₁.2.2⟩ =
      placeRes b₂.2.1 ⟨redHomInv hc hc0 b₂.1 z, red_mem_V hc b₂.1 (rintEquiv hc0 z) b₂.2.2⟩ :=
    fun z ↦ placeHom_eq_innerRes hc hc0 hb₁ hb₂ z
  have hresB : ∀ z ∈ ι.range, ∃ t : kE φ,
      placeRes b₁.2.1 ⟨redHom hc b₁.1 z, red_mem_V hc b₁.1 z b₁.2.2⟩ = algebraMap (kE φ) 𝓀 t := by
    rintro _ ⟨z, rfl⟩; exact hres z
  obtain ⟨t, ht⟩ := exists_residue_eq (k₀ := kE φ) (k := 𝓀) hM₁ hM₂ hLD₁ hLD₂
    (descent_const hc hc0 hφ hχ hι) b₁.2.1.V.toSubring (placeRes b₁.2.1)
    (fun z ↦ red_mem_V hc b₁.1 z b₁.2.2) (fun t ↦ b₁.2.1.algebraMap_mem t)
    b₂.2.1.V.toSubring (placeRes b₂.2.1) (fun z ↦ red_mem_V hc b₂.1 (rintEquiv hc0 z) b₂.2.2)
    (fun t ↦ b₂.2.1.algebraMap_mem t) (fun t ↦ CurvePlace.res_algebraMap _ t) hcomp hresB
    (mem_placeSub.1 a.2).2 ha1 (hspan y) (hspan s) hsr hy₁ hy₂
  obtain ⟨e, rfl⟩ := residue_surjective t
  exact ⟨e, norm_le_one_of_mem hφ e.2,
    (placeSubRes_phi₁_cstB hc hφ hχ hι e).trans (ht.symm.trans (placeSubRes_apply _).symm)⟩

set_option maxHeartbeats 10000000 in
-- the branch types are elaboration-heavy
omit [P'.IsMaximal] in
include hι hχ hφ in
/-- **Residues over `E` at the inner branch are rational.** -/
lemma descent_res₂ (hb₁ : outerBranches hc P' = {b₁}) (hb₂ : innerBranches hc hc0 P' = {b₂})
    (hfpC : ∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b →
      ∃ y s : Rint (φ c₀) F', s ∉ P' ∧ redHom hc b₁.1 y = a * redHom hc b₁.1 s ∧
        redHomInv hc hc0 b₂.1 y = b * redHomInv hc hc0 b₂.1 s)
    (hLD₁ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE χ b₁.1))
    (hLD₂ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE (χInv hc0 χ) b₂.1))
    (hspan : ∀ y, IsSpanned 𝓀 ι.range (redHom hc b₁.1) (redHomInv hc hc0 b₂.1) y)
    (hres : letI := kEAlgebra φ; ∀ b : BE F₀ c₀, ∃ t : kE φ,
      placeHom hc b₁.1 b₁.2.2 (ι b) = algebraMap (kE φ) 𝓀 t)
    (halgk : letI := kEAlgebra φ; Algebra.IsAlgebraic (kE φ) 𝓀)
    (b : placeSub b₂.2.1 (resE (χInv hc0 χ) b₂.1)) :
    ∃ (e : E) (he : ‖e‖ ≤ 1), placeSubRes (phi₁ hc b₁ hι (cstB e he)) = placeSubRes b := by
  letI := kEAlgebra φ
  have hb1 := (mem_placeSub.1 b.2).1
  have hlam : b₁.2.1.res (algebraMap 𝓀 (ResidueField b₁.1.1.valuationSubring) (placeSubRes b)) =
      b₂.2.1.res (b : ResidueField b₂.1.1.valuationSubring) :=
    (CurvePlace.res_algebraMap _ _).trans (placeSubRes_apply b)
  have hex := hfpC (algebraMap 𝓀 _ (placeSubRes b)) (b₁.2.1.algebraMap_mem _)
    (b : ResidueField b₂.1.1.valuationSubring) hb1 hlam
  obtain ⟨y, hy⟩ := hex
  obtain ⟨s, hs⟩ := hy
  obtain ⟨hs, hy₁, hy₂⟩ := hs
  have hM₁ : ∀ z ∈ ι.range, redHom hc b₁.1 z ∈ resE χ b₁.1 := by
    rintro _ ⟨z, rfl⟩; exact (red_mem₁ hc b₁ hι z).2
  have hM₂ : ∀ z ∈ ι.range, redHomInv hc hc0 b₂.1 z ∈ resE (χInv hc0 χ) b₂.1 := by
    rintro _ ⟨z, rfl⟩; exact (red_mem₂ hc hc0 b₂ hι z).2
  have hcomp : ∀ z, placeRes b₂.2.1 ⟨redHomInv hc hc0 b₂.1 z,
      red_mem_V hc b₂.1 (rintEquiv hc0 z) b₂.2.2⟩ =
      placeRes b₁.2.1 ⟨redHom hc b₁.1 z, red_mem_V hc b₁.1 z b₁.2.2⟩ :=
    fun z ↦ (placeHom_eq_innerRes hc hc0 hb₁ hb₂ z).symm
  have hsr : placeRes b₂.2.1 ⟨redHomInv hc hc0 b₂.1 s,
      red_mem_V hc b₂.1 (rintEquiv hc0 s) b₂.2.2⟩ ≠ 0 :=
    (notMem_iff₂ hc hc0 hb₂ s).mp hs
  have hresB : ∀ z ∈ ι.range, ∃ t : kE φ, placeRes b₂.2.1 ⟨redHomInv hc hc0 b₂.1 z,
      red_mem_V hc b₂.1 (rintEquiv hc0 z) b₂.2.2⟩ = algebraMap (kE φ) 𝓀 t := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := hres z
    exact ⟨t, (hcomp (ι z)).trans ht⟩
  have hconst := descent_const hc hc0 hφ hχ hι (b₁ := b₁) (b₂ := b₂)
  have hconst' : ∀ t : kE φ, ∃ o ∈ ι.range,
      redHomInv hc hc0 b₂.1 o = algebraMap 𝓀 _ (algebraMap (kE φ) 𝓀 t) ∧
      redHom hc b₁.1 o = algebraMap 𝓀 _ (algebraMap (kE φ) 𝓀 t) := by
    intro t
    obtain ⟨o, ho, h1, h2⟩ := hconst t
    exact ⟨o, ho, h2, h1⟩
  have hy₁' : redHom hc b₁.1 y = algebraMap 𝓀 (ResidueField b₁.1.1.valuationSubring)
      (placeRes b₂.2.1 ⟨(b : ResidueField b₂.1.1.valuationSubring), hb1⟩) *
        redHom hc b₁.1 s := by
    have e : placeSubRes b = placeRes b₂.2.1 ⟨(b : ResidueField b₂.1.1.valuationSubring), hb1⟩ :=
      (placeSubRes_apply b).trans
        (placeRes_apply (Q := b₂.2.1) ⟨(b : ResidueField b₂.1.1.valuationSubring), hb1⟩).symm
    rw [← e]
    exact hy₁
  obtain ⟨t, ht⟩ := exists_residue_eq (k₀ := kE φ) (k := 𝓀) (B := ι.range)
    (ρ₁ := redHomInv hc hc0 b₂.1) (ρ₂ := redHom hc b₁.1) hM₂ hM₁ hLD₂ hLD₁ hconst'
    b₂.2.1.V.toSubring (placeRes b₂.2.1) (fun z ↦ red_mem_V hc b₂.1 (rintEquiv hc0 z) b₂.2.2)
    (fun t ↦ b₂.2.1.algebraMap_mem t)
    b₁.2.1.V.toSubring (placeRes b₁.2.1) (fun z ↦ red_mem_V hc b₁.1 z b₁.2.2)
    (fun t ↦ b₁.2.1.algebraMap_mem t) (fun t ↦ CurvePlace.res_algebraMap _ t) hcomp hresB
    (mem_placeSub.1 b.2).2 hb1 (isSpanned_swap (hspan y)) (isSpanned_swap (hspan s)) hsr
    hy₂ hy₁'
  obtain ⟨e, rfl⟩ := residue_surjective t
  exact ⟨e, norm_le_one_of_mem hφ e.2,
    (placeSubRes_phi₁_cstB hc hφ hχ hι e).trans (ht.symm.trans (placeSubRes_apply _).symm)⟩

set_option maxHeartbeats 2000000 in
-- the branch types are elaboration-heavy
include hι hχ hφ in
/-- **The kernel hypothesis**: elements of `B_E` vanishing on both branches are divisible by `ϖ`
up to `t₀ ∉ P'`. -/
lemma descent_ker [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    [FiniteDimensional (RatFunc E) F₀]
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    (heo : ∀ (v : Ext C F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    (hei : ∀ (v : GaussExtension (0 : C) (invRad hc0 1) F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    {ϖ : E} (hϖ0 : ϖ ≠ 0) (hϖle : ∀ e : E, ‖e‖ < 1 → ‖e‖ ≤ ‖ϖ‖) (hϖ1 : ‖ϖ‖ ≤ 1)
    (t₀ : BE F₀ c₀)
    (ht₀o : ∀ v : Ext C F', v ≠ b₁.1 → redHom hc v (ι t₀) = 0)
    (ht₀i : ∀ w : Ext C (Inv (φ c₀) hc0 F'), w ≠ b₂.1 → redHomInv hc hc0 w (ι t₀) = 0)
    (b : BE F₀ c₀) (hb₁ : phi₁ hc b₁ hι b = 0) (hb₂ : phi₂ hc hc0 b₂ hι b = 0) :
    ∃ z : BE F₀ c₀, t₀ * b = cstB ϖ hϖ1 * z := by
  have hc₀0 : c₀ ≠ 0 := by rintro rfl; exact hc0 (map_zero φ)
  have hc₀1 : ‖c₀‖ ≤ 1 := by rw [← hφ]; exact hc.le
  have hb₁' : redHom hc b₁.1 (ι b) = 0 := congrArg Subtype.val hb₁
  have hb₂' : redHomInv hc hc0 b₂.1 (ι b) = 0 := congrArg Subtype.val hb₂
  have hout : ∀ v : Ext C F', v.1 (χ (t₀ * b : BE F₀ c₀)) < 1 := by
    intro v
    rw [← hι, ← redHom_eq_zero_iff hc, map_mul, map_mul]
    by_cases hv : v = b₁.1
    · subst hv; rw [hb₁', mul_zero]
    · rw [ht₀o v hv, zero_mul]
  have hin : ∀ v : GaussExtension (0 : C) (invRad hc0 1) F', v.1 (χ (t₀ * b : BE F₀ c₀)) < 1 := by
    intro v
    rw [← hι, ← redHomInv_toInvExt_eq_zero_iff hc hc0, map_mul, map_mul]
    by_cases hv : toInvExt hc0 v = b₂.1
    · rw [hv, hb₂', mul_zero]
    · rw [ht₀i _ hv, zero_mul]
  obtain ⟨z, hz⟩ := exists_eq_cst_mul hp hp1 hφ hχ hdeg hθ hc₀0 hc₀1 hc0 heo hei hϖ0 hϖle
    hout hin
  exact ⟨z, Subtype.ext (by rw [hz]; rfl)⟩

end Descent

end DVRDescent

end SemistableReduction
