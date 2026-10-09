/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothTwist

/-!
# Smooth points over arbitrary residue points (W10, smooth part (2), (4))

Blueprint §9.12 (O7). For `κ_E` perfect, the residue values of a point (finitely many, algebraic
over `κ_E`) become residues of the integers of an unramified extension `E' ⊆ C`.

* `Unramified.exists_root_residue`: a monic `g ∈ O_E[X]` whose reduction has a root `α ∈ 𝓀` has a
  root `β ∈ O_C` with residue `α`;
* `Unramified.exists_unrData`: finitely many elements of `𝓀` algebraic over `κ_E` are residues of
  integers of some unramified `E' = E[X] ⧸ (g)` inside `C` (primitive element of the residue
  extension, `κ_E` perfect).
-/

open Polynomial IsLocalRing

set_option linter.unusedSectionVars false

namespace SemistableReduction

namespace Unramified

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {φ : E →+* C} (hφ : ∀ e, ‖φ e‖ = ‖e‖)

local notation "O_E" => HenselComplete.integers E
local notation "O_C" => HenselComplete.integers C
local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "kv" => ResidueField (HenselComplete.integers E)

include hφ in
/-- A monic `g ∈ O_E[X]` whose reduction has a root `α ∈ 𝓀` has a root `β ∈ O_C` with residue
`α`. -/
theorem exists_root_residue {g : O_E[X]} (hg : g.Monic) {α : 𝓀}
    (hα : ((g.map (residue O_E)).map (DVRDescent.ψ hφ)).eval α = 0) :
    ∃ β : C, g.eval₂ (φ.comp (O_E).subtype) β = 0 ∧ ∃ hβ : β ∈ O_C, residue O_C ⟨β, hβ⟩ = α := by
  classical
  set ι := DVRDescent.intMap hφ
  set G' : O_C[X] := g.map ι
  have hG'm : G'.Monic := hg.map _
  set Gc : C[X] := G'.map (O_C).subtype
  have hGc : Gc = g.map (φ.comp (O_E).subtype) := by
    change (g.map ι).map (O_C).subtype = _
    rw [Polynomial.map_map]; rfl
  have hsplit : Gc = (Gc.roots.map (fun r ↦ X - Polynomial.C r)).prod :=
    (IsAlgClosed.splits Gc).eq_prod_roots_of_monic (hG'm.map _)
  -- the roots are integral
  have hint : ∀ r ∈ Gc.roots, r ∈ O_C := by
    intro r hr
    have hroot : G'.eval₂ (O_C).subtype r = 0 := by
      rw [← eval_map]; exact (mem_roots (hG'm.map _).ne_zero).1 hr
    exact (Valuation.valuationSubring.integers (NormedField.valuation (K := C))).mem_of_integral
      ⟨G', hG'm, hroot⟩
  set Gp : O_C[X] :=
    (Gc.roots.attach.map (fun r ↦ X - Polynomial.C (⟨r.1, hint r.1 r.2⟩ : O_C))).prod
  have hGp : G' = Gp := by
    apply Polynomial.map_injective _ (O_C).subtype_injective
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    conv_lhs => rw [show G'.map (O_C).subtype = Gc from rfl, hsplit]
    congr 1
    conv_lhs => rw [← Multiset.attach_map_val Gc.roots, Multiset.map_map]
    refine Multiset.map_congr rfl fun r _ ↦ ?_
    simp
  have hred : G'.map (residue O_C) = (g.map (residue O_E)).map (DVRDescent.ψ hφ) := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
  rw [← hred, hGp, Polynomial.map_multiset_prod, eval_multiset_prod, Multiset.prod_eq_zero_iff,
    Multiset.map_map, Multiset.map_map] at hα
  obtain ⟨r, -, hr⟩ := Multiset.mem_map.1 hα
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    eval_sub, eval_X, eval_C, sub_eq_zero] at hr
  obtain ⟨r, hr'⟩ := r
  refine ⟨r, ?_, hint r hr', hr.symm⟩
  have := (mem_roots (hG'm.map (O_C).subtype).ne_zero).1 hr'
  rw [IsRoot, show G'.map (O_C).subtype = Gc from rfl, hGc, eval_map] at this
  exact this

/-- `Q(root)` as an integer of `E'`. -/
noncomputable def UnrData.aevalRI (D : UnrData φ) (Q : O_E[X]) : HenselComplete.integers D.F :=
  aeval D.rI Q

/-- Residues of integers of `E'`: `res(Q(root)) = Q̄(β̄)`. -/
lemma UnrData.residue_aeval_rI (D : UnrData φ) (Q : O_E[X]) :
    residue O_C (DVRDescent.intMap (φ := D.φ') D.norm_φ' (D.aevalRI Q)) =
      aeval (residue O_C D.b) ((Q.map (residue O_E)).map D.ψ) := by
  have : DVRDescent.intMap (φ := D.φ') D.norm_φ' (D.aevalRI Q) = aeval D.b (Q.map D.ιO) :=
    Subtype.ext (by
      change D.φ' ((aeval D.rI Q : HenselComplete.integers D.F) : D.F) = _
      rw [UnrData.coe_aeval_rI, UnrData.coe_aeval_b, aeval_def, hom_eval₂, eval₂_map]
      congr 1
      · ext a
        exact D.φ'_algebraMap a
      · exact D.φ'_r)
  rw [this, UnrData.residue_aeval_b]

variable [IsDiscreteValuationRing (HenselComplete.integers E)]

include hφ in
/-- **Unramified extensions making finitely many residues rational.** For `κ_E` perfect and
finitely many `z ∈ 𝓀` algebraic over `κ_E`, there is an unramified `E' = E[X] ⧸ (g)` inside `C`
whose integers have all `z` among their residues. -/
theorem exists_unrData [PerfectField kv] (Z : Finset 𝓀)
    (hZ : ∀ z ∈ Z, letI := (DVRDescent.ψ hφ).toAlgebra; IsAlgebraic kv z) :
    ∃ D : UnrData φ, ∀ z ∈ Z, ∃ e' : HenselComplete.integers D.F,
      residue O_C (DVRDescent.intMap (φ := D.φ') D.norm_φ' e') = z := by
  classical
  letI := (DVRDescent.ψ hφ).toAlgebra
  set L := IntermediateField.adjoin kv (Z : Set 𝓀)
  haveI : FiniteDimensional kv L := IntermediateField.finiteDimensional_adjoin fun z hz ↦
    (hZ z hz).isIntegral
  haveI : Algebra.IsAlgebraic kv L := inferInstance
  obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element kv L
  set α : 𝓀 := (α₀ : 𝓀)
  have hαint : IsIntegral kv α :=
    (Algebra.IsIntegral.isIntegral α₀).map (IsScalarTower.toAlgHom kv L 𝓀)
  set gb := minpoly kv α
  have hgbm : gb.Monic := minpoly.monic hαint
  have hgbirr : Irreducible gb := minpoly.irreducible hαint
  have hgbsep : gb.Separable := by
    have h := Algebra.IsSeparable.isSeparable kv α₀
    rw [IsSeparable, ← minpoly.algebraMap_eq (algebraMap L 𝓀).injective] at h
    exact h
  -- lift to `O_E`
  have hlifts : gb ∈ lifts (residue O_E) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n ↦ residue_surjective _
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic hlifts hgbm
  obtain ⟨a, b, hab⟩ := (separable_def' gb).1 hgbsep
  obtain ⟨A, hA⟩ := map_surjective (residue O_E) residue_surjective a
  obtain ⟨B, hB⟩ := map_surjective (residue O_E) residue_surjective b
  have hres : (derivative g * B + g * A).map (residue O_E) = 1 := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, hg, hA, hB,
      ← hab]
    ring
  -- the root
  obtain ⟨β, hβ, hβC, hβres⟩ := exists_root_residue hφ hgm (α := α) (by
    rw [hg, eval_map]
    have := minpoly.aeval kv α
    rwa [aeval_def] at this)
  let D : UnrData φ := ⟨hφ, g, hgm, by rw [hg]; exact hgbirr, B, A, hres, β, hβ⟩
  refine ⟨D, fun z hz ↦ ?_⟩
  -- `z ∈ κ_E[α]`
  obtain ⟨q, hq⟩ : ∃ q : kv[X], aeval α q = z := by
    have h1 : (⟨z, IntermediateField.subset_adjoin _ _ hz⟩ : L) ∈
        (IntermediateField.adjoin kv {α₀}).toSubalgebra := by rw [hα₀]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α₀), Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨q, hq⟩ := h1
    refine ⟨q, ?_⟩
    have := congrArg (fun w : L ↦ (w : 𝓀)) hq
    simp only at this
    rw [← this]
    change aeval α q = ((aeval α₀ q : L) : 𝓀)
    have h2 := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom kv L 𝓀) α₀ q
    exact h2
  subst hq
  obtain ⟨Q, hQ⟩ := map_surjective (residue O_E) residue_surjective q
  refine ⟨D.aevalRI Q, ?_⟩
  rw [D.residue_aeval_rI Q, hQ]
  have hb : residue O_C D.b = α := hβres
  rw [hb]
  exact aeval_map_algebraMap 𝓀 α q

end Unramified

end SemistableReduction
