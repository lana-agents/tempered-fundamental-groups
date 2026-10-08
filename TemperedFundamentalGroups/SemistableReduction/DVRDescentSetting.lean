/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeUpward
import TemperedFundamentalGroups.SemistableReduction.DefinedOverDVR

/-!
# The setting of the descent of node points to a discretely valued subfield (O1)

Blueprint §9.12, O1 (S7.9). Let `C` be a non-archimedean field, `F' / C(x)` finite, and
`φ : E → C` an embedding of a field `E` (a complete discretely valued subfield; we keep `E` an
abstract field so that typeclass search stays cheap), with the restricted valuation `vE φ`. Let
`F₀ / E(x)` be a field with `χ : F₀ → F'` compatible with `ratFuncMap φ : E(x) → C(x)`
(`IsCompat`), e.g. `F₀ = E(x)(θ)` for a primitive element `θ` of `F'` whose minimal polynomial
has coefficients in `E(x)`.

* the node chart `nodeRing c = O_E[x, c/x] ⊆ E(x)` (for the norm of `E`) maps into the node chart
  `O_C[x, φ c/x]` (`map_nodeRingE_le`, `φ` isometric);
* `BE F₀ c = integralClosure (nodeRing c) F₀`, the integral closure of the node chart over `O_E`,
  and `ιB : BE → Rint (φ c) F'`, injective (`ιB_injective`).
-/

open NNReal Polynomial

namespace SemistableReduction

namespace DVRDescent

open GaussTube

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] (φ : E →+* C)

/-- The valuation of `E` restricted from `C`. -/
noncomputable abbrev vE : Valuation E ℝ≥0 := (NormedField.valuation (K := C)).comap φ

/-- The restricted valuation is the norm valuation of `E` when `φ` is isometric. -/
lemma vE_eq (hφ : ∀ e, ‖φ e‖ = ‖e‖) : vE φ = NormedField.valuation (K := E) := by
  ext e
  simp only [vE, Valuation.comap_apply, NormedField.valuation_apply]
  congr 1
  exact NNReal.coe_injective (by simpa using hφ e)

variable {φ} in
/-- The node chart over `O_E` maps into the node chart over `O_C` (`φ` isometric; the node chart
over `E` is `nodeRing c` for the norm of `E`). -/
theorem map_nodeRingE_le (hφ : ∀ e, ‖φ e‖ = ‖e‖) (c : E) :
    (nodeRing c).map (ratFuncMap φ) ≤ nodeRing (φ c) := by
  rw [Subring.map_le_iff_le_comap]
  refine Subring.closure_le.2 ?_
  rintro z (hz | hz)
  · obtain ⟨e, he, rfl⟩ := hz
    change ratFuncMap φ (algebraMap E (RatFunc E) e) ∈ nodeRing (φ c)
    rw [ratFuncMap_algebraMap_C]
    refine algebraMap_mem_nodeRing ?_
    have : NormedField.valuation (K := E) e ≤ 1 := he
    have h' : ‖e‖₊ ≤ 1 := by simpa [NormedField.valuation_apply] using this
    rw [hφ]
    exact_mod_cast h'
  · rcases hz with rfl | hz
    · change ratFuncMap φ RatFunc.X ∈ nodeRing (φ c)
      have : ratFuncMap φ RatFunc.X = RatFunc.X := by
        rw [← RatFunc.algebraMap_X, ratFuncMap_algebraMap, Polynomial.map_X, RatFunc.algebraMap_X]
      rw [this]
      exact X_mem_nodeRing _
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      change ratFuncMap φ (algebraMap E (RatFunc E) c / RatFunc.X) ∈ nodeRing (φ c)
      have : ratFuncMap φ RatFunc.X = RatFunc.X := by
        rw [← RatFunc.algebraMap_X, ratFuncMap_algebraMap, Polynomial.map_X, RatFunc.algebraMap_X]
      rw [map_div₀, ratFuncMap_algebraMap_C, this]
      exact div_X_mem_nodeRing _

variable {φ} in
/-- The restriction `O_E[x, c/x] → O_C[x, φ c/x]`. -/
noncomputable def nodeMap (hφ : ∀ e, ‖φ e‖ = ‖e‖) (c : E) : nodeRing c →+* nodeRing (φ c) :=
  ((ratFuncMap φ).comp (nodeRing c).subtype).codRestrict _ fun a ↦
    map_nodeRingE_le hφ c ⟨a, a.2, rfl⟩

@[simp]
lemma coe_nodeMap (hφ : ∀ e, ‖φ e‖ = ‖e‖) (c : E) (a : nodeRing c) :
    (nodeMap hφ c a : RatFunc C) = ratFuncMap φ a :=
  rfl

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] (χ : F₀ →+* F')

/-- `χ : F₀ → F'` is compatible with `ratFuncMap φ : E(x) → C(x)`. -/
def IsCompat : Prop :=
  ∀ f : RatFunc E, χ (algebraMap (RatFunc E) F₀ f) = algebraMap (RatFunc C) F' (ratFuncMap φ f)

variable (F₀) in
/-- The integral closure of the node chart `O_E[x, c/x]` over `O_E` in `F₀`. -/
noncomputable abbrev BE (c : E) : Subalgebra (nodeRing c) F₀ :=
  integralClosure (nodeRing c) F₀

variable {φ χ}

/-- Elements of `BE` map to elements integral over the node chart over `O_C`. -/
theorem isIntegral_map (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ) {c : E} (y : BE F₀ c) :
    IsIntegral (nodeRing (φ c)) (χ y) := by
  obtain ⟨p, hp, hpy⟩ := y.2
  refine ⟨p.map (nodeMap hφ c), hp.map _, ?_⟩
  rw [eval₂_map]
  have : (algebraMap (nodeRing (φ c)) F').comp (nodeMap hφ c) =
      χ.comp (algebraMap (nodeRing c) F₀) := by
    ext a
    change algebraMap (RatFunc C) F' (ratFuncMap φ a) = χ (algebraMap (RatFunc E) F₀ a)
    rw [hχ]
  rw [this, ← hom_eval₂, hpy, map_zero]

variable (χ) in
/-- The map `BE → Rint`. -/
noncomputable def ιB (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ) (c : E) :
    BE F₀ c →+* Rint (φ c) F' where
  toFun y := ⟨χ y, isIntegral_map hφ hχ y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
lemma coe_ιB (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ) (c : E) (y : BE F₀ c) :
    ((ιB χ hφ hχ c y : Rint (φ c) F') : F') = χ y := rfl

lemma ιB_injective (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ) (c : E) :
    Function.Injective (ιB χ hφ hχ c) := by
  intro y z h
  have := congrArg (fun w : Rint (φ c) F' ↦ (w : F')) h
  simp only [coe_ιB] at this
  exact Subtype.ext (χ.injective this)

end DVRDescent

end SemistableReduction
