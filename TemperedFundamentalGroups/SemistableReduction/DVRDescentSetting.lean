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

* `nodeRingE φ c = O_E[x, c/x] ⊆ E(x)`, mapped into the node chart `O_C[x, φ c/x]`
  (`map_nodeRingE_le`);
* `BE φ c F₀ = integralClosure (nodeRingE φ c) F₀`, the integral closure of the node chart over
  `O_E`, and `ιB : BE → Rint (φ c) F'`, injective (`ιB_injective`).
-/

open NNReal Polynomial

namespace SemistableReduction

namespace DVRDescent

open GaussTube

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type*} [Field E] (φ : E →+* C)

/-- The valuation of `E` restricted from `C`. -/
noncomputable abbrev vE : Valuation E ℝ≥0 := (NormedField.valuation (K := C)).comap φ

/-- The node chart `O_E[x, c/x] ⊆ E(x)`. -/
noncomputable abbrev nodeRingE (c : E) : Subring (RatFunc E) := nodeChart (vE φ) RatFunc.X c

/-- The node chart over `O_E` maps into the node chart over `O_C`. -/
theorem map_nodeRingE_le (c : E) : (nodeRingE φ c).map (ratFuncMap φ) ≤ nodeRing (φ c) := by
  rw [Subring.map_le_iff_le_comap]
  refine Subring.closure_le.2 ?_
  rintro z (hz | hz)
  · obtain ⟨e, he, rfl⟩ := hz
    change ratFuncMap φ (algebraMap E (RatFunc E) e) ∈ nodeRing (φ c)
    rw [ratFuncMap_algebraMap_C]
    refine algebraMap_mem_nodeRing ?_
    have : vE φ e ≤ 1 := he
    have h' : ‖φ e‖₊ ≤ 1 := by simpa [vE, NormedField.valuation_apply] using this
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

/-- The restriction `O_E[x, c/x] → O_C[x, φ c/x]`. -/
noncomputable def nodeMap (c : E) : nodeRingE φ c →+* nodeRing (φ c) :=
  ((ratFuncMap φ).comp (nodeRingE φ c).subtype).codRestrict _ fun a ↦
    map_nodeRingE_le φ c ⟨a, a.2, rfl⟩

@[simp]
lemma coe_nodeMap (c : E) (a : nodeRingE φ c) : (nodeMap φ c a : RatFunc C) = ratFuncMap φ a :=
  rfl

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] (χ : F₀ →+* F')

/-- `χ : F₀ → F'` is compatible with `ratFuncMap φ : E(x) → C(x)`. -/
def IsCompat : Prop :=
  ∀ f : RatFunc E, χ (algebraMap (RatFunc E) F₀ f) = algebraMap (RatFunc C) F' (ratFuncMap φ f)

variable (F₀) in
/-- The integral closure of the node chart over `O_E` in `F₀`. -/
noncomputable abbrev BE (c : E) : Subalgebra (nodeRingE φ c) F₀ :=
  integralClosure (nodeRingE φ c) F₀

variable {φ χ}

/-- Elements of `BE` map to elements integral over the node chart over `O_C`. -/
theorem isIntegral_map (hχ : IsCompat φ χ) {c : E} (y : BE φ F₀ c) :
    IsIntegral (nodeRing (φ c)) (χ y) := by
  obtain ⟨p, hp, hpy⟩ := y.2
  refine ⟨p.map (nodeMap φ c), hp.map _, ?_⟩
  rw [eval₂_map]
  have : (algebraMap (nodeRing (φ c)) F').comp (nodeMap φ c) =
      χ.comp (algebraMap (nodeRingE φ c) F₀) := by
    ext a
    change algebraMap (RatFunc C) F' (ratFuncMap φ a) = χ (algebraMap (RatFunc E) F₀ a)
    rw [hχ]
  rw [this, ← hom_eval₂, hpy, map_zero]

variable (φ χ) in
/-- The map `BE → Rint`. -/
noncomputable def ιB (hχ : IsCompat φ χ) (c : E) : BE φ F₀ c →+* Rint (φ c) F' where
  toFun y := ⟨χ y, isIntegral_map hχ y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
lemma coe_ιB (hχ : IsCompat φ χ) (c : E) (y : BE φ F₀ c) :
    ((ιB φ χ hχ c y : Rint (φ c) F') : F') = χ y := rfl

lemma ιB_injective (hχ : IsCompat φ χ) (c : E) : Function.Injective (ιB φ χ hχ c) := by
  intro y z h
  have := congrArg (fun w : Rint (φ c) F' ↦ (w : F')) h
  simp only [coe_ιB] at this
  exact Subtype.ext (χ.injective this)

end DVRDescent

end SemistableReduction
