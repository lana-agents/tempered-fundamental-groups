/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentSetting

/-!
# The integral closure of the node chart over a DVR is noetherian and normal (O1, step (A))

Blueprint §9.12, O1. For a non-archimedean field `E` whose ring of integers is noetherian (a DVR)
and `c ∈ E` with `0 < ‖c‖ ≤ 1`:

* `isNoetherianRing_nodeRing`: the node chart `O_E[x, c/x]` is noetherian (the image of the node
  `O_E[u, v] ⧸ (u v - c)`);
* for `F₀ / E(x)` finite separable, `BE F₀ c` (the integral closure of the node chart in `F₀`) is
  noetherian (`isNoetherianRing_BE`) and integrally closed (`isIntegrallyClosed_BE`), and so are
  its localizations.
-/

open NNReal Polynomial

namespace SemistableReduction

namespace GaussTube

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

/-- The node chart over a field with noetherian integers is noetherian. -/
theorem isNoetherianRing_nodeRing [IsNoetherianRing (HenselComplete.integers C)] {c : C}
    (hc1 : ‖c‖ ≤ 1) : IsNoetherianRing (nodeRing c) := by
  have hcO : NormedField.valuation (K := C) c ≤ 1 := by
    rw [NormedField.valuation_apply]; exact_mod_cast hc1
  set f := ZariskiModel.nodeLift (v := NormedField.valuation (K := C))
    (y := (RatFunc.X : RatFunc C)) RatFunc.X_ne_zero hcO
  have h := ZariskiModel.range_nodeLift (v := NormedField.valuation (K := C))
    (y := (RatFunc.X : RatFunc C)) RatFunc.X_ne_zero hcO
  haveI := isNoetherianRing_range f.toRingHom
  have e : f.toRingHom.range = nodeRing c := by
    rw [nodeRing, ← h]; rfl
  exact isNoetherianRing_of_ringEquiv _ (RingEquiv.subringCongr e)

end GaussTube

namespace DVRDescent

open GaussTube

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  (F₀ : Type*) [Field F₀] [Algebra (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  [Algebra.IsSeparable (RatFunc E) F₀]

/-- `BE` is noetherian. -/
theorem isNoetherianRing_BE [IsNoetherianRing (HenselComplete.integers E)] {c : E} (hc0 : c ≠ 0)
    (hc1 : ‖c‖ ≤ 1) : IsNoetherianRing (BE F₀ c) := by
  haveI := isNoetherianRing_nodeRing hc1
  haveI := isIntegrallyClosed_nodeRing hc0 hc1
  haveI := isFractionRing_nodeRing c
  exact IsIntegralClosure.isNoetherianRing (nodeRing c) (RatFunc E) F₀ (BE F₀ c)

omit [Algebra.IsSeparable (RatFunc E) F₀] in
/-- `BE` is integrally closed. -/
theorem isIntegrallyClosed_BE (c : E) : IsIntegrallyClosed (BE F₀ c) := by
  haveI := isFractionRing_nodeRing c
  exact integralClosure.isIntegrallyClosedOfFiniteExtension (RatFunc E)

end DVRDescent

end SemistableReduction
