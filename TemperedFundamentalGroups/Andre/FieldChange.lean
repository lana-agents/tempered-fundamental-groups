/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.Functoriality
import TemperedFundamentalGroups.Tempered.FieldChangePure

/-!
# Change of the valued field and Theorem A (Blueprint §11, F8)

Let `(K, O) → (K', O')` be an extension of complete discretely valued fields of characteristic
zero with perfect residue fields, `O'` finite over `O`, and `R'` a smooth `K'`-algebra (of
dimension one, a domain) which is also smooth over `K`. Theorem A over `(K', O')` and over
`(K, O)`, together with the pure field change `temperedPi1FieldEquiv` (F8), identify André's
groups: `andreFieldEquiv : andreGroup O' R' A' ≃ₜ* andreGroup O R' A'`, compatibly with the
restrictions `temperedPi1 → andreGroup` of Theorem A (`andreFieldEquiv_andreRestrict`).
-/

universe u

open CategoryTheory Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [PerfectField (IsLocalRing.ResidueField O)]
  {K' : Type u} [Field K'] [Algebra K K'] [CharZero K'] {O' : ValuationSubring K'}
  [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O']
  [PerfectField (IsLocalRing.ResidueField O')]
  (hO : O'.comap (algebraMap K K') = O) (hfin : (valMap hO).Finite)
  {R' : Type u} [CommRing R'] [IsDomain R'] [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R']
  [Algebra.Smooth K R'] [Algebra.Smooth K' R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K' R']
  [SMulCommClass A' K R'] [Finite A']
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω] [IsAlgClosed Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
  (hp' : ∃ p : ℕ, p.Prime ∧ (p : O') ∈ IsLocalRing.maximalIdeal O')
  (hR : ringKrullDim R' = 1)

/-- **André's groups over `(K', O')` and over `(K, O)` agree** (Theorem A on both sides and the
pure change of the valued field, F8). -/
def andreFieldEquiv :
    andreGroup O' R' A' V hV' ≃ₜ* andreGroup O R' A' V (TempObj.comap_eq hO V hV') :=
  (andreEquiv' V hV' hp' hR).symm.trans
    ((temperedPi1FieldEquiv hO hfin V hV').trans
      (andreEquiv' V (TempObj.comap_eq hO V hV') hp hR))

/-- `andreFieldEquiv` is compatible with the restrictions `temperedPi1 → andreGroup` of
Theorem A and with the field change `temperedPi1FieldMap`. -/
theorem andreFieldEquiv_andreRestrict (γ : temperedPi1 O' R' A' V hV') :
    andreFieldEquiv hO hfin V hV' hp hp' hR (andreRestrict O' R' A' V hV' γ) =
      andreRestrict O R' A' V (TempObj.comap_eq hO V hV')
        (temperedPi1FieldMap hO (OrbMap.id R' A') V hV' γ) := by
  rw [← andreEquiv'_apply V hV' hp' hR, ← andreEquiv'_apply V _ hp hR, andreFieldEquiv,
    ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.symm_apply_apply,
    ContinuousMulEquiv.trans_apply, temperedPi1FieldEquiv_apply]

end

end TemperedFundamentalGroups
