/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8BLimit
import TemperedFundamentalGroups.SemistableReduction.InvSwap
import TemperedFundamentalGroups.SemistableReduction.NearBoundary

/-!
# The outward germ of annuli at a type-2 point (dual of R4(ii))

Blueprint §9.12 O6.1g. For a centre `a₀` and `z ≠ 0` there is `ρ' > ‖z‖` such that the disc
`D(a₀, |z|)` is exhausting in `ball a₀ ‖d‖` for all `|z| < |d| ≤ ρ'`, in every chart centred at `a₀`
(`S8A.typeTwoGermFor`). Proof: R4(ii) (`GaussTube.belowGerm`) for the field
`G₀ = Inv z (Aff a₀ 1 F)` (coordinate `z / (x - a₀)`: the outward direction at `w_{a₀,|z|}` becomes
the inward direction at the boundary of the unit disc), a rescaling by a unit
(`S8A.Transport.isExhausting_iff_of_rescale`), the identification of `Aff 0 l G₀` with
`Inv c' (Aff a₀ d F)` for `c' d = z / l` (`S8A.Transport.nodeODP_transport_id`) and the inversion
`GaussTube.nodeGood_of_inv`.
-/

open Metric

namespace SemistableReduction

namespace S8A

open GaussTube AffineTwist

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

omit [IsAlgClosed C] in
/-- The two coordinates `z / (l (x - a₀))` and `c' / ((x - a₀) / d)` agree for `c' d = z / l`. -/
lemma aff_inv_aff_eq {a₀ z l d c' : C} (hz : z ≠ 0) (hl : l ≠ 0) (hd : d ≠ 0) (hc' : c' ≠ 0)
    (hrel : c' * d * l = z) (φ : RatFunc C) :
    aff a₀ 1 one_ne_zero (inv hz (aff 0 l hl φ)) = aff a₀ d hd (inv hc' φ) := by
  have h := congrArg (fun χ : RatFunc C →ₐ[C] RatFunc C ↦ χ φ)
    (ratFunc_algHom_ext
      (φ := ((aff a₀ 1 one_ne_zero).toAlgHom.comp (inv hz).toAlgHom).comp (aff 0 l hl).toAlgHom)
      (ψ := (aff a₀ d hd).toAlgHom.comp (inv hc').toAlgHom) ?_)
  · exact h
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, aff_apply, inv_apply, affHom_X, invHom_X]
  rw [gaussCoord_eq, map_zero, sub_zero, map_mul, invHom_X, AlgHom.commutes, map_mul, map_div₀,
    map_div₀, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, affHom_X, affHom_X,
    gaussCoord_eq, gaussCoord_eq]
  have hX : (RatFunc.X : RatFunc C) - algebraMap C (RatFunc C) a₀ ≠ 0 := by
    intro h0
    have := congrArg RatFunc.intDegree (sub_eq_zero.1 h0)
    simp at this
  have hl' : algebraMap C (RatFunc C) l ≠ 0 := by simpa using hl
  have hd' : algebraMap C (RatFunc C) d ≠ 0 := by simpa using hd
  rw [← hrel]
  simp only [map_mul, map_inv₀, map_one, inv_one, one_mul]
  field_simp

omit [CharZero C] in
lemma isExhausting_congr {a c c₁ c₂ : C} (hc : c ≠ 0) (h : c₁ = c₂) (h₁ : ‖c₁‖ < 1)
    (h₁0 : c₁ ≠ 0) (h₂ : ‖c₂‖ < 1) (h₂0 : c₂ ≠ 0) (G : Type*) [Field G] [Algebra (RatFunc C) G]
    [Algebra C G] [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G] :
    IsExhausting a hc h₁ h₁0 G → IsExhausting a hc h₂ h₂0 G := by
  subst h
  exact id

omit [CharZero C] in
/-- `NodeGood` is invariant under isomorphisms over `C(x)`. -/
lemma nodeGood_of_algebraMap_eq {G₁ G₂ : Type*} [Field G₁] [Field G₂] [Algebra (RatFunc C) G₁]
    [Algebra (RatFunc C) G₂] [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
    [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
    [FiniteDimensional (RatFunc C) G₂] (e : G₂ ≃+* G₁)
    (he : ∀ φ, e (algebraMap (RatFunc C) G₂ φ) = algebraMap (RatFunc C) G₁ φ) {c : C}
    (hc : ‖c‖ < 1) (hc0 : c ≠ 0) (h : NodeGood G₂ c hc hc0) : NodeGood G₁ c hc hc0 :=
  Transport.nodeODP_transport_id e he hc hc0 h

include hp hp1 in
/-- **O6.1g: the outward germ of annuli at a type-2 point** (dual of R4(ii)), unconditional. -/
theorem typeTwoGermFor : TypeTwoGermFor C F := by
  intro a₀ z hz
  obtain ⟨e, he0, he1, hgerm⟩ :=
    belowGerm hp hp1 (F' := GaussTube.Inv z hz (Aff a₀ 1 one_ne_zero F)) 0 1 one_ne_zero
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have he' : 0 < ‖e‖ := norm_pos_iff.2 he0
  refine ⟨‖z‖ / ‖e‖, ?_, fun d c' hd hc' hc0' hdc hdρ ↦ ?_⟩
  · change ‖z‖ < ‖z‖ / ‖e‖
    rw [lt_div_iff₀ he']
    nlinarith
  set l := z / (c' * d) with hl_def
  have hcd : ‖c' * d‖ = ‖z‖ := by rw [mul_comm]; exact hdc
  have hl : ‖l‖ = 1 := by rw [norm_div, hcd, div_self hz'.ne']
  have hl0 : l ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hl; exact zero_ne_one hl
  have hrel : c' * d * (1 * l) = z := by
    rw [one_mul, hl_def]; field_simp
  have hcl : ‖c' * l‖ = ‖c'‖ := by rw [norm_mul, hl, mul_one]
  have hlt : ‖c' * l‖ < 1 := hcl ▸ hc'
  have hne : c' * l ≠ 0 := mul_ne_zero hc0' hl0
  have hle : ‖e‖ ≤ ‖c' * l‖ := by
    rw [hcl]
    have hd' : 0 < ‖d‖ := norm_pos_iff.2 hd
    have hc'' : ‖c'‖ = ‖z‖ / ‖d‖ := by
      rw [eq_div_iff hd'.ne', ← norm_mul]; exact hcd
    rw [hc'', le_div_iff₀ hd']
    rw [le_div_iff₀ he'] at hdρ
    linarith [mul_comm ‖d‖ ‖e‖]
  have h1 := hgerm (c' * l) hlt hne hle
  have h2 := (Transport.isExhausting_iff_of_rescale
    (F := GaussTube.Inv z hz (Aff a₀ 1 one_ne_zero F)) (a := 0) one_ne_zero hl hlt hne).1 h1
  have h3 := isExhausting_congr _ (mul_div_cancel_right₀ c' hl0) _ _ hc' hc0'
    (GaussTube.Inv z hz (Aff a₀ 1 one_ne_zero F)) h2
  have h3' : NodeGood (Aff 0 (1 * l) (mul_ne_zero one_ne_zero hl0)
      (GaussTube.Inv z hz (Aff a₀ 1 one_ne_zero F))) c' hc' hc0' := h3
  have h4 : NodeGood (GaussTube.Inv c' hc0' (Aff a₀ d hd F)) c' hc' hc0' := by
    let e : Aff 0 (1 * l) (mul_ne_zero one_ne_zero hl0)
        (GaussTube.Inv z hz (Aff a₀ 1 one_ne_zero F)) ≃+*
          GaussTube.Inv c' hc0' (Aff a₀ d hd F) := RingEquiv.refl F
    refine nodeGood_of_algebraMap_eq e (fun φ ↦ ?_) hc' hc0' h3'
    change algebraMap (RatFunc C) F (aff a₀ 1 one_ne_zero (inv hz (aff 0 (1 * l) _ φ))) =
      algebraMap (RatFunc C) F (aff a₀ d hd (inv hc0' φ))
    rw [aff_inv_aff_eq hz _ hd hc0' hrel]
  exact nodeGood_of_inv hc' hc0' h4

end S8A

end SemistableReduction
