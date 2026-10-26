/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateCuspCovering

/-!
# The cusp special-fibre data of the Tate chart (MR12 S5.6, `CuspSpecial`, `CuspOverOrigin`)

* **`TateCuspCov.cuspSpecial`**: `CuspTower.CuspSpecial (T0 ..) (c0 ..) (h0 ..)` from a tame
  Galois cover: `C0 = B₀/JB₀` (`B₀` the normalisation of `T0`), `cov = covCusp` for
  `B = B₀[1/(1 + h)]`, `ι₀ : B₀/JB₀ → B/JB` the localization map (`NormAway`).
* **`TateCuspCov.cuspOverOrigin`**: the ramified cusp factors of `cuspSpecial` lie over `z = 0`:
  at the cusp `z̄ = 0` in the completion of the special fibre, since `z q₀ ∈ (π)`
  (`TateT0Regular.z0_mul_q0`) and `q₀ ≡ κ (1 + h)` modulo `z` is a unit there; at the other
  points of `h̄ = 0` the indices are `1`.
-/

universe u

open Polynomial IsLocalRing Module TensorProduct

namespace SemistableReduction

namespace TateCuspCov

open TateTwoChart
open AdmissibleLift (J)
open FormalKummer (Cs Rs sIdeal)

noncomputable section

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  [IsAlgClosed k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ π b₄ b₆ t κ ε : O} {m : ℕ}
  (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
  (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
  (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
  [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
  (K : Type u) [Field K] [Algebra (RcT π b₄ t κ) K] [IsFractionRing (RcT π b₄ t κ) K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ e)
  (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (hd : finrank K L ∣ e) [Algebra (RcT π b₄ t κ) L] [IsScalarTower (RcT π b₄ t κ) K L]

/-! ### `z̄ = 0` in the completion at the cusp -/

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] hθ [CharZero O] in
include hker hπ hm hκ in
/-- **`z̄ = 0` in the completion of the special fibre at a point `𝔪 ∋ z`**: `z q₀ ∈ (π)` and `q₀`
is a unit at `𝔪`. -/
theorem algebraMap_z_eq_zero [IsNoetherianRing O] (𝔪 : Ideal (RcT π b₄ t κ)) [𝔪.IsMaximal]
    (hJ : J θ (R := RcT π b₄ t κ) ≤ 𝔪)
    (hz : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ 𝔪) :
    algebraMap (Rs θ (RcT π b₄ t κ)) (AdicCompletion (sIdeal (θ := θ) 𝔪) (Rs θ (RcT π b₄ t κ)))
      (Ideal.Quotient.mk _ (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ))) = 0 := by
  set I₀ := sIdeal (θ := θ) 𝔪
  haveI : I₀.IsMaximal := FormalKummer.isMaximal_sIdeal 𝔪 hJ
  have fg : I₀.FG := IsNoetherian.noetherian I₀
  set 𝔪h := I₀.map (algebraMap (Rs θ (RcT π b₄ t κ)) (AdicCompletion I₀ (Rs θ (RcT π b₄ t κ))))
  haveI : IsAdicComplete 𝔪h (AdicCompletion I₀ (Rs θ (RcT π b₄ t κ))) :=
    AdicCompletion.isAdicComplete_self I₀ fg
  set φ := algebraMap (Rs θ (RcT π b₄ t κ)) (AdicCompletion I₀ (Rs θ (RcT π b₄ t κ)))
  set qb : Rs θ (RcT π b₄ t κ) :=
    Ideal.Quotient.mk _ (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (TateT0Regular.q0 π b₄ t κ))
  have hq : qb ∉ I₀ := by
    rw [Ideal.mem_quotient_iff_mem hJ]
    exact q0_notMem hκ 𝔪 hz
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv ‹_› hq
  have hu : IsUnit (φ qb) := by
    have h1 : IsUnit (φ i * (-1) + 1) := Ideal.mem_jacobson_bot.1
      (IsAdicComplete.le_jacobson_bot 𝔪h (Ideal.mem_map_of_mem _ hi)) (-1)
    have h2 : φ i * (-1) + 1 = φ y * φ qb := by
      rw [← map_mul, show y * qb = 1 - i by rw [← hyi]; ring, map_sub, map_one]
      ring
    rw [h2] at h1
    exact isUnit_of_mul_isUnit_right h1
  have hθϖ : θ ϖ = 0 := RingHom.mem_ker.1 (hker ▸ Ideal.mem_span_singleton_self ϖ)
  have hπJ : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (algebraMap O (T0 π b₄ t κ) π) ∈
      J θ (R := RcT π b₄ t κ) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 (by
      rw [hπ, map_mul, map_pow, hθϖ, zero_pow (by omega), mul_zero]))
  have h0 : Ideal.Quotient.mk (J θ (R := RcT π b₄ t κ))
      (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ)) * qb = 0 := by
    rw [← map_mul, ← map_mul, TateT0Regular.z0_mul_q0, map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ hπJ)
  exact hu.mul_left_eq_zero.1 (by rw [← map_mul, h0, map_zero])

variable (B : Type u) [CommRing B] [Algebra (RcT π b₄ t κ) B] [Algebra B L]
  [IsScalarTower (RcT π b₄ t κ) B L]
  (hunr : ∀ (P : Ideal (RcT π b₄ t κ)) [P.IsMaximal], algebraMap O (RcT π b₄ t κ) ϖ ∈ P →
    ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap (RcT π b₄ t κ) B) < P →
      (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ P →
        (Q.comap (algebraMap (RcT π b₄ t κ) B)).map
            (algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)
            (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))}) →
      Algebra.IsUnramifiedAt (RcT π b₄ t κ) Q)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))))

include hϖ hker hπ hm hε hκ h3 hE hb₆ he hζ hd hunr in
/-- **The ramified cusp factors of `covCusp` lie over `z = 0`**: `z̄ εᵢ = 0` in `R̂` if the index
of the factor `i` is not `1`. -/
theorem covCusp_z_mul_cidem [IsIntegralClosure B (RcT π b₄ t κ) L]
    (i : (covCusp hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀).κ)
    (hi : (covCusp hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀).ce i ≠ 1) :
    algebraMap (Rs θ (RcT π b₄ t κ)) (Admissible.Hat (AdmissibleLift.fbar θ
        (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))))
        (Ideal.Quotient.mk _ (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ))) *
      (covCusp hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀).cidem i = 0 := by
  haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j)
  obtain ⟨j, i⟩ := i
  have hdvd : (covCusp hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀).ce ⟨j, i⟩ ∣
      eP π b₄ t κ e (mC θ π b₄ t κ j) :=
    (pointCuspData hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr (mC θ π b₄ t κ j)
      (J_le_mC θ π b₄ t κ j) (sC_mem_mC θ π b₄ t κ j)).hde i
  have hz : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ mC θ π b₄ t κ j := by
    by_contra hz
    rw [eP_of_notMem hz, Nat.dvd_one] at hdvd
    exact hi hdvd
  change _ * CompletionProd.idem (injective_mC θ π b₄ t κ) (sbar_mem_mC θ π b₄ t κ)
    (iInf_mC_le θ π b₄ t κ) j = 0
  apply (CompletionProd.equiv (injective_mC θ π b₄ t κ) (sbar_mem_mC θ π b₄ t κ)
    (iInf_mC_le θ π b₄ t κ)).injective
  rw [map_mul, map_zero, CompletionProd.equiv_algebraMap, CompletionProd.equiv_idem]
  funext j'
  rw [Pi.mul_apply, Pi.zero_apply]
  by_cases hj : j' = j
  · subst hj
    rw [Pi.single_eq_same, mul_one]
    exact algebraMap_z_eq_zero hker hπ hm hκ _ (J_le_mC θ π b₄ t κ j') hz
  · rw [Pi.single_eq_of_ne hj, mul_zero]

/-! ### The cusp special-fibre data -/

variable [Algebra (T0 π b₄ t κ) L] [IsScalarTower (T0 π b₄ t κ) (RcT π b₄ t κ) L]
  (B₀ : Type u) [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L]
  [IsScalarTower (T0 π b₄ t κ) B₀ L] [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
  [Algebra B₀ B] [IsScalarTower B₀ B L]
  [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
  (hB : ∀ x, algebraMap (RcT π b₄ t κ) B (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) x) =
    algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x))

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] hθ [CharZero O] [NeZero e]
  [IsGalois K L] [FiniteDimensional K L] [Algebra (RcT π b₄ t κ) B]
  [IsScalarTower (RcT π b₄ t κ) B L] in
include B₀ in
/-- `B = B₀[1/(1 + h)]` is the normalisation of `Rc` in `L`. -/
lemma isIntegralClosure_B [Algebra (RcT π b₄ t κ) B] [IsScalarTower (RcT π b₄ t κ) B L] :
    IsIntegralClosure B (RcT π b₄ t κ) L := by
  refine NormAway.isIntegralClosure (B₁ := B₀) (TateGlue0.c0 π b₄ t κ) ?_
  rw [IsScalarTower.algebraMap_apply (T0 π b₄ t κ) (RcT π b₄ t κ) L]
  exact ((IsLocalization.Away.algebraMap_isUnit (TateGlue0.c0 π b₄ t κ)).map _).ne_zero

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] hθ [CharZero O] in
lemma J_Rc_eq : J θ (R := RcT π b₄ t κ) =
    (J θ (R := T0 π b₄ t κ)).map (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ)) := by
  change (RingHom.ker θ).map _ = ((RingHom.ker θ).map _).map _
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The `T0`-algebra structure on `B` (through `B₀`). -/
abbrev algTB : Algebra (T0 π b₄ t κ) B :=
  ((algebraMap B₀ B).comp (algebraMap (T0 π b₄ t κ) B₀)).toAlgebra

/-- **The special-fibre data over the cusp chart** (`CuspTower.CuspSpecial`) of a tame cover:
`C0 = B₀/JB₀`, the covering `covCusp` of the special fibre of `Rc` defined by `B = B₀[1/(1 + h)]`,
and the localization map `ι₀ : B₀/JB₀ → B/JB`. -/
def cuspSpecial :
    CuspTower.CuspSpecial (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ) :=
  haveI := isIntegralClosure_B (π := π) (b₄ := b₄) (t := t) (κ := κ) L B B₀
  letI := algTB (π := π) (b₄ := b₄) (t := t) (κ := κ) B B₀
  haveI : IsScalarTower (T0 π b₄ t κ) (RcT π b₄ t κ) B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hB x).symm
  haveI : IsScalarTower (T0 π b₄ t κ) B₀ B := IsScalarTower.of_algebraMap_eq' rfl
  { C0 := Cs θ (T0 π b₄ t κ) B₀
    φ₀ := φ₀
    cov := covCusp hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀
    noNodes := inferInstanceAs (IsEmpty Empty)
    ι₀ := NormAway.quotMap (B₁ := B₀) (B := B) (J θ (R := T0 π b₄ t κ))
      (J θ (R := RcT π b₄ t κ)) J_Rc_eq
    hι₀ := fun x ↦ NormAway.quotMap_algebraMap (B₁ := B₀) (B := B) (J θ (R := T0 π b₄ t κ))
      (J θ (R := RcT π b₄ t κ)) J_Rc_eq x
    hι := NormAway.isLocalization_quotMap (B₁ := B₀) (B := B) (J θ (R := T0 π b₄ t κ))
      (J θ (R := RcT π b₄ t κ)) J_Rc_eq (TateGlue0.c0 π b₄ t κ) }

/-- **The ramified cusp factors of `cuspSpecial` lie over the cusp `z = 0`**
(`TateGlue0.CuspOverOrigin`). -/
theorem cuspOverOrigin : TateGlue0.CuspOverOrigin
    (cuspSpecial hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB) := by
  haveI := isIntegralClosure_B (π := π) (b₄ := b₄) (t := t) (κ := κ) L B B₀
  intro i hi
  have hi' : (covCusp hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀).ce i ≠ 1 := hi
  have h := covCusp_z_mul_cidem hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ _ hi'
  refine ⟨0, ?_⟩
  rw [mul_zero]
  exact h

end

end TateCuspCov

end SemistableReduction
