/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.OffSkeletonBase
import TemperedFundamentalGroups.SemistableReduction.DiscBridge

/-!
# (T⇒), off-skeleton clause

Blueprint §9.12, O11 (T⇒), off-skeleton clause, via lemma (L). Let the annulus `|c'| < |t| < 1`
(`t = (x - a)/c`) be exhausting, with exact node data at its node points (`NodeDataOfODP`), and
`|c'| < |β| < 1`. Every point over the residue disc `|x - (a + cβ)| < |cβ|` of the skeleton point
`w_{a,|cβ|}` is smooth (`ExhaustGluing.discSmooth_of_exhausting`): at a branch `(v, R)` through
it, the node coordinate `u` at the centre of `v` on the node chart gives `κ(v) = k(ū)`,
`t̄/β = λ ūᵈ` (`vertex_data`), and the elements `Y₂ = (t/β)ᵐ hᴺ`, `Y₁ = Y₂ σ_u u/π` (`h`
separating the node point from the others, `πᵈ = β`) lie in the disc chart
(`exists_coord_data`); `OffSkeleton.isDiscSmooth_of_coord` applies. Then (D⇒)
(`isTubeDisc_of_discSmooth`) gives **`ExhaustGluing.offSkeletonOfExhausting`**:
`NodeDataOfODP C F' → OffSkeletonOfExhausting C F'`.
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace OffSkeleton

open PlaceNorm CurvePlace

section Core

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ]

/-- If `x = λ uᵈ` is transcendental and `[κ : k(x)] ≤ d`, then `κ = k(u)` and `[κ : k(x)] = d`. -/
theorem adjoin_eq_top_of_eq_smul_pow {x u : κ} {lam : k} (hlam : lam ≠ 0) {d : ℕ} (hd : 1 ≤ d)
    (hx : x = algebraMap k κ lam * u ^ d) (hxr : x ∉ (algebraMap k κ).range)
    (hf : Module.finrank k⟮x⟯ κ ≤ d) :
    k⟮u⟯ = ⊤ ∧ Module.finrank k⟮x⟯ κ = d := by
  have hur : u ∉ (algebraMap k κ).range := by
    rintro ⟨b, rfl⟩
    exact hxr ⟨lam * b ^ d, by rw [hx, map_mul, map_pow]⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hur ⟨0, map_zero _⟩
  obtain ⟨hz, hord⟩ := TubeSkeleton.zeros_eq_of_eq_smul_pow hu0 hlam hd hx
  have hsum := sum_ord hxr
  rw [Finset.sum_congr hz fun Q hQ ↦ hord Q hQ, ← Finset.mul_sum, sum_ord hur] at hsum
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_of_notMem_range hur)
  have hpos : 0 < Module.finrank k⟮u⟯ κ := Module.finrank_pos
  have h1 : Module.finrank k⟮u⟯ κ = 1 := by
    have : d * Module.finrank k⟮u⟯ κ ≤ d * 1 := by rw [hsum, mul_one]; exact hf
    have := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  refine ⟨IntermediateField.finrank_eq_one_iff_eq_top.1 h1, ?_⟩
  rw [← hsum, h1, mul_one]

end Core

end OffSkeleton
namespace OffSkeleton

open GaussFibre

section Residue

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {H : Type*} [Field H] [Algebra (RatFunc C) H] [Algebra C H]
  [IsScalarTower C (RatFunc C) H] [FiniteDimensional (RatFunc C) H]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

lemma adjoin_add_one {k κ : Type*} [Field k] [Field κ] [Algebra k κ] (y : κ) :
    k⟮y + 1⟯ = k⟮y⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact add_mem (IntermediateField.mem_adjoin_simple_self k y) (one_mem _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h := sub_mem (IntermediateField.mem_adjoin_simple_self k (y + 1)) (one_mem k⟮y + 1⟯)
    rwa [add_sub_cancel_right] at h

/-- **The residue curve at a vertex with a node coordinate**: `x + 1 ≡ λ Uᵈ` with `|λ| = |U| = 1`
and `[κ(v) : k(x̄)] ≤ d` give `κ(v) = k(Ū)`, `x̄ + 1 = λ̄ Ūᵈ` and `[κ(v) : k(x̄)] = d`. -/
lemma residue_of_node_coord (v : Ext C H) {U : H} (hU : v.1 U = 1) {lam : C}
    (hlam : ‖lam‖₊ = 1) {d : ℕ} (hd : 1 ≤ d)
    (hdiff : v.1 (xF C H + 1 - algebraMap C H lam * U ^ d) < 1)
    (hf : Module.finrank 𝓀⟮red C (xF C H) v⟯ (ResidueField v.1.valuationSubring) ≤ d) :
    ∃ lamR : 𝓀, lamR ≠ 0 ∧
      red C (xF C H) v + 1 = algebraMap 𝓀 _ lamR * red C U v ^ d ∧ 𝓀⟮red C U v⟯ = ⊤ ∧
        Module.finrank 𝓀⟮red C (xF C H) v⟯ (ResidueField v.1.valuationSubring) = d := by
  have hlamC : ‖lam‖₊ ≤ 1 := hlam.le
  set lamR : 𝓀 := IsLocalRing.residue (HenselComplete.integers C)
    ⟨lam, by simpa using (HenselComplete.mem_integers_iff lam).2 (by exact_mod_cast hlamC)⟩
  have hlamR : lamR ≠ 0 := by
    rw [Ne, GaussTube.residue_eq_zero_iff_norm, not_lt]
    change 1 ≤ ‖lam‖
    rw [← coe_nnnorm, hlam, NNReal.coe_one]
  have hUd : v.1 (algebraMap C H lam * U ^ d) ≤ 1 := by
    rw [map_mul, map_pow, hU, one_pow, mul_one, valuation_algebraMap_C']
    exact hlamC
  have hx1 : v.1 (xF C H + 1) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le (valuation_xF v).le (by rw [map_one]))
  have hred : red C (xF C H) v + 1 = algebraMap 𝓀 _ lamR * red C U v ^ d := by
    have h0 := (red_eq_zero_iff ((Valuation.map_sub _ _ _).trans (max_le hx1 hUd))).2 hdiff
    rw [red_sub hx1 hUd, sub_eq_zero, red_add (valuation_xF v).le (by rw [map_one]), red_one] at h0
    rw [h0, red_mul (by rw [valuation_algebraMap_C']; exact hlamC)
      (by rw [map_pow, hU, one_pow]), red_algebraMap_C lam hlamC, red_pow hU.le]
  have hxr : red C (xF C H) v + 1 ∉ (algebraMap 𝓀 (ResidueField v.1.valuationSubring)).range := by
    rintro ⟨b, hb⟩
    refine transcendental_red_x (F := H) v ?_
    have : red C (xF C H) v = algebraMap 𝓀 _ (b - 1) := by rw [map_sub, hb, map_one,
      add_sub_cancel_right]
    rw [this]
    exact isAlgebraic_algebraMap _
  obtain ⟨htop, hfd⟩ := adjoin_eq_top_of_eq_smul_pow hlamR hd hred hxr
    (by rw [adjoin_add_one]; exact hf)
  rw [adjoin_add_one] at hfd
  exact ⟨lamR, hlamR, hred, htop, hfd⟩

end Residue

end OffSkeleton

namespace ExhaustGluing

open GaussTube GaussFibre GaussStability AffineTwist PlaceNorm DiscCount SmoothVertex
  TubeSkeleton OffSkeleton

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma hle_aux {a c β : C} : ‖(a + c * β) - a‖ ≤ ‖c * β‖ := by
  rw [add_sub_cancel_left]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma isIntegral_of_mem_adjoin {A : Type*} [CommRing A] [Algebra C A] {s : Set A} {y : A}
    (hy : y ∈ Algebra.adjoin C s) : IsIntegral (Algebra.adjoin C s) y :=
  isIntegral_algebraMap (x := (⟨y, hy⟩ : Algebra.adjoin C s))

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- `C[x]` maps into `C[x']` under the identity between the twists `(a, c)` and `(a + cβ, cβ)`. -/
lemma affId_mem_adjoin {a c β : C} (hc : c ≠ 0) (hβ0 : β ≠ 0) {y : Aff a c hc F'}
    (hy : y ∈ Algebra.adjoin C {xF C (Aff a c hc F')}) :
    affId (F' := F') (a := a) (a' := a + c * β) hc (mul_ne_zero hc hβ0) y ∈
      Algebra.adjoin C {xF C (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F')} := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.1 hy, affId_xF (F' := F') (a := a) (β := β) (γ := β) hc hβ0]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _)
      (Algebra.self_mem_adjoin_singleton C _))
      (Subalgebra.algebraMap_mem _ _)
  | algebraMap b => exact Subalgebra.algebraMap_mem _ b
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
include hp hp1

set_option maxHeartbeats 800000 in
-- the long proof manipulates several affine twists of `F'` (elaboration of the type synonyms)
/-- **Local coordinate data at a vertex of an exhausting annulus.** Let `|c'| < |t| < 1`
(`t = (x - a)/c`) be exhausting with exact node data, `|c'| < |β| < 1`, and `v` an extension of the
Gauss point `w_{a + cβ,|cβ|} = w_{a,|cβ|}` (on the twist by `(a + cβ, cβ)`, coordinate
`t' = t/β - 1`). Then `κ(v) = k(ū)` with `t̄' + 1 = λ ūᵈ`, and there are `Y₁, Y₂` in the disc
chart with `Ȳ₂ = (t̄' + 1)ᵐ`, `Ȳ₁ = μ Ȳ₂ ū` at `v` and `Ȳ₂ = 0` at every other extension. -/
theorem vertex_data (hND : NodeDataOfODP C F') {a c c' : C} (hc : c ≠ 0) (hc' : ‖c'‖ < 1)
    (hc0' : c' ≠ 0) (hex : IsExhausting a hc hc' hc0' F') {β : C} (hβ0 : β ≠ 0)
    (h1 : ‖c'‖ < ‖β‖) (h2 : ‖β‖ < 1) (v : Ext C (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F')) :
    ∃ (U : Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F') (d : ℕ) (lam : 𝓀), 1 ≤ d ∧
      𝓀⟮red C U v⟯ = ⊤ ∧
      red C (xF C (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F')) v + 1 =
        algebraMap 𝓀 _ lam * red C U v ^ d ∧
      ∃ (uR q : Rint c' (Aff a c hc F')) (π : C) (mu : 𝓀), π ≠ 0 ∧ mu ≠ 0 ∧
        (extTrans hc hβ0 (hle_aux) v).1 (uR : Aff a c hc F') = ‖π‖₊ ∧
        red C (affId (F' := F') (a := a) (a' := a + c * β) hc (mul_ne_zero hc hβ0)
          ((uR : Aff a c hc F') * (algebraMap C (Aff a c hc F') π)⁻¹)) v =
            algebraMap 𝓀 _ mu * red C U v ∧
        (extTrans hc hβ0 (hle_aux) v).1 ((q : Aff a c hc F') - 1) < 1 ∧
        ∀ W' : GaussExtension (0 : C) (Units.mk0 ‖β‖₊ (nnnorm_ne_zero_iff.2 hβ0)) (Aff a c hc F'),
          W' ≠ extTrans hc hβ0 (hle_aux) v → W'.1 (q : Aff a c hc F') < ‖π‖₊ := by
  classical
  set G := Aff a c hc F'
  have hcβ : c * β ≠ 0 := mul_ne_zero hc hβ0
  set H := Aff (a + c * β) (c * β) hcβ F'
  haveI : Algebra.IsSeparable (RatFunc C) G := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Finite (Ext C G) := finite_ext (F := G) hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  have hle : ‖(a + c * β) - a‖ ≤ ‖c * β‖ := hle_aux
  let W := extTrans hc hβ0 hle v
  let sβ : ℝ≥0ˣ := Units.mk0 ‖β‖₊ (nnnorm_ne_zero_iff.2 hβ0)
  haveI : Finite (GaussExtension (0 : C) sβ G) := finite_gaussExtension (F' := G) 0 sβ
  letI : Fintype (GaussExtension (0 : C) sβ G) := Fintype.ofFinite _
  have hs : sβ ∈ segment c' :=
    ⟨show ‖c'‖₊ < ‖β‖₊ by exact_mod_cast h1, show ‖β‖₊ < 1 by exact_mod_cast h2⟩
  -- the centre of `W` and its exact node data
  let P' := center hs W
  haveI hPmax : P'.IsMaximal := center_isMaximal hc' hc0' hs W
  have hPc := comap_center hs W
  obtain ⟨b₁, h₁, ⟨N⟩⟩ := hND a c c' hc hc' hc0' P' hPmax hPc (hex P' hPmax hPc)
  have hP₁ : placeIdeal hc' b₁.1 b₁.2.2 = P' := by
    have : b₁ ∈ outerBranches hc' P' := by rw [h₁]; exact Set.mem_singleton b₁
    exact this
  -- valuations on the twist `(a, c)`
  have hWC (b : C) : W.1 (algebraMap C G b) = ‖b‖₊ := by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) G, ← Valuation.comap_apply,
      W.2, gaussRat_algebraMap_C, NormedField.valuation_apply]
  have hW1 (y : Rint c' G) (hy : y ∉ P') : W.1 (y : G) = 1 :=
    le_antisymm (valuation_le_one_of_isIntegral hs W y.2) (not_lt.1 fun h ↦ hy h)
  have hconst (y : Rint c' G) (hy : y ∉ P') :
      ∃ κ : C, ‖κ‖₊ = 1 ∧ W.1 ((y : G) - algebraMap C G κ) < 1 := by
    obtain ⟨κ, -, hκ⟩ := exists_sub_const_lt_one hs W y
    refine ⟨κ, ?_, hκ⟩
    have h := Valuation.map_eq_of_sub_lt W.1 (x := (y : G))
      (y := algebraMap C G κ) (by rw [Valuation.map_sub_swap, hW1 y hy]; exact hκ)
    rw [hW1 y hy, hWC] at h
    exact h
  obtain ⟨κσ, hκσ, hσκ⟩ := hconst N.σ N.σ_notMem
  obtain ⟨κe, hκe, heκ⟩ := hconst N.e N.e_notMem
  obtain ⟨κu, hκu, huκ⟩ := hconst N.σu N.σu_notMem
  -- `W(u) = |π|`, `πᵈ = β`
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq β (N.one_le_d : 0 < N.d)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by have := N.one_le_d; omega)] at hπ
    exact hβ0 hπ.symm
  have hWx : W.1 (xF C G) = ‖β‖₊ := by
    change W.1 (algebraMap (RatFunc C) G RatFunc.X) = _
    rw [← Valuation.comap_apply, W.2, AnnulusUnit.gaussRat_X]
    rfl
  have hWu : W.1 N.u = ‖π‖₊ := by
    have h := congrArg W.1 N.x_eq
    rw [map_mul, map_mul, map_pow, hW1 _ N.σ_notMem, hW1 _ N.e_notMem, one_mul, one_mul,
      hWx] at h
    have h' : W.1 N.u ^ N.d = ‖π‖₊ ^ N.d := h.symm.trans (by rw [← nnnorm_pow, hπ])
    exact (pow_left_inj₀ zero_le zero_le (by have := N.one_le_d; omega)).1 h'
  -- passing to the twist `(a + cβ, cβ)`
  let ι : G ≃+* H := affId (F' := F') (a := a) (a' := a + c * β) hc hcβ
  have hwι (y : G) : v.1 (ι y) = W.1 y := (extTrans_apply hc hβ0 hle v y).symm
  have hιC (b : C) : ι (algebraMap C G b) = algebraMap C H b := rfl
  have hιx : ι (xF C G) = algebraMap C H β * xF C H + algebraMap C H β :=
    affId_xF (F' := F') (a := a) (β := β) (γ := β) hc hβ0
  have hβH : algebraMap C H β ≠ 0 := by simpa using hβ0
  have hβG : algebraMap C G β ≠ 0 := by simpa using hβ0
  have hx1 : xF C H + 1 = ι (xF C G * (algebraMap C G β)⁻¹) := by
    rw [map_mul, map_inv₀, hιC]
    rw [hιx, add_mul, mul_comm (algebraMap C H β), mul_assoc, mul_inv_cancel₀ hβH, mul_one]
  set U : H := ι (N.u * (algebraMap C G π)⁻¹)
  have hπ0' : algebraMap C G π ≠ 0 := by simpa using hπ0
  have hU : v.1 U = 1 := by
    rw [hwι, map_mul, map_inv₀, hWu, hWC, mul_inv_cancel₀ (nnnorm_ne_zero_iff.2 hπ0)]
  set lam : C := κe / κσ
  have hlam1 : ‖lam‖₊ = 1 := by rw [nnnorm_div, hκe, hκσ, div_one]
  have hσ0 : ((N.σ : G)) ≠ 0 := fun h ↦ by
    have := hW1 _ N.σ_notMem
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hκσ0 : κσ ≠ 0 := fun h ↦ by rw [h, nnnorm_zero] at hκσ; exact zero_ne_one hκσ
  have hκσ' : algebraMap C G κσ ≠ 0 := by simpa using hκσ0
  have hπγ : algebraMap C G π ^ N.d = algebraMap C G β := by rw [← map_pow, hπ]
  have hinner : xF C G * (algebraMap C G β)⁻¹ - algebraMap C G lam *
      (N.u * (algebraMap C G π)⁻¹) ^ N.d =
      ((N.e - algebraMap C G κe) * algebraMap C G κσ -
        algebraMap C G κe * (N.σ - algebraMap C G κσ)) /
        ((N.σ : G) * algebraMap C G κσ) * (N.u * (algebraMap C G π)⁻¹) ^ N.d := by
    have hx : xF C G = N.e * N.u ^ N.d / N.σ := by
      rw [eq_div_iff hσ0, mul_comm]
      exact N.x_eq
    have hk1 : algebraMap C G κσ * (algebraMap C G κσ)⁻¹ = 1 := mul_inv_cancel₀ hκσ'
    have hs1 : (N.σ : G) * (N.σ : G)⁻¹ = 1 := mul_inv_cancel₀ hσ0
    rw [hx]
    simp only [lam, map_div₀]
    rw [← hπγ]
    linear_combination (-(N.e : G) * (N.σ : G)⁻¹ * N.u ^ N.d * ((algebraMap C G π)⁻¹) ^ N.d) * hk1 +
      (algebraMap C G κe * (algebraMap C G κσ)⁻¹ * N.u ^ N.d * ((algebraMap C G π)⁻¹) ^ N.d) * hs1
  have hWinner : W.1 (xF C G * (algebraMap C G β)⁻¹ - algebraMap C G lam *
      (N.u * (algebraMap C G π)⁻¹) ^ N.d) < 1 := by
    rw [hinner, map_mul, map_pow, map_mul, map_inv₀, hWu, hWC, mul_inv_cancel₀
      (nnnorm_ne_zero_iff.2 hπ0), one_pow, mul_one, map_div₀, map_mul, hW1 _ N.σ_notMem, hWC,
      hκσ, one_mul, div_one]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [map_mul, hWC, hκσ, mul_one]
      exact heκ
    · rw [map_mul, hWC, hκe, one_mul]
      exact hσκ
  have hxdiff : v.1 (xF C H + 1 - algebraMap C H lam * U ^ N.d) < 1 := by
    have key : xF C H + 1 - algebraMap C H lam * U ^ N.d = ι (xF C G * (algebraMap C G β)⁻¹ -
        algebraMap C G lam * (N.u * (algebraMap C G π)⁻¹) ^ N.d) := by
      simp only [map_sub, map_mul, map_pow, ← hx1, hιC]
      rfl
    rw [key, hwι]
    exact hWinner
  -- the degree bound `[κ(v) : k(x̄)] ≤ d`, and `W` is the only extension centred at `P'`
  have hsum := tubeDegree_eq_vertexDegree (F' := G) hp hp1 hc' hc0' hs (cs := β)
    (by rw [NormedField.valuation_apply]; rfl) P'
  rw [vertexDegree_eq_ord_of_eq_singleton hc' h₁, NodeData.ord_x hc' hP₁ N] at hsum
  have hmemW : W ∈ Finset.univ.filter
      (fun w' : GaussExtension (0 : C) sβ G ↦ center hs w' = P') :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  have hleW := Finset.single_le_sum (f := fun w' : GaussExtension (0 : C) sβ G ↦
    FundamentalInequality.ramificationIdx (RatFunc C) w'.1 *
      FundamentalInequality.inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 sβ) w'.1)
    (fun _ _ ↦ Nat.zero_le _) hmemW
  rw [← tubeDegree, hsum, ramificationIdx_extTrans hc hβ0 hle v, one_mul] at hleW
  have hf : Module.finrank 𝓀⟮red C (xF C H) v⟯ (ResidueField v.1.valuationSubring) ≤ N.d := by
    rw [finrank_adjoin_red_x, ← inertiaDeg_extTrans hc hβ0 hle v]
    exact hleW
  obtain ⟨lamR, hlamR, hred, htop, hfd⟩ :=
    residue_of_node_coord v hU hlam1 N.one_le_d hxdiff hf
  have hefW : FundamentalInequality.ramificationIdx (RatFunc C) W.1 *
      FundamentalInequality.inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 sβ) W.1 =
        N.d := by
    rw [ramificationIdx_extTrans hc hβ0 hle v, one_mul, inertiaDeg_extTrans hc hβ0 hle v,
      ← finrank_adjoin_red_x, hfd]
  have huniq : ∀ W' : GaussExtension (0 : C) sβ G, center hs W' = P' → W' = W := by
    intro W' hW'
    by_contra hne
    have hmem' : W' ∈ Finset.univ.filter
        (fun w' : GaussExtension (0 : C) sβ G ↦ center hs w' = P') :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hW'⟩
    have h2 := Finset.add_le_sum (f := fun w' : GaussExtension (0 : C) sβ G ↦
      FundamentalInequality.ramificationIdx (RatFunc C) w'.1 *
        FundamentalInequality.inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 sβ) w'.1)
      (fun _ _ ↦ Nat.zero_le _) hmem' hmemW hne
    rw [← tubeDegree, hsum, hefW] at h2
    have h3 : 1 ≤ FundamentalInequality.ramificationIdx (RatFunc C) W'.1 *
        FundamentalInequality.inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 sβ) W'.1 :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (FundamentalInequality.ramificationIdx_ne_zero _)
        (Nat.pos_iff_ne_zero.1 NormedTower.inertiaDeg_pos))
    omega
  -- a separating element of the node chart
  set T : Finset (Ideal (Rint c' G)) := (Finset.univ.image (center hs)).erase P'
  obtain ⟨h₀, hh1, hhT⟩ := exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    obtain ⟨w', -, rfl⟩ := Finset.mem_image.1 hQ
    exact ⟨center_isMaximal hc' hc0' hs w', hne⟩
  have hWh : ∀ W' : GaussExtension (0 : C) sβ G, W' ≠ W → W'.1 (h₀ : G) < 1 := fun W' hne ↦ by
    have hc'' : center hs W' ≠ P' := fun h ↦ hne (huniq W' h)
    exact hhT _ (Finset.mem_erase.2 ⟨hc'', Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
  have hWh1 : W.1 ((h₀ : G) - 1) < 1 := hh1
  set r : ℝ≥0 := Finset.univ.sup fun W' : GaussExtension (0 : C) sβ G ↦
    if W' = W then 0 else W'.1 (h₀ : G)
  have hr : r < 1 := (Finset.sup_lt_iff zero_lt_one).2 fun W' _ ↦ by
    split_ifs with h
    · exact zero_lt_one
    · exact hWh W' h
  obtain ⟨N₀, hN₀⟩ := NNReal.exists_pow_lt_of_lt_one (nnnorm_pos.2 hπ0) hr
  have hWhN : ∀ W' : GaussExtension (0 : C) sβ G, W' ≠ W → W'.1 (h₀ : G) ^ N₀ < ‖π‖₊ :=
    fun W' hne ↦ by
      refine lt_of_le_of_lt (pow_le_pow_left₀ zero_le ?_ N₀) hN₀
      have := Finset.le_sup (f := fun W' : GaussExtension (0 : C) sβ G ↦
        if W' = W then 0 else W'.1 (h₀ : G)) (Finset.mem_univ W')
      simpa [hne] using this
  -- the residue of `σ_u`
  have hκu1 : ‖κu‖₊ ≤ 1 := hκu.le
  set mu : 𝓀 := IsLocalRing.residue (HenselComplete.integers C)
    ⟨κu, by simpa using (HenselComplete.mem_integers_iff κu).2 (by exact_mod_cast hκu1)⟩
  have hmu : mu ≠ 0 := by
    rw [Ne, GaussTube.residue_eq_zero_iff_norm, not_lt]
    change 1 ≤ ‖κu‖
    rw [← coe_nnnorm, hκu, NNReal.coe_one]
  have hσu1 : v.1 (ι (N.σu : G)) = 1 := by rw [hwι]; exact hW1 _ N.σu_notMem
  have hκuH : v.1 (algebraMap C H κu) ≤ 1 := by rw [valuation_algebraMap_C']; exact hκu1
  have hredσ : red C (ι (N.σu : G)) v = algebraMap 𝓀 _ mu := by
    have h0 : red C (ι (N.σu : G) - algebraMap C H κu) v = 0 := by
      rw [red_eq_zero_iff ((Valuation.map_sub _ _ _).trans (max_le hσu1.le hκuH)), ← hιC,
        ← map_sub, hwι]
      exact huκ
    rw [red_sub hσu1.le hκuH, sub_eq_zero, red_algebraMap_C κu hκu1] at h0
    exact h0
  have hh₀1 : W.1 (h₀ : G) ≤ 1 := valuation_le_one_of_isIntegral hs W h₀.2
  refine ⟨U, N.d, lamR, N.one_le_d, htop, hred, N.uR, h₀ ^ N₀, π, mu, hπ0, hmu, ?_, ?_, ?_,
    fun W' hW' ↦ ?_⟩
  · rw [N.uR_eq, map_mul, hW1 _ N.σu_notMem, one_mul, hWu]
  · have heq : ι ((N.uR : G) * (algebraMap C G π)⁻¹) = ι (N.σu : G) * U := by
      rw [N.uR_eq, mul_assoc, map_mul]
    rw [heq, red_mul hσu1.le hU.le, hredσ]
  · have heq : ((h₀ ^ N₀ : Rint c' G) : G) - 1 =
        ((h₀ : G) - 1) * ∑ i ∈ Finset.range N₀, (h₀ : G) ^ i := by
      rw [mul_comm, geom_sum_mul]
      rfl
    rw [heq, map_mul]
    refine (mul_le_of_le_one_right zero_le ?_).trans_lt hWh1
    exact (Valuation.map_sum_le _ fun i _ ↦ by rw [map_pow]; exact pow_le_one₀ zero_le hh₀1)
  · have := hWhN W' hW'
    rw [← map_pow] at this
    exact this

/-- An element of the twist `(a, c)` integral over `C[x]` and bounded at the extensions of
`w_{0,|β|}` lies in the disc chart of the twist `(a + cβ, cβ)`. -/
lemma isIntegral_affId {a c β : C} (hc : c ≠ 0) (hβ0 : β ≠ 0) {z : Aff a c hc F'}
    (hz : IsIntegral (Algebra.adjoin C {xF C (Aff a c hc F')}) z)
    (hW : ∀ v' : Ext C (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F'),
      (extTrans hc hβ0 (hle_aux) v').1 z ≤ 1) :
    IsIntegral (discRing (0 : C) 1)
      (affId (F' := F') (a := a) (a' := a + c * β) hc (mul_ne_zero hc hβ0) z) := by
  set ι := affId (F' := F') (a := a) (a' := a + c * β) hc (mul_ne_zero hc hβ0)
  let φ : Algebra.adjoin C {xF C (Aff a c hc F')} →+*
      Algebra.adjoin C {xF C (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F')} :=
    { toFun := fun y ↦ ⟨ι y, affId_mem_adjoin hc hβ0 y.2⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun y z ↦ Subtype.ext (map_mul ι (y : Aff a c hc F') z)
      map_zero' := Subtype.ext (map_zero ι)
      map_add' := fun y z ↦ Subtype.ext (map_add ι (y : Aff a c hc F') z) }
  have hcomp : (algebraMap (Algebra.adjoin C {xF C (Aff (a + c * β) (c * β)
      (mul_ne_zero hc hβ0) F')}) (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F')).comp φ =
      ι.toRingHom.comp (algebraMap (Algebra.adjoin C {xF C (Aff a c hc F')}) (Aff a c hc F')) :=
    RingHom.ext fun y ↦ by
      change ι (y : Aff a c hc F') = ι (y : Aff a c hc F')
      rfl
  refine SmoothVertex.isIntegral_of_le hp hp1
    (IsIntegral.map_of_comp_eq φ ι.toRingHom hcomp hz) fun v' ↦ ?_
  rw [← extTrans_apply hc hβ0 (hle_aux) v' z]
  exact hW v'

set_option maxHeartbeats 400000 in
-- the long proof manipulates several affine twists of `F'` (elaboration of the type synonyms)
attribute [local instance] GaussFibre.isCurveFunctionField_F in
/-- **Local coordinate data at a vertex of an exhausting annulus.** Let `|c'| < |t| < 1`
(`t = (x - a)/c`) be exhausting with exact node data, `|c'| < |β| < 1`, and `v` an extension of the
Gauss point `w_{a + cβ,|cβ|} = w_{a,|cβ|}` (on the twist by `(a + cβ, cβ)`, coordinate
`t' = t/β - 1`). Then `κ(v) = k(ū)` with `t̄' + 1 = λ ūᵈ`, and there are `Y₁, Y₂` in the disc
chart with `Ȳ₂ = (t̄' + 1)ᵐ`, `Ȳ₁ = μ Ȳ₂ ū` at `v` and `Ȳ₂ = 0` at every other extension. -/
theorem exists_coord_data (hND : NodeDataOfODP C F') {a c c' : C} (hc : c ≠ 0) (hc' : ‖c'‖ < 1)
    (hc0' : c' ≠ 0) (hex : IsExhausting a hc hc' hc0' F') {β : C} (hβ0 : β ≠ 0)
    (h1 : ‖c'‖ < ‖β‖) (h2 : ‖β‖ < 1) (v : Ext C (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F')) :
    ∃ (U : Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F') (d : ℕ) (lam : 𝓀), 1 ≤ d ∧
      𝓀⟮red C U v⟯ = ⊤ ∧
      red C (xF C (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F')) v + 1 =
        algebraMap 𝓀 _ lam * red C U v ^ d ∧
      ∃ (Y₁ Y₂ : DRint (0 : C) 1 (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F')) (m : ℕ)
        (mu : 𝓀), mu ≠ 0 ∧
        redD v Y₂ = (red C (xF C (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F')) v + 1) ^ m ∧
        redD v Y₁ = algebraMap 𝓀 _ mu * redD v Y₂ * red C U v ∧
        ∀ v' : Ext C (Aff (a + c * β) (c * β) (mul_ne_zero hc hβ0) F'), v' ≠ v →
          redD v' Y₂ = 0 := by
  obtain ⟨U, d, lam, hd, htop, hred, uR, q, π, mu, hπ0, hmu, hWuR, hredU, hq1, hqW⟩ :=
    vertex_data hp hp1 hND hc hc' hc0' hex hβ0 h1 h2 v
  refine ⟨U, d, lam, hd, htop, hred, ?_⟩
  classical
  have hcβ : c * β ≠ 0 := mul_ne_zero hc hβ0
  set G := Aff a c hc F'
  set H := Aff (a + c * β) (c * β) hcβ F'
  set ι : G ≃+* H := affId (F' := F') (a := a) (a' := a + c * β) hc hcβ
  set sβ : ℝ≥0ˣ := Units.mk0 ‖β‖₊ (nnnorm_ne_zero_iff.2 hβ0)
  set W := extTrans hc hβ0 (hle_aux) v
  have hwι (y : G) : v.1 (ι y) = W.1 y := (extTrans_apply hc hβ0 (hle_aux) v y).symm
  have hs : sβ ∈ segment c' :=
    ⟨show ‖c'‖₊ < ‖β‖₊ by exact_mod_cast h1, show ‖β‖₊ < 1 by exact_mod_cast h2⟩
  have hWx (W' : GaussExtension (0 : C) sβ G) : W'.1 (xF C G) = ‖β‖₊ := by
    change W'.1 (algebraMap (RatFunc C) G RatFunc.X) = _
    rw [← Valuation.comap_apply, W'.2, AnnulusUnit.gaussRat_X]
    rfl
  have hWC (W' : GaussExtension (0 : C) sβ G) (b : C) : W'.1 (algebraMap C G b) = ‖b‖₊ := by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) G, ← Valuation.comap_apply,
      W'.2, gaussRat_algebraMap_C, NormedField.valuation_apply]
  have hcint : ∀ b : C, IsIntegral (Algebra.adjoin C {xF C G}) (algebraMap C G b) := fun b ↦
    isIntegral_of_mem_adjoin (Subalgebra.algebraMap_mem _ b)
  have hxint : ∀ D : ℕ, IsIntegral (Algebra.adjoin C {xF C G}) (xF C G ^ D) := fun D ↦
    isIntegral_of_mem_adjoin (pow_mem (Algebra.self_mem_adjoin_singleton C (xF C G)) D)
  obtain ⟨D₁, hD₁⟩ := exists_pow_mul_isIntegral_of_nodeRing (G := G) c' (q * uR).2
  obtain ⟨D₂, hD₂⟩ := exists_pow_mul_isIntegral_of_nodeRing (G := G) c' q.2
  set m := D₁ + D₂
  have hmint : ∀ (y : G) (D : ℕ), D ≤ m → IsIntegral (Algebra.adjoin C {xF C G}) (xF C G ^ D * y) →
      IsIntegral (Algebra.adjoin C {xF C G}) (xF C G ^ m * y) := fun y D hD hy ↦ by
    have : xF C G ^ m * y = xF C G ^ (m - D) * (xF C G ^ D * y) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hD]
    rw [this]
    exact (hxint _).mul hy
  -- the two elements
  set z₂ : G := algebraMap C G (β⁻¹ ^ m) * (xF C G ^ m * (q : G))
  set z₁ : G := algebraMap C G (β⁻¹ ^ m * π⁻¹) * (xF C G ^ m * ((q : G) * (uR : G)))
  have hz₂ : IsIntegral (Algebra.adjoin C {xF C G}) z₂ :=
    (hcint _).mul (hmint _ D₂ (by omega) hD₂)
  have hz₁ : IsIntegral (Algebra.adjoin C {xF C G}) z₁ :=
    (hcint _).mul (hmint _ D₁ (by omega) hD₁)
  have hβm : ‖β⁻¹ ^ m‖₊ * ‖β‖₊ ^ m = 1 := by
    rw [nnnorm_pow, nnnorm_inv, ← mul_pow, inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hβ0), one_pow]
  have hval₂ (W' : GaussExtension (0 : C) sβ G) : W'.1 z₂ = W'.1 (q : G) := by
    rw [map_mul, map_mul, hWC, map_pow, hWx, ← mul_assoc, hβm, one_mul]
  have hval₁ (W' : GaussExtension (0 : C) sβ G) :
      W'.1 z₁ = ‖π‖₊⁻¹ * (W'.1 (q : G) * W'.1 (uR : G)) := by
    have h : z₁ = algebraMap C G π⁻¹ * (z₂ * (uR : G)) := by
      simp only [z₁, z₂, map_mul]
      ring
    rw [h, map_mul, map_mul, hWC, hval₂, nnnorm_inv]
  have hqle (W' : GaussExtension (0 : C) sβ G) : W'.1 (q : G) ≤ 1 :=
    valuation_le_one_of_isIntegral hs W' q.2
  have huR1 (W' : GaussExtension (0 : C) sβ G) : W'.1 (uR : G) ≤ 1 :=
    valuation_le_one_of_isIntegral hs W' uR.2
  have hπpos : (0 : ℝ≥0) < ‖π‖₊ := nnnorm_pos.2 hπ0
  -- `extTrans` is injective
  have hinj : ∀ v' : Ext C H, extTrans hc hβ0 (hle_aux) v' = W → v' = v := by
    intro v' h
    refine Subtype.ext (Valuation.ext fun y ↦ ?_)
    have := congrArg (fun W'' : GaussExtension (0 : C) sβ G ↦ W''.1 (ι.symm y)) h
    rw [extTrans_apply, ← hwι] at this
    change v'.1 (ι (ι.symm y)) = v.1 (ι (ι.symm y)) at this
    rwa [RingEquiv.apply_symm_apply] at this
  have hb₂ : ∀ v' : Ext C H, (extTrans hc hβ0 (hle_aux) v').1 z₂ ≤ 1 := fun v' ↦ by
    rw [hval₂]; exact hqle _
  have hb₁ : ∀ v' : Ext C H, (extTrans hc hβ0 (hle_aux) v').1 z₁ ≤ 1 := fun v' ↦ by
    rw [hval₁, inv_mul_le_iff₀ hπpos, mul_one]
    by_cases hv : v' = v
    · subst hv
      rw [hWuR]
      exact mul_le_of_le_one_left zero_le (hqle _)
    · have h3 := hqW _ fun h ↦ hv (hinj v' h)
      exact (mul_le_of_le_one_right zero_le (huR1 _)).trans h3.le
  -- the elements of the disc chart and their reductions
  have hιx : ι (xF C G) = algebraMap C H β * xF C H + algebraMap C H β :=
    affId_xF (F' := F') (a := a) (β := β) (γ := β) hc hβ0
  have hβH : algebraMap C H β ≠ 0 := by simpa using hβ0
  have hιz₂ : ι z₂ = (xF C H + 1) ^ m * ι (q : G) := by
    simp only [z₂, map_mul]
    rw [show ι (algebraMap C G (β⁻¹ ^ m)) = algebraMap C H (β⁻¹ ^ m) from rfl, map_pow ι, hιx,
      map_pow, map_inv₀, ← mul_assoc, ← mul_pow]
    congr 2
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hβH, one_mul]
  have hιz₁ : ι z₁ = ι z₂ * ι ((uR : G) * (algebraMap C G π)⁻¹) := by
    rw [← map_mul]
    congr 1
    simp only [z₁, z₂, map_mul, map_inv₀, map_pow]
    ring
  have hx1 : v.1 (xF C H + 1) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le (valuation_xF v).le (by rw [map_one]))
  have hιq : v.1 (ι (q : G)) ≤ 1 := by rw [hwι]; exact hqle W
  have hredq : red C (ι (q : G)) v = 1 := by
    have h0 : red C (ι (q : G) - 1) v = 0 := by
      rw [red_eq_zero_iff ((Valuation.map_sub _ _ _).trans (max_le hιq (by rw [map_one]))),
        ← map_one ι, ← map_sub, hwι]
      exact hq1
    rwa [red_sub hιq (by rw [map_one]), red_one, sub_eq_zero] at h0
  have hπ1 : ‖π‖₊ ≤ 1 := hWuR ▸ huR1 W
  have hιu : v.1 (ι ((uR : G) * (algebraMap C G π)⁻¹)) ≤ 1 := by
    rw [hwι, map_mul, map_inv₀, hWuR, hWC, mul_inv_cancel₀ hπpos.ne']
  have hz₂v : v.1 (ι z₂) ≤ 1 := by rw [hwι, hval₂]; exact hqle W
  let Y₂ : DRint (0 : C) 1 H := ⟨ι z₂, isIntegral_affId hp hp1 hc hβ0 hz₂ hb₂⟩
  let Y₁ : DRint (0 : C) 1 H := ⟨ι z₁, isIntegral_affId hp hp1 hc hβ0 hz₁ hb₁⟩
  have hY₂ : redD v Y₂ = (red C (xF C H) v + 1) ^ m := by
    rw [redD_apply]
    change red C (ι z₂) v = _
    rw [hιz₂, red_mul (by rw [map_pow]; exact pow_le_one₀ zero_le hx1) hιq, red_pow hx1, hredq,
      mul_one, red_add (valuation_xF v).le (by rw [map_one]), red_one]
  refine ⟨Y₁, Y₂, m, mu, hmu, hY₂, ?_, fun v' hv' ↦ ?_⟩
  · rw [redD_apply]
    change red C (ι z₁) v = _
    rw [hιz₁, red_mul hz₂v hιu, hredU]
    change red C (ι z₂) v * _ = _ * red C (ι z₂) v * _
    ring
  · rw [redD_apply]
    change red C (ι z₂) v' = 0
    have hlt : v'.1 (ι z₂) < 1 := by
      rw [← extTrans_apply hc hβ0 (hle_aux) v' z₂, hval₂]
      exact (hqW _ fun h ↦ hv' (hinj v' h)).trans_le hπ1
    exact (red_eq_zero_iff hlt.le).2 hlt

omit hp hp1 in
include hp hp1 in
/-- Every point of the disc chart over the residue point lies on a branch of the outer vertex. -/
lemma exists_branch {H : Type*} [Field H] [Algebra (RatFunc C) H] [Algebra C H]
    [IsScalarTower C (RatFunc C) H] [FiniteDimensional (RatFunc C) H]
    (P : Ideal (DRint (0 : C) 1 H)) [P.IsMaximal]
    (hP : P.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 H)) = discIdeal (0 : C) 1) :
    ∃ (v : Ext C H) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring))
      (hQ : Q ∈ zeros 𝓀 (red C (xF C H) v)), placeIdealD v hQ = P := by
  classical
  haveI : Finite (Ext C H) := finite_ext hp hp1
  letI : Fintype (Ext C H) := Fintype.ofFinite _
  have hΛ : ChartLocal.IsChart 𝓀 (fun w : Ext C H ↦ red C (xF C H) w) (redRing C H (xF C H)) :=
    { const := algebraMap_mem_redRing _
      mem := red_mem_redRing GaussFibre.xF_mem_intRing
      le := by
        rintro _ ⟨f, hf, rfl⟩ w Q hQ
        exact redD_mem_V w ⟨f, SmoothVertex.isIntegral_of_le hp hp1 hf.1
          (valuation_le_one_of_mem_intRing hf)⟩ hQ
      tr := fun w ↦ transcendental_red_x w }
  obtain ⟨b, hb⟩ := ChartLocal.exists_mem_brs hΛ (DiscBridge.map_isMaximal hp hp1 hP)
  obtain ⟨hQ, hPQ⟩ := DiscBridge.of_mem_brs hp hp1 hΛ hP hb
  exact ⟨b.1, b.2, hQ, hPQ⟩

/-- **Residue discs of the skeleton of an exhausting annulus are good**: for `|c'| < |β| < 1`,
every point over the open disc `|x - (a + cβ)| < |cβ|` is smooth. -/
theorem discSmooth_of_exhausting (hND : NodeDataOfODP C F') {a c c' : C} (hc : c ≠ 0)
    (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0) (hex : IsExhausting a hc hc' hc0' F') {β : C} (hβ0 : β ≠ 0)
    (h1 : ‖c'‖ < ‖β‖) (h2 : ‖β‖ < 1) : DiscSmooth F' (a + c * β) (mul_ne_zero hc hβ0) := by
  intro P hPmax hP
  obtain ⟨v, R, hR, hRP⟩ := exists_branch hp hp1 P hP
  obtain ⟨U, d, lam, hd, htop, hred, Y₁, Y₂, m, mu, hmu, hY₂, hY₁, hoth⟩ :=
    exists_coord_data hp hp1 hND hc hc' hc0' hex hβ0 h1 h2 v
  exact isDiscSmooth_of_coord P v hR hRP htop hd hred hmu hY₂ hY₁ hoth

/-- **(T⇒), off-skeleton clause** (modulo exact node data at ordinary double points): the Gauss
points `w_{a + cβ, |cγ|}` (`|c'| < |β| < 1`, `|γ| < |β|`) of an exhausting annulus off its
skeleton are discs of a tube. Proof: they lie in the residue disc `|x - (a + cβ)| < |cβ|` of the
skeleton point `w_{a,|cβ|}`, which is good (`discSmooth_of_exhausting`), and (D⇒) applies
(`isTubeDisc_of_discSmooth`). -/
theorem offSkeletonOfExhausting (hND : NodeDataOfODP C F') : OffSkeletonOfExhausting C F' := by
  intro a c c' hc hc' hc0' hex β γ hγ h1 h2 h3
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h1
    exact absurd h1 (not_lt.2 (norm_nonneg _))
  have hβpos : 0 < ‖β‖ := norm_pos_iff.2 hβ0
  have hsm := discSmooth_of_exhausting hp hp1 hND hc hc' hc0' hex hβ0 h1 h2
  have hγβ : γ / β ≠ 0 := div_ne_zero hγ hβ0
  have hlt : ‖γ / β‖ < 1 := by rw [norm_div, div_lt_one hβpos]; exact h3
  have h := isTubeDisc_of_discSmooth hp hp1 (mul_ne_zero hc hβ0) hsm (β := 0) (by simp) hγβ hlt
  refine (isTubeDisc_congr _ _ (by ring) ?_).1 h
  field_simp

end ExhaustGluing

end SemistableReduction
