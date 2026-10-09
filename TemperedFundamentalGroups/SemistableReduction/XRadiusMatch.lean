/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XRadius
import TemperedFundamentalGroups.SemistableReduction.XLift
import TemperedFundamentalGroups.SemistableReduction.XLengthChain

/-!
# Radii of a node over a node (Blueprint §9.7, X1/X2)

Let `L₂ ⊆ L₁` be function fields over finite extensions `K₂`, `K₁` of `K` (`ϖ = η₁ ϖ₁ ^ e₁`,
`ϖ = η₂ ϖ₂ ^ e₂`), `z` an unfolded node of a model of `L₁` and `y'` an unfolded node of a model of
`L₂` on the same x-line (`UnfoldedNodeGerm`).

* `rho_match`: if a monomial point `U` of `z` at `s` restricts to a monomial point of `y'` at `s'`,
  then the normalised radii agree:
  `(ord β + α + e s) / e₁ = (ord β' + α' + e' s') / e₂` (`rho_eq_of_restrict'`);
* `node_slope`: if the germs of `y'` map into those of `z` and `u' = ε u ^ p ϖ₁ ^ r` (`p ≥ 1`), the
  interior monomial points of `z` restrict to those of `y'` at `(r + p s) e₂ / e₁`
  (`NodeGerm.isMonomialPt_comap`), so the slopes agree: `e = e' p`; the other orientation
  `u' = ε v ^ p ϖ₁ ^ r` is impossible (the radius would decrease along `z`).
-/

open Polynomial

namespace SemistableReduction

/-- Monomial parameters are at most the thickness. -/
lemma IsMonomialPt.le_of_mul_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    {O : ValuationSubring K} {Q : Set F} {ϖ u v : F} {n : ℕ} {s : ℚ} {U : ValuationSubring F}
    (hU : IsMonomialPt O Q ϖ u s U) (hv : v ∈ Q) (huv : u * v = ϖ ^ n) (hϖ0 : ϖ ≠ 0) :
    s ≤ n := by
  have hw0 : U.valuation ϖ ≠ 0 := by simpa using hϖ0
  have hw1 := hU.2.1
  have hvU : U.valuation v ≤ 1 := (U.valuation_le_one_iff _).2 (hU.1 hv)
  have hprod : U.valuation u * U.valuation v = U.valuation ϖ ^ n := by
    rw [← map_mul, huv, map_pow]
  have hu : U.valuation ϖ ^ n ≤ U.valuation u := hprod ▸ mul_le_of_le_one_right' hvU
  have h := hU.2.2.1
  unfold IsLogValue at h
  have key : U.valuation ϖ ^ ((n : ℤ) * s.den) ≤ U.valuation ϖ ^ s.num := by
    rw [← h, zpow_mul, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left₀ zero_le hu _
  have hle : s.num ≤ (n : ℤ) * s.den := by
    by_contra hlt
    push Not at hlt
    have := zpow_lt_zpow_right_of_lt_one₀ (zero_lt_iff.2 hw0) hw1 hlt
    exact absurd key (not_le.2 this)
  have hs : s = s.num / s.den := (Rat.num_div_den s).symm
  rw [hs, div_le_iff₀ (by exact_mod_cast s.den_pos)]
  exact_mod_cast hle

variable {K K₁ K₂ L₁ L₂ : Type*} [Field K] [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra K K₁] [Algebra K K₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
  [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
  [IsScalarTower K L₂ L₁] [Algebra.IsAlgebraic K K₁] [Algebra.IsAlgebraic K K₂]
  {O₁ : ValuationSubring K₁} [IsDiscreteValuationRing O₁] {ϖ₁ : O₁}
  {O₂ : ValuationSubring K₂} [IsDiscreteValuationRing O₂] {ϖ₂ : O₂}

/-- **Radii of a monomial point and of its restriction agree.** -/
theorem rho_match (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂) {ϖ : K} {η₁ : O₁ˣ}
    {η₂ : O₂ˣ} {e₁ e₂ : ℕ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hϖK₁ : algebraMap K K₁ ϖ = (η₁ : K₁) * (ϖ₁ : K₁) ^ e₁)
    (hϖK₂ : algebraMap K K₂ ϖ = (η₂ : K₂) * (ϖ₂ : K₂) ^ e₂)
    {P : Subring L₁} {u v x₁ ε : L₁} {n : ℕ} {a β : K₁} {e α : ℕ}
    {W₁ W₂ : ValuationSubring L₁} (H : UnfoldedNodeGerm O₁ ϖ₁ P u v n x₁ a β e α ε W₁ W₂)
    {Q : Subring L₂} {u' v' x₂ ε' : L₂} {n' : ℕ} {a' β' : K₂} {e' α' : ℕ}
    {W₁' W₂' : ValuationSubring L₂}
    (H' : UnfoldedNodeGerm O₂ ϖ₂ Q u' v' n' x₂ a' β' e' α' ε' W₁' W₂')
    (hx : algebraMap L₂ L₁ x₂ = x₁) {s s' : ℚ} (hs0 : 0 ≤ s) (hsn : s ≤ n) (hs0' : 0 ≤ s')
    (hsn' : s' ≤ n') {U : ValuationSubring L₁}
    (hU : IsMonomialPt O₁ (P : Set L₁) (algebraMap K₁ L₁ (ϖ₁ : K₁)) u s U)
    (hU' : IsMonomialPt O₂ (Q : Set L₂) (algebraMap K₂ L₂ (ϖ₂ : K₂)) u' s'
      (U.comap (algebraMap L₂ L₁))) :
    (ordO O₁ ϖ₁ β + α + e * s) / e₁ = (ordO O₂ ϖ₂ β' + α' + e' * s') / e₂ := by
  letI : Algebra L₂ (Fbar L₁) := ((algebraMap L₁ (Fbar L₁)).comp (algebraMap L₂ L₁)).toAlgebra
  let φ : Fbar L₂ →ₐ[L₂] Fbar L₁ := IsAlgClosed.lift
  have hφ : ∀ y : L₂,
      φ (algebraMap L₂ (Fbar L₂) y) = algebraMap L₁ (Fbar L₁) (algebraMap L₂ L₁ y) :=
    fun y ↦ φ.commutes y
  let φK : Fbar L₂ →ₐ[K] Fbar L₁ :=
    { (φ : Fbar L₂ →+* Fbar L₁) with
      commutes' := fun k ↦ by
        change φ (algebraMap K (Fbar L₂) k) = algebraMap K (Fbar L₁) k
        rw [IsScalarTower.algebraMap_apply K L₂ (Fbar L₂), hφ,
          ← IsScalarTower.algebraMap_apply K L₂ L₁,
          ← IsScalarTower.algebraMap_apply K L₁ (Fbar L₁)] }
  obtain ⟨U', hU'U⟩ := exists_valuationSubring_comap_eq (F := Fbar L₁) U
  have ha := H.isXGauss hϖ₁ he₁ hϖK₁ hs0 hsn hU U' hU'U
  have hcomap : (U'.comap (φ : Fbar L₂ →+* Fbar L₁)).comap (algebraMap L₂ (Fbar L₂)) =
      U.comap (algebraMap L₂ L₁) := by
    ext y
    simp only [ValuationSubring.mem_comap, RingHom.coe_coe, hφ, ← hU'U]
  have hb := H'.isXGauss hϖ₂ he₂ hϖK₂ hs0' hsn' hU' _ hcomap
  -- the base uniformizer and the x-line correspond under `φ`
  have hφϖ : φ (algebraMap L₂ (Fbar L₂) (algebraMap K₂ L₂ (algebraMap K K₂ ϖ))) =
      algebraMap L₁ (Fbar L₁) (algebraMap K₁ L₁ (algebraMap K K₁ ϖ)) := by
    rw [hφ, ← IsScalarTower.algebraMap_apply K K₂ L₂, ← IsScalarTower.algebraMap_apply K L₂ L₁,
      ← IsScalarTower.algebraMap_apply K K₁ L₁]
  have hφx : φ (algebraMap L₂ (Fbar L₂) x₂) = algebraMap L₁ (Fbar L₁) x₁ := by rw [hφ, hx]
  rw [← hφϖ, ← hφx] at ha
  have hϖ0 : algebraMap L₂ (Fbar L₂) (algebraMap K₂ L₂ (algebraMap K K₂ ϖ)) ≠ 0 := by
    rw [hϖK₂]
    have h1 : ((η₂ : O₂) : K₂) ≠ 0 := fun h ↦ η₂.ne_zero (Subtype.ext h)
    have h2 : (ϖ₂ : K₂) ≠ 0 := fun h ↦ hϖ₂.ne_zero (Subtype.ext h)
    simp [h1, h2]
  have hlt : U'.valuation (φ (algebraMap L₂ (Fbar L₂) (algebraMap K₂ L₂ (algebraMap K K₂ ϖ)))) <
      1 := by
    have hcl : ∀ f : L₁, U.valuation f < 1 → U'.valuation (algebraMap L₁ (Fbar L₁) f) < 1 := by
      intro f hf
      refine lt_of_le_of_ne ((U'.valuation_le_one_iff _).2 ?_) fun h1 ↦ ?_
      · have : f ∈ U := (U.valuation_le_one_iff _).1 hf.le
        rw [← hU'U] at this; exact this
      · have hf0 : f ≠ 0 := by rintro rfl; simp at h1
        have hinv : (algebraMap L₁ (Fbar L₁) f)⁻¹ ∈ U' := by
          rw [← U'.valuation_le_one_iff, map_inv₀, h1, inv_one]
        have : f⁻¹ ∈ U := by rw [← hU'U, ValuationSubring.mem_comap, map_inv₀]; exact hinv
        rw [← U.valuation_le_one_iff, map_inv₀] at this
        exact absurd ((inv_le_one₀ (zero_lt_iff.2 (by simpa using hf0))).1 this) (not_le.2 hf)
    rw [hφϖ]
    refine hcl _ ?_
    have hUO := H.germ.comap_eq hϖ₁ hU
    obtain ⟨-, hwp1⟩ := valuation_uniformizer hUO hϖ₁
    have hη : U.valuation (algebraMap K₁ L₁ ((η₁ : O₁) : K₁)) ≤ 1 :=
      (U.valuation_le_one_iff _).2 (hU.1 (H.germ.algebraMap_mem _))
    rw [hϖK₁, map_mul, map_pow, map_mul, map_pow]
    exact (mul_le_of_le_one_left' hη).trans_lt (pow_lt_one₀ zero_le hwp1 he₁.ne')
  -- the centres correspond
  refine rho_eq_of_restrict' (φ : Fbar L₂ →+* Fbar L₁) hϖ0 hlt ha hb ?_ ?_
  · -- `φ (a')` is algebraic over `K₁`
    have hK : IsAlgebraic K (φ (algebraMap (Kbar K₂ L₂) (Fbar L₂)
        (algebraMap K₂ (Kbar K₂ L₂) a'))) := by
      have h0 : IsAlgebraic K a' := Algebra.IsAlgebraic.isAlgebraic a'
      have h1 : IsAlgebraic K (algebraMap K₂ (Fbar L₂) a') :=
        h0.algHom (IsScalarTower.toAlgHom K K₂ (Fbar L₂))
      exact h1.algHom φK
    exact ⟨⟨_, mem_algebraicClosure_iff.2 (hK.tower_top K₁)⟩, rfl⟩
  · -- the centre `a` has a preimage algebraic over `K₂`
    have hK : IsAlgebraic K (algebraMap (Kbar K₁ L₁) (Fbar L₁) (algebraMap K₁ (Kbar K₁ L₁) a)) := by
      have h0 : IsAlgebraic K a := Algebra.IsAlgebraic.isAlgebraic a
      exact h0.algHom (IsScalarTower.toAlgHom K K₁ (Fbar L₁))
    obtain ⟨c, hc⟩ := exists_preimage_of_isAlgebraic φK hK
    have hcK : IsAlgebraic K c := by
      rw [← hc] at hK
      exact (isAlgebraic_algHom_iff φK φK.toRingHom.injective).1 hK
    exact ⟨⟨c, mem_algebraicClosure_iff.2 (hcK.tower_top K₂)⟩, hc⟩

/-- Two affine functions agreeing at `n / 2` and `n / 4` have the same slope. -/
lemma slope_eq_of_two {c₀ c₁ d₀ d₁ n : ℚ} (hn : n ≠ 0)
    (h₁ : c₀ + c₁ * (n / 2) = d₀ + d₁ * (n / 2)) (h₂ : c₀ + c₁ * (n / 4) = d₀ + d₁ * (n / 4)) :
    c₁ = d₁ := by
  have h : (c₁ - d₁) * n = 0 := by linear_combination 4 * h₁ - 4 * h₂
  rcases mul_eq_zero.1 h with h | h
  · linarith
  · exact absurd h hn

/-- **Slopes of a node over a node** (X1/X2): if `u' = ε u ^ p ϖ₁ ^ r` (`p ≥ 1`) then `e = e' p`;
`u' = ε v ^ p ϖ₁ ^ r` is impossible. -/
theorem node_slope (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂) {ϖ : K} {η₁ : O₁ˣ}
    {η₂ : O₂ˣ} {e₁ e₂ : ℕ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hϖK₁ : algebraMap K K₁ ϖ = (η₁ : K₁) * (ϖ₁ : K₁) ^ e₁)
    (hϖK₂ : algebraMap K K₂ ϖ = (η₂ : K₂) * (ϖ₂ : K₂) ^ e₂)
    {P : Subring L₁} {u v x₁ ε : L₁} {n : ℕ} {a β : K₁} {e α : ℕ}
    {W₁ W₂ : ValuationSubring L₁} (H : UnfoldedNodeGerm O₁ ϖ₁ P u v n x₁ a β e α ε W₁ W₂)
    (HB : NodeBranches O₁ ϖ₁ P (algebraMap O₁ L₁) u v n W₁ W₂)
    (hGs : NodeGerm O₁ ϖ₁ P v u n)
    (hint : ∀ s : ℚ, 0 < s → s < n → ∃ U : ValuationSubring L₁,
      IsMonomialPt O₁ (P : Set L₁) (algebraMap K₁ L₁ (ϖ₁ : K₁)) u s U)
    {Q : Subring L₂} {u' v' x₂ ε' : L₂} {n' : ℕ} {a' β' : K₂} {e' α' : ℕ}
    {W₁' W₂' : ValuationSubring L₂}
    (H' : UnfoldedNodeGerm O₂ ϖ₂ Q u' v' n' x₂ a' β' e' α' ε' W₁' W₂')
    (hx : algebraMap L₂ L₁ x₂ = x₁) (hQP : ∀ q ∈ Q, algebraMap L₂ L₁ q ∈ P)
    {ε'' : L₁} (hε : ε'' ∈ P) (hε' : ε''⁻¹ ∈ P) (hε0 : ε'' ≠ 0) {p r : ℕ} (hp : 1 ≤ p) :
    (algebraMap L₂ L₁ u' = ε'' * u ^ p * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ r → (e : ℚ) = e' * p) ∧
    (algebraMap L₂ L₁ u' = ε'' * v ^ p * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ r → False) := by
  letI : Algebra K₂ L₁ := ((algebraMap L₂ L₁).comp (algebraMap K₂ L₂)).toAlgebra
  haveI : IsScalarTower K₂ L₂ L₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hO₂Q : ∀ o : O₂, algebraMap K₂ L₂ (o : K₂) ∈ Q := H'.germ.algebraMap_mem
  have halg : ∀ k : K₂, IsAlgebraic K₁ (algebraMap K₂ L₁ k) := fun k ↦
    ((Algebra.IsAlgebraic.isAlgebraic (R := K) k).algHom
      ((IsScalarTower.toAlgHom K L₂ L₁).comp (IsScalarTower.toAlgHom K K₂ L₂))).tower_top K₁
  -- `ϖ₂ ^ e₂ = ζ ϖ₁ ^ e₁`
  set ζ : L₁ := algebraMap K₁ L₁ ((η₁ : O₁) : K₁) * (algebraMap K₂ L₁ ((η₂ : O₂) : K₂))⁻¹
  have hη₂0 : algebraMap K₂ L₁ ((η₂ : O₂) : K₂) ≠ 0 := by
    have : ((η₂ : O₂) : K₂) ≠ 0 := fun h ↦ η₂.ne_zero (Subtype.ext h)
    simp [this]
  have hη₁0 : algebraMap K₁ L₁ ((η₁ : O₁) : K₁) ≠ 0 := by
    have : ((η₁ : O₁) : K₁) ≠ 0 := fun h ↦ η₁.ne_zero (Subtype.ext h)
    simp [this]
  have hη₂inv : (algebraMap K₂ L₁ ((η₂ : O₂) : K₂))⁻¹ = algebraMap K₂ L₁ ((η₂⁻¹ : O₂ˣ) : K₂) := by
    rw [← map_inv₀]; congr 1
    exact (eq_inv_of_mul_eq_one_right (congrArg Subtype.val η₂.mul_inv)).symm
  have hη₁inv : (algebraMap K₁ L₁ ((η₁ : O₁) : K₁))⁻¹ = algebraMap K₁ L₁ ((η₁⁻¹ : O₁ˣ) : K₁) := by
    rw [← map_inv₀]; congr 1
    exact (eq_inv_of_mul_eq_one_right (congrArg Subtype.val η₁.mul_inv)).symm
  have hη₂P : ∀ o : O₂, algebraMap K₂ L₁ (o : K₂) ∈ P := fun o ↦ hQP _ (hO₂Q o)
  have hζ : ζ ∈ P := mul_mem (H.germ.algebraMap_mem _) (by rw [hη₂inv]; exact hη₂P _)
  have hζ' : ζ⁻¹ ∈ P := by
    rw [mul_inv, inv_inv, hη₁inv]
    exact mul_mem (H.germ.algebraMap_mem _) (hη₂P _)
  have hζ0 : ζ ≠ 0 := mul_ne_zero hη₁0 (inv_ne_zero hη₂0)
  have hbase : algebraMap K₂ L₁ (algebraMap K K₂ ϖ) = algebraMap K₁ L₁ (algebraMap K K₁ ϖ) := by
    change algebraMap L₂ L₁ (algebraMap K₂ L₂ (algebraMap K K₂ ϖ)) = _
    rw [← IsScalarTower.algebraMap_apply K K₂ L₂, ← IsScalarTower.algebraMap_apply K L₂ L₁,
      IsScalarTower.algebraMap_apply K K₁ L₁]
  have hζϖ : algebraMap K₂ L₁ (ϖ₂ : K₂) ^ e₂ = ζ * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ e₁ := by
    rw [hϖK₂, hϖK₁, map_mul, map_mul, map_pow, map_pow] at hbase
    simp only [ζ]
    field_simp
    rw [← hbase]
    ring
  have hϖ₂0 : algebraMap K₂ L₂ (ϖ₂ : K₂) ≠ 0 := by
    have : (ϖ₂ : K₂) ≠ 0 := fun h ↦ hϖ₂.ne_zero (Subtype.ext h)
    simpa using this
  have he₁0 : (e₁ : ℚ) ≠ 0 := by exact_mod_cast he₁.ne'
  have he₂0 : (e₂ : ℚ) ≠ 0 := by exact_mod_cast he₂.ne'
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := H.one_le_n; omega)
  -- the radius identity at an interior point
  have key : ∀ (w₁ w₂ : L₁) (hG : NodeGerm O₁ ϖ₁ P w₁ w₂ n) (s t : ℚ), 0 < t → t < n →
      ∀ U : ValuationSubring L₁,
      IsMonomialPt O₁ (P : Set L₁) (algebraMap K₁ L₁ (ϖ₁ : K₁)) u s U → 0 ≤ s → s ≤ n →
      IsMonomialPt O₁ (P : Set L₁) (algebraMap K₁ L₁ (ϖ₁ : K₁)) w₁ t U →
      algebraMap L₂ L₁ u' = ε'' * w₁ ^ p * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ r →
      (ordO O₁ ϖ₁ β + α + e * s) * e₂ =
        (ordO O₂ ϖ₂ β' + α') * e₁ + e' * ((r + p * t) * e₂) := by
    intro w₁ w₂ hG s t ht0 htn U hUs hs0 hsn hUt hu'
    have hU' := hG.isMonomialPt_comap hϖ₁ hϖ₂ hQP hO₂Q halg rfl hp hε hε' hε0 hu' he₁ he₂ hζ hζ'
      hζ0 hζϖ ht0 htn hUt
    have hs'0 : (0 : ℚ) ≤ (r + p * t) * e₂ / e₁ := by positivity
    have hs'n := hU'.le_of_mul_eq H'.germ.v_mem H'.germ.mul_eq hϖ₂0
    have h := rho_match hϖ₁ hϖ₂ he₁ he₂ hϖK₁ hϖK₂ H H' hx hs0 hsn hs'0 hs'n hUs hU'
    rw [div_eq_div_iff he₁0 he₂0] at h
    field_simp at h
    linear_combination h
  refine ⟨fun hu' ↦ ?_, fun hv' ↦ ?_⟩
  · have k : ∀ s : ℚ, 0 < s → s < n →
        (ordO O₁ ϖ₁ β + α + e * s) * e₂ = (ordO O₂ ϖ₂ β' + α') * e₁ + e' * ((r + p * s) * e₂) :=
      fun s hs0 hsn ↦ by
        obtain ⟨U, hU⟩ := hint s hs0 hsn
        exact key u v H.germ s s hs0 hsn U hU hs0.le hsn.le hU hu'
    have h₁ := k (n / 2) (by positivity) (by linarith [show (0 : ℚ) < n by positivity])
    have h₂ := k (n / 4) (by positivity) (by linarith [show (0 : ℚ) < n by positivity])
    have := slope_eq_of_two (c₀ := (ordO O₁ ϖ₁ β + α) * e₂) (c₁ := e * e₂)
      (d₀ := (ordO O₂ ϖ₂ β' + α') * e₁ + e' * r * e₂) (d₁ := e' * p * e₂) hn0
      (by linear_combination h₁) (by linear_combination h₂)
    have h3 : ((e : ℚ) - e' * p) * e₂ = 0 := by linear_combination this
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · exact absurd h he₂0
  · have k : ∀ s : ℚ, 0 < s → s < n →
        (ordO O₁ ϖ₁ β + α + e * s) * e₂ =
          (ordO O₂ ϖ₂ β' + α') * e₁ + e' * ((r + p * (n - s)) * e₂) :=
      fun s hs0 hsn ↦ by
        obtain ⟨U, hU⟩ := hint s hs0 hsn
        have hUv : IsMonomialPt O₁ (P : Set L₁) (algebraMap K₁ L₁ (ϖ₁ : K₁)) v (n - s) U :=
          (isMonomialPt_swap_iff HB.base HB.core HB.irred).2 (by simpa using hU)
        exact key v u hGs s (n - s) (by linarith) (by linarith) U hU hs0.le hsn.le hUv hv'
    have h₁ := k (n / 2) (by positivity) (by linarith [show (0 : ℚ) < n by positivity])
    have h₂ := k (n / 4) (by positivity) (by linarith [show (0 : ℚ) < n by positivity])
    have := slope_eq_of_two (c₀ := (ordO O₁ ϖ₁ β + α) * e₂) (c₁ := e * e₂)
      (d₀ := (ordO O₂ ϖ₂ β' + α') * e₁ + e' * (r + p * n) * e₂) (d₁ := -(e' * p * e₂)) hn0
      (by linear_combination h₁) (by linear_combination h₂)
    have h3 : ((e : ℚ) + e' * p) * e₂ = 0 := by linear_combination this
    have he : (1 : ℚ) ≤ e := by exact_mod_cast H.one_le_e
    have hpos : (0 : ℚ) < ((e : ℚ) + e' * p) * e₂ := by positivity
    linarith

end SemistableReduction
