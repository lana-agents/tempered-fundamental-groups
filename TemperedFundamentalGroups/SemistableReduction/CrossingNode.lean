/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CrossingStep

/-!
# The crossing step at a point of a component (Blueprint §10.3.8, CrossingX1, CX6)

`step`: the scheme form of `step_core`, see `CrossingStep`. `node_data` packages the germs at a
node of a split W-model without loops (`exists_nodeGerm`); `branch` and `branch_ne` say that each
component through a node has exactly one node coordinate as a unit, and distinct components
have distinct ones; `two_components` follows.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [Algebra O L] [IsScalarTower O K L] {x : L}
  {c : TemperedFundamentalGroups.ModelCode O} {j : Spec (CommRingCat.of L) ⟶ c.scheme}
  (hW : IsWModel O L x c j) {ϖ : O} (hϖ : Irreducible ϖ) (hsplit : HasSplitNodes ϖ c)
  (hloops : NoLoops c)

include hW hϖ hsplit hloops in
/-- **The germs at a node.** -/
theorem node_data {z : c.scheme} (hz : IsNodePt c z) :
    ∃ (P : Subring L) (a b : L) (m : ℕ), (P : Set L) = germs c j z ∧
      NodeCore P (algebraMap O L) (algebraMap O L ϖ) a b m ∧ IsLocalRing P ∧
      IsNoetherianRing P ∧ ∀ t ∈ P, ∀ M : ℕ, (∃ r ∈ P, t * r = algebraMap O L ϖ ^ M) →
        ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ, t = ε * algebraMap O L ϖ ^ α * a ^ e ∨
          t = ε * algebraMap O L ϖ ^ α * b ^ e := by
  obtain ⟨P, u, v, n, h, hn, -, hPg, ⟨hloc, -, hum, hvm⟩, -, -, -, hODP⟩ :=
    exists_nodeGerm hϖ hW hsplit hloops hz
  have hϖL : algebraMap O L ϖ = algebraMap K L (ϖ : K) := IsScalarTower.algebraMap_apply O K L ϖ
  have hι : (algebraMap K L).comp O.subtype = algebraMap O L :=
    RingHom.ext fun o ↦ (IsScalarTower.algebraMap_apply O K L o).symm
  have hnu : ∀ s (hs : s ∈ P), (⟨s, hs⟩ : P) ∈ maximalIdeal P → ∀ w ∈ P, s * w ≠ 1 :=
    fun s hs hm w hw h1 ↦ hm (isUnit_iff_exists_inv.2 ⟨⟨w, hw⟩, Subtype.ext h1⟩)
  have hcore := NodeCore.of_nodeGerm h hϖ (hnu u h.u_mem hum) (hnu v h.v_mem hvm)
  rw [hι, ← hϖL] at hcore
  refine ⟨P, u, v, n, hPg, hcore, hloc, hODP.isNoetherianRing, fun t ht M hM ↦ ?_⟩
  rw [hϖL] at hM ⊢
  exact hODP.divisor hϖ hn ht hM

include hW hϖ hloops in
/-- **Exactly one node coordinate is a unit on a component through a node.** -/
theorem branch {z : c.scheme} (hz : IsNodePt c z) {P : Subring L} {a b : L} {m : ℕ}
    (hPg : (P : Set L) = germs c j z) (hcore : NodeCore P (algebraMap O L) (algebraMap O L ϖ) a b m)
    [IsLocalRing P] {w : Set c.scheme} (hw : w ∈ components c) (hzw : z ∈ w)
    {V : ValuationSubring L} (hV : IsCentre j V (gp hw)) :
    (V.valuation a = 1 ∧ V.valuation b < 1) ∨ (V.valuation b = 1 ∧ V.valuation a < 1) := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hne, h₁, h₂⟩ := hloops z hz
  refine CrossingTarget.unit_or_unit (specializes_of_isWModel hW z) hPg hcore
    (fun f hf ↦ germs_le hW hV (gp_specializes hw hzw) f (hPg ▸ hf))
    (valuation_ϖ_lt_one hW hϖ (hw.2.1 (gp_mem hw)) hV) hV (gp_ne_of_two hw hw₁ hw₂ hne h₁ h₂)

include hW hϖ in
/-- **Distinct components through a node have distinct unit coordinates.** -/
theorem branch_ne {z : c.scheme} {P : Subring L} {a b : L} {m : ℕ}
    (hPg : (P : Set L) = germs c j z) (hcore : NodeCore P (algebraMap O L) (algebraMap O L ϖ) a b m)
    [IsLocalRing P] [IsNoetherianRing P] {w w' : Set c.scheme} (hw : w ∈ components c)
    (hw' : w' ∈ components c) (hzw : z ∈ w) (hzw' : z ∈ w') {V V' : ValuationSubring L}
    (hV : IsCentre j V (gp hw)) (hV' : IsCentre j V' (gp hw')) (ha : V.valuation a = 1)
    (hb : V.valuation b < 1) (ha' : V'.valuation a = 1) (hb' : V'.valuation b < 1) : w = w' := by
  have hy := specializes_of_isWModel hW z
  have hPV : P ≤ V.toSubring := fun f hf ↦ germs_le hW hV (gp_specializes hw hzw) f (hPg ▸ hf)
  have hPV' : P ≤ V'.toSubring := fun f hf ↦ germs_le hW hV' (gp_specializes hw' hzw') f (hPg ▸ hf)
  have := CrossingTarget.centre_eq_of_branch hy hPg hcore hPV hPV'
    (valuation_ϖ_lt_one hW hϖ (hw.2.1 (gp_mem hw)) hV) hb ha
    (valuation_ϖ_lt_one hW hϖ (hw'.2.1 (gp_mem hw')) hV') hb' ha' hV hV'
  rw [← closure_gp hw, ← closure_gp hw', this]

include hW hϖ hsplit hloops in
/-- **The crossing step.** -/
theorem step {v : Set c.scheme} (hv : v ∈ components c) {W : ValuationSubring L}
    (hWc : IsCentre j W (gp hv)) {t : L} {p : ℕ}
    (htW : W.valuation t = W.valuation (algebraMap O L ϖ) ^ p) {z : c.scheme} (hzv : z ∈ v)
    (htz : t ∈ germs c j z) {M : ℕ} (hM : ∃ r ∈ germs c j z, t * r = algebraMap O L ϖ ^ M)
    {R : ValuationSubring L} (hRz : IsCentre j R z)
    (hR : R.valuation (t / algebraMap O L ϖ ^ p) < 1) :
    IsNodePt c z ∧ ∃ (v' : Set c.scheme) (hv' : v' ∈ components c), v' ≠ v ∧ z ∈ v' ∧
      ∀ W' : ValuationSubring L, IsCentre j W' (gp hv') → ∃ p', p < p' ∧
        W'.valuation t = W'.valuation (algebraMap O L ϖ) ^ p' ∧
        ∀ R' : ValuationSubring L, IsCentre j R' z →
          R'.valuation (t / algebraMap O L ϖ ^ p')⁻¹ < 1 := by
  set ϖL := algebraMap O L ϖ
  have hy := specializes_of_isWModel hW z
  have hz : z ∈ Z c := hv.2.1 hzv
  have hgW : ∀ f ∈ germs c j z, f ∈ W := germs_le hW hWc (gp_specializes hv hzv)
  obtain ⟨hgR, -⟩ := (isCentre_iff_dominates c j hy R).1 hRz
  have hWϖ : W.valuation ϖL < 1 := valuation_ϖ_lt_one hW hϖ (hv.2.1 (gp_mem hv)) hWc
  have hϖ0 : ϖL ≠ 0 := by
    rw [show ϖL = algebraMap K L (ϖ : K) from IsScalarTower.algebraMap_apply O K L ϖ]
    exact (map_ne_zero _).2 fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hWϖ0 : W.valuation ϖL ≠ 0 := by simpa using hϖ0
  have ht0 : t ≠ 0 := fun h ↦ by
    rw [h, map_zero] at htW; exact pow_ne_zero _ hWϖ0 htW.symm
  -- `z` is not a smooth point
  have hs : ¬ IsSmoothPt c z := by
    intro hs
    obtain ⟨ε, hε, hεi, α, rfl⟩ := exists_eq_unit_mul_pow_of_smooth hW hϖ hz hs htz hM
    have hε0 : ε ≠ 0 := fun h ↦ ht0 (by rw [h, zero_mul])
    have hα : p = α := pow_inj hWϖ0 hWϖ (by
      rw [← htW, map_mul, valuation_unit hε0 (hgW _ hε) (hgW _ hεi), one_mul, map_pow])
    subst hα
    rw [mul_div_assoc, div_self (pow_ne_zero _ hϖ0), mul_one,
      valuation_unit hε0 (hgR hε) (hgR hεi)] at hR
    exact lt_irrefl _ hR
  have hnode : IsNodePt c z := ⟨hz, hs⟩
  refine ⟨hnode, ?_⟩
  obtain ⟨P, a, b, m, hPg, hcore, hloc, hnoeth, hdiv⟩ := node_data hW hϖ hsplit hloops hnode
  obtain ⟨w₁, hw₁, w₂, hw₂, hne, h₁, h₂⟩ := hloops z hnode
  obtain ⟨v', hv', hv'v, hzv'⟩ : ∃ v' ∈ components c, v' ≠ v ∧ z ∈ v' := by
    by_cases h : w₁ = v
    · exact ⟨w₂, hw₂, fun h' ↦ hne (h.trans h'.symm), h₂⟩
    · exact ⟨w₁, hw₁, h, h₁⟩
  refine ⟨v', hv', hv'v, hzv', fun W' hW'c ↦ ?_⟩
  have hgW' : ∀ f ∈ germs c j z, f ∈ W' := germs_le hW hW'c (gp_specializes hv' hzv')
  have htP : t ∈ P := by rw [← SetLike.mem_coe, hPg]; exact htz
  have hMP : ∃ r ∈ P, t * r = ϖL ^ M := by
    obtain ⟨r, hr, hr'⟩ := hM; exact ⟨r, by rw [← SetLike.mem_coe, hPg]; exact hr, hr'⟩
  obtain ⟨ε, hε, hεi, α, e, hte⟩ := hdiv t htP M hMP
  have hε0 : ε ≠ 0 := fun h ↦ ht0 (by rcases hte with h' | h' <;> rw [h', h] <;> ring)
  have hPW : (P : Set L) ⊆ W := fun f hf ↦ hgW f (hPg ▸ hf)
  have hPW' : (P : Set L) ⊆ W' := fun f hf ↦ hgW' f (hPg ▸ hf)
  have hPR : (P : Set L) ⊆ R := fun f hf ↦ hgR (hPg ▸ hf)
  have hdom : ∀ R' : ValuationSubring L, IsCentre j R' z → ∀ s ∈ P, (∀ w ∈ P, s * w ≠ 1) →
      R'.valuation s < 1 := fun R' hR' s hs hsu ↦
    ((isCentre_iff_dominates c j hy R').1 hR').2 s (hPg ▸ hs)
      (fun w hw ↦ hsu w (by rw [← SetLike.mem_coe, hPg]; exact hw))
  have hR'P : ∀ R' : ValuationSubring L, IsCentre j R' z → (P : Set L) ⊆ R' := fun R' hR' f hf ↦
    ((isCentre_iff_dominates c j hy R').1 hR').1 (hPg ▸ hf)
  rcases branch hW hϖ hloops hnode hPg hcore hv hzv hWc with ⟨hWa, hWb⟩ | ⟨hWb, hWa⟩
  · have hW'b : W'.valuation b = 1 := by
      rcases branch hW hϖ hloops hnode hPg hcore hv' hzv' hW'c with ⟨hW'a, hW'b⟩ | ⟨hW'b, -⟩
      · exact absurd (branch_ne hW hϖ hPg hcore hv hv' hzv hzv' hWc hW'c hWa hWb hW'a hW'b)
          hv'v.symm
      · exact hW'b
    obtain ⟨p', hpp', hW't, hR'⟩ := step_core hcore.one_le hcore.mul_eq hϖ0 hε0 hε hεi
      hcore.u_mem hte hPW hPW' hPR hWϖ hWa hW'b htW hR
    exact ⟨p', hpp', hW't, fun R' hR'c ↦ hR' R' (hR'P R' hR'c)
      (hdom R' hR'c b hcore.v_mem hcore.v_nonunit)⟩
  · have hW'a : W'.valuation a = 1 := by
      rcases branch hW hϖ hloops hnode hPg hcore hv' hzv' hW'c with ⟨hW'a, -⟩ | ⟨hW'b, hW'a⟩
      · exact hW'a
      · exact absurd (branch_ne hW hϖ hPg hcore.swap hv hv' hzv hzv' hWc hW'c hWb hWa hW'b hW'a)
          hv'v.symm
    obtain ⟨p', hpp', hW't, hR'⟩ := step_core hcore.one_le hcore.swap.mul_eq hϖ0 hε0 hε hεi
      hcore.v_mem hte.symm hPW hPW' hPR hWϖ hWb hW'a htW hR
    exact ⟨p', hpp', hW't, fun R' hR'c ↦ hR' R' (hR'P R' hR'c)
      (hdom R' hR'c a hcore.u_mem hcore.u_nonunit)⟩

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
