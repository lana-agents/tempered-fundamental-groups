/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeRecognition
import TemperedFundamentalGroups.SemistableReduction.AffineTwist

/-!
# Exhausting discs

Blueprint §9.10, L3, R3 ([AW, Def. `exhaustdef`], [KA, Def. 1.23] over `C`, valuative form). Let
`R' = Rint c F'` be the integral closure of the node chart `O_C[x, c/x]` (`0 < |c| < 1`) in `F'`.

* `outerBranches P'`, `innerBranches P'`: the branches through a point `P'` of `R'` over the node,
  i.e. the zeros `Q` of `x̄` on the residue curves of the extensions `v` of the outer Gauss point
  `w_{0,1}` (resp. the zeros of `(c/x)‾` on the residue curves of the extensions of the inner Gauss
  point `w_{0,|c|}`, seen through the inversion `Inv c F'`) whose point is `P'`;
* **`IsNodeODP P'`**: `P'` is an ordinary double point of the special fibre over `C`: exactly one
  outer and one inner branch, and the local ring at `P'` reaches the fibre product
  `{(a, b) ∈ O_{Q₁} × O_{Q₂} | a(Q₁) = b(Q₂)}` of the two branches exactly (`δ = 1`, `m = 2`);
* **`isNodeODP_of_params`** (recognition, [KA, Lemma 1.30]): one outer and one inner branch with
  parameters `u', v' ∈ R'` (`ρ₂ u' = 0 = ρ₁ v'`, uniformizers at `Q₁`, `Q₂`) ⇒ `IsNodeODP P'`;
* **`IsExhausting a c c'`** (R3): for the residue class `U = {|x - a| < |c|}` of `w_{a,|c|}` and the
  closed disc `D = {|t| ≤ |c'|}`, `t = (x - a) / c`, the preimage of the annulus `U ∖ D` is a
  disjoint union of open annuli: in the normalization of the node chart `O_C[t, c'/t]` of the
  model `{w_{a,|c|}, w_{a,|c c'|}}` (through the twist `AffineTwist.Aff a c`), every point over the
  node is an ordinary double point.
-/

open WithZero

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

variable {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)

variable (C F') in
/-- An outer branch: an extension `v` of `w_{0,1}` and a zero of `x̄` on `κ(v)`. -/
abbrev OuterBranch : Type _ :=
  Σ v : Ext C F', {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField v.1.valuationSubring) //
    Q ∈ zeros 𝓀 (red C (xF C F') v)}

/-- The outer branches through a point `P'` of `R'`. -/
def outerBranches (P' : Ideal (Rint c F')) : Set (OuterBranch C F') :=
  {b | placeIdeal hc b.1 b.2.2 = P'}

/-- The inner branches through a point `P'` of `R'` (outer branches of the inversion). -/
def innerBranches (P' : Ideal (Rint c F')) : Set (OuterBranch C (Inv c hc0 F')) :=
  {b | placeIdeal hc b.1 b.2.2 = P'.comap (rintEquiv hc0).symm.toRingHom}

/-- **Ordinary double point over `C`** at a point `P'` of `R'` over the node: one outer branch
`(v₁, Q₁)`, one inner branch `(w₂, Q₂)`, and the local ring reaches the fibre product of the two
branches exactly. -/
def IsNodeODP (P' : Ideal (Rint c F')) : Prop :=
  ∃ b₁ : OuterBranch C F', ∃ b₂ : OuterBranch C (Inv c hc0 F'),
    outerBranches hc P' = {b₁} ∧ innerBranches hc hc0 P' = {b₂} ∧
    ∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b →
      ∃ y s : Rint c F', s ∉ P' ∧ redHom hc b₁.1 y = a * redHom hc b₁.1 s ∧
        redHomInv hc hc0 b₂.1 y = b * redHomInv hc hc0 b₂.1 s

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Recognition of ordinary double points** ([KA, Lemma 1.30], valuative form over `C`): a point
with exactly one outer branch `(v₁, Q₁)` and one inner branch `(w₂, Q₂)`, and parameters
`u', v' ∈ R'` (`ρ₂ u' = 0`, `ρ₁ v' = 0`, `ρ₁ u'`, `ρ₂ v'` uniformizers at `Q₁`, `Q₂`), is an
ordinary double point. -/
theorem isNodeODP_of_params {P' : Ideal (Rint c F')} {b₁ : OuterBranch C F'}
    {b₂ : OuterBranch C (Inv c hc0 F')} (h₁ : outerBranches hc P' = {b₁})
    (h₂ : innerBranches hc hc0 P' = {b₂}) {u' v' : Rint c F'}
    (hu₁ : b₁.2.1.valuation (redHom hc b₁.1 u') = exp (-1))
    (hu₂ : redHomInv hc hc0 b₂.1 u' = 0) (hv₁ : redHom hc b₁.1 v' = 0)
    (hv₂ : b₂.2.1.valuation (redHomInv hc hc0 b₂.1 v') = exp (-1)) :
    IsNodeODP hc hc0 P' := by
  obtain ⟨v₁, Q₁, hQ₁⟩ := b₁
  obtain ⟨w₂, Q₂, hQ₂⟩ := b₂
  have hP₁ : placeIdeal hc v₁ hQ₁ = P' := by
    have : (⟨v₁, Q₁, hQ₁⟩ : OuterBranch C F') ∈ outerBranches hc P' := by rw [h₁]; rfl
    exact this
  have hP₂ : placeIdeal hc w₂ hQ₂ = P'.comap (rintEquiv hc0).symm.toRingHom := by
    have : (⟨w₂, Q₂, hQ₂⟩ : OuterBranch C (Inv c hc0 F')) ∈ innerBranches hc hc0 P' := by
      rw [h₂]; rfl
    exact this
  have hoth₁ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v₁)), R ≠ Q₁ →
      placeIdeal hc v₁ hR ≠ placeIdeal hc v₁ hQ₁ := by
    intro R hR hne heq
    have : (⟨v₁, R, hR⟩ : OuterBranch C F') ∈ outerBranches hc P' := by
      change placeIdeal hc v₁ hR = P'
      rw [heq, hP₁]
    rw [h₁, Set.mem_singleton_iff] at this
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact hne (congrArg Subtype.val this)
  have hoth₂ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂)), R ≠ Q₂ →
      placeIdeal hc w₂ hR ≠ placeIdeal hc w₂ hQ₂ := by
    intro R hR hne heq
    have : (⟨w₂, R, hR⟩ : OuterBranch C (Inv c hc0 F')) ∈ innerBranches hc hc0 P' := by
      change placeIdeal hc w₂ hR = _
      rw [heq, hP₂]
    rw [h₂, Set.mem_singleton_iff] at this
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact hne (congrArg Subtype.val this)
  subst hP₁
  exact ⟨⟨v₁, Q₁, hQ₁⟩, ⟨w₂, Q₂, hQ₂⟩, h₁, h₂, fun a ha b hb hab ↦
    exists_fp_of_params hc hc0 hp hp1 v₁ hQ₁ w₂ hQ₂ hP₂ hoth₁ hoth₂ hu₁ hu₂ hv₁ hv₂ ha hb hab⟩

end GaussTube

namespace AffineTwist

open GaussTube

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

/-- **Exhausting discs** (R3). For the residue class `U = {|x - a| < |c|}` of `w_{a,|c|}` and the
closed disc `D = {|t| ≤ |c'|}` (`t = (x - a) / c`, `0 < |c'| < 1`), `D` is *exhausting* if every
point over the node of the normalization of the node chart `O_C[t, c'/t]` (of the model
`{w_{a,|c|}, w_{a,|c c'|}}`) is an ordinary double point over `C`: the preimage of the annulus
`U ∖ D` is a disjoint union of open annuli. -/
def IsExhausting (a : C) {c : C} (hc0 : c ≠ 0) {c' : C} (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0)
    (F' : Type*) [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
    [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] : Prop :=
  ∀ P' : Ideal (Rint c' (Aff a c hc0 F')), P'.IsMaximal →
    P'.comap (algebraMap (nodeRing c') (Rint c' (Aff a c hc0 F'))) = tubeIdeal c' →
      IsNodeODP hc' hc0' P'

end AffineTwist

end SemistableReduction
