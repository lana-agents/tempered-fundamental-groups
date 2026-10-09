/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Orbicurve.Nullstellensatz
import TemperedFundamentalGroups.Orbicurve.Ring

/-!
# Stability of `ringOf W S` under affine automorphisms

Let `S` be a set of rational points of `W` containing `0`, stable under `P ↦ -P`, and mapped into
itself by an affine automorphism `g = (ε, m)` and by `g⁻¹`. Then `pullback W g` maps
`ringOf W S` (the coordinate ring of `W ∖ S`) into itself (`pullback_mem_ringOf`).

The coordinates of `g(genericPoint W)` lie in `ringOf W S` by the addition formula
(`coords_act_genericPoint_mem`). It remains to see that `pullback W g (x - x(P))` is a unit of
`ringOf W S` for every affine `P ∈ S`. This is the Nullstellensatz unit criterion applied in a
finitely generated subring `ringOfX W T` (`T` consisting of the `x`-coordinates of `m`,
`g⁻¹(P)`, `g⁻¹(-P)`): for a `k`-algebra map `χ : ringOfX W T → k̄`, the value of
`pullback W g (x - x(P))` at `χ` is `x(g(Q)) - x(P)` for the point `Q = (χ x, χ y)`, which avoids
`g⁻¹(±P)`.

For a subgroup `A ≤ AffAut W` with `IsAffStable S A` this gives the action of `A` on
`ringOf W S` by `k`-algebra automorphisms.
-/

universe u

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TemperedFundamentalGroups.Orbicurve

noncomputable section

variable {k : Type u} [Field k] [DecidableEq k] {W : WeierstrassCurve k} [W.IsElliptic]
  {T : Set k}

/-! ### The unit criterion -/

lemma false_of_pointOf_eq_bc {L : Type*} [Field L] [DecidableEq L] [Algebra k L]
    (χ : ringOfX W T →ₐ[k] L) {Q : W.toAffine.Point} (hQ : Q ≠ 0 → xOf Q ∈ T)
    (h : pointOf χ = bc W L Q) : False := by
  have hQ0 : Q ≠ 0 := fun h0 => pointOf_ne_zero χ (by rw [h, h0, map_zero])
  apply xOf_pointOf_ne χ (hQ hQ0)
  rw [h, xOf_bc]

/-- The unit criterion in a finitely generated `ringOfX W T`. -/
theorem isUnit_xR_sub_of_finite (hT : T.Finite) (g : AffAut W) (hm0 : g.m ≠ 0)
    (hm : xOf g.m ∈ T) {P : W.toAffine.Point} (hP : P ≠ 0)
    (h₁ : g⁻¹ • P ≠ 0 → xOf (g⁻¹ • P) ∈ T) (h₂ : g⁻¹ • (-P) ≠ 0 → xOf (g⁻¹ • (-P)) ∈ T) :
    IsUnit (g.xR hm - algebraMap k (ringOfX W T) (xOf P)) := by
  classical
  haveI : Algebra.FiniteType k (ringOfX W T) :=
    (Subalgebra.fg_iff_finiteType (ringOfX W T)).mp (ringOfX_fg hT)
  refine isUnit_of_forall_algHom_ne_zero (k := k) fun χ hχ => ?_
  obtain ⟨h0, hx, -⟩ := act_pointOf χ g hm0 hm
  rw [map_sub, AlgHom.commutes, ← hx, sub_eq_zero] at hχ
  have hbc : bc W (AlgebraicClosure k) P ≠ 0 := by rwa [Ne, bc_eq_zero_iff]
  have hpm : g.act _ (pointOf χ) = bc W _ P ∨ g.act _ (pointOf χ) = -bc W _ P := by
    rw [eq_some_xOf_yOf h0, eq_some_xOf_yOf hbc]
    exact Point.X_eq_iff.mp (by rw [hχ, xOf_bc])
  rcases hpm with hpm | hpm
  · refine false_of_pointOf_eq_bc χ h₁ ?_
    rw [AffAut.bc_smul, ← hpm, AffAut.act_inv_act]
  · refine false_of_pointOf_eq_bc χ h₂ ?_
    rw [AffAut.bc_smul, map_neg, ← hpm, AffAut.act_inv_act]

omit [DecidableEq k] [W.IsElliptic] in
lemma inv_coe_mem_of_isUnit {B : Subalgebra k (funField W)} {u : B} (hu : IsUnit u) :
    (u : funField W)⁻¹ ∈ B := by
  obtain ⟨v, rfl⟩ := hu
  have : ((v⁻¹ : Bˣ) : funField W) * (v : B) = 1 := congrArg Subtype.val v.inv_mul
  rw [← eq_inv_of_mul_eq_one_left this]
  exact Subtype.prop _

/-- For `g = (ε, m)` and an affine rational point `P` such that the `x`-coordinates of `m`,
`g⁻¹(P)` and `g⁻¹(-P)` (when affine) lie in `T`, the function `pullback W g (x - x(P))` is a
unit of `ringOfX W T`. -/
theorem inv_pullback_mem (g : AffAut W) (hm : g.m ≠ 0 → xOf g.m ∈ T) {P : W.toAffine.Point}
    (hP : P ≠ 0) (h₁ : g⁻¹ • P ≠ 0 → xOf (g⁻¹ • P) ∈ T)
    (h₂ : g⁻¹ • (-P) ≠ 0 → xOf (g⁻¹ • (-P)) ∈ T) :
    (pullback W g (xGen W - algebraMap k (funField W) (xOf P)))⁻¹ ∈ ringOfX W T := by
  rw [map_sub, AlgHom.commutes, pullback_xGen, ← pointOf_val (T := T)]
  by_cases hm0 : g.m = 0
  · obtain ⟨-, hx, -⟩ := act_pointOf_of_m_eq_zero (ringOfX W T).val g hm0
    have hginv : g⁻¹ • P = g.ε⁻¹ • P := by
      rw [AffAut.smul_def, AffAut.inv_ε, AffAut.inv_m, hm0, smul_zero, neg_zero, add_zero]
    have hgP : g⁻¹ • P ≠ 0 := by
      rw [hginv]
      exact units_smul_ne_zero _ hP
    have hT := h₁ hgP
    rw [hginv, xOf_units_smul] at hT
    rw [hx]
    exact inv_mem_ringOfX hT
  · set T' : Set k := {a ∈ T | a = xOf g.m ∨ a = xOf (g⁻¹ • P) ∨ a = xOf (g⁻¹ • (-P))}
    have hT'T : T' ⊆ T := fun a ha => ha.1
    have hT' : T'.Finite := (Set.toFinite {xOf g.m, xOf (g⁻¹ • P), xOf (g⁻¹ • (-P))}).subset
      fun a ha => by simpa using ha.2
    have hmT' : xOf g.m ∈ T' := ⟨hm hm0, Or.inl rfl⟩
    have hu := isUnit_xR_sub_of_finite hT' g hm0 hmT' hP
      (fun h => ⟨h₁ h, Or.inr (Or.inl rfl)⟩) (fun h => ⟨h₂ h, Or.inr (Or.inr rfl)⟩)
    obtain ⟨-, hx, -⟩ := act_pointOf (ringOfX W T').val g hm0 hmT'
    have hmem := inv_coe_mem_of_isUnit hu
    rw [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, ← Subalgebra.coe_val, ← hx,
      pointOf_val] at hmem
    rw [pointOf_val]
    exact ringOfX_mono hT'T hmem

/-! ### Stability -/

/-- If `S` contains `0`, is stable under negation and is mapped into itself by `g` and `g⁻¹`,
then the pullback along `g` preserves `ringOf W S`. -/
theorem pullback_mem_ringOf {S : Set W.toAffine.Point} (h0 : 0 ∈ S)
    (hneg : ∀ P ∈ S, -P ∈ S) {g : AffAut W} (hg : ∀ P ∈ S, g • P ∈ S)
    (hg' : ∀ P ∈ S, g⁻¹ • P ∈ S) {f : funField W} (hf : f ∈ ringOf W S) :
    pullback W g f ∈ ringOf W S := by
  have hm : g.m ≠ 0 → xOf g.m ∈ xSet W S := fun hm0 => by
    have := hg 0 h0
    rw [AffAut.smul_def, smul_zero, zero_add] at this
    exact xOf_mem_xSet this hm0
  suffices ringOf W S ≤ (ringOf W S).comap (pullback W g) from this hf
  refine Algebra.adjoin_le ?_
  rintro _ ((rfl | rfl) | ⟨a, ⟨P, ⟨hPS, hP0⟩, rfl⟩, rfl⟩)
  · exact pullback_xGen_mem g hm
  · exact pullback_yGen_mem g hm
  · rw [SetLike.mem_coe, Subalgebra.mem_comap, map_inv₀]
    exact inv_pullback_mem g hm hP0 (fun h => xOf_mem_xSet (hg' P hPS) h)
      (fun h => xOf_mem_xSet (hg' _ (hneg P hPS)) h)

/-- A set `S` of rational points is *stable* under a subgroup `A` of affine automorphisms if it
contains `0`, is stable under negation, and is mapped into itself by every element of `A`. Then
`W ∖ S` is stable under `A`, and `A` acts on its coordinate ring `ringOf W S`. -/
class IsAffStable (S : Set W.toAffine.Point) (A : Subgroup (AffAut W)) : Prop where
  zero_mem : (0 : W.toAffine.Point) ∈ S
  neg_mem : ∀ P ∈ S, -P ∈ S
  smul_mem : ∀ g ∈ A, ∀ P ∈ S, g • P ∈ S

variable (S : Set W.toAffine.Point) (A : Subgroup (AffAut W)) [IsAffStable S A]

lemma smul_mem_ringOf (g : A) {f : funField W} (hf : f ∈ ringOf W S) :
    (g : AffAut W) • f ∈ ringOf W S := by
  rw [smul_funField_def]
  refine pullback_mem_ringOf (IsAffStable.zero_mem (A := A)) (IsAffStable.neg_mem (A := A))
    (IsAffStable.smul_mem _ (A.inv_mem g.2)) (fun P hP => ?_) hf
  rw [inv_inv]
  exact IsAffStable.smul_mem _ g.2 P hP

/-- The action of a subgroup `A` of affine automorphisms on the coordinate ring of `W ∖ S`, for
`S` stable under `A`. -/
instance : MulSemiringAction A (ringOf W S) where
  smul g r := ⟨(g : AffAut W) • (r : funField W), smul_mem_ringOf S A g r.2⟩
  one_smul r := Subtype.ext (one_smul (AffAut W) (r : funField W))
  mul_smul g h r := Subtype.ext (mul_smul (g : AffAut W) (h : AffAut W) (r : funField W))
  smul_zero g := Subtype.ext (smul_zero (g : AffAut W))
  smul_add g r s := Subtype.ext (smul_add (g : AffAut W) (r : funField W) s)
  smul_one g := Subtype.ext (smul_one (g : AffAut W))
  smul_mul g r s := Subtype.ext (smul_mul' (g : AffAut W) (r : funField W) s)

@[simp] lemma coe_smul_ringOf (g : A) (r : ringOf W S) :
    ((g • r : ringOf W S) : funField W) = (g : AffAut W) • (r : funField W) := rfl

instance : SMulCommClass A k (ringOf W S) :=
  ⟨fun g c r => Subtype.ext (smul_comm (g : AffAut W) c (r : funField W))⟩

end

end TemperedFundamentalGroups.Orbicurve
