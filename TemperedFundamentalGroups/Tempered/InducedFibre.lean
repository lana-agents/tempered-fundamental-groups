/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.InducedHom

/-!
# Fibres of induced tempered coverings (Blueprint §11, F7′)

A geometric point `t` of the induced algebra `Π x : S, B'^{(α x)}` factors through exactly one
copy `x` (`IndData.exists_ev`, `IndData.eq_of_comp_ev`). The fibre of `X'` embeds into the fibre
of the induced covering as the fibre elements on the copy `1` (`IndData.ι`, `IndData.ι_injective`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {A' : Type u} [Group A'] [MulSemiringAction A' R] {μ : OrbMap R A R A'}

namespace IndData

variable {X' : TempObj O R A'} (D : IndData μ X')

/-! ### Components -/

/-- The idempotent of the copy `x`. -/
def idem (x : D.S) : D.level.B := D.E.symm (Pi.single (M := fun y => TwAlg X'.Lv.L.B (D.α y)) x 1)

/-- The element of the induced algebra supported on the copy `x` with value `b`. -/
def single (x : D.S) (b : X'.Lv.L.B) : D.level.B :=
  D.E.symm (Pi.single (M := fun y => TwAlg X'.Lv.L.B (D.α y)) x b)

lemma ev_single (x y : D.S) (b : X'.Lv.L.B) : D.ev y (D.single x b) = if y = x then b else 0 := by
  rw [ev_apply, single, AlgEquiv.apply_symm_apply]
  by_cases h : y = x
  · subst h
    rw [if_pos rfl, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne h]
    rfl

lemma ev_single_self (x : D.S) (b : X'.Lv.L.B) : D.ev x (D.single x b) = b := by
  rw [ev_single, if_pos rfl]

lemma idem_eq (x : D.S) : D.idem x = D.single x 1 := rfl

lemma sum_idem : ∑ x, D.idem x = 1 := by
  refine D.ext_ev fun y => ?_
  rw [map_sum, map_one, Finset.sum_eq_single y]
  · rw [idem_eq, ev_single_self]
  · intro x _ hx
    rw [idem_eq, ev_single, if_neg (Ne.symm hx)]
  · intro h
    exact absurd (Finset.mem_univ y) h

lemma idem_mul (x : D.S) (y : D.level.B) : D.idem x * y = D.single x (D.ev x y) := by
  refine D.ext_ev fun z => ?_
  rw [map_mul, idem_eq, ev_single, ev_single]
  split_ifs with h
  · subst h
    rw [one_mul]
  · rw [zero_mul]

lemma single_mul (x : D.S) (a b : X'.Lv.L.B) : D.single x (a * b) = D.single x a * D.single x b := by
  refine D.ext_ev fun z => ?_
  rw [map_mul, ev_single, ev_single, ev_single]
  split_ifs <;> simp

lemma single_add (x : D.S) (a b : X'.Lv.L.B) : D.single x (a + b) = D.single x a + D.single x b := by
  refine D.ext_ev fun z => ?_
  rw [map_add, ev_single, ev_single, ev_single]
  split_ifs <;> simp

variable {Ω : Type u} [Field Ω]

/-- The ring map on the copy `x` of a ring map `t` with `t (idem x) = 1`. -/
def onCopy (t : D.level.B →+* Ω) (x : D.S) (hx : t (D.idem x) = 1) : X'.Lv.L.B →+* Ω where
  toFun b := t (D.single x b)
  map_one' := hx
  map_mul' a b := by rw [single_mul, map_mul]
  map_zero' := by
    rw [show D.single x 0 = 0 from D.ext_ev fun z => by rw [ev_single, map_zero]; simp, map_zero]
  map_add' a b := by rw [single_add, map_add]

lemma onCopy_ev (t : D.level.B →+* Ω) (x : D.S) (hx : t (D.idem x) = 1) (y : D.level.B) :
    D.onCopy t x hx (D.ev x y) = t y := by
  change t (D.single x (D.ev x y)) = t y
  rw [← idem_mul, map_mul, hx, one_mul]

/-- **A geometric point of the induced algebra lies on one copy.** -/
lemma exists_idem (t : D.level.B →+* Ω) : ∃ x, t (D.idem x) = 1 := by
  have hid : ∀ x, t (D.idem x) = 0 ∨ t (D.idem x) = 1 := fun x => by
    have h : D.idem x * D.idem x = D.idem x := by
      rw [idem_mul, idem_eq, ev_single_self]
    have := congrArg t h
    rw [map_mul] at this
    rcases mul_eq_zero.1 (show t (D.idem x) * (t (D.idem x) - 1) = 0 by
      rw [mul_sub, this, mul_one, sub_self]) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.1 h1)
  by_contra hne
  push Not at hne
  have hsum := congrArg t D.sum_idem
  rw [map_sum, map_one, Finset.sum_eq_zero fun x _ => (hid x).resolve_right (hne x)] at hsum
  exact zero_ne_one hsum

lemma eq_of_comp_ev {x y : D.S} {t₀ t₁ : X'.Lv.L.B →+* Ω}
    (h : t₀.comp (D.ev x) = t₁.comp (D.ev y)) : x = y := by
  by_contra hxy
  have := RingHom.congr_fun h (D.idem x)
  simp only [RingHom.comp_apply, idem_eq, ev_single_self, ev_single, if_neg (Ne.symm hxy),
    map_one, map_zero] at this
  exact one_ne_zero this

/-! ### The fibre of `X'` in the fibre of the induced covering -/

variable (hX : IndFaithful X') [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma point_comp_ev₁ (t : X'.Lv.L.B →ₐ[R] Ω) :
    (D.lv hX).point (t.comp D.ev₁) = X'.Lv.point t ≫ D.inc 1 := by
  rw [Level.point, Level.point, Category.assoc, ← specMap_ev_j]
  change Spec.map (CommRingCat.ofHom ((t : X'.Lv.L.B →+* Ω).comp (D.ev 1))) ≫ D.j = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

lemma sp_comp_ev₁ (t : X'.Lv.L.B →ₐ[R] Ω) :
    ((D.lv hX).sp V hV (t.comp D.ev₁)).1 = D.inc 1 (X'.Lv.sp V hV t).1 := by
  unfold Level.sp
  rw [← coe_sp_comp (hV := hV) (D.inc 1) (D.inc_toSpec 1)]
  congr 2
  exact D.point_comp_ev₁ hX t

/-- The inclusion of the copy `1` on special fibres. -/
def inc₁S : X'.Lv.Z → (D.lv hX).Z := specialFibreMap (D.inc 1) (D.inc_toSpec 1)

lemma inc₁S_coe (z : X'.Lv.Z) : (D.inc₁S hX z).1 = D.inc 1 z.1 := coe_specialFibreMap _ _ _

lemma foldS_inc₁S (z : X'.Lv.Z) : D.foldS hX (D.inc₁S hX z) = z := by
  apply Subtype.ext
  rw [coe_foldS, inc₁S_coe, ← Scheme.Hom.comp_apply, inc_fold]
  rfl

/-- The inclusion of `P'` as the copy `1` of the induced covering space. -/
def incP (p : X'.P.carrier) : (D.obj hX).P.carrier :=
  CoveringCode.pullbackLiftFun X'.P (ψ := D.foldS hX) (fun p : X'.P.carrier => D.inc₁S hX p.1.1) id
    (fun p => (D.foldS_inc₁S hX p.1.1).symm) p

lemma incP_fst (p : X'.P.carrier) : (D.incP hX p).1.1 = D.inc₁S hX p.1.1 := rfl

lemma pullbackPt_incP (p : X'.P.carrier) :
    CoveringCode.pullbackPt X'.P (D.foldS hX) (D.incP hX p) = p :=
  CoveringCode.pullbackPt_liftFun _ _ _ _ _

lemma continuous_incP : Continuous (D.incP hX) :=
  CoveringCode.continuous_pullbackLiftFun X'.P (ψ := D.foldS hX)
    (fun p => (D.foldS_inc₁S hX p.1.1).symm)
    ((continuous_specialFibreMap _ _).comp X'.P.continuous_proj) continuous_id

/-- The inclusion of pairs `(t, p)`. -/
def ιPre (q : TempObj.PreFibre Ω V hV X') : TempObj.PreFibre Ω V hV (D.obj hX) :=
  ⟨(q.1.1.comp D.ev₁, D.incP hX q.1.2), by
    change ((D.inc₁S hX q.1.2.1.1).1 : D.c.scheme) = _
    rw [inc₁S_coe, q.2]
    exact (D.sp_comp_ev₁ hX V hV q.1.1).symm⟩

lemma equivT_mem_H0 (k : X'.Lv.L.H0) :
    D.equivT hX (D.β k, k) ∈ D.level.H0 := by
  rw [FiniteLevel.mem_H0, equivT_apply, homT_a, D.hβ, FiniteLevel.mem_H0.1 k.2, map_one]

/-- The element `(β k, k) ∈ H⁰` for `k ∈ H'⁰`. -/
def h0 (k : X'.Lv.L.H0) : (D.obj hX).Lv.L.H0 := ⟨D.equivT hX (D.β k, k), D.equivT_mem_H0 hX k⟩

lemma ev₁_equivT_symm (k : X'.Lv.L.H) (y : D.level.B) :
    D.ev 1 (((D.equivT hX (D.β k, k) : D.level.H) : SemilinearAut R A D.level.B).σ.symm y) =
      (k : SemilinearAut R A' X'.Lv.L.B).σ.symm (D.ev 1 y) := by
  rw [ev_equivT_symm]
  congr 2
  group

lemma inc₁S_ρs (k : X'.Lv.L.H) (z : X'.Lv.Z) :
    (D.lv hX).ρs (D.equivT hX (D.β k, k)) (D.inc₁S hX z) = D.inc₁S hX (X'.Lv.ρs k z) := by
  apply Subtype.ext
  rw [Level.ρs_apply, inc₁S_coe, inc₁S_coe, Level.ρs_apply]
  change D.actHom ((D.equivT hX).symm (D.equivT hX (D.β k, k))) (D.inc 1 z.1) = _
  rw [MulEquiv.symm_apply_apply, ← Scheme.Hom.comp_apply, inc_actHom, Scheme.Hom.comp_apply]
  congr 2
  group

lemma act_incP (k : X'.Lv.L.H) (p : X'.P.carrier) :
    (D.obj hX).P.act (D.equivT hX (D.β k, k)) (D.incP hX p) = D.incP hX (X'.P.act k p) := by
  refine CoveringCode.pullback_ext X'.P (D.foldS hX) ?_ ?_
  · change (D.lv hX).ρs _ (D.inc₁S hX p.1.1) = D.inc₁S hX (X'.P.act k p).1.1
    rw [inc₁S_ρs, X'.P.act_fst]
  · change (X'.P.act (D.toH' hX _) (CoveringCode.pullbackPt X'.P (D.foldS hX) (D.incP hX p))).1.2
      = (X'.P.act k p).1.2
    rw [toH'_equivT, pullbackPt_incP]

lemma ιPre_smul (k : X'.Lv.L.H0) (q : TempObj.PreFibre Ω V hV X') :
    D.ιPre hX V hV (k • q) = D.h0 hX k • D.ιPre hX V hV q := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · ext y
    change (FiniteLevel.fibreAct Ω X'.Lv.L k q.1.1) (D.ev 1 y) =
      q.1.1 (D.ev 1 (((D.equivT hX (D.β k, k) : D.level.H) :
        SemilinearAut R A D.level.B).σ.symm y))
    rw [ev₁_equivT_symm, FiniteLevel.fibreAct_apply]
  · exact (D.act_incP hX (k : X'.Lv.L.H) q.1.2).symm

/-- **The inclusion of fibres** `F'(X') → F(Ind X')` (the copy `1`). -/
def ι : TempObj.Fibre Ω V hV X' → TempObj.Fibre Ω V hV (D.obj hX) :=
  Quotient.map (D.ιPre hX V hV) fun q q' ⟨g, hg⟩ => by
    rw [← hg, ιPre_smul]
    exact ⟨_, rfl⟩

lemma ι_mk (q : TempObj.PreFibre Ω V hV X') :
    D.ι hX V hV (Quotient.mk'' q) = Quotient.mk'' (D.ιPre hX V hV q) := rfl

lemma ev_single_one (b : X'.Lv.L.B) : D.ev 1 (D.single 1 b) = b := D.ev_single_self 1 b

/-- Elements of `H⁰` of the induced level. -/
lemma equivT_symm_mem_H0 {g : D.level.H} (hg : g ∈ D.level.H0) :
    D.α ((D.equivT hX).symm g).1 = 1 := by
  rw [← homT_a, homT_equivT_symm]
  exact FiniteLevel.mem_H0.1 hg

/-- **`ι` is injective.** -/
lemma ι_injective (hα : Function.Injective μ.α) : Function.Injective (D.ι hX V hV) := by
  intro x₁ x₂ h
  induction x₁ using Quotient.inductionOn with | h q₁ =>
  induction x₂ using Quotient.inductionOn with | h q₂ =>
  rw [ι_mk, ι_mk, Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  set t := (D.equivT hX).symm g.1 with ht
  have hgt : g.1 = D.equivT hX t := by rw [ht, MulEquiv.apply_symm_apply]
  have hpt : ∀ y, q₂.1.1 (D.ev 1
      (((D.equivT hX t : D.level.H) : SemilinearAut R A D.level.B).σ.symm y)) =
      q₁.1.1 (D.ev 1 y) := fun y => by
    rw [← hgt]
    exact congrArg (fun q : TempObj.PreFibre Ω V hV (D.obj hX) => q.1.1 y) hg
  simp_rw [ev_equivT_symm] at hpt
  have hcomp : ((q₂.1.1 : X'.Lv.L.B →+* Ω).comp
      ((t.2 : SemilinearAut R A' X'.Lv.L.B).σ.symm : X'.Lv.L.B →+* X'.Lv.L.B)).comp
        (D.ev (t.1 * 1 * (D.β t.2)⁻¹)) = (q₁.1.1 : X'.Lv.L.B →+* Ω).comp (D.ev 1) :=
    RingHom.ext hpt
  have hs := D.eq_of_comp_ev hcomp
  rw [mul_one, mul_inv_eq_one] at hs
  have hk : (t.2 : SemilinearAut R A' X'.Lv.L.B).a = 1 := by
    apply hα
    rw [← D.hβ, ← hs, map_one]
    exact D.equivT_symm_mem_H0 hX g.2
  refine Quotient.sound ⟨⟨t.2, FiniteLevel.mem_H0.2 hk⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
  · ext b
    have := hpt (D.single 1 b)
    rw [hs, mul_one, mul_inv_cancel, ev_single_one] at this
    exact this
  · have h2 := congrArg (fun q : TempObj.PreFibre Ω V hV (D.obj hX) =>
      CoveringCode.pullbackPt X'.P (D.foldS hX) q.1.2) hg
    change CoveringCode.pullbackPt X'.P (D.foldS hX)
      (CoveringCode.pullbackActFun X'.P (D.toH' hX) (D.foldS_ρs hX) g.1
        (D.incP hX q₂.1.2)) =
        CoveringCode.pullbackPt X'.P (D.foldS hX) (D.incP hX q₁.1.2) at h2
    rw [CoveringCode.pullbackPt_actFun, pullbackPt_incP, pullbackPt_incP, hgt, toH'_equivT] at h2
    exact h2

section Natural

variable {X₁ X₂ : TempObj O R A'} (D₁ : IndData μ X₁) (D₂ : IndData μ X₂)
  (hX₁ : IndFaithful X₁) (hX₂ : IndFaithful X₂) (m : X₁ ⟶ X₂) (θ : D₁.S →* D₂.S)
  (hθα : ∀ x, D₂.α (θ x) = D₁.α x) (hθβ : ∀ k, θ (D₁.β k) = D₂.β (m.φ.r k))

lemma ιPre_natural (q : TempObj.PreFibre Ω V hV X₁) :
    D₂.ιPre hX₂ V hV (TempObj.preMap V hV m q) =
      TempObj.preMap V hV (hom D₁ D₂ hX₁ hX₂ m θ hθα hθβ) (D₁.ιPre hX₁ V hV q) := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · ext y
    change q.1.1 (m.φ.f (D₂.ev 1 y)) = q.1.1 (D₁.ev 1 (homF D₁ D₂ m θ hθα y))
    rw [ev_homF, map_one]
  · refine CoveringCode.pullback_ext X₂.P (D₂.foldS hX₂) (Subtype.ext ?_) ?_
    swap
    · change (m.h q.1.2).1.2 =
        (m.h (CoveringCode.pullbackPt X₁.P (D₁.foldS hX₁) (D₁.incP hX₁ q.1.2))).1.2
      rw [pullbackPt_incP]
    change (D₂.inc₁S hX₂ (m.h q.1.2).1.1).1 =
      (homψS D₁ D₂ hX₁ hX₂ m θ (D₁.inc₁S hX₁ q.1.2.1.1)).1
    rw [inc₁S_coe, homψS_coe, inc₁S_coe, m.fst_h,
      show homψ D₁ D₂ m θ (D₁.inc 1 q.1.2.1.1.1) = (D₁.inc 1 ≫ homψ D₁ D₂ m θ) q.1.2.1.1.1 from
        rfl, inc_homψ, map_one]
    rfl

lemma ι_natural (x : TempObj.Fibre Ω V hV X₁) :
    D₂.ι hX₂ V hV (TempObj.fibreMap V hV m x) =
      TempObj.fibreMap V hV (hom D₁ D₂ hX₁ hX₂ m θ hθα hθβ) (D₁.ι hX₁ V hV x) := by
  induction x using Quotient.inductionOn with
  | h q =>
    exact congrArg Quotient.mk'' (ιPre_natural (V := V) (hV := hV) D₁ D₂ hX₁ hX₂ m θ hθα hθβ q)

end Natural

end IndData

end

end TemperedFundamentalGroups
