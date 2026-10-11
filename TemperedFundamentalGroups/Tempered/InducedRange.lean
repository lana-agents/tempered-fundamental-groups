/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.InducedFibre

/-!
# The image of `ι` (Blueprint §11, F7′)

A fibre element of the induced covering whose geometric point lies on the copy `β k`
(`k ∈ H'`) is in the image of `ι` (`IndData.mem_range_ι`): the element `(1, k) ∈ H⁰` moves it to
the copy `1`. Components of geometric points transform under `H⁰` and under morphisms of induced
coverings by `x ↦ s * x * (β k)⁻¹` resp. `x ↦ θ x` (`IndData.comp_σ_symm`,
`IndData.comp_homF`).
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

variable {X' : TempObj O R A'} (D : IndData μ X') (hX : IndFaithful X')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma onCopy_comp (t : D.level.B →+* Ω) (x : D.S) (hx : t (D.idem x) = 1) :
    (D.onCopy t x hx).comp (D.ev x) = t :=
  RingHom.ext (D.onCopy_ev t x hx)

lemma exists_comp_ev (t : D.level.B →+* Ω) : ∃ x, ∃ t₀ : X'.Lv.L.B →+* Ω, t = t₀.comp (D.ev x) :=
  let ⟨x, hx⟩ := D.exists_idem t
  ⟨x, D.onCopy t x hx, (D.onCopy_comp t x hx).symm⟩

lemma comp_σ_symm {t : D.level.B →+* Ω} {t₀ : X'.Lv.L.B →+* Ω} {x : D.S}
    (ht : t = t₀.comp (D.ev x)) (s : D.S) (k : X'.Lv.L.H) :
    t.comp (((D.equivT hX (s, k) : D.level.H) : SemilinearAut R A D.level.B).σ.symm :
      D.level.B →+* D.level.B) =
      (t₀.comp ((k : SemilinearAut R A' X'.Lv.L.B).σ.symm : X'.Lv.L.B →+* X'.Lv.L.B)).comp
        (D.ev (s * x * (D.β k)⁻¹)) := by
  subst ht
  refine RingHom.ext fun y => ?_
  simp only [RingHom.comp_apply]
  exact congrArg t₀ (D.ev_equivT_symm hX (s, k) x y)

/-- **Fibre elements on the copy `β k` are in the image of `ι`.** -/
lemma mem_range_ι (q : TempObj.PreFibre Ω V hV (D.obj hX)) (k : X'.Lv.L.H)
    (t₀ : X'.Lv.L.B →+* Ω) (ht : (q.1.1 : (D.obj hX).Lv.L.B →+* Ω) = t₀.comp (D.ev (D.β k))) :
    ∃ x, D.ι hX V hV x = Quotient.mk'' q := by
  let g : (D.obj hX).Lv.L.H0 := ⟨D.equivT hX (1, k), by
    rw [FiniteLevel.mem_H0]
    change D.α 1 = 1
    rw [map_one]⟩
  set q' := g • q with hq'
  have ht' : (q'.1.1 : (D.obj hX).Lv.L.B →+* Ω) =
      (t₀.comp ((k : SemilinearAut R A' X'.Lv.L.B).σ.symm : X'.Lv.L.B →+* X'.Lv.L.B)).comp
        (D.ev 1) := by
    have := D.comp_σ_symm hX ht 1 k
    rw [one_mul, mul_inv_cancel] at this
    rw [← this]
    rfl
  let t' : X'.Lv.L.B →ₐ[R] Ω :=
    { t₀.comp ((k : SemilinearAut R A' X'.Lv.L.B).σ.symm : X'.Lv.L.B →+* X'.Lv.L.B) with
      commutes' := fun r => by
        have h1 := q'.1.1.commutes r
        have h2 := RingHom.congr_fun ht' (algebraMap R D.level.B r)
        rw [← h1]
        refine Eq.trans ?_ h2.symm
        change _ = (t₀.comp _) (D.ev₁ (algebraMap R D.level.B r))
        rw [AlgHom.commutes]
        rfl }
  have hq't : q'.1.1 = t'.comp D.ev₁ := AlgHom.ext fun y => RingHom.congr_fun ht' y
  let p' := CoveringCode.pullbackPt X'.P (D.foldS hX) q'.1.2
  have hsp1 : q'.1.2.1.1.1 = D.inc 1 (X'.Lv.sp V hV t').1 := by
    rw [q'.2, hq't]
    exact D.sp_comp_ev₁ hX V hV t'
  have hsp : (p'.1.1 : X'.Lv.c.scheme) = (X'.Lv.sp V hV t').1 := by
    change D.fold q'.1.2.1.1.1 = _
    rw [hsp1, ← Scheme.Hom.comp_apply, inc_fold]
    rfl
  refine ⟨Quotient.mk'' ⟨(t', p'), hsp⟩, Quotient.sound ⟨g, ?_⟩⟩
  change q' = D.ιPre hX V hV ⟨(t', p'), hsp⟩
  refine Subtype.ext (Prod.ext hq't ?_)
  refine CoveringCode.pullback_ext X'.P (D.foldS hX) (Subtype.ext ?_) rfl
  change q'.1.2.1.1.1 = (D.inc₁S hX p'.1.1).1
  rw [inc₁S_coe, hsp1, hsp]

end IndData

end

end TemperedFundamentalGroups
