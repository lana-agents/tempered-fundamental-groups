/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalPoints
import TemperedFundamentalGroups.SemistableReduction.CuspInput
import TemperedFundamentalGroups.SemistableReduction.TateGlue0

/-!
# The marked points of the Tate cusp chart (MR12 T2 S5.5)

On the special fibre `R̄ = Rc/J` of the cusp chart `Rc = T0[1/(1 + h)]` the zero set of the
coordinate `s̄ = h̄` is finite: **`TateTwoChart.isArtinianRing_cusp`** — `R̄/(s̄)` is Artinian,
being a finite algebra over `O[h]/(ker θ, h) ≅ k` (it is the image of `T0`, finite over `O[h]`,
since `1 + h` becomes `1`). So `FormalPoints.Pts s̄` is a finite set of points with
`⨅ 𝔪 ≤ √(s̄)` (`FormalPoints.iInf_le_radical`): the index data of the cusp factors.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateTwoChart

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k) (π b₄ t κ : O)

/-- The cusp chart `Rc = T0[1/(1 + h)]`. -/
abbrev RcT : Type u := CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ)

/-- The special fibre of the cusp chart. -/
abbrev RsC : Type u := EtaleTower.Ts θ (RcT π b₄ t κ)

/-- The coordinate `s̄ = h̄` on the special fibre of the cusp chart. -/
abbrev sbarC : RsC θ π b₄ t κ :=
  Ideal.Quotient.mk _ (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))

/-- `R̄/(s̄)`. -/
abbrev SC : Type u := RsC θ π b₄ t κ ⧸ Ideal.span {sbarC θ π b₄ t κ}

/-- `T0 → R̄/(s̄)`. -/
def toSC : T0 π b₄ t κ →+* SC θ π b₄ t κ :=
  (Ideal.Quotient.mk _).comp ((Ideal.Quotient.mk _).comp (algebraMap _ (RcT π b₄ t κ)))

lemma toSC_h0 : toSC θ π b₄ t κ (h0 π b₄ t κ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

lemma toSC_c0 : toSC θ π b₄ t κ (TateGlue0.c0 π b₄ t κ) = 1 := by
  change toSC θ π b₄ t κ (1 + h0 π b₄ t κ) = 1
  rw [map_add, map_one, toSC_h0, add_zero]

lemma toSC_surjective : Function.Surjective (toSC θ π b₄ t κ) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (TateGlue0.c0 π b₄ t κ)) r
  obtain ⟨n, hn⟩ := s.2
  refine ⟨a, ?_⟩
  have h := congrArg (fun x ↦ (Ideal.Quotient.mk (Ideal.span {sbarC θ π b₄ t κ}))
    (Ideal.Quotient.mk (AdmissibleLift.J θ (R := RcT π b₄ t κ)) x))
    (IsLocalization.mk'_spec (RcT π b₄ t κ) a s)
  simp only [map_mul] at h
  have hs : (Ideal.Quotient.mk (Ideal.span {sbarC θ π b₄ t κ}))
      (Ideal.Quotient.mk (AdmissibleLift.J θ (R := RcT π b₄ t κ))
        (algebraMap _ (RcT π b₄ t κ) s.1)) = 1 := by
    change toSC θ π b₄ t κ s.1 = 1
    rw [← hn, map_pow, toSC_c0, one_pow]
  rw [hs, mul_one] at h
  exact h.symm

/-- **`R̄/(s̄)` is Artinian**: the zero set of `s̄` on the special fibre of the cusp chart is
finite. -/
theorem isArtinianRing_cusp (hθ : Function.Surjective θ) :
    IsArtinianRing (SC θ π b₄ t κ) := by
  let φ : T0 π b₄ t κ →ₐ[O[X]] SC θ π b₄ t κ :=
    { toSC θ π b₄ t κ with commutes' := fun _ ↦ rfl }
  haveI : Module.Finite O[X] (SC θ π b₄ t κ) := by
    refine Module.Finite.of_surjective φ.toLinearMap ?_
    intro y
    obtain ⟨a, ha⟩ := toSC_surjective θ π b₄ t κ y
    exact ⟨a, ha⟩
  refine FormalPoints.isArtinianRing_of_finite θ (SC θ π b₄ t κ) hθ (fun o ho ↦ ?_) ?_
  · change (Ideal.Quotient.mk (Ideal.span {sbarC θ π b₄ t κ}))
      (Ideal.Quotient.mk (AdmissibleLift.J θ (R := RcT π b₄ t κ))
        (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (AdjoinRoot.of (G0 π b₄ t κ) (C o)))) = 0
    rw [of_C, ← IsScalarTower.algebraMap_apply,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 ho)), map_zero]
  · change toSC θ π b₄ t κ (AdjoinRoot.of (G0 π b₄ t κ) X) = 0
    exact toSC_h0 θ π b₄ t κ

end

end TateTwoChart

end SemistableReduction
