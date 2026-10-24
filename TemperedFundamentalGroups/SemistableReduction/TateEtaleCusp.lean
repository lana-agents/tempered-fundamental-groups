/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.OverlapKaehlerLocal
import TemperedFundamentalGroups.SemistableReduction.TateEtale

/-!
# The generic fibre of the Tate coverings ramified at the cusp is étale away from the cusp (T1b)

`TateGlue0.etale_overlapCusp` gives étaleness of the generic fibre of the algebraized Tate
covering ramified at the cusp only outside `V(ϖ h)` on the first chart. The fibre `h = 0` of the
projection to `ℙ¹` consists of the cusp `[0 : 1 : 0]` (`z = 0`) and the two points
`[0 : ±√b₆ : 1]` (`z² + 2κ t z + κ = 0`), and `z = w/ℓ₀` separates them:
`z (1 + z ((t² − b₆) z + 2t)) ∈ (h)` in `T0` (**`TateTwoChart.z0_mul`**). If the cusp factors
of the given special-fibre covering with index `≠ 1` lie over `z = 0` (the covering is unramified
over `[0 : ±√b₆ : 1]`, which are not cusps of `E ∖ {0}`), then:

* **`TateGlue0.kills_overlapCusp_z`**: `ϖᵐ z` kills `Ω[B₀⁄T0]`;
* **`TateGlue0.etale_overlapCusp_z`**: `B₀[1/(ϖ z)]` is étale over `T0[1/ϖ]` — so the generic
  fibre of the covering is étale over all of `E ∖ {0}` on the first chart (on the second chart
  `B₁[1/ϖ]` is étale over `T1[1/ϖ]` already, `etale_overlapCusp`).

The hypothesis on the cusp factors (`hspec`) is a condition on the given covering of the special
fibre (where it is ramified), not a shell. Generic pieces: `AlgStr.exists_one_sub_mul_eq`
(`1 − ϖ b` is a unit modulo `X` in `B₀`, `B₀/(X)` being finite over `O`),
`CuspTower.kills_cuspPiece'`, `CuspTower.hC_of_special`.
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace ChartModule

namespace AlgStr

variable {A : Type u} [CommRing A] {M : ChartModule A} (B : AlgStr M)

/-- **`1 − ϖ y` is a unit modulo `X` in `B₀`**, for `ϖ` in the Jacobson radical of `A`:
`B₀/(X)` is finite over `A[X]/(X) = A`. -/
theorem exists_one_sub_mul_eq [Module.Finite A[X] (Module.AEval' M.x0)] {ϖ : A}
    (hϖ : ϖ ∈ (⊥ : Ideal A).jacobson) (y : B.Ring0) :
    ∃ u s, (1 - B.const0 ϖ * y) * u = 1 + B.X0 * s := by
  letI := B.polyHom0.toAlgebra
  haveI := B.finite_polyHom0
  let q := Ideal.Quotient.mk (Ideal.span {B.X0})
  letI : Algebra A (B.Ring0 ⧸ Ideal.span {B.X0}) := (q.comp B.const0).toAlgebra
  have hfac : q.comp B.polyHom0 =
      (algebraMap A (B.Ring0 ⧸ Ideal.span {B.X0})).comp (Polynomial.evalRingHom 0) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp [polyHom0, RingHom.algebraMap_toAlgebra, q]
    · simp only [polyHom0, RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X,
        coe_evalRingHom, eval_X, map_zero, q]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hfin : (q.comp B.polyHom0).Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective q Ideal.Quotient.mk_surjective)
      (RingHom.finite_algebraMap.2 inferInstance)
  rw [hfac] at hfin
  haveI : Module.Finite A (B.Ring0 ⧸ Ideal.span {B.X0}) :=
    RingHom.finite_algebraMap.1 (RingHom.Finite.of_comp_finite hfin)
  haveI : Algebra.IsIntegral A (B.Ring0 ⧸ Ideal.span {B.X0}) := Algebra.IsIntegral.of_finite _ _
  obtain ⟨v, hv⟩ := (KaehlerLocal.isUnit_one_sub_of_isIntegral hϖ (q y)).exists_right_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  have h0 : q ((1 - B.const0 ϖ * y) * u - 1) = 0 := by
    rw [map_sub, map_mul, map_sub, map_one, map_mul, sub_eq_zero]
    exact hv
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  exact ⟨u, s, by linear_combination -hs⟩

/-- `B₀` is Noetherian (finite over `A[X]`). -/
theorem isNoetherianRing_ring0 [IsNoetherianRing A] [Module.Finite A[X] (Module.AEval' M.x0)] :
    IsNoetherianRing B.Ring0 := by
  letI := B.polyHom0.toAlgebra
  haveI := B.finite_polyHom0
  exact Algebra.FiniteType.isNoetherianRing A[X] B.Ring0

end AlgStr

end ChartModule

end ProjectiveLine

namespace SemistableReduction

namespace CuspTower

open TateLevel EtaleTower AdmissibleLift

variable {O : Type u} [CommRing O] {ϖ : O} {T0' : Type u} [CommRing T0'] [Algebra O T0']
  {c0 x0 : T0'} {k : Type u} [Field k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  (Sc : CuspSpecial T0' c0 x0 (θ := θ)) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing T0']
  (hx : ∀ n, IsSMulRegular (Tn ϖ T0' n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O T0')) x0 : Tn ϖ T0' n))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The differentials of the cusp patch, factor-wise** (`PatchInput.kills_piece'`). -/
theorem kills_cuspPiece' (n : ℕ) (d : T0')
    (hC : ∀ i : Sc.cov.κ, Sc.cov.ce i = 1 ∨ ∃ r s,
      algebraMap ((cuspInput Sc hϖ hker hx).R n)
          (FormalPatchLevel.Hat ((cuspInput Sc hϖ hker hx).T.f n))
        (algebraMap (Tn ϖ T0' n) ((cuspInput Sc hϖ hker hx).R n)
          (algebraMap T0' (Tn ϖ T0' n) d)) =
        (cuspInput Sc hϖ hker hx).T.t n * r +
          (1 - ((cuspInput Sc hϖ hker hx).T.level n).M.δ i) * s) :
    KaehlerLocal.Kills (Tn ϖ T0' n) (algebraMap (Tn ϖ T0' n) ((cuspPiece Sc hϖ hker hx hO).P n)
      (algebraMap T0' (Tn ϖ T0' n) d)) :=
  (cuspInput Sc hϖ hker hx).kills_piece' hθ.out hO n _ hC

/-- **The factor-wise condition from the special fibre**: if `z (1 + z w) ∈ (x₀)` in `T0'` and
every ramified cusp factor lies over `z = 0` on the special fibre, then `a z` satisfies the
condition of `kills_cuspPiece'` at every level. -/
theorem hC_of_special (n : ℕ) {z w g : T0'} (hzw : z * (1 + z * w) = x0 * g) (a : O)
    (hspec : ∀ i, Sc.cov.ce i ≠ 1 → ∃ r,
      algebraMap (Ts θ (Rc T0' c0)) (Admissible.Hat (fbar θ (sC T0' c0 x0)))
          (Ideal.Quotient.mk _ (algebraMap T0' (Rc T0' c0) z)) * Sc.cov.cidem i =
        algebraMap (Ts θ (Rc T0' c0)) (Admissible.Hat (fbar θ (sC T0' c0 x0)))
          (Ideal.Quotient.mk _ (sC T0' c0 x0)) * r)
    (i : Sc.cov.κ) : Sc.cov.ce i = 1 ∨ ∃ r s,
      algebraMap ((cuspInput Sc hϖ hker hx).R n)
          (FormalPatchLevel.Hat ((cuspInput Sc hϖ hker hx).T.f n))
        (algebraMap (Tn ϖ T0' n) ((cuspInput Sc hϖ hker hx).R n)
          (algebraMap T0' (Tn ϖ T0' n) (algebraMap O T0' a * z))) =
        (cuspInput Sc hϖ hker hx).T.t n * r +
          (1 - ((cuspInput Sc hϖ hker hx).T.level n).M.δ i) * s := by
  by_cases hce : Sc.cov.ce i = 1
  · exact Or.inl hce
  right
  set D := (cuspInput Sc hϖ hker hx).T.level n
  let φ : T0' →+* FormalPatchLevel.Hat ((cuspInput Sc hϖ hker hx).T.f n) :=
    (algebraMap ((cuspInput Sc hϖ hker hx).R n)
      (FormalPatchLevel.Hat ((cuspInput Sc hϖ hker hx).T.f n))).comp
      ((algebraMap (Tn ϖ T0' n) ((cuspInput Sc hϖ hker hx).R n)).comp
        (algebraMap T0' (Tn ϖ T0' n)))
  have hφ : ∀ d : T0', algebraMap ((cuspInput Sc hϖ hker hx).R n)
      (FormalPatchLevel.Hat ((cuspInput Sc hϖ hker hx).T.f n))
        (algebraMap (Tn ϖ T0' n) ((cuspInput Sc hϖ hker hx).R n)
          (algebraMap T0' (Tn ϖ T0' n) d)) = φ d := fun _ ↦ rfl
  have hza : φ z * (1 + φ z * φ w) ∈ Ideal.span {D.M.t} := by
    rw [← map_mul, ← map_one φ, ← map_add, ← map_mul, hzw, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨r, s, hrs⟩ := D.exists_eq_t_mul
    (z := algebraMap (Tn ϖ T0' n) ((cuspInput Sc hϖ hker hx).R n) (algebraMap T0' (Tn ϖ T0' n) z))
    (w := algebraMap (Tn ϖ T0' n) ((cuspInput Sc hϖ hker hx).R n) (algebraMap T0' (Tn ϖ T0' n) w))
    (z₀ := Ideal.Quotient.mk _ (algebraMap T0' (Rc T0' c0) z)) (eqv_mk _ hϖ n _) hza i
    (by
      obtain ⟨r, hr⟩ := hspec i hce
      exact ⟨r, by simp only [ψb, Polynomial.aeval_X]; exact hr⟩)
  refine ⟨φ (algebraMap O T0' a) * r, φ (algebraMap O T0' a) * s, ?_⟩
  change φ (algebraMap O T0' a * z) = D.M.t * (φ (algebraMap O T0' a) * r) +
    (1 - D.M.δ i) * (φ (algebraMap O T0' a) * s)
  rw [map_mul, show φ z = D.M.t * r + (1 - D.M.δ i) * s from hrs]
  ring

end CuspTower

namespace TateTwoChart

variable {O : Type u} [CommRing O] {π b₄ t κ b₆ : O}

/-- **`z` separates the cusp from the other two points of the fibre `h = 0`**: in `T0`,
`z (1 + z ((t² − b₆) z + 2t)) = h (−(t − π b₄) z² − z + π h²)` (from the cubic relation `eq0` and
`κ (t² − b₆) = 1`). -/
lemma z0_mul (hκ : κ * (t ^ 2 - b₆) = 1) :
    z0 π b₄ t κ * (1 + z0 π b₄ t κ * (algebraMap O _ (t ^ 2 - b₆) * z0 π b₄ t κ +
      algebraMap O _ (2 * t))) =
    h0 π b₄ t κ * (-(algebraMap O _ (t - π * b₄)) * z0 π b₄ t κ ^ 2 - z0 π b₄ t κ +
      algebraMap O _ π * h0 π b₄ t κ ^ 2) := by
  have h := eq0 π b₄ t κ
  have hk : algebraMap O (T0 π b₄ t κ) κ * (algebraMap O _ t ^ 2 - algebraMap O _ b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  simp only [map_mul, map_sub, map_ofNat, map_pow] at h ⊢
  linear_combination (algebraMap O (T0 π b₄ t κ) t ^ 2 - algebraMap O _ b₆) * h -
    (z0 π b₄ t κ ^ 2 * (2 * algebraMap O _ t + (algebraMap O _ t -
      algebraMap O _ π * algebraMap O _ b₄) * h0 π b₄ t κ) +
      z0 π b₄ t κ * (1 + h0 π b₄ t κ) - algebraMap O _ π * h0 π b₄ t κ ^ 3) * hk

end TateTwoChart

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel AdmissibleLift EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (hϖ : θ ϖ = 0) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (hm : m ≠ 0)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [IsAdicComplete (Ideal.span {ϖ}) O]
  [IsEmpty cov₀.κ]

/-- The condition "the ramified cusp factors lie over `z = 0`" on the special-fibre covering
`Sc.cov` over the cusp chart `D(1 + h)`. -/
def CuspOverOrigin
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ)) : Prop :=
  ∀ i, Sc.cov.ce i ≠ 1 → ∃ r,
    algebraMap (Ts θ (CuspTower.Rc (T0 π b₄ t κ) (c0 π b₄ t κ)))
        (Admissible.Hat (fbar θ (CuspTower.sC (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ))))
        (Ideal.Quotient.mk _ (algebraMap (T0 π b₄ t κ)
          (CuspTower.Rc (T0 π b₄ t κ) (c0 π b₄ t κ)) (z0 π b₄ t κ))) * Sc.cov.cidem i =
      algebraMap (Ts θ (CuspTower.Rc (T0 π b₄ t κ) (c0 π b₄ t κ)))
        (Admissible.Hat (fbar θ (CuspTower.sC (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ))))
        (Ideal.Quotient.mk _ (CuspTower.sC (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ))) * r

include hπ' in
/-- **`ϖᵐ z` kills the differentials of the algebraized Tate covering ramified at the cusp** over
the first chart, if the ramified cusp factors lie over `z = 0` (see the module docstring). -/
theorem kills_overlapCusp_z
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (hSc : CuspOverOrigin Sc) (ω : OmegaC hκ hπ Sp Sc.C0)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N
      ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n))
    {ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N}
    (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ)
    (hψα : ∀ n, (α (n + 1)).comp ψ = structureMapsCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω n) :
    letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ
    KaehlerLocal.Kills (T0 π b₄ t κ)
      (B.const0 (ϖ ^ m) * algebraMap (T0 π b₄ t κ) B.Ring0 (z0 π b₄ t κ)) := by
  haveI : IsAdicComplete
      (Ideal.span {(overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  haveI : IsNoetherianRing B.Ring0 := B.isNoetherianRing_ring0
  letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ
  letI : Algebra (TateTwoChart.twoChart π b₄ t κ).R0 B.Ring0 := B.algR0 hψ
  haveI : Module.Finite B.Ring0 Ω[B.Ring0⁄T0 π b₄ t κ] := by
    letI : Algebra O[X] B.Ring0 := B.polyHom0.toAlgebra
    haveI := B.finite_polyHom0
    haveI : IsScalarTower O[X] (T0 π b₄ t κ) B.Ring0 :=
      IsScalarTower.of_algebraMap_eq' (algR0_comp hψ).symm
    haveI : Algebra.FiniteType (T0 π b₄ t κ) B.Ring0 :=
      Algebra.FiniteType.of_restrictScalars_finiteType O[X] (T0 π b₄ t κ) B.Ring0
    infer_instance
  haveI : Module.Finite B.Ring0 Ω[B.Ring0⁄(TateTwoChart.twoChart π b₄ t κ).R0] :=
    ‹Module.Finite B.Ring0 Ω[B.Ring0⁄T0 π b₄ t κ]›
  have hP : ∀ n, KaehlerLocal.Kills (EtaleTower.Tn ϖ (T0 π b₄ t κ) n)
      (algebraMap (EtaleTower.Tn ϖ (T0 π b₄ t κ) n)
        ((CuspTower.cuspPiece Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO).P n)
        (algebraMap (T0 π b₄ t κ) (EtaleTower.Tn ϖ (T0 π b₄ t κ) n)
          (algebraMap O (T0 π b₄ t κ) (ϖ ^ m) * h0 π b₄ t κ ^ 1))) := fun n ↦
    CuspTower.kills_cuspPiece Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO n _ _
      (by rw [pow_one])
  have hPd : ∀ n, KaehlerLocal.Kills (EtaleTower.Tn ϖ (T0 π b₄ t κ) n)
      (algebraMap (EtaleTower.Tn ϖ (T0 π b₄ t κ) n)
        ((CuspTower.cuspPiece Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO).P n)
        (algebraMap (T0 π b₄ t κ) (EtaleTower.Tn ϖ (T0 π b₄ t κ) n)
          (algebraMap O (T0 π b₄ t κ) (ϖ ^ m) * z0 π b₄ t κ))) := fun n ↦
    CuspTower.kills_cuspPiece' Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO n _
      (CuspTower.hC_of_special Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) n (z0_mul hκ) _ hSc)
  have hj : ϖ ∈ (⊥ : Ideal O).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {ϖ}) (Ideal.mem_span_singleton_self ϖ)
  exact NodeEtaleGlue.Overlap.kills_local hθ.out hO
    (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB
    (baseMapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) (formallyUnramified_id _)
    (formallyUnramified_id _) hψ hψα (m := m)
    (fun n ↦ (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).kills_G hθ.out hO n
      (pow_eq_mul π' hπ'))
    hP (z0 π b₄ t κ) hPd (fun y ↦ B.exists_one_sub_mul_eq hj y)

variable [IsDomain O] [IsDiscreteValuationRing O] (hϖ0 : ϖ ≠ 0) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)

include hπ' hm hϖ0 h3 hE in
/-- **M2.5 (f) for the Tate covering ramified at the cusp, on all of `E ∖ {0}`**: if the
ramified cusp factors of the special-fibre covering lie over the cusp (`CuspOverOrigin`), then
`B₀[1/(ϖ z)]` is étale over `T0[1/ϖ]` (for any algebra structure compatible with `ψ`); `z` vanishes
on the generic fibre of the first chart exactly at the cusp `[0 : 1 : 0]`. -/
theorem etale_overlapCusp_z
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (hSc : CuspOverOrigin Sc) (ω : OmegaC hκ hπ Sp Sc.C0)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] [Module.Flat O[X] (Module.AEval' N.x0)]
    {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N
      ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n))
    {ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N}
    (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ)
    (hψα : ∀ n, (α (n + 1)).comp ψ = structureMapsCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω n) :
    letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ
    letI : Algebra (T0 π b₄ t κ) (Localization.Away
        (B.const0 ϖ * algebraMap (T0 π b₄ t κ) B.Ring0 (z0 π b₄ t κ))) :=
      ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra
    ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
        (Localization.Away (B.const0 ϖ * algebraMap (T0 π b₄ t κ) B.Ring0 (z0 π b₄ t κ)))]
      [@IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
        (Localization.Away (B.const0 ϖ * algebraMap (T0 π b₄ t κ) B.Ring0 (z0 π b₄ t κ)))
        Algebra.toSMul Algebra.toSMul Algebra.toSMul],
      Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
        (Localization.Away (B.const0 ϖ * algebraMap (T0 π b₄ t κ) B.Ring0 (z0 π b₄ t κ))) := by
  have hk := kills_overlapCusp_z hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc hSc ω hα hB hψ hψα
  have hπ0 := pi_ne_zero hπ hε hϖ0
  have hu := not_isUnit_varpi hϖ
  haveI := isDedekindDomain_away_T0_of_dvr (t := t) (κ := κ) hϖ0 hu hκ h3 hπ0 hE
  letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ
  set s := B.const0 ϖ * algebraMap (T0 π b₄ t κ) B.Ring0 (z0 π b₄ t κ)
  letI : Algebra (T0 π b₄ t κ) (Localization.Away s) :=
    ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra
  haveI : @IsScalarTower (T0 π b₄ t κ) B.Ring0 (Localization.Away s)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro _ _
  have hs : KaehlerLocal.Kills (T0 π b₄ t κ) (s ^ m) := by
    have e : s ^ m = (B.const0 (ϖ ^ m) * algebraMap (T0 π b₄ t κ) B.Ring0 (z0 π b₄ t κ)) *
        algebraMap (T0 π b₄ t κ) B.Ring0 (z0 π b₄ t κ) ^ (m - 1) := by
      rw [map_pow, mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm),
        mul_pow]
    rw [e]
    exact KaehlerLocal.kills_mul _ hk _
  haveI : Algebra.FormallyUnramified (T0 π b₄ t κ) (Localization.Away s) :=
    KaehlerLocal.formallyUnramified_away_of_pow _ hm hs _
  exact B.etale_away0 (C_ne_zero.2 hϖ0) (algebraMap_C_T0 π b₄ t κ ϖ) _ (algR0_comp hψ) s _

end

end TateGlue0

end SemistableReduction
