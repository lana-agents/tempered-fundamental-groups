/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueSystemMap
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0SpecialCompat
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0PatchSpecial
import TemperedFundamentalGroups.SemistableReduction.CuspInputHom

/-!
# The maps of the lifts reduce to the given maps on the special fibre over `V₀` (generic; MR13)

At a level with `J = 0` the patched levels, the cusp pieces and the first two-chart ring of a
glued covering are identified with the given special covering (`Level.cEquiv`,
`PatchInput.bottom`, `Overlap.r0Equiv'`). The maps of the lifts induced by a map of special data
are compatible with these identifications:

* `LevelTower.pMapOf_toP` (the lift of `φ_f` to the étale lifts is `φ` on `C → C_f ≃ P` when
  `J = 0`), **`LevelTower.levelMap_cEquiv`** (the map of patched levels is the given map at a level
  with `J = 0`);
* **`CuspTower.pieceMap_bottom`** (the maps of the cusp pieces commute with the bottom
  identifications `C0 → P0 n` of `PatchInput.bottom`);
* `NodeEtaleGlue.Overlap.mQ_eQ` (the map of the overlaps over the first chart is the localization
  of `φ1` under `eQ : C1[1/x̄₁] ≃ Q n`), **`Overlap.twoChartMap_f0_r0Equiv'`** (the map of the
  first two-chart rings is `φ0` under `r0Equiv' : C0 ≃ R0 n`).

These are the inputs of the compatibility of the morphisms of algebraized coverings with the
special-fibre identifications `B₀ ⧸ (ϖ) ≃ C0` (`P1Three.Datum.specialFibreEquiv0_algMap`).
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

namespace LevelTower

section Abstract

variable {S : Type u} [CommRing S] (f : S) {J : Ideal S} {m : ℕ} (hJ : J ^ m = ⊥) (hJ0 : J = ⊥)
  {P P' : Type u} [CommRing P] [Algebra S P] [Algebra.FormallyEtale S P]
  [CommRing P'] [Algebra S P']
  {C C' : Type u} [CommRing C] [Algebra S C] [CommRing C'] [Algebra S C']
  (σ : (P ⧸ J.map (algebraMap S P)) ≃ₐ[S] Localization.Away (algebraMap S C f))
  (σ' : (P' ⧸ J.map (algebraMap S P')) ≃ₐ[S] Localization.Away (algebraMap S C' f))

/-- **For `J = 0` the lift of `φ_f` is `φ` on `C → C_f ≃ P`.** -/
lemma pMapOf_toP (φ : C →ₐ[S] C') (c : C) :
    pMapOf f J hJ σ σ' φ (FormalPatchLevel.toP hJ0 f σ c) =
      FormalPatchLevel.toP hJ0 f σ' (φ c) := by
  have hinj : Function.Injective (Ideal.Quotient.mk (J.map (algebraMap S P'))) := fun a b h ↦ by
    rw [← FormalPatchLevel.quotEquivOfEqBot_mk hJ0 (S := S) a,
      ← FormalPatchLevel.quotEquivOfEqBot_mk hJ0 (S := S) b, h]
  apply hinj
  apply σ'.injective
  rw [σ_pMapOf, FormalPatchLevel.mk_toP, FormalPatchLevel.mk_toP]
  exact FormalPatchLevel.NfMap_algebraMap f φ c

end Abstract

section Level

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ}
  (D : Level R cov₀ πL hfe n) (D' : Level R cov₀' πL' hfe n)

/-- **At a level with `J = 0` the map of patched levels is the given map**:
`levelMap φ ∘ cEquiv = cEquiv' ∘ φ`. -/
theorem levelMap_cEquiv (φ : cov₀.C →ₐ[R₀] cov₀'.C)
    (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M) (hκ : KappaCompat hθ D D' φ g)
    (hJ0 : J θ (R := R n) = ⊥) (c : (cov₀.transport (h := hfe n)).C) :
    levelMap hθ D D' φ g hκ (D.cEquiv hθ hO hJ0 c) =
      D'.cEquiv hθ hO hJ0 (transportMapR (hfe n) φ c) := by
  have h : (levelMap hθ D D' φ g hκ).comp (D.cEquiv hθ hO hJ0).toAlgHom =
      (D'.cEquiv hθ hO hJ0).toAlgHom.comp (transportMapR (hfe n) φ) :=
    ext_level hθ D' fun x ↦
      pMapOf_toP (f n) D.hJ hJ0 D.σP D'.σP (transportMapR (hfe n) φ) x
  exact DFunLike.congr_fun h c

/-- `levelMap_cEquiv` through maps `ι₀ : C0 → cov₀.C`, `ι₀' : C0' → cov₀'.C` (the form of the
bottom identifications `PatchInput.toG`), for `φ` compatible with a map `φ0 : C0 → C0'`. -/
theorem levelMap_cEquiv_comp {C0 C0' : Type u} [CommRing C0] [CommRing C0']
    (φ : cov₀.C →ₐ[R₀] cov₀'.C) (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M)
    (hκ : KappaCompat hθ D D' φ g) (hJ0 : J θ (R := R n) = ⊥) (ι₀ : C0 →+* cov₀.C)
    (ι₀' : C0' →+* cov₀'.C) (φ0 : C0 →+* C0') (hφ : ∀ x, φ (ι₀ x) = ι₀' (φ0 x)) (x : C0) :
    levelMap hθ D D' φ g hκ (((D.cEquiv hθ hO hJ0).toRingHom.comp ι₀) x) =
      ((D'.cEquiv hθ hO hJ0).toRingHom.comp ι₀') (φ0 x) :=
  (levelMap_cEquiv hθ hO D D' φ g hκ hJ0 (ι₀ x)).trans
    (congrArg (D'.cEquiv hθ hO hJ0) (hφ x))

end Level

end LevelTower

namespace CuspTower

open TateLevel EtaleTower

variable {O : Type u} [CommRing O] {T0' : Type u} [CommRing T0'] [Algebra O T0'] {c0 x0 : T0'}
  {k : Type u} [Field k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  (Sc Sc' : CuspSpecial T0' c0 x0 (θ := θ)) {ϖ : O} (hϖ : θ ϖ = 0)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing T0']
  (hx : ∀ n, IsSMulRegular (Tn ϖ T0' n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O T0')) x0 : Tn ϖ T0' n))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The maps of the cusp pieces commute with the bottom identifications** `C0 → P0 n`
(`PatchInput.bottom`, at a level with `J = 0`). -/
theorem pieceMap_bottom (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) {n : ℕ}
    (hJ0 : J θ (R := Tn ϖ (Rc T0' c0) n) = ⊥) (c : Sc.C0) :
    pieceMap Sc Sc' hϖ hker hx hnf φ0 n
        (((cuspInput Sc hϖ hker hx).bottom hθ.out hO hJ0).toP c) =
      ((cuspInput Sc' hϖ hker hx).bottom hθ.out hO hJ0).toP (φ0 c) := by
  exact LevelTower.levelMap_cEquiv_comp hθ.out hO _ _ (covMap Sc Sc' φ0) _
    (LevelTower.exists_kappaCompat_cusp hθ.out _ _ (covMap Sc Sc' φ0) rfl hnf).choose_spec hJ0
    Sc.ι₀ Sc'.ι₀ φ0.toRingHom (fun x ↦ covMap_ι₀ Sc Sc' φ0 x) c

end CuspTower

namespace NodeEtaleGlue.Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {R₀' : Type u} [CommRing R₀'] [Algebra k R₀'] {f₀' : R₀'}
  {φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀'} {ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀'}
  {cov₀' : Admissible.Covering φ₀' ψ₀'} {πL' : cov₀'.ι → O}
  {I : Input θ cov₀ πL} {I' : Input θ cov₀' πL'}
  (V : Overlap I) (V' : Overlap I') (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ}
  (hJ0 : J θ (R := I.B n) = ⊥) (hJ0' : J θ (R := I'.B n) = ⊥)

/-- **The map of the overlaps over the first chart is the localization of `φ1`** under
`eQ : C1[1/x̄₁] ≃ Q n`, if `y` is `φ1` under `yEquiv : C1 ≃ Y n` (`J = 0`). -/
lemma mQ_eQ (y : I.Y hθ n →+* I'.Y hθ n)
    (hy1 : y (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (φ1 : I.C1 →+* I'.C1)
    (Lx1 : Localization.Away (algebraMap I.Bs I.C1 V.x1s) →+*
      Localization.Away (algebraMap I'.Bs I'.C1 V'.x1s))
    (hLx1 : ∀ c, Lx1 (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
    (hyE : ∀ c, y (I.yEquiv hθ hO hJ0 c) = I'.yEquiv hθ hO hJ0' (φ1 c))
    (d : Localization.Away (algebraMap I.Bs I.C1 V.x1s)) :
    V.mQ V' hθ n y hy1 (V.eQ hθ hO hJ0 d) = V'.eQ hθ hO hJ0' (Lx1 d) := by
  have h : (V.mQ V' hθ n y hy1).comp (V.eQ hθ hO hJ0).toRingHom =
      (V'.eQ hθ hO hJ0').toRingHom.comp Lx1 :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap I.Bs I.C1 V.x1s))
      (RingHom.ext fun c ↦ by
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
        rw [eQ_algebraMap, mQ_algebraMap, hyE, hLx1, eQ_algebraMap])
  exact RingHom.congr_fun h d

/-- **The map of the first two-chart rings is `φ0`** under `r0Equiv' : C0 ≃ R0 n` (`J = 0`):
for `y` given by `φ1` under `yEquiv`, `p` given by `φ0` under the bottom identifications and
`φ0`, `φ1` compatible with the overlap identifications `ω`, `ω'`. -/
theorem twoChartMap_f0_r0Equiv' (y : I.Y hθ n →+* I'.Y hθ n)
    (hy1 : y (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (hyO : ∀ o : O, y (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o))
    (p : V.P0.P n →+* V'.P0.P n)
    (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ o : O, p (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
    (hψ : ∀ z, V'.ψ hθ hO n (y z) = V.mM V' n p hp0 (V.ψ hθ hO n z))
    (bot : V.P0.Bottom n) (bot' : V'.P0.Bottom n) (φ0 : V.C0 →+* V'.C0)
    (hpb : ∀ c, p (bot.toP c) = bot'.toP (φ0 c))
    (Lx0 : Localization.Away (algebraMap V.Bs' V.C0 V.x0s) →+*
      Localization.Away (algebraMap V'.Bs' V'.C0 V'.x0s))
    (hLx0 : ∀ c, Lx0 (algebraMap V.C0 _ c) = algebraMap V'.C0 _ (φ0 c))
    (φ1 : I.C1 →+* I'.C1)
    (Lx1 : Localization.Away (algebraMap I.Bs I.C1 V.x1s) →+*
      Localization.Away (algebraMap I'.Bs I'.C1 V'.x1s))
    (hLx1 : ∀ c, Lx1 (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
    (hω : ∀ z, V'.ω (Lx0 z) = Lx1 (V.ω z))
    (hyE : ∀ c, y (I.yEquiv hθ hO hJ0 c) = I'.yEquiv hθ hO hJ0' (φ1 c)) (c : V.C0) :
    (V.twoChartMap V' hθ hO n y hy1 hyO p hp0 hpO hψ).f0 (V.r0Equiv' hθ hO hJ0 bot c) =
      V'.r0Equiv' hθ hO hJ0' bot' (φ0 c) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change V.mQ V' hθ n y hy1 (V.eQ hθ hO hJ0
        (V.ω (algebraMap V.C0 (Localization.Away (algebraMap V.Bs' V.C0 V.x0s)) c))) =
      V'.eQ hθ hO hJ0'
        (V'.ω (algebraMap V'.C0 (Localization.Away (algebraMap V'.Bs' V'.C0 V'.x0s)) (φ0 c)))
    rw [V.mQ_eQ V' hθ hO hJ0 hJ0' y hy1 φ1 Lx1 hLx1 hyE, ← hLx0, hω]
  · exact hpb c

/-- **The morphism of algebraizations induced by `systemMap` reduces to `φ0` over the first
chart**: under `r0Equiv' : C0 ≃ R0 0` and the reductions `α 1` (the generic form of
`specialFibreEquiv0` naturality). -/
theorem r0Equiv'_symm_map [IsNoetherianRing O] (ϖ : O) (h : V.ϖ = ϖ) (h' : V'.ϖ = ϖ)
    [IsAdicComplete (Ideal.span {ϖ}) O]
    (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
    (hy1 : ∀ n, y n (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (hyO : ∀ n (o : O), y n (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o))
    (p : ∀ n, V.P0.P n →+* V'.P0.P n)
    (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ n (o : O), p n (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
    (hψ : ∀ n z, V'.ψ hθ hO n (y n z) = V.mM V' n (p n) (hp0 n) (V.ψ hθ hO n z))
    (hyS : ∀ n z, I'.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z))
    (hpS : ∀ n e, V'.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e))
    (L : ProjectiveLine.AdicChartAlgSystem.Algebraization (V.systemAt hθ hO ϖ h))
    (L' : ProjectiveLine.AdicChartAlgSystem.Algebraization (V'.systemAt hθ hO ϖ h'))
    (hJ0 : J θ (R := I.B 0) = ⊥) (hJ0' : J θ (R := I'.B 0) = ⊥)
    (bot : V.P0.Bottom 0) (bot' : V'.P0.Bottom 0) (φ0 : V.C0 →+* V'.C0)
    (hpb : ∀ c, p 0 (bot.toP c) = bot'.toP (φ0 c))
    (Lx0 : Localization.Away (algebraMap V.Bs' V.C0 V.x0s) →+*
      Localization.Away (algebraMap V'.Bs' V'.C0 V'.x0s))
    (hLx0 : ∀ c, Lx0 (algebraMap V.C0 _ c) = algebraMap V'.C0 _ (φ0 c))
    (φ1 : I.C1 →+* I'.C1)
    (Lx1 : Localization.Away (algebraMap I.Bs I.C1 V.x1s) →+*
      Localization.Away (algebraMap I'.Bs I'.C1 V'.x1s))
    (hLx1 : ∀ c, Lx1 (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
    (hω : ∀ z, V'.ω (Lx0 z) = Lx1 (V.ω z))
    (hyE : ∀ c, y 0 (I.yEquiv hθ hO hJ0 c) = I'.yEquiv hθ hO hJ0' (φ1 c)) (b : L.B.Ring0) :
    (V'.r0Equiv' hθ hO hJ0' bot').symm ((L'.α 1).f0
        ((ProjectiveLine.AdicChartAlgSystem.Algebraization.map
          (V.systemMap V' hθ hO ϖ h h' y hy1 hyO p hp0 hpO hψ hyS hpS) L L').f0 b)) =
      φ0 ((V.r0Equiv' hθ hO hJ0 bot).symm ((L.α 1).f0 b)) := by
  rw [RingEquiv.symm_apply_eq, ← V.twoChartMap_f0_r0Equiv' V' hθ hO hJ0 hJ0' (y 0) (hy1 0)
    (hyO 0) (p 0) (hp0 0) (hpO 0) (hψ 0) bot bot' φ0 hpb Lx0 hLx0 φ1 Lx1 hLx1 hω hyE,
    RingEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (congrArg ProjectiveLine.ChartModule.Hom.f0
    (ProjectiveLine.AdicChartAlgSystem.Algebraization.comp_map _ L L' 1)) b

end NodeEtaleGlue.Overlap

end

end SemistableReduction
