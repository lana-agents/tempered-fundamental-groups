/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueEnd

/-!
# Morphisms of the glued adic systems of two overlaps (generic; MR13, Galois action on lifts)

The adic systems `V.system`, `V'.system` of two overlaps live over the ideals `(V.ϖ)`, `(V'.ϖ)`.
Stating both over an explicit `(ϖ)` keeps the concrete instances from unifying `V.ϖ` with `V'.ϖ`
(which unfolds both overlaps and did not finish at the `P1Three` charts, MR13 run 14).

* **`NodeEtaleGlue.Overlap.systemAt`**: the adic system of `V` over `(ϖ)` for any `ϖ = V.ϖ`
  (`systemAt_self`: for `ϖ = V.ϖ` it is `V.system`);
* **`Overlap.systemMap`**: the morphism of the adic systems of two overlaps over the same `(ϖ)`
  induced by families `y n`, `p n` compatible with the overlaps and the successor maps
  (`succ_comp_twoChartMap`), `systemMap_f_succ`;
* **`systemMap_eq_id`**, **`systemMap_comp`** (functoriality, from `twoChartMap_eq_id/comp` and
  `TwoChartTower.systemShiftHom_eq_id/comp`).
-/

universe u

namespace SemistableReduction

open AdmissibleLift ProjectiveLine Polynomial

noncomputable section

namespace NodeEtaleGlue.Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {R₀' : Type u} [CommRing R₀'] [Algebra k R₀'] {f₀' : R₀'}
  {φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀'} {ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀'}
  {cov₀' : Admissible.Covering φ₀' ψ₀'} {πL' : cov₀'.ι → O}
  {R₀'' : Type u} [CommRing R₀''] [Algebra k R₀''] {f₀'' : R₀''}
  {φ₀'' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀''}
  {ψ₀'' : Polynomial k →ₐ[k] Admissible.Hat f₀''}
  {cov₀'' : Admissible.Covering φ₀'' ψ₀''} {πL'' : cov₀''.ι → O}
  {I : Input θ cov₀ πL} {I' : Input θ cov₀' πL'} {I'' : Input θ cov₀'' πL''}
  (V : Overlap I) (V' : Overlap I') (V'' : Overlap I'') (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-! ### The morphisms of the adic systems -/

section System

variable (ϖ : O) (h : V.ϖ = ϖ)

/-- **The adic system of chart algebras of `V` over `(ϖ)`**, for any `ϖ` equal to `V.ϖ`
(`systemAt_self`: for `ϖ = V.ϖ` it is `V.system`). -/
def systemAt : AdicChartAlgSystem (Ideal.span {ϖ}) :=
  TwoChartTower.systemShift _ (fun n ↦ V.twoChart hθ hO n) (fun n ↦ V.succ hθ hO n)
    (fun n ↦ V.surjective_f0 hθ hO n) (fun n ↦ I.surjective_Ymap hθ hO n)
    (fun n ↦ by subst h; exact V.ker_f0' hθ hO n) (fun n ↦ by subst h; exact V.ker_f1 hθ hO n)
    (by subst h; exact V.kill0 hθ hO) (by subst h; exact V.kill1 hθ hO)
    (fun n ↦ V.finite0 hθ hO n) (fun n ↦ V.finite1 hθ hO n)

lemma systemAt_self : V.systemAt hθ hO V.ϖ rfl = V.system hθ hO := rfl

/-- **The morphism of the adic systems of two overlaps** induced by families `y n : Y n → Y' n`
(first chart) and `p n : P0 n → P0' n` (pieces over the second chart) compatible with the
overlaps and the successor maps (`succ_comp_twoChartMap`): level `n + 1` is `twoChartMap n`. -/
def systemMap (h' : V'.ϖ = ϖ) (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
    (hy1 : ∀ n, y n (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (hyO : ∀ n (o : O), y n (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o))
    (p : ∀ n, V.P0.P n →+* V'.P0.P n)
    (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ n (o : O), p n (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
    (hψ : ∀ n z, V'.ψ hθ hO n (y n z) = V.mM V' n (p n) (hp0 n) (V.ψ hθ hO n z))
    (hyS : ∀ n z, I'.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z))
    (hpS : ∀ n e, V'.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e)) :
    AdicChartAlgSystem.Hom (V.systemAt hθ hO ϖ h) (V'.systemAt hθ hO ϖ h') :=
  TwoChartTower.systemShiftHom _
    (fun n ↦ V.twoChartMap V' hθ hO n (y n) (hy1 n) (hyO n) (p n) (hp0 n) (hpO n) (hψ n))
    (fun n ↦ V.succ_comp_twoChartMap V' hθ hO y hy1 hyO p hp0 hpO hψ hyS hpS n)

lemma systemMap_f_succ (h' : V'.ϖ = ϖ) (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
    (hy1 : ∀ n, y n (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (hyO : ∀ n (o : O), y n (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o))
    (p : ∀ n, V.P0.P n →+* V'.P0.P n)
    (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ n (o : O), p n (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
    (hψ : ∀ n z, V'.ψ hθ hO n (y n z) = V.mM V' n (p n) (hp0 n) (V.ψ hθ hO n z))
    (hyS : ∀ n z, I'.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z))
    (hpS : ∀ n e, V'.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e)) (n : ℕ) :
    (V.systemMap V' hθ hO ϖ h h' y hy1 hyO p hp0 hpO hψ hyS hpS).f (n + 1) =
      (V.twoChartMap V' hθ hO n (y n) (hy1 n) (hyO n) (p n) (hp0 n) (hpO n) (hψ n)).toHom :=
  rfl

/-- **`systemMap` of identities is the identity.** -/
lemma systemMap_eq_id (y : ∀ n, I.Y hθ n →+* I.Y hθ n)
    (hy1 : ∀ n, y n (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I.B0 (I.Y hθ n) V.x1)
    (hyO : ∀ n (o : O), y n (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o))
    (p : ∀ n, V.P0.P n →+* V.P0.P n)
    (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0))
    (hpO : ∀ n (o : O), p n (algebraMap O (V.P0.P n) o) = algebraMap O (V.P0.P n) o)
    (hψ : ∀ n z, V.ψ hθ hO n (y n z) = V.mM V n (p n) (hp0 n) (V.ψ hθ hO n z))
    (hyS : ∀ n z, I.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z))
    (hpS : ∀ n e, V.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e))
    (hy : ∀ n z, y n z = z) (hp : ∀ n e, p n e = e) :
    V.systemMap V hθ hO ϖ h h y hy1 hyO p hp0 hpO hψ hyS hpS = AdicChartAlgSystem.Hom.id _ :=
  TwoChartTower.systemShiftHom_eq_id _ _ _ fun n ↦
    V.twoChartMap_eq_id hθ hO n (y n) (hy1 n) (hyO n) (p n) (hp0 n) (hpO n) (hψ n) (hy n) (hp n)

/-- **`systemMap` of composites is the composite.** -/
lemma systemMap_comp (h' : V'.ϖ = ϖ) (h'' : V''.ϖ = ϖ) (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
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
    (y' : ∀ n, I'.Y hθ n →+* I''.Y hθ n)
    (hy1' : ∀ n, y' n (algebraMap I'.B0 (I'.Y hθ n) V'.x1) =
      algebraMap I''.B0 (I''.Y hθ n) V''.x1)
    (hyO' : ∀ n (o : O), y' n (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o) =
      (letI := V''.algOY hθ n; algebraMap O (I''.Y hθ n) o))
    (p' : ∀ n, V'.P0.P n →+* V''.P0.P n)
    (hp0' : ∀ n, p' n (algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0)) =
      algebraMap (V''.B' n) (V''.P0.P n) (algebraMap V''.B0' (V''.B' n) V''.x0))
    (hpO' : ∀ n (o : O), p' n (algebraMap O (V'.P0.P n) o) = algebraMap O (V''.P0.P n) o)
    (hψ' : ∀ n z, V''.ψ hθ hO n (y' n z) = V'.mM V'' n (p' n) (hp0' n) (V'.ψ hθ hO n z))
    (hyS' : ∀ n z, I''.Ymap hθ hO n (y' (n + 1) z) = y' n (I'.Ymap hθ hO n z))
    (hpS' : ∀ n e, V''.P0.sP n (p' (n + 1) e) = p' n (V'.P0.sP n e))
    (y'' : ∀ n, I.Y hθ n →+* I''.Y hθ n)
    (hy1'' : ∀ n, y'' n (algebraMap I.B0 (I.Y hθ n) V.x1) =
      algebraMap I''.B0 (I''.Y hθ n) V''.x1)
    (hyO'' : ∀ n (o : O), y'' n (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V''.algOY hθ n; algebraMap O (I''.Y hθ n) o))
    (p'' : ∀ n, V.P0.P n →+* V''.P0.P n)
    (hp0'' : ∀ n, p'' n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V''.B' n) (V''.P0.P n) (algebraMap V''.B0' (V''.B' n) V''.x0))
    (hpO'' : ∀ n (o : O), p'' n (algebraMap O (V.P0.P n) o) = algebraMap O (V''.P0.P n) o)
    (hψ'' : ∀ n z, V''.ψ hθ hO n (y'' n z) = V.mM V'' n (p'' n) (hp0'' n) (V.ψ hθ hO n z))
    (hyS'' : ∀ n z, I''.Ymap hθ hO n (y'' (n + 1) z) = y'' n (I.Ymap hθ hO n z))
    (hpS'' : ∀ n e, V''.P0.sP n (p'' (n + 1) e) = p'' n (V.P0.sP n e))
    (hy : ∀ n z, y'' n z = y' n (y n z)) (hp : ∀ n e, p'' n e = p' n (p n e)) :
    V.systemMap V'' hθ hO ϖ h h'' y'' hy1'' hyO'' p'' hp0'' hpO'' hψ'' hyS'' hpS'' =
      (V'.systemMap V'' hθ hO ϖ h' h'' y' hy1' hyO' p' hp0' hpO' hψ' hyS' hpS').comp
        (V.systemMap V' hθ hO ϖ h h' y hy1 hyO p hp0 hpO hψ hyS hpS) :=
  TwoChartTower.systemShiftHom_comp _ _ _ _ _ _ _ fun n ↦
    V.twoChartMap_comp V' V'' hθ hO n (y n) (hy1 n) (hyO n) (p n) (hp0 n) (hpO n) (hψ n)
      (y' n) (hy1' n) (hyO' n) (p' n) (hp0' n) (hpO' n) (hψ' n)
      (y'' n) (hy1'' n) (hyO'' n) (p'' n) (hp0'' n) (hpO'' n) (hψ'' n) (hy n) (hp n)

end System

end NodeEtaleGlue.Overlap

end

end SemistableReduction
