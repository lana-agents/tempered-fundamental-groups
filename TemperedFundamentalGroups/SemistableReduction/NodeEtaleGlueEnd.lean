/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelTowerHom
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueHom
import TemperedFundamentalGroups.SemistableReduction.AdicSystemHom

/-!
# Functoriality of the glued adic systems (generic; MR13, Galois action on lifts)

Generic consumers of MR12's lifting core (layers 4, 5): the maps of the two-chart rings
`NodeEtaleGlue.Overlap.twoChartMap` and of the adic systems built from them are functorial in
the maps `y n` of the coverings over the first chart and `p n` of the pieces over the second
chart.

* `AdicChartAlgSystem.Hom.ext'` (morphisms of adic systems are determined by their levels);
* **`AdicChartAlgSystem.Algebraization`** (a bundled algebraization `(N, B, α)` of an adic system)
  and **`Algebraization.map`** (the morphism of algebraizations induced by a morphism of systems,
  `algHom`), `comp_map`, `isHom_map`, `eq_map`, **`map_id`**, **`map_comp`**;
* `TwoChartTower.systemShiftHom_eq_id`, **`systemShiftHom_comp`** (the shifted system morphism of
  identities / of a composite);
* `NodeEtaleGlue.Input.yMap_eq_id`, `Input.yMap_comp` (functoriality of the maps of the coverings
  over the first chart);
* `NodeEtaleGlue.Overlap.mQ_eq_id`, `mQ_comp`, **`twoChartMap_eq_id`**, **`twoChartMap_comp`**;
(the systems of two overlaps live over the ideals `(V.ϖ)`, `(V'.ϖ)`, so the morphism of systems
itself is assembled in the concrete instances, e.g. `P1Three.Datum.Hom.systemMap`).
-/

universe u

namespace ProjectiveLine.AdicChartAlgSystem

open Polynomial

variable {A : Type u} [CommRing A] {I : Ideal A} {S S' : AdicChartAlgSystem I}

/-- **Morphisms of adic systems are determined by their levels.** -/
lemma Hom.ext' {γ γ' : Hom S S'} (h : ∀ n, γ.f n = γ'.f n) : γ = γ' := by
  cases γ
  cases γ'
  congr
  funext n
  exact h n

/-- **An algebraization of an adic system of chart algebras**: a chart algebra `(N, B)`, finite
over both charts, with compatible surjections `α n : N → S.M n` with kernels `Iⁿ N`. -/
structure Algebraization (S : AdicChartAlgSystem I) where
  /-- the chart module -/
  N : ChartModule A
  [fin0 : Module.Finite A[X] (Module.AEval' N.x0)]
  [fin1 : Module.Finite A[X] (Module.AEval' N.x1)]
  /-- the algebra structure -/
  B : ChartModule.AlgStr N
  /-- the reductions -/
  α : ∀ n, ChartModule.Hom N (S.M n)
  hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤
  hc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m
  hB : ∀ n, B.IsHom (S.alg n) (α n)

attribute [instance] Algebraization.fin0 Algebraization.fin1

namespace Algebraization

variable [IsNoetherianRing A] [IsAdicComplete I A] {S'' : AdicChartAlgSystem I}

/-- **The morphism of algebraizations induced by a morphism of adic systems** (`algHom`). -/
noncomputable def map (γ : Hom S S') (L : Algebraization S) (L' : Algebraization S') :
    ChartModule.Hom L.N L'.N :=
  algHom γ L.hc L.hB L'.hα L'.hc L'.hB

lemma comp_map (γ : Hom S S') (L : Algebraization S) (L' : Algebraization S') (n : ℕ) :
    (L'.α n).comp (map γ L L') = (γ.f n).comp (L.α n) :=
  comp_algHom γ L.hc L.hB L'.hα L'.hc L'.hB n

lemma isHom_map (γ : Hom S S') (L : Algebraization S) (L' : Algebraization S') :
    L.B.IsHom L'.B (map γ L L') :=
  isHom_algHom γ L.hc L.hB L'.hα L'.hc L'.hB

/-- **Uniqueness**: a morphism `L.N → L'.N` with reductions `γ` is `map γ`. -/
lemma eq_map (γ : Hom S S') (L : Algebraization S) (L' : Algebraization S')
    (ψ : ChartModule.Hom L.N L'.N) (hψ : ∀ n, (L'.α n).comp ψ = (γ.f n).comp (L.α n)) :
    ψ = map γ L L' :=
  eq_algHom γ L.hc L.hB L'.hα L'.hc L'.hB ψ hψ

lemma map_id (L : Algebraization S) : map (Hom.id S) L L = ChartModule.Hom.id L.N :=
  algHom_id L.hα L.hc L.hB

lemma map_comp (γ : Hom S S') (γ' : Hom S' S'') (L : Algebraization S)
    (L' : Algebraization S') (L'' : Algebraization S'') :
    map (γ'.comp γ) L L'' = (map γ' L' L'').comp (map γ L L') :=
  algHom_comp γ L.hc L.hB L'.hα L'.hc L'.hB γ' L''.hα L''.hc L''.hB

end Algebraization

end ProjectiveLine.AdicChartAlgSystem

namespace SemistableReduction

open AdmissibleLift ProjectiveLine Polynomial

noncomputable section

namespace TwoChartTower

variable {A : Type u} [CommRing A] (I : Ideal A)
  {E E' E'' : ℕ → TwoChartRings A} {e : ∀ n, TwoChartMap (E (n + 1)) (E n)}
  {e' : ∀ n, TwoChartMap (E' (n + 1)) (E' n)} {e'' : ∀ n, TwoChartMap (E'' (n + 1)) (E'' n)}
  {he0 : ∀ n, Function.Surjective (e n).f0} {he1 : ∀ n, Function.Surjective (e n).f1}
  {hK0 : ∀ n, RingHom.ker (e n).f0 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R0)}
  {hK1 : ∀ n, RingHom.ker (e n).f1 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R1)}
  {hL0 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R0) = ⊥}
  {hL1 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R1) = ⊥}
  {hF0 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x0)}
  {hF1 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x1)}
  {he0' : ∀ n, Function.Surjective (e' n).f0} {he1' : ∀ n, Function.Surjective (e' n).f1}
  {hK0' : ∀ n, RingHom.ker (e' n).f0 = (I ^ (n + 1)).map (algebraMap A (E' (n + 1)).R0)}
  {hK1' : ∀ n, RingHom.ker (e' n).f1 = (I ^ (n + 1)).map (algebraMap A (E' (n + 1)).R1)}
  {hL0' : ∀ n, (I ^ (n + 1)).map (algebraMap A (E' n).R0) = ⊥}
  {hL1' : ∀ n, (I ^ (n + 1)).map (algebraMap A (E' n).R1) = ⊥}
  {hF0' : ∀ n, Module.Finite A[X] (Module.AEval' (E' n).chartModule.x0)}
  {hF1' : ∀ n, Module.Finite A[X] (Module.AEval' (E' n).chartModule.x1)}
  {he0'' : ∀ n, Function.Surjective (e'' n).f0} {he1'' : ∀ n, Function.Surjective (e'' n).f1}
  {hK0'' : ∀ n, RingHom.ker (e'' n).f0 = (I ^ (n + 1)).map (algebraMap A (E'' (n + 1)).R0)}
  {hK1'' : ∀ n, RingHom.ker (e'' n).f1 = (I ^ (n + 1)).map (algebraMap A (E'' (n + 1)).R1)}
  {hL0'' : ∀ n, (I ^ (n + 1)).map (algebraMap A (E'' n).R0) = ⊥}
  {hL1'' : ∀ n, (I ^ (n + 1)).map (algebraMap A (E'' n).R1) = ⊥}
  {hF0'' : ∀ n, Module.Finite A[X] (Module.AEval' (E'' n).chartModule.x0)}
  {hF1'' : ∀ n, Module.Finite A[X] (Module.AEval' (E'' n).chartModule.x1)}

/-- **The shifted system morphism of identities is the identity.** -/
lemma systemShiftHom_eq_id (χ : ∀ n, TwoChartMap (E n) (E n))
    (hχ : ∀ n, (e n).comp (χ (n + 1)) = (χ n).comp (e n)) (hid : ∀ n, χ n = TwoChartMap.id _) :
    systemShiftHom I χ hχ (he0 := he0) (he1 := he1) (hK0 := hK0) (hK1 := hK1) (hL0 := hL0)
      (hL1 := hL1) (hF0 := hF0) (hF1 := hF1) (he0' := he0) (he1' := he1) (hK0' := hK0)
      (hK1' := hK1) (hL0' := hL0) (hL1' := hL1) (hF0' := hF0) (hF1' := hF1) =
      AdicChartAlgSystem.Hom.id _ :=
  AdicChartAlgSystem.Hom.ext' fun n ↦ match n with
    | 0 => TwoChartMap.toHom_id
    | n + 1 => by
      change (χ n).toHom = _
      rw [hid n]
      exact TwoChartMap.toHom_id

/-- **The shifted system morphism of a composite is the composite.** -/
lemma systemShiftHom_comp (χ : ∀ n, TwoChartMap (E n) (E' n))
    (hχ : ∀ n, (e' n).comp (χ (n + 1)) = (χ n).comp (e n))
    (χ' : ∀ n, TwoChartMap (E' n) (E'' n))
    (hχ' : ∀ n, (e'' n).comp (χ' (n + 1)) = (χ' n).comp (e' n))
    (χ'' : ∀ n, TwoChartMap (E n) (E'' n))
    (hχ'' : ∀ n, (e'' n).comp (χ'' (n + 1)) = (χ'' n).comp (e n))
    (hcomp : ∀ n, χ'' n = (χ' n).comp (χ n)) :
    systemShiftHom I χ'' hχ'' (he0 := he0) (he1 := he1) (hK0 := hK0) (hK1 := hK1) (hL0 := hL0)
      (hL1 := hL1) (hF0 := hF0) (hF1 := hF1) (he0' := he0'') (he1' := he1'') (hK0' := hK0'')
      (hK1' := hK1'') (hL0' := hL0'') (hL1' := hL1'') (hF0' := hF0'') (hF1' := hF1'') =
    (systemShiftHom I χ' hχ' (he0 := he0') (he1 := he1') (hK0 := hK0') (hK1 := hK1')
      (hL0 := hL0') (hL1 := hL1') (hF0 := hF0') (hF1 := hF1') (he0' := he0'') (he1' := he1'')
      (hK0' := hK0'') (hK1' := hK1'') (hL0' := hL0'') (hL1' := hL1'') (hF0' := hF0'')
      (hF1' := hF1'')).comp
    (systemShiftHom I χ hχ (he0 := he0) (he1 := he1) (hK0 := hK0) (hK1 := hK1) (hL0 := hL0)
      (hL1 := hL1) (hF0 := hF0) (hF1 := hF1) (he0' := he0') (he1' := he1') (hK0' := hK0')
      (hK1' := hK1') (hL0' := hL0') (hL1' := hL1') (hF0' := hF0') (hF1' := hF1')) :=
  AdicChartAlgSystem.Hom.ext' fun n ↦ match n with
    | 0 => by
      change (TwoChartMap.id _).toHom = ((TwoChartMap.id _).comp (TwoChartMap.id _)).toHom
      rw [TwoChartMap.id_comp]
    | n + 1 => by
      change (χ'' n).toHom = ((χ' n).comp (χ n)).toHom
      rw [hcomp n]

end TwoChartTower

namespace NodeEtaleGlue.Input

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
  (I : Input θ cov₀ πL) (I' : Input θ cov₀' πL') (I'' : Input θ cov₀'' πL'')
  (hθ : Function.Surjective θ) (n : ℕ)

/-- **`yMap` of identities is the identity.** -/
lemma yMap_eq_id (g : I.T.G hθ n →+* I.T.G hθ n) (e : I.E n →+* I.E n)
    (he : e (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I.B n) (I.E n) (I.a n))
    (hg : ∀ x, ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE
      I.hbE I.hdiv I.hJB I.B0 n (g x) =
      I.eab I n e he (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
        I.hdiv I.hJB I.B0 n x))
    (hg' : ∀ x, g x = x) (he' : ∀ x, e x = x) (z : I.Y hθ n) :
    I.yMap I hθ n g e he hg z = z :=
  Subtype.ext (Prod.ext (hg' z.1.1) (he' z.1.2))

/-- **`yMap` of composites is the composite.** -/
lemma yMap_comp (g : I.T.G hθ n →+* I'.T.G hθ n) (e : I.E n →+* I'.E n)
    (he : e (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I'.B n) (I'.E n) (I'.a n))
    (hg : ∀ x, ρa0 I'.T hθ I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha I'.hι I'.E I'.σE
      I'.hbE I'.hdiv I'.hJB I'.B0 n (g x) =
      I.eab I' n e he (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
        I.hdiv I.hJB I.B0 n x))
    (g' : I'.T.G hθ n →+* I''.T.G hθ n) (e' : I'.E n →+* I''.E n)
    (he' : e' (algebraMap (I'.B n) (I'.E n) (I'.a n)) =
      algebraMap (I''.B n) (I''.E n) (I''.a n))
    (hg' : ∀ x, ρa0 I''.T hθ I''.B I''.qB I''.φs I''.hφs I''.ι₀ I''.hι₀ I''.a I''.b I''.ha
      I''.hι I''.E I''.σE I''.hbE I''.hdiv I''.hJB I''.B0 n (g' x) =
      I'.eab I'' n e' he' (ρa0 I'.T hθ I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha I'.hι
        I'.E I'.σE I'.hbE I'.hdiv I'.hJB I'.B0 n x))
    (g'' : I.T.G hθ n →+* I''.T.G hθ n) (e'' : I.E n →+* I''.E n)
    (he'' : e'' (algebraMap (I.B n) (I.E n) (I.a n)) =
      algebraMap (I''.B n) (I''.E n) (I''.a n))
    (hg'' : ∀ x, ρa0 I''.T hθ I''.B I''.qB I''.φs I''.hφs I''.ι₀ I''.hι₀ I''.a I''.b I''.ha
      I''.hι I''.E I''.σE I''.hbE I''.hdiv I''.hJB I''.B0 n (g'' x) =
      I.eab I'' n e'' he'' (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE
        I.hbE I.hdiv I.hJB I.B0 n x))
    (hgc : ∀ x, g'' x = g' (g x)) (hec : ∀ x, e'' x = e' (e x)) (z : I.Y hθ n) :
    I.yMap I'' hθ n g'' e'' he'' hg'' z =
      I'.yMap I'' hθ n g' e' he' hg' (I.yMap I' hθ n g e he hg z) :=
  Subtype.ext (Prod.ext (hgc z.1.1) (hec z.1.2))

end NodeEtaleGlue.Input

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

/-! ### Functoriality at a single level -/

section Level

variable (n : ℕ)

lemma mQ_eq_id (y : I.Y hθ n →+* I.Y hθ n)
    (hy1 : y (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I.B0 (I.Y hθ n) V.x1)
    (hy : ∀ z, y z = z) (q : V.Q hθ n) : V.mQ V hθ n y hy1 q = q := by
  have h : V.mQ V hθ n y hy1 = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap I.B0 (I.Y hθ n) V.x1))
      (RingHom.ext fun z ↦ by
        rw [RingHom.comp_apply, mQ_algebraMap, hy, RingHom.comp_apply, RingHom.id_apply])
  exact RingHom.congr_fun h q

lemma mQ_comp (y : I.Y hθ n →+* I'.Y hθ n)
    (hy1 : y (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (y' : I'.Y hθ n →+* I''.Y hθ n)
    (hy1' : y' (algebraMap I'.B0 (I'.Y hθ n) V'.x1) = algebraMap I''.B0 (I''.Y hθ n) V''.x1)
    (y'' : I.Y hθ n →+* I''.Y hθ n)
    (hy1'' : y'' (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I''.B0 (I''.Y hθ n) V''.x1)
    (hy : ∀ z, y'' z = y' (y z)) (q : V.Q hθ n) :
    V.mQ V'' hθ n y'' hy1'' q = V'.mQ V'' hθ n y' hy1' (V.mQ V' hθ n y hy1 q) := by
  have h : V.mQ V'' hθ n y'' hy1'' = (V'.mQ V'' hθ n y' hy1').comp (V.mQ V' hθ n y hy1) :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap I.B0 (I.Y hθ n) V.x1))
      (RingHom.ext fun z ↦ by
        rw [RingHom.comp_apply, mQ_algebraMap, hy, RingHom.comp_apply, RingHom.comp_apply,
          mQ_algebraMap, mQ_algebraMap])
  exact RingHom.congr_fun h q

/-- **`twoChartMap` of identities is the identity.** -/
lemma twoChartMap_eq_id (y : I.Y hθ n →+* I.Y hθ n)
    (hy1 : y (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I.B0 (I.Y hθ n) V.x1)
    (hyO : ∀ o : O, y (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o))
    (p : V.P0.P n →+* V.P0.P n)
    (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0))
    (hpO : ∀ o : O, p (algebraMap O (V.P0.P n) o) = algebraMap O (V.P0.P n) o)
    (hψ : ∀ z, V.ψ hθ hO n (y z) = V.mM V n p hp0 (V.ψ hθ hO n z))
    (hy : ∀ z, y z = z) (hp : ∀ e, p e = e) :
    V.twoChartMap V hθ hO n y hy1 hyO p hp0 hpO hψ = TwoChartMap.id _ :=
  TwoChartMap.ext_of_f0_f1
    (AlgHom.ext fun a ↦ Subtype.ext (Prod.ext (V.mQ_eq_id hθ n y hy1 hy a.1.1) (hp a.1.2)))
    (AlgHom.ext fun z ↦ hy z)

/-- **`twoChartMap` of composites is the composite.** -/
lemma twoChartMap_comp (y : I.Y hθ n →+* I'.Y hθ n)
    (hy1 : y (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (hyO : ∀ o : O, y (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o))
    (p : V.P0.P n →+* V'.P0.P n)
    (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ o : O, p (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
    (hψ : ∀ z, V'.ψ hθ hO n (y z) = V.mM V' n p hp0 (V.ψ hθ hO n z))
    (y' : I'.Y hθ n →+* I''.Y hθ n)
    (hy1' : y' (algebraMap I'.B0 (I'.Y hθ n) V'.x1) = algebraMap I''.B0 (I''.Y hθ n) V''.x1)
    (hyO' : ∀ o : O, y' (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o) =
      (letI := V''.algOY hθ n; algebraMap O (I''.Y hθ n) o))
    (p' : V'.P0.P n →+* V''.P0.P n)
    (hp0' : p' (algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0)) =
      algebraMap (V''.B' n) (V''.P0.P n) (algebraMap V''.B0' (V''.B' n) V''.x0))
    (hpO' : ∀ o : O, p' (algebraMap O (V'.P0.P n) o) = algebraMap O (V''.P0.P n) o)
    (hψ' : ∀ z, V''.ψ hθ hO n (y' z) = V'.mM V'' n p' hp0' (V'.ψ hθ hO n z))
    (y'' : I.Y hθ n →+* I''.Y hθ n)
    (hy1'' : y'' (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I''.B0 (I''.Y hθ n) V''.x1)
    (hyO'' : ∀ o : O, y'' (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V''.algOY hθ n; algebraMap O (I''.Y hθ n) o))
    (p'' : V.P0.P n →+* V''.P0.P n)
    (hp0'' : p'' (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V''.B' n) (V''.P0.P n) (algebraMap V''.B0' (V''.B' n) V''.x0))
    (hpO'' : ∀ o : O, p'' (algebraMap O (V.P0.P n) o) = algebraMap O (V''.P0.P n) o)
    (hψ'' : ∀ z, V''.ψ hθ hO n (y'' z) = V.mM V'' n p'' hp0'' (V.ψ hθ hO n z))
    (hy : ∀ z, y'' z = y' (y z)) (hp : ∀ e, p'' e = p' (p e)) :
    V.twoChartMap V'' hθ hO n y'' hy1'' hyO'' p'' hp0'' hpO'' hψ'' =
      (V'.twoChartMap V'' hθ hO n y' hy1' hyO' p' hp0' hpO' hψ').comp
        (V.twoChartMap V' hθ hO n y hy1 hyO p hp0 hpO hψ) :=
  TwoChartMap.ext_of_f0_f1
    (AlgHom.ext fun a ↦ Subtype.ext (Prod.ext
      (V.mQ_comp V' V'' hθ n y hy1 y' hy1' y'' hy1'' hy a.1.1) (hp a.1.2)))
    (AlgHom.ext fun z ↦ hy z)

end Level

end NodeEtaleGlue.Overlap

end

end SemistableReduction
