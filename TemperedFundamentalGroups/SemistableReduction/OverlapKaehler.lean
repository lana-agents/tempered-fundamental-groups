/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.InputKaehler
import TemperedFundamentalGroups.SemistableReduction.KaehlerTower
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Base
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Patch

/-!
# The differentials of the algebraized covering over the second chart (Blueprint §12.8, M2.5 (f))

For `V : NodeEtaleGlue.Overlap I` (the covering over the second chart `V₀`, glued from
`Q n = Y n[1/x₁]` and the piece `P0 n` over `D(c₀)`):

* `KaehlerLocal.kills_mul`, **`KaehlerLocal.kills_of_isLocalization`** (killing the differentials
  survives localization of the algebra), **`KaehlerLocal.kills_of_tower`** (and enlarging the base,
  `Ω[S⁄R] ↠ Ω[S⁄R']`);
* **`NodeEtaleGlue.Overlap.kills_R0`**: a constant killing `Ω[Y n⁄B0]` and (times `e`) the
  differentials of the piece `P0 n` over `B' n` kills (times `e`) the differentials of the level
  `R0 = Q n ×_{M n} P0 n` over `B0'` (`ZariskiTwo.kills_glued` on `V₀ = D(x₀) ∪ D(c₀)`);
* `NodeEtaleGlue.Overlap.kills_G`: without cusp factors over the node chart, a constant which is a
  multiple of `πⱼ^(eⱼ-1)` for all Kummer factors kills the differentials of the node patches
  (`LevelTower.Level.kills_G`);
* `NodeEtaleGlue.PatchInput.kills_piece`: the same for a formal patch without nodes over `D(c₀)`,
  with a multiple of the cusp coordinate;
* **`NodeEtaleGlue.Overlap.kills_shift`**, **`formallyUnramified_shift`**: for a flat
  algebraization `(N, B, α)` of `S = V.system` with a structure map `ψ : D.algStr → B` from a base
  model `D` (a `BaseMap` with formally unramified `a0`, `a1`; in the Tate case the identities),
  `c Xʲ` kills `Ω[B₀⁄D.R0]` and `c` kills `Ω[B₁⁄D.R1]`, so `B₀[1/(c Xʲ)]` and `B₁[1/c]` are
  formally unramified over `D.R0`, `D.R1` (`TwoChartTower.kills_shift`).
-/

universe u

open Polynomial

namespace KaehlerLocal

variable (R : Type u) {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A multiple of a killer of the differentials kills them. -/
lemma kills_mul {c : S} (hc : Kills R c) (y : S) : Kills R (c * y) := fun ω ↦ by
  rw [mul_comm, mul_smul, hc ω, smul_zero]

/-- **Killing the differentials survives localization**: if `c` kills `Ω[S⁄R]`, its image kills
`Ω[S'⁄R]` for a localization `S'` of `S`. -/
theorem kills_of_isLocalization (M : Submonoid S) (S' : Type u) [CommRing S'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R S S'] [IsLocalization M S'] {c : S} (hc : Kills R c) :
    Kills R (algebraMap S S' c) := by
  haveI : Algebra.FormallyUnramified S S' := Algebra.FormallyUnramified.of_isLocalization M
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange R S S') := by
    rw [← LinearMap.range_eq_top,
      ← (LinearMap.exact_iff.mp (KaehlerDifferential.exact_mapBaseChange_map R S S'))]
    exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)
  intro ω
  obtain ⟨x, rfl⟩ := hsurj ω
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]
  | tmul b w =>
    rw [KaehlerDifferential.mapBaseChange_tmul, smul_comm, algebraMap_smul, ← map_smul, hc w,
      map_zero, smul_zero]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

/-- **Enlarging the base**: for `R → R' → S`, a killer of `Ω[S⁄R]` kills `Ω[S⁄R']`
(`Ω[S⁄R] ↠ Ω[S⁄R']`). -/
theorem kills_of_tower (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' S]
    [IsScalarTower R R' S] {c : S} (hc : Kills R c) : Kills R' c := by
  intro ω
  obtain ⟨ω, rfl⟩ := KaehlerDifferential.map_surjective R R' S ω
  rw [← map_smul, hc ω, map_zero]

end KaehlerLocal

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

/-- **The differentials of `Q n = Y n[1/x₁]` over the second chart**: if `c₁ ∈ B0` kills
`Ω[Y n⁄B0]` and `c' ∈ B0'` has the same image in the overlap `W0`, then `c'` kills
`Ω[Q n⁄B0']` (`Q n` is a localization of `Y n`, `W0 = B0[1/x₁] = B0'[1/x₀]`). -/
theorem kills_Q {c' : V.B0'} {c1 : I.B0}
    (hc : algebraMap V.B0' V.W0 c' = algebraMap I.B0 V.W0 c1)
    (hY : KaehlerLocal.Kills I.B0 (algebraMap I.B0 (I.Y hθ n) c1)) :
    letI := V.alg0'Q hθ n; KaehlerLocal.Kills V.B0' (algebraMap V.B0' (V.Q hθ n) c') := by
  letI := V.algW0Q hθ n
  letI := V.alg0'Q hθ n
  haveI : IsScalarTower I.B0 V.W0 (V.Q hθ n) :=
    IsScalarTower.of_algebraMap_eq fun b ↦ (V.algW0Q_algebraMap hθ n b).symm
  haveI : IsScalarTower V.B0' V.W0 (V.Q hθ n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := V.hW0'
  haveI : Algebra.FormallyUnramified V.B0' V.W0 :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers V.x0)
  refine KaehlerLocal.kills_of_base V.B0' V.W0 ?_
  have h1 : KaehlerLocal.Kills I.B0 (algebraMap I.B0 (V.Q hθ n) c1) := by
    rw [IsScalarTower.algebraMap_apply I.B0 (I.Y hθ n) (V.Q hθ n)]
    exact KaehlerLocal.kills_of_isLocalization I.B0
      (Submonoid.powers (algebraMap I.B0 (I.Y hθ n) V.x1)) _ hY
  rw [IsScalarTower.algebraMap_apply V.B0' V.W0 (V.Q hθ n), hc,
    ← IsScalarTower.algebraMap_apply]
  exact KaehlerLocal.kills_of_tower I.B0 V.W0 h1

/-- The differentials of the piece over `D(c₀)` over the second chart `B0'` (`B0' → B' n`
surjective). -/
theorem kills_P {d : V.B0'} (hP : KaehlerLocal.Kills (V.B' n)
      (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) d))) :
    letI := V.alg0'E n; KaehlerLocal.Kills V.B0' (algebraMap V.B0' (V.P0.P n) d) := by
  letI := V.alg0'E n
  haveI : IsScalarTower V.B0' (V.B' n) (V.P0.P n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := KaehlerLocal.subsingleton_of_surjective V.B0' (V.B' n) (V.surjB' n)
  exact KaehlerLocal.kills_of_base V.B0' (V.B' n) hP

/-- **The differentials of the level `R0 = Q n ×_{M n} P0 n` over the second chart**: if
`c₁ ∈ B0` kills `Ω[Y n⁄B0]`, `c' ∈ B0'` has the same image in `W0` and `c' e` kills the
differentials of the piece `P0 n` over `B' n`, then `c' e` kills `Ω[R0⁄B0']`. -/
theorem kills_R0 {c' : V.B0'} {c1 : I.B0}
    (hc : algebraMap V.B0' V.W0 c' = algebraMap I.B0 V.W0 c1)
    (hY : KaehlerLocal.Kills I.B0 (algebraMap I.B0 (I.Y hθ n) c1)) (e : V.B0')
    (hP : KaehlerLocal.Kills (V.B' n)
      (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) (c' * e)))) :
    letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    KaehlerLocal.Kills V.B0'
      (algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) (c' * e)) := by
  letI := V.alg0'Q hθ n
  letI := V.alg0'E n
  letI := V.alg0'M n
  refine ZariskiTwo.kills_glued _ _ V.hxc (V.fstLM hθ hO n) (V.sndLM hθ hO n) ?_ (V.kills_P n hP)
  rw [map_mul]
  exact KaehlerLocal.kills_mul _ (V.kills_Q hθ n hc hY) _

include hO in
/-- **The differentials of the node patches** (no cusp factors over the node chart): a constant
`c ∈ O` which is a multiple of `πⱼ^(eⱼ-1)` for every Kummer factor `j` kills the differentials of
the patched node algebra `G n` over the node chart `R n` (`LevelTower.Level.kills_G`). -/
theorem kills_G [IsEmpty cov₀.κ] {c : O} (hc : ∀ j, ∃ r : O, c = πL j ^ (cov₀.e j - 1) * r) :
    KaehlerLocal.Kills (I.R n) (algebraMap (I.R n) (I.T.G hθ n) (algebraMap (I.B n) (I.R n)
      (algebraMap I.B0 (I.B n) (letI := V.algOB0; algebraMap O I.B0 c)))) := by
  letI := V.algOB0
  rw [V.hOB0B n c, ← IsScalarTower.algebraMap_apply O (I.B n) (I.R n)]
  refine (I.T.level n).kills_G hθ hO (fun j ↦ ?_) (fun i ↦ isEmptyElim (α := cov₀.κ) i)
  obtain ⟨r, hr⟩ := hc j
  refine ⟨algebraMap O _ r, ?_⟩
  rw [hr, ← IsScalarTower.algebraMap_apply O (I.R n), map_mul, map_pow]
  rfl

end Overlap

namespace PatchInput

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  (D : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

include hO in
/-- **The differentials of a formal patch without nodes** over `D(c₀)`: an element `d ∈ B' n`
whose image in the completion `R̂ n` is a multiple of the cusp coordinate `t n` kills the
differentials of the piece `G n` over `B' n` (`LevelTower.Level.kills_G`; `R n = B' n[1/c₀]`). -/
theorem kills_piece [IsEmpty cov₀.ι] (d : B' n)
    (hC : ∀ _i : cov₀.κ, ∃ r, algebraMap (D.R n) (FormalPatchLevel.Hat (D.T.f n))
      (algebraMap (B' n) (D.R n) d) = D.T.t n * r) :
    KaehlerLocal.Kills (B' n) (algebraMap (B' n) ((D.piece hθ hO).P n) d) := by
  haveI : Algebra.FormallyUnramified (B' n) (D.R n) :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers (algebraMap B0' (B' n) c0))
  refine KaehlerLocal.kills_of_base (B' n) (D.R n) (S := D.G hθ n) ?_
  exact (D.T.level n).kills_G hθ hO (fun j ↦ isEmptyElim j) hC

end PatchInput

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} {V : Overlap I} (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [IsNoetherianRing O]

include hO in
/-- **The differentials of the algebraized covering** (generic): for a flat algebraization
`(N, B, α)` of `S = V.system` with a morphism of chart algebras `ψ : D.algStr → B` reducing to
the structure maps `β n` of a `BaseMap` with formally unramified `a0`, `a1` (in the Tate case the
identities), if `c` kills the differentials of the node patches `G n` over `R n` and `c x₀ʲ` those
of the piece `P0 n` over `B' n`, then `c Xʲ` kills `Ω[B₀⁄D.R0]` and `c` kills `Ω[B₁⁄D.R1]`. -/
theorem kills_shift {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})}
    (hS : V.system hθ hO = S) [IsAdicComplete (Ideal.span {V.ϖ}) O]
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N (S.M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n))
    {D : ProjectiveLine.TwoChartRings O} (b : BaseMap V D)
    (hu0 : letI := b.a0.toAlgebra; Algebra.FormallyUnramified D.R0 V.B0')
    (hu1 : letI := b.a1.toAlgebra; Algebra.FormallyUnramified D.R1 I.B0)
    {ψ : ProjectiveLine.ChartModule.Hom D.chartModule N} (hψ : D.algStr.IsHom B ψ)
    (hψα : ∀ n, (α (n + 1)).comp ψ = b.βS hθ hO n hS)
    {c : O} {j : ℕ} (hj : j ≤ 1)
    (hG : ∀ n, KaehlerLocal.Kills (I.R n) (algebraMap (I.R n) (I.T.G hθ n)
      (algebraMap (I.B n) (I.R n)
        (algebraMap I.B0 (I.B n) (letI := V.algOB0; algebraMap O I.B0 c)))))
    (hP : ∀ n, KaehlerLocal.Kills (V.B' n) (algebraMap (V.B' n) (V.P0.P n)
      (algebraMap V.B0' (V.B' n) (algebraMap O V.B0' c * V.x0 ^ j)))) :
    (letI := B.algR0 hψ; KaehlerLocal.Kills D.R0 (B.const0 c * B.X0 ^ j)) ∧
      (letI := B.algR1 hψ; KaehlerLocal.Kills D.R1 (B.const1 c)) := by
  subst hS
  letI := V.algOB0
  have hc : algebraMap V.B0' V.W0 (algebraMap O V.B0' c) =
      algebraMap I.B0 V.W0 (algebraMap O I.B0 c) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hY : ∀ n, KaehlerLocal.Kills I.B0 (algebraMap I.B0 (I.Y hθ n) (algebraMap O I.B0 c)) :=
    fun n ↦ I.kills_Y hθ hO V.surjB n (hG n)
  refine TwoChartTower.kills_shift (E := fun n ↦ V.twoChart hθ hO n) hα hB hψ hψα hj
    (fun n ↦ ?_) (fun n ↦ ?_)
  · letI := V.alg0'Q hθ n
    letI := V.alg0'E n
    letI := V.alg0'M n
    letI := V.algOQ hθ n
    haveI := V.towerOQ hθ n
    haveI := V.towerOE n
    haveI := V.towerOM n
    letI := b.a0.toAlgebra
    letI : Algebra D.R0 (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) :=
      (b.β hθ hO n).f0.toRingHom.toAlgebra
    haveI : IsScalarTower D.R0 V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    haveI := hu0
    have h := V.kills_R0 hθ hO n hc (hY n) (V.x0 ^ j) (hP n)
    have e : algebraMap O (V.twoChart hθ hO n).R0 c * (V.twoChart hθ hO n).x ^ j =
        algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n))
          (algebraMap O V.B0' c * V.x0 ^ j) := by
      have e0 : algebraMap O (V.twoChart hθ hO n).R0 c =
          algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) (algebraMap O V.B0' c) :=
        Subtype.ext (Prod.ext (IsScalarTower.algebraMap_apply O V.B0' (V.Q hθ n) c)
          (IsScalarTower.algebraMap_apply O V.B0' (V.P0.P n) c))
      rw [map_mul, map_pow, e0]
      rfl
    have h2 := KaehlerLocal.kills_of_base D.R0 V.B0' h
    rw [← e] at h2
    exact h2
  · letI := V.algOY hθ n
    letI := b.a1.toAlgebra
    letI : Algebra D.R1 (I.Y hθ n) := (b.β hθ hO n).f1.toRingHom.toAlgebra
    haveI : IsScalarTower D.R1 I.B0 (I.Y hθ n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    haveI := hu1
    exact KaehlerLocal.kills_of_base D.R1 I.B0 (S := I.Y hθ n) (hY n)

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
