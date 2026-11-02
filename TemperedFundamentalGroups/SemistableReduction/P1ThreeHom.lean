/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialMk
import TemperedFundamentalGroups.SemistableReduction.P1ThreeEtale
import TemperedFundamentalGroups.SemistableReduction.EtaleTowerHom
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueEnd

/-!
# The endomorphisms of the lift of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` (MR13 A1 (b), part 1)

The Galois action on the lift `P1Three.system` / its algebraization comes from endomorphisms of
the special-fibre datum `(Sp, S0, ω)`. This file builds the part over `V₁` and the system /
algebraization part from MR12's generic core:

* `P1Three.CuspChart.Special.covMap`: an endomorphism `φ` of `C1` induces the endomorphism of the
  admissible covering `cov.C = C1[1/1]` (`covMap_ι₀`, `covMap_id`, `covMap_comp`);
* **`P1Three.eMap φ n`**: the endomorphism of the étale lift `E1 n` (`EtaleTower.homLift`),
  `eMap_id`, `eMap_comp`, `sE_eMap`;
* **`P1Three.yEnd φ hg n`**: the endomorphism of the covering over `V₁` at level `n`
  (`NodeEtaleGlue.Input.yEnd` with the trivial patches, `subsingleton_hat_input`), under the
  compatibility `HgCompat φ` of the patch and étale parts on `E n[1/1]`;
* **`P1Three.systemEnd`**, **`P1Three.algEnd`**: given a compatible family `p` of endomorphisms of
  the cusp piece over `V₀` (overlap condition `hψ`, successor maps `hpS`), the endomorphism of the
  adic system of the lift and of its algebraization (`AdicChartAlgSystem.algHom`).

The cusp-piece family `p` (MR12's generic cusp-piece assembly, layer 3) and the discharge of
`HgCompat` and `hψ` from the overlap datum `ω` (MR12 step 2) are the remaining inputs.
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

namespace P1Three

open TateLevel AdmissibleLift EtaleTower

noncomputable section

namespace CuspChart

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {T : Type u} [CommRing T] [Algebra O T] {y s : T}

/-- **The map of the coverings of `T[1/1]/J`** induced by a map `φ : C1 → C1'` of the
special-fibre coverings (`cov.C = C1[1/1]` through `ι₀`). -/
def Special.covMap [Fact (Function.Surjective θ)] (Sp Sp' : Special θ T y s)
    (φ : Sp.C1 →ₐ[Ts θ T] Sp'.C1) : Sp.cov.C →ₐ[Ts θ (CuspTower.Rc T (1 : T))] Sp'.cov.C :=
  letI := Sp.ι₀.toAlgebra
  haveI := Sp.hι
  { IsLocalization.Away.lift (algebraMap (Ts θ T) Sp.C1 (Ideal.Quotient.mk _ 1))
      (g := Sp'.ι₀.comp φ.toRingHom) (by
        rw [map_one, map_one, map_one]; exact isUnit_one) with
    commutes' := fun x ↦ by
      obtain ⟨z, rfl⟩ := (bijective_φsC_one θ T).2 x
      change IsLocalization.Away.lift _ _ _ = _
      rw [← Sp.hι₀, ← Sp'.hι₀]
      change IsLocalization.Away.lift _ _ (algebraMap Sp.C1 Sp.cov.C _) = _
      rw [IsLocalization.Away.lift_eq, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, AlgHom.commutes] }

lemma Special.covMap_ι₀ [Fact (Function.Surjective θ)] (Sp Sp' : Special θ T y s)
    (φ : Sp.C1 →ₐ[Ts θ T] Sp'.C1) (x : Sp.C1) :
    Sp.covMap Sp' φ (Sp.ι₀ x) = Sp'.ι₀ (φ x) :=
  letI := Sp.ι₀.toAlgebra
  haveI := Sp.hι
  IsLocalization.Away.lift_eq (S := Sp.cov.C) _
    (g := Sp'.ι₀.comp φ.toRingHom) (by rw [map_one, map_one, map_one]; exact isUnit_one) x

/-- `covMap` is determined by its values on `ι₀`. -/
lemma Special.covMap_ext [Fact (Function.Surjective θ)] (Sp Sp' : Special θ T y s)
    {f g : Sp.cov.C →ₐ[Ts θ (CuspTower.Rc T (1 : T))] Sp'.cov.C}
    (h : ∀ x, f (Sp.ι₀ x) = g (Sp.ι₀ x)) : f = g := by
  letI := Sp.ι₀.toAlgebra
  haveI := Sp.hι
  exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers
    (algebraMap (Ts θ T) Sp.C1 (Ideal.Quotient.mk _ 1))) (RingHom.ext h))

lemma Special.covMap_id [Fact (Function.Surjective θ)] (Sp : Special θ T y s) :
    Sp.covMap Sp (AlgHom.id _ _) = AlgHom.id _ _ :=
  Special.covMap_ext Sp Sp fun x ↦ Special.covMap_ι₀ Sp Sp _ x

lemma Special.covMap_comp [Fact (Function.Surjective θ)] (Sp Sp' Sp'' : Special θ T y s)
    (φ : Sp.C1 →ₐ[Ts θ T] Sp'.C1) (φ' : Sp'.C1 →ₐ[Ts θ T] Sp''.C1) :
    Sp.covMap Sp'' (φ'.comp φ) = (Sp'.covMap Sp'' φ').comp (Sp.covMap Sp' φ) :=
  Special.covMap_ext Sp Sp'' fun x ↦ by
    rw [AlgHom.comp_apply, Special.covMap_ι₀, Special.covMap_ι₀, Special.covMap_ι₀,
      AlgHom.comp_apply]

end CuspChart

/-! ### The maps over `V₁`: étale pieces and (trivial) patches -/

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (Sp : Special1 O θ a) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing O]

/-- **The map of the étale lifts over `V₁`** at level `n` induced by an endomorphism `φ` of the
special-fibre covering `C1` (`EtaleTower.homLift`). -/
def eMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp.C1) (n : ℕ) :
    (E1 Sp hϖ hker n).E →ₐ[Tn ϖ (R1 O a) n] (E1 Sp hϖ hker n).E :=
  EtaleTower.homLift (R1 O a) hϖ 1 hker φ (E1 Sp hϖ hker n) (E1 Sp hϖ hker n)

lemma eMap_id (n : ℕ) : eMap Sp hϖ hker (AlgHom.id _ _) n = AlgHom.id _ _ :=
  EtaleTower.homLift_id (R1 O a) hϖ 1 hker _

lemma eMap_comp (φ ψ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp.C1) (n : ℕ) :
    eMap Sp hϖ hker (ψ.comp φ) n = (eMap Sp hϖ hker ψ n).comp (eMap Sp hϖ hker φ n) :=
  EtaleTower.homLift_comp (R1 O a) hϖ 1 hker φ ψ _ _ _

lemma sE_eMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp.C1) (n : ℕ) (x : (E1 Sp hϖ hker (n + 1)).E) :
    sE Sp hϖ hker n (eMap Sp hϖ hker φ (n + 1) x) = eMap Sp hϖ hker φ n (sE Sp hϖ hker n x) :=
  EtaleTower.succ_comp_homLift (R1 O a) hϖ 1 hker φ _ _ _ _ x

lemma subsingleton_hat_input (n : ℕ) :
    Subsingleton (FormalPatchLevel.Hat ((input Sp hϖ hker).T.f n)) :=
  subsingleton_hat (by
    change IsUnit (Ideal.Quotient.mk _ (algebraMap (R1 O a) (Rc1 O a) 1))
    rw [map_one, map_one]
    exact isUnit_one)

/-! ### The endomorphism of the covering over `V₁` -/

/-- **The compatibility of the maps of the (trivial) patches and of the étale lifts over
`E n[1/1]`** (the hypothesis `hg` of `NodeEtaleGlue.Input.yMap`). -/
def HgCompat (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp.C1) : Prop :=
  (input Sp hϖ hker).HgEnd hθ.out (subsingleton_hat_input Sp hϖ hker) (Sp.covMap Sp φ)
    (eMap Sp hϖ hker φ)

/-- **The endomorphism of the covering over `V₁` at level `n`** induced by an endomorphism `φ`
of the special-fibre covering `C1`. -/
def yEnd (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp.C1) (hg : HgCompat Sp hϖ hker φ) (n : ℕ) :
    (input Sp hϖ hker).Y hθ.out n →+* (input Sp hϖ hker).Y hθ.out n :=
  (input Sp hϖ hker).yEnd hθ.out (subsingleton_hat_input Sp hϖ hker) (Sp.covMap Sp φ)
    (eMap Sp hϖ hker φ) hg n

/-! ### The endomorphism of the adic system and of the algebraization -/

variable (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ)) (ω : OmegaC Sp S0.C0)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp.C1)
  (hg : HgCompat Sp hϖ hker φ)
  (p : ∀ n, (overlap Sp hϖ hker S0 ω hO).P0.P n →+* (overlap Sp hϖ hker S0 ω hO).P0.P n)
  (hp0 : ∀ n, p n (algebraMap ((overlap Sp hϖ hker S0 ω hO).B' n)
      ((overlap Sp hϖ hker S0 ω hO).P0.P n) (algebraMap (overlap Sp hϖ hker S0 ω hO).B0'
        ((overlap Sp hϖ hker S0 ω hO).B' n) (overlap Sp hϖ hker S0 ω hO).x0)) =
    algebraMap ((overlap Sp hϖ hker S0 ω hO).B' n) ((overlap Sp hϖ hker S0 ω hO).P0.P n)
      (algebraMap (overlap Sp hϖ hker S0 ω hO).B0' ((overlap Sp hϖ hker S0 ω hO).B' n)
        (overlap Sp hϖ hker S0 ω hO).x0))
  (hpO : ∀ n (o : O), p n (algebraMap O ((overlap Sp hϖ hker S0 ω hO).P0.P n) o) =
    algebraMap O ((overlap Sp hϖ hker S0 ω hO).P0.P n) o)
  (hψ : ∀ n z, (overlap Sp hϖ hker S0 ω hO).ψ hθ.out hO n (yEnd Sp hϖ hker φ hg n z) =
    (overlap Sp hϖ hker S0 ω hO).mM (overlap Sp hϖ hker S0 ω hO) n (p n) (hp0 n)
      ((overlap Sp hϖ hker S0 ω hO).ψ hθ.out hO n z))
  (hpS : ∀ n e, (overlap Sp hϖ hker S0 ω hO).P0.sP n (p (n + 1) e) =
    p n ((overlap Sp hϖ hker S0 ω hO).P0.sP n e))

/-- **The endomorphism of the adic system of chart algebras of the lift** induced by `φ` over
`V₁` and a compatible family `p` of endomorphisms of the cusp piece over `V₀`. -/
def systemEnd : ProjectiveLine.AdicChartAlgSystem.Hom (system Sp hϖ hker S0 ω hO)
    (system Sp hϖ hker S0 ω hO) :=
  (overlap Sp hϖ hker S0 ω hO).systemEnd hθ.out hO (yEnd Sp hϖ hker φ hg)
    ((input Sp hϖ hker).yEnd_algebraMap hθ.out (subsingleton_hat_input Sp hϖ hker)
      (Sp.covMap Sp φ) (eMap Sp hϖ hker φ) hg)
    ((input Sp hϖ hker).yEnd_succ hθ.out hO (subsingleton_hat_input Sp hϖ hker)
      (Sp.covMap Sp φ) (eMap Sp hϖ hker φ) hg (sE_eMap Sp hϖ hker φ))
    p hp0 hpO hψ hpS

/-- **The endomorphism of the algebraization** (`AdicChartAlgSystem.algHom` of `systemEnd`):
the unique endomorphism of the chart algebra `(N, B)` on `ℙ¹_O` reducing to `systemEnd`. -/
noncomputable def algEnd [IsAdicComplete (Ideal.span {ϖ}) O] {N : ProjectiveLine.ChartModule O}
    [Module.Finite (Polynomial O) (Module.AEval' N.x0)]
    [Module.Finite (Polynomial O) (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hc : ∀ m n (h : m ≤ n), ((system Sp hϖ hker S0 ω hO).tr h).comp (α n) = α m)
    (hB : ∀ n, B.IsHom ((system Sp hϖ hker S0 ω hO).alg n) (α n)) :
    ProjectiveLine.ChartModule.Hom N N :=
  ProjectiveLine.AdicChartAlgSystem.algHom (systemEnd Sp hϖ hker S0 ω hO φ hg p hp0 hpO hψ hpS)
    hc hB hα hc hB

end

end P1Three

end

end SemistableReduction
