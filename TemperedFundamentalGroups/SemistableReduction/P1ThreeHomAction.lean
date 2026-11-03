/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeHomStructure
import TemperedFundamentalGroups.SemistableReduction.BaseChangeAct

/-!
# The Galois action on the lift is by `R1`-algebra automorphisms (MR13, (f) step 4 bridge)

For a datum `D` of a tame cover of `ℙ¹_k ∖ {0, 1, ā}`, a group `G` acting on `D`
(`act : G → D.Hom D`, `act 1 = id`, `act (g h) = act g ∘ act h`) and an algebraization `L` of
the lift:

* **`Datum.ring1Act : G →* (B₁ ≃+* B₁)`**, **`ring1Act_injective`** (if `G` acts faithfully on
  `C1`: the reduction of `ring1Act g` is `(act g).φ1`, `specialFibreEquiv1_algMap`);
* **`ring1Act_structure`**: `ring1Act g` fixes the image of the structure map (`L` flat on `B₁`);
* **`ring1AlgAct : G →* (B₁ ≃ₐ[R1] B₁)`** for the `R1`-algebra structure `B.algR1 hψ` given by the
  structure map, injective (**`ring1AlgAct_injective`**).

With `BaseChangeAct.act` this gives the faithful action on `K̄ ⊗_O B₁` over `K̄ ⊗_O R1` that iut's
`Pi1GaloisAlgebra.line_exists_sigmaQuotient_ofAlgebra` consumes.
-/

universe u

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower ProjectiveLine Polynomial

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

namespace Datum

variable (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {D D' : Datum O θ a} [IsAdicComplete (Ideal.span {ϖ}) O]

section Action

variable {G : Type*} [Group G] (act : G → D.Hom D)
  (L : AdicChartAlgSystem.Algebraization (systemD hϖ hker hO D))

/-- The ring endomorphism of `B₁` induced by `act g`. -/
def ring1Hom (g : G) : L.B.Ring1 →+* L.B.Ring1 :=
  (isHom_algMap hϖ hker ha0 ha1 hO (act g) L L).ringHom1

omit [Group G] in
lemma ring1Hom_apply (g : G) (x : L.B.Ring1) :
    ring1Hom hϖ hker ha0 ha1 hO act L g x = (algMap hϖ hker ha0 ha1 hO (act g) L L).f1 x :=
  rfl

lemma ring1Hom_mul (hmul : ∀ g h, act (g * h) = (act g).comp (act h)) (g h : G)
    (x : L.B.Ring1) :
    ring1Hom hϖ hker ha0 ha1 hO act L (g * h) x =
      ring1Hom hϖ hker ha0 ha1 hO act L g (ring1Hom hϖ hker ha0 ha1 hO act L h x) := by
  rw [ring1Hom_apply, ring1Hom_apply, ring1Hom_apply, hmul, algMap_comp]
  rfl

lemma ring1Hom_one (hone : act 1 = Hom.id D) (x : L.B.Ring1) :
    ring1Hom hϖ hker ha0 ha1 hO act L 1 x = x := by
  rw [ring1Hom_apply, hone, algMap_id]
  rfl

/-- **The action of `G` on the second chart `B₁` of the lift.** -/
def ring1Act (hone : act 1 = Hom.id D) (hmul : ∀ g h, act (g * h) = (act g).comp (act h)) :
    G →* (L.B.Ring1 ≃+* L.B.Ring1) where
  toFun g :=
    { ring1Hom hϖ hker ha0 ha1 hO act L g with
      invFun := ring1Hom hϖ hker ha0 ha1 hO act L g⁻¹
      left_inv := fun x ↦ by
        change ring1Hom hϖ hker ha0 ha1 hO act L g⁻¹ (ring1Hom hϖ hker ha0 ha1 hO act L g x) = x
        rw [← ring1Hom_mul hϖ hker ha0 ha1 hO act L hmul, inv_mul_cancel,
          ring1Hom_one hϖ hker ha0 ha1 hO act L hone]
      right_inv := fun x ↦ by
        change ring1Hom hϖ hker ha0 ha1 hO act L g (ring1Hom hϖ hker ha0 ha1 hO act L g⁻¹ x) = x
        rw [← ring1Hom_mul hϖ hker ha0 ha1 hO act L hmul, mul_inv_cancel,
          ring1Hom_one hϖ hker ha0 ha1 hO act L hone] }
  map_one' := RingEquiv.ext fun x ↦ ring1Hom_one hϖ hker ha0 ha1 hO act L hone x
  map_mul' g h := RingEquiv.ext fun x ↦ ring1Hom_mul hϖ hker ha0 ha1 hO act L hmul g h x

lemma ring1Act_apply (hone : act 1 = Hom.id D) (hmul : ∀ g h, act (g * h) = (act g).comp (act h))
    (g : G) (x : L.B.Ring1) :
    ring1Act hϖ hker ha0 ha1 hO act L hone hmul g x = ring1Hom hϖ hker ha0 ha1 hO act L g x :=
  rfl

/-- **The action on `B₁` is faithful if the action on `C1` is**: the reduction of `ring1Act g`
under `specialFibreEquiv1 : B₁/ϖ ≃ C1` is `(act g).φ1` (`specialFibreEquiv1_algMap`). -/
theorem ring1Act_injective (hone : act 1 = Hom.id D)
    (hmul : ∀ g h, act (g * h) = (act g).comp (act h))
    (hfaith : ∀ g, (∀ c, (act g).φ1 c = c) → g = 1) :
    Function.Injective (ring1Act hϖ hker ha0 ha1 hO act L hone hmul) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply hfaith
  intro c
  obtain ⟨y, rfl⟩ := (specialFibreEquiv1 D.Sp hϖ hker D.S0 D.om hO L.hα L.hB).surjective c
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← specialFibreEquiv1_algMap hϖ hker ha0 ha1 hO (act g) L L b]
  congr 2
  exact RingEquiv.congr_fun hg b

variable [IsDomain O] [Module.Flat O[X] (Module.AEval' L.N.x1)]

/-- **`G` acts by `R1`-algebra maps**: `ring1Act g` fixes the image of the structure map. -/
theorem ring1Act_structure (hϖu : ¬IsUnit ϖ) (hone : act 1 = Hom.id D)
    (hmul : ∀ g h, act (g * h) = (act g).comp (act h))
    (ψ : ChartModule.Hom (twoChart O a).chartModule L.N)
    (hψα : ∀ n r, ((L.α (n + 1)).f1 (ψ.f1 r) : (input D.Sp hϖ hker).Y hθ.out n) =
      algebraMap (input D.Sp hϖ hker).B0 ((input D.Sp hϖ hker).Y hθ.out n) r)
    (g : G) (r : R1 O a) :
    ring1Act hϖ hker ha0 ha1 hO act L hone hmul g (ψ.f1 r) = ψ.f1 r :=
  (ring1Act_apply hϖ hker ha0 ha1 hO act L hone hmul g (ψ.f1 r)).trans
    ((ring1Hom_apply hϖ hker ha0 ha1 hO act L g (ψ.f1 r)).trans
      (algMap_f1_structure hϖ hker ha0 ha1 hO hϖu (act g) L L ψ ψ hψα hψα r))

include ha0 ha1 in
/-- **The action of `G` on `B₁` by `R1`-algebra automorphisms** (`R1`-structure from the structure
map `ψ`, `ChartModule.AlgStr.algR1`). -/
def ring1AlgAct (hϖu : ¬IsUnit ϖ) (hone : act 1 = Hom.id D)
    (hmul : ∀ g h, act (g * h) = (act g).comp (act h))
    {ψ : ChartModule.Hom (twoChart O a).chartModule L.N}
    (hψ : (twoChart O a).algStr.IsHom L.B ψ)
    (hψα : ∀ n r, ((L.α (n + 1)).f1 (ψ.f1 r) : (input D.Sp hϖ hker).Y hθ.out n) =
      algebraMap (input D.Sp hϖ hker).B0 ((input D.Sp hϖ hker).Y hθ.out n) r) :
    letI : Algebra (R1 O a) L.B.Ring1 := L.B.algR1 hψ
    G →* (L.B.Ring1 ≃ₐ[R1 O a] L.B.Ring1) :=
  @BaseChangeAct.toAlgAct (R1 O a) L.B.Ring1 _ _ (L.B.algR1 hψ) G _
    (ring1Act hϖ hker ha0 ha1 hO act L hone hmul)
    (fun g r ↦ ring1Act_structure hϖ hker ha0 ha1 hO act L hϖu hone hmul ψ hψα g r)

/-- **The action of `G` on `B₁` by `R1`-algebra automorphisms is faithful** if it is on `C1`. -/
theorem ring1AlgAct_injective (hϖu : ¬IsUnit ϖ) (hone : act 1 = Hom.id D)
    (hmul : ∀ g h, act (g * h) = (act g).comp (act h))
    (hfaith : ∀ g, (∀ c, (act g).φ1 c = c) → g = 1)
    {ψ : ChartModule.Hom (twoChart O a).chartModule L.N}
    (hψ : (twoChart O a).algStr.IsHom L.B ψ)
    (hψα : ∀ n r, ((L.α (n + 1)).f1 (ψ.f1 r) : (input D.Sp hϖ hker).Y hθ.out n) =
      algebraMap (input D.Sp hϖ hker).B0 ((input D.Sp hϖ hker).Y hθ.out n) r) :
    Function.Injective (ring1AlgAct hϖ hker ha0 ha1 hO act L hϖu hone hmul hψ hψα) :=
  @BaseChangeAct.toAlgAct_injective (R1 O a) L.B.Ring1 _ _ (L.B.algR1 hψ) G _ _ _
    (ring1Act_injective hϖ hker ha0 ha1 hO act L hone hmul hfaith)

end Action

end Datum

end

end P1Three

end SemistableReduction
