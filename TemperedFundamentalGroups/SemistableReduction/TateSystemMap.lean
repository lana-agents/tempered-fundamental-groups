/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeYMap
import TemperedFundamentalGroups.SemistableReduction.OverlapNodeHomH
import TemperedFundamentalGroups.SemistableReduction.P1ThreeHomDatum
import TemperedFundamentalGroups.SemistableReduction.TateSpecialFibre

/-!
# The morphisms of the adic systems of Tate coverings ramified at the cusp (MR12 I3, Tate)

For special-fibre data `(Sp, Sc, ω)`, `(Sp', Sc', ω')` of Tate coverings ramified at the cusp
(`TateGlue0.overlapCusp`) and a morphism `F = (f₁, f₀)` of the data (`OmegaPair.Hom`) whose map
`f₁` is balanced at the nodes (`TateGlue1.Balanced`, lead decision after MR12 c47), with
`(2 : k) ≠ 0` and `b₆` a unit (for the Kummer normal form at the cusp, `TateGlue0.cuspNFc`):

* **`TateGlue0.systemMapT`**: the morphism of the adic systems of chart algebras on `ℙ¹_O`
  (both over `(ϖ)`, `NodeEtaleGlue.Overlap.systemAt`), the generic
  `NodeEtaleGlue.Overlap.systemMapH` applied to the node patch maps (`LevelTower.nodeLevelMapH`
  of `TateGlue1.covMap f₁`), the maps of the étale lifts `TateGlue1.eMap f₁` and the maps of the
  cusp pieces `CuspTower.pieceP f₀`;
* **`TateGlue0.algMapT`**: the morphism of the algebraizations
  (`AdicChartAlgSystem.Algebraization.map`).
-/

universe u

namespace SemistableReduction

namespace OmegaPair.Hom

variable {R S₀ S₁ C₀ C₁ C₀' C₁' : Type u} [CommRing R] [CommRing S₀] [CommRing S₁]
  [CommRing C₀] [CommRing C₁] [CommRing C₀'] [CommRing C₁'] [Algebra S₀ C₀] [Algebra S₁ C₁]
  [Algebra S₀ C₀'] [Algebra S₁ C₁'] {a₀ : S₀} {a₁ : S₁}
  {i₀ : Algebra R (Localization.Away (algebraMap S₀ C₀ a₀))}
  {i₁ : Algebra R (Localization.Away (algebraMap S₁ C₁ a₁))}
  {i₀' : Algebra R (Localization.Away (algebraMap S₀ C₀' a₀))}
  {i₁' : Algebra R (Localization.Away (algebraMap S₁ C₁' a₁))}

/-- `Hom.comm` for overlap identifications given as algebra equivalences (with their algebra
structures as implicit arguments, so that they are unified rather than synthesized). -/
lemma comm_algEquiv (ω : Localization.Away (algebraMap S₀ C₀ a₀) ≃ₐ[R]
      Localization.Away (algebraMap S₁ C₁ a₁))
    (ω' : Localization.Away (algebraMap S₀ C₀' a₀) ≃ₐ[R]
      Localization.Away (algebraMap S₁ C₁' a₁))
    (φ : Hom a₀ a₁ ⇑ω ⇑ω') (x : Localization.Away (algebraMap S₀ C₀ a₀)) :
    ω' (awayMap a₀ φ.f₀ x) = awayMap a₁ φ.f₁ (ω x) :=
  comm (ω := ω.toRingEquiv.toRingHom) (ω' := ω'.toRingEquiv.toRingHom) φ x

end OmegaPair.Hom

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel KummerEtale AdmissibleLift TateGlue1 ProjectiveLine

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ cov₀' : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O] (hm : m ≠ 0)
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (Sp' : TateGlue1.Special1 hκ hπ hπe τ cov₀')
  (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (π'' : cov₀'.ι → O) (hπ'' : ∀ j, π'' j ^ cov₀'.e j = ϖ ^ m)
  (Sc Sc' : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (ω : OmegaC hκ hπ Sp Sc.C0) (ω' : OmegaC hκ hπ Sp' Sc'.C0)
  (h2 : (2 : k) ≠ 0) (hb₆ : IsUnit b₆) [IsEmpty cov₀.κ] [IsEmpty cov₀'.κ]
  (F : OmegaPair.Hom (Ideal.Quotient.mk (J θ (R := T0 π b₄ t κ)) (h0 π b₄ t κ))
    (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ)) ⇑ω ⇑ω')
  (hbal : Balanced hκ hπ hε Sp Sp' hϖ π' π'' F.f₁)

/-- **The morphism of the adic systems of chart algebras of the Tate coverings ramified at the
cusp** induced by a morphism `F = (f₁, f₀)` of special-fibre data with `f₁` balanced at the
nodes (`NodeEtaleGlue.Overlap.systemMapH`). -/
def systemMapT :
    AdicChartAlgSystem.Hom
      ((overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).systemAt hθ.out hO ϖ rfl)
      ((overlapCusp hκ hπ hε hϖ π'' hπ'' hker Sp' hm Sc' hO ω').systemAt hθ.out hO ϖ rfl) :=
  NodeEtaleGlue.Overlap.systemMapH (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω)
    (overlapCusp hκ hπ hε hϖ π'' hπ'' hker Sp' hm Sc' hO ω') hθ.out hO
    ((input_R hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans (input_R hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_commRingR hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans
      (input_commRingR hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_algOR hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans
      (input_algOR hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_algkR hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans
      (input_algkR hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_algSuccR hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans
      (input_algSuccR hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_f hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans (input_f hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_e hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans (input_e hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    (covMap hκ hπ hε Sp Sp' F.f₁) (nodeCoordI hκ hπ hε hϖ hker hm Sp π' hπ')
    (nodeCoordI hκ hπ hε hϖ hker hm Sp' π'' hπ'') (fun _ ↦ heq_refl_hat _)
    (fun _ ↦ heq_refl_hat _) hbal
    (fun n ↦ (eMap hκ hπ Sp Sp' hϖ hker F.f₁ n).toRingHom)
    (fun n ↦ (eMap hκ hπ Sp Sp' hϖ hker F.f₁ n).commutes _)
    (βI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'')
    (hβJI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'')
    (hβaI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'')
    (heβI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' F.f₁)
    (hβRI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'')
    F.f₁.toRingHom (covMap_ι₀ hκ hπ hε Sp Sp' F.f₁)
    (EtaleTower.CbMap (C := Sp.C1) (C' := Sp'.C1) (T1 π b₄ t κ) (w1 π b₄ t κ) F.f₁)
    (fun c ↦ EtaleTower.CbMap_algebraMap (T1 π b₄ t κ) (w1 π b₄ t κ) F.f₁ c)
    (fun n y ↦ EtaleTower.σ_homLift (T1 π b₄ t κ) hϖ (w1 π b₄ t κ) hker F.f₁
      (E1 hκ hπ hϖ hker Sp n) (E1 hκ hπ hϖ hker Sp' n) y)
    (fun n x ↦ sE_eMap hκ hπ Sp Sp' hϖ hker F.f₁ n x)
    (RingHom.id (T1 π b₄ t κ)) (fun _ _ ↦ rfl) rfl rfl (fun _ ↦ rfl)
    (fun n ↦ CuspTower.pieceP Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
      (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ n)
    (fun n ↦ CuspTower.pieceP_algebraMapB Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
      (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ n _)
    (fun n o ↦ CuspTower.pieceP_algebraMapO Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
      (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ n o)
    (fun n x ↦ CuspTower.sP_pieceP Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
      (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ n x)
    (fun n b ↦ (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).mM_algebraMap0
      (overlapCusp hκ hπ hε hϖ π'' hπ'' hker Sp' hm Sc' hO ω')
      (CuspTower.pieceP Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
        (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ n)
      (CuspTower.pieceP_algebraMapB Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
        (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ n _)
      (RingHom.id (EtaleTower.Tn ϖ (T0 π b₄ t κ) n))
      (fun y ↦ CuspTower.pieceP_algebraMapB Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
        (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ n y)
      (RingHom.id _) (fun _ ↦ rfl) (RingHom.id (T1 π b₄ t κ)) (fun _ ↦ rfl) b)
    (J_Tn_zero_eq_bot hker _) (J_Tn_zero_eq_bot hker _)
    (fun c z hz ↦ (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).mk_mM_γM
      (overlapCusp hκ hπ hε hϖ π'' hπ'' hker Sp' hm Sc' hO ω')
      (CuspTower.pieceP Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
        (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ 0)
      (CuspTower.pieceP_algebraMapB Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
        (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ 0 _)
      (fun o ↦ CuspTower.pieceP_algebraMapO Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
        (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ 0 o)
      F.f₀.toRingHom
      (fun c' z' hz' ↦ CuspTower.mk_liftP_ℓ0 Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
        (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ 0
        (CuspTower.pieceP_algebraMapB Sc Sc' hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO
          (cuspNFc hϖ hker h2 hκ hb₆ Sc') F.f₀ 0 _) c' z' hz')
      (OmegaPair.awayMap (C := Sc.C0) (C' := Sc'.C0)
        (Ideal.Quotient.mk (J θ (R := T0 π b₄ t κ)) (h0 π b₄ t κ)) F.f₀)
      (fun c ↦ OmegaPair.awayMap_algebraMap (C := Sc.C0) (C' := Sc'.C0)
        (Ideal.Quotient.mk (J θ (R := T0 π b₄ t κ)) (h0 π b₄ t κ)) F.f₀ c)
      F.f₁.toRingHom
      (OmegaPair.awayMap (C := Sp.C1) (C' := Sp'.C1)
        (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ)) F.f₁)
      (fun c ↦ OmegaPair.awayMap_algebraMap (C := Sp.C1) (C' := Sp'.C1)
        (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ)) F.f₁ c)
      (fun w ↦ OmegaPair.Hom.comm_algEquiv ω ω' F w) c z hz)
    ϖ rfl rfl


/-- **The morphism of the algebraizations** of the Tate coverings ramified at the cusp induced by
a balanced morphism `F` of special-fibre data: the unique morphism of chart algebras on `ℙ¹_O`
reducing to `systemMapT F` at every level (`AdicChartAlgSystem.Algebraization.map`). -/
def algMapT [IsAdicComplete (Ideal.span {ϖ}) O]
    (L : AdicChartAlgSystem.Algebraization
      ((overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).systemAt hθ.out hO ϖ rfl))
    (L' : AdicChartAlgSystem.Algebraization
      ((overlapCusp hκ hπ hε hϖ π'' hπ'' hker Sp' hm Sc' hO ω').systemAt hθ.out hO ϖ rfl)) :
    ChartModule.Hom L.N L'.N :=
  AdicChartAlgSystem.Algebraization.map
    (systemMapT hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' Sc Sc' hO ω ω' h2 hb₆ F hbal) L L'

lemma isHom_algMapT [IsAdicComplete (Ideal.span {ϖ}) O]
    (L : AdicChartAlgSystem.Algebraization
      ((overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).systemAt hθ.out hO ϖ rfl))
    (L' : AdicChartAlgSystem.Algebraization
      ((overlapCusp hκ hπ hε hϖ π'' hπ'' hker Sp' hm Sc' hO ω').systemAt hθ.out hO ϖ rfl)) :
    L.B.IsHom L'.B (algMapT hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' Sc Sc' hO ω ω' h2 hb₆ F hbal
      L L') :=
  AdicChartAlgSystem.Algebraization.isHom_map _ L L'

lemma comp_algMapT [IsAdicComplete (Ideal.span {ϖ}) O]
    (L : AdicChartAlgSystem.Algebraization
      ((overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).systemAt hθ.out hO ϖ rfl))
    (L' : AdicChartAlgSystem.Algebraization
      ((overlapCusp hκ hπ hε hϖ π'' hπ'' hker Sp' hm Sc' hO ω').systemAt hθ.out hO ϖ rfl))
    (n : ℕ) :
    (L'.α n).comp (algMapT hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' Sc Sc' hO ω ω' h2 hb₆ F hbal
      L L') =
      ((systemMapT hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' Sc Sc' hO ω ω' h2 hb₆ F hbal).f
        n).comp (L.α n) :=
  AdicChartAlgSystem.Algebraization.comp_map _ L L' n

end

end TateGlue0

end SemistableReduction
