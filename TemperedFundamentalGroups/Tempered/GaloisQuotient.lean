/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.GaloisContinuous
import TemperedFundamentalGroups.Tempered.GaloisSurjective
import ContinuousKummerTheory.Curve.PointSection

/-!
# `Π^tp ⧸ Δ^tp ≃ₜ* G_k`

At a base point `V` over a `k`-rational point (`V ≤ A`, `A` a place over the point, `O` a
complete DVR; the setting of `Tempered/GaloisSurjective.lean`), the arithmetic quotient
`Π^tp → G_k` (`piToGk ∘ tempToPi`) induces an **isomorphism of topological groups**
`Π^tp ⧸ Δ^tp ≃ₜ* G_k` (`Kummer.tempQuotGk`), the topological form of the tempered homotopy
exact sequence `1 → Δ^tp → Π^tp → G_k → 1`.

* `Kummer.decompAToV`: `D_A → D_V`, `σ ↦ σ|_R` (`toRAut`), continuous for the Krull topology of
  `Gal(Ω/F)` on `D_A` and `decompTop` on `D_V` (`continuous_decompAToV`);
* `Kummer.galA = galoisToTempered ∘ decompAToV : D_A → Π^tp`, continuous;
* `Kummer.piToGk_galA_surjective`: `D_A → Π^tp → G_k` is onto
  (continuous-kummer-theory `decompositionMap_surjective_of_rational`);
* **`Kummer.tempQuotGk`**: the inverse is continuous since `D_A` is compact
  (continuous-kummer-theory
  `compactSpace_decompositionSubgroup`) and `G_k` Hausdorff, so `D_A ↠ G_k` is a quotient map
  factoring through `Π^tp ⧸ Δ^tp`.
-/

universe u

open IsLocalRing CategoryTheory

open scoped Pointwise

namespace TemperedFundamentalGroups

namespace Kummer

noncomputable section

open KummerTheory KummerTheory.Curve AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)
  (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)]
  (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)
  (hHL : D.HL = D.H) (hVA : V ≤ A)
  [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
/-- **`D_A → D_V`**, `σ ↦ σ|_R`. -/
def decompAToV : A.decompositionSubgroup (F D) →* decompositionGroup D.R V where
  toFun σ := ⟨toRAut D hHL σ.1, toRAut_mem_decompositionGroup D O V hV A hk hkres hHL hVA σ⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)

omit [CharZero k] [IsAlgClosed Ω] in
/-- `D_A → D_V` is continuous (Krull topologies). -/
theorem continuous_decompAToV :
    @Continuous _ _ _ (decompTop D.R V) (decompAToV D O V hV A hk hkres hHL hVA) := by
  letI := decompTop D.R V
  haveI := decompTop_isTopologicalGroup D.R V
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  refine ((decompFilterBasis D.R V).nhds_one_hasBasis).tendsto_right_iff.2 fun _ ⟨S, hS⟩ => ?_
  subst hS
  refine Filter.mem_of_superset ((Filter.biInter_mem S.finite_toSet).2 fun x _ =>
    ((continuous_subtype_val (p := (· ∈ A.decompositionSubgroup (F D)))).isOpen_preimage _
      (stabilizer_isOpen_of_isIntegral (K := F D) x)).mem_nhds
        (show (1 : Ω ≃ₐ[F D] Ω) ∈ MulAction.stabilizer _ x from one_mem _)) ?_
  intro σ hσ
  simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    at hσ
  intro x hx
  exact hσ x hx

omit [IsAlgClosed Ω] in
/-- **The Galois elements of `D_A` in `Π^tp`.** -/
def galA : A.decompositionSubgroup (F D) →* TempPi D O V hV :=
  (galoisToTempered O D.R D.A hV).comp (decompAToV D O V hV A hk hkres hHL hVA)

omit [CharZero k] [IsAlgClosed Ω] in
theorem continuous_galA : Continuous (galA D O V hV A hk hkres hHL hVA) := by
  letI := decompTop D.R V
  exact (continuous_galoisToTempered O D.R D.A V hV).comp
    (continuous_decompAToV D O V hV A hk hkres hHL hVA)

include hrat in
/-- **`D_A → Π^tp → G_k` is surjective** (rational point, complete DVR). -/
theorem piToGk_galA_surjective :
    Function.Surjective (((piToGk D).comp (tempToPi D O V hV)).comp
      (galA D O V hV A hk hkres hHL hVA)) := fun g => by
  set e := kbarEquiv A hk hkres
  obtain ⟨σ, hσ⟩ := decompositionMap_surjective_of_rational D A hk hkres hrat
    (e.symm.trans (g.trans e))
  have hmem := toRAut_mem_decompositionGroup D O V hV A hk hkres hHL hVA σ
  refine ⟨σ, AlgEquiv.ext fun y => ?_⟩
  apply (kbarResidue A hk).injective
  change kbarResidue A hk (piToGk D (tempToPi D O V hV
    (galoisToTempered O D.R D.A hV ⟨toRAut D hHL σ.1, hmem⟩)) y) = _
  rw [kbarResidue_piToGk_tempToPi D O V hV A hk hkres hHL σ hmem, hσ]
  change e (g (e.symm (kbarResidue A hk y))) = kbarResidue A hk (g y)
  rw [show kbarResidue A hk y = e y from rfl, e.symm_apply_apply]
  rfl

include hrat hk hkres hHL hVA in
theorem piToGk_tempToPi_surjective' :
    Function.Surjective ((piToGk D).comp (tempToPi D O V hV)) := fun g => by
  obtain ⟨σ, hσ⟩ := piToGk_galA_surjective D O V hV A hk hkres hrat hHL hVA g
  exact ⟨_, hσ⟩

include hrat in
/-- **`Π^tp ⧸ Δ^tp ≃ₜ* G_k`** at a base point over a `k`-rational point. -/
def tempQuotGk : TempPi D O V hV ⧸ deltaTemp D O V hV ≃ₜ* Gk k Ω where
  toMulEquiv := QuotientGroup.quotientKerEquivOfSurjective _
    (piToGk_tempToPi_surjective' D O V hV A hk hkres hrat hHL hVA)
  continuous_toFun :=
    continuous_quot_lift _ ((continuous_piToGk D).comp (continuous_tempToPi D O V hV))
  continuous_invFun := by
    set f := (piToGk D).comp (tempToPi D O V hV)
    set e := QuotientGroup.quotientKerEquivOfSurjective _
      (piToGk_tempToPi_surjective' D O V hV A hk hkres hrat hHL hVA)
    have hf : Continuous f := (continuous_piToGk D).comp (continuous_tempToPi D O V hV)
    set r := f.comp (galA D O V hV A hk hkres hHL hVA)
    have hr : Continuous r := hf.comp (continuous_galA D O V hV A hk hkres hHL hVA)
    have hq : Topology.IsQuotientMap r :=
      IsClosedMap.isQuotientMap hr.isClosedMap hr
        (piToGk_galA_surjective D O V hV A hk hkres hrat hHL hVA)
    rw [hq.continuous_iff]
    have : (e.symm ∘ r) = fun σ => ((galA D O V hV A hk hkres hHL hVA σ :
        TempPi D O V hV) : TempPi D O V hV ⧸ deltaTemp D O V hV) := by
      funext σ
      apply e.injective
      rw [Function.comp_apply, MulEquiv.apply_symm_apply]
      rfl
    change Continuous (e.symm ∘ r)
    rw [this]
    exact continuous_quot_mk.comp (continuous_galA D O V hV A hk hkres hHL hVA)

include hrat in
@[simp] theorem tempQuotGk_mk (γ : TempPi D O V hV) :
    tempQuotGk D O V hV A hk hkres hrat hHL hVA (γ : TempPi D O V hV ⧸ deltaTemp D O V hV) =
      piToGk D (tempToPi D O V hV γ) := rfl

end

end Kummer

end TemperedFundamentalGroups
