/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueOverlapSucc
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueSpecial

/-!
# The restriction to an overlap at the bottom level (Blueprint §12.8, M2.5 (b))

In the setting of `NodeEtaleGlueOverlap` (a formally étale `B n`-algebra `M` over `D(g)` with
`γM : C1 → M/JM` a localization away from `ḡ`, and `ψ : Y n → M`), at a level with `J = 0`
(where `Y n ≃ C1`, `Input.yEquiv`):

* **`NodeEtaleGlue.Input.mk_ψ_yEquiv`**: `ψ (yEquiv c) ≡ γM c` modulo `J`, i.e. the restriction
  of the covering to the overlap is the given special-fibre map `γM`.

Proof: `glueM` is injective, and both `glueM (γM c)` and `mapYg (yEquiv c)` have the same
components in `G n[1/g] ≃ P n[1/g]` and `E n[1/g]`, which are determined by their reductions
(`red_φPn`, `γPn_eq`, `red_φEn`, `γEn_eq`) since `J = 0`.
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O} (I : Input θ cov₀ πL)
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (n : ℕ) (g : I.B0) {kg : ℕ}
  (hfg : I.T.f n ∣ algebraMap (I.B n) (I.R n) (algebraMap I.B0 (I.B n) g) ^ kg)
  {M : Type u} [CommRing M] [Algebra (I.B n) M] [Algebra.FormallyEtale (I.B n) M]
  [Algebra I.B0 M] [IsScalarTower I.B0 (I.B n) M]
  (γM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    I.C1 →ₐ[I.B n] M ⧸ EtaleNil.JB (J θ (R := I.B n)) M)
  (hM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    letI := γM.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) I.C1 (algebraMap I.B0 (I.B n) g))
      (M ⧸ EtaleNil.JB (J θ (R := I.B n)) M))
  (hJ0 : J θ (R := I.B n) = ⊥)

include hJ0 in
lemma mk_injective_of_eq_bot (X : Type u) [CommRing X] [Algebra (I.B n) X] :
    Function.Injective (Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) X)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rwa [Ideal.Quotient.eq_zero_iff_mem, EtaleNil.JB, hJ0, Ideal.map_bot, Ideal.mem_bot] at hx

/-- **At a level with `J = 0`, the restriction of the covering to the overlap is `γM`**:
`ψ (yEquiv c) ≡ γM c` modulo `J`. -/
theorem mk_ψ_yEquiv (c : I.C1) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) M)
      (I.ψ hθ hO n g hfg γM hM (I.yEquiv hθ hO hJ0 c)) = γM c := by
  set m : M := FormalPatchLevel.quotEquivOfEqBot hJ0 (I.B n) M (γM c) with hm
  have hmk : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) M) m = γM c :=
    FormalPatchLevel.mk_quotEquivOfEqBot hJ0 _
  suffices h : I.glueM hθ hO n g hfg γM hM m = I.mapYg hθ n g (I.yEquiv hθ hO hJ0 c) by
    change Ideal.Quotient.mk _ ((I.glueM hθ hO n g hfg γM hM).symm
      (I.mapYg hθ n g (I.yEquiv hθ hO hJ0 c))) = _
    rw [← h, AlgEquiv.symm_apply_apply, hmk]
  letI := algBP I.T I.B n
  refine I.Yg_ext hθ n g ?_ ?_
  · rw [fstYg_glueM, fstYg_mapYg, RingEquiv.symm_apply_eq, eGn_algebraMap]
    apply I.mk_injective_of_eq_bot n hJ0 (I.Pg n g)
    rw [← EtaleNil.red_mk, hmk, red_φPn]
    exact I.γPn_eq n g c _ (FormalPatchLevel.mk_toP (I.J_R_eq_bot hJ0) (I.T.f n)
      (I.T.level n).σP (I.ι₀ c))
  · letI := alg0 I.B I.B0 n (I.E n)
    rw [sndYg_glueM, sndYg_mapYg]
    apply I.mk_injective_of_eq_bot n hJ0 (ZariskiTwo.Lc g (I.E n))
    rw [← EtaleNil.red_mk, hmk, red_φEn]
    refine I.γEn_eq n g c _ ?_
    letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    change I.σE n (Ideal.Quotient.mk _ (I.φE hJ0 c)) = _
    rw [I.mk_φE hJ0 c, AlgEquiv.apply_symm_apply]

end Input

end NodeEtaleGlue

end

end SemistableReduction
