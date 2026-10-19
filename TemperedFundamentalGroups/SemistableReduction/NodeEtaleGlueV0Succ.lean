/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueOverlapSucc

/-!
# The successor maps of the piece over the overlap (Blueprint §12.8, M2.3 (f), tower)

For `V : NodeEtaleGlue.Overlap I` with the successor maps `sP n : P0 (n+1) → P0 n` of the piece
over `D(c₀) ⊆ V₀` (`Piece0`):

* **`Overlap.sM n : M (n+1) → M n`**: the localization of `sP n` away from `x₀`
  (`M n = P0 n[1/x₀]`, `Piece0.sM`), `sM_algebraMap`, `sM_algebraMapO` (it is `O`-linear);
* `Overlap.sMbar n`: its reduction `M (n+1)/J → M n/J`;
* **`Overlap.γM_succ`**: the special fibres `γM : C1 → M/J` are compatible with the successor
  maps (`Piece0.hℓ0succ`; the overlap datum `ω` is the same at all levels).
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (n : ℕ)

/-- **The successor map of the piece over the overlap** (`Piece0.sM`). -/
abbrev sM : V.M (n + 1) →+* V.M n := V.P0.sM n

lemma sM_algebraMap (e : V.P0.P (n + 1)) :
    V.sM n (algebraMap (V.P0.P (n + 1)) (V.M (n + 1)) e) =
      algebraMap (V.P0.P n) (V.M n) (V.P0.sP n e) :=
  V.P0.hsM n e

lemma sP_algebraMapO (o : O) :
    V.P0.sP n (algebraMap O (V.P0.P (n + 1)) o) = algebraMap O (V.P0.P n) o := by
  rw [IsScalarTower.algebraMap_apply O (V.B' (n + 1)) (V.P0.P (n + 1)), V.P0.hsP,
    ← IsScalarTower.algebraMap_apply O (V.B' (n + 1)) (V.B' n),
    ← IsScalarTower.algebraMap_apply]

/-- `sM` is `O`-linear. -/
lemma sM_algebraMapO (o : O) :
    V.sM n (algebraMap O (V.M (n + 1)) o) = algebraMap O (V.M n) o := by
  rw [IsScalarTower.algebraMap_apply O (V.P0.P (n + 1)) (V.M (n + 1)), sM_algebraMap,
    sP_algebraMapO, ← IsScalarTower.algebraMap_apply]

/-- The ideal `J` of `M n` is `(ker θ) M n`. -/
lemma JB_M : (letI := V.algBM n; EtaleNil.JB (J θ (R := I.B n)) (V.M n)) =
    (RingHom.ker θ).map (algebraMap O (V.M n)) := by
  letI := V.algBM n
  haveI := OverlapPiece.towerOB (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n) (V.P0.P n) (O := O)
    (Bn := I.B n)
  exact OverlapPiece.JB_map _

lemma JB_M_le : (letI := V.algBM (n + 1); EtaleNil.JB (J θ (R := I.B (n + 1))) (V.M (n + 1))) ≤
    (letI := V.algBM n; EtaleNil.JB (J θ (R := I.B n)) (V.M n)).comap (V.sM n) := by
  rw [JB_M, JB_M, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro o ho
  rw [Ideal.mem_comap, RingHom.comp_apply, sM_algebraMapO]
  exact Ideal.mem_map_of_mem _ ho

/-- **The reduction of `sM`**: `M (n+1)/J → M n/J`. -/
def sMbar : (letI := V.algBM (n + 1); V.M (n + 1) ⧸ EtaleNil.JB (J θ (R := I.B (n + 1)))
    (V.M (n + 1))) →+* (letI := V.algBM n; V.M n ⧸ EtaleNil.JB (J θ (R := I.B n)) (V.M n)) :=
  Ideal.quotientMap _ (V.sM n) (V.JB_M_le n)

lemma sMbar_mk (m : V.M (n + 1)) :
    V.sMbar n (Ideal.Quotient.mk _ m) = Ideal.Quotient.mk _ (V.sM n m) :=
  Ideal.quotientMap_mk

omit [Field k] in
/-- A map of quotients applied to an element given through a change of the ideal. -/
lemma quotientMap_quotEquivOfEq {A A' : Type u} [CommRing A] [CommRing A'] {I I₀ : Ideal A}
    {I' I₀' : Ideal A'} (h : I₀ = I) (h' : I₀' = I') (s : A →+* A') (hs : I ≤ I'.comap s)
    (x : A ⧸ I₀) (y : A' ⧸ I₀')
    (hxy : ∀ m, Ideal.Quotient.mk I₀ m = x → Ideal.Quotient.mk I₀' (s m) = y) :
    Ideal.quotientMap I' s hs (Ideal.quotEquivOfEq h x) = Ideal.quotEquivOfEq h' y := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotEquivOfEq_mk, Ideal.quotientMap_mk, ← hxy m rfl, Ideal.quotEquivOfEq_mk]

/-- The special fibre maps `C0 → M n/J` (`Piece0.ℓ0`) are compatible with the successor
maps. -/
lemma ℓ0_succ (c : V.C0) :
    V.sMbar n (Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ)
      (algebraMap V.B0' (V.B' (n + 1)) V.x0) (V.hWn0 (n + 1)) (V.P0.P (n + 1))
        (Bn := I.B (n + 1))) (V.P0.ℓ0 (n + 1) c)) =
    Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ)
      (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n) (V.P0.P n) (Bn := I.B n)) (V.P0.ℓ0 n c) := by
  exact quotientMap_quotEquivOfEq _ _ (V.sM n) (V.JB_M_le n) _ _ (V.P0.hℓ0succ n c)

/-- **The special fibres of `M` are compatible with the successor maps.** -/
theorem γM_succ (c : I.C1) : V.sMbar n (V.γM (n + 1) c) = V.γM n c := by
  have h : (V.sMbar n).comp ((Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ)
      (algebraMap V.B0' (V.B' (n + 1)) V.x0) (V.hWn0 (n + 1)) (V.P0.P (n + 1))
        (Bn := I.B (n + 1)))).toRingHom.comp
      (OverlapPiece.ℓx (RingHom.ker θ) (algebraMap V.B0' (V.B' (n + 1)) V.x0) (V.P0.P (n + 1))
        V.x0s V.c0s (V.P0.ℓ0 (n + 1)) (V.P0.hℓ0loc (n + 1)))) =
      (Ideal.quotEquivOfEq (OverlapPiece.JB_eq (RingHom.ker θ)
        (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n) (V.P0.P n) (Bn := I.B n))).toRingHom.comp
      (OverlapPiece.ℓx (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0) (V.P0.P n)
        V.x0s V.c0s (V.P0.ℓ0 n) (V.P0.hℓ0loc n)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap V.Bs' V.C0 V.x0s))
      (RingHom.ext fun c ↦ ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      OverlapPiece.ℓx_algebraMap]
    exact V.ℓ0_succ n c
  exact RingHom.congr_fun h (V.ω.symm (algebraMap I.C1 _ c))

lemma sM_algWM (w : V.W (n + 1)) :
    V.sM n (letI := V.algWM (n + 1); algebraMap (V.W (n + 1)) (V.M (n + 1)) w) =
      (letI := V.algWM n; algebraMap (V.W n) (V.M n) (algebraMap (V.W (n + 1)) (V.W n) w)) := by
  letI := V.algWM (n + 1)
  letI := V.algWM n
  haveI := V.hWn0 (n + 1)
  have : (V.sM n).comp (algebraMap (V.W (n + 1)) (V.M (n + 1))) =
      (algebraMap (V.W n) (V.M n)).comp (algebraMap (V.W (n + 1)) (V.W n)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap V.B0' (V.B' (n + 1)) V.x0))
      (RingHom.ext fun y ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [V.hWs0, OverlapPiece.algWM_algebraMap, OverlapPiece.algWM_algebraMap,
      IsScalarTower.algebraMap_apply (V.B' (n + 1)) (V.P0.P (n + 1)) (V.M (n + 1)), sM_algebraMap,
      V.P0.hsP, ← IsScalarTower.algebraMap_apply]
  exact RingHom.congr_fun this w

/-- `sM` is semilinear over the levels of the first chart. -/
lemma sM_algB (x : I.B (n + 1)) :
    V.sM n (letI := V.algBM (n + 1); algebraMap (I.B (n + 1)) (V.M (n + 1)) x) =
      (letI := V.algBM n; algebraMap (I.B n) (V.M n) (algebraMap (I.B (n + 1)) (I.B n) x)) := by
  letI := V.algWM (n + 1)
  letI := V.algWM n
  change V.sM n (algebraMap (V.W (n + 1)) (V.M (n + 1)) (algebraMap (I.B (n + 1)) _ x)) =
    algebraMap (V.W n) (V.M n) (algebraMap (I.B n) _ (algebraMap (I.B (n + 1)) (I.B n) x))
  rw [sM_algWM, V.hWs1]

/-- The successor maps on special fibres, elementwise. -/
lemma mk_sM (c : I.C1) (m : V.M (n + 1))
    (hm : Ideal.Quotient.mk (letI := V.algBM (n + 1)
      EtaleNil.JB (J θ (R := I.B (n + 1))) (V.M (n + 1))) m = V.γM (n + 1) c) :
    Ideal.Quotient.mk (letI := V.algBM n; EtaleNil.JB (J θ (R := I.B n)) (V.M n)) (V.sM n m) =
      V.γM n c := by
  rw [← sMbar_mk, hm, γM_succ]

variable (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The restriction maps commute with the successor maps**:
`sM n ∘ ψ (n+1) = ψ n ∘ Ymap n` (`Input.ψ_succ`). -/
theorem ψ_succ (y : I.Y hθ (n + 1)) :
    V.sM n (V.ψ hθ hO (n + 1) y) = V.ψ hθ hO n (I.Ymap hθ hO n y) := by
  letI := V.algBM n
  letI := V.alg0M n
  haveI := V.formallyEtale_M n
  haveI := V.tower0M n
  letI := V.algBM (n + 1)
  letI := V.alg0M (n + 1)
  haveI := V.formallyEtale_M (n + 1)
  haveI := V.tower0M (n + 1)
  exact I.ψ_succ hθ hO n V.g (V.hfg n) (V.hfg (n + 1)) (V.γM n) (V.isLocalization_γM n)
    (V.γM (n + 1)) (V.isLocalization_γM (n + 1)) (V.sM n) (V.sM_algB n) (V.mk_sM n) y

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
