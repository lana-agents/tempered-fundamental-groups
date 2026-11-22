/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspTame
import TemperedFundamentalGroups.SemistableReduction.KummerBaseChange

/-!
# Base change of étale-local cusp Kummer data along `O → O'` (MR12 S5.7 (c), part 1)

The cusp analogue of `KummerBaseChange`: for `ψ : N₁ → N₁'` over `O → O'` and an étale cusp chart
`O[X] → N₁`, `X ↦ t₁`:

* **`KummerBaseChange.nonempty_cuspEquiv`**: `N₁' ⊗_{O[X]} O[y] ≅ N₁' ⊗_{O'[X]} O'[y]`
  (`X ↦ y ^ d`; `O'[X] → N₁'`, `X ↦ ψ t₁`);
* **`KummerBaseChange.cuspNormSplit_baseChange`**: a splitting `Cusp.CuspNormSplit` of `Z` over `N₁`
  gives one of `N₁' ⊗_{N₁} Z` over `N₁'`, given the étaleness of the base-changed cusp chart and a
  prime `𝔫'` over `𝔫`.
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

open Cusp

namespace KummerBaseChange

noncomputable section

variable {O O' : Type u} [CommRing O] [CommRing O'] [Algebra O O']
  {N₁ N₁' : Type u} [CommRing N₁] [CommRing N₁'] [Algebra O N₁] [Algebra O' N₁']
  (ψ : N₁ →+* N₁')
  (hψ : ∀ a : O, ψ (algebraMap O N₁ a) = algebraMap O' N₁' (algebraMap O O' a))
  [Algebra O[X] N₁] [IsScalarTower O O[X] N₁] (d : ℕ)

set_option maxHeartbeats 800000 in
-- many tensor product and algebra structures
include hψ in
/-- **Base change of a cusp Kummer factor**: for `ψ : N₁ → N₁'` over `O → O'`,
`N₁' ⊗_{O[X]} O[y] ≅ N₁' ⊗_{O'[X]} O'[y]` (`X ↦ y ^ d`; `O'[X] → N₁'`, `X ↦ ψ t₁`). -/
theorem nonempty_cuspEquiv :
    letI : Algebra O[X] N₁' := (ψ.comp (algebraMap O[X] N₁)).toAlgebra
    letI : Algebra O'[X] N₁' := (aeval (ψ (algebraMap O[X] N₁ X))).toRingHom.toAlgebra
    Nonempty (N₁' ⊗[O[X]] KPoly O d ≃ₐ[N₁'] N₁' ⊗[O'[X]] KPoly O' d) := by
  letI : Algebra O[X] N₁' := (ψ.comp (algebraMap O[X] N₁)).toAlgebra
  letI : Algebra O'[X] N₁' := (aeval (ψ (algebraMap O[X] N₁ X))).toRingHom.toAlgebra
  have hT1 : ∀ y : O'[X], ((1 : N₁') ⊗ₜ[O'[X]] algebraMap O'[X] (KPoly O' d) y :
      N₁' ⊗[O'[X]] KPoly O' d) = algebraMap _ N₁' y ⊗ₜ 1 := one_tmul_algebraMap
  have hS1 : ∀ y : O[X], ((1 : N₁') ⊗ₜ[O[X]] algebraMap O[X] (KPoly O d) y :
      N₁' ⊗[O[X]] KPoly O d) = algebraMap _ N₁' y ⊗ₜ 1 := one_tmul_algebraMap
  have hC' : ∀ a : O', algebraMap O'[X] N₁' (C a) = algebraMap O' N₁' a := fun a ↦ aeval_C _ a
  have hX' : algebraMap O'[X] N₁' X = ψ (algebraMap O[X] N₁ X) := aeval_X _
  have hC : ∀ a : O, algebraMap O[X] N₁' (C a) = algebraMap O' N₁' (algebraMap O O' a) :=
    fun a ↦ by
      change ψ (algebraMap O[X] N₁ (algebraMap O O[X] a)) = _
      rw [← IsScalarTower.algebraMap_apply, hψ]
  have hX : algebraMap O[X] N₁' X = ψ (algebraMap O[X] N₁ X) := rfl
  -- forward
  letI aT : Algebra O[X] (N₁' ⊗[O'[X]] KPoly O' d) :=
    ((algebraMap N₁' _).comp (algebraMap O[X] N₁')).toAlgebra
  let bK : KPoly O d →+* KPoly O' d := Polynomial.mapRingHom (algebraMap O O')
  have bK_C : ∀ a : O, bK (C a) = (C (algebraMap O O' a) : O'[X]) := fun a ↦ map_C _
  have bK_X : bK (X : O[X]) = (X : O'[X]) := map_X _
  let gF₀ : KPoly O d →+* N₁' ⊗[O'[X]] KPoly O' d :=
    (Algebra.TensorProduct.includeRight :
      KPoly O' d →ₐ[O'[X]] N₁' ⊗[O'[X]] KPoly O' d).toRingHom.comp bK
  have gF₀_apply : ∀ x, gF₀ x = (1 : N₁') ⊗ₜ (bK x : KPoly O' d) := fun _ ↦ rfl
  have hgF : ∀ x : O[X], gF₀ (expand O d x) = algebraMap O[X] _ x := by
    intro x
    refine congrArg (fun f ↦ f x)
      (Polynomial.ringHom_ext (f := gF₀.comp (expand O d).toRingHom)
        (g := algebraMap O[X] _) (fun a ↦ ?_) ?_)
    · change (1 : N₁') ⊗ₜ (bK (expand O d (C a)) : KPoly O' d) =
        algebraMap N₁' _ (algebraMap O[X] N₁' (C a))
      rw [expand_C, bK_C, ← KPoly.algebraMap_C (e := d), hT1, hC', hC]
      rfl
    · change (1 : N₁') ⊗ₜ (bK (expand O d X) : KPoly O' d) =
        algebraMap N₁' _ (algebraMap O[X] N₁' X)
      have e1 : (bK (expand O d X) : O'[X]) = X ^ d := by
        change Polynomial.map (algebraMap O O') (expand O d X) = X ^ d
        rw [expand_X, Polynomial.map_pow, Polynomial.map_X]
      rw [e1]
      change (1 : N₁') ⊗ₜ ((KPoly.Y : KPoly O' d) ^ d) = _
      rw [KPoly.Y_pow, hT1, hX', hX]
      rfl
  let gF : KPoly O d →ₐ[O[X]] N₁' ⊗[O'[X]] KPoly O' d := { gF₀ with commutes' := hgF }
  let fF : N₁' →ₐ[O[X]] N₁' ⊗[O'[X]] KPoly O' d :=
    { algebraMap N₁' _ with commutes' := fun _ ↦ rfl }
  haveI := IsScalarTower.of_algebraMap_eq (R := O[X]) (S := O[X])
    (A := N₁' ⊗[O'[X]] KPoly O' d) fun _ ↦ rfl
  let F : N₁' ⊗[O[X]] KPoly O d →+* N₁' ⊗[O'[X]] KPoly O' d :=
    (Algebra.TensorProduct.lift fF gF fun _ _ ↦ Commute.all _ _).toRingHom
  have F_tmul : ∀ (a : N₁') (b : KPoly O d), F (a ⊗ₜ b) = algebraMap N₁' _ a * gF₀ b :=
    fun _ _ ↦ rfl
  -- backward
  letI aS : Algebra O' (N₁' ⊗[O[X]] KPoly O d) :=
    ((algebraMap N₁' _).comp (algebraMap O' N₁')).toAlgebra
  let gG₀ : O'[X] →ₐ[O'] N₁' ⊗[O[X]] KPoly O d :=
    aeval ((1 : N₁') ⊗ₜ (KPoly.Y : KPoly O d))
  have gG₀_one : gG₀ (1 : O'[X]) = 1 := map_one gG₀
  letI aS' : Algebra O'[X] (N₁' ⊗[O[X]] KPoly O d) :=
    ((algebraMap N₁' _).comp (algebraMap O'[X] N₁')).toAlgebra
  have hgG : ∀ x : O'[X], gG₀ (expand O' d x) = algebraMap O'[X] _ x := by
    intro x
    refine congrArg (fun f ↦ f x)
      (Polynomial.ringHom_ext (f := gG₀.toRingHom.comp (expand O' d).toRingHom)
        (g := algebraMap O'[X] _) (fun a ↦ ?_) ?_)
    · change gG₀ (expand O' d (C a)) = algebraMap N₁' _ (algebraMap O'[X] N₁' (C a))
      rw [expand_C, aeval_C, hC']
      rfl
    · change gG₀ (expand O' d X) = algebraMap N₁' _ (algebraMap O'[X] N₁' X)
      rw [expand_X, map_pow gG₀, aeval_X, Algebra.TensorProduct.tmul_pow, one_pow, KPoly.Y_pow,
        hS1, hX', hX]
      rfl
  let gG : KPoly O' d →ₐ[O'[X]] N₁' ⊗[O[X]] KPoly O d :=
    { gG₀.toRingHom with commutes' := hgG }
  let fG : N₁' →ₐ[O'[X]] N₁' ⊗[O[X]] KPoly O d :=
    { algebraMap N₁' _ with commutes' := fun _ ↦ rfl }
  haveI := IsScalarTower.of_algebraMap_eq (R := O'[X]) (S := O'[X])
    (A := N₁' ⊗[O[X]] KPoly O d) fun _ ↦ rfl
  let G : N₁' ⊗[O'[X]] KPoly O' d →+* N₁' ⊗[O[X]] KPoly O d :=
    (Algebra.TensorProduct.lift fG gG fun _ _ ↦ Commute.all _ _).toRingHom
  have G_tmul : ∀ (a : N₁') (b : KPoly O' d), G (a ⊗ₜ b) = algebraMap N₁' _ a * gG₀ b :=
    fun _ _ ↦ rfl
  have F_alg : ∀ a : N₁', F (algebraMap N₁' _ a) = algebraMap N₁' _ a := fun a ↦ by
    change F (a ⊗ₜ 1) = _
    rw [F_tmul, map_one, mul_one]
  have G_alg : ∀ a : N₁', G (algebraMap N₁' _ a) = algebraMap N₁' _ a := fun a ↦ by
    change G (a ⊗ₜ 1) = _
    rw [G_tmul]
    change _ * gG₀ (1 : O'[X]) = _
    rw [gG₀_one, mul_one]
  have hFG : F.comp G = RingHom.id _ := by
    refine Algebra.TensorProduct.ringHom_ext (RingHom.ext fun a ↦ ?_)
      (RingHom.ext fun b ↦ ?_)
    · change F (G (algebraMap N₁' _ a)) = algebraMap N₁' _ a
      rw [G_alg, F_alg]
    change F (G ((1 : N₁') ⊗ₜ b)) = (1 : N₁') ⊗ₜ b
    rw [G_tmul, map_one, one_mul]
    refine congrArg (fun f ↦ f b)
      (Polynomial.ringHom_ext (f := F.comp gG₀.toRingHom)
        (g := (Algebra.TensorProduct.includeRight :
          KPoly O' d →ₐ[O'[X]] N₁' ⊗[O'[X]] KPoly O' d).toRingHom) (fun a ↦ ?_) ?_)
    · change F (gG₀ (C a)) = (1 : N₁') ⊗ₜ (show KPoly O' d from C a)
      rw [aeval_C]
      change F (algebraMap N₁' _ (algebraMap O' N₁' a)) = _
      rw [F_alg, ← hC']
      change algebraMap O'[X] N₁' (C a) ⊗ₜ 1 = _
      rw [← hT1, KPoly.algebraMap_C]
    · change F (gG₀ X) = (1 : N₁') ⊗ₜ (show KPoly O' d from X)
      rw [aeval_X]
      change F ((1 : N₁') ⊗ₜ (show KPoly O d from X)) = _
      rw [F_tmul, map_one, one_mul, gF₀_apply, bK_X]
  have hGF : G.comp F = RingHom.id _ := by
    refine Algebra.TensorProduct.ringHom_ext (RingHom.ext fun a ↦ ?_)
      (RingHom.ext fun b ↦ ?_)
    · change G (F (algebraMap N₁' _ a)) = algebraMap N₁' _ a
      rw [F_alg, G_alg]
    change G (F ((1 : N₁') ⊗ₜ b)) = (1 : N₁') ⊗ₜ b
    rw [F_tmul, map_one, one_mul]
    refine congrArg (fun f ↦ f b)
      (Polynomial.ringHom_ext (f := G.comp gF₀)
        (g := (Algebra.TensorProduct.includeRight :
          KPoly O d →ₐ[O[X]] N₁' ⊗[O[X]] KPoly O d).toRingHom) (fun a ↦ ?_) ?_)
    · change G ((1 : N₁') ⊗ₜ bK (C a)) = (1 : N₁') ⊗ₜ (show KPoly O d from C a)
      rw [bK_C, ← KPoly.algebraMap_C (e := d), hT1, hC']
      change G (algebraMap N₁' _ (algebraMap O' N₁' (algebraMap O O' a))) = _
      rw [G_alg, ← hC]
      change algebraMap O[X] N₁' (C a) ⊗ₜ 1 = _
      rw [← hS1, KPoly.algebraMap_C]
    · change G ((1 : N₁') ⊗ₜ bK X) = (1 : N₁') ⊗ₜ (show KPoly O d from X)
      rw [bK_X, G_tmul]
      rw [map_one, one_mul]
      exact aeval_X _
  exact ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom F G hFG hGF) F_alg⟩

omit [Algebra O[X] N₁] [IsScalarTower O O[X] N₁] in
variable {ψ} in
include hψ in
/-- **Cusp Kummer splittings base change**: a splitting of `Z` over `N₁` into normalised cusp
Kummer factors gives one of `N₁' ⊗_{N₁} Z` over `N₁'` (for `O → O'`, `ψ : N₁ → N₁'`), given
the étaleness of the base-changed cusp chart `O'[X] → N₁'`, `X ↦ ψ t₁`, and a prime `𝔫'` over
`𝔫`. -/
theorem cuspNormSplit_baseChange {e : ℕ} {t₁ : N₁} {𝔫 : Ideal N₁} {Z : Type u} [CommRing Z]
    [Algebra N₁ Z] (hZ : CuspNormSplit O e t₁ 𝔫 Z) {𝔫' : Ideal N₁'} (h𝔫 : 𝔫 ≤ 𝔫'.comap ψ)
    (het : (aeval (ψ t₁) : O'[X] →ₐ[O'] N₁').toRingHom.Etale) :
    letI := ψ.toAlgebra
    CuspNormSplit O' e (ψ t₁) 𝔫' (N₁' ⊗[N₁] Z) := by
  letI := ψ.toAlgebra
  obtain ⟨palg, hT, hX, -, ht, r, d, hd, hde, ⟨Φ⟩⟩ := hZ
  letI := palg
  subst hX
  letI : Algebra O'[X] N₁' := (aeval (ψ (algebraMap O[X] N₁ X))).toRingHom.toAlgebra
  have hT' : IsScalarTower O' O'[X] N₁' := IsScalarTower.of_algebraMap_eq fun a ↦ (aeval_C _ a).symm
  refine ⟨inferInstance, hT', aeval_X _, RingHom.etale_algebraMap.mp het, h𝔫 ht, r, d, hd, hde,
    ⟨?_⟩⟩
  refine (Algebra.TensorProduct.congr AlgEquiv.refl Φ).trans
    ((Algebra.TensorProduct.piRight N₁ N₁' N₁' _).trans (AlgEquiv.piCongrRight fun i ↦ ?_))
  letI : Algebra O[X] N₁' := (ψ.comp (algebraMap O[X] N₁)).toAlgebra
  haveI : IsScalarTower O[X] N₁ N₁' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine (Algebra.TensorProduct.cancelBaseChange O[X] N₁ N₁' N₁' (KPoly O (d i))).trans ?_
  exact (nonempty_cuspEquiv ψ hψ (d i)).some

end

end KummerBaseChange

end SemistableReduction
