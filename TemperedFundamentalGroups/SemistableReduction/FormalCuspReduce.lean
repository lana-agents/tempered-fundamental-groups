/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerNode
import TemperedFundamentalGroups.SemistableReduction.CuspCover

/-!
# Reduction of cusp factors to the special fibre (MR12 T2 S5.5, reduction)

Let `N₁` be an `O[X]`-algebra (the étale-local coordinate `t = X` at a cusp) and
`N₁ ⊗_{O[X]} O[y]` (`X ↦ y ^ d`, `Cusp.CuspNormalFactor`) a normalised cusp factor. Modulo
`J = (ker θ)·`:

* **`FormalKummer.cuspFactorEquiv`**: `(N₁ ⊗_{O[X]} O[y])/J ≃ (N₁/J) ⊗_{k[X]} k[y]`, where `k[X]`
  acts on `N₁/J` through `X ↦ t̄` (`cuspBar`);
* **`FormalKummer.cuspSplitEquiv`**: for an `N₁`-algebra `X` with `Φ : X ≅ ∏ᵢ N₁ ⊗_{O[X]} O[y]`
  (`X ↦ y ^ dᵢ`), `X/JX ≃ ∏ᵢ (N₁/J) ⊗_{k[X]} k[y]`, compatibly with the maps from `N₁`.

This is the cusp analogue of `FormalKummerReduce` (`TensorQuotTensor.equiv` for
`O[X] → k[X]`, `O[y] → k[y]`).
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

open AdmissibleLift Cusp

namespace FormalKummer

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)]

section Factor

variable {N₁ : Type u} [CommRing N₁] [Algebra O N₁] [Algebra O[X] N₁] [IsScalarTower O O[X] N₁]
  {d : ℕ}

variable (θ N₁) in
/-- `k[X] → N₁/J`, `X ↦ t̄` (`t` the image of `X` in `N₁`). -/
def cuspBar : k[X] →+* N₁ ⧸ J θ (R := N₁) :=
  eval₂RingHom (algebraMap k _) (Ideal.Quotient.mk _ (algebraMap O[X] N₁ X))

variable (θ N₁) in
/-- The algebra structure of `cuspBar`. -/
abbrev cuspBarAlg : Algebra k[X] (N₁ ⧸ J θ (R := N₁)) := (cuspBar θ N₁).toAlgebra

lemma mk_algebraMap_poly (p : O[X]) :
    Ideal.Quotient.mk (J θ (R := N₁)) (algebraMap O[X] N₁ p) = cuspBar θ N₁ (p.map θ) := by
  have := Polynomial.ringHom_ext (f := (Ideal.Quotient.mk (J θ (R := N₁))).comp
      (algebraMap O[X] N₁)) (g := (cuspBar θ N₁).comp (mapRingHom θ))
    (fun o ↦ by
      simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C, cuspBar,
        coe_eval₂RingHom, eval₂_C]
      rw [show (C o : O[X]) = algebraMap O O[X] o from rfl, ← IsScalarTower.algebraMap_apply]
      exact (QuadNodeTower.algK_θ N₁ o).symm)
    (by simp [cuspBar])
  exact RingHom.congr_fun this p

/-- The ideal `(ker θ)·O[X]`. -/
abbrev KX : Ideal O[X] := (RingHom.ker θ).map (algebraMap O O[X])

omit hθ in
lemma map_KX : (KX (θ := θ)).map (algebraMap O[X] N₁) = J θ := by
  rw [KX, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- `O[X] → k[X]`. -/
abbrev algPP : Algebra O[X] k[X] := (mapRingHom θ).toAlgebra

/-- `O[X] → k[y]` (`X ↦ y ^ d` after reduction). -/
abbrev algPK : Algebra O[X] (KPoly k d) :=
  ((algebraMap k[X] (KPoly k d)).comp (mapRingHom θ)).toAlgebra

omit hθ in
lemma ker_map_KPoly : RingHom.ker (mapRingHom θ : KPoly O d →+* KPoly k d) =
    (KX (θ := θ)).map (algebraMap O[X] (KPoly O d)) := by
  change RingHom.ker (mapRingHom θ) = _
  rw [ker_mapRingHom, KX, Ideal.map_map]
  congr 1
  exact RingHom.ext fun o ↦ by
    change C o = expand O d (algebraMap O O[X] o)
    rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, expand_C]

/-- **The reduction of a normalised cusp factor**:
`(N₁ ⊗_{O[X]} O[y])/K ≃ (N₁/J) ⊗_{k[X]} k[y]`. -/
def cuspFactorEquiv :
    (CuspNormalFactor O d N₁ ⧸
        TensorQuotTensor.KT (KX (θ := θ)) (S := N₁) (B := KPoly O d)) ≃+*
      (letI := cuspBarAlg θ N₁; (N₁ ⧸ J θ (R := N₁)) ⊗[k[X]] KPoly k d) :=
  letI := cuspBarAlg θ N₁
  letI := algPP (θ := θ)
  letI := algPK (θ := θ) (d := d)
  haveI : IsScalarTower O[X] k[X] (N₁ ⧸ J θ (R := N₁)) :=
    IsScalarTower.of_algebraMap_eq fun p ↦ mk_algebraMap_poly p
  haveI : IsScalarTower O[X] k[X] (KPoly k d) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let σₐ : N₁ →ₐ[O[X]] N₁ ⧸ J θ (R := N₁) := Ideal.Quotient.mkₐ O[X] (J θ (R := N₁))
  let βₐ : KPoly O d →ₐ[O[X]] KPoly k d :=
    { (mapRingHom θ : KPoly O d →+* KPoly k d) with
      commutes' := fun p ↦ by
        change Polynomial.map θ (expand O d p) = expand k d (Polynomial.map θ p)
        exact map_expand }
  TensorQuotTensor.equiv (σ := σₐ) (β := βₐ) (KX (θ := θ))
    (by
      change RingHom.ker (mapRingHom θ) = _
      rw [ker_mapRingHom]
      rfl)
    (Polynomial.map_surjective _ hθ.out) Ideal.Quotient.mk_surjective
    (Polynomial.map_surjective _ hθ.out)
    (by
      change RingHom.ker (Ideal.Quotient.mk (J θ (R := N₁))) = _
      rw [Ideal.mk_ker, map_KX])
    (ker_map_KPoly (θ := θ))

lemma cuspFactorEquiv_mk_tmul (x : N₁) (b : KPoly O d) :
    letI := cuspBarAlg θ N₁
    cuspFactorEquiv (θ := θ) (N₁ := N₁) (d := d) (Ideal.Quotient.mk
      (TensorQuotTensor.KT (KX (θ := θ)) (S := N₁) (B := KPoly O d)) (x ⊗ₜ b)) =
      Ideal.Quotient.mk (J θ (R := N₁)) x ⊗ₜ[k[X]]
        (show KPoly k d from Polynomial.map θ b) :=
  letI := cuspBarAlg θ N₁
  letI := algPP (θ := θ)
  letI := algPK (θ := θ) (d := d)
  haveI : IsScalarTower O[X] k[X] (N₁ ⧸ J θ (R := N₁)) :=
    IsScalarTower.of_algebraMap_eq fun p ↦ mk_algebraMap_poly p
  haveI : IsScalarTower O[X] k[X] (KPoly k d) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  TensorQuotTensor.equiv_mk_tmul ..

omit hθ in
/-- The ideal `K` of a cusp factor is generated by `J ⊆ N₁`. -/
lemma KT_eq_cusp :
    TensorQuotTensor.KT (KX (θ := θ)) (S := N₁) (B := KPoly O d) =
      (J θ (R := N₁)).map (algebraMap N₁ (CuspNormalFactor O d N₁)) := by
  rw [TensorQuotTensor.KT, IsScalarTower.algebraMap_eq O[X] N₁ (CuspNormalFactor O d N₁),
    ← Ideal.map_map, map_KX]

end Factor

section Split

variable {N₁ : Type u} [CommRing N₁] [Algebra O N₁] [Algebra O[X] N₁] [IsScalarTower O O[X] N₁]
  {Y : Type u} [CommRing Y] [Algebra N₁ Y] {r : ℕ} {d : Fin r → ℕ}

variable (θ N₁) in
/-- The reduced cusp factors `(N₁/J) ⊗_{k[X]} k[y]`. -/
abbrev RedCusp (e : ℕ) : Type u :=
  letI := cuspBarAlg θ N₁
  (N₁ ⧸ J θ (R := N₁)) ⊗[k[X]] KPoly k e

/-- **The reduction of a cusp splitting**: for `Φ : Y ≅ ∏ᵢ N₁ ⊗_{O[X]} O[y]` (over `N₁`),
`Y/JY ≃ ∏ᵢ (N₁/J) ⊗_{k[X]} k[y]`. -/
def cuspSplitEquiv (Φ : Y ≃ₐ[N₁] ∀ i, CuspNormalFactor O (d i) N₁) :
    (Y ⧸ JX (θ := θ) (N₁ := N₁) (X := Y)) ≃+* ∀ i, RedCusp θ N₁ (d i) :=
  (Ideal.quotientEquiv _ _ Φ.toRingEquiv (JX_eq_map Φ)).trans
    ((PiQuot.equiv (J θ (R := N₁)) (fun i ↦ CuspNormalFactor O (d i) N₁)).trans
      (RingEquiv.piCongrRight fun i ↦
        (Ideal.quotEquivOfEq (KT_eq_cusp (θ := θ) (N₁ := N₁) (d := d i)).symm).trans
          cuspFactorEquiv))

lemma cuspSplitEquiv_algebraMap (Φ : Y ≃ₐ[N₁] ∀ i, CuspNormalFactor O (d i) N₁) (x : N₁)
    (i : Fin r) :
    cuspSplitEquiv Φ
        ((Ideal.Quotient.mk (JX (θ := θ) (N₁ := N₁) (X := Y))) (algebraMap N₁ Y x)) i =
      letI := cuspBarAlg θ N₁
      Ideal.Quotient.mk (J θ (R := N₁)) x ⊗ₜ[k[X]] (1 : KPoly k (d i)) := by
  have h1 : Φ (algebraMap N₁ Y x) i = x ⊗ₜ (1 : KPoly O (d i)) := by
    rw [Φ.commutes]
    rfl
  change cuspFactorEquiv (Ideal.quotEquivOfEq (KT_eq_cusp (θ := θ) (N₁ := N₁) (d := d i)).symm
    (Ideal.Quotient.mk ((J θ (R := N₁)).map (algebraMap N₁ (CuspNormalFactor O (d i) N₁)))
      (Φ (algebraMap N₁ Y x) i))) = _
  rw [Ideal.quotEquivOfEq_mk, h1, cuspFactorEquiv_mk_tmul]
  letI := cuspBarAlg θ N₁
  exact congrArg (_ ⊗ₜ[k[X]] ·) (Polynomial.map_one θ)

end Split

end

end FormalKummer

end SemistableReduction
