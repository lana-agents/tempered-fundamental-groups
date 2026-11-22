/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.IsGaloisGroup.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Localizing a Galois action at a submonoid of the base (generic)

MR13 step 7, D1 (S1b): for `G` acting on `B` over `A` and a submonoid `M ⊆ A`, `G` acts on
`B_M = Localization (algebraMapSubmonoid B M)` (**`GaloisLocalization.instAction`**,
`smul_algebraMap'`), and if `G` is a Galois group of `B/A` (and `B → B_M` is injective) it is
one of `B_M/A_M` (**`GaloisLocalization.isGaloisGroup`**). Used at the generic point `P_ℓ` of the
line `ℓ` (`A = T1`, `B = C.B₁`), where `A_M` is a discrete valuation ring and Mathlib's
fundamental identity applies.
-/

namespace SemistableReduction

namespace GaloisLocalization

noncomputable section

variable {A : Type*} (B : Type*) {G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B] (M : Submonoid A)

/-- `B_M`. -/
abbrev BM : Type _ := Localization (Algebra.algebraMapSubmonoid B M)

lemma le_comap (σ : G) : Algebra.algebraMapSubmonoid B M ≤
    (Algebra.algebraMapSubmonoid B M).comap (MulSemiringAction.toRingHom G B σ) := by
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨m, hm, ?_⟩
  simp [smul_algebraMap]

/-- The action of `σ` on `B_M`. -/
def ringHomAt (σ : G) : BM B M →+* BM B M :=
  IsLocalization.map (BM B M) (MulSemiringAction.toRingHom G B σ) (le_comap B M σ)

lemma ringHomAt_algebraMap (σ : G) (b : B) :
    ringHomAt B M σ (algebraMap B (BM B M) b) = algebraMap B (BM B M) (σ • b) :=
  IsLocalization.map_eq _ _

lemma ringHomAt_mul (σ τ : G) : ringHomAt B M (σ * τ) = (ringHomAt B M σ).comp (ringHomAt B M τ) :=
  IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B M) (RingHom.ext fun b ↦ by
    simp [ringHomAt_algebraMap, mul_smul])

lemma ringHomAt_one : ringHomAt B M (1 : G) = RingHom.id _ :=
  IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B M) (RingHom.ext fun b ↦ by
    simp [ringHomAt_algebraMap])

/-- `σ ↦ (B_M ≃+* B_M)`. -/
def toAut : G →* (BM B M ≃+* BM B M) where
  toFun σ := RingEquiv.ofRingHom (ringHomAt B M σ) (ringHomAt B M σ⁻¹)
    (by rw [← ringHomAt_mul, mul_inv_cancel, ringHomAt_one])
    (by rw [← ringHomAt_mul, inv_mul_cancel, ringHomAt_one])
  map_one' := by ext x; simp [ringHomAt_one]
  map_mul' σ τ := by ext x; simp [ringHomAt_mul]

/-- **`G` acts on `B_M`.** -/
instance instAction : MulSemiringAction G (BM B M) := MulSemiringAction.compHom _ (toAut B M)

lemma smul_def (σ : G) (x : BM B M) : σ • x = ringHomAt B M σ x := rfl

lemma smul_algebraMap' (σ : G) (b : B) :
    σ • algebraMap B (BM B M) b = algebraMap B (BM B M) (σ • b) := ringHomAt_algebraMap B M σ b

lemma smul_algebraMapA (σ : G) (a : A) :
    σ • algebraMap A (BM B M) a = algebraMap A (BM B M) a := by
  rw [IsScalarTower.algebraMap_apply A B (BM B M), smul_algebraMap' B M, smul_algebraMap]

instance : SMulCommClass G (Localization M) (BM B M) where
  smul_comm σ r x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_def, smul_def, map_mul]
    congr 1
    have : (ringHomAt B M σ).comp (algebraMap (Localization M) (BM B M)) =
        algebraMap (Localization M) (BM B M) :=
      IsLocalization.ringHom_ext M (RingHom.ext fun a ↦ by
        simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
        exact smul_algebraMapA B M σ a)
    exact DFunLike.congr_fun this r

/-- **A Galois group of `B/A` is one of `B_M/A_M`** (if `B → B_M` is injective). -/
theorem isGaloisGroup [hG : IsGaloisGroup G A B]
    (hinj : Function.Injective (algebraMap B (BM B M))) :
    IsGaloisGroup G (Localization M) (BM B M) where
  faithful := ⟨fun {σ τ} h ↦ by
    have := hG.faithful
    refine eq_of_smul_eq_smul fun b ↦ hinj ?_
    rw [← smul_algebraMap' B M, ← smul_algebraMap' B M, h]⟩
  commutes := inferInstance
  isInvariant := ⟨fun x hx ↦ by
    obtain ⟨⟨b, ⟨_, m, hm, rfl⟩⟩, hbx⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B M) x
    simp only at hbx
    have hb : ∀ σ : G, σ • b = b := fun σ ↦ by
      have h1 := congrArg (σ • ·) hbx
      simp only [smul_mul', hx σ, smul_algebraMap', smul_algebraMap] at h1
      exact hinj (h1.symm.trans hbx)
    obtain ⟨a, rfl⟩ := hG.isInvariant.isInvariant b hb
    refine ⟨IsLocalization.mk' (Localization M) a ⟨m, hm⟩, ?_⟩
    have hu := IsLocalization.map_units (BM B M) (⟨algebraMap A B m, m, hm, rfl⟩ :
      Algebra.algebraMapSubmonoid B M)
    refine (hu.mul_left_inj).mp ?_
    rw [hbx, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A (Localization M)
      (BM B M) m, ← map_mul, IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]⟩

end

end GaloisLocalization

end SemistableReduction
