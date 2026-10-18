/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# Glueing algebras along a cover by two basic opens (generic commutative algebra)

For `a, b ∈ R`, an `R`-algebra `Ba` over `D(a)`, an `R`-algebra `Bb` over `D(b)` and an
`R`-algebra `Bab` with `R`-algebra maps `ρa : Ba → Bab`, `ρb : Bb → Bab` exhibiting `Bab` as
`Ba[1/b]` and as `Bb[1/a]`, the **glued algebra** is the fibre product
`ZariskiTwo.glued ρa ρb = Ba ×_{Bab} Bb`. (This is the two-piece case of
`ZariskiDescent.Datum`, in a form without the indexing by finite sets.)

* **`ZariskiTwo.isLocalization_fst`** / **`isLocalization_snd`**: `Ba = glued[1/a]`,
  `Bb = glued[1/b]` (no hypothesis on `a, b`);
* if `a, b` generate the unit ideal: `finite_glued` (finite over `R` if `Ba`, `Bb` are finite over
  `R[1/a]`, `R[1/b]`), `flat_glued_of` (flat over a base `A` if `Ba`, `Bb` are), and
  **`bijective_lift`** (uniqueness: an `R`-algebra `M` with compatible maps to `Ba`, `Bb` that are
  localizations away from `a`, `b` is the glued algebra; Stacks, Lemma 10.24.1, Tag 00EK), via
  Mathlib's `Module.Finite.of_localizationSpan'`, `Module.flat_of_isLocalized_span`,
  `bijective_of_isLocalized_span`.
-/

universe u

namespace ZariskiTwo

variable {R : Type u} [CommRing R] (a b : R)
  {Ba Bb Bab : Type u} [CommRing Ba] [CommRing Bb] [CommRing Bab]
  [Algebra R Ba] [Algebra R Bb] [Algebra R Bab]
  (ρa : Ba →ₐ[R] Bab) (ρb : Bb →ₐ[R] Bab)

/-- The **glued algebra** `Ba ×_{Bab} Bb`. -/
def glued : Subalgebra R (Ba × Bb) where
  carrier := {p | ρa p.1 = ρb p.2}
  mul_mem' {p q} hp hq := by
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at hp hq ⊢
    rw [hp, hq]
  add_mem' {p q} hp hq := by
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, map_add] at hp hq ⊢
    rw [hp, hq]
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq, Prod.algebraMap_apply, AlgHom.commutes]

lemma mem_glued {p : Ba × Bb} : p ∈ glued ρa ρb ↔ ρa p.1 = ρb p.2 := Iff.rfl

/-- The projection to `Ba`. -/
def fst : glued ρa ρb →ₐ[R] Ba := (AlgHom.fst R Ba Bb).comp (glued ρa ρb).val

/-- The projection to `Bb`. -/
def snd : glued ρa ρb →ₐ[R] Bb := (AlgHom.snd R Ba Bb).comp (glued ρa ρb).val

@[simp] lemma fst_apply (p : glued ρa ρb) : fst ρa ρb p = p.1.1 := rfl

@[simp] lemma snd_apply (p : glued ρa ρb) : snd ρa ρb p = p.1.2 := rfl

lemma fst_snd (p : glued ρa ρb) : ρa (fst ρa ρb p) = ρb (snd ρa ρb p) := p.2

variable {ρa ρb}

/-- The algebra structure of `Ba` over the glued algebra. -/
@[reducible] def algebraFst : Algebra (glued ρa ρb) Ba := (fst ρa ρb).toRingHom.toAlgebra

/-- The algebra structure of `Bb` over the glued algebra. -/
@[reducible] def algebraSnd : Algebra (glued ρa ρb) Bb := (snd ρa ρb).toRingHom.toAlgebra

section Fst

variable (ha : IsUnit (algebraMap R Ba a))
  (hb : letI := ρb.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Bb a) Bab)
include ha hb

/-- **`Ba` is the localization of the glued algebra away from `a`.** -/
theorem isLocalization_fst :
    letI := algebraFst (ρa := ρa) (ρb := ρb)
    IsLocalization.Away (algebraMap R (glued ρa ρb) a) Ba := by
  letI := algebraFst (ρa := ρa) (ρb := ρb)
  letI := ρb.toRingHom.toAlgebra
  have hm : ∀ p : glued ρa ρb, algebraMap (glued ρa ρb) Ba p = p.1.1 := fun _ ↦ rfl
  have hρ : ∀ y : Bb, algebraMap Bb Bab y = ρb y := fun _ ↦ rfl
  refine (isLocalization_iff ..).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [hm]
    simpa using ha.pow n
  · intro x
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, hy⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap R Bb a)) (ρa x)
    simp only [hρ, map_pow, AlgHom.commutes] at hy
    refine ⟨⟨⟨(x * algebraMap R Ba a ^ n, y), ?_⟩, ⟨_, n, rfl⟩⟩, ?_⟩
    · change ρa (x * algebraMap R Ba a ^ n) = ρb y
      rw [map_mul, map_pow, AlgHom.commutes, hy]
    · simp [hm]
  · intro p q hpq
    rw [hm, hm] at hpq
    have h2 : ρb (p.1.2 - q.1.2) = 0 := by
      rw [map_sub, ← p.2, ← q.2, hpq, sub_self]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (algebraMap R Bb a)) Bab (p.1.2 - q.1.2)).1 h2
    refine ⟨⟨_, n, rfl⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp [hpq]
    · have : ((algebraMap R (glued ρa ρb) a ^ n * p : glued ρa ρb) : Ba × Bb).2 =
          algebraMap R Bb a ^ n * p.1.2 := rfl
      have h' : ((algebraMap R (glued ρa ρb) a ^ n * q : glued ρa ρb) : Ba × Bb).2 =
          algebraMap R Bb a ^ n * q.1.2 := rfl
      rw [this, h', ← sub_eq_zero, ← mul_sub]
      exact hn

/-- `fst`, as an `R`-linear map, is a localization away from `a`. -/
theorem isLocalizedModule_fst :
    IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap := by
  letI := algebraFst (ρa := ρa) (ρb := ρb)
  haveI : IsScalarTower R (glued ρa ρb) Ba :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((fst ρa ρb).commutes r).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (glued ρa ρb) (Submonoid.powers a)) Ba := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact isLocalization_fst a ha hb
  exact isLocalizedModule_iff_isLocalization.mpr this

end Fst

section Snd

variable (hb' : IsUnit (algebraMap R Bb b))
  (ha' : letI := ρa.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Ba b) Bab)
include hb' ha'

/-- The glued algebra with the roles of the pieces exchanged. -/
def swapEquiv : glued ρa ρb ≃ₐ[R] glued ρb ρa where
  toFun p := ⟨(p.1.2, p.1.1), p.2.symm⟩
  invFun p := ⟨(p.1.2, p.1.1), p.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit hb' ha' in
lemma snd_eq (p : glued ρa ρb) : snd ρa ρb p = fst ρb ρa (swapEquiv p) := rfl

/-- `snd`, as an `R`-linear map, is a localization away from `b`. -/
theorem isLocalizedModule_snd :
    IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap := by
  have h := isLocalizedModule_fst (ρa := ρb) (ρb := ρa) b hb' ha'
  have : (snd ρa ρb).toLinearMap =
      (fst ρb ρa).toLinearMap ∘ₗ (swapEquiv (ρa := ρa) (ρb := ρb)).toLinearEquiv.toLinearMap :=
    rfl
  rw [this]
  exact IsLocalizedModule.of_linearEquiv_right _ _ _

end Snd

/-- A piece finite over the localization of the base gives a finite localization of the glued
algebra. -/
lemma finite_localized_of {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (c : R) [Module (Localization.Away c) N] [IsScalarTower R (Localization.Away c) N]
    (φ : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers c) φ]
    (H : Module.Finite (Localization.Away c) N) :
    Module.Finite (Localization.Away c) (LocalizedModule (Submonoid.powers c) M) := by
  let e : LocalizedModule (Submonoid.powers c) M ≃ₗ[R] N := IsLocalizedModule.iso _ φ
  let e' := e.extendScalarsOfIsLocalization (Submonoid.powers c) (Localization.Away c)
  exact Module.Finite.equiv e'.symm

section Span

variable (hab : Ideal.span {a, b} = ⊤)
  [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap]
include hab

/-- **Finiteness**: if `a, b` generate the unit ideal and `Ba`, `Bb` are finite over `R[1/a]`,
`R[1/b]`, the glued algebra is a finite `R`-module. -/
theorem finite_glued [Module (Localization.Away a) Ba] [IsScalarTower R (Localization.Away a) Ba]
    [Module (Localization.Away b) Bb] [IsScalarTower R (Localization.Away b) Bb]
    (hBa : Module.Finite (Localization.Away a) Ba) (hBb : Module.Finite (Localization.Away b) Bb) :
    Module.Finite R (glued ρa ρb) := by
  refine Module.Finite.of_localizationSpan' ({a, b} : Set R) hab
    (Rₚ := fun g ↦ Localization.Away g.val)
    (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.val) (glued ρa ρb)) fun g ↦ ?_
  obtain ⟨g, hg⟩ := g
  rcases hg with rfl | hg
  · exact finite_localized_of _ (fst ρa ρb).toLinearMap hBa
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact finite_localized_of _ (snd ρa ρb).toLinearMap hBb

/-- The map from an algebra with compatible maps to the pieces into the glued algebra. -/
def lift {M : Type u} [CommRing M] [Algebra R M] (φa : M →ₐ[R] Ba) (φb : M →ₐ[R] Bb)
    (h : ∀ x, ρa (φa x) = ρb (φb x)) : M →ₐ[R] glued ρa ρb :=
  (φa.prod φb).codRestrict (glued ρa ρb) h

omit hab [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap] in
@[simp] lemma fst_lift {M : Type u} [CommRing M] [Algebra R M] (φa : M →ₐ[R] Ba)
    (φb : M →ₐ[R] Bb) (h : ∀ x, ρa (φa x) = ρb (φb x)) (x : M) :
    fst ρa ρb (lift φa φb h x) = φa x := rfl

omit hab [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap] in
@[simp] lemma snd_lift {M : Type u} [CommRing M] [Algebra R M] (φa : M →ₐ[R] Ba)
    (φb : M →ₐ[R] Bb) (h : ∀ x, ρa (φa x) = ρb (φb x)) (x : M) :
    snd ρa ρb (lift φa φb h x) = φb x := rfl

omit hab in
/-- A map between two localizations of the same piece is bijective on the localizations. -/
lemma bijective_map_of {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R P] (c : R) (φ : M →ₗ[R] P) (ψ : N →ₗ[R] P)
    [IsLocalizedModule (Submonoid.powers c) φ] [IsLocalizedModule (Submonoid.powers c) ψ]
    (F : M →ₗ[R] N) (hF : ∀ x, ψ (F x) = φ x) :
    Function.Bijective (IsLocalizedModule.map (Submonoid.powers c)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) N) F) := by
  let e₁ := IsLocalizedModule.iso (Submonoid.powers c) φ
  let e₂ := IsLocalizedModule.iso (Submonoid.powers c) ψ
  have hc : (e₂ : _ →ₗ[R] P) ∘ₗ IsLocalizedModule.map (Submonoid.powers c)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) N) F = (e₁ : _ →ₗ[R] P) := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers c)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) M) φ
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [IsLocalizedModule.map_apply, LocalizedModule.mkLinearMap_apply,
      LocalizedModule.mkLinearMap_apply, IsLocalizedModule.iso_mk_one,
      IsLocalizedModule.iso_mk_one, hF]
  have hm : ⇑(IsLocalizedModule.map (Submonoid.powers c)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) N) F) = e₂.symm ∘ e₁ := by
    funext y
    rw [Function.comp_apply, LinearEquiv.eq_symm_apply]
    exact LinearMap.congr_fun hc y
  rw [hm]
  exact e₂.symm.bijective.comp e₁.bijective

/-- **Uniqueness of the glueing** (the sheaf property, Stacks, Lemma 10.24.1, Tag 00EK): an
`R`-algebra with compatible maps to the pieces which are localizations away from `a`, `b` is the
glued algebra. -/
theorem bijective_lift {M : Type u} [CommRing M] [Algebra R M] (φa : M →ₐ[R] Ba)
    (φb : M →ₐ[R] Bb) (h : ∀ x, ρa (φa x) = ρb (φb x))
    [IsLocalizedModule (Submonoid.powers a) φa.toLinearMap]
    [IsLocalizedModule (Submonoid.powers b) φb.toLinearMap] :
    Function.Bijective (lift φa φb h) := by
  refine bijective_of_isLocalized_span ({a, b} : Set R) hab
    (fun g ↦ LocalizedModule (Submonoid.powers g.val) M)
    (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.val) M)
    (fun g ↦ LocalizedModule (Submonoid.powers g.val) (glued ρa ρb))
    (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.val) (glued ρa ρb))
    (lift φa φb h).toLinearMap fun g ↦ ?_
  obtain ⟨g, hg⟩ := g
  rcases hg with rfl | hg
  · exact bijective_map_of _ φa.toLinearMap (fst ρa ρb).toLinearMap _ fun _ ↦ rfl
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact bijective_map_of _ φb.toLinearMap (snd ρa ρb).toLinearMap _ fun _ ↦ rfl

/-- The glued algebra is the unique algebra with compatible localizations to the pieces. -/
noncomputable def liftEquiv {M : Type u} [CommRing M] [Algebra R M] (φa : M →ₐ[R] Ba)
    (φb : M →ₐ[R] Bb) (h : ∀ x, ρa (φa x) = ρb (φb x))
    [IsLocalizedModule (Submonoid.powers a) φa.toLinearMap]
    [IsLocalizedModule (Submonoid.powers b) φb.toLinearMap] : M ≃ₐ[R] glued ρa ρb :=
  AlgEquiv.ofBijective (lift φa φb h) (bijective_lift a b hab φa φb h)

end Span

end ZariskiTwo
