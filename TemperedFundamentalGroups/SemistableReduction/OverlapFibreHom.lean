/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlapFibre

/-!
# Naturality of the overlap of a node patch with an étale piece (MR12 I3, generic core, step 2)

In the setting of `EtaleOverlap` / `OverlapFibre` (one level: a ring `R` with a nilpotent ideal
`J`, the node chart `A = R[1/a]`, the étale part `P` of a node patch, an étale piece `E` over
`D(b)`, the overlap `Bab = E[1/a]`, the special-fibre covering `C1` with `Cc = C1[1/a]`, and
`σP : P/J ≃ Cc[1/f]`, `σE : E/J ≃ C1[1/b]`), take a second copy (primed) over a ring `R'` and
maps of all the data compatible with the special-fibre identifications. Then the overlap maps
`κ : P → Bab` (`EtaleOverlap.κ`, the lift of `χ̄ = μ ∘ σP`) are natural:

* `OverlapFibre.eZ`: the induced map `Bab/J → Bab'/J'` of the special fibres of the overlaps;
* `γ1_map`, `γc_map`, `μ_map`: the special-fibre maps `γ1 : C1 → Bab/J`, `γc : Cc → Bab/J`,
  `μ : Cc[1/f] → Bab/J` are natural;
* **`OverlapFibre.κ_map`**: `κ' (p x) = eab (κ x)` for a map `p : P → P'` of the étale parts
  reducing to the map `Cc[1/f] → Cc'[1/f']` of the special-fibre coverings — by uniqueness of maps
  out of the formally étale `P` into the nilpotent thickening `Bab'` of `Bab'/J'`
  (`Algebra.FormallyUnramified.ext`); the base map `β : R → R'` only enters as semilinearity.
-/

universe u

namespace SemistableReduction

namespace OverlapFibre

noncomputable section

/-- **Uniqueness of semilinear maps out of a formally unramified algebra into a nilpotent
thickening**: two ring maps `P → Z`, semilinear over `β : R → R'`, which agree modulo a nilpotent
ideal of `Z` are equal. -/
theorem eq_of_semilinear {R R' P Z : Type*} [CommRing R] [CommRing R'] [CommRing P] [CommRing Z]
    [Algebra R P] [Algebra.FormallyUnramified R P] [Algebra R' Z] (β : R →+* R')
    {I : Ideal Z} (hI : IsNilpotent I) (u v : P →+* Z)
    (hu : ∀ r, u (algebraMap R P r) = algebraMap R' Z (β r))
    (hv : ∀ r, v (algebraMap R P r) = algebraMap R' Z (β r))
    (h : ∀ x, Ideal.Quotient.mk I (u x) = Ideal.Quotient.mk I (v x)) : u = v := by
  letI : Algebra R Z := ((algebraMap R' Z).comp β).toAlgebra
  let u' : P →ₐ[R] Z := { u with commutes' := hu }
  let v' : P →ₐ[R] Z := { v with commutes' := hv }
  have := Algebra.FormallyUnramified.ext (R := R) (A := P) I hI (g₁ := u') (g₂ := v') h
  exact RingHom.ext fun x ↦ AlgHom.congr_fun this x

variable {R : Type u} [CommRing R] (J : Ideal R) (a b : R)
  {A : Type u} [CommRing A] [Algebra R A] [IsLocalization.Away a A]
  {P : Type u} [CommRing P] [Algebra A P] [Algebra R P] [IsScalarTower R A P]
  [Algebra.FormallyEtale A P]
  {E : Type u} [CommRing E] [Algebra R E]
  {C1 : Type u} [CommRing C1] [Algebra R C1]
  {Cc : Type u} [CommRing Cc] [Algebra A Cc] [Algebra R Cc] [IsScalarTower R A Cc]
  (ι : C1 →ₐ[R] Cc) (f : A)
  (σP : (P ⧸ EtaleNil.JB J P) ≃ₐ[R] Localization.Away (algebraMap A Cc f))
  {Lb : Type u} [CommRing Lb] [Algebra C1 Lb] [Algebra R Lb] [IsScalarTower R C1 Lb]
  (σE : (E ⧸ EtaleNil.JB J E) ≃ₐ[R] Lb)
  (hι : letI := (ι : C1 →+* Cc).toAlgebra; IsLocalization.Away (algebraMap R C1 a) Cc)
  (hb : IsUnit (algebraMap R E b)) {k : ℕ} (hdiv : f ∣ algebraMap R A b ^ k)
  {R' : Type u} [CommRing R'] (J' : Ideal R') (a' b' : R')
  {A' : Type u} [CommRing A'] [Algebra R' A'] [IsLocalization.Away a' A']
  {P' : Type u} [CommRing P'] [Algebra A' P'] [Algebra R' P'] [IsScalarTower R' A' P']
  [Algebra.FormallyEtale A' P']
  {E' : Type u} [CommRing E'] [Algebra R' E']
  {C1' : Type u} [CommRing C1'] [Algebra R' C1']
  {Cc' : Type u} [CommRing Cc'] [Algebra A' Cc'] [Algebra R' Cc'] [IsScalarTower R' A' Cc']
  (ι' : C1' →ₐ[R'] Cc') (f' : A')
  (σP' : (P' ⧸ EtaleNil.JB J' P') ≃ₐ[R'] Localization.Away (algebraMap A' Cc' f'))
  {Lb' : Type u} [CommRing Lb'] [Algebra C1' Lb'] [Algebra R' Lb'] [IsScalarTower R' C1' Lb']
  (σE' : (E' ⧸ EtaleNil.JB J' E') ≃ₐ[R'] Lb')
  (hι' : letI := (ι' : C1' →+* Cc').toAlgebra; IsLocalization.Away (algebraMap R' C1' a') Cc')
  (hb' : IsUnit (algebraMap R' E' b')) {k' : ℕ} (hdiv' : f' ∣ algebraMap R' A' b' ^ k')
  (β : R →+* R') (hβJ : J.map β ≤ J') (hβa : β a = a')
  (e : E →+* E') (heβ : ∀ r, e (algebraMap R E r) = algebraMap R' E' (β r))

/-! ### The map of the overlaps and of their special fibres -/

include hβa heβ in
lemma e_a : e (algebraMap R E a) = algebraMap R' E' a' := by rw [heβ, hβa]

include hβa heβ in
/-- The map of overlaps `Bab → Bab'` induced by `e`. -/
def eab : EtaleOverlap.Bab a E →+* EtaleOverlap.Bab a' E' :=
  IsLocalization.Away.lift (algebraMap R E a)
    (g := (algebraMap E' (EtaleOverlap.Bab a' E')).comp e) (by
      rw [RingHom.comp_apply, e_a a a' β hβa e heβ]
      exact IsLocalization.Away.algebraMap_isUnit _)

lemma eab_algebraMap (x : E) :
    eab a a' β hβa e heβ (algebraMap E (EtaleOverlap.Bab a E) x) =
      algebraMap E' (EtaleOverlap.Bab a' E') (e x) :=
  IsLocalization.Away.lift_eq _ _ x

lemma eab_algebraMapR (r : R) :
    eab a a' β hβa e heβ (algebraMap R (EtaleOverlap.Bab a E) r) =
      algebraMap R' (EtaleOverlap.Bab a' E') (β r) := by
  rw [IsScalarTower.algebraMap_apply R E (EtaleOverlap.Bab a E) r, eab_algebraMap, heβ,
    ← IsScalarTower.algebraMap_apply R' E' (EtaleOverlap.Bab a' E')]

include hβJ in
lemma JB_le_comap :
    EtaleNil.JB J (EtaleOverlap.Bab a E) ≤
      (EtaleNil.JB J' (EtaleOverlap.Bab a' E')).comap (eab a a' β hβa e heβ) := by
  rw [EtaleNil.JB, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro r hr
  rw [Ideal.mem_comap, RingHom.comp_apply, eab_algebraMapR]
  exact Ideal.mem_map_of_mem _ (hβJ (Ideal.mem_map_of_mem β hr))

include hβJ in
/-- **The map of the special fibres of the overlaps** `Bab/J → Bab'/J'`. -/
def eZ : Z J a E →+* Z J' a' E' :=
  Ideal.quotientMap _ (eab a a' β hβa e heβ) (JB_le_comap J a J' a' β hβJ hβa e heβ)

lemma eZ_mk (x : EtaleOverlap.Bab a E) :
    eZ J a J' a' β hβJ hβa e heβ (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (eab a a' β hβa e heβ x) :=
  Ideal.quotientMap_mk

/-! ### Naturality of the special-fibre maps -/

variable {σE σE'} (φ1 : C1 →+* C1') (ℓb : Lb →+* Lb')
  (hℓb : ∀ c, ℓb (algebraMap C1 Lb c) = algebraMap C1' Lb' (φ1 c))
  (hσE : ∀ x, σE' (Ideal.Quotient.mk _ (e x)) = ℓb (σE (Ideal.Quotient.mk _ x)))

include hℓb hσE in
/-- **`γ1` is natural.** -/
lemma γ1_map (c : C1) :
    γ1 J' a' C1' σE' (φ1 c) = eZ J a J' a' β hβJ hβa e heβ (γ1 J a C1 σE c) := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (σE.symm (algebraMap C1 Lb c))
  have hx' : σE'.symm (algebraMap C1' Lb' (φ1 c)) = Ideal.Quotient.mk _ (e x) := by
    rw [← hℓb, ← AlgEquiv.apply_symm_apply σE (algebraMap C1 Lb c), ← hx, ← hσE,
      AlgEquiv.symm_apply_apply]
  change redE J' a' (σE'.symm (algebraMap C1' Lb' (φ1 c))) =
    eZ J a J' a' β hβJ hβa e heβ (redE J a (σE.symm (algebraMap C1 Lb c)))
  rw [hx', ← hx, EtaleNil.red_mk, EtaleNil.red_mk, eZ_mk, IsScalarTower.coe_toAlgHom',
    IsScalarTower.coe_toAlgHom', eab_algebraMap]

variable {ι ι'} (φc : Cc →+* Cc') (hφc : ∀ c, φc (ι c) = ι' (φ1 c))

include hℓb hσE hφc in
/-- **`γc` is natural.** -/
lemma γc_map (x : Cc) :
    γc J' a' ι' σE' hι' (φc x) = eZ J a J' a' β hβJ hβa e heβ (γc J a ι σE hι x) := by
  letI := (ι : C1 →+* Cc).toAlgebra
  haveI := hι
  have h := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R C1 a))
    (j := (γc J' a' ι' σE' hι').comp φc)
    (k := (eZ J a J' a' β hβJ hβa e heβ).comp (γc J a ι σE hι)) (RingHom.ext fun c ↦ by
      change γc J' a' ι' σE' hι' (φc (ι c)) = eZ J a J' a' β hβJ hβa e heβ (γc J a ι σE hι (ι c))
      rw [hφc, γc_ι, γc_ι]
      exact γ1_map J a J' a' β hβJ hβa e heβ φ1 ℓb hℓb hσE c)
  exact RingHom.congr_fun h x

variable {f f'}
  (ℓf : Localization.Away (algebraMap A Cc f) →+* Localization.Away (algebraMap A' Cc' f'))
  (hℓf : ∀ c, ℓf (algebraMap Cc _ c) = algebraMap Cc' _ (φc c))

omit [IsLocalization.Away a A] [IsLocalization.Away a' A'] in
include hℓb hσE hφc hℓf in
/-- **`μ` is natural.** -/
lemma μ_map (y : Localization.Away (algebraMap A Cc f)) :
    μ J' a' b' ι' f' σE' hι' hb' hdiv' (ℓf y) =
      eZ J a J' a' β hβJ hβa e heβ (μ J a b ι f σE hι hb hdiv y) := by
  have h := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A Cc f))
    (j := (μ J' a' b' ι' f' σE' hι' hb' hdiv').comp ℓf)
    (k := (eZ J a J' a' β hβJ hβa e heβ).comp (μ J a b ι f σE hι hb hdiv))
    (RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply]
      rw [hℓf, μ_algebraMap, μ_algebraMap]
      exact γc_map J a hι J' a' hι' β hβJ hβa e heβ φ1 ℓb hℓb hσE φc hφc c)
  exact RingHom.congr_fun h y

/-! ### Naturality of the overlap maps -/

variable {σP σP'} {m m' : ℕ} (hJ : J ^ m = ⊥) (hJ' : J' ^ m' = ⊥) (p : P →+* P')
  (hpβ : ∀ r, p (algebraMap R P r) = algebraMap R' P' (β r))
  (hp : ∀ x, σP' (Ideal.Quotient.mk _ (p x)) = ℓf (σP (Ideal.Quotient.mk _ x)))

include hβJ hℓb hσE hφc hℓf hpβ hp in
/-- **The overlap maps are natural**: `κ' ∘ p = eab ∘ κ` for a map `p` of the étale parts
reducing to the map `Cc[1/f] → Cc'[1/f']` of the special-fibre coverings. -/
theorem κ_map (x : P) :
    EtaleOverlap.κ J' hJ' a' A' (χ J' a' b' ι' f' σP' σE' hι' hb' hdiv') (p x) =
      eab a a' β hβa e heβ (EtaleOverlap.κ J hJ a A (χ J a b ι f σP σE hι hb hdiv) x) := by
  haveI := EtaleOverlap.formallyEtale_P a A (P := P)
  have hnil : IsNilpotent (EtaleNil.JB J' (EtaleOverlap.Bab a' E')) :=
    ⟨m', by rw [EtaleNil.JB, ← Ideal.map_pow, hJ', Ideal.map_bot, Ideal.zero_eq_bot]⟩
  have hκ : ∀ y, Ideal.Quotient.mk (EtaleNil.JB J (EtaleOverlap.Bab a E))
      (EtaleOverlap.κ J hJ a A (χ J a b ι f σP σE hι hb hdiv) y) =
        χ J a b ι f σP σE hι hb hdiv (Ideal.Quotient.mk _ y) := fun y ↦
    (EtaleNil.red_mk J _ y).symm.trans
      (AlgHom.congr_fun (EtaleOverlap.red_κ J hJ a A _) (Ideal.Quotient.mk _ y))
  have hκ' : ∀ y, Ideal.Quotient.mk (EtaleNil.JB J' (EtaleOverlap.Bab a' E'))
      (EtaleOverlap.κ J' hJ' a' A' (χ J' a' b' ι' f' σP' σE' hι' hb' hdiv') y) =
        χ J' a' b' ι' f' σP' σE' hι' hb' hdiv' (Ideal.Quotient.mk _ y) := fun y ↦
    (EtaleNil.red_mk J' _ y).symm.trans
      (AlgHom.congr_fun (EtaleOverlap.red_κ J' hJ' a' A' _) (Ideal.Quotient.mk _ y))
  have key := eq_of_semilinear β hnil
    ((EtaleOverlap.κ J' hJ' a' A' (χ J' a' b' ι' f' σP' σE' hι' hb' hdiv') : P' →+* _).comp p)
    ((eab a a' β hβa e heβ).comp
      (EtaleOverlap.κ J hJ a A (χ J a b ι f σP σE hι hb hdiv) : P →+* _))
    (fun r ↦ by
      rw [RingHom.comp_apply, hpβ, RingHom.coe_coe, AlgHom.commutes])
    (fun r ↦ by
      rw [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes, eab_algebraMapR])
    (fun y ↦ by
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [hκ', ← eZ_mk J a J' a' β hβJ hβa e heβ, hκ]
      change μ J' a' b' ι' f' σE' hι' hb' hdiv' (σP' (Ideal.Quotient.mk _ (p y))) =
        eZ J a J' a' β hβJ hβa e heβ (μ J a b ι f σE hι hb hdiv (σP (Ideal.Quotient.mk _ y)))
      rw [hp]
      exact μ_map J a b hι hb hdiv J' a' b' hι' hb' hdiv' β hβJ hβa e heβ φ1 ℓb hℓb hσE φc hφc
        ℓf hℓf _)
  exact RingHom.congr_fun key x

end

end OverlapFibre

end SemistableReduction
