/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelStep
import TemperedFundamentalGroups.SemistableReduction.FormalGlueingQuot

/-!
# The étale parts of consecutive levels (Blueprint §12.8, M2.3 (e'))

In the setting of `LevelStep` (charts `R → R'` of consecutive levels, special-fibre isomorphism
`e`, an admissible covering `cov` of the special fibre of `R` and its transport to `R'`), let
`P`, `P'` be formally étale lifts over `R`, `R'` of the covering on `D(f)`
(`σP : P/JP ≅ C_f`, `σP' : P'/J'P' ≅ C_f'`, e.g. from `AwayLift.exists_lift`).

* **`LevelStep.ρP : P → P'`**: the lift (formal étaleness of `P`, `J'` nilpotent) of
  `P → P/JP ≅ C_f ≅ C_f' ≅ P'/J'P'`; it is compatible with `σ` (`hσ`);
* **`bijective_g`**: its base change `R' ⊗_R P → P'` is an isomorphism (both sides formally étale
  over `R'` and complete along the nilpotent `J'`; the inverse is the lift of the inverse modulo
  `J'`, `EtaleLift.ext_of_comp_eq`), hence **`surjective_ρP`** and **`ker_ρP`**
  (`ker ρP = (ker q) P`): the hypotheses `hρPs`, `hρPk` of `FormalGlueingQuot.equiv`.
-/

universe u

open TensorProduct

namespace SemistableReduction

open AdmissibleLift

namespace LevelStep

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {R' : Type u} [CommRing R'] [Algebra O R']
  [Algebra R R'] (f : R)
  [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  {e : (R ⧸ J θ (R := R)) ≃ₐ[k] (R' ⧸ J θ (R := R'))}
  (he : ∀ r : R, e (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R R' r))

variable {φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}

/-! ### The étale parts of consecutive levels -/

section Etale

omit [Algebra k (R' ⧸ J θ (R := R'))] in
/-- `1 ⊗ x = 0` in `R' ⊗_R P` iff `x ∈ (ker q) P`. -/
lemma mem_of_one_tmul_eq_zero (hq : Function.Surjective (algebraMap R R')) {P : Type u}
    [CommRing P] [Algebra R P] {x : P} (hx : (1 : R') ⊗ₜ[R] x = 0) :
    x ∈ (RingHom.ker (algebraMap R R')).map (algebraMap R P) := by
  let eI : R' ≃ₐ[R] R ⧸ RingHom.ker (algebraMap R R') :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R R') hq).symm
  let Ψ : R' ⊗[R] P →ₐ[R] P ⊗[R] (R ⧸ RingHom.ker (algebraMap R R')) :=
    (Algebra.TensorProduct.map (AlgHom.id R P) eI.toAlgHom).comp
      (Algebra.TensorProduct.comm R R' P).toAlgHom
  have h1 : Ψ ((1 : R') ⊗ₜ x) = x ⊗ₜ 1 := by
    simp [Ψ]
  rw [hx, map_zero] at h1
  have h2 := congrArg (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R) P
    (RingHom.ker (algebraMap R R'))).symm h1
  rw [map_zero] at h2
  have h3 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R) P
      (RingHom.ker (algebraMap R R'))).symm
        (x ⊗ₜ[R] (1 : R ⧸ RingHom.ker (algebraMap R R'))) = Ideal.Quotient.mk _ x :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R) P _).symm_apply_eq).mpr rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← h3, h2]

omit [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))] in
lemma J_map [IsScalarTower O R R'] :
    (J θ (R := R)).map (algebraMap R R') = J θ (R := R') := by
  rw [J, J, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

variable (cov : Admissible.Covering φ ψc)

include he in
lemma algebraMap_C (r : R) :
    algebraMap R' (cov.transport (h := he f)).C (algebraMap R R' r) = algebraMap R cov.C r := by
  change algebraMap (R ⧸ J θ) cov.C (e.symm (Ideal.Quotient.mk _ (algebraMap R R' r))) =
    algebraMap (R ⧸ J θ) cov.C (Ideal.Quotient.mk _ r)
  rw [← he, AlgEquiv.symm_apply_apply]

/-- The localizations `C_f` of the covering at the two levels. -/
def T : Localization.Away (algebraMap R cov.C f) ≃+*
    Localization.Away (algebraMap R' (cov.transport (h := he f)).C (f' (R' := R') f)) :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (algebraMap R cov.C f))
    (T := Submonoid.powers (algebraMap R' (cov.transport (h := he f)).C (f' (R' := R') f))) _ _
    (RingEquiv.refl cov.C) (by
      rw [Submonoid.map_powers, algebraMap_C f he cov f]
      rfl)

lemma T_algebraMap (c : cov.C) :
    T f he cov (algebraMap cov.C _ c) = algebraMap (cov.transport (h := he f)).C _ c :=
  IsLocalization.ringEquivOfRingEquiv_eq _ _

lemma T_algebraMap_R (r : R) :
    T f he cov (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) := by
  have h1 : algebraMap R (Localization.Away (algebraMap R cov.C f)) r =
      algebraMap cov.C _ (algebraMap R cov.C r) := IsScalarTower.algebraMap_apply _ _ _ _
  have h2 : algebraMap R' (Localization.Away
      (algebraMap R' (cov.transport (h := he f)).C (f' (R' := R') f))) (algebraMap R R' r) =
      algebraMap (cov.transport (h := he f)).C _
        (algebraMap R' (cov.transport (h := he f)).C (algebraMap R R' r)) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  rw [h1, T_algebraMap, h2]
  exact congrArg _ (algebraMap_C f he cov r).symm

end Etale

section RhoP

variable [IsScalarTower O R R'] (hq : Function.Surjective (algebraMap R R'))
  (cov : Admissible.Covering φ ψc)
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  {P' : Type u} [CommRing P'] [Algebra R' P'] [Algebra.FormallyEtale R' P'] [Algebra R P']
  [IsScalarTower R R' P']
  (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R cov.C f))
  (σP' : (P' ⧸ (J θ).map (algebraMap R' P')) ≃ₐ[R']
    Localization.Away (algebraMap R' (cov.transport (h := he f)).C (f' (R' := R') f)))
  {m : ℕ} (hJ' : J θ (R := R') ^ m = ⊥)

/-- `P → P'/J'P'`: `P → P/JP ≅ C_f ≅ C_f' ≅ P'/J'P'`. -/
def φ₀ : P →ₐ[R] P' ⧸ (J θ (R := R')).map (algebraMap R' P') where
  toRingHom := (σP'.symm.toRingEquiv.toRingHom.comp (T f he cov).toRingHom).comp
    (σP.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk _))
  commutes' r := by
    change σP'.symm (T f he cov (σP (algebraMap R _ r))) = _
    rw [AlgEquiv.commutes, T_algebraMap_R, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]

omit [IsScalarTower O R R'] [Algebra.FormallyEtale R P] [Algebra.FormallyEtale R' P'] in
lemma φ₀_apply (p : P) :
    φ₀ f he cov σP σP' p = σP'.symm (T f he cov (σP (Ideal.Quotient.mk _ p))) := rfl

omit [Algebra k (R' ⧸ J θ (R := R'))] [Algebra.FormallyEtale R' P'] in
include hJ' in
lemma isAdicComplete_P' : IsAdicComplete ((J θ (R := R')).map (algebraMap R' P')) P' :=
  CompleteFinite.isAdicComplete_of_pow_eq_bot _ (n := m)
    (by rw [← Ideal.map_pow, hJ', Ideal.map_bot])

/-- **The reduction `ρP : P → P'`** of the étale part: the lift of `φ₀`. -/
def ρP : P →ₐ[R] P' :=
  haveI := isAdicComplete_P' (R' := R') (θ := θ) (P' := P') hJ'
  EtaleLift.lift _ (φ₀ f he cov σP σP')

omit [IsScalarTower O R R'] [Algebra.FormallyEtale R' P'] in
lemma mk_ρP (p : P) :
    Ideal.Quotient.mk _ (ρP f he cov σP σP' hJ' p) = φ₀ f he cov σP σP' p :=
  haveI := isAdicComplete_P' (R' := R') (θ := θ) (P' := P') hJ' 
  congrArg (fun g ↦ g p) (EtaleLift.mkₐ_comp_lift _ (φ₀ f he cov σP σP'))

omit [IsScalarTower O R R'] [Algebra.FormallyEtale R' P'] in
lemma σP'_ρP (p : P) :
    σP' (Ideal.Quotient.mk _ (ρP f he cov σP σP' hJ' p)) =
      T f he cov (σP (Ideal.Quotient.mk _ p)) := by
  rw [mk_ρP, φ₀_apply, AlgEquiv.apply_symm_apply]

omit [IsScalarTower O R R'] [Algebra.FormallyEtale R' P'] in
/-- `ρP` is compatible with the identifications `σ` of the special fibres. -/
theorem hσ (p : P) (c : cov.C) (hc : σP (Ideal.Quotient.mk _ p) = algebraMap cov.C _ c) :
    σP' (Ideal.Quotient.mk _ (ρP f he cov σP σP' hJ' p)) =
      algebraMap (cov.transport (h := he f)).C _ c := by
  rw [σP'_ρP, hc, T_algebraMap]

/-- The base change `R' ⊗_R P → P'` of `ρP`. -/
def g : R' ⊗[R] P →ₐ[R'] P' :=
  Algebra.TensorProduct.lift (Algebra.ofId R' P') (ρP f he cov σP σP' hJ')
    fun _ _ ↦ Commute.all _ _

omit [IsScalarTower O R R'] [Algebra.FormallyEtale R' P'] in
lemma g_one_tmul (p : P) : g f he cov σP σP' hJ' ((1 : R') ⊗ₜ p) = ρP f he cov σP σP' hJ' p := by
  rw [g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

omit [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  [Algebra.FormallyEtale R P] in
lemma le_comap_J : (J θ (R := R)).map (algebraMap R P) ≤
    ((J θ (R := R')).map (algebraMap R' (R' ⊗[R] P))).comap
      (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := P)).toRingHom := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro r hr
  rw [Ideal.mem_comap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, IsScalarTower.algebraMap_apply R R' (R' ⊗[R] P)]
  refine Ideal.mem_map_of_mem _ ?_
  rw [← J_map (θ := θ) (R := R) (R' := R')]
  exact Ideal.mem_map_of_mem _ hr

/-- `P/JP → (R' ⊗_R P)/J'`. -/
def a : (P ⧸ (J θ (R := R)).map (algebraMap R P)) →+*
    (R' ⊗[R] P) ⧸ (J θ (R := R')).map (algebraMap R' (R' ⊗[R] P)) :=
  Ideal.quotientMap _ _ le_comap_J

/-- `P' → (R' ⊗_R P)/J'`, the inverse of `g` modulo `J'`. -/
def h₀ : P' →ₐ[R'] (R' ⊗[R] P) ⧸ (J θ (R := R')).map (algebraMap R' (R' ⊗[R] P)) where
  toRingHom := ((a (R' := R') (θ := θ) (P := P)).comp (σP.symm.toRingEquiv.toRingHom.comp
    (T f he cov).symm.toRingHom)).comp (σP'.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk _))
  commutes' r' := by
    obtain ⟨r, rfl⟩ := hq r'
    change a (R' := R') (θ := θ) (P := P)
      (σP.symm ((T f he cov).symm (σP' (algebraMap R' _ (algebraMap R R' r))))) = _
    rw [AlgEquiv.commutes, ← T_algebraMap_R, RingEquiv.symm_apply_apply, AlgEquiv.commutes]
    change Ideal.Quotient.mk _ (Algebra.TensorProduct.includeRight (algebraMap R P r)) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R R' (R' ⊗[R] P)]
    rfl

omit [Algebra.FormallyEtale R P] [Algebra.FormallyEtale R' P'] [Algebra R P']
  [IsScalarTower R R' P'] in
lemma h₀_apply (x : P') :
    h₀ f he hq cov σP σP' x =
      a (R' := R') (θ := θ) (P := P)
        (σP.symm ((T f he cov).symm (σP' (Ideal.Quotient.mk _ x)))) := rfl

omit [Algebra O R] [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  [IsScalarTower O R R'] [Algebra.FormallyEtale R P] in
include hJ' in
lemma isAdicComplete_B :
    IsAdicComplete ((J θ (R := R')).map (algebraMap R' (R' ⊗[R] P))) (R' ⊗[R] P) :=
  CompleteFinite.isAdicComplete_of_pow_eq_bot _ (n := m)
    (by rw [← Ideal.map_pow, hJ', Ideal.map_bot])

omit [IsScalarTower O R R'] [Algebra.FormallyEtale R' P'] in
lemma g_mem {y : R' ⊗[R] P} (hy : y ∈ (J θ (R := R')).map (algebraMap R' (R' ⊗[R] P))) :
    g f he cov σP σP' hJ' y ∈ (J θ (R := R')).map (algebraMap R' P') := by
  have hle : (J θ (R := R')).map (algebraMap R' (R' ⊗[R] P)) ≤
      ((J θ (R := R')).map (algebraMap R' P')).comap (g f he cov σP σP' hJ') :=
    Ideal.map_le_iff_le_comap.mpr fun r hr ↦ by
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ hr
  exact hle hy

include hq in
/-- **`R' ⊗_R P ≅ P'`**: the base change of `ρP` is bijective (both sides are formally étale over
`R'` and complete along the nilpotent `J'`, and `g` is an isomorphism modulo `J'`). -/
theorem bijective_g : Function.Bijective (g f he cov σP σP' hJ') := by
  haveI := isAdicComplete_P' (R' := R') (θ := θ) (P' := P') hJ'
  haveI := isAdicComplete_B (R := R) (R' := R') (θ := θ) (P := P) hJ'
  set g' := g f he cov σP σP' hJ'
  let h := EtaleLift.lift _ (h₀ f he hq cov σP σP')
  have hh : ∀ x, Ideal.Quotient.mk _ (h x) = h₀ f he hq cov σP σP' x := fun x ↦
    congrArg (fun g ↦ g x) (EtaleLift.mkₐ_comp_lift _ (h₀ f he hq cov σP σP'))
  have h1 : g'.comp h = AlgHom.id R' P' := by
    refine EtaleLift.ext_of_comp_eq ((J θ (R := R')).map (algebraMap R' P'))
      (AlgHom.ext fun x ↦ ?_)
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
      (σP.symm ((T f he cov).symm (σP' (Ideal.Quotient.mk _ x))))
    have hx : Ideal.Quotient.mk ((J θ (R := R')).map (algebraMap R' (R' ⊗[R] P))) (h x) =
        Ideal.Quotient.mk _ ((1 : R') ⊗ₜ[R] p) := by
      rw [hh, h₀_apply, ← hp]
      rfl
    rw [Ideal.Quotient.eq] at hx
    have hg := g_mem f he cov σP σP' hJ' hx
    rw [map_sub, g_one_tmul, ← Ideal.Quotient.eq] at hg
    change Ideal.Quotient.mk ((J θ (R := R')).map (algebraMap R' P')) (g' (h x)) =
      Ideal.Quotient.mk _ x
    rw [hg, mk_ρP, φ₀_apply, hp, AlgEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      AlgEquiv.symm_apply_apply]
  have h2 : h.comp g' = AlgHom.id R' (R' ⊗[R] P) := by
    refine EtaleLift.ext_of_comp_eq ((J θ (R := R')).map (algebraMap R' (R' ⊗[R] P)))
      (AlgHom.ext fun b ↦ ?_)
    obtain ⟨p, rfl⟩ := FormalGlueingQuot.exists_one_tmul hq b
    change Ideal.Quotient.mk ((J θ (R := R')).map (algebraMap R' (R' ⊗[R] P)))
      (h (g' ((1 : R') ⊗ₜ p))) = Ideal.Quotient.mk _ ((1 : R') ⊗ₜ p)
    rw [g_one_tmul, hh, h₀_apply, σP'_ρP, RingEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
    rfl
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨h y, congrArg (fun g ↦ g y) h1⟩⟩
  have := congrArg h hxy
  exact (congrArg (fun g ↦ g x) h2).symm.trans (this.trans (congrArg (fun g ↦ g y) h2))

include hq in
/-- **`ρP` is surjective.** -/
theorem surjective_ρP : Function.Surjective (ρP f he cov σP σP' hJ') := fun y ↦ by
  obtain ⟨b, rfl⟩ := (bijective_g f he hq cov σP σP' hJ').2 y
  obtain ⟨p, rfl⟩ := FormalGlueingQuot.exists_one_tmul hq b
  exact ⟨p, (g_one_tmul f he cov σP σP' hJ' p).symm⟩

include hq in
/-- **The kernel of `ρP` is `(ker q) P`.** -/
theorem ker_ρP : RingHom.ker (ρP f he cov σP σP' hJ') =
    (RingHom.ker (algebraMap R R')).map (algebraMap R P) := by
  apply le_antisymm
  · intro x hx
    refine mem_of_one_tmul_eq_zero hq ?_
    apply (bijective_g f he hq cov σP σP' hJ').1
    rw [g_one_tmul, map_zero]
    exact hx
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R R' P', RingHom.mem_ker.mp hr, map_zero]

end RhoP

end

end LevelStep

end SemistableReduction
