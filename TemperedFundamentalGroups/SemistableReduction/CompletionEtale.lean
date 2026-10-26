/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Etale.Basic
import TemperedFundamentalGroups.SemistableReduction.CompletionMap

/-!
# Adic completions along an étale neighbourhood with trivial residue extension

Let `R → S` be a formally étale ring map (e.g. `[Algebra.Etale R S]`, which provides
`Algebra.FormallyEtale R S` as an instance), `𝔪 : Ideal R` and `𝔫 : Ideal S` with
`𝔫.comap (algebraMap R S) = 𝔪`, and suppose the residue extension is trivial, phrased as
`Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))`, i.e. every `s : S` is
congruent modulo `𝔫` to an element of `R` (equivalently: the induced map `R ⧸ 𝔪 → S ⧸ 𝔫` is
surjective). No maximality, primality or finiteness hypotheses are needed. Then:

* `CompletionEtale.resEquiv`: `R ⧸ 𝔪 ≃ₐ[R] S ⧸ 𝔫`; `CompletionEtale.isMaximal`: if `𝔪` is
  maximal, so is `𝔫`;
* `CompletionEtale.quotPowEquiv n : R ⧸ 𝔪 ^ n ≃ₐ[R] S ⧸ 𝔫 ^ n`, the map induced by
  `algebraMap R S` (`quotPowEquiv_mk`, `quotPowEquiv_apply`), compatible with the transition maps
  (`quotPowEquiv_factorPow`);
* **`CompletionEtale.equiv : AdicCompletion 𝔪 R ≃+* AdicCompletion 𝔫 S`**, whose underlying map is
  `CompletionMap.map (algebraMap R S) _` (`equiv_apply`), with `equiv_algebraMap`.

## Proof

Only the infinitesimal lifting properties are used (no flatness, no localization).
`J := 𝔪 (R ⧸ 𝔪 ^ n)` is nilpotent (`J ^ n = 0`) and `(R ⧸ 𝔪 ^ n) ⧸ J` receives `R ⧸ 𝔪 ≅ S ⧸ 𝔫`,
so formal smoothness lifts `S → S ⧸ 𝔫 ≅ R ⧸ 𝔪 → (R ⧸ 𝔪 ^ n) ⧸ J` to an `R`-algebra map
`σ : S → R ⧸ 𝔪 ^ n` with `σ(𝔫) ⊆ J`, hence `σ(𝔫 ^ n) ⊆ J ^ n = 0`, and `σ` descends to
`S ⧸ 𝔫 ^ n → R ⧸ 𝔪 ^ n`. Its composite with `R ⧸ 𝔪 ^ n → S ⧸ 𝔫 ^ n` is the identity of
`R ⧸ 𝔪 ^ n` (an `R`-algebra endomorphism of a quotient of `R`); the other composite is an
`R`-algebra endomorphism of `S ⧸ 𝔫 ^ n` which agrees with the identity modulo the nilpotent ideal
`𝔫 (S ⧸ 𝔫 ^ n)`, hence is the identity by formal unramifiedness. The level isomorphisms are
compatible, so the levelwise inverses assemble (`AdicCompletion.liftRingHom`) to an inverse of
`CompletionMap.map (algebraMap R S) _`.
-/

namespace SemistableReduction

namespace CompletionEtale

noncomputable section

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {𝔪 : Ideal R} {𝔫 : Ideal S}

lemma map_le (hcomap : 𝔫.comap (algebraMap R S) = 𝔪) : 𝔪.map (algebraMap R S) ≤ 𝔫 :=
  Ideal.map_le_iff_le_comap.mpr hcomap.ge

lemma isNilpotent_map_mk {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) :
    IsNilpotent (I.map (Ideal.Quotient.mk (I ^ n))) :=
  ⟨n, (Ideal.map_pow _ _ _).symm.trans (Ideal.map_quotient_self _)⟩

variable (𝔪 𝔫) in
/-- The residue field isomorphism `R ⧸ 𝔪 ≃ₐ[R] S ⧸ 𝔫` (induced by `algebraMap R S`). -/
def resEquiv (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) :
    (R ⧸ 𝔪) ≃ₐ[R] S ⧸ 𝔫 :=
  AlgEquiv.ofBijective (Ideal.quotientMapₐ 𝔫 (Algebra.ofId R S) hcomap.ge)
    ⟨Ideal.quotientMap_injective' (H := hcomap.ge) hcomap.le, fun y ↦ by
      obtain ⟨r, hr⟩ := hsurj y
      exact ⟨Ideal.Quotient.mk 𝔪 r, hr⟩⟩

lemma resEquiv_mk (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (r : R) :
    resEquiv 𝔪 𝔫 hcomap hsurj (Ideal.Quotient.mk 𝔪 r) =
      Ideal.Quotient.mk 𝔫 (algebraMap R S r) :=
  rfl

/-- If `𝔪` is maximal, then so is `𝔫`. -/
theorem isMaximal [𝔪.IsMaximal] (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) :
    𝔫.IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact MulEquiv.isField (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔪 |>.mp ‹_›)
    (resEquiv 𝔪 𝔫 hcomap hsurj).symm.toMulEquiv

variable (𝔪 𝔫) in
/-- The residue map `S → S ⧸ 𝔫 ≅ R ⧸ 𝔪 → (R ⧸ 𝔪 ^ n) ⧸ 𝔪 (R ⧸ 𝔪 ^ n)`. -/
def resToQuot (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ) :
    S →ₐ[R] (R ⧸ 𝔪 ^ n) ⧸ 𝔪.map (Ideal.Quotient.mk (𝔪 ^ n)) :=
  ((Ideal.quotientMapₐ _ (Ideal.Quotient.mkₐ R (𝔪 ^ n)) Ideal.le_comap_map).comp
    (resEquiv 𝔪 𝔫 hcomap hsurj).symm.toAlgHom).comp (Ideal.Quotient.mkₐ R 𝔫)

lemma resToQuot_apply (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ)
    (s : S) :
    resToQuot 𝔪 𝔫 hcomap hsurj n s = Ideal.quotientMap _ (Ideal.Quotient.mk (𝔪 ^ n))
      Ideal.le_comap_map ((resEquiv 𝔪 𝔫 hcomap hsurj).symm (Ideal.Quotient.mk 𝔫 s)) :=
  rfl

variable [Algebra.FormallyEtale R S]

variable (𝔪 𝔫) in
/-- The lift `σ : S →ₐ[R] R ⧸ 𝔪 ^ n` of the residue map (formal smoothness). -/
def sect (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ) :
    S →ₐ[R] R ⧸ 𝔪 ^ n :=
  Algebra.FormallySmooth.lift _ (isNilpotent_map_mk 𝔪 n) (resToQuot 𝔪 𝔫 hcomap hsurj n)

lemma mk_sect (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ)
    (s : S) :
    Ideal.Quotient.mk _ (sect 𝔪 𝔫 hcomap hsurj n s) = resToQuot 𝔪 𝔫 hcomap hsurj n s :=
  Algebra.FormallySmooth.mk_lift _ _ _ s

lemma sect_pow_eq_zero (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ)
    {s : S} (hs : s ∈ 𝔫 ^ n) : sect 𝔪 𝔫 hcomap hsurj n s = 0 := by
  set σ := sect 𝔪 𝔫 hcomap hsurj n
  have h1 : 𝔫.map σ ≤ 𝔪.map (Ideal.Quotient.mk (𝔪 ^ n)) := by
    refine Ideal.map_le_iff_le_comap.mpr fun t ht ↦ ?_
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, mk_sect]
    rw [resToQuot_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ht, map_zero, map_zero]
  have h2 : (𝔫 ^ n).map σ ≤ ⊥ := by
    rw [Ideal.map_pow, ← Ideal.map_quotient_self (𝔪 ^ n), Ideal.map_pow]
    exact Ideal.pow_right_mono h1 n
  exact (Submodule.mem_bot _).mp (h2 (Ideal.mem_map_of_mem _ hs))

variable (𝔪 𝔫) in
/-- **Level isomorphisms** `R ⧸ 𝔪 ^ n ≃ₐ[R] S ⧸ 𝔫 ^ n`, induced by `algebraMap R S`. -/
def quotPowEquiv (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ) :
    (R ⧸ 𝔪 ^ n) ≃ₐ[R] S ⧸ 𝔫 ^ n :=
  AlgEquiv.ofAlgHom
    (Ideal.quotientMapₐ _ (Algebra.ofId R S) (CompletionMap.le_comap _ (map_le hcomap) n))
    (Ideal.Quotient.liftₐ _ (sect 𝔪 𝔫 hcomap hsurj n)
      fun _ hs ↦ sect_pow_eq_zero hcomap hsurj n hs)
    (by
      refine Ideal.Quotient.algHom_ext R
        (Algebra.FormallyUnramified.ext _ (isNilpotent_map_mk 𝔫 n) fun x ↦ ?_)
      obtain ⟨r, hr⟩ := hsurj (Ideal.Quotient.mk 𝔫 x)
      obtain ⟨r', hr'⟩ := Ideal.Quotient.mk_surjective (sect 𝔪 𝔫 hcomap hsurj n x)
      have hsec := mk_sect hcomap hsurj n x
      have hres : (resEquiv 𝔪 𝔫 hcomap hsurj).symm (Ideal.Quotient.mk 𝔫 x) =
          Ideal.Quotient.mk 𝔪 r := by
        rw [AlgEquiv.symm_apply_eq, resEquiv_mk, ← hr, RingHom.comp_apply]
      rw [resToQuot_apply, hres, Ideal.quotientMap_mk, ← hr', Ideal.Quotient.eq, ← map_sub,
        Ideal.mem_quotient_iff_mem_sup] at hsec
      rw [RingHom.comp_apply, Ideal.Quotient.eq] at hr
      change Ideal.Quotient.mk _ (Ideal.quotientMap (𝔫 ^ n) (algebraMap R S)
        (CompletionMap.le_comap _ (map_le hcomap) n) (sect 𝔪 𝔫 hcomap hsurj n x)) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)
      rw [← hr', Ideal.quotientMap_mk, Ideal.Quotient.eq, ← map_sub, Ideal.mem_quotient_iff_mem_sup,
        show algebraMap R S r' - x = algebraMap R S (r' - r) + (algebraMap R S r - x) by
          rw [map_sub]; ring]
      refine add_mem ?_ (Ideal.mem_sup_left (by simpa using hr))
      refine sup_le (hcomap.ge.trans (Ideal.comap_mono le_sup_left))
        ((CompletionMap.le_comap _ (map_le hcomap) n).trans (Ideal.comap_mono le_sup_right)) hsec)
    (by
      ext r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      exact (sect 𝔪 𝔫 hcomap hsurj n).commutes r)

lemma quotPowEquiv_mk (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ)
    (r : R) :
    quotPowEquiv 𝔪 𝔫 hcomap hsurj n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R S r) :=
  rfl

lemma quotPowEquiv_apply (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ)
    (y : R ⧸ 𝔪 ^ n) :
    quotPowEquiv 𝔪 𝔫 hcomap hsurj n y =
      Ideal.quotientMap _ (algebraMap R S) (CompletionMap.le_comap _ (map_le hcomap) n) y :=
  rfl

lemma quotPowEquiv_factorPow (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) {m n : ℕ}
    (hle : m ≤ n) (y : R ⧸ 𝔪 ^ n) :
    quotPowEquiv 𝔪 𝔫 hcomap hsurj m (Ideal.Quotient.factorPow 𝔪 hle y) =
      Ideal.Quotient.factorPow 𝔫 hle (quotPowEquiv 𝔪 𝔫 hcomap hsurj n y) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [quotPowEquiv_mk]
  rfl

lemma factorPow_evalₐ {A : Type*} [CommRing A] (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h a =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
    have ha := AdicCompletion.AdicCauchySequence.mk_eq_mk hle a
    rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at ha
    exact Ideal.Quotient.eq.mpr ha

variable (𝔪 𝔫) in
/-- Level `n` of the inverse of the completion map: `S^∧ → S ⧸ 𝔫 ^ n ≅ R ⧸ 𝔪 ^ n`. -/
def invLev (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ) :
    AdicCompletion 𝔫 S →+* R ⧸ 𝔪 ^ n :=
  ((quotPowEquiv 𝔪 𝔫 hcomap hsurj n).symm : S ⧸ 𝔫 ^ n →+* R ⧸ 𝔪 ^ n).comp
    (AdicCompletion.evalₐ 𝔫 n).toRingHom

lemma invLev_compat (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow 𝔪 hle).comp (invLev 𝔪 𝔫 hcomap hsurj n) =
      invLev 𝔪 𝔫 hcomap hsurj m := by
  ext x
  apply (quotPowEquiv 𝔪 𝔫 hcomap hsurj m).injective
  simp only [invLev, RingHom.comp_apply, RingHom.coe_coe, AlgHom.toRingHom_eq_coe,
    quotPowEquiv_factorPow, AlgEquiv.apply_symm_apply]
  exact factorPow_evalₐ 𝔫 hle x

variable (𝔪 𝔫) in
/-- The inverse of the completion map, assembled from the inverse level isomorphisms. -/
def inv (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) :
    AdicCompletion 𝔫 S →+* AdicCompletion 𝔪 R :=
  AdicCompletion.liftRingHom 𝔪 (invLev 𝔪 𝔫 hcomap hsurj) (invLev_compat hcomap hsurj)

lemma evalₐ_inv (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (n : ℕ)
    (y : AdicCompletion 𝔫 S) :
    AdicCompletion.evalₐ 𝔪 n (inv 𝔪 𝔫 hcomap hsurj y) =
      (quotPowEquiv 𝔪 𝔫 hcomap hsurj n).symm (AdicCompletion.evalₐ 𝔫 n y) :=
  AdicCompletion.evalₐ_liftRingHom 𝔪 _ (invLev_compat hcomap hsurj) n y

variable (𝔪 𝔫) in
/-- **Adic completions are unchanged by an étale neighbourhood with trivial residue extension**:
`CompletionMap.map (algebraMap R S) _ : AdicCompletion 𝔪 R → AdicCompletion 𝔫 S` is a ring
isomorphism. -/
def equiv (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) :
    AdicCompletion 𝔪 R ≃+* AdicCompletion 𝔫 S :=
  RingEquiv.ofBijective (CompletionMap.map (algebraMap R S) (map_le hcomap)) <| by
    constructor
    · refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ AdicCompletion.ext_evalₐ fun n ↦ ?_
      have h := congrArg (AdicCompletion.evalₐ 𝔫 n) hx
      rw [CompletionMap.evalₐ_map, map_zero, ← quotPowEquiv_apply hcomap hsurj] at h
      rw [map_zero]
      exact (map_eq_zero_iff _ (quotPowEquiv 𝔪 𝔫 hcomap hsurj n).injective).mp h
    · refine fun y ↦ ⟨inv 𝔪 𝔫 hcomap hsurj y, AdicCompletion.ext_evalₐ fun n ↦ ?_⟩
      rw [CompletionMap.evalₐ_map, ← quotPowEquiv_apply hcomap hsurj, evalₐ_inv,
        AlgEquiv.apply_symm_apply]

lemma equiv_apply (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S)))
    (x : AdicCompletion 𝔪 R) :
    equiv 𝔪 𝔫 hcomap hsurj x = CompletionMap.map (algebraMap R S) (map_le hcomap) x :=
  rfl

lemma equiv_algebraMap (hcomap : 𝔫.comap (algebraMap R S) = 𝔪)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S))) (r : R) :
    equiv 𝔪 𝔫 hcomap hsurj (algebraMap R _ r) = algebraMap S _ (algebraMap R S r) :=
  CompletionMap.map_algebraMap _ _ r

end

end CompletionEtale

end SemistableReduction
