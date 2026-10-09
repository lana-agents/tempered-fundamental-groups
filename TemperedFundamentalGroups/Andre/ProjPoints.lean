/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.MvPolynomial.Ideal
import TemperedFundamentalGroups.Models.Projective

/-!
# Points of projective space `ℙᵐ_R`

Points of `projSpace R m = Proj R[x₀, …, xₘ]` are relevant homogeneous prime ideals. This file
records:

* `exists_X_notMem`: some coordinate `xᵢ` does not vanish at a point;
* `mem_toSpecZero_iff`, `mem_projSpace_toSpec_iff`: the image of a point `x` in `Spec R` is the
  prime `{c : C c ∈ x}`; for a local ring `R`, `x` lies in the special fibre iff
  `C c ∈ x` for all `c` in the maximal ideal (`mem_specialFibre_projSpace_iff`);
* `projPointOfKer`: the point given by the kernel of a ring homomorphism to a domain that
  respects homogeneous components and does not kill all coordinates.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace TemperedFundamentalGroups

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {m : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R

/-- Some coordinate does not vanish at a point of projective space. -/
lemma exists_X_notMem (x : projSpace R m) :
    ∃ i, (X i : MvPolynomial (Fin (m + 1)) R) ∉ x.asHomogeneousIdeal := by
  by_contra! h
  apply x.not_irrelevant_le
  intro g hg
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hg
  have h0 : coeff 0 g = 0 := by
    change (decomposition.decompose' g 0 : MvPolynomial (Fin (m + 1)) R) = 0 at hg
    rw [decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at hg
    exact hg
  have : g ∈ Ideal.span (X '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro d hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact (mem_support_iff.1 hd) h0
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hd0
    exact ⟨i, Set.mem_univ _, hi⟩
  refine (Ideal.span_le.2 ?_) this
  rintro _ ⟨i, -, rfl⟩
  exact h i

lemma X_mem_one (i : Fin (m + 1)) : (X i : MvPolynomial (Fin (m + 1)) R) ∈ 𝒜 1 :=
  isHomogeneous_X R i

/-- The image of a point of `Proj` in `Spec A₀` is the prime of degree-zero elements vanishing
at it. -/
lemma mem_toSpecZero_iff (x : projSpace R m) (a : 𝒜 0) :
    a ∈ (Proj.toSpecZero 𝒜 x).asIdeal ↔
      (a : MvPolynomial (Fin (m + 1)) R) ∈ x.asHomogeneousIdeal := by
  obtain ⟨i, hi⟩ := exists_X_notMem x
  have hx : x ∈ (Proj.awayι 𝒜 (X i) (X_mem_one i) one_pos).opensRange := by
    rw [Proj.opensRange_awayι]
    exact hi
  obtain ⟨r, rfl⟩ := hx
  have hax : (a : MvPolynomial (Fin (m + 1)) R) * X i ∈ 𝒜 1 := by
    simpa using SetLike.mul_mem_graded a.2 (X_mem_one (R := R) i)
  have h2 := Proj.awayι_preimage_basicOpen 𝒜 (X_mem_one i) one_pos hax one_pos
  have h3 : r ∈ Proj.awayι 𝒜 (X i) (X_mem_one i) one_pos ⁻¹ᵁ
      Proj.basicOpen 𝒜 ((a : MvPolynomial (Fin (m + 1)) R) * X i) ↔
      r ∈ PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem_one i) hax) := by
    rw [h2]
    rfl
  have h4 : Away.isLocalizationElem (X_mem_one (R := R) i) hax = fromZeroRingHom 𝒜 _ a := by
    apply val_injective
    rw [Away.val_mk]
    change _ = Localization.mk _ 1
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [mul_comm]⟩
  rw [h4] at h3
  rw [← Scheme.Hom.comp_apply, Proj.awayι_toSpecZero, Spec.map_apply]
  change fromZeroRingHom 𝒜 _ a ∈ r.asIdeal ↔ _
  have h5 : ((a : MvPolynomial (Fin (m + 1)) R) * X i ∉
      (Proj.awayι 𝒜 (X i) (X_mem_one i) one_pos r).asHomogeneousIdeal) ↔
      fromZeroRingHom 𝒜 _ a ∉ r.asIdeal := h3
  rw [← not_iff_not, ← h5]
  have hp := (Proj.awayι 𝒜 (X i) (X_mem_one i) one_pos r).isPrime
  exact not_iff_not.2
    ⟨fun h => (hp.mem_or_mem h).resolve_right hi, fun h => Ideal.mul_mem_right _ _ h⟩

/-- The image of a point `x` of `ℙᵐ_R` in `Spec R` is `{c : C c ∈ x}`. -/
lemma mem_projSpace_toSpec_iff (x : projSpace R m) (c : R) :
    c ∈ (projSpace.toSpec R m x).asIdeal ↔ C c ∈ x.asHomogeneousIdeal := by
  rw [projSpace.toSpec, Scheme.Hom.comp_apply, Spec.map_apply]
  exact mem_toSpecZero_iff x _

/-- A point of `ℙᵐ_R` over a local ring lies in the special fibre iff all `C c` with `c` in the
maximal ideal vanish at it. -/
lemma mem_specialFibre_projSpace_iff [IsLocalRing R] (x : projSpace R m) :
    x ∈ specialFibre (projSpace.toSpec R m) ↔
      ∀ c ∈ IsLocalRing.maximalIdeal R, C c ∈ x.asHomogeneousIdeal := by
  rw [mem_specialFibre]
  constructor
  · intro h c hc
    rw [← mem_projSpace_toSpec_iff, h]
    exact hc
  · intro h
    apply PrimeSpectrum.ext
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
      fun c hc => ?_
    rw [mem_projSpace_toSpec_iff]
    exact h c hc

/-- The point of `ℙᵐ_R` given by the kernel of a ring homomorphism `θ` to a domain which kills
the homogeneous components of the elements it kills and does not kill the coordinate `xᵢ`. -/
def projPointOfKer {T : Type*} [CommRing T] [IsDomain T]
    (θ : MvPolynomial (Fin (m + 1)) R →+* T)
    (hθ : ∀ h, θ h = 0 → ∀ n, θ (homogeneousComponent n h) = 0) (i : Fin (m + 1))
    (hi : θ (X i) ≠ 0) : projSpace R m where
  asHomogeneousIdeal := ⟨RingHom.ker θ, fun n h hh => by
    change (decomposition.decompose' h n : MvPolynomial (Fin (m + 1)) R) ∈ RingHom.ker θ
    rw [decomposition.decompose'_apply]
    exact hθ h hh n⟩
  isPrime := RingHom.ker_isPrime θ
  not_irrelevant_le h := hi (h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
    (X_mem_one (R := R) i)))

@[simp] lemma mem_projPointOfKer {T : Type*} [CommRing T] [IsDomain T]
    (θ : MvPolynomial (Fin (m + 1)) R →+* T)
    (hθ : ∀ h, θ h = 0 → ∀ n, θ (homogeneousComponent n h) = 0) (i : Fin (m + 1))
    (hi : θ (X i) ≠ 0) (h : MvPolynomial (Fin (m + 1)) R) :
    h ∈ (projPointOfKer θ hθ i hi).asHomogeneousIdeal ↔ θ h = 0 :=
  Iff.rfl

/-! ### Homogeneous components and evaluation -/

/-- Evaluating a homogeneous polynomial of degree `n` at `μ • x` multiplies by `μ ^ n`. -/
lemma eval₂_mul_of_isHomogeneous {σ S : Type*} [CommSemiring S] {φ : MvPolynomial σ R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (f : R →+* S) (x : σ → S) (μ : S) :
    eval₂ f (fun i => μ * x i) φ = μ ^ n * eval₂ f x φ := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hφ.degree_eq_sum_deg_support hd]
  ring

/-- If a ring homomorphism `θ = eval₂ (C ∘ f) g` with `g` homogeneous of a fixed positive degree
kills `h`, it kills every homogeneous component of `h`. -/
lemma eval₂Hom_homogeneousComponent_eq_zero {σ τ k : Type*} [CommRing k] (f : R →+* k)
    (g : σ → MvPolynomial τ k) {e : ℕ} (he : 0 < e) (hg : ∀ i, (g i).IsHomogeneous e)
    {h : MvPolynomial σ R} (hh : eval₂Hom (C.comp f) g h = 0) (n : ℕ) :
    eval₂Hom (C.comp f) g (homogeneousComponent n h) = 0 := by
  have hom : ∀ j, (eval₂Hom (C.comp f) g (homogeneousComponent j h)).IsHomogeneous (e * j) :=
    fun j => (homogeneousComponent_isHomogeneous j h).eval₂ _ _
      (fun r => isHomogeneous_C _ _) hg
  have key : homogeneousComponent (e * n) (eval₂Hom (C.comp f) g h) =
      eval₂Hom (C.comp f) g (homogeneousComponent n h) := by
    conv_lhs => rw [← sum_homogeneousComponent h]
    rw [map_sum, map_sum, Finset.sum_eq_single n]
    · exact homogeneousComponent_eq_self (hom n)
    · intro j _ hjn
      rw [homogeneousComponent_of_mem (hom j), if_neg]
      exact fun h' => hjn (Nat.eq_of_mul_eq_mul_left he h').symm
    · intro hn
      rw [Finset.mem_range, not_lt] at hn
      rw [homogeneousComponent_eq_zero n h (by omega)]
      simp
  rw [← key, hh, map_zero]

/-! ### Points containing the kernel of an evaluation -/

section Local

variable [IsLocalRing R]

/-- For a point `y` of the special fibre, the map `k → R[x₀, …, xₘ] ⧸ y` from the residue
field. -/
def residueLift (y : projSpace R m)
    (hy : ∀ c ∈ IsLocalRing.maximalIdeal R, C c ∈ y.asHomogeneousIdeal) :
    IsLocalRing.ResidueField R →+*
      MvPolynomial (Fin (m + 1)) R ⧸ y.asHomogeneousIdeal.toIdeal :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp C) fun c hc =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hy c hc)

lemma residueLift_residue (y : projSpace R m)
    (hy : ∀ c ∈ IsLocalRing.maximalIdeal R, C c ∈ y.asHomogeneousIdeal) (c : R) :
    residueLift y hy (IsLocalRing.residue R c) = Ideal.Quotient.mk _ (C c) :=
  rfl

/-- **Points containing the kernel of an evaluation.** Let `θ = eval₂ (C ∘ residue) g` with `g`
homogeneous of positive degree `e`, and let `y` be a point of the special fibre. If
`g(pt) = μ · x` in `R[x₀, …, xₘ] ⧸ y` for some `pt` and some `μ ≠ 0` (i.e. `y` is the image of
`pt` under the map given by `g`), then `ker θ ⊆ y`. -/
lemma mem_of_eval₂Hom_eq_zero {τ : Type*} (y : projSpace R m)
    (hy : ∀ c ∈ IsLocalRing.maximalIdeal R, C c ∈ y.asHomogeneousIdeal)
    (g : Fin (m + 1) → MvPolynomial τ (IsLocalRing.ResidueField R)) {e : ℕ} (he : 0 < e)
    (hg : ∀ i, (g i).IsHomogeneous e)
    (pt : τ → MvPolynomial (Fin (m + 1)) R ⧸ y.asHomogeneousIdeal.toIdeal)
    (μ : MvPolynomial (Fin (m + 1)) R ⧸ y.asHomogeneousIdeal.toIdeal) (hμ : μ ≠ 0)
    (hpt : ∀ i, eval₂Hom (residueLift y hy) pt (g i) = μ * Ideal.Quotient.mk _ (X i))
    {h : MvPolynomial (Fin (m + 1)) R}
    (hh : eval₂Hom (C.comp (IsLocalRing.residue R)) g h = 0) :
    h ∈ y.asHomogeneousIdeal := by
  have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  have hcomp : (eval₂Hom (residueLift y hy) pt).comp
      (eval₂Hom (C.comp (IsLocalRing.residue R)) g) =
      eval₂Hom ((Ideal.Quotient.mk _).comp C) (fun i => μ * Ideal.Quotient.mk _ (X i)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp [residueLift_residue]
    · simp [hpt]
  have hmk : eval₂Hom ((Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal).comp C)
      (fun i => Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mk _ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_) <;> simp
  suffices hn : ∀ n, homogeneousComponent n h ∈ y.asHomogeneousIdeal by
    rw [← sum_homogeneousComponent h]
    exact Ideal.sum_mem _ fun n _ => hn n
  intro n
  have h0 := eval₂Hom_homogeneousComponent_eq_zero _ g he hg hh n
  have h1 := congrArg (eval₂Hom (residueLift y hy) pt) h0
  rw [← RingHom.comp_apply, hcomp, map_zero, coe_eval₂Hom,
    eval₂_mul_of_isHomogeneous (homogeneousComponent_isHomogeneous n h), ← coe_eval₂Hom,
    hmk] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact (pow_ne_zero _ hμ h2).elim
  · exact Ideal.Quotient.eq_zero_iff_mem.1 h2

/-- **Points on a line are determined by their image.** Let
`θ = eval₂ (C ∘ residue) g : R[x₀, …, xₘ] → k[t]` with `g` linear, and let `y` be a point of the
special fibre which is the image of `pt ≠ 0` under `g` (`g(pt) = x` in `R[x₀, …, xₘ] ⧸ y`). Then
`θ` kills `y`. -/
lemma eval₂Hom_eq_zero_of_mem (y : projSpace R m)
    (hy : ∀ c ∈ IsLocalRing.maximalIdeal R, C c ∈ y.asHomogeneousIdeal)
    (g : Fin (m + 1) → MvPolynomial (Fin (0 + 1)) (IsLocalRing.ResidueField R))
    (hg : ∀ i, (g i).IsHomogeneous 1)
    (pt : Fin (0 + 1) → MvPolynomial (Fin (m + 1)) R ⧸ y.asHomogeneousIdeal.toIdeal)
    (hpt0 : pt 0 ≠ 0)
    (hpt : ∀ i, eval₂Hom (residueLift y hy) pt (g i) = Ideal.Quotient.mk _ (X i))
    {h : MvPolynomial (Fin (m + 1)) R} (hh : h ∈ y.asHomogeneousIdeal) :
    eval₂Hom (C.comp (IsLocalRing.residue R)) g h = 0 := by
  have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  have hcomp : (eval₂Hom (residueLift y hy) pt).comp
      (eval₂Hom (C.comp (IsLocalRing.residue R)) g) = Ideal.Quotient.mk _ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp [residueLift_residue]
    · simp [hpt]
  rw [← sum_homogeneousComponent h, map_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  have hn : (eval₂Hom (C.comp (IsLocalRing.residue R)) g
      (homogeneousComponent n h)).IsHomogeneous n := by
    simpa using (homogeneousComponent_isHomogeneous n h).eval₂
      (C.comp (IsLocalRing.residue R)) g (fun r => isHomogeneous_C _ _) hg
  have h1 : eval₂Hom (residueLift y hy) pt
      (eval₂Hom (C.comp (IsLocalRing.residue R)) g (homogeneousComponent n h)) = 0 := by
    rw [← RingHom.comp_apply, hcomp, Ideal.Quotient.eq_zero_iff_mem]
    exact homogeneousComponent_mem_of_mem y.asHomogeneousIdeal.isHomogeneous hh n
  rw [isHomogeneous_fin_one hn] at h1 ⊢
  simp only [map_mul, map_pow, eval₂Hom_C, eval₂Hom_X'] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · rw [(residueLift y hy).injective (h2.trans (map_zero _).symm), C_0, zero_mul]
  · exact (pow_ne_zero _ hpt0 h2).elim

omit [IsLocalRing R] in
/-- Points of `ℙᵐ_R` with the same ideal are equal. -/
lemma projSpace_ext {x y : projSpace R m} (h : x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal)
    (h' : y.asHomogeneousIdeal ≤ x.asHomogeneousIdeal) : x = y :=
  le_antisymm (α := ProjectiveSpectrum 𝒜) h h'

/-- **A point of the special fibre on a line is the point given by the line.** -/
lemma eq_projPointOfKer_of_line (y : projSpace R m)
    (hy : ∀ c ∈ IsLocalRing.maximalIdeal R, C c ∈ y.asHomogeneousIdeal)
    (g : Fin (m + 1) → MvPolynomial (Fin (0 + 1)) (IsLocalRing.ResidueField R))
    (hg : ∀ i, (g i).IsHomogeneous 1)
    (hθ : ∀ h, eval₂Hom (C.comp (IsLocalRing.residue R)) g h = 0 →
      ∀ n, eval₂Hom (C.comp (IsLocalRing.residue R)) g (homogeneousComponent n h) = 0)
    (i : Fin (m + 1)) (hi : eval₂Hom (C.comp (IsLocalRing.residue R)) g (X i) ≠ 0)
    (pt0 : MvPolynomial (Fin (m + 1)) R ⧸ y.asHomogeneousIdeal.toIdeal) (hpt0 : pt0 ≠ 0)
    (hpt : ∀ i, eval₂Hom (residueLift y hy) ![pt0] (g i) = Ideal.Quotient.mk _ (X i)) :
    y = projPointOfKer (eval₂Hom (C.comp (IsLocalRing.residue R)) g) hθ i hi := by
  refine projSpace_ext (fun h hh => ?_) fun h hh => ?_
  · exact eval₂Hom_eq_zero_of_mem y hy g hg ![pt0] hpt0 hpt hh
  · refine mem_of_eval₂Hom_eq_zero y hy g one_pos hg ![pt0] 1 one_ne_zero (fun i => ?_) hh
    rw [hpt, one_mul]

omit [IsLocalRing R] in
/-- The points specializing from `x` (the closure of `x`) form a preconnected set. -/
lemma isPreconnected_setOf_le (x : projSpace R m) :
    _root_.IsPreconnected {y : projSpace R m | x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal} := by
  have : {y : projSpace R m | x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal} =
      closure ({x} : Set (ProjectiveSpectrum 𝒜)) := by
    ext y
    exact ProjectiveSpectrum.le_iff_mem_closure _ x y
  rw [this]
  exact isPreconnected_singleton.closure

end Local

end

end TemperedFundamentalGroups
