/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateOmegaNorm

/-!
# The overlap identification of normalisations at every level (MR12 T2 S6, G4 over `V₀`)

For `W = A₀[1/a₀] = A₁[1/a₁]` and the normalisations `B₀`, `B₁` of `A₀`, `A₁` in a field `L`,
`NormOverlap.omegaEquiv` identifies `(B₀/I)[1/ā₀] ≃ (B₁/I)[1/ā₁]` over `W/I` for every ideal
`I` of the base. Here:

* `NormOverlap.awayEquiv_algebraMap`, `NormOverlap.awayAlg_quot` (the `W`-algebra `C[1/a]` of a
  quotient `C = B/I` factors through `W/I`);
* **`NormOverlap.omegaEquivW`**: `omegaEquiv` as an isomorphism over `W` itself;
* **`NormOverlap.exists_mul_pow_eq`**, **`NormOverlap.omegaEquiv_mul_pow`**: for `b ∈ B₀` there
  are `y ∈ B₁`, `k` with `b ↦ y / a₁ᵏ` under `B₀[1/a₀] ≃ B₁[1/a₁]`, and then
  `omegaEquiv I (b̄/1) · ā₁ᵏ = ȳ/1` for **every** `I` (the same witness at all levels and at the
  special fibre).
-/

universe u

namespace SemistableReduction

namespace NormOverlap

noncomputable section

section Away

variable {O A W B : Type u} [CommRing O] [CommRing A] [CommRing W] [CommRing B]
  [Algebra O A] [Algebra O W] [Algebra A W] [IsScalarTower O A W] [Algebra A B]
  (a : A) [IsLocalization.Away a W] (I : Ideal O)
  [Algebra (A ⧸ I.map (algebraMap O A)) (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
    (W ⧸ I.map (algebraMap O W))]

/-- `awayEquiv` on the image of `B/IB`: `b̄/1 ↦ (b/1) mod I`. -/
lemma awayEquiv_algebraMap
    (hS : ∀ x : A, algebraMap (A ⧸ I.map (algebraMap O A)) (W ⧸ I.map (algebraMap O W))
      (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A W x)) (b : B) :
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
      (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
    letI := algW (B := B) (W := W) a
    awayEquiv a I hS (algebraMap (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
        (Localization.Away (algebraMap (A ⧸ I.map (algebraMap O A))
          (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a)))
        (Ideal.Quotient.mk _ b)) =
      Ideal.Quotient.mk _ (algebraMap B (Localization.Away (algebraMap A B a)) b) := by
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
    (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
  letI := algW (B := B) (W := W) a
  haveI := AwayAlg.tower (C := B) (W := W) a
  letI := (qmap (B := B) (W := W) a I).toAlgebra
  haveI : IsLocalization.Away (algebraMap (A ⧸ I.map (algebraMap O A))
      (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a))
      (Localization.Away (algebraMap A B a) ⧸ (I.map (algebraMap O W)).map
        (algebraMap W (Localization.Away (algebraMap A B a)))) :=
    NormAway.isLocalization_quotMap (R := W) (I.map (algebraMap O A)) (I.map (algebraMap O W))
      (map_eq I) a
  exact ((IsLocalization.algEquiv (Submonoid.powers (algebraMap (A ⧸ I.map (algebraMap O A))
      (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a)))
    (Localization.Away (algebraMap (A ⧸ I.map (algebraMap O A))
        (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a)))
    (Localization.Away (algebraMap A B a) ⧸ (I.map (algebraMap O W)).map
        (algebraMap W (Localization.Away (algebraMap A B a))))).commutes
      (Ideal.Quotient.mk _ b)).trans (NormAway.quotMap_mk _ _ (map_eq I) b)

omit [IsScalarTower O A W] in
/-- **The `W`-algebra `C[1/a]` of a quotient `C = B/IB` factors through `W/I`**: the map
`W → C[1/a]` (`AwayAlg.alg` over `A`) is `W → W/I → C[1/ā]` (`AwayAlg.alg` over `A/I`). -/
lemma awayAlg_quot
    (hS : ∀ x : A, algebraMap (A ⧸ I.map (algebraMap O A)) (W ⧸ I.map (algebraMap O W))
      (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A W x)) (w : W) :
    (letI := AwayAlg.alg (W := W) (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) a;
      algebraMap W (Localization.Away (algebraMap A
        (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) a)) w) =
    (letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
      (Ideal.Quotient.mk (I.map (algebraMap O A)) a);
      algebraMap (W ⧸ I.map (algebraMap O W)) (Localization.Away (algebraMap
        (A ⧸ I.map (algebraMap O A)) (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
        (Ideal.Quotient.mk _ a))) (Ideal.Quotient.mk _ w)) := by
  letI := AwayAlg.alg (W := W) (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) a
  haveI := AwayAlg.tower (W := W) (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) a
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
    (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
  haveI := AwayAlg.tower (W := W ⧸ I.map (algebraMap O W))
    (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
    (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers a) (S := W)
    (j := algebraMap W (Localization.Away (algebraMap A
      (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) a)))
    (k := (algebraMap (W ⧸ I.map (algebraMap O W)) (Localization.Away (algebraMap
        (A ⧸ I.map (algebraMap O A)) (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
        (Ideal.Quotient.mk _ a)))).comp (Ideal.Quotient.mk _)) (RingHom.ext fun x ↦ ?_)) w
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply]
  change _ = algebraMap (W ⧸ I.map (algebraMap O W)) (Localization.Away (algebraMap
      (A ⧸ I.map (algebraMap O A)) (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
      (Ideal.Quotient.mk _ a))) (Ideal.Quotient.mk _ (algebraMap A W x))
  rw [← hS, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (A ⧸ I.map (algebraMap O A))
      (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
      (Localization.Away (algebraMap (A ⧸ I.map (algebraMap O A))
        (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a))),
    IsScalarTower.algebraMap_apply A (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
      (Localization.Away (algebraMap A (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) a))]
  rfl

end Away

lemma quotEquiv_mk {W X Y : Type u} [CommRing W] [CommRing X] [CommRing Y] [Algebra W X]
    [Algebra W Y] (J : Ideal W) (e : X ≃ₐ[W] Y) (x : X) :
    quotEquiv J e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (e x) := rfl

/-- `awayCongr` of the identity is the identity. -/
lemma awayCongr_refl_apply {S Ws C : Type u} [CommRing S] [CommRing Ws] [CommRing C]
    [Algebra S Ws] [Algebra S C] (s : S) [IsLocalization.Away s Ws]
    (x : Localization.Away (algebraMap S C s)) :
    letI := AwayAlg.alg (W := Ws) (C := C) s
    awayCongr (Ws := Ws) s (AlgEquiv.refl : C ≃ₐ[S] C) x = x := by
  letI := AwayAlg.alg (W := Ws) (C := C) s
  have h : ((awayCongr (Ws := Ws) s (AlgEquiv.refl : C ≃ₐ[S] C)).toRingEquiv.toRingHom :
      Localization.Away (algebraMap S C s) →+* Localization.Away (algebraMap S C s)) =
      RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap S C s)) (RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply, RingHom.id_apply]
      exact IsLocalization.map_eq (M := Submonoid.powers (algebraMap S C s))
        (T := Submonoid.powers (algebraMap S C s)) (S := Localization.Away (algebraMap S C s))
        (Q := Localization.Away (algebraMap S C s))
        (g := ((AlgEquiv.refl : C ≃ₐ[S] C).toRingEquiv : C →+* C)) (fun _ h ↦ h) c)
  exact RingHom.congr_fun h x

/-- The inverse of `awayCongr` of the identity is the identity. -/
lemma awayCongr_refl_symm_apply {S Ws C : Type u} [CommRing S] [CommRing Ws] [CommRing C]
    [Algebra S Ws] [Algebra S C] (s : S) [IsLocalization.Away s Ws]
    (x : Localization.Away (algebraMap S C s)) :
    letI := AwayAlg.alg (W := Ws) (C := C) s
    (awayCongr (Ws := Ws) s (AlgEquiv.refl : C ≃ₐ[S] C)).symm x = x := by
  letI := AwayAlg.alg (W := Ws) (C := C) s
  rw [AlgEquiv.symm_apply_eq, awayCongr_refl_apply]

section Main

variable {O A₀ A₁ W B₀ B₁ : Type u} {L : Type*} [CommRing O] [CommRing A₀] [CommRing A₁]
  [CommRing W] [CommRing B₀] [CommRing B₁] [Field L]
  [Algebra O A₀] [Algebra O A₁] [Algebra O W] [Algebra A₀ W] [Algebra A₁ W]
  [IsScalarTower O A₀ W] [IsScalarTower O A₁ W]
  [Algebra A₀ L] [Algebra A₁ L] [Algebra W L] [IsScalarTower A₀ W L] [IsScalarTower A₁ W L]
  [Algebra A₀ B₀] [Algebra B₀ L] [IsScalarTower A₀ B₀ L] [IsIntegralClosure B₀ A₀ L]
  [Algebra A₁ B₁] [Algebra B₁ L] [IsScalarTower A₁ B₁ L] [IsIntegralClosure B₁ A₁ L]
  (a₀ : A₀) (a₁ : A₁) [IsLocalization.Away a₀ W] [IsLocalization.Away a₁ W]
  (ha₀ : algebraMap A₀ L a₀ ≠ 0) (ha₁ : algebraMap A₁ L a₁ ≠ 0)

/-- **The witness of the overlap identification**: under `B₀[1/a₀] ≃ B₁[1/a₁]` (both the
normalisation of `W` in `L`), `b/1 ↦ y/a₁ᵏ`. -/
theorem exists_mul_pow_eq (b : B₀) : ∃ (y : B₁) (k : ℕ),
    (letI := algW (B := B₀) (W := W) a₀; letI := algL (B := B₀) a₀ ha₀
      letI := algW (B := B₁) (W := W) a₁; letI := algL (B := B₁) a₁ ha₁
      haveI := towerWL (B := B₀) (W := W) a₀ ha₀
      haveI := isIntegralClosure_away (B := B₀) (W := W) a₀ ha₀
      haveI := towerWL (B := B₁) (W := W) a₁ ha₁
      haveI := isIntegralClosure_away (B := B₁) (W := W) a₁ ha₁
      IsIntegralClosure.equiv (R := W) (B := L) (A := Localization.Away (algebraMap A₀ B₀ a₀))
        (Localization.Away (algebraMap A₁ B₁ a₁)) (algebraMap B₀ _ b)) *
      algebraMap B₁ (Localization.Away (algebraMap A₁ B₁ a₁)) (algebraMap A₁ B₁ a₁) ^ k =
      algebraMap B₁ _ y := by
  obtain ⟨⟨y, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A₁ B₁ a₁))
    (letI := algW (B := B₀) (W := W) a₀; letI := algL (B := B₀) a₀ ha₀
      letI := algW (B := B₁) (W := W) a₁; letI := algL (B := B₁) a₁ ha₁
      haveI := towerWL (B := B₀) (W := W) a₀ ha₀
      haveI := isIntegralClosure_away (B := B₀) (W := W) a₀ ha₀
      haveI := towerWL (B := B₁) (W := W) a₁ ha₁
      haveI := isIntegralClosure_away (B := B₁) (W := W) a₁ ha₁
      IsIntegralClosure.equiv (R := W) (B := L) (A := Localization.Away (algebraMap A₀ B₀ a₀))
        (Localization.Away (algebraMap A₁ B₁ a₁)) (algebraMap B₀ _ b))
  obtain ⟨k, hk⟩ := s.2
  refine ⟨y, k, ?_⟩
  have hs : (s : B₁) = algebraMap A₁ B₁ a₁ ^ k := hk.symm
  rw [← map_pow, ← hs]
  exact h

variable (I : Ideal O)
  [Algebra (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))]
  [Algebra (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
    (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
    (W ⧸ I.map (algebraMap O W))]
  (hS₀ : ∀ x : A₀, algebraMap (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))
    (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₀ W x))
  (hS₁ : ∀ x : A₁, algebraMap (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))
    (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₁ W x))

set_option maxHeartbeats 400000 in
-- unfolding `omegaEquiv`
/-- **`omegaEquiv` on the witness**: if `b/1 ↦ y/a₁ᵏ` under `B₀[1/a₀] ≃ B₁[1/a₁]`, then
`omegaEquiv I (b̄/1) · ā₁ᵏ = ȳ/1` for every ideal `I` of the base. -/
theorem omegaEquiv_mul_pow (b : B₀) (y : B₁) (k : ℕ)
    (h : (letI := algW (B := B₀) (W := W) a₀; letI := algL (B := B₀) a₀ ha₀
      letI := algW (B := B₁) (W := W) a₁; letI := algL (B := B₁) a₁ ha₁
      haveI := towerWL (B := B₀) (W := W) a₀ ha₀
      haveI := isIntegralClosure_away (B := B₀) (W := W) a₀ ha₀
      haveI := towerWL (B := B₁) (W := W) a₁ ha₁
      haveI := isIntegralClosure_away (B := B₁) (W := W) a₁ ha₁
      IsIntegralClosure.equiv (R := W) (B := L) (A := Localization.Away (algebraMap A₀ B₀ a₀))
        (Localization.Away (algebraMap A₁ B₁ a₁)) (algebraMap B₀ _ b)) *
      algebraMap B₁ (Localization.Away (algebraMap A₁ B₁ a₁)) (algebraMap A₁ B₁ a₁) ^ k =
      algebraMap B₁ _ y) :
    omegaEquiv (B₀ := B₀) (B₁ := B₁) (L := L) a₀ a₁ I hS₀ hS₁ ha₀ ha₁
        (algebraMap (B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀)) _
          (Ideal.Quotient.mk _ b)) *
      algebraMap (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
        (Localization.Away (algebraMap (A₁ ⧸ I.map (algebraMap O A₁))
          (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) (Ideal.Quotient.mk _ a₁)))
        (Ideal.Quotient.mk _ (algebraMap A₁ B₁ a₁)) ^ k =
      algebraMap (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) _
        (Ideal.Quotient.mk _ y) := by
  letI := algW (B := B₀) (W := W) a₀
  letI := algL (B := B₀) a₀ ha₀
  haveI := towerL (B := B₀) a₀ ha₀
  haveI := towerWL (B := B₀) (W := W) a₀ ha₀
  haveI := isIntegralClosure_away (B := B₀) (W := W) a₀ ha₀
  letI := algW (B := B₁) (W := W) a₁
  letI := algL (B := B₁) a₁ ha₁
  haveI := towerL (B := B₁) a₁ ha₁
  haveI := towerWL (B := B₁) (W := W) a₁ ha₁
  haveI := isIntegralClosure_away (B := B₁) (W := W) a₁ ha₁
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀))
    (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
    (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
  apply (awayEquiv (B := B₁) a₁ I hS₁).injective
  rw [map_mul, map_pow]
  unfold omegaEquiv
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    awayEquiv_algebraMap, awayEquiv_algebraMap, awayEquiv_algebraMap, quotEquiv_mk,
    ← map_pow, ← map_mul]
  exact congrArg (Ideal.Quotient.mk _) h

/-- **`omegaEquiv` over `W` itself**: `(B₀/I)[1/a₀] ≃ₐ[W] (B₁/I)[1/a₁]`, the `W`-algebras being
`AwayAlg.alg` over `A₀`, `A₁` (as in `NodeEtaleGlue.Overlap.φQn`). -/
def omegaEquivW :
    letI := AwayAlg.alg (W := W) (C := B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀)) a₀
    letI := AwayAlg.alg (W := W) (C := B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) a₁
    Localization.Away (algebraMap A₀ (B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀)) a₀)
      ≃ₐ[W] Localization.Away
        (algebraMap A₁ (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) a₁) :=
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀))
    (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
    (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
  letI := AwayAlg.alg (W := W) (C := B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀)) a₀
  letI := AwayAlg.alg (W := W) (C := B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) a₁
  AlgEquiv.ofRingEquiv (f := (omegaEquiv (B₀ := B₀) (B₁ := B₁) (L := L) a₀ a₁ I hS₀ hS₁ ha₀
      ha₁).toRingEquiv) fun w ↦ by
    rw [awayAlg_quot (a := a₀) (I := I) (hS := hS₀) w,
      awayAlg_quot (a := a₁) (I := I) (hS := hS₁) w]
    exact (omegaEquiv (B₀ := B₀) (B₁ := B₁) (L := L) a₀ a₁ I hS₀ hS₁ ha₀ ha₁).commutes _

/-- **The overlap identification at all levels at once**: for `b ∈ B₀` there are `y ∈ B₁`, `k`
with `omegaEquiv I (b̄/1) · ā₁ᵏ = ȳ/1` for **every** ideal `I` of the base. -/
theorem exists_omegaEquiv_mul_pow (b : B₀) : ∃ (y : B₁) (k : ℕ), ∀ (I : Ideal O)
    [Algebra (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))]
    [Algebra (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))]
    [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
      (W ⧸ I.map (algebraMap O W))]
    [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
      (W ⧸ I.map (algebraMap O W))]
    (hS₀ : ∀ x : A₀, algebraMap (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))
      (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₀ W x))
    (hS₁ : ∀ x : A₁, algebraMap (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))
      (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₁ W x)),
    omegaEquiv (B₀ := B₀) (B₁ := B₁) (L := L) a₀ a₁ I hS₀ hS₁ ha₀ ha₁
        (algebraMap (B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀)) _
          (Ideal.Quotient.mk _ b)) *
      algebraMap (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
        (Localization.Away (algebraMap (A₁ ⧸ I.map (algebraMap O A₁))
          (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) (Ideal.Quotient.mk _ a₁)))
        (Ideal.Quotient.mk _ (algebraMap A₁ B₁ a₁)) ^ k =
      algebraMap (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) _
        (Ideal.Quotient.mk _ y) := by
  obtain ⟨y, k, h⟩ := exists_mul_pow_eq (W := W) (B₀ := B₀) (B₁ := B₁) a₀ a₁ ha₀ ha₁ b
  exact ⟨y, k, fun I _ _ _ _ hS₀ hS₁ ↦
    omegaEquiv_mul_pow (W := W) a₀ a₁ ha₀ ha₁ I hS₀ hS₁ b y k h⟩

end Main

end

end NormOverlap

end SemistableReduction
