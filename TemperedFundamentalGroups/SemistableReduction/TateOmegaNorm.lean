/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue0V0
import TemperedFundamentalGroups.SemistableReduction.NormAway
import TemperedFundamentalGroups.SemistableReduction.FormalKummerNode

/-!
# The overlap datum `ω` for coverings given by normalisations (Blueprint §12.8, M2.3 (f))

Let `W = A₀[1/a₀] = A₁[1/a₁]` and let `B₀`, `B₁` be the normalisations of `A₀`, `A₁` in a field
`L`. Both `B₀[1/a₀]` and `B₁[1/a₁]` are the normalisation of `W` in `L`
(`NormAway.isIntegralClosure`), so modulo `J = I·(-)` for an ideal `I` of the base `O`:

* `NormOverlap.awayEquiv`: `(B/JB)[1/ā] ≃ B[1/a]/J` over `W/J` (`NormAway.isLocalization_quotMap`);
* `NormOverlap.quotEquiv`, `NormOverlap.awayCongr`: functoriality of `X ↦ X/J`, `C ↦ C[1/s]`;
* **`NormOverlap.omegaEquiv`** (generic): `(B₀/J)[1/ā₀] ≃ₐ[W/J] (B₁/J)[1/ā₁]`;
* **`TateGlue0.omegaNorm`**: the instance at the Tate charts `T0`, `T1`, `T01`, of the type of the
  overlap datum `ω` for `C0 = B₀/J`, `C1 = B₁/J`;
* **`TateGlue0.omegaNormC`**: the same as a term of `TateGlue0.OmegaC hκ hπ Sp (B₀/J)` for a
  covering `Sp` over `V₁` with `Sp.C1 ≃ B₁/J`.
-/

universe u

namespace SemistableReduction

namespace NormOverlap

noncomputable section

section Away

variable {O A W B : Type u} [CommRing O] [CommRing A] [CommRing W] [CommRing B]
  [Algebra O A] [Algebra O W] [Algebra A W] [IsScalarTower O A W] [Algebra A B]
  (a : A) [IsLocalization.Away a W] (I : Ideal O)

/-- `B[1/a]` over `W = A[1/a]`. -/
@[reducible] def algW : Algebra W (Localization.Away (algebraMap A B a)) := AwayAlg.alg a

omit [IsLocalization.Away a W] in
lemma map_eq : I.map (algebraMap O W) = (I.map (algebraMap O A)).map (algebraMap A W) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- `B/JB → B[1/a]/J`. -/
def qmap : letI := algW (B := B) (W := W) a
    B ⧸ (I.map (algebraMap O A)).map (algebraMap A B) →+*
      Localization.Away (algebraMap A B a) ⧸ (I.map (algebraMap O W)).map
        (algebraMap W (Localization.Away (algebraMap A B a))) :=
  letI := algW (B := B) (W := W) a
  haveI := AwayAlg.tower (C := B) (W := W) a
  NormAway.quotMap (R := W) (I.map (algebraMap O A)) (I.map (algebraMap O W)) (map_eq I)

variable [Algebra (A ⧸ I.map (algebraMap O A)) (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
    (W ⧸ I.map (algebraMap O W))]

/-- **`(B/JB)[1/ā] ≅ B[1/a]/J`** over the special fibre `W/J` of `W = A[1/a]`. -/
def awayEquiv (hS : ∀ x : A, algebraMap (A ⧸ I.map (algebraMap O A)) (W ⧸ I.map (algebraMap O W))
      (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A W x)) :
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
      (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
    letI := algW (B := B) (W := W) a
    Localization.Away (algebraMap (A ⧸ I.map (algebraMap O A))
        (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a)) ≃ₐ[
      W ⧸ I.map (algebraMap O W)]
      Localization.Away (algebraMap A B a) ⧸ (I.map (algebraMap O W)).map
        (algebraMap W (Localization.Away (algebraMap A B a))) := by
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
    (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
  haveI := AwayAlg.tower (W := W ⧸ I.map (algebraMap O W))
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
  let f := IsLocalization.algEquiv (Submonoid.powers (algebraMap (A ⧸ I.map (algebraMap O A))
      (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a)))
    (Localization.Away (algebraMap (A ⧸ I.map (algebraMap O A))
        (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a)))
    (Localization.Away (algebraMap A B a) ⧸ (I.map (algebraMap O W)).map
        (algebraMap W (Localization.Away (algebraMap A B a))))
  refine AlgEquiv.ofRingEquiv (f := f.toRingEquiv) fun y ↦ ?_
  have h := IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk
      (I.map (algebraMap O A)) a)) (S := W ⧸ I.map (algebraMap O W))
    (j := f.toRingHom.comp (algebraMap _ _)) (k := algebraMap _ _) (RingHom.ext fun x ↦ by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply
        (A ⧸ I.map (algebraMap O A)) (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
        (Localization.Away (algebraMap (A ⧸ I.map (algebraMap O A))
          (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a)))]
      change f _ = _
      rw [AlgEquiv.commutes, hS, Ideal.Quotient.algebraMap_quotient_map_quotient,
        Ideal.Quotient.algebraMap_quotient_map_quotient]
      change qmap a I _ = _
      rw [qmap, NormAway.quotMap_mk, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply])
  exact RingHom.congr_fun h y

end Away

section Norm

variable {A W B : Type u} {L : Type*} [CommRing A] [CommRing W] [CommRing B] [Field L]
  [Algebra A W] [Algebra A L] [Algebra W L] [IsScalarTower A W L]
  [Algebra A B] [Algebra B L] [IsScalarTower A B L]
  (a : A) [IsLocalization.Away a W] (ha : algebraMap A L a ≠ 0)

omit [Algebra A W] [Algebra W L] [IsScalarTower A W L] in
include ha in
lemma isUnit_a : IsUnit (algebraMap B L (algebraMap A B a)) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact ha.isUnit

/-- `B[1/a] → L`. -/
@[reducible] def algL : Algebra (Localization.Away (algebraMap A B a)) L :=
  (IsLocalization.Away.lift (algebraMap A B a) (isUnit_a a ha)).toAlgebra

omit [Algebra A W] [Algebra W L] [IsScalarTower A W L] in
lemma towerL : letI := algL (B := B) a ha
    IsScalarTower B (Localization.Away (algebraMap A B a)) L :=
  letI := algL (B := B) a ha
  IsScalarTower.of_algebraMap_eq fun x ↦ (IsLocalization.Away.lift_eq _ _ x).symm

lemma towerWL : letI := algW (B := B) (W := W) a; letI := algL (B := B) a ha
    IsScalarTower W (Localization.Away (algebraMap A B a)) L := by
  letI := algW (B := B) (W := W) a
  haveI := AwayAlg.tower (C := B) (W := W) a
  letI := algL (B := B) a ha
  refine IsScalarTower.of_algebraMap_eq fun y ↦ RingHom.congr_fun
    (IsLocalization.ringHom_ext (Submonoid.powers a) (j := algebraMap W L)
      (k := (algebraMap (Localization.Away (algebraMap A B a)) L).comp
        (algebraMap W (Localization.Away (algebraMap A B a)))) (RingHom.ext fun x ↦ ?_)) y
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply A W,
    IsScalarTower.algebraMap_apply A B (Localization.Away (algebraMap A B a))]
  exact (IsScalarTower.algebraMap_apply A B L x).trans
    (IsLocalization.Away.lift_eq (algebraMap A B a) (isUnit_a a ha) _).symm

include ha in
/-- **`B[1/a]` is the normalisation of `W = A[1/a]` in `L`** (`NormAway.isIntegralClosure`). -/
theorem isIntegralClosure_away [IsIntegralClosure B A L] :
    letI := algW (B := B) (W := W) a; letI := algL (B := B) a ha
    IsIntegralClosure (Localization.Away (algebraMap A B a)) W L := by
  letI := algW (B := B) (W := W) a
  letI := algL (B := B) a ha
  haveI := towerL (B := B) a ha
  haveI := towerWL (B := B) (W := W) a ha
  exact NormAway.isIntegralClosure (B₁ := B) a ha

end Norm

/-- An isomorphism of `W`-algebras induces one of their reductions modulo `J` over `W/J`. -/
def quotEquiv {W X Y : Type u} [CommRing W] [CommRing X] [CommRing Y] [Algebra W X]
    [Algebra W Y] (J : Ideal W) (e : X ≃ₐ[W] Y) :
    (X ⧸ J.map (algebraMap W X)) ≃ₐ[W ⧸ J] Y ⧸ J.map (algebraMap W Y) :=
  AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv _ _ e.toRingEquiv (by
    rw [Ideal.map_map]
    congr 1
    exact (e.toAlgHom.comp_algebraMap).symm)) fun y ↦ by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.algebraMap_quotient_map_quotient]
    simp

/-- An isomorphism `C ≃ₐ[S] C'` induces `C[1/s] ≃ C'[1/s]` over `W = S[1/s]`. -/
def awayCongr {S Ws C C' : Type u} [CommRing S] [CommRing Ws] [CommRing C] [CommRing C']
    [Algebra S Ws] [Algebra S C] [Algebra S C'] (s : S) [IsLocalization.Away s Ws]
    (e : C ≃ₐ[S] C') :
    letI := AwayAlg.alg (W := Ws) (C := C) s; letI := AwayAlg.alg (W := Ws) (C := C') s
    Localization.Away (algebraMap S C s) ≃ₐ[Ws] Localization.Away (algebraMap S C' s) := by
  letI := AwayAlg.alg (W := Ws) (C := C) s
  letI := AwayAlg.alg (W := Ws) (C := C') s
  haveI := AwayAlg.tower (W := Ws) (C := C) s
  haveI := AwayAlg.tower (W := Ws) (C := C') s
  let f := IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (algebraMap S C s))
    (T := Submonoid.powers (algebraMap S C' s)) (Localization.Away (algebraMap S C s))
    (Localization.Away (algebraMap S C' s)) e.toRingEquiv (by
      rw [Submonoid.map_powers]
      congr 1
      exact e.commutes s)
  refine AlgEquiv.ofRingEquiv (f := f) fun y ↦ RingHom.congr_fun
    (IsLocalization.ringHom_ext (Submonoid.powers s) (S := Ws)
      (j := f.toRingHom.comp (algebraMap _ _)) (k := algebraMap _ _) (RingHom.ext fun x ↦ ?_)) y
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply S C (Localization.Away (algebraMap S C s)),
    IsScalarTower.algebraMap_apply S C' (Localization.Away (algebraMap S C' s))]
  change f _ = _
  rw [IsLocalization.ringEquivOfRingEquiv_eq]
  simp

section Main

variable {O A₀ A₁ W B₀ B₁ : Type u} {L : Type*} [CommRing O] [CommRing A₀] [CommRing A₁]
  [CommRing W] [CommRing B₀] [CommRing B₁] [Field L]
  [Algebra O A₀] [Algebra O A₁] [Algebra O W] [Algebra A₀ W] [Algebra A₁ W]
  [IsScalarTower O A₀ W] [IsScalarTower O A₁ W]
  [Algebra A₀ L] [Algebra A₁ L] [Algebra W L] [IsScalarTower A₀ W L] [IsScalarTower A₁ W L]
  [Algebra A₀ B₀] [Algebra B₀ L] [IsScalarTower A₀ B₀ L] [IsIntegralClosure B₀ A₀ L]
  [Algebra A₁ B₁] [Algebra B₁ L] [IsScalarTower A₁ B₁ L] [IsIntegralClosure B₁ A₁ L]
  (a₀ : A₀) (a₁ : A₁) [IsLocalization.Away a₀ W] [IsLocalization.Away a₁ W] (I : Ideal O)
  [Algebra (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))]
  [Algebra (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
    (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
    (W ⧸ I.map (algebraMap O W))]

/-- **The overlap datum for normalisations** (generic form): for `W = A₀[1/a₀] = A₁[1/a₁]` and
the normalisations `B₀`, `B₁` of `A₀`, `A₁` in a field `L`, the reductions modulo `J = I·O`
satisfy `(B₀/J)[1/ā₀] ≃ (B₁/J)[1/ā₁]` over `W/J` (both are `B_W/J` for the normalisation `B_W`
of `W` in `L`). -/
def omegaEquiv
    (hS₀ : ∀ x : A₀, algebraMap (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))
      (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₀ W x))
    (hS₁ : ∀ x : A₁, algebraMap (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))
      (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₁ W x))
    (ha₀ : algebraMap A₀ L a₀ ≠ 0) (ha₁ : algebraMap A₁ L a₁ ≠ 0) :
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀))
      (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
      (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
    Localization.Away (algebraMap (A₀ ⧸ I.map (algebraMap O A₀))
        (B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀)) (Ideal.Quotient.mk _ a₀)) ≃ₐ[
      W ⧸ I.map (algebraMap O W)]
      Localization.Away (algebraMap (A₁ ⧸ I.map (algebraMap O A₁))
        (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) (Ideal.Quotient.mk _ a₁)) := by
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
  exact (awayEquiv (B := B₀) a₀ I hS₀).trans ((quotEquiv _ (IsIntegralClosure.equiv (R := W)
    (B := L) (A := Localization.Away (algebraMap A₀ B₀ a₀))
    (Localization.Away (algebraMap A₁ B₁ a₁)))).trans (awayEquiv (B := B₁) a₁ I hS₁).symm)

end Main

end

end NormOverlap

namespace TateGlue0

open TateTwoChart TateLevel

noncomputable section

section Norm

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {π b₄ t κ : O}
  {L : Type*} [Field L] [Algebra (T0 π b₄ t κ) L] [Algebra (T1 π b₄ t κ) L]
  [Algebra (T01 π b₄ t κ) L] [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
  {B₀ B₁ : Type u} [CommRing B₀] [CommRing B₁]
  [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [IsScalarTower (T0 π b₄ t κ) B₀ L]
  [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
  [Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [IsScalarTower (T1 π b₄ t κ) B₁ L]
  [IsIntegralClosure B₁ (T1 π b₄ t κ) L]

variable (θ) in
/-- **The overlap datum `ω` for coverings given by normalisations**: for the normalisations `B₀`,
`B₁` of `T0`, `T1` in a field `L` (compatibly with `ρ₀ : T0 → T01`), the special fibres
`C0 = B₀/J`, `C1 = B₁/J` satisfy `C0[1/h̄] ≃ C1[1/h̄']` over `T01/J`. -/
def omegaNorm
    (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
    (h₀ : algebraMap (T0 π b₄ t κ) L (h0 π b₄ t κ) ≠ 0)
    (h₁ : algebraMap (T1 π b₄ t κ) L (h1 π b₄ t κ) ≠ 0) :
    letI := algC0x (FormalKummer.Cs θ (T0 π b₄ t κ) B₀) (θ := θ) (π := π) (b₄ := b₄) (t := t)
      (κ := κ)
    letI := algC1x (FormalKummer.Cs θ (T1 π b₄ t κ) B₁) (θ := θ) (π := π) (b₄ := b₄) (t := t)
      (κ := κ)
    Localization.Away (algebraMap (EtaleTower.Ts θ (T0 π b₄ t κ))
        (FormalKummer.Cs θ (T0 π b₄ t κ) B₀) (Ideal.Quotient.mk _ (h0 π b₄ t κ))) ≃ₐ[
      T01s θ π b₄ t κ]
      Localization.Away (algebraMap (EtaleTower.Ts θ (T1 π b₄ t κ))
        (FormalKummer.Cs θ (T1 π b₄ t κ) B₁) (Ideal.Quotient.mk _ (h1 π b₄ t κ))) := by
  letI := algT0T01 (π := π) (b₄ := b₄) (t := t) (κ := κ)
  haveI := towerT0T01 (π := π) (b₄ := b₄) (t := t) (κ := κ)
  haveI := isLocalization_rho0 π b₄ t κ
  haveI : IsScalarTower (T0 π b₄ t κ) (T01 π b₄ t κ) L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hρ x).symm
  letI := alg0s θ π b₄ t κ
  letI := alg1s θ π b₄ t κ
  haveI := isLocalization_alg0s θ π b₄ t κ
  haveI := isLocalization_alg1s θ π b₄ t κ
  exact NormOverlap.omegaEquiv (B₀ := B₀) (B₁ := B₁) (L := L) (h0 π b₄ t κ) (h1 π b₄ t κ)
    (RingHom.ker θ) (fun _ ↦ rfl) (fun _ ↦ rfl) h₀ h₁

end Norm

section OmegaC

open TateTwoChartNode KummerEtale AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀)
  {L : Type*} [Field L] [Algebra (T0 π b₄ t κ) L] [Algebra (T1 π b₄ t κ) L]
  [Algebra (T01 π b₄ t κ) L] [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
  {B₀ B₁ : Type u} [CommRing B₀] [CommRing B₁]
  [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [IsScalarTower (T0 π b₄ t κ) B₀ L]
  [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
  [Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [IsScalarTower (T1 π b₄ t κ) B₁ L]
  [IsIntegralClosure B₁ (T1 π b₄ t κ) L]

/-- **`omegaNorm` as an overlap datum `OmegaC`** for a covering `Sp` over `V₁` whose special
fibre `Sp.C1` is identified with `B₁/J` (`e`), and `C0 = B₀/J`. -/
def omegaNormC (e : Sp.C1 ≃ₐ[TateGlue1.T1s θ π b₄ t κ] FormalKummer.Cs θ (T1 π b₄ t κ) B₁)
    (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
    (h₀ : algebraMap (T0 π b₄ t κ) L (h0 π b₄ t κ) ≠ 0)
    (h₁ : algebraMap (T1 π b₄ t κ) L (h1 π b₄ t κ) ≠ 0) :
    OmegaC hκ hπ Sp (FormalKummer.Cs θ (T0 π b₄ t κ) B₀) :=
  letI := algC0x (FormalKummer.Cs θ (T0 π b₄ t κ) B₀) (θ := θ) (π := π) (b₄ := b₄) (t := t)
    (κ := κ)
  letI := algC1x (FormalKummer.Cs θ (T1 π b₄ t κ) B₁) (θ := θ) (π := π) (b₄ := b₄) (t := t)
    (κ := κ)
  letI := algC1x Sp.C1 (θ := θ) (π := π) (b₄ := b₄) (t := t) (κ := κ)
  letI := alg1s θ π b₄ t κ
  haveI := isLocalization_alg1s θ π b₄ t κ
  (omegaNorm θ hρ h₀ h₁).trans (NormOverlap.awayCongr (Ws := T01s θ π b₄ t κ)
    (Ideal.Quotient.mk _ (h1 π b₄ t κ)) e).symm

end OmegaC

end

end TateGlue0

end SemistableReduction
