/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Datum

/-!
# The residue facts of a Tate cover over a separably closed residue field

The Tate S5/S6 chain takes the residue facts `TateS6.CovRational θ M' C` of a cover `C`
(`TateTwoChartNode.NodeNbhdRational` at the nodes, `TateCuspCov.CuspNbhdRational` on the cusp
chart; debt R1 over a general residue field). Over a **separably closed** residue field `k` they
hold for every cover:

* `EtaleResidue.surjective_of_awayMap_etale`: if `A_f → C_f` is étale, `I₀ ⊆ A` is maximal with
  `f ∉ I₀` and `A/I₀` is a quotient of a separably closed field, then every prime of `C` over
  `I₀` has residue field `A/I₀`.
* `TateCuspCov.cuspNbhdRational_of_isSepClosed`: `CuspNbhdRational` for the normalisation `B` of
  the cusp chart in a tame cover, from the hypothesis `hunr` of `TateCuspCov.covCusp` (the cusp
  point by `FormalKummer.isCuspNormAtRes_of_isSepClosed`, the other points of `h̄ = 0` by purity,
  `etale_away`, and `surjective_of_awayMap_etale`).
* **`TateS6.covRational_of_isSepClosed`**: `CovRational θ M' C` for every Tate cover `C`
  (`hunr` of the cusp chart from the field `C.hunr₀`, `TateS5.hunr_Bc`).
-/

universe u

open Module Polynomial

namespace SemistableReduction

namespace EtaleResidue

/-- **Residue fields over a point where a localization is étale**: if `A_f → C_f` is étale,
`I₀ ⊆ A` is maximal with `f ∉ I₀`, and `A/I₀` is a quotient of a separably closed field `k`,
then `A → C/P` is surjective for every prime `P` of `C` over `I₀`. -/
theorem surjective_of_awayMap_etale {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    {f : A} (het : (Localization.awayMap (algebraMap A C) f).Etale) (I₀ : Ideal A)
    [I₀.IsMaximal] (hf : f ∉ I₀) {k : Type*} [Field k] [IsSepClosed k] (ρ : k →+* A ⧸ I₀)
    (hρ : Function.Surjective ρ) (P : Ideal C) [P.IsPrime]
    (hP : P.comap (algebraMap A C) = I₀) :
    Function.Surjective ((Ideal.Quotient.mk P).comp (algebraMap A C)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) := het
  have htow : ∀ a : A, algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f))
      (algebraMap A (Localization.Away f) a) =
        algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C a) := fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra]
    unfold Localization.awayMap IsLocalization.Away.map
    rw [IsLocalization.map_eq]
  have hfP : algebraMap A C f ∉ P := fun h ↦ hf (hP ▸ h)
  have hdisj : Disjoint ((Submonoid.powers (algebraMap A C f) : Submonoid C) : Set C) P :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).2 hfP
  set 𝔫 := P.map (algebraMap C (Localization.Away (algebraMap A C f))) with h𝔫def
  haveI h𝔫p : 𝔫.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ P ‹_› hdisj
  have h𝔫 : 𝔫.comap (algebraMap C (Localization.Away (algebraMap A C f))) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hdisj
  set 𝔪' := 𝔫.comap (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)))
  have h𝔪' : 𝔪'.comap (algebraMap A (Localization.Away f)) = I₀ := by
    rw [Ideal.comap_comap, show (algebraMap (Localization.Away f)
        (Localization.Away (algebraMap A C f))).comp (algebraMap A (Localization.Away f)) =
        (algebraMap C (Localization.Away (algebraMap A C f))).comp (algebraMap A C) from
      RingHom.ext htow, ← Ideal.comap_comap, h𝔫, hP]
  haveI : (𝔪'.under A).IsMaximal := by
    rw [Ideal.under, h𝔪']
    infer_instance
  haveI : 𝔪'.IsMaximal := Ideal.IsMaximal.of_isLocalization_of_disjoint (Submonoid.powers f)
  have hq := IsLocalization.surjective_quotientMap_of_maximal_of_localization
    (Submonoid.powers f) (Localization.Away f) (I := 𝔪') (J := I₀) (H := h𝔪'.ge)
    (by rw [Ideal.under, h𝔪']; infer_instance)
  have hs := surjective_of_isSepClosed' 𝔪' 𝔫 rfl
    ((Ideal.quotientMap 𝔪' (algebraMap A (Localization.Away f)) h𝔪'.ge).comp ρ) (hq.comp hρ)
  intro c
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨x, hx⟩ := hs (Ideal.Quotient.mk 𝔫 (algebraMap C _ c))
  obtain ⟨a', ha'⟩ := hq (Ideal.Quotient.mk 𝔪' x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  refine ⟨a, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at ha'
  rw [RingHom.comp_apply, Ideal.Quotient.eq] at hx
  rw [RingHom.comp_apply, Ideal.Quotient.eq, ← h𝔫, Ideal.mem_comap]
  have h := 𝔫.add_mem (Ideal.mem_comap.1 ha') hx
  rw [map_sub, htow, sub_add_sub_cancel] at h
  rwa [map_sub]

end EtaleResidue

namespace TateCuspCov

open TateTwoChart TateGlue0 AdmissibleLift FormalKummer

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ π b₄ b₆ t κ ε : O} {m : ℕ} [hsq : Fact (IsSquare (θ b₆))]
  (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
  (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
  (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
  (K : Type u) [Field K] [Algebra (RcT π b₄ t κ) K] [IsFractionRing (RcT π b₄ t κ) K]
  (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Algebra (RcT π b₄ t κ) L] [IsScalarTower (RcT π b₄ t κ) K L]
  (B : Type u) [CommRing B] [Algebra (RcT π b₄ t κ) B] [Algebra B L]
  [IsScalarTower (RcT π b₄ t κ) B L] [IsIntegralClosure B (RcT π b₄ t κ) L]
  (hunr : ∀ (P : Ideal (RcT π b₄ t κ)) [P.IsMaximal], algebraMap O (RcT π b₄ t κ) ϖ ∈ P →
    ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap (RcT π b₄ t κ) B) < P →
      (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ P →
        (Q.comap (algebraMap (RcT π b₄ t κ) B)).map
            (algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)
            (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))}) →
      Algebra.IsUnramifiedAt (RcT π b₄ t κ) Q)

omit [IsDomain O] [IsDiscreteValuationRing O] hsq in
/-- At a `k`-rational point `𝔪 ⊇ J`, the residue field of `sIdeal 𝔪` is reached from `k`. -/
lemma surjective_mk_sIdeal_comp {R : Type u} [CommRing R] [Algebra O R] {𝔪 : Ideal R}
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R))) :
    Function.Surjective ((Ideal.Quotient.mk (sIdeal (θ := θ) 𝔪)).comp
      (algebraMap k (Rs θ R))) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨o, ho⟩ := hres (Ideal.Quotient.mk 𝔪 a)
  refine ⟨θ o, ?_⟩
  rw [RingHom.comp_apply, QuadNodeTower.algK_θ, Ideal.Quotient.eq, ← map_sub]
  exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.mp ho)

include hϖ hker hπ hm hε hκ h3 hE hb₆ K L hunr in
/-- **`CuspNbhdRational` over a separably closed residue field**, for the normalisation `B` of the
cusp chart in a tame cover (hypothesis `hunr` of `covCusp`): at the cusp by
`isCuspNormAtRes_of_isSepClosed`, at the other points of `h̄ = 0` since `C = B/JB` is étale
there (`etale_away`, `EtaleResidue.surjective_of_awayMap_etale`). -/
theorem cuspNbhdRational_of_isSepClosed [IsSepClosed k] (e : ℕ) :
    CuspNbhdRational θ π b₄ t κ e B := by
  intro 𝔪 _ hJ hs
  have hres := surjective_mk_comp_cuspPt hker hπ hm hκ 𝔪 hJ hs
  refine ⟨fun _ h ↦ isCuspNormAtRes_of_isSepClosed hJ hres h, fun hz P hP hPc ↦ ?_⟩
  haveI := isMaximal_sIdeal (θ := θ) 𝔪 hJ
  exact EtaleResidue.surjective_of_awayMap_etale
    (etale_away hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr _ fun _ _ hzP hz ↦ absurd hz hzP)
    (sIdeal (θ := θ) 𝔪) (by rwa [Ideal.mem_quotient_iff_mem hJ])
    _ (surjective_mk_sIdeal_comp hres) P hPc

end TateCuspCov

namespace TateS6

open TateTwoChart TateTwoChartNode TateGlue0

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m] [hsq : Fact (IsSquare (θ b₆))]
  {hκ : κ * (t ^ 2 - b₆) = 1} {q e : ℕ}
  {K : Type u} [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (RcT (ε * ϖ ^ m) b₄ t κ) K]

/-- **The residue facts of a Tate cover over a separably closed residue field** (S5.7 (b);
`k^sep` wrapper for the consumers): `CovRational θ M' C` holds for every tame cover `C`. -/
theorem covRational_of_isSepClosed [IsSepClosed k] (hϖ : Irreducible ϖ)
    (hker : RingHom.ker θ = Ideal.span {ϖ}) (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) (hb₆ : IsUnit b₆)
    (M' : ℕ) (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) : CovRational θ M' C := by
  letI : Algebra (T0 (ε * ϖ ^ m) b₄ t κ) C.L := C.algT0
  haveI : IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) C.L := C.towT0
  letI : Algebra (T0 (ε * ϖ ^ m) b₄ t κ) C.B₀ := C.algB₀
  haveI : IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) C.B₀ C.L := C.towB₀
  haveI : IsIntegralClosure C.B₀ (T0 (ε * ϖ ^ m) b₄ t κ) C.L := C.intB₀
  haveI : IsLocalization.Away (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) C.B₀
    (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ)) C.Bc := C.locBc
  haveI := TateCuspCov.isIntegralClosure_B (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
    C.L C.Bc C.B₀
  exact ⟨nodeNbhdRational_of_isSepClosed M' C.Bn,
    TateCuspCov.cuspNbhdRational_of_isSepClosed hϖ hker rfl (Nat.one_le_iff_ne_zero.2
      (NeZero.ne m)) (.of_mul_eq_one_right εi hε) h3 hE hκ hb₆ K C.L C.Bc
      (fun P _ hϖP Q _ hQ hz ↦ TateS5.hunr_Bc hκ C.hBc C.hunr₀ P hϖP Q hQ hz) e⟩

end TateS6

end SemistableReduction
