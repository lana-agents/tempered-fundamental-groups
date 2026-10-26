/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateCuspEtaleChart
import TemperedFundamentalGroups.SemistableReduction.TateCuspPoints
import TemperedFundamentalGroups.SemistableReduction.TateSpecial1
import TemperedFundamentalGroups.SemistableReduction.TateEtaleCusp

/-!
# The special-fibre covering over the cusp chart from a tame cover (MR12 S5.6, `CuspSpecial`)

Let `O` be a discrete valuation ring of characteristic zero (uniformizer `ϖ`, `ker θ = (ϖ)`,
residue field `k` algebraically closed), `π = ε ϖᵐ` (`m ≥ 1`, `ε`, `b₆` units),
`Rc = T0[1/(1 + h)]` the cusp chart of the Tate model with fraction field `K`, `e ≥ 1` invertible
in `k` with `ζ_e ∈ K`, `L / K` finite Galois of degree dividing `e`, and `B` the normalisation of
`Rc` in `L`. Assume (`hunr`, debt D3 for the cusp chart) that `B` is unramified over `Rc` at every
prime `Q` lying over a prime `𝔮` strictly inside a maximal ideal `P ∋ ϖ`, except, when `z ∈ P`
(the cusp), for `𝔮 Rc_P = (h)`: ramification along the divisor `h = 0` at the cusp is allowed.

* **`TateCuspCov.covCusp`**: the admissible covering of the special fibre of `Rc` without nodes:
  `C = B/JB`, finite, étale over `D(h̄)` (purity, `hreg_Rc`), with one cusp factor for each point
  `𝔪` of `V(h̄)` (`FormalPoints.Pts`, finite by `isArtinianRing_cusp`) and each factor of its local
  formal cusp form: at the cusp (`z ∈ 𝔪`) by S3 for the étale chart `Rc[1/G₀'(z)]`
  (`TateCuspCov.isTameCuspKummerAt_cusp`), indices dividing `e`; at the other points (`z ∉ 𝔪`)
  by purity on `D(z̄)` (`pointCuspForm_of_etale_special`), indices `1`.
* **`TateCuspCov.cuspSpecial : CuspTower.CuspSpecial (T0 ..) (c0 ..) (h0 ..)`**: with
  `C0 = B₀/JB₀` (`B₀` the normalisation of `T0`, `B = B₀[1/(1 + h)]`) and `ι₀` the localization
  map (`NormAway`).
* **`TateCuspCov.cuspOverOrigin : TateGlue0.CuspOverOrigin cuspSpecial`**: the ramified cusp
  factors lie over `z = 0` (`z̄ = 0` in the completion at the cusp, since `z q₀ ∈ (π)` and `q₀` is
  a unit there).
-/

universe u

open Polynomial IsLocalRing Module TensorProduct

namespace SemistableReduction

namespace TateCuspCov

open TateTwoChart
open AdmissibleLift (J)
open FormalKummer (Cs Rs sIdeal PointCuspForm)

noncomputable section

/-! ### The points of the special fibre on `h̄ = 0` -/

section Points

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  [hθ : Fact (Function.Surjective θ)] (π b₄ t κ : O)

/-- The points of the special fibre of the cusp chart on `h̄ = 0`. -/
abbrev PtsC : Type u := FormalPoints.Pts (sbarC θ π b₄ t κ)

instance : Finite (PtsC θ π b₄ t κ) := by
  haveI := isArtinianRing_cusp θ π b₄ t κ hθ.out
  infer_instance

/-- The number of points on `h̄ = 0`. -/
abbrev nC : ℕ := Nat.card (PtsC θ π b₄ t κ)

/-- The `j`-th point. -/
def ptC (j : Fin (nC θ π b₄ t κ)) : PtsC θ π b₄ t κ := (Finite.equivFin _).symm j

/-- The maximal ideal of `Rc` of the `j`-th point. -/
def mC (j : Fin (nC θ π b₄ t κ)) : Ideal (RcT π b₄ t κ) :=
  (ptC θ π b₄ t κ j).ideal.comap (Ideal.Quotient.mk _)

instance (j : Fin (nC θ π b₄ t κ)) : (mC θ π b₄ t κ j).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

lemma J_le_mC (j : Fin (nC θ π b₄ t κ)) : J θ (R := RcT π b₄ t κ) ≤ mC θ π b₄ t κ j :=
  fun x hx ↦ by
    rw [mC, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact zero_mem _

lemma sIdeal_mC (j : Fin (nC θ π b₄ t κ)) :
    sIdeal (θ := θ) (mC θ π b₄ t κ j) = (ptC θ π b₄ t κ j).ideal :=
  Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _

lemma sC_mem_mC (j : Fin (nC θ π b₄ t κ)) :
    CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ) ∈ mC θ π b₄ t κ j :=
  Ideal.mem_comap.2 (ptC θ π b₄ t κ j).mem

lemma injective_mC : Function.Injective fun j ↦ sIdeal (θ := θ) (mC θ π b₄ t κ j) :=
  fun a b h ↦ (Finite.equivFin _).symm.injective (FormalPoints.ideal_injective _ (by
    simpa only [sIdeal_mC, ptC] using h))

lemma sbar_mem_mC (j : Fin (nC θ π b₄ t κ)) :
    sbarC θ π b₄ t κ ∈ sIdeal (θ := θ) (mC θ π b₄ t κ j) := by
  rw [sIdeal_mC]
  exact (ptC θ π b₄ t κ j).mem

lemma iInf_mC_le [IsNoetherianRing O] :
    ⨅ j, sIdeal (θ := θ) (mC θ π b₄ t κ j) ≤ (Ideal.span {sbarC θ π b₄ t κ}).radical := by
  haveI : Algebra.FiniteType O (T0 π b₄ t κ) :=
    Algebra.FiniteType.trans (S := O[X]) inferInstance inferInstance
  haveI : Algebra.FinitePresentation (T0 π b₄ t κ) (RcT π b₄ t κ) :=
    IsLocalization.Away.finitePresentation (TateGlue0.c0 π b₄ t κ)
  haveI : Algebra.FiniteType O (RcT π b₄ t κ) :=
    Algebra.FiniteType.trans (S := T0 π b₄ t κ) inferInstance inferInstance
  haveI := TateGlue1.isJacobsonRing_quot (θ := θ) (RcT π b₄ t κ)
  simp only [sIdeal_mC]
  rw [show (⨅ j, (ptC θ π b₄ t κ j).ideal) = ⨅ P : PtsC θ π b₄ t κ, P.ideal from
    (Finite.equivFin _).symm.iInf_comp (g := fun P : PtsC θ π b₄ t κ ↦ P.ideal)]
  exact FormalPoints.iInf_le_radical _

/-- The bound on the ramification indices at a point: `e` at the cusp (`z ∈ 𝔪`), `1` elsewhere. -/
def eP (e : ℕ) (𝔪 : Ideal (RcT π b₄ t κ)) : ℕ := by
  classical exact if algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ 𝔪 then e else 1

variable {π b₄ t κ}

lemma eP_of_mem {e : ℕ} {𝔪 : Ideal (RcT π b₄ t κ)}
    (h : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ 𝔪) : eP π b₄ t κ e 𝔪 = e := by
  rw [eP, if_pos h]

lemma eP_of_notMem {e : ℕ} {𝔪 : Ideal (RcT π b₄ t κ)}
    (h : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∉ 𝔪) : eP π b₄ t κ e 𝔪 = 1 := by
  rw [eP, if_neg h]

lemma eP_dvd (e : ℕ) (𝔪 : Ideal (RcT π b₄ t κ)) : eP π b₄ t κ e 𝔪 ∣ e := by
  by_cases h : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ 𝔪
  · rw [eP_of_mem h]
  · rw [eP_of_notMem h]
    exact one_dvd e

end Points

/-! ### The covering -/

/-- A prime contained in `P` does not localize to `(s)` if `s ∉ P`. -/
lemma map_ne_span {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {q : Ideal R} (hq : q ≤ P)
    {s : R} (hs : s ∉ P) :
    q.map (algebraMap R (Localization.AtPrime P)) ≠
      Ideal.span {algebraMap R (Localization.AtPrime P) s} := by
  intro h
  have h1 : algebraMap R (Localization.AtPrime P) s ∈ maximalIdeal (Localization.AtPrime P) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)]
    exact Ideal.map_mono hq (h ▸ Ideal.mem_span_singleton_self _)
  exact hs ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ P s).1 h1)

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  [IsAlgClosed k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ π b₄ b₆ t κ ε : O} {m : ℕ}
  (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
  (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
  (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
  [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
  (K : Type u) [Field K] [Algebra (RcT π b₄ t κ) K] [IsFractionRing (RcT π b₄ t κ) K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ e)
  (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (hd : finrank K L ∣ e) [Algebra (RcT π b₄ t κ) L] [IsScalarTower (RcT π b₄ t κ) K L]
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

omit [CharZero O] in
include hϖ hπ hε hκ h3 hE in
lemma isDomain_Rc' : IsDomain (RcT π b₄ t κ) :=
  isDomain_Rc hϖ hκ h3 (by rw [hπ]; exact mul_ne_zero hε.ne_zero (pow_ne_zero _ hϖ.ne_zero)) hE

omit [IsAlgClosed k] [CharZero O] in
include hϖ hker hπ hm hε hκ h3 hE hb₆ in
lemma isIntegrallyClosed_Rc' : IsIntegrallyClosed (RcT π b₄ t κ) :=
  isIntegrallyClosed_Rc hϖ hθ.out hker hπ hm hε h3 hE hκ hb₆

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] hθ [CharZero O] in
include hker in
lemma ϖ_mem_J : algebraMap O (RcT π b₄ t κ) ϖ ∈ J θ (R := RcT π b₄ t κ) :=
  Ideal.mem_map_of_mem _ (by rw [hker]; exact Ideal.mem_span_singleton_self ϖ)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] hθ [CharZero O] in
lemma finiteType_Rc : Algebra.FiniteType O (RcT π b₄ t κ) := by
  haveI : Algebra.FiniteType O (T0 π b₄ t κ) :=
    Algebra.FiniteType.trans (S := O[X]) inferInstance inferInstance
  haveI : Algebra.FinitePresentation (T0 π b₄ t κ) (RcT π b₄ t κ) :=
    IsLocalization.Away.finitePresentation (TateGlue0.c0 π b₄ t κ)
  exact Algebra.FiniteType.trans (S := T0 π b₄ t κ) inferInstance inferInstance

omit [IsAlgClosed k] [CharZero O] [NeZero e] in
include hϖ hker hπ hm hε hκ h3 hE hb₆ K L in
/-- `C = B/JB` is finite over the special fibre of `Rc`. -/
theorem finite_Cs : Module.Finite (Rs θ (RcT π b₄ t κ)) (Cs θ (RcT π b₄ t κ) B) := by
  haveI := isDomain_Rc' hϖ hπ hε h3 hE hκ
  haveI := isIntegrallyClosed_Rc' hϖ hker hπ hm hε h3 hE hκ hb₆
  haveI : Module.Finite (RcT π b₄ t κ) B := IsIntegralClosure.finite (RcT π b₄ t κ) K L B
  haveI : Module.Finite (RcT π b₄ t κ) (Cs θ (RcT π b₄ t κ) B) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (RcT π b₄ t κ) _).toLinearMap
      Ideal.Quotient.mk_surjective
  exact Module.Finite.of_restrictScalars_finite (RcT π b₄ t κ) (Rs θ (RcT π b₄ t κ))
    (Cs θ (RcT π b₄ t κ) B)

omit [IsAlgClosed k] [CharZero O] [NeZero e] in
include hϖ hker hπ hm hε hκ h3 hE hb₆ K L hunr in
/-- **Purity**: `C = B/JB` is étale over the special fibre of `Rc` on `D(ḡ)` for any `g` with
`g ∉ P` whenever `z ∈ P` and `s ∈ P`. -/
theorem etale_away (g : RcT π b₄ t κ)
    (hg : ∀ (P : Ideal (RcT π b₄ t κ)) [P.IsMaximal], g ∉ P →
      algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ P →
        CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ) ∉ P) :
    (Localization.awayMap (algebraMap (Rs θ (RcT π b₄ t κ)) (Cs θ (RcT π b₄ t κ) B))
      (Ideal.Quotient.mk _ g)).Etale := by
  haveI := isDomain_Rc' hϖ hπ hε h3 hE hκ
  haveI := isIntegrallyClosed_Rc' hϖ hker hπ hm hε h3 hE hκ hb₆
  haveI := finiteType_Rc (O := O) (π := π) (b₄ := b₄) (t := t) (κ := κ)
  haveI := TateGlue1.isJacobsonRing_quot (θ := θ) (RcT π b₄ t κ)
  have hϖJ := ϖ_mem_J (π := π) (b₄ := b₄) (t := t) (κ := κ) hker
  exact PurityLocal.etale_quot_awayMap K (L := L) (J θ (R := RcT π b₄ t κ)) B g
    (fun P _ hJP _ ↦ hreg_Rc hϖ hθ.out hker hπ hm hε h3 hE hκ hb₆ P (hJP hϖJ))
    (fun P _ hJP hgP Q _ hQ ↦ hunr P (hJP hϖJ) Q hQ fun hz ↦
      map_ne_span P hQ.le (hg P hgP hz))

omit [IsAlgClosed k] [CharZero O] [NeZero e] in
include hϖ hker hπ hm hε hκ h3 hE hb₆ K L hunr in
/-- **`C` is étale over `D(s̄)`** (the `etale` field of the covering). -/
theorem etale_s : (Localization.awayMap (algebraMap (Rs θ (RcT π b₄ t κ))
    (Cs θ (RcT π b₄ t κ) B)) (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ)))).Etale :=
  etale_away hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr _ fun _ _ hs _ ↦ hs

include hϖ hker hπ hm hε hκ h3 hE hb₆ hζ hd hunr in
/-- **The local formal cusp form at a point of `h̄ = 0`**, with indices dividing `eP e 𝔪`. -/
theorem pointCuspForm (𝔪 : Ideal (RcT π b₄ t κ)) [𝔪.IsMaximal]
    (hJ : J θ (R := RcT π b₄ t κ) ≤ 𝔪)
    (hs : CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ) ∈ 𝔪) :
    PointCuspForm (θ := θ) (B := B)
      (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ)) (eP π b₄ t κ e 𝔪) 𝔪 := by
  haveI := isDomain_Rc' hϖ hπ hε h3 hE hκ
  haveI := isIntegrallyClosed_Rc' hϖ hker hπ hm hε h3 hE hκ hb₆
  haveI := finiteType_Rc (O := O) (π := π) (b₄ := b₄) (t := t) (κ := κ)
  have hϖ𝔪 := hJ (ϖ_mem_J (π := π) (b₄ := b₄) (t := t) (κ := κ) hker)
  have hres := FormalKummer.surjective_mk_comp_of_isAlgClosed (θ := θ) 𝔪 hJ
  by_cases hz : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ 𝔪
  · rw [eP_of_mem hz]
    have hinj : Function.Injective (algebraMap (RcT π b₄ t κ) L) := by
      rw [IsScalarTower.algebraMap_eq (RcT π b₄ t κ) K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective (RcT π b₄ t κ) K)
    letI := NormLocal.algAtPrime 𝔪 hinj
    haveI := NormLocal.isScalarTower_algAtPrime 𝔪 hinj
    set p : Ideal (RcT π b₄ t κ) → Prop := fun q ↦
      q.map (algebraMap (RcT π b₄ t κ) (Localization.AtPrime 𝔪)) ≠
        Ideal.span {algebraMap (RcT π b₄ t κ) (Localization.AtPrime 𝔪)
          (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))}
    have hunr' : ∀ (Q : Ideal (integralClosure (RcT π b₄ t κ) L)) [Q.IsPrime],
        Q.comap (algebraMap (RcT π b₄ t κ) (integralClosure (RcT π b₄ t κ) L)) < 𝔪 →
          p (Q.comap (algebraMap (RcT π b₄ t κ) (integralClosure (RcT π b₄ t κ) L))) →
            Algebra.IsUnramifiedAt (RcT π b₄ t κ) Q := fun Q _ hQ hp ↦
      PurityLocal.isUnramifiedAt_integralClosure_of_pred B p
        (fun Q' _ hQ' hp' ↦ hunr 𝔪 hϖ𝔪 Q' hQ' fun _ ↦ hp') Q hQ hp
    have h := isTameCuspKummerAt_cusp hϖ hκ 𝔪 hϖ𝔪 hs hz K hζ L hd
      (integralClosure (Localization.AtPrime 𝔪) L) fun Q _ h1 h2 ↦
        NormLocal.isUnramifiedAt_of_pred hinj p hunr' Q h1 (by
          change (Ideal.comap _ _).map _ ≠ _
          rwa [show ((Q.comap (algebraMap (Localization.AtPrime 𝔪)
              (integralClosure (Localization.AtPrime 𝔪) L))).comap
                (algebraMap (RcT π b₄ t κ) (Localization.AtPrime 𝔪))).map
              (algebraMap (RcT π b₄ t κ) (Localization.AtPrime 𝔪)) =
            Q.comap (algebraMap (Localization.AtPrime 𝔪)
              (integralClosure (Localization.AtPrime 𝔪) L)) from
            IsLocalization.map_under 𝔪.primeCompl _ _])
    exact FormalKummer.pointCuspForm_of_isCuspNormAt 𝔪 hJ hres (h.isCuspNormAt (B := B))
  · rw [eP_of_notMem hz]
    haveI := finite_Cs hϖ hker hπ hm hε h3 hE hκ hb₆ K L B
    exact FormalKummer.pointCuspForm_of_etale_special 𝔪 hJ hres hz
      (etale_away hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr _ fun _ _ hzP hz ↦ absurd hz hzP) _

include hϖ hker hπ hm hε hκ h3 hE hb₆ hζ hd hunr in
/-- **The cusp part of the formal Kummer form** of `C` over the special fibre of `Rc`. -/
theorem exists_cusp :
    haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j)
    ∃ (r : Fin (nC θ π b₄ t κ) → ℕ) (d : ∀ j, Fin (r j) → ℕ), (∀ j i, 0 < d j i) ∧
      (∀ j i, d j i ∣ eP π b₄ t κ e (mC θ π b₄ t κ j)) ∧
      Nonempty (Admissible.Hat (sbarC θ π b₄ t κ) ⊗[Rs θ (RcT π b₄ t κ)]
          Cs θ (RcT π b₄ t κ) B ≃ₐ[Admissible.Hat (sbarC θ π b₄ t κ)]
        ∀ p : (Σ j, Fin (r j)), Admissible.CuspPiece
          (CuspTower.ψb (θ := θ) (RcT π b₄ t κ)
            (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))
            (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ)))
          (CompletionProd.idem (injective_mC θ π b₄ t κ) (sbar_mem_mC θ π b₄ t κ)
            (iInf_mC_le θ π b₄ t κ) p.1) (d p.1 p.2)) :=
  FormalKummer.exists_cusp' (mC θ π b₄ t κ) (J_le_mC θ π b₄ t κ)
    (fun j ↦ pointCuspForm hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr _ (J_le_mC θ π b₄ t κ j)
      (sC_mem_mC θ π b₄ t κ j)) _ _ _ _ (Polynomial.aeval_X _)

/-- **The admissible covering of the special fibre of the cusp chart** (no nodes) defined by the
special fibre `C = B/JB` of the normalisation `B` of `Rc` in a tame Galois cover `L`; `φ₀` is
arbitrary (there are no node factors). -/
def covCusp (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ)))) :
    Admissible.Covering φ₀ (CuspTower.ψb (θ := θ) (RcT π b₄ t κ)
      (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))
      (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))) :=
  haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j)
  let H := exists_cusp hϖ hker hπ hm hε h3 hE hκ hb₆ (e := e) K hζ L hd B hunr
  { C := Cs θ (RcT π b₄ t κ) B
    finite := finite_Cs hϖ hker hπ hm hε h3 hE hκ hb₆ K L B
    etale := etale_s hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr
    ι := Empty
    idem := Empty.elim
    isIdempotentElem_idem := fun j ↦ j.elim
    e := Empty.elim
    e_pos := fun j ↦ j.elim
    e_ne_zero := fun j ↦ j.elim
    κ := Σ j, Fin (H.choose j)
    cidem := fun p ↦ CompletionProd.idem _ _ _ p.1
    isIdempotentElem_cidem := fun p ↦ CompletionProd.isIdempotentElem_idem _ _ _ p.1
    ce := fun p ↦ H.choose_spec.choose p.1 p.2
    ce_pos := fun p ↦ H.choose_spec.choose_spec.1 p.1 p.2
    ce_ne_zero := fun p h0 ↦ by
      obtain ⟨c, hc⟩ := (H.choose_spec.choose_spec.2.1 p.1 p.2).trans (eP_dvd e _)
      exact he (by rw [hc, Nat.cast_mul, h0, zero_mul])
    kummer := H.choose_spec.choose_spec.2.2.some.trans AlgEquiv.uniqueProd.symm }

end

end TateCuspCov

end SemistableReduction
