/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspPointDVR
import TemperedFundamentalGroups.SemistableReduction.StabilizerCyclic
import TemperedFundamentalGroups.SemistableReduction.StabIdeal
import TemperedFundamentalGroups.SemistableReduction.EtaleLocalDomain
import TemperedFundamentalGroups.SemistableReduction.P1ThreeCuspNF
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialChart
import TemperedFundamentalGroups.SemistableReduction.P1ThreeHomDatum

/-!
# The special cusp stabilisers of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` are cyclic (MR13 C2)

For a datum `D` (`P1Three.Datum`) of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` (`k` algebraically
closed, `ā ≠ 0, 1`) with a finite group `G` acting on it (`act : G → D.Hom D`), faithfully on the
covering `C1` of `V₁`, `C1` connected, and `|G|` invertible in `k`:

* **`EtaleConnectedDomain.isDomain_of_connected`** (generic): a connected étale algebra over an
  integrally closed domain is a domain (the integral closure commutes with smooth base change, so
  the idempotents of the generic fibre come from `C`; the generic fibre is artinian and reduced);
* `P1Three.bijective_ι₀`, `P1Three.isSMulRegular_C0`: the covering `C0` of the cusp chart `V₀` is
  its admissible covering `cov.C` (`c₀ = 1`), and `x̄ = t (t − 1)(t − ā)` is a nonzerodivisor on it
  (`Admissible.Covering.isSMulRegular_f`);
* **`P1Three.isDiscreteValuationRing_C0`**: at a prime `𝔪 ∋ x̄` of `C0` (a point over a cusp) the
  local ring `C0_𝔪` is a discrete valuation ring
  (`Admissible.Covering.isDiscreteValuationRing_atPrime`;
  `x̄` is a uniformizer of `k[t]` at the cusps since `T (T − 1)(T − ā)` is squarefree);
* `P1Three.Datum.isDomain_C1`, **`P1Three.Datum.isDomain_C0`** (`C0 ↪ C0[1/x̄] ≅ C1[1/ȳ]`),
  **`P1Three.Datum.eq_one_of_φ0`** (faithfulness on `C0` from faithfulness on `C1` via `ω`),
  `P1Three.Datum.exists_residue` (the residue fields at maximal ideals are `k`);
* **`P1Three.Datum.isCyclic_stab`**: the stabiliser in `G` of a maximal ideal `𝔪 ∋ x̄` of `C0` (a
  special point over a cusp) is cyclic (MR12's `StabilizerCyclic.isCyclic_of_faithful`, I5(c)).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

/-! ### Connected étale algebras over normal domains are domains -/

namespace EtaleConnectedDomain

variable {A C : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing C]
  [Algebra A C] [Algebra.Etale A C]

local notation "K" => FractionRing A

omit [IsDomain A] in
/-- Elements of `C ⊗_A K` integral over `C` come from `C`. -/
theorem exists_eq_tmul_one_of_isIntegral {e : C ⊗[A] K} (he : IsIntegral C e) :
    ∃ d : C, d ⊗ₜ[A] (1 : K) = e := by
  have H : Function.Bijective (TensorProduct.toIntegralClosure A C K) :=
    TensorProduct.toIntegralClosure_bijective_of_smooth
  obtain ⟨t, ht⟩ := H.2 ⟨e, he⟩
  have ht' : (Algebra.TensorProduct.map (AlgHom.id C C) (integralClosure A K).val) t = e :=
    congrArg Subtype.val ht
  rw [← ht']
  clear ht ht' H
  induction t with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add]⟩
  | tmul d k =>
    have hk : (k : K) ∈ (⊥ : Subalgebra A K) := by
      rw [← IsIntegrallyClosed.integralClosure_eq_bot A K]
      exact k.2
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hk
    refine ⟨r • d, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr]
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

include A in
/-- **A connected étale algebra over an integrally closed domain is a domain.** -/
theorem isDomain_of_connected [Nontrivial C]
    (hconn : ∀ e : C, IsIdempotentElem e → e = 0 ∨ e = 1) : IsDomain C := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] K) :=
    Algebra.TensorProduct.includeLeft_injective (S := A) (IsFractionRing.injective A K)
  have hidem : ∀ e : C ⊗[A] K, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    have hint : IsIntegral C e := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub (by simp)
      · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, sq, Polynomial.eval₂_mul]
        rw [he.eq, sub_self]
    obtain ⟨d, rfl⟩ := exists_eq_tmul_one_of_isIntegral hint
    have hd : IsIdempotentElem d := by
      apply hinj
      change (d * d) ⊗ₜ[A] (1 : K) = d ⊗ₜ[A] (1 : K)
      rw [← he.eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rcases hconn d hd with h | h
    · left; rw [h, TensorProduct.zero_tmul]
    · right; rw [h]; rfl
  let φ : C ⊗[A] K ≃ₐ[A] K ⊗[A] C := Algebra.TensorProduct.comm A C K
  have hidem' : ∀ e : K ⊗[A] C, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    rcases hidem (φ.symm e) (he.map φ.symm) with h | h
    · left; simpa using congrArg φ h
    · right; simpa using congrArg φ h
  haveI : IsReduced (K ⊗[A] C) := Algebra.FormallyUnramified.isReduced_of_field K _
  haveI : Module.Finite K (K ⊗[A] C) := by
    haveI : Module.Free K (K ⊗[A] C) := Module.Free.of_divisionRing K _
    exact Algebra.FormallyUnramified.finite_of_free K _
  haveI : IsArtinianRing (K ⊗[A] C) := IsArtinianRing.of_finite K _
  haveI : Nontrivial (K ⊗[A] C) := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have := congrArg φ.symm h
    rw [map_zero, map_one] at this
    exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact this))
  have hfield : IsField (C ⊗[A] K) :=
    MulEquiv.isField (isField_of_isArtinianRing_of_isReduced hidem') φ.toRingEquiv.toMulEquiv
  letI := hfield.toField
  exact hinj.isDomain _

/-- The same for an algebra which is étale over `D(x)` for a unit `x` (the form of
`CuspChart.Special.etale`). -/
theorem isDomain_of_etale_away {A C : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing C] [Algebra A C] [Nontrivial C] (x : A) (hx : IsUnit x)
    (h : (Localization.awayMap (algebraMap A C) x).Etale)
    (hconn : ∀ e : C, IsIdempotentElem e → e = 0 ∨ e = 1) : IsDomain C := by
  letI := (Localization.awayMap (algebraMap A C) x).toAlgebra
  haveI : Algebra.Etale (Localization.Away x) (Localization.Away (algebraMap A C x)) := h
  let eA := IsLocalization.atUnit A (Localization.Away x) x hx
  let eC := IsLocalization.atUnit C (Localization.Away (algebraMap A C x)) (algebraMap A C x)
    (hx.map _)
  haveI : IsDomain (Localization.Away x) :=
    eA.toRingEquiv.symm.injective.isDomain eA.toRingEquiv.symm.toRingHom
  haveI : IsIntegrallyClosed (Localization.Away x) := IsIntegrallyClosed.of_equiv eA.toRingEquiv
  haveI : Nontrivial (Localization.Away (algebraMap A C x)) := eC.toRingEquiv.symm.nontrivial
  have hconn' : ∀ e : Localization.Away (algebraMap A C x), IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    rcases hconn (eC.symm e) (he.map eC.symm) with h | h
    · left; simpa using congrArg eC h
    · right; simpa using congrArg eC h
  haveI := isDomain_of_connected (A := Localization.Away x) hconn'
  exact eC.toRingEquiv.injective.isDomain eC.toRingEquiv.toRingHom

end EtaleConnectedDomain

/-! ### Uniformizers in a principal ideal domain -/

/-- In a principal ideal domain, a squarefree `f` is a uniformizer at every prime containing it. -/
theorem exists_uniformizer_of_squarefree {P : Type*} [CommRing P] [IsDomain P]
    [IsPrincipalIdealRing P] {f : P} (hf : Squarefree f) (𝔭 : Ideal P) [𝔭.IsPrime] (h : f ∈ 𝔭) :
    ∃ g ∉ 𝔭, ∀ r ∈ 𝔭, ∃ s, g * r = f * s := by
  obtain ⟨p, hp⟩ := (inferInstance : 𝔭.IsPrincipal)
  have hp' : 𝔭 = Ideal.span {p} := by rw [hp]
  rw [hp', Ideal.mem_span_singleton] at h
  obtain ⟨g, rfl⟩ := h
  refine ⟨g, fun hg ↦ ?_, fun r hr ↦ ?_⟩
  · rw [hp', Ideal.mem_span_singleton] at hg
    obtain ⟨c, rfl⟩ := hg
    have hu := hf p ⟨c, by ring⟩
    exact (Ideal.IsPrime.ne_top ‹_›) (by rw [hp', Ideal.span_singleton_eq_top]; exact hu)
  · rw [hp', Ideal.mem_span_singleton] at hr
    obtain ⟨s, rfl⟩ := hr
    exact ⟨s, by ring⟩

namespace P1Three

open TateLevel AdmissibleLift CuspTower EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {a : O} [IsNoetherianRing O]

/-! ### The cusp chart -/

section Cusp

variable (a θ) in
/-- `R0/J ≃ (R0[1/1])/J` (`φsC`). -/
def eR : Ts θ (R0 O a) ≃+* Ts θ (Rc (R0 O a) 1) :=
  letI := (φsC (R0 O a) 1 θ).toAlgebra
  haveI : IsLocalization.Away (Ideal.Quotient.mk (J θ (R := R0 O a)) 1)
      (Ts θ (Rc (R0 O a) 1)) := isLocalization_φsC
  (IsLocalization.atUnits (Ts θ (R0 O a)) (Submonoid.powers (Ideal.Quotient.mk (J θ) 1))
    (S := Ts θ (Rc (R0 O a) 1)) (by
      rintro _ ⟨m, rfl⟩
      simp)).toRingEquiv

omit hθ [IsNoetherianRing O] in
lemma eR_apply (x : Ts θ (R0 O a)) : eR (a := a) (θ := θ) x = φsC (R0 O a) 1 θ x := rfl

omit hθ [IsNoetherianRing O] in
lemma eR_x0 :
    eR (a := a) (θ := θ) (Ideal.Quotient.mk _ (x0 O a)) = fbar θ (sC (R0 O a) 1 (x0 O a)) := by
  rw [eR_apply, φsC, Ideal.quotientMap_mk]

omit [IsNoetherianRing O] in
lemma isSMulRegular_fbar :
    IsSMulRegular (Ts θ (Rc (R0 O a) 1)) (fbar θ (sC (R0 O a) 1 (x0 O a))) :=
  isSMulRegular_transport (eR (a := a) (θ := θ)) eR_x0 (isSMulRegular_x0bar a)

omit [IsNoetherianRing O] in
/-- `x̄` is a uniformizer of the cusp chart at every prime containing it (`ā ≠ 0, 1`). -/
lemma exists_uniformizer (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (𝔭 : Ideal (Ts θ (Rc (R0 O a) 1)))
    [𝔭.IsPrime] (h : fbar θ (sC (R0 O a) 1 (x0 O a)) ∈ 𝔭) :
    ∃ g ∉ 𝔭, ∀ r ∈ 𝔭, ∃ s, g * r = fbar θ (sC (R0 O a) 1 (x0 O a)) * s := by
  let E : k[X] ≃+* Ts θ (Rc (R0 O a) 1) := (tsEquiv a (θ := θ)).symm.trans (eR (a := a) (θ := θ))
  have hE : E (hbar a (θ := θ)) = fbar θ (sC (R0 O a) 1 (x0 O a)) := by
    change eR (a := a) (θ := θ) ((tsEquiv a (θ := θ)).symm (hbar a)) = _
    rw [tsEquiv_symm_hbar, eR_x0]
  haveI : (𝔭.comap (E : k[X] →+* _)).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨g, hg, hgr⟩ := exists_uniformizer_of_squarefree (separable_hbar a ha0 ha1).squarefree
    (𝔭.comap (E : k[X] →+* _)) (by rw [Ideal.mem_comap]; change E _ ∈ 𝔭; rw [hE]; exact h)
  refine ⟨E g, hg, fun r hr ↦ ?_⟩
  obtain ⟨s, hs⟩ := hgr (E.symm r) (by
    rw [Ideal.mem_comap]; change E (E.symm r) ∈ 𝔭; rwa [E.apply_symm_apply])
  refine ⟨E s, ?_⟩
  have := congrArg E hs
  rwa [map_mul, map_mul, E.apply_symm_apply, hE] at this

variable (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ))

omit [IsNoetherianRing O] in
/-- **`C0 ≅ cov.C`** (`ι₀`, the localization at `c̄₀ = 1`). -/
lemma bijective_ι₀ : Function.Bijective S0.ι₀ := by
  letI := S0.ι₀.toAlgebra
  haveI := S0.hι
  have hu : IsUnit (algebraMap (Ts θ (R0 O a)) S0.C0 (Ideal.Quotient.mk _ 1)) := by
    rw [map_one, map_one]; exact isUnit_one
  let e := IsLocalization.atUnit S0.C0 S0.cov.C _ hu
  have he : ∀ c, e c = S0.ι₀ c := fun c ↦ by
    have := e.commutes c
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
    exact this
  exact ⟨fun x y h ↦ e.injective (by rw [he, he, h]),
    fun z ↦ ⟨e.symm z, by rw [← he, e.apply_symm_apply]⟩⟩

/-- `C0 ≃ cov.C`. -/
def e0 : S0.C0 ≃+* S0.cov.C := RingEquiv.ofBijective S0.ι₀ (bijective_ι₀ S0)

omit [IsNoetherianRing O] in
lemma e0_x0 : e0 S0 (algebraMap (Ts θ (R0 O a)) S0.C0 (Ideal.Quotient.mk _ (x0 O a))) =
    algebraMap (Ts θ (Rc (R0 O a) 1)) S0.cov.C (fbar θ (sC (R0 O a) 1 (x0 O a))) := by
  change S0.ι₀ _ = _
  rw [S0.hι₀, ← eR_apply, eR_x0]

omit [IsNoetherianRing O] in
lemma hψ : (ψb (θ := θ) (Rc (R0 O a) 1) (sC (R0 O a) 1 (x0 O a)) (sC (R0 O a) 1 (x0 O a)))
    Polynomial.X = algebraMap (Ts θ (Rc (R0 O a) 1))
      (Admissible.Hat (fbar θ (sC (R0 O a) 1 (x0 O a))))
      (fbar θ (sC (R0 O a) 1 (x0 O a))) := by
  simp [ψb]

/-- **`x̄` is a nonzerodivisor on `C0`.** -/
theorem isSMulRegular_C0 :
    IsSMulRegular S0.C0 (algebraMap (Ts θ (R0 O a)) S0.C0 (Ideal.Quotient.mk _ (x0 O a))) := by
  have h : IsSMulRegular S0.cov.C
      (algebraMap (Ts θ (Rc (R0 O a) 1)) S0.cov.C (fbar θ (sC (R0 O a) 1 (x0 O a)))) :=
    fun x y hxy ↦ sub_eq_zero.1 (S0.cov.isSMulRegular_f isSMulRegular_fbar (x - y)
      (by rw [mul_sub, sub_eq_zero]; exact hxy))
  exact isSMulRegular_transport (e0 S0).symm (by rw [← e0_x0, RingEquiv.symm_apply_apply]) h

/-- **`C0` localized at a point over a cusp is a discrete valuation ring.** -/
theorem isDiscreteValuationRing_C0 (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (𝔪 : Ideal S0.C0) [𝔪.IsPrime]
    (hx : algebraMap (Ts θ (R0 O a)) S0.C0 (Ideal.Quotient.mk _ (x0 O a)) ∈ 𝔪) :
    ∃ _ : IsDomain (Localization.AtPrime 𝔪), IsDiscreteValuationRing (Localization.AtPrime 𝔪) := by
  set 𝔪' : Ideal S0.cov.C := 𝔪.comap ((e0 S0).symm : S0.cov.C →+* S0.C0) with h𝔪'
  haveI : 𝔪'.IsPrime := Ideal.comap_isPrime _ _
  have hf : algebraMap (Ts θ (Rc (R0 O a) 1)) S0.cov.C (fbar θ (sC (R0 O a) 1 (x0 O a))) ∈ 𝔪' := by
    rw [h𝔪', Ideal.mem_comap, ← e0_x0]
    change (e0 S0).symm (e0 S0 _) ∈ 𝔪
    rwa [RingEquiv.symm_apply_apply]
  obtain ⟨hD, hV⟩ := S0.cov.isDiscreteValuationRing_atPrime hψ isSMulRegular_fbar 𝔪'
    hf
    fun r hr ↦ by
      haveI : (𝔪'.comap (algebraMap (Ts θ (Rc (R0 O a) 1)) S0.cov.C)).IsPrime :=
        Ideal.comap_isPrime _ _
      obtain ⟨g, hg, hgr⟩ := exists_uniformizer ha0 ha1
        (𝔪'.comap (algebraMap (Ts θ (Rc (R0 O a) 1)) S0.cov.C)) (Ideal.mem_comap.2 hf)
      obtain ⟨s, hs⟩ := hgr r (Ideal.mem_comap.2 hr)
      exact ⟨g, s, hg, hs⟩
  have hM : 𝔪.primeCompl.map (e0 S0).toMonoidHom = 𝔪'.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (e0 S0).symm (e0 S0 x) ∉ 𝔪
      rwa [RingEquiv.symm_apply_apply]
    · intro hy
      exact ⟨(e0 S0).symm y, hy, (e0 S0).apply_symm_apply y⟩
  let F : Localization.AtPrime 𝔪 ≃+* Localization.AtPrime 𝔪' :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔪')
      (e0 S0) hM
  haveI : IsDomain (Localization.AtPrime 𝔪) := F.injective.isDomain F.toRingHom
  exact ⟨inferInstance, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing F.symm⟩

end Cusp

/-! ### The datum -/

lemma mem_nonZeroDivisors_of_isSMulRegular {A : Type*} [CommRing A] {x : A}
    (h : IsSMulRegular A x) : x ∈ nonZeroDivisors A :=
  IsRegular.mem_nonZeroDivisors ⟨h, fun y z hyz ↦ h (by
    simp only [smul_eq_mul]
    simpa only [mul_comm] using hyz)⟩

/-- The `k`-algebra structure of `C0` (through `R0/J`). -/
@[reducible] def algK0 (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ)) :
    Algebra k S0.C0 :=
  ((algebraMap (Ts θ (R0 O a)) S0.C0).comp (algebraMap k (Ts θ (R0 O a)))).toAlgebra

omit [IsNoetherianRing O] in
lemma towerK0 (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ)) :
    letI := algK0 S0
    IsScalarTower k (Ts θ (R0 O a)) S0.C0 :=
  letI := algK0 S0
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

section Datum

variable (D : Datum O θ a)

/-- The localization `C0[1/x̄]`. -/
abbrev Cb0 : Type u := EtaleTower.Cb θ (R0 O a) D.S0.C0 (x0 O a)

/-- The localization `C1[1/ȳ]`. -/
abbrev Cb1 : Type u := EtaleTower.Cb θ (R1 O a) D.Sp.C1 (y1 O a)

/-- `C0 → C0[1/x̄] ≅ C1[1/ȳ]` (through `ω`). -/
def toCb1 : D.S0.C0 →+* Cb1 D :=
  letI := algC0x a D.S0.C0 (θ := θ)
  letI := algC1x a D.Sp.C1 (θ := θ)
  D.om.toRingEquiv.toRingHom.comp (algebraMap D.S0.C0 (Cb0 D))

lemma injective_toCb1 : Function.Injective (toCb1 D) := by
  have hle : Submonoid.powers (algebraMap (Ts θ (R0 O a)) D.S0.C0
      (Ideal.Quotient.mk _ (x0 O a))) ≤ nonZeroDivisors D.S0.C0 := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_isSMulRegular ((isSMulRegular_C0 D.S0).pow n)
  have h1 : Function.Injective (algebraMap D.S0.C0 (Cb0 D)) := IsLocalization.injective _ hle
  letI := algC0x a D.S0.C0 (θ := θ)
  letI := algC1x a D.Sp.C1 (θ := θ)
  exact D.om.toRingEquiv.injective.comp h1

omit [IsNoetherianRing O] in
/-- **`C1` is a domain** if it is connected (and nonzero): it is étale over the Dedekind domain
`R1/J ≅ R1 k ā`. -/
theorem isDomain_C1 [Nontrivial D.Sp.C1]
    (hconn : ∀ e : D.Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1) : IsDomain D.Sp.C1 := by
  haveI := isDomain_Ts_R1 a (θ := θ)
  haveI : IsIntegrallyClosed (Ts θ (R1 O a)) := by
    haveI : IsDedekindDomain (R1 k (θ a)) := isDedekindDomain_R1 (θ a)
    exact IsIntegrallyClosed.of_equiv (tsEquiv1 a (θ := θ)).symm
  exact EtaleConnectedDomain.isDomain_of_etale_away (Ideal.Quotient.mk _ 1)
    (by rw [map_one]; exact isUnit_one) D.Sp.etale hconn

variable {D} in
/-- `ȳ ≠ 0` on `C1` if `C0` is nonzero. -/
lemma y_ne_zero [Nontrivial D.S0.C0] :
    algebraMap (Ts θ (R1 O a)) D.Sp.C1 (Ideal.Quotient.mk _ (y1 O a)) ≠ 0 := by
  intro h
  haveI : Nontrivial (Cb1 D) := (injective_toCb1 D).nontrivial
  have h0 : (0 : D.Sp.C1) ∈ Submonoid.powers
      (algebraMap (Ts θ (R1 O a)) D.Sp.C1 (Ideal.Quotient.mk _ (y1 O a))) := ⟨1, by simp [h]⟩
  letI := IsLocalization.uniqueOfZeroMem (S := Cb1 D) h0
  exact not_subsingleton (Cb1 D) inferInstance

/-- **`C0` is a domain** if `C1` is connected (and `C0` nonzero). -/
theorem isDomain_C0 [Nontrivial D.S0.C0]
    (hconn : ∀ e : D.Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1) : IsDomain D.S0.C0 := by
  have hy := y_ne_zero (D := D)
  haveI : Nontrivial D.Sp.C1 := nontrivial_of_ne _ _ hy
  haveI := isDomain_C1 D hconn
  haveI : IsDomain (Cb1 D) := IsLocalization.isDomain_of_le_nonZeroDivisors (Cb1 D)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hy)
  exact (injective_toCb1 D).isDomain (toCb1 D)

variable {D} in
omit [IsNoetherianRing O] in
/-- **Faithfulness on `C0`**: a morphism acting trivially on `C0` acts trivially on `C1` (through
`ω`), if `C1 → C1[1/ȳ]` is injective. -/
lemma φ1_eq_of_φ0 (f : D.Hom D) (hinj : Function.Injective (algebraMap D.Sp.C1 (Cb1 D)))
    (hf : ∀ c, f.φ0 c = c) (c : D.Sp.C1) : f.φ1 c = c := by
  letI := algC0x a D.S0.C0 (θ := θ)
  letI := algC1x a D.Sp.C1 (θ := θ)
  apply hinj
  have h0 : f.φ0 = AlgHom.id _ _ := AlgHom.ext hf
  obtain ⟨z, hz⟩ := D.om.surjective (algebraMap D.Sp.C1 (Cb1 D) c)
  rw [← EtaleTower.CbMap_algebraMap (R1 O a) (y1 O a) f.φ1 c, ← hz, ← f.hω z, h0,
    EtaleTower.CbMap_id]
  rfl

omit [IsNoetherianRing O] in
/-- **The residue fields of `C0` at maximal ideals are `k`** (`k` algebraically closed). -/
theorem exists_residue [IsAlgClosed k] (𝔪 : Ideal D.S0.C0) [𝔪.IsMaximal] (c : D.S0.C0) :
    letI := algK0 D.S0
    ∃ x : k, c - algebraMap k D.S0.C0 x ∈ 𝔪 := by
  letI := algK0 D.S0
  haveI := towerK0 D.S0
  -- `C0` is finite over `R0/J`
  have hfin : (algebraMap (Ts θ (R0 O a)) D.S0.C0).Finite := by
    have h1 : (algebraMap (Ts θ (Rc (R0 O a) 1)) D.S0.cov.C).Finite :=
      RingHom.finite_algebraMap.2 D.S0.cov.finite
    have h2 : algebraMap (Ts θ (R0 O a)) D.S0.C0 = ((e0 D.S0).symm.toRingHom.comp
        (algebraMap (Ts θ (Rc (R0 O a) 1)) D.S0.cov.C)).comp (eR (a := a) (θ := θ)).toRingHom := by
      refine RingHom.ext fun x ↦ ?_
      change _ = (e0 D.S0).symm (algebraMap _ _ (φsC (R0 O a) 1 θ x))
      rw [← D.S0.hι₀]
      exact ((e0 D.S0).symm_apply_apply _).symm
    rw [h2]
    exact ((RingHom.Finite.of_surjective _ (e0 D.S0).symm.surjective).comp h1).comp
      (RingHom.Finite.of_surjective _ (eR (a := a) (θ := θ)).surjective)
  haveI : Module.Finite (Ts θ (R0 O a)) D.S0.C0 := RingHom.finite_algebraMap.1 hfin
  haveI : Algebra.FiniteType k (Ts θ (R0 O a)) := by
    refine Algebra.FiniteType.of_surjective (Polynomial.aeval
      (Ideal.Quotient.mk (J θ (R := R0 O a)) (t0 O a))) fun x ↦ ⟨toPolyBar a x, ?_⟩
    rw [Polynomial.aeval_def]
    exact ofPoly_toPolyBar a x
  haveI : Algebra.FiniteType k D.S0.C0 :=
    Algebra.FiniteType.trans (S := Ts θ (R0 O a)) inferInstance inferInstance
  letI : Field (D.S0.C0 ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Algebra.FiniteType k (D.S0.C0 ⧸ 𝔪) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k 𝔪) Ideal.Quotient.mk_surjective
  haveI : Module.Finite k (D.S0.C0 ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k _
  obtain ⟨x, hx⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := D.S0.C0 ⧸ 𝔪)).2 (Ideal.Quotient.mk 𝔪 c)
  refine ⟨x, ?_⟩
  rw [← Ideal.Quotient.eq, ← hx]
  rfl

/-- The action of `G` on `C0`. -/
def φ0Act {G : Type*} (act : G → D.Hom D) : G → D.S0.C0 →+* D.S0.C0 :=
  fun g ↦ ((act g).φ0 : D.S0.C0 →+* D.S0.C0)

variable {D} {G : Type*} [Group G] (act : G → D.Hom D) (hone : act 1 = Datum.Hom.id D)
  (hmul : ∀ g h, act (g * h) = (act g).comp (act h))

omit [IsNoetherianRing O] in
include hone in
lemma φ0Act_one (x : D.S0.C0) : φ0Act D act 1 x = x := by
  simp [φ0Act, hone, Datum.Hom.id]

omit [IsNoetherianRing O] in
include hmul in
lemma φ0Act_mul (g h : G) (x : D.S0.C0) :
    φ0Act D act (g * h) x = φ0Act D act g (φ0Act D act h x) := by
  simp [φ0Act, hmul, Datum.Hom.comp]

include hone hmul in
/-- **The stabiliser of a special point over a cusp is cyclic** (MR13 C2, via MR12's I5(c)
`StabilizerCyclic.isCyclic_of_faithful`): `G` finite acting on the datum `D` (`ā ≠ 0, 1`, `k`
algebraically closed), faithfully on `C1`, `C1` connected, `|G|` invertible in `k`; `𝔪` a maximal
ideal of `C0` containing `x̄ = t (t − 1)(t − ā)`. -/
theorem isCyclic_stab [IsAlgClosed k] (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) [Finite G]
    (hfaith : ∀ g, (∀ c, (act g).φ1 c = c) → g = 1)
    (hconn : ∀ e : D.Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1) (hG : (Nat.card G : k) ≠ 0)
    (𝔪 : Ideal D.S0.C0) [𝔪.IsMaximal]
    (hx : algebraMap (Ts θ (R0 O a)) D.S0.C0 (Ideal.Quotient.mk _ (x0 O a)) ∈ 𝔪) :
    IsCyclic (StabIdeal.stab (φ0Act D act) (φ0Act_one act hone) (φ0Act_mul act hmul) 𝔪) := by
  set H := StabIdeal.stab (φ0Act D act) (φ0Act_one act hone) (φ0Act_mul act hmul) 𝔪
  haveI : Nontrivial D.S0.C0 := ⟨⟨0, 1, fun h ↦ (‹𝔪.IsMaximal›).ne_top
    ((Ideal.eq_top_iff_one _).2 (h ▸ 𝔪.zero_mem))⟩⟩
  haveI := isDomain_C0 D hconn
  have hy := y_ne_zero (D := D)
  haveI : Nontrivial D.Sp.C1 := nontrivial_of_ne _ _ hy
  haveI := isDomain_C1 D hconn
  have hinj1 : Function.Injective (algebraMap D.Sp.C1 (Cb1 D)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hy)
  obtain ⟨hD, hV⟩ := isDiscreteValuationRing_C0 D.S0 ha0 ha1 𝔪 hx
  letI := algK0 D.S0
  haveI := towerK0 D.S0
  -- the action by `k`-algebra automorphisms
  let ψk : G → D.S0.C0 →ₐ[k] D.S0.C0 := fun g ↦ (act g).φ0.restrictScalars k
  have hψk : ∀ g x, ψk g x = φ0Act D act g x := fun _ _ ↦ rfl
  have hinv : ∀ g x, ψk g (ψk g⁻¹ x) = x := fun g x ↦ by
    rw [hψk, hψk, ← φ0Act_mul act hmul, mul_inv_cancel, φ0Act_one act hone]
  have hinv' : ∀ g x, ψk g⁻¹ (ψk g x) = x := fun g x ↦ by
    rw [hψk, hψk, ← φ0Act_mul act hmul, inv_mul_cancel, φ0Act_one act hone]
  let ρG : G →* (D.S0.C0 ≃ₐ[k] D.S0.C0) :=
    { toFun := fun g ↦ AlgEquiv.ofAlgHom (ψk g) (ψk g⁻¹) (AlgHom.ext (hinv g))
        (AlgHom.ext (hinv' g))
      map_one' := AlgEquiv.ext fun x ↦ by
        change ψk 1 x = x
        rw [hψk, φ0Act_one act hone]
      map_mul' := fun g h ↦ AlgEquiv.ext fun x ↦ by
        change ψk (g * h) x = ψk g (ψk h x)
        rw [hψk, hψk, hψk, φ0Act_mul act hmul] }
  let ρ : H →* (D.S0.C0 ≃ₐ[k] D.S0.C0) := ρG.comp H.subtype
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine hfaith g fun c ↦ φ1_eq_of_φ0 (act g) hinj1 (fun x ↦ ?_) c
    have := congrArg (fun σ : D.S0.C0 ≃ₐ[k] D.S0.C0 ↦ σ x) hg
    exact this
  have hfix : ∀ g : H, 𝔪 = 𝔪.comap (ρ g : D.S0.C0 →+* D.S0.C0) := fun g ↦ by
    have e : (ρ g : D.S0.C0 →+* D.S0.C0) = φ0Act D act g := RingHom.ext fun _ ↦ rfl
    rw [e]
    exact g.2.symm
  have hGH : (Nat.card H : k) ≠ 0 := by
    have h := H.card_mul_index
    rw [← h, Nat.cast_mul] at hG
    exact left_ne_zero_of_mul hG
  have hres : ∀ c : D.S0.C0, ∃ x : k, c - algebraMap k D.S0.C0 x ∈ 𝔪 :=
    fun c ↦ exists_residue D 𝔪 c
  exact StabilizerCyclic.isCyclic_of_faithful ρ 𝔪 hfix hGH hρ hres
    (IsLocalization.injective _ 𝔪.primeCompl_le_nonZeroDivisors)

end Datum

end

end P1Three

end SemistableReduction
