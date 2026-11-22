/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspKummerTameDVR
import TemperedFundamentalGroups.SemistableReduction.FormalCuspAssemble
import TemperedFundamentalGroups.SemistableReduction.FormalPoints
import TemperedFundamentalGroups.SemistableReduction.CuspInput
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialMk
import TemperedFundamentalGroups.SemistableReduction.P1ThreeCuspCyclic

/-!
# The cusp special datum over `V₀` of `P1Three` from a tame cover (MR13 S6/S7)

For a finite flat algebra `C0` over the special fibre `R0/J ≅ k[t]` of the cusp chart `V₀` of
`ℙ¹ ∖ {0, 1, a}` (`k` algebraically closed, `ā ≠ 0, 1`), étale over `D(x̄)`
(`x̄ = t (t − 1)(t − ā)`) and tamely ramified over the cusps (at every prime `P ∋ x̄` of `C0` the
localization `C0_P` is a discrete valuation ring with ramification index dividing `N`,
`N` invertible in `k`), **`P1Three.CuspSpecial.ofTame`** is a cusp special datum
`CuspTower.CuspSpecial (R0 O a) 1 (x0 O a)` with `C0` itself (and its given algebra structure) as
covering and `ι₀ = id`.

Generic pieces (namespace `FormalKummer`):
* `tamePt`, `tameIdeal`: an enumeration of the maximal ideals containing `f` (`FormalPoints.Pts`);
* `TameLocForms`: chosen formal local forms `R̂_𝔪 ⊗_R C ≅ ∏ᵢ R̂_𝔪[t]/(t^{dᵢ} − f)` at the points;
  **`nonempty_tameLocForms`** from the tame Kummer lemma
  (`FormalKummer.exists_cuspLoc_of_tame_of_dvr`);
* **`tameCovering`**: the admissible covering (no nodes, cusp factors along `f`) assembled by
  `FormalKummer.assembleCuspEquiv`;
* transport along ring isomorphisms of the base: `etale_awayMap_ringEquiv`,
  `ramificationIdx_eq_of_ringEquiv`, `tame_transport`.
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace FormalKummer

noncomputable section

open FormalPoints

/-! ### The points of `V(f)` -/

section Points

variable {R : Type u} [CommRing R] (f : R) [Finite (Pts f)]

/-- The `j`-th maximal ideal containing `f`. -/
def tamePt (j : Fin (Nat.card (Pts f))) : Pts f := (Finite.equivFin _).symm j

/-- The ideal of the `j`-th point. -/
def tameIdeal (j : Fin (Nat.card (Pts f))) : Ideal R := (tamePt f j).ideal

instance (j : Fin (Nat.card (Pts f))) : (tameIdeal f j).IsMaximal :=
  inferInstanceAs ((tamePt f j).ideal.IsMaximal)

lemma injective_tameIdeal : Function.Injective (tameIdeal f) :=
  fun _ _ h ↦ (Finite.equivFin _).symm.injective (ideal_injective f h)

lemma mem_tameIdeal (j : Fin (Nat.card (Pts f))) : f ∈ tameIdeal f j := (tamePt f j).mem

lemma iInf_tameIdeal_le [IsJacobsonRing R] :
    ⨅ j, tameIdeal f j ≤ (Ideal.span {f}).radical := by
  rw [show (⨅ j, tameIdeal f j) = ⨅ P : Pts f, P.ideal from
    (Finite.equivFin _).symm.iInf_comp (g := fun P : Pts f ↦ P.ideal)]
  exact iInf_le_radical f

end Points

/-! ### Chosen tame local forms -/

/-- **Formal local forms of a tame cover** at the points `𝔪 j`:
`R̂_{𝔪 j} ⊗_R C ≅ ∏ᵢ R̂_{𝔪 j}[t]/(t^{d j i} − s)` with `0 < d j i ∣ N`. -/
structure TameLocForms {ι : Type} {R : Type u} [CommRing R] (𝔪 : ι → Ideal R) (s : R)
    (C : Type u) [CommRing C] [Algebra R C] (N : ℕ) where
  /-- The number of local factors at the point `j`. -/
  r : ι → ℕ
  /-- The ramification indices of the local factors. -/
  d : ∀ j, Fin (r j) → ℕ
  hd : ∀ j i, 0 < d j i
  hdN : ∀ j i, d j i ∣ N
  /-- The local forms. -/
  Ψ : ∀ j, AdicCompletion (𝔪 j) R ⊗[R] C ≃ₐ[AdicCompletion (𝔪 j) R]
    ∀ i : Fin (r j), AdjoinRoot (X ^ d j i - Polynomial.C (algebraMap R (AdicCompletion (𝔪 j) R) s))

section Exists

variable {k : Type u} [Field k] [IsAlgClosed k] {R : Type u} [CommRing R] [Algebra k R]
  [Algebra.FiniteType k R] {f : R} [Finite (Pts f)] (C : Type u) [CommRing C] [Algebra R C]
  [Module.Finite R C] [Module.Flat R C]

/-- **Tame local forms exist** at all points of `V(f)` if `f` is a regular local parameter at
these points and `C` is finite flat over `R` with discrete valuation rings `C_P` at the primes
`P ∋ f`, with ramification indices dividing `N` (`N` invertible in `k`). -/
theorem nonempty_tameLocForms (hreg : IsSMulRegular R f)
    (hU : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], f ∈ 𝔪 → ∃ g ∉ 𝔪, ∀ r ∈ 𝔪, ∃ r', g * r = f * r')
    {N : ℕ} (hN : (N : k) ≠ 0)
    (hP : ∀ (P : Ideal C) [P.IsPrime], algebraMap R C f ∈ P →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        P.ramificationIdx R ∣ N) :
    Nonempty (TameLocForms (tameIdeal f) f C N) := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have H : ∀ j, ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, 0 < d i) ∧ (∀ i, d i ∣ N) ∧
      Nonempty (AdicCompletion (tameIdeal f j) R ⊗[R] C ≃ₐ[AdicCompletion (tameIdeal f j) R]
        ∀ i, AdjoinRoot (X ^ d i -
          Polynomial.C (algebraMap R (AdicCompletion (tameIdeal f j) R) f))) := fun j ↦
    exists_cuspLoc_of_tame_of_dvr (k := k) (tameIdeal f j)
      (FormalPoints.algebraMap_surjective_quot (k := k) (tameIdeal f j)) (mem_tameIdeal f j) hreg
      (hU _ (mem_tameIdeal f j)) hN fun P _ _ ↦ hP P (by
        have h2 : f ∈ P.under R := Ideal.over_def P (tameIdeal f j) ▸ mem_tameIdeal f j
        exact h2)
  choose r d hd hdN hΨ using H
  exact ⟨⟨r, d, hd, hdN, fun j ↦ (hΨ j).some⟩⟩

end Exists

/-! ### The admissible covering -/

section Covering

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
  [IsJacobsonRing R] {f : R} [Finite (Pts f)] {C : Type u} [CommRing C] [Algebra R C] {N : ℕ}

/-- **The admissible covering of a tame cover** of a chart with cusps along `f`: no nodes, the
cusp factors indexed by the points of `V(f)` and the local factors there. -/
def tameCovering (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
    (ψ : k[X] →ₐ[k] Admissible.Hat f) (hψ : ψ X = algebraMap R (Admissible.Hat f) f)
    (hfin : Module.Finite R C) (het : (Localization.awayMap (algebraMap R C) f).Etale)
    (hN : (N : k) ≠ 0) (L : TameLocForms (tameIdeal f) f C N) : Admissible.Covering φ ψ where
  C := C
  finite := hfin
  etale := het
  ι := Empty
  idem := isEmptyElim
  isIdempotentElem_idem := isEmptyElim
  e := isEmptyElim
  e_pos := isEmptyElim
  e_ne_zero := isEmptyElim
  κ := Σ j, Fin (L.r j)
  cidem p := CompletionProd.idem (injective_tameIdeal f) (mem_tameIdeal f) (iInf_tameIdeal_le f) p.1
  isIdempotentElem_cidem p := CompletionProd.isIdempotentElem_idem _ _ _ p.1
  ce p := L.d p.1 p.2
  ce_pos p := L.hd p.1 p.2
  ce_ne_zero p h0 := by
    obtain ⟨c, hc⟩ := L.hdN p.1 p.2
    exact hN (by rw [hc, Nat.cast_mul, h0, zero_mul])
  kummer := (assembleCuspEquiv (injective_tameIdeal f) (mem_tameIdeal f) (iInf_tameIdeal_le f)
    ψ hψ L.Ψ).trans AlgEquiv.uniqueProd.symm

end Covering

/-! ### Transport along an isomorphism of the base -/

section Transport

/-- The `awayMap` of `g ∘ e⁻¹` at `e x` is étale if that of `g` at `x` is. -/
lemma etale_awayMap_ringEquiv {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (e : A ≃+* B) (g : A →+* C) {x : A} {y : B} (hy : e x = y)
    (h : (Localization.awayMap g x).Etale) :
    (Localization.awayMap (g.comp e.symm.toRingHom) y).Etale := by
  subst hy
  have hgx : (g.comp e.symm.toRingHom) (e x) = g x := by simp
  let e1 : Localization.Away (e x) ≃+* Localization.Away x :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (e x)) (T := Submonoid.powers x)
      _ _ e.symm (by rw [Submonoid.map_powers]; simp)
  let e2 : Localization.Away (g x) ≃+* Localization.Away ((g.comp e.symm.toRingHom) (e x)) :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (g x))
      (T := Submonoid.powers ((g.comp e.symm.toRingHom) (e x))) _ _ (RingEquiv.refl C)
      (by rw [Submonoid.map_powers, hgx]; rfl)
  have hc : Localization.awayMap (g.comp e.symm.toRingHom) (e x) =
      (e2.toRingHom.comp (Localization.awayMap g x)).comp e1.toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (e x)) (RingHom.ext fun b ↦ ?_)
    have h1 : e1 (algebraMap B (Localization.Away (e x)) b) =
        algebraMap A (Localization.Away x) (e.symm b) :=
      IsLocalization.ringEquivOfRingEquiv_eq _ _
    have h2 (c : C) : e2 (algebraMap C (Localization.Away (g x)) c) =
        algebraMap C (Localization.Away ((g.comp e.symm.toRingHom) (e x))) c :=
      IsLocalization.ringEquivOfRingEquiv_eq _ _
    have h3 : Localization.awayMap g x (algebraMap A (Localization.Away x) (e.symm b)) =
        algebraMap C (Localization.Away (g x)) (g (e.symm b)) :=
      IsLocalization.map_eq _ _
    have h4 : Localization.awayMap (g.comp e.symm.toRingHom) (e x)
        (algebraMap B (Localization.Away (e x)) b) =
        algebraMap C (Localization.Away ((g.comp e.symm.toRingHom) (e x))) (g (e.symm b)) :=
      IsLocalization.map_eq _ _
    change Localization.awayMap (g.comp e.symm.toRingHom) (e x)
        (algebraMap B (Localization.Away (e x)) b) =
      e2 (Localization.awayMap g x (e1 (algebraMap B (Localization.Away (e x)) b)))
    rw [h4, h1, h3, h2]
  rw [hc]
  exact RingHom.Etale.respectsIso.2 _ _ (RingHom.Etale.respectsIso.1 _ _ h)

/-- The ramification index does not change along an isomorphism of the base. -/
lemma ramificationIdx_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra B C] (e : A ≃+* B)
    (he : ∀ b, algebraMap B C b = algebraMap A C (e.symm b)) (P : Ideal C) [P.IsPrime] :
    P.ramificationIdx B = P.ramificationIdx A := by
  have hB : algebraMap B C = (algebraMap A C).comp e.symm.toRingHom := RingHom.ext he
  have hI : (P.under B).map (algebraMap B C) = (P.under A).map (algebraMap A C) := by
    simp only [Ideal.under]
    rw [hB, ← Ideal.map_map, ← Ideal.comap_comap,
      Ideal.map_comap_of_surjective e.symm.toRingHom e.symm.surjective]
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def,
    IsScalarTower.algebraMap_eq B C (Localization.AtPrime P),
    IsScalarTower.algebraMap_eq A C (Localization.AtPrime P), ← Ideal.map_map, ← Ideal.map_map, hI]

/-- Transport of the tameness hypothesis along an isomorphism of the base. -/
lemma tame_transport {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    [Algebra B C] (e : A ≃+* B) (he : ∀ b, algebraMap B C b = algebraMap A C (e.symm b))
    {x : A} {y : B} (hy : e x = y) {N : ℕ}
    (hP : ∀ (P : Ideal C) [P.IsPrime], algebraMap A C x ∈ P →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        P.ramificationIdx A ∣ N) :
    ∀ (P : Ideal C) [P.IsPrime], algebraMap B C y ∈ P →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        P.ramificationIdx B ∣ N := by
  intro P _ hyP
  rw [he, ← hy, e.symm_apply_apply] at hyP
  obtain ⟨hD, hV, hd⟩ := hP P hyP
  exact ⟨hD, hV, (ramificationIdx_eq_of_ringEquiv e he P) ▸ hd⟩

/-- Transport of finiteness along an isomorphism of the base. -/
lemma finite_transport {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    [Algebra B C] (e : A ≃+* B) (he : ∀ b, algebraMap B C b = algebraMap A C (e.symm b))
    [Module.Finite A C] : Module.Finite B C := by
  have hB : algebraMap B C = (algebraMap A C).comp e.symm.toRingHom := RingHom.ext he
  refine RingHom.finite_algebraMap.mp ?_
  rw [hB]
  exact (RingHom.finite_algebraMap.mpr inferInstance).comp
    (RingHom.Finite.of_surjective _ e.symm.surjective)

/-- Transport of flatness along an isomorphism of the base. -/
lemma flat_transport {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    [Algebra B C] (e : A ≃+* B) (he : ∀ b, algebraMap B C b = algebraMap A C (e.symm b))
    [Module.Flat A C] : Module.Flat B C := by
  have hB : algebraMap B C = (algebraMap A C).comp e.symm.toRingHom := RingHom.ext he
  refine RingHom.flat_algebraMap_iff.mp ?_
  rw [hB]
  exact (RingHom.Flat.of_bijective e.symm.bijective).comp (RingHom.flat_algebraMap_iff.mpr
    inferInstance)

/-- Transport of étaleness over `D(x)` along an isomorphism of the base. -/
lemma etale_transport {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    [Algebra B C] (e : A ≃+* B) (he : ∀ b, algebraMap B C b = algebraMap A C (e.symm b))
    {x : A} {y : B} (hy : e x = y) (h : (Localization.awayMap (algebraMap A C) x).Etale) :
    (Localization.awayMap (algebraMap B C) y).Etale := by
  have hB : algebraMap B C = (algebraMap A C).comp e.symm.toRingHom := RingHom.ext he
  rw [hB]
  exact etale_awayMap_ringEquiv e _ hy h

end Transport

end

end FormalKummer

namespace P1Three

open TateLevel AdmissibleLift CuspTower EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {a : O}

variable (a θ) in
/-- The special fibre of the cusp chart `V₀` is a finite type `k`-algebra. -/
theorem finiteType_ts_rc : Algebra.FiniteType k (Ts θ (Rc (R0 O a) 1)) := by
  haveI : Algebra.FiniteType O (R0 O a) :=
    Algebra.FiniteType.trans (S := O[X]) inferInstance inferInstance
  haveI : Algebra.FinitePresentation (R0 O a) (Rc (R0 O a) 1) :=
    IsLocalization.Away.finitePresentation (1 : R0 O a)
  haveI : Algebra.FiniteType O (Rc (R0 O a) 1) :=
    Algebra.FiniteType.trans (S := R0 O a) inferInstance inferInstance
  haveI : Algebra.FiniteType O (Ts θ (Rc (R0 O a) 1)) :=
    Algebra.FiniteType.trans (S := Rc (R0 O a) 1) inferInstance inferInstance
  letI : Algebra O k := θ.toAlgebra
  haveI : @IsScalarTower O k (Ts θ (Rc (R0 O a) 1)) _ Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun o ↦ (QuadNodeTower.algK_θ (θ := θ) _ o).symm
  exact Algebra.FiniteType.of_restrictScalars_finiteType O k _

variable (a θ) in
/-- `V(x̄)` in the special fibre of `V₀` is finite: `k[T]/(T (T − 1)(T − ā))` is Artinian. -/
theorem isArtinianRing_ts_rc :
    IsArtinianRing (Ts θ (Rc (R0 O a) 1) ⧸ Ideal.span {fbar θ (sC (R0 O a) 1 (x0 O a))}) := by
  let E : k[X] ≃+* Ts θ (Rc (R0 O a) 1) :=
    (tsEquiv a (θ := θ)).symm.trans (eR (a := a) (θ := θ))
  have hE : E (hbar a (θ := θ)) = fbar θ (sC (R0 O a) 1 (x0 O a)) := by
    change eR (a := a) (θ := θ) ((tsEquiv a (θ := θ)).symm (hbar a)) = _
    rw [tsEquiv_symm_hbar, eR_x0]
  have hspan : Ideal.span {fbar θ (sC (R0 O a) 1 (x0 O a))} =
      (Ideal.span {hbar a (θ := θ)}).map (E : k[X] →+* Ts θ (Rc (R0 O a) 1)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z ↦ Ideal.span {z}) hE.symm
  haveI : Module.Finite k (AdjoinRoot (hbar a (θ := θ))) :=
    (AdjoinRoot.powerBasis (hbar_ne_zero a)).finite
  haveI : IsArtinianRing (AdjoinRoot (hbar a (θ := θ))) := IsArtinianRing.of_finite k _
  haveI : IsArtinianRing (k[X] ⧸ Ideal.span {hbar a (θ := θ)}) :=
    inferInstanceAs (IsArtinianRing (AdjoinRoot (hbar a (θ := θ))))
  exact (Ideal.quotientEquiv _ _ E hspan).isArtinianRing

variable (C0 : Type u) [CommRing C0] [Algebra (Ts θ (R0 O a)) C0]

omit hθ in
lemma algOne_apply (b : Ts θ (Rc (R0 O a) 1)) :
    letI := CuspChart.algOne C0 (θ := θ) (T := R0 O a)
    algebraMap (Ts θ (Rc (R0 O a) 1)) C0 b =
      algebraMap (Ts θ (R0 O a)) C0 ((CuspChart.tsEquivOne θ (R0 O a)).symm b) :=
  rfl

omit hθ in
lemma tsEquivOne_x0 : CuspChart.tsEquivOne θ (R0 O a) (Ideal.Quotient.mk _ (x0 O a)) =
    fbar θ (sC (R0 O a) 1 (x0 O a)) :=
  eR_x0

variable [IsAlgClosed k] [Module.Finite (Ts θ (R0 O a)) C0] [Module.Flat (Ts θ (R0 O a)) C0]

/-- **The admissible covering of the special fibre of `V₀` defined by a tame cover `C0`** of
`R0/J ≅ k[t]` (étale over `D(x̄)`, tamely ramified over the cusps `x̄ = 0`), `C0` viewed over
`R0[1/1]/J` through `tsEquivOne` (`CuspChart.algOne`). -/
def covTame (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1)
    (het : (Localization.awayMap (algebraMap (Ts θ (R0 O a)) C0)
      (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a))).Etale)
    {N : ℕ} (hN : (N : k) ≠ 0)
    (hP : ∀ (P : Ideal C0) [P.IsPrime],
      algebraMap (Ts θ (R0 O a)) C0 (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a)) ∈ P →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        P.ramificationIdx (Ts θ (R0 O a)) ∣ N)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ (sC (R0 O a) 1 (x0 O a)))) :
    Admissible.Covering φ₀ (ψb (θ := θ) (Rc (R0 O a) 1) (sC (R0 O a) 1 (x0 O a))
      (sC (R0 O a) 1 (x0 O a))) :=
  letI := CuspChart.algOne C0 (θ := θ) (T := R0 O a)
  haveI := finiteType_ts_rc (a := a) (θ := θ)
  haveI : IsNoetherianRing (Ts θ (Rc (R0 O a) 1)) :=
    Algebra.FiniteType.isNoetherianRing k (Ts θ (Rc (R0 O a) 1))
  haveI : IsJacobsonRing (Ts θ (Rc (R0 O a) 1)) := isJacobsonRing_of_finiteType (A := k)
  haveI := isArtinianRing_ts_rc (a := a) (θ := θ)
  haveI : Module.Finite (Ts θ (Rc (R0 O a) 1)) C0 :=
    FormalKummer.finite_transport (CuspChart.tsEquivOne θ (R0 O a)) (algOne_apply C0)
  haveI : Module.Flat (Ts θ (Rc (R0 O a) 1)) C0 :=
    FormalKummer.flat_transport (CuspChart.tsEquivOne θ (R0 O a)) (algOne_apply C0)
  FormalKummer.tameCovering φ₀ _ hψ inferInstance
    (FormalKummer.etale_transport (CuspChart.tsEquivOne θ (R0 O a)) (algOne_apply C0)
      tsEquivOne_x0 het) hN
    (Classical.choice (FormalKummer.nonempty_tameLocForms (k := k) C0 isSMulRegular_fbar
      (fun 𝔪 _ h ↦ exists_uniformizer ha0 ha1 𝔪 h) hN
      (FormalKummer.tame_transport (CuspChart.tsEquivOne θ (R0 O a)) (algOne_apply C0)
        tsEquivOne_x0 hP)))

/-- **The cusp special datum over `V₀` of `P1Three` from a tame cover** `C0` of `R0/J ≅ k[t]`
(finite flat, étale over `D(x̄)`, at every prime `P ∋ x̄` a discrete valuation ring with
ramification index dividing `N`, `N` invertible in `k`): the covering is `C0` itself with its given
algebra structure (`covTame`), `ι₀ = id`; `φ₀` is arbitrary (there are no nodes). -/
def CuspSpecial.ofTame (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1)
    (het : (Localization.awayMap (algebraMap (Ts θ (R0 O a)) C0)
      (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a))).Etale)
    {N : ℕ} (hN : (N : k) ≠ 0)
    (hP : ∀ (P : Ideal C0) [P.IsPrime],
      algebraMap (Ts θ (R0 O a)) C0 (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a)) ∈ P →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        P.ramificationIdx (Ts θ (R0 O a)) ∣ N)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ (sC (R0 O a) 1 (x0 O a)))) :
    CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ) where
  C0 := C0
  φ₀ := φ₀
  cov := covTame C0 ha0 ha1 het hN hP φ₀
  noNodes := (inferInstance : IsEmpty Empty)
  ι₀ := RingHom.id C0
  hι₀ := fun x ↦ congrArg (algebraMap (Ts θ (R0 O a)) C0)
    ((CuspChart.tsEquivOne θ (R0 O a)).symm_apply_apply x).symm
  hι := CuspChart.hιOne C0 (θ := θ) (T := R0 O a) (by rw [map_one, map_one]; exact isUnit_one)

/-- The covering of `CuspSpecial.ofTame` is the given `C0`. -/
lemma CuspSpecial.ofTame_C0 (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1)
    (het : (Localization.awayMap (algebraMap (Ts θ (R0 O a)) C0)
      (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a))).Etale)
    {N : ℕ} (hN : (N : k) ≠ 0)
    (hP : ∀ (P : Ideal C0) [P.IsPrime],
      algebraMap (Ts θ (R0 O a)) C0 (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a)) ∈ P →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        P.ramificationIdx (Ts θ (R0 O a)) ∣ N)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ (sC (R0 O a) 1 (x0 O a)))) :
    (CuspSpecial.ofTame C0 ha0 ha1 het hN hP φ₀).C0 = C0 :=
  rfl

/-- The algebra structure of `CuspSpecial.ofTame` is the given one. -/
lemma CuspSpecial.ofTame_algebraMap (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1)
    (het : (Localization.awayMap (algebraMap (Ts θ (R0 O a)) C0)
      (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a))).Etale)
    {N : ℕ} (hN : (N : k) ≠ 0)
    (hP : ∀ (P : Ideal C0) [P.IsPrime],
      algebraMap (Ts θ (R0 O a)) C0 (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a)) ∈ P →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        P.ramificationIdx (Ts θ (R0 O a)) ∣ N)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ (sC (R0 O a) 1 (x0 O a))))
    (x : Ts θ (R0 O a)) :
    (algebraMap (Ts θ (R0 O a)) (CuspSpecial.ofTame C0 ha0 ha1 het hN hP φ₀).C0 x : C0) =
      algebraMap (Ts θ (R0 O a)) C0 x :=
  rfl

/-- The map `ι₀` of `CuspSpecial.ofTame` is the identity. -/
lemma CuspSpecial.ofTame_ι₀ (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1)
    (het : (Localization.awayMap (algebraMap (Ts θ (R0 O a)) C0)
      (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a))).Etale)
    {N : ℕ} (hN : (N : k) ≠ 0)
    (hP : ∀ (P : Ideal C0) [P.IsPrime],
      algebraMap (Ts θ (R0 O a)) C0 (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a)) ∈ P →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        P.ramificationIdx (Ts θ (R0 O a)) ∣ N)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ (sC (R0 O a) 1 (x0 O a))))
    (c : C0) : ((CuspSpecial.ofTame C0 ha0 ha1 het hN hP φ₀).ι₀ c : C0) = c :=
  rfl

end

end P1Three

end SemistableReduction
