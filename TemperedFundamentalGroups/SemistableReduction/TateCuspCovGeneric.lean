/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalCuspNode
import TemperedFundamentalGroups.SemistableReduction.FormalCuspEtale2
import TemperedFundamentalGroups.SemistableReduction.FormalPoints
import TemperedFundamentalGroups.SemistableReduction.PurityLocal

/-!
# Generic inputs for the special-fibre covering over a cusp chart (MR12 S5.6)

* `NormLocal.isUnramifiedAt_of_pred`, `PurityLocal.isUnramifiedAt_integralClosure_of_pred`:
  unramifiedness of a normalisation over the punctured spectrum of a local ring, away from the
  primes excluded by a predicate (at a cusp: the prime `(s)` of the marked divisor);
* `FormalKummer.PointCuspForm.mono`, **`FormalKummer.exists_cusp'`**: `exists_cusp` with a bound
  `e j` on the ramification indices depending on the point;
* `FormalKummer.surjective_mk_comp_of_isAlgClosed`: the closed points of the special fibre of a
  finite type `O`-algebra are `k`-rational for `k` algebraically closed.
-/

universe u

open TensorProduct Polynomial IsLocalRing

namespace SemistableReduction

namespace NormLocal

noncomputable section

variable {A : Type u} [CommRing A] {L : Type u} [Field L] [Algebra A L]
  {𝔪 : Ideal A} [𝔪.IsPrime]

local notation "Aₘ" => Localization.AtPrime 𝔪

variable [Algebra (Localization.AtPrime 𝔪) L] [IsScalarTower A (Localization.AtPrime 𝔪) L]

attribute [local instance] algLoc

/-- **Unramifiedness passes to the localised normalisation**, away from the primes excluded by a
predicate `p` on the primes of `A` (`isUnramifiedAt` for `p = ⊤`). -/
theorem isUnramifiedAt_of_pred (hinj : Function.Injective (algebraMap A L))
    (p : Ideal A → Prop)
    (hunr : ∀ (Q : Ideal (integralClosure A L)) [Q.IsPrime],
      Q.comap (algebraMap A (integralClosure A L)) < 𝔪 →
        p (Q.comap (algebraMap A (integralClosure A L))) → Algebra.IsUnramifiedAt A Q)
    (Q : Ideal (integralClosure Aₘ L)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap Aₘ (integralClosure Aₘ L)) ≠ maximalIdeal Aₘ)
    (hp : p ((Q.comap (algebraMap Aₘ (integralClosure Aₘ L))).comap (algebraMap A Aₘ))) :
    Algebra.IsUnramifiedAt Aₘ Q := by
  haveI := isLocalization hinj (𝔪 := 𝔪)
  have heq : (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L))).comap
      (algebraMap A (integralClosure A L)) =
      (Q.comap (algebraMap Aₘ (integralClosure Aₘ L))).comap (algebraMap A Aₘ) := by
    rw [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have hPA : (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L))).comap
      (algebraMap A (integralClosure A L)) < 𝔪 := by
    rw [heq]
    exact comap_lt (Q.comap (algebraMap Aₘ (integralClosure Aₘ L))) hQ
  haveI : Algebra.FormallyUnramified A (Localization.AtPrime
      (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L)))) :=
    hunr _ hPA (by rw [heq]; exact hp)
  haveI : IsLocalization.AtPrime (Localization.AtPrime Q)
      (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) 𝔪.primeCompl) (Localization.AtPrime Q) Q
  let e := IsLocalization.algEquiv
    (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L))).primeCompl
    (Localization.AtPrime (Q.comap (algebraMap (integralClosure A L) (integralClosure Aₘ L))))
    (Localization.AtPrime Q)
  haveI : Algebra.FormallyUnramified A (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.of_equiv (e.restrictScalars A)
  exact Algebra.FormallyUnramified.of_restrictScalars A Aₘ (Localization.AtPrime Q)

end

end NormLocal

namespace PurityLocal

variable {A L : Type u} [CommRing A] [Field L] [Algebra A L]

/-- `isUnramifiedAt_integralClosure` away from the primes excluded by a predicate `p`. -/
lemma isUnramifiedAt_integralClosure_of_pred (B : Type u) [CommRing B] [Algebra A B]
    [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L] {P : Ideal A}
    (p : Ideal A → Prop)
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) < P →
      p (Q.comap (algebraMap A B)) → Algebra.IsUnramifiedAt A Q)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A (integralClosure A L)) < P)
    (hp : p (Q.comap (algebraMap A (integralClosure A L)))) : Algebra.IsUnramifiedAt A Q := by
  let e : B ≃ₐ[A] integralClosure A L := IsIntegralClosure.equiv A B L (integralClosure A L)
  haveI : (Q.comap e).IsPrime := Ideal.comap_isPrime _ _
  have hc : (Q.comap e).comap (algebraMap A B) =
      Q.comap (algebraMap A (integralClosure A L)) := by
    ext a
    simp
  refine isUnramifiedAt_of_equiv e.symm (Q' := Q.comap e) (by ext; simp)
    (hunr _ (hc ▸ hQ) (hc ▸ hp))

end PurityLocal

namespace FormalKummer

open AdmissibleLift

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]

omit hθ in
/-- Enlarging the bound on the ramification indices of the local formal cusp form. -/
theorem PointCuspForm.mono {s : R} {e e' : ℕ} (hee' : e ∣ e') {𝔪 : Ideal R}
    (h : PointCuspForm (θ := θ) (B := B) s e 𝔪) : PointCuspForm (θ := θ) (B := B) s e' 𝔪 := by
  obtain ⟨r, d, hd, hde, Φ⟩ := h
  exact ⟨r, d, hd, fun i ↦ (hde i).trans hee', Φ⟩

/-- **`exists_cusp` with a bound `e j` on the indices depending on the point `j`.** -/
theorem exists_cusp' [IsNoetherianRing R] {s : R} {ι : Type} [Finite ι] [DecidableEq ι]
    {e : ι → ℕ} (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal] (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
    (hloc : ∀ j, PointCuspForm (θ := θ) (B := B) s (e j) (𝔪 j)) {f : Rs θ R}
    (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
    (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
    (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
    (ψ : Polynomial k →ₐ[k] Admissible.Hat f)
    (hψ : ψ X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s)) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    ∃ (r : ι → ℕ) (d : ∀ j, Fin (r j) → ℕ), (∀ j i, 0 < d j i) ∧ (∀ j i, d j i ∣ e j) ∧
      Nonempty (Admissible.Hat f ⊗[Rs θ R] Cs θ R B ≃ₐ[Admissible.Hat f]
        ∀ p : (Σ j, Fin (r j)), Admissible.CuspPiece ψ
          (CompletionProd.idem hinj hf hrad p.1) (d p.1 p.2)) := by
  haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  haveI := Fintype.ofFinite ι
  choose r d hd hde Ψ using hloc
  exact ⟨r, d, hd, hde, ⟨assembleCuspEquiv hinj hf hrad ψ hψ fun j ↦ (Ψ j).some⟩⟩

omit [Algebra R B] in
/-- **The closed points of the special fibre are rational** over an algebraically closed `k`:
`O → R/𝔪` is onto for every maximal ideal `𝔪 ⊇ J` of a finite type `O`-algebra `R`. -/
theorem surjective_mk_comp_of_isAlgClosed [IsAlgClosed k] [Algebra.FiniteType O R]
    (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪) :
    Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)) := by
  haveI : Algebra.FiniteType O (Rs θ R) :=
    Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  letI : Algebra O k := θ.toAlgebra
  haveI : @IsScalarTower O k (Rs θ R) _ Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun o ↦ (QuadNodeTower.algK_θ (θ := θ) R o).symm
  haveI : Algebra.FiniteType k (Rs θ R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType O k _
  haveI := isMaximal_sIdeal (θ := θ) 𝔪 hJ
  have h := FormalPoints.algebraMap_surjective_quot (k := k) (sIdeal (θ := θ) 𝔪)
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, hc⟩ := h (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ y))
  obtain ⟨o, rfl⟩ := hθ.out c
  refine ⟨o, ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap, QuadNodeTower.algK_θ, Ideal.Quotient.eq,
    ← map_sub, Ideal.mem_quotient_iff_mem hJ] at hc
  rw [RingHom.comp_apply, Ideal.Quotient.eq]
  exact hc

end

end FormalKummer

end SemistableReduction
