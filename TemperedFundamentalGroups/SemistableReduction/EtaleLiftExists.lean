/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import TemperedFundamentalGroups.SemistableReduction.CompleteFinite
import TemperedFundamentalGroups.SemistableReduction.EtaleLiftMonogenic

/-!
# Existence of finite étale lifts along a complete ideal (Blueprint §12.8, M2.2)

Let `A` be a Noetherian ring, complete for the `I`-adic topology, and `S₀` a finite étale
`A/I`-algebra. Then there is a finite étale `A`-algebra `B` with `B/IB ≅ S₀`
(**`exists_finite_etale_lift`**); by `CompleteFinite.finiteEtaleEquivOfQuot` it is unique up to
a unique isomorphism lifting the identity of `S₀`. This is the existence half of the topological
invariance of finite étale algebras along a complete ideal: the essential surjectivity in
Stacks, Lemma 15.13.2 (Tag 09ZL) for the henselian pair `(A, I)`, here for `A` complete Noetherian,
by a direct route (global étale presentation + completion) rather than the Stacks proof via
henselian pairs. It generalizes the monogenic case `EtaleLift.exists_lift`.

Construction.
1. An étale algebra is standard smooth of relative dimension `0` (Mathlib,
   `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`): `S₀ = (A/I)[x_ι]/(f_σ)` with
   `#ι = #σ` and invertible Jacobian.
2. Lift the `f_σ` to `A[x_ι]`, put `C = A[x]/(f)` and `C' = C[1/Δ]`, `Δ` the Jacobian of the
   lifted system. Composing the naive presentation of `C` with the localization gives a
   submersive presentation of `C'` over `A` (Jacobian `Δ²`), so `C'` is étale over `A`
   (`etale_loc`), and `C'/IC' ≅ S₀` (`quotLocEquiv`; the reduction of `Δ` is the Jacobian
   of the presentation of `S₀`, a unit).
3. `C'` is not finite over `A` in general (the lifted equations may acquire roots "at
   infinity"); its `IC'`-adic completion `B` is. `B` is flat over `C'` (completion of a
   Noetherian ring) hence over `A`; `B/IB = C'/IC' ≅ S₀`; `B` is `I`-adically Hausdorff, so `B`
   is finite over `A` by complete Nakayama (`CompleteFinite.finite_of_finite_quotient`, Stacks
   Tag 031D); `B` is unramified over `A` because `Ω_{B/A}` is finite and vanishes modulo `IB`
   (`formallyUnramified_of_quotient`, Nakayama). Flat + unramified + finitely presented is étale
   (Mathlib `Algebra.Etale.of_formallyUnramified_of_flat`, Stacks Tag 08WD).
-/

open MvPolynomial TensorProduct

universe u

namespace SemistableReduction

namespace EtaleLiftExists

section Unramified

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

lemma tmul_D_eq_zero {x : B} (hx : x ∈ I.map (algebraMap A B)) :
    (1 : B ⧸ I.map (algebraMap A B)) ⊗ₜ[B] KaehlerDifferential.D A B x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    simp
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, TensorProduct.tmul_add, hy, hz, add_zero]
  | smul b y hy ihy =>
    rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul, ihy,
      smul_zero, zero_add, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      Ideal.Quotient.algebraMap_eq]
    have hy0 : Ideal.Quotient.mk (I.map (algebraMap A B)) y = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hy
    rw [hy0, TensorProduct.zero_tmul]

/-- **Unramifiedness modulo an ideal in the Jacobson radical**: if `B` is of finite type over
`A`, `IB ⊆ J(B)` and `B/IB` is formally unramified over `A`, then so is `B`. (`Ω_{B/A}` is a
finite `B`-module with `Ω_{B/A}/IB·Ω_{B/A} = 0`, by the conormal sequence of `B → B/IB`.) -/
theorem formallyUnramified_of_quotient [Algebra.FiniteType A B]
    (hJ : I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson)
    [Algebra.FormallyUnramified A (B ⧸ I.map (algebraMap A B))] :
    Algebra.FormallyUnramified A B := by
  set J := I.map (algebraMap A B) with hJdef
  refine ⟨?_⟩
  have hsurj : Function.Surjective (algebraMap B (B ⧸ J)) := Ideal.Quotient.mk_surjective
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange A B (B ⧸ J) hsurj
  have h0 : ∀ z : (B ⧸ J) ⊗[B] Ω[B⁄A], z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (hex z).1 (Subsingleton.elim _ _)
    obtain ⟨w, rfl⟩ := Ideal.toCotangent_surjective _ w
    rw [← hw, KaehlerDifferential.kerCotangentToTensor_toCotangent]
    exact tmul_D_eq_zero I ((Ideal.Quotient.eq_zero_iff_mem).1 (RingHom.mem_ker.1 w.2))
  have htop : (⊤ : Submodule B Ω[B⁄A]) ≤ J • ⊤ := by
    intro ω _
    have := h0 ((TensorProduct.quotTensorEquivQuotSMul Ω[B⁄A] J).symm
      (Submodule.Quotient.mk ω))
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J ⊤ Module.Finite.fg_top htop hJ
  exact ⟨fun x y ↦ by
    have hx : x ∈ (⊥ : Submodule B Ω[B⁄A]) := hbot ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule B Ω[B⁄A]) := hbot ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hx hy
    rw [hx, hy]⟩

end Unramified

section Lift

variable {A : Type u} [CommRing A] (I : Ideal A)
  {S₀ : Type*} [CommRing S₀] [Algebra (A ⧸ I) S₀] [Algebra A S₀] [IsScalarTower A (A ⧸ I) S₀]
  {ι σ : Type} [Finite σ] (P : Algebra.SubmersivePresentation (A ⧸ I) S₀ ι σ)

lemma map_mk_surjective :
    Function.Surjective (MvPolynomial.map (σ := ι) (Ideal.Quotient.mk I)) :=
  MvPolynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Lifts to `A[x_ι]` of the relations of `P`. -/
noncomputable def liftRel (j : σ) : MvPolynomial ι A :=
  (map_mk_surjective I (P.relation j)).choose

omit [Algebra A S₀] [IsScalarTower A (A ⧸ I) S₀] in
lemma map_liftRel (j : σ) :
    MvPolynomial.map (Ideal.Quotient.mk I) (liftRel I P j) = P.relation j :=
  (map_mk_surjective I (P.relation j)).choose_spec

/-- `C = A[x_ι]/(lifted relations)`. -/
abbrev Rel := MvPolynomial ι A ⧸ Ideal.span (Set.range (liftRel I P))

/-- The naive presentation of `C`, with the variable map of `P`. -/
noncomputable def pre : Algebra.PreSubmersivePresentation A (Rel I P) ι σ :=
  Algebra.PreSubmersivePresentation.naive P.map P.map_inj

/-- `C' = C[1/Δ]`, `Δ` the Jacobian of the lifted system. -/
abbrev Loc := Localization.Away (pre I P).jacobian

/-- The submersive presentation of `C'` over `A`. -/
noncomputable def presLoc : Algebra.SubmersivePresentation A (Loc I P) (Unit ⊕ ι) (Unit ⊕ σ) where
  __ := (Algebra.PreSubmersivePresentation.localizationAway (Loc I P) (pre I P).jacobian).comp
    (pre I P)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def, IsUnit.mul_iff, Algebra.PreSubmersivePresentation.localizationAway_jacobian]
    exact ⟨IsLocalization.Away.algebraMap_isUnit _, IsLocalization.Away.algebraMap_isUnit _⟩

omit [Algebra A S₀] [IsScalarTower A (A ⧸ I) S₀] in
/-- **`C'` is étale over `A`.** -/
theorem etale_loc [Finite ι] (hP : P.dimension = 0) : Algebra.Etale A (Loc I P) := by
  rw [Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero]
  refine (presLoc I P).isStandardSmoothOfRelativeDimension ?_
  have h1 := P.card_relations_le_card_vars_of_isFinite
  simp only [Algebra.Presentation.dimension] at hP ⊢
  change Nat.card (Unit ⊕ ι) - Nat.card (Unit ⊕ σ) = 0
  rw [Nat.card_sum, Nat.card_sum]
  omega

/-- The reduction `A[x] → S₀`, `x ↦ P.val`. -/
noncomputable abbrev polyRed : MvPolynomial ι A →ₐ[A] S₀ := MvPolynomial.aeval P.val

lemma polyRed_eq (p : MvPolynomial ι A) :
    polyRed I P p = MvPolynomial.aeval P.val (MvPolynomial.map (Ideal.Quotient.mk I) p) := by
  rw [← Ideal.Quotient.algebraMap_eq, MvPolynomial.aeval_map_algebraMap]

lemma polyRed_liftRel (j : σ) : polyRed I P (liftRel I P j) = 0 := by
  rw [polyRed_eq I P, map_liftRel]
  exact P.aeval_val_relation j

/-- The reduction `C → S₀`. -/
noncomputable def relRed : Rel I P →ₐ[A] S₀ :=
  Ideal.Quotient.liftₐ _ (polyRed I P) fun x hx ↦ by
    have : Ideal.span (Set.range (liftRel I P)) ≤ RingHom.ker (polyRed I P) :=
      Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact polyRed_liftRel I P j)
    exact this hx

lemma relRed_mk (p : MvPolynomial ι A) : relRed I P (Ideal.Quotient.mk _ p) = polyRed I P p := rfl

lemma relRed_algebraMap (p : MvPolynomial ι A) :
    relRed I P (algebraMap (pre I P).Ring (Rel I P) p) = polyRed I P p := by
  rw [Algebra.Generators.algebraMap_apply]
  change relRed I P (MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk _ (X i)) p) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [relRed_mk]

/-- The reduction of the lifted Jacobian is the Jacobian of `P`. -/
lemma relRed_jacobian : relRed I P (pre I P).jacobian = P.jacobian := by
  classical
  letI := Fintype.ofFinite σ
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, relRed_algebraMap,
    Algebra.Generators.algebraMap_apply]
  change (MvPolynomial.aeval P.val).toRingHom _ = (MvPolynomial.aeval P.val).toRingHom _
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  refine (polyRed_eq I P (pderiv (P.map i) (liftRel I P j))).trans ?_
  rw [← MvPolynomial.pderiv_map, map_liftRel]

lemma isUnit_relRed_jacobian : IsUnit (relRed I P (pre I P).jacobian) := by
  rw [relRed_jacobian]
  exact P.jacobian_isUnit

/-- The reduction `C' → S₀`. -/
noncomputable def locRed : Loc I P →ₐ[A] S₀ :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (pre I P).jacobian) (f := relRed I P)
    (by rintro ⟨_, n, rfl⟩; simpa only [map_pow] using (isUnit_relRed_jacobian I P).pow n)

lemma locRed_algebraMap (c : Rel I P) : locRed I P (algebraMap _ (Loc I P) c) = relRed I P c :=
  IsLocalization.lift_eq _ c

lemma locRed_surjective : Function.Surjective (locRed I P) := by
  intro s
  obtain ⟨p₀, hp₀⟩ := P.algebraMap_surjective s
  obtain ⟨p, rfl⟩ := map_mk_surjective I p₀
  refine ⟨algebraMap _ (Loc I P) (Ideal.Quotient.mk (Ideal.span (Set.range (liftRel I P))) p), ?_⟩
  rw [locRed_algebraMap, relRed_mk, polyRed_eq I P, ← hp₀, Algebra.Generators.algebraMap_apply]

omit [Algebra A S₀] [IsScalarTower A (A ⧸ I) S₀] in
lemma algebraMap_rel_eq :
    algebraMap A (Rel I P) = (Ideal.Quotient.mk _).comp (MvPolynomial.C) := rfl

/-- The kernel of `C → S₀` is `IC`. -/
lemma ker_relRed_le {c : Rel I P} (hc : relRed I P c = 0) :
    c ∈ I.map (algebraMap A (Rel I P)) := by
  classical
  letI := Fintype.ofFinite σ
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [relRed_mk, polyRed_eq] at hc
  have hmem : MvPolynomial.map (Ideal.Quotient.mk I) p ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact RingHom.mem_ker.2 ((Algebra.Generators.algebraMap_apply (P := P.toGenerators) _).trans hc)
  obtain ⟨q₀, hq₀⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  choose q hq using fun j ↦
    map_mk_surjective I (q₀ j)
  set r := p - ∑ j, q j * liftRel I P j with hr
  have hr0 : r ∈ RingHom.ker (MvPolynomial.map (σ := ι) (Ideal.Quotient.mk I)) := by
    rw [RingHom.mem_ker, hr, map_sub, map_sum, ← hq₀]
    simp only [map_mul, hq, map_liftRel, sub_self]
  rw [MvPolynomial.ker_map, Ideal.mk_ker] at hr0
  have hpr : Ideal.Quotient.mk (Ideal.span (Set.range (liftRel I P))) p =
      Ideal.Quotient.mk _ r := by
    rw [Ideal.Quotient.eq, hr, sub_sub_cancel]
    exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  rw [hpr, algebraMap_rel_eq, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hr0

/-- The kernel of `C' → S₀` is `IC'`. -/
lemma ker_locRed : RingHom.ker (locRed I P) = I.map (algebraMap A (Loc I P)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (pre I P).jacobian) x
    dsimp only at hx ⊢
    have hc : relRed I P c = 0 := by
      have h := IsLocalization.mk'_spec (Loc I P) c s
      have := congrArg (locRed I P) h
      rw [map_mul, RingHom.mem_ker.1 hx, zero_mul, locRed_algebraMap] at this
      exact this.symm
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine Ideal.mul_mem_right _ _ ?_
    have h := Ideal.mem_map_of_mem (algebraMap (Rel I P) (Loc I P)) (ker_relRed_le I P hc)
    rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
      IsScalarTower.algebraMap_apply A (A ⧸ I) S₀, Ideal.Quotient.algebraMap_eq,
      (Ideal.Quotient.eq_zero_iff_mem).2 ha, map_zero]

/-- `C'/IC' ≅ S₀`. -/
noncomputable def quotLocEquiv : (Loc I P ⧸ I.map (algebraMap A (Loc I P))) ≃ₐ[A] S₀ :=
  (Ideal.quotientEquivAlgOfEq A (ker_locRed I P)).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective (locRed_surjective I P))

end Lift

section Completion

variable {A : Type u} [CommRing A] (I : Ideal A)
  {S₀ : Type*} [CommRing S₀] [Algebra (A ⧸ I) S₀] [Algebra A S₀] [IsScalarTower A (A ⧸ I) S₀]
  {ι σ : Type} [Finite σ] (P : Algebra.SubmersivePresentation (A ⧸ I) S₀ ι σ)

/-- The ideal `IC'` of `C'`. -/
noncomputable abbrev Jl : Ideal (Loc I P) := I.map (algebraMap A (Loc I P))

/-- **The lift**: the `IC'`-adic completion `B` of `C'`. -/
abbrev Comp := AdicCompletion (Jl I P) (Loc I P)

omit [Algebra A S₀] [IsScalarTower A (A ⧸ I) S₀] in
lemma map_comp_eq : I.map (algebraMap A (Comp I P)) =
    (Jl I P).map (algebraMap (Loc I P) (Comp I P)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

instance : IsHausdorff I (Comp I P) :=
  IsHausdorff.map_algebraMap_iff.1 (inferInstance : IsHausdorff (Jl I P) (Comp I P))

variable [IsNoetherianRing (Loc I P)]

/-- `B/IB ≅ C'/IC'`. -/
noncomputable def quotCompEquivLoc :
    (Comp I P ⧸ I.map (algebraMap A (Comp I P))) ≃ₐ[Loc I P] (Loc I P ⧸ Jl I P) :=
  (Ideal.quotientEquivAlgOfEq (Loc I P) ((map_comp_eq I P).trans
    (AdicCompletion.ker_evalOneₐ_eq_map _ (IsNoetherian.noetherian _)).symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.evalOneₐ_surjective _))

/-- **`B/IB ≅ S₀`.** -/
noncomputable def quotCompEquiv : (Comp I P ⧸ I.map (algebraMap A (Comp I P))) ≃ₐ[A] S₀ :=
  ((quotCompEquivLoc I P).restrictScalars A).trans (quotLocEquiv I P)

/-- **`B` is finite over `A`** (complete Nakayama). -/
lemma finite_comp [IsAdicComplete I A] [Module.Finite (A ⧸ I) S₀] : Module.Finite A (Comp I P) := by
  haveI : Module.Finite A (A ⧸ I) :=
    Module.Finite.of_surjective (Algebra.linearMap A (A ⧸ I)) Ideal.Quotient.mk_surjective
  haveI : Module.Finite A S₀ := Module.Finite.trans (A ⧸ I) S₀
  haveI : Module.Finite A (Comp I P ⧸ I.map (algebraMap A (Comp I P))) :=
    Module.Finite.equiv (quotCompEquiv I P).symm.toLinearEquiv
  exact CompleteFinite.finite_of_finite_quotient I (Comp I P)

end Completion

/-- **Existence of finite étale lifts (M2.2)**: over a Noetherian `I`-adically complete ring
`A`, every finite étale `A/I`-algebra `S₀` is `B/IB` for a finite étale `A`-algebra `B`. -/
theorem exists_finite_etale_lift {A : Type u} [CommRing A] (I : Ideal A) [IsNoetherianRing A]
    [IsAdicComplete I A] (S₀ : Type*) [CommRing S₀] [Algebra (A ⧸ I) S₀] [Algebra A S₀]
    [IsScalarTower A (A ⧸ I) S₀] [Algebra.Etale (A ⧸ I) S₀] [Module.Finite (A ⧸ I) S₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty ((B ⧸ I.map (algebraMap A B)) ≃ₐ[A] S₀) := by
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := A ⧸ I) (S := S₀)).1
      inferInstance |>.out
  haveI := etale_loc I P hP
  haveI : IsNoetherianRing (Loc I P) := Algebra.FiniteType.isNoetherianRing A _
  haveI := finite_comp I P
  refine ⟨Comp I P, inferInstance, inferInstance, inferInstance, ?_, ⟨quotCompEquiv I P⟩⟩
  haveI : Algebra.Smooth A (Loc I P) :=
    (Algebra.Etale.iff_formallyUnramified_and_smooth.1 inferInstance).2
  haveI : Module.Flat A (Comp I P) := Module.Flat.trans A (Loc I P) (Comp I P)
  haveI : Algebra.FiniteType A (Comp I P) := inferInstance
  haveI : Algebra.FinitePresentation A (Comp I P) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI : Algebra.FormallyUnramified A S₀ := Algebra.FormallyUnramified.comp A (A ⧸ I) S₀
  haveI : Algebra.FormallyUnramified A (Comp I P ⧸ I.map (algebraMap A (Comp I P))) :=
    Algebra.FormallyUnramified.of_equiv (quotCompEquiv I P).symm
  haveI : Algebra.FormallyUnramified A (Comp I P) :=
    formallyUnramified_of_quotient I
      (EtaleLift.map_le_jacobson (IsAdicComplete.le_jacobson_bot I))
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- **Lifting finite étale algebras along a nilpotent thickening** (the level-`n` step of the
formal patching M2.3, Blueprint §12.8): over a Noetherian ring `A` with `Iⁿ = 0`, every finite
étale `A/I`-algebra is the reduction of a finite étale `A`-algebra. (With
`CompleteFinite.finiteEtaleHomEquiv`, reduction is an equivalence `FEt(A) ≃ FEt(A/I)`.) -/
theorem exists_finite_etale_lift_of_pow_eq_bot {A : Type u} [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] {n : ℕ} (hn : I ^ n = ⊥) (S₀ : Type*) [CommRing S₀]
    [Algebra (A ⧸ I) S₀] [Algebra A S₀] [IsScalarTower A (A ⧸ I) S₀] [Algebra.Etale (A ⧸ I) S₀]
    [Module.Finite (A ⧸ I) S₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty ((B ⧸ I.map (algebraMap A B)) ≃ₐ[A] S₀) :=
  haveI := CompleteFinite.isAdicComplete_of_pow_eq_bot I hn
  exists_finite_etale_lift I S₀

end EtaleLiftExists

end SemistableReduction
