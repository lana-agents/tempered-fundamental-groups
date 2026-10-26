/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalCuspNode
import TemperedFundamentalGroups.SemistableReduction.CompleteFinite
import TemperedFundamentalGroups.SemistableReduction.EtaleResidue

/-!
# The formal cusp form at an étale point (MR12 T2 S5.5, local step)

Let `R` be a Noetherian `O`-algebra (a chart), `B` a finite `R`-algebra, `R̄ = R/J`, `C = B/JB`,
and `𝔪 ⊇ J` a `k`-rational maximal ideal of `R`, `k` separably closed. If `B` is étale over `R`
on a basic open `D(f) ∋ 𝔪` (`B_f` formally étale over `R`), then (**`pointCuspForm_of_etale`**)

  `R̂_𝔪 ⊗_{R̄} C ≅ R̂_𝔪ʳ ≅ ∏ᵢ R̂_𝔪[y]/(y − s̄)`,

i.e. the local formal cusp form `PointCuspForm s 1 𝔪` holds for any `s`.

Proof: `R̂_𝔪 ⊗_{R̄} C ≅ R̂_𝔪 ⊗_R B ≅ R̂_𝔪 ⊗_R B_f` (`tensorAwayEquiv`, `f` is a unit in the local
ring `R̂_𝔪`) is finite and formally étale over `R̂_𝔪`, and it is complete, being the completion
`Ĉ` of the finite `R̄`-module `C` (`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`). A
finite étale algebra over a complete ring with separably closed residue field is split
(**`exists_algEquiv_pi_of_isSepClosed`**): its reduction is split
(`Algebra.FormallyEtale.equivPiOfIsSepClosed`) and étale lifts are unique
(`EtaleLift.algEquivOfQuot`).
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

open AdmissibleLift Cusp

namespace FormalKummer

noncomputable section

section General

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- Hausdorffness pulls back along injective linear maps. -/
theorem isHausdorff_of_injective {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] [IsHausdorff I N] (f : M →ₗ[A] N) (hf : Function.Injective f) :
    IsHausdorff I M := by
  refine ⟨fun x hx ↦ hf ?_⟩
  rw [map_zero]
  refine IsHausdorff.haus ‹_› (f x) fun n ↦ ?_
  have h1 := SModEq.zero.mp (hx n)
  refine SModEq.zero.mpr ?_
  have h2 := Submodule.mem_map_of_mem (f := f) h1
  rw [Submodule.map_smul''] at h2
  exact Submodule.smul_mono le_rfl le_top h2

/-- Adic completeness transports along linear equivalences. -/
theorem isAdicComplete_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [IsAdicComplete I N] (e : M ≃ₗ[A] N) : IsAdicComplete I M :=
  haveI := isHausdorff_of_injective I e.toLinearMap e.injective
  haveI := CompleteFinite.isPrecomplete_of_surjective I e.symm.toLinearMap e.symm.surjective
  { toIsHausdorff := ‹_›, toIsPrecomplete := ‹_› }

/-- Reducing `Aᵐ` modulo `I`. -/
def quotPiEquiv (m : ℕ) :
    ((Fin m → A) ⧸ I.map (algebraMap A (Fin m → A))) ≃ₐ[A] (Fin m → A ⧸ I) :=
  ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor (Fin m → A) I).restrictScalars A).trans <|
    (Algebra.TensorProduct.piRight A A (A ⧸ I) fun _ ↦ A).trans <|
      AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.rid A A (A ⧸ I)

/-- **A finite étale algebra over a complete ring with separably closed residue field splits**:
if `A` is `I`-adically complete, `I` maximal with `A ⧸ I` a quotient of a separably closed
field, and `C` is a finite formally étale `A`-algebra which is `IC`-adically complete, then
`C ≃ Aᵐ`. -/
theorem exists_algEquiv_pi_of_isSepClosed [IsAdicComplete I A] [I.IsMaximal] {K : Type*}
    [Field K] [IsSepClosed K] (ρ : K →+* A ⧸ I) (hρ : Function.Surjective ρ)
    (C : Type*) [CommRing C] [Algebra A C] [Module.Finite A C] [Algebra.FormallyEtale A C]
    [IsAdicComplete (I.map (algebraMap A C)) C] :
    ∃ m : ℕ, Nonempty (C ≃ₐ[A] (Fin m → A)) := by
  letI := Ideal.Quotient.field I
  haveI : IsSepClosed (A ⧸ I) :=
    EtaleResidue.isSepClosed_of_ringEquiv (RingEquiv.ofBijective ρ ⟨ρ.injective, hρ⟩)
  haveI : Module.Finite A (C ⧸ I.map (algebraMap A C)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (A ⧸ I) (C ⧸ I.map (algebraMap A C)) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ I) _
  haveI : Algebra.FormallyEtale (A ⧸ I) (C ⧸ I.map (algebraMap A C)) :=
    .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm
  let e₁ := Algebra.FormallyEtale.equivPiOfIsSepClosed (A ⧸ I) (C ⧸ I.map (algebraMap A C))
  haveI : IsArtinianRing (C ⧸ I.map (algebraMap A C)) := IsArtinianRing.of_finite (A ⧸ I) _
  haveI := Fintype.ofFinite (PrimeSpectrum (C ⧸ I.map (algebraMap A C)))
  let σ := Fintype.equivFin (PrimeSpectrum (C ⧸ I.map (algebraMap A C)))
  let e₂ : (C ⧸ I.map (algebraMap A C)) ≃ₐ[A] (Fin _ → A ⧸ I) :=
    (e₁.restrictScalars A).trans (AlgEquiv.piCongrLeft A (fun _ ↦ A ⧸ I) σ.symm).symm
  haveI : IsAdicComplete (I.map (algebraMap A (Fin (Fintype.card
      (PrimeSpectrum (C ⧸ I.map (algebraMap A C)))) → A))) _ :=
    CompleteFree.isAdicComplete_map I (Pi.basisFun A _)
  haveI : Algebra.FormallyEtale A (Fin (Fintype.card
      (PrimeSpectrum (C ⧸ I.map (algebraMap A C)))) → A) :=
    (Algebra.FormallyEtale.pi_iff _).2 inferInstance
  exact ⟨_, ⟨EtaleLift.algEquivOfQuot I (e₂.trans (quotPiEquiv I _).symm)⟩⟩

/-- Base change kills a localization at an element which becomes a unit:
`S ⊗[R] B ≃ S ⊗[R] B_f` if `f` is a unit in `S`. -/
def tensorAwayEquiv {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra R B] (f : R) (hf : IsUnit (algebraMap R S f)) :
    S ⊗[R] B ≃ₐ[S] S ⊗[R] Localization.Away (algebraMap R B f) :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R B _))
    (Algebra.TensorProduct.lift (Algebra.ofId S (S ⊗[R] B))
      (IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap R B f))
        (f := Algebra.TensorProduct.includeRight) (by
          rintro ⟨_, n, rfl⟩
          change IsUnit (Algebra.TensorProduct.includeRight (R := R) (A := S)
            ((algebraMap R B f) ^ n))
          rw [map_pow]
          refine IsUnit.pow n ?_
          change IsUnit ((1 : S) ⊗ₜ[R] algebraMap R B f)
          rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply R S]
          exact hf.map _))
      fun _ _ ↦ Commute.all _ _)
    (by
      ext x
      simp only [Algebra.TensorProduct.includeRight_apply, AlgHom.coe_restrictScalars',
        AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.lift_tmul,
        IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe, map_mul, AlgHom.coe_id, id_eq,
        map_one]
      rw [show Algebra.algHom R B (Localization.Away (algebraMap R B f)) x =
        algebraMap B (Localization.Away (algebraMap R B f)) x from rfl, IsLocalization.lift_eq]
      simp)
    (by
      ext x
      simp)

/-- `T[y]/(y¹ − a) ≅ T`. -/
def adjoinLinEquiv {T : Type*} [CommRing T] (a : T) : AdjoinRoot (X ^ 1 - C a) ≃ₐ[T] T :=
  (Ideal.quotientEquivAlgOfEq T (by rw [pow_one])).trans (Polynomial.quotientSpanXSubCAlgEquiv a)

end General

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]

/-- **The local formal form at an étale point of the special fibre**: if `B` is finite over the
Noetherian `R` and étale over `R` on a basic open `D(f)` containing the `k`-rational point `𝔪`
(`k` separably closed), then `R̂_𝔪 ⊗_{R̄} C ≅ R̂_𝔪ʳ`, i.e. the local formal cusp form holds with
all `dᵢ = 1`, for any `s`. -/
theorem pointCuspForm_of_etale [IsSepClosed k] [IsNoetherianRing R] [Module.Finite R B]
    (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
    {f : R} (hf : f ∉ 𝔪) [Algebra.FormallyEtale R (Localization.Away (algebraMap R B f))]
    (s : R) : PointCuspForm (θ := θ) (B := B) s 1 𝔪 := by
  set I₀ := sIdeal (θ := θ) 𝔪 with hI₀
  haveI : I₀.IsMaximal := isMaximal_sIdeal 𝔪 hJ
  have fg : I₀.FG := IsNoetherian.noetherian I₀
  set 𝔪h := I₀.map (algebraMap (Rs θ R) (Tn θ 𝔪)) with h𝔪h
  haveI : IsAdicComplete 𝔪h (Tn θ 𝔪) := AdicCompletion.isAdicComplete_self I₀ fg
  haveI : 𝔪h.IsMaximal := AdicCompletion.isMaximal_map_of_le I₀ I₀ le_rfl fg
  have hev (x : Rs θ R) : AdicCompletion.evalOneₐ I₀ (algebraMap _ (Tn θ 𝔪) x) =
      Ideal.Quotient.mk I₀ x :=
    RingHom.congr_fun (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk I₀) x
  have hmem (t : Tn θ 𝔪) : t ∈ 𝔪h ↔ AdicCompletion.evalOneₐ I₀ t = 0 := by
    rw [h𝔪h, ← AdicCompletion.ker_evalOneₐ_eq_map I₀ fg, RingHom.mem_ker]
    rfl
  -- the residue field of the completion is reached from `k`
  have hρ : Function.Surjective ((Ideal.Quotient.mk 𝔪h).comp
      ((algebraMap (Rs θ R) (Tn θ 𝔪)).comp (algebraMap k (Rs θ R)))) := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I₀ t)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨o, ho⟩ := hres (Ideal.Quotient.mk 𝔪 a)
    refine ⟨θ o, ?_⟩
    rw [RingHom.comp_apply, RingHom.comp_apply, QuadNodeTower.algK_θ, Ideal.Quotient.eq, hmem,
      map_sub, hev, ← hr, sub_eq_zero, Ideal.Quotient.eq, ← map_sub]
    exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.mp ho)
  -- `f` is a unit in the completion
  haveI := isLocalRing_of_isAdicComplete_maximal 𝔪h
  have hfu : IsUnit (algebraMap R (Tn θ 𝔪) f) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.eq_maximalIdeal ‹𝔪h.IsMaximal›, hmem,
      IsScalarTower.algebraMap_apply R (Rs θ R) (Tn θ 𝔪), hev, Ideal.Quotient.eq_zero_iff_mem,
      hI₀]
    change Ideal.Quotient.mk _ f ∉ sIdeal (θ := θ) 𝔪
    rw [sIdeal, Ideal.mem_quotient_iff_mem hJ]
    exact hf
  -- `R̂ ⊗_{R̄} C` is finite étale over `R̂`
  haveI : Module.Finite R (Cs θ R B) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R _).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (Rs θ R) (Cs θ R B) := Module.Finite.of_restrictScalars_finite R _ _
  let E : Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B ≃ₐ[Tn θ 𝔪]
      Tn θ 𝔪 ⊗[R] Localization.Away (algebraMap R B f) :=
    ((Algebra.TensorProduct.congr AlgEquiv.refl
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (J θ (R := R)))).trans
      (Algebra.TensorProduct.cancelBaseChange R (Rs θ R) (Tn θ 𝔪) (Tn θ 𝔪) B)).trans
      (tensorAwayEquiv f hfu)
  haveI : Algebra.FormallyEtale (Tn θ 𝔪) (Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B) := .of_equiv E.symm
  -- `R̂ ⊗_{R̄} C ≅ Ĉ` is complete
  haveI : IsAdicComplete (𝔪h.map (algebraMap (Tn θ 𝔪) (Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B)))
      (Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B) := by
    rw [IsAdicComplete.map_algebraMap_iff, h𝔪h, IsAdicComplete.map_algebraMap_iff]
    haveI : IsAdicComplete I₀ (AdicCompletion I₀ (Cs θ R B)) := AdicCompletion.isAdicComplete fg
    exact isAdicComplete_of_linearEquiv I₀
      ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I₀ (Cs θ R B)).restrictScalars _)
  obtain ⟨m, ⟨Φ⟩⟩ := exists_algEquiv_pi_of_isSepClosed 𝔪h _ hρ (Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B)
  exact ⟨m, fun _ ↦ 1, fun _ ↦ one_pos, fun _ ↦ one_dvd _,
    ⟨Φ.trans (AlgEquiv.piCongrRight fun _ ↦ (adjoinLinEquiv _).symm)⟩⟩

end

end FormalKummer

end SemistableReduction
