/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalCuspEtale

/-!
# The formal cusp form at a point where the special fibre is étale

Variant of `FormalKummer.pointCuspForm_of_etale` with the étaleness hypothesis only on the special
fibre: if `C = B/JB` is étale over `R̄ = R/J` on a basic open `D(f̄) ∋ 𝔪̄`, i.e.
`R̄_f̄ → C_f̄` is étale (the output shape of `PurityLocal.etale_quot_awayMap` with `I = J`), then
(**`pointCuspForm_of_etale_special`**) `R̂_𝔪 ⊗_{R̄} C ≅ R̂_𝔪ʳ`, i.e. `PointCuspForm s 1 𝔪`.

Proof: `R̂_𝔪 ⊗_{R̄} C ≅ R̂_𝔪 ⊗_{R̄} C_f̄` (`tensorAwayEquiv`, `f̄` is a unit in `R̂_𝔪`) is finite
and formally étale over `R̂_𝔪`, complete (it is the completion of `C`), hence split
(`exists_algEquiv_pi_of_isSepClosed`).
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

open AdmissibleLift Cusp

namespace FormalKummer

noncomputable section

/-- An étale `awayMap` `A_g → C_g` makes `C_g` formally étale over `A`. -/
theorem formallyEtale_of_awayMap_etale {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    {g : A} (h : (Localization.awayMap (algebraMap A C) g).Etale) :
    Algebra.FormallyEtale A (Localization.Away (algebraMap A C g)) := by
  letI := (Localization.awayMap (algebraMap A C) g).toAlgebra
  haveI : Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A C g)) := h
  haveI : IsScalarTower A (Localization.Away g) (Localization.Away (algebraMap A C g)) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      unfold Localization.awayMap IsLocalization.Away.map
      rw [IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply]
  exact .comp A (Localization.Away g) _

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]

/-- **The local formal form at a point where the special fibre is étale**: if `C = B/JB` is
finite over the Noetherian `R̄` and `R̄_f̄ → C_f̄` is étale for some `f ∉ 𝔪`, `𝔪` a `k`-rational
point (`k` separably closed), then `R̂_𝔪 ⊗_{R̄} C ≅ R̂_𝔪ʳ`, i.e. the local formal cusp form holds
with all `dᵢ = 1`, for any `s`. -/
theorem pointCuspForm_of_etale_special [IsSepClosed k] [IsNoetherianRing R]
    [Module.Finite (Rs θ R) (Cs θ R B)]
    (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
    {f : R} (hf : f ∉ 𝔪)
    (het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B))
      (Ideal.Quotient.mk _ f)).Etale)
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
  -- `f̄` is a unit in the completion
  haveI := isLocalRing_of_isAdicComplete_maximal 𝔪h
  have hfu : IsUnit (algebraMap (Rs θ R) (Tn θ 𝔪) (Ideal.Quotient.mk _ f)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.eq_maximalIdeal ‹𝔪h.IsMaximal›, hmem,
      hev, Ideal.Quotient.eq_zero_iff_mem, hI₀, sIdeal, Ideal.mem_quotient_iff_mem hJ]
    exact hf
  -- `R̂ ⊗_{R̄} C` is finite étale over `R̂`
  haveI := formallyEtale_of_awayMap_etale het
  let E := tensorAwayEquiv (S := Tn θ 𝔪) (B := Cs θ R B) _ hfu
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
