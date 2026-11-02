/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.PurityLocal

/-!
# Maps out of an unramified point agreeing modulo an ideal (MR12, interface I3, injectivity)

Let `f g : B → C` be `A`-algebra maps, `N ⊆ C` a prime with `C_N` noetherian, `M = f⁻¹ N` and
`I ⊆ N` an ideal with `f b - g b ∈ I` for all `b`. If `B` is unramified over `A` at `M`
(`Algebra.FormallyUnramified A B_M`), then `f` and `g` agree in `C_N`
(**`UnramifiedHomExt.algebraMap_eq_of_sub_mem`**): both extend to `B_M → C_N`, agree modulo
`I C_N`, hence modulo every power of `I C_N` (formal unramifiedness,
`Algebra.FormallyUnramified.ext_of_iInf`), and `⋂ₙ (I C_N)ⁿ = 0` (Krull). If `C` is a domain,
`f = g` (**`UnramifiedHomExt.eq_of_sub_mem`**).

**`UnramifiedHomExt.eq_of_normalisation_sub_mem`**: for normalisations `B`, `B'` of a noetherian
normal domain `A` in finite separable extensions `L`, `L'` of `K = Frac A`, two `K`-algebra maps
`f g : L → L'` whose maps of normalisations agree modulo `I₀ B'` are equal, provided `I₀` lies in
a regular closed point `P` (regular pair `x, y`) over which `B` is unramified in codimension one
(`hunr`): then `B` is étale over `A` at every point over `P` (purity, `PurityLocal.isEtaleAt'`).
-/

universe u

namespace SemistableReduction

namespace UnramifiedHomExt

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  (M : Ideal B) [M.IsPrime] (N : Ideal C) [N.IsPrime] (I : Ideal C) (hIN : I ≤ N)
  {f g : B →ₐ[A] C} (hfM : N.comap (f : B →+* C) = M) (hfg : ∀ b, f b - g b ∈ I)

include hfM in
lemma isUnit_f (y : M.primeCompl) :
    IsUnit ((IsScalarTower.toAlgHom A C (Localization.AtPrime N)).comp f y) := by
  refine IsLocalization.map_units (Localization.AtPrime N) (⟨f y, fun h ↦ y.2 ?_⟩ : N.primeCompl)
  have : (y : B) ∈ N.comap (f : B →+* C) := h
  rwa [hfM] at this

include hfM hfg hIN in
lemma isUnit_g (y : M.primeCompl) :
    IsUnit ((IsScalarTower.toAlgHom A C (Localization.AtPrime N)).comp g y) := by
  refine IsLocalization.map_units (Localization.AtPrime N) (⟨g y, fun h ↦ y.2 ?_⟩ : N.primeCompl)
  have h' := N.add_mem (hIN (hfg y)) h
  rw [sub_add_cancel] at h'
  have : (y : B) ∈ N.comap (f : B →+* C) := h'
  rwa [hfM] at this

include hIN hfM hfg in
/-- **Maps out of an unramified point agreeing modulo `I` agree in `C_N`.** -/
theorem algebraMap_eq_of_sub_mem [Algebra.FormallyUnramified A (Localization.AtPrime M)]
    [IsNoetherianRing (Localization.AtPrime N)] (b : B) :
    algebraMap C (Localization.AtPrime N) (f b) = algebraMap C (Localization.AtPrime N) (g b) := by
  set I' := I.map (algebraMap C (Localization.AtPrime N))
  have hI' : I' ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := IsLocalRing.maximalIdeal _) Ideal.IsPrime.ne_top' ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hIN
  have hext := Algebra.FormallyUnramified.ext_of_iInf (I := I')
    (Ideal.iInf_pow_eq_bot_of_isLocalRing I' hI')
    (g₁ := IsLocalization.liftAlgHom (M := M.primeCompl) (S := Localization.AtPrime M)
      (isUnit_f M N hfM))
    (g₂ := IsLocalization.liftAlgHom (M := M.primeCompl) (S := Localization.AtPrime M)
      (isUnit_g M N I hIN hfM hfg)) (fun x ↦ by
      have h : (Ideal.Quotient.mk I').comp
          (IsLocalization.lift (S := Localization.AtPrime M) (isUnit_f M N hfM)) =
          (Ideal.Quotient.mk I').comp (IsLocalization.lift (S := Localization.AtPrime M)
            (isUnit_g M N I hIN hfM hfg)) :=
        IsLocalization.ringHom_ext M.primeCompl (RingHom.ext fun b ↦ by
          simp only [RingHom.comp_apply, IsLocalization.lift_eq]
          rw [Ideal.Quotient.eq]
          change algebraMap C (Localization.AtPrime N) (f b) -
            algebraMap C (Localization.AtPrime N) (g b) ∈ I'
          rw [← map_sub]
          exact Ideal.mem_map_of_mem _ (hfg b))
      exact RingHom.congr_fun h x)
  have := AlgHom.congr_fun hext (algebraMap B (Localization.AtPrime M) b)
  simpa [IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq] using this

include hIN hfM hfg in
/-- **Maps into a domain out of an unramified point agreeing modulo `I` are equal.** -/
theorem eq_of_sub_mem [IsDomain C] [Algebra.FormallyUnramified A (Localization.AtPrime M)]
    [IsNoetherianRing (Localization.AtPrime N)] : f = g :=
  AlgHom.ext fun b ↦ IsLocalization.injective (Localization.AtPrime N)
    N.primeCompl_le_nonZeroDivisors (algebraMap_eq_of_sub_mem M N I hIN hfM hfg b)

section Normalisation

open IsLocalRing

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
  {L L' : Type u} [Field L] [Field L'] [Algebra K L] [Algebra K L'] [Algebra A L] [Algebra A L']
  [IsScalarTower A K L] [IsScalarTower A K L'] [FiniteDimensional K L] [FiniteDimensional K L']
  [Algebra.IsSeparable K L] [Algebra.IsSeparable K L']
  (B B' : Type u) [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] [Algebra B L]
  [Algebra B' L'] [IsScalarTower A B L] [IsScalarTower A B' L'] [IsIntegralClosure B A L]
  [IsIntegralClosure B' A L']

include K in
/-- **Faithfulness of reduction on normalisations**: `K`-algebra maps `f g : L → L'` whose maps
of normalisations `f₁ g₁ : B → B'` agree modulo `I₀ B'`, `I₀ ⊆ P` for a regular closed point `P`
of `A` over which `B` is unramified in codimension one, are equal. -/
theorem eq_of_normalisation_sub_mem (P : Ideal A) [P.IsMaximal] {x y : Localization.AtPrime P}
    (hx : Prime x) (hy : y ∉ Ideal.span {x})
    (hm : maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) < P →
      Algebra.IsUnramifiedAt A Q)
    (I₀ : Ideal A) (hI₀ : I₀ ≤ P) {f g : L →ₐ[K] L'} (f₁ g₁ : B →+* B')
    (hf₁ : ∀ b, algebraMap B' L' (f₁ b) = f (algebraMap B L b))
    (hg₁ : ∀ b, algebraMap B' L' (g₁ b) = g (algebraMap B L b))
    (hfg : ∀ b, f₁ b - g₁ b ∈ I₀.map (algebraMap A B')) : f = g := by
  have hA : ∀ (h : L →ₐ[K] L') (a : A), h (algebraMap A L a) = algebraMap A L' a := fun h a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, h.commutes, ← IsScalarTower.algebraMap_apply]
  have hcomm : ∀ (h : L →ₐ[K] L') (h₁ : B →+* B'),
      (∀ b, algebraMap B' L' (h₁ b) = h (algebraMap B L b)) →
        ∀ a, h₁ (algebraMap A B a) = algebraMap A B' a := fun h h₁ hh a ↦
    IsIntegralClosure.algebraMap_injective B' A L' (by
      rw [hh, ← IsScalarTower.algebraMap_apply, hA, IsScalarTower.algebraMap_apply A B' L'])
  let f₁A : B →ₐ[A] B' := { f₁ with commutes' := hcomm f f₁ hf₁ }
  let g₁A : B →ₐ[A] B' := { g₁ with commutes' := hcomm g g₁ hg₁ }
  haveI : Algebra.IsIntegral A B' := IsIntegralClosure.isIntegral_algebra A L'
  have hinj : Function.Injective (algebraMap A B') := by
    refine fun a a' h ↦ IsFractionRing.injective A K ((algebraMap K L').injective ?_)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A B' L', h, ← IsScalarTower.algebraMap_apply]
  obtain ⟨N, -, hN, hNP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal B')
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI := hN
  set M := N.comap (f₁A : B →+* B')
  have hM : M.comap (algebraMap A B) = P := by
    rw [Ideal.comap_comap, ← hNP]
    congr 1
    exact RingHom.ext fun a ↦ f₁A.commutes a
  haveI : Algebra.IsEtaleAt A M := PurityLocal.isEtaleAt' K (L := L) P hx hy hm B hunr M hM
  haveI : Module.Finite A B' := IsIntegralClosure.finite A K L' B'
  haveI : IsNoetherianRing B' := isNoetherian_of_tower A inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime N) :=
    IsLocalization.isNoetherianRing N.primeCompl _ inferInstance
  haveI : IsDomain B' :=
    (IsIntegralClosure.equiv A B' L' (integralClosure A L')).toMulEquiv.isDomain
      (integralClosure A L')
  have hle : I₀.map (algebraMap A B') ≤ N :=
    Ideal.map_le_iff_le_comap.2 (hI₀.trans hNP.ge)
  have h₁ : f₁A = g₁A := eq_of_sub_mem M N _ hle (f := f₁A) (g := g₁A) rfl hfg
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI := IsIntegralClosure.isLocalization A K L B
  refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (RingHom.ext fun b ↦ ?_))
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.coe_toRingHom, ← hf₁,
    ← hg₁]
  exact congrArg (algebraMap B' L') (AlgHom.congr_fun h₁ b)

end Normalisation

end UnramifiedHomExt

end SemistableReduction
