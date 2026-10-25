/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerNode
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Unramified.Locus

/-!
# Transport of `IsKummerAt` along localizations and isomorphisms (MR12 T2 S4, Tate chart)

`IsKummerAt ϖ n u v F' 𝔪` (`KummerNode`) is a statement about an `N`-algebra `F'` and a prime `𝔪`
of `N`. For a ring map `N' → N` which is étale and an epimorphism in the sense that
`N₁ ⊗_{N'} F' = N₁ ⊗_N F'` (`TensorProduct.CompatibleSMul N' N N₁ F'`, e.g. a localization or an
isomorphism) it descends:

* **`IsKummerAt.comap_of_compatibleSMul`**: `IsKummerAt ϖ n (u) (v) F' 𝔪` over `N` for the images of
  `u, v ∈ N'` gives `IsKummerAt ϖ n u v F' (𝔪 ∩ N')` over `N'`;
* `IsKummerAt.comap_of_isLocalization`, `IsKummerAt.comap_of_bijective`: the two special cases.

The structure map `O → N₁` of the étale neighbourhood is only propositionally equal after
composing with `N' → N`; the predicate is therefore unbundled over this map
(`KummerAtData`, `isKummerAt_iff`) and transported along the equality of maps.

We also transport the hypotheses "integral closure" and "unramified at a prime" along a ring
isomorphism of the base (`isIntegralClosure_of_ringEquiv`, `isUnramifiedAt_of_ringEquiv`).
-/

universe u

open TensorProduct IsLocalRing

namespace SemistableReduction

section Data

variable {O : Type u} [CommRing O] (ϖ : O) (n : ℕ) {N : Type u} [CommRing N] (u v : N)
  (F' : Type u) [CommRing F'] [Algebra N F'] (N₁ : Type u) [CommRing N₁] [Algebra N N₁]
  (𝔫 : Ideal N₁)

/-- The data of `IsKummerAt` over a fixed étale neighbourhood `N₁ ⊇ 𝔫`, with the structure map
`f : O → N₁` as a variable. -/
def KummerAtData (f : O →+* N₁) : Prop :=
  letI : Algebra O N₁ := f.toAlgebra
  ∃ (u₁ v₁ : N₁) (huv : u₁ * v₁ = algebraMap O N₁ (ϖ ^ n)),
    (Node.lift u₁ v₁ huv).toRingHom.Etale ∧ u₁ ∈ 𝔫 ∧ v₁ ∈ 𝔫 ∧
    (∃ η η' : N₁, IsUnit η ∧ IsUnit η' ∧ u₁ = η * algebraMap N N₁ u ∧
      v₁ = η' * algebraMap N N₁ v) ∧
    ∃ (r : ℕ) (m d : Fin r → ℕ) (_ : ∀ i, 0 < d i) (hmd : ∀ i, m i * d i = n),
      Nonempty (N₁ ⊗[N] F' ≃ₐ[N₁] ∀ i, @KummerFactor O _ (ϖ ^ m i) (d i) N₁ _
        (nodeAlgebra N₁ (ϖ ^ m i) (d i) (by rw [← pow_mul, hmd i]; exact huv)))

variable {ϖ n u v F' N₁ 𝔫}

lemma KummerAtData.of_eq {f g : O →+* N₁} (hfg : f = g) (h : KummerAtData ϖ n u v F' N₁ 𝔫 f) :
    KummerAtData ϖ n u v F' N₁ 𝔫 g :=
  hfg ▸ h

variable (ϖ n u v F') in
lemma isKummerAt_iff [Algebra O N] (𝔪 : Ideal N) :
    IsKummerAt ϖ n u v F' 𝔪 ↔ ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : Algebra N N₁)
      (_ : Algebra.Etale N N₁) (𝔫 : Ideal N₁) (_ : 𝔫.IsPrime)
      (_ : 𝔫.comap (algebraMap N N₁) = 𝔪),
      KummerAtData ϖ n u v F' N₁ 𝔫 ((algebraMap N N₁).comp (algebraMap O N)) :=
  Iff.rfl

/-- Descent of the data along `N' → N` when `N₁ ⊗_{N'} F' = N₁ ⊗_N F'`. -/
lemma KummerAtData.comap {N' : Type u} [CommRing N'] [Algebra N' N] [Algebra N' F']
    [IsScalarTower N' N F'] [Algebra N' N₁] [IsScalarTower N' N N₁]
    [CompatibleSMul N' N N₁ F'] {u v : N'} {f : O →+* N₁}
    (h : KummerAtData ϖ n (algebraMap N' N u) (algebraMap N' N v) F' N₁ 𝔫 f) :
    KummerAtData ϖ n u v F' N₁ 𝔫 f := by
  obtain ⟨u₁, v₁, huv, het, hu, hv, ⟨η, η', h1, h2, h3, h4⟩, r, m, d, hd, hmd, ⟨Φ⟩⟩ := h
  refine ⟨u₁, v₁, huv, het, hu, hv, ⟨η, η', h1, h2, ?_, ?_⟩, r, m, d, hd, hmd,
    ⟨(Algebra.TensorProduct.equivOfCompatibleSMul N N' N₁ N₁ F').trans Φ⟩⟩
  · rw [h3, ← IsScalarTower.algebraMap_apply]
  · rw [h4, ← IsScalarTower.algebraMap_apply]

end Data

section Descent

variable {O : Type u} [CommRing O] {ϖ : O} {n : ℕ} {N' N : Type u} [CommRing N'] [CommRing N]
  [Algebra O N'] [Algebra O N] [Algebra N' N] [IsScalarTower O N' N] {u v : N'}
  {F' : Type u} [CommRing F'] [Algebra N F'] [Algebra N' F'] [IsScalarTower N' N F']
  {𝔪 : Ideal N}

/-- **Descent of `IsKummerAt` along an étale map `N' → N` with `N₁ ⊗_{N'} F' = N₁ ⊗_N F'`.** -/
theorem IsKummerAt.comap_of_compatibleSMul [Algebra.Etale N' N]
    (hc : ∀ (N₁ : Type u) [CommRing N₁] [Algebra N N₁] [Algebra N' N₁] [IsScalarTower N' N N₁],
      CompatibleSMul N' N N₁ F')
    (h : IsKummerAt ϖ n (algebraMap N' N u) (algebraMap N' N v) F' 𝔪) :
    IsKummerAt ϖ n u v F' (𝔪.comap (algebraMap N' N)) := by
  obtain ⟨N₁, _, _, _, 𝔫, _, h𝔫, h⟩ := (isKummerAt_iff ϖ n _ _ F' 𝔪).1 h
  letI : Algebra N' N₁ := ((algebraMap N N₁).comp (algebraMap N' N)).toAlgebra
  haveI : IsScalarTower N' N N₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI := hc N₁
  have hf : (algebraMap N N₁).comp (algebraMap O N) = (algebraMap N' N₁).comp (algebraMap O N') :=
    RingHom.ext fun x ↦ by
      change algebraMap N N₁ (algebraMap O N x) =
        algebraMap N N₁ (algebraMap N' N (algebraMap O N' x))
      rw [← IsScalarTower.algebraMap_apply O N' N]
  refine (isKummerAt_iff ϖ n u v F' _).2 ⟨N₁, inferInstance, inferInstance,
    Algebra.Etale.comp N' N N₁, 𝔫, inferInstance, ?_, (h.of_eq hf).comap⟩
  rw [IsScalarTower.algebraMap_eq N' N N₁, ← Ideal.comap_comap, h𝔫]

/-- **Descent of `IsKummerAt` along a localization `N' → N = M⁻¹ N'`** (étale, e.g. `N'[1/g]`). -/
theorem IsKummerAt.comap_of_isLocalization (M : Submonoid N') [IsLocalization M N]
    [Algebra.Etale N' N] (h : IsKummerAt ϖ n (algebraMap N' N u) (algebraMap N' N v) F' 𝔪) :
    IsKummerAt ϖ n u v F' (𝔪.comap (algebraMap N' N)) :=
  h.comap_of_compatibleSMul fun N₁ _ _ _ _ ↦
    IsLocalization.tensorProduct_compatibleSMul (A := N) M N₁ F'

/-- **Transport of `IsKummerAt` along an isomorphism `N' ≅ N`.** -/
theorem IsKummerAt.comap_of_bijective (hb : Function.Bijective (algebraMap N' N))
    (h : IsKummerAt ϖ n (algebraMap N' N u) (algebraMap N' N v) F' 𝔪) :
    IsKummerAt ϖ n u v F' (𝔪.comap (algebraMap N' N)) :=
  haveI : Algebra.Etale N' N := RingHom.etale_algebraMap.mp (RingHom.Etale.of_bijective hb)
  h.comap_of_compatibleSMul fun _ _ _ _ _ ↦ CompatibleSMul.of_algebraMap_surjective _ _ hb.2

end Descent

section BaseEquiv

variable {R R' B L : Type*} [CommRing R] [CommRing R'] [CommRing B] [CommRing L] [Algebra R B]
  [Algebra R' B] [Algebra B L] [Algebra R L] [Algebra R' L] [IsScalarTower R B L]
  [IsScalarTower R' B L] (e : R ≃+* R') (he : ∀ r, algebraMap R' B (e r) = algebraMap R B r)
include he

/-- The integral closure is unchanged by an isomorphism of the base compatible with `B`. -/
theorem isIntegralClosure_of_ringEquiv [IsIntegralClosure B R L] : IsIntegralClosure B R' L := by
  letI : Algebra R R' := e.toRingHom.toAlgebra
  haveI : IsScalarTower R R' L := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R B L, ← he, ← IsScalarTower.algebraMap_apply R' B L]
    rfl
  haveI : Algebra.IsIntegral R R' := ⟨RingHom.isIntegral_of_surjective _ e.surjective⟩
  refine ⟨IsIntegralClosure.algebraMap_injective B R L, fun {x} ↦ ⟨fun hx ↦
    (IsIntegralClosure.isIntegral_iff (R := R)).1 (isIntegral_trans (A := R') x hx), ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact IsIntegral.tower_top (A := R') (IsIntegralClosure.isIntegral R L y).algebraMap

/-- Unramifiedness at a prime is unchanged by an isomorphism of the base compatible with `B`. -/
theorem isUnramifiedAt_of_ringEquiv (Q : Ideal B) [Q.IsPrime] (h : Algebra.IsUnramifiedAt R Q) :
    Algebra.IsUnramifiedAt R' Q := by
  letI : Algebra R R' := e.toRingHom.toAlgebra
  haveI : IsScalarTower R R' (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime Q), ← he,
      ← IsScalarTower.algebraMap_apply R' B (Localization.AtPrime Q)]
    rfl
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime Q) := h
  exact Algebra.FormallyUnramified.of_restrictScalars R R' (Localization.AtPrime Q)

omit [Algebra B L] [Algebra R L] [Algebra R' L] [IsScalarTower R B L] [IsScalarTower R' B L] in
/-- The primes of `B` over the maximal ideal are unchanged by an isomorphism of local bases. -/
theorem comap_ne_maximalIdeal_of_ringEquiv [IsLocalRing R] [IsLocalRing R'] (Q : Ideal B)
    (h : Q.comap (algebraMap R B) ≠ maximalIdeal R) :
    Q.comap (algebraMap R' B) ≠ maximalIdeal R' := by
  intro h'
  apply h
  ext r
  have : algebraMap R B r = algebraMap R' B (e r) := (he r).symm
  rw [Ideal.mem_comap, this, ← Ideal.mem_comap, h', mem_maximalIdeal, mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

end BaseEquiv

end SemistableReduction
