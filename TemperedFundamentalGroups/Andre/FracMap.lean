/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral

/-!
# Maps of fraction fields of finite flat domains (Blueprint §10.3.6, item 4)

Let `f : B' →ₐ[R] B` be a map of domains which are finite and flat over `R` (e.g. the ring map
of a morphism of connected levels: finite étale `R`-algebras). Then

* `injective_of_flat_finite`: `f` is injective (minimal primes of `R` under flat maps; no
  strict inclusions of primes over the same prime of `R` under integral maps);
* `fracMap`: the induced map of fraction fields `L₂ = Frac B' → L₁ = Frac B`;
* `finiteDimensional_fracMap`: `L₁` is finite over `L₂` (`L₁` is the localization of `B` at
  the nonzero elements of `B'`, as `B` is integral over `B'`).
-/

open nonZeroDivisors

namespace TemperedFundamentalGroups

variable {R B' B : Type*} [CommRing R] [CommRing B'] [CommRing B] [Algebra R B'] [Algebra R B]

/-- The kernel of a flat map to a domain is a minimal prime: every prime below it is equal. -/
lemma comap_bot_le_of_flat [IsDomain B] [Module.Flat R B] (q : Ideal R) [q.IsPrime]
    (hq : q ≤ (⊥ : Ideal B).comap (algebraMap R B)) :
    (⊥ : Ideal B).comap (algebraMap R B) ≤ q := by
  haveI : ((⊥ : Ideal B).comap (algebraMap R B)).IsPrime := Ideal.comap_isPrime _ _
  haveI : (⊥ : Ideal B).LiesOver ((⊥ : Ideal B).comap (algebraMap R B)) := ⟨rfl⟩
  obtain ⟨P, hP, hPp, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (R := R) (p := q)
    (q := (⊥ : Ideal B).comap (algebraMap R B)) (⊥ : Ideal B) hq
  rw [le_bot_iff] at hP
  subst hP
  rw [hPl.over]

/-- **Maps of finite flat domains are injective.** -/
theorem injective_of_flat_finite [IsDomain B'] [IsDomain B] [Module.Flat R B'] [Module.Flat R B]
    [Algebra.IsIntegral R B'] (f : B' →ₐ[R] B) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  let P : Ideal B' := RingHom.ker f
  haveI : P.IsPrime := RingHom.ker_isPrime f
  have hcomap : P.comap (algebraMap R B') = (⊥ : Ideal B).comap (algebraMap R B) := by
    ext r
    simp [P, RingHom.mem_ker, f.commutes]
  have hle : (⊥ : Ideal B').comap (algebraMap R B') ≤ P.comap (algebraMap R B') :=
    Ideal.comap_mono bot_le
  haveI : ((⊥ : Ideal B').comap (algebraMap R B')).IsPrime := Ideal.comap_isPrime _ _
  have heq : (⊥ : Ideal B').comap (algebraMap R B') = P.comap (algebraMap R B') :=
    le_antisymm hle (hcomap ▸ comap_bot_le_of_flat _ (hcomap ▸ hle))
  have hP : P = ⊥ := by
    by_contra hne
    exact (Ideal.IsIntegral.comap_lt_comap (R := R) (lt_of_le_of_ne bot_le (Ne.symm hne))).ne
      heq
  intro a ha
  have : a ∈ P := ha
  rwa [hP, Ideal.mem_bot] at this

variable (L₂ L₁ : Type*) [Field L₂] [Field L₁] [Algebra B' L₂] [Algebra B L₁]
  [IsFractionRing B' L₂] [IsFractionRing B L₁]

variable [IsDomain B'] [IsDomain B] [Module.Flat R B'] [Module.Flat R B]
  [Algebra.IsIntegral R B']

/-- **The map of fraction fields** induced by a map of finite flat domains. -/
noncomputable def fracMap (f : B' →ₐ[R] B) : L₂ →+* L₁ :=
  IsFractionRing.lift (g := (algebraMap B L₁).comp (f : B' →+* B))
    ((IsFractionRing.injective B L₁).comp (injective_of_flat_finite f))

variable {L₂ L₁}

@[simp] lemma fracMap_algebraMap (f : B' →ₐ[R] B) (b : B') :
    fracMap L₂ L₁ f (algebraMap B' L₂ b) = algebraMap B L₁ (f b) :=
  IsFractionRing.lift_algebraMap _ _

variable (L₂ L₁) in
/-- **Finiteness of the extension of fraction fields.** -/
theorem finiteDimensional_fracMap [Module.Finite R B] (f : B' →ₐ[R] B) :
    letI := (fracMap L₂ L₁ f).toAlgebra
    FiniteDimensional L₂ L₁ := by
  letI : Algebra L₂ L₁ := (fracMap L₂ L₁ f).toAlgebra
  letI : Algebra B' B := (f : B' →+* B).toAlgebra
  letI : Algebra B' L₁ := ((algebraMap B L₁).comp (f : B' →+* B)).toAlgebra
  haveI : IsScalarTower B' B L₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B' L₂ L₁ := IsScalarTower.of_algebraMap_eq fun b =>
    (fracMap_algebraMap f b).symm
  haveI : IsScalarTower R B' B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  haveI : Module.Finite B' B := Module.Finite.of_restrictScalars_finite R B' B
  haveI : Algebra.IsIntegral B' B := inferInstance
  have hf := injective_of_flat_finite f
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B B'⁰) L₁ := by
    refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, s, hs, rfl⟩
      refine isUnit_iff_ne_zero.2 ?_
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective B L₁)]
      change f s ≠ 0
      rw [Ne, map_eq_zero_iff _ hf]
      exact nonZeroDivisors.ne_zero hs
    · obtain ⟨b₁, ⟨b₂, hb₂⟩, rfl⟩ := IsLocalization.exists_mk'_eq B⁰ z
      have hb₂0 : b₂ ≠ 0 := nonZeroDivisors.ne_zero hb₂
      have hI : (Ideal.span {b₂}).comap (algebraMap B' B) ≠ ⊥ :=
        Ideal.comap_ne_bot_of_integral_mem hb₂0 (Ideal.mem_span_singleton_self b₂)
          (Algebra.IsIntegral.isIntegral b₂)
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hs)
      refine ⟨⟨b₁ * c, ⟨algebraMap B' B s, s, mem_nonZeroDivisors_of_ne_zero hs0, rfl⟩⟩, ?_⟩
      change IsLocalization.mk' L₁ b₁ ⟨b₂, hb₂⟩ * algebraMap B L₁ (algebraMap B' B s) =
        algebraMap B L₁ (b₁ * c)
      rw [← hc, map_mul, mul_comm (algebraMap B L₁ c), ← mul_assoc, IsLocalization.mk'_spec,
        ← map_mul]
    · simp only [OneMemClass.coe_one, one_mul]
      exact IsFractionRing.injective B L₁ h
  exact Module.Finite.of_isLocalization B' B B'⁰

end TemperedFundamentalGroups
