/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerFactor
import TemperedFundamentalGroups.SemistableReduction.NodeBaseChange
import TemperedFundamentalGroups.SemistableReduction.TensorQuotTensor

/-!
# Kummer factors over a base flat modulo an ideal (Blueprint §12.8, M2.3, levels)

At the finite levels `O_n = O/ϖⁿ⁺¹` of a model over a DVR `O`, the formal neighbourhood `S` of
the nodes is killed by `I = (ϖⁿ⁺¹)`, so it is never flat over the node ring
`A = O[u,v]/(uv − π^e)` of the DVR; it is flat over the reduced node ring
`A_I = (O/I)[u,v]/(uv − π̄^e)`. All lift data of the levels must however live over the same `O`
(they share the deformation parameters `π_j`). This file shows that the Kummer factor
`S ⊗_A B` only depends on `S` as an `A_I`-algebra:

* **`KummerFactorQuot.equiv`**: `S ⊗_A B ≃ S ⊗_{A_I} B_I` (`B_I = (O/I)[s,t]/(st − π̄)`) for an
  `A_I`-algebra `S` (via `TensorQuotTensor.equiv`, the kernel `I·(S ⊗_A B)` being zero), with
  `equiv_tmul`;
* `KummerFactorQuot.eq_zero_of_mul_eq_zero`, **`flat_localization`**: the results of
  `KummerFactor` for `S` flat over `A_I` only.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace KummerFactorQuot

open KummerEtale

noncomputable section

variable {O : Type u} [CommRing O] (I : Ideal O) (π : O) {e : ℕ}

/-- The deformation parameter modulo `I`. -/
abbrev πI : O ⧸ I := Ideal.Quotient.mk I π

lemma hpow : Ideal.Quotient.mk I (π ^ e) = πI I π ^ e := map_pow _ _ _

/-- The reduction of the node ring `A → A_I`. -/
abbrev redA : A π e →+* A (πI I π) e := Node.baseMap (Ideal.Quotient.mk I) (hpow I π)

/-- The reduction of the Kummer algebra `B → B_I`. -/
abbrev redB : B π →+* B (πI I π) := Node.baseMap (Ideal.Quotient.mk I) rfl

/-- The ideal `I A` of the node ring. -/
abbrev K : Ideal (A π e) := I.map (algebraMap O (A π e))

variable (S : Type u) [CommRing S] [Algebra (A π e) S] [Algebra (A (πI I π) e) S]
  (hg : (algebraMap (A (πI I π) e) S).comp (redA I π) = algebraMap (A π e) S)

include hg in
lemma algebraMap_K {a : A π e} (ha : a ∈ K I π (e := e)) : algebraMap (A π e) S a = 0 := by
  have h : K I π (e := e) ≤ RingHom.ker (algebraMap (A π e) S) := by
    rw [K, Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hg, RingHom.comp_apply, Node.baseMap_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.mpr hi, map_zero, map_zero]
  exact h ha

include hg in
lemma map_K_S : (K I π (e := e)).map (algebraMap (A π e) S) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  exact fun a ha ↦ algebraMap_K I π S hg ha

include hg in
lemma KT_eq_bot : TensorQuotTensor.KT (K I π (e := e)) (S := S) (B := B π) = ⊥ := by
  rw [TensorQuotTensor.KT, Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  rw [RingHom.mem_ker, Algebra.TensorProduct.algebraMap_apply, algebraMap_K I π S hg ha,
    TensorProduct.zero_tmul]

/-- `A → A_I` (reduction). -/
abbrev algAA : Algebra (A π e) (A (πI I π) e) := (redA I π).toAlgebra

/-- `A → B_I` through the reduction. -/
abbrev algAB : Algebra (A π e) (B (πI I π)) :=
  ((algebraMap (A (πI I π) e) (B (πI I π))).comp (redA I π)).toAlgebra

/-- The reduction `B → B_I` as an `A`-algebra map. -/
def βₐ : letI := algAB (e := e) I π; B π →ₐ[A π e] B (πI I π) :=
  letI := algAB (e := e) I π
  { redB I π with
    commutes' := fun a ↦
      RingHom.congr_fun (Node.baseMap_comp_kummer (Ideal.Quotient.mk I) (c := π) rfl e) a }

/-- **`S ⊗_A B ≃ S ⊗_{A_I} B_I`** for an `A_I`-algebra `S`. -/
def equiv : S ⊗[A π e] B π ≃+* S ⊗[A (πI I π) e] B (πI I π) :=
  letI := algAA (e := e) I π
  letI := algAB (e := e) I π
  haveI : IsScalarTower (A π e) (A (πI I π) e) S :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (RingHom.congr_fun hg a).symm
  haveI : IsScalarTower (A π e) (A (πI I π) e) (B (πI I π)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (RingEquiv.quotientBot _).symm.trans <|
    (Ideal.quotEquivOfEq (KT_eq_bot I π S hg).symm).trans <|
      TensorQuotTensor.equiv (σ := AlgHom.id (A π e) S) (β := βₐ I π) (K I π (e := e))
        (by
          change RingHom.ker (redA (e := e) I π) = _
          rw [Node.ker_baseMap (hpow I π) Ideal.Quotient.mk_surjective, Ideal.mk_ker])
        (Node.surjective_baseMap (hpow I π) Ideal.Quotient.mk_surjective) Function.surjective_id
        (Node.surjective_baseMap (θ := Ideal.Quotient.mk I) (a := π) rfl
          Ideal.Quotient.mk_surjective)
        (by
          change RingHom.ker (RingHom.id S) = _
          rw [map_K_S I π S hg, RingHom.ker_eq_bot_iff_eq_zero]
          exact fun _ h ↦ h)
        (by
          change RingHom.ker (redB I π) = _
          rw [Node.ker_baseMap (θ := Ideal.Quotient.mk I) (a := π) rfl Ideal.Quotient.mk_surjective,
            Ideal.mk_ker, K, Ideal.map_map,
            ← IsScalarTower.algebraMap_eq])

lemma equiv_tmul (s : S) (b : B π) :
    equiv I π S hg (s ⊗ₜ b) = s ⊗ₜ[A (πI I π) e] redB I π b := by
  letI := algAA (e := e) I π
  letI := algAB (e := e) I π
  haveI : IsScalarTower (A π e) (A (πI I π) e) S :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (RingHom.congr_fun hg a).symm
  haveI : IsScalarTower (A π e) (A (πI I π) e) (B (πI I π)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [equiv, RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.quotientBot_symm_mk,
    Ideal.quotEquivOfEq_mk]
  exact TensorQuotTensor.equiv_mk_tmul (A' := A (πI I π) e) (S' := S) (B' := B (πI I π))
    (σ := AlgHom.id (A π e) S) (β := βₐ I π) ..

lemma redA_fA : redA I π (fA π (e := e)) = fA (πI I π) := by
  simp only [fA, map_add, Node.baseMap_u, Node.baseMap_v]

lemma equiv_fA : equiv I π S hg (algebraMap (A π e) (S ⊗[A π e] B π) (fA π)) =
    algebraMap (A (πI I π) e) (S ⊗[A (πI I π) e] B (πI I π)) (fA (πI I π)) := by
  rw [KummerFactor.algebraMap_fA, KummerFactor.algebraMap_fA, equiv_tmul]
  have h1 := RingHom.congr_fun (Node.baseMap_comp_kummer (Ideal.Quotient.mk I) (c := π) rfl e)
    (fA π)
  exact congrArg _ (h1.trans (congrArg (Node.kummer (πI I π) e).toRingHom (redA_fA I π)))

lemma equiv_algebraMap (s : S) :
    equiv I π S hg (algebraMap S (S ⊗[A π e] B π) s) =
      algebraMap S (S ⊗[A (πI I π) e] B (πI I π)) s := by
  change equiv I π S hg (s ⊗ₜ 1) = s ⊗ₜ 1
  rw [equiv_tmul, map_one]

include hg in
/-- **`u + v` is a nonzerodivisor on `S ⊗_A B`** for `S` flat over the reduced node ring. -/
theorem eq_zero_of_mul_eq_zero (he : 0 < e) [Module.Flat (A (πI I π) e) S] (z : S ⊗[A π e] B π)
    (hz : algebraMap (A π e) (S ⊗[A π e] B π) (fA π) * z = 0) : z = 0 := by
  have h := congrArg (equiv I π S hg) hz
  rw [map_mul, equiv_fA, map_zero] at h
  exact (equiv I π S hg).injective
    ((KummerFactor.eq_zero_of_mul_eq_zero (πI I π) S he _ h).trans (map_zero _).symm)

include hg in
/-- **A Kummer factor is flat over its base away from the node**, for `S` flat over the reduced
node ring (`e` invertible). -/
theorem flat_localization (he : 0 < e) (heu : IsUnit (e : O)) [Module.Flat (A (πI I π) e) S] :
    Module.Flat S (Localization.Away (algebraMap (A π e) (S ⊗[A π e] B π) (fA π))) := by
  have heu' : IsUnit (e : O ⧸ I) := by
    simpa only [map_natCast] using heu.map (Ideal.Quotient.mk I)
  haveI := KummerFactor.flat_localization (πI I π) (S := S) he heu'
  let Φ : S ⊗[A π e] B π ≃ₐ[S] S ⊗[A (πI I π) e] B (πI I π) :=
    AlgEquiv.ofRingEquiv (f := equiv I π S hg) (equiv_algebraMap I π S hg)
  have hM : Submonoid.map Φ (Submonoid.powers
      (algebraMap (A π e) (S ⊗[A π e] B π) (fA π))) =
      Submonoid.powers (algebraMap (A (πI I π) e) (S ⊗[A (πI I π) e] B (πI I π))
        (fA (πI I π))) := by
    rw [Submonoid.map_powers]
    congr 1
    exact equiv_fA I π S hg
  let Ψ := IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (algebraMap (A π e) (S ⊗[A π e] B π) (fA π)))
    (Localization.Away (algebraMap (A (πI I π) e) (S ⊗[A (πI I π) e] B (πI I π))
      (fA (πI I π)))) Φ hM
  exact Module.Flat.of_linearEquiv Ψ.toLinearEquiv

/-! ### Flatness modulo `I` -/

variable {π} in
/-- **Node coordinates flat modulo `I`**: `χ : A → T` factors through the reduced node ring
`A_I` by a flat map. -/
def KFlat {T : Type u} [CommRing T] (χ : A π e →+* T) : Prop :=
  ∃ g : A (πI I π) e →+* T, g.Flat ∧ g.comp (redA I π) = χ

lemma bijective_redA_bot : Function.Bijective (redA (e := e) (⊥ : Ideal O) π) := by
  refine ⟨?_, Node.surjective_baseMap _ Ideal.Quotient.mk_surjective⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h : a ∈ RingHom.ker (redA (e := e) (⊥ : Ideal O) π) := ha
  rwa [Node.ker_baseMap _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, Ideal.map_bot] at h

variable {π} in
/-- Flat node coordinates are flat modulo `⊥`. -/
theorem KFlat.of_flat {T : Type u} [CommRing T] {χ : A π e →+* T} (hχ : χ.Flat) :
    KFlat (⊥ : Ideal O) χ := by
  let E := RingEquiv.ofBijective _ (bijective_redA_bot (e := e) π)
  refine ⟨χ.comp E.symm.toRingHom,
    RingHom.Flat.comp (RingHom.Flat.of_bijective E.symm.bijective) hχ, ?_⟩
  refine RingHom.ext fun a ↦ ?_
  change χ (E.symm (E a)) = χ a
  rw [RingEquiv.symm_apply_apply]

end

end KummerFactorQuot

end SemistableReduction
