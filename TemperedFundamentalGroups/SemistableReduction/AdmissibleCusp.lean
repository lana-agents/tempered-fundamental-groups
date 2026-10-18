/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdjoinRoot
import TemperedFundamentalGroups.SemistableReduction.AdmissiblePatch

/-!
# Lifting the cusp factors of an admissible covering (Blueprint §12.8, M2.3, marked points)

An admissible covering (`Admissible.Covering`) is tamely ramified over the marked points
([Mzk1] §3.9, (1′A)): its formal local model there is the **cusp factor**
`(R̂'/(1 − δ))[t']/(t'^e − t)` (`Admissible.CuspPiece`), `t = ψ(X)` the formal coordinate at the
marked points. In the setting of `AdmissibleLift` (level ring `O`, residue map `θ`, chart `R`,
`J = (ker θ) R`, `ψ : R̂ → R̂' = (R/J)^∧`) the **lifted cusp factor** is
`CPiece δ̃ t̃ e = (R̂/(1 − δ̃))[X]/(X^e − t̃)` for a lift `t̃` of `t` and an idempotent lift `δ̃`
of `δ`:

* `AdmissibleLift.cuspEquiv`: modulo `J` it is the cusp factor of the covering
  (Mathlib `AdjoinRoot.quotEquivQuotMap`, and `R̂/(1 − δ̃)` modulo `J` is `R̂'/(1 − δ)`,
  `ker_σc`), compatibly with `R̂ → R̂'` (`cuspEquiv_algebraMap`);
* it is free over `R̂/(1 − δ̃)` (monic), hence finite over `R̂` (`finite_CPiece`) and its
  localization at `f` is flat over `R̂` (`flat_loc_CPiece`);
* `f` is a nonzerodivisor on it if `f` is one on `R̂` (`noTorsion_CPiece`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace AdmissibleLift

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  {R : Type u} [CommRing R] [Algebra O R] (f : R)

/-- The base `R̂/(1 − δ̃)` of a lifted cusp factor. -/
abbrev CBase (δ : FormalPatchLevel.Hat f) : Type u := FormalPatchLevel.Hat f ⧸ Ideal.span {1 - δ}

/-- The polynomial `X^e − t̃` over `R̂/(1 − δ̃)`. -/
abbrev cpoly (δ t : FormalPatchLevel.Hat f) (e : ℕ) : (CBase f δ)[X] :=
  X ^ e - C (Ideal.Quotient.mk _ t)

/-- **The lifted cusp factor** `(R̂/(1 − δ̃))[X]/(X^e − t̃)`. -/
abbrev CPiece (δ t : FormalPatchLevel.Hat f) (e : ℕ) : Type u := AdjoinRoot (cpoly f δ t e)

/-! ### Reduction of the base -/

section Base

variable (δ : FormalPatchLevel.Hat f) (δb : Admissible.Hat (fbar θ f)) (hδ : ψ θ f δ = δb)

/-- `σc : R̂/(1 − δ̃) → R̂'/(1 − δ)`, induced by `ψ`. -/
def σc : CBase f δ →+* Admissible.Hat (fbar θ f) ⧸ Ideal.span {1 - δb} :=
  Ideal.quotientMap (Ideal.span {1 - δb}) (ψ θ f).toRingHom (span_le_comap θ f δ δb hδ)

lemma σc_mk (x : FormalPatchLevel.Hat f) :
    σc θ f δ δb hδ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ψ θ f x) :=
  Ideal.quotientMap_mk

lemma surjective_σc : Function.Surjective (σc θ f δ δb hδ) :=
  Ideal.quotientMap_surjective (surjective_ψ θ f)

/-- **The kernel of `σc` is `J·R̂/(1 − δ̃)`.** -/
lemma ker_σc [IsNoetherianRing R] :
    RingHom.ker (σc θ f δ δb hδ) = (J θ).map (algebraMap R (CBase f δ)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, σc_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, rfl⟩ := surjective_ψ θ f z
    have hker : y - w * (1 - δ) ∈ RingHom.ker (ψ θ f) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_sub, map_one, hδ, hz, sub_self]
    rw [ker_ψ] at hker
    have heq : (Ideal.Quotient.mk (Ideal.span {1 - δ}) y : CBase f δ) =
        Ideal.Quotient.mk (Ideal.span {1 - δ}) (y - w * (1 - δ)) := by
      have h1 : (Ideal.Quotient.mk (Ideal.span {1 - δ}) (1 - δ) : CBase f δ) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [map_sub, map_mul, h1, mul_zero, sub_zero]
    rw [heq]
    have hmap : ((J θ).map (algebraMap R (FormalPatchLevel.Hat f))).map
        (Ideal.Quotient.mk (Ideal.span {1 - δ})) = (J θ).map (algebraMap R (CBase f δ)) := by
      rw [Ideal.map_map]
      rfl
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hker
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change σc θ f δ δb hδ (Ideal.Quotient.mk _ (algebraMap R _ r)) = 0
    rw [σc_mk, ψ_algebraMap_J θ f hr, map_zero]

/-- `(R̂/(1 − δ̃))/J ≃ R̂'/(1 − δ)`. -/
def τ [IsNoetherianRing R] :
    (CBase f δ ⧸ (J θ).map (algebraMap R (CBase f δ))) ≃+*
      Admissible.Hat (fbar θ f) ⧸ Ideal.span {1 - δb} :=
  (Ideal.quotEquivOfEq (ker_σc θ f δ δb hδ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_σc θ f δ δb hδ))

lemma τ_mk [IsNoetherianRing R] (x : FormalPatchLevel.Hat f) :
    τ θ f δ δb hδ (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) =
      Ideal.Quotient.mk _ (ψ θ f x) := by
  rw [τ, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, σc_mk]

end Base

/-! ### The reduction equivalence of a cusp factor -/

section Reduction

variable [Algebra k (R ⧸ J θ)] (ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f))
  (δ t : FormalPatchLevel.Hat f) (δb : Admissible.Hat (fbar θ f)) (hδ : ψ θ f δ = δb)
  (ht : ψ θ f t = ψc X) (e : ℕ)

/-- The ideal `J·(R̂/(1 − δ̃))`. -/
abbrev Jb : Ideal (CBase f δ) := (J θ).map (algebraMap R (CBase f δ))

/-- The ideal `J·CPiece`, through `R̂`. -/
abbrev JC : Ideal (CPiece f δ t e) :=
  (J θ).map ((algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e)).comp
    (algebraMap R (FormalPatchLevel.Hat f)))

omit [Algebra k (R ⧸ J θ)] in
lemma JC_eq : JC θ f δ t e = (Jb θ f δ).map (AdjoinRoot.of (cpoly f δ t e)) := by
  simp only [JC, Jb, J, Ideal.map_map]
  rfl

include ht in
lemma map_cpoly [IsNoetherianRing R] :
    Polynomial.mapEquiv (τ θ f δ δb hδ) ((cpoly f δ t e).map (Ideal.Quotient.mk (Jb θ f δ))) =
      X ^ e - C (Ideal.Quotient.mk (Ideal.span {1 - δb}) (ψc X)) := by
  rw [Polynomial.mapEquiv_apply, Polynomial.map_map, cpoly, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, RingHom.comp_apply,
    RingEquiv.coe_toRingHom, τ_mk, ht]

/-- **The reduction of a lifted cusp factor**: `CPiece/J ≃ (R̂'/(1 − δ))[X]/(X^e − t)`. -/
def cuspEquiv [IsNoetherianRing R] :
    (CPiece f δ t e ⧸ JC θ f δ t e) ≃+* Admissible.CuspPiece ψc δb e :=
  (Ideal.quotEquivOfEq (JC_eq θ f δ t e)).trans
    ((AdjoinRoot.quotEquivQuotMap (cpoly f δ t e) (Jb θ f δ)).toRingEquiv.trans
      (Ideal.quotientEquiv _ _ (Polynomial.mapEquiv (τ θ f δ δb hδ)) (by
        rw [Ideal.map_span, Set.image_singleton]
        exact congrArg (fun p ↦ Ideal.span {p}) (map_cpoly θ f ψc δ t δb hδ ht e).symm)))

lemma cuspEquiv_algebraMap [IsNoetherianRing R] (x : FormalPatchLevel.Hat f) :
    cuspEquiv θ f ψc δ t δb hδ ht e
        (Ideal.Quotient.mk _ (algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) x)) =
      algebraMap (Admissible.Hat (fbar θ f)) (Admissible.CuspPiece ψc δb e) (ψ θ f x) := by
  have h1 : algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) x =
      AdjoinRoot.mk (cpoly f δ t e) (C (Ideal.Quotient.mk _ x)) := rfl
  rw [cuspEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, h1, Ideal.quotEquivOfEq_mk,
    AlgEquiv.coe_ringEquiv, AdjoinRoot.quotEquivQuotMap_apply_mk]
  erw [Ideal.quotientEquiv_mk]
  rw [Polynomial.map_C, Polynomial.mapEquiv_apply, Polynomial.map_C]
  simp only [RingEquiv.coe_toRingHom, τ_mk]
  rfl

end Reduction

/-! ### Finiteness, flatness, torsion -/

section Props

variable {f} {δ : FormalPatchLevel.Hat f} (t : FormalPatchLevel.Hat f) {e : ℕ}

lemma monic_cpoly (he : 0 < e) : (cpoly f δ t e).Monic := monic_X_pow_sub_C _ he.ne'

lemma free_CPiece (he : 0 < e) : Module.Free (CBase f δ) (CPiece f δ t e) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_cpoly (δ := δ) t he)).basis

lemma finite_CPiece (he : 0 < e) :
    Module.Finite (FormalPatchLevel.Hat f) (CPiece f δ t e) := by
  haveI : Module.Finite (CBase f δ) (CPiece f δ t e) :=
    (AdjoinRoot.powerBasis' (monic_cpoly (δ := δ) t he)).finite
  haveI : Module.Finite (FormalPatchLevel.Hat f) (CBase f δ) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) Ideal.Quotient.mk_surjective
  exact Module.Finite.trans (CBase f δ) _

/-- `f` is a nonzerodivisor on `R̂/(1 − δ̃)` if it is one on `R̂`. -/
lemma noTorsion_CBase (hδ : IsIdempotentElem δ)
    (hreg : ∀ y : FormalPatchLevel.Hat f, algebraMap R _ f * y = 0 → y = 0)
    (x : CBase f δ) (hx : algebraMap R (CBase f δ) f * x = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : algebraMap R (CBase f δ) f = Ideal.Quotient.mk _ (algebraMap R _ f) := rfl
  rw [h1, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
  obtain ⟨z, hz⟩ := hx
  have h2 : algebraMap R (FormalPatchLevel.Hat f) f * (δ * y) = 0 := by
    have : δ * (z * (1 - δ)) = 0 := by
      rw [mul_comm z, ← mul_assoc, mul_sub, mul_one, hδ.eq, sub_self, zero_mul]
    rw [mul_left_comm, ← hz]
    exact this
  have h3 := hreg _ h2
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨y, by rw [mul_sub, mul_one, mul_comm, h3, sub_zero]⟩

/-- **`f` is a nonzerodivisor on the lifted cusp factor.** -/
theorem noTorsion_CPiece (he : 0 < e) (hδ : IsIdempotentElem δ)
    (hreg : ∀ y : FormalPatchLevel.Hat f, algebraMap R _ f * y = 0 → y = 0)
    (x : CPiece f δ t e)
    (hx : algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) (algebraMap R _ f) * x = 0) :
    x = 0 := by
  let b := (AdjoinRoot.powerBasis' (monic_cpoly (δ := δ) t he)).basis
  have hc : algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) (algebraMap R _ f) * x =
      (algebraMap R (CBase f δ) f) • x := by
    rw [Algebra.smul_def]
    rfl
  rw [hc] at hx
  apply b.repr.injective
  ext i
  have := congrArg (fun y ↦ b.repr y i) hx
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at this
  rw [noTorsion_CBase hδ hreg _ this]
  simp

/-- **The localization at `f` of the lifted cusp factor is flat over `R̂`.** -/
theorem flat_loc_CPiece (he : 0 < e) (hδ : IsIdempotentElem δ) :
    Module.Flat (FormalPatchLevel.Hat f) (Localization.Away
      (algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) (algebraMap R _ f))) := by
  haveI := free_CPiece t (δ := δ) he
  haveI : Module.Flat (FormalPatchLevel.Hat f) (CBase f δ) :=
    FormalPatchProd.flat_quotient_one_sub hδ
  haveI : Module.Flat (FormalPatchLevel.Hat f) (CPiece f δ t e) :=
    Module.Flat.trans (FormalPatchLevel.Hat f) (CBase f δ) _
  haveI : Module.Flat (CPiece f δ t e) (Localization.Away
      (algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) (algebraMap R _ f))) :=
    IsLocalization.flat _ (Submonoid.powers (algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e)
      (algebraMap R _ f)))
  exact Module.Flat.trans (FormalPatchLevel.Hat f) (CPiece f δ t e) _

end Props

end

end AdmissibleLift

end SemistableReduction
