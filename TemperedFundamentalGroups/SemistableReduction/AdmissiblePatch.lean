/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.AdmissibleLift
import TemperedFundamentalGroups.SemistableReduction.FormalPatchReduction
import TemperedFundamentalGroups.SemistableReduction.FormalPatchProd
import TemperedFundamentalGroups.SemistableReduction.KummerFactor

/-!
# Level-`n` patching of an admissible covering (Blueprint §12.8, M2.3 at one level)

Setting of `AdmissibleLift`: a level ring `O` (local, residue map `θ : O → k`), a Noetherian chart
`R` over `O` with `J = (ker θ) R` nilpotent, `f ∈ R` cutting out the nodes, an admissible covering
`cov` of the special fibre `R/J` without marked points, and lift data `L` of its Kummer factors
whose formal node coordinates `χ_j : O[u,v]/(uv − π_j^{e_j}) → R̂` make `R̂` flat over the node
ring and send `u + v ↦ f`. Given a formally étale `R`-algebra `P` over `D(f)` lifting the
restriction `C_f` of the covering (`σP : P/JP ≃ C_f`, e.g. from
`EtaleLiftExists.exists_finite_etale_lift_of_pow_eq_bot`),

**`AdmissibleLift.patch_spec`**: the patched algebra `G = P ×_{N_f} N` of `FormalPatchLevel`, with
`N = ∏_j (R̂/(1 − ε̃_j)) ⊗ O[s,t]/(st − π_j)` the lifted Kummer model and the identification
`α₀` modulo `J` built from `σP` and `κ` (`AdmissibleLift.kappa`), is a **finite `R`-algebra**,
equal to `P` on `D(f)` and to `N` on the formal neighbourhood of the nodes.

Ingredients: `LPiece.flat` (`R̂/(1 − ε̃)` is flat over the node ring), `noTorsion` (`f` is a
nonzerodivisor on `N`, `KummerFactor.eq_zero_of_mul_eq_zero`), `flat_loc` (`N_f` is flat over
`R̂`, `KummerFactor.flat_localization`, `e_j` invertible in `O` since `(e_j : k) ≠ 0` and `O` is
local), `finite_N` (`N` is finite over `R̂`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace AdmissibleLift

noncomputable section

open KummerEtale

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} {π : O} {e : ℕ}

/-! ### The lifted Kummer factor -/

section Piece

variable (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) {ε : FormalPatchLevel.Hat f}

/-- `R̂/(1 − ε̃)` is flat over the node ring if `R̂` is (through `χ`). -/
theorem LPiece.flat (hχ : χ.toRingHom.Flat) (hε : IsIdempotentElem ε) :
    Module.Flat (A π e) (LPiece f χ ε) := by
  letI : Algebra (A π e) (FormalPatchLevel.Hat f) := χ.toRingHom.toAlgebra
  haveI : Module.Flat (A π e) (FormalPatchLevel.Hat f) := hχ
  haveI : IsScalarTower (A π e) (FormalPatchLevel.Hat f) (LPiece f χ ε) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Module.Flat (FormalPatchLevel.Hat f) (LPiece f χ ε) :=
    FormalPatchProd.flat_quotient_one_sub hε
  exact Module.Flat.trans (A π e) (FormalPatchLevel.Hat f) (LPiece f χ ε)

variable (ε) in
/-- `f ↦ 1 ⊗ (s^e + t^e)` on the lifted factor, if `χ(u + v) = f`. -/
lemma algebraMap_f (hf : χ (fA π) = algebraMap R (FormalPatchLevel.Hat f) f) :
    algebraMap R (N f χ ε) f = algebraMap (A π e) (N f χ ε) (fA π) := by
  change algebraMap (FormalPatchLevel.Hat f) (N f χ ε) (algebraMap R _ f) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
    LPiece.algebraMap_A, hf]
  rfl

/-- **`f` is a nonzerodivisor on the lifted factor.** -/
theorem noTorsion (he : 0 < e) (hχ : χ.toRingHom.Flat) (hε : IsIdempotentElem ε)
    (hf : χ (fA π) = algebraMap R (FormalPatchLevel.Hat f) f) (x : N f χ ε)
    (hx : algebraMap R (N f χ ε) f * x = 0) : x = 0 := by
  haveI := LPiece.flat χ hχ hε
  rw [algebraMap_f χ ε hf] at hx
  exact KummerFactor.eq_zero_of_mul_eq_zero π (LPiece f χ ε) he x hx

instance : Module.Finite (FormalPatchLevel.Hat f) (LPiece f χ ε) :=
  Module.Finite.of_surjective (Algebra.linearMap (FormalPatchLevel.Hat f) (LPiece f χ ε))
    Ideal.Quotient.mk_surjective

/-- The lifted factor is finite over `R̂`. -/
theorem finite_N (he : 0 < e) : Module.Finite (FormalPatchLevel.Hat f) (N f χ ε) := by
  haveI := KummerFactor.finite π (S := LPiece f χ ε) he
  exact Module.Finite.trans (LPiece f χ ε) (N f χ ε)

/-- **`N_f` is flat over `R̂`** (`e` invertible in `O`). -/
theorem flat_loc (he : 0 < e) (heu : IsUnit (e : O)) (hχ : χ.toRingHom.Flat)
    (hε : IsIdempotentElem ε) (hf : χ (fA π) = algebraMap R (FormalPatchLevel.Hat f) f) :
    Module.Flat (FormalPatchLevel.Hat f) (Localization.Away (algebraMap R (N f χ ε) f)) := by
  haveI := LPiece.flat χ hχ hε
  haveI : Module.Flat (FormalPatchLevel.Hat f) (LPiece f χ ε) :=
    FormalPatchProd.flat_quotient_one_sub hε
  haveI := KummerFactor.flat_localization π he heu (S := LPiece f χ ε)
  rw [algebraMap_f χ ε hf]
  exact Module.Flat.trans (FormalPatchLevel.Hat f) (LPiece f χ ε) _

end Piece

/-! ### The patch -/

variable (θ) [Algebra k (R ⧸ J θ)] {φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)} {cov : Admissible.Covering φ ψc}
  (L : KummerLift cov)

/-- The ramification indices are units of the (local) level ring. -/
lemma isUnit_e (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (j : cov.ι) : IsUnit ((cov.e j : ℕ) : O) :=
  hO _ (by rw [map_natCast]; exact cov.e_ne_zero j)

variable {θ}

/-- **Level-`n` patching of an admissible covering** (no marked points): the patched algebra is
finite over the chart, equal to the étale lift `P` on `D(f)`, and to the lifted Kummer model on
the formal neighbourhood of the nodes. -/
theorem patch_spec [IsNoetherianRing R] [IsEmpty cov.κ] (hθ : Function.Surjective θ)
    (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ} (hJ : J θ (R := R) ^ n = ⊥)
    (hflat : ∀ j, (L.χ j).toRingHom.Flat) (hidem : ∀ j, IsIdempotentElem (L.ε j))
    (hf : ∀ j, L.χ j (fA (L.π j)) = algebraMap R (FormalPatchLevel.Hat f) f)
    {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
    (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R cov.C f))
    (hfP : IsUnit (algebraMap R P f))
    (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P)) :
    let α₀ := FormalPatchLevel.alphaOfEquiv f (J θ)
      (FormalPatchLevel.specialFibreEquiv f (J θ) σP (kappa hθ L))
    Module.Finite R (FormalPatchLevel.patch f (J θ) hJ α₀) ∧
      (letI := FormalGlueing.algebraFst (NL L) (FormalPatchLevel.lift f (J θ) hJ α₀);
        IsLocalization.Away (algebraMap R (FormalPatchLevel.patch f (J θ) hJ α₀) f) P) ∧
      IsBaseChange (FormalPatchLevel.Hat f)
        (FormalGlueing.snd (NL L) (FormalPatchLevel.lift f (J θ) hJ α₀)).toLinearMap := by
  intro α₀
  haveI : Module.Flat (FormalPatchLevel.Hat f) (FormalPatchLevel.Nf f (NL L)) :=
    FormalPatchProd.flat_localization f _ fun j ↦
      flat_loc (L.χ j) (cov.e_pos j) (isUnit_e θ hO j) (hflat j) (hidem j) (hf j)
  haveI : ∀ j, Module.Finite (FormalPatchLevel.Hat f) (N f (L.χ j) (L.ε j)) := fun j ↦
    finite_N (L.χ j) (cov.e_pos j)
  have hN : ∀ x : NL L, algebraMap R (NL L) f * x = 0 → x = 0 :=
    FormalPatchProd.eq_zero_of_mul_eq_zero f fun j ↦
      noTorsion (L.χ j) (cov.e_pos j) (hflat j) (hidem j) (hf j)
  have hsurj := FormalPatchLevel.surjective_betaMod_alphaOfEquiv
    (FormalPatchLevel.specialFibreEquiv f (J θ) σP (kappa hθ L))
  have hinj := FormalPatchLevel.mem_of_betaMod_alphaOfEquiv_eq_zero
    (FormalPatchLevel.specialFibreEquiv f (J θ) σP (kappa hθ L))
  exact ⟨FormalPatchLevel.finite_patch f (J θ) hJ hfP hN α₀ hsurj hinj hP,
    FormalPatchLevel.isLocalization_patch f (J θ) hJ α₀ hfP,
    FormalPatchLevel.isBaseChange_patch f (J θ) hJ hfP hN α₀ hsurj hinj⟩

end

end AdmissibleLift

end SemistableReduction
