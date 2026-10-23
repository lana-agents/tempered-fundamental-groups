/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KaehlerLocal
import TemperedFundamentalGroups.SemistableReduction.LevelTowerData

/-!
# The differentials of the patched level algebras (Blueprint §12.8, M2.5 (f), F2)

The patched algebra `G` of a level of a covering (`LevelTower.Level.G`, glued from the étale lift
`P` over `D(f)` and the lifted formal model `NF = ∏ Kummer factors × ∏ cusp factors` over the
`f`-adic completion `R̂`) has differentials killed by a uniform constant:

* **`AdmissibleLift.kills_N`**: on a lifted Kummer factor
  `(R̂/(1 − ε)) ⊗_{O[u,v]/(uv − πᵉ)} O[s,t]/(st − π)` (`e` invertible), `π^(e-1)` kills the
  differentials over `R̂` (`KaehlerLocal.kummer_kills`);
* **`AdmissibleLift.kills_CPiece`**: on a lifted cusp factor `(R̂/(1 − δ))[X]/(Xᵉ − t)`, `t` kills
  them (`KaehlerLocal.root_kills`);
* **`LevelTower.Level.kills_G`**: if `c ∈ R` is a multiple of `πⱼ^(eⱼ-1)` for every Kummer factor
  and its image in `R̂` a multiple of the cusp coordinate `t` (when there are cusp factors), then
  `c` kills `Ω[G⁄R]` (`KaehlerLocal.kills_of_patch`; `P` is étale over `R`).

In the Tate case `πⱼ^(eⱼ) = ϖ^m`, so `c = ϖ^m` works on node charts, and `c = ϖ^m h` near the cusp.
-/

universe u

open TensorProduct

namespace KaehlerLocal

/-- **Killing the differentials of a finite product** factor by factor. -/
theorem kills_pi (R : Type u) [CommRing R] {ι : Type} [Finite ι] (S : ι → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] {c : R}
    (hc : ∀ i, Kills R (algebraMap R (S i) c)) : Kills R (algebraMap R (∀ i, S i) c) := by
  classical
  haveI := Fintype.ofFinite ι
  letI : ∀ i, Algebra (∀ i, S i) (S i) := fun i ↦ (Pi.evalRingHom S i).toAlgebra
  haveI : ∀ i, IsScalarTower R (∀ i, S i) (S i) := fun i ↦
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : ∀ i, IsLocalization.Away (Pi.single i 1 : ∀ i, S i) (S i) := fun i ↦
    IsLocalization.away_of_isIdempotentElem_of_mul
      (by rw [IsIdempotentElem, ← Pi.single_mul, one_mul])
      (fun x y ↦ by
        change x i = y i ↔ _
        constructor
        · intro h
          funext j
          by_cases hj : j = i
          · subst hj
            simp [h]
          · rw [Pi.mul_apply, Pi.mul_apply, Pi.single_eq_of_ne hj, zero_mul, zero_mul]
        · intro h
          have := congrFun h i
          rwa [Pi.mul_apply, Pi.mul_apply, Pi.single_eq_same, one_mul, one_mul] at this)
      (fun z ↦ ⟨Pi.single i z, by
        change Pi.single i z i = z
        exact Pi.single_eq_same i z⟩)
  refine kills_of_away R (a := fun i ↦ (Pi.single i 1 : ∀ i, S i)) ?_ S fun i ↦ ?_
  · rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
    rw [← Finset.univ_sum_single (1 : ∀ i, S i)]
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.subset_span ⟨i, by simp⟩
  · rw [← IsScalarTower.algebraMap_apply]
    exact hc i

end KaehlerLocal

namespace SemistableReduction

open KummerEtale

noncomputable section

namespace AdmissibleLift

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R] (f : R)

variable {π : O} {e : ℕ} (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)

/-- `π` in `R̂/(1 − ε)`, through the node coordinates. -/
abbrev piL : LPiece f χ ε := algebraMap (A π e) (LPiece f χ ε) (algebraMap O (A π e) π)

lemma algebraMap_piL :
    algebraMap (FormalPatchLevel.Hat f) (LPiece f χ ε) (algebraMap O (FormalPatchLevel.Hat f) π) =
      piL f χ ε := by
  rw [piL, LPiece.algebraMap_A, AlgHom.commutes]
  rfl

/-- `π^(e-1)` kills the differentials of the Kummer factor over `R̂/(1 − ε)`. -/
lemma kills_N_base (he : IsUnit (e : O)) :
    KaehlerLocal.Kills (LPiece f χ ε)
      (algebraMap (LPiece f χ ε) (N f χ ε) (piL f χ ε) ^ (e - 1)) := by
  let ι := Algebra.TensorProduct.includeRight (R := A π e) (A := LPiece f χ ε) (B := B π)
  have he' : IsUnit (e : N f χ ε) := by
    have := he.map ((algebraMap R (N f χ ε)).comp (algebraMap O R))
    rwa [map_natCast] at this
  have key : ∀ a : A π e, ι (algebraMap (A π e) (B π) a) =
      algebraMap (LPiece f χ ε) (N f χ ε) (algebraMap (A π e) (LPiece f χ ε) a) := fun a ↦ by
    rw [ι.commutes, IsScalarTower.algebraMap_apply (A π e) (LPiece f χ ε) (N f χ ε)]
  have hu : ι (Node.u π) ^ e ∈ Set.range (algebraMap (LPiece f χ ε) (N f χ ε)) :=
    ⟨_, by rw [← key, algebraMap_u, map_pow]⟩
  have hv : ι (Node.v π) ^ e ∈ Set.range (algebraMap (LPiece f χ ε) (N f χ ε)) :=
    ⟨_, by rw [← key, algebraMap_v, map_pow]⟩
  have hst : ι (Node.u π) * ι (Node.v π) = algebraMap (LPiece f χ ε) (N f χ ε) (piL f χ ε) := by
    rw [← map_mul, Node.u_mul_v, IsScalarTower.algebraMap_apply O (A π e) (B π), key]
  have hk := KaehlerLocal.kummer_kills he' hu hv hst
  refine KaehlerLocal.kills_of_adjoin _ (s := ι '' {Node.u π, Node.v π})
    (Algebra.TensorProduct.adjoin_one_tmul_image_eq_top _ (Node.kummer_adjoin_eq_top π e)) ?_
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with rfl | rfl
  · exact hk.1
  · exact hk.2

/-- **The differentials of a lifted Kummer factor** over `R̂` are killed by `π^(e-1)` (`e`
invertible). -/
theorem kills_N (he : IsUnit (e : O)) {c : FormalPatchLevel.Hat f}
    (hc : ∃ r, c = algebraMap O (FormalPatchLevel.Hat f) π ^ (e - 1) * r) :
    KaehlerLocal.Kills (FormalPatchLevel.Hat f)
      (algebraMap (FormalPatchLevel.Hat f) (N f χ ε) c) := by
  haveI : Subsingleton Ω[(LPiece f χ ε)⁄(FormalPatchLevel.Hat f)] :=
    KaehlerLocal.subsingleton_of_surjective _ _ Ideal.Quotient.mk_surjective
  refine KaehlerLocal.kills_of_base _ (LPiece f χ ε) ?_
  obtain ⟨r, rfl⟩ := hc
  have e1 : algebraMap (FormalPatchLevel.Hat f) (N f χ ε)
      (algebraMap O (FormalPatchLevel.Hat f) π ^ (e - 1) * r) =
      algebraMap (LPiece f χ ε) (N f χ ε) (piL f χ ε) ^ (e - 1) *
        algebraMap (LPiece f χ ε) (N f χ ε)
          (algebraMap (FormalPatchLevel.Hat f) (LPiece f χ ε) r) := by
    simp only [IsScalarTower.algebraMap_apply (FormalPatchLevel.Hat f) (LPiece f χ ε) (N f χ ε),
      map_mul, map_pow, algebraMap_piL]
  intro ω
  rw [e1, mul_comm (algebraMap (LPiece f χ ε) (N f χ ε) (piL f χ ε) ^ (e - 1)), mul_smul,
    kills_N_base f χ ε he ω, smul_zero]

/-- **The differentials of a lifted cusp factor** over `R̂` are killed by the cusp coordinate `t`
(`e` invertible). -/
theorem kills_CPiece (δ t : FormalPatchLevel.Hat f) {e : ℕ} (he : IsUnit (e : O)) (he0 : e ≠ 0)
    {c : FormalPatchLevel.Hat f} (hc : ∃ r, c = t * r) :
    KaehlerLocal.Kills (FormalPatchLevel.Hat f)
      (algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) c) := by
  haveI : Subsingleton Ω[(CBase f δ)⁄(FormalPatchLevel.Hat f)] :=
    KaehlerLocal.subsingleton_of_surjective _ _ Ideal.Quotient.mk_surjective
  refine KaehlerLocal.kills_of_base _ (CBase f δ) fun ω ↦ ?_
  obtain ⟨r, rfl⟩ := hc
  have he' : IsUnit (e : CPiece f δ t e) := by
    have := he.map ((algebraMap R (CPiece f δ t e)).comp (algebraMap O R))
    rwa [map_natCast] at this
  have hroot : AdjoinRoot.root (cpoly f δ t e) ^ e =
      algebraMap (CBase f δ) (CPiece f δ t e) (Ideal.Quotient.mk _ t) := by
    have h := AdjoinRoot.eval₂_root (cpoly f δ t e)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
    exact h
  have hk : KaehlerLocal.Kills (CBase f δ)
      (algebraMap (CBase f δ) (CPiece f δ t e) (Ideal.Quotient.mk _ t)) :=
    KaehlerLocal.kills_of_adjoin _ (s := {AdjoinRoot.root (cpoly f δ t e)})
      (AdjoinRoot.adjoinRoot_eq_top) fun x hx ↦ by
        rw [Set.mem_singleton_iff.1 hx]
        exact KaehlerLocal.root_kills he' he0 hroot
  have e1 : algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) (t * r) =
      algebraMap (CBase f δ) (CPiece f δ t e) (Ideal.Quotient.mk _ t) *
        algebraMap (CBase f δ) (CPiece f δ t e) (Ideal.Quotient.mk _ r) := by
    rw [IsScalarTower.algebraMap_apply (FormalPatchLevel.Hat f) (CBase f δ) (CPiece f δ t e),
      map_mul, map_mul]
    rfl
  rw [e1, mul_comm (algebraMap (CBase f δ) (CPiece f δ t e) (Ideal.Quotient.mk _ t)), mul_smul,
    hk ω, smul_zero]

end AdmissibleLift


namespace GlueKaehler

open FormalGlueing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R) {P : Type u} [CommRing P]
  [Algebra R P] [Algebra.FormallyUnramified R P] (N : Type u) [CommRing N] [Algebra R N]
  [Algebra (FormalPatchLevel.Hat f) N] [IsScalarTower R (FormalPatchLevel.Hat f) N]
  {Q : Type u} [CommRing Q] [Algebra R Q] [Algebra N Q] [IsScalarTower R N Q]
  (α : P →ₐ[R] Q) [IsLocalization.Away (algebraMap R N f) Q]

omit [IsLocalization.Away (algebraMap R N f) Q] in
/-- **The differentials of a formally glued algebra** `G = P ×_Q N` (`P` unramified over `R`,
`N = R̂ ⊗_R G`): a constant killing `Ω[N⁄R̂]` kills `Ω[G⁄R]`. -/
theorem kills_glued (hfin : Module.Finite R (glued N α))
    (hloc : letI := algebraFst N α
      IsLocalization.Away (algebraMap R (glued N α) f) P)
    (hbc : IsBaseChange (FormalPatchLevel.Hat f) (snd N α).toLinearMap) {c : R}
    (hN : KaehlerLocal.Kills (FormalPatchLevel.Hat f) (algebraMap R N c)) :
    KaehlerLocal.Kills R (algebraMap R (glued N α) c) := by
  haveI := hfin
  letI := algebraFst N α
  letI : Algebra (glued N α) N := (snd N α).toRingHom.toAlgebra
  haveI : IsScalarTower R (glued N α) P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (glued N α) N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.IsPushout R (FormalPatchLevel.Hat f) (glued N α) N := ⟨hbc⟩
  exact KaehlerLocal.kills_of_patch f P N (fun _ ↦ Subsingleton.elim _ _) hN

end GlueKaehler

namespace LevelTower

open AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

include hO in
/-- **The differentials of the patched level algebra** `G` over the chart `R n` are killed by any
`c` which is a multiple of `πⱼ^(eⱼ-1)` for every Kummer factor `j` and (in `R̂`) a multiple of the
cusp coordinate `t` if there are cusp factors. -/
theorem Level.kills_G {n : ℕ} (D : Level R cov₀ πL hfe n) {c : R n}
    (hK : ∀ j, ∃ r, algebraMap (R n) (FormalPatchLevel.Hat (f n)) c =
      algebraMap O (FormalPatchLevel.Hat (f n)) (πL j) ^
        ((cov₀.transport (h := hfe n)).e j - 1) * r)
    (hC : ∀ _i : (cov₀.transport (h := hfe n)).κ, ∃ r,
      algebraMap (R n) (FormalPatchLevel.Hat (f n)) c = D.M.t * r) :
    KaehlerLocal.Kills (R n) (algebraMap (R n) (D.G hθ) c) := by
  obtain ⟨hfin, hloc, hbc⟩ := Level.spec hθ hO D
  refine GlueKaehler.kills_glued (f n) (NFall D.L D.M) _ hfin hloc hbc ?_
  rw [IsScalarTower.algebraMap_apply (R n) (FormalPatchLevel.Hat (f n)) (NFall D.L D.M)]
  refine KaehlerLocal.kills_pi _ (NF D.L D.M) fun s ↦ ?_
  rcases s with j | i
  · exact kills_N (f n) (D.L.χ j) (D.L.ε j)
      (hO _ (by rw [map_natCast]; exact (cov₀.transport (h := hfe n)).e_ne_zero j)) (hK j)
  · exact kills_CPiece (f n) (D.M.δ i) D.M.t
      (hO _ (by rw [map_natCast]; exact (cov₀.transport (h := hfe n)).ce_ne_zero i))
      ((cov₀.transport (h := hfe n)).ce_pos i).ne' (hC i)

end LevelTower

end

end SemistableReduction
