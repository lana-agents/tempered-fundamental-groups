/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeQuot

/-!
# Base change of the node ring along a surjection (Blueprint §12.8, M2.3 (d'), step κ3)

For a ring map `θ : O → k` and `a ∈ O`, `b ∈ k` with `θ a = b`, `Node.baseMap θ h` is the ring map
`O[u,v]/(uv − a) → k[u,v]/(uv − b)` (`u ↦ u`, `v ↦ v`, coefficients through `θ`). For `θ`
surjective it is **surjective with kernel `(ker θ)·O[u,v]/(uv − a)`** (`Node.surjective_baseMap`,
**`Node.ker_baseMap`**; via Mathlib `MvPolynomial.ker_map` and `Ideal.comap_map_of_surjective`).

It is compatible with the Kummer maps `u ↦ s^e`, `v ↦ t^e` (`Node.baseMap_comp_kummer`): this is
the reduction `O'[u,v]/(uv − π^e) → k[u,v]/(uv)` (`π ↦ 0`) of the Kummer covering of a node to
the special fibre, used to compare the formal model of a patched covering with an admissible
covering of the special fibre (`Admissible.KummerPiece`).
-/

universe u

namespace SemistableReduction

namespace Node

noncomputable section

open MvPolynomial

variable {O k : Type u} [CommRing O] [CommRing k] (θ : O →+* k) {a : O} {b : k} (h : θ a = b)

include h in
lemma map_gen : MvPolynomial.map θ (X 0 * X 1 - C a : MvPolynomial (Fin 2) O) =
    X 0 * X 1 - C b := by
  simp [h]

/-- **The base change map** `O[u,v]/(uv − a) → k[u,v]/(uv − θ a)`. -/
def baseMap : Node O a →+* Node k b :=
  Ideal.quotientMap _ (MvPolynomial.map θ) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_gen θ h]
    exact Ideal.subset_span rfl)

lemma baseMap_mk (p : MvPolynomial (Fin 2) O) :
    baseMap θ h (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map θ p) :=
  Ideal.quotientMap_mk

@[simp] lemma baseMap_u : baseMap θ h (u a) = u b := by
  rw [u, baseMap_mk, MvPolynomial.map_X]
  rfl

@[simp] lemma baseMap_v : baseMap θ h (v a) = v b := by
  rw [v, baseMap_mk, MvPolynomial.map_X]
  rfl

@[simp] lemma baseMap_algebraMap (o : O) :
    baseMap θ h (algebraMap O (Node O a) o) = algebraMap k (Node k b) (θ o) := by
  rw [← Ideal.Quotient.mk_algebraMap, baseMap_mk, MvPolynomial.algebraMap_eq,
    MvPolynomial.map_C]
  rfl

variable {θ}

/-- The base change map is surjective for `θ` surjective. -/
theorem surjective_baseMap (hθ : Function.Surjective θ) : Function.Surjective (baseMap θ h) :=
  Ideal.quotientMap_surjective (MvPolynomial.map_surjective θ hθ)

/-- **The kernel of the base change map is `(ker θ)·O[u,v]/(uv − a)`** (`θ` surjective). -/
theorem ker_baseMap (hθ : Function.Surjective θ) :
    RingHom.ker (baseMap θ h) = (RingHom.ker θ).map (algebraMap O (Node O a)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, baseMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have hspan : Ideal.span {(X 0 * X 1 - C b : MvPolynomial (Fin 2) k)} =
        (Ideal.span {(X 0 * X 1 - C a : MvPolynomial (Fin 2) O)}).map (MvPolynomial.map θ) := by
      rw [Ideal.map_span, Set.image_singleton, map_gen θ h]
    rw [hspan, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _
      (MvPolynomial.map_surjective θ hθ), ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map] at hx
    obtain ⟨q, hq, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hq, zero_add]
    have hmap : (Ideal.map (C : O →+* MvPolynomial (Fin 2) O) (RingHom.ker θ)).map
        (Ideal.Quotient.mk (Ideal.span {(X 0 * X 1 - C a : MvPolynomial (Fin 2) O)})) =
        (RingHom.ker θ).map (algebraMap O (Node O a)) := by
      rw [Ideal.map_map]
      rfl
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hr
  · rw [Ideal.map_le_iff_le_comap]
    intro o ho
    rw [Ideal.mem_comap, RingHom.mem_ker, baseMap_algebraMap, RingHom.mem_ker.mp ho, map_zero]

variable (θ)

/-- **The base change map is compatible with the Kummer maps** `u ↦ s^e`, `v ↦ t^e`. -/
lemma baseMap_comp_kummer {c : O} {d : k} (hc : θ c = d) (e : ℕ) :
    (baseMap θ hc).comp (kummer c e).toRingHom =
      (kummer d e).toRingHom.comp (baseMap θ (by rw [map_pow, hc])) := by
  refine Node.ringHom_ext (RingHom.ext fun o ↦ ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      baseMap_algebraMap]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, kummer_u,
      baseMap_u, map_pow]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, kummer_v,
      baseMap_v, map_pow]

end

end Node

end SemistableReduction
