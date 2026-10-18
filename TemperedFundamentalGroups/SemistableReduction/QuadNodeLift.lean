/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.QuadraticNodeChart

/-!
# Formal node coordinates of the quadratic node chart for every Kummer index

(Blueprint §12.8, M2.3: the Tate instance of the lift data `AdmissibleLift.KummerLift`.)

The quadratic node chart `R = (A[S]/(S² + S − c))[1/D]` over `A = O[u,v]/(uv − π^e)` (the Tate chart
near its nodes, `QuadNodeLevel.equiv`) has, for every factorization `π'^{e'} = π^e` of the
thickness, formal node coordinates `χ : O[u,v]/(uv − π'^{e'}) → R̂` (`QuadNode.χ`, `u ↦ u`,
`v ↦ v`) which are

* **flat** (`QuadNode.flat_χ`: the node rings are isomorphic, `Node.congrEq`, and `R̂` is flat over
  `A`, `QuadNode.flat_hat`), and
* send `u + v` to the element `f` cutting out the nodes (`QuadNode.χ_fA`).

These are the hypotheses `hflat`, `hf` of `AdmissibleLift.patch_spec` for a Kummer factor of index
`e'` with deformation parameter `π'` (`e' | e·ord(π)` is what makes `π'` exist).
-/

universe u

namespace SemistableReduction

open KummerEtale

namespace Node

variable {O : Type u} [CommRing O] {a b : O}

/-- The node rings `O[u,v]/(uv − a)` and `O[u,v]/(uv − b)` for `a = b`. -/
noncomputable def congrEq (h : a = b) : Node O a ≃ₐ[O] Node O b :=
  AlgEquiv.ofAlgHom (Node.lift (Node.u b) (Node.v b) (by rw [Node.u_mul_v, h]))
    (Node.lift (Node.u a) (Node.v a) (by rw [Node.u_mul_v, h]))
    (Node.algHom_ext (by simp) (by simp)) (Node.algHom_ext (by simp) (by simp))

@[simp] lemma congrEq_u (h : a = b) : congrEq h (Node.u a) = Node.u b := by
  rw [congrEq, AlgEquiv.ofAlgHom_apply]
  exact Node.lift_u _ _ _

@[simp] lemma congrEq_v (h : a = b) : congrEq h (Node.v a) = Node.v b := by
  rw [congrEq, AlgEquiv.ofAlgHom_apply]
  exact Node.lift_v _ _ _

end Node

namespace QuadNode

noncomputable section

variable {O : Type u} [CommRing O] (π : O) (e : ℕ) (c D : A π e) {π' : O} {e' : ℕ}
  (h : π' ^ e' = π ^ e)

/-- **Formal node coordinates of index `e'`** on the completion of the quadratic node chart. -/
def χ : A π' e' →ₐ[O] FormalPatchLevel.Hat (f π e c D) :=
  (IsScalarTower.toAlgHom O (A π e) (FormalPatchLevel.Hat (f π e c D))).comp
    (Node.congrEq h).toAlgHom

/-- The coordinates `χ` are flat. -/
theorem flat_χ [IsNoetherianRing O] : (χ π e c D h).toRingHom.Flat := by
  have h1 : (algebraMap (A π e) (FormalPatchLevel.Hat (f π e c D))).Flat :=
    RingHom.flat_algebraMap_iff.mpr (flat_hat π e c D)
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Node.congrEq h).bijective) h1

/-- `χ(u + v) = f`. -/
theorem χ_fA : χ π e c D h (fA π') =
    algebraMap (R π e c D) (FormalPatchLevel.Hat (f π e c D)) (f π e c D) := by
  rw [algebraMap_f]
  simp [χ, fA]

end

end QuadNode

end SemistableReduction
