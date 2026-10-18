/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.QuadNodeLevel

/-!
# Reduction of the node ring modulo an ideal of the base (Blueprint §12.8, M2.3 (d'), step κ3)

The Kummer algebra `B = O[s,t]/(st − π)` over `A = O[u,v]/(uv − π^e)` is defined over the level
ring `O = O'/ϖⁿ⁺¹`; the admissible covering of the special fibre is stated over the residue
field `k = O/ϖ`, with `π ↦ 0`. Base change of the node ring along `O → O/I`:

* **`Node.quotEquiv I a : Node O a ⧸ I·Node O a ≃+* Node (O/I) (a mod I)`**, `u ↦ u`, `v ↦ v`
  (`Node.quotEquiv_u`, `Node.quotEquiv_v`, `Node.quotEquiv_algebraMap`).
-/

universe u

namespace SemistableReduction

namespace Node

noncomputable section

variable {O : Type u} [CommRing O] (I : Ideal O) (a : O)

/-- The ideal `I · O[u,v]/(uv − a)`. -/
abbrev IN : Ideal (Node O a) := I.map (algebraMap O (Node O a))

/-- `O[u,v]/(uv − a) → (O/I)[u,v]/(uv − ā)`. -/
def quotFwd₀ : Node O a →ₐ[O] Node (O ⧸ I) (Ideal.Quotient.mk I a) :=
  Node.lift (Node.u _) (Node.v _) (by
    rw [Node.u_mul_v, IsScalarTower.algebraMap_apply O (O ⧸ I) (Node (O ⧸ I) _),
      Ideal.Quotient.algebraMap_eq])

lemma quotFwd₀_le : IN I a ≤ RingHom.ker (quotFwd₀ I a) := by
  rw [Ideal.map_le_iff_le_comap]
  intro o ho
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
    IsScalarTower.algebraMap_apply O (O ⧸ I) (Node (O ⧸ I) _), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr ho, map_zero]

/-- The forward map. -/
def quotFwd : Node O a ⧸ IN I a →+* Node (O ⧸ I) (Ideal.Quotient.mk I a) :=
  Ideal.Quotient.lift _ (quotFwd₀ I a).toRingHom fun _ hx ↦ quotFwd₀_le I a hx

/-- `O/I → Node O a ⧸ I`. -/
def quotO : O ⧸ I →+* Node O a ⧸ IN I a :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp (algebraMap O (Node O a))) fun o ho ↦ by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ho

/-- The `O/I`-algebra structure on `Node O a ⧸ I`. -/
abbrev quotAlg : Algebra (O ⧸ I) (Node O a ⧸ IN I a) := (quotO I a).toAlgebra

attribute [local instance] quotAlg

/-- The inverse map. -/
def quotBwd : Node (O ⧸ I) (Ideal.Quotient.mk I a) →+* Node O a ⧸ IN I a :=
  (Node.lift (Ideal.Quotient.mk (IN I a) (Node.u a)) (Ideal.Quotient.mk (IN I a) (Node.v a)) (by
    rw [← map_mul, Node.u_mul_v]
    rfl)).toRingHom

lemma quotBwd_u : quotBwd I a (Node.u _) = Ideal.Quotient.mk _ (Node.u a) := Node.lift_u ..

lemma quotBwd_v : quotBwd I a (Node.v _) = Ideal.Quotient.mk _ (Node.v a) := Node.lift_v ..

lemma quotBwd_algebraMap (x : O ⧸ I) :
    quotBwd I a (algebraMap (O ⧸ I) _ x) = quotO I a x :=
  (Node.lift _ _ _).commutes x

lemma quotFwd_mk (x : Node O a) :
    quotFwd I a (Ideal.Quotient.mk _ x) = quotFwd₀ I a x := Ideal.Quotient.lift_mk _ _ _

/-- **`Node O a ⧸ I ≃+* Node (O/I) (a mod I)`.** -/
def quotEquiv : Node O a ⧸ IN I a ≃+* Node (O ⧸ I) (Ideal.Quotient.mk I a) :=
  RingEquiv.ofRingHom (quotFwd I a) (quotBwd I a)
    (by
      refine Node.ringHom_ext (RingHom.ext fun x ↦ ?_) ?_ ?_
      · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [quotBwd_algebraMap, quotO, Ideal.Quotient.lift_mk, RingHom.comp_apply, quotFwd_mk,
          AlgHom.commutes, IsScalarTower.algebraMap_apply O (O ⧸ I) (Node (O ⧸ I) _),
          Ideal.Quotient.algebraMap_eq]
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [quotBwd_u, quotFwd_mk]
        exact Node.lift_u ..
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [quotBwd_v, quotFwd_mk]
        exact Node.lift_v ..)
    (by
      refine Ideal.Quotient.ringHom_ext (Node.ringHom_ext (RingHom.ext fun o ↦ ?_) ?_ ?_)
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [quotFwd_mk, AlgHom.commutes, IsScalarTower.algebraMap_apply O (O ⧸ I)
          (Node (O ⧸ I) _), quotBwd_algebraMap, quotO, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.lift_mk, RingHom.comp_apply]
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [quotFwd_mk, show quotFwd₀ I a (Node.u a) = Node.u _ from Node.lift_u .., quotBwd_u]
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [quotFwd_mk, show quotFwd₀ I a (Node.v a) = Node.v _ from Node.lift_v .., quotBwd_v])

lemma quotEquiv_apply (x : Node O a ⧸ IN I a) :
    quotEquiv I a x = quotFwd I a x := rfl

lemma quotEquiv_u : quotEquiv I a (Ideal.Quotient.mk _ (Node.u a)) = Node.u _ :=
  (quotFwd_mk I a _).trans (Node.lift_u ..)

lemma quotEquiv_v : quotEquiv I a (Ideal.Quotient.mk _ (Node.v a)) = Node.v _ :=
  (quotFwd_mk I a _).trans (Node.lift_v ..)

lemma quotEquiv_algebraMap (o : O) :
    quotEquiv I a (Ideal.Quotient.mk _ (algebraMap O (Node O a) o)) =
      algebraMap (O ⧸ I) _ (Ideal.Quotient.mk I o) := by
  rw [quotEquiv_apply, quotFwd_mk, AlgHom.commutes,
    IsScalarTower.algebraMap_apply O (O ⧸ I) (Node (O ⧸ I) _),
    Ideal.Quotient.algebraMap_eq]

end

end Node

end SemistableReduction
