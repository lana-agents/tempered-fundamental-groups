/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.QuadraticNodeChart

/-!
# Reduction of the quadratic node chart modulo an ideal of the base (Blueprint §12.8, M2.3 (a'))

The Tate chart near the nodes is `R₀ = (A₀[S]/(S² + S − c))[1/D]` over `A₀ = O[u,v]/(uv − a)`
(`TemperedFundamentalGroups.TateNormal.quadChartEquiv`, `a = ϖⁿ`). The patching happens at the
levels `O' = O/I` (`I = (ϖ^{N})`), over the node ring `A π e = O'[u,v]/(uv − π^e)` of
`KummerPatch` with `π^e = a mod I`. Here:

* `QuadNodeLevel.nodeMap`: `O[u,v]/(uv − a) → O'[u,v]/(uv − π^e)`;
* **`QuadNodeLevel.equiv`**: `R₀/IR₀ ≃+* QuadNode.R π e c' D'` (`c'`, `D'` the images of `c`, `D`),
  with `equiv_algebraMap` (compatibility with the node rings), so that the level-`N` chart is a
  quadratic node chart over `A π e`, to which `QuadNode` (flatness of the completion along the
  nodes over `A π e`) and `KummerPatch` apply.

Generic: `Node.ringHom_ext` (ring maps out of the node ring are determined by `O`, `u`, `v`).
-/

universe u

open Polynomial

namespace SemistableReduction

open KummerEtale

lemma Node.ringHom_ext {O : Type*} [CommRing O] {a : O} {S : Type*} [CommRing S]
    {f g : Node O a →+* S} (hO : f.comp (algebraMap O _) = g.comp (algebraMap O _))
    (hu : f (Node.u a) = g (Node.u a)) (hv : f (Node.v a) = g (Node.v a)) : f = g := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) fun i ↦ ?_)
  · exact RingHom.congr_fun hO r
  · fin_cases i
    · exact hu
    · exact hv

namespace QuadNodeLevel

noncomputable section

variable {O : Type u} [CommRing O] (I : Ideal O) {a : O} (π : O ⧸ I) (e : ℕ)
  (h : π ^ e = Ideal.Quotient.mk I a)

include h in
lemma u_mul_v : Node.u (π ^ e) * Node.v (π ^ e) = algebraMap O (A π e) a := by
  rw [Node.u_mul_v, IsScalarTower.algebraMap_apply O (O ⧸ I) (A π e),
    Ideal.Quotient.algebraMap_eq, ← h]

/-- `O[u,v]/(uv − a) → O'[u,v]/(uv − π^e)`. -/
def nodeMap : Node O a →ₐ[O] A π e := Node.lift (Node.u _) (Node.v _) (u_mul_v I π e h)

variable (c D : Node O a)

/-- The chart `R₀ = (A₀[S]/(S² + S − c))[1/D]` over `A₀ = O[u,v]/(uv − a)`. -/
abbrev R₀ : Type u := Localization.Away (AdjoinRoot.of (QuadraticEtale.poly c) D)

/-- The ideal `I R₀`. -/
abbrev IR : Ideal (R₀ c D) := I.map (algebraMap O (R₀ c D))

/-- The target: the quadratic node chart over `A π e`. -/
abbrev Rlev : Type u := QuadNode.R π e (nodeMap I π e h c) (nodeMap I π e h D)

lemma map_poly : (QuadraticEtale.poly c).map (nodeMap I π e h).toRingHom =
    QuadraticEtale.poly (nodeMap I π e h c) := by
  simp [QuadraticEtale.poly]

/-- `A₀[S]/(S² + S − c) → A[S]/(S² + S − c')`. -/
def qMap : AdjoinRoot (QuadraticEtale.poly c) →+* QuadNode.Q π e (nodeMap I π e h c) :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp (nodeMap I π e h).toRingHom) (AdjoinRoot.root _) (by
    rw [← Polynomial.eval₂_map, map_poly]
    exact AdjoinRoot.eval₂_root _)

lemma qMap_of (x : Node O a) :
    qMap I π e h c (AdjoinRoot.of _ x) = AdjoinRoot.of _ (nodeMap I π e h x) :=
  AdjoinRoot.lift_of _

lemma qMap_root : qMap I π e h c (AdjoinRoot.root _) = AdjoinRoot.root _ :=
  AdjoinRoot.lift_root _

/-- The forward map `R₀ → R` before passing to the quotient. -/
def fwd₀ : R₀ c D →+* Rlev I π e h c D :=
  IsLocalization.Away.lift (AdjoinRoot.of _ D)
    (g := (algebraMap (QuadNode.Q π e (nodeMap I π e h c)) (Rlev I π e h c D)).comp
      (qMap I π e h c)) (by
    rw [RingHom.comp_apply, qMap_of]
    exact IsLocalization.Away.algebraMap_isUnit _)

lemma fwd₀_algebraMap (x : AdjoinRoot (QuadraticEtale.poly c)) :
    fwd₀ I π e h c D (algebraMap _ _ x) =
      algebraMap (QuadNode.Q π e (nodeMap I π e h c)) _ (qMap I π e h c x) :=
  IsLocalization.Away.lift_eq _ _ _

lemma fwd₀_algebraMap_O (o : O) :
    fwd₀ I π e h c D (algebraMap O (R₀ c D) o) = algebraMap O (Rlev I π e h c D) o := by
  rw [IsScalarTower.algebraMap_apply O (AdjoinRoot (QuadraticEtale.poly c)) (R₀ c D),
    fwd₀_algebraMap, IsScalarTower.algebraMap_apply O (Node O a) (AdjoinRoot _),
    AdjoinRoot.algebraMap_eq, qMap_of, AlgHom.commutes]
  exact (IsScalarTower.algebraMap_apply O (QuadNode.Q π e (nodeMap I π e h c))
    (Rlev I π e h c D) o).symm

lemma fwd₀_le : IR I c D ≤ RingHom.ker (fwd₀ I π e h c D) := by
  rw [Ideal.map_le_iff_le_comap]
  intro o ho
  rw [Ideal.mem_comap, RingHom.mem_ker, fwd₀_algebraMap_O,
    IsScalarTower.algebraMap_apply O (O ⧸ I) (Rlev I π e h c D), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr ho, map_zero]

/-- The forward map `R₀/I → R`. -/
def fwd : R₀ c D ⧸ IR I c D →+* Rlev I π e h c D :=
  Ideal.Quotient.lift _ (fwd₀ I π e h c D) fun _ hx ↦ fwd₀_le I π e h c D hx

/-! ### The inverse -/

/-- `O' → R₀/I`. -/
def gO : O ⧸ I →+* R₀ c D ⧸ IR I c D :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp (algebraMap O (R₀ c D))) fun o ho ↦ by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ho

/-- `A₀ → R₀/I`. -/
abbrev ι : Node O a →+* R₀ c D ⧸ IR I c D :=
  (Ideal.Quotient.mk _).comp ((algebraMap (AdjoinRoot (QuadraticEtale.poly c)) (R₀ c D)).comp
    (AdjoinRoot.of _))

lemma ι_algebraMap (o : O) : ι I c D (algebraMap O _ o) = gO I c D (Ideal.Quotient.mk I o) := by
  simp only [ι, gO, RingHom.comp_apply, Ideal.Quotient.lift_mk]
  congr 1

/-- `A π e → R₀/I`. -/
def gN : A π e →+* R₀ c D ⧸ IR I c D :=
  letI := (gO I c D).toAlgebra
  (Node.lift (ι I c D (Node.u a)) (ι I c D (Node.v a)) (by
    rw [← map_mul, Node.u_mul_v, ι_algebraMap, h]; rfl)).toRingHom

lemma gN_u : gN I π e h c D (Node.u _) = ι I c D (Node.u a) := by
  letI := (gO I c D).toAlgebra
  exact Node.lift_u ..

lemma gN_v : gN I π e h c D (Node.v _) = ι I c D (Node.v a) := by
  letI := (gO I c D).toAlgebra
  exact Node.lift_v ..

lemma gN_algebraMap (x : O ⧸ I) : gN I π e h c D (algebraMap (O ⧸ I) _ x) = gO I c D x := by
  letI := (gO I c D).toAlgebra
  exact (Node.lift _ _ _).commutes x

lemma gN_nodeMap : (gN I π e h c D).comp (nodeMap I π e h).toRingHom = ι I c D := by
  refine Node.ringHom_ext (RingHom.ext fun o ↦ ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply O (O ⧸ I) (A π e), gN_algebraMap]
    exact (ι_algebraMap I c D o).symm
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, nodeMap,
      Node.lift_u, gN_u]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, nodeMap,
      Node.lift_v, gN_v]

/-- The image of the root in `R₀/I`. -/
abbrev r : R₀ c D ⧸ IR I c D :=
  Ideal.Quotient.mk _ (algebraMap (AdjoinRoot (QuadraticEtale.poly c)) (R₀ c D)
    (AdjoinRoot.root _))

/-- `A[S]/(S² + S − c') → R₀/I`. -/
def gQ : QuadNode.Q π e (nodeMap I π e h c) →+* R₀ c D ⧸ IR I c D :=
  AdjoinRoot.lift (gN I π e h c D) (r I c D) (by
    rw [← map_poly, Polynomial.eval₂_map, gN_nodeMap]
    have h0 := AdjoinRoot.eval₂_root (QuadraticEtale.poly c)
    have := congrArg ((Ideal.Quotient.mk (IR I c D)).comp
      (algebraMap (AdjoinRoot (QuadraticEtale.poly c)) (R₀ c D))) h0
    rw [map_zero, Polynomial.hom_eval₂] at this
    exact this)

lemma gQ_of (x : A π e) : gQ I π e h c D (AdjoinRoot.of _ x) = gN I π e h c D x :=
  AdjoinRoot.lift_of _

lemma gQ_root : gQ I π e h c D (AdjoinRoot.root _) = r I c D := AdjoinRoot.lift_root _

/-- The inverse map `R → R₀/I`. -/
def bwd : Rlev I π e h c D →+* R₀ c D ⧸ IR I c D :=
  IsLocalization.Away.lift (AdjoinRoot.of _ (nodeMap I π e h D)) (g := gQ I π e h c D) (by
    rw [gQ_of]
    have := RingHom.congr_fun (gN_nodeMap I π e h c D) D
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this]
    exact (IsLocalization.Away.algebraMap_isUnit (AdjoinRoot.of _ D)).map (Ideal.Quotient.mk _))

lemma bwd_algebraMap (x : QuadNode.Q π e (nodeMap I π e h c)) :
    bwd I π e h c D (algebraMap _ _ x) = gQ I π e h c D x :=
  IsLocalization.Away.lift_eq _ _ _

lemma fwd_gO (x : O ⧸ I) : fwd I π e h c D (gO I c D x) = algebraMap (O ⧸ I) _ x := by
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [gO, Ideal.Quotient.lift_mk, RingHom.comp_apply, fwd, Ideal.Quotient.lift_mk,
    fwd₀_algebraMap_O, IsScalarTower.algebraMap_apply O (O ⧸ I) (Rlev I π e h c D),
    Ideal.Quotient.algebraMap_eq]

lemma fwd_ι (x : Node O a) :
    fwd I π e h c D (ι I c D x) = algebraMap (A π e) _ (nodeMap I π e h x) := by
  rw [RingHom.comp_apply, fwd, Ideal.Quotient.lift_mk, RingHom.comp_apply, fwd₀_algebraMap,
    qMap_of]
  exact (IsScalarTower.algebraMap_apply (A π e) (QuadNode.Q π e (nodeMap I π e h c))
    (Rlev I π e h c D) _).symm

lemma bwd_algebraMap_A (x : A π e) :
    bwd I π e h c D (algebraMap (A π e) _ x) = gN I π e h c D x := by
  rw [IsScalarTower.algebraMap_apply (A π e) (QuadNode.Q π e (nodeMap I π e h c))
    (Rlev I π e h c D), bwd_algebraMap]
  exact gQ_of I π e h c D x

lemma nodeMap_u : nodeMap I π e h (Node.u a) = Node.u _ := Node.lift_u ..

lemma nodeMap_v : nodeMap I π e h (Node.v a) = Node.v _ := Node.lift_v ..

set_option maxHeartbeats 800000 in
-- the ring-hom extensionality goals unfold large quotient/localization types
lemma bwd_fwd : (bwd I π e h c D).comp (fwd I π e h c D) = RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (IsLocalization.ringHom_ext
    (Submonoid.powers (AdjoinRoot.of (QuadraticEtale.poly c) D)) (AdjoinRoot.ringHom_ext ?_ ?_))
  · refine Node.ringHom_ext (RingHom.ext fun o ↦ ?_) ?_ ?_
    · change bwd I π e h c D (fwd I π e h c D (ι I c D (algebraMap O _ o))) =
        ι I c D (algebraMap O _ o)
      rw [fwd_ι, AlgHom.commutes, IsScalarTower.algebraMap_apply O (O ⧸ I) (A π e),
        bwd_algebraMap_A, gN_algebraMap]
      exact (ι_algebraMap I c D o).symm
    · change bwd I π e h c D (fwd I π e h c D (ι I c D (Node.u a))) = ι I c D (Node.u a)
      rw [fwd_ι, bwd_algebraMap_A, nodeMap_u, gN_u]
    · change bwd I π e h c D (fwd I π e h c D (ι I c D (Node.v a))) = ι I c D (Node.v a)
      rw [fwd_ι, bwd_algebraMap_A, nodeMap_v, gN_v]
  · change bwd I π e h c D (fwd₀ I π e h c D (algebraMap (AdjoinRoot (QuadraticEtale.poly c))
      (R₀ c D) (AdjoinRoot.root (QuadraticEtale.poly c)))) = r I c D
    rw [fwd₀_algebraMap, qMap_root, bwd_algebraMap, gQ_root]

set_option maxHeartbeats 800000 in
-- the ring-hom extensionality goals unfold large quotient/localization types
lemma fwd_bwd : (fwd I π e h c D).comp (bwd I π e h c D) = RingHom.id _ := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (AdjoinRoot.of (QuadraticEtale.poly (nodeMap I π e h c)) (nodeMap I π e h D)))
    (AdjoinRoot.ringHom_ext ?_ ?_)
  · refine Node.ringHom_ext (RingHom.ext fun x ↦ ?_) ?_ ?_
    · change fwd I π e h c D (bwd I π e h c D (algebraMap (A π e) _ (algebraMap (O ⧸ I) _ x))) =
        algebraMap (A π e) (Rlev I π e h c D) (algebraMap (O ⧸ I) _ x)
      rw [bwd_algebraMap_A, gN_algebraMap, fwd_gO]
      exact IsScalarTower.algebraMap_apply (O ⧸ I) (A π e) (Rlev I π e h c D) x
    · change fwd I π e h c D (bwd I π e h c D (algebraMap (A π e) _ (Node.u (π ^ e)))) =
        algebraMap (A π e) (Rlev I π e h c D) (Node.u (π ^ e))
      rw [bwd_algebraMap_A, gN_u, fwd_ι, nodeMap_u]
    · change fwd I π e h c D (bwd I π e h c D (algebraMap (A π e) _ (Node.v (π ^ e)))) =
        algebraMap (A π e) (Rlev I π e h c D) (Node.v (π ^ e))
      rw [bwd_algebraMap_A, gN_v, fwd_ι, nodeMap_v]
  · change fwd I π e h c D (bwd I π e h c D (algebraMap (QuadNode.Q π e (nodeMap I π e h c))
      (Rlev I π e h c D) (AdjoinRoot.root _))) =
      algebraMap (QuadNode.Q π e (nodeMap I π e h c)) (Rlev I π e h c D) (AdjoinRoot.root _)
    rw [bwd_algebraMap, gQ_root]
    change fwd₀ I π e h c D _ = _
    rw [fwd₀_algebraMap, qMap_root]

/-- **The level-`N` chart is a quadratic node chart over `A π e`:** `R₀/IR₀ ≃+* R`. -/
def equiv : R₀ c D ⧸ IR I c D ≃+* Rlev I π e h c D :=
  RingEquiv.ofRingHom (fwd I π e h c D) (bwd I π e h c D) (fwd_bwd I π e h c D)
    (bwd_fwd I π e h c D)

lemma equiv_apply (x : R₀ c D ⧸ IR I c D) : equiv I π e h c D x = fwd I π e h c D x := rfl

/-- Compatibility with the node rings: `A₀ → R₀/I → R` is `A₀ → A π e → R`. -/
theorem equiv_algebraMap (x : Node O a) :
    equiv I π e h c D (ι I c D x) = algebraMap (A π e) (Rlev I π e h c D) (nodeMap I π e h x) := by
  rw [equiv_apply, fwd_ι]

end

end QuadNodeLevel

end SemistableReduction
