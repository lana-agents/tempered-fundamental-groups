/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import TemperedFundamentalGroups.SemistableReduction.KummerNodePunctured

/-!
# Admissible coverings of the special fibre, chart-wise (Blueprint §12.8, M2.3)

The specialization input M2 lifts coverings of the **special fibre** of a semistable model to
coverings of the model. The coverings of the special fibre that occur are the *admissible
coverings*: in [SemiAnbd] (Mochizuki, *Semi-graphs of anabelioids*), Example 3.10, the finite log
étale coverings of the stable model have geometric special fibres giving the semi-graphs of
anabelioids `𝒢_i`, and in the proof of Corollary 3.11 "Galois coverings of degree a `Σ`-integer
are necessarily admissible [cf., e.g., [Mzk1], §3]"; [SemiAnbd], Example 5.6, and [IUTchI],
proof of Corollary 3.9, use "the semi-graph of anabelioids whose finite étale coverings correspond
to arbitrary admissible coverings of the geometric special fibre of the stable model". The
definition itself is in [Mzk1] = Mochizuki, *The geometry of the compactification of the Hurwitz
scheme* (Publ. RIMS 31, 1995), §3 (not in our library; [AbsTopII], §0, cites [Mzk1], §3.23 for
"the well-known structure of admissible coverings at nodes"). Locally it is the Harris–Mumford
notion: a finite morphism of nodal curves, étale over the smooth locus, and at a node formally
(after completion along the node) the Kummer covering

  `k[[u, v]]/(uv) → k[[s, t]]/(st)`, `u = s^e`, `v = t^e`,

with the **same** ramification index `e` (prime to the characteristic) on both branches.

Here this is formalized **scheme-theoretically on an affine chart** (no valuations): a chart is a
ring `R` over a field `k`, an element `f ∈ R` cutting out the nodes of the chart, and formal node
coordinates `φ : k[u, v]/(uv) → R̂`, `R̂` the `f`-adic completion. An admissible covering of the
chart (`Admissible.Covering`) is

* a finite `R`-algebra `C`,
* étale over the smooth locus `D(f)` (`R_f → C_f` étale),
* **formally Kummer at the nodes**: an `R̂`-algebra isomorphism
  `R̂ ⊗_R C ≅ ∏_j (R̂/(1 − ε_j)) ⊗_{k[u,v]/(uv)} k[s,t]/(st)` (`u ↦ s^{e_j}`, `v ↦ t^{e_j}`),
  for idempotents `ε_j` of `R̂` (selecting the nodes over which the branch `j` lies) and indices
  `e_j` invertible in `k`. Each factor is ramified with the same index `e_j` on both branches.

The Kummer factor is `KummerEtale.B 0` over `KummerEtale.A 0 e` (the case `π = 0` of the Kummer
covering of the node, whose deformations over `O/ϖⁿ⁺¹` are `KummerEtale.B π` over
`KummerEtale.A π e` with `π^e = ϖ^m`). The condition is stated with respect to the *given* formal
node coordinates (no twist by units): this is the form in which the coverings of the Tate model
(`x ↦ x^e` and their compositions with étale coverings) arise, and the form needed to deform the
Kummer factors compatibly with `uv = ϖ^m`.

Basic facts: the Kummer factor is torsion free along the node (`u + v` is a nonzerodivisor,
`KummerEtale.eq_zero_of_mul_eq_zero`) and étale over the punctured node
(`KummerEtale.etale_away`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace Admissible

noncomputable section

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] (f : R)

/-- The `f`-adic completion `R̂` of a chart (the formal neighbourhood of its nodes). -/
abbrev Hat : Type u := AdicCompletion (Ideal.span {f}) R

variable {f}

lemma zero_pow_eq {e : ℕ} (he : 0 < e) : (0 : k) ^ e = 0 := zero_pow he.ne'

/-- The node `k[u, v]/(uv − 0^e)` identified with `k[u, v]/(uv)` (for `0 < e`). -/
def nodeCongr {e : ℕ} (he : 0 < e) : KummerEtale.A (0 : k) e ≃ₐ[k] Node k (0 : k) :=
  AlgEquiv.ofAlgHom
    (Node.lift (Node.u _) (Node.v _) ((Node.u_mul_v _).trans (by simp [zero_pow he.ne'])))
    (Node.lift (Node.u _) (Node.v _) ((Node.u_mul_v _).trans (by simp [zero_pow he.ne'])))
    (Node.algHom_ext (by simp) (by simp)) (Node.algHom_ext (by simp) (by simp))

/-- The base `R̂/(1 − ε)` of a Kummer factor: the part of the formal neighbourhood of the nodes
selected by the idempotent `ε`, with the formal node coordinates `φ` (the index `e` only fixes
the algebra structure over `A = k[u,v]/(uv − 0^e)`). -/
def PieceBase (_φ : Node k (0 : k) →ₐ[k] Hat f) (ε : Hat f) {e : ℕ} (_he : 0 < e) : Type u :=
  Hat f ⧸ Ideal.span {1 - ε}

namespace PieceBase

variable (φ : Node k (0 : k) →ₐ[k] Hat f) (ε : Hat f) {e : ℕ} (he : 0 < e)

instance : CommRing (PieceBase φ ε he) := Ideal.Quotient.commRing _

instance : Algebra (Hat f) (PieceBase φ ε he) := Ideal.Quotient.algebra _

/-- The formal node coordinates on `R̂/(1 − ε)`, as a map from `A = k[u,v]/(uv − 0^e)`. -/
def nodeMap : KummerEtale.A (0 : k) e →+* PieceBase φ ε he :=
  ((Ideal.Quotient.mk (Ideal.span {1 - ε})).comp φ.toRingHom).comp
    (nodeCongr he).toAlgHom.toRingHom

instance : Algebra (KummerEtale.A (0 : k) e) (PieceBase φ ε he) := (nodeMap φ ε he).toAlgebra

instance : SMulCommClass (KummerEtale.A (0 : k) e) (Hat f) (PieceBase φ ε he) :=
  ⟨fun a s x ↦ by
    change (nodeMap φ ε he a) * (algebraMap (Hat f) (PieceBase φ ε he) s * x) =
      algebraMap (Hat f) (PieceBase φ ε he) s * ((nodeMap φ ε he a) * x)
    ring⟩

end PieceBase

/-- The **Kummer factor** `(R̂/(1 − ε)) ⊗_{k[u,v]/(uv)} k[s,t]/(st)` with `u ↦ s^e`, `v ↦ t^e`,
the formal local model of an admissible covering over the nodes selected by `ε`. -/
abbrev KummerPiece (φ : Node k (0 : k) →ₐ[k] Hat f) (ε : Hat f) {e : ℕ} (he : 0 < e) : Type u :=
  PieceBase φ ε he ⊗[KummerEtale.A (0 : k) e] KummerEtale.B (0 : k)

/-- **An admissible covering of a nodal chart** `(R, f, φ)` (see the module docstring and
[SemiAnbd], Example 3.10, Corollary 3.11; [Mzk1], §3): a finite `R`-algebra `C`, étale over the
smooth locus `D(f)`, and formally Kummer at the nodes, with the same ramification index `e_j` on
both branches of each Kummer factor. -/
structure Covering (φ : Node k (0 : k) →ₐ[k] Hat f) where
  /-- The ring of the covering over the chart. -/
  C : Type u
  [commRing : CommRing C]
  [algebra : Algebra R C]
  /-- The covering is finite. -/
  finite : Module.Finite R C
  /-- The covering is étale over the smooth locus `D(f)`. -/
  etale : (Localization.awayMap (algebraMap R C) f).Etale
  /-- The index set of the Kummer factors over the nodes. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The idempotent of `R̂` selecting the nodes under the factor `j`. -/
  idem : ι → Hat f
  isIdempotentElem_idem : ∀ j, IsIdempotentElem (idem j)
  /-- The ramification index of the factor `j` (the same on both branches). -/
  e : ι → ℕ
  e_pos : ∀ j, 0 < e j
  /-- Tameness: the ramification indices are invertible in `k`. -/
  e_ne_zero : ∀ j, (e j : k) ≠ 0
  /-- **Formally Kummer at the nodes.** -/
  kummer : letI := algebra
    (Hat f ⊗[R] C) ≃ₐ[Hat f] ((j : ι) → KummerPiece φ (idem j) (e_pos j))

attribute [instance] Covering.commRing Covering.algebra Covering.fintype

end

end Admissible

end SemistableReduction
