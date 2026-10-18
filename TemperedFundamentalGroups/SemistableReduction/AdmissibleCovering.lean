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
to arbitrary admissible coverings of the geometric special fibre of the stable model".

**The definition in [Mzk1]** (Mochizuki, *The geometry of the compactification of the Hurwitz
scheme*, Publ. RIMS 31 (1995)): §3.5 defines *log admissible coverings* `π^log : C^log → D^log`
of symmetrically pointed stable log-curves (log étale, finite, of degree `d` on a dense open of
every fibre, `μ_f ⊆ π⁻¹(μ_h) ⊆ d·μ_f` on the marked points, and `C` smooth at `c` iff `D` is
smooth at `π(c)`); §3.6 calls `π` *admissible* if it extends to a log admissible covering étale
locally on the base; §3.11 (Proposition) shows that this is equivalent to the Harris–Mumford form
of §3.9 ("HM-admissible"): conditions (2)–(5) of §3.5 and "`π` is étale, except: (1′A) over `μ_h`,
where it exhibits tame ramification; (1′B) over the singular points: if `s ∈ S`, `λ` is a node of
`C_s`, and `ν = π(λ)`, then there exist `a ∈ m^sh_{S,s}`, `x, y ∈ m^sh_{C,λ}`, and
`u, v ∈ m^sh_{D,ν}`, such that `xy = a`, `uv = a^e`, `u = x^e`, `v = y^e` (for some natural number
`e` … such that `e ∈ O^×_{S,s}`) and such that `x, y` (respectively, `u, v`) generate
`m^sh_{f⁻¹(s),λ}` (respectively, `m^sh_{h⁻¹(s),ν}`)", `m^sh` the maximal ideal of the strict
henselization. By §3.9, Remark 1 (with Lemma §3.7: two node coordinate pairs differ by units, up
to swapping) the condition does not depend on the coordinates `u, v` chosen downstairs, because
`e`-th roots of units exist in the strict henselization; §3.23 gives the resulting completed local
rings `O[D][{t_{i,j}}]/(t_{i,j}^{e_{i,j}} − t_i)` of the moduli stack.

**Our chart-wise form** (no valuations, no log structures): a chart is a ring `R` over a field
`k`, an element `f ∈ R` cutting out the nodes **and the marked points** of the chart, formal node
coordinates `φ : k[u, v]/(uv) → R̂` and a formal coordinate `ψ : k[t] → R̂` at the marked points,
`R̂` the `f`-adic completion. An admissible covering of the chart (`Admissible.Covering`) is

* a finite `R`-algebra `C` ((2) of [Mzk1] §3.5),
* étale over `D(f)` (`R_f → C_f` étale: (1′) away from nodes and marked points),
* **formally Kummer along `V(f)`**: an `R̂`-algebra isomorphism
  `R̂ ⊗_R C ≅ ∏_j (R̂/(1 − ε_j)) ⊗_{k[u,v]/(uv)} k[s,t]/(st)
  × ∏_i (R̂/(1 − δ_i))[t']/(t'^{e'_i} − t)`
  (`u ↦ s^{e_j}`, `v ↦ t^{e_j}`) for idempotents `ε_j`, `δ_i` of `R̂` and indices `e_j`, `e'_i`
  invertible in `k`: (1′B) at the nodes, with the same index `e_j` on both branches, and the tame
  ramification (1′A) over the marked points.

**Comparison with [Mzk1]** (`S = Spec k`, so `a = 0`). The local form at the nodes is (1′B) with
`x = s`, `y = t`, and at the marked points the formal form of tame ramification. The differences:

* [Mzk1] works in the strict henselization, so it allows *unit twists* `u = c·x^e` and *separable
  residue field extensions* at the nodes and marked points; we require the split form with respect
  to the **given** coordinates `φ`, `ψ`. Twists by units `≡ 1` along `V(f)` are absorbed by `e`-th
  roots (Hensel, `e` invertible, `R̂` complete); the remaining twists by constants and the residue
  field extensions disappear after a finite separable extension `k'/k`. So for `k` separably closed
  (the *geometric* special fibre, which is what [SemiAnbd] Ex. 5.6 and [IUTchI] Cor. 3.9 use) the
  two notions agree, and in general an [Mzk1]-admissible covering is split admissible after a
  finite separable constant extension (a constant-field level of the tower). This equivalence is
  not formalized.
* Conditions (3) (constant degree), (5) (nodes lie exactly over nodes) and the global stability of
  `C` are not part of the chart-wise notion; (5) for the chart follows from the Kummer form and
  étaleness over `D(f)`.

The Kummer factor at a node is `KummerEtale.B 0` over `KummerEtale.A 0 e` (the case `π = 0` of the
Kummer covering of the node, whose deformations over `O/ϖⁿ⁺¹` are `KummerEtale.B π` over
`KummerEtale.A π e` with `π^e = ϖ^m`); the factor at a marked point is
`AdjoinRoot (X^e − t)` over `R̂/(1 − δ)`.

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

/-- The **cusp factor** `(R̂/(1 − δ))[t']/(t'^e − t)`, `t = ψ(X)` the formal coordinate at the
marked points: the formal local model of a covering tamely ramified with index `e` over the marked
points selected by `δ` ([Mzk1] §3.9, (1′A)). -/
abbrev CuspPiece (ψ : Polynomial k →ₐ[k] Hat f) (δ : Hat f) (e : ℕ) : Type u :=
  AdjoinRoot (Polynomial.X ^ e -
    Polynomial.C (Ideal.Quotient.mk (Ideal.span {1 - δ}) (ψ Polynomial.X)))

/-- **An admissible covering of a pointed nodal chart** `(R, f, φ, ψ)` (see the module docstring;
[Mzk1] §3.5, §3.9, §3.11; [SemiAnbd], Example 3.10, Corollary 3.11): a finite `R`-algebra `C`,
étale over `D(f)` (the complement of the nodes and marked points), and formally Kummer along
`V(f)`: at the nodes with the same ramification index `e_j` on both branches of each Kummer
factor, at the marked points tamely ramified with index `e'_i`. For a chart without marked points
take `κ` empty. -/
structure Covering (φ : Node k (0 : k) →ₐ[k] Hat f) (ψ : Polynomial k →ₐ[k] Hat f) where
  /-- The ring of the covering over the chart. -/
  C : Type u
  [commRing : CommRing C]
  [algebra : Algebra R C]
  /-- The covering is finite. -/
  finite : Module.Finite R C
  /-- The covering is étale over `D(f)`. -/
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
  /-- The index set of the factors over the marked points. -/
  κ : Type
  [fintypeκ : Fintype κ]
  /-- The idempotent of `R̂` selecting the marked points under the factor `i`. -/
  cidem : κ → Hat f
  isIdempotentElem_cidem : ∀ i, IsIdempotentElem (cidem i)
  /-- The ramification index over the marked points of the factor `i`. -/
  ce : κ → ℕ
  ce_pos : ∀ i, 0 < ce i
  /-- Tameness over the marked points. -/
  ce_ne_zero : ∀ i, (ce i : k) ≠ 0
  /-- **Formally Kummer along `V(f)`.** -/
  kummer : letI := algebra
    (Hat f ⊗[R] C) ≃ₐ[Hat f] (((j : ι) → KummerPiece φ (idem j) (e_pos j)) ×
      ((i : κ) → CuspPiece ψ (cidem i) (ce i)))

attribute [instance] Covering.commRing Covering.algebra Covering.fintype Covering.fintypeκ

end

end Admissible

end SemistableReduction
