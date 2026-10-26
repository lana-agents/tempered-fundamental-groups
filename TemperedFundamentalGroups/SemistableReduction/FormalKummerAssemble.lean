/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerNode
import TemperedFundamentalGroups.SemistableReduction.CompletionProd

/-!
# Assembling the formal Kummer form along `V(f)` (MR12 T2 S5.4, assembly)

Let `R` be a Noetherian `k`-algebra (the special fibre of a chart), `f ∈ R` whose zero set
`V(f)` consists of finitely many maximal ideals `𝔪ⱼ` (the nodes), `φ : k[u,v]/(uv) → R̂` the formal
node coordinates `u ↦ x`, `v ↦ y` (`x, y ∈ R`, `x y = 0`), and `C` an `R`-algebra. Suppose that at
every node, `R̂_{𝔪ⱼ} ⊗_R C ≅ ∏ᵢ R̂_{𝔪ⱼ} ⊗_{k[u,v]/(uv)} k[s,t]/(st)` (`u ↦ x ↦ s^{dⱼᵢ}`, as
produced by `FormalKummer.nodeEquiv`). Then (**`FormalKummer.assembleEquiv`**)

  `R̂ ⊗_R C ≅ ∏_{(j, i)} (R̂/(1 − εⱼ)) ⊗_{k[u,v]/(uv)} k[s,t]/(st)`

as `R̂`-algebras, with `R̂` the `f`-adic completion and `εⱼ` the idempotents of the nodes
(`CompletionProd.idem`): the right side is `∏ Admissible.KummerPiece φ εⱼ`, the formally Kummer
condition of an admissible covering (`Admissible.Covering.kummer`). Proof: `R̂ ≅ ∏ⱼ R̂_{𝔪ⱼ}` and
`R̂/(1 − εⱼ) ≅ R̂_{𝔪ⱼ}` (`CompletionProd.equiv`, `quotEquiv`), tensor products commute with finite
products, and the node coordinates correspond (`quotEquiv_nodeMap`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale

namespace FormalKummer

noncomputable section

/-- Currying of a product of rings over a sigma type. -/
def piCurryRingEquiv {ι : Type*} {κ : ι → Type*} (P : (j : ι) → κ j → Type*)
    [∀ j i, Semiring (P j i)] :
    (∀ j i, P j i) ≃+* ∀ p : (Σ j, κ j), P p.1 p.2 where
  toEquiv := (Equiv.piCurry P).symm
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
  {f : R} {ι : Type} [Finite ι] [DecidableEq ι] {𝔪 : ι → Ideal R} [∀ j, (𝔪 j).IsMaximal]
  (hinj : Function.Injective 𝔪) (hf : ∀ j, f ∈ 𝔪 j)
  (hrad : ⨅ j, 𝔪 j ≤ (Ideal.span {f}).radical)
  {x y : R} (hxy : x * y = 0) (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
  (hφu : φ (Node.u _) = algebraMap R _ x) (hφv : φ (Node.v _) = algebraMap R _ y)

/-- The completion at the node `j`. -/
abbrev T (𝔪 : ι → Ideal R) (j : ι) : Type u := AdicCompletion (𝔪 j) R

/-- The `f`-adic completion as an `R`-algebra product of the completions at the nodes. -/
def hatEquiv : Admissible.Hat f ≃ₐ[R] ∀ j, T 𝔪 j :=
  AlgEquiv.ofRingEquiv (f := CompletionProd.equiv hinj hf hrad) fun r ↦ by
    rw [CompletionProd.equiv_algebraMap]
    rfl

include hφu hφv in
/-- The node coordinates of `R̂/(1 − εⱼ)` correspond to the chart map at the node. -/
lemma quotEquiv_nodeMap (j : ι) {e : ℕ} (he : 0 < e) (a : A (0 : k) e) :
    CompletionProd.quotEquiv hinj hf hrad j
      (Admissible.PieceBase.nodeMap φ (CompletionProd.idem hinj hf hrad j) he a) =
      algebraMap R (T 𝔪 j) (chartMap hxy he a) := by
  have := Node.ringHom_ext (O := k) (a := (0 : k) ^ e)
    (f := (CompletionProd.quotEquiv hinj hf hrad j).toRingHom.comp
      (Admissible.PieceBase.nodeMap φ (CompletionProd.idem hinj hf hrad j) he))
    (g := (algebraMap R (T 𝔪 j)).comp (chartMap hxy he).toRingHom)
    (RingHom.ext fun c ↦ by
      change CompletionProd.quotEquiv hinj hf hrad j (Ideal.Quotient.mk _
        (φ (Admissible.nodeCongr he (algebraMap k _ c)))) =
          algebraMap R (T 𝔪 j) (chartMap hxy he (algebraMap k _ c))
      rw [AlgEquiv.commutes, AlgHom.commutes, AlgHom.commutes,
        IsScalarTower.algebraMap_apply k R (Admissible.Hat f), CompletionProd.quotEquiv_mk,
        CompletionMap.map_algebraMap]
      rfl)
    (by
      change CompletionProd.quotEquiv hinj hf hrad j (Ideal.Quotient.mk _
        (φ (Admissible.nodeCongr he (Node.u _)))) =
          algebraMap R (T 𝔪 j) (chartMap hxy he (Node.u _))
      rw [NodeChart.nodeCongr_u, hφu, chartMap_u, CompletionProd.quotEquiv_mk,
        CompletionMap.map_algebraMap]
      rfl)
    (by
      change CompletionProd.quotEquiv hinj hf hrad j (Ideal.Quotient.mk _
        (φ (Admissible.nodeCongr he (Node.v _)))) =
          algebraMap R (T 𝔪 j) (chartMap hxy he (Node.v _))
      rw [NodeChart.nodeCongr_v, hφv, chartMap_v, CompletionProd.quotEquiv_mk,
        CompletionMap.map_algebraMap]
      rfl)
  exact RingHom.congr_fun this a

variable {C : Type u} [CommRing C] [Algebra R C] {r : ι → ℕ} {d : ∀ j, Fin (r j) → ℕ}
  (hd : ∀ j i, 0 < d j i)

include hφu hφv in
/-- `R̂_{𝔪ⱼ} ≅ R̂/(1 − εⱼ)` as algebras over the node ring. -/
def pieceEquiv (j : ι) (i : Fin (r j)) :
    letI := chartAlg (k := k) hxy (hd j i) (T 𝔪 j)
    T 𝔪 j ≃ₐ[A (0 : k) (d j i)]
      Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) (hd j i) :=
  letI := chartAlg (k := k) hxy (hd j i) (T 𝔪 j)
  AlgEquiv.ofRingEquiv (f := (CompletionProd.quotEquiv hinj hf hrad j).symm) fun a ↦ by
    exact (RingEquiv.symm_apply_eq _).mpr
      (quotEquiv_nodeMap hinj hf hrad hxy φ hφu hφv j (hd j i) a).symm

/-- `(∏ⱼ Tⱼ) ⊗_R C ≅ ∏ⱼ Tⱼ ⊗_R C`. -/
def piLeftEquiv [Fintype ι] : (∀ j, T 𝔪 j) ⊗[R] C ≃ₐ[R] ∀ j, T 𝔪 j ⊗[R] C :=
  (Algebra.TensorProduct.comm R _ C).trans
    ((Algebra.TensorProduct.piRight R R C (T 𝔪)).trans
      (AlgEquiv.piCongrRight fun j ↦ Algebra.TensorProduct.comm R C (T 𝔪 j)))

omit [IsNoetherianRing R] [∀ j, (𝔪 j).IsMaximal] [Finite ι] in
lemma piLeftEquiv_tmul [Fintype ι] (t : ∀ j, T 𝔪 j) (c : C) :
    piLeftEquiv (C := C) (t ⊗ₜ c) = fun j ↦ t j ⊗ₜ c := rfl

/-- **The formal Kummer form along `V(f)`**, assembled from the formal Kummer forms at the
nodes. -/
def assembleEquiv [Fintype ι]
    (Ψ : ∀ j, letI : ∀ i, Algebra (A (0 : k) (d j i)) (T 𝔪 j) := fun i ↦
        chartAlg (k := k) hxy (hd j i) (T 𝔪 j)
      T 𝔪 j ⊗[R] C ≃ₐ[T 𝔪 j] ∀ i, T 𝔪 j ⊗[A (0 : k) (d j i)] B (0 : k)) :
    Admissible.Hat f ⊗[R] C ≃ₐ[Admissible.Hat f]
      ∀ p : (Σ j, Fin (r j)), Admissible.KummerPiece φ (CompletionProd.idem hinj hf hrad p.1)
        (hd p.1 p.2) :=
  AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.congr (hatEquiv hinj hf hrad) AlgEquiv.refl).trans
      piLeftEquiv).toRingEquiv.trans
      ((RingEquiv.piCongrRight fun j ↦ (Ψ j).toRingEquiv).trans
        ((RingEquiv.piCongrRight fun j ↦ RingEquiv.piCongrRight fun i ↦
          letI := chartAlg (k := k) hxy (hd j i) (T 𝔪 j)
          (Algebra.TensorProduct.congr (pieceEquiv hinj hf hrad hxy φ hφu hφv hd j i)
            (AlgEquiv.refl (R := A (0 : k) (d j i)) (A₁ := B (0 : k)))).toRingEquiv).trans
          (piCurryRingEquiv _)))) (by
    intro h
    funext p
    obtain ⟨j, i⟩ := p
    letI : ∀ i, Algebra (A (0 : k) (d j i)) (T 𝔪 j) := fun i ↦
      chartAlg (k := k) hxy (hd j i) (T 𝔪 j)
    have h1 : (Ψ j) (hatEquiv hinj hf hrad h j ⊗ₜ (1 : C)) =
        algebraMap (T 𝔪 j) _ (hatEquiv hinj hf hrad h j) := by
      rw [← (Ψ j).commutes]
      rfl
    have h2 : (CompletionProd.quotEquiv hinj hf hrad j).symm (hatEquiv hinj hf hrad h j) =
        Ideal.Quotient.mk _ h := by
      refine (RingEquiv.symm_apply_eq _).mpr ?_
      rw [CompletionProd.quotEquiv_mk]
      rfl
    change (Algebra.TensorProduct.congr (pieceEquiv hinj hf hrad hxy φ hφu hφv hd j i)
      AlgEquiv.refl) ((Ψ j) (hatEquiv hinj hf hrad h j ⊗ₜ (1 : C)) i) = _
    rw [h1]
    change (Algebra.TensorProduct.congr (pieceEquiv hinj hf hrad hxy φ hφu hφv hd j i)
      AlgEquiv.refl) (hatEquiv hinj hf hrad h j ⊗ₜ (1 : B (0 : k))) = _
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    have h3 : (pieceEquiv hinj hf hrad hxy φ hφu hφv hd j i) (hatEquiv hinj hf hrad h j) =
        algebraMap (Admissible.Hat f)
          (Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) (hd j i)) h := h2
    refine (congrArg (fun z ↦ z ⊗ₜ[A (0 : k) (d j i)] (1 : B (0 : k))) h3).trans ?_
    rfl)

end

end FormalKummer

end SemistableReduction
