/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeBalancedTransport
import TemperedFundamentalGroups.SemistableReduction.NodeNormalForm

/-!
# The balance condition from twists on the pieces (MR12 I5(b), generic)

For a map `Φ` of node factors of two admissible coverings of a `k`-algebra chart
(`(R̂/(1 − ε)) ⊗_{k[u,v]/(uv)} k[s,t]/(st)`):

* `AdmissibleLift.NodeHom.pow_s`: `s^e = φ(u)` in a piece of degree `e`; hence
  (**`pow_map_single_s`**) `Φ(s_j)_{j'}^{e} = s'^{e'} Φ(1_j)_{j'}` when the formal node coordinates
  agree, and (**`dvd_of_map_single_ne_zero`**, `NodeNormalForm.eq_zero_or_dvd`) `e ∣ e'` whenever
  `Φ(1_j)_{j'} ≠ 0`, given the node normal form hypotheses on the target pieces;
* **`AdmissibleLift.NodeHom.balancedK_of_twist`**: if moreover on every pair of pieces with
  `Φ(1_j)_{j'} ≠ 0` there is `ζ` with `ζ^e = 1`, `Φ(s) = Φ(1) ζ s'^{e'/e}`,
  `Φ(t) = Φ(1) ζ^{e−1} t'^{e'/e}`, and `πL j = πL' j'^{e'/e}`, then `Φ` is balanced at the special
  chart (`NodeHom.BalancedK`, with all deformation ratios `η = 1`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace AdmissibleLift

namespace NodeHom

variable {k : Type u} [Field k] {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}

/-- `s^e = φ(u)` in a Kummer piece of degree `e`. -/
lemma pow_s (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀) (ε : Admissible.Hat f₀) {e : ℕ}
    (he : 0 < e) :
    ((1 : Admissible.PieceBase φ ε he) ⊗ₜ[KummerEtale.A (0 : k) e] Node.u (0 : k)) ^ e =
      algebraMap (Admissible.Hat f₀) (Admissible.KummerPiece φ ε he) (φ (Node.u (0 : k))) := by
  have h1 : (Node.u (0 : k)) ^ e = algebraMap (KummerEtale.A (0 : k) e) (KummerEtale.B (0 : k))
      (Node.u _) := (Node.kummer_u (0 : k) e).symm
  have h2 : algebraMap (KummerEtale.A (0 : k) e) (Admissible.PieceBase φ ε he) (Node.u _) =
      algebraMap (Admissible.Hat f₀) (Admissible.PieceBase φ ε he) (φ (Node.u (0 : k))) := by
    change Ideal.Quotient.mk _ (φ (Admissible.nodeCongr he (Node.u _))) = _
    rw [Admissible.nodeCongr, AlgEquiv.ofAlgHom_apply, Node.lift_u]
    rfl
  rw [Algebra.TensorProduct.tmul_pow, one_pow, h1, Algebra.algebraMap_eq_smul_one,
    ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, h2,
    Algebra.TensorProduct.algebraMap_apply]

/-- `t^e = φ(v)` in a Kummer piece of degree `e`. -/
lemma pow_t (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀) (ε : Admissible.Hat f₀) {e : ℕ}
    (he : 0 < e) :
    ((1 : Admissible.PieceBase φ ε he) ⊗ₜ[KummerEtale.A (0 : k) e] Node.v (0 : k)) ^ e =
      algebraMap (Admissible.Hat f₀) (Admissible.KummerPiece φ ε he) (φ (Node.v (0 : k))) := by
  have h1 : (Node.v (0 : k)) ^ e = algebraMap (KummerEtale.A (0 : k) e) (KummerEtale.B (0 : k))
      (Node.v _) := (Node.kummer_v (0 : k) e).symm
  have h2 : algebraMap (KummerEtale.A (0 : k) e) (Admissible.PieceBase φ ε he) (Node.v _) =
      algebraMap (Admissible.Hat f₀) (Admissible.PieceBase φ ε he) (φ (Node.v (0 : k))) := by
    change Ideal.Quotient.mk _ (φ (Admissible.nodeCongr he (Node.v _))) = _
    rw [Admissible.nodeCongr, AlgEquiv.ofAlgHom_apply, Node.lift_v]
    rfl
  rw [Algebra.TensorProduct.tmul_pow, one_pow, h1, Algebra.algebraMap_eq_smul_one,
    ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, h2,
    Algebra.TensorProduct.algebraMap_apply]

lemma pi_single_pow {ι : Type*} [DecidableEq ι] {P : ι → Type*} [∀ i, Semiring (P i)] (i : ι)
    (x : P i) {n : ℕ} (hn : 0 < n) : (Pi.single i x : ∀ i, P i) ^ n = Pi.single i (x ^ n) := by
  funext i'
  rw [Pi.pow_apply]
  rcases eq_or_ne i' i with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_pow hn.ne']

variable {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov : Admissible.Covering φ₀ ψ₀} {cov' : Admissible.Covering φ₀' ψ₀'} [DecidableEq cov.ι]
  (Φ : (∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) →ₐ[Admissible.Hat f₀]
      ∀ j', Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j'))

lemma map_single_eq_zero (j : cov.ι) (j' : cov'.ι) (h : Φ (Pi.single j 1) j' = 0)
    (x : Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) : Φ (Pi.single j x) j' = 0 := by
  rw [show (Pi.single j x : ∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) =
    Pi.single j 1 * Pi.single j x by rw [← Pi.single_mul, one_mul], map_mul, Pi.mul_apply, h,
    zero_mul]

lemma map_single_smul (j : cov.ι) (j' : cov'.ι) (a : Admissible.Hat f₀) :
    Φ (Pi.single j (algebraMap _ _ a)) j' =
      algebraMap _ _ a * Φ (Pi.single j 1) j' := by
  have h : (Pi.single j (algebraMap _ _ a) : ∀ j, Admissible.KummerPiece φ₀ (cov.idem j)
      (cov.e_pos j)) = algebraMap _ _ a * Pi.single j 1 := by
    funext i
    rw [Pi.mul_apply, Pi.algebraMap_apply]
    rcases eq_or_ne i j with rfl | h
    · rw [Pi.single_eq_same, Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]
  rw [h, map_mul, AlgHom.commutes, Pi.mul_apply, Pi.algebraMap_apply]

/-- `Φ(s_j)_{j'}^e = s'^{e'} Φ(1_j)_{j'}` (equal formal node coordinates). -/
lemma pow_map_single_s (hφ : φ₀ (Node.u (0 : k)) = φ₀' (Node.u (0 : k))) (j : cov.ι)
    (j' : cov'.ι) :
    Φ (Pi.single j ((1 : Admissible.PieceBase φ₀ (cov.idem j) (cov.e_pos j)) ⊗ₜ
        Node.u (0 : k))) j' ^ cov.e j =
      ((1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ Node.u (0 : k)) ^
        cov'.e j' * Φ (Pi.single j 1) j' := by
  rw [← Pi.pow_apply, ← map_pow, pi_single_pow _ _ (cov.e_pos j), pow_s, map_single_smul,
    pow_s, hφ]

/-- **`Φ(1_j)_{j'} ≠ 0` forces `e ∣ e'`** (node normal form hypotheses on the target pieces). -/
theorem dvd_of_map_single_ne_zero (hφ : φ₀ (Node.u (0 : k)) = φ₀' (Node.u (0 : k)))
    (hinter : ∀ j' (z : Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j')),
      z ∈ Ideal.span {(1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ
        Node.u (0 : k)} →
      z ∈ Ideal.span {(1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ
        Node.v (0 : k)} → z = 0)
    (hs : ∀ j', CuspHom.NFHyp (Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j') ⧸
        Ideal.span {(1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ
          Node.v (0 : k)})
      (Ideal.Quotient.mk _ ((1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ
        Node.u (0 : k))))
    (ht : ∀ j', CuspHom.NFHyp (Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j') ⧸
        Ideal.span {(1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ
          Node.u (0 : k)})
      (Ideal.Quotient.mk _ ((1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ
        Node.v (0 : k))))
    (j : cov.ι) (j' : cov'.ι) (h : Φ (Pi.single j 1) j' ≠ 0) : cov.e j ∣ cov'.e j' := by
  have hE : IsIdempotentElem (Φ (Pi.single j 1) j') := by
    change Φ (Pi.single j 1) j' * Φ (Pi.single j 1) j' = Φ (Pi.single j 1) j'
    rw [← Pi.mul_apply, ← map_mul, ← Pi.single_mul, one_mul]
  exact (NodeNormalForm.eq_zero_or_dvd (hinter j') (hs j') (ht j') (cov.e_pos j) hE
    (pow_map_single_s Φ hφ j j')).resolve_left h

/-- **Balance at the special chart from twists on the pieces** (all `η = 1`). -/
theorem balancedK_of_twist {O : Type u} [CommRing O] (θ : O →+* k) (πL : cov.ι → O)
    (πL' : cov'.ι → O)
    (hdvd : ∀ j j', Φ (Pi.single j 1) j' ≠ 0 → cov.e j ∣ cov'.e j')
    (hπ : ∀ j j', cov.e j ∣ cov'.e j' → πL j = πL' j' ^ (cov'.e j' / cov.e j))
    (htw : ∀ j j', Φ (Pi.single j 1) j' ≠ 0 →
      ∃ ζ : Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j'), ζ ^ cov.e j = 1 ∧
        Φ (Pi.single j ((1 : Admissible.PieceBase φ₀ (cov.idem j) (cov.e_pos j)) ⊗ₜ
            Node.u (0 : k))) j' = Φ (Pi.single j 1) j' * ζ *
          ((1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ Node.u (0 : k)) ^
            (cov'.e j' / cov.e j) ∧
        Φ (Pi.single j ((1 : Admissible.PieceBase φ₀ (cov.idem j) (cov.e_pos j)) ⊗ₜ
            Node.v (0 : k))) j' = Φ (Pi.single j 1) j' * ζ ^ (cov.e j - 1) *
          ((1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ Node.v (0 : k)) ^
            (cov'.e j' / cov.e j)) :
    BalancedK θ πL πL' Φ := by
  classical
  intro j
  have key : ∀ j', ∃ ζ : Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j'),
      ζ ^ cov.e j = 1 ∧ (Φ (Pi.single j 1) j' ≠ 0 →
        Φ (Pi.single j ((1 : Admissible.PieceBase φ₀ (cov.idem j) (cov.e_pos j)) ⊗ₜ
            Node.u (0 : k))) j' = Φ (Pi.single j 1) j' * ζ *
          ((1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ Node.u (0 : k)) ^
            (cov'.e j' / cov.e j) ∧
        Φ (Pi.single j ((1 : Admissible.PieceBase φ₀ (cov.idem j) (cov.e_pos j)) ⊗ₜ
            Node.v (0 : k))) j' = Φ (Pi.single j 1) j' * ζ ^ (cov.e j - 1) *
          ((1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ Node.v (0 : k)) ^
            (cov'.e j' / cov.e j)) := fun j' ↦ by
    by_cases h : Φ (Pi.single j 1) j' = 0
    · exact ⟨1, one_pow _, fun h' ↦ absurd h h'⟩
    · obtain ⟨ζ, h1, h2, h3⟩ := htw j j' h
      exact ⟨ζ, h1, fun _ ↦ ⟨h2, h3⟩⟩
  choose ζ hζ using key
  refine ⟨ζ, fun _ ↦ 1, funext fun j' ↦ (hζ j').1, fun j' hj' ↦ ⟨hdvd j j' hj', ?_, one_pow _⟩,
    funext fun j' ↦ ?_, funext fun j' ↦ ?_⟩
  · rw [one_mul]
    exact hπ j j' (hdvd j j' hj')
  · simp only [Pi.mul_apply]
    by_cases h : Φ (Pi.single j 1) j' = 0
    · rw [map_single_eq_zero Φ j j' h, h, zero_mul, zero_mul]
    · exact ((hζ j').2 h).1
  · simp only [Pi.mul_apply, Pi.pow_apply, map_one, one_mul]
    by_cases h : Φ (Pi.single j 1) j' = 0
    · rw [map_single_eq_zero Φ j j' h, h, zero_mul, zero_mul]
    · exact ((hζ j').2 h).2

end NodeHom

end AdmissibleLift

end SemistableReduction
