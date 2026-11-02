/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeLevelHom

/-!
# Transport of the balance condition to the levels (MR12 I3)

`LevelTower.NodeBalanced hfe πL πL' φ n` is the balance condition (`NodeHom.Balanced`) of the
map of formal node models induced by the transported map `transportMap (hfe n) φ` at level `n`.
Here it is derived from one balance condition at the special chart `(R₀, f₀)`.

* `AdmissibleLift.nodePhiK`: the map of formal node models `kummer' ∘ (R̂₀ ⊗ φ) ∘ kummer⁻¹` of a
  map `φ` of node-only coverings of a `k`-algebra chart `R₀` (the analogue of `nodePhi`).
* `AdmissibleLift.NodeHom.BalancedK θ πL πL' Φ`: the balanced normal form at the special chart,
  with the deformation ratios `η` entering through `θ η ∈ k` (the analogue of
  `NodeHom.Balanced`, where they enter through `ψ θ f (η)`).
* **`AdmissibleLift.balanced_nodePhi_transportMap`**: for `e : R₀ ≃ S/J`, if `nodePhiK φ` is
  balanced at the special chart and `k → S/J` maps `θ o` to the class of `o`, then
  `nodePhi (transportMap h φ)` is balanced.
* **`LevelTower.nodeBalanced_of_balancedK`**: hence `NodeBalanced hfe πL πL' φ n` for all `n`.
-/

universe u

open TensorProduct

namespace SemistableReduction

noncomputable section

namespace AdmissibleLift

/-! ### The map of formal node models at a `k`-algebra chart -/

section Base

variable {k : Type u} [Field k] {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov : Admissible.Covering φ₀ ψ₀} {cov' : Admissible.Covering φ₀' ψ₀'}

/-- The inclusion of the node factors into all factors of a covering without cusp factors. -/
def nodeInclK [IsEmpty cov.κ] :
    (∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) →ₐ[Admissible.Hat f₀]
      ((∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) ×
        (∀ i, Admissible.CuspPiece ψ₀ (cov.cidem i) (cov.ce i))) :=
  (AlgHom.id _ _).prod (AlgHom.pi fun i ↦ isEmptyElim i)

lemma nodeInclK_fst [IsEmpty cov.κ]
    (z : (∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) ×
      (∀ i, Admissible.CuspPiece ψ₀ (cov.cidem i) (cov.ce i))) :
    nodeInclK (cov := cov) z.1 = z :=
  Prod.ext rfl (funext fun i ↦ isEmptyElim i)

/-- **The map of formal node models induced by a map `φc : C → C'` of coverings without cusp
factors** of a `k`-algebra chart: `kummer' ∘ (R̂₀ ⊗ φc) ∘ kummer⁻¹` on the node factors. -/
def nodePhiK [IsEmpty cov.κ] (φc : cov.C →ₐ[R₀] cov'.C) :
    (∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) →ₐ[Admissible.Hat f₀]
      ∀ j', Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j') :=
  (AlgHom.fst _ _ _).comp (cov'.kummer.toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id _ _) φc).comp
      (cov.kummer.symm.toAlgHom.comp nodeInclK)))

lemma nodePhiK_kummer [IsEmpty cov.κ] (φc : cov.C →ₐ[R₀] cov'.C)
    (w : Admissible.Hat f₀ ⊗[R₀] cov.C) :
    nodePhiK φc (cov.kummer w).1 =
      (cov'.kummer (Algebra.TensorProduct.map
        (AlgHom.id (Admissible.Hat f₀) (Admissible.Hat f₀)) φc w)).1 := by
  change (cov'.kummer (Algebra.TensorProduct.map
    (AlgHom.id (Admissible.Hat f₀) (Admissible.Hat f₀)) φc
    (cov.kummer.symm (nodeInclK (cov.kummer w).1)))).1 = _
  rw [nodeInclK_fst, AlgEquiv.symm_apply_apply]

namespace NodeHom

variable {O : Type u} [CommRing O] (θ : O →+* k) [DecidableEq cov.ι]

/-- **Balanced normal form at the special chart** of `Φ` on the source factor `j` (as
`NodeHom.BalancedAt`, with the deformation ratios `η_{j'}` entering through `θ η_{j'} ∈ k`). -/
def BalancedAtK (πL : cov.ι → O) (πL' : cov'.ι → O)
    (Φ : (∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) →ₐ[Admissible.Hat f₀]
      ∀ j', Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j')) (j : cov.ι)
    (ζ : ∀ j', Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j')) (η : cov'.ι → O) :
    Prop :=
  ζ ^ cov.e j = 1 ∧
    (∀ j', Φ (Pi.single j 1) j' ≠ 0 → cov.e j ∣ cov'.e j' ∧
      πL j = η j' * πL' j' ^ (cov'.e j' / cov.e j) ∧ η j' ^ cov.e j = 1) ∧
    Φ (Pi.single j ((1 : Admissible.PieceBase φ₀ (cov.idem j) (cov.e_pos j)) ⊗ₜ
        Node.u (0 : k))) =
      Φ (Pi.single j 1) * ζ * (fun j' ↦
        ((1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ Node.u (0 : k)) ^
          (cov'.e j' / cov.e j)) ∧
    Φ (Pi.single j ((1 : Admissible.PieceBase φ₀ (cov.idem j) (cov.e_pos j)) ⊗ₜ
        Node.v (0 : k))) =
      Φ (Pi.single j 1) * ζ ^ (cov.e j - 1) * (fun j' ↦
        algebraMap (Admissible.Hat f₀) (Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j'))
          (algebraMap k (Admissible.Hat f₀) (θ (η j'))) *
        ((1 : Admissible.PieceBase φ₀' (cov'.idem j') (cov'.e_pos j')) ⊗ₜ Node.v (0 : k)) ^
          (cov'.e j' / cov.e j))

/-- **`Φ` is balanced at the special chart**: it has a balanced normal form on every source
factor. -/
def BalancedK (πL : cov.ι → O) (πL' : cov'.ι → O)
    (Φ : (∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) →ₐ[Admissible.Hat f₀]
      ∀ j', Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j')) : Prop :=
  ∀ j, ∃ ζ η, BalancedAtK θ πL πL' Φ j ζ η

end NodeHom

end Base

/-! ### Transport of the balance condition -/

section Transport

open LevelTower (transportMap)

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {S : Type u} [CommRing S] [Algebra O S] [Algebra k (S ⧸ J θ (R := S))] {g : S}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀} {e : R₀ ≃ₐ[k] (S ⧸ J θ (R := S))}
  (h : e f₀ = fbar θ g)
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}

/-- The image of `η ∈ O` in `R̂' = (S/J)^∧` is `θ η` when `k → S/J` maps `θ o` to `o`. -/
lemma ψ_algebraMap_O
    (hk : ∀ o, algebraMap k (S ⧸ J θ (R := S)) (θ o) = Ideal.Quotient.mk _ (algebraMap O S o))
    (o : O) :
    ψ θ g (algebraMap O (FormalPatchLevel.Hat g) o) =
      algebraMap k (Admissible.Hat (fbar θ g)) (θ o) := by
  rw [IsScalarTower.algebraMap_apply O S (FormalPatchLevel.Hat g), AlgHom.commutes,
    IsScalarTower.algebraMap_apply S (S ⧸ J θ (R := S)), Ideal.Quotient.algebraMap_eq, ← hk,
    ← IsScalarTower.algebraMap_apply]

/-- The index set of the transported covering is the same. -/
instance instDecidableEqTransportι (cov : Admissible.Covering φ₀ ψ₀) [DecidableEq cov.ι] :
    DecidableEq (cov.transport (h := h)).ι :=
  inferInstanceAs (DecidableEq cov.ι)

/-- The transported factors `KummerPiece_j ≃ KummerPiece_j^T`, componentwise. -/
def piEquivT (cov : Admissible.Covering φ₀ ψ₀) :
    (∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) ≃+*
      ∀ j, Admissible.KummerPiece (Admissible.φT (h := h) φ₀) ((cov.transport (h := h)).idem j)
        ((cov.transport (h := h)).e_pos j) :=
  RingEquiv.piCongrRight fun j ↦
    Admissible.kummerPieceEquiv (h := h) φ₀ (cov.idem j) (cov.e_pos j)

lemma piEquivT_apply (cov : Admissible.Covering φ₀ ψ₀)
    (z : ∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j))
    (j : (cov.transport (h := h)).ι) :
    piEquivT h cov z j = Admissible.kummerPieceEquiv (h := h) φ₀ (cov.idem j) (cov.e_pos j) (z j) :=
  rfl

lemma piEquivT_single (cov : Admissible.Covering φ₀ ψ₀) [DecidableEq cov.ι] (j : cov.ι)
    (a : Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) :
    piEquivT h cov (Pi.single j a) = Pi.single (M := fun j : (cov.transport (h := h)).ι ↦
      Admissible.KummerPiece (Admissible.φT (h := h) φ₀) ((cov.transport (h := h)).idem j)
        ((cov.transport (h := h)).e_pos j))
      j (Admissible.kummerPieceEquiv (h := h) φ₀ (cov.idem j) (cov.e_pos j) a) := by
  funext i
  rw [piEquivT_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [Pi.single_eq_same, Pi.single_eq_same]
  · exact (congrArg _ (Pi.single_eq_of_ne
      (M := fun j ↦ Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) hij a)).trans
      ((map_zero _).trans (Pi.single_eq_of_ne (M := fun j : (cov.transport (h := h)).ι ↦
        Admissible.KummerPiece (Admissible.φT (h := h) φ₀) ((cov.transport (h := h)).idem j)
          ((cov.transport (h := h)).e_pos j)) hij _).symm)

lemma kummerPieceEquiv_one_tmul (ε : Admissible.Hat f₀) {n : ℕ} (hn : 0 < n)
    (b : KummerEtale.B (0 : k)) :
    Admissible.kummerPieceEquiv (h := h) φ₀ ε hn
        ((1 : Admissible.PieceBase φ₀ ε hn) ⊗ₜ[KummerEtale.A (0 : k) n] b) =
      (1 : Admissible.PieceBase (Admissible.φT (h := h) φ₀) (Admissible.hatEquiv e h ε) hn) ⊗ₜ
        b := by
  rw [Admissible.kummerPieceEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- The `η`-term of the balanced normal form under the transport. -/
lemma kummerPieceEquiv_eta
    (hk : ∀ o, algebraMap k (S ⧸ J θ (R := S)) (θ o) = Ideal.Quotient.mk _ (algebraMap O S o))
    (ε : Admissible.Hat f₀) {n : ℕ} (hn : 0 < n) (m : ℕ) (o : O) :
    Admissible.kummerPieceEquiv (h := h) φ₀ ε hn
        (algebraMap (Admissible.Hat f₀) (Admissible.KummerPiece φ₀ ε hn)
            (algebraMap k (Admissible.Hat f₀) (θ o)) *
          ((1 : Admissible.PieceBase φ₀ ε hn) ⊗ₜ[KummerEtale.A (0 : k) n] Node.v (0 : k)) ^ m) =
      algebraMap (Admissible.Hat (fbar θ g))
          (Admissible.KummerPiece (Admissible.φT (h := h) φ₀) (Admissible.hatEquiv e h ε) hn)
          (ψ θ g (algebraMap O (FormalPatchLevel.Hat g) o)) *
        ((1 : Admissible.PieceBase (Admissible.φT (h := h) φ₀) (Admissible.hatEquiv e h ε) hn) ⊗ₜ
          Node.v (0 : k)) ^ m := by
  rw [map_mul, map_pow (Admissible.kummerPieceEquiv (h := h) φ₀ ε hn),
    Admissible.kummerPieceEquiv_algebraMap, AlgEquiv.commutes,
    kummerPieceEquiv_one_tmul, ψ_algebraMap_O hk]

/-- `R̂₂ ⊗_{R₂} C ≃ R̂₁ ⊗_{R₁} C` on the transported covering. -/
def tensorEquivT (cov : Admissible.Covering φ₀ ψ₀) :
    Admissible.Hat (fbar θ g) ⊗[S ⧸ J θ (R := S)] (cov.transport (h := h)).C ≃+*
      Admissible.Hat f₀ ⊗[R₀] cov.C :=
  Admissible.tensorEquiv (h := h) e cov.C

lemma tensorEquivT_tmul (cov : Admissible.Covering φ₀ ψ₀) (x : Admissible.Hat (fbar θ g))
    (c : (cov.transport (h := h)).C) :
    tensorEquivT h cov (x ⊗ₜ c) = (Admissible.hatEquiv e h).symm x ⊗ₜ[R₀] @id cov.C c :=
  Admissible.tensorEquiv_tmul e cov.C x c

lemma transport_kummer_eq (cov : Admissible.Covering φ₀ ψ₀)
    (w : Admissible.Hat (fbar θ g) ⊗[S ⧸ J θ (R := S)] (cov.transport (h := h)).C) :
    (cov.transport (h := h)).kummer w =
      Admissible.piecesEquiv (h := h) cov (cov.kummer (tensorEquivT h cov w)) :=
  rfl

/-- `R̂₂ ⊗ C ≃ R̂₁ ⊗ C` commutes with the transported map. -/
lemma tensorEquivT_map (φ : cov₀.C →ₐ[R₀] cov₀'.C)
    (w : Admissible.Hat (fbar θ g) ⊗[S ⧸ J θ (R := S)] (cov₀.transport (h := h)).C) :
    tensorEquivT h cov₀' (Algebra.TensorProduct.map
        (AlgHom.id (Admissible.Hat (fbar θ g)) (Admissible.Hat (fbar θ g)))
        (transportMap h φ) w) =
      Algebra.TensorProduct.map (AlgHom.id (Admissible.Hat f₀) (Admissible.Hat f₀)) φ
        (tensorEquivT h cov₀ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x c =>
    rw [Algebra.TensorProduct.map_tmul, tensorEquivT_tmul, tensorEquivT_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- **`nodePhi` of the transported map is `nodePhiK` transported.** -/
lemma nodePhi_transportMap [IsEmpty cov₀.κ] [IsEmpty (cov₀.transport (h := h)).κ]
    (φ : cov₀.C →ₐ[R₀] cov₀'.C)
    (z : ∀ j, Admissible.KummerPiece φ₀ (cov₀.idem j) (cov₀.e_pos j)) :
    nodePhi (transportMap h φ) (piEquivT h cov₀ z) = piEquivT h cov₀' (nodePhiK φ z) := by
  obtain ⟨w₀, hw₀⟩ := cov₀.kummer.surjective (nodeInclK z)
  obtain ⟨w, rfl⟩ := (tensorEquivT h cov₀).surjective w₀
  have h1 := nodePhi_kummer (transportMap h φ) w
  rw [transport_kummer_eq, hw₀, transport_kummer_eq, tensorEquivT_map] at h1
  refine h1.trans ?_
  change piEquivT h cov₀' (cov₀'.kummer (Algebra.TensorProduct.map
    (AlgHom.id (Admissible.Hat f₀) (Admissible.Hat f₀)) φ (tensorEquivT h cov₀ w))).1 = _
  rw [← nodePhiK_kummer, hw₀]
  rfl

/-- **Transport of the balance condition**: if `nodePhiK φ` is balanced at the special chart
(`BalancedK`) and `k → S/J` maps `θ o` to the class of `o`, then `nodePhi` of the transported
map is balanced. -/
theorem balanced_nodePhi_transportMap
    (hk : ∀ o, algebraMap k (S ⧸ J θ (R := S)) (θ o) = Ideal.Quotient.mk _ (algebraMap O S o))
    [IsEmpty cov₀.κ] [IsEmpty (cov₀.transport (h := h)).κ] [DecidableEq cov₀.ι]
    (φ : cov₀.C →ₐ[R₀] cov₀'.C) {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
    (hbal : NodeHom.BalancedK θ πL πL' (nodePhiK φ)) :
    NodeHom.Balanced πL πL' (nodePhi (transportMap h φ)) := by
  intro j
  obtain ⟨ζ, η, h1, h2, h3, h4⟩ := hbal j
  have key := nodePhi_transportMap h φ
  have h1' : nodePhi (transportMap h φ) (Pi.single j 1) =
      piEquivT h cov₀' (nodePhiK φ (Pi.single j 1)) := by
    rw [← key, piEquivT_single, map_one]
    rfl
  refine ⟨piEquivT h cov₀' ζ, η, ?_, fun j' hj' ↦ h2 j' fun h0 ↦ hj' ?_, ?_, ?_⟩
  · exact (map_pow _ _ _).symm.trans ((congrArg _ h1).trans (map_one _))
  · rw [h1', piEquivT_apply, h0, map_zero]
    rfl
  · have hs : Pi.single j (NodeHom.sK (cov₀.transport (h := h)) j) = piEquivT h cov₀
        (Pi.single j ((1 : Admissible.PieceBase φ₀ (cov₀.idem j) (cov₀.e_pos j)) ⊗ₜ
          Node.u (0 : k))) := by
      rw [piEquivT_single, kummerPieceEquiv_one_tmul]
      rfl
    rw [hs, key, h3, map_mul, map_mul, ← h1']
    congr 1
    funext j'
    exact (map_pow _ _ _).trans (congrArg (· ^ _) (kummerPieceEquiv_one_tmul h _ _ _))
  · have ht : Pi.single j (NodeHom.tK (cov₀.transport (h := h)) j) = piEquivT h cov₀
        (Pi.single j ((1 : Admissible.PieceBase φ₀ (cov₀.idem j) (cov₀.e_pos j)) ⊗ₜ
          Node.v (0 : k))) := by
      rw [piEquivT_single, kummerPieceEquiv_one_tmul]
      rfl
    rw [ht, key, h4, map_mul, map_mul, ← h1']
    congr 1
    · exact congrArg _ (map_pow _ _ _)
    funext j'
    exact (piEquivT_apply h cov₀' _ j').trans (kummerPieceEquiv_eta h hk _ _ _ _)

end Transport

end AdmissibleLift
/-! ### All levels -/

namespace LevelTower

open AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))}

/-- **Balance at the special chart gives balance at every level**, when `k → R_n/J` maps `θ o`
to the class of `o`. -/
theorem nodeBalanced_of_balancedK (hfe : ∀ n, e n f₀ = fbar θ (f n))
    (hk : ∀ n o, algebraMap k (R n ⧸ J θ (R := R n)) (θ o) =
      Ideal.Quotient.mk _ (algebraMap O (R n) o))
    [IsEmpty cov₀.κ] [d : DecidableEq cov₀.ι] {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
    (φ : cov₀.C →ₐ[R₀] cov₀'.C) (hbal : NodeHom.BalancedK θ πL πL' (nodePhiK φ)) (n : ℕ) :
    NodeBalanced hfe πL πL' φ n := by
  obtain rfl : d = Classical.decEq _ := Subsingleton.elim _ _
  letI : DecidableEq cov₀.ι := Classical.decEq _
  haveI : IsEmpty (cov₀.transport (h := hfe n)).κ := ‹IsEmpty cov₀.κ›
  exact balanced_nodePhi_transportMap (hfe n) (hk n) φ hbal

end LevelTower

end

end SemistableReduction
