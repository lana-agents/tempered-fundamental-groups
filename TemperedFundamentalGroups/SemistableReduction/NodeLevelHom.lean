/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspInputHom
import TemperedFundamentalGroups.SemistableReduction.KummerPieceHom

/-!
# Maps of patched levels of node-only coverings (MR12 I3, generic core, layer 3)

The node analogue of the cusp level maps of `CuspInputHom`. A balanced map of node-only
special-fibre coverings lifts to the patched levels.

* `AdmissibleLift.nodePhi`: the map of formal node models induced by a map `φ : C → C'` of
  coverings without cusp factors (`kummer' ∘ (R̂ ⊗ φ) ∘ kummer⁻¹` on the node factors);
  `AdmissibleLift.NodeHom.balanced_nodePhi_id`: the identity is balanced;
  **`AdmissibleLift.exists_nodeKappa`**: if `nodePhi φ` is balanced (`NodeHom.Balanced`) and the
  lifted node coordinates agree, an NF-map `g : NF → NF'` compatible with `φ` under `κ`
  (`kappaF`).
* `LevelTower.NodeBalanced`, `LevelTower.NodeCoord`: the balance of `φ` at level `n` and the
  values `c_u`, `c_v` of the lifted node coordinates of a level (at the Tate charts `χ_j` is
  `NodeChart.χ`, so `c_u`, `c_v` are the chart's `u`, `v`);
  **`LevelTower.nodeLevelMap`**: the map `D.G → D'.G` of patched levels of node-only coverings
  induced by `φ` (first component `pMap φ`, so independent of the choice of the NF-map),
  `nodeLevelMap_eq`, `nodeLevelMap_id/comp`, **`tr_nodeLevelMap`** (compatibility with the
  towers).
-/

universe u

open TensorProduct

namespace SemistableReduction

noncomputable section

namespace AdmissibleLift

/-! ### The NF-map induced by a balanced map of node-only coverings -/

section Kappa

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ φ' : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc ψc' : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  {cov : Admissible.Covering φ ψc} {cov' : Admissible.Covering φ' ψc'}
  {πL : cov.ι → O} {πL' : cov'.ι → O}
  (L : KummerLift cov πL) (M : CuspLift cov) (L' : KummerLift cov' πL') (M' : CuspLift cov')

/-- The inclusion of the node factors into all factors of a covering without cusp factors. -/
def nodeIncl [IsEmpty cov.κ] :
    (∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)) →ₐ[Admissible.Hat (fbar θ f)]
      ((∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)) ×
        (∀ i, Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i))) :=
  (AlgHom.id _ _).prod (AlgHom.pi fun i ↦ isEmptyElim i)

lemma nodeIncl_fst [IsEmpty cov.κ]
    (z : (∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)) ×
      (∀ i, Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i))) :
    nodeIncl (cov := cov) z.1 = z :=
  Prod.ext rfl (funext fun i ↦ isEmptyElim i)

/-- **The map of formal node models induced by a map `φc : C → C'` of coverings without cusp
factors**: `kummer' ∘ (R̂ ⊗ φc) ∘ kummer⁻¹` on the node factors. -/
def nodePhi [IsEmpty cov.κ] (φc : cov.C →ₐ[R ⧸ J θ] cov'.C) :
    (∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)) →ₐ[Admissible.Hat (fbar θ f)]
      ∀ j', Admissible.KummerPiece φ' (cov'.idem j') (cov'.e_pos j') :=
  (AlgHom.fst _ _ _).comp (cov'.kummer.toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id _ _) φc).comp
      (cov.kummer.symm.toAlgHom.comp nodeIncl)))

lemma nodePhi_kummer [IsEmpty cov.κ] (φc : cov.C →ₐ[R ⧸ J θ] cov'.C)
    (w : Admissible.Hat (fbar θ f) ⊗[R ⧸ J θ] cov.C) :
    nodePhi φc (cov.kummer w).1 =
      (cov'.kummer (Algebra.TensorProduct.map
        (AlgHom.id (Admissible.Hat (fbar θ f)) (Admissible.Hat (fbar θ f))) φc w)).1 := by
  change (cov'.kummer (Algebra.TensorProduct.map
    (AlgHom.id (Admissible.Hat (fbar θ f)) (Admissible.Hat (fbar θ f))) φc
    (cov.kummer.symm (nodeIncl (cov.kummer w).1)))).1 = _
  rw [nodeIncl_fst, AlgEquiv.symm_apply_apply]

lemma nodePhi_id [IsEmpty cov.κ] :
    nodePhi (cov' := cov) (AlgHom.id (R ⧸ J θ) cov.C) = AlgHom.id _ _ := by
  refine AlgHom.ext fun z ↦ ?_
  obtain ⟨w, hw⟩ := cov.kummer.surjective (nodeIncl z)
  have h := nodePhi_kummer (cov' := cov) (AlgHom.id (R ⧸ J θ) cov.C) w
  rw [hw, Algebra.TensorProduct.map_id, AlgHom.id_apply, hw] at h
  exact h

/-- **An NF-map compatible with a balanced map of node-only coverings**: for `φc : C → C'`
(coverings without cusp factors, lift data with the same lifted node coordinates `c_u`, `c_v`
and idempotent `ε̃_j`) with `nodePhi φc` balanced there is a map `g : NF → NF'` of `R̂`-algebras
with `κ'(1 ⊗ φc c) = g(κ(1 ⊗ c))` modulo `J`. -/
theorem exists_nodeKappa [IsNoetherianRing R] (hθ : Function.Surjective θ) {n : ℕ}
    (hJ : J θ (R := R) ^ n = ⊥) [IsEmpty cov.κ] [IsEmpty cov'.κ] [DecidableEq cov.ι]
    {cu cv : FormalPatchLevel.Hat f}
    (hu : ∀ j, L.χ j (Node.u (πL j ^ cov.e j)) = cu)
    (hv : ∀ j, L.χ j (Node.v (πL j ^ cov.e j)) = cv)
    (hu' : ∀ j', L'.χ j' (Node.u (πL' j' ^ cov'.e j')) = cu)
    (hv' : ∀ j', L'.χ j' (Node.v (πL' j' ^ cov'.e j')) = cv)
    (hidem : ∀ j, IsIdempotentElem (L.ε j))
    (φc : cov.C →ₐ[R ⧸ J θ] cov'.C) (hbal : NodeHom.Balanced πL πL' (nodePhi φc)) :
    ∃ g : NFall L M →ₐ[FormalPatchLevel.Hat f] NFall L' M', ∀ (c : cov.C) (x : NFall L M),
      Ideal.Quotient.mk _ x = kappaF L M hθ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c) →
      Ideal.Quotient.mk _ (g x) = kappaF L' M' hθ ((1 : FormalPatchLevel.Hat f) ⊗ₜ φc c) := by
  obtain ⟨g, hg⟩ := exists_nodeNFMap L M L' M' hθ hJ hu hv hu' hv' hidem (nodePhi φc) hbal
  refine ⟨g, fun c x hx ↦ (kappa3F L' M' hθ).injective (Prod.ext ?_
    (funext fun i ↦ isEmptyElim i))⟩
  rw [hg, hx, kappa3F_kappaF, kappa3F_kappaF, nodePhi_kummer, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]

namespace NodeHom

/-- **The identity is balanced** (`ζ = 1`, `η = 1`). -/
lemma balanced_id [DecidableEq cov.ι] :
    Balanced πL πL (AlgHom.id (Admissible.Hat (fbar θ f)) (∀ j, KP cov j)) := by
  intro j
  have hd : cov.e j / cov.e j = 1 := Nat.div_self (cov.e_pos j)
  refine ⟨1, fun _ ↦ 1, one_pow _, fun j' hj' ↦ ?_, ?_, ?_⟩
  · obtain rfl : j' = j := by
      by_contra h
      exact hj' (Pi.single_eq_of_ne h _)
    exact ⟨dvd_rfl, by rw [hd, pow_one, one_mul], one_pow _⟩
  · funext j'
    rcases eq_or_ne j' j with rfl | h
    · simp [hd]
    · simp [h]
  · funext j'
    rcases eq_or_ne j' j with rfl | h
    · simp only [hd, Pi.single_eq_same, AlgHom.id_apply, Pi.mul_apply, one_pow, pow_one, mul_one,
        map_one, one_mul]
    · simp [h]

lemma balanced_nodePhi_id [IsEmpty cov.κ] [DecidableEq cov.ι] :
    Balanced πL πL (nodePhi (cov' := cov) (AlgHom.id (R ⧸ J θ) cov.C)) := by
  rw [nodePhi_id]
  exact balanced_id

end NodeHom

end Kappa

end AdmissibleLift


/-! ### Maps of patched levels of node-only coverings -/

namespace LevelTower

open AdmissibleLift

section NodeLevel

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' φ₀'' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {cov₀'' : Admissible.Covering φ₀'' ψ₀} {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  {πL'' : cov₀''.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))}

/-- **`φ` is balanced at level `n`**: the induced map of formal node models of the transported
coverings (`nodePhi`) has a balanced normal form (`NodeHom.Balanced`). -/
def NodeBalanced (hfe : ∀ n, e n f₀ = fbar θ (f n)) (πL : cov₀.ι → O) (πL' : cov₀'.ι → O)
    [IsEmpty cov₀.κ] (φ : cov₀.C →ₐ[R₀] cov₀'.C) (n : ℕ) : Prop :=
  haveI : IsEmpty (cov₀.transport (h := hfe n)).κ := ‹IsEmpty cov₀.κ›
  letI : DecidableEq (cov₀.transport (h := hfe n)).ι := Classical.decEq _
  NodeHom.Balanced πL πL' (nodePhi (transportMap (hfe n) φ))

variable {hfe : ∀ n, e n f₀ = fbar θ (f n)}

/-- **The lifted node coordinates of a level take the values `c_u`, `c_v`**:
`χ_j(u) = c_u`, `χ_j(v) = c_v` for all `j` (at the Tate charts `χ_j = NodeChart.χ`, and `c_u`,
`c_v` are the chart's coordinates `u`, `v`). -/
def NodeCoord {n : ℕ} (D : Level R cov₀ πL hfe n) (cu cv : FormalPatchLevel.Hat (f n)) : Prop :=
  (∀ j, D.L.χ j (Node.u (πL j ^ (cov₀.transport (h := hfe n)).e j)) = cu) ∧
    ∀ j, D.L.χ j (Node.v (πL j ^ (cov₀.transport (h := hfe n)).e j)) = cv

omit [∀ n, IsNoetherianRing (R n)] in
lemma nodeBalanced_id [IsEmpty cov₀.κ] (n : ℕ) :
    NodeBalanced hfe πL πL (AlgHom.id R₀ cov₀.C) n := by
  haveI : IsEmpty (cov₀.transport (h := hfe n)).κ := ‹IsEmpty cov₀.κ›
  letI : DecidableEq (cov₀.transport (h := hfe n)).ι := Classical.decEq _
  have h : transportMap (hfe n) (AlgHom.id R₀ cov₀.C) = AlgHom.id _ _ := AlgHom.ext fun _ ↦ rfl
  unfold NodeBalanced
  rw [h]
  exact NodeHom.balanced_nodePhi_id

variable (hθ : Function.Surjective θ) {n : ℕ}
  (D : Level R cov₀ πL hfe n) (D' : Level R cov₀' πL' hfe n) (D'' : Level R cov₀'' πL'' hfe n)
  [IsEmpty cov₀.κ] [IsEmpty cov₀'.κ] [IsEmpty cov₀''.κ]

/-- **An NF-map compatible with a balanced map of node-only coverings exists at every level.** -/
theorem exists_kappaCompat_node (φ : cov₀.C →ₐ[R₀] cov₀'.C) {cu cv : FormalPatchLevel.Hat (f n)}
    (hc : NodeCoord D cu cv) (hc' : NodeCoord D' cu cv) (hbal : NodeBalanced hfe πL πL' φ n) :
    ∃ g, KappaCompat hθ D D' φ g := by
  haveI : IsEmpty (cov₀.transport (h := hfe n)).κ := ‹IsEmpty cov₀.κ›
  haveI : IsEmpty (cov₀'.transport (h := hfe n)).κ := ‹IsEmpty cov₀'.κ›
  letI : DecidableEq (cov₀.transport (h := hfe n)).ι := Classical.decEq _
  obtain ⟨g, hg⟩ := exists_nodeKappa D.L D.M D'.L D'.M hθ D.hJ hc.1 hc.2 hc'.1 hc'.2 D.hidem
    (transportMap (hfe n) φ) hbal
  refine ⟨g.restrictScalars (R n), fun c ↦ ?_⟩
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (kappaF D.L D.M hθ ((1 : FormalPatchLevel.Hat (f n)) ⊗ₜ c))
  rw [← hx, FormalPatchLevel.NMapQuot_mk]
  exact (hg c x hx).symm

/-- **The map of patched levels of node-only coverings** induced by a balanced
`φ : cov₀.C → cov₀'.C`. -/
def nodeLevelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) {cu cv : FormalPatchLevel.Hat (f n)}
    (hc : NodeCoord D cu cv) (hc' : NodeCoord D' cu cv) (hbal : NodeBalanced hfe πL πL' φ n) :
    D.G hθ →ₐ[R n] D'.G hθ :=
  levelMap hθ D D' φ (exists_kappaCompat_node hθ D D' φ hc hc' hbal).choose
    (exists_kappaCompat_node hθ D D' φ hc hc' hbal).choose_spec

@[simp] lemma fst_nodeLevelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) {cu cv : FormalPatchLevel.Hat (f n)}
    (hc : NodeCoord D cu cv) (hc' : NodeCoord D' cu cv) (hbal : NodeBalanced hfe πL πL' φ n)
    (x : D.G hθ) :
    (nodeLevelMap hθ D D' φ hc hc' hbal x).1.1 = pMap D D' φ x.1.1 :=
  rfl

/-- `nodeLevelMap` is `levelMap` for every compatible NF-map. -/
lemma nodeLevelMap_eq (φ : cov₀.C →ₐ[R₀] cov₀'.C) {cu cv : FormalPatchLevel.Hat (f n)}
    (hc : NodeCoord D cu cv) (hc' : NodeCoord D' cu cv) (hbal : NodeBalanced hfe πL πL' φ n)
    (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M) (hκ : KappaCompat hθ D D' φ g) :
    nodeLevelMap hθ D D' φ hc hc' hbal = levelMap hθ D D' φ g hκ :=
  eq_levelMap hθ D D' φ g hκ _ fun _ ↦ rfl

lemma nodeLevelMap_id (φ : cov₀.C →ₐ[R₀] cov₀.C) {cu cv : FormalPatchLevel.Hat (f n)}
    (hc : NodeCoord D cu cv) (hbal : NodeBalanced hfe πL πL φ n)
    (hφ : φ = AlgHom.id R₀ cov₀.C) :
    nodeLevelMap hθ D D φ hc hc hbal = AlgHom.id (R n) _ := by
  subst hφ
  exact ext_level hθ D fun x ↦ by
    rw [fst_nodeLevelMap, pMap_id]
    rfl

lemma nodeLevelMap_comp (φ : cov₀.C →ₐ[R₀] cov₀'.C) (φ' : cov₀'.C →ₐ[R₀] cov₀''.C)
    (φ'' : cov₀.C →ₐ[R₀] cov₀''.C) {cu cv : FormalPatchLevel.Hat (f n)}
    (hc : NodeCoord D cu cv) (hc' : NodeCoord D' cu cv) (hc'' : NodeCoord D'' cu cv)
    (hbal : NodeBalanced hfe πL πL' φ n) (hbal' : NodeBalanced hfe πL' πL'' φ' n)
    (hbal'' : NodeBalanced hfe πL πL'' φ'' n) (hφ : φ'' = φ'.comp φ) :
    (nodeLevelMap hθ D' D'' φ' hc' hc'' hbal').comp (nodeLevelMap hθ D D' φ hc hc' hbal) =
      nodeLevelMap hθ D D'' φ'' hc hc'' hbal'' := by
  subst hφ
  exact ext_level hθ D'' fun x ↦ by
    rw [AlgHom.comp_apply, fst_nodeLevelMap, fst_nodeLevelMap, fst_nodeLevelMap,
      pMap_comp D D' D'' φ φ', AlgHom.comp_apply]

end NodeLevel

section NodeTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ)
  [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hq : ∀ n, Function.Surjective (algebraMap (R (n + 1)) (R n)))
  (hf : ∀ n, LevelStep.f' (R' := R n) (f (n + 1)) = f n)
  (he : ∀ n (r : R (n + 1)), e n ((e (n + 1)).symm (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (algebraMap (R (n + 1)) (R n) r))
  (D : ∀ n, Level R cov₀ πL hfe n)
  (hχχ : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.χ j a) = (D n).L.χ j a)
  (hεε : ∀ n j, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.ε j) = (D n).L.ε j)
  (hδδ : ∀ n i, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).M.δ i) = (D n).M.δ i)
  (htt : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (D (n + 1)).M.t = (D n).M.t)
  (D' : ∀ n, Level R cov₀' πL' hfe n)
  (hχχ' : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D' (n + 1)).L.χ j a) =
    (D' n).L.χ j a)
  (hεε' : ∀ n j, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D' (n + 1)).L.ε j) = (D' n).L.ε j)
  (hδδ' : ∀ n i, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D' (n + 1)).M.δ i) = (D' n).M.δ i)
  (htt' : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (D' (n + 1)).M.t = (D' n).M.t)
  [IsEmpty cov₀.κ] [IsEmpty cov₀'.κ]

/-- **The maps of patched levels of node-only coverings commute with the transition maps.** -/
theorem tr_nodeLevelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) {cu cv : ∀ n, FormalPatchLevel.Hat (f n)}
    (hc : ∀ n, NodeCoord (D n) (cu n) (cv n)) (hc' : ∀ n, NodeCoord (D' n) (cu n) (cv n))
    (hbal : ∀ n, NodeBalanced hfe πL πL' φ n) (n : ℕ) (x : (D (n + 1)).G hθ) :
    tr hθ hO hq hf he D' hχχ' hεε' hδδ' htt' n
        (nodeLevelMap hθ (D (n + 1)) (D' (n + 1)) φ (hc (n + 1)) (hc' (n + 1)) (hbal (n + 1)) x) =
      nodeLevelMap hθ (D n) (D' n) φ (hc n) (hc' n) (hbal n)
        (tr hθ hO hq hf he D hχχ hεε hδδ htt n x) :=
  tr_levelMap hθ hO hq hf he D hχχ hεε hδδ htt D' hχχ' hεε' hδδ' htt' φ
    (fun n ↦ (exists_kappaCompat_node hθ (D n) (D' n) φ (hc n) (hc' n) (hbal n)).choose)
    (fun n ↦ (exists_kappaCompat_node hθ (D n) (D' n) φ (hc n) (hc' n) (hbal n)).choose_spec) n x

end NodeTower

end LevelTower

end

end SemistableReduction
