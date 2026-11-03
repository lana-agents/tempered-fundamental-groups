/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateLevelHom
import TemperedFundamentalGroups.SemistableReduction.LevelTowerHomH

/-!
# The maps of the node patches of Tate coverings over `V₁` (MR12 I3, Tate instance, part 2)

For a morphism `f₁ : Sp.C1 → Sp'.C1` of special-fibre coverings over `V₁` whose induced map of
node coverings is balanced (`TateGlue1.Balanced`):

* `TateGlue1.input_R`, `input_commRingR`, `input_algOR`, `input_algkR`, `input_f`, `input_e`,
  `input_algBR` (`rfl`/`HEq.rfl`: the base data of `TateGlue1.input` for one covering);
* **`TateGlue1.gI`**: the maps of the node patches `(input … Sp).T.G n → (input … Sp').T.G n`
  (`LevelTower.nodeLevelMapH`, the base identifications composed from the lemmas above, so that
  no unification problem between the levels of the two inputs is posed). `gI` is accepted as the
  argument `g` of `NodeEtaleGlue.Input.yMap` (input … Sp) (input … Sp').

Next (MR12 c49): the overlap condition `hg` of `yMap` for `gI` and `eMap` by
`Input.hg_of_special` with `LevelTower.pMapH`, `nfMapH`, `fst_nodeLevelMapH`, `σP_pMapH`,
`pMapH_algebraMap` (a first draft exceeds the heartbeat limit), then `yMap_succ`
(`LevelTower.tr_nodeLevelMapH`) and the overlap wiring.
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

namespace TateGlue1

open TateTwoChart TateTwoChartNode TateLevel KummerEtale

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
  {hπe : θ (ϖ ^ m) = 0} {τ : Rb b₄ b₆ ϖ m ε}
  {cov₀ cov₀' : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O] (hm : m ≠ 0)

section Single

variable (Sp : Special1 hκ hπ hπe τ cov₀) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)

lemma input_R : (input hκ hπ hε hϖ π' hπ' hker Sp hm).R = R b₄ b₆ ϖ m ε := rfl

lemma input_commRingR : HEq (input hκ hπ hε hϖ π' hπ' hker Sp hm).commRingR
    (fun n ↦ (inferInstance : CommRing (R b₄ b₆ ϖ m ε n))) := HEq.rfl

lemma input_algOR : HEq (input hκ hπ hε hϖ π' hπ' hker Sp hm).algOR
    (fun n ↦ (inferInstance : Algebra O (R b₄ b₆ ϖ m ε n))) := HEq.rfl

lemma input_algkR : HEq (input hκ hπ hε hϖ π' hπ' hker Sp hm).algkR
    (fun n ↦ (inferInstance : Algebra k (R b₄ b₆ ϖ m ε n ⧸ J θ (R := R b₄ b₆ ϖ m ε n)))) := HEq.rfl

lemma input_f : HEq (input hκ hπ hε hϖ π' hπ' hker Sp hm).T.f
    (QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) := HEq.rfl

lemma input_algBR (n : ℕ) (r : B ϖ π b₄ t κ n) :
    HEq (algebraMap ((input hκ hπ hε hϖ π' hπ' hker Sp hm).B n)
      ((input hκ hπ hε hϖ π' hπ' hker Sp hm).R n) r) (toRn b₄ hκ hπ n r) := HEq.rfl

lemma input_e : HEq (input hκ hπ hε hϖ π' hπ' hker Sp hm).T.e
    (QuadNodeTower.eqv ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) hϖ) := HEq.rfl

lemma nodeCoordI (n : ℕ) :
    LevelTower.NodeCoord ((input hκ hπ hε hϖ π' hπ' hker Sp hm).T.level n)
      (algebraMap (KummerEtale.A ϖ m) (FormalPatchLevel.Hat
        (QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n)) (Node.u (ϖ ^ m)))
      (algebraMap (KummerEtale.A ϖ m) (FormalPatchLevel.Hat
        (QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n)) (Node.v (ϖ ^ m))) :=
  QuadNodeTower.nodeCoord hϖ π' hπ' hker n

end Single

omit hθ in
lemma heq_refl_hat {X : Type u} (x : X) : HEq x x := HEq.rfl

variable (Sp : Special1 hκ hπ hπe τ cov₀) (Sp' : Special1 hκ hπ hπe τ cov₀')
  (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (π'' : cov₀'.ι → O) (hπ'' : ∀ j, π'' j ^ cov₀'.e j = ϖ ^ m)
  [IsEmpty cov₀.κ] [IsEmpty cov₀'.κ] (f₁ : Sp.C1 →ₐ[T1s θ π b₄ t κ] Sp'.C1)
  (hbal : Balanced hκ hπ hε Sp Sp' hϖ π' π'' f₁)

/-- **The map of the node patches at level `n`** over the levels of the two inputs
(`LevelTower.nodeLevelMapH`; all base identifications are composites of the `rfl`-lemmas
`input_R`, `input_commRingR`, … of one input at a time). -/
noncomputable def gI (n : ℕ) :=
  LevelTower.nodeLevelMapH hθ.out
    ((input_R hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans (input_R hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_commRingR hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans
      (input_commRingR hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_algOR hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans
      (input_algOR hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_algkR hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans
      (input_algkR hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_f hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans (input_f hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input_e hκ hπ hε hϖ hker hm Sp' π'' hπ'').trans (input_e hκ hπ hε hϖ hker hm Sp π' hπ').symm)
    ((input hκ hπ hε hϖ π' hπ' hker Sp hm).T.level n)
    ((input hκ hπ hε hϖ π'' hπ'' hker Sp' hm).T.level n)
    (covMap hκ hπ hε Sp Sp' f₁) (nodeCoordI hκ hπ hε hϖ hker hm Sp π' hπ' n)
    (nodeCoordI hκ hπ hε hϖ hker hm Sp' π'' hπ'' n) (heq_refl_hat _) (heq_refl_hat _) (hbal n)

end TateGlue1

end

end SemistableReduction
