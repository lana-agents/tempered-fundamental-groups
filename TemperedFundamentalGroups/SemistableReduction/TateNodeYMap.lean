/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateLevelHom
import TemperedFundamentalGroups.SemistableReduction.LevelTowerHomH

/-!
# The base data of the Tate inputs over `V₁` for two coverings (MR12 I3, Tate instance, part 2)

For two special-fibre coverings `Sp`, `Sp'` over `V₁` and a morphism `f₁ : Sp.C1 → Sp'.C1`:

* `TateGlue1.input_R`, `input_commRingR`, `input_algOR`, `input_algkR`, `input_algSuccR`,
  `input_f`, `input_e`, `input_algBR` (`rfl`/`HEq.rfl`: the base data of `TateGlue1.input` for
  one covering), `nodeCoordI`;
* `TateGlue1.βI`, `hβaI`, `hβJI`, `heβI`, `hβRI`: the identity maps of the bases `B n` of the two
  inputs and their compatibilities.

These are the arguments of the generic `NodeEtaleGlue.Input.gH`/`yH` and
`NodeEtaleGlue.Overlap.systemMapH` (`InputNodeHomH`, `OverlapNodeHomH`) at the Tate inputs. All
equations between the base data of the two inputs are composites of the single-input lemmas, so
that no unification problem between the levels of the two inputs is posed (MR12 c48/c49: such
problems do not terminate at the Tate charts; in particular, a `def` wrapping `gH` at the Tate
inputs and statements of the overlap condition `hg` at the Tate inputs hang, while the generic
terms applied with explicit arguments elaborate in seconds).
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

lemma input_algSuccR : HEq (input hκ hπ hε hϖ π' hπ' hker Sp hm).algSuccR
    (fun n ↦ (inferInstance : Algebra (R b₄ b₆ ϖ m ε (n + 1)) (R b₄ b₆ ϖ m ε n))) := HEq.rfl

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
  (f₁ : Sp.C1 →ₐ[T1s θ π b₄ t κ] Sp'.C1)

/-- The family of identity maps of the base rings `B n` of the two inputs (the `β` of
`NodeEtaleGlue.Input.hg_gH`). -/
def βI (n : ℕ) : (input hκ hπ hε hϖ π' hπ' hker Sp hm).B n →+*
    (input hκ hπ hε hϖ π'' hπ'' hker Sp' hm).B n :=
  RingHom.id (B ϖ π b₄ t κ n)

lemma hβaI (n : ℕ) : βI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' n
    ((input hκ hπ hε hϖ π' hπ' hker Sp hm).a n) = (input hκ hπ hε hϖ π'' hπ'' hker Sp' hm).a n :=
  rfl

lemma hβJI (n : ℕ) : (J θ (R := (input hκ hπ hε hϖ π' hπ' hker Sp hm).B n)).map
    (βI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' n) ≤
      J θ (R := (input hκ hπ hε hϖ π'' hπ'' hker Sp' hm).B n) :=
  Ideal.map_le_iff_le_comap.2 fun _ hx ↦ hx

lemma heβI (n : ℕ) (r : (input hκ hπ hε hϖ π' hπ' hker Sp hm).B n) :
    (eMap hκ hπ Sp Sp' hϖ hker f₁ n).toRingHom
        (algebraMap ((input hκ hπ hε hϖ π' hπ' hker Sp hm).B n)
          ((input hκ hπ hε hϖ π' hπ' hker Sp hm).E n) r) =
      algebraMap ((input hκ hπ hε hϖ π'' hπ'' hker Sp' hm).B n)
        ((input hκ hπ hε hϖ π'' hπ'' hker Sp' hm).E n)
        (βI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' n r) :=
  (eMap hκ hπ Sp Sp' hϖ hker f₁ n).commutes r

lemma hβRI (n : ℕ) (r : (input hκ hπ hε hϖ π' hπ' hker Sp hm).B n) :
    HEq (algebraMap ((input hκ hπ hε hϖ π'' hπ'' hker Sp' hm).B n)
        ((input hκ hπ hε hϖ π'' hπ'' hker Sp' hm).R n)
        (βI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' n r))
      (algebraMap ((input hκ hπ hε hϖ π' hπ' hker Sp hm).B n)
        ((input hκ hπ hε hϖ π' hπ' hker Sp hm).R n) r) :=
  (input_algBR hκ hπ hε hϖ hker hm Sp' π'' hπ'' n
    (βI hκ hπ hε hϖ hker hm Sp Sp' π' hπ' π'' hπ'' n r)).trans
    (input_algBR hκ hπ hε hϖ hker hm Sp π' hπ' n r).symm

end TateGlue1

end

end SemistableReduction
