/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeLevelHom

/-!
# Maps of patched levels over equal but differently spelled bases (generic; MR12 I3)

`LevelTower.nodeLevelMap` needs the source and target levels over one family of base rings `R`
with one choice of `f`, `e`. For two glueing inputs `I`, `I'` of *different* coverings (e.g. the
Tate inputs `TateGlue1.input … Sp`, `TateGlue1.input … Sp'`) these data are equal, but spelled
as projections of different structures, and a map typed `I.T.G n → I'.T.G n` cannot be obtained
from `nodeLevelMap` at the concrete charts: the unifier unfolds the `abbrev`s `Data.G`,
`Level.G`, … on both sides and compares differently spelled instance terms over the concrete
rings (MR12 c48).

Here the base data of the target are independent variables `R'`, its instances, `f'`, `e'`,
related to those of the source by equations (`HEq`), and the maps are defined by `subst`:

* **`nodeLevelMapH`**, `pMapH`, `nfMapH` (the heterogeneous `nodeLevelMap`, `pMap`,
  `NfMap ∘ transportMapR`);
* `fst_nodeLevelMapH`, `σP_pMapH`, `nfMapH_algebraMap`, `pMapH_algebraMap`,
  `nodeLevelMapH_algebraMap`;
* **`tr_nodeLevelMapH`** (compatibility with the transition maps).

At a concrete use site all equations are composites of `rfl`-lemmas for one input at a time.
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

namespace LevelTower

section Level

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  {R R' : ℕ → Type u}
  [cR : ∀ n, CommRing (R n)] [aR : ∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [kR : ∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  [cR' : ∀ n, CommRing (R' n)] [aR' : ∀ n, Algebra O (R' n)]
  [∀ n, IsNoetherianRing (R' n)] [kR' : ∀ n, Algebra k (R' n ⧸ J θ (R := R' n))]
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))}
  {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  {f' : ∀ n, R' n} {e' : ∀ n, R₀ ≃ₐ[k] (R' n ⧸ J θ (R := R' n))}
  {hfe' : ∀ n, e' n f₀ = fbar θ (f' n)}
  (hθ : Function.Surjective θ) {n : ℕ}
  (hR : R' = R) (hc : HEq cR' cR) (ha : HEq aR' aR) (hk : HEq kR' kR)
  (hf : HEq f' f) (he : HEq e' e)

/-- `φ` on the localizations at `f` (`NfMap ∘ transportMapR`), over equal bases. -/
def nfMapH (φ : cov₀.C →ₐ[R₀] cov₀'.C) :
    Localization.Away (algebraMap (R n) (cov₀.transport (h := hfe n)).C (f n)) →+*
      Localization.Away (algebraMap (R' n) (cov₀'.transport (h := hfe' n)).C (f' n)) := by
  subst R'
  obtain rfl := (eq_of_heq hc).symm
  obtain rfl := (eq_of_heq ha).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := (eq_of_heq hf).symm
  obtain rfl := (eq_of_heq he).symm
  exact (FormalPatchLevel.NfMap (f n) (transportMapR (hfe n) φ)).toRingHom

omit [∀ n, IsNoetherianRing (R n)] in
lemma nfMapH_algebraMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (c : (cov₀.transport (h := hfe n)).C) :
    nfMapH (n := n) hR hc ha hk hf he φ (algebraMap (cov₀.transport (h := hfe n)).C _ c) =
      algebraMap (cov₀'.transport (h := hfe' n)).C _ (φ c) := by
  subst R'
  obtain rfl := (eq_of_heq hc).symm
  obtain rfl := (eq_of_heq ha).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := (eq_of_heq hf).symm
  obtain rfl := (eq_of_heq he).symm
  exact FormalPatchLevel.NfMap_algebraMap _ _ c

variable (D : Level R cov₀ πL hfe n) (D' : Level R' cov₀' πL' hfe' n)

/-- **The map of étale lifts** `D.P → D'.P` induced by `φ` (`pMap`), over equal bases. -/
def pMapH (φ : cov₀.C →ₐ[R₀] cov₀'.C) : D.P →+* D'.P := by
  subst R'
  obtain rfl := (eq_of_heq hc).symm
  obtain rfl := (eq_of_heq ha).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := (eq_of_heq hf).symm
  obtain rfl := (eq_of_heq he).symm
  exact (pMap D D' φ).toRingHom

omit [∀ n, IsNoetherianRing (R n)] in
lemma σP_pMapH (φ : cov₀.C →ₐ[R₀] cov₀'.C) (x : D.P) :
    D'.σP (Ideal.Quotient.mk _ (pMapH hR hc ha hk hf he D D' φ x)) =
      nfMapH hR hc ha hk hf he φ (D.σP (Ideal.Quotient.mk _ x)) := by
  subst R'
  obtain rfl := (eq_of_heq hc).symm
  obtain rfl := (eq_of_heq ha).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := (eq_of_heq hf).symm
  obtain rfl := (eq_of_heq he).symm
  exact σP_pMap D D' φ x

omit [∀ n, IsNoetherianRing (R n)] in
lemma pMapH_algebraMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (r : R n) (r' : R' n) (h : HEq r' r) :
    pMapH hR hc ha hk hf he D D' φ (algebraMap (R n) D.P r) = algebraMap (R' n) D'.P r' := by
  subst R'
  obtain rfl := (eq_of_heq hc).symm
  obtain rfl := (eq_of_heq ha).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := (eq_of_heq hf).symm
  obtain rfl := (eq_of_heq he).symm
  obtain rfl := (eq_of_heq h).symm
  exact (pMap D D' φ).commutes r

variable [IsEmpty cov₀.κ] [IsEmpty cov₀'.κ]

/-- **`nodeLevelMap` between levels over equal but differently spelled bases.** -/
def nodeLevelMapH (φ : cov₀.C →ₐ[R₀] cov₀'.C) {cu cv : FormalPatchLevel.Hat (f n)}
    (hcd : NodeCoord D cu cv) {cu' cv' : FormalPatchLevel.Hat (f' n)}
    (hcd' : NodeCoord D' cu' cv') (hcu : HEq cu' cu) (hcv : HEq cv' cv)
    (hbal : NodeBalanced hfe πL πL' φ n) : D.G hθ →+* D'.G hθ := by
  subst R'
  obtain rfl := (eq_of_heq hc).symm
  obtain rfl := (eq_of_heq ha).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := (eq_of_heq hf).symm
  obtain rfl := (eq_of_heq he).symm
  exact (nodeLevelMap hθ D D' φ hcd (eq_of_heq hcu ▸ eq_of_heq hcv ▸ hcd') hbal).toRingHom

lemma fst_nodeLevelMapH (φ : cov₀.C →ₐ[R₀] cov₀'.C) {cu cv : FormalPatchLevel.Hat (f n)}
    (hcd : NodeCoord D cu cv) {cu' cv' : FormalPatchLevel.Hat (f' n)}
    (hcd' : NodeCoord D' cu' cv') (hcu : HEq cu' cu) (hcv : HEq cv' cv)
    (hbal : NodeBalanced hfe πL πL' φ n) (x : D.G hθ) :
    (nodeLevelMapH hθ hR hc ha hk hf he D D' φ hcd hcd' hcu hcv hbal x).1.1 =
      pMapH hR hc ha hk hf he D D' φ x.1.1 := by
  subst R'
  obtain rfl := (eq_of_heq hc).symm
  obtain rfl := (eq_of_heq ha).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := (eq_of_heq hf).symm
  obtain rfl := (eq_of_heq he).symm
  rfl

lemma nodeLevelMapH_algebraMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) {cu cv : FormalPatchLevel.Hat (f n)}
    (hcd : NodeCoord D cu cv) {cu' cv' : FormalPatchLevel.Hat (f' n)}
    (hcd' : NodeCoord D' cu' cv') (hcu : HEq cu' cu) (hcv : HEq cv' cv)
    (hbal : NodeBalanced hfe πL πL' φ n) (r : R n) (r' : R' n) (h : HEq r' r) :
    nodeLevelMapH hθ hR hc ha hk hf he D D' φ hcd hcd' hcu hcv hbal
        (algebraMap (R n) (D.G hθ) r) = algebraMap (R' n) (D'.G hθ) r' := by
  subst R'
  obtain rfl := (eq_of_heq hc).symm
  obtain rfl := (eq_of_heq ha).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := (eq_of_heq hf).symm
  obtain rfl := (eq_of_heq he).symm
  obtain rfl := (eq_of_heq h).symm
  exact (nodeLevelMap hθ D D' φ hcd _ hbal).commutes r

end Level

section Tower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  {R R' : ℕ → Type u}
  [cR : ∀ n, CommRing (R n)] [aR : ∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [kR : ∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  [cR' : ∀ n, CommRing (R' n)] [aR' : ∀ n, Algebra O (R' n)]
  [∀ n, IsNoetherianRing (R' n)] [kR' : ∀ n, Algebra k (R' n ⧸ J θ (R := R' n))]
  [sR : ∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  [sR' : ∀ n, Algebra (R' (n + 1)) (R' n)] [∀ n, IsScalarTower O (R' (n + 1)) (R' n)]
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))}
  {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  {f' : ∀ n, R' n} {e' : ∀ n, R₀ ≃ₐ[k] (R' n ⧸ J θ (R := R' n))}
  {hfe' : ∀ n, e' n f₀ = fbar θ (f' n)}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hq : ∀ n, Function.Surjective (algebraMap (R (n + 1)) (R n)))
  (hf : ∀ n, LevelStep.f' (R' := R n) (f (n + 1)) = f n)
  (he : ∀ n (r : R (n + 1)), e n ((e (n + 1)).symm (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (algebraMap (R (n + 1)) (R n) r))
  (D : ∀ n, Level R cov₀ πL hfe n)
  (hχχ : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.χ j a) = (D n).L.χ j a)
  (hεε : ∀ n j, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.ε j) = (D n).L.ε j)
  (hδδ : ∀ n i, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).M.δ i) = (D n).M.δ i)
  (htt : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (D (n + 1)).M.t = (D n).M.t)
  (hq' : ∀ n, Function.Surjective (algebraMap (R' (n + 1)) (R' n)))
  (hf' : ∀ n, LevelStep.f' (R' := R' n) (f' (n + 1)) = f' n)
  (he' : ∀ n (r : R' (n + 1)), e' n ((e' (n + 1)).symm (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (algebraMap (R' (n + 1)) (R' n) r))
  (D' : ∀ n, Level R' cov₀' πL' hfe' n)
  (hχχ' : ∀ n j a, LevelStep.ψ₂ (f' (n + 1)) (f' n) (hf' n) ((D' (n + 1)).L.χ j a) =
    (D' n).L.χ j a)
  (hεε' : ∀ n j, LevelStep.ψ₂ (f' (n + 1)) (f' n) (hf' n) ((D' (n + 1)).L.ε j) = (D' n).L.ε j)
  (hδδ' : ∀ n i, LevelStep.ψ₂ (f' (n + 1)) (f' n) (hf' n) ((D' (n + 1)).M.δ i) = (D' n).M.δ i)
  (htt' : ∀ n, LevelStep.ψ₂ (f' (n + 1)) (f' n) (hf' n) (D' (n + 1)).M.t = (D' n).M.t)
  (hR : R' = R) (hc : HEq cR' cR) (ha : HEq aR' aR) (hk : HEq kR' kR) (hs : HEq sR' sR)
  (hF : HEq f' f) (hE : HEq e' e)
  [IsEmpty cov₀.κ] [IsEmpty cov₀'.κ]

include hs in
/-- **The heterogeneous node level maps commute with the transition maps.** -/
theorem tr_nodeLevelMapH (φ : cov₀.C →ₐ[R₀] cov₀'.C) {cu cv : ∀ n, FormalPatchLevel.Hat (f n)}
    (hcd : ∀ n, NodeCoord (D n) (cu n) (cv n)) {cu' cv' : ∀ n, FormalPatchLevel.Hat (f' n)}
    (hcd' : ∀ n, NodeCoord (D' n) (cu' n) (cv' n)) (hcu : ∀ n, HEq (cu' n) (cu n))
    (hcv : ∀ n, HEq (cv' n) (cv n)) (hbal : ∀ n, NodeBalanced hfe πL πL' φ n) (n : ℕ)
    (x : (D (n + 1)).G hθ) :
    tr hθ hO hq' hf' he' D' hχχ' hεε' hδδ' htt' n
        (nodeLevelMapH hθ hR hc ha hk hF hE (D (n + 1)) (D' (n + 1)) φ (hcd (n + 1))
          (hcd' (n + 1)) (hcu (n + 1)) (hcv (n + 1)) (hbal (n + 1)) x) =
      nodeLevelMapH hθ hR hc ha hk hF hE (D n) (D' n) φ (hcd n) (hcd' n) (hcu n) (hcv n)
        (hbal n) (tr hθ hO hq hf he D hχχ hεε hδδ htt n x) := by
  subst R'
  obtain rfl := (eq_of_heq hc).symm
  obtain rfl := (eq_of_heq ha).symm
  obtain rfl := (eq_of_heq hk).symm
  obtain rfl := (eq_of_heq hs).symm
  obtain rfl := (eq_of_heq hF).symm
  obtain rfl := (eq_of_heq hE).symm
  exact tr_nodeLevelMap hθ hO hq hf he D hχχ hεε hδδ htt D' hχχ' hεε' hδδ' htt' φ hcd
    (fun n ↦ eq_of_heq (hcu n) ▸ eq_of_heq (hcv n) ▸ hcd' n) hbal n x

end Tower

end LevelTower

end

end SemistableReduction
