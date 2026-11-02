/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelTowerHom
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueHom
import TemperedFundamentalGroups.SemistableReduction.AdicSystemHom

/-!
# Endomorphisms of glued coverings with trivial patches (generic; MR13, G-action on lifts)

Generic consumers of MR12's lifting core (layers 1, 4, 5 and `LevelTowerHom`) for the case where
the patch tower over the first chart has **zero formal models** (the completion along `f n` is
the zero ring, e.g. the trivial patch `D(1)` of `P1Three` over `V₁ = ℙ¹ ∖ {0, 1, a}`), and for
endomorphisms (the Galois action on a single covering):

* `LevelTower.levelMap_eq_id`, `levelMap_eq_comp` (functoriality up to a propositional equality of
  the special maps), `subsingleton_NFall_of`, `kappaCompat_of_subsingleton` (`KappaCompat` is
  automatic for zero formal models);
* **`LevelTower.Data.zEnd`**: the endomorphism of level `n` induced by an endomorphism `φ` of the
  special-fibre covering, `zEnd_id`, `zEnd_comp`, **`tr_zEnd`** (compatibility with the transition
  maps, from `tr_levelMap`);
* `NodeEtaleGlue.Input.HgAt` (the hypothesis `hg` of `Input.yMap` as a `Prop`), `HgEnd`,
  **`Input.yEnd`** (`yMap` of `zEnd φ` and étale endomorphisms `e n`), `yEnd_succ`,
  `yEnd_algebraMap`;
* **`NodeEtaleGlue.Overlap.twoChartEnd`**, **`Overlap.systemEnd`**: from endomorphisms `y n` of the
  coverings over the first chart and `p n` of the pieces over the second chart (with the overlap
  condition `hψ`), the endomorphism of the adic system of chart algebras
  (`Overlap.twoChartMap`, `succ_comp_twoChartMap`, `TwoChartTower.systemShiftHom`).
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

/-! ### Generic: endomorphisms of the levels of a tower with zero formal models -/

namespace LevelTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  (hθ : Function.Surjective θ)

section Level

variable {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))}
  {hfe : ∀ n, e n f₀ = fbar θ (f n)} {n : ℕ} (D : Level R cov₀ πL hfe n)

lemma levelMap_eq_id {φ : cov₀.C →ₐ[R₀] cov₀.C} (hφ : φ = AlgHom.id _ _)
    (g : NFall D.L D.M →ₐ[R n] NFall D.L D.M) (hκ : KappaCompat hθ D D φ g) :
    levelMap hθ D D φ g hκ = AlgHom.id _ _ :=
  ext_level hθ D fun x ↦ (fst_levelMap hθ D D φ g hκ x).trans (by
    subst hφ
    exact congrArg (fun p : D.P →ₐ[R n] D.P ↦ p x.1.1) (pMap_id D))

lemma levelMap_eq_comp {φ φ' φ'' : cov₀.C →ₐ[R₀] cov₀.C} (hφ : φ'' = φ'.comp φ)
    (g g' g'' : NFall D.L D.M →ₐ[R n] NFall D.L D.M) (hκ : KappaCompat hθ D D φ g)
    (hκ' : KappaCompat hθ D D φ' g') (hκ'' : KappaCompat hθ D D φ'' g'') :
    levelMap hθ D D φ'' g'' hκ'' = (levelMap hθ D D φ' g' hκ').comp (levelMap hθ D D φ g hκ) := by
  subst hφ
  refine ext_level hθ D fun x ↦ ?_
  rw [fst_levelMap hθ D D (φ'.comp φ) g'' hκ'' x, AlgHom.comp_apply,
    fst_levelMap hθ D D φ' g' hκ', fst_levelMap hθ D D φ g hκ x, pMap_comp D D D φ φ',
    AlgHom.comp_apply]

omit [∀ n, IsNoetherianRing (R n)] in
/-- The lifted formal model over a zero completion is zero. -/
lemma subsingleton_NFall_of (h : Subsingleton (FormalPatchLevel.Hat (f n))) :
    Subsingleton (NFall D.L D.M) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_zero (algebraMap (FormalPatchLevel.Hat (f n)) (NFall D.L D.M)),
    ← map_one (algebraMap (FormalPatchLevel.Hat (f n)) (NFall D.L D.M))]
  exact congrArg _ (Subsingleton.elim _ _)

/-- `KappaCompat` holds trivially if the target formal model is zero. -/
lemma kappaCompat_of_subsingleton (h : Subsingleton (NFall D.L D.M))
    (φ : cov₀.C →ₐ[R₀] cov₀.C) (g : NFall D.L D.M →ₐ[R n] NFall D.L D.M) :
    KappaCompat hθ D D φ g := fun _ ↦ by
  haveI := (Ideal.Quotient.mk_surjective (I := (J θ).map (algebraMap (R n)
    (NFall D.L D.M)))).subsingleton
  exact Subsingleton.elim _ _

end Level

namespace Data

variable [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (T : Data (θ := θ) R cov₀ πL) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hs : ∀ n, Subsingleton (FormalPatchLevel.Hat (T.f n)))

/-- **The endomorphism of the level `n` of a tower with zero formal models** induced by an
endomorphism `φ` of the special-fibre covering (`levelMap` with the identity of the zero formal
model). -/
def zEnd (φ : cov₀.C →ₐ[R₀] cov₀.C) (n : ℕ) : T.G hθ n →ₐ[R n] T.G hθ n :=
  levelMap hθ (T.level n) (T.level n) φ (AlgHom.id _ _)
    (kappaCompat_of_subsingleton hθ _ (subsingleton_NFall_of _ (hs n)) φ _)

omit [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
lemma zEnd_id (n : ℕ) : T.zEnd hθ hs (AlgHom.id _ _) n = AlgHom.id _ _ :=
  levelMap_eq_id hθ (T.level n) rfl _ _

omit [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
lemma zEnd_comp (φ ψ : cov₀.C →ₐ[R₀] cov₀.C) (n : ℕ) :
    T.zEnd hθ hs (ψ.comp φ) n = (T.zEnd hθ hs ψ n).comp (T.zEnd hθ hs φ n) :=
  levelMap_eq_comp hθ (T.level n) rfl _ _ _ _ _ _

lemma tr_zEnd (φ : cov₀.C →ₐ[R₀] cov₀.C) (n : ℕ) (x : T.G hθ (n + 1)) :
    T.tr hθ hO n (T.zEnd hθ hs φ (n + 1) x) = T.zEnd hθ hs φ n (T.tr hθ hO n x) := by
  rw [tr_eq_tr]
  exact tr_levelMap hθ hO T.hq T.hf T.he T.level T.hcχ _ _ T.hct T.level T.hcχ _ _ T.hct φ
    (fun _ ↦ AlgHom.id _ _) _ n x

end Data

end LevelTower

/-! ### Generic: endomorphisms of the coverings over the first chart -/

namespace NodeEtaleGlue.Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {R₀' : Type u} [CommRing R₀'] [Algebra k R₀'] {f₀' : R₀'}
  {φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀'} {ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀'}
  {cov₀' : Admissible.Covering φ₀' ψ₀'} {πL' : cov₀'.ι → O}
  (I : Input θ cov₀ πL) (I' : Input θ cov₀' πL') (hθ : Function.Surjective θ) (n : ℕ)

/-- **The hypothesis `hg` of `Input.yMap`** (compatibility of `g` and `e` on `E n[1/a]`). -/
def HgAt (g : I.T.G hθ n →+* I'.T.G hθ n) (e : I.E n →+* I'.E n)
    (he : e (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I'.B n) (I'.E n) (I'.a n)) :
    Prop :=
  ∀ x, ρa0 I'.T hθ I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha I'.hι I'.E I'.σE
    I'.hbE I'.hdiv I'.hJB I'.B0 n (g x) =
    I.eab I' n e he (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hJB I.B0 n x)

variable (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hs : ∀ n, Subsingleton (FormalPatchLevel.Hat (I.T.f n))) (φ : cov₀.C →ₐ[R₀] cov₀.C)
  (e : ∀ n, I.E n →ₐ[I.B n] I.E n)

/-- The compatibility of the endomorphisms of the patches and of the étale pieces. -/
def HgEnd : Prop :=
  ∀ n, I.HgAt I hθ n (I.T.zEnd hθ hs φ n).toRingHom (e n).toRingHom ((e n).commutes _)

/-- **The endomorphism of the covering over the first chart at level `n`** for a tower with zero
formal models (`yMap` of `zEnd φ` and `e`). -/
def yEnd (hg : I.HgEnd hθ hs φ e) (n : ℕ) : I.Y hθ n →+* I.Y hθ n :=
  I.yMap I hθ n (I.T.zEnd hθ hs φ n).toRingHom (e n).toRingHom ((e n).commutes _) (hg n)

lemma yEnd_succ (hg : I.HgEnd hθ hs φ e) (heS : ∀ n x, I.sE n (e (n + 1) x) = e n (I.sE n x))
    (n : ℕ) (z : I.Y hθ (n + 1)) :
    I.Ymap hθ hO n (I.yEnd hθ hs φ e hg (n + 1) z) = I.yEnd hθ hs φ e hg n (I.Ymap hθ hO n z) :=
  I.yMap_succ I hθ hO (fun n ↦ (I.T.zEnd hθ hs φ n).toRingHom) (fun n ↦ (e n).toRingHom)
    (fun n ↦ (e n).commutes _) hg (I.T.tr_zEnd hθ hO hs φ) heS n z

lemma yEnd_algebraMap (hg : I.HgEnd hθ hs φ e) (n : ℕ) (b : I.B0) :
    I.yEnd hθ hs φ e hg n (algebraMap I.B0 (I.Y hθ n) b) = algebraMap I.B0 (I.Y hθ n) b :=
  I.yMap_algebraMap I hθ n _ _ ((e n).commutes _) (hg n) (RingHom.id _)
    (fun _ ↦ (I.T.zEnd hθ hs φ n).commutes _) (fun _ ↦ (e n).commutes _) b

end NodeEtaleGlue.Input

/-! ### Generic: the endomorphism of the adic system of an overlap -/

namespace NodeEtaleGlue.Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (y : ∀ n, I.Y hθ n →+* I.Y hθ n)
  (hy : ∀ n b, y n (algebraMap I.B0 (I.Y hθ n) b) = algebraMap I.B0 (I.Y hθ n) b)
  (hyS : ∀ n z, I.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z))
  (p : ∀ n, V.P0.P n →+* V.P0.P n)
  (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
    algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0))
  (hpO : ∀ n (o : O), p n (algebraMap O (V.P0.P n) o) = algebraMap O (V.P0.P n) o)
  (hψ : ∀ n z, V.ψ hθ hO n (y n z) = V.mM V n (p n) (hp0 n) (V.ψ hθ hO n z))
  (hpS : ∀ n e, V.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e))

/-- **The endomorphism of the two-chart ring at level `n`** from endomorphisms `y n` of the
covering over the first chart (fixing `B0`) and `p n` of the piece over the second chart. -/
def twoChartEnd (n : ℕ) : SemistableReduction.TwoChartMap (A := O) (V.twoChart hθ hO n)
    (V.twoChart hθ hO n) :=
  V.twoChartMap V hθ hO n (y n) (hy n V.x1) (fun o ↦ hy n (@algebraMap O I.B0 _ _ V.algOB0 o))
    (p n) (hp0 n) (hpO n) (hψ n)

/-- **The endomorphism of the adic system of chart algebras** (`TwoChartTower.systemShiftHom`). -/
def systemEnd : ProjectiveLine.AdicChartAlgSystem.Hom (V.system hθ hO) (V.system hθ hO) :=
  TwoChartTower.systemShiftHom _ (V.twoChartEnd hθ hO y hy p hp0 hpO hψ)
    (fun n ↦ V.succ_comp_twoChartMap V hθ hO y (fun n ↦ hy n V.x1)
      (fun n o ↦ hy n (@algebraMap O I.B0 _ _ V.algOB0 o)) p hp0 hpO
      hψ hyS hpS n)

end NodeEtaleGlue.Overlap

end

end SemistableReduction
