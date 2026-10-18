/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelTowerData
import TemperedFundamentalGroups.SemistableReduction.AdmissibleEtaleLift

/-!
# Constructing the tower of patched algebras (Blueprint §12.8, M2.3 (e'), tower)

Given, at every level `n` of a tower of charts (`LevelTower`), formal node coordinates
`χ n j : O[u,v]/(uv − π_j^{e_j}) → R̂_n` and a coordinate `t n ∈ R̂_n` at the marked points
lifting those of the transported covering `cov₀.transport (e n)`, compatible under the
completion maps `ψ₂ : R̂_{n+1} → R̂_n`, together with the flatness, regularity and nilpotence
hypotheses of `patch_specF`:

* `LevelTower.mkLevel n`: the patching data at level `n` — lifted idempotents chosen by
  `AdmissibleLift.exists_idem_lift`, the étale lift `P` over `D(f n)` chosen by
  `AwayLift.exists_lift` (independent choices at each level);
* `hεε_mk`, `hδδ_mk`: the chosen idempotents are automatically compatible (`eq_idem₂`);
* **`LevelTower.trMk`**: the transition maps `G (n+1) → G n` of the tower of patched algebras,
  surjective with kernel `(ker q_n) G (n+1)` (`surjective_trMk`, `ker_trMk`), and
  **`LevelTower.spec_mk`**: each `G n` is finite over `R n`, equal to `P n` on `D(f n)` and to the
  lifted formal model along `V(f n)`;
* **`LevelTower.Data`**: all this data bundled in one structure, with `Data.G`, `Data.tr`,
  `Data.surjective_tr`, `Data.ker_tr` (`ker_tr_of`: `= I G (n+1)` if `ker q_n = I R (n+1)`),
  `Data.tr_algebraMap`, `Data.spec`. Concrete towers (e.g. `QuadNodeTower.tower`) are single
  definitions of type `Data`, to which these apply without re-elaborating the patched algebras.
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

noncomputable section

namespace LevelTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} (hfe : ∀ n, e n f₀ = fbar θ (f n))
  (hπ : ∀ j, θ (πL j) = 0)
  (χ : ∀ n j, A (πL j) (cov₀.e j) →ₐ[O] FormalPatchLevel.Hat (f n))
  (hχ : ∀ n j a, ψ θ (f n) (χ n j a) = Admissible.φT (h := hfe n) φ₀
    (Admissible.nodeCongr (cov₀.e_pos j) (Node.baseMap θ (hA (hπ j)) a)))
  (t : ∀ n, FormalPatchLevel.Hat (f n))
  (ht : ∀ n, ψ θ (f n) (t n) = Admissible.ψT (h := hfe n) ψ₀ Polynomial.X)
  {m : ℕ → ℕ} (hJ : ∀ n, J θ (R := R n) ^ m n = ⊥)
  {I : ℕ → Ideal O} (hflat : ∀ n j, KummerFactorQuot.KFlat (I n) (χ n j).toRingHom)
  (hfχ : ∀ n j, χ n j (fA (πL j)) = algebraMap (R n) (FormalPatchLevel.Hat (f n)) (f n))
  (hreg : ∀ n (y : FormalPatchLevel.Hat (f n)), algebraMap (R n) _ (f n) * y = 0 → y = 0)

include hJ in
lemma exists_ε (n : ℕ) (j : cov₀.ι) : ∃ ε : FormalPatchLevel.Hat (f n), IsIdempotentElem ε ∧
    ψ θ (f n) ε = Admissible.hatEquiv (e n) (hfe n) (cov₀.idem j) :=
  exists_idem_lift θ (hJ n) ((cov₀.transport (h := hfe n)).isIdempotentElem_idem j)

include hJ in
lemma exists_δ (n : ℕ) (i : cov₀.κ) : ∃ δ : FormalPatchLevel.Hat (f n), IsIdempotentElem δ ∧
    ψ θ (f n) δ = Admissible.hatEquiv (e n) (hfe n) (cov₀.cidem i) :=
  exists_idem_lift θ (hJ n) ((cov₀.transport (h := hfe n)).isIdempotentElem_cidem i)

include hJ in
lemma exists_P (n : ℕ) :
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra (R n) P), Algebra.FormallyEtale (R n) P ∧
      IsUnit (algebraMap (R n) P (f n)) ∧
      (∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f n ^ k • p ∈ Submodule.span (R n) (s : Set P)) ∧
      Nonempty ((P ⧸ (J θ).map (algebraMap (R n) P)) ≃ₐ[R n]
        Localization.Away (algebraMap (R n) (cov₀.transport (h := hfe n)).C (f n))) :=
  haveI : Module.Finite (R n ⧸ J θ) (cov₀.transport (h := hfe n)).C :=
    (cov₀.transport (h := hfe n)).finite
  AwayLift.exists_lift (J θ) (f n) (hJ n) (C := (cov₀.transport (h := hfe n)).C)
    (cov₀.transport (h := hfe n)).etale

/-- **The patching data at level `n`** built from the coordinates `χ n`, `t n`. -/
def mkLevel (n : ℕ) : Level R cov₀ πL hfe n where
  L :=
    { hπ := hπ
      χ := χ n
      ε := fun j ↦ (exists_ε hfe hJ n j).choose
      hε := fun j ↦ (exists_ε hfe hJ n j).choose_spec.2
      hχ := hχ n }
  M :=
    { t := t n
      ht := ht n
      δ := fun i ↦ (exists_δ hfe hJ n i).choose
      hδ := fun i ↦ (exists_δ hfe hJ n i).choose_spec.2 }
  m := m n
  hJ := hJ n
  I := I n
  hflat := hflat n
  hidem := fun j ↦ (exists_ε hfe hJ n j).choose_spec.1
  hfχ := hfχ n
  hcidem := fun i ↦ (exists_δ hfe hJ n i).choose_spec.1
  hreg := hreg n
  P := (exists_P hfe hJ n).choose
  commRing := (exists_P hfe hJ n).choose_spec.choose
  algebra := (exists_P hfe hJ n).choose_spec.choose_spec.choose
  etale := (exists_P hfe hJ n).choose_spec.choose_spec.choose_spec.1
  σP := (exists_P hfe hJ n).choose_spec.choose_spec.choose_spec.2.2.2.some
  hfP := (exists_P hfe hJ n).choose_spec.choose_spec.choose_spec.2.1
  hP := (exists_P hfe hJ n).choose_spec.choose_spec.choose_spec.2.2.1

variable (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

include hO in
/-- **Level-`n` patching** for the constructed data. -/
theorem spec_mk (n : ℕ) :
    Module.Finite (R n) ((mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg n).G hθ) ∧
      IsBaseChange (FormalPatchLevel.Hat (f n))
        (FormalGlueing.snd (NFall (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg n).L
          (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg n).M)
          (FormalPatchLevel.lift (f n) (J θ) (hJ n)
          (FormalPatchLevel.alphaOfEquiv (f n) (J θ)
            (FormalPatchLevel.specialFibreEquiv (f n) (J θ)
              (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg n).σP
              (kappaF (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg n).L
                (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg n).M hθ))))).toLinearMap :=
  ⟨(Level.spec hθ hO _).1, (Level.spec hθ hO _).2.2⟩

variable [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (hq : ∀ n, Function.Surjective (algebraMap (R (n + 1)) (R n)))
  (hf : ∀ n, LevelStep.f' (R' := R n) (f (n + 1)) = f n)
  (he : ∀ n (r : R (n + 1)), e n ((e (n + 1)).symm (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (algebraMap (R (n + 1)) (R n) r))
  (hcχ : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (χ (n + 1) j a) = χ n j a)
  (hct : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (t (n + 1)) = t n)

omit [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
include he in
lemma hεε_mk (n : ℕ) (j : cov₀.ι) :
    LevelStep.ψ₂ (f (n + 1)) (f n) (hf n)
        ((mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg (n + 1)).L.ε j) =
      (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg n).L.ε j :=
  LevelStep.eq_idem₂ (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) (hJ n)
    (exists_ε hfe hJ (n + 1) j).choose_spec.1 (exists_ε hfe hJ (n + 1) j).choose_spec.2
    (exists_ε hfe hJ n j).choose_spec.1 (exists_ε hfe hJ n j).choose_spec.2

omit [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
include he in
lemma hδδ_mk (n : ℕ) (i : cov₀.κ) :
    LevelStep.ψ₂ (f (n + 1)) (f n) (hf n)
        ((mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg (n + 1)).M.δ i) =
      (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg n).M.δ i :=
  LevelStep.eq_idem₂ (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) (hJ n)
    (exists_δ hfe hJ (n + 1) i).choose_spec.1 (exists_δ hfe hJ (n + 1) i).choose_spec.2
    (exists_δ hfe hJ n i).choose_spec.1 (exists_δ hfe hJ n i).choose_spec.2

/-- **The transition maps of the tower of patched algebras** built from compatible coordinates. -/
def trMk (n : ℕ) : (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg (n + 1)).G hθ →+*
    (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg n).G hθ :=
  tr hθ hO hq hf he (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg) hcχ
    (hεε_mk hfe hπ χ hχ t ht hJ hflat hfχ hreg hf he)
    (hδδ_mk hfe hπ χ hχ t ht hJ hflat hfχ hreg hf he) hct n

/-- The transition maps are surjective. -/
theorem surjective_trMk (n : ℕ) :
    Function.Surjective (trMk hfe hπ χ hχ t ht hJ hflat hfχ hreg hθ hO hq hf he hcχ hct n) :=
  surjective_tr hθ hO hq hf he (mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg) hcχ
    (hεε_mk hfe hπ χ hχ t ht hJ hflat hfχ hreg hf he)
    (hδδ_mk hfe hπ χ hχ t ht hJ hflat hfχ hreg hf he) hct n

/-- **The kernel of the transition map** `G (n+1) → G n` is `(ker q_n) G (n+1)`. -/
theorem ker_trMk (n : ℕ) :
    RingHom.ker (trMk hfe hπ χ hχ t ht hJ hflat hfχ hreg hθ hO hq hf he hcχ hct n) =
      (RingHom.ker (algebraMap (R (n + 1)) (R n))).map
        (algebraMap (R (n + 1)) ((mkLevel hfe hπ χ hχ t ht hJ hflat hfχ hreg (n + 1)).G hθ)) :=
  ker_tr ..

/-- The transition maps are semilinear over `q_n`. -/
theorem trMk_algebraMap (n : ℕ) (r : R (n + 1)) :
    trMk hfe hπ χ hχ t ht hJ hflat hfχ hreg hθ hO hq hf he hcχ hct n (algebraMap (R (n + 1)) _ r) =
      algebraMap (R n) _ (algebraMap (R (n + 1)) (R n) r) :=
  tr_algebraMap ..


/-! ### The bundled tower

All data of a tower in one structure, so that instances (e.g. the Tate tower) are a single
definition and the generic statements apply to them without re-elaborating the patched algebras. -/

variable (R) in
/-- **The data of a tower of patched algebras**: compatible coordinates on the level charts
`R n` together with the hypotheses of `trMk`. -/
structure Data (cov₀ : Admissible.Covering φ₀ ψ₀) (πL : cov₀.ι → O) where
  f : ∀ n, R n
  e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))
  hfe : ∀ n, e n f₀ = fbar θ (f n)
  hπ : ∀ j, θ (πL j) = 0
  χ : ∀ n j, A (πL j) (cov₀.e j) →ₐ[O] FormalPatchLevel.Hat (f n)
  hχ : ∀ n j a, ψ θ (f n) (χ n j a) = Admissible.φT (h := hfe n) φ₀
    (Admissible.nodeCongr (cov₀.e_pos j) (Node.baseMap θ (hA (hπ j)) a))
  t : ∀ n, FormalPatchLevel.Hat (f n)
  ht : ∀ n, ψ θ (f n) (t n) = Admissible.ψT (h := hfe n) ψ₀ Polynomial.X
  m : ℕ → ℕ
  hJ : ∀ n, J θ (R := R n) ^ m n = ⊥
  I : ℕ → Ideal O
  hflat : ∀ n j, KummerFactorQuot.KFlat (I n) (χ n j).toRingHom
  hfχ : ∀ n j, χ n j (fA (πL j)) = algebraMap (R n) (FormalPatchLevel.Hat (f n)) (f n)
  hreg : ∀ n (y : FormalPatchLevel.Hat (f n)), algebraMap (R n) _ (f n) * y = 0 → y = 0
  hq : ∀ n, Function.Surjective (algebraMap (R (n + 1)) (R n))
  hf : ∀ n, LevelStep.f' (R' := R n) (f (n + 1)) = f n
  he : ∀ n (r : R (n + 1)), e n ((e (n + 1)).symm (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (algebraMap (R (n + 1)) (R n) r)
  hcχ : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (χ (n + 1) j a) = χ n j a
  hct : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (t (n + 1)) = t n

namespace Data

variable (T : Data (θ := θ) R cov₀ πL)

/-- The patching data at level `n`. -/
abbrev level (n : ℕ) : Level R cov₀ πL T.hfe n :=
  mkLevel T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg n

/-- The patched algebra at level `n`. -/
abbrev G (n : ℕ) : Type u := (T.level n).G hθ

/-- **The transition map** `G (n+1) → G n`. -/
def tr (n : ℕ) : T.G hθ (n + 1) →+* T.G hθ n :=
  trMk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg hθ hO T.hq T.hf T.he T.hcχ T.hct n

/-- The transition maps are surjective. -/
theorem surjective_tr (n : ℕ) : Function.Surjective (T.tr hθ hO n) :=
  surjective_trMk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg hθ hO T.hq T.hf T.he
    T.hcχ T.hct n

/-- **The kernel of the transition map** `G (n+1) → G n` is `(ker q_n) G (n+1)`. -/
theorem ker_tr (n : ℕ) : RingHom.ker (T.tr hθ hO n) =
    (RingHom.ker (algebraMap (R (n + 1)) (R n))).map (algebraMap (R (n + 1)) (T.G hθ (n + 1))) :=
  ker_trMk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg hθ hO T.hq T.hf T.he T.hcχ T.hct n

/-- If `ker q_n = I R (n+1)` for an ideal `I` of `O`, then the kernel of the transition map is
`I G (n+1)`. -/
theorem ker_tr_of {I : Ideal O} {n : ℕ}
    (hI : RingHom.ker (algebraMap (R (n + 1)) (R n)) = I.map (algebraMap O (R (n + 1)))) :
    RingHom.ker (T.tr hθ hO n) =
      I.map ((algebraMap (R (n + 1)) (T.G hθ (n + 1))).comp (algebraMap O (R (n + 1)))) := by
  rw [T.ker_tr hθ hO n, hI, Ideal.map_map]

/-- The transition maps are semilinear over `q_n`. -/
theorem tr_algebraMap (n : ℕ) (r : R (n + 1)) :
    T.tr hθ hO n (algebraMap (R (n + 1)) _ r) =
      algebraMap (R n) _ (algebraMap (R (n + 1)) (R n) r) :=
  trMk_algebraMap T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg hθ hO T.hq T.hf T.he
    T.hcχ T.hct n r

omit [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
include hO in
/-- **Level-`n` patching**: `G n` is finite over `R n` and equal to the lifted formal model along
`V(f n)` (for `G n` on `D(f n)` see `Level.spec`). -/
theorem spec (n : ℕ) :
    Module.Finite (R n) ((T.level n).G hθ) ∧
      IsBaseChange (FormalPatchLevel.Hat (T.f n))
        (FormalGlueing.snd (NFall (T.level n).L (T.level n).M)
          (FormalPatchLevel.lift (T.f n) (J θ) (T.hJ n)
          (FormalPatchLevel.alphaOfEquiv (T.f n) (J θ)
            (FormalPatchLevel.specialFibreEquiv (T.f n) (J θ) (T.level n).σP
              (kappaF (T.level n).L (T.level n).M hθ))))).toLinearMap :=
  ⟨(Level.spec hθ hO (T.level n)).1, (Level.spec hθ hO (T.level n)).2.2⟩

end Data

end LevelTower

end

end SemistableReduction
