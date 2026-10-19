/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueOverlap

/-!
# The maps to étale algebras over an overlap along the tower (Blueprint §12.8, M2.3 (f), tower)

For an input `I : NodeEtaleGlue.Input`, `g ∈ B0` with `f n ∣ gᵏ` at the levels `n` and `n + 1`,
and formally étale algebras `M0` over `B n`, `M1` over `B (n+1)` with special fibres `C1[1/ḡ]`
(`γ0`, `γ1`), connected by a ring map `s : M1 → M0` over `B (n+1) → B n` compatible with `γ0`,
`γ1`:

* `Input.trg`, `Input.sEg`, `Input.ρPg`: the successor maps `tr n`, `sE n`, `ρP n` localized
  away from `g`;
* `Input.φPn_succ`, `Input.φEn_succ`: the étale lifts `M → P n[1/g]`, `M → E n[1/g]` commute with
  the successor maps (`EtaleNil.ext_of_comp` over `B (n+1)`, `NodeEtaleGlue.J_succ`);
* **`NodeEtaleGlue.Input.ψ_succ`**: the maps `ψ : Y n → M` (`Input.ψ`) commute with the successor
  maps, `s ∘ ψ (n+1) = ψ n ∘ Ymap n`.
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O} (I : Input θ cov₀ πL)
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (n : ℕ) (g : I.B0)

/-! ### The components at one level -/

section Level

variable {kg : ℕ}
  (hfg : I.T.f n ∣ algebraMap (I.B n) (I.R n) (algebraMap I.B0 (I.B n) g) ^ kg)
  {M : Type u} [CommRing M] [Algebra (I.B n) M] [Algebra.FormallyEtale (I.B n) M]
  (γM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    I.C1 →ₐ[I.B n] M ⧸ EtaleNil.JB (J θ (R := I.B n)) M)
  (hM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    letI := γM.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) I.C1 (algebraMap I.B0 (I.B n) g))
      (M ⧸ EtaleNil.JB (J θ (R := I.B n)) M))

/-- `G m[1/g]` (a `def` with explicit instances, so that statements mentioning two levels need
no competing local instances `B0 → G m`). -/
def LcG (m : ℕ) : Type u :=
  Localization.Away (@algebraMap I.B0 (I.T.G hθ m) _ _ (alg0G I.T hθ I.B I.B0 m) g)

instance (m : ℕ) : CommRing (I.LcG hθ g m) :=
  inferInstanceAs (CommRing (Localization.Away
    (@algebraMap I.B0 (I.T.G hθ m) _ _ (alg0G I.T hθ I.B I.B0 m) g)))

instance (m : ℕ) : Algebra (I.T.G hθ m) (I.LcG hθ g m) :=
  inferInstanceAs (Algebra (I.T.G hθ m) (Localization.Away
    (@algebraMap I.B0 (I.T.G hθ m) _ _ (alg0G I.T hθ I.B I.B0 m) g)))

instance (m : ℕ) : IsLocalization.Away
    (@algebraMap I.B0 (I.T.G hθ m) _ _ (alg0G I.T hθ I.B I.B0 m) g) (I.LcG hθ g m) :=
  Localization.isLocalization

include hO hfg in
/-- `G n[1/g] ≃ P n[1/g]` (`EtaleOverlap.eG`). -/
def eGn : letI := algBP I.T I.B n; I.LcG hθ g n ≃+* I.Pg n g := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := algBP I.T I.B n
  haveI := towerBP I.T I.B n
  letI := algBG I.T hθ I.B n
  haveI := towerBG I.T hθ I.B n
  haveI := I.isLocalization_LcG hθ n g
  exact (EtaleOverlap.eG (I.T.f n) (algebraMap I.B0 (I.B n) g) (fstP I.T hθ n)
    (isLocalization_fstP I.T hθ hO n) hfg (Pg := I.Pg n g)
      (Gg := ZariskiTwo.Lc g (I.T.G hθ n))).toRingEquiv

lemma eGn_algebraMap (x : I.T.G hθ n) : letI := algBP I.T I.B n
    I.eGn hθ hO n g hfg (algebraMap _ (I.LcG hθ g n) x) =
      algebraMap (I.T.level n).P (I.Pg n g) x.1.1 := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := algBP I.T I.B n
  haveI := towerBP I.T I.B n
  letI := algBG I.T hθ I.B n
  haveI := towerBG I.T hθ I.B n
  haveI := I.isLocalization_LcG hθ n g
  exact EtaleOverlap.eG_algebraMap (I.T.f n) (algebraMap I.B0 (I.B n) g) (fstP I.T hθ n)
    (isLocalization_fstP I.T hθ hO n) hfg (Pg := I.Pg n g) (Gg := ZariskiTwo.Lc g (I.T.G hθ n)) x

/-- The special fibre `C1 → P n[1/g]/J` (`EtaleOverlap.γP`). -/
def γPn : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n; letI := algBP I.T I.B n
    I.C1 →ₐ[I.B n] I.Pg n g ⧸ EtaleNil.JB (J θ (R := I.B n)) (I.Pg n g) := by
  letI := algBP I.T I.B n
  haveI := towerBP I.T I.B n
  letI := algBC I.T I.B n
  haveI := towerBC I.T I.B n
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  exact EtaleOverlap.γP (J θ (R := I.B n)) (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n) (I.T.f n)
    (σPn I.T I.B n) (Pg := I.Pg n g)

include hfg in
/-- The étale lift `M → P n[1/g]` (`EtaleOverlap.φP`). -/
def φPn : letI := algBP I.T I.B n; M →ₐ[I.B n] I.Pg n g := by
  letI := algBP I.T I.B n
  haveI := towerBP I.T I.B n
  letI := algBC I.T I.B n
  haveI := towerBC I.T I.B n
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  exact EtaleOverlap.φP (J θ (R := I.B n)) (I.hJB n) (I.a n) (I.R n)
    (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n) (I.T.f n) (σPn I.T I.B n)
    (isLocalization_ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.ha I.hι n)
    (algebraMap I.B0 (I.B n) g) hfg γM hM

lemma red_φPn (c : I.C1) : letI := algBP I.T I.B n
    EtaleNil.red (J θ (R := I.B n)) (I.φPn n g hfg γM hM) (γM c) = I.γPn n g c := by
  letI := algBP I.T I.B n
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  exact EtaleNil.red_liftLoc_comp (J θ (R := I.B n)) (I.hJB n) γM (I.γPn n g) _ (I.a n) hM _ c

lemma γPn_eq (c : I.C1) (p : (I.T.level n).P)
    (hp : (I.T.level n).σP (Ideal.Quotient.mk _ p) =
      algebraMap (Cc I.T n) (Localization.Away (algebraMap (I.R n) (Cc I.T n) (I.T.f n)))
        (I.ι₀ c)) : letI := algBP I.T I.B n
    I.γPn n g c = Ideal.Quotient.mk _ (algebraMap (I.T.level n).P (I.Pg n g) p) := by
  letI := algBP I.T I.B n
  letI := algBC I.T I.B n
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  have h : (σPn I.T I.B n).symm (algebraMap (Cc I.T n) _
      (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n c)) = Ideal.Quotient.mk _ p := by
    apply (σPn I.T I.B n).injective
    rw [AlgEquiv.apply_symm_apply]
    exact hp.symm
  change EtaleNil.red _ _ ((σPn I.T I.B n).symm (algebraMap (Cc I.T n) _
      (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n c))) = _
  rw [h]
  rfl

/-- The special fibre `C1 → E n[1/g]/J` (`EtaleOverlap.γE`). -/
def γEn : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n; letI := alg0 I.B I.B0 n (I.E n)
    I.C1 →ₐ[I.B n] ZariskiTwo.Lc g (I.E n) ⧸
      EtaleNil.JB (J θ (R := I.B n)) (ZariskiTwo.Lc g (I.E n)) := by
  letI := alg0 I.B I.B0 n (I.E n)
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  haveI : IsLocalization.Away (algebraMap (I.B n) (I.E n) (algebraMap I.B0 (I.B n) g))
      (ZariskiTwo.Lc g (I.E n)) := Localization.isLocalization
  exact EtaleOverlap.γE (J θ (R := I.B n)) (I.σE n) (Eg := ZariskiTwo.Lc g (I.E n))

/-- The étale lift `M → E n[1/g]` (`EtaleOverlap.φE`). -/
def φEn : letI := alg0 I.B I.B0 n (I.E n); M →ₐ[I.B n] ZariskiTwo.Lc g (I.E n) := by
  letI := alg0 I.B I.B0 n (I.E n)
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  haveI := isLocalization_C1 I.B I.qB I.C1 I.b I.hbb n
  haveI : IsLocalization.Away (algebraMap (I.B n) (I.E n) (algebraMap I.B0 (I.B n) g))
      (ZariskiTwo.Lc g (I.E n)) := Localization.isLocalization
  exact EtaleOverlap.φE (J θ (R := I.B n)) (I.hJB n) (I.b n) (I.σE n)
    (algebraMap I.B0 (I.B n) g) γM hM (Eg := ZariskiTwo.Lc g (I.E n))

lemma red_φEn (c : I.C1) : letI := alg0 I.B I.B0 n (I.E n)
    EtaleNil.red (J θ (R := I.B n)) (I.φEn n g γM hM) (γM c) = I.γEn n g c := by
  letI := alg0 I.B I.B0 n (I.E n)
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  exact EtaleNil.red_liftLoc_comp (J θ (R := I.B n)) (I.hJB n) γM (I.γEn n g) _ (I.b n) hM _ c

lemma γEn_eq (c : I.C1) (e : I.E n)
    (he : I.σE n (Ideal.Quotient.mk _ e) =
      algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) c) :
    letI := alg0 I.B I.B0 n (I.E n)
    I.γEn n g c = Ideal.Quotient.mk _ (algebraMap (I.E n) (ZariskiTwo.Lc g (I.E n)) e) := by
  letI := alg0 I.B I.B0 n (I.E n)
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  have h : (I.σE n).symm (algebraMap I.C1 _ c) = Ideal.Quotient.mk _ e := by
    apply (I.σE n).injective
    rw [AlgEquiv.apply_symm_apply]
    exact he.symm
  change EtaleNil.red _ _ ((I.σE n).symm (algebraMap I.C1 _ c)) = _
  rw [h]
  rfl

/-! ### The components of the glueings -/

/-- The first component `Y n[1/g] → G n[1/g]`. -/
def fstYg (x : I.Yg hθ n g) : I.LcG hθ g n := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  exact ZariskiTwo.fst (ZariskiTwo.ρaL g (ρa := I.ρA hθ n)) (ZariskiTwo.ρbL g (ρb := I.ρB n)) x

/-- The second component `Y n[1/g] → E n[1/g]`. -/
def sndYg (x : I.Yg hθ n g) : letI := alg0 I.B I.B0 n (I.E n); ZariskiTwo.Lc g (I.E n) := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  exact ZariskiTwo.snd (ZariskiTwo.ρaL g (ρa := I.ρA hθ n)) (ZariskiTwo.ρbL g (ρb := I.ρB n)) x

lemma Yg_ext {x y : I.Yg hθ n g} (h1 : I.fstYg hθ n g x = I.fstYg hθ n g y)
    (h2 : I.sndYg hθ n g x = I.sndYg hθ n g y) : x = y :=
  Subtype.ext (Prod.ext h1 h2)

/-- The first component `Y n → G n`. -/
def fstY (x : I.Y hθ n) : I.T.G hθ n := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  exact ZariskiTwo.fst (I.ρA hθ n) (I.ρB n) x

/-- The second component `Y n → E n`. -/
def sndY (x : I.Y hθ n) : I.E n := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  exact ZariskiTwo.snd (I.ρA hθ n) (I.ρB n) x

lemma fstYg_mapYg (w : I.Y hθ n) :
    I.fstYg hθ n g (I.mapYg hθ n g w) = algebraMap (I.T.G hθ n) (I.LcG hθ g n) (I.fstY hθ n w) :=
  rfl

lemma sndYg_mapYg (w : I.Y hθ n) : letI := alg0 I.B I.B0 n (I.E n)
    I.sndYg hθ n g (I.mapYg hθ n g w) =
      algebraMap (I.E n) (ZariskiTwo.Lc g (I.E n)) (I.sndY hθ n w) := rfl

variable [Algebra I.B0 M] [IsScalarTower I.B0 (I.B n) M]

lemma fstYg_glueM (m : M) : letI := algBP I.T I.B n
    I.fstYg hθ n g (I.glueM hθ hO n g hfg γM hM m) =
      (I.eGn hθ hO n g hfg).symm (I.φPn n g hfg γM hM m) := rfl

lemma sndYg_glueM (m : M) :
    I.sndYg hθ n g (I.glueM hθ hO n g hfg γM hM m) = I.φEn n g γM hM m := rfl

end Level

/-! ### The successor maps localized at `g` -/

section Maps

lemma ρP_algebraMapB (x : I.B (n + 1)) : letI := algBP I.T I.B (n + 1); letI := algBP I.T I.B n
    I.T.ρP n (algebraMap (I.B (n + 1)) (I.T.level (n + 1)).P x) =
      algebraMap (I.B n) (I.T.level n).P (algebraMap (I.B (n + 1)) (I.B n) x) := by
  letI := algBP I.T I.B (n + 1)
  letI := algBP I.T I.B n
  letI := algP I.T.level n
  change I.T.ρP n (algebraMap (I.R (n + 1)) _ (algebraMap (I.B (n + 1)) (I.R (n + 1)) x)) = _
  rw [AlgHom.commutes]
  change algebraMap (I.R n) _ (algebraMap (I.R (n + 1)) (I.R n)
    (algebraMap (I.B (n + 1)) (I.R (n + 1)) x)) = _
  rw [I.hBR]
  rfl

lemma isUnit_ρPg : letI := algBP I.T I.B (n + 1); letI := algBP I.T I.B n
    letI := algP I.T.level n
    IsUnit (((algebraMap (I.T.level n).P (I.Pg n g)).comp
      (I.T.ρP n : (I.T.level (n + 1)).P →+* (I.T.level n).P))
        (algebraMap (I.B (n + 1)) (I.T.level (n + 1)).P (algebraMap I.B0 (I.B (n + 1)) g))) := by
  letI := algBP I.T I.B (n + 1)
  letI := algBP I.T I.B n
  letI := algP I.T.level n
  rw [RingHom.comp_apply, RingHom.coe_coe, ρP_algebraMapB,
    ← IsScalarTower.algebraMap_apply I.B0 (I.B (n + 1)) (I.B n)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- `ρP n` localized at `g`: `P (n+1)[1/g] → P n[1/g]`. -/
def ρPg : I.Pg (n + 1) g →+* I.Pg n g :=
  letI := algBP I.T I.B (n + 1)
  IsLocalization.Away.lift
    (algebraMap (I.B (n + 1)) (I.T.level (n + 1)).P (algebraMap I.B0 (I.B (n + 1)) g))
    (I.isUnit_ρPg n g)

lemma ρPg_algebraMap (p : (I.T.level (n + 1)).P) :
    I.ρPg n g (algebraMap _ (I.Pg (n + 1) g) p) =
      algebraMap (I.T.level n).P (I.Pg n g) (I.T.ρP n p) :=
  letI := algBP I.T I.B (n + 1)
  IsLocalization.Away.lift_eq _ (I.isUnit_ρPg n g) p

lemma ρPg_algebraMapB (x : I.B (n + 1)) : letI := algBP I.T I.B (n + 1)
    letI := algBP I.T I.B n
    I.ρPg n g (algebraMap (I.B (n + 1)) (I.Pg (n + 1) g) x) =
      algebraMap (I.B n) (I.Pg n g) (algebraMap (I.B (n + 1)) (I.B n) x) := by
  letI := algBP I.T I.B (n + 1)
  letI := algBP I.T I.B n
  rw [IsScalarTower.algebraMap_apply (I.B (n + 1)) (I.T.level (n + 1)).P (I.Pg (n + 1) g),
    ρPg_algebraMap, ρP_algebraMapB, ← IsScalarTower.algebraMap_apply]

lemma ρPg_mk {y y' : I.Pg (n + 1) g} (h : letI := algBP I.T I.B (n + 1)
      Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B (n + 1))) (I.Pg (n + 1) g)) y =
        Ideal.Quotient.mk _ y') : letI := algBP I.T I.B n
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (I.Pg n g)) (I.ρPg n g y) =
      Ideal.Quotient.mk _ (I.ρPg n g y') := by
  letI := algBP I.T I.B (n + 1)
  letI := algBP I.T I.B n
  rw [Ideal.Quotient.eq] at h ⊢
  rw [← map_sub]
  have hle : EtaleNil.JB (J θ (R := I.B (n + 1))) (I.Pg (n + 1) g) ≤
      (EtaleNil.JB (J θ (R := I.B n)) (I.Pg n g)).comap (I.ρPg n g) := by
    rw [EtaleNil.JB, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply, ρPg_algebraMapB]
    exact Ideal.mem_map_of_mem _ (J_le I.B n (Ideal.mem_map_of_mem _ hx))
  exact hle h

lemma isUnit_trg : IsUnit (((algebraMap (I.T.G hθ n) (I.LcG hθ g n)).comp (I.T.tr hθ hO n))
    (@algebraMap I.B0 (I.T.G hθ (n + 1)) _ _ (alg0G I.T hθ I.B I.B0 (n + 1)) g)) := by
  rw [RingHom.comp_apply, tr_algebraMap0 I.T hθ I.B hO I.hBR I.B0 n g]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- `tr n` localized at `g`: `G (n+1)[1/g] → G n[1/g]`. -/
def trg : I.LcG hθ g (n + 1) →+* I.LcG hθ g n :=
  IsLocalization.Away.lift
    (@algebraMap I.B0 (I.T.G hθ (n + 1)) _ _ (alg0G I.T hθ I.B I.B0 (n + 1)) g)
    (I.isUnit_trg hθ hO n g)

lemma trg_algebraMap (x : I.T.G hθ (n + 1)) :
    I.trg hθ hO n g (algebraMap _ (I.LcG hθ g (n + 1)) x) =
      algebraMap _ (I.LcG hθ g n) (I.T.tr hθ hO n x) :=
  IsLocalization.Away.lift_eq _ (I.isUnit_trg hθ hO n g) x

lemma isUnit_sEg : letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1)); letI := alg0 I.B I.B0 n (I.E n)
    IsUnit (((algebraMap (I.E n) (ZariskiTwo.Lc g (I.E n))).comp (I.sE n))
      (algebraMap I.B0 (I.E (n + 1)) g)) := by
  letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1))
  letI := alg0 I.B I.B0 n (I.E n)
  change IsUnit (algebraMap (I.E n) _ (I.sE n (algebraMap (I.B (n + 1)) (I.E (n + 1))
    (algebraMap I.B0 (I.B (n + 1)) g))))
  rw [I.hsE, ← IsScalarTower.algebraMap_apply I.B0 (I.B (n + 1)) (I.B n)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- `sE n` localized at `g`: `E (n+1)[1/g] → E n[1/g]`. -/
def sEg : letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1)); letI := alg0 I.B I.B0 n (I.E n)
    ZariskiTwo.Lc g (I.E (n + 1)) →+* ZariskiTwo.Lc g (I.E n) :=
  letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1))
  letI := alg0 I.B I.B0 n (I.E n)
  IsLocalization.Away.lift (algebraMap I.B0 (I.E (n + 1)) g) (I.isUnit_sEg n g)

lemma sEg_algebraMap (x : I.E (n + 1)) :
    letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1)); letI := alg0 I.B I.B0 n (I.E n)
    I.sEg n g (algebraMap _ (ZariskiTwo.Lc g (I.E (n + 1))) x) =
      algebraMap _ (ZariskiTwo.Lc g (I.E n)) (I.sE n x) :=
  letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1))
  letI := alg0 I.B I.B0 n (I.E n)
  IsLocalization.Away.lift_eq _ (I.isUnit_sEg n g) x

lemma sEg_algebraMapB (x : I.B (n + 1)) :
    letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1)); letI := alg0 I.B I.B0 n (I.E n)
    I.sEg n g (algebraMap (I.B (n + 1)) (ZariskiTwo.Lc g (I.E (n + 1))) x) =
      algebraMap (I.B n) (ZariskiTwo.Lc g (I.E n)) (algebraMap (I.B (n + 1)) (I.B n) x) := by
  letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1))
  letI := alg0 I.B I.B0 n (I.E n)
  rw [IsScalarTower.algebraMap_apply (I.B (n + 1)) (I.E (n + 1)) (ZariskiTwo.Lc g (I.E (n + 1))),
    sEg_algebraMap, I.hsE, ← IsScalarTower.algebraMap_apply]

lemma sEg_mk {y y' : letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1)); ZariskiTwo.Lc g (I.E (n + 1))}
    (h : letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1))
      Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B (n + 1))) (ZariskiTwo.Lc g (I.E (n + 1)))) y =
        Ideal.Quotient.mk _ y') : letI := alg0 I.B I.B0 n (I.E n)
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (ZariskiTwo.Lc g (I.E n))) (I.sEg n g y) =
      Ideal.Quotient.mk _ (I.sEg n g y') := by
  letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1))
  letI := alg0 I.B I.B0 n (I.E n)
  rw [Ideal.Quotient.eq] at h ⊢
  rw [← map_sub]
  have hle : EtaleNil.JB (J θ (R := I.B (n + 1))) (ZariskiTwo.Lc g (I.E (n + 1))) ≤
      (EtaleNil.JB (J θ (R := I.B n)) (ZariskiTwo.Lc g (I.E n))).comap (I.sEg n g) := by
    rw [EtaleNil.JB, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply, sEg_algebraMapB]
    exact Ideal.mem_map_of_mem _ (J_le I.B n (Ideal.mem_map_of_mem _ hx))
  exact hle h

/-- `ρP n` on lifts of the special fibre `C1 → Cc (n+1)[1/f]`. -/
lemma σP_ρP_ι (c : I.C1) (p : (I.T.level (n + 1)).P)
    (hp : (I.T.level (n + 1)).σP (Ideal.Quotient.mk _ p) =
      algebraMap (Cc I.T (n + 1))
        (Localization.Away (algebraMap (I.R (n + 1)) (Cc I.T (n + 1)) (I.T.f (n + 1)))) (I.ι₀ c)) :
    (I.T.level n).σP (Ideal.Quotient.mk _ (I.T.ρP n p)) =
      algebraMap (Cc I.T n) (Localization.Away (algebraMap (I.R n) (Cc I.T n) (I.T.f n)))
        (I.ι₀ c) := by
  rw [LevelTower.Data.σP_ρP, hp, LevelStep.Tmap_algebraMap]
  rfl

end Maps

/-! ### The étale lifts along the tower -/

section Succ

variable {kg0 kg1 : ℕ}
  (hfg0 : I.T.f n ∣ algebraMap (I.B n) (I.R n) (algebraMap I.B0 (I.B n) g) ^ kg0)
  (hfg1 : I.T.f (n + 1) ∣
    algebraMap (I.B (n + 1)) (I.R (n + 1)) (algebraMap I.B0 (I.B (n + 1)) g) ^ kg1)
  {M0 : Type u} [CommRing M0] [Algebra (I.B n) M0] [Algebra.FormallyEtale (I.B n) M0]
  (γ0 : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    I.C1 →ₐ[I.B n] M0 ⧸ EtaleNil.JB (J θ (R := I.B n)) M0)
  (hM0 : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    letI := γ0.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) I.C1 (algebraMap I.B0 (I.B n) g))
      (M0 ⧸ EtaleNil.JB (J θ (R := I.B n)) M0))
  {M1 : Type u} [CommRing M1] [Algebra (I.B (n + 1)) M1]
  [Algebra.FormallyEtale (I.B (n + 1)) M1]
  (γ1 : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 (n + 1)
    I.C1 →ₐ[I.B (n + 1)] M1 ⧸ EtaleNil.JB (J θ (R := I.B (n + 1))) M1)
  (hM1 : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 (n + 1)
    letI := γ1.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B (n + 1)) I.C1 (algebraMap I.B0 (I.B (n + 1)) g))
      (M1 ⧸ EtaleNil.JB (J θ (R := I.B (n + 1))) M1))
  (s : M1 →+* M0)
  (hs : ∀ x : I.B (n + 1), s (algebraMap (I.B (n + 1)) M1 x) =
    algebraMap (I.B n) M0 (algebraMap (I.B (n + 1)) (I.B n) x))
  (hγ : ∀ (c : I.C1) (m : M1),
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B (n + 1))) M1) m = γ1 c →
      Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) M0) (s m) = γ0 c)

include hs hγ in
/-- **The étale lifts to `P n[1/g]` commute with the successor maps.** -/
theorem φPn_succ (m : M1) : I.φPn n g hfg0 γ0 hM0 (s m) =
    I.ρPg n g (I.φPn (n + 1) g hfg1 γ1 hM1 m) := by
  letI := algBP I.T I.B (n + 1)
  letI := algBP I.T I.B n
  letI : Algebra (I.B (n + 1)) (I.Pg n g) :=
    ((algebraMap (I.B n) (I.Pg n g)).comp (algebraMap (I.B (n + 1)) (I.B n))).toAlgebra
  let φ : M1 →ₐ[I.B (n + 1)] I.Pg n g :=
    { toRingHom := (I.φPn n g hfg0 γ0 hM0 : M0 →+* I.Pg n g).comp s
      commutes' := fun r ↦ by
        change I.φPn n g hfg0 γ0 hM0 (s (algebraMap _ _ r)) = _
        rw [hs, AlgHom.commutes]
        rfl }
  let ψ : M1 →ₐ[I.B (n + 1)] I.Pg n g :=
    { toRingHom := (I.ρPg n g).comp (I.φPn (n + 1) g hfg1 γ1 hM1 : M1 →+* I.Pg (n + 1) g)
      commutes' := fun r ↦ by
        change I.ρPg n g (I.φPn (n + 1) g hfg1 γ1 hM1 (algebraMap _ _ r)) = _
        rw [AlgHom.commutes, ρPg_algebraMapB]
        rfl }
  have key : φ = ψ := by
    letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 (n + 1)
    refine EtaleNil.ext_of_comp (J θ (R := I.B (n + 1))) (I.hJB (n + 1)) γ1 _ hM1 fun c ↦ ?_
    obtain ⟨m, hm⟩ := Ideal.Quotient.mk_surjective (γ1 c)
    rw [← hm, EtaleNil.red_mk, EtaleNil.red_mk, Ideal.Quotient.eq, J_succ I.B n,
      ← Ideal.Quotient.eq]
    change Ideal.Quotient.mk _ (I.φPn n g hfg0 γ0 hM0 (s m)) =
      Ideal.Quotient.mk _ (I.ρPg n g (I.φPn (n + 1) g hfg1 γ1 hM1 m))
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ((I.T.level (n + 1)).σP.symm
      (algebraMap (Cc I.T (n + 1)) _ (I.ι₀ c)))
    have hp' : (I.T.level (n + 1)).σP (Ideal.Quotient.mk _ p) =
        algebraMap (Cc I.T (n + 1)) _ (I.ι₀ c) := by
      rw [hp, AlgEquiv.apply_symm_apply]
    have h1 : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B (n + 1))) (I.Pg (n + 1) g))
        (I.φPn (n + 1) g hfg1 γ1 hM1 m) =
          Ideal.Quotient.mk _ (algebraMap (I.T.level (n + 1)).P (I.Pg (n + 1) g) p) := by
      rw [← EtaleNil.red_mk (J θ (R := I.B (n + 1))) (I.φPn (n + 1) g hfg1 γ1 hM1) m, hm,
        red_φPn, γPn_eq _ _ _ _ p hp']
    rw [I.ρPg_mk n g h1, ρPg_algebraMap,
      ← EtaleNil.red_mk (J θ (R := I.B n)) (I.φPn n g hfg0 γ0 hM0) (s m), hγ c m hm, red_φPn,
      γPn_eq _ _ _ _ (I.T.ρP n p) (I.σP_ρP_ι n c p hp')]
  exact AlgHom.congr_fun key m

include hs hγ in
/-- **The étale lifts to `E n[1/g]` commute with the successor maps.** -/
theorem φEn_succ (m : M1) : I.φEn n g γ0 hM0 (s m) =
    I.sEg n g (I.φEn (n + 1) g γ1 hM1 m) := by
  letI := alg0 I.B I.B0 (n + 1) (I.E (n + 1))
  letI := alg0 I.B I.B0 n (I.E n)
  letI : Algebra (I.B (n + 1)) (ZariskiTwo.Lc g (I.E n)) :=
    ((algebraMap (I.B n) (ZariskiTwo.Lc g (I.E n))).comp
      (algebraMap (I.B (n + 1)) (I.B n))).toAlgebra
  let φ : M1 →ₐ[I.B (n + 1)] ZariskiTwo.Lc g (I.E n) :=
    { toRingHom := (I.φEn n g γ0 hM0 : M0 →+* ZariskiTwo.Lc g (I.E n)).comp s
      commutes' := fun r ↦ by
        change I.φEn n g γ0 hM0 (s (algebraMap _ _ r)) = _
        rw [hs, AlgHom.commutes]
        rfl }
  let ψ : M1 →ₐ[I.B (n + 1)] ZariskiTwo.Lc g (I.E n) :=
    { toRingHom := (I.sEg n g).comp
        (I.φEn (n + 1) g γ1 hM1 : M1 →+* ZariskiTwo.Lc g (I.E (n + 1)))
      commutes' := fun r ↦ by
        change I.sEg n g (I.φEn (n + 1) g γ1 hM1 (algebraMap _ _ r)) = _
        rw [AlgHom.commutes, sEg_algebraMapB]
        rfl }
  have key : φ = ψ := by
    letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 (n + 1)
    refine EtaleNil.ext_of_comp (J θ (R := I.B (n + 1))) (I.hJB (n + 1)) γ1 _ hM1 fun c ↦ ?_
    obtain ⟨m, hm⟩ := Ideal.Quotient.mk_surjective (γ1 c)
    rw [← hm, EtaleNil.red_mk, EtaleNil.red_mk, Ideal.Quotient.eq, J_succ I.B n,
      ← Ideal.Quotient.eq]
    change Ideal.Quotient.mk _ (I.φEn n g γ0 hM0 (s m)) =
      Ideal.Quotient.mk _ (I.sEg n g (I.φEn (n + 1) g γ1 hM1 m))
    obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective ((I.σE (n + 1)).symm
      (algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) c))
    have he' : I.σE (n + 1) (Ideal.Quotient.mk _ e) =
        algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) c := by
      rw [he, AlgEquiv.apply_symm_apply]
    have h1 : Ideal.Quotient.mk
        (EtaleNil.JB (J θ (R := I.B (n + 1))) (ZariskiTwo.Lc g (I.E (n + 1))))
        (I.φEn (n + 1) g γ1 hM1 m) = Ideal.Quotient.mk _
          (algebraMap (I.E (n + 1)) (ZariskiTwo.Lc g (I.E (n + 1))) e) := by
      rw [← EtaleNil.red_mk (J θ (R := I.B (n + 1))) (I.φEn (n + 1) g γ1 hM1) m, hm,
        red_φEn, γEn_eq _ _ _ _ e he']
    rw [I.sEg_mk n g h1, sEg_algebraMap,
      ← EtaleNil.red_mk (J θ (R := I.B n)) (I.φEn n g γ0 hM0) (s m), hγ c m hm, red_φEn,
      γEn_eq _ _ _ _ (I.sE n e) (by rw [I.hσE, he'])]
  exact AlgHom.congr_fun key m

include hO in
lemma eGn_trg (x : I.LcG hθ g (n + 1)) : I.eGn hθ hO n g hfg0 (I.trg hθ hO n g x) =
    I.ρPg n g (I.eGn hθ hO (n + 1) g hfg1 x) := by
  have h : (I.eGn hθ hO n g hfg0).toRingHom.comp (I.trg hθ hO n g) =
      (I.ρPg n g).comp (I.eGn hθ hO (n + 1) g hfg1).toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers
      (@algebraMap I.B0 (I.T.G hθ (n + 1)) _ _ (alg0G I.T hθ I.B I.B0 (n + 1)) g))
      (RingHom.ext fun y ↦ ?_)
    change I.eGn hθ hO n g hfg0 (I.trg hθ hO n g (algebraMap _ _ y)) =
      I.ρPg n g (I.eGn hθ hO (n + 1) g hfg1 (algebraMap _ _ y))
    rw [trg_algebraMap, eGn_algebraMap, eGn_algebraMap, ρPg_algebraMap,
      LevelTower.Data.tr_fst_eq]
  exact RingHom.congr_fun h x

include hO hs hγ in
lemma φa_succ (m : M1) : (I.eGn hθ hO n g hfg0).symm (I.φPn n g hfg0 γ0 hM0 (s m)) =
    I.trg hθ hO n g ((I.eGn hθ hO (n + 1) g hfg1).symm (I.φPn (n + 1) g hfg1 γ1 hM1 m)) := by
  rw [RingEquiv.symm_apply_eq, I.eGn_trg hθ hO n g hfg0 hfg1, RingEquiv.apply_symm_apply,
    I.φPn_succ n g hfg0 hfg1 γ0 hM0 γ1 hM1 s hs hγ]

variable [Algebra I.B0 M0] [IsScalarTower I.B0 (I.B n) M0] [Algebra I.B0 M1]
  [IsScalarTower I.B0 (I.B (n + 1)) M1]

include hs hγ in
/-- **The maps `ψ : Y n → M` commute with the successor maps**: `s ∘ ψ (n+1) = ψ n ∘ Ymap n`. -/
theorem ψ_succ (y : I.Y hθ (n + 1)) :
    s (I.ψ hθ hO (n + 1) g hfg1 γ1 hM1 y) = I.ψ hθ hO n g hfg0 γ0 hM0 (I.Ymap hθ hO n y) := by
  have h1 : I.glueM hθ hO (n + 1) g hfg1 γ1 hM1 (I.ψ hθ hO (n + 1) g hfg1 γ1 hM1 y) =
      I.mapYg hθ (n + 1) g y :=
    (I.glueM hθ hO (n + 1) g hfg1 γ1 hM1).apply_symm_apply _
  apply (I.glueM hθ hO n g hfg0 γ0 hM0).injective
  change _ = I.glueM hθ hO n g hfg0 γ0 hM0
    ((I.glueM hθ hO n g hfg0 γ0 hM0).symm (I.mapYg hθ n g (I.Ymap hθ hO n y)))
  rw [AlgEquiv.apply_symm_apply]
  refine I.Yg_ext hθ n g ?_ ?_
  · have h := congrArg (I.fstYg hθ (n + 1) g) h1
    rw [fstYg_glueM, fstYg_mapYg] at h
    rw [fstYg_glueM, fstYg_mapYg, I.φa_succ hθ hO n g hfg0 hfg1 γ0 hM0 γ1 hM1 s hs hγ, h]
    exact I.trg_algebraMap hθ hO n g _
  · have h := congrArg (I.sndYg hθ (n + 1) g) h1
    rw [sndYg_glueM, sndYg_mapYg] at h
    rw [sndYg_glueM, sndYg_mapYg, I.φEn_succ n g γ0 hM0 γ1 hM1 s hs hγ, h]
    exact I.sEg_algebraMap n g _

end Succ

end Input

end NodeEtaleGlue

end

end SemistableReduction
