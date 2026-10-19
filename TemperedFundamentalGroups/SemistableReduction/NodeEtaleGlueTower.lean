/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlue
import TemperedFundamentalGroups.SemistableReduction.LevelTowerFst

/-!
# The tower of glued coverings over the base charts (Blueprint §12.8, M2.3 (f), tower)

In the setting of `NodeEtaleGlue`, with maps of base charts `B (n+1) → B n` and successor maps
`sE n : E (n+1) → E n` of the étale pieces compatible with the identifications `σE`:

* `NodeEtaleGlue.sab n : E (n+1)[1/a] → E n[1/a]` (the overlaps);
* **`NodeEtaleGlue.ρa_tr`**: the overlap maps commute with the transition maps of the node
  patches, `ρa n ∘ tr n = sab n ∘ ρa (n+1)` (both sides are maps out of the formally étale
  `P (n+1)` after `tr_fst_eq`, equal modulo `J` by the compatibility of `χ̄` with `Tmap`,
  `EtaleNil.ext`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (T : Data (θ := θ) R cov₀ πL) (hθ : Function.Surjective θ)
  (B : ℕ → Type u) [∀ n, CommRing (B n)]
  [∀ n, Algebra (B n) (R n)] (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  [∀ n, Algebra O (B n)] [∀ n, IsScalarTower O (B n) (R n)]
  {Bs : Type u} [CommRing Bs] (qB : ∀ n, B n →+* Bs) (φs : Bs →+* R₀)
  (hφs : ∀ n (x : B n), T.e n (φs (qB n x)) = Ideal.Quotient.mk _ (algebraMap (B n) (R n) x))
  {C1 : Type u} [CommRing C1] [Algebra Bs C1] (ι₀ : C1 →+* cov₀.C)
  (hι₀ : ∀ x : Bs, ι₀ (algebraMap Bs C1 x) = algebraMap R₀ cov₀.C (φs x))
  (a b : ∀ n, B n) [∀ n, IsLocalization.Away (a n) (R n)] {abar : Bs}
  (ha : ∀ n, qB n (a n) = abar)
  (hι : letI := ι₀.toAlgebra; IsLocalization.Away (algebraMap Bs C1 abar) cov₀.C)
  (E : ℕ → Type u) [∀ n, CommRing (E n)] [∀ n, Algebra (B n) (E n)]
  [∀ n, Algebra.FormallyEtale (B n) (E n)]
  {bbar : Bs} (σE : ∀ n, letI := algC1 B qB C1 n
    (E n ⧸ EtaleNil.JB (J θ (R := B n)) (E n)) ≃ₐ[B n] Localization.Away (algebraMap Bs C1 bbar))
  (hbE : ∀ n, IsUnit (algebraMap (B n) (E n) (b n)))
  {kdiv : ℕ → ℕ} (hdiv : ∀ n, T.f n ∣ algebraMap (B n) (R n) (b n) ^ kdiv n)
  (hbb : ∀ n, qB n (b n) = bbar)
  {mB : ℕ → ℕ} (hJB : ∀ n, J θ (R := B n) ^ mB n = ⊥)

/-! ### Maps between consecutive levels -/

variable [∀ n, Algebra (B (n + 1)) (B n)] [∀ n, IsScalarTower O (B (n + 1)) (B n)]
  (hBR : ∀ n (x : B (n + 1)), algebraMap (R (n + 1)) (R n) (algebraMap (B (n + 1)) (R (n + 1)) x) =
    algebraMap (B n) (R n) (algebraMap (B (n + 1)) (B n) x))
  (hqB : ∀ n (x : B (n + 1)), qB n (algebraMap (B (n + 1)) (B n) x) = qB (n + 1) x)
  (haS : ∀ n, algebraMap (B (n + 1)) (B n) (a (n + 1)) = a n)
  (sE : ∀ n, E (n + 1) →+* E n)
  (hsE : ∀ n (x : B (n + 1)), sE n (algebraMap (B (n + 1)) (E (n + 1)) x) =
    algebraMap (B n) (E n) (algebraMap (B (n + 1)) (B n) x))
  (hσE : ∀ n (x : E (n + 1)), σE n (Ideal.Quotient.mk _ (sE n x)) =
    σE (n + 1) (Ideal.Quotient.mk _ x))

omit [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] in
include hsE haS in
lemma isUnit_sab (n : ℕ) : IsUnit ((algebraMap (E n) (EtaleOverlap.Bab (a n) (E n))).comp (sE n)
    (algebraMap (B (n + 1)) (E (n + 1)) (a (n + 1)))) := by
  rw [RingHom.comp_apply, hsE, haS]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- **The map of overlaps** `E (n+1)[1/a] → E n[1/a]`. -/
def sab (n : ℕ) : EtaleOverlap.Bab (a (n + 1)) (E (n + 1)) →+* EtaleOverlap.Bab (a n) (E n) :=
  IsLocalization.Away.lift (algebraMap (B (n + 1)) (E (n + 1)) (a (n + 1)))
    (isUnit_sab B a E haS sE hsE n)

omit [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] in
lemma sab_algebraMap (n : ℕ) (y : E (n + 1)) :
    sab B a E haS sE hsE n (algebraMap _ _ y) = algebraMap _ _ (sE n y) :=
  IsLocalization.Away.lift_eq _ _ y

omit [∀ n, IsScalarTower O (B n) (R n)] in
lemma J_le (n : ℕ) :
    (J θ (R := B (n + 1))).map (algebraMap (B (n + 1)) (B n)) ≤ J θ (R := B n) := by
  rw [J, J, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The ideal `J` of the overlap at level `n`. -/
abbrev JZ (n : ℕ) : Ideal (EtaleOverlap.Bab (a n) (E n)) :=
  EtaleNil.JB (J θ (R := B n)) (EtaleOverlap.Bab (a n) (E n))

omit [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] [∀ n, IsScalarTower O (B n) (R n)] in
lemma JZ_le (n : ℕ) : JZ (θ := θ) B a E (n + 1) ≤
    (JZ (θ := θ) B a E n).comap (sab B a E haS sE hsE n) := by
  rw [JZ, EtaleNil.JB, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro x hx
  rw [Ideal.mem_comap, RingHom.comp_apply,
    IsScalarTower.algebraMap_apply (B (n + 1)) (E (n + 1))
      (EtaleOverlap.Bab (a (n + 1)) (E (n + 1))),
    sab_algebraMap, hsE, ← IsScalarTower.algebraMap_apply]
  exact Ideal.mem_map_of_mem _ (J_le B n (Ideal.mem_map_of_mem _ hx))

/-- `Bab (n+1)/J → Bab n/J`. -/
def sabZ (n : ℕ) : OverlapFibre.Z (J θ (R := B (n + 1))) (a (n + 1)) (E (n + 1)) →+*
    OverlapFibre.Z (J θ (R := B n)) (a n) (E n) :=
  Ideal.quotientMap _ (sab B a E haS sE hsE n) (JZ_le B a E haS sE hsE n)

/-- `γ1` at level `n`. -/
abbrev γ1n (n : ℕ) : C1 →+* OverlapFibre.Z (J θ (R := B n)) (a n) (E n) :=
  letI := algC1 B qB C1 n
  (OverlapFibre.γ1 (J θ (R := B n)) (a n) C1 (σE n) : C1 →+* _)

omit [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] in
include hσE in
lemma γ1_succ (n : ℕ) (c : C1) :
    γ1n B qB a E σE n c = sabZ B a E haS sE hsE n (γ1n B qB a E σE (n + 1) c) := by
  letI := algC1 B qB C1 n
  letI := algC1 B qB C1 (n + 1)
  obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective
    ((σE (n + 1)).symm (algebraMap C1 (Localization.Away (algebraMap Bs C1 bbar)) c))
  have h1 : (σE n).symm (algebraMap C1 (Localization.Away (algebraMap Bs C1 bbar)) c) =
      Ideal.Quotient.mk _ (sE n e) := by
    apply (σE n).injective
    rw [AlgEquiv.apply_symm_apply, hσE, he, AlgEquiv.apply_symm_apply]
  change OverlapFibre.redE _ (a n) ((σE n).symm (algebraMap C1 _ c)) =
    sabZ B a E haS sE hsE n
      (OverlapFibre.redE _ (a (n + 1)) ((σE (n + 1)).symm (algebraMap C1 _ c)))
  rw [h1, ← he, EtaleNil.red_mk, EtaleNil.red_mk]
  change _ = Ideal.Quotient.mk _ (sab B a E haS sE hsE n (algebraMap _ _ e))
  rw [sab_algebraMap]
  rfl

/-- `γc` at level `n`. -/
abbrev γcn (n : ℕ) : cov₀.C →+* OverlapFibre.Z (J θ (R := B n)) (a n) (E n) :=
  letI := algBC T B n
  letI := algC1 B qB C1 n
  (OverlapFibre.γc (J θ (R := B n)) (a n) (ιn T B qB φs hφs ι₀ hι₀ n) (σE n)
    (isLocalization_ιn T B qB φs hφs ι₀ hι₀ a ha hι n) : Cc T n →+* _)

omit [∀ (n : ℕ), IsNoetherianRing (R n)] [∀ (n : ℕ), IsScalarTower O (R (n + 1)) (R n)]
  [∀ (n : ℕ), IsScalarTower O (B n) (R n)] [∀ (n : ℕ), IsLocalization.Away (a n) (R n)]
  [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] in
include hσE in
lemma γc_succ (n : ℕ) (c : cov₀.C) :
    γcn T B qB φs hφs ι₀ hι₀ a ha hι E σE n c =
      sabZ B a E haS sE hsE n (γcn T B qB φs hφs ι₀ hι₀ a ha hι E σE (n + 1) c) := by
  letI := ι₀.toAlgebra
  haveI := hι
  have h : γcn T B qB φs hφs ι₀ hι₀ a ha hι E σE n =
      (sabZ B a E haS sE hsE n).comp (γcn T B qB φs hφs ι₀ hι₀ a ha hι E σE (n + 1)) :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap Bs C1 abar)) (RingHom.ext fun c ↦ by
      letI := algBC T B n
      letI := algC1 B qB C1 n
      letI := algBC T B (n + 1)
      letI := algC1 B qB C1 (n + 1)
      change OverlapFibre.γc _ _ _ _ _ (ιn T B qB φs hφs ι₀ hι₀ n c) =
        sabZ B a E haS sE hsE n (OverlapFibre.γc _ _ _ _ _ (ιn T B qB φs hφs ι₀ hι₀ (n + 1) c))
      rw [OverlapFibre.γc_ι, OverlapFibre.γc_ι]
      exact γ1_succ B qB a E σE haS sE hsE hσE n c)
  exact RingHom.congr_fun h c

/-- `μ` at level `n`. -/
abbrev μn (n : ℕ) : Localization.Away (algebraMap (R n) (Cc T n) (T.f n)) →+*
    OverlapFibre.Z (J θ (R := B n)) (a n) (E n) :=
  letI := algBC T B n
  haveI := towerBC T B n
  letI := algC1 B qB C1 n
  OverlapFibre.μ (J θ (R := B n)) (a n) (b n) (ιn T B qB φs hφs ι₀ hι₀ n) (T.f n) (σE n)
    (isLocalization_ιn T B qB φs hφs ι₀ hι₀ a ha hι n) (hbE n) (hdiv n)

omit [∀ (n : ℕ), IsNoetherianRing (R n)] [∀ (n : ℕ), IsScalarTower O (R (n + 1)) (R n)]
  [∀ (n : ℕ), IsScalarTower O (B n) (R n)] [∀ (n : ℕ), IsLocalization.Away (a n) (R n)]
  [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] in
include hσE in
lemma μ_succ (n : ℕ) (y : Localization.Away (algebraMap (R (n + 1)) (Cc T (n + 1)) (T.f (n + 1)))) :
    μn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv n
      (LevelStep.Tmap (T.f (n + 1)) (T.f n) (T.hf n) (T.hfe (n + 1)) (T.hfe n) (T.he n) cov₀ y) =
      sabZ B a E haS sE hsE n (μn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv (n + 1) y) := by
  have h : (μn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv n).comp
      (LevelStep.Tmap (T.f (n + 1)) (T.f n) (T.hf n) (T.hfe (n + 1)) (T.hfe n) (T.he n) cov₀) =
      (sabZ B a E haS sE hsE n).comp (μn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv (n + 1)) :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap (R (n + 1)) (Cc T (n + 1))
      (T.f (n + 1)))) (RingHom.ext fun c ↦ by
      letI := algBC T B n
      haveI := towerBC T B n
      letI := algC1 B qB C1 n
      letI := algBC T B (n + 1)
      haveI := towerBC T B (n + 1)
      letI := algC1 B qB C1 (n + 1)
      simp only [RingHom.comp_apply]
      rw [LevelStep.Tmap_algebraMap, OverlapFibre.μ_algebraMap, OverlapFibre.μ_algebraMap]
      exact γc_succ T B qB φs hφs ι₀ hι₀ a ha hι E σE haS sE hsE hσE n c)
  exact RingHom.congr_fun h y

/-- `κ` at level `n`: the lift `P n → E n[1/a]` of `χ̄ n` (`EtaleOverlap.κ`). -/
abbrev κn (n : ℕ) : (T.level n).P →+* EtaleOverlap.Bab (a n) (E n) :=
  letI := algBP T B n
  haveI := towerBP T B n
  (EtaleOverlap.κ (J θ (R := B n)) (hJB n) (a n) (R n)
    (χn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv n) : (T.level n).P →+* _)

omit [(n : ℕ) → Algebra (B (n + 1)) (B n)] [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)]
  [∀ (n : ℕ), IsScalarTower O (B (n + 1)) (B n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
lemma mk_κn (n : ℕ) (p : (T.level n).P) :
    Ideal.Quotient.mk (JZ (θ := θ) B a E n)
        (κn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB n p) =
      μn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv n
        ((T.level n).σP (Ideal.Quotient.mk _ p)) := by
  letI := algBP T B n
  haveI := towerBP T B n
  haveI := EtaleOverlap.formallyEtale_P (a n) (R n) (P := (T.level n).P)
  exact EtaleNil.mk_lift (J θ (R := B n)) (hJB n) _ p

omit [∀ n, IsScalarTower O (B n) (R n)] in
lemma J_succ (n : ℕ) (X : Type u) [CommRing X] [Algebra (B n) X] :
    letI : Algebra (B (n + 1)) X :=
      ((algebraMap (B n) X).comp (algebraMap (B (n + 1)) (B n))).toAlgebra
    EtaleNil.JB (J θ (R := B (n + 1))) X = EtaleNil.JB (J θ (R := B n)) X := by
  letI : Algebra (B (n + 1)) X :=
    ((algebraMap (B n) X).comp (algebraMap (B (n + 1)) (B n))).toAlgebra
  rw [EtaleNil.JB, EtaleNil.JB, J, J, Ideal.map_map, Ideal.map_map]
  congr 1
  ext o
  change algebraMap (B n) X (algebraMap (B (n + 1)) (B n) (algebraMap O (B (n + 1)) o)) = _
  rw [← IsScalarTower.algebraMap_apply O (B (n + 1)) (B n)]
  rfl

omit [∀ (n : ℕ), IsScalarTower O (R (n + 1)) (R n)]
  [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] in
include hσE hBR in
/-- **The lifts `κ` commute with the successor maps**: `κ n ∘ ρP n = sab n ∘ κ (n+1)`. -/
theorem κ_succ (n : ℕ) (p : (T.level (n + 1)).P) :
    κn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB n (T.ρP n p) =
      sab B a E haS sE hsE n (κn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB (n + 1) p) := by
  letI := algBP T B (n + 1)
  haveI := towerBP T B (n + 1)
  letI := algBP T B n
  haveI := towerBP T B n
  letI := algP T.level n
  haveI := EtaleOverlap.formallyEtale_P (a (n + 1)) (R (n + 1)) (P := (T.level (n + 1)).P)
  letI : Algebra (B (n + 1)) (EtaleOverlap.Bab (a n) (E n)) :=
    ((algebraMap (B n) (EtaleOverlap.Bab (a n) (E n))).comp
      (algebraMap (B (n + 1)) (B n))).toAlgebra
  set κ0 := κn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB n
  set κ1 := κn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB (n + 1)
  set s := sab B a E haS sE hsE n
  have hκ0 : ∀ y : B n, κ0 (algebraMap (B n) (T.level n).P y) =
      algebraMap (B n) (EtaleOverlap.Bab (a n) (E n)) y := fun y ↦ by
    exact (EtaleOverlap.κ (J θ (R := B n)) (hJB n) (a n) (R n)
      (χn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv n)).commutes y
  have hκ1 : ∀ y : B (n + 1), κ1 (algebraMap (B (n + 1)) (T.level (n + 1)).P y) =
      algebraMap (B (n + 1)) (EtaleOverlap.Bab (a (n + 1)) (E (n + 1))) y := fun y ↦
    (EtaleOverlap.κ (J θ (R := B (n + 1))) (hJB (n + 1)) (a (n + 1)) (R (n + 1))
      (χn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv (n + 1))).commutes y
  let φ : (T.level (n + 1)).P →ₐ[B (n + 1)] EtaleOverlap.Bab (a n) (E n) :=
    { toRingHom := κ0.comp (T.ρP n).toRingHom
      commutes' := fun r ↦ by
        change κ0 (T.ρP n (algebraMap (R (n + 1)) _ (algebraMap (B (n + 1)) (R (n + 1)) r))) = _
        rw [AlgHom.commutes]
        change κ0 (algebraMap (R n) _ (algebraMap (R (n + 1)) (R n)
          (algebraMap (B (n + 1)) (R (n + 1)) r))) = _
        rw [hBR]
        exact hκ0 _ }
  let ψ : (T.level (n + 1)).P →ₐ[B (n + 1)] EtaleOverlap.Bab (a n) (E n) :=
    { toRingHom := s.comp κ1
      commutes' := fun r ↦ by
        change s (κ1 (algebraMap (B (n + 1)) _ r)) = _
        rw [hκ1, IsScalarTower.algebraMap_apply (B (n + 1)) (E (n + 1))
          (EtaleOverlap.Bab (a (n + 1)) (E (n + 1))), sab_algebraMap, hsE,
          ← IsScalarTower.algebraMap_apply]
        rfl }
  have key : φ = ψ := EtaleNil.ext (J θ (R := B (n + 1))) (hJB (n + 1)) fun p ↦ by
    rw [Ideal.Quotient.eq, J_succ B n, ← Ideal.Quotient.eq]
    change Ideal.Quotient.mk (JZ (θ := θ) B a E n) (κ0 (T.ρP n p)) =
      Ideal.Quotient.mk (JZ (θ := θ) B a E n) (s (κ1 p))
    rw [mk_κn, LevelTower.Data.σP_ρP, μ_succ T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv haS sE hsE
      hσE n]
    change _ = sabZ B a E haS sE hsE n (Ideal.Quotient.mk _ (κ1 p))
    rw [mk_κn]
  exact AlgHom.congr_fun key p

omit [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] in
include hσE hBR in
/-- **The overlap maps commute with the transition maps**: `ρa n ∘ tr n = sab n ∘ ρa (n+1)`. -/
theorem ρa_tr (n : ℕ) (x : T.G hθ (n + 1)) :
    ρa T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB n (T.tr hθ hO n x) =
      sab B a E haS sE hsE n
        (ρa T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB (n + 1) x) := by
  change κn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB n (T.tr hθ hO n x).1.1 =
    sab B a E haS sE hsE n (κn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB (n + 1) x.1.1)
  rw [LevelTower.Data.tr_fst_eq]
  exact κ_succ T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB hBR haS sE hsE hσE n x.1.1

/-! ### The glued coverings over a common base

All levels are algebras over one base `B0` (Tate case: the chart `T1`), with `a n`, `b n` the
images of `a0, b0 ∈ B0`. -/

variable (B0 : Type u) [CommRing B0] [∀ n, Algebra B0 (B n)]
  [∀ n, IsScalarTower B0 (B (n + 1)) (B n)] {a0 b0 : B0}
  (haB : ∀ n, algebraMap B0 (B n) a0 = a n) (hbB : ∀ n, algebraMap B0 (B n) b0 = b n)

/-- `X` over `B0` through a `B n`-algebra structure. -/
@[reducible] def alg0 (n : ℕ) (X : Type u) [CommRing X] [Algebra (B n) X] : Algebra B0 X :=
  ((algebraMap (B n) X).comp (algebraMap B0 (B n))).toAlgebra

/-- `G n` over `B0`. -/
@[reducible] def alg0G (n : ℕ) : Algebra B0 (T.G hθ n) :=
  letI := algBG T hθ B n
  alg0 B B0 n (T.G hθ n)

/-- **The overlap map over `B0`.** -/
def ρa0 (n : ℕ) : letI := alg0G T hθ B B0 n
    letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
    T.G hθ n →ₐ[B0] EtaleOverlap.Bab (a n) (E n) :=
  letI := alg0G T hθ B B0 n
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  letI := algBG T hθ B n
  { (ρa T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB n : T.G hθ n →+* _) with
    commutes' := fun _ ↦ (ρa T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB n).commutes _ }

/-- The localization map `E n → E n[1/a]` over `B0`. -/
def ρb0 (n : ℕ) : letI := alg0 B B0 n (E n)
    letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
    E n →ₐ[B0] EtaleOverlap.Bab (a n) (E n) :=
  letI := alg0 B B0 n (E n)
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  { algebraMap (E n) (EtaleOverlap.Bab (a n) (E n)) with
    commutes' := fun _ ↦ (IsScalarTower.algebraMap_apply (B n) (E n) _ _).symm }

/-- **The covering over the base chart at level `n`** (over `B0`):
`Y n = G n ×_{E n[1/a]} E n`. -/
def Y0 (n : ℕ) : Type u :=
  letI := alg0G T hθ B B0 n
  letI := alg0 B B0 n (E n)
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  ZariskiTwo.glued (ρa0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n)
    (ρb0 B a E B0 n)

instance (n : ℕ) : CommRing (Y0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n) :=
  letI := alg0G T hθ B B0 n
  letI := alg0 B B0 n (E n)
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  (ZariskiTwo.glued (ρa0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n)
    (ρb0 B a E B0 n)).toCommRing

instance (n : ℕ) : Algebra B0 (Y0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n) :=
  letI := alg0G T hθ B B0 n
  letI := alg0 B B0 n (E n)
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  (ZariskiTwo.glued (ρa0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n)
    (ρb0 B a E B0 n)).algebra

/-! ### The successor maps over `B0` -/

omit [(n : ℕ) → Algebra O (B n)] [∀ (n : ℕ), IsScalarTower O (B n) (R n)]
  [∀ (n : ℕ), IsScalarTower O (B (n + 1)) (B n)] in
include hBR in
lemma tr_algebraMap0 (n : ℕ) (y : B0) :
    T.tr hθ hO n (letI := alg0G T hθ B B0 (n + 1); algebraMap B0 (T.G hθ (n + 1)) y) =
      (letI := alg0G T hθ B B0 n; algebraMap B0 (T.G hθ n) y) := by
  change T.tr hθ hO n (algebraMap (R (n + 1)) _ (algebraMap (B (n + 1)) (R (n + 1))
    (algebraMap B0 (B (n + 1)) y))) = algebraMap (R n) _ (algebraMap (B n) (R n)
      (algebraMap B0 (B n) y))
  rw [LevelTower.Data.tr_algebraMap, hBR, ← IsScalarTower.algebraMap_apply B0 (B (n + 1)) (B n)]

/-- The transition map of the node patches over `B0`. -/
def sa0 (n : ℕ) : letI := alg0G T hθ B B0 (n + 1); letI := alg0G T hθ B B0 n
    T.G hθ (n + 1) →ₐ[B0] T.G hθ n :=
  letI := alg0G T hθ B B0 (n + 1)
  letI := alg0G T hθ B B0 n
  { T.tr hθ hO n with commutes' := tr_algebraMap0 T hθ B hO hBR B0 n }

/-- The successor map of the étale pieces over `B0`. -/
def sb0 (n : ℕ) : letI := alg0 B B0 (n + 1) (E (n + 1)); letI := alg0 B B0 n (E n)
    E (n + 1) →ₐ[B0] E n :=
  letI := alg0 B B0 (n + 1) (E (n + 1))
  letI := alg0 B B0 n (E n)
  { sE n with
    commutes' := fun y ↦ by
      change sE n (algebraMap (B (n + 1)) _ (algebraMap B0 (B (n + 1)) y)) = _
      rw [hsE, ← IsScalarTower.algebraMap_apply B0 (B (n + 1)) (B n)]
      rfl }

/-- The map of overlaps over `B0`. -/
def sab0 (n : ℕ) : letI := alg0 B B0 (n + 1) (EtaleOverlap.Bab (a (n + 1)) (E (n + 1)))
    letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
    EtaleOverlap.Bab (a (n + 1)) (E (n + 1)) →ₐ[B0] EtaleOverlap.Bab (a n) (E n) :=
  letI := alg0 B B0 (n + 1) (EtaleOverlap.Bab (a (n + 1)) (E (n + 1)))
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  { sab B a E haS sE hsE n with
    commutes' := fun y ↦ by
      change sab B a E haS sE hsE n (algebraMap (B (n + 1)) _ (algebraMap B0 (B (n + 1)) y)) = _
      rw [IsScalarTower.algebraMap_apply (B (n + 1)) (E (n + 1))
        (EtaleOverlap.Bab (a (n + 1)) (E (n + 1))), sab_algebraMap, hsE,
        ← IsScalarTower.algebraMap_apply B0 (B (n + 1)) (B n),
        ← IsScalarTower.algebraMap_apply (B n) (E n)]
      rfl }

omit [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] in
include hBR hσE in
lemma hsa0 (n : ℕ) (x : T.G hθ (n + 1)) :
    ρa0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n (sa0 T hθ B hO hBR B0 n x) =
      sab0 B a E haS sE hsE B0 n
        (ρa0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 (n + 1) x) := by
  change ρa T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB n (T.tr hθ hO n x) =
    sab B a E haS sE hsE n (ρa T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB (n + 1) x)
  exact ρa_tr T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB hBR haS sE hsE hσE n x

omit [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] in
lemma hsb0 (n : ℕ) (x : E (n + 1)) :
    ρb0 B a E B0 n (sb0 B E sE hsE B0 n x) =
      sab0 B a E haS sE hsE B0 n (ρb0 B a E B0 (n + 1) x) := by
  change algebraMap (E n) _ (sE n x) = sab B a E haS sE hsE n (algebraMap _ _ x)
  exact (sab_algebraMap B a E haS sE hsE n x).symm

/-- **The successor map of the glued coverings** `Y (n+1) → Y n` (`ZariskiTwo.map`). -/
def Ymap (n : ℕ) : Y0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 (n + 1) →ₐ[B0]
    Y0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n :=
  letI := alg0G T hθ B B0 (n + 1)
  letI := alg0 B B0 (n + 1) (E (n + 1))
  letI := alg0 B B0 (n + 1) (EtaleOverlap.Bab (a (n + 1)) (E (n + 1)))
  letI := alg0G T hθ B B0 n
  letI := alg0 B B0 n (E n)
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  ZariskiTwo.map (sa0 T hθ B hO hBR B0 n) (sb0 B E sE hsE B0 n) (sab0 B a E haS sE hsE B0 n)
    (hsa0 T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB hBR haS sE hsE hσE B0 n)
    (hsb0 B a E haS sE hsE B0 n)

/-! ### Surjectivity and kernels of the successor maps -/

omit [∀ (n : ℕ), IsScalarTower O (R (n + 1)) (R n)] [∀ (n : ℕ), IsScalarTower O (B n) (R n)]
  [∀ (n : ℕ), IsScalarTower O (B (n + 1)) (B n)] [∀ (n : ℕ), IsScalarTower B0 (B (n + 1)) (B n)]
  [(n : ℕ) → Algebra O (B n)] [(n : ℕ) → Algebra (B (n + 1)) (B n)] in
include haB in
lemma isUnit_a0 (n : ℕ) : IsUnit (letI := alg0G T hθ B B0 n; algebraMap B0 (T.G hθ n) a0) := by
  change IsUnit (algebraMap (R n) (T.G hθ n) (algebraMap (B n) (R n) (algebraMap B0 (B n) a0)))
  rw [haB]
  exact (IsLocalization.Away.algebraMap_isUnit (a n)).map _

omit [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)]
  [∀ (n : ℕ), IsScalarTower B0 (B (n + 1)) (B n)] [(n : ℕ) → Algebra (B (n + 1)) (B n)] in
include haB in
lemma isLocalization_ρb0 (n : ℕ) : letI := alg0 B B0 n (E n)
    letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
    letI := (ρb0 B a E B0 n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap B0 (E n) a0) (EtaleOverlap.Bab (a n) (E n)) := by
  letI := alg0 B B0 n (E n)
  have h := (IsLocalization.isLocalization_iff_of_ringEquiv
    (Submonoid.powers (algebraMap (B n) (E n) (a n)))
    (RingEquiv.refl (EtaleOverlap.Bab (a n) (E n)))).mp Localization.isLocalization
  have e : algebraMap B0 (E n) a0 = algebraMap (B n) (E n) (a n) := by
    rw [← haB n]
    rfl
  rw [e]
  exact h

omit [∀ (n : ℕ), IsScalarTower O (R (n + 1)) (R n)]
  [∀ (n : ℕ), IsScalarTower O (B (n + 1)) (B n)] [∀ (n : ℕ), IsScalarTower B0 (B (n + 1)) (B n)]
  [(n : ℕ) → Algebra (B (n + 1)) (B n)] in
include hO hbb hbB in
lemma isLocalization_ρa0 (n : ℕ) : letI := alg0G T hθ B B0 n
    letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
    letI := (ρa0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap B0 (T.G hθ n) b0) (EtaleOverlap.Bab (a n) (E n)) := by
  letI := alg0G T hθ B B0 n
  letI := algBG T hθ B n
  have e : algebraMap B0 (T.G hθ n) b0 = algebraMap (B n) (T.G hθ n) (b n) := by
    rw [← hbB n]
    rfl
  rw [e]
  exact isLocalization_ρa T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hbb hJB n

omit [∀ (n : ℕ), IsScalarTower O (R (n + 1)) (R n)]
  [∀ (n : ℕ), Algebra.FormallyEtale (B n) (E n)] [∀ (n : ℕ), IsScalarTower O (B (n + 1)) (B n)]
  [∀ (n : ℕ), IsScalarTower B0 (B (n + 1)) (B n)] [(n : ℕ) → Algebra (B (n + 1)) (B n)] in
include haB in
lemma locFst (n : ℕ) : letI := alg0G T hθ B B0 n; letI := alg0 B B0 n (E n)
    letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
    IsLocalizedModule (Submonoid.powers a0) (ZariskiTwo.fst
      (ρa0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n)
      (ρb0 B a E B0 n)).toLinearMap :=
  letI := alg0G T hθ B B0 n
  letI := alg0 B B0 n (E n)
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  ZariskiTwo.isLocalizedModule_fst a0 (isUnit_a0 T hθ B a B0 haB n)
    (isLocalization_ρb0 B a E B0 haB n)

omit [∀ (n : ℕ), IsScalarTower O (R (n + 1)) (R n)]
  [∀ (n : ℕ), IsScalarTower O (B (n + 1)) (B n)] [∀ (n : ℕ), IsScalarTower B0 (B (n + 1)) (B n)]
  [(n : ℕ) → Algebra (B (n + 1)) (B n)] in
include hO hbb hbB in
lemma locSnd (n : ℕ) : letI := alg0G T hθ B B0 n; letI := alg0 B B0 n (E n)
    letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
    IsLocalizedModule (Submonoid.powers b0) (ZariskiTwo.snd
      (ρa0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 n)
      (ρb0 B a E B0 n)).toLinearMap :=
  letI := alg0G T hθ B B0 n
  letI := alg0 B B0 n (E n)
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  ZariskiTwo.isLocalizedModule_snd b0 (by
      change IsUnit (algebraMap (B n) (E n) (algebraMap B0 (B n) b0))
      rw [hbB]
      exact hbE n)
    (isLocalization_ρa0 T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hbb hJB B0 hbB n)

variable (hab : Ideal.span {a0, b0} = ⊤) (K : ℕ → Ideal B0)
  (hsEs : ∀ n, Function.Surjective (sE n))
  (hkG : ∀ n, RingHom.ker (T.tr hθ hO n) =
    (K n).map (letI := alg0G T hθ B B0 (n + 1); algebraMap B0 (T.G hθ (n + 1))))
  (hkE : ∀ n, RingHom.ker (sE n) =
    (K n).map (letI := alg0 B B0 (n + 1) (E (n + 1)); algebraMap B0 (E (n + 1))))

include hab hsEs hkG hkE haB hbB hbb in
/-- **The successor maps of the glued coverings are surjective.** -/
theorem surjective_Ymap (n : ℕ) : Function.Surjective
    (Ymap T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB hBR haS sE hsE hσE B0 n) := by
  letI := alg0G T hθ B B0 (n + 1)
  letI := alg0 B B0 (n + 1) (E (n + 1))
  letI := alg0 B B0 (n + 1) (EtaleOverlap.Bab (a (n + 1)) (E (n + 1)))
  letI := alg0G T hθ B B0 n
  letI := alg0 B B0 n (E n)
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  haveI := locFst T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 haB (n + 1)
  haveI := locSnd T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hbb hJB B0 hbB (n + 1)
  haveI := locFst T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 haB n
  haveI := locSnd T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hbb hJB B0 hbB n
  exact ZariskiTwo.surjective_map a0 b0 _ _ _ _ _ (K n) hab (T.surjective_tr hθ hO n) (hsEs n)
    (hkG n) (hkE n)

include hab hsEs hkG hkE haB hbB hbb in
/-- **The kernel of the successor map of the glued coverings is `K n · Y (n+1)`.** -/
theorem ker_Ymap (n : ℕ) : RingHom.ker
      (Ymap T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB hBR haS sE hsE hσE B0 n) =
      (K n).map
        (algebraMap B0 (Y0 T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 (n + 1))) := by
  letI := alg0G T hθ B B0 (n + 1)
  letI := alg0 B B0 (n + 1) (E (n + 1))
  letI := alg0 B B0 (n + 1) (EtaleOverlap.Bab (a (n + 1)) (E (n + 1)))
  letI := alg0G T hθ B B0 n
  letI := alg0 B B0 n (E n)
  letI := alg0 B B0 n (EtaleOverlap.Bab (a n) (E n))
  haveI := locFst T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 haB (n + 1)
  haveI := locSnd T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hbb hJB B0 hbB (n + 1)
  haveI := locFst T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB B0 haB n
  haveI := locSnd T hθ B hO qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hbb hJB B0 hbB n
  exact ZariskiTwo.ker_map a0 b0 _ _ _ _ _ (K n) hab (T.surjective_tr hθ hO n) (hsEs n)
    (hkG n) (hkE n)

end NodeEtaleGlue

end

end SemistableReduction
