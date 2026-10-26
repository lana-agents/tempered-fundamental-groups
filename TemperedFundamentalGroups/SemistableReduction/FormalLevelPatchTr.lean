/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalLevelPatch
import TemperedFundamentalGroups.SemistableReduction.LevelTowerFst

/-!
# Transition maps of level patches (MR12 T2 S6, step G3, compatibility with the tower)

The patched algebra `G = P ×_{N_f} N` of a level is determined by its étale component when `f` is
regular on `N` (**`FormalGlueing.ext_of_fst_eq`**). Hence a transition map `tr : G (n+1) → G n`
of a tower of patched algebras (`LevelTower.Data.tr`, whose étale component is the reduction
`ρP` of the étale parts, `LevelTower.Data.tr_fst_eq`) is determined by `ρP`
(**`LevelTower.Data.tr_eq_of_fst`**). Two maps out of an algebra `M` which is formally étale over
`D(f)` into a nilpotent thickening agree if they agree modulo the thickening
(**`FormalLevel.EtaleIso.ext_away`**); so `ρP` is compatible with any étale identifications
`φ₁` of the levels with algebras `M n` compatible with the reductions to the special fibre
(**`LevelTower.Data.ρP_comp_eq`**), and the transition maps of the patched algebras are the maps
`M (n+1) → M n` under identifications whose étale components are such `φ₁`
(**`LevelTower.Data.tr_eq_of_etale`**). This is the compatibility of
`FormalLevel.levelPatchEquiv` with the tower (the hypothesis `hαc` of the algebraization).
-/

universe u

open TensorProduct

namespace FormalGlueing

variable {R : Type*} [CommRing R] (f : R) {P : Type*} [CommRing P] [Algebra R P]
  (N : Type*) [CommRing N] [Algebra R N] (α : P →ₐ[R] Localization.Away (algebraMap R N f))

/-- Powers of a regular element are regular. -/
lemma eq_zero_of_pow_mul_eq_zero (hN : ∀ x : N, algebraMap R N f * x = 0 → x = 0) :
    ∀ (k : ℕ) (z : N), algebraMap R N f ^ k * z = 0 → z = 0 := by
  intro k
  induction k with
  | zero => intro z hz; simpa using hz
  | succ k ih =>
    intro z hz
    exact ih z (hN _ (by rw [← mul_assoc, ← pow_succ']; exact hz))

/-- **The glued algebra is determined by its first component** if `f` is regular on `N`. -/
theorem ext_of_fst_eq (hN : ∀ x : N, algebraMap R N f * x = 0 → x = 0) {x y : glued N α}
    (h : x.1.1 = y.1.1) : x = y := by
  have hx := (mem_glued N α).1 x.2
  have hy := (mem_glued N α).1 y.2
  have h0 : algebraMap N (Localization.Away (algebraMap R N f)) (x.1.2 - y.1.2) = 0 := by
    rw [map_sub, ← hx, ← hy, h, sub_self]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R N f)) _ _).1 h0
  exact Subtype.ext (Prod.ext h (sub_eq_zero.1 (eq_zero_of_pow_mul_eq_zero f N hN k _ hk)))

end FormalGlueing

namespace SemistableReduction

namespace FormalLevel.EtaleIso

/-- **Maps out of an algebra formally étale over `D(f)` are determined modulo a nilpotent
ideal**: two `A`-algebra maps `M → S` inverting `f` and agreeing modulo `I` (`I` nilpotent) are
equal if `M[1/f]` is formally étale over `A`. -/
theorem ext_away {A M S : Type*} [CommRing A] [CommRing M] [Algebra A M] [CommRing S]
    [Algebra A S] (f : A) [Algebra.FormallyEtale A (Localization.Away (algebraMap A M f))]
    (I : Ideal S) {m : ℕ} (hI : I ^ m = ⊥) (hf : IsUnit (algebraMap A S f))
    (g₁ g₂ : M →ₐ[A] S)
    (h : ∀ z, Ideal.Quotient.mk I (g₁ z) = Ideal.Quotient.mk I (g₂ z)) : g₁ = g₂ := by
  haveI : IsAdicComplete I S := CompleteFinite.isAdicComplete_of_pow_eq_bot I hI
  have hu : ∀ g : M →ₐ[A] S, IsUnit (g (algebraMap A M f)) := fun g ↦ by
    rw [g.commutes]; exact hf
  let G : (M →ₐ[A] S) → (Localization.Away (algebraMap A M f) →ₐ[A] S) := fun g ↦
    { IsLocalization.Away.lift (algebraMap A M f) (hu g) with
      commutes' := fun a ↦ by
        change IsLocalization.Away.lift (algebraMap A M f) (hu g)
          (algebraMap A (Localization.Away (algebraMap A M f)) a) = _
        rw [IsScalarTower.algebraMap_apply A M (Localization.Away (algebraMap A M f)),
          IsLocalization.Away.lift_eq]
        exact g.commutes a }
  have hG : ∀ g z, G g (algebraMap M (Localization.Away (algebraMap A M f)) z) = g z :=
    fun g z ↦ IsLocalization.Away.lift_eq _ (hu g) z
  have hGG : G g₁ = G g₂ := by
    refine EtaleLift.ext_of_comp_eq I (AlgHom.coe_ringHom_injective
      (IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A M f))
        (RingHom.ext fun z ↦ ?_)))
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [hG, hG, h]
  ext z
  rw [← hG g₁, ← hG g₂, hGG]

end FormalLevel.EtaleIso

noncomputable section

namespace LevelTower.Data

open KummerEtale AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (T : Data (θ := θ) R cov₀ πL) (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The transition maps are determined by their étale components**: `tr x = y` as soon as the
reduction `ρP` of the étale component of `x` is the étale component of `y`. -/
theorem tr_eq_of_fst (n : ℕ) (x : T.G hθ (n + 1)) (y : T.G hθ n) (h : T.ρP n x.1.1 = y.1.1) :
    T.tr hθ hO n x = y :=
  FormalGlueing.ext_of_fst_eq (T.f n) _ _
    (noTorsion_NFall (T.level n).L (T.level n).M (T.level n).hflat (T.level n).hidem
      (T.level n).hfχ (T.level n).hcidem (T.level n).hreg)
    ((T.tr_fst_eq hθ hO n x).trans h)

omit [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
/-- **`ρP` is compatible with étale identifications of consecutive levels**: if
`φ' : M' → P (n+1)` and `φ : M → P n` are compatible with the reductions `ρ'`, `ρ` to the special
fibre `C` (via `σP`), `μ : M' → M` is semilinear over `R (n+1) → R n` and compatible with `ρ'`,
`ρ`, and `M'[1/f]` is formally étale over `R (n+1)`, then `ρP ∘ φ' = φ ∘ μ`. -/
theorem ρP_comp_eq (n : ℕ) {M' M : Type*} [CommRing M'] [Algebra (R (n + 1)) M'] [CommRing M]
    [Algebra (R n) M]
    [Algebra.FormallyEtale (R (n + 1))
      (Localization.Away (algebraMap (R (n + 1)) M' (T.f (n + 1))))]
    (φ' : M' →ₐ[R (n + 1)] (T.level (n + 1)).P) (φ : M →ₐ[R n] (T.level n).P) (μ : M' →+* M)
    (hμ : ∀ r, μ (algebraMap (R (n + 1)) M' r) =
      algebraMap (R n) M (algebraMap (R (n + 1)) (R n) r))
    (ρ' : M' → (cov₀.transport (h := T.hfe (n + 1))).C)
    (ρ : M → (cov₀.transport (h := T.hfe n)).C)
    (hσ' : ∀ z, (T.level (n + 1)).σP (Ideal.Quotient.mk _ (φ' z)) = algebraMap _ _ (ρ' z))
    (hσ : ∀ z, (T.level n).σP (Ideal.Quotient.mk _ (φ z)) = algebraMap _ _ (ρ z))
    (hρ : ∀ z, ρ (μ z) =
      LevelStep.idC (T.f (n + 1)) (T.f n) (T.hfe (n + 1)) (T.hfe n) cov₀ (ρ' z))
    (z : M') : T.ρP n (φ' z) = φ (μ z) := by
  letI := algP T.level n
  haveI : IsScalarTower (R (n + 1)) (R n) (T.level n).P :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let g₂ : M' →ₐ[R (n + 1)] (T.level n).P :=
    { (φ : M →+* (T.level n).P).comp μ with
      commutes' := fun r ↦ by
        change φ (μ (algebraMap (R (n + 1)) M' r)) = _
        rw [hμ, AlgHom.commutes]
        rfl }
  have hf : IsUnit (algebraMap (R (n + 1)) (T.level n).P (T.f (n + 1))) := by
    rw [IsScalarTower.algebraMap_apply (R (n + 1)) (R n) (T.level n).P]
    change IsUnit (algebraMap (R n) _ (LevelStep.f' (R' := R n) (T.f (n + 1))))
    rw [T.hf n]
    exact (T.level n).hfP
  have hI : ((J θ (R := R n)).map (algebraMap (R n) (T.level n).P)) ^ (T.level n).m = ⊥ := by
    rw [← Ideal.map_pow, (T.level n).hJ, Ideal.map_bot]
  have key := FormalLevel.EtaleIso.ext_away (T.f (n + 1)) _ hI hf
    (((T.ρP n).restrictScalars (R (n + 1))).comp φ') g₂ fun w ↦ by
      apply (T.level n).σP.injective
      change (T.level n).σP (Ideal.Quotient.mk _ (T.ρP n (φ' w))) =
        (T.level n).σP (Ideal.Quotient.mk _ (φ (μ w)))
      rw [σP_ρP, hσ', hσ, hρ, LevelStep.Tmap_algebraMap]
  exact AlgHom.congr_fun key z

/-- **The transition maps of the patched algebras under étale identifications**: if
`x ∈ G (n+1)`, `y ∈ G n` have étale components `φ' z`, `φ (μ z)` (hypotheses of `ρP_comp_eq`),
then `tr x = y`. -/
theorem tr_eq_of_etale (n : ℕ) {M' M : Type*} [CommRing M'] [Algebra (R (n + 1)) M'] [CommRing M]
    [Algebra (R n) M]
    [Algebra.FormallyEtale (R (n + 1))
      (Localization.Away (algebraMap (R (n + 1)) M' (T.f (n + 1))))]
    (φ' : M' →ₐ[R (n + 1)] (T.level (n + 1)).P) (φ : M →ₐ[R n] (T.level n).P) (μ : M' →+* M)
    (hμ : ∀ r, μ (algebraMap (R (n + 1)) M' r) =
      algebraMap (R n) M (algebraMap (R (n + 1)) (R n) r))
    (ρ' : M' → (cov₀.transport (h := T.hfe (n + 1))).C)
    (ρ : M → (cov₀.transport (h := T.hfe n)).C)
    (hσ' : ∀ z, (T.level (n + 1)).σP (Ideal.Quotient.mk _ (φ' z)) = algebraMap _ _ (ρ' z))
    (hσ : ∀ z, (T.level n).σP (Ideal.Quotient.mk _ (φ z)) = algebraMap _ _ (ρ z))
    (hρ : ∀ z, ρ (μ z) =
      LevelStep.idC (T.f (n + 1)) (T.f n) (T.hfe (n + 1)) (T.hfe n) cov₀ (ρ' z))
    (z : M') (x : T.G hθ (n + 1)) (y : T.G hθ n) (hx : x.1.1 = φ' z) (hy : y.1.1 = φ (μ z)) :
    T.tr hθ hO n x = y :=
  T.tr_eq_of_fst hθ hO n x y (by rw [hx, hy]; exact T.ρP_comp_eq n φ' φ μ hμ ρ' ρ hσ' hσ hρ z)

end LevelTower.Data

namespace FormalLevel

open KummerEtale FormalKummer AdmissibleLift

attribute [local instance] KummerNormAtData.algO

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ϖ : O} {n M' : ℕ} {x y : R}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
  {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
  (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
  (hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
  (D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j)) {g : R}
  (hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
  (hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j))
  (hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical)
  (φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g))
  (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
  (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y))
  (ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g))
  (hfin : Module.Finite (Rs θ R) (Cs θ R B))
  (het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale)
  (hk : ∀ j i, ((D j).d i : k) ≠ 0)
  (Rt : ℕ → Type u) [∀ l, CommRing (Rt l)] [∀ l, Algebra O (Rt l)]
  [∀ l, IsNoetherianRing (Rt l)] [∀ l, Algebra R (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
  [∀ l, Algebra (Rt (l + 1)) (Rt l)] [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)]
  [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)]
  (T : LevelTower.Data (θ := θ) Rt
    (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk) (πK 𝔪 D))
  (he : ∀ l (r : R), T.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Rt l) r))

/-- The map `Rt (l+1) ⊗_R B → Rt l ⊗_R B` of the levels. -/
abbrev levelMap (l : ℕ) : Rt (l + 1) ⊗[R] B →ₐ[R] Rt l ⊗[R] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (Rt (l + 1)) (Rt l)) (AlgHom.id R B)

omit [∀ l, IsNoetherianRing (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
  [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)] in
/-- The reductions `ρ` of consecutive levels are compatible with `levelMap`. -/
lemma ρ_levelMap (l : ℕ) (z : Rt (l + 1) ⊗[R] B) :
    ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe he l
        (levelMap Rt l z) =
      LevelStep.idC (T.f (l + 1)) (T.f l) (T.hfe (l + 1)) (T.hfe l)
        (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk)
        (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe he (l + 1)
          z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]; rfl
  | tmul c b =>
    rw [levelMap, Algebra.TensorProduct.map_tmul, ρ_tmul, ρ_tmul]
    simp only [LevelStep.idC]
    congr 1
    change algebraMap (Rs θ R) (Cs θ R B) ((T.e l).symm (Ideal.Quotient.mk _
        (algebraMap (Rt (l + 1)) (Rt l) c))) =
      algebraMap (Rs θ R) (Cs θ R B) ((T.e (l + 1)).symm (Ideal.Quotient.mk _ c))
    rw [← T.he l c, AlgEquiv.symm_apply_apply]

variable [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]

/-- **The level data of the M2 lift of `covOf …` along a tower `T`** (the per-level hypotheses
of `FormalLevel.levelPatchEquiv`): level nodes `𝔪' l` reducing into the special-fibre nodes,
residue maps `r l`, node coordinates `hχL` and lifted idempotents `hεL` of the levels of `T`,
and the étaleness of `(Rt l ⊗_R B)[1/f l]`. -/
structure NodeLevels where
  𝔪' : ∀ l, ι → Ideal (Rt l)
  isMaximal : ∀ l j, (𝔪' l j).IsMaximal
  hinj : ∀ l, Function.Injective (𝔪' l)
  hf : ∀ l j, T.f l ∈ 𝔪' l j
  hrad : ∀ l, ⨅ j, 𝔪' l j ≤ (Ideal.span {T.f l}).radical
  r : ∀ l j, (D j).N₁ →ₐ[R] Rt l ⧸ 𝔪' l j
  hχL : ∀ l p a, χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe
    (T.level l) p a = algebraMap R (FormalPatchLevel.Hat (T.f l)) (chart hxy (D p.1) p.2 a)
  hεL : ∀ l p, (haveI := isMaximal l; CompletionProd.idem (hinj l) (hf l) (hrad l) p.1) =
    (T.level l).L.ε p
  hm : ∀ l j, (𝔪' l j).map (red θ (T.e l)) ≤ sIdeal (θ := θ) (𝔪 j)
  hr : ∀ l j, ∀ z ∈ (D j).𝔫, r l j z = 0
  etale : ∀ l, Algebra.FormallyEtale (Rt l)
    (Localization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (T.f l)))

namespace NodeLevels

variable {hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T}
variable (V : NodeLevels hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

include V in
/-- The étale component `φ₁ : Rt l ⊗_R B → P l` of the level patch (`exists_φ₁`). -/
def φ₁ (l : ℕ) : Rt l ⊗[R] B →ₐ[Rt l] (T.level l).P :=
  haveI := V.etale l
  (exists_φ₁ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe he
    (T.level l)).choose

omit [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)] [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)]
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
lemma isLocalization_φ₁ (l : ℕ) : letI := (V.φ₁ he l).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (T.f l)) (T.level l).P :=
  haveI := V.etale l
  (exists_φ₁ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe he
    (T.level l)).choose_spec.1

omit [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)] [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)]
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
lemma σP_φ₁ (l : ℕ) (z : Rt l ⊗[R] B) :
    (T.level l).σP (Ideal.Quotient.mk _ (V.φ₁ he l z)) = algebraMap _ _
      (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe he l z) :=
  haveI := V.etale l
  (exists_φ₁ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe he
    (T.level l)).choose_spec.2 z

set_option maxRecDepth 20000 in
/-- **The level-`l` patch of the M2 lift is `Rt l ⊗_R B`** (`FormalLevel.levelPatchEquiv` at
the level data `V`). -/
def equiv (l : ℕ) : Rt l ⊗[R] B ≃ₐ[Rt l] T.G hθ.out l :=
  haveI := V.isMaximal l
  haveI := V.etale l
  levelPatchEquiv hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe he
    (T.level l) (V.hinj l) (V.hf l) (V.hrad l) (V.r l) (V.hχL l) (V.hεL l) (V.hm l) (V.hr l) hO

omit [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)] [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)] in
lemma equiv_fst (l : ℕ) (z : Rt l ⊗[R] B) : (V.equiv he hO l z).1.1 = V.φ₁ he l z := rfl

set_option maxRecDepth 20000 in
/-- **The level patches of the M2 lift form a tower**: `equiv` commutes with the transition maps
`tr` of the tower and the maps `Rt (l+1) ⊗_R B → Rt l ⊗_R B`. -/
theorem equiv_tr (l : ℕ) (z : Rt (l + 1) ⊗[R] B) :
    T.tr hθ.out hO l (V.equiv he hO (l + 1) z) = V.equiv he hO l (levelMap Rt l z) :=
  haveI := V.etale (l + 1)
  T.tr_eq_of_etale hθ.out hO l (V.φ₁ he (l + 1)) (V.φ₁ he l) (levelMap Rt l).toRingHom
    (fun c ↦ by
      change Algebra.TensorProduct.map _ _ (c ⊗ₜ (1 : B)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl)
    (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe he (l + 1))
    (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T.hfe he l)
    (V.σP_φ₁ he (l + 1)) (V.σP_φ₁ he l)
    (ρ_levelMap hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt T he l) z
    _ _ rfl rfl

end NodeLevels

end FormalLevel

end

end SemistableReduction
