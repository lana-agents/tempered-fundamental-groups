/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Patch
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueOverlapSucc

/-!
# The levels of the covering over the second chart (MR12 T2 S6, step G4 over `V₀`)

For an overlap `V : NodeEtaleGlue.Overlap I` the level `n` of the covering over `V₀` is the
glueing `R0 n = Q n ×_{M n} P0 n` (`TwoChartGlue.Patch0`). Let `X` be a `B0'`-algebra with maps
`φQ : X → Q n` and `φP : X → P0 n`, the second one a localization away from `c₀`. Then:

* **`NodeEtaleGlue.Overlap.ρ0a_φQ`**: if `ρ0a ∘ φQ` and `ρ0b ∘ φP` agree modulo `J`, they agree
  (`M n` is formally étale over `B' n` and a localization of `X` away from `c₀ x₀`;
  `EtaleNil.ext`);
* **`NodeEtaleGlue.PatchInput.mk_Loc`**: for a patch over `D(c₀)` (`PatchInput`), the special fibre
  of an element of the patched algebra `G n` on `D(x₀)` is computed by `ℓ0` from its étale
  component.
-/

universe u

namespace SemistableReduction

open AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O} (I : Input θ cov₀ πL)
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (n : ℕ) (g : I.B0) {kg : ℕ}
  (hfg : I.T.f n ∣ algebraMap (I.B n) (I.R n) (algebraMap I.B0 (I.B n) g) ^ kg)
  {M : Type u} [CommRing M] [Algebra (I.B n) M] [Algebra.FormallyEtale (I.B n) M]
  (γM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    I.C1 →ₐ[I.B n] M ⧸ EtaleNil.JB (J θ (R := I.B n)) M)
  (hM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    letI := γM.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) I.C1 (algebraMap I.B0 (I.B n) g))
      (M ⧸ EtaleNil.JB (J θ (R := I.B n)) M))

/-- `M → P n[1/g]` is a localization away from `a`. -/
lemma isLocalization_φPn : letI := algBP I.T I.B n
    letI := (I.φPn n g hfg γM hM).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) M (I.a n)) (I.Pg n g) := by
  letI := algBP I.T I.B n
  haveI := towerBP I.T I.B n
  letI := algBC I.T I.B n
  haveI := towerBC I.T I.B n
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  exact EtaleOverlap.isLocalization_φP (J θ (R := I.B n)) (I.hJB n) (I.a n)
    (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n) (I.T.f n) (σPn I.T I.B n)
    (isLocalization_ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.ha I.hι n)
    (algebraMap I.B0 (I.B n) g) hfg γM hM

/-- `M → E n[1/g]` is a localization away from `b`. -/
lemma isLocalization_φEn : letI := alg0 I.B I.B0 n (I.E n)
    letI := (I.φEn n g γM hM).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) M (I.b n)) (ZariskiTwo.Lc g (I.E n)) := by
  letI := alg0 I.B I.B0 n (I.E n)
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  haveI := isLocalization_C1 I.B I.qB I.C1 I.b I.hbb n
  haveI : IsLocalization.Away (algebraMap (I.B n) (I.E n) (algebraMap I.B0 (I.B n) g))
      (ZariskiTwo.Lc g (I.E n)) := Localization.isLocalization
  exact EtaleOverlap.isLocalization_φE (J θ (R := I.B n)) (I.hJB n) (I.b n) (I.σE n) (I.hbE n)
    (algebraMap I.B0 (I.B n) g) γM hM

omit [Algebra.FormallyEtale (I.B n) M] in
/-- An element of `M` whose image in a localization `S = M[1/s]` (along `φ : M → S` over `B n`)
lies in `J S` has `sᵏ m ∈ J M` for some `k`. -/
lemma exists_pow_mul_mem {S : Type u} [CommRing S] [Algebra (I.B n) S] (φ : M →ₐ[I.B n] S)
    (s : I.B n) (hφ : letI := φ.toRingHom.toAlgebra
      IsLocalization.Away (algebraMap (I.B n) M s) S) (m : M)
    (hm : φ m ∈ EtaleNil.JB (J θ (R := I.B n)) S) :
    ∃ k : ℕ, algebraMap (I.B n) M s ^ k * m ∈ EtaleNil.JB (J θ (R := I.B n)) M := by
  letI := φ.toRingHom.toAlgebra
  have e : EtaleNil.JB (J θ (R := I.B n)) S =
      (EtaleNil.JB (J θ (R := I.B n)) M).map (algebraMap M S) := by
    change Ideal.map (algebraMap (I.B n) S) (J θ (R := I.B n)) =
      Ideal.map (algebraMap M S) (Ideal.map (algebraMap (I.B n) M) (J θ (R := I.B n)))
    rw [Ideal.map_map (algebraMap (I.B n) M) (algebraMap M S),
      show (algebraMap M S).comp (algebraMap (I.B n) M) = algebraMap (I.B n) S from
        φ.comp_algebraMap]
  rw [e] at hm
  obtain ⟨⟨i, ⟨_, l, rfl⟩⟩, hi⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Submonoid.powers (algebraMap (I.B n) M s)) S).1 hm
  have h0 : algebraMap M S (m * algebraMap (I.B n) M s ^ l - i) = 0 := by
    rw [map_sub, map_mul]
    exact sub_eq_zero.2 hi
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap (I.B n) M s)) S _).1 h0
  refine ⟨k + l, ?_⟩
  have : algebraMap (I.B n) M s ^ (k + l) * m =
      (algebraMap (I.B n) M s ^ k * (m * algebraMap (I.B n) M s ^ l - i)) +
        algebraMap (I.B n) M s ^ k * i := by ring
  have hk' : algebraMap (I.B n) M s ^ k * (m * algebraMap (I.B n) M s ^ l - i) = 0 := hk
  rw [this, hk', zero_add]
  exact Ideal.mul_mem_left _ _ i.2

variable [Algebra I.B0 M] [IsScalarTower I.B0 (I.B n) M]

/-- **The special fibre of `ψ`**: an element `w` of `Y n` whose components reduce to `ι₀ c`
(node patch) and `c` (étale piece) for some `c ∈ C1` has `ψ w ≡ γM c` modulo `J`. -/
theorem mk_ψ (w : I.Y hθ n) (c : I.C1)
    (hP : (I.T.level n).σP (Ideal.Quotient.mk _ (I.fstY hθ n w).1.1) =
      algebraMap (Cc I.T n) (Localization.Away (algebraMap (I.R n) (Cc I.T n) (I.T.f n)))
        (I.ι₀ c))
    (hE : I.σE n (Ideal.Quotient.mk _ (I.sndY hθ n w)) =
      algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) c) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) M) (I.ψ hθ hO n g hfg γM hM w) = γM c := by
  letI := algBP I.T I.B n
  letI := alg0 I.B I.B0 n (I.E n)
  set m : M := I.ψ hθ hO n g hfg γM hM w
  have hglue : I.glueM hθ hO n g hfg γM hM m = I.mapYg hθ n g w := by
    change I.glueM hθ hO n g hfg γM hM ((I.glueM hθ hO n g hfg γM hM).symm
      (I.mapYg hθ n g w)) = _
    exact AlgEquiv.apply_symm_apply _ _
  -- the two components of `m`
  have h1 : I.φPn n g hfg γM hM m = algebraMap (I.T.level n).P (I.Pg n g) (I.fstY hθ n w).1.1 := by
    have := congrArg (I.fstYg hθ n g) hglue
    rw [fstYg_glueM, fstYg_mapYg, RingEquiv.symm_apply_eq, eGn_algebraMap] at this
    exact this
  have h2 : I.φEn n g γM hM m = algebraMap (I.E n) (ZariskiTwo.Lc g (I.E n)) (I.sndY hθ n w) := by
    have := congrArg (I.sndYg hθ n g) hglue
    rw [sndYg_glueM, sndYg_mapYg] at this
    exact this
  obtain ⟨m', hm'⟩ := Ideal.Quotient.mk_surjective (γM c)
  -- `m - m'` dies in both localizations modulo `J`
  have hP' : I.φPn n g hfg γM hM (m - m') ∈ EtaleNil.JB (J θ (R := I.B n)) (I.Pg n g) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, sub_eq_zero, h1,
      ← EtaleNil.red_mk (J θ (R := I.B n)) (I.φPn n g hfg γM hM) m', hm', red_φPn]
    exact (I.γPn_eq n g c _ hP).symm
  have hE' : I.φEn n g γM hM (m - m') ∈
      EtaleNil.JB (J θ (R := I.B n)) (ZariskiTwo.Lc g (I.E n)) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, sub_eq_zero, h2,
      ← EtaleNil.red_mk (J θ (R := I.B n)) (I.φEn n g γM hM) m', hm', red_φEn]
    exact (I.γEn_eq n g c _ hE).symm
  obtain ⟨k, hk⟩ := I.exists_pow_mul_mem n (I.φPn n g hfg γM hM) (I.a n)
    (I.isLocalization_φPn n g hfg γM hM) _ hP'
  obtain ⟨l, hl⟩ := I.exists_pow_mul_mem n (I.φEn n g γM hM) (I.b n)
    (I.isLocalization_φEn n g γM hM) _ hE'
  have e1 : algebraMap (I.B n) M (I.a n) = algebraMap I.B0 M I.a0 :=
    (IsScalarTower.algebraMap_apply _ _ _ _).symm
  have e2 : algebraMap (I.B n) M (I.b n) = algebraMap I.B0 M I.b0 :=
    (IsScalarTower.algebraMap_apply _ _ _ _).symm
  rw [e1] at hk
  rw [e2] at hl
  have hc : IsCoprime I.a0 I.b0 := by
    obtain ⟨r, s, h⟩ := Ideal.mem_span_pair.1
      (I.hab.symm ▸ Submodule.mem_top : (1 : I.B0) ∈ Ideal.span {I.a0, I.b0})
    exact ⟨r, s, h⟩
  obtain ⟨r, s, hrs⟩ := hc.pow (m := k) (n := l)
  have hrs' := congrArg (algebraMap I.B0 M) hrs
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_one] at hrs'
  rw [← hm', Ideal.Quotient.eq]
  have h1' : m - m' = algebraMap I.B0 M r * (algebraMap I.B0 M I.a0 ^ k * (m - m')) +
      algebraMap I.B0 M s * (algebraMap I.B0 M I.b0 ^ l * (m - m')) := by
    linear_combination -(m - m') * hrs'
  rw [h1']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hk) (Ideal.mul_mem_left _ _ hl)

end Input

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

lemma isUnit_c0_M : IsUnit (algebraMap (V.B' n) (V.M n) (algebraMap V.B0' (V.B' n) V.c0)) := by
  rw [IsScalarTower.algebraMap_apply (V.B' n) (V.P0.P n) (V.M n)]
  exact (V.P0.hcP n).map _

lemma isUnit_x0_M : IsUnit (algebraMap (V.B' n) (V.M n) (algebraMap V.B0' (V.B' n) V.x0)) := by
  rw [IsScalarTower.algebraMap_apply (V.B' n) (V.P0.P n) (V.M n)]
  exact IsLocalization.Away.algebraMap_isUnit _

variable {X : Type u} [CommRing X] [Algebra V.B0' X]
  (φQ : letI := V.alg0'Q hθ n; X →ₐ[V.B0'] V.Q hθ n)
  (φP : letI := V.alg0'E n; X →ₐ[V.B0'] V.P0.P n)
  (hP : letI := V.alg0'E n; letI := φP.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X V.c0) (V.P0.P n))
  {m : ℕ} (hJ : J θ (R := V.B' n) ^ m = ⊥)

include hP hJ in
/-- **The two maps to the overlap `M n` agree if they agree modulo `J`**: `ρ0b ∘ φP` exhibits
`M n` as `X[1/(c₀ x₀)]`, and `M n` is formally étale over `B' n`. -/
theorem ρ0a_φQ
    (h : ∀ x, Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V.B' n)) (V.M n))
      (V.ρ0a hθ hO n (φQ x)) = Ideal.Quotient.mk _ (V.ρ0b n (φP x))) (x : X) :
    V.ρ0a hθ hO n (φQ x) = V.ρ0b n (φP x) := by
  letI := V.alg0'Q hθ n
  letI := V.alg0'E n
  letI := V.alg0'M n
  haveI := V.P0.etaleM n
  -- `u = ρ0b ∘ φP : X → M n` is a localization away from `c₀ x₀`
  let u : X →+* V.M n := (V.ρ0b n : V.P0.P n →+* V.M n).comp (φP : X →+* V.P0.P n)
  let w : X →+* V.M n := (V.ρ0a hθ hO n : V.Q hθ n →+* V.M n).comp (φQ : X →+* V.Q hθ n)
  have hu : letI := u.toAlgebra
      IsLocalization.Away (algebraMap V.B0' X V.c0 * algebraMap V.B0' X V.x0) (V.M n) := by
    refine RingHomAway.comp (φP : X →+* V.P0.P n) (V.ρ0b n : V.P0.P n →+* V.M n) _ _ hP ?_
    change letI := (V.ρ0b n : V.P0.P n →+* V.M n).toAlgebra
      IsLocalization.Away (φP (algebraMap V.B0' X V.x0)) (V.M n)
    rw [AlgHom.commutes]
    exact V.isLocalization_ρ0b n
  letI := u.toAlgebra
  have hwu : IsUnit (w (algebraMap V.B0' X V.c0 * algebraMap V.B0' X V.x0)) := by
    simp only [w, RingHom.comp_apply, map_mul, RingHom.coe_coe, AlgHom.commutes]
    exact (V.isUnit_c0_M n).mul (V.isUnit_x0_M n)
  let w' : V.M n →+* V.M n := IsLocalization.Away.lift _ hwu
  have hw' : ∀ y, w' (u y) = w y := IsLocalization.Away.lift_eq _ hwu
  let w'' : V.M n →ₐ[V.B' n] V.M n :=
    { w' with
      commutes' := fun r ↦ by
        obtain ⟨y, rfl⟩ := V.surjB' n r
        have h1 : algebraMap (V.B' n) (V.M n) (algebraMap V.B0' (V.B' n) y) =
            u (algebraMap V.B0' X y) := by
          simp only [u, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
          rfl
        change w' _ = _
        rw [h1, hw']
        simp only [w, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
        simp only [u, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes] }
  have key : w'' = AlgHom.id (V.B' n) (V.M n) := by
    refine EtaleNil.ext (J θ (R := V.B' n)) hJ fun e ↦ ?_
    have hext : (Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V.B' n)) (V.M n))).comp w' =
        Ideal.Quotient.mk _ := by
      refine IsLocalization.ringHom_ext
        (Submonoid.powers (algebraMap V.B0' X V.c0 * algebraMap V.B0' X V.x0))
        (RingHom.ext fun y ↦ ?_)
      change Ideal.Quotient.mk _ (w' (u y)) = Ideal.Quotient.mk _ (u y)
      rw [hw']
      exact h y
    exact RingHom.congr_fun hext e
  have h2 := hw' x
  change w'' (u x) = w x at h2
  rw [key] at h2
  exact h2.symm

end Overlap

namespace PatchInput

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  (D : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

/-- **The special fibre of the patch on `D(x₀)`**: an element `g` of `G n` whose étale component
reduces to `ι₀ c` has special fibre `ℓ0 c` on `D(x₀)`. -/
theorem mk_Loc (g : D.G hθ n) (c : C0)
    (hg : (D.T.level n).σP (Ideal.Quotient.mk _ (D.fst hθ n g)) =
      algebraMap (Cc D.T n) (D.Lf n) (D.ι₀ c)) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' n)) (D.Loc hθ n))
      (algebraMap (D.G hθ n) (D.Loc hθ n) g) = D.ℓ0 hθ hO n c := by
  have h1 : (D.T.level n).σP.symm (algebraMap (Cc D.T n) (D.Lf n) (D.ι₀ c)) =
      Ideal.Quotient.mk _ (D.fst hθ n g) := by
    rw [← hg, AlgEquiv.symm_apply_apply]
  have h2 : (D.eR hθ hO n).symm (algebraMap (D.P n) (D.Mp n) (D.fst hθ n g)) =
      algebraMap (D.G hθ n) (D.Loc hθ n) g := by
    rw [AlgEquiv.symm_apply_eq]
    exact (D.e_algebraMap hθ hO n g).symm
  change _ = D.qe hθ hO n (EtaleNil.red (J θ (R := D.R n))
    (IsScalarTower.toAlgHom (D.R n) (D.P n) (D.Mp n))
      ((D.T.level n).σP.symm (algebraMap (Cc D.T n) (D.Lf n) (D.ι₀ c))))
  rw [h1, EtaleNil.red_mk, qe, Ideal.quotientEquiv_mk]
  change _ = Ideal.Quotient.mk _ ((D.eR hθ hO n).symm (algebraMap (D.P n) (D.Mp n)
    (D.fst hθ n g)))
  rw [h2]

end PatchInput

end NodeEtaleGlue

end

end SemistableReduction
