/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueHom
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueOverlapSpecial
import TemperedFundamentalGroups.SemistableReduction.OverlapFibreHom

/-!
# The overlap condition of maps of glued levels (MR12 I3, generic core, step 2)

For two overlaps `V : Overlap I`, `V' : Overlap I'` (the second chart of two coverings) and maps
`y n : Y n → Y' n` of the coverings over the first chart and `p n : P0 n → P0' n` of the pieces
over `D(c₀)`, compatible with the successor maps, the hypothesis `hψ` of
`NodeEtaleGlue.Overlap.twoChartMap` (`ψ' ∘ y = mM p ∘ ψ` on the overlaps `M n = P0 n[1/x₀]`)
follows from the special fibre at the bottom level:

* `Piece0.ker_sM_le`: the kernel of the successor map `M (n+1) → M n` of a piece lies in
  `ϖⁿ⁺¹ M (n+1)` (a square-zero ideal);
* `Overlap.yM`: the map `M n = Y n[1/g] → M' n` extending `ψ' ∘ y` (`yM_ψ`, `sM_yM`);
* **`Overlap.yM_eq_mM`**, **`Overlap.hψ_of_bottom`**: if `y` and `mM p` are semilinear over a map
  `β₀` of the first charts, and at the bottom level (`J = 0`) `y 0` is `φ₁ : C1 → C1'` under
  `yEquiv` and `mM p` is `φ₁` under `γM`, then `ψ' (y n z) = mM p (ψ z)` at every level — by
  induction, using the uniqueness of maps out of the formally unramified `M (n+1)` into the
  square-zero thickening `M' (n+1)` of `M' n`.
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace OverlapPiece

open EtaleNil

/-! ### Naturality of the special fibre `γ0` of a piece restricted to the overlap -/

variable {O : Type u} [CommRing O] (K : Ideal O)
  {B'n : Type u} [CommRing B'n] [Algebra O B'n] {x0 : B'n}
  {E0 : Type u} [CommRing E0] [Algebra B'n E0] [Algebra O E0] [IsScalarTower O B'n E0]
  {Bs Bs' Ws : Type u} [CommRing Bs] [CommRing Bs'] [CommRing Ws]
  {C1 C0 : Type u} [CommRing C1] [CommRing C0] [Algebra Bs C1] [Algebra Bs' C0]
  {x1s : Bs} {x0s c0s : Bs'}
  [Algebra Ws (Localization.Away (algebraMap Bs C1 x1s))]
  [Algebra Ws (Localization.Away (algebraMap Bs' C0 x0s))]
  {ω : Localization.Away (algebraMap Bs' C0 x0s) ≃ₐ[Ws] Localization.Away (algebraMap Bs C1 x1s)}
  {l0 : C0 →+* M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0)}
  (hl0loc : letI := l0.toAlgebra
    IsLocalization.Away (algebraMap Bs' C0 c0s * algebraMap Bs' C0 x0s)
      (M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0)))
  {B'n₂ : Type u} [CommRing B'n₂] [Algebra O B'n₂] {x0' : B'n₂}
  {E0' : Type u} [CommRing E0'] [Algebra B'n₂ E0'] [Algebra O E0'] [IsScalarTower O B'n₂ E0']
  {Bs₂ Bs'₂ Ws₂ : Type u} [CommRing Bs₂] [CommRing Bs'₂] [CommRing Ws₂]
  {C1' C0' : Type u} [CommRing C1'] [CommRing C0'] [Algebra Bs₂ C1'] [Algebra Bs'₂ C0']
  {x1s' : Bs₂} {x0s' c0s' : Bs'₂}
  [Algebra Ws₂ (Localization.Away (algebraMap Bs₂ C1' x1s'))]
  [Algebra Ws₂ (Localization.Away (algebraMap Bs'₂ C0' x0s'))]
  {ω' : Localization.Away (algebraMap Bs'₂ C0' x0s') ≃ₐ[Ws₂]
    Localization.Away (algebraMap Bs₂ C1' x1s')}
  {l0' : C0' →+* M x0' E0' ⧸ JB (K.map (algebraMap O B'n₂)) (M x0' E0')}
  (hl0loc' : letI := l0'.toAlgebra
    IsLocalization.Away (algebraMap Bs'₂ C0' c0s' * algebraMap Bs'₂ C0' x0s')
      (M x0' E0' ⧸ JB (K.map (algebraMap O B'n₂)) (M x0' E0')))

/-- The ideal `J M = K M` of the overlap. -/
lemma JB_eq_map : JB (K.map (algebraMap O B'n)) (M x0 E0) = K.map (algebraMap O (M x0 E0)) := by
  rw [JB, Ideal.map_map]
  congr 1
  ext o
  change algebraMap B'n (M x0 E0) (algebraMap O B'n o) = _
  rw [IsScalarTower.algebraMap_apply B'n E0 (M x0 E0), ← IsScalarTower.algebraMap_apply O B'n E0,
    ← IsScalarTower.algebraMap_apply O E0 (M x0 E0)]

variable (mm : M x0 E0 →+* M x0' E0')
  (hmmO : ∀ o, mm (algebraMap O (M x0 E0) o) = algebraMap O (M x0' E0') o)

include hmmO in
lemma JB_le_comap_mm : JB (K.map (algebraMap O B'n)) (M x0 E0) ≤
    (JB (K.map (algebraMap O B'n₂)) (M x0' E0')).comap mm := by
  rw [JB_eq_map, JB_eq_map, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro o ho
  rw [Ideal.mem_comap, RingHom.comp_apply, hmmO]
  exact Ideal.mem_map_of_mem _ ho

variable (φ0 : C0 →+* C0')
  (hl : ∀ c m, Ideal.Quotient.mk (JB (K.map (algebraMap O B'n)) (M x0 E0)) m = l0 c →
    Ideal.Quotient.mk (JB (K.map (algebraMap O B'n₂)) (M x0' E0')) (mm m) = l0' (φ0 c))
  (Lx0 : Localization.Away (algebraMap Bs' C0 x0s) →+* Localization.Away (algebraMap Bs'₂ C0' x0s'))
  (hLx0 : ∀ c, Lx0 (algebraMap C0 _ c) = algebraMap C0' _ (φ0 c))
  (φ1 : C1 →+* C1')
  (Lx1 : Localization.Away (algebraMap Bs C1 x1s) →+* Localization.Away (algebraMap Bs₂ C1' x1s'))
  (hLx1 : ∀ c, Lx1 (algebraMap C1 _ c) = algebraMap C1' _ (φ1 c))
  (hω : ∀ z, ω' (Lx0 z) = Lx1 (ω z))

include hmmO hl hLx0 hLx1 hω in
/-- **The special fibre `γ0 : C1 → M/J` of a piece on the overlap is natural**: a map `mm` of the
overlaps reducing to `φ0` on `C0` (through `l0`) reduces to `φ1` on `C1` (through `γ0`), if `φ0`,
`φ1` are compatible with the chart descriptions `ω`, `ω'`. -/
theorem γ0_map (c : C1) (m : M x0 E0)
    (hm : Ideal.Quotient.mk (JB (K.map (algebraMap O B'n)) (M x0 E0)) m =
      γ0 K x0 E0 x1s x0s c0s ω l0 hl0loc c) :
    Ideal.Quotient.mk (JB (K.map (algebraMap O B'n₂)) (M x0' E0')) (mm m) =
      γ0 K x0' E0' x1s' x0s' c0s' ω' l0' hl0loc' (φ1 c) := by
  set mmb := Ideal.quotientMap _ mm (JB_le_comap_mm K mm hmmO)
  have hB : mmb.comp (ℓx K x0 E0 x0s c0s l0 hl0loc) =
      (ℓx K x0' E0' x0s' c0s' l0' hl0loc').comp Lx0 :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap Bs' C0 x0s)) (RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply]
      rw [ℓx_algebraMap, hLx0, ℓx_algebraMap]
      obtain ⟨m, hm⟩ := Ideal.Quotient.mk_surjective (l0 c)
      rw [← hm, Ideal.quotientMap_mk]
      exact hl c m hm)
  have hω' : Lx0 (ω.symm (algebraMap C1 _ c)) = ω'.symm (algebraMap C1' _ (φ1 c)) := by
    rw [AlgEquiv.eq_symm_apply, hω, AlgEquiv.apply_symm_apply, hLx1]
  change Ideal.Quotient.mk _ (mm m) = ℓx K x0' E0' x0s' c0s' l0' hl0loc'
    (ω'.symm (algebraMap C1' _ (φ1 c)))
  rw [← hω', ← RingHom.comp_apply _ Lx0, ← hB, RingHom.comp_apply]
  change _ = mmb (ℓx K x0 E0 x0s c0s l0 hl0loc (ω.symm (algebraMap C1 _ c)))
  rw [show ℓx K x0 E0 x0s c0s l0 hl0loc (ω.symm (algebraMap C1 _ c)) =
    γ0 K x0 E0 x1s x0s c0s ω l0 hl0loc c from rfl, ← hm, Ideal.quotientMap_mk]

end OverlapPiece

namespace NodeEtaleGlue

/-! ### The kernel of the successor maps of a piece -/

namespace Piece0

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}
  (P0 : Piece0 θ B' qB' C0 x0 c0 x0s c0s ϖ)

lemma sP_x0 (n : ℕ) :
    P0.sP n (algebraMap (B' (n + 1)) (P0.P (n + 1)) (algebraMap B0' (B' (n + 1)) x0)) =
      algebraMap (B' n) (P0.P n) (algebraMap B0' (B' n) x0) := by
  rw [P0.hsP, ← IsScalarTower.algebraMap_apply B0' (B' (n + 1)) (B' n)]

/-- **The kernel of the successor map of the restriction to the overlap** lies in
`ϖⁿ⁺¹ M (n+1)`. -/
theorem ker_sM_le (n : ℕ) : RingHom.ker (P0.sM n) ≤
    (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (Loc0 (B' (n + 1)) (P0.P (n + 1)) x0)) := by
  intro m hm
  rw [RingHom.mem_ker] at hm
  set x : P0.P (n + 1) := algebraMap (B' (n + 1)) (P0.P (n + 1)) (algebraMap B0' (B' (n + 1)) x0)
  obtain ⟨⟨p, ⟨_, kk, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) m
  dsimp only at hm ⊢
  have h1 : P0.sM n (algebraMap (P0.P (n + 1)) (Loc0 (B' (n + 1)) (P0.P (n + 1)) x0) p) = 0 := by
    rw [← IsLocalization.mk'_spec (M := Submonoid.powers x) (Loc0 (B' (n + 1)) (P0.P (n + 1)) x0) p
      (⟨x ^ kk, kk, rfl⟩ : Submonoid.powers x), map_mul, hm, zero_mul]
  rw [P0.hsM, IsLocalization.map_eq_zero_iff (Submonoid.powers
    (algebraMap (B' n) (P0.P n) (algebraMap B0' (B' n) x0)))] at h1
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := h1
  have h2 : x ^ j * p ∈ RingHom.ker (P0.sP n) := by
    rw [RingHom.mem_ker, map_mul, map_pow, sP_x0]
    exact hj
  rw [P0.hkP] at h2
  have h3 : algebraMap (P0.P (n + 1)) (Loc0 (B' (n + 1)) (P0.P (n + 1)) x0) (x ^ j * p) ∈
      (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (Loc0 (B' (n + 1)) (P0.P (n + 1)) x0)) := by
    rw [IsScalarTower.algebraMap_eq O (P0.P (n + 1)) (Loc0 (B' (n + 1)) (P0.P (n + 1)) x0),
      ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ h2
  have h4 : IsLocalization.mk' (Loc0 (B' (n + 1)) (P0.P (n + 1)) x0) p
      (⟨x ^ kk, kk, rfl⟩ : Submonoid.powers x) =
      algebraMap _ _ (x ^ j * p) * IsLocalization.mk' (Loc0 (B' (n + 1)) (P0.P (n + 1)) x0)
        (1 : P0.P (n + 1)) (⟨x ^ (j + kk), j + kk, rfl⟩ : Submonoid.powers x) := by
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [pow_add]
    ring
  rw [h4]
  exact Ideal.mul_mem_right _ _ h3

end Piece0

/-! ### The overlap condition -/

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {R₀' : Type u} [CommRing R₀'] [Algebra k R₀'] {f₀' : R₀'}
  {φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀'} {ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀'}
  {cov₀' : Admissible.Covering φ₀' ψ₀'} {πL' : cov₀'.ι → O}

namespace Input

variable (I : Input θ cov₀ πL) (I' : Input θ cov₀' πL') (hθ : Function.Surjective θ) (n : ℕ)
  (g : I.T.G hθ n →+* I'.T.G hθ n) (e : I.E n →+* I'.E n)
  (he : e (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I'.B n) (I'.E n) (I'.a n))
  (β : I.B n →+* I'.B n) (hβJ : (J θ (R := I.B n)).map β ≤ J θ (R := I'.B n))
  (hβa : β (I.a n) = I'.a n)
  (heβ : ∀ r, e (algebraMap (I.B n) (I.E n) r) = algebraMap (I'.B n) (I'.E n) (β r))
  (p : (I.T.level n).P →+* (I'.T.level n).P)
  (hgp : ∀ x, fstP I'.T hθ n (g x) = p (fstP I.T hθ n x))
  (hpβ : ∀ r, p (algebraMap (I.R n) (I.T.level n).P (algebraMap (I.B n) (I.R n) r)) =
    algebraMap (I'.R n) (I'.T.level n).P (algebraMap (I'.B n) (I'.R n) (β r)))
  (φc : cov₀.C →+* cov₀'.C)
  (ℓf : Localization.Away (algebraMap (I.R n) (Cc I.T n) (I.T.f n)) →+*
    Localization.Away (algebraMap (I'.R n) (Cc I'.T n) (I'.T.f n)))
  (hℓf : ∀ c, ℓf (algebraMap (Cc I.T n) _ c) = algebraMap (Cc I'.T n) _ (φc c))
  (hp : ∀ x, (I'.T.level n).σP (Ideal.Quotient.mk _ (p x)) =
    ℓf ((I.T.level n).σP (Ideal.Quotient.mk _ x)))
  (φ1 : I.C1 →+* I'.C1) (hφc : ∀ c, φc (I.ι₀ c) = I'.ι₀ (φ1 c))
  (ℓb : Localization.Away (algebraMap I.Bs I.C1 I.bbar) →+*
    Localization.Away (algebraMap I'.Bs I'.C1 I'.bbar))
  (hℓb : ∀ c, ℓb (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
  (hσE : ∀ x, (letI := NodeEtaleGlue.algC1 I'.B I'.qB I'.C1 n
      I'.σE n (Ideal.Quotient.mk _ (e x))) =
    ℓb (letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n; I.σE n (Ideal.Quotient.mk _ x)))

include hβJ hβa heβ hgp hpβ hℓf hp hφc hℓb hσE in
/-- **The overlap condition `hg` of `Input.yMap`** from the special fibres: if the first component
of `g` is a map `p` of the étale parts reducing to a map `φc` of the special-fibre coverings of
the node charts, `e` reduces to `φ1 : C1 → C1'`, and `φc ∘ ι₀ = ι₀' ∘ φ1`, then
`ρa0' ∘ g = eab ∘ ρa0`. -/
theorem hg_of_special (x : I.T.G hθ n) :
    ρa0 I'.T hθ I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha I'.hι I'.E I'.σE
      I'.hbE I'.hdiv I'.hJB I'.B0 n (g x) =
    I.eab I' n e he (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hJB I.B0 n x) := by
  letI := algBP I.T I.B n
  haveI := towerBP I.T I.B n
  letI := algBC I.T I.B n
  haveI := towerBC I.T I.B n
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  letI := algBP I'.T I'.B n
  haveI := towerBP I'.T I'.B n
  letI := algBC I'.T I'.B n
  haveI := towerBC I'.T I'.B n
  letI := NodeEtaleGlue.algC1 I'.B I'.qB I'.C1 n
  change κn I'.T I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha I'.hι I'.E I'.σE I'.hbE
      I'.hdiv I'.hJB n (fstP I'.T hθ n (g x)) =
    I.eab I' n e he (κn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hJB n (fstP I.T hθ n x))
  rw [hgp]
  exact OverlapFibre.κ_map (J θ (R := I.B n)) (I.a n) (I.b n)
    (isLocalization_ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.ha I.hι n) (I.hbE n) (I.hdiv n)
    (J θ (R := I'.B n)) (I'.a n) (I'.b n)
    (isLocalization_ιn I'.T I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.ha I'.hι n) (I'.hbE n)
    (I'.hdiv n) β hβJ hβa e heβ φ1 ℓb hℓb hσE φc hφc ℓf hℓf (I.hJB n) (I'.hJB n) p hpβ hp _

omit [Field k] in
lemma mk_injective_bot {X : Type u} [CommRing X] {I₀ : Ideal X} (h : I₀ = ⊥) :
    Function.Injective (Ideal.Quotient.mk I₀) := by
  subst h
  intro a b hab
  rwa [Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at hab

variable (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (hJ0 : J θ (R := I.B n) = ⊥)
  (hJ0' : J θ (R := I'.B n) = ⊥)

include hp hℓf hJ0' in
/-- At a level with `J = 0`, `p` is `φc` on the identifications `C[1/f] ≃ P`. -/
lemma p_toP (x : Cc I.T n) :
    p (FormalPatchLevel.toP (I.J_R_eq_bot hJ0) (I.T.f n) (I.T.level n).σP x) =
      FormalPatchLevel.toP (I'.J_R_eq_bot hJ0') (I'.T.f n) (I'.T.level n).σP (φc x) := by
  have hb : (J θ (R := I'.R n)).map (algebraMap (I'.R n) (I'.T.level n).P) = ⊥ := by
    rw [I'.J_R_eq_bot hJ0', Ideal.map_bot]
  apply mk_injective_bot hb
  apply (I'.T.level n).σP.injective
  rw [hp, FormalPatchLevel.mk_toP, FormalPatchLevel.mk_toP, hℓf]

include hgp hp hℓf hφc hℓb hσE in
/-- **At a level with `J = 0`, `yMap` is `φ1` on the identifications `yEquiv : C1 ≃ Y n`** (the
hypothesis `hyE` of `Overlap.yM_eq_mM`). -/
theorem yMap_yEquiv (hg : ∀ x, ρa0 I'.T hθ I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha
      I'.hι I'.E I'.σE I'.hbE I'.hdiv I'.hJB I'.B0 n (g x) =
    I.eab I' n e he (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hJB I.B0 n x)) (c : I.C1) :
    I.yMap I' hθ n g e he hg (I.yEquiv hθ hO hJ0 c) = I'.yEquiv hθ hO hJ0' (φ1 c) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change g (I.φG hθ hO hJ0 c) = I'.φG hθ hO hJ0' (φ1 c)
    refine FormalGlueing.eq_of_fst_eq (f := I'.T.f n) (NFall (I'.T.level n).L (I'.T.level n).M) _
      (noTorsion_NFall (I'.T.level n).L (I'.T.level n).M (I'.T.level n).hflat
        (I'.T.level n).hidem (I'.T.level n).hfχ (I'.T.level n).hcidem (I'.T.level n).hreg) ?_
    change fstP I'.T hθ n (g (I.φG hθ hO hJ0 c)) = fstP I'.T hθ n (I'.φG hθ hO hJ0' (φ1 c))
    rw [hgp]
    change p (FormalPatchLevel.toP (I.J_R_eq_bot hJ0) (I.T.f n) (I.T.level n).σP (I.ι₀ c)) =
      FormalPatchLevel.toP (I'.J_R_eq_bot hJ0') (I'.T.f n) (I'.T.level n).σP (I'.ι₀ (φ1 c))
    rw [p_toP I I' n p φc ℓf hℓf hp hJ0 hJ0', hφc]
  · change e (I.φE hJ0 c) = I'.φE hJ0' (φ1 c)
    letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    letI := NodeEtaleGlue.algC1 I'.B I'.qB I'.C1 n
    have hb : EtaleNil.JB (J θ (R := I'.B n)) (I'.E n) = ⊥ := by
      rw [EtaleNil.JB, hJ0', Ideal.map_bot]
    apply mk_injective_bot hb
    apply (I'.σE n).injective
    rw [hσE, mk_φE, mk_φE, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hℓb]

end Input

namespace Overlap

variable {I : Input θ cov₀ πL} {I' : Input θ cov₀' πL'} (V : Overlap I) (V' : Overlap I')
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **At the bottom level the restriction to the overlap is `γM`** (`Input.mk_ψ_yEquiv`). -/
lemma mk_ψ_yEquiv {n : ℕ} (hJ0 : J θ (R := I.B n) = ⊥) (c : I.C1) :
    Ideal.Quotient.mk (letI := V.algBM n; EtaleNil.JB (J θ (R := I.B n)) (V.M n))
      (V.ψ hθ hO n (I.yEquiv hθ hO hJ0 c)) = V.γM n c := by
  letI := V.algBM n
  letI := V.alg0M n
  haveI := V.formallyEtale_M n
  haveI := V.tower0M n
  exact I.mk_ψ_yEquiv hθ hO n V.g (V.hfg n) (V.γM n) (V.isLocalization_γM n) hJ0 c

/-- `mM p` is `O`-linear if `p` is. -/
lemma mM_algebraMapO {n : ℕ} (p : V.P0.P n →+* V'.P0.P n)
    (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ o : O, p (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o) (o : O) :
    V.mM V' n p hp0 (algebraMap O (V.M n) o) = algebraMap O (V'.M n) o := by
  rw [IsScalarTower.algebraMap_apply O (V.P0.P n) (V.M n), mM_algebraMap, hpO,
    ← IsScalarTower.algebraMap_apply]

/-- `mM p` on the overlap `W n` (through which `M n` is a `B n`-algebra): if `p` is semilinear over
`βB : B' n → B'' n` and `βW : W n → W' n` extends `βB`, then `mM p` extends `βW`. -/
lemma mM_algebraMapW {n : ℕ} (p : V.P0.P n →+* V'.P0.P n)
    (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (βB : V.B' n →+* V'.B' n)
    (hpB : ∀ y, p (algebraMap (V.B' n) (V.P0.P n) y) = algebraMap (V'.B' n) (V'.P0.P n) (βB y))
    (βW : V.W n →+* V'.W n)
    (hβW : ∀ y, βW (algebraMap (V.B' n) (V.W n) y) = algebraMap (V'.B' n) (V'.W n) (βB y))
    (w : V.W n) :
    V.mM V' n p hp0 (letI := V.algWM n; algebraMap (V.W n) (V.M n) w) =
      (letI := V'.algWM n; algebraMap (V'.W n) (V'.M n) (βW w)) := by
  letI := V.algWM n
  letI := V'.algWM n
  haveI := V.hWn0 n
  have h := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap V.B0' (V.B' n) V.x0))
    (S := V.W n) (j := (V.mM V' n p hp0).comp (algebraMap (V.W n) (V.M n)))
    (k := (algebraMap (V'.W n) (V'.M n)).comp βW) (RingHom.ext fun y ↦ by
      simp only [RingHom.comp_apply]
      rw [OverlapPiece.algWM_algebraMap, hβW, OverlapPiece.algWM_algebraMap,
        IsScalarTower.algebraMap_apply (V.B' n) (V.P0.P n) (V.M n), mM_algebraMap, hpB,
        ← IsScalarTower.algebraMap_apply])
  exact RingHom.congr_fun h w

/-- **`mM p` is semilinear over a map `β0` of the first charts** (the hypothesis `hpB` of
`yM_eq_mM`) if `p` is semilinear over `βB` and `βW` extends `βB` and `β0`. -/
lemma mM_algebraMap0 {n : ℕ} (p : V.P0.P n →+* V'.P0.P n)
    (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (βB : V.B' n →+* V'.B' n)
    (hpB : ∀ y, p (algebraMap (V.B' n) (V.P0.P n) y) = algebraMap (V'.B' n) (V'.P0.P n) (βB y))
    (βW : V.W n →+* V'.W n)
    (hβW : ∀ y, βW (algebraMap (V.B' n) (V.W n) y) = algebraMap (V'.B' n) (V'.W n) (βB y))
    (β0 : I.B0 →+* I'.B0)
    (hβW0 : ∀ b, βW (algebraMap (I.B n) (V.W n) (algebraMap I.B0 (I.B n) b)) =
      algebraMap (I'.B n) (V'.W n) (algebraMap I'.B0 (I'.B n) (β0 b)))
    (b : I.B0) :
    V.mM V' n p hp0 (letI := V.alg0M n; algebraMap I.B0 (V.M n) b) =
      (letI := V'.alg0M n; algebraMap I'.B0 (V'.M n) (β0 b)) := by
  change V.mM V' n p hp0 (letI := V.algWM n; algebraMap (V.W n) (V.M n)
      (algebraMap (I.B n) (V.W n) (algebraMap I.B0 (I.B n) b))) =
    (letI := V'.algWM n; algebraMap (V'.W n) (V'.M n)
      (algebraMap (I'.B n) (V'.W n) (algebraMap I'.B0 (I'.B n) (β0 b))))
  rw [V.mM_algebraMapW V' p hp0 βB hpB βW hβW, hβW0]

/-- **`mM p` reduces to `φ1` through `γM`** if `p` reduces to `φ0` through `ℓ0` and `φ0`, `φ1` are
compatible with the chart descriptions `ω`, `ω'` (the hypothesis `hpγ` of `yM_eq_mM`). -/
theorem mk_mM_γM {n : ℕ} (p : V.P0.P n →+* V'.P0.P n)
    (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ o : O, p (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
    (φ0 : V.C0 →+* V'.C0)
    (hpℓ : ∀ c m, Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V.B' n)) (V.M n)) m = V.P0.ℓ0 n c →
      Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V'.B' n)) (V'.M n)) (V.mM V' n p hp0 m) =
        V'.P0.ℓ0 n (φ0 c))
    (Lx0 : Localization.Away (algebraMap V.Bs' V.C0 V.x0s) →+*
      Localization.Away (algebraMap V'.Bs' V'.C0 V'.x0s))
    (hLx0 : ∀ c, Lx0 (algebraMap V.C0 _ c) = algebraMap V'.C0 _ (φ0 c))
    (φ1 : I.C1 →+* I'.C1)
    (Lx1 : Localization.Away (algebraMap I.Bs I.C1 V.x1s) →+*
      Localization.Away (algebraMap I'.Bs I'.C1 V'.x1s))
    (hLx1 : ∀ c, Lx1 (algebraMap I.C1 _ c) = algebraMap I'.C1 _ (φ1 c))
    (hω : ∀ z, V'.ω (Lx0 z) = Lx1 (V.ω z)) (c : I.C1) (m : V.M n)
    (hm : Ideal.Quotient.mk (letI := V.algBM n; EtaleNil.JB (J θ (R := I.B n)) (V.M n)) m =
      V.γM n c) :
    Ideal.Quotient.mk (letI := V'.algBM n; EtaleNil.JB (J θ (R := I'.B n)) (V'.M n))
      (V.mM V' n p hp0 m) = V'.γM n (φ1 c) := by
  letI := V.algBM n
  letI := V'.algBM n
  have e := OverlapPiece.JB_eq (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n)
    (V.P0.P n) (Bn := I.B n)
  have e' := OverlapPiece.JB_eq (RingHom.ker θ) (algebraMap V'.B0' (V'.B' n) V'.x0) (V'.hWn0 n)
    (V'.P0.P n) (Bn := I'.B n)
  have hm' : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V.B' n)) (V.M n)) m =
      OverlapPiece.γ0 (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0) (V.P0.P n) V.x1s V.x0s
        V.c0s V.ω (V.P0.ℓ0 n) (V.P0.hℓ0loc n) c := by
    apply (Ideal.quotEquivOfEq e).injective
    rw [Ideal.quotEquivOfEq_mk]
    exact hm
  have h := OverlapPiece.γ0_map (RingHom.ker θ) (V.P0.hℓ0loc n) (V'.P0.hℓ0loc n)
    (V.mM V' n p hp0) (V.mM_algebraMapO V' p hp0 hpO) φ0 hpℓ Lx0 hLx0 φ1 Lx1 hLx1 hω c m hm'
  change _ = Ideal.quotEquivOfEq e' (OverlapPiece.γ0 (RingHom.ker θ)
    (algebraMap V'.B0' (V'.B' n) V'.x0) (V'.P0.P n) V'.x1s V'.x0s V'.c0s V'.ω (V'.P0.ℓ0 n)
    (V'.P0.hℓ0loc n) (φ1 c))
  rw [← h, Ideal.quotEquivOfEq_mk]

section Single

variable (n : ℕ) (y : I.Y hθ n →+* I'.Y hθ n)
  (hyg : y (algebraMap I.B0 (I.Y hθ n) V.g) = algebraMap I'.B0 (I'.Y hθ n) V'.g)

include hyg in
lemma isUnit_yM : IsUnit (((V'.ψ hθ hO n : I'.Y hθ n →+* V'.M n).comp y)
    (algebraMap I.B0 (I.Y hθ n) V.g)) := by
  rw [RingHom.comp_apply, hyg]
  letI := V'.alg0M n
  letI := (V'.ψ hθ hO n).toRingHom.toAlgebra
  haveI := V'.isLocalization_ψ hθ hO n
  exact IsLocalization.Away.algebraMap_isUnit (algebraMap I'.B0 (I'.Y hθ n) V'.g)

include hyg in
/-- **The map `M n = Y n[1/g] → M' n` extending `ψ' ∘ y`.** -/
def yM : V.M n →+* V'.M n :=
  letI := V.alg0M n
  letI := (V.ψ hθ hO n).toRingHom.toAlgebra
  haveI := V.isLocalization_ψ hθ hO n
  IsLocalization.Away.lift (algebraMap I.B0 (I.Y hθ n) V.g) (V.isUnit_yM V' hθ hO n y hyg)

lemma yM_ψ (z : I.Y hθ n) : V.yM V' hθ hO n y hyg (V.ψ hθ hO n z) = V'.ψ hθ hO n (y z) :=
  letI := V.alg0M n
  letI := (V.ψ hθ hO n).toRingHom.toAlgebra
  haveI := V.isLocalization_ψ hθ hO n
  IsLocalization.Away.lift_eq _ (V.isUnit_yM V' hθ hO n y hyg) z

/-- Ring maps out of `M n = Y n[1/g]` are determined on `Y n`. -/
lemma M_ext {Z : Type*} [CommRing Z] {u v : V.M n →+* Z}
    (h : ∀ z, u (V.ψ hθ hO n z) = v (V.ψ hθ hO n z)) : u = v := by
  letI := V.alg0M n
  letI := (V.ψ hθ hO n).toRingHom.toAlgebra
  haveI := V.isLocalization_ψ hθ hO n
  exact IsLocalization.ringHom_ext (Submonoid.powers (algebraMap I.B0 (I.Y hθ n) V.g))
    (RingHom.ext h)

end Single

variable (n : ℕ) (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
  (hyg : ∀ n, y n (algebraMap I.B0 (I.Y hθ n) V.g) = algebraMap I'.B0 (I'.Y hθ n) V'.g)
  (hyS : ∀ n z, I'.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z))
  (p : ∀ n, V.P0.P n →+* V'.P0.P n)
  (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
    algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
  (hpS : ∀ n e, V'.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e))

include hyS in
/-- `yM` commutes with the successor maps. -/
lemma sM_yM (m : V.M (n + 1)) :
    V'.sM n (V.yM V' hθ hO (n + 1) (y (n + 1)) (hyg (n + 1)) m) =
      V.yM V' hθ hO n (y n) (hyg n) (V.sM n m) := by
  have h := V.M_ext hθ hO (n + 1)
    (u := (V'.sM n).comp (V.yM V' hθ hO (n + 1) (y (n + 1)) (hyg (n + 1))))
    (v := (V.yM V' hθ hO n (y n) (hyg n)).comp (V.sM n)) fun z ↦ by
      simp only [RingHom.comp_apply]
      rw [yM_ψ, V'.ψ_succ, hyS, V.ψ_succ, yM_ψ]
  exact RingHom.congr_fun h m

include hpS in
/-- `mM p` commutes with the successor maps. -/
lemma sM_mM (m : V.M (n + 1)) :
    V'.sM n (V.mM V' (n + 1) (p (n + 1)) (hp0 (n + 1)) m) =
      V.mM V' n (p n) (hp0 n) (V.sM n m) := by
  have h := IsLocalization.ringHom_ext (Submonoid.powers
      (algebraMap (V.B' (n + 1)) (V.P0.P (n + 1)) (algebraMap V.B0' (V.B' (n + 1)) V.x0)))
    (j := (V'.sM n).comp (V.mM V' (n + 1) (p (n + 1)) (hp0 (n + 1))))
    (k := (V.mM V' n (p n) (hp0 n)).comp (V.sM n)) (RingHom.ext fun e ↦ by
      simp only [RingHom.comp_apply]
      rw [mM_algebraMap, V'.sM_algebraMap, hpS, sM_algebraMap, mM_algebraMap])
  exact RingHom.congr_fun h m

variable (β0 : I.B0 →+* I'.B0)
  (hyB : ∀ n b, y n (algebraMap I.B0 (I.Y hθ n) b) = algebraMap I'.B0 (I'.Y hθ n) (β0 b))
  (hpB : ∀ n b, V.mM V' n (p n) (hp0 n) (letI := V.alg0M n; algebraMap I.B0 (V.M n) b) =
    (letI := V'.alg0M n; algebraMap I'.B0 (V'.M n) (β0 b)))
  (hJ0 : J θ (R := I.B 0) = ⊥) (hJ0' : J θ (R := I'.B 0) = ⊥) (φ1 : I.C1 →+* I'.C1)
  (hyE : ∀ c, y 0 (I.yEquiv hθ hO hJ0 c) = I'.yEquiv hθ hO hJ0' (φ1 c))
  (hpγ : ∀ c m, Ideal.Quotient.mk (letI := V.algBM 0; EtaleNil.JB (J θ (R := I.B 0)) (V.M 0)) m =
      V.γM 0 c →
    Ideal.Quotient.mk (letI := V'.algBM 0; EtaleNil.JB (J θ (R := I'.B 0)) (V'.M 0))
      (V.mM V' 0 (p 0) (hp0 0) m) = V'.γM 0 (φ1 c))

/-- `ϖⁿ⁺¹ M (n+1)` is nilpotent. -/
lemma isNilpotent_pow (n : ℕ) :
    IsNilpotent ((Ideal.span {V'.ϖ} ^ (n + 1)).map (algebraMap O (V'.M (n + 1)))) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [← Ideal.map_pow, ← pow_mul]
  calc ((Ideal.span {V'.ϖ}) ^ ((n + 1) * 2)).map (algebraMap O (V'.M (n + 1)))
      ≤ ((Ideal.span {V'.ϖ}) ^ (n + 1 + 1)).map (algebraMap O (V'.M (n + 1))) :=
        Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
    _ = ⊥ := by
        rw [IsScalarTower.algebraMap_eq O (V'.P0.P (n + 1)) (V'.M (n + 1)),
          IsScalarTower.algebraMap_eq O (V'.B' (n + 1)) (V'.P0.P (n + 1)), ← Ideal.map_map,
          ← Ideal.map_map, V'.killB', Ideal.map_bot, Ideal.map_bot]

include hyS hpS hyB hpB hyE hpγ in
/-- **`yM = mM p` at every level**, from the bottom level (induction with the uniqueness of maps
out of the formally unramified `M (n+1)` into the square-zero thickening `M' (n+1)` of `M' n`). -/
theorem yM_eq_mM (n : ℕ) : V.yM V' hθ hO n (y n) (hyg n) = V.mM V' n (p n) (hp0 n) := by
  induction n with
  | zero =>
    refine V.M_ext hθ hO 0 fun z ↦ ?_
    letI := I.algC10 0
    obtain ⟨c, rfl⟩ := (I.yEquiv hθ hO hJ0).surjective z
    rw [yM_ψ, hyE]
    letI := V'.algBM 0
    apply I'.mk_injective_of_eq_bot 0 hJ0' (V'.M 0)
    rw [V'.mk_ψ_yEquiv hθ hO hJ0' (φ1 c)]
    exact (hpγ c _ (V.mk_ψ_yEquiv hθ hO hJ0 c)).symm
  | succ n ih =>
    letI := V.algBM (n + 1)
    letI := V.alg0M (n + 1)
    haveI := V.formallyEtale_M (n + 1)
    haveI := V.tower0M (n + 1)
    haveI : Algebra.FormallyUnramified I.B0 (I.B (n + 1)) :=
      Algebra.FormallyUnramified.of_surjective (Algebra.ofId I.B0 (I.B (n + 1))) (V.surjB (n + 1))
    haveI : Algebra.FormallyUnramified I.B0 (V.M (n + 1)) :=
      Algebra.FormallyUnramified.comp I.B0 (I.B (n + 1)) (V.M (n + 1))
    letI := V'.alg0M (n + 1)
    refine OverlapFibre.eq_of_semilinear β0 (isNilpotent_pow V' n) _ _ (fun b ↦ ?_)
      (fun b ↦ hpB (n + 1) b) (fun x ↦ ?_)
    · rw [← (V.ψ hθ hO (n + 1)).commutes b, yM_ψ, hyB, AlgHom.commutes]
    · rw [Ideal.Quotient.eq]
      apply Piece0.ker_sM_le V'.P0 n
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      change V'.sM n _ = V'.sM n _
      rw [sM_yM V V' hθ hO n y hyg hyS, sM_mM V V' n p hp0 hpS, ih]

include hyS hpS hyB hpB hyE hpγ hyg in
/-- **The overlap condition `hψ` of `Overlap.twoChartMap` from the bottom level.** -/
theorem hψ_of_bottom (n : ℕ) (z : I.Y hθ n) :
    V'.ψ hθ hO n (y n z) = V.mM V' n (p n) (hp0 n) (V.ψ hθ hO n z) := by
  rw [← V.yM_eq_mM V' hθ hO y hyg hyS p hp0 hpS β0 hyB hpB hJ0 hJ0' φ1 hyE hpγ n, yM_ψ]

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
