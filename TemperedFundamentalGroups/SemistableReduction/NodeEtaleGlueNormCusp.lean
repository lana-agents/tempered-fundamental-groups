/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueNormLevels
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelEquivP

/-!
# The algebraization of a covering with the patch over `D(c₀)` from cusp level data (MR12 T2 S6, G5)

For a covering `V : NodeEtaleGlue.Overlap I` whose piece over `D(c₀)` is the piece of a patch `Dp`
with cusp level data `Vc` (as in `NodeEtaleGlueV0LevelEquivP`), two-chart rings `P` over `O` and
families of level data:

* over `V₁`: `X1 n` with identifications `e1 : I.LevelEquivFam …` (`X1 n ≃ Y n`, a tower);
* over `V₀`: `X0 n` with overlap identifications `ωn n`, localizations `t n : X0 n → Dp.R n ⊗ B`
  and reductions, forming a tower (`μ0`, `hμt`) with common witnesses (`hω2`);
* reductions `q0 n : P.R0 → X0 n`, `q1 n : P.R1 → X1 n` (surjective, kernels `ϖⁿ⁺¹`) compatible with
  `μ0`, `μ1`, and witnesses `hW` of `ωn` on the overlap of `P`,

**`NodeEtaleGlue.Overlap.exists_iso_of_cuspLevels`**: every algebraization of the covering is
isomorphic to `P` as a chart algebra (`exists_iso_of_levels'` with `e0 n = levelEquiv0P …`, the
tower property from `f0_levelEquiv0P`, and `hρ` from `φQn_mul_pow`);
**`exists_iso_of_cuspLevelsW`**: the same with the common witnesses of consecutive levels
obtained from `hW`.
-/

universe u

open TensorProduct Polynomial ProjectiveLine ProjectiveLine.ChartModule

namespace SemistableReduction

namespace NodeEtaleGlue

namespace Overlap

noncomputable section

open FormalKummer AdmissibleLift FormalLevel FormalCuspLevel

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)]
  {R₁ : Type u} [CommRing R₁] [Algebra k R₁] {f₁ : R₁}
  {φ₁ : Node k (0 : k) →ₐ[k] Admissible.Hat f₁} {ψ₁ : Polynomial k →ₐ[k] Admissible.Hat f₁}
  {cov₁ : Admissible.Covering φ₁ ψ₁} {πL₁ : cov₁.ι → O}
  {I : Input θ cov₁ πL₁} (V : Overlap I) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {𝔪 : ι → Ideal R} [∀ j, (𝔪 j).IsMaximal]
  {hJ : ∀ j, J θ (R := R) ≤ 𝔪 j} {s : R} {E : ι → ℕ}
  {D : ∀ j, PointCuspFormData (θ := θ) (B := B) s (E j) (𝔪 j)} {g : R}
  {hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j)}
  {hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j)}
  {hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g)}
  {ψk : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g)}
  {hψ : ψk Polynomial.X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s)}
  {hfin : Module.Finite (Rs θ R) (Cs θ R B)}
  {het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale}
  {hk : ∀ j i, ((D j).d i : k) ≠ 0}
  {πL : (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk).ι → O}
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]
  (Dp : PatchInput θ V.B' V.qB' V.C0 V.x0 V.c0 V.x0s V.c0s V.ϖ
    (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL)
  [algRI : ∀ l, Algebra R (Dp.R l)] [towerORI : ∀ l, IsScalarTower O R (Dp.R l)]
  [towerRII : ∀ l, IsScalarTower R (Dp.R (l + 1)) (Dp.R l)]
  {T' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    LevelTower.Data (θ := θ) Dp.R (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL}
  {he : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ l (r : R), T'.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Dp.R l) r)}
  (Vc : CuspLevels 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T' he)
  (hkI : (fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)) = Dp.algkR) (hT : HEq T' Dp.T)


variable (hP0 : V.P0 = Dp.piece hθ.out hO) (P : TwoChartRings O)
  {X1 : ℕ → Type u} [∀ n, CommRing (X1 n)] [∀ n, Algebra I.B0 (X1 n)] [∀ n, Algebra (I.B n) (X1 n)]
  {μ1 : ∀ n, X1 (n + 1) →+* X1 n} (e1 : I.LevelEquivFam hθ.out hO X1 μ1)
  {X0 : ℕ → Type u} [∀ n, CommRing (X0 n)] [∀ n, Algebra V.B0' (X0 n)]
  (μ0 : ∀ n, X0 (n + 1) →+* X0 n)
  (ωn : ∀ n, haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0 n) V.x0
    letI := awayAlg (W := V.W0) (C := X1 n) V.x1
    Localization.Away (algebraMap V.B0' (X0 n) V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 (X1 n) V.x1))
  (t : ∀ n, X0 n →+* Dp.R n ⊗[R] B)
  (ht : ∀ n r, t n (algebraMap V.B0' (X0 n) r) = algebraMap (Dp.R n) (Dp.R n ⊗[R] B)
    (algebraMap (V.B' n) (Dp.R n) (algebraMap V.B0' (V.B' n) r)))
  (htloc : ∀ n, letI := (t n).toAlgebra
    IsLocalization.Away (algebraMap V.B0' (X0 n) V.c0) (Dp.R n ⊗[R] B))
  (ρX1 : ∀ n, letI := algC1 I.B I.qB I.C1 n; X1 n →ₐ[I.B n] I.C1) (ρX0 : ∀ n, X0 n →+* V.C0)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ n x, ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T'.hfe he n (t n x) =
      Dp.ι₀ (ρX0 n x))
  {mJ : ℕ → ℕ} (hJm : ∀ n, J θ (R := V.B' n) ^ mJ n = ⊥)
  (hψ1 : ∀ n y, (letI := V.algBM n; Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (V.M n))
    (V.ψ hθ.out hO n (e1.equiv n y))) = V.γM n (ρX1 n y))
  (hx1 : ∀ n, ρX1 n (algebraMap I.B0 (X1 n) V.x1) = algebraMap I.Bs I.C1 V.x1s)
  (hω : ∀ n (x : X0 n), ∃ (y : X1 n) (k : ℕ),
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0 n) V.x0
      letI := awayAlg (W := V.W0) (C := X1 n) V.x1
      ωn n (algebraMap (X0 n) _ x) *
        algebraMap (X1 n) (Localization.Away (algebraMap I.B0 (X1 n) V.x1))
          (algebraMap I.B0 (X1 n) V.x1) ^ k = algebraMap (X1 n) _ y) ∧
    V.ω (algebraMap V.C0 _ (ρX0 n x)) *
        algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
          (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1 n y))

/-- **The identifications over `V₀`**: `X0 n ≃ₐ[B0'] Q n ×_{M n} P0 n` (`levelEquiv0P`). -/
abbrev e0Cusp (n : ℕ) : letI := V.alg0'Q hθ.out n; letI := V.alg0'E n; letI := V.alg0'M n
    X0 n ≃ₐ[V.B0'] ZariskiTwo.glued (V.ρ0a hθ.out hO n) (V.ρ0b n) :=
  V.levelEquiv0P hO Dp Vc hkI hT hP0 n (e1.equiv n) (ωn n) (t n) (ht n) (htloc n) (ρX1 n) (ρX0 n)
    (hρ n) (hJm n) (hψ1 n) (hx1 n) (hω n)

variable (q0 : ∀ n, P.R0 →+* X0 n)
  (hq0O : ∀ n o, q0 n (algebraMap O P.R0 o) = algebraMap V.B0' (X0 n) (algebraMap O V.B0' o))
  (q1 : ∀ n, P.R1 →+* X1 n)
  (hq1O : ∀ n o, q1 n (algebraMap O P.R1 o) =
    algebraMap I.B0 (X1 n) (letI := V.algOB0; algebraMap O I.B0 o))
  (hx : ∀ n, q0 n P.x = algebraMap V.B0' (X0 n) V.x0)
  (hy : ∀ n, q1 n P.y = algebraMap I.B0 (X1 n) V.x1)
  (hW : ∀ n a m (k : ℕ), P.ρ0 a * P.ρ1 P.y ^ k = P.ρ1 m →
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0 n) V.x0
      letI := awayAlg (W := V.W0) (C := X1 n) V.x1
      ωn n (algebraMap (X0 n) _ (q0 n a)) *
        algebraMap (X1 n) (Localization.Away (algebraMap I.B0 (X1 n) V.x1))
          (algebraMap I.B0 (X1 n) V.x1) ^ k = algebraMap (X1 n) _ (q1 n m)))

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
include hW in
/-- The hypothesis `hρ` of `βOf` for `e0Cusp` from witnesses of `ωn` on the overlap of `P`. -/
theorem hρ_e0Cusp (n : ℕ) (a : P.R0) (m : P.R1) (k : ℕ) (h : P.ρ0 a * P.ρ1 P.y ^ k = P.ρ1 m) :
    (V.twoChart hθ.out hO n).ρ0 (V.f0Of hθ.out hO P (V.e0Cusp hO Dp Vc hkI hT hP0 e1 ωn t ht htloc
      ρX1 ρX0 hρ hJm hψ1 hx1 hω) q0 hq0O n a) *
        (V.twoChart hθ.out hO n).ρ1 (V.twoChart hθ.out hO n).y ^ k =
      (V.twoChart hθ.out hO n).ρ1 (V.f1Of hθ.out hO P e1 q1 hq1O n m) :=
  V.hρ_of_fst hθ.out hO P e1 q1 hq1O _ q0 hq0O (fun n a m k h ↦
    V.φQn_mul_pow hθ.out n (e1.equiv n) (ωn n) (q0 n a) (q1 n m) k (hW n a m k h)) n a m k h

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
include Vc hkI hT hP0 e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0 hq0O q1 hq1O hx hy hW in
/-- **G5 with the patch over `D(c₀)` from cusp level data: the covering is the algebraization of
`P`**: every algebraization `(N, BN, α)` of a system `S = V.system` is isomorphic to `P` as a chart
algebra, given level identifications over `V₁` (`e1`) and level data over `V₀` forming towers,
reductions `q0`, `q1` of `P` (surjective, kernels `ϖⁿ⁺¹`, compatible with the towers) and
witnesses `hW` of the overlap identifications on the overlap of `P`. -/
theorem exists_iso_of_cuspLevels [IsNoetherianRing O] [IsAdicComplete (Ideal.span {V.ϖ}) O]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
    (hμt : ∀ n x, t n (μ0 n x) = levelMap Dp.R n (t (n + 1) x))
    (hω2 : ∀ n (x : X0 (n + 1)), ∃ (y : X1 (n + 1)) (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0 (n + 1)) V.x0
        letI := awayAlg (W := V.W0) (C := X1 (n + 1)) V.x1
        ωn (n + 1) (algebraMap (X0 (n + 1)) _ x) *
          algebraMap (X1 (n + 1)) (Localization.Away (algebraMap I.B0 (X1 (n + 1)) V.x1))
            (algebraMap I.B0 (X1 (n + 1)) V.x1) ^ k = algebraMap (X1 (n + 1)) _ y) ∧
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0 n) V.x0
        letI := awayAlg (W := V.W0) (C := X1 n) V.x1
        ωn n (algebraMap (X0 n) _ (μ0 n x)) *
          algebraMap (X1 n) (Localization.Away (algebraMap I.B0 (X1 n) V.x1))
            (algebraMap I.B0 (X1 n) V.x1) ^ k = algebraMap (X1 n) _ (μ1 n y)))
    (hμ0 : ∀ n r, μ0 n (q0 (n + 1) r) = q0 n r) (hμ1 : ∀ n r, μ1 n (q1 (n + 1) r) = q1 n r)
    (hs0 : ∀ n, Function.Surjective (q0 n)) (hs1 : ∀ n, Function.Surjective (q1 n))
    (hk0 : ∀ n, RingHom.ker (q0 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R0))
    (hk1 : ∀ n, RingHom.ker (q1 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R1))
    {S : AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ.out hO = S)
    {N : ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)]
    {α : ∀ n, Hom N (S.M n)} {BN : AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m)
    (hBN : ∀ n, BN.IsHom (S.alg n) (α n)) :
    ∃ (γ : Hom P.chartModule N) (δ : Hom N P.chartModule), γ.comp δ = Hom.id N ∧
      δ.comp γ = Hom.id P.chartModule ∧ P.algStr.IsHom BN γ ∧ BN.IsHom P.algStr δ :=
  V.exists_iso_of_levels' hθ.out hO P e1 q1 hq1O
    (V.e0Cusp hO Dp Vc hkI hT hP0 e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω) q0 hq0O hx hy
    (V.hρ_e0Cusp hO Dp Vc hkI hT hP0 P e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0 hq0O q1 hq1O
      hW)
    (fun n x ↦ V.f0_levelEquiv0P hO Dp Vc hkI hT hP0 n (e1.equiv n) (ωn n) (t n) (ht n) (htloc n)
      (ρX1 n) (ρX0 n) (hρ n) (hJm n) (hψ1 n) (hx1 n) (hω n) (e1.equiv (n + 1)) (ωn (n + 1))
      (t (n + 1)) (ht (n + 1)) (htloc (n + 1)) (ρX1 (n + 1)) (ρX0 (n + 1)) (hρ (n + 1))
      (hJm (n + 1)) (hψ1 (n + 1)) (hx1 (n + 1)) (hω (n + 1)) (μ1 n) (μ0 n) (e1.succ n) (hμt n)
      (hω2 n) x)
    hμ0 hμ1 hs0 hs1 hk0 hk1 hS hα hαc hBN

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
include Vc hkI hT hP0 e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0 hq0O q1 hq1O hx hy hW in
/-- **`exists_iso_of_cuspLevels` with the common witnesses `hω2` from `hW`** (for `b ∈ P.R0` a
witness `ρ0 b · ρ1 yᵏ = ρ1 m` exists in every two-chart ring, `TwoChartRings.exists1`; `hW` at the
levels `n + 1` and `n` gives the witnesses of `ωn (n + 1)` and `ωn n`). -/
theorem exists_iso_of_cuspLevelsW [IsNoetherianRing O] [IsAdicComplete (Ideal.span {V.ϖ}) O]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
    (hμt : ∀ n x, t n (μ0 n x) = levelMap Dp.R n (t (n + 1) x))
    (hμ0 : ∀ n r, μ0 n (q0 (n + 1) r) = q0 n r) (hμ1 : ∀ n r, μ1 n (q1 (n + 1) r) = q1 n r)
    (hs0 : ∀ n, Function.Surjective (q0 n)) (hs1 : ∀ n, Function.Surjective (q1 n))
    (hk0 : ∀ n, RingHom.ker (q0 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R0))
    (hk1 : ∀ n, RingHom.ker (q1 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R1))
    {S : AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ.out hO = S)
    {N : ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)]
    {α : ∀ n, Hom N (S.M n)} {BN : AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m)
    (hBN : ∀ n, BN.IsHom (S.alg n) (α n)) :
    ∃ (γ : Hom P.chartModule N) (δ : Hom N P.chartModule), γ.comp δ = Hom.id N ∧
      δ.comp γ = Hom.id P.chartModule ∧ P.algStr.IsHom BN γ ∧ BN.IsHom P.algStr δ := by
  refine V.exists_iso_of_cuspLevels hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1
    hx1 hω q0 hq0O q1 hq1O hx hy hW hμt ?_ hμ0 hμ1 hs0 hs1 hk0 hk1 hS hα hαc hBN
  intro n x
  obtain ⟨b, rfl⟩ := hs0 (n + 1) x
  obtain ⟨m, k, h⟩ := P.exists1 (P.ρ0 b)
  have h' : P.ρ0 b * P.ρ1 P.y ^ k = P.ρ1 m := by rw [P.ρ1_y, mul_comm]; exact h
  refine ⟨q1 (n + 1) m, k, hW (n + 1) b m k h', ?_⟩
  rw [hμ0, hμ1]
  exact hW n b m k h'

/-! ### With the structure maps from a base model -/

variable {D : TwoChartRings O} (b : BaseMap V D) (ψP : TwoChartMap D P)
  (hq0B : ∀ n r, q0 n (ψP.f0 r) = algebraMap V.B0' (X0 n) (b.a0 r))
  (hq1B : ∀ n r, q1 n (ψP.f1 r) = algebraMap I.B0 (X1 n) (b.a1 r))

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
include Vc hkI hT hP0 e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0 hq0O q1 hq1O hx hy hW
  hq0B hq1B in
/-- **`exists_iso_of_cuspLevels` with the structure maps**: the isomorphism `γ : P ≅ N` sends the
structure map `ψP : D → P` to the structure map `ψ : D → N` of the algebraization (reducing to
the base maps `b.β n`). -/
theorem exists_iso_of_cuspLevels_base [IsNoetherianRing O]
    [IsAdicComplete (Ideal.span {V.ϖ}) O]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
    [Module.Finite O[X] (Module.AEval' D.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' D.chartModule.x1)]
    (hμt : ∀ n x, t n (μ0 n x) = levelMap Dp.R n (t (n + 1) x))
    (hω2 : ∀ n (x : X0 (n + 1)), ∃ (y : X1 (n + 1)) (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0 (n + 1)) V.x0
        letI := awayAlg (W := V.W0) (C := X1 (n + 1)) V.x1
        ωn (n + 1) (algebraMap (X0 (n + 1)) _ x) *
          algebraMap (X1 (n + 1)) (Localization.Away (algebraMap I.B0 (X1 (n + 1)) V.x1))
            (algebraMap I.B0 (X1 (n + 1)) V.x1) ^ k = algebraMap (X1 (n + 1)) _ y) ∧
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0 n) V.x0
        letI := awayAlg (W := V.W0) (C := X1 n) V.x1
        ωn n (algebraMap (X0 n) _ (μ0 n x)) *
          algebraMap (X1 n) (Localization.Away (algebraMap I.B0 (X1 n) V.x1))
            (algebraMap I.B0 (X1 n) V.x1) ^ k = algebraMap (X1 n) _ (μ1 n y)))
    (hμ0 : ∀ n r, μ0 n (q0 (n + 1) r) = q0 n r) (hμ1 : ∀ n r, μ1 n (q1 (n + 1) r) = q1 n r)
    (hs0 : ∀ n, Function.Surjective (q0 n)) (hs1 : ∀ n, Function.Surjective (q1 n))
    (hk0 : ∀ n, RingHom.ker (q0 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R0))
    (hk1 : ∀ n, RingHom.ker (q1 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R1))
    {S : AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ.out hO = S)
    {N : ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)]
    {α : ∀ n, Hom N (S.M n)} {BN : AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m)
    (hBN : ∀ n, BN.IsHom (S.alg n) (α n))
    {ψ : Hom D.chartModule N} (hψ : ∀ n, (α (n + 1)).comp ψ = b.βS hθ.out hO n hS) :
    ∃ (γ : Hom P.chartModule N) (δ : Hom N P.chartModule), γ.comp δ = Hom.id N ∧
      δ.comp γ = Hom.id P.chartModule ∧ P.algStr.IsHom BN γ ∧ BN.IsHom P.algStr δ ∧
      γ.comp ψP.toHom = ψ :=
  V.exists_iso_of_levels_base hθ.out hO P e1 q1 hq1O
    (V.e0Cusp hO Dp Vc hkI hT hP0 e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω) q0 hq0O hx hy
    (V.hρ_e0Cusp hO Dp Vc hkI hT hP0 P e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0 hq0O q1 hq1O
      hW)
    (fun n x ↦ V.f0_levelEquiv0P hO Dp Vc hkI hT hP0 n (e1.equiv n) (ωn n) (t n) (ht n) (htloc n)
      (ρX1 n) (ρX0 n) (hρ n) (hJm n) (hψ1 n) (hx1 n) (hω n) (e1.equiv (n + 1)) (ωn (n + 1))
      (t (n + 1)) (ht (n + 1)) (htloc (n + 1)) (ρX1 (n + 1)) (ρX0 (n + 1)) (hρ (n + 1))
      (hJm (n + 1)) (hψ1 (n + 1)) (hx1 (n + 1)) (hω (n + 1)) (μ1 n) (μ0 n) (e1.succ n) (hμt n)
      (hω2 n) x)
    hμ0 hμ1 b ψP hq0B hq1B hs0 hs1 hk0 hk1 hS hα hαc hBN hψ

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
include Vc hkI hT hP0 e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω q0 hq0O q1 hq1O hx hy hW
  hq0B hq1B in
/-- **`exists_iso_of_cuspLevelsW` with the structure maps**: the isomorphism `γ : P ≅ N` sends the
structure map `ψP : D → P` to the structure map `ψ : D → N` of the algebraization. -/
theorem exists_iso_of_cuspLevelsW_base [IsNoetherianRing O]
    [IsAdicComplete (Ideal.span {V.ϖ}) O]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' P.chartModule.x1)]
    [Module.Finite O[X] (Module.AEval' D.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' D.chartModule.x1)]
    (hμt : ∀ n x, t n (μ0 n x) = levelMap Dp.R n (t (n + 1) x))
    (hμ0 : ∀ n r, μ0 n (q0 (n + 1) r) = q0 n r) (hμ1 : ∀ n r, μ1 n (q1 (n + 1) r) = q1 n r)
    (hs0 : ∀ n, Function.Surjective (q0 n)) (hs1 : ∀ n, Function.Surjective (q1 n))
    (hk0 : ∀ n, RingHom.ker (q0 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R0))
    (hk1 : ∀ n, RingHom.ker (q1 n) = (Ideal.span {V.ϖ} ^ (n + 1)).map (algebraMap O P.R1))
    {S : AdicChartAlgSystem (Ideal.span {V.ϖ})} (hS : V.system hθ.out hO = S)
    {N : ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)]
    {α : ∀ n, Hom N (S.M n)} {BN : AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m)
    (hBN : ∀ n, BN.IsHom (S.alg n) (α n))
    {ψ : Hom D.chartModule N} (hψ : ∀ n, (α (n + 1)).comp ψ = b.βS hθ.out hO n hS) :
    ∃ (γ : Hom P.chartModule N) (δ : Hom N P.chartModule), γ.comp δ = Hom.id N ∧
      δ.comp γ = Hom.id P.chartModule ∧ P.algStr.IsHom BN γ ∧ BN.IsHom P.algStr δ ∧
      γ.comp ψP.toHom = ψ := by
  refine V.exists_iso_of_cuspLevels_base hO Dp Vc hkI hT hP0 P e1 μ0 ωn t ht htloc ρX1 ρX0 hρ
    hJm hψ1 hx1 hω q0 hq0O q1 hq1O hx hy hW b ψP hq0B hq1B hμt ?_ hμ0 hμ1 hs0 hs1 hk0 hk1 hS hα
    hαc hBN hψ
  intro n x
  obtain ⟨b', rfl⟩ := hs0 (n + 1) x
  obtain ⟨m, k, h⟩ := P.exists1 (P.ρ0 b')
  have h' : P.ρ0 b' * P.ρ1 P.y ^ k = P.ρ1 m := by rw [P.ρ1_y, mul_comm]; exact h
  refine ⟨q1 (n + 1) m, k, hW (n + 1) b' m k h', ?_⟩
  rw [hμ0, hμ1]
  exact hW n b' m k h'

end

end Overlap

end NodeEtaleGlue

end SemistableReduction
