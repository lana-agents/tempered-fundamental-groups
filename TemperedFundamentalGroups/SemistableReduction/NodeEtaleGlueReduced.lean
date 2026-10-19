/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Patch
import TemperedFundamentalGroups.SemistableReduction.EtaleTower
import TemperedFundamentalGroups.SemistableReduction.RegularPieces
import TemperedFundamentalGroups.SemistableReduction.ReducedFibreNormal
import TemperedFundamentalGroups.SemistableReduction.EtaleReduced

/-!
# Reducedness of the levels of a glued covering (Blueprint §12.8, M2.5 input)

The normalised-model statement `TwoChartTower.isIntegralClosure_shift0/1` needs the level-`0`
two-chart rings `(Overlap.twoChart 0).R0`, `.R1` to be reduced. Over a reduced special fibre of
the base charts this holds for every piece, without any smoothness input:

* **`isReduced_of_span_pow`**: a formally étale algebra over a reduced Noetherian ring, finitely
  generated as a module up to powers of an element inverted in it, is reduced (it is étale,
  `RegularPieces.finiteType_of_span_pow`, `EtaleReduced.isReduced_of_etale`): the étale lifts
  `E n`, `E0 n` (`EtaleTower.Lift.isReduced`) and the étale part `P` of the node patches;
* **`LevelTower.Level.isReduced_G`**, `Data.isReduced_G`: the patched algebra `G ⊆ P × NF` is
  reduced over a reduced chart: `f` is a nonzerodivisor on `G` (a unit on `P`, regular on `NF` by
  `AdmissibleLift.noTorsion_NFall`) and `G[1/f] = P` (`Level.spec`), so
  `isReduced_of_away` applies;
* `ZariskiTwo.isReduced_glued`: Zariski glueings of reduced pieces are reduced (subalgebras of
  the product);
* **`NodeEtaleGlue.Input.isReduced_Y`**: `Y n = G n ×_{E n[1/a]} E n` is reduced if the chart
  `B n` is reduced and Noetherian;
* `PatchInput.isReduced_piece`: the cusp/node patch over `D(c₀)` is reduced if `B' n` is;
* **`NodeEtaleGlue.Overlap.isReduced_twoChart`**: `(V.twoChart n).R0 = Q n ×_{M n} P0 n` and
  `(V.twoChart n).R1 = Y n` are reduced if `B n` is reduced and Noetherian and the piece
  `P0 n` over `D(c₀)` is reduced (`isReduced_R0`, `isReduced_R1`, `isReduced_R01`).

All statements are for an arbitrary level `n`; they apply at `n = 0`, where the charts are the
special fibres of the base charts (reduced for the Tate curve: `TateReduced`).
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift

section Etale

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]

/-- **A formally étale algebra over a reduced Noetherian ring, finitely generated as a module up
to powers of an element inverted in it, is reduced** (it is étale). -/
theorem isReduced_of_span_pow [IsNoetherianRing R] [IsReduced R] [Algebra.FormallyEtale R S]
    (b : R) (hb : IsUnit (algebraMap R S b)) (s : Finset S)
    (hs : ∀ p : S, ∃ k : ℕ, b ^ k • p ∈ Submodule.span R (s : Set S)) : IsReduced S := by
  haveI := RegularPieces.finiteType_of_span_pow b hb s hs
  haveI : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  haveI : Algebra.Etale R S := {}
  exact EtaleReduced.isReduced_of_etale R S

/-- Localizations of reduced rings are reduced. -/
theorem isReduced_of_isLocalization (M : Submonoid R) [IsLocalization M S] [IsReduced R] :
    IsReduced S :=
  isReduced_localizationPreserves M S ‹_›

end Etale

namespace EtaleTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {ϖ : O}
  {T : Type u} [CommRing T] [Algebra O T] [IsNoetherianRing T] {hϖ : θ ϖ = 0}
  {C : Type u} [CommRing C] [Algebra (Ts θ T) C] {b : T} {n : ℕ}

/-- **The étale lifts over a reduced level are reduced.** -/
theorem Lift.isReduced (L : Lift T hϖ C b n) [IsReduced (Tn ϖ T n)] : IsReduced L.E :=
  isReduced_of_span_pow _ L.hb L.hfin.choose L.hfin.choose_spec

end EtaleTower

namespace LevelTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

include hO in
/-- **The patched algebra over a reduced chart is reduced**: `G ↪ G[1/f] = P`, `P` étale over
`R n`. -/
theorem Level.isReduced_G {n : ℕ} (D : Level R cov₀ πL hfe n) [IsReduced (R n)] :
    IsReduced (D.G hθ) := by
  haveI : IsReduced D.P := isReduced_of_span_pow (f n) D.hfP D.hP.choose D.hP.choose_spec
  have hP : IsSMulRegular D.P (f n) :=
    (isSMulRegular_algebraMap_iff (A := D.P) (M := D.P)).mp (D.hfP.isSMulRegular _)
  have hN : IsSMulRegular (NFall D.L D.M) (f n) :=
    isSMulRegular_iff_right_eq_zero_of_smul.mpr fun x hx ↦
      noTorsion_NFall D.L D.M D.hflat D.hidem D.hfχ D.hcidem D.hreg x
        (by rwa [Algebra.smul_def] at hx)
  have hG : IsSMulRegular (D.G hθ) (f n) := RegularPieces.isSMulRegular_subalgebra_prod _ hP hN
  letI := FormalGlueing.algebraFst (NFall D.L D.M) (FormalPatchLevel.lift (f n) (J θ) D.hJ
        (FormalPatchLevel.alphaOfEquiv (f n) (J θ)
          (FormalPatchLevel.specialFibreEquiv (f n) (J θ) D.σP (kappaF D.L D.M hθ))))
  haveI := (Level.spec hθ hO D).2.1
  exact isReduced_of_away (L := D.P) (f := algebraMap (R n) (D.G hθ) (f n))
    (mem_nonZeroDivisors_iff_right.2 fun y hy ↦ hG (by
      change f n • y = f n • (0 : D.G hθ)
      rw [Algebra.smul_def, Algebra.smul_def, mul_zero, mul_comm, hy]))

variable [∀ n, Algebra (R (n + 1)) (R n)]

include hO in
/-- **The patched algebras of a tower over a reduced chart are reduced.** -/
theorem Data.isReduced_G (T : Data (θ := θ) R cov₀ πL) (n : ℕ) [IsReduced (R n)] :
    IsReduced (T.G hθ n) :=
  Level.isReduced_G hθ hO (T.level n)

end LevelTower

section Glued

variable {R : Type u} [CommRing R] {Ba Bb Bab : Type u} [CommRing Ba] [CommRing Bb]
  [CommRing Bab]
  [Algebra R Ba] [Algebra R Bb] [Algebra R Bab] (ρa : Ba →ₐ[R] Bab) (ρb : Bb →ₐ[R] Bab)

/-- **A Zariski glueing of reduced pieces is reduced.** -/
theorem _root_.ZariskiTwo.isReduced_glued [IsReduced Ba] [IsReduced Bb] :
    IsReduced (ZariskiTwo.glued ρa ρb) :=
  isReduced_of_injective (ZariskiTwo.glued ρa ρb).val Subtype.val_injective

end Glued

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

include hO in
/-- **The covering over the first chart is reduced** if the chart `B n` is reduced and Noetherian
(`hfin`: the étale piece `E n` is finite over `D(b₀)`, the field `Overlap.hfinE`). -/
theorem Input.isReduced_Y (I : Input θ cov₀ πL) [IsReduced (I.B n)] [IsNoetherianRing (I.B n)]
    (hfin : ∃ s : Finset (I.E n), ∀ p : I.E n, ∃ k : ℕ,
      algebraMap I.B0 (I.B n) I.b0 ^ k • p ∈ Submodule.span (I.B n) (s : Set (I.E n))) :
    IsReduced (I.Y hθ n) := by
  haveI : IsReduced (I.R n) := isReduced_of_isLocalization (Submonoid.powers (I.a n)) (S := I.R n)
  haveI : IsReduced (I.T.G hθ n) := I.T.isReduced_G hθ hO n
  haveI : IsReduced (I.E n) := isReduced_of_span_pow _ (I.hbE n) hfin.choose hfin.choose_spec
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  exact ZariskiTwo.isReduced_glued _ _

namespace Overlap

variable {I : Input θ cov₀ πL} (V : Overlap I)

/-- `R1 = Y n`. -/
theorem isReduced_R1 [IsReduced (I.Y hθ n)] : IsReduced (V.twoChart hθ hO n).R1 :=
  ‹IsReduced (I.Y hθ n)›

/-- `R01 = Q n = Y n[1/x₁]`. -/
theorem isReduced_R01 [IsReduced (I.Y hθ n)] : IsReduced (V.twoChart hθ hO n).R01 :=
  (inferInstance : IsReduced (V.Q hθ n))

/-- `R0 = Q n ×_{M n} P0 n`. -/
theorem isReduced_R0 [IsReduced (I.Y hθ n)] [IsReduced (V.P0.P n)] :
    IsReduced (V.twoChart hθ hO n).R0 := by
  letI := V.alg0'Q hθ n
  letI := V.alg0'E n
  letI := V.alg0'M n
  exact ZariskiTwo.isReduced_glued (V.ρ0a hθ hO n) (V.ρ0b n)

include hO in
/-- **The two-chart rings of the covering at level `n` are reduced** if the chart `B n` is reduced
and Noetherian and the piece `P0 n` over `D(c₀)` is reduced (at `n = 0`: the input `I2` of
`TwoChartTower.isIntegralClosure_shift0/1`). -/
theorem isReduced_twoChart [hB : IsReduced (I.B n)] [hBN : IsNoetherianRing (I.B n)]
    [hP : IsReduced (V.P0.P n)] :
    IsReduced (V.twoChart hθ hO n).R0 ∧ IsReduced (V.twoChart hθ hO n).R1 := by
  haveI := I.isReduced_Y hθ hO n (V.hfinE n)
  exact ⟨V.isReduced_R0 hθ hO n, V.isReduced_R1 hθ hO n⟩

end Overlap

section Pieces

variable {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)]
  [∀ n, Algebra O (B' n)] [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}
  [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)]

/-- **The patch piece over `D(c₀)` is reduced** if the level `B' n` is (`R n = B' n[1/c₀]`). -/
theorem PatchInput.isReduced_piece (D : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL)
    [IsReduced (B' n)] : IsReduced ((D.piece hθ hO).P n) := by
  haveI : IsReduced (D.R n) :=
    isReduced_of_isLocalization (Submonoid.powers (algebraMap B0' (B' n) c0)) (S := D.R n)
  exact D.T.isReduced_G hθ hO n

end Pieces

end NodeEtaleGlue

end SemistableReduction
