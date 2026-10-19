/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Tower
import TemperedFundamentalGroups.SemistableReduction.RegularPieces
import TemperedFundamentalGroups.SemistableReduction.TwoChartRegular
import FormalSchemes.ChartModuleFlatGlobal

/-!
# The special fibre of the glued coverings is torsion-free over `k[X]` (Blueprint §12.8, M2.4, 3f)

For the glued coverings of `NodeEtaleGlue` (generic over `I : Input`, `V : Overlap I`):

* **`NodeEtaleGlue.Input.isSMulRegular_Y`**: an element of `B0` regular on the level `B n` of the
  base chart is regular on `Y n = G n ×_{E n[1/a]} E n` (regular on the patched algebra `G n`,
  `LevelTower.Data.isSMulRegular_G`, and on the étale piece `E n`, which is flat);
* `NodeEtaleGlue.Overlap.isNoetherianRing_B`, `isNoetherianRing_B'`: the levels of the charts are
  Noetherian (for `O` Noetherian);
* **`NodeEtaleGlue.Overlap.polyRegular_y`**, **`polyRegular_x`**: `PolyRegular` (nonzero
  polynomials over `O/ϖ` in the coordinate are nonzerodivisors) of both coordinates of the
  two-chart rings `Overlap.twoChart n`, from `PolyRegular` of `x₁` on `B n`, of `x₀` on `B' n`,
  and regularity of the piece `P0` over `D(c₀)` (`Piece0.RegularOn`);
* **`NodeEtaleGlue.Piece0.regularOn_ofEtale`**, **`PatchInput.regularOn_piece`**: the étale piece
  and the cusp patch are `RegularOn`;
* **`NodeEtaleGlue.Overlap.flat_quotient0`**, **`flat_quotient1`**: the hypotheses `hflat0`,
  `hflat1` of `ProjectiveLine.ChartModule.flat_of_system` for the adic system `Overlap.system`
  (given the flatness of its levels over `O/ϖⁿ`, the `ϖ`-purity);
* **`NodeEtaleGlue.Overlap.exists_flat_algebraization`**: the algebraization of the covering
  (`Overlap.exists_algebraization`) is flat over both charts `O[X]`
  (`ProjectiveLine.ChartModule.flat_of_system`).
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower TensorProduct

noncomputable section

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

namespace Input

variable (I : Input θ cov₀ πL)

include hO in
/-- An element regular on the level `B n` of the base chart is regular on the patched algebra
`G n` (over `B0`). -/
theorem isSMulRegular_G (n : ℕ) {g : I.B0}
    (hg : IsSMulRegular (I.B n) (algebraMap I.B0 (I.B n) g)) :
    letI := alg0G I.T hθ I.B I.B0 n
    IsSMulRegular (I.T.G hθ n) g := by
  letI := alg0G I.T hθ I.B I.B0 n
  haveI : Module.Flat (I.B n) (I.R n) :=
    IsLocalization.flat (I.R n) (Submonoid.powers (algebraMap I.B0 (I.B n) I.a0))
  have h1 : IsSMulRegular (I.R n) (algebraMap (I.B n) (I.R n) (algebraMap I.B0 (I.B n) g)) :=
    hg.of_flat
  have h2 := (isSMulRegular_algebraMap_iff (A := I.T.G hθ n) (M := I.T.G hθ n)).mpr
    (Data.isSMulRegular_G hθ hO I.T h1)
  exact (isSMulRegular_algebraMap_iff (R := I.B0) (A := I.T.G hθ n) (M := I.T.G hθ n)).mp h2

/-- An element regular on the level `B n` of the base chart is regular on the étale piece `E n`
(flat over `B n`). -/
theorem isSMulRegular_E (n : ℕ) [IsNoetherianRing (I.B n)]
    (hfinE : ∃ s : Finset (I.E n), ∀ p : I.E n, ∃ k : ℕ,
      I.b n ^ k • p ∈ Submodule.span (I.B n) (s : Set (I.E n)))
    {g : I.B0} (hg : IsSMulRegular (I.B n) (algebraMap I.B0 (I.B n) g)) :
    letI := alg0 I.B I.B0 n (I.E n)
    IsSMulRegular (I.E n) g := by
  letI := alg0 I.B I.B0 n (I.E n)
  haveI := RegularPieces.flat_of_span_pow (I.b n) (I.hbE n) hfinE.choose hfinE.choose_spec
  have h := (isSMulRegular_algebraMap_iff (A := I.E n) (M := I.E n)).mpr
    (RegularPieces.isSMulRegular_of_flat (S := I.E n) hg)
  exact (isSMulRegular_algebraMap_iff (R := I.B0) (A := I.E n) (M := I.E n)).mp h

include hO in
/-- **An element of `B0` regular on the level `B n` is regular on the glued covering `Y n`.** -/
theorem isSMulRegular_Y (n : ℕ) [IsNoetherianRing (I.B n)]
    (hfinE : ∃ s : Finset (I.E n), ∀ p : I.E n, ∃ k : ℕ,
      I.b n ^ k • p ∈ Submodule.span (I.B n) (s : Set (I.E n)))
    {g : I.B0} (hg : IsSMulRegular (I.B n) (algebraMap I.B0 (I.B n) g)) :
    IsSMulRegular (I.Y hθ n) g := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  exact RegularPieces.isSMulRegular_subalgebra_prod
    (ZariskiTwo.glued (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hJB I.B0 n) (ρb0 I.B I.a I.E I.B0 n))
    (I.isSMulRegular_G hθ hO n hg) (I.isSMulRegular_E n hfinE hg)

end Input

namespace Piece0

variable {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)]
  [∀ n, Algebra O (B' n)] [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}

/-- **Regularity of a piece over `D(c₀)` at level `n`**: elements regular on the level `B' n`
of the chart stay regular on the piece. -/
def RegularOn (P0 : Piece0 θ B' qB' C0 x0 c0 x0s c0s ϖ) (n : ℕ) : Prop :=
  ∀ g : B' n, IsSMulRegular (B' n) g → IsSMulRegular (P0.P n) g

variable [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)] [∀ n, IsScalarTower O (B' (n + 1)) (B' n)]
  (E0 : ℕ → Type u) [∀ n, CommRing (E0 n)] [∀ n, Algebra (B' n) (E0 n)] [∀ n, Algebra O (E0 n)]
  [∀ n, IsScalarTower O (B' n) (E0 n)] [∀ n, Algebra.FormallyEtale (B' n) (E0 n)]
  (σE0 : ∀ n, letI := ((algebraMap Bs' C0).comp (qB' n)).toAlgebra
    (E0 n ⧸ EtaleNil.JB (J θ (R := B' n)) (E0 n)) ≃ₐ[B' n]
      Localization.Away (algebraMap Bs' C0 c0s))
  (hcE0 : ∀ n, IsUnit (algebraMap (B' n) (E0 n) (algebraMap B0' (B' n) c0)))
  (hfinE0 : ∀ n, ∃ s : Finset (E0 n), ∀ p : E0 n, ∃ k : ℕ,
    algebraMap B0' (B' n) c0 ^ k • p ∈ Submodule.span (B' n) (s : Set (E0 n)))
  (hx0 : ∀ n, qB' n (algebraMap B0' (B' n) x0) = x0s)
  (sE0 : ∀ n, E0 (n + 1) →+* E0 n)
  (hsE0 : ∀ n (x : B' (n + 1)), sE0 n (algebraMap (B' (n + 1)) (E0 (n + 1)) x) =
    algebraMap (B' n) (E0 n) (algebraMap (B' (n + 1)) (B' n) x))
  (hσE0 : ∀ n (x : E0 (n + 1)), σE0 n (Ideal.Quotient.mk _ (sE0 n x)) =
    σE0 (n + 1) (Ideal.Quotient.mk _ x))
  (hsE0s : ∀ n, Function.Surjective (sE0 n))
  (hkE0 : ∀ n, RingHom.ker (sE0 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (E0 (n + 1))))

/-- **The étale piece is regular** (the étale lifts are flat over the Noetherian levels). -/
theorem regularOn_ofEtale (n : ℕ) [IsNoetherianRing (B' n)] :
    (ofEtale E0 σE0 hcE0 hfinE0 hx0 sE0 hsE0 hσE0 hsE0s hkE0).RegularOn n := fun _ hg ↦
  haveI := RegularPieces.flat_of_span_pow _ (hcE0 n) (hfinE0 n).choose (hfinE0 n).choose_spec
  RegularPieces.isSMulRegular_of_flat (S := E0 n) hg

end Piece0

namespace Overlap

variable {I : Input θ cov₀ πL} (V : Overlap I)

include V in
/-- The base chart `B0` is Noetherian (finite over `O[X]`). -/
theorem isNoetherianRing_B0 [IsNoetherianRing O] : IsNoetherianRing I.B0 :=
  letI := V.algOB0
  letI := (Polynomial.aeval V.x1 : Polynomial O →ₐ[O] I.B0).toRingHom.toAlgebra
  haveI := V.finB0
  IsNoetherianRing.of_finite (Polynomial O) I.B0

include V in
/-- The levels `B n` are Noetherian. -/
theorem isNoetherianRing_B [IsNoetherianRing O] (n : ℕ) : IsNoetherianRing (I.B n) :=
  haveI := isNoetherianRing_B0 V
  isNoetherianRing_of_surjective I.B0 (I.B n) _ (V.surjB n)

/-- The second chart `B0'` is Noetherian. -/
theorem isNoetherianRing_B0' [IsNoetherianRing O] : IsNoetherianRing V.B0' :=
  letI := (Polynomial.aeval V.x0 : Polynomial O →ₐ[O] V.B0').toRingHom.toAlgebra
  haveI := V.finB0'
  IsNoetherianRing.of_finite (Polynomial O) V.B0'

/-- The levels `B' n` are Noetherian. -/
theorem isNoetherianRing_B' [IsNoetherianRing O] (n : ℕ) : IsNoetherianRing (V.B' n) :=
  haveI := V.isNoetherianRing_B0'
  isNoetherianRing_of_surjective V.B0' (V.B' n) _ (V.surjB' n)

/-- **Nonzero polynomials over `O/ϖ` in `x₁` are regular on the level `B n`.** -/
def RegularB (n : ℕ) : Prop :=
  ∀ p : Polynomial O, p ∉ (Ideal.span {V.ϖ}).map Polynomial.C →
    IsSMulRegular (I.B n) (algebraMap I.B0 (I.B n) (letI := V.algOB0; Polynomial.aeval V.x1 p))

/-- **Nonzero polynomials over `O/ϖ` in `x₀` are regular on the level `B' n`.** -/
def RegularB' (n : ℕ) : Prop :=
  ∀ p : Polynomial O, p ∉ (Ideal.span {V.ϖ}).map Polynomial.C →
    IsSMulRegular (V.B' n) (algebraMap V.B0' (V.B' n) (Polynomial.aeval V.x0 p))

/-- **The coordinate `y` of the chart `U₁`**: `PolyRegular` on `Y n` from `PolyRegular` of `x₁`
on the level `B n`. -/
theorem polyRegular_y [IsNoetherianRing O] (n : ℕ)
    (hB : V.RegularB n) :
    PolyRegular (Ideal.span {V.ϖ}) (V.twoChart hθ hO n).y := by
  intro p hp
  letI := V.algOB0
  letI := V.algOY hθ n
  haveI : IsScalarTower O I.B0 (I.Y hθ n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := isNoetherianRing_B V n
  have h := (isSMulRegular_algebraMap_iff (A := I.Y hθ n) (M := I.Y hθ n)).mpr
    (I.isSMulRegular_Y hθ hO n (V.hfinE n) (hB p hp))
  change IsSMulRegular (I.Y hθ n) (Polynomial.aeval (algebraMap I.B0 (I.Y hθ n) V.x1) p)
  rw [Polynomial.aeval_algebraMap_apply]
  exact h

/-- `PolyRegular` of `x₀` on the piece over `D(c₀)` from its regularity. -/
theorem polyRegular_P0 (n : ℕ) (hreg : V.P0.RegularOn n)
    (hB' : V.RegularB' n) :
    letI := V.alg0'E n
    PolyRegular (Ideal.span {V.ϖ}) (algebraMap V.B0' (V.P0.P n) V.x0) := by
  letI := V.alg0'E n
  haveI := V.towerOE n
  intro p hp
  rw [Polynomial.aeval_algebraMap_apply]
  exact (isSMulRegular_algebraMap_iff (R := V.B' n) (A := V.P0.P n) (M := V.P0.P n)).mpr
    (hreg _ (hB' p hp))

/-- **The coordinate `x` of the chart `U₀`**: `PolyRegular` on `R0 = Q n ×_{M n} P0 n`. -/
theorem polyRegular_x [IsNoetherianRing O] (n : ℕ) (hϖ : Ideal.span {V.ϖ} ≠ ⊤)
    (hB : V.RegularB n)
    (hB' : V.RegularB' n)
    (hreg : V.P0.RegularOn n) :
    PolyRegular (Ideal.span {V.ϖ}) (V.twoChart hθ hO n).x := by
  letI := V.alg0'Q hθ n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  letI := V.algOY hθ n
  letI := V.alg0'E n
  haveI := V.towerOE n
  letI := V.alg0'M n
  haveI := V.towerOM n
  exact TwoChartGlue.polyRegular_x (algebraMap I.B0 (I.Y hθ n) V.x1) (V.ιQ hθ n)
    (RingHomAway.of_algebra _) V.x0 (V.hxy hθ n) (V.patch0 hθ hO n).ρ0a (V.patch0 hθ hO n).ρ0b
    (V.patch0 hθ hO n).hb0 hϖ (V.polyRegular_y hθ hO n hB)
    (V.polyRegular_P0 n hreg hB')

/-! ### The adic system of the covering -/

/-- **Fibre-regularity of the chart `U₀` of the system** (level `1` = `twoChart 0`). -/
theorem fibreRegular0 [IsNoetherianRing O] (hϖ : Ideal.span {V.ϖ} ≠ ⊤) (hB : V.RegularB 0)
    (hB' : V.RegularB' 0) (hreg : V.P0.RegularOn 0) :
    FibreFlat.FibreRegular (Ideal.span {V.ϖ}) ((V.system hθ hO).M 1).x0 :=
  (V.polyRegular_x hθ hO 0 hϖ hB hB' hreg).fibreRegular
    (TwoChartTower.smul_top_eq_bot (by simpa using V.kill0 hθ hO 0))

/-- **Fibre-regularity of the chart `U₁` of the system.** -/
theorem fibreRegular1 [IsNoetherianRing O] (hB : V.RegularB 0) :
    FibreFlat.FibreRegular (Ideal.span {V.ϖ}) ((V.system hθ hO).M 1).x1 :=
  (V.polyRegular_y hθ hO 0 hB).fibreRegular
    (TwoChartTower.smul_top_eq_bot (by simpa using V.kill1 hθ hO 0))

/-- **The hypothesis `hflat0` of `ProjectiveLine.ChartModule.flat_of_system`** for the system of
the covering: from the flatness of its levels over `O/ϖⁿ` (`hpure`) and the regularity of the
coordinates on the level `0` of the charts and of the piece over `D(c₀)`. -/
theorem flat_quotient0 [IsNoetherianRing O] [(Ideal.span {V.ϖ}).IsMaximal]
    (hpure : ∀ n, Module.Flat (O ⧸ Ideal.span {V.ϖ} ^ n)
      ((O ⧸ Ideal.span {V.ϖ} ^ n) ⊗[O] Module.AEval' ((V.system hθ hO).M n).x0))
    (hB : V.RegularB 0) (hB' : V.RegularB' 0) (hreg : V.P0.RegularOn 0) (n : ℕ) :
    Module.Flat (Polynomial O ⧸ (Ideal.span {V.ϖ}).map Polynomial.C ^ n)
      ((Polynomial O ⧸ (Ideal.span {V.ϖ}).map Polynomial.C ^ n) ⊗[Polynomial O]
        Module.AEval' ((V.system hθ hO).M n).x0) :=
  haveI := hpure
  FibreFlat.flat_quotient0 (V.system hθ hO).toAdicChartSystem
    (V.fibreRegular0 hθ hO (Ideal.IsMaximal.ne_top inferInstance) hB hB' hreg) n

/-- **The hypothesis `hflat1` of `ProjectiveLine.ChartModule.flat_of_system`** for the system of
the covering. -/
theorem flat_quotient1 [IsNoetherianRing O] [(Ideal.span {V.ϖ}).IsMaximal]
    (hpure : ∀ n, Module.Flat (O ⧸ Ideal.span {V.ϖ} ^ n)
      ((O ⧸ Ideal.span {V.ϖ} ^ n) ⊗[O] Module.AEval' ((V.system hθ hO).M n).x1))
    (hB : V.RegularB 0) (n : ℕ) :
    Module.Flat (Polynomial O ⧸ (Ideal.span {V.ϖ}).map Polynomial.C ^ n)
      ((Polynomial O ⧸ (Ideal.span {V.ϖ}).map Polynomial.C ^ n) ⊗[Polynomial O]
        Module.AEval' ((V.system hθ hO).M n).x1) :=
  haveI := hpure
  FibreFlat.flat_quotient1 (V.system hθ hO).toAdicChartSystem (V.fibreRegular1 hθ hO hB) n

/-- **Flat algebraization of the covering** (Blueprint §12.8, M2.4, step 3f): the coherent chart
algebra on `ℙ¹_O` of `exists_algebraization` is flat over both charts `O[X]`
(`ProjectiveLine.ChartModule.flat_of_system`, fibrewise criterion), given the flatness of the
levels over `O/ϖⁿ` (`hpure0`, `hpure1`) and the regularity of the coordinates on the levels `0`
of the charts and of the piece over `D(c₀)`. -/
theorem exists_flat_algebraization [IsNoetherianRing O] [IsAdicComplete (Ideal.span {V.ϖ}) O]
    [(Ideal.span {V.ϖ}).IsMaximal]
    (hpure0 : ∀ n, Module.Flat (O ⧸ Ideal.span {V.ϖ} ^ n)
      ((O ⧸ Ideal.span {V.ϖ} ^ n) ⊗[O] Module.AEval' ((V.system hθ hO).M n).x0))
    (hpure1 : ∀ n, Module.Flat (O ⧸ Ideal.span {V.ϖ} ^ n)
      ((O ⧸ Ideal.span {V.ϖ} ^ n) ⊗[O] Module.AEval' ((V.system hθ hO).M n).x1))
    (hB : V.RegularB 0) (hB' : V.RegularB' 0) (hreg : V.P0.RegularOn 0) :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite (Polynomial O) (Module.AEval' N.x0))
      (_ : Module.Finite (Polynomial O) (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N ((V.system hθ hO).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n), ((V.system hθ hO).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((V.system hθ hO).alg n) (α n)) ∧
      Module.Flat (Polynomial O) (Module.AEval' N.x0) ∧
      Module.Flat (Polynomial O) (Module.AEval' N.x1) := by
  obtain ⟨N, h0, h1, Bα, α, hα, hc, hBα⟩ := V.exists_algebraization hθ hO
  have hflat := ProjectiveLine.ChartModule.flat_of_system (Ideal.span {V.ϖ}) N
    (V.system hθ hO).M α (fun n ↦ (hα n).1) (fun n ↦ (hα n).2.1) (fun n ↦ (hα n).2.2.1)
    (fun n ↦ (hα n).2.2.2) (V.system hθ hO).kill0 (V.system hθ hO).kill1
    (V.flat_quotient0 hθ hO hpure0 hB hB' hreg) (V.flat_quotient1 hθ hO hpure1 hB)
  exact ⟨N, h0, h1, Bα, α, hα, hc, hBα, hflat⟩

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
