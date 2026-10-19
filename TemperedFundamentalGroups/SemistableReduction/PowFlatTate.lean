/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.PowFlatOverlap
import TemperedFundamentalGroups.SemistableReduction.PowFlatQuot
import TemperedFundamentalGroups.SemistableReduction.TateGlue0CuspTower

/-!
# `ϖ`-purity of the levels of the Tate coverings (Blueprint §12.8, M2.4, step 3f)

Generic:

* `PowFlat.isSMulRegular_of_free`, **`PowFlat.tn`**, `tn_kill`: the levels `T/ϖⁿ⁺¹` of a chart
  free over `O[X]` (`O` a domain, `ϖ ≠ 0`);
* `PowFlat.aeval_x0`, `aeval_x1`: the chart modules of two-chart rings;
* **`PowFlat.system_pure0`**, **`system_pure1`**: for `V : NodeEtaleGlue.Overlap I` (`(ϖ)` maximal),
  the chart modules of the adic system `V.system` are flat over `O/ϖⁿ`
  (`PowFlat.flat_quotient`), given `PowFlat` of the base chart levels `B n` and of the piece
  `P0 n` over `D(c₀)`.

Tate (only through the generic statements):

* `TateGlue0.powFlat_T1n`, `powFlat_T0n`, `π'_ne_zero`, `powFlat_piece0` (étale lifts),
  `powFlat_cuspPiece` (cusp patch), `powFlat_overlapP` (`R0`, `R1` of `overlapP .. twoChart n`);
* **`TateGlue0.system_hpure0`, `system_hpure1`, `systemCusp_hpure0`, `systemCusp_hpure1`**: the
  hypotheses `hpure0`, `hpure1` of `TateGlue0.exists_flat_algebraization(_cusp)` (for `O` a domain,
  `ϖ ≠ 0`, `(ϖ)` maximal).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace PowFlat

/-- `ϖ` is a nonzerodivisor on an algebra free over `O[X]`, for `O` a domain and `ϖ ≠ 0`. -/
theorem isSMulRegular_of_free {O : Type u} [CommRing O] [IsDomain O] {ϖ : O} (hϖ : ϖ ≠ 0)
    {T : Type u} [CommRing T] [Algebra O T] [Algebra O[X] T] [IsScalarTower O O[X] T]
    [Module.Free O[X] T] : IsSMulRegular T ϖ := by
  intro x y hxy
  have h : (C ϖ : O[X]) • x = (C ϖ : O[X]) • y := by
    rw [← Polynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul]
    exact hxy
  exact smul_right_injective T (Polynomial.C_ne_zero.mpr hϖ) h

/-- **The levels `T/ϖⁿ⁺¹` of a chart** without `ϖ`-torsion. -/
theorem tn {O : Type u} [CommRing O] {ϖ : O} {T : Type u} [CommRing T] [Algebra O T]
    (hreg : IsSMulRegular T ϖ) (n : ℕ) : PowFlat ϖ (n + 1) (EtaleTower.Tn ϖ T n) :=
  quotient hreg _ (by
    rw [EtaleTower.Iv, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow])

/-- `ϖⁿ⁺¹ = 0` on the levels `T/ϖⁿ⁺¹`. -/
lemma tn_kill {O : Type u} [CommRing O] (ϖ : O) (T : Type u) [CommRing T] [Algebra O T]
    (n : ℕ) : algebraMap O (EtaleTower.Tn ϖ T n) ϖ ^ (n + 1) = 0 := by
  rw [← map_pow, IsScalarTower.algebraMap_apply O T, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.mem_map_of_mem _ ?_
  rw [EtaleTower.Iv, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

/-- Every module is `PowFlat` of exponent `0`. -/
theorem zero {O : Type u} [CommRing O] {ϖ : O} {M : Type u} [AddCommGroup M] [Module O M] :
    PowFlat ϖ 0 M := fun i hi m _ ↦ ⟨m, by rw [Nat.le_zero.mp hi, pow_zero, one_smul]⟩

/-- The chart module `x0` of two-chart rings is `PowFlat` if `R0` is. -/
theorem aeval_x0 {O : Type u} [CommRing O] {ϖ : O} {N : ℕ} (D : ProjectiveLine.TwoChartRings O)
    (h : PowFlat ϖ N D.R0) : PowFlat ϖ N (Module.AEval' D.chartModule.x0) :=
  of_addEquiv (Module.AEval'.of D.chartModule.x0).symm.toAddEquiv
    (fun m ↦ (Module.AEval'.of D.chartModule.x0).symm.map_smul ϖ m) h

/-- The chart module `x1` of two-chart rings is `PowFlat` if `R1` is. -/
theorem aeval_x1 {O : Type u} [CommRing O] {ϖ : O} {N : ℕ} (D : ProjectiveLine.TwoChartRings O)
    (h : PowFlat ϖ N D.R1) : PowFlat ϖ N (Module.AEval' D.chartModule.x1) :=
  of_addEquiv (Module.AEval'.of D.chartModule.x1).symm.toAddEquiv
    (fun m ↦ (Module.AEval'.of D.chartModule.x1).symm.map_smul ϖ m) h

/-- `ϖⁿ⁺¹` kills a ring `R` if `(ϖ)ⁿ⁺¹ R = 0`. -/
lemma pow_smul_eq_zero {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R] {ϖ : O}
    {n : ℕ} (h : (Ideal.span {ϖ} ^ n).map (algebraMap O R) = ⊥) (r : R) : ϖ ^ n • r = 0 := by
  rw [Algebra.smul_def]
  have : algebraMap O R (ϖ ^ n) ∈ (Ideal.span {ϖ} ^ n).map (algebraMap O R) :=
    Ideal.mem_map_of_mem _ (by
      rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
  rw [h, Ideal.mem_bot] at this
  rw [this, zero_mul]

section System

open NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [IsDomain O] [∀ n, IsNoetherianRing (I.B n)]
  [(Ideal.span {V.ϖ}).IsMaximal] (hπ : ∀ j, πL j ≠ 0) (hϖ : V.ϖ ≠ 0)
  (hB : ∀ n, PowFlat V.ϖ (n + 1) (I.B n)) (hI : ∀ n, I.T.I n = Ideal.span {V.ϖ ^ (n + 1)})

include hπ hϖ hB hI in
/-- **`ϖ`-purity of the adic system of the covering, chart `U₀`** (the hypothesis `hpure0` of the
flat algebraization): its chart modules are flat over `O/ϖⁿ`, given `PowFlat` of the levels of
the base chart and of the piece over `D(c₀)`. -/
theorem system_pure0 (hP0 : ∀ n, PowFlat V.ϖ (n + 1) (V.P0.P n)) (n : ℕ) :
    Module.Flat (O ⧸ Ideal.span {V.ϖ} ^ n) ((O ⧸ Ideal.span {V.ϖ} ^ n) ⊗[O]
      Module.AEval' ((V.system hθ hO).M n).x0) := by
  rcases n with _ | n
  · haveI : Subsingleton (Module.AEval' ((V.system hθ hO).M 0).x0) :=
      ⟨fun a b ↦ Subsingleton.elim (α := PUnit) a b⟩
    exact flat_quotient 0 zero fun _ ↦ Subsingleton.elim _ _
  · change Module.Flat _ (_ ⊗[O] Module.AEval' (V.twoChart hθ hO n).chartModule.x0)
    exact flat_quotient (n + 1)
      (aeval_x0 _ (twoChart_R0 V hθ hO n hπ hϖ (hB n) (hI n) (hP0 n)))
      (fun m ↦ (Module.AEval'.of (V.twoChart hθ hO n).chartModule.x0).symm.injective (by
        rw [LinearEquiv.map_smul, map_zero]
        exact pow_smul_eq_zero (R := (V.twoChart hθ hO n).R0) (V.kill0 hθ hO n) _))

include hπ hϖ hB hI in
/-- **`ϖ`-purity of the adic system of the covering, chart `U₁`** (`hpure1`). -/
theorem system_pure1 (n : ℕ) :
    Module.Flat (O ⧸ Ideal.span {V.ϖ} ^ n) ((O ⧸ Ideal.span {V.ϖ} ^ n) ⊗[O]
      Module.AEval' ((V.system hθ hO).M n).x1) := by
  rcases n with _ | n
  · haveI : Subsingleton (Module.AEval' ((V.system hθ hO).M 0).x1) :=
      ⟨fun a b ↦ Subsingleton.elim (α := PUnit) a b⟩
    exact flat_quotient 0 zero fun _ ↦ Subsingleton.elim _ _
  · change Module.Flat _ (_ ⊗[O] Module.AEval' (V.twoChart hθ hO n).chartModule.x1)
    exact flat_quotient (n + 1)
      (aeval_x1 _ (twoChart_R1 V hθ hO n hπ hϖ (hB n) (hI n)))
      (fun m ↦ (Module.AEval'.of (V.twoChart hθ hO n).chartModule.x1).symm.injective (by
        rw [LinearEquiv.map_smul, map_zero]
        exact pow_smul_eq_zero (R := (V.twoChart hθ hO n).R1) (V.kill1 hθ hO n) _))

end System

end PowFlat

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel KummerEtale AdmissibleLift PowFlat

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (hϖ : θ ϖ = 0) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (hm : m ≠ 0)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

omit [IsNoetherianRing O] in
/-- The levels `T1/ϖⁿ⁺¹` of the chart over `U₁`. -/
theorem powFlat_T1n [IsDomain O] (hϖ0 : ϖ ≠ 0) (n : ℕ) :
    PowFlat ϖ (n + 1) (TateGlue1.B ϖ π b₄ t κ n) :=
  tn (T := T1 π b₄ t κ) (isSMulRegular_of_free hϖ0) n

omit [IsNoetherianRing O] in
/-- The levels `T0/ϖⁿ⁺¹` of the chart over `U₀`. -/
theorem powFlat_T0n [IsDomain O] (hϖ0 : ϖ ≠ 0) (n : ℕ) :
    PowFlat ϖ (n + 1) (TateGlue0.B ϖ π b₄ t κ n) :=
  tn (T := T0 π b₄ t κ) (isSMulRegular_of_free hϖ0) n

include hπ' in
omit [IsNoetherianRing O] in
/-- The deformation parameters of the Kummer factors are nonzero. -/
lemma π'_ne_zero [IsDomain O] (hϖ0 : ϖ ≠ 0) (j : cov₀.ι) : π' j ≠ 0 := by
  intro h
  have := hπ' j
  rw [h, zero_pow (cov₀.e_pos j).ne'] at this
  exact pow_ne_zero m hϖ0 this.symm

omit hθ in
/-- **The étale lifts `E0 n` over `D(1 + h)`** (the piece `piece0`). -/
theorem powFlat_piece0 [IsDomain O] (hϖ0 : ϖ ≠ 0) (Sp0 : Special0 θ π b₄ t κ) (n : ℕ) :
    PowFlat ϖ (n + 1) ((piece0 (hϖ := hϖ) (hker := hker) (Sp0 := Sp0)).P n) := by
  letI := algOE0 hϖ hker Sp0 n
  haveI := towerOE0 hϖ hker Sp0 n
  have h : PowFlat ϖ (n + 1) (E0 Sp0 hϖ hker n).E :=
    PowFlat.etale (B := TateGlue0.B ϖ π b₄ t κ n) (powFlat_T0n hϖ0 n) (tn_kill ϖ _ n)
      (E0 Sp0 hϖ hker n).hb (E0 Sp0 hϖ hker n).hfin
  exact h

/-- **The chart rings of the Tate covering with any piece over `D(1 + h)`** (`overlapP`) at level
`n` are `PowFlat ϖ (n+1)`, if the piece is (`R01` : `PowFlat.twoChart_R01`). -/
theorem powFlat_overlapP [IsDomain O] (hϖ0 : ϖ ≠ 0) (C0 : Type u) [CommRing C0]
    [Algebra (T0s θ π b₄ t κ) C0] (ω : OmegaC hκ hπ Sp C0)
    (P0 : NodeEtaleGlue.Piece0 θ (B ϖ π b₄ t κ) (EtaleTower.q (T0 π b₄ t κ) hϖ) C0
      (h0 π b₄ t κ) (c0 π b₄ t κ) (Ideal.Quotient.mk _ (h0 π b₄ t κ))
      (Ideal.Quotient.mk _ (c0 π b₄ t κ)) ϖ) (n : ℕ) (hP0 : PowFlat ϖ (n + 1) (P0.P n)) :
    @PowFlat O _ ϖ (n + 1)
        ((overlapP hκ hπ hε hϖ π' hπ' hker Sp hm C0 ω P0).twoChart hθ.out hO n).R0 _
        Algebra.toModule ∧
      @PowFlat O _ ϖ (n + 1)
        ((overlapP hκ hπ hε hϖ π' hπ' hker Sp hm C0 ω P0).twoChart hθ.out hO n).R1 _
        Algebra.toModule := by
  have hπ0 := π'_ne_zero π' hπ' hϖ0
  have hB : PowFlat ϖ (n + 1) (TateGlue1.B ϖ π b₄ t κ n) := powFlat_T1n hϖ0 n
  have hI : (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).T.I n = Ideal.span {ϖ ^ (n + 1)} :=
    Ideal.span_singleton_pow ϖ (n + 1)
  haveI : IsNoetherianRing ((TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).B n) :=
    (inferInstance : IsNoetherianRing (TateGlue1.B ϖ π b₄ t κ n))
  exact ⟨twoChart_R0 (overlapP hκ hπ hε hϖ π' hπ' hker Sp hm C0 ω P0) hθ.out hO n hπ0 hϖ0 hB hI
      hP0,
    twoChart_R1 (overlapP hκ hπ hε hϖ π' hπ' hker Sp hm C0 ω P0) hθ.out hO n hπ0 hϖ0 hB hI⟩

section Pure

variable [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] (hϖ0 : ϖ ≠ 0)

include hϖ0 in
/-- **`hpure0` for the Tate covering étale over `D(1 + h)`**: the chart modules over `U₀` of its
adic system are flat over `O/ϖⁿ` (the hypothesis of `TateGlue0.exists_flat_algebraization`). -/
theorem system_hpure0 (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0) (n : ℕ) :
    Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n).x0) := by
  haveI : (Ideal.span {(overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  haveI : ∀ n, IsNoetherianRing ((TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).B n) :=
    fun n ↦ (inferInstance : IsNoetherianRing (TateGlue1.B ϖ π b₄ t κ n))
  exact system_pure0 (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω) hθ.out hO
    (π'_ne_zero π' hπ' hϖ0) hϖ0 (fun n ↦ powFlat_T1n hϖ0 n)
    (fun n ↦ Ideal.span_singleton_pow ϖ (n + 1)) (fun n ↦ powFlat_piece0 hϖ hker hϖ0 Sp0 n) n

include hϖ0 in
/-- **`hpure1` for the Tate covering étale over `D(1 + h)`** (chart `U₁`). -/
theorem system_hpure1 (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0) (n : ℕ) :
    Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n).x1) := by
  haveI : (Ideal.span {(overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  haveI : ∀ n, IsNoetherianRing ((TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).B n) :=
    fun n ↦ (inferInstance : IsNoetherianRing (TateGlue1.B ϖ π b₄ t κ n))
  exact system_pure1 (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω) hθ.out hO
    (π'_ne_zero π' hπ' hϖ0) hϖ0 (fun n ↦ powFlat_T1n hϖ0 n)
    (fun n ↦ Ideal.span_singleton_pow ϖ (n + 1)) n

omit [(Ideal.span {ϖ}).IsMaximal] in
include hϖ0 in
/-- The cusp patch pieces over `D(1 + h)` are `PowFlat`. -/
theorem powFlat_cuspPiece
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ)) (n : ℕ) :
    PowFlat ϖ (n + 1)
      ((CuspTower.cuspPiece Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO).P n) := by
  haveI : ∀ n, IsScalarTower (T0 π b₄ t κ) (EtaleTower.Tn ϖ (T0 π b₄ t κ) (n + 1))
      (EtaleTower.Tn ϖ (T0 π b₄ t κ) n) := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact patchInput_piece (CuspTower.cuspInput Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ)) hθ.out hO
    (fun j ↦ isEmptyElim j) hϖ0 (powFlat_T0n hϖ0 n) (tn_kill ϖ _ n)
    (Ideal.span_singleton_pow ϖ (n + 1))

include hϖ0 in
/-- **`hpure0` for the Tate covering ramified at the cusp** (the hypothesis of
`TateGlue0.exists_flat_algebraization_cusp`, chart `U₀`). -/
theorem systemCusp_hpure0
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) (n : ℕ) :
    Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n).x0) := by
  haveI : (Ideal.span {(overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  haveI : ∀ n, IsNoetherianRing ((TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).B n) :=
    fun n ↦ (inferInstance : IsNoetherianRing (TateGlue1.B ϖ π b₄ t κ n))
  exact system_pure0 (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω) hθ.out hO
    (π'_ne_zero π' hπ' hϖ0) hϖ0 (fun n ↦ powFlat_T1n hϖ0 n)
    (fun n ↦ Ideal.span_singleton_pow ϖ (n + 1)) (fun n ↦ powFlat_cuspPiece hϖ hker hO hϖ0 Sc n) n

include hϖ0 in
/-- **`hpure1` for the Tate covering ramified at the cusp** (chart `U₁`). -/
theorem systemCusp_hpure1
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) (n : ℕ) :
    Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n).x1) := by
  haveI : (Ideal.span {(overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  haveI : ∀ n, IsNoetherianRing ((TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm).B n) :=
    fun n ↦ (inferInstance : IsNoetherianRing (TateGlue1.B ϖ π b₄ t κ n))
  exact system_pure1 (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω) hθ.out hO
    (π'_ne_zero π' hπ' hϖ0) hϖ0 (fun n ↦ powFlat_T1n hϖ0 n)
    (fun n ↦ Ideal.span_singleton_pow ϖ (n + 1)) n

end Pure

end

end TateGlue0

end SemistableReduction
