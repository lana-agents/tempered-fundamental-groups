/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleAdic
import TemperedFundamentalGroups.SemistableReduction.NilpotentFlatness

/-!
# Flatness of the special fibre over `k[X]` from torsion-freeness (Blueprint §12.8, M2.4, step 3f)

The second hypothesis of the fibrewise flatness criterion (`NilpotentFlatness`) for a chart module
`M` (an `A`-module with an endomorphism `φ`, i.e. an `A[X]`-module `Module.AEval' φ`) is flatness
of `M / I M` over `A[X] / I A[X] ≅ (A / I)[X]`. For a maximal ideal `I` this ring is a principal
ideal domain, so flatness is torsion-freeness (`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`).
We state torsion-freeness elementwise on `M` itself:

* **`FibreRegular I φ`**: for every polynomial `p ∉ I A[X]` and `m : M`, `p(φ) m ∈ I M` implies
  `m ∈ I M`;
* **`FibreRegular.flat`**: then `(A[X] / I A[X]) ⊗_{A[X]} M` is flat over `A[X] / I A[X]`;
* `FibreRegular.of_killed`: for `M` killed by `I` (the level `0`), `FibreRegular` says that every
  `p(φ)` with `p ∉ I A[X]` is injective;
* **`FibreRegular.of_surjective`**: `FibreRegular` descends along a surjection `M ↠ M₀`
  commuting with the endomorphisms whose kernel is `I M` (the transition maps of a tower);
* **`FibreFlat.fibreRegular0`, `fibreRegular1`**: in an adic system of chart modules, the
  fibre flatness of all levels from `FibreRegular` of level `1`;
  **`FibreFlat.flat_quotient0`, `flat_quotient1`**: combined with flatness over `A / Iⁿ`,
  the hypotheses `hflat0`, `hflat1` of `ProjectiveLine.ChartModule.flat_of_system`.
-/

universe u v

open Polynomial TensorProduct

namespace SemistableReduction

namespace FibreFlat

variable {A : Type u} [CommRing A] (I : Ideal A) {M : Type v} [AddCommGroup M] [Module A M]

/-- **Torsion-freeness of the fibre over `I`**, elementwise: `p(φ) m ∈ I M` implies `m ∈ I M`
for every polynomial `p` not in `I A[X]`. -/
def FibreRegular (φ : M →ₗ[A] M) : Prop :=
  ∀ p : A[X], p ∉ I.map C → ∀ m : M, aeval φ p m ∈ I • (⊤ : Submodule A M) →
    m ∈ I • (⊤ : Submodule A M)

variable {I}

/-- `A[X] / I A[X]` is a domain for a prime ideal `I`. -/
instance isDomain_quotient [I.IsPrime] : IsDomain (A[X] ⧸ I.map (C : A →+* A[X])) :=
  Ideal.Quotient.isDomain _

/-- `A[X] / I A[X]` is a principal ideal ring for a maximal ideal `I`. -/
instance isPrincipalIdealRing_quotient [I.IsMaximal] :
    IsPrincipalIdealRing (A[X] ⧸ I.map (C : A →+* A[X])) := by
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  exact IsPrincipalIdealRing.of_surjective _
    (Ideal.polynomialQuotientEquivQuotientPolynomial I).surjective

/-- **Flatness of the special fibre**: if `I` is maximal and `φ` is fibre-regular, then
`(A[X] / I A[X]) ⊗_{A[X]} M` (with `X` acting by `φ`) is flat over `A[X] / I A[X]`. -/
theorem FibreRegular.flat [I.IsMaximal] {φ : M →ₗ[A] M} (h : FibreRegular I φ) :
    Module.Flat (A[X] ⧸ I.map C) ((A[X] ⧸ I.map C) ⊗[A[X]] Module.AEval' φ) := by
  set Q := A[X] ⧸ I.map (C : A →+* A[X])
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro t ⟨⟨q, hq⟩, hqt⟩
  change q • t = 0 at hqt
  rw [Submodule.mem_bot]
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  set e := quotTensorEquivQuotSMul (Module.AEval' φ) (I.map (C : A →+* A[X]))
  obtain ⟨m', hm'⟩ := Submodule.mkQ_surjective _ (e t)
  have ht : t = Ideal.Quotient.mk _ 1 ⊗ₜ[A[X]] m' := by
    apply e.injective
    rw [quotTensorEquivQuotSMul_mk_tmul, one_smul, ← hm']
    rfl
  have hp : p ∉ I.map C := fun hp ↦ hq0 (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  rw [ht, smul_tmul', smul_eq_mul, map_one, mul_one] at hqt
  have hmem := congrArg e hqt
  rw [map_zero, quotTensorEquivQuotSMul_mk_tmul, Submodule.Quotient.mk_eq_zero] at hmem
  set m := (Module.AEval'.of φ).symm m'
  have hm : m' = Module.AEval'.of φ m := (LinearEquiv.apply_symm_apply _ _).symm
  rw [hm, ← Module.AEval.of_aeval_smul] at hmem
  have hmem' : Module.AEval'.of φ (aeval φ p m) ∈
      (I • (⊤ : Submodule A (Module.AEval' φ))) := by
    rw [← NilpotentFlatness.restrictScalars_map_C_smul_top]
    exact hmem
  have hIM : ∀ y : M, Module.AEval'.of φ y ∈ (I • (⊤ : Submodule A (Module.AEval' φ))) →
      y ∈ I • (⊤ : Submodule A M) := fun y hy ↦ by
    have := Submodule.mem_map_of_mem (f := ((Module.AEval'.of φ).symm : _ →ₗ[A] M)) hy
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at this
    simpa using this
  have hm0 := h p hp m (hIM _ hmem')
  rw [ht, hm]
  apply e.injective
  rw [map_zero, quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero]
  have hof : Module.AEval'.of φ m ∈ (I • (⊤ : Submodule A (Module.AEval' φ))) := by
    have := Submodule.mem_map_of_mem (f := ((Module.AEval'.of φ).toLinearMap)) hm0
    rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at this
  rw [← NilpotentFlatness.restrictScalars_map_C_smul_top] at hof
  exact hof

/-- Linear maps intertwining two endomorphisms intertwine their polynomials. -/
lemma aeval_comm {M₀ : Type*} [AddCommGroup M₀] [Module A M₀] {φ : M →ₗ[A] M}
    {φ₀ : M₀ →ₗ[A] M₀} (ψ : M →ₗ[A] M₀) (hψ : ∀ m, ψ (φ m) = φ₀ (ψ m)) (p : A[X]) (m : M) :
    ψ (aeval φ p m) = aeval φ₀ p (ψ m) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp,
      hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial]
    simp only [Module.End.mul_apply, map_smul, Module.algebraMap_end_apply]
    congr 1
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hψ, ih]

/-- **`FibreRegular` descends along a surjection** `ψ : M ↠ M₀` intertwining the endomorphisms
with kernel contained in `I M` (e.g. the transition map to the level `1` of an adic system). -/
theorem FibreRegular.of_surjective {M₀ : Type*} [AddCommGroup M₀] [Module A M₀]
    {φ : M →ₗ[A] M} {φ₀ : M₀ →ₗ[A] M₀} (h₀ : FibreRegular I φ₀) (ψ : M →ₗ[A] M₀)
    (hψ : ∀ m, ψ (φ m) = φ₀ (ψ m)) (hs : Function.Surjective ψ)
    (hk : LinearMap.ker ψ ≤ I • ⊤) : FibreRegular I φ := by
  intro p hp m hm
  have hmap : (I • (⊤ : Submodule A M)).map ψ = I • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hs]
  have h1 : ψ (aeval φ p m) ∈ I • (⊤ : Submodule A M₀) := hmap ▸ Submodule.mem_map_of_mem hm
  rw [aeval_comm ψ hψ] at h1
  have h2 := h₀ p hp (ψ m) h1
  rw [← hmap] at h2
  obtain ⟨m', hm', he⟩ := h2
  have h3 : m - m' ∈ I • (⊤ : Submodule A M) := hk (by rw [LinearMap.mem_ker, map_sub, he,
    sub_self])
  simpa using Submodule.add_mem _ h3 hm'

/-- For a module killed by `I`, `FibreRegular` is injectivity of `p(φ)` for `p ∉ I A[X]`. -/
theorem FibreRegular.of_killed {φ : M →ₗ[A] M} (hkill : I • (⊤ : Submodule A M) = ⊥)
    (h : ∀ p : A[X], p ∉ I.map C → ∀ m : M, aeval φ p m = 0 → m = 0) : FibreRegular I φ := by
  intro p hp m hm
  rw [hkill, Submodule.mem_bot] at hm ⊢
  exact h p hp m hm

/-- A module killed by the unit ideal is fibre-regular. -/
theorem FibreRegular.of_top {φ : M →ₗ[A] M} (hkill : (⊤ : Ideal A) • (⊤ : Submodule A M) = ⊥) :
    FibreRegular I φ := by
  intro p _ m _
  have : m ∈ (⊤ : Ideal A) • (⊤ : Submodule A M) := by
    rw [Submodule.top_smul]
    exact Submodule.mem_top
  rw [hkill, Submodule.mem_bot] at this
  rw [this]
  exact Submodule.zero_mem _

/-! ### Adic systems of chart modules -/

variable (S : ProjectiveLine.AdicChartSystem I)

/-- Fibre-regularity of all levels (chart `Spec A[X]`) from the level `1`. -/
theorem fibreRegular0 (h : FibreRegular I (S.M 1).x0) (n : ℕ) : FibreRegular I (S.M n).x0 := by
  rcases n with _ | n
  · exact FibreRegular.of_top (by simpa using S.kill0 0)
  · refine h.of_surjective (S.tr (Nat.le_add_left 1 n)).f0 (S.tr _).comm_x0
      (S.surj0 _) ?_
    rw [S.ker0, pow_one]

/-- Fibre-regularity of all levels (chart `Spec A[Y]`) from the level `1`. -/
theorem fibreRegular1 (h : FibreRegular I (S.M 1).x1) (n : ℕ) : FibreRegular I (S.M n).x1 := by
  rcases n with _ | n
  · exact FibreRegular.of_top (by simpa using S.kill1 0)
  · refine h.of_surjective (S.tr (Nat.le_add_left 1 n)).f1 (S.tr _).comm_x1
      (S.surj1 _) ?_
    rw [S.ker1, pow_one]

/-- **The hypothesis `hflat0` of `ChartModule.flat_of_system`** from flatness of the levels over
`A / Iⁿ` and fibre-regularity of the level `1` (chart `Spec A[X]`). -/
theorem flat_quotient0 [I.IsMaximal]
    [∀ n, Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] Module.AEval' (S.M n).x0)]
    (h : FibreRegular I (S.M 1).x0) (n : ℕ) :
    Module.Flat (A[X] ⧸ I.map C ^ n) ((A[X] ⧸ I.map C ^ n) ⊗[A[X]] Module.AEval' (S.M n).x0) :=
  haveI := (fibreRegular0 S h n).flat
  NilpotentFlatness.flat_quotient_polynomial _ I n

/-- **The hypothesis `hflat1` of `ChartModule.flat_of_system`** (chart `Spec A[Y]`). -/
theorem flat_quotient1 [I.IsMaximal]
    [∀ n, Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] Module.AEval' (S.M n).x1)]
    (h : FibreRegular I (S.M 1).x1) (n : ℕ) :
    Module.Flat (A[X] ⧸ I.map C ^ n) ((A[X] ⧸ I.map C ^ n) ⊗[A[X]] Module.AEval' (S.M n).x1) :=
  haveI := (fibreRegular1 S h n).flat
  NilpotentFlatness.flat_quotient_polynomial _ I n

end FibreFlat

end SemistableReduction
