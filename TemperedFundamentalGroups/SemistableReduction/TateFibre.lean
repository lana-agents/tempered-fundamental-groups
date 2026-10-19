/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue0CuspTower
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueRegular

/-!
# The special fibre of the Tate coverings is flat over `k[X]` (Blueprint §12.8, M2.4, step 3f)

* **`NodeEtaleGlue.PatchInput.regularOn_piece`**: a tower of patched algebras over `D(c₀)` (the
  cusp patch) is a regular piece (`Piece0.RegularOn`);
* `BasisIdeal.mul_mem_of_prime`: for `T` free over `A` and a prime `K ⊆ A`, `p ∉ K` is a
  nonzerodivisor modulo `K T`;
* **`TateGlue0.regularB`**, **`regularB'`**: nonzero polynomials over `O/ϖ` in `h'` (resp. `h`)
  are nonzerodivisors on the level `0` of the charts `T1/ϖ`, `T0/ϖ` (free over `O[X]`), for
  `(ϖ)` prime;
* `TateGlue0.regularOn_piece0`: the étale piece over `D(1 + h)` is regular;
* **`TateGlue0.flat_quotient0`, `flat_quotient1`**: the hypotheses `hflat0`, `hflat1` of
  `ProjectiveLine.ChartModule.flat_of_system` for the adic system `TateGlue0.system`, given the
  flatness of its levels over `O/ϖⁿ` (`ϖ`-purity, `hpure`);
* **`TateGlue0.exists_flat_algebraization`**, **`exists_flat_algebraization_cusp`**: the
  algebraizations of the Tate coverings (étale over `D(1 + h)`, resp. with the cusp patch) are flat
  over both charts `O[X]` of `ℙ¹_O`, given the `ϖ`-purity of the levels.
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

open AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

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
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)]

/-- **The cusp patch is a regular piece**: regular elements of `B' n` are regular on
`R n = B' n[1/c₀]` (flat) and hence on the patched algebra `G n`
(`LevelTower.Data.isSMulRegular_G`). -/
theorem regularOn_piece (n : ℕ) : (D.piece hθ hO).RegularOn n := fun g hg ↦ by
  haveI : Module.Flat (B' n) (D.R n) :=
    IsLocalization.flat (D.R n) (Submonoid.powers (algebraMap B0' (B' n) c0))
  have h1 : IsSMulRegular (D.R n) (algebraMap (B' n) (D.R n) g) := hg.of_flat
  have h2 := (isSMulRegular_algebraMap_iff (A := D.G hθ n) (M := D.G hθ n)).mpr
    (Data.isSMulRegular_G hθ hO D.T h1)
  exact (isSMulRegular_algebraMap_iff (R := B' n) (A := D.G hθ n) (M := D.G hθ n)).mp h2

end PatchInput

end NodeEtaleGlue

namespace BasisIdeal

variable {A T : Type u} {ι : Type*} [CommRing A] [CommRing T] [Algebra A T]
  (b : Module.Basis ι A T) [Finite ι] (K : Ideal A) [K.IsPrime]

include b in
/-- For `T` free over `A` and a prime `K ⊆ A`, an element `p ∉ K` is a nonzerodivisor modulo
`K T`. -/
lemma mem_of_mul_mem {p : A} (hp : p ∉ K) {y : T}
    (hy : algebraMap A T p * y ∈ K.map (algebraMap A T)) : y ∈ K.map (algebraMap A T) :=
  mem_of_repr_mem b K fun i ↦ by
    have := repr_mem b K hy i
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    exact (‹K.IsPrime›.mem_or_mem this).resolve_left hp

include b in
/-- An element `p ∉ K` is regular on `T / K T`. -/
lemma isSMulRegular_mk {p : A} (hp : p ∉ K) :
    IsSMulRegular (T ⧸ K.map (algebraMap A T))
      (Ideal.Quotient.mk (K.map (algebraMap A T)) (algebraMap A T p)) := by
  intro y z hyz
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk _ (algebraMap A T p) * Ideal.Quotient.mk _ y =
    Ideal.Quotient.mk _ (algebraMap A T p) * Ideal.Quotient.mk _ z at hyz
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at hyz
  rw [Ideal.Quotient.eq]
  exact mem_of_mul_mem b K hp hyz

end BasisIdeal

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel KummerEtale EtaleTower

/-! ### The levels `0` of the Tate charts -/

section Charts

variable {O : Type u} [CommRing O] (ϖ π b₄ t κ : O) [(Ideal.span {ϖ}).IsPrime]

omit [(Ideal.span {ϖ}).IsPrime] in
/-- `T/ϖ T = T/(ϖ O[X]) T` for an `O[X]`-algebra `T`. -/
lemma Iv_zero_map {T : Type u} [CommRing T] [Algebra O[X] T] [Algebra O T]
    [IsScalarTower O O[X] T] :
    (Ideal.span {ϖ} ^ (0 + 1)).map (algebraMap O T) =
      ((Ideal.span {ϖ}).map C).map (algebraMap O[X] T) := by
  rw [zero_add, pow_one, Ideal.map_map, ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq]

/-- **Nonzero polynomials over `O/ϖ` in `h'` are nonzerodivisors on `T1/ϖ`** (`T1` is free over
`O[h']`). -/
theorem regularB1 (p : O[X]) (hp : p ∉ (Ideal.span {ϖ}).map C) :
    IsSMulRegular (T1n ϖ π b₄ t κ 0)
      (algebraMap (T1 π b₄ t κ) (T1n ϖ π b₄ t κ 0) (aeval (h1 π b₄ t κ) p)) := by
  have e : aeval (h1 π b₄ t κ) p = algebraMap O[X] (T1 π b₄ t κ) p := by
    rw [h1, ← AdjoinRoot.algebraMap_eq, Polynomial.aeval_algebraMap_apply, aeval_X_left_apply]
  rw [e, Ideal.Quotient.algebraMap_eq]
  have h := BasisIdeal.isSMulRegular_mk (AdjoinRoot.powerBasis' (monic_G1 π b₄ t κ)).basis _ hp
  rw [← Iv_zero_map] at h
  exact h

/-- **Nonzero polynomials over `O/ϖ` in `h` are nonzerodivisors on `T0/ϖ`.** -/
theorem regularB0 (p : O[X]) (hp : p ∉ (Ideal.span {ϖ}).map C) :
    IsSMulRegular (B ϖ π b₄ t κ 0)
      (algebraMap (T0 π b₄ t κ) (B ϖ π b₄ t κ 0) (aeval (h0 π b₄ t κ) p)) := by
  have e : aeval (h0 π b₄ t κ) p = algebraMap O[X] (T0 π b₄ t κ) p := by
    rw [h0, ← AdjoinRoot.algebraMap_eq, Polynomial.aeval_algebraMap_apply, aeval_X_left_apply]
  rw [e, Ideal.Quotient.algebraMap_eq]
  have h := BasisIdeal.isSMulRegular_mk (AdjoinRoot.powerBasis' (monic_G0 π b₄ t κ)).basis _ hp
  rw [← Iv_zero_map] at h
  exact h

end Charts

/-! ### The adic systems of the Tate coverings -/

section System

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (hϖ : θ ϖ = 0) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (hm : m ≠ 0) (Sp0 : Special0 θ π b₄ t κ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

omit hθ in
/-- **The étale piece over `D(1 + h)` is regular** (the étale lifts are flat). -/
theorem regularOn_piece0 (n : ℕ) :
    (piece0 (hϖ := hϖ) (hker := hker) (Sp0 := Sp0)).RegularOn n := fun g hg ↦ by
  haveI := RegularPieces.flat_of_span_pow _ (E0 Sp0 hϖ hker n).hb
    (E0 Sp0 hϖ hker n).hfin.choose (E0 Sp0 hϖ hker n).hfin.choose_spec
  exact RegularPieces.isSMulRegular_of_flat (S := (E0 Sp0 hϖ hker n).E) hg

variable [(Ideal.span {ϖ}).IsMaximal] (ω : Omega hκ hπ Sp Sp0)

/-- **The hypothesis `hflat0` of `ChartModule.flat_of_system` for the Tate covering** (étale over
`D(1 + h)`), given the flatness of its levels over `O/ϖⁿ`. -/
theorem flat_quotient0
    (hpure : ∀ n, Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n).x0)) (n : ℕ) :
    Module.Flat (O[X] ⧸ (Ideal.span {ϖ}).map C ^ n) ((O[X] ⧸ (Ideal.span {ϖ}).map C ^ n) ⊗[O[X]]
      Module.AEval' ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n).x0) := by
  haveI : (Ideal.span {(overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  exact (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).flat_quotient0 hθ.out hO hpure
    (regularB1 ϖ π b₄ t κ) (regularB0 ϖ π b₄ t κ) (regularOn_piece0 hϖ hker Sp0 0) n

/-- **The hypothesis `hflat1` of `ChartModule.flat_of_system` for the Tate covering.** -/
theorem flat_quotient1
    (hpure : ∀ n, Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n).x1)) (n : ℕ) :
    Module.Flat (O[X] ⧸ (Ideal.span {ϖ}).map C ^ n) ((O[X] ⧸ (Ideal.span {ϖ}).map C ^ n) ⊗[O[X]]
      Module.AEval' ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n).x1) := by
  haveI : (Ideal.span {(overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  exact (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).flat_quotient1 hθ.out hO hpure
    (regularB1 ϖ π b₄ t κ) n

/-- **Flat algebraization of the Tate covering** (étale over `D(1 + h)`; Blueprint §12.8, M2.4,
step 3f): the coherent chart algebra on `ℙ¹_O` with reductions the levels of the covering is flat
over both charts `O[X]`, given the flatness of the levels over `O/ϖⁿ` (`hpure0`, `hpure1`). -/
theorem exists_flat_algebraization [IsAdicComplete (Ideal.span {ϖ}) O]
    (hpure0 : ∀ n, Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n).x0))
    (hpure1 : ∀ n, Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n).x1)) :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) := by
  haveI : (Ideal.span {(overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  haveI : IsAdicComplete (Ideal.span {(overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  exact (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).exists_flat_algebraization hθ.out hO
    hpure0 hpure1 (regularB1 ϖ π b₄ t κ) (regularB0 ϖ π b₄ t κ) (regularOn_piece0 hϖ hker Sp0 0)

end System

/-! ### The coverings ramified at the cusp -/

section Cusp

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
  (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (ω : OmegaC hκ hπ Sp Sc.C0) [(Ideal.span {ϖ}).IsMaximal]

/-- **Flat algebraization of the Tate covering ramified at the cusp** (the cusp patch over
`D(1 + h)`), given the flatness of the levels over `O/ϖⁿ` (`hpure0`, `hpure1`). -/
theorem exists_flat_algebraization_cusp [IsAdicComplete (Ideal.span {ϖ}) O]
    (hpure0 : ∀ n, Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n).x0))
    (hpure1 : ∀ n, Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n).x1)) :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) := by
  haveI : (Ideal.span {(overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  haveI : IsAdicComplete (Ideal.span {(overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  exact (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).exists_flat_algebraization hθ.out hO
    hpure0 hpure1 (regularB1 ϖ π b₄ t κ) (regularB0 ϖ π b₄ t κ)
    ((CuspTower.cuspInput Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ)).regularOn_piece hθ.out hO 0)

end Cusp

end TateGlue0

end

end SemistableReduction
