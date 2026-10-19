/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue1Tower
import TemperedFundamentalGroups.SemistableReduction.TateGlue0Overlap
import TemperedFundamentalGroups.SemistableReduction.TateOverlap
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0

/-!
# The Tate coverings over the chart `V₀` (Blueprint §12.8, M2.3 (f))

For special-fibre coverings `Sp : TateGlue1.Special1` over `V₁` and `Sp0 : TateGlue0.Special0`
over `V₀` (both étale outside the nodes) together with the overlap datum
`ω : C0[1/h̄] ≃ C1[1/h̄']` over the special fibre `T01/J` of the overlap chart (`TateGlue0.Omega`):

* **`TateGlue0.overlap Sp Sp0 ω : NodeEtaleGlue.Overlap (TateGlue1.input ..)`**: the second chart
  `V₀ = Spec T0` with levels `T0n`, the overlap `T01 = T1[1/h'] = T0[1/h]` with levels `T01n`,
  `x₀ = h`, `c₀ = 1 + h`, `x₁ = h'`, `g = h'(1 + h')` (`D(g)` misses the nodes:
  `TateOverlap.fn_dvd_g`), and the étale lifts `TateGlue0.E0 n` of `C0` over `D(1 + h)`.

So `NodeEtaleGlue.Overlap.twoChart (overlap ..) n` are the two-chart rings of the Tate covering at
level `n`. As in `TateGlue1Tower`, statements about these coverings are to be derived from the
generic statements about an `Overlap`, not re-elaborated at the Tate types.
-/

universe u

namespace SemistableReduction

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel KummerEtale AdmissibleLift

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
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (hm : m ≠ 0) (Sp0 : Special0 θ π b₄ t κ)

/-- **The type of the overlap datum** for a covering `C0` of the special fibre of `V₀`:
`C0[1/h̄] ≃ₐ C1[1/h̄']` over the special fibre `T01/J` of the overlap chart. Together with `C0`
and `C1` this is the chart description of one covering of the special fibre. -/
abbrev OmegaC (C0 : Type u) [CommRing C0] [Algebra (T0s θ π b₄ t κ) C0] : Type u :=
  letI := algC0x C0 (θ := θ) (π := π) (b₄ := b₄) (t := t) (κ := κ)
  letI := algC1x Sp.C1 (θ := θ) (π := π) (b₄ := b₄) (t := t) (κ := κ)
  Localization.Away (algebraMap (T0s θ π b₄ t κ) C0 (Ideal.Quotient.mk _ (h0 π b₄ t κ))) ≃ₐ[
    T01s θ π b₄ t κ]
    Localization.Away (algebraMap (TateGlue1.T1s θ π b₄ t κ) Sp.C1
      (Ideal.Quotient.mk _ (h1 π b₄ t κ)))

/-- **The type of the overlap datum** for the covering `Sp0` étale over `D(1 + h̄)`. -/
abbrev Omega : Type u := OmegaC hκ hπ Sp Sp0.C

/-- The function `g = h'(1 + h')` on `V₁`: `D(g)` is the overlap of `D(1 + h) ⊆ V₀` with `V₁`. -/
abbrev g1 (π b₄ t κ : O) : T1 π b₄ t κ := h1 π b₄ t κ * (1 + h1 π b₄ t κ)

omit [IsNoetherianRing O] in
lemma rho0_c0 : rho0 π b₄ t κ (c0 π b₄ t κ) *
    algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (h1 π b₄ t κ) ^ 2 =
      algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (g1 π b₄ t κ) := by
  have hI := h1_mul_hinv π b₄ t κ
  rw [c0, map_add, map_one, rho0_h0, map_mul, map_add, map_one]
  linear_combination algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (h1 π b₄ t κ) * hI

omit [IsNoetherianRing O] in
lemma toNode_h1 : toNode b₄ hκ hπ (h1 π b₄ t κ) =
    SR b₄ b₆ ϖ m ε - algebraMap O _ t * uR b₄ b₆ ϖ m ε := by
  rw [toNode, liftT1_h1]

omit [IsNoetherianRing O] in
include hm in
/-- `D(g)` misses the nodes: `f ∣ g^{2(n+1)}` on the level-`n` node chart. -/
lemma fn_dvd_g1 (n : ℕ) :
    QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n ∣
      toRn b₄ hκ hπ n (Ideal.Quotient.mk _ (g1 π b₄ t κ)) ^ (2 * (n + 1)) := by
  rw [toRn_mk, map_mul, map_add, map_one, toNode_h1]
  exact TateOverlap.fn_dvd_g hm n

/-- `T01` over `T0` (through `ρ₀`). -/
@[reducible] def algT0T01 : Algebra (T0 π b₄ t κ) (T01 π b₄ t κ) :=
  (rho0 π b₄ t κ : T0 π b₄ t κ →+* T01 π b₄ t κ).toAlgebra

omit [IsNoetherianRing O] in
lemma towerT0T01 : letI := algT0T01 (π := π) (b₄ := b₄) (t := t) (κ := κ)
    IsScalarTower O (T0 π b₄ t κ) (T01 π b₄ t κ) :=
  letI := algT0T01 (π := π) (b₄ := b₄) (t := t) (κ := κ)
  IsScalarTower.of_algebraMap_eq fun o ↦ ((rho0 π b₄ t κ).commutes o).symm

/-- `T01n` over `T1n` (`ρ₁` at level `n`). -/
@[reducible] def alg1n (n : ℕ) : Algebra (T1n ϖ π b₄ t κ n) (T01n ϖ π b₄ t κ n) :=
  (rho1n ϖ π b₄ t κ n).toAlgebra

/-- `T01n` over `T0n` (`ρ₀` at level `n`). -/
@[reducible] def alg0n (n : ℕ) : Algebra (T0n ϖ π b₄ t κ n) (T01n ϖ π b₄ t κ n) :=
  (rho0n ϖ π b₄ t κ n).toAlgebra

omit [IsNoetherianRing O] in
lemma tower1n (n : ℕ) : letI := alg1n (ϖ := ϖ) (π := π) (b₄ := b₄) (t := t) (κ := κ) n
    IsScalarTower O (T1n ϖ π b₄ t κ n) (T01n ϖ π b₄ t κ n) :=
  letI := alg1n (ϖ := ϖ) (π := π) (b₄ := b₄) (t := t) (κ := κ) n
  IsScalarTower.of_algebraMap_eq fun o ↦ by
    change Ideal.Quotient.mk _ (algebraMap O (T01 π b₄ t κ) o) =
      Ideal.Quotient.mk _ (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (algebraMap O _ o))
    rw [← IsScalarTower.algebraMap_apply]

omit [IsNoetherianRing O] in
lemma tower0n (n : ℕ) : letI := alg0n (ϖ := ϖ) (π := π) (b₄ := b₄) (t := t) (κ := κ) n
    IsScalarTower O (T0n ϖ π b₄ t κ n) (T01n ϖ π b₄ t κ n) :=
  letI := alg0n (ϖ := ϖ) (π := π) (b₄ := b₄) (t := t) (κ := κ) n
  IsScalarTower.of_algebraMap_eq fun o ↦ by
    change Ideal.Quotient.mk _ (algebraMap O (T01 π b₄ t κ) o) =
      Ideal.Quotient.mk _ (rho0 π b₄ t κ (algebraMap O _ o))
    rw [AlgHom.commutes]

/-- The étale lifts over `D(1 + h)` as `O`-algebras. -/
@[reducible] def algOE0 (n : ℕ) : Algebra O (E0 Sp0 hϖ hker n).E :=
  ((algebraMap (B ϖ π b₄ t κ n) (E0 Sp0 hϖ hker n).E).comp
    (algebraMap O (B ϖ π b₄ t κ n))).toAlgebra

omit hθ in
lemma towerOE0 (n : ℕ) : letI := algOE0 hϖ hker Sp0 n
    IsScalarTower O (B ϖ π b₄ t κ n) (E0 Sp0 hϖ hker n).E :=
  letI := algOE0 hϖ hker Sp0 n
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

omit hθ [IsNoetherianRing O] in
lemma hq1T (n : ℕ) (r : T1n ϖ π b₄ t κ n) :
    EtaleTower.q (T01 π b₄ t κ) hϖ n (rho1n ϖ π b₄ t κ n r) =
      EtaleNil.red (RingHom.ker θ) (IsScalarTower.toAlgHom O (T1 π b₄ t κ) (T01 π b₄ t κ))
        (EtaleTower.q (T1 π b₄ t κ) hϖ n r) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [quotMap_mk, EtaleTower.q_mk, EtaleTower.q_mk, EtaleNil.red_mk]

omit hθ [IsNoetherianRing O] in
lemma hq0T (n : ℕ) (r : T0n ϖ π b₄ t κ n) :
    EtaleTower.q (T01 π b₄ t κ) hϖ n (rho0n ϖ π b₄ t κ n r) =
      EtaleNil.red (RingHom.ker θ) (rho0 π b₄ t κ) (EtaleTower.q (T0 π b₄ t κ) hϖ n r) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [quotMap_mk, EtaleTower.q_mk, EtaleTower.q_mk, EtaleNil.red_mk]

omit [IsNoetherianRing O] in
lemma hWs1T (n : ℕ) (x : T1n ϖ π b₄ t κ (n + 1)) :
    algebraMap (EtaleTower.Tn ϖ (T01 π b₄ t κ) (n + 1)) (EtaleTower.Tn ϖ (T01 π b₄ t κ) n)
      (rho1n ϖ π b₄ t κ (n + 1) x) =
    rho1n ϖ π b₄ t κ n (algebraMap (EtaleTower.Tn ϖ (T1 π b₄ t κ) (n + 1))
      (EtaleTower.Tn ϖ (T1 π b₄ t κ) n) x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

omit [IsNoetherianRing O] in
lemma hWs0T (n : ℕ) (x : T0n ϖ π b₄ t κ (n + 1)) :
    algebraMap (EtaleTower.Tn ϖ (T01 π b₄ t κ) (n + 1)) (EtaleTower.Tn ϖ (T01 π b₄ t κ) n)
      (rho0n ϖ π b₄ t κ (n + 1) x) =
    rho0n ϖ π b₄ t κ n (algebraMap (EtaleTower.Tn ϖ (T0 π b₄ t κ) (n + 1))
      (EtaleTower.Tn ϖ (T0 π b₄ t κ) n) x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

omit [IsNoetherianRing O] in
/-- A finite algebra is finite for any equal algebra structure. -/
lemma finite_of_eq {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (f : R →+* S) (hf : f = algebraMap R S) : letI := f.toAlgebra; Module.Finite R S := by
  subst hf
  rw [show (algebraMap R S).toAlgebra = ‹Algebra R S› from Algebra.algebra_ext _ _ fun _ ↦ rfl]
  infer_instance

omit [IsNoetherianRing O] in
/-- `T1` is finite over `O[X]` via `X ↦ h'`. -/
lemma finite_aeval_h1 : letI := (Polynomial.aeval (h1 π b₄ t κ) :
      Polynomial O →ₐ[O] T1 π b₄ t κ).toRingHom.toAlgebra
    Module.Finite (Polynomial O) (T1 π b₄ t κ) :=
  finite_of_eq _ (Polynomial.ringHom_ext (fun o ↦ by
    change Polynomial.aeval (h1 π b₄ t κ) (Polynomial.C o) =
      AdjoinRoot.of (G1 π b₄ t κ) (Polynomial.C o)
    rw [Polynomial.aeval_C, of_C]) (by
    change Polynomial.aeval (h1 π b₄ t κ) Polynomial.X =
      AdjoinRoot.of (G1 π b₄ t κ) Polynomial.X
    rw [Polynomial.aeval_X]))

omit [IsNoetherianRing O] in
/-- `T0` is finite over `O[X]` via `X ↦ h`. -/
lemma finite_aeval_h0 : letI := (Polynomial.aeval (h0 π b₄ t κ) :
      Polynomial O →ₐ[O] T0 π b₄ t κ).toRingHom.toAlgebra
    Module.Finite (Polynomial O) (T0 π b₄ t κ) :=
  finite_of_eq _ (Polynomial.ringHom_ext (fun o ↦ by
    change Polynomial.aeval (h0 π b₄ t κ) (Polynomial.C o) =
      AdjoinRoot.of (G0 π b₄ t κ) (Polynomial.C o)
    rw [Polynomial.aeval_C, of_C]) (by
    change Polynomial.aeval (h0 π b₄ t κ) Polynomial.X =
      AdjoinRoot.of (G0 π b₄ t κ) Polynomial.X
    rw [Polynomial.aeval_X]))

omit [IsNoetherianRing O] in
/-- `V₀ = D(h) ∪ D(1 + h)`. -/
lemma span_h0_c0 : Ideal.span {h0 π b₄ t κ, c0 π b₄ t κ} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : (1 : T0 π b₄ t κ) = c0 π b₄ t κ - h0 π b₄ t κ := by rw [c0]; ring
  rw [h]
  exact Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    (Ideal.subset_span (Set.mem_insert _ _))

omit hθ in
/-- The kernels of the successor maps of the étale lifts over `D(1 + h)`. -/
lemma hkE0 (n : ℕ) : letI := algOE0 hϖ hker Sp0 (n + 1)
    RingHom.ker (sE0 Sp0 hϖ hker n) =
      (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (E0 Sp0 hϖ hker (n + 1)).E) := by
  rw [ker_sE0, Ideal.map_map]
  rfl

/-- **The étale lifts of `C0` over `D(1 + h)`** as the piece of the covering over `D(c₀)`
(`NodeEtaleGlue.Piece0.ofEtale`). -/
def piece0 : NodeEtaleGlue.Piece0 θ (B ϖ π b₄ t κ) (EtaleTower.q (T0 π b₄ t κ) hϖ) Sp0.C
    (h0 π b₄ t κ) (c0 π b₄ t κ) (Ideal.Quotient.mk _ (h0 π b₄ t κ))
    (Ideal.Quotient.mk _ (c0 π b₄ t κ)) ϖ := by
  letI : ∀ n, Algebra O (E0 Sp0 hϖ hker n).E := algOE0 hϖ hker Sp0
  haveI : ∀ n, IsScalarTower O (B ϖ π b₄ t κ n) (E0 Sp0 hϖ hker n).E := towerOE0 hϖ hker Sp0
  haveI : ∀ n, IsScalarTower (T0 π b₄ t κ) (B ϖ π b₄ t κ (n + 1)) (B ϖ π b₄ t κ n) :=
    fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact NodeEtaleGlue.Piece0.ofEtale (fun n ↦ (E0 Sp0 hϖ hker n).E)
    (fun n ↦ (E0 Sp0 hϖ hker n).σ) (fun n ↦ (E0 Sp0 hϖ hker n).hb)
    (fun n ↦ (E0 Sp0 hϖ hker n).hfin) (fun _ ↦ rfl) (sE0 Sp0 hϖ hker)
    (Sp0.succ_algebraMap hϖ hker) (Sp0.σ_succ' hϖ hker) (surjective_sE0 Sp0 hϖ hker)
    (hkE0 hϖ hker Sp0)

/-- **The Tate covering over the chart `V₀` and the overlap datum** (`NodeEtaleGlue.Overlap`),
for any special-fibre covering `C0` of `V₀`, overlap datum `ω` and piece `P0` of the covering over
`D(1 + h)` (`NodeEtaleGlue.Piece0`: the étale lifts `piece0`, or a cusp patch). -/
def overlapP (C0 : Type u) [CommRing C0] [Algebra (T0s θ π b₄ t κ) C0] (ω : OmegaC hκ hπ Sp C0)
    (P0 : NodeEtaleGlue.Piece0 θ (B ϖ π b₄ t κ) (EtaleTower.q (T0 π b₄ t κ) hϖ) C0
      (h0 π b₄ t κ) (c0 π b₄ t κ) (Ideal.Quotient.mk _ (h0 π b₄ t κ))
      (Ideal.Quotient.mk _ (c0 π b₄ t κ)) ϖ) :
    NodeEtaleGlue.Overlap (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm) where
  B0' := T0 π b₄ t κ
  B' := B ϖ π b₄ t κ
  W0 := T01 π b₄ t κ
  algB0W0 := (inferInstance : Algebra (T1 π b₄ t κ) (T01 π b₄ t κ))
  algB0'W0 := algT0T01
  algOB0 := (inferInstance : Algebra O (T1 π b₄ t κ))
  algOW0 := inferInstance
  towerOB0W0 := (inferInstance : IsScalarTower O (T1 π b₄ t κ) (T01 π b₄ t κ))
  towerOB0'W0 := towerT0T01
  W := T01n ϖ π b₄ t κ
  algOW := fun _ ↦ inferInstance
  algBW := alg1n
  algB'W := alg0n
  towerOBW := tower1n
  towerOB'W := tower0n
  algW0W := fun _ ↦ inferInstance
  x0 := h0 π b₄ t κ
  c0 := c0 π b₄ t κ
  x1 := h1 π b₄ t κ
  g := g1 π b₄ t κ
  hW0 := (inferInstance : IsLocalization.Away (h1 π b₄ t κ) (T01 π b₄ t κ))
  hxW0 := by
    change rho0 π b₄ t κ (h0 π b₄ t κ) * _ = 1
    rw [rho0_h0, mul_comm]
    exact h1_mul_hinv π b₄ t κ
  kc := 2
  hcW0 := rho0_c0
  hx1g := Dvd.intro _ rfl
  hWn0 := isLocalization_rho0n ϖ π b₄ t κ
  hWn1 := isLocalization_rho1n ϖ π b₄ t κ
  hWB := fun _ _ ↦ rfl
  hWB' := fun _ _ ↦ rfl
  kg := fun n ↦ 2 * (n + 1)
  hfg := fn_dvd_g1 hκ hπ hm
  Bs' := T0s θ π b₄ t κ
  qB' := EtaleTower.q (T0 π b₄ t κ) hϖ
  Ws := T01s θ π b₄ t κ
  algBsWs := alg1s θ π b₄ t κ
  algBs'Ws := alg0s θ π b₄ t κ
  qW := EtaleTower.q (T01 π b₄ t κ) hϖ
  hq1 := hq1T hϖ
  hq0 := hq0T hϖ
  x0s := Ideal.Quotient.mk _ (h0 π b₄ t κ)
  c0s := Ideal.Quotient.mk _ (c0 π b₄ t κ)
  x1s := Ideal.Quotient.mk _ (h1 π b₄ t κ)
  gs := Ideal.Quotient.mk _ (g1 π b₄ t κ)
  hx0 := fun _ ↦ rfl
  hc0 := fun _ ↦ rfl
  hx1 := fun _ ↦ rfl
  hg := fun _ ↦ rfl
  hcg := by
    change Ideal.Quotient.mk _ (rho0 π b₄ t κ (c0 π b₄ t κ)) *
      Ideal.Quotient.mk _ (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (h1 π b₄ t κ)) ^ 2 =
        Ideal.Quotient.mk _ (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (g1 π b₄ t κ))
    rw [← map_pow, ← map_mul, rho0_c0]
  C0 := C0
  algWs1 := algC1x Sp.C1
  towerWs1 := towerC1x Sp.C1
  algWs0 := algC0x C0
  towerWs0 := towerC0x C0
  ω := ω
  hxc := span_h0_c0
  hW0' := isLocalization_rho0 π b₄ t κ
  finB0 := finite_aeval_h1
  finB0' := finite_aeval_h0
  surjB := fun _ ↦ Ideal.Quotient.mk_surjective
  surjB' := fun _ ↦ Ideal.Quotient.mk_surjective
  hfinE := fun n ↦ (TateGlue1.E1 hκ hπ hϖ hker Sp n).hfin
  algSuccB' := fun _ ↦ inferInstance
  towerOSuccB' := fun _ ↦ inferInstance
  towerB0'SuccB' := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  algSuccW := fun n ↦ (inferInstance :
    Algebra (EtaleTower.Tn ϖ (T01 π b₄ t κ) (n + 1)) (EtaleTower.Tn ϖ (T01 π b₄ t κ) n))
  hWs1 := hWs1T
  hWs0 := hWs0T
  ϖ := ϖ
  hOB0B := fun _ _ ↦ rfl
  hK := fun _ ↦ rfl
  killB := EtaleTower.kill (T1 π b₄ t κ)
  killB' := EtaleTower.kill (T0 π b₄ t κ)
  P0 := P0

/-- **The Tate covering over `V₀` étale outside the nodes** (`overlapP` with the étale lifts
`piece0` of `Sp0` over `D(1 + h)`). -/
def overlap (ω : Omega hκ hπ Sp Sp0) :
    NodeEtaleGlue.Overlap (TateGlue1.input hκ hπ hε hϖ π' hπ' hker Sp hm) :=
  overlapP hκ hπ hε hϖ π' hπ' hker Sp hm Sp0.C ω (piece0 (hϖ := hϖ) (hker := hker) (Sp0 := Sp0))

end

end TateGlue0

end SemistableReduction
