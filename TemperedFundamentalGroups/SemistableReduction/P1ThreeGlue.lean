/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeLevel
import TemperedFundamentalGroups.SemistableReduction.CuspInput
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Tower

/-!
# The M2 lift of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` to `ℙ¹_O` (MR13 A1: glueing, algebraisation)

Let `O` be a Noetherian ring with `θ : O ↠ k`, `ϖ ∈ ker θ`, `ker θ ⊆ (ϖ)`, `a ∈ O`, and consider
the model `h = t (t − 1) (t − a) : ℙ¹_t → ℙ¹_X` of `P1ThreeChart` (charts `V₀ = Spec R0`,
`R0 = O[t]`, containing the three cusps `t = 0, 1, a` over `X = 0`, and `V₁ = Spec R1`,
`V₁ = ℙ¹_t ∖ {0, 1, a}`, `s = 1/t`). A covering of the special fibre `ℙ¹_k` that is étale over
`ℙ¹_k ∖ {0, 1, ā}` and tamely ramified (Kummer) over `0, 1, ā` is given chart-wise by

* **`P1Three.Special1`** over `V₁`: a finite étale `R1/J`-algebra `C1` (`CuspChart.Special` with
  no marked points: the patch chart is `D(1)` with coordinate `1`);
* `S0 : CuspTower.CuspSpecial R0 1 X` over `V₀`: the covering `C0` with cusp factors `X^e = X̄`
  along `V(X̄) = {0} ⊔ {1} ⊔ {ā}` (`X = t (t − 1) (t − a)` is a uniformizer at the three cusps if
  `ā ≠ 0, 1`);
* **`ω : P1Three.OmegaC Sp S0.C0`**: the identification `C0[1/X̄] ≃ C1[1/Ȳ]` over the special
  fibre of the overlap.

Then:

* **`P1Three.input`** (a `NodeEtaleGlue.Input` over `V₁`: the trivial patch tower
  `CuspTower.tower` on `D(1)` and the étale lifts of `C1`) and **`P1Three.overlap`** (the
  `NodeEtaleGlue.Overlap` over `V₀`, whose piece over `D(1) = V₀` is the cusp patch
  `CuspTower.cuspPiece` along `X`);
* **`P1Three.system`**: the adic system of chart algebras of the covering on `ℙ¹_O`;
* **`P1Three.exists_algebraization`**: a coherent chart algebra on `ℙ¹_O` whose reductions modulo
  `ϖⁿ` are the levels of the covering (Grothendieck existence,
  `NodeEtaleGlue.Overlap.exists_algebraization`).

This is the formal lifting step of the "lifting half" of tame specialisation for
`U = ℙ¹ ∖ {three points}` ([SGA1] XIII, proof of Cor 2.12: the specialisation morphism
`π₁(U_K̄) → π₁^t(U_k)` is surjective, i.e. every tame covering of `U_k` lifts; there via
cohomological properness, XIII Cor 2.8; here by formal patching and algebraisation as in the
Tate case `TateGlue0.exists_algebraization_cusp`).
-/

universe u

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}

variable (O a) in
/-- The chart `V₁` as the patch chart `D(1)` (`CuspTower.Rc`). -/
abbrev Rc1 : Type u := CuspTower.Rc (R1 O a) 1

namespace CuspChart

variable (θ) (T : Type u) [CommRing T] [Algebra O T] (y s : T)

/-- **The special-fibre covering over a chart `T` with marked points `V(ȳ)`** (coordinate `s̄` at
the marked points): a finite `T/J`-algebra `C1`, étale over `D(ȳ)`, with an admissible covering
`cov` of the special fibre of `T[1/1]` without nodes and with cusp factors along `ȳ`,
`cov.C = C1[1/1]` (`ι₀`). (A variant of `CuspTower.CuspSpecial` with `s ≠ y`.) -/
structure Special where
  C1 : Type u
  [commRing : CommRing C1]
  [algebra : Algebra (Ts θ T) C1]
  finite : Module.Finite (Ts θ T) C1
  etale : (Localization.awayMap (algebraMap (Ts θ T) C1) (Ideal.Quotient.mk _ y)).Etale
  φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ (CuspTower.sC T 1 y))
  cov : Admissible.Covering φ₀
    (CuspTower.ψb (θ := θ) _ (CuspTower.sC T 1 y) (CuspTower.sC T 1 s))
  [noNodes : IsEmpty cov.ι]
  ι₀ : C1 →+* cov.C
  hι₀ : ∀ x, ι₀ (algebraMap (Ts θ T) C1 x) =
    algebraMap (Ts θ (CuspTower.Rc T 1)) cov.C (CuspTower.φsC T 1 θ x)
  hι : letI := ι₀.toAlgebra
    IsLocalization.Away (algebraMap (Ts θ T) C1 (Ideal.Quotient.mk _ 1)) cov.C

attribute [instance] Special.commRing Special.algebra Special.noNodes

end CuspChart

variable (O a θ) in
/-- **The special-fibre covering over `V₁ = ℙ¹ ∖ {0, 1, a}`** (`CuspChart.Special` for `R1` with
`y = s = 1`, i.e. no marked points): a finite `R1/J`-algebra, étale everywhere, with its
(trivially admissible) covering of `R1[1/1]/J`. -/
abbrev Special1 : Type (u + 1) := CuspChart.Special θ (R1 O a) 1 1

variable (Sp : Special1 O θ a) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing O]

/-- The (empty) deformation parameters of the Kummer factors. -/
def πc : Sp.cov.ι → O := fun j ↦ isEmptyElim j

instance : IsNoetherianRing (R1 O a) := AdjoinRoot.instIsNoetherianRing

instance : IsNoetherianRing (R0 O a) := AdjoinRoot.instIsNoetherianRing

/-- **The (trivial) tower of patches over `V₁`**: no marked points (coordinate `1`). -/
abbrev tower1 : LevelTower.Data (θ := θ) (Tn ϖ (Rc1 O a)) Sp.cov (πc Sp) :=
  CuspTower.tower _ hϖ (CuspTower.sC (R1 O a) 1 1) (CuspTower.sC (R1 O a) 1 1) Sp.cov (πc Sp) hker
    (CuspTower.isSMulRegular_s ϖ (R1 O a) 1 1 (fun n ↦ by rw [map_one]; exact IsSMulRegular.one _))

lemma hφs1 (n : ℕ) (x : Tn ϖ (R1 O a) n) :
    (tower1 Sp hϖ hker).e n (CuspTower.φsC (R1 O a) 1 θ (EtaleTower.q (R1 O a) hϖ n x)) =
      Ideal.Quotient.mk _ (letI := CuspTower.algBR ϖ (R1 O a) 1 n
        algebraMap (Tn ϖ (R1 O a) n) (Tn ϖ (Rc1 O a) n) x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact CuspTower.eqv_mk _ hϖ n _

/-- **The étale lifts of `C1`** (over `D(1) = V₁`) at level `n` (`EtaleTower.lift`). -/
def E1 (n : ℕ) : EtaleTower.Lift (R1 O a) hϖ Sp.C1 1 n :=
  haveI := Sp.finite
  EtaleTower.lift (R1 O a) hϖ Sp.C1 1 hker Sp.etale n

/-- The successor maps of the étale lifts `E1`. -/
def sE (n : ℕ) : (E1 Sp hϖ hker (n + 1)).E →+* (E1 Sp hϖ hker n).E :=
  letI := EtaleTower.algE (R1 O a) hϖ Sp.C1 1 (E1 Sp hϖ hker n)
  (EtaleTower.succ (R1 O a) hϖ Sp.C1 1 hker (E1 Sp hϖ hker (n + 1))
    (E1 Sp hϖ hker n) : (E1 Sp hϖ hker (n + 1)).E →+* _)

lemma hsE (n : ℕ) (x : Tn ϖ (R1 O a) (n + 1)) :
    sE Sp hϖ hker n (algebraMap _ (E1 Sp hϖ hker (n + 1)).E x) =
      algebraMap (Tn ϖ (R1 O a) n) _ (algebraMap (Tn ϖ (R1 O a) (n + 1)) (Tn ϖ (R1 O a) n) x) :=
  letI := EtaleTower.algE (R1 O a) hϖ Sp.C1 1 (E1 Sp hϖ hker n)
  (EtaleTower.succ (R1 O a) hϖ Sp.C1 1 hker (E1 Sp hϖ hker (n + 1))
    (E1 Sp hϖ hker n)).commutes x

lemma hσE (n : ℕ) (x : (E1 Sp hϖ hker (n + 1)).E) :
    (letI := EtaleTower.algC (R1 O a) hϖ Sp.C1 n;
      (E1 Sp hϖ hker n).σ (Ideal.Quotient.mk _ (sE Sp hϖ hker n x))) =
      (letI := EtaleTower.algC (R1 O a) hϖ Sp.C1 (n + 1);
        (E1 Sp hϖ hker (n + 1)).σ (Ideal.Quotient.mk _ x)) :=
  EtaleTower.σ_succ (R1 O a) hϖ Sp.C1 1 hker _ _ x

omit [IsNoetherianRing O] in
variable (O a) in
lemma span_one_one : Ideal.span {(1 : R1 O a), 1} = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span (Set.mem_insert _ _))

variable (ϖ) in
/-- The ideal `ϖⁿ⁺¹ R1` of the base chart. -/
abbrev K1 (n : ℕ) : Ideal (R1 O a) := (EtaleTower.Iv ϖ n).map (algebraMap O _)

lemma hkE (n : ℕ) : RingHom.ker (sE Sp hϖ hker n) =
    (K1 ϖ n).map ((algebraMap (Tn ϖ (R1 O a) (n + 1)) (E1 Sp hϖ hker (n + 1)).E).comp
      (algebraMap (R1 O a) (Tn ϖ (R1 O a) (n + 1)))) :=
  EtaleTower.ker_succ_base (R1 O a) hϖ Sp.C1 1 hker _ _

/-- **The covering over `V₁` as an input of the glueing** (`NodeEtaleGlue.Input`): the trivial
patches on `D(1) = V₁` and the étale lifts of `C1` on `D(1)`. -/
def input : NodeEtaleGlue.Input θ Sp.cov (πc Sp) where
  R := Tn ϖ (Rc1 O a)
  T := tower1 Sp hϖ hker
  B := Tn ϖ (R1 O a)
  algBR := CuspTower.algBR ϖ (R1 O a) 1
  towerOBR := CuspTower.towerBR ϖ (R1 O a) 1
  B0 := R1 O a
  a0 := 1
  b0 := 1
  hab := span_one_one O a
  away := CuspTower.isLocalization_BR ϖ (R1 O a) 1
  Bs := Ts θ (R1 O a)
  qB := EtaleTower.q (R1 O a) hϖ
  φs := CuspTower.φsC (R1 O a) 1 θ
  hφs := hφs1 Sp hϖ hker
  C1 := Sp.C1
  ι₀ := Sp.ι₀
  hι₀ := Sp.hι₀
  abar := Ideal.Quotient.mk _ 1
  bbar := Ideal.Quotient.mk _ 1
  ha := fun _ ↦ rfl
  hι := Sp.hι
  hbb := fun _ ↦ rfl
  E := fun n ↦ (E1 Sp hϖ hker n).E
  σE := fun n ↦ (E1 Sp hϖ hker n).σ
  hbE := fun n ↦ (E1 Sp hϖ hker n).hb
  kdiv := fun _ ↦ 1
  hdiv := fun _ ↦ by rw [pow_one]; exact dvd_refl _
  mB := fun n ↦ n + 1
  hJB := fun n ↦ EtaleTower.hJ hker n
  hBR := fun _ x ↦ by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  sE := sE Sp hϖ hker
  hsE := hsE Sp hϖ hker
  hσE := hσE Sp hϖ hker
  hsEs := fun n ↦ by
    letI := EtaleTower.algE (R1 O a) hϖ Sp.C1 1 (E1 Sp hϖ hker n)
    exact EtaleTower.surjective_succ (R1 O a) hϖ Sp.C1 1 hker _ _
  K := K1 ϖ
  hkR := fun n ↦ by
    rw [EtaleTower.ker_succ_T, K1, Ideal.map_map]
    refine congrArg (fun f ↦ Ideal.map f _) (RingHom.ext fun o ↦ ?_)
    change _ = quotMap _ _ (Ideal.Quotient.mk _ (algebraMap O (R1 O a) o))
    rw [quotMap_mk, AlgHom.commutes]
    rfl
  hkE := hkE Sp hϖ hker

/-! ### The chart `V₀` and the overlap -/

/-- **The type of the overlap datum** for a covering `C0` of the special fibre of `V₀`:
`C0[1/X̄] ≃ₐ C1[1/Ȳ]` over the special fibre `R01/J` of the overlap chart. -/
abbrev OmegaC (C0 : Type u) [CommRing C0] [Algebra (Ts θ (R0 O a)) C0] : Type u :=
  letI := algC0x a C0 (θ := θ)
  letI := algC1x a Sp.C1 (θ := θ)
  Localization.Away (algebraMap (Ts θ (R0 O a)) C0 (Ideal.Quotient.mk _ (x0 O a))) ≃ₐ[R01s O a θ]
    Localization.Away (algebraMap (Ts θ (R1 O a)) Sp.C1 (Ideal.Quotient.mk _ (y1 O a)))

/-- `R01` over `R0` (through `ρ₀`). -/
@[reducible] def algR0R01 : Algebra (R0 O a) (R01 O a) := (rho0 O a : R0 O a →+* R01 O a).toAlgebra

/-- `R01n` over `R1n` (`ρ₁` at level `n`). -/
@[reducible] def alg1n (n : ℕ) : Algebra (Tn ϖ (R1 O a) n) (Tn ϖ (R01 O a) n) :=
  (rho1n ϖ a n).toAlgebra

/-- `R01n` over `R0n` (`ρ₀` at level `n`). -/
@[reducible] def alg0n (n : ℕ) : Algebra (Tn ϖ (R0 O a) n) (Tn ϖ (R01 O a) n) :=
  (rho0n ϖ a n).toAlgebra

omit [IsNoetherianRing O] in
lemma tower1n (n : ℕ) : letI := alg1n (a := a) (ϖ := ϖ) n
    IsScalarTower O (Tn ϖ (R1 O a) n) (Tn ϖ (R01 O a) n) :=
  letI := alg1n (a := a) (ϖ := ϖ) n
  IsScalarTower.of_algebraMap_eq fun o ↦ by
    change Ideal.Quotient.mk _ (algebraMap O (R01 O a) o) =
      Ideal.Quotient.mk _ (algebraMap (R1 O a) (R01 O a) (algebraMap O _ o))
    rw [← IsScalarTower.algebraMap_apply]

omit [IsNoetherianRing O] in
lemma tower0n (n : ℕ) : letI := alg0n (a := a) (ϖ := ϖ) n
    IsScalarTower O (Tn ϖ (R0 O a) n) (Tn ϖ (R01 O a) n) :=
  letI := alg0n (a := a) (ϖ := ϖ) n
  IsScalarTower.of_algebraMap_eq fun o ↦ by
    change Ideal.Quotient.mk _ (algebraMap O (R01 O a) o) =
      Ideal.Quotient.mk _ (rho0 O a (algebraMap O _ o))
    rw [AlgHom.commutes]

omit hθ [IsNoetherianRing O] in
lemma hq1T (n : ℕ) (r : Tn ϖ (R1 O a) n) :
    EtaleTower.q (R01 O a) hϖ n (rho1n ϖ a n r) =
      EtaleNil.red (RingHom.ker θ) (IsScalarTower.toAlgHom O (R1 O a) (R01 O a))
        (EtaleTower.q (R1 O a) hϖ n r) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [quotMap_mk, EtaleTower.q_mk, EtaleTower.q_mk, EtaleNil.red_mk]

omit hθ [IsNoetherianRing O] in
lemma hq0T (n : ℕ) (r : Tn ϖ (R0 O a) n) :
    EtaleTower.q (R01 O a) hϖ n (rho0n ϖ a n r) =
      EtaleNil.red (RingHom.ker θ) (rho0 O a) (EtaleTower.q (R0 O a) hϖ n r) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [quotMap_mk, EtaleTower.q_mk, EtaleTower.q_mk, EtaleNil.red_mk]

omit [IsNoetherianRing O] in
lemma hWs1T (n : ℕ) (x : Tn ϖ (R1 O a) (n + 1)) :
    algebraMap (Tn ϖ (R01 O a) (n + 1)) (Tn ϖ (R01 O a) n) (rho1n ϖ a (n + 1) x) =
    rho1n ϖ a n (algebraMap (Tn ϖ (R1 O a) (n + 1)) (Tn ϖ (R1 O a) n) x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

omit [IsNoetherianRing O] in
lemma hWs0T (n : ℕ) (x : Tn ϖ (R0 O a) (n + 1)) :
    algebraMap (Tn ϖ (R01 O a) (n + 1)) (Tn ϖ (R01 O a) n) (rho0n ϖ a (n + 1) x) =
    rho0n ϖ a n (algebraMap (Tn ϖ (R0 O a) (n + 1)) (Tn ϖ (R0 O a) n) x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

omit [IsNoetherianRing O] in
lemma rho0_one_mul : rho0 O a 1 * algebraMap (R1 O a) (R01 O a) (y1 O a) ^ 1 =
    algebraMap (R1 O a) (R01 O a) (y1 O a) := by
  rw [map_one, one_mul, pow_one]

omit [IsNoetherianRing O] in
variable (O a) in
lemma span_x0_one : Ideal.span {x0 O a, (1 : R0 O a)} = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

variable (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ)) (ω : OmegaC Sp S0.C0)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The covering over `V₀` and the overlap datum** (`NodeEtaleGlue.Overlap`): the second chart
`V₀ = Spec R0` with levels `R0/ϖⁿ⁺¹`, the overlap `R01` with its levels, `x₀ = X`, `c₀ = 1`,
`x₁ = g = Y`, and as the piece over `D(c₀) = V₀` the cusp patch of `S0` along `X`. -/
def overlap : NodeEtaleGlue.Overlap (input Sp hϖ hker) where
  B0' := R0 O a
  B' := Tn ϖ (R0 O a)
  W0 := R01 O a
  algB0W0 := (inferInstance : Algebra (R1 O a) (R01 O a))
  algB0'W0 := algR0R01
  algOB0 := (inferInstance : Algebra O (R1 O a))
  algOW0 := inferInstance
  towerOB0W0 := (inferInstance : IsScalarTower O (R1 O a) (R01 O a))
  towerOB0'W0 := towerR0R01 O a
  W := Tn ϖ (R01 O a)
  algOW := fun _ ↦ inferInstance
  algBW := alg1n
  algB'W := alg0n
  towerOBW := tower1n
  towerOB'W := tower0n
  algW0W := fun _ ↦ inferInstance
  x0 := x0 O a
  c0 := 1
  x1 := y1 O a
  g := y1 O a
  hW0 := (inferInstance : IsLocalization.Away (y1 O a) (R01 O a))
  hxW0 := by
    change rho0 O a (x0 O a) * _ = 1
    rw [rho0_x0, mul_comm]
    exact y1_mul_yinv O a
  kc := 1
  hcW0 := rho0_one_mul
  hx1g := dvd_refl _
  hWn0 := isLocalization_rho0n ϖ a
  hWn1 := isLocalization_rho1n ϖ a
  hWB := fun _ _ ↦ rfl
  hWB' := fun _ _ ↦ rfl
  kg := fun _ ↦ 1
  hfg := fun _ ↦ by
    change Ideal.Quotient.mk _ (algebraMap (R1 O a) (Rc1 O a) 1) ∣ _
    rw [map_one, map_one]
    exact one_dvd _
  Bs' := Ts θ (R0 O a)
  qB' := EtaleTower.q (R0 O a) hϖ
  Ws := R01s O a θ
  algBsWs := alg1s O a θ
  algBs'Ws := alg0s O a θ
  qW := EtaleTower.q (R01 O a) hϖ
  hq1 := hq1T hϖ
  hq0 := hq0T hϖ
  x0s := Ideal.Quotient.mk _ (x0 O a)
  c0s := Ideal.Quotient.mk _ 1
  x1s := Ideal.Quotient.mk _ (y1 O a)
  gs := Ideal.Quotient.mk _ (y1 O a)
  hx0 := fun _ ↦ rfl
  hc0 := fun _ ↦ rfl
  hx1 := fun _ ↦ rfl
  hg := fun _ ↦ rfl
  hcg := by
    change Ideal.Quotient.mk _ (rho0 O a 1) *
      Ideal.Quotient.mk _ (algebraMap (R1 O a) (R01 O a) (y1 O a)) ^ 1 =
        Ideal.Quotient.mk _ (algebraMap (R1 O a) (R01 O a) (y1 O a))
    rw [← map_pow, ← map_mul, rho0_one_mul]
  C0 := S0.C0
  algWs1 := algC1x a Sp.C1
  towerWs1 := towerC1x a Sp.C1
  algWs0 := algC0x a S0.C0
  towerWs0 := towerC0x a S0.C0
  ω := ω
  hxc := span_x0_one O a
  hW0' := isLocalization_rho0 O a
  finB0 := finite_aeval_y1 O a
  finB0' := finite_aeval_x0 O a
  surjB := fun _ ↦ Ideal.Quotient.mk_surjective
  surjB' := fun _ ↦ Ideal.Quotient.mk_surjective
  hfinE := fun n ↦ (E1 Sp hϖ hker n).hfin
  algSuccB' := fun _ ↦ inferInstance
  towerOSuccB' := fun _ ↦ inferInstance
  towerB0'SuccB' := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  algSuccW := fun n ↦ (inferInstance :
    Algebra (EtaleTower.Tn ϖ (R01 O a) (n + 1)) (EtaleTower.Tn ϖ (R01 O a) n))
  hWs1 := hWs1T
  hWs0 := hWs0T
  ϖ := ϖ
  hOB0B := fun _ _ ↦ rfl
  hK := fun _ ↦ rfl
  killB := EtaleTower.kill (R1 O a)
  killB' := EtaleTower.kill (R0 O a)
  P0 := CuspTower.cuspPiece S0 hϖ hker (isSMulRegular_x0 ϖ a) hO

/-- **The adic system of chart algebras on `ℙ¹_O` of the covering.** -/
abbrev system : ProjectiveLine.AdicChartAlgSystem (Ideal.span {ϖ}) :=
  (overlap Sp hϖ hker S0 ω hO).system hθ.out hO

/-- **Algebraization of the covering** (MR13 A1): a coherent chart algebra on `ℙ¹_O` (finite over
both charts of `ℙ¹_O`) whose reductions modulo `ϖⁿ` are the levels of the lift of the tame
covering of `ℙ¹_k ∖ {0, 1, ā}` given by `Sp`, `S0`, `ω`. -/
theorem exists_algebraization [IsAdicComplete (Ideal.span {ϖ}) O] :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite (Polynomial O) (Module.AEval' N.x0))
      (_ : Module.Finite (Polynomial O) (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n), ((system Sp hϖ hker S0 ω hO).tr h).comp (α n) = α m) ∧
      ∀ n, B.IsHom ((system Sp hϖ hker S0 ω hO).alg n) (α n) := by
  haveI : IsAdicComplete (Ideal.span {(overlap Sp hϖ hker S0 ω hO).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  exact (overlap Sp hϖ hker S0 ω hO).exists_algebraization hθ.out hO

end

end P1Three

end SemistableReduction
