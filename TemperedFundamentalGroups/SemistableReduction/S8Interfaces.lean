/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.BallTree

/-!
# S8.A: the local inputs of the global improvement argument (open interfaces)

Blueprint §9.10 (S8.A–S8.C), §9.12 (O6, O10 and the rows listed below). This file contains only
**definitions**: the ball-level forms of "good residue disc" and "exhausting disc", and the
precise statements of the local results consumed by the global argument of [AW §2.5]
(`S8Global`). None of them is assumed anywhere as an axiom. `W7.statement_of_interfaces` takes them
as explicit hypotheses, and each is recorded in Blueprint §9.12 as **open** until its owner
discharges it.

Setting: `C` algebraically closed non-archimedean, `char C = 0`, `‖p‖ < 1`, not complete; `F` a
finite extension of `C(x)`.

## Ball-level predicates

* `DiscGood a hc F`: every point over the residue point `t̄ = 0` of the normalized chart
  `O_C[t]`, `t = (x - a)/c` (i.e. over the open disc `|x - a| < |c|`), is smooth
  (`SmoothVertex.IsDiscSmooth`);
* `BallGood F B`: `DiscGood` for **every** representation `B = ball a ‖c‖` of the open ball `B`;
* `EdgeGood F E G`: for discs `E ⊊ G`, every point over the node of the annulus between `E` and
  `G` is an ordinary double point (`AffineTwist.IsExhausting`, for every representation
  `E = closedBall a ‖c c'‖`, `G = closedBall a ‖c‖`); "`E` is exhausting in the residue ball of `G`
  containing `E`";
* `IsMinExh F b hc D`: `D` is the smallest exhausting disc in `ball b ‖c‖`;
* `InftyChartGood a hc F`: every point over `∞` of the disc `closedBall a ‖c‖` is smooth;
* `Brk F D D'`: the **breaks** of the segment `D ⊆ D'`: discs `D ⊊ G ⊊ D'` over which no good
  edge of the segment passes.

## Interfaces (Blueprint §9.12)

* `S8BMin` (S8.B, [AW Thm 2.6], owner S8.5 agent): for `F` Galois over `C(x)`, a bad residue ball
  contains a smallest exhausting disc;
* `R5Measure` (R5, [AW Def 2.5, Lemma 2.6, §2.5], owner S8.5 agent): a measure on bad residue balls
  decreasing from a bad ball to every bad residue ball of its smallest exhausting disc
  (`(δ, -m)` encoded in `ℕ`, `m ≤ δ + 1`);
* `FiniteBad` (S7.7-type finiteness of singular points): a disc has only finitely many bad residue
  balls;
* `InftyGoodIface` (S8.2 at the classical point `∞` + R1): the residue class at `∞` of a large disc
  is good;
* `EdgeRepair` (O10, owner R4 agent): the breaks of a segment are finite, and every sub-edge
  containing no break is good;
* `TransportFor`: `BallGood` and `EdgeGood` are invariant under isometric automorphisms `τ` of
  `C` extending to `τ`-semilinear automorphisms of `F` (**proved**, `S8A.Transport.transportFor`);
* `S8CReduction` (S8.C, [AW Prop 2.1], L1 A1–A6, owner S8.5/L1): a finite family of extensions
  embeds into one Galois extension `F''` of `C(x)` such that semistability of a Gauss tree for
  `F''` implies it for every member, and `τ`-semilinear automorphisms of the family lift to `F''`.
-/

universe u v

open Metric

namespace SemistableReduction

namespace S8A

open GaussTube DiscCount AffineTwist SmoothVertex BallTree

section Predicates

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- Every point over the open disc `|x - a| < |c|` (the residue point `t̄ = 0` of the normalized
chart `O_C[t]`, `t = (x - a)/c`) is smooth. -/
def DiscGood (a : C) {c : C} (hc : c ≠ 0) : Prop :=
  ∀ P' : Ideal (DRint (0 : C) 1 (Aff a c hc F)), P'.IsMaximal →
    P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff a c hc F))) =
      discIdeal (0 : C) 1 → IsDiscSmooth P'

/-- Every point over the residue class at `∞` of the disc `closedBall a ‖c‖` (the residue point
of the normalized chart `O_C[c/(x - a)]`) is smooth. -/
def InftyChartGood (a : C) {c : C} (hc : c ≠ 0) : Prop :=
  ∀ P' : Ideal (DRint (0 : C) 1 (GaussTube.Inv (1 : C) one_ne_zero (Aff a c hc F))),
    P'.IsMaximal →
    P'.comap (algebraMap (discRing (0 : C) 1)
      (DRint (0 : C) 1 (GaussTube.Inv (1 : C) one_ne_zero (Aff a c hc F)))) =
        discIdeal (0 : C) 1 → IsDiscSmooth P'

/-- The open ball `B` is **good**: every point over it is smooth (for every representation). -/
def BallGood (B : Set C) : Prop :=
  ∀ (a c : C) (hc : c ≠ 0), B = ball a ‖c‖ → DiscGood F a hc

/-- The edge `E ⊊ G` is **good**: `E` is exhausting in the residue ball of `G` containing `E` (for
every representation `E = closedBall a ‖c c'‖`, `G = closedBall a ‖c‖`). -/
def EdgeGood (E G : Set C) : Prop :=
  ∀ (a c c' : C) (hc : c ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0),
    E = closedBall a ‖c * c'‖ → G = closedBall a ‖c‖ → IsExhausting a hc hc' hc0' F

/-- `D` is the **smallest exhausting disc** in the open ball `ball b ‖c‖`. -/
def IsMinExh (b : C) {c : C} (_hc : c ≠ 0) (D : Set C) : Prop :=
  IsDisc D ∧ D ⊆ ball b ‖c‖ ∧ EdgeGood F D (closedBall b ‖c‖) ∧
    ∀ D', IsDisc D' → D' ⊆ ball b ‖c‖ → EdgeGood F D' (closedBall b ‖c‖) → D ⊆ D'

/-- `B` is an open **residue ball** of the disc `D`. -/
def IsResBall (D B : Set C) : Prop :=
  ∃ a b c : C, c ≠ 0 ∧ D = closedBall a ‖c‖ ∧ b ∈ D ∧ B = ball b ‖c‖

/-- The **breaks** of the segment `D ⊆ D'`: the discs strictly between `D` and `D'` over which no
good edge `G₁ ⊊ G ⊊ G₂` of the segment passes. -/
def Brk (D D' : Set C) : Set (Set C) :=
  {G | IsDisc G ∧ D ⊂ G ∧ G ⊂ D' ∧ ¬ ∃ G₁ G₂ : Set C, IsDisc G₁ ∧ IsDisc G₂ ∧ D ⊆ G₁ ∧
    G₁ ⊂ G ∧ G ⊂ G₂ ∧ G₂ ⊆ D' ∧ EdgeGood F G₁ G₂}

end Predicates

section Field

variable (C : Type*) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- **S8.B** ([AW Thm 2.6]) for `F`: a bad residue ball contains a smallest exhausting disc. -/
def S8BMinFor : Prop :=
  ∀ (b c : C) (hc : c ≠ 0), ¬ BallGood F (ball b ‖c‖) → ∃ D, IsMinExh F b hc D

/-- **R5** ([AW Lemma 2.6, §2.5]) for `F`: a measure on bad residue balls which decreases from a
bad ball to every bad residue ball of its smallest exhausting disc. -/
def R5MeasureFor : Prop :=
  ∃ μ : Set C → ℕ, ∀ (b c : C) (hc : c ≠ 0) (D : Set C), ¬ BallGood F (ball b ‖c‖) →
    IsMinExh F b hc D → ∀ B', IsResBall D B' → ¬ BallGood F B' → μ B' < μ (ball b ‖c‖)

/-- **Finiteness of bad residue balls** for `F`. -/
def FiniteBadFor : Prop :=
  ∀ D : Set C, IsDisc D → {B | IsResBall D B ∧ ¬ BallGood F B}.Finite

/-- **The residue class at `∞` of a large disc is good** for `F`. -/
def InftyGoodFor : Prop :=
  ∃ R₀ : ℝ, ∀ (a c : C) (hc : c ≠ 0), R₀ ≤ ‖c‖ → ‖a‖ ≤ ‖c‖ → InftyChartGood F a hc

/-- **EdgeRepair** (O10) for `F`: the breaks of a segment are finite, and every sub-edge of the
segment containing no break is good. -/
def EdgeRepairFor : Prop :=
  ∀ D D' : Set C, IsDisc D → IsDisc D' → D ⊆ D' → (Brk F D D').Finite ∧
    ∀ G₁ G₂ : Set C, IsDisc G₁ → IsDisc G₂ → D ⊆ G₁ → G₁ ⊂ G₂ → G₂ ⊆ D' →
      (∀ G ∈ Brk F D D', ¬ (G₁ ⊂ G ∧ G ⊂ G₂)) → EdgeGood F G₁ G₂

/-- `σ` is a `τ`-semilinear automorphism of `F` (over the action of `τ` on the coefficients of
`C(x)`). -/
def IsSemilinear (τ : C ≃+* C) (σ : F ≃+* F) : Prop :=
  ∀ φ : RatFunc C,
    σ (algebraMap (RatFunc C) F φ) = algebraMap (RatFunc C) F (ratFuncMap τ.toRingHom φ)

/-- **Transport** for `F`: goodness of balls and edges is invariant under isometric automorphisms of
`C` extending to semilinear automorphisms of `F`. -/
def TransportFor : Prop :=
  ∀ (τ : C ≃+* C), (∀ z, ‖τ z‖ = ‖z‖) → ∀ σ : F ≃+* F, IsSemilinear C F τ σ →
    (∀ B : Set C, BallGood F (τ '' B) ↔ BallGood F B) ∧
    (∀ E G : Set C, EdgeGood F (τ '' E) (τ '' G) ↔ EdgeGood F E G)

end Field

/-! ### The interfaces, quantified over all bases and Galois extensions -/

/-- The local inputs for Galois extensions (S8.B, R5, finiteness, `∞`, EdgeRepair). -/
structure GaloisInputs : Prop where
  s8b : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F] [IsGalois (RatFunc C) F], S8BMinFor C F
  r5 : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F] [IsGalois (RatFunc C) F], R5MeasureFor C F
  finiteBad : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], FiniteBadFor C F
  infty : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], InftyGoodFor C F
  edgeRepair : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F], EdgeRepairFor C F

/-- **S8.C** ([AW Prop 2.1], L1): a finite family of finite extensions of `C(x)` embeds into one
finite Galois extension `F''` such that every Gauss tree semistable for `F''` is semistable for
every member, and every `τ`-semilinear automorphism of the family (isometric `τ`) lifts to a
`τ`-semilinear automorphism of `F''`. -/
def S8CReduction : Prop :=
  ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
    (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (κ : Type) [Fintype κ] (F' : κ → Type v) [∀ k, Field (F' k)]
    [∀ k, Algebra (RatFunc C) (F' k)] [∀ k, Algebra C (F' k)]
    [∀ k, IsScalarTower C (RatFunc C) (F' k)] [∀ k, FiniteDimensional (RatFunc C) (F' k)],
    ∃ (F'' : Type u) (_ : Field F'') (_ : Algebra (RatFunc C) F'') (_ : Algebra C F'')
      (_ : IsScalarTower C (RatFunc C) F'') (_ : FiniteDimensional (RatFunc C) F'')
      (_ : IsGalois (RatFunc C) F''),
      (∀ (ι : Type) [Fintype ι] (a c : ι → C) (hc : ∀ i, c i ≠ 0),
        W7.IsSemistableTree a c hc F'' → ∀ k, W7.IsSemistableTree a c hc (F' k)) ∧
      ∀ τ : C ≃+* C, (∀ z, ‖τ z‖ = ‖z‖) →
        (∃ σ : (Π k, F' k) ≃+* (Π k, F' k), ∀ (φ : RatFunc C) (k : κ),
          σ (fun k' ↦ algebraMap (RatFunc C) (F' k') φ) k =
            algebraMap (RatFunc C) (F' k) (ratFuncMap τ.toRingHom φ)) →
        ∃ σ'' : F'' ≃+* F'', IsSemilinear C F'' τ σ''

end S8A

end SemistableReduction
