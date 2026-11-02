/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateCovering
import TemperedFundamentalGroups.Andre.ProjPoints
import TemperedFundamentalGroups.SemistableReduction.W10Scheme

/-!
# The `4`-gon model of `E_{q²}` over the `2`-gon model of `E_q`: its special fibre

Let `E_Q` (`Q = q² = s⁴`) be a Tate curve with Tate data `π = s`, `a₄ = π² b₄`, `a₆ = π² b₆`,
`T = (x_T, y_T)` its `2`-torsion point `u = q`, `P₁ = (x₁, y₁)` a point and
`P₂ = P₁ + T = (x₂, y₂)`.
The point `[x₁ : y₁ : x₂ : y₂ : π]` of `ℙ⁴` satisfies (with `x_T = π ε`, `C_T = π² γ`,
`x(P + T) − x_T = C_T / (x − x_T)`):

* the Tate cubics `F₁ = cub 0 1`, `F₂ = cub 2 3` of `E_Q` in the coordinates `[x : y : π]`;
* `Q₃ = (X₀ − ε X₄)(X₂ − ε X₄) − γ X₄²` (`(x₁ − x_T)(x₂ − x_T) = C_T`);
* `Q₄ = (2X₃ + X₂)(X₀ − ε X₄) + (2X₁ + X₀)(X₂ − ε X₄)` (`z₂(x₁ − x_T) + z₁(x₂ − x_T) = 0`,
  `z = y + x/2`);
* `Q₅ = (2X₁ + X₀)(2X₃ + X₂) + γ (4π X₄ (X₀ + X₂) + (4πε + 1) X₄²)`
  (`z₁ z₂ + C_T (x₁ + x₂ + x_T + 1/4) = 0`).

This file is generic: `O` is any commutative ring and `P` any prime ideal of `O[X₀, …, X₄]`
containing these five polynomials and `π, b₆, ε` (a point of the special fibre when `O` is local
and `π, b₆, ε ∈ 𝔪`), with `2` and `γ` units.

* `FourGon.mem_pieces`: `P` lies on one of the four lines of the `4`-gon
  `L_c = V(X₄, X₂, X₃)`, `G₊ = V(X₁, X₂ + X₃)`, `L_b = V(X₄, X₀, X₁)`, `G₋ = V(X₀ + X₁, X₃)`;
* `FourGon.memA_and_memB_iff`: the halves `A = L_c ∪ G₊` and `B = L_b ∪ G₋` meet exactly in the
  points `Cp = V(X₀, X₁, X₄, X₂ + X₃)` and `Cq = V(X₂, X₃, X₄, X₀ + X₁)`;
* `FourGon.decomp`: hence a `TateCovering.Decomp` of every space mapping continuously to `ℙ⁴_O`
  through such points (the universal `ℤ`-chain of the `4`-gon is its `toCode`);
* `ProjScheme.mem_imageι_of_evalHom_eq_zero`: a homogeneous polynomial vanishing at the
  coordinates `f` vanishes at every point of the projective model `projModelCode O f`.

The application (TFGD-plan, "Run 4"): the model of the level `K(E_{q²})` whose special fibre is
the `4`-gon, on which the deck involution (translation by `T`, `X₀ ↔ X₂`, `X₁ ↔ X₃`) swaps the
halves; it is the geometric input of `ZM 0` in `iut`.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace TemperedFundamentalGroups

namespace FourGon

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O]

set_option hygiene false in
local notation "R5" => MvPolynomial (Fin (4 + 1)) O

/-! ### The equations -/

variable (π b₄ b₆ ε γ : O)

/-- The Tate cubic `v²w + uvw − πu³ − πb₄uw² − b₆w³` on the coordinates `(X a, X b, X 4)`. -/
def cub (a b : Fin (4 + 1)) : R5 :=
  X b ^ 2 * X 4 + X a * X b * X 4 - C π * X a ^ 3 - C (π * b₄) * X a * X 4 ^ 2 - C b₆ * X 4 ^ 3

/-- `Q₃ = (X₀ − ε X₄)(X₂ − ε X₄) − γ X₄²`. -/
def Q₃ : R5 := (X 0 - C ε * X 4) * (X 2 - C ε * X 4) - C γ * X 4 ^ 2

/-- `Q₄ = (2X₃ + X₂)(X₀ − ε X₄) + (2X₁ + X₀)(X₂ − ε X₄)`. -/
def Q₄ : R5 := (2 * X 3 + X 2) * (X 0 - C ε * X 4) + (2 * X 1 + X 0) * (X 2 - C ε * X 4)

/-- `Q₅ = (2X₁ + X₀)(2X₃ + X₂) + γ (4π X₄ (X₀ + X₂) + (4πε + 1) X₄²)`. -/
def Q₅ : R5 :=
  (2 * X 1 + X 0) * (2 * X 3 + X 2) +
    C γ * (C (4 * π) * X 4 * (X 0 + X 2) + C (4 * π * ε + 1) * X 4 ^ 2)

/-- The five equations hold at a point (a prime ideal). -/
structure Rels (P : Ideal R5) : Prop where
  cub₁ : cub π b₄ b₆ 0 1 ∈ P
  cub₂ : cub π b₄ b₆ 2 3 ∈ P
  q₃ : Q₃ ε γ ∈ P
  q₄ : Q₄ ε ∈ P
  q₅ : Q₅ π ε γ ∈ P

/-! ### The special fibre: the four lines and the two halves -/

section Points

variable {π b₄ b₆ ε γ} {P : Ideal R5} [hP : P.IsPrime]

lemma mem_of_unit_mul {u : O} (hu : IsUnit u) {g : R5} (h : C u * g ∈ P) : g ∈ P :=
  (hP.mem_or_mem h).resolve_left fun h' => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (hu.map C))

omit hP in
lemma cub_reduce {a b : Fin (4 + 1)} (h : cub π b₄ b₆ a b ∈ P) (hπ : C π ∈ P) (hb : C b₆ ∈ P) :
    X 4 * (X b * (X a + X b)) ∈ P := by
  have e : X 4 * (X b * (X a + X b)) = cub π b₄ b₆ a b +
      C π * (X a ^ 3 + C b₄ * X a * X 4 ^ 2) + C b₆ * X 4 ^ 3 := by
    simp only [cub, map_mul]
    ring
  rw [e]
  exact P.add_mem (P.add_mem h (P.mul_mem_right _ hπ)) (P.mul_mem_right _ hb)

omit hP in
lemma q₃_reduce (h : Q₃ ε γ ∈ P) (hε : C ε ∈ P) : X 0 * X 2 - C γ * X 4 ^ 2 ∈ P := by
  have e : X 0 * X 2 - C γ * X 4 ^ 2 =
      Q₃ ε γ + C ε * (X 4 * X 0 + X 4 * X 2 - C ε * X 4 ^ 2) := by
    simp only [Q₃]
    ring
  rw [e]
  exact P.add_mem h (P.mul_mem_right _ hε)

omit hP in
lemma q₄_reduce (h : Q₄ ε ∈ P) (hε : C ε ∈ P) :
    X 0 * (2 * X 3 + X 2) + X 2 * (2 * X 1 + X 0) ∈ P := by
  have e : X 0 * (2 * X 3 + X 2) + X 2 * (2 * X 1 + X 0) =
      Q₄ ε + C ε * (X 4 * (2 * X 3 + X 2) + X 4 * (2 * X 1 + X 0)) := by
    simp only [Q₄]
    ring
  rw [e]
  exact P.add_mem h (P.mul_mem_right _ hε)

omit hP in
lemma q₅_reduce (h : Q₅ π ε γ ∈ P) (hπ : C π ∈ P) :
    (2 * X 1 + X 0) * (2 * X 3 + X 2) + C γ * X 4 ^ 2 ∈ P := by
  have e : (2 * X 1 + X 0) * (2 * X 3 + X 2) + C γ * X 4 ^ 2 =
      Q₅ π ε γ - C π * (C γ * (4 * X 4 * (X 0 + X 2) + 4 * C ε * X 4 ^ 2)) := by
    simp only [Q₅, map_mul, map_add, map_one, map_ofNat]
    ring
  rw [e]
  exact P.sub_mem h (P.mul_mem_right _ hπ)

lemma two_mul_mem {g : R5} (h2 : IsUnit (2 : O)) (h : 2 * g ∈ P) : g ∈ P := by
  refine mem_of_unit_mul h2 ?_
  rwa [map_ofNat]

/-- `X₀ X₂ + γ X₄² ∈ P` and `X₀ X₂ − γ X₄² ∈ P` force `X₄ ∈ P`. -/
lemma X4_mem_of (h2 : IsUnit (2 : O)) (hγ : IsUnit γ) (h₁ : X 0 * X 2 + C γ * X 4 ^ 2 ∈ P)
    (h₂ : X 0 * X 2 - C γ * X 4 ^ 2 ∈ P) : (X 4 : R5) ∈ P := by
  have h : C (2 * γ) * X 4 ^ 2 ∈ P := by
    have e : (C (2 * γ) * X 4 ^ 2 : R5) =
        (X 0 * X 2 + C γ * X 4 ^ 2) - (X 0 * X 2 - C γ * X 4 ^ 2) := by
      simp only [map_mul, map_ofNat]
      ring
    rw [e]
    exact P.sub_mem h₁ h₂
  exact hP.mem_of_pow_mem 2 (mem_of_unit_mul (h2.mul hγ) h)

/-- The line `L_c = V(X₄, X₂, X₃)` (the circle `|u| = 1`, over the line `C` of the `2`-gon). -/
def Lc (P : Ideal R5) : Prop := X 4 ∈ P ∧ X 2 ∈ P ∧ X 3 ∈ P

/-- The conic `G₊ = V(X₁, X₂ + X₃)` (the circle `|u| = |s|`, over the conic `E'`). -/
def Gp (P : Ideal R5) : Prop := X 1 ∈ P ∧ X 2 + X 3 ∈ P

/-- The line `L_b = V(X₄, X₀, X₁)` (the circle `|u| = |s|²`, over `C`). -/
def Lb (P : Ideal R5) : Prop := X 4 ∈ P ∧ X 0 ∈ P ∧ X 1 ∈ P

/-- The conic `G₋ = V(X₀ + X₁, X₃)` (the circle `|u| = |s|³`, over `E'`). -/
def Gm (P : Ideal R5) : Prop := X 0 + X 1 ∈ P ∧ X 3 ∈ P

/-- **Every point of the special fibre lies on the `4`-gon** `L_c ∪ G₊ ∪ L_b ∪ G₋`. -/
theorem mem_pieces (hR : Rels π b₄ b₆ ε γ P) (hπ : C π ∈ P) (hb : C b₆ ∈ P) (hε : C ε ∈ P)
    (h2 : IsUnit (2 : O)) (hγ : IsUnit γ) : Lc P ∨ Gp P ∨ Lb P ∨ Gm P := by
  have r3 := q₃_reduce hR.q₃ hε
  have r4 := q₄_reduce hR.q₄ hε
  have r5 := q₅_reduce hR.q₅ hπ
  by_cases h4 : (X 4 : R5) ∈ P
  · have h4' : C γ * X 4 ^ 2 ∈ P := P.mul_mem_left _ (P.pow_mem_of_mem h4 2 two_pos)
    have h02 : X 0 * X 2 ∈ P := by
      have := P.add_mem r3 h4'
      rwa [sub_add_cancel] at this
    have r5' : (2 * X 1 + X 0) * (2 * X 3 + X 2) ∈ P := by
      have := P.sub_mem r5 h4'
      rwa [add_sub_cancel_right] at this
    -- the case `X₀ ∈ P`
    have case0 : (X 0 : R5) ∈ P → Lc P ∨ Gp P ∨ Lb P ∨ Gm P := fun h0 => by
      have hx : X 2 * (2 * X 1 + X 0) ∈ P := by
        have := P.sub_mem r4 (P.mul_mem_right (2 * X 3 + X 2) h0)
        rwa [add_sub_cancel_left] at this
      have h1 : (2 * X 1 + X 0 : R5) ∈ P → (X 1 : R5) ∈ P := fun h => by
        refine two_mul_mem h2 ?_
        have := P.sub_mem h h0
        rwa [add_sub_cancel_right] at this
      rcases hP.mem_or_mem hx with hx2 | hx1
      · rcases hP.mem_or_mem r5' with h | h
        · exact Or.inr (Or.inr (Or.inl ⟨h4, h0, h1 h⟩))
        · refine Or.inl ⟨h4, hx2, two_mul_mem h2 ?_⟩
          have := P.sub_mem h hx2
          rwa [add_sub_cancel_right] at this
      · exact Or.inr (Or.inr (Or.inl ⟨h4, h0, h1 hx1⟩))
    rcases hP.mem_or_mem h02 with h0 | h2'
    · exact case0 h0
    · have hx : X 0 * (2 * X 3 + X 2) ∈ P := by
        have := P.sub_mem r4 (P.mul_mem_right (2 * X 1 + X 0) h2')
        rwa [add_sub_cancel_right] at this
      rcases hP.mem_or_mem hx with h0 | h3
      · exact case0 h0
      · refine Or.inl ⟨h4, h2', two_mul_mem h2 ?_⟩
        have := P.sub_mem h3 h2'
        rwa [add_sub_cancel_right] at this
  · have r1 := cub_reduce hR.cub₁ hπ hb
    have r2 := cub_reduce hR.cub₂ hπ hb
    have hA : (X 1 : R5) ∈ P ∨ X 0 + X 1 ∈ P :=
      hP.mem_or_mem ((hP.mem_or_mem r1).resolve_left h4)
    have hB : (X 3 : R5) ∈ P ∨ X 2 + X 3 ∈ P :=
      hP.mem_or_mem ((hP.mem_or_mem r2).resolve_left h4)
    -- in the two mixed cases `X₀ X₂ + γ X₄² ∈ P`, which forces `X₄ ∈ P`
    have key : (2 * X 1 + X 0) * (2 * X 3 + X 2) - X 0 * X 2 ∈ P → False := fun h => by
      refine h4 (X4_mem_of h2 hγ ?_ r3)
      have e : (X 0 * X 2 + C γ * X 4 ^ 2 : R5) =
          ((2 * X 1 + X 0) * (2 * X 3 + X 2) + C γ * X 4 ^ 2) -
          ((2 * X 1 + X 0) * (2 * X 3 + X 2) - X 0 * X 2) := by ring
      rw [e]
      exact P.sub_mem r5 h
    rcases hA with h1 | h01 <;> rcases hB with h3 | h23
    · exfalso
      refine key ?_
      have e : ((2 * X 1 + X 0) * (2 * X 3 + X 2) - X 0 * X 2 : R5) =
          X 1 * (2 * (2 * X 3 + X 2)) + X 3 * (2 * X 0) := by ring
      rw [e]
      exact P.add_mem (P.mul_mem_right _ h1) (P.mul_mem_right _ h3)
    · exact Or.inr (Or.inl ⟨h1, h23⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h01, h3⟩))
    · exfalso
      refine key ?_
      have e : ((2 * X 1 + X 0) * (2 * X 3 + X 2) - X 0 * X 2 : R5) =
          (X 0 + X 1) * (4 * (X 2 + X 3) - 2 * X 2) - (X 2 + X 3) * (2 * X 0) := by ring
      rw [e]
      exact P.sub_mem (P.mul_mem_right _ h01) (P.mul_mem_right _ h23)

/-- The half `A = L_c ∪ G₊`. -/
def MemA (P : Ideal R5) : Prop := Lc P ∨ Gp P

/-- The half `B = L_b ∪ G₋`. -/
def MemB (P : Ideal R5) : Prop := Lb P ∨ Gm P

/-- The point `Cp = G₊ ∩ L_b = [0 : 0 : 1 : −1 : 0]`. -/
def MemCp (P : Ideal R5) : Prop := X 0 ∈ P ∧ X 1 ∈ P ∧ X 4 ∈ P ∧ X 2 + X 3 ∈ P

/-- The point `Cq = L_c ∩ G₋ = [1 : −1 : 0 : 0 : 0]`. -/
def MemCq (P : Ideal R5) : Prop := X 2 ∈ P ∧ X 3 ∈ P ∧ X 4 ∈ P ∧ X 0 + X 1 ∈ P

lemma memA_or_memB (hR : Rels π b₄ b₆ ε γ P) (hπ : C π ∈ P) (hb : C b₆ ∈ P) (hε : C ε ∈ P)
    (h2 : IsUnit (2 : O)) (hγ : IsUnit γ) : MemA P ∨ MemB P := by
  rcases mem_pieces hR hπ hb hε h2 hγ with h | h | h | h
  exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr (Or.inl h), Or.inr (Or.inr h)]

/-- **The two halves meet exactly in `Cp ⊔ Cq`.** -/
theorem memA_and_memB_iff (hR : Rels π b₄ b₆ ε γ P) (hε : C ε ∈ P) (hγ : IsUnit γ)
    (hX : ∃ i, (X i : R5) ∉ P) : MemA P ∧ MemB P ↔ MemCp P ∨ MemCq P := by
  have r3 := q₃_reduce hR.q₃ hε
  have sub : ∀ {a b : R5}, a + b ∈ P → b ∈ P → a ∈ P := fun {a b} h hb => by
    have := P.sub_mem h hb
    rwa [add_sub_cancel_right] at this
  have all : (X 0 : R5) ∈ P → (X 1 : R5) ∈ P → (X 2 : R5) ∈ P → (X 3 : R5) ∈ P →
      (X 4 : R5) ∈ P → False := fun h0 h1 h2 h3 h4 => by
    obtain ⟨i, hi⟩ := hX
    fin_cases i
    exacts [hi h0, hi h1, hi h2, hi h3, hi h4]
  constructor
  · rintro ⟨⟨h4, h2, h3⟩ | ⟨h1, h23⟩, ⟨h4', h0, h1'⟩ | ⟨h01, h3'⟩⟩
    · exact (all h0 h1' h2 h3 h4).elim
    · exact Or.inr ⟨h2, h3, h4, h01⟩
    · exact Or.inl ⟨h0, h1, h4', h23⟩
    · exfalso
      have h0 : (X 0 : R5) ∈ P := sub h01 h1
      have h2 : (X 2 : R5) ∈ P := sub h23 h3'
      have h4 : (X 4 : R5) ∈ P := by
        have h' : C γ * X 4 ^ 2 ∈ P := by
          have := P.sub_mem (P.mul_mem_right (X 2) h0) r3
          rwa [sub_sub_cancel] at this
        exact hP.mem_of_pow_mem 2 (mem_of_unit_mul hγ h')
      exact all h0 h1 h2 h3' h4
  · rintro (⟨h0, h1, h4, h23⟩ | ⟨h2, h3, h4, h01⟩)
    · exact ⟨Or.inr ⟨h1, h23⟩, Or.inl ⟨h4, h0, h1⟩⟩
    · exact ⟨Or.inl ⟨h4, h2, h3⟩, Or.inr ⟨h01, h3⟩⟩

omit hP in
lemma not_memCp_and_memCq (hX : ∃ i, (X i : R5) ∉ P) : ¬ (MemCp P ∧ MemCq P) := by
  rintro ⟨⟨h0, h1, h4, -⟩, ⟨h2, h3, -, -⟩⟩
  obtain ⟨i, hi⟩ := hX
  fin_cases i
  exacts [hi h0, hi h1, hi h2, hi h3, hi h4]

end Points

/-! ### The decomposition of a space of such points -/

section Space

variable [IsLocalRing O] {π b₄ b₆ ε γ}

local notation "𝔪" => IsLocalRing.maximalIdeal O

variable {m : ℕ} {Z : Type*} [TopologicalSpace Z] {ι : Z → projSpace O m}

local notation "𝒜ₘ" => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

omit [IsLocalRing O] in
lemma isClosed_setOf_mem (hι : Continuous ι) (g : MvPolynomial (Fin (m + 1)) O) :
    IsClosed {z : Z | g ∈ (ι z).asHomogeneousIdeal} := by
  have : {z : Z | g ∈ (ι z).asHomogeneousIdeal} =
      ι ⁻¹' (↑(Proj.basicOpen 𝒜ₘ g) : Set (Proj 𝒜ₘ))ᶜ := by
    ext z
    exact not_not.symm
  rw [this]
  exact (Proj.basicOpen 𝒜ₘ g).isOpen.isClosed_compl.preimage hι

/-- The hypotheses on a space `Z` of points of the special fibre of a model in `ℙᵐ_O` whose
coordinates contain those of the `4`-gon model through `ρ : O[X₀, …, X₄] → O[X₀, …, Xₘ]`
(e.g. a renaming of variables): the five equations hold, the points are special, and some
`ρ X_i` does not vanish. -/
structure Hyp (ι : Z → projSpace O m) (ρ : R5 →+* MvPolynomial (Fin (m + 1)) O) : Prop where
  continuous : Continuous ι
  rels : ∀ z, Rels π b₄ b₆ ε γ ((ι z).asHomogeneousIdeal.toIdeal.comap ρ)
  special : ∀ z, ∀ c ∈ 𝔪, ρ (C c) ∈ (ι z).asHomogeneousIdeal
  nonvanish : ∀ z, ∃ i, ρ (X i) ∉ (ι z).asHomogeneousIdeal
  π_mem : π ∈ 𝔪
  b₆_mem : b₆ ∈ 𝔪
  ε_mem : ε ∈ 𝔪
  two : IsUnit (2 : O)
  γ_unit : IsUnit γ

variable {ρ : R5 →+* MvPolynomial (Fin (m + 1)) O}

/-- The prime of `O[X₀, …, X₄]` of a point. -/
abbrev pt (ρ : R5 →+* MvPolynomial (Fin (m + 1)) O) (ι : Z → projSpace O m) (z : Z) : Ideal R5 :=
  (ι z).asHomogeneousIdeal.toIdeal.comap ρ

instance (z : Z) : (pt ρ ι z).IsPrime := Ideal.comap_isPrime ρ _

omit [IsLocalRing O] in
lemma isClosed_setOf_pt (hι : Continuous ι) (g : R5) : IsClosed {z : Z | g ∈ pt ρ ι z} :=
  isClosed_setOf_mem hι (ρ g)

variable (π b₄ b₆ ε γ ι ρ) in
/-- **The special fibre of the `4`-gon model as two halves meeting in two points**:
`C = A = L_c ∪ G₊`, `E = B = L_b ∪ G₋`, `C ∩ E = Cp ⊔ Cq`. -/
def decomp (h : Hyp (π := π) (b₄ := b₄) (b₆ := b₆) (ε := ε) (γ := γ) ι ρ) :
    TateCovering.Decomp Z where
  C := {z | MemA (pt ρ ι z)}
  E := {z | MemB (pt ρ ι z)}
  Cp := {z | MemCp (pt ρ ι z)}
  Cq := {z | MemCq (pt ρ ι z)}
  isClosed_C := by
    have hc := isClosed_setOf_pt (Z := Z) (ρ := ρ) h.continuous
    exact ((hc _).inter ((hc _).inter (hc _))).union ((hc _).inter (hc _))
  isClosed_E := by
    have hc := isClosed_setOf_pt (Z := Z) (ρ := ρ) h.continuous
    exact ((hc _).inter ((hc _).inter (hc _))).union ((hc _).inter (hc _))
  isClosed_Cp := by
    have hc := isClosed_setOf_pt (Z := Z) (ρ := ρ) h.continuous
    exact (hc _).inter ((hc _).inter ((hc _).inter (hc _)))
  isClosed_Cq := by
    have hc := isClosed_setOf_pt (Z := Z) (ρ := ρ) h.continuous
    exact (hc _).inter ((hc _).inter ((hc _).inter (hc _)))
  union := Set.eq_univ_of_forall fun z => memA_or_memB (P := pt ρ ι z) (h.rels z)
    (h.special z _ h.π_mem) (h.special z _ h.b₆_mem) (h.special z _ h.ε_mem) h.two h.γ_unit
  inter := by
    ext z
    exact memA_and_memB_iff (P := pt ρ ι z) (h.rels z) (h.special z _ h.ε_mem) h.γ_unit
      (h.nonvanish z)
  disjoint := by
    rw [Set.disjoint_left]
    exact fun z h₁ h₂ => not_memCp_and_memCq (P := pt ρ ι z) (h.nonvanish z) ⟨h₁, h₂⟩

end Space

/-! ### Polynomials vanishing at the generic point of a projective model -/

section ProjModel

open SemistableReduction.ProjScheme

variable {F : Type u} [Field F] [Algebra O F] {m : ℕ} {f : Fin (m + 1) → F}

local notation "𝒜'" => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

/-- Membership of a homogeneous element in a point of the standard chart `D₊(x_i)`. -/
lemma mem_stdι_iff (i : Fin (m + 1)) (P : Spec (CommRingCat.of (Away 𝒜' (X i))))
    {g : MvPolynomial (Fin (m + 1)) O} {e : ℕ} (hg : g ∈ 𝒜' e) (he : 0 < e) :
    g ∈ (stdι O m i P).asHomogeneousIdeal ↔
      Away.isLocalizationElem (X_mem (O := O) (m := m) i) hg ∈ P.asIdeal := by
  have h := Proj.awayι_preimage_basicOpen 𝒜' (X_mem (O := O) (m := m) i) one_pos hg he
  have h' : P ∈ stdι O m i ⁻¹ᵁ Proj.basicOpen 𝒜' g ↔
      P ∈ PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem (O := O) (m := m) i) hg) := by
    rw [← h]
    rfl
  rw [← not_iff_not]
  exact h'

/-- **A homogeneous polynomial vanishing at the coordinates `f` vanishes at every point of the
projective model** `projModelCode O f` (the closure of the generic point `Spec F ⟶ ℙᵐ_O`). -/
theorem mem_imageι_of_evalHom_eq_zero (hf : ∀ i, f i ≠ 0) {g : MvPolynomial (Fin (m + 1)) O}
    {d : ℕ} (hg : g ∈ 𝒜' d) (hd : 0 < d) (h0 : evalHom f g = 0)
    (z : (projModelCode O hf).scheme) :
    g ∈ ((toProj O hf).imageι z).asHomogeneousIdeal := by
  have hclosed : IsClosed {y : projSpace O m | g ∈ y.asHomogeneousIdeal} := by
    have e : {y : projSpace O m | g ∈ y.asHomogeneousIdeal} =
        (↑(Proj.basicOpen 𝒜' g) : Set (Proj 𝒜'))ᶜ := by
      ext y
      exact not_not.symm
    rw [e]
    exact (Proj.basicOpen 𝒜' g).isOpen.isClosed_compl
  have hrange : Set.range (toProj O hf) ⊆ {y : projSpace O m | g ∈ y.asHomogeneousIdeal} := by
    rintro _ ⟨x, rfl⟩
    change g ∈ (toProj O hf x).asHomogeneousIdeal
    rw [toProj_eq hf 0, Scheme.Hom.comp_apply, mem_stdι_iff 0 _ hg hd, Spec.map_apply]
    change awayEval _ _ _ _ ∈ x.asIdeal
    rw [Away.isLocalizationElem, awayEval_mk, pow_one, h0, zero_div]
    exact zero_mem _
  haveI : QuasiCompact (toProj O hf) := by
    have : QuasiCompact (toProj O hf ≫ projSpace.toSpec O m) := by
      rw [toProj_toSpec]
      infer_instance
    exact .of_comp _ (projSpace.toSpec O m)
  have hz : (toProj O hf).imageι z ∈ closure (Set.range (toProj O hf)) := by
    rw [← Scheme.Hom.support_ker, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  exact closure_minimal hrange hclosed hz

end ProjModel

end

end FourGon

/-! ### Pulling back a decomposition along a continuous map -/

namespace TateCovering.Decomp

variable {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z']

/-- The decomposition `Φ⁻¹C ∪ Φ⁻¹E` of `Z` pulled back along a continuous map `Φ : Z → Z'`. -/
def comapC (Φ : Z → Z') (hΦ : Continuous Φ) (D : Decomp Z') : Decomp Z where
  C := Φ ⁻¹' D.C
  E := Φ ⁻¹' D.E
  Cp := Φ ⁻¹' D.Cp
  Cq := Φ ⁻¹' D.Cq
  isClosed_C := D.isClosed_C.preimage hΦ
  isClosed_E := D.isClosed_E.preimage hΦ
  isClosed_Cp := D.isClosed_Cp.preimage hΦ
  isClosed_Cq := D.isClosed_Cq.preimage hΦ
  union := by rw [← Set.preimage_union, D.union, Set.preimage_univ]
  inter := by rw [← Set.preimage_inter, D.inter, Set.preimage_union]
  disjoint := D.disjoint.preimage Φ

end TateCovering.Decomp

end TemperedFundamentalGroups

/-! ### Morphisms of projective models from domination on a covering set of charts -/

namespace SemistableReduction.ProjScheme

open CategoryTheory.Limits

section DominateOn

variable {O₁ O₂ : Type u} [CommRing O₁] [CommRing O₂] {F₁ F₂ : Type u} [Field F₁] [Field F₂]
  [Algebra O₁ F₁] [Algebra O₂ F₂] {m n : ℕ} {f : Fin (m + 1) → F₁} {g : Fin (n + 1) → F₂}
  {R₁ : Subring F₁} {R₂ : Subring F₂}

/-- **Zariski domination on a set `S` of charts of `g`**: every chart `R₂[g / g j]`, `j ∈ S`,
contains the `φ`-image of some chart `R₁[f / f i]`. -/
def DominatesOn (R₁ : Subring F₁) (R₂ : Subring F₂) (φ : F₁ →+* F₂) (f : Fin (m + 1) → F₁)
    (g : Fin (n + 1) → F₂) (S : Set (Fin (n + 1))) : Prop :=
  ∀ j ∈ S, ∃ i, ∀ x ∈ projChart R₁ f i, φ x ∈ projChart R₂ g j

variable (hR₁ : (algebraMap O₁ F₁).range = R₁) (hR₂ : (algebraMap O₂ F₂).range = R₂)
  (hf : ∀ i, f i ≠ 0) (hg : ∀ j, g j ≠ 0) (φ : F₁ →+* F₂) {S : Set (Fin (n + 1))}

/-- The charts `Spec R[g / g j]`, `j ∈ S`, as an open cover (when they cover the model). -/
noncomputable def chartCoverOn (hS : ∀ x : (projModelCode O₂ hg).scheme, ∃ j ∈ S,
      x ∈ chartOpen O₂ hg j) : (projModelCode O₂ hg).scheme.OpenCover :=
  Scheme.Cover.mkOfCovers S (fun j ↦ Spec (CommRingCat.of (projChart R₂ g j)))
    (fun j ↦ chartι R₂ hR₂ hg j) (fun x ↦ by
      obtain ⟨j, hj, hx⟩ := hS x
      rw [← opensRange_chartι R₂ hR₂ hg j] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨⟨j, hj⟩, y, hy⟩)

/-- Compatibility of the local morphisms on overlaps of charts (any choice of target charts). -/
lemma localHom_compat_of {i i' : Fin (m + 1)} (j j' : Fin (n + 1))
    (h : ∀ x ∈ projChart R₁ f i, φ x ∈ projChart R₂ g j)
    (h' : ∀ x ∈ projChart R₁ f i', φ x ∈ projChart R₂ g j') :
    pullback.fst (chartι R₂ hR₂ hg j) (chartι R₂ hR₂ hg j') ≫ localHom hR₁ hf φ h =
      pullback.snd (chartι R₂ hR₂ hg j) (chartι R₂ hR₂ hg j') ≫ localHom hR₁ hf φ h' := by
  have : IsReduced (pullback (chartι R₂ hR₂ hg j) (chartι R₂ hR₂ hg j')) :=
    isReduced_of_isOpenImmersion (pullback.fst _ _)
  let ι := pullback.lift (f := chartι R₂ hR₂ hg j) (g := chartι R₂ hR₂ hg j')
    (Spec.map (CommRingCat.ofHom (projChart R₂ g j).subtype))
    (Spec.map (CommRingCat.ofHom (projChart R₂ g j').subtype))
    (by rw [← genericPt_eq_chartι, ← genericPt_eq_chartι])
  have : IsDominant (ι ≫ pullback.fst _ _ ≫ chartι R₂ hR₂ hg j) := by
    rw [pullback.lift_fst_assoc, ← genericPt_eq_chartι]
    infer_instance
  have : IsDominant ι :=
    IsDominant.of_comp_of_isOpenImmersion ι (pullback.fst _ _ ≫ chartι R₂ hR₂ hg j)
  refine ext_of_isDominant ι ?_
  rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, SpecMap_subtype_localHom,
    SpecMap_subtype_localHom]

/-- **The morphism of projective models from domination on a covering set of charts.** -/
noncomputable def homOfDominatesOn (hS : ∀ x : (projModelCode O₂ hg).scheme, ∃ j ∈ S,
      x ∈ chartOpen O₂ hg j) (hφ : DominatesOn R₁ R₂ φ f g S) :
    (projModelCode O₂ hg).scheme ⟶ (projModelCode O₁ hf).scheme :=
  (chartCoverOn hR₂ hg hS).glueMorphisms (fun j ↦ localHom hR₁ hf φ (hφ j.1 j.2).choose_spec)
    (fun j j' ↦ localHom_compat_of hR₁ hR₂ hf hg φ j.1 j'.1 _ _)

lemma chartι_homOfDominatesOn (hS : ∀ x : (projModelCode O₂ hg).scheme, ∃ j ∈ S,
      x ∈ chartOpen O₂ hg j) (hφ : DominatesOn R₁ R₂ φ f g S) {j : Fin (n + 1)} (hj : j ∈ S) :
    chartι R₂ hR₂ hg j ≫ homOfDominatesOn hR₁ hR₂ hf hg φ hS hφ =
      localHom hR₁ hf φ (hφ j hj).choose_spec :=
  Scheme.Cover.ι_glueMorphisms (chartCoverOn hR₂ hg hS) _ _ ⟨j, hj⟩

/-- The morphism is compatible with the generic points. -/
theorem genericPt_comp_homOfDominatesOn (hS : ∀ x : (projModelCode O₂ hg).scheme, ∃ j ∈ S,
      x ∈ chartOpen O₂ hg j) (hφ : DominatesOn R₁ R₂ φ f g S) :
    genericPt O₂ hg ≫ homOfDominatesOn hR₁ hR₂ hf hg φ hS hφ =
      Spec.map (CommRingCat.ofHom φ) ≫ genericPt O₁ hf := by
  obtain ⟨j, hj, -⟩ := hS (genericPt O₂ hg ⟨⊥, Ideal.isPrime_bot⟩)
  rw [genericPt_eq_chartι R₂ hR₂ hg j, Category.assoc, chartι_homOfDominatesOn hR₁ hR₂ hf hg φ hS
    hφ hj, SpecMap_subtype_localHom]

/-- The morphism lies over the common base ring. -/
theorem homOfDominatesOn_toSpec_self {O : Type u} [CommRing O] [Algebra O F₁] [Algebra O F₂]
    {R₁ : Subring F₁} {R₂ : Subring F₂}
    (hR₁ : (algebraMap O F₁).range = R₁) (hR₂ : (algebraMap O F₂).range = R₂)
    (hf : ∀ i, f i ≠ 0) (hg : ∀ j, g j ≠ 0) (φ : F₁ →+* F₂)
    (hS : ∀ x : (projModelCode O hg).scheme, ∃ j ∈ S, x ∈ chartOpen O hg j)
    (hφ : DominatesOn R₁ R₂ φ f g S) (hτ : φ.comp (algebraMap O F₁) = algebraMap O F₂) :
    homOfDominatesOn hR₁ hR₂ hf hg φ hS hφ ≫ (projModelCode O hf).toSpec =
      (projModelCode O hg).toSpec := by
  refine hom_ext_genericPt hg ?_
  rw [reassoc_of% genericPt_comp_homOfDominatesOn, genericPt_toSpec, genericPt_toSpec,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]

end DominateOn

end SemistableReduction.ProjScheme
