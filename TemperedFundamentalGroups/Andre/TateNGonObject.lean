/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateNGon
import TemperedFundamentalGroups.Andre.TateFourGonObject

/-!
# The `2N`-gon model of `E_{q^N}` over the Tate model of `E_q`

Let `π, b₄, b₆` be the Tate data of `E_q` and `π, b₄', b₆'` those of `E_{q^N}` (`N ≥ 3`). The
model equations (TFGD-plan, "Run 6", "Run 7") in `ℙ^{2N}_O`, coordinates `[B_0 : … : B_{N−1} : W]`:

* the block cubics `cub k` (the Tate cubic of `E_{q^N}` on `(x_k, y_k, W)`);
* for every `d ≠ 0` and every `k`, three bilinear relations `bil (cP r d) k d` between the blocks
  `B_k` and `B_{k+d}` (translation by `dT`), with coefficient matrices `cP r d` in the basis
  `(W, x, y) ⊗ (W, x', y')`;
* the cyclic quadrics `gam (e d) (g d) d = Σ_k (x_k − e_d W)(x_{k+d} − e_d W) − g_d W²`;
* `F(ℓ)`: the Tate cubic of `E_q` on the Vélu forms
  `ℓ = (Σ_k x_k − ε W, Σ_k y_k + κ W, W)`.

`NGon.red_of_rels`: when the coefficients reduce to the patterns of `NGon.Red` modulo an ideal
`J` of `O` (in the application `J = 𝔪`), every prime containing the equations and `J` satisfies
`NGon.Red` (so `NGon.mem_pieces` and `NGon.decomp` apply).

`NGon.model`: the reduced closed subscheme of `ℙ^{2N}_O` on the common zeros of the equations;
`NGon.ψ : model ⟶ TateModel.model π b₄ b₆`: the linear projection `[ℓ₀ : ℓ₁ : ℓ₂]` (the model
misses its centre: `NGon.exists_ℓψ_notMem`, for `O` local with `𝔪 = √(π)`).

On the generic fibre the common zeros of `cub` and `bil` are exactly the curve `u ↦ [P(u) : P(qu) :
… : P(q^{N−1}u) : π]` (TFGD-plan "Run 7", helper h1: a rank lemma for the bilinear relations; the
equations `gam` and `F(ℓ)` are only needed on the special fibre resp. for `ψ`).
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open SemistableReduction.LinearProjectionN

namespace TemperedFundamentalGroups

/-! ### Maps `(z, n) ↦ (f z, M n + κ z + c)` of `ℤ`-coverings -/

namespace TateCovering.Decomp

variable {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z']

/-- The map `(z, n) ↦ (f z, M n + κ z + c)` from the `ℤ`-covering of `D'` to that of `D`. -/
def mapN (D' : Decomp Z') (D : Decomp Z) (f : Z' → Z) (M : ℤ) (κ : Z' → ℤ) (c : ℤ)
    (y : D'.Space) : D.Space :=
  ⟨f y.pt, M * y.n + κ y.pt + c⟩

variable {D' : Decomp Z'} {D : Decomp Z}

/-- **Continuity of `mapN`**: the sheet labels are locally constant along the sheets. -/
theorem continuous_mapN {f : Z' → Z} (hf : Continuous f) (M : ℤ) (κ : Z' → ℤ) (c : ℤ)
    (h1 : ∀ z, f z ∉ D.Cq → z ∉ D'.Cq)
    (h2 : ∀ v, IsOpen {z | f z ∉ D.Cq ∧ κ z = v})
    (h3 : ∀ v, IsOpen {z | z ∉ D'.Cq ∧ f z ∉ D.Cp ∧ κ z - D.shift (f z) = v})
    (h4 : ∀ v, IsOpen {z | z ∉ D'.Cp ∧ f z ∉ D.Cp ∧
      M * D'.shift z + κ z - D.shift (f z) = v}) :
    Continuous (mapN D' D f M κ c) := by
  rw [continuous_iff]
  refine ⟨hf.comp D'.continuous_pt, fun k => ?_, fun k => ?_⟩
  · have : {y : D'.Space | (mapN D' D f M κ c y).pt ∉ D.Cq ∧ (mapN D' D f M κ c y).n = k} =
        ⋃ j : ℤ, {y : D'.Space | y.pt ∉ D'.Cq ∧ y.n = j} ∩
          (fun y : D'.Space => y.pt) ⁻¹' {z | f z ∉ D.Cq ∧ κ z = k - M * j - c} := by
      ext y
      simp only [mapN, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hq, hk⟩
        exact ⟨y.n, ⟨h1 _ hq, rfl⟩, hq, by linear_combination hk⟩
      · rintro ⟨j, ⟨-, rfl⟩, hq, hk⟩
        exact ⟨hq, by linear_combination hk⟩
    rw [this]
    exact isOpen_iUnion fun j => (D'.isOpen_sheet₁ j).inter ((h2 _).preimage D'.continuous_pt)
  · have : {y : D'.Space | (mapN D' D f M κ c y).pt ∉ D.Cp ∧
        (mapN D' D f M κ c y).n - D.shift (mapN D' D f M κ c y).pt = k} =
        ⋃ j : ℤ, (({y : D'.Space | y.pt ∉ D'.Cq ∧ y.n = j} ∩
          (fun y : D'.Space => y.pt) ⁻¹'
            {z | z ∉ D'.Cq ∧ f z ∉ D.Cp ∧ κ z - D.shift (f z) = k - M * j - c}) ∪
          ({y : D'.Space | y.pt ∉ D'.Cp ∧ y.n - D'.shift y.pt = j} ∩
          (fun y : D'.Space => y.pt) ⁻¹' {z | z ∉ D'.Cp ∧ f z ∉ D.Cp ∧
            M * D'.shift z + κ z - D.shift (f z) = k - M * j - c})) := by
      ext y
      simp only [mapN, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union, Set.mem_inter_iff,
        Set.mem_preimage]
      constructor
      · rintro ⟨hp, hk⟩
        by_cases hq : y.pt ∈ D'.Cq
        · have hp' : y.pt ∉ D'.Cp := fun h => D'.notMem_Cq_of_mem_Cp h hq
          exact ⟨y.n - D'.shift y.pt, Or.inr ⟨⟨hp', rfl⟩, hp', hp, by linear_combination hk⟩⟩
        · exact ⟨y.n, Or.inl ⟨⟨hq, rfl⟩, hq, hp, by linear_combination hk⟩⟩
      · rintro ⟨j, ⟨⟨-, rfl⟩, -, hp, hk⟩ | ⟨⟨-, hj⟩, -, hp, hk⟩⟩
        · exact ⟨hp, by linear_combination hk⟩
        · exact ⟨hp, by linear_combination hk + M * hj⟩
    rw [this]
    exact isOpen_iUnion fun j =>
      ((D'.isOpen_sheet₁ j).inter ((h3 _).preimage D'.continuous_pt)).union
        ((D'.isOpen_sheet₂ j).inter ((h4 _).preimage D'.continuous_pt))

end TateCovering.Decomp

namespace NGon

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] {N : ℕ} [NeZero N]

set_option hygiene false in
local notation "RN" => MvPolynomial (Fin (2 * N + 1)) O

local notation "𝒜N" => MvPolynomial.homogeneousSubmodule (Fin (2 * N + 1)) O
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) O

/-! ### The equations -/

variable (O N) in
/-- The coefficients of the model equations. -/
structure Coeffs where
  /-- The Tate data `π, b₄, b₆` of `E_q`. -/
  π : O
  /-- `b₄` of `E_q`. -/
  b₄ : O
  /-- `b₆` of `E_q`. -/
  b₆ : O
  /-- `b₄'` of `E_{q^N}` (same `π`). -/
  b₄' : O
  /-- `b₆'` of `E_{q^N}`. -/
  b₆' : O
  /-- The coefficient matrices of the bilinear relations for translation by `dT`. -/
  cP : Fin 3 → ZMod N → Fin 3 → Fin 3 → O
  /-- `e_d = x_{dT} / π`. -/
  e : ZMod N → O
  /-- `g_d = K_d / π²`. -/
  g : ZMod N → O
  /-- The Vélu constant of `x`: `x = Σ_k x_k − π ε`. -/
  ε : O
  /-- The Vélu constant of `y`: `y = Σ_k y_k + π κ`. -/
  κ : O

/-- The basis `(W, x_k, y_k)`. -/
def vA (k : ZMod N) : Fin 3 → RN := ![ww O N, xx k, yy k]

/-- The Tate cubic `y²W + xyW − πx³ − πb₄xW² − b₆W³` on the block `B_k`. -/
def cub (π b₄ b₆ : O) (k : ZMod N) : RN :=
  yy k ^ 2 * ww O N + xx k * yy k * ww O N - C π * xx k ^ 3 - C (π * b₄) * xx k * ww O N ^ 2 -
    C b₆ * ww O N ^ 3

/-- The bilinear form `Σ_{a,b} c_{ab} v_a(B_k) v_b(B_{k+d})`. -/
def bil (c : Fin 3 → Fin 3 → O) (k d : ZMod N) : RN :=
  ∑ a, ∑ b, C (c a b) * vA k a * vA (k + d) b

/-- The cyclic quadric `Σ_k (x_k − e W)(x_{k+d} − e W) − g W²`. -/
def gam (e g : O) (d : ZMod N) : RN :=
  ∑ k : ZMod N, (xx k - C e * ww O N) * (xx (k + d) - C e * ww O N) - C g * ww O N ^ 2

/-- The Vélu linear forms `ℓ = (Σ_k x_k − ε W, Σ_k y_k + κ W, W)`. -/
def ℓψ (ε κ : O) : Fin (2 + 1) → RN :=
  ![∑ k : ZMod N, xx k - C ε * ww O N, ∑ k : ZMod N, yy k + C κ * ww O N, ww O N]

/-- The Tate cubic of `E_q` on the linear forms `ℓ`. -/
def Fℓ (D : Coeffs O N) : RN := aeval (ℓψ D.ε D.κ) (TateModel.F D.π D.b₄ D.b₆)

/-- The set of model equations. -/
def eqns (D : Coeffs O N) : Set RN :=
  Set.range (cub D.π D.b₄' D.b₆') ∪
    {r | ∃ (i : Fin 3) (d k : ZMod N), d ≠ 0 ∧ r = bil (D.cP i d) k d} ∪
    {r | ∃ d : ZMod N, d ≠ 0 ∧ r = gam (D.e d) (D.g d) d} ∪ {Fℓ D}

/-- The equations hold at `P`. -/
def Rels (D : Coeffs O N) (P : Ideal RN) : Prop := eqns D ⊆ P

section RelsLemmas

variable {D : Coeffs O N} {P : Ideal RN}

lemma Rels.cub (h : Rels D P) (k : ZMod N) : cub D.π D.b₄' D.b₆' k ∈ P :=
  h (Or.inl (Or.inl (Or.inl ⟨k, rfl⟩)))

lemma Rels.bil (h : Rels D P) (i : Fin 3) {d : ZMod N} (hd : d ≠ 0) (k : ZMod N) :
    bil (D.cP i d) k d ∈ P :=
  h (Or.inl (Or.inl (Or.inr ⟨i, d, k, hd, rfl⟩)))

lemma Rels.gam (h : Rels D P) {d : ZMod N} (hd : d ≠ 0) : gam (D.e d) (D.g d) d ∈ P :=
  h (Or.inl (Or.inr ⟨d, hd, rfl⟩))

lemma Rels.fℓ (h : Rels D P) : Fℓ D ∈ P := h (Or.inr rfl)

end RelsLemmas

/-! ### Reduction of the equations -/

/-- The pattern `x x' + y x'`. -/
def pA0 : Fin 3 → Fin 3 → O := ![![0, 0, 0], ![0, 1, 0], ![0, 1, 0]]
/-- The pattern `x y'`. -/
def pA1 : Fin 3 → Fin 3 → O := ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]
/-- The pattern `y y'`. -/
def pY : Fin 3 → Fin 3 → O := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]
/-- The pattern `x x'`. -/
def pB0 : Fin 3 → Fin 3 → O := ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]]
/-- The pattern `x x' + x y' + y x'`. -/
def pB1 : Fin 3 → Fin 3 → O := ![![0, 0, 0], ![0, 1, 1], ![0, 1, 0]]

lemma bil_pA0 (k d : ZMod N) : bil (O := O) pA0 k d = (xx k + yy k) * xx (k + d) := by
  simp [bil, pA0, vA, Fin.sum_univ_three]
  ring

lemma bil_pA1 (k d : ZMod N) : bil (O := O) pA1 k d = xx k * yy (k + d) := by
  simp [bil, pA1, vA, Fin.sum_univ_three]

lemma bil_pY (k d : ZMod N) : bil (O := O) pY k d = yy k * yy (k + d) := by
  simp [bil, pY, vA, Fin.sum_univ_three]

lemma bil_pB0 (k d : ZMod N) : bil (O := O) pB0 k d = xx k * xx (k + d) := by
  simp [bil, pB0, vA, Fin.sum_univ_three]

lemma bil_pB1 (k d : ZMod N) :
    bil (O := O) pB1 k d = xx k * xx (k + d) + (xx k * yy (k + d) + yy k * xx (k + d)) := by
  simp [bil, pB1, vA, Fin.sum_univ_three]
  ring

lemma bil_sub (c c' : Fin 3 → Fin 3 → O) (k d : ZMod N) :
    bil c k d - bil c' k d = bil (fun a b => c a b - c' a b) k d := by
  simp only [bil, ← Finset.sum_sub_distrib, map_sub, sub_mul]

variable {P : Ideal RN}

lemma bil_mem_of {c : Fin 3 → Fin 3 → O} (hc : ∀ a b, C (c a b) ∈ P) (k d : ZMod N) :
    bil c k d ∈ P :=
  P.sum_mem fun a _ => P.sum_mem fun b _ => P.mul_mem_right _ (P.mul_mem_right _ (hc a b))

lemma bil_reduce {J : Ideal O} (hJ : ∀ c ∈ J, C c ∈ P) {c p : Fin 3 → Fin 3 → O}
    (hcp : ∀ a b, c a b - p a b ∈ J) {k d : ZMod N} (h : bil c k d ∈ P) : bil p k d ∈ P := by
  have : bil c k d - bil p k d ∈ P := by
    rw [bil_sub]
    exact bil_mem_of (fun a b => hJ _ (hcp a b)) k d
  have := P.sub_mem h this
  rwa [sub_sub_cancel] at this

lemma gam_reduce {J : Ideal O} (hJ : ∀ c ∈ J, C c ∈ P) {e g : O} (he : e ∈ J) {d : ZMod N}
    (h : gam e g d ∈ P) : ∑ k : ZMod N, xx k * xx (k + d) - C g * ww O N ^ 2 ∈ P := by
  have hd : gam e g d - (∑ k : ZMod N, xx k * xx (k + d) - C g * ww O N ^ 2) =
      ∑ k : ZMod N, C e * (C e * ww O N ^ 2 - ww O N * xx (k + d) - ww O N * xx k) := by
    rw [gam, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hm : gam e g d - (∑ k : ZMod N, xx k * xx (k + d) - C g * ww O N ^ 2) ∈ P := by
    rw [hd]
    exact P.sum_mem fun k _ => P.mul_mem_right _ (hJ e he)
  have := P.sub_mem h hm
  rwa [sub_sub_cancel] at this

variable (N) in
/-- The reduction hypotheses on the coefficients modulo an ideal `J` of `O`. -/
def RedCoeffs (D : Coeffs O N) (J : Ideal O) : Prop :=
  (∀ d : ZMod N, 0 < d.val → 2 * d.val < N → ∀ a b,
    D.cP 0 d a b - pA0 a b ∈ J ∧ D.cP 1 d a b - pA1 a b ∈ J ∧ D.cP 2 d a b - pY a b ∈ J) ∧
  (∀ d : ZMod N, 2 * d.val = N → ∀ a b,
    D.cP 0 d a b - pB0 a b ∈ J ∧ D.cP 1 d a b - pB1 a b ∈ J ∧ D.cP 2 d a b - pY a b ∈ J) ∧
  (∀ d, D.e d ∈ J) ∧ (∀ d : ZMod N, 2 ≤ d.val → 2 * d.val < N → D.g d ∈ J)

/-- **The equations reduce to `NGon.Red`** at every prime containing `J`. -/
theorem red_of_rels {D : Coeffs O N} {J : Ideal O} (hD : RedCoeffs N D J) (hN : 3 ≤ N)
    (hJ : ∀ c ∈ J, C c ∈ P) (hR : Rels D P) : Red (D.g 1) P := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨hA, hB, he, hg⟩ := hD
  have ne0 : ∀ d : ZMod N, 0 < d.val → d ≠ 0 := fun d h e => by
    rw [e, ZMod.val_zero] at h
    exact lt_irrefl 0 h
  refine ⟨fun k d hpos hlt => ?_, fun k d h2 => ?_, ?_, fun d h2 hlt => ?_⟩
  · have hd := ne0 d hpos
    refine ⟨?_, ?_, ?_⟩
    · rw [← bil_pA0]
      exact bil_reduce hJ (fun a b => (hA d hpos hlt a b).1) (hR.bil 0 hd k)
    · rw [← bil_pA1]
      exact bil_reduce hJ (fun a b => (hA d hpos hlt a b).2.1) (hR.bil 1 hd k)
    · rw [← bil_pY]
      exact bil_reduce hJ (fun a b => (hA d hpos hlt a b).2.2) (hR.bil 2 hd k)
  · have hd : d ≠ 0 := ne0 d (by omega)
    have h0 : xx k * xx (k + d) ∈ P := by
      rw [← bil_pB0]
      exact bil_reduce hJ (fun a b => (hB d h2 a b).1) (hR.bil 0 hd k)
    have h1 : xx k * xx (k + d) + (xx k * yy (k + d) + yy k * xx (k + d)) ∈ P := by
      rw [← bil_pB1]
      exact bil_reduce hJ (fun a b => (hB d h2 a b).2.1) (hR.bil 1 hd k)
    refine ⟨h0, sub_mem_right h1 h0, ?_⟩
    rw [← bil_pY]
    exact bil_reduce hJ (fun a b => (hB d h2 a b).2.2) (hR.bil 2 hd k)
  · exact gam_reduce hJ (he 1) (hR.gam one_ne_zero)
  · have := gam_reduce hJ (he d) (hR.gam (ne0 d (by omega)))
    have hw : C (D.g d) * ww O N ^ 2 ∈ P := P.mul_mem_right _ (hJ _ (hg d h2 hlt))
    have := P.add_mem this hw
    rwa [sub_add_cancel] at this

/-! ### The model misses the centre of the projection -/

lemma ℓψ_mem (ε κ : O) (j : Fin (2 + 1)) : ℓψ (N := N) ε κ j ∈ 𝒜N 1 := by
  rw [mem_homogeneousSubmodule]
  have hs : ∀ f : ZMod N → Fin (2 * N + 1), (∑ k, X (f k) : RN).IsHomogeneous 1 := fun f =>
    IsHomogeneous.sum _ _ _ fun k _ => isHomogeneous_X _ _
  have hc : ∀ e : O, (C e * ww O N : RN).IsHomogeneous 1 := fun e => by
    simpa using (isHomogeneous_C (Fin (2 * N + 1)) e).mul (isHomogeneous_X O (iw N))
  fin_cases j
  · exact (hs ix).sub (hc ε)
  · exact (hs iy).add (hc κ)
  · exact isHomogeneous_X O (iw N)

/-- `bil c k d ≡ c₂₂ y_k y_{k+d}` modulo `W` and the `x`'s. -/
lemma bil_eq_yy (c : Fin 3 → Fin 3 → O) (k d : ZMod N) :
    bil c k d = C (c 2 2) * (yy k * yy (k + d)) +
      (ww O N * (C (c 0 0) * ww O N + C (c 0 1) * xx (k + d) + C (c 0 2) * yy (k + d) +
        C (c 1 0) * xx k + C (c 2 0) * yy k) +
      xx k * (C (c 1 1) * xx (k + d) + C (c 1 2) * yy (k + d)) +
      xx (k + d) * (C (c 2 1) * yy k)) := by
  simp [bil, vA, Fin.sum_univ_three]
  ring

/-! ### The model -/

section ModelDef

variable (D : Coeffs O N)

/-- The closed subset of `ℙ^{2N}_O` cut out by the equations. -/
def relSet : TopologicalSpace.Closeds (projSpace O (2 * N)) :=
  ⟨{y | Rels D y.asHomogeneousIdeal.toIdeal}, by
    have : {y : projSpace O (2 * N) | Rels D y.asHomogeneousIdeal.toIdeal} =
        ⋂ r ∈ eqns D, {y | r ∈ y.asHomogeneousIdeal} := by
      ext y
      simp only [Rels, Set.mem_setOf_eq, Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_biInter fun r _ => by
      have e : {y : projSpace O (2 * N) | r ∈ y.asHomogeneousIdeal} =
          (↑(Proj.basicOpen 𝒜N r) : Set (Proj 𝒜N))ᶜ := by
        ext y
        exact not_not.symm
      rw [e]
      exact (Proj.basicOpen 𝒜N r).isOpen.isClosed_compl⟩

/-- The ideal sheaf of the model. -/
abbrev modelIdeal : (projSpace O (2 * N)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (relSet D)

/-- **The `2N`-gon model**: the reduced closed subscheme of `ℙ^{2N}_O` on `relSet`. -/
def model : ModelCode O where
  m := 2 * N
  I := modelIdeal D

/-- The closed immersion of the model into `ℙ^{2N}_O`. -/
abbrev ιm : (modelIdeal D).subscheme ⟶ projSpace O (2 * N) := (modelIdeal D).subschemeι

lemma range_ιm : Set.range (ιm D) = {y | Rels D y.asHomogeneousIdeal.toIdeal} := by
  rw [Scheme.IdealSheafData.range_subschemeι, modelIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

lemma rels_ιm (z : (modelIdeal D).subscheme) : Rels D (ιm D z).asHomogeneousIdeal.toIdeal := by
  have : ιm D z ∈ Set.range (ιm D) := ⟨z, rfl⟩
  rwa [range_ιm] at this

lemma toSpec_eq : (model D).toSpec = ιm D ≫ projSpace.toSpec O (2 * N) := rfl

end ModelDef

variable [IsLocalRing O]

local notation "𝔪" => IsLocalRing.maximalIdeal O

lemma isUnit_of_sub_one_mem {a : O} (h : a - 1 ∈ 𝔪) : IsUnit a := by
  by_contra ha
  have : (1 : O) ∈ 𝔪 := by
    have := (𝔪).sub_mem ((IsLocalRing.mem_maximalIdeal a).2 ha) h
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.mem_maximalIdeal 1).1 this isUnit_one

section Points

variable [hP : P.IsPrime]

/-- **The model misses the centre of the projection** `[ℓ₀ : ℓ₁ : ℓ₂]` (`O` local with
`𝔪 = √(π)`, `N ≥ 3`, `g₁` a unit). -/
theorem exists_ℓψ_notMem {D : Coeffs O N} (hD : RedCoeffs N D 𝔪) (hN : 3 ≤ N)
    (hg : IsUnit (D.g 1)) (hrad : ∀ c ∈ 𝔪, ∃ n, D.π ∣ c ^ n) (hR : Rels D P)
    (hX : ∃ j, (X j : RN) ∉ P) : ∃ j, ℓψ D.ε D.κ j ∉ P := by
  by_contra hall
  push Not at hall
  have hw : ww O N ∈ P := hall 2
  have h0 : ∑ k : ZMod N, xx k ∈ P := by
    have h0' : (∑ k : ZMod N, xx k - C D.ε * ww O N) + C D.ε * ww O N ∈ P :=
      P.add_mem (hall 0) (P.mul_mem_left _ hw)
    rwa [sub_add_cancel] at h0'
  have h1 : ∑ k : ZMod N, yy k ∈ P :=
    sub_mem_left (hall 1 : (∑ k : ZMod N, yy k + C D.κ * ww O N) ∈ P) (P.mul_mem_left _ hw)
  by_cases hπ : C D.π ∈ P
  · -- the special fibre: the pieces
    have hJ : ∀ c ∈ 𝔪, C c ∈ P := fun c hc => by
      obtain ⟨n, r, hr⟩ := hrad c hc
      refine hP.mem_of_pow_mem n ?_
      rw [← map_pow, hr, map_mul]
      exact P.mul_mem_right _ hπ
    obtain ⟨i, hi⟩ := mem_pieces (red_of_rels hD hN hJ hR) hg hN hX
    rcases hi with hL | hG
    · have hx : xx i ∈ P := by
        have := sum_sub_mem (f := fun k => xx k) i fun k hk => (hL.2 k hk).1
        have := P.sub_mem h0 this
        rwa [sub_sub_cancel] at this
      have hy : yy i ∈ P := by
        have := sum_sub_mem (f := fun k => yy k) i fun k hk => (hL.2 k hk).2
        have := P.sub_mem h1 this
        rwa [sub_sub_cancel] at this
      exact all_false hX (fun k => by
        by_cases hk : k = i
        · subst hk; exact ⟨hx, hy⟩
        · exact hL.2 k hk) hw
    · have hne : i - 1 ≠ i := fun e => by
        haveI : Fact (1 < N) := ⟨by omega⟩
        exact one_ne_zero (by linear_combination -e : (1 : ZMod N) = 0)
      have hy : yy (i - 1) ∈ P := by
        have := sum_sub_mem (f := fun k => yy k) (i - 1) fun k hk => by
          by_cases hki : k = i
          · subst hki; exact hG.2.2
          · exact (hG.1 k hk hki).2
        have := P.sub_mem h1 this
        rwa [sub_sub_cancel] at this
      have hx : xx (i - 1) ∈ P := sub_mem_left hG.2.1 hy
      have hxi : xx i ∈ P := by
        have := sum_sub_mem (f := fun k => xx k) i fun k hk => by
          by_cases hki : k = i - 1
          · subst hki; exact hx
          · exact (hG.1 k hki hk).1
        have := P.sub_mem h0 this
        rwa [sub_sub_cancel] at this
      exact all_false hX (fun k => by
        by_cases hk : k = i
        · subst hk; exact ⟨hxi, hG.2.2⟩
        · by_cases hk' : k = i - 1
          · subst hk'; exact ⟨hx, hy⟩
          · exact hG.1 k hk' hk) hw
  · -- off `π = 0`: all `x_k` vanish, and the `y_k y_{k'}` relations
    have hx : ∀ k, xx k ∈ P := fun k => by
      have hc := hR.cub k
      have e : C D.π * xx k ^ 3 = ww O N * (yy k ^ 2 + xx k * yy k - C (D.π * D.b₄') * xx k *
          ww O N - C D.b₆' * ww O N ^ 2) - cub D.π D.b₄' D.b₆' k := by
        simp only [cub]
        ring
      have : C D.π * xx k ^ 3 ∈ P := by
        rw [e]
        exact P.sub_mem (P.mul_mem_right _ hw) hc
      exact hP.mem_of_pow_mem 3 ((hP.mem_or_mem this).resolve_left hπ)
    obtain ⟨hA, hB, -, -⟩ := hD
    have hyy : ∀ k d : ZMod N, 0 < d.val → 2 * d.val ≤ N → yy k * yy (k + d) ∈ P := by
      intro k d hpos hle
      have hd : d ≠ 0 := fun e => by rw [e, ZMod.val_zero] at hpos; exact lt_irrefl 0 hpos
      have hc : D.cP 2 d 2 2 - 1 ∈ 𝔪 := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · simpa [pY] using (hA d hpos hlt 2 2).2.2
        · simpa [pY] using (hB d heq 2 2).2.2
      have hb := hR.bil 2 hd k
      rw [bil_eq_yy] at hb
      have hrest : ww O N * (C (D.cP 2 d 0 0) * ww O N + C (D.cP 2 d 0 1) * xx (k + d) +
          C (D.cP 2 d 0 2) * yy (k + d) + C (D.cP 2 d 1 0) * xx k + C (D.cP 2 d 2 0) * yy k) +
          xx k * (C (D.cP 2 d 1 1) * xx (k + d) + C (D.cP 2 d 1 2) * yy (k + d)) +
          xx (k + d) * (C (D.cP 2 d 2 1) * yy k) ∈ P :=
        P.add_mem (P.add_mem (P.mul_mem_right _ hw) (P.mul_mem_right _ (hx k)))
          (P.mul_mem_right _ (hx _))
      have := sub_mem_left hb hrest
      exact (hP.mem_or_mem this).resolve_left fun h =>
        hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h ((isUnit_of_sub_one_mem hc).map C))
    have hpair : ∀ i j : ZMod N, i ≠ j → yy i * yy j ∈ P := fun i j hij => by
      have hd : j - i ≠ 0 := sub_ne_zero.2 hij.symm
      by_cases hle : 2 * (j - i).val ≤ N
      · have := hyy i (j - i) (val_pos_of_ne hd) hle
        rwa [add_sub_cancel] at this
      · obtain ⟨h', hpos⟩ := val_neg_lt hd (by omega)
        have := hyy j (-(j - i)) hpos h'.le
        rw [show j + -(j - i) = i by ring] at this
        rwa [mul_comm (yy j) (yy i)] at this
    by_cases hall0 : ∀ k, yy k ∈ P
    · exact all_false hX (fun k => ⟨hx k, hall0 k⟩) hw
    · push Not at hall0
      obtain ⟨i, hi⟩ := hall0
      have hoth : ∀ k, k ≠ i → yy k ∈ P := fun k hk =>
        (hP.mem_or_mem (hpair i k (Ne.symm hk))).resolve_left hi
      refine hi ?_
      have := sum_sub_mem (f := fun k => yy k) i hoth
      have := P.sub_mem h1 this
      rwa [sub_sub_cancel] at this


end Points

section Model

/-- The hypotheses on the coefficients used for the model map. -/
def Good (D : Coeffs O N) : Prop :=
  RedCoeffs N D (IsLocalRing.maximalIdeal O) ∧ 3 ≤ N ∧ IsUnit (D.g 1) ∧
    ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ n, D.π ∣ c ^ n

variable {D : Coeffs O N}

/-- The model misses the centre of the projection. -/
lemma hcov (hD : Good D) (z : (modelIdeal D).subscheme) :
    ∃ k, ιm D z ∈ SemistableReduction.LinearProjectionN.D (ℓψ D.ε D.κ) (ℓψ_mem D.ε D.κ) k := by
  obtain ⟨k, hk⟩ := exists_ℓψ_notMem (P := (ιm D z).asHomogeneousIdeal.toIdeal)
    (hP := (ιm D z).isPrime) hD.1 hD.2.1 hD.2.2.1 hD.2.2.2 (rels_ιm D z) (exists_X_notMem _)
  refine ⟨k, ?_⟩
  change linHom (ℓψ D.ε D.κ) (ℓψ_mem D.ε D.κ) (X k) ∉ _
  rwa [linHom_apply, aeval_X]

/-- The linear projection `[ℓ₀ : ℓ₁ : ℓ₂] : model ⟶ ℙ²_O`. -/
def ψ₀ (hD : Good D) : (modelIdeal D).subscheme ⟶ projSpace O 2 :=
  proj (ℓψ D.ε D.κ) (ℓψ_mem D.ε D.κ) (ιm D) (hcov hD)

lemma ψ₀_toSpec (hD : Good D) :
    ψ₀ hD ≫ projSpace.toSpec O 2 = ιm D ≫ projSpace.toSpec O (2 * N) :=
  proj_toSpec _ _ _ _

lemma mem_ψ₀_iff (hD : Good D) {g : MvPolynomial (Fin (2 + 1)) O} {d : ℕ}
    (hg : g ∈ 𝒜₂ d) (hd : 0 < d) (z : (modelIdeal D).subscheme) :
    g ∈ (ψ₀ hD z).asHomogeneousIdeal ↔ aeval (ℓψ D.ε D.κ) g ∈ (ιm D z).asHomogeneousIdeal :=
  mem_proj_iff _ hg hd z

instance (hD : Good D) : QuasiCompact (ψ₀ hD) := by
  have : QuasiCompact (ψ₀ hD ≫ projSpace.toSpec O 2) := by
    rw [ψ₀_toSpec]
    haveI : QuasiCompact (projSpace.toSpec O (2 * N)) := inferInstance
    infer_instance
  exact .of_comp _ (projSpace.toSpec O 2)

lemma modelIdeal_le_ker (hD : Good D) :
    TateModel.modelIdeal D.π D.b₄ D.b₆ ≤ (ψ₀ hD).ker := by
  refine le_trans ?_ (TateModel.radical_ker_le _)
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
  change (↑((ψ₀ hD).ker.support) : Set (projSpace O 2)) ⊆ _
  rw [Scheme.Hom.support_ker]
  refine (TateModel.cubicSet D.π D.b₄ D.b₆).isClosed.closure_subset_iff.2 ?_
  rintro _ ⟨z, rfl⟩
  refine not_not.2 ?_
  rw [mem_ψ₀_iff hD ((mem_homogeneousSubmodule _ _).2 (TateModel.isHomogeneous_F D.π D.b₄ D.b₆))
    three_pos]
  exact (rels_ιm D z).fℓ

/-- **The model map `ψ : model ⟶ 𝒯`** to the Tate model of `E_q`. -/
def ψ (hD : Good D) : (modelIdeal D).subscheme ⟶ (TateModel.modelIdeal D.π D.b₄ D.b₆).subscheme :=
  (ψ₀ hD).toImage ≫ Scheme.IdealSheafData.inclusion (modelIdeal_le_ker hD)

lemma ψ_ι (hD : Good D) : ψ hD ≫ TateModel.ι D.π D.b₄ D.b₆ = ψ₀ hD := by
  rw [ψ, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]

lemma ψ_toSpec (hD : Good D) :
    ψ hD ≫ TateModel.ι D.π D.b₄ D.b₆ ≫ projSpace.toSpec O 2 =
      ιm D ≫ projSpace.toSpec O (2 * N) := by
  rw [← Category.assoc, ψ_ι, ψ₀_toSpec]

lemma mem_ψ_iff (hD : Good D) {g : MvPolynomial (Fin (2 + 1)) O} {d : ℕ}
    (hg : g ∈ 𝒜₂ d) (hd : 0 < d) (z : (modelIdeal D).subscheme) :
    g ∈ (TateModel.ι D.π D.b₄ D.b₆ (ψ hD z)).asHomogeneousIdeal ↔
      aeval (ℓψ D.ε D.κ) g ∈ (ιm D z).asHomogeneousIdeal := by
  rw [← Scheme.Hom.comp_apply, ψ_ι]
  exact mem_ψ₀_iff hD hg hd z

end Model

end

end NGon

end TemperedFundamentalGroups
