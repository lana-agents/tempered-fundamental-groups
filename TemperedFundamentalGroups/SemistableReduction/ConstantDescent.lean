/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Descent of fibre-product witnesses along an extension of the constants (O1, step (F))

Blueprint §9.12, O1 (S7.9 (iii)/(iv)). Abstract setting: `k₀ ⊆ k` fields (the residue fields
`κ_E ⊆ k` of `O_E ⊆ O_C`), `ρᵢ : R → κᵢ` (`i = 1, 2`) maps of a ring `R` (the integral closure of
the node chart over `O_C`) to two `k`-algebras (the residue fields of the two branch vertices),
`B ⊆ R` a subring (the integral closure over `O_E`) with `ρᵢ(B) ⊆ Mᵢ` for subrings `Mᵢ ⊆ κᵢ`
(the residue fields over `E`) which are **linearly disjoint** from `k` over `k₀`
(`LinDisj`), and such that every reduction of `R` is a `k`-combination of reductions of `B`
(`IsSpanned`) and the constants `k₀` lift to `B`.

* `sum_split`: a `k`-combination of reductions of `B` is `Σ_l β_l ρ(y_l)` with `y_l ∈ B` for
  any `k₀`-basis `β` of a space containing the coefficients;
* `exists_decomp`: such bases exist (finite-dimensional spans);
* **`exists_fp_descent`**: a fibre-product witness `(y, s)` over `R` (`ρ₁ y = a ρ₁ s`,
  `ρ₂ y = b ρ₂ s`, `s` a unit at the point) for `a ∈ M₁`, `b ∈ M₂` can be chosen in `B`;
* **`exists_residue_eq_of_descent`**: if moreover the residues of `B` at the point lie in `k₀`,
  then so do the residues of all elements of `M₁` regular at the place.
-/

open Polynomial

namespace SemistableReduction

namespace ConstantDescent

variable {k₀ k : Type*} [Field k₀] [Field k] [Algebra k₀ k]

/-- `M ⊆ κ` is linearly disjoint from `k` over `k₀`: `k₀`-independent elements of `k` stay
independent over `M`. -/
def LinDisj (k₀ k : Type*) [Field k₀] [Field k] [Algebra k₀ k] {κ : Type*} [Field κ]
    [Algebra k κ] (M : Subring κ) : Prop :=
  ∀ {m : ℕ} (β : Fin m → k) (z : Fin m → κ), LinearIndependent k₀ β → (∀ l, z l ∈ M) →
    ∑ l, algebraMap k κ (β l) * z l = 0 → ∀ l, z l = 0

/-- Finite-dimensional subspaces of `k` have `k₀`-bases (as families in `k`). -/
theorem exists_decomp_of_finiteDimensional (W : Submodule k₀ k) [FiniteDimensional k₀ W] :
    ∃ (m : ℕ) (β : Fin m → k), LinearIndependent k₀ β ∧ (∀ l, β l ∈ W) ∧
      ∀ s ∈ W, ∃ c : Fin m → k₀, s = ∑ l, algebraMap k₀ k (c l) * β l := by
  classical
  let b := Module.finBasis k₀ W
  refine ⟨Module.finrank k₀ W, fun l ↦ (b l : k), ?_, fun l ↦ (b l).2, fun s hsW ↦ ?_⟩
  · exact b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  · refine ⟨fun l ↦ b.repr ⟨s, hsW⟩ l, ?_⟩
    have := congrArg (Subtype.val : W → k) (b.sum_repr ⟨s, hsW⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [← Algebra.smul_def]
    exact this.symm

/-- Finite families in `k` have coordinates in a common `k₀`-independent family. -/
theorem exists_decomp (S : Finset k) :
    ∃ (m : ℕ) (β : Fin m → k), LinearIndependent k₀ β ∧
      ∀ s ∈ S, ∃ c : Fin m → k₀, s = ∑ l, algebraMap k₀ k (c l) * β l := by
  classical
  let W := Submodule.span k₀ (S : Set k)
  haveI : FiniteDimensional k₀ W := FiniteDimensional.span_finset k₀ S
  let b := Module.finBasis k₀ W
  refine ⟨Module.finrank k₀ W, fun l ↦ (b l : k), ?_, fun s hs ↦ ?_⟩
  · exact b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  · have hsW : s ∈ W := Submodule.subset_span hs
    refine ⟨fun l ↦ b.repr ⟨s, hsW⟩ l, ?_⟩
    have := congrArg (Subtype.val : W → k) (b.sum_repr ⟨s, hsW⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [← Algebra.smul_def]
    exact this.symm

variable {κ R : Type*} [Field κ] [Algebra k κ] [CommRing R]

/-- **Splitting a `k`-combination of reductions along a `k₀`-basis.** -/
theorem sum_split (ρ : R →+* κ) {n m : ℕ} (lam : Fin n → k) (b : Fin n → R) (β : Fin m → k)
    (c : Fin n → Fin m → k₀) (hc : ∀ j, lam j = ∑ l, algebraMap k₀ k (c j l) * β l)
    (o : Fin n → Fin m → R) (ho : ∀ j l, ρ (o j l) = algebraMap k κ (algebraMap k₀ k (c j l))) :
    ∑ j, algebraMap k κ (lam j) * ρ (b j) =
      ∑ l, algebraMap k κ (β l) * ρ (∑ j, o j l * b j) := by
  simp only [hc, map_sum, map_mul, ho, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- A `k`-combination of reductions of `B`, for both reductions at once. -/
def IsSpanned (k : Type*) [Field k] {κ₁ κ₂ : Type*} [Field κ₁] [Field κ₂] [Algebra k κ₁]
    [Algebra k κ₂] (B : Subring R) (ρ₁ : R →+* κ₁) (ρ₂ : R →+* κ₂) (y : R) : Prop :=
  ∃ (n : ℕ) (lam : Fin n → k) (b : Fin n → R), (∀ j, b j ∈ B) ∧
    ρ₁ y = ∑ j, algebraMap k κ₁ (lam j) * ρ₁ (b j) ∧
    ρ₂ y = ∑ j, algebraMap k κ₂ (lam j) * ρ₂ (b j)

variable {κ₁ κ₂ : Type*} [Field κ₁] [Field κ₂] [Algebra k κ₁] [Algebra k κ₂]
  {B : Subring R} {ρ₁ : R →+* κ₁} {ρ₂ : R →+* κ₂}

/-- **Splitting a spanned element along a `k₀`-basis**: if `y, s` are spanned, there are a
`k₀`-independent `β` and `y_l, s_l ∈ B` with `ρᵢ y = Σ β_l ρᵢ y_l`, `ρᵢ s = Σ β_l ρᵢ s_l`. -/
theorem exists_split
    (hconst : ∀ c : k₀, ∃ o ∈ B, ρ₁ o = algebraMap k κ₁ (algebraMap k₀ k c) ∧
      ρ₂ o = algebraMap k κ₂ (algebraMap k₀ k c))
    {y s : R} (hy : IsSpanned k B ρ₁ ρ₂ y) (hs : IsSpanned k B ρ₁ ρ₂ s) (T : Finset k) :
    ∃ (m : ℕ) (β : Fin m → k) (yl sl : Fin m → R), LinearIndependent k₀ β ∧
      (∀ l, yl l ∈ B) ∧ (∀ l, sl l ∈ B) ∧
      (∀ t ∈ T, ∃ c : Fin m → k₀, t = ∑ l, algebraMap k₀ k (c l) * β l) ∧
      ρ₁ y = ∑ l, algebraMap k κ₁ (β l) * ρ₁ (yl l) ∧
      ρ₂ y = ∑ l, algebraMap k κ₂ (β l) * ρ₂ (yl l) ∧
      ρ₁ s = ∑ l, algebraMap k κ₁ (β l) * ρ₁ (sl l) ∧
      ρ₂ s = ∑ l, algebraMap k κ₂ (β l) * ρ₂ (sl l) := by
  classical
  obtain ⟨n, lam, b, hb, hy₁, hy₂⟩ := hy
  obtain ⟨n', mu, b', hb', hs₁, hs₂⟩ := hs
  obtain ⟨m, β, hβ, hdec⟩ := exists_decomp (k₀ := k₀)
    (Finset.univ.image lam ∪ Finset.univ.image mu ∪ T)
  choose c hc using fun j ↦ hdec (lam j) (by simp)
  choose c' hc' using fun j ↦ hdec (mu j) (by simp)
  choose o ho using hconst
  refine ⟨m, β, fun l ↦ ∑ j, o (c j l) * b j, fun l ↦ ∑ j, o (c' j l) * b' j, hβ,
    fun l ↦ Subring.sum_mem _ fun j _ ↦ B.mul_mem (ho _).1 (hb j),
    fun l ↦ Subring.sum_mem _ fun j _ ↦ B.mul_mem (ho _).1 (hb' j),
    fun t ht ↦ hdec t (by simp [ht]), ?_, ?_, ?_, ?_⟩
  · rw [hy₁]; exact sum_split ρ₁ lam b β c hc (fun j l ↦ o (c j l)) fun j l ↦ (ho _).2.1
  · rw [hy₂]; exact sum_split ρ₂ lam b β c hc (fun j l ↦ o (c j l)) fun j l ↦ (ho _).2.2
  · rw [hs₁]; exact sum_split ρ₁ mu b' β c' hc' (fun j l ↦ o (c' j l)) fun j l ↦ (ho _).2.1
  · rw [hs₂]; exact sum_split ρ₂ mu b' β c' hc' (fun j l ↦ o (c' j l)) fun j l ↦ (ho _).2.2

/-- Coefficientwise equations from linear disjointness. -/
lemma eq_of_linDisj {κ : Type*} [Field κ] [Algebra k κ] {M : Subring κ} (hLD : LinDisj k₀ k M)
    {m : ℕ} {β : Fin m → k} (hβ : LinearIndependent k₀ β) {a : κ} (ha : a ∈ M)
    {Y S : Fin m → κ} (hY : ∀ l, Y l ∈ M) (hS : ∀ l, S l ∈ M)
    (h : ∑ l, algebraMap k κ (β l) * Y l = a * ∑ l, algebraMap k κ (β l) * S l) :
    ∀ l, Y l = a * S l := by
  have := hLD β (fun l ↦ Y l - a * S l) hβ (fun l ↦ M.sub_mem (hY l) (M.mul_mem ha (hS l)))
    (by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [h, Finset.mul_sum]
      simp only [sub_eq_zero]
      exact Finset.sum_congr rfl fun l _ ↦ by ring)
  exact fun l ↦ sub_eq_zero.mp (this l)

/-- **Descent of fibre-product witnesses.** Let `(y, s)` be a witness over `R` for `(a, b)`
(`ρ₁ y = a ρ₁ s`, `ρ₂ y = b ρ₂ s`, `s` a unit at the point `P`, i.e. of nonzero residue `r₁`),
with `a ∈ M₁`, `b ∈ M₂`. If `y, s` are spanned by `B` and `M₁, M₂` are linearly disjoint from
`k` over `k₀`, there is a witness in `B`. -/
theorem exists_fp_descent {M₁ : Subring κ₁} {M₂ : Subring κ₂}
    (hM₁ : ∀ b ∈ B, ρ₁ b ∈ M₁) (hM₂ : ∀ b ∈ B, ρ₂ b ∈ M₂)
    (hLD₁ : LinDisj k₀ k M₁) (hLD₂ : LinDisj k₀ k M₂)
    (hconst : ∀ c : k₀, ∃ o ∈ B, ρ₁ o = algebraMap k κ₁ (algebraMap k₀ k c) ∧
      ρ₂ o = algebraMap k κ₂ (algebraMap k₀ k c))
    (V₁ : Subring κ₁) (r₁ : V₁ →+* k) (hρV : ∀ y, ρ₁ y ∈ V₁)
    (hVk : ∀ t : k, algebraMap k κ₁ t ∈ V₁)
    {a : κ₁} {b : κ₂} (ha : a ∈ M₁) (hb : b ∈ M₂) {y s : R}
    (hys : IsSpanned k B ρ₁ ρ₂ y) (hss : IsSpanned k B ρ₁ ρ₂ s)
    (hs : r₁ ⟨ρ₁ s, hρV s⟩ ≠ 0) (h₁ : ρ₁ y = a * ρ₁ s) (h₂ : ρ₂ y = b * ρ₂ s) :
    ∃ y' ∈ B, ∃ s' ∈ B, r₁ ⟨ρ₁ s', hρV s'⟩ ≠ 0 ∧ ρ₁ y' = a * ρ₁ s' ∧ ρ₂ y' = b * ρ₂ s' := by
  classical
  obtain ⟨m, β, yl, sl, hβ, hyl, hsl, -, ey₁, ey₂, es₁, es₂⟩ :=
    exists_split (k₀ := k₀) hconst hys hss ∅
  have e₁ := eq_of_linDisj hLD₁ hβ ha (fun l ↦ hM₁ _ (hyl l)) (fun l ↦ hM₁ _ (hsl l))
    (by rw [← ey₁, ← es₁, h₁])
  have e₂ := eq_of_linDisj hLD₂ hβ hb (fun l ↦ hM₂ _ (hyl l)) (fun l ↦ hM₂ _ (hsl l))
    (by rw [← ey₂, ← es₂, h₂])
  -- some `s_l` is a unit at the point
  obtain ⟨l, hl⟩ : ∃ l, r₁ ⟨ρ₁ (sl l), hρV _⟩ ≠ 0 := by
    by_contra! hall
    apply hs
    have : (⟨ρ₁ s, hρV s⟩ : V₁) = ∑ l, ⟨_, hVk (β l)⟩ * ⟨ρ₁ (sl l), hρV _⟩ := by
      apply Subtype.ext
      change ρ₁ s = _
      rw [es₁]
      push_cast
      rfl
    rw [this, map_sum]
    exact Finset.sum_eq_zero fun l _ ↦ by rw [map_mul, hall l, mul_zero]
  exact ⟨yl l, hyl l, sl l, hsl l, hl, e₁ l, e₂ l⟩

/-- **Residues of `M₁` lie in `k₀`** once the residues of `B` do: for `a ∈ M₁` regular at the
place with residue `λ`, a witness `(y, s)` over `R` for the pair `(a, λ)` splits along a `k₀`-basis
of a `k₀(λ)`-stable space; comparing residues gives `λ γ_n = Σ_l C_{ln} γ_l` with `γ_l ∈ k₀`
(the residues of the `s_l ∈ B`) not all zero and `C` the matrix of `λ`, so `λ ∈ k₀`. -/
theorem exists_residue_eq [Algebra.IsAlgebraic k₀ k] {M₁ : Subring κ₁} {M₂ : Subring κ₂}
    (hM₁ : ∀ b ∈ B, ρ₁ b ∈ M₁) (hM₂ : ∀ b ∈ B, ρ₂ b ∈ M₂)
    (hLD₁ : LinDisj k₀ k M₁) (hLD₂ : LinDisj k₀ k M₂)
    (hconst : ∀ c : k₀, ∃ o ∈ B, ρ₁ o = algebraMap k κ₁ (algebraMap k₀ k c) ∧
      ρ₂ o = algebraMap k κ₂ (algebraMap k₀ k c))
    (V₁ : Subring κ₁) (r₁ : V₁ →+* k) (hρV₁ : ∀ y, ρ₁ y ∈ V₁)
    (hVk₁ : ∀ t : k, algebraMap k κ₁ t ∈ V₁)
    (V₂ : Subring κ₂) (r₂ : V₂ →+* k) (hρV₂ : ∀ y, ρ₂ y ∈ V₂)
    (hVk₂ : ∀ t : k, algebraMap k κ₂ t ∈ V₂) (hr₂ : ∀ t : k, r₂ ⟨_, hVk₂ t⟩ = t)
    (hcomp : ∀ y, r₁ ⟨ρ₁ y, hρV₁ y⟩ = r₂ ⟨ρ₂ y, hρV₂ y⟩)
    (hresB : ∀ b ∈ B, ∃ c : k₀, r₁ ⟨ρ₁ b, hρV₁ b⟩ = algebraMap k₀ k c)
    {a : κ₁} (ha : a ∈ M₁) (haV : a ∈ V₁) {y s : R}
    (hys : IsSpanned k B ρ₁ ρ₂ y) (hss : IsSpanned k B ρ₁ ρ₂ s)
    (hs : r₁ ⟨ρ₁ s, hρV₁ s⟩ ≠ 0) (h₁ : ρ₁ y = a * ρ₁ s)
    (h₂ : ρ₂ y = algebraMap k κ₂ (r₁ ⟨a, haV⟩) * ρ₂ s) :
    ∃ c : k₀, r₁ ⟨a, haV⟩ = algebraMap k₀ k c := by
  classical
  set lam := r₁ ⟨a, haV⟩ with hlam
  obtain ⟨n, ly, by', hby', hy₁, hy₂⟩ := hys
  obtain ⟨n', ls, bs', hbs', hs₁, hs₂⟩ := hss
  -- a `k₀(λ)`-stable finite-dimensional space containing the coefficients
  let Kl := IntermediateField.adjoin k₀ {lam}
  haveI : FiniteDimensional k₀ Kl :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral lam)
  let S : Finset k := Finset.univ.image ly ∪ Finset.univ.image ls
  let WK : Submodule Kl k := Submodule.span Kl (S : Set k)
  haveI : FiniteDimensional Kl WK := FiniteDimensional.span_finset Kl S
  haveI : FiniteDimensional k₀ WK := Module.Finite.trans Kl WK
  let W : Submodule k₀ k := WK.restrictScalars k₀
  haveI : FiniteDimensional k₀ W := ‹FiniteDimensional k₀ WK›
  obtain ⟨m, β, hβ, hβW, hdec⟩ := exists_decomp_of_finiteDimensional W
  have hlamW : ∀ w ∈ W, lam * w ∈ W := fun w hw ↦
    WK.smul_mem (⟨lam, IntermediateField.mem_adjoin_simple_self k₀ lam⟩ : Kl) hw
  choose c hc using fun j ↦ hdec (ly j) (Submodule.subset_span (by simp [S]))
  choose c' hc' using fun j ↦ hdec (ls j) (Submodule.subset_span (by simp [S]))
  choose C hC using fun l ↦ hdec (lam * β l) (hlamW _ (hβW l))
  choose o ho using hconst
  set yl : Fin m → R := fun l ↦ ∑ j, o (c j l) * by' j
  set sl : Fin m → R := fun l ↦ ∑ j, o (c' j l) * bs' j
  have hyl : ∀ l, yl l ∈ B := fun l ↦ Subring.sum_mem _ fun j _ ↦ B.mul_mem (ho _).1 (hby' j)
  have hsl : ∀ l, sl l ∈ B := fun l ↦ Subring.sum_mem _ fun j _ ↦ B.mul_mem (ho _).1 (hbs' j)
  have ey₁ : ρ₁ y = ∑ l, algebraMap k κ₁ (β l) * ρ₁ (yl l) := by
    rw [hy₁]; exact sum_split ρ₁ ly by' β c hc (fun j l ↦ o (c j l)) fun j l ↦ (ho _).2.1
  have ey₂ : ρ₂ y = ∑ l, algebraMap k κ₂ (β l) * ρ₂ (yl l) := by
    rw [hy₂]; exact sum_split ρ₂ ly by' β c hc (fun j l ↦ o (c j l)) fun j l ↦ (ho _).2.2
  have es₁ : ρ₁ s = ∑ l, algebraMap k κ₁ (β l) * ρ₁ (sl l) := by
    rw [hs₁]; exact sum_split ρ₁ ls bs' β c' hc' (fun j l ↦ o (c' j l)) fun j l ↦ (ho _).2.1
  have es₂ : ρ₂ s = ∑ l, algebraMap k κ₂ (β l) * ρ₂ (sl l) := by
    rw [hs₂]; exact sum_split ρ₂ ls bs' β c' hc' (fun j l ↦ o (c' j l)) fun j l ↦ (ho _).2.2
  -- the first branch: `ρ₁ y_n = a ρ₁ s_n`
  have e₁ := eq_of_linDisj hLD₁ hβ ha (fun l ↦ hM₁ _ (hyl l)) (fun l ↦ hM₁ _ (hsl l))
    (by rw [← ey₁, ← es₁, h₁])
  -- the second branch: `ρ₂ y_n = Σ_l C_{ln} ρ₂ s_l`
  have hC₂ : ∀ l n, algebraMap k κ₂ (algebraMap k₀ k (C l n)) ∈ M₂ := fun l n ↦ by
    rw [← (ho (C l n)).2.2]; exact hM₂ _ (ho _).1
  have e₂ : ∀ n, ρ₂ (yl n) = ∑ l, algebraMap k κ₂ (algebraMap k₀ k (C l n)) * ρ₂ (sl l) := by
    have := hLD₂ β (fun n ↦ ρ₂ (yl n) -
        ∑ l, algebraMap k κ₂ (algebraMap k₀ k (C l n)) * ρ₂ (sl l)) hβ
      (fun n ↦ M₂.sub_mem (hM₂ _ (hyl n))
        (M₂.sum_mem fun l _ ↦ M₂.mul_mem (hC₂ l n) (hM₂ _ (hsl l)))) (by
        have h := h₂
        rw [ey₂, es₂, Finset.mul_sum] at h
        simp only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero]
        rw [h]
        calc ∑ l, algebraMap k κ₂ lam * (algebraMap k κ₂ (β l) * ρ₂ (sl l))
            = ∑ l, ∑ n, algebraMap k κ₂ (β n) *
                (algebraMap k κ₂ (algebraMap k₀ k (C l n)) * ρ₂ (sl l)) := by
              refine Finset.sum_congr rfl fun l _ ↦ ?_
              rw [← mul_assoc, ← map_mul, hC l, map_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun n _ ↦ ?_
              rw [map_mul]; ring
          _ = _ := by
              rw [Finset.sum_comm]
              simp only [Finset.mul_sum])
    exact fun n ↦ sub_eq_zero.mp (this n)
  -- residues
  choose g hg using fun l ↦ hresB _ (hsl l)
  have hres : ∀ n, lam * algebraMap k₀ k (g n) = ∑ l, algebraMap k₀ k (C l n) *
      algebraMap k₀ k (g l) := by
    intro n
    have r1 : r₁ ⟨ρ₁ (yl n), hρV₁ _⟩ = lam * algebraMap k₀ k (g n) := by
      rw [← hg n]
      have : (⟨ρ₁ (yl n), hρV₁ _⟩ : V₁) = ⟨a, haV⟩ * ⟨ρ₁ (sl n), hρV₁ _⟩ :=
        Subtype.ext (e₁ n)
      rw [this, map_mul]
    have r2 : r₂ ⟨ρ₂ (yl n), hρV₂ _⟩ = ∑ l, algebraMap k₀ k (C l n) * algebraMap k₀ k (g l) := by
      have : (⟨ρ₂ (yl n), hρV₂ _⟩ : V₂) =
          ∑ l, ⟨_, hVk₂ (algebraMap k₀ k (C l n))⟩ * ⟨ρ₂ (sl l), hρV₂ _⟩ := by
        apply Subtype.ext
        change ρ₂ (yl n) = _
        rw [e₂ n]
        push_cast
        rfl
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [map_mul, hr₂, ← hcomp, hg l]
    rw [← r1, hcomp, r2]
  -- some `γ_n` is nonzero
  obtain ⟨n, hn⟩ : ∃ n, g n ≠ 0 := by
    by_contra! hall
    apply hs
    have : (⟨ρ₁ s, hρV₁ s⟩ : V₁) = ∑ l, ⟨_, hVk₁ (β l)⟩ * ⟨ρ₁ (sl l), hρV₁ _⟩ := by
      apply Subtype.ext
      change ρ₁ s = _
      rw [es₁]
      push_cast
      rfl
    rw [this, map_sum]
    exact Finset.sum_eq_zero fun l _ ↦ by rw [map_mul, hg l, hall l, map_zero, mul_zero]
  refine ⟨(∑ l, C l n * g l) / g n, ?_⟩
  have hgn : algebraMap k₀ k (g n) ≠ 0 := (map_ne_zero_iff _ (algebraMap k₀ k).injective).mpr hn
  rw [map_div₀, eq_div_iff hgn, hres n, map_sum]
  simp only [map_mul]

/-- **Rational residues**: if every reduction is spanned by a subring `G ⊆ B` whose residues
lie in `k₀`, then all residues of `B` lie in `k₀` (`M₁` linearly disjoint from `k`). -/
theorem exists_residue_eq_of_span {M₁ : Subring κ₁} (hM₁ : ∀ b ∈ B, ρ₁ b ∈ M₁)
    (hLD₁ : LinDisj k₀ k M₁)
    (hconst : ∀ c : k₀, ∃ o ∈ B, ρ₁ o = algebraMap k κ₁ (algebraMap k₀ k c) ∧
      ρ₂ o = algebraMap k κ₂ (algebraMap k₀ k c))
    (V₁ : Subring κ₁) (r₁ : V₁ →+* k) (hρV : ∀ y, ρ₁ y ∈ V₁)
    (hVk : ∀ t : k, algebraMap k κ₁ t ∈ V₁) (hr : ∀ t : k, r₁ ⟨_, hVk t⟩ = t)
    {G : Subring R} (hGB : G ≤ B) (hGres : ∀ g ∈ G, ∃ c : k₀, r₁ ⟨ρ₁ g, hρV g⟩ = algebraMap k₀ k c)
    (hspan : ∀ y, IsSpanned k G ρ₁ ρ₂ y) {b : R} (hb : b ∈ B) :
    ∃ c : k₀, r₁ ⟨ρ₁ b, hρV b⟩ = algebraMap k₀ k c := by
  classical
  obtain ⟨n, lam, g, hg, h₁, -⟩ := hspan b
  obtain ⟨m, β, hβ, hdec⟩ := exists_decomp (k₀ := k₀) (Finset.univ.image lam ∪ {1})
  choose c hc using fun j ↦ hdec (lam j) (by simp)
  obtain ⟨c₁, hc₁⟩ := hdec 1 (by simp)
  choose o ho using hconst
  set yl : Fin m → R := fun l ↦ ∑ j, o (c j l) * g j
  have hyl : ∀ l, yl l ∈ B := fun l ↦
    Subring.sum_mem _ fun j _ ↦ B.mul_mem (ho _).1 (hGB (hg j))
  have ey : ρ₁ b = ∑ l, algebraMap k κ₁ (β l) * ρ₁ (yl l) := by
    rw [h₁]; exact sum_split ρ₁ lam g β c hc (fun j l ↦ o (c j l)) fun j l ↦ (ho _).2.1
  -- residues of the `y_l` are rational
  have hres : ∀ l, ∃ c' : k₀, r₁ ⟨ρ₁ (yl l), hρV _⟩ = algebraMap k₀ k c' := by
    intro l
    choose d hd using fun j ↦ hGres (g j) (hg j)
    refine ⟨∑ j, c j l * d j, ?_⟩
    have : (⟨ρ₁ (yl l), hρV _⟩ : V₁) =
        ∑ j, ⟨_, hVk (algebraMap k₀ k (c j l))⟩ * ⟨ρ₁ (g j), hρV _⟩ := by
      apply Subtype.ext
      change ρ₁ (yl l) = _
      simp only [yl, map_sum, map_mul, (ho _).2.1]
      push_cast
      rfl
    rw [this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, hr, hd, map_mul]
  -- compare with `1 = Σ c₁ β`
  have e1 : ∀ l, ρ₁ (yl l) = algebraMap k κ₁ (algebraMap k₀ k (c₁ l)) * ρ₁ b := by
    have := hLD₁ β (fun l ↦ ρ₁ (yl l) - algebraMap k κ₁ (algebraMap k₀ k (c₁ l)) * ρ₁ b) hβ
      (fun l ↦ M₁.sub_mem (hM₁ _ (hyl l)) (M₁.mul_mem (by
        rw [← (ho (c₁ l)).2.1]; exact hM₁ _ (ho _).1) (hM₁ _ hb))) (by
        simp only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero]
        rw [← ey]
        have : ρ₁ b = algebraMap k κ₁ 1 * ρ₁ b := by rw [map_one, one_mul]
        conv_lhs => rw [this, hc₁]
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [map_mul]; ring)
    exact fun l ↦ sub_eq_zero.mp (this l)
  obtain ⟨l, hl⟩ : ∃ l, c₁ l ≠ 0 := by
    by_contra! hall
    have h := hc₁
    simp only [hall, map_zero, zero_mul, Finset.sum_const_zero] at h
    exact one_ne_zero h
  obtain ⟨c', hc'⟩ := hres l
  refine ⟨c' / c₁ l, ?_⟩
  have hb' : (⟨ρ₁ (yl l), hρV _⟩ : V₁) =
      ⟨_, hVk (algebraMap k₀ k (c₁ l))⟩ * ⟨ρ₁ b, hρV b⟩ := Subtype.ext (e1 l)
  rw [hb', map_mul, hr] at hc'
  have hne : algebraMap k₀ k (c₁ l) ≠ 0 := (map_ne_zero_iff _ (algebraMap k₀ k).injective).mpr hl
  rw [map_div₀, eq_div_iff hne, ← hc', mul_comm]

end ConstantDescent

end SemistableReduction
