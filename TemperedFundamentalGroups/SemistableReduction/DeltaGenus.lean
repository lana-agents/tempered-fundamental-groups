/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DeltaCount
import TemperedFundamentalGroups.SemistableReduction.MultiGauss

/-!
# The δ-count for a set of vertices

Blueprint §9.9, S7.6 (abstract form). Let `S` be the set of all extensions to `F` of the Gauss
points of finitely many coordinates (a vertex set `V'`, S7.4). Suppose `D_m` are divisors of `F`
with divisors `D̄_{m,W}` on the residue curves (`W ∈ S`) such that
* `Σ_W deg D̄_{m,W} = deg D_m` and `deg D̄_{m,W} ≥ m`;
* the reduction of every `f ∈ L(D_m)` with `‖f‖_S ≤ 1` lies in `Π_W L(D̄_{m,W})`;
and let *points* `p` be given by pairwise disjoint sets of branches (where the `D̄_{m,W}` vanish)
and condition spaces `O p` containing all these reductions.

* `sum_genus_add_le`: if the families `t p` (regular at the branches of `p`) are independent
  modulo `O p + K_{M,p}`, then `Σ_W g(κ(W)) + Σ_p #(t p) ≤ g(F) + #S - 1`;
* `sum_genus_add_card_le`: if every `O p` consists of elements with equal residues at the
  branches of `p`, then `Σ_W g(κ(W)) + Σ_p (r_p - 1) ≤ g(F) + #S - 1` (`b₁` form);
* `not_indep_of_le`: if conversely `g(F) + #S - 1 ≤ Σ_W g(κ(W)) + Σ_p (r_p - 1)` (S8), then at
  every point no `r_p` elements regular at the branches are independent modulo
  `O p + K_{M, p}`: **`δ'_p = 0`** at every jet order `M ≥ 1`.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion GaussFibre DeltaCount

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra C F]
  [IsAlgClosed C] [CharZero C] [IsCurveFunctionField C F]
  {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-- The residue curve of a vertex. -/
abbrev Kappa (S : Finset (TypeTwo C F)) (W : S) : Type _ := ResidueField W.1.val.valuationSubring

/-- The reduction of `f` at all vertices of `S`. -/
noncomputable def redVec (S : Finset (TypeTwo C F)) (f : F) : Π W : S, Kappa S W :=
  fun W ↦ W.1.red f

include hp hp1 in
/-- **The δ-count for a set of vertices** (S7.6, abstract form). -/
theorem sum_genus_add_le {I : Type*} [Finite I] [Nonempty I] (x : I → F)
    (hx : ∀ i, Transcendental C (x i)) (S : Finset (TypeTwo C F))
    (hS : ∀ W, W ∈ S ↔ ∃ i, IsOver (hx i) W)
    (D : ℕ → CurveDivisor C F) (Db : ℕ → ∀ W : S, CurveDivisor 𝓀 (Kappa S W))
    (hdeg : ∀ m, ∑ W, (Db m W).degree = (D m).degree)
    (hlarge : ∀ (m : ℕ) W, (m : ℤ) ≤ (Db m W).degree)
    (hred : ∀ m f, f ∈ rrSpace (D m) → mnorm S f ≤ 1 → redVec S f ∈ piRR 𝓀 (Kappa S) (Db m))
    {ι : Type*} [Fintype ι] (Sp : ι → Finset (Branch 𝓀 (Kappa S)))
    (hdisj : ∀ p q, p ≠ q → Disjoint (Sp p) (Sp q)) (hzero : ∀ m p, ∀ b ∈ Sp p, Db m b.1 b.2 = 0)
    (O : ι → Submodule 𝓀 (Π W : S, Kappa S W))
    (hO : ∀ m f, f ∈ rrSpace (D m) → mnorm S f ≤ 1 → ∀ p, redVec S f ∈ O p) (M : ℕ)
    {T : ι → Type*} [∀ p, Fintype (T p)] (t : ∀ p, T p → Π W : S, Kappa S W)
    (ht : ∀ p i, t p i ∈ regAt 𝓀 (Kappa S) (Sp p))
    (hind : ∀ p, ∀ a : T p → 𝓀, ∑ i, a i • t p i ∈ O p ⊔ jetKer 𝓀 (Kappa S) M (Sp p) → a = 0) :
    (∑ W : S, (genus 𝓀 (Kappa S W) : ℤ)) + ∑ p, (Fintype.card (T p) : ℤ) ≤
      genus C F + S.card - 1 := by
  classical
  obtain ⟨c, hc⟩ := finrank_add_sum_le (k := 𝓀) (κ := Kappa S) Sp (T := T)
  obtain ⟨cF, hcF⟩ := ell_eq_of_le_degree (k := C) (κ := F)
  choose cW hcW using fun W : S ↦ ell_eq_of_le_degree (k := 𝓀) (κ := Kappa S W)
  have hSne : 0 < S.card := by
    obtain ⟨i⟩ := ‹Nonempty I›
    by_contra h
    simp only [not_lt, nonpos_iff_eq_zero, Finset.card_eq_zero] at h
    obtain ⟨W, hW⟩ := exists_isOver hp hp1 (hx i)
    have := (hS W).2 ⟨i, hW⟩
    rw [h] at this
    exact Finset.notMem_empty W this
  -- a large `m`
  set s : ℕ := ∑ W, ((c W).toNat + (cW W).toNat)
  set m : ℕ := cF.toNat + s + M * ∑ p, (Sp p).card
  have hm : (m : ℤ) = cF.toNat + s + M * ((∑ p, (Sp p).card : ℕ) : ℤ) := by
    push_cast [m]; ring
  have hmW (W : S) : c W + M * ((∑ p, (Sp p).card : ℕ) : ℤ) ≤ (Db m W).degree ∧
      cW W ≤ (Db m W).degree := by
    have h1 := hlarge m W
    have h2 : (c W).toNat + (cW W).toNat ≤ s :=
      Finset.single_le_sum (f := fun W ↦ (c W).toNat + (cW W).toNat) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ W)
    have h2' : ((c W).toNat : ℤ) + (cW W).toNat ≤ s := by exact_mod_cast h2
    have h3 := Int.self_le_toNat (c W)
    have h4 := Int.self_le_toNat (cW W)
    have h5 : (0 : ℤ) ≤ cF.toNat := Int.natCast_nonneg _
    have h6 : (0 : ℤ) ≤ (cW W).toNat := Int.natCast_nonneg _
    have h7 : (0 : ℤ) ≤ (c W).toNat := Int.natCast_nonneg _
    have h8 : (0 : ℤ) ≤ M * ((∑ p, (Sp p).card : ℕ) : ℤ) :=
      mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    exact ⟨by linarith only [h1, h2', h3, h5, h6, hm],
      by linarith only [h1, h2', h4, h5, h7, h8, hm]⟩
  have hmF : cF ≤ (D m).degree := by
    rw [← hdeg m]
    obtain ⟨W₀⟩ : Nonempty S := by
      obtain ⟨W, hW⟩ := Finset.card_pos.1 hSne
      exact ⟨⟨W, hW⟩⟩
    have h1 : (Db m W₀).degree ≤ ∑ W, (Db m W).degree :=
      Finset.single_le_sum (f := fun W ↦ (Db m W).degree)
        (fun W _ ↦ (Int.natCast_nonneg m).trans (hlarge m W)) (Finset.mem_univ W₀)
    have h2 := hlarge m W₀
    have h3 := Int.self_le_toNat cF
    have : (cF.toNat : ℤ) ≤ m := by
      have : cF.toNat ≤ m := le_trans (Nat.le_add_right _ s) (Nat.le_add_right _ _)
      exact_mod_cast this
    linarith
  -- the space of reductions
  set R : Submodule 𝓀 (Π W : S, Kappa S W) := Submodule.span 𝓀
    {a | ∃ f ∈ rrSpace (D m), mnorm S f ≤ 1 ∧ redVec S f = a}
  have hR : R ≤ piRR 𝓀 (Kappa S) (Db m) := Submodule.span_le.2 fun a ⟨f, hf, hn, hfa⟩ ↦
    hfa ▸ hred m f hf hn
  haveI : FiniteDimensional 𝓀 R := Submodule.finiteDimensional_of_le hR
  have hRO (p : ι) : R ≤ O p ⊔ jetKer 𝓀 (Kappa S) M (Sp p) :=
    le_sup_of_le_left (Submodule.span_le.2 fun a ⟨f, hf, hn, hfa⟩ ↦ hfa ▸ hO m f hf hn p)
  have hcount := hc (Db m) M (fun W ↦ (hmW W).1) (hzero m) hdisj O R hR hRO t ht hind
  have hell : ell (D m) ≤ Module.finrank 𝓀 R :=
    finrank_le_of_red_mem hp hp1 x hx S hS (rrSpace (D m)) R fun f hf hn ↦
      Submodule.subset_span ⟨f, hf, hn, rfl⟩
  have hF := hcF (D m) hmF
  have hW (W : S) := hcW W (Db m W) (hmW W).2
  have h1 : (ell (D m) : ℤ) + ∑ p, (Fintype.card (T p) : ℤ) ≤ ∑ W, (ell (Db m W) : ℤ) := by
    have : ell (D m) + ∑ p, Fintype.card (T p) ≤ ∑ W, ell (Db m W) := le_trans (by omega) hcount
    exact_mod_cast this
  rw [hF, ← hdeg m] at h1
  simp only [hW] at h1
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one] at h1
  linarith

section Corollaries

include hp hp1 in
/-- The δ-count with independent finite sets (`sum_genus_add_le`). -/
theorem sum_genus_add_card_le
    {I : Type*} [Finite I] [Nonempty I] (x : I → F)
    (hx : ∀ i, Transcendental C (x i)) (S : Finset (TypeTwo C F))
    (hS : ∀ W, W ∈ S ↔ ∃ i, IsOver (hx i) W)
    (D : ℕ → CurveDivisor C F) (Db : ℕ → ∀ W : S, CurveDivisor 𝓀 (Kappa S W))
    (hdeg : ∀ m, ∑ W, (Db m W).degree = (D m).degree)
    (hlarge : ∀ (m : ℕ) W, (m : ℤ) ≤ (Db m W).degree)
    (hred : ∀ m f, f ∈ rrSpace (D m) → mnorm S f ≤ 1 → redVec S f ∈ piRR 𝓀 (Kappa S) (Db m))
    {ι : Type*} [Fintype ι] (Sp : ι → Finset (Branch 𝓀 (Kappa S)))
    (hdisj : ∀ p q, p ≠ q → Disjoint (Sp p) (Sp q)) (hzero : ∀ m p, ∀ b ∈ Sp p, Db m b.1 b.2 = 0)
    (Oc : ι → Submodule 𝓀 (Π W : S, Kappa S W))
    (hO : ∀ m f, f ∈ rrSpace (D m) → mnorm S f ≤ 1 → ∀ p, redVec S f ∈ Oc p)
    (M : ℕ) (A : ι → Finset (Π W : S, Kappa S W))
    (hA : ∀ p, ∀ y ∈ A p, y ∈ regAt 𝓀 (Kappa S) (Sp p))
    (hind : ∀ p, ∀ a : A p → 𝓀, ∑ i, a i • (i : Π W : S, Kappa S W) ∈
      Oc p ⊔ jetKer 𝓀 (Kappa S) M (Sp p) → a = 0) :
    (∑ W : S, (genus 𝓀 (Kappa S W) : ℤ)) + ∑ p, ((A p).card : ℤ) ≤ genus C F + S.card - 1 := by
  have := sum_genus_add_le hp hp1 x hx S hS D Db hdeg hlarge hred Sp hdisj hzero Oc hO M
    (T := fun p ↦ A p) (fun p i ↦ i.1) (fun p i ↦ hA p i.1 i.2) hind
  simpa only [Fintype.card_coe] using this

include hp hp1 in
/-- **The `b₁` form** (S7.6): if the condition spaces consist of elements with equal residues at
the `r_p ≥ 1` branches of `p`, then `Σ_W g(κ(W)) + Σ_p (r_p - 1) ≤ g(F) + #S - 1`. -/
theorem sum_genus_add_sum_card_sub_one_le
    {I : Type*} [Finite I] [Nonempty I] (x : I → F)
    (hx : ∀ i, Transcendental C (x i)) (S : Finset (TypeTwo C F))
    (hS : ∀ W, W ∈ S ↔ ∃ i, IsOver (hx i) W)
    (D : ℕ → CurveDivisor C F) (Db : ℕ → ∀ W : S, CurveDivisor 𝓀 (Kappa S W))
    (hdeg : ∀ m, ∑ W, (Db m W).degree = (D m).degree)
    (hlarge : ∀ (m : ℕ) W, (m : ℤ) ≤ (Db m W).degree)
    (hred : ∀ m f, f ∈ rrSpace (D m) → mnorm S f ≤ 1 → redVec S f ∈ piRR 𝓀 (Kappa S) (Db m))
    {ι : Type*} [Fintype ι] (Sp : ι → Finset (Branch 𝓀 (Kappa S)))
    (hdisj : ∀ p q, p ≠ q → Disjoint (Sp p) (Sp q)) (hzero : ∀ m p, ∀ b ∈ Sp p, Db m b.1 b.2 = 0)
    (Oc : ι → Submodule 𝓀 (Π W : S, Kappa S W))
    (hO : ∀ m f, f ∈ rrSpace (D m) → mnorm S f ≤ 1 → ∀ p, redVec S f ∈ Oc p)
    (hOeq : ∀ p, Oc p ≤ eqRes 𝓀 (Kappa S) (Sp p)) (hne : ∀ p, (Sp p).Nonempty) :
    (∑ W : S, (genus 𝓀 (Kappa S W) : ℤ)) + ∑ p, (((Sp p).card : ℤ) - 1) ≤
      genus C F + S.card - 1 := by
  classical
  choose b hb using hne
  choose A hAcard hA hAind using fun p ↦ exists_finset_indep_of_le_eqRes (Sp p) (hb p)
  have h := sum_genus_add_card_le hp hp1 x hx S hS D Db hdeg hlarge hred Sp hdisj hzero Oc hO 1 A
    hA fun p ↦ hAind p _ (sup_le (hOeq p) (jetKer_le_eqRes le_rfl (Sp p)))
  have hc (p : ι) : ((A p).card : ℤ) = (Sp p).card - 1 := by
    rw [hAcard p, Nat.cast_sub (Finset.card_pos.2 ⟨b p, hb p⟩)]
    simp
  simpa only [hc] using h

include hp hp1 in
/-- **`δ' = 0` at every point** (S7.6 with S8): if moreover
`g(F) + #S - 1 ≤ Σ_W g(κ(W)) + Σ_p (r_p - 1)`, then at every point `p₀` and jet order `M ≥ 1`,
a set of elements regular at the branches of `p₀` and independent modulo `Oc p₀ + K_{M, p₀}` has at
most `r_{p₀} - 1` elements. -/
theorem card_le_of_indep
    {I : Type*} [Finite I] [Nonempty I] (x : I → F)
    (hx : ∀ i, Transcendental C (x i)) (S : Finset (TypeTwo C F))
    (hS : ∀ W, W ∈ S ↔ ∃ i, IsOver (hx i) W)
    (D : ℕ → CurveDivisor C F) (Db : ℕ → ∀ W : S, CurveDivisor 𝓀 (Kappa S W))
    (hdeg : ∀ m, ∑ W, (Db m W).degree = (D m).degree)
    (hlarge : ∀ (m : ℕ) W, (m : ℤ) ≤ (Db m W).degree)
    (hred : ∀ m f, f ∈ rrSpace (D m) → mnorm S f ≤ 1 → redVec S f ∈ piRR 𝓀 (Kappa S) (Db m))
    {ι : Type*} [Fintype ι] (Sp : ι → Finset (Branch 𝓀 (Kappa S)))
    (hdisj : ∀ p q, p ≠ q → Disjoint (Sp p) (Sp q)) (hzero : ∀ m p, ∀ b ∈ Sp p, Db m b.1 b.2 = 0)
    (Oc : ι → Submodule 𝓀 (Π W : S, Kappa S W))
    (hO : ∀ m f, f ∈ rrSpace (D m) → mnorm S f ≤ 1 → ∀ p, redVec S f ∈ Oc p)
    (hOeq : ∀ p, Oc p ≤ eqRes 𝓀 (Kappa S) (Sp p)) (hne : ∀ p, (Sp p).Nonempty)
    (hS8 : genus C F + S.card - 1 ≤
      (∑ W : S, (genus 𝓀 (Kappa S W) : ℤ)) + ∑ p, (((Sp p).card : ℤ) - 1))
    (p₀ : ι) {M : ℕ} (hM : 1 ≤ M) (A₀ : Finset (Π W : S, Kappa S W))
    (hA₀ : ∀ y ∈ A₀, y ∈ regAt 𝓀 (Kappa S) (Sp p₀))
    (hind : ∀ a : A₀ → 𝓀, ∑ i, a i • (i : Π W : S, Kappa S W) ∈
      Oc p₀ ⊔ jetKer 𝓀 (Kappa S) M (Sp p₀) → a = 0) :
    (A₀.card : ℤ) ≤ (Sp p₀).card - 1 := by
  classical
  choose b hb using hne
  choose B hBcard hB hBind using fun p ↦ exists_finset_indep_of_le_eqRes (Sp p) (hb p)
  set A : ι → Finset (Π W : S, Kappa S W) := fun p ↦ if p = p₀ then A₀ else B p
  have h := sum_genus_add_card_le hp hp1 x hx S hS D Db hdeg hlarge hred Sp hdisj hzero Oc hO M A
    (fun p y hy ↦ by
      by_cases hp : p = p₀
      · subst hp
        simp only [A, if_pos rfl] at hy
        exact hA₀ y hy
      · simp only [A, if_neg hp] at hy
        exact hB p y hy)
    (fun p ↦ by
      by_cases hp : p = p₀
      · subst hp
        rw [show A p = A₀ from if_pos rfl]
        exact hind
      · rw [show A p = B p from if_neg hp]
        exact hBind p _ (sup_le (hOeq p) (jetKer_le_eqRes hM (Sp p))))
  have hc (p : ι) (hp : p ≠ p₀) : ((A p).card : ℤ) = (Sp p).card - 1 := by
    simp only [A, if_neg hp]
    rw [hBcard p, Nat.cast_sub (Finset.card_pos.2 ⟨b p, hb p⟩)]
    simp
  have h1 := h.trans hS8
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ p₀),
    Finset.sum_congr rfl fun p hp ↦ hc p (Finset.ne_of_mem_erase hp)] at h1
  simp only [A, if_pos rfl] at h1
  linarith

end Corollaries

end SemistableReduction
