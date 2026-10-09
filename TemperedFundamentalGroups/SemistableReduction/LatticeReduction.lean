/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussFibre

/-!
# Orthonormal bases of finite-dimensional subspaces

Blueprint §9.5, G6.4. Let `C` be a non-archimedean field.

* `exists_orthonormal_pi`: every subspace `U` of `C^J` (sup norm) has a basis `u` with
  `‖Σ cₗ uₗ‖ = maxₗ ‖cₗ‖` (reduced row echelon form with a maximal-entry pivot; no completeness
  or spherical completeness of `C` is needed);
* `exists_orthonormal_of_linearMap`: the same for a subspace `V` of a normed space admitting a
  linear map `T` to `C^J` with `‖T f‖ = λ ‖f‖`, `λ ∈ ‖C^×‖`;
* `GaussFibre.exists_orthonormal_submodule`: for `F / C(X)` finite with an orthonormal
  `C(X)`-basis for `gnorm` (G6.3), every finite-dimensional `C`-subspace `V ⊆ F` has an
  orthonormal `C`-basis for `gnorm` (clear denominators: `q V ⊆ ⊕ᵢ C[X]_{≤ M} bᵢ`).
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace LatticeReduction

variable {C : Type*} [NontriviallyNormedField C]

section Pi

variable {J : Type*} [Fintype J]

/-- The sup norm on `C^J`. -/
noncomputable def supNorm (v : J → C) : ℝ≥0 := Finset.univ.sup fun j ↦ ‖v j‖₊

lemma le_supNorm (v : J → C) (j : J) : ‖v j‖₊ ≤ supNorm v :=
  Finset.le_sup (f := fun j ↦ ‖v j‖₊) (Finset.mem_univ j)

lemma supNorm_le_iff {v : J → C} {r : ℝ≥0} : supNorm v ≤ r ↔ ∀ j, ‖v j‖₊ ≤ r := by
  simp [supNorm, Finset.sup_le_iff]

lemma supNorm_add_le [IsUltrametricDist C] (v w : J → C) :
    supNorm (v + w) ≤ max (supNorm v) (supNorm w) :=
  supNorm_le_iff.2 fun j ↦ (IsUltrametricDist.nnnorm_add_le_max _ _).trans
    (max_le_max (le_supNorm v j) (le_supNorm w j))

lemma supNorm_smul (c : C) (v : J → C) : supNorm (c • v) = ‖c‖₊ * supNorm v := by
  simp only [supNorm, Pi.smul_apply, smul_eq_mul, nnnorm_mul]
  exact (Finset.mul_sup₀ _ _ _).symm

lemma supNorm_neg (v : J → C) : supNorm (-v) = supNorm v := by
  simp [supNorm]

lemma supNorm_sub_le [IsUltrametricDist C] (v w : J → C) :
    supNorm (v - w) ≤ max (supNorm v) (supNorm w) := by
  rw [sub_eq_add_neg, ← supNorm_neg w]
  exact supNorm_add_le v (-w)

lemma supNorm_eq_zero {v : J → C} : supNorm v = 0 ↔ v = 0 := by
  refine ⟨fun h ↦ funext fun j ↦ ?_, fun h ↦ by simp [h, supNorm]⟩
  have := le_supNorm v j
  rw [h, nonpos_iff_eq_zero, nnnorm_eq_zero] at this
  exact this

lemma sup_fin_succ {n : ℕ} (c : Fin (n + 1) → ℝ≥0) :
    (Finset.univ.sup c) = max (c 0) (Finset.univ.sup fun l : Fin n ↦ c l.succ) := by
  refine le_antisymm (Finset.sup_le fun l _ ↦ ?_) (max_le ?_ (Finset.sup_le fun l _ ↦ ?_))
  · refine Fin.cases ?_ (fun l ↦ ?_) l
    · exact le_max_left _ _
    · exact le_max_of_le_right (Finset.le_sup (f := fun l : Fin n ↦ c l.succ)
        (Finset.mem_univ l))
  · exact Finset.le_sup (f := c) (Finset.mem_univ 0)
  · exact Finset.le_sup (f := c) (Finset.mem_univ l.succ)

/-- **Orthonormal bases of subspaces of `C^J`** (reduced row echelon form). -/
theorem exists_orthonormal_pi [IsUltrametricDist C] : ∀ (n : ℕ) (U : Submodule C (J → C)),
    Module.finrank C U = n → ∃ u : Fin n → J → C, (∀ l, u l ∈ U) ∧
      ∀ c : Fin n → C, supNorm (∑ l, c l • u l) = Finset.univ.sup fun l ↦ ‖c l‖₊ := by
  intro n
  induction n with
  | zero =>
    intro U _
    exact ⟨Fin.elim0, fun l ↦ l.elim0, fun c ↦ by simp [supNorm]⟩
  | succ n ih =>
    intro U hU
    classical
    have hne : U ≠ ⊥ := by
      rintro rfl
      simp at hU
    obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hJ : (Finset.univ : Finset J).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
      exact hv0 (funext fun j ↦ (h.false j).elim)
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j ↦ ‖v j‖₊) hJ
    have hvj : v j ≠ 0 := by
      intro h
      refine hv0 (supNorm_eq_zero.1 (le_antisymm ?_ zero_le))
      exact supNorm_le_iff.2 fun i ↦ (hj i (Finset.mem_univ i)).trans (by simp [h])
    set u₀ := (v j)⁻¹ • v
    have hu₀U : u₀ ∈ U := U.smul_mem _ hvU
    have hu₀j : u₀ j = 1 := by simp [u₀, hvj]
    have hu₀ : supNorm u₀ = 1 := by
      refine le_antisymm (supNorm_le_iff.2 fun i ↦ ?_) (by simpa [hu₀j] using le_supNorm u₀ j)
      simp only [u₀, Pi.smul_apply, smul_eq_mul, nnnorm_mul, nnnorm_inv]
      rw [inv_mul_le_iff₀ (nnnorm_pos.2 hvj), mul_one]
      exact hj i (Finset.mem_univ i)
    set U' := U ⊓ LinearMap.ker (LinearMap.proj (R := C) (φ := fun _ : J ↦ C) j)
    set S := Submodule.span C {u₀}
    have hsup : U' ⊔ S = U := by
      refine le_antisymm (sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).2 hu₀U))
        fun x hx ↦ ?_
      have hx' : x - x j • u₀ ∈ U' := ⟨U.sub_mem hx (U.smul_mem _ hu₀U), by simp [hu₀j]⟩
      have : x = (x - x j • u₀) + x j • u₀ := by abel
      rw [this]
      exact Submodule.add_mem_sup hx' (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    have hinf : U' ⊓ S = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨-, hxker⟩, hxS⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxS
      have : c = 0 := by simpa [hu₀j] using hxker
      simp [this]
    have hrank : Module.finrank C U' = n := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq U' S
      rw [hsup, hinf, finrank_bot, add_zero, hU,
        finrank_span_singleton (fun h ↦ by simp [h] at hu₀j)] at h
      omega
    obtain ⟨u', hu'U, hu'⟩ := ih U' hrank
    refine ⟨Fin.cons u₀ u', fun l ↦ Fin.cases hu₀U (fun l ↦ (hu'U l).1) l, fun c ↦ ?_⟩
    rw [Fin.sum_univ_succ, sup_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    set v' := ∑ l : Fin n, c l.succ • u' l
    have hv'U : v' ∈ U' := Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (hu'U l)
    have hv'j : v' j = 0 := by simpa using hv'U.2
    have hv' : supNorm v' = Finset.univ.sup fun l : Fin n ↦ ‖c l.succ‖₊ := hu' _
    rw [← hv']
    have hc0 : supNorm (c 0 • u₀) = ‖c 0‖₊ := by rw [supNorm_smul, hu₀, mul_one]
    refine le_antisymm ((supNorm_add_le _ _).trans (by rw [hc0])) ?_
    have h1 : ‖c 0‖₊ ≤ supNorm (c 0 • u₀ + v') := by
      simpa [hu₀j, hv'j] using le_supNorm (c 0 • u₀ + v') j
    have h2 : supNorm v' ≤ max (supNorm (c 0 • u₀ + v')) ‖c 0‖₊ := by
      have := supNorm_sub_le (c 0 • u₀ + v') (c 0 • u₀)
      rwa [add_sub_cancel_left, hc0] at this
    exact max_le h1 (h2.trans (max_le le_rfl h1))

end Pi

section Field

open GaussFibre

variable [IsUltrametricDist C] {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [Fintype (Ext C F)]

lemma gnorm_smul_C (γ : C) (f : F) : gnorm C (γ • f) = ‖γ‖₊ * gnorm C f := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply C (RatFunc C) F, gnorm_algebraMap_mul,
    gauss1_algebraMap_C]

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma eq_zero_of_gnorm_eq_zero [Nonempty (Ext C F)] {f : F} (h : gnorm C f = 0) : f = 0 := by
  obtain ⟨w⟩ := ‹Nonempty (Ext C F)›
  have := le_gnorm w f
  rw [h, nonpos_iff_eq_zero, Valuation.zero_iff] at this
  exact this

variable (C) in
/-- A family `g` in `F` is orthonormal for `gnorm` if `‖Σ cₗ gₗ‖ = max ‖cₗ‖` for `cₗ ∈ C`. -/
def IsOrthonormal {n : ℕ} (g : Fin n → F) : Prop :=
  ∀ c : Fin n → C, gnorm C (∑ l, c l • g l) = Finset.univ.sup fun l ↦ ‖c l‖₊

/-- Transfer of orthonormal bases along a linear map with `‖T f‖ = ‖γ‖ ‖f‖`. -/
theorem exists_orthonormal_of_linearMap [Nonempty (Ext C F)] (V : Submodule C F)
    [FiniteDimensional C V] {J : Type*} [Fintype J] (T : V →ₗ[C] (J → C)) {γ : C} (hγ : γ ≠ 0)
    (hT : ∀ f : V, supNorm (T f) = ‖γ‖₊ * gnorm C (f : F)) :
    ∃ g : Fin (Module.finrank C V) → F, (∀ l, g l ∈ V) ∧ IsOrthonormal C g := by
  classical
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    have h := hT f
    rw [LinearMap.mem_ker.1 hf, show supNorm (0 : J → C) = 0 from supNorm_eq_zero.2 rfl,
      eq_comm, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd (nnnorm_eq_zero.1 h) hγ
    · exact (Submodule.mem_bot C).2 (Subtype.ext (eq_zero_of_gnorm_eq_zero h))
  obtain ⟨u, huU, hu⟩ := exists_orthonormal_pi (Module.finrank C V) (LinearMap.range T)
    (LinearMap.finrank_range_of_inj hinj)
  choose a ha using fun l ↦ LinearMap.mem_range.1 (huU l)
  refine ⟨fun l ↦ γ • (a l : F), fun l ↦ V.smul_mem γ (a l).2, fun c ↦ ?_⟩
  have h1 : ∑ l, c l • γ • (a l : F) = γ • ((∑ l, c l • a l : V) : F) := by
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ smul_comm _ _ _
  rw [h1, gnorm_smul_C, ← hT, map_sum]
  simp only [map_smul, ha]
  exact hu c

/-- The Gauss norm of a polynomial of degree `≤ M` is the max of its first `M + 1` coefficients. -/
lemma sup_eq_sup_coeff {Q : C[X]} {M : ℕ} (hQ : Q.natDegree ≤ M) :
    Gauss.sup (NormedField.valuation (K := C)) 1 Q =
      Finset.univ.sup fun m : Fin (M + 1) ↦ ‖Q.coeff m‖₊ := by
  refine le_antisymm (Gauss.sup_le_iff.2 fun i ↦ ?_) (Finset.sup_le fun m _ ↦ ?_)
  · simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply]
    by_cases hi : i ≤ M
    · exact Finset.le_sup (f := fun m : Fin (M + 1) ↦ ‖Q.coeff m‖₊)
        (Finset.mem_univ ⟨i, Nat.lt_succ_of_le hi⟩)
    · rw [coeff_eq_zero_of_natDegree_lt (hQ.trans_lt (not_le.1 hi)), nnnorm_zero]
      exact zero_le
  · have := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) Q m
    simpa [Gauss.term] using this

/-- **G6.4** (isometric coordinates). If `F` has an orthonormal `C(X)`-basis for `gnorm` (G6.3),
every finite-dimensional `C`-subspace `V ⊆ F` embeds linearly into some `C^J` with
`‖T f‖ = ‖γ‖ gnorm f` (clearing denominators: `V ⊆ ⊕ᵢ C[X]_{≤ M} bᵢ / D`). -/
theorem exists_isometry {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (RatFunc C) F)
    (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
    (V : Submodule C F) [FiniteDimensional C V] :
    ∃ (M : ℕ) (T : V →ₗ[C] (ι × Fin (M + 1) → C)) (γ : C), γ ≠ 0 ∧
      ∀ f : V, supNorm (T f) = ‖γ‖₊ * gnorm C (f : F) := by
  classical
  set r := Module.finrank C V
  set v := Module.finBasis C V
  set ψ : ι × Fin r → RatFunc C := fun p ↦ b.repr (v p.2 : F) p.1
  set D : C[X] := ∏ p, (ψ p).denom
  set cof : ι × Fin r → C[X] := fun p ↦ ∏ p' ∈ Finset.univ.erase p, (ψ p').denom
  have hD (p : ι × Fin r) : D = (ψ p).denom * cof p :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ p)).symm
  set P : ι × Fin r → C[X] := fun p ↦ (ψ p).num * cof p
  have hP (p : ι × Fin r) : algebraMap C[X] (RatFunc C) (P p) =
      algebraMap C[X] (RatFunc C) D * ψ p := by
    have hden : algebraMap C[X] (RatFunc C) (ψ p).denom ≠ 0 := by
      simpa using (ψ p).denom_ne_zero
    have h := RatFunc.num_div_denom (ψ p)
    rw [div_eq_iff hden] at h
    simp only [P, hD p, map_mul, h]
    ring
  set M := Finset.univ.sup fun p ↦ (P p).natDegree
  have hM (p : ι × Fin r) : (P p).natDegree ≤ M :=
    Finset.le_sup (f := fun p ↦ (P p).natDegree) (Finset.mem_univ p)
  -- the linear map to `C^(ι × Fin (M + 1))`
  let T : V →ₗ[C] (ι × Fin (M + 1) → C) :=
    LinearMap.pi fun q ↦ ∑ k : Fin r, (P (q.1, k)).coeff q.2 • v.coord k
  have hT (f : V) (q : ι × Fin (M + 1)) :
      T f q = (∑ k : Fin r, v.repr f k • P (q.1, k)).coeff q.2 := by
    simp only [T, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, finsetSum_coeff, coeff_smul]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hDne : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ ↦ (ψ p).denom_ne_zero
  obtain ⟨γ, hγ⟩ := exists_sup_eq D
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero, Gauss.sup_eq_zero_iff] at hγ
    exact hDne hγ
  refine ⟨M, T, γ, hγ0, fun f ↦ ?_⟩
  -- coordinates of `f`
  set Q : ι → C[X] := fun i ↦ ∑ k : Fin r, v.repr f k • P (i, k)
  have hQ (i : ι) : algebraMap C[X] (RatFunc C) (Q i) =
      algebraMap C[X] (RatFunc C) D * b.repr (f : F) i := by
    have hf : (f : F) = ∑ k : Fin r, v.repr f k • (v k : F) := by
      conv_lhs => rw [← v.sum_repr f]
      rw [Submodule.coe_sum]
      rfl
    have hrepr : b.repr (f : F) i = ∑ k : Fin r, v.repr f k • ψ (i, k) := by
      rw [hf, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← algebraMap_smul (RatFunc C) (v.repr f k) (v k : F), LinearEquiv.map_smul,
        Finsupp.smul_apply, algebraMap_smul]
    rw [hrepr, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Polynomial.smul_eq_C_mul, map_mul, hP, Algebra.smul_def, RatFunc.algebraMap_C,
      ← RatFunc.algebraMap_eq_C]
    ring
  have hQdeg (i : ι) : (Q i).natDegree ≤ M := by
    refine (natDegree_sum_le _ _).trans (Finset.sup_le fun k _ ↦ ?_)
    exact (natDegree_smul_le _ _).trans (hM _)
  have hgn : gnorm C (f : F) = Finset.univ.sup fun i ↦ gauss1 C (b.repr (f : F) i) := by
    conv_lhs => rw [← b.sum_repr (f : F)]
    exact hb _
  have hQn (i : ι) : gauss1 C (algebraMap C[X] (RatFunc C) D) * gauss1 C (b.repr (f : F) i) =
      Finset.univ.sup fun m : Fin (M + 1) ↦ ‖(Q i).coeff m‖₊ := by
    rw [← map_mul, ← hQ, gauss1_algebraMap, sup_eq_sup_coeff (hQdeg i)]
  rw [hgn, ← hγ, ← gauss1_algebraMap, Finset.mul_sup₀]
  simp only [hQn]
  rw [supNorm, ← Finset.univ_product_univ, Finset.sup_product_left]
  simp [hT, Q]

/-- **G6.4** (orthonormal bases of finite-dimensional subspaces). If `F` has an orthonormal
`C(X)`-basis for `gnorm` (G6.3), every finite-dimensional `C`-subspace `V ⊆ F` has an
orthonormal `C`-basis (`exists_isometry`, `exists_orthonormal_of_linearMap`). -/
theorem exists_orthonormal_submodule [Nonempty (Ext C F)] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (RatFunc C) F)
    (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
    (V : Submodule C F) [FiniteDimensional C V] :
    ∃ g : Fin (Module.finrank C V) → F, (∀ l, g l ∈ V) ∧ IsOrthonormal C g := by
  obtain ⟨M, T, γ, hγ, hT⟩ := exists_isometry b hb V
  exact exists_orthonormal_of_linearMap V T hγ hT

end Field

end LatticeReduction

end SemistableReduction
