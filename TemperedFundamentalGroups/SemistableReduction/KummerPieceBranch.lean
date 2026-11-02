/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.AdmissibleCovering
import TemperedFundamentalGroups.SemistableReduction.CuspPieceHom

/-!
# The branches of a Kummer factor at a node (MR12, generic core)

Let `A = k[u, v]/(uv)` (`KummerEtale.A 0 e`), `B = k[s, t]/(st)` (`KummerEtale.B 0`) with
`u ↦ s^e`, `v ↦ t^e`, and let `P` be an `A`-algebra; write `ū, v̄` for the images of `u, v`
in `P`. We verify the hypotheses of the node normal form (`NodeNormalForm`) for the Kummer
factor `P ⊗_A B` with `s := 1 ⊗ s`, `t := 1 ⊗ t`:

* **`kummerTensor_nfHyp_s`**: if `ū` satisfies `CuspHom.NFHyp` on `P/(v̄)`, then `s` satisfies
  it on `(P ⊗_A B)/(t)`; symmetrically **`kummerTensor_nfHyp_t`**;
* **`kummerTensor_hinter`**: if `(ū) ∩ (v̄) = 0` in `P`, then `(s) ∩ (t) = 0` in `P ⊗_A B`.

The proof: `B` is spanned over `A` by `s^i, t^j` (`i, j < e`) (`node_span`), so every element of
`P ⊗_A B` is `∑ c_i ⊗ s^i + ∑ d_j ⊗ t^j`. The map `P ⊗_A B → (P/(v̄))[X]/(X^e − ū)`,
`s ↦ X`, `t ↦ 0` (`branchMap`) is surjective with kernel `(t)` (`ker_branchMap`), by comparing
coefficients in the power basis `1, X, …, X^{e−1}`; so `(P ⊗_A B)/(t) ≅ (P/(v̄))[X]/(X^e − ū)`
with `s ↦ X`, and the hypotheses follow from `CuspNormalForm.isSMulRegular_root`,
`isReduced_quot_root`, `separated_root`. For the intersection, an element of `(s) ∩ (t)` is killed
by both branch maps, which forces `c_0 + d_0 ∈ (ū) ∩ (v̄)`, `c_i ∈ (v̄)` and `d_j ∈ (ū)` for
`i, j ≠ 0`, and `v̄ ⊗ s^i = 1 ⊗ t^e s^i = 0`.

**`Admissible.kummerPiece_hinter`**, **`kummerPiece_nfHyp_s`**, **`kummerPiece_nfHyp_t`** are the
statements for `Admissible.KummerPiece φ ε he`.
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

namespace NodeNormalForm

open AdmissibleLift

/-! ### Transport along ring isomorphisms -/

section Transport

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- `CuspHom.NFHyp` transfers along a ring isomorphism. -/
theorem nfHyp_of_ringEquiv (Φ : R ≃+* R') {x : R} {x' : R'} (hx : Φ x = x')
    (h : CuspHom.NFHyp R' x') : CuspHom.NFHyp R x := by
  refine ⟨fun a b hab ↦ Φ.injective (h.1 ?_), ?_, fun a ha ↦ Φ.injective ?_⟩
  · change x' * Φ a = x' * Φ b
    have := congrArg Φ (show x * a = x * b from hab)
    rwa [map_mul, map_mul, hx] at this
  · have hJ : Ideal.span {x'} = (Ideal.span {x}).map Φ := by
      rw [Ideal.map_span, Set.image_singleton, hx]
    haveI := h.2.1
    exact isReduced_of_injective (Ideal.quotientEquiv _ _ Φ hJ)
      (Ideal.quotientEquiv _ _ Φ hJ).injective
  · rw [map_zero]
    exact h.2.2 _ fun m ↦ by rw [← hx, ← map_pow]; exact map_dvd Φ (ha m)

end Transport

/-! ### Coefficients in `R[X]/(X^e − r)` -/

section Coeff

variable {R : Type*} [CommRing R] (r : R) {e : ℕ}

/-- Comparing coefficients in the power basis `1, X, …, X^{e−1}` of `R[X]/(X^e − r)`. -/
theorem coeff_eq_zero_of_sum (he : 0 < e) {a : Fin e → R} {b : R}
    (h : ∑ i, AdjoinRoot.of (X ^ e - C r) (a i) * AdjoinRoot.root (X ^ e - C r) ^ (i : ℕ) +
      AdjoinRoot.of (X ^ e - C r) b = 0) :
    a ⟨0, he⟩ + b = 0 ∧ ∀ i : Fin e, (i : ℕ) ≠ 0 → a i = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
  set Q : R[X] := ∑ i : Fin e, C (a i) * X ^ (i : ℕ) + C b with hQ
  have hmk : AdjoinRoot.mk (X ^ e - C r) Q = 0 := by
    rw [hQ, map_add, map_sum, AdjoinRoot.mk_C]
    simpa only [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X] using h
  have hQ0 : Q = 0 := by
    by_contra hne
    refine (monic_X_pow_sub_C r he.ne').not_dvd_of_degree_lt hne ?_
      (AdjoinRoot.mk_eq_zero.mp hmk)
    rw [degree_X_pow_sub_C he]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (degree_sum_fin_lt _) ?_)
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast he)
  have hc : ∀ i : Fin e, Q.coeff i = a i + if (i : ℕ) = 0 then b else 0 := by
    intro i
    rw [hQ, coeff_add, finsetSum_coeff, coeff_C]
    congr 1
    rw [Fintype.sum_eq_single i]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro j hj
      rw [coeff_C_mul_X_pow, if_neg fun h ↦ hj (Fin.ext h.symm)]
  refine ⟨?_, fun i hi ↦ ?_⟩
  · have := hc ⟨0, he⟩
    rwa [hQ0, coeff_zero, if_pos rfl, eq_comm] at this
  · have := hc i
    rwa [hQ0, coeff_zero, if_neg hi, add_zero, eq_comm] at this

end Coeff

/-! ### The branch maps of `P ⊗_A B` -/

section BranchRing

variable {A : Type*} [CommRing A]

/-- The branch ring `(P/(ȳ))[X]/(X^e − x̄)`. -/
abbrev BranchRing (P : Type*) [CommRing P] [Algebra A P] (x y : A) (e : ℕ) : Type _ :=
  AdjoinRoot (X ^ e - C (Ideal.Quotient.mk (Ideal.span {algebraMap A P y}) (algebraMap A P x)))

/-- The map `P → (P/(ȳ))[X]/(X^e − x̄)`. -/
noncomputable def toBranch (P : Type*) [CommRing P] [Algebra A P] (x y : A) (e : ℕ) :
    P →ₐ[A] BranchRing P x y e :=
  (IsScalarTower.toAlgHom A (P ⧸ Ideal.span {algebraMap A P y}) (BranchRing P x y e)).comp
    (Ideal.Quotient.mkₐ A _)

lemma toBranch_apply (P : Type*) [CommRing P] [Algebra A P] (x y : A) (e : ℕ) (p : P) :
    toBranch P x y e p = AdjoinRoot.of _ (Ideal.Quotient.mk _ p) := rfl

lemma branch_root_pow (P : Type*) [CommRing P] [Algebra A P] (x y : A) (e : ℕ) :
    AdjoinRoot.root (X ^ e - C (Ideal.Quotient.mk (Ideal.span {algebraMap A P y})
      (algebraMap A P x))) ^ e = algebraMap A (BranchRing P x y e) x :=
  CuspNormalForm.root_pow _

lemma branch_zero_pow (P : Type*) [CommRing P] [Algebra A P] (x y : A) {e : ℕ} (he : 0 < e) :
    (0 : BranchRing P x y e) ^ e = algebraMap A (BranchRing P x y e) y := by
  rw [zero_pow he.ne']
  change (0 : BranchRing P x y e) = AdjoinRoot.of _ (Ideal.Quotient.mk _ (algebraMap A P y))
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]

end BranchRing

section Branch

variable {A B P : Type*} [CommRing A] [CommRing B] [CommRing P] [Algebra A B] [Algebra A P]
  {e : ℕ} {x y : A} {σ τ : B}

/-- Every element of `P ⊗_A B` is `∑ c_i ⊗ σ^i + ∑ d_j ⊗ τ^j` if `B` is spanned by these. -/
theorem exists_repr
    (hspan : ∀ b : B, ∃ a a' : Fin e → A,
      b = ∑ i, a i • σ ^ (i : ℕ) + ∑ j, a' j • τ ^ (j : ℕ)) (z : P ⊗[A] B) :
    ∃ c d : Fin e → P, z = ∑ i, c i ⊗ₜ[A] (σ ^ (i : ℕ)) + ∑ j, d j ⊗ₜ[A] (τ ^ (j : ℕ)) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul p b =>
    obtain ⟨a, a', rfl⟩ := hspan b
    refine ⟨fun i ↦ a i • p, fun j ↦ a' j • p, ?_⟩
    simp only [tmul_add, tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add z w hz hw =>
    obtain ⟨c, d, rfl⟩ := hz
    obtain ⟨c', d', rfl⟩ := hw
    refine ⟨c + c', d + d', ?_⟩
    simp only [Pi.add_apply, add_tmul, Finset.sum_add_distrib]
    abel

variable (g : B →ₐ[A] BranchRing P x y e)

/-- The branch map `P ⊗_A B → (P/(ȳ))[X]/(X^e − x̄)` induced by `g`. -/
noncomputable def branchMap : P ⊗[A] B →ₐ[A] BranchRing P x y e :=
  Algebra.TensorProduct.lift (toBranch P x y e) g fun _ _ ↦ Commute.all _ _

lemma branchMap_tmul (p : P) (b : B) : branchMap g (p ⊗ₜ b) = toBranch P x y e p * g b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

variable {g} (hgσ : g σ = AdjoinRoot.root _) (hgτ : g τ = 0)

include hgσ hgτ in
lemma branchMap_repr (he : 0 < e) (c d : Fin e → P) :
    branchMap g (∑ i, c i ⊗ₜ[A] (σ ^ (i : ℕ)) + ∑ j, d j ⊗ₜ[A] (τ ^ (j : ℕ))) =
      ∑ i, AdjoinRoot.of _ (Ideal.Quotient.mk _ (c i)) *
        AdjoinRoot.root (X ^ e - C (Ideal.Quotient.mk (Ideal.span {algebraMap A P y})
          (algebraMap A P x))) ^ (i : ℕ) +
        AdjoinRoot.of _ (Ideal.Quotient.mk _ (d ⟨0, he⟩)) := by
  rw [map_add, map_sum, map_sum]
  simp only [branchMap_tmul, map_pow, hgσ, hgτ, toBranch_apply]
  congr 1
  rw [Fintype.sum_eq_single ⟨0, he⟩]
  · simp
  · intro j hj
    rw [zero_pow (fun h ↦ hj (Fin.ext h)), mul_zero]

include hgσ hgτ in
/-- The coefficients of an element of the kernel of the branch map. -/
theorem coeffs_mem (he : 0 < e) (c d : Fin e → P)
    (hz : branchMap g (∑ i, c i ⊗ₜ[A] (σ ^ (i : ℕ)) + ∑ j, d j ⊗ₜ[A] (τ ^ (j : ℕ))) = 0) :
    c ⟨0, he⟩ + d ⟨0, he⟩ ∈ Ideal.span {algebraMap A P y} ∧
      ∀ i : Fin e, (i : ℕ) ≠ 0 → c i ∈ Ideal.span {algebraMap A P y} := by
  rw [branchMap_repr hgσ hgτ he] at hz
  obtain ⟨h0, hi⟩ := coeff_eq_zero_of_sum _ he hz
  refine ⟨?_, fun i hi' ↦ ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_add]; exact h0
  · rw [← Ideal.Quotient.eq_zero_iff_mem]; exact hi i hi'

lemma tmul_pow_mem (q : P) {j : ℕ} (hj : j ≠ 0) :
    q ⊗ₜ[A] (τ ^ j) ∈ Ideal.span {(1 : P) ⊗ₜ[A] τ} := by
  have : q ⊗ₜ[A] (τ ^ j) = (q ⊗ₜ[A] (τ ^ (j - 1))) * ((1 : P) ⊗ₜ[A] τ) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← pow_succ,
      Nat.sub_add_cancel (Nat.pos_of_ne_zero hj)]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

lemma mul_tmul_eq (hτe : algebraMap A B y = τ ^ e) (r : P) (b : B) :
    (r * algebraMap A P y) ⊗ₜ[A] b = r ⊗ₜ[A] (τ ^ e * b) := by
  rw [← hτe, ← Algebra.smul_def, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]

lemma mem_span_tmul (hτe : algebraMap A B y = τ ^ e) (he : 0 < e) {p : P}
    (hp : p ∈ Ideal.span {algebraMap A P y}) (b : B) :
    p ⊗ₜ[A] b ∈ Ideal.span {(1 : P) ⊗ₜ[A] τ} := by
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  have h2 : r ⊗ₜ[A] (τ ^ e * b) = (r ⊗ₜ[A] (τ ^ (e - 1) * b)) * ((1 : P) ⊗ₜ[A] τ) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_right_comm, ← pow_succ,
      Nat.sub_add_cancel he]
  rw [mul_tmul_eq hτe, h2]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

lemma tmul_eq_zero (hτe : algebraMap A B y = τ ^ e) (hστ : σ * τ = 0) (he : 0 < e) {p : P}
    (hp : p ∈ Ideal.span {algebraMap A P y}) {i : ℕ} (hi : i ≠ 0) :
    p ⊗ₜ[A] (σ ^ i) = 0 := by
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  have h0 : τ ^ (e' + 1) * σ ^ (i' + 1) = 0 :=
    calc τ ^ (e' + 1) * σ ^ (i' + 1) = τ ^ e' * σ ^ i' * (σ * τ) := by ring
      _ = 0 := by rw [hστ, mul_zero]
  rw [mul_tmul_eq hτe, h0, tmul_zero]

include hgσ hgτ in
/-- **The kernel of the branch map is `(1 ⊗ τ)`.** -/
theorem ker_branchMap (he : 0 < e)
    (hspan : ∀ b : B, ∃ a a' : Fin e → A,
      b = ∑ i, a i • σ ^ (i : ℕ) + ∑ j, a' j • τ ^ (j : ℕ))
    (hτe : algebraMap A B y = τ ^ e) :
    RingHom.ker (branchMap g) = Ideal.span {(1 : P) ⊗ₜ[A] τ} := by
  refine le_antisymm (fun z hz ↦ ?_) ?_
  · obtain ⟨c, d, rfl⟩ := exists_repr hspan z
    obtain ⟨h0, hi⟩ := coeffs_mem hgσ hgτ he c d (RingHom.mem_ker.mp hz)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_sum, map_sum,
      Fintype.sum_eq_single ⟨0, he⟩, Fintype.sum_eq_single ⟨0, he⟩]
    · rw [show σ ^ ((⟨0, he⟩ : Fin e) : ℕ) = 1 from pow_zero σ,
        show τ ^ ((⟨0, he⟩ : Fin e) : ℕ) = 1 from pow_zero τ, ← map_add, ← add_tmul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact mem_span_tmul hτe he h0 _
    · intro j hj
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact tmul_pow_mem _ fun h ↦ hj (Fin.ext h)
    · intro i hi'
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact mem_span_tmul hτe he (hi i fun h ↦ hi' (Fin.ext h)) _
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      branchMap_tmul, hgτ, mul_zero]

include hgσ in
/-- **The branch map is surjective.** -/
theorem branchMap_surjective : Function.Surjective (branchMap g) := by
  intro w
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective w
  refine Polynomial.induction_on q (fun a ↦ ?_) (fun q r hq hr ↦ ?_) (fun n a h ↦ ?_)
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨p ⊗ₜ 1, by rw [branchMap_tmul, map_one, mul_one, toBranch_apply, AdjoinRoot.mk_C]⟩
  · obtain ⟨z, hz⟩ := hq
    obtain ⟨z', hz'⟩ := hr
    exact ⟨z + z', by rw [map_add, hz, hz', map_add]⟩
  · obtain ⟨z, hz⟩ := h
    refine ⟨z * ((1 : P) ⊗ₜ[A] σ), ?_⟩
    rw [map_mul, hz, branchMap_tmul, map_one, one_mul, hgσ, pow_succ, ← mul_assoc,
      map_mul (AdjoinRoot.mk _) (C a * X ^ n) X, AdjoinRoot.mk_X]

include hgσ hgτ in
/-- **The branch `(P ⊗_A B)/(τ)` satisfies the cusp normal form hypotheses for `σ`** if
`P/(ȳ)` does for `x̄`. -/
theorem nfHyp_branch (he : 0 < e)
    (hspan : ∀ b : B, ∃ a a' : Fin e → A,
      b = ∑ i, a i • σ ^ (i : ℕ) + ∑ j, a' j • τ ^ (j : ℕ))
    (hτe : algebraMap A B y = τ ^ e)
    (hP : CuspHom.NFHyp (P ⧸ Ideal.span {algebraMap A P y})
      (Ideal.Quotient.mk _ (algebraMap A P x))) :
    CuspHom.NFHyp ((P ⊗[A] B) ⧸ Ideal.span {(1 : P) ⊗ₜ[A] τ})
      (Ideal.Quotient.mk _ ((1 : P) ⊗ₜ[A] σ)) := by
  refine nfHyp_of_ringEquiv
    ((Ideal.quotEquivOfEq (ker_branchMap hgσ hgτ he hspan hτe).symm).trans
      (RingHom.quotientKerEquivOfSurjective (branchMap_surjective hgσ))) ?_
    ⟨CuspNormalForm.isSMulRegular_root _ he hP.1,
      CuspNormalForm.isReduced_quot_root _ he hP.2.1,
      CuspNormalForm.separated_root _ he hP.2.2⟩
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact (branchMap_tmul g 1 σ).trans (by rw [map_one, one_mul, hgσ])

include hgσ hgτ in
/-- **The two branches meet in `0`** if `(x̄) ∩ (ȳ) = 0` in `P`. -/
theorem inter_eq_zero (he : 0 < e)
    (hspan : ∀ b : B, ∃ a a' : Fin e → A,
      b = ∑ i, a i • σ ^ (i : ℕ) + ∑ j, a' j • τ ^ (j : ℕ))
    (hσe : algebraMap A B x = σ ^ e) (hτe : algebraMap A B y = τ ^ e) (hστ : σ * τ = 0)
    {gs : B →ₐ[A] BranchRing P y x e} (hgsτ : gs τ = AdjoinRoot.root _) (hgsσ : gs σ = 0)
    (hP : ∀ p, p ∈ Ideal.span {algebraMap A P x} → p ∈ Ideal.span {algebraMap A P y} → p = 0)
    (z : P ⊗[A] B) (hzs : z ∈ Ideal.span {(1 : P) ⊗ₜ[A] σ})
    (hzt : z ∈ Ideal.span {(1 : P) ⊗ₜ[A] τ}) : z = 0 := by
  have h1 : branchMap g z = 0 := by
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hzt
    rw [map_mul, branchMap_tmul, map_one, one_mul, hgτ, mul_zero]
  have h2 : branchMap gs z = 0 := by
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hzs
    rw [map_mul, branchMap_tmul, map_one, one_mul, hgsσ, mul_zero]
  obtain ⟨c, d, rfl⟩ := exists_repr hspan z
  obtain ⟨ht0, hti⟩ := coeffs_mem hgσ hgτ he c d h1
  rw [add_comm] at h2
  obtain ⟨hs0, hsi⟩ := coeffs_mem hgsτ hgsσ he d c h2
  rw [Fintype.sum_eq_single ⟨0, he⟩, Fintype.sum_eq_single ⟨0, he⟩]
  · rw [show σ ^ ((⟨0, he⟩ : Fin e) : ℕ) = 1 from pow_zero σ,
      show τ ^ ((⟨0, he⟩ : Fin e) : ℕ) = 1 from pow_zero τ, ← add_tmul,
      hP _ (by rwa [add_comm]) ht0, zero_tmul]
  · intro j hj
    exact tmul_eq_zero hσe (by rw [mul_comm, hστ]) he (hsi j fun h ↦ hj (Fin.ext h))
      fun h ↦ hj (Fin.ext h)
  · intro i hi
    exact tmul_eq_zero hτe hστ he (hti i fun h ↦ hi (Fin.ext h)) fun h ↦ hi (Fin.ext h)

end Branch

/-! ### The Kummer factor `P ⊗_{k[u,v]/(uv)} k[s,t]/(st)` -/

section Node

variable {k : Type u} [Field k] {e : ℕ}

lemma pow_eq_smul {w : KummerEtale.B (0 : k)} {z : KummerEtale.A (0 : k) e}
    (hz : algebraMap _ _ z = w ^ e) (n : ℕ) : w ^ n = z ^ (n / e) • w ^ (n % e) := by
  rw [Algebra.smul_def, map_pow, hz, ← pow_mul, ← pow_add, Nat.div_add_mod]

/-- `k[s, t]/(st)` is spanned over `k[u, v]/(uv)` (`u = s^e`, `v = t^e`) by the `s^i`, `t^j`,
`i, j < e`. -/
theorem node_span (he : 0 < e) (b : KummerEtale.B (0 : k)) :
    ∃ a a' : Fin e → KummerEtale.A (0 : k) e,
      b = ∑ i, a i • Node.u (0 : k) ^ (i : ℕ) + ∑ j, a' j • Node.v (0 : k) ^ (j : ℕ) := by
  have hb : b ∈ Submodule.span k (Set.range (Node.monomial (0 : k))) := by
    rw [Node.span_eq_top]; exact Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, rfl⟩ := hw
    rcases m with n | n
    · refine ⟨Pi.single ⟨n % e, Nat.mod_lt _ he⟩ (Node.u _ ^ (n / e)), 0, ?_⟩
      simp only [Node.monomial, Sum.elim_inl, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
        add_zero, Pi.single_apply, ite_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact pow_eq_smul (KummerEtale.algebraMap_u _ _) n
    · refine ⟨0, Pi.single ⟨(n + 1) % e, Nat.mod_lt _ he⟩ (Node.v _ ^ ((n + 1) / e)), ?_⟩
      simp only [Node.monomial, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
        zero_add, Pi.single_apply, ite_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact pow_eq_smul (KummerEtale.algebraMap_v _ _) (n + 1)
  | zero => exact ⟨0, 0, by simp⟩
  | add w w' _ _ hw hw' =>
    obtain ⟨a, a', rfl⟩ := hw
    obtain ⟨c, c', rfl⟩ := hw'
    refine ⟨a + c, a' + c', ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  | smul r w _ hw =>
    obtain ⟨a, a', rfl⟩ := hw
    refine ⟨r • a, r • a', ?_⟩
    simp only [smul_add, Finset.smul_sum, Pi.smul_apply, smul_assoc]

/-- An algebra map out of `k[s, t]/(st)` over `k[u, v]/(uv)`, given the images of `s, t`. -/
noncomputable def nodeLift {S : Type*} [CommRing S] [Algebra (KummerEtale.A (0 : k) e) S]
    (α β : S) (hαβ : α * β = 0)
    (hα : α ^ e = algebraMap (KummerEtale.A (0 : k) e) S (Node.u _))
    (hβ : β ^ e = algebraMap (KummerEtale.A (0 : k) e) S (Node.v _)) :
    KummerEtale.B (0 : k) →ₐ[KummerEtale.A (0 : k) e] S :=
  letI : Algebra k S :=
    ((algebraMap (KummerEtale.A (0 : k) e) S).comp (algebraMap k _)).toAlgebra
  { (Node.lift (O := k) α β (by rw [hαβ, map_zero])).toRingHom with
    commutes' := fun a ↦ by
      haveI : IsScalarTower k (KummerEtale.A (0 : k) e) S :=
        IsScalarTower.of_algebraMap_eq' rfl
      have h : (Node.lift (O := k) α β (by rw [hαβ, map_zero])).comp
          (Node.kummer (0 : k) e) = IsScalarTower.toAlgHom k (KummerEtale.A (0 : k) e) S :=
        Node.algHom_ext (by simp [hα]) (by simp [hβ])
      exact DFunLike.congr_fun h a }

section Lift

variable {S : Type*} [CommRing S] [Algebra (KummerEtale.A (0 : k) e) S] (α β : S)
  (hαβ : α * β = 0) (hα : α ^ e = algebraMap (KummerEtale.A (0 : k) e) S (Node.u _))
  (hβ : β ^ e = algebraMap (KummerEtale.A (0 : k) e) S (Node.v _))

lemma nodeLift_u : nodeLift α β hαβ hα hβ (Node.u (0 : k)) = α := by
  letI : Algebra k S :=
    ((algebraMap (KummerEtale.A (0 : k) e) S).comp (algebraMap k _)).toAlgebra
  exact Node.lift_u (O := k) α β (by rw [hαβ, map_zero])

lemma nodeLift_v : nodeLift α β hαβ hα hβ (Node.v (0 : k)) = β := by
  letI : Algebra k S :=
    ((algebraMap (KummerEtale.A (0 : k) e) S).comp (algebraMap k _)).toAlgebra
  exact Node.lift_v (O := k) α β (by rw [hαβ, map_zero])

end Lift

variable {P : Type*} [CommRing P] [Algebra (KummerEtale.A (0 : k) e) P]

lemma u_mul_v_zero : Node.u (0 : k) * Node.v (0 : k) = 0 := by
  rw [Node.u_mul_v, map_zero]

variable (P) in
/-- The `s`-branch map `B → (P/(v̄))[X]/(X^e − ū)`, `s ↦ X`, `t ↦ 0`. -/
noncomputable def gS (he : 0 < e) : KummerEtale.B (0 : k) →ₐ[KummerEtale.A (0 : k) e]
    BranchRing P (Node.u ((0 : k) ^ e)) (Node.v ((0 : k) ^ e)) e :=
  nodeLift (AdjoinRoot.root _) 0 (mul_zero _) (branch_root_pow P _ _ e) (branch_zero_pow P _ _ he)

variable (P) in
/-- The `t`-branch map `B → (P/(ū))[X]/(X^e − v̄)`, `t ↦ X`, `s ↦ 0`. -/
noncomputable def gT (he : 0 < e) : KummerEtale.B (0 : k) →ₐ[KummerEtale.A (0 : k) e]
    BranchRing P (Node.v ((0 : k) ^ e)) (Node.u ((0 : k) ^ e)) e :=
  nodeLift 0 (AdjoinRoot.root _) (zero_mul _) (branch_zero_pow P _ _ he) (branch_root_pow P _ _ e)

lemma gS_u (he : 0 < e) : gS P he (Node.u (0 : k)) = AdjoinRoot.root _ := nodeLift_u ..

lemma gS_v (he : 0 < e) : gS P he (Node.v (0 : k)) = 0 := nodeLift_v ..

lemma gT_u (he : 0 < e) : gT P he (Node.u (0 : k)) = 0 := nodeLift_u ..

lemma gT_v (he : 0 < e) : gT P he (Node.v (0 : k)) = AdjoinRoot.root _ := nodeLift_v ..

lemma node_span' (he : 0 < e) (b : KummerEtale.B (0 : k)) :
    ∃ a a' : Fin e → KummerEtale.A (0 : k) e,
      b = ∑ i, a i • Node.v (0 : k) ^ (i : ℕ) + ∑ j, a' j • Node.u (0 : k) ^ (j : ℕ) := by
  obtain ⟨a, a', h⟩ := node_span he b
  exact ⟨a', a, h.trans (add_comm _ _)⟩

/-- **The `s`-branch of the Kummer factor `P ⊗_A B`** satisfies the cusp normal form hypotheses
if `ū` does on `P/(v̄)`. -/
theorem kummerTensor_nfHyp_s (he : 0 < e)
    (hP : CuspHom.NFHyp
      (P ⧸ Ideal.span {algebraMap (KummerEtale.A (0 : k) e) P (Node.v ((0 : k) ^ e))})
      (Ideal.Quotient.mk _ (algebraMap (KummerEtale.A (0 : k) e) P (Node.u ((0 : k) ^ e))))) :
    CuspHom.NFHyp ((P ⊗[KummerEtale.A (0 : k) e] KummerEtale.B (0 : k)) ⧸
        Ideal.span {(1 : P) ⊗ₜ[KummerEtale.A (0 : k) e] Node.v (0 : k)})
      (Ideal.Quotient.mk _ ((1 : P) ⊗ₜ[KummerEtale.A (0 : k) e] Node.u (0 : k))) :=
  nfHyp_branch (gS_u he) (gS_v he) he (node_span he) (KummerEtale.algebraMap_v _ _) hP

/-- **The `t`-branch of the Kummer factor `P ⊗_A B`** satisfies the cusp normal form hypotheses
if `v̄` does on `P/(ū)`. -/
theorem kummerTensor_nfHyp_t (he : 0 < e)
    (hP : CuspHom.NFHyp
      (P ⧸ Ideal.span {algebraMap (KummerEtale.A (0 : k) e) P (Node.u ((0 : k) ^ e))})
      (Ideal.Quotient.mk _ (algebraMap (KummerEtale.A (0 : k) e) P (Node.v ((0 : k) ^ e))))) :
    CuspHom.NFHyp ((P ⊗[KummerEtale.A (0 : k) e] KummerEtale.B (0 : k)) ⧸
        Ideal.span {(1 : P) ⊗ₜ[KummerEtale.A (0 : k) e] Node.u (0 : k)})
      (Ideal.Quotient.mk _ ((1 : P) ⊗ₜ[KummerEtale.A (0 : k) e] Node.v (0 : k))) :=
  nfHyp_branch (gT_v he) (gT_u he) he (node_span' he) (KummerEtale.algebraMap_u _ _) hP

/-- **The branches of the Kummer factor `P ⊗_A B` meet in `0`** if `(ū) ∩ (v̄) = 0` in `P`. -/
theorem kummerTensor_hinter (he : 0 < e)
    (hP : ∀ p : P,
      p ∈ Ideal.span {algebraMap (KummerEtale.A (0 : k) e) P (Node.u ((0 : k) ^ e))} →
      p ∈ Ideal.span {algebraMap (KummerEtale.A (0 : k) e) P (Node.v ((0 : k) ^ e))} → p = 0)
    (z : P ⊗[KummerEtale.A (0 : k) e] KummerEtale.B (0 : k))
    (hzs : z ∈ Ideal.span {(1 : P) ⊗ₜ[KummerEtale.A (0 : k) e] Node.u (0 : k)})
    (hzt : z ∈ Ideal.span {(1 : P) ⊗ₜ[KummerEtale.A (0 : k) e] Node.v (0 : k)}) : z = 0 :=
  inter_eq_zero (A := KummerEtale.A (0 : k) e) (B := KummerEtale.B (0 : k)) (P := P)
    (x := Node.u ((0 : k) ^ e)) (y := Node.v ((0 : k) ^ e)) (σ := Node.u (0 : k))
    (τ := Node.v (0 : k)) (g := gS P he) (gs := gT P he) (gS_u he) (gS_v he) he
    (node_span he) (KummerEtale.algebraMap_u _ _) (KummerEtale.algebraMap_v _ _) u_mul_v_zero
    (gT_v he) (gT_u he) hP z hzs hzt

end Node

end NodeNormalForm

/-! ### The statements for `Admissible.KummerPiece` -/

namespace Admissible

open AdmissibleLift TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {f : R}
  (φ : Node k (0 : k) →ₐ[k] Hat f) (ε : Hat f) {e : ℕ} (he : 0 < e)

/-- **The `s`-branch of the Kummer factor** `KP = (R̂/(1 − ε)) ⊗_A B`: `s = 1 ⊗ s` satisfies the
cusp normal form hypotheses on `KP/(t)` if `ū` does on `(R̂/(1 − ε))/(v̄)`. -/
theorem kummerPiece_nfHyp_s
    (hP : CuspHom.NFHyp
      (PieceBase φ ε he ⧸ Ideal.span {PieceBase.nodeMap φ ε he (Node.v ((0 : k) ^ e))})
      (Ideal.Quotient.mk _ (PieceBase.nodeMap φ ε he (Node.u ((0 : k) ^ e))))) :
    CuspHom.NFHyp (KummerPiece φ ε he ⧸
        Ideal.span {(1 : PieceBase φ ε he) ⊗ₜ[KummerEtale.A (0 : k) e] Node.v (0 : k)})
      (Ideal.Quotient.mk _ ((1 : PieceBase φ ε he) ⊗ₜ[KummerEtale.A (0 : k) e] Node.u (0 : k))) :=
  NodeNormalForm.kummerTensor_nfHyp_s he hP

/-- **The `t`-branch of the Kummer factor**: `t = 1 ⊗ t` satisfies the cusp normal form
hypotheses on `KP/(s)` if `v̄` does on `(R̂/(1 − ε))/(ū)`. -/
theorem kummerPiece_nfHyp_t
    (hP : CuspHom.NFHyp
      (PieceBase φ ε he ⧸ Ideal.span {PieceBase.nodeMap φ ε he (Node.u ((0 : k) ^ e))})
      (Ideal.Quotient.mk _ (PieceBase.nodeMap φ ε he (Node.v ((0 : k) ^ e))))) :
    CuspHom.NFHyp (KummerPiece φ ε he ⧸
        Ideal.span {(1 : PieceBase φ ε he) ⊗ₜ[KummerEtale.A (0 : k) e] Node.u (0 : k)})
      (Ideal.Quotient.mk _ ((1 : PieceBase φ ε he) ⊗ₜ[KummerEtale.A (0 : k) e] Node.v (0 : k))) :=
  NodeNormalForm.kummerTensor_nfHyp_t he hP

/-- **The branches of the Kummer factor meet in `0`** if `(ū) ∩ (v̄) = 0` in `R̂/(1 − ε)`. -/
theorem kummerPiece_hinter
    (hP : ∀ p : PieceBase φ ε he,
      p ∈ Ideal.span {PieceBase.nodeMap φ ε he (Node.u ((0 : k) ^ e))} →
      p ∈ Ideal.span {PieceBase.nodeMap φ ε he (Node.v ((0 : k) ^ e))} → p = 0)
    (z : KummerPiece φ ε he)
    (hzs : z ∈ Ideal.span {(1 : PieceBase φ ε he) ⊗ₜ[KummerEtale.A (0 : k) e] Node.u (0 : k)})
    (hzt : z ∈ Ideal.span {(1 : PieceBase φ ε he) ⊗ₜ[KummerEtale.A (0 : k) e] Node.v (0 : k)}) :
    z = 0 :=
  NodeNormalForm.kummerTensor_hinter he hP z hzs hzt

end Admissible

end SemistableReduction
