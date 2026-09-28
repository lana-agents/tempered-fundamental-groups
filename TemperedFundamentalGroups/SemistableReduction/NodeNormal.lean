/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Node

/-!
# The node is normal

Let `O` be an integrally closed domain with fraction field `K` and `c ∈ O` nonzero. We show that
the node `O[w, z] ⧸ (w z - c)` is integrally closed (`Node.isIntegrallyClosed`).

Via `Node.laurent c 1` (`w ↦ T`, `z ↦ c T⁻¹`), the node is the subring `O[T, c T⁻¹]` of the
Laurent polynomial ring `K[T;T⁻¹]`, which is integrally closed (a localization of `K[X]`) with the
same fraction field. An element `f ∈ K[T;T⁻¹]` integral over `O[T, c T⁻¹]` is integral over the
two "charts" `O[T, T⁻¹]` and `O[c T, (c T)⁻¹] = τ⁻¹ O[T, T⁻¹]`, where `τ : T ↦ c T`:

* `integralLaurent O`, the Laurent polynomials with coefficients in `O`, is integrally closed in
  `K[T;T⁻¹]` (`mem_integralLaurent_of_eval_eq_zero`): after multiplying by a power of `T` this is
  the statement that `O[X]` is integrally closed in `K[X]` (Mathlib's `IsIntegral.coeff`);
* hence the coefficients `f_j` of `f` lie in `O`, and those of `τ f`, namely `c ^ j f_j`, too;
  these two conditions say exactly that `f ∈ O[T, c T⁻¹]` (`mem_range_laurent`).
-/

open LaurentPolynomial

namespace SemistableReduction

variable {O : Type*} [CommRing O]

local notation "K" => FractionRing O

section IntegralLaurent

variable (O) in
/-- The Laurent polynomials over the fraction field `K` of `O` all of whose coefficients lie in
`O`, i.e. the image of `O[T;T⁻¹]` in `K[T;T⁻¹]`. -/
def integralLaurent : Subalgebra O K[T;T⁻¹] where
  carrier := {f | ∀ j, f.coeff j ∈ (algebraMap O K).range}
  mul_mem' {f g} hf hg j := by
    rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
    exact Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (hf i) (hg _)
  add_mem' {f g} hf hg j := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact Subring.add_mem _ (hf j) (hg j)
  algebraMap_mem' r j := by
    rw [LaurentPolynomial.algebraMap_apply, ← single_eq_C, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    split_ifs
    · exact ⟨r, rfl⟩
    · exact Subring.zero_mem _

lemma mem_integralLaurent {f : K[T;T⁻¹]} :
    f ∈ integralLaurent O ↔ ∀ j, f.coeff j ∈ (algebraMap O K).range := Iff.rfl

lemma T_mem_integralLaurent (n : ℤ) : (T n : K[T;T⁻¹]) ∈ integralLaurent O := by
  intro j
  rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs
  · exact ⟨1, map_one _⟩
  · exact Subring.zero_mem _

/-- The image of `O[X]` in `K[T;T⁻¹]`. -/
lemma toLaurent_map_mem_integralLaurent (h : Polynomial O) :
    Polynomial.toLaurent (h.map (algebraMap O K)) ∈ integralLaurent O := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add]; exact add_mem hp hq
  | monomial n r =>
    rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.toLaurent_C_mul_X_pow, ← LaurentPolynomial.algebraMap_apply]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (T_mem_integralLaurent _)

lemma coeff_toLaurent_natCast (p : Polynomial K) (k : ℕ) :
    (Polynomial.toLaurent p).coeff (k : ℤ) = p.coeff k := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.cast_injective _ k

lemma exists_map_eq_of_toLaurent_mem {p : Polynomial K}
    (hp : Polynomial.toLaurent p ∈ integralLaurent O) :
    ∃ h : Polynomial O, h.map (algebraMap O K) = p := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro k
  rw [← coeff_toLaurent_natCast]
  exact hp k

/-- `g` becomes an element of the image of `O[X]` after multiplication by `T ^ N`. -/
def Good (g : K[T;T⁻¹]) (N : ℕ) : Prop :=
  ∃ h : Polynomial O, Polynomial.toLaurent (h.map (algebraMap O K)) = T N * g

lemma Good.mono {g : K[T;T⁻¹]} {N N' : ℕ} (hg : Good g N) (hN : N ≤ N') : Good g N' := by
  obtain ⟨h, hh⟩ := hg
  refine ⟨h * Polynomial.X ^ (N' - N), ?_⟩
  rw [Polynomial.map_mul, map_mul, hh, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.toLaurent_X_pow, mul_comm, ← mul_assoc, ← T_add]
  congr 2
  push_cast [hN]; ring

lemma exists_good {g : K[T;T⁻¹]} (hg : g ∈ integralLaurent O) : ∃ N, Good g N := by
  obtain ⟨n, g', hg'⟩ := exists_T_pow g
  have : Polynomial.toLaurent g' ∈ integralLaurent O := hg' ▸ mul_mem hg (T_mem_integralLaurent _)
  obtain ⟨h, rfl⟩ := exists_map_eq_of_toLaurent_mem this
  exact ⟨n, h, hg'.trans (mul_comm _ _)⟩

lemma exists_good_coeff {q : Polynomial K[T;T⁻¹]} (hq : ∀ i, q.coeff i ∈ integralLaurent O) :
    ∃ N, ∀ i, Good (q.coeff i) N := by
  classical
  choose N hN using fun i ↦ exists_good (hq i)
  refine ⟨q.support.sup N, fun i ↦ ?_⟩
  by_cases hi : i ∈ q.support
  · exact (hN i).mono (Finset.le_sup hi)
  · rw [Polynomial.notMem_support_iff.mp hi]
    exact ⟨0, by simp⟩

attribute [local instance] Polynomial.algebra in
/-- `integralLaurent O` is integrally closed in `K[T;T⁻¹]`: a root of a monic polynomial with
coefficients in `integralLaurent O` lies in `integralLaurent O`. -/
theorem mem_integralLaurent_of_eval_eq_zero [IsDomain O] [IsIntegrallyClosed O] {f : K[T;T⁻¹]}
    {q : Polynomial K[T;T⁻¹]} (hqm : q.Monic) (hq : ∀ i, q.coeff i ∈ integralLaurent O)
    (hf : q.eval f = 0) : f ∈ integralLaurent O := by
  obtain ⟨N, hN⟩ := exists_good_coeff hq
  obtain ⟨n₀, g', hg'⟩ := exists_T_pow f
  set L := N + n₀
  set y : K[T;T⁻¹] := T L * f
  have hy : Polynomial.toLaurent (g' * Polynomial.X ^ N) = y := by
    rw [map_mul, hg', Polynomial.toLaurent_X_pow, mul_assoc, ← T_add, mul_comm]
    simp [y, L, add_comm]
  -- the scaled polynomial has coefficients in the image of `O[X]`
  let ι : Polynomial O →+* K[T;T⁻¹] :=
    Polynomial.toLaurent.comp (Polynomial.mapRingHom (algebraMap O K))
  set Q := q.scaleRoots (T L)
  have hQm : Q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr hqm
  have hQ : Q ∈ Polynomial.lifts ι := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    by_cases hi : i < q.natDegree
    · obtain ⟨h, hh⟩ := (hN i).mono (show N ≤ L * (q.natDegree - i) from
        (Nat.le_add_right N n₀).trans (Nat.le_mul_of_pos_right _ (by lia)))
      refine ⟨h, ?_⟩
      simp only [ι, RingHom.comp_apply, Polynomial.coe_mapRingHom, hh, T_pow, mul_comm]
      push_cast; ring_nf
    · rw [show q.natDegree - i = 0 by lia, pow_zero, mul_one]
      rcases (not_lt.mp hi).eq_or_lt with h | h
      · rw [← h, hqm.coeff_natDegree]; exact ⟨1, map_one _⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, map_zero _⟩
  obtain ⟨P, hPQ, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hQ hQm
  have hQy : Q.eval y = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := q) (RingHom.id _) f (T L)
    simp only [RingHom.id_apply, Polynomial.eval₂_id] at this
    rw [show y = T L * f from rfl, this, hf, mul_zero]
  -- hence `g' X ^ N` is integral over `O[X]`, so its coefficients lie in `O`
  have hint : IsIntegral (Polynomial O) (g' * Polynomial.X ^ N) := by
    refine ⟨P, hPm, Polynomial.toLaurent_injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, hy, Polynomial.algebraMap_def,
      show Polynomial.toLaurent.comp (Polynomial.mapRingHom (algebraMap O K)) = ι from rfl,
      ← Polynomial.eval_map, hPQ, hQy]
  have hcoeff : ∀ k, (g' * Polynomial.X ^ N).coeff k ∈ Set.range (algebraMap O K) := fun k ↦
    IsIntegrallyClosed.isIntegral_iff.mp (hint.coeff k)
  obtain ⟨h, hh⟩ : g' * Polynomial.X ^ N ∈ Polynomial.lifts (algebraMap O K) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr hcoeff
  have hymem : y ∈ integralLaurent O := by
    rw [← hy, ← hh]; exact toLaurent_map_mem_integralLaurent h
  have : f = T (-L) * y := by
    rw [show y = T L * f from rfl, ← mul_assoc, ← T_add, neg_add_cancel, T_zero, one_mul]
  rw [this]
  exact mul_mem (T_mem_integralLaurent _) hymem

end IntegralLaurent

section Scale

lemma coeff_C_mul_T (a : K) (n j : ℤ) :
    (C a * T n : K[T;T⁻¹]).coeff j = if n = j then a else 0 := by
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

variable [IsDomain O]

/-- The unit `c T` of `K[T;T⁻¹]`. -/
noncomputable def scaleUnit {c : K} (hc : c ≠ 0) : (K[T;T⁻¹])ˣ where
  val := C c * T 1
  inv := C c⁻¹ * T (-1)
  val_inv := by
    rw [mul_mul_mul_comm, ← map_mul, ← T_add, mul_inv_cancel₀ hc, add_neg_cancel, map_one, T_zero,
      one_mul]
  inv_val := by
    rw [mul_mul_mul_comm, ← map_mul, ← T_add, inv_mul_cancel₀ hc, neg_add_cancel, map_one, T_zero,
      one_mul]

/-- The ring endomorphism `T ↦ c T` of `K[T;T⁻¹]`. -/
noncomputable def scale {c : K} (hc : c ≠ 0) : K[T;T⁻¹] →+* K[T;T⁻¹] :=
  LaurentPolynomial.eval₂ C (scaleUnit hc)

lemma coeff_scale {c : K} (hc : c ≠ 0) (f : K[T;T⁻¹]) (j : ℤ) : (scale hc f).coeff j = c ^ j * f.coeff j := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
  | C_mul_T n a =>
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [scale, eval₂_C_mul_T_n]
      simp only [scaleUnit, mul_pow, T_pow, ← map_pow]
      rw [← mul_assoc, ← map_mul, coeff_C_mul_T, coeff_C_mul_T, mul_one]
      split_ifs with h
      · subst h; rw [zpow_natCast, mul_comm]
      · rw [mul_zero]
    · rw [scale, eval₂_C_mul_T_neg_n]
      have hinv : ((scaleUnit hc)⁻¹ : (K[T;T⁻¹])ˣ).val = C c⁻¹ * T (-1) := rfl
      rw [hinv, mul_pow, T_pow, ← map_pow, ← mul_assoc, ← map_mul, coeff_C_mul_T, coeff_C_mul_T]
      split_ifs with h₁ h₂ h₂
      · rw [← h₂, zpow_neg, zpow_natCast, inv_pow, mul_comm]
      · exact absurd (by rw [← h₁]; ring) h₂
      · exact absurd (by rw [← h₂]; ring) h₁
      · rw [mul_zero]

end Scale

namespace Node

variable (a : O)

lemma adjoin_u_v : Algebra.adjoin O {u a, v a} = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r =>
    have : (Ideal.Quotient.mk _ (MvPolynomial.C r) : Node O a) = algebraMap O _ r := by
      rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp (Algebra.subset_adjoin ?_)
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl

/-- An `O`-algebra map out of the node lands in a subalgebra containing the images of `u`, `v`. -/
lemma range_le {B : Type*} [CommRing B] [Algebra O B] (χ : Node O a →ₐ[O] B)
    {S : Subalgebra O B} (hu : χ (u a) ∈ S) (hv : χ (v a) ∈ S) : χ.range ≤ S := by
  rw [← Algebra.map_top, ← adjoin_u_v, AlgHom.map_adjoin, Algebra.adjoin_le_iff,
    Set.image_pair, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hu, hv⟩

variable {a}

lemma algebraMap_ne_zero (ha : a ≠ 0) : algebraMap O K a ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mpr ha

variable [IsDomain O] in
/-- `f ∈ K[T;T⁻¹]` lies in `O[T, c T⁻¹]` as soon as its coefficients lie in `O` and those of
`f(c T)` do. -/
lemma mem_range_laurent {c : O} (hc : c ≠ 0) {f : K[T;T⁻¹]} (h₁ : f ∈ integralLaurent O)
    (h₂ : scale (algebraMap_ne_zero hc) f ∈ integralLaurent O) : f ∈ (laurent c 1).range := by
  rw [← AddMonoidAlgebra.sum_coeff_single f, Finsupp.sum]
  refine Subalgebra.sum_mem _ fun j _ ↦ ?_
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · obtain ⟨o, ho⟩ := h₁ k
    refine ⟨algebraMap O _ o * u c ^ k, ?_⟩
    change laurent c 1 (algebraMap O _ o * u c ^ k) = _
    rw [map_mul, AlgHom.commutes, map_pow, laurent_u, LaurentPolynomial.algebraMap_apply, ho,
      single_eq_C_mul_T, T_pow]
    simp
  · obtain ⟨o, ho⟩ := h₂ (-k)
    rw [coeff_scale, zpow_neg, zpow_natCast] at ho
    have hf : f.coeff (-k) = algebraMap O K c ^ k * algebraMap O K o := by
      rw [ho, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (algebraMap_ne_zero hc)), one_mul]
    refine ⟨algebraMap O _ o * v c ^ k, ?_⟩
    change laurent c 1 (algebraMap O _ o * v c ^ k) = _
    rw [map_mul, AlgHom.commutes, map_pow, laurent_v, LaurentPolynomial.algebraMap_apply, hf,
      single_eq_C_mul_T, mul_pow, T_pow, ← map_pow, ← mul_assoc, ← map_mul, mul_comm (_ ^ k)]
    congr 2
    push_cast; ring

variable [IsDomain O] [IsIntegrallyClosed O]

/-- An element of `K[T;T⁻¹]` integral over `O[T, c T⁻¹]` lies in `O[T, c T⁻¹]`. -/
theorem mem_range_laurent_of_isIntegral {c : O} (hc : c ≠ 0) {f : K[T;T⁻¹]}
    (hf : IsIntegral (laurent c 1).range f) : f ∈ (laurent c 1).range := by
  obtain ⟨p, hpm, hp⟩ := hf
  set q := p.map (algebraMap (laurent c 1).range K[T;T⁻¹])
  have hqm : q.Monic := hpm.map _
  have hq : ∀ i, q.coeff i ∈ (laurent c 1).range := fun i ↦ by
    rw [Polynomial.coeff_map]; exact (p.coeff i).2
  have hqf : q.eval f = 0 := by rw [Polynomial.eval_map]; exact hp
  have hS₁ : (laurent c 1).range ≤ integralLaurent O := by
    refine range_le c _ ?_ ?_
    · rw [laurent_u]; exact T_mem_integralLaurent _
    · rw [laurent_v, ← LaurentPolynomial.algebraMap_apply]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (T_mem_integralLaurent _)
  set τ := scale (algebraMap_ne_zero hc)
  have hS₂ : ∀ x ∈ (laurent c 1).range, τ x ∈ integralLaurent O := by
    let S : Subalgebra O K[T;T⁻¹] :=
      { (integralLaurent O).toSubring.comap τ with
        algebraMap_mem' := fun r ↦ by
          change τ (C (algebraMap O K r)) ∈ integralLaurent O
          rw [show τ (C (algebraMap O K r)) = C (algebraMap O K r) from eval₂_C _ _ _,
            ← LaurentPolynomial.algebraMap_apply]
          exact Subalgebra.algebraMap_mem _ _ }
    refine fun x hx ↦ range_le c _ (S := S) ?_ ?_ hx
    · change τ (laurent c 1 (u c)) ∈ integralLaurent O
      have hT : τ (T ((1 : ℕ) : ℤ)) = C (algebraMap O K c) * T 1 := by
        change LaurentPolynomial.eval₂ C (scaleUnit _) (T ((1 : ℕ) : ℤ)) = _
        rw [eval₂_T_n, pow_one]; rfl
      rw [laurent_u, hT, ← LaurentPolynomial.algebraMap_apply]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (T_mem_integralLaurent _)
    · change τ (laurent c 1 (v c)) ∈ integralLaurent O
      rw [laurent_v, show τ (C (algebraMap O K c) * T (-(1 : ℕ))) = T (-1) by
        change LaurentPolynomial.eval₂ C (scaleUnit _) (C _ * T (-((1 : ℕ) : ℤ))) = _
        rw [eval₂_C_mul_T_neg_n]
        change C (algebraMap O K c) * (C (algebraMap O K c)⁻¹ * T (-1)) ^ 1 = T (-1)
        rw [pow_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (algebraMap_ne_zero hc), map_one,
          one_mul]]
      exact T_mem_integralLaurent _
  have h₁ : f ∈ integralLaurent O :=
    mem_integralLaurent_of_eval_eq_zero hqm (fun i ↦ hS₁ (hq i)) hqf
  have h₂ : τ f ∈ integralLaurent O := by
    refine mem_integralLaurent_of_eval_eq_zero (hqm.map τ) (fun i ↦ ?_) ?_
    · rw [Polynomial.coeff_map]; exact hS₂ _ (hq i)
    · have h := Polynomial.hom_eval₂ q (RingHom.id _) τ f
      rw [RingHom.comp_id] at h
      rw [Polynomial.eval_map, ← h, Polynomial.eval₂_id, hqf, map_zero]
  exact mem_range_laurent hc h₁ h₂

/-- **The node is normal.** For an integrally closed domain `O` and `c ≠ 0`, the node
`O[w, z] ⧸ (w z - c)` is integrally closed. -/
theorem isIntegrallyClosed {c : O} (hc : c ≠ 0) : IsIntegrallyClosed (Node O c) := by
  have : IsIntegrallyClosed K[T;T⁻¹] :=
    isIntegrallyClosed_of_isLocalization (R := Polynomial K) K[T;T⁻¹]
      (Submonoid.powers Polynomial.X)
      (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)
  have : IsIntegrallyClosedIn (laurent c 1).range K[T;T⁻¹] :=
    isIntegrallyClosedIn_iff.mpr ⟨Subtype.val_injective,
      fun hf ↦ ⟨⟨_, mem_range_laurent_of_isIntegral hc hf⟩, rfl⟩⟩
  have : IsIntegrallyClosed (laurent c 1).range :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K[T;T⁻¹]
  exact IsIntegrallyClosed.of_equiv (R := (laurent c 1).range) (S := Node O c)
    (AlgEquiv.ofInjective _ (laurent_injective hc one_pos)).symm.toRingEquiv

end Node

end SemistableReduction
