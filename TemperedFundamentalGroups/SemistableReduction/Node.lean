/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The local model of a node

For a commutative ring `O` and `a : O`, `SemistableReduction.Node O a` is the `O`-algebra
`O[u, v] ⧸ (u v - a)`, the local model of a node of thickness `a` (Blueprint §9.2, the local
tame lemma). We show:

* `Node.span_eq_top`: as an `O`-module, `Node O a` is spanned by the monomials `u ^ i` and
  `v ^ (j + 1)` (the normal form of an element).
* `Node.laurent O a k`: for a domain `O` with fraction field `K`, the `O`-algebra map
  `Node O a → K[T;T⁻¹]`, `u ↦ T ^ k`, `v ↦ a T ^ (-k)`; it is injective when `a ≠ 0` and
  `0 < k` (`Node.laurent_injective`).
* `Node.isDomain`: `Node O a` is a domain if `O` is and `a ≠ 0`.
* `Node.kummer O c m`: the `O`-algebra map `Node O (c ^ m) → Node O c`, `u ↦ u ^ m`, `v ↦ v ^ m`,
  injective for `c ≠ 0`, `0 < m` (`Node.kummer_injective`), and making `Node O c` a finite
  (`Node.kummer_finite`), hence integral, algebra over `Node O (c ^ m)`.
-/


open LaurentPolynomial

namespace SemistableReduction

variable (O : Type*) [CommRing O]

/-- The local model `O[u, v] ⧸ (u v - a)` of a node of thickness `a`. -/
abbrev Node (a : O) : Type _ :=
  MvPolynomial (Fin 2) O ⧸ Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C a}

namespace Node

variable {O} (a : O)

/-- The first coordinate `u` of the node `O[u, v] ⧸ (u v - a)`. -/
noncomputable def u : Node O a := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The second coordinate `v` of the node `O[u, v] ⧸ (u v - a)`. -/
noncomputable def v : Node O a := Ideal.Quotient.mk _ (MvPolynomial.X 1)

lemma u_mul_v : u a * v a = algebraMap O (Node O a) a := by
  rw [u, v, ← map_mul, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
    Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

variable {a}

/-- The `O`-algebra map out of the node sending `u ↦ x` and `v ↦ y`, for `x y = a`. -/
noncomputable def lift {S : Type*} [CommRing S] [Algebra O S] (x y : S)
    (h : x * y = algebraMap O S a) : Node O a →ₐ[O] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![x, y]) fun p hp ↦ by
    induction hp using Submodule.span_induction with
    | mem q hq =>
      rw [Set.mem_singleton_iff.mp hq]
      simp [h]
    | zero => simp
    | add _ _ _ _ h₁ h₂ => simp [h₁, h₂]
    | smul r _ _ h₁ => simp [h₁]

@[simp] lemma lift_u {S : Type*} [CommRing S] [Algebra O S] (x y : S)
    (h : x * y = algebraMap O S a) : lift x y h (u a) = x := by
  simp [lift, u]

@[simp] lemma lift_v {S : Type*} [CommRing S] [Algebra O S] (x y : S)
    (h : x * y = algebraMap O S a) : lift x y h (v a) = y := by
  simp [lift, v]

/-- Two `O`-algebra maps out of the node agreeing on `u` and `v` are equal. -/
lemma algHom_ext {S : Type*} [CommRing S] [Algebra O S] {f g : Node O a →ₐ[O] S}
    (hu : f (u a) = g (u a)) (hv : f (v a) = g (v a)) : f = g := by
  refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ ?_)
  fin_cases i
  · exact hu
  · exact hv

variable (a)

/-- The monomials `u ^ i` (`i : ℕ`) and `v ^ (j + 1)` (`j : ℕ`) of the node. -/
noncomputable def monomial : ℕ ⊕ ℕ → Node O a :=
  Sum.elim (fun i ↦ u a ^ i) (fun j ↦ v a ^ (j + 1))

lemma mul_u_mem {x : Node O a} (hx : x ∈ Submodule.span O (Set.range (monomial a))) :
    x * u a ∈ Submodule.span O (Set.range (monomial a)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    rcases s with i | j
    · exact Submodule.subset_span ⟨.inl (i + 1), by simp [monomial, pow_succ]⟩
    · have : v a ^ (j + 1) * u a = a • v a ^ j :=
        calc v a ^ (j + 1) * u a = algebraMap O (Node O a) a * v a ^ j := by
              rw [← u_mul_v, pow_succ]; ring
          _ = a • v a ^ j := (Algebra.smul_def _ _).symm
      simp only [monomial, Sum.elim_inr, this]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rcases j with _ | j
      · exact ⟨.inl 0, by simp⟩
      · exact ⟨.inr j, rfl⟩
  | zero => simp
  | add _ _ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
  | smul r _ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁

lemma mul_v_mem {x : Node O a} (hx : x ∈ Submodule.span O (Set.range (monomial a))) :
    x * v a ∈ Submodule.span O (Set.range (monomial a)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    rcases s with i | j
    · rcases i with _ | i
      · exact Submodule.subset_span ⟨.inr 0, by simp [monomial]⟩
      · have : u a ^ (i + 1) * v a = a • u a ^ i :=
          calc u a ^ (i + 1) * v a = algebraMap O (Node O a) a * u a ^ i := by
                rw [← u_mul_v, pow_succ]; ring
            _ = a • u a ^ i := (Algebra.smul_def _ _).symm
        simp only [monomial, Sum.elim_inl, this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl i, rfl⟩)
    · exact Submodule.subset_span ⟨.inr (j + 1), by simp [monomial, pow_succ]⟩
  | zero => simp
  | add _ _ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
  | smul r _ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁

/-- Normal form: the node is spanned over `O` by the monomials `u ^ i` and `v ^ (j + 1)`. -/
lemma span_eq_top : Submodule.span O (Set.range (monomial a)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r =>
    have : (Ideal.Quotient.mk _ (MvPolynomial.C r) : Node O a) = r • (1 : Node O a) :=
      calc (Ideal.Quotient.mk _ (MvPolynomial.C r) : Node O a)
          = algebraMap O (Node O a) r * 1 := by
            rw [mul_one, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
        _ = r • (1 : Node O a) := (Algebra.smul_def _ _).symm
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl 0, by simp [monomial]⟩)
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    fin_cases i
    · exact mul_u_mem a hp
    · exact mul_v_mem a hp

section Laurent

local notation "K" => FractionRing O

/-- The `O`-algebra map `Node O a → K[T;T⁻¹]`, `u ↦ T ^ k`, `v ↦ a T ^ (-k)`, where `K` is the
fraction field of `O`. -/
noncomputable def laurent (k : ℕ) : Node O a →ₐ[O] K[T;T⁻¹] :=
  lift (T k) (C (algebraMap O K a) * T (-k)) (by
    rw [mul_left_comm, ← T_add, add_neg_cancel, T_zero, mul_one,
      LaurentPolynomial.algebraMap_apply])

@[simp] lemma laurent_u (k : ℕ) : laurent a k (u a) = T k := lift_u ..

@[simp] lemma laurent_v (k : ℕ) : laurent a k (v a) = C (algebraMap O K a) * T (-k) := lift_v ..

/-- The exponent of the image of a monomial under `laurent a k`. -/
def laurentExp (k : ℕ) : ℕ ⊕ ℕ → ℤ :=
  Sum.elim (fun i ↦ k * i) (fun j ↦ -(k * (j + 1)))

/-- The coefficient of the image of a monomial under `laurent a k`. -/
noncomputable def laurentCoeff : ℕ ⊕ ℕ → K :=
  Sum.elim (fun _ ↦ 1) (fun j ↦ algebraMap O K a ^ (j + 1))

lemma laurent_monomial (k : ℕ) (s : ℕ ⊕ ℕ) :
    laurent a k (monomial a s) = AddMonoidAlgebra.single (laurentExp k s) (laurentCoeff a s) := by
  rcases s with i | j
  · simp only [monomial, Sum.elim_inl, map_pow, laurent_u, T_pow, laurentExp, laurentCoeff]
    rw [mul_comm]; rfl
  · simp only [monomial, Sum.elim_inr]
    rw [map_pow, laurent_v, mul_pow, ← map_pow, T_pow, single_eq_C_mul_T]
    simp only [laurentExp, laurentCoeff, Sum.elim_inr]
    congr 2
    push_cast; ring

variable [IsDomain O]

/-- An `O`-algebra map from the node to `K[T;T⁻¹]` sending the monomials to nonzero multiples of
pairwise distinct powers of `T` is injective. -/
lemma injective_of_monomial (χ : Node O a →ₐ[O] K[T;T⁻¹]) (e : ℕ ⊕ ℕ → ℤ)
    (he : Function.Injective e) (γ : ℕ ⊕ ℕ → K) (hγ : ∀ s, γ s ≠ 0)
    (hχ : ∀ s, χ (monomial a s) = AddMonoidAlgebra.single (e s) (γ s)) :
    Function.Injective χ := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : x ∈ Submodule.span O (Set.range (monomial a)) := by
    rw [span_eq_top]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx'
  suffices c = 0 by simp [this]
  ext s
  have h := congr_arg (fun f : K[T;T⁻¹] ↦ f.coeff (e s)) hx
  simp only [map_finsuppSum, map_smul, hχ, AddMonoidAlgebra.coeff_finsuppSum,
    AddMonoidAlgebra.smul_single, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply, Finsupp.sum_apply] at h
  rw [Finsupp.sum, Finset.sum_eq_single s] at h
  · rw [Finsupp.single_eq_same, Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · simpa using (FaithfulSMul.algebraMap_injective O K) (h.trans (map_zero _).symm)
    · exact absurd h (hγ s)
  · intro t _ hts
    rw [Finsupp.single_eq_of_ne (he.ne hts).symm]
  · intro hs
    rw [Finsupp.notMem_support_iff.mp hs, zero_smul, Finsupp.single_zero, Finsupp.zero_apply]

variable {a}

/-- For `a ≠ 0` and `0 < k`, the map `u ↦ T ^ k`, `v ↦ a T ^ (-k)` is injective. -/
theorem laurent_injective (ha : a ≠ 0) {k : ℕ} (hk : 0 < k) :
    Function.Injective (laurent a k) := by
  refine injective_of_monomial a _ (laurentExp k) ?_ (laurentCoeff a) ?_ (laurent_monomial a k)
  · have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    rintro (i | i) (j | j) h <;> simp only [laurentExp, Sum.elim_inl, Sum.elim_inr] at h
    · simpa using (mul_left_cancel₀ hk' h)
    · nlinarith [mul_pos (show (0 : ℤ) < k by exact_mod_cast hk)
        (show (0 : ℤ) < j + 1 by positivity), mul_nonneg (show (0 : ℤ) ≤ k by positivity)
        (show (0 : ℤ) ≤ i by positivity)]
    · nlinarith [mul_pos (show (0 : ℤ) < k by exact_mod_cast hk)
        (show (0 : ℤ) < i + 1 by positivity), mul_nonneg (show (0 : ℤ) ≤ k by positivity)
        (show (0 : ℤ) ≤ j by positivity)]
    · have := mul_left_cancel₀ hk' (neg_inj.mp h)
      simp only [Sum.inr.injEq]; lia
  · rintro (i | j)
    · exact one_ne_zero
    · exact pow_ne_zero _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mpr ha)

/-- The node `O[u, v] ⧸ (u v - a)` over a domain `O` is a domain if `a ≠ 0`. -/
theorem isDomain (ha : a ≠ 0) : IsDomain (Node O a) :=
  (laurent_injective ha one_pos).isDomain

end Laurent

section Kummer

variable (c : O) (m : ℕ)

/-- The Kummer map `O[u, v] ⧸ (u v - c ^ m) → O[w, z] ⧸ (w z - c)`, `u ↦ w ^ m`, `v ↦ z ^ m`. -/
noncomputable def kummer : Node O (c ^ m) →ₐ[O] Node O c :=
  lift (u c ^ m) (v c ^ m) (by rw [← mul_pow, u_mul_v, map_pow])

@[simp] lemma kummer_u : kummer c m (u (c ^ m)) = u c ^ m := lift_u ..

@[simp] lemma kummer_v : kummer c m (v (c ^ m)) = v c ^ m := lift_v ..

lemma laurent_comp_kummer [IsDomain O] :
    (laurent c 1).comp (kummer c m) = laurent (c ^ m) m := by
  refine algHom_ext ?_ ?_
  · simp [T_pow]
  · rw [AlgHom.comp_apply, kummer_v, map_pow, laurent_v, laurent_v, mul_pow, T_pow,
      map_pow (algebraMap O _), map_pow C]
    congr 2
    push_cast; ring

variable {c m}

/-- The Kummer map is injective for `c ≠ 0` and `0 < m`. -/
theorem kummer_injective [IsDomain O] (hc : c ≠ 0) (hm : 0 < m) :
    Function.Injective (kummer c m) := by
  have h := laurent_injective (pow_ne_zero m hc) hm
  rw [← laurent_comp_kummer] at h
  exact Function.Injective.of_comp h

variable (c m)

/-- `O[w, z] ⧸ (w z - c)` as an algebra over `O[u, v] ⧸ (u v - c ^ m)` via the Kummer map
`u ↦ w ^ m`, `v ↦ z ^ m`. Not an instance. -/
noncomputable abbrev kummerAlgebra : Algebra (Node O (c ^ m)) (Node O c) :=
  (kummer c m).toAlgebra

lemma kummer_algebraMap_u :
    letI := kummerAlgebra c m
    algebraMap (Node O (c ^ m)) (Node O c) (u (c ^ m)) = u c ^ m :=
  kummer_u c m

lemma kummer_algebraMap_v :
    letI := kummerAlgebra c m
    algebraMap (Node O (c ^ m)) (Node O c) (v (c ^ m)) = v c ^ m :=
  kummer_v c m

lemma kummer_adjoin_eq_top :
    letI := kummerAlgebra c m
    Algebra.adjoin (Node O (c ^ m)) {u c, v c} = ⊤ := by
  letI := kummerAlgebra c m
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r =>
    have : (Ideal.Quotient.mk _ (MvPolynomial.C r) : Node O c) =
        algebraMap (Node O (c ^ m)) (Node O c) (algebraMap O _ r) := by
      rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
      exact ((kummer c m).commutes r).symm
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp (Algebra.subset_adjoin ?_)
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl

variable {m}

lemma kummer_isIntegral_u (hm : 0 < m) :
    letI := kummerAlgebra c m
    IsIntegral (Node O (c ^ m)) (u c) := by
  letI := kummerAlgebra c m
  refine ⟨Polynomial.X ^ m - Polynomial.C (u (c ^ m)), Polynomial.monic_X_pow_sub_C _ hm.ne', ?_⟩
  simp [Polynomial.eval₂_sub, kummer_algebraMap_u]

lemma kummer_isIntegral_v (hm : 0 < m) :
    letI := kummerAlgebra c m
    IsIntegral (Node O (c ^ m)) (v c) := by
  letI := kummerAlgebra c m
  refine ⟨Polynomial.X ^ m - Polynomial.C (v (c ^ m)), Polynomial.monic_X_pow_sub_C _ hm.ne', ?_⟩
  simp [Polynomial.eval₂_sub, kummer_algebraMap_v]

/-- `O[w, z] ⧸ (w z - c)` is a finite algebra over `O[u, v] ⧸ (u v - c ^ m)` via the Kummer map,
for `0 < m`. -/
theorem kummer_finite (hm : 0 < m) :
    letI := kummerAlgebra c m
    Module.Finite (Node O (c ^ m)) (Node O c) := by
  letI := kummerAlgebra c m
  have h := fg_adjoin_of_finite (R := Node O (c ^ m)) (Set.toFinite {u c, v c}) (by
    rintro x (rfl | rfl)
    · exact kummer_isIntegral_u c hm
    · exact kummer_isIntegral_v c hm)
  rw [kummer_adjoin_eq_top, Algebra.top_toSubmodule] at h
  exact ⟨h⟩

/-- `O[w, z] ⧸ (w z - c)` is integral over `O[u, v] ⧸ (u v - c ^ m)` via the Kummer map, for
`0 < m`. -/
theorem kummer_isIntegral (hm : 0 < m) :
    letI := kummerAlgebra c m
    Algebra.IsIntegral (Node O (c ^ m)) (Node O c) := by
  letI := kummerAlgebra c m
  have := kummer_finite c hm
  exact Algebra.IsIntegral.of_finite _ _

end Kummer

end Node

end SemistableReduction
