/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TameLocal

/-!
# The closed point of a node and the regular node of thickness one

Let `O` be a commutative ring, `s ∈ O` and `a ∈ O` with `s ∣ a`. On the node
`Node O a = O[u, v] ⧸ (u v - a)` we consider the ideal `𝔪 = (u, v, s)` of the closed point
`u = v = s = 0` (`Node.closedPoint`). This file provides the commutative algebra of steps (1)
and (2) of the lemma "S4-local" of the MR12 plan (the generalisation of [Mzk1] §3.12 to
arbitrary thickness, a special case of [MzkExt] Thm. 3.3):

* `Node.ker_residue`: `𝔪` is the kernel of the residue map `Node O a → O ⧸ (s)`, `u, v ↦ 0`;
  it is maximal when `(s)` is (`Node.isMaximal_closedPoint`).
* **Thickness one.** For `a = s` we have `𝔪 = (u, v)` (`Node.closedPoint_self`), and `(u)` is
  the kernel of `Node O s → (O ⧸ (s))[Y]`, `u ↦ 0`, `v ↦ Y` (`Node.ker_branch`); hence `(u)` is
  prime when `(s)` is (`Node.isPrime_span_u`) and `v ∉ (u)` (`Node.v_notMem_span_u`).
  Consequently every localization `R₁` of `Node O s` at `𝔪` over a discrete valuation ring `O`
  with uniformizer `s` is a Noetherian integrally closed local domain whose maximal ideal is
  `(u, v)` with `u` prime and `v ∉ (u)` (`Node.ThicknessOne.prime_u`,
  `Node.ThicknessOne.v_notMem_span_u`, `Node.ThicknessOne.maximalIdeal_eq`,
  `Node.ThicknessOne.isIntegrallyClosed`, ...): exactly the hypotheses of the purity theorem
  `Purity.etale_of_isUnramifiedAt_of_maximalIdeal_eq_span_pair` (SGA 1, Exp. X, Cor. 3.2).
  (`R₁` is regular of dimension two with regular system of parameters `u, v`.)
* **The Kummer map.** For `0 < M` the Kummer map `Node.kummer s M : Node O (s ^ M) → Node O s`,
  `u ↦ u ^ M`, `v ↦ v ^ M`, pulls the closed point back to the closed point
  (`Node.comap_kummer_closedPoint`), and the closed point is the only prime over it
  (`Node.eq_closedPoint_of_comap_kummer`): the Kummer map identifies the punctured spectra
  `W₁ = Spec R₁ ∖ {𝔪}` and `φ⁻¹(W_M)`, whatever the thickness `M` (also for `p ∣ M`).

## References

* [SGA 1] A. Grothendieck, *Revêtements étales et groupe fondamental*, Exp. X, Cor. 3.2, 3.3.
* [MzkExt] S. Mochizuki, *Extending families of curves over log regular schemes*, J. reine angew.
  Math. 511 (1999), Thm. 3.3, Lemmas 3.1, 3.2, 4.2.
* [Mzk1] S. Mochizuki, *Semi-graphs of anabelioids*, §3.12.
-/

open IsLocalRing Polynomial

namespace SemistableReduction.Node

variable {O : Type*} [CommRing O]

section Residue

variable (a : O)

/-- Every element of the node is congruent to a constant modulo `(u, v)`. -/
lemma exists_sub_algebraMap_mem (x : Node O a) :
    ∃ c : O, x - algebraMap O (Node O a) c ∈ Ideal.span {u a, v a} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨r, ?_⟩
    rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, sub_self]
    exact zero_mem _
  | add p q hp hq =>
    obtain ⟨c, hc⟩ := hp
    obtain ⟨d, hd⟩ := hq
    refine ⟨c + d, ?_⟩
    convert add_mem hc hd using 1
    rw [map_add, map_add]
    ring
  | mul_X p i _ =>
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, map_mul]
    refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl

variable {a} (s : O)

/-- The ideal `(u, v, s)` of the closed point `u = v = s = 0` of the node `Node O a`. -/
noncomputable def closedPoint (a : O) : Ideal (Node O a) :=
  Ideal.span {u a, v a, algebraMap O (Node O a) s}

lemma u_mem_closedPoint : u a ∈ closedPoint s a := Ideal.subset_span (by simp)

lemma v_mem_closedPoint : v a ∈ closedPoint s a := Ideal.subset_span (by simp)

lemma algebraMap_mem_closedPoint : algebraMap O (Node O a) s ∈ closedPoint s a :=
  Ideal.subset_span (by simp)

/-- The residue map `Node O a → O ⧸ (s)`, `u, v ↦ 0`, for `s ∣ a`. -/
noncomputable def residue (h : s ∣ a) : Node O a →ₐ[O] O ⧸ Ideal.span {s} :=
  lift 0 0 (by
    rw [zero_mul, eq_comm, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr h)

lemma closedPoint_le_ker_residue (h : s ∣ a) :
    closedPoint s a ≤ RingHom.ker (residue s h) := by
  rw [closedPoint, Ideal.span_le]
  rintro y (rfl | rfl | rfl)
  · simp [residue]
  · simp [residue]
  · simp [AlgHom.commutes, Ideal.Quotient.algebraMap_eq]

/-- The closed point `(u, v, s)` is the kernel of the residue map `Node O a → O ⧸ (s)`. -/
theorem ker_residue (h : s ∣ a) : RingHom.ker (residue s h) = closedPoint s a := by
  refine le_antisymm (fun x hx ↦ ?_) (closedPoint_le_ker_residue s h)
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem a x
  have hle : Ideal.span {u a, v a} ≤ closedPoint s a :=
    Ideal.span_mono (Set.insert_subset_insert (Set.singleton_subset_iff.mpr (by simp)))
  have h1 : residue s h (x - algebraMap O _ c) = 0 := closedPoint_le_ker_residue s h (hle hc)
  rw [map_sub, RingHom.mem_ker.mp hx, zero_sub, neg_eq_zero, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at h1
  obtain ⟨d, rfl⟩ := h1
  have : x = (x - algebraMap O _ (s * d)) + algebraMap O _ s * algebraMap O _ d := by
    rw [map_mul]; ring
  rw [this]
  exact add_mem (hle hc) (Ideal.mul_mem_right _ _ (algebraMap_mem_closedPoint s))

lemma residue_surjective (h : s ∣ a) : Function.Surjective (residue s h) := by
  intro y
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap O _ c, by rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq]⟩

/-- If `(s)` is maximal and `s ∣ a`, the closed point `(u, v, s)` of `Node O a` is maximal. -/
theorem isMaximal_closedPoint [(Ideal.span {s}).IsMaximal] (h : s ∣ a) :
    (closedPoint s a).IsMaximal := by
  letI := Ideal.Quotient.field (Ideal.span {s})
  rw [← ker_residue s h]
  exact RingHom.ker_isMaximal_of_surjective _ (residue_surjective s h)

/-- For the node of thickness `s`, the closed point is `(u, v)`. -/
theorem closedPoint_self : closedPoint s s = Ideal.span {u s, v s} := by
  refine le_antisymm ?_ (Ideal.span_mono (Set.insert_subset_insert (by simp)))
  rw [closedPoint, Ideal.span_le]
  rintro y (rfl | rfl | rfl)
  · exact Ideal.subset_span (by simp)
  · exact Ideal.subset_span (by simp)
  · rw [SetLike.mem_coe, ← u_mul_v]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

end Residue

section Branch

variable (s : O)

/-- The map `Node O s → (O ⧸ (s))[Y]`, `u ↦ 0`, `v ↦ Y`: the restriction to the branch
`u = 0` of the special fibre of the node of thickness `s`. -/
noncomputable def branch : Node O s →ₐ[O] (O ⧸ Ideal.span {s})[X] :=
  lift 0 X (by
    rw [zero_mul, eq_comm, Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self s), map_zero])

@[simp] lemma branch_u : branch s (u s) = 0 := lift_u ..

@[simp] lemma branch_v : branch s (v s) = X := lift_v ..

/-- Every element of the node of thickness `s` is a polynomial in `v` modulo `(u)`. -/
lemma exists_sub_aeval_mem (x : Node O s) :
    ∃ p : O[X], x - aeval (v s) p ∈ Ideal.span {u s} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨C r, ?_⟩
    rw [aeval_C, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, sub_self]
    exact zero_mem _
  | add p q hp hq =>
    obtain ⟨c, hc⟩ := hp
    obtain ⟨d, hd⟩ := hq
    refine ⟨c + d, ?_⟩
    convert add_mem hc hd using 1
    rw [map_add, map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨c, hc⟩ := hp
    rw [map_mul]
    fin_cases i
    · exact ⟨0, by
        rw [map_zero, sub_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩
    · refine ⟨c * X, ?_⟩
      have : (Ideal.Quotient.mk _ (MvPolynomial.X 1) : Node O s) = v s := rfl
      convert Ideal.mul_mem_right (v s) _ hc using 1
      simp only [Fin.mk_one, this, map_mul, aeval_X]
      ring

lemma aeval_X_eq_map (p : O[X]) :
    aeval (X : (O ⧸ Ideal.span {s})[X]) p = p.map (algebraMap O (O ⧸ Ideal.span {s})) := by
  induction p using Polynomial.induction_on with
  | C r => simp [Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n r _ => simp [Polynomial.algebraMap_apply]

/-- The branch `u = 0`: the kernel of `Node O s → (O ⧸ (s))[Y]` is `(u)`. -/
theorem ker_branch : RingHom.ker (branch s) = Ideal.span {u s} := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨p, hp⟩ := exists_sub_aeval_mem s x
    have h1 : branch s (aeval (v s) p) = 0 := by
      have := RingHom.mem_ker.mp hx
      have h2 : branch s (x - aeval (v s) p) = 0 := by
        obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hp
        rw [← hy, map_mul, branch_u, mul_zero]
      rwa [map_sub, this, zero_sub, neg_eq_zero] at h2
    rw [← aeval_algHom_apply, branch_v, aeval_X_eq_map, ← Polynomial.coe_mapRingHom,
      ← RingHom.mem_ker, Polynomial.ker_mapRingHom, Ideal.Quotient.algebraMap_eq,
      Ideal.mk_ker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h1
    obtain ⟨q, rfl⟩ := h1
    have : x = (x - aeval (v s) (C s * q)) + u s * (v s * aeval (v s) q) := by
      rw [map_mul, aeval_C, ← u_mul_v]; ring
    rw [this]
    exact add_mem hp (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, branch_u]

/-- If `(s)` is prime, the branch `(u)` of the node of thickness `s` is a prime ideal. -/
theorem isPrime_span_u [(Ideal.span {s}).IsPrime] : (Ideal.span {u s}).IsPrime := by
  rw [← ker_branch]
  exact RingHom.ker_isPrime _

/-- If `s` is not a unit, `v ∉ (u)` in the node of thickness `s`. -/
theorem v_notMem_span_u [Nontrivial (O ⧸ Ideal.span {s})] : v s ∉ Ideal.span {u s} := by
  rw [← ker_branch, RingHom.mem_ker, branch_v]
  exact X_ne_zero

end Branch

section Kummer

variable (s : O) {M : ℕ}

lemma residue_comp_kummer (hM : 0 < M) :
    (residue s (dvd_refl s)).comp (kummer s M) = residue s (dvd_pow_self s hM.ne') := by
  refine algHom_ext ?_ ?_
  · rw [AlgHom.comp_apply, kummer_u, map_pow]
    simp [residue, zero_pow hM.ne']
  · rw [AlgHom.comp_apply, kummer_v, map_pow]
    simp [residue, zero_pow hM.ne']

/-- **The Kummer map pulls back the closed point to the closed point**: under
`Node O (s ^ M) → Node O s`, `u ↦ u ^ M`, `v ↦ v ^ M`, the preimage of `(u, v)` is
`(u, v, s)`. -/
theorem comap_kummer_closedPoint (hM : 0 < M) :
    (closedPoint s s).comap (kummer s M) = closedPoint s (s ^ M) := by
  rw [← ker_residue s (dvd_refl s), ← ker_residue s (dvd_pow_self s hM.ne'),
    ← residue_comp_kummer s hM]
  ext x
  simp [RingHom.mem_ker]

/-- **The punctured spectra correspond**: if `(s)` is maximal, the only prime of `Node O s` over
the closed point of `Node O (s ^ M)` (via the Kummer map) is the closed point `(u, v)`. -/
theorem eq_closedPoint_of_comap_kummer [(Ideal.span {s}).IsMaximal]
    (Q : Ideal (Node O s)) [Q.IsPrime] (hQ : Q.comap (kummer s M) = closedPoint s (s ^ M)) :
    Q = closedPoint s s := by
  have hle : closedPoint s s ≤ Q := by
    rw [closedPoint_self, Ideal.span_le]
    rintro y (rfl | rfl)
    · have : kummer s M (u (s ^ M)) ∈ Q := by
        rw [← Ideal.mem_comap, hQ]; exact u_mem_closedPoint s
      rw [kummer_u] at this
      exact Ideal.IsPrime.mem_of_pow_mem inferInstance _ this
    · have : kummer s M (v (s ^ M)) ∈ Q := by
        rw [← Ideal.mem_comap, hQ]; exact v_mem_closedPoint s
      rw [kummer_v] at this
      exact Ideal.IsPrime.mem_of_pow_mem inferInstance _ this
  exact ((isMaximal_closedPoint s (dvd_refl s)).eq_of_le
    (Ideal.IsPrime.ne_top ‹Q.IsPrime›) hle).symm

/-- A prime of `Node O s` other than the closed point lies over a prime of `Node O (s ^ M)`
other than the closed point: the Kummer map sends the punctured spectrum `W₁` to `W_M`. -/
theorem comap_kummer_ne_closedPoint [(Ideal.span {s}).IsMaximal]
    (Q : Ideal (Node O s)) [Q.IsPrime] (hQ : Q ≠ closedPoint s s) :
    Q.comap (kummer s M) ≠ closedPoint s (s ^ M) :=
  fun h ↦ hQ (eq_closedPoint_of_comap_kummer s Q h)

end Kummer

namespace ThicknessOne

/-! ### The local ring `R₁` of the node of thickness one at its closed point -/

variable {s : O} (R : Type*) [CommRing R] [Algebra (Node O s) R] [(closedPoint s s).IsPrime]
  [IsLocalization.AtPrime R (closedPoint s s)]

omit [(closedPoint s s).IsPrime] [IsLocalization.AtPrime R (closedPoint s s)] in
lemma isMaximal_span [IsDomain O] [IsDiscreteValuationRing O] (hs : Irreducible s) :
    (Ideal.span {s}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible hs

include s in
lemma isLocalRing : IsLocalRing R :=
  IsLocalization.AtPrime.isLocalRing R (closedPoint s s)

/-- `R₁` is a domain. -/
theorem isDomain [IsDomain O] (hs : s ≠ 0) : IsDomain R := by
  have := Node.isDomain hs
  exact IsLocalization.isDomain_of_atPrime R (closedPoint s s)

include s in
/-- `R₁` is Noetherian. -/
theorem isNoetherianRing [IsNoetherianRing O] : IsNoetherianRing R :=
  IsLocalization.isNoetherianRing (closedPoint s s).primeCompl R inferInstance

/-- `R₁` is integrally closed. -/
theorem isIntegrallyClosed [IsDomain O] [IsIntegrallyClosed O] (hs : s ≠ 0) :
    IsIntegrallyClosed R := by
  have := Node.isDomain hs
  have := Node.isIntegrallyClosed hs
  exact isIntegrallyClosed_of_isLocalization R (closedPoint s s).primeCompl
    (closedPoint s s).primeCompl_le_nonZeroDivisors

/-- The maximal ideal of `R₁` is `(u, v)`. -/
theorem maximalIdeal_eq :
    letI := isLocalRing (s := s) R
    maximalIdeal R = Ideal.span {algebraMap (Node O s) R (u s), algebraMap (Node O s) R (v s)} := by
  letI := isLocalRing (s := s) R
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (closedPoint s s) R, closedPoint_self,
    Ideal.map_span, Set.image_pair]

omit [(closedPoint s s).IsPrime] in
lemma span_u_le : Ideal.span {u s} ≤ closedPoint s s := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact u_mem_closedPoint s

omit [IsLocalization.AtPrime R (closedPoint s s)] in
lemma disjoint_span_u :
    Disjoint ((closedPoint s s).primeCompl : Set (Node O s)) (Ideal.span {u s}) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  exact hy (span_u_le hy')

variable [IsDomain O] [IsDiscreteValuationRing O]

/-- In `R₁`, the coordinate `u` is a prime element. -/
theorem prime_u (hs : Irreducible s) : Prime (algebraMap (Node O s) R (u s)) := by
  have := (isMaximal_span hs).isPrime
  have := isPrime_span_u s
  have := Node.isDomain hs.ne_zero
  have := isDomain R hs.ne_zero
  have hP := IsLocalization.isPrime_of_isPrime_disjoint (closedPoint s s).primeCompl R _
    inferInstance (disjoint_span_u (s := s))
  rw [Ideal.map_span, Set.image_singleton] at hP
  refine (Ideal.span_singleton_prime ?_).mp hP
  have hu : u s ≠ 0 := fun h ↦ by
    have := laurent_u s 1
    rw [h, map_zero] at this
    exact (LaurentPolynomial.isUnit_T 1).ne_zero this.symm
  exact fun h ↦ hu (IsLocalization.injective R (closedPoint s s).primeCompl_le_nonZeroDivisors
    (h.trans (map_zero _).symm))

/-- In `R₁`, `v ∉ (u)`. -/
theorem v_notMem_span_u (hs : Irreducible s) :
    algebraMap (Node O s) R (v s) ∉ Ideal.span {algebraMap (Node O s) R (u s)} := by
  have := (isMaximal_span hs).isPrime
  have := isPrime_span_u s
  intro h
  have h' : v s ∈ (Ideal.map (algebraMap (Node O s) R) (Ideal.span {u s})).under (Node O s) := by
    rw [Ideal.under, Ideal.mem_comap, Ideal.map_span, Set.image_singleton]
    exact h
  rw [IsLocalization.under_map_of_isPrime_disjoint (closedPoint s s).primeCompl R inferInstance
    (disjoint_span_u (s := s))] at h'
  exact Node.v_notMem_span_u s h'

end ThicknessOne

end SemistableReduction.Node
