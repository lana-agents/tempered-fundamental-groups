/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Tactic.LinearCombination

/-!
# Formal glueing of algebras along `f` (generic commutative algebra)

This file is **generic commutative algebra** (it imports only Mathlib and is independent of the rest
of the project). It provides the formal glueing (Beauville–Laszlo type) needed at the nodes in the
formal patching step M2.3 of Blueprint §12.8: the local model of an admissible covering at a node is
the Kummer covering only after completion at the node, so the covering near the node is glued from
an algebra over the punctured neighbourhood `D(f)` and an algebra over the completion.

Let `R → S` be flat, `f ∈ R`, such that `R → S/fᵏS` is surjective for every `k` (e.g. `S` the
`f`-adic completion of a Noetherian ring `R`). Glueing data: an `R`-algebra `P` on which `f` is
invertible (an algebra over `R_f`), an `S`-algebra `N` on which `f` is a nonzerodivisor, and an
algebra `Q` which is at the same time the localization `N_f` (via `algebraMap N Q`) and the base
change `S ⊗_R P` (via `α : P → Q`, `IsBaseChange S α`). The glued algebra is the fibre product
`P ×_Q N` (`FormalGlueing.glued`). Results:

* **`FormalGlueing.isLocalization_fst`**: `P` is the localization of the glued algebra away from
  `f` (no hypothesis on `S` needed);
* **`FormalGlueing.isBaseChange_snd`**: `N` is the base change of the glued algebra along `R → S`.

This is the essential surjectivity half of Stacks, Theorem 15.91.18 (Tag 05ES:
`Mod_R ≃ Mod_S ×_{Mod_{S_f}} Mod_{R_f}` for `R → S` flat with `R/fR ≅ S/fS`), in the case of
algebras with `f`-torsion-free `N`; the Noetherian completion case is Stacks, Proposition 15.91.19
(Tag 05ET). The proof here is elementwise and different from the one in Stacks: with
`M = P ×_Q N` and `ψ : S ⊗_R M → N`,
1. `Q = α(P) + N` (as `S = R + fᵏS` and `fᵏ α(p) ∈ N` for large `k`), hence `M/fM ≅ N/fN`;
2. `ψ` becomes an isomorphism after inverting `f` (`(S ⊗ M)_f = S ⊗ P = Q`), so `ker ψ` is
   `f`-power torsion, hence zero (`S ⊗ M` is `f`-torsion free as `S` is flat);
3. `coker ψ` is `f`-power torsion, and `f n ∈ im ψ ⇒ n ∈ im ψ` by step 1 (using `S = R + fS`),
   so `ψ` is onto.
-/

namespace FormalGlueing

open TensorProduct

variable {R : Type*} [CommRing R] (f : R)
  {P : Type*} [CommRing P] [Algebra R P]
  (N : Type*) [CommRing N] [Algebra R N]
  {Q : Type*} [CommRing Q] [Algebra R Q] [Algebra N Q] [IsScalarTower R N Q]
  (α : P →ₐ[R] Q)

/-- The **glued algebra** `P ×_Q N`. -/
def glued : Subalgebra R (P × N) :=
  AlgHom.equalizer (α.comp (AlgHom.fst R P N))
    ((IsScalarTower.toAlgHom R N Q).comp (AlgHom.snd R P N))

lemma mem_glued {x : P × N} : x ∈ glued N α ↔ α x.1 = algebraMap N Q x.2 := Iff.rfl

/-- The projection of the glued algebra to `P`. -/
def fst : glued N α →ₐ[R] P := (AlgHom.fst R P N).comp (glued N α).val

/-- The projection of the glued algebra to `N`. -/
def snd : glued N α →ₐ[R] N := (AlgHom.snd R P N).comp (glued N α).val

@[simp] lemma fst_apply (x : glued N α) : fst N α x = x.1.1 := rfl
@[simp] lemma snd_apply (x : glued N α) : snd N α x = x.1.2 := rfl

lemma algebraMap_glued_fst (r : R) : (algebraMap R (glued N α) r).1.1 = algebraMap R P r := rfl
lemma algebraMap_glued_snd (r : R) : (algebraMap R (glued N α) r).1.2 = algebraMap R N r := rfl

lemma algebraMap_N_Q (r : R) : algebraMap N Q (algebraMap R N r) = algebraMap R Q r :=
  (IsScalarTower.algebraMap_apply R N Q r).symm

variable [IsLocalization.Away (algebraMap R N f) Q]

/-- The algebra structure of `P` over the glued algebra (via `fst`). -/
@[reducible] def algebraFst : Algebra (glued N α) P := (fst N α).toRingHom.toAlgebra

/-- **Formal glueing, the `D(f)` side**: `P` is the localization of `P ×_Q N` away from `f`. -/
theorem isLocalization_fst (hfP : IsUnit (algebraMap R P f)) :
    letI := algebraFst N α
    IsLocalization.Away (algebraMap R (glued N α) f) P := by
  letI := algebraFst N α
  have hm : ∀ x : glued N α, algebraMap (glued N α) P x = x.1.1 := fun _ ↦ rfl
  refine (isLocalization_iff ..).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    simpa [hm] using hfP.pow k
  · intro p
    obtain ⟨⟨n, ⟨_, k, rfl⟩⟩, hn⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap R N f)) (α p)
    simp only [map_pow, algebraMap_N_Q] at hn
    refine ⟨⟨⟨(p * algebraMap R P f ^ k, n), ?_⟩, ⟨_, k, rfl⟩⟩, ?_⟩
    · rw [mem_glued]
      simp [hn]
    · simp [hm]
  · intro x y hxy
    have h0 : (x - y).1.1 = 0 := by simpa [hm, sub_eq_zero] using hxy
    have hQ : algebraMap N Q (x - y).1.2 = 0 := by rw [← (mem_glued N α).mp (x - y).2, h0, map_zero]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (algebraMap R N f)) Q _).mp hQ
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change algebraMap R P f ^ k * ((x : P × N).1 - (y : P × N).1) = 0
      rw [show (x : P × N).1 - (y : P × N).1 = 0 from h0, mul_zero]
    · simpa using hk

variable (S : Type*) [CommRing S] [Algebra R S] [Algebra S N] [IsScalarTower R S N]
  [Algebra S Q] [IsScalarTower R S Q] [IsScalarTower S N Q]

section BaseChange

variable {f}
variable (hfP : IsUnit (algebraMap R P f))
  (hS : ∀ (k : ℕ) (s : S), ∃ (r : R) (t : S), s = algebraMap R S r + algebraMap R S f ^ k * t)
  (hN : ∀ n : N, algebraMap R N f * n = 0 → n = 0)
  (hα : IsBaseChange S α.toLinearMap)

include hS hα in
/-- Every element of `Q = N_f = S ⊗_R P` is a sum of an element of `P` and one of `N`. -/
lemma exists_eq_add (q : Q) : ∃ (p : P) (n : N), q = α p + algebraMap N Q n := by
  refine hα.inductionOn q _ ⟨0, 0, by simp⟩ (fun p ↦ ⟨p, 0, by simp⟩) ?_ ?_
  · rintro s _ ⟨p, n, rfl⟩
    obtain ⟨⟨n₀, ⟨_, k, rfl⟩⟩, hn₀⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap R N f)) (α p)
    simp only [map_pow, algebraMap_N_Q] at hn₀
    obtain ⟨r, t, rfl⟩ := hS k s
    refine ⟨r • p, t • n₀ + (algebraMap R S r + algebraMap R S f ^ k * t) • n, ?_⟩
    rw [map_smul]
    simp only [Algebra.smul_def, map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    rw [← hn₀]
    ring
  · rintro _ _ ⟨p, n, rfl⟩ ⟨p', n', rfl⟩
    exact ⟨p + p', n + n', by simp only [map_add]; ring⟩

include hfP hS hα in
/-- `M/fM → N/fN` is onto. -/
lemma exists_snd_eq (n : N) : ∃ (x : glued N α) (n' : N), x.1.2 = n + algebraMap R N f * n' := by
  obtain ⟨u, hu⟩ := hfP.exists_left_inv
  have hfQ : IsUnit (algebraMap R Q f) := by
    rw [← algebraMap_N_Q N]
    exact IsLocalization.map_units Q (⟨_, 1, pow_one _⟩ : Submonoid.powers (algebraMap R N f))
  obtain ⟨v, hv⟩ := hfQ.exists_left_inv
  obtain ⟨p, m, hpm⟩ := exists_eq_add N α S hS hα (v * algebraMap N Q n)
  refine ⟨⟨(algebraMap R P f * p, n - algebraMap R N f * m), ?_⟩, -m, by ring⟩
  rw [mem_glued]
  have : algebraMap N Q n = algebraMap R Q f * (α p + algebraMap N Q m) := by
    rw [← hpm, ← mul_assoc, mul_comm _ v, hv, one_mul]
  simp only [map_mul, AlgHom.commutes, map_sub, algebraMap_N_Q, this]
  ring

omit [IsLocalization.Away (algebraMap R N f) Q] in
include hfP in
/-- `M/fM → N/fN` is injective. -/
lemma exists_eq_smul (x : glued N α) (n' : N) (hx : x.1.2 = algebraMap R N f * n') :
    ∃ y : glued N α, x = algebraMap R (glued N α) f * y := by
  obtain ⟨u, hu⟩ := hfP.exists_left_inv
  refine ⟨⟨(u * x.1.1, n'), ?_⟩, ?_⟩
  · rw [mem_glued]
    have h := (mem_glued N α).mp x.2
    rw [hx, map_mul, algebraMap_N_Q] at h
    have hfQ : α (algebraMap R P f) = algebraMap R Q f := α.commutes f
    calc α (u * x.1.1) = α u * α x.1.1 := map_mul _ _ _
      _ = α u * (algebraMap R Q f * algebraMap N Q n') := by rw [h]
      _ = α (u * algebraMap R P f) * algebraMap N Q n' := by rw [map_mul, hfQ]; ring
      _ = algebraMap N Q n' := by rw [hu, map_one, one_mul]
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · change x.1.1 = algebraMap R P f * (u * x.1.1)
      rw [← mul_assoc, mul_comm _ u, hu, one_mul]
    · exact hx

omit [IsLocalization.Away (algebraMap R N f) Q] in
include hfP hN in
/-- The glued algebra is `f`-torsion free. -/
lemma glued_torsionFree (x : glued N α) (hx : algebraMap R (glued N α) f * x = 0) : x = 0 := by
  have h1 : algebraMap R P f * x.1.1 = 0 := congrArg (fun y : glued N α ↦ y.1.1) hx
  have h2 : algebraMap R N f * x.1.2 = 0 := congrArg (fun y : glued N α ↦ y.1.2) hx
  refine Subtype.ext (Prod.ext ?_ (hN _ h2))
  simpa using (hfP.mul_right_eq_zero).mp h1

/-- The comparison map `S ⊗_R (P ×_Q N) → N`. -/
noncomputable def psi : S ⊗[R] glued N α →ₗ[S] N := (snd N α).toLinearMap.liftBaseChange S

omit [Algebra S Q] [IsScalarTower R S Q] [IsScalarTower S N Q] in
@[simp] lemma psi_tmul (s : S) (x : glued N α) : psi N α S (s ⊗ₜ x) = s • x.1.2 := rfl

omit [IsLocalization.Away (algebraMap R N f) Q] [Algebra S N] [IsScalarTower R S N] [Algebra S Q]
  [IsScalarTower R S Q] [IsScalarTower S N Q] in
include hS in
/-- Every element of `S ⊗_R M` is `1 ⊗ m + f z`. -/
lemma exists_tmul_add (z : S ⊗[R] glued N α) :
    ∃ (m : glued N α) (z' : S ⊗[R] glued N α), z = 1 ⊗ₜ m + f • z' := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul s m =>
    obtain ⟨r, t, rfl⟩ := hS 1 s
    refine ⟨r • m, t ⊗ₜ m, ?_⟩
    rw [add_tmul, tmul_smul, pow_one, smul_tmul', smul_tmul', Algebra.smul_def f t,
      ← Algebra.algebraMap_eq_smul_one]
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨m₁, z₁', rfl⟩ := h₁
    obtain ⟨m₂, z₂', rfl⟩ := h₂
    exact ⟨m₁ + m₂, z₁' + z₂', by rw [tmul_add, smul_add]; abel⟩

omit [IsLocalization.Away (algebraMap R N f) Q] [Algebra S N] [IsScalarTower R S N] [Algebra S Q]
  [IsScalarTower R S Q] [IsScalarTower S N Q] in
include hfP hN in
/-- `S ⊗_R M` is `f`-torsion free (`S` flat). -/
lemma tensor_torsionFree [Module.Flat R S] (z : S ⊗[R] glued N α) (k : ℕ)
    (hz : f ^ k • z = 0) : z = 0 := by
  have hinj : Function.Injective (LinearMap.lsmul R (glued N α) f) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact glued_torsionFree N α hfP hN x (by rw [← Algebra.smul_def]; exact hx)
  have hl : ∀ w : S ⊗[R] glued N α,
      LinearMap.lTensor S (LinearMap.lsmul R (glued N α) f) w = f • w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s x => simp [tmul_smul]
    | add a b ha hb => rw [map_add, ha, hb, smul_add]
  have h1 : ∀ w : S ⊗[R] glued N α, f • w = 0 → w = 0 := by
    intro w hw
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := S) _ hinj
    rw [hl, map_zero, hw]
  induction k generalizing z with
  | zero => simpa using hz
  | succ k ih => exact h1 _ (ih _ (by rwa [smul_smul, ← pow_succ]))

lemma algebraMap_smul_N (s : S) (n : N) :
    algebraMap N Q (s • n) = s • algebraMap N Q n := by
  simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

include hfP hS hN hα in
/-- **The comparison map `S ⊗_R (P ×_Q N) → N` is bijective.** -/
theorem psi_bijective [Module.Flat R S] : Function.Bijective (psi N α S) := by
  letI := algebraFst N α
  haveI : IsScalarTower R (glued N α) P :=
    IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  haveI hloc : IsLocalizedModule (Submonoid.powers f) (fst N α).toLinearMap := by
    haveI : IsLocalization (Algebra.algebraMapSubmonoid (glued N α) (Submonoid.powers f)) P := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      exact isLocalization_fst f N α hfP
    exact isLocalizedModule_iff_isLocalization.mpr this
  let g := AlgebraTensorModule.rTensor R S (fst N α).toLinearMap
  haveI : IsLocalizedModule (Submonoid.powers f) g := by dsimp only [g]; infer_instance
  -- the comparison `S ⊗ M → S ⊗ P ≅ Q` is `β ∘ ψ`
  have key : ∀ z : S ⊗[R] glued N α, hα.equiv (TensorProduct.comm R P S
      (g (TensorProduct.comm R S (glued N α) z))) = algebraMap N Q (psi N α S z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      simp [g, IsBaseChange.equiv_tmul, algebraMap_smul_N, (mem_glued N α).mp x.2]
    | add a b ha hb => simp only [map_add, ha, hb]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : g (TensorProduct.comm R S (glued N α) z) = 0 := by
      have := key z
      rw [hz, map_zero] at this
      simpa using this
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) g).mp h1
    refine tensor_torsionFree N α S hfP hN z k ?_
    apply (TensorProduct.comm R S (glued N α)).injective
    rw [map_smul, map_zero]
    exact hk
  · have F1 : ∀ n : N, ∃ (z : S ⊗[R] glued N α) (k : ℕ),
        psi N α S z = algebraMap R N f ^ k * n := by
      intro n
      obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers f) g
        (TensorProduct.comm R S P (hα.equiv.symm (algebraMap N Q n)))
      have h2 : algebraMap N Q (psi N α S (TensorProduct.comm R (glued N α) S x)) =
          algebraMap N Q (algebraMap R N f ^ k * n) := by
        rw [← key, show TensorProduct.comm R S (glued N α) (TensorProduct.comm R (glued N α) S x)
          = x by simp, ← hx]
        rw [Submonoid.smul_def, map_smul, ← algebraMap_smul S (f ^ k), map_smul]
        simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      rw [← sub_eq_zero, ← map_sub] at h2
      obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff
        (Submonoid.powers (algebraMap R N f)) Q _).mp h2
      refine ⟨f ^ j • TensorProduct.comm R (glued N α) S x, j + k, ?_⟩
      rw [LinearMap.map_smul_of_tower, Algebra.smul_def, map_pow]
      simp only at hj
      rw [mul_sub, sub_eq_zero] at hj
      rw [hj, pow_add, mul_assoc]
    have F2 : ∀ n : N, (∃ z, psi N α S z = algebraMap R N f * n) → ∃ z, psi N α S z = n := by
      rintro n ⟨z, hz⟩
      obtain ⟨m, z', rfl⟩ := exists_tmul_add N α S hS z
      rw [map_add, psi_tmul, one_smul, LinearMap.map_smul_of_tower, Algebra.smul_def] at hz
      obtain ⟨y, hy⟩ := exists_eq_smul N α hfP m (n - psi N α S z') (by linear_combination hz)
      have hy2 : m.1.2 = algebraMap R N f * y.1.2 := by rw [hy]; rfl
      refine ⟨1 ⊗ₜ y + z', ?_⟩
      rw [map_add, psi_tmul, one_smul]
      have := hN (y.1.2 + psi N α S z' - n) (by linear_combination hz - hy2)
      linear_combination this
    have F : ∀ (k : ℕ) (n : N), (∃ z, psi N α S z = algebraMap R N f ^ k * n) →
        ∃ z, psi N α S z = n := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro n hn
        rw [pow_succ, mul_assoc] at hn
        exact F2 n (ih _ hn)
    intro n
    obtain ⟨z, k, hz⟩ := F1 n
    exact F k n ⟨z, hz⟩

include hfP hS hN hα in
/-- **Formal glueing, the completion side**: `N` is the base change of the glued algebra
`P ×_Q N` along `R → S`. -/
theorem isBaseChange_snd [Module.Flat R S] : IsBaseChange S (snd N α).toLinearMap :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective (psi N α S) (psi_bijective N α S hfP hS hN hα))
    fun x ↦ by simp


end BaseChange

section Completion

omit [IsLocalization.Away (algebraMap R N f) Q] in
/-- In the `f`-adic completion, `S = R + fᵏ S` for every `k`. -/
lemma completion_eq_add (k : ℕ) (s : AdicCompletion (Ideal.span {f}) R) :
    ∃ (r : R) (t : AdicCompletion (Ideal.span {f}) R),
      s = algebraMap R _ r + algebraMap R _ f ^ k * t := by
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {f}) R k s)
  have hmem : s - algebraMap R _ r ∈ (Ideal.span {f}) ^ k • (⊤ : Submodule R
      (AdicCompletion (Ideal.span {f}) R)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton f), LinearMap.mem_ker,
      map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AdicCompletion.eval_of, ← hr, Submodule.mkQ_apply, sub_self]
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨t, -, ht⟩ := hmem
  refine ⟨r, t, ?_⟩
  rw [← map_pow, ← Algebra.smul_def, ht, add_sub_cancel]

variable [IsNoetherianRing R] [Algebra (AdicCompletion (Ideal.span {f}) R) N]
  [IsScalarTower R (AdicCompletion (Ideal.span {f}) R) N]
  [Algebra (AdicCompletion (Ideal.span {f}) R) Q]
  [IsScalarTower R (AdicCompletion (Ideal.span {f}) R) Q]
  [IsScalarTower (AdicCompletion (Ideal.span {f}) R) N Q]

/-- **Formal glueing over a Noetherian ring** (cf. Stacks, Proposition 15.91.19, Tag 05ET): for
`R` Noetherian, `R̂` its `f`-adic completion, `P` an `R_f`-algebra, `N` an `R̂`-algebra without
`f`-torsion and `Q = N_f = R̂ ⊗_R P`, the fibre product `P ×_Q N` localizes to `P` away from `f`
(`isLocalization_fst`) and its base change to `R̂` is `N`. -/
theorem isBaseChange_snd_completion (hfP : IsUnit (algebraMap R P f))
    (hN : ∀ n : N, algebraMap R N f * n = 0 → n = 0)
    (hα : IsBaseChange (AdicCompletion (Ideal.span {f}) R) α.toLinearMap) :
    IsBaseChange (AdicCompletion (Ideal.span {f}) R) (snd N α).toLinearMap :=
  isBaseChange_snd N α _ hfP (completion_eq_add f) hN hα

end Completion

end FormalGlueing
