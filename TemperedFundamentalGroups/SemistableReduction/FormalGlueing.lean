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
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Module.Torsion.Basic

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
* **`FormalGlueing.isBaseChange_snd`**: `N` is the base change of the glued algebra along `R → S`;
* **`FormalGlueing.finite_glued`**: if moreover `R/fᵏ → S/fᵏS` is injective, `P` is finite over
  `R_f` and `N` is finite over `S`, the glued algebra is a finite `R`-module (`S ⊗ (M/M') = 0` and
  flatness of `S` kill the `f`-power torsion of `M/M'`, cf. Stacks, Lemma 15.91.2, Tag 05E9);
* `FormalGlueing.isBaseChange_snd_completion`, `FormalGlueing.finite_glued_completion`: the case of
  the `f`-adic completion of a Noetherian ring.

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


section Finite

variable [Module.Flat R S]
  (hS' : ∀ (k : ℕ) (r : R) (t : S), algebraMap R S r = algebraMap R S f ^ k * t →
    ∃ r' : R, r = f ^ k * r')

omit [IsLocalization.Away (algebraMap R N f) Q] [Algebra S N] [IsScalarTower R S N] [Algebra S Q]
  [IsScalarTower R S Q] [IsScalarTower S N Q] in
include hS hS' in
/-- If the base change to `S` of a submodule `M'` of the glued algebra is everything, then
`M/M'` has no `f`-power torsion (flatness of `S` and `R/fᵏ ≅ S/fᵏ`). -/
lemma mem_of_pow_smul_mem (M' : Submodule R (glued N α))
    (hM' : ∀ z : S ⊗[R] glued N α,
      z ∈ LinearMap.range (AlgebraTensorModule.lTensor S S M'.subtype))
    (m : glued N α) (k : ℕ) (hm : f ^ k • m ∈ M') : m ∈ M' := by
  -- `S ⊗ (M ⧸ M') = 0`
  have hzero : ∀ y : S ⊗[R] (glued N α ⧸ M'), y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective S M'.mkQ_surjective y
    obtain ⟨x', hx'⟩ := hM' x
    rw [← hx']
    change (LinearMap.lTensor S M'.mkQ ∘ₗ LinearMap.lTensor S M'.subtype) x' = 0
    rw [← LinearMap.lTensor_comp, show M'.mkQ ∘ₗ M'.subtype = 0 from LinearMap.ext fun x ↦ by simp,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  set c := M'.mkQ m
  set J := Ideal.torsionOf R (glued N α ⧸ M') c
  have hfk : f ^ k ∈ J := by
    rw [Ideal.mem_torsionOf_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hm
  -- `S ⊗ R/J ↪ S ⊗ (M ⧸ M') = 0`
  let ι : (R ⧸ J) →ₗ[R] glued N α ⧸ M' :=
    (R ∙ c).subtype ∘ₗ (Ideal.quotTorsionOfEquivSpanSingleton R _ c).toLinearMap
  have hι : Function.Injective ι :=
    (Submodule.injective_subtype _).comp (LinearEquiv.injective _)
  have h1 : (1 : S) ⊗ₜ[R] (Ideal.Quotient.mk J 1) = 0 :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S) ι hι
      (by rw [map_zero]; exact hzero _)
  have h2 : (1 : S) ∈ J • (⊤ : Submodule R S) := by
    have := congrArg (tensorQuotEquivQuotSMul S J) h1
    rw [tensorQuotEquivQuotSMul_tmul_mk, map_zero, one_smul,
      Submodule.Quotient.mk_eq_zero] at this
    exact this
  -- `J S ⊆ J + fᵏ S`
  have h3 : ∀ x ∈ J • (⊤ : Submodule R S), ∃ a ∈ J, ∃ t : S,
      x = algebraMap R S a + algebraMap R S f ^ k * t := by
    intro x hx
    refine Submodule.smul_induction_on (p := fun x ↦ ∃ a ∈ J, ∃ t : S,
      x = algebraMap R S a + algebraMap R S f ^ k * t) hx ?_ ?_
    · intro a ha s _
      obtain ⟨r, t, rfl⟩ := hS k s
      exact ⟨a * r, J.mul_mem_right r ha, a • t, by
        simp only [Algebra.smul_def, map_mul]; ring⟩
    · rintro x y ⟨a, ha, t, rfl⟩ ⟨b, hb, t', rfl⟩
      exact ⟨a + b, J.add_mem ha hb, t + t', by simp only [map_add]; ring⟩
  obtain ⟨a, ha, t, hat⟩ := h3 1 h2
  obtain ⟨r', hr'⟩ := hS' k (1 - a) t (by rw [map_sub, map_one, hat]; ring)
  have hJ : (1 : R) ∈ J := by
    have : (1 : R) = a + f ^ k * r' := by rw [← hr']; ring
    rw [this]
    exact J.add_mem ha (J.mul_mem_right _ hfk)
  rw [Ideal.mem_torsionOf_iff, one_smul] at hJ
  exact (Submodule.Quotient.mk_eq_zero M').mp hJ

include hfP hS hN hα hS' in
/-- **Finiteness of the glued algebra**: if `P` is finite over `R_f` (in the form: finitely many
elements generate `P` up to powers of `f`) and `N` is finite over `S`, then `P ×_Q N` is a finite
`R`-module. -/
theorem finite_glued (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ,
      f ^ k • p ∈ Submodule.span R (s : Set P)) [Module.Finite S N] :
    Module.Finite R (glued N α) := by
  letI := algebraFst N α
  have hloc := isLocalization_fst f N α hfP
  have hψ := psi_bijective N α S hfP hS hN hα
  obtain ⟨s, hs⟩ := hP
  -- lifts of the generators of `P`
  have hlift : ∀ p : P, ∃ (x : glued N α) (j : ℕ), x.1.1 = f ^ j • p := by
    intro p
    obtain ⟨⟨x, ⟨_, j, rfl⟩⟩, hx⟩ := IsLocalization.surj
      (Submonoid.powers (algebraMap R (glued N α) f)) p
    refine ⟨x, j, ?_⟩
    change p * algebraMap R P f ^ j = x.1.1 at hx
    rw [← hx, Algebra.smul_def, map_pow, mul_comm]
  choose xP jP hxP using hlift
  -- the generators of `N`, as images of elementary tensors
  obtain ⟨n, gN, hgN⟩ := Module.Finite.exists_fin (R := S) (M := N)
  choose z hz using fun l : Fin n ↦ hψ.2 (gN l)
  choose kz sz mz hsz using fun l : Fin n ↦ TensorProduct.exists_sum_tmul_eq (z l)
  set G : Set (glued N α) := Set.range (fun p : s ↦ xP p) ∪
    Set.range (fun lj : Σ l, Fin (kz l) ↦ mz lj.1 lj.2) with hG
  have hGfin : G.Finite := (Set.finite_range _).union (Set.finite_range _)
  set M' := Submodule.span R G
  -- `S ⊗ M' → S ⊗ M` is onto
  have hM' : ∀ w : S ⊗[R] glued N α,
      w ∈ LinearMap.range (AlgebraTensorModule.lTensor S S M'.subtype) := by
    let V : Submodule S N :=
      (LinearMap.range (AlgebraTensorModule.lTensor S S M'.subtype)).map (psi N α S)
    have hV : V = ⊤ := by
      rw [eq_top_iff, ← hgN, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine ⟨z l, ⟨∑ j, sz l j ⊗ₜ ⟨mz l j, Submodule.subset_span (Or.inr ⟨⟨l, j⟩, rfl⟩)⟩, ?_⟩,
        hz l⟩
      simp [hsz l]
    intro w
    obtain ⟨w', hw', hw'w⟩ : psi N α S w ∈ V := hV ▸ Submodule.mem_top
    rwa [← hψ.1 hw'w]
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨G, hGfin, eq_top_iff.mpr fun m _ ↦ ?_⟩
  -- some `fᵏ m` lies in `M'`
  obtain ⟨k, hk⟩ := hs m.1.1
  have hspan : ∀ y ∈ Submodule.span R (s : Set P), ∃ y' ∈ M',
      y'.1.1 = f ^ (∑ p : s, jP p) • y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem p hp =>
      refine ⟨f ^ (∑ q : s, jP q - jP p) • xP p,
        M'.smul_mem _ (Submodule.subset_span (Or.inl ⟨⟨p, hp⟩, rfl⟩)), ?_⟩
      have hle : jP p ≤ ∑ q : s, jP q :=
        Finset.single_le_sum (f := fun q : s ↦ jP q) (by simp) (Finset.mem_univ ⟨p, hp⟩)
      change f ^ (∑ q : s, jP q - jP p) • (xP p).1.1 = _
      rw [hxP, smul_smul, ← pow_add, Nat.sub_add_cancel hle]
    | zero => exact ⟨0, M'.zero_mem, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', ha'e⟩ := ha
      obtain ⟨b', hb', hb'e⟩ := hb
      exact ⟨a' + b', M'.add_mem ha' hb', by simp [ha'e, hb'e]⟩
    | smul r a _ ha =>
      obtain ⟨a', ha', ha'e⟩ := ha
      exact ⟨r • a', M'.smul_mem r ha', by simp [ha'e, smul_comm r]⟩
  obtain ⟨y', hy', hy'e⟩ := hspan _ hk
  set K := (∑ p : s, jP p) + k
  have hmK : f ^ K • m = y' := by
    have hd1 : (f ^ K • m - y').1.1 = 0 := by
      change f ^ K • m.1.1 - y'.1.1 = 0
      rw [hy'e, smul_smul, ← pow_add, sub_self]
    have hdQ : algebraMap N Q (f ^ K • m - y').1.2 = 0 := by
      rw [← (mem_glued N α).mp (f ^ K • m - y').2, hd1, map_zero]
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (algebraMap R N f)) Q _).mp hdQ
    have hd2 : (f ^ K • m - y').1.2 = 0 := by
      simp only at hj
      clear hd1 hdQ
      induction j with
      | zero => simpa using hj
      | succ j ih => exact ih (hN _ (by rw [← mul_assoc, ← pow_succ']; exact hj))
    rw [← sub_eq_zero]
    exact Subtype.ext (Prod.ext hd1 hd2)
  exact mem_of_pow_smul_mem N α S hS hS' M' hM' m K (hmK ▸ hy')

end Finite

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

omit [IsLocalization.Away (algebraMap R N f) Q] in
/-- `R/fᵏ → R̂/fᵏR̂` is injective. -/
lemma completion_dvd (k : ℕ) (r : R) (t : AdicCompletion (Ideal.span {f}) R)
    (h : algebraMap R _ r = algebraMap R _ f ^ k * t) : ∃ r' : R, r = f ^ k * r' := by
  have h1 := congrArg (AdicCompletion.eval (Ideal.span {f}) R k) h
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.eval_of, ← map_pow, ← Algebra.smul_def, map_smul] at h1
  have h2 : f ^ k • AdicCompletion.eval (Ideal.span {f}) R k t = 0 := by
    obtain ⟨y, hy⟩ :=
      Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {f}) R k t)
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul
      (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _) Submodule.mem_top
  rw [h2, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨r', -, hr'⟩ := h1
  exact ⟨r', by rw [← hr', smul_eq_mul]⟩

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

/-- **Finiteness, Noetherian completion case**: the glued algebra of a finite `R_f`-algebra and a
finite `R̂`-algebra is a finite `R`-module. -/
theorem finite_glued_completion (hfP : IsUnit (algebraMap R P f))
    (hN : ∀ n : N, algebraMap R N f * n = 0 → n = 0)
    (hα : IsBaseChange (AdicCompletion (Ideal.span {f}) R) α.toLinearMap)
    (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P))
    [Module.Finite (AdicCompletion (Ideal.span {f}) R) N] : Module.Finite R (glued N α) :=
  finite_glued N α _ hfP (completion_eq_add f) hN hα (completion_dvd f) hP

end Completion

end FormalGlueing
