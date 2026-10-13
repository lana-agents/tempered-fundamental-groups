/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Adic completeness of finite free algebras (Blueprint §12.8, M2.2)

Let `A` be `I`-adically complete and `B` an `A`-algebra which is finite free as an `A`-module.
Then `B` is `IB`-adically complete (`isAdicComplete_map`), so `(B, IB)` is a Henselian pair
(`IsAdicComplete.henselianRing`).

* `mem_pow_smul_top_iff`: for a basis `b`, `x ∈ I^n • ⊤` iff every coordinate of `x` lies in
  `I^n`;
* `isAdicComplete_of_basis`: `B` is `I`-adically complete as an `A`-module;
* `mem_map_pow_iff`: `(IB)^n • ⊤ = I^n • ⊤` (as sets), so the two adic topologies agree;
* **`isAdicComplete_map`**.
-/

namespace SemistableReduction

namespace CompleteFree

variable {A : Type*} [CommRing A] (I : Ideal A)

section Module

variable {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*} [Finite ι] (b : Module.Basis ι A M)

/-- **Membership in `I^n • ⊤` is coordinatewise.** -/
theorem mem_smul_top_iff (J : Ideal A) (x : M) :
    x ∈ J • (⊤ : Submodule A M) ↔ ∀ i, b.repr x i ∈ J := by
  cases nonempty_fintype ι
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun y => b.repr y i ∈ J) hx ?_ ?_
    · intro a ha m _
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ ha
    · intro x y hx hy
      rw [map_add, Finsupp.add_apply]
      exact J.add_mem hx hy
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

lemma mem_pow_smul_top_iff (n : ℕ) (x : M) :
    x ∈ (I ^ n • ⊤ : Submodule A M) ↔ ∀ i, b.repr x i ∈ I ^ n :=
  mem_smul_top_iff b (I ^ n) x

lemma mem_pow_smul_top_self_iff (n : ℕ) (a : A) : a ∈ (I ^ n • ⊤ : Submodule A A) ↔ a ∈ I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

variable [IsAdicComplete I A]

include b in
/-- **A finite free module over an `I`-adically complete ring is `I`-adically complete.** -/
theorem isAdicComplete_of_basis : IsAdicComplete I M := by
  cases nonempty_fintype ι
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hc : ∀ i, b.repr x i = 0 := fun i =>
      IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I))
      (b.repr x i) fun n => by
        rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top_self_iff]
        have := hx n
        rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top_iff I b] at this
        exact this i
    rw [← b.sum_repr x]
    simp [hc]
  · intro f hf
    have hcoord : ∀ i, ∃ L : A, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] := by
      intro i
      refine IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := I)) fun {m n} hmn => ?_
      rw [SModEq.sub_mem, mem_pow_smul_top_self_iff]
      have := hf hmn
      rw [SModEq.sub_mem, mem_pow_smul_top_iff I b] at this
      have h := this i
      rwa [map_sub, Finsupp.sub_apply] at h
    choose L hL using hcoord
    refine ⟨∑ i, L i • b i, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_pow_smul_top_iff I b]
    intro i
    have h := hL i n
    rw [SModEq.sub_mem, mem_pow_smul_top_self_iff] at h
    have hs : ∑ c, (Finsupp.single c (L c) : ι →₀ A) i = L i := by
      rw [Finset.sum_eq_single (f := fun c => (Finsupp.single c (L c) : ι →₀ A) i) i
        (fun c _ hc => by simp [hc])
        (fun h => absurd (Finset.mem_univ i) h)]
      simp
    simpa [map_sub, Finsupp.sub_apply, b.repr_self, hs] using h

end Module

section Algebra

variable {B : Type*} [CommRing B] [Algebra A B]

/-- **The `IB`-adic and the `I`-adic topologies on `B` agree.** -/
lemma mem_map_pow_iff (n : ℕ) (x : B) :
    x ∈ ((I.map (algebraMap A B)) ^ n • ⊤ : Submodule B B) ↔ x ∈ (I ^ n • ⊤ : Submodule A B) := by
  rw [smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow, Ideal.smul_top_eq_map]
  rfl

variable {ι : Type*} [Finite ι] (b : Module.Basis ι A B) [IsAdicComplete I A]

include b in
/-- **A finite free algebra over an `I`-adically complete ring is `IB`-adically complete.** -/
theorem isAdicComplete_map : IsAdicComplete (I.map (algebraMap A B)) B := by
  have h := isAdicComplete_of_basis I b
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    refine IsHausdorff.haus h.toIsHausdorff x fun n => ?_
    have := hx n
    rw [SModEq.sub_mem, sub_zero, mem_map_pow_iff] at this
    rwa [SModEq.sub_mem, sub_zero]
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete fun {m n} hmn => by
      have := hf hmn
      rw [SModEq.sub_mem, mem_map_pow_iff] at this
      rwa [SModEq.sub_mem]
    refine ⟨L, fun n => ?_⟩
    have := hL n
    rw [SModEq.sub_mem] at this
    rwa [SModEq.sub_mem, mem_map_pow_iff]

end Algebra

end CompleteFree

end SemistableReduction
