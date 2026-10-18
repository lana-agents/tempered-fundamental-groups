/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

/-!
# Inverse systems of rings from successor maps (Blueprint §12.8, M2.3/M2.4)

Given commutative rings `G n` (`n : ℕ`) with ring maps `a n : O → G n` from a base ring `O` and
transition maps `t n : G (n+1) → G n` compatible with the `a n`, surjective with kernel
`J n · G (n+1)` for ideals `J n` of `O` (e.g. `J n = I^{n+1}` or `I^n`):

* `TowerSystem.trLe h : G n →+* G m` for `m ≤ n` (composite of the `t k`), `trLe_refl`,
  `trLe_succ`, **`trLe_comp`** (`trLe h₁ ∘ trLe h₂ = trLe (h₁.trans h₂)`), `trLe_comp_a`;
* **`surjective_trLe`**, **`ker_trLe`**: `ker (trLe h) = J m · G n` for a decreasing sequence of
  ideals `J n` of `O` with `ker (t n) = J n · G (n+1)` and `J n · G n = 0` (induction with
  `Ideal.comap_map_of_surjective`); `ker_trLe_pow` for `J n = I^{n+1}`;
* `trLe_apply_of` (compatible elements), `trLe_comm` (naturality for maps of towers).

This is the shape of the transition maps of an adic system (`AdicChartSystem`, up to the index
shift `n ↦ n + 1`).
-/

universe u v

namespace SemistableReduction

namespace TowerSystem

variable {O : Type v} [CommRing O] {G : ℕ → Type u} [∀ n, CommRing (G n)]
  (t : ∀ n, G (n + 1) →+* G n)

/-- The transition map `G n → G m` for `m ≤ n`: the composite of the successor maps. -/
def trLe {m n : ℕ} (h : m ≤ n) : G n →+* G m :=
  Nat.leRecOn (C := fun k ↦ G k →+* G m) h (fun {k} (f : G k →+* G m) ↦ f.comp (t k))
    (RingHom.id (G m))

@[simp]
lemma trLe_refl (m : ℕ) : trLe t (le_refl m) = RingHom.id (G m) :=
  Nat.leRecOn_self _

lemma trLe_succ' {m n : ℕ} (h : m ≤ n + 1) (h' : m ≤ n) :
    trLe t h = (trLe t h').comp (t n) :=
  Nat.leRecOn_succ (C := fun k ↦ G k →+* G m) h' _

lemma trLe_succ {m n : ℕ} (h : m ≤ n) :
    trLe t (h.trans (Nat.le_succ n)) = (trLe t h).comp (t n) :=
  trLe_succ' t _ h

lemma trLe_self_succ (n : ℕ) : trLe t (Nat.le_succ n) = t n := by
  rw [trLe_succ' t (Nat.le_succ n) le_rfl, trLe_refl, RingHom.id_comp]

/-- **Composition of the transition maps.** -/
theorem trLe_comp {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) :
    (trLe t h₁).comp (trLe t h₂) = trLe t (h₁.trans h₂) := by
  induction n, h₂ using Nat.le_induction with
  | base => rw [trLe_refl, RingHom.comp_id]
  | succ n hmn ih =>
    rw [trLe_succ' t _ hmn, trLe_succ' t _ (h₁.trans hmn), ← RingHom.comp_assoc, ih]

lemma trLe_apply_trLe {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) (x : G n) :
    trLe t h₁ (trLe t h₂ x) = trLe t (h₁.trans h₂) x :=
  RingHom.congr_fun (trLe_comp t h₁ h₂) x

/-- The transition maps are surjective if the successor maps are. -/
theorem surjective_trLe (ht : ∀ n, Function.Surjective (t n)) {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (trLe t h) := by
  induction n, h using Nat.le_induction with
  | base => rw [trLe_refl]; exact Function.surjective_id
  | succ n hmn ih =>
    rw [trLe_succ' t _ hmn, RingHom.coe_comp]
    exact ih.comp (ht n)

variable {t} (a : ∀ n, O →+* G n) (ha : ∀ n, (t n).comp (a (n + 1)) = a n)

include ha in
lemma trLe_comp_a {m n : ℕ} (h : m ≤ n) : (trLe t h).comp (a n) = a m := by
  induction n, h using Nat.le_induction with
  | base => rw [trLe_refl, RingHom.id_comp]
  | succ n hmn ih => rw [trLe_succ' t _ hmn, RingHom.comp_assoc, ha, ih]

include ha in
/-- **The kernel of the transition map** `G n → G m` is `J m · G n` for a decreasing sequence of
ideals `J` of `O` if the kernels of the successor maps are `J k · G (k+1)` and `J k` kills `G k`. -/
theorem ker_trLe (ht : ∀ n, Function.Surjective (t n)) {J : ℕ → Ideal O} (hJ : Antitone J)
    (hker : ∀ n, RingHom.ker (t n) = (J n).map (a (n + 1)))
    (hkill : ∀ n, (J n).map (a n) = ⊥) {m n : ℕ} (h : m ≤ n) :
    RingHom.ker (trLe t h) = (J m).map (a n) := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [trLe_refl, hkill]
    exact (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id
  | succ n hmn ih =>
    rw [trLe_succ' t _ hmn, ← RingHom.comap_ker, ih, ← ha n, ← Ideal.map_map,
      Ideal.comap_map_of_surjective' _ (ht n), hker n]
    exact sup_eq_left.mpr (Ideal.map_mono (hJ hmn))

include ha in
/-- `ker_trLe` for the powers `J n = I^{n+1}`. -/
theorem ker_trLe_pow (ht : ∀ n, Function.Surjective (t n)) {I : Ideal O}
    (hker : ∀ n, RingHom.ker (t n) = (I ^ (n + 1)).map (a (n + 1)))
    (hkill : ∀ n, (I ^ (n + 1)).map (a n) = ⊥) {m n : ℕ} (h : m ≤ n) :
    RingHom.ker (trLe t h) = (I ^ (m + 1)).map (a n) :=
  ker_trLe a ha ht (J := fun n ↦ I ^ (n + 1))
    (fun _ _ hmn ↦ Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)) hker hkill h

/-- Compatible elements are mapped to each other. -/
lemma trLe_apply_of {x : ∀ n, G n} (hx : ∀ n, t n (x (n + 1)) = x n) {m n : ℕ} (h : m ≤ n) :
    trLe t h (x n) = x m := by
  induction n, h using Nat.le_induction with
  | base => rw [trLe_refl, RingHom.id_apply]
  | succ n hmn ih => rw [trLe_succ' t _ hmn, RingHom.comp_apply, hx, ih]

/-- **Naturality**: the transition maps commute with compatible maps of towers. -/
lemma trLe_comm {H : ℕ → Type*} [∀ n, CommRing (H n)] {t' : ∀ n, H (n + 1) →+* H n}
    (ρ : ∀ n, G n →+* H n) (hρ : ∀ n x, t' n (ρ (n + 1) x) = ρ n (t n x)) {m n : ℕ}
    (h : m ≤ n) (x : G n) : trLe t' h (ρ n x) = ρ m (trLe t h x) := by
  induction n, h using Nat.le_induction with
  | base => rw [trLe_refl, trLe_refl, RingHom.id_apply, RingHom.id_apply]
  | succ n hmn ih =>
    rw [trLe_succ' t' _ hmn, trLe_succ' t _ hmn, RingHom.comp_apply, RingHom.comp_apply, hρ, ih]

end TowerSystem

end SemistableReduction
