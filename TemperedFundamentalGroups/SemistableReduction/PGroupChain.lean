/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Subnormal chains of index `p` in finite `p`-groups

Blueprint §9.4, D4. In a finite `p`-group `T`, every proper subgroup `H` is contained with index
`p` and as a normal subgroup in a larger subgroup (`exists_normal_relIndex_eq`), hence every
subgroup `H` sits in a chain `H = H₀ ◁ H₁ ◁ ⋯ ◁ H_m = T` with `[H_{i+1} : H_i] = p`
(`exists_chain`). Via Galois theory, `N^H ⊇ N^{H₁} ⊇ ⋯ ⊇ N^T` is a tower of Galois extensions of
degree `p` (used in G1/G3).

The one-step statement follows from Sylow's `exists_subgroup_card_pow_succ` (a subgroup of order
`p^n` lies in one of order `p^(n+1)`), and a subgroup of index `p` = the smallest prime factor of
the order is normal (`Subgroup.normal_of_index_eq_minFac_card`).
-/

namespace SemistableReduction

namespace PGroupChain

variable {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]

omit [Finite T] hp in
/-- The index of `H` in `K ≥ H` times the order of `H` is the order of `K`. -/
lemma relIndex_mul_card {H K : Subgroup T} (hHK : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, mul_comm, Subgroup.relIndex,
    Subgroup.card_mul_index]

/-- **One step.** A proper subgroup `H` of a finite `p`-group is a normal subgroup of index `p`
of a larger subgroup. -/
theorem exists_normal_relIndex_eq (hT : IsPGroup p T) {H : Subgroup T} (hH : H ≠ ⊤) :
    ∃ K : Subgroup T, H ≤ K ∧ (H.subgroupOf K).Normal ∧ H.relIndex K = p := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hT
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hT.to_subgroup H)
  have hlt : n < m := by
    have hle : Nat.card H ≤ Nat.card T := Subgroup.card_le_card_group H
    have hne : Nat.card H ≠ Nat.card T := fun h ↦ hH (Subgroup.card_eq_iff_eq_top H |>.1 h)
    rw [hn, hm] at hle hne
    exact (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 (lt_of_le_of_ne hle hne)
  obtain ⟨K, hK, hHK⟩ := Sylow.exists_subgroup_card_pow_succ
    (by rw [hm]; exact pow_dvd_pow p hlt) hn
  have hidx : H.relIndex K = p := by
    have h := relIndex_mul_card hHK
    rw [hn, hK, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos n) (h.trans (mul_comm _ _))
  refine ⟨K, hHK, ?_, hidx⟩
  apply Subgroup.normal_of_index_eq_minFac_card
  rw [← Subgroup.relIndex, hidx, hK, Nat.Prime.pow_minFac hp.out (Nat.succ_ne_zero n)]

/-- **D4.** Every subgroup `H` of a finite `p`-group `T` sits in a chain
`H = H₀ ≤ H₁ ≤ ⋯ ≤ H_m = T` with `Hᵢ` normal of index `p` in `H_{i+1}`. -/
theorem exists_chain (hT : IsPGroup p T) (H : Subgroup T) :
    ∃ (m : ℕ) (c : ℕ → Subgroup T), c 0 = H ∧ c m = ⊤ ∧
      ∀ i < m, c i ≤ c (i + 1) ∧ ((c i).subgroupOf (c (i + 1))).Normal ∧
        (c i).relIndex (c (i + 1)) = p := by
  induction hk : H.index using Nat.strong_induction_on generalizing H with
  | _ k ih =>
    by_cases hH : H = ⊤
    · exact ⟨0, fun _ ↦ H, rfl, hH, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
    obtain ⟨K, hHK, hnormal, hidx⟩ := exists_normal_relIndex_eq hT hH
    have hKlt : K.index < k := by
      rw [← hk, ← Subgroup.relIndex_mul_index hHK, hidx]
      exact lt_mul_left (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hp.out.one_lt
    obtain ⟨m, c, hc0, hcm, hc⟩ := ih _ hKlt K rfl
    let c' : ℕ → Subgroup T := fun i ↦ match i with
      | 0 => H
      | j + 1 => c j
    refine ⟨m + 1, c', rfl, hcm, fun i hi ↦ ?_⟩
    rcases i with _ | i
    · change H ≤ c 0 ∧ (H.subgroupOf (c 0)).Normal ∧ H.relIndex (c 0) = p
      rw [hc0]
      exact ⟨hHK, hnormal, hidx⟩
    · exact hc i (by omega)

end PGroupChain

end SemistableReduction
