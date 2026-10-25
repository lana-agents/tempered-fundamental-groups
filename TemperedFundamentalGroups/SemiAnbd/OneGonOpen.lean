/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.OneGonTower

/-!
# Open subgroups of `π^temp(G^Σ)` of the stable 1-gon: `HI` and temp-slimness

A finite étale covering of the stable `1`-gon (e.g. the `G^Σ` of `X = (E/M) ∖ (E[ℓ]/M)` in
[EtTh] / IUT) has as tempered fundamental group an open subgroup `U` of `π^temp(G^Σ)`, acting on
the same tree tower (pulled back along `U ↪ π^temp(G^Σ)`, `TreeTower.comap`).

* `TreeTower.HI.comap_subtype`: `(HI s)` passes to the pulled back tower of a subgroup `U` with
  `U ⊓ stab s` of finite index in `stab s` (indices drop at most by the factor
  `[stab s : U ⊓ stab s]`);
* `oneGon_HI_comap`: for every open subgroup `U ⊆ π^temp(G^Σ)` of the 1-gon, the base system
  satisfies `HI` in the tower over `U` (bridge B2b for coverings, step 2 of the MR13 plan);
* `oneGon_tempSlim_of_isOpen`: open subgroups of `π^temp(G^Σ)` are temp-slim.
-/

open CategoryTheory

namespace TemperedFundamentalGroups

namespace TreeTower

variable {Γ : Type*} [Group Γ] {J : Type*} [Category J] {T : TreeTower Γ J}

lemma fixAt_comap {Γ' : Type*} [Group Γ'] (φ : Γ' →* Γ) (k : J) (w : T.V k) :
    (T.comap φ).fixAt k w = (T.fixAt k w).comap φ := rfl

/-- **`(HI)` for subgroups of finite index in the verticial subgroup**: if `U ⊓ stab s` has finite
index in `stab s`, then `s` satisfies `(HI)` in the tower pulled back to `U`. -/
theorem HI.comap_subtype {s : T.Sys} (hs : T.HI s) (U : Subgroup Γ)
    (hU : U.relIndex (stab s) ≠ 0) : (T.comap U.subtype).HI (T.comapSys U.subtype s) := by
  intro n j
  obtain ⟨k, f, hk⟩ := hs (n * U.relIndex (stab s)) j
  refine ⟨k, f, fun w hw ↦ ?_⟩
  rw [stab_comap, fixAt_comap, Subgroup.relIndex_comap, Subgroup.map_comap_eq,
    Subgroup.range_subtype]
  have hmul := Subgroup.relIndex_inf_mul_relIndex (T.fixAt k w) U (stab s)
  have hdvd : (T.fixAt k w).relIndex (stab s) ∣ (T.fixAt k w ⊓ U).relIndex (stab s) :=
    Subgroup.relIndex_dvd_of_le_left _ inf_le_left
  rcases Nat.eq_zero_or_pos ((T.fixAt k w).relIndex (U ⊓ stab s)) with h0 | hpos
  · exact .inl h0
  refine .inr ?_
  rcases hk w hw with h | h
  · rw [h, zero_dvd_iff, ← hmul] at hdvd
    exact absurd hdvd (Nat.mul_ne_zero hpos.ne' hU)
  · have hle := Nat.le_of_dvd (by rw [← hmul]; exact Nat.mul_pos hpos (Nat.pos_of_ne_zero hU))
      hdvd
    rw [← hmul] at hle
    by_contra hn
    have := Nat.mul_le_mul_right (U.relIndex (stab s)) (not_lt.1 hn)
    omega

end TreeTower

open LoopTower

variable {P : ℕ → Prop}

/-- **`(HI)` over open subgroups of `π^temp(G^Σ)`** (the tempered groups of finite étale coverings
of the 1-gon): the base system satisfies `HI` in the tower pulled back to an open subgroup. -/
theorem oneGon_HI_comap {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) (U : Subgroup (oneGonTempered P))
    (hU : IsOpen (U : Set (oneGonTempered P))) :
    ((oneGonTower P).comap U.subtype).HI
      ((oneGonTower P).comapSys U.subtype (baseSys (oneGonB₀ P) (oneGonB₁ P))) :=
  (oneGon_HI hℓ hP).comap_subtype U
    (TempSlim.relIndex_ne_zero_of_isCompact isCompact_stab_baseSys hU)

/-- **Open subgroups of `π^temp(G^Σ)` of the 1-gon are temp-slim** (for `Σ ∋ ℓ`). -/
theorem oneGon_tempSlim_of_isOpen {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ)
    (U : Subgroup (oneGonTempered P)) (hU : IsOpen (U : Set (oneGonTempered P))) : TempSlim U :=
  (oneGon_tempSlim hℓ hP).of_isOpen hU

end TemperedFundamentalGroups
