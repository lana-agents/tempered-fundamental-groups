/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.LoopProfinite
import TemperedFundamentalGroups.SemiAnbd.OneGonOpen
import TemperedFundamentalGroups.SemiAnbd.OneGonSysEstranged

/-!
# `PSCAdj` and CG3' over open subgroups of `π^temp(G^Σ)` of the stable 1-gon

A finite étale covering of the stable `1`-gon has as tempered fundamental group an open subgroup
`U` of `π^temp(G^Σ)`, acting on the same tree tower pulled back along `U ↪ π^temp(G^Σ)`
(`TreeTower.comap`). We transport the adjacency hypothesis `PSCAdj` and CG3' ([SemiAnbd]
Thm 3.7(iii)/Cor 3.9 in tower form) to these pulled back towers.

Generic transport along homomorphisms:
* `TreeTower.IsFunctorial.comap`, `TreeTower.NoBranchSwap.comap`, `TreeTower.PreservesKind.comap`;
* `TreeTower.SysEstranged.comap` (for injective homomorphisms).

Loop towers:
* **`LoopTower.stab_inf_ne_bot_of_edge`**: if `b₁(ε)` has infinite order, every edge-like subgroup
  meets every open subgroup nontrivially (edge-like subgroups are conjugates of the image of
  `b₁(E)`, `LoopTower.stab_edge_eq_conj`, and an open subgroup has finite index in the compact
  verticial subgroup of the base system).

The 1-gon:
* `oneGon_pow_ne_one`: the node inertia generator has infinite order in `Π^Σ_{0,3}`;
* `oneGon_hedge_comap`, **`oneGon_pscAdj_comap`** and **`oneGon_isGraphic_iff_comap`** (CG3' for
  open subgroups `U ⊆ π^temp(G^Σ)`, `U' ⊆ π^temp(G^{Σ'})`). The last two carry the named hypothesis
  `OneGonSysEstrangedUnbounded` (debt, `MR13-plan.md`) of the 1-gon;
* `oneGon_toHat_injective`: `π^temp(G^Σ) ↪ π̂₁(G^Σ)` for the 1-gon ([SemiAnbd] Prop 3.6(iii),
  `LoopTower.toHat_injective`).
-/

open CategoryTheory Pi1 Pi1.Profinite Pi1.SurfaceGroup
open scoped Pointwise

namespace TemperedFundamentalGroups

namespace TreeTower

variable {Γ : Type*} [Group Γ] {J : Type*} [Category J] {T : TreeTower Γ J}
  {Γ' : Type*} [Group Γ'] (φ : Γ' →* Γ)

lemma IsFunctorial.comap (hT : T.IsFunctorial) : (T.comap φ).IsFunctorial :=
  ⟨hT.map_id, hT.map_comp⟩

lemma NoBranchSwap.comap (hB : T.NoBranchSwap) : (T.comap φ).NoBranchSwap := hB

lemma PreservesKind.comap (hK : T.PreservesKind) : (T.comap φ).PreservesKind := hK

/-- Estrangement of systems passes to the tower pulled back along an injective homomorphism. -/
lemma SysEstranged.comap (hE : T.SysEstranged) (hφ : Function.Injective φ) :
    (T.comap φ).SysEstranged := by
  intro g hg s s' hs hs' k
  refine hE (φ g) (fun h ↦ hg (hφ (h.trans φ.map_one.symm))) ((T.comapSys φ).symm s)
    ((T.comapSys φ).symm s') ?_ ?_ k
  · have : g ∈ stab (T.comapSys φ ((T.comapSys φ).symm s)) := by rwa [Equiv.apply_symm_apply]
    rwa [stab_comap] at this
  · have : g ∈ stab (T.comapSys φ ((T.comapSys φ).symm s')) := by rwa [Equiv.apply_symm_apply]
    rwa [stab_comap] at this

/-- For cofiltered levels and colour-preserving maps, a system that is cofinally of edge kind is of
edge kind at every level. -/
lemma kind_eq_false_of_cofinal [IsCofilteredOrEmpty J] (hK : T.PreservesKind) (e : T.Sys)
    (he : ∀ j, ∃ (k : J) (_ : k ⟶ j), T.kind k (e.1 k) = false) (j : J) :
    T.kind j (e.1 j) = false := by
  obtain ⟨k, f, hk⟩ := he j
  rw [← e.2 f, hK]
  exact hk

end TreeTower

namespace LoopTower

universe u

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [IsTopologicalGroup Pv] [CompactSpace Pv]
  [Group E] {b₀ b₁ : E →* Pv}

/-- **Edge-like subgroups meet open subgroups nontrivially**: if `b₁(ε)` has infinite order, then
for every open subgroup `U` of the loop group and every system `e` of edge kind,
`stab e ⊓ U ≠ ⊥`. -/
theorem stab_inf_ne_bot_of_edge (hsep : ∀ π : Pv, π ≠ 1 → ∃ N : Level b₀ b₁, π ∉ N.1)
    (hcl : IsClosed (b₁.range : Set Pv)) {ε : E} (hε : ∀ n : ℕ, 0 < n → b₁ ε ^ n ≠ 1)
    (U : Subgroup (loopGroup b₀ b₁)) (hU : IsOpen (U : Set (loopGroup b₀ b₁)))
    (e : (tower b₀ b₁).Sys) (he : ∀ N, (tower b₀ b₁).kind N (e.1 N) = false) :
    TreeTower.stab e ⊓ U ≠ ⊥ := by
  obtain ⟨h, hh⟩ := stab_edge_eq_conj hsep hcl e he
  -- the conjugate `h⁻¹ U h` is open
  set U' : Subgroup (loopGroup b₀ b₁) := U.comap (MulAut.conj h).toMonoidHom
  have hU' : IsOpen (U' : Set (loopGroup b₀ b₁)) :=
    hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hidx := TempSlim.relIndex_ne_zero_of_isCompact isCompact_stab_baseSys hU'
  set x := vertexIncl b₀ b₁ (b₁ ε)
  obtain ⟨n, hn, -, hxn⟩ :=
    Subgroup.exists_pow_mem_of_relIndex_ne_zero hidx (vertexIncl_mem_stab (b₁ ε))
  refine (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨h * x ^ n * h⁻¹, ?_, ?_⟩, ?_⟩
  · rw [hh]
    have : x ^ n ∈ (b₁.range).map (vertexIncl b₀ b₁) :=
      pow_mem (Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.2 ⟨ε, rfl⟩)) n
    have := Subgroup.smul_mem_pointwise_smul (x ^ n) (ConjAct.toConjAct h) _ this
    rwa [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at this
  · exact hxn.1
  · intro h1
    have h1' : h * x ^ n * h⁻¹ = 1 := congrArg Subtype.val h1
    rw [mul_inv_eq_one, mul_eq_left] at h1'
    rw [← map_pow] at h1'
    exact hε n hn (vertexIncl_injective hsep (h1'.trans (map_one _).symm))

end LoopTower

open LoopTower

variable {P : ℕ → Prop}

/-- **The node inertia of the 1-gon has infinite order** in `Π^Σ_{0,3}` (for `Σ ∋ ℓ`): its image in
a quotient with cusps of order `(ℓⁿ)³` has order `> n`. -/
theorem oneGon_pow_ne_one {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) (n : ℕ) (hn : 0 < n) :
    oneGonB₁ P (ProSigmaCompletion.eta P (Multiplicative.ofAdd (1 : ℤ))) ^ n ≠ 1 := by
  obtain ⟨Q, _, _, _, ρ, -, -, -, hc, -, -, -⟩ :=
    exists_elevated_proSigma (P := P) (g := 0) (r := 3) (pow_pos hℓ.pos n)
      (fun p hp hpℓ ↦ (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hpℓ) ▸ hP)
      (by unfold IsHyperbolic; omega)
  have hord : orderOf (ρ (ProSigmaCompletion.eta P (oneGonGen false false))) = (ℓ ^ n) ^ 3 := by
    simp only [oneGonGen, map_inv, orderOf_inv]; exact hc 1
  have hb : oneGonB₁ P (ProSigmaCompletion.eta P (Multiplicative.ofAdd (1 : ℤ))) =
      ProSigmaCompletion.eta P (oneGonGen false false) := by
    rw [ProSigmaCompletion.map_eta, zpowersHom_apply, toAdd_ofAdd, zpow_one]
  intro h
  rw [hb] at h
  have h' : ρ (ProSigmaCompletion.eta P (oneGonGen false false)) ^ n = 1 := by
    rw [← map_pow, h, map_one]
  refine pow_ne_one_of_lt_orderOf hn.ne' ?_ h'
  rw [hord, ← pow_mul]
  calc n < ℓ ^ n := Nat.lt_pow_self hℓ.one_lt
    _ ≤ ℓ ^ (n * 3) := Nat.pow_le_pow_right hℓ.pos (by omega)

/-- **Edge-like subgroups over open subgroups are nontrivial** (the `hedge` hypothesis for the
tower of `π^temp(G^Σ)` pulled back to an open subgroup `U`). -/
theorem oneGon_hedge_comap {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) (U : Subgroup (oneGonTempered P))
    (hU : IsOpen (U : Set (oneGonTempered P))) (e : ((oneGonTower P).comap U.subtype).Sys)
    (he : ∀ N, ∃ (N' : Level (oneGonB₀ P) (oneGonB₁ P)) (_ : N' ⟶ N),
      ((oneGonTower P).comap U.subtype).kind N' (e.1 N') = false) :
    TreeTower.stab e ≠ ⊥ := by
  set e₀ : (oneGonTower P).Sys := ((oneGonTower P).comapSys U.subtype).symm e
  have he₀ : e = (oneGonTower P).comapSys U.subtype e₀ := (Equiv.apply_symm_apply _ e).symm
  have hk := TreeTower.kind_eq_false_of_cofinal preservesKind_tower e₀ he
  have hne := stab_inf_ne_bot_of_edge oneGon_sep (oneGon_isClosed_range true)
    (oneGon_pow_ne_one hℓ hP) U hU e₀ hk
  obtain ⟨⟨g, hg, hgU⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  rw [he₀, TreeTower.stab_comap]
  refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨g, hgU⟩, hg⟩, fun h ↦ hg1 ?_⟩
  exact Subtype.ext (congrArg (fun y : U ↦ (y : oneGonTempered P)) (congrArg Subtype.val h))

/-- **`PSCAdj` over open subgroups of `π^temp(G^Σ)` of the 1-gon** (the tempered groups of finite
étale coverings), given the unbounded case of estrangement of systems (debt). -/
theorem oneGon_pscAdj_comap {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) (hU : OneGonSysEstrangedUnbounded P)
    (U : Subgroup (oneGonTempered P)) (hUo : IsOpen (U : Set (oneGonTempered P))) :
    ((oneGonTower P).comap U.subtype).PSCAdj :=
  TreeTower.pscAdj_of_sysEstranged (isFunctorial_tower.comap _)
    ((oneGon_sysEstranged hU).comap _ U.subtype_injective) (noBranchSwap_tower.comap _)
    (oneGon_hedge_comap hℓ hP U hUo)

/-- **CG3' over open subgroups** ([SemiAnbd] Thm 3.7(iii)/Cor 3.9, tower form, for finite étale
coverings of the pro-`Σ` 1-gon): an isomorphism `U ≃* U'` of open subgroups of the tempered
fundamental groups of two pro-`Σ` 1-gons is graphic iff it is group-theoretically verticial,
given the unbounded case of estrangement of systems on both sides (debt). -/
theorem oneGon_isGraphic_iff_comap {P' : ℕ → Prop} {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ)
    (hℓ' : ℓ'.Prime) (hP' : P' ℓ') (hU : OneGonSysEstrangedUnbounded P)
    (hU' : OneGonSysEstrangedUnbounded P') (U : Subgroup (oneGonTempered P))
    (hUo : IsOpen (U : Set (oneGonTempered P))) (U' : Subgroup (oneGonTempered P'))
    (hUo' : IsOpen (U' : Set (oneGonTempered P'))) (α : U ≃* U') :
    TreeTower.IsGraphic ((oneGonTower P).comap U.subtype) ((oneGonTower P').comap U'.subtype) α ↔
      TreeTower.IsGroupTheoreticallyVerticial ((oneGonTower P).comap U.subtype)
        ((oneGonTower P').comap U'.subtype) α :=
  TreeTower.isGraphic_iff_isGroupTheoreticallyVerticial (oneGon_pscAdj_comap hℓ hP hU U hUo)
    (oneGon_pscAdj_comap hℓ' hP' hU' U' hUo')

/-- **`π^temp(G^Σ) ↪ π̂₁(G^Σ)` for the stable 1-gon** ([SemiAnbd] Prop 3.6(iii)): the tempered
fundamental group injects continuously into the profinite fundamental group
`lim_N Ĥ_N` (`LoopTower.loopHat`). -/
theorem oneGon_toHat_injective :
    Function.Injective (toHat (b₀ := oneGonB₀ P) (b₁ := oneGonB₁ P)) :=
  toHat_injective

end TemperedFundamentalGroups
