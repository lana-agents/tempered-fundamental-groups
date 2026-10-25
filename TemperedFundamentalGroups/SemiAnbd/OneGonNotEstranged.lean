/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.FixedArc
import TemperedFundamentalGroups.SemiAnbd.OneGonTower

/-!
# The level-wise estrangement `TreeTower.Estranged` fails for the pro-`ℓ` 1-gon

`TreeTower.Estranged` (W9) asks that every nontrivial element fix, at cofinally many levels, a set
of diameter `≤ 2` of the tree of that level. This is the intermediate claim of the proof of
[SemiAnbd] Thm 3.7(iii) (`semianbd.txt` l.1947–1961: "for some cofinal subset `J ⊆ I`, `H` fixes at
least one, but no more than two vertices of `G∞,j`"). For the pro-`ℓ` semi-graph of anabelioids
`G^{ℓ}` of the stable `1`-gon (`oneGonSigma`, [SemiAnbd] Ex 2.10) it is **false**, although `G^{ℓ}`
is totally estranged in the sense of [SemiAnbd] Def 2.4(iv) (profinite malnormality of the cusp
inertia groups):

At every level `N`, the quotient `Q_N = Π^{ℓ}_{0,3} / N` is a finite `ℓ`-group, hence nilpotent, so
the image `A_N` of the first branch is properly contained in its normalizer as soon as `A_N ≠ Q_N`
(normalizer condition). For `r ∈ N_{Q_N}(A_N) ∖ A_N`, the image of the cusp generator `c₀` fixes
the two distinct edges `t⁻¹ B` and `r t⁻¹ B` at the base vertex of the Bass–Serre tree, hence the
arc `t⁻¹ B – G – r t⁻¹ B – r t⁻¹ G` (`TreeTower.FixedArcAt`), at every level below one where
`A_N ≠ Q_N`.

* `HNNExtension.tLength_t_mul_of_mul_inv_t`: `t r t⁻¹` has `t`-length `2` for `r ∉ A` (Britton);
* `LoopTower.fixedArcAt_of_normalizer`: an element of the vertex group whose image lies in `A_N`
  fixes an arc at level `N` if `A_N` is not self-normalising;
* `oneGon_exists_level_ne_top`: some level has `A_N ≠ Q_N` (an elevated quotient, pi1
  `exists_elevated_proSigma`);
* **`oneGonTower_not_estranged`**: for `Σ = {ℓ}`, `(oneGonTower (· = ℓ)).Estranged` is false.

Consequently, the `TreeTower.Estranged` route to `PSCAdj` (`TreeTower.pscAdj_of_estranged`) and to
[SemiAnbd] Thm 3.7(iii) (`TreeTower.exists_le_stab_of_estranged`) is not available for `G^{ℓ}`; the
estrangement of [SemiAnbd] Def 2.4(iv) has to be used for compatible systems (in the limit), not
level by level.
-/

open CategoryTheory Pi1 Pi1.Profinite Pi1.SurfaceGroup HNNExtension
open scoped Pointwise

namespace HNNExtension

open NormalWord

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- **Britton**: for `r ∉ A`, `t r t⁻¹` has `t`-length `2`. -/
theorem tLength_t_mul_of_mul_inv_t {r : G} (hr : r ∉ A) :
    tLength (t * of r * t⁻¹ : HNNExtension G A B φ) = 2 := by
  have hc : ([] ++ [((1 : ℤˣ), (1 : G))]).IsChain
      (fun a b : ℤˣ × G => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1) := List.isChain_singleton _
  have h := tLength_mul_of_mul_t_pow (φ := φ) 1 [] 1 1 hc r (-1)
  have hp : (⟨1, [] ++ [((1 : ℤˣ), (1 : G))], hc⟩ : ReducedWord G A B).prod φ = t := by
    simp [ReducedWord.prod]
  rw [hp, if_neg (by simpa using hr)] at h
  simpa using h

end HNNExtension

namespace TemperedFundamentalGroups

namespace LoopTower

universe u

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [Group E] {b₀ b₁ : E →* Pv}

lemma smul_inl_mk {N : Level b₀ b₁} (g k : levelGroup N) :
    g • (Sum.inl (k : _ ⧸ vertexSubgroup (levelEquiv N)) : BSVertex (levelEquiv N)) =
      Sum.inl ((g * k : levelGroup N) : _ ⧸ vertexSubgroup (levelEquiv N)) := by
  rw [Sum.smul_inl, MulAction.Quotient.smul_mk, smul_eq_mul]

lemma smul_inr_mk {N : Level b₀ b₁} (g k : levelGroup N) :
    g • (Sum.inr (k : _ ⧸ edgeSubgroup (levelEquiv N)) : BSVertex (levelEquiv N)) =
      Sum.inr ((g * k : levelGroup N) : _ ⧸ edgeSubgroup (levelEquiv N)) := by
  rw [Sum.smul_inr, MulAction.Quotient.smul_mk, smul_eq_mul]

/-- If the image of `π` lies in the first branch image `A_N` and `r` normalises `A_N` without lying
in it, the image of `π` fixes the arc `t⁻¹ B – G – r t⁻¹ B – r t⁻¹ G` at level `N`. -/
theorem fixedArcAt_of_normalizer (N : Level b₀ b₁) (π : Pv)
    (hπ : (π : levelQuot N) ∈ (branch₀ N).range) {r : levelQuot N}
    (hrN : r ∈ Subgroup.normalizer ((branch₀ N).range : Set (levelQuot N)))
    (hrA : r ∉ (branch₀ N).range) :
    (tower b₀ b₁).FixedArcAt N (vertexIncl b₀ b₁ π) := by
  set A := (branch₀ N).range
  set a : levelQuot N := (π : levelQuot N)
  -- the conjugate `r⁻¹ a r` lies in `A`
  have ha' : r⁻¹ * a * r ∈ A := by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hrN) a).1 hπ
  set G := levelGroup N
  let x₀ : BSVertex (levelEquiv N) := .inr ((t⁻¹ : G) : G ⧸ edgeSubgroup (levelEquiv N))
  let x₁ : BSVertex (levelEquiv N) := .inl ((1 : G) : G ⧸ vertexSubgroup (levelEquiv N))
  let x₂ : BSVertex (levelEquiv N) := .inr ((of r * t⁻¹ : G) : G ⧸ edgeSubgroup (levelEquiv N))
  let x₃ : BSVertex (levelEquiv N) := .inl ((of r * t⁻¹ : G) : G ⧸ vertexSubgroup (levelEquiv N))
  -- the key identities `a t⁻¹ = t⁻¹ φ(a)` and `a r t⁻¹ = r t⁻¹ φ(r⁻¹ a r)`
  have e₀ : (of a * t⁻¹ : G) = t⁻¹ * of (levelEquiv N ⟨a, hπ⟩ : levelQuot N) :=
    of_mul_inv_t (⟨a, hπ⟩ : A)
  have e₂ : (of a * (of r * t⁻¹) : G) =
      (of r * t⁻¹) * of (levelEquiv N ⟨r⁻¹ * a * r, ha'⟩ : levelQuot N) := by
    rw [mul_assoc (of r), ← of_mul_inv_t (⟨r⁻¹ * a * r, ha'⟩ : A), ← mul_assoc (of r),
      ← mul_assoc]
    congr 1
    rw [← map_mul, ← map_mul]
    congr 1
    group
  have hg : (tower b₀ b₁).ρ N (vertexIncl b₀ b₁ π) = (of a : G) := rfl
  refine ⟨x₀, x₁, x₂, x₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `t⁻¹ B` meets `t⁻¹ t G = G`
    change (bassSerreGraph (levelEquiv N)).Adj x₀ x₁
    rw [adj_inr_iff]
    exact Or.inr (by rw [inv_mul_cancel])
  · change (bassSerreGraph (levelEquiv N)).Adj x₁ x₂
    refine SimpleGraph.Adj.symm ?_
    rw [adj_inr_iff]
    refine Or.inr (congrArg Sum.inl ?_)
    rw [inv_mul_cancel_right]
    exact (mk_vertex_eq_iff (k := 1) (k' := of r)).2 ⟨r, by rw [one_mul]⟩
  · change (bassSerreGraph (levelEquiv N)).Adj x₂ x₃
    rw [adj_inr_iff]
    exact Or.inl rfl
  · -- the two edges at the base vertex are distinct
    intro h
    have h' := Sum.inr.inj h
    obtain ⟨b, hb⟩ := mk_edge_eq_iff.1 h'
    have h2 : (t * of r * t⁻¹ : G) = of (b : levelQuot N) := by
      rw [mul_assoc, hb, ← mul_assoc, mul_inv_cancel, one_mul]
    have h3 := congrArg tLength h2
    rw [tLength_t_mul_of_mul_inv_t hrA] at h3
    rw [(tLength_eq_zero_iff _).2 ⟨_, rfl⟩] at h3
    exact absurd h3 (by norm_num)
  · intro h
    have h' := Sum.inl.inj h
    obtain ⟨y, hy⟩ := mk_vertex_eq_iff.1 h'
    have h3 := congrArg tLength hy
    rw [one_mul, (tLength_eq_zero_iff _).2 ⟨_, rfl⟩] at h3
    have h4 := tLength_of_mul_t_pow (φ := levelEquiv N) r (-1)
    simp only [Units.val_neg, Units.val_one, Int.reduceNeg, zpow_neg, zpow_one] at h4
    rw [h4] at h3
    exact absurd h3 (by norm_num)
  · rw [hg]
    refine (smul_inr_mk _ _).trans ?_
    rw [e₀]
    exact congrArg Sum.inr ((mk_edge_eq_iff (k := t⁻¹)).2 ⟨_, rfl⟩).symm
  · rw [hg]
    refine (smul_inl_mk _ _).trans ?_
    rw [mul_one]
    exact congrArg Sum.inl ((mk_vertex_eq_iff (k := 1) (k' := of a)).2 ⟨a, by rw [one_mul]⟩).symm
  · rw [hg]
    refine (smul_inr_mk _ _).trans ?_
    rw [e₂]
    exact congrArg Sum.inr ((mk_edge_eq_iff (k := of r * t⁻¹)).2 ⟨_, rfl⟩).symm
  · rw [hg]
    refine (smul_inl_mk _ _).trans ?_
    rw [e₂]
    exact congrArg Sum.inl ((mk_vertex_eq_iff (k := of r * t⁻¹)).2 ⟨_, rfl⟩).symm

/-- The first branch images are surjected onto by the transition maps: if `A_N = Q_N`, then
`A_{N'} = Q_{N'}` for `N ≤ N'`. -/
lemma range_branch₀_eq_top_of_le {N N' : Level b₀ b₁} (h : N ≤ N')
    (hN : (branch₀ N).range = ⊤) : (branch₀ N').range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨π, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨ε, hε⟩ := (eq_top_iff.1 hN) (Subgroup.mem_top (π : levelQuot N))
  refine ⟨ε, ?_⟩
  rw [← quotMap_branch₀ h, hε, quotMap_mk]

end LoopTower

open LoopTower

variable {P : ℕ → Prop}

/-- **A level of the 1-gon where `A_N ≠ Q_N`** and the image of the cusp generator `c₀` is
nontrivial (an elevated quotient with cusp orders `ℓ³`). -/
theorem oneGon_exists_level_ne_top {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    ∃ L : Level (oneGonB₀ P) (oneGonB₁ P),
      ((ProSigmaCompletion.eta P (cusp 0) : proSigma P 0 3) : levelQuot L) ≠ 1 ∧
        (branch₀ L).range ≠ ⊤ := by
  obtain ⟨Q, _, _, _, ρ, N, hρo, hρs, hc, hr, hN, hconj⟩ :=
    exists_elevated_proSigma (P := P) (g := 0) (r := 3) hℓ.pos
      (fun p hp hpℓ ↦ (Nat.prime_dvd_prime_iff_eq hp hℓ).1 hpℓ ▸ hP) (by unfold IsHyperbolic; omega)
  have hord : ∀ β, orderOf (ρ (ProSigmaCompletion.eta P (oneGonGen false β))) = ℓ ^ 3 := by
    rintro (_ | _)
    · simp only [oneGonGen, map_inv, orderOf_inv]; exact hc 1
    · exact hc 0
  have hloop : ρ.ker.comap (oneGonB₀ P) = ρ.ker.comap (oneGonB₁ P) := by
    ext x
    simp only [Subgroup.mem_comap, MonoidHom.mem_ker]
    obtain ⟨k, hk, hk'⟩ := ProSigmaCompletion.exists_zpow_eq ρ hρo (oneGonGen false true)
      (oneGonGen false false) x
    rw [hk, hk', ← orderOf_dvd_iff_zpow_eq_one, ← orderOf_dvd_iff_zpow_eq_one, hord, hord]
  let L : Level (oneGonB₀ P) (oneGonB₁ P) := ⟨ρ.ker, ρ.normal_ker, hρo 1, hloop⟩
  have hmk : ∀ x y : proSigma P 0 3, (x : levelQuot L) = y ↔ ρ x = ρ y := fun x y ↦ by
    rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
  refine ⟨L, fun h ↦ ?_, fun htop ↦ ?_⟩
  · rw [← QuotientGroup.mk_one, hmk, map_one, ← orderOf_eq_one_iff, hc 0] at h
    have : 1 < ℓ ^ 3 := Nat.one_lt_pow (by norm_num) hℓ.one_lt
    omega
  · -- every element of `N` lies in the image of the first branch, so `N = 1`
    have hbot : N = ⊥ := by
      rw [← inf_eq_left.2 (le_top : N ≤ ⊤), eq_bot_iff]
      intro x hx
      obtain ⟨π, rfl⟩ := hρs x
      obtain ⟨ε, hε⟩ := (eq_top_iff.1 htop) (Subgroup.mem_top (π : levelQuot L))
      have hε' : ρ (oneGonB₀ P ε) = ρ π := (hmk _ _).1 hε
      have hmem : ρ π ∈ N ⊓ (ConjAct.toConjAct (1 : Q) •
          (ρ.comp (cuspInertiaSigma P (g := 0) (r := 3) 0)).range) := by
        refine ⟨hx.1, ?_⟩
        rw [map_one, one_smul]
        exact ⟨ε, hε'⟩
      rw [hconj 0 1] at hmem
      exact hmem
    have h1 := hN
    rw [hbot, Subgroup.card_bot] at h1
    exact absurd h1 (not_le.2 hℓ.one_lt)

/-- The levels of the pro-`ℓ` 1-gon are finite `ℓ`-groups. -/
theorem oneGon_isPGroup_levelQuot {ℓ : ℕ}
    (N : Level (oneGonB₀ (· = ℓ)) (oneGonB₁ (· = ℓ))) :
    Finite (levelQuot N) ∧ IsPGroup ℓ (levelQuot N) := by
  have hS := MaxProSigma.isSigmaNat_index_maxProSigma (P := (· = ℓ)) N.1 N.2.2.1
  haveI : N.1.FiniteIndex := ⟨hS.1⟩
  have hfin : Finite (levelQuot N) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨hfin, IsPGroup.of_card (n := N.1.index.primeFactorsList.length) ?_⟩
  rw [← Subgroup.index]
  exact Nat.eq_prime_pow_of_unique_prime_dvd hS.1 fun hd hdvd ↦ hS.2 _ hd hdvd

/-- **Level-wise estrangement fails for the pro-`ℓ` 1-gon**: the image of the cusp generator
`c₀` in `π^temp(G^{ℓ})` fixes an arc of the tree at every level below a level where the first branch
image is a proper subgroup, so `(oneGonTower (· = ℓ)).Estranged` is false. -/
theorem oneGonTower_not_estranged {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ¬ (oneGonTower (· = ℓ)).Estranged := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨L, hc₀, hL⟩ := oneGon_exists_level_ne_top (P := (· = ℓ)) hℓ rfl
  set c₀ : proSigma (· = ℓ) 0 3 := ProSigmaCompletion.eta (· = ℓ) (cusp 0)
  set g := vertexIncl (oneGonB₀ (· = ℓ)) (oneGonB₁ (· = ℓ)) c₀
  have hc₀A : ∀ N : Level (oneGonB₀ (· = ℓ)) (oneGonB₁ (· = ℓ)),
      (c₀ : levelQuot N) ∈ (branch₀ N).range := fun N ↦
    ⟨ProSigmaCompletion.eta (· = ℓ) (Multiplicative.ofAdd 1), by
      simp [branch₀, oneGonB₀, oneGonGen, c₀, ProSigmaCompletion.map_eta]⟩
  have hg : g ≠ 1 := fun h ↦ hc₀ (by
    have := congrArg (proj L) h
    rw [proj_vertexIncl, map_one] at this
    exact (of_injective (φ := levelEquiv L)).eq_iff.1 (this.trans (map_one _).symm))
  intro hE
  refine TreeTower.not_estrangedElt_of_forall_fixedArcAt (j := L) (fun k f ↦ ?_) (hE g hg)
  obtain ⟨hfin, hp⟩ := oneGon_isPGroup_levelQuot k
  haveI := hfin
  haveI := hp.isNilpotent
  have hlt : (branch₀ k).range < ⊤ :=
    lt_top_iff_ne_top.2 fun htop ↦ hL (range_branch₀_eq_top_of_le f.le htop)
  obtain ⟨r, hrN, hrA⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  exact fixedArcAt_of_normalizer k c₀ (hc₀A k) hrN hrA

end TemperedFundamentalGroups
