/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.ClopenNhdofOne
import TemperedFundamentalGroups.SemiAnbd.LoopTowerVertex
import TemperedFundamentalGroups.SemiAnbd.OneGonSigma

/-!
# The tempered fundamental group of `G^Σ` for the stable 1-gon, and its temp-slimness

`G^Σ` of the stable `1`-gon (`oneGonSigma P`, [SemiAnbd] Ex 2.10) is a loop of groups: vertex
group `Π^Σ_{0,3}`, edge group `ℤ^Σ`, branches the inertia maps of `c₀` and `c₁⁻¹`. Its tempered
fundamental group (the inverse limit of the HNN level groups, `SemiAnbd/LoopTower.lean`) is
`oneGonTempered P`, acting on the tree tower `oneGonTower P` (bridge B1 of `MR12-tfg-plan.md`).

* `oneGon_level_of_approximator`: the `π₁`-epimorphic approximators of [SemiAnbd] Def 2.3 are
  levels.
* **`oneGon_HI`** (bridge B2b): the base vertex system satisfies `HI`, from
  `oneGonSigma_totallyElevated` ([SemiAnbd] Def 2.4(i), Ex 2.10).
* `oneGon_sep`: the levels separate the points of `Π^Σ_{0,3}` (every open subgroup of `ℤ^Σ` of
  index `m` contains the kernel of a cusp-order-`m³` quotient, pi1 Lemma A).
* **`oneGon_tempSlim`** (`tempSlim^Σ` of the MR13 plan, [SemiAnbd] Prop 3.6(iv)/Ex 3.10 for
  `G^Σ`): `π^temp(G^Σ)` of the stable `1`-gon is temp-slim, for every `Σ` containing a prime.
-/

open CategoryTheory Pi1 Pi1.Profinite Pi1.SurfaceGroup HNNExtension
open scoped Pointwise

namespace TemperedFundamentalGroups

open LoopTower

variable (P : ℕ → Prop)

/-- The first branch of the loop of the 1-gon: the inertia map of `c₀`. -/
noncomputable abbrev oneGonB₀ : ProSigmaCompletion P (Multiplicative ℤ) →* proSigma P 0 3 :=
  ProSigmaCompletion.map (zpowersHom _ (oneGonGen false true))

/-- The second branch of the loop of the 1-gon: the inertia map of `c₁⁻¹`. -/
noncomputable abbrev oneGonB₁ : ProSigmaCompletion P (Multiplicative ℤ) →* proSigma P 0 3 :=
  ProSigmaCompletion.map (zpowersHom _ (oneGonGen false false))

/-- **The tempered fundamental group `π^temp(G^Σ)` of the stable 1-gon** (inverse limit of the
HNN level groups). -/
abbrev oneGonTempered : Type := loopGroup (oneGonB₀ P) (oneGonB₁ P)

/-- **The tree tower of `G^Σ` of the stable 1-gon** (bridge B1). -/
noncomputable abbrev oneGonTower : TreeTower (oneGonTempered P) (Level (oneGonB₀ P) (oneGonB₁ P)) :=
  tower (oneGonB₀ P) (oneGonB₁ P)

variable {P}

/-- A `π₁`-epimorphic approximator of `G^Σ` ([SemiAnbd] Def 2.3(ii)) is a level of the loop. -/
def oneGon_level_of_approximator (A : (oneGonSigma P).Approximator) :
    Level (oneGonB₀ P) (oneGonB₁ P) :=
  ⟨A.N (), A.normal (), A.isOpen (), A.compat false () () rfl rfl⟩

/-- **Bridge B2b for the 1-gon**: the base vertex system of `oneGonTower P` satisfies `HI`. -/
theorem oneGon_HI {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    (oneGonTower P).HI (baseSys (oneGonB₀ P) (oneGonB₁ P)) := by
  refine HI_baseSys fun n ↦ ?_
  obtain ⟨A, H, hM, hconj⟩ := oneGonSigma_totallyElevated hℓ hP () (n + 1)
  refine ⟨oneGon_level_of_approximator A, H, hM, fun q ↦ ⟨?_, ?_⟩⟩
  · rw [branch₀, MonoidHom.range_comp]
    exact hconj false true rfl q
  · rw [branch₁, MonoidHom.range_comp]
    exact hconj false false rfl q

/-- The kernel of a homomorphism `ρ` (with open fibres), restricted along the inertia map of `γ`,
lies in every open subgroup `V` of `ℤ^Σ` whose index divides the order of `ρ(γ)`. -/
lemma comap_ker_le {Q : Type} [Group Q] (ρ : proSigma P 0 3 →* Q)
    (hρo : ∀ q, IsOpen {x | ρ x = q}) (γ : SurfaceGroup 0 3)
    (V : Subgroup (ProSigmaCompletion P (Multiplicative ℤ))) [V.Normal]
    (hVo : IsOpen (V : Set (ProSigmaCompletion P (Multiplicative ℤ))))
    (hdvd : V.index ∣ orderOf (ρ (ProSigmaCompletion.eta P γ))) :
    (ρ.ker).comap (ProSigmaCompletion.map (zpowersHom _ γ)) ≤ V := by
  intro x hx
  rw [Subgroup.mem_comap, MonoidHom.mem_ker] at hx
  have hU : IsOpen {y | ρ (ProSigmaCompletion.map (zpowersHom _ γ) y) = 1 ∧
      (y : _ ⧸ V) = (x : _ ⧸ V)} := by
    refine ((hρo 1).preimage (ProSigmaCompletion.continuous_map _)).inter ?_
    have : {y : ProSigmaCompletion P (Multiplicative ℤ) | (y : _ ⧸ V) = (x : _ ⧸ V)} =
        x • (V : Set _) := by
      ext y
      simp only [Set.mem_setOf_eq, mem_leftCoset_iff, QuotientGroup.eq]
      exact ⟨fun h ↦ by simpa using inv_mem h, fun h ↦ by simpa using inv_mem h⟩
    have h2 : IsOpen {y : ProSigmaCompletion P (Multiplicative ℤ) | (y : _ ⧸ V) = (x : _ ⧸ V)} :=
      this ▸ hVo.smul x
    exact h2
  obtain ⟨w, hw1, hw2⟩ := ProSigmaCompletion.exists_eta_mem_of_isOpen hU ⟨hx, rfl⟩
  rw [ProSigmaCompletion.map_eta, zpowersHom_apply, map_zpow, map_zpow,
    ← orderOf_dvd_iff_zpow_eq_one] at hw1
  set g : ProSigmaCompletion P (Multiplicative ℤ) ⧸ V :=
    ((ProSigmaCompletion.eta P (Multiplicative.ofAdd (1 : ℤ)) : _) : _ ⧸ V)
  have hg : orderOf g ∣ orderOf (ρ (ProSigmaCompletion.eta P γ)) :=
    (orderOf_dvd_natCard g).trans (by rwa [← Subgroup.index])
  have hw' : w = Multiplicative.ofAdd (1 : ℤ) ^ Multiplicative.toAdd w := by
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  rw [← QuotientGroup.eq_one_iff, ← hw2, hw', map_zpow, QuotientGroup.mk_zpow]
  exact orderOf_dvd_iff_zpow_eq_one.1 ((Int.natCast_dvd_natCast.2 hg).trans hw1)

/-- **The levels separate the points of `Π^Σ_{0,3}`.** -/
theorem oneGon_sep (π : proSigma P 0 3) (hπ : π ≠ 1) :
    ∃ N : Level (oneGonB₀ P) (oneGonB₁ P), π ∉ N.1 := by
  -- an open normal subgroup `U` avoiding `π`
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := proSigma P 0 3) (isOpen_compl_singleton (x := π)) (Ne.symm hπ)
  -- the open subgroup `V = b₀⁻¹ U ∩ b₁⁻¹ U` of `ℤ^Σ` and its index `m`
  set V := U.toSubgroup.comap (oneGonB₀ P) ⊓ U.toSubgroup.comap (oneGonB₁ P)
  haveI : V.Normal := Subgroup.normal_inf_normal _ _
  have hVo : IsOpen (V : Set (ProSigmaCompletion P (Multiplicative ℤ))) :=
    (U.isOpen'.preimage (ProSigmaCompletion.continuous_map _)).inter
      (U.isOpen'.preimage (ProSigmaCompletion.continuous_map _))
  have hm := MaxProSigma.isSigmaNat_index_maxProSigma (P := P) V hVo
  -- a quotient in which all cusps have order `m³`
  obtain ⟨Q, _, _, _, ρ, -, hρo, -, hc, -, -, -⟩ :=
    exists_elevated_proSigma (P := P) (g := 0) (r := 3) (Nat.pos_of_ne_zero hm.1)
      (fun p hp hpm ↦ hm.2 p hp hpm) (by unfold IsHyperbolic; omega)
  have hord : ∀ β, orderOf (ρ (ProSigmaCompletion.eta P (oneGonGen false β))) = V.index ^ 3 := by
    rintro (_ | _)
    · simp only [oneGonGen, map_inv, orderOf_inv]; exact hc 1
    · exact hc 0
  have hdvd : ∀ β, V.index ∣ orderOf (ρ (ProSigmaCompletion.eta P (oneGonGen false β))) :=
    fun β ↦ hord β ▸ dvd_pow_self _ (by norm_num)
  have h₀ := comap_ker_le ρ hρo _ V hVo (hdvd true)
  have h₁ := comap_ker_le ρ hρo _ V hVo (hdvd false)
  -- the two branches pull back `ker ρ` to the same subgroup
  have hloop : ρ.ker.comap (oneGonB₀ P) = ρ.ker.comap (oneGonB₁ P) := by
    ext x
    simp only [Subgroup.mem_comap, MonoidHom.mem_ker]
    obtain ⟨k, hk, hk'⟩ := ProSigmaCompletion.exists_zpow_eq ρ hρo (oneGonGen false true)
      (oneGonGen false false) x
    rw [hk, hk', ← orderOf_dvd_iff_zpow_eq_one, ← orderOf_dvd_iff_zpow_eq_one, hord, hord]
  refine ⟨⟨U.toSubgroup ⊓ ρ.ker, Subgroup.normal_inf_normal _ _, U.isOpen'.inter (hρo 1), ?_⟩,
    fun h ↦ hU h.1 rfl⟩
  rw [Subgroup.comap_inf, Subgroup.comap_inf, inf_eq_right.2 (h₀.trans inf_le_left),
    inf_eq_right.2 (h₁.trans inf_le_right), hloop]

/-- **`π^temp(G^Σ)` of the stable 1-gon is temp-slim** ([SemiAnbd] Prop 3.6(iv), the argument of
Ex 3.10, for `G^Σ`), for every `Σ` containing a prime `ℓ`. -/
theorem oneGon_tempSlim {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) : TempSlim (oneGonTempered P) :=
  tempSlim_loopGroup oneGon_sep (oneGon_HI hℓ hP)
    ((tempSlim_iff_isSlim _).2 (SurfaceGroup.isSlim_proSigma (g := 0) (r := 3) (by norm_num)
      (by unfold IsHyperbolic; omega) hℓ hP))

end TemperedFundamentalGroups
