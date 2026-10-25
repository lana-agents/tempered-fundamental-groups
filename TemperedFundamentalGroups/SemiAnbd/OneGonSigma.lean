/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.Def24
import Pi1.Surface.ProSigma
import Pi1.Surface.SlimProSigma
import TemperedFundamentalGroups.SemiAnbd.TempSlimPi1

import Pi1.Surface.EstrangedProSigma
/-!
# The pro-`Σ` semi-graph of anabelioids of the stable 1-gon is totally elevated

The stable model of `E ∖ {0}` at a bad place (contraction of the `(0, 2)`-component `E'` of the
Tate model) has as dual semi-graph the **1-gon** `oneGon`: one vertex `v` (the projective line
with three special points, `(g, r) = (0, 3)`), one closed edge (the node, a loop at `v`) and one
open edge (the cusp at the origin). Its pro-`Σ` semi-graph of anabelioids `G^Σ` ([SemiAnbd]
Ex 2.10, Cor 3.11) is `oneGonSigma P`: vertex group `Π^Σ_{0,3}`, edge groups `ℤ^Σ`, branch
homomorphisms the cusp inertia maps of `c₀` and `c₁⁻¹` (the two branches of the node: the
inertia generators of the two branches at `xy = t` are inverse to each other) and `c₂` (the cusp).

* `ProSigmaCompletion.exists_zpow_eq`, `ProSigmaCompletion.range_comp_map_zpowersHom`: for a
  continuous homomorphism `ρ` from a pro-`Σ` completion to a finite group, the values on the
  images of `ℤ^Σ` are powers of the images of the generators (density of `ℤ` in `ℤ^Σ`);
* **`oneGonSigma_totallyElevated`** ([SemiAnbd] Def 2.4(i) for `G^Σ`, the "totally elevated" of
  Ex 2.10): if `Σ` contains a prime, `oneGonSigma P` is totally elevated (from
  `Pi1.SurfaceGroup.exists_elevated_proSigma`: all cusps of order exactly `n³`, so the two branches
  of the loop have the same kernel and the quotients form a `π₁`-epimorphic approximator);
* **`oneGonSigma_totallyEstranged`** ([SemiAnbd] Def 2.4(iv)): the branch inertia groups are
  estranged (pi1 `SurfaceGroup.cuspInertiaSigma_estranged_zero_three`).
* **`oneGonSigma_verticiallySlim`** ([SemiAnbd] Def 2.4(ii) for `G^Σ`): `Π^Σ_{0,3}` is slim
  (`Pi1.SurfaceGroup.isSlim_proSigma`).
-/

open CategoryTheory Pi1 Pi1.Profinite Pi1.SurfaceGroup
open scoped Pointwise

namespace Pi1.Profinite.ProSigmaCompletion

variable {P : ℕ → Prop} {Γ : Type} [Group Γ] {Q : Type*} [Group Q]

/-- Values of `ρ` on the images of `ℤ^Σ` under two elements `γ, γ'` are simultaneous powers of
`ρ(γ)`, `ρ(γ')` (the fibres of `ρ` are open and `ℤ` is dense in `ℤ^Σ`). -/
theorem exists_zpow_eq (ρ : ProSigmaCompletion P Γ →* Q) (hρ : ∀ q, IsOpen {x | ρ x = q})
    (γ γ' : Γ) (x : ProSigmaCompletion P (Multiplicative ℤ)) :
    ∃ k : ℤ, ρ (map (zpowersHom _ γ) x) = ρ (eta P γ) ^ k ∧
      ρ (map (zpowersHom _ γ') x) = ρ (eta P γ') ^ k := by
  have hU : IsOpen {y | ρ (map (zpowersHom _ γ) y) = ρ (map (zpowersHom _ γ) x) ∧
      ρ (map (zpowersHom _ γ') y) = ρ (map (zpowersHom _ γ') x)} :=
    ((hρ _).preimage (continuous_map _)).inter ((hρ _).preimage (continuous_map _))
  obtain ⟨w, hw1, hw2⟩ := exists_eta_mem_of_isOpen hU ⟨rfl, rfl⟩
  refine ⟨Multiplicative.toAdd w, ?_, ?_⟩
  · rw [← hw1, map_eta, zpowersHom_apply, map_zpow, map_zpow]
  · rw [← hw2, map_eta, zpowersHom_apply, map_zpow, map_zpow]

theorem range_comp_map_zpowersHom (ρ : ProSigmaCompletion P Γ →* Q)
    (hρ : ∀ q, IsOpen {x | ρ x = q}) (γ : Γ) :
    (ρ.comp (map (zpowersHom _ γ))).range = Subgroup.zpowers (ρ (eta P γ)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk, -⟩ := exists_zpow_eq ρ hρ γ γ x
    rw [MonoidHom.comp_apply, hk]
    exact Subgroup.zpow_mem_zpowers _ _
  · rw [Subgroup.zpowers_le]
    refine ⟨eta P (Multiplicative.ofAdd 1), ?_⟩
    rw [MonoidHom.comp_apply, map_eta, zpowersHom_apply, toAdd_ofAdd, zpow_one]

end Pi1.Profinite.ProSigmaCompletion

namespace TemperedFundamentalGroups

/-- **The stable 1-gon**: one vertex, the loop `false` (the node, both branches at the vertex) and
the open edge `true` (the cusp; only the branch `true` abuts). -/
def oneGon : SemiGraph.{0} where
  V := Unit
  E := Bool
  ζ
    | (false, _) => some ()
    | (true, true) => some ()
    | (true, false) => none

/-- The generators of the branch inertia groups of the 1-gon in `Π_{0,3}`: `c₀`, `c₁⁻¹` for the
two branches of the loop, `c₂` for the cusp. -/
def oneGonGen : Bool → Bool → SurfaceGroup 0 3
  | false, true => cusp 0
  | false, false => (cusp 1)⁻¹
  | true, _ => cusp 2

variable (P : ℕ → Prop)

/-- **The pro-`Σ` semi-graph of anabelioids `G^Σ` of the stable 1-gon** ([SemiAnbd] Ex 2.10):
vertex group `Π^Σ_{0,3}`, edge groups `ℤ^Σ`, branch maps the cusp inertia maps. -/
noncomputable def oneGonSigma : SemiGraphOfAnabelioids.{0, 0} oneGon where
  vGrp _ := ProfiniteGrp.of (SurfaceGroup.proSigma P 0 3)
  eGrp _ := ProfiniteGrp.of (ProSigmaCompletion P (Multiplicative ℤ))
  br e β _ _ := ProfiniteGrp.ofHom
    ⟨ProSigmaCompletion.map (zpowersHom _ (oneGonGen e β)), ProSigmaCompletion.continuous_map _⟩

variable {P}

lemma oneGonSigma_brHom (e : Bool) (β : Bool) (v : Unit) (h : oneGon.ζ (e, β) = some v) :
    (oneGonSigma P).brHom e β v h = ProSigmaCompletion.map (zpowersHom _ (oneGonGen e β)) :=
  rfl

/-- **`G^Σ` of the stable 1-gon is totally elevated** ([SemiAnbd] Def 2.4(i), Ex 2.10), for any
`Σ` containing a prime `ℓ`. -/
theorem oneGonSigma_totallyElevated {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    (oneGonSigma P).TotallyElevated := by
  intro v M
  set n := ℓ ^ M
  have hn : 0 < n := pow_pos hℓ.pos M
  have hMn : M ≤ n := (Nat.lt_pow_self hℓ.one_lt).le
  have hS : ∀ p, p.Prime → p ∣ n → P p := fun p hp hpn ↦
    (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hpn) ▸ hP
  obtain ⟨Q, _, _, _, ρ, N, hρo, hρs, hc, -, hN, hconj⟩ :=
    exists_elevated_proSigma (P := P) (g := 0) (r := 3) hn hS (by unfold IsHyperbolic; omega)
  -- the generators of the branch images have order `n³`
  have hord : ∀ e β, orderOf (ρ (ProSigmaCompletion.eta P (oneGonGen e β))) = n ^ 3 := by
    rintro (_ | _) (_ | _)
    · simp only [oneGonGen, map_inv, orderOf_inv]; exact hc 1
    · exact hc 0
    · exact hc 2
    · exact hc 2
  -- the images of the branch groups are generated by the images of the generators
  have hconj' : ∀ e β (q' : Q), N ⊓ (ConjAct.toConjAct q' •
      Subgroup.zpowers (ρ (ProSigmaCompletion.eta P (oneGonGen e β)))) = ⊥ := by
    have hj : ∀ (j : Fin 3) (q' : Q), N ⊓ (ConjAct.toConjAct q' •
        Subgroup.zpowers (ρ (ProSigmaCompletion.eta P (cusp j)))) = ⊥ := fun j q' ↦ by
      rw [← ProSigmaCompletion.range_comp_map_zpowersHom ρ hρo (cusp j)]
      exact hconj j q'
    rintro (_ | _) (_ | _) q'
    · simp only [oneGonGen, map_inv, Subgroup.zpowers_inv]; exact hj 1 q'
    · exact hj 0 q'
    · exact hj 2 q'
    · exact hj 2 q'
  have hloop : ∀ x : ProSigmaCompletion P (Multiplicative ℤ),
      ρ (ProSigmaCompletion.map (zpowersHom _ (oneGonGen false true)) x) = 1 ↔
        ρ (ProSigmaCompletion.map (zpowersHom _ (oneGonGen false false)) x) = 1 := fun x ↦ by
    obtain ⟨k, hk, hk'⟩ := ProSigmaCompletion.exists_zpow_eq ρ hρo (oneGonGen false true)
      (oneGonGen false false) x
    rw [hk, hk', ← orderOf_dvd_iff_zpow_eq_one, ← orderOf_dvd_iff_zpow_eq_one, hord, hord]
  refine (oneGonSigma P).exists_elevated_of_surjective
    { N := fun _ ↦ ρ.ker
      isOpen := fun _ ↦ hρo 1
      normal := fun _ ↦ ρ.normal_ker
      compat := ?_ } ρ hρs rfl N (hMn.trans hN) fun e β h q ↦ ?_
  · rintro (_ | _) v₁ v₂ h₁ h₂
    · ext x
      simp only [Subgroup.mem_comap, oneGonSigma_brHom]
      exact hloop x
    · exact absurd h₂ (by simp [oneGon])
  · rw [SemiGraphOfAnabelioids.brRange, MonoidHom.map_range, oneGonSigma_brHom]
    have := ProSigmaCompletion.range_comp_map_zpowersHom ρ hρo (oneGonGen e β)
    have h2 := hconj' e β q
    rw [← this] at h2
    exact h2

/-- **`G^Σ` of the stable 1-gon is verticially slim** ([SemiAnbd] Def 2.4(ii), Ex 2.10), for any
`Σ` containing a prime `ℓ`. -/
theorem oneGonSigma_verticiallySlim {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    (oneGonSigma P).VerticiallySlim := fun _ ↦
  (tempSlim_iff_isSlim _).2
    (SurfaceGroup.isSlim_proSigma (g := 0) (r := 3) (by norm_num) (by unfold IsHyperbolic; omega)
      hℓ hP)

/-- The cusp index of a branch of the 1-gon: `c₀`, `c₁` for the two branches of the loop, `c₂` for
the cusp. -/
def oneGonIdx : Bool → Bool → Fin 3
  | false, true => 0
  | false, false => 1
  | true, _ => 2

/-- The range of `ℤ^Σ → Γ^Σ`, `1 ↦ γ⁻¹`, is that of `1 ↦ γ`. -/
theorem range_map_zpowersHom_inv {Γ : Type} [Group Γ] (γ : Γ) :
    (ProSigmaCompletion.map (P := P) (zpowersHom _ γ⁻¹)).range =
      (ProSigmaCompletion.map (P := P) (zpowersHom _ γ)).range := by
  set ν : Multiplicative ℤ →* Multiplicative ℤ := zpowersHom _ (Multiplicative.ofAdd (-1))
  have hν : (zpowersHom _ γ).comp ν = zpowersHom _ γ⁻¹ := by
    ext; simp [ν]
  have hνν : ν.comp ν = MonoidHom.id _ := by
    ext; simp [ν]
  have hsurj : Function.Surjective (ProSigmaCompletion.map (P := P) ν) := fun x ↦
    ⟨ProSigmaCompletion.map ν x, by
      rw [← MonoidHom.comp_apply, ProSigmaCompletion.map_comp, hνν, ProSigmaCompletion.map_id,
        MonoidHom.id_apply]⟩
  rw [← hν, ← ProSigmaCompletion.map_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr hsurj]
  exact (MonoidHom.range_eq_map _).symm

theorem oneGonSigma_brRange (e β : Bool) (h : oneGon.ζ (e, β) = some ()) :
    (oneGonSigma P).brRange e β () h =
      (SurfaceGroup.cuspInertiaSigma P (g := 0) (r := 3) (oneGonIdx e β)).range := by
  rw [SemiGraphOfAnabelioids.brRange, oneGonSigma_brHom]
  rcases e <;> rcases β
  · exact range_map_zpowersHom_inv _
  · rfl
  · exact absurd h (by simp [oneGon])
  · rfl

/-- **`G^Σ` of the stable 1-gon is totally estranged** ([SemiAnbd] Def 2.4(iv), Ex 2.10): the
branch inertia groups `⟨c₀⟩, ⟨c₁⟩, ⟨c₂⟩` of `Π^Σ_{0,3}` are pairwise conjugacy-disjoint and
malnormal (pi1 `SurfaceGroup.cuspInertiaSigma_estranged_zero_three`), for every `Σ`. -/
theorem oneGonSigma_totallyEstranged : (oneGonSigma P).TotallyEstranged := by
  intro e β v h e' β' h' g hr
  obtain rfl : v = () := rfl
  rw [oneGonSigma_brRange e β h, oneGonSigma_brRange e' β' h']
  obtain ⟨h1, h2⟩ := SurfaceGroup.cuspInertiaSigma_estranged_zero_three (P := P)
  by_cases hb : (e', β') = (e, β)
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hb
    rcases hr with hr | hr
    · exact absurd hb hr
    · rw [oneGonSigma_brRange _ _ h] at hr
      exact h2 _ g hr
  · have hf : oneGon.ζ (true, false) ≠ some () := by intro hx; cases hx
    refine h1 _ _ ?_ g
    intro hidx
    apply hb
    rcases e <;> rcases β <;> rcases e' <;> rcases β' <;>
      first | rfl | exact absurd h hf | exact absurd h' hf | (simp [oneGonIdx] at hidx)

end TemperedFundamentalGroups
