/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.OneOneHNN

/-!
# The group-theoretic assembly of Route B (MR13 plan, run 8 (2), run 9 next step 3)

Route B identifies the vertex group `D_v` of the pro-`Σ` geometric fundamental group `Δ^Σ` of
the Tate curve `E ∖ {O}` with `Π^Σ_{0,3}`: `Π^Σ_{1,1}` is the pro-`Σ` HNN extension of
`Π^Σ_{0,3}` (`OneOneHNN.hnnLift`), it maps onto `Δ^Σ = HNN^Σ(D_v)` if `Π^Σ_{0,3} → D_v` is onto,
`Δ^Σ ≅ Π^Σ_{1,1}` abstractly (PI1TOP), so by Hopficity the map is an isomorphism and the vertex
map is injective. This file proves the abstract statements, for any profinite pro-`Σ` group `H`
(later `Δ^Σ`):

* **`RouteB.eq_top_of_sup_openNormal`**: a closed subgroup `C` of a profinite group with
  `N ⊔ C = ⊤` for every open normal `N` is everything;
* **`RouteB.hnnLift_surjective`**: if `β : Π^Σ_{0,3} → H` and `τ ∈ H` satisfy the HNN relation
  and `β(Π^Σ_{0,3})` and `τ` generate `H` modulo every open normal subgroup, `hnnLift β τ` is onto;
* **`RouteB.hnnLift_bijective`**, **`RouteB.hnnEquiv`** (`Π^Σ_{1,1} ≃ₜ* H`) if moreover
  `H ≃ₜ* Π^Σ_{1,1}` (Hopficity, `IsTopFG.bijective_of_surjective_of_equiv`);
* **`RouteB.injective_of_hnn`**: then `β` is injective (`OneOneHNN.vtxSigma_injective`, `Σ ∋ ℓ`),
  and **`RouteB.isClosedEmbedding_of_hnn`**: a closed embedding — `Π^Σ_{0,3} ≅ β(Π^Σ_{0,3})`;
* **`RouteB.exists_mem_iInter_of_saturated`** (the compactness step of B4): in a compact group,
  a decreasing family `A N ⊆ G × G` indexed by the open normal subgroups, each nonempty and stable
  under right multiplication by `N × N`, has a common point — e.g. pairs `(β(c₀), β(c₁))` with
  prescribed behaviour on the finite quotients `D_v/N` (generators of the branch inertias);
* **`RouteB.pairHom`**: the continuous homomorphism `Π^Σ_{0,3} → H`, `c₀ ↦ g₀`, `c₁ ↦ g₁`
  (`Π_{0,3}` is free on `c₀, c₁`), and **`RouteB.pairHom_surjective`**: it is onto if `g₀, g₁`
  generate `H` modulo every open normal subgroup.
-/

universe u

open Pi1 Pi1.Profinite Pi1.SurfaceGroup Pi1.SurfaceGen Pi1.Profinite.ProSigmaCompletion

namespace TemperedFundamentalGroups

namespace RouteB

/-! ### Density modulo open normal subgroups -/

/-- **A closed subgroup which is everything modulo every open normal subgroup is everything.** -/
theorem eq_top_of_sup_openNormal {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] {C : Subgroup G} (hC : IsClosed (C : Set G))
    (h : ∀ N : OpenNormalSubgroup G, (N : Subgroup G) ⊔ C = ⊤) : C = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  by_contra hx
  have hU : IsOpen ((fun y ↦ y * x) ⁻¹' (C : Set G)ᶜ) :=
    hC.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU
    (by simpa using hx)
  have hxN : x ∈ ((N : Subgroup G) ⊔ C : Subgroup G) := by rw [h N]; trivial
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hxN
  obtain ⟨n, hn, c, hc, rfl⟩ := hxN
  have hn' : n⁻¹ ∈ (N : Set G) := (N : Subgroup G).inv_mem hn
  have := hN hn'
  simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe] at this
  exact this (by rwa [inv_mul_cancel_left])

/-! ### The HNN map onto `H` -/

section HNN

open OneOneHNN

variable {P : ℕ → Prop} {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [TotallyDisconnectedSpace H]
  (hH : ∀ M : Subgroup H, IsOpen (M : Set H) → M.Normal → IsSigmaNat P M.index)
  (β : proSigma P 0 3 →* H) (hβ : Continuous β) (τ : H)
  (hτ : ∀ x, τ * β (oneGonB₀ P x) * τ⁻¹ = β (oneGonB₁ P x))
  (hgen : ∀ N : OpenNormalSubgroup H,
    (N : Subgroup H) ⊔ Subgroup.closure (Set.range β ∪ {τ}) = ⊤)

include hβ hτ hgen in
/-- **The HNN map is onto** if `β(Π^Σ_{0,3})` and `τ` generate `H` modulo every open normal
subgroup. -/
theorem hnnLift_surjective : Function.Surjective (hnnLift hH β τ) := by
  have hcl : IsClosed ((hnnLift hH β τ).range : Set H) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_hnnLift hH β τ)).isClosed
  have hle : Subgroup.closure (Set.range β ∪ {τ}) ≤ (hnnLift hH β τ).range := by
    rw [Subgroup.closure_le]
    rintro _ (⟨π, rfl⟩ | h)
    · exact ⟨vtxSigma P π, hnnLift_vtxSigma hH β hβ τ hτ π⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact ⟨tSigma P, hnnLift_tSigma hH β τ⟩
  have htop := eq_top_of_sup_openNormal hcl fun N ↦
    eq_top_iff.mpr ((hgen N) ▸ sup_le_sup_left hle _)
  exact MonoidHom.range_eq_top.mp htop

include hβ hτ hgen in
/-- **Hopficity for the HNN map**: if moreover `H ≃ₜ* Π^Σ_{1,1}` (abstractly), the HNN map
`Π^Σ_{1,1} → H` is bijective. -/
theorem hnnLift_bijective (e : H ≃ₜ* proSigma P 1 1) : Function.Bijective (hnnLift hH β τ) :=
  (isTopFG_proSigma11 P).bijective_of_surjective_of_equiv (continuous_hnnLift hH β τ)
    (hnnLift_surjective hH β hβ τ hτ hgen) e

include hH hβ hτ hgen in
/-- **`Π^Σ_{1,1} ≃ₜ* H`** through the HNN map. -/
noncomputable def hnnEquiv (e : H ≃ₜ* proSigma P 1 1) : proSigma P 1 1 ≃ₜ* H :=
  haveI : T2Space H := e.toHomeomorph.isEmbedding.t2Space
  let f := MulEquiv.ofBijective (hnnLift hH β τ) (hnnLift_bijective hH β hβ τ hτ hgen e)
  let h := (continuous_hnnLift hH β τ).homeoOfEquivCompactToT2 (f := f.toEquiv)
  { f with
    continuous_toFun := continuous_hnnLift hH β τ
    continuous_invFun := h.symm.continuous }

@[simp] lemma hnnEquiv_apply (e : H ≃ₜ* proSigma P 1 1) (x : proSigma P 1 1) :
    hnnEquiv hH β hβ τ hτ hgen e x = hnnLift hH β τ x := rfl

include hH hβ hτ hgen in
/-- **The vertex map is injective**: `β` is injective (`Σ ∋ ℓ`). -/
theorem injective_of_hnn (e : H ≃ₜ* proSigma P 1 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    Function.Injective β := by
  have h : ⇑β = hnnLift hH β τ ∘ vtxSigma P :=
    funext fun π ↦ (hnnLift_vtxSigma hH β hβ τ hτ π).symm
  rw [h]
  exact (hnnLift_bijective hH β hβ τ hτ hgen e).1.comp (vtxSigma_injective hℓ hP)

include hH hβ hτ hgen in
/-- **`Π^Σ_{0,3}` is isomorphic to its image**: `β` is a closed embedding. -/
theorem isClosedEmbedding_of_hnn (e : H ≃ₜ* proSigma P 1 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    Topology.IsClosedEmbedding β :=
  haveI : T2Space H := e.toHomeomorph.isEmbedding.t2Space
  hβ.isClosedEmbedding (injective_of_hnn hH β hβ τ hτ hgen e hℓ hP)

end HNN

/-! ### Choosing the images of the generators (compactness) -/

section Choice

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A subset of `G × G` stable under right multiplication by `N × N` (`N` open) is closed. -/
lemma isClosed_of_saturated (N : OpenSubgroup G) {A : Set (G × G)}
    (hsat : ∀ p ∈ A, ∀ n₀ ∈ N, ∀ n₁ ∈ N, (p.1 * n₀, p.2 * n₁) ∈ A) : IsClosed A := by
  refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun q hq ↦ ?_)
  refine ⟨(fun p : G × G ↦ (q.1⁻¹ * p.1, q.2⁻¹ * p.2)) ⁻¹' ((N : Set G) ×ˢ (N : Set G)),
    fun p hp hpA ↦ hq ?_, ?_, ?_⟩
  · have h := hsat p hpA _ ((N : Subgroup G).inv_mem hp.1) _ ((N : Subgroup G).inv_mem hp.2)
    simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using h
  · exact (N.isOpen.prod N.isOpen).preimage
      ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  · simp only [Set.mem_preimage, inv_mul_cancel, Set.mem_prod, SetLike.mem_coe]
    exact ⟨N.one_mem, N.one_mem⟩

variable [CompactSpace G]

/-- **A compatible family of nonempty saturated sets of pairs has a common point** (the
compactness step of B4: choosing `(β(c₀), β(c₁))` with prescribed images in all finite quotients
`G/N`). -/
theorem exists_mem_iInter_of_saturated (A : OpenNormalSubgroup G → Set (G × G))
    (hsat : ∀ N, ∀ p ∈ A N, ∀ n₀ ∈ N, ∀ n₁ ∈ N, (p.1 * n₀, p.2 * n₁) ∈ A N)
    (hne : ∀ N, (A N).Nonempty) (hmono : ∀ N N', N ≤ N' → A N ⊆ A N') :
    ∃ p : G × G, ∀ N, p ∈ A N := by
  haveI : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⊤, isNormal' := ⟨fun _ _ _ ↦ trivial⟩ }⟩
  have hcl : ∀ N, IsClosed (A N) := fun N ↦ isClosed_of_saturated N.toOpenSubgroup (hsat N)
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed A
    (fun N N' ↦ ⟨N ⊓ N', hmono _ _ inf_le_left, hmono _ _ inf_le_right⟩) hne
    (fun N ↦ (hcl N).isCompact) hcl
  exact ⟨p, Set.mem_iInter.mp hp⟩

end Choice

/-! ### Homomorphisms out of `Π^Σ_{0,3}` from pairs -/

section Pair

open OneOneHNN

variable {P : ℕ → Prop} {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [TotallyDisconnectedSpace H]
  (hH : ∀ M : Subgroup H, IsOpen (M : Set H) → M.Normal → IsSigmaNat P M.index)

/-- The discrete homomorphism `Π_{0,3} → H`, `c₀ ↦ g₀`, `c₁ ↦ g₁`, `c₂ ↦ (g₀ g₁)⁻¹`. -/
def pairDisc (g₀ g₁ : H) : SurfaceGroup 0 3 →* H :=
  SurfaceGroup.lift ![] ![] ![g₀, g₁, (g₀ * g₁)⁻¹] (by simp [commProd, ordProd])

/-- **The continuous homomorphism `Π^Σ_{0,3} → H`, `c₀ ↦ g₀`, `c₁ ↦ g₁`.** -/
noncomputable def pairHom (g₀ g₁ : H) : proSigma P 0 3 →* H := liftPro hH (pairDisc g₀ g₁)

theorem continuous_pairHom (g₀ g₁ : H) : Continuous (pairHom hH g₀ g₁) := continuous_liftPro _ _

@[simp] theorem pairHom_c₀ (g₀ g₁ : H) : pairHom hH g₀ g₁ (eta P (cusp 0)) = g₀ := by
  simp [pairHom, pairDisc]

@[simp] theorem pairHom_c₁ (g₀ g₁ : H) : pairHom hH g₀ g₁ (eta P (cusp 1)) = g₁ := by
  simp [pairHom, pairDisc]

/-- **`pairHom` is onto** if `g₀, g₁` generate `H` modulo every open normal subgroup. -/
theorem pairHom_surjective (g₀ g₁ : H)
    (hgen : ∀ N : OpenNormalSubgroup H, (N : Subgroup H) ⊔ Subgroup.closure {g₀, g₁} = ⊤) :
    Function.Surjective (pairHom hH g₀ g₁) := by
  have hcl : IsClosed ((pairHom hH g₀ g₁).range : Set H) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_pairHom hH g₀ g₁)).isClosed
  have hle : Subgroup.closure {g₀, g₁} ≤ (pairHom hH g₀ g₁).range := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact ⟨_, (pairHom_c₀ hH g₀ g₁).trans hx.symm⟩
    · exact ⟨_, (pairHom_c₁ hH g₀ g₁).trans (Set.mem_singleton_iff.mp hx).symm⟩
  have htop := eq_top_of_sup_openNormal hcl fun N ↦
    eq_top_iff.mpr ((hgen N) ▸ sup_le_sup_left hle _)
  exact MonoidHom.range_eq_top.mp htop

end Pair

end RouteB

end TemperedFundamentalGroups
