/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.Anabelioid
import TemperedFundamentalGroups.SemiAnbd.TempSlim

/-!
# Elevated vertices, verticial slimness, estranged edges ([SemiAnbd] Def 2.3, 2.4), group form

For a semi-graph of anabelioids `𝒢` in group form (`SemiGraphOfAnabelioids`: profinite vertex
groups `Π_v`, edge groups `Π_e`, branch homomorphisms `Π_e → Π_v`; `Π_b ⊆ Π_v` the image of the
branch `b`):

* `SemiGraphOfAnabelioids.Approximator` ([SemiAnbd] Def 2.3(ii), `π₁`-epimorphic, in the image
  form of Remark 2.3.1): open normal subgroups `N_v ⊴ Π_v` such that for every closed edge the two
  branches pull them back to the same subgroup of `Π_e`; the approximating semi-graph of
  anabelioids `𝒢'` has vertex groups `Π_v ⧸ N_v` and edge groups `Π_e ⧸ br⁻¹ N_v` (embedded in the
  vertex quotients through both branches; bounded order since `𝔾` is finite in the cases used).
* **`SemiGraphOfAnabelioids.IsElevated v`** ([SemiAnbd] Def 2.4(i)): for every `M` there is an
  approximator and a subgroup `N ⊆ Π_v ⧸ N_v` of order `≥ M` meeting all conjugates of the images
  of all branches abutting to `v` trivially; `TotallyElevated`.
* **`SemiGraphOfAnabelioids.VerticiallySlim`** ([SemiAnbd] Def 2.4(ii)): every `Π_v` is slim
  (`TempSlim`: open subgroups have trivial centralizer; `tempSlim_iff_isSlim`).
* **`SemiGraphOfAnabelioids.IsEstranged e`**, `IsAloof e` ([SemiAnbd] Def 2.4(iv)): for a branch `b`
  of `e` abutting to `v` and `g ∈ Π_v`, `Π_b ∩ g Π_{b'} g⁻¹` is trivial (resp. of infinite index in
  `Π_b`) whenever `b'` is another branch abutting to `v`, or `b' = b` and `g ∉ Π_b`;
  `TotallyEstranged`, `TotallyAloof`, `IsAloof.of_isEstranged` (Remark 2.4.1).

These are the hypotheses of [SemiAnbd] Thm 3.7 / Cor 3.9 for the pro-`Σ` semi-graph of
anabelioids `G^Σ` of a stable curve (Ex 2.10), the input of the bridges to the tree tower
`T(G^Σ)` (MR12 T3, bridge B0; see `TreeTower.Elevated` for the tower form of (i)).
-/

universe u w

open CategoryTheory
open scoped Pointwise

namespace TemperedFundamentalGroups

namespace SemiGraphOfAnabelioids

variable {𝔾 : SemiGraph.{u}} (𝒢 : SemiGraphOfAnabelioids.{u, w} 𝔾)

/-- **A `π₁`-epimorphic approximator** ([SemiAnbd] Def 2.3(ii), image form of Remark 2.3.1):
open normal subgroups `N_v` of the vertex groups whose pull-backs along the two branches of every
closed edge agree. -/
structure Approximator where
  /-- The kernels `N_v` of the vertex quotients `Π_v ↠ π₁(𝒢'_v)`. -/
  N : ∀ v : 𝔾.V, Subgroup (𝒢.vGrp v)
  isOpen : ∀ v, IsOpen (N v : Set (𝒢.vGrp v))
  normal : ∀ v, (N v).Normal
  /-- The two branches of a closed edge pull back the vertex kernels to the same subgroup of
  `Π_e` (the kernel of `Π_e ↠ π₁(𝒢'_e)`). -/
  compat : ∀ (e : 𝔾.E) (v₁ v₂ : 𝔾.V) (h₁ : 𝔾.ζ (e, true) = some v₁)
    (h₂ : 𝔾.ζ (e, false) = some v₂),
    (N v₁).comap (𝒢.brHom e true v₁ h₁) = (N v₂).comap (𝒢.brHom e false v₂ h₂)

attribute [instance] Approximator.normal

/-- The image `Π_b ⊆ Π_v` of the branch `b = (e, β)` abutting to `v`. -/
def brRange (e : 𝔾.E) (β : Bool) (v : 𝔾.V) (h : 𝔾.ζ (e, β) = some v) : Subgroup (𝒢.vGrp v) :=
  (𝒢.brHom e β v h).range

/-- **Elevated vertex** ([SemiAnbd] Def 2.4(i)): for every `M ≥ 1` there are a `π₁`-epimorphic
approximator `𝒢 → 𝒢'` and a subgroup `N_M ⊆ π₁(𝒢'_v)` of order `≥ M` with trivial intersection
with all conjugates, in `π₁(𝒢'_v)`, of the images of the edge groups of all branches abutting
to `v`. -/
def IsElevated (v : 𝔾.V) : Prop :=
  ∀ M : ℕ, ∃ (A : 𝒢.Approximator) (H : Subgroup (𝒢.vGrp v ⧸ A.N v)), M ≤ Nat.card H ∧
    ∀ (e : 𝔾.E) (β : Bool) (h : 𝔾.ζ (e, β) = some v) (q : 𝒢.vGrp v ⧸ A.N v),
      H ⊓ (ConjAct.toConjAct q • (𝒢.brRange e β v h).map (QuotientGroup.mk' (A.N v))) = ⊥

/-- **Totally elevated** ([SemiAnbd] Def 2.4(i)): every vertex is elevated. -/
def TotallyElevated : Prop := ∀ v, 𝒢.IsElevated v

/-- **Verticially slim** ([SemiAnbd] Def 2.4(ii)): every vertex group is slim. -/
def VerticiallySlim : Prop := ∀ v, TempSlim (𝒢.vGrp v)

/-- The pairs of a branch `b'` abutting to `v` and `g ∈ Π_v` that [SemiAnbd] Def 2.4(iv)
compares with the branch `b = (e, β)`: `b' ≠ b`, or `b' = b` and `g ∉ Π_b`. -/
def Rival (e : 𝔾.E) (β : Bool) (v : 𝔾.V) (h : 𝔾.ζ (e, β) = some v) (e' : 𝔾.E) (β' : Bool)
    (g : 𝒢.vGrp v) : Prop :=
  (e', β') ≠ (e, β) ∨ g ∉ 𝒢.brRange e β v h

/-- **Estranged edge** ([SemiAnbd] Def 2.4(iv)): for every branch `b` of `e` abutting to a vertex
`v`, every `g ∈ Π_v` and every branch `b'` abutting to `v` with `b' ≠ b` (or `b' = b` and
`g ∉ Π_b`), `Π_b ∩ g Π_{b'} g⁻¹ = 1`. -/
def IsEstranged (e : 𝔾.E) : Prop :=
  ∀ (β : Bool) (v : 𝔾.V) (h : 𝔾.ζ (e, β) = some v) (e' : 𝔾.E) (β' : Bool)
    (h' : 𝔾.ζ (e', β') = some v) (g : 𝒢.vGrp v), 𝒢.Rival e β v h e' β' g →
      𝒢.brRange e β v h ⊓ (ConjAct.toConjAct g • 𝒢.brRange e' β' v h') = ⊥

/-- **Aloof edge** ([SemiAnbd] Def 2.4(iv)): the intersections of `Π_b` with its rivals have
infinite index in `Π_b`. -/
def IsAloof (e : 𝔾.E) : Prop :=
  ∀ (β : Bool) (v : 𝔾.V) (h : 𝔾.ζ (e, β) = some v) (e' : 𝔾.E) (β' : Bool)
    (h' : 𝔾.ζ (e', β') = some v) (g : 𝒢.vGrp v), 𝒢.Rival e β v h e' β' g →
      ((𝒢.brRange e β v h ⊓ (ConjAct.toConjAct g • 𝒢.brRange e' β' v h')).subgroupOf
        (𝒢.brRange e β v h)).index = 0

/-- **Totally estranged**: every edge is estranged. -/
def TotallyEstranged : Prop := ∀ e, 𝒢.IsEstranged e

/-- **Totally aloof**: every edge is aloof. -/
def TotallyAloof : Prop := ∀ e, 𝒢.IsAloof e

/-- **Elevation from a quotient**: if the vertex kernel of an approximator is the kernel of a
surjection `ρ : Π_v ↠ Q` and `N ≤ Q` meets all conjugates of the images `ρ(Π_b)` of the branches
abutting to `v` trivially, then the transported subgroup witnesses [SemiAnbd] Def 2.4(i) for `M`. -/
theorem exists_elevated_of_surjective {v : 𝔾.V} {M : ℕ} (A : 𝒢.Approximator) {Q : Type*}
    [Group Q] (ρ : 𝒢.vGrp v →* Q) (hρ : Function.Surjective ρ) (hA : A.N v = ρ.ker)
    (N : Subgroup Q) (hN : M ≤ Nat.card N)
    (hc : ∀ (e : 𝔾.E) (β : Bool) (h : 𝔾.ζ (e, β) = some v) (q : Q),
      N ⊓ (ConjAct.toConjAct q • (𝒢.brRange e β v h).map ρ) = ⊥) :
    ∃ (A : 𝒢.Approximator) (H : Subgroup (𝒢.vGrp v ⧸ A.N v)), M ≤ Nat.card H ∧
      ∀ (e : 𝔾.E) (β : Bool) (h : 𝔾.ζ (e, β) = some v) (q : 𝒢.vGrp v ⧸ A.N v),
        H ⊓ (ConjAct.toConjAct q • (𝒢.brRange e β v h).map (QuotientGroup.mk' (A.N v))) = ⊥ := by
  let φ : 𝒢.vGrp v ⧸ A.N v ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hA).trans (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  have hφ : ∀ z, φ (QuotientGroup.mk' (A.N v) z) = ρ z := fun _ ↦ rfl
  refine ⟨A, N.comap φ.toMonoidHom, ?_, fun e β h q ↦ ?_⟩
  · have : Nat.card (N.comap φ.toMonoidHom) = Nat.card N :=
      Nat.card_congr ((Equiv.subtypeEquiv φ.toEquiv fun _ ↦ Iff.rfl).trans (Equiv.refl _))
    rw [this]
    exact hN
  · rw [eq_bot_iff]
    rintro x ⟨hxN, hxB⟩
    rw [Subgroup.mem_bot]
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hxB
    have hmem : φ (ConjAct.toConjAct q • QuotientGroup.mk' (A.N v) z) ∈
        N ⊓ (ConjAct.toConjAct (φ q) • (𝒢.brRange e β v h).map ρ) := by
      refine ⟨hxN, (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨ρ z, ⟨z, hz, rfl⟩, ?_⟩⟩
      simp only [ConjAct.toConjAct_smul, map_mul, map_inv, hφ]
    rw [hc e β h (φ q), Subgroup.mem_bot] at hmem
    exact φ.injective (hmem.trans (map_one φ).symm)

variable {𝒢}

/-- **Estranged edges are aloof** when the branch images are infinite ([SemiAnbd] Remark 2.4.1;
the trivial subgroup has infinite index in an infinite group). -/
theorem IsAloof.of_isEstranged {e : 𝔾.E} (he : 𝒢.IsEstranged e)
    (hinf : ∀ (β : Bool) (v : 𝔾.V) (h : 𝔾.ζ (e, β) = some v), Infinite (𝒢.brRange e β v h)) :
    𝒢.IsAloof e := by
  intro β v h e' β' h' g hr
  rw [he β v h e' β' h' g hr, Subgroup.bot_subgroupOf, Subgroup.index_bot]
  haveI := hinf β v h
  exact Nat.card_eq_zero_of_infinite

theorem TotallyAloof.of_totallyEstranged (he : 𝒢.TotallyEstranged)
    (hinf : ∀ (e : 𝔾.E) (β : Bool) (v : 𝔾.V) (h : 𝔾.ζ (e, β) = some v),
      Infinite (𝒢.brRange e β v h)) : 𝒢.TotallyAloof :=
  fun e ↦ IsAloof.of_isEstranged (he e) (hinf e)

end SemiGraphOfAnabelioids

end TemperedFundamentalGroups
