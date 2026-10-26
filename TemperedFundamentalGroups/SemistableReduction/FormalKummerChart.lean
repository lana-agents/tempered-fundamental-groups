/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerAssemble
import TemperedFundamentalGroups.SemistableReduction.EtaleResidue

/-!
# The formal Kummer form of the special fibre of a chart (MR12 T2 S5.4)

Let `R` be a Noetherian `O`-algebra (a chart of a model over the level ring `O`, residue map
`θ : O → k` onto a separably closed field), `x, y ∈ R` with `x y = ϖⁿ` (`θ ϖ = 0`, `n ≥ 1`) the
node coordinates, `B` an `R`-algebra (the normalisation of the chart in a cover) and `𝔪ⱼ` finitely
many `k`-rational maximal ideals of `R` over `ϖ` (the nodes). If `B` is tamely Kummer at every
`𝔪ⱼ` (`IsKummerNormAt ϖ n M' x y B 𝔪ⱼ`, e.g. from `IsTameKummerAt.isKummerNormAt`), and the nodes
are exactly the zero set of `f̄` on the special fibre `R̄ = R/J`, then
(**`FormalKummer.exists_kummer`**) the special fibre `C = B/JB` is formally Kummer along `V(f̄)`:

  `R̂ ⊗_{R̄} C ≅ ∏_{(j, i)} (R̂/(1 − εⱼ)) ⊗_{k[u,v]/(uv)} k[s,t]/(st)`  (`u ↦ s^{dⱼᵢ}`, `dⱼᵢ ∣ M'`)

with respect to any formal node coordinates `φ : k[u,v]/(uv) → R̂` with `φ u = x̄`, `φ v = ȳ`:
the `kummer` field of `Admissible.Covering` (lead decision D1 after continuation 28: the split form
holds after a finite separable constant extension; here the residue field is separably closed, so
the étale neighbourhoods of `IsKummerNormAt` have trivial residue field extensions,
`EtaleResidue.surjective_of_isSepClosed'`).

Proof: `FormalKummer.nodeEquiv` at every node, assembled by `FormalKummer.assembleEquiv`.
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

namespace FormalKummer

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]

attribute [local instance] algRN

/-- The special fibre of an ideal containing `J`. -/
abbrev sIdeal (𝔪 : Ideal R) : Ideal (Rs θ R) := 𝔪.map (Ideal.Quotient.mk (J θ (R := R)))

variable (θ) in
/-- The completion of the special fibre at a node. -/
abbrev Tn (𝔪 : Ideal R) : Type u := AdicCompletion (sIdeal (θ := θ) 𝔪) (Rs θ R)

/-- **The local formal Kummer form at a node with separably closed residue field.** -/
theorem exists_nodeEquiv [IsSepClosed k] {ϖ : O} {n M' : ℕ} {x y : R}
    (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
    (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
    (h : IsKummerNormAt ϖ n M' x y B 𝔪) :
    ∃ (r : ℕ) (d : Fin r → ℕ) (hd : ∀ i, 0 < d i), (∀ i, d i ∣ M') ∧
      Nonempty (letI : ∀ i, Algebra (A (0 : k) (d i)) (Tn θ 𝔪) :=
          fun i ↦ (chartAlg (k := k)
            (xy_bar (θ := θ) hxy (by rw [map_pow, hϖ, zero_pow hn0.ne'])) (hd i) _)
        Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B ≃ₐ[Tn θ 𝔪]
          ∀ i, Tn θ 𝔪 ⊗[A (0 : k) (d i)] KummerEtale.B (0 : k)) := by
  obtain ⟨N₁, _, _, _, 𝔫, _, h𝔫, hdata⟩ := h
  letI : Algebra O N₁ := ((algebraMap R N₁).comp (algebraMap O R)).toAlgebra
  haveI : IsScalarTower O R N₁ := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨huv, -, -, -, r, m, d, hd, hdM, hmd, ⟨Φ⟩⟩ := hdata
  have hn : θ (ϖ ^ n) = 0 := by rw [map_pow, hϖ, zero_pow hn0.ne']
  have hc : ∀ i, θ (ϖ ^ m i) = 0 := fun i ↦ by
    have : 0 < m i := Nat.pos_of_ne_zero fun h0 ↦ hn0.ne' (by rw [← hmd i, h0, zero_mul])
    rw [map_pow, hϖ, zero_pow this.ne']
  -- the special fibres of the nodes
  have hJ𝔫 : J θ (R := N₁) ≤ 𝔫 := by
    rw [← J_N₁_eq θ R N₁, Ideal.map_le_iff_le_comap, h𝔫]
    exact hJ
  set 𝔫s : Ideal (Ns θ N₁) := 𝔫.map (Ideal.Quotient.mk _)
  have hcomap : 𝔫s.comap (algebraMap (Rs θ R) (Ns θ N₁)) = sIdeal (θ := θ) 𝔪 := by
    ext z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.mem_comap, algebraMap_RN, Ideal.mem_quotient_iff_mem hJ𝔫,
      Ideal.mem_quotient_iff_mem hJ, ← Ideal.mem_comap, h𝔫]
  -- trivial residue field extension
  have hρ : Function.Surjective ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R))) := by
    intro z
    obtain ⟨o, ho⟩ := hres z
    refine ⟨θ o, ?_⟩
    rw [RingHom.comp_apply, QuadNodeTower.algK_θ, Ideal.Quotient.factor_mk]
    exact ho
  have hsurj0 := EtaleResidue.surjective_of_isSepClosed' 𝔪 𝔫 h𝔫
    ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R))) hρ
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk 𝔫s).comp (algebraMap (Rs θ R) (Ns θ N₁))) := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hsurj0 (Ideal.Quotient.mk 𝔫 z)
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    simp only [RingHom.comp_apply] at ha ⊢
    rw [Ideal.Quotient.eq] at ha ⊢
    rw [algebraMap_RN, ← map_sub]
    exact Ideal.mem_map_of_mem _ ha
  haveI : Algebra.FormallyEtale R N₁ := inferInstance
  exact ⟨r, d, hd, hdM, ⟨nodeEquiv hxy hmd hc hd hn (sIdeal 𝔪) 𝔫s hcomap hsurj Φ⟩⟩

omit hθ in
lemma isMaximal_sIdeal (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪) :
    (sIdeal (θ := θ) 𝔪).IsMaximal := by
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    ‹_›).resolve_left fun h ↦ ?_
  have h1 : Ideal.Quotient.mk (J θ (R := R)) 1 ∈ sIdeal (θ := θ) 𝔪 := by
    rw [sIdeal, h]; exact Submodule.mem_top
  rw [Ideal.mem_quotient_iff_mem hJ] at h1
  exact Ideal.IsMaximal.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h1)

/-- **The formal Kummer form of the special fibre of a chart along its nodes** (separably closed
residue field). -/
theorem exists_kummer [IsSepClosed k] [IsNoetherianRing R] {ϖ : O} {n M' : ℕ} {x y : R}
    (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
    {ι : Type} [Finite ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
    (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
    (hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
    (hK : ∀ j, IsKummerNormAt ϖ n M' x y B (𝔪 j)) {f : Rs θ R}
    (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
    (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
    (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
    (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
    (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
    (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y)) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    ∃ (r : ι → ℕ) (d : ∀ j, Fin (r j) → ℕ) (hd : ∀ j i, 0 < d j i), (∀ j i, d j i ∣ M') ∧
      Nonempty (Admissible.Hat f ⊗[Rs θ R] Cs θ R B ≃ₐ[Admissible.Hat f]
        ∀ p : (Σ j, Fin (r j)), Admissible.KummerPiece φ
          (CompletionProd.idem hinj hf hrad p.1) (hd p.1 p.2)) := by
  haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  haveI := Fintype.ofFinite ι
  have hn : θ (ϖ ^ n) = 0 := by rw [map_pow, hϖ, zero_pow hn0.ne']
  choose r d hd hdM Ψ using fun j ↦
    exists_nodeEquiv (B := B) hxy hϖ hn0 (𝔪 j) (hJ j) (hres j) (hK j)
  exact ⟨r, d, hd, hdM, ⟨assembleEquiv hinj hf hrad (xy_bar (θ := θ) hxy hn) φ hφu hφv hd
    fun j ↦ (Ψ j).some⟩⟩

end

end FormalKummer

end SemistableReduction
