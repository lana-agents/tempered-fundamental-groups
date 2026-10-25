/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import TemperedFundamentalGroups.SemiAnbd.TempSlim

/-!
# Trivial centralizers of finite-index subgroups via a dense embedding into a slim group

The finite-index route to temp-slimness (MR13 plan, decision D4; [EtTh] Prop 2.11 with finite
`μ_N` only uses that *finite-index* open subgroups have trivial centralizers): if `f : P →* Q`
is injective with dense image in a Hausdorff topological group `Q` all of whose open subgroups
have trivial centralizers (e.g. a slim profinite group, `tempSlim_iff_isSlim`), then every
finite-index subgroup of `P` has trivial centralizer. Typical use: `P = π^temp` and
`Q = π̂₁` (`LoopTower.toHat`, [SemiAnbd] Prop 3.6(iii)).

* `finiteIndex_topologicalClosure_map`: the closure of the image of a finite-index subgroup under
  a homomorphism with dense image has finite index (hence is open when closed);
* **`TempSlim.centralizer_eq_bot_of_denseRange`**.
-/

open scoped Pointwise

namespace TemperedFundamentalGroups

variable {P Q : Type*} [Group P] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- The closure of the image of a finite-index subgroup under a homomorphism with dense image has
finite index. -/
theorem finiteIndex_topologicalClosure_map (f : P →* Q) (hd : DenseRange f) (H : Subgroup P)
    [H.FiniteIndex] : ((H.map f).topologicalClosure).FiniteIndex := by
  set K := (H.map f).topologicalClosure
  have hcov : ∀ q : Q, ∃ c : P ⧸ H, q ∈ f (Quotient.out c) • (K : Set Q) := by
    intro q
    have hsub : Set.range f ⊆
        ⋃ c : P ⧸ H, f (Quotient.out c) • ((H.map f : Subgroup Q) : Set Q) := by
      rintro _ ⟨p, rfl⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H p
      refine Set.mem_iUnion.2 ⟨(p : P ⧸ H), Set.mem_smul_set.2 ⟨f (h⁻¹ : H), ?_, ?_⟩⟩
      · exact Subgroup.mem_map_of_mem f (h⁻¹ : H).2
      · rw [smul_eq_mul, hh, map_mul, mul_assoc, ← map_mul]
        simp
    have hq : q ∈ closure (⋃ c : P ⧸ H, f (Quotient.out c) • ((H.map f : Subgroup Q) : Set Q)) :=
      closure_mono hsub (hd.closure_eq ▸ Set.mem_univ q)
    rw [closure_iUnion_of_finite] at hq
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hq
    refine ⟨c, ?_⟩
    rwa [closure_smul, ← Subgroup.topologicalClosure_coe] at hc
  have hsurj : Function.Surjective fun c : P ⧸ H ↦ ((f (Quotient.out c) : Q) : Q ⧸ K) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H q =>
      obtain ⟨c, hc⟩ := hcov q
      obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hc
      refine ⟨c, QuotientGroup.eq.2 ?_⟩
      simpa [smul_eq_mul] using hk
  haveI : Finite (Q ⧸ K) := Finite.of_surjective _ hsurj
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **Finite-index subgroups have trivial centralizers** in a group `P` that embeds with dense
image into a Hausdorff topological group `Q` whose open subgroups have trivial centralizers. -/
theorem TempSlim.centralizer_eq_bot_of_denseRange [T2Space Q] (hQ : TempSlim Q) (f : P →* Q)
    (hinj : Function.Injective f) (hd : DenseRange f) (H : Subgroup P) [H.FiniteIndex] :
    Subgroup.centralizer (H : Set P) = ⊥ := by
  set K := (H.map f).topologicalClosure
  haveI := finiteIndex_topologicalClosure_map f hd H
  have hKo : IsOpen (K : Set Q) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex K (Subgroup.isClosed_topologicalClosure _)
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx ↦ ?_
  rw [Subgroup.mem_centralizer_iff] at hx
  have hS : IsClosed {y : Q | y * f x = f x * y} :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hsub : ((H.map f : Subgroup Q) : Set Q) ⊆ {y : Q | y * f x = f x * y} := by
    rintro _ ⟨h, hh, rfl⟩
    simp only [Set.mem_setOf_eq, ← map_mul, hx h hh]
  have hK : (K : Set Q) ⊆ {y : Q | y * f x = f x * y} := by
    rw [Subgroup.topologicalClosure_coe]
    exact closure_minimal hsub hS
  have h1 : f x = 1 := hQ.eq_one hKo fun y hy ↦ hK hy
  exact hinj (h1.trans (map_one f).symm)

end TemperedFundamentalGroups
