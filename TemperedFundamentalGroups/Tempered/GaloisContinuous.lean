/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.Galois

/-!
# The Krull topology on the decomposition group and continuity of `galoisToTempered`

The decomposition group `D_V = decompositionGroup R V ⊆ Aut_R(Ω)` carries the **Krull topology**
(`decompTop R V`): the topology of pointwise convergence on `Ω` (discrete), i.e. the group
topology with basis of neighbourhoods of `1` the pointwise stabilisers `decompStab R V S` of
finite subsets `S ⊆ Ω` (for `R` a field and `Ω/R` Galois this is Mathlib's Krull topology; here
`R` is a ring, so it is a `def`, not an instance, to avoid diamonds).

* `decompTop_isTopologicalGroup`;
* `galoisToTempered_app_mk_eq`, `galoisToTempered_app_eq`: a fibre element `[(t, p)]` of a
  tempered covering with level `B = R[x₁, …, xₙ]/I` is fixed by every `σ` fixing the finitely
  many elements `t(xᵢ) ∈ Ω` (`pointGens`), since then `σ ∘ t = t` (`comp_eq_of_mem_decompStab`);
* **`continuous_galoisToTempered`**: `galoisToTempered : D_V → Π^tp` is continuous.

Not here (MR13 plan, run 8, item 4): the topological isomorphism `Π^tp ⧸ Δ^tp ≃ₜ* G_k`, which also
needs the compactness of the decomposition group `D_A` of a place over a rational point in the
Krull topology of `Gal(Ω/F)` and the continuity of `D_A → D_V` and `D_A ↠ G_k`.
-/

universe u

open CategoryTheory Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (R : Type u) [CommRing R] [Algebra K R] (A : Type u) [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- The pointwise stabiliser in `D_V` of a finite subset of `Ω`. -/
def decompStab (S : Finset Ω) : Subgroup (decompositionGroup R V) where
  carrier := {σ | ∀ x ∈ S, (σ : Ω ≃ₐ[R] Ω) x = x}
  one_mem' _ _ := rfl
  mul_mem' {σ τ} hσ hτ x hx := by
    change (σ : Ω ≃ₐ[R] Ω) ((τ : Ω ≃ₐ[R] Ω) x) = x
    rw [hτ x hx, hσ x hx]
  inv_mem' {σ} hσ x hx := by
    change (σ : Ω ≃ₐ[R] Ω).symm x = x
    rw [AlgEquiv.symm_apply_eq, hσ x hx]

lemma decompStab_anti {S T : Finset Ω} (h : S ⊆ T) : decompStab R V T ≤ decompStab R V S :=
  fun _ hσ x hx => hσ x (h hx)

open Classical in
/-- The group filter basis of pointwise stabilisers of finite subsets of `Ω`. -/
@[reducible] def decompFilterBasis : GroupFilterBasis (decompositionGroup R V) where
  sets := Set.range fun S => (decompStab R V S : Set (decompositionGroup R V))
  nonempty := ⟨_, ⟨∅, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨S, rfl⟩ ⟨T, rfl⟩
    exact ⟨_, ⟨S ∪ T, rfl⟩, fun σ hσ =>
      ⟨decompStab_anti R V Finset.subset_union_left hσ,
        decompStab_anti R V Finset.subset_union_right hσ⟩⟩
  one' := by
    rintro _ ⟨S, rfl⟩
    exact (decompStab R V S).one_mem
  mul' := by
    rintro _ ⟨S, rfl⟩
    refine ⟨_, ⟨S, rfl⟩, ?_⟩
    rintro _ ⟨σ, hσ, τ, hτ, rfl⟩
    exact (decompStab R V S).mul_mem hσ hτ
  inv' := by
    rintro _ ⟨S, rfl⟩
    exact ⟨_, ⟨S, rfl⟩, fun σ hσ => (decompStab R V S).inv_mem hσ⟩
  conj' := by
    rintro τ _ ⟨S, rfl⟩
    refine ⟨_, ⟨S.image fun x => (τ : Ω ≃ₐ[R] Ω).symm x, rfl⟩, fun σ hσ x hx => ?_⟩
    have h := hσ _ (Finset.mem_image_of_mem _ hx)
    change (τ : Ω ≃ₐ[R] Ω) ((σ : Ω ≃ₐ[R] Ω) ((τ : Ω ≃ₐ[R] Ω).symm x)) = x
    rw [h, AlgEquiv.apply_symm_apply]

/-- **The Krull topology on the decomposition group** (pointwise convergence on `Ω`). -/
@[reducible] def decompTop : TopologicalSpace (decompositionGroup R V) :=
  (decompFilterBasis R V).topology

theorem decompTop_isTopologicalGroup :
    @IsTopologicalGroup (decompositionGroup R V) (decompTop R V) _ :=
  (decompFilterBasis R V).isTopologicalGroup

open Classical in
/-- The elements of `Ω` that a geometric point `t : R[x₁, …, xₙ]/I → Ω` takes on the
generators. -/
def pointGens {n : ℕ} {I : Ideal (MvPolynomial (Fin n) R)} (t : LevelRing R n I →ₐ[R] Ω) :
    Finset Ω :=
  Finset.univ.image fun i => t (Ideal.Quotient.mkₐ R I (MvPolynomial.X i))

theorem comp_eq_of_mem_decompStab {n : ℕ} {I : Ideal (MvPolynomial (Fin n) R)}
    (t : LevelRing R n I →ₐ[R] Ω) {S : Finset Ω} (hS : pointGens R t ⊆ S)
    {σ : decompositionGroup R V} (hσ : σ ∈ decompStab R V S) :
    ((σ : Ω ≃ₐ[R] Ω) : Ω →ₐ[R] Ω).comp t = t := by
  classical
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => ?_)
  exact hσ _ (hS (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

/-- A fibre element `[(t, p)]` is fixed by every `σ` fixing the values of `t` on the
generators. -/
theorem galoisToTempered_app_mk_eq (X : TempObj O R A) (q : TempObj.PreFibre Ω V hV X)
    {S : Finset Ω} (hS : pointGens R q.1.1 ⊆ S) {σ : decompositionGroup R V}
    (hσ : σ ∈ decompStab R V S) :
    (galoisToTempered O R A hV σ).app X (Quotient.mk _ q) = Quotient.mk _ q := by
  rw [galoisToTempered_app_mk]
  congr 1
  exact Subtype.ext (Prod.ext (comp_eq_of_mem_decompStab R V q.1.1 hS hσ) rfl)

theorem galoisToTempered_app_eq (X : TempObj O R A) (x : (tempFibre O R A V hV).obj X)
    {S : Finset Ω} (hS : pointGens R (Quotient.out (x : TempObj.Fibre Ω V hV X)).1.1 ⊆ S)
    {σ : decompositionGroup R V} (hσ : σ ∈ decompStab R V S) :
    (galoisToTempered O R A hV σ).app X x = x := by
  have h := galoisToTempered_app_mk_eq O R A V hV X (Quotient.out (x : TempObj.Fibre Ω V hV X))
    hS hσ
  rwa [Quotient.out_eq] at h

open Classical in
/-- **`galoisToTempered : D_V → Π^tp` is continuous** for the Krull topology on `D_V`. -/
theorem continuous_galoisToTempered :
    @Continuous (decompositionGroup R V) (temperedPi1 O R A V hV) (decompTop R V) _
      (galoisToTempered O R A hV) := by
  letI := decompTop R V
  haveI := decompTop_isTopologicalGroup R V
  refine continuous_of_continuousAt_one (galoisToTempered O R A hV) ?_
  have h1 : galoisToTempered O R A hV 1 = 1 := map_one _
  change Filter.Tendsto _ _ _
  rw [h1]
  have hb := (decompFilterBasis R V).nhds_one_hasBasis
  have hb' := FibreAut.nhds_one_hasBasis (tempFibre O R A V hV)
  refine (hb.tendsto_iff hb').2 fun S _ => ?_
  refine ⟨(decompStab R V (S.biUnion fun p => pointGens R
    (Quotient.out (p.2 : TempObj.Fibre Ω V hV p.1)).1.1) : Set (decompositionGroup R V)),
    ⟨_, rfl⟩, fun σ hσ => ?_⟩
  refine FibreAut.mem_stabilizer.2 fun p hp => ?_
  exact galoisToTempered_app_eq O R A V hV p.1 p.2
    (Finset.subset_biUnion_of_mem (fun p : (Σ X, (tempFibre O R A V hV).obj X) =>
      pointGens R (Quotient.out (p.2 : TempObj.Fibre Ω V hV p.1)).1.1) hp) hσ

end

end TemperedFundamentalGroups
