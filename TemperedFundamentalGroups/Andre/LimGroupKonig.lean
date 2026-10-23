/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Filtered.Final
import TemperedFundamentalGroups.Andre.CurveTower

/-!
# König's lemma for the inverse limit of the stage groups

Let `Φ : C ⥤ Type w` and `𝒢` satisfy (gal) and (rig), with a cofiltered category `PtGal Φ 𝒢` of
pointed Galois objects. Pointed morphisms are unique when they exist (`subsingleton_hom`, by
rigidity).

* **`exists_limGroup_mem`**: given `q₀` and finite nonempty sets `T p ⊆ stageGroup Φ p.G` for all
  `p` over `q₀`, stable under the transition maps, some element of the limit group has its
  `p`-component in `T p` for every `p` over `q₀` (König: Mathlib's
  `nonempty_sections_of_finite_cofiltered_system` on the cofiltered category `Over q₀`, and the
  section is extended to all of `PtGal Φ 𝒢` through cofilteredness).
* **`exists_stageLimit_mem`**, **`exists_andreGroup_mem`**: the same for the curve tower
  `curveTower` on `stageLimit` and, through `andreGroupHomeoLim`, for André's group.
-/

universe w v u

open CategoryTheory Pi1.Orbifold

namespace TemperedFundamentalGroups

namespace GaloisLimit

variable {C : Type u} [Category.{v} C] {Φ : C ⥤ Type w} {𝒢 : ObjectProperty C}
  (hgal : IsGaloisClass Φ 𝒢) (hrig : IsRigid Φ 𝒢)

include hrig in
/-- **Pointed morphisms between pointed Galois objects are unique** (rigidity). -/
lemma subsingleton_hom (p q : PtGal Φ 𝒢) : Subsingleton (p ⟶ q) := by
  refine ⟨fun f f' ↦ ?_⟩
  obtain ⟨⟨a, ha⟩, h⟩ := f.2
  obtain ⟨⟨b, hb⟩, h'⟩ := f'.2
  apply Subtype.ext
  rw [← ha, ← hb]
  have e := hrig _ p.mem a b p.g (by rw [ha, hb, h, h'])
  rw [e]

/-- The finite sets `T p` over `q₀` as a functor on `Over q₀`. -/
noncomputable def overFunctor {q₀ : PtGal Φ 𝒢} (T : ∀ p : PtGal Φ 𝒢, Set (stageGroup Φ p.G))
    (hT : ∀ {p p' : PtGal Φ 𝒢} (f : p ⟶ p'), (p' ⟶ q₀) → ∀ σ ∈ T p,
      transition hgal hrig f σ ∈ T p') : Over q₀ ⥤ Type w where
  obj P := T P.left
  map {P P'} g := TypeCat.ofHom fun x ↦ ⟨transition hgal hrig g.left x.1,
    hT g.left P'.hom x.1 x.2⟩
  map_id P := by
    refine TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun x ↦ Subtype.ext ?_))
    exact transition_id hgal hrig P.left x.1
  map_comp {P P' P''} g g' := by
    refine TypeCat.Hom.ext (TypeCat.Fun.ext (funext fun x ↦ Subtype.ext ?_))
    exact transition_comp hgal hrig g.left g'.left x.1

/-- **König's lemma for the limit of the stage groups**: finite nonempty sets `T p` of stage group
elements for the pointed Galois objects `p` over `q₀`, stable under the transition maps, contain
the components of a common element of the limit group. -/
theorem exists_limGroup_mem [IsCofilteredOrEmpty (PtGal Φ 𝒢)] (q₀ : PtGal Φ 𝒢)
    (T : ∀ p : PtGal Φ 𝒢, Set (stageGroup Φ p.G)) (hfin : ∀ p, (p ⟶ q₀) → (T p).Finite)
    (hne : ∀ p, (p ⟶ q₀) → (T p).Nonempty)
    (hT : ∀ {p p' : PtGal Φ 𝒢} (f : p ⟶ p'), (p' ⟶ q₀) → ∀ σ ∈ T p,
      transition hgal hrig f σ ∈ T p') :
    ∃ γ : limGroup Φ 𝒢 hgal hrig, ∀ p, (p ⟶ q₀) → γ.1 p ∈ T p := by
  have hsub := subsingleton_hom hrig
  let F := overFunctor hgal hrig T hT
  haveI : ∀ P : Over q₀, Finite (F.obj P) := fun P ↦ (hfin P.left P.hom).to_subtype
  haveI : ∀ P : Over q₀, Nonempty (F.obj P) := fun P ↦ (hne P.left P.hom).to_subtype
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system F
  -- a level over both `p` and `q₀`
  have hcone : ∀ p : PtGal Φ 𝒢, ∃ P : Over q₀, Nonempty (P.left ⟶ p) := fun p ↦ by
    obtain ⟨r, f, g, -⟩ := IsCofilteredOrEmpty.cone_objs p q₀
    exact ⟨Over.mk g, ⟨f⟩⟩
  let P : PtGal Φ 𝒢 → Over q₀ := fun p ↦ (hcone p).choose
  let h : ∀ p, (P p).left ⟶ p := fun p ↦ (hcone p).choose_spec.some
  let γ : ∀ p : PtGal Φ 𝒢, stageGroup Φ p.G := fun p ↦ transition hgal hrig (h p) (s (P p)).1
  -- independence of the choices
  have hwd : ∀ {p : PtGal Φ 𝒢} (Q : Over q₀) (k : Q.left ⟶ p),
      transition hgal hrig k (s Q).1 = γ p := by
    intro p Q k
    obtain ⟨r, u, u', -⟩ := IsCofilteredOrEmpty.cone_objs Q.left (P p).left
    let Rr : Over q₀ := Over.mk (u ≫ Q.hom)
    have h₁ : (s Q).1 = transition hgal hrig u (s Rr).1 :=
      (congrArg Subtype.val (hs (Over.homMk u rfl : Rr ⟶ Q))).symm
    have h₂ : (s (P p)).1 = transition hgal hrig u' (s Rr).1 :=
      (congrArg Subtype.val (hs (Over.homMk u' (Subsingleton.elim _ _) : Rr ⟶ P p))).symm
    change _ = transition hgal hrig (h p) (s (P p)).1
    rw [h₁, h₂, ← transition_comp, ← transition_comp, Subsingleton.elim (u ≫ k) (u' ≫ h p)]
  refine ⟨⟨γ, fun {p q} f ↦ ?_⟩, fun p hp ↦ ?_⟩
  · rw [← hwd (P p) (h p), ← transition_comp]
    exact hwd (P p) (h p ≫ f)
  · change γ p ∈ T p
    have e := transition_id hgal hrig p (s (Over.mk hp)).1
    rw [← hwd (Over.mk hp) (𝟙 p)]
    exact (congrArg (fun x ↦ x ∈ T p) e).mpr (s (Over.mk hp)).2

end GaloisLimit

noncomputable section

open GaloisLimit

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

/-- **König's lemma for the curve tower**: finite nonempty sets `T p` of stage group elements for
the pointed Galois objects `p` over `q₀`, stable under the transition maps, contain the
components of a common element of `stageLimit`. -/
theorem exists_stageLimit_mem (q₀ : PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (T : ∀ p : PtGal (tempFibre O R A V hV) (galW O R A Ω hR),
      Set (stageGroup (tempFibre O R A V hV) p.G))
    (hfin : ∀ p, (p ⟶ q₀) → (T p).Finite) (hne : ∀ p, (p ⟶ q₀) → (T p).Nonempty)
    (hT : ∀ {p p' : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (f : p ⟶ p'), (p' ⟶ q₀) →
      ∀ σ ∈ T p, transition (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
        (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 f σ ∈ T p') :
    ∃ γ : stageLimit (R := R) (A := A) V hV hp hR, ∀ p, (p ⟶ q₀) → γ.1 p ∈ T p := by
  haveI := isCofiltered (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.1
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2
  exact exists_limGroup_mem _ _ q₀ T hfin hne hT

/-- **König's lemma for André's group**: finite nonempty sets `T p` of stage group elements for
the pointed Galois objects `p` over `q₀`, stable under the transition maps, contain the
components (through `andreGroupHomeoLim`) of an element of André's group. -/
theorem exists_andreGroup_mem [Finite A] [SMulCommClass A K R]
    (q₀ : PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (T : ∀ p : PtGal (tempFibre O R A V hV) (galW O R A Ω hR),
      Set (stageGroup (tempFibre O R A V hV) p.G))
    (hfin : ∀ p, (p ⟶ q₀) → (T p).Finite) (hne : ∀ p, (p ⟶ q₀) → (T p).Nonempty)
    (hT : ∀ {p p' : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (f : p ⟶ p'), (p' ⟶ q₀) →
      ∀ σ ∈ T p, transition (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
        (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 f σ ∈ T p') :
    ∃ g : andreGroup O R A V hV,
      ∀ p, (p ⟶ q₀) → (andreGroupHomeoLim (R := R) (A := A) V hV hp hR g).1 p ∈ T p := by
  obtain ⟨γ, hγ⟩ := exists_stageLimit_mem V hV hp hR q₀ T hfin hne hT
  refine ⟨(andreGroupHomeoLim (R := R) (A := A) V hV hp hR).symm γ, fun p hp' ↦ ?_⟩
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact hγ p hp'

end

end TemperedFundamentalGroups
