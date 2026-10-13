/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateInvolution
import TemperedFundamentalGroups.SemiAnbd.FixedArc

/-!
# The wild Tate part at finite levels: fixed arcs in special fibres (Blueprint §12.10, E17)

**Exact reduction to arcs.** By `TreeTower.smallFixAt_iff_not_fixedArcAt`, an element of André's
group is estranged iff below every level there is a level at which it fixes no arc
`x₀ – x₁ – x₂ – x₃` of the tree; so `TateWildPart Δ` is equivalent to the arc form
(**`tateWildPart_iff_fixedArcAt`**).

**Finite-level criterion.** The stage group of a level acts on the tree of the dual graph over the
homeomorphism `zAct` of the special fibre of the level's W-model (a finite curve over the residue
field). A fixed arc of the tree gives a fixed reduced walk of length `3` in the finite incidence
graph of components and special points (`CurveConfig.fixedArc_of_tree`):

* `UData.zAct`, **`UData.fixedArc_of_stageTree`**;
* `andreZAct q g`, `AndreFixedArc q g` (the homeomorphism of the special fibre at level `q`
  induced by `g` fixes the components and special points of such a walk),
  **`fixedArc_of_fixedArcAt_andreTower`**, **`smallFixAt_andreTower_of_not_andreFixedArc`**,
  **`estrangedElt_andreTower_of_fin`**;
* **`TateWildFin Δ`**: for every nontrivial elliptic `g ∈ Δ ∩ Π^tp_Ÿ`, below every level there is
  a level `k` such that `g` fixes no arc of the finite incidence graph of the special fibre at `k`;
  **`tateWildPart_of_fin`**: `TateWildFin Δ ⇒ TateWildPart Δ`, hence (E16) the estrangement of
  André's tower over `Δ` (`estranged_comap_andreTower_of_tateWildFin`). `TateWildFin` is a
  sufficient condition only: a fixed arc downstairs need not lift to a fixed arc of the tree.

**Obstruction (model dependence).** `FixedArcBelow q g` (`g` fixes an arc of the tree at every
level below `q`) refutes `TateWildPart` for any `Δ ∋ g` (`not_tateWildPart_of_fixedArcBelow`).
The W-models chosen by `curveData` are arbitrary (refined Gauss trees are allowed), and at a level
whose model subdivides an annulus into a chain, the inertia of the annulus fixes the lifted chain
at all *tame* levels below; so for such elements `FixedArcBelow` can only fail through wild
coverings (Blueprint §12.10, "Model dependence"). This is a sketch, not proved here.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit CurveConfig TateObject

/-! ### The action of the stage group on the special fibre -/

section Stage

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace UData

variable {X : TempObj O R A} (D : UData Ω X)

/-- **The homeomorphism of the special fibre** of the level of `X` induced by an element of the
stage group (through a chosen automorphism representing it). -/
def zAct (σ : stageGroup (tempFibre O R A V hV) X) : D.Lv.Z ≃ₜ D.Lv.Z :=
  zHomeoU (D.e.conjAut (eq_stageOf σ).choose)

/-- **A fixed arc of the tree gives a fixed arc of the finite incidence graph.** -/
theorem fixedArc_of_stageTree (σ : stageGroup (tempFibre O R A V hV) X) {t₀ t₁ t₂ t₃ : D.Tr}
    (h₀₁ : t₀.Adj t₁) (h₁₂ : t₁.Adj t₂) (h₂₃ : t₂.Adj t₃) (h₀₂ : t₀ ≠ t₂) (h₁₃ : t₁ ≠ t₃)
    (f₀ : D.stageTree V hV σ t₀ = t₀) (f₁ : D.stageTree V hV σ t₁ = t₁)
    (f₂ : D.stageTree V hV σ t₂ = t₂) (f₃ : D.stageTree V hV σ t₃ = t₃) :
    (curveConfig D.Lv.Z D.hdim).FixedArc (D.zAct V hV σ) := by
  set b := D.e.conjAut (eq_stageOf σ).choose
  exact fixedArc_of_tree (hηU D.hdim) (f := uTreeMap b.hom) (ψ := zHomeoU b) (uTreeMap_fst b)
    (fun i ↦ ⟨_, curveConfig_η_homeo D.hdim (zHomeoU b) i⟩)
    (curveConfig_mem_S_homeo D.hdim (zHomeoU b)) h₀₁ h₁₂ h₂₃ h₀₂ h₁₃ f₀ f₁ f₂ f₃

end UData

end Stage

/-! ### André's tower -/

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
  [Finite A] [SMulCommClass A K R]

/-- **The homeomorphism of the special fibre of the W-model at level `q`** induced by an element
of André's group. -/
def andreZAct (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (g : andreGroup O R A V hV) :
    (curveData V hV hR q).Lv.Z ≃ₜ (curveData V hV hR q).Lv.Z :=
  (curveData V hV hR q).zAct V hV ((andreTower (R := R) (A := A) V hV hp hR).ρ q g)

/-- **`g` fixes an arc of the special fibre at level `q`**: the homeomorphism `andreZAct q g` of
the special fibre of the W-model of `q` fixes the components and special points of a reduced walk
`v₀ – v₁ – v₂ – v₃` of its incidence graph. -/
def AndreFixedArc (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (g : andreGroup O R A V hV) : Prop :=
  (curveConfig (curveData V hV hR q).Lv.Z (curveData V hV hR q).hdim).FixedArc
    (andreZAct V hV hp hR q g)

/-- **A fixed arc of the tree at `q` gives a fixed arc of the special fibre at `q`.** -/
theorem fixedArc_of_fixedArcAt_andreTower {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    {g : andreGroup O R A V hV} (h : (andreTower (R := R) (A := A) V hV hp hR).FixedArcAt q g) :
    AndreFixedArc V hV hp hR q g := by
  obtain ⟨x₀, x₁, x₂, x₃, h₀₁, h₁₂, h₂₃, h₀₂, h₁₃, f₀, f₁, f₂, f₃⟩ := h
  exact (curveData V hV hR q).fixedArc_of_stageTree V hV _ h₀₁ h₁₂ h₂₃ h₀₂ h₁₃ f₀ f₁ f₂ f₃

/-- **Finite-level criterion at one level**: if `g` fixes no arc of the special fibre at `q`, its
fixed set in the tree at `q` has diameter `≤ 2`. -/
theorem smallFixAt_andreTower_of_not_andreFixedArc
    {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} {g : andreGroup O R A V hV}
    (h : ¬ AndreFixedArc V hV hp hR q g) :
    (andreTower (R := R) (A := A) V hV hp hR).SmallFixAt q g :=
  (TreeTower.smallFixAt_iff_not_fixedArcAt q g).2
    fun h' ↦ h (fixedArc_of_fixedArcAt_andreTower V hV hp hR h')

/-- **Finite-level criterion for estrangement**: `g` is estranged if below every level there is a
level at which it fixes no arc of the special fibre. -/
theorem estrangedElt_andreTower_of_fin {g : andreGroup O R A V hV}
    (h : ∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
      ¬ AndreFixedArc V hV hp hR k g) :
    (andreTower (R := R) (A := A) V hV hp hR).EstrangedElt g := fun j ↦ by
  obtain ⟨k, f, hk⟩ := h j
  exact ⟨k, f, smallFixAt_andreTower_of_not_andreFixedArc V hV hp hR hk⟩

section Double

variable (D : DoubleData O R) (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)

/-- **`TateWildPart` in arc form (exact)**: every nontrivial elliptic `g ∈ Δ ∩ Π^tp_Ÿ` fixes no
arc of the tree at cofinally many levels. -/
theorem tateWildPart_iff_fixedArcAt (Δ : Subgroup (andreGroup O R A V hV)) :
    TateWildPart (A := A) V hV hp hR D s hs Δ ↔
      ∀ g ∈ Δ, (andreTower (R := R) (A := A) V hV hp hR).Elliptic g →
        charYY (A := A) V hV hp hR D s hs g = 1 → g ≠ 1 → ∀ j, ∃ (k : PtGal
          (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
            ¬ (andreTower (R := R) (A := A) V hV hp hR).FixedArcAt k g := by
  constructor
  · intro h g hg he hc hg1
    exact (TreeTower.estrangedElt_iff_not_fixedArcAt g).1 (h g ⟨hg, he, hc⟩ hg1)
  · rintro h g ⟨hg, he, hc⟩ hg1
    exact (TreeTower.estrangedElt_iff_not_fixedArcAt g).2 (h g hg he hc hg1)

/-- **The wild Tate part at finite levels**: for every nontrivial elliptic `g ∈ Δ ∩ Π^tp_Ÿ`,
below every level there is a level `k` at which the homeomorphism of the special fibre of the
W-model of `k` induced by `g` fixes no reduced walk of length `3` of its incidence graph
(components and special points). Open; a statement about finite coverings and the special fibres
of their W-models. -/
def TateWildFin (Δ : Subgroup (andreGroup O R A V hV)) : Prop :=
  ∀ g ∈ Δ, (andreTower (R := R) (A := A) V hV hp hR).Elliptic g →
    charYY (A := A) V hV hp hR D s hs g = 1 → g ≠ 1 →
      ∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        ¬ AndreFixedArc V hV hp hR k g

/-- **`TateWildFin Δ ⇒ TateWildPart Δ`.** -/
theorem tateWildPart_of_fin (Δ : Subgroup (andreGroup O R A V hV))
    (h : TateWildFin V hV hp hR D s hs Δ) : TateWildPart (A := A) V hV hp hR D s hs Δ := by
  rintro g ⟨hg, he, hc⟩ hg1
  exact estrangedElt_andreTower_of_fin V hV hp hR (h g hg he hc hg1)

/-- **Estrangement of André's tower over `Δ` from the finite-level wild Tate part.** -/
theorem estranged_comap_andreTower_of_tateWildFin (Δ : Subgroup (andreGroup O R A V hV))
    (h : TateWildFin V hV hp hR D s hs Δ) :
    ((andreTower (R := R) (A := A) V hV hp hR).comap Δ.subtype).Estranged :=
  (estranged_comap_andreTower_iff_tateWild V hV hp hR D s hs Δ).2
    (tateWildPart_of_fin V hV hp hR D s hs Δ h)

/-- `g` **fixes an arc of the tree at every level below `q`**. -/
def FixedArcBelow (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (g : andreGroup O R A V hV) : Prop :=
  ∀ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ q),
    (andreTower (R := R) (A := A) V hV hp hR).FixedArcAt k g

/-- **The obstruction**: a nontrivial elliptic `g ∈ Δ ∩ Π^tp_Ÿ` fixing an arc at all levels below
some level refutes `TateWildPart Δ`. -/
theorem not_tateWildPart_of_fixedArcBelow {Δ : Subgroup (andreGroup O R A V hV)}
    {g : andreGroup O R A V hV} (hg : g ∈ Δ)
    (he : (andreTower (R := R) (A := A) V hV hp hR).Elliptic g)
    (hc : charYY (A := A) V hV hp hR D s hs g = 1) (hg1 : g ≠ 1)
    {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (hq : FixedArcBelow V hV hp hR q g) :
    ¬ TateWildPart (A := A) V hV hp hR D s hs Δ := fun h ↦
  TreeTower.not_estrangedElt_of_forall_fixedArcAt hq (h g ⟨hg, he, hc⟩ hg1)

end Double

end

end TemperedFundamentalGroups
