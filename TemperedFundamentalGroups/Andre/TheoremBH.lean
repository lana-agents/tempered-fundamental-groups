/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.HeightW
import TemperedFundamentalGroups.Andre.TheoremBW
import TemperedFundamentalGroups.Topology.HeightBound

/-!
# Theorem B from the height-corrected length (Blueprint §10.3.8, I7)

Scheme case. Fix a member `Y₀` of `galClassW` with a fibre element `y₀` over the base point `x₀`
of the Tate object `X₀` (through `a₀ : Y₀ ⟶ X₀`). The pointed members of `galClassW` over `Y₀`
(`GaloisLimit.overY`) still satisfy (gal), (dom), (rig). For a pointed member `p = (G, g)` with
its chosen presentation, let

`S_p = {γ | ∃ a : G ⟶ X₀, a(g) = x₀, a(γ) = δ(d) x₀ and HCW(g, γ) ≤ ℓ₀}`

(`HCW`: the height-corrected length condition `Q − 2h ≤ ℓ₀`, `Pres.HCW`). These sets are mapped
into each other by pointed morphisms (`Pres.hcw_map`, from `HarmonicX` and
`NodeOfTwoComponents`). If they are finite (`hfin`) and nonempty (`hne`, the loop over
`δ(d) x₀`), K1/K2 (`GaloisLimit.exists_deckCharacter_eq_of_sets`) give an element of
`temperedPi1` with character `d` (`TateObject.exists_character_eq_of_hcw`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold
open scoped ENNReal

namespace TemperedFundamentalGroups

namespace GaloisLimit

variable {C : Type*} [Category C] {Φ : C ⥤ Type*} {𝒢 : ObjectProperty C}

variable (𝒢) in
/-- The members of `𝒢` admitting a morphism to `Y₀`. -/
def overY (Y₀ : C) : ObjectProperty C := fun X => 𝒢 X ∧ Nonempty (X ⟶ Y₀)

lemma isGaloisClass_over (h : IsGaloisClass Φ 𝒢) (Y₀ : C) : IsGaloisClass Φ (overY 𝒢 Y₀) :=
  fun G hG => h G hG.1

lemma isRigid_over (h : IsRigid Φ 𝒢) (Y₀ : C) : IsRigid Φ (overY 𝒢 Y₀) :=
  fun G hG => h G hG.1

lemma isDominating_over (h : IsDominating Φ 𝒢) (Y₀ : C) (y₀ : Φ.obj Y₀) :
    IsDominating Φ (overY 𝒢 Y₀) := by
  intro n P
  obtain ⟨G, hG, g, f, hf⟩ := h (n + 1) (Fin.cons ⟨Y₀, y₀⟩ P)
  exact ⟨G, ⟨hG, ⟨f 0⟩⟩, g, fun k => f k.succ, fun k => hf k.succ⟩

end GaloisLimit

noncomputable section

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) {x : R}
  (T : TateObject.Data O R)

namespace Pres

variable {X : TempObj O R A} (P : Pres x X)

lemma tateNu_eq (a a' : X ⟶ TateObject.X₀ (A := A) T) :
    P.tateNu T a = P.tateNu T a' := by
  unfold tateNu
  rw [P.tateMap_eq T a a']

/-- `HCW` does not depend on the morphism to the Tate object. -/
lemma hcw_congr (a a' : X ⟶ TateObject.X₀ (A := A) T) (ϖ : O)
    (g γ : (tempFibre O R A V hV).obj X) (ℓ : ℝ≥0∞) :
    P.HCW V hV T a ϖ g γ ℓ ↔ P.HCW V hV T a' ϖ g γ ℓ := by
  unfold HCW
  rw [P.tateNu_eq T a a']

omit [IsReduced R] [Subsingleton A] [Algebra K Ω] [IsScalarTower K R Ω] in
/-- A presentation of a member of `galClassW`, with the Galois property of its level. -/
lemma exists_gal {X : TempObj O R A} (hX : galClassW O R A Ω (Level.IsW x) X) :
    ∃ P : Pres x X, ∀ t t' : P.Lv.L.B →ₐ[R] Ω, ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B,
      t.comp (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) = t' := by
  obtain ⟨Lv, _, _, _, _, _, hdim, z₀, hP, -, hgal, hidem, hact, hss, hdom, ⟨iso⟩⟩ := hX
  obtain ⟨D⟩ := WData.nonempty_of_isW hP
  exact ⟨⟨Lv, hdim, z₀, D, iso, hidem, hact, hss⟩, fun t t' => (hgal t t').exists⟩

end Pres

namespace TateObject

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- **Theorem B from the height-corrected length**: given (gal), (dom), (rig) for `galClassW`, a
pointed member `(Y₀, y₀)` over `(X₀, x₀)`, finiteness of the sets `HCW ≤ ℓ₀` and the loop
(`hne`: every pointed member over `(Y₀, y₀)` has an element over `δ(d) x₀` with `HCW ≤ ℓ₀`),
some element of `temperedPi1` has character `d`. -/
theorem exists_character_eq_of_hcw
    (hgal : IsGaloisClass (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (hdom : IsDominating (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (hrig : IsRigid (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (Y₀ : TempObj O R A) (hY₀ : galClassW O R A Ω (Level.IsW x) Y₀)
    (y₀ : (tempFibre O R A V hV).obj Y₀) (a₀ : Y₀ ⟶ X₀ (A := A) T)
    (ha₀ : (tempFibre O R A V hV).map a₀ y₀ = basePoint T V hV) (d : Multiplicative ℤ)
    (ℓ₀ : ℝ≥0∞)
    (hfin : ∀ (X : TempObj O R A) (P : Pres x X) (a : X ⟶ X₀ (A := A) T)
      (g : (tempFibre O R A V hV).obj X), {γ | P.HCW V hV T a ϖ g γ ℓ₀}.Finite)
    (hne : ∀ (X : TempObj O R A) (P : Pres x X), (∀ t t' : P.Lv.L.B →ₐ[R] Ω,
      ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B, t.comp (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) = t') →
      ∀ (m : X ⟶ Y₀) (g : (tempFibre O R A V hV).obj X),
      (tempFibre O R A V hV).map m g = y₀ → ∃ γ, (tempFibre O R A V hV).map (m ≫ a₀) γ =
        FibreAut.deckAct (X₀ T) (deck T) d (basePoint T V hV) ∧
        P.HCW V hV T (m ≫ a₀) ϖ g γ ℓ₀) :
    ∃ τ : temperedPi1 O R A V hV, character T V hV τ = d := by
  classical
  let Φ := tempFibre O R A V hV
  let 𝒢₀ := overY (galClassW O R A Ω (Level.IsW x)) Y₀
  let pres : ∀ p : PtGal Φ 𝒢₀, Pres x p.G := fun p => (Pres.exists_gal p.mem.1).choose
  have hpt : ∀ p : PtGal Φ 𝒢₀, ∃ m : p.G ⟶ Y₀, Φ.map m p.g = y₀ := fun p => by
    obtain ⟨m₁⟩ := p.mem.2
    obtain ⟨σ, hσ⟩ := hgal Y₀ hY₀ (Φ.map m₁ p.g) y₀
    exact ⟨m₁ ≫ σ.hom, by rw [Functor.map_comp_apply]; exact hσ⟩
  let S : ∀ p : PtGal Φ 𝒢₀, Set (Φ.obj p.G) := fun p =>
    {γ | ∃ a : p.G ⟶ X₀ (A := A) T, Φ.map a p.g = basePoint T V hV ∧
      Φ.map a γ = FibreAut.deckAct (X₀ T) (deck T) d (basePoint T V hV) ∧
      (pres p).HCW V hV T a ϖ p.g γ ℓ₀}
  refine exists_deckCharacter_eq_of_sets (isGaloisClass_over hgal Y₀) (isDominating_over hdom Y₀ y₀)
    (isRigid_over hrig Y₀) (X₀ T) (deck T) (basePoint T V hV) (isDeckTorsor T V hV) d S
    ?_ ?_ ?_ ?_
  · -- the sets are mapped into each other
    rintro p q f _ ⟨γ, ⟨a, ha, hγ, hH⟩, rfl⟩
    obtain ⟨mq, hmq⟩ := hpt q
    obtain ⟨⟨mf, hmf⟩, hfg⟩ := f.2
    have hrigf : Φ.map (mf ≫ mq ≫ a₀) = Φ.map a := hrig p.G p.mem.1 _ _ p.g (by
      rw [ha, Functor.map_comp_apply, Functor.map_comp_apply, hmf, hfg, hmq, ha₀])
    refine ⟨mq ≫ a₀, ?_, ?_, ?_⟩
    · rw [Functor.map_comp_apply, hmq, ha₀]
    · rw [← hmf, ← Functor.map_comp_apply, hrigf, hγ]
    · rw [← hmf, ← hfg, ← hmf]
      exact Pres.hcw_map V hV T hX hN ϖ hϖ (pres p) (pres q) mf (mq ≫ a₀) p.g γ ℓ₀
        ((Pres.hcw_congr V hV T (pres p) a _ ϖ p.g γ ℓ₀).1 hH)
  · -- finiteness
    intro p
    obtain ⟨m, -⟩ := hpt p
    refine (hfin p.G (pres p) (m ≫ a₀) p.g).subset ?_
    rintro γ ⟨a, -, -, hH⟩
    exact (Pres.hcw_congr V hV T (pres p) a _ ϖ p.g γ ℓ₀).1 hH
  · -- nonemptiness: the loop
    intro p
    obtain ⟨m, hm⟩ := hpt p
    obtain ⟨γ, hγ, hH⟩ := hne p.G (pres p) (Pres.exists_gal p.mem.1).choose_spec m p.g hm
    exact ⟨γ, m ≫ a₀, by rw [Functor.map_comp_apply, hm, ha₀], hγ, hH⟩
  · -- elements of `S` lie over `δ(d) x₀`
    rintro p γ ⟨a, ha, hγ, -⟩ f hf
    rw [hrig p.G p.mem.1 f a p.g (hf.trans ha.symm), hγ]

end TateObject

end

end TemperedFundamentalGroups
