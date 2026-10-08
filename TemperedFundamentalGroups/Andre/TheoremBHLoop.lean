/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.Transport

/-!
# The loop hypothesis `hne` of Theorem B from one loop of `Y₀` (Blueprint §10.3.8, transport)

`TateObject.hne_of_loop`: given a member `Y₀` (presentation `Q`) with an automorphism `κ` of
`U₀ = Q.U` acting on the fibre of the Tate object `X₀` through `δ(d)`, every member `X` over
`(Y₀, y₀)` has a fibre element over `δ(d) x₀` with `HCW ≤ ℓ₀`, for a uniform `ℓ₀ < ⊤`
(`Pres.exists_conj`, `Pres.exists_hc_loop`). The remaining inputs are stated as hypotheses:
no component of a member is a point (`NoPt`), some component is not contracted over the Tate
model (G1), and relative G-transitivity (I4, `HasI4`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open scoped ENNReal

namespace TemperedFundamentalGroups

open CurveConfig

noncomputable section

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) {x : R}
  (T : TateObject.Data O R)

namespace Pres

variable {X Y : TempObj O R A} (P : Pres x X)

omit [IsReduced R] in
/-- **Rigidity on fibres** for the Galois object of a presentation. -/
lemma rigid {Z : TempObj O R A} (F F' : P.U ⟶ Z) (y : (tempFibre O R A V hV).obj P.U)
    (h : (tempFibre O R A V hV).map F y = (tempFibre O R A V hV).map F' y)
    (z : (tempFibre O R A V hV).obj P.U) :
    (tempFibre O R A V hV).map F z = (tempFibre O R A V hV).map F' z := by
  haveI : IsSchemeTheoreticallyDominant P.Lv.j := P.dom
  exact congrFun (fibreMap_eq_of_eq' (Lv := P.Lv) V hV P.idem F F' y h) z

omit [IsReduced R] [Subsingleton A] in
lemma map_hom_inv (D : P.U ≅ P.U) (z : (tempFibre O R A V hV).obj P.U) :
    (tempFibre O R A V hV).map D.hom ((tempFibre O R A V hV).map D.inv z) = z := by
  rw [← Functor.map_comp_apply, Iso.inv_hom_id, Functor.map_id_apply]

/-- Deck transformations of `U` act on the fibre of `X₀` through deck transformations. -/
lemma exists_deck_char (a₀ : P.U ⟶ TateObject.X₀ (A := A) T) (D : P.U ≅ P.U)
    (y : (tempFibre O R A V hV).obj P.U) :
    ∃ k : Multiplicative ℤ, ∀ z, (tempFibre O R A V hV).map (D.hom ≫ a₀) z =
      FibreAut.deckAct (TateObject.X₀ T) (TateObject.deck T) k
        ((tempFibre O R A V hV).map a₀ z) := by
  obtain ⟨k, hk, -⟩ := TateObject.isDeckTorsor T V hV ((tempFibre O R A V hV).map a₀ y)
    ((tempFibre O R A V hV).map (D.hom ≫ a₀) y)
  refine ⟨k, fun z => ?_⟩
  rw [Pres.rigid V hV P (D.hom ≫ a₀) (a₀ ≫ (TateObject.deck T k).hom) y
    (by rw [← hk]; exact (Functor.map_comp_apply (tempFibre O R A V hV) a₀
      (TateObject.deck T k).hom y).symm) z,
    Functor.map_comp_apply]
  rfl

/-- Conjugation by a deck transformation does not change the action on the fibre of `X₀`. -/
lemma conj_char (a₀ : P.U ⟶ TateObject.X₀ (A := A) T) (κ D : P.U ≅ P.U) (d : Multiplicative ℤ)
    (hκ : ∀ z, (tempFibre O R A V hV).map (κ.hom ≫ a₀) z =
      FibreAut.deckAct (TateObject.X₀ T) (TateObject.deck T) d
        ((tempFibre O R A V hV).map a₀ z))
    (y : (tempFibre O R A V hV).obj P.U) (z : (tempFibre O R A V hV).obj P.U) :
    (tempFibre O R A V hV).map ((D.inv ≫ κ.hom ≫ D.hom) ≫ a₀) z =
      FibreAut.deckAct (TateObject.X₀ T) (TateObject.deck T) d
        ((tempFibre O R A V hV).map a₀ z) := by
  obtain ⟨k, hk⟩ := P.exists_deck_char V hV T a₀ D y
  have hinv : (tempFibre O R A V hV).map a₀ ((tempFibre O R A V hV).map D.inv z) =
      FibreAut.deckAct (TateObject.X₀ T) (TateObject.deck T) k⁻¹
        ((tempFibre O R A V hV).map a₀ z) := by
    have h := hk ((tempFibre O R A V hV).map D.inv z)
    rw [Functor.map_comp_apply, P.map_hom_inv V hV] at h
    rw [h, ← FibreAut.deckAct_mul, inv_mul_cancel, FibreAut.deckAct_one]
  simp only [Category.assoc, Functor.map_comp_apply] at hk hκ ⊢
  rw [hk, hκ, hinv, ← FibreAut.deckAct_mul, ← FibreAut.deckAct_mul, mul_comm k d, mul_assoc,
    mul_inv_cancel, mul_one]

end Pres


namespace TateObject

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- **The loop hypothesis `hne` from one loop of `Y₀`** (modulo `NoPt`, G1 and I4). -/
theorem hne_of_loop [IsAlgClosed Ω] (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {Y₀ : TempObj O R A} (Q : Pres x Y₀) (y₀ : (tempFibre O R A V hV).obj Y₀)
    (a₀ : Y₀ ⟶ X₀ (A := A) T) (ha₀ : (tempFibre O R A V hV).map a₀ y₀ = basePoint T V hV)
    (d : Multiplicative ℤ) (κ : Q.U ≅ Q.U)
    (hκ : ∀ z, (tempFibre O R A V hV).map (κ.hom ≫ Q.iso.inv ≫ a₀) z =
      FibreAut.deckAct (X₀ T) (deck T) d ((tempFibre O R A V hV).map (Q.iso.inv ≫ a₀) z))
    (hnsQ : Q.NoPt) (hNoPt : ∀ (X : TempObj O R A) (P : Pres x X), P.NoPt)
    (hG1 : ∀ (X : TempObj O R A) (P : Pres x X) (a : X ⟶ X₀ (A := A) T),
      ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
        IsComp t₁ ∧ P.tateNu T a (lab t₁))
    (hI4 : ∀ (X : TempObj O R A) (P : Pres x X) (mm : P.U ⟶ Q.U), P.HasI4 Q mm) :
    ∃ ℓ₀ : ℝ≥0∞, ℓ₀ ≠ ⊤ ∧ ∀ (X : TempObj O R A) (P : Pres x X), (∀ t t' : P.Lv.L.B →ₐ[R] Ω,
      ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B, t.comp (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) = t') →
      ∀ (m : X ⟶ Y₀) (g : (tempFibre O R A V hV).obj X),
      (tempFibre O R A V hV).map m g = y₀ → ∃ γ, (tempFibre O R A V hV).map (m ≫ a₀) γ =
        FibreAut.deckAct (X₀ T) (deck T) d (basePoint T V hV) ∧
        P.HCW V hV T (m ≫ a₀) ϖ g γ ℓ₀ := by
  obtain ⟨ℓ₀, hℓ₀, hconj⟩ := Q.exists_conj hX hN ϖ hϖ hnsQ κ
  refine ⟨ℓ₀, hℓ₀, fun X P hgal m g hg => ?_⟩
  let Φ := tempFibre O R A V hV
  let mm : P.U ⟶ Q.U := P.iso.inv ≫ m ≫ Q.iso.hom
  have hmm : P.iso.inv ≫ m ≫ a₀ = mm ≫ Q.iso.inv ≫ a₀ := by simp [mm]
  obtain ⟨t₁, ht₁, hν₁⟩ := hG1 X P (m ≫ a₀)
  have htate : ∀ z, P.tateMap T (m ≫ a₀) z = Q.tateMap T a₀ (Pres.sfm P Q mm z) := fun z => by
    apply Subtype.ext
    change (P.iso.inv ≫ m ≫ a₀).ψ z.1 = (Q.iso.inv ≫ a₀).ψ (mm.ψ z.1)
    rw [hmm, comp_ψ, Scheme.Hom.comp_apply]
  have hνnc : ∀ i, P.tateNu T (m ≫ a₀) i →
      ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (Pres.sfm P Q mm) i := by
    rintro i hν ⟨y, hy⟩
    refine hν ⟨Q.tateMap T a₀ y, ?_⟩
    rw [show P.tateMap T (m ≫ a₀) = Q.tateMap T a₀ ∘ Pres.sfm P Q mm from funext htate,
      Set.image_comp, hy, Set.image_singleton]
  have hνπ : ∀ (π : P.U ≅ P.U) i i', Pres.sfm P P π.hom '' (curveConfig P.Lv.Z P.hdim).C i =
      (curveConfig P.Lv.Z P.hdim).C i' → P.tateNu T (m ≫ a₀) i → P.tateNu T (m ≫ a₀) i' := by
    rintro π i i' h hν ⟨y, hy⟩
    refine hν ⟨y, ?_⟩
    have hinv : P.tateMap T (m ≫ a₀) ∘ Pres.sfm P P π.hom = P.tateMap T (m ≫ a₀) := by
      funext z
      apply Subtype.ext
      change (P.iso.inv ≫ m ≫ a₀).ψ (π.hom.ψ z.1) = (P.iso.inv ≫ m ≫ a₀).ψ z.1
      rw [← Scheme.Hom.comp_apply, ← comp_ψ, P.ψ_eq T (π.hom ≫ P.iso.inv ≫ m ≫ a₀)]
    rw [← hy, ← h, ← Set.image_comp, hinv]
  obtain ⟨π, D, -, hπm, hHC⟩ := P.exists_hc_loop Q hX hN ϖ hϖ V hV hgal mm κ (hNoPt X P)
    (hI4 X P mm) (P.tateNu T (m ≫ a₀)) hνnc hνπ ht₁ hν₁ hconj (Φ.map P.iso.hom g)
  refine ⟨Φ.map (P.iso.hom ≫ π.hom ≫ P.iso.inv) g, ?_, ?_⟩
  · have hm : m ≫ a₀ = P.iso.hom ≫ mm ≫ Q.iso.inv ≫ a₀ := by simp [mm]
    have h₁ : Φ.map (m ≫ a₀) (Φ.map (P.iso.hom ≫ π.hom ≫ P.iso.inv) g) =
        Φ.map ((D.inv ≫ κ.hom ≫ D.hom) ≫ Q.iso.inv ≫ a₀) (Φ.map (P.iso.hom ≫ mm) g) := by
      rw [hm, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
      congr 1
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc π.hom mm, hπm]
      simp only [Category.assoc]
    rw [h₁, Pres.conj_char V hV T Q (Q.iso.inv ≫ a₀) κ D d hκ (Φ.map (P.iso.hom ≫ mm) g)]
    congr 1
    rw [← Functor.map_comp_apply, Category.assoc, ← hm, Functor.map_comp_apply, hg, ha₀]
  · unfold Pres.HCW
    have h₂ : Φ.map P.iso.hom (Φ.map (P.iso.hom ≫ π.hom ≫ P.iso.inv) g) =
        Φ.map π.hom (Φ.map P.iso.hom g) := by
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      simp
    rw [h₂]
    exact hHC

end TateObject

end

end TemperedFundamentalGroups
