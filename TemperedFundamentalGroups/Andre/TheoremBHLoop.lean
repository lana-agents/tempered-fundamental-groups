/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.Transport
import TemperedFundamentalGroups.Andre.WCentre

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

omit [IsReduced R] in
/-- Deck transformations of `U` act on the fibre of `X₀` through deck transformations. -/
lemma exists_deck_charG {X₀ : TempObj O R A} (δ : Multiplicative ℤ →* Aut X₀)
    (htors : FibreAut.IsDeckTorsor (F := tempFibre O R A V hV) X₀ δ) (a₀ : P.U ⟶ X₀) (D : P.U ≅ P.U)
    (y : (tempFibre O R A V hV).obj P.U) :
    ∃ k : Multiplicative ℤ, ∀ z, (tempFibre O R A V hV).map (D.hom ≫ a₀) z =
      FibreAut.deckAct X₀ δ k
        ((tempFibre O R A V hV).map a₀ z) := by
  obtain ⟨k, hk, -⟩ := htors ((tempFibre O R A V hV).map a₀ y)
    ((tempFibre O R A V hV).map (D.hom ≫ a₀) y)
  refine ⟨k, fun z => ?_⟩
  rw [Pres.rigid V hV P (D.hom ≫ a₀) (a₀ ≫ (δ k).hom) y
    (by rw [← hk]; exact (Functor.map_comp_apply (tempFibre O R A V hV) a₀
      (δ k).hom y).symm) z,
    Functor.map_comp_apply]
  rfl

omit [IsReduced R] in
/-- Conjugation by a deck transformation does not change the action on the fibre of `X₀`. -/
lemma conj_charG {X₀ : TempObj O R A} (δ : Multiplicative ℤ →* Aut X₀)
    (htors : FibreAut.IsDeckTorsor (F := tempFibre O R A V hV) X₀ δ) (a₀ : P.U ⟶ X₀)
    (κ D : P.U ≅ P.U) (d : Multiplicative ℤ)
    (hκ : ∀ z, (tempFibre O R A V hV).map (κ.hom ≫ a₀) z =
      FibreAut.deckAct X₀ δ d
        ((tempFibre O R A V hV).map a₀ z))
    (y : (tempFibre O R A V hV).obj P.U) (z : (tempFibre O R A V hV).obj P.U) :
    (tempFibre O R A V hV).map ((D.inv ≫ κ.hom ≫ D.hom) ≫ a₀) z =
      FibreAut.deckAct X₀ δ d
        ((tempFibre O R A V hV).map a₀ z) := by
  obtain ⟨k, hk⟩ := P.exists_deck_charG V hV δ htors a₀ D y
  have hinv : (tempFibre O R A V hV).map a₀ ((tempFibre O R A V hV).map D.inv z) =
      FibreAut.deckAct X₀ δ k⁻¹
        ((tempFibre O R A V hV).map a₀ z) := by
    have h := hk ((tempFibre O R A V hV).map D.inv z)
    rw [Functor.map_comp_apply, P.map_hom_inv V hV] at h
    rw [h, ← FibreAut.deckAct_mul, inv_mul_cancel, FibreAut.deckAct_one]
  simp only [Category.assoc, Functor.map_comp_apply] at hk hκ ⊢
  rw [hk, hκ, hinv, ← FibreAut.deckAct_mul, ← FibreAut.deckAct_mul, mul_comm k d, mul_assoc,
    mul_inv_cancel, mul_one]

/-- Deck transformations of `U` act on the fibre of `X₀` through deck transformations. -/
lemma exists_deck_char (a₀ : P.U ⟶ TateObject.X₀ (A := A) T) (D : P.U ≅ P.U)
    (y : (tempFibre O R A V hV).obj P.U) :
    ∃ k : Multiplicative ℤ, ∀ z, (tempFibre O R A V hV).map (D.hom ≫ a₀) z =
      FibreAut.deckAct (TateObject.X₀ T) (TateObject.deck T) k
        ((tempFibre O R A V hV).map a₀ z) :=
  P.exists_deck_charG V hV _ (TateObject.isDeckTorsor T V hV) a₀ D y

/-- Conjugation by a deck transformation does not change the action on the fibre of `X₀`. -/
lemma conj_char (a₀ : P.U ⟶ TateObject.X₀ (A := A) T) (κ D : P.U ≅ P.U) (d : Multiplicative ℤ)
    (hκ : ∀ z, (tempFibre O R A V hV).map (κ.hom ≫ a₀) z =
      FibreAut.deckAct (TateObject.X₀ T) (TateObject.deck T) d
        ((tempFibre O R A V hV).map a₀ z))
    (y : (tempFibre O R A V hV).obj P.U) (z : (tempFibre O R A V hV).obj P.U) :
    (tempFibre O R A V hV).map ((D.inv ≫ κ.hom ≫ D.hom) ≫ a₀) z =
      FibreAut.deckAct (TateObject.X₀ T) (TateObject.deck T) d
        ((tempFibre O R A V hV).map a₀ z) :=
  P.conj_charG V hV _ (TateObject.isDeckTorsor T V hV) a₀ κ D d hκ y z

end Pres


omit [IsReduced R] [Subsingleton A] in
/-- **Finiteness** of the sets `HCW ≤ ℓ₀`, given a component not contracted over the Tate
model (G1). -/
theorem Pres.finite_hcwG [CharZero K] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {X₀ X : TempObj O R A} (P : Pres x X) (a : X ⟶ X₀)
    (g : (tempFibre O R A V hV).obj X)
    {t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀)}
    (ht₁ : IsComp t₁) (hν₁ : P.tateNuG a (lab t₁)) {ℓ₀ : ℝ≥0∞} (hℓ₀ : ℓ₀ ≠ ⊤) :
    {γ | P.HCWG V hV a ϖ g γ ℓ₀}.Finite := by
  obtain ⟨M, hM, hdN⟩ := exists_dN_le (WData.weight_ne_top P.D ϖ) (P.tateNuG a) ht₁ hν₁
  refine (P.finite_len_le V hV hX hN ϖ hϖ g (ℓ₀ := ℓ₀ + (M + M))
    (ENNReal.add_ne_top.2 ⟨hℓ₀, ENNReal.add_ne_top.2 ⟨hM, hM⟩⟩)).subset fun γ hγ => ?_
  exact tlen_le_of_hc_of_le hγ hdN

omit [IsReduced R] [Subsingleton A] in
/-- A component not contracted over the Tate model (G1) excludes components which are points. -/
lemma Pres.noPt_ofG {X₀ X : TempObj O R A} (P : Pres x X) (a : X ⟶ X₀)
    {t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀)}
    (hν₁ : P.tateNuG a (lab t₁)) : P.NoPt := by
  intro j z hj
  have hu := curveConfig_eq_univ_of_singleton P.hdim hj
  refine hν₁ ⟨P.tateMapG a z, ?_⟩
  have hall : ∀ w : P.Lv.Z, w = z := fun w => by
    have h : w ∈ (Set.univ : Set P.Lv.Z) := trivial
    rw [hu] at h
    exact h
  have hC : (curveConfig P.Lv.Z P.hdim).C (lab t₁) = {z} :=
    Set.eq_singleton_iff_unique_mem.2
      ⟨hall ((curveConfig P.Lv.Z P.hdim).η (lab t₁)) ▸ (curveConfig P.Lv.Z P.hdim).η_mem _,
        fun w _ => hall w⟩
  rw [hC, Set.image_singleton]

/-- **Finiteness** of the sets `HCW ≤ ℓ₀`, given a component not contracted over the Tate
model (G1). -/
theorem Pres.finite_hcw [CharZero K] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {X : TempObj O R A} (P : Pres x X) (a : X ⟶ TateObject.X₀ (A := A) T)
    (g : (tempFibre O R A V hV).obj X)
    {t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀)}
    (ht₁ : IsComp t₁) (hν₁ : P.tateNu T a (lab t₁)) {ℓ₀ : ℝ≥0∞} (hℓ₀ : ℓ₀ ≠ ⊤) :
    {γ | P.HCW V hV T a ϖ g γ ℓ₀}.Finite :=
  P.finite_hcwG V hV hX hN ϖ hϖ a g ht₁ hν₁ hℓ₀

/-- A component not contracted over the Tate model (G1) excludes components which are points. -/
lemma Pres.noPt_of {X : TempObj O R A} (P : Pres x X) (a : X ⟶ TateObject.X₀ (A := A) T)
    {t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀)}
    (hν₁ : P.tateNu T a (lab t₁)) : P.NoPt :=
  P.noPt_ofG a hν₁

omit [IsReduced R] [Subsingleton A] [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **I4 for morphisms of members** (from `exists_aut_image_eq_of_pres`). -/
lemma Pres.hasI4 [IsDiscreteValuationRing O] [IsAlgClosed Ω] {X Y : TempObj O R A} (P : Pres x X)
    (Q : Pres x Y) (t₀ : P.Lv.L.B →ₐ[R] Ω)
    (hgal : ∀ t t' : P.Lv.L.B →ₐ[R] Ω, ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B,
      t.comp (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) = t') (mm : P.U ⟶ Q.U) : P.HasI4 Q mm := by
  intro a b hc himg
  exact exists_aut_image_eq_of_pres P Q t₀ (fun t => hgal t₀ t) mm a.2 b.2 hc himg

namespace TateObject

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

omit [IsReduced R] in
/-- **The loop hypothesis `hne` from one loop of `Y₀`** (modulo G1), for any target `X₀`. -/
theorem hne_of_loopG [IsAlgClosed Ω] (X₀ : TempObj O R A) (δ : Multiplicative ℤ →* Aut X₀)
    (x₀ : (tempFibre O R A V hV).obj X₀)
    (htors : FibreAut.IsDeckTorsor (F := tempFibre O R A V hV) X₀ δ)
    (hU : Pres.ModelUnique x X₀) (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {Y₀ : TempObj O R A} (Q : Pres x Y₀) (y₀ : (tempFibre O R A V hV).obj Y₀)
    (a₀ : Y₀ ⟶ X₀) (ha₀ : (tempFibre O R A V hV).map a₀ y₀ = x₀)
    (d : Multiplicative ℤ) (κ : Q.U ≅ Q.U)
    (hκ : ∀ z, (tempFibre O R A V hV).map (κ.hom ≫ Q.iso.inv ≫ a₀) z =
      FibreAut.deckAct X₀ δ d ((tempFibre O R A V hV).map (Q.iso.inv ≫ a₀) z))
    (hG1 : ∀ (X : TempObj O R A) (P : Pres x X) (a : X ⟶ X₀),
      ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
        IsComp t₁ ∧ P.tateNuG a (lab t₁)) :
    ∃ ℓ₀ : ℝ≥0∞, ℓ₀ ≠ ⊤ ∧ ∀ (X : TempObj O R A) (P : Pres x X), (∀ t t' : P.Lv.L.B →ₐ[R] Ω,
      ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B, t.comp (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) = t') →
      ∀ (m : X ⟶ Y₀) (g : (tempFibre O R A V hV).obj X),
      (tempFibre O R A V hV).map m g = y₀ → ∃ γ, (tempFibre O R A V hV).map (m ≫ a₀) γ =
        FibreAut.deckAct X₀ δ d (x₀) ∧
        P.HCWG V hV (m ≫ a₀) ϖ g γ ℓ₀ := by
  have hNoPt : ∀ (X : TempObj O R A) (P : Pres x X) (a : X ⟶ X₀), P.NoPt :=
    fun X P a => by
      obtain ⟨t₁, -, hν₁⟩ := hG1 X P a
      exact P.noPt_ofG a hν₁
  obtain ⟨ℓ₀, hℓ₀, hconj⟩ := Q.exists_conj hX hN ϖ hϖ (hNoPt Y₀ Q a₀) κ
  refine ⟨ℓ₀, hℓ₀, fun X P hgal m g hg => ?_⟩
  let Φ := tempFibre O R A V hV
  let mm : P.U ⟶ Q.U := P.iso.inv ≫ m ≫ Q.iso.hom
  have hmm : P.iso.inv ≫ m ≫ a₀ = mm ≫ Q.iso.inv ≫ a₀ := by simp [mm]
  obtain ⟨t₁, ht₁, hν₁⟩ := hG1 X P (m ≫ a₀)
  have htate : ∀ z, P.tateMapG (m ≫ a₀) z = Q.tateMapG a₀ (Pres.sfm P Q mm z) := fun z => by
    apply Subtype.ext
    change (P.iso.inv ≫ m ≫ a₀).ψ z.1 = (Q.iso.inv ≫ a₀).ψ (mm.ψ z.1)
    rw [hmm, comp_ψ, Scheme.Hom.comp_apply]
  have hνnc : ∀ i, P.tateNuG (m ≫ a₀) i →
      ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (Pres.sfm P Q mm) i := by
    rintro i hν ⟨y, hy⟩
    refine hν ⟨Q.tateMapG a₀ y, ?_⟩
    rw [show P.tateMapG (m ≫ a₀) = Q.tateMapG a₀ ∘ Pres.sfm P Q mm from funext htate,
      Set.image_comp, hy, Set.image_singleton]
  have hνπ : ∀ (π : P.U ≅ P.U) i i', Pres.sfm P P π.hom '' (curveConfig P.Lv.Z P.hdim).C i =
      (curveConfig P.Lv.Z P.hdim).C i' → P.tateNuG (m ≫ a₀) i → P.tateNuG (m ≫ a₀) i' := by
    rintro π i i' h hν ⟨y, hy⟩
    obtain ⟨e, he⟩ := hU P (P.iso.inv ≫ m ≫ a₀) (π.hom ≫ P.iso.inv ≫ m ≫ a₀)
    have hinv : P.tateMapG (m ≫ a₀) ∘ Pres.sfm P P π.hom = e ∘ P.tateMapG (m ≫ a₀) := by
      funext z
      refine (Subtype.ext ?_).trans (he z)
      change (P.iso.inv ≫ m ≫ a₀).ψ (π.hom.ψ z.1) = (π.hom ≫ P.iso.inv ≫ m ≫ a₀).ψ z.1
      simp only [comp_ψ, Scheme.Hom.comp_apply]
    refine hν ((CurveConfig.contr_homeomorph_comp _ e i).1 ⟨y, ?_⟩)
    rw [← hinv, Set.image_comp, h, hy]
  obtain ⟨π, D, -, hπm, hHC⟩ := P.exists_hc_loop Q hX hN ϖ hϖ V hV hgal mm κ (hNoPt X P (m ≫ a₀))
    (Pres.hasI4 P Q (Quotient.out (Φ.map P.iso.hom g) : PreFibre Ω V hV P.U).1.1 hgal mm)
    (P.tateNuG (m ≫ a₀)) hνnc hνπ ht₁ hν₁ hconj (Φ.map P.iso.hom g)
  refine ⟨Φ.map (P.iso.hom ≫ π.hom ≫ P.iso.inv) g, ?_, ?_⟩
  · have hm : m ≫ a₀ = P.iso.hom ≫ mm ≫ Q.iso.inv ≫ a₀ := by simp [mm]
    have h₁ : Φ.map (m ≫ a₀) (Φ.map (P.iso.hom ≫ π.hom ≫ P.iso.inv) g) =
        Φ.map ((D.inv ≫ κ.hom ≫ D.hom) ≫ Q.iso.inv ≫ a₀) (Φ.map (P.iso.hom ≫ mm) g) := by
      rw [hm, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
      congr 1
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc π.hom mm, hπm]
      simp only [Category.assoc]
    rw [h₁, Pres.conj_charG V hV Q δ htors (Q.iso.inv ≫ a₀) κ D d hκ (Φ.map (P.iso.hom ≫ mm) g)]
    congr 1
    rw [← Functor.map_comp_apply, Category.assoc, ← hm, Functor.map_comp_apply, hg, ha₀]
  · unfold Pres.HCWG
    have h₂ : Φ.map P.iso.hom (Φ.map (P.iso.hom ≫ π.hom ≫ P.iso.inv) g) =
        Φ.map π.hom (Φ.map P.iso.hom g) := by
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      simp
    rw [h₂]
    exact hHC

omit [IsReduced R] in
/-- **Theorem B, reduced to its geometric inputs** (any target `X₀`): from (gal), (dom), (rig) of
`galClassW`,
`HarmonicX`, `NodeOfTwoComponents`, one pointed member `(Y₀, y₀)` over `(X₀, x₀)` with an
automorphism `κ` acting through `δ(d)` (hbase), and G1, some element of
`temperedPi1` has character `d`. -/
theorem exists_character_eq_of_loopG [IsAlgClosed Ω] (X₀ : TempObj O R A)
    (δ : Multiplicative ℤ →* Aut X₀) (x₀ : (tempFibre O R A V hV).obj X₀)
    (htors : FibreAut.IsDeckTorsor (F := tempFibre O R A V hV) X₀ δ)
    (hU : Pres.ModelUnique x X₀)
    (hgal : IsGaloisClass (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (hdom : IsDominating (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (hrig : IsRigid (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {Y₀ : TempObj O R A} (hY₀ : galClassW O R A Ω (Level.IsW x) Y₀) (Q : Pres x Y₀)
    (y₀ : (tempFibre O R A V hV).obj Y₀)
    (a₀ : Y₀ ⟶ X₀) (ha₀ : (tempFibre O R A V hV).map a₀ y₀ = x₀)
    (d : Multiplicative ℤ) (κ : Q.U ≅ Q.U)
    (hκ : ∀ z, (tempFibre O R A V hV).map (κ.hom ≫ Q.iso.inv ≫ a₀) z =
      FibreAut.deckAct X₀ δ d ((tempFibre O R A V hV).map (Q.iso.inv ≫ a₀) z))
    (hG1 : ∀ (X : TempObj O R A) (P : Pres x X) (a : X ⟶ X₀),
      ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
        IsComp t₁ ∧ P.tateNuG a (lab t₁)) :
    ∃ τ : temperedPi1 O R A V hV, FibreAut.deckCharacter X₀ δ x₀ htors τ = d := by
  obtain ⟨ℓ₀, hℓ₀, hne⟩ := hne_of_loopG V hV X₀ δ x₀ htors hU hX hN ϖ hϖ Q y₀ a₀ ha₀ d κ hκ hG1
  refine exists_character_eq_of_hcwG V hV X₀ δ x₀ htors hU hgal hdom hrig hX hN ϖ hϖ Y₀ hY₀ y₀ a₀
    ha₀ d ℓ₀
    (fun X P a g => ?_) hne
  obtain ⟨t₁, ht₁, hν₁⟩ := hG1 X P a
  exact P.finite_hcwG V hV hX hN ϖ hϖ a g ht₁ hν₁ hℓ₀

/-- **The loop hypothesis `hne` from one loop of `Y₀`** (modulo G1). -/
theorem hne_of_loop [IsAlgClosed Ω] (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {Y₀ : TempObj O R A} (Q : Pres x Y₀) (y₀ : (tempFibre O R A V hV).obj Y₀)
    (a₀ : Y₀ ⟶ X₀ (A := A) T) (ha₀ : (tempFibre O R A V hV).map a₀ y₀ = basePoint T V hV)
    (d : Multiplicative ℤ) (κ : Q.U ≅ Q.U)
    (hκ : ∀ z, (tempFibre O R A V hV).map (κ.hom ≫ Q.iso.inv ≫ a₀) z =
      FibreAut.deckAct (X₀ T) (deck T) d ((tempFibre O R A V hV).map (Q.iso.inv ≫ a₀) z))
    (hG1 : ∀ (X : TempObj O R A) (P : Pres x X) (a : X ⟶ X₀ (A := A) T),
      ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
        IsComp t₁ ∧ P.tateNu T a (lab t₁)) :
    ∃ ℓ₀ : ℝ≥0∞, ℓ₀ ≠ ⊤ ∧ ∀ (X : TempObj O R A) (P : Pres x X), (∀ t t' : P.Lv.L.B →ₐ[R] Ω,
      ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B, t.comp (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) = t') →
      ∀ (m : X ⟶ Y₀) (g : (tempFibre O R A V hV).obj X),
      (tempFibre O R A V hV).map m g = y₀ → ∃ γ, (tempFibre O R A V hV).map (m ≫ a₀) γ =
        FibreAut.deckAct (X₀ T) (deck T) d (basePoint T V hV) ∧
        P.HCW V hV T (m ≫ a₀) ϖ g γ ℓ₀ :=
  hne_of_loopG V hV (X₀ T) (deck T) (basePoint T V hV) (isDeckTorsor T V hV)
    (TateObject.modelUnique T) hX hN ϖ hϖ Q y₀ a₀ ha₀ d κ hκ hG1

/-- **Theorem B, reduced to its geometric inputs**: from (gal), (dom), (rig) of `galClassW`,
`HarmonicX`, `NodeOfTwoComponents`, one pointed member `(Y₀, y₀)` over `(X₀, x₀)` with an
automorphism `κ` acting through `δ(d)` (hbase), and G1, some element of
`temperedPi1` has character `d`. -/
theorem exists_character_eq_of_loop [IsAlgClosed Ω]
    (hgal : IsGaloisClass (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (hdom : IsDominating (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (hrig : IsRigid (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {Y₀ : TempObj O R A} (hY₀ : galClassW O R A Ω (Level.IsW x) Y₀) (Q : Pres x Y₀)
    (y₀ : (tempFibre O R A V hV).obj Y₀)
    (a₀ : Y₀ ⟶ X₀ (A := A) T) (ha₀ : (tempFibre O R A V hV).map a₀ y₀ = basePoint T V hV)
    (d : Multiplicative ℤ) (κ : Q.U ≅ Q.U)
    (hκ : ∀ z, (tempFibre O R A V hV).map (κ.hom ≫ Q.iso.inv ≫ a₀) z =
      FibreAut.deckAct (X₀ T) (deck T) d ((tempFibre O R A V hV).map (Q.iso.inv ≫ a₀) z))
    (hG1 : ∀ (X : TempObj O R A) (P : Pres x X) (a : X ⟶ X₀ (A := A) T),
      ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
        IsComp t₁ ∧ P.tateNu T a (lab t₁)) :
    ∃ τ : temperedPi1 O R A V hV, character T V hV τ = d :=
  exists_character_eq_of_loopG V hV (X₀ T) (deck T) (basePoint T V hV) (isDeckTorsor T V hV)
    (TateObject.modelUnique T) hgal hdom hrig hX hN ϖ hϖ hY₀ Q y₀ a₀ ha₀ d κ hκ hG1

end TateObject

end

end TemperedFundamentalGroups
