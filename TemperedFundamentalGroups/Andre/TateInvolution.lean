/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateEstrangement
import TemperedFundamentalGroups.Setup.NegOneSumSq
import TemperedFundamentalGroups.Tempered.Comparison
import TemperedFundamentalGroups.Tempered.EtaleInvolution

/-!
# No Kummer involutions: M4 for Tate curves is the wild Tate part (Blueprint §12.10, E16)

**Involutions do not move `√c`.** The covering `Ÿ → X` maps to the finite étale covering
`X' = Spec R[√c]` (`TateObject.toKummer`: the Tate model maps to the trivial model `Spec O`,
the `ℤ`-covering of its special fibre to the one-sheeted covering), so the `ℤ/2`-component of
`χ_Ÿ(α)` is the action of `temperedToEtale α ∈ π₁ᵉᵗ(Spec R)` on the two square roots of `c`
(`ptAct_kummer`). Since `−1` is a sum of squares in `K` (`isSumSq_neg_one`, `K` complete of
residue characteristic `p`), an involution of `π₁ᵉᵗ` fixes all square roots of units
(`EtaleInvolution.fixQ_of_mul_self_eq_one`). Hence:

* **`character₂_snd_eq_one_of_mul_self`**: `α² = 1 ⇒ χ_Ÿ(α) ∈ ℤ × {0}` for `α ∈ Π^tp_X`;
* **`charYY_eq_one_of_elliptic_of_sq`**: an elliptic element `g` of André's group with
  `g² = 1` lies in `Π^tp_Ÿ` (`χ_Y(g) = 0` for elliptic `g`, E13);
* **`tateInvolutionPart_of_tateWildPart`**: `TateWildPart Δ ⇒ TateInvolutionPart Δ`, so the
  involution part of E15 is **not an extra hypothesis**;
* **`estranged_comap_andreTower_iff_tateWild`**, **`ellipticEstrangement_iff_tateWild`**: the
  estrangement of André's tower over `Δ` (equivalently the M4 input `EllipticEstrangement Δ`
  relative to the rigid levels) is **equivalent to `TateWildPart Δ` alone**;
* consumers: [SemiAnbd] Thm. 3.7(iii) for `Δ` and (iv) for André's group from `TateWildPart`
  alone (`exists_le_stab_andreTower_of_tateWild`, `exists_eq_stab_of_maximal_of_tateWild`);
  `PSCAdj` and CG3' from `TateWildPart ⊤` and nontrivial edge-like subgroups (M2)
  (`pscAdj_andreTower_of_tateWild`, `isGraphic_iff_andreTower_of_tateWild`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open EtaleInvolution

namespace TateObject

/-! ### The map `Ÿ → X' = Spec R[√c]` to a finite étale cover -/

section Model

variable {K : Type u} [Field K] {O : ValuationSubring K} {R : Type u} [CommRing R] [Algebra K R]
  [IsReduced R] {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  [SMulCommClass A K R] (D : DoubleData O R)

/-- **The Kummer covering `R[√c]`** as a (coded) finite étale cover. -/
abbrev kummerObj : EquivEtale R A :=
  etObj A (QE D.c) (QE.etale D.two_unit D.c_unit) inferInstance

variable (O) in
/-- `Spec O ≅ ℙ⁰_O`, the inverse of the structure map of the trivial model. -/
def trivInv :=
  CategoryTheory.inv (ModelCode.trivial O).toSpec

omit [IsReduced R] [Subsingleton A] [SMulCommClass A K R] in
lemma trivInv_toSpec : trivInv O ≫ (ModelCode.trivial O).toSpec = 𝟙 _ := by
  simp [trivInv]

/-- The algebra map of `X' → Spec R[√c]`. -/
def kummerMap : (kummerObj (A := A) D).B →ₐ[R] (level' (A := A) D).B :=
  (QuadraticLevel.equivAdjoinRoot D.c).symm.toAlgHom.comp (etEquiv A (QE D.c) _ _).toAlgHom

/-- The morphism of levels `X' → Spec R[√c]`. -/
def kummerLevelHom : (level' (A := A) D) ⟶ (kummerObj (A := A) D).level where
  f := kummerMap D
  r := 1
  r_a _ := Subsingleton.elim _ _
  f_σ g y := by
    rw [level'_H_eq_one D g]
    rfl

/-- **`Ÿ → Spec R[√c]`**: the identity of `X'`, the Tate model mapped to the trivial model
`Spec O`, the `ℤ`-covering of the special fibre mapped to the one-sheeted covering. -/
def toKummer : Yddot (A := A) D ⟶ (etaleToTemp O R A).obj (kummerObj (A := A) D) where
  φ := kummerLevelHom D
  ψ := (level₂ (A := A) D).c.toSpec ≫ trivInv O
  ψ_toSpec := by
    change ((level₂ (A := A) D).c.toSpec ≫ trivInv O) ≫
      (ModelCode.trivial O).toSpec = _
    rw [Category.assoc, trivInv_toSpec, Category.comp_id]
  j_ψ := by
    change (level₂ (A := A) D).j ≫ ((level₂ (A := A) D).c.toSpec ≫ trivInv O) =
      Spec.map (CommRingCat.ofHom ((kummerLevelHom (A := A) D).f : _ →+* _)) ≫
        (Spec.map (CommRingCat.ofHom (levelStructureMap O R A (kummerObj (A := A) D).level)) ≫
          trivInv O)
    rw [← Category.assoc, (level₂ (A := A) D).j_toSpec, ← Category.assoc,
      ← spec_levelStructureMap O R A (kummerLevelHom (A := A) D)]
  h x := ⟨(specialFibreMap ((level₂ (A := A) D).c.toSpec ≫ trivInv O)
    (by
      change ((level₂ (A := A) D).c.toSpec ≫ trivInv O) ≫ (ModelCode.trivial O).toSpec = _
      rw [Category.assoc, trivInv_toSpec, Category.comp_id]) x.1.1, 0), Set.mem_univ _,
    Nat.zero_lt_one⟩
  continuous_h := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ continuous_const) _
    exact (continuous_specialFibreMap _ _).comp (Yddot (A := A) D).P.continuous_proj
  fst_h _ := rfl
  h_act g x := by
    rw [level'_H_eq_one D g, map_one, map_one]
    rfl

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- The fibre map of `Ÿ → Spec R[√c]` on geometric points. -/
lemma fibre_toKummer (q : TempObj.PreFibre Ω V hV (Yddot (A := A) D)) :
    etaleToTempFibreEquiv O R A V hV (kummerObj (A := A) D)
      ((tempFibre O R A V hV).map (toKummer (A := A) D) ⟦q⟧) = q.1.1.comp (kummerMap D) :=
  rfl

/-- **The action of `temperedToEtale α` on the square roots of `c`** is the `ℤ/2`-component of
`χ_Ÿ(α)`. -/
theorem ptAct_kummer (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) (α : temperedPi1 O R A V hV) :
    ptAct (temperedToEtale O R A V hV α) (QE D.c) (QE.etale D.two_unit D.c_unit) inferInstance
      ((t₀ (A := A) D s hs).comp (QuadraticLevel.equivAdjoinRoot D.c).symm.toAlgHom) =
      ((t₀ (A := A) D s hs).comp (σPow D (character₂ (A := A) D V hV s hs α).2)).comp
        (QuadraticLevel.equivAdjoinRoot D.c).symm.toAlgHom := by
  set E := etaleToTempFibreEquiv O R A V hV (kummerObj (A := A) D)
  set b := basePoint₂ (A := A) D V hV s hs
  -- `α` on the base point of `Ÿ`
  have h₁ : α.app (Yddot (A := A) D) b =
      FibreAut.deckAct (F := tempFibre O R A V hV) (Yddot (A := A) D) (deck₂ D)
        (character₂ (A := A) D V hV s hs α) b :=
    (FibreAut.deckAct_deckCharacterFun (F := tempFibre O R A V hV) (Yddot (A := A) D)
      (deck₂ D) b (isDeckTorsor₂ D V hV) α).symm
  -- the images in the fibre of `R[√c]`
  have hb : E ((tempFibre O R A V hV).map (toKummer (A := A) D) b) =
      (t₀ (A := A) D s hs).comp (kummerMap D) := rfl
  have hαb : E ((tempFibre O R A V hV).map (toKummer (A := A) D)
      (α.app (Yddot (A := A) D) b)) =
      ((t₀ (A := A) D s hs).comp (σPow D (character₂ (A := A) D V hV s hs α).2)).comp
        (kummerMap D) := by
    rw [h₁]
    rfl
  have happ : appAlg (temperedToEtale O R A V hV α) (kummerObj (A := A) D)
      ((t₀ (A := A) D s hs).comp (kummerMap D)) =
      ((t₀ (A := A) D s hs).comp (σPow D (character₂ (A := A) D V hV s hs α).2)).comp
        (kummerMap D) := by
    rw [← hαb, ← FibreAut.app_naturality, ← hb]
    change E (α.app _ (E.symm (E _))) = _
    rw [Equiv.symm_apply_apply]
  unfold ptAct
  have ht : ((t₀ (A := A) D s hs).comp
      (QuadraticLevel.equivAdjoinRoot D.c).symm.toAlgHom).comp
        (etEquiv A (QE D.c) (QE.etale D.two_unit D.c_unit) inferInstance).toAlgHom =
      (t₀ (A := A) D s hs).comp (kummerMap D) := rfl
  rw [ht, happ]
  ext
  simp [kummerMap]

/-- **An involution of `Π^tp_X` does not move `√c`**: `α² = 1 ⇒ χ_Ÿ(α) ∈ ℤ × {0}`. -/
theorem character₂_snd_eq_one_of_mul_self [IsAlgClosed Ω] (hK : IsSumSq (-1 : K)) (s : Ω)
    (hs : s ^ 2 = algebraMap R Ω D.c) {α : temperedPi1 O R A V hV} (hα : α * α = 1) :
    (character₂ (A := A) D V hV s hs α).2 = 1 := by
  have hg : temperedToEtale O R A V hV α * temperedToEtale O R A V hV α = 1 := by
    rw [← map_mul, hα, map_one]
  have hfix := fixQ_of_mul_self_eq_one hK (temperedToEtale O R A V hV α) hg D.two_unit
    D.c_unit ((t₀ (A := A) D s hs).comp (QuadraticLevel.equivAdjoinRoot D.c).symm.toAlgHom)
  rw [ptAct_kummer D V hV s hs α] at hfix
  have h' : (t₀ (A := A) D s hs).comp (σPow D (character₂ (A := A) D V hV s hs α).2) =
      (t₀ (A := A) D s hs).comp (σPow D 1) := by
    rw [σPow_one]
    ext z
    have := congrArg (fun φ : QE D.c →ₐ[R] Ω ↦ φ (QuadraticLevel.equivAdjoinRoot D.c z)) hfix
    simpa using this
  exact comp_σPow_injective D _ h'

end Model

end TateObject

/-! ### André's tower: the wild Tate part suffices -/

open GaloisLimit TateObject

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
  [Finite A] [SMulCommClass A K R]

section Double

variable (D : DoubleData O R) (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)

/-- **Involutions of André's group do not move `√c`.** -/
theorem charYY_snd_eq_one_of_sq {g : andreGroup O R A V hV} (hg : g ^ 2 = 1) :
    (charYY (A := A) V hV hp hR D s hs g).2 = 1 := by
  refine character₂_snd_eq_one_of_mul_self D V hV (isSumSq_neg_one O hp) s hs ?_
  rw [← map_mul, ← sq, hg, map_one]

/-- **An elliptic involution of André's group lies in `Π^tp_Ÿ`.** -/
theorem charYY_eq_one_of_elliptic_of_sq {g : andreGroup O R A V hV}
    (he : (andreTower (R := R) (A := A) V hV hp hR).Elliptic g) (hg : g ^ 2 = 1) :
    charYY (A := A) V hV hp hR D s hs g = 1 := by
  refine Prod.ext ?_ (charYY_snd_eq_one_of_sq V hV hp hR D s hs hg)
  rw [charYY_fst, charY_eq_one_of_elliptic V hV hp hR D.toData he]
  rfl

/-- **The involution part follows from the wild part.** -/
theorem tateInvolutionPart_of_tateWildPart (Δ : Subgroup (andreGroup O R A V hV))
    (hW : TateWildPart (A := A) V hV hp hR D s hs Δ) : TateInvolutionPart (A := A) V hV hp hR Δ :=
  fun g ⟨hgΔ, he, hg2⟩ ↦ hW g ⟨hgΔ, he, charYY_eq_one_of_elliptic_of_sq V hV hp hR D s hs he hg2⟩

/-- **Estrangement of André's tower over `Δ` is equivalent to the wild Tate part alone.** -/
theorem estranged_comap_andreTower_iff_tateWild (Δ : Subgroup (andreGroup O R A V hV)) :
    ((andreTower (R := R) (A := A) V hV hp hR).comap Δ.subtype).Estranged ↔
      TateWildPart (A := A) V hV hp hR D s hs Δ := by
  rw [estranged_comap_andreTower_iff_tate V hV hp hR D s hs Δ]
  exact ⟨And.left, fun hW ↦ ⟨hW, tateInvolutionPart_of_tateWildPart V hV hp hR D s hs Δ hW⟩⟩

/-- **The M4 input relative to the rigid levels, for the Tate curve, is the wild Tate part.** -/
theorem ellipticEstrangement_iff_tateWild (Δ : Subgroup (andreGroup O R A V hV)) :
    EllipticEstrangement V hV hp hR Δ ↔ TateWildPart (A := A) V hV hp hR D s hs Δ := by
  rw [ellipticEstrangement_iff_tate V hV hp hR D s hs Δ]
  exact ⟨And.left, fun hW ↦ ⟨hW, tateInvolutionPart_of_tateWildPart V hV hp hR D s hs Δ hW⟩⟩

/-- **Estrangement of André's tower ⇔ the wild Tate part for the whole group.** -/
theorem estranged_andreTower_iff_tateWild :
    (andreTower (R := R) (A := A) V hV hp hR).Estranged ↔
      TateWildPart (A := A) V hV hp hR D s hs ⊤ := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  rw [← estranged_comap_andreTower_iff_tateWild V hV hp hR D s hs ⊤,
    TreeTower.estranged_comap_subtype_iff, TreeTower.estranged_iff_estrangedOn_univ]
  exact ⟨fun h ↦ h.mono fun _ _ ↦ trivial, fun h ↦ h.mono fun _ _ ↦ Subgroup.mem_top _⟩

/-- **[SemiAnbd] Thm. 3.7(iii) for `Δ` (system form) from the wild Tate part alone.** -/
theorem exists_le_stab_andreTower_of_tateWild (Δ : Subgroup (andreGroup O R A V hV))
    (hW : TateWildPart (A := A) V hV hp hR D s hs Δ)
    (H : Subgroup (andreGroup O R A V hV)) (hHΔ : H ≤ Δ) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ e : (andreTower (R := R) (A := A) V hV hp hR).Sys, H ≤ TreeTower.stab e :=
  exists_le_stab_andreTower_of_tate V hV hp hR D s hs Δ hW
    (tateInvolutionPart_of_tateWildPart V hV hp hR D s hs Δ hW) H hHΔ hH1 hH

/-- **[SemiAnbd] Thm. 3.7(iv) for André's group (system form) from the wild Tate part alone.** -/
theorem exists_eq_stab_of_maximal_of_tateWild (hW : TateWildPart (A := A) V hV hp hR D s hs ⊤)
    (H : Subgroup (andreGroup O R A V hV)) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV)))
    (hmax : ∀ H' : Subgroup (andreGroup O R A V hV), IsCompact (H' : Set (andreGroup O R A V hV)) →
      H ≤ H' → H' = H) :
    ∃ e : (andreTower (R := R) (A := A) V hV hp hR).Sys, H = TreeTower.stab e :=
  exists_eq_stab_of_maximal_of_tate V hV hp hR D s hs hW
    (tateInvolutionPart_of_tateWildPart V hV hp hR D s hs ⊤ hW) H hH1 hH hmax

/-- **`PSCAdj` for André's group of a Tate curve** from the wild Tate part and nontrivial
edge-like subgroups (M2). -/
theorem pscAdj_andreTower_of_tateWild (hW : TateWildPart (A := A) V hV hp hR D s hs ⊤)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    (andreTower (R := R) (A := A) V hV hp hR).PSCAdj :=
  pscAdj_andreTower_of_estranged' V hV hp hR
    ((estranged_andreTower_iff_tateWild V hV hp hR D s hs).2 hW) hedge

/-- **CG3' for André's group of a Tate curve** from the wild Tate part and nontrivial edge-like
subgroups (M2), against a functorial estranged tree tower without branch inversions. -/
theorem isGraphic_iff_andreTower_of_tateWild {Γ' : Type*} [Group Γ'] {J' : Type*}
    [Category J'] [IsCofilteredOrEmpty J'] {T' : TreeTower Γ' J'}
    {α : andreGroup O R A V hV ≃* Γ'} (hW : TateWildPart (A := A) V hV hp hR D s hs ⊤)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥)
    (hT' : T'.IsFunctorial) (hE' : T'.Estranged) (hB' : T'.NoBranchSwap)
    (hedge' : ∀ e : T'.Sys, (∀ j, ∃ (k : J') (_ : k ⟶ j), T'.kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    TreeTower.IsGraphic (andreTower (R := R) (A := A) V hV hp hR) T' α ↔
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR) T' α :=
  isGraphic_iff_andreTower_of_estranged' V hV hp hR
    ((estranged_andreTower_iff_tateWild V hV hp hR D s hs).2 hW) hedge hT' hE' hB' hedge'

end Double

end

end TemperedFundamentalGroups
