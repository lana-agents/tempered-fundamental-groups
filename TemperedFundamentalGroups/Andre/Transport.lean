/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TheoremBH
import TemperedFundamentalGroups.Topology.CurveGeneric

/-!
# Transport of loop elements between members (Blueprint §10.3.8, transport)

Tree-level facts on the universal coverings of members, used to transport one loop element of a
fixed member `Y₀` to every member over it.

* `Pres.covMap_comp`, `Pres.covMap_id`: functoriality of the maps of universal coverings.
* `Pres.covMap_gen`: a morphism maps the generic point of a non-contracted component vertex to the
  generic point of its image vertex.
* `Pres.exists_deck`: the deck transformations of `U` act transitively on the component vertices
  with a given label.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open scoped ENNReal

namespace TemperedFundamentalGroups

open CurveConfig

/-- In the curve configuration of a curve, generic points are not special. -/
lemma curveConfig_η_notMem_S {Z : Type u} [TopologicalSpace Z] [NoetherianSpace Z] [T0Space Z]
    [QuasiSober Z] (hdim : topologicalKrullDim Z ≤ 1) (i : irreducibleComponents Z) :
    (curveConfig Z hdim).η i ∉ (curveConfig Z hdim).S := by
  rintro ⟨a, b, hab, ha, hb⟩
  rw [curveConfig_η] at ha hb
  have hcl : ∀ c : irreducibleComponents Z, i.2.1.genericPoint ∈ c.1 → c = i := by
    intro c hc
    have hgen : closure {i.2.1.genericPoint} = i.1 :=
      i.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents i.1 i.2)
    have hsub : i.1 ⊆ c.1 := hgen ▸ (isClosed_of_mem_irreducibleComponents c.1 c.2).closure_subset_iff.2
      (singleton_subset_iff.2 hc)
    exact Subtype.ext (subset_antisymm (i.2.2 c.2.1 hsub) hsub)
  exact hab ((hcl a ha).trans (hcl b hb).symm)

lemma CurveConfig.gen_snd_of_inl {Z : Type u} [TopologicalSpace Z] {ι : Type*}
    {K : CurveConfig Z ι} {r : ι} {t : K.Tree r} {i : ι} (h : t.1.head? = some (.inl i))
    (hS : K.η i ∉ K.S) : (gen t).1.2 = t := by
  rw [gen_of_inl h, incl_of_notMem hS]

noncomputable section

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  {x : R}

namespace Pres

variable {X Y W : TempObj O R A} (P : Pres x X) (Q : Pres x Y) (S : Pres x W)

lemma covMap_comp (m : P.U ⟶ Q.U) (n : Q.U ⟶ S.U) (e : P.E) :
    covMap P S (m ≫ n) e = covMap Q S n (covMap P Q m e) := by
  simp only [covMap, comp_h, Function.comp_apply, Q.Θ'_ecov]

lemma covMap_id (e : P.E) : covMap P P (𝟙 P.U) e = e := by
  simp only [covMap, id_h, id, P.ecov_Θ']

/-- The map of special fibres of a morphism of Galois objects. -/
abbrev sfm (m : P.U ⟶ Q.U) : P.Lv.Z → Q.Lv.Z := specialFibreMap m.ψ m.ψ_toSpec

lemma hNC (m : P.U ⟶ Q.U) (i : irreducibleComponents P.Lv.Z)
    (hi : ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (sfm P Q m) i) :
    ∃ i', sfm P Q m '' (curveConfig P.Lv.Z P.hdim).C i = (curveConfig Q.Lv.Z Q.hdim).C i' ∧
      sfm P Q m ((curveConfig P.Lv.Z P.hdim).η i) ∉ (curveConfig Q.Lv.Z Q.hdim).S :=
  curveConfig_contr_or P.hdim Q.hdim (continuous_specialFibreMap _ _)
    (isClosedMap_specialFibreMap m) i hi

/-- **Generic points of non-contracted component vertices go to generic points.** -/
lemma covMap_gen (m : P.U ⟶ Q.U) {t : (curveConfig P.Lv.Z P.hdim).Tree
      (universalCovering.root P.hdim P.z₀)} {i : irreducibleComponents P.Lv.Z}
    (ht : t.1.head? = some (.inl i))
    (hc : ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (sfm P Q m) i) :
    covMap P Q m (gen t) = gen (img (covMap P Q m) t) := by
  obtain ⟨i', hi', hii'⟩ := map_gen_of_not_contr (covMap_fst P Q m) (P.hNC Q m) ht hc
  obtain ⟨-, -, hS⟩ := P.hNC Q m i hc
  have hη := curveConfig_map_η P.hdim Q.hdim (continuous_specialFibreMap m.ψ m.ψ_toSpec) hii'
  exact eq_gen_of hi' (by rw [covMap_fst, gen_fst_of_inl ht]; exact hη) (hη ▸ hS)

/-- **Deck transformations are transitive on component vertices with the same label.** -/
lemma exists_deck {t₁ t₂ : (curveConfig Q.Lv.Z Q.hdim).Tree (universalCovering.root Q.hdim Q.z₀)}
    {i : irreducibleComponents Q.Lv.Z} (h₁ : t₁.1.head? = some (.inl i))
    (h₂ : t₂.1.head? = some (.inl i)) :
    ∃ D : Q.U ≅ Q.U, D.hom.ψ = 𝟙 _ ∧ covMap Q Q D.hom (gen t₁) = gen t₂ := by
  let hp := universalCovering.isUniversalCovering.{u, u, u} Q.hdim Q.z₀
  have hpe : universalCovering.proj Q.hdim Q.z₀ (gen t₂) =
      Q.Lv.ρs 1 (universalCovering.proj Q.hdim Q.z₀ (gen t₁)) := by
    rw [map_one, Homeomorph.one_apply]
    change (gen t₂).1.1 = (gen t₁).1.1
    rw [gen_fst_of_inl h₁, gen_fst_of_inl h₂]
  obtain ⟨τ, hτ, hτe⟩ := exists_lift Q.Lv hp 1 hpe
  let π : Pi Q.Lv (universalCovering.proj Q.hdim Q.z₀) := ⟨(1, τ), hτ⟩
  refine ⟨deck hp hp.countable_fibre π, rfl, ?_⟩
  change Q.ecov ((deckHom hp hp.countable_fibre π).h (Q.Θ' ⟨1, gen t₁⟩)) = gen t₂
  rw [show (deckHom hp hp.countable_fibre π).h (Q.Θ' ⟨1, gen t₁⟩) =
    Q.Θ' (deckInd π ⟨1, gen t₁⟩) from deckHom_h_Θ π _]
  change Q.ecov (Q.Θ' ⟨1 * 1⁻¹, τ (gen t₁)⟩) = gen t₂
  rw [hτe, mul_inv_cancel, Q.ecov_Θ']

lemma sfm_injective (f : P.U ≅ Q.U) : Function.Injective (sfm P Q f.hom) := by
  have key : ∀ z, sfm Q P f.inv (sfm P Q f.hom z) = z := fun z => Subtype.ext (by
    change (f.hom.ψ ≫ f.inv.ψ) z.1 = z.1
    rw [← comp_ψ, f.hom_inv_id, id_ψ]
    rfl)
  intro a b h
  rw [← key a, ← key b, h]

/-- No component of the special fibre is a single point. -/
def NoPt : Prop :=
  ∀ (j : irreducibleComponents P.Lv.Z) (z : P.Lv.Z), (curveConfig P.Lv.Z P.hdim).C j ≠ {z}

lemma iso_not_contr (f : P.U ≅ Q.U) (hns : P.NoPt) (i : irreducibleComponents P.Lv.Z) :
    ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (sfm P Q f.hom) i :=
  curveConfig_not_contr_of_injective P.hdim (P.sfm_injective Q f) hns i

lemma covMap_inv_hom (f : P.U ≅ Q.U) (e : P.E) : covMap Q P f.inv (covMap P Q f.hom e) = e := by
  rw [← covMap_comp, f.hom_inv_id, covMap_id]

section Conj

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- **Conjugating a loop by deck transformations** (the uniform bound `ℓ₀`): for an automorphism
`κ` of `U`, there is `ℓ₀ < ⊤` such that at every component vertex `ŵ` some conjugate
`D⁻¹ κ D` by a deck transformation `D` moves `gen ŵ` to the generic point of the end of a walk
from `ŵ` of weight `≤ ℓ₀`. -/
theorem exists_conj (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (hns : Q.NoPt) (κ : Q.U ≅ Q.U) :
    ∃ ℓ₀ : ℝ≥0∞, ℓ₀ ≠ ⊤ ∧ ∀ (ŵ : (curveConfig Q.Lv.Z Q.hdim).Tree
        (universalCovering.root Q.hdim Q.z₀)) (i : irreducibleComponents Q.Lv.Z),
      ŵ.1.head? = some (.inl i) → ∃ D : Q.U ≅ Q.U, D.hom.ψ = 𝟙 _ ∧
        ∃ L, PWalk ŵ L ∧ cost (Q.D.weight ϖ) L ≤ ℓ₀ ∧
          covMap Q Q (D.inv ≫ κ.hom ≫ D.hom) (gen ŵ) = gen (pend ŵ L) := by
  classical
  haveI := Fintype.ofFinite (irreducibleComponents Q.Lv.Z)
  have hw : ∀ f : Q.U ⟶ Q.U, IsHarmonicWeight (curveConfig Q.Lv.Z Q.hdim)
      (curveConfig Q.Lv.Z Q.hdim) (sfm Q Q f) (Q.D.weight ϖ) (Q.D.weight ϖ) :=
    fun f => WData.isHarmonicWeight hX hN ϖ hϖ f Q.D Q.D Q.hdim Q.hdim
  -- for each label with a vertex, a chosen vertex and a walk to its image under `κ`
  have hloc : ∀ i : irreducibleComponents Q.Lv.Z, ∃ c : ℝ≥0∞, c ≠ ⊤ ∧
      ∀ t₀ : (curveConfig Q.Lv.Z Q.hdim).Tree (universalCovering.root Q.hdim Q.z₀),
        t₀.1.head? = some (.inl i) → ∃ t : (curveConfig Q.Lv.Z Q.hdim).Tree
          (universalCovering.root Q.hdim Q.z₀), t.1.head? = some (.inl i) ∧ ∃ L,
          PWalk t L ∧ cost (Q.D.weight ϖ) L ≤ c ∧
          covMap Q Q κ.hom (gen t) = gen (pend t L) := by
    intro i
    by_cases hex : ∃ t : (curveConfig Q.Lv.Z Q.hdim).Tree (universalCovering.root Q.hdim Q.z₀),
        t.1.head? = some (.inl i)
    · obtain ⟨t, ht⟩ := hex
      have hc := Q.iso_not_contr Q κ hns i
      obtain ⟨i', hi', -⟩ := map_gen_of_not_contr (covMap_fst Q Q κ.hom) (Q.hNC Q κ.hom) ht hc
      obtain ⟨L, hL, hLe⟩ := exists_pWalk_of_isComp ⟨i, ht⟩ ⟨i', hi'⟩
      refine ⟨cost (Q.D.weight ϖ) L, cost_ne_top (WData.weight_ne_top Q.D ϖ) L,
        fun _ _ => ⟨t, ht, L, hL, le_rfl, ?_⟩⟩
      rw [hLe]
      exact Q.covMap_gen Q κ.hom ht hc
    · exact ⟨0, ENNReal.zero_ne_top, fun t₀ h₀ => absurd ⟨t₀, h₀⟩ hex⟩
  choose c hc hcw using hloc
  refine ⟨Finset.univ.sup c, ((Finset.sup_lt_iff ENNReal.zero_lt_top).2
    fun i _ => (hc i).lt_top).ne, fun ŵ i hŵ => ?_⟩
  obtain ⟨t, ht, L, hL, hLc, hκ⟩ := hcw i ŵ hŵ
  obtain ⟨D, hDψ, hD⟩ := Q.exists_deck ht hŵ
  have hDc : ∀ j, ¬ Contr (K := curveConfig Q.Lv.Z Q.hdim) (sfm Q Q D.hom) j :=
    Q.iso_not_contr Q D hns
  -- the image of the walk under `D`
  have hpendc : IsComp (pend t L) := hL.isComp_pend ⟨i, ht⟩
  obtain ⟨j, hj⟩ := hpendc
  obtain ⟨j', hj', -⟩ := map_gen_of_not_contr (covMap_fst Q Q D.hom) (Q.hNC Q D.hom) hj (hDc j)
  obtain ⟨Y', L', hY', hL', hend, hcost⟩ := exists_walk_img (continuous_covMap Q Q D.hom)
    (covMap_fst Q Q D.hom) (Q.hNC Q D.hom) (curveConfig_injective_C Q.hdim) (hw D.hom)
    ⟨i, ht⟩ (by rw [lab_of ht]; exact hDc i) hL (img (covMap Q Q D.hom) (pend t L)) (.inl rfl)
  have hY'eq : Y' = img (covMap Q Q D.hom) (pend t L) := by
    rcases hY' with ⟨h, -⟩ | ⟨⟨s, hs⟩, -⟩
    · exact h
    · rw [img, hj'] at hs
      cases hs
  have himg : img (covMap Q Q D.hom) t = ŵ := by
    rw [img, hD, gen_snd_of_inl hŵ (curveConfig_η_notMem_S Q.hdim i)]
  rw [himg] at hL' hend
  refine ⟨D, hDψ, L', hL', hcost.trans (hLc.trans (Finset.le_sup (f := c)
    (Finset.mem_univ i))), ?_⟩
  have hinv : covMap Q Q D.inv (gen ŵ) = gen t := by
    rw [← hD, covMap_inv_hom]
  rw [covMap_comp, covMap_comp, hinv, hκ, Q.covMap_gen Q D.hom hj (hDc j), hend, hY'eq]

end Conj

end Pres

end

end TemperedFundamentalGroups
