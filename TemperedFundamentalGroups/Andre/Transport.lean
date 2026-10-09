/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TheoremBH
import TemperedFundamentalGroups.Topology.CurveGeneric
import TemperedFundamentalGroups.Andre.PointLift
import TemperedFundamentalGroups.Andre.GTransitive

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
    have hsub : i.1 ⊆ c.1 :=
      hgen ▸ (isClosed_of_mem_irreducibleComponents c.1 c.2).closure_subset_iff.2
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
theorem exists_conj (hX : SemistableReduction.Statement.HarmonicXS.{u})
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

section Lift

/-- **Rigidity**: two morphisms out of `U` with the same map of rings which agree at one point of
the universal covering are equal. -/
lemma hom_eq_of (f g : P.U ⟶ Q.U) (hf : f.φ.f = g.φ.f) (e : P.E)
    (he : covMap P Q f e = covMap P Q g e) : f = g := by
  haveI : Subsingleton Q.U.Lv.L.H := Q.sub
  haveI : IsSchemeTheoreticallyDominant P.U.Lv.j := P.dom
  have hφ : f.φ = g.φ :=
    FiniteLevel.Hom.ext hf (MonoidHom.ext fun _ => Subsingleton.elim _ _)
  have hψ : f.ψ = g.ψ := by
    refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated Q.U.Lv.c.toSpec
      (by rw [f.ψ_toSpec, g.ψ_toSpec]) P.U.Lv.j ?_
    rw [f.j_ψ, g.j_ψ, hφ]
  refine hom_ext hφ hψ (P.Θ' ⟨1, e⟩) ?_
  rw [← Q.Θ'_ecov (f.h _), ← Q.Θ'_ecov (g.h _)]
  exact congrArg (fun e => Q.Θ' ⟨1, e⟩) he

/-- Morphisms out of `U` with the same map of rings have the same model map. -/
lemma ψ_eq_of_φ (f g : P.U ⟶ Q.U) (hf : f.φ.f = g.φ.f) : f.ψ = g.ψ := by
  haveI : Subsingleton Q.U.Lv.L.H := Q.sub
  haveI : IsSchemeTheoreticallyDominant P.U.Lv.j := P.dom
  have hφ : f.φ = g.φ :=
    FiniteLevel.Hom.ext hf (MonoidHom.ext fun _ => Subsingleton.elim _ _)
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated Q.U.Lv.c.toSpec
    (by rw [f.ψ_toSpec, g.ψ_toSpec]) P.U.Lv.j ?_
  rw [f.j_ψ, g.j_ψ, hφ]

/-- **Endomorphisms of `U` over a model automorphism, through prescribed points.** -/
lemma exists_endo (σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B) (ψσ : P.Lv.c.scheme ⟶ P.Lv.c.scheme)
    (hψ : ψσ ≫ P.Lv.c.toSpec = P.Lv.c.toSpec)
    (hj : P.Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : P.Lv.L.B →+* P.Lv.L.B)) ≫ P.Lv.j)
    (e₁ e₂ : P.E) (h : e₂.1.1 = specialFibreMap ψσ hψ e₁.1.1) :
    ∃ f : P.U ⟶ P.U, f.φ.f = (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) ∧ f.ψ = ψσ ∧
      covMap P P f e₁ = e₂ := by
  haveI : IsSchemeTheoreticallyDominant P.Lv.j := P.dom
  let ℓ := P.Lv.autHom σ ψσ hψ hj
  let hp := universalCovering.isUniversalCovering.{u, u, u} P.hdim P.z₀
  obtain ⟨s, hs, hps, hse⟩ := hp.exists_lift P.Lv.Z P.U.P.carrier (fun x => x.1.1)
    P.U.P.isCoveringMap (ℓ.ψs ∘ universalCovering.proj P.hdim P.z₀)
    (ℓ.continuous_ψs.comp hp.isCoveringMap.continuous) e₁ (P.Θ' ⟨1, e₂⟩) (by
      change (P.Θ' ⟨1, e₂⟩).1.1 = specialFibreMap ψσ hψ e₁.1.1
      rw [← h]
      exact (Θ_fst _).trans (indProj_one _ _))
  have hps' : ∀ e, (s e).1.1 = ℓ.ψs (universalCovering.proj P.hdim P.z₀ e) := congrFun hps
  have key := liftHom_h_one (hp := hp) (hc := hp.countable_fibre) ℓ
    (LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant ℓ) hs hps' e₁
  exact ⟨liftHom hp hp.countable_fibre ℓ
    (LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant ℓ) hs hps', rfl, rfl,
    (congrArg P.ecov key).trans (by rw [hse, P.ecov_Θ'])⟩

/-- The model maps of `σ` and `σ⁻¹` are inverse (by dominance of `j`). -/
lemma model_inv (σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B) {ψ ψ' : P.Lv.c.scheme ⟶ P.Lv.c.scheme}
    (hψ' : ψ' ≫ P.Lv.c.toSpec = P.Lv.c.toSpec)
    (hψ : ψ ≫ P.Lv.c.toSpec = P.Lv.c.toSpec)
    (hj : P.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (σ : P.Lv.L.B →+* P.Lv.L.B)) ≫ P.Lv.j)
    (hj' : P.Lv.j ≫ ψ' =
      Spec.map (CommRingCat.ofHom (σ.symm : P.Lv.L.B →+* P.Lv.L.B)) ≫ P.Lv.j) :
    ψ ≫ ψ' = 𝟙 _ := by
  haveI := P.dom
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated P.Lv.c.toSpec
    (by rw [Category.assoc, hψ', hψ, Category.id_comp]) P.Lv.j ?_
  rw [← Category.assoc, hj, Category.assoc, hj', ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, Category.comp_id]
  have : (σ : P.Lv.L.B →+* P.Lv.L.B).comp (σ.symm : P.Lv.L.B →+* P.Lv.L.B) = RingHom.id _ :=
    RingHom.ext fun b => σ.apply_symm_apply b
  rw [this]
  erw [Spec.map_id, Category.id_comp]

lemma sfm_comp_eq (σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B) {ψ ψ' : P.Lv.c.scheme ⟶ P.Lv.c.scheme}
    (hψ' : ψ' ≫ P.Lv.c.toSpec = P.Lv.c.toSpec)
    (hψ : ψ ≫ P.Lv.c.toSpec = P.Lv.c.toSpec)
    (hj : P.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (σ : P.Lv.L.B →+* P.Lv.L.B)) ≫ P.Lv.j)
    (hj' : P.Lv.j ≫ ψ' =
      Spec.map (CommRingCat.ofHom (σ.symm : P.Lv.L.B →+* P.Lv.L.B)) ≫ P.Lv.j) (z : P.Lv.Z) :
    specialFibreMap ψ' hψ' (specialFibreMap ψ hψ z) = z := by
  apply Subtype.ext
  change (ψ ≫ ψ') z.1 = z.1
  rw [P.model_inv σ hψ' hψ hj hj']
  rfl

/-- **I4 for a morphism of members** (relative G-transitivity), as used by the transport: two
components of the source with the same (non-point) image are conjugate under an automorphism of
`B` fixing `B₀`. -/
def HasI4 (m : P.U ⟶ Q.U) : Prop :=
  ∀ a b : irreducibleComponents P.Lv.Z,
    ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (sfm P Q m) a →
    sfm P Q m '' (curveConfig P.Lv.Z P.hdim).C a = sfm P Q m '' (curveConfig P.Lv.Z P.hdim).C b →
    ∃ τ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B, (τ : P.Lv.L.B →ₐ[R] P.Lv.L.B).comp m.φ.f = m.φ.f ∧
      ∃ (ψτ : P.Lv.c.scheme ⟶ P.Lv.c.scheme) (hψτ : ψτ ≫ P.Lv.c.toSpec = P.Lv.c.toSpec),
        P.Lv.j ≫ ψτ = Spec.map (CommRingCat.ofHom (τ : P.Lv.L.B →+* P.Lv.L.B)) ≫ P.Lv.j ∧
        specialFibreMap ψτ hψτ '' (curveConfig P.Lv.Z P.hdim).C a =
          (curveConfig P.Lv.Z P.hdim).C b

/-- **Lifting an endomorphism of `Y₀` to an automorphism of `U` through prescribed vertices.**
Let `m : U ⟶ U₀` and `κ` an endomorphism of `U₀`. If `κ m` maps the generic point of a component
vertex `n` to the image of the generic point of `n''` (non-contracted), there is an automorphism
`π` of `U` with `π m = m κ` and `π (gen n) = gen n''`. -/
theorem exists_iso_over {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (t : P.Lv.L.B →ₐ[R] Ω)
    (hgal : ∀ t t' : P.Lv.L.B →ₐ[R] Ω, ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B,
      t.comp (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) = t')
    (m : P.U ⟶ Q.U) (κ : Q.U ⟶ Q.U) (hns : P.NoPt) (hI4 : P.HasI4 Q m)
    {n n'' : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀)}
    {i i'' : irreducibleComponents P.Lv.Z} (hn : n.1.head? = some (.inl i))
    (hn'' : n''.1.head? = some (.inl i''))
    (hc'' : ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (sfm P Q m) i'')
    (hκ : covMap Q Q κ (covMap P Q m (gen n)) = covMap P Q m (gen n'')) :
    ∃ π : P.U ≅ P.U, π.hom ≫ m = m ≫ κ ∧ covMap P P π.hom (gen n) = gen n'' := by
  haveI := P.dom
  haveI := Q.D.isDomain
  haveI := P.D.isDomain
  haveI := P.Lv.L.etale
  haveI := P.Lv.L.finite
  haveI := Q.Lv.L.etale
  haveI := Q.Lv.L.finite
  let φ : Q.Lv.L.B →ₐ[R] P.Lv.L.B := m.φ.f
  obtain ⟨σ₁, hσ₁⟩ := exists_aut_comp_eq P.idem hgal t φ κ.φ.f
  obtain ⟨ψ₁, hψ₁, hj₁⟩ := P.act σ₁
  obtain ⟨ψ₁', hψ₁', hj₁'⟩ := P.act σ₁.symm
  -- `ψ₁` contracts nothing
  have hinj₁ : Function.Injective (specialFibreMap ψ₁ hψ₁) := fun a b h => by
    rw [← P.sfm_comp_eq σ₁ hψ₁' hψ₁ hj₁ hj₁' a, ← P.sfm_comp_eq σ₁ hψ₁' hψ₁ hj₁ hj₁' b, h]
  have hnc₁ := curveConfig_not_contr_of_injective P.hdim hinj₁ hns i
  obtain ⟨a, ha, -⟩ := curveConfig_contr_or P.hdim P.hdim (continuous_specialFibreMap _ _)
    (isClosedMap_specialFibreMap' ψ₁ hψ₁) i hnc₁
  have hηa := curveConfig_map_η P.hdim P.hdim (continuous_specialFibreMap ψ₁ hψ₁) ha
  -- `ψ₁ m = m κ` on special fibres
  have hcomp : ∀ z : P.Lv.Z, sfm P Q m (specialFibreMap ψ₁ hψ₁ z) = sfm Q Q κ (sfm P Q m z) := by
    let hp := universalCovering.isUniversalCovering.{u, u, u} P.hdim P.z₀
    haveI := hp.connectedSpace
    obtain ⟨e₂, he₂⟩ := hp.isCoveringMap.surjective_of_connectedSpace
      (specialFibreMap ψ₁ hψ₁ (gen n).1.1)
    obtain ⟨f₁, hf₁φ, hf₁ψ, -⟩ := P.exists_endo σ₁ ψ₁ hψ₁ hj₁ (gen n) e₂ he₂
    have hψeq := P.ψ_eq_of_φ Q (f₁ ≫ m) (m ≫ κ) (by
      change f₁.φ.f.comp m.φ.f = m.φ.f.comp κ.φ.f
      rw [hf₁φ]
      exact hσ₁)
    intro z
    apply Subtype.ext
    have := congrArg (fun F => F z.1) hψeq
    simp only [comp_ψ, Scheme.Hom.comp_apply, hf₁ψ] at this
    exact this
  -- `C a` and `C i''` have the same image
  have hgenη : ∀ (e : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀))
      (j : irreducibleComponents P.Lv.Z), e.1.head? = some (.inl j) →
      (gen e).1.1 = (curveConfig P.Lv.Z P.hdim).η j := fun e j he => gen_fst_of_inl he
  have hpt : sfm P Q m ((curveConfig P.Lv.Z P.hdim).η a) =
      sfm P Q m ((curveConfig P.Lv.Z P.hdim).η i'') := by
    have h₁ := congrArg (fun e => e.1.1) hκ
    simp only [covMap_fst] at h₁
    rw [hgenη n i hn, hgenη n'' i'' hn''] at h₁
    rw [← hηa, hcomp]
    exact h₁
  have himg : sfm P Q m '' (curveConfig P.Lv.Z P.hdim).C a =
      sfm P Q m '' (curveConfig P.Lv.Z P.hdim).C i'' := by
    have e₁ := curveConfig_image_eq_closure (Z := P.Lv.Z) P.hdim (ψ := sfm P Q m)
      (continuous_specialFibreMap _ _) (isClosedMap_specialFibreMap m) a
    have e₂ := curveConfig_image_eq_closure (Z := P.Lv.Z) P.hdim (ψ := sfm P Q m)
      (continuous_specialFibreMap _ _) (isClosedMap_specialFibreMap m) i''
    rw [e₁, e₂, hpt]
  have hca : ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (sfm P Q m) a := fun ⟨y, hy⟩ =>
    hc'' ⟨y, himg ▸ hy⟩
  obtain ⟨τ, hτ, ψτ, hψτ, hjτ, hτC⟩ := hI4 a i'' hca himg
  have hητ := curveConfig_map_η P.hdim P.hdim (continuous_specialFibreMap ψτ hψτ) hτC
  -- the automorphism `σ = σ₁ ∘ τ` with model map `ψ₁ ≫ ψτ`
  let σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B := τ.trans σ₁
  have hψσ : (ψ₁ ≫ ψτ) ≫ P.Lv.c.toSpec = P.Lv.c.toSpec := by
    rw [Category.assoc, hψτ, hψ₁]
  have hjσ : P.Lv.j ≫ ψ₁ ≫ ψτ =
      Spec.map (CommRingCat.ofHom (σ : P.Lv.L.B →+* P.Lv.L.B)) ≫ P.Lv.j := by
    rw [← Category.assoc, hj₁, Category.assoc, hjτ, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  have hσφ : (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B).comp φ = φ.comp κ.φ.f := by
    refine AlgHom.ext fun b => ?_
    have h1 := congrArg (fun F => F b) hτ
    have h2 := congrArg (fun F => F b) hσ₁
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at h1 h2
    exact (congrArg σ₁ h1).trans h2
  obtain ⟨ψi, hψi, hji⟩ := P.act σ.symm
  have hηi'' : specialFibreMap (ψ₁ ≫ ψτ) hψσ ((curveConfig P.Lv.Z P.hdim).η i) =
      (curveConfig P.Lv.Z P.hdim).η i'' := by
    rw [← hητ, ← hηa]
    rfl
  obtain ⟨f, hff, -, hfe⟩ := P.exists_endo σ (ψ₁ ≫ ψτ) hψσ hjσ (gen n) (gen n'')
    (by rw [hgenη n i hn, hgenη n'' i'' hn'', hηi''])
  obtain ⟨g, hgf, -, hge⟩ := P.exists_endo σ.symm ψi hψi hji (gen n'') (gen n)
    (by rw [hgenη n i hn, hgenη n'' i'' hn'', ← hηi'',
      P.sfm_comp_eq σ hψi hψσ hjσ hji])
  have hfg : f ≫ g = 𝟙 _ := P.hom_eq_of P _ _ (by
      change f.φ.f.comp g.φ.f = AlgHom.id R _
      rw [hff, hgf]
      ext b
      exact σ.apply_symm_apply b) (gen n)
    (by rw [covMap_comp, hfe, hge, covMap_id])
  have hgf' : g ≫ f = 𝟙 _ := P.hom_eq_of P _ _ (by
      change g.φ.f.comp f.φ.f = AlgHom.id R _
      rw [hff, hgf]
      ext b
      exact σ.symm_apply_apply b) (gen n'')
    (by rw [covMap_comp, hge, hfe, covMap_id])
  refine ⟨⟨f, g, hfg, hgf'⟩, P.hom_eq_of Q _ _ ?_ (gen n) ?_, hfe⟩
  · change f.φ.f.comp m.φ.f = m.φ.f.comp κ.φ.f
    rw [hff]
    exact hσφ
  · change covMap P Q (f ≫ m) (gen n) = covMap P Q (m ≫ κ) (gen n)
    rw [covMap_comp, covMap_comp, hfe, hκ]

end Lift

section Loop

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- Walk lifting along morphisms of members ((X1) of `HarmonicX`). -/
lemma isWalkLifting (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (f : P.U ⟶ Q.U) :
    IsWalkLifting (sfm P Q f) (covMap P Q f) (P.D.weight ϖ) (Q.D.weight ϖ) :=
  isWalkLifting_of_isEdgeLifting (continuous_covMap P Q f) (covMap_fst P Q f) (P.hNC Q f)
    (curveConfig_injective_C Q.hdim) (WData.isHarmonicWeight hX hN ϖ hϖ f P.D Q.D P.hdim Q.hdim)
    (WData.isEdgeLifting hX hN ϖ hϖ f P.D Q.D P.hdim Q.hdim)

/-- **Heights do not increase under automorphisms preserving `ν`.** -/
lemma dN_img_le (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (π : P.U ≅ P.U) (hns : P.NoPt) (ν : irreducibleComponents P.Lv.Z → Prop)
    (hν : ∀ i i', sfm P P π.hom '' (curveConfig P.Lv.Z P.hdim).C i =
      (curveConfig P.Lv.Z P.hdim).C i' → ν i → ν i')
    {t : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀)}
    (ht : IsComp t) :
    dN (P.D.weight ϖ) ν (img (covMap P P π.hom) t) ≤ dN (P.D.weight ϖ) ν t := by
  refine le_sInf ?_
  rintro _ ⟨L, hL, ⟨j, hj⟩, hνL, rfl⟩
  have hc := P.iso_not_contr P π hns
  obtain ⟨j', hj', hjj'⟩ := map_gen_of_not_contr (covMap_fst P P π.hom) (P.hNC P π.hom) hj (hc j)
  obtain ⟨k, hk⟩ := ht
  obtain ⟨Y', L', hY', hL', hend, hcost⟩ := exists_walk_img (continuous_covMap P P π.hom)
    (covMap_fst P P π.hom) (P.hNC P π.hom) (curveConfig_injective_C P.hdim)
    (WData.isHarmonicWeight hX hN ϖ hϖ π.hom P.D P.D P.hdim P.hdim) ⟨k, hk⟩
    (by rw [lab_of hk]; exact hc k) hL (img (covMap P P π.hom) (pend t L)) (.inl rfl)
  have hY : Y' = img (covMap P P π.hom) (pend t L) := by
    rcases hY' with ⟨h, -⟩ | ⟨⟨s, hs⟩, -⟩
    · exact h
    · rw [img, hj'] at hs
      cases hs
  rw [hY] at hend
  refine (dN_le _ ν hL' (hend ▸ ⟨j', hj'⟩) ?_).trans hcost
  rw [hend, img, lab_of hj']
  rw [lab_of hj] at hνL
  exact hν j j' hjj' hνL

/-- **The loop element in a member over `Y₀`** (`U`-level form of `hne`). For `mm : U ⟶ U₀`, an
automorphism `κ` of `U₀` with the conjugation bound `ℓ₀` (`exists_conj`), and a set `ν` of
components (not contracted by `mm`, preserved by automorphisms, nonempty), every fibre element
`u` of `U` has an automorphism `π` lifting a deck conjugate of `κ` with `HC(u, π u) ≤ ℓ₀`. -/
theorem exists_hc_loop (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
    (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
    (hgal : ∀ t t' : P.Lv.L.B →ₐ[R] Ω, ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B,
      t.comp (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) = t')
    (mm : P.U ⟶ Q.U) (κ : Q.U ≅ Q.U) (hnsP : P.NoPt) (hI4 : P.HasI4 Q mm)
    (ν : irreducibleComponents P.Lv.Z → Prop)
    (hνnc : ∀ i, ν i → ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (sfm P Q mm) i)
    (hνπ : ∀ (π : P.U ≅ P.U) i i', sfm P P π.hom '' (curveConfig P.Lv.Z P.hdim).C i =
      (curveConfig P.Lv.Z P.hdim).C i' → ν i → ν i')
    {t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀)}
    (ht₁ : IsComp t₁) (hν₁ : ν (lab t₁)) {ℓ₀ : ℝ≥0∞}
    (hconj : ∀ (ŵ : (curveConfig Q.Lv.Z Q.hdim).Tree
        (universalCovering.root Q.hdim Q.z₀)) (i : irreducibleComponents Q.Lv.Z),
      ŵ.1.head? = some (.inl i) → ∃ D : Q.U ≅ Q.U, D.hom.ψ = 𝟙 _ ∧
        ∃ L, PWalk ŵ L ∧ cost (Q.D.weight ϖ) L ≤ ℓ₀ ∧
          covMap Q Q (D.inv ≫ κ.hom ≫ D.hom) (gen ŵ) = gen (pend ŵ L))
    (u : (tempFibre O R A V hV).obj P.U) :
    ∃ (π : P.U ≅ P.U) (D : Q.U ≅ Q.U), D.hom.ψ = 𝟙 _ ∧
      π.hom ≫ mm = mm ≫ (D.inv ≫ κ.hom ≫ D.hom) ∧
      HC (P.D.weight ϖ) ν (P.vtx V hV u)
        (P.vtx V hV ((tempFibre O R A V hV).map π.hom u)) ℓ₀ := by
  set e := P.ecov (Quotient.out u : PreFibre Ω V hV P.U).1.2 with he
  obtain ⟨b, hb⟩ := exists_near e.1.2
  have hbc := hb.isComp
  obtain ⟨μ, hμ0, hμ'⟩ := WData.exists_weight_pos hX hN ϖ hϖ (X := P.U) P.D P.hdim
  have hμ : ∀ s ∈ (curveConfig P.Lv.Z P.hdim).S, μ ≤ P.D.weight ϖ s := hμ'
  obtain ⟨W₁, hW₁, hnc, hνn, hcW₁⟩ := exists_dN_eq (K := curveConfig P.Lv.Z P.hdim)
    (r := universalCovering.root P.hdim P.z₀) (WData.weight_ne_top P.D ϖ) hμ0 hμ ν hbc
    (by
      obtain ⟨L, hL, hLe⟩ := exists_pWalk_of_isComp hbc ht₁
      exact ⟨L, hL, hLe ▸ ht₁, hLe ▸ hν₁⟩)
  generalize hndef : pend b W₁ = n at hnc hνn
  obtain ⟨i, hi⟩ := hnc
  have hncm : ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (sfm P Q mm) i :=
    hνnc i (lab_of hi ▸ hνn)
  obtain ⟨i₀, hŵ, -⟩ := map_gen_of_not_contr (covMap_fst P Q mm) (P.hNC Q mm) hi hncm
  obtain ⟨D, hDψ, L₀, hL₀, hL₀c, hκD⟩ := hconj _ i₀ hŵ
  obtain ⟨L, hL, hLc, ⟨i'', hi''⟩, hn''nc, hn''img⟩ :=
    P.isWalkLifting Q hX hN ϖ hϖ mm n ⟨i, hi⟩ (by rw [lab_of hi]; exact hncm) L₀ hL₀
  rw [lab_of hi''] at hn''nc
  generalize hn''def : pend n L = n'' at hi'' hn''nc hn''img
  have hκ : covMap Q Q (D.inv ≫ κ.hom ≫ D.hom) (covMap P Q mm (gen n)) =
      covMap P Q mm (gen n'') := by
    rw [P.covMap_gen Q mm hi hncm]
    simp only [img] at hn''img ⊢
    rw [hκD, P.covMap_gen Q mm hi'' hn''nc, img, hn''img]
  obtain ⟨π, hπm, hπn⟩ := P.exists_iso_over Q (Quotient.out u : PreFibre Ω V hV P.U).1.1 hgal
    mm (D.inv ≫ κ.hom ≫ D.hom) hnsP hI4 hi hi'' hn''nc hκ
  refine ⟨π, D, hDψ, hπm, ?_⟩
  -- the vertex of `π u` is near `b' = π b`
  have hcπ := P.iso_not_contr P π hnsP
  obtain ⟨ib, hib⟩ := hbc
  obtain ⟨ib', hib', -⟩ := map_gen_of_not_contr (covMap_fst P P π.hom) (P.hNC P π.hom) hib
    (hcπ ib)
  set b' := img (covMap P P π.hom) b
  have hvtx : P.vtx V hV ((tempFibre O R A V hV).map π.hom u) = (covMap P P π.hom e).1.2 :=
    vtx_map V hV P P π.hom u
  have hnear' : Near (P.vtx V hV ((tempFibre O R A V hV).map π.hom u)) b' := by
    rw [hvtx]
    exact (below_map_gen (continuous_covMap P P π.hom) hb).near ⟨ib', hib'⟩
  -- the image of `W₁` under `π`: a walk from `b'` to `n''`
  have himgn : img (covMap P P π.hom) n = n'' := by
    rw [img, hπn, gen_snd_of_inl hi'' (curveConfig_η_notMem_S P.hdim i'')]
  obtain ⟨Y', L₂, hY', hL₂, hend₂, hcost₂⟩ := exists_walk_img (continuous_covMap P P π.hom)
    (covMap_fst P P π.hom) (P.hNC P π.hom) (curveConfig_injective_C P.hdim)
    (WData.isHarmonicWeight hX hN ϖ hϖ π.hom P.D P.D P.hdim P.hdim) ⟨ib, hib⟩
    (by rw [lab_of hib]; exact hcπ ib) hW₁ n'' (by rw [hndef, himgn]; exact .inl rfl)
  have hY' : Y' = n'' := by
    rcases hY' with ⟨h, -⟩ | ⟨⟨s, hs⟩, -⟩
    · exact h
    · rw [hi''] at hs
      cases hs
  rw [hY'] at hend₂
  obtain ⟨hrev, hrevend⟩ := PWalk.prev hL₂
  rw [hend₂] at hrev hrevend
  -- `dN b ≤ dN b'`
  have hbb : img (covMap P P π.inv) b' = b := by
    rw [img, ← P.covMap_gen P π.hom hib (hcπ ib), covMap_inv_hom,
      gen_snd_of_inl hib (curveConfig_η_notMem_S P.hdim ib)]
  have hdN : dN (P.D.weight ϖ) ν b ≤ dN (P.D.weight ϖ) ν b' := by
    have := P.dN_img_le hX hN ϖ hϖ π.symm hnsP ν (hνπ π.symm) (t := b') ⟨ib', hib'⟩
    rwa [Iso.symm_hom, hbb] at this
  refine ⟨b, b', W₁ ++ L ++ prev b' L₂, hb, hnear', ?_, ?_, ?_⟩
  · rw [pWalk_append, pWalk_append, pend_append, hndef, hn''def]
    exact ⟨⟨hW₁, hndef ▸ hL⟩, hrev⟩
  · rw [pend_append, pend_append, hndef, hn''def]
    exact hrevend
  · rw [cost_append, cost_append, cost_prev, hcW₁]
    calc dN (P.D.weight ϖ) ν b + cost (P.D.weight ϖ) L + cost (P.D.weight ϖ) L₂
        ≤ dN (P.D.weight ϖ) ν b + ℓ₀ + dN (P.D.weight ϖ) ν b' := by
          gcongr
          · exact hLc.trans hL₀c
          · exact hcost₂.trans (hcW₁.le.trans hdN)
      _ = ℓ₀ + dN (P.D.weight ϖ) ν b + dN (P.D.weight ϖ) ν b' := by
          rw [add_comm (dN _ ν b) ℓ₀]

end Loop

end Pres

end

end TemperedFundamentalGroups
