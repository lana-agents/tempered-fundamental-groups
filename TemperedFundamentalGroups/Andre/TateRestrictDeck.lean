/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictLoop
import TemperedFundamentalGroups.Andre.TateRestrictUnique

/-!
# The base loop for the restricted Tate object (Blueprint §10.3.8, `v(q) = 1`, B3g)

As `TateLoop`, for `X₀'`: a deck transformation of `U` moving the generic point of a component
vertex to another one acts on the fibre of `X₀'` by the difference of sheets
(`Pres.deck_char_of_sheetR`). The level maps of `D ≫ a` and `a` agree since their model maps do
(`TateRestrict.φf_eq_of_ψ_eq`). Hence `HarmonicTateR` gives an automorphism of `U` acting through
a non-trivial deck transformation (`Pres.exists_loop_of_harmonicTateR`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace

namespace TemperedFundamentalGroups

open CurveConfig

noncomputable section

open TempObj GaloisObject GaloisLimit TateRestrict RamifiedQuadratic SemistableReduction.W10Apply

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (hϖ : Irreducible ϖ)
  [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero K]
  (b₄ b₆ : O)
  [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)))]
  (R : Type u) [CommRing R] [Algebra K R] {x y : R}
  (heqR : y ^ 2 + x * y = x ^ 3 + algebraMap K R (ϖ * b₄) * x + algebraMap K R (ϖ * b₆))
  (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A] {xW : R}
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

set_option quotPrecheck false in
local notation "𝔛" => X₀' hϖ b₄ b₆ R heqR A
set_option quotPrecheck false in
local notation "𝔇" => decompR hϖ b₄ b₆
set_option quotPrecheck false in
local notation "𝔓" => preserves_ρs hϖ b₄ b₆ R heqR A

namespace Pres

variable {Y : TempObj O R A} (Q : Pres xW Y)

/-- The map from the universal covering of the special fibre of a member to the `ℤ`-covering of
the Tate 2-gon, induced by `a : U ⟶ X₀`. -/
def toSpaceR (a : Q.U ⟶ 𝔛) (e : Q.E) : (𝔇).Space :=
  letI := (𝔇).codeTop
  (𝔇).codeHomeomorph (a.h (Q.Θ' ⟨1, e⟩))

set_option quotPrecheck false in
local notation "𝔰" => Pres.toSpaceR hϖ b₄ b₆ R heqR A

lemma continuous_toSpaceR (a : Q.U ⟶ 𝔛) : Continuous (𝔰 Q a) := by
  letI := (𝔇).codeTop
  exact (𝔇).codeHomeomorph.continuous.comp (a.continuous_h.comp
    (Q.Θ'.continuous.comp (continuous_sigmaMk (σ := fun _ : Q.Lv.L.H => Q.E))))

lemma toSpaceR_pt (a : Q.U ⟶ 𝔛) (e : Q.E) :
    (𝔰 Q a e).pt = specialFibreMap a.ψ a.ψ_toSpec e.1.1 := by
  apply Subtype.ext
  have h₁ := a.fst_h (Q.Θ' ⟨1, e⟩)
  erw [Θ_fst, indProj_one] at h₁
  exact h₁

/-- **A deck transformation of `U` acts on `X₀` by the difference of sheets.** -/
lemma deck_char_of_sheetR (a : Q.U ⟶ 𝔛) (D : Q.U ≅ Q.U) (hDψ : D.hom.ψ = 𝟙 _)
    {t t' : (curveConfig Q.Lv.Z Q.hdim).Tree (universalCovering.root Q.hdim Q.z₀)}
    (hD : covMap Q Q D.hom (gen t) = gen t')
    (hpt : (𝔰 Q a (gen t')).pt = (𝔰 Q a (gen t)).pt) (z) :
    (tempFibre O R A V hV).map (D.hom ≫ a) z = FibreAut.deckAct (𝔛) (deck' hϖ b₄ b₆ R heqR A)
      (Multiplicative.ofAdd ((𝔰 Q a (gen t')).n - (𝔰 Q a (gen t)).n))
      ((tempFibre O R A V hV).map a z) := by
  letI := (𝔇).codeTop
  set k := Multiplicative.ofAdd ((𝔰 Q a (gen t')).n -
    (𝔰 Q a (gen t)).n)
  let hp := universalCovering.isUniversalCovering.{u, u, u} Q.hdim Q.z₀
  -- the covering maps agree after the deck transformation `k`
  have key : (fun e => (D.hom ≫ a).h (Q.Θ' ⟨1, e⟩)) =
      fun e => (𝔇).deckCodeEq _ (𝔓) k (a.h (Q.Θ' ⟨1, e⟩)) := by
    refine lift_ext hp (𝔛).P.isCoveringMap
      ((D.hom ≫ a).continuous_h.comp
        (Q.Θ'.continuous.comp (continuous_sigmaMk (σ := fun _ : Q.Lv.L.H => Q.E))))
      (((𝔇).deckCodeEq _ (𝔓) k).continuous.comp (a.continuous_h.comp
        (Q.Θ'.continuous.comp (continuous_sigmaMk (σ := fun _ : Q.Lv.L.H => Q.E)))))
      (funext fun e => ?_) (gen t) ?_
    · apply Subtype.ext
      change (((D.hom ≫ a).h (Q.Θ' ⟨1, e⟩)).1.1 : (𝔛).Lv.c.scheme) =
        ((a.h (Q.Θ' ⟨1, e⟩)).1.1 : (𝔛).Lv.c.scheme)
      rw [(D.hom ≫ a).fst_h, a.fst_h, comp_ψ, hDψ]
      rfl
    · apply (𝔇).codeHomeomorph.injective
      have h₁ : (D.hom ≫ a).h (Q.Θ' ⟨1, gen t⟩) = a.h (Q.Θ' ⟨1, gen t'⟩) := by
        rw [comp_h, Function.comp_apply, ← Q.Θ'_ecov (D.hom.h _)]
        exact congrArg (fun e => a.h (Q.Θ' ⟨1, e⟩)) hD
      change (𝔇).codeHomeomorph ((D.hom ≫ a).h (Q.Θ' ⟨1, gen t⟩)) =
        (𝔇).codeHomeomorph ((𝔇).codeHomeomorph.symm
          ((𝔇).deck k ((𝔇).codeHomeomorph
            (a.h (Q.Θ' ⟨1, gen t⟩)))))
      rw [Homeomorph.apply_symm_apply, h₁]
      change 𝔰 Q a (gen t') = (𝔇).deck k (𝔰 Q a (gen t))
      refine TateCovering.Decomp.Space.ext hpt ?_
      rw [TateCovering.Decomp.deck_n, toAdd_ofAdd]
      ring
  obtain ⟨q, rfl⟩ := Quotient.mk_surjective z
  change Quotient.mk _ (preMap V hV (D.hom ≫ a) q) =
    Quotient.mk _ (preMap V hV (deck' hϖ b₄ b₆ R heqR A k).hom (preMap V hV a q))
  congr 1
  have hφ : (D.hom ≫ a).φ.f = a.φ.f := by
    haveI : IsSchemeTheoreticallyDominant Q.U.Lv.j := Q.dom
    refine φf_eq_of_ψ_eq hϖ b₄ b₆ R heqR A Q.idem a (D.hom ≫ a) ?_
    rw [comp_ψ, hDψ, Category.id_comp]
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change q.1.1.comp (D.hom ≫ a).φ.f = (q.1.1.comp a.φ.f).comp (AlgHom.id _ _)
    rw [hφ]
    rfl
  change (D.hom ≫ a).h q.1.2 = (𝔇).deckCodeEq _ (𝔓) k (a.h q.1.2)
  rw [← Q.Θ'_ecov q.1.2]
  exact congrFun key _

/-- **The base loop from alternating crossings** (hbase). If the components of the special fibre
of `Q` over the line `C` of the Tate 2-gon all cross over `p` to components over the conic `E`,
and those over `E` all cross over `q` back to components over `C`, then some automorphism of `U`
acts on the fibre of `X₀` through a non-trivial deck transformation. -/
theorem exists_loop_of_crossingsR (a : Q.U ⟶ 𝔛)
    (VC VE : irreducibleComponents Q.Lv.Z → Prop)
    (hVC : ∀ i, VC i → specialFibreMap a.ψ a.ψ_toSpec ((curveConfig Q.Lv.Z Q.hdim).η i) ∈
      (𝔇).C)
    (hVE : ∀ i, VE i → specialFibreMap a.ψ a.ψ_toSpec ((curveConfig Q.Lv.Z Q.hdim).η i) ∉
      (𝔇).C)
    (crossP : ∀ i, VC i → ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i L ∧
      (∀ p ∈ L, specialFibreMap a.ψ a.ψ_toSpec p.1 ∉ (𝔇).Cq) ∧
      VE (lastLab i L))
    (crossQ : ∀ i, VE i → ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i L ∧
      (∀ p ∈ L, specialFibreMap a.ψ a.ψ_toSpec p.1 ∉ (𝔇).Cp) ∧
      VC (lastLab i L))
    {t₀ : (curveConfig Q.Lv.Z Q.hdim).Tree (universalCovering.root Q.hdim Q.z₀)}
    {i₀ : irreducibleComponents Q.Lv.Z} (ht₀ : t₀.1.head? = some (.inl i₀)) (hi₀ : VC i₀) :
    ∃ (κ : Q.U ≅ Q.U) (d : Multiplicative ℤ), d ≠ 1 ∧ ∀ z,
      (tempFibre O R A V hV).map (κ.hom ≫ a) z =
        FibreAut.deckAct (𝔛) (deck' hϖ b₄ b₆ R heqR A) d ((tempFibre O R A V hV).map a z) := by
  obtain ⟨t, t', i, ht, ht', hne⟩ := exists_sheet_ne (h := 𝔰 Q a)
    (Q.continuous_toSpaceR hϖ b₄ b₆ R heqR A a) (Q.toSpaceR_pt hϖ b₄ b₆ R heqR A a) VC VE hVC hVE
    crossP crossQ ht₀ hi₀
  obtain ⟨D, hDψ, hD⟩ := Q.exists_deck ht ht'
  refine ⟨D, _, fun h => hne ?_, Q.deck_char_of_sheetR hϖ b₄ b₆ R heqR A V hV a D hDψ hD (by
    rw [Q.toSpaceR_pt hϖ b₄ b₆ R heqR A, Q.toSpaceR_pt hϖ b₄ b₆ R heqR A, gen_fst_of_inl ht,
      gen_fst_of_inl ht'])⟩
  have := congrArg Multiplicative.toAdd h
  simp only [toAdd_ofAdd, toAdd_one] at this
  omega

/-- **hbase from `HarmonicTate`**: given a component over `C` (with a tree vertex), the members
of `ℰ` inside `E` and not points, and the generic points of the components mapped into `E` (not
contracted) off the line `C`, some automorphism of `U` acts on `X₀` through a non-trivial deck
transformation. -/
theorem exists_loop_of_harmonicTateR (a : Q.U ⟶ 𝔛)
    (ℰ : Set (Set (specialFibre (modelR hϖ b₄ b₆).toSpec)))
    (hℰ : ∀ S ∈ ℰ, S ⊆ (𝔇).E ∧ ¬ ∃ y, S = {y}) (hHT : Q.HarmonicTateR hϖ b₄ b₆ R heqR A ℰ a)
    (hE : ∀ i : irreducibleComponents Q.Lv.Z,
      specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i ⊆ (𝔇).E →
      ¬ Contr (K := curveConfig Q.Lv.Z Q.hdim) (specialFibreMap a.ψ a.ψ_toSpec) i →
      specialFibreMap a.ψ a.ψ_toSpec ((curveConfig Q.Lv.Z Q.hdim).η i) ∉ (𝔇).C)
    {t₀ : (curveConfig Q.Lv.Z Q.hdim).Tree (universalCovering.root Q.hdim Q.z₀)}
    {i₀ : irreducibleComponents Q.Lv.Z} (ht₀ : t₀.1.head? = some (.inl i₀))
    (hi₀ : specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i₀ =
      (𝔇).C) :
    ∃ (κ : Q.U ≅ Q.U) (d : Multiplicative ℤ), d ≠ 1 ∧ ∀ z,
      (tempFibre O R A V hV).map (κ.hom ≫ a) z =
        FibreAut.deckAct (𝔛) (deck' hϖ b₄ b₆ R heqR A) d ((tempFibre O R A V hV).map a z) := by
  refine Q.exists_loop_of_crossingsR hϖ b₄ b₆ R heqR A V hV a
    (fun i => specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i =
      (𝔇).C)
    (fun i => specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i ∈ ℰ)
    (fun i hi => hi ▸ ⟨_, (curveConfig Q.Lv.Z Q.hdim).η_mem i, rfl⟩)
    (fun i hi => hE i (hℰ _ hi).1 (hℰ _ hi).2) (fun i hi => ?_) (fun i hi => ?_) ht₀ hi₀
  · obtain ⟨L, hL, hp, he⟩ := hHT.1 i hi
    exact ⟨L, hL, fun p hpL => fun hq =>
      Set.disjoint_left.1 (𝔇).disjoint (hp p hpL) hq, he⟩
  · obtain ⟨L, hL, hq, hc⟩ := hHT.2 i hi
    exact ⟨L, hL, hq, hc⟩

end Pres

end

end TemperedFundamentalGroups
