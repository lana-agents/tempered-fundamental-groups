/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TheoremBHLoop
import TemperedFundamentalGroups.Andre.TateWinding

/-!
# The base loop from alternating crossings (Blueprint §10.3.8, hbase)

For a presentation `Q` of a member with a morphism `a : U ⟶ X₀` to the Tate object, the covering
part of `a` gives a map `Q.toSpace a` from the universal covering of the special fibre to the
`ℤ`-covering `D.Space` of the Tate 2-gon (`D = TateObject.decomp T`). A deck transformation of `U`
moving the generic point of a component vertex `t` to that of `t'` acts on the fibre of `X₀` by
the difference of the sheets of `t'` and `t` (`Pres.deck_char_of_sheet`). With alternating
crossings (`CurveConfig.exists_sheet_ne`) this gives an automorphism of `U` acting through a
non-trivial deck transformation of `X₀` (`Pres.exists_loop_of_crossings`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open scoped ENNReal

namespace TemperedFundamentalGroups

open CurveConfig

noncomputable section

open TempObj GaloisObject GaloisLimit TateObject

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) {x : R}
  (T : TateObject.Data O R)

namespace Pres

variable {Y : TempObj O R A} (Q : Pres x Y)

/-- The map from the universal covering of the special fibre of a member to the `ℤ`-covering of
the Tate 2-gon, induced by `a : U ⟶ X₀`. -/
def toSpace (a : Q.U ⟶ X₀ (A := A) T) (e : Q.E) : (decomp (A := A) T).Space :=
  letI := (decomp (A := A) T).codeTop
  (decomp (A := A) T).codeHomeomorph (a.h (Q.Θ' ⟨1, e⟩))

lemma continuous_toSpace (a : Q.U ⟶ X₀ (A := A) T) : Continuous (Q.toSpace T a) := by
  letI := (decomp (A := A) T).codeTop
  exact (decomp (A := A) T).codeHomeomorph.continuous.comp (a.continuous_h.comp
    (Q.Θ'.continuous.comp (continuous_sigmaMk (σ := fun _ : Q.Lv.L.H => Q.E))))

lemma toSpace_pt (a : Q.U ⟶ X₀ (A := A) T) (e : Q.E) :
    (Q.toSpace T a e).pt = specialFibreMap a.ψ a.ψ_toSpec e.1.1 := by
  apply Subtype.ext
  have h₁ := a.fst_h (Q.Θ' ⟨1, e⟩)
  erw [Θ_fst, indProj_one] at h₁
  exact h₁

/-- **A deck transformation of `U` acts on `X₀` by the difference of sheets.** -/
lemma deck_char_of_sheet (a : Q.U ⟶ X₀ (A := A) T) (D : Q.U ≅ Q.U) (hDψ : D.hom.ψ = 𝟙 _)
    {t t' : (curveConfig Q.Lv.Z Q.hdim).Tree (universalCovering.root Q.hdim Q.z₀)}
    (hD : covMap Q Q D.hom (gen t) = gen t')
    (hpt : (Q.toSpace T a (gen t')).pt = (Q.toSpace T a (gen t)).pt) (z) :
    (tempFibre O R A V hV).map (D.hom ≫ a) z = FibreAut.deckAct (X₀ T) (deck T)
      (Multiplicative.ofAdd ((Q.toSpace T a (gen t')).n - (Q.toSpace T a (gen t)).n))
      ((tempFibre O R A V hV).map a z) := by
  letI := (decomp (A := A) T).codeTop
  set k := Multiplicative.ofAdd ((Q.toSpace T a (gen t')).n - (Q.toSpace T a (gen t)).n)
  let hp := universalCovering.isUniversalCovering.{u, u, u} Q.hdim Q.z₀
  -- the covering maps agree after the deck transformation `k`
  have key : (fun e => (D.hom ≫ a).h (Q.Θ' ⟨1, e⟩)) =
      fun e => (decomp (A := A) T).deckCode _ (level_ρs T) k (a.h (Q.Θ' ⟨1, e⟩)) := by
    refine lift_ext hp (X₀ (A := A) T).P.isCoveringMap
      ((D.hom ≫ a).continuous_h.comp
        (Q.Θ'.continuous.comp (continuous_sigmaMk (σ := fun _ : Q.Lv.L.H => Q.E))))
      (((decomp (A := A) T).deckCode _ (level_ρs T) k).continuous.comp (a.continuous_h.comp
        (Q.Θ'.continuous.comp (continuous_sigmaMk (σ := fun _ : Q.Lv.L.H => Q.E)))))
      (funext fun e => ?_) (gen t) ?_
    · apply Subtype.ext
      change (((D.hom ≫ a).h (Q.Θ' ⟨1, e⟩)).1.1 : (X₀ (A := A) T).Lv.c.scheme) =
        ((a.h (Q.Θ' ⟨1, e⟩)).1.1 : (X₀ (A := A) T).Lv.c.scheme)
      rw [(D.hom ≫ a).fst_h, a.fst_h, comp_ψ, hDψ]
      rfl
    · apply (decomp (A := A) T).codeHomeomorph.injective
      have h₁ : (D.hom ≫ a).h (Q.Θ' ⟨1, gen t⟩) = a.h (Q.Θ' ⟨1, gen t'⟩) := by
        rw [comp_h, Function.comp_apply, ← Q.Θ'_ecov (D.hom.h _)]
        exact congrArg (fun e => a.h (Q.Θ' ⟨1, e⟩)) hD
      change (decomp (A := A) T).codeHomeomorph ((D.hom ≫ a).h (Q.Θ' ⟨1, gen t⟩)) =
        (decomp (A := A) T).codeHomeomorph ((decomp (A := A) T).codeHomeomorph.symm
          ((decomp (A := A) T).deck k ((decomp (A := A) T).codeHomeomorph
            (a.h (Q.Θ' ⟨1, gen t⟩)))))
      rw [Homeomorph.apply_symm_apply, h₁]
      change Q.toSpace T a (gen t') = (decomp (A := A) T).deck k (Q.toSpace T a (gen t))
      refine TateCovering.Decomp.Space.ext hpt ?_
      rw [TateCovering.Decomp.deck_n, toAdd_ofAdd]
      ring
  obtain ⟨q, rfl⟩ := Quotient.mk_surjective z
  change Quotient.mk _ (preMap V hV (D.hom ≫ a) q) =
    Quotient.mk _ (preMap V hV (deck T k).hom (preMap V hV a q))
  congr 1
  refine Subtype.ext (Prod.ext ((subsingleton_fibre (A := A)).elim _ _) ?_)
  change (D.hom ≫ a).h q.1.2 = (decomp (A := A) T).deckCode _ (level_ρs T) k (a.h q.1.2)
  rw [← Q.Θ'_ecov q.1.2]
  exact congrFun key _

/-- **The base loop from alternating crossings** (hbase). If the components of the special fibre
of `Q` over the line `C` of the Tate 2-gon all cross over `p` to components over the conic `E`,
and those over `E` all cross over `q` back to components over `C`, then some automorphism of `U`
acts on the fibre of `X₀` through a non-trivial deck transformation. -/
theorem exists_loop_of_crossings (a : Q.U ⟶ X₀ (A := A) T)
    (VC VE : irreducibleComponents Q.Lv.Z → Prop)
    (hVC : ∀ i, VC i → specialFibreMap a.ψ a.ψ_toSpec ((curveConfig Q.Lv.Z Q.hdim).η i) ∈
      (decomp (A := A) T).C)
    (hVE : ∀ i, VE i → specialFibreMap a.ψ a.ψ_toSpec ((curveConfig Q.Lv.Z Q.hdim).η i) ∉
      (decomp (A := A) T).C)
    (crossP : ∀ i, VC i → ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i L ∧
      (∀ p ∈ L, specialFibreMap a.ψ a.ψ_toSpec p.1 ∉ (decomp (A := A) T).Cq) ∧
      VE (lastLab i L))
    (crossQ : ∀ i, VE i → ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i L ∧
      (∀ p ∈ L, specialFibreMap a.ψ a.ψ_toSpec p.1 ∉ (decomp (A := A) T).Cp) ∧
      VC (lastLab i L))
    {t₀ : (curveConfig Q.Lv.Z Q.hdim).Tree (universalCovering.root Q.hdim Q.z₀)}
    {i₀ : irreducibleComponents Q.Lv.Z} (ht₀ : t₀.1.head? = some (.inl i₀)) (hi₀ : VC i₀) :
    ∃ (κ : Q.U ≅ Q.U) (d : Multiplicative ℤ), d ≠ 1 ∧ ∀ z,
      (tempFibre O R A V hV).map (κ.hom ≫ a) z =
        FibreAut.deckAct (X₀ T) (deck T) d ((tempFibre O R A V hV).map a z) := by
  obtain ⟨t, t', i, ht, ht', hne⟩ := exists_sheet_ne (h := Q.toSpace T a)
    (Q.continuous_toSpace T a) (Q.toSpace_pt T a) VC VE hVC hVE crossP crossQ ht₀ hi₀
  obtain ⟨D, hDψ, hD⟩ := Q.exists_deck ht ht'
  refine ⟨D, _, fun h => hne ?_, Q.deck_char_of_sheet V hV T a D hDψ hD (by
    rw [Q.toSpace_pt, Q.toSpace_pt, gen_fst_of_inl ht, gen_fst_of_inl ht'])⟩
  have := congrArg Multiplicative.toAdd h
  simp only [toAdd_ofAdd, toAdd_one] at this
  omega

/-- **`HarmonicTate`** (targeted, Blueprint §10.3.8) for a member `Q` over `X₀`, relative to a
family `ℰ` of subsets of the conic `E` (its components: `{E}` if `b₆` is a unit, the two lines if
`b₆ ∈ 𝔪`): (X1) of the model map `a.ψ : c → 𝒯` at the nodes of the Tate special fibre `C ∪ E`.
Every component mapped onto the line `C` has a walk crossing `p` (special points over `p`) to a
component mapped onto a member of `ℰ`; every component mapped onto a member of `ℰ` has a walk
avoiding `p` (crossing the nodes inside `E` and then `q`) to a component mapped onto `C`.
(A consequence of `CrossingX1` at the nodes of `𝒯`.) -/
def HarmonicTate (ℰ : Set (Set (X₀ (A := A) T).Lv.Z)) (a : Q.U ⟶ X₀ (A := A) T) : Prop :=
  (∀ i : irreducibleComponents Q.Lv.Z,
    specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i = (decomp (A := A) T).C →
    ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i L ∧
      (∀ p ∈ L, specialFibreMap a.ψ a.ψ_toSpec p.1 ∈ (decomp (A := A) T).Cp) ∧
      specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C (lastLab i L) ∈ ℰ) ∧
  (∀ i : irreducibleComponents Q.Lv.Z,
    specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i ∈ ℰ →
    ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i L ∧
      (∀ p ∈ L, specialFibreMap a.ψ a.ψ_toSpec p.1 ∉ (decomp (A := A) T).Cp) ∧
      specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C (lastLab i L) =
        (decomp (A := A) T).C)

/-- **hbase from `HarmonicTate`**: given a component over `C` (with a tree vertex), the members
of `ℰ` inside `E` and not points, and the generic points of the components mapped into `E` (not
contracted) off the line `C`, some automorphism of `U` acts on `X₀` through a non-trivial deck
transformation. -/
theorem exists_loop_of_harmonicTate (a : Q.U ⟶ X₀ (A := A) T)
    (ℰ : Set (Set (X₀ (A := A) T).Lv.Z))
    (hℰ : ∀ S ∈ ℰ, S ⊆ (decomp (A := A) T).E ∧ ¬ ∃ y, S = {y}) (hHT : Q.HarmonicTate T ℰ a)
    (hE : ∀ i : irreducibleComponents Q.Lv.Z,
      specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i ⊆ (decomp (A := A) T).E →
      ¬ Contr (K := curveConfig Q.Lv.Z Q.hdim) (specialFibreMap a.ψ a.ψ_toSpec) i →
      specialFibreMap a.ψ a.ψ_toSpec ((curveConfig Q.Lv.Z Q.hdim).η i) ∉ (decomp (A := A) T).C)
    {t₀ : (curveConfig Q.Lv.Z Q.hdim).Tree (universalCovering.root Q.hdim Q.z₀)}
    {i₀ : irreducibleComponents Q.Lv.Z} (ht₀ : t₀.1.head? = some (.inl i₀))
    (hi₀ : specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i₀ =
      (decomp (A := A) T).C) :
    ∃ (κ : Q.U ≅ Q.U) (d : Multiplicative ℤ), d ≠ 1 ∧ ∀ z,
      (tempFibre O R A V hV).map (κ.hom ≫ a) z =
        FibreAut.deckAct (X₀ T) (deck T) d ((tempFibre O R A V hV).map a z) := by
  refine Q.exists_loop_of_crossings V hV T a
    (fun i => specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i =
      (decomp (A := A) T).C)
    (fun i => specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i ∈ ℰ)
    (fun i hi => hi ▸ ⟨_, (curveConfig Q.Lv.Z Q.hdim).η_mem i, rfl⟩)
    (fun i hi => hE i (hℰ _ hi).1 (hℰ _ hi).2) (fun i hi => ?_) (fun i hi => ?_) ht₀ hi₀
  · obtain ⟨L, hL, hp, he⟩ := hHT.1 i hi
    exact ⟨L, hL, fun p hpL => fun hq =>
      Set.disjoint_left.1 (decomp (A := A) T).disjoint (hp p hpL) hq, he⟩
  · obtain ⟨L, hL, hq, hc⟩ := hHT.2 i hi
    exact ⟨L, hL, hq, hc⟩

end Pres

end

end TemperedFundamentalGroups
