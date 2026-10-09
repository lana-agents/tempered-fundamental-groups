/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateLoop
import TemperedFundamentalGroups.Andre.TateG1

/-!
# Theorem B: assembly (Blueprint §10.3.8)

`TateObject.exists_character_ne_one`: from W10 with components (`StrongComponentA`, mixed
characteristic), `HarmonicX`, `NodeOfTwoComponents`, `HarmonicTate` (targeted) and the Tate
dominance inputs G1 (some component over the line `C`, components over the conic have their
generic point off `C`, and some component not contracted over the Tate model), some element of
`temperedPi1` has non-trivial character. The base member `Y₀` is any member of `galClassW` over
`(X₀, x₀)` (domination); its loop comes from `HarmonicTate` (`Pres.exists_loop_of_harmonicTate`),
and it is transported to all members over `Y₀` (`TateObject.exists_character_eq_of_loop`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open scoped ENNReal

namespace TemperedFundamentalGroups

open CurveConfig

noncomputable section

open TempObj GaloisObject GaloisLimit

namespace TateObject

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A] (T : Data O R)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Algebra.Smooth K R] [IsDomain R] [Subsingleton A] in
/-- A component vertex of the tree over every component. -/
lemma _root_.TemperedFundamentalGroups.Pres.exists_tree_head {x : R} {X : TempObj O R A}
    (P : Pres x X) (i : irreducibleComponents P.Lv.Z) :
    ∃ t : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
      t.1.head? = some (.inl i) := by
  haveI : Nonempty P.E := ⟨universalCovering.base P.hdim P.z₀⟩
  obtain ⟨e, he⟩ := (universalCovering.isUniversalCovering.{u, u, u} P.hdim
    P.z₀).isCoveringMap.surjective_of_connectedSpace ((curveConfig P.Lv.Z P.hdim).η i)
  have he' : e.1.1 = (curveConfig P.Lv.Z P.hdim).η i := he
  have hS := curveConfig_η_notMem_S P.hdim i
  rcases e.1.2.2.head_cases with ⟨j, hj⟩ | ⟨s, -, hs⟩
  · have hm := Cover.mem_piece_inl hj
    rw [he'] at hm
    have hji : j = i := ((curveConfig P.Lv.Z P.hdim).eq_of_notMem_S
      ((curveConfig P.Lv.Z P.hdim).η_mem i) hm.1 hS).symm
    exact ⟨e.1.2, hji ▸ hj⟩
  · have h1 := Cover.eq_of_inr hs
    have h2 := mem_S_of_head hs
    rw [← h1, he'] at h2
    exact absurd h2 hS

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Algebra.Smooth K R] in
/-- Components mapped into the conic and not contracted have their generic point off the line. -/
lemma _root_.TemperedFundamentalGroups.Pres.eta_notMem_C {x : R}
    {X : TempObj O R A} (P : Pres x X) (a : P.U ⟶ X₀ (A := A) T)
    (i : irreducibleComponents P.Lv.Z)
    (hi : specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig P.Lv.Z P.hdim).C i ⊆
      (decomp (A := A) T).E)
    (hc : ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (specialFibreMap a.ψ a.ψ_toSpec) i) :
    specialFibreMap a.ψ a.ψ_toSpec ((curveConfig P.Lv.Z P.hdim).η i) ∉ (decomp (A := A) T).C := by
  intro hC
  have hE : specialFibreMap a.ψ a.ψ_toSpec ((curveConfig P.Lv.Z P.hdim).η i) ∈
      (decomp (A := A) T).E := hi ⟨_, (curveConfig P.Lv.Z P.hdim).η_mem i, rfl⟩
  have hclo : ∀ z ∈ (decomp (A := A) T).Cp ∪ (decomp (A := A) T).Cq,
      IsClosed ({z} : Set (X₀ (A := A) T).Lv.Z) := by
    obtain ⟨hp, hq, -⟩ := decomp_spec (A := A) T
    rintro z (hz | hz)
    · have hsub : (decomp (A := A) T).Cp.Subsingleton := by
        rw [hp]; exact Set.subsingleton_singleton
      convert (decomp (A := A) T).isClosed_Cp using 1
      exact congrArg IsClosed (hsub.eq_singleton_of_mem hz).symm |>.to_iff
    · have hsub : (decomp (A := A) T).Cq.Subsingleton := by
        rw [hq]; exact Set.subsingleton_singleton
      convert (decomp (A := A) T).isClosed_Cq using 1
      exact congrArg IsClosed (hsub.eq_singleton_of_mem hz).symm |>.to_iff
  have hmem : specialFibreMap a.ψ a.ψ_toSpec ((curveConfig P.Lv.Z P.hdim).η i) ∈
      (decomp (A := A) T).Cp ∪ (decomp (A := A) T).Cq := by
    rw [← (decomp (A := A) T).inter]
    exact ⟨hC, hE⟩
  refine hc ⟨specialFibreMap a.ψ a.ψ_toSpec ((curveConfig P.Lv.Z P.hdim).η i), ?_⟩
  rw [curveConfig_image_eq_closure P.hdim (continuous_specialFibreMap _ _)
    (isClosedMap_specialFibreMap' a.ψ a.ψ_toSpec) i]
  exact (hclo _ hmem).closure_eq

/-- **Theorem B (scheme case), assembled**: some element of `temperedPi1` has non-trivial
character `temperedPi1 → ℤ`. The inputs beyond W10/`HarmonicX`/`NodeOfTwoComponents` are the
targeted `HarmonicTate`, and the hypotheses on the Tate data: `d` squarefree (the Tate model
is irreducible) and the **non-degeneracy condition `hx : Transcendental K T.x`** (false for
constant data, Blueprint §10.3.8). -/
theorem exists_character_ne_one (hW : SemistableReduction.Statement.StrongComponentA.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
    (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (hHT : ∀ {X : TempObj O R A} (P : Pres (exists_finite_aeval (K := K) hR).choose X)
      (a : P.U ⟶ X₀ (A := A) T), P.HarmonicTate T a)
    (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆)) (hx : Transcendental K T.x) :
    ∃ τ : temperedPi1 O R A V hV, character T V hV τ ≠ 1 := by
  obtain ⟨hgal, hdom, hrig⟩ := galoisLimitDataW (A := A) V hV hW p hp hpm hR
  obtain ⟨p₀, f₀, hf₀⟩ := dom₁ hdom (X₀ (A := A) T) (basePoint T V hV)
  obtain ⟨Q, -⟩ := Pres.exists_gal (Ω := Ω) p₀.mem
  obtain ⟨i₀, hi₀, -⟩ := Q.exists_image_eq_C T hd hx f₀
  obtain ⟨t₀, ht₀⟩ := Q.exists_tree_head i₀
  obtain ⟨κ, d, hd1, hκ⟩ := Q.exists_loop_of_harmonicTate V hV T (Q.iso.inv ≫ f₀)
    (hHT Q _) (fun i hi hc => Pres.eta_notMem_C T Q _ i hi hc) ht₀ hi₀
  obtain ⟨τ, hτ⟩ := exists_character_eq_of_loop V hV T hgal hdom hrig hX hN ϖ hϖ p₀.mem Q p₀.g
    f₀ hf₀ d κ hκ (fun X P a => P.exists_tree_tateNu T hd hx a)
  exact ⟨τ, hτ ▸ hd1⟩

end TateObject

end

end TemperedFundamentalGroups
