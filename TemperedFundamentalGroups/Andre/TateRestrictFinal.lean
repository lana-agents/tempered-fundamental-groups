/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictDeck
import TemperedFundamentalGroups.Andre.TheoremBFinal

/-!
# Theorem B for the restricted Tate object (Blueprint §10.3.8, `v(q) = 1`, assembly)

`TateRestrict.exists_character'_ne_one_of`: as `TateObject.exists_character_ne_one`, for the
restricted Tate object `X₀'` and its character `character'`, through the middle layer for any
target (`TateObject.exists_character_eq_of_loopG`) with `ModelUnique` for `X₀'`
(`TateRestrict.modelUnique'`, the `σ`-invariance of `tateNuG` and `HCWG`). The geometric inputs
(a component over the line `C`, and `HarmonicTateR`) are hypotheses here.
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
  (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

omit [Subsingleton A] in
/-- Generic points of non-contracted components mapped into `E` lie off `C`, when the two parts
of `C ∩ E` are subsingletons. -/
lemma eta_notMem_of_decomp {Z Z' : Type u} [TopologicalSpace Z] [TopologicalSpace Z']
    [NoetherianSpace Z] [T0Space Z] [QuasiSober Z]
    (hdim : topologicalKrullDim Z ≤ 1) (D : TateCovering.Decomp Z')
    (hp : D.Cp.Subsingleton) (hq : D.Cq.Subsingleton) {ψ : Z → Z'} (hψ : Continuous ψ)
    (hψc : IsClosedMap ψ) (i : irreducibleComponents Z) (hi : ψ '' (curveConfig Z hdim).C i ⊆ D.E)
    (hc : ¬ Contr (K := curveConfig Z hdim) ψ i) : ψ ((curveConfig Z hdim).η i) ∉ D.C := by
  intro hC
  have hE : ψ ((curveConfig Z hdim).η i) ∈ D.E := hi ⟨_, (curveConfig Z hdim).η_mem i, rfl⟩
  have hmem : ψ ((curveConfig Z hdim).η i) ∈ D.Cp ∪ D.Cq := D.inter ▸ ⟨hC, hE⟩
  have hclo : IsClosed {ψ ((curveConfig Z hdim).η i)} := by
    rcases hmem with hz | hz
    · exact hp.eq_singleton_of_mem hz ▸ D.isClosed_Cp
    · exact hq.eq_singleton_of_mem hz ▸ D.isClosed_Cq
  refine hc ⟨ψ ((curveConfig Z hdim).η i), ?_⟩
  rw [curveConfig_image_eq_closure hdim hψ hψc i]
  exact hclo.closure_eq

omit [Subsingleton A] in
lemma decompR_Cp_subsingleton : (decompR hϖ b₄ b₆).Cp.Subsingleton := by
  unfold decompR TateCovering.Decomp.comap
  unfold TateModel.decomp
  dsimp only
  rw [TateModel.Cp_eq (sO_mem hϖ)]
  intro z hz w hw
  exact (ΦR hϖ b₄ b₆).injective (hz.trans hw.symm)

omit [Subsingleton A] in
lemma decompR_Cq_subsingleton : (decompR hϖ b₄ b₆).Cq.Subsingleton := by
  unfold decompR TateCovering.Decomp.comap
  unfold TateModel.decomp
  dsimp only
  rw [TateModel.Cq_eq (sO_mem hϖ)]
  intro z hz w hw
  exact (ΦR hϖ b₄ b₆).injective (hz.trans hw.symm)

namespace Pres

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero K]
  [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)))]
  [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω] [Subsingleton A] in
/-- (G1), tree form, from a component not contracted over the target. -/
lemma exists_tree_tateNuG {xW : R} {X₀ X : TempObj O R A} (P : Pres xW X) (a : X ⟶ X₀)
    (i : irreducibleComponents P.Lv.Z) (hi : P.tateNuG a i) :
    ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
      IsComp t₁ ∧ P.tateNuG a (lab t₁) := by
  obtain ⟨t, ht⟩ := P.exists_tree_head i
  exact ⟨t, ⟨i, ht⟩, by rw [lab_of ht]; exact hi⟩

omit [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω] in
/-- Components mapped into the conic and not contracted have their generic point off the line. -/
lemma eta_notMem_CR {xW : R} {X : TempObj O R A} (P : Pres xW X)
    (a : P.U ⟶ X₀' hϖ b₄ b₆ R heqR A) (i : irreducibleComponents P.Lv.Z)
    (hi : specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig P.Lv.Z P.hdim).C i ⊆
      (decompR hϖ b₄ b₆).E)
    (hc : ¬ Contr (K := curveConfig P.Lv.Z P.hdim) (specialFibreMap a.ψ a.ψ_toSpec) i) :
    specialFibreMap a.ψ a.ψ_toSpec ((curveConfig P.Lv.Z P.hdim).η i) ∉
      (decompR hϖ b₄ b₆).C :=
  eta_notMem_of_decomp P.hdim (decompR hϖ b₄ b₆) (decompR_Cp_subsingleton hϖ b₄ b₆)
    (decompR_Cq_subsingleton hϖ b₄ b₆) (continuous_specialFibreMap _ _)
    (isClosedMap_specialFibreMap' a.ψ a.ψ_toSpec) i hi hc

end Pres

namespace TateRestrict

/-- **Theorem B for the restricted Tate object** (`v(q) = 1`), from the geometric inputs: a
component over the line `C` (S1, with G1) and `HarmonicTateR`. The middle layer is
`exists_character_eq_of_loopG` with `ModelUnique` for `X₀'` (`modelUnique'`). -/
theorem exists_character'_ne_one_of [Algebra.Smooth K R] [IsDomain R]
    (hW : SemistableReduction.Statement.StrongComponentAS.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u})
    (hS1 : ∀ {X : TempObj O R A} (P : Pres (exists_finite_aeval (K := K) hR).choose X)
      (a : X ⟶ X₀' hϖ b₄ b₆ R heqR A), ∃ i : irreducibleComponents P.Lv.Z,
        P.tateMapG a '' (curveConfig P.Lv.Z P.hdim).C i = (decompR hϖ b₄ b₆).C ∧
          P.tateNuG a i)
    (ℰ : Set (Set (specialFibre (modelR hϖ b₄ b₆).toSpec)))
    (hℰ : ∀ S ∈ ℰ, S ⊆ (decompR hϖ b₄ b₆).E ∧ ¬ ∃ y, S = {y})
    (hHT : ∀ {X : TempObj O R A} (P : Pres (exists_finite_aeval (K := K) hR).choose X)
      (a : P.U ⟶ X₀' hϖ b₄ b₆ R heqR A), P.HarmonicTateR hϖ b₄ b₆ R heqR A ℰ a) :
    ∃ τ : temperedPi1 O R A V hV, character' hϖ b₄ b₆ R heqR A V hV τ ≠ 1 := by
  obtain ⟨hgal, hdom, hrig⟩ := galoisLimitDataW (A := A) V hV hW p hp hpm hR
  obtain ⟨p₀, f₀, hf₀⟩ := dom₁ hdom (X₀' hϖ b₄ b₆ R heqR A) (basePoint' hϖ b₄ b₆ R heqR A V hV)
  obtain ⟨Q, -⟩ := Pres.exists_gal (Ω := Ω) p₀.mem
  obtain ⟨i₀, hi₀, -⟩ := hS1 Q f₀
  obtain ⟨t₀, ht₀⟩ := Q.exists_tree_head i₀
  obtain ⟨κ, d, hd1, hκ⟩ := Q.exists_loop_of_harmonicTateR hϖ b₄ b₆ R heqR A V hV
    (Q.iso.inv ≫ f₀) ℰ hℰ (hHT Q _)
    (fun i hi hc ↦ Pres.eta_notMem_CR hϖ b₄ b₆ R heqR A Q _ i hi hc) ht₀ hi₀
  obtain ⟨τ, hτ⟩ := TateObject.exists_character_eq_of_loopG V hV (X₀' hϖ b₄ b₆ R heqR A)
    (deck' hϖ b₄ b₆ R heqR A) (basePoint' hϖ b₄ b₆ R heqR A V hV)
    (isDeckTorsor' hϖ b₄ b₆ R heqR A V hV) (modelUnique' hϖ b₄ b₆ R heqR A) hgal hdom hrig
    SemistableReduction.harmonicXS hN ϖ hϖ p₀.mem Q p₀.g f₀ hf₀ d κ hκ
    (fun X P a ↦ by
      obtain ⟨i, -, hi⟩ := hS1 P a
      exact P.exists_tree_tateNuG R A a i hi)
  exact ⟨τ, hτ ▸ hd1⟩

end TateRestrict

end

end TemperedFundamentalGroups
