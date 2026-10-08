/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateLoop

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

/-- **Theorem B (scheme case), assembled**: some element of `temperedPi1` has non-trivial
character `temperedPi1 → ℤ`. The inputs beyond W10/`HarmonicX`/`NodeOfTwoComponents` are the
targeted `HarmonicTate` and the Tate dominance statements (G1). -/
theorem exists_character_ne_one (hW : SemistableReduction.Statement.StrongComponentA.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
    (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (hHT : ∀ {X : TempObj O R A} (P : Pres (exists_finite_aeval (K := K) hR).choose X)
      (a : P.U ⟶ X₀ (A := A) T), P.HarmonicTate T a)
    (hCC : ∀ {X : TempObj O R A} (P : Pres (exists_finite_aeval (K := K) hR).choose X)
      (a : P.U ⟶ X₀ (A := A) T), ∃ (t₀ : (curveConfig P.Lv.Z P.hdim).Tree
        (universalCovering.root P.hdim P.z₀)) (i₀ : irreducibleComponents P.Lv.Z),
        t₀.1.head? = some (.inl i₀) ∧
        specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig P.Lv.Z P.hdim).C i₀ =
          (decomp (A := A) T).C)
    (hE : ∀ {X : TempObj O R A} (P : Pres (exists_finite_aeval (K := K) hR).choose X)
      (a : P.U ⟶ X₀ (A := A) T) (i : irreducibleComponents P.Lv.Z),
      specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig P.Lv.Z P.hdim).C i = (decomp (A := A) T).E →
      specialFibreMap a.ψ a.ψ_toSpec ((curveConfig P.Lv.Z P.hdim).η i) ∉ (decomp (A := A) T).C)
    (hG1 : ∀ (X : TempObj O R A) (P : Pres (exists_finite_aeval (K := K) hR).choose X)
      (a : X ⟶ X₀ (A := A) T),
      ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
        IsComp t₁ ∧ P.tateNu T a (lab t₁)) :
    ∃ τ : temperedPi1 O R A V hV, character T V hV τ ≠ 1 := by
  obtain ⟨hgal, hdom, hrig⟩ := galoisLimitDataW (A := A) V hV hW p hp hpm hR
  obtain ⟨p₀, f₀, hf₀⟩ := dom₁ hdom (X₀ (A := A) T) (basePoint T V hV)
  obtain ⟨Q, -⟩ := Pres.exists_gal (Ω := Ω) p₀.mem
  obtain ⟨t₀, i₀, ht₀, hi₀⟩ := hCC Q (Q.iso.inv ≫ f₀)
  obtain ⟨κ, d, hd, hκ⟩ := Q.exists_loop_of_harmonicTate V hV T (Q.iso.inv ≫ f₀)
    (hHT Q _) (hE Q _) ht₀ hi₀
  obtain ⟨τ, hτ⟩ := exists_character_eq_of_loop V hV T hgal hdom hrig hX hN ϖ hϖ p₀.mem Q p₀.g
    f₀ hf₀ d κ hκ hG1
  exact ⟨τ, hτ ▸ hd⟩

end TateObject

end

end TemperedFundamentalGroups
