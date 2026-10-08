/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SplitChart

/-!
# Components through a point as minimal primes (W8′, XL1, H6 glue)

Blueprint §9.7 (XL1). For a model `c` over a DVR `O` with uniformizer `ϖ`, an affine open `U` and
`x ∈ U`, `x` lies in the special fibre iff `ϖ` lies in the prime of `x` (`mem_Z_iff`). If a point
`y` lies on two distinct components, their generic points give two distinct primes of `Γ(U)`
inside the prime of `y`, minimal among the primes containing `ϖ` (`exists_minimal_primes_of_mem`;
for node points under `NoLoops`: `exists_minimal_primes_of_noLoops`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

open _root_.SemistableReduction

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {c : TemperedFundamentalGroups.ModelCode O}

/-- **The special fibre in an affine chart**: `x ∈ Z c` iff `ϖ` vanishes at `x`. -/
theorem mem_Z_iff {ϖ : O} (hϖ : Irreducible ϖ) {U : c.scheme.Opens} (hU : IsAffineOpen U)
    {x : c.scheme} (hx : x ∈ U) :
    letI := sectionsAlgebra c U
    x ∈ Z c ↔ algebraMap O Γ(c.scheme, U) ϖ ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  letI := sectionsAlgebra c U
  rw [mem_primeIdealOf_iff]
  have hbo : c.scheme.basicOpen (algebraMap O Γ(c.scheme, U) ϖ) =
      U ⊓ c.toSpec ⁻¹ᵁ (Spec (CommRingCat.of O)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ) := by
    change c.scheme.basicOpen ((c.scheme.presheaf.map (homOfLE le_top).op).hom
      ((c.toSpec.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ))) = _
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
    rfl
  have hmem : c.toSpec x ∈ (Spec (CommRingCat.of O)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ) ↔ ϖ ∉ (c.toSpec x).asIdeal := by
    rw [AlgebraicGeometry.basicOpen_eq_of_affine]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [hbo]
  simp only [TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage, not_and, hx, true_implies]
  rw [hmem, not_not]
  change c.toSpec x = closedPoint O ↔ _
  constructor
  · intro h
    rw [h]
    exact (mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  · intro h
    apply PrimeSpectrum.ext
    rw [IsLocalRing.closedPoint]
    refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (c.toSpec x).isPrime.ne_top ?_).symm
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_le,
      Set.singleton_subset_iff]
    exact h

/-- Components of the special fibre are closed. -/
lemma isClosed_of_mem_components {v : Set c.scheme} (hv : v ∈ components c) : IsClosed v := by
  have h1 : closure v ⊆ Z c := closure_minimal hv.2.1 (isClosed_Z c)
  have h2 := hv.2.2 (closure v) hv.1.closure h1 subset_closure
  rw [← h2]; exact isClosed_closure

/-- **Two components give two minimal primes.** If the point `y` lies on two distinct
components `v ≠ w`, their generic points give two distinct primes of `Γ(U)` (`U` affine, `y ∈ U`)
contained in the prime of `y`, each minimal among the primes containing `ϖ`. -/
theorem exists_minimal_primes_of_mem {ϖ : O} (hϖ : Irreducible ϖ) {y : c.scheme}
    {v w : Set c.scheme} (hv : v ∈ components c) (hw : w ∈ components c) (hvw : v ≠ w)
    (hyv : y ∈ v) (hyw : y ∈ w) {U : c.scheme.Opens} (hU : IsAffineOpen U) (hyU : y ∈ U) :
    letI := sectionsAlgebra c U
    ∃ P₁ P₂ : Ideal Γ(c.scheme, U), P₁.IsPrime ∧ P₂.IsPrime ∧
      algebraMap O _ ϖ ∈ P₁ ∧ algebraMap O _ ϖ ∈ P₂ ∧
      P₁ ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∧ P₂ ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∧
      (∀ Q : Ideal Γ(c.scheme, U), Q.IsPrime → algebraMap O _ ϖ ∈ Q → Q ≤ P₁ → Q = P₁) ∧
      (∀ Q : Ideal Γ(c.scheme, U), Q.IsPrime → algebraMap O _ ϖ ∈ Q → Q ≤ P₂ → Q = P₂) ∧
      P₁ ≠ P₂ := by
  letI := sectionsAlgebra c U
  have hind : Topology.IsInducing hU.fromSpec := hU.fromSpec.isOpenEmbedding.isInducing
  -- the prime of a component through `y`
  have key : ∀ v ∈ components c, y ∈ v → ∃ η ∈ U, closure {η} = v ∧
      (∃ hη : η ∈ U, ((hU.primeIdealOf ⟨η, hη⟩).asIdeal).IsPrime ∧
        algebraMap O _ ϖ ∈ (hU.primeIdealOf ⟨η, hη⟩).asIdeal ∧
        (hU.primeIdealOf ⟨η, hη⟩).asIdeal ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∧
        ∀ Q : Ideal Γ(c.scheme, U), Q.IsPrime → algebraMap O _ ϖ ∈ Q →
          Q ≤ (hU.primeIdealOf ⟨η, hη⟩).asIdeal → Q = (hU.primeIdealOf ⟨η, hη⟩).asIdeal) := by
    intro v hv hyv
    have hcl := isClosed_of_mem_components hv
    set η := hv.1.genericPoint
    have hgen : closure {η} = v := by
      have := hv.1.isGenericPoint_genericPoint_closure
      rw [hcl.closure_eq] at this
      exact this
    have hηy : η ⤳ y := by
      rw [specializes_iff_mem_closure, hgen]; exact hyv
    have hηU : η ∈ U := hηy.mem_open U.isOpen hyU
    have hηv : η ∈ v := by rw [← hgen]; exact subset_closure rfl
    refine ⟨η, hηU, hgen, hηU, inferInstance, (mem_Z_iff hϖ hU hηU).mp (hv.2.1 hηv), ?_, ?_⟩
    · have : hU.fromSpec (hU.primeIdealOf ⟨η, hηU⟩) ⤳ hU.fromSpec (hU.primeIdealOf ⟨y, hyU⟩) := by
        rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]; exact hηy
      exact (PrimeSpectrum.le_iff_specializes _ _).mpr (hind.specializes_iff.mp this)
    · intro Q hQ hϖQ hQle
      let q : PrimeSpectrum Γ(c.scheme, U) := ⟨Q, hQ⟩
      set z := hU.fromSpec q
      have hzU : z ∈ U := by
        have : z ∈ Set.range hU.fromSpec := Set.mem_range_self q
        rwa [hU.range_fromSpec] at this
      have hqz : hU.primeIdealOf ⟨z, hzU⟩ = q := by
        apply hU.fromSpec.isOpenEmbedding.injective
        rw [hU.fromSpec_primeIdealOf]
      have hzη : z ⤳ η := by
        have : q ⤳ hU.primeIdealOf ⟨η, hηU⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hQle
        have := hind.specializes_iff.mpr this
        rwa [hU.fromSpec_primeIdealOf] at this
      have hzZ : z ∈ Z c := by
        rw [mem_Z_iff hϖ hU hzU, hqz]; exact hϖQ
      have hirr : IsIrreducible (closure {z}) := isIrreducible_singleton.closure
      have hsub : closure {z} ⊆ Z c := closure_minimal (by simpa using hzZ) (isClosed_Z c)
      have hvsub : v ⊆ closure {z} := by
        rw [← hgen]
        exact closure_minimal (by simpa [← specializes_iff_mem_closure] using hzη) isClosed_closure
      have heq := hv.2.2 _ hirr hsub hvsub
      have hz : z = η := by
        have h1 : IsGenericPoint z v := by rw [IsGenericPoint, heq]
        have h2 : IsGenericPoint η v := hgen
        exact h1.eq h2
      have : q = hU.primeIdealOf ⟨η, hηU⟩ := by
        rw [← hqz]; congr 1; exact Subtype.ext hz
      exact congrArg PrimeSpectrum.asIdeal this
  obtain ⟨η₁, -, hgen₁, hη₁, hp₁, hϖ₁, hle₁, hmin₁⟩ := key v hv hyv
  obtain ⟨η₂, -, hgen₂, hη₂, hp₂, hϖ₂, hle₂, hmin₂⟩ := key w hw hyw
  refine ⟨_, _, hp₁, hp₂, hϖ₁, hϖ₂, hle₁, hle₂, hmin₁, hmin₂, fun heq ↦ hvw ?_⟩
  have : η₁ = η₂ := by
    have e1 := hU.fromSpec_primeIdealOf ⟨η₁, hη₁⟩
    have e2 := hU.fromSpec_primeIdealOf ⟨η₂, hη₂⟩
    have e3 : hU.primeIdealOf ⟨η₁, hη₁⟩ = hU.primeIdealOf ⟨η₂, hη₂⟩ := PrimeSpectrum.ext heq
    rw [e3] at e1
    exact e1.symm.trans e2
  rw [← hgen₁, ← hgen₂, this]

/-- **No loops gives two minimal primes.** If the node point `y` lies on two distinct components,
their generic points give two distinct primes of `Γ(U)` (`U` affine, `y ∈ U`) contained in the
prime of `y`, each minimal among the primes containing `ϖ`. -/
theorem exists_minimal_primes_of_noLoops {ϖ : O} (hϖ : Irreducible ϖ) (hc : NoLoops c)
    {y : c.scheme} (hy : IsNodePt c y) {U : c.scheme.Opens} (hU : IsAffineOpen U) (hyU : y ∈ U) :
    letI := sectionsAlgebra c U
    ∃ P₁ P₂ : Ideal Γ(c.scheme, U), P₁.IsPrime ∧ P₂.IsPrime ∧
      algebraMap O _ ϖ ∈ P₁ ∧ algebraMap O _ ϖ ∈ P₂ ∧
      P₁ ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∧ P₂ ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal ∧
      (∀ Q : Ideal Γ(c.scheme, U), Q.IsPrime → algebraMap O _ ϖ ∈ Q → Q ≤ P₁ → Q = P₁) ∧
      (∀ Q : Ideal Γ(c.scheme, U), Q.IsPrime → algebraMap O _ ϖ ∈ Q → Q ≤ P₂ → Q = P₂) ∧
      P₁ ≠ P₂ := by
  obtain ⟨v, hv, w, hw, hvw, hyv, hyw⟩ := hc y hy
  exact exists_minimal_primes_of_mem hϖ hv hw hvw hyv hyw hU hyU

end TemperedFundamentalGroups.SemistableReduction.ModelCode
