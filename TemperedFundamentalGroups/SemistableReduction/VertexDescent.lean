/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussDescent
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization
import TemperedFundamentalGroups.Setup.Valuation

/-!
# Descent of vertex sets

Blueprint §9.8 (W9), layer D3. Let `K ⊆ C` be an algebraic extension (in the application a finite
extension `K'` of the henselian base inside `C = \bar K'`), `v` a valuation on `C` and
`v' = v|_K`.

* **Residue fields of algebraic extensions are algebraic** (`isAlgebraic_residueField`): the
  residues of algebraic elements are algebraic (`not_isResidueTranscendental_of_isAlgebraic`).
* **D3a: Gauss valuations have a unique extension along `K(X) → C(X)`**
  (`eq_gaussRat_of_comap_eq`): a valuation subring `W` of `C(X)` over `O_C` lying over the Gauss
  valuation `w'_{a, r}` of `K(X)` (with `a`, and a `c` with `v(c) = r`, in `K`) is the Gauss
  valuation `w_{a, r}` of `C(X)`. The residue of `(X - a)/c` is transcendental over `κ(O_K)`, and
  `κ(O_C)/κ(O_K)` is algebraic, so it stays transcendental over `κ(O_C)` (W2 in the form
  `IsGaussCoord.eq_of_isResidueTranscendental`).
* **D3b: vertex sets of normalizations restrict onto each other**
  (`comap_comap_eq_gaussRat`, `exists_comap_eq_gaussRat`, `vertexSet_mapsTo`,
  `vertexSet_surjOn`): for function fields `L'/K(X)`, `L/C(X)` and a compatible embedding
  `χ : L' → L`, restriction along `χ` maps the vertex set of the normalization of the tree model
  over `O_C` in `L` onto the vertex set of the normalization of the tree model over `O_K` in `L'`,
  provided `O_C` is the only extension of `O_K` to `C` (e.g. `K` henselian).
* **D3c: restriction becomes injective on a finite set after enlarging the field**
  (`exists_injOn_comap`): if `L` is the directed union of subfields `E j`, then for every finite
  set of valuation subrings of `L` restriction to some `E j` is injective on it. Together with
  D3b (applied to `L' = E j`, `E j = L'·K_j` for finite `K_j ⊇ K`) the vertex sets over `C` and
  over `K_j` are in bijection for `K_j` large.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

open ZariskiModel

/-! ### Residue fields of algebraic extensions -/

section Residue

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {O : ValuationSubring K}
  {V : ValuationSubring Ω}

/-- The residue of an algebraic element is algebraic. -/
lemma not_isResidueTranscendental_of_isAlgebraic {x : Ω} (hx : IsAlgebraic K x) :
    ¬IsResidueTranscendental O V x := by
  rintro ⟨-, h⟩
  obtain ⟨p, hp0, hpx⟩ := hx
  obtain ⟨d, hd, hdp⟩ := IsGaussCoord.exists_sup_eq_one (v := O.valuation) hp0
  have hcoeff (n : ℕ) : (C d * p).coeff n ∈ O :=
    (O.valuation_le_one_iff _).1 (coeff_le_one_of_sup_le_one hdp.le n)
  obtain ⟨P, hP⟩ : ∃ P : O[X], P.map (algebraMap O K) = C d * p := by
    rw [← mem_lifts, lifts_iff_coeff_lifts]
    exact fun n ↦ ⟨⟨_, hcoeff n⟩, rfl⟩
  have hP0 : P.map (residue O) ≠ 0 := by
    intro h0
    obtain ⟨j, hj⟩ := Gauss.exists_term_eq_sup (v := O.valuation) (r := 1) (C d * p)
    have hres : residue O (P.coeff j) = 0 := by simpa using congrArg (coeff · j) h0
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      ValuationSubring.valuation_eq_one_iff] at hres
    apply hres
    have hPj : ((P.coeff j : O) : K) = (C d * p).coeff j := by
      rw [← hP, coeff_map]
      rfl
    rw [hPj]
    simpa [Gauss.term, hdp] using hj
  have := h P hP0
  rw [hP, map_mul, aeval_C, hpx, mul_zero, map_zero] at this
  exact zero_ne_one this

/-- **Residue fields of algebraic extensions are algebraic.** -/
theorem isAlgebraic_residueField [Algebra.IsAlgebraic K Ω]
    (hV : V.comap (algebraMap K Ω) = O) :
    letI := residueAlgebra hV
    Algebra.IsAlgebraic (ResidueField O) (ResidueField V) := by
  letI := residueAlgebra hV
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective z
  have h := (isResidueTranscendental_iff hV x.2).not.1
    (not_isResidueTranscendental_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic (x : Ω)))
  exact not_not.1 h

end Residue

end SemistableReduction
