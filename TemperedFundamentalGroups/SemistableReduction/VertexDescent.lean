/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussDescent
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization
import TemperedFundamentalGroups.Setup.Valuation
import TemperedFundamentalGroups.SemistableReduction.UniqueExtension

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

/-! ### D3a: unique extension of Gauss valuations -/

section Unique

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation Ω Γ₀)

/-- The Gauss valuation `w_{a, r}` lies over `v`. -/
lemma comap_algebraMap_gaussRat (v : Valuation K Γ₀) (a : K) (r : Γ₀ˣ) :
    (gaussRat v a r).valuationSubring.comap (algebraMap K (RatFunc K)) = v.valuationSubring := by
  ext x
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
    Valuation.mem_valuationSubring_iff, gaussRat_algebraMap_C]

variable {v}

/-- **(W9, D3a) Unique extension of Gauss valuations.** Let `Ω/K` be algebraic, `v` a valuation
on `Ω`, `a, c ∈ K` with `v(c) = r`. A valuation subring `W` of `Ω(X)` with `W ∩ Ω = O_v` lying
over the Gauss valuation `w_{a, r}` of `K(X)` (for `v|_K`) is the Gauss valuation `w_{a, r}` of
`Ω(X)`. -/
theorem eq_gaussRat_of_comap_eq [Algebra.IsAlgebraic K Ω] {a c : K} {r : Γ₀ˣ}
    (hc : v (algebraMap K Ω c) = r) {W : ValuationSubring (RatFunc Ω)}
    (hWΩ : W.comap (algebraMap Ω (RatFunc Ω)) = v.valuationSubring)
    (hW : W.comap (ratFuncMap (algebraMap K Ω)) =
      (gaussRat (v.comap (algebraMap K Ω)) a r).valuationSubring) :
    W = (gaussRat v (algebraMap K Ω a) r).valuationSubring := by
  set φ := algebraMap K Ω
  set v' := v.comap φ
  set y' := gaussCoord a c
  have hG' : IsGaussCoord v' (gaussRat v' a r) y' := isGaussCoord_gaussCoord
    (by rw [Valuation.comap_apply]; exact hc)
  have hG : IsGaussCoord v (gaussRat v (φ a) r) (ratFuncMap φ y') := by
    rw [ratFuncMap_gaussCoord]
    exact isGaussCoord_gaussCoord hc
  refine hG.eq_of_isResidueTranscendental hWΩ ?_
  have hO : v.valuationSubring.comap φ = v'.valuationSubring := (comap_valuationSubring φ v).symm
  have hW' : W.comap (algebraMap K (RatFunc Ω)) = v'.valuationSubring := by
    rw [IsScalarTower.algebraMap_eq K Ω (RatFunc Ω), ← ValuationSubring.comap_comap, hWΩ, hO]
  have hval (z : RatFunc K) : W.valuation (ratFuncMap φ z) = 1 ↔
      (gaussRat v' a r).valuationSubring.valuation z = 1 := by
    rw [valuation_eq_one_iff_mem_and_inv_mem, valuation_eq_one_iff_mem_and_inv_mem, ← hW,
      ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀,
      map_ne_zero_iff _ (ratFuncMap φ).injective]
  have haeval (Q : K[X]) : aeval (ratFuncMap φ y') Q = ratFuncMap φ (aeval y' Q) := by
    rw [aeval_def, aeval_def, hom_eval₂]
    congr 1
    ext k
    exact (IsScalarTower.algebraMap_apply K Ω (RatFunc Ω) k).trans
      (ratFuncMap_algebraMap_C φ k).symm
  have hyW : ratFuncMap φ y' ∈ W := by
    rw [← ValuationSubring.mem_comap, hW]
    exact hG'.isResidueTranscendental.1
  have hRT : IsResidueTranscendental v'.valuationSubring W (ratFuncMap φ y') :=
    ⟨hyW, fun P hP ↦ by rw [haeval, hval]; exact hG'.isResidueTranscendental.2 P hP⟩
  letI := residueAlgebra hW'
  letI := residueAlgebra hWΩ
  letI := residueAlgebra hO
  haveI : IsScalarTower (ResidueField v'.valuationSubring) (ResidueField v.valuationSubring)
      (ResidueField W) := by
    refine IsScalarTower.of_algebraMap_eq' (Ideal.Quotient.ringHom_ext (RingHom.ext fun o ↦ ?_))
    change ResidueField.map _ (residue _ o) = ResidueField.map _ (ResidueField.map _ (residue _ o))
    rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
    congr 1
  haveI := isAlgebraic_residueField hO
  have ht := (isResidueTranscendental_iff hW' hyW).1 hRT
  rw [isResidueTranscendental_iff hWΩ hyW]
  exact fun halg ↦ ht (halg.restrictScalars (R := ResidueField v'.valuationSubring))

end Unique

/-! ### D3b: vertex sets of normalizations restrict onto each other -/

section Vertex

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation Ω Γ₀}
  {L' L : Type*} [Field L'] [Field L] [Algebra (RatFunc K) L'] [Algebra (RatFunc Ω) L]
  {χ : L' →+* L}
  (hχ : ∀ x, χ (algebraMap (RatFunc K) L' x) =
    algebraMap (RatFunc Ω) L (ratFuncMap (algebraMap K Ω) x))

include hχ

lemma comp_algebraMap_eq :
    χ.comp (algebraMap (RatFunc K) L') =
      (algebraMap (RatFunc Ω) L).comp (ratFuncMap (algebraMap K Ω)) :=
  RingHom.ext hχ

/-- **(W9, D3b) Restriction of vertices.** A valuation subring of `L` over the Gauss valuation
`w_{a, r}` of `Ω(X)` restricts to a valuation subring of `L'` over the Gauss valuation `w_{a, r}`
of `K(X)`. -/
theorem comap_comap_eq_gaussRat {a : K} {r : Γ₀ˣ} {W : ValuationSubring L}
    (hW : W.comap (algebraMap (RatFunc Ω) L) = (gaussRat v (algebraMap K Ω a) r).valuationSubring) :
    (W.comap χ).comap (algebraMap (RatFunc K) L') =
      (gaussRat (v.comap (algebraMap K Ω)) a r).valuationSubring := by
  rw [ValuationSubring.comap_comap, comp_algebraMap_eq hχ, ← ValuationSubring.comap_comap, hW,
    comap_valuationSubring_gaussRat]

/-- **(W9, D3b) Lifting of vertices.** Let `Ω/K` be algebraic and assume `O_v` is the only
valuation subring of `Ω` over `O_v ∩ K` (e.g. `K` henselian). Every valuation subring `W'` of `L'`
over the Gauss valuation `w_{a, r}` of `K(X)` (`a`, `c ∈ K`, `v(c) = r`) is the restriction of a
valuation subring of `L` over the Gauss valuation `w_{a, r}` of `Ω(X)`. -/
theorem exists_comap_eq_gaussRat [Algebra.IsAlgebraic K Ω]
    (huniq : ∀ V : ValuationSubring Ω, V.comap (algebraMap K Ω) =
      v.valuationSubring.comap (algebraMap K Ω) → V = v.valuationSubring)
    {a c : K} {r : Γ₀ˣ} (hc : v (algebraMap K Ω c) = r) {W' : ValuationSubring L'}
    (hW' : W'.comap (algebraMap (RatFunc K) L') =
      (gaussRat (v.comap (algebraMap K Ω)) a r).valuationSubring) :
    ∃ W : ValuationSubring L, W.comap (algebraMap (RatFunc Ω) L) =
      (gaussRat v (algebraMap K Ω a) r).valuationSubring ∧ W.comap χ = W' := by
  letI : Algebra L' L := χ.toAlgebra
  obtain ⟨W, hW⟩ := TemperedFundamentalGroups.ValuationSubring.exists_comap_eq (Ω := L) W'
  have hWχ : W.comap χ = W' := hW
  set U := W.comap (algebraMap (RatFunc Ω) L)
  have hU : U.comap (ratFuncMap (algebraMap K Ω)) =
      (gaussRat (v.comap (algebraMap K Ω)) a r).valuationSubring := by
    rw [ValuationSubring.comap_comap, ← comp_algebraMap_eq hχ, ← ValuationSubring.comap_comap,
      hWχ, hW']
  have hUΩ : U.comap (algebraMap Ω (RatFunc Ω)) = v.valuationSubring := by
    refine huniq _ ?_
    rw [ValuationSubring.comap_comap, ← ratFuncMap_comp_algebraMap,
      ← ValuationSubring.comap_comap, hU, comap_algebraMap_gaussRat, comap_valuationSubring]
  exact ⟨W, eq_gaussRat_of_comap_eq hc hUΩ hU, hWχ⟩

variable [Algebra K L'] [IsScalarTower K (RatFunc K) L'] [Algebra.IsAlgebraic (RatFunc K) L']
  [Algebra Ω L] [IsScalarTower Ω (RatFunc Ω) L] [Algebra.IsAlgebraic (RatFunc Ω) L]
  {ι : Type*} [Fintype ι] {a c : ι → K} {r : ι → Γ₀ˣ}

/-- **(W9, D3b) Vertices restrict to vertices**: restriction along `χ` maps the vertex set of the
normalization in `L` of the tree model over `O_v` into the vertex set of the normalization in `L'`
of the tree model over `O_v ∩ K`. -/
theorem vertexSet_mapsTo (hc : ∀ i, v (algebraMap K Ω (c i)) = r i) :
    Set.MapsTo (fun W : ValuationSubring L ↦ W.comap χ)
      ((gaussJoinModel v (fun i ↦ algebraMap K Ω (a i))
        (fun i ↦ algebraMap K Ω (c i))).normalization L).vertexSet
      ((gaussJoinModel (v.comap (algebraMap K Ω)) a c).normalization L').vertexSet := by
  rw [gaussJoinModel_normalization_vertexSet hc,
    gaussJoinModel_normalization_vertexSet (v := v.comap (algebraMap K Ω)) (r := r)
      (fun i ↦ by rw [Valuation.comap_apply]; exact hc i)]
  rintro W ⟨i, hi⟩
  exact ⟨i, comap_comap_eq_gaussRat hχ hi⟩

/-- **(W9, D3b) Every vertex over `O_v ∩ K` lifts**: if `Ω/K` is algebraic and `O_v` is the only
extension of `O_v ∩ K` to `Ω`, restriction along `χ` maps the vertex set of the normalization in
`L` of the tree model over `O_v` onto the vertex set of the normalization in `L'` of the tree model
over `O_v ∩ K`. -/
theorem vertexSet_surjOn [Algebra.IsAlgebraic K Ω]
    (huniq : ∀ V : ValuationSubring Ω, V.comap (algebraMap K Ω) =
      v.valuationSubring.comap (algebraMap K Ω) → V = v.valuationSubring)
    (hc : ∀ i, v (algebraMap K Ω (c i)) = r i) :
    Set.SurjOn (fun W : ValuationSubring L ↦ W.comap χ)
      ((gaussJoinModel v (fun i ↦ algebraMap K Ω (a i))
        (fun i ↦ algebraMap K Ω (c i))).normalization L).vertexSet
      ((gaussJoinModel (v.comap (algebraMap K Ω)) a c).normalization L').vertexSet := by
  rw [gaussJoinModel_normalization_vertexSet hc,
    gaussJoinModel_normalization_vertexSet (v := v.comap (algebraMap K Ω)) (r := r)
      (fun i ↦ by rw [Valuation.comap_apply]; exact hc i)]
  rintro W' ⟨i, hi⟩
  obtain ⟨W, hW, hWχ⟩ := exists_comap_eq_gaussRat hχ huniq (hc i) hi
  exact ⟨W, ⟨i, hW⟩, hWχ⟩

end Vertex

/-! ### D3c: injectivity after enlarging the field -/

/-- **(W9, D3c)** If the field `L` is the directed union of subfields `E j`, then for every finite
set `S` of valuation subrings of `L` there is a `j` such that restriction to `E j` is injective on
`S`: two distinct valuation subrings are separated by an element, which lies in some `E j`. -/
theorem exists_injOn_comap {L : Type*} [Field L] {J : Type*} [Nonempty J] (E : J → Subfield L)
    (hdir : Directed (· ≤ ·) E) (hcov : ∀ x, ∃ j, x ∈ E j) {S : Set (ValuationSubring L)}
    (hS : S.Finite) : ∃ j, Set.InjOn (fun W : ValuationSubring L ↦ W.comap (E j).subtype) S := by
  classical
  have hsep (W₁ W₂ : ValuationSubring L) : ∃ j, W₁ ≠ W₂ →
      ∃ x ∈ E j, ¬(x ∈ W₁ ↔ x ∈ W₂) := by
    by_cases h : W₁ = W₂
    · exact ⟨Classical.arbitrary J, fun h' ↦ (h' h).elim⟩
    obtain ⟨x, hx⟩ : ∃ x, ¬(x ∈ W₁ ↔ x ∈ W₂) := by
      by_contra hne
      exact h (SetLike.ext fun x ↦ not_not.1 fun hx ↦ hne ⟨x, hx⟩)
    obtain ⟨j, hj⟩ := hcov x
    exact ⟨j, fun _ ↦ ⟨x, hj, hx⟩⟩
  choose f hf using hsep
  obtain ⟨j, hj⟩ := hdir.finset_le ((hS.prod hS).toFinset.image fun p ↦ f p.1 p.2)
  refine ⟨j, fun W₁ h₁ W₂ h₂ h12 ↦ ?_⟩
  by_contra hne
  obtain ⟨x, hxE, hx⟩ := hf W₁ W₂ hne
  have hle : E (f W₁ W₂) ≤ E j :=
    hj _ (Finset.mem_image.2 ⟨(W₁, W₂), by simp [h₁, h₂], rfl⟩)
  have hmem (W : ValuationSubring L) : x ∈ W ↔ (⟨x, hle hxE⟩ : E j) ∈ W.comap (E j).subtype :=
    Iff.rfl
  apply hx
  rw [hmem, hmem]
  exact Iff.of_eq (congrArg (fun V : ValuationSubring (E j) ↦ (⟨x, hle hxE⟩ : E j) ∈ V) h12)

/-- Unique extension passes up towers: if `O_v` is the only extension to `Ω` of `O_v ∩ K₀`, it is
the only extension of `O_v ∩ K` for every intermediate `K₀ ⊆ K ⊆ Ω` (so the hypothesis `huniq`
of D3b over a finite extension `K'` reduces to the henselian base field `K₀`). -/
lemma eq_of_comap_eq_of_tower {K₀ K Ω : Type*} [Field K₀] [Field K] [Field Ω] [Algebra K₀ K]
    [Algebra K Ω] [Algebra K₀ Ω] [IsScalarTower K₀ K Ω] {O : ValuationSubring Ω}
    (huniq : ∀ V : ValuationSubring Ω, V.comap (algebraMap K₀ Ω) = O.comap (algebraMap K₀ Ω) →
      V = O)
    (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O.comap (algebraMap K Ω)) :
    V = O := by
  refine huniq V ?_
  rw [IsScalarTower.algebraMap_eq K₀ K Ω, ← ValuationSubring.comap_comap,
    ← ValuationSubring.comap_comap, hV]

/-- **Unique extension over a complete base** (C3): over a complete non-archimedean field `K`,
two valuation subrings of an algebraic extension `Ω` lying over the unit ball of `K` coincide. This
discharges the hypothesis `huniq` of D3b when the base is complete. -/
theorem eq_of_comap_eq_of_completeSpace {K Ω : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    {V₁ V₂ : ValuationSubring Ω}
    (h₁ : V₁.comap (algebraMap K Ω) = (NormedField.valuation (K := K)).valuationSubring)
    (h₂ : V₂.comap (algebraMap K Ω) = (NormedField.valuation (K := K)).valuationSubring) :
    V₁ = V₂ := by
  have hext (V : ValuationSubring Ω)
      (h : V.comap (algebraMap K Ω) = (NormedField.valuation (K := K)).valuationSubring) :
      (NormedField.valuation (K := K)).HasExtension V.valuation := by
    refine ⟨(Valuation.isEquiv_iff_valuationSubring _ _).2 ?_⟩
    rw [← h]
    ext x
    simp [ValuationSubring.valuation_le_one_iff]
  haveI := hext V₁ h₁
  haveI := hext V₂ h₂
  have := UniqueExtension.valuationSubring_eq (K := K) V₁.valuation V₂.valuation
  rwa [ValuationSubring.valuationSubring_valuation, ValuationSubring.valuationSubring_valuation]
    at this

/-! ### D3b + D3c: bijection of vertex sets after enlarging the field -/

section Bijection

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation Ω Γ₀} {L : Type*} [Field L] [Algebra (RatFunc Ω) L] [Algebra Ω L]
  [IsScalarTower Ω (RatFunc Ω) L] [Algebra.IsAlgebraic (RatFunc Ω) L]
  {J : Type*} [Nonempty J] {K : J → Type*} [∀ j, Field (K j)] [∀ j, Algebra (K j) Ω]
  {E : J → Subfield L} [∀ j, Algebra (RatFunc (K j)) (E j)] [∀ j, Algebra (K j) (E j)]
  [∀ j, IsScalarTower (K j) (RatFunc (K j)) (E j)]
  [∀ j, Algebra.IsAlgebraic (RatFunc (K j)) (E j)] {ι : Type*} [Fintype ι]

/-- **(W9, D3b + D3c) The vertex sets over `Ω` and over a large enough subfield are in bijection.**
Let `K j ⊆ Ω` (`Ω/K j` algebraic, `O_v` the only extension of `O_v ∩ K j` to `Ω`) and subfields
`E j ⊆ L` with compatible structures `K j(X) → E j`, the `E j` directed with union `L` (e.g.
`E j = L' · K j` for finite `K j`). Given Gauss data `a, c` over `Ω` descending to every `K j`
and a finite vertex set over `Ω` (W4), for some `j` restriction to `E j` is a bijection from the
vertex set of the normalization in `L` of the tree model over `O_v` onto the vertex set of the
normalization in `E j` of the tree model over `O_v ∩ K j`. -/
theorem exists_vertexSet_bijOn [∀ j, Algebra.IsAlgebraic (K j) Ω]
    (hE : ∀ j x, ((algebraMap (RatFunc (K j)) (E j) x : E j) : L) =
      algebraMap (RatFunc Ω) L (ratFuncMap (algebraMap (K j) Ω) x))
    (hdir : Directed (· ≤ ·) E) (hcov : ∀ x, ∃ j, x ∈ E j)
    (huniq : ∀ j, ∀ V : ValuationSubring Ω, V.comap (algebraMap (K j) Ω) =
      v.valuationSubring.comap (algebraMap (K j) Ω) → V = v.valuationSubring)
    {a c : ι → Ω} {r : ι → Γ₀ˣ} (hc : ∀ i, v (c i) = r i) (a' c' : ∀ j, ι → K j)
    (ha : ∀ j i, algebraMap (K j) Ω (a' j i) = a i)
    (hc' : ∀ j i, algebraMap (K j) Ω (c' j i) = c i)
    (hfin : ((gaussJoinModel v a c).normalization L).vertexSet.Finite) :
    ∃ j, Set.BijOn (fun W : ValuationSubring L ↦ W.comap (E j).subtype)
      ((gaussJoinModel v a c).normalization L).vertexSet
      ((gaussJoinModel (v.comap (algebraMap (K j) Ω)) (a' j) (c' j)).normalization
        (E j)).vertexSet := by
  obtain ⟨j, hj⟩ := exists_injOn_comap E hdir hcov hfin
  have hcj (i : ι) : v (algebraMap (K j) Ω (c' j i)) = r i := by rw [hc' j i]; exact hc i
  obtain rfl : a = fun i ↦ algebraMap (K j) Ω (a' j i) := funext fun i ↦ (ha j i).symm
  obtain rfl : c = fun i ↦ algebraMap (K j) Ω (c' j i) := funext fun i ↦ (hc' j i).symm
  exact ⟨j, vertexSet_mapsTo (χ := (E j).subtype) (hE j) hcj, hj,
    vertexSet_surjOn (χ := (E j).subtype) (hE j) (huniq j) hcj⟩

end Bijection

end SemistableReduction
