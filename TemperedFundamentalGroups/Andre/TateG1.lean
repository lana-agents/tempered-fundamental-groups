/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateSurjective
import TemperedFundamentalGroups.Andre.Transport

/-!
# Components of members not contracted over the Tate model (G1)

* `TateModel.exists_closure_eq_Cset` **(S2)**: the line `C` of the special fibre of the Tate model
  has a generic point `zC ∉ E'`; `TateModel.exists_closure_eq_Eset`: so has the conic `E'` when
  `b₆` is a unit (`zE ∉ C`). (If `b₆ ∈ 𝔪`, `E'` is the union of two lines and has no generic
  point.)
* `Pres.exists_image_eq_closure`: for a member `P` and a point `z` of the special fibre of `𝒯`
  whose closure together with a closed set avoiding `z` covers it, some component of `P` maps
  onto `closure {z}` (from the surjectivity **(S1)** `Pres.tateMap_surjective`).
* `Pres.exists_image_eq_C`, `Pres.exists_image_eq_E` **(G1)**: some component of `P` maps onto
  `C` (resp. onto `E'`, when `b₆` is a unit), so it is not contracted;
* `Pres.exists_tree_tateNu` **(G1)**, the form used by Theorem B: a component vertex of the tree
  of the universal covering whose component is not contracted over `𝒯`.

Hypotheses: `x` transcendental over `K` (for constant data the claim fails), `O` a discrete
valuation ring, `R` a domain, and `d = X² + 4 (π X³ + π b₄ X + b₆)` squarefree (e.g. `2 ≠ 0` and
`Δ ≠ 0`, `TateNormal.squarefree_dpoly`), which makes `V(F)` irreducible.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial Set

namespace TemperedFundamentalGroups

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace TateModel

variable {O : Type u} [CommRing O] [IsLocalRing O] {π b₄ b₆ : O}

lemma closure_eq_of_ιZ {y : projSpace O 2} {z : Z π b₄ b₆} (hz : ιZ π b₄ b₆ z = y) (w : Z π b₄ b₆) :
    w ∈ closure {z} ↔ y.asHomogeneousIdeal ≤ (ιZ π b₄ b₆ w).asHomogeneousIdeal := by
  rw [← specializes_iff_mem_closure, ← (isEmbedding_ιZ π b₄ b₆).isInducing.specializes_iff,
    specializes_iff_mem_closure, ← hz]
  exact (ProjectiveSpectrum.le_iff_mem_closure _ _ _).symm

/-- **(S2) The generic point of the line `C`**; it does not lie on the conic `E'`. -/
lemma exists_closure_eq_Cset (hπ : π ∈ IsLocalRing.maximalIdeal O) :
    ∃ zC : Z π b₄ b₆, closure {zC} = Cset π b₄ b₆ ∧ zC ∉ Eset π b₄ b₆ := by
  have hπ' := (IsLocalRing.residue_eq_zero_iff π).2 hπ
  obtain ⟨z, hz⟩ := exists_ιZ_eq_of_le (g := gC O) (π := π) (b₄ := b₄) (b₆ := b₆)
    (by simp [F, gC, hπ']) (y := pointC O) fun _ hh => hh
  refine ⟨z, ?_, ?_⟩
  · ext w
    rw [closure_eq_of_ιZ hz, mem_Cset_iff]
  · intro hE
    have h0 : θ (gC O) (G b₆) = 0 := by
      have : G b₆ ∈ (pointC O).asHomogeneousIdeal := hz ▸ hE
      exact this
    have h1 := congrArg (MvPolynomial.eval ![0, 1, 0]) h0
    simp [G, gC] at h1

/-- **(S2) The generic point of the conic `E'`** when `b₆` is a unit; it does not lie on `C`. -/
lemma exists_closure_eq_Eset (hπ : π ∈ IsLocalRing.maximalIdeal O) (hb : IsUnit b₆) :
    ∃ zE : Z π b₄ b₆, closure {zE} = Eset π b₄ b₆ ∧ zE ∉ Cset π b₄ b₆ := by
  have hF : θ (gE b₆) (F π b₄ b₆) = 0 := by
    rw [F_eq, map_sub, map_mul, θ_gE_G, mul_zero, zero_sub, map_mul, θ_C _ hπ, zero_mul,
      neg_zero]
  obtain ⟨z, hz⟩ := exists_ιZ_eq_of_le (g := gE b₆) hF (y := pointE b₆) fun _ hh => hh
  refine ⟨z, ?_, ?_⟩
  · ext w
    rw [closure_eq_of_ιZ hz, mem_Eset_iff_of_isUnit hb]
  · intro hC
    have h0 : θ (gE b₆) (X 2) = 0 := by
      have : X 2 ∈ (pointE b₆).asHomogeneousIdeal := hz ▸ hC
      exact this
    have h1 := congrArg (MvPolynomial.eval ![1, 1]) h0
    simp [gE] at h1

lemma pZ_mem_Cset (hπ : π ∈ IsLocalRing.maximalIdeal O) : pZ π b₄ b₆ hπ ∈ Cset π b₄ b₆ := by
  have : pZ π b₄ b₆ hπ ∈ Cp π b₄ b₆ := by rw [Cp_eq hπ]; rfl
  exact this.1

lemma qZ_mem_Cset (hπ : π ∈ IsLocalRing.maximalIdeal O) : qZ π b₄ b₆ hπ ∈ Cset π b₄ b₆ := by
  have : qZ π b₄ b₆ hπ ∈ Cq π b₄ b₆ := by rw [Cq_eq hπ]; rfl
  exact this.1

lemma pZ_mem_Eset (hπ : π ∈ IsLocalRing.maximalIdeal O) : pZ π b₄ b₆ hπ ∈ Eset π b₄ b₆ := by
  have : pZ π b₄ b₆ hπ ∈ Cp π b₄ b₆ := by rw [Cp_eq hπ]; rfl
  have h := (decomp (π := π) (b₄ := b₄) (b₆ := b₆) hπ).inter
  have : pZ π b₄ b₆ hπ ∈ Cset π b₄ b₆ ∩ Eset π b₄ b₆ := by
    change pZ π b₄ b₆ hπ ∈ (decomp hπ).C ∩ (decomp hπ).E
    rw [h]
    exact Or.inl this
  exact this.2

lemma qZ_mem_Eset (hπ : π ∈ IsLocalRing.maximalIdeal O) : qZ π b₄ b₆ hπ ∈ Eset π b₄ b₆ := by
  have : qZ π b₄ b₆ hπ ∈ Cq π b₄ b₆ := by rw [Cq_eq hπ]; rfl
  have h := (decomp (π := π) (b₄ := b₄) (b₆ := b₆) hπ).inter
  have : qZ π b₄ b₆ hπ ∈ Cset π b₄ b₆ ∩ Eset π b₄ b₆ := by
    change qZ π b₄ b₆ hπ ∈ (decomp hπ).C ∩ (decomp hπ).E
    rw [h]
    exact Or.inr this
  exact this.2

end TateModel

open TempObj CurveConfig

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] {x : R} (T : TateObject.Data O R)

namespace Pres

variable {X : TempObj O R A} (P : Pres x X)

omit [IsReduced R] [Subsingleton A] in
/-- A surjective model map has a component mapping onto `closure {z}`, for `z` whose closure and a
closed set avoiding `z` cover the special fibre (any target object `X₀`). -/
lemma exists_image_eq_closureG {X₀ : TempObj O R A} (a : X ⟶ X₀)
    (hsurj : Function.Surjective (P.tateMapG a)) {z : X₀.Lv.Z} {E₀ : Set X₀.Lv.Z}
    (hE : IsClosed E₀) (hcov : closure {z} ∪ E₀ = univ) (hz : z ∉ E₀) :
    ∃ i : irreducibleComponents P.Lv.Z,
      P.tateMapG a '' (curveConfig P.Lv.Z P.hdim).C i = closure {z} := by
  obtain ⟨w, hw⟩ := hsurj z
  set i := (curveConfig P.Lv.Z P.hdim).comp w
  refine ⟨i, subset_antisymm ?_ ?_⟩
  · have hirr : IsIrreducible (P.tateMapG a '' (curveConfig P.Lv.Z P.hdim).C i) :=
      i.2.1.image _ (continuous_specialFibreMap _ _).continuousOn
    rcases isPreirreducible_iff_isClosed_union_isClosed.1 hirr.isPreirreducible _ _
      isClosed_closure hE (by rw [hcov]; exact subset_univ _) with h | h
    · exact h
    · exact absurd (h ⟨w, (curveConfig P.Lv.Z P.hdim).mem_comp w, hw⟩) hz
  · refine (isClosedMap_specialFibreMap (P.iso.inv ≫ a) _
      ((curveConfig P.Lv.Z P.hdim).isClosed_C i)).closure_subset_iff.2 ?_
    exact singleton_subset_iff.2 ⟨w, (curveConfig P.Lv.Z P.hdim).mem_comp w, hw⟩

/-- A surjective model map has a component mapping onto `closure {z}`, for `z` whose closure and a
closed set avoiding `z` cover the special fibre. -/
lemma exists_image_eq_closure (a : X ⟶ TateObject.X₀ (A := A) T)
    (hsurj : Function.Surjective (P.tateMap T a)) {z : (TateObject.X₀ (A := A) T).Lv.Z}
    {E₀ : Set (TateObject.X₀ (A := A) T).Lv.Z} (hE : IsClosed E₀)
    (hcov : closure {z} ∪ E₀ = univ) (hz : z ∉ E₀) :
    ∃ i : irreducibleComponents P.Lv.Z,
      P.tateMap T a '' (curveConfig P.Lv.Z P.hdim).C i = closure {z} :=
  P.exists_image_eq_closureG a hsurj hE hcov hz

omit [IsReduced R] [Subsingleton A] in
/-- A component mapping onto a set containing two distinct points is not contracted (any target
object `X₀`). -/
lemma not_contr_of_image_eqG {X₀ : TempObj O R A} (a : X ⟶ X₀)
    {i : irreducibleComponents P.Lv.Z} {S : Set X₀.Lv.Z}
    (hi : P.tateMapG a '' (curveConfig P.Lv.Z P.hdim).C i = S) {p q} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) : P.tateNuG a i := by
  rintro ⟨y, hy⟩
  rw [hi] at hy
  rw [hy] at hp hq
  exact hpq (hp.trans hq.symm)

/-- A component mapping onto a set containing two distinct points is not contracted. -/
lemma not_contr_of_image_eq (a : X ⟶ TateObject.X₀ (A := A) T)
    {i : irreducibleComponents P.Lv.Z} {S : Set (TateObject.X₀ (A := A) T).Lv.Z}
    (hi : P.tateMap T a '' (curveConfig P.Lv.Z P.hdim).C i = S) {p q} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) : P.tateNu T a i :=
  P.not_contr_of_image_eqG a hi hp hq hpq

variable [IsDiscreteValuationRing O] [IsDomain R]

/-- **(G1) Some component of a member maps onto the line `C` of the Tate model.** -/
theorem exists_image_eq_C (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))
    (hx : Transcendental K T.x) (a : X ⟶ TateObject.X₀ (A := A) T) :
    ∃ i : irreducibleComponents P.Lv.Z,
      P.tateMap T a '' (curveConfig P.Lv.Z P.hdim).C i = (TateObject.decomp (A := A) T).C ∧
        P.tateNu T a i := by
  obtain ⟨zC, hC, hE⟩ := TateModel.exists_closure_eq_Cset (b₄ := T.b₄) (b₆ := T.b₆) T.π_mem
  have hcov : closure {zC} ∪ (TateObject.decomp (A := A) T).E = univ := by
    rw [hC]
    exact (TateObject.decomp (A := A) T).union
  obtain ⟨i, hi⟩ := P.exists_image_eq_closure T a (P.tateMap_surjective T hd hx a)
    (TateObject.decomp (A := A) T).isClosed_E hcov hE
  replace hi := hi.trans hC
  exact ⟨i, hi, P.not_contr_of_image_eq T a hi (TateModel.pZ_mem_Cset T.π_mem)
    (TateModel.qZ_mem_Cset T.π_mem) (TateModel.pZ_ne_qZ T.π_mem)⟩

/-- **(G1) Some component of a member maps onto the conic `E'` of the Tate model**, when `b₆` is a
unit. -/
theorem exists_image_eq_E (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))
    (hx : Transcendental K T.x) (hb : IsUnit T.b₆) (a : X ⟶ TateObject.X₀ (A := A) T) :
    ∃ i : irreducibleComponents P.Lv.Z,
      P.tateMap T a '' (curveConfig P.Lv.Z P.hdim).C i = (TateObject.decomp (A := A) T).E ∧
        P.tateNu T a i := by
  obtain ⟨zE, hE, hC⟩ := TateModel.exists_closure_eq_Eset (b₄ := T.b₄) T.π_mem hb
  have hcov : closure {zE} ∪ (TateObject.decomp (A := A) T).C = univ := by
    rw [hE, union_comm]
    exact (TateObject.decomp (A := A) T).union
  obtain ⟨i, hi⟩ := P.exists_image_eq_closure T a (P.tateMap_surjective T hd hx a)
    (TateObject.decomp (A := A) T).isClosed_C hcov hC
  replace hi := hi.trans hE
  exact ⟨i, hi, P.not_contr_of_image_eq T a hi (TateModel.pZ_mem_Eset T.π_mem)
    (TateModel.qZ_mem_Eset T.π_mem) (TateModel.pZ_ne_qZ T.π_mem)⟩

omit [IsReduced R] [Subsingleton A] [IsDiscreteValuationRing O] [IsDomain R] in
/-- Every component is the label of a component vertex of the tree of the universal covering. -/
lemma exists_tree_lab_eq (i : irreducibleComponents P.Lv.Z) :
    ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
      IsComp t₁ ∧ lab t₁ = i := by
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
    exact ⟨e.1.2, ⟨j, hj⟩, (lab_of hj).trans hji⟩
  · have h1 := Cover.eq_of_inr hs
    have h2 := mem_S_of_head hs
    rw [← h1, he'] at h2
    exact absurd h2 hS

/-- **(G1), tree form**: a component vertex of the tree of the universal covering of a member
whose component is not contracted over the Tate model. -/
theorem exists_tree_tateNu (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))
    (hx : Transcendental K T.x) (a : X ⟶ TateObject.X₀ (A := A) T) :
    ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
      IsComp t₁ ∧ P.tateNu T a (lab t₁) := by
  obtain ⟨i, -, hi⟩ := P.exists_image_eq_C T hd hx a
  obtain ⟨t₁, ht, hl⟩ := P.exists_tree_lab_eq i
  exact ⟨t₁, ht, hl ▸ hi⟩

/-- **(G1), tree form**, for `2 ≠ 0` and nonzero discriminant `Δ = -π² E` of the Tate curve. -/
theorem exists_tree_tateNu_of_tateDisc (h2 : (2 : O) ≠ 0)
    (hΔ : TateNormal.tateDisc T.π T.b₄ T.b₆ ≠ 0) (hx : Transcendental K T.x)
    (a : X ⟶ TateObject.X₀ (A := A) T) :
    ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree (universalCovering.root P.hdim P.z₀),
      IsComp t₁ ∧ P.tateNu T a (lab t₁) :=
  P.exists_tree_tateNu T (TateNormal.squarefree_dpoly _ _ _ h2 hΔ) hx a

end Pres

end

end TemperedFundamentalGroups
