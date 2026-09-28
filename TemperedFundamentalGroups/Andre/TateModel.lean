/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.ProjPoints
import TemperedFundamentalGroups.Andre.TateCovering

/-!
# A projective model of a Tate curve whose special fibre contains a cycle

Let `O` be a local ring (in the application a valuation ring of a valued field `K`), `π ∈ O` a
non-unit and `b₄, b₆ ∈ O`. Consider the Weierstrass curve
`E : y² + xy = x³ + a₄ x + a₆` with `a₄ = π² b₄`, `a₆ = π² b₆` (split multiplicative reduction of
type `I_n`, `n ≥ 2`). In the coordinates `[u : v : w] = [x : y : π z]` (the second factor of the
blow-up of the Weierstrass model along the ideal `(x, y, π)` of the node of its special fibre),
the equation of `E` divided by `π³` becomes the cubic
`F = v² w + u v w - π u³ - π b₄ u w² - b₆ w³ ∈ O[u, v, w]`.
Modulo `π`, `F = w · G` with the conic `G = v² + u v - b₆ w²`. So the special fibre of the
model `V(F) ⊆ ℙ²_O` is the union of the line `C = {w = 0}` (the strict transform of the nodal
cubic) and the conic `E' = {G = 0}` (the exceptional curve), which meet in the two points
`p = [1 : 0 : 0]` and `q = [1 : -1 : 0]` (the two tangent directions `y = 0`, `y = -x` of the
node).

## Main definitions and results

* `TateModel.model π b₄ b₆ : ModelCode O`: the reduced closed subscheme of `ℙ²_O` with underlying
  set `V(F)` (`TateModel.range_ι`). (Since `F` is not divisible by `π` and `F mod π` is
  reduced, this is the subscheme `V(F)` itself; this is not needed here.)
* `TateModel.Z`: its special fibre; `TateModel.decomp : TateCovering.Decomp Z`: the decomposition
  `Z = C ∪ E'`, `C ∩ E' = Cp ⊔ Cq` into closed sets, with `Cp = {p}` and `Cq = {q}`
  (`TateModel.Cp_eq`, `TateModel.Cq_eq`), `p ≠ q`, `C` irreducible and `E'` connected
  (`TateModel.isPreconnected_C`, `TateModel.isPreconnected_E`).
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace TemperedFundamentalGroups

namespace TateModel

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) O
local notation "𝔪" => IsLocalRing.maximalIdeal O
local notation "k" => IsLocalRing.ResidueField O

variable (π b₄ b₆ : O)

/-- The cubic `F = v² w + u v w - π u³ - π b₄ u w² - b₆ w³`. -/
def F : MvPolynomial (Fin (2 + 1)) O :=
  X 1 ^ 2 * X 2 + X 0 * X 1 * X 2 - C π * X 0 ^ 3 - C (π * b₄) * X 0 * X 2 ^ 2 - C b₆ * X 2 ^ 3

/-- The conic `G = v² + u v - b₆ w²`. -/
def G : MvPolynomial (Fin (2 + 1)) O := X 1 ^ 2 + X 0 * X 1 - C b₆ * X 2 ^ 2

lemma F_eq : F π b₄ b₆ = X 2 * G b₆ - C π * (X 0 ^ 3 + C b₄ * X 0 * X 2 ^ 2) := by
  simp only [F, G, map_mul]
  ring

lemma G_eq : G b₆ = X 1 * (X 0 + X 1) - C b₆ * X 2 ^ 2 := by
  simp only [G]
  ring

/-- The closed subset `V(F)` of `ℙ²_O`. -/
def cubicSet : TopologicalSpace.Closeds (Proj 𝒜) :=
  ⟨(↑(Proj.basicOpen 𝒜 (F π b₄ b₆)) : Set (Proj 𝒜))ᶜ,
    (Proj.basicOpen 𝒜 (F π b₄ b₆)).isOpen.isClosed_compl⟩

/-- The ideal sheaf of the model: the vanishing ideal of `V(F)`. -/
def modelIdeal : (projSpace O 2).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (X := projSpace O 2) (cubicSet π b₄ b₆)

/-- **The model**: the reduced closed subscheme of `ℙ²_O` supported on `V(F)`. -/
def model : ModelCode O where
  m := 2
  I := modelIdeal π b₄ b₆

/-- The closed immersion of the model into `ℙ²_O`. -/
abbrev ι : (modelIdeal π b₄ b₆).subscheme ⟶ projSpace O 2 := (modelIdeal π b₄ b₆).subschemeι

lemma range_ι : Set.range (ι π b₄ b₆) = {y | F π b₄ b₆ ∈ y.asHomogeneousIdeal} := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  ext y
  exact not_not

lemma F_mem (z : (modelIdeal π b₄ b₆).subscheme) :
    F π b₄ b₆ ∈ (ι π b₄ b₆ z).asHomogeneousIdeal := by
  have : ι π b₄ b₆ z ∈ Set.range (ι π b₄ b₆) := ⟨z, rfl⟩
  rwa [range_ι] at this

lemma toSpec_eq : (model π b₄ b₆).toSpec = ι π b₄ b₆ ≫ projSpace.toSpec O 2 := rfl

lemma not_all_X_mem (y : projSpace O 2) (h0 : X 0 ∈ y.asHomogeneousIdeal)
    (h1 : X 1 ∈ y.asHomogeneousIdeal) (h2 : X 2 ∈ y.asHomogeneousIdeal) : False := by
  obtain ⟨i, hi⟩ := exists_X_notMem y
  fin_cases i
  exacts [hi h0, hi h1, hi h2]

variable [IsLocalRing O]

/-- The special fibre of the model. -/
abbrev Z : Type u := specialFibre (model π b₄ b₆).toSpec

/-- The special fibre of the model, as a subspace of `ℙ²_O`. -/
def ιZ (z : Z π b₄ b₆) : projSpace O 2 := ι π b₄ b₆ z.1

lemma isEmbedding_ιZ : Topology.IsEmbedding (ιZ π b₄ b₆) :=
  (ι π b₄ b₆).isEmbedding.comp Topology.IsEmbedding.subtypeVal

lemma mem_Z_iff (z : (modelIdeal π b₄ b₆).subscheme) :
    z ∈ specialFibre (model π b₄ b₆).toSpec ↔
      ∀ c ∈ 𝔪, C c ∈ (ι π b₄ b₆ z).asHomogeneousIdeal := by
  rw [← mem_specialFibre_projSpace_iff]
  rfl

lemma C_mem (z : Z π b₄ b₆) {c : O} (hc : c ∈ 𝔪) : C c ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal :=
  (mem_Z_iff π b₄ b₆ z.1).1 z.2 c hc

variable {π b₄ b₆} in
/-- A point of `V(F)` in the special fibre of `ℙ²_O` is a point of `Z`. -/
lemma exists_ιZ_eq {y : projSpace O 2} (hF : F π b₄ b₆ ∈ y.asHomogeneousIdeal)
    (hy : ∀ c ∈ 𝔪, C c ∈ y.asHomogeneousIdeal) : ∃ z : Z π b₄ b₆, ιZ π b₄ b₆ z = y := by
  have : y ∈ Set.range (ι π b₄ b₆) := by
    rw [range_ι]
    exact hF
  obtain ⟨z, rfl⟩ := this
  exact ⟨⟨z, (mem_Z_iff π b₄ b₆ z).2 hy⟩, rfl⟩

lemma isClosed_setOf_mem (g : MvPolynomial (Fin (2 + 1)) O) :
    IsClosed {z : Z π b₄ b₆ | g ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal} := by
  have : {z : Z π b₄ b₆ | g ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal} =
      ιZ π b₄ b₆ ⁻¹' (↑(Proj.basicOpen 𝒜 g) : Set (Proj 𝒜))ᶜ := by
    ext z
    exact not_not.symm
  rw [this]
  exact (Proj.basicOpen 𝒜 g).isOpen.isClosed_compl.preimage
    (isEmbedding_ιZ π b₄ b₆).continuous

/-! ### The decomposition of the special fibre -/

variable {π b₄ b₆}

lemma X_or_G_mem (hπ : π ∈ 𝔪) (z : Z π b₄ b₆) :
    X 2 ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal ∨ G b₆ ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal := by
  have hp := (ιZ π b₄ b₆ z).isPrime
  apply hp.mem_or_mem
  have h1 : X 2 * G b₆ = F π b₄ b₆ + C π * (X 0 ^ 3 + C b₄ * X 0 * X 2 ^ 2) := by
    rw [F_eq]
    ring
  rw [h1]
  exact Ideal.add_mem _ (F_mem π b₄ b₆ z.1) (Ideal.mul_mem_right _ _ (C_mem π b₄ b₆ z hπ))

variable (π b₄ b₆) in
/-- The strict transform `C = {w = 0}` of the nodal cubic. -/
def Cset : Set (Z π b₄ b₆) := {z | X 2 ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal}

variable (π b₄ b₆) in
/-- The exceptional conic `E' = {G = 0}`. -/
def Eset : Set (Z π b₄ b₆) := {z | G b₆ ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal}

variable (π b₄ b₆) in
/-- The part of `C ∩ E'` on `v = 0` (the point `p = [1 : 0 : 0]`). -/
def Cp : Set (Z π b₄ b₆) :=
  {z | X 2 ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal ∧ X 1 ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal}

variable (π b₄ b₆) in
/-- The part of `C ∩ E'` on `u + v = 0` (the point `q = [1 : -1 : 0]`). -/
def Cq : Set (Z π b₄ b₆) :=
  {z | X 2 ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal ∧
    X 0 + X 1 ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal}

/-- **The special fibre is a line and a conic meeting in two places.** -/
def decomp (hπ : π ∈ 𝔪) : TateCovering.Decomp (Z π b₄ b₆) where
  C := Cset π b₄ b₆
  E := Eset π b₄ b₆
  Cp := Cp π b₄ b₆
  Cq := Cq π b₄ b₆
  isClosed_C := isClosed_setOf_mem π b₄ b₆ _
  isClosed_E := isClosed_setOf_mem π b₄ b₆ _
  isClosed_Cp := (isClosed_setOf_mem π b₄ b₆ _).inter (isClosed_setOf_mem π b₄ b₆ _)
  isClosed_Cq := (isClosed_setOf_mem π b₄ b₆ _).inter (isClosed_setOf_mem π b₄ b₆ _)
  union := Set.eq_univ_of_forall fun z => X_or_G_mem hπ z
  inter := by
    ext z
    have hp := (ιZ π b₄ b₆ z).isPrime
    simp only [Cset, Eset, Cp, Cq, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h2, hG⟩
      rw [G_eq] at hG
      have : X 1 * (X 0 + X 1) ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal := by
        rw [← sub_add_cancel (X 1 * (X 0 + X 1)) (C b₆ * X 2 ^ 2)]
        exact Ideal.add_mem _ hG (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h2 2 two_pos))
      rcases hp.mem_or_mem this with h | h
      exacts [Or.inl ⟨h2, h⟩, Or.inr ⟨h2, h⟩]
    · rintro (⟨h2, h⟩ | ⟨h2, h⟩) <;> refine ⟨h2, ?_⟩ <;> rw [G_eq] <;>
        refine Ideal.sub_mem _ ?_ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h2 2 two_pos))
      exacts [Ideal.mul_mem_right _ _ h, Ideal.mul_mem_left _ _ h]
  disjoint := by
    rw [Set.disjoint_left]
    rintro z ⟨h2, h1⟩ ⟨-, h01⟩
    refine not_all_X_mem _ ?_ h1 h2
    have := Ideal.sub_mem _ h01 h1
    rwa [add_sub_cancel_right] at this

/-! ### The points `p` and `q` -/

/-- The evaluation `θ_g = eval₂ (C ∘ residue) g`, a map to polynomials over the residue field. -/
abbrev θ {τ : Type*} (g : Fin (2 + 1) → MvPolynomial τ k) :
    MvPolynomial (Fin (2 + 1)) O →+* MvPolynomial τ k :=
  eval₂Hom (C.comp (IsLocalRing.residue O)) g

lemma θ_homogeneousComponent {τ : Type*} (g : Fin (2 + 1) → MvPolynomial τ k) {e : ℕ}
    (he : 0 < e) (hg : ∀ i, (g i).IsHomogeneous e) (h : MvPolynomial (Fin (2 + 1)) O)
    (hh : θ g h = 0) (n : ℕ) : θ g (homogeneousComponent n h) = 0 :=
  eval₂Hom_homogeneousComponent_eq_zero _ g he hg hh n

lemma θ_C {τ : Type*} (g : Fin (2 + 1) → MvPolynomial τ k) {c : O} (hc : c ∈ 𝔪) :
    θ g (C c) = 0 := by
  simp [(IsLocalRing.residue_eq_zero_iff c).2 hc]

variable (O) in
/-- The line `[t : 0 : 0]` (the point `p`). -/
def gp : Fin (2 + 1) → MvPolynomial (Fin (0 + 1)) k := ![X 0, 0, 0]

variable (O) in
/-- The line `[t : -t : 0]` (the point `q`). -/
def gq : Fin (2 + 1) → MvPolynomial (Fin (0 + 1)) k := ![X 0, -X 0, 0]

lemma gp_hom (i : Fin (2 + 1)) : (gp O i).IsHomogeneous 1 := by
  fin_cases i
  exacts [isHomogeneous_X _ _, isHomogeneous_zero _ _ _, isHomogeneous_zero _ _ _]

lemma gq_hom (i : Fin (2 + 1)) : (gq O i).IsHomogeneous 1 := by
  fin_cases i
  exacts [isHomogeneous_X _ _, (isHomogeneous_X _ _).neg, isHomogeneous_zero _ _ _]

variable (O) in
/-- The point `p = [1 : 0 : 0]` of `ℙ²` over the residue field. -/
def pointP : projSpace O 2 :=
  projPointOfKer (θ (gp O)) (θ_homogeneousComponent _ one_pos gp_hom) 0 (by simp [gp])

variable (O) in
/-- The point `q = [1 : -1 : 0]` of `ℙ²` over the residue field. -/
def pointQ : projSpace O 2 :=
  projPointOfKer (θ (gq O)) (θ_homogeneousComponent _ one_pos gq_hom) 0 (by simp [gq])

lemma mem_pointP {h : MvPolynomial (Fin (2 + 1)) O} :
    h ∈ (pointP O).asHomogeneousIdeal ↔ θ (gp O) h = 0 :=
  Iff.rfl

lemma mem_pointQ {h : MvPolynomial (Fin (2 + 1)) O} :
    h ∈ (pointQ O).asHomogeneousIdeal ↔ θ (gq O) h = 0 :=
  Iff.rfl

lemma F_mem_pointP (hπ : π ∈ 𝔪) : F π b₄ b₆ ∈ (pointP O).asHomogeneousIdeal := by
  simp [mem_pointP, F, gp, (IsLocalRing.residue_eq_zero_iff π).2 hπ]

lemma F_mem_pointQ (hπ : π ∈ 𝔪) : F π b₄ b₆ ∈ (pointQ O).asHomogeneousIdeal := by
  simp [mem_pointQ, F, gq, (IsLocalRing.residue_eq_zero_iff π).2 hπ]

variable (π b₄ b₆) in
/-- The point `p` of the special fibre. -/
def pZ (hπ : π ∈ 𝔪) : Z π b₄ b₆ :=
  (exists_ιZ_eq (F_mem_pointP (b₄ := b₄) (b₆ := b₆) hπ) fun _ hc => θ_C _ hc).choose

lemma ιZ_pZ (hπ : π ∈ 𝔪) : ιZ π b₄ b₆ (pZ π b₄ b₆ hπ) = pointP O :=
  (exists_ιZ_eq (F_mem_pointP (b₄ := b₄) (b₆ := b₆) hπ) fun _ hc => θ_C _ hc).choose_spec

variable (π b₄ b₆) in
/-- The point `q` of the special fibre. -/
def qZ (hπ : π ∈ 𝔪) : Z π b₄ b₆ :=
  (exists_ιZ_eq (F_mem_pointQ (b₄ := b₄) (b₆ := b₆) hπ) fun _ hc => θ_C _ hc).choose

lemma ιZ_qZ (hπ : π ∈ 𝔪) : ιZ π b₄ b₆ (qZ π b₄ b₆ hπ) = pointQ O :=
  (exists_ιZ_eq (F_mem_pointQ (b₄ := b₄) (b₆ := b₆) hπ) fun _ hc => θ_C _ hc).choose_spec

omit [IsLocalRing O] in
lemma X0_notMem {y : projSpace O 2} (h1 : X 0 + X 1 ∈ y.asHomogeneousIdeal ∨
    X 1 ∈ y.asHomogeneousIdeal) (h2 : X 2 ∈ y.asHomogeneousIdeal) :
    Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (X 0) ≠ 0 := by
  intro h0
  rw [Ideal.Quotient.eq_zero_iff_mem] at h0
  refine not_all_X_mem y h0 ?_ h2
  rcases h1 with h1 | h1
  · have := Ideal.sub_mem _ h1 h0
    rwa [add_sub_cancel_left] at this
  · exact h1

/-- `C ∩ E'` on `v = 0` is the single point `p`. -/
lemma Cp_eq (hπ : π ∈ 𝔪) : Cp π b₄ b₆ = {pZ π b₄ b₆ hπ} := by
  ext z
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨h2, h1⟩
    apply (isEmbedding_ιZ π b₄ b₆).injective
    rw [ιZ_pZ]
    refine eq_projPointOfKer_of_line (ιZ π b₄ b₆ z) (fun c hc => C_mem π b₄ b₆ z hc) _ gp_hom
      _ 0 _ _ (X0_notMem (Or.inr h1) h2) fun i => ?_
    fin_cases i
    · simp [gp]
    · simpa [gp] using (Ideal.Quotient.eq_zero_iff_mem.2 h1).symm
    · simpa [gp] using (Ideal.Quotient.eq_zero_iff_mem.2 h2).symm
  · rintro rfl
    change X 2 ∈ (ιZ π b₄ b₆ (pZ π b₄ b₆ hπ)).asHomogeneousIdeal ∧
      X 1 ∈ (ιZ π b₄ b₆ (pZ π b₄ b₆ hπ)).asHomogeneousIdeal
    rw [ιZ_pZ, mem_pointP, mem_pointP]
    simp [gp]

/-- `C ∩ E'` on `u + v = 0` is the single point `q`. -/
lemma Cq_eq (hπ : π ∈ 𝔪) : Cq π b₄ b₆ = {qZ π b₄ b₆ hπ} := by
  ext z
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨h2, h1⟩
    apply (isEmbedding_ιZ π b₄ b₆).injective
    rw [ιZ_qZ]
    refine eq_projPointOfKer_of_line (ιZ π b₄ b₆ z) (fun c hc => C_mem π b₄ b₆ z hc) _ gq_hom
      _ 0 _ _ (X0_notMem (Or.inl h1) h2) fun i => ?_
    fin_cases i
    · simp [gq]
    · have := Ideal.Quotient.eq_zero_iff_mem.2 h1
      rw [map_add] at this
      simpa [gq] using neg_eq_of_add_eq_zero_right this
    · simpa [gq] using (Ideal.Quotient.eq_zero_iff_mem.2 h2).symm
  · rintro rfl
    change X 2 ∈ (ιZ π b₄ b₆ (qZ π b₄ b₆ hπ)).asHomogeneousIdeal ∧
      X 0 + X 1 ∈ (ιZ π b₄ b₆ (qZ π b₄ b₆ hπ)).asHomogeneousIdeal
    rw [ιZ_qZ, mem_pointQ, mem_pointQ]
    simp [gq]

lemma pZ_ne_qZ (hπ : π ∈ 𝔪) : pZ π b₄ b₆ hπ ≠ qZ π b₄ b₆ hπ := by
  intro h
  have h1 : X 1 ∈ (ιZ π b₄ b₆ (pZ π b₄ b₆ hπ)).asHomogeneousIdeal := by
    rw [ιZ_pZ, mem_pointP]
    simp [gp]
  rw [h, ιZ_qZ, mem_pointQ] at h1
  simp [gq] at h1

/-! ### Connectedness of the two components -/

lemma isPreconnected_of_image_eq {s : Set (Z π b₄ b₆)} {T : Set (projSpace O 2)}
    (hT : _root_.IsPreconnected T) (h : ιZ π b₄ b₆ '' s = T) : _root_.IsPreconnected s := by
  rw [← (isEmbedding_ιZ π b₄ b₆).isInducing.isPreconnected_image, h]
  exact hT

/-- A point `y` of `ℙ²_O` containing `ker θ_g`, for `θ_g` killing `F` and the maximal ideal, is a
point of `Z`. -/
lemma exists_ιZ_eq_of_le {τ : Type*} {g : Fin (2 + 1) → MvPolynomial τ k}
    (hF : θ g (F π b₄ b₆) = 0) {y : projSpace O 2}
    (hy : ∀ h, θ g h = 0 → h ∈ y.asHomogeneousIdeal) : ∃ z : Z π b₄ b₆, ιZ π b₄ b₆ z = y :=
  exists_ιZ_eq (hy _ hF) fun _ hc => hy _ (θ_C g hc)

variable (O) in
/-- The line `w = 0`. -/
def gC : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k := ![X 0, X 1, 0]

lemma gC_hom (i : Fin (2 + 1)) : (gC O i).IsHomogeneous 1 := by
  fin_cases i
  exacts [isHomogeneous_X _ _, isHomogeneous_X _ _, isHomogeneous_zero _ _ _]

variable (O) in
/-- The generic point of the line `C = {w = 0}`. -/
def pointC : projSpace O 2 :=
  projPointOfKer (θ (gC O)) (θ_homogeneousComponent _ one_pos gC_hom) 0 (by simp [gC])

lemma mem_Cset_iff (z : Z π b₄ b₆) : z ∈ Cset π b₄ b₆ ↔
    (pointC O).asHomogeneousIdeal ≤ (ιZ π b₄ b₆ z).asHomogeneousIdeal := by
  constructor
  · intro h2 h hh
    refine mem_of_eval₂Hom_eq_zero (ιZ π b₄ b₆ z) (fun c hc => C_mem π b₄ b₆ z hc) (gC O)
      one_pos gC_hom (fun i => Ideal.Quotient.mk _ (X i)) 1 one_ne_zero (fun i => ?_) hh
    fin_cases i
    · simp [gC]
    · simp [gC]
    · simpa [gC] using (Ideal.Quotient.eq_zero_iff_mem.2 h2).symm
  · intro h
    exact h (by simp [gC] : θ (gC O) (X 2) = 0)

/-- **The line `C` is irreducible**, in particular preconnected. -/
lemma isPreconnected_C (hπ : π ∈ 𝔪) : _root_.IsPreconnected (Cset π b₄ b₆) := by
  refine isPreconnected_of_image_eq (isPreconnected_setOf_le (pointC O)) ?_
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_Cset_iff z).1 hz
  · intro hy
    obtain ⟨z, rfl⟩ := exists_ιZ_eq_of_le (g := gC O) (π := π) (b₄ := b₄) (b₆ := b₆)
      (by simp [F, gC, (IsLocalRing.residue_eq_zero_iff π).2 hπ]) hy
    exact ⟨z, (mem_Cset_iff z).2 hy, rfl⟩

/-! #### The conic when `b₆` is a unit: a smooth conic -/

variable (b₆) in
/-- The parametrization `[s : t] ↦ [b₆ s² - t² : t² : s t]` of the conic `G = 0`. -/
def gE : Fin (2 + 1) → MvPolynomial (Fin (1 + 1)) k :=
  ![C (IsLocalRing.residue O b₆) * X 0 ^ 2 - X 1 ^ 2, X 1 ^ 2, X 0 * X 1]

lemma gE_hom (i : Fin (2 + 1)) : (gE b₆ i).IsHomogeneous 2 := by
  fin_cases i
  · exact (isHomogeneous_C_mul_X_pow _ _ _).sub (isHomogeneous_X_pow _ _)
  · exact isHomogeneous_X_pow _ _
  · exact (isHomogeneous_X _ _).mul (isHomogeneous_X _ _)

variable (b₆) in
/-- The generic point of the conic `E'`, when `b₆` is a unit. -/
def pointE : projSpace O 2 :=
  projPointOfKer (θ (gE b₆)) (θ_homogeneousComponent _ two_pos gE_hom) 1 (by simp [gE])

lemma θ_gE_G : θ (gE b₆) (G b₆) = 0 := by
  simp only [G, gE, map_sub, map_add, map_mul, map_pow, eval₂Hom_X', eval₂Hom_C,
    RingHom.coe_comp, Function.comp_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

omit [IsLocalRing O] in
lemma mk_G {y : projSpace O 2} (hG : G b₆ ∈ y.asHomogeneousIdeal) :
    Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (X 1) ^ 2 +
      Ideal.Quotient.mk _ (X 0) * Ideal.Quotient.mk _ (X 1) -
      Ideal.Quotient.mk _ (C b₆) * Ideal.Quotient.mk _ (X 2) ^ 2 = 0 := by
  have := Ideal.Quotient.eq_zero_iff_mem.2 hG
  simpa [G] using this

/-- A point of the special fibre on the smooth conic `G = 0` specializes from its generic
point. -/
lemma pointE_le (hb : IsUnit b₆) {y : projSpace O 2}
    (hy : ∀ c ∈ 𝔪, C c ∈ y.asHomogeneousIdeal) (hG : G b₆ ∈ y.asHomogeneousIdeal) :
    (pointE b₆).asHomogeneousIdeal ≤ y.asHomogeneousIdeal := by
  intro h hh
  have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  have hrel := mk_G hG
  have hB : IsUnit (Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (C b₆)) :=
    (hb.map C).map _
  have hres : residueLift y hy (IsLocalRing.residue O b₆) =
      Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (C b₆) :=
    residueLift_residue y hy b₆
  by_cases hV : Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (X 1) = 0
  · have hW : Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (X 2) = 0 := by
      rw [hV] at hrel
      have : Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (C b₆) *
          Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (X 2) ^ 2 = 0 := by
        linear_combination -hrel
      exact pow_eq_zero_iff two_ne_zero |>.1 ((hB.mul_right_eq_zero).1 this)
    have hU : Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (X 0) ≠ 0 := fun hU =>
      not_all_X_mem y (Ideal.Quotient.eq_zero_iff_mem.1 hU) (Ideal.Quotient.eq_zero_iff_mem.1 hV)
        (Ideal.Quotient.eq_zero_iff_mem.1 hW)
    refine mem_of_eval₂Hom_eq_zero y hy (gE b₆) two_pos gE_hom
      ![Ideal.Quotient.mk _ (X 0) + Ideal.Quotient.mk _ (X 1),
        Ideal.Quotient.mk _ (C b₆) * Ideal.Quotient.mk _ (X 2)]
      (Ideal.Quotient.mk _ (C b₆) *
        (Ideal.Quotient.mk _ (X 0) + Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (X 1)))
      (mul_ne_zero hB.ne_zero (by rwa [hV, add_zero])) (fun i => ?_) hh
    fin_cases i
    · simp only [gE, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, map_sub, map_mul,
        eval₂Hom_C, hres, map_pow, eval₂Hom_X', Matrix.cons_val_one]
      linear_combination Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (C b₆) * hrel
    · simp [gE]
      linear_combination (-Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal (C b₆)) * hrel
    · simp [gE]
      ring
  · refine mem_of_eval₂Hom_eq_zero y hy (gE b₆) two_pos gE_hom
      ![Ideal.Quotient.mk _ (X 2), Ideal.Quotient.mk _ (X 1)] _ hV (fun i => ?_) hh
    fin_cases i
    · simp only [gE, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, map_sub, map_mul,
        eval₂Hom_C, hres, map_pow, eval₂Hom_X', Matrix.cons_val_one]
      linear_combination (-1 : MvPolynomial (Fin (2 + 1)) O ⧸ y.asHomogeneousIdeal.toIdeal) * hrel
    · simp [gE]
      ring
    · simp [gE]
      ring

lemma mem_Eset_iff_of_isUnit (hb : IsUnit b₆) (z : Z π b₄ b₆) : z ∈ Eset π b₄ b₆ ↔
    (pointE b₆).asHomogeneousIdeal ≤ (ιZ π b₄ b₆ z).asHomogeneousIdeal :=
  ⟨pointE_le hb fun _ hc => C_mem π b₄ b₆ z hc, fun h => h θ_gE_G⟩

/-! #### The conic when `b₆ ∈ 𝔪`: two lines through `[0 : 0 : 1]` -/

variable (O) in
/-- The line `v = 0`. -/
def gL₁ : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k := ![X 0, 0, X 2]

variable (O) in
/-- The line `u + v = 0`. -/
def gL₂ : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k := ![X 0, -X 0, X 2]

variable (O) in
/-- The point `[0 : 0 : 1]`. -/
def gN : Fin (2 + 1) → MvPolynomial (Fin (0 + 1)) k := ![0, 0, X 0]

lemma gL₁_hom (i : Fin (2 + 1)) : (gL₁ O i).IsHomogeneous 1 := by
  fin_cases i
  exacts [isHomogeneous_X _ _, isHomogeneous_zero _ _ _, isHomogeneous_X _ _]

lemma gL₂_hom (i : Fin (2 + 1)) : (gL₂ O i).IsHomogeneous 1 := by
  fin_cases i
  exacts [isHomogeneous_X _ _, (isHomogeneous_X _ _).neg, isHomogeneous_X _ _]

lemma gN_hom (i : Fin (2 + 1)) : (gN O i).IsHomogeneous 1 := by
  fin_cases i
  exacts [isHomogeneous_zero _ _ _, isHomogeneous_zero _ _ _, isHomogeneous_X _ _]

variable (O) in
/-- The generic point of the line `v = 0`. -/
def pointL₁ : projSpace O 2 :=
  projPointOfKer (θ (gL₁ O)) (θ_homogeneousComponent _ one_pos gL₁_hom) 0 (by simp [gL₁])

variable (O) in
/-- The generic point of the line `u + v = 0`. -/
def pointL₂ : projSpace O 2 :=
  projPointOfKer (θ (gL₂ O)) (θ_homogeneousComponent _ one_pos gL₂_hom) 0 (by simp [gL₂])

variable (O) in
/-- The point `[0 : 0 : 1]` of `ℙ²` over the residue field. -/
def pointN : projSpace O 2 :=
  projPointOfKer (θ (gN O)) (θ_homogeneousComponent _ one_pos gN_hom) 2 (by simp [gN])

lemma pointL₁_le {y : projSpace O 2} (hy : ∀ c ∈ 𝔪, C c ∈ y.asHomogeneousIdeal)
    (h1 : X 1 ∈ y.asHomogeneousIdeal) :
    (pointL₁ O).asHomogeneousIdeal ≤ y.asHomogeneousIdeal := fun _ hh =>
  mem_of_eval₂Hom_eq_zero y hy (gL₁ O) one_pos gL₁_hom (fun i => Ideal.Quotient.mk _ (X i)) 1
    one_ne_zero (fun i => by
      fin_cases i
      · simp [gL₁]
      · simpa [gL₁] using (Ideal.Quotient.eq_zero_iff_mem.2 h1).symm
      · simp [gL₁]) hh

lemma pointL₂_le {y : projSpace O 2} (hy : ∀ c ∈ 𝔪, C c ∈ y.asHomogeneousIdeal)
    (h1 : X 0 + X 1 ∈ y.asHomogeneousIdeal) :
    (pointL₂ O).asHomogeneousIdeal ≤ y.asHomogeneousIdeal := fun _ hh =>
  mem_of_eval₂Hom_eq_zero y hy (gL₂ O) one_pos gL₂_hom (fun i => Ideal.Quotient.mk _ (X i)) 1
    one_ne_zero (fun i => by
      fin_cases i
      · simp [gL₂]
      · have := Ideal.Quotient.eq_zero_iff_mem.2 h1
        rw [map_add] at this
        simpa [gL₂] using neg_eq_of_add_eq_zero_right this
      · simp [gL₂]) hh

lemma mem_Eset_iff_of_mem (hb : b₆ ∈ 𝔪) (z : Z π b₄ b₆) : z ∈ Eset π b₄ b₆ ↔
    ((pointL₁ O).asHomogeneousIdeal ≤ (ιZ π b₄ b₆ z).asHomogeneousIdeal ∨
      (pointL₂ O).asHomogeneousIdeal ≤ (ιZ π b₄ b₆ z).asHomogeneousIdeal) := by
  have hb' := (IsLocalRing.residue_eq_zero_iff b₆).2 hb
  constructor
  · intro hG
    have hp := (ιZ π b₄ b₆ z).isPrime
    have hy : ∀ c ∈ 𝔪, C c ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal := fun c hc => C_mem π b₄ b₆ z hc
    rw [Eset, Set.mem_setOf_eq, G_eq] at hG
    have : X 1 * (X 0 + X 1) ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal := by
      rw [← sub_add_cancel (X 1 * (X 0 + X 1)) (C b₆ * X 2 ^ 2)]
      exact Ideal.add_mem _ hG (Ideal.mul_mem_right _ _ (hy b₆ hb))
    rcases hp.mem_or_mem this with h | h
    exacts [Or.inl (pointL₁_le hy h), Or.inr (pointL₂_le hy h)]
  · rintro (h | h)
    · exact h (by simp [G, gL₁, hb'] : θ (gL₁ O) (G b₆) = 0)
    · exact h (by simp [G, gL₂, hb']; ring : θ (gL₂ O) (G b₆) = 0)

/-- **The conic `E'` is connected.** -/
lemma isPreconnected_E (hπ : π ∈ 𝔪) : _root_.IsPreconnected (Eset π b₄ b₆) := by
  have hπ' := (IsLocalRing.residue_eq_zero_iff π).2 hπ
  by_cases hb : IsUnit b₆
  · refine isPreconnected_of_image_eq (isPreconnected_setOf_le (pointE b₆)) ?_
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (mem_Eset_iff_of_isUnit hb z).1 hz
    · intro hy
      have hF : θ (gE b₆) (F π b₄ b₆) = 0 := by
        rw [F_eq, map_sub, map_mul, θ_gE_G, mul_zero, zero_sub, map_mul, θ_C _ hπ, zero_mul,
          neg_zero]
      obtain ⟨z, rfl⟩ := exists_ιZ_eq_of_le hF hy
      exact ⟨z, (mem_Eset_iff_of_isUnit hb z).2 hy, rfl⟩
  · have hb : b₆ ∈ 𝔪 := (IsLocalRing.mem_maximalIdeal b₆).2 hb
    have hb' := (IsLocalRing.residue_eq_zero_iff b₆).2 hb
    have hN : ∀ c ∈ 𝔪, C c ∈ (pointN O).asHomogeneousIdeal := fun c hc => θ_C _ hc
    refine isPreconnected_of_image_eq ((isPreconnected_setOf_le (pointL₁ O)).union (pointN O)
      (pointL₁_le hN (by simp [gN] : θ (gN O) (X 1) = 0))
      (pointL₂_le hN (by simp [gN] : θ (gN O) (X 0 + X 1) = 0))
      (isPreconnected_setOf_le (pointL₂ O))) ?_
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (mem_Eset_iff_of_mem hb z).1 hz
    · rintro (hy | hy)
      · obtain ⟨z, rfl⟩ := exists_ιZ_eq_of_le (π := π) (b₄ := b₄) (b₆ := b₆)
          (by simp [F, gL₁, hπ', hb'] : θ (gL₁ O) (F π b₄ b₆) = 0) hy
        exact ⟨z, (mem_Eset_iff_of_mem hb z).2 (Or.inl hy), rfl⟩
      · obtain ⟨z, rfl⟩ := exists_ιZ_eq_of_le (π := π) (b₄ := b₄) (b₆ := b₆)
          (by simp [F, gL₂, hπ', hb']; ring : θ (gL₂ O) (F π b₄ b₆) = 0) hy
        exact ⟨z, (mem_Eset_iff_of_mem hb z).2 (Or.inr hy), rfl⟩

end

end TateModel

end TemperedFundamentalGroups
