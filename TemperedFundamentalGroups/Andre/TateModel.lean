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

end

end TateModel

end TemperedFundamentalGroups
