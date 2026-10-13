/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TameEstrangement
import TemperedFundamentalGroups.Andre.TateObjectDouble
import TemperedFundamentalGroups.Andre.TheoremBGoodTate
import TemperedFundamentalGroups.SemiAnbd.CharacterEstrangement

/-!
# M4 for Tate curves through the explicit coverings `Y`, `Ÿ` (Blueprint §12.10, E12–E15)

Scheme case, under the hypotheses of Theorem A, for Tate data `D` on `R` (`TateObject.Data`,
`TateObject.DoubleData`). The explicit tempered coverings `Ÿ → Y → X` give the characters
`χ_Y : Π^tp_X → ℤ` (`TateObject.character`, kernel `Π^tp_Y`) and `χ_Ÿ : Π^tp_X → ℤ × ℤ/2`
(`TateObject.character₂`, kernel `Π^tp_Ÿ = piYddot`), transported to André's group along
Theorem A (`andreEquiv'`) as `charY`, `charYY`.

**Which elements matter (E12).** Every pointed object of the tempered category is dominated by a
pointed Galois object over a W-model level (`exists_level_fix`); so `χ_Y` is detected at one
level `q` of André's tower (`charY_eq_one_of_ρ`), where vertex stabilizers are finite
(`UData.finite_stab`). By `TreeTower.eq_one_of_elliptic` (`ℤ` is torsion-free):

* **`charY_eq_one_of_elliptic`**: **every elliptic element of André's tower lies in `Π^tp_Y`**,
  and its square lies in `Π^tp_Ÿ` (`charYY_sq_eq_one_of_elliptic`); in particular every
  nontrivial compact subgroup lies in `Π^tp_Y` (`le_ker_charY_of_isCompact`);
* **`estrangedElt_of_charY_ne_one`** (unconditional): every element with `χ_Y ≠ 1` (nontrivial
  image in the deck group of `Y`) fixes no vertex at `q` and is estranged — no comparison of
  W-models is needed; such elements exist (Theorem B, `exists_estranged_of_goodTate`);
* in the explicit model, the involution of `Ÿ → Y` acts trivially on the covering space of the
  special fibre (`deckHom₂_h_involution`), so it is invisible on the dual graph; the model tower
  (`DihedralLine.yddotTower`) is not estranged (`DihedralLine.not_estranged_yddot`).

**The reduction (E13).** Relative to the explicit Tate coverings, the M4 input is split as

* `TateWildPart Δ`: the nontrivial elliptic elements of `Δ ∩ Π^tp_Ÿ` (acting trivially on the
  fibres of all explicit Tate coverings) are estranged — **the genuinely wild remaining part**;
* `TateInvolutionPart Δ`: the elliptic elements `g ≠ 1` of `Δ` with `g ^ 2 = 1` are estranged
  (implied by `TateWildPart Δ`, since involutions do not move `√c`:
  `tateInvolutionPart_of_tateWildPart`, `Andre/TateInvolution.lean`),

and **`estranged_comap_andreTower_iff_tate`**, **`ellipticEstrangement_iff_tate`**: the
estrangement of André's tower over `Δ` (equivalently `EllipticEstrangement Δ`, the M4 input
relative to the rigid levels) is equivalent to `TateWildPart Δ ∧ TateInvolutionPart Δ`. The
Kummer elements (`χ_Ÿ = (0, 1)`) need no separate hypothesis: their squares lie in `Π^tp_Ÿ`, and
the fixed set of `g` is contained in that of `g²`.

**Comparison (E14).** `TateLevel q`: the kernel of the action on the tree at `q` is `Π^tp_Y`
(what the Tate model at `q` would give; implied by `TateLineLevel q (tateLineHom ∘ χ_Y)`,
`tateLevel_of_tateLineLevel`; not provided by the construction, `curveData` picks arbitrary
W-models). Under it, `TameEstrangement Δ (· = q)` holds (`tameEstrangement_of_tateLevel`) and
**`wildEstrangement_tateLevel_iff`**: M4 for `P = {q}` is `TateWildPart Δ ∧ TateInvolutionPart Δ`
(`wildEstrangement_of_tate`: M4 for Tate ⇐ comparison ∧ remaining wild part).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold DihedralGroup

namespace TemperedFundamentalGroups

noncomputable section

open GaloisLimit TateObject

/-! ### The explicit model: the involution of `Ÿ` is invisible on the special fibre -/

lemma sq_eq_one_zmod2 (ε : Multiplicative (ZMod 2)) : ε ^ 2 = 1 := by
  rcases TateObject.zmod2_cases (Multiplicative.toAdd ε) with h | h <;>
    exact Multiplicative.toAdd.injective (by rw [toAdd_pow, h]; decide)

section Model

variable {K : Type u} [Field K] {O : ValuationSubring K} {R : Type u} [CommRing R] [Algebra K R]
  [IsReduced R] {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  (D : DoubleData O R)

/-- **The involution of `Ÿ → Y` acts trivially on the covering space of the special fibre**
(hence on its dual graph, the line): only the `ℤ`-component of `ℤ × ℤ/2` moves the chain of
components. -/
lemma deckHom₂_h_involution (ε : Multiplicative (ZMod 2)) :
    ((deckHom₂ (A := A) D (1, ε)).h : _ → _) = id := by
  change ((decomp (A := A) D.toData).deckCode _ (level₂_ρs D) 1 : _ → _) = id
  rw [map_one]
  rfl

end Model

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

/-! ### Detection at one level -/

/-- **Every pointed object is detected at one level**: there is a pointed Galois object `q`
over a W-model level such that every element of `Π^tp` with trivial stage component at `q`
fixes the given point of the fibre of `Z`. -/
theorem exists_level_fix (Z : TempObj O R A) (z : (tempFibre O R A V hV).obj Z) :
    ∃ q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR), ∀ α : temperedPi1 O R A V hV,
      (temperedPi1EquivLim V hV hp hR α).1 q = 1 → α.app Z z = z := by
  obtain ⟨q, f, hf⟩ := dom₁ (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.1 Z z
  refine ⟨q, fun α hα ↦ ?_⟩
  have h1 := temperedPi1EquivLim_apply V hV hp hR α q
  rw [hα] at h1
  have h2 : α.app q.G q.g = q.g := by
    calc α.app q.G q.g = α.app q.G (α⁻¹.app q.G q.g) := by rw [← h1]; rfl
      _ = q.g := FibreAut.app_inv_app α q.G q.g
  rw [← hf, FibreAut.app_naturality, h2]

variable [Finite A] [SMulCommClass A K R]

/-- The action of `andreEquiv' α` at a level is the stage component of `α`. -/
lemma andreTower_ρ_andreEquiv' (α : temperedPi1 O R A V hV)
    (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) :
    (andreTower (R := R) (A := A) V hV hp hR).ρ q (andreEquiv' V hV hp hR α) =
      (temperedPi1EquivLim V hV hp hR α).1 q := by
  change ((temperedPi1HomeoLim (A := A) V hV hp hR)
    ((andreEquiv' V hV hp hR).symm (andreEquiv' V hV hp hR α))).1 q = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

/-- Vertex stabilizers in the stage groups of André's tower are finite. -/
lemma finite_stab_andreTower (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (v : (andreTower (R := R) (A := A) V hV hp hR).V q) :
    {h : (andreTower (R := R) (A := A) V hV hp hR).G q | h • v = v}.Finite :=
  (curveData V hV hR q).finite_stab V hV v

/-- An element of André's group whose stage component at `q` is trivial, through Theorem A. -/
lemma app_eq_of_ρ_eq_one {Z : TempObj O R A} {z : (tempFibre O R A V hV).obj Z}
    {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    (hq : ∀ α : temperedPi1 O R A V hV, (temperedPi1EquivLim V hV hp hR α).1 q = 1 →
      α.app Z z = z) {g : andreGroup O R A V hV}
    (hg : (andreTower (R := R) (A := A) V hV hp hR).ρ q g = 1) :
    ((andreEquiv' V hV hp hR).symm g).app Z z = z := by
  refine hq _ ?_
  rw [← andreTower_ρ_andreEquiv', ContinuousMulEquiv.apply_symm_apply]
  exact hg

/-! ### The Tate characters on André's group -/

section Characters

variable (D : Data O R)

/-- **The character of `Y`** on André's group, `χ_Y ∘ (Theorem A)⁻¹`. -/
def charY : andreGroup O R A V hV →* Multiplicative ℤ :=
  (character (A := A) D V hV).comp
    (andreEquiv' V hV hp hR).symm.toMulEquiv.toMonoidHom

lemma charY_apply (g : andreGroup O R A V hV) :
    charY (A := A) V hV hp hR D g =
      character (A := A) D V hV ((andreEquiv' V hV hp hR).symm g) := rfl

/-- **`χ_Y` is detected at one level of André's tower.** -/
theorem exists_level_charY :
    ∃ q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR), ∀ g,
      (andreTower (R := R) (A := A) V hV hp hR).ρ q g = 1 → charY (A := A) V hV hp hR D g = 1 := by
  obtain ⟨q, hq⟩ := exists_level_fix V hV hp hR (X₀ (A := A) D) (basePoint D V hV)
  refine ⟨q, fun g hg ↦ ?_⟩
  have hfix := app_eq_of_ρ_eq_one V hV hp hR hq hg
  exact FibreAut.deckCharacterFun_eq (X₀ (A := A) D) (deck D) (basePoint D V hV)
    (isDeckTorsor D V hV) ((FibreAut.deckAct_one _ _ _).trans hfix.symm)

/-- **Elliptic elements of André's tower lie in `Π^tp_Y`.** -/
theorem charY_eq_one_of_elliptic {g : andreGroup O R A V hV}
    (he : (andreTower (R := R) (A := A) V hV hp hR).Elliptic g) :
    charY (A := A) V hV hp hR D g = 1 := by
  obtain ⟨q, hq⟩ := exists_level_charY (A := A) V hV hp hR D
  exact TreeTower.eq_one_of_elliptic (charY (A := A) V hV hp hR D)
    (fun _ ↦ isOfFinOrder_multiplicative_int) hq (finite_stab_andreTower V hV hp hR q) he

/-- **Elements with nontrivial image in the deck group of `Y` fix no vertex at some level.** -/
theorem exists_hyperbolicAt_of_charY_ne_one {g : andreGroup O R A V hV}
    (hg : charY (A := A) V hV hp hR D g ≠ 1) :
    ∃ q, (andreTower (R := R) (A := A) V hV hp hR).HyperbolicAt q g := by
  obtain ⟨q, hq⟩ := exists_level_charY (A := A) V hV hp hR D
  exact ⟨q, TreeTower.hyperbolicAt_of_ne_one (charY (A := A) V hV hp hR D)
    (fun _ ↦ isOfFinOrder_multiplicative_int) hq (finite_stab_andreTower V hV hp hR q) hg⟩

/-- **Unconditional estrangement of the elements detected by `Y`**: every element of André's
group with nontrivial image in the deck group `ℤ` of `Y → X` is estranged. -/
theorem estrangedElt_of_charY_ne_one {g : andreGroup O R A V hV}
    (hg : charY (A := A) V hV hp hR D g ≠ 1) :
    (andreTower (R := R) (A := A) V hV hp hR).EstrangedElt g := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  obtain ⟨q, hq⟩ := exists_hyperbolicAt_of_charY_ne_one V hV hp hR D hg
  exact TreeTower.estrangedElt_of_hyperbolicAt hq

/-- **Nontrivial compact subgroups of André's group lie in `Π^tp_Y`** (their elements are
elliptic). -/
theorem le_ker_charY_of_isCompact (H : Subgroup (andreGroup O R A V hV))
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) : H ≤ (charY (A := A) V hV hp hR D).ker :=
  fun _ hg ↦ charY_eq_one_of_elliptic V hV hp hR D
    (TreeTower.elliptic_of_mem (finite_map_of_isCompact_andre V hV hp hR H hH) hg)

end Characters

section Double

variable (D : DoubleData O R) (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)

/-- **The character of `Ÿ`** on André's group, `χ_Ÿ ∘ (Theorem A)⁻¹`; its kernel is the image of
`Π^tp_Ÿ` (`mem_piYddot_iff_charYY`). -/
def charYY : andreGroup O R A V hV →* Multiplicative ℤ × Multiplicative (ZMod 2) :=
  (character₂ (A := A) D V hV s hs).comp (andreEquiv' V hV hp hR).symm.toMulEquiv.toMonoidHom

lemma mem_piYddot_iff_charYY (g : andreGroup O R A V hV) :
    (andreEquiv' V hV hp hR).symm g ∈ piYddot (A := A) D V hV s hs ↔
      charYY (A := A) V hV hp hR D s hs g = 1 :=
  MonoidHom.mem_ker

lemma charYY_fst (g : andreGroup O R A V hV) :
    (charYY (A := A) V hV hp hR D s hs g).1 = charY (A := A) V hV hp hR D.toData g :=
  (character_eq_fst D V hV s hs _).symm

/-- **The square of an elliptic element lies in `Π^tp_Ÿ`.** -/
theorem charYY_sq_eq_one_of_elliptic {g : andreGroup O R A V hV}
    (he : (andreTower (R := R) (A := A) V hV hp hR).Elliptic g) :
    charYY (A := A) V hV hp hR D s hs (g ^ 2) = 1 := by
  rw [map_pow]
  refine Prod.ext ?_ (sq_eq_one_zmod2 _)
  rw [Prod.pow_fst, charYY_fst, charY_eq_one_of_elliptic V hV hp hR D.toData he, one_pow]
  rfl

/-- **The genuinely wild remaining part of M4 for the Tate curve**: the nontrivial elliptic
elements of `Δ` acting trivially on the fibres of all explicit Tate coverings (`Π^tp_Ÿ`) are
estranged. Open. -/
def TateWildPart (Δ : Subgroup (andreGroup O R A V hV)) : Prop :=
  (andreTower (R := R) (A := A) V hV hp hR).EstrangedOn
    {g | g ∈ Δ ∧ (andreTower (R := R) (A := A) V hV hp hR).Elliptic g ∧
      charYY (A := A) V hV hp hR D s hs g = 1}

/-- **The involution part**: elliptic elements `g ≠ 1` of `Δ` with `g ^ 2 = 1` are estranged.
It follows from `TateWildPart Δ` (`tateInvolutionPart_of_tateWildPart`,
`Andre/TateInvolution.lean`: an involution of `Π^tp` fixes `±√c`, so elliptic involutions lie in
`Π^tp_Ÿ`). -/
def TateInvolutionPart (Δ : Subgroup (andreGroup O R A V hV)) : Prop :=
  (andreTower (R := R) (A := A) V hV hp hR).EstrangedOn
    {g | g ∈ Δ ∧ (andreTower (R := R) (A := A) V hV hp hR).Elliptic g ∧ g ^ 2 = 1}

/-- **Estrangement of André's tower over `Δ` = the wild Tate part + the involution part**: the
elements outside `Π^tp_Y` are estranged unconditionally, the Kummer elements through their
squares. -/
theorem estranged_comap_andreTower_iff_tate (Δ : Subgroup (andreGroup O R A V hV)) :
    ((andreTower (R := R) (A := A) V hV hp hR).comap Δ.subtype).Estranged ↔
      TateWildPart (A := A) V hV hp hR D s hs Δ ∧ TateInvolutionPart (A := A) V hV hp hR Δ := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  rw [TreeTower.estranged_comap_subtype_iff]
  constructor
  · intro h
    exact ⟨h.mono fun g hg ↦ hg.1, h.mono fun g hg ↦ hg.1⟩
  · rintro ⟨hW, hI⟩ g hg hg1
    by_cases he : (andreTower (R := R) (A := A) V hV hp hR).Elliptic g
    · by_cases h2 : g ^ 2 = 1
      · exact hI g ⟨hg, he, h2⟩ hg1
      · exact TreeTower.EstrangedElt.of_pow (hW (g ^ 2) ⟨Δ.pow_mem hg 2, he.pow 2,
          charYY_sq_eq_one_of_elliptic V hV hp hR D s hs he⟩ h2)
    · exact TreeTower.estrangedElt_of_not_elliptic he

/-- **The M4 input relative to the rigid levels, for the Tate curve**: `EllipticEstrangement Δ`
is the wild Tate part plus the involution part. -/
theorem ellipticEstrangement_iff_tate (Δ : Subgroup (andreGroup O R A V hV)) :
    EllipticEstrangement V hV hp hR Δ ↔
      TateWildPart (A := A) V hV hp hR D s hs Δ ∧ TateInvolutionPart (A := A) V hV hp hR Δ := by
  rw [← estranged_comap_andreTower_iff_elliptic, estranged_comap_andreTower_iff_tate]

/-- **[SemiAnbd] Thm. 3.7(iii) for `Δ` (system form) from the wild Tate part and the involution
part.** -/
theorem exists_le_stab_andreTower_of_tate (Δ : Subgroup (andreGroup O R A V hV))
    (hW : TateWildPart (A := A) V hV hp hR D s hs Δ) (hI : TateInvolutionPart (A := A) V hV hp hR Δ)
    (H : Subgroup (andreGroup O R A V hV)) (hHΔ : H ≤ Δ) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H ≤ TreeTower.stab s :=
  exists_le_stab_andreTower_of_le_estranged V hV hp hR Δ
    ((estranged_comap_andreTower_iff_tate V hV hp hR D s hs Δ).2 ⟨hW, hI⟩) H hHΔ hH1 hH

/-- **[SemiAnbd] Thm. 3.7(iv) for André's group (system form) from the wild Tate part and the
involution part.** -/
theorem exists_eq_stab_of_maximal_of_tate (hW : TateWildPart (A := A) V hV hp hR D s hs ⊤)
    (hI : TateInvolutionPart (A := A) V hV hp hR ⊤) (H : Subgroup (andreGroup O R A V hV))
    (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV)))
    (hmax : ∀ H' : Subgroup (andreGroup O R A V hV), IsCompact (H' : Set (andreGroup O R A V hV)) →
      H ≤ H' → H' = H) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H = TreeTower.stab s :=
  exists_eq_stab_of_maximal_of_elliptic V hV hp hR
    ((ellipticEstrangement_iff_tate V hV hp hR D s hs ⊤).2 ⟨hW, hI⟩) H hH1 hH hmax

end Double

/-! ### Comparison with a Tate level of André's tower -/

section Comparison

variable (D : Data O R)

/-- **Comparison with a Tate level**: the elements acting trivially on the tree at `q` are
exactly those of `Π^tp_Y` (what the Tate model at `q` gives: the tree is the line, `Π^tp_X`
acting through the translations by `χ_Y`). Not provided by the construction. -/
def TateLevel (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) : Prop :=
  (andreTower (R := R) (A := A) V hV hp hR).actKer (· = q) = (charY (A := A) V hV hp hR D).ker

/-- The line comparison `TateLineLevel q (tateLineHom ∘ χ_Y)` gives `TateLevel q`. -/
theorem tateLevel_of_tateLineLevel {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    (h : TateLineLevel V hV hp hR q (DihedralLine.tateLineHom.comp (charY (A := A) V hV hp hR D))) :
    TateLevel (A := A) V hV hp hR D q := by
  obtain ⟨φ, -, hφ⟩ := h
  ext g
  rw [TreeTower.mem_actKer, MonoidHom.mem_ker]
  constructor
  · intro hg
    have h0 := hφ g (φ.symm 0)
    rw [hg q rfl, Equiv.apply_symm_apply] at h0
    change (0 : ℤ) = DihedralLine.tateLineHom (charY (A := A) V hV hp hR D g) • (0 : ℤ) at h0
    refine DihedralLine.tateLineHom_eq_one.1 (DihedralLine.eq_one_of_forall_smul_eq fun x ↦ ?_)
    change DihedralLine.tateLineHom (charY (A := A) V hV hp hR D g) • x = x
    have hx := hφ g (φ.symm x)
    rw [hg q rfl, Equiv.apply_symm_apply] at hx
    change x = DihedralLine.tateLineHom (charY (A := A) V hV hp hR D g) • x at hx
    exact hx.symm
  · intro hg j hj v
    subst hj
    apply φ.injective
    rw [hφ]
    change DihedralLine.tateLineHom (charY (A := A) V hV hp hR D g) • φ v = φ v
    rw [hg, map_one, one_smul]

/-- **Under the comparison, the tame half holds for `P = {q}`** (unconditionally in fact for the
elements outside `Π^tp_Y`, `estrangedElt_of_charY_ne_one`). -/
theorem tameEstrangement_of_tateLevel {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    (h : TateLevel (A := A) V hV hp hR D q) (Δ : Subgroup (andreGroup O R A V hV)) :
    TameEstrangement V hV hp hR Δ (· = q) := by
  rintro g ⟨-, hgK⟩ -
  rw [h, MonoidHom.mem_ker] at hgK
  exact estrangedElt_of_charY_ne_one V hV hp hR D hgK

end Comparison

section ComparisonDouble

variable (D : DoubleData O R) (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)

/-- **Under the comparison, M4 for the Tate level `q` is the wild Tate part plus the involution
part.** -/
theorem wildEstrangement_tateLevel_iff {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    (h : TateLevel (A := A) V hV hp hR D.toData q) (Δ : Subgroup (andreGroup O R A V hV)) :
    WildEstrangement V hV hp hR Δ (· = q) ↔
      TateWildPart (A := A) V hV hp hR D s hs Δ ∧ TateInvolutionPart (A := A) V hV hp hR Δ := by
  rw [← estranged_comap_andreTower_iff_tate,
    estranged_comap_andreTower_iff V hV hp hR Δ (· = q)]
  exact ⟨fun hW ↦ ⟨tameEstrangement_of_tateLevel V hV hp hR D.toData h Δ, hW⟩, And.right⟩

/-- **M4 for the Tate curve ⇐ comparison ∧ remaining wild part (∧ involution part).** -/
theorem wildEstrangement_of_tate {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    (h : TateLevel (A := A) V hV hp hR D.toData q) (Δ : Subgroup (andreGroup O R A V hV))
    (hW : TateWildPart (A := A) V hV hp hR D s hs Δ)
    (hI : TateInvolutionPart (A := A) V hV hp hR Δ) :
    WildEstrangement V hV hp hR Δ (· = q) :=
  (wildEstrangement_tateLevel_iff V hV hp hR D s hs h Δ).2 ⟨hW, hI⟩

end ComparisonDouble

/-! ### Nonvacuity -/

/-- **André's tower has nontrivial, non-elliptic, estranged elements** for good Tate data
(Theorem B gives `χ_Y ≠ 1`). -/
theorem exists_estranged_of_goodTate (T : Data O R) (ϖ : O) (hϖ : Irreducible ϖ)
    (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))
    (hb : IsUnit T.b₆ ∨ (T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ≠ 0 ∧ T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ∣ T.π))
    (hx : Transcendental K T.x) :
    ∃ g : andreGroup O R A V hV, g ≠ 1 ∧
      ¬ (andreTower (R := R) (A := A) V hV hp hR).Elliptic g ∧
      (andreTower (R := R) (A := A) V hV hp hR).EstrangedElt g := by
  obtain ⟨τ, hτ⟩ := exists_character_ne_one_of_goodTate (A := A) T V hV hp.choose
    hp.choose_spec.1 hp.choose_spec.2 hR ϖ hϖ hd hb hx
  have hg : charY (A := A) V hV hp hR T (andreEquiv' V hV hp hR τ) ≠ 1 := by
    rwa [charY_apply, ContinuousMulEquiv.symm_apply_apply]
  refine ⟨andreEquiv' V hV hp hR τ, fun h1 ↦ hg (by rw [h1, map_one]), fun he ↦
    hg (charY_eq_one_of_elliptic V hV hp hR T he), estrangedElt_of_charY_ne_one V hV hp hR T hg⟩

end

end TemperedFundamentalGroups
