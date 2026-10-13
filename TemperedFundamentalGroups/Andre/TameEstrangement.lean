/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.WildEstrangement
import TemperedFundamentalGroups.SemiAnbd.DihedralLine

/-!
# The tame half of M4 for André's tower at rigid levels (Blueprint §12.10)

Scheme case, under the hypotheses of Theorem A. At a level `q` of André's tower the stage group
is an extension of the Galois group of the level by the deck group of the tree covering of the
dual graph (`Andre/StageGroup.lean`); an element acting trivially on the level and fixing a
vertex of the tree is trivial (`UData.stageOf_eq_one_of_fixed`). Hence:

* **`hyperbolicAt_curveTower_of_lev`**: a nontrivial stage element acting trivially on the level
  fixes no vertex of the tree;
* `RigidLevel q`: the level ring `B` of `q` has no `R`-endomorphism but the identity (e.g.
  `B = R`: the levels over the base curve, with any W-model, whose universal Galois object is the
  tree covering of the dual graph and whose stage group is its deck group; that `galW` contains
  rigid levels is not shown here — without them the results below about `RigidLevel` are empty);
  **`hyperbolicAt_andreTower_of_rigid`**: at a rigid level every element of André's group acting
  nontrivially on the tree acts without fixed vertices;
* **`tameEstrangement_rigid`** (unconditional): `TameEstrangement Δ RigidLevel` — every element
  of `Δ` acting nontrivially on the tree of some rigid level is estranged (it fixes no vertex at
  any deeper level, wild or not);
* **`wildEstrangement_rigid_iff`**: relative to the rigid levels, M4 is exactly
  **`EllipticEstrangement Δ`** (the nontrivial elements of `Δ` fixing a vertex at every level are
  estranged), and **`estranged_comap_andreTower_iff_elliptic`**: the estrangement of André's tower
  over `Δ` is equivalent to it;
* consumers without any tame hypothesis: **`exists_le_stab_andreTower_of_elliptic`**,
  **`exists_eq_stab_of_maximal_of_elliptic`** ([SemiAnbd] Thm. 3.7(iii)/(iv), system form),
  `exists_le_stab_andreTower_of_wild_rigid`.

**What this does and does not give.** The rigid-level tame half is a theorem, but it concerns
only hyperbolic elements, and hyperbolic elements lie in no compact subgroup
(`TreeTower.not_hyperbolicAt_of_mem`). For Thm. 3.7(iii)/(iv) the whole remaining input is the
estrangement of the elliptic elements, `EllipticEstrangement` (open; Blueprint §12.10).

**The Tate line.** `TateLineLevel q χ` is the comparison of the tree of a level `q` of André's
tower with the explicit line of `SemiAnbd/DihedralLine.lean`, equivariantly along
`χ : andreGroup →* D_∞` (for the Tate curve with its Tate model at `q`, `χ` would be the Tate
character `TateObject.character` composed with the translations; this needs the W-model chosen by
`curveData` at `q` to be the Tate model, which the construction does not provide). Under it:
the tree at `q` is a line (`lineAt_of_tateLineLevel`), translations by `χ` are hyperbolic
(`hyperbolicAt_of_tateLineLevel`), reflections fix a single vertex at `q`
(`smallFixAt_of_tateLineLevel`), and if `χ` takes values in the translations, the tame half holds
for `P = {q}` (`tameEstrangement_of_tateLineLevel`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold DihedralGroup

namespace TemperedFundamentalGroups

noncomputable section

open GaloisLimit

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

/-! ### Deck elements are hyperbolic -/

/-- **A nontrivial stage element acting trivially on the level fixes no vertex of the tree**
(the deck group of the tree covering acts freely). -/
theorem hyperbolicAt_curveTower_of_lev (γ : stageLimit (R := R) (A := A) V hV hp hR)
    (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (a : Aut q.G)
    (ha : γ.1 q = stageOf a) (hlev : (curveData V hV hR q).lev a = AlgHom.id R _)
    (h1 : γ.1 q ≠ 1) : (curveTower (R := R) (A := A) V hV hp hR).HyperbolicAt q γ := by
  intro v hv
  change (curveData V hV hR q).stageTree V hV (γ.1 q) v = v at hv
  rw [ha, UData.stageTree_stageOf] at hv
  exact h1 (ha.trans ((curveData V hV hR q).stageOf_eq_one_of_fixed V hV a hv hlev))

/-- A **rigid level**: the level ring has no `R`-endomorphism but the identity (e.g. the levels
`B = R` over the base curve; their presence in `galW` is not shown here). -/
def RigidLevel (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) : Prop :=
  ∀ φ : (curveData V hV hR q).Lv.L.B →ₐ[R] (curveData V hV hR q).Lv.L.B, φ = AlgHom.id R _

variable [Finite A] [SMulCommClass A K R]

/-- **At a rigid level, every element of André's group acting nontrivially on the tree acts
without fixed vertices.** -/
theorem hyperbolicAt_andreTower_of_rigid {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    (hq : RigidLevel V hV hR q) {g : andreGroup O R A V hV}
    (hg : ∃ v : (andreTower (R := R) (A := A) V hV hp hR).V q,
      (andreTower (R := R) (A := A) V hV hp hR).ρ q g • v ≠ v) :
    (andreTower (R := R) (A := A) V hV hp hR).HyperbolicAt q g := by
  set γ := (andreGroupHomeoLim (R := R) (A := A) V hV hp hR) g
  obtain ⟨a, ha⟩ := eq_stageOf (γ.1 q)
  refine hyperbolicAt_curveTower_of_lev V hV hp hR γ q a ha (hq _) fun h1 ↦ ?_
  obtain ⟨v, hv⟩ := hg
  apply hv
  change (curveData V hV hR q).stageTree V hV (γ.1 q) v = v
  rw [h1, map_one]
  rfl

/-- At a rigid level, an element acting nontrivially on the tree is not elliptic. -/
theorem not_elliptic_of_rigid {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    (hq : RigidLevel V hV hR q) {g : andreGroup O R A V hV}
    (hg : ∃ v : (andreTower (R := R) (A := A) V hV hp hR).V q,
      (andreTower (R := R) (A := A) V hV hp hR).ρ q g • v ≠ v) :
    ¬ (andreTower (R := R) (A := A) V hV hp hR).Elliptic g := fun he ↦ by
  obtain ⟨v, hv⟩ := he q
  exact hyperbolicAt_andreTower_of_rigid V hV hp hR hq hg v hv

/-- **The tame half at the rigid levels holds unconditionally**: every element of `Δ` acting
nontrivially on the tree of a rigid level is estranged. -/
theorem tameEstrangement_rigid (Δ : Subgroup (andreGroup O R A V hV)) :
    TameEstrangement V hV hp hR Δ (RigidLevel (A := A) V hV hR) := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  exact TreeTower.tameEstranged_of_hyperbolicAt fun _ _ _ hq hg ↦
    hyperbolicAt_andreTower_of_rigid V hV hp hR hq hg

/-! ### Elliptic estrangement -/

/-- **Elliptic estrangement** for André's tower over `Δ`: every nontrivial element of `Δ` fixing a
vertex of the tree at every level has, at cofinally many levels, a fixed set of diameter `≤ 2`.
This is the whole input needed for [SemiAnbd] Thm. 3.7(iii)/(iv) (open). -/
def EllipticEstrangement (Δ : Subgroup (andreGroup O R A V hV)) : Prop :=
  (andreTower (R := R) (A := A) V hV hp hR).EstrangedOn
    {g | g ∈ Δ ∧ (andreTower (R := R) (A := A) V hV hp hR).Elliptic g}

/-- **Estrangement of André's tower over `Δ` is elliptic estrangement.** -/
theorem estranged_comap_andreTower_iff_elliptic (Δ : Subgroup (andreGroup O R A V hV)) :
    ((andreTower (R := R) (A := A) V hV hp hR).comap Δ.subtype).Estranged ↔
      EllipticEstrangement V hV hp hR Δ := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  rw [TreeTower.estranged_comap_subtype_iff, TreeTower.estrangedOn_iff_elliptic]
  rfl

/-- **Relative to the rigid levels, M4 is elliptic estrangement**: elliptic elements act
trivially on the trees of rigid levels. -/
theorem wildEstrangement_rigid_iff (Δ : Subgroup (andreGroup O R A V hV)) :
    WildEstrangement V hV hp hR Δ (RigidLevel (A := A) V hV hR) ↔
      EllipticEstrangement V hV hp hR Δ := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  rw [WildEstrangement, TreeTower.wildEstranged_iff_elliptic, EllipticEstrangement]
  refine ⟨fun h ↦ h.mono fun g hg ↦ ⟨hg.1, ?_, hg.2⟩, fun h ↦ h.mono fun g hg ↦ ⟨hg.1, hg.2.2⟩⟩
  refine TreeTower.mem_actKer.2 fun q hq v ↦ ?_
  by_contra hv
  exact not_elliptic_of_rigid V hV hp hR hq ⟨v, hv⟩ hg.2

/-- **The estrangement of André's tower over `Δ` is M4 relative to the rigid levels** (the tame
half being `tameEstrangement_rigid`). -/
theorem estranged_comap_andreTower_iff_wild_rigid (Δ : Subgroup (andreGroup O R A V hV)) :
    ((andreTower (R := R) (A := A) V hV hp hR).comap Δ.subtype).Estranged ↔
      WildEstrangement V hV hp hR Δ (RigidLevel (A := A) V hV hR) := by
  rw [wildEstrangement_rigid_iff, estranged_comap_andreTower_iff_elliptic]

/-- **[SemiAnbd] Thm. 3.7(iii) for `Δ` (system form) from elliptic estrangement.** -/
theorem exists_le_stab_andreTower_of_elliptic (Δ : Subgroup (andreGroup O R A V hV))
    (hE : EllipticEstrangement V hV hp hR Δ)
    (H : Subgroup (andreGroup O R A V hV)) (hHΔ : H ≤ Δ) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H ≤ TreeTower.stab s :=
  exists_le_stab_andreTower_of_le_estranged V hV hp hR Δ
    ((estranged_comap_andreTower_iff_elliptic V hV hp hR Δ).2 hE) H hHΔ hH1 hH

/-- **[SemiAnbd] Thm. 3.7(iii) for `Δ` from M4 relative to the rigid levels alone** (no tame
hypothesis). -/
theorem exists_le_stab_andreTower_of_wild_rigid (Δ : Subgroup (andreGroup O R A V hV))
    (hW : WildEstrangement V hV hp hR Δ (RigidLevel (A := A) V hV hR))
    (H : Subgroup (andreGroup O R A V hV)) (hHΔ : H ≤ Δ) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H ≤ TreeTower.stab s :=
  exists_le_stab_andreTower_of_tame_wild V hV hp hR Δ (RigidLevel (A := A) V hV hR)
    (tameEstrangement_rigid V hV hp hR Δ) hW H hHΔ hH1 hH

/-- **[SemiAnbd] Thm. 3.7(iv) for André's group (system form) from elliptic estrangement.** -/
theorem exists_eq_stab_of_maximal_of_elliptic
    (hE : EllipticEstrangement (R := R) (A := A) V hV hp hR ⊤)
    (H : Subgroup (andreGroup O R A V hV)) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV)))
    (hmax : ∀ H' : Subgroup (andreGroup O R A V hV), IsCompact (H' : Set (andreGroup O R A V hV)) →
      H ≤ H' → H' = H) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H = TreeTower.stab s :=
  exists_eq_stab_of_maximal_of_tame_wild V hV hp hR (RigidLevel (A := A) V hV hR)
    (tameEstrangement_rigid V hV hp hR ⊤) ((wildEstrangement_rigid_iff V hV hp hR ⊤).2 hE) H
    hH1 hH hmax

/-! ### Comparison with the Tate line -/

/-- **Comparison of a level of André's tower with the Tate line**: the tree at level `q` is
identified with the line `ℤ` of `DihedralLine`, equivariantly along `χ : andreGroup →* D_∞`
(for the Tate curve with the Tate model at `q`: the deck action of the Tate character on the
`ℤ`-chain of components). Not provided by the construction: `curveData` chooses an arbitrary
W-model at each level. -/
def TateLineLevel (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (χ : andreGroup O R A V hV →* DihedralGroup 0) : Prop :=
  ∃ φ : (andreTower (R := R) (A := A) V hV hp hR).V q ≃ ℤ,
    (∀ x y, ((andreTower (R := R) (A := A) V hV hp hR).graph q).Adj x y ↔
      DihedralLine.lineGraph.Adj (φ x) (φ y)) ∧
    ∀ g v, φ ((andreTower (R := R) (A := A) V hV hp hR).ρ q g • v) = χ g • φ v

variable {V hV hp hR}

/-- Under the comparison, the tree at `q` is a line. -/
theorem lineAt_of_tateLineLevel {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    {χ : andreGroup O R A V hV →* DihedralGroup 0} (h : TateLineLevel V hV hp hR q χ) :
    (andreTower (R := R) (A := A) V hV hp hR).LineAt q := by
  obtain ⟨φ, hadj, -⟩ := h
  intro v a b c ha hb hc
  rw [hadj, DihedralLine.lineGraph_adj] at ha hb hc
  have : φ a = φ b ∨ φ a = φ c ∨ φ b = φ c := by omega
  rcases this with h | h | h
  exacts [Or.inl (φ.injective h), Or.inr (Or.inl (φ.injective h)), Or.inr (Or.inr (φ.injective h))]

/-- Under the comparison, elements acting by nontrivial translations are hyperbolic at `q`,
hence estranged. -/
theorem hyperbolicAt_of_tateLineLevel {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    {χ : andreGroup O R A V hV →* DihedralGroup 0} (h : TateLineLevel V hV hp hR q χ)
    {g : andreGroup O R A V hV} {i : ZMod 0} (hg : χ g = r i) (hi : i ≠ 0) :
    (andreTower (R := R) (A := A) V hV hp hR).HyperbolicAt q g := by
  obtain ⟨φ, -, hφ⟩ := h
  intro v hv
  have := hφ g v
  rw [hv, hg] at this
  exact DihedralLine.r_smul_ne hi (φ v) this.symm

/-- Under the comparison, an element acting by a reflection fixes a single vertex at `q`. -/
theorem smallFixAt_of_tateLineLevel {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    {χ : andreGroup O R A V hV →* DihedralGroup 0} (h : TateLineLevel V hV hp hR q χ)
    {g : andreGroup O R A V hV} {i : ZMod 0} (hg : χ g = sr i) :
    (andreTower (R := R) (A := A) V hV hp hR).SmallFixAt q g := by
  obtain ⟨φ, -, hφ⟩ := h
  intro x y hx hy
  have h₁ := hφ g x
  have h₂ := hφ g y
  rw [hx, hg] at h₁
  rw [hy, hg] at h₂
  have hxy : x = y := φ.injective
    ((DihedralLine.sr_smul_eq_iff.1 h₁.symm).trans (DihedralLine.sr_smul_eq_iff.1 h₂.symm).symm)
  subst hxy
  simp

/-- **Under the comparison with `χ` valued in the translations, the tame half holds for
`P = {q}`.** -/
theorem tameEstrangement_of_tateLineLevel {q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    {χ : andreGroup O R A V hV →* DihedralGroup 0} (h : TateLineLevel V hV hp hR q χ)
    (hχ : ∀ g, ∃ i, χ g = r i) (Δ : Subgroup (andreGroup O R A V hV)) :
    TameEstrangement V hV hp hR Δ (· = q) := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  refine TreeTower.tameEstranged_of_hyperbolicAt fun g _ j hj hmov ↦ ?_
  subst hj
  obtain ⟨i, hi⟩ := hχ g
  refine hyperbolicAt_of_tateLineLevel h hi fun hi0 ↦ ?_
  obtain ⟨φ, -, hφ⟩ := h
  obtain ⟨v, hv⟩ := hmov
  apply hv
  apply φ.injective
  rw [hφ, hi, hi0, ← one_def, one_smul]

end

end TemperedFundamentalGroups
