/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.StageLimit
import TemperedFundamentalGroups.Andre.StageTower

/-!
# The tree tower on André's group (Blueprint §12.5, C6)

Scheme case, under the hypotheses of Theorem A. The members of `galW` are universal Galois
objects over W-model levels (`nonempty_uData_of_galClassW`), so the inverse limit `stageLimit` of
their stage groups carries the tree tower `curveTower` (`Andre/StageTower.lean`), and so does
André's group through `andreGroupHomeoLim : andreGroup ≃ₜ* stageLimit` (`andreTower`).

* **`isCompact_stab_curveTower`**, **`isCompact_stab_andreTower`**: the stabilizers of compatible
  systems of vertices of the trees of the dual graphs — the verticial subgroups (decomposition
  groups of components) and the edge-like subgroups (of nodes) — are compact subgroups of
  `stageLimit`, resp. of André's group.
* The general results of Blueprint §12.4 apply to `andreTower`: `stab_smul`,
  `exists_adj_fixed_inf` unconditionally; commensurable terminality `commensurator_stab` and
  `eq_of_stab_le` under `(HI s)`, which is not proved for curves (Blueprint §12.5, C6).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open GaloisLimit

section Data

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- The members of `galClassW` are universal Galois objects. -/
lemma nonempty_uData_of_galClassW {P : Level O R A → Prop} {X : TempObj O R A}
    (hX : galClassW O R A Ω P X) : Nonempty (UData Ω X) := by
  obtain ⟨Lv, _, _, _, _, _, hdim, z₀, -, _, -, hidem, -, -, _, ⟨e⟩⟩ := hX
  exact ⟨{ Lv := Lv, hdim := hdim, z₀ := z₀, hidem := hidem, e := e }⟩

end Data

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

/-- The identification of the members of `galW` with universal Galois objects. -/
def curveData (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) : UData Ω q.G :=
  (nonempty_uData_of_galClassW q.mem).some

/-- **The tree tower of the curve** on the inverse limit of the stage groups. -/
def curveTower : TreeTower.{u, u, u} (stageLimit (R := R) (A := A) V hV hp hR)
    (PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) :=
  stageTower V hV _ _ (curveData V hV hR)

/-- **Verticial and edge-like subgroups of `lim Π_Lv` are compact.** -/
theorem isCompact_stab_curveTower (s : (curveTower (R := R) (A := A) V hV hp hR).Sys) :
    IsCompact (SetLike.coe (TreeTower.stab s)) :=
  isCompact_stab (R := R) (A := A) V hV _ _ (curveData V hV hR) s

variable [Finite A] [SMulCommClass A K R]

/-- **The tree tower on André's group**, through `andreGroupHomeoLim`. -/
def andreTower : TreeTower.{u, u, u} (andreGroup O R A V hV)
    (PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) :=
  (curveTower (R := R) (A := A) V hV hp hR).comap
    (andreGroupHomeoLim (R := R) (A := A) V hV hp hR).toMulEquiv.toMonoidHom

/-- **Verticial (decomposition groups of components) and edge-like subgroups of André's group are
compact.** -/
theorem isCompact_stab_andreTower (s : (curveTower (R := R) (A := A) V hV hp hR).Sys) :
    IsCompact (SetLike.coe (TreeTower.stab ((curveTower (R := R) (A := A) V hV hp hR).comapSys
      (andreGroupHomeoLim (R := R) (A := A) V hV hp hR).toMulEquiv.toMonoidHom s))) := by
  rw [TreeTower.stab_comap]
  have h := (isCompact_stab_curveTower V hV hp hR s).image
    (andreGroupHomeoLim (R := R) (A := A) V hV hp hR).symm.continuous
  convert h using 1
  ext g
  simp only [Subgroup.coe_comap, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hg
    exact ⟨_, hg, (andreGroupHomeoLim (R := R) (A := A) V hV hp hR).symm_apply_apply g⟩
  · rintro ⟨γ, hγ, rfl⟩
    change (andreGroupHomeoLim (R := R) (A := A) V hV hp hR)
      ((andreGroupHomeoLim (R := R) (A := A) V hV hp hR).symm γ) ∈ _
    rwa [ContinuousMulEquiv.apply_symm_apply]

end

end TemperedFundamentalGroups
