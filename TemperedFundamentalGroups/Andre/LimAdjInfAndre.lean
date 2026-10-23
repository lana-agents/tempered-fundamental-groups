/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.CentreMove
import TemperedFundamentalGroups.Andre.ComponentDVR
import TemperedFundamentalGroups.Andre.CompositeCentre
import TemperedFundamentalGroups.Andre.LimGroupKonig
import TemperedFundamentalGroups.Andre.RootLevel
import TemperedFundamentalGroups.Andre.StageFix
import TemperedFundamentalGroups.Andre.TateInvolution
import TemperedFundamentalGroups.Andre.VertexPoints
import TemperedFundamentalGroups.Andre.WildEstrangement
import TemperedFundamentalGroups.SemiAnbd.CombGC
import TemperedFundamentalGroups.SemiAnbd.MidpointAdj
import TemperedFundamentalGroups.SemistableReduction.KummerValuation

/-!
# Edge-like subgroups between adjacent verticial subgroups of André's group (M2.6)

Scheme case, under the hypotheses of Theorem A. **`limAdjInf_andreTower`**: two verticial
systems of André's tree tower which are adjacent in the limit tree have stabilizers with
nontrivial intersection (`TreeTower.LimAdjInf`). Hence `PSCAdj` and CG3' hold for André's group
under estrangement alone (no hypothesis on edge-like subgroups).

Proof (valuations, Blueprint §12.8, Route A'). By `TreeTower.limAdjInf_of_mid` it suffices to show
that a midpoint system `e` (of edge kind, adjacent to `s k` wherever `s k ≠ s' k`) has a nontrivial
stabilizer. Fix `j₀` with `s j₀ ≠ s' j₀` and a valuation subring `V₀` of `F₀ = Frac B_{j₀}`
centred at the generic point of the component of `s j₀`; it is a DVR in which `ϖ = u tⁿ`,
`n ≥ 1`. Choose a prime `ℓ > n` and a level `P ⟶ j₀` containing `α` with `α ^ ℓ = ϖ`
(`exists_ptGal_pow_eq`). For every level `l ⟶ P`, a valuation subring `W` of `L = Frac B_l`
centred at the point of `e l` lies below a valuation centred at the generic point of the
component of `s l`, which restricts to `V₀` (no contraction at midpoints); so `W ∩ F₀` satisfies
the Kummer condition, and the orbit argument gives `τ ∈ Gal(L / F₀)` stabilizing `W` and moving
`α` (`Level.exists_algEquiv_apply_ne`). Its model automorphism fixes the centre of `W`, i.e.
the point of `e l`, so some stage group element fixes `e l` and has nontrivial image at `P`
(`exists_stage_fix_transition_ne_one_of_kummer`). König's lemma (`exists_andreGroup_mem`) gives
a nontrivial element of André's group fixing `e`.

## Main results

* `Level.exists_algEquiv_apply_ne`: the valuation-theoretic core.
* **`limAdjInf_andreTower`**.
* `TreeTower.isGraphic_iff_of_estranged_of_limAdjInf` (CG3' from estrangement and `LimAdjInf`).
* **`pscAdj_andreTower_of_estranged''`**, **`isGraphic_iff_andreTower_of_limAdjInf`**,
  **`isGraphic_iff_andreTower_andreTower'`**, and the forms `pscAdj_andreTower_of_tame_wild'`,
  `isGraphic_iff_andreTower_of_tame_wild'`, `pscAdj_andreTower_of_tateWild'`,
  `isGraphic_iff_andreTower_of_tateWild'` without the hypothesis on edge-like subgroups.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology TopologicalSpace
open scoped Pointwise

namespace TemperedFundamentalGroups

/-! ### CG3' from estrangement and `LimAdjInf` -/

namespace TreeTower

variable {Γ : Type*} [Group Γ] {J : Type*} [Category J] {T : TreeTower.{_, _, u} Γ J}
  {Γ' : Type*} [Group Γ'] {J' : Type*} [Category J'] {T' : TreeTower.{_, _, u} Γ' J'}

/-- **CG3' from estrangement and the restricted edge hypothesis** on both towers. -/
theorem isGraphic_iff_of_estranged_of_limAdjInf {α : Γ ≃* Γ'} (hE : T.Estranged)
    (hE' : T'.Estranged) (hL : T.LimAdjInf) (hL' : T'.LimAdjInf) :
    IsGraphic T T' α ↔ IsGroupTheoreticallyVerticial T T' α :=
  isGraphic_iff_isGroupTheoreticallyVerticial (pscAdj_of_estranged_of_limAdjInf hE hL)
    (pscAdj_of_estranged_of_limAdjInf hE' hL')

end TreeTower

noncomputable section

open ValuativeCentre GaloisLimit TempObj GaloisObject CurveConfig

/-! ### The valuation-theoretic core -/

section Level

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

lemma toRingEquiv_smul_valuationSubring {F L : Type u} [Field F] [Field L] [Algebra F L]
    (τ : L ≃ₐ[F] L) (W : ValuationSubring L) : τ.toRingEquiv • W = τ • W := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

/-- **A valuation centred at a specialization, restricting into `V₀`.** Let `ψ` be a model map
over a level map `φ : B₀ → B`, `η` a point of the model of `B` with `ψ η = x₀`, where the centre
`x₀` determines the valuation, and `V₀` centred at `x₀`. Then every specialization `m` of `η`
is the centre of a valuation subring `W` of `Frac B` with `W ∩ Frac B₀ ⊆ V₀`. -/
theorem Level.exists_isCentre_comap_le (Lv Lv₀ : Level O R A) [IsDomain Lv.L.B]
    [IsDomain Lv₀.L.B] [IsSchemeTheoreticallyDominant Lv.j] (φ : Lv₀.L.B →ₐ[R] Lv.L.B)
    (ψ : Lv.c.scheme ⟶ Lv₀.c.scheme)
    (hjψ : Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (φ : Lv₀.L.B →+* Lv.L.B)) ≫ Lv₀.j)
    {x₀ : Lv₀.c.scheme} (hdet : CentreDetermines (Lv₀.gen (FractionRing Lv₀.L.B)) x₀)
    {V₀ : ValuationSubring (FractionRing Lv₀.L.B)}
    (hV₀ : IsCentre (Lv₀.gen (FractionRing Lv₀.L.B)) V₀ x₀)
    {η m : Lv.c.scheme} (hη : ψ η = x₀) (hηm : η ⤳ m) :
    ∃ W : ValuationSubring (FractionRing Lv.L.B), IsCentre (Lv.gen (FractionRing Lv.L.B)) W m ∧
      ∀ f : FractionRing Lv₀.L.B →+* FractionRing Lv.L.B,
        (∀ b, f (algebraMap Lv₀.L.B _ b) = algebraMap Lv.L.B _ (φ b)) → W.comap f ≤ V₀ := by
  haveI : FaithfulSMul Lv.L.B (FractionRing Lv.L.B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  obtain ⟨V₁, hV₁⟩ := exists_isCentre (Lv.gen (FractionRing Lv.L.B))
    (Lv.gen_specializes (FractionRing Lv.L.B) η)
  obtain ⟨W, hWV, hW⟩ := hV₁.exists_le_of_specializes hηm
  refine ⟨W, hW, fun f hf x hx ↦ ?_⟩
  have h₁ := Level.isCentre_comap Lv Lv₀ φ f hf ψ hjψ hV₁
  rw [hη] at h₁
  rw [← hdet _ _ h₁ hV₀]
  exact hWV hx

open SemistableReduction.KummerValuation in
/-- **The valuation-theoretic core of M2.6.** In the situation of `exists_isCentre_comap_le`,
let `B` be Galois (`Aut_R(B)` transitive on a geometric fibre, `B` connected), `c ∈ K` nonzero
whose image `π ∈ Frac B₀` satisfies the Kummer condition for `V₀` and a prime `ℓ`, and
`α ∈ B` with `α ^ ℓ = c`. Then some `σ ∈ Aut_R(B)` moves `α`, and every model automorphism of
`σ` fixes `m`. -/
theorem Level.exists_algEquiv_apply_ne {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (Lv Lv₀ : Level O R A) [IsDomain Lv.L.B] [IsDomain Lv₀.L.B]
    [IsSchemeTheoreticallyDominant Lv.j] (t₀ : Lv.L.B →ₐ[R] Ω)
    (hgal : ∀ t : Lv.L.B →ₐ[R] Ω, ∃ σ : Lv.L.B ≃ₐ[R] Lv.L.B,
      t₀.comp (σ : Lv.L.B →ₐ[R] Lv.L.B) = t)
    (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (φ : Lv₀.L.B →ₐ[R] Lv.L.B) (ψ : Lv.c.scheme ⟶ Lv₀.c.scheme)
    (hjψ : Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (φ : Lv₀.L.B →+* Lv.L.B)) ≫ Lv₀.j)
    {x₀ : Lv₀.c.scheme} (hdet : CentreDetermines (Lv₀.gen (FractionRing Lv₀.L.B)) x₀)
    {V₀ : ValuationSubring (FractionRing Lv₀.L.B)}
    (hV₀ : IsCentre (Lv₀.gen (FractionRing Lv₀.L.B)) V₀ x₀) {ℓ : ℕ} (hℓ : ℓ.Prime) {c : K}
    (hc : c ≠ 0)
    (hK : ∀ β : FractionRing Lv₀.L.B, β ≠ 0 → V₀.valuation
      (algebraMap Lv₀.L.B (FractionRing Lv₀.L.B) (algebraMap R Lv₀.L.B (algebraMap K R c)) /
        β ^ ℓ) ≠ 1)
    {η m : Lv.c.scheme} (hη : ψ η = x₀) (hηm : η ⤳ m)
    {α : Lv.L.B} (hα : α ^ ℓ = algebraMap R Lv.L.B (algebraMap K R c)) :
    ∃ σ : Lv.L.B ≃ₐ[R] Lv.L.B, σ α ≠ α ∧ ∀ ψσ : Lv.c.scheme ⟶ Lv.c.scheme,
      ψσ ≫ Lv.c.toSpec = Lv.c.toSpec →
      Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j → ψσ m = m := by
  haveI := Lv.L.etale
  haveI := Lv.L.finite
  haveI := Lv₀.L.etale
  haveI := Lv₀.L.finite
  obtain ⟨W, hW, hWV⟩ := Lv.exists_isCentre_comap_le Lv₀ φ ψ hjψ hdet hV₀ hη hηm
  replace hWV := hWV _ (fracMap_algebraMap (L₂ := FractionRing Lv₀.L.B)
    (L₁ := FractionRing Lv.L.B) φ)
  letI : Algebra (FractionRing Lv₀.L.B) (FractionRing Lv.L.B) :=
    (fracMap (FractionRing Lv₀.L.B) (FractionRing Lv.L.B) φ).toAlgebra
  obtain ⟨hGal, hτ⟩ := FracGalois.isGalois_and_exists (FractionRing Lv₀.L.B)
    (FractionRing Lv.L.B) φ t₀ hgal hidem
  haveI : FiniteDimensional (FractionRing Lv₀.L.B) (FractionRing Lv.L.B) :=
    finiteDimensional_fracMap (FractionRing Lv₀.L.B) (FractionRing Lv.L.B) φ
  have hπ0 : algebraMap Lv₀.L.B (FractionRing Lv₀.L.B)
      (algebraMap R Lv₀.L.B (algebraMap K R c)) ≠ 0 := by
    intro h0
    apply hc
    have h1 := IsFractionRing.injective Lv₀.L.B (FractionRing Lv₀.L.B)
      (h0.trans (map_zero _).symm)
    exact ((algebraMap R Lv₀.L.B).comp (algebraMap K R)).injective (h1.trans (map_zero _).symm)
  have hαL : algebraMap Lv.L.B (FractionRing Lv.L.B) α ^ ℓ =
      algebraMap (FractionRing Lv₀.L.B) (FractionRing Lv.L.B)
        (algebraMap Lv₀.L.B (FractionRing Lv₀.L.B) (algebraMap R Lv₀.L.B (algebraMap K R c))) := by
    rw [← map_pow, hα]
    change _ = fracMap (FractionRing Lv₀.L.B) (FractionRing Lv.L.B) φ _
    rw [fracMap_algebraMap, φ.commutes]
  obtain ⟨τ, hτW, hτα⟩ := exists_smul_eq_self_and_apply_ne_of_pow_eq hℓ hαL hπ0 W
    (kummer_of_le (U := W.comap (algebraMap (FractionRing Lv₀.L.B) (FractionRing Lv.L.B)))
      hWV hK)
  obtain ⟨σ, -, hσ⟩ := hτ τ
  refine ⟨σ, fun h ↦ hτα (by rw [hσ, h]), fun ψσ hψσ hjσ ↦ ?_⟩
  exact Lv.map_centre_of_smul_eq (FractionRing Lv.L.B) σ ψσ hψσ hjσ τ.toRingEquiv
    (fun b ↦ hσ b) hW hW ((toRingEquiv_smul_valuationSubring τ W).trans hτW)

end Level

/-! ### Galois objects: transitivity and model automorphisms -/

section UData

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace UData

variable {X : TempObj O R A} (D : UData Ω X)

/-- **`Aut_R(B)` acts transitively on the geometric fibre** of the level of a Galois object. -/
theorem exists_comp_eq {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hX : 𝒢 X) (t₀ t : D.Lv.L.B →ₐ[R] Ω) :
    ∃ σ : D.Lv.L.B ≃ₐ[R] D.Lv.L.B, t₀.comp (σ : D.Lv.L.B →ₐ[R] D.Lv.L.B) = t := by
  haveI : Algebra.Etale R D.Lv.L.B := D.Lv.L.etale
  haveI : Module.Finite R D.Lv.L.B := D.Lv.L.finite
  have hsurj := levelPt_surjective V hV
    (hp := universalCovering.isUniversalCovering.{u, u, u} D.hdim D.z₀)
    (hc := (universalCovering.isUniversalCovering.{u, u, u} D.hdim D.z₀).countable_fibre)
  obtain ⟨x₀, hx₀⟩ := hsurj t₀
  obtain ⟨x₁, hx₁⟩ := hsurj t
  obtain ⟨a, ha⟩ := hgal X hX (fibreMap V hV D.e.inv x₀) (fibreMap V hV D.e.inv x₁)
  have hb : fibreMap V hV (D.e.conjAut a).hom x₀ = x₁ := by
    rw [Iso.conjAut_hom, Iso.conj_apply, fibreMap_comp_apply, fibreMap_comp_apply]
    change fibreMap V hV D.e.hom ((tempFibre O R A V hV).map a.hom _) = _
    rw [ha, ← fibreMap_comp_apply, Iso.inv_hom_id, fibreMap_id_apply]
  haveI : Subsingleton (universalObj D.Lv D.hdim D.z₀).Lv.L.H := D.sub
  have h := levelPt_fibreMap V hV (D.e.conjAut a).hom x₀
  have ht : t = t₀.comp (D.lev a) :=
    hx₁.symm.trans ((congrArg (levelPt V hV _) hb.symm).trans
      (h.trans (congrArg (fun s : D.Lv.L.B →ₐ[R] Ω ↦ s.comp (D.e.conjAut a).hom.φ.f) hx₀)))
  refine ⟨AlgEquiv.ofAlgHom (D.lev a) (D.lev a⁻¹) ?_ ?_, ?_⟩
  · rw [← lev_mul, inv_mul_cancel, lev_one]
  · rw [← lev_mul, mul_inv_cancel, lev_one]
  · rw [AlgEquiv.toAlgHom_ofAlgHom]
    exact ht.symm

/-- **Every automorphism of the level ring has a model automorphism** (gal). -/
theorem exists_modelAut {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hX : 𝒢 X)
    (σ : D.Lv.L.B ≃ₐ[R] D.Lv.L.B) :
    ∃ ψσ : D.Lv.c.scheme ⟶ D.Lv.c.scheme, ψσ ≫ D.Lv.c.toSpec = D.Lv.c.toSpec ∧
      D.Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : D.Lv.L.B →+* D.Lv.L.B)) ≫ D.Lv.j := by
  obtain ⟨a, ha⟩ := D.exists_lev_eq V hV hgal hX σ
  refine ⟨(D.e.conjAut a).hom.ψ, (D.e.conjAut a).hom.ψ_toSpec,
    (D.e.conjAut a).hom.j_ψ.trans ?_⟩
  change Spec.map (CommRingCat.ofHom
    ((D.lev a : D.Lv.L.B →ₐ[R] D.Lv.L.B) : D.Lv.L.B →+* D.Lv.L.B)) ≫ D.Lv.j = _
  rw [ha]
  rfl

end UData

end UData

/-! ### André's tower -/

section Andre

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

/-- **The maps of trees of the curve tower are equivariant along the transition maps** (at the
level of the stage groups). -/
lemma curveTower_map_stageTree {l l' : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    (f : l ⟶ l') (γ : stageGroup (tempFibre O R A V hV) l.G)
    (x : (curveData V hV hR l).Tr) :
    (curveData V hV hR l).vmapHom (curveData V hV hR l') (ptHomMor V hV f)
        ((curveData V hV hR l).stageTree V hV γ x) =
      (curveData V hV hR l').stageTree V hV
        (transition (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
          (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 f γ)
        ((curveData V hV hR l).vmapHom (curveData V hV hR l') (ptHomMor V hV f) x) := by
  obtain ⟨a, rfl⟩ := eq_stageOf γ
  obtain ⟨b, hb⟩ := eq_stageOf (transition (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 f (stageOf a))
  rw [hb, UData.stageTree_stageOf, UData.stageTree_stageOf]
  exact UData.vmapHom_treeAut V hV _ _ _ a b
    (fibreMap_transition V hV _ _ f a b hb) x

/-- **P7 + Kummer at one level.** Let `h : P ⟶ j₀`, `g : l ⟶ P`, `t` a vertex of vertex kind of
the tree at `l` with a neighbour `m`, mapped to a vertex `t'` of vertex kind and an edge vertex
`m'` at `j₀`. Let `V₀` be a valuation of `Frac B_{j₀}` centred at the point of `t'` satisfying
the Kummer condition for `c` and `ℓ`, and `α ∈ B_P` with `α ^ ℓ = c`. Then some stage group
element of `l` fixes `m` and has nontrivial transition along `g`. -/
theorem exists_stage_fix_transition_ne_one_of_kummer
    {j₀ P l : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (h : P ⟶ j₀) (g : l ⟶ P)
    {t m : (curveTower (R := R) (A := A) V hV hp hR).V l}
    {t' m' : (curveTower (R := R) (A := A) V hV hp hR).V j₀}
    (hadj : ((curveTower (R := R) (A := A) V hV hp hR).graph l).Adj t m)
    (ht : (curveTower (R := R) (A := A) V hV hp hR).kind l t = true)
    (htt' : (curveTower (R := R) (A := A) V hV hp hR).map (g ≫ h) t = t')
    (hmm' : (curveTower (R := R) (A := A) V hV hp hR).map (g ≫ h) m = m')
    (ht' : (curveTower (R := R) (A := A) V hV hp hR).kind j₀ t' = true)
    (hm' : (curveTower (R := R) (A := A) V hV hp hR).kind j₀ m' = false)
    [IsDomain (curveData V hV hR j₀).Lv.L.B]
    {V₀ : ValuationSubring (FractionRing (curveData V hV hR j₀).Lv.L.B)}
    (hV₀ : IsCentre ((curveData V hV hR j₀).Lv.gen (FractionRing (curveData V hV hR j₀).Lv.L.B))
      V₀ ((curveData V hV hR j₀).vertexPt t' : (curveData V hV hR j₀).Lv.c.scheme))
    {ℓ : ℕ} (hℓ : ℓ.Prime) {c : K} (hc : c ≠ 0)
    (hK : ∀ β : FractionRing (curveData V hV hR j₀).Lv.L.B, β ≠ 0 → V₀.valuation
      (algebraMap (curveData V hV hR j₀).Lv.L.B _
        (algebraMap R (curveData V hV hR j₀).Lv.L.B (algebraMap K R c)) / β ^ ℓ) ≠ 1)
    {α : (curveData V hV hR P).Lv.L.B} (hα : α ^ ℓ = algebraMap R _ (algebraMap K R c)) :
    ∃ γ : stageGroup (tempFibre O R A V hV) l.G,
      (curveData V hV hR l).stageTree V hV γ m = m ∧
        transition (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
          (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 g γ ≠ 1 := by
  subst htt' hmm'
  haveI := (WData.nonempty_of_isW (curveData_isW V hV hR l)).some.isDomain
  have hgalW := (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
  set Dl := curveData V hV hR l
  set D₀ := curveData V hV hR j₀
  obtain ⟨t₀⟩ := Dl.ne
  have hdet := (WData.nonempty_of_isW (curveData_isW V hV hR j₀)).some.centreDetermines
    (FractionRing D₀.Lv.L.B) _ (D₀.closure_vertexPt_mem ht')
  have hη : ptModelMap V hV (curveData V hV hR) (g ≫ h) (Dl.vertexPt t : Dl.Lv.c.scheme) =
      (D₀.vertexPt ((curveTower (R := R) (A := A) V hV hp hR).map (g ≫ h) t) :
        D₀.Lv.c.scheme) := by
    rw [← coe_ptFibreMap, curveTower_vertexPt_of_vertex V hV hp hR (g ≫ h) hadj ht ht' hm']
  have hηm : (Dl.vertexPt t : Dl.Lv.c.scheme) ⤳ (Dl.vertexPt m : Dl.Lv.c.scheme) :=
    (Dl.vertexPt_specializes ht hadj).map continuous_subtype_val
  obtain ⟨σ, hσα, hσψ⟩ := Level.exists_algEquiv_apply_ne Dl.Lv D₀.Lv t₀
    (Dl.exists_comp_eq V hV hgalW l.mem t₀) Dl.hidem
    (ptLevelMap V hV (curveData V hV hR) (g ≫ h)) (ptModelMap V hV (curveData V hV hR) (g ≫ h))
    (j_ptModelMap V hV (curveData V hV hR) (g ≫ h)) hdet hV₀ hℓ hc hK hη hηm
    (α := ptLevelMap V hV (curveData V hV hR) g α) (by rw [← map_pow, hα, AlgHom.commutes])
  obtain ⟨ψσ, hψσ, hjσ⟩ := Dl.exists_modelAut V hV hgalW l.mem σ
  refine UData.exists_stage_fix_transition_ne_one V hV hgalW
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 g Dl (curveData V hV hR P) σ ψσ hψσ
    hjσ m (hσψ ψσ hψσ hjσ) fun H ↦ hσα ?_
  exact DFunLike.congr_fun H α

variable [Finite A] [SMulCommClass A K R]

/-- The projections of André's tree tower are the components through `andreGroupHomeoLim`. -/
lemma andreTower_ρ (q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (g : andreGroup O R A V hV) :
    (andreTower (R := R) (A := A) V hV hp hR).ρ q g =
      (andreGroupHomeoLim (R := R) (A := A) V hV hp hR g).1 q := rfl

/-- **König for the midpoint system.** If, for the levels `l` over `P`, the sets of stage group
elements fixing `e l` with nontrivial transition to `P` are nonempty, then `stab e ≠ ⊥`. -/
theorem stab_ne_bot_of_nonempty (e : (andreTower (R := R) (A := A) V hV hp hR).Sys)
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (hne : ∀ l (g : l ⟶ P), ∃ γ : stageGroup (tempFibre O R A V hV) l.G,
      (curveData V hV hR l).stageTree V hV γ (e.1 l) = e.1 l ∧
        transition (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
          (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 g γ ≠ 1) :
    TreeTower.stab e ≠ ⊥ := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  have hgr := galoisLimitData_galW (R := R) (A := A) V hV hp hR
  haveI := GaloisLimit.subsingleton_hom hgr.2.2
  let T : ∀ l : PtGal (tempFibre O R A V hV) (galW O R A Ω hR),
      Set (stageGroup (tempFibre O R A V hV) l.G) := fun l ↦
    {γ | (curveData V hV hR l).stageTree V hV γ (e.1 l) = e.1 l ∧
      ∀ g : l ⟶ P, transition hgr.1 hgr.2.2 g γ ≠ 1}
  have hfin : ∀ l, (l ⟶ P) → (T l).Finite := fun l _ ↦
    (UData.finite_stab V hV (curveData V hV hR l) (e.1 l)).subset fun γ hγ ↦ hγ.1
  have hne' : ∀ l, (l ⟶ P) → (T l).Nonempty := by
    intro l g
    obtain ⟨γ, h₁, h₂⟩ := hne l g
    exact ⟨γ, h₁, fun g' ↦ Subsingleton.elim g g' ▸ h₂⟩
  have hT : ∀ {l l' : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (f : l ⟶ l'),
      (l' ⟶ P) → ∀ γ ∈ T l, transition hgr.1 hgr.2.2 f γ ∈ T l' := by
    intro l l' f _ γ hγ
    refine ⟨?_, fun g' ↦ ?_⟩
    · have h := curveTower_map_stageTree V hV hp hR f γ (e.1 l)
      rw [hγ.1] at h
      have he := e.2 f
      change (curveData V hV hR l).vmapHom (curveData V hV hR l') (ptHomMor V hV f) (e.1 l) =
        e.1 l' at he
      rw [he] at h
      exact h.symm
    · rw [← transition_comp]
      exact hγ.2 (f ≫ g')
  obtain ⟨g, hg⟩ := exists_andreGroup_mem V hV hp hR P T hfin hne' hT
  have hstab : g ∈ TreeTower.stab e := by
    refine TreeTower.mem_stab.2 fun j ↦ ?_
    obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j P
    have hk : (andreTower (R := R) (A := A) V hV hp hR).ρ k g • e.1 k = e.1 k := (hg k b).1
    rw [← e.2 a, ← (andreTower (R := R) (A := A) V hV hp hR).map_smul, hk]
  refine fun hbot ↦ (hg P (𝟙 P)).2 (𝟙 P) ?_
  have h1 : g = 1 := by
    have := hbot ▸ hstab
    exact (Subgroup.mem_bot.1 this)
  rw [transition_id, h1, map_one]
  rfl

/-- **Midpoint systems of adjacent verticial systems have nontrivial stabilizers.** -/
theorem stab_ne_bot_of_mid {s s' e : (andreTower (R := R) (A := A) V hV hp hR).Sys}
    (hs : TreeTower.IsVert s) (hne : s ≠ s')
    (hmid : ∀ k, s.1 k ≠ s'.1 k → ((andreTower (R := R) (A := A) V hV hp hR).graph k).Adj
      (s.1 k) (e.1 k) ∧ ((andreTower (R := R) (A := A) V hV hp hR).graph k).Adj (e.1 k) (s'.1 k)) :
    TreeTower.stab e ≠ ⊥ := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, s.1 j ≠ s'.1 j := by
    by_contra! hc
    exact hne (TreeTower.Sys.ext hc)
  have hadj : ∀ {l} (f : l ⟶ j₀), ((andreTower (R := R) (A := A) V hV hp hR).graph l).Adj
      (s.1 l) (e.1 l) := fun f ↦ (hmid _ (TreeTower.ne_of_ne f hj₀)).1
  have hej₀ : (andreTower (R := R) (A := A) V hV hp hR).kind j₀ (e.1 j₀) = false := by
    have := (andreTower (R := R) (A := A) V hV hp hR).kind_adj j₀ _ _ (hadj (𝟙 j₀))
    rw [hs j₀] at this
    simpa using this
  set D₀ := curveData V hV hR j₀
  set W₀ := (WData.nonempty_of_isW (curveData_isW V hV hR j₀)).some
  haveI := W₀.isDomain
  haveI : FaithfulSMul D₀.Lv.L.B (FractionRing D₀.Lv.L.B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  have hζ := D₀.closure_vertexPt_mem (hs j₀)
  obtain ⟨V₀, hV₀⟩ := exists_isCentre (D₀.Lv.gen (FractionRing D₀.Lv.L.B))
    (D₀.Lv.gen_specializes (FractionRing D₀.Lv.L.B) (D₀.vertexPt (s.1 j₀)))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  haveI := W₀.isDiscreteValuationRing_of_isCentre (FractionRing D₀.Lv.L.B) _ hζ hV₀
  obtain ⟨t, ht, u, n, hn, hπ⟩ :=
    W₀.exists_eq_unit_mul_pow_of_isCentre (FractionRing D₀.Lv.L.B) _ hζ hV₀ ϖ hϖ
  obtain ⟨ℓ, hnℓ, hℓ⟩ := Nat.exists_infinite_primes (n + 1)
  have hK := SemistableReduction.KummerValuation.kummer_of_isDiscreteValuationRing ht u hn hnℓ hπ
  have hc : (ϖ : K) ≠ 0 := fun h0 ↦ hϖ.ne_zero (Subtype.ext h0)
  obtain ⟨P, hP, α, hα⟩ := exists_ptGal_pow_eq V hV hp hR j₀ hℓ.ne_zero (ϖ : K)
  refine stab_ne_bot_of_nonempty V hV hp hR e P fun l g ↦ ?_
  exact exists_stage_fix_transition_ne_one_of_kummer V hV hp hR hP g (hadj (g ≫ hP)) (hs l)
    (s.2 (g ≫ hP)) (e.2 (g ≫ hP)) (hs j₀) hej₀ hV₀ hℓ hc hK hα

/-- **M2.6: adjacent verticial subgroups of André's group intersect nontrivially**
(`TreeTower.LimAdjInf` for André's tree tower, unconditionally). -/
theorem limAdjInf_andreTower : (andreTower (R := R) (A := A) V hV hp hR).LimAdjInf := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  exact TreeTower.limAdjInf_of_mid (isFunctorial_andreTower_galW V hV hp hR)
    (noBranchSwap_andreTower V hV hp hR) fun _ _ _ hs _ h hmid ↦
      stab_ne_bot_of_mid V hV hp hR hs h.1 hmid

/-! ### Consumers without the hypothesis on edge-like subgroups -/

/-- **`PSCAdj` for André's group from estrangement alone.** -/
theorem pscAdj_andreTower_of_estranged''
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged) :
    (andreTower (R := R) (A := A) V hV hp hR).PSCAdj :=
  TreeTower.pscAdj_of_estranged_of_limAdjInf hE (limAdjInf_andreTower V hV hp hR)

/-- **CG3' for André's group from estrangement alone**, against an estranged tree tower
satisfying the restricted edge hypothesis. -/
theorem isGraphic_iff_andreTower_of_limAdjInf {Γ' : Type*} [Group Γ'] {J' : Type*}
    [Category J'] {T' : TreeTower Γ' J'} {α : andreGroup O R A V hV ≃* Γ'}
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged) (hE' : T'.Estranged)
    (hL' : T'.LimAdjInf) :
    TreeTower.IsGraphic (andreTower (R := R) (A := A) V hV hp hR) T' α ↔
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR) T' α :=
  TreeTower.isGraphic_iff_of_estranged_of_limAdjInf hE hE' (limAdjInf_andreTower V hV hp hR) hL'

/-- **CG3' between the André groups of two curves from estrangement alone.** -/
theorem isGraphic_iff_andreTower_andreTower'
    {K₂ : Type u} [Field K₂] [CharZero K₂] {O₂ : ValuationSubring K₂}
    [IsDiscreteValuationRing O₂] [IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂]
    [PerfectField (IsLocalRing.ResidueField O₂)]
    {R₂ : Type u} [CommRing R₂] [Algebra K₂ R₂] [Algebra.Smooth K₂ R₂] [IsDomain R₂]
    {A₂ : Type u} [Group A₂] [MulSemiringAction A₂ R₂] [Subsingleton A₂] [Finite A₂]
    [SMulCommClass A₂ K₂ R₂]
    {Ω₂ : Type u} [Field Ω₂] [IsAlgClosed Ω₂] [Algebra K₂ Ω₂] [Algebra R₂ Ω₂]
    [IsScalarTower K₂ R₂ Ω₂] (V₂ : ValuationSubring Ω₂) (hV₂ : V₂.comap (algebraMap K₂ Ω₂) = O₂)
    (hp₂ : ∃ p : ℕ, p.Prime ∧ (p : O₂) ∈ IsLocalRing.maximalIdeal O₂)
    (hR₂ : ringKrullDim R₂ = 1) {α : andreGroup O R A V hV ≃* andreGroup O₂ R₂ A₂ V₂ hV₂}
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (hE₂ : (andreTower (R := R₂) (A := A₂) V₂ hV₂ hp₂ hR₂).Estranged) :
    TreeTower.IsGraphic (andreTower (R := R) (A := A) V hV hp hR)
        (andreTower (R := R₂) (A := A₂) V₂ hV₂ hp₂ hR₂) α ↔
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR)
        (andreTower (R := R₂) (A := A₂) V₂ hV₂ hp₂ hR₂) α :=
  isGraphic_iff_andreTower_of_limAdjInf V hV hp hR hE hE₂ (limAdjInf_andreTower V₂ hV₂ hp₂ hR₂)

/-- **`PSCAdj` for André's group from tame estrangement and M4** (no hypothesis on edge-like
subgroups). -/
theorem pscAdj_andreTower_of_tame_wild'
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop)
    (hT : TameEstrangement V hV hp hR ⊤ P) (hW : WildEstrangement V hV hp hR ⊤ P) :
    (andreTower (R := R) (A := A) V hV hp hR).PSCAdj :=
  pscAdj_andreTower_of_estranged'' V hV hp hR ((estranged_andreTower_iff V hV hp hR P).2 ⟨hT, hW⟩)

/-- **CG3' for André's group from tame estrangement and M4**, against an estranged tree tower
satisfying the restricted edge hypothesis. -/
theorem isGraphic_iff_andreTower_of_tame_wild' {Γ' : Type*} [Group Γ'] {J' : Type*}
    [Category J'] {T' : TreeTower Γ' J'} {α : andreGroup O R A V hV ≃* Γ'}
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop)
    (hT : TameEstrangement V hV hp hR ⊤ P) (hW : WildEstrangement V hV hp hR ⊤ P)
    (hE' : T'.Estranged) (hL' : T'.LimAdjInf) :
    TreeTower.IsGraphic (andreTower (R := R) (A := A) V hV hp hR) T' α ↔
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR) T' α :=
  isGraphic_iff_andreTower_of_limAdjInf V hV hp hR
    ((estranged_andreTower_iff V hV hp hR P).2 ⟨hT, hW⟩) hE' hL'

section Double

open TateObject

variable (D : DoubleData O R) (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)

/-- **`PSCAdj` for André's group of a Tate curve from the wild Tate part alone.** -/
theorem pscAdj_andreTower_of_tateWild' (hW : TateWildPart (A := A) V hV hp hR D s hs ⊤) :
    (andreTower (R := R) (A := A) V hV hp hR).PSCAdj :=
  pscAdj_andreTower_of_estranged'' V hV hp hR
    ((estranged_andreTower_iff_tateWild V hV hp hR D s hs).2 hW)

/-- **CG3' for André's group of a Tate curve from the wild Tate part alone**, against an
estranged tree tower satisfying the restricted edge hypothesis. -/
theorem isGraphic_iff_andreTower_of_tateWild' {Γ' : Type*} [Group Γ'] {J' : Type*}
    [Category J'] {T' : TreeTower Γ' J'} {α : andreGroup O R A V hV ≃* Γ'}
    (hW : TateWildPart (A := A) V hV hp hR D s hs ⊤) (hE' : T'.Estranged) (hL' : T'.LimAdjInf) :
    TreeTower.IsGraphic (andreTower (R := R) (A := A) V hV hp hR) T' α ↔
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR) T' α :=
  isGraphic_iff_andreTower_of_limAdjInf V hV hp hR
    ((estranged_andreTower_iff_tateWild V hV hp hR D s hs).2 hW) hE' hL'

end Double

end Andre

end

end TemperedFundamentalGroups
