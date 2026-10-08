/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentDisc
import TemperedFundamentalGroups.SemistableReduction.W7Statement
import TemperedFundamentalGroups.SemistableReduction.SmoothLemma

/-!
# Descent of smooth points to a discretely valued subfield (W10, smooth part)

Blueprint §9.12 (O7), the one-branch analogue of O1 (S7.9 + S9). Setting of `DVRDescentDisc`:
`φ : E → C` isometric (`O_E` a DVR with uniformizer `ϖ`), `χ : F₀ → F'` compatible,
`BD = DRint 0 1 F₀` the integral closure of `O_E[x]` in `F₀`, `ιD : BD → R' = DRint 0 1 F'`.

**`isSemistableAt_of_isDiscSmooth` (S)**: let `P'` be a maximal ideal of `R'` over `(𝔪_C, x)` at
which the special fibre over `C` is smooth (`SmoothVertex.IsDiscSmooth`: one branch `(v, Q)`,
reduction local ring `O_Q`). Assume `E` is large enough:
* `[F₀ : E(x)] = [F' : C(x)]`, `F' = C(x)(χ θ₀)` (`hdeg`, `hθ`);
* restriction to `F₀` is injective on the vertices and the residues over `E` generate the
  residue fields over `C` (`hinj`, `hgen`, D3c/D3d: then `e = 1` and linear disjointness);
* the reductions of `R'` at any two vertices are `k`-spanned by reductions of `ιD(BD)`
  (`hspan`, D3e; `exists_spanningD` provides finitely many generators to put into `BD`);
* the point `𝔭 = ιD⁻¹ P'` is `κ_E`-rational (`hrat`, S7.9 (iv)).
Then `BD` is étale-locally `O_E[u]` at `𝔭`: `IsSemistableAt ϖ 𝔭`.

Proof: a uniformizer `u ∈ BD` of the branch exists (spanning + rationality: a `k`-combination of
reductions of `BD` vanishing at `Q` to order `1`); for `z ∈ 𝔭`, `z / u` reduces into `O_Q`, so
`IsDiscSmooth` gives a witness `(y, s)` over `R'`, which descends to `BD`
(`ConstantDescent.exists_fp_descent`, linear disjointness); elements killing the other vertices
outside `P'` (`exists_mem_ker_notMemD`) descend likewise, and the kernel lemma
(`exists_eq_cst_mulD`) gives `t z ∈ ϖ BD + u BD` with `t ∉ 𝔭`. So the maximal ideal of `BD_𝔭` is
`(ϖ, u)`, the residue field is `κ_E`, and the smooth-point lemma
(`isSemistableAt_of_maximalIdeal_eq_span`) applies.
-/

open NNReal Polynomial IsLocalRing Valuation WithZero

namespace SemistableReduction

namespace DVRDescent

open GaussTube DiscCount SmoothVertex FundamentalInequality GaussStability GaussFibre PlaceNorm
  ConstantDescent

universe u w

/-- The residue map of a place, as a ring homomorphism on its valuation ring. -/
noncomputable def curveResHom {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
    [IsCurveFunctionField k κ] (Q : CurvePlace k κ) : Q.V.toSubring →+* k where
  toFun y := Q.res y
  map_one' := Q.res_one
  map_mul' y z := Q.res_mul y.2 z.2
  map_zero' := Q.res_zero
  map_add' y z := Q.res_add y.2 z.2

lemma le_exp_neg_one {x : ℤᵐ⁰} (h : x < 1) : x ≤ exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← exp_log hx] at h ⊢
    rw [← exp_zero, exp_lt_exp] at h
    rw [exp_le_exp]
    omega

lemma eq_exp_neg_one {x : ℤᵐ⁰} (h1 : x < 1) (h2 : ¬ x ≤ exp (-2)) : x = exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact absurd zero_le h2
  · rw [← exp_log hx] at h1 h2 ⊢
    rw [← exp_zero, exp_lt_exp] at h1
    rw [exp_le_exp] at h2
    rw [exp_inj]
    omega

section Main

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {E : Type w} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  {F₀ : Type w} [Field F₀] [Algebra (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  [Algebra.IsSeparable (RatFunc E) F₀] {χ : F₀ →+* F'} (hχ : IsCompat φ χ)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) F']
  [FiniteDimensional (RatFunc E) F₀] [Algebra.IsSeparable (RatFunc E) F₀] in
include hφ in
lemma norm_map_le_one (e : HenselComplete.integers E) :
    φ e ∈ HenselComplete.integers C := by
  rw [HenselComplete.mem_integers_iff, hφ]
  exact HenselComplete.norm_le_one e

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) F']
  [FiniteDimensional (RatFunc E) F₀] [Algebra.IsSeparable (RatFunc E) F₀] in
lemma ιD_cstD (e : HenselComplete.integers E) :
    ιD χ hφ hχ (cstD e) = constD ⟨φ e, norm_map_le_one hφ e⟩ := by
  apply Subtype.ext
  rw [coe_ιD, coe_cstD, χ_cst hχ]
  change _ = algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) (φ e))
  rw [← IsScalarTower.algebraMap_apply]

omit [IsAlgClosed C] [CharZero C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] [FiniteDimensional (RatFunc E) F₀]
  [Algebra.IsSeparable (RatFunc E) F₀] in
lemma constD_mem {P' : Ideal (DRint (0 : C) 1 F')}
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F')) = discIdeal (0 : C) 1)
    {b : HenselComplete.integers C} (hb : ‖(b : C)‖ < 1) : constD b ∈ P' := by
  change algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F') ⟨_, algebraMap_mem_discRing' b⟩ ∈ P'
  rw [← Ideal.mem_comap, hP']
  refine ⟨Polynomial.C (b : C), fun i ↦ ?_, by rw [aeval_C], ?_⟩
  · rw [coeff_C]
    split_ifs
    · exact_mod_cast HenselComplete.norm_le_one b
    · simp only [nnnorm_zero, zero_le]
  · rw [coeff_C_zero]
    exact_mod_cast hb

omit [IsAlgClosed C] [CharZero C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] [FiniteDimensional (RatFunc E) F₀]
  [Algebra.IsSeparable (RatFunc E) F₀] in
lemma xD_mem {P' : Ideal (DRint (0 : C) 1 F')}
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F')) = discIdeal (0 : C) 1) :
    xD ∈ P' := by
  change algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F') ⟨RatFunc.X, X_mem_discRing⟩ ∈ P'
  rw [← Ideal.mem_comap, hP']
  refine ⟨Polynomial.X, fun i ↦ ?_, by rw [aeval_X, gaussCoord_zero_one], by simp⟩
  rw [coeff_X]
  split_ifs <;> simp

omit [CharZero C] [FiniteDimensional (RatFunc E) F₀] [Algebra.IsSeparable (RatFunc E) F₀] in
/-- An element of `BD` whose reduction has order `1` at a branch is transcendental over `O_E`. -/
lemma transcendental_of_valuation_eq {v : Ext C F'}
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)} {u : BD E F₀}
    (hu : Q.valuation (redD v (ιD χ hφ hχ u)) = exp (-1)) :
    letI := bdAlgebra (E := E) (F₀ := F₀)
    Transcendental (HenselComplete.integers E) u := by
  letI := bdAlgebra (E := E) (F₀ := F₀)
  rintro ⟨P, hP0, hPu⟩
  set ψ : HenselComplete.integers E →+* C := φ.comp (HenselComplete.integers E).subtype
  have hψ : Function.Injective ψ := φ.injective.comp Subtype.val_injective
  have hcomp : χ.comp ((BD E F₀).val.toRingHom.comp (algebraMap (HenselComplete.integers E)
      (BD E F₀))) = (algebraMap C F').comp ψ := by
    ext e
    change χ (cst (e : E)) = _
    rw [χ_cst hχ]
    rfl
  have h0 : aeval (χ u) (P.map ψ) = 0 := by
    have := congrArg (fun z : BD E F₀ ↦ χ (z : F₀)) hPu
    simp only [map_zero, ZeroMemClass.coe_zero] at this
    rw [← this, aeval_def, eval₂_map, aeval_def]
    change _ = χ ((BD E F₀).val.toRingHom (eval₂ _ _ _))
    rw [hom_eval₂, hom_eval₂, hcomp]
    rfl
  have halg : IsAlgebraic C (χ u) :=
    ⟨P.map ψ, (Polynomial.map_ne_zero_iff hψ).2 hP0, h0⟩
  have hint := halg.isIntegral
  obtain ⟨c, hc⟩ : (χ u) ∈ (algebraMap C F').range :=
    minpoly.mem_range_of_degree_eq_one C _
      (IsAlgClosed.degree_eq_one_of_irreducible C (minpoly.irreducible hint))
  have hle := valuation_le_one_D v (ιD χ hφ hχ u)
  change v.1 (χ u) ≤ 1 at hle
  have hcn : v.1 (algebraMap C F' c) = ‖c‖₊ := by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F', valuation_algebraMap,
      gauss1_algebraMap_C]
  rw [← hc, hcn] at hle
  have hred : redD v (ιD χ hφ hχ u) = algebraMap 𝓀 _
      (residue (HenselComplete.integers C) ⟨c, by simpa using hle⟩) := by
    change red C (χ u) v = _
    rw [← hc, red_algebraMap_C c hle]
  rw [hred] at hu
  by_cases h0 : residue (HenselComplete.integers C) ⟨c, by simpa using hle⟩ = 0
  · rw [h0, map_zero, map_zero] at hu
    exact exp_ne_zero hu.symm
  · rw [valuation_algebraMap_eq_one Q.valuation_algebraMap_le_one h0] at hu
    have := congrArg log hu
    simp at this

set_option maxHeartbeats 800000 in
-- the proof assembles many reductions in one context
include hp hp1 in
/-- **Descent of a smooth point to `O_E` (S)**: at the point `𝔭 = ιD⁻¹ P'` of the vertex chart
`BD` over `O_E`, under a point `P'` of `R'` over `(𝔪_C, x)` at which the special fibre over `C`
is smooth, `BD` is étale-locally the affine line `O_E[u]`, provided `E` is large enough
(`hdeg`, `hθ`, `hinj`, `hgen`, `hspan`) and `𝔭` is `κ_E`-rational (`hrat`). -/
theorem isSemistableAt_of_isDiscSmooth [IsDiscreteValuationRing (HenselComplete.integers E)]
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    (hinj : ∀ W W' : Ext C F', W.1.comap χ = W'.1.comap χ → W = W')
    (hgen : ∀ W : Ext C F', IntermediateField.adjoin 𝓀
      (resE χ W : Set (ResidueField W.1.valuationSubring)) = ⊤)
    (hspan : ∀ v₁ v₂ : Ext C F', ∀ y,
      IsSpanned 𝓀 (ιD χ hφ hχ (F₀ := F₀)).range (redD v₁) (redD v₂) y)
    {ϖ : HenselComplete.integers E} (hϖ : Irreducible ϖ)
    (P' : Ideal (DRint (0 : C) 1 F')) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F')) = discIdeal (0 : C) 1)
    (hsm : IsDiscSmooth P')
    (hrat : ∀ z : BD E F₀, ∃ e : HenselComplete.integers E, ιD χ hφ hχ (z - cstD e) ∈ P') :
    letI := bdAlgebra (E := E) (F₀ := F₀)
    IsSemistableAt ϖ (P'.comap (ιD χ hφ hχ)) := by
  classical
  letI := bdAlgebra (E := E) (F₀ := F₀)
  haveI := finiteType_BD (E := E) (F₀ := F₀)
  set ι := ιD χ hφ hχ (F₀ := F₀) with hιdef
  set 𝔭 := P'.comap ι with h𝔭
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime ι P'
  obtain ⟨⟨v, Q, hQ⟩, hb, hloc⟩ := hsm
  set ρ := redD (F' := F') v with hρ
  have hPQ : placeIdealD v hQ = P' := by
    have : (⟨v, Q, hQ⟩ : OuterBranch C F') ∈ discBranches P' := by
      rw [hb]; exact Set.mem_singleton _
    exact this
  have hV : ∀ y, ρ y ∈ Q.V := fun y ↦ redD_mem_V v y (xbar_mem_V v hQ)
  have hmemP : ∀ y, y ∈ P' ↔ Q.valuation (ρ y) < 1 := fun y ↦ by
    rw [← hPQ, mem_placeIdealD_iff, CurvePlace.res_eq_zero_iff Q (hV y)]
  have hle1 : ∀ y, Q.valuation (ρ y) ≤ 1 := fun y ↦ Q.valuation_le_one_iff.2 (hV y)
  have hr0 : ∀ y, curveResHom Q ⟨ρ y, hV y⟩ ≠ 0 ↔ y ∉ P' := fun y ↦ by
    rw [hmemP, ← CurvePlace.res_eq_zero_iff Q (hV y)]
    rfl
  -- the uniformizer of `O_E`
  have hϖ0 : (ϖ : E) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hϖ1 : ‖(ϖ : E)‖ < 1 :=
    (HenselComplete.mem_maximalIdeal_iff_norm_lt_one ϖ).1 ((mem_maximalIdeal _).2 hϖ.not_isUnit)
  have hϖE : ∀ e : E, ‖e‖ < 1 → ‖e‖ ≤ ‖(ϖ : E)‖ := by
    intro e he
    have hmem : (⟨e, (HenselComplete.mem_integers_iff e).2 he.le⟩ : HenselComplete.integers E) ∈
        maximalIdeal _ := (HenselComplete.mem_maximalIdeal_iff_norm_lt_one _).2 he
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
    obtain ⟨o, ho⟩ := hmem
    have := congrArg (fun x : HenselComplete.integers E ↦ ‖(x : E)‖) ho
    simp only [MulMemClass.coe_mul, norm_mul] at this
    rw [← this]
    exact mul_le_of_le_one_left (norm_nonneg _) (HenselComplete.norm_le_one o)
  -- `e = 1`, linear disjointness, constants
  have heo := exists_valuation_eq hp hp1 hφ hχ hdeg hinj hgen
  letI := kEAlgebra φ
  have hLD : ∀ W : Ext C F', LinDisj (kE φ) 𝓀 (resE χ W) := fun W ↦
    linDisj_resE hp hp1 hφ hχ hdeg hinj hgen W
  have hM : ∀ W : Ext C F', ∀ b ∈ ι.range, redD W b ∈ resE χ W := by
    rintro W _ ⟨z, rfl⟩
    exact ⟨z, valuation_le_one_D W (ι z), rfl⟩
  have hcst : ∀ c : kE φ, ∃ e : HenselComplete.integers E, ∀ W : Ext C F',
      redD W (ι (cstD e)) = algebraMap 𝓀 (ResidueField W.1.valuationSubring)
        (algebraMap (kE φ) 𝓀 c) := by
    intro c
    obtain ⟨a, rfl⟩ := residue_surjective c
    have ha : ‖(a : E)‖ ≤ 1 := by
      have : vE φ a ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 a.2
      simp only [vE, Valuation.comap_apply, NormedField.valuation_apply] at this
      rw [← hφ]
      exact_mod_cast this
    refine ⟨⟨a, (HenselComplete.mem_integers_iff _).2 ha⟩, fun W ↦ ?_⟩
    rw [hιdef, ιD_cstD, redD_constD]
    rfl
  have hconstB : ∀ W W' : Ext C F', ∀ c : kE φ, ∃ o ∈ ι.range,
      redD W o = algebraMap 𝓀 _ (algebraMap (kE φ) 𝓀 c) ∧
        redD W' o = algebraMap 𝓀 _ (algebraMap (kE φ) 𝓀 c) := by
    intro W W' c
    obtain ⟨e, he⟩ := hcst c
    exact ⟨ι (cstD e), ⟨_, rfl⟩, he W, he W'⟩
  -- a uniformizer of the branch in `BD`
  obtain ⟨π, hπ⟩ := Q.exists_valuation_eq_exp_neg_one
  have hπV : π ∈ Q.V := Q.valuation_le_one_iff.1 (by rw [hπ, ← exp_zero, exp_le_exp]; omega)
  obtain ⟨y, s, hs, hys⟩ := hloc π hπV
  have hsval : Q.valuation (ρ s) = 1 :=
    le_antisymm (hle1 s) (not_lt.1 fun h ↦ hs ((hmemP s).2 h))
  have hyval : Q.valuation (ρ y) = exp (-1) := by
    rw [show ρ y = π * ρ s from hys, map_mul, hπ, hsval, mul_one]
  obtain ⟨n, lam, bb, hbb, hy1, -⟩ := hspan v v y
  choose z hz using fun j ↦ hbb j
  choose e he using fun j ↦ hrat (z j)
  have hdP : ∀ j, Q.valuation (ρ (ι (z j - cstD (e j)))) < 1 := fun j ↦ (hmemP _).1 (he j)
  have hbbj : ∀ j, ρ (bb j) = ρ (ι (z j - cstD (e j))) + algebraMap 𝓀 _
      (residue (HenselComplete.integers C) ⟨φ (e j), norm_map_le_one hφ (e j)⟩) := by
    intro j
    have hc : ι (cstD (e j)) = constD ⟨φ (e j), norm_map_le_one hφ (e j)⟩ := ιD_cstD hφ hχ (e j)
    rw [← hz j]
    rw [_root_.map_sub, _root_.map_sub, hc, hρ, redD_constD]
    ring
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : 𝓀, c₀ = ∑ j, lam j *
      residue (HenselComplete.integers C) ⟨φ (e j), norm_map_le_one hφ (e j)⟩ := ⟨_, rfl⟩
  have hsum : ρ y = ∑ j, algebraMap 𝓀 _ (lam j) * ρ (ι (z j - cstD (e j))) + algebraMap 𝓀 _ c₀ := by
    simp only [← hρ] at hy1
    rw [hy1]
    simp only [hbbj, mul_add, Finset.sum_add_distrib, hc₀def, map_sum, map_mul]
  have hsumlt : Q.valuation (∑ j, algebraMap 𝓀 (ResidueField v.1.valuationSubring) (lam j) *
      ρ (ι (z j - cstD (e j)))) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun j _ ↦ by
      rw [map_mul]
      exact (mul_le_of_le_one_left' (Q.valuation_algebraMap_le_one _)).trans_lt (hdP j)
  have hc₀ : c₀ = 0 := by
    by_contra h
    have h1 := valuation_algebraMap_eq_one Q.valuation_algebraMap_le_one h
    have h2 : algebraMap 𝓀 (ResidueField v.1.valuationSubring) c₀ =
        ρ y - ∑ j, algebraMap 𝓀 _ (lam j) * ρ (ι (z j - cstD (e j))) := by rw [hsum]; ring
    have h3 : Q.valuation (ρ y) < 1 := by rw [hyval, ← exp_zero, exp_lt_exp]; omega
    rw [h2] at h1
    exact absurd h1 ((Valuation.map_sub _ _ _).trans_lt (max_lt h3 hsumlt)).ne
  have hsum' : ρ y = ∑ j, algebraMap 𝓀 _ (lam j) * ρ (ι (z j - cstD (e j))) := by
    rw [hsum, hc₀, map_zero, add_zero]
  obtain ⟨j, hj⟩ : ∃ j, ¬ Q.valuation (ρ (ι (z j - cstD (e j)))) ≤ exp (-2) := by
    by_contra! hall
    have : Q.valuation (ρ y) ≤ exp (-2) := by
      rw [hsum']
      exact Valuation.map_sum_le _ fun j _ ↦ by
        rw [map_mul]
        exact (mul_le_of_le_one_left' (Q.valuation_algebraMap_le_one _)).trans (hall j)
    rw [hyval, exp_le_exp] at this
    omega
  obtain ⟨u, hu⟩ : ∃ u : BD E F₀, Q.valuation (ρ (ι u)) = exp (-1) :=
    ⟨z j - cstD (e j), eq_exp_neg_one (hdP j) hj⟩
  have hu0 : ρ (ι u) ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hu
    exact exp_ne_zero hu.symm
  have huP : ι u ∈ P' := (hmemP _).2 (by rw [hu, ← exp_zero, exp_lt_exp]; omega)
  have htr := transcendental_of_valuation_eq hφ hχ hu
  -- elements killing the other vertices outside `P'`
  have hT : ∀ v' : Ext C F', v' ≠ v → ∃ T : BD E F₀, ι T ∉ P' ∧ redD v' (ι T) = 0 := by
    intro v' hv'
    obtain ⟨t, ht0, htP⟩ := exists_mem_ker_notMemD v' (xD_mem hP') (fun Q' hQ' h ↦ hv' (by
      have : (⟨v', Q', hQ'⟩ : OuterBranch C F') ∈ discBranches P' := h
      rw [hb] at this
      exact congrArg Sigma.fst (Set.mem_singleton_iff.1 this)))
    obtain ⟨y'', ⟨T, rfl⟩, s'', -, hs'', hT₁, hT₂⟩ := exists_fp_descent (ρ₁ := ρ)
      (ρ₂ := redD v') (hM v) (hM v') (hLD v) (hLD v') (hconstB v v') Q.V.toSubring
      (curveResHom Q) hV
      Q.algebraMap_mem (a := 1) (b := 0) (one_mem _) (zero_mem _) (hspan v v' t) (hspan v v' t)
      ((hr0 t).2 htP) (by rw [one_mul]) (by rw [ht0, zero_mul])
    refine ⟨T, ?_, by rw [hT₂, zero_mul]⟩
    rw [← hr0]
    have : (⟨ρ (ι T), hV _⟩ : Q.V.toSubring) = ⟨ρ s'', hV _⟩ := Subtype.ext (by
      change ρ (ι T) = ρ s''
      rw [hT₁, one_mul])
    rw [this]
    exact hs''
  choose! Tf hTf using hT
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  haveI : Fintype (Ext C F') := Fintype.ofFinite _
  obtain ⟨Tot, hTotdef⟩ : ∃ T : BD E F₀, T = ∏ v' ∈ Finset.univ.erase v, Tf v' := ⟨_, rfl⟩
  have hTot : ι Tot ∉ P' := by
    rw [hTotdef, map_prod, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨v', hv', hmem⟩
    exact (hTf v' (Finset.ne_of_mem_erase hv')).1 hmem
  -- the key: `t z ∈ ϖ BD + u BD` with `t ∉ 𝔭`
  have hM' : ∀ zz ∈ 𝔭, ∃ ss : BD E F₀, ss ∉ 𝔭 ∧ ∃ y₁ y₂ : BD E F₀,
      ss * zz = cstD ϖ * y₁ + y₂ * u := by
    intro zz hzz
    have hzzP : ι zz ∈ P' := hzz
    obtain ⟨α, hα⟩ : ∃ α, α = ρ (ι zz) / ρ (ι u) := ⟨_, rfl⟩
    have hzα : ρ (ι zz) = α * ρ (ι u) := by rw [hα, div_mul_cancel₀ _ hu0]
    have hαV : α ∈ Q.V := by
      rw [← Q.valuation_le_one_iff, hα, map_div₀, hu,
        div_le_iff₀ (zero_lt_iff.2 exp_ne_zero), one_mul]
      exact le_exp_neg_one ((hmemP _).1 hzzP)
    have huv : v.1 (χ u) = 1 := le_antisymm (valuation_le_one_D v (ι u))
      (not_lt.1 fun h ↦ hu0 ((red_eq_zero_iff (valuation_le_one_D v (ι u))).2 h))
    have huF : (u : F₀) ≠ 0 := by
      intro h
      rw [h, map_zero, Valuation.map_zero] at huv
      exact zero_ne_one huv
    have hαM : α ∈ resE χ v := by
      have h1 : v.1 (χ ((zz : F₀) / u)) ≤ 1 := by
        rw [map_div₀, map_div₀, huv, div_one]
        exact valuation_le_one_D v (ι zz)
      refine ⟨(zz : F₀) / u, h1, ?_⟩
      have := red_mul h1 (valuation_le_one_D v (ι u))
      change red C (χ ((zz : F₀) / u) * χ u) v = red C (χ ((zz : F₀) / u)) v * red C (χ u) v
        at this
      rw [← map_mul, div_mul_cancel₀ _ huF] at this
      rw [hα, eq_div_iff hu0]
      exact this.symm
    obtain ⟨y, s, hs, hys⟩ := hloc α hαV
    obtain ⟨y', ⟨Y, rfl⟩, s', ⟨S, rfl⟩, hS, hY₁, -⟩ := exists_fp_descent (ρ₁ := ρ) (ρ₂ := ρ)
      (hM v) (hM v) (hLD v) (hLD v) (hconstB v v) Q.V.toSubring (curveResHom Q) hV Q.algebraMap_mem
      hαM hαM (hspan v v y) (hspan v v s) ((hr0 s).2 hs) hys hys
    have hSP : ι S ∉ P' := (hr0 _).1 hS
    obtain ⟨w₀, hw₀def⟩ : ∃ w : BD E F₀, w = S * zz - Y * u := ⟨_, rfl⟩
    have hw₀ : ρ (ι w₀) = 0 := by
      simp only [hw₀def, _root_.map_sub, map_mul, hY₁, hzα]
      ring
    have hkill : ∀ v' : Ext C F', v'.1 (χ ((Tot * w₀ : BD E F₀) : F₀)) < 1 := by
      intro v'
      refine (red_eq_zero_iff (valuation_le_one_D v' (ι (Tot * w₀)))).1 ?_
      change redD v' (ι (Tot * w₀)) = 0
      rw [map_mul, map_mul]
      by_cases hv' : v' = v
      · subst hv'
        rw [hw₀, mul_zero]
      · rw [hTotdef, map_prod, map_prod,
          Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hv', Finset.mem_univ _⟩)
          (hTf v' hv').2, zero_mul]
    obtain ⟨y₁, hy₁⟩ := exists_eq_cst_mulD hp hp1 hφ hχ hdeg hθ heo hϖ0 hϖE hkill
    have hy₁' : Tot * w₀ = cstD ϖ * y₁ := Subtype.ext (by rw [hy₁]; rfl)
    refine ⟨Tot * S, ?_, y₁, Tot * Y, ?_⟩
    · change ι (Tot * S) ∉ P'
      rw [map_mul]
      exact fun h ↦ ((inferInstance : P'.IsPrime).mem_or_mem h).elim hTot hSP
    · rw [← hy₁']
      rw [hw₀def]
      ring
  -- the maximal ideal of `BD_𝔭` is `(ϖ, u)`
  have hϖ𝔭 : cstD ϖ ∈ 𝔭 := by
    change ι (cstD ϖ) ∈ P'
    rw [hιdef, ιD_cstD]
    exact constD_mem hP' (by change ‖φ ϖ‖ < 1; rw [hφ]; exact hϖ1)
  have hmax := maximalIdeal_eq_span_of_forall (O := HenselComplete.integers E) 𝔭 (ϖ := ϖ)
    hϖ𝔭 huP hM'
  -- the residue field of `BD_𝔭` is `κ_E`
  have hres := exists_sub_mem_maximalIdeal_of_forall (O := HenselComplete.integers E) 𝔭
    (fun o ho ↦ by
      change ι (cstD o) ∈ P'
      rw [hιdef, ιD_cstD]
      refine constD_mem hP' ?_
      change ‖φ o‖ < 1
      rw [hφ]
      exact (HenselComplete.mem_maximalIdeal_iff_norm_lt_one o).1 ho)
    (fun z ↦ hrat z)
  exact isSemistableAt_of_maximalIdeal_eq_span htr 𝔭 hmax hres

end Main

end DVRDescent

end SemistableReduction
