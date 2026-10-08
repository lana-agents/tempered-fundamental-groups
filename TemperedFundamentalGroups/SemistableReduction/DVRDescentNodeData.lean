/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentAssembly

/-!
# Exact node data from the descent data (O1)

Blueprint §9.12, O1. `nonempty_nodeData`: from the descent data over `E` (the hypotheses of
`DVRDescentAssembly`), the local ring of `B_E` at `P' ∩ B_E` is an ordinary double point over `O_E`
(`exists_node_of_branches`) with exact coordinates `u v = ϖⁿ`, `x = ε u^d`, which give the exact
node data `GaussTube.NodeData` at `P'`.
-/

open NNReal Polynomial IsLocalRing Valuation WithZero

namespace SemistableReduction

namespace DVRDescent

open GaussTube FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm
  ConstantDescent

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* F'}

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Fields

variable {c₀ : E} (hc : ‖φ c₀‖ < 1) (hc0 : φ c₀ ≠ 0) {P' : Ideal (Rint (φ c₀) F')}
  {b₁ : OuterBranch C F'} {b₂ : OuterBranch C (Inv (φ c₀) hc0 F')}
  {ι : BE F₀ c₀ →+* Rint (φ c₀) F'} (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
  (hι : ∀ y, (ι y : F') = χ y)

include hι hχ hφ in
/-- The field `hO₁` of `BranchData` from `descent_res₁`. -/
lemma branchData_hO₁ (hb₁ : outerBranches hc P' = {b₁})
    (hb₂ : innerBranches hc hc0 P' = {b₂})
    (hfpC : ∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b →
      ∃ y s : Rint (φ c₀) F', s ∉ P' ∧ redHom hc b₁.1 y = a * redHom hc b₁.1 s ∧
        redHomInv hc hc0 b₂.1 y = b * redHomInv hc hc0 b₂.1 s)
    (hLD₁ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE χ b₁.1))
    (hLD₂ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE (χInv hc0 χ) b₂.1))
    (hspan : ∀ y, IsSpanned 𝓀 ι.range (redHom hc b₁.1) (redHomInv hc hc0 b₂.1) y)
    (hres : letI := kEAlgebra φ; ∀ b : BE F₀ c₀, ∃ t : kE φ,
      placeHom hc b₁.1 b₁.2.2 (ι b) = algebraMap (kE φ) 𝓀 t)
    (halgk : letI := kEAlgebra φ; Algebra.IsAlgebraic (kE φ) 𝓀)
    (a : placeSub b₁.2.1 (resE χ b₁.1)) :
    letI := algO (F₀ := F₀) c₀
    ∃ o : HenselComplete.integers E,
      placeSubRes (phi₁ hc b₁ hι (algebraMap (HenselComplete.integers E) (BE F₀ c₀) o)) =
        placeSubRes a := by
  letI := algO (F₀ := F₀) c₀
  exact (descent_res₁ hc hc0 hφ hχ hι hb₁ hb₂ hfpC hLD₁ hLD₂ hspan hres halgk a).elim
    fun e h ↦ h.elim fun he h ↦ ⟨⟨e, (HenselComplete.mem_integers_iff _).2 he⟩,
      (congrArg (fun z ↦ placeSubRes (phi₁ hc b₁ hι z)) (algO_apply c₀ _)).trans h⟩

include hι hχ hφ in
/-- The field `hO₂` of `BranchData` from `descent_res₂`. -/
lemma branchData_hO₂ (hb₁ : outerBranches hc P' = {b₁})
    (hb₂ : innerBranches hc hc0 P' = {b₂})
    (hfpC : ∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b →
      ∃ y s : Rint (φ c₀) F', s ∉ P' ∧ redHom hc b₁.1 y = a * redHom hc b₁.1 s ∧
        redHomInv hc hc0 b₂.1 y = b * redHomInv hc hc0 b₂.1 s)
    (hLD₁ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE χ b₁.1))
    (hLD₂ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE (χInv hc0 χ) b₂.1))
    (hspan : ∀ y, IsSpanned 𝓀 ι.range (redHom hc b₁.1) (redHomInv hc hc0 b₂.1) y)
    (hres : letI := kEAlgebra φ; ∀ b : BE F₀ c₀, ∃ t : kE φ,
      placeHom hc b₁.1 b₁.2.2 (ι b) = algebraMap (kE φ) 𝓀 t)
    (halgk : letI := kEAlgebra φ; Algebra.IsAlgebraic (kE φ) 𝓀)
    (b : placeSub b₂.2.1 (resE (χInv hc0 χ) b₂.1)) :
    letI := algO (F₀ := F₀) c₀
    ∃ o : HenselComplete.integers E,
      placeSubRes (phi₁ hc b₁ hι (algebraMap (HenselComplete.integers E) (BE F₀ c₀) o)) =
        placeSubRes b := by
  letI := algO (F₀ := F₀) c₀
  exact (descent_res₂ hc hc0 hφ hχ hι hb₁ hb₂ hfpC hLD₁ hLD₂ hspan hres halgk b).elim
    fun e h ↦ h.elim fun he h ↦ ⟨⟨e, (HenselComplete.mem_integers_iff _).2 he⟩,
      (congrArg (fun z ↦ placeSubRes (phi₁ hc b₁ hι z)) (algO_apply c₀ _)).trans h⟩

include hι hχ hφ in
/-- The field `hker` of `BranchData` from `descent_ker`. -/
lemma branchData_hker [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    [FiniteDimensional (RatFunc E) F₀]
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    (heo : ∀ (v : Ext C F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    (hei : ∀ (v : GaussExtension (0 : C) (invRad hc0 1) F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    {ϖ : HenselComplete.integers E} (hϖ0 : (ϖ : E) ≠ 0)
    (hϖle : ∀ e : E, ‖e‖ < 1 → ‖e‖ ≤ ‖(ϖ : E)‖) (t₀ : BE F₀ c₀) (ht₀ : ι t₀ ∉ P')
    (ht₀o : ∀ v : Ext C F', v ≠ b₁.1 → redHom hc v (ι t₀) = 0)
    (ht₀i : ∀ w : Ext C (Inv (φ c₀) hc0 F'), w ≠ b₂.1 → redHomInv hc hc0 w (ι t₀) = 0)
    (b : BE F₀ c₀) (hb₁ : phi₁ hc b₁ hι b = 0) (hb₂ : phi₂ hc hc0 b₂ hι b = 0) :
    letI := algO (F₀ := F₀) c₀
    ∃ t ∉ P'.comap ι, ∃ z,
      t * b = algebraMap (HenselComplete.integers E) (BE F₀ c₀) ϖ * z := by
  letI := algO (F₀ := F₀) c₀
  exact (descent_ker hc hc0 hφ hχ hι hp hp1 hdeg hθ heo hei hϖ0 hϖle
    (HenselComplete.norm_le_one ϖ) t₀ ht₀o ht₀i b hb₁ hb₂).elim fun z hz ↦
      ⟨t₀, ht₀, z, hz.trans (congrArg (· * z) (algO_apply c₀ ϖ).symm)⟩

end Fields

set_option maxHeartbeats 4000000 in
-- the branch types are elaboration-heavy
/-- **The branch data over `O_E`** at `P' ∩ B_E` (the input of `BranchData.exists_node` and
`BranchData.isAnnulusAt`) from the descent data. -/
theorem branchData [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    [IsDiscreteValuationRing (HenselComplete.integers E)] [FiniteDimensional (RatFunc E) F₀]
    (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    {c₀ : E} (hc : ‖φ c₀‖ < 1) (hc0 : φ c₀ ≠ 0) {P' : Ideal (Rint (φ c₀) F')} [P'.IsMaximal]
    (hODP : IsNodeODP hc hc0 P') {b₁ : OuterBranch C F'} (hb₁ : outerBranches hc P' = {b₁})
    {b₂ : OuterBranch C (Inv (φ c₀) hc0 F')} (hb₂ : innerBranches hc hc0 P' = {b₂})
    {ι : BE F₀ c₀ →+* Rint (φ c₀) F'} (hι : ∀ y, (ι y : F') = χ y)
    (heo : ∀ (v : Ext C F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    (hei : ∀ (v : GaussExtension (0 : C) (invRad hc0 1) F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    (hLD₁ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE χ b₁.1))
    (hLD₂ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE (χInv hc0 χ) b₂.1))
    (t₀ : BE F₀ c₀) (ht₀ : ι t₀ ∉ P')
    (ht₀o : ∀ v : Ext C F', v ≠ b₁.1 → redHom hc v (ι t₀) = 0)
    (ht₀i : ∀ w : Ext C (Inv (φ c₀) hc0 F'), w ≠ b₂.1 → redHomInv hc hc0 w (ι t₀) = 0)
    (yu : BE F₀ c₀) (hyu₁ : b₁.2.1.valuation (redHom hc b₁.1 (ι yu)) = exp (-1))
    (hyu₂ : redHomInv hc hc0 b₂.1 (ι yu) = 0)
    (yv : BE F₀ c₀) (hyv₂ : b₂.2.1.valuation (redHomInv hc hc0 b₂.1 (ι yv)) = exp (-1))
    (hyv₁ : redHom hc b₁.1 (ι yv) = 0)
    (hspan : ∀ y : Rint (φ c₀) F',
      IsSpanned 𝓀 ι.range (redHom hc b₁.1) (redHomInv hc hc0 b₂.1) y)
    (hres : letI := kEAlgebra φ; ∀ b : BE F₀ c₀, ∃ t : kE φ,
      placeHom hc b₁.1 b₁.2.2 (ι b) = algebraMap (kE φ) 𝓀 t)
    (halgk : letI := kEAlgebra φ; Algebra.IsAlgebraic (kE φ) 𝓀)
    {ϖ : HenselComplete.integers E} (hϖ : Irreducible ϖ) :
    letI := algO (F₀ := F₀) c₀
    letI := isLocalRing_placeSub (Q := b₁.2.1) (M := resE χ b₁.1) fun _ ha ↦ resE_inv_mem ha
    letI := isLocalRing_placeSub (Q := b₂.2.1) (M := resE (χInv hc0 χ) b₂.1)
      fun _ ha ↦ resE_inv_mem ha
    ∃ (c₀' : HenselComplete.integers E) (d : ℕ), (c₀' : E) = c₀ ∧
      BranchData (P'.comap ι) (phi₁ hc b₁ hι) (phi₂ hc hc0 b₂ hι) placeSubRes placeSubRes ϖ yu yv
        (algebraMap (nodeRing c₀) (BE F₀ c₀) ⟨RatFunc.X, X_mem_nodeRing c₀⟩)
        (algebraMap (nodeRing c₀) (BE F₀ c₀)
          ⟨algebraMap E (RatFunc E) c₀ / RatFunc.X, div_X_mem_nodeRing c₀⟩) c₀' d := by
  classical
  letI := kEAlgebra φ
  have hc₀0 : c₀ ≠ 0 := by rintro rfl; exact hc0 (map_zero φ)
  have hc₀1 : ‖c₀‖ < 1 := by rw [← hφ]; exact hc
  letI := algO (F₀ := F₀) c₀
  have hϖmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ0 : (ϖ : E) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hϖ1 : ‖(ϖ : E)‖ ≤ 1 := HenselComplete.norm_le_one ϖ
  have hϖlt : ‖(ϖ : E)‖ < 1 := by
    have : ϖ ∈ maximalIdeal (HenselComplete.integers E) := hϖ.not_isUnit
    rw [mem_maximalIdeal, mem_nonunits_iff, HenselComplete.isUnit_iff_norm_eq_one] at this
    exact lt_of_le_of_ne hϖ1 this
  have hϖle : ∀ e : E, ‖e‖ < 1 → ‖e‖ ≤ ‖(ϖ : E)‖ := by
    intro e he
    have hmem : (⟨e, (HenselComplete.mem_integers_iff e).2 he.le⟩ : HenselComplete.integers E) ∈
        maximalIdeal (HenselComplete.integers E) := by
      rw [mem_maximalIdeal, mem_nonunits_iff, HenselComplete.isUnit_iff_norm_eq_one]
      exact he.ne
    rw [hϖmax, Ideal.mem_span_singleton'] at hmem
    obtain ⟨o, ho⟩ := hmem
    have := congrArg (fun x : HenselComplete.integers E ↦ ‖(x : E)‖) ho
    simp only [MulMemClass.coe_mul, norm_mul] at this
    rw [← this]
    exact mul_le_of_le_one_left (norm_nonneg _) (HenselComplete.norm_le_one o)
  -- the branch local rings
  have hM₁ : ∀ a ∈ resE χ b₁.1, a⁻¹ ∈ resE χ b₁.1 := fun a ha ↦ resE_inv_mem ha
  have hM₂ : ∀ a ∈ resE (χInv hc0 χ) b₂.1, a⁻¹ ∈ resE (χInv hc0 χ) b₂.1 :=
    fun a ha ↦ resE_inv_mem ha
  letI := isLocalRing_placeSub (Q := b₁.2.1) hM₁
  letI := isLocalRing_placeSub (Q := b₂.2.1) hM₂
  have hfpC := fp_of_isNodeODP hc hc0 hb₁ hb₂ hODP
  have hP₁ := placeIdeal_eq₁ hc hb₁
  haveI : (P'.comap ι).IsPrime := Ideal.comap_isPrime ι P'
  -- the coordinates `x`, `c/x` of the node
  obtain ⟨xB, hxBdef⟩ : ∃ z : BE F₀ c₀,
      algebraMap (nodeRing c₀) (BE F₀ c₀) ⟨RatFunc.X, X_mem_nodeRing c₀⟩ = z := ⟨_, rfl⟩
  obtain ⟨yB, hyBdef⟩ : ∃ z : BE F₀ c₀, algebraMap (nodeRing c₀) (BE F₀ c₀)
      ⟨algebraMap E (RatFunc E) c₀ / RatFunc.X, div_X_mem_nodeRing c₀⟩ = z := ⟨_, rfl⟩
  have hιx : ι xB = xR (φ c₀) := by
    subst hxBdef
    exact Subtype.ext <|
      (ι_algebraMap hχ hι ⟨RatFunc.X, X_mem_nodeRing c₀⟩).trans (by rw [ratFuncMap_X]; rfl)
  have hιy : ι yB = yR (φ c₀) := by
    subst hyBdef
    exact Subtype.ext <|
      (ι_algebraMap hχ hι ⟨algebraMap E (RatFunc E) c₀ / RatFunc.X, div_X_mem_nodeRing c₀⟩).trans
        (by rw [map_div₀, ratFuncMap_X, ratFuncMap_algebraMap_C]; rfl)
  -- the uniformizers of the two branches
  obtain ⟨d, hd_def⟩ : ∃ d, ord (red C (xF C F') b₁.1) b₁.2.1 = d := ⟨_, rfl⟩
  have hd : 1 ≤ d := hd_def ▸ one_le_ord b₁.2.2
  have hxv : b₁.2.1.valuation (redHom hc b₁.1 (ι xB)) = exp (-(d : ℤ)) := by
    rw [hιx, redHom_xR, ← hd_def]; exact valuation_x b₁.2.2
  have hu0' : redHom hc b₁.1 (ι yu) ≠ 0 := by
    intro h; rw [h, map_zero] at hyu₁; exact exp_ne_zero hyu₁.symm
  -- `η = x̄ / ū^d`
  obtain ⟨η₀, hη₀⟩ : ∃ η₀, redHom hc b₁.1 (ι xB) / redHom hc b₁.1 (ι yu) ^ d = η₀ := ⟨_, rfl⟩
  have hηv : b₁.2.1.valuation η₀ = 1 := by
    rw [← hη₀, map_div₀, map_pow, hxv, hyu₁, ← exp_nsmul,
      show d • (-1 : ℤ) = -(d : ℤ) by simp]
    exact div_self exp_ne_zero
  have hηmem : η₀ ∈ placeSub b₁.2.1 (resE χ b₁.1) := by
    refine ⟨b₁.2.1.valuation_le_one_iff.1 hηv.le, ?_⟩
    rw [← hη₀]
    refine (resE χ b₁.1).mul_mem (red_mem₁ hc b₁ hι xB).2 (hM₁ _ ?_)
    exact (resE χ b₁.1).pow_mem (red_mem₁ hc b₁ hι yu).2 d
  have hη : placeSubRes (⟨η₀, hηmem⟩ : placeSub b₁.2.1 (resE χ b₁.1)) ≠ 0 :=
    res_ne_zero_of_valuation_eq_one hηmem.1 hηv
  have hx₁ : phi₁ hc b₁ hι xB =
      (⟨η₀, hηmem⟩ : placeSub b₁.2.1 (resE χ b₁.1)) * phi₁ hc b₁ hι yu ^ d := by
    apply Subtype.ext
    change redHom hc b₁.1 (ι xB) = η₀ * redHom hc b₁.1 (ι yu) ^ d
    rw [← hη₀, div_mul_cancel₀ _ (pow_ne_zero _ hu0')]
  have hx₂ : phi₂ hc hc0 b₂ hι xB = 0 := by
    apply Subtype.ext
    exact (coe_phi₂ hc hc0 b₂ hι xB).trans ((congrArg (redHomInv hc hc0 b₂.1) hιx).trans
      ((redHomInv_xR hc hc0 b₂.1).trans (ZeroMemClass.coe_zero _).symm))
  have hyB : phi₂ hc hc0 b₂ hι yB ≠ 0 := fun h ↦ by
    have h1 := congrArg Subtype.val h
    have h2 : redHomInv hc hc0 b₂.1 (yR (φ c₀)) = 0 :=
      (congrArg (redHomInv hc hc0 b₂.1) hιy).symm.trans
        ((coe_phi₂ hc hc0 b₂ hι yB).symm.trans (h1.trans (ZeroMemClass.coe_zero _)))
    exact red_xF_ne_zero' _ ((redHomInv_yR hc hc0 b₂.1).symm.trans h2)
  -- the constants
  obtain ⟨c₀', hc₀'def⟩ : ∃ c₀' : HenselComplete.integers E,
      ⟨c₀, (HenselComplete.mem_integers_iff _).2 hc₀1.le⟩ = c₀' := ⟨_, rfl⟩
  have hc₀'E : (c₀' : E) = c₀ := by rw [← hc₀'def]
  have hc₀' : c₀' ≠ 0 := fun h ↦ hc₀0 (by rw [← hc₀'E, h]; rfl)
  have hxy : xB * yB = algebraMap (HenselComplete.integers E) (BE F₀ c₀) c₀' := by
    subst hc₀'def
    rw [← hxBdef, ← hyBdef, algO_apply, cstB, ← map_mul]
    congr 1
    apply Subtype.ext
    change RatFunc.X * (algebraMap E (RatFunc E) c₀ / RatFunc.X) = algebraMap E (RatFunc E) c₀
    rw [mul_div_cancel₀ _ RatFunc.X_ne_zero]
  have hϖB : algebraMap (HenselComplete.integers E) (BE F₀ c₀) ϖ = cstB (ϖ : E) hϖ1 :=
    algO_apply c₀ ϖ
  have hresϖ : residue (HenselComplete.integers C)
      ⟨φ ϖ, (HenselComplete.mem_integers_iff _).2 (by rw [hφ]; exact hϖ1)⟩ = 0 := by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      HenselComplete.isUnit_iff_norm_eq_one]
    change ‖φ (ϖ : E)‖ ≠ 1
    rw [hφ]; exact hϖlt.ne
  have hϖ₁ : phi₁ hc b₁ hι (algebraMap (HenselComplete.integers E) (BE F₀ c₀) ϖ) = 0 := by
    refine Subtype.ext ((coe_phi₁ hc b₁ hι _).trans ?_)
    refine (congrArg (redHom hc b₁.1) ((congrArg ι hϖB).trans (ι_cstB hφ hχ hι _ hϖ1))).trans ?_
    refine (redHom_constR hc b₁.1 _).trans ?_
    exact ((congrArg (algebraMap 𝓀 _) hresϖ).trans (map_zero _)).trans
      (ZeroMemClass.coe_zero _).symm
  have hϖ₂ : phi₂ hc hc0 b₂ hι (algebraMap (HenselComplete.integers E) (BE F₀ c₀) ϖ) = 0 := by
    refine Subtype.ext ((coe_phi₂ hc hc0 b₂ hι _).trans ?_)
    refine (congrArg (redHomInv hc hc0 b₂.1)
      ((congrArg ι hϖB).trans (ι_cstB hφ hχ hι _ hϖ1))).trans ?_
    refine (redHomInv_constR hc hc0 b₂.1 _).trans ?_
    exact ((congrArg (algebraMap 𝓀 _) hresϖ).trans (map_zero _)).trans
      (ZeroMemClass.coe_zero _).symm
  have hϖB0 : algebraMap (HenselComplete.integers E) (BE F₀ c₀) ϖ ≠ 0 := by
    intro h
    have := congrArg (fun z : BE F₀ c₀ ↦ χ (z : F₀)) h
    simp only [hϖB, ZeroMemClass.coe_zero, map_zero] at this
    rw [show ((cstB (ϖ : E) hϖ1 : BE F₀ c₀) : F₀) = cst (ϖ : E) from rfl, χ_cst hχ,
      map_eq_zero_iff _ (algebraMap C F').injective, map_eq_zero_iff _ φ.injective] at this
    exact hϖ0 this
  have hker := branchData_hker hc hc0 hφ hχ hι hp hp1 hdeg hθ heo hei hϖ0 hϖle t₀ ht₀ ht₀o ht₀i
  have hO₁ := branchData_hO₁ hc hc0 hφ hχ hι hb₁ hb₂ hfpC hLD₁ hLD₂ hspan hres halgk
  have hO₂ := branchData_hO₂ hc hc0 hφ hχ hι hb₁ hb₂ hfpC hLD₁ hLD₂ hspan hres halgk
  have h𝔭 : ∀ b, b ∈ P'.comap ι ↔ placeSubRes (phi₁ hc b₁ hι b) = 0 := by
    intro b
    have := notMem_iff₁ hc hb₁ (ι b)
    rw [Ideal.mem_comap, placeSubRes_phi₁]
    tauto
  have hv0 : phi₂ hc hc0 b₂ hι yv ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    change redHomInv hc hc0 b₂.1 (ι yv) = 0 at this
    rw [this, map_zero] at hyv₂
    exact exp_ne_zero hyv₂.symm
  subst hxBdef hyBdef
  exact ⟨c₀', d, hc₀'E, ⟨placeSubRes_eq_zero_iff hM₁, placeSubRes_eq_zero_iff hM₂,
    fun b ↦ (placeSubRes_phi₁ hc b₁ hι b).trans ((placeHom_eq_innerRes hc hc0 hb₁ hb₂ _).trans
      (placeSubRes_phi₂ hc hc0 b₂ hι b).symm), h𝔭, hϖ, hϖB0, hϖ₁, hϖ₂, hker,
    fun a b hab ↦ descent_fp hc hc0 hφ hχ hι hb₁ hfpC hLD₁ hLD₂ hspan a b hab, hO₁,
    hO₂, maximalIdeal_placeSub hM₁ hyu₁, Subtype.ext hyu₂, maximalIdeal_placeSub hM₂ hyv₂,
    Subtype.ext hyv₁, fun h ↦ hu0' (congrArg Subtype.val h), hv0, hc₀', hxy, hd,
    ⟨_, hη, hx₁⟩, hx₂, hyB⟩⟩

set_option maxHeartbeats 4000000 in
-- the branch types are elaboration-heavy
/-- **Exact node data from the descent data** (the local assembly of O1). -/
theorem nonempty_nodeData [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    [IsDiscreteValuationRing (HenselComplete.integers E)] [FiniteDimensional (RatFunc E) F₀]
    [Algebra.IsSeparable (RatFunc E) F₀] (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    {c₀ : E} {c : C} (hcc : φ c₀ = c) (hc : ‖c‖ < 1) (hc0 : c ≠ 0)
    {P' : Ideal (Rint c F')} [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c)
    (hODP : IsNodeODP hc hc0 P') {b₁ : OuterBranch C F'} (hb₁ : outerBranches hc P' = {b₁})
    {b₂ : OuterBranch C (Inv c hc0 F')} (hb₂ : innerBranches hc hc0 P' = {b₂})
    (ι : BE F₀ c₀ →+* Rint c F') (hι : ∀ y, (ι y : F') = χ y)
    (heo : ∀ (v : Ext C F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    (hei : ∀ (v : GaussExtension (0 : C) (invRad hc0 1) F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    (hLD₁ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE χ b₁.1))
    (hLD₂ : letI := kEAlgebra φ; LinDisj (kE φ) 𝓀 (resE (χInv hc0 χ) b₂.1))
    (t₀ : BE F₀ c₀) (ht₀ : ι t₀ ∉ P')
    (ht₀o : ∀ v : Ext C F', v ≠ b₁.1 → redHom hc v (ι t₀) = 0)
    (ht₀i : ∀ w : Ext C (Inv c hc0 F'), w ≠ b₂.1 → redHomInv hc hc0 w (ι t₀) = 0)
    (yu : BE F₀ c₀) (hyu₁ : b₁.2.1.valuation (redHom hc b₁.1 (ι yu)) = exp (-1))
    (hyu₂ : redHomInv hc hc0 b₂.1 (ι yu) = 0)
    (yv : BE F₀ c₀) (hyv₂ : b₂.2.1.valuation (redHomInv hc hc0 b₂.1 (ι yv)) = exp (-1))
    (hyv₁ : redHom hc b₁.1 (ι yv) = 0)
    (hspan : ∀ y : Rint c F', IsSpanned 𝓀 ι.range (redHom hc b₁.1) (redHomInv hc hc0 b₂.1) y)
    (hres : letI := kEAlgebra φ; ∀ b : BE F₀ c₀, ∃ t : kE φ,
      placeHom hc b₁.1 b₁.2.2 (ι b) = algebraMap (kE φ) 𝓀 t)
    (halgk : letI := kEAlgebra φ; Algebra.IsAlgebraic (kE φ) 𝓀) :
    Nonempty (NodeData hc P' b₁) := by
  classical
  subst hcc
  have hc₀0 : c₀ ≠ 0 := by rintro rfl; exact hc0 (map_zero φ)
  have hc₀1 : ‖c₀‖ < 1 := by rw [← hφ]; exact hc
  haveI : IsNoetherianRing (BE F₀ c₀) := isNoetherianRing_BE F₀ hc₀0 hc₀1.le
  haveI : IsIntegrallyClosed (BE F₀ c₀) := isIntegrallyClosed_BE F₀ c₀
  letI := algO (F₀ := F₀) c₀
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (HenselComplete.integers E)
  have hϖ0 : (ϖ : E) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hϖ1 : ‖(ϖ : E)‖ ≤ 1 := HenselComplete.norm_le_one ϖ
  letI := isLocalRing_placeSub (Q := b₁.2.1) (M := resE χ b₁.1) fun _ ha ↦ resE_inv_mem ha
  letI := isLocalRing_placeSub (Q := b₂.2.1) (M := resE (χInv hc0 χ) b₂.1)
    fun _ ha ↦ resE_inv_mem ha
  have hP₁ := placeIdeal_eq₁ hc hb₁
  obtain ⟨c₀', d, -, H⟩ := branchData hp hp1 hφ hχ hdeg hθ hc hc0 hODP hb₁ hb₂ hι heo hei hLD₁
    hLD₂ t₀ ht₀ ht₀o ht₀i yu hyu₁ hyu₂ yv hyv₂ hyv₁ hspan hres halgk hϖ
  haveI : (P'.comap ι).IsPrime := Ideal.comap_isPrime ι P'
  obtain ⟨xB, hxBdef⟩ : ∃ z : BE F₀ c₀,
      algebraMap (nodeRing c₀) (BE F₀ c₀) ⟨RatFunc.X, X_mem_nodeRing c₀⟩ = z := ⟨_, rfl⟩
  have hιx : ι xB = xR (φ c₀) := by
    subst hxBdef
    exact Subtype.ext <|
      (ι_algebraMap hχ hι ⟨RatFunc.X, X_mem_nodeRing c₀⟩).trans (by rw [ratFuncMap_X]; rfl)
  have hd := H.hd
  obtain ⟨n, u, v, hn, huv, -, hua, ε, hε⟩ := H.exists_node
  have hϖB : algebraMap (HenselComplete.integers E) (BE F₀ c₀) ϖ = cstB (ϖ : E) hϖ1 :=
    algO_apply c₀ ϖ
  -- the map `B_(P'.comap ι) → F'`
  have hunit : ∀ s : (P'.comap ι).primeCompl, IsUnit ((χ.comp (BE F₀ c₀).val.toRingHom) s) := by
    intro s
    refine isUnit_iff_ne_zero.mpr fun h ↦ s.2 ?_
    have h' : ((s : BE F₀ c₀) : F₀) = 0 := χ.injective (by rw [map_zero]; exact h)
    rw [show (s : BE F₀ c₀) = 0 from Subtype.ext h']
    exact zero_mem _
  obtain ⟨liftD, hliftD⟩ : ∃ f : Localization.AtPrime (P'.comap ι) →+* F',
      IsLocalization.lift hunit = f :=
    ⟨_, rfl⟩
  have hlift : ∀ b : BE F₀ c₀, liftD (algebraMap _ _ b) = χ b := fun b ↦ by
    subst hliftD; exact IsLocalization.lift_eq hunit b
  have hliftmk : ∀ (b : BE F₀ c₀) (s : (P'.comap ι).primeCompl),
      liftD (IsLocalization.mk' _ b s) * χ (s : BE F₀ c₀) = χ b := fun b s ↦ by
    subst hliftD
    rw [mul_comm]
    exact ((IsLocalization.lift_mk'_spec (hg := hunit) b _ s).mp rfl).symm
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (P'.comap ι).primeCompl u
  obtain ⟨⟨a', s'⟩, rfl⟩ := IsLocalization.mk'_surjective (P'.comap ι).primeCompl v
  obtain ⟨⟨e₁, σ₁⟩, hεe⟩ :=
    IsLocalization.mk'_surjective (P'.comap ι).primeCompl (ε : Localization.AtPrime (P'.comap ι))
  have he₁ : e₁ ∉ (P'.comap ι) := by
    have := ε.isUnit
    rw [← hεe, IsLocalization.AtPrime.isUnit_mk'_iff] at this
    exact this
  have hns : ∀ t : (P'.comap ι).primeCompl, ι t ∉ P' := fun t ↦ t.2
  have hliftϖ :
      liftD (algebraMap (HenselComplete.integers E) (Localization.AtPrime (P'.comap ι)) ϖ) =
      algebraMap C F' (φ ϖ) := by
    rw [IsScalarTower.algebraMap_apply (HenselComplete.integers E) (BE F₀ c₀), hlift, hϖB]
    exact χ_cst hχ (ϖ : E)
  have hxF : χ (xB : F₀) = xF C F' := by rw [← hι, hιx]; rfl
  refine ⟨⟨d, hd, liftD (IsLocalization.mk' _ a s), liftD (IsLocalization.mk' _ a' s'), φ ϖ ^ n,
    pow_ne_zero _ (by rw [ne_eq, map_eq_zero_iff _ φ.injective]; exact hϖ0), ?_, ι σ₁, ι e₁,
    hns σ₁, he₁, ?_, ι a, ι s, hns s, ?_, ι a', ι s', hns s', ?_, ?_⟩⟩
  · rw [← map_mul, huv, map_pow, hliftϖ, map_pow]
  · have h1 := congrArg liftD hε
    rw [hlift, map_mul, map_pow, ← hεe, hxBdef] at h1
    rw [hι, hι, ← hxF, h1, ← hliftmk e₁ σ₁]
    ring
  · rw [hι, hι, ← hliftmk a s, mul_comm]
  · rw [hι, hι, ← hliftmk a' s', mul_comm]
  · have h := congrArg Subtype.val (hua a s rfl)
    change redHom hc b₁.1 (ι a) = redHom hc b₁.1 (ι s) * redHom hc b₁.1 (ι yu) at h
    rw [h, map_mul, Qval_one_of_notMem hc hP₁ (hns s), one_mul, hyu₁]

end DVRDescent

end SemistableReduction
