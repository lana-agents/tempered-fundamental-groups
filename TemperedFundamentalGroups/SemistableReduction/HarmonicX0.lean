/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.UnfoldedNodeMain

/-!
# (X0): x-lengths of nodes of unfolded W-models exist and are positive (Blueprint §9.7)

* `toL_mul_ne_one`: a section whose germ at `y` is not a unit is not invertible among the germs;
* `exists_ramification`: `ϖ = η ϖ₁ ^ e₀` with `e₀ > 0` for a base uniformizer `ϖ` and a uniformizer
  `ϖ₁` of a discrete valuation ring over the base;
* `x0`: at every node of an unfolded split W-model without loops, the x-length (for any node
  coordinates from sections near the node, `isXLength_of_coord`) is `e n / e₀ > 0`
  (`UnfoldedNodeGerm.isXLength`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction

/-- **The ramification of a base uniformizer.** -/
lemma exists_ramification {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]
    {O : ValuationSubring K} {O₁ : ValuationSubring K₁} [IsDiscreteValuationRing O₁]
    (h₁ : O₁.comap (algebraMap K K₁) = O) {ϖ : O} (hϖ : Irreducible ϖ) {ϖ₁ : O₁}
    (hϖ₁ : Irreducible ϖ₁) :
    ∃ (η : O₁ˣ) (e₀ : ℕ), 0 < e₀ ∧ algebraMap K K₁ ϖ = (η : K₁) * (ϖ₁ : K₁) ^ e₀ := by
  have hmem : algebraMap K K₁ ϖ ∈ O₁ := by
    have : (ϖ : K) ∈ O₁.comap (algebraMap K K₁) := h₁ ▸ ϖ.2
    exact this
  have hϖ0 : (ϖ : K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hne : (⟨_, hmem⟩ : O₁) ≠ 0 := fun h ↦ hϖ0 (by
    have := congrArg Subtype.val h
    simpa using this)
  obtain ⟨e₀, η, hη⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ₁
  have hval : algebraMap K K₁ ϖ = (η : K₁) * (ϖ₁ : K₁) ^ e₀ := by
    have := congrArg Subtype.val hη
    simpa using this
  refine ⟨η, e₀, Nat.pos_of_ne_zero fun he ↦ hϖ.not_isUnit ?_, hval⟩
  rw [he, pow_zero, mul_one] at hval
  have h1 : ((η : O₁) : K₁) * ((η⁻¹ : O₁ˣ) : O₁) = 1 := congrArg Subtype.val η.mul_inv
  have hinv' : (algebraMap K K₁ (ϖ : K))⁻¹ ∈ O₁ := by
    rw [hval, inv_eq_of_mul_eq_one_right h1]; exact (η⁻¹ : O₁ˣ).val.2
  have hinv : (ϖ : K)⁻¹ ∈ O := by
    have : (ϖ : K)⁻¹ ∈ O₁.comap (algebraMap K K₁) := by
      rw [ValuationSubring.mem_comap, map_inv₀]; exact hinv'
    rw [h₁] at this
    exact this
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hϖ0)⟩

namespace CrossingSource

open CentreGerms ValuativeCentre ModelCode _root_.SemistableReduction

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [Algebra O L] [IsScalarTower O K L] {x : L}
  {c : TemperedFundamentalGroups.ModelCode O} {j : Spec (CommRingCat.of L) ⟶ c.scheme}

/-- **A section with a non-unit germ is not invertible among the germs.** -/
lemma toL_mul_ne_one (hW : IsWModel O L x c j) {U : c.scheme.Opens} {y : c.scheme} (hy : y ∈ U)
    (h : ⊤ ≤ j ⁻¹ᵁ U) (s : Γ(c.scheme, U))
    (hs : ¬ IsUnit ((c.scheme.presheaf.germ U y hy).hom s)) :
    ∀ w ∈ germs c j y, toL j h s * w ≠ 1 := by
  have hsp := specializes_of_isWModel hW y
  intro w hw h1
  rw [germs_eq_range c j hsp] at hw
  obtain ⟨t, rfl⟩ := hw
  apply hs
  rw [isUnit_iff_exists_mul j hsp]
  refine ⟨t, ?_⟩
  rw [stalkTo_germ j hsp U hy s]
  exact h1

/-- Sections from the base. -/
lemma toL_algebraMap (hW : IsWModel O L x c j) {U : c.scheme.Opens} (h : ⊤ ≤ j ⁻¹ᵁ U) (o : O) :
    letI := sectionsAlgebra c U
    toL j h (algebraMap O Γ(c.scheme, U) o) = algebraMap O L o := by
  letI := sectionsAlgebra c U
  rw [← baseHom_eq_toL c j h o]
  exact baseHom_eq_of_isWModel hW o

variable [IsDiscreteValuationRing O]

/-- **The x-length of an unfolded node** is `e n / e₀`, for any node coordinates from sections
near the node (`isXLength_of_coord`). -/
theorem isXLength_iff_of_unfolded (hW : IsWModel O L x c j) {ϖ : O} (hϖ : Irreducible ϖ)
    {ϖ₀ : K} {η : Oˣ} {e₀ : ℕ} (he₀ : 0 < e₀) (hϖ₀ : ϖ₀ = (η : K) * (ϖ : K) ^ e₀)
    {y : c.scheme} {P : Subring L} {u v : L} {n : ℕ} {a β : K} {e α : ℕ} {ε : L}
    {W₁ W₂ : ValuationSubring L} (H : UnfoldedNodeGerm O ϖ P u v n x a β e α ε W₁ W₂)
    (HB : NodeBranches O ϖ P (algebraMap O L) u v n W₁ W₂) (hPg : (P : Set L) = germs c j y)
    (hdiv : ∀ t ∈ P, ∀ M : ℕ, (∃ r ∈ P, t * r = algebraMap O L ϖ ^ M) →
      ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ, t = ε * algebraMap O L ϖ ^ α * u ^ e ∨
        t = ε * algebraMap O L ϖ ^ α * v ^ e)
    (hsec : ∃ (V : c.scheme.Opens) (hyV : y ∈ V) (hV : ⊤ ≤ j ⁻¹ᵁ V) (su sv : Γ(c.scheme, V)),
        letI := sectionsAlgebra c V
        su * sv = algebraMap O Γ(c.scheme, V) (ϖ ^ n) ∧
        ¬ IsUnit ((c.scheme.presheaf.germ V y hyV).hom su) ∧
        ¬ IsUnit ((c.scheme.presheaf.germ V y hyV).hom sv) ∧ toL j hV su = u) (l : ℚ) :
    IsXLength (algebraMap K L ϖ₀) O ϖ c j x y l ↔ l = e * n / e₀ := by
  obtain ⟨V, hyV, hV, su, sv, hsuv, hsu, hsv, hsuL⟩ := hsec
  have hX := H.isXLength hϖ he₀ hϖ₀
  have hϖL : algebraMap K L (ϖ : K) = algebraMap O L ϖ := algebraMap_O_K ϖ
  constructor
  · rintro ⟨U', hy', h', n', su', sv', hsuv', hsu', hsv', hl⟩
    letI := sectionsAlgebra c U'
    have hv'P : toL j h' sv' ∈ P := by
      rw [← SetLike.mem_coe, hPg]; exact toL_mem_germs j h' hy' sv'
    have hu'P : toL j h' su' ∈ P := by
      rw [← SetLike.mem_coe, hPg]; exact toL_mem_germs j h' hy' su'
    have huv' : toL j h' su' * toL j h' sv' = algebraMap K L (ϖ : K) ^ n' := by
      rw [← toLHom_apply, ← toLHom_apply, ← map_mul, hsuv', toLHom_apply, toL_algebraMap hW,
        map_pow, hϖL]
    have hu'nu : ∀ w ∈ P, toL j h' su' * w ≠ 1 := fun w hw ↦
      toL_mul_ne_one hW hy' h' su' hsu' w (by rw [← hPg]; exact hw)
    have hdiv' : ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ,
        toL j h' su' = ε * algebraMap K L (ϖ : K) ^ α * u ^ e ∨
          toL j h' su' = ε * algebraMap K L (ϖ : K) ^ α * v ^ e := by
      rw [hϖL]
      exact hdiv _ hu'P n' ⟨_, hv'P, by rw [huv', hϖL]⟩
    rw [← hPg, ← hϖL] at hl
    exact (HB.isXLength_of_coord hv'P huv' hu'nu hdiv' hl).unique hX
  · rintro rfl
    refine ⟨V, hyV, hV, n, su, sv, hsuv, hsu, hsv, ?_⟩
    rw [hsuL, ← hPg, ← hϖL]
    exact hX

/-- **(X0) for unfolded W-models**: x-lengths of nodes exist and are positive. -/
theorem x0 (hU : IsUnfolded O x c j) {ϖ : O} (hϖ : Irreducible ϖ) (hsplit : HasSplitNodes ϖ c)
    (hloops : NoLoops c) {ϖ₀ : K} {η : Oˣ} {e₀ : ℕ} (he₀ : 0 < e₀)
    (hϖ₀ : ϖ₀ = (η : K) * (ϖ : K) ^ e₀) (y : c.scheme) (hy : IsNodePt c y) :
    (∃ l, IsXLength (algebraMap K L ϖ₀) O ϖ c j x y l) ∧
      ∀ l, IsXLength (algebraMap K L ϖ₀) O ϖ c j x y l → 0 < l := by
  obtain ⟨P, u, v, n, a, β, e, α, ε, v₁, v₂, hv₁, hv₂, H, HB, hPg, -, -, -, -, hdiv, hsec⟩ :=
    exists_unfoldedNodeGerm hU hϖ hsplit hloops hy
  have key := isXLength_iff_of_unfolded hU.isWModel hϖ he₀ hϖ₀ H HB hPg hdiv hsec
  refine ⟨⟨_, (key _).2 rfl⟩, fun l hl ↦ ?_⟩
  rw [(key l).1 hl]
  have : (1 : ℚ) ≤ e := by exact_mod_cast H.one_le_e
  have : (1 : ℚ) ≤ n := by exact_mod_cast H.one_le_n
  positivity

end CrossingSource

end TemperedFundamentalGroups.SemistableReduction
