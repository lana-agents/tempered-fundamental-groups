/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourUnif
import TemperedFundamentalGroups.SemistableReduction.GaloisReduction
import TemperedFundamentalGroups.SemistableReduction.PGroupChain
import TemperedFundamentalGroups.SemistableReduction.KummerNormalForm

/-!
# Local uniformization at type-4 points: the Kummer tower

Blueprint §9.12, leaf T4, interface `TypeFour.UnifFor`. Let `F / C(x)` be Galois and `ξ'` an
extension of a type-4 point `ξ`. The automorphisms preserving `ξ'` form the decomposition group
`D = stab ξ'` (`mem_decompositionGroup_iff`), a `p`-group (A4: the residue field of the
decomposition field is the residue field of `C`, its values are those of `C`). Along a chain
`1 = H₀ ◁ ⋯ ◁ H_m = D` of index-`p` steps the fixed fields grow by Kummer steps
`K ⊆ K(θ)`, `σ θ = ζ θ` for some `σ ∈ D`; the density of `C(s)` is carried up the tower by the
**Kummer step** `TypeFour.KummerStepFor` (stated here, proved separately).
-/

open Polynomial
open scoped NNReal Pointwise

namespace SemistableReduction

namespace TypeFour

open DiscCount LocalGlobal DenseCompletion GaloisReduction

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

section Defs

variable (C) {F : Type*} [Field F] [Algebra C F]

/-- `C(s)` is dense in the subset `S` of `(F, ξ')`. -/
def DenseOn (ξ' : Valuation F ℝ≥0) (S : Set F) (s : F) : Prop :=
  ∀ y ∈ S, ∀ ε : ℝ≥0, 0 < ε → ∃ P Q : C[X], aeval s Q ≠ 0 ∧ ξ' (y - aeval s P / aeval s Q) < ε

variable {C} [Algebra (RatFunc C) F]

/-- `y ∈ K[θ]`: `y = Σ_{j < p} c_j θ^j` with `c_j ∈ K`. -/
def InAdj (p : ℕ) (K : IntermediateField (RatFunc C) F) (θ y : F) : Prop :=
  ∃ c : ℕ → F, (∀ j, c j ∈ K) ∧ y = ∑ j ∈ Finset.range p, c j * θ ^ j

variable (C F) [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

/-- **The Kummer step** at a type-4 point (Blueprint §9.10 fallback (1), Temkin §6.3 case
`a = 0`, Arzdorf's critical radius descent): let `ξ'` be a valuation of `F` over a type-4 point
of `C(x)` (radius bounded below, i.e. not a point of `Ĉ ∖ C`), `K` an intermediate field in
which `C(s)` is dense, and `θ ≠ 0` with `θ ^ p ∈ K`, moved by an automorphism `σ` fixing `K` and
preserving `ξ'` as `σ θ = ζ θ`. Then some `w ∈ K[θ]` has `C(w)` dense in `K[θ]`. -/
def KummerStepFor (p : ℕ) : Prop :=
  ∀ ξ' : Valuation F ℝ≥0, (∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊) →
    Splitting.IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F)) →
    (∃ r : ℝ≥0, 0 < r ∧ ∀ b : C,
      r ≤ ξ' (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) b))) →
    ∀ (K : IntermediateField (RatFunc C) F) (θ : F) (σ : F ≃ₐ[RatFunc C] F) (ζ : C),
      IsPrimitiveRoot ζ p → θ ≠ 0 → θ ^ p ∈ K → σ θ = algebraMap C F ζ * θ →
      (∀ y ∈ K, σ y = y) → (∀ y, ξ' (σ y) = ξ' y) →
      ∀ s ∈ K, DenseOn C ξ' K s →
      ∃ w : F, InAdj p K θ w ∧ DenseOn C ξ' {y | InAdj p K θ y} w

end Defs

/-! ### The decomposition group -/

section Stab

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

variable (C) in
/-- The automorphisms preserving `ξ'`. -/
def stab (ξ' : Valuation F ℝ≥0) : Subgroup (F ≃ₐ[RatFunc C] F) where
  carrier := {σ | ∀ y, ξ' (σ y) = ξ' y}
  one_mem' y := rfl
  mul_mem' {σ τ} hσ hτ y := by
    change ξ' (σ (τ y)) = ξ' y
    rw [hσ, hτ]
  inv_mem' {σ} hσ y := by
    have := hσ (σ.symm y)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma mem_stab {ξ' : Valuation F ℝ≥0} {σ : F ≃ₐ[RatFunc C] F} :
    σ ∈ stab C ξ' ↔ ∀ y, ξ' (σ y) = ξ' y := Iff.rfl

omit [IsUltrametricDist C] [FiniteDimensional (RatFunc C) F] in
/-- The decomposition group of the valuation ring of `ξ'` is the stabilizer of `ξ'`. -/
theorem mem_decompositionGroup_iff {ξ' : Valuation F ℝ≥0}
    (hconst : ∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊) (σ : F ≃ₐ[RatFunc C] F) :
    σ ∈ decompositionGroup (RatFunc C) ξ'.valuationSubring ↔ σ ∈ stab C ξ' := by
  have hσC : ∀ (τ : F ≃ₐ[RatFunc C] F) (b : C), τ (algebraMap C F b) = algebraMap C F b :=
    fun τ b ↦ by rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, AlgEquiv.commutes]
  rw [decompositionGroup, MulAction.mem_stabilizer_iff, mem_stab]
  constructor
  · intro h
    have hmem : ∀ y, ξ' (σ⁻¹ y) ≤ 1 ↔ ξ' y ≤ 1 := fun y ↦ by
      have := congrArg (fun W : ValuationSubring F ↦ y ∈ W) h
      simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        Valuation.mem_valuationSubring_iff, AlgEquiv.smul_def, eq_iff_iff] at this
      exact this
    have heq := valuation_eq_of_le_one_iff (v₁ := ξ'.comap (σ⁻¹ : F ≃ₐ[RatFunc C] F).toRingHom)
      (v₂ := ξ') (fun b ↦ by
        change ξ' ((σ⁻¹ : F ≃ₐ[RatFunc C] F) (algebraMap C F b)) = _
        rw [hσC, hconst]) hconst hmem
    intro y
    have := congrArg (fun v : Valuation F ℝ≥0 ↦ v (σ y)) heq
    simp only [Valuation.comap_apply] at this
    change ξ' ((σ⁻¹ : F ≃ₐ[RatFunc C] F) (σ y)) = ξ' (σ y) at this
    rw [← this]
    congr 1
    exact σ.symm_apply_apply y
  · intro h
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Valuation.mem_valuationSubring_iff,
      Valuation.mem_valuationSubring_iff, AlgEquiv.smul_def]
    have := h ((σ⁻¹ : F ≃ₐ[RatFunc C] F) y)
    change ξ' (σ (σ.symm y)) = ξ' (σ.symm y) at this
    change ξ' (σ.symm y) ≤ 1 ↔ _
    rw [← this, AlgEquiv.apply_symm_apply]

end Stab

/-! ### The decomposition group is a `p`-group -/

/-- Algebraic closedness is transported along ring isomorphisms (across universes). -/
lemma isAlgClosed_of_ringEquiv' {K L : Type*} [Field K] [Field L] [IsAlgClosed K] (e : K ≃+* L) :
    IsAlgClosed L := by
  refine IsAlgClosed.of_exists_root L fun q hq hirr ↦ ?_
  have hdeg : (q.map e.symm.toRingHom).degree ≠ 0 := by
    rw [degree_map]; exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (q.map e.symm.toRingHom) hdeg
  refine ⟨e x, ?_⟩
  rw [IsRoot, eval_map] at hx
  have h := Polynomial.hom_eval₂ q e.symm.toRingHom e.toRingHom x
  rw [hx, map_zero] at h
  have hc : e.toRingHom.comp e.symm.toRingHom = RingHom.id L := by
    ext a; simp
  rw [hc] at h
  exact h.symm

section PGroup

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] [IsGalois (RatFunc C) F]
  [CharZero C]

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- Elements fixed by the decomposition group are close to constants (residue field `k`, values
`|C^×|`). -/
theorem exists_const_of_fixed {ξ' : Valuation F ℝ≥0}
    (hξ : Splitting.IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F))) {y : F}
    (hy : ∀ σ ∈ stab C ξ', σ y = y) (hy0 : y ≠ 0) :
    ∃ b : C, ξ' (y - algebraMap C F b) < ξ' y := by
  obtain ⟨a, c, ν, hν⟩ := exists_discVal hξ
  have hξ0 : 0 < ξ' y := (zero_le).lt_of_ne (Ne.symm ((map_ne_zero ξ').2 hy0))
  obtain ⟨φ, hφ⟩ := exists_ratFunc_approx_of_fixed ν (ξ' := ξ') hν.symm (y := y)
    (fun σ hσ ↦ hy σ hσ) hξ0
  have hφy : ξ' (algebraMap (RatFunc C) F φ) = ξ' y :=
    Valuation.map_eq_of_sub_lt ξ' (by rwa [← Valuation.map_neg, neg_sub])
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hφy
    exact hξ0.ne hφy
  obtain ⟨b, hb⟩ := exists_const_sub_lt hξ hφ0
  refine ⟨b, ?_⟩
  rw [show y - algebraMap C F b = (y - algebraMap (RatFunc C) F φ) +
    algebraMap (RatFunc C) F (φ - algebraMap C (RatFunc C) b) by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]; ring]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt hφ ?_)
  rw [← Valuation.comap_apply (algebraMap (RatFunc C) F) ξ', ← hφy,
    ← Valuation.comap_apply (algebraMap (RatFunc C) F) ξ']
  exact hb

variable {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

attribute [local instance] DiscreteCoefficients.isAlgClosed_residueField

include hp hp1 in
/-- **A4 at a type-4 point**: the decomposition group is a `p`-group. -/
theorem isPGroup_stab {ξ' : Valuation F ℝ≥0}
    (hconst : ∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊)
    (hξ : Splitting.IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F))) :
    IsPGroup p (stab C ξ') := by
  classical
  set W := ξ'.valuationSubring
  have hD : decompositionGroup (RatFunc C) W = stab C ξ' := by
    ext σ; exact mem_decompositionGroup_iff hconst σ
  set E := decompositionField (RatFunc C) W
  set u := W.valuation.comap (algebraMap E F)
  set V := u.valuationSubring
  set vE : Valuation E ℝ≥0 := ξ'.comap (algebraMap E F)
  have hequiv : vE.IsEquiv V.valuation :=
    ((Valuation.isEquiv_valuation_valuationSubring ξ').comap (algebraMap E F)).trans
      (Valuation.isEquiv_valuation_valuationSubring u)
  have hfix : ∀ y : E, ∀ σ ∈ stab C ξ', σ (y : F) = y := fun y σ hσ ↦ by
    have := (IntermediateField.mem_fixedField_iff _ _).1 y.2 σ (hD ▸ hσ)
    exact this
  have hvE : ∀ y : E, vE y = ξ' (y : F) := fun y ↦ rfl
  -- elements of `E` are close to constants
  have hres : ∀ y : E, ξ' (y : F) ≤ 1 → ∃ b : C, ‖b‖ ≤ 1 ∧ ξ' ((y : F) - algebraMap C F b) < 1 := by
    intro y hy
    by_cases hy0 : (y : F) = 0
    · exact ⟨0, by simp, by rw [hy0, map_zero, sub_zero, map_zero]; exact zero_lt_one⟩
    by_cases hlt : ξ' (y : F) < 1
    · exact ⟨0, by simp, by rwa [map_zero, sub_zero]⟩
    have h1 : ξ' (y : F) = 1 := le_antisymm hy (not_lt.1 hlt)
    obtain ⟨b, hb⟩ := exists_const_of_fixed hξ (fun σ hσ ↦ hfix y σ hσ) hy0
    refine ⟨b, ?_, by rwa [h1] at hb⟩
    have hbe : ξ' (algebraMap C F b) = ξ' (y : F) :=
      Valuation.map_eq_of_sub_lt ξ' (by rwa [← Valuation.map_neg, neg_sub])
    rw [hconst, h1] at hbe
    have : ‖b‖₊ = 1 := hbe
    exact (congrArg NNReal.toReal this).le.trans (by simp)
  -- constants
  let ι : C →+* E := (algebraMap (RatFunc C) E).comp (algebraMap C (RatFunc C))
  have hι : ∀ b, ((ι b : E) : F) = algebraMap C F b := fun b ↦
    (IsScalarTower.algebraMap_apply C (RatFunc C) F b).symm
  have hιinj : Function.Injective ι := ι.injective
  -- membership, maximal ideal, units of `V`
  have hV : ∀ y : E, y ∈ V ↔ ξ' (y : F) ≤ 1 := fun y ↦ by
    rw [Valuation.mem_valuationSubring_iff]
    change W.valuation (y : F) ≤ 1 ↔ _
    rw [ValuationSubring.valuation_le_one_iff, Valuation.mem_valuationSubring_iff]
  have hmax : ∀ a : V, a ∈ IsLocalRing.maximalIdeal V ↔ ξ' ((a : E) : F) < 1 := fun a ↦ by
    rw [ValuationSubring.valuation_lt_one_iff, ← hequiv.lt_one_iff_lt_one]
    rfl
  have hunit : ∀ a : V, IsUnit a ↔ ξ' ((a : E) : F) = 1 := fun a ↦ by
    rw [ValuationSubring.valuation_eq_one_iff, ← map_one V.valuation,
      ← hequiv.eq_iff, map_one]
    rfl
  -- the residue map `k → κ(V)`
  let φ₀ : HenselComplete.integers C →+* V :=
    { toFun := fun b ↦ ⟨ι b, (hV _).2 (by
        rw [hι, hconst]; exact_mod_cast (HenselComplete.norm_le_one b))⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  have hφ₀ : ∀ b, (((φ₀ b : V) : E) : F) = algebraMap C F b := fun b ↦ hι b
  haveI : IsLocalHom φ₀ := ⟨fun b hb ↦ by
    rw [hunit, hφ₀, hconst] at hb
    rw [HenselComplete.isUnit_iff_norm_eq_one, ← coe_nnnorm, hb, NNReal.coe_one]⟩
  set R := IsLocalRing.ResidueField V
  let φ : 𝓀 →+* R := IsLocalRing.ResidueField.map φ₀
  have hsurj : Function.Surjective φ := by
    intro r
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨b, hb1, hb⟩ := hres y ((hV y).1 y.2)
    refine ⟨IsLocalRing.residue _ ⟨b, (HenselComplete.mem_integers_iff b).2 hb1⟩, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    refine (Ideal.Quotient.eq).2 ((hmax _).2 ?_)
    change ξ' ((((φ₀ _ : V) : E) : F) - ((y : E) : F)) < 1
    rw [hφ₀, ← Valuation.map_neg, neg_sub]
    exact hb
  have hbij : Function.Bijective φ := ⟨φ.injective, hsurj⟩
  let e : 𝓀 ≃+* R := RingEquiv.ofBijective φ hbij
  haveI : IsAlgClosed R := isAlgClosed_of_ringEquiv' e
  haveI : CharP 𝓀 p := KummerNormalForm.charP_residueField hp hp1
  haveI : CharP R p := charP_of_injective_ringHom e.injective p
  have hchar : ringChar R = p := ringChar.eq R p
  have hdiv : ∀ (c : E) (n : ℕ), 0 < n → ∃ d : E,
      W.valuation (algebraMap E F d) ^ n = W.valuation (algebraMap E F c) := by
    intro c n hn
    by_cases hc0 : (c : F) = 0
    · refine ⟨0, ?_⟩
      rw [map_zero, map_zero, zero_pow hn.ne']
      change 0 = W.valuation (c : F)
      rw [hc0, map_zero]
    obtain ⟨b, hb⟩ := exists_const_of_fixed hξ (fun σ hσ ↦ hfix c σ hσ) hc0
    have hbe : ξ' (algebraMap C F b) = ξ' (c : F) :=
      Valuation.map_eq_of_sub_lt ξ' (by rwa [← Valuation.map_neg, neg_sub])
    obtain ⟨d₀, hd₀⟩ := IsAlgClosed.exists_pow_nat_eq b hn
    refine ⟨ι d₀, ?_⟩
    rw [← map_pow]
    have : ξ' (algebraMap E F (ι d₀) ^ n) = ξ' (algebraMap E F c) := by
      change ξ' ((ι d₀ : F) ^ n) = ξ' (c : F)
      rw [hι, ← map_pow, hd₀, hbe]
    exact ((Valuation.isEquiv_valuation_valuationSubring ξ').eq_iff).1 this
  have hμ : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : R) ≠ 0 → ∃ ζ : E, IsPrimitiveRoot ζ ℓ := by
    intro ℓ hℓ _
    haveI : NeZero (ℓ : C) := ⟨by exact_mod_cast hℓ.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C ℓ
    exact ⟨ι ζ, hζ.map_of_injective hιinj⟩
  have h := isPGroup_decompositionGroup W hdiv hμ
  rw [hchar, hD] at h
  exact h

end PGroup

/-! ### Index-`p` steps and resolvents -/

section Steps

/-- An index-`p` normal step `B ◁ A`: a generator `σ` of `A / B` with `σ ^ p ∈ B`, and every
element of `A` is `σ ^ k b`, `b ∈ B`. -/
lemma exists_step_gen {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {A B : Subgroup G}
    (hN : (B.subgroupOf A).Normal) (hidx : B.relIndex A = p) :
    ∃ σ ∈ A, σ ∉ B ∧ σ ^ p ∈ B ∧ ∀ a ∈ A, ∃ k : ℕ, ∃ b ∈ B, a = σ ^ k * b := by
  set N := B.subgroupOf A
  have hcard : Nat.card (A ⧸ N) = p := by
    rw [← Subgroup.index_eq_card]; exact hidx
  obtain ⟨a, ha⟩ : ∃ a : A, a ∉ N := by
    by_contra! h
    have htop : B.subgroupOf A = ⊤ := eq_top_iff.2 fun x _ ↦ h x
    have : B.relIndex A = 1 := by rw [Subgroup.relIndex, htop, Subgroup.index_top]
    rw [this] at hidx
    exact hp.out.one_lt.ne hidx
  have hq : (a : A ⧸ N) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  refine ⟨a, a.2, fun h ↦ ha (Subgroup.mem_subgroupOf.2 h), ?_, fun a' ha' ↦ ?_⟩
  · have h1 : ((a ^ p : A) : A ⧸ N) = 1 := by
      rw [QuotientGroup.mk_pow, ← hcard, pow_card_eq_one']
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · obtain ⟨k, hk⟩ := mem_powers_of_prime_card hcard hq (g' := ((⟨a', ha'⟩ : A) : A ⧸ N))
    refine ⟨k, (a : G)⁻¹ ^ k * a', ?_, by group⟩
    have h2 : ((a ^ k : A) : A ⧸ N) = ((⟨a', ha'⟩ : A) : A ⧸ N) := by
      rw [QuotientGroup.mk_pow]; exact hk
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    simpa [inv_pow] using h2

variable {F : Type*} [Field F] [Algebra (RatFunc C) F]

/-- The resolvent `Σ_{k < p} ζ^{-jk} σ^k y`. -/
noncomputable def res (p : ℕ) (σ : F ≃ₐ[RatFunc C] F) (ζ : F) (j : ℕ) (y : F) : F :=
  ∑ k ∈ Finset.range p, ((ζ ^ j)⁻¹) ^ k * (σ ^ k) y

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- The resolvent is an eigenvector of `σ`. -/
lemma res_eigen {p : ℕ} (σ : F ≃ₐ[RatFunc C] F) {ζ : F} (hζ0 : ζ ≠ 0) (hζp : ζ ^ p = 1)
    (hσζ : σ ζ = ζ) (j : ℕ) {y : F} (hy : (σ ^ p) y = y) :
    σ (res p σ ζ j y) = ζ ^ j * res p σ ζ j y := by
  set u := (ζ ^ j)⁻¹
  have hu : u ^ p = 1 := by rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hζp, one_pow, inv_one]
  have hu0 : u ≠ 0 := inv_ne_zero (pow_ne_zero _ hζ0)
  have hσu : σ u = u := by simp only [u, map_inv₀, map_pow, hσζ]
  have hσu' : σ ((ζ ^ j)⁻¹) = (ζ ^ j)⁻¹ := hσu
  set f : ℕ → F := fun k ↦ u ^ k * (σ ^ k) y
  have h1 : σ (res p σ ζ j y) = ∑ k ∈ Finset.range p, u ^ k * (σ ^ (k + 1)) y := by
    simp only [res, map_sum, map_mul, map_pow, hσu', pow_succ', AlgEquiv.mul_apply]
    rfl
  have h2 : u * ∑ k ∈ Finset.range p, u ^ k * (σ ^ (k + 1)) y = res p σ ζ j y := by
    rw [Finset.mul_sum]
    have e1 := Finset.sum_range_succ' f p
    have e2 := Finset.sum_range_succ f p
    have hfp : f p = f 0 := by simp only [f, hu, hy, pow_zero, one_mul, AlgEquiv.one_apply]
    rw [e2, hfp] at e1
    have e3 : ∑ k ∈ Finset.range p, f (k + 1) = ∑ k ∈ Finset.range p, f k :=
      add_right_cancel e1.symm
    simp only [f] at e3
    rw [res, ← e3]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [h1, ← h2, ← mul_assoc, show ζ ^ j * u = 1 from mul_inv_cancel₀ (pow_ne_zero _ hζ0), one_mul]

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- The resolvents add up to `p y`. -/
lemma sum_res {p : ℕ} (hp0 : p ≠ 0) (σ : F ≃ₐ[RatFunc C] F) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (y : F) : ∑ j ∈ Finset.range p, res p σ ζ j y = p * y := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp0
  have hswap : ∀ j k : ℕ, ((ζ ^ j)⁻¹) ^ k = ((ζ ^ k)⁻¹) ^ j := fun j k ↦ by
    rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  simp only [res]
  rw [Finset.sum_comm]
  simp_rw [hswap _ _, ← Finset.sum_mul]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.pos_of_ne_zero hp0))]
  · simp
  · intro k hk hk0
    have hz : (ζ ^ k)⁻¹ ≠ 1 := by
      rw [Ne, inv_eq_one]
      exact hζ.pow_ne_one_of_pos_of_lt hk0 (Finset.mem_range.1 hk)
    have hzp : ((ζ ^ k)⁻¹) ^ p = 1 := by
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, inv_one]
    rw [geom_sum_eq hz, hzp, sub_self, zero_div, zero_mul]

end Steps

/-! ### The tower -/

section Tower

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] [IsGalois (RatFunc C) F]
  [CharZero C] {p : ℕ}

omit [IsUltrametricDist C] [IsAlgClosed C] [IsGalois (RatFunc C) F] [CharZero C]
  [FiniteDimensional (RatFunc C) F] in
lemma algEquiv_algebraMap_C (τ : F ≃ₐ[RatFunc C] F) (b : C) :
    τ (algebraMap C F b) = algebraMap C F b := by
  rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, AlgEquiv.commutes]

omit [IsUltrametricDist C] [IsAlgClosed C] [IsGalois (RatFunc C) F] [CharZero C] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] in
lemma conj_pow_mem {H' : Subgroup (F ≃ₐ[RatFunc C] F)} {σ : F ≃ₐ[RatFunc C] F}
    (hnorm : ∀ b ∈ H', σ⁻¹ * b * σ ∈ H') (k : ℕ) {b : F ≃ₐ[RatFunc C] F} (hb : b ∈ H') :
    (σ ^ k)⁻¹ * b * σ ^ k ∈ H' := by
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    rw [pow_succ, mul_inv_rev, show σ⁻¹ * (σ ^ k)⁻¹ * b * (σ ^ k * σ) =
      σ⁻¹ * ((σ ^ k)⁻¹ * b * σ ^ k) * σ by group]
    exact hnorm _ ih

omit [IsUltrametricDist C] [IsAlgClosed C] [IsGalois (RatFunc C) F] [CharZero C] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] in
/-- Powers of `σ` preserve the fixed elements of `H'` if `σ` normalizes `H'`. -/
lemma pow_apply_mem_fixedField {H' : Subgroup (F ≃ₐ[RatFunc C] F)} {σ : F ≃ₐ[RatFunc C] F}
    (hnorm : ∀ b ∈ H', σ⁻¹ * b * σ ∈ H') (k : ℕ) {y : F}
    (hy : y ∈ IntermediateField.fixedField H') :
    (σ ^ k) y ∈ IntermediateField.fixedField H' := by
  rw [IntermediateField.mem_fixedField_iff] at hy ⊢
  intro τ hτ
  have h := hy _ (conj_pow_mem hnorm k hτ)
  have : τ ((σ ^ k) y) = (σ ^ k) (((σ ^ k)⁻¹ * τ * σ ^ k) y) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    change τ ((σ ^ k) y) = (σ ^ k) ((σ ^ k).symm (τ ((σ ^ k) y)))
    rw [AlgEquiv.apply_symm_apply]
  rw [this, h]

omit [IsGalois (RatFunc C) F] in
/-- **One step of the tower**: from density on the fixed field of `H` to density on the fixed
field of an index-`p` normal subgroup `H' ◁ H` (Kummer generator by a resolvent, decomposition
of the `H'`-fixed elements into `σ`-eigenvectors, and the Kummer step). -/
theorem tower_step (hp : p.Prime) (hKS : KummerStepFor C F p) {ξ' : Valuation F ℝ≥0}
    (hconst : ∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊)
    (hT : Splitting.IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F)))
    (hr : ∃ r : ℝ≥0, 0 < r ∧ ∀ b : C,
      r ≤ ξ' (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) b)))
    {H H' : Subgroup (F ≃ₐ[RatFunc C] F)} (hH'H : H' ≤ H) (hHD : H ≤ stab C ξ')
    {σ : F ≃ₐ[RatFunc C] F} (hσH : σ ∈ H) (hσH' : σ ∉ H') (hσp : σ ^ p ∈ H')
    (hgen : ∀ τ ∈ H, ∃ k : ℕ, ∃ b ∈ H', τ = σ ^ k * b)
    (hnorm : ∀ b ∈ H', σ⁻¹ * b * σ ∈ H')
    {s : F} (hs : s ∈ IntermediateField.fixedField H)
    (hdense : DenseOn C ξ' (IntermediateField.fixedField H) s) :
    ∃ s' ∈ IntermediateField.fixedField H', DenseOn C ξ' (IntermediateField.fixedField H') s' := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap C F).injective
  set K := IntermediateField.fixedField H
  set K' := IntermediateField.fixedField H'
  have hKK' : K ≤ K' := IntermediateField.fixedField_antitone hH'H
  have hσk : ∀ (k : ℕ) {y : F}, σ y = y → (σ ^ k) y = y := by
    intro k y hy
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hy, ih]
  have hfixH : ∀ {y : F}, y ∈ K' → σ y = y → y ∈ K := by
    intro y hy hσy
    rw [IntermediateField.mem_fixedField_iff] at hy ⊢
    intro τ hτ
    obtain ⟨k, b, hb, rfl⟩ := hgen τ hτ
    rw [AlgEquiv.mul_apply, hy b hb, hσk k hσy]
  -- an element of `K'` moved by `σ`
  have hσnot : σ ∉ IntermediateField.fixingSubgroup K' := by
    rwa [IntermediateField.fixingSubgroup_fixedField]
  obtain ⟨y₀, hy₀, hσy₀⟩ : ∃ y₀ ∈ K', σ y₀ ≠ y₀ := by
    by_contra! h
    exact hσnot ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy ↦ h y hy)
  -- roots of unity
  haveI : NeZero (p : C) := ⟨by exact_mod_cast hp.ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  set z₀ := algebraMap C F ζ₀
  have hz₀ : IsPrimitiveRoot z₀ p := hζ₀.map_of_injective (algebraMap C F).injective
  have hσz₀ : ∀ τ : F ≃ₐ[RatFunc C] F, τ z₀ = z₀ := fun τ ↦ algEquiv_algebraMap_C τ ζ₀
  have hz₀0 : z₀ ≠ 0 := hz₀.ne_zero hp.ne_zero
  have hσpK' : ∀ y ∈ K', (σ ^ p) y = y := fun y hy ↦
    (IntermediateField.mem_fixedField_iff _ _).1 hy _ hσp
  have hconstK' : ∀ q : F, (∀ τ : F ≃ₐ[RatFunc C] F, τ q = q) → q ∈ K' := fun q hq ↦
    (IntermediateField.mem_fixedField_iff _ _).2 fun τ _ ↦ hq τ
  have hresK' : ∀ j, ∀ y ∈ K', res p σ z₀ j y ∈ K' := by
    intro j y hy
    refine sum_mem fun k _ ↦ mul_mem (hconstK' _ fun τ ↦ ?_) (pow_apply_mem_fixedField hnorm k hy)
    rw [map_pow, map_inv₀, map_pow, hσz₀]
  -- a nonzero resolvent
  obtain ⟨j, hj0, hjp, hθ0⟩ : ∃ j, 0 < j ∧ j < p ∧ res p σ z₀ j y₀ ≠ 0 := by
    by_contra! h
    have hsum := sum_res hp.ne_zero σ hz₀ y₀
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hp.pos)
      (fun i hi hi0 ↦ h i (Nat.pos_of_ne_zero hi0) (Finset.mem_range.1 hi))] at hsum
    have he := res_eigen σ hz₀0 hz₀.pow_eq_one (hσz₀ σ) 0 (hσpK' y₀ hy₀)
    rw [pow_zero, one_mul, hsum, map_mul, map_natCast] at he
    exact hσy₀ (mul_left_cancel₀ (Nat.cast_ne_zero.2 hp.ne_zero) he)
  set θ := res p σ z₀ j y₀
  have hjcop : j.Coprime p :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hj0 hjp))
  have hζ : IsPrimitiveRoot (ζ₀ ^ j) p := hζ₀.pow_of_coprime j hjcop
  have hζF : IsPrimitiveRoot (z₀ ^ j) p := hz₀.pow_of_coprime j hjcop
  have hσθ : σ θ = algebraMap C F (ζ₀ ^ j) * θ := by
    rw [res_eigen σ hz₀0 hz₀.pow_eq_one (hσz₀ σ) j (hσpK' y₀ hy₀), map_pow]
  have hθK' : θ ∈ K' := hresK' j y₀ hy₀
  have hθp : θ ^ p ∈ K := by
    refine hfixH (pow_mem hθK' p) ?_
    rw [map_pow, hσθ, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul]
  have hσK : ∀ y ∈ K, σ y = y := fun y hy ↦ (IntermediateField.mem_fixedField_iff _ _).1 hy σ hσH
  obtain ⟨w, hw, hwd⟩ := hKS ξ' hconst hT hr K θ σ (ζ₀ ^ j) hζ hθ0 hθp hσθ hσK (hHD hσH) s hs
    hdense
  -- `K' ⊆ K[θ]`: decomposition into `σ`-eigenvectors
  have hsub : ∀ y ∈ K', InAdj p K θ y := by
    intro y hy
    have hsum := sum_res hp.ne_zero σ hz₀ y
    have hpF : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hexp : ∀ i, ∃ e < p, (z₀ ^ j) ^ e = z₀ ^ i := fun i ↦
      hζF.eq_pow_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hz₀.pow_eq_one, one_pow])
    choose e he heq using hexp
    set R : ℕ → F := fun i ↦ res p σ z₀ i y
    set c : ℕ → F := fun i ↦ (p : F)⁻¹ * (R i / θ ^ e i)
    have hpK : (p : F)⁻¹ ∈ K := by
      rw [← map_natCast (algebraMap (RatFunc C) F), ← map_inv₀]
      exact IntermediateField.algebraMap_mem _ _
    have hcK : ∀ i, c i ∈ K := by
      intro i
      refine mul_mem hpK (hfixH (div_mem (hresK' i y hy) (pow_mem hθK' _)) ?_)
      rw [map_div₀, map_pow, hσθ, res_eigen σ hz₀0 hz₀.pow_eq_one (hσz₀ σ) i (hσpK' y hy),
        mul_pow, map_pow, heq i]
      field_simp
      all_goals rfl
    have hRc : ∀ i, R i = p * (c i * θ ^ e i) := fun i ↦ by
      simp only [c]
      field_simp
    have hy' : y = ∑ i ∈ Finset.range p, c i * θ ^ e i := by
      have : (p : F) * y = (p : F) * ∑ i ∈ Finset.range p, c i * θ ^ e i := by
        rw [← hsum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ hRc i
      exact mul_left_cancel₀ hpF this
    refine ⟨fun e' ↦ ∑ i ∈ Finset.range p with e i = e', c i, fun e' ↦ sum_mem fun i _ ↦ hcK i,
      ?_⟩
    rw [hy']
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (g := e) (t := Finset.range p)
      (fun i _ ↦ Finset.mem_range.2 (he i))]
    refine Finset.sum_congr rfl fun e' _ ↦ Finset.sum_congr rfl fun i hi ↦ ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hsup : ∀ y, InAdj p K θ y → y ∈ K' := by
    rintro y ⟨c, hc, rfl⟩
    exact sum_mem fun e _ ↦ mul_mem (hKK' (hc e)) (pow_mem hθK' e)
  exact ⟨w, hsup w hw, fun y hy ε hε ↦ hwd y (hsub y hy) ε hε⟩

/-- **Local uniformization from the Kummer step**: for `F / C(x)` Galois, every extension of a
type-4 point (or a point of `Ĉ ∖ C`) admits a topological generator. -/
theorem unifFor_of_kummerStep (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    (hKS : KummerStepFor C F p) : UnifFor C F := by
  classical
  intro ξ' hconst hT
  haveI : Fact p.Prime := ⟨hp⟩
  set ξ := ξ'.comap (algebraMap (RatFunc C) F)
  by_cases hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ b : C, ξ (RatFunc.X - algebraMap C (RatFunc C) b) < ε
  · exact ⟨_, coordDense_of_small hT hsmall rfl⟩
  push Not at hsmall
  obtain ⟨r, hr0, hr⟩ := hsmall
  have hr' : ∃ r : ℝ≥0, 0 < r ∧ ∀ b : C,
      r ≤ ξ' (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) b)) :=
    ⟨r, hr0, hr⟩
  set D := stab C ξ'
  have hpD : IsPGroup p D := isPGroup_stab hp hp1 hconst hT
  haveI : Finite D := inferInstance
  obtain ⟨m, c, hc0, hcm, hstep⟩ := PGroupChain.exists_chain hpD (⊥ : Subgroup D)
  set Hs : ℕ → Subgroup (F ≃ₐ[RatFunc C] F) := fun i ↦ (c i).map D.subtype
  -- density on the decomposition field
  have hbase : ∃ s ∈ IntermediateField.fixedField (Hs m),
      DenseOn C ξ' (IntermediateField.fixedField (Hs m)) s := by
    obtain ⟨a, c', ν, hν⟩ := exists_discVal hT
    have hHm : Hs m = D := by
      simp only [Hs, hcm, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine ⟨algebraMap (RatFunc C) F RatFunc.X, IntermediateField.algebraMap_mem _ _,
      fun y hy ε hε ↦ ?_⟩
    rw [hHm] at hy
    obtain ⟨φ, hφ⟩ := exists_ratFunc_approx_of_fixed ν (ξ' := ξ') hν.symm (y := y)
      (fun σ hσ ↦ (IntermediateField.mem_fixedField_iff _ _).1 hy σ hσ) hε
    refine ⟨φ.num, φ.denom, ?_, ?_⟩
    · rw [aeval_X_eq, map_ne_zero_iff _ (algebraMap (RatFunc C) F).injective]
      exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero φ)
    · rwa [aeval_X_div]
  -- downward induction along the chain
  have key : ∀ k ≤ m, ∃ s ∈ IntermediateField.fixedField (Hs (m - k)),
      DenseOn C ξ' (IntermediateField.fixedField (Hs (m - k))) s := by
    intro k hk
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
      obtain ⟨s, hs, hsd⟩ := ih (Nat.le_of_succ_le hk)
      set i := m - (k + 1)
      have hi : i < m := by omega
      have hi1 : i + 1 = m - k := by omega
      obtain ⟨hle, hN, hidx⟩ := hstep i hi
      obtain ⟨σ', hσA, hσB, hσp, hgen⟩ := exists_step_gen hN hidx
      rw [← hi1] at hs hsd
      refine tower_step hp hKS hconst hT hr' (H := Hs (i + 1)) (H' := Hs i)
        (Subgroup.map_mono hle) ?_ (σ := σ') ⟨σ', hσA, rfl⟩ ?_ ⟨σ' ^ p, hσp, rfl⟩ ?_ ?_ hs hsd
      · rw [Subgroup.map_le_iff_le_comap]
        intro x _
        exact x.2
      · rintro ⟨x, hx, hxe⟩
        exact hσB (by rwa [Subtype.ext hxe] at hx)
      · rintro τ ⟨τ', hτ', rfl⟩
        obtain ⟨k', b, hb, hτb⟩ := hgen τ' hτ'
        exact ⟨k', b, ⟨b, hb, rfl⟩, by rw [hτb]; rfl⟩
      · rintro b ⟨b', hb', rfl⟩
        refine ⟨σ'⁻¹ * b' * σ', ?_, rfl⟩
        have hb'A : b' ∈ c (i + 1) := hle hb'
        have := hN.conj_mem ⟨b', hb'A⟩ (Subgroup.mem_subgroupOf.2 hb') ⟨σ'⁻¹, inv_mem hσA⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
  obtain ⟨s, -, hs⟩ := key m le_rfl
  have h0 : Hs (m - m) = ⊥ := by
    simp only [Nat.sub_self, Hs, hc0, Subgroup.map_bot]
  rw [h0, IntermediateField.fixedField_bot] at hs
  exact ⟨s, fun y ε hε ↦ hs y IntermediateField.mem_top ε hε⟩

end Tower

end TypeFour

end SemistableReduction
