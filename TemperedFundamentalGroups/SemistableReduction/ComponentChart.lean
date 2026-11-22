/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.GaloisLocalization
import TemperedFundamentalGroups.SemistableReduction.EtaleQuotientDedekind
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The chart of a component of the special fibre away from a divisor (generic)

MR13 step 7, D1 (S7, `V₁` part). Let `B/A` be an extension of rings, `p` a prime of `A`, `Q` a
prime of `B` over `p` (a component of the special fibre over the component `V(p)`), and `g ∈ A`
with `g ∉ p` (the nodes of `V(p)` are `V(p, g)`). The **component chart** is

  `C1 = (B/Q)[1/ḡ]`  over  `R = (A/p)[1/ḡ]`

(`ComponentChart.R`, `ComponentChart.C1`, with `M = {ḡⁿ}` and `C1 = (B/Q)_M` in the form of
`GaloisLocalization.BM`, so that `Aut_{A/p}(B/Q)` acts on it). We show:

* **`ComponentChart.isDomain_C1`**, **`injective_algebraMap_R`**: `C1` is a domain containing `R`;
* **`ComponentChart.finite_C1`**: `C1` is finite over `R` if `B` is finite over `A`;
* **`ComponentChart.etale_C1`**: if `R` is a Dedekind domain and `(B/pB)[1/ḡ]` is étale over `R`
  (purity, `PurityLocal.etale_quot_awayMap`), then `C1` is étale over `R`
  (`EtaleQuotientDedekind.etale_of_surjective`);
* **`ComponentChart.finrank_C1`**: `rank_R C1 = f(Q | p)` (`Ideal.inertiaDeg`), via
  `rank_R C1 = rank_{A/p} (B/Q) = [κ(Q) : κ(p)]` (localisations, `IsLocalizedModule.finrank_eq`,
  `IsLocalization.rank_eq`);
* **`ComponentChart.autC1`**: the action of `Aut_{A/p}(B/Q)` on `C1`, faithful
  (**`autC1_injective`**) and `R`-linear.
-/

open Module

namespace SemistableReduction

namespace ComponentChart

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) [p.IsPrime] (g : A)

/-- The powers of `ḡ` in `A/p`. -/
abbrev M : Submonoid (A ⧸ p) := Submonoid.powers (Ideal.Quotient.mk p g)

/-- `R = (A/p)[1/ḡ]`. -/
abbrev R : Type _ := Localization (M p g)

variable {p g} in
lemma M_le (hg : g ∉ p) : M p g ≤ nonZeroDivisors (A ⧸ p) := by
  refine Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero ?_)
  rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]

variable {p g} in
lemma isDomain_R (hg : g ∉ p) : IsDomain (R p g) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (R p g) (M_le hg)

variable (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p]

/-- **The component chart** `C1 = (B/Q)[1/ḡ]`. -/
abbrev C1 : Type _ := GaloisLocalization.BM (B ⧸ Q) (M p g)

omit [p.IsPrime] [Q.IsPrime] in
/-- `A/p → B/Q` is injective. -/
lemma injective_quot : Function.Injective (algebraMap (A ⧸ p) (B ⧸ Q)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a⟩ ha
  change Ideal.Quotient.mk Q (algebraMap A B a) = 0 at ha
  rw [Ideal.Quotient.eq_zero_iff_mem] at ha
  change Ideal.Quotient.mk p a = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.over_def Q p]
  exact ha

variable {p Q g} (hg : g ∉ p)

include hg in
lemma algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid (B ⧸ Q) (M p g) ≤ nonZeroDivisors (B ⧸ Q) :=
  map_le_nonZeroDivisors_of_injective _ (injective_quot p Q) (M_le hg)

include hg in
lemma isDomain_C1 : IsDomain (C1 p g Q) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (C1 p g Q) (algebraMapSubmonoid_le (Q := Q) hg)

include hg in
lemma injective_algebraMap_C1 : Function.Injective (algebraMap (B ⧸ Q) (C1 p g Q)) :=
  IsLocalization.injective _ (algebraMapSubmonoid_le (Q := Q) hg)

include hg in
/-- `R → C1` is injective. -/
lemma injective_algebraMap_R : Function.Injective (algebraMap (R p g) (C1 p g Q)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (M p g) x
  have hu := IsLocalization.map_units (C1 p g Q)
    (⟨algebraMap (A ⧸ p) (B ⧸ Q) (Ideal.Quotient.mk p g ^ n), _, ⟨n, rfl⟩, rfl⟩ :
      Algebra.algebraMapSubmonoid (B ⧸ Q) (M p g))
  have h1 : algebraMap (R p g) (C1 p g Q) (IsLocalization.mk' (R p g) a
      (⟨_, n, rfl⟩ : M p g)) * algebraMap (A ⧸ p) (C1 p g Q) (Ideal.Quotient.mk p g ^ n) =
      algebraMap (A ⧸ p) (C1 p g Q) a := by
    rw [IsScalarTower.algebraMap_apply (A ⧸ p) (R p g) (C1 p g Q), ← map_mul,
      IsLocalization.mk'_spec]
    exact (IsScalarTower.algebraMap_apply (A ⧸ p) (R p g) (C1 p g Q) a).symm
  rw [hx, zero_mul, IsScalarTower.algebraMap_apply (A ⧸ p) (B ⧸ Q) (C1 p g Q)] at h1
  have h3 : algebraMap (A ⧸ p) (B ⧸ Q) a = 0 :=
    injective_algebraMap_C1 (Q := Q) hg (by rw [map_zero]; exact h1.symm)
  have h2 : a = 0 := injective_quot p Q (h3.trans (map_zero _).symm)
  rw [h2, IsLocalization.mk'_zero]

omit [p.IsPrime] [Q.IsPrime] in
variable (p Q g) in
/-- `C1` is finite over `R`. -/
lemma finite_C1 [Module.Finite A B] : Module.Finite (R p g) (C1 p g Q) := by
  haveI : Module.Finite (A ⧸ p) (B ⧸ Q) := by
    haveI : Module.Finite A (B ⧸ Q) := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ A Q).toLinearMap Ideal.Quotient.mk_surjective
    exact Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  exact Module.Finite.of_isLocalization (A ⧸ p) (B ⧸ Q) (M p g)

/-! ### Étaleness -/

variable (B p g) in
/-- `E = (B/pB)[1/ḡ]`. -/
abbrev E : Type _ :=
  Localization.Away (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B)) (Ideal.Quotient.mk p g))

/-- `E` over `R` (the `awayMap`). -/
@[reducible] def algRE : Algebra (R p g) (E B p g) :=
  (Localization.awayMap (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B)))
    (Ideal.Quotient.mk p g)).toAlgebra

omit [p.IsPrime] [Q.IsPrime] in
lemma map_le : p.map (algebraMap A B) ≤ Q := by
  rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← Ideal.over_def Q p]

/-- `B/pB → B/Q`. -/
def factor : B ⧸ p.map (algebraMap A B) →+* B ⧸ Q := Ideal.Quotient.factor (map_le (p := p))

omit [p.IsPrime] [Q.IsPrime] in
lemma factor_mk (b : B) : factor (p := p) (Q := Q) (Ideal.Quotient.mk _ b) =
    Ideal.Quotient.mk Q b := rfl

omit [p.IsPrime] [Q.IsPrime] in
lemma factor_algebraMap (a : A ⧸ p) : factor (p := p) (Q := Q)
    (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B)) a) = algebraMap (A ⧸ p) (B ⧸ Q) a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

omit [p.IsPrime] [Q.IsPrime] in
lemma isUnit_g_C1 : IsUnit (algebraMap (B ⧸ Q) (C1 p g Q)
    (algebraMap (A ⧸ p) (B ⧸ Q) (Ideal.Quotient.mk p g))) :=
  IsLocalization.map_units (C1 p g Q) (⟨_, _, Submonoid.mem_powers _, rfl⟩ :
    Algebra.algebraMapSubmonoid (B ⧸ Q) (M p g))

/-- `E → C1`. -/
def toC1 : E B p g →+* C1 p g Q :=
  IsLocalization.Away.lift _
    (g := (algebraMap (B ⧸ Q) (C1 p g Q)).comp (factor (p := p) (Q := Q))) (by
    rw [RingHom.comp_apply, factor_algebraMap]
    exact isUnit_g_C1)

omit [p.IsPrime] [Q.IsPrime] in
lemma toC1_algebraMap (x : B ⧸ p.map (algebraMap A B)) :
    toC1 (p := p) (Q := Q) (g := g) (algebraMap _ (E B p g) x) =
      algebraMap (B ⧸ Q) (C1 p g Q) (factor x) := by
  unfold toC1
  rw [IsLocalization.Away.lift_eq]
  rfl

omit [p.IsPrime] [Q.IsPrime] in
lemma toC1_surjective : Function.Surjective (toC1 (p := p) (Q := Q) (g := g)) := by
  intro y
  obtain ⟨b, ⟨_, m, ⟨n, rfl⟩, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid (B ⧸ Q) (M p g)) y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨algebraMap _ (E B p g) (Ideal.Quotient.mk (p.map (algebraMap A B)) b) *
    IsLocalization.mk' (E B p g) (1 : B ⧸ p.map (algebraMap A B))
      (⟨algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B)) (Ideal.Quotient.mk p g) ^ n, n, rfl⟩ :
        Submonoid.powers (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B))
          (Ideal.Quotient.mk p g))), ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, mul_assoc]
  have h1 : algebraMap (B ⧸ Q) (C1 p g Q)
      (algebraMap (A ⧸ p) (B ⧸ Q) (Ideal.Quotient.mk p g ^ n)) =
      toC1 (algebraMap _ (E B p g)
        (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B)) (Ideal.Quotient.mk p g) ^ n)) := by
    simp only [toC1_algebraMap, map_pow, factor_algebraMap]
  change _ * (_ * algebraMap (B ⧸ Q) (C1 p g Q)
    (algebraMap (A ⧸ p) (B ⧸ Q) (Ideal.Quotient.mk p g ^ n))) = _
  rw [h1, ← map_mul, IsLocalization.mk'_spec, map_one, map_one, mul_one, toC1_algebraMap,
    factor_mk]

omit [p.IsPrime] [Q.IsPrime] in
/-- `toC1` is `R`-linear. -/
lemma toC1_comp : toC1.comp (Localization.awayMap
    (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B))) (Ideal.Quotient.mk p g)) =
    algebraMap (R p g) (C1 p g Q) := by
  refine IsLocalization.ringHom_ext (M p g) (RingHom.ext fun a ↦ ?_)
  simp only [RingHom.comp_apply]
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, toC1_algebraMap,
    factor_algebraMap, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

include hg in
/-- **The component chart is étale over `R`** if `R` is a Dedekind domain and `(B/pB)[1/ḡ]` is
étale over `R`. -/
theorem etale_C1 [IsDedekindDomain (A ⧸ p)]
    (hE : (Localization.awayMap (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B)))
      (Ideal.Quotient.mk p g)).Etale) :
    Algebra.Etale (R p g) (C1 p g Q) := by
  letI := algRE (B := B) (p := p) (g := g)
  haveI : Algebra.Etale (R p g) (E B p g) := RingHom.etale_algebraMap.1 hE
  haveI := isDomain_C1 (Q := Q) hg
  haveI := isDomain_R hg
  haveI : IsDedekindDomain (R p g) := IsLocalization.isDedekindDomain (A ⧸ p) (M_le hg) (R p g)
  let f : E B p g →ₐ[R p g] C1 p g Q :=
    { toC1 with commutes' := fun r ↦ RingHom.congr_fun toC1_comp r }
  exact EtaleQuotientDedekind.etale_of_surjective f toC1_surjective (injective_algebraMap_R hg)

/-! ### The degree -/

attribute [local instance] Ideal.Quotient.field in
include hg in
/-- **`rank_R C1 = f(Q | p)`.** -/
theorem finrank_C1 [Module.Finite A B] :
    finrank (R p g) (C1 p g Q) = Q.inertiaDeg A := by
  haveI := isDomain_R (p := p) hg
  -- `rank_R C1 = rank_{A/p} C1 = rank_{A/p} (B/Q)`
  have h1 : finrank (R p g) (C1 p g Q) = finrank (A ⧸ p) (C1 p g Q) := by
    simp only [Module.finrank, IsLocalization.rank_eq (R p g) (M p g) (M_le hg)]
  haveI : IsLocalizedModule (M p g)
      (IsScalarTower.toAlgHom (A ⧸ p) (B ⧸ Q) (C1 p g Q)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have h2 : finrank (A ⧸ p) (C1 p g Q) = finrank (A ⧸ p) (B ⧸ Q) :=
    IsLocalizedModule.finrank_eq (M p g)
      (IsScalarTower.toAlgHom (A ⧸ p) (B ⧸ Q) (C1 p g Q)).toLinearMap (M_le hg)
  -- `rank_{A/p} (B/Q) = [κ(Q) : κ(p)]`
  let := Localization.AtPrime.algebraOfLiesOver p Q
  letI : Algebra (A ⧸ p) Q.ResidueField :=
    ((algebraMap (B ⧸ Q) Q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ Q))).toAlgebra
  haveI : IsScalarTower (A ⧸ p) (B ⧸ Q) Q.ResidueField := .of_algebraMap_eq' rfl
  have heq : (algebraMap (B ⧸ Q) Q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ Q)) =
      (algebraMap p.ResidueField Q.ResidueField).comp (algebraMap (A ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower (A ⧸ p) p.ResidueField Q.ResidueField := .of_algebraMap_eq' heq
  haveI : FaithfulSMul (A ⧸ p) (B ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (injective_quot p Q)
  haveI : Module.Finite (A ⧸ p) (B ⧸ Q) := by
    haveI : Module.Finite A (B ⧸ Q) := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ A Q).toLinearMap Ideal.Quotient.mk_surjective
    exact Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  have h3 : finrank (A ⧸ p) (B ⧸ Q) = finrank (A ⧸ p) Q.ResidueField :=
    (IsLocalizedModule.finrank_eq (nonZeroDivisors (A ⧸ p))
      (IsScalarTower.toAlgHom (A ⧸ p) (B ⧸ Q) Q.ResidueField).toLinearMap le_rfl).symm
  have h4 : finrank p.ResidueField Q.ResidueField = finrank (A ⧸ p) Q.ResidueField := by
    simp only [Module.finrank,
      IsLocalization.rank_eq p.ResidueField (nonZeroDivisors (A ⧸ p)) le_rfl]
  rw [h1, h2, h3, ← h4, Ideal.inertiaDeg_eq p Q]

/-! ### The automorphisms -/

variable (p Q g) in
/-- The automorphism group `Aut_{A/p}(B/Q)` of the component. -/
abbrev Aut : Type _ := (B ⧸ Q) ≃ₐ[A ⧸ p] (B ⧸ Q)

/-- `Aut_{A/p}(B/Q)` acts on `C1`, `R`-linearly. -/
def autC1 (σ : Aut p Q) : C1 p g Q ≃ₐ[R p g] C1 p g Q :=
  MulSemiringAction.toAlgEquiv (R p g) (C1 p g Q) σ

omit [p.IsPrime] [Q.IsPrime] in
lemma autC1_algebraMap (σ : Aut p Q) (b : B ⧸ Q) :
    autC1 (g := g) σ (algebraMap (B ⧸ Q) (C1 p g Q) b) =
      algebraMap (B ⧸ Q) (C1 p g Q) (σ b) :=
  GaloisLocalization.smul_algebraMap' (B ⧸ Q) (M p g) σ b

omit [p.IsPrime] [Q.IsPrime] in
lemma autC1_one : autC1 (g := g) (1 : Aut p Q) = AlgEquiv.refl := by
  ext x
  exact one_smul (Aut p Q) x

omit [p.IsPrime] [Q.IsPrime] in
lemma autC1_mul (σ τ : Aut p Q) :
    autC1 (g := g) (σ * τ) = (autC1 τ).trans (autC1 σ) := by
  ext x
  exact mul_smul σ τ x

include hg in
/-- **The action on the component chart is faithful.** -/
lemma autC1_injective {σ : Aut p Q} (h : ∀ x, autC1 (g := g) σ x = x) : σ = 1 := by
  ext b
  refine injective_algebraMap_C1 (Q := Q) hg ?_
  rw [← autC1_algebraMap, h]
  rfl

end

end ComponentChart

end SemistableReduction
