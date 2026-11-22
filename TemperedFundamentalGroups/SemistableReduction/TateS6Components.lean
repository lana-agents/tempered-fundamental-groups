/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Extend
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# The Galois action on the normalisation and the components of its special fibre (generic)

For a cover `C : TateS6.CovData` (over two-chart rings `D`; the Tate instance is `TateS6.Cov`):

* **`TateS6.CovData.instMulSemiringActionB₁`**: `Gal(C.L/K)` acts on the normalisation `C.B₁` by
  ring automorphisms, `σ • b = map1 σ b` (**`smul_B₁_def`**; the maps of normalisations of I1,
  so the induced action on `C.B₁ ⧸ J` is the one of `datumHom σ`), with
  **`algebraMap_smul_B₁`** (`σ • b` is `σ b` in `C.L`) and `SMulCommClass Gal D.R1 C.B₁`;
* **`isInvariant_B₁`**: if `D.R1` is an integrally closed domain with fraction field `K`, the
  fixed points of `Gal(C.L/K)` on `C.B₁` come from `D.R1` (`Algebra.IsInvariant`); hence
  **`exists_smul_eq_of_under_eq`**: `Gal(C.L/K)` acts transitively on the primes of `C.B₁` over a
  given prime of `D.R1`: the orbit of a prime over `p` is `p.primesOver C.B₁`
  (**`orbit_eq_primesOver`**);
* **the components of the special fibre** `Spec (C.B₁ ⧸ ϖ)`:
  **`mem_minimalPrimes_iff`** — a prime `Q` of `C.B₁` is minimal over `ϖ C.B₁` iff `Q ∩ D.R1` is
  minimal over `ϖ` (going down + incomparability); **`Comp C`**, the set of these components,
  with the action of `Gal(C.L/K)` (**`instMulActionComp`**), the components over a component `p`
  of the special fibre of `D.R1` (**`compOverEquiv`**: they are `p.primesOver C.B₁`),
  transitivity over `p`
  (**`exists_smul_comp_eq`**), and the orbit–stabiliser count
  **`card_primesOver_mul_card_stabilizer`**: `#{components over p} · #Stab(Q) = [C.L : K]`.

The stabiliser of a component is its decomposition group `MulAction.stabilizer Gal(C.L/K) Q`
(MR13 step 7, D1: `Γ_v`); with `isInvariant_B₁`, Mathlib's `Ideal.Quotient.stabilizerHom` (and
its surjectivity) gives its action on the component ring `C.B₁ ⧸ Q`.
-/

universe u

open Module
open scoped Pointwise

namespace SemistableReduction

namespace TateS6

noncomputable section

namespace CovData

variable {A : Type u} [CommRing A] {K : Type u} [Field K] {D : ProjectiveLine.TwoChartRings A}
  {Rn Rc : Type u} [CommRing Rn] [CommRing Rc] [Algebra D.R1 K] [Algebra Rn K] [Algebra Rc K]
  [Algebra D.R0 Rc] {toN : D.R1 → Rn} {dT : D.R1} {c0 : D.R0} {ϖ1 : D.R1} {ϖ0 : D.R0}
  {I0 : Ideal D.R0} {q e : ℕ} (C : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e)

/-- **The Galois action on the normalisation `C.B₁`**: `σ • b = map1 σ b`. -/
instance instMulSemiringActionB₁ : MulSemiringAction (C.L ≃ₐ[K] C.L) C.B₁ where
  smul σ b := map1 (σ : C.L →ₐ[K] C.L) b
  one_smul b := map1_id b
  mul_smul σ τ b := map1_comp (τ : C.L →ₐ[K] C.L) (σ : C.L →ₐ[K] C.L) b
  smul_zero σ := map_zero (map1 (σ : C.L →ₐ[K] C.L))
  smul_add σ := map_add (map1 (σ : C.L →ₐ[K] C.L))
  smul_one σ := map_one (map1 (σ : C.L →ₐ[K] C.L))
  smul_mul σ := map_mul (map1 (σ : C.L →ₐ[K] C.L))

variable {C}

lemma smul_B₁_def (σ : C.L ≃ₐ[K] C.L) (b : C.B₁) : σ • b = map1 (σ : C.L →ₐ[K] C.L) b := rfl

/-- `σ • b` is `σ b` in `C.L`. -/
lemma algebraMap_smul_B₁ (σ : C.L ≃ₐ[K] C.L) (b : C.B₁) :
    algebraMap C.B₁ C.L (σ • b) = σ (algebraMap C.B₁ C.L b) :=
  algebraMap_map1 (σ : C.L →ₐ[K] C.L) b

/-- The Galois action on `C.B₁` fixes `D.R1`. -/
lemma smul_algebraMap_B₁ (σ : C.L ≃ₐ[K] C.L) (a : D.R1) :
    σ • algebraMap D.R1 C.B₁ a = algebraMap D.R1 C.B₁ a :=
  map1_algebraMap (σ : C.L →ₐ[K] C.L) a

instance instSMulCommClassB₁ : SMulCommClass (C.L ≃ₐ[K] C.L) D.R1 C.B₁ where
  smul_comm σ a b := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap_B₁]

variable (C) in
/-- **The fixed points of `Gal(C.L/K)` on `C.B₁` come from `D.R1`** (`D.R1` an integrally closed
domain with fraction field `K`). -/
theorem isInvariant_B₁ [IsDomain D.R1] [IsFractionRing D.R1 K] [IsIntegrallyClosed D.R1] :
    Algebra.IsInvariant D.R1 C.B₁ (C.L ≃ₐ[K] C.L) := by
  have h := ((IsGalois.tfae (F := K) (E := C.L)).out 0 1).mp C.gal
  refine ⟨fun b hb ↦ ?_⟩
  have hb' : algebraMap C.B₁ C.L b ∈
      IntermediateField.fixedField (⊤ : Subgroup (C.L ≃ₐ[K] C.L)) := by
    rintro ⟨σ, -⟩
    exact (algebraMap_smul_B₁ σ b).symm.trans (congrArg (algebraMap C.B₁ C.L) (hb σ))
  rw [h, IntermediateField.mem_bot] at hb'
  obtain ⟨x, hx⟩ := hb'
  have hbi : IsIntegral D.R1 b := IsIntegralClosure.isIntegral D.R1 C.L b
  rw [← isIntegral_algebraMap_iff (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L), ← hx,
    isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K C.L)] at hbi
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hbi
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply D.R1 C.B₁ C.L,
    (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).eq_iff] at hx
  exact ⟨a, hx⟩

/-- `C.B₁` is integral over `D.R1`. -/
lemma isIntegral_B₁ : Algebra.IsIntegral D.R1 C.B₁ :=
  IsIntegralClosure.isIntegral_algebra D.R1 C.L

/-- `C.B₁` is a domain. -/
lemma isDomain_B₁ : IsDomain C.B₁ :=
  (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _

variable [IsFractionRing D.R1 K] [IsIntegrallyClosed D.R1]

/-- **`Gal(C.L/K)` acts transitively on the primes of `C.B₁` over a prime of `D.R1`.** -/
theorem exists_smul_eq_of_under_eq [IsDomain D.R1] (P Q : Ideal C.B₁) [P.IsPrime] [Q.IsPrime]
    (h : P.under D.R1 = Q.under D.R1) : ∃ σ : C.L ≃ₐ[K] C.L, σ • P = Q := by
  haveI := isInvariant_B₁ C
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq D.R1 C.B₁ (C.L ≃ₐ[K] C.L) P Q h
  exact ⟨σ, hσ.symm⟩

/-- **The orbit of a prime `Q` of `C.B₁` over `p` is the set of all primes over `p`.** -/
theorem orbit_eq_primesOver [IsDomain D.R1] (p : Ideal D.R1) (Q : Ideal C.B₁) [Q.IsPrime]
    [Q.LiesOver p] :
    MulAction.orbit (C.L ≃ₐ[K] C.L) Q = p.primesOver C.B₁ := by
  haveI := isInvariant_B₁ C
  exact Algebra.IsInvariant.orbit_eq_primesOver D.R1 C.B₁ (C.L ≃ₐ[K] C.L) p Q

omit [IsIntegrallyClosed D.R1] in
/-- `D.R1 → C.B₁` is injective. -/
lemma injective_algebraMap_B₁ : Function.Injective (algebraMap D.R1 C.B₁) := by
  intro a b h
  have h' : algebraMap D.R1 C.L a = algebraMap D.R1 C.L b := by
    rw [IsScalarTower.algebraMap_apply D.R1 C.B₁ C.L, h, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply D.R1 K C.L, IsScalarTower.algebraMap_apply D.R1 K C.L] at h'
  exact IsFractionRing.injective D.R1 K (FaithfulSMul.algebraMap_injective K C.L h')

/-- **Components of the special fibre of `C.B₁`**: a prime `Q` of `C.B₁` is minimal over
`ϖ C.B₁` iff its contraction to `D.R1` is minimal over `ϖ` (going down for the integral
extension `D.R1 → C.B₁` of the integrally closed domain `D.R1`, and incomparability). -/
theorem mem_minimalPrimes_iff (Q : Ideal C.B₁) :
    Q ∈ (Ideal.span {algebraMap D.R1 C.B₁ ϖ1}).minimalPrimes ↔
      Q.IsPrime ∧ Q.under D.R1 ∈ (Ideal.span {ϖ1}).minimalPrimes := by
  haveI := isIntegral_B₁ (C := C)
  haveI := isDomain_B₁ (C := C)
  haveI : FaithfulSMul D.R1 C.B₁ :=
    (faithfulSMul_iff_algebraMap_injective D.R1 C.B₁).2 injective_algebraMap_B₁
  have hspan : ∀ P : Ideal C.B₁, Ideal.span {algebraMap D.R1 C.B₁ ϖ1} ≤ P ↔
      Ideal.span {ϖ1} ≤ P.under D.R1 := fun P ↦ by
    rw [Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff, Set.singleton_subset_iff]
    rfl
  constructor
  · rintro ⟨⟨hQ, hϖQ⟩, hmin⟩
    refine ⟨hQ, ⟨⟨Ideal.IsPrime.under D.R1 Q, (hspan Q).1 hϖQ⟩, fun p ⟨hp, hϖp⟩ hpQ ↦ ?_⟩⟩
    haveI := hp
    haveI : Q.LiesOver (Q.under D.R1) := ⟨rfl⟩
    obtain ⟨P, hPQ, hP, hPp⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := Q.under D.R1)
      Q hpQ
    have hPϖ : Ideal.span {algebraMap D.R1 C.B₁ ϖ1} ≤ P := by
      rw [hspan, ← Ideal.over_def P p]
      exact hϖp
    have hQP := hmin ⟨hP, hPϖ⟩ hPQ
    rw [Ideal.over_def P p]
    exact Ideal.comap_mono hQP
  · rintro ⟨hQ, ⟨⟨hp, hϖp⟩, hmin⟩⟩
    refine ⟨⟨hQ, (hspan Q).2 hϖp⟩, fun P ⟨hP, hϖP⟩ hPQ ↦ ?_⟩
    by_contra hQP
    have hlt : P < Q := lt_of_le_of_ne hPQ fun h ↦ hQP (h ▸ le_refl P)
    have h1 := Ideal.IsIntegral.comap_lt_comap (R := D.R1) hlt
    have h2 := hmin ⟨Ideal.IsPrime.under D.R1 P, (hspan P).1 hϖP⟩ h1.le
    exact (lt_irrefl _ (h1.trans_le h2))

variable (C) in
/-- **The components of the special fibre of `C.B₁`**: the minimal primes over `ϖ C.B₁`. -/
def Comp : Set (Ideal C.B₁) := (Ideal.span {algebraMap D.R1 C.B₁ ϖ1}).minimalPrimes

lemma mem_comp_iff (Q : Ideal C.B₁) :
    Q ∈ C.Comp ↔ Q.IsPrime ∧ Q.under D.R1 ∈ (Ideal.span {ϖ1}).minimalPrimes :=
  mem_minimalPrimes_iff Q

/-- **The Galois action on the components of the special fibre.** -/
instance instMulActionComp : MulAction (C.L ≃ₐ[K] C.L) C.Comp where
  smul σ Q := ⟨σ • Q.1, by
    obtain ⟨hQ, hQp⟩ := (mem_comp_iff Q.1).1 Q.2
    exact (mem_comp_iff _).2 ⟨hQ.smul σ, by rw [Ideal.under_smul]; exact hQp⟩⟩
  one_smul Q := Subtype.ext (one_smul _ Q.1)
  mul_smul σ τ Q := Subtype.ext (mul_smul σ τ Q.1)

lemma coe_smul_comp (σ : C.L ≃ₐ[K] C.L) (Q : C.Comp) : ((σ • Q : C.Comp) : Ideal C.B₁) = σ • Q.1 :=
  rfl

/-- The components over a component `p` of the special fibre of `D.R1` are the primes of `C.B₁`
over `p`. -/
lemma primesOver_subset_comp {p : Ideal D.R1} (hp : p ∈ (Ideal.span {ϖ1}).minimalPrimes) :
    p.primesOver C.B₁ ⊆ C.Comp := fun Q ⟨hQ, _⟩ ↦
  (mem_comp_iff Q).2 ⟨hQ, (Ideal.over_def Q p) ▸ hp⟩

/-- **The components of `C.B₁` over a component `p` of `D.R1`** (as a subtype of `Comp C`)
are the primes over `p`. -/
def compOverEquiv {p : Ideal D.R1} (hp : p ∈ (Ideal.span {ϖ1}).minimalPrimes) :
    {Q : C.Comp // Q.1.under D.R1 = p} ≃ p.primesOver C.B₁ where
  toFun Q := ⟨Q.1.1, ((mem_comp_iff Q.1.1).1 Q.1.2).1, ⟨Q.2.symm⟩⟩
  invFun Q := ⟨⟨Q.1, primesOver_subset_comp hp Q.2⟩, (Ideal.over_def Q.1 p).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Transitivity on the components over `p`.** -/
theorem exists_smul_comp_eq [IsDomain D.R1] (Q Q' : C.Comp) (h : Q.1.under D.R1 = Q'.1.under D.R1) :
    ∃ σ : C.L ≃ₐ[K] C.L, σ • Q = Q' := by
  haveI := ((mem_comp_iff Q.1).1 Q.2).1
  haveI := ((mem_comp_iff Q'.1).1 Q'.2).1
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_under_eq (C := C) Q.1 Q'.1 h
  exact ⟨σ, Subtype.ext hσ⟩

/-- The stabiliser of a component in `Comp C` is the stabiliser of the ideal. -/
lemma stabilizer_comp (Q : C.Comp) :
    MulAction.stabilizer (C.L ≃ₐ[K] C.L) Q = MulAction.stabilizer (C.L ≃ₐ[K] C.L) Q.1 := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
  rfl

/-- **Orbit–stabiliser for the components**: the number of components over a prime `p` of `D.R1`
times the order of the decomposition group of one of them is `[C.L : K]`. -/
theorem card_primesOver_mul_card_stabilizer [IsDomain D.R1] (p : Ideal D.R1) (Q : Ideal C.B₁)
    [Q.IsPrime] [Q.LiesOver p] :
    (p.primesOver C.B₁).ncard * Nat.card (MulAction.stabilizer (C.L ≃ₐ[K] C.L) Q) =
      finrank K C.L := by
  rw [← orbit_eq_primesOver p Q, ← MulAction.index_stabilizer, Subgroup.index_mul_card,
    ← IsGalois.card_aut_eq_finrank]

end CovData

end

end TateS6

end SemistableReduction
