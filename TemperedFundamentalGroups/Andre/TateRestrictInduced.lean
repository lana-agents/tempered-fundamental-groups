/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictObject
import TemperedFundamentalGroups.Andre.TransferGeneric

/-!
# The induction of the restricted Tate object to `[Spec R / A]` (`v(q) = 1`, B4)

For a finite group `G` acting on `R` fixing `c`, `G` acts on `B = R[x]/(x² - c)` through the
coefficients (`QuadraticLevel.actB`), commuting with `σ`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

namespace QuadraticLevel

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [MulSemiringAction G R] {c : R}
  (hcG : ∀ g : G, g • c = c)

include hcG in
lemma I_le_comap (g : G) :
    I c ≤ (I c).comap (MvPolynomial.map (MulSemiringAction.toRingHom G R g)) := by
  rw [I, Ideal.span_le, Set.singleton_subset_iff]
  change MvPolynomial.map _ (MvPolynomial.X 0 ^ 2 - MvPolynomial.C c) ∈ I c
  rw [map_sub, map_pow, MvPolynomial.map_X, MvPolynomial.map_C]
  change MvPolynomial.X 0 ^ 2 - MvPolynomial.C (g • c) ∈ I c
  rw [hcG]
  exact Ideal.subset_span rfl

/-- **The action of `g ∈ G` on `B c` through the coefficients.** -/
def actB (g : G) : B c →+* B c :=
  Ideal.quotientMap (I c) (MvPolynomial.map (MulSemiringAction.toRingHom G R g))
    (I_le_comap hcG g)

lemma actB_algebraMap (g : G) (r : R) :
    actB hcG g (algebraMap R (B c) r) = algebraMap R (B c) (g • r) := by
  change actB hcG g (Ideal.Quotient.mk _ (MvPolynomial.C r)) = Ideal.Quotient.mk _ _
  rw [actB, Ideal.quotientMap_mk, MvPolynomial.map_C]
  rfl

lemma actB_x (g : G) : actB hcG g (x c) = x c := by
  change actB hcG g (Ideal.Quotient.mk _ (MvPolynomial.X 0)) = Ideal.Quotient.mk _ _
  rw [actB, Ideal.quotientMap_mk, MvPolynomial.map_X]

/-- Ring maps out of `B c` are determined by `algebraMap` and `x`. -/
lemma ringHom_ext {S : Type*} [Semiring S] {φ ψ : B c →+* S}
    (h₁ : ∀ r, φ (algebraMap R (B c) r) = ψ (algebraMap R (B c) r)) (h₂ : φ (x c) = ψ (x c)) :
    φ = ψ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r ↦ h₁ r) fun i ↦ ?_)
  rw [Subsingleton.elim i 0]
  exact h₂

lemma actB_mul (g h : G) : actB hcG (g * h) = (actB hcG g).comp (actB hcG h) :=
  ringHom_ext (fun r ↦ by simp [actB_algebraMap, mul_smul]) (by simp [actB_x])

lemma actB_one : actB hcG (1 : G) = RingHom.id _ :=
  ringHom_ext (fun r ↦ by simp [actB_algebraMap]) (by simp [actB_x])

lemma actB_σ (g : G) : (actB hcG g).comp (σ c : B c →+* B c) =
    (σ c : B c →+* B c).comp (actB hcG g) :=
  ringHom_ext (fun r ↦ by simp [actB_algebraMap]) (by simp [actB_x])

lemma actB_bijective (g : G) : Function.Bijective (actB hcG g) := by
  refine Function.bijective_iff_has_inverse.2 ⟨actB hcG g⁻¹, fun b ↦ ?_, fun b ↦ ?_⟩
  · rw [← RingHom.comp_apply, ← actB_mul, inv_mul_cancel, actB_one, RingHom.id_apply]
  · rw [← RingHom.comp_apply, ← actB_mul, mul_inv_cancel, actB_one, RingHom.id_apply]

end

end QuadraticLevel

namespace TateRestrict

open RamifiedQuadratic SemistableReduction.W10Apply QuadraticLevel

noncomputable section

/-! ### The induced ring `A → B` -/

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (R : Type u) [CommRing R]
  [Algebra K R] (A : Type u) [Group A] [Fintype A] [DecidableEq A] [MulSemiringAction A R]
  [SMulCommClass A K R]

local notation "Bc" => BR (ϖ := ϖ) R

omit [Fintype A] [DecidableEq A] in
lemma cR_smul (a : A) : a • cR (ϖ := ϖ) R = cR (ϖ := ϖ) R := smul_algebraMap a (ϖ : K)

/-- The generators `e_a` and `x` of `A → B`. -/
def indGen : Fin (Fintype.card A + 1) → (A → Bc) :=
  Fin.lastCases (fun _ ↦ x (cR (ϖ := ϖ) R)) fun i ↦ Pi.single ((Fintype.equivFin A).symm i) 1

/-- `R[x_a, x] → (A → B)`. -/
def indMapR : MvPolynomial (Fin (Fintype.card A + 1)) R →ₐ[R] (A → Bc) :=
  MvPolynomial.aeval (indGen (ϖ := ϖ) R A)

omit [Group A] [MulSemiringAction A R] [SMulCommClass A K R] in
lemma indMapR_surjective : Function.Surjective (indMapR (ϖ := ϖ) R A) := by
  have hdiag : ∀ b : Bc, Pi.constAlgHom R A Bc b ∈ (indMapR (ϖ := ϖ) R A).range := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (I (cR (ϖ := ϖ) R)) b
    refine ⟨MvPolynomial.rename (fun _ ↦ Fin.last _) p, ?_⟩
    have : (indMapR (ϖ := ϖ) R A).comp (MvPolynomial.rename fun _ ↦ Fin.last _) =
        (Pi.constAlgHom R A Bc).comp (Ideal.Quotient.mkₐ R (I (cR (ϖ := ϖ) R))) := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      simp only [AlgHom.comp_apply, MvPolynomial.rename_X, indMapR, MvPolynomial.aeval_X,
        indGen, Fin.lastCases_last]
      rw [Subsingleton.elim i 0]
      rfl
    exact AlgHom.congr_fun this p
  have hsingle : ∀ a b, Pi.single a b ∈ (indMapR (ϖ := ϖ) R A).range := by
    intro a b
    have he : (Pi.single a 1 : A → Bc) ∈ (indMapR (ϖ := ϖ) R A).range :=
      ⟨MvPolynomial.X (Fin.castSucc (Fintype.equivFin A a)), by
        simp [indMapR, indGen]⟩
    have : (Pi.single a b : A → Bc) = Pi.single a 1 * Pi.constAlgHom R A Bc b := by
      ext c
      by_cases h : c = a
      · subst h; simp
      · simp [h]
    rw [this]
    exact mul_mem he (hdiag b)
  intro f
  have : f = ∑ a, Pi.single a (f a) := (Finset.univ_sum_single f).symm
  rw [this]
  exact sum_mem fun a _ ↦ hsingle a (f a)

/-- The ideal of relations. -/
def indIdealR : Ideal (MvPolynomial (Fin (Fintype.card A + 1)) R) :=
  RingHom.ker (indMapR (ϖ := ϖ) R A)

/-- The coded ring `≅ A → B`. -/
def indEquivR : LevelRing R _ (indIdealR (ϖ := ϖ) R A) ≃ₐ[R] (A → Bc) :=
  Ideal.quotientKerAlgEquivOfSurjective (indMapR_surjective R A)

/-! ### The twisted automorphisms -/

variable {R A} (A' : Type u) [Group A'] [MulSemiringAction A' R] [Subsingleton A']

local notation "H'" => Subgroup.zpowers (σS (cR (ϖ := ϖ) R) A')

omit [Fintype A] [DecidableEq A] in
lemma actB_comm (a : A) {g : SemilinearAut R A' Bc} (hg : g ∈ H') (b : Bc) :
    actB (cR_smul (ϖ := ϖ) R A) a (g.σ b) = g.σ (actB (cR_smul (ϖ := ϖ) R A) a b) := by
  rcases eq_one_or_eq_σS _ A' hg with rfl | rfl
  · rfl
  · exact RingHom.congr_fun (actB_σ (cR_smul (ϖ := ϖ) R A) a) b

/-- `f ↦ (b ↦ a · g(f(a⁻¹ b)))` on `A → B`. -/
def twR (a : A) (g : SemilinearAut R A' Bc) : (A → Bc) →+* (A → Bc) :=
  RingHom.pi fun b ↦ (actB (cR_smul (ϖ := ϖ) R A) a).comp
    ((g.σ : Bc →+* Bc).comp (Pi.evalRingHom (fun _ : A ↦ Bc) (a⁻¹ * b)))

omit [Fintype A] [DecidableEq A] [Subsingleton A'] in
lemma twR_apply (a : A) (g : SemilinearAut R A' Bc) (f : A → Bc) (b : A) :
    twR A' a g f b = actB (cR_smul (ϖ := ϖ) R A) a (g.σ (f (a⁻¹ * b))) := rfl

omit [Fintype A] [DecidableEq A] in
lemma twR_mul (a a' : A) {g : SemilinearAut R A' Bc} (hg : g ∈ H') (g' : SemilinearAut R A' Bc) :
    (twR A' a g).comp (twR A' a' g') = twR A' (a * a') (g * g') := by
  ext f b
  simp only [RingHom.comp_apply, twR_apply, SemilinearAut.mul_σ, RingEquiv.trans_apply,
    mul_inv_rev, mul_assoc]
  rw [← actB_comm A' a' hg, ← RingHom.comp_apply (actB _ a), ← actB_mul]

omit [Fintype A] [DecidableEq A] [Subsingleton A'] in
lemma twR_one : twR (ϖ := ϖ) (R := R) (A := A) A' 1 1 = RingHom.id _ := by
  ext f b
  simp [twR_apply, actB_one]

omit [Fintype A] [DecidableEq A] in
lemma twR_algebraMap (a : A) (g : SemilinearAut R A' Bc) (r : R) :
    twR A' a g (algebraMap R (A → Bc) r) = algebraMap R (A → Bc) (a • r) := by
  ext b
  change actB (cR_smul (ϖ := ϖ) R A) a (g.σ (algebraMap R Bc r)) = algebraMap R Bc (a • r)
  rw [g.map_algebraMap, Subsingleton.elim g.a 1, one_smul, actB_algebraMap]

/-- **The semilinear automorphism `(a, g)` of the induced ring.** -/
def indAutR (a : A) (g : H') : SemilinearAut R A (LevelRing R _ (indIdealR (ϖ := ϖ) R A)) where
  a := a
  σ := RingEquiv.ofRingHom
    ((indEquivR R A).symm.toRingHom.comp ((twR A' a g.1).comp (indEquivR R A).toRingHom))
    ((indEquivR R A).symm.toRingHom.comp ((twR A' a⁻¹ g⁻¹.1).comp (indEquivR R A).toRingHom))
    (RingHom.ext fun y ↦ by
      change (indEquivR R A).symm (twR A' a g.1 (indEquivR R A ((indEquivR R A).symm
        (twR A' a⁻¹ g⁻¹.1 (indEquivR R A y))))) = y
      rw [AlgEquiv.apply_symm_apply, ← RingHom.comp_apply (twR A' a _), twR_mul A' _ _ g.2,
        mul_inv_cancel, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, twR_one,
        RingHom.id_apply, AlgEquiv.symm_apply_apply])
    (RingHom.ext fun y ↦ by
      change (indEquivR R A).symm (twR A' a⁻¹ g⁻¹.1 (indEquivR R A ((indEquivR R A).symm
        (twR A' a g.1 (indEquivR R A y))))) = y
      rw [AlgEquiv.apply_symm_apply, ← RingHom.comp_apply (twR A' a⁻¹ _), twR_mul A' _ _ g⁻¹.2,
        inv_mul_cancel, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, twR_one,
        RingHom.id_apply, AlgEquiv.symm_apply_apply])
  map_algebraMap r := by
    change (indEquivR R A).symm (twR A' a g.1 (indEquivR R A (algebraMap R _ r))) = _
    rw [AlgEquiv.commutes, twR_algebraMap, AlgEquiv.commutes]

lemma indAutR_σ (a : A) (g : H') (y : LevelRing R _ (indIdealR (ϖ := ϖ) R A)) :
    (indAutR A' a g).σ y = (indEquivR R A).symm (twR A' a g.1 (indEquivR R A y)) := rfl

/-- `A × ⟨σ⟩ →* G_B`. -/
def indHomR : A × H' →* SemilinearAut R A (LevelRing R _ (indIdealR (ϖ := ϖ) R A)) where
  toFun p := indAutR A' p.1 p.2
  map_one' := SemilinearAut.ext rfl (by
    ext y
    change (indEquivR R A).symm (twR A' 1 1 (indEquivR R A y)) = y
    rw [twR_one, RingHom.id_apply, AlgEquiv.symm_apply_apply])
  map_mul' p q := SemilinearAut.ext rfl (by
    ext y
    change (indEquivR R A).symm (twR A' (p.1 * q.1) (p.2 * q.2).1 (indEquivR R A y)) =
      (indEquivR R A).symm (twR A' p.1 p.2.1 (indEquivR R A ((indEquivR R A).symm
        (twR A' q.1 q.2.1 (indEquivR R A y)))))
    rw [AlgEquiv.apply_symm_apply, ← RingHom.comp_apply (twR A' p.1 _), twR_mul A' _ _ p.2.2]
    rfl)

omit [Fintype A] [DecidableEq A] in
lemma twR_const (a : A) {g : SemilinearAut R A' Bc} (hg : g ∈ H') (y : Bc) :
    twR A' a g (fun b ↦ actB (cR_smul (ϖ := ϖ) R A) b y) =
      fun b ↦ actB (cR_smul (ϖ := ϖ) R A) b (g.σ y) := by
  ext b
  rw [twR_apply, ← actB_comm A' (a⁻¹ * b) hg, ← RingHom.comp_apply (actB _ a), ← actB_mul,
    mul_inv_cancel_left]

lemma indHomR_injective : Function.Injective (indHomR (ϖ := ϖ) (R := R) (A := A) A') := by
  intro p q h
  have ha : p.1 = q.1 := congrArg SemilinearAut.a h
  refine Prod.ext ha (Subtype.ext (SemilinearAut.ext (Subsingleton.elim _ _)
    (RingEquiv.ext fun y ↦ ?_)))
  have h1 := congrArg (fun g : SemilinearAut R A _ ↦ indEquivR R A
    (g.σ ((indEquivR R A).symm fun b ↦ actB (cR_smul (ϖ := ϖ) R A) b y)) p.1) h
  change indEquivR R A ((indEquivR R A).symm (twR A' p.1 p.2.1 (indEquivR R A
      ((indEquivR R A).symm _)))) p.1 = indEquivR R A ((indEquivR R A).symm (twR A' q.1 q.2.1
      (indEquivR R A ((indEquivR R A).symm _)))) p.1 at h1
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply] at h1
  rw [twR_const A' _ p.2.2, twR_const A' _ q.2.2] at h1
  exact (actB_bijective _ p.1).1 h1

/-! ### The induced level with the model -/

variable (hϖ : Irreducible ϖ) [CharZero K]

/-- **The induced level** `(A → R[t]/(t² - ϖ), A × ⟨σ⟩)` of `[Spec R / A]`. -/
def indLevelR : FiniteLevel R A where
  n := Fintype.card A + 1
  I := indIdealR (ϖ := ϖ) R A
  etale := by
    haveI := QuadraticLevel.etale (isUnit_two (K := K) R) (isUnit_cR hϖ R)
    exact Algebra.Etale.of_equiv (indEquivR R A).symm
  finite := by
    haveI : Module.Finite R Bc := QuadraticLevel.finite _
    exact Module.Finite.equiv (indEquivR R A).symm.toLinearEquiv
  H := (indHomR (ϖ := ϖ) (R := R) (A := A) A').range
  surjective a := ⟨indHomR A' (a, 1), ⟨_, rfl⟩, rfl⟩

/-- The decomposition `H ≅ A × ⟨σ⟩`. -/
def indHEquiv : A × H' ≃* (indLevelR (R := R) (A := A) A' hϖ).H :=
  MonoidHom.ofInjective (indHomR_injective A')

/-- `τ : B → (A → B)`, `τ(y)(b) = b · y`. -/
def τInd : Bc →+* (indLevelR (R := R) (A := A) A' hϖ).B :=
  (indEquivR R A).symm.toRingHom.comp
    (RingHom.pi fun b ↦ actB (cR_smul (ϖ := ϖ) R A) b)

lemma indHEquiv_apply (p : A × H') :
    (indHEquiv (R := R) (A := A) A' hϖ p).1 = indHomR A' p := rfl

lemma σ_τR (g : (indLevelR (R := R) (A := A) A' hϖ).H) (y : Bc) :
    g.1.σ (τInd A' hϖ y) = τInd A' hϖ (((indHEquiv A' hϖ).symm g).2.1.σ y) := by
  set p := (indHEquiv (R := R) (A := A) A' hϖ).symm g
  have hg : g = indHEquiv A' hϖ p := ((indHEquiv A' hϖ).apply_symm_apply g).symm
  rw [hg, indHEquiv_apply]
  change (indEquivR R A).symm (twR A' p.1 p.2.1 (indEquivR R A ((indEquivR R A).symm _))) = _
  rw [AlgEquiv.apply_symm_apply]
  change _ = (indEquivR R A).symm _
  congr 1
  exact twR_const A' p.1 p.2.2 y

lemma σ_symm_comp_τR (g : (indLevelR (R := R) (A := A) A' hϖ).H) :
    (g.1.σ.symm.toRingHom : (indLevelR (R := R) (A := A) A' hϖ).B →+* _).comp (τInd A' hϖ) =
      (τInd A' hϖ).comp
        (((indHEquiv A' hϖ).symm g).2.1.σ.symm.toRingHom : Bc →+* Bc) := by
  refine RingHom.ext fun y ↦ ?_
  change g.1.σ.symm (τInd A' hϖ y) = τInd A' hϖ (_)
  rw [RingEquiv.symm_apply_eq, σ_τR]
  exact congrArg _ (RingEquiv.apply_symm_apply _ y).symm

lemma τR_levelStructureMap :
    (τInd (ϖ := ϖ) (R := R) (A := A) A' hϖ).comp
        (levelStructureMap O R A' (levelR (hϖ := hϖ) (R := R) (A := A'))) =
      levelStructureMap O R A (indLevelR (R := R) (A := A) A' hϖ) := by
  refine RingHom.ext fun o ↦ ?_
  change (indEquivR R A).symm (fun b ↦ actB (cR_smul (ϖ := ϖ) R A) b
    (algebraMap R Bc (algebraMap K R o))) = algebraMap R _ (algebraMap K R o)
  have : (fun b ↦ actB (cR_smul (ϖ := ϖ) R A) b (algebraMap R Bc (algebraMap K R o))) =
      algebraMap R (A → Bc) (algebraMap K R o) := by
    ext b
    rw [actB_algebraMap, smul_algebraMap]
    rfl
  rw [this, AlgEquiv.commutes]

variable [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (b₄ b₆ : O)
  [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)))]
  {x y : R} (heqR : y ^ 2 + x * y = x ^ 3 + algebraMap K R (ϖ * b₄) * x + algebraMap K R (ϖ * b₆))

/-- The action of `H = A × ⟨σ⟩` on the model, through `⟨σ⟩`. -/
def indρ : (indLevelR (R := R) (A := A) A' hϖ).H →* Aut (modelR hϖ b₄ b₆).scheme :=
  (ρH hϖ R b₄ b₆ A').comp ((MonoidHom.snd _ _).comp (indHEquiv A' hϖ).symm.toMonoidHom)

/-- **The induced level with the model**: `j = j₀ ∘ Spec τ`. -/
def indLvR : Level O R A where
  L := indLevelR A' hϖ
  c := modelR hϖ b₄ b₆
  j := Spec.map (CommRingCat.ofHom (τInd A' hϖ)) ≫ jR hϖ R b₄ b₆ heqR
  j_toSpec := by
    rw [Category.assoc, jR_toSpec hϖ R b₄ b₆ heqR A']
    erw [← Spec.map_comp, ← CommRingCat.ofHom_comp, τR_levelStructureMap]
  ρ := indρ A' hϖ b₄ b₆
  ρ_toSpec g := ρfun_toSpec hϖ R b₄ b₆ A' _
  ρ_j g := by
    have hg := QuadraticLevel.eq_one_or_eq_σS _ A' ((indHEquiv A' hϖ).symm g).2.2
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    erw [σ_symm_comp_τR A' hϖ g]
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    erw [ρfun_j hϖ R b₄ b₆ heqR A' hg]
    rfl

/-- The element `(1, h)` of `H⁰` of the induced level. -/
def ιH0 : (levelR (hϖ := hϖ) (R := R) (A := A')).H →* (indLevelR (R := R) (A := A) A' hϖ).H0 :=
  ((indHEquiv (R := R) (A := A) A' hϖ).toMonoidHom.comp (MonoidHom.inr A H')).codRestrict _
    fun _ ↦ FiniteLevel.mem_H0.2 rfl

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma ιH0_σ (h : (levelR (hϖ := hϖ) (R := R) (A := A')).H)
    (z : (indLevelR (R := R) (A := A) A' hϖ).B) :
    (ιH0 A' hϖ h).1.1.σ z = (indEquivR R A).symm (twR A' 1 h.1 (indEquivR R A z)) := rfl

lemma ρs_indLvR (g : (indLevelR (R := R) (A := A) A' hϖ).H)
    (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    ((indLvR (A := A) A' hϖ b₄ b₆ heqR).ρs g z).1 =
      ((levelM hϖ R b₄ b₆ heqR A').ρs ((indHEquiv A' hϖ).symm g).2 z).1 :=
  rfl

lemma preserves_indLvR (g : (indLevelR (R := R) (A := A) A' hϖ).H) :
    (decompR hϖ b₄ b₆).Preserves ((indLvR (A := A) A' hϖ b₄ b₆ heqR).ρs g) :=
  Preserves.of_eq (preserves_ρs hϖ b₄ b₆ R heqR A' ((indHEquiv A' hϖ).symm g).2)
    fun z ↦ Subtype.ext (ρs_indLvR (A := A) A' hϖ b₄ b₆ heqR g z)

/-- **The induced object** `Ind X₀'` of `[Spec R / A]`. -/
def indObjR : TempObj O R A where
  Lv := indLvR (A := A) A' hϖ b₄ b₆ heqR
  P := (decompR hϖ b₄ b₆).toCodeEq _ (preserves_indLvR (A := A) A' hϖ b₄ b₆ heqR)

/-- The deck transformations of `Ind X₀'`. -/
def indDeckR (d : Multiplicative ℤ) :
    indObjR (A := A) A' hϖ b₄ b₆ heqR ⟶ indObjR (A := A) A' hϖ b₄ b₆ heqR where
  φ := 𝟙 _
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := by rw [TempObj.spec_map_id_f, Category.comp_id, Category.id_comp]
  h := (decompR hϖ b₄ b₆).deckCodeEq _ (preserves_indLvR (A := A) A' hϖ b₄ b₆ heqR) d
  continuous_h :=
    ((decompR hϖ b₄ b₆).deckCodeEq _ (preserves_indLvR (A := A) A' hϖ b₄ b₆ heqR) d).continuous
  fst_h _ := rfl
  h_act g x :=
    (decompR hϖ b₄ b₆).deckCodeEq_act _ (preserves_indLvR (A := A) A' hϖ b₄ b₆ heqR) d g x

/-! ### The inclusion `X₀' ⟶ Res (Ind X₀')` -/

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
include hϖ in
/-- Evaluation at `1 ∈ A`. -/
def evalOneR : (indLevelR (R := R) (A := A) A' hϖ).B →ₐ[R] Bc :=
  (Pi.evalAlgHom R (fun _ : A ↦ Bc) 1).comp (indEquivR R A).toAlgHom

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma evalOneR_τR (y : Bc) : evalOneR (A := A) A' hϖ (τInd A' hϖ y) = y := by
  change indEquivR R A ((indEquivR R A).symm _) 1 = y
  rw [AlgEquiv.apply_symm_apply]
  exact RingHom.congr_fun (actB_one (cR_smul (ϖ := ϖ) R A)) y

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma evalOneR_σ (h : (levelR (hϖ := hϖ) (R := R) (A := A')).H)
    (z : (indLevelR (R := R) (A := A) A' hϖ).B) :
    evalOneR (A := A) A' hϖ ((ιH0 A' hϖ h).1.1.σ z) = h.1.σ (evalOneR A' hϖ z) := by
  rw [ιH0_σ]
  change indEquivR R A ((indEquivR R A).symm _) 1 = _
  rw [AlgEquiv.apply_symm_apply, twR_apply, inv_one, one_mul, actB_one]
  rfl

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- The map of levels onto the component `1 ∈ A`. -/
def ιLevelR : levelR (hϖ := hϖ) (R := R) (A := A') ⟶
    (indLevelR (R := R) (A := A) A' hϖ).res A' where
  f := evalOneR A' hϖ
  r := (FiniteLevel.resEquiv A' _).toMonoidHom.comp (ιH0 A' hϖ)
  r_a _ := Subsingleton.elim _ _
  f_σ g y := by
    have h := evalOneR_σ (A := A) A' hϖ g y
    rw [← FiniteLevel.σ_resEquiv A' _ (ιH0 A' hϖ g)] at h
    exact h

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma indHEquiv_symm_ιH0 (h : (levelR (hϖ := hϖ) (R := R) (A := A')).H) :
    (indHEquiv (R := R) (A := A) A' hϖ).symm (ιH0 A' hϖ h).1 = (1, h) :=
  (indHEquiv A' hϖ).symm_apply_apply _

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma evalOneR_τR_spec :
    Spec.map (CommRingCat.ofHom ((evalOneR (R := R) (A := A) A' hϖ).toRingHom :
      (indLevelR (R := R) (A := A) A' hϖ).B →+* Bc)) ≫
        Spec.map (CommRingCat.ofHom (τInd A' hϖ)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : ((evalOneR (R := R) (A := A) A' hϖ).toRingHom :
      (indLevelR (R := R) (A := A) A' hϖ).B →+* Bc).comp
      (τInd A' hϖ) = RingHom.id _ := RingHom.ext (evalOneR_τR A' hϖ)
  rw [this, CommRingCat.ofHom_id, Spec.map_id]

lemma j_eqR : jR hϖ R b₄ b₆ heqR =
    Spec.map (CommRingCat.ofHom ((evalOneR (R := R) (A := A) A' hϖ).toRingHom :
      (indLevelR (R := R) (A := A) A' hϖ).B →+* Bc)) ≫
        (Spec.map (CommRingCat.ofHom (τInd A' hϖ)) ≫ jR hϖ R b₄ b₆ heqR) :=
  ((Category.id_comp _).symm.trans
    (congrArg (· ≫ jR hϖ R b₄ b₆ heqR) (evalOneR_τR_spec A' hϖ).symm)).trans
    (Category.assoc _ _ _)

omit [Fintype A] [DecidableEq A] [MulSemiringAction A R] [SMulCommClass A K R]
  [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma _root_.TemperedFundamentalGroups.TateCovering.Decomp.toCodeEq_act_congr {Z : Type u}
    [TopologicalSpace Z] (D : TateCovering.Decomp Z) {G G' : Type u} [Group G] [Group G']
    (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, D.Preserves (ρ g)) (ρ' : G' →* (Z ≃ₜ Z))
    (hρ' : ∀ g, D.Preserves (ρ' g)) {g : G} {g' : G'} (h : ∀ z, ρ g z = ρ' g' z)
    (x : (D.toCodeEq ρ hρ).carrier) :
    (D.toCodeEq ρ hρ).act g x = (D.toCodeEq ρ' hρ').act g' x := by
  letI := D.codeTop
  change D.codeHomeomorph.symm (D.liftAct ρ hρ g (D.codeHomeomorph x)) =
    D.codeHomeomorph.symm (D.liftAct ρ' hρ' g' (D.codeHomeomorph x))
  congr 1
  exact TateCovering.Decomp.Space.ext (h _) rfl

lemma ρs_ιLevelR (g : (levelR (hϖ := hϖ) (R := R) (A := A')).H)
    (z : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    (levelM hϖ R b₄ b₆ heqR A').ρs g z = (indLvR (A := A) A' hϖ b₄ b₆ heqR).ρs
      ((FiniteLevel.resEquiv A' _).symm ((ιLevelR (A := A) A' hϖ).r g)).1 z := by
  refine Subtype.ext ((ρs_indLvR (A := A) A' hϖ b₄ b₆ heqR _ _).trans ?_).symm
  have e : ((FiniteLevel.resEquiv A' _).symm ((ιLevelR (A := A) A' hϖ).r g)) =
      ιH0 A' hϖ g := (FiniteLevel.resEquiv A' _).symm_apply_apply _
  rw [e, indHEquiv_symm_ιH0]

/-- **The inclusion `X₀' ⟶ Res (Ind X₀')`** of the component `1 ∈ A`. -/
def ιR : X₀' hϖ b₄ b₆ R heqR A' ⟶
    (resFunctor O R A A').obj (indObjR (A := A) A' hϖ b₄ b₆ heqR) where
  φ := ιLevelR A' hϖ
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := (Category.comp_id _).trans (j_eqR A' hϖ b₄ b₆ heqR)
  h := fun x ↦ x
  continuous_h := continuous_id
  fst_h _ := rfl
  h_act g x := TateCovering.Decomp.toCodeEq_act_congr (decompR hϖ b₄ b₆) _ _ _ _
    (ρs_ιLevelR A' hϖ b₄ b₆ heqR g) x

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma evalOneR_surjective : Function.Surjective (evalOneR (R := R) (A := A) A' hϖ) :=
  fun y ↦ ⟨τInd A' hϖ y, evalOneR_τR A' hϖ y⟩

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma eq_ιH0 (G : (indLevelR (R := R) (A := A) A' hϖ).H0) :
    G = ιH0 A' hϖ ((indHEquiv A' hϖ).symm G.1).2 := by
  set p := (indHEquiv (R := R) (A := A) A' hϖ).symm G.1
  have hp1 : p.1 = 1 := by
    have h1 := FiniteLevel.mem_H0.1 G.2
    have h2 : G.1 = indHEquiv A' hϖ p := ((indHEquiv A' hϖ).apply_symm_apply _).symm
    rw [h2] at h1
    exact h1
  refine Subtype.ext ((indHEquiv A' hϖ).symm.injective ?_)
  rw [indHEquiv_symm_ιH0]
  exact Prod.ext hp1 rfl

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- `X₀' ⟶ Res (Ind X₀')` is injective on fibres. -/
lemma fibreMap_ιR_injective :
    Function.Injective ((tempFibre O R A' V hV).map (ιR (A := A) A' hϖ b₄ b₆ heqR)) := by
  intro u v huv
  induction u using Quotient.inductionOn with | h q => ?_
  induction v using Quotient.inductionOn with | h q' => ?_
  have huv' : (⟦TempObj.preMap V hV (ιR (A := A) A' hϖ b₄ b₆ heqR) q⟧ :
      TempObj.Fibre Ω V hV ((resFunctor O R A A').obj (indObjR (A := A) A' hϖ b₄ b₆ heqR))) =
      ⟦TempObj.preMap V hV (ιR (A := A) A' hϖ b₄ b₆ heqR) q'⟧ := huv
  obtain ⟨g', hg'⟩ := Quotient.exact huv'
  set G := (FiniteLevel.resEquiv A' _).symm g'.1
  set h := ((indHEquiv (R := R) (A := A) A' hϖ).symm G.1).2
  have hG : G = ιH0 A' hϖ h := eq_ιH0 A' hϖ G
  have hgr : g'.1 = (ιLevelR (A := A) A' hϖ).r h := by
    change g'.1 = FiniteLevel.resEquiv A' _ (ιH0 A' hϖ h)
    rw [← hG]
    exact ((FiniteLevel.resEquiv A' _).apply_symm_apply _).symm
  have h1 := congrArg (fun r : TempObj.PreFibre Ω V hV _ ↦ r.1.1) hg'
  have h2 := congrArg (fun r : TempObj.PreFibre Ω V hV _ ↦ r.1.2) hg'
  simp only [TempObj.smul_val] at h1 h2
  have ht : FiniteLevel.fibreAct Ω (X₀' hϖ b₄ b₆ R heqR A').Lv.L
      ⟨h, FiniteLevel.mem_H0.2 (Subsingleton.elim _ _)⟩ q'.1.1 = q.1.1 := by
    refine AlgHom.ext fun w ↦ ?_
    obtain ⟨z, rfl⟩ := evalOneR_surjective (A := A) A' hϖ w
    have h1z := DFunLike.congr_fun h1 z
    change q'.1.1 (evalOneR A' hϖ (g'.1.1.σ.symm z)) = q.1.1 (evalOneR A' hϖ z) at h1z
    rw [FiniteLevel.fibreAct_apply, ← h1z]
    congr 1
    have key := (ιLevelR (A := A) A' hϖ).f_σ h (g'.1.1.σ.symm z)
    rw [← hgr] at key
    erw [RingEquiv.apply_symm_apply] at key
    rw [RingEquiv.symm_apply_eq]
    exact key
  have hp : (X₀' hϖ b₄ b₆ R heqR A').P.act h q'.1.2 = q.1.2 := by
    refine Eq.trans ?_ h2
    refine TateCovering.Decomp.toCodeEq_act_congr (decompR hϖ b₄ b₆) _ _ _ _ (fun z ↦ ?_) _
    rw [hgr]
    exact ρs_ιLevelR A' hϖ b₄ b₆ heqR h z
  exact Quotient.sound ⟨⟨h, FiniteLevel.mem_H0.2 (Subsingleton.elim _ _)⟩,
    Subtype.ext (Prod.ext ht hp)⟩

/-- Fibre elements of `Ind X₀'` over a common geometric point are related by deck
transformations. -/
lemma indObjR_deck (q q' : TempObj.PreFibre Ω V hV (indObjR (A := A) A' hϖ b₄ b₆ heqR))
    (h : q.1.1 = q'.1.1) : ∃ e : indObjR (A := A) A' hϖ b₄ b₆ heqR ⟶ indObjR A' hϖ b₄ b₆ heqR,
      (tempFibre O R A V hV).map e ⟦q⟧ = ⟦q'⟧ := by
  have hbase : q.1.2.1.1 = q'.1.2.1.1 := Subtype.ext (q.2.trans
    ((congrArg (fun t ↦ ((indObjR (A := A) A' hϖ b₄ b₆ heqR).Lv.sp V hV t :
      (indObjR (A := A) A' hϖ b₄ b₆ heqR).Lv.c.scheme)) h).trans q'.2.symm))
  obtain ⟨d, hd, -⟩ := (decompR hϖ b₄ b₆).existsUnique_deckCodeEq _
    (preserves_indLvR (A := A) A' hϖ b₄ b₆ heqR) hbase
  refine ⟨indDeckR A' hϖ b₄ b₆ heqR d, ?_⟩
  change (⟦TempObj.preMap V hV (indDeckR (A := A) A' hϖ b₄ b₆ heqR d) q⟧ :
    TempObj.Fibre Ω V hV (indObjR (A := A) A' hϖ b₄ b₆ heqR)) = ⟦q'⟧
  exact congrArg _ (Subtype.ext (Prod.ext ((AlgHom.comp_id _).trans h) hd))

omit [Fintype A] [DecidableEq A] in
/-- **Non-degeneracy of `temperedPi1 [Spec R / A]` from a nontrivial character of `X₀'`**
(`v(q) = 1`): an open normal subgroup with infinite quotient, the kernel of the action on the
fibre of `Ind X₀'`. -/
theorem exists_open_normal_infinite_quotient_of_ne_one' [Finite A] [IsAlgClosed Ω]
    (hχ : ∃ τ, character' hϖ b₄ b₆ R heqR A' V hV τ ≠ 1) :
    ∃ N : Subgroup (temperedPi1 O R A V hV), IsOpen (N : Set (temperedPi1 O R A V hV)) ∧
      N.Normal ∧ Infinite (temperedPi1 O R A V hV ⧸ N) := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  exact InducedTate.exists_open_normal_infinite_quotient_of_ne_one_gen A A' V hV
    (indObjR (A := A) A' hϖ b₄ b₆ heqR) (indObjR_deck A' hϖ b₄ b₆ heqR V hV)
    (X₀' hϖ b₄ b₆ R heqR A') (deck' hϖ b₄ b₆ R heqR A') (basePoint' hϖ b₄ b₆ R heqR A' V hV)
    (isDeckTorsor' hϖ b₄ b₆ R heqR A' V hV) (ιR A' hϖ b₄ b₆ heqR)
    (fibreMap_ιR_injective A' hϖ b₄ b₆ heqR V hV) hχ

end

end TateRestrict

end TemperedFundamentalGroups
