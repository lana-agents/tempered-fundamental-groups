/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateOrbicurve
import TemperedFundamentalGroups.Andre.Transfer

/-!
# Non-degeneracy of `temperedPi1 [Y/A]` from the `ℤ`-character of `Y` (Blueprint §10.3.2)

Let `A` be a finite group acting `K`-linearly on `R`, and `A'` a trivial group. From the object
`X₀` of the scheme case (`TateObject.X₀`, over the level `(R, 1)`) we build its **induction**
`indObj A A' D` to `[Spec R / A]`, without disjoint unions of models:

* the level is `B = R^A` (coded as a quotient of `R[x_a : a ∈ A]`) with `H ≅ A` acting by
  `(a · f)(b) = a • f(a⁻¹ b)`; so `H⁰ = 1` and `Spec B = ∐_{a ∈ A} Spec R`;
* the model is the Tate model of `X₀`, with the trivial action of `H`, and
  `j = j₀ ∘ Spec(τ)`, where `τ : R → R^A`, `τ(r)(b) = b • r`, is `H`-invariant;
* the covering space is that of `X₀`.

Its fibre is `∐_{a ∈ A} Φ(a^* X₀)`, so the deck group `ℤ` of `X₀` acts on it with finitely many
orbits, and the kernel `N` of `temperedPi1 [Y/A]` acting on this fibre is an **open normal
subgroup**. Evaluation at `1 ∈ A` gives a morphism `X₀ ⟶ Res (indObj A A' D)` in the scheme
category, injective on fibres, so `temperedPi1 Y → temperedPi1 [Y/A] ⧸ N` has kernel inside the
kernel of the `ℤ`-character. Hence (`exists_open_normal_infinite_quotient_of_surjective`,
`TateOrbicurve.nondegenerate_of_character`): **if the character of `Y` is surjective, then
`temperedPi1 [Y/A]` has an open normal subgroup with infinite quotient**; in particular it is not
profinite.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

namespace InducedTate

noncomputable section

/-! ### `R`-algebra maps from `R^ι` to a domain -/

section Pi

variable {ι R Ω : Type*} [Finite ι] [CommRing R] [CommRing Ω] [IsDomain Ω]
  [Algebra R Ω]

/-- An `R`-algebra map `R^ι → Ω` to a domain is the evaluation at any `a` with
`t (e_a) ≠ 0`. -/
lemma algHom_pi_apply [DecidableEq ι] (t : (ι → R) →ₐ[R] Ω) {a : ι} (ha : t (Pi.single a 1) ≠ 0)
    (f : ι → R) : t f = algebraMap R Ω (f a) := by
  have := Fintype.ofFinite ι
  have h0 : ∀ b, b ≠ a → t (Pi.single b 1) = 0 := fun b hb => by
    have : (Pi.single b 1 : ι → R) * Pi.single a 1 = 0 := by
      ext i
      simp only [Pi.mul_apply, Pi.single_apply, Pi.zero_apply]
      split_ifs with h1 h2 <;> simp_all
    have h := congrArg t this
    rw [map_mul, map_zero] at h
    exact (mul_eq_zero.1 h).resolve_right ha
  have h1 : t (Pi.single a 1) = 1 := by
    have : (Pi.single a 1 : ι → R) * Pi.single a 1 = Pi.single a 1 := by
      ext i
      simp only [Pi.mul_apply, Pi.single_apply]
      split_ifs <;> simp
    have h := congrArg t this
    rw [map_mul] at h
    exact mul_left_cancel₀ ha (h.trans (mul_one _).symm)
  have hf : f = ∑ b, f b • (Pi.single b 1 : ι → R) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hf]
  rw [map_sum, Finset.sum_eq_single a]
  · rw [map_smul, h1, Algebra.smul_def, mul_one]
  · intro b _ hb
    rw [map_smul, h0 b hb, smul_zero]
  · simp

variable (ι R Ω) in
lemma finite_algHom_pi : Finite ((ι → R) →ₐ[R] Ω) := by
  classical
  have := Fintype.ofFinite ι
  have hex : ∀ t : (ι → R) →ₐ[R] Ω, ∃ a, t (Pi.single a 1) ≠ 0 := by
    intro t
    by_contra! h
    have : (∑ a, (Pi.single a 1 : ι → R)) = 1 := by
      ext i
      simp [Pi.single_apply]
    have h' := congrArg t this
    rw [map_sum, map_one, Finset.sum_eq_zero (fun a _ => h a)] at h'
    exact zero_ne_one h'
  choose a ha using hex
  refine Finite.of_injective a fun t t' htt' => AlgHom.ext fun f => ?_
  rw [algHom_pi_apply t (ha t), algHom_pi_apply t' (ha t'), htt']

end Pi

/-! ### The induced level `(R^A, A)` -/

section Ind

variable {K : Type u} [Field K] {O : ValuationSubring K} (R : Type u) [CommRing R] [Algebra K R]
  (A : Type u) [Group A] [Fintype A] [DecidableEq A] [MulSemiringAction A R]

/-- The generators `x_a ↦ e_a` of `R^A`. -/
def indMap : MvPolynomial (Fin (Fintype.card A)) R →ₐ[R] (A → R) :=
  MvPolynomial.aeval fun i => Pi.single ((Fintype.equivFin A).symm i) 1

omit [Group A] [MulSemiringAction A R] in
lemma indMap_surjective : Function.Surjective (indMap R A) := by
  intro f
  refine ⟨∑ i, MvPolynomial.C (f ((Fintype.equivFin A).symm i)) * MvPolynomial.X i, ?_⟩
  simp only [indMap, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  refine ((Fintype.equivFin A).symm.sum_comp
    (fun a => algebraMap R (A → R) (f a) * Pi.single a 1)).trans ?_
  ext b
  simp [Finset.sum_apply, Pi.single_apply]

/-- The ideal of relations of `R^A`. -/
def indIdeal : Ideal (MvPolynomial (Fin (Fintype.card A)) R) := RingHom.ker (indMap R A)

/-- `R[x_a] ⧸ I ≅ R^A`. -/
def indEquiv : LevelRing R _ (indIdeal R A) ≃ₐ[R] (A → R) :=
  Ideal.quotientKerAlgEquivOfSurjective (indMap_surjective R A)

/-- The action of `a ∈ A` on `R^A`: `(a · f)(b) = a • f(a⁻¹ b)`. -/
def twistAct (a : A) : (A → R) ≃+* (A → R) where
  toFun f b := a • f (a⁻¹ * b)
  invFun f b := a⁻¹ • f (a * b)
  left_inv f := by
    ext b
    simp [smul_smul]
  right_inv f := by
    ext b
    simp [smul_smul]
  map_mul' f g := by
    ext b
    simp [smul_mul']
  map_add' f g := by
    ext b
    simp [smul_add]

omit [Fintype A] [DecidableEq A] in
lemma twistAct_apply (a : A) (f : A → R) (b : A) : twistAct R A a f b = a • f (a⁻¹ * b) := rfl

/-- The semilinear automorphism of the coded `R^A` given by `a`. -/
def indAut (a : A) : SemilinearAut R A (LevelRing R _ (indIdeal R A)) where
  a := a
  σ := (indEquiv R A).toRingEquiv.trans ((twistAct R A a).trans (indEquiv R A).symm.toRingEquiv)
  map_algebraMap r := by
    change (indEquiv R A).symm (twistAct R A a (indEquiv R A (algebraMap R _ r))) = _
    rw [AlgEquiv.commutes]
    have : twistAct R A a (algebraMap R (A → R) r) = algebraMap R (A → R) (a • r) := rfl
    rw [this, AlgEquiv.commutes]

lemma indAut_σ (a : A) (x : LevelRing R _ (indIdeal R A)) :
    (indAut R A a).σ x = (indEquiv R A).symm (twistAct R A a (indEquiv R A x)) := rfl

/-- The lift `A →* G_B` of the action of `A` to `R^A`. -/
def indHom : A →* SemilinearAut R A (LevelRing R _ (indIdeal R A)) where
  toFun := indAut R A
  map_one' := SemilinearAut.ext rfl (by
    ext x
    change (indEquiv R A).symm (twistAct R A 1 (indEquiv R A x)) = x
    have : twistAct R A 1 (indEquiv R A x) = indEquiv R A x := by
      ext b
      simp [twistAct_apply]
    rw [this, AlgEquiv.symm_apply_apply])
  map_mul' a b := SemilinearAut.ext rfl (by
    ext x
    change (indAut R A (a * b)).σ x = (indAut R A a).σ ((indAut R A b).σ x)
    rw [indAut_σ, indAut_σ, indAut_σ, AlgEquiv.apply_symm_apply]
    congr 1
    ext c
    simp [twistAct_apply, mul_smul, mul_assoc])

/-- **The induced level** `(R^A, A)` of `[Spec R / A]`. -/
def indLevel : FiniteLevel R A where
  n := Fintype.card A
  I := indIdeal R A
  etale := Algebra.Etale.of_equiv (indEquiv R A).symm
  finite := Module.Finite.equiv (indEquiv R A).symm.toLinearEquiv
  H := (indHom R A).range
  surjective a := ⟨indHom R A a, ⟨a, rfl⟩, rfl⟩

/-- `τ : R → R^A`, `τ(r)(b) = b • r`. -/
def twist : R →+* (A → R) := RingHom.pi fun b => MulSemiringAction.toRingHom A R b

variable (A' : Type u) [Group A'] [Subsingleton A'] [MulSemiringAction A' R]

/-- `τ` on the coded rings. -/
def gHom : (TateObject.unitLevel R A').B →+* (indLevel R A).B :=
  (indEquiv R A).symm.toRingHom.comp ((twist R A).comp (TateObject.unitEquiv R).toRingHom)

/-- The evaluation `R^A → R` at `1`, on the coded rings. -/
def evalOne : (indLevel R A).B →ₐ[R] (TateObject.unitLevel R A').B :=
  (TateObject.unitEquiv R).symm.toAlgHom.comp
    ((Pi.evalAlgHom R (fun _ : A => R) 1).comp (indEquiv R A).toAlgHom)

lemma evalOne_comp_gHom :
    (evalOne R A A' : (indLevel R A).B →+* (TateObject.unitLevel R A').B).comp (gHom R A A') =
      RingHom.id _ := by
  refine RingHom.ext fun y => ?_
  change (TateObject.unitEquiv R).symm ((indEquiv R A ((indEquiv R A).symm
    (twist R A (TateObject.unitEquiv R y)))) 1) = y
  rw [AlgEquiv.apply_symm_apply]
  change (TateObject.unitEquiv R).symm ((1 : A) • TateObject.unitEquiv R y) = y
  rw [one_smul, AlgEquiv.symm_apply_apply]

/-- The image of `τ` is `H`-invariant. -/
lemma σ_gHom (g : (indLevel R A).H) (y : (TateObject.unitLevel R A').B) :
    g.1.σ (gHom R A A' y) = gHom R A A' y := by
  obtain ⟨x, hx⟩ := g
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
  change (indEquiv R A).symm (twistAct R A a ((indEquiv R A) ((indEquiv R A).symm
    (twist R A (TateObject.unitEquiv R y))))) =
      (indEquiv R A).symm (twist R A (TateObject.unitEquiv R y))
  have : twistAct R A a (twist R A (TateObject.unitEquiv R y)) =
      twist R A (TateObject.unitEquiv R y) := by
    ext b
    simp [twistAct_apply, twist, smul_smul]
  rw [AlgEquiv.apply_symm_apply, this]

lemma σ_symm_comp_gHom (g : (indLevel R A).H) :
    ((g.1.σ.symm : (indLevel R A).B →+* (indLevel R A).B)).comp (gHom R A A') = gHom R A A' := by
  refine RingHom.ext fun y => ?_
  change g.1.σ.symm (gHom R A A' y) = gHom R A A' y
  rw [RingEquiv.symm_apply_eq, σ_gHom]

variable [SMulCommClass A K R]

lemma gHom_comp_levelStructureMap :
    (gHom R A A').comp (levelStructureMap O R A' (TateObject.unitLevel R A')) =
      levelStructureMap O R A (indLevel R A) := by
  refine RingHom.ext fun o => ?_
  have h : twist R A (algebraMap K R o) = algebraMap R (A → R) (algebraMap K R o) := by
    ext b
    exact smul_algebraMap b o
  change (indEquiv R A).symm (twist R A (TateObject.unitEquiv R
    (algebraMap R _ (algebraMap K R o)))) = algebraMap R _ (algebraMap K R o)
  rw [AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply, h, AlgEquiv.commutes]

/-! ### The induced object -/

variable {R} [IsReduced R] (D : TateObject.Data O R)

/-- **The induced level with the Tate model**: `j = j₀ ∘ Spec τ`, trivial action on the model. -/
def indLv : Level O R A where
  L := indLevel R A
  c := (TateObject.level (A := A') D).c
  j := Spec.map (CommRingCat.ofHom (gHom R A A')) ≫ (TateObject.level (A := A') D).j
  j_toSpec := by
    refine (Category.assoc _ _ _).trans ((Spec.map (CommRingCat.ofHom (gHom R A A')) ≫=
      (TateObject.level (A := A') D).j_toSpec).trans ((Spec.map_comp _ _).symm.trans ?_))
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (gHom_comp_levelStructureMap R A A')
  ρ := 1
  ρ_toSpec _ := Category.id_comp _
  ρ_j g := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, σ_symm_comp_gHom]
    exact (Category.comp_id _).symm

lemma indLv_ρs (g : (indLv A A' D).L.H) : (indLv A A' D).ρs g = 1 := by
  have : (indLv A A' D).ρs g = (indLv A A' D).ρs 1 := rfl
  rw [this, map_one]

/-- **The induced object** `Ind X₀` of `[Spec R / A]`. -/
def indObj : TempObj O R A where
  Lv := indLv A A' D
  P := (TateObject.decomp (A := A') D).toCode _ (indLv_ρs A A' D)

/-- The deck transformations of `Ind X₀`. -/
def indDeck (d : Multiplicative ℤ) : indObj A A' D ⟶ indObj A A' D where
  φ := 𝟙 _
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := by rw [TempObj.spec_map_id_f, Category.comp_id, Category.id_comp]
  h := (TateObject.decomp (A := A') D).deckCode _ (indLv_ρs A A' D) d
  continuous_h := ((TateObject.decomp (A := A') D).deckCode _ (indLv_ρs A A' D) d).continuous
  fst_h _ := rfl
  h_act _ _ := rfl

/-- The map of levels `Spec R → Spec R^A` onto the component `1 ∈ A`. -/
def ιLevel : TateObject.unitLevel R A' ⟶ (indLevel R A).res A' where
  f := evalOne R A A'
  r := 1
  r_a _ := Subsingleton.elim _ _
  f_σ g y := by
    rw [TateObject.unitLevel_H_eq_one g]
    rfl

omit [IsReduced R] in
lemma evalOne_gHom :
    Spec.map (CommRingCat.ofHom
      (evalOne R A A' : (indLevel R A).B →+* (TateObject.unitLevel R A').B)) ≫
      Spec.map (CommRingCat.ofHom (gHom R A A')) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, evalOne_comp_gHom, CommRingCat.ofHom_id,
    Spec.map_id]

lemma j_eq : (TateObject.level (A := A') D).j =
    Spec.map (CommRingCat.ofHom
      (evalOne R A A' : (indLevel R A).B →+* (TateObject.unitLevel R A').B)) ≫
      (indLv A A' D).j :=
  ((Category.id_comp _).symm.trans
    (congrArg (· ≫ (TateObject.level (A := A') D).j) (evalOne_gHom A A').symm)).trans
    (Category.assoc _ _ _)

/-- **The inclusion `X₀ ⟶ Res (Ind X₀)`** of the component `1 ∈ A`. -/
def ι : TateObject.X₀ (A := A') D ⟶ (indObj A A' D).res A' where
  φ := ιLevel A A'
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := (Category.comp_id _).trans (j_eq A A' D)
  h := fun x => x
  continuous_h := continuous_id
  fst_h _ := rfl
  h_act _ _ := rfl

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- `X₀ ⟶ Res (Ind X₀)` is injective on fibres. -/
lemma fibreMap_ι_injective :
    Function.Injective ((tempFibre O R A' V hV).map (ι A A' D)) := by
  intro x y hxy
  induction x using Quotient.inductionOn with | h q => ?_
  induction y using Quotient.inductionOn with | h q' => ?_
  have hxy' : (⟦TempObj.preMap V hV (ι A A' D) q⟧ : TempObj.Fibre Ω V hV ((indObj A A' D).res A')) =
      ⟦TempObj.preMap V hV (ι A A' D) q'⟧ := hxy
  obtain ⟨g, hg⟩ := Quotient.exact hxy'
  have h2 : q'.1.2 = q.1.2 := congrArg (fun r => r.1.2) hg
  have h1 : q'.1.1 = q.1.1 := (TateObject.subsingleton_fibre (A := A')).elim _ _
  exact congrArg _ (Subtype.ext (Prod.ext h1 h2)).symm

instance : Finite ((indObj A A' D).Lv.L.B →ₐ[R] Ω) := by
  have := finite_algHom_pi A R Ω
  exact Finite.of_injective (fun t => t.comp (indEquiv R A).symm.toAlgHom) fun t t' h => by
    ext y
    have := DFunLike.congr_fun h (indEquiv R A y)
    exact (congrArg t ((indEquiv R A).symm_apply_apply y)).symm.trans
      (this.trans (congrArg t' ((indEquiv R A).symm_apply_apply y)))

end Ind

variable {K : Type u} [Field K] {O : ValuationSubring K} {R : Type u} [CommRing R] [Algebra K R]
  [IsReduced R] (A : Type u) [Group A] [Finite A] [MulSemiringAction A R] [SMulCommClass A K R]
  (A' : Type u) [Group A'] [Subsingleton A'] [MulSemiringAction A' R] (D : TateObject.Data O R)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Non-degeneracy of `temperedPi1 [Y/A]`.** If the character `temperedPi1 Y → ℤ` of `X₀` is
surjective, then `temperedPi1 [Spec R / A]` has an open normal subgroup with infinite quotient:
the kernel of its action on the fibre of `Ind X₀`. -/
theorem exists_open_normal_infinite_quotient_of_surjective
    (hχ : Function.Surjective (TateObject.character (A := A') D V hV)) :
    ∃ N : Subgroup (temperedPi1 O R A V hV), IsOpen (N : Set (temperedPi1 O R A V hV)) ∧
      N.Normal ∧ Infinite (temperedPi1 O R A V hV ⧸ N) := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  let Z := indObj A A' D
  let F := tempFibre O R A V hV
  let S : Set (Σ c, F.obj c) :=
    Set.range fun t : {t : Z.Lv.L.B →ₐ[R] Ω // ∃ q : TempObj.PreFibre Ω V hV Z, q.1.1 = t} =>
      (⟨Z, ⟦t.2.choose⟧⟩ : Σ c, F.obj c)
  have hS : S.Finite := Set.finite_range _
  let M := FibreAut.stabilizer F hS.toFinset
  -- `M` acts trivially on the whole fibre of `Z`.
  have hfix : ∀ γ ∈ M, ∀ z : F.obj Z, γ.app Z z = z := by
    intro γ hγ z
    induction z using Quotient.inductionOn with | h q => ?_
    have hex : ∃ q' : TempObj.PreFibre Ω V hV Z, q'.1.1 = q.1.1 := ⟨q, rfl⟩
    have h₀ : hex.choose.1.1 = q.1.1 := hex.choose_spec
    have hbase : hex.choose.1.2.1.1 = q.1.2.1.1 := Subtype.ext (hex.choose.2.trans
      ((congrArg (fun t => (Z.Lv.sp V hV t : Z.Lv.c.scheme)) h₀).trans q.2.symm))
    obtain ⟨d, hd, -⟩ :=
      (TateObject.decomp (A := A') D).existsUnique_deckCode _ (indLv_ρs A A' D) hbase
    have hmem : (⟨Z, ⟦hex.choose⟧⟩ : Σ c, F.obj c) ∈ hS.toFinset :=
      (Set.Finite.mem_toFinset hS).2 ⟨⟨q.1.1, hex⟩, rfl⟩
    have hq₀ : γ.app Z ⟦hex.choose⟧ = ⟦hex.choose⟧ := hγ _ hmem
    have hdeck : F.map (indDeck A A' D d) ⟦hex.choose⟧ = ⟦q⟧ := by
      change (⟦TempObj.preMap V hV (indDeck A A' D d) hex.choose⟧ : F.obj Z) = ⟦q⟧
      exact congrArg _ (Subtype.ext (Prod.ext ((AlgHom.comp_id _).trans h₀) hd))
    rw [← hdeck, FibreAut.app_naturality, hq₀]
  have hnorm : M.Normal := ⟨fun γ hγ g p hp => by
    obtain ⟨t, rfl⟩ := (Set.Finite.mem_toFinset hS).1 hp
    change (g * γ * g⁻¹).app Z _ = _
    rw [FibreAut.mul_app, FibreAut.mul_app, hfix γ hγ, FibreAut.app_inv_app]⟩
  -- An element of `temperedPi1 Y` whose image lies in `M` has trivial character.
  let x₀ := TateObject.basePoint (A := A') D V hV
  let e := resFibreIso O R A A' V hV
  have key : ∀ τ, restrictHom O R A A' V hV τ ∈ M → TateObject.character D V hV τ = 1 := by
    intro τ hτ
    let y := (tempFibre O R A' V hV).map (ι A A' D) x₀
    have h1 : e.hom.app Z (τ.app ((resFunctor O R A A').obj Z) y) = e.hom.app Z y := by
      have := hfix _ hτ (e.hom.app Z y)
      rwa [restrictHom, FibreAut.restrict_app, Iso.hom_inv_id_app_apply] at this
    have h2 : τ.app ((resFunctor O R A A').obj Z) y = y := by
      have := congrArg (e.inv.app Z) h1
      rwa [Iso.hom_inv_id_app_apply, Iso.hom_inv_id_app_apply] at this
    have h3 : (tempFibre O R A' V hV).map (ι A A' D) (τ.app _ x₀) = y :=
      (FibreAut.app_naturality τ (ι A A' D) x₀).symm.trans h2
    have h4 := fibreMap_ι_injective A A' D V hV h3
    exact FibreAut.deckCharacterFun_eq (TateObject.X₀ (A := A') D) (TateObject.deck D)
      (TateObject.basePoint D V hV) (TateObject.isDeckTorsor D V hV)
      (by rw [FibreAut.deckAct_one]; exact h4.symm)
  choose σ hσ using hχ
  refine ⟨M, FibreAut.isOpen_stabilizer _ _, hnorm, Infinite.of_injective
    (fun n : Multiplicative ℤ =>
      (QuotientGroup.mk (restrictHom O R A A' V hV (σ n)) : temperedPi1 O R A V hV ⧸ M))
    fun n m hnm => ?_⟩
  rw [QuotientGroup.eq, ← map_inv, ← map_mul] at hnm
  have h := key _ hnm
  rw [map_mul, map_inv, hσ, hσ] at h
  exact inv_mul_eq_one.1 h

end

end InducedTate

namespace TateOrbicurve

open Orbicurve

variable {K : Type u} [Field K] {O : ValuationSubring K} {W : WeierstrassCurve K} [DecidableEq K]
  (A : Type u) [Group A] [Finite A] (A' : Type u) [Group A'] [Subsingleton A']
  {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}
  [MulSemiringAction A (geomOrbicurveRing W ℓ M)] [SMulCommClass A K (geomOrbicurveRing W ℓ M)]
  [MulSemiringAction A' (geomOrbicurveRing W ℓ M)]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra (geomOrbicurveRing W ℓ M) Ω]
  [IsScalarTower K (geomOrbicurveRing W ℓ M) Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Non-degeneracy for IUT's orbicurve `[Y/A]`** (Blueprint §10.3.2, T4): for
`Y = E_q ∖ (E[ℓ] + M)` and a finite group `A` acting `K`-linearly on `Y`, if the continuous
character `temperedPi1 Y → ℤ` of the Tate curve (`TateOrbicurve.character`) is surjective, then
`temperedPi1 [Y/A]` has an open normal subgroup with infinite (discrete) quotient; in particular it
is not profinite. -/
theorem nondegenerate_of_character {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal O)
    (hsurj : Function.Surjective (character A' ℓ M V hV hW hπ hπm)) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) := by
  exact InducedTate.exists_open_normal_infinite_quotient_of_surjective A A'
    (data hW hπ hπm ℓ M) V hV hsurj

end TateOrbicurve

end TemperedFundamentalGroups
