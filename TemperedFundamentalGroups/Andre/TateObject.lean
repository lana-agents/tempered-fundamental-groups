/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateModel
import TemperedFundamentalGroups.FibreFunctor.Character
import TemperedFundamentalGroups.Tempered.Category

/-!
# The object `X₀` of the `ℤ`-witness (Blueprint §10.3.1, B6)

Let `O ⊆ K` be a valuation ring, `π ∈ O` a nonzero non-unit, `b₄, b₆ ∈ O`, and let `R` be a
reduced `K`-algebra with a point `(x, y)` of `E : y² + xy = x³ + π² b₄ x + π² b₆`, for instance
the coordinate ring of `E` minus finitely many points (`Orbicurve.geomOrbicurveRing`). For a
trivial group `A`:

* `TateObject.unitLevel`: the level `(R, 1)` (`B = R[∅] ⧸ 0 ≅ R`);
* `TateObject.level`: this level with the model `TateModel.model π b₄ b₆ ⊆ ℙ²_O` and
  `j = [x : y : π] : Spec B → 𝒯` (`TateModel.toModel`);
* `TateObject.X₀`: the `ℤ`-covering of the special fibre `C ∪ E'` of the model obtained by gluing
  copies of the line `C` and the conic `E'` alternately at `p` and `q`
  (`TateCovering.Decomp.toCode` for `TateModel.decomp`); it is connected
  (`TateObject.connectedSpace_X₀`);
* `TateObject.deck : Multiplicative ℤ →* Aut X₀`, the deck transformations, which act simply
  transitively on the fibre of the fibre functor (`TateObject.isDeckTorsor`);
* `TateObject.character : temperedPi1 O R A V hV →* Multiplicative ℤ`, the resulting continuous
  character (`TateObject.continuous_character`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

namespace TateObject

noncomputable section

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (R : Type u) [CommRing R] [Algebra K R] (A : Type u) [Group A] [MulSemiringAction A R]

/-! ### The level `(R, 1)` -/

/-- The presentation `R[∅] ⧸ 0` of `R`. -/
def unitIdeal : Ideal (MvPolynomial (Fin 0) R) :=
  RingHom.ker (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom

/-- `R[∅] ⧸ 0 ≅ R`. -/
def unitEquiv : LevelRing R 0 (unitIdeal R) ≃ₐ[R] R :=
  Ideal.quotientKerAlgEquivOfSurjective (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).surjective

variable [Subsingleton A]

/-- **The level `(R, 1)`** of `[Spec R / A]` for a trivial group `A`. -/
def unitLevel : FiniteLevel R A where
  n := 0
  I := unitIdeal R
  etale := Algebra.Etale.of_equiv (unitEquiv R).symm
  finite := Module.Finite.equiv (unitEquiv R).symm.toLinearEquiv
  H := ⊥
  surjective _ := ⟨1, Subgroup.one_mem _, Subsingleton.elim _ _⟩

variable {R A}

lemma unitLevel_H_eq_one (g : (unitLevel R A).H) : g = 1 := by
  have := (Subgroup.mem_bot.1 g.2)
  exact Subtype.ext this

instance : Subsingleton (unitLevel R A).H := ⟨fun g h => by
  rw [unitLevel_H_eq_one g, unitLevel_H_eq_one h]⟩

instance subsingleton_fibre {Ω : Type u} [CommRing Ω] [Algebra R Ω] :
    Subsingleton ((unitLevel R A).B →ₐ[R] Ω) :=
  ⟨fun f g => by
    have : f.comp (unitEquiv R).symm.toAlgHom = g.comp (unitEquiv R).symm.toAlgHom :=
      Subsingleton.elim (α := R →ₐ[R] Ω) _ _
    ext b
    obtain ⟨r, rfl⟩ := (unitEquiv R).symm.surjective b
    exact DFunLike.congr_fun this r⟩

instance [IsReduced R] : IsReduced (unitLevel R A).B :=
  isReduced_of_injective (unitEquiv R).toRingEquiv.toRingHom (unitEquiv R).injective

/-! ### The level with the model -/

variable {O}

/-- The data of the Tate-type equation: `π ∈ O` a nonzero non-unit, `b₄, b₆ ∈ O`, and a point
`(x, y) ∈ R²` of `y² + xy = x³ + π² b₄ x + π² b₆`. -/
structure Data (O : ValuationSubring K) (R : Type u) [CommRing R] [Algebra K R] where
  /-- The uniformizer (any nonzero non-unit). -/
  π : O
  /-- `a₄ = π² b₄`. -/
  b₄ : O
  /-- `a₆ = π² b₆`. -/
  b₆ : O
  π_ne_zero : π ≠ 0
  π_mem : π ∈ IsLocalRing.maximalIdeal O
  /-- The `x`-coordinate. -/
  x : R
  /-- The `y`-coordinate. -/
  y : R
  equation : y ^ 2 + x * y = x ^ 3 + algebraMap K R ((π : K) ^ 2 * b₄) * x +
    algebraMap K R ((π : K) ^ 2 * b₆)

variable (D : Data O R)

lemma Data.equation_B :
    algebraMap R (unitLevel R A).B D.y ^ 2 +
        algebraMap R (unitLevel R A).B D.x * algebraMap R (unitLevel R A).B D.y =
      algebraMap R (unitLevel R A).B D.x ^ 3 +
        levelStructureMap O R A (unitLevel R A) (D.π ^ 2 * D.b₄) *
          algebraMap R (unitLevel R A).B D.x +
        levelStructureMap O R A (unitLevel R A) (D.π ^ 2 * D.b₆) := by
  have := congrArg (algebraMap R (unitLevel R A).B) D.equation
  simp only [map_add, map_mul, map_pow] at this
  simpa [levelStructureMap] using this

lemma Data.isUnit_π :
    IsUnit (levelStructureMap O R A (unitLevel R A) D.π) := by
  have : IsUnit ((D.π : K)) := isUnit_iff_ne_zero.2 (by
    intro h
    exact D.π_ne_zero (Subtype.ext h))
  exact (this.map (algebraMap K R)).map (algebraMap R (unitLevel R A).B)

variable [IsReduced R]

/-- **The level with the model** `𝒯 = V(F) ⊆ ℙ²_O` and `j = [x : y : π]`. -/
def level : Level O R A where
  L := unitLevel R A
  c := TateModel.model D.π D.b₄ D.b₆
  j := TateModel.toModel D.π D.b₄ D.b₆ (levelStructureMap O R A (unitLevel R A)) D.equation_B
    D.isUnit_π
  j_toSpec := TateModel.toModel_toSpec _ _ _ _ _ _
  ρ := 1
  ρ_toSpec _ := Category.id_comp _
  ρ_j g := by
    rw [unitLevel_H_eq_one g, map_one]
    change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    convert Category.id_comp _
    rw [← Spec.map_id]
    rfl

lemma level_ρs (g : (level (A := A) D).L.H) : (level (A := A) D).ρs g = 1 := by
  have h1 : g = 1 := unitLevel_H_eq_one (A := A) g
  rw [h1, map_one]

/-- The decomposition of the special fibre of the model. -/
def decomp : TateCovering.Decomp (level (A := A) D).Z :=
  TateModel.decomp D.π_mem

/-! ### The object `X₀` -/

/-- **The object `X₀`**: the `ℤ`-covering of the special fibre `C ∪ E'` of the model. -/
def X₀ : TempObj O R A where
  Lv := level D
  P := (decomp (A := A) D).toCode _ (level_ρs D)

/-- The special fibre of the model is a line and a conic meeting in exactly two points. -/
lemma decomp_spec :
    (decomp (A := A) D).Cp = {TateModel.pZ D.π D.b₄ D.b₆ D.π_mem} ∧
      (decomp (A := A) D).Cq = {TateModel.qZ D.π D.b₄ D.b₆ D.π_mem} ∧
      TateModel.pZ D.π D.b₄ D.b₆ D.π_mem ≠ TateModel.qZ D.π D.b₄ D.b₆ D.π_mem ∧
      _root_.IsPreconnected (decomp (A := A) D).C ∧ _root_.IsPreconnected (decomp (A := A) D).E :=
  ⟨TateModel.Cp_eq D.π_mem, TateModel.Cq_eq D.π_mem, TateModel.pZ_ne_qZ D.π_mem,
    TateModel.isPreconnected_C D.π_mem, TateModel.isPreconnected_E D.π_mem⟩

/-- **The covering space `X₀` is connected.** -/
lemma connectedSpace_X₀ : ConnectedSpace (X₀ (A := A) D).P.carrier := by
  obtain ⟨hp, hq, -, hC, hE⟩ := decomp_spec (A := A) D
  exact (decomp (A := A) D).connectedSpace_toCode _ (level_ρs D) hC hE
    (by rw [hp]; exact Set.singleton_nonempty _) (by rw [hq]; exact Set.singleton_nonempty _)

/-- The deck transformation of `X₀` by `d ∈ ℤ`, as a morphism. -/
def deckHom (d : Multiplicative ℤ) : X₀ (A := A) D ⟶ X₀ (A := A) D where
  φ := 𝟙 _
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := by rw [TempObj.spec_map_id_f, Category.comp_id, Category.id_comp]
  h := (decomp (A := A) D).deckCode _ (level_ρs D) d
  continuous_h := ((decomp (A := A) D).deckCode _ (level_ρs D) d).continuous
  fst_h _ := rfl
  h_act g x := by
    have h1 : g = 1 := unitLevel_H_eq_one (A := A) g
    rw [h1, map_one, map_one]
    rfl

lemma deckHom_h (d : Multiplicative ℤ) :
    (deckHom (A := A) D d).h = (decomp (A := A) D).deckCode _ (level_ρs D) d :=
  rfl

lemma deckHom_mul (d e : Multiplicative ℤ) :
    deckHom (A := A) D e ≫ deckHom D d = deckHom D (d * e) :=
  TempObj.Hom.ext (Category.id_comp _) (Category.id_comp _) (by
    rw [TempObj.comp_h, deckHom_h, deckHom_h, deckHom_h, map_mul]
    rfl)

lemma deckHom_one : deckHom (A := A) D 1 = 𝟙 _ :=
  TempObj.Hom.ext rfl rfl (by
    rw [deckHom_h, map_one, TempObj.id_h]
    rfl)

/-- **The deck action** `ℤ →* Aut X₀`. -/
def deck : Multiplicative ℤ →* Aut (X₀ (A := A) D) where
  toFun d :=
    { hom := deckHom D d
      inv := deckHom D d⁻¹
      hom_inv_id := by rw [deckHom_mul, inv_mul_cancel, deckHom_one]
      inv_hom_id := by rw [deckHom_mul, mul_inv_cancel, deckHom_one] }
  map_one' := by
    ext1
    exact deckHom_one D
  map_mul' d e := by
    ext1
    rw [Aut.Aut_mul_def, Iso.trans_hom]
    exact (deckHom_mul D d e).symm

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The deck group `ℤ` acts simply transitively on the fibre of `X₀`.** -/
theorem isDeckTorsor :
    FibreAut.IsDeckTorsor (F := tempFibre O R A V hV) (X₀ (A := A) D) (deck D) := by
  intro x y
  induction x using Quotient.inductionOn with | h q => ?_
  induction y using Quotient.inductionOn with | h q' => ?_
  have ht : q.1.1 = q'.1.1 := (subsingleton_fibre (A := A)).elim _ _
  have hfst : q.1.2.1.1 = q'.1.2.1.1 := Subtype.ext (q.2.trans
    ((congrArg (fun t => ((X₀ (A := A) D).Lv.sp V hV t : (X₀ (A := A) D).Lv.c.scheme)) ht).trans
      q'.2.symm))
  obtain ⟨d, hd, hu⟩ := (decomp (A := A) D).existsUnique_deckCode _ (level_ρs D) hfst
  have key : ∀ e : Multiplicative ℤ, FibreAut.deckAct (F := tempFibre O R A V hV)
      (X₀ (A := A) D) (deck D) e (⟦q⟧ : (tempFibre O R A V hV).obj (X₀ (A := A) D)) =
      (⟦(⟨(q.1.1, (decomp (A := A) D).deckCode _ (level_ρs D) e q.1.2), q.2⟩ :
        TempObj.PreFibre Ω V hV (X₀ (A := A) D))⟧ :
          (tempFibre O R A V hV).obj (X₀ (A := A) D)) := fun e => rfl
  refine ⟨d, (key d).trans ?_, fun e he => hu e ?_⟩
  · congr 1
    exact Subtype.ext (Prod.ext ht hd)
  · obtain ⟨g, hg⟩ := Quotient.exact ((key e).symm.trans he)
    have hg1 : g = 1 := Subtype.ext (unitLevel_H_eq_one (A := A) g.1)
    simp only [hg1, one_smul] at hg
    exact congrArg (fun r : TempObj.PreFibre Ω V hV (X₀ (A := A) D) => r.1.2) hg.symm

/-- A point of the fibre of `X₀`, for a geometric point `R → Ω`. -/
def basePoint : (tempFibre O R A V hV).obj (X₀ (A := A) D) :=
  let t : (unitLevel R A).B →ₐ[R] Ω := (Algebra.ofId R Ω).comp (unitEquiv R).toAlgHom
  Quotient.mk _ ⟨(t, ⟨((level (A := A) D).sp V hV t, 0), Set.mem_univ _⟩), rfl⟩

/-- **The character `temperedPi1 → ℤ`** defined by the deck torsor `X₀`. -/
def character : temperedPi1 O R A V hV →* Multiplicative ℤ :=
  FibreAut.deckCharacter (X₀ (A := A) D) (deck D) (basePoint D V hV) (isDeckTorsor D V hV)

/-- The character is continuous. -/
theorem continuous_character : Continuous (character (A := A) D V hV) :=
  FibreAut.continuous_deckCharacter _ _ _ _

end

end TateObject

end TemperedFundamentalGroups
