/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.StageGroup

/-!
# Level classes and the action of stage groups on them (Blueprint §11.3, G6)

For a tempered covering `X` over a level `L = (B, H)` a point of the fibre `Φ X` is a class
`[t, p]` of a geometric point `t ∈ F_L = Hom_R(B, Ω)` and a point `p` of the covering, modulo the
diagonal action of `H⁰ = ker (H → A)`. So the **level class** `[t] ∈ F_L / H⁰` of a point is well
defined (`levelCls`), natural along morphisms (`levelCls_fibreMap`, the map of level classes
`levelMap m : [t] ↦ [t ∘ φ.f]`, well defined by `fibreAct_comp`).

* `stageCls : stageGroup Φ X →* Perm (LevelCls X)` (if `levelCls` is surjective): the action of
  the stage group on level classes (`stageCls_levelCls`), `stageOf a ↦ levelMap a.hom`
  (`stageCls_stageOf`);
* `stageCls_transition`: compatibility with the transition maps of pointed morphisms
  (`[t] ↦ [t ∘ φ.f]`).

This generalizes `stageLevel` (scheme case, trivial `H`, `F_L / H⁰ = F_L`) to orbifolds.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace TempObj

variable (Ω) in
/-- `H⁰`-equivalence of geometric points of a level. -/
def levelSetoid (X : TempObj O R A) : Setoid (X.Lv.L.B →ₐ[R] Ω) where
  r t t' := ∃ k : X.Lv.L.H0, FiniteLevel.fibreAct Ω X.Lv.L k t = t'
  iseqv :=
    { refl t := ⟨1, FiniteLevel.fibreAct_one _ _ _⟩
      symm := fun ⟨k, hk⟩ ↦ ⟨k⁻¹, by
        rw [← hk, ← FiniteLevel.fibreAct_mul, inv_mul_cancel, FiniteLevel.fibreAct_one]⟩
      trans := fun ⟨k, hk⟩ ⟨k', hk'⟩ ↦ ⟨k' * k, by rw [FiniteLevel.fibreAct_mul, hk, hk']⟩ }

variable (Ω) in
/-- **The level classes** `F_L / H⁰` of a covering `X` over the level `L`. -/
abbrev LevelCls (X : TempObj O R A) : Type u := Quotient (levelSetoid Ω X)

/-- **The level class** `[t, p] ↦ [t]` of a point of the fibre. -/
def levelCls (X : TempObj O R A) : Fibre Ω V hV X → LevelCls Ω X :=
  Quotient.lift (fun q ↦ (Quotient.mk _ q.1.1 : LevelCls Ω X)) fun q q' ⟨g, hg⟩ ↦ by
    refine Quotient.sound ⟨g⁻¹, ?_⟩
    rw [← hg]
    change FiniteLevel.fibreAct Ω X.Lv.L g⁻¹ (FiniteLevel.fibreAct Ω X.Lv.L g q'.1.1) = q'.1.1
    rw [← FiniteLevel.fibreAct_mul, inv_mul_cancel, FiniteLevel.fibreAct_one]

lemma levelCls_mk (X : TempObj O R A) (q : PreFibre Ω V hV X) :
    levelCls V hV X (Quotient.mk _ q) = Quotient.mk _ q.1.1 := rfl

/-- **The map of level classes** `[t] ↦ [t ∘ φ.f]` of a morphism. -/
def levelMap {X Y : TempObj O R A} (m : X ⟶ Y) : LevelCls Ω X → LevelCls Ω Y :=
  Quotient.map (fun t ↦ t.comp m.φ.f) fun t t' ⟨k, hk⟩ ↦
    ⟨⟨m.φ.r k, FiniteLevel.r_mem_H0 m.φ k.2⟩, by
      rw [← hk, FiniteLevel.fibreAct_comp]⟩

lemma levelMap_mk {X Y : TempObj O R A} (m : X ⟶ Y) (t : X.Lv.L.B →ₐ[R] Ω) :
    levelMap m (Quotient.mk _ t : LevelCls Ω X) = Quotient.mk _ (t.comp m.φ.f) := rfl

lemma levelMap_id (X : TempObj O R A) (c : LevelCls Ω X) : levelMap (𝟙 X) c = c := by
  induction c using Quotient.inductionOn
  rfl

lemma levelMap_comp {X Y Z : TempObj O R A} (m : X ⟶ Y) (n : Y ⟶ Z) (c : LevelCls Ω X) :
    levelMap (m ≫ n) c = levelMap n (levelMap m c) := by
  induction c using Quotient.inductionOn
  rfl

/-- The level class is natural: `levelCls (m x) = levelMap m (levelCls x)`. -/
lemma levelCls_fibreMap {X Y : TempObj O R A} (m : X ⟶ Y) (x : Fibre Ω V hV X) :
    levelCls V hV Y (fibreMap V hV m x) = levelMap m (levelCls V hV X x) := by
  induction x using Quotient.inductionOn
  rfl

end TempObj

section Stage

variable {X : TempObj O R A}

/-- Stage group elements act on level classes. -/
lemma levelCls_stage_eq (σ : stageGroup (tempFibre O R A V hV) X) {x y : Fibre Ω V hV X}
    (h : levelCls V hV X x = levelCls V hV X y) :
    levelCls V hV X (σ.1 x) = levelCls V hV X (σ.1 y) := by
  obtain ⟨a, rfl⟩ := eq_stageOf σ
  change levelCls V hV X (fibreMap V hV a.hom x) = levelCls V hV X (fibreMap V hV a.hom y)
  rw [levelCls_fibreMap, levelCls_fibreMap, h]

variable (hsurj : Function.Surjective (levelCls V hV X))

/-- The action of a stage group element on level classes (as a function). -/
def stageClsFun (σ : stageGroup (tempFibre O R A V hV) X) (c : LevelCls Ω X) : LevelCls Ω X :=
  levelCls V hV X (σ.1 (hsurj c).choose)

lemma stageClsFun_levelCls (σ : stageGroup (tempFibre O R A V hV) X) (x : Fibre Ω V hV X) :
    stageClsFun V hV hsurj σ (levelCls V hV X x) = levelCls V hV X (σ.1 x) :=
  levelCls_stage_eq V hV σ (hsurj _).choose_spec

/-- **The action of the stage group on the level classes** `F_L / H⁰`. -/
def stageCls : stageGroup (tempFibre O R A V hV) X →* Equiv.Perm (LevelCls Ω X) where
  toFun σ :=
    { toFun := stageClsFun V hV hsurj σ
      invFun := stageClsFun V hV hsurj σ⁻¹
      left_inv := fun c ↦ by
        obtain ⟨x, rfl⟩ := hsurj c
        rw [stageClsFun_levelCls, stageClsFun_levelCls, ← Equiv.Perm.mul_apply,
          ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      right_inv := fun c ↦ by
        obtain ⟨x, rfl⟩ := hsurj c
        rw [stageClsFun_levelCls, stageClsFun_levelCls, ← Equiv.Perm.mul_apply,
          ← Subgroup.coe_mul, mul_inv_cancel]
        rfl }
  map_one' := by
    refine Equiv.ext fun c ↦ ?_
    obtain ⟨x, rfl⟩ := hsurj c
    exact stageClsFun_levelCls V hV hsurj 1 x
  map_mul' σ τ := by
    refine Equiv.ext fun c ↦ ?_
    obtain ⟨x, rfl⟩ := hsurj c
    change stageClsFun V hV hsurj (σ * τ) _ =
      stageClsFun V hV hsurj σ (stageClsFun V hV hsurj τ _)
    rw [stageClsFun_levelCls, stageClsFun_levelCls, stageClsFun_levelCls]
    rfl

lemma stageCls_levelCls (σ : stageGroup (tempFibre O R A V hV) X) (x : Fibre Ω V hV X) :
    stageCls V hV hsurj σ (levelCls V hV X x) = levelCls V hV X (σ.1 x) :=
  stageClsFun_levelCls V hV hsurj σ x

/-- The stage group element of an automorphism acts on level classes by `[t] ↦ [t ∘ φ.f]`. -/
lemma stageCls_stageOf (a : X ≅ X) (c : LevelCls Ω X) :
    stageCls V hV hsurj (stageOf a) c = levelMap a.hom c := by
  obtain ⟨x, rfl⟩ := hsurj c
  rw [stageCls_levelCls]
  exact levelCls_fibreMap V hV a.hom x

lemma stageCls_stageOf_mk (a : X ≅ X) (t : X.Lv.L.B →ₐ[R] Ω) :
    stageCls V hV hsurj (stageOf a) (Quotient.mk _ t) = Quotient.mk _ (t.comp a.hom.φ.f) :=
  stageCls_stageOf V hV hsurj a _

end Stage

section Functor

variable {X Y : TempObj O R A} (hX : Function.Surjective (levelCls V hV X))
  (hY : Function.Surjective (levelCls V hV Y))

/-- **Transition maps are compatible with level classes**: if `τ ∘ F = F ∘ σ` on fibres, then
`τ` acts on `[t ∘ φ.f]` as `σ` acts on `[t]`, followed by `levelMap F`. -/
lemma stageCls_comm (F : X ⟶ Y) (σ : stageGroup (tempFibre O R A V hV) X)
    (τ : stageGroup (tempFibre O R A V hV) Y)
    (h : ∀ x, τ.1 (fibreMap V hV F x) = fibreMap V hV F (σ.1 x)) (c : LevelCls Ω X) :
    stageCls V hV hY τ (levelMap F c) = levelMap F (stageCls V hV hX σ c) := by
  obtain ⟨x, rfl⟩ := hX c
  rw [← levelCls_fibreMap, stageCls_levelCls, h, levelCls_fibreMap, stageCls_levelCls]

/-- **The transition map of a pointed morphism** (with underlying morphism `F`) on level
classes. -/
lemma stageCls_transition {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)
    {p q : PtGal (tempFibre O R A V hV) 𝒢}
    (hp : Function.Surjective (levelCls V hV p.G)) (hq : Function.Surjective (levelCls V hV q.G))
    (f : p ⟶ q) (F : p.G ⟶ q.G) (hF : fibreMap V hV F = f.1)
    (σ : stageGroup (tempFibre O R A V hV) p.G) (c : LevelCls Ω p.G) :
    stageCls V hV hq (transition hgal hrig f σ) (levelMap F c) =
      levelMap F (stageCls V hV hp σ c) :=
  stageCls_comm V hV hp hq F σ _ (fun x ↦ by
    have := transition_comm hgal hrig f σ x
    rw [← hF] at this
    exact this) c

end Functor

end

end TemperedFundamentalGroups
