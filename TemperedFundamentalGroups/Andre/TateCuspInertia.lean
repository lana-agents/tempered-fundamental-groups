/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.CuspInertia
import TemperedFundamentalGroups.Andre.TateObjectIsogeny

/-!
# Cusp inertia of the levels lies in `Π^tp_Ÿ` ([EtTh], §1)

The `ℤ`-covering `Y → X` of the special fibre of a Tate model (`TateObject.X₀`, deck character
`TateObject.character`) has the level `R` itself, so every Galois element of a base point `V`
fixes the base point of its fibre: **Galois elements lie in `Π^tp_Y = ker χ`**
(`character_galoisToTempered`), in particular the tempered inertia groups `I^tp_W` of places
`W ≥ V` (`inertiaTempered_le_ker_character`). For `Ÿ → X` through a finite étale level
`R → R'` with Tate data `D'` (`TateObjectIsogeny`):

* `galoisToTempered_mem_piYddot`: Galois elements over `R'` give elements of `Π^tp_Ÿ`;
* **`inertiaTempered_le_comap_piYddot`**: the tempered inertia group `I^tp_W ≤ Π^tp_{X'}` of a
  place `W` of `X' = Spec R'` maps into `Π^tp_Ÿ`;
* **towers** `R → R' → R''` (e.g. `R''` the level `Ÿ'_N` of [EtTh] §1, a finite étale cover of
  `X'`): **`inertiaTempered_le_comap_piYddotAt`** — `I^tp_W ≤ Π^tp_{X''}` of a place `W` of
  `X''` (e.g. a cusp of `Ÿ'_N`) maps into `Π^tp_Ÿ ∩ Π^tp_{X''}` (`piYddotAt`), hence into `Π^tp_Ÿ`:
  the cusps of `Ÿ` over the cusps of `Ÿ'_N` have the full inertia of `Ÿ'_N` (the covering
  `Ÿ → Ÿ'_N` is unramified at the cusps). No domination hypothesis (`Π^tp_Ÿ ≤ Π^tp_{X''}`) is
  needed for this inclusion; under it, `piYddotAt = piYddot` (`piYddotAt_eq_iff`).
* the same for the presentation `Π^tp_Ÿ = Π^tp_Y ∩ Π^tp_{X₁}` used in `iut` (`Y` the `ℤ`-covering
  of `X` itself, `X₁ → X` a finite étale level): `inertiaTempered_le_comap_ker_inf_range`.

This is requirement T2 of the étale theta track (`MR14-plan.md`, run 10).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

/-! ### Galois elements lie in `Π^tp_Y` -/

section CharacterGalois

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  {V : ValuationSubring Ω} (hV : V.comap (algebraMap K Ω) = O) (T : TateObject.Data O R)

/-- **Galois elements lie in `Π^tp_Y`**: they act trivially on the fibre of `Y` (its level is `R`
itself). (As `TateObjectDouble.character_galois`, for any Tate data.) -/
theorem character_galoisToTempered (σ : decompositionGroup R V) :
    TateObject.character (A := A) T V hV (galoisToTempered O R A hV σ) = 1 := by
  refine FibreAut.deckCharacterFun_eq (TateObject.X₀ (A := A) T) (TateObject.deck T)
    (TateObject.basePoint T V hV) (TateObject.isDeckTorsor T V hV) ?_
  rw [FibreAut.deckAct_one]
  change (TateObject.basePoint T V hV : (tempFibre O R A V hV).obj (TateObject.X₀ (A := A) T)) =
    ⟦TempObj.preGalois hV (TateObject.X₀ (A := A) T) σ σ.2 _⟧
  exact congrArg (Quotient.mk _) (Subtype.ext (Prod.ext
    ((TateObject.subsingleton_fibre (A := A)).elim _ _) rfl))

/-- **Tempered inertia lies in `Π^tp_Y`.** -/
theorem inertiaTempered_le_ker_character {W : ValuationSubring Ω} (hVW : V ≤ W) :
    inertiaTempered O A hV hVW ≤ (TateObject.character (A := A) T V hV).ker := by
  rintro _ ⟨σ, rfl⟩
  exact character_galoisToTempered hV T _

end CharacterGalois

/-! ### `Π^tp_Ÿ = Π^tp_Y ∩ Π^tp_{X₁}` -/

section KerInfRange

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {R₁ : Type u} [CommRing R₁] [Algebra K R₁] [Algebra R R₁] [IsScalarTower K R R₁]
  {A₁ : Type u} [Group A₁] [MulSemiringAction A₁ R₁] (μ₁ : OrbMap R A R₁ A₁)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R₁ Ω] [IsScalarTower K R₁ Ω] [IsScalarTower R R₁ Ω]
  {V : ValuationSubring Ω} (hV : V.comap (algebraMap K Ω) = O) (T : TateObject.Data O R)

/-- **The tempered inertia group of a place of `X₁` lies in `Π^tp_Y ∩ Π^tp_{X₁}`** (the form of
`Π^tp_Ÿ` used in `iut`, `Y → X` the `ℤ`-covering of `X` and `X₁ → X` a finite level). -/
theorem inertiaTempered_le_comap_ker_inf_range {W : ValuationSubring Ω} (hVW : V ≤ W) :
    (inertiaTempered O A₁ hV hVW).map (temperedPi1Map μ₁ V hV) ≤
      (TateObject.character (A := A) T V hV).ker ⊓ (temperedPi1Map μ₁ V hV).range := by
  rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
  refine ⟨?_, ⟨_, rfl⟩⟩
  rw [temperedPi1Map_inertiaToTempered]
  exact character_galoisToTempered hV T _

end KerInfRange

/-! ### `Ÿ` through a finite étale level -/

namespace TateObjectIsogeny

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [Subsingleton A]
  [MulSemiringAction A R] [SMulCommClass A K R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  [Algebra.Etale R R'] [Module.Finite R R'] [IsReduced R']
  {A' : Type u} [Group A'] [Subsingleton A'] [MulSemiringAction A' R']
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (μ : OrbMap R A R' A') (D' : TateObject.Data O R')

omit [Subsingleton A] [SMulCommClass A K R] [Algebra.Etale R R'] [Module.Finite R R'] in
/-- **Galois elements over `R'` lie in `Π^tp_Ÿ`.** -/
theorem galoisToTempered_mem_piYddot (σ : decompositionGroup R' V) :
    galoisToTempered O R A hV (decompRestrict σ) ∈ piYddot V hV μ D' :=
  ⟨galoisToTempered O R' A' hV σ, character_galoisToTempered hV D' σ,
    temperedPi1Map_galoisToTempered μ hV σ⟩

/-- **The tempered inertia group of a place of `X'` maps into `Π^tp_Ÿ`.** -/
theorem inertiaTempered_le_comap_piYddot {W : ValuationSubring Ω} (hVW : V ≤ W) :
    inertiaTempered O A' hV hVW ≤ (piYddot V hV μ D').comap (temperedPi1Map μ V hV) := by
  rw [comap_piYddot]
  exact inertiaTempered_le_ker_character hV D' hVW

section Tower

variable {R'' : Type u} [CommRing R''] [Algebra K R''] [Algebra R' R''] [IsScalarTower K R' R'']
  [Algebra R R''] [IsScalarTower R R' R''] [IsScalarTower K R R'']
  {A'' : Type u} [Group A''] [MulSemiringAction A'' R'']
  [Algebra R'' Ω] [IsScalarTower K R'' Ω] [IsScalarTower R' R'' Ω] [IsScalarTower R R'' Ω]
  (μ₂ : OrbMap R' A' R'' A'')

omit [Subsingleton A] [SMulCommClass A K R] [Algebra.Etale R R'] [Module.Finite R R']
  [IsScalarTower K R R'] [IsScalarTower R R' Ω] in
/-- **The tempered inertia group of a place of `X''` maps into `Π^tp_Ÿ ∩ Π^tp_{X''}`** (for
`X'' → X'` a finite étale cover, e.g. the level `Ÿ'_N`, and `W` a cusp of `X''`). -/
theorem inertiaTempered_le_comap_piYddotAt {W : ValuationSubring Ω} (hVW : V ≤ W) :
    inertiaTempered O A'' hV hVW ≤
      (piYddotAt V hV μ D' μ₂).comap (temperedPi1Map (μ.comp μ₂) V hV) := by
  rintro _ ⟨σ, rfl⟩
  refine ⟨inertiaToTempered O A'' hV hVW σ, ?_, rfl⟩
  change TateObject.character D' V hV (temperedPi1Map μ₂ V hV _) = 1
  rw [temperedPi1Map_inertiaToTempered]
  exact character_galoisToTempered hV D' _

/-- The tempered inertia group of a place of `X''` maps into `Π^tp_Ÿ`. -/
theorem inertiaTempered_le_comap_piYddot_of_tower {W : ValuationSubring Ω} (hVW : V ≤ W) :
    inertiaTempered O A'' hV hVW ≤
      (piYddot V hV μ D').comap (temperedPi1Map (μ.comp μ₂) V hV) := by
  intro γ hγ
  have h := inertiaTempered_le_comap_piYddotAt V hV μ D' μ₂ hVW hγ
  rw [Subgroup.mem_comap, piYddotAt_eq] at h
  exact h.1

end Tower

end TateObjectIsogeny

end

end TemperedFundamentalGroups
