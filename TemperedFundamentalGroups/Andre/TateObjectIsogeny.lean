/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateObject
import TemperedFundamentalGroups.Tempered.CoverImage
import TemperedFundamentalGroups.Tempered.BaseChangeComp

/-!
# The tempered covering `Ÿ → X` for `X = E_q ∖ {O}` through a finite étale level ([EtTh], §1)

In [EtTh] §1 the tempered covering `Ÿ → X` of the punctured Tate curve `X = E_q ∖ {O}` is the
`ℤ`-covering (on the coordinate `Ü`, `Ü² = U`) of the finite étale double covering
`X' = E_{√q} ∖ {±1} → X` given by the `2`-isogeny `Ü ↦ Ü²`. The file `TateObjectDouble.lean`
realises `Ÿ` through the Kummer presentation `R[t]/(t² − (x − e))`, which is étale only away from
the `2`-torsion point; here the finite étale level is **an arbitrary finite étale `R`-algebra
`R'`** (for `Ÿ`: the coordinate ring of `X'`), carrying the Tate data of the curve whose
`ℤ`-covering is taken (for `Ÿ`: the Tate curve `E_{√q}` with its point `(x_{√q}, y_{√q}) ∈ R'²`).

Setting: `R` and `R'` with trivial groups `A`, `A'`, `R → R'` finite étale (`μ : OrbMap`),
`D' : TateObject.Data O R'` (Tate data with a point in `R'`).

* `yddot D' = TateObject.X₀ D'`: the `ℤ`-covering of the special fibre of the Tate model of `D'`,
  as an object over `X' = Spec R'`; `TateObject.character D'` is its deck character
  `Π^tp_{X'} → ℤ`, and `ker_character_iff`: its kernel is the stabilizer of the base point.
* `yddotX D' = push (yddot D')`: the same covering as an object over `X = Spec R`, with base point
  `basePt` (the image of the base point of `yddot D'`).
* **`piYddot μ D'`** `= temperedPi1Map μ (ker χ_{D'}) ⊆ Π^tp_X` (`Π^tp_Ÿ`), and
  **`mem_piYddot_iff`**: it is the stabilizer of `basePt` in `Π^tp_X`. It is open
  (`isOpen_piYddot`), contained in the open subgroup `Π^tp_{X'}` (`piYddot_le_range`), and normal
  there (`map_comap_piYddot`: `Π^tp_Ÿ` is the image of a normal subgroup of `Π^tp_{X'}`).
* `yddotToCover`: the structure morphism `Ÿ → (Spec R' → Spec R)` (`TempObj.coverHom`), so that
  `Π^tp_Ÿ` fixes the base point of the cover `Spec R'` (`piYddot_le_range` again).

**Towers** `R → R' → R''` (`piYddotAt`): the image in `Π^tp_X` of the kernel of
`χ_{D'} ∘ (Π^tp_{X''} → Π^tp_{X'})` is `Π^tp_Ÿ ∩ Π^tp_{X''}` (`piYddotAt_eq`). For `R''` the
coordinate ring of a finite étale cover `X'' → X'` (e.g. the level `Ÿ'_N` of [EtTh] §1), this is the
part of `Π^tp_Ÿ` that lies in `Π^tp_{X''}`; it is all of `Π^tp_Ÿ` exactly when
`Π^tp_Ÿ ≤ Π^tp_{X''}` (`piYddotAt_eq_iff`), i.e. when `X''` is dominated by the `ℤ`-covering `Ÿ`.

This is the object of requirement R1 of the étale theta function track (`MR14-plan.md`): the
finite level `R'` is arbitrary, so it can be the coordinate ring of `X'` or of any finite étale
cover of `X'` carrying the point of `E_{√q}`.
-/

universe w v u' u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

/-! ### A point fixed by the image of a push lies over the base point of the cover -/

namespace PushData

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v} C'] {F : C ⥤ Type w}
  {F' : C' ⥤ Type w} {G : C ⥤ C'} {e : G ⋙ F' ≅ F}

/-- An automorphism fixing a point `ι x` of a pushed object fixes the base point of the cover. -/
lemma mem_stab_of_app_ι (D : PushData G e) {γ : FibreAut F} {X' : C'} {x : F'.obj X'}
    (h : γ.app (D.P.obj X') (D.ι X' x) = D.ι X' x) : γ ∈ D.stab := by
  have hx : F.map (D.τ X') (D.ι X' x) = D.x₀ := (D.range_ι X' _).1 ⟨x, rfl⟩
  rw [mem_stab, ← hx, FibreAut.app_naturality, h]

end PushData

namespace TateObjectIsogeny

noncomputable section

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

/-! ### `Ÿ` over `X'` -/

variable (A') in
/-- **`Ÿ` over `X' = Spec R'`**: the `ℤ`-covering of the special fibre of the Tate model of `D'`. -/
abbrev yddot : TempObj O R' A' := TateObject.X₀ (A := A') D'

/-- **The kernel of the deck character is the stabilizer of the base point.** -/
theorem ker_character_iff (γ : temperedPi1 O R' A' V hV) :
    γ ∈ (TateObject.character (A := A') D' V hV).ker ↔
      γ.app (yddot A' D') (TateObject.basePoint D' V hV) = TateObject.basePoint D' V hV := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have := FibreAut.deckAct_deckCharacter (yddot A' D') (TateObject.deck D')
      (TateObject.basePoint D' V hV) (TateObject.isDeckTorsor D' V hV) γ
    change FibreAut.deckAct _ _ (TateObject.character D' V hV γ) _ = _ at this
    rw [h, FibreAut.deckAct_one] at this
    exact this.symm
  · intro h
    exact FibreAut.deckCharacterFun_eq (yddot A' D') (TateObject.deck D') _
      (TateObject.isDeckTorsor D' V hV) (by rw [h, FibreAut.deckAct_one])

/-! ### `Ÿ` over `X` -/

variable (R A A') in
/-- **`Ÿ` as a tempered covering of `X = Spec R`** (push along `Spec R' → Spec R`). -/
abbrev yddotX : TempObj O R A := (yddot A' D').push R A

variable (R A) in
/-- The base point of `Ÿ` over `X`. -/
def basePt : TempObj.Fibre Ω V hV (yddotX R A A' D') :=
  TempObj.pushι R A V hV (yddot A' D') (TateObject.basePoint D' V hV)

/-- **`Π^tp_Ÿ ⊆ Π^tp_X`**: the image of the kernel of the deck character of `Ÿ → X'`. -/
def piYddot : Subgroup (temperedPi1 O R A V hV) :=
  (TateObject.character (A := A') D' V hV).ker.map (temperedPi1Map μ V hV)

/-- **`Π^tp_Ÿ` is the stabilizer of the base point of `Ÿ` over `X`.** -/
theorem mem_piYddot_iff (γ : temperedPi1 O R A V hV) :
    γ ∈ piYddot V hV μ D' ↔
      γ.app (yddotX R A A' D') (basePt R A V hV D') = basePt R A V hV D' := by
  constructor
  · rintro ⟨γ', hγ', rfl⟩
    have hγ'' := (ker_character_iff V hV D' γ').1 hγ'
    rw [basePt, temperedPi1Map_app_pushι, hγ'']
  · intro h
    have hst : γ ∈ (coverPushData V hV μ).stab :=
      (coverPushData V hV μ).mem_stab_of_app_ι (X' := yddot A' D')
        (x := TateObject.basePoint D' V hV) h
    rw [← (coverPushData V hV μ).range_restrict] at hst
    obtain ⟨γ', rfl⟩ := hst
    refine ⟨γ', (ker_character_iff V hV D' γ').2 ?_, rfl⟩
    exact (TempObj.pushι_injective V hV _) ((temperedPi1Map_app_pushι V hV μ γ' _ _).symm.trans h)

omit [Subsingleton A] [SMulCommClass A K R] [Algebra.Etale R R'] [Module.Finite R R'] in
/-- `Π^tp_Ÿ` lies in the open subgroup `Π^tp_{X'}` (the stabilizer of the base point of the cover
`Spec R' → Spec R`). -/
theorem piYddot_le_range : piYddot V hV μ D' ≤ (temperedPi1Map (O := O) μ V hV).range := by
  rintro _ ⟨γ', -, rfl⟩
  exact ⟨γ', rfl⟩

/-- **`Π^tp_Ÿ` is open in `Π^tp_X`.** -/
theorem isOpen_piYddot : IsOpen (piYddot V hV μ D' : Set (temperedPi1 O R A V hV)) := by
  have hker : IsOpen ((TateObject.character (A := A') D' V hV).ker :
      Set (temperedPi1 O R' A' V hV)) := by
    have : ((TateObject.character (A := A') D' V hV).ker : Set (temperedPi1 O R' A' V hV)) =
        TateObject.character D' V hV ⁻¹' {1} := rfl
    rw [this]
    exact (isOpen_discrete _).preimage (TateObject.continuous_character D' V hV)
  have := (isOpenEmbedding_temperedPi1Map (O := O) V hV μ).isOpenMap _ hker
  simpa [piYddot, Subgroup.coe_map] using this

/-- **`Π^tp_Ÿ` is normal in `Π^tp_{X'}`**: its preimage in `Π^tp_{X'}` is the kernel of the deck
character. -/
theorem comap_piYddot :
    (piYddot V hV μ D').comap (temperedPi1Map (O := O) μ V hV) =
      (TateObject.character (A := A') D' V hV).ker :=
  Subgroup.comap_map_eq_self_of_injective (temperedPi1Map_injective V hV μ) _

variable (A') in
/-- **The structure morphism `Ÿ → (Spec R' → Spec R)`** of the tempered covering `Ÿ` over `X`
to the finite étale cover `X' → X`. -/
def yddotToCover : yddotX R A A' D' ⟶ coverObj O R A R' :=
  TempObj.coverHom R A (yddot A' D')

include μ in
/-- The structure morphism maps the base point of `Ÿ` to the base point of the cover. -/
theorem yddotToCover_basePt :
    TempObj.fibreMap V hV (yddotToCover A' D') (basePt (A' := A') R A V hV D') =
      coverFibrePt V hV :=
  ((coverPushData V hV μ).range_ι (yddot A' D') _).1 ⟨TateObject.basePoint D' V hV, rfl⟩

/-! ### Towers `R → R' → R''` -/

section Tower

variable {R'' : Type u} [CommRing R''] [Algebra K R''] [Algebra R' R''] [IsScalarTower K R' R'']
  [Algebra R R''] [IsScalarTower R R' R''] [IsScalarTower K R R'']
  {A'' : Type u} [Group A''] [MulSemiringAction A'' R'']
  [Algebra R'' Ω] [IsScalarTower K R'' Ω] [IsScalarTower R' R'' Ω] [IsScalarTower R R'' Ω]
  (μ₂ : OrbMap R' A' R'' A'')

/-- **`Π^tp_Ÿ ∩ Π^tp_{X''}`** for a tower `X'' → X' → X`: the image in `Π^tp_X` of the kernel of
the deck character of `Ÿ → X'` restricted to `Π^tp_{X''}`. -/
def piYddotAt : Subgroup (temperedPi1 O R A V hV) :=
  ((TateObject.character (A := A') D' V hV).comp (temperedPi1Map μ₂ V hV)).ker.map
    (temperedPi1Map (μ.comp μ₂) V hV)

/-- **`piYddotAt = Π^tp_Ÿ ∩ Π^tp_{X''}`.** -/
theorem piYddotAt_eq :
    piYddotAt V hV μ D' μ₂ =
      piYddot V hV μ D' ⊓ (temperedPi1Map (O := O) (μ.comp μ₂) V hV).range := by
  ext γ
  constructor
  · rintro ⟨γ'', hγ'', rfl⟩
    refine ⟨⟨temperedPi1Map μ₂ V hV γ'', hγ'', (temperedPi1Map_comp μ μ₂ V hV γ'').symm⟩,
      ⟨γ'', rfl⟩⟩
  · rintro ⟨⟨γ', hγ', rfl⟩, ⟨γ'', hγ''⟩⟩
    have e : temperedPi1Map μ₂ V hV γ'' = γ' :=
      temperedPi1Map_injective V hV μ ((temperedPi1Map_comp μ μ₂ V hV γ'').symm.trans hγ'')
    refine ⟨γ'', ?_, hγ''⟩
    change TateObject.character D' V hV (temperedPi1Map μ₂ V hV γ'') = 1
    rw [e]
    exact hγ'

/-- `piYddotAt` is all of `Π^tp_Ÿ` iff `Π^tp_Ÿ ≤ Π^tp_{X''}`. -/
theorem piYddotAt_eq_iff :
    piYddotAt V hV μ D' μ₂ = piYddot V hV μ D' ↔
      piYddot V hV μ D' ≤ (temperedPi1Map (O := O) (μ.comp μ₂) V hV).range := by
  rw [piYddotAt_eq, inf_eq_left]

/-- `piYddotAt ≤ Π^tp_{X''}`. -/
theorem piYddotAt_le_range :
    piYddotAt V hV μ D' μ₂ ≤ (temperedPi1Map (O := O) (μ.comp μ₂) V hV).range := by
  rw [piYddotAt_eq]
  exact inf_le_right

end Tower

end

end TateObjectIsogeny

end TemperedFundamentalGroups
