/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.FieldChangeFinite
import TemperedFundamentalGroups.Tempered.MixedCover

/-!
# F8 for orbifolds and finite étale maps of orbifolds (Blueprint §11, F8)

**Finite étale maps of orbifolds.** Let `ν : OrbMap R A R' A'` be a map of orbifolds
`[Spec R' / A'] → [Spec R / A]` with `R → R'` finite étale, `A`, `A'` finite and `R`, `R'`
noetherian domains (e.g. `A' = A` acting compatibly). Then `ν ∘ (Spec R' → [Spec R' / A'])`
equals `(Spec R → [Spec R / A]) ∘ (Spec R' → Spec R)` (`EtaleOrb.comp_eq`), and the known
cases F7 (scheme case), F7′ (orbifold covers) and the mixed case give:

* the image of `temperedPi1Map ν` is an **open subgroup of finite index**
  (`isOpen_range_temperedPi1Map_etaleOrb`, `finiteIndex_range_temperedPi1Map_etaleOrb`);
* its kernel is **finite** and meets the open subgroup of finite index
  `temperedPi1 O R' 1 ⊆ temperedPi1 O R' A'` trivially (`finite_ker_temperedPi1Map_etaleOrb`,
  `ker_inf_range_temperedPi1Map_etaleOrb`).

If moreover `A'` acts faithfully on `R'`, the kernel is trivial: `temperedPi1Map ν` and the field
change `temperedPi1FieldMap hO ν` are injective open embeddings
(`temperedPi1Map_injective_etaleOrb`, `isOpenEmbedding_temperedPi1Map_etaleOrb`,
`temperedPi1FieldMap_injective_etaleOrb`, `isOpenEmbedding_temperedPi1FieldMap_etaleOrb`, in
`Tempered/EtaleOrbCover.lean`, using the statements of this file).

**Field change.** For `O` a complete DVR and `K'/K` finite separable, the pure field change is
an isomorphism (`temperedPi1FieldEquiv'`), so for **any** map of orbifolds `μ` the field change
`temperedPi1FieldMap hO μ` has the same image as `temperedPi1Map μ`, and is injective (an open
embedding) iff `temperedPi1Map μ` is (`range_temperedPi1FieldMap_eq`,
`temperedPi1FieldMap_injective_iff`, `isOpenEmbedding_temperedPi1FieldMap_iff`). Hence F8 holds
for orbifold covers (`*_temperedPi1FieldMap_orbifold`), for the mixed case
(`*_temperedPi1FieldMap_mixed`), and its image statement for finite étale maps of orbifolds
(`isOpen_range_temperedPi1FieldMap_etaleOrb`, `finiteIndex_range_temperedPi1FieldMap_etaleOrb`).
-/

universe u

open CategoryTheory IsLocalRing Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

/-- Maps of orbifolds are determined by their group homomorphisms. -/
lemma OrbMap.ext_α {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]
    {R' : Type u} [CommRing R'] [Algebra R R'] {A' : Type u} [Group A']
    [MulSemiringAction A' R'] {μ μ' : OrbMap R A R' A'} (h : μ.α = μ'.α) : μ = μ' := by
  cases μ
  cases μ'
  cases h
  rfl

namespace EtaleOrb

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra R R'] {A' : Type u} [Group A'] [MulSemiringAction A' R']

variable (R A) in
/-- The orbifold cover `Spec R → [Spec R / A]` (trivial group `⊥ ≤ A`). -/
def cov : OrbMap R A R (⊥ : Subgroup A) where
  α := (⊥ : Subgroup A).subtype
  map_smul _ _ := rfl
  injective := fun _ _ h => h

/-- The finite étale map `Spec R' → Spec R` underlying `ν` (trivial groups). -/
def under (ν : OrbMap R A R' A') : OrbMap R (⊥ : Subgroup A) R' (⊥ : Subgroup A') where
  α := 1
  map_smul a r := by
    rw [Subsingleton.elim a 1, MonoidHom.one_apply, one_smul, one_smul]
  injective := ν.injective

/-- `ν ∘ (Spec R' → [Spec R' / A']) = (Spec R → [Spec R / A]) ∘ (Spec R' → Spec R)`. -/
lemma comp_eq (ν : OrbMap R A R' A') : ν.comp (cov R' A') = (cov R A).comp (under ν) :=
  OrbMap.ext_α <| MonoidHom.ext fun a => by
    rw [Subsingleton.elim a 1, map_one, map_one]

instance faithful_bot : FaithfulSMul (⊥ : Subgroup A) R := ⟨fun _ => Subsingleton.elim _ _⟩

end EtaleOrb

section EtaleOrb

open EtaleOrb

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsDomain R] [IsNoetherianRing R]
  {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R] [Finite A]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  [IsDomain R'] [IsNoetherianRing R'] [Algebra.Etale R R'] [Module.Finite R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K R'] [Finite A']
  (ν : OrbMap R A R' A')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma temperedPi1Map_comp_cov_eq :
    (temperedPi1Map ν V hV).comp (temperedPi1Map (O := O) (cov R' A') V hV) =
      temperedPi1Map ((cov R A).comp (under ν)) V hV := by
  rw [← temperedPi1Map_comp_eq, comp_eq]

/-- The image of `temperedPi1Map ν` contains the image of the mixed composite. -/
lemma range_mixed_le_range_temperedPi1Map_etaleOrb :
    (temperedPi1Map (O := O) ((cov R A).comp (under ν)) V hV).range ≤
      (temperedPi1Map ν V hV).range := by
  rw [← temperedPi1Map_comp_cov_eq, MonoidHom.range_comp]
  exact Subgroup.map_le_range _ _

/-- **Finite étale maps of orbifolds: the image of `temperedPi1Map ν` is open.** -/
theorem isOpen_range_temperedPi1Map_etaleOrb :
    IsOpen ((temperedPi1Map (O := O) ν V hV).range : Set (temperedPi1 O R A V hV)) :=
  Subgroup.isOpen_mono (range_mixed_le_range_temperedPi1Map_etaleOrb ν V hV)
    (by
      rw [MonoidHom.coe_range]
      exact (isOpenEmbedding_temperedPi1Map_mixed (cov R A) (under ν) V hV).isOpen_range)

/-- **Finite étale maps of orbifolds: the image of `temperedPi1Map ν` has finite index.** -/
theorem finiteIndex_range_temperedPi1Map_etaleOrb :
    (temperedPi1Map (O := O) ν V hV).range.FiniteIndex := by
  haveI := finiteIndex_range_temperedPi1Map_mixed (O := O) (cov R A) (under ν) V hV
  exact Subgroup.finiteIndex_of_le (range_mixed_le_range_temperedPi1Map_etaleOrb ν V hV)

/-- The kernel of `temperedPi1Map ν` meets the image of `temperedPi1 O R' 1` trivially. -/
theorem ker_inf_range_temperedPi1Map_etaleOrb :
    (temperedPi1Map (O := O) ν V hV).ker ⊓ (temperedPi1Map (O := O) (cov R' A') V hV).range =
      ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hk, ⟨y, rfl⟩⟩
  have hinj := temperedPi1Map_injective_mixed (O := O) (cov R A) (under ν) V hV
  rw [← temperedPi1Map_comp_cov_eq] at hinj
  have hk' : temperedPi1Map ν V hV (temperedPi1Map (O := O) (cov R' A') V hV y) = 1 := hk
  have hy : y = 1 := hinj (by rw [MonoidHom.comp_apply, hk', map_one])
  rw [Subgroup.mem_bot, hy, map_one]

/-- **Finite étale maps of orbifolds: the kernel of `temperedPi1Map ν` is finite.** -/
theorem finite_ker_temperedPi1Map_etaleOrb : Finite (temperedPi1Map (O := O) ν V hV).ker := by
  set N := (temperedPi1Map (O := O) ν V hV).ker
  set H := (temperedPi1Map (O := O) (cov R' A') V hV).range
  haveI : H.FiniteIndex := finiteIndex_range_temperedPi1Map_orbifold (cov R' A') V hV
  have hbot : H.subgroupOf N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : temperedPi1 O R' A' V hV) ∈ N ⊓ H := ⟨x.2, hx⟩
    rw [ker_inf_range_temperedPi1Map_etaleOrb ν V hV, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  have hfi : (H.subgroupOf N).FiniteIndex := inferInstance
  rw [hbot, Subgroup.finiteIndex_iff, Subgroup.index_bot] at hfi
  exact Nat.finite_of_card_ne_zero hfi

end EtaleOrb

section FieldChange

variable {K : Type u} [Field K] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
  {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra.IsSeparable K K']
  {O' : ValuationSubring K'} (hO : O'.comap (algebraMap K K') = O)

section General

variable {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R']
  [Algebra R R'] [IsScalarTower K R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K' R']
  (μ : OrbMap R A R' A')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω]
  [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

lemma coe_temperedPi1FieldMap_eq : ⇑(temperedPi1FieldMap hO μ V hV') =
    temperedPi1Map μ V (TempObj.comap_eq hO V hV') ∘ temperedPi1FieldEquiv' hO V hV' := by
  rw [temperedPi1FieldMap_eq_comp']
  rfl

/-- **F8 for any map of orbifolds: the field change has the same image as `temperedPi1Map μ`**
(`O` a complete DVR, `K'/K` finite separable). -/
theorem range_temperedPi1FieldMap_eq :
    (temperedPi1FieldMap hO μ V hV').range =
      (temperedPi1Map μ V (TempObj.comap_eq hO V hV')).range := by
  rw [temperedPi1FieldMap_eq_comp', MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (bijective_temperedPi1FieldMap_pure' hO V hV').2,
    ← MonoidHom.range_eq_map]

theorem temperedPi1FieldMap_injective_iff :
    Function.Injective (temperedPi1FieldMap hO μ V hV') ↔
      Function.Injective (temperedPi1Map μ V (TempObj.comap_eq hO V hV')) := by
  rw [coe_temperedPi1FieldMap_eq]
  exact Function.Injective.of_comp_iff' _ (temperedPi1FieldEquiv' hO V hV').bijective

theorem isOpenEmbedding_temperedPi1FieldMap_iff :
    Topology.IsOpenEmbedding (temperedPi1FieldMap hO μ V hV') ↔
      Topology.IsOpenEmbedding (temperedPi1Map μ V (TempObj.comap_eq hO V hV')) := by
  set e := temperedPi1FieldEquiv' (R' := R') (A' := A') hO V hV'
  rw [coe_temperedPi1FieldMap_eq]
  refine ⟨fun h => ?_, fun h => h.comp e.toHomeomorph.isOpenEmbedding⟩
  have : ⇑(temperedPi1Map μ V (TempObj.comap_eq hO V hV')) =
      (temperedPi1Map μ V (TempObj.comap_eq hO V hV') ∘ e) ∘ e.symm := by
    funext x
    simp
  rw [this]
  exact h.comp e.symm.toHomeomorph.isOpenEmbedding

end General

section Orbifold

variable {R : Type u} [CommRing R] [Algebra K R] [Algebra K' R] [IsScalarTower K K' R]
  [IsDomain R] [IsNoetherianRing R]
  {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R] [Finite A]
  {A' : Type u} [Group A'] [MulSemiringAction A' R] [SMulCommClass A' K R]
  [SMulCommClass A' K' R] [FaithfulSMul A' R] (μ : OrbMap R A R A')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [IsScalarTower K' R Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

/-- **F8 for orbifold covers** `[Spec R / A'] → [Spec R / A]`: the field change is injective. -/
theorem temperedPi1FieldMap_injective_orbifold :
    Function.Injective (temperedPi1FieldMap hO μ V hV') :=
  (temperedPi1FieldMap_injective_iff hO μ V hV').2 (temperedPi1Map_injective_orbifold μ V _)

/-- **F8 for orbifold covers: the field change is an open embedding.** -/
theorem isOpenEmbedding_temperedPi1FieldMap_orbifold :
    Topology.IsOpenEmbedding (temperedPi1FieldMap hO μ V hV') :=
  (isOpenEmbedding_temperedPi1FieldMap_iff hO μ V hV').2
    (isOpenEmbedding_temperedPi1Map_orbifold μ V _)

/-- **F8 for orbifold covers: the image is the stabilizer of the base point of the cover**,
the image of `temperedPi1Map μ`, of finite index. -/
theorem range_temperedPi1FieldMap_orbifold :
    (temperedPi1FieldMap hO μ V hV').range =
      (temperedPi1Map μ V (TempObj.comap_eq hO V hV')).range :=
  range_temperedPi1FieldMap_eq hO μ V hV'

theorem finiteIndex_range_temperedPi1FieldMap_orbifold :
    (temperedPi1FieldMap hO μ V hV').range.FiniteIndex := by
  rw [range_temperedPi1FieldMap_eq]
  exact finiteIndex_range_temperedPi1Map_orbifold μ V _

end Orbifold

section Mixed

variable {R : Type u} [CommRing R] [Algebra K R] [IsDomain R] [IsNoetherianRing R]
  {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R] [Finite A]
  {A₁ : Type u} [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R']
  [Algebra R R'] [IsScalarTower K R R'] [Algebra.Etale R R'] [Module.Finite R R']
  {A₂ : Type u} [Group A₂] [Subsingleton A₂] [MulSemiringAction A₂ R'] [SMulCommClass A₂ K' R']
  (μ₁ : OrbMap R A R A₁) (μ₂ : OrbMap R A₁ R' A₂)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω]
  [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

/-- **F8, mixed case** `Spec R' → Spec R → [Spec R / A]`: the field change is an open
embedding. -/
theorem isOpenEmbedding_temperedPi1FieldMap_mixed :
    Topology.IsOpenEmbedding (temperedPi1FieldMap hO (μ₁.comp μ₂) V hV') :=
  (isOpenEmbedding_temperedPi1FieldMap_iff hO _ V hV').2
    (isOpenEmbedding_temperedPi1Map_mixed μ₁ μ₂ V _)

theorem finiteIndex_range_temperedPi1FieldMap_mixed :
    (temperedPi1FieldMap hO (μ₁.comp μ₂) V hV').range.FiniteIndex := by
  rw [range_temperedPi1FieldMap_eq]
  exact finiteIndex_range_temperedPi1Map_mixed μ₁ μ₂ V _

end Mixed

section EtaleOrb

variable {R : Type u} [CommRing R] [Algebra K R] [IsDomain R] [IsNoetherianRing R]
  {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R] [Finite A]
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R']
  [Algebra R R'] [IsScalarTower K R R'] [IsDomain R'] [IsNoetherianRing R']
  [Algebra.Etale R R'] [Module.Finite R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K R']
  [SMulCommClass A' K' R'] [Finite A'] (ν : OrbMap R A R' A')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R Ω] [IsScalarTower K R Ω] [Algebra R' Ω] [IsScalarTower K' R' Ω]
  [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

/-- **F8 image statement for finite étale maps of orbifolds** `[Spec R' / A'] → [Spec R / A]`:
the image of the field change is open. -/
theorem isOpen_range_temperedPi1FieldMap_etaleOrb :
    IsOpen ((temperedPi1FieldMap hO ν V hV').range :
      Set (temperedPi1 O R A V (TempObj.comap_eq hO V hV'))) := by
  rw [range_temperedPi1FieldMap_eq]
  exact isOpen_range_temperedPi1Map_etaleOrb ν V _

/-- **F8 image statement for finite étale maps of orbifolds: the image has finite index.** -/
theorem finiteIndex_range_temperedPi1FieldMap_etaleOrb :
    (temperedPi1FieldMap hO ν V hV').range.FiniteIndex := by
  rw [range_temperedPi1FieldMap_eq]
  exact finiteIndex_range_temperedPi1Map_etaleOrb ν V _

end EtaleOrb

end FieldChange

end

end TemperedFundamentalGroups
