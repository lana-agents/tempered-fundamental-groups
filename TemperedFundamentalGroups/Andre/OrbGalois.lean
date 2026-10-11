/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.InducedCounit
import TemperedFundamentalGroups.Andre.GaloisClass2

/-!
# Galois objects of an orbifold `[Spec R / A]` (Blueprint §11.3, G6, orbifold case)

The Galois objects of the scheme case (`Andre/GaloisDomW.lean`) are the coverings
`U_Lv = Ind_1^H Z̃` over levels `Lv = (B, H)` with trivial `H` and `B` Galois over `R`. For a
nontrivial `A` a level with trivial `H` does not exist, and a level `(B, H)` with `B` connected
does not map to the level `(Π_{a ∈ A} R^{(a)}, A)` of the cover `Spec R → [Spec R / A]`. The
Galois objects of `[Spec R / A]` are therefore built by **induction** (F7′, `IndData`) from a
scheme level `Lv₁` (over a trivial group `A₁`, `B = Lv₁.L.B` Galois over `R`):

* `OrbGal.μ₁ : OrbMap R A R A₁` (the identity of `R`, trivial on groups) and, for a finite group
  `S` with `α : S ↠ A`, the induction data `OrbGal.data` (`β = 1`): the induced level
  `(Π_{x : S} B^{(α x)}, S)` with model `∐_{x : S} 𝒯₁`;
* `OrbGal.proj`: the universal covering `p₁ : Z̃ → Z₁` of the special fibre of `Lv₁` followed
  by the inclusion of the copy `1`; it is a universal covering in the sense of
  `IsUniversalCovering` (`isUniversalCovering_proj`, the copy `1` being clopen);
* `OrbGal.obj`: **the Galois object** `GaloisObject.obj (D.lv) proj = Ind_1^S Z̃`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {A₁ : Type u} [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]

namespace OrbGal

variable (A A₁) in
/-- The map of orbifolds `Spec R = [Spec R / A₁] → [Spec R / A]` (`A₁` trivial). -/
def μ₁ : OrbMap R A R A₁ where
  α := 1
  map_smul a r := by
    rw [Subsingleton.elim a 1, one_smul, MonoidHom.one_apply, one_smul]
  injective := Function.injective_id

variable (X₁ : TempObj O R A₁) (S : Type u) [Group S] [Fintype S] [DecidableEq S]
  (α : S →* A) (hα : Function.Surjective α)

/-- **The induction data** `(S, α, β = 1)` on a covering of the scheme `[Spec R / A₁]`. -/
abbrev data : IndData (μ₁ A A₁) X₁ where
  S := S
  α := α
  α_surj := hα
  β := 1
  hβ k := by
    rw [MonoidHom.one_apply, map_one]
    rfl

variable {X₁} in
/-- The faithfulness hypothesis holds for levels with trivial `H` and nonzero `B`. -/
lemma indFaithful [Subsingleton X₁.Lv.L.H] [Nontrivial X₁.Lv.L.B] : IndFaithful X₁ :=
  ⟨inferInstance, fun k _ => Subsingleton.elim k 1⟩

lemma data_S : (data X₁ S α hα).S = S := rfl

variable {X₁} (D : IndData (μ₁ A A₁) X₁)

/-- The map `β` of induction data over a level with trivial `H` is trivial. -/
lemma β_eq_one [Subsingleton X₁.Lv.L.H] (k : X₁.Lv.L.H) : D.β k = 1 := by
  rw [Subsingleton.elim k 1, map_one]

variable (hX : IndFaithful X₁)

instance [Finite X₁.Lv.L.H] : Finite (D.lv hX).L.H :=
  Finite.of_equiv _ (D.equivT hX).toEquiv

/-! ### The covering `Z̃ → Z₁ → ∐_S Z₁` -/

lemma isEmbedding_inc₁S : Topology.IsEmbedding (D.inc₁S hX) := by
  have h₁ : Topology.IsEmbedding (fun z : (D.lv hX).Z => z.1) :=
    Topology.IsEmbedding.subtypeVal
  have h₂ : Topology.IsEmbedding ((D.inc 1).base ∘ fun z : X₁.Lv.Z => (z : X₁.Lv.c.scheme)) :=
    (D.inc 1).isOpenEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have h₃ : (fun z : (D.lv hX).Z => z.1) ∘ D.inc₁S hX =
      (D.inc 1).base ∘ fun z : X₁.Lv.Z => (z : X₁.Lv.c.scheme) := by
    funext z
    exact D.inc₁S_coe hX z
  rw [← h₃] at h₂
  exact Topology.IsEmbedding.of_comp (continuous_specialFibreMap _ _) h₁.continuous h₂

lemma range_inc₁S :
    Set.range (D.inc₁S hX) =
      {z | D.copy z.1 = 1} := by
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq]
  rw [IndData.copy_eq_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1, (D.inc₁S_coe hX w).symm⟩
  · rintro ⟨w, hw⟩
    have hw' : w ∈ specialFibre X₁.Lv.c.toSpec := by
      have hz := z.2
      change z.1 ∈ specialFibre D.c.toSpec at hz
      rw [← hw] at hz
      have h2 : D.c.toSpec (D.inc 1 w) = X₁.Lv.c.toSpec w := by
        rw [← Scheme.Hom.comp_apply, D.inc_toSpec]
      change X₁.Lv.c.toSpec w ∈ ({IsLocalRing.closedPoint O} : Set _)
      rw [← h2]
      exact hz
    exact ⟨⟨w, hw'⟩, Subtype.ext ((D.inc₁S_coe hX _).trans hw)⟩

lemma isClopen_range_inc₁S : IsClopen (Set.range (D.inc₁S hX)) := by
  rw [range_inc₁S D hX]
  have hopen : ∀ x : D.S, IsOpen {z : (D.lv hX).Z | D.copy z.1 = x} := fun x =>
    (D.isOpen_copy x).preimage continuous_subtype_val
  refine ⟨?_, hopen 1⟩
  rw [← isOpen_compl_iff]
  have : {z : (D.lv hX).Z | D.copy z.1 = 1}ᶜ =
      ⋃ x ∈ ({1}ᶜ : Set D.S), {z : (D.lv hX).Z | D.copy z.1 = x} := by
    ext z
    simp
  rw [this]
  exact isOpen_biUnion fun x _ => hopen x

variable {E : Type u} [TopologicalSpace E] {p : E → X₁.Lv.Z}

/-- The covering `Z̃ → Z₁` followed by the inclusion of the copy `1`. -/
def proj (p : E → X₁.Lv.Z) : E → (D.lv hX).Z :=
  D.inc₁S hX ∘ p

lemma isCoveringMap_proj (hp : IsCoveringMap p) : IsCoveringMap (proj D hX p) := by
  set s := Set.range (D.inc₁S hX)
  have hs := isClopen_range_inc₁S D hX
  let e : X₁.Lv.Z ≃ₜ s := (isEmbedding_inc₁S D hX).toHomeomorph
  have hon : IsCoveringMapOn (proj D hX p) s := by
    refine IsCoveringMapOn.of_isCoveringMap_subtype hs.isOpen (fun x => ⟨p x, rfl⟩) ?_
    have : (fun x => (⟨proj D hX p x, ⟨p x, rfl⟩⟩ : s)) = e ∘ p := by
      funext x
      rfl
    rw [this]
    exact hp.homeomorph_comp e
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  intro z _
  by_cases hz : z ∈ s
  · exact hon z hz
  · haveI : IsEmpty (proj D hX p ⁻¹' {z}) :=
      ⟨fun ⟨x, hx⟩ => hz ⟨p x, hx⟩⟩
    exact IsEvenlyCovered.of_preimage_eq_empty (proj D hX p ⁻¹' {z})
      (hs.isClosed.isOpen_compl.mem_nhds hz)
      (Set.eq_empty_of_forall_notMem fun x hx => hx ⟨p x, rfl⟩)

/-- `proj` is a universal covering in the sense of `IsUniversalCovering` (which only depends on
the total space `Z̃`). -/
lemma isUniversalCovering_proj (hp : IsUniversalCovering.{u, u, u, u} p) :
    IsUniversalCovering.{u, u, u, u} (proj D hX p) :=
  ⟨isCoveringMap_proj D hX hp.isCoveringMap, hp.connectedSpace, hp.exists_lift⟩

lemma countable_proj (hc : ∀ z, (p ⁻¹' {z}).Countable) (z : (D.lv hX).Z) :
    (proj D hX p ⁻¹' {z}).Countable := by
  by_cases hz : z ∈ Set.range (D.inc₁S hX)
  · obtain ⟨w, rfl⟩ := hz
    have : proj D hX p ⁻¹' {D.inc₁S hX w} = p ⁻¹' {w} := by
      ext x
      simp only [proj, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
      exact (isEmbedding_inc₁S D hX).injective.eq_iff
    rw [this]
    exact hc w
  · have : proj D hX p ⁻¹' {z} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => hz ⟨p x, hx⟩
    rw [this]
    exact Set.countable_empty

variable [Finite X₁.Lv.L.H] (hp : IsUniversalCovering.{u, u, u, u} p)
  (hc : ∀ z, (p ⁻¹' {z}).Countable)

/-- **The Galois object** `Ind_1^S Z̃` over the induced level `(Π_{x : S} B^{(α x)}, S)`. -/
abbrev obj : TempObj O R A :=
  GaloisObject.obj (D.lv hX) (isUniversalCovering_proj D hX hp)
    (countable_proj D hX hc)

end OrbGal

end

end TemperedFundamentalGroups
