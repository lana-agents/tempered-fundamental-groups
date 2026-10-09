/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Orbifold.FibreAut

/-!
# Characters of `Aut F` from deck transformations

Let `F : C ⥤ Type w` be a fibre functor, `c : C` an object and `δ : D →* Aut c` an action of a
commutative group `D` on `c` (deck transformations) such that `D` acts simply transitively on the
fibre `F c`. Every automorphism `α` of `F` commutes with the deck transformations (naturality), so
it acts on the `D`-torsor `F c` by a translation: `α x₀ = δ(χ α) • x₀`. This defines a continuous
homomorphism `FibreAut.deckCharacter : FibreAut F →* D` (for `D` with the discrete topology;
its kernel contains the open stabilizer of `x₀`).

For the tempered fundamental group this is how a `ℤ`-covering of the special fibre of a model
(e.g. the universal covering of a cycle of projective lines, with deck group `ℤ`) gives a
continuous homomorphism `temperedPi1 → ℤ`. Whether its image is nonzero (the non-degeneracy of
the tempered group) is a separate question — see Blueprint §5 (G1).
-/

universe w v u

open CategoryTheory Pi1.Orbifold Pi1.Orbifold.FibreAut

namespace TemperedFundamentalGroups

namespace FibreAut

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w} {D : Type*} [CommGroup D]

/-- The action of a deck transformation on the fibre. -/
def deckAct (c : C) (δ : D →* Aut c) (d : D) (x : F.obj c) : F.obj c := F.map (δ d).hom x

/-- `D` acts simply transitively on the fibre `F c` through `δ`. -/
def IsDeckTorsor (c : C) (δ : D →* Aut c) : Prop :=
  ∀ x y : F.obj c, ∃! d : D, deckAct c δ d x = y

lemma deckAct_mul (c : C) (δ : D →* Aut c) (d e : D) (x : F.obj c) :
    deckAct (F := F) c δ (d * e) x = deckAct c δ d (deckAct c δ e x) := by
  simp only [deckAct, map_mul, Aut.Aut_mul_def, Iso.trans_hom, Functor.map_comp_apply]

@[simp] lemma deckAct_one (c : C) (δ : D →* Aut c) (x : F.obj c) :
    deckAct (F := F) c δ 1 x = x := by
  simp only [deckAct, map_one]
  exact Functor.map_id_apply F c x

lemma app_deckAct (α : FibreAut F) (c : C) (δ : D →* Aut c) (d : D) (x : F.obj c) :
    α.app c (deckAct c δ d x) = deckAct c δ d (α.app c x) :=
  app_naturality α _ x

variable (c : C) (δ : D →* Aut c) (x₀ : F.obj c) (h : IsDeckTorsor (F := F) c δ)

/-- The translation by which an automorphism acts on the deck torsor `F c`. -/
noncomputable def deckCharacterFun (α : FibreAut F) : D :=
  (h x₀ (α.app c x₀)).exists.choose

lemma deckAct_deckCharacterFun (α : FibreAut F) :
    deckAct c δ (deckCharacterFun c δ x₀ h α) x₀ = α.app c x₀ :=
  (h x₀ (α.app c x₀)).exists.choose_spec

lemma deckCharacterFun_eq {α : FibreAut F} {d : D} (hd : deckAct c δ d x₀ = α.app c x₀) :
    deckCharacterFun c δ x₀ h α = d :=
  (h x₀ (α.app c x₀)).unique (deckAct_deckCharacterFun c δ x₀ h α) hd

/-- **The character of `Aut F` defined by a deck torsor.** -/
noncomputable def deckCharacter : FibreAut F →* D where
  toFun := deckCharacterFun c δ x₀ h
  map_one' := deckCharacterFun_eq c δ x₀ h (by simp)
  map_mul' α β := by
    apply deckCharacterFun_eq
    rw [mul_app, ← deckAct_deckCharacterFun c δ x₀ h β, app_deckAct,
      ← deckAct_deckCharacterFun c δ x₀ h α, ← deckAct_mul, mul_comm]

lemma deckAct_deckCharacter (α : FibreAut F) :
    deckAct c δ (deckCharacter c δ x₀ h α) x₀ = α.app c x₀ :=
  deckAct_deckCharacterFun c δ x₀ h α

/-- The deck character is continuous for the discrete topology on `D`. -/
lemma continuous_deckCharacter [TopologicalSpace D] [DiscreteTopology D] :
    Continuous (deckCharacter c δ x₀ h) := by
  have : IsOpen ((deckCharacter c δ x₀ h).ker : Set (FibreAut F)) := by
    refine Subgroup.isOpen_mono (H₁ := stabilizer F {⟨c, x₀⟩}) ?_ (isOpen_stabilizer F _)
    intro α hα
    have hα' : α.app c x₀ = x₀ := hα ⟨c, x₀⟩ (Finset.mem_singleton_self _)
    rw [MonoidHom.mem_ker]
    exact deckCharacterFun_eq c δ x₀ h (by rw [hα']; simp)
  exact continuous_of_continuousAt_one _
    (by rw [ContinuousAt, map_one]
        exact tendsto_nhds_of_eventually_eq (Filter.mem_of_superset
          (this.mem_nhds (Subgroup.one_mem _)) fun α hα => hα))

/-- The deck character is surjective as soon as every translation of the torsor is realized by
an automorphism of `F`. -/
lemma deckCharacter_surjective_iff :
    Function.Surjective (deckCharacter c δ x₀ h) ↔
      ∀ d : D, ∃ α : FibreAut F, α.app c x₀ = deckAct c δ d x₀ := by
  constructor
  · intro hs d
    obtain ⟨α, rfl⟩ := hs d
    exact ⟨α, (deckAct_deckCharacter c δ x₀ h α).symm⟩
  · intro hs d
    obtain ⟨α, hα⟩ := hs d
    exact ⟨α, deckCharacterFun_eq c δ x₀ h hα.symm⟩

end FibreAut

end TemperedFundamentalGroups
