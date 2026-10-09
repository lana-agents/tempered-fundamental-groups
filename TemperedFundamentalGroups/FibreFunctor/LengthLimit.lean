/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.FibreFunctor.GaloisLimit
import TemperedFundamentalGroups.FibreFunctor.Character

/-!
# Deck characters from length functions (Blueprint §10.3.6, items 3–5, formal part)

Let `Φ : C ⥤ Type w` with a class `𝒢` of Galois objects satisfying (gal), (dom), (rig)
(`FibreFunctor/GaloisLimit.lean`), and `c : C` with a deck torsor `δ : D →* Aut c`, base point
`x₀`. Suppose every pointed Galois object `p = (G, g)` carries a **length** `len p : Φ G → ℕ`
such that

* the base point has length `0`;
* (finite) for every bound `L`, only finitely many `γ ∈ Φ G` have `len p γ ≤ L`;
* (monotone) pointed morphisms `p ⟶ q` do not increase lengths;
* (loop) if `(G, g)` lies over `(c, x₀)` (some `f : G ⟶ c` with `Φ f g = x₀`), some `γ` of length
  `≤ ℓ₀` lies over `δ(d) x₀`.

Then the sets `S_p = {γ : len p γ ≤ ℓ₀, Φ f γ = δ(d) x₀ for every pointed f : (G, g) ⟶ (c, x₀)}`
are finite, nonempty and mapped into each other, and König (K2,
`GaloisLimit.exists_fibreAut_of_finite_nonempty`) gives an automorphism `α` of `Φ` with
`deckCharacter α = d` (`GaloisLimit.exists_deckCharacter_eq_of_length`).

This is the formal skeleton of B5; the geometric content is the construction of the length
(the length of the reduced edge path in the universal covering of the special fibre) with the
four properties.
-/

universe w v u

open CategoryTheory Pi1.Orbifold Pi1.Orbifold.FibreAut

namespace TemperedFundamentalGroups

namespace GaloisLimit

variable {C : Type u} [Category.{v} C] {Φ : C ⥤ Type w} {𝒢 : ObjectProperty C}
  {D : Type*} [CommGroup D]

/-- **K1 + K2 with a deck torsor.** If finite nonempty subsets `S_p ⊆ Φ G`, mapped into each other
by pointed morphisms, consist of elements lying over `δ(d) x₀` along every pointed morphism to
`(c, x₀)`, then some automorphism of `Φ` has deck character `d`. -/
theorem exists_deckCharacter_eq_of_sets (hgal : IsGaloisClass Φ 𝒢) (hdom : IsDominating Φ 𝒢)
    (hrig : IsRigid Φ 𝒢) (c : C) (δ : D →* Aut c) (x₀ : Φ.obj c)
    (h : FibreAut.IsDeckTorsor (F := Φ) c δ) (d : D) (S : ∀ p : PtGal Φ 𝒢, Set (Φ.obj p.G))
    (hS : ∀ {p q : PtGal Φ 𝒢} (f : p ⟶ q), f.1 '' S p ⊆ S q) (hfin : ∀ p, (S p).Finite)
    (hne : ∀ p, (S p).Nonempty)
    (hSd : ∀ p : PtGal Φ 𝒢, ∀ γ ∈ S p, ∀ f : p.G ⟶ c, Φ.map f p.g = x₀ →
      Φ.map f γ = FibreAut.deckAct c δ d x₀) :
    ∃ α : FibreAut Φ, FibreAut.deckCharacter c δ x₀ h α = d := by
  obtain ⟨α, hα⟩ := exists_fibreAut_of_finite_nonempty S hS hgal hdom hrig hfin hne
  obtain ⟨p, f, hf⟩ := dom₁ hdom c x₀
  refine ⟨α, FibreAut.deckCharacterFun_eq c δ x₀ h ?_⟩
  rw [← hf, FibreAut.app_naturality, hSd p _ (hα p) f hf, hf]

/-- **B5, formal part: deck characters from a length function** (lengths in any preorder `α`,
e.g. `ℝ` for rational x-lengths): the base point has length `≤ ℓ₀`, only finitely many fibre
elements have length `≤ ℓ₀`, lengths do not increase along pointed morphisms, and pointed members
over `(c, x₀)` have an element of length `≤ ℓ₀` over `δ(d) x₀`. -/
theorem exists_deckCharacter_eq_of_length' {α : Type*} [Preorder α] (hgal : IsGaloisClass Φ 𝒢)
    (hdom : IsDominating Φ 𝒢) (hrig : IsRigid Φ 𝒢) (c : C) (δ : D →* Aut c) (x₀ : Φ.obj c)
    (h : FibreAut.IsDeckTorsor (F := Φ) c δ) (d : D) (len : ∀ p : PtGal Φ 𝒢, Φ.obj p.G → α)
    (ℓ₀ : α) (hzero : ∀ p, len p p.g ≤ ℓ₀)
    (hfin : ∀ p, {γ | len p γ ≤ ℓ₀}.Finite)
    (hmono : ∀ {p q : PtGal Φ 𝒢} (f : p ⟶ q) (γ : Φ.obj p.G), len q (f.1 γ) ≤ len p γ)
    (hloop : ∀ p : PtGal Φ 𝒢, ∀ f : p.G ⟶ c, Φ.map f p.g = x₀ →
      ∃ γ, len p γ ≤ ℓ₀ ∧ Φ.map f γ = FibreAut.deckAct c δ d x₀) :
    ∃ α : FibreAut Φ, FibreAut.deckCharacter c δ x₀ h α = d := by
  classical
  let S : ∀ p : PtGal Φ 𝒢, Set (Φ.obj p.G) := fun p =>
    {γ | len p γ ≤ ℓ₀ ∧ ∀ f : p.G ⟶ c, Φ.map f p.g = x₀ → Φ.map f γ = FibreAut.deckAct c δ d x₀}
  refine exists_deckCharacter_eq_of_sets hgal hdom hrig c δ x₀ h d S ?_ (fun p =>
    (hfin p).subset fun γ hγ => hγ.1) (fun p => ?_) (fun p γ hγ f hf => hγ.2 f hf)
  · rintro p q φ _ ⟨γ, ⟨hγl, hγd⟩, rfl⟩
    obtain ⟨⟨a, ha⟩, hpt⟩ := φ.2
    refine ⟨(hmono φ γ).trans hγl, fun g hg => ?_⟩
    have h₁ : Φ.map (a ≫ g) p.g = x₀ := by
      rw [Functor.map_comp_apply, ha, hpt, hg]
    rw [← hγd _ h₁, Functor.map_comp_apply, ha]
  · by_cases hc : ∃ f : p.G ⟶ c, Φ.map f p.g = x₀
    · obtain ⟨f, hf⟩ := hc
      obtain ⟨γ, hγl, hγd⟩ := hloop p f hf
      refine ⟨γ, hγl, fun f' hf' => ?_⟩
      rw [← hγd]
      rw [hrig _ p.mem f' f p.g (hf'.trans hf.symm)]
    · exact ⟨p.g, hzero p, fun f hf => (hc ⟨f, hf⟩).elim⟩

/-- **B5, formal part: deck characters from a length function** (natural lengths). -/
theorem exists_deckCharacter_eq_of_length (hgal : IsGaloisClass Φ 𝒢) (hdom : IsDominating Φ 𝒢)
    (hrig : IsRigid Φ 𝒢) (c : C) (δ : D →* Aut c) (x₀ : Φ.obj c)
    (h : FibreAut.IsDeckTorsor (F := Φ) c δ) (d : D) (len : ∀ p : PtGal Φ 𝒢, Φ.obj p.G → ℕ)
    (ℓ₀ : ℕ) (hzero : ∀ p, len p p.g = 0)
    (hfin : ∀ p (L : ℕ), {γ | len p γ ≤ L}.Finite)
    (hmono : ∀ {p q : PtGal Φ 𝒢} (f : p ⟶ q) (γ : Φ.obj p.G), len q (f.1 γ) ≤ len p γ)
    (hloop : ∀ p : PtGal Φ 𝒢, ∀ f : p.G ⟶ c, Φ.map f p.g = x₀ →
      ∃ γ, len p γ ≤ ℓ₀ ∧ Φ.map f γ = FibreAut.deckAct c δ d x₀) :
    ∃ α : FibreAut Φ, FibreAut.deckCharacter c δ x₀ h α = d :=
  exists_deckCharacter_eq_of_length' hgal hdom hrig c δ x₀ h d len ℓ₀
    (fun p => (hzero p).le.trans (Nat.zero_le _)) (fun p => hfin p ℓ₀) hmono hloop

/-- **The Tate loop from lifting** (formal part): if fibre elements lift along pointed
morphisms without increasing length (`hlift`, path lifting) and lengths do not increase along
pointed morphisms, then one pointed member `p₀` over `(c, x₀)` with an element `γ₀` over
`δ(d) x₀` gives, in every pointed member over `(c, x₀)`, an element over `δ(d) x₀` of length
at most that of `γ₀` (domination by a common pointed member, lifting, pushing down; the
morphisms to `c` agree by rigidity). -/
theorem exists_loop_of_lift {α : Type*} [Preorder α] (hdom : IsDominating Φ 𝒢)
    (hrig : IsRigid Φ 𝒢) (c : C) (δ : D →* Aut c) (x₀ : Φ.obj c) (d : D)
    (len : ∀ p : PtGal Φ 𝒢, Φ.obj p.G → α)
    (hmono : ∀ {p q : PtGal Φ 𝒢} (f : p ⟶ q) (γ : Φ.obj p.G), len q (f.1 γ) ≤ len p γ)
    (hlift : ∀ {p q : PtGal Φ 𝒢} (f : p ⟶ q) (γ' : Φ.obj q.G),
      ∃ γ, f.1 γ = γ' ∧ len p γ ≤ len q γ')
    (p₀ : PtGal Φ 𝒢) (f₀ : p₀.G ⟶ c) (hf₀ : Φ.map f₀ p₀.g = x₀) (γ₀ : Φ.obj p₀.G)
    (hγ₀ : Φ.map f₀ γ₀ = FibreAut.deckAct c δ d x₀) :
    ∀ p : PtGal Φ 𝒢, ∀ f : p.G ⟶ c, Φ.map f p.g = x₀ →
      ∃ γ, len p γ ≤ len p₀ γ₀ ∧ Φ.map f γ = FibreAut.deckAct c δ d x₀ := by
  intro p f hf
  obtain ⟨G, hG, g, m, hm⟩ := hdom 2 ![⟨p.G, p.g⟩, ⟨p₀.G, p₀.g⟩]
  let r : PtGal Φ 𝒢 := ⟨G, hG, g⟩
  let a : r ⟶ p := ptHom (m 0) (hm 0)
  let b : r ⟶ p₀ := ptHom (m 1) (hm 1)
  obtain ⟨γr, hγr, hlen⟩ := hlift b γ₀
  refine ⟨a.1 γr, (hmono a γr).trans hlen, ?_⟩
  have h₁ : Φ.map (m 0 ≫ f) g = Φ.map (m 1 ≫ f₀) g := by
    rw [Functor.map_comp_apply, Functor.map_comp_apply, hm 0, hm 1]
    exact hf.trans hf₀.symm
  have hab := hrig G hG _ _ g h₁
  have h₂ : Φ.map (m 0 ≫ f) γr = Φ.map (m 1 ≫ f₀) γr := by rw [hab]
  rw [Functor.map_comp_apply, Functor.map_comp_apply] at h₂
  refine h₂.trans ?_
  have h₃ : Φ.map (m 1) γr = γ₀ := hγr
  rw [h₃]
  exact hγ₀

end GaloisLimit

end TemperedFundamentalGroups
