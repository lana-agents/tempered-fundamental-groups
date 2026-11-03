/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.Group

/-!
# Stabilisers of ideals under a group action by ring endomorphisms (generic; MR13 B4′)

For `φ : G → (C →+* C)` with `φ 1 = id` and `φ (g h) = φ g ∘ φ h` (e.g. the action of the Galois
group of a special cover on `C0`):

* **`StabIdeal.stab φ 𝔪`**: the subgroup `{g | 𝔪.comap (φ g) = 𝔪}`;
* **`StabIdeal.conj_mem_stab`**: `s ∈ Stab(𝔪) ⇒ h s h⁻¹ ∈ Stab(𝔪.comap (φ h⁻¹))`;
* **`StabIdeal.isMaximal_comap`**: translates of maximal ideals are maximal.
-/

namespace SemistableReduction

namespace StabIdeal

variable {C : Type*} [CommRing C] {G : Type*} [Group G] (φ : G → C →+* C)
  (hone : ∀ x, φ 1 x = x) (hmul : ∀ g h x, φ (g * h) x = φ g (φ h x))

include hmul in
lemma comap_comap (𝔪 : Ideal C) (g h : G) :
    (𝔪.comap (φ g)).comap (φ h) = 𝔪.comap (φ (g * h)) := by
  rw [Ideal.comap_comap]
  congr 1
  exact (RingHom.ext fun x ↦ hmul g h x).symm

include hone in
lemma comap_one (𝔪 : Ideal C) : 𝔪.comap (φ 1) = 𝔪 := by
  rw [show φ 1 = RingHom.id C from RingHom.ext hone]
  exact Ideal.comap_id 𝔪

/-- **The stabiliser of an ideal** under the action `φ`. -/
def stab (𝔪 : Ideal C) : Subgroup G where
  carrier := {g | 𝔪.comap (φ g) = 𝔪}
  one_mem' := comap_one φ hone 𝔪
  mul_mem' {g h} hg hh := by
    change 𝔪.comap (φ (g * h)) = 𝔪
    have hg' : 𝔪.comap (φ g) = 𝔪 := hg
    have hh' : 𝔪.comap (φ h) = 𝔪 := hh
    rw [← comap_comap φ hmul, hg', hh']
  inv_mem' {g} hg := by
    change 𝔪.comap (φ g⁻¹) = 𝔪
    have hg' : 𝔪.comap (φ g) = 𝔪 := hg
    conv_lhs => rw [← hg']
    rw [comap_comap φ hmul, mul_inv_cancel, comap_one φ hone]

lemma mem_stab (𝔪 : Ideal C) (g : G) : g ∈ stab φ hone hmul 𝔪 ↔ 𝔪.comap (φ g) = 𝔪 :=
  Iff.rfl

/-- **Conjugation of stabilisers**: `s ∈ Stab(𝔪) ⇒ h s h⁻¹ ∈ Stab(𝔪.comap (φ h⁻¹))`. -/
lemma conj_mem_stab (𝔪 : Ideal C) {s : G} (hs : s ∈ stab φ hone hmul 𝔪) (h : G) :
    h * s * h⁻¹ ∈ stab φ hone hmul (𝔪.comap (φ h⁻¹)) := by
  rw [mem_stab] at hs ⊢
  rw [comap_comap φ hmul, show h⁻¹ * (h * s * h⁻¹) = s * h⁻¹ by group,
    ← comap_comap φ hmul, hs]

include hone hmul in
/-- The translate of a maximal ideal is maximal. -/
lemma isMaximal_comap (𝔪 : Ideal C) [𝔪.IsMaximal] (g : G) : (𝔪.comap (φ g)).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ fun z ↦ ⟨φ g⁻¹ z, by
    rw [← hmul, mul_inv_cancel, hone]⟩

end StabIdeal

end SemistableReduction
