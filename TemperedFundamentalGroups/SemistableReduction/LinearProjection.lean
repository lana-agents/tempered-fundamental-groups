/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Models.Projective

/-!
# Linear projections `ℙᵐ ⇢ ℙ¹` on basic opens (Blueprint §12.8, M2 step 4(c))

For linear forms `ℓ₀, ℓ₁` in `O[x₀, …, xₘ]`, the graded homomorphism
`linHom ℓ : O[y₀, y₁] → O[x₀, …, xₘ]`, `y_j ↦ ℓ_j`, defines the linear projection
`[ℓ₀ : ℓ₁] : ℙᵐ_O ⇢ ℙ¹_O`, a morphism on `D₊(ℓ₀) ∪ D₊(ℓ₁)` (Mathlib's `Proj.map` needs the
image of the irrelevant ideal to generate it, i.e. no centre). Here it is given chart by chart:

* `chartMap ℓ s : D₊(φ s) ⟶ ℙ¹_O` for homogeneous `s ∈ O[y₀, y₁]` of positive degree:
  `D₊(φ s) ≅ Spec (O[x]_{(φ s)})₀ → Spec (O[y]_{(s)})₀ ⊆ ℙ¹_O`, the second map being
  `Spec` of `HomogeneousLocalization.Away.map`;
* `homOfLE_chartMap`: for `x = s * g`, the restriction of `chartMap ℓ s` to `D₊(φ x)` is
  `chartMap ℓ x`; hence the charts agree on overlaps (`chartMap_compat`);
* `chartMap_toSpec`: the charts lie over `Spec O`.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace SemistableReduction

namespace LinearProjection

open TemperedFundamentalGroups

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] {m : ℕ}

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

/-- **The graded homomorphism `O[y₀, y₁] → O[x₀, …, xₘ]`, `y_j ↦ ℓ_j`** for linear forms
`ℓ_j`. -/
noncomputable def linHom (ℓ : Fin (1 + 1) → MvPolynomial (Fin (m + 1)) O)
    (hℓ : ∀ j, ℓ j ∈ (𝒜 m) 1) : (𝒜 1) →+*ᵍ (𝒜 m) where
  toRingHom := (aeval ℓ).toRingHom
  map_mem := by
    intro i x hx
    have hx' : x.IsHomogeneous i := (mem_homogeneousSubmodule _ _).1 hx
    have := hx'.aeval ℓ (fun j ↦ (mem_homogeneousSubmodule _ _).1 (hℓ j))
    rw [one_mul] at this
    exact (mem_homogeneousSubmodule _ _).2 this

variable (ℓ : Fin (1 + 1) → MvPolynomial (Fin (m + 1)) O)
  (hℓ : ∀ j, ℓ j ∈ MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O 1)

@[simp]
lemma linHom_apply (x : MvPolynomial (Fin (1 + 1)) O) : linHom ℓ hℓ x = aeval ℓ x := rfl

lemma linHom_X (j : Fin (1 + 1)) : linHom ℓ hℓ (X j) = ℓ j := by simp

/-- **The projection on the chart `D₊(φ s)`**: `D₊(φ s) ≅ Spec (O[x]_{(φ s)})₀ ⟶
Spec (O[y]_{(s)})₀ ⊆ ℙ¹_O`. -/
noncomputable def chartMap (s : MvPolynomial (Fin (1 + 1)) O) {d : ℕ} (hs : s ∈ (𝒜 1) d)
    (hd : 0 < d) :
    (Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s)).toScheme ⟶ Proj (𝒜 1) :=
  (Proj.basicOpenIsoSpec (𝒜 m) (linHom ℓ hℓ s) ((linHom ℓ hℓ).map_mem hs) hd).hom ≫
    Spec.map (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) s)) ≫ Proj.awayι (𝒜 1) s hs hd

/-- The ring identity behind `homOfLE_chartMap`. -/
lemma awayMap_comp_awayMap {s g x : MvPolynomial (Fin (1 + 1)) O} {d e : ℕ} (hs : s ∈ (𝒜 1) d)
    (hg : g ∈ (𝒜 1) e) (hx : x = s * g) :
    (awayMap (𝒜 m) ((linHom ℓ hℓ).map_mem hg)
        (show linHom ℓ hℓ x = linHom ℓ hℓ s * linHom ℓ hℓ g by rw [hx, map_mul])).comp
      (Away.map (linHom ℓ hℓ) s) =
    (Away.map (linHom ℓ hℓ) x).comp (awayMap (𝒜 1) hg hx) := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (𝒜 1) hs z
  simp only [RingHom.coe_comp, Function.comp_apply, Away.map_mk, awayMap_mk, Away.val_mk,
    map_mul, map_pow]
  rfl

/-- **Restriction of a chart of the projection to a smaller basic open.** -/
lemma homOfLE_chartMap {s g x : MvPolynomial (Fin (1 + 1)) O} {d e : ℕ} (hs : s ∈ (𝒜 1) d)
    (hd : 0 < d) (hg : g ∈ (𝒜 1) e) (hx : x = s * g) (hxd : x ∈ (𝒜 1) (d + e))
    (hle : Proj.basicOpen (𝒜 m) (linHom ℓ hℓ x) ≤ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s)) :
    (Proj (𝒜 m)).homOfLE hle ≫ chartMap ℓ hℓ s hs hd =
      chartMap ℓ hℓ x hxd (hd.trans_le (Nat.le_add_right d e)) := by
  have hx' : linHom ℓ hℓ x = linHom ℓ hℓ s * linHom ℓ hℓ g := by rw [hx, map_mul]
  have key := Proj.basicOpenToSpec_SpecMap_awayMap (𝒜 m)
    ((linHom ℓ hℓ).map_mem hg) hx' (f := linHom ℓ hℓ s)
  simp only [chartMap, Proj.basicOpenIsoSpec_hom]
  change (Proj (𝒜 m)).homOfLE hle ≫ _ = _
  rw [← Category.assoc ((Proj (𝒜 m)).homOfLE hle), ← key, Category.assoc,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    awayMap_comp_awayMap ℓ hℓ hs hg hx, CommRingCat.ofHom_comp, Spec.map_comp_assoc,
    Proj.SpecMap_awayMap_awayι (𝒜 1) hs hd hg hx]

/-- **The charts of the projection agree on overlaps.** -/
lemma chartMap_compat {s g x : MvPolynomial (Fin (1 + 1)) O} {d : ℕ} (hs : s ∈ (𝒜 1) d)
    (hg : g ∈ (𝒜 1) d) (hd : 0 < d) (hx : x = s * g) (hxd : x ∈ (𝒜 1) (d + d))
    (hle₁ : Proj.basicOpen (𝒜 m) (linHom ℓ hℓ x) ≤ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s))
    (hle₂ : Proj.basicOpen (𝒜 m) (linHom ℓ hℓ x) ≤ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ g)) :
    (Proj (𝒜 m)).homOfLE hle₁ ≫ chartMap ℓ hℓ s hs hd =
      (Proj (𝒜 m)).homOfLE hle₂ ≫ chartMap ℓ hℓ g hg hd := by
  rw [homOfLE_chartMap ℓ hℓ hs hd hg hx hxd,
    homOfLE_chartMap ℓ hℓ hg hd hs (hx.trans (mul_comm _ _)) hxd]

/-- **The charts of the projection lie over `Spec O`.** -/
lemma chartMap_toSpec (s : MvPolynomial (Fin (1 + 1)) O) {d : ℕ} (hs : s ∈ (𝒜 1) d)
    (hd : 0 < d) :
    chartMap ℓ hℓ s hs hd ≫ projSpace.toSpec O 1 =
      (Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s)).ι ≫ projSpace.toSpec O m := by
  have hι : (Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s)).ι =
      (Proj.basicOpenIsoSpec (𝒜 m) (linHom ℓ hℓ s) ((linHom ℓ hℓ).map_mem hs) hd).hom ≫
        Proj.awayι (𝒜 m) (linHom ℓ hℓ s) ((linHom ℓ hℓ).map_mem hs) hd := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  rw [hι]
  change chartMap ℓ hℓ s hs hd ≫ Proj.toSpecZero (𝒜 1) ≫ _ =
    _ ≫ Proj.toSpecZero (𝒜 m) ≫ _
  simp only [chartMap, Category.assoc]
  rw [Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc]
  congr 1
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext o
  change val (Away.map (linHom ℓ hℓ) s (fromZeroRingHom (𝒜 1) _ (algebraMap O _ o))) =
    val (fromZeroRingHom (𝒜 m) _ (algebraMap O _ o))
  simp only [fromZeroRingHom, Away.map, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    HomogeneousLocalization.map_mk, val_mk]
  simp [MvPolynomial.algebraMap_eq]

end LinearProjection

end SemistableReduction
