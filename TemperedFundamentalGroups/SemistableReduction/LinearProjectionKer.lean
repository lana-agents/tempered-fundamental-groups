/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.ModelProjection

/-!
# The kernel of the restriction to the charts of a linear projection

For a reduced closed subscheme `ι : Z ⟶ ℙᵐ_O` with underlying set `V(F)` (`F` homogeneous of
positive degree `e`) and linear forms `ℓ₀, ℓ₁`, the restriction of homogeneous fractions to the
chart `V_k = ι⁻¹ D₊(ℓ_k)` (`LinearProjection.secRes`, surjective) has kernel the radical of
`F / ℓ_k ^ e` (**`LinearProjection.ker_secRes`**), so `Γ(V_k) ≅ (O[x]_{(ℓ_k)})₀ ⧸ √(F / ℓ_k ^ e)`.

Also: the closed subscheme of a vanishing ideal is reduced
(**`Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`**).
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **The closed subscheme defined by a vanishing ideal is reduced.** -/
instance isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  have (U : X.affineOpens) : IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U) := by
    have : _root_.IsReduced (Γ(X, U) ⧸ (vanishingIdeal Z).ideal U) := by
      rw [vanishingIdeal_ideal]
      exact (Ideal.isRadical_iff_quotient_reduced _).1 (PrimeSpectrum.isRadical_vanishingIdeal _)
    exact inferInstanceAs (IsReduced (Spec (.of (Γ(X, U) ⧸ (vanishingIdeal Z).ideal U))))
  exact IsReduced.of_openCover (X := (vanishingIdeal Z).subscheme)
    (vanishingIdeal Z).subschemeCover.openCover

end AlgebraicGeometry.Scheme.IdealSheafData

namespace SemistableReduction

namespace LinearProjection

open TemperedFundamentalGroups

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] {m : ℕ}

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

variable (ℓ : Fin (1 + 1) → MvPolynomial (Fin (m + 1)) O)
  (hℓ : ∀ j, ℓ j ∈ MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O 1)
  {Z : Scheme.{u}} (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O))

/-- The chart `V_k ⟶ Spec (O[x]_{(ℓ_k)})₀` followed by `Spec (O[x]_{(ℓ_k)})₀ ⟶ ℙᵐ` is `ι`. -/
lemma awayι_chartSpec (k : Fin (1 + 1)) (x : V ℓ hℓ ι k) :
    Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k)) one_pos
      (chartSpec ℓ hℓ ι k x) = ι x.1 := by
  rw [← Scheme.Hom.comp_apply, chartSpec, Category.assoc, ← Proj.basicOpenIsoSpec_inv_ι,
    Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
  rfl

/-- A restricted fraction `σ_k a` is invertible at `x` iff `a` is not in the prime
`chartSpec x`. -/
lemma mem_basicOpen_secRes_iff (k : Fin (1 + 1)) (a : Away (𝒜 m) (linHom ℓ hℓ (X k)))
    (x : V ℓ hℓ ι k) :
    x ∈ (V ℓ hℓ ι k).toScheme.basicOpen (secRes ℓ hℓ ι k a) ↔
      a ∉ (chartSpec ℓ hℓ ι k x).asIdeal := by
  have h : (V ℓ hℓ ι k).toScheme.basicOpen (secRes ℓ hℓ ι k a) =
      chartSpec ℓ hℓ ι k ⁻¹ᵁ (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv a) := by
    rw [Scheme.preimage_basicOpen_top]
    rfl
  rw [h, basicOpen_eq_of_affine]
  rfl

/-- **The kernel of the restriction to a chart.** Let `ι : Z ⟶ ℙᵐ_O` be a closed immersion of a
reduced scheme with image `V(F)`, `F` homogeneous of positive degree `e`. Then the kernel of
`σ_k : (O[x]_{(ℓ_k)})₀ → Γ(V_k)` is the radical of `F / ℓ_k ^ e`. -/
theorem ker_secRes [IsClosedImmersion ι] [IsReduced Z] (k : Fin (1 + 1))
    {F : MvPolynomial (Fin (m + 1)) O} {e : ℕ} (hF : F ∈ (𝒜 m) e) (he : 0 < e)
    (hZ : Set.range ι = {y | F ∈ y.asHomogeneousIdeal}) :
    RingHom.ker (secRes ℓ hℓ ι k) =
      (Ideal.span {Away.isLocalizationElem ((linHom ℓ hℓ).map_mem (X_mem' k)) hF}).radical := by
  apply le_antisymm
  · intro a ha
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hP, hPp⟩
    let P' : Spec (CommRingCat.of (Away (𝒜 m) (linHom ℓ hℓ (X k)))) := ⟨P, hPp⟩
    have hFy : F ∈ (Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k))
        one_pos P').asHomogeneousIdeal := by
      by_contra hn
      have h' : P' ∈ Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k))
          one_pos ⁻¹ᵁ Proj.basicOpen (𝒜 m) F := (Proj.mem_basicOpen _ _ _).2 hn
      rw [Proj.awayι_preimage_basicOpen (𝒜 m) _ one_pos hF he] at h'
      exact h' (hP (Ideal.mem_span_singleton_self _))
    have hy : Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k)) one_pos P'
        ∈ Set.range ι := by rw [hZ]; exact hFy
    obtain ⟨z, hz⟩ := hy
    have hzV : z ∈ V ℓ hℓ ι k := by
      have h2 : Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k)) one_pos P'
          ∈ (Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k))
            one_pos).opensRange := ⟨P', rfl⟩
      rw [Proj.opensRange_awayι, ← hz] at h2
      exact h2
    have hx : chartSpec ℓ hℓ ι k ⟨z, hzV⟩ = P' :=
      (Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k))
        one_pos).isOpenEmbedding.injective (by rw [awayι_chartSpec, hz])
    by_contra haP
    have h' := (mem_basicOpen_secRes_iff ℓ hℓ ι k a ⟨z, hzV⟩).2 (by rw [hx]; exact haP)
    rw [RingHom.mem_ker.1 ha, Scheme.basicOpen_zero] at h'
    exact h'
  · rintro a ⟨n, hn⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hn
    have hFZ : ∀ z : Z, F ∈ (ι z).asHomogeneousIdeal := fun z ↦
      (show ι z ∈ {y | F ∈ y.asHomogeneousIdeal} from hZ ▸ ⟨z, rfl⟩)
    have hnil : IsNilpotent (secRes ℓ hℓ ι k a) := by
      refine ⟨n, ?_⟩
      rw [← map_pow, hc, map_mul,
        (isNilpotent_secRes ℓ hℓ ι k hF he hFZ).eq_zero, zero_mul]
    exact hnil.eq_zero

/-! ### Ring homomorphisms out of the charts -/

/-- **Ring homomorphisms out of a chart `(O[x]_{(ℓ_k)})₀` are determined by the constants and the
coordinate functions `x_i / ℓ_k`.** -/
lemma awayHom_ext {T : Type*} [CommRing T] (k : Fin (1 + 1))
    {φ ψ : Away (𝒜 m) (linHom ℓ hℓ (X k)) →+* T}
    (h0 : ∀ o : O, φ (fromZeroRingHom (𝒜 m) _ (algebraMap O _ o)) =
      ψ (fromZeroRingHom (𝒜 m) _ (algebraMap O _ o)))
    (h : ∀ i, φ (coordFrac ℓ hℓ k i) = ψ (coordFrac ℓ hℓ k i)) : φ = ψ := by
  let S : Subalgebra ((𝒜 m) 0) (Away (𝒜 m) (linHom ℓ hℓ (X k))) :=
    { carrier := {b | φ b = ψ b}
      mul_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
        rw [ha, hb]
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        rw [ha, hb]
      algebraMap_mem' := fun r ↦ by
        obtain ⟨o, rfl⟩ := (bijective_algebraMap_projSpace O m).2 r
        exact h0 o }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← Away.adjoin_mk_prod_pow_eq_top ((linHom ℓ hℓ).map_mem (X_mem' k))
      (Fin (m + 1)) X (adjoin_X_eq_top (O := O) (m := m)) (fun _ ↦ 1)
      (fun i ↦ (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X O i)), Algebra.adjoin_le_iff]
    rintro _ ⟨a, ai, hai, -, rfl⟩
    change φ _ = ψ _
    rw [mk_prod_eq ℓ hℓ k a ai hai, map_prod, map_prod]
    simp only [map_pow, h]
  ext b
  exact (show b ∈ S from hS ▸ Algebra.mem_top)

/-- **Evaluation of a chart at a point** `c` of an `O`-algebra `T` with `s(c) = 1`:
`(O[x]_{(s)})₀ → T`, `a / s ^ n ↦ a(c)`. -/
noncomputable def awayEval {T : Type*} [CommRing T] [Algebra O T] (c : Fin (m + 1) → T)
    (s : MvPolynomial (Fin (m + 1)) O) (hs : aeval c s = 1) : Away (𝒜 m) s →+* T :=
  (Localization.awayLift (aeval c).toRingHom s (by
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs]; exact isUnit_one)).comp
    (algebraMap _ (Localization.Away s))

lemma awayEval_mk {T : Type*} [CommRing T] [Algebra O T] (c : Fin (m + 1) → T)
    {s : MvPolynomial (Fin (m + 1)) O} (hs : aeval c s = 1) {d : ℕ} (hsd : s ∈ (𝒜 m) d) (n : ℕ)
    (a : MvPolynomial (Fin (m + 1)) O) (ha : a ∈ (𝒜 m) (n • d)) :
    awayEval c s hs (Away.mk (𝒜 m) hsd n a ha) = aeval c a := by
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.mk_eq_mk', Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec]
  simp [hs]

lemma awayEval_fromZero {T : Type*} [CommRing T] [Algebra O T] (c : Fin (m + 1) → T)
    {s : MvPolynomial (Fin (m + 1)) O} (hs : aeval c s = 1) (o : O) :
    awayEval c s hs (fromZeroRingHom (𝒜 m) _ (algebraMap O ((𝒜 m) 0) o)) = algebraMap O T o := by
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, val_fromZero]
  rw [Localization.awayLift, IsLocalization.Away.lift, IsLocalization.lift_eq]
  simp

lemma awayEval_coordFrac {T : Type*} [CommRing T] [Algebra O T] (c : Fin (m + 1) → T)
    (k : Fin (1 + 1)) (hs : aeval c (linHom ℓ hℓ (X k)) = 1) (i : Fin (m + 1)) :
    awayEval c _ hs (coordFrac ℓ hℓ k i) = c i := by
  rw [awayEval_mk, aeval_X]

end LinearProjection

end SemistableReduction
