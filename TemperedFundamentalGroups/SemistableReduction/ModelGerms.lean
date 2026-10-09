/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XHarmonic
import TemperedFundamentalGroups.SemistableReduction.SplitChart

/-!
# Germs of a model at a point via an affine chart (W8′, H6 glue)

Blueprint §9.7 (XL1, H6). For a model `c` with generic point `j : Spec L ⟶ c` and a point `y` in
an affine open `U` through which `j` factors, the germs of `c` at `y` (`ModelCode.germs`, the
functions regular at `y`) are the fractions `a / b` of sections over `U` with `b` not vanishing
at `y` (`germs_eq_of_isAffineOpen`): every section near `y` is, on a basic open of `U` around
`y`, a fraction `a / t ^ k`.

* `toL_res`: `toL` commutes with restriction;
* `top_le_preimage_basicOpen`: the generic point lies in `D(b)` when `toL b ≠ 0`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

variable {O : Type u} [CommRing O] {L : Type u} [Field L]
  {c : TemperedFundamentalGroups.ModelCode O} (j : Spec (CommRingCat.of L) ⟶ c.scheme)

/-- `toL` commutes with restriction of sections. -/
lemma toL_res {U V : c.scheme.Opens} (hVU : V ≤ U) (hV : ⊤ ≤ j ⁻¹ᵁ V) (hU : ⊤ ≤ j ⁻¹ᵁ U)
    (s : Γ(c.scheme, U)) :
    toL j hV ((c.scheme.presheaf.map (homOfLE hVU).op).hom s) = toL j hU s := by
  unfold toL
  rw [← CommRingCat.comp_apply (c.scheme.presheaf.map (homOfLE hVU).op) (j.appLE V ⊤ hV),
    Scheme.Hom.map_appLE]

/-- The generic point lies in `D(b)` if `b` does not vanish generically. -/
lemma top_le_preimage_basicOpen {U : c.scheme.Opens} (hU : ⊤ ≤ j ⁻¹ᵁ U) (b : Γ(c.scheme, U))
    (hb : toL j hU b ≠ 0) : ⊤ ≤ j ⁻¹ᵁ c.scheme.basicOpen b := by
  rw [Scheme.preimage_basicOpen]
  -- the image of `b` on `Spec L` is a unit
  have hunit : IsUnit ((j.appLE U ⊤ hU).hom b) := by
    have h1 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom ((j.appLE U ⊤ hU).hom b)) :=
      isUnit_iff_ne_zero.mpr hb
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at h2
  have h3 : (Spec (CommRingCat.of L)).basicOpen ((j.appLE U ⊤ hU).hom b) = ⊤ :=
    Scheme.basicOpen_of_isUnit _ hunit
  have h4 : (j.appLE U ⊤ hU).hom b = (Spec (CommRingCat.of L)).presheaf.map
      (homOfLE hU).op ((j.app U).hom b) := by
    rw [Scheme.Hom.appLE]; rfl
  rw [h4, Scheme.basicOpen_res] at h3
  exact le_of_eq_of_le h3.symm inf_le_right

/-- `toL` as a ring homomorphism. -/
noncomputable def toLHom {U : c.scheme.Opens} (h : ⊤ ≤ j ⁻¹ᵁ U) : Γ(c.scheme, U) →+* L :=
  (j.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom).hom

lemma toLHom_apply {U : c.scheme.Opens} (h : ⊤ ≤ j ⁻¹ᵁ U) (s : Γ(c.scheme, U)) :
    toLHom j h s = toL j h s := rfl

/-- **Germs via an affine chart**: the germs at `y` are the fractions `a / b` of sections over an
affine open `U ∋ y` (through which the generic point factors, `toL` injective) with `b` not
vanishing at `y`. -/
theorem germs_eq_of_isAffineOpen {U : c.scheme.Opens} (hU : IsAffineOpen U) {y : c.scheme}
    (hy : y ∈ U) (h : ⊤ ≤ j ⁻¹ᵁ U) (hinj : Function.Injective (toL j h)) :
    germs c j y = {f | ∃ a b : Γ(c.scheme, U), b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      f = toL j h a / toL j h b} := by
  have hne : ∀ b : Γ(c.scheme, U), b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal → toL j h b ≠ 0 :=
    fun b hb h0 ↦ hb (by
      rw [show b = 0 from hinj (by rw [h0, ← toLHom_apply, map_zero])]; exact zero_mem _)
  ext f
  constructor
  · rintro ⟨U', hy', h', s, rfl⟩
    obtain ⟨t, htU', hyt⟩ := hU.exists_basicOpen_le ⟨y, hy'⟩ hy
    have hyt' : t ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
      rw [mem_primeIdealOf_iff]; exact not_not.mpr hyt
    set V := c.scheme.basicOpen t
    have hVU : V ≤ U := c.scheme.basicOpen_le t
    have hV : ⊤ ≤ j ⁻¹ᵁ V := top_le_preimage_basicOpen j h t (hne t hyt')
    haveI := hU.isLocalization_basicOpen t
    let s' := (c.scheme.presheaf.map (homOfLE htU').op).hom s
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hak⟩ := IsLocalization.surj (Submonoid.powers t) s'
    simp only at hak
    have hres : ∀ r : Γ(c.scheme, U), toL j hV (algebraMap Γ(c.scheme, U) Γ(c.scheme, V) r) =
        toL j h r := fun r ↦ toL_res j hVU hV h r
    have e := congrArg (toLHom j hV) hak
    rw [map_mul, toLHom_apply, toLHom_apply, toLHom_apply, hres, hres,
      toL_res j htU' hV h'] at e
    refine ⟨a, t ^ k, fun hm ↦ hyt' (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hm), ?_⟩
    rw [eq_div_iff (hne _ fun hm ↦ hyt' (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hm))]
    exact e
  · rintro ⟨a, b, hb, rfl⟩
    have hyb : y ∈ c.scheme.basicOpen b := by
      rw [mem_primeIdealOf_iff] at hb; exact not_not.mp hb
    set V := c.scheme.basicOpen b
    have hVU : V ≤ U := c.scheme.basicOpen_le b
    have hV : ⊤ ≤ j ⁻¹ᵁ V := top_le_preimage_basicOpen j h b (hne b hb)
    haveI := hU.isLocalization_basicOpen b
    have hunit : IsUnit ((c.scheme.presheaf.map (homOfLE hVU).op).hom b) :=
      IsLocalization.Away.algebraMap_isUnit (S := Γ(c.scheme, V)) b
    refine ⟨V, hyb, hV, (c.scheme.presheaf.map (homOfLE hVU).op).hom a * ↑hunit.unit⁻¹, ?_⟩
    have e1 : toL j hV ((c.scheme.presheaf.map (homOfLE hVU).op).hom a * ↑hunit.unit⁻¹) =
        toL j hV ((c.scheme.presheaf.map (homOfLE hVU).op).hom a) * toL j hV ↑hunit.unit⁻¹ :=
      map_mul (toLHom j hV) _ _
    change toL j hV _ = _
    rw [e1, toL_res j hVU hV h, div_eq_mul_inv]
    congr 1
    have h1 : toLHom j hV ((c.scheme.presheaf.map (homOfLE hVU).op).hom b) *
        toLHom j hV ↑hunit.unit⁻¹ = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    rw [toLHom_apply, toL_res j hVU hV h] at h1
    exact (eq_inv_of_mul_eq_one_right h1)

end TemperedFundamentalGroups.SemistableReduction.ModelCode
