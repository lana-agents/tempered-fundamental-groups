/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateAffineGlue

/-!
# The glued generic fibre is a normalization (G6, generic part)

In the setting of `TemperedFundamentalGroups.SemistableReduction.TateAffineGlue`, let `L` be a
field with an `A[1/ϖ]`-algebra structure and let `j₀ : B₀ → L`, `j₁ : B₁ → L`, `j₀₁ : B₀₁ → L`
be injective ring maps compatible with the restrictions `r₀`, `r₁`, such that `B₀`, `B₁` are the
integral closures of `T0`, `T1` in `L` (via `j₀ ∘ ι₀`, `j₁ ∘ ι₁`), and such that the
`A[1/ϖ]`-algebra structure of `L` factors through `T0[1/(ϖ z)]`. Then:

* **`TateAffine.jA`**, **`jB`**, **`jAB`**: the induced injective maps `Ba → L`, `Bb → L`,
  `Bab → L` (**`jA_injective`**, **`jB_injective`**, **`jAB_injective`**), compatible with
  `rhoA`, `rhoB` (**`jAB_rhoA`**, **`jAB_rhoB`**);
* **`TateAffine.gluedKToL`**: the injective (**`gluedKToL_injective`**) `A[1/ϖ]`-algebra map
  from the glued algebra `gluedK` to `L`;
* **`TateAffine.range_gluedKToL`**: if `B₀`, `B₁` are finite over `T0`, `T1`, its image is the
  integral closure of `A[1/ϖ]` in `L`;
* **`TateAffine.gluedKEquiv`**: hence `gluedK ≃ₐ[A[1/ϖ]] integralClosure A[1/ϖ] L`;
* **`TateAffine.gluedKNorm`**: the same, as the `Prop` **`TateAffine.GluedKNorm`** (whose
  statement contains no `letI`, for use at the concrete Tate types).

The generic inputs are **`TateAffine.injective_of_isLocalization`** (a map out of a localization
extending an injective map is injective) and **`TateAffine.mem_range_of_isIntegralElem`** (the
localization of an integral closure is the integral closure of the localization,
via `IsIntegral.exists_multiple_integral_of_isLocalization`).
-/

universe u

namespace SemistableReduction

namespace TateAffine

open TateTwoChart TemperedFundamentalGroups.TateNormal

noncomputable section

section Generic

variable {R B Bₘ L : Type u} [CommRing R] [CommRing B] [CommRing Bₘ] [CommRing L]

/-- A ring map out of a localization of `B` that extends an injective map is injective. -/
lemma injective_of_isLocalization (M : Submonoid B) [Algebra B Bₘ] [IsLocalization M Bₘ]
    (jₘ : Bₘ →+* L) {j : B →+* L} (hjm : ∀ b, jₘ (algebraMap B Bₘ b) = j b)
    (hj : Function.Injective j) : Function.Injective jₘ := by
  refine (injective_iff_map_eq_zero jₘ).2 fun z hz ↦ ?_
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  have h := congrArg jₘ (IsLocalization.mk'_spec Bₘ b m)
  rw [map_mul, hz, zero_mul, hjm] at h
  have hb : b = 0 := hj (h.symm.trans (map_zero j).symm)
  rw [hb]
  exact IsLocalization.mk'_zero m

/-- An element integral over `R[1/s]` lies in the image of `B[1/ι(s)]` if every element
integral over `R` lies in the image of `B`. -/
lemma mem_range_of_isIntegralElem (s : R) {Rₘ : Type u} [CommRing Rₘ] [Algebra R Rₘ]
    [IsLocalization.Away s Rₘ] (ι : R →+* B) (j : B →+* L) [Algebra B Bₘ]
    [IsLocalization.Away (ι s) Bₘ] (jₘ : Bₘ →+* L) (hjm : ∀ b, jₘ (algebraMap B Bₘ b) = j b)
    (ψ : Rₘ →+* L) (hψ : ∀ a, ψ (algebraMap R Rₘ a) = j (ι a))
    (hcl : ∀ x : L, (j.comp ι).IsIntegralElem x → x ∈ j.range) {x : L}
    (hx : ψ.IsIntegralElem x) : x ∈ jₘ.range := by
  letI : Algebra R L := (j.comp ι).toAlgebra
  letI : Algebra Rₘ L := ψ.toAlgebra
  haveI : IsScalarTower R Rₘ L := IsScalarTower.of_algebraMap_eq fun a ↦ (hψ a).symm
  obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers s) x hx
  obtain ⟨b, hb⟩ := hcl _ hm
  have hb' : j b = j (ι s ^ n) * x := by
    rw [hb, Submonoid.smul_def, Algebra.smul_def, map_pow, map_pow]
    rfl
  let m : Submonoid.powers (ι s) := ⟨ι s ^ n, n, rfl⟩
  have hu : IsUnit (j (ι s ^ n)) := by
    have h := ((IsLocalization.Away.algebraMap_isUnit (S := Bₘ) (ι s)).pow n).map jₘ
    rwa [← map_pow, hjm] at h
  refine ⟨IsLocalization.mk' Bₘ b m, (hu.mul_left_inj).1 ?_⟩
  have h := congrArg jₘ (IsLocalization.mk'_spec Bₘ b m)
  rw [map_mul, hjm, hjm, hb'] at h
  rw [h, mul_comm]

/-- If `x` is integral via `ψ ∘ f`, it is integral via `ψ`. -/
lemma isIntegralElem_of_comp {S : Type u} [CommRing S] (f : R →+* S) (ψ : S →+* L) {x : L}
    (h : (ψ.comp f).IsIntegralElem x) : ψ.IsIntegralElem x := by
  obtain ⟨p, hp, he⟩ := h
  exact ⟨p.map f, hp.map f, by rwa [Polynomial.eval₂_map]⟩

end Generic

variable {O : Type u} [CommRing O] (b₄ : O) {π b₆ t κ ϖ : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π ∣ ϖ ^ m)
  {B0 B1 B01 : Type u} [CommRing B0] [CommRing B1] [CommRing B01]
  {ι0 : T0 π b₄ t κ →+* B0} {ι1 : T1 π b₄ t κ →+* B1} {ι01 : T01 π b₄ t κ →+* B01}
  {r0 : B0 →+* B01} {r1 : B1 →+* B01}
  (hc0 : r0.comp ι0 = ι01.comp (rho0 π b₄ t κ).toRingHom)
  (hc1 : r1.comp ι1 = ι01.comp (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ)))
  (hloc0 : letI := r0.toAlgebra; IsLocalization.Away (ι0 (h0 π b₄ t κ)) B01)
  (hloc1 : letI := r1.toAlgebra; IsLocalization.Away (ι1 (h1 π b₄ t κ)) B01)
  {L : Type u} [Field L]
  (j0 : B0 →+* L) (j1 : B1 →+* L) (j01 : B01 →+* L)
  (hj0 : ∀ a, j01 (r0 a) = j0 a) (hj1 : ∀ a, j01 (r1 a) = j1 a)
  (hi0 : Function.Injective j0) (hi1 : Function.Injective j1) (hi01 : Function.Injective j01)
  (hϖ0 : j0 (ι0 (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)) ≠ 0)
  (hϖ1 : j1 (ι1 (algebraMap O (T1 π b₄ t κ) ϖ)) ≠ 0)

/-! ### The maps `Ba → L`, `Bb → L`, `Bab → L` -/

/-- `Ba = B₀[1/(ϖ z)] → L`, induced by `j₀`. -/
def jA : Ba b₄ ϖ ι0 →+* L := IsLocalization.Away.lift _ hϖ0.isUnit

/-- `Bb = B₁[1/ϖ] → L`, induced by `j₁`. -/
def jB : Bb b₄ ϖ ι1 →+* L := IsLocalization.Away.lift _ hϖ1.isUnit

include hc1 hj1 in
lemma j01_varpi : j01 (ι01 (algebraMap O (T01 π b₄ t κ) ϖ)) =
    j1 (ι1 (algebraMap O (T1 π b₄ t κ) ϖ)) := by
  rw [← hj1, r1_iota1 b₄ hc1, ← IsScalarTower.algebraMap_apply]

/-- `Bab = B₀₁[1/ϖ] → L`, induced by `j₀₁`. -/
def jAB : Bab b₄ ϖ ι01 →+* L :=
  IsLocalization.Away.lift _ ((j01_varpi b₄ hc1 j1 j01 hj1).trans_ne hϖ1).isUnit

lemma jA_algebraMap (a : B0) : jA b₄ j0 hϖ0 (algebraMap B0 _ a) = j0 a :=
  IsLocalization.Away.lift_eq _ _ a

lemma jB_algebraMap (a : B1) : jB b₄ j1 hϖ1 (algebraMap B1 _ a) = j1 a :=
  IsLocalization.Away.lift_eq _ _ a

lemma jAB_algebraMap (a : B01) :
    jAB b₄ hc1 j1 j01 hj1 hϖ1 (algebraMap B01 _ a) = j01 a :=
  IsLocalization.Away.lift_eq _ _ a

include hi0 in
lemma jA_injective : Function.Injective (jA b₄ j0 hϖ0) :=
  injective_of_isLocalization
    (Submonoid.powers (ι0 (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ))) _
    (jA_algebraMap b₄ j0 hϖ0) hi0

include hi1 in
lemma jB_injective : Function.Injective (jB b₄ j1 hϖ1) :=
  injective_of_isLocalization
    (Submonoid.powers (ι1 (algebraMap O (T1 π b₄ t κ) ϖ))) _ (jB_algebraMap b₄ j1 hϖ1) hi1

include hi01 in
lemma jAB_injective : Function.Injective (jAB b₄ hc1 j1 j01 hj1 hϖ1) :=
  injective_of_isLocalization
    (Submonoid.powers (ι01 (algebraMap O (T01 π b₄ t κ) ϖ))) _
    (jAB_algebraMap b₄ hc1 j1 j01 hj1 hϖ1) hi01

include hj0 in
lemma jAB_rhoA (a : Ba b₄ ϖ ι0) :
    jAB b₄ hc1 j1 j01 hj1 hϖ1 (rhoA b₄ hκ hπ hc0 a) = jA b₄ j0 hϖ0 a := by
  have : (jAB b₄ hc1 j1 j01 hj1 hϖ1).comp (rhoA b₄ hκ hπ hc0) = jA b₄ j0 hϖ0 :=
    IsLocalization.ringHom_ext
      (Submonoid.powers (ι0 (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)))
      (RingHom.ext fun b ↦ by
        simp only [RingHom.comp_apply, rhoA_algebraMap, jAB_algebraMap, jA_algebraMap, hj0])
  exact RingHom.congr_fun this a

lemma jAB_rhoB (a : Bb b₄ ϖ ι1) :
    jAB b₄ hc1 j1 j01 hj1 hϖ1 (rhoB b₄ hc1 a) = jB b₄ j1 hϖ1 a := by
  have : (jAB b₄ hc1 j1 j01 hj1 hϖ1).comp (rhoB b₄ hc1) = jB b₄ j1 hϖ1 :=
    IsLocalization.ringHom_ext (Submonoid.powers (ι1 (algebraMap O (T1 π b₄ t κ) ϖ)))
      (RingHom.ext fun b ↦ by
        simp only [RingHom.comp_apply, rhoB_algebraMap, jAB_algebraMap, jB_algebraMap, hj1])
  exact RingHom.congr_fun this a

/-! ### The map from the glued algebra to `L` -/

variable [Algebra (AK π b₄ b₆ ϖ) L]
  (hAK : ∀ a : AK π b₄ b₆ ϖ,
    algebraMap (AK π b₄ b₆ ϖ) L a = jA b₄ j0 hϖ0 (iotaA b₄ ϖ ι0 (f0K π b₄ ϖ hκ a)))
  (hcl0 : ∀ x : L, (j0.comp ι0).IsIntegralElem x → x ∈ j0.range)
  (hcl1 : ∀ x : L, (j1.comp ι1).IsIntegralElem x → x ∈ j1.range)
  (hf0 : ι0.Finite) (hf1 : ι1.Finite)

include hc0 hc1 hj0 hj1 hAK in
/-- The `A[1/ϖ]`-structure of `L` also factors through `T1[1/ϖ]`. -/
lemma algebraMap_eq_jB (a : AK π b₄ b₆ ϖ) :
    algebraMap (AK π b₄ b₆ ϖ) L a = jB b₄ j1 hϖ1 (iotaB b₄ ϖ ι1 (f1K b₄ hκ hπ a)) := by
  set jab := jAB b₄ hc1 j1 j01 hj1 hϖ1
  calc algebraMap (AK π b₄ b₆ ϖ) L a = jA b₄ j0 hϖ0 (iotaA b₄ ϖ ι0 (f0K π b₄ ϖ hκ a)) := hAK a
    _ = jab (rhoA b₄ hκ hπ hc0 (iotaA b₄ ϖ ι0 (f0K π b₄ ϖ hκ a))) :=
        (jAB_rhoA b₄ hκ hπ hc0 hc1 j0 j1 j01 hj0 hj1 hϖ0 hϖ1 _).symm
    _ = jab (iotaAB b₄ ϖ ι01 (r0K b₄ hκ hπ (f0K π b₄ ϖ hκ a))) :=
        congrArg jab (RingHom.congr_fun (rhoA_iotaA b₄ hκ hπ hc0) _)
    _ = jab (iotaAB b₄ ϖ ι01 (r1K π b₄ t κ ϖ (f1K b₄ hκ hπ a))) :=
        congrArg (fun y ↦ jab (iotaAB b₄ ϖ ι01 y)) (AlgHom.congr_fun (r0K_comp b₄ hκ hπ) a)
    _ = jab (rhoB b₄ hc1 (iotaB b₄ ϖ ι1 (f1K b₄ hκ hπ a))) :=
        congrArg jab (RingHom.congr_fun (rhoB_iotaB b₄ hc1) _).symm
    _ = jB b₄ j1 hϖ1 (iotaB b₄ ϖ ι1 (f1K b₄ hκ hπ a)) :=
        jAB_rhoB b₄ hc1 j1 j01 hj1 hϖ1 _

/-- **The glued algebra maps to `L`**: the first component followed by `jA`. -/
def gluedKToL : letI := algA b₄ ϖ hκ ι0; letI := algB b₄ hκ hπ ι1
    gluedK b₄ hκ hπ hc0 hc1 →ₐ[AK π b₄ b₆ ϖ] L :=
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  { (jA b₄ j0 hϖ0).comp ((RingHom.fst _ _).comp (gluedK b₄ hκ hπ hc0 hc1).val.toRingHom) with
    commutes' := fun a ↦ (hAK a).symm }

lemma gluedKToL_apply : letI := algA b₄ ϖ hκ ι0; letI := algB b₄ hκ hπ ι1
    ∀ g : gluedK b₄ hκ hπ hc0 hc1,
      gluedKToL b₄ hκ hπ hc0 hc1 j0 hϖ0 hAK g = jA b₄ j0 hϖ0 g.1.1 :=
  fun _ ↦ rfl

include hj1 hi0 hi1 hϖ1 in
/-- **The map from the glued algebra to `L` is injective.** -/
theorem gluedKToL_injective :
    Function.Injective (gluedKToL b₄ hκ hπ hc0 hc1 j0 hϖ0 hAK) := by
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  intro g g' h
  have h1 : g.1.1 = g'.1.1 :=
    jA_injective b₄ j0 hi0 hϖ0 (show jA b₄ j0 hϖ0 g.1.1 = jA b₄ j0 hϖ0 g'.1.1 from h)
  have hg := g.2
  have hg' := g'.2
  have h2 : g.1.2 = g'.1.2 := by
    refine jB_injective b₄ j1 hi1 hϖ1 ?_
    rw [← jAB_rhoB b₄ hc1 j1 j01 hj1 hϖ1, ← jAB_rhoB b₄ hc1 j1 j01 hj1 hϖ1]
    exact congrArg _ ((hg.symm.trans (congrArg (rhoA b₄ hκ hπ hc0) h1)).trans hg')
  exact Subtype.ext (Prod.ext h1 h2)


include hj0 hj1 hi01 hϖ1 hcl0 hcl1 hf0 hf1 hloc0 hloc1 in
/-- **The image of the glued algebra in `L` is the integral closure of `A[1/ϖ]`.** -/
theorem range_gluedKToL :
    (gluedKToL b₄ hκ hπ hc0 hc1 j0 hϖ0 hAK).range = integralClosure (AK π b₄ b₆ ϖ) L := by
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  haveI := finite_gluedK b₄ hκ hπ hc0 hc1 hloc0 hloc1 hf0 hf1
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨g, rfl⟩
    exact (Algebra.IsIntegral.isIntegral g).map (gluedKToL b₄ hκ hπ hc0 hc1 j0 hϖ0 hAK)
  have hx' : (algebraMap (AK π b₄ b₆ ϖ) L).IsIntegralElem x := hx
  have e0 : algebraMap (AK π b₄ b₆ ϖ) L = ((jA b₄ j0 hϖ0).comp (iotaA b₄ ϖ ι0)).comp
      (f0K π b₄ ϖ hκ : AK π b₄ b₆ ϖ →+* T0K π b₄ t κ ϖ) := RingHom.ext hAK
  have e1 : algebraMap (AK π b₄ b₆ ϖ) L = ((jB b₄ j1 hϖ1).comp (iotaB b₄ ϖ ι1)).comp
      (f1K b₄ hκ hπ : AK π b₄ b₆ ϖ →+* T1K π b₄ t κ ϖ) :=
    RingHom.ext (algebraMap_eq_jB b₄ hκ hπ hc0 hc1 j0 j1 j01 hj0 hj1 hϖ0 hϖ1 hAK)
  obtain ⟨ya, hya⟩ := mem_range_of_isIntegralElem (Rₘ := T0K π b₄ t κ ϖ)
    (Bₘ := Ba b₄ ϖ ι0) (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ) ι0
    j0 (jA b₄ j0 hϖ0) (jA_algebraMap b₄ j0 hϖ0) _
    (fun a ↦ by rw [RingHom.comp_apply, iotaA_algebraMap, jA_algebraMap]) hcl0
    (isIntegralElem_of_comp _ _ (e0 ▸ hx'))
  obtain ⟨yb, hyb⟩ := mem_range_of_isIntegralElem (Rₘ := T1K π b₄ t κ ϖ)
    (Bₘ := Bb b₄ ϖ ι1) (algebraMap O (T1 π b₄ t κ) ϖ) ι1
    j1 (jB b₄ j1 hϖ1) (jB_algebraMap b₄ j1 hϖ1) _
    (fun a ↦ by rw [RingHom.comp_apply, iotaB_algebraMap, jB_algebraMap]) hcl1
    (isIntegralElem_of_comp _ _ (e1 ▸ hx'))
  have hab : rhoA b₄ hκ hπ hc0 ya = rhoB b₄ hc1 yb := by
    refine jAB_injective b₄ hc1 j1 j01 hj1 hi01 hϖ1 ?_
    rw [jAB_rhoA b₄ hκ hπ hc0 hc1 j0 j1 j01 hj0 hj1 hϖ0 hϖ1,
      jAB_rhoB b₄ hc1 j1 j01 hj1 hϖ1, hya, hyb]
  exact (AlgHom.mem_range _).2 ⟨⟨(ya, yb), hab⟩, hya⟩

/-- **G6: the glued generic fibre is the normalization of `A[1/ϖ]` in `L`.** -/
def gluedKEquiv : letI := algA b₄ ϖ hκ ι0; letI := algB b₄ hκ hπ ι1
    gluedK b₄ hκ hπ hc0 hc1 ≃ₐ[AK π b₄ b₆ ϖ] integralClosure (AK π b₄ b₆ ϖ) L :=
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  (AlgEquiv.ofInjective _
    (gluedKToL_injective b₄ hκ hπ hc0 hc1 j0 j1 j01 hj1 hi0 hi1 hϖ0 hϖ1 hAK)).trans
    (Subalgebra.equivOfEq _ _ (range_gluedKToL b₄ hκ hπ hc0 hc1 hloc0 hloc1 j0 j1 j01 hj0 hj1
      hi01 hϖ0 hϖ1 hAK hcl0 hcl1 hf0 hf1))

lemma gluedKEquiv_apply : letI := algA b₄ ϖ hκ ι0; letI := algB b₄ hκ hπ ι1
    ∀ g : gluedK b₄ hκ hπ hc0 hc1,
      ((gluedKEquiv b₄ hκ hπ hc0 hc1 hloc0 hloc1 j0 j1 j01 hj0 hj1 hi0 hi1 hi01 hϖ0 hϖ1 hAK
        hcl0 hcl1 hf0 hf1 g : integralClosure (AK π b₄ b₆ ϖ) L) : L) =
        gluedKToL b₄ hκ hπ hc0 hc1 j0 hϖ0 hAK g :=
  fun _ ↦ rfl


variable (L) in
set_option linter.defProp false in
/-- **G6** as a `Prop` without `letI` in its uses: the glued generic fibre `gluedK` is
isomorphic, as an `A[1/ϖ]`-algebra, to the integral closure of `A[1/ϖ]` in `L`. -/
def GluedKNorm : Prop :=
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  Nonempty (gluedK b₄ hκ hπ hc0 hc1 ≃ₐ[AK π b₄ b₆ ϖ] integralClosure (AK π b₄ b₆ ϖ) L)

include hloc0 hloc1 hj0 hj1 hi0 hi1 hi01 hϖ1 hAK hcl0 hcl1 hf0 hf1 in
/-- **G6: the glued generic fibre is the normalization of `A[1/ϖ]` in `L`** (`gluedKEquiv`). -/
theorem gluedKNorm : GluedKNorm b₄ hκ hπ hc0 hc1 L :=
  ⟨gluedKEquiv b₄ hκ hπ hc0 hc1 hloc0 hloc1 j0 j1 j01 hj0 hj1 hi0 hi1 hi01 hϖ0 hϖ1 hAK
    hcl0 hcl1 hf0 hf1⟩

end

end TateAffine

end SemistableReduction
