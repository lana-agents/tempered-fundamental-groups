/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerNodeEtale
import TemperedFundamentalGroups.SemistableReduction.NodeCoeff
import TemperedFundamentalGroups.SemistableReduction.NodeSmooth

/-!
# The Kummer covering of a node over the punctured neighbourhood (Blueprint §12.8, M2.3)

Let `A = Node O (π^e)` (`uv = π^e`) and `B = Node O π` (`st = π`) with the Kummer map
`u ↦ s^e`, `v ↦ t^e` (`KummerEtale`). The element `u + v ∈ A` cuts out the node on the special
fibre (`uv ≡ 0` there), so `D(u + v)` is the punctured neighbourhood of the node. Here:

* `KummerEtale.eq_zero_of_mul_eq_zero`: `u + v` is a nonzerodivisor on `B`, over any base `O`
  (`Node.eq_zero_of_pow_add_pow_mul_eq_zero`);
* **`KummerEtale.eq_zero_of_mul_eq_zero_tensor`**: hence on `S ⊗_A B` for every flat `A`-algebra
  `S` (e.g. a completion of a ring étale over `A` along the node): the hypothesis `hN` of the formal
  glueing `FormalGlueing.glued` for the Kummer algebra;
* `etale_comp_away_away` (generic): if `A → B_g` is étale, so is `A_f → (B_f)_g`;
* **`KummerEtale.etale_away`**: for `e` invertible in `O`, `B_{u+v}` is étale over `A_{u+v}`: the
  Kummer covering is étale over the punctured neighbourhood. Proof: `s, t` generate the unit ideal
  of `B_{u+v}` (`s^e + t^e` is a unit); `B_s` is étale over `A` (`KummerEtale.etale`), and so is
  `B_t` by the symmetry `u ↔ v`, `s ↔ t` (`Node.swap`); étaleness is local on the target
  (Mathlib `RingHom.Etale.ofLocalizationSpanTarget`).
-/

universe w

open TensorProduct

namespace SemistableReduction

/-! ### Generic: étaleness after inverting an element of the base -/

section Generic

variable {A B : Type w} [CommRing A] [CommRing B]

/-- If `A → B_g` is étale then so is `A_f → (B_{φ f})_g`. -/
theorem etale_comp_away_away (φ : A →+* B) (f : A) (g : B)
    (hg : ((algebraMap B (Localization.Away g)).comp φ).Etale) :
    ((algebraMap (Localization.Away (φ f))
        (Localization.Away (algebraMap B (Localization.Away (φ f)) g))).comp
      (Localization.awayMap φ f)).Etale := by
  set Bf := Localization.Away (φ f)
  set T := Localization.Away (algebraMap B Bf g)
  set Bg := Localization.Away g
  set T' := Localization.Away (algebraMap B Bg (φ f))
  -- `T` and `T'` are both `B` localized at `g φ(f)`
  haveI : IsLocalization.Away (g * φ f) T := by
    rw [mul_comm]; infer_instance
  let ι : T' ≃ₐ[B] T := IsLocalization.algEquiv (Submonoid.powers (g * φ f)) T' T
  have hBT : (algebraMap B T).comp φ =
      (ι.toRingEquiv.toRingHom.comp (algebraMap Bg T')).comp ((algebraMap B Bg).comp φ) := by
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      RingHom.coe_coe]
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  have h1 : ((algebraMap B T).comp φ).Etale := by
    rw [hBT]
    refine RingHom.Etale.stableUnderComposition _ _ hg ?_
    refine RingHom.Etale.respectsIso.1 _ ι.toRingEquiv ?_
    exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (algebraMap B Bg (φ f)))
  -- descend to `A_f`
  letI : Algebra A T := ((algebraMap B T).comp φ).toAlgebra
  letI : Algebra (Localization.Away f) T :=
    ((algebraMap Bf T).comp (Localization.awayMap φ f)).toAlgebra
  haveI : IsScalarTower A (Localization.Away f) T := by
    refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
    change algebraMap B T (φ a) = algebraMap Bf T (Localization.awayMap φ f (algebraMap A _ a))
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
      ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.Etale A T := (RingHom.etale_algebraMap).mp h1
  haveI : Algebra.Etale A (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  have : Algebra.Etale (Localization.Away f) T :=
    Algebra.Etale.of_restrictScalars A (Localization.Away f) T
  exact RingHom.etale_algebraMap.mpr this

end Generic

namespace Node

variable {O : Type w} [CommRing O]

/-- The symmetry `u ↔ v` as an algebra equivalence (`Node.swap`, `NodeSmooth.lean`). -/
noncomputable def swapAlgEquiv (a : O) : Node O a ≃ₐ[O] Node O a :=
  AlgEquiv.ofAlgHom (swap a) (swap a) (swap_swap a) (swap_swap a)

lemma swap_comp_kummer (c : O) (m : ℕ) :
    (swap c).comp (kummer c m) = (kummer c m).comp (swap (c ^ m)) :=
  algHom_ext (by simp) (by simp)

end Node

namespace KummerEtale

noncomputable section

variable {O : Type w} [CommRing O] (π : O) {e : ℕ}

/-- `u + v ∈ A`: it cuts out the node on the special fibre. -/
abbrev fA : A π e := Node.u (π ^ e) + Node.v (π ^ e)

lemma algebraMap_fA : algebraMap (A π e) (B π) (fA π) = Node.u π ^ e + Node.v π ^ e := by
  rw [map_add, algebraMap_u, algebraMap_v]

/-- **`u + v` is a nonzerodivisor on the Kummer algebra `B`** (any base `O`). -/
theorem eq_zero_of_mul_eq_zero (he : 0 < e) {b : B π}
    (hb : algebraMap (A π e) (B π) (fA π) * b = 0) : b = 0 := by
  rw [algebraMap_fA] at hb
  exact Node.eq_zero_of_pow_add_pow_mul_eq_zero π he hb

/-- **`u + v` is a nonzerodivisor on `S ⊗_A B` for `S` flat over `A`.** -/
theorem eq_zero_of_mul_eq_zero_tensor (he : 0 < e) (S : Type*) [CommRing S] [Algebra (A π e) S]
    [Module.Flat (A π e) S] {z : S ⊗[A π e] B π}
    (hz : algebraMap (A π e) (S ⊗[A π e] B π) (fA π) * z = 0) : z = 0 := by
  let μ : B π →ₗ[A π e] B π := LinearMap.mulLeft (A π e) (algebraMap (A π e) (B π) (fA π))
  have hμ : Function.Injective μ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro b hb
    exact eq_zero_of_mul_eq_zero π he hb
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := S) μ hμ
  have hμz : ∀ z : S ⊗[A π e] B π,
      μ.lTensor S z = algebraMap (A π e) (S ⊗[A π e] B π) (fA π) * z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        show algebraMap (A π e) (B π) (fA π) * y = fA π • y from (Algebra.smul_def _ _).symm,
        show algebraMap (A π e) S (fA π) * x = fA π • x from (Algebra.smul_def _ _).symm,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add x y hx hy => rw [map_add, hx, hy, mul_add]
  rw [← hμz] at hz
  exact hinj (by rw [hz, map_zero])

variable {π}

/-- `A → B_s` is étale. -/
theorem etale_s (he : 0 < e) (heu : IsUnit (e : O)) :
    ((algebraMap (B π) (Bs π)).comp (algebraMap (A π e) (B π))).Etale := by
  haveI := etale π he heu
  haveI : Algebra.Etale (A π e) (Au π e) :=
    Algebra.Etale.of_isLocalizationAway (Node.u (π ^ e))
  haveI : IsScalarTower (A π e) (Au π e) (Bs π) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      rw [IsScalarTower.algebraMap_apply (A π e) (B π) (Bs π)]
      exact (auToBs_algebraMap π a).symm
  haveI : Algebra.Etale (A π e) (Bs π) := Algebra.Etale.comp (A π e) (Au π e) (Bs π)
  rw [← IsScalarTower.algebraMap_eq]
  exact RingHom.etale_algebraMap.mpr this

/-- `A → B_t` is étale (by the symmetry `u ↔ v`). -/
theorem etale_t (he : 0 < e) (heu : IsUnit (e : O)) :
    ((algebraMap (B π) (Localization.Away (Node.v π))).comp (algebraMap (A π e) (B π))).Etale := by
  -- the swap of `B` induces `B_s ≃ B_t`
  let σB := (Node.swapAlgEquiv π).toRingEquiv
  let σA := (Node.swapAlgEquiv (π ^ e)).toRingEquiv
  have hmap : Submonoid.map (σB : B π →+* B π) (Submonoid.powers (Node.u π)) =
      Submonoid.powers (Node.v π) := by
    rw [Submonoid.map_powers]
    simp [σB, Node.swapAlgEquiv]
  let ρ : Bs π ≃+* Localization.Away (Node.v π) :=
    IsLocalization.ringEquivOfRingEquiv (Bs π) (Localization.Away (Node.v π)) σB hmap
  have hcomp : (algebraMap (B π) (Localization.Away (Node.v π))).comp (algebraMap (A π e) (B π)) =
      ((ρ : Bs π →+* _).comp ((algebraMap (B π) (Bs π)).comp (algebraMap (A π e) (B π)))).comp
        (σA : A π e →+* A π e) := by
    refine RingHom.ext fun a ↦ ?_
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    congr 1
    change Node.kummer π e a = Node.swap π (Node.kummer π e (Node.swap (π ^ e) a))
    rw [← AlgHom.comp_apply (Node.swap π), Node.swap_comp_kummer, AlgHom.comp_apply,
      ← AlgHom.comp_apply (Node.swap (π ^ e)), Node.swap_swap, AlgHom.id_apply]
  rw [hcomp]
  refine RingHom.Etale.respectsIso.2 _ σA ?_
  exact RingHom.Etale.respectsIso.1 _ ρ (etale_s he heu)

variable (π e) in
/-- `A_{u+v}`. -/
abbrev Af : Type w := Localization.Away (fA π (e := e))

variable (π e) in
/-- `B_{u+v}`. -/
abbrev Bf : Type w := Localization.Away (algebraMap (A π e) (B π) (fA π))

variable (π e) in
/-- `A_{u+v} → B_{u+v}`. -/
abbrev afToBf : Af π e →+* Bf π e :=
  Localization.awayMap (algebraMap (A π e) (B π)) (fA π)

/-- **The Kummer covering is étale over the punctured neighbourhood** `D(u + v)` of the node
(for `e` invertible in `O`). -/
theorem etale_away (he : 0 < e) (heu : IsUnit (e : O)) : (afToBf π e).Etale := by
  set F := algebraMap (A π e) (B π) (fA π)
  have hspan : Ideal.span {algebraMap (B π) (Bf π e) (Node.u π),
      algebraMap (B π) (Bf π e) (Node.v π)} = ⊤ := by
    have hF : IsUnit (algebraMap (B π) (Bf π e) F) :=
      IsLocalization.Away.algebraMap_isUnit F
    rw [Ideal.eq_top_iff_one]
    obtain ⟨w, hw⟩ := hF.exists_right_inv
    obtain ⟨k, hk⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hx : ∀ x : Bf π e, x ^ e = x * x ^ k := fun x ↦ by
      rw [← pow_succ']; exact congrArg (x ^ ·) hk
    have key : algebraMap (B π) (Bf π e) F = algebraMap (B π) _ (Node.u π) *
        algebraMap (B π) _ (Node.u π) ^ k +
        algebraMap (B π) _ (Node.v π) * algebraMap (B π) _ (Node.v π) ^ k := by
      calc algebraMap (B π) (Bf π e) F =
            algebraMap (B π) (Bf π e) (Node.u π ^ e + Node.v π ^ e) := congrArg _ (algebraMap_fA π)
        _ = _ := by
          rw [map_add]
          exact congrArg₂ (· + ·) ((map_pow _ _ _).trans (hx _)) ((map_pow _ _ _).trans (hx _))
    rw [key] at hw
    have : (1 : Bf π e) = algebraMap (B π) _ (Node.u π) *
        (algebraMap (B π) _ (Node.u π) ^ k * w) +
        algebraMap (B π) _ (Node.v π) * (algebraMap (B π) _ (Node.v π) ^ k * w) := by
      linear_combination -hw
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  refine RingHom.Etale.ofLocalizationSpanTarget _ _ hspan ?_
  rintro ⟨r, hr⟩
  rcases hr with rfl | hr
  · exact etale_comp_away_away (algebraMap (A π e) (B π)) (fA π) (Node.u π) (etale_s he heu)
  · rw [Set.mem_singleton_iff] at hr
    subst hr
    exact etale_comp_away_away (algebraMap (A π e) (B π)) (fA π) (Node.v π) (etale_t he heu)

end

end KummerEtale

end SemistableReduction
