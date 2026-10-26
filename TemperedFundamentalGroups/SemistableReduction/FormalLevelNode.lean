/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerChart
import TemperedFundamentalGroups.SemistableReduction.CompletionEtale

/-!
# The formal Kummer form at a node at every level (MR12 T2 S6, step G2)

Let `R` be a chart (an `O`-algebra), `B` an `R`-algebra (the normalisation of the chart in a
cover) and `D : KummerNormAtData ϖ n M' x y B 𝔪` the chosen Kummer data at a node `𝔪` of `R`: an
étale neighbourhood `N₁ ⊇ 𝔫` of `𝔪` and a splitting
`Φ : N₁ ⊗_R B ≅ ∏ᵢ N₁ ⊗_{A_i} O[s,t]/(st − ϖ^{mᵢ})`
(`A_i = O[u,v]/(uv − ϖⁿ)`, `u ↦ sᵈⁱ`, `v ↦ tᵈⁱ`, `u, v ↦ x, y`).

For **any** `R`-algebra `R'` (e.g. a level `R/ϖᵏ⁺¹R` of the chart, or its special fibre) with an
ideal `𝔪'` and an `R`-algebra map `N₁ → R'/𝔪'` (the residue map at `𝔫`), the formal étaleness of
`N₁` gives a canonical `R`-algebra map `N₁ → R̂' = (R')^∧_{𝔪'}` (**`FormalLevel.hatLift`**, the
compatible lifts `N₁ → R'/𝔪'ᵏ⁺¹`), characterised by its residue map (`hatLift_unique`), and the base
change of `Φ` along it is (**`FormalLevel.nodeEquiv`**)

  `R̂' ⊗_R B ≃ₐ[R̂'] ∏ᵢ R̂' ⊗_{A_i} O[s,t]/(st − ϖ^{mᵢ})`   (`u, v ↦ x, y`).

These are the level-`k` Kummer forms of the normalisation used to identify it with the levels of
the M2 lift (S6); being base changes of the one splitting `Φ` along maps characterised by their
residue maps, they are compatible with each other and with the formal Kummer form of the special
fibre (`FormalKummer.nodeEquivOf`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalLevel

noncomputable section

section HatLift

variable {R : Type u} [CommRing R] {N₁ : Type u} [CommRing N₁] [Algebra R N₁]
  {R' : Type u} [CommRing R'] [Algebra R R'] (𝔪 : Ideal R')

/-- The residue map `R̂' → R'/𝔪'` of the `𝔪'`-adic completion. -/
def resHat : AdicCompletion 𝔪 R' →ₐ[R'] R' ⧸ 𝔪 :=
  (Ideal.Quotient.factorₐ R' (pow_one 𝔪).le).comp (AdicCompletion.evalₐ 𝔪 1)

/-- `R'/𝔪'ᵏ⁺¹ → R'/𝔪'`. -/
abbrev fac (k : ℕ) : R' ⧸ 𝔪 ^ (k + 1) →ₐ[R] R' ⧸ 𝔪 :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_self (I := 𝔪) k.succ_ne_zero)

lemma isNilpotent_ker_fac (k : ℕ) :
    IsNilpotent (RingHom.ker (fac (R := R) 𝔪 k : R' ⧸ 𝔪 ^ (k + 1) →+* R' ⧸ 𝔪)) := by
  refine ⟨k + 1, ?_⟩
  have hker : RingHom.ker (fac (R := R) 𝔪 k : R' ⧸ 𝔪 ^ (k + 1) →+* R' ⧸ 𝔪) =
      𝔪.map (Ideal.Quotient.mk _) := by
    ext z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, AlgHom.coe_toRingHom, Ideal.Quotient.factorₐ_apply_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_quotient_iff_mem
        (Ideal.pow_le_self k.succ_ne_zero)]
  rw [hker, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

variable [Algebra.FormallyEtale R N₁] {𝔪}

/-- The lift `N₁ → R'/𝔪'ᵏ⁺¹` of the residue map `r : N₁ → R'/𝔪'` (formal étaleness). -/
def levLift (r : N₁ →ₐ[R] R' ⧸ 𝔪) (k : ℕ) : N₁ →ₐ[R] R' ⧸ 𝔪 ^ (k + 1) :=
  Algebra.FormallySmooth.liftOfSurjective r (fac 𝔪 k)
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_self k.succ_ne_zero))
    (isNilpotent_ker_fac 𝔪 k)

lemma factor_levLift (r : N₁ →ₐ[R] R' ⧸ 𝔪) (k : ℕ) :
    (fac 𝔪 k).comp (levLift r k) = r :=
  Algebra.FormallySmooth.comp_liftOfSurjective ..

/-- Lifts of the residue map through `R'/𝔪'ᵏ⁺¹ → R'/𝔪'` are unique. -/
lemma eq_levLift (r : N₁ →ₐ[R] R' ⧸ 𝔪) (k : ℕ) (g : N₁ →ₐ[R] R' ⧸ 𝔪 ^ (k + 1))
    (hg : (fac 𝔪 k).comp g = r) : g = levLift r k :=
  Algebra.FormallyUnramified.lift_unique_of_ringHom _ (isNilpotent_ker_fac 𝔪 k) _ _ (by
    rw [← AlgHom.comp_toRingHom, ← AlgHom.comp_toRingHom, hg, factor_levLift])

/-- The maps `N₁ → R'/𝔪'ᵏ` of the tower (through `R'/𝔪'ᵏ⁺¹`). -/
def levMap (r : N₁ →ₐ[R] R' ⧸ 𝔪) (k : ℕ) : N₁ →ₐ[R] R' ⧸ 𝔪 ^ k :=
  (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right k.le_succ)).comp (levLift r k)

lemma factor_levLift_succ (r : N₁ →ₐ[R] R' ⧸ 𝔪) {k l : ℕ} (hkl : k ≤ l) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_succ hkl))).comp
      (levLift r l) = levLift r k := by
  refine eq_levLift r k _ ?_
  rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp, factor_levLift]

lemma levMap_compat (r : N₁ →ₐ[R] R' ⧸ 𝔪) {k l : ℕ} (hkl : k ≤ l) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hkl)).comp (levMap r l) = levMap r k := by
  rw [levMap, levMap, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp,
    ← factor_levLift_succ r hkl, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]

/-- **The canonical map `N₁ → R̂'` lifting a residue map `r : N₁ → R'/𝔪'`** (formal étaleness of
`N₁` over `R`). -/
def hatLift (r : N₁ →ₐ[R] R' ⧸ 𝔪) : N₁ →ₐ[R] AdicCompletion 𝔪 R' :=
  AdicCompletion.liftAlgHom 𝔪 (levMap r) fun hkl ↦ levMap_compat r hkl

lemma evalₐ_hatLift (r : N₁ →ₐ[R] R' ⧸ 𝔪) (k : ℕ) (z : N₁) :
    AdicCompletion.evalₐ 𝔪 k (hatLift r z) = levMap r k z :=
  AdicCompletion.evalₐ_liftAlgHom ..

/-- **Uniqueness of `hatLift`**: an `R`-algebra map `N₁ → R̂'` is determined by its residue map. -/
theorem hatLift_unique (r : N₁ →ₐ[R] R' ⧸ 𝔪) (g : N₁ →ₐ[R] AdicCompletion 𝔪 R')
    (hg : ∀ z, resHat 𝔪 (g z) = r z) : g = hatLift r := by
  have hlev : ∀ k, ((AdicCompletion.evalₐ 𝔪 (k + 1)).restrictScalars R).comp g = levLift r k :=
    fun k ↦ eq_levLift r k _ (AlgHom.ext fun z ↦ by
      rw [← hg z]
      have h1 := CompletionEtale.factorPow_evalₐ 𝔪 (show 1 ≤ k + 1 by omega) (g z)
      obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔪 (k + 1) (g z))
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, resHat]
      rw [← h1, ← hw]
      rfl)
  refine AlgHom.ext fun z ↦ AdicCompletion.ext_evalₐ fun k ↦ ?_
  rw [evalₐ_hatLift, levMap, AlgHom.comp_apply, ← hlev k]
  have h1 := CompletionEtale.factorPow_evalₐ 𝔪 k.le_succ (g z)
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔪 (k + 1) (g z))
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  rw [← h1, ← hw]
  rfl

end HatLift

section Red

open KummerEtale

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k) {c : O} {d : ℕ}
  (hc : θ c = 0) {N : Type u} [CommRing N] [Algebra (A c d) N]
  {T : Type u} [CommRing T] [Algebra (A (0 : k) d) T]

/-- `T ⊗_{k[u,v]/(uv)} k[s,t]/(st)` as an algebra over `O[u,v]/(uv − c^d)` (reduction). -/
abbrev redAlg : Algebra (A c d) (T ⊗[A (0 : k) d] B (0 : k)) :=
  ((algebraMap (A (0 : k) d) (T ⊗[A (0 : k) d] B (0 : k))).comp
    (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc))).toAlgebra

/-- **The reduction of a Kummer factor along a ring map `g : N → T`**:
`N ⊗_{O[u,v]/(uv − c^d)} O[s,t]/(st − c) → T ⊗_{k[u,v]/(uv)} k[s,t]/(st)`, `n ⊗ b ↦ g n ⊗ b̄`,
for `g` compatible with the node rings. -/
def redTensorMap (g : N →+* T)
    (hg : ∀ a, g (algebraMap (A c d) N a) =
      algebraMap (A (0 : k) d) T (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc) a)) :
    N ⊗[A c d] KNode c d →+* T ⊗[A (0 : k) d] B (0 : k) :=
  letI := redAlg (T := T) (d := d) θ hc
  (Algebra.TensorProduct.lift
    ({ Algebra.TensorProduct.includeLeftRingHom.comp g with
        commutes' := fun a ↦ by
          change g (algebraMap (A c d) N a) ⊗ₜ[A (0 : k) d] (1 : B (0 : k)) = _
          rw [hg]
          rfl } : N →ₐ[A c d] T ⊗[A (0 : k) d] B (0 : k))
    ({ (Algebra.TensorProduct.includeRight (R := A (0 : k) d) (A := T)).toRingHom.comp
          (Node.baseMap θ hc : Node O c →+* Node k (0 : k)) with
        commutes' := fun a ↦ by
          have h := RingHom.congr_fun (Node.baseMap_comp_kummer θ hc d) a
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
          change (1 : T) ⊗ₜ[A (0 : k) d] (Node.baseMap θ hc (Node.kummer c d a)) = _
          rw [h]
          change _ = algebraMap (A (0 : k) d) (T ⊗[A (0 : k) d] B (0 : k))
            (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc) a)
          rw [Algebra.TensorProduct.algebraMap_apply']
          rfl } : KNode c d →ₐ[A c d] T ⊗[A (0 : k) d] B (0 : k))
    fun _ _ ↦ Commute.all _ _).toRingHom

lemma redTensorMap_tmul (g : N →+* T)
    (hg : ∀ a, g (algebraMap (A c d) N a) =
      algebraMap (A (0 : k) d) T (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc) a))
    (x : N) (b : KNode c d) :
    redTensorMap θ hc g hg (x ⊗ₜ b) =
      g x ⊗ₜ[A (0 : k) d] (Node.baseMap θ hc : Node O c →+* Node k (0 : k)) b := by
  letI := redAlg (T := T) (d := d) θ hc
  simp only [redTensorMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.lift_tmul]
  change (g x ⊗ₜ[A (0 : k) d] (1 : B (0 : k))) * ((1 : T) ⊗ₜ _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Red

section Res

variable {R : Type u} [CommRing R] {N₁ : Type u} [CommRing N₁] [Algebra R N₁] {𝔪 : Ideal R}
  {𝔫 : Ideal N₁} (hcomap : 𝔫.comap (algebraMap R N₁) = 𝔪)
  (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R N₁)))
  {R' : Type u} [CommRing R'] [Algebra R R'] {𝔪' : Ideal R'}
  (h𝔪 : 𝔪 ≤ 𝔪'.comap (algebraMap R R'))

/-- `R/𝔪 ≃ N₁/𝔫` (trivial residue field extension). -/
def resEquiv : (R ⧸ 𝔪) ≃ₐ[R] (N₁ ⧸ 𝔫) :=
  AlgEquiv.ofBijective (Ideal.quotientMapₐ 𝔫 (Algebra.ofId R N₁) hcomap.ge) ⟨by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk 𝔫 (algebraMap R N₁ a) = 0 at hz
    rw [Ideal.Quotient.eq_zero_iff_mem] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hcomap]
    exact hz, by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk 𝔫 z)
    exact ⟨Ideal.Quotient.mk 𝔪 a, ha⟩⟩

/-- **The residue map `N₁ → N₁/𝔫 ≅ R/𝔪 → R'/𝔪'`.** -/
def resMap : N₁ →ₐ[R] R' ⧸ 𝔪' :=
  ((Ideal.quotientMapₐ 𝔪' (Algebra.ofId R R') h𝔪).comp
    (resEquiv hcomap hsurj).symm.toAlgHom).comp (Ideal.Quotient.mkₐ R 𝔫)

include hcomap in
lemma resMap_eq_zero {z : N₁} (hz : z ∈ 𝔫) : resMap hcomap hsurj h𝔪 z = 0 := by
  simp only [resMap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]

end Res

section Node

open KummerEtale FormalKummer

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] {ϖ : O} {n M' : ℕ} {x y : R} {𝔪 : Ideal R}
  {R' : Type u} [CommRing R'] [Algebra R R'] {𝔪' : Ideal R'}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) (D : KummerNormAtData ϖ n M' x y B 𝔪)

include hxy in
lemma hxy_i (i : Fin D.r) : x * y = algebraMap O R ((ϖ ^ D.m i) ^ D.d i) := by
  rw [← pow_mul, D.hmd i]; exact hxy

/-- The node chart `O[u,v]/(uv − ϖⁿ) → R`, `u, v ↦ x, y`, of the `i`-th Kummer factor. -/
abbrev chart (i : Fin D.r) : A (ϖ ^ D.m i) (D.d i) →ₐ[O] R := Node.lift x y (hxy_i hxy D i)

/-- `R̂'` as an algebra over the node ring of the `i`-th factor, through the chart `u, v ↦ x, y`. -/
abbrev hatAlg (i : Fin D.r) : Algebra (A (ϖ ^ D.m i) (D.d i)) (AdicCompletion 𝔪' R') :=
  ((algebraMap R (AdicCompletion 𝔪' R')).comp (chart hxy D i).toRingHom).toAlgebra

lemma algebraMap_N₁ (i : Fin D.r) (a : A (ϖ ^ D.m i) (D.d i)) :
    letI : Algebra O D.N₁ := ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra
    letI := nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i D.huv D.hmd i)
    algebraMap (A (ϖ ^ D.m i) (D.d i)) D.N₁ a = algebraMap R D.N₁ (chart hxy D i a) := by
  letI : Algebra O D.N₁ := ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra
  haveI : IsScalarTower O R D.N₁ := IsScalarTower.of_algebraMap_eq' rfl
  have h : (IsScalarTower.toAlgHom O R D.N₁).comp (chart hxy D i) =
      Node.lift (algebraMap R D.N₁ x) (algebraMap R D.N₁ y) (huv_i D.huv D.hmd i) :=
    Node.algHom_ext (by simp) (by simp)
  exact (congrArg (fun φ : A (ϖ ^ D.m i) (D.d i) →ₐ[O] D.N₁ ↦ φ a) h).symm

/-- **The level formal Kummer form at a node**: the base change of the chosen splitting `D.Φ`
along `hatLift r : N₁ → R̂'` (`r` the residue map at `𝔫`),
`R̂' ⊗_R B ≃ₐ[R̂'] ∏ᵢ R̂' ⊗_{O[u,v]/(uv − ϖⁿ)} O[s,t]/(st − ϖ^{mᵢ})` (`u, v ↦ x, y`). -/
def nodeEquiv (r : D.N₁ →ₐ[R] R' ⧸ 𝔪') :
    letI := fun i ↦ hatAlg (𝔪' := 𝔪') hxy D i
    AdicCompletion 𝔪' R' ⊗[R] B ≃ₐ[AdicCompletion 𝔪' R']
      ∀ i, AdicCompletion 𝔪' R' ⊗[A (ϖ ^ D.m i) (D.d i)] KNode (ϖ ^ D.m i) (D.d i) :=
  letI := fun i ↦ hatAlg (𝔪' := 𝔪') hxy D i
  letI : Algebra O D.N₁ := ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra
  letI := fun i ↦ nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i D.huv D.hmd i)
  haveI : Algebra.FormallyEtale R D.N₁ := inferInstance
  baseChangeEquiv (hatLift r) (fun i ↦ (chart hxy D i).toRingHom)
    (fun i a ↦ algebraMap_N₁ hxy D i a) (fun _ _ ↦ rfl) D.Φ

end Node

end

end FormalLevel

end SemistableReduction
