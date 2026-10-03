/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TameLocal
import TemperedFundamentalGroups.SemistableReduction.LocalModel

/-!
# Kummer covers of nodes (W8 at a node, and W8′)

Blueprint §9.3 (W7 → W8 interface), §9.7 (W8′). Let `O` be a discrete valuation ring with
uniformizer `ϖ`, `N` an `O`-algebra (a chart of a model of a curve, e.g. the node chart
`O[u, ϖⁿ/u]` of the Gauss tree) with a prime `𝔪` (a node point), and `F'` an `N`-algebra (the
function field of a finite cover). The cover is **Kummer at `𝔪`** (`IsKummerAt`) if, étale-locally
at `𝔪`, it is a product of Kummer covers of a node: there are

* an étale `N`-algebra `N₁` with a prime `𝔫` over `𝔪`;
* an étale node chart `O[u, v] ⧸ (u v - ϖ ⁿ) → N₁`, `u ↦ u₁`, `v ↦ v₁`;
* an `N₁`-algebra isomorphism `N₁ ⊗_N F' ≃ ∏ᵢ N₁ ⊗_{O[u,v]/(uv - ϖⁿ)} Frac (O[w, z] ⧸ (w z - ϖ^{mᵢ}))`,
  where `n = mᵢ dᵢ` and `u ↦ w ^ dᵢ`, `v ↦ z ^ dᵢ` (`Node.kummer`).

Then (`IsKummerAt.isEtaleLocallyAt`) every prime of the integral closure of `N` in `F'` over `𝔪`
is étale-locally a node of thickness `ϖ ^ mᵢ` for some `i`, on which the base coordinate `u₁` is the
`dᵢ`-th power of the node coordinate: the thickness is divided by the local degree `dᵢ` (W8′).

Proof: normalization commutes with étale base change (Mathlib,
`TensorProduct.toIntegralClosure_bijective_of_smooth`), and the normalization of a node in a
Kummer extension is a node (the local tame lemma `Node.kummer_isIntegralClosure`, valid for every
`dᵢ`, including `p ∣ dᵢ`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace Node

variable {O : Type*} [CommRing O]

/-- Nodes with equal parameters are isomorphic (`u ↦ u`, `v ↦ v`). -/
noncomputable def congr {a b : O} (h : a = b) : Node O a ≃ₐ[O] Node O b := h ▸ AlgEquiv.refl

@[simp] lemma congr_u {a b : O} (h : a = b) : congr h (u a) = u b := by
  subst h; rfl

@[simp] lemma congr_v {a b : O} (h : a = b) : congr h (v a) = v b := by
  subst h; rfl

end Node

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, CommRing (S i)]

/-- A prime of a finite product of rings comes from one factor. -/
theorem exists_eq_comap_evalRingHom (P : Ideal (∀ i, S i)) [hP : P.IsPrime] :
    ∃ (i : ι) (Q : Ideal (S i)), Q.IsPrime ∧ P = Q.comap (Pi.evalRingHom S i) := by
  have h1 : ∃ i, (Pi.single i 1 : ∀ j, S j) ∉ P := by
    by_contra! H
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : ∀ i, S i) = ∑ i, Pi.single i 1 := by
      funext j; simp [Finset.sum_apply]
    rw [this]
    exact Ideal.sum_mem _ fun i _ ↦ H i
  obtain ⟨i, hi⟩ := h1
  have hsurj : Function.Surjective (Pi.evalRingHom S i) := fun y ↦
    ⟨Pi.single i y, by simp⟩
  have key : ∀ x y : ∀ j, S j, x i = y i → x * Pi.single i 1 = y * Pi.single i 1 := by
    intro x y hxy
    funext j
    by_cases hj : j = i
    · subst hj; simp [hxy]
    · simp [hj]
  have hker : RingHom.ker (Pi.evalRingHom S i) ≤ P := by
    intro y hy
    rw [RingHom.mem_ker, Pi.evalRingHom_apply] at hy
    have := key y 0 (by simp [hy])
    rw [zero_mul] at this
    exact (hP.mem_or_mem (this ▸ P.zero_mem)).resolve_right hi
  refine ⟨i, P.map (Pi.evalRingHom S i), Ideal.map_isPrime_of_surjective hsurj hker, ?_⟩
  rw [Ideal.comap_map_of_surjective _ hsurj]
  refine le_antisymm le_sup_left (sup_le le_rfl ?_)
  intro x hx
  rw [Ideal.mem_comap] at hx
  have : Ideal.comap (Pi.evalRingHom S i) ⊥ = RingHom.ker (Pi.evalRingHom S i) := rfl
  exact hker (by rwa [← this])

omit [Fintype ι] in
theorem etale_evalRingHom (i : ι) : (Pi.evalRingHom S i).Etale := by
  letI : Algebra (∀ j, S j) (S i) := (Pi.evalRingHom S i).toAlgebra
  have : IsLocalization.Away (Pi.single i (1 : S i) : ∀ j, S j) (S i) := by
    apply IsLocalization.away_of_isIdempotentElem
    · simp [IsIdempotentElem, ← Pi.single_mul_left]
    · apply RingHom.ker_evalRingHom
    · apply (Pi.evalRingHom S i).surjective
  exact Algebra.Etale.of_isLocalizationAway (Pi.single i (1 : S i))

end Pi

section IntegralClosure

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, CommRing (X i)]
  [∀ i, Algebra R (X i)]

/-- An element of a finite product is integral iff its components are. -/
theorem isIntegral_pi_iff {x : ∀ i, X i} : IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  classical
  refine ⟨fun h i ↦ h.map (Pi.evalAlgHom R X i), fun h ↦ ?_⟩
  choose p hpm hp using h
  refine ⟨∏ i, p i, Polynomial.monic_prod_of_monic _ _ fun i _ ↦ hpm i, ?_⟩
  funext j
  rw [← Polynomial.aeval_def, Pi.zero_apply]
  have : (Polynomial.aeval x (∏ i, p i)) j = Polynomial.aeval (x j) (∏ i, p i) :=
    (Polynomial.aeval_algHom_apply (Pi.evalAlgHom R X j) x (∏ i, p i)).symm
  rw [this, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [Polynomial.aeval_def]; exact hp j)

/-- The integral closure in a finite product is the product of the integral closures. -/
noncomputable def integralClosurePiEquiv :
    integralClosure R (∀ i, X i) ≃ₐ[R] ∀ i, integralClosure R (X i) where
  toFun x i := ⟨x.1 i, isIntegral_pi_iff.mp x.2 i⟩
  invFun y := ⟨fun i ↦ (y i).1, isIntegral_pi_iff.mpr fun i ↦ (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end IntegralClosure

section KummerField

variable {O : Type u} [CommRing O]

/-- The node `O[w, z] ⧸ (w z - c)`, as an algebra over `O[u, v] ⧸ (u v - c ^ d)` via the Kummer
map `u ↦ w ^ d`, `v ↦ z ^ d`. -/
def KNode (c : O) (_d : ℕ) : Type u := Node O c

/-- The function field `Frac (O[w, z] ⧸ (w z - c))` of the Kummer cover `u = w ^ d` of the node
`O[u, v] ⧸ (u v - c ^ d)`, as an algebra over the latter (`u ↦ w ^ d`, `v ↦ z ^ d`). -/
def KummerField (c : O) (_d : ℕ) : Type u := FractionRing (Node O c)

variable (c : O) (d : ℕ)

noncomputable instance : CommRing (KNode c d) := inferInstanceAs (CommRing (Node O c))

noncomputable instance : Algebra O (KNode c d) := inferInstanceAs (Algebra O (Node O c))

noncomputable instance : Algebra (Node O (c ^ d)) (KNode c d) := Node.kummerAlgebra c d

noncomputable instance : CommRing (KummerField c d) :=
  inferInstanceAs (CommRing (FractionRing (Node O c)))

noncomputable instance : Algebra (KNode c d) (KummerField c d) :=
  inferInstanceAs (Algebra (Node O c) (FractionRing (Node O c)))

noncomputable instance : Algebra (Node O (c ^ d)) (KummerField c d) :=
  letI := Node.kummerAlgebra c d
  inferInstanceAs (Algebra (Node O (c ^ d)) (FractionRing (Node O c)))

instance : IsScalarTower (Node O (c ^ d)) (KNode c d) (KummerField c d) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The coordinate `w` of the Kummer cover. -/
noncomputable def KNode.u : KNode c d := Node.u c

/-- The coordinate `z` of the Kummer cover. -/
noncomputable def KNode.v : KNode c d := Node.v c

lemma KNode.u_pow : KNode.u c d ^ d = algebraMap (Node O (c ^ d)) (KNode c d) (Node.u (c ^ d)) :=
  (Node.kummer_u c d).symm

lemma KNode.v_pow : KNode.v c d ^ d = algebraMap (Node O (c ^ d)) (KNode c d) (Node.v (c ^ d)) :=
  (Node.kummer_v c d).symm

variable [IsDomain O] [IsIntegrallyClosed O] {c d}

/-- The integral closure of the node `O[u, v] ⧸ (u v - c ^ d)` in the Kummer field is the node
`O[w, z] ⧸ (w z - c)` (the local tame lemma). -/
noncomputable def kummerIntegralClosureEquiv (hc : c ≠ 0) (hd : 0 < d) :
    KNode c d ≃ₐ[Node O (c ^ d)] integralClosure (Node O (c ^ d)) (KummerField c d) :=
  haveI : IsIntegralClosure (KNode c d) (Node O (c ^ d)) (KummerField c d) :=
    Node.kummer_isIntegralClosure hc hd
  IsIntegralClosure.equiv (Node O (c ^ d)) (KNode c d) (KummerField c d)
    (integralClosure (Node O (c ^ d)) (KummerField c d))

variable (N₁ : Type u) [CommRing N₁] [Algebra (Node O (c ^ d)) N₁]

/-- The Kummer factor `N₁ ⊗_{O[u,v]/(uv - c^d)} Frac (O[w, z] ⧸ (w z - c))` (`u ↦ w ^ d`). -/
abbrev KummerFactor : Type u := N₁ ⊗[Node O (c ^ d)] KummerField c d

/-- Its normalization `N₁ ⊗_{O[u,v]/(uv - c^d)} O[w, z] ⧸ (w z - c)`. -/
abbrev KummerNodeFactor : Type u := N₁ ⊗[Node O (c ^ d)] KNode c d

variable [Algebra.Smooth (Node O (c ^ d)) N₁]

/-- **Étale-local tame lemma.** For a smooth (e.g. étale) algebra `N₁` over the node
`O[u, v] ⧸ (u v - c ^ d)`, the integral closure of `N₁` in the base changed Kummer field is
`N₁ ⊗ O[w, z] ⧸ (w z - c)`. -/
noncomputable def kummerFactorEquiv (hc : c ≠ 0) (hd : 0 < d) :
    KummerNodeFactor (c := c) (d := d) N₁ ≃ₐ[N₁]
      integralClosure N₁ (KummerFactor (c := c) (d := d) N₁) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (kummerIntegralClosureEquiv hc hd)).trans
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure (Node O (c ^ d)) N₁ (KummerField c d))
      TensorProduct.toIntegralClosure_bijective_of_smooth)

end KummerField

section Factors

variable {O : Type u} [CommRing O] (N₁ : Type u) [CommRing N₁] [Algebra O N₁] {u₁ v₁ : N₁}
  (c : O) (d : ℕ)

/-- The node chart `O[u, v] ⧸ (u v - c ^ d) → N₁`, `u ↦ u₁`, `v ↦ v₁`, as an algebra. -/
noncomputable abbrev nodeAlgebra (h : u₁ * v₁ = algebraMap O N₁ (c ^ d)) :
    Algebra (Node O (c ^ d)) N₁ :=
  (Node.lift u₁ v₁ h).toAlgebra

end Factors

/-- **The cover `F'` of `N` is Kummer at the node point `𝔪`** (the W7 → W8 interface, Blueprint
§9.3): étale-locally at `𝔪` the base is a node `O[u, v] ⧸ (u v - ϖ ^ n)` and `F'` is a product of
Kummer covers `u = w ^ dᵢ` of it, `n = mᵢ dᵢ`. -/
def IsKummerAt {O : Type u} [CommRing O] (ϖ : O) (n : ℕ) {N : Type u} [CommRing N] [Algebra O N]
    (F' : Type u) [CommRing F'] [Algebra N F'] (𝔪 : Ideal N) : Prop :=
  ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : Algebra N N₁) (_ : Algebra.Etale N N₁) (𝔫 : Ideal N₁)
    (_ : 𝔫.IsPrime) (_ : 𝔫.comap (algebraMap N N₁) = 𝔪),
    letI : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
    ∃ (u₁ v₁ : N₁) (huv : u₁ * v₁ = algebraMap O N₁ (ϖ ^ n)),
      (Node.lift u₁ v₁ huv).toRingHom.Etale ∧ u₁ ∈ 𝔫 ∧ v₁ ∈ 𝔫 ∧
      ∃ (r : ℕ) (m d : Fin r → ℕ) (_ : ∀ i, 0 < d i) (hmd : ∀ i, m i * d i = n),
        Nonempty (N₁ ⊗[N] F' ≃ₐ[N₁] ∀ i, @KummerFactor O _ (ϖ ^ m i) (d i) N₁ _
          (nodeAlgebra N₁ (ϖ ^ m i) (d i) (by rw [← pow_mul, hmd i]; exact huv)))

section Main

open Algebra.TensorProduct

/-- `C → B ⊗_A C` is étale if `A → B` is. -/
theorem etale_includeRight {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] (h : (algebraMap A B).Etale) :
    (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom.Etale := by
  have h₁ : (includeLeftRingHom : C →+* C ⊗[A] B).Etale :=
    RingHom.Etale.isStableUnderBaseChange.tensorProduct C h
  have e : (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom =
      (Algebra.TensorProduct.comm A C B).toRingHom.comp includeLeftRingHom := by
    ext c
    simp
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ h₁
    (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm A C B).bijective)

variable {O : Type u} [CommRing O]

/-- The node charts `Node O (c ^ d) → N₁` for the different ways of writing `ϖ ^ n`. -/
theorem lift_etale_of_eq {N₁ : Type u} [CommRing N₁] [Algebra O N₁] {u₁ v₁ : N₁} {a b : O}
    (hab : a = b) (ha : u₁ * v₁ = algebraMap O N₁ a) (hb : u₁ * v₁ = algebraMap O N₁ b)
    (h : (Node.lift u₁ v₁ ha).toRingHom.Etale) : (Node.lift u₁ v₁ hb).toRingHom.Etale := by
  subst hab
  exact h

/-- **W8 at a node (Kummer case).** If the cover `F'` of `N` is Kummer at the node point `𝔪`, every
prime `𝔮` of the normalization of `N` in `F'` over `𝔪` is étale-locally the singular point of a node
`O[w, z] ⧸ (w z - ϖ ^ m)` with `m d = n` (`d ≥ 1` the local degree: the thickness of the base
node is `d` times that of the node above it). -/
theorem IsKummerAt.exists_isEtaleLocallyAt [IsDomain O] [IsIntegrallyClosed O] {ϖ : O}
    (hϖ : ϖ ≠ 0) {n : ℕ} {N : Type u} [CommRing N] [Algebra O N] {F' : Type u} [CommRing F']
    [Algebra N F'] [Algebra O F'] [IsScalarTower O N F'] {𝔪 : Ideal N} (h : IsKummerAt ϖ n F' 𝔪)
    (𝔮 : Ideal (integralClosure N F')) [𝔮.IsPrime]
    (h𝔮 : 𝔮.comap (algebraMap N (integralClosure N F')) = 𝔪) :
    ∃ m d : ℕ, 0 < d ∧ m * d = n ∧
      ∃ (C : Type u) (_ : CommRing C) (g : integralClosure N F' →+* C)
        (f : Node O (ϖ ^ m) →+* C) (𝔔 : Ideal C),
        g.Etale ∧ f.Etale ∧ 𝔔.IsPrime ∧ 𝔔.comap g = 𝔮 ∧
        f.comp (algebraMap O _) = g.comp (algebraMap O _) ∧
        Node.u (ϖ ^ m) ∈ 𝔔.comap f ∧ Node.v (ϖ ^ m) ∈ 𝔔.comap f := by
  classical
  obtain ⟨N₁, _, _, hN₁, 𝔫, _, h𝔫, h⟩ := h
  letI : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
  obtain ⟨u₁, v₁, huv, hf, hu𝔫, hv𝔫, r, m, d, hd, hmd, ⟨e⟩⟩ := h
  have hi : ∀ i, u₁ * v₁ = algebraMap O N₁ ((ϖ ^ m i) ^ d i) := fun i ↦ by
    rw [← pow_mul, hmd i]; exact huv
  have hfi : ∀ i, (Node.lift u₁ v₁ (hi i)).toRingHom.Etale := fun i ↦
    lift_etale_of_eq (by rw [← pow_mul, hmd i]) huv (hi i) hf
  -- the normalization of the base change
  let Ψ₀ : N₁ ⊗[N] (integralClosure N F') ≃ₐ[N₁] integralClosure N₁ (N₁ ⊗[N] F') :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure N N₁ F')
      TensorProduct.toIntegralClosure_bijective_of_smooth
  let Ψ₃ : ∀ i, integralClosure N₁
      (@KummerFactor O _ (ϖ ^ m i) (d i) N₁ _ (nodeAlgebra N₁ _ _ (hi i))) ≃ₐ[N₁]
      @KummerNodeFactor O _ (ϖ ^ m i) (d i) N₁ _ (nodeAlgebra N₁ _ _ (hi i)) := fun i ↦
    letI := nodeAlgebra N₁ (ϖ ^ m i) (d i) (hi i)
    haveI : Algebra.Etale (Node O ((ϖ ^ m i) ^ d i)) N₁ := hfi i
    (kummerFactorEquiv (c := ϖ ^ m i) (d := d i) N₁ (pow_ne_zero _ hϖ) (hd i)).symm
  let Ψ : N₁ ⊗[N] (integralClosure N F') ≃ₐ[N₁]
      ∀ i, @KummerNodeFactor O _ (ϖ ^ m i) (d i) N₁ _ (nodeAlgebra N₁ _ _ (hi i)) :=
    Ψ₀.trans (e.mapIntegralClosure.trans
      (integralClosurePiEquiv.trans (AlgEquiv.piCongrRight Ψ₃)))
  -- a prime over `𝔫` and `𝔮`
  obtain ⟨R, hR, hR₁, hR₂⟩ := exists_isPrime_tensorProduct (A := N) (B := N₁) (C := (integralClosure N F')) 𝔫 𝔮
    (by rw [h𝔫, h𝔮])
  set R' : Ideal (∀ i, @KummerNodeFactor O _ (ϖ ^ m i) (d i) N₁ _ (nodeAlgebra N₁ _ _ (hi i))) :=
    R.comap Ψ.symm.toRingEquiv.toRingHom
  haveI : R'.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨i, Q, hQ, hR'⟩ := exists_eq_comap_evalRingHom R'
  letI := nodeAlgebra N₁ (ϖ ^ m i) (d i) (hi i)
  have hN₁' : (algebraMap N N₁).Etale := RingHom.etale_algebraMap.mpr hN₁
  have hR'R : R'.comap Ψ.toRingEquiv.toRingHom = R := by
    ext x
    simp [R']
  -- `N₁ → C` and its compatibility with `Ψ`
  have hΨalg : ∀ y : N₁, Pi.evalRingHom _ i (Ψ (algebraMap N₁ (N₁ ⊗[N] (integralClosure N F')) y)) =
      algebraMap N₁ (KummerNodeFactor (c := ϖ ^ m i) (d := d i) N₁) y := fun y ↦ by
    rw [Ψ.commutes]
    rfl
  have hmemQ : ∀ y ∈ 𝔫, algebraMap N₁ (KummerNodeFactor (c := ϖ ^ m i) (d := d i) N₁) y ∈ Q := by
    intro y hy
    have h1 : algebraMap N₁ (N₁ ⊗[N] (integralClosure N F')) y ∈ R := by
      rw [← hR₁] at hy; exact hy
    have h2 : Ψ (algebraMap N₁ (N₁ ⊗[N] (integralClosure N F')) y) ∈ R' := by
      change Ψ.symm (Ψ _) ∈ R
      rwa [AlgEquiv.symm_apply_apply]
    rw [hR'] at h2
    rw [← hΨalg]
    exact h2
  -- the base coordinates are `d`-th powers
  have hu : (algebraMap N₁ (KummerNodeFactor (c := ϖ ^ m i) (d := d i) N₁) u₁) =
      ((1 : N₁) ⊗ₜ[Node O ((ϖ ^ m i) ^ d i)] KNode.u (ϖ ^ m i) (d i)) ^ d i := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
    rw [KNode.u_pow, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    change u₁ ⊗ₜ 1 = _
    congr 1
    exact (Node.lift_u u₁ v₁ (hi i)).symm
  have hv : (algebraMap N₁ (KummerNodeFactor (c := ϖ ^ m i) (d := d i) N₁) v₁) =
      ((1 : N₁) ⊗ₜ[Node O ((ϖ ^ m i) ^ d i)] KNode.v (ϖ ^ m i) (d i)) ^ d i := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
    rw [KNode.v_pow, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    change v₁ ⊗ₜ 1 = _
    congr 1
    exact (Node.lift_v u₁ v₁ (hi i)).symm
  refine ⟨m i, d i, hd i, hmd i, KummerNodeFactor (c := ϖ ^ m i) (d := d i) N₁, inferInstance,
    (Pi.evalRingHom _ i).comp (Ψ.toRingEquiv.toRingHom.comp
      (includeRight : (integralClosure N F') →ₐ[N] N₁ ⊗[N] (integralClosure N F')).toRingHom),
    (includeRight : KNode (ϖ ^ m i) (d i) →ₐ[Node O ((ϖ ^ m i) ^ d i)]
      KummerNodeFactor (c := ϖ ^ m i) (d := d i) N₁).toRingHom, Q, ?_, ?_, hQ, ?_, ?_, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _ (etale_includeRight hN₁')
        (RingHom.Etale.of_bijective Ψ.bijective)) (etale_evalRingHom i)
  · exact etale_includeRight (C := KNode (ϖ ^ m i) (d i)) (hfi i)
  · rw [← Ideal.comap_comap, ← Ideal.comap_comap, ← hR', hR'R]
    exact hR₂
  · ext o
    have eL : (includeRight : KNode (ϖ ^ m i) (d i) →ₐ[Node O ((ϖ ^ m i) ^ d i)]
        KummerNodeFactor (c := ϖ ^ m i) (d := d i) N₁) (algebraMap O (Node O (ϖ ^ m i)) o) =
        algebraMap N₁ (KummerNodeFactor (c := ϖ ^ m i) (d := d i) N₁) (algebraMap O N₁ o) := by
      rw [← (Node.kummer (ϖ ^ m i) (d i)).commutes o]
      change (includeRight : KNode (ϖ ^ m i) (d i) →ₐ[Node O ((ϖ ^ m i) ^ d i)] _)
        (algebraMap (Node O ((ϖ ^ m i) ^ d i)) (KNode (ϖ ^ m i) (d i))
          (algebraMap O (Node O ((ϖ ^ m i) ^ d i)) o)) = _
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      change (Node.lift u₁ v₁ (hi i)) (algebraMap O _ o) ⊗ₜ 1 = algebraMap O N₁ o ⊗ₜ 1
      rw [AlgHom.commutes]
    have eR : Pi.evalRingHom _ i (Ψ ((includeRight : (integralClosure N F') →ₐ[N]
        N₁ ⊗[N] (integralClosure N F')) (algebraMap O (integralClosure N F') o))) =
        algebraMap N₁ (KummerNodeFactor (c := ϖ ^ m i) (d := d i) N₁) (algebraMap O N₁ o) := by
      rw [IsScalarTower.algebraMap_apply O N (integralClosure N F'), AlgHom.commutes,
        IsScalarTower.algebraMap_apply N N₁ (N₁ ⊗[N] (integralClosure N F'))]
      exact hΨalg _
    exact eL.trans eR.symm
  · refine hQ.mem_of_pow_mem (d i) ?_
    change ((1 : N₁) ⊗ₜ[Node O ((ϖ ^ m i) ^ d i)] KNode.u (ϖ ^ m i) (d i)) ^ d i ∈ Q
    rw [← hu]
    exact hmemQ u₁ hu𝔫
  · refine hQ.mem_of_pow_mem (d i) ?_
    change ((1 : N₁) ⊗ₜ[Node O ((ϖ ^ m i) ^ d i)] KNode.v (ϖ ^ m i) (d i)) ^ d i ∈ Q
    rw [← hv]
    exact hmemQ v₁ hv𝔫

end Main

end SemistableReduction
