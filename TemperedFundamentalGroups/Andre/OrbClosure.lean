/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.Components
import TemperedFundamentalGroups.Tempered.InducedAlg

/-!
# Galois closures over an orbifold `[Spec R / A]` (Blueprint §11.3, G6, orbifold case)

A finite étale `R`-algebra `B₀` with a semilinear automorphism over every `a ∈ A` has a Galois
closure `B` (connected, `Aut_R(B)` transitive on the geometric points, every geometric point of
`B₀` factoring through the base point of `B`) **on which every `a ∈ A` lifts to a semilinear
automorphism** (`exists_galoisClosure_sym`): `B` is Galois over `[Spec R / A]`.

The construction is that of `Components.exists_galoisClosure` (the component `ε` of the tensor
power `T = ⨂_{i < d} B₀` through the tuple of all `d` geometric points); the semilinear
automorphism `λ_a` of `B₀` acts on `T` factorwise (`powMap`), moves `ε` to a component through a
tuple of *twisted* points, which is again injective (`twisted_injective`, a ring-level form of
the diagonal idempotent, `diag_ring`), hence a permutation of `ε`; composing with the permutation
of the factors gives a semilinear endomorphism of `B = T ⧸ (1 - ε)`, bijective by the Galois
property.
-/

universe u

open CategoryTheory TensorProduct Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

namespace Components

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]

section Diag

variable {B₀ : Type u} [CommRing B₀] [Algebra R B₀] {F : Type u} [Field F]

/-- **The diagonal idempotent at ring-valued points**: for `τ ∈ B₀ ⊗ B₀` with
`τ (b ⊗ 1 - 1 ⊗ b) = 0` and `μ τ = 1`, a ring map `φ : B₀ ⊗ B₀ → F` to a field takes the value
`1` at `τ` iff it agrees on both factors. -/
lemma diag_ring {τ : B₀ ⊗[R] B₀} (hτ : ∀ b : B₀, (1 ⊗ₜ b - b ⊗ₜ 1) * τ = 0)
    (hτ₁ : Algebra.TensorProduct.lmul' R τ = 1) (φ : B₀ ⊗[R] B₀ →+* F) :
    φ τ = 1 ↔ ∀ b, φ (b ⊗ₜ 1) = φ (1 ⊗ₜ b) := by
  constructor
  · intro h b
    have := congrArg φ (hτ b)
    rw [map_mul, h, mul_one, map_sub, map_zero, sub_eq_zero] at this
    exact this.symm
  · intro h
    have key : ∀ x : B₀ ⊗[R] B₀, φ x = φ ((Algebra.TensorProduct.lmul' R x) ⊗ₜ 1) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b c =>
        have hbc : b ⊗ₜ[R] c = (b ⊗ₜ[R] (1 : B₀)) * ((1 : B₀) ⊗ₜ[R] c) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        conv_lhs => rw [hbc, map_mul, ← h c, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul]
        rw [Algebra.TensorProduct.lmul'_apply_tmul]
      | add x y hx hy =>
        rw [map_add, hx, hy, map_add, TensorProduct.add_tmul, map_add]
    rw [key, hτ₁, ← Algebra.TensorProduct.one_def, map_one]

lemma diag_ring_eq_zero_or_one {τ : B₀ ⊗[R] B₀} (hτ₁ : Algebra.TensorProduct.lmul' R τ = 1)
    (hτ : ∀ b : B₀, (1 ⊗ₜ b - b ⊗ₜ 1) * τ = 0) (φ : B₀ ⊗[R] B₀ →+* F) : φ τ = 0 ∨ φ τ = 1 := by
  have hidem : IsIdempotentElem τ := by
    change τ * τ = τ
    rw [mul_eq_lmul'_tmul_one_mul hτ, hτ₁, ← Algebra.TensorProduct.one_def, one_mul]
  exact IsIdempotentElem.iff_eq_zero_or_one.1 (hidem.map φ)

end Diag

section Twist

variable {B₀ : Type u} [CommRing B₀] [Algebra R B₀]

/-- A semilinear automorphism `σ` over `a`, as an `R`-algebra map `B₀ → B₀^{(a⁻¹)}`. -/
def σTw (σ : SemilinearAut R A B₀) : B₀ →ₐ[R] TwAlg B₀ σ.a⁻¹ :=
  { (σ.σ : B₀ →+* B₀) with
    commutes' := fun r => by
      change σ.σ (algebraMap R B₀ r) = algebraMap R B₀ ((σ.a⁻¹)⁻¹ • r)
      rw [σ.map_algebraMap, inv_inv] }

/-- An `R`-algebra map, as an `R`-algebra map of twisted algebras. -/
def twMap {C : Type u} [CommRing C] [Algebra R C] (g : B₀ →ₐ[R] C) (a : A) :
    TwAlg B₀ a →ₐ[R] TwAlg C a :=
  { (g : B₀ →+* C) with
    commutes' := fun r => g.commutes (a⁻¹ • r) }

variable {d : ℕ}

/-- **The factorwise action** of a semilinear automorphism on the tensor power. -/
def powMap (σ : SemilinearAut R A B₀) : Pow R B₀ d →+* Pow R B₀ d :=
  ((lift fun i => (twMap (ι i) σ.a⁻¹).comp (σTw σ)) :
    Pow R B₀ d →ₐ[R] TwAlg (Pow R B₀ d) σ.a⁻¹).toRingHom

lemma powMap_ι (σ : SemilinearAut R A B₀) (i : Fin d) (b : B₀) :
    powMap σ (ι i b) = ι i (σ.σ b) :=
  lift_ι_apply (S := TwAlg (Pow R B₀ d) σ.a⁻¹) _ i b

lemma powMap_algebraMap (σ : SemilinearAut R A B₀) (r : R) :
    powMap (d := d) σ (algebraMap R _ r) = algebraMap R _ (σ.a • r) := by
  have := ((lift fun i => (twMap (ι i) σ.a⁻¹).comp (σTw σ)) :
    Pow R B₀ d →ₐ[R] TwAlg (Pow R B₀ d) σ.a⁻¹).commutes r
  rw [twAlg_algebraMap, inv_inv] at this
  exact this

lemma powMap_symm_comp (σ : SemilinearAut R A B₀) (x : Pow R B₀ d) :
    powMap σ⁻¹ (powMap σ x) = x := by
  let φ : Pow R B₀ d →ₐ[R] Pow R B₀ d :=
    { (powMap σ⁻¹).comp (powMap σ) with
      commutes' := fun r => by
        change powMap σ⁻¹ (powMap σ (algebraMap R _ r)) = _
        rw [powMap_algebraMap, powMap_algebraMap, SemilinearAut.inv_a, inv_smul_smul] }
  have h : φ = AlgHom.id R _ := hom_ext fun i => by
    ext b
    change powMap σ⁻¹ (powMap σ (ι i b)) = ι i b
    rw [powMap_ι, powMap_ι, SemilinearAut.inv_σ, RingEquiv.symm_apply_apply]
  exact DFunLike.congr_fun h x

/-- The factorwise action as a ring automorphism. -/
def powEquiv (σ : SemilinearAut R A B₀) : Pow R B₀ d ≃+* Pow R B₀ d :=
  RingEquiv.ofRingHom (powMap σ) (powMap σ⁻¹)
    (RingHom.ext fun x => by
      have := powMap_symm_comp (d := d) σ⁻¹ x
      rwa [inv_inv] at this)
    (RingHom.ext fun x => powMap_symm_comp σ x)

lemma powEquiv_apply (σ : SemilinearAut R A B₀) (x : Pow R B₀ d) :
    powEquiv σ x = powMap σ x := rfl

end Twist

section Closure

variable [IsDomain R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
  {B₀ : Type u} [CommRing B₀] [Algebra R B₀] [Algebra.Etale R B₀] [Module.Finite R B₀]

/-- **Galois closure over `[Spec R / A]`**: a finite étale `B₀` with a geometric point and with a
semilinear automorphism over every `a ∈ A` has a Galois closure `B` with a semilinear
automorphism over every `a ∈ A`. -/
theorem exists_galoisClosure_sym (lam : A → SemilinearAut R A B₀) (hlam : ∀ a, (lam a).a = a)
    [Nonempty (B₀ →ₐ[R] Ω)] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra.Etale R B)
      (_ : Module.Finite R B) (t₀ : B →ₐ[R] Ω),
      (∀ s : B₀ →ₐ[R] Ω, ∃ g : B₀ →ₐ[R] B, t₀.comp g = s) ∧
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
      (∀ t t' : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t.comp (σ : B →ₐ[R] B) = t') ∧
      ∀ a : A, ∃ γ : SemilinearAut R A B, γ.a = a := by
  classical
  let d := Nat.card (B₀ →ₐ[R] Ω)
  let en : (B₀ →ₐ[R] Ω) ≃ Fin d := Finite.equivFin _
  let T := Pow R B₀ d
  let sT : T →ₐ[R] Ω := lift fun i => en.symm i
  obtain ⟨ε, hε, hsε⟩ := exists_isPrimitive sT
  obtain ⟨τ, hτ, hτ₁⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R)
    (S := B₀)).1 inferInstance
  let L : Fin d → Fin d → (B₀ ⊗[R] B₀ →ₐ[R] T) := fun i j =>
    Algebra.TensorProduct.lift (ι i) (ι j) (fun _ _ => Commute.all _ _)
  have hval : ∀ (w : T →+* Ω) (i j : Fin d), w (L i j τ) = 1 ↔
      ∀ b, w (ι i b) = w (ι j b) := fun w i j => by
    have := diag_ring hτ hτ₁ (w.comp (L i j : B₀ ⊗[R] B₀ →+* T))
    simpa [L] using this
  have h01 : ∀ (w : T →+* Ω) (i j : Fin d), w (L i j τ) = 0 ∨ w (L i j τ) = 1 := fun w i j =>
    diag_ring_eq_zero_or_one hτ₁ hτ (w.comp (L i j : B₀ ⊗[R] B₀ →+* T))
  -- ring-valued points through `ε` have injective tuples
  have hinj : ∀ w : T →+* Ω, w ε = 1 → ∀ i j : Fin d, (∀ b, w (ι i b) = w (ι j b)) → i = j := by
    intro w hw i j hij
    by_contra hne
    have hsT : sT (L i j τ) = 0 := by
      refine (h01 sT i j).resolve_right fun h => hne ?_
      have h' := (hval sT i j).1 h
      refine en.symm.injective (AlgHom.ext fun b => ?_)
      exact (lift_ι_apply (S := Ω) (fun i => en.symm i) i b).symm.trans
        ((h' b).trans (lift_ι_apply (S := Ω) (fun i => en.symm i) j b))
    have hidem : IsIdempotentElem (L i j τ) := by
      have : IsIdempotentElem τ := by
        change τ * τ = τ
        rw [mul_eq_lmul'_tmul_one_mul hτ, hτ₁, ← Algebra.TensorProduct.one_def, one_mul]
      exact this.map _
    have hf : (1 - L i j τ) * ε = ε := by
      refine (hε.2 _ hidem.one_sub).resolve_left fun h0 => ?_
      have := congrArg sT h0
      rw [map_mul, map_sub, map_one, hsT, hsε, map_zero] at this
      norm_num at this
    have h1 : w (L i j τ) = 0 := by
      have := congrArg w hf
      rw [map_mul, hw, mul_one, map_sub, map_one] at this
      linear_combination -this
    have h2 : w (L i j τ) = 1 := (hval w i j).2 hij
    rw [h1] at h2
    exact zero_ne_one h2
  have hbij : ∀ u : T →ₐ[R] Ω, u ε = 1 → Function.Bijective fun i => u.comp (ι i) := by
    intro u hu
    refine Function.Injective.bijective_of_nat_card_le (fun i j hij => ?_) (by simp [d])
    exact hinj (u : T →+* Ω) hu i j fun b => DFunLike.congr_fun hij b
  -- permutations of the factors
  have hperm : ∀ u u' : T →ₐ[R] Ω, u ε = 1 → u' ε = 1 →
      ∃ Pe : T ≃ₐ[R] T, u.comp (Pe : T →ₐ[R] T) = u' := by
    intro u u' hu hu'
    let x := Equiv.ofBijective _ (hbij u hu)
    let x' := Equiv.ofBijective _ (hbij u' hu')
    let π : Fin d ≃ Fin d := x'.trans x.symm
    have hπ : ∀ i, u.comp (ι (π i)) = u'.comp (ι i) := fun i => by
      change x (x.symm (x' i)) = x' i
      rw [Equiv.apply_symm_apply]
    refine ⟨AlgEquiv.ofAlgHom (lift fun i => ι (π i)) (lift fun i => ι (π.symm i))
      (hom_ext fun i => by
        ext a
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, lift_ι_apply, lift_ι_apply,
          Equiv.apply_symm_apply]
        rfl)
      (hom_ext fun i => by
        ext a
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, lift_ι_apply, lift_ι_apply,
          Equiv.symm_apply_apply]
        rfl), hom_ext fun i => ?_⟩
    ext a
    change u ((lift (R := R) (B₀ := B₀) (S := T) fun i => ι (π i)) (ι i a)) = _
    rw [lift_ι_apply]
    exact DFunLike.congr_fun (hπ i) a
  let B := T ⧸ Ideal.span {1 - ε}
  haveI : Algebra.Etale R B := quotient_etale hε.1
  have hdesc : ∀ Θ : T ≃+* T, Θ ε = ε →
      Ideal.span {1 - ε} = (Ideal.span {1 - ε}).map (Θ : T →+* T) := fun Θ hΘ => by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change 1 - ε = Θ (1 - ε)
    rw [map_sub, map_one, hΘ]
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, liftPoint sT hsε,
    fun s₀ => ⟨(Ideal.Quotient.mkₐ R _).comp (ι (en s₀)), ?_⟩, isConnected_quotient hε,
    fun v v' => ?_, fun a => ?_⟩
  · ext a
    change sT (ι (en s₀) a) = s₀ a
    rw [lift_ι_apply, Equiv.symm_apply_apply]
  · let u := v.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - ε}))
    let u' := v'.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - ε}))
    have hu : u ε = 1 := comp_mk_eps v
    have hu' : u' ε = 1 := comp_mk_eps v'
    obtain ⟨Pe, huPe⟩ := hperm u u' hu hu'
    have hPeε : Pe ε = ε := by
      refine (hε.map Pe).eq hε u ?_ hu
      change (u.comp (Pe : T →ₐ[R] T)) ε = 1
      rw [huPe, hu']
    have hI := hdesc Pe.toRingEquiv hPeε
    refine ⟨Ideal.quotientEquivAlg _ _ Pe hI, Ideal.Quotient.algHom_ext R
      (AlgHom.ext fun y => ?_)⟩
    change v (Ideal.quotientEquivAlg _ _ Pe hI (Ideal.Quotient.mk _ y)) = u' y
    rw [Ideal.quotientEquivAlg_mk, ← huPe]
    rfl
  · -- the semilinear lift of `a`
    let Γ : T ≃+* T := powEquiv (lam a)
    have hΓε : IsPrimitive (Γ ε) := hε.map_ringEquiv Γ
    have hΓ0 : Γ ε ≠ 0 := fun h => by
      have : ε = 0 := Γ.injective (h.trans (map_zero Γ).symm)
      rw [this, map_zero] at hsε
      exact zero_ne_one hsε
    obtain ⟨u, hu⟩ : ∃ u : T →ₐ[R] Ω, u (Γ ε) = 1 := by
      by_contra hno
      push Not at hno
      exact hΓ0 (eq_zero_of_forall_algHom hΓε.1 fun u =>
        (idem_eq_zero_or_one hΓε.1 u).resolve_right (hno u))
    -- the tuple of `u` is injective
    have hw : ((u : T →+* Ω).comp (Γ : T →+* T)) ε = 1 := hu
    have hbu : Function.Bijective fun i => u.comp (ι i) := by
      refine Function.Injective.bijective_of_nat_card_le (fun i j hij => ?_) (by simp [d])
      refine hinj _ hw i j fun b => ?_
      change u (Γ (ι i b)) = u (Γ (ι j b))
      rw [powEquiv_apply, powEquiv_apply, powMap_ι, powMap_ι]
      exact DFunLike.congr_fun hij _
    -- a permutation moving `ε` to `Γ ε`
    let x := Equiv.ofBijective _ hbu
    let x' := Equiv.ofBijective _ (hbij sT hsε)
    let π : Fin d ≃ Fin d := x'.trans x.symm
    have hπ : ∀ i, u.comp (ι (π i)) = sT.comp (ι i) := fun i => by
      change x (x.symm (x' i)) = x' i
      rw [Equiv.apply_symm_apply]
    let Pe : T ≃ₐ[R] T := AlgEquiv.ofAlgHom (lift fun i => ι (π i)) (lift fun i => ι (π.symm i))
      (hom_ext fun i => by
        ext a
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, lift_ι_apply, lift_ι_apply,
          Equiv.apply_symm_apply]
        rfl)
      (hom_ext fun i => by
        ext a
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, lift_ι_apply, lift_ι_apply,
          Equiv.symm_apply_apply]
        rfl)
    have huPe : u.comp (Pe : T →ₐ[R] T) = sT := hom_ext fun i => by
      ext a
      change u ((lift (R := R) (B₀ := B₀) (S := T) fun i => ι (π i)) (ι i a)) = _
      rw [lift_ι_apply]
      exact DFunLike.congr_fun (hπ i) a
    have hPe : Pe ε = Γ ε := by
      refine (hε.map Pe).eq hΓε u ?_ hu
      change (u.comp (Pe : T →ₐ[R] T)) ε = 1
      rw [huPe, hsε]
    let Φ : T ≃+* T := Γ.trans Pe.symm.toRingEquiv
    have hΦ : Φ ε = ε := by
      change Pe.symm (Γ ε) = ε
      rw [← hPe, AlgEquiv.symm_apply_apply]
    let Φb : B ≃+* B := Ideal.quotientEquiv _ _ Φ (hdesc Φ hΦ)
    refine ⟨⟨a, Φb, fun r => ?_⟩, rfl⟩
    change Φb (Ideal.Quotient.mk _ (algebraMap R T r)) = Ideal.Quotient.mk _ (algebraMap R T (a • r))
    change Ideal.Quotient.mk _ (Φ (algebraMap R T r)) = _
    congr 1
    change Pe.symm (powMap (lam a) (algebraMap R T r)) = _
    rw [powMap_algebraMap, hlam, AlgEquiv.commutes]

end Closure

end Components

end

end TemperedFundamentalGroups
