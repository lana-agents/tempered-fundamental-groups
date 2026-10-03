/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.GaloisClass

/-!
# Connected components and Galois closures of finite étale algebras

Let `R` be a domain and `Ω` an algebraically closed field which is an `R`-algebra (a geometric
point of `Spec R`). For a finite étale `R`-algebra `C`:

* `nonempty_algHom_of_nontrivial`: a nonzero finite flat `R`-algebra has a geometric point
  (lying over, then `IsAlgClosed.lift`);
* `eq_zero_of_forall_algHom`: an idempotent of `C` vanishing at all geometric points is `0`;
* `exists_primitive`: every geometric point `s` lies on a **primitive** idempotent `ε`
  (`f * ε ∈ {0, ε}` for all idempotents `f`), i.e. a connected component `C ⧸ (1 - ε)`
  (`isConnected_quotient`);
* `exists_galoisClosure`: a finite étale `R`-algebra `B₀` with a geometric point `s₀` maps to a
  connected finite étale `B*` with a point `t₀` over `s₀` on whose geometric fibre `Aut_R(B*)`
  acts transitively: the connected component through an injective tuple of points of the tensor
  power `⨂_{i < d} B₀`, `d = #(B₀ →ₐ[R] Ω)`.
-/

universe u

open CategoryTheory

namespace TemperedFundamentalGroups

noncomputable section

namespace Components

variable {R : Type u} [CommRing R] [IsDomain R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  [Algebra R Ω]

/-- **A nonzero finite flat algebra over a domain has a geometric point.** -/
theorem nonempty_algHom_of_nontrivial (C : Type u) [CommRing C] [Algebra R C] [Module.Finite R C]
    [Module.Flat R C] [Nontrivial C] : Nonempty (C →ₐ[R] Ω) := by
  classical
  let p : Ideal R := RingHom.ker (algebraMap R Ω)
  haveI : p.IsPrime := RingHom.ker_isPrime _
  haveI : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  haveI : FaithfulSMul R C := inferInstance
  obtain ⟨⟨Q, hQ, hQp⟩⟩ := (inferInstance : Nonempty (p.primesOver C))
  letI : Algebra (R ⧸ p) Ω := (RingHom.kerLift (algebraMap R Ω)).toAlgebra
  haveI : IsScalarTower R (R ⧸ p) Ω := IsScalarTower.of_algebraMap_eq fun r =>
    (RingHom.kerLift_mk (algebraMap R Ω) r).symm
  haveI : FaithfulSMul (R ⧸ p) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective _)
  haveI : Module.IsTorsionFree (R ⧸ p) Ω := Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (R ⧸ p) (C ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  let g : C ⧸ Q →ₐ[R ⧸ p] Ω := IsAlgClosed.lift (R := R ⧸ p) (S := C ⧸ Q) (M := Ω)
  refine ⟨{ (g : C ⧸ Q →+* Ω).comp (Ideal.Quotient.mk Q) with commutes' := fun r => ?_ }⟩
  change g (Ideal.Quotient.mk Q (algebraMap R C r)) = algebraMap R Ω r
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply R C,
    IsScalarTower.algebraMap_apply R (R ⧸ p) (C ⧸ Q), g.commutes]
  rfl

variable {C : Type u} [CommRing C] [Algebra R C] [Algebra.Etale R C] [Module.Finite R C]

omit [IsDomain R] [IsAlgClosed Ω] [Algebra.Etale R C] [Module.Finite R C] in
lemma idem_eq_zero_or_one {e : C} (he : IsIdempotentElem e) (t : C →ₐ[R] Ω) :
    t e = 0 ∨ t e = 1 :=
  IsIdempotentElem.iff_eq_zero_or_one.1 (he.map t)

lemma quotient_nontrivial {ε : C} (hε : IsIdempotentElem ε) (h0 : ε ≠ 0) :
    Nontrivial (C ⧸ Ideal.span {1 - ε}) := by
  refine Ideal.Quotient.nontrivial_iff.2 fun h => h0 ?_
  rw [Ideal.span_singleton_eq_top] at h
  have := (IsIdempotentElem.iff_eq_one_of_isUnit h).1 hε.one_sub
  rw [sub_eq_self] at this
  exact this

omit [IsDomain R] [Module.Finite R C] in
lemma quotient_etale {ε : C} (hε : IsIdempotentElem ε) :
    Algebra.Etale R (C ⧸ Ideal.span {1 - ε}) := by
  haveI := IsLocalization.Away.quotient_of_isIdempotentElem hε
  haveI : Algebra.Etale C (C ⧸ Ideal.span {1 - ε}) := Algebra.Etale.of_isLocalizationAway ε
  exact Algebra.Etale.comp R C _

/-- An idempotent vanishing at all geometric points is `0`. -/
theorem eq_zero_of_forall_algHom {ε : C} (hε : IsIdempotentElem ε)
    (h : ∀ t : C →ₐ[R] Ω, t ε = 0) : ε = 0 := by
  by_contra h0
  haveI := quotient_nontrivial hε h0
  haveI := quotient_etale (R := R) hε
  obtain ⟨t⟩ := nonempty_algHom_of_nontrivial (R := R) (Ω := Ω) (C ⧸ Ideal.span {1 - ε})
  have h1 : t (Ideal.Quotient.mk _ ε) = 1 := by
    have : Ideal.Quotient.mk (Ideal.span {1 - ε}) (1 - ε) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [map_sub, map_one, sub_eq_zero] at this
    rw [← this, map_one]
  have := h (t.comp (Ideal.Quotient.mkₐ R _))
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, h1] at this
  exact one_ne_zero this

/-- A **primitive idempotent**: a nonzero minimal idempotent, i.e. a connected component. -/
def IsPrimitive {S : Type*} [CommRing S] (ε : S) : Prop :=
  IsIdempotentElem ε ∧ ∀ f : S, IsIdempotentElem f → f * ε = 0 ∨ f * ε = ε

omit [IsDomain R] [IsAlgClosed Ω] [Algebra.Etale R C] [Module.Finite R C] in
/-- Two primitive idempotents through a common geometric point are equal. -/
lemma IsPrimitive.eq {ε ε' : C} (h : IsPrimitive ε) (h' : IsPrimitive ε') (t : C →ₐ[R] Ω)
    (ht : t ε = 1) (ht' : t ε' = 1) : ε = ε' := by
  have h₁ : ε' * ε = ε := (h.2 ε' h'.1).resolve_left fun h0 => by
    have := congrArg t h0
    rw [map_mul, ht, ht', map_zero, one_mul] at this
    exact one_ne_zero this
  have h₂ : ε * ε' = ε' := (h'.2 ε h.1).resolve_left fun h0 => by
    have := congrArg t h0
    rw [map_mul, ht, ht', map_zero, one_mul] at this
    exact one_ne_zero this
  rw [← h₁, mul_comm, h₂]

omit [IsDomain R] [IsAlgClosed Ω] [Algebra.Etale R C] [Module.Finite R C] in
lemma IsPrimitive.map {ε : C} (h : IsPrimitive ε) (σ : C ≃ₐ[R] C) : IsPrimitive (σ ε) := by
  refine ⟨h.1.map σ, fun f hf => ?_⟩
  rcases h.2 (σ.symm f) (hf.map σ.symm) with h0 | h0
  · left
    have := congrArg σ h0
    rwa [map_mul, AlgEquiv.apply_symm_apply, map_zero] at this
  · right
    have := congrArg σ h0
    rwa [map_mul, AlgEquiv.apply_symm_apply] at this

/-- **Every geometric point lies on a connected component**: there is a primitive idempotent `ε`
with `s ε = 1`. -/
theorem exists_isPrimitive (s : C →ₐ[R] Ω) : ∃ ε : C, IsPrimitive ε ∧ s ε = 1 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ ε : C, IsIdempotentElem ε ∧ s ε = 1 ∧ Set.ncard {t : C →ₐ[R] Ω | t ε = 1} = n
  have hP : ∃ n, P n := ⟨_, 1, IsIdempotentElem.one, map_one s, rfl⟩
  obtain ⟨ε, hε, hsε, hn⟩ := Nat.find_spec hP
  have key : ∀ a : C, IsIdempotentElem a → a * ε = a → s a = 1 → a = ε := by
    intro a ha haε hsa
    have hsub : {t : C →ₐ[R] Ω | t a = 1} ⊆ {t | t ε = 1} := fun t (hta : t a = 1) => by
      have := congrArg t haε
      rw [map_mul, hta, one_mul] at this
      exact this
    have hle : Nat.find hP ≤ Set.ncard {t : C →ₐ[R] Ω | t a = 1} :=
      Nat.find_min' hP ⟨a, ha, hsa, rfl⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hn]; exact hle) (Set.toFinite _)
    have hb : IsIdempotentElem (ε - a) := by
      unfold IsIdempotentElem at hε ha ⊢
      linear_combination hε - 2 * haε + ha + 0 * (mul_comm a ε)
    have h0 : ε - a = 0 := eq_zero_of_forall_algHom (R := R) (Ω := Ω) hb fun t => by
      rw [map_sub]
      rcases idem_eq_zero_or_one hε t with h | h
      · have := congrArg t haε
        rw [map_mul, h, mul_zero] at this
        rw [h, ← this, sub_zero]
      · have : t ∈ {t : C →ₐ[R] Ω | t a = 1} := by rw [heq]; exact h
        rw [h, show t a = 1 from this, sub_self]
    exact (sub_eq_zero.1 h0).symm
  refine ⟨ε, ⟨hε, fun f hf => ?_⟩, hsε⟩
  have ha : IsIdempotentElem (f * ε) := hf.mul hε
  have haε : f * ε * ε = f * ε := by rw [mul_assoc, hε.eq]
  rcases idem_eq_zero_or_one ha s with h | h
  · left
    have hb : IsIdempotentElem ((1 - f) * ε) := hf.one_sub.mul hε
    have hbε : (1 - f) * ε * ε = (1 - f) * ε := by rw [mul_assoc, hε.eq]
    have hsb : s ((1 - f) * ε) = 1 := by
      rw [sub_mul, one_mul, map_sub, h, hsε, sub_zero]
    have := key _ hb hbε hsb
    rw [sub_mul, one_mul, sub_eq_self] at this
    exact this
  · exact Or.inr (key _ ha haε h)

omit [IsDomain R] [IsAlgClosed Ω] [Algebra.Etale R C] [Module.Finite R C] in
lemma mk_eps (ε : C) : Ideal.Quotient.mk (Ideal.span {1 - ε}) ε = 1 := by
  have : Ideal.Quotient.mk (Ideal.span {1 - ε}) (1 - ε) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this.symm

omit [IsDomain R] [IsAlgClosed Ω] [Algebra.Etale R C] [Module.Finite R C] in
/-- **The connected component** `C ⧸ (1 - ε)` of a primitive idempotent is connected. -/
theorem isConnected_quotient {ε : C} (h : IsPrimitive ε) (x : C ⧸ Ideal.span {1 - ε})
    (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y * y - y ∈ Ideal.span {1 - ε} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hx.eq, sub_self]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hy
  have hf : IsIdempotentElem (y * ε) := by
    unfold IsIdempotentElem
    have hε := h.1.eq
    linear_combination (ε * ε) * hz.symm + (y - z * ε) * hε
  have hmk : Ideal.Quotient.mk (Ideal.span {1 - ε}) y =
      Ideal.Quotient.mk (Ideal.span {1 - ε}) (y * ε) := by
    rw [map_mul, mk_eps, mul_one]
  rcases h.2 _ hf with h0 | h0 <;> rw [mul_assoc, h.1.eq] at h0
  · left; rw [hmk, h0, map_zero]
  · right; rw [hmk, h0, mk_eps]

omit [IsDomain R] [IsAlgClosed Ω] [Algebra.Etale R C] [Module.Finite R C] in
/-- A geometric point through `ε` descends to the component `C ⧸ (1 - ε)`. -/
def liftPoint {ε : C} (t : C →ₐ[R] Ω) (ht : t ε = 1) : C ⧸ Ideal.span {1 - ε} →ₐ[R] Ω :=
  Ideal.Quotient.liftₐ _ t fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_sub, map_one, ht, sub_self, mul_zero]

omit [IsDomain R] [IsAlgClosed Ω] [Algebra.Etale R C] [Module.Finite R C] in
@[simp] lemma liftPoint_mk {ε : C} (t : C →ₐ[R] Ω) (ht : t ε = 1) (y : C) :
    liftPoint t ht (Ideal.Quotient.mk _ y) = t y := rfl

omit [IsDomain R] [IsAlgClosed Ω] [Algebra.Etale R C] [Module.Finite R C] in
lemma comp_mk_eps {ε : C} (v : C ⧸ Ideal.span {1 - ε} →ₐ[R] Ω) :
    (v.comp (Ideal.Quotient.mkₐ R _)) ε = 1 := by
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mk_eps, map_one]

section Pow

variable (R) (B₀ : Type u) [CommRing B₀] [Algebra R B₀]

/-- The tensor power `⨂_{i < d} B₀`. -/
abbrev Pow (d : ℕ) : Type u := PiTensorProduct R (fun _ : Fin d => B₀)

variable {R B₀} {d : ℕ}

/-- The `i`-th tensor factor. -/
def ι (i : Fin d) : B₀ →ₐ[R] Pow R B₀ d :=
  PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin d => B₀) i

/-- The universal property of the tensor power (commutative targets). -/
def lift {S : Type u} [CommRing S] [Algebra R S] (g : Fin d → (B₀ →ₐ[R] S)) :
    Pow R B₀ d →ₐ[R] S :=
  PiTensorProduct.liftAlgHom ((MultilinearMap.mkPiAlgebra R (Fin d) S).compLinearMap
      fun i => (g i).toLinearMap)
    (by simp) (fun x y => by simp [Finset.prod_mul_distrib])

omit [IsDomain R] in
lemma lift_ι {S : Type u} [CommRing S] [Algebra R S] (g : Fin d → (B₀ →ₐ[R] S)) (i : Fin d) :
    (lift g).comp (ι i) = g i := by
  classical
  ext a
  simp only [lift, ι, AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply,
    PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply]
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle, hj]) (by simp)]
  simp

omit [IsDomain R] in
lemma lift_ι_apply {S : Type u} [CommRing S] [Algebra R S] (g : Fin d → (B₀ →ₐ[R] S))
    (i : Fin d) (a : B₀) : lift g (ι i a) = g i a :=
  DFunLike.congr_fun (lift_ι g i) a

omit [IsDomain R] in
lemma hom_ext {S : Type u} [CommRing S] [Algebra R S] {f g : Pow R B₀ d →ₐ[R] S}
    (h : ∀ i, f.comp (ι i) = g.comp (ι i)) : f = g :=
  PiTensorProduct.algHom_ext (A := fun _ : Fin d => B₀) h

omit [IsDomain R] in
lemma lift_comp {S : Type u} [CommRing S] [Algebra R S] (u : Pow R B₀ d →ₐ[R] S) :
    lift (fun i => u.comp (ι i)) = u :=
  hom_ext fun i => lift_ι _ i

/-- `⨂_{i < d+1} B₀ → (⨂_{i < d} B₀) ⊗ B₀`. -/
def powSuccTo (d : ℕ) : Pow R B₀ (d + 1) →ₐ[R] TensorProduct R (Pow R B₀ d) B₀ :=
  lift fun i => Fin.lastCases (motive := fun _ => B₀ →ₐ[R] TensorProduct R (Pow R B₀ d) B₀)
    Algebra.TensorProduct.includeRight (fun j => Algebra.TensorProduct.includeLeft.comp (ι j)) i

/-- `(⨂_{i < d} B₀) ⊗ B₀ → ⨂_{i < d+1} B₀`. -/
def powSuccFrom (d : ℕ) : TensorProduct R (Pow R B₀ d) B₀ →ₐ[R] Pow R B₀ (d + 1) :=
  Algebra.TensorProduct.lift (lift fun j => ι j.castSucc) (ι (Fin.last d))
    fun _ _ => Commute.all _ _

/-- `⨂_{i < d+1} B₀ ≅ (⨂_{i < d} B₀) ⊗ B₀`. -/
def powSuccEquiv (d : ℕ) : Pow R B₀ (d + 1) ≃ₐ[R] TensorProduct R (Pow R B₀ d) B₀ := by
  refine AlgEquiv.ofAlgHom (powSuccTo d) (powSuccFrom d) ?_ ?_
  · apply Algebra.TensorProduct.ext
    · refine hom_ext fun j => ?_
      ext a
      simp [powSuccTo, powSuccFrom, lift_ι_apply]
    · ext b
      simp [powSuccTo, powSuccFrom, lift_ι_apply]
  · refine hom_ext fun i => ?_
    induction i using Fin.lastCases with
    | last => ext b; simp [powSuccTo, powSuccFrom, lift_ι_apply]
    | cast j => ext a; simp [powSuccTo, powSuccFrom, lift_ι_apply]

/-- The tensor power with `0` factors is `R`. -/
def powZeroEquiv : Pow R B₀ 0 ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (lift fun i => i.elim0) (Algebra.ofId R _)
    (AlgHom.ext fun r => by simp)
    (hom_ext fun i => i.elim0)

variable [Algebra.Etale R B₀] [Module.Finite R B₀]

instance etale_pow : ∀ d, Algebra.Etale R (Pow R B₀ d)
  | 0 => Algebra.Etale.of_equiv powZeroEquiv.symm
  | d + 1 => by
    haveI := etale_pow d
    haveI : Algebra.Etale R (TensorProduct R (Pow R B₀ d) B₀) :=
      Algebra.Etale.comp R (Pow R B₀ d) _
    exact Algebra.Etale.of_equiv (powSuccEquiv d).symm

end Pow

section Closure

variable {B₀ : Type u} [CommRing B₀] [Algebra R B₀] [Algebra.Etale R B₀] [Module.Finite R B₀]

omit [IsDomain R] [IsAlgClosed Ω] [Module.Finite R B₀] in
/-- **The diagonal idempotent** of `B₀ ⊗_R B₀` (`B₀` unramified): it is `1` exactly at the
geometric points `(x, y)` with `x = y`. -/
lemma exists_diag : ∃ τ : TensorProduct R B₀ B₀, IsIdempotentElem τ ∧
    ∀ x y : B₀ →ₐ[R] Ω,
      Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _) τ = 1 ↔ x = y := by
  obtain ⟨τ, hτ, hτ₁⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R)
    (S := B₀)).1 inferInstance
  have hidem : IsIdempotentElem τ := by
    change τ * τ = τ
    rw [mul_eq_lmul'_tmul_one_mul hτ, hτ₁, ← Algebra.TensorProduct.one_def, one_mul]
  refine ⟨τ, hidem, fun x y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · ext b
    have := congrArg (Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)) (hτ b)
    rw [map_mul, h, mul_one, map_zero, map_sub] at this
    simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one, sub_eq_zero] at this
    exact this.symm
  · subst h
    have : Algebra.TensorProduct.lift x x (fun _ _ => Commute.all _ _) =
        x.comp (Algebra.TensorProduct.lmul' R) := by
      ext a <;> simp
    rw [this, AlgHom.comp_apply, hτ₁, map_one]

omit [IsDomain R] [IsAlgClosed Ω] [Algebra.Etale R B₀] [Module.Finite R B₀] in
lemma comp_tensorLift {S T : Type u} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
    (u : S →ₐ[R] T) (a b : B₀ →ₐ[R] S) :
    u.comp (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)) =
      Algebra.TensorProduct.lift (u.comp a) (u.comp b) (fun _ _ => Commute.all _ _) := by
  ext <;> simp

/-- **Galois closure**: a finite étale `R`-algebra `B₀` with a geometric point `s₀` maps to a
connected finite étale `R`-algebra `B` with a geometric point `t₀` over `s₀` such that
`Aut_R(B)` acts transitively on the geometric points of `B`. -/
theorem exists_galoisClosure (s₀ : B₀ →ₐ[R] Ω) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra.Etale R B)
      (_ : Module.Finite R B) (t₀ : B →ₐ[R] Ω) (g : B₀ →ₐ[R] B),
      t₀.comp g = s₀ ∧ (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
      ∀ t t' : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t.comp (σ : B →ₐ[R] B) = t' := by
  classical
  let d := Nat.card (B₀ →ₐ[R] Ω)
  let en : (B₀ →ₐ[R] Ω) ≃ Fin d := Finite.equivFin _
  let T := Pow R B₀ d
  let sT : T →ₐ[R] Ω := lift fun i => en.symm i
  obtain ⟨ε, hε, hsε⟩ := exists_isPrimitive sT
  obtain ⟨τ, hτ, hτx⟩ := exists_diag (R := R) (Ω := Ω) (B₀ := B₀)
  -- points through `ε` are injective tuples
  have hinj : ∀ u : T →ₐ[R] Ω, u ε = 1 → Function.Injective fun i => u.comp (ι i) := by
    intro u hu i j hij
    by_contra hne
    let τij : T := Algebra.TensorProduct.lift (ι i) (ι j) (fun _ _ => Commute.all _ _) τ
    have hval : ∀ v : T →ₐ[R] Ω, v τij = 1 ↔ v.comp (ι i) = v.comp (ι j) := fun v => by
      rw [← hτx]
      change (v.comp (Algebra.TensorProduct.lift (ι i) (ι j)
        (fun _ _ => Commute.all _ _))) τ = 1 ↔ _
      rw [comp_tensorLift]
    have hsT : sT τij = 0 := by
      refine (idem_eq_zero_or_one (hτ.map _) sT).resolve_right fun h => hne ?_
      have := (hval sT).1 h
      rw [lift_ι, lift_ι] at this
      exact en.symm.injective this
    have hf : (1 - τij) * ε = ε := by
      refine (hε.2 _ (hτ.map _).one_sub).resolve_left fun h0 => ?_
      have := congrArg sT h0
      rw [map_mul, map_sub, map_one, hsT, hsε, map_zero] at this
      norm_num at this
    have h1 : u τij = 0 := by
      have := congrArg u hf
      rw [map_mul, hu, mul_one, map_sub, map_one] at this
      linear_combination -this
    have h2 : u τij = 1 := (hval u).2 hij
    rw [h1] at h2
    exact zero_ne_one h2
  have hbij : ∀ u : T →ₐ[R] Ω, u ε = 1 → Function.Bijective fun i => u.comp (ι i) :=
    fun u hu => (hinj u hu).bijective_of_nat_card_le (by simp [d])
  let B := T ⧸ Ideal.span {1 - ε}
  haveI : Algebra.Etale R B := quotient_etale hε.1
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, liftPoint sT hsε,
    (Ideal.Quotient.mkₐ R _).comp (ι (en s₀)), ?_, isConnected_quotient hε, fun v v' => ?_⟩
  · ext a
    change sT (ι (en s₀) a) = s₀ a
    rw [lift_ι_apply, Equiv.symm_apply_apply]
  · let u := v.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - ε}))
    let u' := v'.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - ε}))
    have hu : u ε = 1 := comp_mk_eps v
    have hu' : u' ε = 1 := comp_mk_eps v'
    let x := Equiv.ofBijective _ (hbij u hu)
    let x' := Equiv.ofBijective _ (hbij u' hu')
    let π : Fin d ≃ Fin d := x'.trans x.symm
    have hπ : ∀ i, u.comp (ι (π i)) = u'.comp (ι i) := fun i => by
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
    have huPe : u.comp (Pe : T →ₐ[R] T) = u' := hom_ext fun i => by
      ext a
      change u ((lift (R := R) (B₀ := B₀) (S := T) fun i => ι (π i)) (ι i a)) = _
      rw [lift_ι_apply]
      exact DFunLike.congr_fun (hπ i) a
    have hPeε : Pe ε = ε := by
      refine (hε.map Pe).eq hε u ?_ hu
      change (u.comp (Pe : T →ₐ[R] T)) ε = 1
      rw [huPe, hu']
    have hI : Ideal.span {1 - ε} = (Ideal.span {1 - ε}).map (Pe : T →+* T) := by
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      change 1 - ε = Pe (1 - ε)
      rw [map_sub, map_one, hPeε]
    refine ⟨Ideal.quotientEquivAlg _ _ Pe hI, Ideal.Quotient.algHom_ext R (AlgHom.ext fun y => ?_)⟩
    change v (Ideal.quotientEquivAlg _ _ Pe hI (Ideal.Quotient.mk _ y)) = u' y
    rw [Ideal.quotientEquivAlg_mk, ← huPe]
    rfl

end Closure

end Components

end

end TemperedFundamentalGroups
