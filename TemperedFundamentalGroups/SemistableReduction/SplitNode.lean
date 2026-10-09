/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LocalModel

/-!
# Split nodes (ring level)

Blueprint §9.7a, §10.3.8 (split nodes for `ModelCode.HasSplitNodes`). The `O`-algebra `A` has a
**split node at `𝔭`** (`IsSplitNodeAt ϖ 𝔭`) if it is étale-locally the node
`Node O (ϖ ^ n) = O[u, v] ⧸ (u v - ϖ ^ n)` at its singular point (`u, v ∈ 𝔮`), and the point `𝔮`
of the common étale neighbourhood `C` has the residue field of `O` (`O → C ⧸ 𝔮` surjective).
`IsSplitSemistableAt ϖ 𝔭`: `A` is étale-locally the affine line `O[X]` at `𝔭`, or has a split
node there. This implies `IsSemistableAt`.

* `IsSplitNodeAt.of_etale_of_comap`, `IsSplitNodeAt.of_etale`: descent along étale maps, ascent
  along étale maps to points with the residue field of `O`;
* `residue_of_isLocalization_away`: localizations at points of the special fibre with the residue
  field of `O` keep it;
* `Node.isEtaleLocallyAt_of_u_notMem`, `Node.isEtaleLocallyAt_of_v_notMem`: off the singular point
  the node is étale-locally `O[X]` (`Node[1/u] = O[u, 1/u]`);
* generization: `SplitNodeGen.lean`.
-/

universe u

open Polynomial TensorProduct IsLocalRing

namespace SemistableReduction

variable {O : Type u} [CommRing O]

/-- `A` has a **split node at `𝔭`**: a common étale neighbourhood `C` of `𝔭 ∈ Spec A` and of the
singular point of the node `O[u, v] ⧸ (u v - ϖ ^ n)` (`u, v ∈ 𝔮`) whose point `𝔮` has the residue
field of `O`. -/
def IsSplitNodeAt (ϖ : O) {A : Type u} [CommRing A] [Algebra O A] (𝔭 : Ideal A) : Prop :=
  ∃ (n : ℕ) (C : Type u) (_ : CommRing C) (g : A →+* C) (f : Node O (ϖ ^ n) →+* C)
    (𝔮 : Ideal C), g.Etale ∧ f.Etale ∧ 𝔮.IsPrime ∧ 𝔮.comap g = 𝔭 ∧
      f.comp (algebraMap O (Node O (ϖ ^ n))) = g.comp (algebraMap O A) ∧
      f (Node.u (ϖ ^ n)) ∈ 𝔮 ∧ f (Node.v (ϖ ^ n)) ∈ 𝔮 ∧
      Function.Surjective ((Ideal.Quotient.mk 𝔮).comp (g.comp (algebraMap O A)))

/-- `A` is **split semistable at `𝔭`**: étale-locally `O[X]`, or a split node. -/
def IsSplitSemistableAt (ϖ : O) {A : Type u} [CommRing A] [Algebra O A] (𝔭 : Ideal A) : Prop :=
  IsEtaleLocallyAt O O[X] 𝔭 ∨ IsSplitNodeAt ϖ 𝔭

variable {ϖ : O} {A A' : Type u} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

namespace IsSplitNodeAt

theorem isEtaleLocallyAt {𝔭 : Ideal A} (h : IsSplitNodeAt ϖ 𝔭) :
    ∃ n : ℕ, IsEtaleLocallyAt O (Node O (ϖ ^ n)) 𝔭 := by
  obtain ⟨n, C, _, g, f, 𝔮, hg, hf, h𝔮, hc, hO, -⟩ := h
  exact ⟨n, C, inferInstance, g, f, 𝔮, hg, hf, h𝔮, hc, hO⟩

theorem isSemistableAt {𝔭 : Ideal A} (h : IsSplitNodeAt ϖ 𝔭) : IsSemistableAt ϖ 𝔭 :=
  .inl h.isEtaleLocallyAt

/-- The residue field at a split node is that of `O`. -/
theorem residue {𝔭 : Ideal A} (h : IsSplitNodeAt ϖ 𝔭) (a : A) :
    ∃ o : O, a - algebraMap O A o ∈ 𝔭 := by
  obtain ⟨n, C, _, g, f, 𝔮, -, -, -, hc, -, -, -, hs⟩ := h
  obtain ⟨o, ho⟩ := hs (Ideal.Quotient.mk 𝔮 (g a))
  refine ⟨o, ?_⟩
  rw [← hc, Ideal.mem_comap, map_sub, ← Ideal.Quotient.eq]
  exact ho.symm

/-- In a common étale neighbourhood, a prime containing `v` contains `ϖ`. -/
lemma mem_of_u_v_mem {n : ℕ} {C : Type u} [CommRing C] {g : A →+* C}
    {f : Node O (ϖ ^ n) →+* C} (hO : f.comp (algebraMap O (Node O (ϖ ^ n))) =
      g.comp (algebraMap O A)) {𝔮 : Ideal C} [𝔮.IsPrime]
    (hv : f (Node.v (ϖ ^ n)) ∈ 𝔮) : g (algebraMap O A ϖ) ∈ 𝔮 := by
  have h1 := 𝔮.mul_mem_left (f (Node.u (ϖ ^ n))) hv
  rw [← map_mul, Node.u_mul_v] at h1
  have h2 : (f.comp (algebraMap O (Node O (ϖ ^ n)))) (ϖ ^ n) ∈ 𝔮 := h1
  rw [hO, RingHom.comp_apply, map_pow, map_pow] at h2
  exact ‹𝔮.IsPrime›.mem_of_pow_mem n h2

/-- A split node lies on the special fibre. -/
theorem algebraMap_mem {𝔭 : Ideal A} (h : IsSplitNodeAt ϖ 𝔭) : algebraMap O A ϖ ∈ 𝔭 := by
  obtain ⟨n, C, _, g, f, 𝔮, -, -, h𝔮, hc, hO, -, hv, -⟩ := h
  rw [← hc, Ideal.mem_comap]
  exact mem_of_u_v_mem hO hv

/-- **Descent from an étale neighbourhood.** -/
theorem of_etale_of_comap (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) {𝔭' : Ideal A'}
    (h : IsSplitNodeAt ϖ 𝔭') : IsSplitNodeAt ϖ (𝔭'.comap φ.toRingHom) := by
  obtain ⟨n, C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp, hu, hv, hs⟩ := h
  have hφO : g.comp (algebraMap O A') = (g.comp φ.toRingHom).comp (algebraMap O A) := by
    rw [RingHom.comp_assoc]
    exact congrArg g.comp (AlgHom.comp_algebraMap φ).symm
  refine ⟨n, C, inferInstance, g.comp φ.toRingHom, f, 𝔮,
    RingHom.Etale.stableUnderComposition _ _ hφ hg, hf, h𝔮,
    by rw [← Ideal.comap_comap, hcomap], by rw [hcomp, hφO], hu, hv, ?_⟩
  rwa [← hφO]

/-- **Ascent along étale maps** to a point `𝔭'` with the residue field of `O`. -/
theorem of_etale (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) (𝔭' : Ideal A') [𝔭'.IsPrime]
    (hres : ∀ a' : A', ∃ o : O, a' - algebraMap O A' o ∈ 𝔭')
    (h : IsSplitNodeAt ϖ (𝔭'.comap φ.toRingHom)) : IsSplitNodeAt ϖ 𝔭' := by
  obtain ⟨n, C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp, hu, hv, hs⟩ := h
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  letI : Algebra A C := g.toAlgebra
  obtain ⟨R, hR, hR₁, hR₂⟩ := exists_isPrime_tensorProduct (A := A) 𝔭' 𝔮 hcomap.symm
  have hl : (Algebra.TensorProduct.includeLeftRingHom : A' →+* A' ⊗[A] C).Etale :=
    RingHom.Etale.isStableUnderBaseChange.tensorProduct A' hg
  have hr : (Algebra.TensorProduct.includeRight : C →ₐ[A] A' ⊗[A] C).toRingHom.Etale := by
    have h₁ : (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[A] A').Etale :=
      RingHom.Etale.isStableUnderBaseChange.tensorProduct C hφ
    have e : (Algebra.TensorProduct.includeRight : C →ₐ[A] A' ⊗[A] C).toRingHom =
        (Algebra.TensorProduct.comm A C A').toRingHom.comp
          Algebra.TensorProduct.includeLeftRingHom := by
      ext c
      simp
    rw [e]
    exact RingHom.Etale.stableUnderComposition _ _ h₁
      (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm A C A').bijective)
  set iL : A' →+* A' ⊗[A] C := Algebra.TensorProduct.includeLeftRingHom
  set iR : C →ₐ[A] A' ⊗[A] C := Algebra.TensorProduct.includeRight
  have hY : ∀ o : O, iR (g (algebraMap O A o)) = iL (algebraMap O A' o) := by
    intro o
    change iR (algebraMap A C (algebraMap O A o)) = _
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    change _ = (algebraMap O A' o) ⊗ₜ[A] (1 : C)
    congr 1
    exact φ.commutes o
  have hcompat : (iR.toRingHom.comp f).comp (algebraMap O (Node O (ϖ ^ n))) =
      iL.comp (algebraMap O A') := by
    rw [RingHom.comp_assoc, hcomp]
    ext o
    exact hY o
  have hL : ∀ a' : A', a' ∈ 𝔭' → iL a' ∈ R := fun a' ha ↦ by
    rw [← hR₁] at ha; exact ha
  have hRr : ∀ c : C, c ∈ 𝔮 → iR c ∈ R := fun c hc ↦ by
    rw [← hR₂] at hc; exact hc
  have key : ∀ z : A' ⊗[A] C, ∃ o : O, z - iL (algebraMap O A' o) ∈ R := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a' c =>
      obtain ⟨o₁, ho₁⟩ := hres a'
      obtain ⟨o₂, ho₂⟩ := hs (Ideal.Quotient.mk 𝔮 c)
      have h₂ : c - g (algebraMap O A o₂) ∈ 𝔮 := by
        rw [← Ideal.Quotient.eq]; exact ho₂.symm
      refine ⟨o₁ * o₂, ?_⟩
      have h₁' := hL _ ho₁
      have h₂' := hRr _ h₂
      rw [map_sub] at h₁'
      rw [map_sub, hY] at h₂'
      have he : a' ⊗ₜ[A] c = iL a' * iR c := by
        simp [iL, iR]
      have : a' ⊗ₜ[A] c - iL (algebraMap O A' (o₁ * o₂)) =
          (iL a' - iL (algebraMap O A' o₁)) * iR c +
            iL (algebraMap O A' o₁) * (iR c - iL (algebraMap O A' o₂)) := by
        rw [he, map_mul, map_mul]; ring
      rw [this]
      exact R.add_mem (R.mul_mem_right _ h₁') (R.mul_mem_left _ h₂')
    | add x y hx hy =>
      obtain ⟨o₁, h₁⟩ := hx
      obtain ⟨o₂, h₂⟩ := hy
      refine ⟨o₁ + o₂, ?_⟩
      have : x + y - iL (algebraMap O A' (o₁ + o₂)) =
          (x - iL (algebraMap O A' o₁)) + (y - iL (algebraMap O A' o₂)) := by
        rw [map_add, map_add]; ring
      rw [this]
      exact R.add_mem h₁ h₂
  refine ⟨n, A' ⊗[A] C, inferInstance, iL, iR.toRingHom.comp f, R, hl,
    RingHom.Etale.stableUnderComposition f _ hf hr, hR, hR₁, hcompat, hRr _ hu, hRr _ hv, ?_⟩
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨o, ho⟩ := key z
  exact ⟨o, (Ideal.Quotient.eq.2 ho).symm⟩

end IsSplitNodeAt

/-- **Residue fields of localizations**: if `A` has the residue field of `O` at `𝔭' ∩ A`, which
lies on the special fibre, so does a localization `A' = A[1/s]` at `𝔭'`. -/
theorem residue_of_isLocalization_away [IsLocalRing O] (hϖ : maximalIdeal O ≤ Ideal.span {ϖ})
    [Algebra A A'] [IsScalarTower O A A'] (s : A) [IsLocalization.Away s A'] (𝔭' : Ideal A')
    [𝔭'.IsPrime] (hϖ𝔭 : algebraMap O A ϖ ∈ 𝔭'.comap (algebraMap A A'))
    (hres : ∀ a : A, ∃ o : O, a - algebraMap O A o ∈ 𝔭'.comap (algebraMap A A')) (a' : A') :
    ∃ o : O, a' - algebraMap O A' o ∈ 𝔭' := by
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers s) a'
  simp only at h
  obtain ⟨o₁, ho₁⟩ := hres a
  obtain ⟨o₂, ho₂⟩ := hres s
  have hsu : IsUnit (algebraMap A A' s) := IsLocalization.Away.algebraMap_isUnit s
  have hs𝔭 : algebraMap A A' s ∉ 𝔭' := fun h ↦
    ‹𝔭'.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem _ h hsu)
  have hunit : IsUnit o₂ := by
    by_contra hn
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hϖ ((mem_maximalIdeal _).2 hn))
    apply hs𝔭
    have h1 : algebraMap O A o₂ ∈ 𝔭'.comap (algebraMap A A') := by
      rw [← hr, map_mul]; exact Ideal.mul_mem_left _ _ hϖ𝔭
    have h2 := Ideal.add_mem _ ho₂ h1
    rw [sub_add_cancel] at h2
    exact h2
  set π := Ideal.Quotient.mk 𝔭'
  have hT : ∀ o : O, algebraMap O A' o = algebraMap A A' (algebraMap O A o) :=
    fun o ↦ IsScalarTower.algebraMap_apply O A A' o
  have e₁ : π (algebraMap A A' a) = π (algebraMap O A' o₁) := by
    rw [Ideal.Quotient.eq, hT, ← map_sub]; exact ho₁
  have e₂ : π (algebraMap A A' s) = π (algebraMap O A' o₂) := by
    rw [Ideal.Quotient.eq, hT, ← map_sub]; exact ho₂
  have e₃ : π (algebraMap O A' (↑hunit.unit⁻¹ : O)) * π (algebraMap O A' o₂) = 1 := by
    have : (↑hunit.unit⁻¹ : O) * o₂ = 1 := hunit.val_inv_mul
    rw [← map_mul, ← map_mul, this, map_one, map_one]
  refine ⟨o₁ * (↑hunit.unit⁻¹ : O) ^ k, ?_⟩
  have hsk : algebraMap A A' (s ^ k) ∉ 𝔭' := by
    rw [map_pow]; exact fun h ↦ hs𝔭 (‹𝔭'.IsPrime›.mem_of_pow_mem k h)
  refine (‹𝔭'.IsPrime›.mem_or_mem (Ideal.Quotient.eq_zero_iff_mem.1 ?_)).resolve_right hsk
  have h' := congrArg π h
  simp only [map_mul, map_pow, map_sub] at h' ⊢
  rw [e₂] at h' ⊢
  rw [e₁] at h'
  rw [sub_mul, mul_assoc, ← mul_pow, e₃, one_pow, mul_one]
  exact sub_eq_zero.2 h'

/-! ### The node off its singular point -/

namespace Node

variable {a : O}

/-- Every element of the node is congruent to a constant modulo `(u, v)`. -/
lemma exists_sub_mem_span (x : Node O a) :
    ∃ o : O, x - algebraMap O (Node O a) o ∈ Ideal.span {u a, v a} := by
  have hx : x ∈ Submodule.span O (Set.range (monomial a)) := by rw [span_eq_top]; trivial
  have hu : u a ∈ Ideal.span {u a, v a} := Ideal.subset_span (by simp)
  have hv : v a ∈ Ideal.span {u a, v a} := Ideal.subset_span (by simp)
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    rcases s with i | j
    · rcases i with _ | i
      · exact ⟨1, by simp [monomial]⟩
      · refine ⟨0, ?_⟩
        simp only [monomial, Sum.elim_inl, map_zero, sub_zero]
        exact Ideal.pow_mem_of_mem _ hu _ (Nat.succ_pos i)
    · refine ⟨0, ?_⟩
      simp only [monomial, Sum.elim_inr, map_zero, sub_zero]
      exact Ideal.pow_mem_of_mem _ hv _ (Nat.succ_pos j)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨o₁, h₁⟩ := hx
    obtain ⟨o₂, h₂⟩ := hy
    refine ⟨o₁ + o₂, ?_⟩
    have : x + y - algebraMap O (Node O a) (o₁ + o₂) =
        (x - algebraMap O (Node O a) o₁) + (y - algebraMap O (Node O a) o₂) := by
      rw [map_add]; ring
    rw [this]
    exact add_mem h₁ h₂
  | smul r x _ hx =>
    obtain ⟨o, h⟩ := hx
    refine ⟨r * o, ?_⟩
    have : r • x - algebraMap O (Node O a) (r * o) =
        algebraMap O (Node O a) r * (x - algebraMap O (Node O a) o) := by
      rw [mul_sub, ← map_mul]
      exact congrArg (· - _) (Algebra.smul_def r x)
    rw [this]
    exact Ideal.mul_mem_left _ _ h

variable (a) in
/-- The node in the Laurent polynomials, `u ↦ T`, `v ↦ a T⁻¹`. -/
noncomputable def toLaurent : Node O a →ₐ[O] LaurentPolynomial O :=
  lift (LaurentPolynomial.T 1) (LaurentPolynomial.C a * LaurentPolynomial.T (-1)) (by
    rw [mul_left_comm, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one, LaurentPolynomial.C_eq_algebraMap])

lemma toLaurent_aeval_u (p : O[X]) : toLaurent a (aeval (u a) p) = p.toLaurent := by
  rw [← AlgHom.comp_apply]
  have : (toLaurent a).comp (aeval (u a)) = Polynomial.toLaurentAlg := by
    refine Polynomial.algHom_ext ?_
    simp [toLaurent, Polynomial.toLaurentAlg_apply]
  rw [this, Polynomial.toLaurentAlg_apply]

/-- `x u ^ m` is a polynomial in `u` for some `m`. -/
lemma exists_mul_pow_mem_range (x : Node O a) :
    ∃ (m : ℕ) (p : O[X]), x * u a ^ m = aeval (u a) p := by
  have hx : x ∈ Submodule.span O (Set.range (monomial a)) := by rw [span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    rcases s with i | j
    · exact ⟨0, X ^ i, by simp [monomial]⟩
    · refine ⟨j + 1, C a ^ (j + 1), ?_⟩
      simp only [monomial, Sum.elim_inr, map_pow, aeval_C]
      rw [← mul_pow, mul_comm (v a) (u a), u_mul_v]
  | zero => exact ⟨0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, p₁, h₁⟩ := hx
    obtain ⟨m₂, p₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, p₁ * X ^ m₂ + p₂ * X ^ m₁, ?_⟩
    simp only [map_add, map_mul, map_pow, aeval_X, ← h₁, ← h₂, pow_add]
    ring
  | smul r x _ hx =>
    obtain ⟨m, p, h⟩ := hx
    refine ⟨m, C r * p, ?_⟩
    rw [map_mul, aeval_C, ← h]
    exact (congrArg (· * u a ^ m) (Algebra.smul_def r x)).trans (mul_assoc _ _ _)

/-- `Node[1/u]` is `O[X][1/X]`, `X ↦ u`. -/
lemma isLocalization_away_u :
    letI : Algebra O[X] (Localization.Away (u a)) :=
      ((algebraMap (Node O a) (Localization.Away (u a))).comp
        (aeval (u a)).toRingHom).toAlgebra
    IsLocalization.Away (X : O[X]) (Localization.Away (u a)) := by
  letI : Algebra O[X] (Localization.Away (u a)) :=
    ((algebraMap (Node O a) (Localization.Away (u a))).comp (aeval (u a)).toRingHom).toAlgebra
  have hX : algebraMap O[X] (Localization.Away (u a)) X =
      algebraMap (Node O a) (Localization.Away (u a)) (u a) := by
    change algebraMap (Node O a) _ (aeval (u a) X) = _
    rw [aeval_X]
  have hu : IsUnit (algebraMap (Node O a) (Localization.Away (u a)) (u a)) :=
    IsLocalization.Away.algebraMap_isUnit (u a)
  have hinj : Function.Injective (algebraMap O[X] (Localization.Away (u a))) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    change algebraMap (Node O a) _ (aeval (u a) p) = 0 at hp
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (u a)) _ _).1 hp
    have := congrArg (toLaurent a) hk
    simp only [map_mul, map_pow, map_zero, toLaurent_aeval_u] at this
    have hT : toLaurent a (u a) = LaurentPolynomial.T 1 := by simp [toLaurent]
    rw [hT] at this
    have h0 : p.toLaurent = 0 :=
      ((LaurentPolynomial.isUnit_T 1).pow k).mul_right_eq_zero.1 this
    exact Polynomial.toLaurent_injective (by rw [h0, map_zero])
  change IsLocalization (Submonoid.powers X) _
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    simp only [map_pow, hX]
    exact hu.pow k
  · intro z
    obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (u a)) z
    obtain ⟨m, p, hp⟩ := exists_mul_pow_mem_range x
    refine ⟨⟨p, ⟨X ^ (k + m), k + m, rfl⟩⟩, ?_⟩
    simp only at hz ⊢
    rw [map_pow, hX]
    change z * _ = algebraMap (Node O a) _ (aeval (u a) p)
    rw [← hp, map_mul, ← hz, map_pow, map_pow, pow_add]
    ring
  · intro p q h
    exact ⟨1, by rw [hinj h]⟩

/-- **Off the singular point the node is étale-locally the affine line** (`u ∉ 𝔫`). -/
theorem isEtaleLocallyAt_of_u_notMem (𝔫 : Ideal (Node O a)) [𝔫.IsPrime] (hu : u a ∉ 𝔫) :
    IsEtaleLocallyAt O O[X] 𝔫 := by
  letI : Algebra O[X] (Localization.Away (u a)) :=
    ((algebraMap (Node O a) (Localization.Away (u a))).comp (aeval (u a)).toRingHom).toAlgebra
  haveI := isLocalization_away_u (a := a)
  have hdisj : Disjoint (Submonoid.powers (u a) : Set (Node O a)) 𝔫 := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hu (‹𝔫.IsPrime›.mem_of_pow_mem k hk)
  refine ⟨Localization.Away (u a), inferInstance, algebraMap _ _,
    algebraMap O[X] (Localization.Away (u a)), 𝔫.map (algebraMap _ _),
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (u a)),
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway X),
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (u a)) _ 𝔫 inferInstance hdisj,
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (u a)) _ inferInstance hdisj,
    ?_⟩
  ext o
  change algebraMap (Node O a) _ (aeval (u a) (C o)) = algebraMap (Node O a) _ (algebraMap O _ o)
  rw [aeval_C]

/-- The swap `u ↔ v` of the node. -/
noncomputable def swap : Node O a ≃ₐ[O] Node O a :=
  AlgEquiv.ofAlgHom (lift (v a) (u a) (by rw [mul_comm, u_mul_v]))
    (lift (v a) (u a) (by rw [mul_comm, u_mul_v]))
    (algHom_ext (by simp) (by simp)) (algHom_ext (by simp) (by simp))

lemma swap_u : swap (a := a) (u a) = v a := by
  simp [swap]

/-- The same with `v ∉ 𝔫`. -/
theorem isEtaleLocallyAt_of_v_notMem (𝔫 : Ideal (Node O a)) [𝔫.IsPrime] (hv : v a ∉ 𝔫) :
    IsEtaleLocallyAt O O[X] 𝔫 := by
  have h : IsEtaleLocallyAt O O[X] (𝔫.comap (swap (a := a)).toAlgHom.toRingHom) :=
    isEtaleLocallyAt_of_u_notMem _ (by
      rw [Ideal.mem_comap]
      change swap (a := a) (u a) ∉ 𝔫
      rw [swap_u]; exact hv)
  have h' := h.of_etale_of_comap (swap (a := a)).symm.toAlgHom
    (RingHom.Etale.of_bijective (swap (a := a)).symm.bijective)
  convert h' using 1
  ext x
  simp [Ideal.mem_comap]

end Node

namespace IsSplitSemistableAt

theorem isSemistableAt {𝔭 : Ideal A} (h : IsSplitSemistableAt ϖ 𝔭) : IsSemistableAt ϖ 𝔭 :=
  h.elim .inr IsSplitNodeAt.isSemistableAt

theorem of_etale_of_comap (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) {𝔭' : Ideal A'}
    (h : IsSplitSemistableAt ϖ 𝔭') : IsSplitSemistableAt ϖ (𝔭'.comap φ.toRingHom) :=
  h.imp (fun h ↦ h.of_etale_of_comap φ hφ) (fun h ↦ h.of_etale_of_comap φ hφ)

end IsSplitSemistableAt

end SemistableReduction
