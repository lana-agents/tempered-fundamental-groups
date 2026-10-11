/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Finite extensions of complete discrete valuation rings (Blueprint §11, F8)

Let `A` be a complete discrete valuation ring with fraction field `K` and `L / K` a finite
separable extension. Then the integral closure `B` of `A` in `L` is a **local** ring
(`isLocalRing_integralClosure`), hence a discrete valuation ring, and it is the unique valuation
subring of `L` lying over `A`: every valuation subring `O'` of `L` such that `A → O'` is a local
homomorphism equals `B` (`mem_integralClosure_of_mem`), so in particular `O'` is finite over
`A` (`finite_of_isLocalHom`).

Proof of locality: `B` is finite free over `A`, hence `𝔪_A`-adically complete
(`isPrecomplete_of_basis`). If `M₁ ≠ M₂` are maximal ideals of `B`, the Chinese remainder
theorem gives `x ∈ M₁` with `1 - x` in every other maximal ideal, so `x - x²` lies in the
radical of `𝔪_A B`; the idempotent lifting formula `1 - (1 - xⁿ)ⁿ` and the Newton iteration
`x ↦ 2x² - x⁴` converge to an idempotent `e ∈ M₁` with `1 - e ∈ M₂`, impossible in a domain.
-/

open IsLocalRing Polynomial

namespace TemperedFundamentalGroups

section Precomplete

/-- A finite free module over an `I`-adically precomplete ring is `I`-adically precomplete. -/
theorem isPrecomplete_of_basis {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite ι] (I : Ideal R) [hR : IsPrecomplete I R] (b : Module.Basis ι R M) :
    IsPrecomplete I M := by
  have := Fintype.ofFinite ι
  have hmap : ∀ (n : ℕ) (x : M) (i : ι), x ∈ I ^ n • (⊤ : Submodule R M) →
      b.repr x i ∈ I ^ n • (⊤ : Submodule R R) := fun n x i hx =>
    Submodule.smul_top_le_comap_smul_top (I ^ n) (b.coord i) hx
  refine ⟨fun {f} hf => ?_⟩
  choose L hL using fun i => hR.prec (f := fun n => b.repr (f n) i) fun {m n} hmn => by
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    simpa using hmap m _ i h
  refine ⟨∑ i, L i • b i, fun n => ?_⟩
  rw [SModEq.sub_mem]
  nth_rw 1 [← b.sum_repr (f n)]
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← sub_smul]
  have h := SModEq.sub_mem.1 (hL i n)
  rw [smul_eq_mul, Ideal.mul_top] at h
  exact Submodule.smul_mem_smul h Submodule.mem_top

end Precomplete

section Newton

variable {B : Type*} [CommRing B]

/-- Newton iteration `x ↦ 2x² - x⁴` for idempotents. -/
def idemNewton (e : B) : ℕ → B
  | 0 => e
  | k + 1 => 2 * idemNewton e k ^ 2 - idemNewton e k ^ 4

lemma idemNewton_succ (e : B) (k : ℕ) :
    idemNewton e (k + 1) = 2 * idemNewton e k ^ 2 - idemNewton e k ^ 4 := rfl

lemma idemNewton_succ_sub (e : B) (k : ℕ) : idemNewton e (k + 1) - idemNewton e k =
    (idemNewton e k - idemNewton e k ^ 2) * (idemNewton e k ^ 2 + idemNewton e k - 1) := by
  rw [idemNewton_succ]; ring

lemma idemNewton_succ_sub_sq (e : B) (k : ℕ) :
    idemNewton e (k + 1) - idemNewton e (k + 1) ^ 2 = (idemNewton e k - idemNewton e k ^ 2) ^ 2 *
      ((1 + idemNewton e k) ^ 2 * (2 - idemNewton e k ^ 2)) := by
  rw [idemNewton_succ]; ring

/-- If `e - e² ∈ J`, then `xₖ - xₖ² ∈ J^(k+1)` for the Newton iterates `xₖ`. -/
lemma idemNewton_sub_sq_mem {J : Ideal B} {e : B} (he : e - e ^ 2 ∈ J) (k : ℕ) :
    idemNewton e k - idemNewton e k ^ 2 ∈ J ^ (k + 1) := by
  induction k with
  | zero => simpa [idemNewton] using he
  | succ k ih =>
    rw [idemNewton_succ_sub_sq]
    refine J.pow_le_pow_right (show k + 1 + 1 ≤ (k + 1) * 2 by omega) ?_
    rw [pow_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ih 2)

lemma idemNewton_sub_mem {J : Ideal B} {e : B} (he : e - e ^ 2 ∈ J) {m n : ℕ} (hmn : m ≤ n) :
    idemNewton e n - idemNewton e m ∈ J ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [show idemNewton e (n + 1) - idemNewton e m =
      (idemNewton e (n + 1) - idemNewton e n) + (idemNewton e n - idemNewton e m) by ring,
      idemNewton_succ_sub]
    exact add_mem (J.pow_le_pow_right (by omega)
      (Ideal.mul_mem_right _ _ (idemNewton_sub_sq_mem he n))) ih

/-- The Newton iterates stay in the fibres `x = 0` and `x = 1` of a quotient map. -/
lemma idemNewton_map {S : Type*} [CommRing S] (f : B →+* S) (e : B) (c : S) (hc : c = 0 ∨ c = 1)
    (he : f e = c) (k : ℕ) : f (idemNewton e k) = c := by
  induction k with
  | zero => exact he
  | succ k ih =>
    rw [idemNewton_succ, map_sub, map_mul, map_pow, map_pow, ih, map_ofNat]
    rcases hc with rfl | rfl <;> norm_num

end Newton

section Local

variable {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]
  {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

omit [IsDomain A] [IsPrincipalIdealRing A] [IsAdicComplete (maximalIdeal A) A] [IsDomain B]
  [Module.IsTorsionFree A B] in
lemma map_maximalIdeal_le_of_isMaximal (M : Ideal B) [M.IsMaximal] :
    (maximalIdeal A).map (algebraMap A B) ≤ M := by
  rw [Ideal.map_le_iff_le_comap]
  exact le_of_eq
    (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)).symm

variable (A) in
include A in
/-- **A finite torsion-free domain over a complete discrete valuation ring (more generally a
complete local PID) with finitely many maximal ideals is local.** -/
theorem isLocalRing_of_finite_maximal (hfin : {I : Ideal B | I.IsMaximal}.Finite) :
    IsLocalRing B := by
  classical
  haveI : Module.Free A B := Module.free_of_finite_type_torsion_free'
  haveI : IsPrecomplete (maximalIdeal A) B :=
    isPrecomplete_of_basis _ (Module.Free.chooseBasis A B)
  set J := (maximalIdeal A).map (algebraMap A B) with hJdef
  have hsm : ∀ (m : ℕ) (y : B), y ∈ (maximalIdeal A ^ m) • (⊤ : Submodule A B) ↔ y ∈ J ^ m := by
    intro m y
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    rfl
  obtain ⟨M₁, hM₁⟩ := Ideal.exists_maximal B
  refine IsLocalRing.of_unique_max_ideal ⟨M₁, hM₁, fun M₂ hM₂ => ?_⟩
  by_contra hne
  -- Chinese remainder theorem
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x : B, x ∈ M₁ ∧ ∀ M : Ideal B, M.IsMaximal → M ≠ M₁ → 1 - x ∈ M := by
    have h := Ideal.sup_iInf_eq_top (I := M₁) (s := hfin.toFinset.erase M₁) (J := id)
      fun M hM => by
        rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hM
        exact hM₁.coprime_of_ne hM.2 (Ne.symm hM.1)
    obtain ⟨a, ha, c, hc, hac⟩ :=
      Submodule.mem_sup.1 (h.symm ▸ Submodule.mem_top : (1 : B) ∈ M₁ ⊔ ⨅ i ∈ _, id i)
    refine ⟨a, ha, fun M hM hM' => ?_⟩
    rw [← hac, add_sub_cancel_left]
    exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hc M)
      (by simp [Finset.mem_erase, hM, hM'])
  -- `x - x²` lies in the radical of `J`
  have hmax : ∀ P : Ideal B, P.IsPrime → J ≤ P → P.IsMaximal := fun P hP hJP => by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A)
    have hle : maximalIdeal A ≤ P.comap (algebraMap A B) := Ideal.map_le_iff_le_comap.1 hJP
    rw [← (maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.comap _).ne_top hle]
    exact maximalIdeal.isMaximal A
  have hrad : x - x ^ 2 ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hJP, hP⟩
    rw [show x - x ^ 2 = x * (1 - x) by ring]
    by_cases h : P = M₁
    · exact Ideal.mul_mem_right _ P (h ▸ hx₁)
    · exact Ideal.mul_mem_left P _ (hx₂ P (hmax P hP hJP) h)
  obtain ⟨n, hn⟩ := hrad
  have hN : (x - x ^ 2) ^ (n + 1) ∈ J := by rw [pow_succ]; exact J.mul_mem_right _ hn
  -- first approximation `e₀ = 1 - (1 - x^N)^N` of an idempotent
  set e₀ := 1 - (1 - x ^ (n + 1)) ^ (n + 1) with he₀def
  have he₀ : e₀ - e₀ ^ 2 ∈ J := by
    have hid := isIdempotentElem_one_sub_one_sub_pow_pow (Ideal.Quotient.mk J x) (n + 1)
      (by rw [← map_pow, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hN)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, he₀def, map_sub, map_one, map_pow,
      map_sub, map_one, map_pow, sub_eq_zero, pow_two]
    exact hid.symm
  have hx₁' : Ideal.Quotient.mk M₁ x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hx₁
  have hx₂' : Ideal.Quotient.mk M₂ x = 1 := by
    rw [← map_one (Ideal.Quotient.mk M₂), Ideal.Quotient.eq, ← neg_mem_iff, neg_sub]
    exact hx₂ M₂ hM₂ hne
  have he₀₁ : Ideal.Quotient.mk M₁ e₀ = 0 := by
    simp [he₀def, hx₁']
  have he₀₂ : Ideal.Quotient.mk M₂ e₀ = 1 := by
    simp [he₀def, hx₂']
  -- the Newton limit
  obtain ⟨e, he⟩ := IsPrecomplete.prec ‹IsPrecomplete (maximalIdeal A) B›
    (f := idemNewton e₀) fun {m k} hmk => by
      rw [SModEq.sub_mem, hsm, ← neg_mem_iff, neg_sub]
      exact idemNewton_sub_mem he₀ hmk
  have he' : ∀ k, idemNewton e₀ k - e ∈ J ^ k := fun k => (hsm k _).1 (SModEq.sub_mem.1 (he k))
  have hidem : e - e ^ 2 = 0 := by
    refine IsHausdorff.haus (I := maximalIdeal A) inferInstance _ fun k => ?_
    rw [SModEq.sub_mem, sub_zero, hsm]
    rw [show e - e ^ 2 = (idemNewton e₀ k - idemNewton e₀ k ^ 2) -
      (idemNewton e₀ k - e) * (1 - idemNewton e₀ k - e) by ring]
    exact sub_mem (J.pow_le_pow_right (Nat.le_succ k) (idemNewton_sub_sq_mem he₀ k))
      (Ideal.mul_mem_right _ _ (he' k))
  have hJM : ∀ M : Ideal B, M.IsMaximal → J ≤ M := fun M _ => map_maximalIdeal_le_of_isMaximal M
  have h1 : idemNewton e₀ 1 - e ∈ J := by simpa using he' 1
  have he₁ : e ∈ M₁ := by
    rw [show e = idemNewton e₀ 1 - (idemNewton e₀ 1 - e) by ring]
    refine sub_mem ?_ (hJM M₁ hM₁ h1)
    exact Ideal.Quotient.eq_zero_iff_mem.1 (idemNewton_map _ e₀ 0 (.inl rfl) he₀₁ 1)
  have he₂ : 1 - e ∈ M₂ := by
    rw [show 1 - e = (1 - idemNewton e₀ 1) + (idemNewton e₀ 1 - e) by ring]
    refine add_mem ?_ (hJM M₂ hM₂ h1)
    rw [← Ideal.Quotient.eq, map_one]
    exact (idemNewton_map _ e₀ 1 (.inr rfl) he₀₂ 1).symm
  have : IsIdempotentElem e := by
    rw [IsIdempotentElem, ← pow_two, eq_comm, ← sub_eq_zero]; exact hidem
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 this with rfl | rfl
  · exact hM₂.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using he₂))
  · exact hM₁.ne_top ((Ideal.eq_top_iff_one _).2 he₁)

end Local

section IntegralClosure

variable (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

omit [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] in
include K in
lemma isTorsionFree_integralClosure : Module.IsTorsionFree A (integralClosure A L) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  intro a b h
  have h' := congrArg (algebraMap (integralClosure A L) L) h
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at h'
  exact IsFractionRing.injective A K ((algebraMap K L).injective h')

include K in
/-- **The integral closure of a complete discrete valuation ring in a finite separable extension
of its fraction field is local.** -/
theorem isLocalRing_integralClosure : IsLocalRing (integralClosure A L) := by
  haveI := isTorsionFree_integralClosure A K L
  haveI := IsIntegralClosure.finite A K L (integralClosure A L)
  haveI := integralClosure.isDedekindDomain A K L
  refine isLocalRing_of_finite_maximal A ((IsDedekindDomain.primesOver_finite
    (maximalIdeal A) (integralClosure A L)).subset fun M (hM : M.IsMaximal) => ?_)
  refine ⟨hM.isPrime, ⟨?_⟩⟩
  exact (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)).symm

section ValuationSubring

variable {A} {L} (O' : ValuationSubring L) (φ : A →+* O')
  (hφ : (algebraMap O' L).comp φ = algebraMap A L)

omit [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [IsDomain A] [IsFractionRing A K] [IsScalarTower A K L] in
include hφ in
/-- The integral closure of `A` is contained in every valuation subring over `A`. -/
lemma mem_of_mem_integralClosure {x : L} (hx : x ∈ integralClosure A L) : x ∈ O' := by
  obtain ⟨p, hp, h⟩ := hx
  have : IsIntegral O' x := ⟨p.map φ, hp.map φ, by rw [eval₂_map, hφ]; exact h⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  rw [← hy]
  exact y.2

include K hφ in
/-- **Uniqueness of the valuation ring over a complete discrete valuation ring**: a valuation
subring `O'` of `L` with `A → O'` local is contained in (hence equal to) the integral closure. -/
theorem mem_integralClosure_of_mem [IsLocalHom φ] {x : L} (hx : x ∈ O') :
    x ∈ integralClosure A L := by
  set B := integralClosure A L
  haveI := isLocalRing_integralClosure A K L
  haveI := integralClosure.isDedekindDomain A K L
  haveI := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  let i : B →+* O' :=
    (algebraMap B L).codRestrict O' fun b => mem_of_mem_integralClosure O' φ hφ b.2
  have hiφ : i.comp (algebraMap A B) = φ := RingHom.ext fun a => Subtype.ext <| by
    change algebraMap B L (algebraMap A B a) = algebraMap O' L (φ a)
    rw [← IsScalarTower.algebraMap_apply, ← hφ, RingHom.comp_apply]
  have hP : (maximalIdeal O').comap i = maximalIdeal B := by
    have : ((maximalIdeal O').comap i).IsMaximal := by
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A)
      rw [Ideal.comap_comap, hiφ, IsLocalRing.maximalIdeal_comap]
      exact maximalIdeal.isMaximal A
    exact IsLocalRing.eq_maximalIdeal this
  haveI : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_finite_maximals
    ((Set.finite_singleton (maximalIdeal B)).subset fun I hI => IsLocalRing.eq_maximalIdeal hI)
  rcases (ValuationRing.iff_isInteger_or_isInteger B L).1 inferInstance x with ⟨b, hb⟩ | ⟨b, hb⟩
  · rw [← hb]; exact b.2
  by_cases hx0 : x = 0
  · rw [hx0]; exact zero_mem _
  by_cases hbu : IsUnit b
  · have hbc := congrArg (algebraMap B L) hbu.mul_val_inv
    rw [map_mul, map_one, hb, inv_mul_eq_one₀ hx0] at hbc
    rw [hbc]
    exact (↑hbu.unit⁻¹ : B).2
  · exfalso
    have hbm : b ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).2 hbu
    rw [← hP, Ideal.mem_comap] at hbm
    refine (IsLocalRing.mem_maximalIdeal _).1 hbm
      (IsUnit.of_mul_eq_one (a := i b) ⟨x, hx⟩ (Subtype.ext ?_))
    change algebraMap B L b * x = 1
    rw [hb, inv_mul_cancel₀ hx0]

include K hφ in
/-- **A valuation subring over a complete discrete valuation ring `A` (with `A → O'` local) in a
finite separable extension is finite over `A`.** -/
theorem finite_of_isLocalHom [IsLocalHom φ] : φ.Finite := by
  letI := φ.toAlgebra
  haveI := IsIntegralClosure.finite A K L (integralClosure A L)
  let f : integralClosure A L →ₗ[A] O' :=
    { toFun b := ⟨b, mem_of_mem_integralClosure O' φ hφ b.2⟩
      map_add' _ _ := rfl
      map_smul' a b := Subtype.ext <| by
        simp only [RingHom.id_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        change algebraMap A L a * (b : L) = ((φ a : O') : L) * b
        rw [← hφ]
        rfl }
  exact Module.Finite.of_surjective f fun y =>
    ⟨⟨y, mem_integralClosure_of_mem K O' φ hφ y.2⟩, rfl⟩

end ValuationSubring

end IntegralClosure

end TemperedFundamentalGroups
