/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CompletionMap
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The `f`-adic completion as a product of local completions ("lemma F")

Let `R` be a Noetherian ring, `f : R`, and `𝔪 : ι → Ideal R` (`ι` finite) pairwise distinct
maximal ideals with `f ∈ 𝔪 i` for all `i` and `⨅ i, 𝔪 i ≤ √(f)` (equivalently: the primes
containing `f` are exactly the `𝔪 i`, see `iInf_le_radical_of_forall_prime`). Then

* **`CompletionProd.equiv`** : `R^∧_{(f)} ≃+* ∏ i, R^∧_{𝔪 i}`, whose components are the
  completion maps `CompletionMap.map (RingHom.id R) _` (as `(f) ⊆ 𝔪 i`), and which is compatible
  with the maps from `R` (`equiv_algebraMap`);
* the idempotents **`idem i`** `:= equiv.symm (Pi.single i 1)` (idempotent, orthogonal,
  summing to `1`), and **`quotEquiv i`** : `R^∧_{(f)} ⧸ (1 - idem i) ≃+* R^∧_{𝔪 i}`, again
  compatible with the maps from `R` (`quotEquiv_algebraMap`).

## Proof (Chinese remainder route)

Put `P := ∏ i, 𝔪 i`. The powers `𝔪 i ^ k` are pairwise coprime, so
`⨅ i, 𝔪 i ^ k = P ^ k`, and `P ≤ ⨅ i, 𝔪 i ≤ √(f)`; as `R` is Noetherian, `P ^ N ≤ (f)` for
some `N`, hence `⨅ i, 𝔪 i ^ ((N + 1) n) ≤ (f) ^ n` for all `n` (`iInf_pow_lvl_le`).
The inverse of the componentwise map is the lift (`AdicCompletion.liftRingHom`) of the compatible
family `∏ i, R^∧_{𝔪 i} → ∏ i, R ⧸ 𝔪 i ^ ((N + 1) n) ≅ R ⧸ ⨅ i, 𝔪 i ^ ((N + 1) n) → R ⧸ (f) ^ n`
(Chinese remainder theorem `Ideal.quotientInfRingEquivPiQuotient` in the middle). Both
composites are checked levelwise via the characterisation `invLev_spec` of the levels.
-/

universe u v

namespace SemistableReduction

namespace CompletionProd

noncomputable section

open AdicCompletion Function

variable {R : Type u} [CommRing R] (f : R) {ι : Type v} [Finite ι] (𝔪 : ι → Ideal R)

omit [Finite ι] in
/-- The hypothesis `⨅ i, 𝔪 i ≤ √(f)` follows from: every prime containing `f` is some `𝔪 i`. -/
lemma iInf_le_radical_of_forall_prime
    (hprime : ∀ p : Ideal R, p.IsPrime → f ∈ p → ∃ i, p = 𝔪 i) :
    ⨅ i, 𝔪 i ≤ (Ideal.span {f}).radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro p ⟨hle, hp⟩
  obtain ⟨i, rfl⟩ := hprime p hp (hle (Ideal.mem_span_singleton_self f))
  exact iInf_le _ i

omit [Finite ι] in
lemma span_le (hf : ∀ i, f ∈ 𝔪 i) (i : ι) : (Ideal.span {f}).map (RingHom.id R) ≤ 𝔪 i := by
  rw [Ideal.map_id, Ideal.span_le, Set.singleton_subset_iff]
  exact hf i

variable [∀ i, (𝔪 i).IsMaximal]

omit [Finite ι] in
lemma pairwise_isCoprime (hinj : Function.Injective 𝔪) (k : ℕ) :
    Pairwise (IsCoprime on fun i ↦ 𝔪 i ^ k) :=
  fun _ _ hij ↦ (Ideal.isCoprime_of_isMaximal (hinj.ne hij)).pow

omit [Finite ι] in
lemma iInf_pow_eq [Fintype ι] (hinj : Function.Injective 𝔪) (k : ℕ) :
    ⨅ i, 𝔪 i ^ k = (∏ i, 𝔪 i) ^ k := by
  rw [← Finset.prod_pow, Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (fun i _ j _ hij ↦ pairwise_isCoprime 𝔪 hinj k hij)]
  simp

variable [IsNoetherianRing R]

lemma exists_iInf_pow_le (hinj : Function.Injective 𝔪)
    (hrad : ⨅ i, 𝔪 i ≤ (Ideal.span {f}).radical) :
    ∃ N : ℕ, ∀ n, ⨅ i, 𝔪 i ^ ((N + 1) * n) ≤ Ideal.span {f} ^ n := by
  have := Fintype.ofFinite ι
  have hP : ∏ i, 𝔪 i ≤ (Ideal.span {f}).radical := by
    have h1 := iInf_pow_eq 𝔪 hinj 1
    simp only [pow_one] at h1
    rwa [← h1]
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hP (IsNoetherian.noetherian _)
  refine ⟨N, fun n ↦ ?_⟩
  rw [iInf_pow_eq 𝔪 hinj, pow_mul]
  exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ N)).trans hN) n

/-- The level `(N + 1) n` of the local completions used to reach level `n` of the `f`-adic one. -/
def lvl (hinj : Function.Injective 𝔪) (hrad : ⨅ i, 𝔪 i ≤ (Ideal.span {f}).radical) (n : ℕ) :
    ℕ :=
  (Classical.choose (exists_iInf_pow_le f 𝔪 hinj hrad) + 1) * n

variable {f 𝔪}
variable (hinj : Function.Injective 𝔪) (hf : ∀ i, f ∈ 𝔪 i)
  (hrad : ⨅ i, 𝔪 i ≤ (Ideal.span {f}).radical)

include hinj hrad in
lemma iInf_pow_lvl_le (n : ℕ) : ⨅ i, 𝔪 i ^ lvl f 𝔪 hinj hrad n ≤ Ideal.span {f} ^ n :=
  Classical.choose_spec (exists_iInf_pow_le f 𝔪 hinj hrad) n

lemma le_lvl (n : ℕ) : n ≤ lvl f 𝔪 hinj hrad n :=
  Nat.le_mul_of_pos_left n (Nat.succ_pos _)

lemma lvl_mono {m n : ℕ} (h : m ≤ n) : lvl f 𝔪 hinj hrad m ≤ lvl f 𝔪 hinj hrad n :=
  Nat.mul_le_mul_left _ h

omit [Finite ι] [∀ i, (𝔪 i).IsMaximal] [IsNoetherianRing R] in
lemma factorPow_evalₐ {S : Type*} [CommRing S] {I : Ideal S} {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  have h := CompletionMap.lev_compat (RingHom.id S) (I₁ := I) (I₂ := I) (by simp) hle
  have hx := congr($h x)
  simp only [RingHom.comp_apply, CompletionMap.lev, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] at hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ I m x)
  rw [← ha, ← hb, Ideal.quotientMap_mk, Ideal.quotientMap_mk] at hx
  rw [← ha, ← hb]
  simpa using hx

/-- Levels of the inverse map: `∏ R^∧_{𝔪 i} → ∏ R/𝔪 i ^ k ≅ R/⨅ 𝔪 i ^ k → R/(f) ^ n`. -/
def invLev (n : ℕ) : ((i : ι) → AdicCompletion (𝔪 i) R) →+* R ⧸ Ideal.span {f} ^ n :=
  (Ideal.Quotient.factor (iInf_pow_lvl_le hinj hrad n)).comp
    ((Ideal.quotientInfRingEquivPiQuotient _
      (pairwise_isCoprime 𝔪 hinj (lvl f 𝔪 hinj hrad n))).symm.toRingHom.comp
      (RingHom.pi fun i ↦ (evalₐ (𝔪 i) (lvl f 𝔪 hinj hrad n)).toRingHom.comp
        (Pi.evalRingHom _ i)))

omit [IsNoetherianRing R] in
include hinj in
lemma exists_mk_eq (k : ℕ) (y : (i : ι) → AdicCompletion (𝔪 i) R) :
    ∃ r : R, ∀ i, Ideal.Quotient.mk (𝔪 i ^ k) r = evalₐ (𝔪 i) k (y i) :=
  Ideal.pi_quotient_surjective (pairwise_isCoprime 𝔪 hinj k) _

lemma invLev_spec (n : ℕ) (y : (i : ι) → AdicCompletion (𝔪 i) R) (r : R)
    (hr : ∀ i, Ideal.Quotient.mk _ r = evalₐ (𝔪 i) (lvl f 𝔪 hinj hrad n) (y i)) :
    invLev hinj hrad n y = Ideal.Quotient.mk _ r := by
  have : (Ideal.quotientInfRingEquivPiQuotient _
      (pairwise_isCoprime 𝔪 hinj (lvl f 𝔪 hinj hrad n))).symm
      (fun i ↦ evalₐ (𝔪 i) (lvl f 𝔪 hinj hrad n) (y i)) = Ideal.Quotient.mk _ r := by
    rw [RingEquiv.symm_apply_eq]
    funext i
    exact (hr i).symm
  simp only [invLev, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← Ideal.Quotient.factor_mk (iInf_pow_lvl_le hinj hrad n), ← this]
  rfl

lemma invLev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (invLev hinj hrad n) = invLev hinj hrad m := by
  ext y
  obtain ⟨r, hr⟩ := exists_mk_eq hinj (lvl f 𝔪 hinj hrad n) y
  obtain ⟨s, hs⟩ := exists_mk_eq hinj (lvl f 𝔪 hinj hrad m) y
  rw [RingHom.comp_apply, invLev_spec hinj hrad n y r hr, invLev_spec hinj hrad m y s hs,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  refine iInf_pow_lvl_le hinj hrad m (Ideal.mem_iInf.2 fun i ↦ ?_)
  rw [← Ideal.Quotient.eq, hs i,
    ← factorPow_evalₐ (lvl_mono hinj hrad hle), ← hr i, Ideal.Quotient.factor_mk]

/-- The inverse map `∏ R^∧_{𝔪 i} → R^∧_{(f)}`. -/
def inv : ((i : ι) → AdicCompletion (𝔪 i) R) →+* AdicCompletion (Ideal.span {f}) R :=
  liftRingHom _ (invLev hinj hrad) (invLev_compat hinj hrad)

/-- The component `R^∧_{(f)} → R^∧_{𝔪 i}` (the completion map of `id`). -/
def proj (i : ι) : AdicCompletion (Ideal.span {f}) R →+* AdicCompletion (𝔪 i) R :=
  CompletionMap.map (RingHom.id R) (span_le f 𝔪 hf i)

lemma proj_inv (y : (i : ι) → AdicCompletion (𝔪 i) R) (i : ι) :
    proj hf i (inv hinj hrad y) = y i := by
  refine ext_evalₐ fun n ↦ ?_
  obtain ⟨r, hr⟩ := exists_mk_eq hinj (lvl f 𝔪 hinj hrad n) y
  rw [proj, CompletionMap.evalₐ_map, inv, evalₐ_liftRingHom, invLev_spec hinj hrad n y r hr,
    Ideal.quotientMap_mk, RingHom.id_apply, ← factorPow_evalₐ (le_lvl hinj hrad n), ← hr i,
    Ideal.Quotient.factor_mk]

lemma inv_proj (x : AdicCompletion (Ideal.span {f}) R) :
    inv hinj hrad (fun i ↦ proj hf i x) = x := by
  refine ext_evalₐ fun n ↦ ?_
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (evalₐ _ (lvl f 𝔪 hinj hrad n) x)
  rw [inv, evalₐ_liftRingHom, invLev_spec hinj hrad n _ t, ← factorPow_evalₐ (le_lvl hinj hrad n),
    ← ht, Ideal.Quotient.factor_mk]
  intro i
  rw [proj, CompletionMap.evalₐ_map, ← ht, Ideal.quotientMap_mk, RingHom.id_apply]

/-- **Lemma F.** The `f`-adic completion is the product of the `𝔪 i`-adic completions. -/
def equiv : AdicCompletion (Ideal.span {f}) R ≃+* ((i : ι) → AdicCompletion (𝔪 i) R) where
  __ := RingHom.pi (proj hf)
  invFun := inv hinj hrad
  left_inv := inv_proj hinj hf hrad
  right_inv y := funext (proj_inv hinj hf hrad y)

lemma equiv_apply (x : AdicCompletion (Ideal.span {f}) R) (i : ι) :
    equiv hinj hf hrad x i = CompletionMap.map (RingHom.id R) (span_le f 𝔪 hf i) x :=
  rfl

lemma equiv_algebraMap (r : R) :
    equiv hinj hf hrad (algebraMap R _ r) = fun _ ↦ algebraMap R _ r :=
  funext fun _ ↦ CompletionMap.map_algebraMap _ _ r

include hinj hrad in
lemma proj_surjective (i : ι) : Function.Surjective (proj hf i) := fun y ↦ by
  classical
  exact ⟨inv hinj hrad (Pi.single i y), by rw [proj_inv, Pi.single_eq_same]⟩

variable [DecidableEq ι]

/-- The idempotent of `R^∧_{(f)}` cutting out the factor `R^∧_{𝔪 i}`. -/
def idem (i : ι) : AdicCompletion (Ideal.span {f}) R :=
  (equiv hinj hf hrad).symm (Pi.single i 1)

lemma equiv_idem (i : ι) : equiv hinj hf hrad (idem hinj hf hrad i) = Pi.single i 1 :=
  (equiv hinj hf hrad).apply_symm_apply _

lemma isIdempotentElem_idem (i : ι) : IsIdempotentElem (idem hinj hf hrad i) := by
  refine (equiv hinj hf hrad).injective ?_
  rw [map_mul, equiv_idem]
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

lemma idem_mul_idem {i j : ι} (hij : i ≠ j) : idem hinj hf hrad i * idem hinj hf hrad j = 0 := by
  refine (equiv hinj hf hrad).injective ?_
  rw [map_mul, equiv_idem, equiv_idem, map_zero]
  funext k
  by_cases hk : k = i
  · subst hk; simp [Pi.single_eq_of_ne hij]
  · simp [Pi.single_eq_of_ne hk]

lemma sum_idem [Fintype ι] : ∑ i, idem hinj hf hrad i = 1 := by
  refine (equiv hinj hf hrad).injective ?_
  rw [map_sum, map_one]
  simp_rw [equiv_idem]
  simpa using Finset.univ_sum_single (1 : (i : ι) → AdicCompletion (𝔪 i) R)

lemma ker_proj (i : ι) : RingHom.ker (proj hf i) = Ideal.span {1 - idem hinj hf hrad i} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  have hx : ∀ z, proj hf i z = equiv hinj hf hrad z i := fun _ ↦ rfl
  constructor
  · intro h
    refine ⟨x, (equiv hinj hf hrad).injective ?_⟩
    rw [map_mul, map_sub, map_one, equiv_idem]
    funext j
    by_cases hj : j = i
    · subst hj; simp [← hx, h]
    · simp [Pi.single_eq_of_ne hj]
  · rintro ⟨a, rfl⟩
    rw [hx, map_mul, map_sub, map_one, equiv_idem]
    simp

/-- **The factor `R^∧_{𝔪 i}` as a quotient** `R^∧_{(f)} ⧸ (1 - idem i)`. -/
def quotEquiv (i : ι) :
    (AdicCompletion (Ideal.span {f}) R ⧸ Ideal.span {1 - idem hinj hf hrad i}) ≃+*
      AdicCompletion (𝔪 i) R :=
  (Ideal.quotEquivOfEq (ker_proj hinj hf hrad i).symm).trans
    (RingHom.quotientKerEquivOfSurjective (proj_surjective hinj hf hrad i))

lemma quotEquiv_mk (i : ι) (x : AdicCompletion (Ideal.span {f}) R) :
    quotEquiv hinj hf hrad i (Ideal.Quotient.mk _ x) =
      CompletionMap.map (RingHom.id R) (span_le f 𝔪 hf i) x := by
  rw [quotEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

lemma quotEquiv_algebraMap (i : ι) (r : R) :
    quotEquiv hinj hf hrad i (algebraMap R _ r) = algebraMap R _ r := by
  rw [← Ideal.Quotient.mk_algebraMap, quotEquiv_mk]
  exact CompletionMap.map_algebraMap _ _ r

end

end CompletionProd

end SemistableReduction
