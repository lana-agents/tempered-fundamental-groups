/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# Zariski descent of algebras along a finite basic-open cover (generic commutative algebra)

This file is **generic commutative algebra** (it imports only Mathlib and is independent of the rest
of the project). It provides the gluing of algebras along a finite cover of `Spec R` by basic opens
`D(s i)`, needed for the formal patching step M2.3 of Blueprint §12.8.

## The descent datum

Let `s : ι → R` with `ι` finite. A descent datum (`ZariskiDescent.Datum`) consists of an
`R`-algebra `B J` for every finite set `J ⊆ ι` (thought of as an algebra over `D(∏_{j ∈ J} s j)`),
with `s j` invertible in `B J` for `j ∈ J`, and `R`-algebra maps `ρ : B J → B K` for `J ⊆ K`,
compatible with composition, such that for nonempty `J` the map `B J → B K` is a localization away
from `∏_{k ∈ K \ J} s k`. This functorial format (a "Čech" presheaf on the finite subsets) has no
separate cocycle condition: the cocycle condition is the compatibility of `ρ` with composition.
(In the application the `B J` are determined up to unique isomorphism, e.g. finite étale lifts, and
the maps `ρ` and their compatibility come from full faithfulness.)

## Main results

* `ZariskiDescent.Datum.glued`: the glued algebra, the equalizer of `∏ B {i} ⇉ ∏ B {i, j}`.
* **`ZariskiDescent.Datum.isLocalization_eval`**: `B {k}` is the localization of the glued algebra
  away from `s k`, via the projection `eval k`. (This does not need the `s i` to generate the unit
  ideal; that hypothesis is needed for the following properties.)
* `ZariskiDescent.Datum.finite_glued`, `ZariskiDescent.Datum.flat_glued`,
  `ZariskiDescent.Datum.flat_glued_of`: if `Σ R s i = R` and every `B {i}` is finite over
  `R[1/s i]` (resp. flat over `R`, resp. over an `R`-algebra base `A`), the glued algebra is finite
  (resp. flat over `R`, resp. over `A`) (Mathlib's `Module.Finite.of_localizationSpan'`,
  `Module.flat_of_isLocalized_span`).
* **`ZariskiDescent.Datum.bijective_lift`**: uniqueness — an `R`-algebra `M` with compatible maps
  `M → B {i}` that are localizations away from `s i` is isomorphic to the glued algebra (if
  `Σ R s i = R`); this is the sheaf property of quasi-coherent modules (Stacks, Lemma 10.24.1,
  Tag 00EK: `M → ∏ M_{f_i} ⇉ ∏ M_{f_i f_j}` is exact), checked locally.

Together: effective descent of (finite, flat) quasi-coherent algebras along finite basic-open covers
of an affine scheme. The proof of `isLocalization_eval` is elementwise (localization commutes
with the finite equalizer); compare the classical glueing in Stacks, Section 10.24.
-/

universe u v w

namespace ZariskiDescent

open Finset

variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι] (s : ι → R)
  (B : Finset ι → Type w) [∀ J, CommRing (B J)] [∀ J, Algebra R (B J)]

/-- A **Zariski descent datum** of `R`-algebras along `s : ι → R`: an algebra over each
`D(∏_{j ∈ J} s j)`, with restriction maps that are localizations, compatible with composition. -/
structure Datum where
  /-- The restriction maps. -/
  ρ : ∀ {J K : Finset ι}, J ⊆ K → B J →ₐ[R] B K
  ρ_ρ : ∀ {J K L : Finset ι} (h₁ : J ⊆ K) (h₂ : K ⊆ L) (x : B J),
    ρ h₂ (ρ h₁ x) = ρ (h₁.trans h₂) x
  isUnit : ∀ {J : Finset ι} {j : ι}, j ∈ J → IsUnit (algebraMap R (B J) (s j))
  isLocalization : ∀ {J K : Finset ι} (h : J ⊆ K), J.Nonempty →
    letI := (ρ h).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (B J) (∏ k ∈ K \ J, s k)) (B K)

namespace Datum

variable {s B} (D : Datum s B)

/-- Compatibility of the restriction maps, with an arbitrary proof of the composite inclusion. -/
lemma ρ_ρ' {J K L : Finset ι} (h₁ : J ⊆ K) (h₂ : K ⊆ L) (h₃ : J ⊆ L) (x : B J) :
    D.ρ h₂ (D.ρ h₁ x) = D.ρ h₃ x :=
  D.ρ_ρ h₁ h₂ x

lemma prod_dvd {J K : Finset ι} {k : ι} (hk : K \ J ⊆ {k}) : (∏ i ∈ K \ J, s i) ∣ s k := by
  rcases Finset.subset_singleton_iff.mp hk with h | h <;> simp [h]

/-- Elements killed by a restriction `B J → B K` with `K \ J ⊆ {k}` are `s k`-power torsion. -/
lemma exists_pow_mul_eq_zero {J K : Finset ι} (h : J ⊆ K) (hJ : J.Nonempty) {k : ι}
    (hk : K \ J ⊆ {k}) {x : B J} (hx : D.ρ h x = 0) :
    ∃ n : ℕ, algebraMap R (B J) (s k) ^ n * x = 0 := by
  letI := (D.ρ h).toRingHom.toAlgebra
  have := D.isLocalization h hJ
  have hx' : algebraMap (B J) (B K) x = 0 := hx
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap R (B J) (∏ k ∈ K \ J, s k))) (B K) x).mp hx'
  obtain ⟨t, ht⟩ := prod_dvd (s := s) hk
  refine ⟨n, ?_⟩
  simp only at hn
  rw [ht, map_mul, mul_pow, mul_comm (_ ^ n), mul_assoc, hn, mul_zero]

/-- Every element of `B K` becomes a restriction after multiplying by a power of `s k`, if
`K \ J ⊆ {k}`. -/
lemma exists_ρ_eq {J K : Finset ι} (h : J ⊆ K) (hJ : J.Nonempty) {k : ι}
    (hk : K \ J ⊆ {k}) (y : B K) :
    ∃ (x : B J) (n : ℕ), D.ρ h x = y * algebraMap R (B K) (s k) ^ n := by
  letI := (D.ρ h).toRingHom.toAlgebra
  have := D.isLocalization h hJ
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hxn⟩ := IsLocalization.surj
    (Submonoid.powers (algebraMap R (B J) (∏ k ∈ K \ J, s k))) y
  obtain ⟨t, ht⟩ := prod_dvd (s := s) hk
  refine ⟨x * algebraMap R (B J) t ^ n, n, ?_⟩
  have hc : ∀ r : R, algebraMap (B J) (B K) (algebraMap R (B J) r) = algebraMap R (B K) r :=
    fun r ↦ (D.ρ h).commutes r
  simp only [map_pow, hc] at hxn
  change algebraMap (B J) (B K) (x * algebraMap R (B J) t ^ n) = _
  rw [map_mul, map_pow, hc, ← hxn, ht, map_mul, mul_pow, mul_assoc]

/-- The inclusion `{i} ⊆ {i, j}`. -/
lemma sub_left (i j : ι) : ({i} : Finset ι) ⊆ {i, j} := by simp

/-- The inclusion `{j} ⊆ {i, j}`. -/
lemma sub_right (i j : ι) : ({j} : Finset ι) ⊆ {i, j} := by simp

/-- The **glued algebra**: families `(b i)_i ∈ ∏ B {i}` agreeing on all overlaps `B {i, j}`. -/
def glued : Subalgebra R (∀ i : ι, B {i}) where
  carrier := {b | ∀ i j, D.ρ (sub_left i j) (b i) = D.ρ (sub_right i j) (b j)}
  mul_mem' {a b} ha hb i j := by simp [map_mul, ha i j, hb i j]
  add_mem' {a b} ha hb i j := by simp [map_add, ha i j, hb i j]
  algebraMap_mem' r i j := by simp

lemma mem_glued {b : ∀ i : ι, B {i}} :
    b ∈ D.glued ↔ ∀ i j, D.ρ (sub_left i j) (b i) = D.ρ (sub_right i j) (b j) := Iff.rfl

/-- The projection of the glued algebra to the `k`-th piece. -/
def eval (k : ι) : D.glued →ₐ[R] B {k} := (Pi.evalAlgHom R (fun i ↦ B {i}) k).comp D.glued.val

@[simp] lemma eval_apply (k : ι) (b : D.glued) : D.eval k b = (b : ∀ i, B {i}) k := rfl

lemma eval_algebraMap (k : ι) (r : R) :
    D.eval k (algebraMap R D.glued r) = algebraMap R (B {k}) r := (D.eval k).commutes r

/-- Restriction of a glued family to an overlap containing `i`. -/
lemma ρ_eval_eq (b : D.glued) {i j : ι} {K : Finset ι} (hi : {i} ⊆ K) (hj : {j} ⊆ K)
    (hij : ({i, j} : Finset ι) ⊆ K) : D.ρ hi (b.1 i) = D.ρ hj (b.1 j) := by
  rw [← D.ρ_ρ' (sub_left i j) hij hi, ← D.ρ_ρ' (sub_right i j) hij hj, b.2 i j]

variable [Finite ι]

section

variable (k : ι)

omit [Finite ι] in
lemma sdiff_pair_left (i : ι) : ({i, k} : Finset ι) \ {i} ⊆ {k} := by
  intro x; simp only [mem_sdiff, mem_insert, mem_singleton]; tauto

omit [Finite ι] in
lemma sdiff_triple (i j : ι) : ({i, j, k} : Finset ι) \ {i, j} ⊆ {k} := by
  intro x; simp only [mem_sdiff, mem_insert, mem_singleton]; tauto

/-- Elements of the glued algebra vanishing in `B {k}` are killed by a power of `s k`. -/
lemma exists_pow_smul_eq_zero (b : D.glued) (hb : D.eval k b = 0) :
    ∃ n : ℕ, algebraMap R D.glued (s k) ^ n * b = 0 := by
  have := Fintype.ofFinite ι
  have H : ∀ i, ∃ n : ℕ, algebraMap R (B {i}) (s k) ^ n * b.1 i = 0 := fun i ↦ by
    refine D.exists_pow_mul_eq_zero (sub_left i k) (by simp) (sdiff_pair_left k i) ?_
    rw [b.2 i k]
    simp only [eval_apply] at hb
    rw [hb, map_zero]
  choose n hn using H
  refine ⟨∑ i, n i, Subtype.ext (funext fun i ↦ ?_)⟩
  have hle : n i ≤ ∑ i, n i := Finset.single_le_sum (by simp) (Finset.mem_univ i)
  change algebraMap R (B {i}) (s k) ^ (∑ i, n i) * b.1 i = 0
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hn, mul_zero]

/-- Every element of `B {k}` times a power of `s k` comes from the glued algebra. -/
lemma exists_eval_eq (y : B {k}) :
    ∃ (b : D.glued) (n : ℕ), D.eval k b = y * algebraMap R (B {k}) (s k) ^ n := by
  have := Fintype.ofFinite ι
  -- local sections `c i` on `D(s i)` restricting to `y * s k ^ m i` on `D(s i s k)`
  have H : ∀ i, ∃ (c : B {i}) (m : ℕ), D.ρ (sub_left i k) c =
      D.ρ (sub_right i k) y * algebraMap R _ (s k) ^ m :=
    fun i ↦ D.exists_ρ_eq (sub_left i k) (by simp) (sdiff_pair_left k i) _
  choose c m hcm using H
  set M := ∑ i, m i
  have hmM : ∀ i, m i ≤ M := fun i ↦ Finset.single_le_sum (by simp) (Finset.mem_univ i)
  set c' : ∀ i, B {i} := fun i ↦ c i * algebraMap R _ (s k) ^ (M - m i)
  have hc' : ∀ i, D.ρ (sub_left i k) (c' i) =
      D.ρ (sub_right i k) (y * algebraMap R _ (s k) ^ M) := fun i ↦ by
    simp only [c', map_mul, map_pow, AlgHom.commutes, hcm, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (hmM i)]
  clear_value c'
  -- on the double overlaps the `c' i` agree after multiplying by a power of `s k`
  have H2 : ∀ i j, ∃ n : ℕ, algebraMap R (B {i, j}) (s k) ^ n *
      (D.ρ (sub_left i j) (c' i) - D.ρ (sub_right i j) (c' j)) = 0 := by
    intro i j
    refine D.exists_pow_mul_eq_zero (K := {i, j, k}) (by intro x; simp; tauto) (by simp)
      (sdiff_triple k i j) ?_
    have hi : ({i} : Finset ι) ⊆ {i, j, k} := by simp
    have hj : ({j} : Finset ι) ⊆ {i, j, k} := by intro x; simp; tauto
    have hk : ({k} : Finset ι) ⊆ {i, j, k} := by intro x; simp; tauto
    have hik : ({i, k} : Finset ι) ⊆ {i, j, k} := by intro x; simp; tauto
    have hjk : ({j, k} : Finset ι) ⊆ {i, j, k} := by intro x; simp; tauto
    rw [map_sub, D.ρ_ρ' _ _ hi, D.ρ_ρ' _ _ hj, ← D.ρ_ρ' (sub_left i k) hik hi,
      ← D.ρ_ρ' (sub_left j k) hjk hj, hc', hc', D.ρ_ρ' _ _ hk, D.ρ_ρ' _ _ hk, sub_self]
  choose n hn using H2
  -- the correction at `k` itself (the restriction `B {k} → B {k, k}` is injective up to torsion)
  obtain ⟨n₀, hn₀⟩ := D.exists_pow_mul_eq_zero (sub_left k k) (by simp) (sdiff_pair_left k k)
    (x := c' k - y * algebraMap R _ (s k) ^ M) (by
      rw [map_sub, hc']; exact sub_self _)
  set N := ∑ i, ∑ j, n i j + n₀
  have hnN : ∀ i j, n i j ≤ N := fun i j ↦
    ((Finset.single_le_sum (f := n i) (by simp) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i ↦ ∑ j, n i j) (by simp) (Finset.mem_univ i))).trans
      (Nat.le_add_right _ _)
  refine ⟨⟨fun i ↦ algebraMap R _ (s k) ^ N * c' i, fun i j ↦ ?_⟩, M + N, ?_⟩
  · change D.ρ _ (algebraMap R _ (s k) ^ N * c' i) = D.ρ _ (algebraMap R _ (s k) ^ N * c' j)
    rw [map_mul, map_mul, map_pow, map_pow, AlgHom.commutes, AlgHom.commutes,
      ← sub_eq_zero, ← mul_sub, ← Nat.sub_add_cancel (hnN i j), pow_add, mul_assoc,
      hn i j, mul_zero]
  · simp only [eval_apply]
    have : algebraMap R (B {k}) (s k) ^ N * (c' k - y * algebraMap R _ (s k) ^ M) = 0 := by
      rw [show N = ∑ i, ∑ j, n i j + n₀ from rfl, pow_add, mul_assoc, hn₀, mul_zero]
    rw [mul_sub, sub_eq_zero] at this
    rw [this, pow_add]; ring

end

/-- The algebra structure of `B {k}` over the glued algebra (via `eval k`). -/
@[reducible] def algebraEval (k : ι) : Algebra D.glued (B {k}) := (D.eval k).toRingHom.toAlgebra

/-- **Descent, local form**: `B {k}` is the localization of the glued algebra away from `s k`. -/
theorem isLocalization_eval (k : ι) :
    letI := D.algebraEval k
    IsLocalization.Away (algebraMap R D.glued (s k)) (B {k}) := by
  letI := D.algebraEval k
  have hm : ∀ b : D.glued, algebraMap D.glued (B {k}) b = D.eval k b := fun _ ↦ rfl
  refine (isLocalization_iff ..).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simpa [hm, eval_algebraMap] using (D.isUnit (mem_singleton_self k)).pow n
  · intro y
    obtain ⟨b, n, hb⟩ := D.exists_eval_eq k y
    exact ⟨⟨b, ⟨_, n, rfl⟩⟩, by simp [hm, hb]⟩
  · intro a b hab
    obtain ⟨n, hn⟩ := D.exists_pow_smul_eq_zero k (a - b) (by simpa [hm, sub_eq_zero] using hab)
    exact ⟨⟨_, n, rfl⟩, by simpa [mul_sub, sub_eq_zero] using hn⟩

/-- `eval k`, as an `R`-linear map, is a localization away from `s k`. -/
instance isLocalizedModule_eval (k : ι) :
    IsLocalizedModule (Submonoid.powers (s k)) (D.eval k).toLinearMap := by
  letI := D.algebraEval k
  haveI : IsScalarTower R D.glued (B {k}) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (D.eval_algebraMap k r).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D.glued (Submonoid.powers (s k)))
      (B {k}) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact D.isLocalization_eval k
  exact isLocalizedModule_iff_isLocalization.mpr this

section Span

variable (hs : Ideal.span (Set.range s) = ⊤)
include hs

/-- If the `s i` generate the unit ideal and every `B {i}` is finite over a localization `Rₗ i`
of `R` away from `s i`, the glued algebra is a finite `R`-module. -/
theorem finite_glued (Rₗ : ι → Type*) [∀ i, CommRing (Rₗ i)] [∀ i, Algebra R (Rₗ i)]
    [∀ i, IsLocalization.Away (s i) (Rₗ i)] [∀ i, Algebra (Rₗ i) (B {i})]
    [∀ i, IsScalarTower R (Rₗ i) (B {i})] (H : ∀ i, Module.Finite (Rₗ i) (B {i})) :
    Module.Finite R D.glued := by
  choose idx hidx using fun g : Set.range s ↦ g.2
  haveI : ∀ g : Set.range s, IsLocalization.Away g.val (Rₗ (idx g)) := fun g ↦ by
    rw [← hidx g]; infer_instance
  haveI : ∀ g : Set.range s, IsLocalizedModule.Away g.val (D.eval (idx g)).toLinearMap :=
    fun g ↦ by rw [← hidx g]; exact D.isLocalizedModule_eval (idx g)
  exact Module.Finite.of_localizationSpan' (Set.range s) hs (Rₚ := fun g ↦ Rₗ (idx g))
    (fun g ↦ (D.eval (idx g)).toLinearMap) (fun g ↦ H (idx g))

/-- If the `s i` generate the unit ideal and every `B {i}` is flat over `R`, the glued algebra is
flat over `R`. -/
theorem flat_glued (H : ∀ i, Module.Flat R (B {i})) : Module.Flat R D.glued := by
  choose idx hidx using fun g : Set.range s ↦ g.2
  haveI : ∀ g : Set.range s, IsLocalizedModule.Away g.val (D.eval (idx g)).toLinearMap :=
    fun g ↦ by rw [← hidx g]; exact D.isLocalizedModule_eval (idx g)
  exact Module.flat_of_isLocalized_span R D.glued (Set.range s) hs (fun g ↦ B {idx g})
    (fun g ↦ (D.eval (idx g)).toLinearMap) (fun g ↦ H (idx g))

/-- Flatness over a base: if the `s i` generate the unit ideal, `R` is an `A`-algebra and every
`B {i}` is flat over `A` (compatibly), the glued algebra is flat over `A`. (In the application `A`
is the coordinate ring of a chart of `ℙ¹` and `R` that of its preimage in a finite model: the
covering is flat over `ℙ¹` but not over the model at the nodes.) -/
theorem flat_glued_of (A : Type*) [CommRing A] [Algebra A R] [∀ J, Algebra A (B J)]
    [∀ J, IsScalarTower A R (B J)] (H : ∀ i, Module.Flat A (B {i})) : Module.Flat A D.glued := by
  choose idx hidx using fun g : Set.range s ↦ g.2
  haveI : ∀ g : Set.range s, IsLocalizedModule.Away g.val (D.eval (idx g)).toLinearMap :=
    fun g ↦ by rw [← hidx g]; exact D.isLocalizedModule_eval (idx g)
  exact Module.flat_of_isLocalized_span (R := A) R D.glued (Set.range s) hs
    (fun g ↦ B {idx g}) (fun g ↦ (D.eval (idx g)).toLinearMap) (fun g ↦ H (idx g))

/-- The map from an algebra with compatible localizations to the glued algebra. -/
def lift {M : Type*} [CommRing M] [Algebra R M] (φ : ∀ i, M →ₐ[R] B {i})
    (hφ : ∀ i j x, D.ρ (sub_left i j) (φ i x) = D.ρ (sub_right i j) (φ j x)) :
    M →ₐ[R] D.glued :=
  (AlgHom.pi φ).codRestrict D.glued fun x i j ↦ hφ i j x

omit hs [Finite ι] in
@[simp] lemma eval_lift {M : Type*} [CommRing M] [Algebra R M] (φ : ∀ i, M →ₐ[R] B {i})
    (hφ : ∀ i j x, D.ρ (sub_left i j) (φ i x) = D.ρ (sub_right i j) (φ j x)) (i : ι) (x : M) :
    D.eval i (D.lift φ hφ x) = φ i x := rfl

/-- **Descent, uniqueness** (the sheaf property): if the `s i` generate the unit ideal, an
`R`-algebra `M` with compatible maps `φ i : M → B {i}` which are localizations away from `s i` is
isomorphic to the glued algebra via `lift`. -/
theorem bijective_lift {M : Type*} [CommRing M] [Algebra R M] (φ : ∀ i, M →ₐ[R] B {i})
    (hφ : ∀ i j x, D.ρ (sub_left i j) (φ i x) = D.ρ (sub_right i j) (φ j x))
    [hl : ∀ i, IsLocalizedModule (Submonoid.powers (s i)) (φ i).toLinearMap] :
    Function.Bijective (D.lift φ hφ) := by
  choose idx hidx using fun g : Set.range s ↦ g.2
  haveI : ∀ g : Set.range s, IsLocalizedModule.Away g.val (φ (idx g)).toLinearMap :=
    fun g ↦ by rw [← hidx g]; exact hl (idx g)
  haveI : ∀ g : Set.range s, IsLocalizedModule.Away g.val (D.eval (idx g)).toLinearMap :=
    fun g ↦ by rw [← hidx g]; exact D.isLocalizedModule_eval (idx g)
  refine bijective_of_isLocalized_span (Set.range s) hs (fun g ↦ B {idx g})
    (fun g ↦ (φ (idx g)).toLinearMap) (fun g ↦ B {idx g}) (fun g ↦ (D.eval (idx g)).toLinearMap)
    (D.lift φ hφ).toLinearMap fun g ↦ ?_
  have : IsLocalizedModule.map (Submonoid.powers g.val) (φ (idx g)).toLinearMap
      (D.eval (idx g)).toLinearMap (D.lift φ hφ).toLinearMap = LinearMap.id := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers g.val) (φ (idx g)).toLinearMap
      (φ (idx g)).toLinearMap
    rw [IsLocalizedModule.map_comp]
    ext x
    rfl
  rw [this]
  exact Function.bijective_id

/-- The isomorphism of `M` with the glued algebra (uniqueness of descent). -/
noncomputable def liftEquiv {M : Type*} [CommRing M] [Algebra R M] (φ : ∀ i, M →ₐ[R] B {i})
    (hφ : ∀ i j x, D.ρ (sub_left i j) (φ i x) = D.ρ (sub_right i j) (φ j x))
    [∀ i, IsLocalizedModule (Submonoid.powers (s i)) (φ i).toLinearMap] :
    M ≃ₐ[R] D.glued :=
  AlgEquiv.ofBijective (D.lift φ hφ) (D.bijective_lift hs φ hφ)

end Span

end Datum

end ZariskiDescent
