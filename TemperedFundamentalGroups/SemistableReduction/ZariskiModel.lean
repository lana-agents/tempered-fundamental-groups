/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Zariski models of function fields

Blueprint §9.6 (W5), layer M1. A ring-level (birational) formulation of models of a function
field, after Zariski's abstract varieties: a model of a field `F` over a subring `R ⊆ F` is a
finite set of *charts*, subrings `A ⊆ F` containing `R`; the points of the model are the local
rings `A_𝔭 ⊆ F` of the charts at their primes, and two charts are glued along their common local
rings. Every prime of a chart is the center `𝔪_W ∩ A` of a valuation subring `W ⊇ A`, so the
points are the rings `localAt A W` (`A ≤ W`).

* `localAt A W = {x | ∃ s ∈ A, W(s) = 1, x s ∈ A}`: the localization of `A` at the center of `W`
  (the local ring of the point of `Spec A` at which `W` is centered);
  `localAt_eq_localSubringOfPrime` identifies it with Mathlib's `LocalSubring.ofPrime`.
* `localAt_eq_of_le` (**gluing lemma**): if `A ≤ B ≤ localAt A W`, then
  `localAt B W = localAt A W`.
* `ZariskiModel R`: a finite set of charts containing `R`; `IsSeparated` (Zariski's
  irredundance: a valuation ring dominates at most one point, equivalently
  `B ≤ localAt A W` for charts `A, B ≤ W`), `IsProper` (every valuation subring `W ⊇ R` contains a
  chart: the valuative criterion of properness), `IsNormal`, `IsFiniteType`.
* `center M W`: the **specialization** (reduction) of a valuation subring `W ⊇ R` of `F`: the point
  of the model at which `W` is centered (`center_eq`: computed in any chart contained in `W`).
* For `R = baseRing O F` (`O` a valuation subring of a field `K ⊆ F`): `specialFibre`, the points
  whose maximal ideal contains `𝔪_O`, and `vertexSet`, the valuation subrings `W` of `F` over `O`
  (`W ∩ K = O`) which are points of the model — the local rings of the generic points of the
  components of the special fibre (`mem_vertexSet_iff`: `W ∩ K = O` and `center W = W`).
-/

open IsLocalRing

namespace SemistableReduction

variable {F : Type*} [Field F]

lemma one_le_of_inv_le_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ} (ha : a ≠ 0)
    (h : a⁻¹ ≤ 1) : 1 ≤ a := by
  simpa using (inv_le_one₀ (zero_lt_iff.2 ha)).1 h

/-! ### Local rings at centers of valuations -/

/-- The local ring of the subring `A` at the center of the valuation subring `W`: the elements
`x` with `x s ∈ A` for some `s ∈ A` which is a unit of `W`. For `A ≤ W` it is the localization of
`A` at the prime `𝔪_W ∩ A` (`localAt_eq_localSubringOfPrime`). -/
def localAt (A : Subring F) (W : ValuationSubring F) : Subring F where
  carrier := {x | ∃ s ∈ A, W.valuation s = 1 ∧ x * s ∈ A}
  mul_mem' {x y} := by
    rintro ⟨s, hs, hsW, hxs⟩ ⟨s', hs', hs'W, hys'⟩
    refine ⟨s * s', A.mul_mem hs hs', by rw [map_mul, hsW, hs'W, one_mul], ?_⟩
    rw [show x * y * (s * s') = (x * s) * (y * s') by ring]
    exact A.mul_mem hxs hys'
  one_mem' := ⟨1, A.one_mem, map_one _, by simp⟩
  add_mem' {x y} := by
    rintro ⟨s, hs, hsW, hxs⟩ ⟨s', hs', hs'W, hys'⟩
    refine ⟨s * s', A.mul_mem hs hs', by rw [map_mul, hsW, hs'W, one_mul], ?_⟩
    rw [show (x + y) * (s * s') = (x * s) * s' + (y * s') * s by ring]
    exact A.add_mem (A.mul_mem hxs hs') (A.mul_mem hys' hs)
  zero_mem' := ⟨1, A.one_mem, map_one _, by simp⟩
  neg_mem' {x} := by
    rintro ⟨s, hs, hsW, hxs⟩
    exact ⟨s, hs, hsW, by simpa [neg_mul] using A.neg_mem hxs⟩

variable {A B : Subring F} {W : ValuationSubring F}

lemma mem_localAt {x : F} : x ∈ localAt A W ↔ ∃ s ∈ A, W.valuation s = 1 ∧ x * s ∈ A :=
  Iff.rfl

lemma le_localAt : A ≤ localAt A W := fun x hx ↦
  ⟨1, A.one_mem, map_one _, by simpa using hx⟩

/-- Inverses of the `W`-units of `A` lie in the local ring of `A` at the center of `W`. -/
lemma inv_mem_localAt {s : F} (hs : s ∈ A) (hsW : W.valuation s = 1) : s⁻¹ ∈ localAt A W := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hsW
  exact ⟨s, hs, hsW, by simp [inv_mul_cancel₀ hs0]⟩

lemma localAt_mono (h : A ≤ B) : localAt A W ≤ localAt B W := by
  rintro x ⟨s, hs, hsW, hxs⟩
  exact ⟨s, h hs, hsW, h hxs⟩

/-- The local ring at the center of `W` is contained in `W`. -/
lemma localAt_le (h : A ≤ W.toSubring) : localAt A W ≤ W.toSubring := by
  rintro x ⟨s, hs, hsW, hxs⟩
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hsW
  have hx : x = (x * s) * s⁻¹ := by field_simp
  rw [hx]
  refine W.mul_mem _ _ (h hxs) ?_
  rw [← W.valuation_le_one_iff, map_inv₀, hsW, inv_one]

/-- **Gluing lemma.** If `A ≤ B ≤ localAt A W`, the local rings of `A` and `B` at the center of `W`
coincide. -/
lemma localAt_eq_of_le (hAB : A ≤ B) (hB : B ≤ localAt A W) : localAt B W = localAt A W := by
  refine le_antisymm ?_ (localAt_mono hAB)
  rintro x ⟨s, hs, hsW, hxs⟩
  obtain ⟨s₁, hs₁, hs₁W, h₁⟩ := hB hs
  obtain ⟨s₂, hs₂, hs₂W, h₂⟩ := hB hxs
  refine ⟨s * s₁ * s₂, A.mul_mem h₁ hs₂, by rw [map_mul, map_mul, hsW, hs₁W, hs₂W, one_mul,
    one_mul], ?_⟩
  rw [show x * (s * s₁ * s₂) = (x * s * s₂) * s₁ by ring]
  exact A.mul_mem h₂ hs₁

/-- The local ring of a valuation subring at its own center is itself. -/
lemma localAt_self : localAt W.toSubring W = W.toSubring :=
  le_antisymm (localAt_le le_rfl) le_localAt

/-- If the valuation subring `W` is the local ring of `A` at the center of some `W' ⊇ A`, then it
is the local ring of `A` at its own center. -/
lemma localAt_eq_of_localAt_eq {W' : ValuationSubring F} (hA : A ≤ W'.toSubring)
    (h : localAt A W' = W.toSubring) : localAt A W = W.toSubring := by
  have hW : W.toSubring ≤ W'.toSubring := h ▸ localAt_le hA
  have hAW : A ≤ W.toSubring := h ▸ le_localAt
  refine le_antisymm (localAt_le hAW) (h ▸ ?_)
  rintro x ⟨s, hs, hsW, hxs⟩
  refine ⟨s, hs, ?_, hxs⟩
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hsW
  refine le_antisymm ((W.valuation_le_one_iff s).2 (hAW hs)) ?_
  have hinv : s⁻¹ ∈ W := by
    rw [← ValuationSubring.mem_toSubring, ← h]
    exact inv_mem_localAt hs hsW
  rw [← W.valuation_le_one_iff, map_inv₀] at hinv
  exact one_le_of_inv_le_one (by simpa using hs0) hinv

/-! #### Comparison with `LocalSubring.ofPrime` -/

/-- The prime `𝔪_W ∩ A` of `A` at which `W ⊇ A` is centered. -/
def centerIdeal (A : Subring F) (W : ValuationSubring F) (h : A ≤ W.toSubring) : Ideal A :=
  (maximalIdeal W).comap (Subring.inclusion h)

instance (h : A ≤ W.toSubring) : (centerIdeal A W h).IsPrime :=
  Ideal.comap_isPrime _ _

lemma mem_centerIdeal_iff (h : A ≤ W.toSubring) (a : A) :
    a ∈ centerIdeal A W h ↔ W.valuation (a : F) < 1 := by
  rw [centerIdeal, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

lemma valuation_eq_one_iff_notMem_centerIdeal (h : A ≤ W.toSubring) (a : A) :
    W.valuation (a : F) = 1 ↔ a ∉ centerIdeal A W h := by
  rw [mem_centerIdeal_iff, not_lt]
  exact ⟨fun h' ↦ h'.ge, fun h' ↦ le_antisymm ((W.valuation_le_one_iff _).2 (h a.2)) h'⟩

/-- `localAt A W` is the localization of `A` at the center `𝔪_W ∩ A` of `W`, as in Mathlib's
`LocalSubring.ofPrime`. -/
theorem localAt_eq_localSubringOfPrime (h : A ≤ W.toSubring) :
    localAt A W = (LocalSubring.ofPrime A (centerIdeal A W h)).toSubring := by
  set P := centerIdeal A W h
  have hloc : IsLocalization.AtPrime (LocalSubring.ofPrime A P).toSubring P := inferInstance
  ext x
  constructor
  · rintro ⟨s, hs, hsW, hxs⟩
    have hsP : (⟨s, hs⟩ : A) ∈ P.primeCompl :=
      (valuation_eq_one_iff_notMem_centerIdeal h ⟨s, hs⟩).1 hsW
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hsW
    have hunit := IsLocalization.map_units (LocalSubring.ofPrime A P).toSubring
      (⟨⟨s, hs⟩, hsP⟩ : P.primeCompl)
    obtain ⟨u, hu⟩ := hunit
    have hmem : (x * s) * (u⁻¹ : (LocalSubring.ofPrime A P).toSubring ˣ).1.1 = x := by
      have hu' : (u : (LocalSubring.ofPrime A P).toSubring).1 = s := congrArg Subtype.val hu
      have : ((u⁻¹ : (LocalSubring.ofPrime A P).toSubring ˣ) : _).1 * s = 1 := by
        rw [← hu']
        exact congrArg Subtype.val u.inv_mul
      rw [mul_assoc, mul_comm s, this, mul_one]
    rw [← hmem]
    exact Subring.mul_mem _ (LocalSubring.le_ofPrime A P hxs) (Subtype.prop _)
  · intro hx
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj P.primeCompl (⟨x, hx⟩ :
      (LocalSubring.ofPrime A P).toSubring)
    have hs' := congrArg Subtype.val hs
    refine ⟨(s : A), (s : A).2, (valuation_eq_one_iff_notMem_centerIdeal h s).2 s.2, ?_⟩
    have : x * ((s : A) : F) = ((a : A) : F) := hs'
    rw [this]
    exact a.2

/-! ### Models -/

/-- A **Zariski model** of the field `F` over the subring `R`: a finite set of charts, subrings
of `F` containing `R`. The points of the model are the local rings `localAt A W` of the charts at
the centers of valuation subrings `W ⊇ A`. -/
structure ZariskiModel (R : Subring F) where
  /-- The affine charts. -/
  charts : Finset (Subring F)
  /-- Every chart contains the base ring. -/
  le_chart : ∀ A ∈ charts, R ≤ A

namespace ZariskiModel

variable {R : Subring F} (M : ZariskiModel R)

/-- The points of the model: local rings of the charts at centers of valuation subrings. -/
def points : Set (Subring F) :=
  {B | ∃ A ∈ M.charts, ∃ W : ValuationSubring F, A ≤ W.toSubring ∧ localAt A W = B}

/-- The model is **separated** (Zariski's irredundance: no valuation subring dominates two
distinct points): for charts `A, B ⊆ W`, `B` lies in the local ring of `A` at the center of `W`. -/
def IsSeparated : Prop :=
  ∀ A ∈ M.charts, ∀ B ∈ M.charts, ∀ W : ValuationSubring F, A ≤ W.toSubring →
    B ≤ W.toSubring → B ≤ localAt A W

/-- The model is **proper** (complete, in Zariski's terminology; the existence part of the
valuative criterion): every valuation subring of `F` containing `R` contains a chart. -/
def IsProper : Prop :=
  ∀ W : ValuationSubring F, R ≤ W.toSubring → ∃ A ∈ M.charts, A ≤ W.toSubring

/-- The model is **normal**: every chart is integrally closed in `F`. -/
def IsNormal : Prop :=
  ∀ A ∈ M.charts, ∀ x : F, IsIntegral A x → x ∈ A

/-- The model is **of finite type** over `R`: every chart is generated by `R` and finitely many
elements. -/
def IsFiniteType : Prop :=
  ∀ A ∈ M.charts, ∃ s : Finset F, A = Subring.closure ((R : Set F) ∪ s)

variable {M}

/-- In a separated model the local rings of two charts at the center of `W` coincide. -/
theorem IsSeparated.localAt_eq (hM : M.IsSeparated) {A B : Subring F} (hA : A ∈ M.charts)
    (hB : B ∈ M.charts) (hAW : A ≤ W.toSubring) (hBW : B ≤ W.toSubring) :
    localAt A W = localAt B W := by
  have h₁ : A ⊔ B ≤ localAt A W := sup_le le_localAt (hM A hA B hB W hAW hBW)
  have h₂ : A ⊔ B ≤ localAt B W := sup_le (hM B hB A hA W hBW hAW) le_localAt
  rw [← localAt_eq_of_le le_sup_left h₁, localAt_eq_of_le le_sup_right h₂]

/-- A criterion for separatedness: for charts `A, B ⊆ W`, `B` is contained in the local ring of
`A`, which holds when the generators of `B` are in it. -/
theorem isSeparated_iff : M.IsSeparated ↔ ∀ A ∈ M.charts, ∀ B ∈ M.charts,
    ∀ W : ValuationSubring F, A ≤ W.toSubring → B ≤ W.toSubring → B ≤ localAt A W :=
  Iff.rfl

/-- The **specialization** (center, reduction) of a valuation subring `W ⊇ R` of `F` on a proper
model: the local ring of a chart contained in `W` at the center of `W`. -/
noncomputable def center (hM : M.IsProper) (W : ValuationSubring F) (hW : R ≤ W.toSubring) :
    Subring F :=
  localAt (hM W hW).choose W

/-- The specialization is computed in any chart contained in `W` (for separated models). -/
theorem center_eq (hM : M.IsProper) (hs : M.IsSeparated) {W : ValuationSubring F}
    (hW : R ≤ W.toSubring) {A : Subring F} (hA : A ∈ M.charts) (hAW : A ≤ W.toSubring) :
    M.center hM W hW = localAt A W :=
  hs.localAt_eq (hM W hW).choose_spec.1 hA (hM W hW).choose_spec.2 hAW

theorem center_mem_points (hM : M.IsProper) (W : ValuationSubring F) (hW : R ≤ W.toSubring) :
    M.center hM W hW ∈ M.points :=
  ⟨_, (hM W hW).choose_spec.1, W, (hM W hW).choose_spec.2, rfl⟩

/-- The specialization of `W` is dominated by `W`. -/
theorem center_le (hM : M.IsProper) (W : ValuationSubring F) (hW : R ≤ W.toSubring) :
    M.center hM W hW ≤ W.toSubring :=
  localAt_le (hM W hW).choose_spec.2

/-- The points of a proper separated model are exactly the specializations of the valuation
subrings of `F` containing `R`. -/
theorem mem_points_iff (hM : M.IsProper) (hs : M.IsSeparated) {B : Subring F} :
    B ∈ M.points ↔ ∃ (W : ValuationSubring F) (hW : R ≤ W.toSubring), M.center hM W hW = B := by
  constructor
  · rintro ⟨A, hA, W, hAW, rfl⟩
    exact ⟨W, (M.le_chart A hA).trans hAW, center_eq hM hs _ hA hAW⟩
  · rintro ⟨W, hW, rfl⟩
    exact center_mem_points hM W hW

end ZariskiModel

/-! ### Models over a valuation ring: special fibre and vertex set -/

section Base

variable {K : Type*} [Field K] [Algebra K F]

variable (F) in
/-- The image of the valuation subring `O ⊆ K` in `F`: the base ring of models over `O`. -/
def baseRing (O : ValuationSubring K) : Subring F :=
  O.toSubring.map (algebraMap K F)

lemma algebraMap_mem_baseRing {O : ValuationSubring K} {o : K} (ho : o ∈ O) :
    algebraMap K F o ∈ baseRing F O :=
  ⟨o, ho, rfl⟩

/-- A valuation subring `W` of `F` contains the base ring iff `O ≤ W ∩ K`. -/
lemma baseRing_le_iff {O : ValuationSubring K} {W : ValuationSubring F} :
    baseRing F O ≤ W.toSubring ↔ O ≤ W.comap (algebraMap K F) := by
  constructor
  · intro h o ho
    exact h ⟨o, ho, rfl⟩
  · rintro h _ ⟨o, ho, rfl⟩
    exact h ho

/-- If `W ∩ K = O`, the elements of `𝔪_O` have `W`-valuation `< 1`. -/
lemma valuation_lt_one_of_comap_eq {O : ValuationSubring K} {W : ValuationSubring F}
    (hW : W.comap (algebraMap K F) = O) {o : K} (ho : o ∈ O) (hno : o⁻¹ ∉ O) :
    W.valuation (algebraMap K F o) < 1 := by
  have h₁ : algebraMap K F o ∈ W := by
    rw [← ValuationSubring.mem_comap, hW]
    exact ho
  have h₂ : (algebraMap K F o)⁻¹ ∉ W := by
    rw [← map_inv₀, ← ValuationSubring.mem_comap, hW]
    exact hno
  rw [← W.valuation_le_one_iff] at h₁
  refine lt_of_le_of_ne h₁ fun h ↦ h₂ ?_
  rw [← W.valuation_le_one_iff, map_inv₀, h, inv_one]

/-- If `W ∩ K = O`, the units of `O` are `W`-units. -/
lemma valuation_eq_one_of_comap_eq {O : ValuationSubring K} {W : ValuationSubring F}
    (hW : W.comap (algebraMap K F) = O) {o : K} (ho0 : o ≠ 0) (ho : o ∈ O) (hno : o⁻¹ ∈ O) :
    W.valuation (algebraMap K F o) = 1 := by
  have h₁ : algebraMap K F o ∈ W := by
    rw [← ValuationSubring.mem_comap, hW]
    exact ho
  have h₂ : (algebraMap K F o)⁻¹ ∈ W := by
    rw [← map_inv₀, ← ValuationSubring.mem_comap, hW]
    exact hno
  rw [← W.valuation_le_one_iff] at h₁ h₂
  rw [map_inv₀] at h₂
  exact le_antisymm h₁ (one_le_of_inv_le_one (by simpa using ho0) h₂)

namespace ZariskiModel

variable {O : ValuationSubring K} (M : ZariskiModel (baseRing F O))

/-- The **special fibre**: the points whose maximal ideal contains `𝔪_O`, i.e. in which no
non-unit of `O` becomes invertible. -/
def specialFibre : Set (Subring F) :=
  {B | B ∈ M.points ∧ ∀ o ∈ O, o⁻¹ ∉ O → (algebraMap K F o)⁻¹ ∉ B}

/-- The **vertex set** of the model: the valuation subrings `W` of `F` over `O` (`W ∩ K = O`)
that are points of the model. For normal models these are the local rings at the generic points
of the irreducible components of the special fibre. -/
def vertexSet : Set (ValuationSubring F) :=
  {W | W.comap (algebraMap K F) = O ∧ W.toSubring ∈ M.points}

variable {M}

/-- A vertex lies in the special fibre. -/
theorem toSubring_mem_specialFibre {W : ValuationSubring F} (hW : W ∈ M.vertexSet) :
    W.toSubring ∈ M.specialFibre := by
  refine ⟨hW.2, fun o ho hno h ↦ hno ?_⟩
  have h' : (algebraMap K F o)⁻¹ ∈ W := h
  rw [← map_inv₀, ← ValuationSubring.mem_comap, hW.1] at h'
  exact h'

/-- **Vertices are the valuation subrings over `O` that are their own specialization.** -/
theorem mem_vertexSet_iff (hM : M.IsProper) (hs : M.IsSeparated) {W : ValuationSubring F} :
    W ∈ M.vertexSet ↔ ∃ h : W.comap (algebraMap K F) = O,
      M.center hM W (baseRing_le_iff.2 h.ge) = W.toSubring := by
  constructor
  · rintro ⟨hW, A, hA, W', hAW', hloc⟩
    refine ⟨hW, ?_⟩
    have hAW : A ≤ W.toSubring := hloc ▸ le_localAt
    rw [center_eq hM hs _ hA hAW]
    exact localAt_eq_of_localAt_eq hAW' hloc
  · rintro ⟨hW, h⟩
    exact ⟨hW, h ▸ center_mem_points hM W _⟩

/-- A valuation subring `W` over `O` with `localAt A W = W` for a chart `A ⊆ W` is a vertex. -/
theorem mem_vertexSet_of_localAt_eq {W : ValuationSubring F}
    (hW : W.comap (algebraMap K F) = O) {A : Subring F} (hA : A ∈ M.charts)
    (hAW : A ≤ W.toSubring) (h : localAt A W = W.toSubring) : W ∈ M.vertexSet :=
  ⟨hW, A, hA, W, hAW, h⟩

/-- Conversely, a vertex is the local ring at its own center of every chart it contains (for
separated models). -/
theorem localAt_eq_of_mem_vertexSet (hs : M.IsSeparated) {W : ValuationSubring F}
    (hW : W ∈ M.vertexSet) {A : Subring F} (hA : A ∈ M.charts) (hAW : A ≤ W.toSubring) :
    localAt A W = W.toSubring := by
  obtain ⟨-, B, hB, W', hBW', hloc⟩ := hW
  have hBW : B ≤ W.toSubring := hloc ▸ le_localAt
  rw [hs.localAt_eq hA hB hAW hBW]
  exact localAt_eq_of_localAt_eq hBW' hloc

end ZariskiModel

end Base

end SemistableReduction
