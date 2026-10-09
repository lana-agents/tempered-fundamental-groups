/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeDeformation

/-!
# Recognizing smooth points and ordinary double points from their branches

Blueprint §9.10, L3, R1 and R2 ([KA, Lemmas 1.28 and 1.30] in algebraic form, without
completions). Let `O` be a DVR with uniformizer `ϖ` and `D` a local noetherian integrally closed
domain over `O` (the local ring of a normal model at a closed point of the special fibre). The
**branches** of the special fibre at the closed point are primes `𝔔 ∋ ϖ` such that every prime
containing `ϖ` contains one of them; the special fibre is reduced at `𝔔` if `ϖ` generates `𝔔`
in `D_𝔔`.

* `mem_span_of_forall_mem`: if the special fibre is reduced at its branches, an element lying in
  every branch is divisible by `ϖ` (`(ϖ) = ⋂ 𝔔`: a normal noetherian domain is the intersection
  of its DVR localizations, `KrullDVR`; the special fibre has no embedded points);
* `surjective_of_finite`: (**Nakayama**) a finite `D`-algebra `V` (the normalization of a branch)
  such that every element of `V` is congruent to an element of `D` modulo `t V`, with `t` in the
  maximal ideal, is a quotient of `D`; so a branch whose normalization is a DVR with uniformizer
  `t̄` and residue field that of `D` is itself that DVR (`δ = 0` on the branch);
* **R1** `maximalIdeal_eq_span_of_branch`: one branch, reduced, with normalization `V` as above:
  the maximal ideal of `D` is `(ϖ, t)` (a smooth point of the special fibre, [KA Lemma 1.28]);
* **R2** `isOrdinaryDoublePoint_of_branches`: two branches, reduced, with normalizations
  `V₁, V₂` having uniformizers `ū'`, `v̄'` (`u' v' ∈ (ϖ)`, `u' ∉ 𝔔₁`, `v' ∉ 𝔔₂`): the closed point
  is an ordinary double point with coordinates `u', v'` (`IsOrdinaryDoublePoint`, the input of
  the node lemma S9, [KA Lemma 1.30]).
-/

open IsLocalRing

namespace SemistableReduction

namespace BranchRecognition

section Krull

variable {D : Type*} [CommRing D] [IsDomain D]

/-- A nonzero prime contained in a prime with DVR localization is equal to it. -/
theorem eq_of_le_of_isDiscreteValuationRing {𝔔 𝔮 : Ideal D} [h𝔔 : 𝔔.IsPrime] [𝔮.IsPrime]
    (hle : 𝔔 ≤ 𝔮) (h0 : 𝔔 ≠ ⊥) (hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔮)) :
    𝔔 = 𝔮 := by
  set L := Localization.AtPrime 𝔮
  have hdisj : Disjoint (𝔮.primeCompl : Set D) 𝔔 := by
    rw [Set.disjoint_left]
    intro a ha haQ
    exact ha (hle haQ)
  have hP := IsLocalization.isPrime_of_isPrime_disjoint 𝔮.primeCompl L 𝔔 h𝔔 hdisj
  have hne : 𝔔.map (algebraMap D L) ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    intro hb
    apply ha0
    have : algebraMap D L a = 0 := by
      rw [← Ideal.mem_bot, ← hb]
      exact Ideal.mem_map_of_mem _ ha
    exact IsLocalization.injective L 𝔮.primeCompl_le_nonZeroDivisors (by rw [this, map_zero])
  have hmax : 𝔔.map (algebraMap D L) = maximalIdeal L :=
    IsLocalRing.eq_maximalIdeal (hP.isMaximal hne)
  have := IsLocalization.under_map_of_isPrime_disjoint 𝔮.primeCompl L h𝔔 hdisj
  rw [hmax, Localization.AtPrime.under_maximalIdeal] at this
  exact this.symm

end Krull

section Setting

variable {O : Type*} [CommRing O] {D : Type*} [CommRing D] [IsDomain D] [IsNoetherianRing D]
  [IsIntegrallyClosed D] [Algebra O D]

/-- **The special fibre has no embedded points.** If every prime containing `ϖ` contains one of
the primes `𝔔 ∈ S` (the branches), each containing `ϖ`, and the special fibre is reduced at each
branch, then an element lying in every branch is divisible by `ϖ`. -/
theorem mem_span_of_forall_mem {ϖ : O} (hϖ : algebraMap O D ϖ ≠ 0) {S : Set (Ideal D)}
    (hprime : ∀ 𝔔 ∈ S, 𝔔.IsPrime) (hmem : ∀ 𝔔 ∈ S, algebraMap O D ϖ ∈ 𝔔)
    (hred : ∀ 𝔔 ∈ S, ∀ z ∈ 𝔔, ∃ s ∉ 𝔔, s * z ∈ Ideal.span {algebraMap O D ϖ})
    (hbr : ∀ 𝔮 : Ideal D, 𝔮.IsPrime → algebraMap O D ϖ ∈ 𝔮 → ∃ 𝔔 ∈ S, 𝔔 ≤ 𝔮)
    {z : D} (hz : ∀ 𝔔 ∈ S, z ∈ 𝔔) : z ∈ Ideal.span {algebraMap O D ϖ} := by
  obtain ⟨g, hg⟩ := exists_mul_eq_of_forall_dvr (P := z) hϖ fun 𝔮 h𝔮 hdvr ↦ by
    by_cases hϖ𝔮 : algebraMap O D ϖ ∈ 𝔮
    · right
      obtain ⟨𝔔, h𝔔S, h𝔔𝔮⟩ := hbr 𝔮 h𝔮 hϖ𝔮
      haveI := hprime 𝔔 h𝔔S
      have h0 : 𝔔 ≠ ⊥ := fun h ↦ hϖ (by rw [← Ideal.mem_bot, ← h]; exact hmem 𝔔 h𝔔S)
      obtain rfl := eq_of_le_of_isDiscreteValuationRing h𝔔𝔮 h0 hdvr
      obtain ⟨s, hs, hsz⟩ := hred 𝔔 h𝔔S z (hz 𝔔 h𝔔S)
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hsz
      have hsu : IsUnit (algebraMap D (Localization.AtPrime 𝔔) s) :=
        IsLocalization.map_units _ (⟨s, hs⟩ : 𝔔.primeCompl)
      refine ⟨algebraMap D _ r * ↑hsu.unit⁻¹, ?_⟩
      have := congrArg (algebraMap D (Localization.AtPrime 𝔔)) hr
      rw [map_mul, map_mul] at this
      calc algebraMap D (Localization.AtPrime 𝔔) z
          = algebraMap D _ z * (algebraMap D _ s * ↑hsu.unit⁻¹) := by
            rw [IsUnit.mul_val_inv, mul_one]
        _ = algebraMap D _ (algebraMap O D ϖ) * (algebraMap D _ r * ↑hsu.unit⁻¹) := by
            rw [← mul_assoc, mul_comm (algebraMap D _ z), ← this]
            ring
    · left
      exact ⟨1, by rwa [mul_one]⟩
  exact Ideal.mem_span_singleton'.2 ⟨g, by rw [mul_comm, hg]⟩

end Setting

section Nakayama

variable {D : Type*} [CommRing D] [IsLocalRing D] {V : Type*} [CommRing V] [Algebra D V]

/-- **Nakayama.** A finite `D`-algebra `V` in which every element is congruent modulo `t V` to an
element of `D`, for some `t` in the maximal ideal of `D`, is a quotient of `D`. -/
theorem surjective_of_finite [Module.Finite D V] {t : D} (ht : t ∈ maximalIdeal D)
    (hres : ∀ v : V, ∃ d : D, v - algebraMap D V d ∈ Ideal.span {algebraMap D V t}) :
    Function.Surjective (algebraMap D V) := by
  let N : Submodule D V := LinearMap.range (Algebra.linearMap D V)
  have hle : (⊤ : Submodule D V) ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal D) Module.Finite.fg_top
      (maximalIdeal_le_jacobson _) fun v _ ↦ ?_
    obtain ⟨d, hd⟩ := hres v
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hd
    have hv : v = algebraMap D V d + t • w := by
      rw [Algebra.smul_def, mul_comm, hw]
      ring
    rw [hv]
    exact Submodule.add_mem_sup ⟨d, rfl⟩ (Submodule.smul_mem_smul ht Submodule.mem_top)
  intro v
  obtain ⟨d, hd⟩ := hle (Submodule.mem_top (x := v))
  exact ⟨d, hd⟩

/-- With `V` as in `surjective_of_finite`, an element `z` of `D` whose image in `V` lies in `t V`
is congruent to a multiple of `t` modulo the kernel. -/
theorem exists_sub_mem_ker [Module.Finite D V] {t : D} (ht : t ∈ maximalIdeal D)
    (hres : ∀ v : V, ∃ d : D, v - algebraMap D V d ∈ Ideal.span {algebraMap D V t}) {z : D}
    (hz : algebraMap D V z ∈ Ideal.span {algebraMap D V t}) :
    ∃ d : D, z - t * d ∈ RingHom.ker (algebraMap D V) := by
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hz
  obtain ⟨d, rfl⟩ := surjective_of_finite ht hres w
  refine ⟨d, ?_⟩
  rw [RingHom.mem_ker, map_sub, map_mul, ← hw, mul_comm, sub_self]

end Nakayama

section Recognition

variable {O : Type*} [CommRing O] {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsIntegrallyClosed D] [Algebra O D]

/-- **R1: recognition of smooth points** ([KA, Lemma 1.28], algebraic form). Suppose the special
fibre at the closed point of `D` has a single branch `𝔔` (every prime containing `ϖ` contains
`𝔔`), reduced at `𝔔`, and the branch has a finite normalization `V` (a `D`-algebra with kernel
`𝔔`) in which an element `t` of the maximal ideal of `D` generates the maximal ideal and every
element is congruent modulo `t` to an element of `D` (residue field that of `D`). Then the maximal
ideal of `D` is `(ϖ, t)`: the closed point is a smooth point of the special fibre. -/
theorem maximalIdeal_eq_span_of_branch {ϖ : O} (hϖ : algebraMap O D ϖ ≠ 0) {𝔔 : Ideal D}
    [h𝔔 : 𝔔.IsPrime] (hmem : algebraMap O D ϖ ∈ 𝔔)
    (hred : ∀ z ∈ 𝔔, ∃ s ∉ 𝔔, s * z ∈ Ideal.span {algebraMap O D ϖ})
    (hbr : ∀ 𝔮 : Ideal D, 𝔮.IsPrime → algebraMap O D ϖ ∈ 𝔮 → 𝔔 ≤ 𝔮)
    {V : Type*} [CommRing V] [Algebra D V] [Module.Finite D V]
    (hker : RingHom.ker (algebraMap D V) = 𝔔) {t : D} (ht : t ∈ maximalIdeal D)
    (hres : ∀ v : V, ∃ d : D, v - algebraMap D V d ∈ Ideal.span {algebraMap D V t})
    (hloc : ∀ z ∈ maximalIdeal D, algebraMap D V z ∈ Ideal.span {algebraMap D V t}) :
    maximalIdeal D = Ideal.span {algebraMap O D ϖ, t} := by
  have hspan : 𝔔 ≤ Ideal.span {algebraMap O D ϖ} := fun z hz ↦
    mem_span_of_forall_mem (S := {𝔔}) hϖ (by simpa using h𝔔) (by simpa using hmem)
      (by simpa using hred) (fun 𝔮 h𝔮 hϖ𝔮 ↦ ⟨𝔔, rfl, hbr 𝔮 h𝔮 hϖ𝔮⟩) (by simpa using hz)
  refine le_antisymm (fun z hz ↦ ?_) ?_
  · obtain ⟨d, hd⟩ := exists_sub_mem_ker ht hres (hloc z hz)
    rw [hker] at hd
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hspan hd)
    refine Ideal.mem_span_pair.2 ⟨a, d, ?_⟩
    rw [ha]
    ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact le_maximalIdeal h𝔔.ne_top hmem
    · exact ht

/-- **R2: recognition of ordinary double points** ([KA, Lemma 1.30], algebraic form). Suppose
the special fibre at the closed point of `D` has two branches `𝔔₁, 𝔔₂`, reduced, with finite
normalizations `V₁, V₂` (kernels `𝔔ᵢ`) in which `u'` resp. `v'` generate the maximal ideal and
every element is congruent to an element of `D`, that `u' v' ∈ (ϖ)`, `u' ∉ 𝔔₁`, `v' ∉ 𝔔₂`, and
that the residue field of `D` is that of `O`. Then the closed point is an ordinary double point
with coordinates `u', v'`. -/
theorem isOrdinaryDoublePoint_of_branches [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : algebraMap O D ϖ ≠ 0) {𝔔₁ 𝔔₂ : Ideal D} [h₁ : 𝔔₁.IsPrime] [h₂ : 𝔔₂.IsPrime]
    (hmem₁ : algebraMap O D ϖ ∈ 𝔔₁) (hmem₂ : algebraMap O D ϖ ∈ 𝔔₂)
    (hred₁ : ∀ z ∈ 𝔔₁, ∃ s ∉ 𝔔₁, s * z ∈ Ideal.span {algebraMap O D ϖ})
    (hred₂ : ∀ z ∈ 𝔔₂, ∃ s ∉ 𝔔₂, s * z ∈ Ideal.span {algebraMap O D ϖ})
    (hbr : ∀ 𝔮 : Ideal D, 𝔮.IsPrime → algebraMap O D ϖ ∈ 𝔮 → 𝔔₁ ≤ 𝔮 ∨ 𝔔₂ ≤ 𝔮)
    (hresO : ∀ z : D, ∃ o : O, z - algebraMap O D o ∈ maximalIdeal D)
    {u' v' : D} (huv : u' * v' ∈ Ideal.span {algebraMap O D ϖ}) (hu₁ : u' ∉ 𝔔₁)
    (hv₂ : v' ∉ 𝔔₂)
    {V₁ : Type*} [CommRing V₁] [Algebra D V₁] [Module.Finite D V₁]
    (hker₁ : RingHom.ker (algebraMap D V₁) = 𝔔₁)
    (hres₁ : ∀ v : V₁, ∃ d : D, v - algebraMap D V₁ d ∈ Ideal.span {algebraMap D V₁ u'})
    (hloc₁ : ∀ z ∈ maximalIdeal D, algebraMap D V₁ z ∈ Ideal.span {algebraMap D V₁ u'})
    {V₂ : Type*} [CommRing V₂] [Algebra D V₂] [Module.Finite D V₂]
    (hker₂ : RingHom.ker (algebraMap D V₂) = 𝔔₂)
    (hres₂ : ∀ v : V₂, ∃ d : D, v - algebraMap D V₂ d ∈ Ideal.span {algebraMap D V₂ v'})
    (hloc₂ : ∀ z ∈ maximalIdeal D, algebraMap D V₂ z ∈ Ideal.span {algebraMap D V₂ v'}) :
    IsOrdinaryDoublePoint ϖ u' v' 𝔔₁ 𝔔₂ := by
  have hspan₁ : Ideal.span {algebraMap O D ϖ} ≤ 𝔔₁ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem₁
  have hspan₂ : Ideal.span {algebraMap O D ϖ} ≤ 𝔔₂ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem₂
  have hv₁ : v' ∈ 𝔔₁ := (h₁.mem_or_mem (hspan₁ huv)).resolve_left hu₁
  have hu₂ : u' ∈ 𝔔₂ := (h₂.mem_or_mem (hspan₂ huv)).resolve_right hv₂
  have hm₁ : 𝔔₁ ≤ maximalIdeal D := le_maximalIdeal h₁.ne_top
  have hm₂ : 𝔔₂ ≤ maximalIdeal D := le_maximalIdeal h₂.ne_top
  have hinter : ∀ z, z ∈ 𝔔₁ → z ∈ 𝔔₂ → z ∈ Ideal.span {algebraMap O D ϖ} := by
    intro z hz₁ hz₂
    refine mem_span_of_forall_mem (S := {𝔔₁, 𝔔₂}) hϖ ?_ ?_ ?_ ?_ ?_
    · rintro 𝔔 (rfl | rfl) <;> assumption
    · rintro 𝔔 (rfl | rfl) <;> assumption
    · rintro 𝔔 (rfl | rfl) <;> assumption
    · intro 𝔮 h𝔮 hϖ𝔮
      rcases hbr 𝔮 h𝔮 hϖ𝔮 with h | h
      · exact ⟨𝔔₁, Or.inl rfl, h⟩
      · exact ⟨𝔔₂, Or.inr rfl, h⟩
    · rintro 𝔔 (rfl | rfl) <;> assumption
  refine ⟨le_antisymm (fun z hz ↦ ?_) ?_, hresO, huv, h₁, h₂, hmem₁, hmem₂, hu₁, hv₂, hred₁,
    hred₂, hbr⟩
  · obtain ⟨d₁, hd₁⟩ := exists_sub_mem_ker (hm₂ hu₂) hres₁ (hloc₁ z hz)
    obtain ⟨d₂, hd₂⟩ := exists_sub_mem_ker (hm₁ hv₁) hres₂ (hloc₂ z hz)
    rw [hker₁] at hd₁
    rw [hker₂] at hd₂
    have hz' := hinter (z - u' * d₁ - v' * d₂)
      (by simpa using sub_mem hd₁ (Ideal.mul_mem_right d₂ _ hv₁))
      (by
        have := sub_mem hd₂ (Ideal.mul_mem_right d₁ _ hu₂)
        rwa [show z - v' * d₂ - u' * d₁ = z - u' * d₁ - v' * d₂ by ring] at this)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hz'
    have hz_eq : z = a * algebraMap O D ϖ + d₁ * u' + d₂ * v' := by
      linear_combination -ha
    rw [hz_eq]
    refine add_mem (add_mem ?_ ?_) ?_ <;> refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_) <;>
      simp
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hm₁ hmem₁
    · exact hm₂ hu₂
    · exact hm₁ hv₁

end Recognition

end BranchRecognition

end SemistableReduction
