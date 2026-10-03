/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KrullDVR
import TemperedFundamentalGroups.SemistableReduction.Node

/-!
# Ordinary double points over a DVR are nodes (W7, S9, the deformation step)

Blueprint §9.9, S9. Let `O` be a discrete valuation ring with uniformizer `ϖ` and `D` a local
noetherian normal domain over `O` whose maximal ideal is `(ϖ, u', v')`, with residue field that
of `O` and `u' v' ∈ (ϖ)` (the special fibre is an ordinary double point with coordinates
`ū', v̄'`). Then the node coordinates can be corrected to an honest node:

* **Newton iteration** (`exists_newton`): since `D = O + (ϖ, u, v)`, writing the error
  `u v - c = ϖ ^ k g` as `g = λ + ϖ γ + u α + v β` and replacing `u, v` by `u - ϖ ^ k β`,
  `v - ϖ ^ k α` improves the error to `ϖ ^ (k + 1)`; after finitely many steps
  `u v = c + ϖ ^ (K + 1) g` with `c ∈ O`.
* **Termination** (`NodeDeformation`): the base coordinate `x` (`x y = c₀ = ϖ ^ N · unit`,
  `x ≡ η u'^d` on the outer branch) bounds the valuation of `c` by `N`, by a Krull-divisor
  argument (`mem_of_forall_isDiscreteValuationRing`) and the order on the outer branch; then
  `u v = ϖ ^ n · unit` exactly, `N = d n`, and `x = ε u ^ d`, `y = ε' v ^ d` with units `ε, ε'`.
-/

open IsLocalRing

namespace SemistableReduction

section Newton

variable {O D : Type*} [CommRing O] [CommRing D] [Algebra O D] [IsLocalRing D]

/-- **One Newton step.** -/
theorem exists_newton_step (ϖ : O)
    (hres : ∀ z : D, ∃ o : O, z - algebraMap O D o ∈ maximalIdeal D) {u v : D}
    (hm : maximalIdeal D = Ideal.span {algebraMap O D ϖ, u, v}) {k : ℕ} (hk : 1 ≤ k) {c : O}
    {g : D} (h : u * v = algebraMap O D c + algebraMap O D ϖ ^ k * g) :
    ∃ (u₁ v₁ : D) (c₁ : O) (g₁ : D),
      u₁ - u ∈ Ideal.span {algebraMap O D ϖ ^ k} ∧ v₁ - v ∈ Ideal.span {algebraMap O D ϖ ^ k} ∧
      c₁ - c ∈ Ideal.span {ϖ ^ k} ∧
      u₁ * v₁ = algebraMap O D c₁ + algebraMap O D ϖ ^ (k + 1) * g₁ := by
  obtain ⟨l, hl⟩ := hres g
  rw [hm] at hl
  obtain ⟨γ, hγ⟩ : ∃ γ α β : D, g - algebraMap O D l = γ * algebraMap O D ϖ + α * u + β * v := by
    obtain ⟨γ, z, hz, e⟩ := Ideal.mem_span_insert.mp hl
    obtain ⟨α, w, hw, e'⟩ := Ideal.mem_span_insert.mp hz
    obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    exact ⟨γ, α, β, by rw [e, e']; ring⟩
  obtain ⟨α, β, hαβ⟩ := hγ
  set p := algebraMap O D ϖ
  refine ⟨u - p ^ k * β, v - p ^ k * α, c + ϖ ^ k * l, γ + p ^ (k - 1) * α * β, ?_, ?_, ?_, ?_⟩
  · exact Ideal.mem_span_singleton'.mpr ⟨-β, by ring⟩
  · exact Ideal.mem_span_singleton'.mpr ⟨-α, by ring⟩
  · exact Ideal.mem_span_singleton'.mpr ⟨l, by ring⟩
  · have hg : g = algebraMap O D l + γ * p + α * u + β * v := by
      linear_combination hαβ
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [map_add, map_mul, map_pow]
    linear_combination h + p ^ (j + 1) * hg

/-- **Newton iteration**: starting from `u' v' ∈ (ϖ)`, after `K` steps
`u v = c + ϖ ^ (K + 1) g` with `u ≡ u'`, `v ≡ v'` modulo `ϖ`. -/
theorem exists_newton (ϖ : O)
    (hres : ∀ z : D, ∃ o : O, z - algebraMap O D o ∈ maximalIdeal D) {u' v' : D}
    (hm : maximalIdeal D = Ideal.span {algebraMap O D ϖ, u', v'})
    (h₀ : u' * v' ∈ Ideal.span {algebraMap O D ϖ}) (K : ℕ) :
    ∃ (u v : D) (c : O) (g : D),
      u - u' ∈ Ideal.span {algebraMap O D ϖ} ∧ v - v' ∈ Ideal.span {algebraMap O D ϖ} ∧
      u * v = algebraMap O D c + algebraMap O D ϖ ^ (K + 1) * g := by
  induction K with
  | zero =>
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h₀
    exact ⟨u', v', 0, g, by simp, by simp, by rw [map_zero, zero_add, pow_one, ← hg, mul_comm]⟩
  | succ K ih =>
    obtain ⟨u, v, c, g, hu, hv, h⟩ := ih
    have hm' : maximalIdeal D = Ideal.span {algebraMap O D ϖ, u, v} := by
      rw [hm]
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hv
      have eu : u = u' + a * algebraMap O D ϖ := by rw [ha]; ring
      have ev : v = v' + b * algebraMap O D ϖ := by rw [hb]; ring
      have hp : algebraMap O D ϖ ∈ Ideal.span {algebraMap O D ϖ, u, v} :=
        Ideal.subset_span (by simp)
      have hu0 : u ∈ Ideal.span {algebraMap O D ϖ, u, v} := Ideal.subset_span (by simp)
      have hv0 : v ∈ Ideal.span {algebraMap O D ϖ, u, v} := Ideal.subset_span (by simp)
      have hp' : algebraMap O D ϖ ∈ Ideal.span {algebraMap O D ϖ, u', v'} :=
        Ideal.subset_span (by simp)
      have hu0' : u' ∈ Ideal.span {algebraMap O D ϖ, u', v'} := Ideal.subset_span (by simp)
      have hv0' : v' ∈ Ideal.span {algebraMap O D ϖ, u', v'} := Ideal.subset_span (by simp)
      apply le_antisymm <;> rw [Ideal.span_le] <;> intro z hz <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      · rcases hz with hz | hz | hz <;> rw [hz]
        · exact hp
        · rw [show u' = u - a * algebraMap O D ϖ by rw [eu]; ring]
          exact sub_mem hu0 (Ideal.mul_mem_left _ _ hp)
        · rw [show v' = v - b * algebraMap O D ϖ by rw [ev]; ring]
          exact sub_mem hv0 (Ideal.mul_mem_left _ _ hp)
      · rcases hz with hz | hz | hz <;> rw [hz]
        · exact hp'
        · rw [eu]; exact add_mem hu0' (Ideal.mul_mem_left _ _ hp')
        · rw [ev]; exact add_mem hv0' (Ideal.mul_mem_left _ _ hp')
    obtain ⟨u₁, v₁, c₁, g₁, hu₁, hv₁, -, h₁⟩ :=
      exists_newton_step ϖ hres hm' (k := K + 1) (by omega) h
    have hpow : Ideal.span {algebraMap O D ϖ ^ (K + 1)} ≤ Ideal.span {algebraMap O D ϖ} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact dvd_pow_self _ (by omega)
    refine ⟨u₁, v₁, c₁, g₁, ?_, ?_, h₁⟩
    · have := add_mem (hpow hu₁) hu
      rwa [sub_add_sub_cancel] at this
    · have := add_mem (hpow hv₁) hv
      rwa [sub_add_sub_cancel] at this

end Newton

section DVRFacts

variable {D : Type*} [CommRing D] [IsDomain D]

/-- Divisibility in a localization `D_𝔔` gives membership of the quotient in `D_𝔔`. -/
theorem exists_mul_eq_of_dvd_localization {𝔔 : Ideal D} [𝔔.IsPrime] {P Q : D}
    (h : algebraMap D (Localization.AtPrime 𝔔) Q ∣ algebraMap D (Localization.AtPrime 𝔔) P) :
    ∃ a : D, ∃ s ∉ 𝔔, s * P = Q * a := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj 𝔔.primeCompl r
  refine ⟨a, s, s.2, IsLocalization.injective (Localization.AtPrime 𝔔)
    𝔔.primeCompl_le_nonZeroDivisors ?_⟩
  simp only at has
  rw [map_mul, map_mul, ← has, hr]
  ring

variable [IsNoetherianRing D] [IsIntegrallyClosed D]

/-- **Krull criterion for quotients**: `Q ∣ P` in `D` as soon as, at every prime `𝔔` with
`D_𝔔` a DVR, either some multiple `Q Q'` lies outside `𝔔` or `Q ∣ P` in `D_𝔔`. -/
theorem exists_mul_eq_of_forall_dvr {P Q : D} (hQ : Q ≠ 0)
    (h : ∀ 𝔔 : Ideal D, ∀ _ : 𝔔.IsPrime, IsDiscreteValuationRing (Localization.AtPrime 𝔔) →
      (∃ Q', Q * Q' ∉ 𝔔) ∨
        algebraMap D (Localization.AtPrime 𝔔) Q ∣ algebraMap D (Localization.AtPrime 𝔔) P) :
    ∃ g : D, Q * g = P := by
  let F := FractionRing D
  have hQF : algebraMap D F Q ≠ 0 := by simpa using hQ
  obtain ⟨g, hg⟩ := mem_of_forall_isDiscreteValuationRing (D := D) (F := F)
    (algebraMap D F P / algebraMap D F Q) fun 𝔔 h𝔔 hdvr ↦ by
      rcases h 𝔔 h𝔔 hdvr with ⟨Q', hQ'⟩ | hdvd
      · refine ⟨P * Q', Q * Q', hQ', ?_⟩
        rw [map_mul, map_mul, mul_div_assoc', div_eq_iff hQF]
        ring
      · obtain ⟨a, s, hs, e⟩ := exists_mul_eq_of_dvd_localization hdvd
        refine ⟨a, s, hs, ?_⟩
        rw [mul_div_assoc', div_eq_iff hQF, ← map_mul, ← map_mul, e, mul_comm]
  refine ⟨g, IsFractionRing.injective D F ?_⟩
  rw [map_mul, hg, mul_div_cancel₀ _ hQF]

end DVRFacts

section Helpers

variable {R : Type*} [CommRing R]

/-- Changing two of three generators modulo the first and by units does not change the ideal. -/
theorem span_triple_eq {p a b a' b' : R} (ha : a - a' ∈ Ideal.span {p})
    (hb : b - b' ∈ Ideal.span {p}) :
    Ideal.span {p, a, b} = Ideal.span {p, a', b'} := by
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.mp hb
  have key : ∀ {a b a' b' : R} (α β : R), α * p = a - a' → β * p = b - b' →
      Ideal.span {p, a, b} ≤ Ideal.span {p, a', b'} := by
    intro a b a' b' α β hα hβ
    have hp : p ∈ Ideal.span {p, a', b'} := Ideal.subset_span (by simp)
    have ha' : a' ∈ Ideal.span {p, a', b'} := Ideal.subset_span (by simp)
    have hb' : b' ∈ Ideal.span {p, a', b'} := Ideal.subset_span (by simp)
    rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz <;> rw [hz]
    · exact hp
    · rw [show a = a' + α * p by rw [hα]; ring]
      exact add_mem ha' (Ideal.mul_mem_left _ _ hp)
    · rw [show b = b' + β * p by rw [hβ]; ring]
      exact add_mem hb' (Ideal.mul_mem_left _ _ hp)
  exact le_antisymm (key α β hα hβ) (key (-α) (-β) (by rw [← neg_sub, ← hα]; ring)
    (by rw [← neg_sub, ← hβ]; ring))

/-- Multiplying a generator by a unit does not change the ideal. -/
theorem span_triple_mul_unit (p a b : R) (e : Rˣ) :
    Ideal.span {p, a, b * e} = Ideal.span {p, a, b} := by
  have hb : b * e ∈ Ideal.span {p, a, b} :=
    Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  have hb' : b ∈ Ideal.span {p, a, b * e} := by
    have : b * e * ↑e⁻¹ ∈ Ideal.span {p, a, b * e} :=
      Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    rwa [mul_assoc, Units.mul_inv, mul_one] at this
  apply le_antisymm <;> rw [Ideal.span_le] <;> intro z hz <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz <;>
    rcases hz with hz | hz | hz <;> rw [hz]
  all_goals first
    | exact hb | exact hb'
    | exact Ideal.subset_span (by simp)

/-- Divisibility of powers of `unit * ϖ ^ i`. -/
theorem dvd_of_eq_unit_mul_pow {A B ϖ : R} {α β : Rˣ} {i j k l : ℕ} (hA : A = α * ϖ ^ i)
    (hB : B = β * ϖ ^ j) (h : k * i ≤ l * j) : A ^ k ∣ B ^ l := by
  rw [hA, hB, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show i * k ≤ j * l by rwa [mul_comm j l, mul_comm i k])
  refine ⟨↑(α ^ k)⁻¹ * ↑(β ^ l) * ϖ ^ m, ?_⟩
  rw [hm, pow_add]
  simp only [Units.val_pow_eq_pow_val]
  have : (↑α : R) ^ k * ↑(α ^ k)⁻¹ = 1 := by
    rw [← Units.val_pow_eq_pow_val, Units.mul_inv]
  linear_combination (-(↑β ^ l * ϖ ^ (i * k) * ϖ ^ m)) * this

end Helpers

section Deformation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
  [IsIntegrallyClosed D] [Algebra O D]

/-- **An ordinary double point over `O`** at the closed point of `D`, with coordinates `u', v'`
and branches `𝔔₁` (outer, `u'` a unit) and `𝔔₂` (inner, `v'` a unit): the maximal ideal is
`(ϖ, u', v')`, the residue field is that of `O`, `u' v' ∈ (ϖ)`, the special fibre is reduced at
both branches (`e = 1`), and every prime containing `ϖ` contains one of the branches. -/
structure IsOrdinaryDoublePoint (ϖ : O) (u' v' : D) (𝔔₁ 𝔔₂ : Ideal D) : Prop where
  maximalIdeal_eq : maximalIdeal D = Ideal.span {algebraMap O D ϖ, u', v'}
  residue : ∀ z : D, ∃ o : O, z - algebraMap O D o ∈ maximalIdeal D
  mul_mem : u' * v' ∈ Ideal.span {algebraMap O D ϖ}
  isPrime₁ : 𝔔₁.IsPrime
  isPrime₂ : 𝔔₂.IsPrime
  mem₁ : algebraMap O D ϖ ∈ 𝔔₁
  mem₂ : algebraMap O D ϖ ∈ 𝔔₂
  notMem₁ : u' ∉ 𝔔₁
  notMem₂ : v' ∉ 𝔔₂
  reduced₁ : ∀ z ∈ 𝔔₁, ∃ s ∉ 𝔔₁, s * z ∈ Ideal.span {algebraMap O D ϖ}
  reduced₂ : ∀ z ∈ 𝔔₂, ∃ s ∉ 𝔔₂, s * z ∈ Ideal.span {algebraMap O D ϖ}
  branches : ∀ 𝔔 : Ideal D, 𝔔.IsPrime → algebraMap O D ϖ ∈ 𝔔 → 𝔔₁ ≤ 𝔔 ∨ 𝔔₂ ≤ 𝔔

omit [IsDomain O] [IsDiscreteValuationRing O] [IsLocalRing D] [IsIntegrallyClosed D] in
/-- A branch with `e = 1` is a DVR with uniformizer `ϖ`. -/
theorem isDiscreteValuationRing_of_reduced {ϖ : O} (hϖ0 : algebraMap O D ϖ ≠ 0) {𝔔 : Ideal D}
    [𝔔.IsPrime] (hmem : algebraMap O D ϖ ∈ 𝔔)
    (hred : ∀ z ∈ 𝔔, ∃ s ∉ 𝔔, s * z ∈ Ideal.span {algebraMap O D ϖ}) :
    IsDiscreteValuationRing (Localization.AtPrime 𝔔) ∧
      maximalIdeal (Localization.AtPrime 𝔔) =
        Ideal.span {algebraMap O (Localization.AtPrime 𝔔) ϖ} := by
  let L := Localization.AtPrime 𝔔
  have hinj : Function.Injective (algebraMap D L) :=
    IsLocalization.injective L 𝔔.primeCompl_le_nonZeroDivisors
  have hp : algebraMap O L ϖ = algebraMap D L (algebraMap O D ϖ) :=
    IsScalarTower.algebraMap_apply O D L ϖ
  have hmax : maximalIdeal L = Ideal.span {algebraMap O L ϖ} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj 𝔔.primeCompl z
      simp only at hat
      have ha : a ∈ 𝔔 := by
        by_contra hc
        have : algebraMap D L a ∈ maximalIdeal L := by
          rw [← hat]; exact Ideal.mul_mem_right _ _ hz
        exact this (IsLocalization.map_units L (⟨a, hc⟩ : 𝔔.primeCompl))
      obtain ⟨s, hs, hsa⟩ := hred a ha
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hsa
      have hu : IsUnit (algebraMap D L (s * t)) :=
        IsLocalization.map_units L (⟨s * t, 𝔔.primeCompl.mul_mem hs t.2⟩ : 𝔔.primeCompl)
      have e : algebraMap D L w * algebraMap D L (algebraMap O D ϖ) =
          algebraMap D L (s * t) * z := by
        rw [← map_mul, hw, map_mul, map_mul, ← hat]; ring
      refine Ideal.mem_span_singleton'.mpr ⟨algebraMap D L w * ↑hu.unit⁻¹, ?_⟩
      rw [hp]
      calc algebraMap D L w * ↑hu.unit⁻¹ * algebraMap D L (algebraMap O D ϖ)
          = ↑hu.unit⁻¹ * (algebraMap D L w * algebraMap D L (algebraMap O D ϖ)) := by ring
        _ = ↑hu.unit⁻¹ * (algebraMap D L (s * t) * z) := by rw [e]
        _ = z := by rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff, hp]
      by_contra hc
      have hu : IsUnit (algebraMap D L (algebraMap O D ϖ)) := by
        simpa [mem_maximalIdeal, mem_nonunits_iff] using hc
      have := (IsLocalization.AtPrime.isUnit_to_map_iff L 𝔔 _).mp hu
      exact this hmem
  have hϖL : algebraMap O L ϖ ≠ 0 := by
    rw [hp]; exact fun h ↦ hϖ0 (hinj (by rw [h, map_zero]))
  have hnf : ¬ IsField L := fun hF ↦ by
    have := (isField_iff_maximalIdeal_eq).mp hF
    rw [this] at hmax
    exact hϖL (Ideal.span_singleton_eq_bot.mp hmax.symm)
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing 𝔔.primeCompl L inferInstance
  have hpr : (maximalIdeal L).IsPrincipal := ⟨⟨_, hmax⟩⟩
  exact ⟨((IsDiscreteValuationRing.TFAE L hnf).out 0 4).mpr hpr, hmax⟩

variable {ϖ : O} {u' v' : D} {𝔔₁ 𝔔₂ : Ideal D}

namespace IsOrdinaryDoublePoint

omit [IsDomain O] [IsDiscreteValuationRing O] [IsDomain D] [IsNoetherianRing D]
  [IsIntegrallyClosed D] in
lemma mem₁_v (H : IsOrdinaryDoublePoint ϖ u' v' 𝔔₁ 𝔔₂) : v' ∈ 𝔔₁ := by
  haveI := H.isPrime₁
  have : u' * v' ∈ 𝔔₁ := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp H.mul_mem
    rw [← ha]; exact Ideal.mul_mem_left _ _ H.mem₁
  exact (‹𝔔₁.IsPrime›.mem_or_mem this).resolve_left H.notMem₁

omit [IsDomain O] [IsDiscreteValuationRing O] [IsDomain D] [IsNoetherianRing D]
  [IsIntegrallyClosed D] in
lemma mem₂_u (H : IsOrdinaryDoublePoint ϖ u' v' 𝔔₁ 𝔔₂) : u' ∈ 𝔔₂ := by
  haveI := H.isPrime₂
  have : u' * v' ∈ 𝔔₂ := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp H.mul_mem
    rw [← ha]; exact Ideal.mul_mem_left _ _ H.mem₂
  exact (‹𝔔₂.IsPrime›.mem_or_mem this).resolve_right H.notMem₂

omit [IsDomain O] [IsDiscreteValuationRing O] [IsIntegrallyClosed D] [IsDomain D] in
/-- **The outer branch** `D ⧸ 𝔔₁` is a DVR with uniformizer `ū'`. -/
theorem isDiscreteValuationRing_quotient [𝔔₁.IsPrime] (H : IsOrdinaryDoublePoint ϖ u' v' 𝔔₁ 𝔔₂) :
    IsDiscreteValuationRing (D ⧸ 𝔔₁) ∧ Irreducible (Ideal.Quotient.mk 𝔔₁ u') := by
  let π := Ideal.Quotient.mk 𝔔₁
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (D ⧸ 𝔔₁) := IsLocalRing.of_surjective' π hsurj
  have hnu : ∀ z : D, IsUnit (π z) → IsUnit z := by
    intro z hz
    by_contra hc
    obtain ⟨w, hw⟩ := hsurj (hz.unit⁻¹ : (D ⧸ 𝔔₁)ˣ)
    have h1 : z * w - 1 ∈ 𝔔₁ := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one]
      change π z * π w - 1 = 0
      rw [hw, IsUnit.mul_val_inv, sub_self]
    have hmax : z * w ∈ maximalIdeal D :=
      Ideal.mul_mem_right _ _ ((mem_maximalIdeal z).mpr hc)
    have : (1 : D) ∈ maximalIdeal D := by
      have := sub_mem hmax (le_maximalIdeal H.isPrime₁.ne_top h1)
      rwa [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal D).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hmax : maximalIdeal (D ⧸ 𝔔₁) = Ideal.span {π u'} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨z, rfl⟩ := hsurj z
      have hz' : z ∈ maximalIdeal D := fun hu ↦ hz ((hu.map π))
      rw [H.maximalIdeal_eq] at hz'
      obtain ⟨a, w, hw, e⟩ := Ideal.mem_span_insert.mp hz'
      obtain ⟨b, w', hw', e'⟩ := Ideal.mem_span_insert.mp hw
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw'
      refine Ideal.mem_span_singleton'.mpr ⟨π b, ?_⟩
      rw [e, e', map_add, map_add, map_mul, map_mul, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr H.mem₁, Ideal.Quotient.eq_zero_iff_mem.mpr H.mem₁_v]
      ring
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      intro hu
      have := hnu u' hu
      have hm : u' ∈ maximalIdeal D := by
        rw [H.maximalIdeal_eq]; exact Ideal.subset_span (by simp)
      exact hm this
  have hne : π u' ≠ 0 := fun h ↦ H.notMem₁ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnf : ¬ IsField (D ⧸ 𝔔₁) := fun hF ↦ by
    have := (isField_iff_maximalIdeal_eq).mp hF
    rw [this] at hmax
    exact hne (Ideal.span_singleton_eq_bot.mp hmax.symm)
  have hpr : (maximalIdeal (D ⧸ 𝔔₁)).IsPrincipal := ⟨⟨_, hmax⟩⟩
  exact ⟨((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).mpr hpr,
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hmax⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [IsNoetherianRing D] [IsIntegrallyClosed D] in
/-- **The only DVR primes containing `ϖ` are the two branches.** -/
theorem eq_or_eq_of_isDiscreteValuationRing (H : IsOrdinaryDoublePoint ϖ u' v' 𝔔₁ 𝔔₂)
    (hϖ0 : algebraMap O D ϖ ≠ 0) {𝔔 : Ideal D} [𝔔.IsPrime]
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔔)) (hmem : algebraMap O D ϖ ∈ 𝔔) :
    𝔔 = 𝔔₁ ∨ 𝔔 = 𝔔₂ := by
  let L := Localization.AtPrime 𝔔
  have hinj : Function.Injective (algebraMap D L) :=
    IsLocalization.injective L 𝔔.primeCompl_le_nonZeroDivisors
  have key : ∀ P : Ideal D, P.IsPrime → algebraMap O D ϖ ∈ P → P ≤ 𝔔 → P = 𝔔 := by
    intro P hP hPϖ hle
    have hdisj : Disjoint (𝔔.primeCompl : Set D) P := by
      rw [Set.disjoint_left]; intro z hz hzP; exact hz (hle hzP)
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint 𝔔.primeCompl L P hP hdisj
    have hne : P.map (algebraMap D L) ≠ ⊥ := by
      intro h
      have : algebraMap D L (algebraMap O D ϖ) ∈ P.map (algebraMap D L) :=
        Ideal.mem_map_of_mem _ hPϖ
      rw [h, Ideal.mem_bot] at this
      exact hϖ0 (hinj (by rw [this, map_zero]))
    have hmaxP := hprime.isMaximal hne
    have heq : P.map (algebraMap D L) = maximalIdeal L := IsLocalRing.eq_maximalIdeal hmaxP
    have h1 := IsLocalization.under_map_of_isPrime_disjoint 𝔔.primeCompl L hP hdisj
    rw [heq, Localization.AtPrime.under_maximalIdeal] at h1
    exact h1.symm
  rcases H.branches 𝔔 inferInstance hmem with h | h
  · exact Or.inl (key 𝔔₁ H.isPrime₁ H.mem₁ h).symm
  · exact Or.inr (key 𝔔₂ H.isPrime₂ H.mem₂ h).symm

/-- **Ordinary double points over a DVR are nodes.** If the closed point of `D` is an ordinary
double point (`IsOrdinaryDoublePoint`) over which the base node coordinates `x, y`
(`x y = c₀ ≠ 0`) satisfy `x ≡ η u'^d` on the outer branch and `y ∉ 𝔔₂`, then there are node
coordinates `u ≡ u'`, `v` with `u v = ϖ ^ n` exactly, `𝔪 = (ϖ, u, v)`, and `x = ε u ^ d`,
`y = ε' v ^ d` with units `ε, ε'`. -/
theorem exists_node (H : IsOrdinaryDoublePoint ϖ u' v' 𝔔₁ 𝔔₂) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap O D ϖ ≠ 0) {x y : D} {c₀ : O} (hc₀ : c₀ ≠ 0)
    (hxy : x * y = algebraMap O D c₀) {d : ℕ} (hd : 1 ≤ d) {s η : D}
    (hs : s ∉ maximalIdeal D) (hη : η ∉ maximalIdeal D)
    (hx : s * x - η * u' ^ d ∈ Ideal.span {algebraMap O D ϖ, v'}) (hy : y ∉ 𝔔₂) :
    ∃ (n : ℕ) (u v : D), 1 ≤ n ∧ u * v = algebraMap O D ϖ ^ n ∧
      maximalIdeal D = Ideal.span {algebraMap O D ϖ, u, v} ∧ u ∉ 𝔔₁ ∧ v ∉ 𝔔₂ ∧
      u - u' ∈ Ideal.span {algebraMap O D ϖ} ∧
      (∃ ε : Dˣ, x = ε * u ^ d) ∧ (∃ ε' : Dˣ, y = ε' * v ^ d) := by
  haveI := H.isPrime₁
  haveI := H.isPrime₂
  set p := algebraMap O D ϖ with hp_def
  obtain ⟨N, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc₀ hϖ
  have hpmax : p ∈ maximalIdeal D := by
    rw [H.maximalIdeal_eq]; exact Ideal.subset_span (Set.mem_insert _ _)
  have hu'max : u' ∈ maximalIdeal D := by
    rw [H.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hwD : IsUnit (algebraMap O D w) := w.isUnit.map _
  have hc₀D : algebraMap O D c₀ = algebraMap O D w * p ^ N := by
    rw [hw, map_mul, map_pow]
  -- branch 2
  obtain ⟨hR₂, hmax₂⟩ := isDiscreteValuationRing_of_reduced hϖ0 H.mem₂ H.reduced₂
  let L₂ := Localization.AtPrime 𝔔₂
  let ι₂ := algebraMap D L₂
  have hinj₂ : Function.Injective ι₂ :=
    IsLocalization.injective L₂ 𝔔₂.primeCompl_le_nonZeroDivisors
  have hp₂ : algebraMap O L₂ ϖ = ι₂ p := IsScalarTower.algebraMap_apply O D L₂ ϖ
  have hϖ₂ne : ι₂ p ≠ 0 := fun h ↦ hϖ0 (hinj₂ (by rw [h, map_zero]))
  have hϖ₂ : Irreducible (ι₂ p) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hϖ₂ne (hp₂ ▸ hmax₂)
  have hunit₂ : ∀ z ∉ 𝔔₂, IsUnit (ι₂ z) := fun z hz ↦
    IsLocalization.map_units L₂ (⟨z, hz⟩ : 𝔔₂.primeCompl)
  -- `ι₂ x = unit * ϖ ^ N`
  have hx₂ : ∃ ν : L₂ˣ, ι₂ x = ν * ι₂ p ^ N := by
    obtain ⟨hyu⟩ := hunit₂ y hy
    refine ⟨(hwD.map ι₂).unit * (hunit₂ y hy).unit⁻¹, ?_⟩
    have : ι₂ x * ι₂ y = ι₂ (algebraMap O D w) * ι₂ p ^ N := by
      rw [← map_mul, hxy, hc₀D, map_mul, map_pow]
    simp only [Units.val_mul, IsUnit.unit_spec]
    calc ι₂ x = ι₂ x * ι₂ y * ↑(hunit₂ y hy).unit⁻¹ := by
          rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
      _ = _ := by rw [this]; ring
  -- outer branch
  obtain ⟨hR', hu'irr⟩ := H.isDiscreteValuationRing_quotient
  let π := Ideal.Quotient.mk 𝔔₁
  have hunitπ : ∀ z ∉ maximalIdeal D, IsUnit (π z) := fun z hz ↦
    ((mem_maximalIdeal z).not.mp hz |> not_not.mp).map π
  have hπx : ∃ e : (D ⧸ 𝔔₁)ˣ, π x = e * π u' ^ d := by
    refine ⟨(hunitπ s hs).unit⁻¹ * (hunitπ η hη).unit, ?_⟩
    have h1 : s * x - η * u' ^ d ∈ 𝔔₁ := by
      refine (Ideal.span_le.mpr ?_) hx
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact H.mem₁
      · exact H.mem₁_v
    have h2 : π s * π x = π η * π u' ^ d := by
      rw [← map_mul, ← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h1
    simp only [Units.val_mul, IsUnit.unit_spec]
    calc π x = ↑(hunitπ s hs).unit⁻¹ * (π s * π x) := by
          rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = _ := by rw [h2]; ring
  obtain ⟨e, he⟩ := hπx
  have hπu' : π u' ≠ 0 := hu'irr.ne_zero
  have hx₁ : x ∉ 𝔔₁ := fun h ↦ by
    have : π x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [he] at this
    exact pow_ne_zero d hπu' ((Units.mul_right_eq_zero e).mp this)
  have hx0 : x ≠ 0 := fun h ↦ hx₁ (h ▸ zero_mem _)
  -- generic primes: `ϖ ∉ 𝔔` makes `p` a non-member
  have hgen : ∀ 𝔔 : Ideal D, 𝔔.IsPrime → p ∉ 𝔔 → ∀ m : ℕ, ∀ z : D, IsUnit z →
      z * p ^ m ∉ 𝔔 := by
    intro 𝔔 h𝔔 hp𝔔 m z hz hmem
    rcases h𝔔.mem_or_mem hmem with h | h
    · exact h𝔔.ne_top (Ideal.eq_top_of_isUnit_mem _ h hz)
    · exact hp𝔔 (h𝔔.mem_of_pow_mem _ h)
  -- order on the outer branch
  have hord : ∀ {i j : ℕ}, (π u') ^ i ∣ (π u') ^ j → i ≤ j := fun h ↦
    (pow_dvd_pow_iff hπu' hu'irr.not_isUnit).mp h
  -- Newton
  obtain ⟨u, v, c, g, hu, hv, huv⟩ := exists_newton ϖ H.residue H.maximalIdeal_eq H.mul_mem N
  have hπu : π u = π u' := by
    rw [← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.span_singleton_le_iff_mem _).mpr H.mem₁ hu)
  have hu₁ : u ∉ 𝔔₁ := fun h ↦ hπu' (by rw [← hπu]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hv₂ : v ∉ 𝔔₂ := fun h ↦ by
    have := sub_mem h ((Ideal.span_singleton_le_iff_mem _).mpr H.mem₂ hv)
    rw [sub_sub_cancel] at this
    exact H.notMem₂ this
  have hu0 : u ≠ 0 := fun h ↦ hu₁ (h ▸ zero_mem _)
  have humax : u ∈ maximalIdeal D := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu
    rw [show u = u' + a * p by rw [ha]; ring]
    exact add_mem hu'max (Ideal.mul_mem_left _ _ hpmax)
  -- the constant term has valuation `≤ N`
  have hc : c ∉ Ideal.span {ϖ ^ (N + 1)} := by
    intro hcm
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hcm
    have hu₂0 : ι₂ u ≠ 0 := fun h ↦ hu0 (hinj₂ (by rw [h, map_zero]))
    obtain ⟨a, μ, hμ⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hu₂0 hϖ₂
    have ha : N + 1 ≤ a := by
      have huv' : u * v = p ^ (N + 1) * (algebraMap O D c' + g) := by
        rw [huv, map_mul, map_pow]; ring
      have h1 : ι₂ p ^ (N + 1) ∣ ι₂ u * ι₂ v := by
        rw [← map_mul, huv', map_mul, map_pow]
        exact dvd_mul_right _ _
      rw [hμ, mul_assoc, mul_comm (ι₂ p ^ a), ← mul_assoc] at h1
      have h2 : ι₂ p ^ (N + 1) ∣ ι₂ p ^ a :=
        (Units.dvd_mul_left (u := μ * (hunit₂ v hv₂).unit)).mp (by
          simpa only [Units.val_mul, IsUnit.unit_spec] using h1)
      exact (pow_dvd_pow_iff hϖ₂ne hϖ₂.not_isUnit).mp h2
    obtain ⟨ν, hν⟩ := hx₂
    obtain ⟨g₀, hg₀⟩ := exists_mul_eq_of_forall_dvr (P := u ^ N) (Q := x ^ a)
      (pow_ne_zero _ hx0) fun 𝔔 h𝔔 hdvr ↦ by
        by_cases hp𝔔 : p ∈ 𝔔
        · rcases H.eq_or_eq_of_isDiscreteValuationRing hϖ0 hdvr hp𝔔 with h | h <;> subst 𝔔
          · exact Or.inl ⟨1, by rw [mul_one]; exact fun h ↦ hx₁ (H.isPrime₁.mem_of_pow_mem _ h)⟩
          · right
            rw [map_pow, map_pow]
            exact dvd_of_eq_unit_mul_pow hν hμ (by rw [mul_comm])
        · left
          refine ⟨y ^ a, ?_⟩
          rw [← mul_pow, hxy, hc₀D, mul_pow, ← pow_mul]
          exact hgen 𝔔 h𝔔 hp𝔔 _ _ (hwD.pow a)
    have := congrArg π hg₀
    rw [map_mul, map_pow, map_pow, he, hπu, mul_pow, ← pow_mul] at this
    have hdvd : (π u') ^ (d * a) ∣ (π u') ^ N :=
      ⟨π g₀ * ↑(e ^ a), by rw [← this, Units.val_pow_eq_pow_val]; ring⟩
    have := hord hdvd
    nlinarith
  have hc0 : c ≠ 0 := fun h ↦ hc (h ▸ zero_mem _)
  obtain ⟨n, w', hw'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  have hnN : n ≤ N := by
    by_contra hlt
    exact hc (Ideal.mem_span_singleton'.mpr ⟨w' * ϖ ^ (n - (N + 1)), by
      rw [hw', mul_assoc, ← pow_add]; congr 2; omega⟩)
  set E := algebraMap O D w' + p ^ (N + 1 - n) * g with hE_def
  have hE : IsUnit E := by
    by_contra hc'
    have hEm : E ∈ maximalIdeal D := (mem_maximalIdeal E).mpr hc'
    have : algebraMap O D w' ∈ maximalIdeal D := by
      have := sub_mem hEm (Ideal.mul_mem_right g _ (Ideal.pow_mem_of_mem _ hpmax _
        (by omega : 0 < N + 1 - n)))
      rwa [hE_def, add_sub_cancel_right] at this
    exact this ((w'.isUnit.map (algebraMap O D)))
  have huvE : u * v = p ^ n * E := by
    have hpow : p ^ (N + 1) = p ^ n * p ^ (N + 1 - n) := by
      rw [← pow_add]; congr 1; omega
    rw [huv, hw', map_mul, map_pow, hE_def, ← hp_def, hpow]
    ring
  set v₁ := v * ↑hE.unit⁻¹ with hv₁_def
  have huv₁ : u * v₁ = p ^ n := by
    rw [hv₁_def, ← mul_assoc, huvE, mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hn : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    rw [this, pow_zero] at huv₁
    exact (mem_maximalIdeal u).mp humax (IsUnit.of_mul_eq_one (b := v₁) huv₁)
  have hmax' : maximalIdeal D = Ideal.span {p, u, v₁} := by
    rw [H.maximalIdeal_eq, hv₁_def, span_triple_mul_unit,
      span_triple_eq (by rw [← neg_sub]; exact neg_mem hu) (by rw [← neg_sub]; exact neg_mem hv)]
  have hv₁₂ : v₁ ∉ 𝔔₂ := fun h ↦ by
    have : v₁ * E ∈ 𝔔₂ := Ideal.mul_mem_right _ _ h
    rw [hv₁_def, mul_assoc, IsUnit.val_inv_mul, mul_one] at this
    exact hv₂ this
  -- `ι₂ u = unit * ϖ ^ n`
  have hu₂ : ∃ μ : L₂ˣ, ι₂ u = μ * ι₂ p ^ n := by
    refine ⟨(hunit₂ v₁ hv₁₂).unit⁻¹, ?_⟩
    calc ι₂ u = ↑(hunit₂ v₁ hv₁₂).unit⁻¹ * (ι₂ u * ι₂ v₁) := by
          rw [mul_comm (ι₂ u), ← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = _ := by rw [← map_mul, huv₁, map_pow]
  obtain ⟨μ, hμ⟩ := hu₂
  obtain ⟨ν, hν⟩ := hx₂
  -- the Krull criterion for quotients of monomials in `u` and `x`
  have krull : ∀ i j k l : ℕ, (n * k + N * l ≤ n * i + N * j) →
      ∃ g : D, u ^ k * x ^ l * g = u ^ i * x ^ j := by
    intro i j k l hijkl
    refine exists_mul_eq_of_forall_dvr
      (mul_ne_zero (pow_ne_zero _ hu0) (pow_ne_zero _ hx0)) fun 𝔔 h𝔔 hdvr ↦ ?_
    by_cases hp𝔔 : p ∈ 𝔔
    · rcases H.eq_or_eq_of_isDiscreteValuationRing hϖ0 hdvr hp𝔔 with h | h <;> subst 𝔔
      · refine Or.inl ⟨1, ?_⟩
        rw [mul_one]
        intro hm
        rcases H.isPrime₁.mem_or_mem hm with h | h
        · exact hu₁ (H.isPrime₁.mem_of_pow_mem _ h)
        · exact hx₁ (H.isPrime₁.mem_of_pow_mem _ h)
      · right
        have e1 : ι₂ (u ^ k * x ^ l) = ↑(μ ^ k * ν ^ l) * ι₂ p ^ (n * k + N * l) := by
          rw [map_mul, map_pow, map_pow, hμ, hν]
          simp only [Units.val_mul, Units.val_pow_eq_pow_val]
          ring
        have e2 : ι₂ (u ^ i * x ^ j) = ↑(μ ^ i * ν ^ j) * ι₂ p ^ (n * i + N * j) := by
          rw [map_mul, map_pow, map_pow, hμ, hν]
          simp only [Units.val_mul, Units.val_pow_eq_pow_val]
          ring
        simpa using dvd_of_eq_unit_mul_pow (k := 1) (l := 1) e1 e2 (by omega)
    · refine Or.inl ⟨v₁ ^ k * y ^ l, ?_⟩
      have : u ^ k * x ^ l * (v₁ ^ k * y ^ l) =
          algebraMap O D (↑(w ^ l)) * p ^ (n * k + N * l) := by
        rw [show u ^ k * x ^ l * (v₁ ^ k * y ^ l) = (u * v₁) ^ k * (x * y) ^ l by ring, huv₁,
          hxy, hc₀D, Units.val_pow_eq_pow_val, map_pow]
        ring
      rw [this]
      exact hgen 𝔔 h𝔔 hp𝔔 _ _ ((w ^ l).isUnit.map (algebraMap O D))
  -- `N = d n`
  obtain ⟨g₂, hg₂⟩ := krull N 0 0 n (le_of_eq (by ring))
  obtain ⟨g₂', hg₂'⟩ := krull 0 n N 0 (le_of_eq (by ring))
  simp only [pow_zero, one_mul, mul_one] at hg₂ hg₂'
  have hg₂u : IsUnit g₂ := by
    refine IsUnit.of_mul_eq_one (b := g₂') ?_
    have : u ^ N * (g₂ * g₂') = u ^ N * 1 := by
      rw [mul_one, mul_comm g₂ g₂', ← mul_assoc, hg₂', hg₂]
    exact mul_left_cancel₀ (pow_ne_zero _ hu0) this
  have hNdn : N = d * n := by
    have := congrArg π hg₂
    rw [map_mul, map_pow, map_pow, he, hπu, mul_pow, ← pow_mul] at this
    have hgπ : IsUnit (π g₂) := hg₂u.map π
    apply le_antisymm
    · refine hord ⟨↑(hgπ.unit⁻¹) * ↑(e ^ n)⁻¹, ?_⟩
      rw [← this]
      have h1 : (↑e : D ⧸ 𝔔₁) ^ n * ↑(e ^ n)⁻¹ = 1 := by
        rw [← Units.val_pow_eq_pow_val, Units.mul_inv]
      have h2 : π g₂ * ↑hgπ.unit⁻¹ = 1 := IsUnit.mul_val_inv _
      linear_combination (-(π u' ^ (d * n) * (π g₂ * ↑hgπ.unit⁻¹))) * h1 - π u' ^ (d * n) * h2
    · exact hord ⟨↑e ^ n * π g₂, by rw [← this]; ring⟩
  -- `x = ε u ^ d`
  obtain ⟨g₃, hg₃⟩ := krull 0 1 d 0 (by rw [hNdn]; nlinarith)
  obtain ⟨g₃', hg₃'⟩ := krull d 0 0 1 (by rw [hNdn]; nlinarith)
  simp only [pow_zero, one_mul, mul_one, pow_one] at hg₃ hg₃'
  have hg₃u : g₃ * g₃' = 1 := by
    have : u ^ d * (g₃ * g₃') = u ^ d * 1 := by
      rw [mul_one, ← mul_assoc, hg₃, hg₃']
    exact mul_left_cancel₀ (pow_ne_zero _ hu0) this
  let ε : Dˣ := ⟨g₃, g₃', hg₃u, by rw [mul_comm]; exact hg₃u⟩
  refine ⟨n, u, v₁, hn, huv₁, hmax', hu₁, hv₁₂, ?_, ⟨ε, ?_⟩, ⟨ε⁻¹ * (hwD.unit), ?_⟩⟩
  · exact hu
  · change x = g₃ * u ^ d
    rw [← hg₃, mul_comm]
  · -- `ε u ^ d y = w (u v)^d`
    have h1 : u ^ d * (g₃ * y) = u ^ d * (algebraMap O D w * v₁ ^ d) := by
      calc u ^ d * (g₃ * y) = x * y := by rw [← hg₃]; ring
        _ = algebraMap O D w * (u * v₁) ^ d := by
          rw [hxy, hc₀D, huv₁, ← pow_mul, hNdn, mul_comm d n]
        _ = _ := by rw [mul_pow]; ring
    have h2 := mul_left_cancel₀ (pow_ne_zero d hu0) h1
    simp only [Units.val_mul, IsUnit.unit_spec]
    change y = g₃' * algebraMap O D w * v₁ ^ d
    calc y = g₃' * (g₃ * y) := by rw [← mul_assoc, mul_comm g₃' g₃, hg₃u, one_mul]
      _ = _ := by rw [h2]; ring

omit [IsIntegrallyClosed D] in
/-- **Node coordinates are transcendental**: an element `u` whose image in the outer branch
`D ⧸ 𝔔₁` is a uniformizer satisfies no nonzero polynomial equation over `O`. -/
theorem transcendental_of_irreducible (H : IsOrdinaryDoublePoint ϖ u' v' 𝔔₁ 𝔔₂)
    (hϖ : Irreducible ϖ) (hϖ0 : algebraMap O D ϖ ≠ 0) {u : D}
    (hu : Irreducible (Ideal.Quotient.mk 𝔔₁ u)) {P : Polynomial O}
    (hP : Polynomial.aeval u P = 0) : P = 0 := by
  classical
  haveI := H.isPrime₁
  obtain ⟨hR', -⟩ := H.isDiscreteValuationRing_quotient
  let π := Ideal.Quotient.mk 𝔔₁
  by_contra hP0
  -- remove the `ϖ`-content of `P`
  have hbound : ∃ k, ¬ Polynomial.C (ϖ ^ (k + 1)) ∣ P := by
    obtain ⟨i, hi⟩ : ∃ i, P.coeff i ≠ 0 := by
      by_contra h; push Not at h; exact hP0 (Polynomial.ext h)
    obtain ⟨k, w, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hi hϖ
    refine ⟨k, fun h ↦ ?_⟩
    have := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp h i
    rw [hk, pow_succ, mul_comm (↑w : O)] at this
    have h3 := (mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)).mp this
    exact hϖ.not_isUnit (isUnit_of_dvd_unit h3 w.isUnit)
  let k := Nat.find hbound
  have hk : ¬ Polynomial.C (ϖ ^ (k + 1)) ∣ P := Nat.find_spec hbound
  have hk' : Polynomial.C (ϖ ^ k) ∣ P := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero, map_one]; exact one_dvd _
    · have := Nat.find_min hbound (show k - 1 < k by omega)
      push Not at this
      rwa [Nat.sub_add_cancel hpos] at this
  obtain ⟨Q, hQP⟩ := hk'
  have hQ : Polynomial.aeval u Q = 0 := by
    rw [hQP, map_mul, Polynomial.aeval_C, map_pow] at hP
    exact (mul_eq_zero.mp hP).resolve_left (pow_ne_zero _ hϖ0)
  have hQϖ : ¬ Polynomial.C ϖ ∣ Q := fun h ↦ hk (by
    rw [hQP, pow_succ, map_mul]; exact mul_dvd_mul_left _ h)
  -- coefficients of `Q` map to `0` or units of `D ⧸ 𝔔₁`
  have hcoef : ∀ o : O, ϖ ∣ o ∨ IsUnit (π (algebraMap O D o)) := by
    intro o
    by_cases h : ϖ ∣ o
    · exact Or.inl h
    · right
      have : IsUnit o := by
        by_contra hnu
        have hm : o ∈ maximalIdeal O := (mem_maximalIdeal o).mpr hnu
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ] at hm
        exact h (Ideal.mem_span_singleton.mp hm)
      exact this.map _ |>.map _
  have hzero : ∀ o : O, ϖ ∣ o → π (algebraMap O D o) = 0 := by
    rintro o ⟨o', rfl⟩
    rw [map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr H.mem₁, zero_mul]
  let Q' : Polynomial (D ⧸ 𝔔₁) := Q.map (π.comp (algebraMap O D))
  have hQ'0 : Q' ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, ¬ ϖ ∣ Q.coeff i := by
      by_contra h; push Not at h
      exact hQϖ ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr h)
    intro h0
    have : Q'.coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
    rw [Polynomial.coeff_map] at this
    exact ((hcoef _).resolve_left hi).ne_zero this
  have hQ'u : Q'.eval (π u) = 0 := by
    rw [Polynomial.eval_map, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hQ, map_zero]
  obtain ⟨R, hR, hRX⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q' hQ'0 0
  set m := Polynomial.rootMultiplicity 0 Q'
  simp only [map_zero, sub_zero] at hR hRX
  have hR0 : R.coeff 0 ≠ 0 := fun h ↦ hRX (Polynomial.X_dvd_iff.mpr h)
  have hRunit : IsUnit (R.coeff 0) := by
    have hc : R.coeff 0 = Q'.coeff m := by
      conv_rhs => rw [hR]
      rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    rw [hc, Polynomial.coeff_map] at hR0 ⊢
    exact (hcoef _).resolve_left fun h ↦ hR0 (hzero _ h)
  have hRev : IsUnit (R.eval (π u)) := by
    have hmem : R.eval (π u) - R.coeff 0 ∈ maximalIdeal (D ⧸ 𝔔₁) := by
      obtain ⟨S, hS⟩ := Polynomial.X_dvd_iff.mpr (show (R - Polynomial.C (R.coeff 0)).coeff 0 = 0
        by simp)
      have : R.eval (π u) - R.coeff 0 = π u * S.eval (π u) := by
        have := congrArg (Polynomial.eval (π u)) hS
        simpa using this
      rw [this]
      exact Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr hu.not_isUnit)
    by_contra hnu
    have h1 : R.eval (π u) ∈ maximalIdeal (D ⧸ 𝔔₁) := (mem_maximalIdeal _).mpr hnu
    have := sub_mem h1 hmem
    rw [sub_sub_cancel] at this
    exact (mem_maximalIdeal _).mp this hRunit
  rw [hR, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hQ'u
  rcases mul_eq_zero.mp hQ'u with h | h
  · exact hu.ne_zero (pow_eq_zero_iff'.mp h).1
  · exact hRev.ne_zero h

end IsOrdinaryDoublePoint

end Deformation

section NodeInjective

variable {O S : Type*} [CommRing O] [IsDomain O] [CommRing S] [Algebra O S]

/-- **The node embeds** into a domain along transcendental coordinates: if `u` satisfies no
nonzero polynomial over `O` and `u v = a ≠ 0`, then `Node O a → S`, `u ↦ u`, `v ↦ v` is
injective. -/
theorem Node.lift_injective {a : O} (ha : a ≠ 0) {u v : S} (huv : u * v = algebraMap O S a)
    (htr : ∀ P : Polynomial O, Polynomial.aeval u P = 0 → P = 0) :
    Function.Injective (Node.lift u v huv) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hz' : z ∈ Submodule.span O (Set.range (Node.monomial a)) := by
    rw [Node.span_eq_top]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz'
  suffices c = 0 by simp [this]
  -- the bound on the `v`-exponents
  let M : ℕ := c.support.sup (Sum.elim (fun _ ↦ 0) (fun j ↦ j + 1))
  have hM : ∀ j, Sum.inr j ∈ c.support → j + 1 ≤ M := fun j hj ↦
    Finset.le_sup (f := Sum.elim (fun _ ↦ 0) (fun j ↦ j + 1)) hj
  let deg : ℕ ⊕ ℕ → ℕ := Sum.elim (fun i ↦ M + i) (fun j ↦ M - (j + 1))
  let coef : ℕ ⊕ ℕ → O := Sum.elim (fun _ ↦ 1) (fun j ↦ a ^ (j + 1))
  let P : Polynomial O := c.sum fun s r ↦ Polynomial.monomial (deg s) (r * coef s)
  have hP : Polynomial.aeval u P =
      u ^ M * Node.lift u v huv (c.sum fun s r ↦ r • Node.monomial a s) := by
    simp only [P, map_finsuppSum, Finsupp.mul_sum, map_smul, Polynomial.aeval_monomial]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rcases s with i | j
    · simp only [deg, coef, Node.monomial, Sum.elim_inl, map_pow, Node.lift_u, mul_one,
        Algebra.smul_def]
      rw [pow_add]; ring
    · simp only [deg, coef, Node.monomial, Sum.elim_inr, map_pow, Node.lift_v, map_mul,
        Algebra.smul_def]
      have hj := hM j hs
      rw [← huv, mul_pow]
      conv_rhs => rw [show M = (M - (j + 1)) + (j + 1) by omega, pow_add]
      ring
  have hP0 : P = 0 := htr P (by rw [hP, hz, mul_zero])
  ext s
  by_cases hs : s ∈ c.support
  swap
  · exact Finsupp.notMem_support_iff.mp hs
  have hdeg : ∀ t ∈ c.support, deg t = deg s → t = s := by
    intro t ht h
    rcases s with i | j <;> rcases t with i' | j' <;>
      simp only [deg, Sum.elim_inl, Sum.elim_inr] at h
    · rw [show i' = i by omega]
    · have := hM j' ht; omega
    · have := hM j hs; omega
    · have := hM j hs; have := hM j' ht; rw [show j' = j by omega]
  have hcoef : P.coeff (deg s) = c s * coef s := by
    simp only [P, Finsupp.sum, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single s]
    · simp
    · intro t ht hts
      rw [if_neg (fun h ↦ hts (hdeg t ht h))]
    · intro h; exact absurd hs h
  have hcoef0 : coef s ≠ 0 := by
    rcases s with i | j
    · exact one_ne_zero
    · exact pow_ne_zero _ ha
  rw [hP0, Polynomial.coeff_zero] at hcoef
  simpa [hcoef0] using hcoef.symm

end NodeInjective

end SemistableReduction
