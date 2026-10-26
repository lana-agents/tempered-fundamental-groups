/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeNormal

/-!
# Regularity of the Tate node chart away from its nodes (MR12 S5.2)

Let `O` be a DVR with uniformizer `ϖ` and residue field `k` (`θ : O → k` onto, `ker θ = (ϖ)`),
`m ≥ 1`, `ε` a unit, and `NR = (A[S]/(S² + S − c))[1/D]` the quadratic node chart of the Tate
model (`TateTwoChartNode.NR`, `A = O[u,v]/(uv − ϖᵐ)`). At a closed point `P` of the special fibre
which is not one of the two nodes (`ϖ ∈ P`, `f = u + v ∉ P`) the local ring `NR_P` is regular with
regular system of parameters `(ϖ, y)`:

* **`TateTwoChartNode.exists_regular_pair`**: `ϖ` is prime in `NR_P`, `𝔪_P = (ϖ, y)` and
  `y ∉ (ϖ)` (the input of `Purity.etale_of_isUnramifiedAt_of_maximalIdeal_eq_span_pair`). Valid in
  every residue characteristic, including `2` and `3`.

Method. The special fibre `L̄ = NR_P/(ϖ)` is identified with a localization `k[X]_Q` at a nonzero
prime (`TateNodeRegular.exists_regular_pair_of_chartData`): from *chart data* (`ChartData`), i.e.
a map `γ : NR → k[X][1/h]` (built with `liftNR`) inverse to `β : k[X] → L̄`, `X ↦ z`, one gets
mutually inverse maps `L̄ ⇄ k[X]_Q` for `Q = β⁻¹(𝔪)`; `Q ≠ 0` because `P` is maximal (otherwise
`k[X][1/h] → k(X)` would be onto). So `L̄` is a DVR, and a uniformizer of `L̄` lifts to `y`
(`TateNodeRegular.exists_regular_pair_of_quotient_equiv`). As `uv = ϖᵐ`, exactly one of `u`, `v`
is a unit at `P`:

* `v` a unit (`chartData_V`): `u = 0` and `S² + S = ε v` on `L̄`; chart `k[X]`, `S ↦ X`,
  `u ↦ 0`, `v ↦ (X² + X)/ε`;
* `u` a unit (`chartData_U`): `v = 0` and `S² + S = b₆ u²`; for the root `s₀ ∈ {0, −1}` of
  `S² + S` with `S − s₀` a unit at `P` and `τ = 1 + 2 s₀` (so `τ² = 1`), `X = (S − s₀)/u` gives the
  chart `k[X][1/h]`, `h = X (b₆ − X²) ((b₆ − X²)² + b₄ X²)`, `u ↦ τ X/(b₆ − X²)`,
  `S ↦ s₀ + τ X²/(b₆ − X²)` (the polynomial identities are `sU_sq`, `wU_D`, `wU_eq`, `sU_eq`,
  `isUnit_U`).

All computations happen in rings that are variables (`ChartData` is stated for an arbitrary ring
map `φ` out of `NR`); only the final assembly instantiates `φ` with `NR → NR_P/(ϖ)`.
-/

universe u

open Polynomial IsLocalRing

namespace SemistableReduction

namespace TateNodeRegular

/-! ### Generic commutative algebra -/

section Generic

lemma isUnit_of_isUnit_mk {L : Type*} [CommRing L] [IsLocalRing L] {I : Ideal L}
    (hI : I ≤ maximalIdeal L) {l : L} (hl : IsUnit (Ideal.Quotient.mk I l)) : IsUnit l := by
  obtain ⟨l', hl'⟩ := hl.exists_right_inv
  obtain ⟨l'', rfl⟩ := Ideal.Quotient.mk_surjective l'
  rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hl'
  by_contra hu
  have h1 : l * l'' ∈ maximalIdeal L := Ideal.mul_mem_right _ _ ((mem_maximalIdeal l).2 hu)
  exact (maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).2
    (by simpa using Ideal.sub_mem _ h1 (hI hl')))

/-- **A regular pair from a DVR quotient**: if `x ≠ 0` lies in the maximal ideal of a local domain
`L` and `L/(x)` is a discrete valuation ring, then `x` is prime and `𝔪 = (x, y)` with
`y ∉ (x)`. -/
theorem exists_regular_pair_of_quotient_equiv {L : Type*} [CommRing L] [IsLocalRing L]
    {x : L} (hx0 : x ≠ 0) (hxm : x ∈ maximalIdeal L) {D : Type*} [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] (e : L ⧸ Ideal.span {x} ≃+* D) :
    ∃ y : L, Prime x ∧ y ∉ Ideal.span {x} ∧ maximalIdeal L = Ideal.span {x, y} := by
  have hI : Ideal.span {x} ≤ maximalIdeal L := (Ideal.span_singleton_le_iff_mem _).2 hxm
  have hprime : Prime x := by
    rw [← Ideal.span_singleton_prime hx0, ← Ideal.Quotient.isDomain_iff_prime]
    exact Function.Injective.isDomain (e : L ⧸ Ideal.span {x} →+* D) e.injective
  obtain ⟨ϖD, hϖD⟩ := IsDiscreteValuationRing.exists_irreducible D
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e.symm ϖD)
  have hey : e (Ideal.Quotient.mk _ y) = ϖD := by rw [hy, RingEquiv.apply_symm_apply]
  -- `l ∈ 𝔪 ↔ e (l mod x) ∈ (ϖD)`
  have key : ∀ l : L, l ∈ maximalIdeal L ↔ e (Ideal.Quotient.mk _ l) ∈ Ideal.span {ϖD} := by
    intro l
    rw [← hϖD.maximalIdeal_eq, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    refine not_congr ⟨fun h ↦ (h.map (Ideal.Quotient.mk _)).map e, fun h ↦ ?_⟩
    exact isUnit_of_isUnit_mk hI (by simpa using h.map e.symm)
  refine ⟨y, hprime, fun hy0 ↦ hϖD.ne_zero ?_, ?_⟩
  · rw [← hey, Ideal.Quotient.eq_zero_iff_mem.2 hy0, map_zero]
  · ext l
    rw [key, Ideal.mem_span_singleton', Ideal.mem_span_pair]
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e.symm d)
      have hl : Ideal.Quotient.mk (Ideal.span {x}) l = e.symm d * Ideal.Quotient.mk _ y := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, hey, hd]
      have : Ideal.Quotient.mk (Ideal.span {x}) (l - b * y) = 0 := by
        rw [map_sub, map_mul, hb, hl, sub_self]
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
      exact ⟨a, b, by rw [ha]; ring⟩
    · rintro ⟨a, b, rfl⟩
      refine ⟨e (Ideal.Quotient.mk _ b), ?_⟩
      rw [map_add, map_mul, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self x), mul_zero, zero_add,
        map_mul, hey]

end Generic

/-! ### Regular pairs from a chart of the special fibre -/

/-! ### Identities on the `u`-branch -/

section UBranch

variable {T : Type*} [CommRing T]

/-- `1/(b₆ − X²)` on the chart of the `u`-branch, given `Hi = 1/h`. -/
def eiU (b₄ b₆ X Hi : T) : T := X * ((b₆ - X ^ 2) ^ 2 + b₄ * X ^ 2) * Hi

/-- The value of `u` on the chart of the `u`-branch: `τ X/(b₆ − X²)`. -/
def wU (b₄ b₆ s₀ X Hi : T) : T := (1 + 2 * s₀) * X * eiU b₄ b₆ X Hi

/-- The value of `S` on the chart of the `u`-branch: `s₀ + τ X²/(b₆ − X²)`. -/
def sU (b₄ b₆ s₀ X Hi : T) : T := s₀ + (1 + 2 * s₀) * X ^ 2 * eiU b₄ b₆ X Hi

variable {b₄ b₆ s₀ X Hi : T}

lemma sU_sq (hs₀ : s₀ ^ 2 + s₀ = 0)
    (hH : X * (b₆ - X ^ 2) * ((b₆ - X ^ 2) ^ 2 + b₄ * X ^ 2) * Hi = 1) :
    sU b₄ b₆ s₀ X Hi ^ 2 + sU b₄ b₆ s₀ X Hi - b₆ * wU b₄ b₆ s₀ X Hi ^ 2 = 0 := by
  have hei : (b₆ - X ^ 2) * eiU b₄ b₆ X Hi = 1 := by rw [eiU]; linear_combination hH
  unfold sU wU
  linear_combination hs₀ - X ^ 2 * eiU b₄ b₆ X Hi * (1 + 2 * s₀) ^ 2 * hei

lemma wU_D (hs₀ : s₀ ^ 2 + s₀ = 0)
    (hH : X * (b₆ - X ^ 2) * ((b₆ - X ^ 2) ^ 2 + b₄ * X ^ 2) * Hi = 1) :
    (1 + b₄ * wU b₄ b₆ s₀ X Hi ^ 2) * ((b₆ - X ^ 2) ^ 3 * X * Hi) = 1 := by
  have hei : eiU b₄ b₆ X Hi * (b₆ - X ^ 2) = 1 := by rw [eiU]; linear_combination hH
  unfold wU
  linear_combination hH + b₄ * X ^ 2 * (b₆ - X ^ 2) * X * Hi *
    ((1 + 2 * s₀) ^ 2 * (eiU b₄ b₆ X Hi * (b₆ - X ^ 2) + 1) * hei + 4 * hs₀)

variable {u S z hi : T}

lemma U_claim (hs₀ : s₀ ^ 2 + s₀ = 0) (hu : IsUnit u) (hzu : z * u = S - s₀)
    (hR : S ^ 2 + S = b₆ * u ^ 2) : (1 + 2 * s₀) * z = (b₆ - z ^ 2) * u := by
  have hS : S = z * u + s₀ := by rw [hzu]; ring
  rw [hS] at hR
  have hG : (1 + 2 * s₀) * z * u - b₆ * u ^ 2 + z ^ 2 * u ^ 2 = 0 := by
    linear_combination hR - hs₀
  have hui : u * ↑hu.unit⁻¹ = 1 := hu.mul_val_inv
  linear_combination ↑hu.unit⁻¹ * hG - ((1 + 2 * s₀) * z - (b₆ - z ^ 2) * u) * hui

lemma wU_eq (hs₀ : s₀ ^ 2 + s₀ = 0) (hu : IsUnit u) (hzu : z * u = S - s₀)
    (hR : S ^ 2 + S = b₆ * u ^ 2)
    (hhi : z * (b₆ - z ^ 2) * ((b₆ - z ^ 2) ^ 2 + b₄ * z ^ 2) * hi = 1) :
    wU b₄ b₆ s₀ z hi = u := by
  have hc := U_claim hs₀ hu hzu hR
  unfold wU eiU
  linear_combination (z * ((b₆ - z ^ 2) ^ 2 + b₄ * z ^ 2) * hi) * hc + u * hhi

lemma sU_eq (hs₀ : s₀ ^ 2 + s₀ = 0) (hu : IsUnit u) (hzu : z * u = S - s₀)
    (hR : S ^ 2 + S = b₆ * u ^ 2)
    (hhi : z * (b₆ - z ^ 2) * ((b₆ - z ^ 2) ^ 2 + b₄ * z ^ 2) * hi = 1) :
    sU b₄ b₆ s₀ z hi = S := by
  have hw := wU_eq hs₀ hu hzu hR hhi
  unfold wU at hw
  unfold sU
  linear_combination z * hw + hzu

lemma isUnit_U (hs₀ : s₀ ^ 2 + s₀ = 0) (hu : IsUnit u) (hS : IsUnit (S - s₀))
    (hD : IsUnit (1 + b₄ * u ^ 2)) (hzu : z * u = S - s₀) (hR : S ^ 2 + S = b₆ * u ^ 2) :
    IsUnit (z * (b₆ - z ^ 2) * ((b₆ - z ^ 2) ^ 2 + b₄ * z ^ 2)) := by
  have hc := U_claim hs₀ hu hzu hR
  have hui : u * ↑hu.unit⁻¹ = 1 := hu.mul_val_inv
  have hz : IsUnit z := by
    rw [show z = (S - s₀) * ↑hu.unit⁻¹ by linear_combination ↑hu.unit⁻¹ * hzu - z * hui]
    exact hS.mul hu.unit⁻¹.isUnit
  have hτ : IsUnit (1 + 2 * s₀) := IsUnit.of_mul_eq_one (1 + 2 * s₀) (by
    linear_combination 4 * hs₀)
  have he : IsUnit (b₆ - z ^ 2) := by
    rw [show b₆ - z ^ 2 = (1 + 2 * s₀) * z * ↑hu.unit⁻¹ by
      linear_combination -(↑hu.unit⁻¹ * hc) - (b₆ - z ^ 2) * hui]
    exact (hτ.mul hz).mul hu.unit⁻¹.isUnit
  have hF : IsUnit ((b₆ - z ^ 2) ^ 2 + b₄ * z ^ 2) := by
    rw [show (b₆ - z ^ 2) ^ 2 + b₄ * z ^ 2 = z ^ 2 * (1 + b₄ * u ^ 2) * ↑hu.unit⁻¹ ^ 2 by
      linear_combination (↑hu.unit⁻¹ ^ 2 * (-((b₆ - z ^ 2) * u + (1 + 2 * s₀) * z))) * hc +
        ↑hu.unit⁻¹ ^ 2 * z ^ 2 * 4 * hs₀ -
        ((b₆ - z ^ 2) ^ 2 + b₄ * z ^ 2) * (u * ↑hu.unit⁻¹ + 1) * hui]
    exact ((hz.pow 2).mul hD).mul (hu.unit⁻¹.isUnit.pow 2)
  exact (hz.mul he).mul hF

end UBranch

section Chart

variable {R : Type u} [CommRing R] {k : Type u} [Field k] {B : Type u} [CommRing B]

/-- **Chart data** for a ring map `φ : R → B` at `(x, P)`: a ring map `c : k → B`, an element `z`
(giving `β : k[X] → B`, `X ↦ z`), a polynomial `h` with `β h` a unit and a ring map
`γ : R → k[X][1/h]` killing `x`, such that `β ∘ γ = φ`, every `c a` is `φ r` for some `r` with
`γ r = a`, and `z = (φ r₁ - φ r₀) / φ r₂` with `r₂ ∉ P`, `γ r₁ - γ r₀ = X γ r₂`. -/
def ChartData (φ : R →+* B) (x : R) (P : Ideal R) (c : k →+* B) : Prop :=
  ∃ (z : B) (h : k[X]) (hβh : IsUnit (eval₂RingHom c z h)) (γ : R →+* Localization.Away h)
    (r₀ r₁ r₂ : R), γ x = 0 ∧
    (∀ r, IsLocalization.Away.lift (S := Localization.Away h) h hβh (γ r) = φ r) ∧
    (∀ a, ∃ r, c a = φ r ∧ γ r = algebraMap k[X] _ (C a)) ∧
    r₂ ∉ P ∧ z * φ r₂ = φ r₁ - φ r₀ ∧ γ r₁ - γ r₀ = algebraMap k[X] _ X * γ r₂

variable [IsDomain R] {P : Ideal R} [P.IsMaximal] {x : R}

local notation "𝓛" => Localization.AtPrime P

local notation "𝕀" => Ideal.span {algebraMap R 𝓛 x}

/-- **Regular pair from a chart of the special fibre.** Let `P` be a maximal ideal of a domain
`R`, `0 ≠ x ∈ P`, `L = R_P` and `L̄ = L/(x)`. Given chart data for `R → L̄` (`ChartData`),
`L̄ ≅ k[X]_Q` for the nonzero prime `Q = β⁻¹(𝔪)` of `k[X]` (nonzero because `P` is maximal), so
`L̄` is a DVR, and `x` is part of a regular system of parameters `(x, y)` of `L`. -/
theorem exists_regular_pair_of_chartData (hx0 : x ≠ 0) (hxP : x ∈ P) (c : k →+* 𝓛 ⧸ 𝕀)
    (hcd : ChartData ((Ideal.Quotient.mk 𝕀).comp (algebraMap R 𝓛)) x P c) :
    ∃ y : Localization.AtPrime P, Prime (algebraMap R (Localization.AtPrime P) x) ∧
      y ∉ Ideal.span {algebraMap R (Localization.AtPrime P) x} ∧
      maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap R (Localization.AtPrime P) x, y} := by
  obtain ⟨z, h, hβh, γ, r₀, r₁, r₂, hγx, hΨγ, hc, hr₂, hz, hγz⟩ := hcd
  simp only [RingHom.comp_apply] at hΨγ hc hz
  classical
  have hxL0 : algebraMap R 𝓛 x ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective 𝓛 P.primeCompl_le_nonZeroDivisors)).2 hx0
  have hxLm : algebraMap R 𝓛 x ∈ maximalIdeal 𝓛 :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff 𝓛 P x).2 hxP
  have hIm : 𝕀 ≤ maximalIdeal 𝓛 := (Ideal.span_singleton_le_iff_mem _).2 hxLm
  haveI : Nontrivial (𝓛 ⧸ 𝕀) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal 𝓛).ne_top hIm)
  haveI : IsLocalRing (𝓛 ⧸ 𝕀) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let β : k[X] →+* 𝓛 ⧸ 𝕀 := eval₂RingHom c z
  let Q : Ideal k[X] := (maximalIdeal (𝓛 ⧸ 𝕀)).comap β
  have hQ : ∀ p, p ∉ Q ↔ IsUnit (β p) := fun p ↦ by
    simp [Q, mem_maximalIdeal, mem_nonunits_iff]
  let TQ := Localization.AtPrime Q
  let Ψ : TQ →+* 𝓛 ⧸ 𝕀 :=
    IsLocalization.lift (M := Q.primeCompl) (g := β) fun p ↦ (hQ p).1 p.2
  have hΨ : ∀ p, Ψ (algebraMap k[X] TQ p) = β p := IsLocalization.lift_eq _
  have hhQ : h ∉ Q := (hQ h).2 hβh
  let ι : Localization.Away h →+* TQ :=
    IsLocalization.Away.lift h (g := algebraMap k[X] TQ)
      (IsLocalization.map_units TQ (⟨h, hhQ⟩ : Q.primeCompl))
  have hι : ∀ p, ι (algebraMap k[X] _ p) = algebraMap k[X] TQ p :=
    IsLocalization.Away.lift_eq _ _
  have hΨι : Ψ.comp ι = IsLocalization.Away.lift (S := Localization.Away h) h hβh :=
    IsLocalization.ringHom_ext (Submonoid.powers h) (RingHom.ext fun p ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, hι, hΨ, RingHom.comp_apply,
        IsLocalization.Away.lift_eq])
  let α : R →+* TQ := ι.comp γ
  have hΨα : ∀ r, Ψ (α r) = Ideal.Quotient.mk 𝕀 (algebraMap R 𝓛 r) := fun r ↦ by
    rw [← hΨγ, ← hΨι]; rfl
  -- `Ψ` reflects units
  have hunit : ∀ t : TQ, IsUnit (Ψ t) → IsUnit t := by
    intro t ht
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj Q.primeCompl t
    have hβa : IsUnit (β a) := by
      rw [← hΨ, ← hs, map_mul]
      exact ht.mul ((IsLocalization.map_units TQ s).map Ψ)
    have : IsUnit (t * algebraMap k[X] TQ s) := by
      rw [hs]; exact IsLocalization.map_units TQ (⟨a, (hQ a).2 hβa⟩ : Q.primeCompl)
    exact isUnit_of_mul_isUnit_left this
  have hαunit : ∀ r, r ∉ P → IsUnit (α r) := fun r hr ↦ hunit _ (by
    rw [hΨα]; exact ((IsLocalization.map_units 𝓛 (⟨r, hr⟩ : P.primeCompl)).map _))
  let Φ : 𝓛 →+* TQ := IsLocalization.lift (M := P.primeCompl) (g := α) fun r ↦ hαunit r r.2
  have hΦ : ∀ r, Φ (algebraMap R 𝓛 r) = α r := IsLocalization.lift_eq _
  have hΦx : ∀ a ∈ 𝕀, Φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hΦ]
    simp [α, hγx]
  let Φb : 𝓛 ⧸ 𝕀 →+* TQ := Ideal.Quotient.lift 𝕀 Φ hΦx
  have hΦb : ∀ r, Φb (Ideal.Quotient.mk 𝕀 (algebraMap R 𝓛 r)) = α r := fun r ↦ by
    simp only [Φb, Ideal.Quotient.lift_mk, hΦ]
  have h1 : Ψ.comp Φb = RingHom.id _ :=
    Ideal.Quotient.ringHom_ext (IsLocalization.ringHom_ext P.primeCompl (RingHom.ext fun r ↦ by
      simp only [RingHom.comp_apply, hΦb, hΨα, RingHom.id_apply]))
  have hΦbz : Φb z = algebraMap k[X] TQ X := by
    have h' := congrArg Φb hz
    rw [map_mul, map_sub, hΦb, hΦb, hΦb] at h'
    have h'' : α r₁ - α r₀ = algebraMap k[X] TQ X * α r₂ := by
      simp only [α, RingHom.comp_apply, ← map_sub, hγz, map_mul, hι]
    rw [h''] at h'
    exact (hαunit r₂ hr₂).mul_left_inj.1 h'
  have h2 : Φb.comp Ψ = RingHom.id _ := by
    refine IsLocalization.ringHom_ext Q.primeCompl (Polynomial.ringHom_ext (fun a ↦ ?_) ?_)
    · obtain ⟨r, hr, hγr⟩ := hc a
      simp only [RingHom.comp_apply, hΨ, β, coe_eval₂RingHom, eval₂_C, hr, hΦb, α, hγr, hι,
        RingHom.id_apply]
    · simp only [RingHom.comp_apply, hΨ, β, coe_eval₂RingHom, eval₂_X, hΦbz, RingHom.id_apply]
  let e : 𝓛 ⧸ 𝕀 ≃+* TQ := RingEquiv.ofRingHom Φb Ψ h2 h1
  -- `Q ≠ ⊥`: otherwise `k[X][1/h] → k(X)` would be onto, as `P` is maximal.
  have hQ0 : Q ≠ ⊥ := by
    intro hQ0
    have hh0 : h ≠ 0 := by
      rintro rfl
      simp at hβh
    set p : k[X] := X * h + 1
    have hpdeg : p.natDegree = h.natDegree + 1 := by
      rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp [natDegree_X_mul hh0]
    have hp0 : p ≠ 0 := fun hp ↦ by simp [hp] at hpdeg
    have hpQ : p ∉ Q := by rw [hQ0]; exact hp0
    have hpu : IsUnit (algebraMap k[X] TQ p) :=
      IsLocalization.map_units TQ (⟨p, hpQ⟩ : Q.primeCompl)
    -- the class of `p⁻¹` comes from `R`
    obtain ⟨l, hl⟩ := Ideal.Quotient.mk_surjective (Ψ ↑hpu.unit⁻¹)
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.primeCompl l
    obtain ⟨s', hs'⟩ : ∃ s', s.1 * s' - 1 ∈ P := by
      obtain ⟨s', i, hi, he⟩ := Ideal.IsMaximal.exists_inv (I := P) inferInstance s.2
      exact ⟨s', by rw [show s.1 * s' - 1 = -i by rw [← he]; ring]; exact P.neg_mem hi⟩
    have hmem : l - algebraMap R 𝓛 (r * s') ∈ maximalIdeal 𝓛 := by
      have : l - algebraMap R 𝓛 (r * s') = -(l * algebraMap R 𝓛 (s.1 * s' - 1)) := by
        rw [map_sub, map_mul, map_one, map_mul, ← hrs]; ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_left _ _
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff 𝓛 P _).2 hs'))
    have hmem' :
        Φb (Ideal.Quotient.mk 𝕀 (l - algebraMap R 𝓛 (r * s'))) ∈ maximalIdeal TQ := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := (hu.map Ψ)
      rw [← RingHom.comp_apply, h1, RingHom.id_apply] at this
      exact (mem_maximalIdeal _).1 hmem (isUnit_of_isUnit_mk hIm this)
    have hmax : maximalIdeal TQ = ⊥ := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q TQ, Ideal.map_eq_bot_iff_le_ker]
      intro q hq
      rw [show q = 0 by simpa [hQ0] using hq, RingHom.mem_ker, map_zero]
    rw [hmax, Ideal.mem_bot, map_sub, map_sub, hl, ← RingHom.comp_apply Φb Ψ, h2,
      RingHom.id_apply, hΦb,
      sub_eq_zero] at hmem'
    -- so `p⁻¹ = ι (γ (r s'))`; clear denominators in `k[X][1/h]`
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers h) (γ (r * s'))
    have ha' : α (r * s') * algebraMap k[X] TQ (h ^ n) = algebraMap k[X] TQ a := by
      have := congrArg ι ha
      rw [map_mul, hι, hι] at this
      exact this
    rw [← hmem'] at ha'
    have hpa : algebraMap k[X] TQ (h ^ n) = algebraMap k[X] TQ (a * p) := by
      have hinv : (↑hpu.unit⁻¹ : TQ) * algebraMap k[X] TQ p = 1 := hpu.val_inv_mul
      rw [map_mul]
      linear_combination algebraMap k[X] TQ p * ha' - algebraMap k[X] TQ (h ^ n) * hinv
    have hdvd : p ∣ h ^ n :=
      ⟨a, by rw [IsLocalization.injective TQ Q.primeCompl_le_nonZeroDivisors hpa, mul_comm]⟩
    have hcop : IsCoprime p (h ^ n) := IsCoprime.pow_right ⟨1, -X, by ring⟩
    have := natDegree_eq_zero_of_isUnit (hcop.isUnit_of_dvd' dvd_rfl hdvd)
    omega
  haveI : IsDiscreteValuationRing TQ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X] hQ0 TQ
  exact exists_regular_pair_of_quotient_equiv hxL0 hxLm e

end Chart


end TateNodeRegular

/-! ### The Tate node chart -/

namespace TateTwoChartNode

open TateNodeRegular TateTwoChart KummerEtale

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {b₄ b₆ ϖ ε : O} {m : ℕ} {B : Type u} [CommRing B]

local notation "ιN" => algebraMap O (NR b₄ b₆ ϖ m ε)

/-- Ring maps out of the node chart agreeing on `O`, `u`, `v`, `S` are equal. -/
lemma ringHom_ext_NR {f g : (NR b₄ b₆ ϖ m ε) →+* B} (hO : ∀ o, f (ιN o) = g (ιN o))
    (hu : f (uR b₄ b₆ ϖ m ε) = g (uR b₄ b₆ ϖ m ε)) (hv : f (vR b₄ b₆ ϖ m ε) = g (vR b₄ b₆ ϖ m ε))
    (hS : f (SR b₄ b₆ ϖ m ε) = g (SR b₄ b₆ ϖ m ε)) : f = g := by
  letI : Algebra O B := (g.comp (algebraMap O (NR b₄ b₆ ϖ m ε))).toAlgebra
  let f' : (NR b₄ b₆ ϖ m ε) →ₐ[O] B := { f with commutes' := hO }
  let g' : (NR b₄ b₆ ϖ m ε) →ₐ[O] B := { g with commutes' := fun _ ↦ rfl }
  have := algHom_ext_NR (f := f') (g := g') hu hv hS
  ext r
  exact AlgHom.congr_fun this r

variable (φ : (NR b₄ b₆ ϖ m ε) →+* B)

lemma map_uR_mul_vR (hϖ0 : φ (ιN ϖ) = 0) (hm : 1 ≤ m) :
    φ (uR b₄ b₆ ϖ m ε) * φ (vR b₄ b₆ ϖ m ε) = 0 := by
  rw [← map_mul, uR_mul_vR, map_pow, hϖ0, zero_pow (by omega)]

lemma map_SR_sq : φ (SR b₄ b₆ ϖ m ε) ^ 2 + φ (SR b₄ b₆ ϖ m ε) =
    φ (ιN ε) * (1 + φ (ιN b₄) * φ (uR b₄ b₆ ϖ m ε) ^ 2) * φ (vR b₄ b₆ ϖ m ε) +
      φ (ιN b₆) * φ (uR b₄ b₆ ϖ m ε) ^ 2 := by
  have h := congrArg φ (SR_sq b₄ b₆ ϖ m ε)
  rw [algebraMap_cN] at h
  simpa only [map_add, map_mul, map_pow, map_one] using h

lemma isUnit_map_D : IsUnit (1 + φ (ιN b₄) * φ (uR b₄ b₆ ϖ m ε) ^ 2) := by
  have := (isUnit_D_node (b₄ := b₄) (b₆ := b₆) (ϖ := ϖ) (m := m) (ε := ε)).map φ
  simpa only [map_add, map_mul, map_pow, map_one] using this

variable (θ) in
/-- `O → B` killing `ϖ` factors through the residue field `k = O/(ϖ)`. -/
def residueFieldLift (g : O →+* B) (hg : g ϖ = 0) (hθ : Function.Surjective θ)
    (hker : RingHom.ker θ = Ideal.span {ϖ}) : k →+* B :=
  (Ideal.Quotient.lift (RingHom.ker θ) g fun a ha ↦ by
      rw [hker] at ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hg, mul_zero]).comp
    (RingHom.quotientKerEquivOfSurjective hθ).symm.toRingHom

lemma residueFieldLift_θ (g : O →+* B) (hg : g ϖ = 0) (hθ : Function.Surjective θ)
    (hker : RingHom.ker θ = Ideal.span {ϖ}) (o : O) :
    residueFieldLift θ g hg hθ hker (θ o) = g o := by
  have : (RingHom.quotientKerEquivOfSurjective hθ).symm (θ o) = Ideal.Quotient.mk _ o := by
    rw [RingEquiv.symm_apply_eq, RingHom.quotientKerEquivOfSurjective_apply_mk]
  simp only [residueFieldLift, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, this, Ideal.Quotient.lift_mk]

variable {φ}

/-- **Chart data from a map `k[X][1/h] → B` inverse to a map out of the node chart.** -/
lemma chartData_of_liftNR {c : k →+* B} (hc : ∀ o, c (θ o) = φ (ιN o))
    (hθ : Function.Surjective θ) (hθϖ : θ ϖ = 0) {P : Ideal (NR b₄ b₆ ϖ m ε)} {εi : O}
    (hεi : εi * ε = 1)
    (z : B) {h : k[X]} (hβh : IsUnit (eval₂RingHom c z h)) [Algebra O (Localization.Away h)]
    (halg : ∀ o, algebraMap O (Localization.Away h) o = algebraMap k[X] _ (C (θ o)))
    {s w : Localization.Away h} (hch : ChartEq (ε * ϖ ^ m) b₄ b₆ s w)
    (hD : IsUnit (1 + algebraMap O _ b₄ * w ^ 2))
    (hu : IsLocalization.Away.lift (S := Localization.Away h) h hβh w = φ (uR b₄ b₆ ϖ m ε))
    (hv : IsLocalization.Away.lift (S := Localization.Away h) h hβh (vVal b₄ b₆ εi s w hD) =
      φ (vR b₄ b₆ ϖ m ε))
    (hS : IsLocalization.Away.lift (S := Localization.Away h) h hβh s = φ (SR b₄ b₆ ϖ m ε))
    {r₀ r₁ r₂ : (NR b₄ b₆ ϖ m ε)} (hr₂ : r₂ ∉ P) (hz : z * φ r₂ = φ r₁ - φ r₀)
    (hγz : ∀ γ' : (NR b₄ b₆ ϖ m ε) →ₐ[O] Localization.Away h, γ' (SR b₄ b₆ ϖ m ε) = s →
      γ' (uR b₄ b₆ ϖ m ε) = w → (∀ o, γ' (ιN o) = algebraMap O _ o) →
      γ' r₁ - γ' r₀ = algebraMap k[X] _ X * γ' r₂) :
    ChartData φ (ιN ϖ) P c := by
  set γ := liftNR hεi rfl hch hD
  have hγO : ∀ o, γ (ιN o) = algebraMap k[X] _ (C (θ o)) := fun o ↦ by
    rw [AlgHom.commutes, halg]
  refine ⟨z, h, hβh, γ.toRingHom, r₀, r₁, r₂, ?_, ?_, fun a ↦ ?_, hr₂, hz,
    hγz γ (liftNR_SR ..) (liftNR_uR ..) fun o ↦ γ.commutes o⟩
  · change γ (ιN ϖ) = 0
    rw [hγO, hθϖ, map_zero, map_zero]
  · have : (IsLocalization.Away.lift (S := Localization.Away h) h hβh).comp γ.toRingHom = φ := by
      refine ringHom_ext_NR (fun o ↦ ?_) ?_ ?_ ?_
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hγO,
          IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_C, hc]
      · simpa [γ, liftNR_uR] using hu
      · simpa [γ, liftNR_vR] using hv
      · simpa [γ, liftNR_SR] using hS
    exact fun r ↦ RingHom.congr_fun this r
  · obtain ⟨o, rfl⟩ := hθ a
    exact ⟨ιN o, hc o, hγO o⟩

/-- **Chart data at a point of the `v`-branch** (`v` invertible): there `u = 0` and
`S² + S = ε v`, and the special fibre is `k[X]` (`S ↦ X`, `u ↦ 0`, `v ↦ (X² + X)/ε`). -/
lemma chartData_V {c : k →+* B} (hc : ∀ o, c (θ o) = φ (ιN o)) (hθ : Function.Surjective θ)
    (hθϖ : θ ϖ = 0) (hϖ0 : φ (ιN ϖ) = 0) (hm : 1 ≤ m) {P : Ideal (NR b₄ b₆ ϖ m ε)} (hP : P ≠ ⊤)
    {εi : O}
    (hεi : εi * ε = 1) (hv : IsUnit (φ (vR b₄ b₆ ϖ m ε))) : ChartData φ (ιN ϖ) P c := by
  have hu0 : φ (uR b₄ b₆ ϖ m ε) = 0 := by
    have := map_uR_mul_vR φ hϖ0 hm
    calc φ (uR b₄ b₆ ϖ m ε) = φ (uR b₄ b₆ ϖ m ε) * φ (vR b₄ b₆ ϖ m ε) * ↑hv.unit⁻¹ := by
          rw [mul_assoc, hv.mul_val_inv, mul_one]
      _ = 0 := by rw [this, zero_mul]
  have hR := map_SR_sq φ (b₄ := b₄) (b₆ := b₆) (ϖ := ϖ) (m := m) (ε := ε)
  rw [hu0] at hR
  have hεB : φ (ιN εi) * φ (ιN ε) = 1 := by rw [← map_mul, ← map_mul, hεi, map_one, map_one]
  have hβh : IsUnit (eval₂RingHom c (φ (SR b₄ b₆ ϖ m ε)) 1) := by
    rw [map_one]; exact isUnit_one
  letI : Algebra O (Localization.Away (1 : k[X])) :=
    ((algebraMap k[X] (Localization.Away (1 : k[X]))).comp (C.comp θ)).toAlgebra
  have halg : ∀ o, algebraMap O (Localization.Away (1 : k[X])) o =
      algebraMap k[X] _ (C (θ o)) := fun _ ↦ rfl
  have hπ : algebraMap O (Localization.Away (1 : k[X])) (ε * ϖ ^ m) = 0 := by
    rw [halg, map_mul, map_pow, hθϖ, zero_pow (by omega), mul_zero, map_zero, map_zero]
  have hch : ChartEq (ε * ϖ ^ m) b₄ b₆ (algebraMap k[X] (Localization.Away (1 : k[X])) X) 0 := by
    unfold ChartEq; rw [hπ]; ring
  have hD : IsUnit (1 + algebraMap O (Localization.Away (1 : k[X])) b₄ * 0 ^ 2) := by simp
  have hΨO : ∀ o, IsLocalization.Away.lift (S := Localization.Away (1 : k[X])) 1 hβh
      (algebraMap O _ o) = φ (ιN o) := fun o ↦ by
    rw [halg, IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_C, hc]
  have hΨX : IsLocalization.Away.lift (S := Localization.Away (1 : k[X])) 1 hβh
      (algebraMap k[X] _ X) = φ (SR b₄ b₆ ϖ m ε) := by
    rw [IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_X]
  refine chartData_of_liftNR hc hθ hθϖ hεi (φ (SR b₄ b₆ ϖ m ε)) hβh halg hch hD ?_ ?_ hΨX
    (r₀ := ιN ϖ) (r₁ := SR b₄ b₆ ϖ m ε) (r₂ := 1)
    (fun h1 ↦ hP ((Ideal.eq_top_iff_one _).2 h1)) (by rw [map_one, mul_one, hϖ0, sub_zero])
    fun γ' h1 _ h3 ↦ by rw [h1, h3, map_one, mul_one, halg, hθϖ, map_zero, map_zero, sub_zero]
  · rw [map_zero, hu0]
  · have hd := congrArg (IsLocalization.Away.lift (S := Localization.Away (1 : k[X])) 1 hβh)
      hD.mul_val_inv
    simp only [map_mul, map_add, map_pow, map_one, map_zero, hΨO] at hd
    simp only [vVal, map_mul, map_add, map_sub, map_pow, map_zero, hΨO, hΨX]
    linear_combination φ (ιN εi) * IsLocalization.Away.lift (S := Localization.Away (1 : k[X])) 1
        hβh ↑hD.unit⁻¹ * hR + φ (vR b₄ b₆ ϖ m ε) * IsLocalization.Away.lift
        (S := Localization.Away (1 : k[X])) 1 hβh ↑hD.unit⁻¹ * hεB + φ (vR b₄ b₆ ϖ m ε) * hd

/-- **Chart data at a point of the `u`-branch** (`u` and `S − s₀` invertible, `s₀² + s₀ = 0`):
there `v = 0` and `S² + S = b₆ u²`, and with `X = (S − s₀)/u` the special fibre is `k[X]`
localized at `h = X (b₆ − X²) ((b₆ − X²)² + b₄ X²)` (`u ↦ τ X/(b₆ − X²)`,
`S ↦ s₀ + τ X²/(b₆ − X²)`, `τ = 1 + 2 s₀`). -/
lemma chartData_U {c : k →+* B} (hc : ∀ o, c (θ o) = φ (ιN o)) (hθ : Function.Surjective θ)
    (hθϖ : θ ϖ = 0) (hϖ0 : φ (ιN ϖ) = 0) (hm : 1 ≤ m) {P : Ideal (NR b₄ b₆ ϖ m ε)} {εi : O}
    (hεi : εi * ε = 1) {s₀ : O} (hs₀ : s₀ ^ 2 + s₀ = 0) (huP : uR b₄ b₆ ϖ m ε ∉ P)
    (hu : IsUnit (φ (uR b₄ b₆ ϖ m ε))) (hS : IsUnit (φ (SR b₄ b₆ ϖ m ε - ιN s₀))) :
    ChartData φ (ιN ϖ) P c := by
  rw [map_sub] at hS
  have hv0 : φ (vR b₄ b₆ ϖ m ε) = 0 := by
    have := map_uR_mul_vR φ hϖ0 hm
    calc φ (vR b₄ b₆ ϖ m ε) = ↑hu.unit⁻¹ * (φ (uR b₄ b₆ ϖ m ε) * φ (vR b₄ b₆ ϖ m ε)) := by
          rw [← mul_assoc, hu.val_inv_mul, one_mul]
      _ = 0 := by rw [this, mul_zero]
  have hR : φ (SR b₄ b₆ ϖ m ε) ^ 2 + φ (SR b₄ b₆ ϖ m ε) =
      φ (ιN b₆) * φ (uR b₄ b₆ ϖ m ε) ^ 2 := by
    have := map_SR_sq φ (b₄ := b₄) (b₆ := b₆) (ϖ := ϖ) (m := m) (ε := ε)
    rw [hv0] at this
    linear_combination this
  have hs₀B : φ (ιN s₀) ^ 2 + φ (ιN s₀) = 0 := by
    rw [← map_pow, ← map_pow, ← map_add, ← map_add, hs₀, map_zero, map_zero]
  obtain ⟨z, hzdef⟩ : ∃ z, z = (φ (SR b₄ b₆ ϖ m ε) - φ (ιN s₀)) * ↑hu.unit⁻¹ := ⟨_, rfl⟩
  have hzu : z * φ (uR b₄ b₆ ϖ m ε) = φ (SR b₄ b₆ ϖ m ε) - φ (ιN s₀) := by
    rw [hzdef, mul_assoc, hu.val_inv_mul, mul_one]
  obtain ⟨h, hh⟩ : ∃ h : k[X],
      h = X * (C (θ b₆) - X ^ 2) * ((C (θ b₆) - X ^ 2) ^ 2 + C (θ b₄) * X ^ 2) := ⟨_, rfl⟩
  have hβh : IsUnit (eval₂RingHom c z h) := by
    have := isUnit_U (b₄ := φ (ιN b₄)) (b₆ := φ (ιN b₆)) hs₀B hu hS (isUnit_map_D φ) hzu hR
    rw [hh]
    simpa only [coe_eval₂RingHom, eval₂_mul, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
      eval₂_C, hc] using this
  letI : Algebra O (Localization.Away h) :=
    ((algebraMap k[X] (Localization.Away h)).comp (C.comp θ)).toAlgebra
  have halg : ∀ o, algebraMap O (Localization.Away h) o = algebraMap k[X] _ (C (θ o)) :=
    fun _ ↦ rfl
  obtain ⟨Xt, hXt⟩ : ∃ Xt, Xt = algebraMap k[X] (Localization.Away h) X := ⟨_, rfl⟩
  obtain ⟨Hi, hHi⟩ : ∃ Hi, Hi = IsLocalization.Away.invSelf (S := Localization.Away h) h :=
    ⟨_, rfl⟩
  have hH : Xt * (algebraMap O _ b₆ - Xt ^ 2) *
      ((algebraMap O _ b₆ - Xt ^ 2) ^ 2 + algebraMap O _ b₄ * Xt ^ 2) * Hi = 1 := by
    have := IsLocalization.Away.mul_invSelf (S := Localization.Away h) h
    have hmap := congrArg (algebraMap k[X] (Localization.Away h)) hh
    simp only [map_mul, map_sub, map_add, map_pow, ← halg, ← hXt] at hmap
    rwa [← hHi, hmap] at this
  have hs₀T : algebraMap O (Localization.Away h) s₀ ^ 2 + algebraMap O _ s₀ = 0 := by
    rw [← map_pow, ← map_add, hs₀, map_zero]
  obtain ⟨w, hw⟩ : ∃ w, w = wU (algebraMap O (Localization.Away h) b₄)
      (algebraMap O (Localization.Away h) b₆) (algebraMap O (Localization.Away h) s₀) Xt Hi :=
    ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = sU (algebraMap O (Localization.Away h) b₄)
      (algebraMap O (Localization.Away h) b₆) (algebraMap O (Localization.Away h) s₀) Xt Hi :=
    ⟨_, rfl⟩
  have hq : s ^ 2 + s - algebraMap O _ b₆ * w ^ 2 = 0 := by
    rw [hw, hs]; exact sU_sq hs₀T hH
  have hπ : algebraMap O (Localization.Away h) (ε * ϖ ^ m) = 0 := by
    rw [halg, map_mul, map_pow, hθϖ, zero_pow (by omega), mul_zero, map_zero, map_zero]
  have hch : ChartEq (ε * ϖ ^ m) b₄ b₆ s w := by
    unfold ChartEq; rw [hq, hπ, mul_zero, zero_mul]
  have hD : IsUnit (1 + algebraMap O (Localization.Away h) b₄ * w ^ 2) := by
    rw [hw]; exact IsUnit.of_mul_eq_one _ (wU_D hs₀T hH)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = IsLocalization.Away.lift (S := Localization.Away h) h hβh :=
    ⟨_, rfl⟩
  have hΨO : ∀ o, Ψ (algebraMap O _ o) = φ (ιN o) := fun o ↦ by
    rw [hΨ, halg, IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_C, hc]
  have hΨX : Ψ Xt = z := by
    rw [hΨ, hXt, IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_X]
  have hhi :
      z * (φ (ιN b₆) - z ^ 2) * ((φ (ιN b₆) - z ^ 2) ^ 2 + φ (ιN b₄) * z ^ 2) * Ψ Hi = 1 := by
    have := congrArg Ψ hH
    simpa only [map_mul, map_sub, map_add, map_pow, map_one, hΨO, hΨX] using this
  have hΨw : Ψ w = φ (uR b₄ b₆ ϖ m ε) := by
    rw [show Ψ w = wU (φ (ιN b₄)) (φ (ιN b₆)) (φ (ιN s₀)) z (Ψ Hi) by
      simp only [hw, wU, eiU, map_mul, map_add, map_sub, map_pow, map_one, map_ofNat, hΨO, hΨX]]
    exact wU_eq hs₀B hu hzu hR hhi
  have hΨs : Ψ s = φ (SR b₄ b₆ ϖ m ε) := by
    rw [show Ψ s = sU (φ (ιN b₄)) (φ (ιN b₆)) (φ (ιN s₀)) z (Ψ Hi) by
      simp only [hs, sU, eiU, map_mul, map_add, map_sub, map_pow, map_one, map_ofNat, hΨO, hΨX]]
    exact sU_eq hs₀B hu hzu hR hhi
  subst hΨ
  refine chartData_of_liftNR hc hθ hθϖ hεi z hβh halg hch hD hΨw ?_ hΨs huP
    (r₀ := ιN s₀) (r₁ := SR b₄ b₆ ϖ m ε) hzu fun γ' h1 h2 h3 ↦ ?_
  · change IsLocalization.Away.lift (S := Localization.Away h) h hβh
      ((s ^ 2 + s - algebraMap O _ b₆ * w ^ 2) * algebraMap O _ εi * ↑hD.unit⁻¹) = _
    rw [hq, zero_mul, zero_mul, map_zero, hv0]
  · rw [h1, h2, h3, hs, hw, sU, wU, hXt]
    ring

/-! ### Regularity away from the nodes -/

/-- **Chart data away from the nodes**: for a ring map `φ` out of the node chart killing `ϖ` and
inverting everything outside a maximal ideal `P ∌ u + v`, there is chart data at `P`. -/
lemma chartData_of_not_mem (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    (hm : 1 ≤ m) (hε : IsUnit ε) {P : Ideal (NR b₄ b₆ ϖ m ε)} (hP : P.IsMaximal)
    (hf : uR b₄ b₆ ϖ m ε + vR b₄ b₆ ϖ m ε ∉ P) (hϖ0 : φ (ιN ϖ) = 0)
    (hunit : ∀ r ∉ P, IsUnit (φ r)) :
    ChartData φ (ιN ϖ) P
      (residueFieldLift θ (φ.comp (algebraMap O (NR b₄ b₆ ϖ m ε))) hϖ0 hθ hker) := by
  have hθϖ : θ ϖ = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ϖ
  obtain ⟨εi, hεi⟩ : ∃ εi, εi * ε = 1 := ⟨↑hε.unit⁻¹, hε.val_inv_mul⟩
  have hc : ∀ o, residueFieldLift θ (φ.comp (algebraMap O (NR b₄ b₆ ϖ m ε))) hϖ0 hθ hker (θ o) =
      φ (ιN o) := residueFieldLift_θ _ _ _ _
  by_cases hv : vR b₄ b₆ ϖ m ε ∈ P
  · have hu : uR b₄ b₆ ϖ m ε ∉ P := fun hu ↦ hf (P.add_mem hu hv)
    by_cases hS : SR b₄ b₆ ϖ m ε ∈ P
    · refine chartData_U hc hθ hθϖ hϖ0 hm hεi (s₀ := -1) (by ring) hu (hunit _ hu)
        (hunit _ fun h1 ↦ hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_))
      have := P.sub_mem h1 hS
      rwa [map_neg, map_one, sub_neg_eq_add, add_sub_cancel_left] at this
    · exact chartData_U hc hθ hθϖ hϖ0 hm hεi (s₀ := 0) (by ring) hu (hunit _ hu)
        (hunit _ (by rwa [map_zero, sub_zero]))
  · exact chartData_V hc hθ hθϖ hϖ0 hm hP.ne_top hεi (hunit _ hv)

/-- **The Tate node chart is regular at the closed points of the special fibre other than the
two nodes** (MR12 S5.2): if `P` is a maximal ideal of `NR` containing `ϖ` but not `f = u + v`,
then `ϖ` is prime in `NR_P` and `𝔪_P = (ϖ, y)` with `y ∉ (ϖ)`. Valid in every residue
characteristic. -/
theorem exists_regular_pair [IsDomain O] [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ)
    (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hm : 1 ≤ m)
    (hε : IsUnit ε) (P : Ideal (NR b₄ b₆ ϖ m ε)) [hP : P.IsMaximal]
    (hϖP : algebraMap O _ ϖ ∈ P) (hf : uR b₄ b₆ ϖ m ε + vR b₄ b₆ ϖ m ε ∉ P) :
    ∃ y : Localization.AtPrime P, Prime (algebraMap O (Localization.AtPrime P) ϖ) ∧
      y ∉ Ideal.span {algebraMap O (Localization.AtPrime P) ϖ} ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap O (Localization.AtPrime P) ϖ, y} := by
  haveI := isDomain_NR b₄ b₆ hϖ.prime hm hε
  have := exists_regular_pair_of_chartData (algebraMap_ϖ_NR_ne_zero hϖ.prime hm hε) hϖP _
    (chartData_of_not_mem (φ := (Ideal.Quotient.mk _).comp
        (algebraMap (NR b₄ b₆ ϖ m ε) (Localization.AtPrime P))) hθ hker hm hε hP hf
      (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
      fun r hr ↦ (IsLocalization.map_units (Localization.AtPrime P) (⟨r, hr⟩ : P.primeCompl)).map
        (Ideal.Quotient.mk _))
  rwa [IsScalarTower.algebraMap_apply O (NR b₄ b₆ ϖ m ε) (Localization.AtPrime P)]

end

end TateTwoChartNode

end SemistableReduction
