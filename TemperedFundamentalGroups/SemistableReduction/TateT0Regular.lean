/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateT1Regular
import TemperedFundamentalGroups.SemistableReduction.NormalLocalCriterion
import TemperedFundamentalGroups.SemistableReduction.TateGlue0
import TemperedFundamentalGroups.SemistableReduction.CuspInput

/-!
# Regularity and normality of the Tate chart `T0` over `D(1 + h)` (MR12 S5.2)

Let `O` be a DVR with uniformizer `ϖ` and residue field `k` (`θ : O → k` onto, `ker θ = (ϖ)`),
`π = ε ϖᵐ` (`m ≥ 1`, `ε` a unit), `κ (t² − b₆) = 1`, `b₆` a unit, and
`T0 = O[h][z]/(G₀)` the chart `ℓ₀ ≠ 0` of the Tate model (`TateTwoChart.T0`), with relation
`z³ + κ (2t + (t − π b₄) h) z² + κ (1 + h) z − κ π h³ = 0` (`TateTwoChart.eq0`). Let
`Rc = T0[1/(1 + h)]` (`CuspTower.Rc`, `TateGlue0.c0`).

* `TateTwoChart.liftT0`, `TateTwoChart.ringHom_ext_T0`: maps out of `T0`.
* **`TateTwoChart.isDomain_T0`**, **`TateTwoChart.isDomain_Rc`**.
* **`TateTwoChart.exists_regular_pair_T0`**, **`TateTwoChart.exists_regular_pair_Rc`**: at a
  maximal ideal `P` containing `ϖ` (and not `1 + h`), `ϖ` is prime in the local ring and
  `𝔪_P = (ϖ, y)` with `y ∉ (ϖ)`, in every residue characteristic.
* **`TateTwoChart.isIntegrallyClosed_Rc`**: `Rc` is integrally closed.

Method (`TateNodeRegular.exists_regular_pair_of_chartData`): modulo `ϖ` the relation becomes
`z Q = 0` with `Q = z² + κ t (2 + h) z + κ (1 + h) = κ (t z + 1) h + (z² + 2κ t z + κ)`.
* `z ∈ P`: then `Q ≡ κ (1 + h)` is a unit at `P`, so `z = 0` on the special fibre, which is the
  line `k[X][1/(1 + X)]` (`h ↦ X`, `z ↦ 0`; `chartData_line`).
* `z ∉ P`: then `Q = 0` at `P`. From `κ b₆ = (t z + 1) W − t² Q` (with `W` explicit) and `b₆` a
  unit, `t z + 1` is a unit at `P`; and `z (z + κ t) = −κ (t z + 1) (1 + h) + Q`. The special
  fibre is the conic chart `k[X][1/((tX + 1) X (X + κ t))]` (`z ↦ X`,
  `h ↦ −(t² − b₆)(X² + 2κ t X + κ)/(tX + 1)`, using `κ⁻¹ = t² − b₆`; `chartData_conic`).

The charts are built for an arbitrary localization `R` of `T0` at a submonoid of the powers of
`1 + h` (this covers `T0` itself and `Rc`). Normality of `Rc`: local criterion
(`NormalLocal.isIntegrallyClosed_atPrime_of_away`) with the Dedekind domain `T0[1/ϖ]`
(`TateTwoChart.isDedekindDomain_away_T0_of_dvr`) at the primes of `T0` below the maximal ideals
of `Rc`.
-/

universe u

open Polynomial IsLocalRing

namespace SemistableReduction

namespace TateTwoChart

/-! ### Maps out of `T0` -/

section Lift

variable {O : Type u} [CommRing O] {π b₄ t κ : O} {S : Type u} [CommRing S] [Algebra O S]

/-- The relation of the chart `T0` for values `h ↦ a`, `z ↦ b`. -/
def Rel0 (π b₄ t κ : O) (a b : S) : Prop :=
  b ^ 3 + algebraMap O S κ * (algebraMap O S (2 * t) + algebraMap O S (t - π * b₄) * a) * b ^ 2 +
    algebraMap O S κ * (1 + a) * b - algebraMap O S (κ * π) * a ^ 3 = 0

lemma eval_G0_of {a b : S} (h : Rel0 π b₄ t κ a b) :
    (G0 π b₄ t κ).eval₂ ((Polynomial.aeval a : O[X] →ₐ[O] S) : O[X] →+* S) b = 0 := by
  unfold Rel0 at h
  simp only [G0, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_one,
    RingHom.coe_coe, map_mul, map_add, map_one, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  simp only [map_mul, map_sub, map_ofNat] at h ⊢
  linear_combination h

/-- **Maps out of `T0`**: `h ↦ a`, `z ↦ b` for `a, b` satisfying the relation of `T0`. -/
noncomputable def liftT0 (a b : S) (h : Rel0 π b₄ t κ a b) : T0 π b₄ t κ →ₐ[O] S :=
  AdjoinRoot.liftAlgHom (G0 π b₄ t κ) (Polynomial.aeval a) b (eval_G0_of h)

lemma liftT0_h0 (a b : S) (h : Rel0 π b₄ t κ a b) : liftT0 a b h (h0 π b₄ t κ) = a := by
  simp [liftT0]

lemma liftT0_z0 (a b : S) (h : Rel0 π b₄ t κ a b) : liftT0 a b h (z0 π b₄ t κ) = b := by
  simp [liftT0]

/-- Ring maps out of `T0` agreeing on `O`, `h` and `z` are equal. -/
lemma ringHom_ext_T0 {B : Type*} [CommRing B] {f g : T0 π b₄ t κ →+* B}
    (hO : ∀ o, f (algebraMap O _ o) = g (algebraMap O _ o))
    (hh : f (h0 π b₄ t κ) = g (h0 π b₄ t κ)) (hz : f (z0 π b₄ t κ) = g (z0 π b₄ t κ)) :
    f = g := by
  letI : Algebra O B := (g.comp (algebraMap O (T0 π b₄ t κ))).toAlgebra
  let f' : T0 π b₄ t κ →ₐ[O] B := { f with commutes' := hO }
  let g' : T0 π b₄ t κ →ₐ[O] B := { g with commutes' := fun _ ↦ rfl }
  have : f' = g' := AdjoinRoot.algHom_ext' (Polynomial.algHom_ext hh) hz
  exact RingHom.ext fun r ↦ AlgHom.congr_fun this r

end Lift

/-! ### `T0` and `Rc` are domains -/

section Domain

variable {O : Type u} [CommRing O] {π b₄ t κ : O}

private lemma natDegree_G0' [Nontrivial O] : (G0 π b₄ t κ).natDegree = 3 := by
  unfold G0
  compute_degree!

lemma algebraMap_mem_T0 [IsDomain O] {p : O[X]} (hp : p ≠ 0) :
    algebraMap O[X] (T0 π b₄ t κ) p ∈ nonZeroDivisors (T0 π b₄ t κ) := by
  have hreg : IsSMulRegular (T0 π b₄ t κ) p := (IsRegular.of_ne_zero hp).isSMulRegular
  have he : ∀ x : T0 π b₄ t κ, algebraMap O[X] (T0 π b₄ t κ) p * x = p • x := fun x ↦ by
    rw [Algebra.smul_def]
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx ↦ hreg ?_, fun x hx ↦ hreg ?_⟩
  · dsimp only
    rw [← he, hx, smul_zero]
  · dsimp only
    rw [← he, mul_comm, hx, smul_zero]

lemma algebraMap_ϖ_mem_T0 [IsDomain O] {ϖ : O} (hϖ : ϖ ≠ 0) :
    algebraMap O (T0 π b₄ t κ) ϖ ∈ nonZeroDivisors (T0 π b₄ t κ) := by
  rw [IsScalarTower.algebraMap_apply O O[X] (T0 π b₄ t κ), Polynomial.algebraMap_apply]
  exact algebraMap_mem_T0 (C_ne_zero.2 hϖ)

lemma c0_mem_T0 [IsDomain O] :
    TateGlue0.c0 π b₄ t κ ∈ nonZeroDivisors (T0 π b₄ t κ) := by
  have : TateGlue0.c0 π b₄ t κ = algebraMap O[X] (T0 π b₄ t κ) (1 + X) := by
    rw [map_add, map_one, AdjoinRoot.algebraMap_eq]
  rw [this]
  exact algebraMap_mem_T0 (by
    intro h
    have := congrArg (Polynomial.coeff · 1) h
    simp [Polynomial.coeff_one] at this)

lemma algebraMap_ϖ_T0_ne_zero [IsDomain O] {ϖ : O} (hϖ : ϖ ≠ 0) :
    algebraMap O (T0 π b₄ t κ) ϖ ≠ 0 := by
  haveI : Nontrivial (T0 π b₄ t κ) := (AdjoinRoot.of.injective_of_degree_ne_zero (f :=
    G0 π b₄ t κ) (by
    rw [degree_eq_natDegree (Monic.ne_zero (monic_G0 π b₄ t κ)), natDegree_G0']; decide)).nontrivial
  exact nonZeroDivisors.ne_zero (algebraMap_ϖ_mem_T0 hϖ)

/-- **The chart ring `T0` is a domain** over a discrete valuation ring `O`, for
`κ (t² − b₆) = 1`, `3 ≠ 0`, `π ≠ 0` and `E = tateE π b₄ b₆ ≠ 0`: it embeds into its generic
fibre `T0[1/ϖ]`, a Dedekind domain. -/
theorem isDomain_T0 [IsDomain O] [IsDiscreteValuationRing O] {b₆ ϖ : O} (hϖ : Irreducible ϖ)
    (hκ : κ * (t ^ 2 - b₆) = 1) (h3 : (3 : O) ≠ 0) (hπ0 : π ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0) : IsDomain (T0 π b₄ t κ) := by
  haveI := isDedekindDomain_away_T0_of_dvr (t := t) (κ := κ) hϖ.ne_zero hϖ.not_isUnit hκ h3 hπ0 hE
  have hinj : Function.Injective (algebraMap (T0 π b₄ t κ)
      (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))) :=
    IsLocalization.injective _ (Submonoid.powers_le.2 (algebraMap_ϖ_mem_T0 hϖ.ne_zero))
  exact hinj.isDomain _

/-- **The cusp chart `Rc = T0[1/(1 + h)]` is a domain** (under the hypotheses of
`isDomain_T0`). -/
theorem isDomain_Rc [IsDomain O] [IsDiscreteValuationRing O] {b₆ ϖ : O} (hϖ : Irreducible ϖ)
    (hκ : κ * (t ^ 2 - b₆) = 1) (h3 : (3 : O) ≠ 0) (hπ0 : π ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0) :
    IsDomain (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ)) := by
  haveI := isDomain_T0 hϖ hκ h3 hπ0 hE
  exact IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (nonZeroDivisors.ne_zero c0_mem_T0))

end Domain

/-! ### Charts of the special fibre -/

namespace TateT0Regular

open TateNodeRegular TateTwoChartNode

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {π b₄ b₆ t κ ϖ ε : O} {m : ℕ} {B : Type u} [CommRing B]
  {R : Type u} [CommRing R] [Algebra (T0 π b₄ t κ) R] {M : Submonoid (T0 π b₄ t κ)}
  [IsLocalization M R]

local notation "ιT" => algebraMap O (T0 π b₄ t κ)

local notation "ιR" => algebraMap (T0 π b₄ t κ) R

/-- `Q = z² + κ t (2 + h) z + κ (1 + h)`, the conic factor of the special fibre of `T0`. -/
def q0 (π b₄ t κ : O) : T0 π b₄ t κ :=
  z0 π b₄ t κ ^ 2 + algebraMap O _ κ * algebraMap O _ t * (2 + h0 π b₄ t κ) * z0 π b₄ t κ +
    algebraMap O _ κ * (1 + h0 π b₄ t κ)

lemma z0_mul_q0 : z0 π b₄ t κ * q0 π b₄ t κ = algebraMap O _ π * (algebraMap O _ κ *
    (algebraMap O _ b₄ * h0 π b₄ t κ * z0 π b₄ t κ ^ 2 + h0 π b₄ t κ ^ 3)) := by
  have h := eq0 π b₄ t κ
  simp only [map_mul, map_sub, map_ofNat] at h
  unfold q0
  linear_combination h

variable {φ : R →+* B}

private lemma map_π_eq_zero (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hϖ0 : φ (ιR (ιT ϖ)) = 0) :
    φ (ιR (ιT π)) = 0 := by
  simp only [hπ, map_mul, map_pow, hϖ0, zero_pow (by omega : m ≠ 0), mul_zero]

/-- Chart data from a map `γ : T0 → k[X][1/h]` with `γ (1 + h)` a unit, `γ r = X`, and
`β ∘ γ = φ` on `T0`. -/
private lemma chartData_of_lift (hM : M ≤ Submonoid.powers (TateGlue0.c0 π b₄ t κ))
    {c : k →+* B} (hθ : Function.Surjective θ) (hθϖ : θ ϖ = 0) {P : Ideal R} (hP : P ≠ ⊤)
    {h : k[X]} {r : T0 π b₄ t κ} (hβh : IsUnit (eval₂RingHom c (φ (ιR r)) h))
    (γ : T0 π b₄ t κ →+* Localization.Away h) (hγc : IsUnit (γ (TateGlue0.c0 π b₄ t κ)))
    (hγO : ∀ o, γ (ιT o) = algebraMap k[X] _ (C (θ o))) (hγr : γ r = algebraMap k[X] _ X)
    (hc : ∀ o, c (θ o) = φ (ιR (ιT o)))
    (hT : (IsLocalization.Away.lift (S := Localization.Away h) h hβh).comp γ = φ.comp ιR) :
    ChartData φ (ιR (ιT ϖ)) P c := by
  have hγM : ∀ y : M, IsUnit (γ y) := fun y ↦ by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 (hM y.2)
    rw [← hn, map_pow]
    exact hγc.pow n
  have hγR : ∀ a, IsLocalization.lift (M := M) (S := R) hγM (ιR a) = γ a :=
    IsLocalization.lift_eq hγM
  have hΨ : (IsLocalization.Away.lift (S := Localization.Away h) h hβh).comp
      (IsLocalization.lift (M := M) (S := R) hγM) = φ :=
    IsLocalization.ringHom_ext M (RingHom.ext fun a ↦ by
      simp only [RingHom.comp_apply, hγR]
      exact RingHom.congr_fun hT a)
  refine ⟨φ (ιR r), h, hβh, IsLocalization.lift (M := M) (S := R) hγM, 0, ιR r, 1, ?_,
    fun a ↦ RingHom.congr_fun hΨ a, fun a ↦ ?_, fun h1 ↦ hP ((Ideal.eq_top_iff_one _).2 h1),
    by rw [map_one, mul_one, map_zero, sub_zero], ?_⟩
  · rw [hγR, hγO, hθϖ, map_zero, map_zero]
  · obtain ⟨o, rfl⟩ := hθ a
    exact ⟨ιR (ιT o), hc o, by rw [hγR, hγO]⟩
  · rw [hγR, hγr, map_zero, map_one, sub_zero, mul_one]

/-- **Chart data on the line `z = 0`** (`Q` a unit): the special fibre is `k[X][1/(1 + X)]`,
`h ↦ X`, `z ↦ 0`. -/
lemma chartData_line (hM : M ≤ Submonoid.powers (TateGlue0.c0 π b₄ t κ)) {c : k →+* B}
    (hc : ∀ o, c (θ o) = φ (ιR (ιT o))) (hθ : Function.Surjective θ) (hθϖ : θ ϖ = 0)
    (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hϖ0 : φ (ιR (ιT ϖ)) = 0)
    (hc0 : IsUnit (φ (ιR (TateGlue0.c0 π b₄ t κ)))) {P : Ideal R} (hP : P ≠ ⊤)
    (hq : IsUnit (φ (ιR (q0 π b₄ t κ)))) : ChartData φ (ιR (ιT ϖ)) P c := by
  have hπ0 : φ (ιR (ιT π)) = 0 := map_π_eq_zero hπ hm hϖ0
  have hz : φ (ιR (z0 π b₄ t κ)) = 0 := by
    have h := congrArg (fun r ↦ φ (ιR r)) (z0_mul_q0 (π := π) (b₄ := b₄) (t := t) (κ := κ))
    simp only [map_mul, hπ0, zero_mul] at h
    exact hq.mul_left_eq_zero.1 h
  obtain ⟨h, hh⟩ : ∃ h : k[X], h = 1 + X := ⟨_, rfl⟩
  have hβh : IsUnit (eval₂RingHom c (φ (ιR (h0 π b₄ t κ))) h) := by
    rw [hh]
    simp only [TateGlue0.c0, map_add, map_one] at hc0
    simpa only [coe_eval₂RingHom, eval₂_add, eval₂_one, eval₂_X] using hc0
  letI : Algebra O (Localization.Away h) :=
    ((algebraMap k[X] (Localization.Away h)).comp (C.comp θ)).toAlgebra
  have halg : ∀ o, algebraMap O (Localization.Away h) o = algebraMap k[X] _ (C (θ o)) :=
    fun _ ↦ rfl
  have hπL : algebraMap O (Localization.Away h) π = 0 := by
    rw [congrArg (algebraMap O (Localization.Away h)) hπ, halg, map_mul, map_pow, hθϖ,
      zero_pow (by omega), mul_zero, map_zero, map_zero]
  have hrel : Rel0 π b₄ t κ (algebraMap k[X] (Localization.Away h) X) 0 := by
    unfold Rel0
    simp only [map_mul, hπL]
    ring
  set γ := liftT0 _ _ hrel
  have hγO : ∀ o, γ (ιT o) = algebraMap k[X] _ (C (θ o)) := fun o ↦ γ.commutes o
  have hΨO : ∀ o, IsLocalization.Away.lift (S := Localization.Away h) h hβh
      (algebraMap k[X] _ (C (θ o))) = φ (ιR (ιT o)) := fun o ↦ by
    rw [IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_C, hc]
  refine chartData_of_lift hM hθ hθϖ hP hβh γ.toRingHom ?_ hγO (liftT0_h0 _ _ hrel) hc
    (ringHom_ext_T0 (fun o ↦ ?_) ?_ ?_)
  · have : γ (TateGlue0.c0 π b₄ t κ) = algebraMap k[X] (Localization.Away h) h := by
      rw [TateGlue0.c0, map_add, map_one, liftT0_h0, hh, map_add, map_one]
    change IsUnit (γ (TateGlue0.c0 π b₄ t κ))
    rw [this]
    exact IsLocalization.Away.algebraMap_isUnit h
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hγO, hΨO]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, γ, liftT0_h0,
      IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_X]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, γ, liftT0_z0,
      map_zero, hz]

/-- **Chart data on the conic `Q = 0`** (`z` a unit, `b₆` a unit): the special fibre is
`k[X][1/((tX + 1) X (X + κ t))]`, `z ↦ X`, `h ↦ −(t² − b₆)(X² + 2κ t X + κ)/(tX + 1)`. -/
lemma chartData_conic (hM : M ≤ Submonoid.powers (TateGlue0.c0 π b₄ t κ))
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆) {c : k →+* B}
    (hc : ∀ o, c (θ o) = φ (ιR (ιT o))) (hθ : Function.Surjective θ) (hθϖ : θ ϖ = 0)
    (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hϖ0 : φ (ιR (ιT ϖ)) = 0)
    (hc0 : IsUnit (φ (ιR (TateGlue0.c0 π b₄ t κ)))) {P : Ideal R} (hP : P ≠ ⊤)
    (hzu : IsUnit (φ (ιR (z0 π b₄ t κ)))) : ChartData φ (ιR (ιT ϖ)) P c := by
  have hπ0 : φ (ιR (ιT π)) = 0 := map_π_eq_zero hπ hm hϖ0
  have hq : φ (ιR (z0 π b₄ t κ)) ^ 2 + φ (ιR (ιT κ)) * φ (ιR (ιT t)) *
      (2 + φ (ιR (h0 π b₄ t κ))) * φ (ιR (z0 π b₄ t κ)) +
      φ (ιR (ιT κ)) * (1 + φ (ιR (h0 π b₄ t κ))) = 0 := by
    have h := congrArg (fun r ↦ φ (ιR r)) (z0_mul_q0 (π := π) (b₄ := b₄) (t := t) (κ := κ))
    simp only [map_mul, hπ0, zero_mul] at h
    have h' := hzu.mul_right_eq_zero.1 h
    simpa only [q0, map_add, map_mul, map_pow, map_ofNat, map_one] using h'
  have hk : φ (ιR (ιT κ)) * (φ (ιR (ιT t)) ^ 2 - φ (ιR (ιT b₆))) = 1 := by
    have h := congrArg (fun o ↦ φ (ιR (ιT o))) hκ
    simpa only [map_mul, map_sub, map_pow, map_one] using h
  have hc0' : IsUnit (1 + φ (ιR (h0 π b₄ t κ))) := by
    simpa only [TateGlue0.c0, map_add, map_one] using hc0
  have hK : IsUnit (φ (ιR (ιT κ))) := IsUnit.of_mul_eq_one _ hk
  have hTz : IsUnit (φ (ιR (ιT t)) * φ (ιR (z0 π b₄ t κ)) + 1) := by
    have e : φ (ιR (ιT κ)) * φ (ιR (ιT b₆)) =
        (φ (ιR (ιT t)) * φ (ιR (z0 π b₄ t κ)) + 1) * (φ (ιR (ιT κ)) * φ (ιR (ιT t)) ^ 2 *
          φ (ιR (h0 π b₄ t κ)) + φ (ιR (ιT t)) * φ (ιR (z0 π b₄ t κ)) - 1 +
          2 * φ (ιR (ιT κ)) * φ (ιR (ιT t)) ^ 2) := by
      linear_combination (-φ (ιR (ιT t)) ^ 2) * hq - hk
    have hKb : IsUnit (φ (ιR (ιT κ)) * φ (ιR (ιT b₆))) := hK.mul ((hb₆.map ιT).map ιR |>.map φ)
    rw [e] at hKb
    exact isUnit_of_mul_isUnit_left hKb
  have hzz : IsUnit (φ (ιR (z0 π b₄ t κ)) *
      (φ (ιR (z0 π b₄ t κ)) + φ (ιR (ιT κ)) * φ (ιR (ιT t)))) := by
    rw [show φ (ιR (z0 π b₄ t κ)) * (φ (ιR (z0 π b₄ t κ)) + φ (ιR (ιT κ)) * φ (ιR (ιT t))) =
      -(φ (ιR (ιT κ)) * (φ (ιR (ιT t)) * φ (ιR (z0 π b₄ t κ)) + 1) *
        (1 + φ (ιR (h0 π b₄ t κ)))) by linear_combination hq]
    exact ((hK.mul hTz).mul hc0').neg
  obtain ⟨h, hh⟩ : ∃ h : k[X], h = (C (θ t) * X + 1) * X * (X + C (θ κ) * C (θ t)) := ⟨_, rfl⟩
  have hβh : IsUnit (eval₂RingHom c (φ (ιR (z0 π b₄ t κ))) h) := by
    rw [hh]
    simp only [coe_eval₂RingHom, eval₂_mul, eval₂_add, eval₂_one, eval₂_X, eval₂_C, hc]
    convert hTz.mul hzz using 1
    ring
  letI : Algebra O (Localization.Away h) :=
    ((algebraMap k[X] (Localization.Away h)).comp (C.comp θ)).toAlgebra
  have halg : ∀ o, algebraMap O (Localization.Away h) o = algebraMap k[X] _ (C (θ o)) :=
    fun _ ↦ rfl
  have hπL : algebraMap O (Localization.Away h) π = 0 := by
    rw [congrArg (algebraMap O (Localization.Away h)) hπ, halg, map_mul, map_pow, hθϖ,
      zero_pow (by omega), mul_zero, map_zero, map_zero]
  obtain ⟨Xt, hXt⟩ : ∃ Xt, Xt = algebraMap k[X] (Localization.Away h) X := ⟨_, rfl⟩
  obtain ⟨Hi, hHi⟩ : ∃ Hi, Hi = IsLocalization.Away.invSelf (S := Localization.Away h) h :=
    ⟨_, rfl⟩
  obtain ⟨tL, htL⟩ : ∃ tL, tL = algebraMap O (Localization.Away h) t := ⟨_, rfl⟩
  obtain ⟨κL, hκL⟩ : ∃ κL, κL = algebraMap O (Localization.Away h) κ := ⟨_, rfl⟩
  obtain ⟨bL, hbL⟩ : ∃ bL, bL = algebraMap O (Localization.Away h) b₆ := ⟨_, rfl⟩
  have hH : (tL * Xt + 1) * Xt * (Xt + κL * tL) * Hi = 1 := by
    have := IsLocalization.Away.mul_invSelf (S := Localization.Away h) h
    have hmap := congrArg (algebraMap k[X] (Localization.Away h)) hh
    simp only [map_mul, map_add, map_one, ← halg, ← hXt, ← htL, ← hκL] at hmap
    rw [← hHi, hmap] at this
    exact this
  have hkL : κL * (tL ^ 2 - bL) = 1 := by
    rw [hκL, htL, hbL, ← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  obtain ⟨aH, haH⟩ : ∃ aH, aH = -((tL ^ 2 - bL) * (Xt ^ 2 + 2 * κL * tL * Xt + κL) * Xt *
      (Xt + κL * tL) * Hi) := ⟨_, rfl⟩
  have hrel : Rel0 π b₄ t κ aH Xt := by
    unfold Rel0
    simp only [map_mul, map_sub, map_ofNat, hπL, ← htL, ← hκL]
    rw [haH]
    linear_combination (-(Xt * (Xt ^ 2 + 2 * κL * tL * Xt + κL))) * hkL -
      Xt * (Xt ^ 2 + 2 * κL * tL * Xt + κL) * (κL * (tL ^ 2 - bL)) * hH
  set γ := liftT0 _ _ hrel
  have hγO : ∀ o, γ (ιT o) = algebraMap k[X] _ (C (θ o)) := fun o ↦ γ.commutes o
  have hΨO : ∀ o, IsLocalization.Away.lift (S := Localization.Away h) h hβh
      (algebraMap O _ o) = φ (ιR (ιT o)) := fun o ↦ by
    rw [halg, IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_C, hc]
  have hΨX : IsLocalization.Away.lift (S := Localization.Away h) h hβh Xt =
      φ (ιR (z0 π b₄ t κ)) := by
    rw [hXt, IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_X]
  have hhi : (φ (ιR (ιT t)) * φ (ιR (z0 π b₄ t κ)) + 1) * φ (ιR (z0 π b₄ t κ)) *
      (φ (ιR (z0 π b₄ t κ)) + φ (ιR (ιT κ)) * φ (ιR (ιT t))) *
      IsLocalization.Away.lift (S := Localization.Away h) h hβh Hi = 1 := by
    have := congrArg (IsLocalization.Away.lift (S := Localization.Away h) h hβh) hH
    simpa only [map_mul, map_add, map_one, htL, hκL, hΨO, hΨX] using this
  have hγc : IsUnit (γ (TateGlue0.c0 π b₄ t κ)) := by
    rw [TateGlue0.c0, map_add, map_one, liftT0_h0]
    have e : 1 + aH = -((tL ^ 2 - bL) * (Xt * (Xt + κL * tL)) ^ 2 * Hi) := by
      rw [haH]
      linear_combination -hkL - κL * (tL ^ 2 - bL) * hH
    rw [e]
    have htb : IsUnit (tL ^ 2 - bL) := IsUnit.of_mul_eq_one_right _ hkL
    have hXX : IsUnit (Xt * (Xt + κL * tL)) :=
      IsUnit.of_mul_eq_one ((tL * Xt + 1) * Hi) (by linear_combination hH)
    have hHi' : IsUnit Hi := IsUnit.of_mul_eq_one_right ((tL * Xt + 1) * Xt * (Xt + κL * tL)) hH
    exact ((htb.mul (hXX.pow 2)).mul hHi').neg
  refine chartData_of_lift hM hθ hθϖ hP hβh γ.toRingHom hγc hγO
    ((liftT0_z0 _ _ hrel).trans hXt) hc (ringHom_ext_T0 (fun o ↦ ?_) ?_ ?_)
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hγO, ← halg, hΨO]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, γ, liftT0_h0]
    rw [haH]
    simp only [map_neg, map_mul, map_sub, map_add, map_pow, map_ofNat, htL, hκL, hbL, hΨO, hΨX]
    linear_combination (-(φ (ιR (ιT t)) ^ 2 - φ (ιR (ιT b₆))) * φ (ιR (z0 π b₄ t κ)) *
      (φ (ιR (z0 π b₄ t κ)) + φ (ιR (ιT κ)) * φ (ιR (ιT t))) *
      IsLocalization.Away.lift (S := Localization.Away h) h hβh Hi) * hq +
      φ (ιR (h0 π b₄ t κ)) * (φ (ιR (ιT κ)) * (φ (ιR (ιT t)) ^ 2 - φ (ιR (ιT b₆)))) * hhi +
      φ (ιR (h0 π b₄ t κ)) * hk
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, γ, liftT0_z0, hΨX]

/-- **Regular pairs on a localization `R` of `T0` at powers of `1 + h`**: at a maximal ideal `P`
of `R` containing `ϖ` but not `1 + h`, `ϖ` is prime in `R_P` and `𝔪_P = (ϖ, y)`, `y ∉ (ϖ)`. -/
theorem exists_regular_pair_loc (hM : M ≤ Submonoid.powers (TateGlue0.c0 π b₄ t κ))
    (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [IsDomain R] (P : Ideal R) [hP : P.IsMaximal] (hx0 : ιR (ιT ϖ) ≠ 0)
    (hϖP : ιR (ιT ϖ) ∈ P) (hcP : ιR (TateGlue0.c0 π b₄ t κ) ∉ P) :
    ∃ y : Localization.AtPrime P, Prime (algebraMap R (Localization.AtPrime P) (ιR (ιT ϖ))) ∧
      y ∉ Ideal.span {algebraMap R (Localization.AtPrime P) (ιR (ιT ϖ))} ∧
      maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap R (Localization.AtPrime P) (ιR (ιT ϖ)), y} := by
  have hθϖ : θ ϖ = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ϖ
  set φ : R →+* Localization.AtPrime P ⧸
      Ideal.span {algebraMap R (Localization.AtPrime P) (ιR (ιT ϖ))} :=
    (Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime P))
  have hϖ0 : φ (ιR (ιT ϖ)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hunit : ∀ r ∉ P, IsUnit (φ r) := fun r hr ↦
    (IsLocalization.map_units (Localization.AtPrime P) (⟨r, hr⟩ : P.primeCompl)).map
      (Ideal.Quotient.mk _)
  have hc : ∀ o, residueFieldLift θ ((φ.comp ιR).comp ιT) hϖ0 hθ hker (θ o) =
      φ (ιR (ιT o)) := residueFieldLift_θ _ _ _ _
  have hcd : ChartData φ (ιR (ιT ϖ)) P (residueFieldLift θ ((φ.comp ιR).comp ιT) hϖ0 hθ hker) := by
    by_cases hz : ιR (z0 π b₄ t κ) ∈ P
    · refine chartData_line hM hc hθ hθϖ hπ hm hϖ0 (hunit _ hcP) hP.ne_top (hunit _ ?_)
      intro hq
      have hmem : ιR (ιT κ) * ιR (TateGlue0.c0 π b₄ t κ) ∈ P := by
        rw [show ιR (ιT κ) * ιR (TateGlue0.c0 π b₄ t κ) = ιR (q0 π b₄ t κ) - ιR (z0 π b₄ t κ) *
            ιR (z0 π b₄ t κ + ιT κ * ιT t * (2 + h0 π b₄ t κ)) by
          rw [← map_mul, ← map_mul, ← map_sub]
          congr 1
          unfold q0 TateGlue0.c0
          ring]
        exact P.sub_mem hq (P.mul_mem_right _ hz)
      refine hcP ((hP.isPrime.mem_or_mem hmem).resolve_left fun hκP ↦ hP.ne_top ?_)
      exact Ideal.eq_top_of_isUnit_mem _ hκP (((IsUnit.of_mul_eq_one _ hκ).map ιT).map ιR)
    · exact chartData_conic hM hκ hb₆ hc hθ hθϖ hπ hm hϖ0 (hunit _ hcP) hP.ne_top (hunit _ hz)
  exact exists_regular_pair_of_chartData hx0 hϖP _ hcd

end

end TateT0Regular

open TateT0Regular

/-- **The Tate chart `T0` is regular at the closed points of the special fibre in `D(1 + h)`**
(MR12 S5.2): if `P` is a maximal ideal of `T0` containing `ϖ` but not `1 + h`, then `ϖ` is
prime in `T0_P` and `𝔪_P = (ϖ, y)` with `y ∉ (ϖ)`. Valid in every residue characteristic. -/
theorem exists_regular_pair_T0 {O : Type u} [CommRing O] [IsDomain O] {k : Type u} [Field k]
    {θ : O →+* k} {π b₄ b₆ t κ ϖ ε : O} {m : ℕ} (hϖ : Irreducible ϖ)
    (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [IsDomain (T0 π b₄ t κ)] (P : Ideal (T0 π b₄ t κ)) [hP : P.IsMaximal]
    (hϖP : algebraMap O _ ϖ ∈ P) (hcP : TateGlue0.c0 π b₄ t κ ∉ P) :
    ∃ y : Localization.AtPrime P, Prime (algebraMap O (Localization.AtPrime P) ϖ) ∧
      y ∉ Ideal.span {algebraMap O (Localization.AtPrime P) ϖ} ∧
      maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap O (Localization.AtPrime P) ϖ, y} := by
  letI : Algebra (T0 π b₄ t κ) (T0 π b₄ t κ) := Algebra.id _
  haveI hloc : IsLocalization (⊥ : Submonoid (T0 π b₄ t κ)) (T0 π b₄ t κ) :=
    IsLocalization.self bot_le
  have hx0 : algebraMap (T0 π b₄ t κ) (T0 π b₄ t κ) (algebraMap O _ ϖ) ≠ 0 := by
    rw [Algebra.algebraMap_self_apply]; exact algebraMap_ϖ_T0_ne_zero hϖ.ne_zero
  have hϖP' : algebraMap (T0 π b₄ t κ) (T0 π b₄ t κ) (algebraMap O _ ϖ) ∈ P := by
    rw [Algebra.algebraMap_self_apply]; exact hϖP
  have hcP' : algebraMap (T0 π b₄ t κ) (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) ∉ P := by
    rw [Algebra.algebraMap_self_apply]; exact hcP
  have hM : (⊥ : Submonoid (T0 π b₄ t κ)) ≤ Submonoid.powers (TateGlue0.c0 π b₄ t κ) := bot_le
  have := exists_regular_pair_loc (R := T0 π b₄ t κ) (M := ⊥) hM hθ hker hπ hm hκ hb₆ P
    hx0 hϖP' hcP'
  simp only [Algebra.algebraMap_self_apply] at this
  rw [IsScalarTower.algebraMap_apply O (T0 π b₄ t κ) (Localization.AtPrime P)]
  exact this

/-- **The cusp chart `Rc = T0[1/(1 + h)]` is regular along the special fibre** (MR12 S5.2): at
every maximal ideal `P` of `Rc` containing `ϖ`, `ϖ` is prime in `Rc_P` and `𝔪_P = (ϖ, y)` with
`y ∉ (ϖ)`. Valid in every residue characteristic. -/
theorem exists_regular_pair_Rc {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {k : Type u} [Field k] {θ : O →+* k} {π b₄ b₆ t κ ϖ ε : O} {m : ℕ} (hϖ : Irreducible ϖ)
    (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    (P : Ideal (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ))) [hP : P.IsMaximal]
    (hϖP : algebraMap O _ ϖ ∈ P) :
    ∃ y : Localization.AtPrime P, Prime (algebraMap O (Localization.AtPrime P) ϖ) ∧
      y ∉ Ideal.span {algebraMap O (Localization.AtPrime P) ϖ} ∧
      maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap O (Localization.AtPrime P) ϖ, y} := by
  have hπ0 : π ≠ 0 := by
    rw [hπ]; exact mul_ne_zero hε.ne_zero (pow_ne_zero _ hϖ.ne_zero)
  haveI := isDomain_T0 (b₄ := b₄) (t := t) hϖ hκ h3 hπ0 hE
  haveI := isDomain_Rc (b₄ := b₄) (t := t) hϖ hκ h3 hπ0 hE
  have hinj : Function.Injective
      (algebraMap (T0 π b₄ t κ) (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ))) :=
    IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (nonZeroDivisors.ne_zero c0_mem_T0))
  have hϖR : algebraMap O (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ)) ϖ =
      algebraMap (T0 π b₄ t κ) _ (algebraMap O _ ϖ) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have := exists_regular_pair_loc (R := CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ))
    (M := Submonoid.powers (TateGlue0.c0 π b₄ t κ)) le_rfl hθ hker hπ hm hκ hb₆ P
    ((map_ne_zero_iff _ hinj).2 (algebraMap_ϖ_T0_ne_zero hϖ.ne_zero)) (hϖR ▸ hϖP)
    fun h ↦ hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (IsLocalization.Away.algebraMap_isUnit (TateGlue0.c0 π b₄ t κ)))
  rwa [IsScalarTower.algebraMap_apply O (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ))
    (Localization.AtPrime P), hϖR]

/-- `exists_regular_pair_Rc` in the shape of the regularity hypothesis of
`PurityLocal.etale_quot_awayMap`. -/
theorem hreg_Rc {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {k : Type u} [Field k] {θ : O →+* k} {π b₄ b₆ t κ ϖ ε : O} {m : ℕ} (hϖ : Irreducible ϖ)
    (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    (P : Ideal (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ))) [P.IsMaximal]
    (hϖP : algebraMap O _ ϖ ∈ P) :
    ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
      maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y} := by
  obtain ⟨y, h1, h2, h3⟩ := exists_regular_pair_Rc hϖ hθ hker hπ hm hε h3 hE hκ hb₆ P hϖP
  exact ⟨_, y, h1, h2, h3⟩

/-- **The cusp chart `Rc = T0[1/(1 + h)]` is integrally closed** (MR12 S5.2), for `O` a discrete
valuation ring, `π = ε ϖᵐ`, `m ≥ 1`, `ε` and `b₆` units, `κ (t² − b₆) = 1`, `3 ≠ 0`, `E ≠ 0`. -/
theorem isIntegrallyClosed_Rc {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {k : Type u} [Field k] {θ : O →+* k} {π b₄ b₆ t κ ϖ ε : O} {m : ℕ} (hϖ : Irreducible ϖ)
    (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆) :
    IsIntegrallyClosed (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ)) := by
  have hπ0 : π ≠ 0 := by
    rw [hπ]; exact mul_ne_zero hε.ne_zero (pow_ne_zero _ hϖ.ne_zero)
  haveI := isDomain_T0 (b₄ := b₄) (t := t) hϖ hκ h3 hπ0 hE
  haveI := isDomain_Rc (b₄ := b₄) (t := t) hϖ hκ h3 hπ0 hE
  haveI := isDedekindDomain_away_T0_of_dvr (π := π) (b₄ := b₄) (t := t) (κ := κ) hϖ.ne_zero
    hϖ.not_isUnit hκ h3 hπ0 hE
  refine IsIntegrallyClosed.of_localization_maximal fun P _ _ ↦ ?_
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (TateGlue0.c0 π b₄ t κ)) P
  suffices IsIntegrallyClosed (Localization.AtPrime
      (P.comap (algebraMap (T0 π b₄ t κ)
        (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ))))) from
    IsIntegrallyClosed.of_equiv e.toRingEquiv
  refine NormalLocal.isIntegrallyClosed_atPrime_of_away _ (algebraMap_ϖ_T0_ne_zero hϖ.ne_zero)
    (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) ?_
  by_cases hϖP : algebraMap O (T0 π b₄ t κ) ϖ ∈
      P.comap (algebraMap (T0 π b₄ t κ) (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ)))
  · right
    have hϖP' : algebraMap O (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ)) ϖ ∈ P := by
      rwa [IsScalarTower.algebraMap_apply O (T0 π b₄ t κ)]
    obtain ⟨y, hp, -⟩ := exists_regular_pair_Rc hϖ hθ hker hπ hm hε h3 hE hκ hb₆ P hϖP'
    rw [← MulEquiv.prime_iff e, AlgEquiv.commutes]
    rwa [IsScalarTower.algebraMap_apply O (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ))
      (Localization.AtPrime P), IsScalarTower.algebraMap_apply O (T0 π b₄ t κ)
      (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ)), ← IsScalarTower.algebraMap_apply] at hp
  · exact Or.inl hϖP

end TateTwoChart

end SemistableReduction
