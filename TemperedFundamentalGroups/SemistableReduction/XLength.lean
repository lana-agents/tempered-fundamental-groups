/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiModel

/-!
# Intrinsic x-line lengths of nodes (W8′, `Statement.HarmonicX`, valuative core)

Blueprint §9.7. Let `F` be the function field of a curve over a field `K` (the constants of the
x-line), `O' ⊆ K` a valuation subring with uniformizer `ϖ'`, `ϖ` the uniformizer of the base
`O ⊆ O'` (the **normalisation**: all lengths are measured in units of `v(ϖ) = 1`, hence do not
depend on `O'`), and `x ∈ F` transcendental over `K` (the **x-line** `K(x) ⊆ F`).

A node of a model of `F` over `O'`, given by node coordinates `u, v` (`u v = ϖ' ^ n`) at the
point `P` (its local ring, or any set of functions regular at the point), joins two type-2
valuations `W₁` (`u` a unit with transcendental residue) and `W₂` (`v` such a unit). The
**interpolating monomial valuations** of the node are the valuations `U_s` of `F`, `0 ≤ s ≤ n`,
with `P ⊆ U_s`, `U_s(u) = U_s(ϖ') ^ s` and transcendental residue of the monomial
`u ^ den s / ϖ' ^ num s` (`IsMonomialPt`; `U_0 = W₁`, `U_n = W₂`). Restricting them to `K(x)`
gives a path `s ↦ U_s|K(x)` of Gauss valuations `w_{a, r}` (W2: `IsXGauss`, centre `a ∈ K`,
normalised log radius `ρ`, `r = |ϖ| ^ ρ`) on the x-line. Its **x-length**
`λ = ∑ |Δ log r|` over the finitely many monotone pieces of the path, normalised to `v(ϖ) = 1`,
is the total variation of the log radius along the path (in the Bruhat–Tits tree of the x-line
every edge changes the radius, so the length of a path is the total variation of its log
radius). The path may **fold**: for `x = z + ϖ / z` on the node `z · (ϖ / z) = ϖ` it runs from
`w_{0,1}` down to `w_{0,|ϖ|^{1/2}}` and back, `λ = 1`, although both branches restrict to the
same Gauss point.

Formally (`IsXLength`): `λ` is the greatest length `∑ |ρ_{i+1} - ρ_i|` of a *chain*
`0 = s₀ < … < s_m = n` of monomial points with Gauss data of their restrictions (`XChain`); the
greatest element exists (the breakpoints of the path) and is the total variation. No Berkovich
space is used: everything is a statement about valuation subrings of `F`.

## Main results

* `IsLogValue.unique`, `IsXGauss.rho_unique`: the normalised log radius of a Gauss point is
  well defined (independent of the chosen centre);
* `IsMonomialPt.param_unique`: monomial points at different parameters differ;
* `XChain.length_nonneg`, `IsXLength.unique`, `IsXLength.nonneg`: the x-length is well defined
  and nonnegative; `IsXLength.le_of_chain` (every chain gives a lower bound), in particular
  `IsXLength.abs_sub_le`: `λ ≥ |ρ(W₂) - ρ(W₁)|` (the radii of the two branches).
-/

open Polynomial

namespace SemistableReduction

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- `ρ ∈ ℚ` is the **`ϖ`-normalised order** of `f` at `U`: `U(f) = U(ϖ) ^ ρ`, i.e.
`U(f) ^ den ρ = U(ϖ) ^ num ρ`. -/
def IsLogValue (U : ValuationSubring F) (ϖ f : F) (ρ : ℚ) : Prop :=
  U.valuation f ^ ρ.den = U.valuation ϖ ^ ρ.num

/-- Integer powers of an element `0 < γ < 1` are injective. -/
lemma zpow_injective_of_lt_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {γ : Γ}
    (h0 : γ ≠ 0) (h1 : γ < 1) : Function.Injective fun n : ℤ ↦ γ ^ n := by
  intro a b hab
  have key : ∀ k : ℤ, 0 < k → γ ^ k < 1 := fun k hk ↦ by
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
    rw [zpow_natCast]
    exact pow_lt_one₀ zero_le h1 (by omega)
  simp only at hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := key (b - a) (by omega)
    rw [zpow_sub₀ h0, ← hab, div_self (zpow_ne_zero _ h0)] at this
    exact lt_irrefl _ this
  · have := key (a - b) (by omega)
    rw [zpow_sub₀ h0, hab, div_self (zpow_ne_zero _ h0)] at this
    exact lt_irrefl _ this

/-- The normalised order is unique when `U(ϖ) < 1`. -/
theorem IsLogValue.unique {U : ValuationSubring F} {ϖ f : F} {ρ σ : ℚ}
    (hϖ0 : U.valuation ϖ ≠ 0) (hϖ : U.valuation ϖ < 1) (hρ : IsLogValue U ϖ f ρ)
    (hσ : IsLogValue U ϖ f σ) : ρ = σ := by
  unfold IsLogValue at hρ hσ
  have h : U.valuation ϖ ^ (ρ.num * σ.den) = U.valuation ϖ ^ (σ.num * ρ.den) := by
    rw [zpow_mul, ← hρ, zpow_mul, ← hσ, zpow_natCast, zpow_natCast, ← pow_mul, ← pow_mul,
      mul_comm]
  rw [Rat.eq_iff_mul_eq_mul]
  exact zpow_injective_of_lt_one hϖ0 hϖ h

/-- **`U` restricts on `K(x)` to the Gauss valuation `w_{a, |ϖ|^ρ}`**: `U(x - a) = U(ϖ) ^ ρ`
and `U(Q(x - a)) = max_i U(Qᵢ (x - a) ^ i)` for every polynomial `Q` over `K` (W2: over an
algebraically closed `K` every type-2 or type-3 valuation of `K(x)` is of this form). -/
def IsXGauss (ϖ x : F) (a : K) (ρ : ℚ) (U : ValuationSubring F) : Prop :=
  IsLogValue U ϖ (x - algebraMap K F a) ρ ∧
    ∀ Q : K[X], U.valuation (aeval (x - algebraMap K F a) Q) =
      Q.support.sup fun i ↦ U.valuation (algebraMap K F (Q.coeff i) * (x - algebraMap K F a) ^ i)

/-- At a Gauss point, the value of `x - b` for any other centre `b` is at least the radius. -/
lemma IsXGauss.valuation_le {ϖ x : F} {a : K} {ρ : ℚ} {U : ValuationSubring F}
    (h : IsXGauss ϖ x a ρ U) (b : K) :
    U.valuation (x - algebraMap K F a) ≤ U.valuation (x - algebraMap K F b) := by
  by_cases hab : a = b
  · rw [hab]
  have hQ := h.2 (X + C (a - b))
  have he : aeval (x - algebraMap K F a) (X + C (a - b)) = x - algebraMap K F b := by
    simp [map_sub]
  rw [he] at hQ
  rw [hQ]
  have h1 : (1 : ℕ) ∈ (X + C (a - b) : K[X]).support := by
    rw [mem_support_iff, coeff_add, coeff_X_one, coeff_C]
    simp
  refine le_trans (le_of_eq ?_) (Finset.le_sup h1)
  simp

/-- **The radius of a Gauss point does not depend on the centre**: two Gauss data `(a, ρ)`,
`(b, σ)` of the same `U` (with `0 < U(ϖ) < 1`) have `ρ = σ`. -/
theorem IsXGauss.rho_unique {ϖ x : F} {a b : K} {ρ σ : ℚ} {U : ValuationSubring F}
    (hϖ0 : U.valuation ϖ ≠ 0) (hϖ : U.valuation ϖ < 1) (ha : IsXGauss ϖ x a ρ U)
    (hb : IsXGauss ϖ x b σ U) : ρ = σ := by
  have he : U.valuation (x - algebraMap K F a) = U.valuation (x - algebraMap K F b) :=
    le_antisymm (ha.valuation_le b) (hb.valuation_le a)
  have hσ : IsLogValue U ϖ (x - algebraMap K F a) σ := by
    unfold IsLogValue
    rw [he]
    exact hb.1
  exact IsLogValue.unique hϖ0 hϖ ha.1 hσ

/-- **Interpolating monomial point** of the node with coordinate `u` (`u v = ϖ' ^ n`) at the
parameter `s`: `U ⊇ P`, `U(ϖ') < 1` (non-trivial on the constants), `U(u) = U(ϖ') ^ s`, and the
monomial `u ^ den s / ϖ' ^ num s` has transcendental residue over the residue field of `O'`.
The branches are the monomial points at `s = 0` (`u` itself has transcendental residue) and
`s = n` (`1 / v = u / ϖ' ^ n`). -/
def IsMonomialPt (O' : ValuationSubring K) (P : Set F) (ϖ' u : F) (s : ℚ)
    (U : ValuationSubring F) : Prop :=
  P ⊆ U ∧ U.valuation ϖ' < 1 ∧ IsLogValue U ϖ' u s ∧
    IsResidueTranscendental O' U (u ^ s.den / ϖ' ^ s.num)

/-- Monomial points at different parameters are different (XL4: the path is injective). -/
theorem IsMonomialPt.param_unique {O' : ValuationSubring K} {P : Set F} {ϖ' u : F} {s t : ℚ}
    {U : ValuationSubring F} (hϖ0 : U.valuation ϖ' ≠ 0) (hϖ : U.valuation ϖ' < 1)
    (hs : IsMonomialPt O' P ϖ' u s U) (ht : IsMonomialPt O' P ϖ' u t U) : s = t :=
  IsLogValue.unique hϖ0 hϖ hs.2.2.1 ht.2.2.1

/-- The algebraic closure of `F`, over which the centres of Gauss points live. -/
abbrev Fbar (F : Type*) [Field F] : Type _ := AlgebraicClosure F

variable (K F) in
/-- The constants of the x-line over `F̄`: the elements of `F̄` algebraic over `K` (an algebraic
closure of `K`). Centres of Gauss points are taken here, so that every monomial point has Gauss
data (W2), also when the path turns into directions not defined over `K`. -/
abbrev Kbar : Type _ := ↥(algebraicClosure K (Fbar F))

/-- A **chain** along the node with coordinate `u` of thickness `n` (over `O'`, uniformizer
`ϖ'`): parameters `0 = s₀ < s₁ < … < s_m = n`, monomial points `U i` at `s i`, extensions
`U' i` of them to `F̄`, and Gauss data `(a i, ρ i)` (centres `a i` algebraic over `K`) of the
restrictions of `U' i` to the x-line `K̄(x)`, radii normalised by `ϖ`. The normalised radius
does not depend on the centre (`IsXGauss.rho_unique`); the length (`XChain.length`) is the
variation of the radii, invariant under extension of the constants. -/
structure XChain (O' : ValuationSubring K) (P : Set F) (ϖ ϖ' u x : F) (n : ℕ) where
  /-- The number of pieces. -/
  m : ℕ
  /-- The parameters along the node. -/
  s : Fin (m + 1) → ℚ
  /-- The monomial points. -/
  U : Fin (m + 1) → ValuationSubring F
  /-- Extensions of the monomial points to `F̄`. -/
  U' : Fin (m + 1) → ValuationSubring (Fbar F)
  /-- The centres of their restrictions to the x-line `K̄(x)`. -/
  a : Fin (m + 1) → Kbar K F
  /-- The normalised log radii of their restrictions to the x-line. -/
  ρ : Fin (m + 1) → ℚ
  s_zero : s 0 = 0
  s_last : s (Fin.last m) = n
  strictMono : StrictMono s
  isMonomialPt : ∀ i, IsMonomialPt O' P ϖ' u (s i) (U i)
  comap_eq : ∀ i, (U' i).comap (algebraMap F (Fbar F)) = U i
  isXGauss : ∀ i, IsXGauss (algebraMap F (Fbar F) ϖ) (algebraMap F (Fbar F) x) (a i) (ρ i) (U' i)

/-- Telescoping: `|p k - p 0| ≤ ∑ |p (i+1) - p i|`. -/
lemma abs_sub_le_sum_abs {k : ℕ} (p : Fin (k + 1) → ℚ) :
    |p (Fin.last k) - p 0| ≤ ∑ i : Fin k, |p i.succ - p i.castSucc| := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    calc |p (Fin.last (k + 1)) - p 0|
        = |(p (Fin.last k).succ - p (Fin.last k).castSucc) +
            (p (Fin.last k).castSucc - p 0)| := by
          congr 1
          simp only [Fin.succ_last]
          abel
      _ ≤ |p (Fin.last k).succ - p (Fin.last k).castSucc| +
            |p (Fin.last k).castSucc - p 0| := abs_add_le _ _
      _ ≤ |p (Fin.last k).succ - p (Fin.last k).castSucc| +
            ∑ i : Fin k, |p i.succ.castSucc - p i.castSucc.castSucc| := by
          have := ih (fun i ↦ p i.castSucc)
          simp only [Fin.castSucc_zero] at this
          gcongr
      _ = _ := by
          rw [add_comm]
          simp only [Fin.succ_castSucc]

namespace XChain

variable {O' : ValuationSubring K} {P : Set F} {ϖ ϖ' u x : F} {n : ℕ}

/-- The length of a chain: `∑ |ρ_{i+1} - ρ_i|`, the variation of the log radius. -/
def length (γ : XChain O' P ϖ ϖ' u x n) : ℚ :=
  ∑ i : Fin γ.m, |γ.ρ i.succ - γ.ρ i.castSucc|

lemma length_nonneg (γ : XChain O' P ϖ ϖ' u x n) : 0 ≤ γ.length :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The length of a chain bounds the radius difference of its end points (telescoping). -/
lemma abs_sub_le_length (γ : XChain O' P ϖ ϖ' u x n) :
    |γ.ρ (Fin.last γ.m) - γ.ρ 0| ≤ γ.length := by
  unfold length
  exact abs_sub_le_sum_abs γ.ρ

end XChain

/-- **The x-length of a node** (Blueprint §9.7, `Statement.HarmonicX`): the node at `P` with
coordinate `u` of thickness `n` over `O'` (`u v = ϖ' ^ n`) has x-length `λ` if `λ` is the
greatest length of a chain of its interpolating monomial valuations: the total variation of
the log radius (normalised to `v(ϖ) = 1`) of the path `s ↦ U_s|K(x)`, `0 ≤ s ≤ n`, of their
restrictions to the x-line, i.e. the sum of `|Δ log radius|` over its finitely many monotone
pieces, **folds included**. Purely valuation-theoretic (W5 dictionary, W2 Gauss points). -/
def IsXLength (O' : ValuationSubring K) (P : Set F) (ϖ ϖ' u x : F) (n : ℕ) (l : ℚ) : Prop :=
  IsGreatest (Set.range (XChain.length (O' := O') (P := P) (ϖ := ϖ) (ϖ' := ϖ') (u := u)
    (x := x) (n := n))) l

namespace IsXLength

variable {O' : ValuationSubring K} {P : Set F} {ϖ ϖ' u x : F} {n : ℕ} {l l' : ℚ}

/-- The x-length is well defined. -/
theorem unique (h : IsXLength O' P ϖ ϖ' u x n l) (h' : IsXLength O' P ϖ ϖ' u x n l') :
    l = l' :=
  IsGreatest.unique h h'

theorem nonneg (h : IsXLength O' P ϖ ϖ' u x n l) : 0 ≤ l := by
  obtain ⟨γ, hγ⟩ := h.1
  rw [← hγ]
  exact γ.length_nonneg

/-- Every chain gives a lower bound for the x-length. -/
theorem le_of_chain (h : IsXLength O' P ϖ ϖ' u x n l) (γ : XChain O' P ϖ ϖ' u x n) :
    γ.length ≤ l :=
  h.2 ⟨γ, rfl⟩

/-- The x-length is at least the radius difference of the restrictions of the two branches. -/
theorem abs_sub_le (h : IsXLength O' P ϖ ϖ' u x n l) (γ : XChain O' P ϖ ϖ' u x n) :
    |γ.ρ (Fin.last γ.m) - γ.ρ 0| ≤ l :=
  γ.abs_sub_le_length.trans (h.le_of_chain γ)

end IsXLength

end SemistableReduction
