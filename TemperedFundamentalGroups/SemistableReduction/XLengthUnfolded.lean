/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.MonomialExists
import TemperedFundamentalGroups.SemistableReduction.XGauss

/-!
# The x-length of an unfolded node (Blueprint §9.7, XL3/XL6, the unfolded case)

Let `P` be the germs of a node of a model of `L` over `O'` (`NodeGerm`, coordinates `u v = ϖ' ^ n`)
lying over a node of the Gauss tree of the x-line (`ModelCode.IsUnfolded`): the base node
coordinate `t = (x - a) / β` (`a, β ∈ K'`) is `t = ε w ^ e ϖ' ^ α` with `ε` a unit of `P` and
`w = u` or `w = v` (XL6, the output of the W7 node lemma S9). Then along the node the restriction
of the monomial point `U_s` to the x-line is the Gauss point with centre `a` and normalised log
radius `ρ(s) = (ord β + α + e σ(s)) / e₀` (`σ(s) = s` or `n - s`, `ϖ₀ = η ϖ' ^ e₀` the base
uniformizer), linear in `s`: the x-path is monotone and

  `λ = e n / e₀` (`IsXLength.of_unfolded`).

Gauss data over `K̄` come from residue transcendence of the monomial in `t`
(`valuation_aeval_eq_sup_of_residue`); every chain then has length exactly `e n / e₀` (the radius
does not depend on the centre, `IsXGauss.rho_unique`), and the chain `0 < n` through the two
branches exists.
-/

open Polynomial

namespace SemistableReduction

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

/-- **Every valuation subring extends** along a field extension (Chevalley). -/
theorem exists_valuationSubring_comap_eq (U : ValuationSubring L) :
    ∃ U' : ValuationSubring F, U'.comap (algebraMap L F) = U := by
  set R : Subring F := U.toSubring.map (algebraMap L F)
  let e : U.toSubring ≃+* R :=
    U.toSubring.equivMapOfInjective (algebraMap L F) (algebraMap L F).injective
  set 𝔐 : Ideal R := (IsLocalRing.maximalIdeal U).comap e.symm.toRingHom
  obtain ⟨U', hR, hlt, -⟩ := exists_valuationSubring_of_isPrime R 𝔐
  refine ⟨U', ?_⟩
  ext q
  refine ⟨fun hq ↦ ?_, fun hq ↦ hR ⟨q, hq, rfl⟩⟩
  by_contra hqU
  have hq0 : q ≠ 0 := fun h ↦ hqU (h ▸ U.zero_mem)
  have hinv : q⁻¹ ∈ U := (U.mem_or_inv_mem q).resolve_left hqU
  have hmax : (⟨q⁻¹, hinv⟩ : U) ∈ IsLocalRing.maximalIdeal U := by
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    apply hqU
    have : q = (w : L) := by
      have := congrArg (fun z : U ↦ (z : L)) hw
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
      field_simp at this
      exact this.symm
    rw [this]; exact w.2
  have h1 : U'.valuation (algebraMap L F q⁻¹) < 1 := by
    have := hlt (e ⟨q⁻¹, hinv⟩) (by simpa [𝔐] using hmax)
    rwa [Subring.coe_equivMapOfInjective_apply] at this
  have h2 : U'.valuation (algebraMap L F q) ≤ 1 := (U'.valuation_le_one_iff _).mpr hq
  have h3 : U'.valuation (algebraMap L F q) * U'.valuation (algebraMap L F q⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hq0, map_one, map_one]
  have h4 : U'.valuation (algebraMap L F q) * U'.valuation (algebraMap L F q⁻¹) < 1 :=
    calc _ ≤ 1 * U'.valuation (algebraMap L F q⁻¹) := mul_le_mul_left h2 _
      _ < 1 := by rw [one_mul]; exact h1
  rw [h3] at h4
  exact lt_irrefl _ h4

variable {U : ValuationSubring L} {U' : ValuationSubring F}

/-- Units are preserved by extensions of valuation subrings. -/
lemma valuation_eq_one_of_comap (hU' : U'.comap (algebraMap L F) = U) {f : L}
    (hf : U.valuation f = 1) : U'.valuation (algebraMap L F f) = 1 := by
  obtain ⟨hf0, h1, h2⟩ := (valuation_eq_one_iff_mem_and_inv_mem U).mp hf
  rw [valuation_eq_one_iff_mem_and_inv_mem]
  refine ⟨by simpa using hf0, ?_, ?_⟩
  · rw [← ValuationSubring.mem_comap, hU']; exact h1
  · rw [← map_inv₀, ← ValuationSubring.mem_comap, hU']; exact h2

/-- Equalities of values transfer to extensions. -/
lemma valuation_eq_of_comap (hU' : U'.comap (algebraMap L F) = U) {f g : L} (hg : g ≠ 0)
    (hfg : U.valuation f = U.valuation g) :
    U'.valuation (algebraMap L F f) = U'.valuation (algebraMap L F g) := by
  by_cases hf : f = 0
  · subst hf
    exact absurd ((map_eq_zero _).mp (by rw [← hfg, map_zero])) hg
  have h1 : U.valuation (f / g) = 1 := by
    rw [map_div₀, hfg, div_self (by simpa using hg)]
  have := valuation_eq_one_of_comap hU' h1
  rw [map_div₀, map_div₀, div_eq_one_iff_eq (by simpa using hg)] at this
  exact this

/-- `IsLogValue` transfers to extensions. -/
lemma IsLogValue.of_comap (hU' : U'.comap (algebraMap L F) = U) {ϖ f : L} (hϖ : ϖ ≠ 0)
    {q : ℚ} (h : IsLogValue U ϖ f q) : IsLogValue U' (algebraMap L F ϖ) (algebraMap L F f) q := by
  unfold IsLogValue at h ⊢
  rw [← map_pow, ← map_zpow₀, ← map_pow, ← map_zpow₀]
  exact valuation_eq_of_comap hU' (zpow_ne_zero _ hϖ) (by rwa [map_pow, map_zpow₀])

/-- Residue transcendence transfers to extensions. -/
lemma IsResidueTranscendental.of_comap {K : Type*} [Field K] [Algebra K L] [Algebra K F]
    [IsScalarTower K L F] {O : ValuationSubring K} (hU' : U'.comap (algebraMap L F) = U) {z : L}
    (h : IsResidueTranscendental O U z) : IsResidueTranscendental O U' (algebraMap L F z) := by
  refine ⟨?_, fun P hP ↦ ?_⟩
  · rw [← ValuationSubring.mem_comap, hU']; exact h.1
  · have := valuation_eq_one_of_comap hU' (h.2 P hP)
    rwa [← aeval_algebraMap_apply] at this

/-- `IsLogValue` from a non-reduced exponent `N / D`. -/
lemma IsLogValue.of_pow_eq {U : ValuationSubring L} {ϖ f : L} {N : ℤ} {D : ℕ} (hD : 0 < D)
    (h : U.valuation f ^ D = U.valuation ϖ ^ N) : IsLogValue U ϖ f ((N : ℚ) / D) := by
  set q : ℚ := (N : ℚ) / D
  have hq : (q.num : ℚ) * D = N * q.den := by
    have h1 : (q.num : ℚ) = q * q.den := q.mul_den_eq_num.symm
    rw [h1]; simp only [q]; field_simp
  have hq' : q.num * (D : ℤ) = N * q.den := by exact_mod_cast hq
  unfold IsLogValue
  have key : (U.valuation f ^ q.den) ^ D = (U.valuation ϖ ^ q.num) ^ D := by
    rw [← pow_mul, mul_comm, pow_mul, h, ← zpow_natCast, ← zpow_mul, ← zpow_natCast,
      ← zpow_mul, hq']
  exact le_antisymm ((pow_le_pow_iff_left₀ zero_le zero_le hD.ne').mp key.le)
    ((pow_le_pow_iff_left₀ zero_le zero_le hD.ne').mp key.ge)

/-- Telescoping sums over `Fin`. -/
lemma sum_succ_sub_castSucc : ∀ (m : ℕ) (s : Fin (m + 1) → ℚ),
    ∑ i : Fin m, (s i.succ - s i.castSucc) = s (Fin.last m) - s 0
  | 0, s => by simp
  | m + 1, s => by
    rw [Fin.sum_univ_castSucc]
    have := sum_succ_sub_castSucc m (fun i ↦ s i.castSucc)
    simp only [Fin.succ_castSucc] at this ⊢
    rw [this]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    ring

/-- Telescoping for a linear function of a strictly increasing sequence. -/
lemma sum_abs_sub_of_linear {m : ℕ} (s ρ : Fin (m + 1) → ℚ) (hs : StrictMono s) {k c : ℚ}
    (hk : 0 ≤ k) (hρ : ∀ i, ρ i = c + k * s i) :
    ∑ i : Fin m, |ρ i.succ - ρ i.castSucc| = k * (s (Fin.last m) - s 0) := by
  have hterm : ∀ i : Fin m, |ρ i.succ - ρ i.castSucc| = k * (s i.succ - s i.castSucc) := by
    intro i
    rw [hρ, hρ, show c + k * s i.succ - (c + k * s i.castSucc) = k * (s i.succ - s i.castSucc)
      by ring]
    exact abs_of_nonneg (mul_nonneg hk (sub_nonneg.mpr (hs.monotone (Fin.castSucc_le_succ i))))
  simp only [hterm, ← Finset.mul_sum]
  rw [sum_succ_sub_castSucc]

section GaussData

variable {K' : Type*} [Field K'] [Algebra K' L] {O' : ValuationSubring K'}

/-- **Gauss data from residue transcendence** (XL3): if `U(x - a) ^ d = U(c)` and
`(x - a) ^ d / c` has transcendental residue over `κ(O')`, then every extension `U'` of `U` to
`F̄` restricts on the x-line `K̄(x)` to the Gauss point with centre `a` (`IsXGauss`). -/
theorem isXGauss_of_residue (hU : U.comap (algebraMap K' L) = O') {x : L} {a c : K'}
    (hc0 : c ≠ 0) {d : ℕ} (hd : 0 < d)
    (hy : U.valuation (x - algebraMap K' L a) ^ d = U.valuation (algebraMap K' L c))
    (htr : IsResidueTranscendental O' U ((x - algebraMap K' L a) ^ d / algebraMap K' L c))
    {ϖ₀ : L} (hϖ₀ : ϖ₀ ≠ 0) {ρ : ℚ} (hρ : IsLogValue U ϖ₀ (x - algebraMap K' L a) ρ)
    (U' : ValuationSubring (Fbar L)) (hU' : U'.comap (algebraMap L (Fbar L)) = U) :
    IsXGauss (algebraMap L (Fbar L) ϖ₀) (algebraMap L (Fbar L) x)
      (algebraMap K' (Kbar K' L) a) ρ U' := by
  haveI : IsAlgClosed (Kbar K' L) := IsAlgClosure.isAlgClosed K'
  haveI : Algebra.IsAlgebraic K' (Kbar K' L) := IsAlgClosure.isAlgebraic
  have hcoe : algebraMap (Kbar K' L) (Fbar L) (algebraMap K' (Kbar K' L) a) =
      algebraMap L (Fbar L) (algebraMap K' L a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hy' : algebraMap L (Fbar L) x - algebraMap (Kbar K' L) (Fbar L)
      (algebraMap K' (Kbar K' L) a) = algebraMap L (Fbar L) (x - algebraMap K' L a) := by
    rw [hcoe, map_sub]
  refine ⟨?_, fun Q ↦ ?_⟩
  · rw [hy']
    exact hρ.of_comap hU' hϖ₀
  · rw [hy']
    have hU'' : U'.comap (algebraMap K' (Fbar L)) = O' := by
      rw [IsScalarTower.algebraMap_eq K' L (Fbar L), ← ValuationSubring.comap_comap, hU', hU]
    have hc' : algebraMap L (Fbar L) (algebraMap K' L c) = algebraMap K' (Fbar L) c :=
      (IsScalarTower.algebraMap_apply _ _ _ _).symm
    have hyF : U'.valuation (algebraMap L (Fbar L) (x - algebraMap K' L a)) ^ d =
        U'.valuation (algebraMap K' (Fbar L) c) := by
      rw [← map_pow, ← map_pow, ← hc']
      exact valuation_eq_of_comap hU' (by simpa using hc0) (by rwa [map_pow])
    have htrF : IsResidueTranscendental O' U'
        ((algebraMap L (Fbar L) (x - algebraMap K' L a)) ^ d / algebraMap K' (Fbar L) c) := by
      have := htr.of_comap (F := Fbar L) hU'
      rwa [map_div₀, map_pow, hc'] at this
    exact valuation_aeval_eq_sup_of_residue (Kb := Kbar K' L) hU'' hc0 hd hyF htrF Q

variable [IsDiscreteValuationRing O']

/-- Gauss data with the radius in base units: if `U(x - a) ^ d = U(β ^ d ϖ' ^ N)` and the
corresponding monomial has transcendental residue, then the extensions of `U` restrict to the Gauss
point with centre `a` and normalised log radius `(d · ord β + N) / (d e₀)` in units of
`ϖ₀ = η ϖ' ^ e₀`. -/
theorem isXGauss_of_monomial (hU : U.comap (algebraMap K' L) = O') {ϖ' : O'}
    (hϖ : Irreducible ϖ') {x : L} {a β : K'} (hβ : β ≠ 0) {d N : ℕ} (hd : 0 < d)
    (hy : U.valuation (x - algebraMap K' L a) ^ d =
      U.valuation (algebraMap K' L (β ^ d * (ϖ' : K') ^ N)))
    (htr : IsResidueTranscendental O' U
      ((x - algebraMap K' L a) ^ d / algebraMap K' L (β ^ d * (ϖ' : K') ^ N)))
    {ϖ₀ : K'} {η : O'ˣ} {e₀ : ℕ} (he₀ : 0 < e₀) (hϖ₀ : ϖ₀ = (η : K') * (ϖ' : K') ^ e₀)
    (U' : ValuationSubring (Fbar L)) (hU' : U'.comap (algebraMap L (Fbar L)) = U) :
    IsXGauss (algebraMap L (Fbar L) (algebraMap K' L ϖ₀)) (algebraMap L (Fbar L) x)
      (algebraMap K' (Kbar K' L) a)
      (((d : ℤ) * ordO O' ϖ' β + N : ℤ) / ((d * e₀ : ℕ) : ℚ)) U' := by
  have hϖ0 : (ϖ' : K') ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hc0 : β ^ d * (ϖ' : K') ^ N ≠ 0 := mul_ne_zero (pow_ne_zero _ hβ) (pow_ne_zero _ hϖ0)
  have hη0 : ((η : O') : K') ≠ 0 := fun h ↦ η.ne_zero (Subtype.ext h)
  have hϖ₀0 : ϖ₀ ≠ 0 := by
    rw [hϖ₀]
    exact mul_ne_zero hη0 (pow_ne_zero _ hϖ0)
  refine isXGauss_of_residue hU hc0 hd hy htr (by simpa using hϖ₀0) ?_ U' hU'
  refine IsLogValue.of_pow_eq (Nat.mul_pos hd he₀) ?_
  obtain ⟨hwp0, -⟩ := valuation_uniformizer hU hϖ
  have hη : U.valuation (algebraMap K' L (η : K')) = 1 := by
    rw [valuation_eq_one_iff_mem_and_inv_mem]
    refine ⟨by simp [hη0], ?_, ?_⟩
    · rw [← ValuationSubring.mem_comap, hU]; exact (η : O').2
    · rw [← map_inv₀, ← ValuationSubring.mem_comap, hU]
      have : ((η : O') : K')⁻¹ = ((η⁻¹ : O'ˣ) : O') := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hη0]
        exact_mod_cast η.inv_mul
      rw [this]; exact ((η⁻¹ : O'ˣ) : O').2
  have hβv := valuation_eq_zpow_ordO hU hϖ hβ
  set w := U.valuation (algebraMap K' L (ϖ' : K'))
  have hR : U.valuation (algebraMap K' L ϖ₀) = w ^ (e₀ : ℤ) := by
    rw [hϖ₀, map_mul, map_mul, hη, one_mul, map_pow, map_pow, zpow_natCast]
  have h1 : U.valuation (algebraMap K' L β) ^ d = w ^ ((d : ℤ) * ordO O' ϖ' β) := by
    rw [hβv, ← zpow_natCast, ← zpow_mul, mul_comm]
  have hy' : U.valuation (x - algebraMap K' L a) ^ d = w ^ ((d : ℤ) * ordO O' ϖ' β + N) := by
    rw [hy, map_mul, map_pow, map_pow, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow,
      h1, zpow_add₀ hwp0, zpow_natCast]
  have hL : U.valuation (x - algebraMap K' L a) ^ (d * e₀) =
      w ^ (((d : ℤ) * ordO O' ϖ' β + N) * e₀) := by
    rw [pow_mul, hy', ← zpow_natCast, ← zpow_mul]
  rw [hL, hR, ← zpow_mul]
  congr 1
  ring

omit [IsDiscreteValuationRing O'] in
/-- **Twisting a residue-transcendental unit** by an element congruent to a unit constant: if `g`
has transcendental residue and `ε ≡ o` (`o ∈ O'ˣ`), then `ε g ^ e` (`e ≥ 1`) has transcendental
residue. -/
theorem IsResidueTranscendental.mul_pow (hU : U.comap (algebraMap K' L) = O') {g ε : L}
    (hg : IsResidueTranscendental O' U g) {e : ℕ} (he : 1 ≤ e) {o : O'} (hou : IsUnit o)
    (hε : U.valuation (ε - algebraMap K' L o) < 1) : IsResidueTranscendental O' U (ε * g ^ e) := by
  have hO : ∀ o : O', algebraMap K' L (o : K') ∈ U := fun o ↦ by
    rw [← ValuationSubring.mem_comap, hU]; exact o.2
  have hεU : ε ∈ U := by
    have : ε = (ε - algebraMap K' L o) + algebraMap K' L o := by ring
    rw [this]
    exact U.add_mem _ _ ((U.valuation_le_one_iff _).mp hε.le) (hO o)
  have hz : algebraMap K' L o * g ^ e ∈ U := U.mul_mem _ _ (hO o) (U.pow_mem hg.1 e)
  refine ⟨U.mul_mem _ _ hεU (U.pow_mem hg.1 e), fun Q hQ ↦ ?_⟩
  set R : O'[X] := Q.comp (C o * X ^ e)
  have hR : R.map (IsLocalRing.residue O') ≠ 0 := by
    rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X]
    intro h
    rcases comp_eq_zero_iff.mp h with h | ⟨-, h⟩
    · exact hQ h
    · have hres : IsLocalRing.residue O' o ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hou
      have := congrArg (fun P ↦ P.coeff e) h
      simp only [coeff_C_mul, coeff_X_pow_self, mul_one, coeff_C] at this
      rw [if_neg (by omega)] at this
      exact hres this
  have h1 := hg.2 R hR
  have hRe : aeval g (R.map (algebraMap O' K')) =
      aeval (algebraMap K' L o * g ^ e) (Q.map (algebraMap O' K')) := by
    rw [Polynomial.map_comp, aeval_comp]
    simp
  rw [hRe] at h1
  have h2 := valuation_aeval_sub_le hO (U.mul_mem _ _ hεU (U.pow_mem hg.1 e)) hz Q
  have h3 : U.valuation (ε * g ^ e - algebraMap K' L o * g ^ e) < 1 := by
    rw [← sub_mul, map_mul, map_pow]
    calc U.valuation (ε - algebraMap K' L o) * U.valuation g ^ e
        ≤ U.valuation (ε - algebraMap K' L o) * 1 :=
          mul_le_mul_right (pow_le_one₀ zero_le ((U.valuation_le_one_iff _).mpr hg.1)) _
      _ < 1 := by rw [mul_one]; exact hε
  have h4 := h2.trans_lt h3
  have : aeval (ε * g ^ e) (Q.map (algebraMap O' K')) =
      aeval (algebraMap K' L o * g ^ e) (Q.map (algebraMap O' K')) +
      (aeval (ε * g ^ e) (Q.map (algebraMap O' K')) -
        aeval (algebraMap K' L o * g ^ e) (Q.map (algebraMap O' K'))) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [h1]; exact h4), h1]

end GaussData

section Unfolded

variable {K' : Type*} [Field K'] [Algebra K' L] {O' : ValuationSubring K'}
  [IsDiscreteValuationRing O']

/-- **An unfolded node germ** (the input from XL1 and XL6): node germs `P` with coordinates
`u v = ϖ' ^ n` (`n ≥ 1`), its two branches `W₁` (`s = 0`) and `W₂` (`s = n`), the only monomial
points at the ends, and the base node coordinate `t = (x - a) / β = ε u ^ e ϖ' ^ α` with `ε` a unit
of `P`, whose monomials `t / ϖ' ^ α = ε u ^ e` and `t / ϖ' ^ (α + e n)` are the Gauss coordinates
of the two branches (transcendental residues). -/
structure UnfoldedNodeGerm (O' : ValuationSubring K') (ϖ' : O') (P : Subring L) (u v : L)
    (n : ℕ) (x : L) (a β : K') (e α : ℕ) (ε : L) (W₁ W₂ : ValuationSubring L) : Prop where
  germ : NodeGerm O' ϖ' P u v n
  one_le_n : 1 ≤ n
  β_ne : β ≠ 0
  one_le_e : 1 ≤ e
  ε_ne : ε ≠ 0
  ε_mem : ε ∈ P
  ε_inv_mem : ε⁻¹ ∈ P
  coord : x - algebraMap K' L a =
    algebraMap K' L β * (ε * u ^ e * algebraMap K' L (ϖ' : K') ^ α)
  isMonomialPt₁ : IsMonomialPt O' (P : Set L) (algebraMap K' L (ϖ' : K')) u 0 W₁
  isMonomialPt₂ : IsMonomialPt O' (P : Set L) (algebraMap K' L (ϖ' : K')) u n W₂
  unique₁ : ∀ U, IsMonomialPt O' (P : Set L) (algebraMap K' L (ϖ' : K')) u 0 U → U = W₁
  unique₂ : ∀ U, IsMonomialPt O' (P : Set L) (algebraMap K' L (ϖ' : K')) u n U → U = W₂
  residue₁ : IsResidueTranscendental O' W₁ (ε * u ^ e)
  residue₂ : IsResidueTranscendental O' W₂ (ε * u ^ e / algebraMap K' L (ϖ' : K') ^ (e * n))

namespace UnfoldedNodeGerm

variable {ϖ' : O'} {P : Subring L} {u v : L} {n : ℕ} {x : L} {a β : K'} {e α : ℕ} {ε : L}
  {W₁ W₂ : ValuationSubring L}

/-- **The restriction of a monomial point of an unfolded node to the x-line** (XL3/XL6): every
extension to `F̄` of the monomial point at `s ∈ [0, n]` restricts to the Gauss point with centre `a`
and normalised log radius `(ord β + α + e s) / e₀`. -/
theorem isXGauss (H : UnfoldedNodeGerm O' ϖ' P u v n x a β e α ε W₁ W₂) (hϖ : Irreducible ϖ')
    {ϖ₀ : K'} {η : O'ˣ} {e₀ : ℕ} (he₀ : 0 < e₀) (hϖ₀ : ϖ₀ = (η : K') * (ϖ' : K') ^ e₀)
    {s : ℚ} (hs0 : 0 ≤ s) (hsn : s ≤ n) {U : ValuationSubring L}
    (hUm : IsMonomialPt O' (P : Set L) (algebraMap K' L (ϖ' : K')) u s U)
    (U' : ValuationSubring (Fbar L)) (hU' : U'.comap (algebraMap L (Fbar L)) = U) :
    IsXGauss (algebraMap L (Fbar L) (algebraMap K' L ϖ₀)) (algebraMap L (Fbar L) x)
      (algebraMap K' (Kbar K' L) a) ((ordO O' ϖ' β + α + e * s) / e₀) U' := by
  have hUO := H.germ.comap_eq hϖ hUm
  set p := algebraMap K' L (ϖ' : K')
  have hϖ0 : (ϖ' : K') ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hp0 : p ≠ 0 := by simpa [p] using hϖ0
  obtain ⟨hwp0, hwp1⟩ := valuation_uniformizer hUO hϖ
  have hβ0 : algebraMap K' L β ≠ 0 := by simpa using H.β_ne
  have hε1 : U.valuation ε = 1 := by
    exact (valuation_eq_one_iff_mem_and_inv_mem U).mpr ⟨H.ε_ne, hUm.1 H.ε_mem, hUm.1 H.ε_inv_mem⟩
  have hxa : U.valuation (x - algebraMap K' L a) =
      U.valuation (algebraMap K' L β) * (U.valuation u ^ e * U.valuation p ^ α) := by
    rw [H.coord, map_mul, map_mul, map_mul, hε1, one_mul, map_pow, map_pow]
  rcases hs0.eq_or_lt with hs | hs0'
  · -- the outer branch
    subst hs
    have hUW : U = W₁ := H.unique₁ U hUm
    have hu1 : U.valuation u = 1 := by
      have := hUm.2.2.1; unfold IsLogValue at this; simpa using this
    have key := isXGauss_of_monomial (x := x) (a := a) (N := α) (d := 1) hUO hϖ H.β_ne one_pos
      ?_ ?_ he₀ hϖ₀ U' hU'
    · convert key using 2 <;> push_cast <;> ring
    · rw [pow_one, hxa, hu1, one_pow, one_mul, pow_one, map_mul, map_mul, map_pow,
        Valuation.map_pow]
    · have : (x - algebraMap K' L a) ^ 1 / algebraMap K' L (β ^ 1 * (ϖ' : K') ^ α) = ε * u ^ e := by
        rw [pow_one, H.coord, pow_one, map_mul, map_pow, mul_div_mul_left _ _ hβ0,
          mul_div_assoc, div_self (pow_ne_zero _ hp0), mul_one]
      rw [this, hUW]; exact H.residue₁
  rcases hsn.eq_or_lt with hs | hsn'
  · -- the inner branch
    subst hs
    have hUW : U = W₂ := H.unique₂ U hUm
    have hun : U.valuation u = U.valuation p ^ n := by
      have := hUm.2.2.1; unfold IsLogValue at this; simpa using this
    have key := isXGauss_of_monomial (x := x) (a := a) (N := α + e * n) (d := 1) hUO hϖ H.β_ne
      one_pos ?_ ?_ he₀ hϖ₀ U' hU'
    · convert key using 2 <;> push_cast <;> ring
    · rw [pow_one, hxa, hun, pow_one, map_mul, map_mul, map_pow, Valuation.map_pow, ← pow_mul,
        ← pow_add, add_comm, mul_comm n e]
    · have : (x - algebraMap K' L a) ^ 1 /
          algebraMap K' L (β ^ 1 * (ϖ' : K') ^ (α + e * n)) =
          ε * u ^ e / algebraMap K' L (ϖ' : K') ^ (e * n) := by
        rw [pow_one, H.coord, pow_one, map_mul, map_pow, mul_div_mul_left _ _ hβ0, pow_add,
          ← div_div, mul_div_assoc, div_self (pow_ne_zero _ hp0), mul_one]
      rw [this, hUW]; exact H.residue₂
  · -- interior points
    obtain ⟨g1, g2, g3⟩ := generator_bounds H.germ.mul_eq hUO hϖ hs0' hsn' hUm.2.2.1
    have hlt1 : ∀ y, U.valuation y ^ s.den ≤ U.valuation p → U.valuation y < 1 := by
      intro y hy
      by_contra hge
      push Not at hge
      exact absurd ((one_le_pow₀ hge).trans hy) (not_le.mpr hwp1)
    have hu1 := hlt1 u g2
    have hv1 := hlt1 v g3
    set d := s.den
    set mN := s.num.toNat
    have hm : (mN : ℤ) = s.num := Int.toNat_of_nonneg (Rat.num_pos.mpr hs0').le
    have hgtr := hUm.2.2.2
    set g := u ^ s.den / p ^ s.num with hg
    have hg' : g = u ^ d / p ^ mN := by rw [hg, ← hm, zpow_natCast]
    have hg1 : U.valuation g = 1 := by
      have := hgtr.2 X (by simp)
      simpa using this
    -- `ε ^ d` is congruent to a unit constant
    obtain ⟨o, a₁, ha₁, b₁, hb₁, c₁, hc₁, hεd⟩ := H.germ.gen (ε ^ d) (P.pow_mem H.ε_mem d)
    have hle1 : ∀ z ∈ P, U.valuation z ≤ 1 := fun z hz ↦ (U.valuation_le_one_iff z).mpr (hUm.1 hz)
    have hεo : U.valuation (ε ^ d - algebraMap K' L (o : K')) < 1 := by
      have : ε ^ d - algebraMap K' L (o : K') = p * a₁ + u * b₁ + v * c₁ := by
        rw [hεd]; ring
      rw [this]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (lt_of_le_of_lt
        (Valuation.map_add _ _ _) (max_lt ?_ ?_)) ?_) <;> rw [map_mul]
      · exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hle1 _ ha₁)) hwp1
      · exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hle1 _ hb₁)) hu1
      · exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hle1 _ hc₁)) hv1
    have hεd1 : U.valuation (ε ^ d) = 1 := by rw [map_pow, hε1, one_pow]
    have ho1 : U.valuation (algebraMap K' L (o : K')) = 1 := by
      have : algebraMap K' L (o : K') = ε ^ d - (ε ^ d - algebraMap K' L (o : K')) := by ring
      rw [this, Valuation.map_sub_eq_of_lt_left _ (by rw [hεd1]; exact hεo), hεd1]
    have hou : IsUnit o := by
      obtain ⟨ho0, -, hinv⟩ := (valuation_eq_one_iff_mem_and_inv_mem U).mp ho1
      rw [← map_inv₀, ← ValuationSubring.mem_comap, hUO] at hinv
      have ho0' : (o : K') ≠ 0 := fun h ↦ ho0 (by rw [h, map_zero])
      exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O') (Subtype.ext (by simp [ho0']))
    have htr' := hgtr.mul_pow hUO H.one_le_e hou hεo
    set N := α * d + e * mN
    have hid : (x - algebraMap K' L a) ^ d / algebraMap K' L (β ^ d * (ϖ' : K') ^ N) =
        ε ^ d * g ^ e := by
      have hp0' : algebraMap K' L (ϖ' : K') ≠ 0 := hp0
      rw [H.coord, hg']
      simp only [p, N, map_mul, map_pow, pow_add, pow_mul]
      simp only [div_pow]
      field_simp [hp0', hβ0]
      ring
    have hy : U.valuation (x - algebraMap K' L a) ^ d =
        U.valuation (algebraMap K' L (β ^ d * (ϖ' : K') ^ N)) := by
      have hc0 : algebraMap K' L (β ^ d * (ϖ' : K') ^ N) ≠ 0 := by
        simp [H.β_ne, hϖ0]
      have : (x - algebraMap K' L a) ^ d =
          algebraMap K' L (β ^ d * (ϖ' : K') ^ N) * (ε ^ d * g ^ e) := by
        rw [← hid, mul_div_cancel₀ _ hc0]
      rw [← map_pow, this, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow,
        Valuation.map_pow, hε1, hg1, one_pow, one_pow, mul_one, mul_one]
    have key := isXGauss_of_monomial (x := x) (a := a) (N := N) (d := d) hUO hϖ H.β_ne s.den_pos
      hy (by rw [hid]; exact htr') he₀ hϖ₀ U' hU'
    have hs : s = (mN : ℚ) / d := by
      rw [show ((mN : ℚ)) = ((mN : ℤ) : ℚ) by norm_cast, hm]
      exact (Rat.num_div_den s).symm
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast s.den_nz
    have he0 : (e₀ : ℚ) ≠ 0 := by exact_mod_cast he₀.ne'
    have hρ : (ordO O' ϖ' β + α + e * s) / e₀ =
        (((d : ℤ) * ordO O' ϖ' β + N : ℤ) : ℚ) / ((d * e₀ : ℕ) : ℚ) := by
      rw [hs]
      simp only [N]
      push_cast
      field_simp
      ring
    rw [hρ]
    exact key

/-- **The x-length of an unfolded node** (XL3/XL6, hence X0 for unfolded models): every chain
has length `e n / e₀` (the x-path is monotone, `ρ` linear in `s`), and the chain through the two
branches exists; so `λ = e n / e₀`. -/
theorem isXLength (H : UnfoldedNodeGerm O' ϖ' P u v n x a β e α ε W₁ W₂)
    (hϖ : Irreducible ϖ') {ϖ₀ : K'} {η : O'ˣ} {e₀ : ℕ} (he₀ : 0 < e₀)
    (hϖ₀ : ϖ₀ = (η : K') * (ϖ' : K') ^ e₀) :
    IsXLength O' (P : Set L) (algebraMap K' L ϖ₀) (algebraMap K' L (ϖ' : K')) u x n
      ((e * n : ℚ) / e₀) := by
  set ρf : ℚ → ℚ := fun s ↦ (ordO O' ϖ' β + α + e * s) / e₀ with hρf
  have hϖ0 : (ϖ' : K') ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hη0 : ((η : O') : K') ≠ 0 := fun h ↦ η.ne_zero (Subtype.ext h)
  have hϖ₀0 : ϖ₀ ≠ 0 := by rw [hϖ₀]; exact mul_ne_zero hη0 (pow_ne_zero _ hϖ0)
  have hϖ₀O : ϖ₀ ∈ O' := by
    rw [hϖ₀]; exact O'.mul_mem _ _ (η : O').2 (O'.pow_mem ϖ'.2 _)
  have hϖ₀inv : ϖ₀⁻¹ ∉ O' := by
    intro h
    apply hϖ.not_isUnit
    have hu : IsUnit (⟨ϖ₀, hϖ₀O⟩ : O') :=
      IsUnit.of_mul_eq_one (⟨_, h⟩ : O') (Subtype.ext (by simp [hϖ₀0]))
    have : (⟨ϖ₀, hϖ₀O⟩ : O') = (η : O') * ϖ' ^ e₀ := Subtype.ext (by simp [hϖ₀])
    rw [this] at hu
    exact (isUnit_pow_iff he₀.ne').mp (isUnit_of_mul_isUnit_right hu)
  -- the values of `ϖ₀` at the extensions
  have hval : ∀ (U : ValuationSubring L) (s : ℚ),
      IsMonomialPt O' (P : Set L) (algebraMap K' L (ϖ' : K')) u s U →
      ∀ U' : ValuationSubring (Fbar L), U'.comap (algebraMap L (Fbar L)) = U →
      U'.valuation (algebraMap L (Fbar L) (algebraMap K' L ϖ₀)) ≠ 0 ∧
      U'.valuation (algebraMap L (Fbar L) (algebraMap K' L ϖ₀)) < 1 := by
    intro U s hU U' hU'
    have hUO := H.germ.comap_eq hϖ hU
    have hU'O : U'.comap (algebraMap K' (Fbar L)) = O' := by
      rw [IsScalarTower.algebraMap_eq K' L (Fbar L), ← ValuationSubring.comap_comap, hU', hUO]
    rw [← IsScalarTower.algebraMap_apply]
    exact ⟨by simpa using hϖ₀0, valuation_lt_one_of_comap_eq hU'O hϖ₀O hϖ₀inv⟩
  refine ⟨?_, ?_⟩
  · -- the chain through the two branches
    obtain ⟨U'₁, hU'₁⟩ := exists_valuationSubring_comap_eq (F := Fbar L) W₁
    obtain ⟨U'₂, hU'₂⟩ := exists_valuationSubring_comap_eq (F := Fbar L) W₂
    have hn : (0 : ℚ) < n := by exact_mod_cast H.one_le_n
    let γ : XChain O' (P : Set L) (algebraMap K' L ϖ₀) (algebraMap K' L (ϖ' : K')) u x n :=
      { m := 1
        s := ![0, n]
        U := ![W₁, W₂]
        U' := ![U'₁, U'₂]
        a := fun _ ↦ algebraMap K' (Kbar K' L) a
        ρ := ![ρf 0, ρf n]
        s_zero := rfl
        s_last := rfl
        strictMono := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all
        isMonomialPt := by
          intro i
          fin_cases i
          · exact H.isMonomialPt₁
          · exact_mod_cast H.isMonomialPt₂
        comap_eq := by
          intro i
          fin_cases i
          · exact hU'₁
          · exact hU'₂
        isXGauss := by
          intro i
          fin_cases i
          · exact H.isXGauss hϖ he₀ hϖ₀ le_rfl hn.le H.isMonomialPt₁ U'₁ hU'₁
          · exact H.isXGauss hϖ he₀ hϖ₀ hn.le le_rfl (by exact_mod_cast H.isMonomialPt₂) U'₂
              hU'₂ }
    refine ⟨γ, ?_⟩
    simp only [XChain.length, γ, ρf]
    simp only [Fin.sum_univ_one, Fin.succ_zero_eq_one, Fin.castSucc_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    have he0 : (e₀ : ℚ) ≠ 0 := by exact_mod_cast he₀.ne'
    rw [show (ordO O' ϖ' β + α + e * (n : ℚ)) / e₀ - (ordO O' ϖ' β + α + e * 0) / e₀ =
      e * n / e₀ by field_simp; ring]
    exact abs_of_nonneg (by positivity)
  · -- every chain has this length
    rintro _ ⟨γ, rfl⟩
    have hρ : ∀ i, γ.ρ i = (ordO O' ϖ' β + α) / e₀ + (e / e₀) * γ.s i := by
      intro i
      have hs0 : 0 ≤ γ.s i := by
        rw [← γ.s_zero]; exact γ.strictMono.monotone (Fin.zero_le i)
      have hsn : γ.s i ≤ n := by
        rw [← γ.s_last]; exact γ.strictMono.monotone (Fin.le_last i)
      have hG := H.isXGauss hϖ he₀ hϖ₀ hs0 hsn (γ.isMonomialPt i) (γ.U' i) (γ.comap_eq i)
      obtain ⟨h0, h1⟩ := hval _ _ (γ.isMonomialPt i) _ (γ.comap_eq i)
      rw [IsXGauss.rho_unique h0 h1 (γ.isXGauss i) hG]
      have he0 : (e₀ : ℚ) ≠ 0 := by exact_mod_cast he₀.ne'
      field_simp
    have hk : (0 : ℚ) ≤ e / e₀ := by positivity
    rw [XChain.length, sum_abs_sub_of_linear γ.s γ.ρ γ.strictMono hk hρ, γ.s_last, γ.s_zero]
    rw [sub_zero, div_mul_eq_mul_div]

/-- **(X0) for unfolded nodes**: the x-length exists and is positive. -/
theorem exists_isXLength_pos (H : UnfoldedNodeGerm O' ϖ' P u v n x a β e α ε W₁ W₂)
    (hϖ : Irreducible ϖ') {ϖ₀ : K'} {η : O'ˣ} {e₀ : ℕ} (he₀ : 0 < e₀)
    (hϖ₀ : ϖ₀ = (η : K') * (ϖ' : K') ^ e₀) :
    (∃ l, IsXLength O' (P : Set L) (algebraMap K' L ϖ₀) (algebraMap K' L (ϖ' : K')) u x n l) ∧
    ∀ l, IsXLength O' (P : Set L) (algebraMap K' L ϖ₀) (algebraMap K' L (ϖ' : K')) u x n l →
      0 < l := by
  have h := H.isXLength hϖ he₀ hϖ₀
  refine ⟨⟨_, h⟩, fun l hl ↦ ?_⟩
  rw [hl.unique h]
  have : (1 : ℚ) ≤ e := by exact_mod_cast H.one_le_e
  have : (1 : ℚ) ≤ n := by exact_mod_cast H.one_le_n
  positivity

end UnfoldedNodeGerm

end Unfolded

end SemistableReduction
