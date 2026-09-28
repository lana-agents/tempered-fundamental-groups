/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.PthPower
import TemperedFundamentalGroups.SemistableReduction.UnramifiedRoot
import TemperedFundamentalGroups.SemistableReduction.FrobeniusBasis
import TemperedFundamentalGroups.SemistableReduction.DenseCompletion

/-!
# The Kummer normal form in mixed characteristic

Blueprint §9.4, F4 (Kuhlmann, *Elimination of ramification I*, Proposition 4.13).

## Residue tests

Let `M` be a non-archimedean normed field whose residue field `κ` has characteristic `p`, `E / M`
a finite extension with a valuation `w` extending the norm valuation of `M`, and `ϑ ∈ E` with
`ϑ ^ p = 1 + b`, `b ∈ M`. Fix `γ` with `γ ^ (p - 1) = -p`.

* `le_inertiaDeg_of_insep`: if `‖γ‖ < ‖t‖ ≤ 1`, `‖b‖ ≤ ‖t‖ ^ p` and the residue of `b / t ^ p`
  is not a `p`-th power, then `p ≤ f(w | M)`: `χ = (ϑ - 1) / t` is integral with reduced
  equation `χ̄ ^ p = (b / t ^ p)‾` (the purely inseparable case).
* `le_inertiaDeg_of_sep`: if `‖b‖ ≤ ‖γ‖ ^ p` and the residue of `b / γ ^ p` is not of the form
  `z ^ p - z`, then `p ≤ f(w | M)`: `χ = (ϑ - 1) / γ` has reduced equation
  `χ̄ ^ p - χ̄ = (b / γ ^ p)‾` (the separable, Artin–Schreier case).

The second test needs `irreducible_X_pow_sub_X_sub_C`: over a field of characteristic `p`, an
Artin–Schreier polynomial `X ^ p - X - a` without root is irreducible (the roots of a factor are
`α + j`, `j ∈ 𝔽_p`, so the sum of its roots determines `α` unless its degree is divisible by `p`).

## The normal form

Let `C ⊆ M` be algebraically closed, `M` complete, and `L : LiftedFrobeniusBasis C M p`: a
Frobenius-closed basis `B = {1} ⊔ {ū_q ^ p ^ n}` of `κ` over the residue field `k` of `C`
(Blueprint E2), lifts `u_q` with `‖u_q‖ ≤ 1`, and density of the `C`-span of
`bᵢ ∈ {1} ⊔ {u_q ^ p ^ n}` in `M` (Blueprint F2). Then `‖Σ cᵢ bᵢ‖ = max ‖cᵢ‖` (`nnnorm_val`,
from A1). `exists_visible`: every `a ∈ M ∖ 0` that is not a `p`-th power becomes, after
multiplication by a `p`-th power, a `1`-unit `1 + b` in one of the two forms of the residue tests
(`Visible`). The procedure (Kuhlmann, Proposition 4.13, made effective):

1. scale `a` to norm `1` (value group of `M` = value group of `C`, `exists_norm_eq`); if `ā` is
   not a `p`-th power, we are done; otherwise divide by a lift of `ā^{1/p}` to get a `1`-unit;
2. approximate the `1`-unit by `1 + Σ cᵢ bᵢ` up to `‖γ‖ ^ p` (density and Corollary 2.12 a);
3. `phase1`: remove all terms `cᵢ bᵢ` with `bᵢ` a `p`-th power of a basis element and
   `‖cᵢ‖ ≥ ‖p‖`, by dividing by `(1 + Σ cᵢ^{1/p} b_{root i}) ^ p`; the new error terms are
   smaller by a fixed factor `max ρ ‖π‖ < 1` (`‖π‖ ^ p = ‖p‖`), so finitely many steps suffice
   (`phase1_step`);
4. if some coefficient exceeds `‖γ‖`, the leading terms are at the `u_q` and we are done;
   otherwise remove the constant term (`remove_const`) and replace every remaining term
   `c b_{root i} ^ p` by `-p c^{1/p} b_{root i}` (Corollary 2.12 d, `phase2`, induction on the
   Frobenius depth);
5. terms of norm `< ‖γ‖ ^ p` are `p`-th powers (Lemma 2.11); the leading residue then lies in
   `Span_k ū ∖ 0`, which meets neither `κ^p` nor `℘(κ)` (E2), `visible_of_leading`.

**F4** (`le_inertiaDeg_of_pow_eq`, `defectless_of_pow_eq`): if `ϑ ^ p = a` with `a ∈ M ∖ M^p`,
then `f(M(ϑ) | M) ≥ p`, so a Kummer extension of degree `p` of `M` is defectless.
-/

open Polynomial IsLocalRing Valuation

namespace SemistableReduction

namespace KummerNormalForm

section ArtinSchreier

variable {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]

/-- **Artin–Schreier polynomials.** Over a field of characteristic `p`, `X ^ p - X - a` is
irreducible if it has no root. -/
theorem irreducible_X_pow_sub_X_sub_C {a : F} (ha : ∀ x : F, x ^ p - x ≠ a) :
    Irreducible (X ^ p - X - C a : F[X]) := by
  classical
  have hp2 := hp.out.two_le
  set f : F[X] := X ^ p - X - C a with hf
  have hfdeg : f.natDegree = p := by
    rw [hf, natDegree_sub_C, natDegree_sub_eq_left_of_natDegree_lt
      (by rw [natDegree_X, natDegree_X_pow]; omega), natDegree_X_pow]
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hfdeg
    omega
  -- every irreducible factor of `f` has degree `≥ p`
  have key : ∀ g : F[X], Irreducible g → g ∣ f → p ≤ g.natDegree := by
    intro g hg hgf
    haveI := Fact.mk hg
    set L := AdjoinRoot g
    set i : F →+* L := AdjoinRoot.of g
    set α : L := AdjoinRoot.root g
    have hinj : Function.Injective i := i.injective
    haveI : CharP L p := charP_of_injective_algebraMap hinj p
    set ι : ZMod p →+* L := ZMod.castHom (dvd_refl p) L
    have hι : Function.Injective ι := ι.injective
    have hfα : (f.map i).IsRoot α := by
      obtain ⟨h, hh⟩ := hgf
      rw [hh, Polynomial.map_mul, IsRoot, eval_mul]
      rw [(AdjoinRoot.isRoot_root g).eq_zero, zero_mul]
    have hfα' : α ^ p - α - i a = 0 := by
      simpa [hf, IsRoot] using hfα
    have hroot (j : ZMod p) : (f.map i).IsRoot (α + ι j) := by
      simp only [hf, IsRoot, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub,
        eval_pow, eval_X, eval_C]
      rw [add_pow_char, ← map_pow, ZMod.pow_card]
      linear_combination hfα'
    set T : Finset L := Finset.univ.image fun j : ZMod p ↦ α + ι j
    have hTcard : T.card = p := by
      rw [Finset.card_image_of_injective _ fun j j' h ↦ hι (add_left_cancel h), Finset.card_univ,
        ZMod.card]
    have hfm0 : f.map i ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hf0
    have hTle : T.val ≤ (f.map i).roots := by
      rw [Multiset.le_iff_subset T.nodup]
      intro r hr
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hr
      exact (mem_roots hfm0).2 (hroot j)
    have hdeg : (f.map i).natDegree = p := by rw [natDegree_map, hfdeg]
    have hTeq : T.val = (f.map i).roots :=
      Multiset.eq_of_le_of_card_le hTle (by
        rw [Finset.card_val, hTcard, ← hdeg]
        exact card_roots' _)
    have hsplit : (f.map i).Splits := splits_iff_card_roots.2 (by rw [← hTeq, hdeg]; exact hTcard)
    have hgdvd : g.map i ∣ f.map i := Polynomial.map_dvd i hgf
    have hgsplit : (g.map i).Splits := hsplit.of_dvd hfm0 hgdvd
    have hgroots : (g.map i).roots ≤ (f.map i).roots := roots.le_of_dvd hfm0 hgdvd
    -- the roots of `g` are `α + j`
    have hmemr : ∀ r ∈ (g.map i).roots, r - α ∈ ι.range := by
      intro r hr
      have : r ∈ T.val := hTeq ▸ Multiset.mem_of_le hgroots hr
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 this
      exact ⟨j, by ring⟩
    set d := g.natDegree
    have hcard : (g.map i).roots.card = d := by
      rw [← hgsplit.natDegree_eq_card_roots, natDegree_map]
    have hsum : (g.map i).roots.sum =
        (d : L) * α + ((g.map i).roots.map fun r ↦ r - α).sum := by
      conv_lhs => rw [← Multiset.map_id' (g.map i).roots]
      rw [show (fun x : L ↦ x) = fun r ↦ α + (r - α) from funext fun r ↦ by ring,
        Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul]
    obtain ⟨s, hs⟩ : ((g.map i).roots.map fun r ↦ r - α).sum ∈ ι.range :=
      multiset_sum_mem _ fun x hx ↦ by
        obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
        exact hmemr r hr
    have hιi : ι = i.comp (ZMod.castHom (dvd_refl p) F) := RingHom.ext_zmod _ _
    have hnext := hgsplit.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
    rw [nextCoeff_map hinj, leadingCoeff_map, hsum, ← hs, hιi, RingHom.comp_apply] at hnext
    have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hg.ne_zero
    by_contra hlt
    push Not at hlt
    have hd0 : 0 < d := hg.natDegree_pos
    have hdL : (d : L) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff L p]
      exact fun h ↦ (Nat.le_of_dvd hd0 h).not_gt hlt
    set β : F := (-(g.nextCoeff / g.leadingCoeff) - ZMod.castHom (dvd_refl p) F s) / d
    have hi_lc : i g.leadingCoeff ≠ 0 := (map_ne_zero_iff i hinj).2 hlc
    have hq : i g.nextCoeff / i g.leadingCoeff =
        -((d : L) * α + i (ZMod.castHom (dvd_refl p) F s)) := by
      rw [hnext, div_eq_iff hi_lc]
      ring
    have h1 : (d : L) * α = i (-(g.nextCoeff / g.leadingCoeff) -
        ZMod.castHom (dvd_refl p) F s) := by
      rw [_root_.map_sub, _root_.map_neg, map_div₀, hq]
      ring
    have hαβ : α = i β := by
      rw [map_div₀, map_natCast, ← h1, mul_div_cancel_left₀ _ hdL]
    apply ha β
    have : i (β ^ p - β - a) = 0 := by
      rw [_root_.map_sub, _root_.map_sub, map_pow, ← hαβ]
      exact hfα'
    exact sub_eq_zero.1 ((map_eq_zero_iff i hinj).1 this)
  -- hence `f` is irreducible
  have hfu : ¬IsUnit f := fun h ↦ by
    have := natDegree_eq_zero_of_isUnit h
    omega
  refine ⟨hfu, fun g h hgh ↦ ?_⟩
  by_contra! hne
  obtain ⟨g₁, hg₁, hg₁g⟩ := WfDvdMonoid.exists_irreducible_factor hne.1
    (fun h0 ↦ hf0 (by rw [hgh, h0, zero_mul]))
  obtain ⟨h₁, hh₁, hh₁h⟩ := WfDvdMonoid.exists_irreducible_factor hne.2
    (fun h0 ↦ hf0 (by rw [hgh, h0, mul_zero]))
  have hg0 : g ≠ 0 := fun h0 ↦ hf0 (by rw [hgh, h0, zero_mul])
  have hh0 : h ≠ 0 := fun h0 ↦ hf0 (by rw [hgh, h0, mul_zero])
  have h1 := key g₁ hg₁ (hg₁g.trans ⟨h, hgh⟩)
  have h2 := key h₁ hh₁ (hh₁h.trans ⟨g, by rw [hgh, mul_comm]⟩)
  have h3 := natDegree_le_of_dvd hg₁g hg0
  have h4 := natDegree_le_of_dvd hh₁h hh0
  have h5 : f.natDegree = g.natDegree + h.natDegree := by rw [hgh, natDegree_mul hg0 hh0]
  omega

end ArtinSchreier

section Residue

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => HenselComplete.integers K

/-- The residue of an element of norm `≤ 1` (and `0` for other elements). -/
noncomputable def rd (x : K) : ResidueField 𝒪 :=
  if h : ‖x‖ ≤ 1 then residue 𝒪 ⟨x, (HenselComplete.mem_integers_iff x).2 h⟩ else 0

lemma rd_coe (x : 𝒪) : rd (x : K) = residue 𝒪 x := by
  rw [rd, dif_pos (HenselComplete.norm_le_one x)]

lemma rd_eq_zero_iff {x : K} (hx : ‖x‖ ≤ 1) : rd x = 0 ↔ ‖x‖ < 1 := by
  rw [rd, dif_pos hx, residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one]

lemma rd_eq_zero {x : K} (hx : ‖x‖ < 1) : rd x = 0 := (rd_eq_zero_iff hx.le).2 hx

lemma rd_add {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : rd (x + y) = rd x + rd y := by
  set x' : 𝒪 := ⟨x, (HenselComplete.mem_integers_iff x).2 hx⟩
  set y' : 𝒪 := ⟨y, (HenselComplete.mem_integers_iff y).2 hy⟩
  rw [show x + y = ((x' + y' : 𝒪) : K) from rfl, rd_coe, map_add, ← rd_coe, ← rd_coe]

lemma rd_mul {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : rd (x * y) = rd x * rd y := by
  set x' : 𝒪 := ⟨x, (HenselComplete.mem_integers_iff x).2 hx⟩
  set y' : 𝒪 := ⟨y, (HenselComplete.mem_integers_iff y).2 hy⟩
  rw [show x * y = ((x' * y' : 𝒪) : K) from rfl, rd_coe, map_mul, ← rd_coe, ← rd_coe]

lemma rd_neg (x : K) : rd (-x) = -rd x := by
  by_cases hx : ‖x‖ ≤ 1
  · set x' : 𝒪 := ⟨x, (HenselComplete.mem_integers_iff x).2 hx⟩
    rw [show -x = ((-x' : 𝒪) : K) from rfl, rd_coe, _root_.map_neg, ← rd_coe]
  · rw [rd, rd, dif_neg (by rwa [norm_neg]), dif_neg hx, neg_zero]

lemma rd_one : rd (1 : K) = 1 := by
  rw [show (1 : K) = ((1 : 𝒪) : K) from rfl, rd_coe, map_one]

lemma rd_pow {x : K} (hx : ‖x‖ ≤ 1) (n : ℕ) : rd (x ^ n) = rd x ^ n := by
  set x' : 𝒪 := ⟨x, (HenselComplete.mem_integers_iff x).2 hx⟩
  rw [show x ^ n = ((x' ^ n : 𝒪) : K) from rfl, rd_coe, map_pow, ← rd_coe]

/-- The residue field has characteristic `p` if `‖p‖ < 1`. -/
lemma charP_residueField {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) :
    CharP (ResidueField 𝒪) p := by
  rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (residue 𝒪) p, residue_eq_zero_iff,
    HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
  simpa using hp1

variable {E : Type*} [Field E] [Algebra K E] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (w : Valuation E Γ) [(NormedField.valuation (K := K)).HasExtension w]

/-- A root in `E` of a monic polynomial over the ring of integers of `K` with irreducible
reduction bounds the inertia degree from below. -/
theorem natDegree_le_inertiaDeg_of_aeval [FiniteDimensional K E] {g : 𝒪[X]} (hg : g.Monic)
    (hirr : Irreducible (g.map (residue 𝒪))) {χ : E}
    (hχ : aeval χ (g.map (algebraMap 𝒪 K)) = 0) :
    g.natDegree ≤ FundamentalInequality.inertiaDeg (NormedField.valuation (K := K)) w := by
  have hcomp : (algebraMap w.valuationSubring E).comp (algebraMap 𝒪 w.valuationSubring) =
      (algebraMap K E).comp (algebraMap 𝒪 K) := by
    ext x
    exact HasExtension.coe_algebraMap_valuationSubring_eq (NormedField.valuation (K := K)) w x
  have hint : IsIntegral w.valuationSubring χ := by
    refine ⟨g.map (algebraMap 𝒪 w.valuationSubring), hg.map _, ?_⟩
    rw [eval₂_map, hcomp, ← eval₂_map, ← aeval_def]
    exact hχ
  have hmem : χ ∈ w.valuationSubring :=
    (Valuation.valuationSubring.integers w).mem_of_integral hint
  refine FundamentalInequality.natDegree_le_inertiaDeg hg hirr (y := ⟨χ, hmem⟩) ?_
  apply Subtype.val_injective
  rw [ZeroMemClass.coe_zero, ← hχ, aeval_map_algebraMap]
  exact (aeval_algebraMap_apply E (⟨χ, hmem⟩ : w.valuationSubring) g).symm

end Residue

section Shift

variable {K : Type*} [Field K]

/-- `(X + t⁻¹) ^ p - (1 + b) / t ^ p`: if `ϑ ^ p = 1 + b`, then `(ϑ - 1) / t` is a root. -/
noncomputable def shiftPoly (p : ℕ) (t b : K) : K[X] := (X + C t⁻¹) ^ p - C ((1 + b) / t ^ p)

lemma coeff_shiftPoly (p : ℕ) {t : K} (ht : t ≠ 0) (b : K) (k : ℕ) :
    (shiftPoly p t b).coeff k =
      if k = 0 then -(b / t ^ p) else t⁻¹ ^ (p - k) * (p.choose k : K) := by
  simp only [shiftPoly, coeff_sub, coeff_X_add_C_pow, coeff_C]
  split_ifs with hk
  · subst hk
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, inv_pow]
    field_simp
    ring
  · rw [sub_zero]

lemma monic_shiftPoly {p : ℕ} (hp : 0 < p) (t b : K) : (shiftPoly p t b).Monic := by
  refine ((monic_X_add_C _).pow p).sub_of_left ?_
  rw [degree_pow, degree_X_add_C, nsmul_eq_mul, mul_one]
  exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hp)

lemma natDegree_shiftPoly {p : ℕ} (t b : K) : (shiftPoly p t b).natDegree = p := by
  rw [shiftPoly, natDegree_sub_C, natDegree_pow, natDegree_X_add_C, mul_one]

lemma aeval_shiftPoly {E : Type*} [Field E] [Algebra K E] {p : ℕ} {t b : K} (ht : t ≠ 0)
    {ϑ : E} (hϑ : ϑ ^ p = algebraMap K E (1 + b)) :
    aeval ((ϑ - 1) / algebraMap K E t) (shiftPoly p t b) = 0 := by
  have ht' : algebraMap K E t ≠ 0 := (map_ne_zero_iff _ (algebraMap K E).injective).2 ht
  rw [shiftPoly, _root_.map_sub, _root_.map_pow, _root_.map_add, aeval_X, aeval_C, aeval_C,
    map_inv₀, map_div₀,
    _root_.map_pow, show (ϑ - 1) / algebraMap K E t + (algebraMap K E t)⁻¹ = ϑ / algebraMap K E t by
      field_simp; ring, div_pow, hϑ, sub_self]

end Shift

section Tests

variable {M : Type*} [NormedField M] [IsUltrametricDist M]
  {E : Type*} [Field E] [Algebra M E] [FiniteDimensional M E]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (w : Valuation E Γ) [(NormedField.valuation (K := M)).HasExtension w]
  {p : ℕ} (hp : p.Prime) {γ : M} (hγ : γ ^ (p - 1) = -(p : M))

local notation "𝒪" => HenselComplete.integers M

omit [IsUltrametricDist M] in
lemma norm_coeff_shiftPoly_le {t : M} (ht : t ≠ 0) (b : M) {k : ℕ} (hk : k ≠ 0)
    (hle : ∀ j, j ≠ 0 → j < p → ‖(p.choose j : M)‖ ≤ ‖t‖ ^ (p - j)) :
    ‖(shiftPoly p t b).coeff k‖ ≤ 1 := by
  rw [coeff_shiftPoly p ht, if_neg hk]
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  rcases lt_trichotomy k p with hkp | rfl | hkp
  · rw [norm_mul, norm_pow, norm_inv]
    calc ‖t‖⁻¹ ^ (p - k) * ‖(p.choose k : M)‖ ≤ ‖t‖⁻¹ ^ (p - k) * ‖t‖ ^ (p - k) :=
          mul_le_mul_of_nonneg_left (hle k hk hkp) (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ htn.ne', one_pow]
  · simp
  · rw [Nat.choose_eq_zero_of_lt hkp]
    simp

omit [IsUltrametricDist M] in
lemma norm_coeff_shiftPoly_lt {t : M} (ht : t ≠ 0) (b : M) {k : ℕ} (hk : k ≠ 0)
    (hlt : ‖(p.choose k : M)‖ < ‖t‖ ^ (p - k)) :
    ‖(shiftPoly p t b).coeff k‖ < 1 := by
  rw [coeff_shiftPoly p ht, if_neg hk]
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  rw [norm_mul, norm_pow, norm_inv]
  calc ‖t‖⁻¹ ^ (p - k) * ‖(p.choose k : M)‖ < ‖t‖⁻¹ ^ (p - k) * ‖t‖ ^ (p - k) :=
        mul_lt_mul_of_pos_left hlt (by positivity)
    _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ htn.ne', one_pow]

include hp hγ

/-- **Residue test, purely inseparable case.** If `ϑ ^ p = 1 + b` with `‖b‖ ≤ ‖t‖ ^ p`,
`‖γ‖ < ‖t‖ ≤ 1`, and the residue of `b / t ^ p` is not a `p`-th power, then `p ≤ f(w | M)`. -/
theorem le_inertiaDeg_of_insep {ϑ : E} {b t : M} (hϑ : ϑ ^ p = algebraMap M E (1 + b))
    (ht : ‖γ‖ < ‖t‖) (ht1 : ‖t‖ ≤ 1) (hb : ‖b‖ ≤ ‖t‖ ^ p)
    (hres : ∀ z : ResidueField 𝒪, z ^ p ≠ rd (b / t ^ p)) :
    p ≤ FundamentalInequality.inertiaDeg (NormedField.valuation (K := M)) w := by
  have ht0 : t ≠ 0 := norm_pos_iff.1 ((norm_nonneg γ).trans_lt ht)
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  set P := shiftPoly p t b with hP
  have hlt : ∀ j, j ≠ 0 → j < p → ‖(p.choose j : M)‖ < ‖t‖ ^ (p - j) := by
    intro j hj hjp
    calc ‖(p.choose j : M)‖ ≤ ‖(p : M)‖ := PthPower.norm_choose_le hp hj hjp
      _ = ‖γ‖ ^ (p - 1) := (PthPower.norm_gamma_pow_sub_one hγ).symm
      _ < ‖t‖ ^ (p - 1) := pow_lt_pow_left₀ ht (norm_nonneg _) (by have := hp.two_le; omega)
      _ ≤ ‖t‖ ^ (p - j) := pow_le_pow_of_le_one htn.le ht1 (by omega)
  have hbound : ∀ k, ‖P.coeff k‖ ≤ 1 := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [hP, coeff_shiftPoly p ht0, if_pos rfl, norm_neg, norm_div, norm_pow]
      exact div_le_one_of_le₀ hb (by positivity)
    · exact norm_coeff_shiftPoly_le ht0 b hk fun j hj hjp ↦ (hlt j hj hjp).le
  obtain ⟨g, hg⟩ := PthPower.exists_map_eq P hbound
  have hgm : g.Monic := monic_of_injective (fun _ _ h ↦ Subtype.ext h)
    (by rw [hg]; exact monic_shiftPoly hp.pos t b)
  have hgdeg : g.natDegree = p := by
    rw [← natDegree_map_eq_of_injective (f := algebraMap 𝒪 M) (fun _ _ h ↦ Subtype.ext h) g]
    exact (congrArg natDegree hg).trans (natDegree_shiftPoly t b)
  have hcoeff (k : ℕ) : (g.map (residue 𝒪)).coeff k = rd (P.coeff k) := by
    rw [coeff_map, ← rd_coe, ← hg, coeff_map]
    rfl
  have hred : g.map (residue 𝒪) = X ^ p - C (rd (b / t ^ p)) := by
    ext k
    rw [hcoeff, coeff_sub, coeff_X_pow, coeff_C]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [hP, coeff_shiftPoly p ht0, if_pos rfl, if_neg hp.ne_zero.symm, if_pos rfl, rd_neg,
        zero_sub]
    rw [if_neg hk, sub_zero]
    rcases lt_trichotomy k p with hkp | rfl | hkp
    · rw [if_neg hkp.ne, rd_eq_zero (norm_coeff_shiftPoly_lt ht0 b hk (hlt k hk hkp))]
    · rw [if_pos rfl, hP, coeff_shiftPoly k ht0, if_neg hk, Nat.sub_self, pow_zero,
        Nat.choose_self, Nat.cast_one, mul_one, rd_one]
    · rw [if_neg hkp.ne', hP, coeff_shiftPoly p ht0, if_neg hk, Nat.choose_eq_zero_of_lt hkp,
        Nat.cast_zero, mul_zero]
      exact (rd_eq_zero_iff (by simp)).2 (by simp)
  have hirr : Irreducible (g.map (residue 𝒪)) := by
    rw [hred]
    exact X_pow_sub_C_irreducible_of_prime hp hres
  rw [← hgdeg]
  exact natDegree_le_inertiaDeg_of_aeval w hgm hirr (χ := (ϑ - 1) / algebraMap M E t)
    (by rw [hg]; exact aeval_shiftPoly ht0 hϑ)

/-- **Residue test, separable (Artin–Schreier) case.** If `ϑ ^ p = 1 + b` with
`‖b‖ ≤ ‖γ‖ ^ p` and the residue of `b / γ ^ p` is not of the form `z ^ p - z`, then
`p ≤ f(w | M)`. -/
theorem le_inertiaDeg_of_sep (hp0 : (p : M) ≠ 0) (hp1 : ‖(p : M)‖ < 1) {ϑ : E} {b : M}
    (hϑ : ϑ ^ p = algebraMap M E (1 + b)) (hb : ‖b‖ ≤ ‖γ‖ ^ p)
    (hres : ∀ z : ResidueField 𝒪, z ^ p - z ≠ rd (b / γ ^ p)) :
    p ≤ FundamentalInequality.inertiaDeg (NormedField.valuation (K := M)) w := by
  haveI := Fact.mk hp
  haveI := charP_residueField hp hp1
  have hγ0 : γ ≠ 0 := PthPower.gamma_ne_zero hp hγ hp0
  have hγn : 0 < ‖γ‖ := norm_pos_iff.2 hγ0
  have hγ1 : ‖γ‖ < 1 := PthPower.norm_gamma_lt_one hp hγ hp1
  set P := shiftPoly p γ b with hP
  have hle : ∀ j, j ≠ 0 → j < p → ‖(p.choose j : M)‖ ≤ ‖γ‖ ^ (p - j) := by
    intro j hj hjp
    calc ‖(p.choose j : M)‖ ≤ ‖(p : M)‖ := PthPower.norm_choose_le hp hj hjp
      _ = ‖γ‖ ^ (p - 1) := (PthPower.norm_gamma_pow_sub_one hγ).symm
      _ ≤ ‖γ‖ ^ (p - j) := pow_le_pow_of_le_one hγn.le hγ1.le (by omega)
  have hlt : ∀ j, 1 < j → j < p → ‖(p.choose j : M)‖ < ‖γ‖ ^ (p - j) := by
    intro j hj hjp
    calc ‖(p.choose j : M)‖ ≤ ‖(p : M)‖ := PthPower.norm_choose_le hp (by omega) hjp
      _ = ‖γ‖ ^ (p - 1) := (PthPower.norm_gamma_pow_sub_one hγ).symm
      _ < ‖γ‖ ^ (p - j) := pow_lt_pow_right_of_lt_one₀ hγn hγ1 (by omega)
  have hbound : ∀ k, ‖P.coeff k‖ ≤ 1 := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [hP, coeff_shiftPoly p hγ0, if_pos rfl, norm_neg, norm_div, norm_pow]
      exact div_le_one_of_le₀ hb (by positivity)
    · exact norm_coeff_shiftPoly_le hγ0 b hk hle
  obtain ⟨g, hg⟩ := PthPower.exists_map_eq P hbound
  have hgm : g.Monic := monic_of_injective (fun _ _ h ↦ Subtype.ext h)
    (by rw [hg]; exact monic_shiftPoly hp.pos γ b)
  have hgdeg : g.natDegree = p := by
    rw [← natDegree_map_eq_of_injective (f := algebraMap 𝒪 M) (fun _ _ h ↦ Subtype.ext h) g]
    exact (congrArg natDegree hg).trans (natDegree_shiftPoly γ b)
  have hcoeff (k : ℕ) : (g.map (residue 𝒪)).coeff k = rd (P.coeff k) := by
    rw [coeff_map, ← rd_coe, ← hg, coeff_map]
    rfl
  have hred : g.map (residue 𝒪) = X ^ p - X - C (rd (b / γ ^ p)) := by
    ext k
    rw [hcoeff, coeff_sub, coeff_sub, coeff_X_pow, coeff_X, coeff_C]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [hP, coeff_shiftPoly p hγ0, if_pos rfl, if_neg hp.ne_zero.symm, if_neg one_ne_zero,
        if_pos rfl, rd_neg]
      ring
    rw [if_neg hk, sub_zero]
    rcases eq_or_ne k 1 with rfl | hk1
    · rw [if_neg hp.one_lt.ne, if_pos rfl, hP, coeff_shiftPoly p hγ0, if_neg one_ne_zero,
        Nat.choose_one_right, inv_pow, hγ, zero_sub, show (-(p : M))⁻¹ * p = -1 by
          field_simp, rd_neg, rd_one]
    rw [if_neg (Ne.symm hk1), sub_zero]
    rcases lt_trichotomy k p with hkp | rfl | hkp
    · rw [if_neg hkp.ne, rd_eq_zero (norm_coeff_shiftPoly_lt hγ0 b hk
        (hlt k (by omega) hkp))]
    · rw [if_pos rfl, hP, coeff_shiftPoly k hγ0, if_neg hk, Nat.sub_self, pow_zero,
        Nat.choose_self, Nat.cast_one, mul_one, rd_one]
    · rw [if_neg hkp.ne', hP, coeff_shiftPoly p hγ0, if_neg hk, Nat.choose_eq_zero_of_lt hkp,
        Nat.cast_zero, mul_zero]
      exact (rd_eq_zero_iff (by simp)).2 (by simp)
  have hirr : Irreducible (g.map (residue 𝒪)) := by
    rw [hred]
    exact irreducible_X_pow_sub_X_sub_C hres
  rw [← hgdeg]
  exact natDegree_le_inertiaDeg_of_aeval w hgm hirr (χ := (ϑ - 1) / algebraMap M E γ)
    (by rw [hg]; exact aeval_shiftPoly hγ0 hϑ)

end Tests

section Lifted

/-! ### Lifted Frobenius-closed bases -/

/-- The family `{1} ⊔ {u_q ^ p ^ n}` built from `u`. -/
def liftBasis {M ι : Type*} [Monoid M] (p : ℕ) (u : ι → M) : Option (ℕ × ι) → M
  | none => 1
  | some (n, q) => u q ^ p ^ n

/-- The indices of the basis elements that are not `p`-th powers of basis elements: the `u_q`. -/
def IsU {ι : Type*} : Option (ℕ × ι) → Prop
  | some (0, _) => True
  | _ => False

/-- The index of the `p`-th root of a basis element (for indices of `p`-th powers). -/
def root {ι : Type*} : Option (ℕ × ι) → Option (ℕ × ι)
  | none => none
  | some (n, q) => some (n - 1, q)

/-- The Frobenius depth of an index. -/
def depth {ι : Type*} : Option (ℕ × ι) → ℕ
  | none => 0
  | some (n, _) => n

lemma liftBasis_root_pow {M ι : Type*} [Monoid M] (p : ℕ) (u : ι → M) {i : Option (ℕ × ι)}
    (hi : ¬IsU i) : liftBasis p u (root i) ^ p = liftBasis p u i := by
  rcases i with _ | ⟨n, q⟩
  · simp [liftBasis, root]
  · rcases n with _ | n
    · exact (hi trivial).elim
    · simp only [liftBasis, root, Nat.add_sub_cancel, ← pow_mul, ← pow_succ]

lemma root_injOn {ι : Type*} {i j : Option (ℕ × ι)} (hi : ¬IsU i) (hj : ¬IsU j)
    (h : root i = root j) : i = j := by
  rcases i with _ | ⟨n, q⟩ <;> rcases j with _ | ⟨m, q'⟩
  · rfl
  · simp [root] at h
  · simp [root] at h
  · rcases n with _ | n
    · exact (hi trivial).elim
    rcases m with _ | m
    · exact (hj trivial).elim
    simp only [root, Nat.add_sub_cancel, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1, h.2]

lemma isU_some_zero {ι : Type*} (q : ι) : IsU (some (0, q) : Option (ℕ × ι)) := trivial

lemma not_isU_none {ι : Type*} : ¬IsU (none : Option (ℕ × ι)) := id

lemma root_some_succ {ι : Type*} (n : ℕ) (q : ι) :
    root (some (n + 1, q) : Option (ℕ × ι)) = some (n, q) := rfl

variable {C M : Type*} [NormedField C] [IsUltrametricDist C] [NormedField M]
  [IsUltrametricDist M] [NormedAlgebra C M]

local notation "𝒪C" => HenselComplete.integers C
local notation "𝒪M" => HenselComplete.integers M

variable (C M) in
/-- **A lifted Frobenius-closed basis** (Kuhlmann's (LFC), Lemma 4.9): a Frobenius-closed basis
`B` of the residue field `κ` of `M` over the residue field `k` of `C`, together with lifts
`u_q ∈ M` (`‖u_q‖ ≤ 1`) of its generators `ū_q`, such that the `C`-span of the family
`{1} ⊔ {u_q ^ p ^ n}` is dense in `M`. -/
structure LiftedFrobeniusBasis (p : ℕ) where
  /-- The Frobenius-closed basis of the residue field. -/
  B : FrobeniusBasis (ResidueField 𝒪C) (ResidueField 𝒪M) p
  /-- The lifts of its generators. -/
  u : B.ι → M
  norm_u_le : ∀ q, ‖u q‖ ≤ 1
  rd_u : ∀ q, rd (u q) = B.u q
  dense : Dense (Submodule.span C (Set.range (liftBasis p u)) : Set M)

namespace LiftedFrobeniusBasis

variable {p : ℕ} (L : LiftedFrobeniusBasis C M p)

/-- The lifted basis `{1} ⊔ {u_q ^ p ^ n}`. -/
abbrev b : Option (ℕ × L.B.ι) → M := liftBasis p L.u

/-- The element `Σ cᵢ bᵢ` of `M`. -/
noncomputable def val (c : Option (ℕ × L.B.ι) →₀ C) : M :=
  Finsupp.linearCombination C L.b c

lemma norm_b_le (i : Option (ℕ × L.B.ι)) : ‖L.b i‖ ≤ 1 := by
  rcases i with _ | ⟨n, q⟩
  · simp [liftBasis]
  · simp only [liftBasis, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (L.norm_u_le q)

lemma rd_b (i : Option (ℕ × L.B.ι)) : rd (L.b i) = L.B.basis i := by
  rcases i with _ | ⟨n, q⟩
  · simp [liftBasis, rd_one, L.B.basis_none]
  · simp only [liftBasis]
    rw [rd_pow (L.norm_u_le q), L.rd_u, L.B.basis_some]

lemma val_eq_sum (c : Option (ℕ × L.B.ι) →₀ C) :
    L.val c = ∑ i ∈ c.support, algebraMap C M (c i) * L.b i := by
  rw [val, Finsupp.linearCombination_apply, Finsupp.sum]
  simp_rw [Algebra.smul_def]

@[simp] lemma val_add (c c' : Option (ℕ × L.B.ι) →₀ C) : L.val (c + c') = L.val c + L.val c' :=
  map_add _ _ _

@[simp] lemma val_sub (c c' : Option (ℕ × L.B.ι) →₀ C) : L.val (c - c') = L.val c - L.val c' :=
  map_sub _ _ _

@[simp] lemma val_smul (a : C) (c : Option (ℕ × L.B.ι) →₀ C) :
    L.val (a • c) = algebraMap C M a * L.val c := by
  rw [val, map_smul, Algebra.smul_def]
  rfl

@[simp] lemma val_single (i : Option (ℕ × L.B.ι)) (a : C) :
    L.val (Finsupp.single i a) = algebraMap C M a * L.b i := by
  rw [val, Finsupp.linearCombination_single, Algebra.smul_def]

@[simp] lemma val_zero : L.val 0 = 0 := map_zero _

lemma val_sum {κ : Type*} (s : Finset κ) (f : κ → Option (ℕ × L.B.ι) →₀ C) :
    L.val (∑ j ∈ s, f j) = ∑ j ∈ s, L.val (f j) :=
  map_sum (Finsupp.linearCombination C L.b) _ _

/-- **Orthonormality** (A1): `‖Σ cᵢ bᵢ‖ = maxᵢ ‖cᵢ‖`. -/
theorem nnnorm_val (c : Option (ℕ × L.B.ι) →₀ C) :
    ‖L.val c‖₊ = c.support.sup fun i ↦ ‖c i‖₊ := by
  set x : Option (ℕ × L.B.ι) → 𝒪M := fun i ↦ ⟨L.b i, (HenselComplete.mem_integers_iff _).2
    (L.norm_b_le i)⟩
  have hx : LinearIndependent (ResidueField 𝒪C) (fun i ↦ residue 𝒪M (x i)) := by
    have hfun : (fun i ↦ residue 𝒪M (x i)) = ⇑L.B.basis := by
      ext i
      rw [← rd_coe]
      exact L.rd_b i
    rw [hfun]
    exact L.B.basis.linearIndependent
  have h := FundamentalInequality.valuation_sum_eq_sup (v := NormedField.valuation (K := C))
    (w := NormedField.valuation (K := M)) hx c.support (fun i ↦ c i)
  rw [NormedField.valuation_apply] at h
  rw [val_eq_sum, h]
  congr 1
  ext i
  rw [NormedField.valuation_apply, nnnorm_algebraMap']

lemma norm_coeff_le_norm_val (c : Option (ℕ × L.B.ι) →₀ C) (i : Option (ℕ × L.B.ι)) :
    ‖c i‖ ≤ ‖L.val c‖ := by
  classical
  by_cases hi : i ∈ c.support
  · rw [← coe_nnnorm, ← coe_nnnorm (L.val c), NNReal.coe_le_coe, nnnorm_val]
    exact Finset.le_sup (f := fun i ↦ ‖c i‖₊) hi
  · rw [Finsupp.notMem_support_iff.1 hi, norm_zero]
    exact norm_nonneg _

lemma norm_val_le_iff (c : Option (ℕ × L.B.ι) →₀ C) {r : ℝ} (hr : 0 ≤ r) :
    ‖L.val c‖ ≤ r ↔ ∀ i, ‖c i‖ ≤ r := by
  refine ⟨fun h i ↦ (L.norm_coeff_le_norm_val c i).trans h, fun h ↦ ?_⟩
  rw [← coe_nnnorm, nnnorm_val, ← NNReal.coe_mk r hr, NNReal.coe_le_coe, Finset.sup_le_iff]
  intro i _
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact h i

lemma exists_coeff_eq (c : Option (ℕ × L.B.ι) →₀ C) (hc : c ≠ 0) :
    ∃ i, c i ≠ 0 ∧ ‖c i‖ = ‖L.val c‖ := by
  obtain ⟨i, hi, hi'⟩ := c.support.exists_mem_eq_sup (Finsupp.support_nonempty_iff.2 hc)
    fun i ↦ ‖c i‖₊
  refine ⟨i, Finsupp.mem_support_iff.1 hi, ?_⟩
  rw [← coe_nnnorm, ← coe_nnnorm (L.val c), nnnorm_val, hi']

lemma val_eq_zero_iff (c : Option (ℕ × L.B.ι) →₀ C) : L.val c = 0 ↔ c = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, val_zero]⟩
  ext i
  have := L.norm_coeff_le_norm_val c i
  rw [h, norm_zero] at this
  simpa using this

lemma norm_val_lt (c : Option (ℕ × L.B.ι) →₀ C) {r : ℝ} (hr : 0 < r) (h : ∀ i, ‖c i‖ < r) :
    ‖L.val c‖ < r := by
  by_cases hc : c = 0
  · rw [hc, val_zero, norm_zero]
    exact hr
  obtain ⟨i, -, hi⟩ := L.exists_coeff_eq c hc
  rw [← hi]
  exact h i

/-- **Density**: every element is approximated by some `Σ cᵢ bᵢ` of no larger norm. -/
theorem exists_approx (m : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ c, ‖m - L.val c‖ < ε ∧ ‖L.val c‖ ≤ ‖m‖ := by
  by_cases hm : ‖m‖ < ε
  · exact ⟨0, by simpa using hm, by simp⟩
  push Not at hm
  obtain ⟨y, hy, hdist⟩ := L.dense.exists_dist_lt m hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hy
  refine ⟨c, ?_, ?_⟩
  · rwa [dist_eq_norm, ← Finsupp.linearCombination_apply] at hdist
  · rw [dist_eq_norm, ← Finsupp.linearCombination_apply] at hdist
    have := DenseCompletion.norm_eq_of_norm_sub_lt (a := L.val c) (b := m)
      (by rw [norm_sub_rev]; exact hdist.trans_le hm)
    exact this.le

include L in
/-- **Value group**: every nonzero element of `M` has the norm of an element of `C`. -/
theorem exists_norm_eq (m : M) (hm : m ≠ 0) : ∃ d : C, d ≠ 0 ∧ ‖m‖ = ‖d‖ := by
  have hmn : 0 < ‖m‖ := norm_pos_iff.2 hm
  obtain ⟨c, h1, h2⟩ := L.exists_approx m hmn
  have heq : ‖L.val c‖ = ‖m‖ := DenseCompletion.norm_eq_of_norm_sub_lt (by
    rw [norm_sub_rev]; exact h1)
  have hc : c ≠ 0 := by
    rintro rfl
    rw [val_zero, norm_zero] at heq
    exact hmn.ne heq
  obtain ⟨i, hi, hi'⟩ := L.exists_coeff_eq c hc
  exact ⟨c i, hi, by rw [← heq, hi']⟩

lemma rd_algebraMap {x : C} (hx : ‖x‖ ≤ 1) :
    rd (algebraMap C M x) = algebraMap (ResidueField 𝒪C) (ResidueField 𝒪M) (rd x) := by
  set x' : 𝒪C := ⟨x, (HenselComplete.mem_integers_iff x).2 hx⟩
  rw [show x = (x' : C) from rfl, rd_coe,
    HasExtension.algebraMap_residue_eq_residue_algebraMap, ← rd_coe,
    HasExtension.coe_algebraMap_valuationSubring_eq]

lemma rd_sum {ι : Type*} (s : Finset ι) (f : ι → M) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    rd (∑ i ∈ s, f i) = ∑ i ∈ s, rd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact rd_eq_zero (by simp)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, rd_add (hf j (Finset.mem_insert_self j s))
      (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi ↦
        hf i (Finset.mem_insert_of_mem hi)), ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- **The residue of a normalized combination**: for `‖Σ cᵢ bᵢ‖ ≤ ‖a‖`, the residue of
`(Σ cᵢ bᵢ) / a` is `Σ (cᵢ / a)‾ Bᵢ`. -/
theorem rd_val_div (c : Option (ℕ × L.B.ι) →₀ C) {a : C} (ha : a ≠ 0)
    (hc : ‖L.val c‖ ≤ ‖a‖) :
    rd (L.val c / algebraMap C M a) =
      ∑ i ∈ c.support, rd (c i / a) • L.B.basis i := by
  have han : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hci (i : Option (ℕ × L.B.ι)) : ‖c i / a‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ ((L.norm_coeff_le_norm_val c i).trans hc) han.le
  rw [val_eq_sum, Finset.sum_div, rd_sum]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show algebraMap C M (c i) * L.b i / algebraMap C M a = algebraMap C M (c i / a) * L.b i
      by rw [map_div₀]; ring, rd_mul (by rw [norm_algebraMap']; exact hci i) (L.norm_b_le i),
      rd_algebraMap (hci i), L.rd_b, Algebra.smul_def]
  · intro i _
    rw [show algebraMap C M (c i) * L.b i / algebraMap C M a = algebraMap C M (c i / a) * L.b i
      by rw [map_div₀]; ring, norm_mul, norm_algebraMap']
    exact mul_le_one₀ (hci i) (norm_nonneg _) (L.norm_b_le i)

section Phases

/-! ### The normal form procedure -/

variable [IsAlgClosed C] [CompleteSpace M] {p : ℕ} (L : LiftedFrobeniusBasis C M p)

omit [IsUltrametricDist C] [IsUltrametricDist M] [IsAlgClosed C] [CompleteSpace M] in
lemma norm_natCast_eq (n : ℕ) : ‖(n : M)‖ = ‖(n : C)‖ := by
  rw [← map_natCast (algebraMap C M), norm_algebraMap']

omit [IsUltrametricDist C] [IsAlgClosed C] [CompleteSpace M] in
lemma norm_one_add_eq_one {z : M} (hz : ‖z‖ < 1) : ‖1 + z‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : M)) (y := z)
    (by rw [norm_one]; exact hz.ne')
  rwa [norm_one, max_eq_left hz.le] at this

/-- **One elimination step** (first phase): all coefficients `cᵢ` of `p`-th powers `bᵢ` with
`‖cᵢ‖ ≥ ‖p‖` are removed at once by dividing by `(1 + Σ cᵢ^{1/p} b_{root i}) ^ p`; the error
terms (re-expanded by density, up to `‖γ‖ ^ p`) are smaller by the factor `max ρ ‖π‖ < 1`,
where `‖π‖ ^ p = ‖p‖`. -/
theorem phase1_step (hp : p.Prime) (hp0 : (p : M) ≠ 0) {γ : M} (hγ : γ ^ (p - 1) = -(p : M))
    {π : C} (hπ : ‖π‖ ^ p = ‖(p : C)‖) (hπ1 : ‖π‖ < 1) {ρ : ℝ} (hρ : ρ < 1)
    (c : Option (ℕ × L.B.ι) →₀ C) (hc : ‖L.val c‖ ≤ ρ) {R : ℝ}
    (hR : ∀ i, ¬IsU i → ‖(p : C)‖ ≤ ‖c i‖ → ‖c i‖ ≤ R) :
    ∃ c' y, 1 + L.val c = (1 + L.val c') * y ^ p ∧ ‖L.val c'‖ ≤ ρ ∧
      ∀ i, ¬IsU i → ‖(p : C)‖ ≤ ‖c' i‖ → ‖c' i‖ ≤ max ρ ‖π‖ * R := by
  classical
  have hpC0 : (p : C) ≠ 0 := by
    intro h
    apply hp0
    rw [← map_natCast (algebraMap C M), h, map_zero]
  have hpCn : 0 < ‖(p : C)‖ := norm_pos_iff.2 hpC0
  have hρ0 : 0 ≤ ρ := (_root_.norm_nonneg _).trans hc
  set S := c.support.filter fun i ↦ ¬IsU i ∧ ‖(p : C)‖ ≤ ‖c i‖ with hS
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨c, 1, by rw [one_pow, mul_one], hc, fun i hi hpi ↦ ?_⟩
    exfalso
    have hci : c i ≠ 0 := fun h ↦ by
      rw [h, norm_zero] at hpi
      exact hpCn.not_ge hpi
    have : i ∈ S := Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hci, hi, hpi⟩
    rw [hSe] at this
    simp at this
  choose d hd using fun i ↦ IsAlgClosed.exists_pow_nat_eq (c i) hp.pos
  have hdc (i : Option (ℕ × L.B.ι)) : ‖d i‖ ^ p = ‖c i‖ := by rw [← norm_pow, hd]
  set r : ℝ := S.sup' hSne fun i ↦ ‖d i‖ with hr
  obtain ⟨i₀, hi₀S, hi₀⟩ := S.exists_mem_eq_sup' hSne fun i ↦ ‖d i‖
  obtain ⟨-, hi₀U, hi₀p⟩ := Finset.mem_filter.1 hi₀S
  have hri : r = ‖d i₀‖ := hi₀
  have hr0 : 0 ≤ r := hri ▸ _root_.norm_nonneg _
  have hrp : r ^ p = ‖c i₀‖ := by rw [hri, hdc]
  have hRp : r ^ p ≤ R := hrp ▸ hR i₀ hi₀U hi₀p
  have hpr : ‖(p : C)‖ ≤ r ^ p := hrp ▸ hi₀p
  have hrρ : r ^ p ≤ ρ := hrp ▸ (L.norm_coeff_le_norm_val c i₀).trans hc
  have hr1 : r ≤ 1 := ((pow_lt_one_iff_of_nonneg hr0 hp.ne_zero).1 (hrρ.trans_lt hρ)).le
  have hdS : ∀ i ∈ S, ‖d i‖ ≤ r := fun i hi ↦ Finset.le_sup' (fun i ↦ ‖d i‖) hi
  have hcS : ∀ i ∈ S, ‖c i‖ ≤ r ^ p := fun i hi ↦ by
    rw [← hdc]
    exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hdS i hi) p
  have hπr : ‖π‖ ≤ r := le_of_pow_le_pow_left₀ hp.ne_zero hr0 (hπ ▸ hpr)
  have hsucc : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  have hpr' : ‖(p : M)‖ * r ≤ ‖π‖ * r ^ p := by
    rw [norm_natCast_eq (C := C), ← hπ, ← hsucc, pow_succ', pow_succ, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (_root_.norm_nonneg _) hπr _) hr0) (_root_.norm_nonneg _)
  set y : Option (ℕ × L.B.ι) → M := fun i ↦ algebraMap C M (d i) * L.b (root i) with hy
  have hyp : ∀ i ∈ S, y i ^ p = algebraMap C M (c i) * L.b i := by
    intro i hi
    have hiU := (Finset.mem_filter.1 hi).2.1
    simp only [hy]
    rw [mul_pow, ← map_pow, hd, liftBasis_root_pow p L.u hiU]
  have hyn : ∀ i ∈ S, ‖y i‖ ≤ r := by
    intro i hi
    simp only [hy]
    rw [norm_mul, norm_algebraMap']
    exact (mul_le_of_le_one_right (_root_.norm_nonneg _) (L.norm_b_le _)).trans (hdS i hi)
  set x := ∑ i ∈ S, y i with hx_def
  have hx : ‖x‖ ≤ r := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr0 hyn
  set T := ∑ i ∈ S, algebraMap C M (c i) * L.b i with hT_def
  have hT : ‖T‖ ≤ r ^ p := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi ↦ ?_
    rw [norm_mul, norm_algebraMap']
    exact (mul_le_of_le_one_right (_root_.norm_nonneg _) (L.norm_b_le _)).trans (hcS i hi)
  set e := (1 + x) ^ p - 1 - T with he_def
  have he : ‖e‖ ≤ ‖(p : M)‖ * r := by
    have h1 := PthPower.norm_add_pow_sub_le hp (x := (1 : M)) (y := x) (by simp) (hx.trans hr1)
    have h2 := PthPower.norm_sum_pow_sub_le hp S y hyn hr1 hr0
    have hT' : T = ∑ i ∈ S, y i ^ p := Finset.sum_congr rfl fun i hi ↦ (hyp i hi).symm
    have : e = ((1 + x) ^ p - 1 ^ p - x ^ p) + (x ^ p - ∑ i ∈ S, y i ^ p) := by
      rw [he_def, hT']
      ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1.trans ?_) h2)
    rw [norm_one, one_mul]
    exact mul_le_mul_of_nonneg_left hx (_root_.norm_nonneg _)
  have heπ : ‖e‖ ≤ ‖π‖ * r ^ p := he.trans hpr'
  have hTe : ‖T + e‖ ≤ r ^ p :=
    (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le hT (heπ.trans (mul_le_of_le_one_left (by positivity) hπ1.le)))
  have hw : (1 + x) ^ p = 1 + (T + e) := by rw [he_def]; ring
  have hw1 : ‖(1 + x) ^ p‖ = 1 := by
    rw [hw]
    exact norm_one_add_eq_one (hTe.trans_lt (hrρ.trans_lt hρ))
  have hw0 : (1 + x) ^ p ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    exact zero_ne_one hw1
  set c₁ := c - ∑ i ∈ S, Finsupp.single i (c i) with hc₁_def
  have hc₁val : L.val c₁ = L.val c - T := by
    rw [hc₁_def, val_sub, val_sum]
    simp only [val_single]
    rfl
  have hc₁i (i : Option (ℕ × L.B.ι)) : c₁ i = if i ∈ S then 0 else c i := by
    rw [hc₁_def, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs <;> simp
  have hc₁n : ‖L.val c₁‖ ≤ ρ := by
    refine (L.norm_val_le_iff c₁ hρ0).2 fun i ↦ ?_
    rw [hc₁i]
    split_ifs
    · simpa using hρ0
    · exact (L.norm_coeff_le_norm_val c i).trans hc
  set m := (1 + L.val c) / (1 + x) ^ p - 1 - L.val c₁ with hm_def
  have hm_eq : m = -(e + L.val c₁ * (T + e)) / (1 + x) ^ p := by
    have hv : 1 + L.val c = 1 + L.val c₁ + T := by rw [hc₁val]; ring
    rw [eq_div_iff hw0, hm_def, sub_mul, sub_mul, div_mul_cancel₀ _ hw0, hv, hw]
    ring
  have hq1 : max ρ ‖π‖ ≤ 1 := max_le hρ.le hπ1.le
  have hm : ‖m‖ ≤ max ρ ‖π‖ * r ^ p := by
    rw [hm_eq, norm_div, hw1, div_one, norm_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact heπ.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    · rw [norm_mul]
      exact (mul_le_mul hc₁n hTe (_root_.norm_nonneg _) hρ0).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hmρ : ‖m‖ ≤ ρ := hm.trans ((mul_le_of_le_one_left (by positivity) hq1).trans hrρ)
  have hγn : 0 < ‖γ‖ ^ p := pow_pos (norm_pos_iff.2 (PthPower.gamma_ne_zero hp hγ hp0)) p
  obtain ⟨c₂, hc₂a, hc₂n⟩ := L.exists_approx m hγn
  have hu : ‖(1 + L.val (c₁ + c₂)) - 1‖ < 1 := by
    rw [add_sub_cancel_left, val_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (hc₁n.trans_lt hρ) ((hc₂n.trans hmρ).trans_lt hρ))
  obtain ⟨z, hz⟩ := PthPower.exists_eq_mul_pow hp hγ hp0 hu
    (v := (1 + L.val c) / (1 + x) ^ p) (by
      have : (1 + L.val c) / (1 + x) ^ p - (1 + L.val (c₁ + c₂)) = m - L.val c₂ := by
        rw [hm_def, val_add]
        ring
      rwa [this])
  refine ⟨c₁ + c₂, z * (1 + x), ?_, ?_, ?_⟩
  · rw [mul_pow, ← mul_assoc, ← hz, div_mul_cancel₀ _ hw0]
  · rw [val_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc₁n (hc₂n.trans hmρ))
  · intro i hiU hpi
    have hc₂i : ‖c₂ i‖ ≤ max ρ ‖π‖ * R :=
      (L.norm_coeff_le_norm_val c₂ i).trans (hc₂n.trans (hm.trans
        (mul_le_mul_of_nonneg_left hRp (by positivity))))
    rw [Finsupp.add_apply, hc₁i] at hpi ⊢
    split_ifs at hpi ⊢ with hiS
    · rwa [zero_add]
    · have hci : ‖c i‖ < ‖(p : C)‖ := by
        by_contra! h
        have hci0 : c i ≠ 0 := fun h0 ↦ by
          rw [h0, norm_zero] at h
          exact hpCn.not_ge h
        exact hiS (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hci0, hiU, h⟩)
      rcases le_max_iff.1 (IsUltrametricDist.norm_add_le_max (c i) (c₂ i)) with h | h
      · exact absurd (hpi.trans h) (not_le.2 hci)
      · exact h.trans hc₂i

/-- **First phase**: after finitely many elimination steps, all coefficients of `p`-th powers
have norm `< ‖p‖`. -/
theorem phase1 (hp : p.Prime) (hp0 : (p : M) ≠ 0) (hp1 : ‖(p : M)‖ < 1) {γ : M}
    (hγ : γ ^ (p - 1) = -(p : M)) {ρ : ℝ} (hρ : ρ < 1) (c : Option (ℕ × L.B.ι) →₀ C)
    (hc : ‖L.val c‖ ≤ ρ) :
    ∃ c' y, 1 + L.val c = (1 + L.val c') * y ^ p ∧ ‖L.val c'‖ ≤ ρ ∧
      ∀ i, ¬IsU i → ‖c' i‖ < ‖(p : C)‖ := by
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) hp.pos
  have hπn : ‖π‖ ^ p = ‖(p : C)‖ := by rw [← norm_pow, hπ]
  have hpC : ‖(p : C)‖ < 1 := by rwa [← norm_natCast_eq (M := M)]
  have hπ1 : ‖π‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (_root_.norm_nonneg _) hp.ne_zero, hπn]
    exact hpC
  have hρ0 : 0 ≤ ρ := (_root_.norm_nonneg _).trans hc
  set q := max ρ ‖π‖ with hq
  have hq1 : q < 1 := max_lt hρ hπ1
  have hq0 : 0 ≤ q := hρ0.trans (le_max_left _ _)
  have key : ∀ N : ℕ, ∃ c' y, 1 + L.val c = (1 + L.val c') * y ^ p ∧ ‖L.val c'‖ ≤ ρ ∧
      ∀ i, ¬IsU i → ‖(p : C)‖ ≤ ‖c' i‖ → ‖c' i‖ ≤ q ^ N := by
    intro N
    induction N with
    | zero =>
      exact ⟨c, 1, by rw [one_pow, mul_one], hc, fun i _ _ ↦ by
        rw [pow_zero]
        exact ((L.norm_coeff_le_norm_val c i).trans hc).trans hρ.le⟩
    | succ N ih =>
      obtain ⟨c', y, h1, h2, h3⟩ := ih
      obtain ⟨c'', y', h1', h2', h3'⟩ := L.phase1_step hp hp0 hγ hπn hπ1 hρ c' h2 h3
      refine ⟨c'', y' * y, by rw [h1, h1', mul_pow]; ring, h2', fun i hi hpi ↦ ?_⟩
      rw [pow_succ']
      exact h3' i hi hpi
  have hpCn : 0 < ‖(p : C)‖ := by
    rw [← norm_natCast_eq (M := M)]
    exact norm_pos_iff.2 hp0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpCn hq1
  obtain ⟨c', y, h1, h2, h3⟩ := key N
  refine ⟨c', y, h1, h2, fun i hi ↦ ?_⟩
  by_contra! h
  exact (h3 i hi h).not_gt (hN.trans_le h) |>.elim

omit [CompleteSpace M] in
/-- **Removing the constant term**: `1 + c₀` is a `p`-th power in `C`. -/
theorem remove_const (hp : p.Prime) (c : Option (ℕ × L.B.ι) →₀ C) (hc : ‖L.val c‖ < 1) :
    ∃ c' y, 1 + L.val c = (1 + L.val c') * y ^ p ∧ c' none = 0 ∧
      ∀ i, i ≠ none → ‖c' i‖ = ‖c i‖ := by
  classical
  set c₀ := c none
  have hc₀ : ‖c₀‖ < 1 := (L.norm_coeff_le_norm_val c none).trans_lt hc
  have hA : ‖1 + c₀‖ = 1 := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : C)) (y := c₀)
      (by rw [norm_one]; exact hc₀.ne')
    rwa [norm_one, max_eq_left hc₀.le] at this
  have hA0 : 1 + c₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hA
    exact zero_ne_one hA
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (1 + c₀) hp.pos
  set c' := (1 + c₀)⁻¹ • (c - Finsupp.single none c₀) with hc'
  have hA0' : algebraMap C M (1 + c₀) ≠ 0 := (_root_.map_ne_zero _).2 hA0
  refine ⟨c', algebraMap C M e, ?_, ?_, fun i hi ↦ ?_⟩
  · rw [← map_pow, he, hc', val_smul, val_sub, val_single]
    simp only [liftBasis, mul_one]
    rw [map_inv₀]
    field_simp
    rw [map_add, map_one]
    ring
  · simp [hc', c₀]
  · simp only [hc', Finsupp.coe_smul, Finsupp.coe_sub, Pi.smul_apply, Pi.sub_apply,
      Finsupp.single_apply, if_neg (Ne.symm hi), sub_zero, smul_eq_mul, norm_mul, norm_inv, hA,
      inv_one, one_mul]

/-- **Second phase** (Kuhlmann, Corollary 2.12 d): if `‖Σ cᵢ bᵢ‖ ≤ ‖γ‖`, there is no constant
term and all coefficients of `p`-th powers have norm `< ‖p‖`, then each term `c b_{root i} ^ p`
can be replaced by `-p c^{1/p} b_{root i}`; by induction on the total Frobenius depth, no
`p`-th powers remain. -/
theorem phase2 (hp : p.Prime) (hp0 : (p : M) ≠ 0) (hp1 : ‖(p : M)‖ < 1) {γ : M}
    (hγ : γ ^ (p - 1) = -(p : M)) (c : Option (ℕ × L.B.ι) →₀ C) (hn : c none = 0)
    (hc : ‖L.val c‖ ≤ ‖γ‖) (hP : ∀ i, ¬IsU i → ‖c i‖ < ‖(p : C)‖) :
    ∃ c' y, 1 + L.val c = (1 + L.val c') * y ^ p ∧ ‖L.val c'‖ ≤ ‖γ‖ ∧
      ∀ i, c' i ≠ 0 → IsU i := by
  classical
  have hpγ : ‖(p : C)‖ ≤ ‖γ‖ := by
    rw [← norm_natCast_eq (M := M)]
    exact PthPower.norm_natCast_le_norm_gamma hp hγ
  suffices H : ∀ N : ℕ, ∀ c : Option (ℕ × L.B.ι) →₀ C,
      ∑ i ∈ c.support, depth i ≤ N → c none = 0 → ‖L.val c‖ ≤ ‖γ‖ →
      (∀ i, ¬IsU i → ‖c i‖ < ‖(p : C)‖) →
      ∃ c' y, 1 + L.val c = (1 + L.val c') * y ^ p ∧ ‖L.val c'‖ ≤ ‖γ‖ ∧
        ∀ i, c' i ≠ 0 → IsU i from H _ c le_rfl hn hc hP
  intro N
  induction N with
  | zero =>
    intro c hD hn hc hP
    refine ⟨c, 1, by rw [one_pow, mul_one], hc, fun i hi ↦ ?_⟩
    rcases i with _ | ⟨_ | n, q⟩
    · exact (hi hn).elim
    · trivial
    · have hmem : some (n + 1, q) ∈ c.support := Finsupp.mem_support_iff.2 hi
      have := Finset.single_le_sum (f := depth) (fun _ _ ↦ Nat.zero_le _) hmem
      have h' : depth (some (n + 1, q) : Option (ℕ × L.B.ι)) = n + 1 := rfl
      omega
  | succ N ih =>
    intro c hD hn hc hP
    by_cases hall : ∀ i, c i ≠ 0 → IsU i
    · exact ⟨c, 1, by rw [one_pow, mul_one], hc, hall⟩
    push Not at hall
    obtain ⟨i, hi0, hiU⟩ := hall
    rcases i with _ | ⟨_ | n, q⟩
    · exact (hi0 hn).elim
    · exact (hiU trivial).elim
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (c (some (n + 1, q))) hp.pos
    have hpCn : 0 < ‖(p : C)‖ := by
      rw [← norm_natCast_eq (M := M)]
      exact norm_pos_iff.2 hp0
    have hdn : ‖d‖ ^ p < ‖(p : C)‖ := by rw [← norm_pow, hd]; exact hP _ hiU
    have hd1 : ‖d‖ < 1 := by
      rw [← pow_lt_one_iff_of_nonneg (_root_.norm_nonneg _) hp.ne_zero]
      exact hdn.trans (by rwa [← norm_natCast_eq (M := M)])
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Option (ℕ × L.B.ι) →₀ C,
        c₀ = c - Finsupp.single (some (n + 1, q)) (c (some (n + 1, q))) := ⟨_, rfl⟩
    have hc₀i (k : Option (ℕ × L.B.ι)) :
        c₀ k = if k = some (n + 1, q) then 0 else c k := by
      rw [hc₀, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      by_cases hk : k = some (n + 1, q)
      · rw [if_pos hk.symm, if_pos hk, hk, sub_self]
      · rw [if_neg (Ne.symm hk), if_neg hk, sub_zero]
    have hγ0 : 0 ≤ ‖γ‖ := _root_.norm_nonneg _
    have hc₀n : ‖L.val c₀‖ ≤ ‖γ‖ := by
      refine (L.norm_val_le_iff c₀ hγ0).2 fun k ↦ ?_
      rw [hc₀i]
      split_ifs
      · rw [norm_zero]
        exact hγ0
      · exact (L.norm_coeff_le_norm_val c k).trans hc
    have hbj : L.b (some (n, q)) ^ p = L.b (some (n + 1, q)) := liftBasis_root_pow p L.u hiU
    obtain ⟨z, hz⟩ := PthPower.exists_eq_mul_pow_of_pow hp hγ hp0 hp1 hc₀n
      (c := algebraMap C M d * L.b (some (n, q))) (by
        rw [norm_mul, norm_algebraMap']
        calc (‖d‖ * ‖L.b (some (n, q))‖) ^ p ≤ ‖d‖ ^ p :=
              pow_le_pow_left₀ (by positivity)
                (mul_le_of_le_one_right (_root_.norm_nonneg _) (L.norm_b_le _)) p
          _ < ‖(p : M)‖ := by rwa [norm_natCast_eq (C := C)])
    obtain ⟨c'', hc''⟩ : ∃ c'' : Option (ℕ × L.B.ι) →₀ C,
        c'' = c₀ - Finsupp.single (some (n, q)) ((p : C) * d) := ⟨_, rfl⟩
    have hval : 1 + L.val c = 1 + L.val c₀ + (algebraMap C M d * L.b (some (n, q))) ^ p := by
      rw [mul_pow, ← map_pow, hd, hbj, hc₀, val_sub, val_single]
      ring
    have hval'' : 1 + L.val c₀ - (p : M) * (algebraMap C M d * L.b (some (n, q))) =
        1 + L.val c'' := by
      rw [hc'', val_sub, val_single, _root_.map_mul, map_natCast]
      ring
    have hc''k (k : Option (ℕ × L.B.ι)) :
        c'' k = (if k = some (n + 1, q) then 0 else c k) -
          (if k = some (n, q) then (p : C) * d else 0) := by
      rw [hc'', Finsupp.coe_sub, Pi.sub_apply, hc₀i, Finsupp.single_apply]
      by_cases hk : k = some (n, q)
      · rw [if_pos hk.symm, if_pos hk]
      · rw [if_neg (Ne.symm hk), if_neg hk]
    have hpd : ‖(p : C) * d‖ ≤ ‖(p : C)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) hd1.le
    have hpd' : ‖(p : C) * d‖ < ‖(p : C)‖ := by
      rw [norm_mul]
      exact mul_lt_of_lt_one_right hpCn hd1
    have hn'' : c'' none = 0 := by
      rw [hc''k, if_neg (by simp), if_neg (by simp), hn, sub_zero]
    have hc''n : ‖L.val c''‖ ≤ ‖γ‖ := by
      refine (L.norm_val_le_iff c'' hγ0).2 fun k ↦ ?_
      rw [hc''k]
      refine (PthPower.norm_sub_le_max' _ _).trans (max_le ?_ ?_)
      · split_ifs
        · rw [norm_zero]
          exact hγ0
        · exact (L.norm_coeff_le_norm_val c k).trans hc
      · split_ifs
        · exact hpd.trans hpγ
        · rw [norm_zero]
          exact hγ0
    have hP'' : ∀ k, ¬IsU k → ‖c'' k‖ < ‖(p : C)‖ := by
      intro k hk
      rw [hc''k]
      refine lt_of_le_of_lt (PthPower.norm_sub_le_max' _ _) (max_lt ?_ ?_)
      · split_ifs
        · rw [norm_zero]
          exact hpCn
        · exact hP k hk
      · split_ifs
        · exact hpd'
        · rw [norm_zero]
          exact hpCn
    have hsupp : c''.support ⊆ insert (some (n, q)) (c.support.erase (some (n + 1, q))) := by
      intro k hk
      rw [Finsupp.mem_support_iff, hc''k] at hk
      rw [Finset.mem_insert, Finset.mem_erase, Finsupp.mem_support_iff]
      by_cases hkj : k = some (n, q)
      · exact Or.inl hkj
      · right
        rw [if_neg hkj, sub_zero] at hk
        by_cases hki : k = some (n + 1, q)
        · rw [if_pos hki] at hk
          exact (hk rfl).elim
        · rw [if_neg hki] at hk
          exact ⟨hki, hk⟩
    have hD'' : ∑ k ∈ c''.support, depth k ≤ N := by
      have h1 : ∑ k ∈ c''.support, depth k ≤
          ∑ k ∈ insert (some (n, q)) (c.support.erase (some (n + 1, q))), depth k :=
        Finset.sum_le_sum_of_subset hsupp
      have h2 : ∑ k ∈ insert (some (n, q)) (c.support.erase (some (n + 1, q))), depth k ≤
          depth (some (n, q) : Option (ℕ × L.B.ι)) +
            ∑ k ∈ c.support.erase (some (n + 1, q)), depth k := by
        by_cases hjm : some (n, q) ∈ c.support.erase (some (n + 1, q))
        · rw [Finset.insert_eq_of_mem hjm]
          exact Nat.le_add_left _ _
        · rw [Finset.sum_insert hjm]
      have h3 := Finset.add_sum_erase c.support depth (Finsupp.mem_support_iff.2 hi0)
      have e1 : depth (some (n, q) : Option (ℕ × L.B.ι)) = n := rfl
      have e2 : depth (some (n + 1, q) : Option (ℕ × L.B.ι)) = n + 1 := rfl
      omega
    obtain ⟨c', y, h1, h2, h3⟩ := ih c'' hD'' hn'' hc''n hP''
    refine ⟨c', y * z, ?_, h2, h3⟩
    rw [hval, hz, hval'', h1]
    ring

end Phases

section Assembly

variable [IsAlgClosed C] [CompleteSpace M] {p : ℕ} (L : LiftedFrobeniusBasis C M p)

variable (p) in
/-- The two "visible" normal forms of a `1`-unit `1 + b` (Kuhlmann, Proposition 4.13): either
`‖γ‖ < ‖t‖ ≤ 1`, `‖b‖ ≤ ‖t‖ ^ p` and the residue of `b / t ^ p` is not a `p`-th power, or
`‖b‖ ≤ ‖γ‖ ^ p` and the residue of `b / γ ^ p` is not of the form `z ^ p - z`. -/
def Visible (γ b : M) : Prop :=
  (∃ t : M, ‖γ‖ < ‖t‖ ∧ ‖t‖ ≤ 1 ∧ ‖b‖ ≤ ‖t‖ ^ p ∧ ∀ z : ResidueField 𝒪M, z ^ p ≠ rd (b / t ^ p)) ∨
    (‖b‖ ≤ ‖γ‖ ^ p ∧ ∀ z : ResidueField 𝒪M, z ^ p - z ≠ rd (b / γ ^ p))

omit [IsAlgClosed C] [CompleteSpace M] in
/-- If all leading coefficients (`‖cᵢ‖ = ‖a‖`) sit at indices of the `u_q`, the residue of
`(Σ cᵢ bᵢ) / a` lies in `Span_k u`. -/
lemma rd_val_div_mem_span (c : Option (ℕ × L.B.ι) →₀ C) {a : C} (ha : a ≠ 0)
    (hc : ‖L.val c‖ ≤ ‖a‖) (hU : ∀ i, c i ≠ 0 → ‖c i‖ = ‖a‖ → IsU i) :
    rd (L.val c / algebraMap C M a) ∈ Submodule.span (ResidueField 𝒪C) (Set.range L.B.u) := by
  rw [L.rd_val_div c ha hc]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  have han : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hci : ‖c i‖ ≤ ‖a‖ := (L.norm_coeff_le_norm_val c i).trans hc
  rcases hci.lt_or_eq with hlt | heq
  · rw [rd_eq_zero (by rw [norm_div]; exact (div_lt_one han).2 hlt), zero_smul]
    exact Submodule.zero_mem _
  · obtain ⟨q, rfl⟩ : ∃ q, i = some (0, q) := by
      rcases i with _ | ⟨_ | n, q⟩
      · exact (hU _ (Finsupp.mem_support_iff.1 hi) heq).elim
      · exact ⟨q, rfl⟩
      · exact (hU _ (Finsupp.mem_support_iff.1 hi) heq).elim
    rw [L.B.basis_some, pow_zero, pow_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

omit [IsAlgClosed C] [CompleteSpace M] in
/-- A coefficient of norm `‖a‖` makes the residue of `(Σ cᵢ bᵢ) / a` nonzero. -/
lemma rd_val_div_ne_zero (c : Option (ℕ × L.B.ι) →₀ C) {a : C} (ha : a ≠ 0)
    (hc : ‖L.val c‖ ≤ ‖a‖) {i₀ : Option (ℕ × L.B.ι)} (hi₀ : ‖c i₀‖ = ‖a‖) :
    rd (L.val c / algebraMap C M a) ≠ 0 := by
  have han : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hi₀0 : c i₀ ≠ 0 := fun h ↦ by rw [h, norm_zero] at hi₀; exact han.ne hi₀
  rw [L.rd_val_div c ha hc]
  intro h
  have := (linearIndependent_iff'.1 L.B.basis.linearIndependent) c.support
    (fun i ↦ rd (c i / a)) h i₀ (Finsupp.mem_support_iff.2 hi₀0)
  rw [rd_eq_zero_iff (by rw [norm_div, hi₀, div_self han.ne'])] at this
  rw [norm_div, hi₀, div_self han.ne'] at this
  exact lt_irrefl _ this

omit [CompleteSpace M] in
/-- **Visibility of the normal form**: if `‖γ‖ ^ p ≤ ‖Σ cᵢ bᵢ‖ < 1` and all leading coefficients
sit at indices of the `u_q`, then `Σ cᵢ bᵢ` is visible. -/
theorem visible_of_leading (hp : p.Prime) {γ : C} (c : Option (ℕ × L.B.ι) →₀ C) (hc0 : c ≠ 0)
    (hlow : ‖γ‖ ^ p ≤ ‖L.val c‖) (hc1 : ‖L.val c‖ < 1)
    (hU : ∀ i, c i ≠ 0 → ‖c i‖ = ‖L.val c‖ → IsU i) :
    Visible p (algebraMap C M γ) (L.val c) := by
  obtain ⟨i₀, hi₀0, hi₀⟩ := L.exists_coeff_eq c hc0
  have hγn : ‖algebraMap C M γ‖ = ‖γ‖ := norm_algebraMap' M γ
  simp only [Visible, hγn]
  rcases hlow.lt_or_eq with hlt | heq
  · left
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (c i₀) hp.pos
    have hdn : ‖d‖ ^ p = ‖L.val c‖ := by rw [← norm_pow, hd, hi₀]
    refine ⟨algebraMap C M d, ?_, ?_, ?_, fun z hz ↦ ?_⟩
    · rw [norm_algebraMap']
      exact lt_of_pow_lt_pow_left₀ p (_root_.norm_nonneg _) (hdn ▸ hlt)
    · rw [norm_algebraMap']
      exact ((pow_lt_one_iff_of_nonneg (_root_.norm_nonneg _) hp.ne_zero).1 (hdn ▸ hc1)).le
    · rw [norm_algebraMap', hdn]
    · have hc0' : c i₀ ≠ 0 := hi₀0
      rw [← map_pow, hd] at hz
      have hmem := L.rd_val_div_mem_span c hc0' hi₀.ge fun i hi h ↦ hU i hi (h.trans hi₀)
      exact L.rd_val_div_ne_zero c hc0' hi₀.ge rfl
        (L.B.eq_zero_of_eq_pow _ hmem z hz.symm)
  · right
    refine ⟨heq.ge, fun z hz ↦ ?_⟩
    have hγ0 : γ ^ p ≠ 0 := by
      intro h
      rw [← norm_pow, h, norm_zero] at heq
      rw [← heq] at hi₀
      exact hi₀0 (norm_eq_zero.1 hi₀)
    have hn : ‖γ ^ p‖ = ‖L.val c‖ := by rw [norm_pow, heq]
    rw [← map_pow] at hz
    have hmem := L.rd_val_div_mem_span c hγ0 hn.ge fun i hi h ↦ hU i hi (h.trans hn)
    exact L.rd_val_div_ne_zero c hγ0 hn.ge (hi₀.trans hn.symm)
      (L.B.eq_zero_of_eq_pow_sub _ hmem z hz.symm)

/-- **The Kummer normal form** (Kuhlmann, Proposition 4.13, residue-transcendental mixed
characteristic case). Let `M ⊇ C` carry a lifted Frobenius-closed basis, `p` a prime with
`0 < ‖p‖ < 1`, `γ ∈ C` with `γ ^ (p - 1) = -p`. Every `a ∈ M ∖ 0` that is not a `p`-th power
becomes, after multiplication by a `p`-th power, a visible `1`-unit `1 + b`. -/
theorem exists_visible (L : LiftedFrobeniusBasis C M p) (hp : p.Prime) (hp0 : (p : M) ≠ 0)
    (hp1 : ‖(p : M)‖ < 1) {γ : C}
    (hγ : γ ^ (p - 1) = -(p : C)) {a : M} (ha0 : a ≠ 0) (ha : ∀ y : M, y ^ p ≠ a) :
    ∃ y b : M, a * y ^ p = 1 + b ∧ Visible p (algebraMap C M γ) b := by
  haveI := Fact.mk hp
  haveI := charP_residueField hp hp1
  set γM := algebraMap C M γ with hγM_def
  have hγM : γM ^ (p - 1) = -(p : M) := by
    rw [hγM_def, ← map_pow, hγ, _root_.map_neg, map_natCast]
  have hγ1 : ‖γM‖ < 1 := PthPower.norm_gamma_lt_one hp hγM hp1
  have hγn : 0 < ‖γM‖ := norm_pos_iff.2 (PthPower.gamma_ne_zero hp hγM hp0)
  -- a class-tracking step
  have step : ∀ {Y y : M} {c c' : Option (ℕ × L.B.ι) →₀ C}, a * Y ^ p = 1 + L.val c →
      ‖L.val c‖ < 1 → 1 + L.val c = (1 + L.val c') * y ^ p → a * (Y * y⁻¹) ^ p = 1 + L.val c' := by
    intro Y y c c' h1 hc h2
    have hne : 1 + L.val c ≠ 0 := by
      intro h
      have := norm_one_add_eq_one hc
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hy : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero, mul_zero] at h2
      exact hne h2
    rw [mul_pow, ← mul_assoc, h1, h2, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy),
      mul_one]
  -- normalize `‖a‖ = 1`
  obtain ⟨d₀, hd₀0, hd₀⟩ := L.exists_norm_eq a ha0
  obtain ⟨e₀, he₀⟩ := IsAlgClosed.exists_pow_nat_eq d₀ hp.pos
  have he₀0 : e₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at he₀
    exact hd₀0 he₀.symm
  set E₀ := (algebraMap C M e₀)⁻¹ with hE₀
  have hE₀0 : E₀ ≠ 0 := inv_ne_zero ((_root_.map_ne_zero _).2 he₀0)
  set a₁ := a * E₀ ^ p with ha₁
  have ha₁n : ‖a₁‖ = 1 := by
    rw [ha₁, norm_mul, norm_pow, hE₀, norm_inv, norm_algebraMap', inv_pow, ← norm_pow, he₀, hd₀,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 hd₀0)]
  by_cases hres : ∀ z : ResidueField 𝒪M, z ^ p ≠ rd a₁
  · -- the purely inseparable case with `t = 1`
    refine ⟨E₀, a₁ - 1, by rw [← ha₁]; ring, Or.inl ⟨1, ?_, ?_, ?_, fun z hz ↦ ?_⟩⟩
    · rwa [norm_one]
    · rw [norm_one]
    · rw [norm_one, one_pow]
      exact (PthPower.norm_sub_le_max' _ _).trans (by rw [ha₁n, norm_one, max_self])
    · rw [one_pow, div_one, sub_eq_add_neg, rd_add ha₁n.le (by simp), rd_neg, rd_one] at hz
      exact hres (z + 1) (by rw [add_pow_char, one_pow, hz]; ring)
  push Not at hres
  obtain ⟨z, hz⟩ := hres
  have hrd1 : rd a₁ ≠ 0 := by
    rw [Ne, rd_eq_zero_iff ha₁n.le, ha₁n]
    exact lt_irrefl 1
  obtain ⟨g', hg'⟩ := IsLocalRing.residue_surjective z
  set g : M := (g' : M) with hg
  have hg1 : ‖g‖ ≤ 1 := HenselComplete.norm_le_one g'
  have hrdg : rd g = z := by rw [hg, rd_coe, hg']
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hz
    exact hrd1 hz.symm
  have hgn : ‖g‖ = 1 := by
    by_contra h
    exact hz0 (hrdg ▸ rd_eq_zero (lt_of_le_of_ne hg1 h))
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgn
    exact zero_ne_one hgn
  set a₂ := a₁ * (g⁻¹) ^ p with ha₂
  have ha₂1 : ‖a₂ - 1‖ < 1 := by
    have hn2 : ‖a₂‖ = 1 := by rw [ha₂, norm_mul, norm_pow, norm_inv, hgn, ha₁n]; simp
    have hrd2 : rd a₂ = 1 := by
      have h1 : rd (a₂ * g ^ p) = rd a₁ := by
        rw [ha₂, mul_assoc, ← mul_pow, inv_mul_cancel₀ hg0, one_pow, mul_one]
      rw [rd_mul hn2.le (by rw [norm_pow, hgn, one_pow]), rd_pow hg1, hrdg, ← hz] at h1
      exact (mul_eq_right₀ (pow_ne_zero _ hz0)).1 h1
    have hle : ‖a₂ - 1‖ ≤ 1 :=
      (PthPower.norm_sub_le_max' _ _).trans (by rw [hn2, norm_one, max_self])
    rw [← rd_eq_zero_iff hle, sub_eq_add_neg, rd_add hn2.le (by simp), rd_neg, rd_one, hrd2,
      add_neg_cancel]
  have hstart : a * (E₀ * g⁻¹) ^ p = a₂ := by rw [ha₂, ha₁, mul_pow]; ring
  -- approximate `a₂ - 1`
  have hγp : 0 < ‖γM‖ ^ p := pow_pos hγn p
  obtain ⟨c₀, hc₀a, hc₀n⟩ := L.exists_approx (a₂ - 1) hγp
  have hc₀1 : ‖L.val c₀‖ < 1 := hc₀n.trans_lt ha₂1
  obtain ⟨y₁, hy₁⟩ := PthPower.exists_eq_mul_pow hp hγM hp0 (u := 1 + L.val c₀) (v := a₂)
    (by rwa [add_sub_cancel_left]) (by
      rw [show a₂ - (1 + L.val c₀) = (a₂ - 1) - L.val c₀ by ring]
      exact hc₀a)
  have hy₁0 : y₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero, mul_zero] at hy₁
    rw [hy₁, zero_sub, norm_neg, norm_one] at ha₂1
    exact lt_irrefl 1 ha₂1
  have hA0 : a * (E₀ * g⁻¹ * y₁⁻¹) ^ p = 1 + L.val c₀ := by
    rw [mul_pow, ← mul_assoc, hstart, hy₁, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy₁0),
      mul_one]
  -- first phase
  obtain ⟨c₁, y₂, hy₂, hc₁n, hc₁P⟩ := L.phase1 hp hp0 hp1 hγM ha₂1 c₀ hc₀n
  have hA1 := step hA0 hc₀1 hy₂
  have hc₁1 : ‖L.val c₁‖ < 1 := hc₁n.trans_lt ha₂1
  have hpγ : ‖(p : C)‖ ≤ ‖γ‖ := by
    rw [← norm_natCast_eq (M := M), ← norm_algebraMap' M γ]
    exact PthPower.norm_natCast_le_norm_gamma hp hγM
  have hγC : ‖γM‖ = ‖γ‖ := norm_algebraMap' M γ
  rcases lt_or_ge ‖γ‖ ‖L.val c₁‖ with hA | hB
  · -- the leading coefficients are not at `p`-th powers
    refine ⟨_, _, hA1, L.visible_of_leading hp c₁ ?_ ?_ hc₁1 fun i hi h ↦ ?_⟩
    · rintro rfl
      rw [val_zero, norm_zero] at hA
      exact (not_lt.2 (_root_.norm_nonneg _)) hA
    · refine le_trans ?_ hA.le
      rw [← hγC]
      exact pow_le_of_le_one (_root_.norm_nonneg _) hγ1.le hp.ne_zero
    · by_contra hU
      have := hc₁P i hU
      rw [h] at this
      exact (lt_irrefl _ ((this.trans_le hpγ).trans hA))
  · -- remove the constant term and apply the second phase
    obtain ⟨c₂, y₃, hy₃, hc₂0, hc₂⟩ := L.remove_const hp c₁ hc₁1
    have hA2 := step hA1 hc₁1 hy₃
    have hc₂i : ∀ i, ‖c₂ i‖ ≤ ‖c₁ i‖ := by
      intro i
      by_cases hi : i = none
      · rw [hi, hc₂0, norm_zero]
        exact _root_.norm_nonneg _
      · rw [hc₂ i hi]
    have hc₂n : ‖L.val c₂‖ ≤ ‖γM‖ := by
      refine (L.norm_val_le_iff c₂ (_root_.norm_nonneg _)).2 fun i ↦ ?_
      rw [hγC]
      exact (hc₂i i).trans ((L.norm_coeff_le_norm_val c₁ i).trans hB)
    have hc₂1 : ‖L.val c₂‖ < 1 := hc₂n.trans_lt hγ1
    have hc₂P : ∀ i, ¬IsU i → ‖c₂ i‖ < ‖(p : C)‖ := fun i hi ↦ (hc₂i i).trans_lt (hc₁P i hi)
    obtain ⟨c₃, y₄, hy₄, hc₃n, hc₃U⟩ := L.phase2 hp hp0 hp1 hγM c₂ hc₂0 hc₂n hc₂P
    have hA3 := step hA2 hc₂1 hy₄
    rcases lt_or_ge ‖L.val c₃‖ (‖γM‖ ^ p) with hsmall | hbig
    · exfalso
      obtain ⟨y₅, hy₅⟩ := PthPower.exists_pow_eq_one_add hp hγM hp0 hsmall
      set Y := E₀ * g⁻¹ * y₁⁻¹ * y₂⁻¹ * y₃⁻¹ * y₄⁻¹
      have hY0 : Y ≠ 0 := by
        intro h
        rw [h, zero_pow hp.ne_zero, mul_zero] at hA3
        have := norm_one_add_eq_one (hc₃n.trans_lt hγ1)
        rw [← hA3, norm_zero] at this
        exact zero_ne_one this
      apply ha (y₅ * Y⁻¹)
      rw [mul_pow, hy₅, ← hA3, inv_pow]
      field_simp
    · refine ⟨_, _, hA3, L.visible_of_leading hp c₃ ?_ ?_ (hc₃n.trans_lt hγ1)
        fun i hi _ ↦ hc₃U i hi⟩
      · rintro rfl
        rw [val_zero, norm_zero] at hbig
        exact (not_le.2 hγp) hbig
      · rwa [← hγC]


variable {E : Type*} [Field E] [Algebra M E] [FiniteDimensional M E]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (w : Valuation E Γ) [(NormedField.valuation (K := M)).HasExtension w]

/-- **F4: Kummer extensions of degree `p` have residue degree `≥ p`.** Let `M ⊇ C` carry a lifted
Frobenius-closed basis (`C` algebraically closed, `M` complete, `0 < ‖p‖ < 1`), `E / M` finite
with a valuation `w` extending the norm valuation, and `ϑ ∈ E` with `ϑ ^ p = a ∈ M`, where
`a ≠ 0` is not a `p`-th power in `M`. Then `p ≤ f(w | M)`. -/
theorem le_inertiaDeg_of_pow_eq (L : LiftedFrobeniusBasis C M p) (hp : p.Prime)
    (hp0 : (p : M) ≠ 0) (hp1 : ‖(p : M)‖ < 1) {ϑ : E} {a : M}
    (hϑ : ϑ ^ p = algebraMap M E a) (ha0 : a ≠ 0) (ha : ∀ y : M, y ^ p ≠ a) :
    p ≤ FundamentalInequality.inertiaDeg (NormedField.valuation (K := M)) w := by
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (-(p : C)) (Nat.sub_pos_of_lt hp.one_lt)
  have hγM : algebraMap C M γ ^ (p - 1) = -(p : M) := by
    rw [← map_pow, hγ, _root_.map_neg, map_natCast]
  obtain ⟨y, b, hab, hvis⟩ := exists_visible L hp hp0 hp1 hγ ha0 ha
  have hϑ' : (ϑ * algebraMap M E y) ^ p = algebraMap M E (1 + b) := by
    rw [mul_pow, hϑ, ← map_pow, ← _root_.map_mul, hab]
  rcases hvis with ⟨t, ht, ht1, hb, hres⟩ | ⟨hb, hres⟩
  · exact le_inertiaDeg_of_insep w hp hγM hϑ' ht ht1 hb hres
  · exact le_inertiaDeg_of_sep w hp hγM hp0 hp1 hϑ' hb hres

/-- **F4, defectless form.** Under the hypotheses of `le_inertiaDeg_of_pow_eq`, if moreover
`[E : M] ≤ p` (e.g. `E = M(ϑ)`), then `e(w | M) = 1` and `f(w | M) = [E : M] = p`: the
extension is defectless. -/
theorem defectless_of_pow_eq (L : LiftedFrobeniusBasis C M p) (hp : p.Prime)
    (hp0 : (p : M) ≠ 0) (hp1 : ‖(p : M)‖ < 1) {ϑ : E} {a : M}
    (hϑ : ϑ ^ p = algebraMap M E a) (ha0 : a ≠ 0) (ha : ∀ y : M, y ^ p ≠ a)
    (hdeg : Module.finrank M E ≤ p) :
    FundamentalInequality.ramificationIdx M w = 1 ∧
      FundamentalInequality.inertiaDeg (NormedField.valuation (K := M)) w =
        Module.finrank M E ∧ Module.finrank M E = p := by
  have hf := le_inertiaDeg_of_pow_eq w L hp hp0 hp1 hϑ ha0 ha
  have hef : FundamentalInequality.ramificationIdx M w *
      FundamentalInequality.inertiaDeg (NormedField.valuation (K := M)) w ≤
        Module.finrank M E :=
    FundamentalInequality.ramificationIdx_mul_inertiaDeg_le
  have he := Nat.pos_of_ne_zero (FundamentalInequality.ramificationIdx_ne_zero (K := M) w)
  have hfle : FundamentalInequality.inertiaDeg (NormedField.valuation (K := M)) w ≤
      Module.finrank M E := le_trans (Nat.le_mul_of_pos_left _ he) hef
  have hfeq : FundamentalInequality.inertiaDeg (NormedField.valuation (K := M)) w =
      Module.finrank M E := le_antisymm hfle (hdeg.trans hf)
  have hn : 0 < Module.finrank M E := Module.finrank_pos
  refine ⟨?_, hfeq, le_antisymm hdeg (hf.trans hfle)⟩
  rw [hfeq] at hef
  exact le_antisymm ((Nat.le_div_iff_mul_le hn).2 hef |>.trans (Nat.div_self hn).le) he

end Assembly

end LiftedFrobeniusBasis

end Lifted

end KummerNormalForm

end SemistableReduction
