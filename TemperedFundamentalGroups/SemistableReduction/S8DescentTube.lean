/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.RatFunc.Luroth
import TemperedFundamentalGroups.SemistableReduction.S8DescentA6
import TemperedFundamentalGroups.SemistableReduction.TwoDirections
import TemperedFundamentalGroups.SemistableReduction.ExhaustGluing
import TemperedFundamentalGroups.SemistableReduction.ChartTwist

/-!
# Descent (S8.C), part 5: the valuative tube condition descends

Blueprint §9.12 O6.6. Let `C(x) ⊆ E ⊆ L` be finite. The valuative tube and disc conditions
(`ExhaustGluing.TubeCond`, `IsTubeDisc`, `IsTubeCircle`: rational residue curves with prescribed
numbers of points over `t̄ = 0, ∞`) descend from `L` to `E`:

* `genus_eq_zero_of_algebra` (**Lüroth**): a function field of one variable inside one of genus
  `0` has genus `0`;
* `card_zeros_of_algebraMap`: if `z ∈ κ₁` has exactly one zero on `κ₂ ⊇ κ₁`, it has exactly one
  zero on `κ₁` (restriction of places is surjective, `sum_ramIdx_eq`);
* `exists_resExt_eq`: every extension of `w_{0,1}` to `E` is the restriction of one to `L` (W4);
* **`tubeCond_descent`**, `isTubeDisc_descent`, `isTubeCircle_descent`.
-/

open IntermediateField IsLocalRing Valuation

namespace SemistableReduction

namespace S8A

namespace Descent

open CurvePlace PlaceNorm

section Genus

variable {k κ₁ κ₂ : Type*} [Field k] [Field κ₁] [Field κ₂] [Algebra k κ₁] [Algebra k κ₂]
  [Algebra κ₁ κ₂] [IsScalarTower k κ₁ κ₂] [IsAlgClosed k]
  [IsCurveFunctionField k κ₁] [IsCurveFunctionField k κ₂]

omit [Algebra κ₁ κ₂] [IsScalarTower k κ₁ κ₂] [IsCurveFunctionField k κ₁] in
/-- A function field of one variable has two distinct places (a zero and a pole of a
transcendental element). -/
lemma exists_ne_place : ∃ P Q : CurvePlace k κ₂, P ≠ Q := by
  obtain ⟨y, hy, -⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
    (κ := κ₂)
  have hyr : y ∉ (algebraMap k κ₂).range := fun ⟨c, hc⟩ ↦ hy (hc ▸ isAlgebraic_algebraMap c)
  have hyir : y⁻¹ ∉ (algebraMap k κ₂).range := fun ⟨c, hc⟩ ↦
    hyr ⟨c⁻¹, by rw [map_inv₀, hc, inv_inv]⟩
  have hne : ∀ z : κ₂, z ∉ (algebraMap k κ₂).range → (zeros k z).Nonempty := by
    intro z hz
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty] at h'
    have hs := sum_ord hz
    rw [h', Finset.sum_empty] at hs
    haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_of_notMem_range hz)
    exact Module.finrank_pos.ne hs
  obtain ⟨P, hP⟩ := hne y hyr
  obtain ⟨Q, hQ⟩ := hne y⁻¹ hyir
  refine ⟨P, Q, fun h ↦ ?_⟩
  rw [mem_zeros] at hP hQ
  rw [inv_inv, ← h] at hQ
  rcases P.V.mem_or_inv_mem y with h1 | h1
  · exact hQ h1
  · exact hP h1

/-- **Lüroth**: a function field of one variable inside one of genus `0` has genus `0`. -/
theorem genus_eq_zero_of_algebra (hg : genus k κ₂ = 0) : genus k κ₁ = 0 := by
  obtain ⟨P, Q, hPQ⟩ := exists_ne_place (k := k) (κ₂ := κ₂)
  obtain ⟨t, -, ht⟩ := exists_divisor_eq_single_sub_single hg P Q
  have htop : k⟮t⟯ = ⊤ := adjoin_eq_top_of_divisor hPQ ht
  have htr : Transcendental k t := by
    obtain ⟨y, hy, -⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
      (κ := κ₂)
    intro halg
    have hbot : k⟮t⟯ = ⊥ := by
      rw [IntermediateField.adjoin_simple_eq_bot_iff]
      obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k t
        (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible halg.isIntegral))
      exact hc ▸ IntermediateField.algebraMap_mem _ c
    have hy' : y ∈ (⊥ : IntermediateField k κ₂) := by
      rw [← hbot, htop]
      trivial
    obtain ⟨d, rfl⟩ := IntermediateField.mem_bot.1 hy'
    exact hy (isAlgebraic_algebraMap d)
  -- `κ₂ ≅ k(X)`
  let e₂ : RatFunc k ≃ₐ[k] κ₂ := (RatFunc.algEquivOfTranscendental t htr).trans
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
  let f : κ₁ →ₐ[k] RatFunc k := e₂.symm.toAlgHom.comp (IsScalarTower.toAlgHom k κ₁ κ₂)
  have hE : f.fieldRange ≠ ⊥ := by
    obtain ⟨y, hy, -⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
      (κ := κ₁)
    intro h
    have hmem : f y ∈ (⊥ : IntermediateField k (RatFunc k)) := h ▸ f.mem_fieldRange.2 ⟨y, rfl⟩
    obtain ⟨d, hd⟩ := IntermediateField.mem_bot.1 hmem
    apply hy
    have h2 : f y = f (algebraMap k κ₁ d) := by rw [AlgHom.commutes]; exact hd.symm
    have : y = algebraMap k κ₁ d := f.toRingHom.injective h2
    rw [this]
    exact isAlgebraic_algebraMap d
  let e : RatFunc k ≃ₐ[k] κ₁ :=
    (RatFunc.Luroth.algEquiv hE).trans (AlgEquiv.ofInjectiveField f).symm
  rw [genus_congr e]
  exact genus_ratFunc k

end Genus

section Zeros

variable {k κ₁ κ₂ : Type*} [Field k] [Field κ₁] [Field κ₂] [Algebra k κ₁] [Algebra k κ₂]
  [Algebra κ₁ κ₂] [IsScalarTower k κ₁ κ₂] [IsAlgClosed k]
  [IsCurveFunctionField k κ₁] [IsCurveFunctionField k κ₂] [FiniteDimensional κ₁ κ₂]

lemma mem_zeros_algebraMap {z : κ₁} {Q : CurvePlace k κ₂} :
    Q ∈ zeros k (algebraMap κ₁ κ₂ z) ↔ resPlace (κ₁ := κ₁) Q ∈ zeros k z := by
  rw [mem_zeros, mem_zeros, mem_resPlace, map_inv₀]

/-- **Restriction of places is surjective.** -/
lemma exists_resPlace_eq (Q₁ : CurvePlace k κ₁) :
    ∃ Q : CurvePlace k κ₂, resPlace (κ₁ := κ₁) Q = Q₁ := by
  obtain ⟨S, hS, hsum⟩ := sum_ramIdx_eq (κ₂ := κ₂) Q₁
  by_contra h
  push Not at h
  have : S = ∅ := Finset.eq_empty_of_forall_notMem fun Q hQ ↦ h Q ((hS Q).1 hQ)
  rw [this, Finset.sum_empty] at hsum
  exact Module.finrank_pos.ne hsum

/-- An element with exactly one zero on `κ₂` has exactly one zero on `κ₁`. -/
theorem card_zeros_of_algebraMap {z : κ₁} (h : (zeros k (algebraMap κ₁ κ₂ z)).card = 1) :
    (zeros k z).card = 1 := by
  obtain ⟨Q, hQ⟩ := Finset.card_eq_one.1 h
  refine Finset.card_eq_one.2 ⟨resPlace (κ₁ := κ₁) Q,
    Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun Q₁ hQ₁ ↦ ?_⟩⟩
  · exact mem_zeros_algebraMap.1 (hQ ▸ Finset.mem_singleton_self Q)
  · obtain ⟨Q', rfl⟩ := exists_resPlace_eq (κ₂ := κ₂) Q₁
    have : Q' ∈ zeros k (algebraMap κ₁ κ₂ z) := mem_zeros_algebraMap.2 hQ₁
    rw [hQ, Finset.mem_singleton] at this
    rw [this]

end Zeros

section Tube

open GaussFibre GaussTube DiscCount FundamentalInequality DenseCompletion ExhaustGluing
  AffineTwist ClassicalSmooth

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {E L : Type*} [Field E] [Field L] [Algebra (RatFunc C) E] [Algebra (RatFunc C) L]
  [Algebra E L] [IsScalarTower (RatFunc C) E L] [Algebra C E] [Algebra C L]
  [IsScalarTower C (RatFunc C) E] [IsScalarTower C (RatFunc C) L]
  [FiniteDimensional (RatFunc C) E] [FiniteDimensional (RatFunc C) L]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

omit [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] in
include hp hp1 in
/-- Every extension of `w_{0,1}` to `E` is the restriction of an extension to `L`. -/
lemma exists_resExt_eq (v : Ext C E) : ∃ w : Ext C L, resExt w = v := by
  classical
  haveI := finite_ext (F := L) hp hp1
  letI : Fintype (Ext C L) := Fintype.ofFinite _
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  have h := sum_fdeg_eq hp hp1 (L := L) v
  by_contra hne
  push Not at hne
  rw [Finset.sum_eq_zero fun w _ ↦ fdeg_of_ne (hne w)] at h
  exact Module.finrank_pos.ne h

omit [CharZero C] in
lemma genus_resExt (w : Ext C L) (h : genus 𝓀 (ResidueField w.1.valuationSubring) = 0) :
    genus 𝓀 (ResidueField (resExt (E := E) w).1.valuationSubring) = 0 :=
  genus_eq_zero_of_algebra (κ₂ := ResidueField w.1.valuationSubring) h

omit [CharZero C] in
lemma card_zeros_resExt (w : Ext C L)
    (h : (zeros 𝓀 (red C (xF C L) w)).card = 1) :
    (zeros 𝓀 (red C (xF C E) (resExt w))).card = 1 := by
  rw [xF_eq (E := E), red_algebraMap] at h
  exact card_zeros_of_algebraMap h

omit [CharZero C] in
lemma card_zeros_inv_resExt (w : Ext C L)
    (h : (zeros 𝓀 (red C (xF C L) w)⁻¹).card = 1) :
    (zeros 𝓀 (red C (xF C E) (resExt w))⁻¹).card = 1 := by
  rw [xF_eq (E := E), red_algebraMap, ← map_inv₀] at h
  exact card_zeros_of_algebraMap h

attribute [local instance] algebraAffAff

include hp hp1 in
/-- **Discs of tubes descend.** -/
theorem isTubeDisc_descent {b γ : C} (hγ : γ ≠ 0) (h : IsTubeDisc L b hγ) :
    IsTubeDisc E b hγ := by
  haveI := isScalarTower_affAff (E := E) (L := L) b γ hγ
  intro v
  obtain ⟨w, rfl⟩ := exists_resExt_eq hp hp1 (E := Aff b γ hγ E) (L := Aff b γ hγ L) v
  obtain ⟨hg, hc⟩ := h w
  exact ⟨genus_resExt w hg, card_zeros_inv_resExt w hc⟩

include hp hp1 in
/-- **Circles of tubes descend.** -/
theorem isTubeCircle_descent {b γ : C} (hγ : γ ≠ 0) (h : IsTubeCircle L b hγ) :
    IsTubeCircle E b hγ := by
  intro b' hb'
  refine ⟨isTubeDisc_descent hp hp1 hγ (h b' hb').1, fun v ↦ ?_⟩
  haveI := isScalarTower_affAff (E := E) (L := L) b' γ hγ
  obtain ⟨w, rfl⟩ := exists_resExt_eq hp hp1 (E := Aff b' γ hγ E) (L := Aff b' γ hγ L) v
  exact card_zeros_resExt w ((h b' hb').2 w)

include hp hp1 in
/-- **The valuative tube condition descends** from `L` to `E`. -/
theorem tubeCond_descent {a c c' : C} (hc : c ≠ 0) (h : TubeCond L a hc c') :
    TubeCond E a hc c' :=
  ⟨fun γ hγ h1 h2 ↦ isTubeCircle_descent hp hp1 _ (h.1 γ hγ h1 h2),
    fun β γ hγ h1 h2 h3 ↦ isTubeDisc_descent hp hp1 _ (h.2 β γ hγ h1 h2 h3)⟩

end Tube

end Descent

end S8A

end SemistableReduction
