/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.AnnulusModel

/-!
# Charts with the same local ring are étale-locally isomorphic

Blueprint §9.6 (W5), layer M7c: from local rings to the étale-local models of `LocalModel.lean`.

* `awayChart A he = A[1/e] = {x | ∃ n, x eⁿ ∈ A}` (`e ∈ A`), a localization away from `e`
  (`isLocalization_awayChart`), so `A → A[1/e]` is étale (`etale_inclusion_awayChart`);
* `exists_awayChart_eq`: if two charts `B, C` of finite type over the base have the same local
  ring at the center of `W`, they have a common basic open neighbourhood of the center:
  `B[1/u] = C[1/u']` with `W`-units `u ∈ B`, `u' ∈ C`;
* `isEtaleLocallyAt_of_localAt_eq`, `isSemistableAt_of_localAt_eq`: hence `C` is étale-locally
  `M` (resp. semistable) at its center of `W` as soon as `B` is;
* `exists_centerIdeal_eq`: every prime of a chart is the center of a valuation subring
  (Chevalley).
-/

universe u

open IsLocalRing

namespace SemistableReduction

variable {F : Type u} [Field F]

/-! ### Localizations away from an element, inside `F` -/

section Away

variable {A : Subring F} {e : F}

/-- The localization `A[1/e] = {x | ∃ n, x eⁿ ∈ A}` of the subring `A` away from `e ∈ A`. -/
def awayChart (A : Subring F) (he : e ∈ A) : Subring F where
  carrier := {x | ∃ n : ℕ, x * e ^ n ∈ A}
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨n + m, ?_⟩
    rw [show x * y * e ^ (n + m) = (x * e ^ n) * (y * e ^ m) by ring]
    exact A.mul_mem hx hy
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨n + m, ?_⟩
    rw [show (x + y) * e ^ (n + m) = (x * e ^ n) * e ^ m + (y * e ^ m) * e ^ n by ring]
    exact A.add_mem (A.mul_mem hx (A.pow_mem he m)) (A.mul_mem hy (A.pow_mem he n))
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨n, hx⟩
    exact ⟨n, by rw [neg_mul]; exact A.neg_mem hx⟩

lemma mem_awayChart (he : e ∈ A) {x : F} : x ∈ awayChart A he ↔ ∃ n : ℕ, x * e ^ n ∈ A :=
  Iff.rfl

lemma le_awayChart (he : e ∈ A) : A ≤ awayChart A he := fun x hx ↦ ⟨0, by simpa using hx⟩

lemma inv_mem_awayChart (he : e ∈ A) (he0 : e ≠ 0) : e⁻¹ ∈ awayChart A he :=
  ⟨1, by rw [pow_one, inv_mul_cancel₀ he0]; exact A.one_mem⟩

/-- `A[1/e]` is the localization of `A` away from `e`. -/
theorem isLocalization_awayChart (he : e ∈ A) (he0 : e ≠ 0) :
    letI := (Subring.inclusion (le_awayChart he)).toAlgebra
    IsLocalization.Away (⟨e, he⟩ : A) (awayChart A he) := by
  letI := (Subring.inclusion (le_awayChart he)).toAlgebra
  change IsLocalization (Submonoid.powers _) _
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    refine isUnit_iff_exists_inv.2 ⟨⟨e⁻¹ ^ n, ⟨n, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [← mul_pow, inv_mul_cancel₀ he0, one_pow]; exact A.one_mem
    · change e ^ n * e⁻¹ ^ n = 1
      rw [← mul_pow, mul_inv_cancel₀ he0, one_pow]
  · rintro ⟨z, n, hz⟩
    exact ⟨(⟨z * e ^ n, hz⟩, ⟨⟨e ^ n, A.pow_mem he n⟩, n, rfl⟩), Subtype.ext rfl⟩
  · intro x y hxy
    refine ⟨1, ?_⟩
    have h : ((algebraMap A (awayChart A he) x : awayChart A he) : F) =
        ((algebraMap A (awayChart A he) y : awayChart A he) : F) := congrArg Subtype.val hxy
    have : x = y := Subtype.ext h
    rw [this]

/-- `A → A[1/e]` is étale. -/
theorem etale_inclusion_awayChart (he : e ∈ A) (he0 : e ≠ 0) :
    (Subring.inclusion (le_awayChart he)).Etale := by
  letI := (Subring.inclusion (le_awayChart he)).toAlgebra
  haveI := isLocalization_awayChart he he0
  exact Algebra.Etale.of_isLocalizationAway (⟨e, he⟩ : A)

/-- `A[1/e]` is contained in `W` if `e ∈ A ⊆ W` is a `W`-unit. -/
lemma awayChart_le {W : ValuationSubring F} (he : e ∈ A) (hAW : A ≤ W.toSubring)
    (heW : W.valuation e = 1) : awayChart A he ≤ W.toSubring := by
  rintro x ⟨n, hx⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at heW
  have : x = (x * e ^ n) * (e⁻¹) ^ n := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ he0, one_pow, mul_one]
  rw [this]
  refine W.mul_mem _ _ (hAW hx) (W.pow_mem ?_ _)
  change e⁻¹ ∈ W
  rw [← W.valuation_le_one_iff, map_inv₀, heW, inv_one]

end Away

/-! ### A common basic open neighbourhood -/

section Common

variable {R B C : Subring F} {W : ValuationSubring F}

/-- A chart generated over `R ⊆ B` by a finite set contained in `localAt B W` lies in `B[1/g]`
for a `W`-unit `g ∈ B`. -/
lemma exists_le_awayChart (hRB : R ≤ B) (s : Finset F)
    (hs : ∀ x ∈ s, x ∈ localAt B W) :
    ∃ (g : F) (hg : g ∈ B), W.valuation g = 1 ∧
      Subring.closure ((R : Set F) ∪ s) ≤ awayChart B hg := by
  classical
  choose g hgB hgW hxg using hs
  set G := ∏ x ∈ s.attach, g x.1 x.2
  have hGB : G ∈ B := Subring.prod_mem _ fun x _ ↦ hgB x.1 x.2
  have hGW : W.valuation G = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun x _ ↦ hgW x.1 x.2
  refine ⟨G, hGB, hGW, Subring.closure_le.2 (Set.union_subset
    (fun x hx ↦ le_awayChart hGB (hRB hx)) fun x hx ↦ ⟨1, ?_⟩)⟩
  rw [pow_one]
  have hmem : (⟨x, hx⟩ : s) ∈ s.attach := Finset.mem_attach _ _
  have hG : G = g x hx * ∏ y ∈ s.attach.erase ⟨x, hx⟩, g y.1 y.2 :=
    (Finset.mul_prod_erase _ (fun y : s ↦ g y.1 y.2) hmem).symm
  rw [hG, ← mul_assoc]
  exact B.mul_mem (hxg x hx) (Subring.prod_mem _ fun y _ ↦ hgB y.1 y.2)

/-- The key inclusion of basic opens (exponent bookkeeping). -/
lemma awayChart_le_awayChart {P Q : Subring F} {p q : F} {N M : ℕ} (hq : q ∈ Q)
    (hpQ : p * q ^ M ∈ Q) (hPQ : P ≤ awayChart Q hq)
    (h₁ : p ^ (N + 1) * q ∈ P) (h₂ : q ^ (M + 1) * p ∈ Q) :
    awayChart P h₁ ≤ awayChart Q h₂ := by
  rintro x ⟨n, hx⟩
  obtain ⟨k, hk⟩ := hPQ hx
  refine ⟨n * (N + 1) + n + k, ?_⟩
  have heq : x * (q ^ (M + 1) * p) ^ (n * (N + 1) + n + k) =
      (x * (p ^ (N + 1) * q) ^ n * q ^ k) * (p * q ^ M) ^ (n + k) *
        q ^ (n * (N + 1) * (M + 1)) := by
    ring
  rw [heq]
  exact Q.mul_mem (Q.mul_mem hk (Q.pow_mem hpQ _)) (Q.pow_mem hq _)

/-- **Common basic open neighbourhood.** If the charts `B` and `C` (of finite type over `R`) have
the same local ring at the center of `W`, then `B[1/u] = C[1/u']` for `W`-units `u ∈ B`,
`u' ∈ C`. -/
theorem exists_awayChart_eq (hRB : R ≤ B) (hRC : R ≤ C) (sB sC : Finset F)
    (hB : B = Subring.closure ((R : Set F) ∪ sB)) (hC : C = Subring.closure ((R : Set F) ∪ sC))
    (hloc : localAt C W = localAt B W) :
    ∃ (u : F) (hu : u ∈ B) (u' : F) (hu' : u' ∈ C), W.valuation u = 1 ∧ W.valuation u' = 1 ∧
      awayChart B hu = awayChart C hu' := by
  obtain ⟨g, hgB, hgW, hCg⟩ := exists_le_awayChart hRB sC fun x hx ↦ by
    rw [← hloc]; exact le_localAt (hC ▸ Subring.subset_closure (Or.inr hx))
  obtain ⟨h, hhC, hhW, hBh⟩ := exists_le_awayChart hRC sB fun x hx ↦ by
    rw [hloc]; exact le_localAt (hB ▸ Subring.subset_closure (Or.inr hx))
  rw [← hC] at hCg
  rw [← hB] at hBh
  obtain ⟨N, hN⟩ := hCg hhC
  obtain ⟨M, hM⟩ := hBh hgB
  have h₁ : g ^ (N + 1) * h ∈ B := by
    rw [pow_succ, mul_comm (g ^ N) g, mul_assoc, mul_comm (g ^ N)]
    exact B.mul_mem hgB hN
  have h₂ : h ^ (M + 1) * g ∈ C := by
    rw [pow_succ, mul_comm (h ^ M) h, mul_assoc, mul_comm (h ^ M)]
    exact C.mul_mem hhC hM
  refine ⟨_, h₁, _, h₂, ?_, ?_, le_antisymm ?_ ?_⟩
  · rw [map_mul, map_pow, hgW, hhW, one_pow, one_mul]
  · rw [map_mul, map_pow, hgW, hhW, one_pow, one_mul]
  · exact awayChart_le_awayChart hhC hM hBh h₁ h₂
  · exact awayChart_le_awayChart hgB hN hCg h₂ h₁

end Common

/-! ### Transfer of étale-local structure -/

section Transfer

variable {K : Type u} [Field K] [Algebra K F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} [Algebra v.valuationSubring F] [IsScalarTower v.valuationSubring K F]

/-- The inclusion of charts as a map of `O`-algebras. -/
def chartIncl {A A' : Subring F} [Algebra v.valuationSubring A] [Algebra v.valuationSubring A']
    (h : A ≤ A')
    (hA : ∀ o, ((algebraMap v.valuationSubring A o : A) : F) = algebraMap v.valuationSubring F o)
    (hA' : ∀ o, ((algebraMap v.valuationSubring A' o : A') : F) =
      algebraMap v.valuationSubring F o) :
    A →ₐ[v.valuationSubring] A' :=
  { Subring.inclusion h with
    commutes' := fun o ↦ Subtype.ext ((hA o).trans (hA' o).symm) }

lemma comap_centerIdeal {A A' : Subring F} {W : ValuationSubring F} (h : A ≤ A')
    (hA'W : A' ≤ W.toSubring) :
    (centerIdeal A' W hA'W).comap (Subring.inclusion h) = centerIdeal A W (h.trans hA'W) :=
  rfl

variable {W : ValuationSubring F} {B C : Subring F} [Algebra v.valuationSubring B]
  [Algebra v.valuationSubring C]

/-- **Charts with the same local ring are étale-locally isomorphic.** If the charts `B, C` (of
finite type over the base) have the same local ring at the center of `W` and `B` is étale-locally
`M` there, then so is `C`. -/
theorem isEtaleLocallyAt_of_localAt_eq {M : Type u} [CommRing M] [Algebra v.valuationSubring M]
    (hBc : ∀ o, ((algebraMap v.valuationSubring B o : B) : F) = algebraMap v.valuationSubring F o)
    (hCc : ∀ o, ((algebraMap v.valuationSubring C o : C) : F) = algebraMap v.valuationSubring F o)
    (hRB : baseRing F v.valuationSubring ≤ B) (hRC : baseRing F v.valuationSubring ≤ C)
    (sB sC : Finset F)
    (hB : B = Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ sB))
    (hC : C = Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ sC))
    (hBW : B ≤ W.toSubring) (hCW : C ≤ W.toSubring) (hloc : localAt C W = localAt B W)
    (h : IsEtaleLocallyAt v.valuationSubring M (centerIdeal B W hBW)) :
    IsEtaleLocallyAt v.valuationSubring M (centerIdeal C W hCW) := by
  obtain ⟨u, hu, u', hu', huW, hu'W, hD⟩ := exists_awayChart_eq hRB hRC sB sC hB hC hloc
  have hu0 : u ≠ 0 := by rintro rfl; simp at huW
  have hu'0 : u' ≠ 0 := by rintro rfl; simp at hu'W
  set D := awayChart C hu'
  have hDW : D ≤ W.toSubring := awayChart_le hu' hCW hu'W
  have hRD : baseRing F v.valuationSubring ≤ D := hRC.trans (le_awayChart hu')
  letI : Algebra v.valuationSubring D := ZariskiModel.chartAlgebra hRD
  have hDc : ∀ o, ((algebraMap v.valuationSubring D o : D) : F) =
      algebraMap v.valuationSubring F o := fun _ ↦ rfl
  have hBD : B ≤ D := hD ▸ le_awayChart hu
  have hCD : C ≤ D := le_awayChart hu'
  have hetB : (Subring.inclusion hBD).Etale := by
    have key : ∀ (D' : Subring F) (hD' : D' = awayChart B hu) (h' : B ≤ D'),
        (Subring.inclusion h').Etale := by
      rintro D' rfl h'
      exact etale_inclusion_awayChart hu hu0
    exact key D hD.symm hBD
  have hetC : (Subring.inclusion hCD).Etale := etale_inclusion_awayChart hu' hu'0
  set Q := centerIdeal D W hDW
  have h₁ : IsEtaleLocallyAt v.valuationSubring M Q :=
    IsEtaleLocallyAt.of_etale (chartIncl hBD hBc hDc) hetB Q
      (by rw [show Q.comap (chartIncl hBD hBc hDc).toRingHom = centerIdeal B W hBW from rfl];
          exact h)
  exact IsEtaleLocallyAt.of_etale_of_comap (chartIncl hCD hCc hDc) hetC h₁

/-- Semistability at the center transfers between charts with the same local ring. -/
theorem isSemistableAt_of_localAt_eq {ϖ : v.valuationSubring}
    (hBc : ∀ o, ((algebraMap v.valuationSubring B o : B) : F) = algebraMap v.valuationSubring F o)
    (hCc : ∀ o, ((algebraMap v.valuationSubring C o : C) : F) = algebraMap v.valuationSubring F o)
    (hRB : baseRing F v.valuationSubring ≤ B) (hRC : baseRing F v.valuationSubring ≤ C)
    (sB sC : Finset F)
    (hB : B = Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ sB))
    (hC : C = Subring.closure ((baseRing F v.valuationSubring : Set F) ∪ sC))
    (hBW : B ≤ W.toSubring) (hCW : C ≤ W.toSubring) (hloc : localAt C W = localAt B W)
    (h : IsSemistableAt ϖ (centerIdeal B W hBW)) : IsSemistableAt ϖ (centerIdeal C W hCW) := by
  rcases h with ⟨n, h⟩ | h
  · exact .inl ⟨n, isEtaleLocallyAt_of_localAt_eq hBc hCc hRB hRC sB sC hB hC hBW hCW hloc h⟩
  · exact .inr (isEtaleLocallyAt_of_localAt_eq hBc hCc hRB hRC sB sC hB hC hBW hCW hloc h)

end Transfer

/-! ### Primes of charts are centers -/

/-- **Chevalley**: every prime `𝔭` of a subring `A ⊆ F` is the center `𝔪_W ∩ A` of a valuation
subring `W ⊇ A`. -/
theorem exists_centerIdeal_eq (A : Subring F) (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (W : ValuationSubring F) (h : A ≤ W.toSubring), centerIdeal A W h = 𝔭 := by
  obtain ⟨W, hle, hloc⟩ := (LocalSubring.ofPrime A 𝔭).exists_le_valuationSubring
  set L := (LocalSubring.ofPrime A 𝔭).toSubring
  have hAW : A ≤ W.toSubring := (LocalSubring.le_ofPrime A 𝔭).trans hle
  refine ⟨W, hAW, ?_⟩
  ext a
  rw [mem_centerIdeal_iff]
  constructor
  · intro ha
    by_contra hna
    have hu : IsUnit (algebraMap A L a) :=
      IsLocalization.map_units L (⟨a, hna⟩ : 𝔭.primeCompl)
    obtain ⟨w, hw⟩ := hu.exists_left_inv
    have hw' : ((w : L) : F) * a = 1 := congrArg Subtype.val hw
    have ha0 : (a : F) ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hw'
      exact zero_ne_one hw'
    have hinv : (a : F)⁻¹ ∈ W := by
      rw [← eq_inv_of_mul_eq_one_left hw']
      exact hle w.2
    have h1 : W.valuation (a : F) = 1 :=
      (valuation_eq_one_iff_mem_and_inv_mem W).2 ⟨ha0, hAW a.2, hinv⟩
    rw [h1] at ha
    exact lt_irrefl _ ha
  · intro ha
    by_contra hlt
    have h1 : W.valuation (a : F) = 1 :=
      le_antisymm ((W.valuation_le_one_iff _).2 (hAW a.2)) (not_lt.1 hlt)
    obtain ⟨ha0, -, hinv⟩ := (valuation_eq_one_iff_mem_and_inv_mem W).1 h1
    have hunitW : IsUnit (Subring.inclusion hle (algebraMap A L a)) :=
      isUnit_iff_exists_inv.2 ⟨⟨(a : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
    have hunitL : IsUnit (algebraMap A L a) := hloc.map_nonunit _ hunitW
    have hmax : algebraMap A L a ∈ maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L 𝔭 a).2 ha
    exact hmax hunitL

end SemistableReduction
