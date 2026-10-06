/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChartLocal
import TemperedFundamentalGroups.SemistableReduction.PlaceNorm

/-!
# Intrinsic local `δ`-invariants of the closed points of an affine chart

Blueprint §9.12, O12 / R5 (abstract part). For an affine chart `Λ ⊆ Π_j κ j` (`ChartLocal.IsChart`)
the local `δ`-invariant `ChartLocal.delta` of S7⁺ depends on a conductor element `σ` only through
the set of branches of the point. Here:

* `brs 𝔫`: all branches with centre `𝔫` (finite for `𝔫 ≠ ⊤`, `brs_finite`), `brsF 𝔫` the finset;
* `dl 𝔫 M`: the `δ`-invariant at jet order `M` with the branches `brsF 𝔫`;
  `delta_eq_dl`: `delta σ 𝔫 M = dl 𝔫 M` for `𝔫 ∈ points σ`;
* `dl_eq_zero_of_conductor`: `dl 𝔫 M = 0` if a conductor element is a unit at `𝔫`;
* `dl_mono`: `dl 𝔫` is monotone in `M`; `dinf 𝔫 = sup_M dl 𝔫 M`;
* `card_sub_one_le_dl`: `δ ≥ r - 1`;
* `exists_locSet_of_dl_eq_zero` (one branch, `δ = 0`) and `eqRes_le_of_dl_eq` (`δ = r - 1`):
  the jet forms of smooth points and ordinary double points.
-/

open WithZero Polynomial

namespace SemistableReduction

namespace ChartLocal

open DeltaCount CurvePlace

variable {k : Type*} [Field k] [IsAlgClosed k] {J : Type*} {κ : J → Type*}
  [∀ j, Field (κ j)] [∀ j, Algebra k (κ j)] [∀ j, IsCurveFunctionField k (κ j)]

variable {z : Π j, κ j} {Λ : Subring (Π j, κ j)} (hΛ : IsChart k z Λ)
include hΛ

/-! ### Branches of a closed point -/

/-- The branches of the closed point `𝔫`: the branches whose centre is `𝔫`. -/
def brs (𝔫 : Ideal Λ) : Set (Branch k κ) := {b | centerOf hΛ b = 𝔫}

lemma mem_brs {𝔫 : Ideal Λ} {b : Branch k κ} : b ∈ brs hΛ 𝔫 ↔ centerOf hΛ b = 𝔫 := Iff.rfl

lemma mem_V_of_mem_brs {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {b : Branch k κ} (hb : b ∈ brs hΛ 𝔫) :
    z b.1 ∈ b.2.V :=
  mem_V_of_centerOf_ne_top hΛ (by rw [hb]; exact h𝔫)

lemma centerOf_eq {b : Branch k κ} (hb : z b.1 ∈ b.2.V) : centerOf hΛ b = center hΛ b.2 hb := by
  classical
  unfold centerOf
  rw [dif_pos hb]

/-- An element of `Λ` lies in `𝔫` iff its component has positive order at one (every) branch. -/
lemma mem_iff_of_mem_brs {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {b : Branch k κ} (hb : b ∈ brs hΛ 𝔫)
    (a : Λ) : a ∈ 𝔫 ↔ b.2.valuation (a.1 b.1) < 1 := by
  have hz := mem_V_of_mem_brs hΛ h𝔫 hb
  rw [← (show centerOf hΛ b = 𝔫 from hb), centerOf_eq hΛ hz, mem_center]

/-- Elements of `Λ` are regular at the branches of a proper ideal. -/
lemma mem_V_of_mem_brs' {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {b : Branch k κ} (hb : b ∈ brs hΛ 𝔫)
    (a : Λ) : a.1 b.1 ∈ b.2.V :=
  hΛ.le a.2 b.1 b.2 (mem_V_of_mem_brs hΛ h𝔫 hb)

/-- An element of `Λ ∖ 𝔫` is a unit at the branches of `𝔫`. -/
lemma valuation_eq_one_of_notMem {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {b : Branch k κ}
    (hb : b ∈ brs hΛ 𝔫) {a : Λ} (ha : a ∉ 𝔫) : b.2.valuation (a.1 b.1) = 1 :=
  le_antisymm (b.2.valuation_le_one_iff.2 (mem_V_of_mem_brs' hΛ h𝔫 hb a))
    (not_lt.1 fun h ↦ ha ((mem_iff_of_mem_brs hΛ h𝔫 hb a).2 h))

/-- The constant `c ∈ k` as an element of `Λ`. -/
def constΛ (c : k) : Λ := ⟨fun j ↦ algebraMap k (κ j) c, hΛ.const c⟩

/-- All branches of a point have the same residue map on `Λ`. -/
lemma res_eq_of_mem_brs {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {b b' : Branch k κ} (hb : b ∈ brs hΛ 𝔫)
    (hb' : b' ∈ brs hΛ 𝔫) (a : Λ) : b.2.res (a.1 b.1) = b'.2.res (a.1 b'.1) := by
  set c := b.2.res (a.1 b.1)
  have h1 : a - constΛ hΛ c ∈ 𝔫 := by
    rw [mem_iff_of_mem_brs hΛ h𝔫 hb]
    exact b.2.valuation_sub_res_lt_one (mem_V_of_mem_brs' hΛ h𝔫 hb a)
  rw [mem_iff_of_mem_brs hΛ h𝔫 hb'] at h1
  exact (b'.2.res_eq_of_valuation_sub_lt_one h1).symm

omit hΛ in
/-- `b` is a zero of `σ` (`σ b.1 ≠ 0`) iff `σ` has positive order at `b`. -/
lemma mem_zeros_iff [Fintype J] {σ : Π j, κ j} {b : Branch k κ} (hne : σ b.1 ≠ 0) :
    b ∈ zeros k κ σ ↔ b.2.valuation (σ b.1) < 1 := by
  rw [mem_zeros, ← b.2.valuation_le_one_iff, map_inv₀, not_le,
    one_lt_inv₀ ((Valuation.pos_iff _).2 hne)]

/-- **Finiteness of the branches** of a proper ideal. -/
lemma brs_finite [Finite J] {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) : (brs hΛ 𝔫).Finite := by
  classical
  haveI := Fintype.ofFinite J
  rcases (brs hΛ 𝔫).eq_empty_or_nonempty with he | ⟨b₀, hb₀⟩
  · rw [he]; exact Set.finite_empty
  set c := b₀.2.res (z b₀.1)
  set σ : Λ := ⟨z, hΛ.mem⟩ - constΛ hΛ c
  have hσ : σ ∈ 𝔫 := by
    rw [mem_iff_of_mem_brs hΛ h𝔫 hb₀]
    exact b₀.2.valuation_sub_res_lt_one (mem_V_of_mem_brs hΛ h𝔫 hb₀)
  refine (zeros k κ σ.1).finite_toSet.subset fun b hb ↦ ?_
  have hlt : b.2.valuation (σ.1 b.1) < 1 := (mem_iff_of_mem_brs hΛ h𝔫 hb σ).1 hσ
  have hne : σ.1 b.1 ≠ 0 := by
    intro h
    apply hΛ.tr b.1
    have : z b.1 = algebraMap k (κ b.1) c := by
      have h' : z b.1 - algebraMap k (κ b.1) c = 0 := h
      exact sub_eq_zero.1 h'
    rw [this]
    exact isAlgebraic_algebraMap c
  rw [Finset.mem_coe, mem_zeros_iff hne]
  exact hlt

/-- Every maximal ideal has a branch. -/
lemma exists_mem_brs [Finite J] {𝔫 : Ideal Λ} (h𝔫 : 𝔫.IsMaximal) : ∃ b, b ∈ brs hΛ 𝔫 := by
  obtain ⟨j, Q, hQ, hc⟩ := exists_center_eq hΛ 𝔫
  exact ⟨⟨j, Q⟩, by rw [mem_brs, centerOf_eq hΛ hQ]; exact hc⟩

open Classical in
/-- The branches of `𝔫` as a finset (empty for `𝔫 = ⊤`). -/
noncomputable def brsF (𝔫 : Ideal Λ) : Finset (Branch k κ) :=
  if h : (brs hΛ 𝔫).Finite then h.toFinset else ∅

lemma mem_brsF [Finite J] {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {b : Branch k κ} :
    b ∈ brsF hΛ 𝔫 ↔ b ∈ brs hΛ 𝔫 := by
  classical
  rw [brsF, dif_pos (brs_finite hΛ h𝔫), Set.Finite.mem_toFinset]

lemma mem_V_of_mem_brsF [Finite J] {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {b : Branch k κ}
    (hb : b ∈ brsF hΛ 𝔫) : z b.1 ∈ b.2.V :=
  mem_V_of_mem_brs hΛ h𝔫 ((mem_brsF hΛ h𝔫).1 hb)

/-- For `𝔫 ∈ points σ` (`σ ∈ Λ` nonzero on every component), the branches of `𝔫` among the zeros
of `σ` are all the branches of `𝔫`. -/
lemma branches_eq_brsF [Fintype J] {σ : Π j, κ j} (hσ : σ ∈ Λ) (hσ0 : ∀ j, σ j ≠ 0)
    {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ∈ points hΛ σ) : branches hΛ σ 𝔫 = brsF hΛ 𝔫 := by
  classical
  have hmax := isMaximal_of_mem_points hΛ h𝔫
  have hσ𝔫 : (⟨σ, hσ⟩ : Λ) ∈ 𝔫 := by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h𝔫
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h1
    have hz := mem_V_of_centerOf_ne_top hΛ h2
    rw [centerOf_eq hΛ hz, mem_center]
    exact (mem_zeros_iff (hσ0 b.1)).1 hb
  ext b
  rw [mem_brsF hΛ hmax.ne_top, branches, Finset.mem_filter, mem_brs]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  exact (mem_zeros_iff (hσ0 b.1)).2
    ((mem_iff_of_mem_brs hΛ hmax.ne_top (show b ∈ brs hΛ 𝔫 from h) ⟨σ, hσ⟩).1 hσ𝔫)

/-! ### The local `δ`-invariant of a closed point -/

variable (k κ) in
/-- The local `δ`-invariant (at jet order `M`) of the closed point `𝔫`, with all its branches. -/
noncomputable def dl (𝔫 : Ideal Λ) (M : ℕ) : ℕ :=
  Module.finrank k (regAt k κ (brsF hΛ 𝔫) ⧸
    (locSpace k 𝔫 ⊔ jetKer k κ M (brsF hΛ 𝔫)).comap (regAt k κ (brsF hΛ 𝔫)).subtype)

/-- `delta` with a conductor element is `dl`. -/
lemma delta_eq_dl [Fintype J] {σ : Π j, κ j} (hσ : σ ∈ Λ) (hσ0 : ∀ j, σ j ≠ 0) {𝔫 : Ideal Λ}
    (h𝔫 : 𝔫 ∈ points hΛ σ) (M : ℕ) : delta k κ hΛ σ 𝔫 M = dl k κ hΛ 𝔫 M := by
  rw [delta, dl, branches_eq_brsF hΛ hσ hσ0 h𝔫]

omit hΛ in
/-- **Jet approximation by regular elements**: an element regular at finitely many branches
containing `z` agrees to order `M` there with an element regular at all places containing `z`. -/
theorem exists_regRing_sub_mem_jetKer [Finite J] (hz : ∀ j, Transcendental k (z j))
    {S : Finset (Branch k κ)} (hS : ∀ b ∈ S, z b.1 ∈ b.2.V) (M : ℕ) {a : Π j, κ j}
    (ha : a ∈ regAt k κ S) : ∃ f ∈ regRing k κ z, a - f ∈ jetKer k κ M S := by
  classical
  choose c hc using fun j ↦ CurvePlace.exists_jet (k := k) (κ := κ j)
  have hzr (j : J) : z j ∉ (algebraMap k (κ j)).range := fun ⟨a, ha⟩ ↦
    hz j (ha ▸ isAlgebraic_algebraMap a)
  set S' : (j : J) → Finset (CurvePlace k (κ j)) := fun j ↦
    S.preimage (fun Q : CurvePlace k (κ j) ↦ (⟨j, Q⟩ : Branch k κ))
      fun _ _ _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.1 h).2
  set n : J → ℕ := fun j ↦ (c j + M * (S' j).card).toNat
  set D : ∀ j, CurveDivisor k (κ j) := fun j ↦ n j • poleDivisor k (z j)
  have hdeg (j : J) : c j + M * (S' j).card ≤ (D j).degree := by
    rw [map_nsmul, degree_poleDivisor (hzr j), nsmul_eq_mul]
    have h1 : (1 : ℤ) ≤ (Module.finrank (IntermediateField.adjoin k {z j}) (κ j) : ℤ) := by
      haveI := IsCurveFunctionField.finiteDimensional_adjoin (k := k) (hz j)
      exact_mod_cast Module.finrank_pos
    have h2 := Int.self_le_toNat (c j + M * (S' j).card)
    nlinarith [Int.natCast_nonneg (c j + M * (S' j).card).toNat]
  have hD0 (j : J) (Q : CurvePlace k (κ j)) (hQ : z j ∈ Q.V) : D j Q = 0 := by
    simp [D, poleDivisor_apply, Q.poleOrder_eq_zero_iff.2 hQ]
  have hj (j : J) := hc j (D j) (S' j) M (hdeg j)
    (fun Q hQ ↦ hD0 j Q (hS _ (Finset.mem_preimage.1 hQ))) (fun _ ↦ a j)
    (fun Q hQ ↦ ha ⟨j, Q⟩ (Finset.mem_preimage.1 hQ))
  choose f hf hfQ using hj
  refine ⟨f, fun j Q hQ ↦ ?_, fun b hb ↦ ?_⟩
  · have := hf j Q
    rw [hD0 j Q hQ, exp_zero] at this
    exact Q.valuation_le_one_iff.1 this
  · have := hfQ b.1 b.2 (Finset.mem_preimage.2 hb)
    rw [← Valuation.map_neg, neg_sub] at this
    exact this

/-- **No `δ` away from a conductor element**: if `σ` is in the conductor and `σ ∉ 𝔫`, then
`dl 𝔫 M = 0`. -/
theorem dl_eq_zero_of_conductor [Finite J] {σ : Π j, κ j} (hσ : σ ∈ Λ)
    (hcond : ∀ v ∈ regRing k κ z, σ * v ∈ Λ) {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤)
    (hσ𝔫 : (⟨σ, hσ⟩ : Λ) ∉ 𝔫) (M : ℕ) : dl k κ hΛ 𝔫 M = 0 := by
  have htop : (locSpace k 𝔫 ⊔ jetKer k κ M (brsF hΛ 𝔫)).comap
      (regAt k κ (brsF hΛ 𝔫)).subtype = ⊤ := by
    refine eq_top_iff.2 fun a _ ↦ ?_
    rw [Submodule.mem_comap, Submodule.coe_subtype]
    obtain ⟨f, hf, haf⟩ := exists_regRing_sub_mem_jetKer hΛ.tr
      (fun b hb ↦ mem_V_of_mem_brsF hΛ h𝔫 hb) M a.2
    have hfloc : f ∈ locSpace k 𝔫 := subset_locSpace 𝔫 ⟨⟨σ, hσ⟩, hσ𝔫, hcond f hf⟩
    have : (a : Π j, κ j) = f + (a - f) := by ring
    rw [this]
    exact add_mem (Submodule.mem_sup_left hfloc) (Submodule.mem_sup_right haf)
  rw [dl, htop]
  haveI : Subsingleton (regAt k κ (brsF hΛ 𝔫) ⧸ (⊤ : Submodule k (regAt k κ (brsF hΛ 𝔫)))) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  exact Module.finrank_zero_of_subsingleton

/-- `dl` is monotone in the jet order. -/
theorem dl_mono [Finite J] {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {M M' : ℕ} (h : M ≤ M') :
    dl k κ hΛ 𝔫 M ≤ dl k κ hΛ 𝔫 M' := by
  set S := brsF hΛ 𝔫
  set A := regAt k κ S
  have hle : (locSpace k 𝔫 ⊔ jetKer k κ M' S).comap A.subtype ≤
      (locSpace k 𝔫 ⊔ jetKer k κ M S).comap A.subtype := by
    refine Submodule.comap_mono (sup_le_sup_left (fun a ha b hb ↦ (ha b hb).trans ?_) _)
    rw [exp_le_exp]
    omega
  haveI := finiteDimensional_regAt_quot hΛ.tr (fun b hb ↦ mem_V_of_mem_brsF hΛ h𝔫 hb) M'
    (locSpace k 𝔫)
  exact LinearMap.finrank_le_finrank_of_surjective (f := Submodule.factor hle)
    (Submodule.factor_surjective hle)

variable (k κ) in
/-- The local `δ`-invariant: the supremum over the jet orders. -/
noncomputable def dinf (𝔫 : Ideal Λ) : ℕ := ⨆ M, dl k κ hΛ 𝔫 M

/-- A bounded `dl` reaches `dinf` from some order on. -/
theorem exists_dl_eq_dinf [Finite J] {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {B : ℕ}
    (hB : ∀ M, dl k κ hΛ 𝔫 M ≤ B) : ∃ M₀, ∀ M, M₀ ≤ M → dl k κ hΛ 𝔫 M = dinf k κ hΛ 𝔫 := by
  have hbdd : BddAbove (Set.range (dl k κ hΛ 𝔫)) := ⟨B, by rintro _ ⟨M, rfl⟩; exact hB M⟩
  obtain ⟨M₀, hM₀⟩ : dinf k κ hΛ 𝔫 ∈ Set.range (dl k κ hΛ 𝔫) :=
    Nat.sSup_mem (Set.range_nonempty _) hbdd
  refine ⟨M₀, fun M hM ↦ le_antisymm (le_ciSup hbdd M) ?_⟩
  rw [← hM₀]
  exact dl_mono hΛ h𝔫 hM

lemma dl_le_dinf {𝔫 : Ideal Λ} {B : ℕ} (hB : ∀ M, dl k κ hΛ 𝔫 M ≤ B) (M : ℕ) :
    dl k κ hΛ 𝔫 M ≤ dinf k κ hΛ 𝔫 :=
  le_ciSup ⟨B, by rintro _ ⟨M, rfl⟩; exact hB M⟩ M

/-! ### `δ ≥ r - 1` and its equality case -/

/-- Elements of the local ring have equal residues at the branches. -/
theorem locSpace_le_eqRes [Finite J] {𝔫 : Ideal Λ} [h𝔫 : 𝔫.IsPrime] :
    locSpace k 𝔫 ≤ eqRes k κ (brsF hΛ 𝔫) := by
  have hne := h𝔫.ne_top
  refine Submodule.span_le.2 fun a ⟨s, hs, hsa⟩ ↦ ?_
  have hb (b : Branch k κ) (hb : b ∈ brsF hΛ 𝔫) :
      a b.1 ∈ b.2.V ∧ b.2.res (s.1 b.1) * b.2.res (a b.1) =
        b.2.res ((⟨s.1 * a, hsa⟩ : Λ).1 b.1) ∧ b.2.res (s.1 b.1) ≠ 0 := by
    have hb' := (mem_brsF hΛ hne).1 hb
    have hs1 := valuation_eq_one_of_notMem hΛ hne hb' hs
    have hsV := mem_V_of_mem_brs' hΛ hne hb' s
    have hsaV := mem_V_of_mem_brs' hΛ hne hb' ⟨s.1 * a, hsa⟩
    have hs0 : s.1 b.1 ≠ 0 := fun h ↦ by rw [h, map_zero] at hs1; exact zero_ne_one hs1
    have haV : a b.1 ∈ b.2.V := by
      have : a b.1 = (s.1 * a) b.1 * (s.1 b.1)⁻¹ := by
        rw [Pi.mul_apply]; field_simp
      rw [this]
      refine mul_mem hsaV (b.2.valuation_le_one_iff.1 ?_)
      rw [map_inv₀, hs1, inv_one]
    refine ⟨haV, ?_, fun h ↦ ?_⟩
    · rw [← b.2.res_mul hsV haV]
      rfl
    · rw [CurvePlace.res_eq_zero_iff _ hsV, hs1] at h
      exact lt_irrefl _ h
  refine ⟨fun b hb' ↦ (hb b hb').1, fun b hb₁ b' hb₂ ↦ ?_⟩
  obtain ⟨-, h1, h1'⟩ := hb b hb₁
  obtain ⟨-, h2, h2'⟩ := hb b' hb₂
  have hs := res_eq_of_mem_brs hΛ hne ((mem_brsF hΛ hne).1 hb₁) ((mem_brsF hΛ hne).1 hb₂) s
  have hsa := res_eq_of_mem_brs hΛ hne ((mem_brsF hΛ hne).1 hb₁) ((mem_brsF hΛ hne).1 hb₂)
    ⟨s.1 * a, hsa⟩
  rw [← h1, ← h2, hs] at hsa
  exact mul_left_cancel₀ (hs ▸ h1') hsa

lemma sup_le_eqRes [Finite J] {𝔫 : Ideal Λ} [𝔫.IsPrime] {M : ℕ} (hM : 1 ≤ M) :
    locSpace k 𝔫 ⊔ jetKer k κ M (brsF hΛ 𝔫) ≤ eqRes k κ (brsF hΛ 𝔫) :=
  sup_le (locSpace_le_eqRes hΛ) (jetKer_le_eqRes hM _)

/-- **`δ ≥ r - 1`**. -/
theorem card_sub_one_le_dl [Finite J] {𝔫 : Ideal Λ} [h𝔫 : 𝔫.IsPrime] {M : ℕ} (hM : 1 ≤ M) :
    (brsF hΛ 𝔫).card - 1 ≤ dl k κ hΛ 𝔫 M := by
  classical
  rcases (brsF hΛ 𝔫).eq_empty_or_nonempty with he | ⟨b₀, hb₀⟩
  · rw [he, Finset.card_empty]; exact Nat.zero_le _
  set S := brsF hΛ 𝔫
  set N := locSpace k 𝔫 ⊔ jetKer k κ M S
  set N' := N.comap (regAt k κ S).subtype
  haveI := finiteDimensional_regAt_quot hΛ.tr (fun b hb ↦ mem_V_of_mem_brsF hΛ h𝔫.ne_top hb) M
    (locSpace k 𝔫)
  obtain ⟨A, hAcard, hAreg, hind⟩ := exists_finset_indep_of_le_eqRes S hb₀
  set v : A → regAt k κ S ⧸ N' := fun y ↦ N'.mkQ ⟨y, hAreg y y.2⟩
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hmem : ∑ i, g i • (i : Π j, κ j) ∈ N := by
      have h0 : N'.mkQ (∑ i, g i • (⟨i, hAreg i i.2⟩ : regAt k κ S)) = 0 := by
        rw [map_sum]; simp_rw [map_smul]; exact hg
      have h := (Submodule.Quotient.mk_eq_zero N').1 h0
      rw [Submodule.mem_comap] at h
      simpa using h
    exact congrFun (hind N (sup_le_eqRes hΛ hM) g hmem)
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, hAcard] at this
  exact this

/-- **Equality case of `δ ≥ r - 1`**: if `δ = r - 1`, every element of `eqRes` lies in the local
ring modulo the jets of order `M`. -/
theorem eqRes_le_of_dl_le [Finite J] {𝔫 : Ideal Λ} [h𝔫 : 𝔫.IsPrime] {M : ℕ} (hM : 1 ≤ M)
    (hS : (brsF hΛ 𝔫).Nonempty) (hdl : dl k κ hΛ 𝔫 M ≤ (brsF hΛ 𝔫).card - 1) :
    eqRes k κ (brsF hΛ 𝔫) ≤ locSpace k 𝔫 ⊔ jetKer k κ M (brsF hΛ 𝔫) := by
  classical
  obtain ⟨b₀, hb₀⟩ := hS
  set S := brsF hΛ 𝔫
  set N := locSpace k 𝔫 ⊔ jetKer k κ M S
  set N' := N.comap (regAt k κ S).subtype
  haveI := finiteDimensional_regAt_quot hΛ.tr (fun b hb ↦ mem_V_of_mem_brsF hΛ h𝔫.ne_top hb) M
    (locSpace k 𝔫)
  intro e he
  by_contra heN
  obtain ⟨A, hAcard, hAreg, hind⟩ := exists_finset_indep_of_le_eqRes S hb₀
  set v : Option A → regAt k κ S ⧸ N' := fun o ↦ match o with
    | none => N'.mkQ ⟨e, he.1⟩
    | some y => N'.mkQ ⟨y, hAreg y y.2⟩
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_option] at hg
    have hmem : g none • e + ∑ i, g (some i) • (i : Π j, κ j) ∈ N := by
      have h0 : N'.mkQ (g none • (⟨e, he.1⟩ : regAt k κ S) +
          ∑ i, g (some i) • (⟨i, hAreg i i.2⟩ : regAt k κ S)) = 0 := by
        rw [map_add, map_sum]; simp_rw [map_smul]; exact hg
      have h := (Submodule.Quotient.mk_eq_zero N').1 h0
      rw [Submodule.mem_comap] at h
      simpa using h
    have hE : ∑ i, g (some i) • (i : Π j, κ j) ∈ eqRes k κ S := by
      have h1 := sup_le_eqRes hΛ hM hmem
      have h2 : g none • e ∈ eqRes k κ S := Submodule.smul_mem _ _ he
      have := sub_mem h1 h2
      rwa [add_sub_cancel_left] at this
    have hsome := hind (eqRes k κ S) le_rfl (fun i ↦ g (some i)) hE
    have hnone : g none = 0 := by
      by_contra h0
      apply heN
      have hsum : ∑ i, g (some i) • (i : Π j, κ j) = 0 := by
        exact Finset.sum_eq_zero fun i _ ↦ by
          rw [show g (some i) = 0 from congrFun hsome i, zero_smul]
      rw [hsum, add_zero] at hmem
      have := Submodule.smul_mem N (g none)⁻¹ hmem
      rwa [inv_smul_smul₀ h0] at this
    rintro (_ | i)
    · exact hnone
    · exact congrFun hsome i
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_option, Fintype.card_coe, hAcard] at this
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨b₀, hb₀⟩
  change _ ≤ dl k κ hΛ 𝔫 M at this
  omega

/-- The jet form of `eqRes ≤ locSpace + K_M`: every element with equal residues at the branches is
approximated to order `M` at all branches by an element of the local ring. -/
theorem exists_locSet_of_eqRes_le [Finite J] {𝔫 : Ideal Λ} [h𝔫 : 𝔫.IsPrime] {M : ℕ}
    (h : eqRes k κ (brsF hΛ 𝔫) ≤ locSpace k 𝔫 ⊔ jetKer k κ M (brsF hΛ 𝔫))
    {a : Π j, κ j} (ha : a ∈ eqRes k κ (brsF hΛ 𝔫)) :
    ∃ o ∈ locSet 𝔫, ∀ b ∈ brsF hΛ 𝔫, b.2.valuation (o b.1 - a b.1) ≤ exp (-(M : ℤ)) := by
  obtain ⟨o, ho, kk, hk, hok⟩ := Submodule.mem_sup.1 (h ha)
  refine ⟨o, mem_locSet_of_mem_locSpace hΛ ho, fun b hb ↦ ?_⟩
  have : o b.1 - a b.1 = -kk b.1 := by rw [← hok]; simp
  rw [this, Valuation.map_neg]
  exact hk b hb

/-! ### Sums over closed points -/

/-- A closed point containing `σ` (nonzero on every component) is a point of `σ`. -/
lemma mem_points_of_mem [Fintype J] {σ : Π j, κ j} (hσ : σ ∈ Λ) (hσ0 : ∀ j, σ j ≠ 0)
    {𝔫 : Ideal Λ} (h𝔫 : 𝔫.IsMaximal) (hσ𝔫 : (⟨σ, hσ⟩ : Λ) ∈ 𝔫) : 𝔫 ∈ points hΛ σ := by
  classical
  obtain ⟨b, hb⟩ := exists_mem_brs hΛ h𝔫
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨b, ?_, hb⟩, ?_⟩
  · rw [mem_zeros_iff (hσ0 b.1)]
    exact (mem_iff_of_mem_brs hΛ h𝔫.ne_top hb _).1 hσ𝔫
  · exact h𝔫.ne_top

/-- **Sums of `delta` over the points of a conductor element as finite sums of `dl`.** -/
theorem sum_delta_eq_finsum [Fintype J] {σ : Π j, κ j} (hσ : σ ∈ Λ) (hσ0 : ∀ j, σ j ≠ 0)
    (hcond : ∀ v ∈ regRing k κ z, σ * v ∈ Λ) (P : Ideal Λ → Prop) [DecidablePred P] (M : ℕ) :
    ∑ y ∈ (points hΛ σ).filter P, delta k κ hΛ σ y M =
      ∑ᶠ (𝔫 : Ideal Λ) (_ : 𝔫 ∈ {𝔫 : Ideal Λ | 𝔫.IsMaximal ∧ P 𝔫}), dl k κ hΛ 𝔫 M := by
  classical
  rw [finsum_mem_eq_sum_of_inter_support_eq (t := (points hΛ σ).filter P)]
  · refine Finset.sum_congr rfl fun y hy ↦ ?_
    exact delta_eq_dl hΛ hσ hσ0 (Finset.mem_filter.1 hy).1 M
  · ext 𝔫
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Finset.coe_filter]
    constructor
    · rintro ⟨⟨hmax, hP⟩, hne⟩
      refine ⟨⟨?_, hP⟩, hne⟩
      by_contra hn
      apply hne
      refine dl_eq_zero_of_conductor hΛ hσ hcond hmax.ne_top (fun hσ𝔫 ↦ hn ?_) M
      exact mem_points_of_mem hΛ hσ hσ0 hmax hσ𝔫
    · rintro ⟨⟨hy, hP⟩, hne⟩
      exact ⟨⟨isMaximal_of_mem_points hΛ hy, hP⟩, hne⟩

/-- **Stabilization of `dl`**: if the `δ`-sum over the points of a conductor element satisfying
`P` is bounded for large `M`, then from some order on `dl 𝔫 M = dinf 𝔫` at every maximal ideal
satisfying `P`. -/
theorem exists_forall_dl_eq_dinf [Fintype J] {σ : Π j, κ j} (hσ : σ ∈ Λ) (hσ0 : ∀ j, σ j ≠ 0)
    (hcond : ∀ v ∈ regRing k κ z, σ * v ∈ Λ) (P : Ideal Λ → Prop) [DecidablePred P] {B M₀ : ℕ}
    (hB : ∀ M, M₀ ≤ M → ∑ y ∈ (points hΛ σ).filter P, delta k κ hΛ σ y M ≤ B) :
    ∃ M₁, ∀ M, M₁ ≤ M → ∀ 𝔫 : Ideal Λ, 𝔫.IsMaximal → P 𝔫 →
      dl k κ hΛ 𝔫 M = dinf k κ hΛ 𝔫 := by
  classical
  set T := (points hΛ σ).filter P
  have hbd (𝔫 : Ideal Λ) (h𝔫 : 𝔫 ∈ T) (M : ℕ) : dl k κ hΛ 𝔫 M ≤ B := by
    have h𝔫' := (Finset.mem_filter.1 h𝔫).1
    have hne := (isMaximal_of_mem_points hΛ h𝔫').ne_top
    calc dl k κ hΛ 𝔫 M ≤ dl k κ hΛ 𝔫 (max M M₀) := dl_mono hΛ hne (le_max_left _ _)
      _ = delta k κ hΛ σ 𝔫 (max M M₀) := (delta_eq_dl hΛ hσ hσ0 h𝔫' _).symm
      _ ≤ ∑ y ∈ T, delta k κ hΛ σ y (max M M₀) :=
          Finset.single_le_sum (f := fun y ↦ delta k κ hΛ σ y (max M M₀))
            (fun _ _ ↦ Nat.zero_le _) h𝔫
      _ ≤ B := hB _ (le_max_right _ _)
  choose M' hM' using fun (𝔫 : T) ↦
    exists_dl_eq_dinf hΛ (isMaximal_of_mem_points hΛ (Finset.mem_filter.1 𝔫.2).1).ne_top
      (hbd 𝔫.1 𝔫.2)
  refine ⟨Finset.univ.sup M', fun M hM 𝔫 h𝔫 hP ↦ ?_⟩
  by_cases hp : 𝔫 ∈ points hΛ σ
  · have hT : 𝔫 ∈ T := Finset.mem_filter.2 ⟨hp, hP⟩
    exact hM' ⟨𝔫, hT⟩ M ((Finset.le_sup (f := M') (Finset.mem_univ _)).trans hM)
  · have hσ𝔫 : (⟨σ, hσ⟩ : Λ) ∉ 𝔫 := fun h ↦ hp (mem_points_of_mem hΛ hσ hσ0 h𝔫 h)
    have h0 (M : ℕ) := dl_eq_zero_of_conductor hΛ hσ hcond h𝔫.ne_top hσ𝔫 M
    rw [h0, dinf]
    simp [h0]

end ChartLocal

end SemistableReduction
