/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ExhaustGluing

/-!
# EdgeRepair (O10)

Blueprint §9.12, O10, in the form `S8A.EdgeRepairFor` of the S8.A agent (wp-tempered-s8a 7060859;
the definitions `IsDisc`, `EdgeGood`, `Brk`, `EdgeRepairFor` are copied verbatim). For a segment
`D ⊆ D'` of closed discs of `C`, the breaks are finite and every sub-edge containing no break is
good, **modulo** the named hypotheses (T⇒) `TubeOfExhausting`, (T⇐) `ExhaustingOfTube` (O11, O12),
R4(ii) `BelowGerm`, its dual `AboveGerm` and the type-3 germ `TypeThreeGerm`.

Under (T⇒) and (T⇐) an edge is good iff all radii of its open annulus are **clean**
(`Clean a ρ`: the skeleton Gauss point of radius `ρ` is a circle of a tube and the Gauss points
of the residue discs hanging off it are discs of tubes; `clean_of_edgeGood`, `edgeGood_of_clean`).
Cleanness is pointwise in the radius, so:

* a sub-edge without breaks is good: every radius strictly inside lies in a good edge
  (`edgeRepairFor`, second clause; radii which are not norms are vacuously clean);
* the germs give every radius a punctured neighbourhood of clean radii (`exists_clean_nhds`), so
  by compactness only finitely many radii of `[r(D), r(D')]` are not clean (`finite_not_clean`),
  and every break has a non-clean radius (norms are dense, `exists_norm_mem_Ioo`).
-/

open Metric
open scoped NNReal

namespace SemistableReduction

namespace EdgeRepair

open GaussTube GaussFibre AffineTwist PlaceNorm ExhaustGluing

universe u

section Density

variable {C : Type u} [NontriviallyNormedField C] [IsAlgClosed C]

/-- The norms of an algebraically closed nontrivially normed field are dense in `(0, ∞)`. -/
theorem exists_norm_mem_Ioo {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h : r₁ < r₂) :
    ∃ z : C, r₁ < ‖z‖ ∧ ‖z‖ < r₂ := by
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm C
  have hq : 1 < r₂ / r₁ := (one_lt_div h0).2 h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖x‖ hq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact absurd (hx.trans hn) (lt_irrefl 1)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x (Nat.pos_of_ne_zero hn0)
  have hyn : ‖y‖ ^ n = ‖x‖ := by rw [← norm_pow, hy]
  have hy1 : 1 < ‖y‖ := by
    by_contra! hle
    have := pow_le_one₀ (norm_nonneg y) hle (n := n)
    rw [hyn] at this
    exact absurd (hx.trans_le this) (lt_irrefl 1)
  have hyq : ‖y‖ < r₂ / r₁ := by
    by_contra! hle
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ r₂ / r₁) hle n
    rw [hyn] at this
    exact absurd (hn.trans_le this) (lt_irrefl _)
  obtain ⟨k, hk₁, hk₂⟩ := exists_mem_Ico_zpow h0 hy1
  have hy0 : y ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans hy1)
  refine ⟨y ^ (k + 1), ?_, ?_⟩
  · rw [norm_zpow]; exact hk₂
  · rw [norm_zpow, zpow_add_one₀ (norm_ne_zero_iff.2 hy0)]
    calc ‖y‖ ^ k * ‖y‖ ≤ r₁ * ‖y‖ := mul_le_mul_of_nonneg_right hk₁ (norm_nonneg _)
      _ < r₁ * (r₂ / r₁) := mul_lt_mul_of_pos_left hyq h0
      _ = r₂ := by field_simp

end Density

section Clean

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

variable (F') in
/-- The radius `ρ` is **clean** around `a`: the Gauss point `w_{a,ρ}` of the skeleton is a circle
of a tube, and every Gauss point `w_{a + β, |γ|}` (`|β| = ρ`, `|γ| < ρ`) of a residue disc hanging
off it is a disc of a tube. -/
def Clean (a : C) (ρ : ℝ) : Prop :=
  (∀ (γ : C) (hγ : γ ≠ 0), ‖γ‖ = ρ → IsTubeCircle F' a hγ) ∧
  ∀ (β γ : C) (hγ : γ ≠ 0), ‖β‖ = ρ → ‖γ‖ < ρ → IsTubeDisc F' (a + β) hγ

/-- The tube condition is cleanness of all radii of the open annulus. -/
theorem tubeCond_iff_clean {a c c' : C} (hc : c ≠ 0) :
    TubeCond F' a hc c' ↔ ∀ ρ : ℝ, ‖c * c'‖ < ρ → ρ < ‖c‖ → Clean F' a ρ := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  constructor
  · rintro ⟨h₁, h₂⟩ ρ hρ₁ hρ₂
    refine ⟨fun γ hγ hγρ ↦ ?_, fun β γ hγ hβ hγβ ↦ ?_⟩
    · have hγc : γ / c ≠ 0 := div_ne_zero hγ hc
      refine (isTubeCircle_congr _ _ rfl (by field_simp)).1 (h₁ (γ / c) hγc ?_ ?_)
      · rw [norm_div, lt_div_iff₀ hc', mul_comm, ← norm_mul, hγρ]; exact hρ₁
      · rw [norm_div, div_lt_one hc', hγρ]; exact hρ₂
    · have hγc : γ / c ≠ 0 := div_ne_zero hγ hc
      refine (isTubeDisc_congr _ _ (by field_simp) (by field_simp)).1
        (h₂ (β / c) (γ / c) hγc ?_ ?_ ?_)
      · rw [norm_div, lt_div_iff₀ hc', mul_comm, ← norm_mul, hβ]; exact hρ₁
      · rw [norm_div, div_lt_one hc', hβ]; exact hρ₂
      · rw [norm_div, norm_div, hβ]; exact div_lt_div_of_pos_right hγβ hc'
  · intro h
    refine ⟨fun γ hγ h1 h2 ↦ ?_, fun β γ hγ h1 h2 h3 ↦ ?_⟩
    · refine (h ‖c * γ‖ ?_ ?_).1 _ _ rfl
      · rw [norm_mul, norm_mul]; exact mul_lt_mul_of_pos_left h1 hc'
      · rw [norm_mul]; exact mul_lt_of_lt_one_right hc' h2
    · refine (h ‖c * β‖ ?_ ?_).2 _ _ _ rfl ?_
      · rw [norm_mul, norm_mul]; exact mul_lt_mul_of_pos_left h1 hc'
      · rw [norm_mul]; exact mul_lt_of_lt_one_right hc' h2
      · rw [norm_mul, norm_mul]; exact mul_lt_mul_of_pos_left h3 hc'


/-- Cleanness does not depend on the centre within the open disc of radius `ρ`. -/
theorem Clean.recenter {a b : C} {ρ : ℝ} (h : Clean F' a ρ) (hab : ‖a - b‖ < ρ) :
    Clean F' b ρ := by
  refine ⟨fun γ hγ hγρ ↦ ?_, fun β γ hγ hβ hγβ ↦ ?_⟩
  · unfold IsTubeCircle; intro b' hb'
    refine h.1 γ hγ hγρ b' ?_
    calc ‖a - b'‖ = ‖(a - b) + (b - b')‖ := by ring_nf
      _ ≤ max ‖a - b‖ ‖b - b'‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < ‖γ‖ := max_lt (hγρ ▸ hab) hb'
  · have hβ' : ‖(b - a) + β‖ = ρ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [norm_sub_rev, hβ]; exact hab.ne), hβ,
        max_eq_right (by rw [norm_sub_rev]; exact hab.le)]
    refine (isTubeDisc_congr _ _ (by ring) rfl).1 (h.2 ((b - a) + β) γ hγ hβ' (hβ' ▸ hγβ))

/-- A radius which is not a norm is clean (there are no Gauss points of that radius). -/
theorem clean_of_forall_ne {a : C} {ρ : ℝ} (h : ∀ z : C, ‖z‖ ≠ ρ) : Clean F' a ρ :=
  ⟨fun γ _ hγ ↦ absurd hγ (h γ), fun β _ _ hβ ↦ absurd hβ (h β)⟩

end Clean


section Discs

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

/-- A closed disc `closedBall a ‖c‖`, `c ≠ 0` (`S8A.IsDisc`, wp-tempered-s8a). -/
def IsDisc (D : Set C) : Prop := ∃ a c : C, c ≠ 0 ∧ D = closedBall a ‖c‖

/-- The radius of a closed disc of radius a norm is determined by the disc. -/
lemma norm_eq_of_closedBall_eq {a b c g : C}
    (h : closedBall b ‖c‖ = closedBall a ‖g‖) : ‖c‖ = ‖g‖ := by
  have hb : b ∈ closedBall a ‖g‖ := h ▸ mem_closedBall_self (norm_nonneg _)
  have ha : a ∈ closedBall b ‖c‖ := h ▸ mem_closedBall_self (norm_nonneg _)
  rw [mem_closedBall, dist_eq_norm] at ha hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hz : a + g ∈ closedBall a ‖g‖ := by simp [mem_closedBall, dist_eq_norm]
    rw [← h, mem_closedBall, dist_eq_norm] at hz
    have : ‖a + g - b‖ = ‖g‖ := by
      rw [show a + g - b = g + (a - b) by ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ha.trans_lt hlt).ne',
        max_eq_left (ha.trans hlt.le)]
    linarith
  · have hz : b + c ∈ closedBall b ‖c‖ := by simp [mem_closedBall, dist_eq_norm]
    rw [h, mem_closedBall, dist_eq_norm] at hz
    have : ‖b + c - a‖ = ‖c‖ := by
      rw [show b + c - a = c + (b - a) by ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (hb.trans_lt hlt).ne',
        max_eq_left (hb.trans hlt.le)]
    linarith

/-- A disc containing `a` is centred at `a`. -/
lemma IsDisc.eq_closedBall {G : Set C} (hG : IsDisc G) {a : C} (ha : a ∈ G) :
    ∃ g : C, g ≠ 0 ∧ G = closedBall a ‖g‖ := by
  obtain ⟨b, g, hg, rfl⟩ := hG
  exact ⟨g, hg, IsUltrametricDist.closedBall_eq_of_mem ha⟩

omit [IsUltrametricDist C] in
lemma closedBall_ssubset_iff {a g₁ g₂ : C} :
    closedBall a ‖g₁‖ ⊂ closedBall a ‖g₂‖ ↔ ‖g₁‖ < ‖g₂‖ := by
  constructor
  · rintro ⟨hsub, hne⟩
    by_contra! hle
    exact hne (closedBall_subset_closedBall hle)
  · intro hlt
    refine ⟨closedBall_subset_closedBall hlt.le, fun hsub ↦ ?_⟩
    have : a + g₂ ∈ closedBall a ‖g₁‖ := hsub (by simp [mem_closedBall, dist_eq_norm])
    simp [mem_closedBall, dist_eq_norm] at this
    linarith

omit [IsUltrametricDist C] in
lemma closedBall_subset_iff {a g₁ g₂ : C} :
    closedBall a ‖g₁‖ ⊆ closedBall a ‖g₂‖ ↔ ‖g₁‖ ≤ ‖g₂‖ := by
  constructor
  · intro hsub
    have : a + g₁ ∈ closedBall a ‖g₂‖ := hsub (by simp [mem_closedBall, dist_eq_norm])
    simpa [mem_closedBall, dist_eq_norm] using this
  · exact fun h ↦ closedBall_subset_closedBall h

omit [IsUltrametricDist C] in
lemma lt_radius_of_closedBall_ssubset {a : C} {r ρ : ℝ} (h : closedBall a r ⊂ closedBall a ρ) :
    r < ρ := by
  by_contra! hle
  exact h.2 (closedBall_subset_closedBall hle)

omit [IsUltrametricDist C] in
lemma radius_lt_of_closedBall_ssubset {a : C} {r ρ : ℝ} (h : closedBall a ρ ⊂ closedBall a r) :
    ρ < r := by
  by_contra! hle
  exact h.2 (closedBall_subset_closedBall hle)

end Discs

section Statement

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- The edge `E ⊊ G` is good: `E` is exhausting in the residue ball of `G` containing it, for
every representation (`S8A.EdgeGood`, wp-tempered-s8a). -/
def EdgeGood (E G : Set C) : Prop :=
  ∀ (a c c' : C) (hc : c ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0),
    E = closedBall a ‖c * c'‖ → G = closedBall a ‖c‖ → IsExhausting a hc hc' hc0' F

/-- The breaks of the segment `D ⊆ D'` (`S8A.Brk`, wp-tempered-s8a). -/
def Brk (D D' : Set C) : Set (Set C) :=
  {G | IsDisc G ∧ D ⊂ G ∧ G ⊂ D' ∧ ¬ ∃ G₁ G₂ : Set C, IsDisc G₁ ∧ IsDisc G₂ ∧ D ⊆ G₁ ∧
    G₁ ⊂ G ∧ G ⊂ G₂ ∧ G₂ ⊆ D' ∧ EdgeGood F G₁ G₂}

variable (C) in
/-- **EdgeRepair** (O10, `S8A.EdgeRepairFor`, wp-tempered-s8a 7060859). -/
def EdgeRepairFor : Prop :=
  ∀ D D' : Set C, IsDisc D → IsDisc D' → D ⊆ D' → (Brk F D D').Finite ∧
    ∀ G₁ G₂ : Set C, IsDisc G₁ → IsDisc G₂ → D ⊆ G₁ → G₁ ⊂ G₂ → G₂ ⊆ D' →
      (∀ G ∈ Brk F D D', ¬ (G₁ ⊂ G ∧ G ⊂ G₂)) → EdgeGood F G₁ G₂

variable (C) in
/-- **R4(ii)** (named hypothesis, the R4 agent): in the residue class `|x - a| < |c|`, all discs
`D(a, |c c'|)` of radius at least some `|c e| < |c|` are exhausting. -/
def BelowGerm : Prop :=
  ∀ (a c : C) (hc : c ≠ 0), ∃ e : C, e ≠ 0 ∧ ‖e‖ < 1 ∧
    ∀ (c' : C) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0), ‖e‖ ≤ ‖c'‖ → IsExhausting a hc hc' hc0' F

variable (C) in
/-- **Dual of R4(ii)** (named hypothesis): every disc `D(a, |c|)` is exhausting in the residue
class of `w_{a,|c₂|}` containing it, for all `|c| < |c₂| ≤ ρ₂`, some `ρ₂ > |c|`. -/
def AboveGerm : Prop :=
  ∀ (a c : C), c ≠ 0 → ∃ ρ₂ : ℝ, ‖c‖ < ρ₂ ∧ ∀ c₂ : C, ‖c‖ < ‖c₂‖ → ‖c₂‖ ≤ ρ₂ →
    EdgeGood F (closedBall a ‖c‖) (closedBall a ‖c₂‖)

variable (C) in
/-- **The type-3 germ** (named hypothesis, `S8A.TypeThreeGermFor`, the S8.B agent): around a radius
which is not a norm there is a good edge. -/
def TypeThreeGerm : Prop :=
  ∀ (a : C) (ρ : ℝ), 0 < ρ → (∀ z : C, ‖z‖ ≠ ρ) → ∃ c₁ : C, c₁ ≠ 0 ∧ ‖c₁‖ < ρ ∧
    ∃ ρ₂ : ℝ, ρ < ρ₂ ∧ ∀ c₂ : C, ρ < ‖c₂‖ → ‖c₂‖ ≤ ρ₂ →
      EdgeGood F (closedBall a ‖c₁‖) (closedBall a ‖c₂‖)

end Statement


section Repair

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- A good edge makes the radii of its open annulus clean (via (T⇒)). -/
theorem clean_of_edgeGood (hT : TubeOfExhausting C F) {a g₁ g₂ : C} (hg₁ : g₁ ≠ 0)
    (hg₂ : g₂ ≠ 0) (hlt : ‖g₁‖ < ‖g₂‖) (h : EdgeGood F (closedBall a ‖g₁‖) (closedBall a ‖g₂‖))
    {ρ : ℝ} (h₁ : ‖g₁‖ < ρ) (h₂ : ρ < ‖g₂‖) : Clean F a ρ := by
  have hg₂' : 0 < ‖g₂‖ := norm_pos_iff.2 hg₂
  have hc' : ‖g₁ / g₂‖ < 1 := by rw [norm_div, div_lt_one hg₂']; exact hlt
  have hcc : g₂ * (g₁ / g₂) = g₁ := by field_simp
  have hE := h a g₂ (g₁ / g₂) hg₂ hc' (div_ne_zero hg₁ hg₂) (by rw [hcc]) rfl
  exact (tubeCond_iff_clean hg₂).1 (hT _ _ _ _ _ _ hE) ρ (by rw [hcc]; exact h₁) h₂

/-- Clean radii make a good edge (via (T⇐)). -/
theorem edgeGood_of_clean (hT' : ExhaustingOfTube C F) {a g₁ g₂ : C}
    (h : ∀ ρ : ℝ, ‖g₁‖ < ρ → ρ < ‖g₂‖ → Clean F a ρ) :
    EdgeGood F (closedBall a ‖g₁‖) (closedBall a ‖g₂‖) := by
  intro b c c' hc hc' hc0' hE hG
  have h₁ : ‖c * c'‖ = ‖g₁‖ := norm_eq_of_closedBall_eq hE.symm
  have h₂ : ‖c‖ = ‖g₂‖ := norm_eq_of_closedBall_eq hG.symm
  have hb : ‖a - b‖ ≤ ‖g₁‖ := by
    have : b ∈ closedBall a ‖g₁‖ := hE ▸ mem_closedBall_self (norm_nonneg _)
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at this
    exact this
  refine hT' _ _ _ _ _ _ ((tubeCond_iff_clean hc).2 fun ρ hρ₁ hρ₂ ↦ ?_)
  rw [h₁] at hρ₁
  rw [h₂] at hρ₂
  exact (h ρ hρ₁ hρ₂).recenter (hb.trans_lt hρ₁)

/-- Every positive radius has a punctured neighbourhood of clean radii (from the germs). -/
theorem exists_clean_nhds (hT : TubeOfExhausting C F) (hB : BelowGerm C F) (hA : AboveGerm C F)
    (h3 : TypeThreeGerm C F) (a : C) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε > 0, ∀ ρ' : ℝ, |ρ' - ρ| < ε → ρ' ≠ ρ → Clean F a ρ' := by
  by_cases hz : ∃ z : C, ‖z‖ = ρ
  · obtain ⟨z, rfl⟩ := hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 hρ
    obtain ⟨e, he0, he1, hex⟩ := hB a z hz0
    have hlow : ∀ ρ', ‖z * e‖ < ρ' → ρ' < ‖z‖ → Clean F a ρ' := fun ρ' h1 h2 ↦
      (tubeCond_iff_clean hz0).1 (hT _ _ _ _ _ _ (hex e he1 he0 le_rfl)) ρ' h1 h2
    obtain ⟨ρ₂, hρ₂, hρ₂x⟩ := hA a z hz0
    obtain ⟨c₂, hc₂, hc₂'⟩ := exists_norm_mem_Ioo (C := C) hρ hρ₂
    have hc₂0 : c₂ ≠ 0 := norm_pos_iff.1 (hρ.trans hc₂)
    have hup : ∀ ρ', ‖z‖ < ρ' → ρ' < ‖c₂‖ → Clean F a ρ' := fun ρ' h1 h2 ↦
      clean_of_edgeGood hT hz0 hc₂0 hc₂ (hρ₂x c₂ hc₂ hc₂'.le) h1 h2
    have hze : ‖z * e‖ < ‖z‖ := by
      rw [norm_mul]; exact mul_lt_of_lt_one_right hρ he1
    refine ⟨min (‖z‖ - ‖z * e‖) (‖c₂‖ - ‖z‖), lt_min (by linarith) (by linarith),
      fun ρ' hρ' hne ↦ ?_⟩
    rw [abs_lt] at hρ'
    have m1 := min_le_left (‖z‖ - ‖z * e‖) (‖c₂‖ - ‖z‖)
    have m2 := min_le_right (‖z‖ - ‖z * e‖) (‖c₂‖ - ‖z‖)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hlow ρ' (by linarith) hlt
    · exact hup ρ' hlt (by linarith)
  · push Not at hz
    obtain ⟨c₁, hc₁0, hc₁, ρ₂, hρ₂, hρ₂x⟩ := h3 a ρ hρ hz
    obtain ⟨c₂, hc₂, hc₂'⟩ := exists_norm_mem_Ioo (C := C) hρ hρ₂
    have hc₂0 : c₂ ≠ 0 := norm_pos_iff.1 (hρ.trans hc₂)
    have hcl : ∀ ρ', ‖c₁‖ < ρ' → ρ' < ‖c₂‖ → Clean F a ρ' := fun ρ' h1 h2 ↦
      clean_of_edgeGood hT hc₁0 hc₂0 (hc₁.trans hc₂) (hρ₂x c₂ hc₂ hc₂'.le) h1 h2
    refine ⟨min (ρ - ‖c₁‖) (‖c₂‖ - ρ), lt_min (by linarith) (by linarith),
      fun ρ' hρ' _ ↦ ?_⟩
    rw [abs_lt] at hρ'
    have m1 := min_le_left (ρ - ‖c₁‖) (‖c₂‖ - ρ)
    have m2 := min_le_right (ρ - ‖c₁‖) (‖c₂‖ - ρ)
    exact hcl ρ' (by linarith) (by linarith)

/-- On a compact interval of positive radii only finitely many radii are not clean. -/
theorem finite_not_clean (hT : TubeOfExhausting C F) (hB : BelowGerm C F) (hA : AboveGerm C F)
    (h3 : TypeThreeGerm C F) (a : C) {r R : ℝ} (hr : 0 < r) :
    {ρ ∈ Set.Icc r R | ¬ Clean F a ρ}.Finite := by
  have hpos : ∀ ρ : Set.Icc r R, 0 < (ρ : ℝ) := fun ρ ↦ hr.trans_le ρ.2.1
  choose ε hε hεc using fun ρ : Set.Icc r R ↦ exists_clean_nhds hT hB hA h3 a (hpos ρ)
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun ρ : Set.Icc r R ↦ Set.Ioo ((ρ : ℝ) - ε ρ) (ρ + ε ρ)) (fun _ ↦ isOpen_Ioo)
    fun ρ hρ ↦ Set.mem_iUnion.2 ⟨⟨ρ, hρ⟩, by
      simp only [Set.mem_Ioo]; constructor <;> linarith [hε ⟨ρ, hρ⟩]⟩
  refine (t.finite_toSet.image (fun ρ : Set.Icc r R ↦ (ρ : ℝ))).subset fun u ⟨hu, hnc⟩ ↦ ?_
  obtain ⟨i, hi, hui⟩ := Set.mem_iUnion₂.1 (ht hu)
  refine ⟨i, hi, ?_⟩
  by_contra hne
  refine hnc (hεc i u ?_ (Ne.symm hne))
  rw [Set.mem_Ioo] at hui
  rw [abs_lt]
  constructor <;> linarith

/-- **O10: EdgeRepair** (modulo (T⇒), (T⇐), R4(ii), its dual and the type-3 germ). For a segment
`D ⊆ D'` of closed discs, the breaks are finite, and every sub-edge of the segment containing no
break is good. -/
theorem edgeRepairFor (hT : TubeOfExhausting C F) (hT' : ExhaustingOfTube C F)
    (hB : BelowGerm C F) (hA : AboveGerm C F) (h3 : TypeThreeGerm C F) : EdgeRepairFor C F := by
  intro D D' hD hD' hDD'
  obtain ⟨a, d, hd, rfl⟩ := hD
  have ha : a ∈ closedBall a ‖d‖ := mem_closedBall_self (norm_nonneg _)
  obtain ⟨d', hd', rfl⟩ := hD'.eq_closedBall (hDD' ha)
  have hd0 : 0 < ‖d‖ := norm_pos_iff.2 hd
  -- Clean radii between the radii of a good edge of the segment
  have hwit : ∀ (ρ : ℝ) (G₁ G₂ : Set C), IsDisc G₁ → IsDisc G₂ → closedBall a ‖d‖ ⊆ G₁ →
      G₁ ⊂ closedBall a ρ → closedBall a ρ ⊂ G₂ → EdgeGood F G₁ G₂ → Clean F a ρ := by
    intro ρ G₁ G₂ hG₁ hG₂ hDG₁ h₁ h₂ hgood
    obtain ⟨g₁, hg₁, rfl⟩ := hG₁.eq_closedBall (hDG₁ ha)
    obtain ⟨g₂, hg₂, rfl⟩ := hG₂.eq_closedBall (h₂.1 (h₁.1 (hDG₁ ha)))
    have hr₁ := lt_radius_of_closedBall_ssubset h₁
    have hr₂ := radius_lt_of_closedBall_ssubset h₂
    exact clean_of_edgeGood hT hg₁ hg₂ (hr₁.trans hr₂) hgood hr₁ hr₂
  refine ⟨?_, fun G₁ G₂ hG₁ hG₂ hDG₁ h12 hG₂D' hnb ↦ ?_⟩
  · -- finiteness of the breaks
    have hU := finite_not_clean hT hB hA h3 a (R := ‖d'‖) hd0
    refine (hU.image (fun ρ ↦ closedBall a ρ)).subset ?_
    rintro G ⟨hGd, hDG, hGD', hno⟩
    obtain ⟨g, hg, rfl⟩ := hGd.eq_closedBall (hDG.1 ha)
    have hdg : ‖d‖ < ‖g‖ := closedBall_ssubset_iff.1 hDG
    have hgd : ‖g‖ < ‖d'‖ := closedBall_ssubset_iff.1 hGD'
    refine ⟨‖g‖, ⟨⟨hdg.le, hgd.le⟩, fun hcl ↦ hno ?_⟩, rfl⟩
    have hgU : ‖g‖ ∉ {ρ ∈ Set.Icc ‖d‖ ‖d'‖ | ¬ Clean F a ρ} := fun h ↦ h.2 hcl
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU.isClosed.isOpen_compl ‖g‖ hgU
    obtain ⟨z₁, hz₁, hz₁'⟩ := exists_norm_mem_Ioo (C := C)
      (lt_max_of_lt_left hd0 : 0 < max ‖d‖ (‖g‖ - δ)) (max_lt hdg (by linarith))
    obtain ⟨z₂, hz₂, hz₂'⟩ := exists_norm_mem_Ioo (C := C) (hd0.trans hdg)
      (lt_min hgd (by linarith) : ‖g‖ < min ‖d'‖ (‖g‖ + δ))
    have hz₁0 : z₁ ≠ 0 := norm_pos_iff.1 ((lt_max_of_lt_left hd0).trans hz₁)
    have hz₂0 : z₂ ≠ 0 := norm_pos_iff.1 ((hd0.trans hdg).trans hz₂)
    have m1 := le_max_left ‖d‖ (‖g‖ - δ)
    have m2 := le_max_right ‖d‖ (‖g‖ - δ)
    have m3 := min_le_left ‖d'‖ (‖g‖ + δ)
    have m4 := min_le_right ‖d'‖ (‖g‖ + δ)
    refine ⟨closedBall a ‖z₁‖, closedBall a ‖z₂‖, ⟨a, z₁, hz₁0, rfl⟩, ⟨a, z₂, hz₂0, rfl⟩,
      closedBall_subset_iff.2 (by linarith), closedBall_ssubset_iff.2 hz₁',
      closedBall_ssubset_iff.2 hz₂, closedBall_subset_iff.2 (by linarith),
      edgeGood_of_clean hT' fun ρ h1 h2 ↦ ?_⟩
    by_contra hnc
    refine hball ?_ ⟨⟨by linarith, by linarith⟩, hnc⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  · -- sub-edges without breaks are good
    obtain ⟨g₁, hg₁, rfl⟩ := hG₁.eq_closedBall (hDG₁ ha)
    obtain ⟨g₂, hg₂, rfl⟩ := hG₂.eq_closedBall (h12.1 (hDG₁ ha))
    refine edgeGood_of_clean hT' fun ρ h1 h2 ↦ ?_
    by_cases hz : ∃ z : C, ‖z‖ = ρ
    · obtain ⟨z, rfl⟩ := hz
      have hz0 : z ≠ 0 := norm_pos_iff.1 ((norm_nonneg _).trans_lt h1)
      by_contra hnc
      refine hnb (closedBall a ‖z‖) ⟨⟨a, z, hz0, rfl⟩,
        hDG₁.trans_ssubset (closedBall_ssubset_iff.2 h1),
        (closedBall_ssubset_iff.2 h2).trans_subset hG₂D',
        fun ⟨G₁', G₂', hG₁', hG₂', hDG₁', h₁', h₂', _, hgood⟩ ↦
          hnc (hwit _ G₁' G₂' hG₁' hG₂' hDG₁' h₁' h₂' hgood)⟩
        ⟨closedBall_ssubset_iff.2 h1, closedBall_ssubset_iff.2 h2⟩
    · push Not at hz
      exact clean_of_forall_ne hz

end Repair

end EdgeRepair

end SemistableReduction
