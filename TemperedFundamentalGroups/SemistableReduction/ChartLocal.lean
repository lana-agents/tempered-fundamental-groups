/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DeltaCount
import TemperedFundamentalGroups.SemistableReduction.CurveGenerators

/-!
# Local–global principle for an affine chart of a reduced curve

Blueprint §9.9, S7⁺.7 (abstract part). Let `κ j` (`j ∈ J`, finite) be function fields of one
variable over an algebraically closed field `k`, `z ∈ Π_j κ j` with transcendental components, and
`Λ ⊆ Π_j κ j` a subring containing `k` and `z` whose elements are regular at every place
containing `z` (`IsChart`): the coordinate ring of an affine chart of a reduced curve with
normalization `Π_j κ j`, mapped into the function fields of its components.

* `center_isMaximal`, `exists_center_eq`: the closed points of the chart are the centres of the
  places of the components containing `z`;
* `locSpace k 𝔫`: the elements `a` with `s a ∈ Λ` for some `s ∈ Λ ∖ 𝔫` (the local ring at `𝔫`);
* **`mem_of_forall_mem_sup`** (local–global): if `σ ∈ Λ` is a conductor element
  (`σ · regRing ⊆ Λ`, nonzero on every component), then for `M ≫ 0` an element `v` regular at all
  places containing `z` lies in `Λ` as soon as it lies in `locSpace k 𝔫 + K_M` at the finitely many
  closed points `𝔫 ∋ σ` (`K_M`: order `≥ M` at the branches of `𝔫`).
-/

open WithZero Polynomial

namespace SemistableReduction

namespace ChartLocal

open DeltaCount CurvePlace

variable {k : Type*} [Field k] [IsAlgClosed k] {J : Type*} {κ : J → Type*}
  [∀ j, Field (κ j)] [∀ j, Algebra k (κ j)] [∀ j, IsCurveFunctionField k (κ j)]

variable (k κ) in
/-- The elements regular at every place containing `z` (the normalization of the chart). -/
def regRing (z : Π j, κ j) : Subring (Π j, κ j) where
  carrier := {v | ∀ j (Q : CurvePlace k (κ j)), z j ∈ Q.V → v j ∈ Q.V}
  mul_mem' ha hb j Q hQ := mul_mem (ha j Q hQ) (hb j Q hQ)
  one_mem' _ _ _ := one_mem _
  add_mem' ha hb j Q hQ := add_mem (ha j Q hQ) (hb j Q hQ)
  zero_mem' _ _ _ := zero_mem _
  neg_mem' ha j Q hQ := neg_mem (ha j Q hQ)

variable (k) in
/-- An affine chart: a subring containing `k` and `z`, inside the normalization `regRing z`. -/
structure IsChart (z : Π j, κ j) (Λ : Subring (Π j, κ j)) : Prop where
  const : ∀ c : k, (fun j ↦ algebraMap k (κ j) c) ∈ Λ
  mem : z ∈ Λ
  le : Λ ≤ regRing k κ z
  tr : ∀ j, Transcendental k (z j)

variable {z : Π j, κ j} {Λ : Subring (Π j, κ j)} (hΛ : IsChart k z Λ)
include hΛ

/-- The closed point cut out by a place `Q` of `κ j` containing `z j`. -/
def center {j : J} (Q : CurvePlace k (κ j)) (hQ : z j ∈ Q.V) : Ideal Λ where
  carrier := {a | Q.valuation (a.1 j) < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Subring.coe_add, Pi.add_apply] at ha hb ⊢
    exact (Valuation.map_add _ _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, Pi.mul_apply, map_mul] at ha ⊢
    exact (mul_le_of_le_one_left' (Q.valuation_le_one_iff.2 (hΛ.le c.2 j Q hQ))).trans_lt ha

lemma mem_center {j : J} {Q : CurvePlace k (κ j)} {hQ : z j ∈ Q.V} {a : Λ} :
    a ∈ center hΛ Q hQ ↔ Q.valuation (a.1 j) < 1 := Iff.rfl

/-- The centre of a place is a maximal ideal (the residue map onto `k`). -/
lemma center_isMaximal {j : J} (Q : CurvePlace k (κ j)) (hQ : z j ∈ Q.V) :
    (center hΛ Q hQ).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨by simp [mem_center], fun I x hle hx hxI ↦ ?_⟩
  have hxV : x.1 j ∈ Q.V := hΛ.le x.2 j Q hQ
  have hres : Q.res (x.1 j) ≠ 0 := fun h ↦ hx ((Q.res_eq_zero_iff hxV).1 h)
  set c := Q.res (x.1 j)
  set b : Λ := ⟨fun j ↦ algebraMap k (κ j) c⁻¹, hΛ.const c⁻¹⟩
  have hmem : x * b - 1 ∈ center hΛ Q hQ := by
    rw [mem_center]
    have h1 := Q.valuation_sub_res_lt_one hxV
    have : (x * b - 1 : Λ).1 j = (x.1 j - algebraMap k (κ j) c) * algebraMap k (κ j) c⁻¹ := by
      change x.1 j * algebraMap k (κ j) c⁻¹ - 1 = _
      rw [sub_mul, ← map_mul, mul_inv_cancel₀ hres, map_one]
    rw [this, map_mul, valuation_algebraMap_eq_one Q.valuation_algebraMap_le_one
      (inv_ne_zero hres), mul_one]
    exact h1
  have : (1 : Λ) = x * b - (x * b - 1) := by ring
  rw [this]
  exact sub_mem (I.mul_mem_right b hxI) (hle hmem)

omit [∀ j, IsCurveFunctionField k (κ j)] in
/-- The image of `Λ` in a component is not a field. -/
lemma not_isField_range (j : J) :
    ¬ IsField ((Pi.evalRingHom κ j).comp Λ.subtype).range := by
  intro hfield
  set φ := (Pi.evalRingHom κ j).comp Λ.subtype
  set y : φ.range := ⟨z j, ⟨⟨z, hΛ.mem⟩, rfl⟩⟩
  have hz0 : z j ≠ 0 := fun h ↦ hΛ.tr j (h ▸ isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun h ↦ hz0 (congrArg Subtype.val h)
  obtain ⟨u, hu⟩ := hfield.mul_inv_cancel hy0
  have hu' : (u : κ j) = (z j)⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hu)
  have hnr : (z j)⁻¹ ∉ (algebraMap k (κ j)).range := by
    rintro ⟨c, hc⟩
    exact hΛ.tr j (by
      have : z j = algebraMap k (κ j) c⁻¹ := by rw [map_inv₀, hc, inv_inv]
      rw [this]
      exact isAlgebraic_algebraMap _)
  obtain ⟨Q, hQ⟩ := CurvePlace.exists_not_mem hnr
  have hzQ : z j ∈ Q.V := (Q.V.mem_or_inv_mem _).resolve_right hQ
  obtain ⟨⟨a, ha⟩, hau⟩ := u.2
  have : (u : κ j) ∈ Q.V := by
    rw [← hau]
    exact hΛ.le ha j Q hzQ
  rw [hu'] at this
  exact hQ this

variable [Fintype J]

/-- **Every closed point is a centre**: a maximal ideal of `Λ` is the centre of a place of some
component. -/
lemma exists_center_eq (𝔫 : Ideal Λ) [h𝔫 : 𝔫.IsMaximal] :
    ∃ (j : J) (Q : CurvePlace k (κ j)) (hQ : z j ∈ Q.V), center hΛ Q hQ = 𝔫 := by
  classical
  -- a component whose kernel lies in `𝔫`
  obtain ⟨j, hj⟩ : ∃ j, RingHom.ker ((Pi.evalRingHom κ j).comp Λ.subtype) ≤ 𝔫 := by
    by_contra h
    push Not at h
    choose a ha ha𝔫 using fun j ↦ Set.not_subset.1 (h j)
    have hprod : ∏ j, a j ∈ 𝔫 := by
      have : ∏ j, a j = 0 := by
        apply Subtype.ext
        funext i
        change (Λ.subtype (∏ j, a j)) i = 0
        rw [map_prod, Finset.prod_apply]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (RingHom.mem_ker.1 (ha i))
      rw [this]
      exact zero_mem _
    haveI := h𝔫.isPrime
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (p := 𝔫)).1 hprod
    exact ha𝔫 i hi
  set φ := (Pi.evalRingHom κ j).comp Λ.subtype
  set A := φ.range
  set ψ := φ.rangeRestrict
  have hψ : Function.Surjective ψ := RingHom.rangeRestrict_surjective _
  have hkerψ : RingHom.ker ψ ≤ 𝔫 := by rwa [RingHom.ker_rangeRestrict]
  have hmax : (𝔫.map ψ).IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hψ hkerψ
  obtain ⟨V, hAV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring (𝔫.map ψ) hmax.ne_top
  have hmemA (a : Λ) : a.1 j ∈ A := ⟨a, rfl⟩
  have hVne : V ≠ ⊤ := by
    rintro rfl
    apply not_isField_range hΛ j
    rw [Ring.isField_iff_maximal_bot]
    convert hmax
    symm
    rw [eq_bot_iff]
    intro y hy
    have : ((y : A) : κ j) ∈ (⊤ : ValuationSubring (κ j)).nonunits := hV ⟨y, hy, rfl⟩
    rw [ValuationSubring.mem_nonunits_iff] at this
    rw [Ideal.mem_bot]
    by_contra hy0
    have hy0' : ((y : A) : κ j) ≠ 0 := fun h ↦ hy0 (Subtype.ext h)
    have h1 : (⊤ : ValuationSubring (κ j)).valuation (y : A) = 1 := by
      refine le_antisymm ((ValuationSubring.valuation_le_one_iff _ _).2 trivial) ?_
      have h2 := (ValuationSubring.valuation_le_one_iff _ _).2
        (show ((y : A) : κ j)⁻¹ ∈ (⊤ : ValuationSubring (κ j)) from trivial)
      rw [map_inv₀] at h2
      exact (inv_le_one₀ ((Valuation.pos_iff _).2 hy0')).1 h2
    rw [h1] at this
    exact lt_irrefl _ this
  set Q : CurvePlace k (κ j) :=
    ⟨V, fun c ↦ hAV (hmemA ⟨_, hΛ.const c⟩), hVne⟩
  have hdom (a : Λ) : a.1 j ∈ Q.V := hAV (hmemA a)
  have hzQ : z j ∈ Q.V := hdom ⟨z, hΛ.mem⟩
  have hback (a : Λ) (h : a ∈ 𝔫) : Q.valuation (a.1 j) < 1 := by
    rw [CurvePlace.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff]
    exact hV ⟨ψ a, Ideal.mem_map_of_mem ψ h, rfl⟩
  refine ⟨j, Q, hzQ, ?_⟩
  have hle : 𝔫 ≤ center hΛ Q hzQ := fun a ha ↦ hback a ha
  exact ((h𝔫.eq_of_le (center_isMaximal hΛ Q hzQ).ne_top hle)).symm

/-- The elements `a` with `s a ∈ Λ` for some `s ∈ Λ ∖ 𝔫`. -/
def locSet (𝔫 : Ideal Λ) : Set (Π j, κ j) := {a | ∃ s : Λ, s ∉ 𝔫 ∧ s.1 * a ∈ Λ}

variable (k) in
/-- The local ring of the chart at `𝔫`, as a subspace of `Π_j κ j`. -/
def locSpace (𝔫 : Ideal Λ) : Submodule k (Π j, κ j) := Submodule.span k (locSet 𝔫)

omit [IsAlgClosed k] [∀ j, IsCurveFunctionField k (κ j)] [Fintype J] in
lemma mem_locSet_of_mem_locSpace {𝔫 : Ideal Λ} [h𝔫 : 𝔫.IsPrime] {a : Π j, κ j}
    (ha : a ∈ locSpace k 𝔫) : a ∈ locSet 𝔫 := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨1, fun h ↦ h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one),
      by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, fun h ↦ (h𝔫.mem_or_mem h).elim hs ht, ?_⟩
    have : (s * t).1 * (x + y) = t.1 * (s.1 * x) + s.1 * (t.1 * y) := by
      simp only [Subring.coe_mul]; ring
    rw [this]
    exact add_mem (mul_mem t.2 hsx) (mul_mem s.2 hty)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    refine ⟨s, hs, ?_⟩
    have : s.1 * (c • x) = (fun j ↦ algebraMap k (κ j) c) * (s.1 * x) := by
      funext j
      change s.1 j * (c • x j) = algebraMap k (κ j) c * (s.1 j * x j)
      rw [Algebra.smul_def]
      ring
    rw [this]
    exact mul_mem (hΛ.const c) hsx

omit [IsAlgClosed k] [∀ j, IsCurveFunctionField k (κ j)] hΛ [Fintype J] in
lemma subset_locSpace (𝔫 : Ideal Λ) : locSet 𝔫 ⊆ locSpace k 𝔫 := Submodule.subset_span

omit hΛ [Fintype J] in
/-- Multiplication by regular elements preserves high order at branches containing `z`. -/
lemma mul_mem_jetKer {a u : Π j, κ j} (ha : a ∈ regRing k κ z) {M : ℕ}
    {S : Finset (Branch k κ)} (hS : ∀ b ∈ S, z b.1 ∈ b.2.V) (hu : u ∈ jetKer k κ M S) :
    a * u ∈ jetKer k κ M S := fun b hb ↦ by
  rw [Pi.mul_apply, map_mul]
  exact (mul_le_of_le_one_left' (b.2.valuation_le_one_iff.2 (ha b.1 b.2 (hS b hb)))).trans
    (hu b hb)


omit hΛ in
variable (k κ) in
/-- The branches `(j, Q)` at which `σ j` has a zero. -/
noncomputable def zeros (σ : Π j, κ j) : Finset (Branch k κ) :=
  Finset.univ.sigma fun j ↦ (finite_setOf_notMem (k := k) (σ j)⁻¹).toFinset

omit hΛ in
lemma mem_zeros {σ : Π j, κ j} {b : Branch k κ} : b ∈ zeros k κ σ ↔ (σ b.1)⁻¹ ∉ b.2.V := by
  simp [zeros]

open Classical in
/-- The closed point of a branch (`⊤` if the place does not contain `z`). -/
noncomputable def centerOf (b : Branch k κ) : Ideal Λ :=
  if h : z b.1 ∈ b.2.V then center hΛ b.2 h else ⊤

open Classical in
/-- The closed points containing `σ`. -/
noncomputable def points (σ : Π j, κ j) : Finset (Ideal Λ) :=
  ((zeros k κ σ).image (centerOf hΛ)).filter (· ≠ ⊤)

open Classical in
/-- The branches of the closed point `𝔫` among the zeros of `σ`. -/
noncomputable def branches (σ : Π j, κ j) (𝔫 : Ideal Λ) : Finset (Branch k κ) :=
  (zeros k κ σ).filter fun b ↦ centerOf hΛ b = 𝔫

omit [Fintype J] in
lemma centerOf_isMaximal {b : Branch k κ} (hb : centerOf hΛ b ≠ ⊤) :
    (centerOf hΛ b).IsMaximal := by
  unfold centerOf at hb ⊢
  split_ifs with h
  · exact center_isMaximal hΛ _ h
  · rw [dif_neg h] at hb
    exact absurd rfl hb

omit [Fintype J] in
lemma mem_V_of_centerOf_ne_top {b : Branch k κ} (hb : centerOf hΛ b ≠ ⊤) : z b.1 ∈ b.2.V := by
  by_contra h
  unfold centerOf at hb
  rw [dif_neg h] at hb
  exact hb rfl

lemma mem_V_of_mem_branches {σ : Π j, κ j} {𝔫 : Ideal Λ} (h𝔫 : 𝔫 ≠ ⊤) {b : Branch k κ}
    (hb : b ∈ branches hΛ σ 𝔫) : z b.1 ∈ b.2.V := by
  classical
  refine mem_V_of_centerOf_ne_top hΛ ?_
  rw [(Finset.mem_filter.1 hb).2]
  exact h𝔫

lemma isMaximal_of_mem_points {σ : Π j, κ j} {𝔫 : Ideal Λ} (h : 𝔫 ∈ points hΛ σ) :
    𝔫.IsMaximal := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 h1
  exact centerOf_isMaximal hΛ h2

omit [Fintype J] in
/-- Elements of `center Q` have order `≥ 1` at `Q`, so elements of its `N`-th power have
order `≥ N`. -/
lemma valuation_le_of_mem_pow {j : J} {Q : CurvePlace k (κ j)} (hQ : z j ∈ Q.V) (N : ℕ)
    {a : Λ} (ha : a ∈ center hΛ Q hQ ^ N) : Q.valuation (a.1 j) ≤ exp (-(N : ℤ)) := by
  let I : ℕ → Ideal Λ := fun n ↦
    { carrier := {a | Q.valuation (a.1 j) ≤ exp (-(n : ℤ))}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, Subring.coe_add, Pi.add_apply] at ha hb ⊢
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha ↦ by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, Pi.mul_apply,
          map_mul] at ha ⊢
        exact (mul_le_of_le_one_left' (Q.valuation_le_one_iff.2 (hΛ.le c.2 j Q hQ))).trans ha }
  suffices h : ∀ n, center hΛ Q hQ ^ n ≤ I n from h N ha
  intro n
  induction n with
  | zero =>
    intro a _
    change Q.valuation (a.1 j) ≤ exp (-((0 : ℕ) : ℤ))
    simpa using Q.valuation_le_one_iff.2 (hΛ.le a.2 j Q hQ)
  | succ n ih =>
    rw [pow_succ]
    refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
    have h1 : Q.valuation (a.1 j) ≤ exp (-(n : ℤ)) := ih ha
    have h2 : Q.valuation (b.1 j) ≤ exp (-1) :=
      WithZero.le_exp_of_lt_exp_add_one (by simpa using (mem_center hΛ).1 hb)
    change Q.valuation ((a * b).1 j) ≤ exp (-((n + 1 : ℕ) : ℤ))
    rw [Subring.coe_mul, Pi.mul_apply, map_mul]
    calc Q.valuation (a.1 j) * Q.valuation (b.1 j) ≤ exp (-(n : ℤ)) * exp (-1) := by
          gcongr
      _ = _ := by rw [← exp_add]; push_cast; ring_nf

/-- **The local–global principle** with a conductor element `σ`. -/
theorem mem_of_forall_mem_sup {σ : Π j, κ j} (hσ : σ ∈ Λ) (hσ0 : ∀ j, σ j ≠ 0)
    (hcond : ∀ v ∈ regRing k κ z, σ * v ∈ Λ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ v ∈ regRing k κ z,
      (∀ 𝔫 ∈ points hΛ σ, v ∈ locSpace k 𝔫 ⊔ jetKer k κ M (branches hΛ σ 𝔫)) → v ∈ Λ := by
  classical
  set N := Finset.univ.sup fun j ↦ poleNorm k (σ j)⁻¹
  -- `σ` has order `≤ N` everywhere
  have hσN (j : J) (Q : CurvePlace k (κ j)) : exp (-(N : ℤ)) ≤ Q.valuation (σ j) := by
    have h1 := (Q.valuation_le_exp_poleOrder (σ j)⁻¹).trans (exp_le_exp.2
      (show (Q.poleOrder (σ j)⁻¹ : ℤ) ≤ N by
        exact_mod_cast (poleOrder_le_poleNorm Q _).trans
          (Finset.le_sup (f := fun j ↦ poleNorm k (σ j)⁻¹) (Finset.mem_univ j))))
    rw [map_inv₀] at h1
    have hpos : 0 < Q.valuation (σ j) := (Valuation.pos_iff _).2 (hσ0 j)
    have := (inv_le_comm₀ hpos exp_pos).1 h1
    rwa [← exp_neg] at this
  refine ⟨N, fun M hM v hv hloc ↦ ?_⟩
  have hσreg : σ ∈ regRing k κ z := hΛ.le hσ
  -- step 1: high-order elements are local at the points of `σ`
  have hjet (𝔫 : Ideal Λ) (h𝔫p : 𝔫 ∈ points hΛ σ) (u : Π j, κ j) (hu : u ∈ regRing k κ z)
      (huj : u ∈ jetKer k κ M (branches hΛ σ 𝔫)) : u ∈ locSet 𝔫 := by
    have h𝔫 := isMaximal_of_mem_points hΛ h𝔫p
    set Z' := (zeros k κ σ).filter fun b ↦ centerOf hΛ b ≠ 𝔫 ∧ centerOf hΛ b ≠ ⊤
    set I := ∏ b ∈ Z', centerOf hΛ b ^ N
    have hcop : IsCoprime I 𝔫 := by
      refine IsCoprime.prod_left fun b hb ↦ IsCoprime.pow_left ?_
      obtain ⟨-, hne, htop⟩ := Finset.mem_filter.1 hb
      have hmax := centerOf_isMaximal hΛ htop
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hsup
      have hle : centerOf hΛ b ≤ centerOf hΛ b ⊔ 𝔫 := le_sup_left
      rcases hmax.eq_of_le hsup hle with h
      · exact hne (h𝔫.eq_of_le (centerOf_isMaximal hΛ htop).ne_top
          (h ▸ le_sup_right) |>.symm)
    obtain ⟨s, hsI, t, ht, hst⟩ := Ideal.isCoprime_iff_exists.1 hcop
    have hs𝔫 : s ∉ 𝔫 := fun h ↦ h𝔫.ne_top ((Ideal.eq_top_iff_one _).2 (hst ▸ add_mem h ht))
    have hsZ (b : Branch k κ) (hb : b ∈ Z') : b.2.valuation (s.1 b.1) ≤ exp (-(N : ℤ)) := by
      obtain ⟨-, -, htop⟩ := Finset.mem_filter.1 hb
      have hzb := mem_V_of_centerOf_ne_top hΛ htop
      have hmem : s ∈ centerOf hΛ b ^ N :=
        (Ideal.prod_le_inf.trans (Finset.inf_le hb)) hsI
      unfold centerOf at hmem
      rw [dif_pos hzb] at hmem
      exact valuation_le_of_mem_pow hΛ hzb N hmem
    set v' : Π j, κ j := fun j ↦ s.1 j * u j * (σ j)⁻¹
    have hv' : v' ∈ regRing k κ z := by
      intro j Q hQ
      rw [← Q.valuation_le_one_iff]
      simp only [v', map_mul, map_inv₀]
      have hs1 : Q.valuation (s.1 j) ≤ 1 := Q.valuation_le_one_iff.2 (hΛ.le s.2 j Q hQ)
      have hu1 : Q.valuation (u j) ≤ 1 := Q.valuation_le_one_iff.2 (hu j Q hQ)
      have hσ1 : Q.valuation (σ j) ≤ 1 := Q.valuation_le_one_iff.2 (hσreg j Q hQ)
      have hpos : 0 < Q.valuation (σ j) := (Valuation.pos_iff _).2 (hσ0 j)
      rw [mul_inv_le_iff₀ hpos, one_mul]
      rcases hσ1.lt_or_eq with hlt | heq
      · have hb : (⟨j, Q⟩ : Branch k κ) ∈ zeros k κ σ := by
          rw [mem_zeros]
          intro h
          have := Q.valuation_le_one_iff.2 h
          rw [map_inv₀] at this
          exact absurd ((inv_le_one₀ hpos).1 this) (not_le.2 hlt)
        by_cases hc : centerOf hΛ ⟨j, Q⟩ = 𝔫
        · have hbr : (⟨j, Q⟩ : Branch k κ) ∈ branches hΛ σ 𝔫 := Finset.mem_filter.2 ⟨hb, hc⟩
          have := huj _ hbr
          calc Q.valuation (s.1 j) * Q.valuation (u j) ≤ 1 * exp (-(M : ℤ)) := by
                gcongr
            _ ≤ exp (-(N : ℤ)) := by
                rw [one_mul, exp_le_exp]
                omega
            _ ≤ Q.valuation (σ j) := hσN j Q
        · have hcne : centerOf hΛ ⟨j, Q⟩ ≠ ⊤ := by
            unfold centerOf
            rw [dif_pos hQ]
            exact (center_isMaximal hΛ Q hQ).ne_top
          have := hsZ _ (Finset.mem_filter.2 ⟨hb, hc, hcne⟩)
          calc Q.valuation (s.1 j) * Q.valuation (u j) ≤ exp (-(N : ℤ)) * 1 := by
                gcongr
            _ ≤ Q.valuation (σ j) := by rw [mul_one]; exact hσN j Q
      · rw [heq]
        exact mul_le_one' hs1 hu1
    refine ⟨s, hs𝔫, ?_⟩
    have : s.1 * u = σ * v' := by
      funext j
      simp only [Pi.mul_apply, v']
      field_simp [hσ0 j]
    rw [this]
    exact hcond v' hv'
  -- step 2: local at the points of `σ`
  have hloc' (𝔫 : Ideal Λ) (h𝔫p : 𝔫 ∈ points hΛ σ) : v ∈ locSet 𝔫 := by
    haveI h𝔫 := isMaximal_of_mem_points hΛ h𝔫p
    obtain ⟨o, ho, kk, hk, rfl⟩ := Submodule.mem_sup.1 (hloc 𝔫 h𝔫p)
    obtain ⟨s, hs, hso⟩ := mem_locSet_of_mem_locSpace hΛ ho
    have hsk : s.1 * kk ∈ regRing k κ z := by
      have : s.1 * kk = s.1 * (o + kk) - s.1 * o := by ring
      rw [this]
      exact sub_mem (mul_mem (hΛ.le s.2) hv) (hΛ.le hso)
    have hskj : s.1 * kk ∈ jetKer k κ M (branches hΛ σ 𝔫) :=
      mul_mem_jetKer (hΛ.le s.2) (fun b hb ↦ mem_V_of_mem_branches hΛ h𝔫.ne_top hb) hk
    obtain ⟨s', hs', hs'k⟩ := hjet 𝔫 h𝔫p _ hsk hskj
    refine ⟨s' * s, fun h ↦ (h𝔫.isPrime.mem_or_mem h).elim hs' hs, ?_⟩
    have : (s' * s).1 * (o + kk) = s'.1 * (s.1 * o) + s'.1 * (s.1 * kk) := by
      simp only [Subring.coe_mul]; ring
    rw [this]
    exact add_mem (mul_mem s'.2 hso) hs'k
  -- step 3: the ideal of denominators
  let Iv : Ideal Λ :=
    { carrier := {s | s.1 * v ∈ Λ}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, Subring.coe_add, add_mul] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c a ha ↦ by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at ha ⊢
        exact mul_mem c.2 ha }
  have hσIv : (⟨σ, hσ⟩ : Λ) ∈ Iv := hcond v hv
  by_cases htop : Iv = ⊤
  · have h1 : (1 : Λ) ∈ Iv := htop ▸ Submodule.mem_top
    have h2 : (1 : Λ).1 * v ∈ Λ := h1
    simpa using h2
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal Iv htop
  obtain ⟨j, Q, hQ, hc⟩ := exists_center_eq hΛ 𝔪
  have hσ𝔪 : (⟨σ, hσ⟩ : Λ) ∈ 𝔪 := hle hσIv
  have h𝔪p : 𝔪 ∈ points hΛ σ := by
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨⟨j, Q⟩, ?_, ?_⟩, h𝔪.ne_top⟩
    · rw [mem_zeros]
      intro h
      have h1 := Q.valuation_le_one_iff.2 h
      rw [← hc, mem_center] at hσ𝔪
      rw [map_inv₀] at h1
      exact absurd ((inv_le_one₀ ((Valuation.pos_iff _).2 (hσ0 j))).1 h1) (not_le.2 hσ𝔪)
    · unfold centerOf
      rw [dif_pos hQ]
      exact hc
  obtain ⟨s, hs, hsv⟩ := hloc' 𝔪 h𝔪p
  exact absurd (hle hsv) hs

end ChartLocal

end SemistableReduction
