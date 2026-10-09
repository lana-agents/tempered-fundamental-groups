/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CurvePlace

/-!
# Frobenius-closed bases of function fields in characteristic `p`

Blueprint §9.4, E2 (Temkin, *Stable modification of relative curves*, Lemma `basislem`;
Kuhlmann [K5, Thm 10] and *Elimination of ramification I*, Lemma 4.8). Let `k` be a perfect
field of characteristic `p` and `κ / k` a field extension. A `FrobeniusBasis k κ p` consists of
a family `u : ι → κ` such that

* `{1} ⊔ {u_q ^ (p ^ i)}_{i ∈ ℕ, q ∈ ι}` is a `k`-basis of `κ` (`FrobeniusBasis.basis`),
* `Span_k u ∩ κ^p = 0` (`FrobeniusBasis.eq_zero_of_eq_pow`),
* `Span_k u ∩ ℘(κ) = 0`, where `℘(g) = g ^ p - g` (`FrobeniusBasis.eq_zero_of_eq_pow_sub`),

and consequently `Span_k u ∩ (κ^p + k) = 0` (`FrobeniusBasis.eq_zero_of_eq_pow_add_algebraMap`).

Existence (`IsFrobeniusNorm.nonempty_frobeniusBasis`) is proved for any `κ` carrying a
"Frobenius-compatible norm" `‖·‖ : κ → ℕ` (`IsFrobeniusNorm`: `‖f + g‖ ≤ max ‖f‖ ‖g‖`,
`‖c • f‖ ≤ ‖f‖`, `‖f ^ p‖ = p ‖f‖`, `‖f‖ = 0 → f ∈ k`); for a function field of one variable
over an algebraically closed field the pole norm of `SemistableReduction.CurvePlace` is one
(`isFrobeniusNorm_poleNorm`, `nonempty_frobeniusBasis`).

## Proof (Temkin)

Let `L_n = {‖f‖ ≤ n}` and `π : κ → κ / κ^p`. Choose linearly independent sets `T_0 ⊆ T_1 ⊆ …`
in `κ / κ^p` with `T_n ⊆ π(L_n) ⊆ Span T_n`, and lift each element of `T = ⋃ T_n` to `L_n` for
the first `n` with `q ∈ T_n`. Then every `f` decomposes as `f = f₀ + g^p` with `f₀ ∈ Span u`,
`‖f₀‖ ≤ ‖f‖`, hence `p ‖g‖ ≤ ‖f‖`; by induction on `‖f‖` the family spans `κ`. Linear
independence follows level by level: the Frobenius maps independent families to independent
families (`k` perfect), their span lies in `κ^p`, and `u` is independent modulo `κ^p`. For
`f = g^p - g` in `Span u` with `f ≠ 0`, `g` is non-constant, and decomposing `g = g₀ + h^p` gives
`f = -g₀`, so `p ‖g‖ = ‖f + g‖ ≤ ‖g‖`, a contradiction.
-/

open Submodule Set

namespace SemistableReduction

universe u v

variable (k : Type u) (κ : Type v) [Field k] [Field κ] [Algebra k κ] (p : ℕ)

/-- A Frobenius-compatible norm on `κ / k`: a function `‖·‖ : κ → ℕ` with
`‖f + g‖ ≤ max ‖f‖ ‖g‖`, `‖c • f‖ ≤ ‖f‖` (`c ∈ k`), `‖f ^ p‖ = p ‖f‖`, vanishing only on `k`. -/
structure IsFrobeniusNorm (N : κ → ℕ) : Prop where
  add_le (f g : κ) : N (f + g) ≤ max (N f) (N g)
  smul_le (c : k) (f : κ) : N (c • f) ≤ N f
  pow_char (f : κ) : N (f ^ p) = p * N f
  mem_range_of_eq_zero (f : κ) : N f = 0 → f ∈ (algebraMap k κ).range

/-- A Frobenius-closed basis of `κ / k` (Temkin's Lemma `basislem`, Kuhlmann's [K5, Thm 10]):
a family `u : ι → κ` such that `1` and the `u_q ^ (p ^ i)` form a `k`-basis of `κ`, and whose
span meets neither `κ^p` nor `℘(κ) = {g ^ p - g}` nontrivially. -/
structure FrobeniusBasis where
  /-- The index type of the family `u`. -/
  ι : Type v
  /-- The family `u`. -/
  u : ι → κ
  /-- The basis `{1} ⊔ {u_q ^ (p ^ i)}`. -/
  basis : Module.Basis (Option (ℕ × ι)) k κ
  basis_none : basis none = 1
  basis_some (i : ℕ) (q : ι) : basis (some (i, q)) = u q ^ p ^ i
  eq_zero_of_eq_pow : ∀ f ∈ span k (range u), ∀ g : κ, f = g ^ p → f = 0
  eq_zero_of_eq_pow_sub : ∀ f ∈ span k (range u), ∀ g : κ, f = g ^ p - g → f = 0

variable {k κ p}

section Frobenius

variable [Fact p.Prime] [CharP k p] [PerfectRing k p]

lemma pow_frobeniusEquiv_symm (c : k) : (frobeniusEquiv k p).symm c ^ p = c := by
  have := (frobeniusEquiv k p).apply_symm_apply c
  rwa [frobeniusEquiv_apply, frobenius_def] at this

variable [CharP κ p]

variable (k κ p) in
/-- The `k`-subspace `κ^p` of `p`-th powers (a subspace since `k` is perfect). -/
def pthPowers : Submodule k κ where
  carrier := {f | ∃ g : κ, g ^ p = f}
  zero_mem' := ⟨0, zero_pow (Fact.out : p.Prime).ne_zero⟩
  add_mem' := by
    rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g + h, by rw [add_pow_char]⟩
  smul_mem' := by
    rintro c _ ⟨g, rfl⟩
    exact ⟨(frobeniusEquiv k p).symm c • g, by rw [smul_pow, pow_frobeniusEquiv_symm]⟩

lemma mem_pthPowers {f : κ} : f ∈ pthPowers k κ p ↔ ∃ g : κ, g ^ p = f := Iff.rfl

lemma pow_mem_pthPowers (g : κ) : g ^ p ∈ pthPowers k κ p := ⟨g, rfl⟩

lemma algebraMap_mem_pthPowers (c : k) : algebraMap k κ c ∈ pthPowers k κ p :=
  ⟨algebraMap k κ ((frobeniusEquiv k p).symm c), by rw [← map_pow, pow_frobeniusEquiv_symm]⟩

/-- The Frobenius maps `k`-linearly independent families to linearly independent families. -/
lemma LinearIndependent.pow_char {ι : Type*} {w : ι → κ} (hw : LinearIndependent k w) :
    LinearIndependent k (fun i ↦ w i ^ p) := by
  rw [linearIndependent_iff'] at hw ⊢
  intro s g hg i hi
  have h := hw s (fun i ↦ (frobeniusEquiv k p).symm (g i)) ?_ i hi
  · simpa using congrArg (frobeniusEquiv k p) h
  · refine (frobenius_inj κ p) ?_
    simp only [frobenius_def, zero_pow (Fact.out : p.Prime).ne_zero, sum_pow_char, smul_pow,
      pow_frobeniusEquiv_symm]
    exact hg

end Frobenius

namespace FrobeniusBasis

variable [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP κ p] (B : FrobeniusBasis k κ p)

/-- `Span_k u ∩ (κ^p + k) = 0` (Kuhlmann, Lemma 4.8): `κ^p + k = κ^p` as `k` is perfect. -/
lemma eq_zero_of_eq_pow_add_algebraMap {f : κ} (hf : f ∈ span k (range B.u)) (g : κ) (c : k)
    (h : f = g ^ p + algebraMap k κ c) : f = 0 :=
  B.eq_zero_of_eq_pow f hf (g + algebraMap k κ ((frobeniusEquiv k p).symm c)) (by
    rw [h, add_pow_char, ← map_pow, pow_frobeniusEquiv_symm])

omit [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP κ p] in
lemma linearIndependent_u : LinearIndependent k B.u := by
  have := B.basis.linearIndependent.comp (fun q ↦ some (0, q)) (fun _ _ h ↦ by simpa using h)
  convert this using 1
  ext q
  simp [B.basis_some]

/-- The elements `u_q` are not `p`-th powers. -/
lemma u_notMem_pthPowers (q : B.ι) : B.u q ∉ pthPowers k κ p := by
  rintro ⟨g, hg⟩
  exact B.linearIndependent_u.ne_zero q
    (B.eq_zero_of_eq_pow _ (subset_span ⟨q, rfl⟩) g hg.symm)

end FrobeniusBasis

namespace IsFrobeniusNorm

variable {N : κ → ℕ} (hN : IsFrobeniusNorm k κ p N)
include hN

lemma map_neg (f : κ) : N (-f) = N f :=
  le_antisymm (by simpa using hN.smul_le (-1) f) (by simpa using hN.smul_le (-1) (-f))

variable [Fact p.Prime]

lemma map_zero : N 0 = 0 := by
  have h := hN.pow_char 0
  rw [zero_pow (Fact.out : p.Prime).ne_zero] at h
  have := (Fact.out : p.Prime).two_le
  nlinarith

/-- The `k`-subspace `{‖f‖ ≤ n}`. -/
def ball (n : ℕ) : Submodule k κ where
  carrier := {f | N f ≤ n}
  zero_mem' := by simp [hN.map_zero]
  add_mem' ha hb := (hN.add_le _ _).trans (max_le ha hb)
  smul_mem' c f hf := (hN.smul_le c f).trans hf

lemma mem_ball {n : ℕ} {f : κ} : f ∈ hN.ball n ↔ N f ≤ n := Iff.rfl

variable [CharP k p] [PerfectRing k p] [CharP κ p]

/-- Adapted linearly independent sets in `κ / κ^p`: `T 0 ⊆ T 1 ⊆ …`, with `T n` spanning the
image of `{‖f‖ ≤ n}`. -/
noncomputable def adaptedSet : ℕ → {s : Set (κ ⧸ pthPowers k κ p) // LinearIndepOn k id s}
  | 0 => ⟨(linearIndepOn_empty k id).extend
      (empty_subset ((pthPowers k κ p).mkQ '' (hN.ball 0))),
      (linearIndepOn_empty k id).linearIndepOn_extend (empty_subset _)⟩
  | n + 1 => ⟨(adaptedSet n).2.extend
      (subset_union_left (t := (pthPowers k κ p).mkQ '' (hN.ball (n + 1)))),
      (adaptedSet n).2.linearIndepOn_extend subset_union_left⟩

lemma adaptedSet_mono : Monotone fun n ↦ (hN.adaptedSet n).1 :=
  monotone_nat_of_le_succ fun n ↦ (hN.adaptedSet n).2.subset_extend subset_union_left

lemma adaptedSet_subset (n : ℕ) :
    (hN.adaptedSet n).1 ⊆ (pthPowers k κ p).mkQ '' (hN.ball n) := by
  induction n with
  | zero => exact (linearIndepOn_empty k id).extend_subset (empty_subset _)
  | succ n ih =>
    refine ((hN.adaptedSet n).2.extend_subset subset_union_left).trans
      (union_subset (ih.trans ?_) le_rfl)
    exact image_mono fun f hf ↦ (hN.mem_ball.1 hf).trans (Nat.le_succ n)

lemma subset_span_adaptedSet (n : ℕ) :
    (pthPowers k κ p).mkQ '' (hN.ball n) ⊆ span k (hN.adaptedSet n).1 := by
  cases n with
  | zero => exact (linearIndepOn_empty k id).subset_span_extend (empty_subset _)
  | succ n =>
    exact (subset_union_right (s := (hN.adaptedSet n).1)).trans
      ((hN.adaptedSet n).2.subset_span_extend subset_union_left)

/-- Existence of Frobenius-closed bases for fields with a Frobenius-compatible norm. -/
theorem nonempty_frobeniusBasis : Nonempty (FrobeniusBasis k κ p) := by
  have hp := (Fact.out : p.Prime)
  set Pp := pthPowers k κ p
  set π := Pp.mkQ
  set T := fun n ↦ (hN.adaptedSet n).1
  set S := ⋃ n, T n
  have hS : LinearIndepOn k id S :=
    linearIndepOn_iUnion_of_directed hN.adaptedSet_mono.directed_le fun n ↦ (hN.adaptedSet n).2
  -- lifts of the elements of `S`
  have hlift (q : S) : ∃ f : κ, π f = q ∧ ∀ n, (q : κ ⧸ Pp) ∈ T n → N f ≤ n := by
    classical
    have hq : ∃ n, (q : κ ⧸ Pp) ∈ T n := mem_iUnion.1 q.2
    obtain ⟨f, hf, hfq⟩ := hN.adaptedSet_subset _ (Nat.find_spec hq)
    exact ⟨f, hfq, fun n hn ↦ (hN.mem_ball.1 hf).trans (Nat.find_min' hq hn)⟩
  choose u hπu hNu using hlift
  -- `u` is linearly independent modulo `κ^p`
  have hLI : LinearIndependent k (π ∘ u) := by
    have : π ∘ u = fun q : S ↦ (q : κ ⧸ Pp) := funext hπu
    rw [this]
    exact hS
  have hdisj : ∀ f ∈ span k (range u), f ∈ Pp → f = 0 := by
    intro f hf hfP
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
    have h0 : Finsupp.linearCombination k (π ∘ u) c = 0 := by
      rw [Finsupp.linearCombination_apply]
      have : π (c.sum fun i a ↦ a • u i) = 0 := (Submodule.Quotient.mk_eq_zero Pp).2 hfP
      rw [map_finsuppSum] at this
      simpa using this
    rw [(linearIndependent_iff.1 hLI) c h0]
    simp
  -- decomposition `f = f₀ + g ^ p` with `f₀ ∈ Span u`, `‖f₀‖ ≤ ‖f‖`
  have hstep (f : κ) : ∃ f₀ ∈ span k (range u), N f₀ ≤ N f ∧ f - f₀ ∈ Pp := by
    have h1 : π f ∈ span k (T (N f)) := hN.subset_span_adaptedSet _ ⟨f, hN.mem_ball.2 le_rfl, rfl⟩
    have h2 : T (N f) = π '' (u '' {q | (q : κ ⧸ Pp) ∈ T (N f)}) := by
      ext q
      constructor
      · intro hq
        exact ⟨u ⟨q, mem_iUnion.2 ⟨N f, hq⟩⟩, ⟨_, hq, rfl⟩, hπu _⟩
      · rintro ⟨_, ⟨q', hq', rfl⟩, rfl⟩
        rw [hπu]
        exact hq'
    rw [h2, span_image] at h1
    obtain ⟨f₀, hf₀, hπf₀⟩ := mem_map.1 h1
    refine ⟨f₀, span_mono (image_subset_range _ _) hf₀, ?_,
      (Submodule.Quotient.eq Pp).1 hπf₀.symm⟩
    have : span k (u '' {q | (q : κ ⧸ Pp) ∈ T (N f)}) ≤ hN.ball (N f) :=
      span_le.2 (by rintro _ ⟨q, hq, rfl⟩; exact hNu q _ hq)
    exact this hf₀
  -- the family `{1} ⊔ {u_q ^ p ^ i}`
  set b : Option (ℕ × S) → κ := fun j ↦ j.elim 1 fun iq ↦ u iq.2 ^ p ^ iq.1 with hb
  set M := span k (range b)
  have hbσ (j : Option (ℕ × S)) :
      b (j.map fun iq ↦ (iq.1 + 1, iq.2)) = b j ^ p := by
    rcases j with _ | ⟨i, q⟩
    · simp [hb]
    · simp [hb, pow_succ, pow_mul]
  have hu_b : range u ⊆ range b := by
    rintro _ ⟨q, rfl⟩
    exact ⟨some (0, q), by simp [hb]⟩
  -- spanning
  have hfrob : ∀ h ∈ M, h ^ p ∈ M := by
    intro h hh
    induction hh using span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← hbσ]
      exact subset_span ⟨_, rfl⟩
    | zero => simp [zero_pow hp.ne_zero]
    | add x y _ _ hx hy => rw [add_pow_char]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_pow]; exact smul_mem _ _ hx
  have hall : ∀ n, ∀ f : κ, N f = n → f ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro f hf
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · obtain ⟨c, rfl⟩ := hN.mem_range_of_eq_zero f (hf.trans h0)
      rw [Algebra.algebraMap_eq_smul_one]
      exact smul_mem _ _ (subset_span ⟨none, rfl⟩)
    · obtain ⟨f₀, hf₀, hNf₀, g, hg⟩ := hstep f
      have hNg : N g < n := by
        have h1 : N (g ^ p) ≤ n := by
          rw [hg, sub_eq_add_neg]
          exact (hN.add_le _ _).trans (max_le hf.le (by rw [hN.map_neg]; omega))
        rw [hN.pow_char] at h1
        have := hp.two_le
        nlinarith
      have hf' : f = f₀ + g ^ p := by rw [hg]; ring
      rw [hf']
      exact add_mem (span_mono hu_b hf₀) (hfrob g (ih _ hNg g rfl))
  -- linear independence, level by level
  set s : ℕ → Set (Option (ℕ × S)) := fun m ↦ {j | j.elim True fun iq ↦ iq.1 < m} with hs
  have hs_succ (m : ℕ) : s (m + 1) =
      (Option.map fun iq ↦ (iq.1 + 1, iq.2)) '' s m ∪ range fun q ↦ some (0, q) := by
    ext j
    rcases j with _ | ⟨_ | i, q⟩
    · simp [hs]
    · simp [hs]
    · simp [hs]
  have hsLI : ∀ m, LinearIndepOn k b (s m) := by
    intro m
    induction m with
    | zero =>
      have : s 0 = {none} := by
        ext j
        rcases j with _ | ⟨i, q⟩ <;> simp [hs]
      rw [this]
      exact (linearIndepOn_singleton_iff k).2 (by simp [hb])
    | succ m ih =>
      rw [hs_succ]
      refine LinearIndepOn.union ?_ ?_ ?_
      · refine LinearIndepOn.image_of_comp _ _ ?_
        have : b ∘ (Option.map fun iq ↦ (iq.1 + 1, iq.2)) = fun j ↦ b j ^ p := funext hbσ
        rw [this]
        exact LinearIndependent.pow_char (k := k) ih
      · rw [← image_univ]
        refine LinearIndepOn.image_of_comp _ _ ?_
        rw [linearIndepOn_univ_iff]
        convert LinearIndependent.of_comp π hLI using 1
        ext q
        simp [hb]
      · rw [Submodule.disjoint_def]
        intro f hf hf'
        refine hdisj f ?_ ?_
        · refine span_mono ?_ hf'
          rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
          exact ⟨q, by simp [hb]⟩
        · refine span_le.2 ?_ hf
          rintro _ ⟨_, ⟨j, -, rfl⟩, rfl⟩
          rw [hbσ]
          exact pow_mem_pthPowers _
  have hbLI : LinearIndependent k b := by
    rw [← linearIndepOn_univ_iff]
    have : univ = ⋃ m, s m := by
      refine (eq_univ_of_forall fun j ↦ ?_).symm
      rcases j with _ | ⟨i, q⟩
      · exact mem_iUnion.2 ⟨0, by simp [hs]⟩
      · exact mem_iUnion.2 ⟨i + 1, by simp [hs]⟩
    rw [this]
    refine linearIndepOn_iUnion_of_directed (Monotone.directed_le fun m m' h j hj ↦ ?_) hsLI
    rcases j with _ | ⟨i, q⟩
    · simp [hs]
    · simp only [hs, mem_setOf_eq, Option.elim_some] at hj ⊢
      omega
  let B := Module.Basis.mk hbLI (fun f _ ↦ hall _ f rfl)
  refine ⟨⟨S, u, B, by simp [B, hb], fun i q ↦ by simp [B, hb],
    fun f hf g hfg ↦ hdisj f hf (hfg ▸ pow_mem_pthPowers g), fun f hf g hfg ↦ ?_⟩⟩
  -- `Span u ∩ ℘(κ) = 0`
  by_contra hf0
  have hNg : N g ≠ 0 := by
    intro h
    obtain ⟨c, rfl⟩ := hN.mem_range_of_eq_zero g h
    exact hf0 (hdisj f hf (hfg ▸ sub_mem (pow_mem_pthPowers _) (algebraMap_mem_pthPowers c)))
  obtain ⟨g₀, hg₀, hNg₀, h, hh⟩ := hstep g
  have hfg₀ : f + g₀ = 0 := by
    refine hdisj _ (add_mem hf hg₀) ⟨g - h, ?_⟩
    rw [sub_pow_char, hh, hfg]
    ring
  have h1 : N f ≤ N g := by
    rw [eq_neg_of_add_eq_zero_left hfg₀, hN.map_neg]
    exact hNg₀
  have h2 : p * N g ≤ N g := by
    rw [← hN.pow_char, show g ^ p = f + g by rw [hfg]; ring]
    exact (hN.add_le _ _).trans (max_le h1 le_rfl)
  have := hp.two_le
  have : 0 < N g := Nat.pos_of_ne_zero hNg
  nlinarith

end IsFrobeniusNorm

section CurveFunctionField

variable [IsAlgClosed k] [IsCurveFunctionField k κ]

variable (k κ p) in
/-- The pole norm of a function field of one variable over an algebraically closed field is a
Frobenius-compatible norm (Blueprint §9.4, E1). -/
theorem isFrobeniusNorm_poleNorm : IsFrobeniusNorm k κ p (poleNorm k) where
  add_le := poleNorm_add_le
  smul_le := poleNorm_smul_le
  pow_char f := poleNorm_pow f p
  mem_range_of_eq_zero _ := poleNorm_eq_zero_iff.1

variable (k κ p) in
/-- **Frobenius-closed bases of residue curves** (Blueprint §9.4, E2): a function field of one
variable over an algebraically closed field of characteristic `p` has a Frobenius-closed basis. -/
theorem nonempty_frobeniusBasis [Fact p.Prime] [CharP k p] : Nonempty (FrobeniusBasis k κ p) :=
  haveI : CharP κ p := charP_of_injective_algebraMap (algebraMap k κ).injective p
  (isFrobeniusNorm_poleNorm k κ p).nonempty_frobeniusBasis

end CurveFunctionField

end SemistableReduction
