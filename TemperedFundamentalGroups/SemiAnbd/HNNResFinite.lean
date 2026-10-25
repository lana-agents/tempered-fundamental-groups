/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.HNNExtension
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.Logic.Equiv.Fintype

/-!
# HNN extensions of finite groups are residually finite

For a finite group `G` with subgroups `A`, `B` and an isomorphism `φ : A ≃* B`, the HNN extension
`G *_φ` is residually finite. This is the group-theoretic input of [SemiAnbd] Prop 3.6(iii)
(`semianbd.txt` l.1808, proof l.1880: the tempered fundamental group injects into the profinite
one since "discrete free groups ... are residually finite") for the level groups of a loop of
finite groups; we give a direct proof by permutation representations, without free groups.

**The representations.** Choose a bijection `σ : G ≃ G` with `σ (a * x) = φ a * σ x` for `a ∈ A`
(it exists since `A` and `B` have the same number of right cosets; `HNNExtension.ResFin.sigma`).
For a finite set `V` and permutations `π c` of `V` indexed by the right cosets `c ∈ A\G`,
`G` acts on `G × V` by left multiplication on the first factor and `t` acts by
`(x, v) ↦ (σ x, π [x] v)`; this defines `HNNExtension.ResFin.rep : G *_φ →* Perm (G × V)`.
Taking `V` a point gives a finite quotient in which `G` embeds ([SemiAnbd] Prop 2.5(ii) for the
loop: `HNNExtension.exists_finite_quotient_injective_of`).

**Faithfulness on a given element.** For a reduced word `g₀ t^{u₁} g₁ ⋯ t^{uₙ} gₙ` with `n ≥ 1`,
the first coordinate of the orbit of `(x, 0)` is independent of the `π c`; the letter `t^{uₖ}`
needs `π cₖ` to move `k - 1 ↦ k` (`uₖ = 1`) resp. `k ↦ k - 1` (`uₖ = -1`) in `V = {0, …, n}`.
These prescriptions form a partial injection for every `c`: two consecutive letters `t g t⁻¹`
(`g ∉ A`) or `t⁻¹ g t` (`g ∉ B`) have different cosets, which is exactly reducedness
(Britton). Extending the partial injections to permutations, the word moves `(x, 0)` to `(·, n)`.

* `HNNExtension.residuallyFinite`: `Group.ResiduallyFinite (HNNExtension G A B φ)` for finite `G`.
-/

open Function

namespace HNNExtension

namespace ResFin

universe u

variable {G : Type u} [Group G] {A B : Subgroup G}

/-- The right coset `A x`, as the left coset `x⁻¹ A`. -/
abbrev cls (A : Subgroup G) (x : G) : G ⧸ A := ((x⁻¹ : G) : G ⧸ A)

lemma cls_mul_of_mem {a : G} (ha : a ∈ A) (x : G) : cls A (a * x) = cls A x := by
  simp only [cls, mul_inv_rev]
  exact QuotientGroup.mk_mul_of_mem _ (inv_mem ha)

lemma cls_eq_iff {x y : G} : cls A x = cls A y ↔ x * y⁻¹ ∈ A := by
  simp only [cls, QuotientGroup.eq, inv_inv]

/-- A representative of a right coset. -/
noncomputable abbrev rep (A : Subgroup G) (c : G ⧸ A) : G := (Quotient.out c)⁻¹

lemma cls_rep (c : G ⧸ A) : cls A (rep A c) = c := by
  simp only [cls, rep, inv_inv]
  exact QuotientGroup.out_eq' c

lemma mul_rep_inv_mem (x : G) : x * (rep A (cls A x))⁻¹ ∈ A :=
  cls_eq_iff.1 (cls_rep (cls A x)).symm

variable [Finite G] (φ : A ≃* B)

include φ in
lemma card_quotient_eq : Nat.card (G ⧸ A) = Nat.card (G ⧸ B) := by
  have hA := Subgroup.card_mul_index A
  have hB := Subgroup.card_mul_index B
  have hAB : Nat.card A = Nat.card B := Nat.card_congr φ.toEquiv
  have hpos : 0 < Nat.card A := Nat.card_pos
  change Nat.card A * Nat.card (G ⧸ A) = Nat.card G at hA
  change Nat.card B * Nat.card (G ⧸ B) = Nat.card G at hB
  rw [hAB] at hA
  exact Nat.eq_of_mul_eq_mul_left (hAB ▸ hpos) (hA.trans hB.symm)

/-- A bijection of the right coset spaces `A\G ≃ B\G`. -/
noncomputable def cosetEquiv : G ⧸ A ≃ G ⧸ B :=
  (Finite.card_eq.1 (card_quotient_eq φ)).some

/-- The underlying map of `sigma`. -/
noncomputable def sigmaFun (x : G) : G :=
  (φ ⟨x * (rep A (cls A x))⁻¹, mul_rep_inv_mem x⟩ : G) * rep B (cosetEquiv φ (cls A x))

lemma cls_sigmaFun (x : G) : cls B (sigmaFun φ x) = cosetEquiv φ (cls A x) := by
  rw [sigmaFun, cls_mul_of_mem (φ _).2, cls_rep]

lemma sigmaFun_mul (a : A) (x : G) : sigmaFun φ (a * x) = φ a * sigmaFun φ x := by
  have hc : cls A (a * x) = cls A x := cls_mul_of_mem a.2 x
  have key : ∀ (c : G ⧸ A) (hc1 : cls A (a * x) = c) (hc2 : cls A x = c),
      (φ ⟨a * x * (rep A c)⁻¹, hc1 ▸ mul_rep_inv_mem (a * x)⟩ : G) =
        φ a * (φ ⟨x * (rep A c)⁻¹, hc2 ▸ mul_rep_inv_mem x⟩ : G) := by
    intro c hc1 hc2
    rw [← Subgroup.coe_mul, ← map_mul]
    congr 2
    exact Subtype.ext (by simp [mul_assoc])
  have := key (cls A x) hc rfl
  simp only [sigmaFun, hc]
  rw [this, mul_assoc]

lemma sigmaFun_injective : Injective (sigmaFun φ) := by
  intro x y h
  have hc : cls A x = cls A y := by
    have := congrArg (cls B) h
    rw [cls_sigmaFun, cls_sigmaFun] at this
    exact (cosetEquiv φ).injective this
  have key : ∀ (c : G ⧸ A) (hx : cls A x = c) (hy : cls A y = c),
      (φ ⟨x * (rep A c)⁻¹, hx ▸ mul_rep_inv_mem x⟩ : G) * rep B (cosetEquiv φ c) =
        (φ ⟨y * (rep A c)⁻¹, hy ▸ mul_rep_inv_mem y⟩ : G) * rep B (cosetEquiv φ c) → x = y := by
    intro c hx hy he
    have h1 := mul_right_cancel he
    have h2 := φ.injective (Subtype.ext h1)
    exact mul_right_cancel (congrArg Subtype.val h2)
  refine key (cls A x) rfl hc.symm ?_
  have h' : sigmaFun φ y = (φ ⟨y * (rep A (cls A x))⁻¹, hc ▸ mul_rep_inv_mem y⟩ : G) *
      rep B (cosetEquiv φ (cls A x)) := by
    simp only [sigmaFun, hc]
  rw [← h', ← h]
  rfl

/-- **The coset-matching bijection** `σ : G ≃ G`, `σ (a * x) = φ a * σ x` for `a ∈ A`. -/
noncomputable def sigma : G ≃ G :=
  Equiv.ofBijective (sigmaFun φ) (Finite.injective_iff_bijective.1 (sigmaFun_injective φ))

lemma sigma_apply (x : G) : sigma φ x = sigmaFun φ x := rfl

lemma sigma_mul (a : A) (x : G) : sigma φ (a * x) = φ a * sigma φ x := sigmaFun_mul φ a x

lemma cls_sigma (x : G) : cls B (sigma φ x) = cosetEquiv φ (cls A x) := cls_sigmaFun φ x

lemma cls_sigma_symm (z : G) : cls A ((sigma φ).symm z) = (cosetEquiv φ).symm (cls B z) := by
  rw [Equiv.eq_symm_apply, ← cls_sigma, Equiv.apply_symm_apply]

variable {V : Type*} [Finite V]

/-- The action of `G` on `G × V` by left multiplication on the first factor. -/
def psi : G →* Equiv.Perm (G × V) where
  toFun g := (Equiv.mulLeft g).prodCongr (Equiv.refl V)
  map_one' := by ext <;> simp
  map_mul' g h := by ext <;> simp [mul_assoc]

omit [Finite G] [Finite V] in
@[simp]
lemma psi_apply (g : G) (p : G × V) : psi g p = (g * p.1, p.2) := rfl

/-- The underlying map of `tau`. -/
noncomputable def tauFun (π : G ⧸ A → Equiv.Perm V) (p : G × V) : G × V :=
  (sigma φ p.1, π (cls A p.1) p.2)

omit [Finite V] in
lemma tauFun_injective (π : G ⧸ A → Equiv.Perm V) : Injective (tauFun φ π) := by
  rintro ⟨x, v⟩ ⟨y, w⟩ h
  simp only [tauFun, Prod.mk.injEq] at h
  obtain rfl := (sigma φ).injective h.1
  exact Prod.ext rfl ((π _).injective h.2)

/-- The action of the stable letter: `(x, v) ↦ (σ x, π [x] v)`. -/
noncomputable def tau (π : G ⧸ A → Equiv.Perm V) : Equiv.Perm (G × V) :=
  Equiv.ofBijective (tauFun φ π) (Finite.injective_iff_bijective.1 (tauFun_injective φ π))

lemma tau_apply (π : G ⧸ A → Equiv.Perm V) (p : G × V) :
    tau φ π p = (sigma φ p.1, π (cls A p.1) p.2) := rfl

lemma tau_symm_apply (π : G ⧸ A → Equiv.Perm V) (p : G × V) :
    (tau φ π).symm p =
      ((sigma φ).symm p.1, (π (cls A ((sigma φ).symm p.1))).symm p.2) := by
  rw [Equiv.symm_apply_eq, tau_apply]
  simp

lemma tau_mul_psi (π : G ⧸ A → Equiv.Perm V) (a : A) :
    tau φ π * psi (a : G) = psi (φ a : G) * tau φ π := by
  ext ⟨x, v⟩
  · simp [tau_apply, sigma_mul]
  · simp [tau_apply, cls_mul_of_mem a.2]

/-- **The permutation representation** `G *_φ →* Perm (G × V)`. -/
noncomputable def rep' (π : G ⧸ A → Equiv.Perm V) : HNNExtension G A B φ →* Equiv.Perm (G × V) :=
  lift psi (tau φ π) (tau_mul_psi φ π)

lemma rep'_of (π : G ⧸ A → Equiv.Perm V) (g : G) : rep' φ π (of g) = psi g := lift_of _ _ _ _

lemma rep'_t (π : G ⧸ A → Equiv.Perm V) : rep' φ π t = tau φ π := lift_t _ _ _

/-! ### The orbit of a reduced word -/

/-- The first coordinate of the action of `t^u * g`. -/
noncomputable def step (u : ℤˣ) (g y : G) : G :=
  if u = 1 then sigma φ (g * y) else (sigma φ).symm (g * y)

/-- The right coset used by the letter `t^u * g` at `y`. -/
noncomputable def letterCls (u : ℤˣ) (g y : G) : G ⧸ A :=
  if u = 1 then cls A (g * y) else cls A ((sigma φ).symm (g * y))

/-- The product of the letters `t^u * g` of a list. -/
def prodL (L : List (ℤˣ × G)) : HNNExtension G A B φ :=
  (L.map fun x ↦ t ^ (x.1 : ℤ) * of x.2).prod

/-- The first coordinate of the orbit. -/
noncomputable def gpart : List (ℤˣ × G) → G → G
  | [], x => x
  | (u, g) :: L, x => step φ u g (gpart L x)

lemma rep'_letter (π : G ⧸ A → Equiv.Perm V) (u : ℤˣ) (g y : G) (v : V) :
    rep' φ π (t ^ (u : ℤ) * of g) (y, v) =
      (step φ u g y,
        if u = 1 then π (letterCls φ u g y) v else (π (letterCls φ u g y)).symm v) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [map_mul, rep'_t, rep'_of, tau_apply, step, letterCls]
  · have hne : (-1 : ℤˣ) ≠ 1 := by decide
    simp [map_mul, rep'_t, rep'_of, tau_symm_apply, step, letterCls, hne]

/-- The point `m` of `{0, …, n}` (truncated at `n`). -/
def pt (n m : ℕ) : Fin (n + 1) := ⟨min m n, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma pt_val {n m : ℕ} (hm : m ≤ n) : (pt n m : ℕ) = m := min_eq_left hm

/-- The prescription for the letters of a list: the letter of level `k` moves `k - 1 ↦ k`. -/
noncomputable def Good {n : ℕ} (π : G ⧸ A → Equiv.Perm (Fin (n + 1))) :
    List (ℤˣ × G) → G → Prop
  | [], _ => True
  | (u, g) :: L, x => Good π L x ∧
      if u = 1 then π (letterCls φ u g (gpart φ L x)) (pt n L.length) = pt n (L.length + 1)
      else π (letterCls φ u g (gpart φ L x)) (pt n (L.length + 1)) = pt n L.length

lemma rep'_prodL {n : ℕ} (π : G ⧸ A → Equiv.Perm (Fin (n + 1))) (x : G) :
    ∀ L : List (ℤˣ × G), Good φ π L x →
      rep' φ π (prodL φ L) (x, pt n 0) = (gpart φ L x, pt n L.length)
  | [], _ => by simp [prodL, gpart]
  | (u, g) :: L, ⟨hL, hg⟩ => by
    have ih := rep'_prodL π x L hL
    rw [prodL, List.map_cons, List.prod_cons, map_mul, Equiv.Perm.mul_apply]
    change rep' φ π _ (rep' φ π (prodL φ L) (x, pt n 0)) = _
    rw [ih, rep'_letter]
    refine Prod.ext rfl ?_
    simp only [List.length_cons]
    split_ifs at hg ⊢ with hu
    · rw [hg]
    · rw [Equiv.symm_apply_eq, hg]

/-! ### The partial injections -/

/-- The edges prescribed by the letters of a list for the coset `c` (as pairs of naturals). -/
noncomputable def Rel (c : G ⧸ A) : List (ℤˣ × G) → G → ℕ → ℕ → Prop
  | [], _, _, _ => False
  | (u, g) :: L, x, a, b => Rel c L x a b ∨ (c = letterCls φ u g (gpart φ L x) ∧
      if u = 1 then a = L.length ∧ b = L.length + 1 else a = L.length + 1 ∧ b = L.length)

lemma Rel.le {c : G ⧸ A} {x : G} :
    ∀ {L : List (ℤˣ × G)} {a b : ℕ}, Rel φ c L x a b → a ≤ L.length ∧ b ≤ L.length
  | [], _, _, h => h.elim
  | (u, g) :: L, a, b, h => by
    rcases h with h | ⟨-, h⟩
    · have := Rel.le h
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      split_ifs at h <;> omega

/-- An edge touching the top vertex `L.length` comes from the first letter. -/
lemma Rel.top {c : G ⧸ A} {x : G} {u : ℤˣ} {g : G} {L : List (ℤˣ × G)} {a b : ℕ}
    (h : Rel φ c ((u, g) :: L) x a b) (hab : a = L.length + 1 ∨ b = L.length + 1) :
    c = letterCls φ u g (gpart φ L x) ∧
      if u = 1 then a = L.length ∧ b = L.length + 1 else a = L.length + 1 ∧ b = L.length := by
  rcases h with h | h
  · have := Rel.le φ h
    omega
  · exact h

lemma letterCls_one (g y : G) : letterCls φ 1 g y = cls A (g * y) := by simp [letterCls]

lemma letterCls_neg (g y : G) : letterCls φ (-1) g y = cls A ((sigma φ).symm (g * y)) := by
  simp [letterCls, show (-1 : ℤˣ) ≠ 1 by decide]

lemma step_one (g y : G) : step φ 1 g y = sigma φ (g * y) := by simp [step]

lemma step_neg (g y : G) : step φ (-1) g y = (sigma φ).symm (g * y) := by
  simp [step, show (-1 : ℤˣ) ≠ 1 by decide]

/-- `t g t⁻¹` with `g ∉ A`: different cosets. -/
lemma letterCls_ne_of_t_g_tinv {g g' y : G} (hg : g ∉ A) :
    letterCls φ 1 g (step φ (-1) g' y) ≠ letterCls φ (-1) g' y := by
  rw [letterCls_one, letterCls_neg, step_neg, ne_eq, cls_eq_iff, mul_assoc, mul_inv_cancel,
    mul_one]
  exact hg

/-- `t⁻¹ g t` with `g ∉ B`: different cosets. -/
lemma letterCls_ne_of_tinv_g_t {g g' y : G} (hg : g ∉ B) :
    letterCls φ (-1) g (step φ 1 g' y) ≠ letterCls φ 1 g' y := by
  rw [letterCls_neg, letterCls_one, step_one, cls_sigma_symm]
  intro h
  have h' := congrArg (cosetEquiv φ) h
  rw [Equiv.apply_symm_apply, ← cls_sigma, cls_eq_iff, mul_assoc, mul_inv_cancel, mul_one] at h'
  exact hg h'

lemma units_ne_one {u : ℤˣ} (h : u ≠ 1) : u = -1 := (Int.units_eq_one_or u).resolve_left h

/-- The source conflict is excluded: after a letter `t g` (moving `m ↦ m + 1`, `m = L.length`)
no edge of the same coset leaves `m` (reducedness: `t g t⁻¹` with `g ∈ A` does not occur). -/
lemma Rel.not_src {c : G ⧸ A} {x g : G} {L : List (ℤˣ × G)}
    (hch : (((1 : ℤˣ), g) :: L).IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1))
    (hc : c = letterCls φ 1 g (gpart φ L x)) {b : ℕ} (h : Rel φ c L x L.length b) : False := by
  cases L with
  | nil => exact h
  | cons l L =>
    obtain ⟨u', g'⟩ := l
    obtain ⟨hc', ht⟩ := Rel.top φ h (Or.inl (by simp))
    have hne : u' ≠ 1 := by
      intro hu
      rw [if_pos hu] at ht
      simp at ht
    have hu' := units_ne_one hne
    subst hu'
    have hgA : g ∉ A := fun hg ↦ by
      have := (List.isChain_cons_cons.1 hch).1 (by rw [toSubgroup_one]; exact hg)
      exact hne (by simp at this)
    exact letterCls_ne_of_t_g_tinv φ hgA (hc.symm.trans hc')

/-- The target conflict is excluded: after a letter `t⁻¹ g` (moving `m + 1 ↦ m`) no edge of
the same coset enters `m` (reducedness: `t⁻¹ g t` with `g ∈ B` does not occur). -/
lemma Rel.not_tgt {c : G ⧸ A} {x g : G} {L : List (ℤˣ × G)}
    (hch : (((-1 : ℤˣ), g) :: L).IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1))
    (hc : c = letterCls φ (-1) g (gpart φ L x)) {a : ℕ} (h : Rel φ c L x a L.length) : False := by
  cases L with
  | nil => exact h
  | cons l L =>
    obtain ⟨u', g'⟩ := l
    obtain ⟨hc', ht⟩ := Rel.top φ h (Or.inr (by simp))
    have hu' : u' = 1 := by
      by_contra hne
      rw [if_neg hne] at ht
      simp at ht
    subst hu'
    have hgB : g ∉ B := fun hg ↦ by
      have := (List.isChain_cons_cons.1 hch).1 (by rw [toSubgroup_neg_one]; exact hg)
      exact (show (-1 : ℤˣ) ≠ 1 by decide) (by simp at this)
    exact letterCls_ne_of_tinv_g_t φ hgB (hc.symm.trans hc')

/-- The prescribed edges form a partial function (reducedness). -/
lemma Rel.functional {c : G ⧸ A} {x : G} :
    ∀ {L : List (ℤˣ × G)}, L.IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1) →
      ∀ {a b b' : ℕ}, Rel φ c L x a b → Rel φ c L x a b' → b = b'
  | [], _, _, _, _, h, _ => h.elim
  | (u, g) :: L, hch, a, b, b', h, h' => by
    have hchL := (List.isChain_cons.1 hch).2
    rcases h with h | ⟨hc, hu⟩ <;> rcases h' with h' | ⟨hc', hu'⟩
    · exact Rel.functional hchL h h'
    · exfalso
      have hle := Rel.le φ h
      by_cases h1 : u = 1
      · rw [if_pos h1] at hu'
        subst h1
        rw [hu'.1] at h
        exact Rel.not_src φ hch hc' h
      · rw [if_neg h1] at hu'
        omega
    · exfalso
      have hle := Rel.le φ h'
      by_cases h1 : u = 1
      · rw [if_pos h1] at hu
        subst h1
        rw [hu.1] at h'
        exact Rel.not_src φ hch hc h'
      · rw [if_neg h1] at hu
        omega
    · by_cases h1 : u = 1
      · rw [if_pos h1] at hu hu'
        omega
      · rw [if_neg h1] at hu hu'
        omega

/-- The prescribed edges form an injective partial function (reducedness). -/
lemma Rel.injective {c : G ⧸ A} {x : G} :
    ∀ {L : List (ℤˣ × G)}, L.IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1) →
      ∀ {a a' b : ℕ}, Rel φ c L x a b → Rel φ c L x a' b → a = a'
  | [], _, _, _, _, h, _ => h.elim
  | (u, g) :: L, hch, a, a', b, h, h' => by
    have hchL := (List.isChain_cons.1 hch).2
    rcases h with h | ⟨hc, hu⟩ <;> rcases h' with h' | ⟨hc', hu'⟩
    · exact Rel.injective hchL h h'
    · exfalso
      have hle := Rel.le φ h
      by_cases h1 : u = 1
      · rw [if_pos h1] at hu'
        omega
      · rw [if_neg h1] at hu'
        have hu1 := units_ne_one h1
        subst hu1
        rw [hu'.2] at h
        exact Rel.not_tgt φ hch hc' h
    · exfalso
      have hle := Rel.le φ h'
      by_cases h1 : u = 1
      · rw [if_pos h1] at hu
        omega
      · rw [if_neg h1] at hu
        have hu1 := units_ne_one h1
        subst hu1
        rw [hu.2] at h'
        exact Rel.not_tgt φ hch hc h'
    · by_cases h1 : u = 1
      · rw [if_pos h1] at hu hu'
        omega
      · rw [if_neg h1] at hu hu'
        omega

/-- A bounded injective partial function on `ℕ` extends to a permutation of `Fin (n + 1)`. -/
lemma exists_perm_of_rel {n : ℕ} (R : ℕ → ℕ → Prop) (hle : ∀ a b, R a b → a ≤ n ∧ b ≤ n)
    (hf : ∀ a b b', R a b → R a b' → b = b') (hi : ∀ a a' b, R a b → R a' b → a = a') :
    ∃ π : Equiv.Perm (Fin (n + 1)), ∀ a b, R a b → π (pt n a) = pt n b := by
  classical
  have hlt : ∀ i : {i : Fin (n + 1) // ∃ b, R i b}, Classical.choose i.2 < n + 1 := fun i ↦
    Nat.lt_succ_of_le (hle _ _ (Classical.choose_spec i.2)).2
  let f : {i : Fin (n + 1) // ∃ b, R i b} → Fin (n + 1) := fun i ↦ ⟨Classical.choose i.2, hlt i⟩
  have hfR : ∀ i, R i.1 (f i) := fun i ↦ Classical.choose_spec i.2
  have hinj : Injective f := fun i i' h ↦
    Subtype.ext (Fin.ext (hi _ _ _ (hfR i) (h ▸ hfR i')))
  refine ⟨(Equiv.ofInjective f hinj).extendSubtype, fun a b hab ↦ ?_⟩
  have ha := (hle a b hab).1
  have hpa : ∃ b', R ((pt n a : Fin (n + 1)) : ℕ) b' := ⟨b, (pt_val ha).symm ▸ hab⟩
  rw [Equiv.extendSubtype_apply_of_mem (Equiv.ofInjective f hinj) (pt n a) hpa]
  refine Fin.ext ?_
  rw [pt_val (hle a b hab).2]
  change (f ⟨_, hpa⟩ : ℕ) = b
  exact hf _ _ _ (hfR ⟨_, hpa⟩) ((pt_val ha).symm ▸ hab)

lemma good_of_rel {n : ℕ} (π : G ⧸ A → Equiv.Perm (Fin (n + 1))) (x : G) :
    ∀ L : List (ℤˣ × G), (∀ c a b, Rel φ c L x a b → π c (pt n a) = pt n b) → Good φ π L x
  | [], _ => trivial
  | (u, g) :: L, h => by
    refine ⟨good_of_rel π x L fun c a b hr ↦ h c a b (Or.inl hr), ?_⟩
    split_ifs with hu
    · exact h _ _ _ (Or.inr ⟨rfl, by simp [hu]⟩)
    · exact h _ _ _ (Or.inr ⟨rfl, by simp [hu]⟩)

/-- **Every nontrivial element of `G *_φ` acts nontrivially in some permutation representation on
a finite set.** -/
theorem exists_rep'_ne_one (w : HNNExtension G A B φ) (hw : w ≠ 1) :
    ∃ (n : ℕ) (π : G ⧸ A → Equiv.Perm (Fin (n + 1))), rep' φ π w ≠ 1 := by
  obtain ⟨d⟩ := NormalWord.TransversalPair.nonempty G A B
  set nw := NormalWord.equiv φ d w
  have hprod : w = of nw.head * prodL φ nw.toList :=
    ((NormalWord.equiv φ d).symm_apply_apply w).symm
  set L := nw.toList
  have hch : L.IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1) := nw.chain
  have hR : ∀ c, ∃ π : Equiv.Perm (Fin (L.length + 1)), ∀ a b, Rel φ c L 1 a b →
      π (pt L.length a) = pt L.length b := fun c ↦
    exists_perm_of_rel _ (fun a b h ↦ Rel.le φ h) (fun a b b' h h' ↦ Rel.functional φ hch h h')
      (fun a a' b h h' ↦ Rel.injective φ hch h h')
  choose π hπ using hR
  refine ⟨L.length, π, fun h1 ↦ ?_⟩
  have hgood := good_of_rel φ π 1 L hπ
  have hact := congrArg (fun f : Equiv.Perm (G × Fin (L.length + 1)) ↦ f (1, pt L.length 0)) h1
  simp only [Equiv.Perm.one_apply] at hact
  rw [hprod, map_mul, Equiv.Perm.mul_apply, rep'_prodL φ π 1 L hgood, rep'_of, psi_apply,
    Prod.mk.injEq] at hact
  rcases hL : L.length with _ | n
  · -- no stable letters: `w = of head`
    have hnil : L = [] := List.length_eq_zero_iff.1 hL
    have hg : gpart φ L 1 = 1 := by rw [hnil]; rfl
    rw [hg, mul_one] at hact
    apply hw
    rw [hprod, hact.1]
    rw [hnil]
    simp [prodL]
  · have h2 := congrArg Fin.val hact.2
    rw [pt_val le_rfl, pt_val (Nat.zero_le _), hL] at h2
    exact Nat.succ_ne_zero n h2

end ResFin

open ResFin

universe v

/-- **HNN extensions of finite groups are residually finite** (the input of [SemiAnbd]
Prop 3.6(iii) for loops of finite groups). -/
instance residuallyFinite {G : Type*} [Group G] [Finite G] {A B : Subgroup G} (φ : A ≃* B) :
    Group.ResiduallyFinite (HNNExtension G A B φ) :=
  Group.residuallyFinite_of_forall_exists_finite_monoidHom fun w hw ↦ by
    obtain ⟨n, π, h⟩ := exists_rep'_ne_one φ w hw
    exact ⟨_, inferInstance, inferInstance, rep' φ π, h⟩

/-- **[SemiAnbd] Prop 2.5(ii) for a loop of finite groups**: there is a finite quotient of
`G *_φ` in which `G` embeds. -/
theorem exists_finite_quotient_injective_of {G : Type v} [Group G] [Finite G] {A B : Subgroup G}
    (φ : A ≃* B) : ∃ (Q : Type v) (_ : Group Q) (_ : Finite Q) (f : HNNExtension G A B φ →* Q),
      Injective (f.comp of) := by
  refine ⟨Equiv.Perm (G × Fin 1), inferInstance, inferInstance,
    rep' φ (fun _ ↦ 1), fun g g' h ↦ ?_⟩
  have := congrArg (fun f : Equiv.Perm (G × Fin 1) ↦ (f (1, 0)).1) h
  simpa [rep'_of] using this

end HNNExtension
