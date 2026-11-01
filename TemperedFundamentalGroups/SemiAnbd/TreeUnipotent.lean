/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing

/-!
# Groups acting freely on trees are residually `ℓ`

Let a group `F` act on a tree `T` by graph automorphisms, **freely on the vertices** and
preserving a **bipartition** of `T` (adjacent vertices have different colours; this excludes
inversions). Then for every prime `ℓ` and every `h ≠ 1` in `F` there is a normal subgroup
`U ⊴ F` of finite index with `h ∉ U` and `f ^ (ℓ ^ m) ∈ U` for all `f` (so `F ⧸ U` is a finite
`ℓ`-group): `TreeUnipotent.exists_normal_pow_mem`.

This is the input "free discrete groups inject into their pro-`Σ` completions" of
[SemiAnbd] Cor 3.11 (`semianbd.txt` l.2279–2280, citing Rem 1.7.1 l.893–895: the pro-`l`
version of residual finiteness, [RZ] Prop 3.3.15) in the form needed for the level groups of
a loop of groups (`SemiAnbd/OneGonSigmaKernel.lean`), where the free group is the kernel of a
finite quotient injective on the vertex group, acting freely on the Bass–Serre tree. We do not
show that `F` is free: we use the tree directly.

**The representation** (unipotent, a "path" version of the Magnus representation). Let
`d₀, …, d_{k-1}` be the darts of the path from a base vertex `x₀` to `h • x₀` (`k ≥ 1` since the
action is free). To a dart `(u, v)` attach the `(k+1) × (k+1)` matrix over `ZMod ℓ`
`w u v = 1 + ∑ₐ c(u,v,a) E_{a,a+1}`, `c(u,v,a) = [(u,v) ∈ F·dₐ] - [(v,u) ∈ F·dₐ]`. Then
`w v u = (w u v)⁻¹` (no two consecutive darts of the path lie in one `F`-orbit up to reversal:
that needs freeness and the bipartition), and `ρ f = ∏` of `w` along the path from `x₀` to `f • x₀`
is a homomorphism (`TreeUnipotent.pprod_trans`: products along walks in a tree only depend on the
endpoints). The `(0, k)` entry of `ρ h` is `∏ₐ c(dₐ, a) = 1`, so `ρ h ≠ 1`; all `ρ f` are
unipotent upper triangular, so `(ρ f) ^ (ℓ ^ m) = 1` for `ℓ ^ m ≥ k + 1`.

* `TreeUnipotent.pprod`, `pprod_trans`, `pprod_smul`: path products in a tree;
* `TreeUnipotent.sd`, `IsSU`, `isSU_pow_eq_zero`, `pow_char_pow_one_add`, `entry_prod_sd`:
  superdiagonal and unipotent matrices;
* **`TreeUnipotent.exists_normal_pow_mem`**.
-/

open SimpleGraph

namespace TemperedFundamentalGroups

namespace TreeUnipotent

/-! ### Superdiagonal and unipotent matrices -/

section Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The superdiagonal matrix with entry `s a` at `(a, a + 1)`. -/
def sd (s : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b ↦ if (b : ℕ) = a + 1 then s a else 0

lemma sd_apply (s : ℕ → R) (a b : Fin n) :
    (sd s : Matrix (Fin n) (Fin n) R) a b = if (b : ℕ) = a + 1 then s a else 0 := rfl

/-- Strictly upper triangular. -/
def IsSU (N : Matrix (Fin n) (Fin n) R) : Prop := ∀ a b : Fin n, (b : ℕ) ≤ a → N a b = 0

lemma isSU_sd (s : ℕ → R) : IsSU (sd s : Matrix (Fin n) (Fin n) R) := fun a b hab ↦ by
  rw [sd_apply, if_neg (by omega)]

lemma IsSU.add {N N' : Matrix (Fin n) (Fin n) R} (h : IsSU N) (h' : IsSU N') : IsSU (N + N') :=
  fun a b hab ↦ by simp [h a b hab, h' a b hab]

lemma IsSU.mul {N N' : Matrix (Fin n) (Fin n) R} (h : IsSU N) (h' : IsSU N') : IsSU (N * N') :=
  fun a b hab ↦ by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ ↦ ?_
    by_cases hm : (m : ℕ) ≤ a
    · rw [h a m hm, zero_mul]
    · rw [h' m b (by omega), mul_zero]

lemma IsSU.pow_apply {N : Matrix (Fin n) (Fin n) R} (h : IsSU N) :
    ∀ (r : ℕ) (a b : Fin n), (b : ℕ) < a + r → (N ^ r) a b = 0
  | 0, a, b, hab => by
    rw [pow_zero, Matrix.one_apply_ne]
    intro hab'
    rw [hab'] at hab
    omega
  | r + 1, a, b, hab => by
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ ↦ ?_
    by_cases hm : (m : ℕ) < a + r
    · rw [h.pow_apply r a m hm, zero_mul]
    · rw [h m b (by omega), mul_zero]

lemma IsSU.pow_eq_zero {N : Matrix (Fin n) (Fin n) R} (h : IsSU N) : N ^ n = 0 := by
  ext a b
  exact h.pow_apply n a b (by omega)

/-- **Unipotent matrices have `ℓ`-power order in characteristic `ℓ`.** -/
lemma pow_char_pow_one_add {ℓ : ℕ} [Fact ℓ.Prime] [CharP R ℓ] {N : Matrix (Fin n) (Fin n) R}
    (h : IsSU N) : (1 + N) ^ (ℓ ^ n) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [add_pow_char_pow_of_commute ℓ n (Commute.one_left N), one_pow]
    have hle : n ≤ ℓ ^ n := (Nat.lt_pow_self (Fact.out : ℓ.Prime).one_lt).le
    rw [← Nat.add_sub_cancel' hle, pow_add, h.pow_eq_zero, zero_mul, add_zero]

/-- The product of a list of unipotent matrices is unipotent. -/
lemma isSU_prod_sub_one (L : List (Matrix (Fin n) (Fin n) R)) (hL : ∀ A ∈ L, IsSU (A - 1)) :
    IsSU (L.prod - 1) := by
  induction L with
  | nil => intro a b _; simp
  | cons A L ih =>
    have hA := hL A List.mem_cons_self
    have hL' := ih fun B hB ↦ hL B (List.mem_cons_of_mem _ hB)
    have : (A :: L).prod - 1 = (A - 1) + (L.prod - 1) + (A - 1) * (L.prod - 1) := by
      rw [List.prod_cons]; noncomm_ring
    rw [this]
    exact (hA.add hL').add (hA.mul hL')

lemma sd_mul_sd_eq_zero (s : ℕ → R) (hs : ∀ a, s a * s (a + 1) = 0) :
    (sd s : Matrix (Fin n) (Fin n) R) * sd s = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [sd_apply, sd_apply]
  by_cases h1 : (m : ℕ) = a + 1
  · by_cases h2 : (b : ℕ) = m + 1
    · rw [if_pos h1, if_pos h2, h1]; exact hs a
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

lemma mul_sd_apply (X : Matrix (Fin n) (Fin n) R) (s : ℕ → R) (a b : Fin n) :
    (X * (sd s : Matrix (Fin n) (Fin n) R)) a b =
      ∑ m : Fin n, if (b : ℕ) = m + 1 then X a m * s m else 0 := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [sd_apply, mul_ite, mul_zero]

/-- **The corner entry of a product of `1 + sd`'s.** For a list `L` and entries `φ x`, if the
`i`-th factor has entry `1` at `(i, i + 1)`, the product has entry `1` at `(0, |L|)` and `0`
further right. -/
lemma entry_prod_sd {X : Type*} (φ : X → ℕ → R) (L : List X) (hn : L.length < n)
    (hL : ∀ (i : ℕ) (hi : i < L.length), φ L[i] i = 1) :
    (L.map fun x ↦ (1 + sd (φ x) : Matrix (Fin n) (Fin n) R)).prod
        ⟨0, by omega⟩ ⟨L.length, hn⟩ = 1 ∧
      ∀ b : Fin n, L.length < b →
        (L.map fun x ↦ (1 + sd (φ x) : Matrix (Fin n) (Fin n) R)).prod ⟨0, by omega⟩ b = 0 := by
  induction L using List.reverseRecOn with
  | nil =>
    refine ⟨by simp, fun b hb ↦ ?_⟩
    rw [List.map_nil, List.prod_nil, Matrix.one_apply_ne]
    intro h
    rw [← h] at hb
    simp at hb
  | append_singleton L x ih =>
    have hn' : L.length < n := by simp at hn; omega
    obtain ⟨ih1, ih2⟩ := ih hn' fun i hi ↦ by
      have := hL i (by simp; omega)
      rwa [List.getElem_append_left hi] at this
    have hx : φ x L.length = 1 := by
      have := hL L.length (by simp)
      rwa [List.getElem_concat_length rfl] at this
    set P := (L.map fun x ↦ (1 + sd (φ x) : Matrix (Fin n) (Fin n) R)).prod
    have hprod : ((L ++ [x]).map fun x ↦ (1 + sd (φ x) : Matrix (Fin n) (Fin n) R)).prod =
        P + P * sd (φ x) := by
      rw [List.map_append, List.prod_append]; simp [P, mul_add]
    rw [hprod]
    refine ⟨?_, fun b hb ↦ ?_⟩
    · rw [Matrix.add_apply, mul_sd_apply, ih2 _ (by simp), zero_add,
        Finset.sum_eq_single ⟨L.length, hn'⟩]
      · simp [ih1, hx]
      · intro m _ hm
        rw [if_neg]
        intro h
        exact hm (Fin.ext (by simp at h ⊢; omega))
      · simp
    · simp only [List.length_append, List.length_singleton] at hb
      rw [Matrix.add_apply, mul_sd_apply, ih2 b (by omega), zero_add]
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      by_cases h : (b : ℕ) = m + 1
      · rw [if_pos h, ih2 m (by omega), zero_mul]
      · rw [if_neg h]

end Matrix

/-! ### Path products in a tree -/

section Tree

variable {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) {M : Type*} [Monoid M]

/-- The product of `w` along a walk. -/
def wprod (w : V → V → M) {x y : V} (p : T.Walk x y) : M :=
  (p.darts.map fun d ↦ w d.fst d.snd).prod

@[simp] lemma wprod_nil (w : V → V → M) (x : V) : wprod w (Walk.nil : T.Walk x x) = 1 := rfl

@[simp] lemma wprod_cons (w : V → V → M) {x x' y : V} (h : T.Adj x x') (p : T.Walk x' y) :
    wprod w (Walk.cons h p) = w x x' * wprod w p := by
  simp [wprod]

lemma wprod_append (w : V → V → M) {x y z : V} (p : T.Walk x y) (q : T.Walk y z) :
    wprod w (p.append q) = wprod w p * wprod w q := by
  simp [wprod, Walk.darts_append]

/-- The unique path between two vertices of a tree. -/
noncomputable def tpath (x y : V) : T.Walk x y := (hT.existsUnique_path x y).exists.choose

lemma tpath_isPath (x y : V) : (tpath hT x y).IsPath :=
  (hT.existsUnique_path x y).exists.choose_spec

lemma eq_tpath {x y : V} {p : T.Walk x y} (hp : p.IsPath) : p = tpath hT x y :=
  (hT.existsUnique_path x y).unique hp (tpath_isPath hT x y)

/-- The product of `w` along the path between two vertices. -/
noncomputable def pprod (w : V → V → M) (x y : V) : M := wprod w (tpath hT x y)

variable {hT} {w : V → V → M} (hw : ∀ u v, T.Adj u v → w u v * w v u = 1)
include hw

lemma pprod_cons {x x' : V} (h : T.Adj x x') (z : V) :
    w x x' * pprod hT w x' z = pprod hT w x z := by
  classical
  set p := tpath hT x' z
  have hp : p.IsPath := tpath_isPath hT x' z
  by_cases hx : x ∈ p.support
  · have h1 : p.takeUntil x hx = Walk.cons h.symm Walk.nil :=
      (hT.existsUnique_path x' x).unique (hp.takeUntil hx)
        (by simpa using h.ne.symm)
    have h2 : p.dropUntil x hx = tpath hT x z := eq_tpath hT (hp.dropUntil hx)
    have hpp : pprod hT w x' z = w x' x * pprod hT w x z := by
      change wprod w p = _
      rw [← p.take_spec hx, wprod_append, h1, h2, wprod_cons, wprod_nil, mul_one]
      rfl
    rw [hpp, ← mul_assoc, hw x x' h, one_mul]
  · have hq : (Walk.cons h p).IsPath := (Walk.cons_isPath_iff h p).2 ⟨hp, hx⟩
    change _ = wprod w (tpath hT x z)
    rw [← eq_tpath hT hq, wprod_cons]
    rfl

omit hw in
lemma pprod_self (x : V) : pprod hT w x x = 1 := by
  change wprod w (tpath hT x x) = 1
  rw [← eq_tpath hT (Walk.IsPath.nil : (Walk.nil : T.Walk x x).IsPath)]
  rfl

/-- **Products along walks in a tree only depend on the endpoints.** -/
lemma wprod_eq_pprod {x z : V} (p : T.Walk x z) : wprod w p = pprod hT w x z := by
  induction p with
  | nil => exact (pprod_self _).symm
  | cons h p ih => rw [wprod_cons, ih, pprod_cons hw h]

lemma pprod_trans (x y z : V) : pprod hT w x y * pprod hT w y z = pprod hT w x z := by
  change wprod w (tpath hT x y) * wprod w (tpath hT y z) = _
  rw [← wprod_append, wprod_eq_pprod hw]

/-- Invariance of path products under graph automorphisms preserving `w`. -/
lemma pprod_iso (σ : T ≃g T) (hσ : ∀ u v, w (σ u) (σ v) = w u v) (x y : V) :
    pprod hT w (σ x) (σ y) = pprod hT w x y := by
  refine (wprod_eq_pprod hw ((tpath hT x y).map σ.toHom)).symm.trans ?_
  unfold wprod pprod
  rw [Walk.darts_map, List.map_map]
  congr 1
  exact List.map_congr_left fun d _ ↦ hσ d.fst d.snd

end Tree

/-! ### Free actions on bipartite trees -/

section Action

variable {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) {F : Type*} [Group F] [MulAction F V]
  (hadj : ∀ (f : F) (x y : V), T.Adj (f • x) (f • y) ↔ T.Adj x y)

/-- The graph automorphism given by a group element. -/
def isoOf (f : F) : T ≃g T where
  toEquiv := MulAction.toPerm f
  map_rel_iff' := hadj f _ _

@[simp] lemma isoOf_apply (f : F) (x : V) : isoOf hadj f x = f • x := rfl

variable {M : Type*} [Monoid M] {w : V → V → M} (hw : ∀ u v, T.Adj u v → w u v * w v u = 1)
  (hwF : ∀ (f : F) u v, w (f • u) (f • v) = w u v)

/-- The path-product homomorphism `f ↦ ∏ w` along the path from `x₀` to `f • x₀`. -/
noncomputable def pathHom (x₀ : V) : F →* M where
  toFun f := pprod hT w x₀ (f • x₀)
  map_one' := by rw [one_smul]; exact pprod_self x₀
  map_mul' f g := by
    rw [mul_smul, ← pprod_trans hw x₀ (f • x₀) (f • g • x₀)]
    congr 1
    exact pprod_iso hw (isoOf hadj f) (fun u v ↦ hwF f u v) x₀ (g • x₀)

lemma pathHom_apply (x₀ : V) (f : F) :
    pathHom hT hadj hw hwF x₀ f = pprod hT w x₀ (f • x₀) := rfl

end Action

section Detect

open Classical in
/-- The coefficient `c(u, v, a) = [(u, v) ∈ F·dₐ] - [(v, u) ∈ F·dₐ]`. -/
noncomputable def coef {V : Type*} {T : SimpleGraph V} (F : Type*) [Group F] [MulAction F V]
    (R : Type*) [CommRing R] (D : List T.Dart) (u v : V) (a : ℕ) : R :=
  if ha : a < D.length then
    (if ∃ f : F, f • u = D[a].fst ∧ f • v = D[a].snd then 1 else 0) -
      (if ∃ f : F, f • v = D[a].fst ∧ f • u = D[a].snd then 1 else 0)
  else 0

variable {V : Type*} {T : SimpleGraph V} {F : Type*} [Group F] [MulAction F V]
  {R : Type*} [CommRing R] (D : List T.Dart)

lemma coef_swap (u v : V) (a : ℕ) : coef F R D v u a = - coef F R D u v a := by
  unfold coef
  split_ifs <;> simp

lemma coef_smul (f : F) (u v : V) (a : ℕ) : coef F R D (f • u) (f • v) a = coef F R D u v a := by
  have key : ∀ (x y p q : V), (∃ g : F, g • f • x = p ∧ g • f • y = q) ↔
      (∃ g : F, g • x = p ∧ g • y = q) :=
    fun x y p q ↦ ⟨fun ⟨g, h1, h2⟩ ↦
        ⟨g * f, by rw [mul_smul]; exact h1, by rw [mul_smul]; exact h2⟩,
      fun ⟨g, h1, h2⟩ ↦ ⟨g * f⁻¹, by rw [mul_smul, inv_smul_smul]; exact h1,
        by rw [mul_smul, inv_smul_smul]; exact h2⟩⟩
  unfold coef
  by_cases ha : a < D.length
  · rw [dif_pos ha, dif_pos ha, propext (key u v _ _), propext (key v u _ _)]
  · rw [dif_neg ha, dif_neg ha]

end Detect

section Main

variable {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) {F : Type*} [Group F] [MulAction F V]
  {R : Type*} [CommRing R]
  (hadj : ∀ (f : F) (x y : V), T.Adj (f • x) (f • y) ↔ T.Adj x y)
  (κ : V → Bool) (hκ : ∀ x y, T.Adj x y → κ x ≠ κ y) (hκF : ∀ (f : F) x, κ (f • x) = κ x)
  (hfree : ∀ (f : F) (x : V), f • x = x → f = 1)

/-- Two consecutive darts of a path are not opposite. -/
lemma darts_succ_ne_symm {x y : V} {p : T.Walk x y} (hp : p.IsPath) (a : ℕ)
    (ha : a + 1 < p.darts.length) : p.darts[a + 1] ≠ (p.darts[a]).symm := by
  intro h
  have hnd : p.edges.Nodup := hp.isTrail.edges_nodup
  have hlen : p.edges.length = p.darts.length := by simp [Walk.edges]
  have he : p.edges[a + 1]'(by omega) = p.edges[a]'(by omega) := by
    simp only [Walk.edges, List.getElem_map, h, Dart.edge_symm]
  have := hnd.getElem_inj_iff.1 he
  omega

lemma darts_succ_fst {x y : V} (p : T.Walk x y) (a : ℕ) (ha : a + 1 < p.darts.length) :
    (p.darts[a + 1]).fst = (p.darts[a]).snd := by
  have := List.isChain_iff_getElem.1 (Walk.isChain_dartAdj_darts p) a ha
  exact this.symm

include hκ hκF hfree in
lemma coef_mul_succ_eq_zero {x y : V} {p : T.Walk x y} (hp : p.IsPath) {u v : V}
    (huv : T.Adj u v) (a : ℕ) :
    coef F R p.darts u v a * coef F R p.darts u v (a + 1) = 0 := by
  classical
  by_cases ha : a + 1 < p.darts.length
  swap
  · unfold coef; rw [dif_neg ha, mul_zero]
  have ha' : a < p.darts.length := by omega
  have hfst := darts_succ_fst p a ha
  have hsymm := darts_succ_ne_symm hp a ha
  -- the four cases
  have hcases : ∀ f g : F,
      ¬ ((f • u = (p.darts[a]).fst ∧ f • v = (p.darts[a]).snd ∨
          f • v = (p.darts[a]).fst ∧ f • u = (p.darts[a]).snd) ∧
        (g • u = (p.darts[a + 1]).fst ∧ g • v = (p.darts[a + 1]).snd ∨
          g • v = (p.darts[a + 1]).fst ∧ g • u = (p.darts[a + 1]).snd)) := by
    rintro f g ⟨h1 | h1, h2 | h2⟩
    · -- `f • v = g • u`: colours
      have : κ v = κ u := by rw [← hκF f v, h1.2, ← hfst, ← h2.1, hκF]
      exact hκ u v huv this.symm
    · -- `f • v = g • v`, so `f = g` and the darts are opposite
      have hfg : f = g := by
        have h3 : (g⁻¹ * f) • v = v := by rw [mul_smul, h1.2, ← hfst, ← h2.1, inv_smul_smul]
        exact (inv_mul_eq_one.1 (hfree _ _ h3)).symm
      subst hfg
      exact hsymm ((Dart.ext_iff _ _).2 (Prod.ext (h2.1.symm.trans h1.2) (h2.2.symm.trans h1.1)))
    · have hfg : f = g := by
        have h3 : (g⁻¹ * f) • u = u := by rw [mul_smul, h1.2, ← hfst, ← h2.1, inv_smul_smul]
        exact (inv_mul_eq_one.1 (hfree _ _ h3)).symm
      subst hfg
      exact hsymm ((Dart.ext_iff _ _).2 (Prod.ext (h2.1.symm.trans h1.2) (h2.2.symm.trans h1.1)))
    · have : κ u = κ v := by rw [← hκF f u, h1.2, ← hfst, ← h2.1, hκF]
      exact hκ u v huv this
  unfold coef
  rw [dif_pos ha', dif_pos ha]
  by_cases hA : (∃ f : F, f • u = (p.darts[a]).fst ∧ f • v = (p.darts[a]).snd) ∨
      (∃ f : F, f • v = (p.darts[a]).fst ∧ f • u = (p.darts[a]).snd)
  · have hB : ¬ ((∃ g : F, g • u = (p.darts[a + 1]).fst ∧ g • v = (p.darts[a + 1]).snd) ∨
        (∃ g : F, g • v = (p.darts[a + 1]).fst ∧ g • u = (p.darts[a + 1]).snd)) := by
      rintro (⟨g, hg⟩ | ⟨g, hg⟩) <;> rcases hA with ⟨f, hf⟩ | ⟨f, hf⟩
      · exact hcases f g ⟨Or.inl hf, Or.inl hg⟩
      · exact hcases f g ⟨Or.inr hf, Or.inl hg⟩
      · exact hcases f g ⟨Or.inl hf, Or.inr hg⟩
      · exact hcases f g ⟨Or.inr hf, Or.inr hg⟩
    have hB1 : ¬ ∃ g : F, g • u = (p.darts[a + 1]).fst ∧ g • v = (p.darts[a + 1]).snd :=
      fun h ↦ hB (Or.inl h)
    have hB2 : ¬ ∃ g : F, g • v = (p.darts[a + 1]).fst ∧ g • u = (p.darts[a + 1]).snd :=
      fun h ↦ hB (Or.inr h)
    rw [if_neg hB1, if_neg hB2]
    simp
  · have hA1 : ¬ ∃ g : F, g • u = (p.darts[a]).fst ∧ g • v = (p.darts[a]).snd :=
      fun h ↦ hA (Or.inl h)
    have hA2 : ¬ ∃ g : F, g • v = (p.darts[a]).fst ∧ g • u = (p.darts[a]).snd :=
      fun h ↦ hA (Or.inr h)
    rw [if_neg hA1, if_neg hA2]
    simp

include hκ hκF in
lemma coef_dart {x y : V} (p : T.Walk x y) (a : ℕ) (ha : a < p.darts.length) :
    coef F R p.darts (p.darts[a]).fst (p.darts[a]).snd a = 1 := by
  classical
  unfold coef
  rw [dif_pos ha, if_pos ⟨1, one_smul _ _, one_smul _ _⟩, if_neg]
  · simp
  rintro ⟨f, h1, -⟩
  have hadj' := (p.darts[a]).adj
  exact hκ _ _ hadj' (by rw [← h1, hκF])

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

include hT hadj hκ hκF hfree in
/-- **Groups acting freely on bipartite trees are residually `ℓ`.** -/
theorem exists_normal_pow_mem (x₀ : V) (h : F) (hh : h ≠ 1) :
    ∃ (U : Subgroup F) (m : ℕ), U.Normal ∧ U.FiniteIndex ∧ h ∉ U ∧ ∀ f : F, f ^ (ℓ ^ m) ∈ U := by
  classical
  set p := tpath hT x₀ (h • x₀)
  have hp : p.IsPath := tpath_isPath hT _ _
  set D := p.darts
  set k := D.length
  set n := k + 1
  let w : V → V → Matrix (Fin n) (Fin n) (ZMod ℓ) := fun u v ↦ 1 + sd (coef F (ZMod ℓ) D u v)
  have hwsym : ∀ u v, w v u = 1 - sd (coef F (ZMod ℓ) D u v) := fun u v ↦ by
    have hc : coef F (ZMod ℓ) D v u = fun a ↦ - coef F (ZMod ℓ) D u v a :=
      funext (coef_swap D u v)
    simp only [w, hc, sub_eq_add_neg]
    congr 1
    ext a b
    simp only [sd_apply, Matrix.neg_apply]
    split_ifs <;> simp
  have hw : ∀ u v, T.Adj u v → w u v * w v u = 1 := fun u v huv ↦ by
    rw [hwsym u v]
    have h0 := sd_mul_sd_eq_zero (n := n) (coef F (ZMod ℓ) D u v)
      (coef_mul_succ_eq_zero κ hκ hκF hfree hp huv)
    simp only [w]
    rw [mul_sub, mul_one, add_mul, one_mul, h0, add_zero, add_sub_cancel_right]
  have hwF : ∀ (f : F) u v, w (f • u) (f • v) = w u v := fun f u v ↦ by
    simp only [w]
    congr 2
    funext a
    exact coef_smul D f u v a
  let ρ := pathHom hT hadj hw hwF x₀
  -- every `ρ f` is unipotent
  have hSU : ∀ f : F, IsSU (ρ f - 1) := fun f ↦ by
    rw [pathHom_apply]
    refine isSU_prod_sub_one _ fun A hA ↦ ?_
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hA
    simpa [w] using isSU_sd _
  have hpow : ∀ f : F, ρ f ^ (ℓ ^ n) = 1 := fun f ↦ by
    have := pow_char_pow_one_add (ℓ := ℓ) (hSU f)
    rwa [add_sub_cancel] at this
  -- `ρ h ≠ 1`: its `(0, k)` entry is `1`
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exfalso
      have hlen : p.length = 0 := by rw [← Walk.length_darts]; exact hk
      exact hh (hfree h x₀ (Walk.eq_of_length_eq_zero hlen).symm)
    · exact hk
  have hρh : ρ h ≠ 1 := by
    intro h1
    have hentry := (entry_prod_sd (n := n) (fun d : T.Dart ↦ coef F (ZMod ℓ) D d.fst d.snd) D
      (by omega) fun i hi ↦ coef_dart κ hκ hκF p i hi).1
    have : ρ h = (D.map fun d : T.Dart ↦ (1 + sd (coef F (ZMod ℓ) D d.fst d.snd) :
        Matrix (Fin n) (Fin n) (ZMod ℓ))).prod := by
      rw [pathHom_apply]
      change wprod w p = _
      simp only [wprod, w, D]
    rw [← this, h1, Matrix.one_apply_ne (by simp [Fin.ext_iff]; omega)] at hentry
    exact zero_ne_one hentry
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : Finite (Matrix (Fin n) (Fin n) (ZMod ℓ)) :=
    inferInstanceAs (Finite (Fin n → Fin n → ZMod ℓ))
  haveI : Finite (Matrix (Fin n) (Fin n) (ZMod ℓ))ˣ := Finite.of_injective _ Units.val_injective
  refine ⟨ρ.toHomUnits.ker, n, MonoidHom.normal_ker _, ?_, ?_, fun f ↦ ?_⟩
  · refine ⟨?_⟩
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  · intro hm
    apply hρh
    have := congrArg Units.val (MonoidHom.mem_ker.1 hm)
    simpa using this
  · rw [MonoidHom.mem_ker]
    ext
    simp [hpow f]

end Main

end TreeUnipotent

end TemperedFundamentalGroups
