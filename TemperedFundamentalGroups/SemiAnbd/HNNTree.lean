/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.GroupTheory.GroupAction.Quotient
import TemperedFundamentalGroups.SemiAnbd.DepthTree
import TemperedFundamentalGroups.SemiAnbd.HNNLength

/-!
# The Bass–Serre tree of an HNN extension

Let `H = HNNExtension G A B φ` (`t * a = φ a * t` for `a ∈ A`). Its **Bass–Serre tree**, in
barycentrically subdivided form, has the vertex cosets `H ⧸ G` (kind `true`) and the edge cosets
`H ⧸ B` (kind `false`); the edge `k B` joins `k G` and `k t G` (well defined since
`t⁻¹ B t = A ⊆ G`). This is the tree of the level groups of the tempered fundamental group of a
semi-graph of anabelioids with one vertex and one loop (the stable `1`-gon, [SemiAnbd] §3; the
level groups are HNN extensions `Q_v *_{Q_e}`, decision (c) of `MR12-tfg-plan.md`).

The tree property is proved with the depth criterion `SimpleGraph.isTree_of_depth`: the depth of
`k G` is twice the `t`-length of `k`, and every vertex other than `G` has exactly one neighbour of
smaller depth (Britton's lemma, through `HNNExtension.tLength_mul_of_mul_t_pow`).

## Main results

* `HNNExtension.bassSerreGraph`: the subdivided Bass–Serre graph on `H ⧸ G ⊕ H ⧸ B`.
* `HNNExtension.adj_inr_iff`: the two neighbours of an edge coset.
* `HNNExtension.isTree_bassSerreGraph`: it is a tree.
* `HNNExtension.bassSerreGraph_adj_smul`: `H` acts by graph automorphisms (left translation).
-/

open HNNExtension.NormalWord QuotientGroup

namespace HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

variable (φ) in
/-- The vertex stabiliser `G ⊆ H`. -/
abbrev vertexSubgroup : Subgroup (HNNExtension G A B φ) := (of : G →* HNNExtension G A B φ).range

variable (φ) in
/-- The edge stabiliser `B ⊆ H` (the stabiliser of the edge from `G` to `t G`). -/
abbrev edgeSubgroup : Subgroup (HNNExtension G A B φ) := B.map (of : G →* HNNExtension G A B φ)

variable (φ) in
/-- The vertices of the subdivided Bass–Serre tree. -/
abbrev BSVertex : Type _ :=
  (HNNExtension G A B φ ⧸ vertexSubgroup φ) ⊕ (HNNExtension G A B φ ⧸ edgeSubgroup φ)

variable (φ) in
/-- The incidence relation: the edge coset `k B` meets `k G` and `k t G`. -/
def BSRel : BSVertex φ → BSVertex φ → Prop
  | .inl x, .inr e => ∃ k : HNNExtension G A B φ, e = (k : _ ⧸ edgeSubgroup φ) ∧
      (x = (k : _ ⧸ vertexSubgroup φ) ∨ x = ((k * t : HNNExtension G A B φ) : _ ⧸ vertexSubgroup φ))
  | _, _ => False

variable (φ) in
/-- **The subdivided Bass–Serre graph** of the HNN extension. -/
def bassSerreGraph : SimpleGraph (BSVertex φ) := SimpleGraph.fromRel (BSRel φ)

lemma mk_vertex_eq_iff {k k' : HNNExtension G A B φ} :
    (k : _ ⧸ vertexSubgroup φ) = k' ↔ ∃ y : G, k' = k * of y := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [hy, mul_inv_cancel_left]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp⟩

lemma mk_edge_eq_iff {k k' : HNNExtension G A B φ} :
    (k : _ ⧸ edgeSubgroup φ) = k' ↔ ∃ b : B, k' = k * of (b : G) := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨y, hy, hyk⟩
    exact ⟨⟨y, hy⟩, by rw [hyk, mul_inv_cancel_left]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by simp⟩

/-- The two neighbours of the edge coset `k B` are `k G` and `k t G`. -/
theorem adj_inr_iff (k : HNNExtension G A B φ) (y : BSVertex φ) :
    (bassSerreGraph φ).Adj (.inr (k : _ ⧸ edgeSubgroup φ)) y ↔
      y = .inl (k : _ ⧸ vertexSubgroup φ) ∨
        y = .inl ((k * t : HNNExtension G A B φ) : _ ⧸ vertexSubgroup φ) := by
  rcases y with x | e
  · simp only [bassSerreGraph, SimpleGraph.fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true,
      BSRel, false_or, true_and, Sum.inl.injEq]
    constructor
    · rintro ⟨k', hk', hx⟩
      obtain ⟨b, rfl⟩ := mk_edge_eq_iff.1 hk'
      rcases hx with rfl | rfl
      · exact Or.inl ((mk_vertex_eq_iff (k := k) (k' := k * of (b : G))).2 ⟨b, rfl⟩).symm
      · refine Or.inr ((mk_vertex_eq_iff (k := k * t)
          (k' := (k * of (b : G) * t : HNNExtension G A B φ))).2 ⟨φ.symm b, ?_⟩).symm
        rw [mul_assoc, of_mul_t, ← mul_assoc]
    · intro hx
      exact ⟨k, rfl, hx⟩
  · simp [bassSerreGraph, BSRel]

lemma adj_inl_inr_iff (x : HNNExtension G A B φ ⧸ vertexSubgroup φ)
    (e : HNNExtension G A B φ ⧸ edgeSubgroup φ) :
    (bassSerreGraph φ).Adj (.inl x) (.inr e) ↔ BSRel φ (.inl x) (.inr e) := by
  simp [bassSerreGraph, BSRel]

lemma not_adj_inl_inl (x y : HNNExtension G A B φ ⧸ vertexSubgroup φ) :
    ¬ (bassSerreGraph φ).Adj (.inl x) (.inl y) := by
  simp [bassSerreGraph, BSRel]

lemma not_adj_inr_inr (x y : HNNExtension G A B φ ⧸ edgeSubgroup φ) :
    ¬ (bassSerreGraph φ).Adj (.inr x) (.inr y) := by
  simp [bassSerreGraph, BSRel]

/-! ### Depth -/

/-- The `t`-length of a vertex coset. -/
noncomputable def vertexDepth (x : HNNExtension G A B φ ⧸ vertexSubgroup φ) : ℕ :=
  Quotient.liftOn' x tLength fun a b hab ↦ by
    obtain ⟨y, rfl⟩ := mk_vertex_eq_iff.1 (Quotient.sound' hab)
    exact (tLength_mul_of a y).symm

@[simp] lemma vertexDepth_mk (k : HNNExtension G A B φ) :
    vertexDepth (k : _ ⧸ vertexSubgroup φ) = tLength k := rfl

/-- The smaller `t`-length of the two ends of an edge coset. -/
noncomputable def edgeDepth (e : HNNExtension G A B φ ⧸ edgeSubgroup φ) : ℕ :=
  Quotient.liftOn' e (fun k ↦ min (tLength k) (tLength (k * t))) fun a b hab ↦ by
    obtain ⟨b, rfl⟩ := mk_edge_eq_iff.1 (Quotient.sound' hab)
    rw [tLength_mul_of, mul_assoc, of_mul_t, ← mul_assoc, tLength_mul_of]

@[simp] lemma edgeDepth_mk (k : HNNExtension G A B φ) :
    edgeDepth (k : _ ⧸ edgeSubgroup φ) = min (tLength k) (tLength (k * t)) := rfl

/-- The depth on the subdivided Bass–Serre graph. -/
noncomputable def bsDepth : BSVertex φ → ℕ
  | .inl x => 2 * vertexDepth x
  | .inr e => 2 * edgeDepth e + 1

lemma tLength_mul_t (k : HNNExtension G A B φ) :
    tLength (k * t) = tLength k + 1 ∨ tLength (k * t) + 1 = tLength k := by
  simpa using tLength_mul_t_pow k 1

/-- Every vertex coset `h G` other than `G` has a unique edge coset going down, described by a
reduced word `head, l ++ [(u, g)]` of `h`. -/
lemma down_unique (head : G) (l : List (ℤˣ × G)) (u : ℤˣ) (g : G)
    (hc : (l ++ [(u, g)]).IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1))
    (k : HNNExtension G A B φ)
    (hk : (k : _ ⧸ vertexSubgroup φ) =
        ((⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ : _ ⧸ vertexSubgroup φ) ∨
      ((k * t : HNNExtension G A B φ) : _ ⧸ vertexSubgroup φ) =
        ((⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ : _ ⧸ vertexSubgroup φ))
    (hlt : min (tLength k) (tLength (k * t)) < l.length + 1) :
    (k : _ ⧸ edgeSubgroup φ) =
      (if u = -1 then (⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ * of g⁻¹
        else (⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ * of g⁻¹ * t⁻¹ :
          HNNExtension G A B φ) := by
  set h := (⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ with hh
  have hlen : tLength h = l.length + 1 := by simp [h, tLength_prod]
  rcases hk with hk | hk
  · obtain ⟨y, rfl⟩ := mk_vertex_eq_iff.1 hk.symm
    have hf := tLength_mul_of_mul_t_pow (φ := φ) head l u g hc y 1
    rw [tLength_mul_of, hlen] at hlt
    simp only [Units.val_one, zpow_one] at hf
    rw [← hh] at hf
    split_ifs at hf with hcan
    · obtain ⟨hmem, hu⟩ := hcan
      have hu' : u = -1 := by rw [hu, neg_neg]
      subst hu'
      rw [if_pos rfl]
      have hmem' : g * y ∈ B := hmem
      refine (mk_edge_eq_iff.2 ⟨⟨g * y, hmem'⟩, ?_⟩).symm
      change h * of y = h * of g⁻¹ * of (g * y)
      rw [mul_assoc, ← map_mul, inv_mul_cancel_left]
    · omega
  · have hk' : k = h * of (by exact (mk_vertex_eq_iff.1 hk.symm).choose) * t⁻¹ := by
      rw [← (mk_vertex_eq_iff.1 hk.symm).choose_spec, mul_inv_cancel_right]
    set y := (mk_vertex_eq_iff.1 hk.symm).choose
    rw [hk'] at hlt ⊢
    have hf := tLength_mul_of_mul_t_pow (φ := φ) head l u g hc y (-1)
    simp only [Units.val_neg, Units.val_one, Int.reduceNeg, zpow_neg, zpow_one] at hf
    rw [← hh] at hf
    rw [inv_mul_cancel_right, tLength_mul_of, hlen] at hlt
    split_ifs at hf with hcan
    · obtain ⟨hmem, hu⟩ := hcan
      have hu' : u = 1 := neg_injective hu.symm
      subst hu'
      rw [if_neg (by decide)]
      have hmem' : g * y ∈ A := hmem
      refine (mk_edge_eq_iff.2 ⟨φ ⟨g * y, hmem'⟩, ?_⟩).symm
      rw [equiv_eq_conj]
      simp only [mul_assoc, inv_mul_cancel_left]
      rw [← mul_assoc (of g⁻¹), ← map_mul, inv_mul_cancel_left]
    · omega

/-- The depth criterion holds for the subdivided Bass–Serre graph. -/
theorem depthData :
    (bassSerreGraph φ).DepthData bsDepth
      (.inl ((1 : HNNExtension G A B φ) : _ ⧸ vertexSubgroup φ)) where
  ne_of_adj x y hxy := by
    rcases x with x | x <;> rcases y with y | y
    · exact absurd hxy (not_adj_inl_inl x y)
    · simp only [bsDepth]; omega
    · simp only [bsDepth]; omega
    · exact absurd hxy (not_adj_inr_inr x y)
  root_depth := by
    simp only [bsDepth]
    rw [show ((1 : HNNExtension G A B φ) : _ ⧸ vertexSubgroup φ) = QuotientGroup.mk 1 from rfl,
      vertexDepth_mk, (tLength_eq_zero_iff _).2 (one_mem _)]
  exists_lt x hx := by
    rcases x with x | e
    · induction x using QuotientGroup.induction_on with
      | H h =>
      obtain ⟨⟨head, l, hc⟩, rfl⟩ := exists_reducedWord φ h
      rcases l.eq_nil_or_append_singleton with rfl | ⟨l, ⟨u, g⟩, rfl⟩
      · exact absurd ((congrArg Sum.inl (QuotientGroup.eq.2 (by
          simp [ReducedWord.prod]))).symm) hx
      set h := (⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ with hh
      have hlen : tLength h = l.length + 1 := by simp [h, tLength_prod]
      rcases Int.units_eq_one_or u with rfl | rfl
      · -- the edge `h g⁻¹ t⁻¹ B`, whose upper end is `h G`
        refine ⟨.inr ((h * of g⁻¹ * t⁻¹ : HNNExtension G A B φ) : _ ⧸ edgeSubgroup φ), ?_, ?_⟩
        · rw [SimpleGraph.adj_comm, adj_inr_iff]
          right
          rw [inv_mul_cancel_right]
          exact congrArg Sum.inl (mk_vertex_eq_iff.2 ⟨g, by simp⟩).symm
        · have hf := tLength_mul_of_mul_t_pow (φ := φ) head l 1 g hc g⁻¹ (-1)
          simp only [mul_inv_cancel, one_mem, Units.val_neg, Units.val_one, Int.reduceNeg,
            zpow_neg, zpow_one, true_and, if_pos] at hf
          rw [← hh] at hf
          simp only [bsDepth, edgeDepth_mk, vertexDepth_mk, hlen, hf]
          omega
      · -- the edge `h g⁻¹ B`, whose lower end is `h g⁻¹ t G`
        refine ⟨.inr ((h * of g⁻¹ : HNNExtension G A B φ) : _ ⧸ edgeSubgroup φ), ?_, ?_⟩
        · rw [SimpleGraph.adj_comm, adj_inr_iff]
          left
          exact congrArg Sum.inl (mk_vertex_eq_iff.2 ⟨g, by simp⟩).symm
        · have hf := tLength_mul_of_mul_t_pow (φ := φ) head l (-1) g hc g⁻¹ 1
          simp only [mul_inv_cancel, one_mem, neg_neg, true_and, if_pos, Units.val_one,
            zpow_one] at hf
          rw [← hh] at hf
          simp only [bsDepth, edgeDepth_mk, vertexDepth_mk, hlen, hf]
          omega
    · induction e using QuotientGroup.induction_on with
      | H k =>
      rcases tLength_mul_t k with h1 | h1
      · refine ⟨.inl (k : _ ⧸ vertexSubgroup φ), (adj_inr_iff k _).2 (Or.inl rfl), ?_⟩
        simp only [bsDepth, edgeDepth_mk, vertexDepth_mk]
        omega
      · refine ⟨.inl ((k * t : HNNExtension G A B φ) : _ ⧸ vertexSubgroup φ),
          (adj_inr_iff k _).2 (Or.inr rfl), ?_⟩
        simp only [bsDepth, edgeDepth_mk, vertexDepth_mk]
        omega
  unique_lt x y z hxy hy hxz hz := by
    rcases x with x | e
    · induction x using QuotientGroup.induction_on with
      | H h =>
      obtain ⟨⟨head, l, hc⟩, rfl⟩ := exists_reducedWord φ h
      rcases l.eq_nil_or_append_singleton with rfl | ⟨l, ⟨u, g⟩, rfl⟩
      · rcases y with y | y
        · exact absurd hxy (not_adj_inl_inl _ _)
        · simp only [bsDepth, vertexDepth_mk, tLength_prod, List.length_nil] at hy
          omega
      have hlen : tLength ((⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ) =
          l.length + 1 := by simp [tLength_prod]
      -- both `y` and `z` are the canonical edge going down
      have key : ∀ w : BSVertex φ, (bassSerreGraph φ).Adj (.inl (QuotientGroup.mk
          ((⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ))) w →
          bsDepth w < bsDepth (.inl (QuotientGroup.mk
            ((⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ))) →
          w = .inr (QuotientGroup.mk (if u = -1 then
            (⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ * of g⁻¹
            else (⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ * of g⁻¹ * t⁻¹)) := by
        intro w hw hd
        rcases w with w | w
        · exact absurd hw (not_adj_inl_inl _ _)
        induction w using QuotientGroup.induction_on with
        | H k =>
        rw [SimpleGraph.adj_comm, adj_inr_iff] at hw
        simp only [bsDepth, edgeDepth_mk, vertexDepth_mk, hlen] at hd
        refine congrArg Sum.inr (down_unique head l u g hc k ?_ (by omega))
        rcases hw with hw | hw
        · exact Or.inl (Sum.inl_injective hw).symm
        · exact Or.inr (Sum.inl_injective hw).symm
      rw [key y hxy hy, key z hxz hz]
    · induction e using QuotientGroup.induction_on with
      | H k =>
      rw [adj_inr_iff] at hxy hxz
      have hd := tLength_mul_t k
      rcases hxy with rfl | rfl <;> rcases hxz with rfl | rfl <;>
        simp only [bsDepth, edgeDepth_mk, vertexDepth_mk] at hy hz ⊢ <;> omega

/-- **The Bass–Serre graph of an HNN extension is a tree.** -/
theorem isTree_bassSerreGraph : (bassSerreGraph φ).IsTree :=
  SimpleGraph.isTree_of_depth _ depthData

/-! ### The action of `H` -/

lemma bsRel_smul (g : HNNExtension G A B φ) (x y : BSVertex φ) :
    BSRel φ (g • x) (g • y) ↔ BSRel φ x y := by
  suffices h : ∀ (g : HNNExtension G A B φ) (x y : BSVertex φ), BSRel φ x y →
      BSRel φ (g • x) (g • y) by
    refine ⟨fun hg ↦ ?_, h g x y⟩
    simpa [smul_smul] using h g⁻¹ _ _ hg
  intro g x y hxy
  rcases x with x | x <;> rcases y with e | e <;> simp only [BSRel] at hxy
  obtain ⟨k, rfl, hx⟩ := hxy
  refine ⟨g * k, rfl, ?_⟩
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by simp [mul_assoc])

/-- `H` acts on the Bass–Serre tree by graph automorphisms. -/
theorem bassSerreGraph_adj_smul (g : HNNExtension G A B φ) (x y : BSVertex φ) :
    (bassSerreGraph φ).Adj (g • x) (g • y) ↔ (bassSerreGraph φ).Adj x y := by
  simp only [bassSerreGraph, SimpleGraph.fromRel_adj, ne_eq, smul_left_cancel_iff, bsRel_smul]

end HNNExtension
