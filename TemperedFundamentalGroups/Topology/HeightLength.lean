/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Topology.CoverLength

/-!
# Height-corrected lengths on tree coverings (Blueprint §10.3.8, I6)

Let `K` be a curve configuration with tree covering `K.Cover r`, with weights `w` on the special
points, and let `ν : ι → Prop` be a set of components (in the application: the components not
contracted over a fixed base model `𝒴`). The **height** of a component vertex `b` is
`dN w ν b`, the infimum of the weights of the walks from `b` to a component vertex labelled in
`ν`. The **height-corrected length condition** `HC w ν a c ℓ` between two vertices `a`, `c`
says that some walk between component vertices `b` near `a` and `b'` near `c` has weight at most
`ℓ + dN b + dN b'` (that is, `D = Q − 2h ≤ ℓ`, without subtraction, with the minimum over the
near vertices of special endpoints).

* `CurveConfig.prev`, `CurveConfig.PWalk.prev`, `CurveConfig.cost_prev`: reversal of walks.
* `CurveConfig.hc_map` (**monotonicity**): along a continuous map `h` of tree coverings over
  `ψ` with harmonic weights (as in `tlen_map_le`), finite weights, and **lifting** of walks
  from non-contracted component vertices with no larger weight (`IsWalkLifting`, from (X1)),
  the condition `HC … ℓ` is preserved: `HC w ν x y ℓ → HC w' ν' (h x) (h y) ℓ`.

The point of the correction is that the true displacement of the base point grows under
refinement around the base point (Blueprint §10.3.7), while `Q − 2h` does not grow.
-/

universe u v u' v'

open Set
open scoped ENNReal

namespace TemperedFundamentalGroups

namespace CurveConfig

section Rev

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

/-- The reversal of a walk of the tree from `t`. -/
def prev : K.Tree r → List (K.Tree r × K.Tree r) → List (K.Tree r × K.Tree r)
  | _, [] => []
  | t, (σ, t') :: L => prev t' L ++ [(σ, t)]

lemma PWalk.prev : ∀ {t : K.Tree r} {L : List (K.Tree r × K.Tree r)}, PWalk t L →
    PWalk (pend t L) (CurveConfig.prev t L) ∧ pend (pend t L) (CurveConfig.prev t L) = t
  | _, [], _ => ⟨trivial, rfl⟩
  | t, (σ, t') :: L, ⟨h₁, h₂, h₃⟩ => by
    obtain ⟨ih₁, ih₂⟩ := PWalk.prev h₃
    simp only [pend_cons, CurveConfig.prev]
    rw [pWalk_append, pend_append, ih₂]
    exact ⟨⟨ih₁, Tree.adj_comm.1 h₂, Tree.adj_comm.1 h₁, trivial⟩, rfl⟩

lemma cost_prev (w : Z → ℝ≥0∞) : ∀ (t : K.Tree r) (L : List (K.Tree r × K.Tree r)),
    cost w (prev t L) = cost w L
  | _, [] => rfl
  | t, (σ, t') :: L => by
    rw [prev, cost_append, cost_prev w t' L, cost_cons, cost_cons, cost_nil, add_zero, add_comm]

lemma cost_ne_top {w : Z → ℝ≥0∞} (hw : ∀ z, w z ≠ ⊤) :
    ∀ L : List (K.Tree r × K.Tree r), cost w L ≠ ⊤
  | [] => by simp
  | p :: L => by
    rw [cost_cons]
    refine ENNReal.add_ne_top.2 ⟨?_, cost_ne_top hw L⟩
    unfold tw
    rcases p.1.1.head? with _ | (_ | s)
    · simp
    · simp
    · simpa using hw s

end Rev

section Height

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

/-- **The height** of a vertex `b`: the infimum of the weights of the walks from `b` to a
component vertex labelled in `ν`. -/
noncomputable def dN (w : Z → ℝ≥0∞) (ν : ι → Prop) (b : K.Tree r) : ℝ≥0∞ :=
  sInf {x | ∃ L, PWalk b L ∧ IsComp (pend b L) ∧ ν (lab (pend b L)) ∧ cost w L = x}

lemma dN_le (w : Z → ℝ≥0∞) (ν : ι → Prop) {b : K.Tree r} {L : List (K.Tree r × K.Tree r)}
    (hL : PWalk b L) (hc : IsComp (pend b L)) (hν : ν (lab (pend b L))) :
    dN w ν b ≤ cost w L :=
  sInf_le ⟨L, hL, hc, hν, rfl⟩

/-- **The height-corrected length condition** `Q − dN b − dN b' ≤ ℓ` for some component
vertices `b` near `a` and `b'` near `c` and a walk between them. -/
def HC (w : Z → ℝ≥0∞) (ν : ι → Prop) (a c : K.Tree r) (ℓ : ℝ≥0∞) : Prop :=
  ∃ b b' L, Near a b ∧ Near c b' ∧ PWalk b L ∧ pend b L = b' ∧
    cost w L ≤ ℓ + dN w ν b + dN w ν b'

lemma hc_of_below (w : Z → ℝ≥0∞) (ν : ι → Prop) {X Y V : K.Tree r} (hX : Below X V)
    (hY : Below Y V) (ℓ : ℝ≥0∞) : HC w ν X Y ℓ := by
  rcases isComp_or_isSpecial V with hV | hV
  · exact ⟨V, V, [], hX.near hV, hY.near hV, trivial, rfl, by simp⟩
  · rw [hX.eq_of_isSpecial hV, hY.eq_of_isSpecial hV]
    obtain ⟨b, hb⟩ := exists_near V
    exact ⟨b, b, [], hb, hb, trivial, rfl, by simp⟩

/-- `HC` bounds the tree length. -/
lemma tlen_le_of_hc {w : Z → ℝ≥0∞} {ν : ι → Prop} {a c : K.Tree r} {ℓ M : ℝ≥0∞}
    (h : HC w ν a c ℓ) (hM : ∀ b b', Near a b → Near c b' → dN w ν b + dN w ν b' ≤ M) :
    tlen w a c ≤ ℓ + M := by
  obtain ⟨b, b', L, hb, hb', hL, hend, hcost⟩ := h
  refine (tlen_le w hb hb' hL hend).trans (hcost.trans ?_)
  rw [add_assoc]
  gcongr
  exact hM b b' hb hb'

/-- Finitely many walks of bounded length from a vertex. -/
lemma finite_pWalks [Finite ι] (b : K.Tree r) :
    ∀ N : ℕ, {L : List (K.Tree r × K.Tree r) | PWalk b L ∧ L.length ≤ N}.Finite
  | 0 => (Set.finite_singleton []).subset (by
      rintro L ⟨-, hL⟩
      simp [List.length_eq_zero_iff.1 (Nat.le_zero.1 hL)])
  | N + 1 => by
    have ih := finite_pWalks b N
    refine (ih.union (ih.biUnion fun L _ => (finite_adj (pend b L)).biUnion fun σ _ =>
      (finite_adj σ).image fun t => L ++ [(σ, t)])).subset ?_
    rintro L ⟨hL, hlen⟩
    rcases L.eq_nil_or_concat with rfl | ⟨L', p, rfl⟩
    · exact .inl ⟨trivial, Nat.zero_le _⟩
    · obtain ⟨σ, t⟩ := p
      rw [List.concat_eq_append] at hL hlen ⊢
      rw [pWalk_append] at hL
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      exact .inr (mem_biUnion (x := L') ⟨hL.1, by omega⟩
        (mem_biUnion (x := σ) hL.2.1 ⟨t, hL.2.2.1, rfl⟩))

/-- **The height is attained** (positive weights bounded below, finite weights). -/
lemma exists_dN_eq [Finite ι] {w : Z → ℝ≥0∞} (hfin : ∀ z, w z ≠ ⊤) {μ : ℝ≥0∞} (hμ0 : μ ≠ 0)
    (hμ : ∀ s ∈ K.S, μ ≤ w s) (ν : ι → Prop) {b : K.Tree r} (hb : IsComp b)
    (hne : ∃ L, PWalk b L ∧ IsComp (pend b L) ∧ ν (lab (pend b L))) :
    ∃ L, PWalk b L ∧ IsComp (pend b L) ∧ ν (lab (pend b L)) ∧ cost w L = dN w ν b := by
  obtain ⟨L₀, hL₀, hc₀, hν₀⟩ := hne
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hμ0 (cost_ne_top hfin L₀)
  let F := {L : List (K.Tree r × K.Tree r) | PWalk b L ∧ L.length ≤ N ∧ IsComp (pend b L) ∧
    ν (lab (pend b L))}
  have hF : Set.Finite F := (finite_pWalks b N).subset fun L hL => ⟨hL.1, hL.2.1⟩
  have hlen : ∀ L, PWalk b L → cost w L ≤ cost w L₀ → L.length ≤ N := by
    intro L hL hcost
    by_contra hgt
    push Not at hgt
    have h₁ : (N : ℝ≥0∞) * μ ≤ L.length * μ := by gcongr
    exact absurd (hN.trans_le (h₁.trans ((length_mul_le_cost hμ hb hL).trans hcost)))
      (lt_irrefl _)
  have hL₀F : L₀ ∈ F := ⟨hL₀, hlen L₀ hL₀ le_rfl, hc₀, hν₀⟩
  obtain ⟨L, hLF, hmin⟩ := Set.exists_min_image F (cost w) hF ⟨L₀, hL₀F⟩
  refine ⟨L, hLF.1, hLF.2.2.1, hLF.2.2.2, le_antisymm ?_ (dN_le w ν hLF.1 hLF.2.2.1 hLF.2.2.2)⟩
  refine le_sInf ?_
  rintro _ ⟨L', hL', hc', hν', rfl⟩
  by_cases h : cost w L' ≤ cost w L₀
  · exact hmin L' ⟨hL', hlen L' hL' h, hc', hν'⟩
  · push Not at h
    exact (hmin L₀ hL₀F).trans h.le

end Height

lemma Near.below {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}
    {X T : K.Tree r} (h : Near X T) : Below X T := by
  rcases h with ⟨rfl, -⟩ | ⟨hs, hadj⟩
  · exact .inl rfl
  · exact .inr ⟨hs, hadj⟩

section Map

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}
  {Z' : Type u'} [TopologicalSpace Z'] {ι' : Type v'} {K' : CurveConfig Z' ι'} {r' : ι'}
  {ψ : Z → Z'} {h : K.Cover r → K'.Cover r'}

variable (ψ h) in
/-- **Lifting of walks** along `h`: every walk of the target tree from the image of a
non-contracted component vertex `t` lifts to a walk from `t` of no larger weight, ending at a
non-contracted component vertex over its end. -/
def IsWalkLifting (w : Z → ℝ≥0∞) (w' : Z' → ℝ≥0∞) : Prop :=
  ∀ t : K.Tree r, IsComp t → ¬ Contr (K := K) ψ (lab t) →
    ∀ L' : List (K'.Tree r' × K'.Tree r'), PWalk (img h t) L' →
      ∃ L, PWalk t L ∧ cost w L ≤ cost w' L' ∧ IsComp (pend t L) ∧
        ¬ Contr (K := K) ψ (lab (pend t L)) ∧ img h (pend t L) = pend (img h t) L'

variable (hh : Continuous h) (hψ : ∀ x, (h x).1.1 = ψ x.1.1)
  (hNC : ∀ i, ¬ Contr (K := K) ψ i → ∃ i', ψ '' K.C i = K'.C i' ∧ ψ (K.η i) ∉ K'.S)
include hh hψ hNC

omit hh in
lemma isComp_img_of_not_contr {t : K.Tree r} (ht : IsComp t) (hc : ¬ Contr (K := K) ψ (lab t)) :
    IsComp (img h t) := by
  obtain ⟨i, hi⟩ := ht
  rw [lab_of hi] at hc
  obtain ⟨i', hi', -⟩ := map_gen_of_not_contr hψ hNC hi hc
  exact ⟨i', hi'⟩


/-- (Prefix) A walk from a component vertex `b` near (the vertex of) `x` either has all its
components contracted, and then its end has the image of `b`; or it splits at its first
non-contracted component vertex `t₁`, whose image is near the image of `x`. -/
lemma prefix_split (x : K.Cover r) {b : K.Tree r} (hb : Near x.1.2 b)
    {L : List (K.Tree r × K.Tree r)} (hL : PWalk b L) :
    (Contr (K := K) ψ (lab b) ∧ img h (pend b L) = img h b) ∨
    ∃ P R t₁, L = P ++ R ∧ PWalk b P ∧ pend b P = t₁ ∧ IsComp t₁ ∧
      ¬ Contr (K := K) ψ (lab t₁) ∧ Near (h x).1.2 (img h t₁) ∧ PWalk t₁ R := by
  have hbc := hb.isComp
  have hbx : Below (h x).1.2 (img h b) := below_map_gen hh hb
  by_cases hc : Contr (K := K) ψ (lab b)
  · obtain ⟨i₀, hi₀⟩ := hbc
    have hc' := hc
    rw [lab_of hi₀] at hc'
    rcases exists_split (fun p => Contr (K := K) ψ (lab p.2)) L with
      hall | ⟨L₁, ⟨σ, t⟩, L₃, rfl, h₁, hct⟩
    · left
      refine ⟨hc, ?_⟩
      rcases L with _ | ⟨⟨σ₁, t₁⟩, L⟩
      · rfl
      · have e := map_gen_pend_of_contr hh hψ ⟨i₀, hi₀⟩ hL hall
        have hσ₁ := isSpecial_of_adj ⟨i₀, hi₀⟩ hL.1
        have e₀ : h (gen σ₁) = h (gen b) :=
          map_eq_map_gen hh hψ hi₀ hc' (gen_near_of_adj hσ₁ (Tree.adj_comm.1 hL.1))
        rw [img, img, e, e₀]
    · right
      rw [show L₁ ++ (σ, t) :: L₃ = (L₁ ++ [(σ, t)]) ++ L₃ by simp] at hL ⊢
      rw [pWalk_append] at hL
      have hpend : pend b (L₁ ++ [(σ, t)]) = t := by simp [pend_append]
      have hL₂ := hL.2
      rw [hpend] at hL₂
      have ht : IsComp t := by
        have := PWalk.isComp_pend ⟨i₀, hi₀⟩ hL.1
        rwa [hpend] at this
      obtain ⟨σ₁, t₁, M, hSM⟩ : ∃ σ₁ t₁ M, L₁ ++ [(σ, t)] = (σ₁, t₁) :: M := by
        rcases L₁ with _ | ⟨⟨σ₁, t₁⟩, M⟩
        · exact ⟨σ, t, [], rfl⟩
        · exact ⟨σ₁, t₁, M ++ [(σ, t)], rfl⟩
      have hS := hL.1
      rw [hSM] at hS
      have hdl : ((σ₁, t₁) :: M).dropLast = L₁ := by rw [← hSM, List.dropLast_concat]
      obtain ⟨hseg₁, -⟩ := map_gen_seg hh hψ ⟨i₀, hi₀⟩ hS (by rw [hdl]; exact h₁)
      have hσσ₁ : h (gen σ) = h (gen σ₁) := hseg₁ (σ, t) (by rw [← hSM]; simp)
      have hσ₁ := isSpecial_of_adj ⟨i₀, hi₀⟩ hS.1
      have e₀ : h (gen σ₁) = h (gen b) :=
        map_eq_map_gen hh hψ hi₀ hc' (gen_near_of_adj hσ₁ (Tree.adj_comm.1 hS.1))
      have hσ : IsSpecial σ ∧ σ.Adj t := by
        have := hL.1
        rw [pWalk_append] at this
        exact ⟨isSpecial_of_adj (PWalk.isComp_pend ⟨i₀, hi₀⟩ this.1) this.2.1, this.2.2.1⟩
      have hbt : Below (img h b) (img h t) := by
        rw [img, ← e₀, ← hσσ₁]
        exact below_map_gen hh (gen_near_of_adj hσ.1 hσ.2)
      have htc : IsComp (img h t) := isComp_img_of_not_contr hψ hNC ht hct
      refine ⟨L₁ ++ [(σ, t)], L₃, t, rfl, hL.1, hpend, ht, hct, ?_, hL₂⟩
      rcases hbt with hbt | ⟨hsp, hadj⟩
      · rw [← hbt] at htc ⊢
        exact hbx.near htc
      · rw [hbx.eq_of_isSpecial hsp]
        exact .inr ⟨hsp, hadj⟩
  · right
    refine ⟨[], L, b, rfl, trivial, rfl, hbc, hc, ?_, hL⟩
    exact hbx.near (isComp_img_of_not_contr hψ hNC hbc hc)

variable {w : Z → ℝ≥0∞} {w' : Z' → ℝ≥0∞} {ν : ι → Prop} {ν' : ι' → Prop}

omit hh hψ hNC in
/-- Heights do not increase under lifting: the height of a non-contracted component vertex is
at most that of its image. -/
lemma dN_le_dN_img (hl : IsWalkLifting ψ h w w')
    (hν : ∀ t : K.Tree r, IsComp t → ¬ Contr (K := K) ψ (lab t) → ν' (lab (img h t)) →
      ν (lab t))
    {t : K.Tree r} (ht : IsComp t) (hc : ¬ Contr (K := K) ψ (lab t)) :
    dN w ν t ≤ dN w' ν' (img h t) := by
  refine le_sInf ?_
  rintro _ ⟨L', hL', hcomp', hν', rfl⟩
  obtain ⟨L, hL, hcost, hcomp, hc', himg⟩ := hl t ht hc L' hL'
  refine (dN_le w ν hL hcomp (hν _ hcomp hc' ?_)).trans hcost
  rw [himg]
  exact hν'

omit hh hψ hNC in
lemma dN_le_add {t₀ t : K.Tree r} {P : List (K.Tree r × K.Tree r)} (hP : PWalk t₀ P)
    (hend : pend t₀ P = t) : dN w ν t₀ ≤ cost w P + dN w ν t := by
  rw [show dN w ν t = sInf {x | ∃ L, PWalk t L ∧ IsComp (pend t L) ∧ ν (lab (pend t L)) ∧
    cost w L = x} from rfl, ENNReal.add_sInf]
  refine le_iInf₂ fun x ⟨L, hL, hc, hν, hx⟩ => ?_
  rw [← hx, ← cost_append]
  refine dN_le w ν ?_ ?_ ?_
  · rw [pWalk_append, hend]; exact ⟨hP, hL⟩
  · rw [pend_append, hend]; exact hc
  · rw [pend_append, hend]; exact hν

variable (hC' : Function.Injective K'.C) (hw : IsHarmonicWeight K K' ψ w w')
  (hfin : ∀ z, w z ≠ ⊤) (hl : IsWalkLifting ψ h w w')
  (hν : ∀ t : K.Tree r, IsComp t → ¬ Contr (K := K) ψ (lab t) → ν' (lab (img h t)) → ν (lab t))
include hC' hw hfin hl hν

/-- **Monotonicity of the height-corrected length condition** along a map of tree coverings
with harmonic weights and lifting of walks. -/
theorem hc_map (x y : K.Cover r) (ℓ : ℝ≥0∞) (H : HC w ν x.1.2 y.1.2 ℓ) :
    HC w' ν' (h x).1.2 (h y).1.2 ℓ := by
  obtain ⟨b, b', L, hb, hb', hL, hend, hcost⟩ := H
  rcases prefix_split hh hψ hNC x hb hL with ⟨-, himg⟩ | ⟨P, R, t₁, rfl, hP, hPe, ht₁, hc₁, hn₁, hR⟩
  · -- degenerate: everything maps below the image of `b`
    have hy : Below (h y).1.2 (img h b) := by
      rw [← himg, hend]; exact below_map_gen hh hb'
    exact hc_of_below w' ν' (below_map_gen hh hb) hy ℓ
  · -- reverse the rest of the walk, from `b'`
    rw [pWalk_append, hPe] at hL
    have hRend : pend t₁ R = b' := by rw [← hend, pend_append, hPe]
    obtain ⟨hRr, hRre⟩ := hR.prev
    rw [hRend] at hRr hRre
    rcases prefix_split hh hψ hNC y hb' hRr with ⟨hcb', himg'⟩ |
      ⟨P₃, R₃, t₃, hsplit, hP₃, hP₃e, ht₃, hc₃, hn₃, hR₃⟩
    · -- the reversed walk only meets contracted components: both ends map near `img t₁`
      have hy : Below (h y).1.2 (img h t₁) := by
        rw [← hRre, himg']; exact below_map_gen hh hb'
      exact hc_of_below w' ν' hn₁.below hy ℓ
    · have hR₃e : pend t₃ R₃ = t₁ := by rw [← hRre, hsplit, pend_append, hP₃e]
      -- the image of the middle walk
      obtain ⟨Y', M', hY', hM', hMend, hMcost⟩ :=
        exists_walk_img hh hψ hNC hC' hw ht₃ hc₃ hR₃ (img h t₁) (by rw [hR₃e]; exact .inl rfl)
      have hY'eq : Y' = img h t₁ := by
        rcases hY' with ⟨rfl, -⟩ | ⟨hsp, -⟩
        · rfl
        · exact absurd (isComp_img_of_not_contr hψ hNC ht₁ hc₁)
            (not_isComp_of_isSpecial hsp)
      subst hY'eq
      obtain ⟨hMr, hMre⟩ := hM'.prev
      rw [hMend] at hMr hMre
      refine ⟨img h t₁, img h t₃, prev (img h t₃) M', hn₁, hn₃, hMr, hMre, ?_⟩
      rw [cost_prev]
      -- the arithmetic
      have hd₁ : dN w ν b ≤ cost w P + dN w' ν' (img h t₁) :=
        (dN_le_add hP hPe).trans (add_le_add_right (dN_le_dN_img hl hν ht₁ hc₁) _)
      have hd₃ : dN w ν b' ≤ cost w P₃ + dN w' ν' (img h t₃) :=
        (dN_le_add hP₃ hP₃e).trans (add_le_add_right (dN_le_dN_img hl hν ht₃ hc₃) _)
      have hcR : cost w R = cost w P₃ + cost w R₃ := by
        rw [← cost_prev w t₁ R, hsplit, cost_append]
      rw [cost_append, hcR] at hcost
      have key : cost w P + cost w P₃ + cost w R₃ ≤
          cost w P + cost w P₃ + (ℓ + dN w' ν' (img h t₁) + dN w' ν' (img h t₃)) := by
        calc cost w P + cost w P₃ + cost w R₃ = cost w P + (cost w P₃ + cost w R₃) := by
              rw [add_assoc]
          _ ≤ ℓ + dN w ν b + dN w ν b' := hcost
          _ ≤ ℓ + (cost w P + dN w' ν' (img h t₁)) + (cost w P₃ + dN w' ν' (img h t₃)) :=
              by gcongr
          _ = _ := by ring
      exact hMcost.trans (ENNReal.le_of_add_le_add_left
        (ENNReal.add_ne_top.2 ⟨cost_ne_top hfin P, cost_ne_top hfin P₃⟩) key)

end Map

section Lift

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

/-- **Lifting walks of the incidence graph to the tree**: a walk of the incidence graph from the
label of a component vertex `t` is the labelled walk of a walk of the tree from `t`. -/
lemma exists_pWalk_labW : ∀ {t : K.Tree r} (L : List (Z × ι)), IsComp t → IncWalk K (lab t) L →
    ∃ T, PWalk t T ∧ labW T = L
  | _, [], _, _ => ⟨[], trivial, rfl⟩
  | t, (s, j) :: L, ⟨i, hi⟩, ⟨hS, hsi, hsj, hL⟩ => by
    rw [lab_of hi] at hsi
    let σ := t.nbr hi (v := .inr s) ⟨hS, hsi⟩
    have hσ : σ.1.head? = some (.inr s) := t.nbr_head hi _
    let t' := σ.nbr hσ (v := .inl j) ⟨hS, hsj⟩
    have ht' : t'.1.head? = some (.inl j) := σ.nbr_head hσ _
    obtain ⟨T, hT, hTL⟩ := exists_pWalk_labW (t := t') L ⟨j, ht'⟩ (by rw [lab_of ht']; exact hL)
    refine ⟨(σ, t') :: T, ⟨t.adj_nbr hi _, σ.adj_nbr hσ _, hT⟩, ?_⟩
    simp only [labW, List.map_cons] at hTL ⊢
    rw [hTL, spt_of hσ, lab_of ht']

lemma eq_of_adj_of_head {t a b : K.Tree r} (ha : t.Adj a) (hb : t.Adj b) {v : ι ⊕ Z}
    (hav : a.1.head? = some v) (hbv : b.1.head? = some v) : a = b := by
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · have hadj : K.Adj (.inl i) v := adj_head t.2 a.2 ha hi hav
    exact (Tree.eq_nbr ha hi hadj hav).trans (Tree.eq_nbr hb hi hadj hbv).symm
  · have hadj : K.Adj (.inr s) v := adj_head t.2 a.2 ha hs hav
    exact (Tree.eq_nbr ha hs hadj hav).trans (Tree.eq_nbr hb hs hadj hbv).symm

variable {Z' : Type u'} [TopologicalSpace Z'] {ι' : Type v'} {K' : CurveConfig Z' ι'} {r' : ι'}
  {ψ : Z → Z'} {h : K.Cover r → K'.Cover r'}

variable (K K' ψ) in
/-- **Edge lifting with lengths** along `ψ` ((X1) of `HarmonicX`): for every special point `y'`
of `K'` on two components `C' a ≠ C' b` and every non-contracted component `C i₀` mapped onto
`C' a`, a walk of the incidence graph from `i₀` crosses `y'` (special points over `y'`, inner
components contracted to `y'`) to a non-contracted component mapped onto `C' b`, with weight at
most `w' y'`. -/
def IsEdgeLifting (w : Z → ℝ≥0∞) (w' : Z' → ℝ≥0∞) : Prop :=
  ∀ (i₀ : ι) (y' : Z') (a b : ι'), ¬ Contr (K := K) ψ i₀ → ψ '' K.C i₀ = K'.C a → a ≠ b →
    y' ∈ K'.S → y' ∈ K'.C a → y' ∈ K'.C b →
    ∃ L : List (Z × ι), IncWalk K i₀ L ∧ (∀ p ∈ L, ψ p.1 = y') ∧
      (∀ p ∈ L.dropLast, ψ '' K.C p.2 = {y'}) ∧ ¬ Contr (K := K) ψ (lastLab i₀ L) ∧
      ψ '' K.C (lastLab i₀ L) = K'.C b ∧ (L.map fun p => w p.1).sum ≤ w' y'

variable (hh : Continuous h) (hψ : ∀ x, (h x).1.1 = ψ x.1.1)
  (hNC : ∀ i, ¬ Contr (K := K) ψ i → ∃ i', ψ '' K.C i = K'.C i' ∧ ψ (K.η i) ∉ K'.S)
  (hC' : Function.Injective K'.C) {w : Z → ℝ≥0∞} {w' : Z' → ℝ≥0∞}
  (hw : IsHarmonicWeight K K' ψ w w')
include hh hψ hNC hC' hw

/-- **Walk lifting from edge lifting**: (X1) for the incidence graphs gives lifting of walks of
the tree coverings. -/
theorem isWalkLifting_of_isEdgeLifting (he : IsEdgeLifting K K' ψ w w') :
    IsWalkLifting ψ h w w' := by
  intro t ht hc L' hL'
  induction L' generalizing t with
  | nil => exact ⟨[], trivial, le_rfl, ht, hc, rfl⟩
  | cons p rest ih =>
    obtain ⟨σ', t'⟩ := p
    obtain ⟨h₁, h₂, h₃⟩ := hL'
    obtain ⟨i, hi⟩ := ht
    have hc' := hc
    rw [lab_of hi] at hc'
    obtain ⟨a, ha, hia⟩ := map_gen_of_not_contr hψ hNC hi hc'
    -- `σ'` is the special vertex over `y'`, `t'` the component vertex over `b`
    obtain ⟨y', hy', hy'S, hy'a⟩ := head_inr_of_adj (img h t).2 σ'.2 h₁ ha
    obtain ⟨b, hb, -, hy'b⟩ := head_inl_of_adj σ'.2 t'.2 h₂ hy'
    by_cases hab : a = b
    · -- backtracking: `t' = img h t`
      subst hab
      have ht'eq : t' = img h t :=
        eq_of_adj_of_head h₂ (Tree.adj_comm.1 h₁) hb ha
      rw [ht'eq] at h₃
      obtain ⟨L, hL, hcost, hcomp, hcL, himg⟩ := ih t ⟨i, hi⟩ hc h₃
      refine ⟨L, hL, hcost.trans ?_, hcomp, hcL, ?_⟩
      · rw [cost_cons]; exact le_add_self
      · rw [himg, pend_cons, ht'eq]
    · obtain ⟨L, hL, hLy, hLc, hlc, hlb, hLw⟩ :=
        he i y' a b hc' hia hab hy'S hy'a hy'b
      obtain ⟨T, hT, hTL⟩ := exists_pWalk_labW (t := t) L ⟨i, hi⟩ (by rw [lab_of hi]; exact hL)
      have hlab : lab (pend t T) = lastLab i L := by rw [← lab_of hi, ← lastLab_labW, hTL]
      have hTne : T ≠ [] := by
        rintro rfl
        subst hTL
        exact hab (hC' (hia.symm.trans hlb))
      obtain ⟨S, ⟨σ, te⟩, hST⟩ := List.eq_nil_or_concat T |>.resolve_left hTne
      rw [List.concat_eq_append] at hST
      subst hST
      have hte : pend t (S ++ [(σ, te)]) = te := by simp [pend_append]
      have htec : IsComp te := by
        have := PWalk.isComp_pend ⟨i, hi⟩ hT; rwa [hte] at this
      have hlte : ¬ Contr (K := K) ψ (lab te) := by rw [← hte, hlab]; exact hlc
      have hSc : ∀ p ∈ S, Contr (K := K) ψ (lab p.2) := fun p hp => by
        have hmem : (spt p.1, lab p.2) ∈ L.dropLast := by
          rw [← hTL, labW, List.map_dropLast.symm, List.dropLast_concat]
          exact List.mem_map_of_mem hp
        exact ⟨y', hLc _ hmem⟩
      obtain ⟨b', hb', hib'⟩ := map_gen_of_not_contr hψ hNC (i := lab te)
        (by obtain ⟨j, hj⟩ := htec; rw [lab_of hj]; exact hj) hlte
      have hbb : b' = b := hC' (hib'.symm.trans (by rw [← hte, hlab]; exact hlb))
      subst hbb
      have hne : img h t ≠ img h te := by
        intro e
        have e' : (h (gen te)).1.2.1.head? = (h (gen t)).1.2.1.head? := by
          change (img h te).1.head? = (img h t).1.head?
          rw [e]
        rw [hb', ha] at e'
        exact hab (by simpa using e'.symm)
      obtain ⟨hsp, hadj₀, hadj₁, -⟩ :=
        cross_le hh hψ hNC hC' hw ⟨i, hi⟩ (by rw [lab_of hi]; exact hc') hT hSc hlte hne
      -- the image of `σ` is `σ'`
      have hσy : (h (gen σ)).1.1 = y' := by
        rw [hψ]
        have hmem : (spt σ, lab te) ∈ L := by
          rw [← hTL, labW, List.map_append]; simp
        exact hLy _ hmem
      have hhead : (h (gen σ)).1.2.1.head? = some (.inr y') := by
        obtain ⟨s', hs'⟩ := hsp
        rw [hs', ← hσy, Cover.eq_of_inr hs']
      have hσ' : (h (gen σ)).1.2 = σ' :=
        eq_of_adj_of_head (Tree.adj_comm.1 hadj₀) h₁ hhead hy'
      rw [hσ'] at hadj₁
      have hte' : img h te = t' := eq_of_adj_of_head hadj₁ h₂ hb' hb
      obtain ⟨L₂, hL₂, hcost₂, hcomp₂, hc₂, himg₂⟩ := ih te htec hlte (by rw [hte']; exact h₃)
      refine ⟨S ++ [(σ, te)] ++ L₂, ?_, ?_, ?_, ?_, ?_⟩
      · rw [pWalk_append, hte]; exact ⟨hT, hL₂⟩
      · rw [cost_append, cost_cons, tw_of_inr w' hy']
        refine add_le_add ?_ hcost₂
        rw [← sum_labW w ⟨i, hi⟩ hT, hTL]
        exact hLw
      · rw [pend_append, hte]; exact hcomp₂
      · rw [pend_append, hte]; exact hc₂
      · rw [pend_append, hte, himg₂, hte', pend_cons]

end Lift

end CurveConfig

end TemperedFundamentalGroups
