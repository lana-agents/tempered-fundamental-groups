/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CrossingZero

/-!
# The crossing walk (Blueprint §10.3.8, CrossingX1, CX8)

`exists_walk`: the walk assembly of `Statement.CrossingX1` on the source side. Starting from a
component `v₀` of position `0` (`W(t) = 1`) and a point `z₀ ∈ v₀` over `y'` at which `t`
vanishes, repeat the crossing step (`step`, `exists_zero`): the positions `p` with
`W(t) = W(ϖ) ^ p` strictly increase and are bounded by `N`, components of position `< N` are
contracted to `y'`, and a component of position `N` lies over `w₂'`. Nodes are distinct because
at most two components pass through a node (`two_components`) and positions increase.

The target side enters only through the hypotheses `hM`, `hbound`, `hcontr`, `hend`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode

section Snoc

variable {R : Type u} [CommRing R] [IsLocalRing R] {c : TemperedFundamentalGroups.ModelCode R}

/-- Append an edge to a walk. -/
def snoc (w : Walk c) (z : c.scheme) (v' : Set c.scheme) (hv' : v' ∈ components c)
    (hj : Joins c z (w.v (Fin.last w.k)) v') : Walk c where
  k := w.k + 1
  v := Fin.snoc (α := fun _ ↦ Set c.scheme) w.v v'
  x := Fin.snoc (α := fun _ ↦ c.scheme) w.x z
  mem_components i := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simpa using hv'
    · simpa using w.mem_components i
  joins i := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simpa [Fin.succ_last] using hj
    · have e : (Fin.castSucc i).succ = i.succ.castSucc := Fin.succ_castSucc i
      change Joins c (Fin.snoc (α := fun _ ↦ c.scheme) w.x z i.castSucc)
        (Fin.snoc (α := fun _ ↦ Set c.scheme) w.v v' i.castSucc.castSucc)
        (Fin.snoc (α := fun _ ↦ Set c.scheme) w.v v' i.castSucc.succ)
      rw [e]
      simp only [Fin.snoc_castSucc]
      exact w.joins i

variable (w : Walk c) (z : c.scheme) (v' : Set c.scheme) (hv' : v' ∈ components c)
  (hj : Joins c z (w.v (Fin.last w.k)) v')

@[simp] lemma snoc_v_castSucc (i : Fin (w.k + 1)) : (snoc w z v' hv' hj).v i.castSucc = w.v i :=
  Fin.snoc_castSucc (α := fun _ ↦ Set c.scheme) _ _ _

@[simp] lemma snoc_v_last : (snoc w z v' hv' hj).v (Fin.last (w.k + 1)) = v' :=
  Fin.snoc_last (α := fun _ ↦ Set c.scheme) _ _

@[simp] lemma snoc_x_castSucc (i : Fin w.k) : (snoc w z v' hv' hj).x i.castSucc = w.x i :=
  Fin.snoc_castSucc (α := fun _ ↦ c.scheme) _ _ _

@[simp] lemma snoc_x_last : (snoc w z v' hv' hj).x (Fin.last w.k) = z :=
  Fin.snoc_last (α := fun _ ↦ c.scheme) _ _

lemma snoc_v_zero : (snoc w z v' hv' hj).v 0 = w.v 0 :=
  snoc_v_castSucc w z v' hv' hj 0

/-- The walk consisting of one component. -/
def single (v₀ : Set c.scheme) (hv₀ : v₀ ∈ components c) : Walk c where
  k := 0
  v := fun _ ↦ v₀
  x := Fin.elim0
  mem_components := fun _ ↦ hv₀
  joins := fun i ↦ i.elim0

end Snoc

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [Algebra O L] [IsScalarTower O K L] {x : L}
  {c : TemperedFundamentalGroups.ModelCode O} {j : Spec (CommRingCat.of L) ⟶ c.scheme}
  (hW : IsWModel O L x c j)

omit [IsDiscreteValuationRing O] in
lemma Wc_congr {v v' : Set c.scheme} (hv : v ∈ components c) (hv' : v' ∈ components c)
    (h : v = v') : Wc hW hv = Wc hW hv' := by
  subst h; rfl

/-- **The crossing walk.** -/
theorem exists_walk {ϖ : O} (hϖ : Irreducible ϖ) (hsplit : HasSplitNodes ϖ c)
    (hloops : NoLoops c) {R₂ : Type u} [CommRing R₂] {c' : TemperedFundamentalGroups.ModelCode R₂}
    (ψ : c.scheme ⟶ c'.scheme) (y' : c'.scheme) (w₂' : Set c'.scheme) (t : L) (N : ℕ)
    (hN : 0 < N)
    (hM : ∀ z, ψ z = y' → t ∈ germs c j z ∧ ∃ r ∈ germs c j z, t * r = algebraMap O L ϖ ^ N)
    (hbound : ∀ (v : Set c.scheme) (hv : v ∈ components c) (W : ValuationSubring L),
      IsCentre j W (gp hv) → ∀ z ∈ v, ψ z = y' → ∀ p : ℕ,
        W.valuation t = W.valuation (algebraMap O L ϖ) ^ p → p ≤ N)
    (hcontr : ∀ (v : Set c.scheme) (hv : v ∈ components c) (W : ValuationSubring L),
      IsCentre j W (gp hv) → ∀ z ∈ v, ψ z = y' → ∀ p : ℕ,
        W.valuation t = W.valuation (algebraMap O L ϖ) ^ p → 0 < p → p < N → ψ '' v = {y'})
    (hend : ∀ (v : Set c.scheme) (hv : v ∈ components c) (W : ValuationSubring L),
      IsCentre j W (gp hv) → ∀ z ∈ v, ψ z = y' →
        W.valuation t = W.valuation (algebraMap O L ϖ) ^ N → ψ '' v = w₂')
    (hw₂ : ∀ y, w₂' ≠ {y}) {v₀ : Set c.scheme} (hv₀ : v₀ ∈ components c)
    (hv₀c : ¬ IsContracted' ψ v₀)
    (hstart : (Wc hW hv₀).valuation t = 1) {z₀ : c.scheme} (hz₀ : z₀ ∈ v₀) (hψz₀ : ψ z₀ = y')
    (hR₀ : ∀ R : ValuationSubring L, IsCentre j R z₀ → R.valuation t < 1) :
    ∃ w : Walk c, w.v 0 = v₀ ∧ w.Crosses ψ y' ∧ ψ '' w.v (Fin.last w.k) = w₂' ∧
    (∀ i : Fin w.k, ∃ q q' : ℕ, q < q' ∧
      (Wc hW (w.mem_components i.castSucc)).valuation t =
        (Wc hW (w.mem_components i.castSucc)).valuation (algebraMap O L ϖ) ^ q ∧
      (Wc hW (w.mem_components i.succ)).valuation t =
        (Wc hW (w.mem_components i.succ)).valuation (algebraMap O L ϖ) ^ q') := by
  set ϖL := algebraMap O L ϖ
  let Inv : Walk c → ℕ → Prop := fun w p ↦
    w.v 0 = v₀ ∧ Function.Injective w.x ∧ (∀ i, ψ (w.x i) = y') ∧
    (∀ i : Fin (w.k + 1), i ≠ 0 → ψ '' w.v i = {y'}) ∧
    (∀ i : Fin w.k, w.v i.castSucc ≠ w.v i.succ) ∧
    (∀ i, ∃ q ≤ p, (Wc hW (w.mem_components i)).valuation t =
      (Wc hW (w.mem_components i)).valuation ϖL ^ q) ∧
    (Wc hW (w.mem_components (Fin.last w.k))).valuation t =
      (Wc hW (w.mem_components (Fin.last w.k))).valuation ϖL ^ p ∧
    (∃ z ∈ w.v (Fin.last w.k), ψ z = y' ∧
      ∃ R : ValuationSubring L, IsCentre j R z ∧ R.valuation (t / ϖL ^ p) < 1) ∧ p < N ∧
    (∀ i : Fin w.k, ∃ q q' : ℕ, q < q' ∧
      (Wc hW (w.mem_components i.castSucc)).valuation t =
        (Wc hW (w.mem_components i.castSucc)).valuation (ϖL) ^ q ∧
      (Wc hW (w.mem_components i.succ)).valuation t =
        (Wc hW (w.mem_components i.succ)).valuation (ϖL) ^ q')
  have hϖ0 : ϖL ≠ 0 := by
    rw [show ϖL = algebraMap K L (ϖ : K) from IsScalarTower.algebraMap_apply O K L ϖ]
    exact (map_ne_zero _).2 fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hWϖ : ∀ {v} (hv : v ∈ components c), (Wc hW hv).valuation ϖL < 1 := fun hv ↦
    valuation_ϖ_lt_one hW hϖ (hv.2.1 (gp_mem hv)) (Wc_spec hW hv)
  have key : ∀ k, ∀ (w : Walk c) (p : ℕ), Inv w p → N - p = k →
      ∃ w : Walk c, w.v 0 = v₀ ∧ w.Crosses ψ y' ∧ ψ '' w.v (Fin.last w.k) = w₂' ∧
      (∀ i : Fin w.k, ∃ q q' : ℕ, q < q' ∧
      (Wc hW (w.mem_components i.castSucc)).valuation t =
        (Wc hW (w.mem_components i.castSucc)).valuation (ϖL) ^ q ∧
      (Wc hW (w.mem_components i.succ)).valuation t =
        (Wc hW (w.mem_components i.succ)).valuation (ϖL) ^ q') := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro w p ⟨hstart', hinj, hnodes, hinner, hdist, hpos, hlast, ⟨z, hz, hψz, R, hRz, hR⟩, hpN,
      hinc⟩ hk
    have hvl := w.mem_components (Fin.last w.k)
    obtain ⟨htz, hMz⟩ := hM z hψz
    obtain ⟨hnode, v', hv', hv'ne, hzv', hW'⟩ :=
      step hW hϖ hsplit hloops hvl (Wc_spec hW hvl) hlast hz htz hMz hRz hR
    obtain ⟨p', hpp', hW't, hpole⟩ := hW' _ (Wc_spec hW hv')
    have hp'N := hbound v' hv' _ (Wc_spec hW hv') z hzv' hψz p' hW't
    have hjoin : Joins c z (w.v (Fin.last w.k)) v' := ⟨hnode, hz, hzv', .inl hv'ne.symm⟩
    -- the new node is new
    have hznew : ∀ i : Fin w.k, w.x i ≠ z := by
      intro i hi
      have hA := w.joins i
      rw [hi] at hA
      have hpos_ne : ∀ i', w.v i' ≠ v' := fun i' h ↦ by
        obtain ⟨q, hq, hq'⟩ := hpos i'
        rw [Wc_congr hW _ hv' h, hW't] at hq'
        have := pow_inj (by simpa using hϖ0) (hWϖ hv') hq'
        omega
      rcases two_components hW hϖ hsplit hloops hnode hv' (w.mem_components i.castSucc)
          (w.mem_components i.succ) hzv' hA.2.1 hA.2.2.1 with h | h | h
      · exact hpos_ne _ h.symm
      · exact hpos_ne _ h.symm
      · exact hdist i h
    set w' := snoc w z v' hv' hjoin
    have hinj' : Function.Injective w'.x := by
      intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b =>
          change w'.x (Fin.last w.k) = w'.x b.castSucc at hab
          rw [snoc_x_last, snoc_x_castSucc] at hab
          exact absurd hab.symm (hznew b)
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          change w'.x a.castSucc = w'.x (Fin.last w.k) at hab
          rw [snoc_x_last, snoc_x_castSucc] at hab
          exact absurd hab (hznew a)
        | cast b =>
          change w'.x a.castSucc = w'.x b.castSucc at hab
          rw [snoc_x_castSucc, snoc_x_castSucc] at hab
          rw [hinj hab]
    have hnodes' : ∀ i, ψ (w'.x i) = y' := fun i ↦ by
      induction i using Fin.lastCases with
      | last => rw [snoc_x_last]; exact hψz
      | cast i => rw [snoc_x_castSucc]; exact hnodes i
    have hstart'' : w'.v 0 = v₀ := by rw [snoc_v_zero]; exact hstart'
    have hold : ∀ i : Fin (w.k + 1), i ≠ 0 → ψ '' w'.v i.castSucc = {y'} := fun i hi ↦ by
      rw [snoc_v_castSucc]; exact hinner i hi
    have hinc' : (∀ i : Fin w'.k, ∃ q q' : ℕ, q < q' ∧
        (Wc hW (w'.mem_components i.castSucc)).valuation t =
          (Wc hW (w'.mem_components i.castSucc)).valuation (ϖL) ^ q ∧
        (Wc hW (w'.mem_components i.succ)).valuation t =
          (Wc hW (w'.mem_components i.succ)).valuation (ϖL) ^ q') := by
      have congrv : ∀ (u u' : Set c.scheme) (hu : u ∈ components c) (hu' : u' ∈ components c),
          u = u' → ∀ q : ℕ, (Wc hW hu').valuation t = (Wc hW hu').valuation ϖL ^ q →
            (Wc hW hu).valuation t = (Wc hW hu).valuation ϖL ^ q := by
        rintro u _ hu hu' rfl q hq; exact hq
      intro i
      induction i using Fin.lastCases with
      | last =>
        refine ⟨p, p', hpp', congrv _ _ _ (w.mem_components (Fin.last w.k)) ?_ p hlast,
          congrv _ _ _ hv' ?_ p' hW't⟩
        · change w'.v (Fin.last w.k).castSucc = w.v (Fin.last w.k)
          exact snoc_v_castSucc w z v' hv' hjoin _
        · change w'.v (Fin.last (w.k + 1)) = v'
          exact snoc_v_last w z v' hv' hjoin
      | cast i =>
        obtain ⟨q, q', hqq, h1, h2⟩ := hinc i
        refine ⟨q, q', hqq, congrv _ _ _ (w.mem_components i.castSucc) ?_ q h1,
          congrv _ _ _ (w.mem_components i.succ) ?_ q' h2⟩
        · change w'.v i.castSucc.castSucc = w.v i.castSucc
          exact snoc_v_castSucc w z v' hv' hjoin _
        · change w'.v i.castSucc.succ = w.v i.succ
          rw [Fin.succ_castSucc]
          exact snoc_v_castSucc w z v' hv' hjoin _
    have hg : (Wc hW hv').valuation (t / ϖL ^ p') = 1 := by
      rw [map_div₀, hW't, map_pow, div_self (pow_ne_zero _ (by simpa using hϖ0))]
    have key1 : ∀ (u : Set c.scheme) (hu : u ∈ components c), u = v' →
        (Wc hW hu).valuation t = (Wc hW hu).valuation ϖL ^ p' := by
      rintro u hu rfl; exact hW't
    rcases hp'N.lt_or_eq with hlt | heq
    · -- `v'` is contracted: continue
      have hcon := hcontr v' hv' _ (Wc_spec hW hv') z hzv' hψz p' hW't (by omega) hlt
      obtain ⟨z'', hz'', R'', hR''z, hR''⟩ :=
        exists_zero hW hϖ hv' (Wc_spec hW hv') hg hzv' hpole
      have hψz'' : ψ z'' = y' := by
        have : ψ z'' ∈ ψ '' v' := ⟨z'', hz'', rfl⟩
        rw [hcon] at this; exact this
      have hz''' : z'' ∈ w'.v (Fin.last w'.k) := by
        change z'' ∈ w'.v (Fin.last (w.k + 1)); rw [snoc_v_last]; exact hz''
      refine ih (N - p') (by omega) w' p' ⟨hstart'', hinj', hnodes', fun i hi ↦ ?_, fun i ↦ ?_,
        fun i ↦ ?_, ?_, ⟨z'', hz''', hψz'', R'', hR''z, hR''⟩, hlt, hinc'⟩ rfl
      · induction i using Fin.lastCases with
        | last => change ψ '' w'.v (Fin.last (w.k + 1)) = {y'}; rw [snoc_v_last]; exact hcon
        | cast i => exact hold i (fun h ↦ hi (by rw [h]; rfl))
      · induction i using Fin.lastCases with
        | last =>
          change w'.v (Fin.last w.k).castSucc ≠ w'.v (Fin.last (w.k + 1))
          rw [snoc_v_castSucc, snoc_v_last]; exact hv'ne.symm
        | cast i =>
          change w'.v i.castSucc.castSucc ≠ w'.v i.castSucc.succ
          rw [Fin.succ_castSucc, snoc_v_castSucc, snoc_v_castSucc]; exact hdist i
      · induction i using Fin.lastCases with
        | last => exact ⟨p', le_rfl, key1 _ _ (snoc_v_last w z v' hv' hjoin)⟩
        | cast i =>
          obtain ⟨q, hq, hq'⟩ := hpos i
          have keyq : ∀ (u : Set c.scheme) (hu : u ∈ components c), u = w.v i →
              (Wc hW hu).valuation t = (Wc hW hu).valuation ϖL ^ q := by
            rintro u hu rfl; exact hq'
          exact ⟨q, by omega, keyq _ _ (snoc_v_castSucc w z v' hv' hjoin i)⟩
      · exact key1 _ _ (snoc_v_last w z v' hv' hjoin)
    · -- `v'` lies over `w₂'`: done
      subst heq
      have hend' := hend v' hv' _ (Wc_spec hW hv') z hzv' hψz hW't
      refine ⟨w', hstart'', ⟨by simp [w', snoc], hinj', ?_, ?_, fun i hi hi' ↦ ?_, hnodes'⟩, ?_,
        hinc'⟩
      · rw [hstart'']; exact hv₀c
      · rintro ⟨y, hy⟩
        change ψ '' w'.v (Fin.last (w.k + 1)) = {y} at hy
        rw [snoc_v_last, hend'] at hy
        exact hw₂ y hy
      · induction i using Fin.lastCases with
        | last => exact absurd rfl hi'
        | cast i => exact hold i (fun h ↦ hi (by rw [h]; rfl))
      · change ψ '' w'.v (Fin.last (w.k + 1)) = w₂'
        rw [snoc_v_last]; exact hend'
  -- the start
  obtain ⟨R₀, hR₀z⟩ := exists_isCentre j (specializes_of_isWModel hW z₀)
  refine key (N - 0) (single v₀ hv₀) 0 ⟨rfl, fun a ↦ a.elim0, fun a ↦ a.elim0, fun i hi ↦
    (hi (Fin.ext (by have := i.2; change i.1 < 1 at this; change i.1 = 0; omega))).elim,
    fun a ↦ a.elim0, fun i ↦ ⟨0, le_rfl, ?_⟩, ?_,
    ⟨z₀, hz₀, hψz₀, R₀, hR₀z, ?_⟩, hN, fun a ↦ a.elim0⟩ rfl
  · rw [pow_zero]; exact hstart
  · rw [pow_zero]; exact hstart
  · rw [pow_zero, div_one]; exact hR₀ R₀ hR₀z

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
