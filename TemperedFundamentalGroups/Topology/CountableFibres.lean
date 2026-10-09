/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Fibres of connected coverings of noetherian spaces are countable

Let `p : E → Z` be a covering map onto a noetherian topological space `Z`. We show that every
preconnected subset of `E` meets every fibre of `p` in a countable set
(`IsCoveringMap.countable_inter_fibre_of_isPreconnected`). In particular the fibres of a
covering with connected total space are countable (`IsCoveringMap.countable_fibre`), and so are
the fibres of the restriction of `p` to a connected component of `E`
(`IsCoveringMap.countable_connectedComponent_inter_fibre`).

The proof: `Z` is quasi-compact, so finitely many evenly covered opens `U_w` cover `Z`. The sheets
over the `U_w` form an open cover of `E` in which each sheet meets only finitely many other sheets
(the intersection of a sheet over `U_w` with the preimage of `U_{w'}` is homeomorphic to the
compact space `U_w ∩ U_{w'}`, so it meets only finitely many sheets over `U_{w'}`), and each sheet
meets each fibre in at most one point. A chain argument (`countable_inter_of_isPreconnected`)
finishes the proof.
-/

open Set TopologicalSpace

/-- Let `S` be an open cover of `E` in which each member meets only finitely many members, and
let `F ⊆ E` meet each member of the cover in a finite set. Then every preconnected subset of `E`
meets `F` in a countable set. -/
theorem countable_inter_of_isPreconnected {E ι : Type*} [TopologicalSpace E]
    (S : ι → Set E) (hS : ∀ i, IsOpen (S i)) (hcov : ∀ x, ∃ i, x ∈ S i)
    (hfin : ∀ i, {j | (S i ∩ S j).Nonempty}.Finite) {F : Set E} (hF : ∀ i, (S i ∩ F).Finite)
    {C : Set E} (hC : IsPreconnected C) : (C ∩ F).Countable := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  obtain ⟨i₀, hi₀⟩ := hcov x₀
  let I : ℕ → Set ι := fun n ↦
    Nat.rec {i₀} (fun _ s ↦ ⋃ i ∈ s, {j | (S i ∩ S j).Nonempty}) n
  have hIsucc (n : ℕ) : I (n + 1) = ⋃ i ∈ I n, {j | (S i ∩ S j).Nonempty} := rfl
  have hI (n : ℕ) : (I n).Finite := by
    induction n with
    | zero => exact finite_singleton _
    | succ n ih => rw [hIsucc]; exact ih.biUnion fun i _ ↦ hfin i
  let W := ⋃ n, ⋃ i ∈ I n, S i
  have hWo : IsOpen W := isOpen_iUnion fun n ↦ isOpen_biUnion fun i _ ↦ hS i
  have hWc : IsClosed W := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨j, hj⟩ := hcov x
    refine ⟨S j, fun y hy hyW ↦ hx ?_, hS j, hj⟩
    simp only [W, mem_iUnion] at hyW ⊢
    obtain ⟨n, i, hi, hyi⟩ := hyW
    exact ⟨n + 1, j, by rw [hIsucc]; exact mem_biUnion hi ⟨y, hyi, hy⟩, hj⟩
  have hCW : C ⊆ W := hC.subset_isClopen ⟨hWc, hWo⟩
    ⟨x₀, hx₀, mem_iUnion.2 ⟨0, mem_biUnion (mem_singleton i₀) hi₀⟩⟩
  have hsub : C ∩ F ⊆ ⋃ n, ⋃ i ∈ I n, S i ∩ F := by
    rintro x ⟨hxC, hxF⟩
    have := hCW hxC
    simp only [W, mem_iUnion] at this ⊢
    obtain ⟨n, i, hi, hx⟩ := this
    exact ⟨n, i, hi, hx, hxF⟩
  exact (countable_iUnion fun n ↦ ((hI n).biUnion fun i _ ↦ hF i).countable).mono hsub

/-- A preconnected subset of the total space of a covering of a noetherian space meets every
fibre in a countable set. -/
theorem IsCoveringMap.countable_inter_fibre_of_isPreconnected {E Z : Type*} [TopologicalSpace E]
    [TopologicalSpace Z] [NoetherianSpace Z] {p : E → Z} (hp : IsCoveringMap p) {C : Set E}
    (hC : IsPreconnected C) (z : Z) : (C ∩ p ⁻¹' {z}).Countable := by
  choose hd U hzU hU hpU H hH using hp
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U (fun w ↦ hU w)
    (fun w _ ↦ mem_iUnion.2 ⟨w, hzU w⟩)
  let S : (Σ w : T, p ⁻¹' {w.1}) → Set E := fun j ↦
    Subtype.val '' ((fun y ↦ (H j.1 y).2) ⁻¹' {j.2})
  have mem_S {j : Σ w : T, p ⁻¹' {w.1}} {x : E} :
      x ∈ S j ↔ ∃ hx : p x ∈ U j.1, (H j.1 ⟨x, hx⟩).2 = j.2 := by
    simp [S]
  refine countable_inter_of_isPreconnected S (fun j ↦ ?_) (fun x ↦ ?_) (fun j ↦ ?_)
    (fun j ↦ ?_) hC
  · have := hd j.1.1
    exact (hpU j.1).isOpenMap_subtype_val _ <|
      (isOpen_discrete {j.2}).preimage (continuous_snd.comp (H j.1).continuous)
  · obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.1 (hT (mem_univ (p x)))
    exact ⟨⟨⟨w, hw⟩, (H w ⟨x, hxw⟩).2⟩, mem_S.2 ⟨hxw, rfl⟩⟩
  · obtain ⟨⟨w, hw⟩, a⟩ := j
    have key (w' : T) : {b : p ⁻¹' {w'.1} |
        (S ⟨⟨w, hw⟩, a⟩ ∩ S ⟨w', b⟩).Nonempty}.Finite := by
      have := hd w'.1
      let D := {u : U w | u.1 ∈ U w'}
      let h : D → p ⁻¹' {w'.1} := fun d ↦ (H w' ⟨((H w).symm (d.1, a)).1, by
        have := hH w ((H w).symm (d.1, a))
        simp only [Homeomorph.apply_symm_apply] at this
        change p _ ∈ U w'
        rw [← this]
        exact d.2⟩).2
      have hh : Continuous h := by
        refine continuous_snd.comp ((H w').continuous.comp ?_)
        fun_prop
      refine (isCompact_range hh).finite_of_discrete.subset ?_
      rintro b ⟨x, hx₁, hx₂⟩
      obtain ⟨hxw, hxa⟩ : ∃ hx : p x ∈ U w, (H w ⟨x, hx⟩).2 = a := mem_S.1 hx₁
      obtain ⟨hxw', hxb⟩ : ∃ hx : p x ∈ U w', (H w' ⟨x, hx⟩).2 = b := mem_S.1 hx₂
      have h1 : ((H w ⟨x, hxw⟩).1 : Z) = p x := hH w _
      refine ⟨⟨(H w ⟨x, hxw⟩).1, by simpa [D, h1] using hxw'⟩, ?_⟩
      have h2 : (H w).symm ((H w ⟨x, hxw⟩).1, a) = ⟨x, hxw⟩ := by
        rw [← hxa]; exact (H w).symm_apply_apply _
      simp only [h, h2]
      exact hxb
    refine ((finite_iUnion fun w' ↦ (key w').image (Sigma.mk w')).subset ?_)
    rintro ⟨w', b⟩ hb
    exact mem_iUnion.2 ⟨w', b, hb, rfl⟩
  · refine Subsingleton.finite fun x hx y hy ↦ ?_
    obtain ⟨hxw, hxa⟩ := mem_S.1 hx.1
    obtain ⟨hyw, hya⟩ := mem_S.1 hy.1
    have : H j.1 ⟨x, hxw⟩ = H j.1 ⟨y, hyw⟩ :=
      Prod.ext (Subtype.ext (by rw [hH, hH]; exact hx.2.trans hy.2.symm)) (hxa.trans hya.symm)
    exact congrArg Subtype.val ((H j.1).injective this)

/-- The fibres of a covering map with connected total space onto a noetherian space are
countable. -/
theorem IsCoveringMap.countable_fibre {E Z : Type*} [TopologicalSpace E] [TopologicalSpace Z]
    [NoetherianSpace Z] {p : E → Z} (hp : IsCoveringMap p) [PreconnectedSpace E] (z : Z) :
    (p ⁻¹' {z}).Countable := by
  simpa using hp.countable_inter_fibre_of_isPreconnected isPreconnected_univ z

/-- For a covering map onto a noetherian space, every connected component of the total space
meets every fibre in a countable set. -/
theorem IsCoveringMap.countable_connectedComponent_inter_fibre {E Z : Type*} [TopologicalSpace E]
    [TopologicalSpace Z] [NoetherianSpace Z] {p : E → Z} (hp : IsCoveringMap p) (e : E) (z : Z) :
    (connectedComponent e ∩ p ⁻¹' {z}).Countable :=
  hp.countable_inter_fibre_of_isPreconnected isPreconnected_connectedComponent z
