/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateCovering
import TemperedFundamentalGroups.Topology.HeightLength

/-!
# Sheets along walks in the `ℤ`-covering of the Tate 2-gon (Blueprint §10.3.8, hbase)

Let `D : TateCovering.Decomp Z` (`Z = C ∪ E`, `C ∩ E = Cp ⊔ Cq`) with its `ℤ`-covering
`D.Space`. Specialization in `D.Space` preserves the sheet over `Z ∖ Cq` and the shifted sheet
over `Z ∖ Cp` (`Decomp.n_eq_of_mem_closure`, `Decomp.n_sub_shift_eq_of_mem_closure`).

For a tree covering `K.Cover r` of a curve with a continuous map `h` to `D.Space` over `f`, the
sheet `N t = (h (gen t)).n` of the generic points of component vertices is therefore constant
along walks whose special points map outside `Cq` (`CurveConfig.sheet_pend_of_notMem_Cq`), and
`N t − shift (f η)` is constant along walks whose special points map outside `Cp`
(`CurveConfig.sheet_pend_of_notMem_Cp`).
-/

universe u v

open Set Topology

namespace TemperedFundamentalGroups

namespace TateCovering.Decomp

variable {Z : Type u} [TopologicalSpace Z] (D : Decomp Z)

/-- Specialization preserves the sheet over `Z ∖ Cq`. -/
lemma n_eq_of_mem_closure {x y : D.Space} (h : y ∈ closure {x}) (hy : y.pt ∉ D.Cq) :
    x.n = y.n := by
  obtain ⟨w, hw, rfl⟩ := mem_closure_iff.1 h _ (D.isOpen_sheet₁ y.n) ⟨hy, rfl⟩
  exact hw.2

/-- Specialization preserves the shifted sheet over `Z ∖ Cp`. -/
lemma n_sub_shift_eq_of_mem_closure {x y : D.Space} (h : y ∈ closure {x}) (hy : y.pt ∉ D.Cp) :
    x.n - D.shift x.pt = y.n - D.shift y.pt := by
  obtain ⟨w, hw, rfl⟩ := mem_closure_iff.1 h _ (D.isOpen_sheet₂ (y.n - D.shift y.pt)) ⟨hy, rfl⟩
  exact hw.2

end TateCovering.Decomp

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}
  {Z' : Type u} [TopologicalSpace Z'] {D : TateCovering.Decomp Z'} {f : Z → Z'}
  {h : K.Cover r → D.Space} (hh : Continuous h) (hf : ∀ e, (h e).pt = f e.1.1)
include hh hf

omit hf in
/-- One step of a walk: through a special vertex `σ` adjacent to `t`, the image of `gen σ`
specializes from the image of `gen t`. -/
lemma map_gen_mem_closure {σ t : K.Tree r} (hσ : IsSpecial σ) (hadj : σ.Adj t) :
    h (gen σ) ∈ closure {h (gen t)} :=
  map_mem_closure hh (mem_closure_gen (gen_near_of_adj hσ hadj))
    (fun a ha => by rw [mem_singleton_iff.1 ha]; rfl)

/-- **The sheet is constant along walks avoiding `Cq`.** -/
lemma sheet_pend_of_notMem_Cq : ∀ {t : K.Tree r} {L : List (K.Tree r × K.Tree r)}, IsComp t →
    PWalk t L → (∀ p ∈ L, f (spt p.1) ∉ D.Cq) → (h (gen (pend t L))).n = (h (gen t)).n
  | _, [], _, _, _ => rfl
  | t, (σ, t') :: L, ht, ⟨h₁, h₂, h₃⟩, hq => by
    have hσ := isSpecial_of_adj ht h₁
    have ht' := isComp_of_adj hσ h₂
    rw [pend_cons, sheet_pend_of_notMem_Cq ht' h₃ fun p hp => hq p (List.mem_cons_of_mem _ hp)]
    have hσq : (h (gen σ)).pt ∉ D.Cq := by
      rw [hf]; exact hq _ (List.mem_cons_self ..)
    rw [D.n_eq_of_mem_closure (map_gen_mem_closure hh hσ h₂) hσq,
      D.n_eq_of_mem_closure (map_gen_mem_closure hh hσ (Tree.adj_comm.1 h₁)) hσq]

/-- **The shifted sheet is constant along walks avoiding `Cp`.** -/
lemma sheet_pend_of_notMem_Cp : ∀ {t : K.Tree r} {L : List (K.Tree r × K.Tree r)}, IsComp t →
    PWalk t L → (∀ p ∈ L, f (spt p.1) ∉ D.Cp) →
    (h (gen (pend t L))).n - D.shift (f (gen (pend t L)).1.1) =
      (h (gen t)).n - D.shift (f (gen t).1.1)
  | _, [], _, _, _ => rfl
  | t, (σ, t') :: L, ht, ⟨h₁, h₂, h₃⟩, hp => by
    have hσ := isSpecial_of_adj ht h₁
    have ht' := isComp_of_adj hσ h₂
    rw [pend_cons, sheet_pend_of_notMem_Cp ht' h₃ fun p hp' =>
      hp p (List.mem_cons_of_mem _ hp')]
    have hσp : (h (gen σ)).pt ∉ D.Cp := by
      rw [hf]; exact hp _ (List.mem_cons_self ..)
    have e₁ := D.n_sub_shift_eq_of_mem_closure (map_gen_mem_closure hh hσ h₂) hσp
    have e₂ := D.n_sub_shift_eq_of_mem_closure
      (map_gen_mem_closure hh hσ (Tree.adj_comm.1 h₁)) hσp
    rw [hf] at e₁ e₂
    rw [e₁, e₂]

omit hh hf in
lemma labW_mem {L : List (K.Tree r × K.Tree r)} {P : Z → Prop}
    (hL : ∀ p ∈ labW L, P p.1) : ∀ p ∈ L, P (spt p.1) := by
  intro p hp
  exact hL _ (List.mem_map_of_mem (f := fun p : K.Tree r × K.Tree r => (spt p.1, lab p.2)) hp)

/-- **Alternating crossings wind** (pigeonhole). Let `VC`, `VE` be sets of components whose
generic points map into `C`, resp. outside `C`. If every component in `VC` has a crossing walk
avoiding `Cq` to a component in `VE`, and every component in `VE` one avoiding `Cp` to a
component in `VC`, then some two component vertices with the same label carry different
sheets. -/
theorem exists_sheet_ne [Finite ι] (VC VE : ι → Prop)
    (hVC : ∀ i, VC i → f (K.η i) ∈ D.C) (hVE : ∀ i, VE i → f (K.η i) ∉ D.C)
    (crossP : ∀ i, VC i → ∃ L : List (Z × ι), IncWalk K i L ∧ (∀ p ∈ L, f p.1 ∉ D.Cq) ∧
      VE (lastLab i L))
    (crossQ : ∀ i, VE i → ∃ L : List (Z × ι), IncWalk K i L ∧ (∀ p ∈ L, f p.1 ∉ D.Cp) ∧
      VC (lastLab i L))
    {t₀ : K.Tree r} {i₀ : ι} (ht₀ : t₀.1.head? = some (.inl i₀)) (hi₀ : VC i₀) :
    ∃ (t t' : K.Tree r) (i : ι), t.1.head? = some (.inl i) ∧ t'.1.head? = some (.inl i) ∧
      (h (gen t)).n ≠ (h (gen t')).n := by
  classical
  choose LP hLP using crossP
  choose LQ hLQ using crossQ
  let step : {i // VC i} → {i // VC i} := fun i =>
    ⟨lastLab (lastLab i.1 (LP i.1 i.2)) (LQ _ (hLP i.1 i.2).2.2),
      (hLQ _ (hLP i.1 i.2).2.2).2.2⟩
  -- one round lowers the sheet by one
  have hround : ∀ (i : {i // VC i}) (t : K.Tree r), t.1.head? = some (.inl i.1) →
      ∃ t' : K.Tree r, t'.1.head? = some (.inl (step i).1) ∧
        (h (gen t')).n = (h (gen t)).n - 1 := by
    intro i t ht
    obtain ⟨hP₁, hP₂, hP₃⟩ := hLP i.1 i.2
    obtain ⟨T₁, hT₁, hT₁L⟩ := exists_pWalk_labW (LP i.1 i.2) ⟨i.1, ht⟩
      (by rw [lab_of ht]; exact hP₁)
    have hc₁ : IsComp (pend t T₁) := hT₁.isComp_pend ⟨i.1, ht⟩
    have hlab₁ : lab (pend t T₁) = lastLab i.1 (LP i.1 i.2) := by
      rw [← lastLab_labW, hT₁L, lab_of ht]
    obtain ⟨Q₁, hQ₂, hQ₃⟩ := hLQ _ hP₃
    obtain ⟨T₂, hT₂, hT₂L⟩ := exists_pWalk_labW (LQ _ hP₃) hc₁ (by rw [hlab₁]; exact Q₁)
    have hc₂ : IsComp (pend (pend t T₁) T₂) := hT₂.isComp_pend hc₁
    obtain ⟨j, hj⟩ := hc₂
    have hlab₂ : j = (step i).1 := by
      rw [← lab_of hj, ← lastLab_labW, hT₂L, hlab₁]
    refine ⟨pend (pend t T₁) T₂, hlab₂ ▸ hj, ?_⟩
    have e₁ := sheet_pend_of_notMem_Cq hh hf ⟨i.1, ht⟩ hT₁
      (labW_mem (P := fun z => f z ∉ D.Cq) (by rw [hT₁L]; exact hP₂))
    have e₂ := sheet_pend_of_notMem_Cp hh hf hc₁ hT₂
      (labW_mem (P := fun z => f z ∉ D.Cp) (by rw [hT₂L]; exact hQ₂))
    obtain ⟨k, hk⟩ := hc₁
    rw [gen_fst_of_inl hj, gen_fst_of_inl hk, D.shift_of_mem (hVC _ (hlab₂ ▸ (step i).2)),
      D.shift_of_notMem (hVE _ (by rw [← lab_of hk, hlab₁]; exact hP₃)), e₁] at e₂
    linarith
  -- iterate
  have hiter : ∀ k : ℕ, ∃ t : K.Tree r, t.1.head? = some (.inl (step^[k] ⟨i₀, hi₀⟩).1) ∧
      (h (gen t)).n = (h (gen t₀)).n - k := by
    intro k
    induction k with
    | zero => exact ⟨t₀, ht₀, by simp⟩
    | succ k ih =>
      obtain ⟨t, ht, hn⟩ := ih
      obtain ⟨t', ht', hn'⟩ := hround _ t ht
      refine ⟨t', by rw [Function.iterate_succ_apply']; exact ht', ?_⟩
      rw [hn', hn]
      push_cast
      ring
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => step^[k] ⟨i₀, hi₀⟩)
  obtain ⟨t, ht, hn⟩ := hiter a
  obtain ⟨t', ht', hn'⟩ := hiter b
  refine ⟨t, t', _, ht, (congrArg Subtype.val he) ▸ ht', ?_⟩
  rw [hn, hn']
  intro e
  exact hab (by exact_mod_cast (by linarith : (a : ℤ) = b))

end CurveConfig

end TemperedFundamentalGroups
