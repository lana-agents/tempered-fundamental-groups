/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateCrossing

/-!
# The 3-gon: `HarmonicTate` from `CrossingX1` when `b₆ ∈ 𝔪` (Blueprint §10.3.8)

If `b₆ ∈ 𝔪`, the conic `E'` of the special fibre of the Tate model is the union of the lines
`L₁ = {x₁ = 0} ∋ p` and `L₂ = {x₀ + x₁ = 0} ∋ q`, meeting at `r = [0 : 0 : 1]`
(`TateModel.L1set`, `L2set`, `rZ`): the special fibre is the 3-gon `C, L₁, L₂`.

When moreover `c = b₆ − π² b₄² ≠ 0` divides `π`, the germ at `r` is an exact node
(`TateNormal.nodeGerm_of_mem_two`), and `CrossingX1` at `p`, `r`, `q` gives
`Pres.HarmonicTate T {L₁, L₂} a` (`Pres.harmonicTate_of_crossingX1_threeGon`): from a component
over `L₁` one crosses `r` to a component over `L₂` and then `q` to a component over `C`.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial Set

namespace TemperedFundamentalGroups

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace TateModel

variable {O : Type u} [CommRing O] [IsLocalRing O] {π b₄ b₆ : O}

variable (π b₄ b₆) in
/-- The line `L₁ = {x₁ = 0}` of the special fibre. -/
def L1set : Set (Z π b₄ b₆) := {z | X 1 ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal}

variable (π b₄ b₆) in
/-- The line `L₂ = {x₀ + x₁ = 0}` of the special fibre. -/
def L2set : Set (Z π b₄ b₆) := {z | X 0 + X 1 ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal}

/-- The generic point of `L₁` (for `b₆ ∈ 𝔪`); it lies neither on `C` nor on `L₂`. -/
lemma exists_closure_eq_L1set (hπ : π ∈ IsLocalRing.maximalIdeal O)
    (hb : b₆ ∈ IsLocalRing.maximalIdeal O) :
    ∃ z : Z π b₄ b₆, closure {z} = L1set π b₄ b₆ ∧ z ∉ Cset π b₄ b₆ ∧ z ∉ L2set π b₄ b₆ := by
  have hπ' := (IsLocalRing.residue_eq_zero_iff π).2 hπ
  have hb' := (IsLocalRing.residue_eq_zero_iff b₆).2 hb
  obtain ⟨z, hz⟩ := exists_ιZ_eq_of_le (g := gL₁ O) (π := π) (b₄ := b₄) (b₆ := b₆)
    (by simp [F, gL₁, hπ', hb']) (y := pointL₁ O) fun _ hh => hh
  refine ⟨z, ?_, ?_, ?_⟩
  · ext w
    rw [closure_eq_of_ιZ hz]
    exact ⟨fun h => h (by simp [gL₁] : θ (gL₁ O) (X 1) = 0),
      fun h => pointL₁_le (fun c hc => C_mem π b₄ b₆ w hc) h⟩
  · intro h
    have h0 : θ (gL₁ O) (X 2) = 0 := by
      have : X 2 ∈ (pointL₁ O).asHomogeneousIdeal := hz ▸ h
      exact this
    simp [gL₁] at h0
  · intro h
    have h0 : θ (gL₁ O) (X 0 + X 1) = 0 := by
      have : X 0 + X 1 ∈ (pointL₁ O).asHomogeneousIdeal := hz ▸ h
      exact this
    simp [gL₁] at h0

/-- The generic point of `L₂` (for `b₆ ∈ 𝔪`); it lies neither on `C` nor on `L₁`. -/
lemma exists_closure_eq_L2set (hπ : π ∈ IsLocalRing.maximalIdeal O)
    (hb : b₆ ∈ IsLocalRing.maximalIdeal O) :
    ∃ z : Z π b₄ b₆, closure {z} = L2set π b₄ b₆ ∧ z ∉ Cset π b₄ b₆ ∧ z ∉ L1set π b₄ b₆ := by
  have hπ' := (IsLocalRing.residue_eq_zero_iff π).2 hπ
  have hb' := (IsLocalRing.residue_eq_zero_iff b₆).2 hb
  obtain ⟨z, hz⟩ := exists_ιZ_eq_of_le (g := gL₂ O) (π := π) (b₄ := b₄) (b₆ := b₆)
    (by simp [F, gL₂, hπ', hb']; ring) (y := pointL₂ O) fun _ hh => hh
  refine ⟨z, ?_, ?_, ?_⟩
  · ext w
    rw [closure_eq_of_ιZ hz]
    exact ⟨fun h => h (by simp [gL₂] : θ (gL₂ O) (X 0 + X 1) = 0),
      fun h => pointL₂_le (fun c hc => C_mem π b₄ b₆ w hc) h⟩
  · intro h
    have h0 : θ (gL₂ O) (X 2) = 0 := by
      have : X 2 ∈ (pointL₂ O).asHomogeneousIdeal := hz ▸ h
      exact this
    simp [gL₂] at h0
  · intro h
    have h0 : θ (gL₂ O) (X 1) = 0 := by
      have : X 1 ∈ (pointL₂ O).asHomogeneousIdeal := hz ▸ h
      exact this
    simp [gL₂] at h0

lemma Eset_eq_union (hb : b₆ ∈ IsLocalRing.maximalIdeal O) :
    Eset π b₄ b₆ = L1set π b₄ b₆ ∪ L2set π b₄ b₆ := by
  ext z
  rw [mem_Eset_iff_of_mem hb, mem_union]
  have hy : ∀ c ∈ IsLocalRing.maximalIdeal O, C c ∈ (ιZ π b₄ b₆ z).asHomogeneousIdeal :=
    fun c hc => C_mem π b₄ b₆ z hc
  exact or_congr ⟨fun h => h (by simp [gL₁] : θ (gL₁ O) (X 1) = 0), pointL₁_le hy⟩
    ⟨fun h => h (by simp [gL₂] : θ (gL₂ O) (X 0 + X 1) = 0), pointL₂_le hy⟩

variable (π b₄ b₆) in
/-- The point `r = [0 : 0 : 1]` of the special fibre (for `b₆ ∈ 𝔪`). -/
def rZ (hπ : π ∈ IsLocalRing.maximalIdeal O) (hb : b₆ ∈ IsLocalRing.maximalIdeal O) :
    Z π b₄ b₆ :=
  (exists_ιZ_eq_of_le (g := gN O) (π := π) (b₄ := b₄) (b₆ := b₆)
    (by simp [F, gN, (IsLocalRing.residue_eq_zero_iff π).2 hπ,
      (IsLocalRing.residue_eq_zero_iff b₆).2 hb]) (y := pointN O) fun _ hh => hh).choose

lemma ιZ_rZ (hπ : π ∈ IsLocalRing.maximalIdeal O) (hb : b₆ ∈ IsLocalRing.maximalIdeal O) :
    ιZ π b₄ b₆ (rZ π b₄ b₆ hπ hb) = pointN O :=
  (exists_ιZ_eq_of_le (g := gN O) (π := π) (b₄ := b₄) (b₆ := b₆)
    (by simp [F, gN, (IsLocalRing.residue_eq_zero_iff π).2 hπ,
      (IsLocalRing.residue_eq_zero_iff b₆).2 hb]) (y := pointN O) fun _ hh => hh).choose_spec

lemma mem_pointN {h : MvPolynomial (Fin (2 + 1)) O} :
    h ∈ (pointN O).asHomogeneousIdeal ↔ θ (gN O) h = 0 :=
  Iff.rfl

end TateModel


open TempObj CurveConfig TateObject SemistableReduction.ProjScheme

attribute [local instance] TateNormal.algK

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] {x : R}
  (T : TateObject.Data O R) [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))]

namespace TateObject

omit [IsDiscreteValuationRing O] [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))] in
lemma mem_irreducibleComponents_L1 (hb : T.b₆ ∈ IsLocalRing.maximalIdeal O) :
    TateModel.L1set T.π T.b₄ T.b₆ ∈ irreducibleComponents (X₀ (A := A) T).Lv.Z := by
  obtain ⟨z, hz, hC, h2⟩ := TateModel.exists_closure_eq_L1set (b₄ := T.b₄) T.π_mem hb
  have h : closure ({z} : Set (TateModel.Z T.π T.b₄ T.b₆)) ∈
      irreducibleComponents (TateModel.Z T.π T.b₄ T.b₆) :=
    closure_mem_irreducibleComponents ((decomp (A := A) T).isClosed_C.union
      (TateModel.isClosed_setOf_mem _ _ _ _))
      (by
        rw [hz]
        refine Set.eq_univ_of_forall fun w => ?_
        have hw : w ∈ (decomp (A := A) T).C ∪ (decomp (A := A) T).E := by
          rw [(decomp (A := A) T).union]; trivial
        rcases hw with hw | hw
        · exact Or.inr (Or.inl hw)
        · have hw' : w ∈ TateModel.L1set T.π T.b₄ T.b₆ ∪ TateModel.L2set T.π T.b₄ T.b₆ := by
            rw [← TateModel.Eset_eq_union hb]; exact hw
          rcases hw' with hw' | hw'
          · exact Or.inl hw'
          · exact Or.inr (Or.inr hw'))
      (fun h => h.elim hC h2)
  rw [hz] at h
  exact h

omit [IsDiscreteValuationRing O] [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))] in
lemma mem_irreducibleComponents_L2 (hb : T.b₆ ∈ IsLocalRing.maximalIdeal O) :
    TateModel.L2set T.π T.b₄ T.b₆ ∈ irreducibleComponents (X₀ (A := A) T).Lv.Z := by
  obtain ⟨z, hz, hC, h1⟩ := TateModel.exists_closure_eq_L2set (b₄ := T.b₄) T.π_mem hb
  have h : closure ({z} : Set (TateModel.Z T.π T.b₄ T.b₆)) ∈
      irreducibleComponents (TateModel.Z T.π T.b₄ T.b₆) :=
    closure_mem_irreducibleComponents ((decomp (A := A) T).isClosed_C.union
      (TateModel.isClosed_setOf_mem _ _ _ _))
      (by
        rw [hz]
        refine Set.eq_univ_of_forall fun w => ?_
        have hw : w ∈ (decomp (A := A) T).C ∪ (decomp (A := A) T).E := by
          rw [(decomp (A := A) T).union]; trivial
        rcases hw with hw | hw
        · exact Or.inr (Or.inl hw)
        · have hw' : w ∈ TateModel.L1set T.π T.b₄ T.b₆ ∪ TateModel.L2set T.π T.b₄ T.b₆ := by
            rw [← TateModel.Eset_eq_union hb]; exact hw
          rcases hw' with hw' | hw'
          · exact Or.inr (Or.inr hw')
          · exact Or.inl hw')
      (fun h => h.elim hC h1)
  rw [hz] at h
  exact h

omit [IsDiscreteValuationRing O] [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))] in
/-- The two lines of the 3-gon lie in the conic and are not points. -/
lemma threeGon_lines (hb : T.b₆ ∈ IsLocalRing.maximalIdeal O) :
    ∀ S ∈ ({TateModel.L1set T.π T.b₄ T.b₆, TateModel.L2set T.π T.b₄ T.b₆} :
      Set (Set (X₀ (A := A) T).Lv.Z)), S ⊆ (decomp (A := A) T).E ∧ ¬ ∃ y, S = {y} := by
  set pZ := TateModel.pZ T.π T.b₄ T.b₆ T.π_mem
  set qZ := TateModel.qZ T.π T.b₄ T.b₆ T.π_mem
  set rZ := TateModel.rZ T.π T.b₄ T.b₆ T.π_mem hb
  have hpP : TateModel.ιZ T.π T.b₄ T.b₆ pZ = TateModel.pointP O := TateModel.ιZ_pZ T.π_mem
  have hqQ : TateModel.ιZ T.π T.b₄ T.b₆ qZ = TateModel.pointQ O := TateModel.ιZ_qZ T.π_mem
  have hrN : TateModel.ιZ T.π T.b₄ T.b₆ rZ = TateModel.pointN O := TateModel.ιZ_rZ T.π_mem hb
  have hpC : pZ ∈ (decomp (A := A) T).C := TateModel.pZ_mem_Cset T.π_mem
  have hqC : qZ ∈ (decomp (A := A) T).C := TateModel.qZ_mem_Cset T.π_mem
  have hrC : rZ ∉ (decomp (A := A) T).C := by
    change (X 2 : MvPolynomial (Fin (2 + 1)) O) ∉
      (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
    rw [hrN, TateModel.mem_pointN]
    simp [TateModel.gN]
  have hE : TateModel.Eset T.π T.b₄ T.b₆ =
      TateModel.L1set T.π T.b₄ T.b₆ ∪ TateModel.L2set T.π T.b₄ T.b₆ :=
    TateModel.Eset_eq_union hb
  rintro S (rfl | rfl)
  · refine ⟨fun z hz => ?_, ?_⟩
    · change z ∈ TateModel.Eset T.π T.b₄ T.b₆
      rw [hE]; exact Or.inl hz
    · rintro ⟨y, hy⟩
      have hp : pZ ∈ TateModel.L1set T.π T.b₄ T.b₆ := by
        change (X 1 : MvPolynomial (Fin (2 + 1)) O) ∈
          (TateModel.ιZ T.π T.b₄ T.b₆ pZ).asHomogeneousIdeal
        rw [hpP, TateModel.mem_pointP]
        simp [TateModel.gp]
      have hr : rZ ∈ TateModel.L1set T.π T.b₄ T.b₆ := by
        change (X 1 : MvPolynomial (Fin (2 + 1)) O) ∈
          (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
        rw [hrN, TateModel.mem_pointN]
        simp [TateModel.gN]
      rw [hy] at hp hr
      exact hrC ((hr.trans hp.symm) ▸ hpC)
  · refine ⟨fun z hz => ?_, ?_⟩
    · change z ∈ TateModel.Eset T.π T.b₄ T.b₆
      rw [hE]; exact Or.inr hz
    · rintro ⟨y, hy⟩
      have hq : qZ ∈ TateModel.L2set T.π T.b₄ T.b₆ := by
        change (X 0 + X 1 : MvPolynomial (Fin (2 + 1)) O) ∈
          (TateModel.ιZ T.π T.b₄ T.b₆ qZ).asHomogeneousIdeal
        rw [hqQ, TateModel.mem_pointQ]
        simp [TateModel.gq]
      have hr : rZ ∈ TateModel.L2set T.π T.b₄ T.b₆ := by
        change (X 0 + X 1 : MvPolynomial (Fin (2 + 1)) O) ∈
          (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
        rw [hrN, TateModel.mem_pointN]
        simp [TateModel.gN]
      rw [hy] at hq hr
      exact hrC ((hr.trans hq.symm) ▸ hqC)

end TateObject



namespace Pres

variable [CharZero K] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain R]
  {Y : TempObj O R A} (Q : Pres x Y)

/-- **Crossing a node of the Tate model** on the special fibre of a member: a component mapped
onto `S` has a walk with special points over `y` to a component mapped onto `S'`. -/
lemma exists_incWalk_crossing (hC : SemistableReduction.Statement.CrossingX1S.{u})
    (hx : Transcendental K T.x) {ϖ : O} (hϖ : Irreducible ϖ) (a : Q.U ⟶ X₀ (A := A) T)
    {S S' : Set (X₀ (A := A) T).Lv.Z} (hS : S ∈ irreducibleComponents (X₀ (A := A) T).Lv.Z)
    (hS' : S' ∈ irreducibleComponents (X₀ (A := A) T).Lv.Z) (hne : S ≠ S')
    {y : (X₀ (A := A) T).Lv.Z} (hyS : y ∈ S) (hyS' : y ∈ S')
    (hG : ∃ (P : Subring (TateNormal.TateField T.π T.b₄ T.b₆))
      (u v : TateNormal.TateField T.π T.b₄ T.b₆) (n : ℕ),
      (P : Set (TateNormal.TateField T.π T.b₄ T.b₆)) =
        SemistableReduction.ModelCode.germs (tgtModel T)
          (genericPt O (TateNormal.hcoords T.π T.b₄ T.b₆ T.π_ne_zero)) (tpt (A := A) T y) ∧
      _root_.SemistableReduction.NodeGerm O ϖ P u v n ∧ (∀ w ∈ P, u * w ≠ 1) ∧
        (∀ w ∈ P, v * w ≠ 1))
    (i : irreducibleComponents Q.Lv.Z)
    (hi : specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i = S) :
    ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i L ∧
      (∀ p ∈ L, specialFibreMap a.ψ a.ψ_toSpec p.1 = y) ∧
      specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C (lastLab i L) = S' := by
  obtain ⟨w, hw0, hcross, hlast⟩ := Q.crossing_tate T hC hx hϖ a (tpt (A := A) T y)
    (tSet (A := A) T S) (tSet (A := A) T S') (tSet_mem T hS) (tSet_mem T hS')
    ((tSet_injective T).ne hne) ⟨_, hyS, rfl⟩ ⟨_, hyS', rfl⟩ hG (Q.D.compSet i.1)
    (Q.D.compSet_mem i.2) (by rw [Q.tateψ_image_compSet T a]; exact congrArg _ hi)
  obtain ⟨L, hL, hpL, hlastL⟩ := Q.exists_incWalk_of_crosses T a w i hw0 hcross
  refine ⟨L, hL, fun p hp => tpt_injective T (hpL p hp), ?_⟩
  rw [hlast] at hlastL
  exact (tSet_injective T hlastL).symm

/-- **`HarmonicTate` from `CrossingX1` for the 3-gon** (`b₆ ∈ 𝔪`), when
`c = b₆ − π² b₄² ≠ 0` divides `π` (so that `r` is an exact node). -/
theorem harmonicTate_of_crossingX1_threeGon (hC : SemistableReduction.Statement.CrossingX1S.{u})
    (hb : T.b₆ ∈ IsLocalRing.maximalIdeal O) (hc0 : T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ≠ 0)
    (hcπ : T.b₆ - T.π ^ 2 * T.b₄ ^ 2 ∣ T.π) (hx : Transcendental K T.x) {ϖ : O}
    (hϖ : Irreducible ϖ) (a : Q.U ⟶ X₀ (A := A) T) :
    Q.HarmonicTate T {TateModel.L1set T.π T.b₄ T.b₆, TateModel.L2set T.π T.b₄ T.b₆} a := by
  have hCc := mem_irreducibleComponents_C (A := A) T
  have hL1 := mem_irreducibleComponents_L1 (A := A) T hb
  have hL2 := mem_irreducibleComponents_L2 (A := A) T hb
  obtain ⟨hCp, -, -, -⟩ := decomp_spec (A := A) T
  obtain ⟨z1, hz1, hz1C, hz12⟩ := TateModel.exists_closure_eq_L1set (b₄ := T.b₄) T.π_mem hb
  obtain ⟨z2, hz2, hz2C, -⟩ := TateModel.exists_closure_eq_L2set (b₄ := T.b₄) T.π_mem hb
  have hz1m : z1 ∈ TateModel.L1set T.π T.b₄ T.b₆ := hz1 ▸ subset_closure rfl
  have hz2m : z2 ∈ TateModel.L2set T.π T.b₄ T.b₆ := hz2 ▸ subset_closure rfl
  have hCL1 : (decomp (A := A) T).C ≠ TateModel.L1set T.π T.b₄ T.b₆ := fun h =>
    hz1C (by change z1 ∈ (decomp (A := A) T).C; rw [h]; exact hz1m)
  have hCL2 : (decomp (A := A) T).C ≠ TateModel.L2set T.π T.b₄ T.b₆ := fun h =>
    hz2C (by change z2 ∈ (decomp (A := A) T).C; rw [h]; exact hz2m)
  have hL12 : TateModel.L1set T.π T.b₄ T.b₆ ≠ TateModel.L2set T.π T.b₄ T.b₆ := fun h =>
    hz12 (h ▸ hz1m)
  set pZ := TateModel.pZ T.π T.b₄ T.b₆ T.π_mem
  set qZ := TateModel.qZ T.π T.b₄ T.b₆ T.π_mem
  set rZ := TateModel.rZ T.π T.b₄ T.b₆ T.π_mem hb
  have hpP : TateModel.ιZ T.π T.b₄ T.b₆ pZ = TateModel.pointP O := TateModel.ιZ_pZ T.π_mem
  have hqQ : TateModel.ιZ T.π T.b₄ T.b₆ qZ = TateModel.pointQ O := TateModel.ιZ_qZ T.π_mem
  have hrN : TateModel.ιZ T.π T.b₄ T.b₆ rZ = TateModel.pointN O := TateModel.ιZ_rZ T.π_mem hb
  have hpC : pZ ∈ (decomp (A := A) T).C := TateModel.pZ_mem_Cset T.π_mem
  have hqC : qZ ∈ (decomp (A := A) T).C := TateModel.qZ_mem_Cset T.π_mem
  have hpL1 : pZ ∈ TateModel.L1set T.π T.b₄ T.b₆ := by
    change (X 1 : MvPolynomial (Fin (2 + 1)) O) ∈
      (TateModel.ιZ T.π T.b₄ T.b₆ pZ).asHomogeneousIdeal
    rw [hpP, TateModel.mem_pointP]
    simp [TateModel.gp]
  have hqL2 : qZ ∈ TateModel.L2set T.π T.b₄ T.b₆ := by
    change (X 0 + X 1 : MvPolynomial (Fin (2 + 1)) O) ∈
      (TateModel.ιZ T.π T.b₄ T.b₆ qZ).asHomogeneousIdeal
    rw [hqQ, TateModel.mem_pointQ]
    simp [TateModel.gq]
  have hrL1 : rZ ∈ TateModel.L1set T.π T.b₄ T.b₆ := by
    change (X 1 : MvPolynomial (Fin (2 + 1)) O) ∈
      (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
    rw [hrN, TateModel.mem_pointN]
    simp [TateModel.gN]
  have hrL2 : rZ ∈ TateModel.L2set T.π T.b₄ T.b₆ := by
    change (X 0 + X 1 : MvPolynomial (Fin (2 + 1)) O) ∈
      (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
    rw [hrN, TateModel.mem_pointN]
    simp [TateModel.gN]
  have hrC : rZ ∉ (decomp (A := A) T).C := by
    change (X 2 : MvPolynomial (Fin (2 + 1)) O) ∉
      (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
    rw [hrN, TateModel.mem_pointN]
    simp [TateModel.gN]
  have hrp : rZ ∉ (decomp (A := A) T).Cp := by
    rw [hCp]; exact fun h => hrC ((Set.mem_singleton_iff.1 h) ▸ hpC)
  have hqp : qZ ∉ (decomp (A := A) T).Cp := by
    obtain ⟨-, -, hpq, -⟩ := decomp_spec (A := A) T
    rw [hCp]; exact fun h => hpq (Set.mem_singleton_iff.1 h).symm
  have hGp := TateNormal.nodeGerm_p T.π_ne_zero T.π_mem hϖ (b₄ := T.b₄) (b₆ := T.b₆)
  have hGq := TateNormal.nodeGerm_q T.π_ne_zero T.π_mem hϖ (b₄ := T.b₄) (b₆ := T.b₆)
  have hGr := TateNormal.nodeGerm_of_mem_two T.π T.b₄ T.b₆ T.π_ne_zero hϖ T.π_mem hc0 hcπ
    rZ.1 (by change X 2 ∉ (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
             rw [hrN, TateModel.mem_pointN]; simp [TateModel.gN])
    (by change X 0 ∈ (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
        rw [hrN, TateModel.mem_pointN]; simp [TateModel.gN])
    (by change X 1 ∈ (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
        rw [hrN, TateModel.mem_pointN]; simp [TateModel.gN])
    (fun o ho => by
      change C o * X 2 ∈ (TateModel.ιZ T.π T.b₄ T.b₆ rZ).asHomogeneousIdeal
      rw [hrN, TateModel.mem_pointN]
      simp [TateModel.gN, (IsLocalRing.residue_eq_zero_iff o).2 ho])
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨L, hL, hpL, hlast⟩ := Q.exists_incWalk_crossing T hC hx hϖ a hCc hL1 hCL1 hpC hpL1
      hGp i hi
    refine ⟨L, hL, fun p hp => ?_, ?_⟩
    · rw [hpL p hp, hCp]; rfl
    · rw [hlast]; exact Or.inl rfl
  · rcases hi with hi | hi
    · -- over `L₁`: cross `r` to `L₂`, then `q` to `C`
      obtain ⟨L, hL, hpL, hlast⟩ := Q.exists_incWalk_crossing T hC hx hϖ a hL1 hL2 hL12 hrL1
        hrL2 hGr i hi
      obtain ⟨L', hL', hpL', hlast'⟩ := Q.exists_incWalk_crossing T hC hx hϖ a hL2 hCc
        hCL2.symm hqL2 hqC hGq _ hlast
      refine ⟨L ++ L', CurveConfig.incWalk_append.2 ⟨hL, hL'⟩, fun p hp => ?_, ?_⟩
      · rcases List.mem_append.1 hp with hp | hp
        · rw [hpL p hp]; exact hrp
        · rw [hpL' p hp]; exact hqp
      · rw [CurveConfig.lastLab_append]; exact hlast'
    · -- over `L₂`: cross `q` to `C`
      obtain ⟨L, hL, hpL, hlast⟩ := Q.exists_incWalk_crossing T hC hx hϖ a hL2 hCc hCL2.symm
        hqL2 hqC hGq i hi
      exact ⟨L, hL, fun p hp => by rw [hpL p hp]; exact hqp, hlast⟩

end Pres

end

end TemperedFundamentalGroups
