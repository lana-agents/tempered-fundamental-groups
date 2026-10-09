/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CrossingPrep

/-!
# Proof of `Statement.CrossingX1` (Blueprint §10.3.8, CX8)

The positions argument: `t = u'^{e₂}` (the pull back of the node coordinate `u`, `e₂` the
ramification of `O₂` over `O`) satisfies `t s = ϖ₁ ^ N` at every point over `y'`, `N = e₁ n`.
The position of a component of `c` through a point over `y'` is the `p` with
`W(t) = W(ϖ₁) ^ p` at its generic point:

* position `0`: the component lies over `w₁'` (`u` is a unit on `w₁'`, orientation by
  `NodeCore.valuation_lt_one_of_branch`);
* `0 < p < N`: the component is contracted to `y'` (its points are centres of valuations
  dominating the node germ; unique extension over the complete `O` puts `O₂` inside them);
* `p = N`: the component maps onto `w₂'` (its generic point maps to the generic point of `w₂'`,
  and every point of `w₂'` is the image of a centre inside the component).

The walk is `CrossingSource.exists_walk`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction

open CentreGerms ValuativeCentre ModelCode CrossingSource CrossingGlue

/-- **`Statement.CrossingX1` with positions**: the crossing walk, for the given node coordinates
`u v = ϖ₂ ^ n` of `y'`, comes with a coordinate `a ∈ {u, v}` and an exponent `m > 0` such that
the exponent of `a ^ m` (in powers of `ϖ₁`) strictly increases along each edge. -/
def CrossingX1Inc : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    (O₁ : ValuationSubring K₁) (O₂ : ValuationSubring K₂)
    (h₁ : O₁.comap (algebraMap K K₁) = O) (h₂ : O₂.comap (algebraMap K K₂) = O)
    [IsDiscreteValuationRing O₁] [IsDiscreteValuationRing O₂] (ϖ₁ : O₁) (ϖ₂ : O₂)
    (_ : Irreducible ϖ₁) (_ : Irreducible ϖ₂)
    (L₁ L₂ : Type u) [Field L₁] [Field L₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
    [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
    [IsScalarTower K L₂ L₁]
    [Algebra O₁ L₁] [IsScalarTower O₁ K₁ L₁] [Algebra O₂ L₂] [IsScalarTower O₂ K₂ L₂] (x : L₁)
    (c : TemperedFundamentalGroups.ModelCode O₁) (c' : TemperedFundamentalGroups.ModelCode O₂)
    (ψ : c.scheme ⟶ c'.scheme)
    (j : Spec (CommRingCat.of L₁) ⟶ c.scheme) (j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme)
    (hunf : ModelCode.IsUnfolded O₁ x c j),
    j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j' →
    ψ ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₂).restrict O O₂
      (fun y hy ↦ by rw [← h₂] at hy; exact hy))) =
      c.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₁).restrict O O₁
        (fun y hy ↦ by rw [← h₁] at hy; exact hy))) →
    ModelCode.HasSplitNodes ϖ₁ c → ModelCode.NoLoops c →
    Dense (Set.range j'.base) →
    ∀ (y' : c'.scheme) (w₁' w₂' : Set c'.scheme), w₁' ∈ ModelCode.components c' →
      w₂' ∈ ModelCode.components c' → w₁' ≠ w₂' → y' ∈ w₁' → y' ∈ w₂' →
      ∀ (P : Subring L₂) (u v : L₂) (n : ℕ), (P : Set L₂) = ModelCode.germs c' j' y' →
        _root_.SemistableReduction.NodeGerm O₂ ϖ₂ P u v n →
        (∀ w ∈ P, u * w ≠ 1) → (∀ w ∈ P, v * w ≠ 1) →
      ∀ v₀ ∈ ModelCode.components c, ψ '' v₀ = w₁' →
        ∃ w : ModelCode.Walk c, w.v 0 = v₀ ∧ w.Crosses ψ y' ∧ ψ '' w.v (Fin.last w.k) = w₂' ∧
          ∃ (a : L₂) (m : ℕ), (a = u ∨ a = v) ∧ 0 < m ∧
            ∀ i : Fin w.k, ∃ q q' : ℕ, q < q' ∧
              (Wc hunf.isWModel (w.mem_components i.castSucc)).valuation
                  (algebraMap L₂ L₁ a ^ m) =
                (Wc hunf.isWModel (w.mem_components i.castSucc)).valuation
                  (algebraMap O₁ L₁ ϖ₁) ^ q ∧
              (Wc hunf.isWModel (w.mem_components i.succ)).valuation (algebraMap L₂ L₁ a ^ m) =
                (Wc hunf.isWModel (w.mem_components i.succ)).valuation
                  (algebraMap O₁ L₁ ϖ₁) ^ q'

/-- **`CrossingX1Inc` holds.** -/
theorem crossingX1_inc : CrossingX1Inc.{u} := by
  intro K _ _ O _ _ K₁ K₂ _ _ _ _ _ _ O₁ O₂ h₁ h₂ _ _ ϖ₁ ϖ₂ hϖ₁ hϖ₂ L₁ L₂ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ x c c' ψ j j' hunf hj hψO hsplit0 hloops hdense y' w₁' w₂' hw₁ hw₂ hne hy₁ hy₂ P u v n
    hPg hG hu hv v₀ hv₀ hψv₀
  have hW : IsWModel O₁ L₁ x c j := hunf.isWModel
  have hsplit := hsplit0
  set ι := algebraMap L₂ L₁ with hι
  -- the generic point of the target is dense
  have hdom : ∀ y, j' (closedPoint L₂) ⤳ y := by
    intro y
    rw [specializes_iff_mem_closure]
    have : y ∈ closure (Set.range j'.base) := by rw [hdense.closure_eq]; trivial
    refine closure_mono ?_ this
    rintro _ ⟨p, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim p (closedPoint L₂)]
  haveI hPloc := (CrossingTarget.germs_local (hdom y') hPg).1
  haveI hPnoeth := (CrossingTarget.germs_local (hdom y') hPg).2
  have core₀ := NodeCore.of_nodeGerm hG hϖ₂ hu hv
  clear hG hu hv
  set ι₂ := (algebraMap K₂ L₂).comp O₂.subtype
  set ϖ₂L := algebraMap K₂ L₂ (ϖ₂ : K₂)
  set ϖ₁L := algebraMap O₁ L₁ ϖ₁
  -- generic points of `w₁'`, `w₂'`
  have hη₁y := gp_specializes hw₁ hy₁
  have hη₂y := gp_specializes hw₂ hy₂
  have hη₁ne : gp hw₁ ≠ y' := gp_ne_of_two hw₁ hw₁ hw₂ hne hy₁ hy₂
  have hη₂ne : gp hw₂ ≠ y' := gp_ne_of_two hw₂ hw₁ hw₂ hne hy₁ hy₂
  -- ramification
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e₂, μ₂, he₂, hμ₂⟩ := exists_ramification h₂ hϖ₀ hϖ₂
  obtain ⟨e₁, μ₁, he₁, hμ₁⟩ := exists_ramification h₁ hϖ₀ hϖ₁
  have hbase := fun o ↦ baseHom_target h₂ h₁ hW hj hψO o
  -- valuations containing the node germ
  have hPV : ∀ η, η ⤳ y' → ∀ V : ValuationSubring L₂, IsCentre j' V η → P ≤ V.toSubring :=
    fun η hη V hV f hf ↦ ((isCentre_iff_dominates c' j' (hdom η) V).1 hV).1
      (germs_anti c' j' hη (hPg ▸ hf))
  have hμ₂P : ι₂ μ₂ ∈ P ∧ ι₂ ↑μ₂⁻¹ ∈ P := ⟨core₀.base_mem _, core₀.base_mem _⟩
  have hμ₂0 : ι₂ μ₂ ≠ 0 := by simp [ι₂]
  have hμ₂inv : (ι₂ μ₂)⁻¹ = ι₂ ↑μ₂⁻¹ := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hμ₂0, ← map_mul, Units.inv_mul, map_one]
  -- `ϖ₂` at points of the special fibre of the target
  have hϖV : ∀ η ∈ Z c', ∀ V : ValuationSubring L₂, IsCentre j' V η → P ≤ V.toSubring →
      V.valuation ϖ₂L < 1 := by
    intro η hη V hV hPV'
    have hb := valuation_baseHom_lt_one hϖ₂ c' j' hη hV
    have hμ : V.valuation (baseHom c' j' μ₂) ≤ 1 :=
      (V.valuation_le_one_iff _).2 (((isCentre_iff_dominates c' j' (hdom η) V).1 hV).1
        (baseHom_mem_germs c' j' η _))
    have hK : V.valuation (algebraMap K L₂ ϖ₀) < 1 := by
      have e : (algebraMap K K₂).restrict O O₂ (fun y hy ↦ by rw [← h₂] at hy; exact hy) ϖ₀ =
          μ₂ * ϖ₂ ^ e₂ := Subtype.ext hμ₂
      rw [← hbase, e, map_mul, map_pow, map_mul, map_pow]
      exact (mul_le_of_le_one_left' hμ).trans_lt (pow_lt_one₀ zero_le hb (by omega))
    rw [IsScalarTower.algebraMap_apply K K₂ L₂, hμ₂, map_mul, map_pow, map_mul, map_pow] at hK
    have hu₂ : V.valuation (algebraMap K₂ L₂ ((μ₂ : O₂) : K₂)) = 1 :=
      valuation_unit hμ₂0 (hPV' hμ₂P.1)
        (by change (ι₂ ↑μ₂)⁻¹ ∈ V; rw [hμ₂inv]; exact hPV' hμ₂P.2)
    rw [hu₂, one_mul] at hK
    exact lt_one_of_pow_lt_one ((V.valuation_le_one_iff _).2 (hPV' core₀.ϖ_mem)) hK
  -- orientation
  obtain ⟨V₁, hV₁⟩ := exists_isCentre j' (hdom (gp hw₁))
  obtain ⟨V₂, hV₂⟩ := exists_isCentre j' (hdom (gp hw₂))
  have hP₁ := hPV _ hη₁y V₁ hV₁
  have hP₂ := hPV _ hη₂y V₂ hV₂
  have hϖ₁V := hϖV _ (hw₁.2.1 (gp_mem hw₁)) V₁ hV₁ hP₁
  have hϖ₂V := hϖV _ (hw₂.2.1 (gp_mem hw₂)) V₂ hV₂ hP₂
  have hη : gp hw₁ ≠ gp hw₂ := fun h ↦ hne (by rw [← closure_gp hw₁, ← closure_gp hw₂, h])
  have hsame : ∀ {a b : L₂}, NodeCore P ι₂ ϖ₂L a b n → ∀ V : ValuationSubring L₂,
      IsCentre j' V (gp hw₁) → P ≤ V.toSubring → V.valuation ϖ₂L < 1 → V.valuation a = 1 →
      V.valuation b < 1 → V₂.valuation a = 1 → V₂.valuation b < 1 → False :=
    fun core V hV hPV' hϖV' h1 h2 h3 h4 ↦ hη (CrossingTarget.centre_eq_of_branch (hdom y') hPg
      core hPV' hP₂ hϖV' h2 h1 hϖ₂V h4 h3 hV hV₂)
  suffices H : ∀ a b : L₂, NodeCore P ι₂ ϖ₂L a b n → V₁.valuation a = 1 →
      V₂.valuation b = 1 → V₂.valuation a < 1 →
      ∃ w : Walk c, w.v 0 = v₀ ∧ w.Crosses ψ y' ∧ ψ '' w.v (Fin.last w.k) = w₂' ∧
        ∃ m : ℕ, 0 < m ∧ ∀ i : Fin w.k, ∃ q q' : ℕ, q < q' ∧
          (Wc hW (w.mem_components i.castSucc)).valuation (ι a ^ m) =
            (Wc hW (w.mem_components i.castSucc)).valuation (algebraMap O₁ L₁ ϖ₁) ^ q ∧
          (Wc hW (w.mem_components i.succ)).valuation (ι a ^ m) =
            (Wc hW (w.mem_components i.succ)).valuation (algebraMap O₁ L₁ ϖ₁) ^ q' by
    rcases CrossingTarget.unit_or_unit (hdom y') hPg core₀ hP₁ hϖ₁V hV₁ hη₁ne with
      ⟨hu₁, hv₁⟩ | ⟨hv₁, hu₁⟩ <;>
    rcases CrossingTarget.unit_or_unit (hdom y') hPg core₀ hP₂ hϖ₂V hV₂ hη₂ne with
      ⟨hu₂, hv₂⟩ | ⟨hv₂, hu₂⟩
    · exact (hsame core₀ V₁ hV₁ hP₁ hϖ₁V hu₁ hv₁ hu₂ hv₂).elim
    · obtain ⟨w, h1, h2, h3, m, hm, hinc⟩ := H u v core₀ hu₁ hv₂ hu₂
      exact ⟨w, h1, h2, h3, u, m, .inl rfl, hm, hinc⟩
    · obtain ⟨w, h1, h2, h3, m, hm, hinc⟩ := H v u core₀.swap hv₁ hu₂ hv₂
      exact ⟨w, h1, h2, h3, v, m, .inr rfl, hm, hinc⟩
    · exact (hsame core₀.swap V₁ hV₁ hP₁ hϖ₁V hv₁ hu₁ hv₂ hu₂).elim
  intro a b core ha₁ hb₂ ha₂
  clear core₀
  -- the source data
  have hE₂ : algebraMap K L₁ ϖ₀ = ι (ι₂ μ₂ * ϖ₂L ^ e₂) := by
    rw [IsScalarTower.algebraMap_apply K L₂ L₁, IsScalarTower.algebraMap_apply K K₂ L₂, hμ₂,
      map_mul, map_pow]
    rfl
  have hE₁ : algebraMap K L₁ ϖ₀ = algebraMap O₁ L₁ μ₁ * ϖ₁L ^ e₁ := by
    rw [IsScalarTower.algebraMap_apply K K₁ L₁, hμ₁, map_mul, map_pow,
      IsScalarTower.algebraMap_apply O₁ K₁ L₁ (μ₁ : O₁),
      show ϖ₁L = algebraMap K₁ L₁ (ϖ₁ : K₁) from IsScalarTower.algebraMap_apply O₁ K₁ L₁ ϖ₁]
    rfl
  set t := ι a ^ e₂ with ht
  set μ₁' := algebraMap O₁ L₁ ↑μ₁⁻¹
  set s' := ι b ^ e₂ * ι (ι₂ μ₂) ^ n * μ₁' ^ n with hs'
  set N := e₁ * n
  have hn := core.one_le
  have hμ₁ : algebraMap O₁ L₁ μ₁ * μ₁' = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hE : ι (ι₂ μ₂) * ι ϖ₂L ^ e₂ = algebraMap O₁ L₁ μ₁ * ϖ₁L ^ e₁ := by
    rw [← map_pow, ← map_mul, ← hE₂, hE₁]
  have hkey : t * s' = ϖ₁L ^ N := by
    have hab : ι a * ι b = ι ϖ₂L ^ n := by rw [← map_mul, core.mul_eq, map_pow]
    calc t * s' = (ι a * ι b) ^ e₂ * ι (ι₂ μ₂) ^ n * μ₁' ^ n := by rw [ht, hs']; ring
      _ = (ι (ι₂ μ₂) * ι ϖ₂L ^ e₂) ^ n * μ₁' ^ n := by rw [hab]; ring
      _ = (algebraMap O₁ L₁ μ₁ * μ₁') ^ n * ϖ₁L ^ N := by rw [hE]; ring
      _ = ϖ₁L ^ N := by rw [hμ₁, one_pow, one_mul]
  -- germs at points over `y'`
  have hgS : ∀ z, (((stalkTo j (specializes_of_isWModel hW z)).hom.range : Subring L₁) :
      Set L₁) = germs c j z := fun z ↦ by
    rw [germs_eq_range c j (specializes_of_isWModel hW z), RingHom.coe_range]
  have hιg : ∀ z, ψ z = y' → ∀ f ∈ P,
      ι f ∈ (stalkTo j (specializes_of_isWModel hW z)).hom.range := fun z hz f hf ↦ by
      rw [← SetLike.mem_coe, hgS]
      exact germs_map ψ j j' hj z (by rw [hz, ← hPg]; exact hf)
  have hOg : ∀ z (o : O₁),
      algebraMap O₁ L₁ o ∈ (stalkTo j (specializes_of_isWModel hW z)).hom.range := fun z o ↦ by
    rw [← SetLike.mem_coe, hgS]; exact algebraMap_mem_germs hW z o
  have hM : ∀ z, ψ z = y' → t ∈ germs c j z ∧ ∃ r ∈ germs c j z, t * r = ϖ₁L ^ N := by
    intro z hz
    rw [← hgS z]
    exact ⟨pow_mem (hιg z hz a core.u_mem) _, s', mul_mem (mul_mem
      (pow_mem (hιg z hz b core.v_mem) _) (pow_mem (hιg z hz _ (core.base_mem _)) _))
      (pow_mem (hOg z _) _), hkey⟩
  have hι0 : ∀ f : L₂, f ≠ 0 → ι f ≠ 0 := fun f hf ↦ (map_ne_zero ι).2 hf
  have hμ₁inv : μ₁'⁻¹ = algebraMap O₁ L₁ μ₁ := (eq_inv_of_mul_eq_one_left hμ₁).symm
  have hμ₁0 : μ₁' ≠ 0 := fun h ↦ by rw [h, mul_zero] at hμ₁; exact zero_ne_one hμ₁
  -- valuations at generic points of components through points over `y'`
  have hfacts : ∀ (v : Set c.scheme) (hv : v ∈ components c) (W : ValuationSubring L₁),
      IsCentre j W (gp hv) → ∀ z ∈ v, ψ z = y' → (∀ f ∈ P, ι f ∈ W) ∧
        W.valuation t * W.valuation (ι b) ^ e₂ = W.valuation ϖ₁L ^ N ∧
        W.valuation ϖ₁L < 1 ∧ W.valuation (ι ϖ₂L) < 1 ∧
        W.valuation (algebraMap O₁ L₁ μ₁) = 1 := by
    intro v hv W hWc z hz hψz
    have hg : ∀ f ∈ (stalkTo j (specializes_of_isWModel hW z)).hom.range, f ∈ W :=
      fun f hf ↦ germs_le hW hWc (gp_specializes hv hz) f (by rw [← hgS]; exact hf)
    have hιW := fun f hf ↦ hg _ (hιg z hψz f hf)
    have hOW := fun o ↦ hg _ (hOg z o)
    have hu₂W : W.valuation (ι (ι₂ μ₂)) = 1 := valuation_unit (hι0 _ hμ₂0) (hιW _ hμ₂P.1)
      (by rw [← map_inv₀, hμ₂inv]; exact hιW _ hμ₂P.2)
    have hu₁W : W.valuation μ₁' = 1 :=
      valuation_unit hμ₁0 (hOW _) (by rw [hμ₁inv]; exact hOW _)
    have hu₁W' : W.valuation (algebraMap O₁ L₁ μ₁) = 1 := by
      rw [← hμ₁inv, map_inv₀, hu₁W, inv_one]
    have hϖW := valuation_ϖ_lt_one hW hϖ₁ (hv.2.1 (gp_mem hv)) hWc
    refine ⟨hιW, ?_, hϖW, ?_, hu₁W'⟩
    · have := congrArg W.valuation hkey
      simp only [hs', map_mul, map_pow, hu₂W, hu₁W, one_pow, mul_one] at this
      exact this
    · have := congrArg W.valuation hE
      rw [map_mul, map_mul, hu₂W, hu₁W', one_mul, one_mul, map_pow, map_pow] at this
      exact lt_one_of_pow_lt_one ((W.valuation_le_one_iff _).2 (hιW _ core.ϖ_mem))
        (this ▸ pow_lt_one₀ zero_le hϖW (by omega))
  have hϖ₁L0 : ϖ₁L ≠ 0 := by
    rw [show ϖ₁L = algebraMap K₁ L₁ (ϖ₁ : K₁) from IsScalarTower.algebraMap_apply O₁ K₁ L₁ ϖ₁]
    exact (map_ne_zero _).2 fun h ↦ hϖ₁.ne_zero (Subtype.ext h)
  have hb1 : ∀ W : ValuationSubring L₁, (∀ f ∈ P, ι f ∈ W) → W.valuation (ι b) ≤ 1 :=
    fun W hιW ↦ (W.valuation_le_one_iff _).2 (hιW b core.v_mem)
  -- bound on positions
  have hbound : ∀ (v : Set c.scheme) (hv : v ∈ components c) (W : ValuationSubring L₁),
      IsCentre j W (gp hv) → ∀ z ∈ v, ψ z = y' → ∀ p : ℕ,
        W.valuation t = W.valuation ϖ₁L ^ p → p ≤ N := by
    intro v hv W hWc z hz hψz p hp
    obtain ⟨hιW, hprod, hϖW, -, -⟩ := hfacts v hv W hWc z hz hψz
    rw [hp] at hprod
    have hle : W.valuation ϖ₁L ^ N ≤ W.valuation ϖ₁L ^ p :=
      hprod ▸ mul_le_of_le_one_right' (pow_le_one₀ zero_le (hb1 W hιW))
    have h0 : W.valuation ϖ₁L ≠ 0 := by simpa using hϖ₁L0
    exact (pow_le_pow_iff_right_of_lt_one₀ (zero_lt_iff.2 h0) hϖW).1 hle
  -- components of position in `(0, N)` are contracted
  have hφ₂ : (ι.comp (algebraMap K₂ L₂)).comp (algebraMap K K₂) = algebraMap K L₁ :=
    RingHom.ext fun k ↦ by
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply K K₂ L₂, ← IsScalarTower.algebraMap_apply K L₂ L₁]
  have hKO : ∀ o : O, algebraMap K L₁ o = algebraMap O₁ L₁
      ((algebraMap K K₁).restrict O O₁ (fun y hy ↦ by rw [← h₁] at hy; exact hy) o) := fun o ↦ by
    rw [IsScalarTower.algebraMap_apply K K₁ L₁, IsScalarTower.algebraMap_apply O₁ K₁ L₁]
    rfl
  have hcontr : ∀ (v : Set c.scheme) (hv : v ∈ components c) (W : ValuationSubring L₁),
      IsCentre j W (gp hv) → ∀ z ∈ v, ψ z = y' → ∀ p : ℕ,
        W.valuation t = W.valuation ϖ₁L ^ p → 0 < p → p < N → ψ '' v = {y'} := by
    intro v hv W hWc z hz hψz p hp hp0 hpN
    obtain ⟨hιW, hprod, hϖW, hϖ₂W, hμ₁W⟩ := hfacts v hv W hWc z hz hψz
    have h0 : W.valuation ϖ₁L ≠ 0 := by simpa using hϖ₁L0
    have haW : W.valuation (ι a) < 1 := by
      refine lt_one_of_pow_lt_one ((W.valuation_le_one_iff _).2 (hιW a core.u_mem)) (e := e₂) ?_
      rw [← map_pow, ← ht, hp]; exact pow_lt_one₀ zero_le hϖW (by omega)
    have hbW : W.valuation (ι b) < 1 := by
      refine lt_one_of_pow_lt_one (hb1 W hιW) (e := e₂) ?_
      have e : W.valuation ϖ₁L ^ p * W.valuation (ι b) ^ e₂ =
          W.valuation ϖ₁L ^ p * W.valuation ϖ₁L ^ (N - p) := by
        rw [← pow_add, Nat.add_sub_cancel' hpN.le, ← hprod, hp]
      rw [mul_left_cancel₀ (pow_ne_zero _ h0) e]
      exact pow_lt_one₀ zero_le hϖW (by omega)
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨z, hz, hψz⟩, ?_⟩
    rintro _ ⟨z', hz', rfl⟩
    obtain ⟨R, hRW, hRz⟩ := exists_le_centre hW (gp_specializes hv hz') hWc
    have hRg : ∀ f ∈ germs c j z', f ∈ R := fun f hf ↦
      ((isCentre_iff_dominates c j (specializes_of_isWModel hW z') R).1 hRz).1 hf
    have hRϖ₁ : R.valuation ϖ₁L < 1 := valuation_ϖ_lt_one hW hϖ₁ (hv.2.1 hz') hRz
    have hRK : ∀ o : O, algebraMap K L₁ o ∈ R := fun o ↦ by
      rw [hKO]; exact hRg _ (algebraMap_mem_germs hW z' _)
    have hRϖ : R.valuation (algebraMap K L₁ ϖ₀) < 1 := by
      rw [hE₁, map_mul, map_pow]
      exact (mul_le_of_le_one_left' ((R.valuation_le_one_iff _).2
        (hRg _ (algebraMap_mem_germs hW z' _)))).trans_lt (pow_lt_one₀ zero_le hRϖ₁ (by omega))
    have hO₂R := mem_of_base h₂ hϖ₀ (ι.comp (algebraMap K₂ L₂)) hφ₂ hRK hRϖ
    have hlt : ∀ f, W.valuation f < 1 → R.valuation f < 1 :=
      fun f hf ↦ CompositeValuation.valuation_lt_one_of_le hRW hf
    have hRm : ∀ f, W.valuation f < 1 → f ∈ R := fun f hf ↦
      (R.valuation_le_one_iff _).1 (hlt f hf).le
    have hPR : P ≤ (R.comap ι).toSubring := by
      intro f hf
      obtain ⟨o, a', ha', b', hb', c'', hc'', rfl⟩ := core.gen f hf
      change ι _ ∈ R
      have hsmall : ∀ g g' : L₂, W.valuation (ι g) < 1 → g' ∈ P → W.valuation (ι (g * g')) < 1 :=
        fun g g' hg hg' ↦ by
          rw [map_mul, map_mul]
          exact (mul_le_of_le_one_right' ((W.valuation_le_one_iff _).2 (hιW g' hg'))).trans_lt hg
      simp only [map_add]
      refine add_mem (add_mem (add_mem (hO₂R o) (hRm _ (hsmall _ _ hϖ₂W ha')))
        (hRm _ (hsmall _ _ haW hb'))) (hRm _ (hsmall _ _ hbW hc''))
    have hcy := CrossingTarget.isCentre_of_lt_one (hdom y') hPg core hPR
      ((valuation_comap_lt_one_iff _ _).2 (hlt _ hϖ₂W))
      ((valuation_comap_lt_one_iff _ _).2 (hlt _ haW))
      ((valuation_comap_lt_one_iff _ _).2 (hlt _ hbW))
    exact centre_unique c'.toSpec (IsCentre.comap j j' ψ hj hRz) hcy
  -- components of position `N` lie over `w₂'`
  have hend : ∀ (v : Set c.scheme) (hv : v ∈ components c) (W : ValuationSubring L₁),
      IsCentre j W (gp hv) → ∀ z ∈ v, ψ z = y' →
        W.valuation t = W.valuation ϖ₁L ^ N → ψ '' v = w₂' := by
    intro v hv W hWc z hz hψz hp
    obtain ⟨hιW, hprod, hϖW, hϖ₂W, hμ₁W⟩ := hfacts v hv W hWc z hz hψz
    have h0 : W.valuation ϖ₁L ≠ 0 := by simpa using hϖ₁L0
    have haW : W.valuation (ι a) < 1 := by
      refine lt_one_of_pow_lt_one ((W.valuation_le_one_iff _).2 (hιW a core.u_mem)) (e := e₂) ?_
      rw [← map_pow, ← ht, hp]; exact pow_lt_one₀ zero_le hϖW (by positivity)
    have hbW : W.valuation (ι b) = 1 := by
      refine eq_one_of_pow_eq_one (hb1 W hιW) he₂ ?_
      have e : W.valuation ϖ₁L ^ N * W.valuation (ι b) ^ e₂ = W.valuation ϖ₁L ^ N * 1 := by
        calc W.valuation ϖ₁L ^ N * W.valuation (ι b) ^ e₂ =
              W.valuation t * W.valuation (ι b) ^ e₂ := by rw [hp]
          _ = W.valuation ϖ₁L ^ N * 1 := by rw [hprod, mul_one]
      exact mul_left_cancel₀ (pow_ne_zero _ h0) e
    have hVc := IsCentre.comap j j' ψ hj hWc
    have hPW : P ≤ (W.comap ι).toSubring := fun f hf ↦ hιW f hf
    have hψη : ψ (gp hv) = gp hw₂ := CrossingTarget.centre_eq_of_branch (hdom y') hPg core.swap
      hPW hP₂ ((valuation_comap_lt_one_iff _ _).2 hϖ₂W) ((valuation_comap_lt_one_iff _ _).2 haW)
      ((valuation_comap_eq_one_iff _ _ _).2 hbW) hϖ₂V ha₂ hb₂ hVc hV₂
    rw [hψη] at hVc
    refine Set.Subset.antisymm ?_ fun y'' hy'' ↦ ?_
    · rintro _ ⟨z', hz', rfl⟩
      rw [← closure_gp hw₂, ← specializes_iff_mem_closure, ← hψη]
      exact (gp_specializes hv hz').map ψ.continuous
    · have hη₂y'' := gp_specializes hw₂ hy''
      have hs := hdom y''
      have hφW : ∀ s, ι ((stalkTo j' hs).hom s) ∈ W := fun s ↦
        ((isCentre_iff_dominates c' j' (hdom _) _).1 hVc).1
          (germs_anti c' j' hη₂y'' (by rw [germs_eq_range c' j' hs]; exact ⟨s, rfl⟩))
      obtain ⟨R, hRW, hRφ, hRloc⟩ := CompositeValuation.exists_le_dominates W
        (ι.comp (stalkTo j' hs).hom) hφW
      have hR'' : IsCentre j' (R.comap ι) y'' := (isCentre_iff j' hs _).2
        ⟨fun s ↦ hRφ s, fun s hs' ↦ (valuation_comap_lt_one_iff _ _).2 (hRloc s hs')⟩
      have hRK : ∀ o : O, algebraMap K L₁ o ∈ R := fun o ↦ by
        rw [IsScalarTower.algebraMap_apply K L₂ L₁, ← hbase]
        have hmem := baseHom_mem_germs c' j' y''
          ((algebraMap K K₂).restrict O O₂ (fun y hy ↦ by rw [← h₂] at hy; exact hy) o)
        rw [germs_eq_range c' j' hs] at hmem
        obtain ⟨s, hs'⟩ := hmem
        rw [← hs']; exact hRφ s
      have hRϖ : R.valuation (algebraMap K L₁ ϖ₀) < 1 := by
        refine CompositeValuation.valuation_lt_one_of_le hRW ?_
        rw [hE₁, map_mul, hμ₁W, one_mul, map_pow]
        exact pow_lt_one₀ zero_le hϖW (by omega)
      have hO₁R : ∀ o : O₁, algebraMap O₁ L₁ o ∈ R := fun o ↦ by
        rw [IsScalarTower.algebraMap_apply O₁ K₁ L₁]
        exact mem_of_base h₁ hϖ₀ (algebraMap K₁ L₁)
          (RingHom.ext fun k ↦ (IsScalarTower.algebraMap_apply K K₁ L₁ k).symm) hRK hRϖ o
      obtain ⟨z'', hz''⟩ := exists_centre hW hO₁R
      refine ⟨z'', ?_, centre_unique c'.toSpec (IsCentre.comap j j' ψ hj hz'') hR''⟩
      rw [← closure_gp hv, ← specializes_iff_mem_closure]
      exact centre_specializes hRW hz'' hWc
  -- the start
  have hnot : ∀ (w' : Set c'.scheme) (hw' : w' ∈ components c'), y' ∈ w' → ∀ y, w' ≠ {y} :=
    fun w' hw' hy y h ↦ gp_ne_of_two hw' hw₁ hw₂ hne hy₁ hy₂
      ((Set.mem_singleton_iff.1 (h ▸ gp_mem hw')).trans (Set.mem_singleton_iff.1 (h ▸ hy)).symm)
  have hv₀c : ¬ IsContracted' ψ v₀ := by
    rintro ⟨y, hy⟩; rw [hψv₀] at hy; exact hnot w₁' hw₁ hy₁ y hy
  have hψη₁ : ψ (gp hv₀) = gp hw₁ :=
    map_genericPoint ψ (by rw [closure_gp hv₀, closure_gp hw₁, hψv₀])
  have hstart : (Wc hW hv₀).valuation t = 1 := by
    have hVc := IsCentre.comap j j' ψ hj (Wc_spec hW hv₀)
    rw [hψη₁] at hVc
    have hP₀ := hPV _ hη₁y _ hVc
    have hϖ₀V := hϖV _ (hw₁.2.1 (gp_mem hw₁)) _ hVc hP₀
    rcases CrossingTarget.unit_or_unit (hdom y') hPg core hP₀ hϖ₀V hVc hη₁ne with
      ⟨ha, -⟩ | ⟨hb, ha⟩
    · have := (valuation_comap_eq_one_iff _ _ _).1 ha
      rw [ht, map_pow]
      change (Wc hW hv₀).valuation (algebraMap L₂ L₁ a) ^ e₂ = 1
      rw [this, one_pow]
    · exact (hsame core.swap _ hVc hP₀ hϖ₀V hb ha hb₂ ha₂).elim
  obtain ⟨z₀, hz₀, hψz₀⟩ : y' ∈ ψ '' v₀ := hψv₀ ▸ hy₁
  have hR₀ : ∀ R : ValuationSubring L₁, IsCentre j R z₀ → R.valuation t < 1 := by
    intro R hR
    have hRc := IsCentre.comap j j' ψ hj hR
    rw [hψz₀] at hRc
    obtain ⟨-, hdomR⟩ := CrossingTarget.le_of_isCentre (hdom y') hPg hRc
    have := (valuation_comap_lt_one_iff _ _).1 (hdomR a core.u_mem core.u_nonunit)
    rw [ht, map_pow]
    exact pow_lt_one₀ zero_le this (by omega)
  obtain ⟨w, h1, h2, h3, hinc⟩ := exists_walk hW hϖ₁ hsplit hloops ψ y' w₂' t N
    (Nat.mul_pos he₁ hn) hM hbound hcontr hend (hnot w₂' hw₂ hy₂) hv₀ hv₀c hstart hz₀ hψz₀ hR₀
  exact ⟨w, h1, h2, h3, e₂, he₂, hinc⟩

/-- **`Statement.CrossingX1S` holds.** -/
theorem crossingX1S : Statement.CrossingX1S.{u} := by
  intro K _ _ O _ _ K₁ K₂ _ _ _ _ _ _ O₁ O₂ h₁ h₂ _ _ ϖ₁ ϖ₂ hϖ₁ hϖ₂ L₁ L₂ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ x c c' ψ j j' hunf hj hψO hsplit0 hloops hdense y' w₁' w₂' hw₁ hw₂ hne hy₁ hy₂ hP
    v₀ hv₀ hψv₀
  obtain ⟨P, u, v, n, hPg, hG, hu, hv⟩ := hP
  obtain ⟨w, h1, h2, h3, -⟩ := crossingX1_inc K O K₁ K₂ O₁ O₂ h₁ h₂ ϖ₁ ϖ₂ hϖ₁ hϖ₂ L₁ L₂ x c c'
    ψ j j' hunf hj hψO hsplit0 hloops hdense y' w₁' w₂' hw₁ hw₂ hne hy₁ hy₂ P u v n hPg hG hu hv
    v₀ hv₀ hψv₀
  exact ⟨w, h1, h2, h3⟩

/-- **`Statement.CrossingX1` holds** (from `CrossingX1S`). -/
theorem crossingX1 : Statement.CrossingX1.{u} := by
  intro K _ _ O _ _ K₁ K₂ _ _ _ _ _ _ O₁ O₂ h₁ h₂ _ _ ϖ₁ ϖ₂ hϖ₁ hϖ₂ L₁ L₂ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ x c c' ψ j j' hunf hj hψO hsplit0 hloops
  exact crossingX1S K O K₁ K₂ O₁ O₂ h₁ h₂ ϖ₁ ϖ₂ hϖ₁ hϖ₂ L₁ L₂ x c c' ψ j j' hunf hj hψO hsplit0.1
    hloops

end TemperedFundamentalGroups.SemistableReduction
