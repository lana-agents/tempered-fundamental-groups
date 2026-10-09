/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.UnfoldedNode

/-!
# Nodes of unfolded W-models (Blueprint §9.7, XL6): the main statement

`exists_unfoldedNodeGerm`: at a node `y` of an unfolded split W-model without loops, the germs
form an `UnfoldedNodeGerm` (coordinates `u v = ϖ ^ n` coming from sections near `y`) whose branch
valuations are the centre valuations of the two components through `y`, together with the divisor
lemma for its coordinates.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial

namespace TemperedFundamentalGroups.SemistableReduction

/-- The x-line coordinate is the image of `X`. -/
lemma xLineAlgebra_X {K L : Type u} [Field K] [Field L] [Algebra K L] {x : L}
    (hx : Transcendental K x) :
    letI := xLineAlgebra L hx
    algebraMap (RatFunc K) L RatFunc.X = x := by
  letI := xLineAlgebra L hx
  change RatFunc.liftAlgHom _ _ RatFunc.X = x
  have := RatFunc.liftAlgHom_apply_div (aeval x : K[X] →ₐ[K] L) (fun p hp ↦ by
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, ne_eq] at hp ⊢
    exact fun h ↦ hp ((injective_iff_map_eq_zero _).mp
      (transcendental_iff_injective.mp hx) p h)) X 1
  rw [map_one, div_one, map_one, div_one, aeval_X, RatFunc.algebraMap_X] at this
  exact this

namespace CrossingSource

open CentreGerms ValuativeCentre ModelCode _root_.SemistableReduction

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [Algebra O L] [IsScalarTower O K L] {x : L}
  {c : TemperedFundamentalGroups.ModelCode O} {j : Spec (CommRingCat.of L) ⟶ c.scheme}

/-- **Nodes of unfolded W-models are unfolded node germs** (XL6). -/
theorem exists_unfoldedNodeGerm (hU : IsUnfolded O x c j) {ϖ : O} (hϖ : Irreducible ϖ)
    (hsplit : HasSplitNodes ϖ c) (hloops : NoLoops c) {y : c.scheme} (hy : IsNodePt c y) :
    ∃ (P : Subring L) (u v : L) (n : ℕ) (a β : K) (e α : ℕ) (ε : L) (v₁ v₂ : Set c.scheme)
      (hv₁ : v₁ ∈ components c) (hv₂ : v₂ ∈ components c),
      UnfoldedNodeGerm O ϖ P u v n x a β e α ε (Wc hU.isWModel hv₁) (Wc hU.isWModel hv₂) ∧
      NodeBranches O ϖ P (algebraMap O L) u v n (Wc hU.isWModel hv₁) (Wc hU.isWModel hv₂) ∧
      (P : Set L) = germs c j y ∧ y ∈ v₁ ∧ y ∈ v₂ ∧ NodeGerm O ϖ P v u n ∧
      (∀ s : ℚ, 0 < s → s < n → ∃ U : ValuationSubring L,
        IsMonomialPt O (P : Set L) (algebraMap K L (ϖ : K)) u s U) ∧
      (∀ t ∈ P, ∀ M : ℕ, (∃ r ∈ P, t * r = algebraMap O L ϖ ^ M) →
        ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ, t = ε * algebraMap O L ϖ ^ α * u ^ e ∨
          t = ε * algebraMap O L ϖ ^ α * v ^ e) ∧
      ∃ (V : c.scheme.Opens) (hyV : y ∈ V) (hV : ⊤ ≤ j ⁻¹ᵁ V) (su sv : Γ(c.scheme, V)),
        letI := sectionsAlgebra c V
        su * sv = algebraMap O Γ(c.scheme, V) (ϖ ^ n) ∧
        ¬ IsUnit ((c.scheme.presheaf.germ V y hyV).hom su) ∧
        ¬ IsUnit ((c.scheme.presheaf.germ V y hyV).hom sv) ∧ toL j hV su = u := by
  classical
  have hW := hU.isWModel
  obtain ⟨P, u, v, n, hG, hn, -, hPg, ⟨hloc, hϖm, hum, hvm⟩, hutr, ⟨φN, hflat, himg, hφO, hφu, -⟩,
    hsec, hODP⟩ := exists_nodeGerm hϖ hW hsplit hloops hy
  haveI := hloc
  haveI := hODP.isNoetherianRing
  have hϖL : algebraMap O L ϖ = algebraMap K L (ϖ : K) := IsScalarTower.algebraMap_apply O K L ϖ
  have hι : (algebraMap K L).comp O.subtype = algebraMap O L :=
    RingHom.ext fun o ↦ (IsScalarTower.algebraMap_apply O K L o).symm
  have hnu : ∀ s (hs : s ∈ P), (⟨s, hs⟩ : P) ∈ maximalIdeal P → ∀ w ∈ P, s * w ≠ 1 :=
    fun s hs hm w hw h1 ↦ hm (isUnit_iff_exists_inv.2 ⟨⟨w, hw⟩, Subtype.ext h1⟩)
  have hcore := NodeCore.of_nodeGerm hG hϖ (hnu u hG.u_mem hum) (hnu v hG.v_mem hvm)
  rw [hι, ← hϖL] at hcore
  have hdiv : ∀ t ∈ P, ∀ M : ℕ, (∃ r ∈ P, t * r = algebraMap O L ϖ ^ M) →
      ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ, t = ε * algebraMap O L ϖ ^ α * u ^ e ∨
        t = ε * algebraMap O L ϖ ^ α * v ^ e := fun t ht M hM ↦ by
    rw [hϖL] at hM ⊢; exact hODP.divisor hϖ hn ht hM
  obtain ⟨v₁, v₂, hv₁, hv₂, hy₁, hy₂, HB⟩ :=
    exists_nodeBranches_of_core hW hϖ hloops hy hPg hcore
  obtain ⟨V, hyV, hV, su, sv, hsuv, hsu, hsv, hsuL, hsvL⟩ := hsec
  -- a valuation dominating the germs
  obtain ⟨R, -, hR⟩ := exists_le_centre hW (gp_specializes hv₁ hy₁) (Wc_spec hW hv₁)
  have hdomR := (isCentre_iff_dominates c j (specializes_of_isWModel hW y) R).1 hR
  -- the Gauss tree
  obtain ⟨hx, ι, _, _, a, b, hWof, hconv, hred, hnode⟩ := id hU
  letI := xLineAlgebra L hx
  haveI : IsScalarTower K (RatFunc K) L := IsScalarTower.of_algebraMap_eq fun k ↦ by
    change algebraMap K L k = RatFunc.liftAlgHom _ _ (algebraMap K (RatFunc K) k)
    rw [AlgHom.commutes]
  obtain ⟨halgx, hb, -⟩ := id hWof
  have hvtr : Transcendental K v := by
    intro hvalg
    apply hutr
    have hv0 : v ≠ 0 := HB.v_ne_zero
    have e1 : u = algebraMap K L ((ϖ : K) ^ n) * v⁻¹ := by
      rw [map_pow, ← hG.mul_eq, mul_inv_cancel_right₀ hv0]
    rw [e1]
    exact (isAlgebraic_algebraMap _).mul hvalg.inv
  have halgv : Algebra.IsAlgebraic (Algebra.adjoin K {v}) L :=
    isAlgebraic_adjoin_of_transcendental hx (isAlgebraic_adjoin_of_ratFunc hx halgx) hvtr
  have hint : ∀ s : ℚ, 0 < s → s < n → ∃ U : ValuationSubring L,
      IsMonomialPt O (P : Set L) (algebraMap K L (ϖ : K)) u s U := by
    intro s hs0 hsn
    letI := φN.toAlgebra
    haveI := hflat
    exact hG.exists_isMonomialPt hϖ hutr hϖm hum hvm (A := Node O (ϖ ^ n)) himg
      (fun o ↦ ⟨algebraMap O _ o, hφO o⟩) ⟨Node.u _, hφu⟩ hs0 hsn
  have hintv : ∀ s : ℚ, 0 < s → s < n → ∃ U : ValuationSubring L,
      IsMonomialPt O (P : Set L) (algebraMap K L (ϖ : K)) v s U := by
    intro s hs0 hsn
    obtain ⟨U, hU⟩ := hint (n - s) (by linarith) (by linarith)
    exact ⟨U, (isMonomialPt_swap_iff HB.base HB.core HB.irred).2 hU⟩
  obtain ⟨hV₀, hcen⟩ := center_subset_germs hx hWof hPg hdomR
  obtain ⟨W₁', hW₁', W₂', hW₂', hne, hsub⟩ := hnode y hy
  have hsub' : ∀ f : RatFunc K, algebraMap (RatFunc K) L f ∈ P → f ∈ W₁' ∧ f ∈ W₂' :=
    fun f hf ↦ hsub f (hPg ▸ hf)
  have hle₁ := fun f hf ↦ (hsub' f (hcen f hf)).1
  have hle₂ := fun f hf ↦ (hsub' f (hcen f hf)).2
  have hϖ0 : (ϖ : K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hϖv : O.valuation (ϖ : K) < 1 := (O.valuation_lt_one_iff ϖ).1 hϖ.not_isUnit
  obtain ⟨jj, m, Wt, Ws, hbj, hbm, hc'1, ht, hs, hWW⟩ :=
    exists_nodeChart_of_two_vertices hb hconv hred (rank_le_one O) ⟨ϖ, hϖ0, hϖv⟩ hV₀ hW₁' hW₂'
      hne hle₁ hle₂
  set φ := algebraMap (RatFunc K) L with hφ
  set t := GaussTree.coord (RatFunc.X : RatFunc K) (a jj) (b m) with ht_def
  set c' := b jj / b m with hc'_def
  have ht0 : t ≠ 0 := (isGaussCoord_coord (v := O.valuation) (a := a jj) hbm).ne_zero
  have hc'0 : c' ≠ 0 := div_ne_zero hbj hbm
  have hTP : φ t ∈ P := hcen _ ht
  have hSP : φ (algebraMap K (RatFunc K) c' / t) ∈ P := hcen _ hs
  have hunit : ∀ f : RatFunc K, f ≠ 0 → φ f ∈ P → φ f⁻¹ ∈ P →
      W₁'.valuation f = 1 ∧ W₂'.valuation f = 1 := fun f hf0 hf hfi ↦
    ⟨valuation_eq_one_of_mem_of_inv_mem hf0 (hsub' f hf).1 (hsub' _ hfi).1,
      valuation_eq_one_of_mem_of_inv_mem hf0 (hsub' f hf).2 (hsub' _ hfi).2⟩
  have hW₁ := hWW W₁' hW₁' hle₁
  have hW₂ := hWW W₂' hW₂' hle₂
  have hTnu : ∀ w ∈ P, φ t * w ≠ 1 := by
    intro w hw h1
    have hw' : w = φ t⁻¹ := by rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right h1
    obtain ⟨h₁, h₂⟩ := hunit t ht0 hTP (hw' ▸ hw)
    exact hne ((hW₁.2.1 h₁).trans (hW₂.2.1 h₂).symm)
  -- `c' = η ϖ ^ M`
  have hc'O : c' ∈ O := (O.valuation_le_one_iff c').1 hc'1.le
  obtain ⟨M, η, hη⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨c', hc'O⟩ : O)) (fun h ↦ hc'0 (congrArg Subtype.val h)) hϖ
  have hc'eq : c' = ((η : O) : K) * (ϖ : K) ^ M := by
    have := congrArg Subtype.val hη
    simpa using this
  have hTS : φ t * (φ (algebraMap K (RatFunc K) c' / t) * algebraMap O L ↑η⁻¹) =
      algebraMap O L ϖ ^ M := by
    have h1 : φ t * φ (algebraMap K (RatFunc K) c' / t) = algebraMap K L c' := by
      rw [← map_mul, mul_div_cancel₀ _ ht0, ← IsScalarTower.algebraMap_apply]
    have h2 : algebraMap O L ↑η * algebraMap O L ↑η⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [← mul_assoc, h1, hc'eq, map_mul, map_pow, algebraMap_O_K, algebraMap_O_K,
      mul_comm (algebraMap O L _) _, mul_assoc, h2, mul_one]
  obtain ⟨ε, hε, hεi, α, e, hT⟩ := hdiv (φ t) hTP M
    ⟨_, mul_mem hSP (hcore.base_mem _), hTS⟩
  have hφt0 : φ t ≠ 0 := (map_ne_zero φ).2 ht0
  have hε0 : ε ≠ 0 := by
    rintro rfl
    rcases hT with h | h <;> simp [h] at hφt0
  have he : ∀ w : L, φ t = ε * algebraMap O L ϖ ^ α * w ^ e → 1 ≤ e := by
    intro w hTw
    by_contra h0
    have he0 : e = 0 := by omega
    rw [he0, pow_zero, mul_one] at hTw
    have hϖα : algebraMap K (RatFunc K) ((ϖ : K) ^ α) ≠ 0 := by simp [hϖ0]
    set f₀ := t / algebraMap K (RatFunc K) ((ϖ : K) ^ α)
    have hf₀ : φ f₀ = ε := by
      have hϖL0 : algebraMap O L ϖ ≠ 0 := by rw [hϖL]; simp [hϖ0]
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, hTw, map_pow, ← hϖL]
      field_simp
    have hf₀0 : f₀ ≠ 0 := div_ne_zero ht0 hϖα
    obtain ⟨h₁, h₂⟩ := hunit f₀ hf₀0 (hf₀ ▸ hε) (by rw [map_inv₀, hf₀]; exact hεi)
    rcases Nat.eq_zero_or_pos α with hα | hα
    · apply hTnu ε⁻¹ hεi
      rw [hTw, hα, pow_zero, mul_one, mul_inv_cancel₀ hε0]
    · have hlt : ∀ W' : ValuationSubring (RatFunc K),
          W' ∈ (gaussJoinModel O.valuation a b).vertexSet → W'.valuation f₀ = 1 →
          W'.valuation t ≠ 1 := by
        intro W' hW' hf1 h1
        have e1 : t = f₀ * algebraMap K (RatFunc K) ((ϖ : K) ^ α) := by
          rw [div_mul_cancel₀ _ hϖα]
        rw [e1, map_mul, hf1, one_mul] at h1
        have := (GaussTree.valuation_algebraMap_lt_one_iff hW'.1).2
          (show O.valuation ((ϖ : K) ^ α) < 1 by
            rw [map_pow]; exact pow_lt_one₀ zero_le hϖv (by omega))
        rw [h1] at this
        exact lt_irrefl _ this
      have hS₁ := hW₁.1.resolve_left (hlt W₁' hW₁' h₁)
      have hS₂ := hW₂.1.resolve_left (hlt W₂' hW₂' h₂)
      exact hne ((hW₁.2.2 hS₁).trans (hW₂.2.2 hS₂).symm)
  have hφt : φ t = (x - algebraMap K L (a jj)) / algebraMap K L (b m) := by
    simp only [t, GaussTree.coord, map_div₀, map_sub, xLineAlgebra_X hx, φ,
      ← IsScalarTower.algebraMap_apply]
  have hbmL : algebraMap K L (b m) ≠ 0 := by simpa using hbm
  have hcoord : ∀ w : L, φ t = ε * algebraMap O L ϖ ^ α * w ^ e →
      x - algebraMap K L (a jj) =
        algebraMap K L (b m) * (ε * w ^ e * algebraMap K L (ϖ : K) ^ α) := by
    intro w hTw
    have := hφt.symm.trans hTw
    rw [div_eq_iff hbmL] at this
    rw [this, hϖL]
    ring
  rcases hT with hT | hT
  · exact ⟨P, u, v, n, a jj, b m, e, α, ε, v₁, v₂, hv₁, hv₂,
      unfoldedNodeGerm_of hW hϖ hG hn hPg hv₁ hv₂ hy₁ hy₂ HB hbm (he u hT) hε0 hε hεi
        (hcoord u hT), HB, hPg, hy₁, hy₂, hG.swap' halgv, hint, hdiv, V, hyV, hV, su, sv, hsuv,
        hsu, hsv, hsuL⟩
  · refine ⟨P, v, u, n, a jj, b m, e, α, ε, v₂, v₁, hv₂, hv₁,
      unfoldedNodeGerm_of hW hϖ (hG.swap' halgv) hn hPg hv₂ hv₁ hy₂ hy₁ HB.swap hbm (he v hT)
        hε0 hε hεi (hcoord v hT), HB.swap, hPg, hy₂, hy₁, hG, hintv,
      fun t ht M hM ↦ ?_, V, hyV, hV, sv, su, by rw [mul_comm]; exact hsuv, hsv, hsu, hsvL⟩
    obtain ⟨ε', hε', hεi', α', e', h⟩ := hdiv t ht M hM
    exact ⟨ε', hε', hεi', α', e', h.symm⟩

end CrossingSource

end TemperedFundamentalGroups.SemistableReduction
