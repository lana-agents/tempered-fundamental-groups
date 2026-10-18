/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelTowerMk
import TemperedFundamentalGroups.SemistableReduction.QuadNodePatch
import TemperedFundamentalGroups.SemistableReduction.QuadNodeLevel

/-!
# The tower of levels of the quadratic node chart (Blueprint §12.8, M2.3, Tate case)

The quadratic node chart `R̄ = QuadNode.R π e c D` over the node ring `A π e = O[u,v]/(uv − π^e)`
of the base `O` is the Tate chart near the nodes. Its levels are `R n = R̄/ϖⁿ⁺¹R̄`
(`QuadNodeTower.Rn`), with the surjections `R (n+1) → R n` (`Ideal.Quotient.factor`), all
`O`-algebras and algebras over `A π e`. For `θ : O → k` surjective with `θ ϖ = 0`:

* `QuadNodeTower.eqv n : R̄/J ≃ₐ[k] R n/J` (`J = (ker θ)·`, built from `Ideal.quotientMap` and
  `Ideal.Quotient.lift`), compatible with the surjections (`he`) and with `f = u + v` (`hfe`), so
  every level carries the transport of one admissible covering `cov₀` of the special fibre `R̄/J`;
* `QuadNodeTower.hatEquiv_bar`, `φT_eq`: the transport isomorphisms of the completions are the
  identity on images of elements of `R̄`, so the transported node coordinates are those of `R n`;
* node coordinates `χn` (`NodeChart.χ` at every level, `hcχ`), the coordinate `tn` at the marked
  points (`hct`), **`kflat`** (the node coordinates at level `n` are flat modulo `ϖⁿ⁺¹`), `hreg`,
  `hJ` (`J^{n+1} = 0` if `ker θ ⊆ (ϖ)`);
* **`QuadNodeTower.tower`**: the tower data (`LevelTower.Data`) of an admissible covering `cov₀` of
  the special fibre of `R̄`, with patched algebras `G n` and transition maps `tr n : G (n+1) → G n`;
  `ker_succ` (`ker (R (n+1) → R n) = ϖⁿ⁺¹ R (n+1)`) and `kill` (`ϖⁿ⁺¹ R n = 0`). The generic
  statements apply to `tower` directly: `(tower ..).surjective_tr`, `(tower ..).ker_tr_of
  (ker_succ ..)` (kernel `ϖⁿ⁺¹ G (n+1)`), `(tower ..).spec` (level-`n` patching), and
  `(tower ..).ker_trLe (ker_succ ..) (kill ..)` (`LevelTowerSystem`). (Restating them here with
  `type_of%` makes writing the `.olean` extremely slow, so they are not restated.)
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

noncomputable section

namespace NodeChart

lemma χ_apply {O : Type u} [CommRing O] {π : O} {e : ℕ} {R : Type u} [CommRing R] [Algebra O R]
    [Algebra (A π e) R] [IsScalarTower O (A π e) R] {π' : O} {e' : ℕ} (h : π' ^ e' = π ^ e)
    (a : A π' e') :
    χ R h a = algebraMap (A π e) (FormalPatchLevel.Hat (fR (π := π) (e := e) R))
      (Node.congrEq h a) := rfl

end NodeChart

namespace QuadNodeTower

variable {O : Type u} [CommRing O] (ϖ : O) (π : O) (e : ℕ) (c D : A π e)

/-- The base chart `R̄`. -/
abbrev Rb : Type u := QuadNode.R π e c D

/-- The ideal `ϖⁿ⁺¹` of the base. -/
abbrev Iv (n : ℕ) : Ideal O := Ideal.span {ϖ} ^ (n + 1)

lemma Iv_le (n : ℕ) : Iv ϖ (n + 1) ≤ Iv ϖ n := Ideal.pow_le_pow_right (Nat.le_succ _)

/-- The ideal `ϖⁿ⁺¹ R̄`. -/
abbrev IRb (n : ℕ) : Ideal (Rb π e c D) := (Iv ϖ n).map (algebraMap O (Rb π e c D))

/-- **The level-`n` chart** `R n = R̄/ϖⁿ⁺¹R̄`. -/
def Rn (n : ℕ) : Type u := Rb π e c D ⧸ IRb ϖ π e c D n

instance (n : ℕ) : CommRing (Rn ϖ π e c D n) := Ideal.Quotient.commRing _

instance (n : ℕ) : Algebra (A π e) (Rn ϖ π e c D n) := Ideal.Quotient.algebra _

instance (n : ℕ) : Algebra O (Rn ϖ π e c D n) := Ideal.Quotient.algebra _

instance (n : ℕ) : Algebra (Rb π e c D) (Rn ϖ π e c D n) := Ideal.Quotient.algebra _

instance (n : ℕ) : IsScalarTower O (A π e) (Rn ϖ π e c D n) :=
  IsScalarTower.of_algebraMap_eq fun o ↦ by
    change Ideal.Quotient.mk _ (algebraMap O (Rb π e c D) o) =
      Ideal.Quotient.mk _ (algebraMap (A π e) (Rb π e c D) (algebraMap O (A π e) o))
    rw [← IsScalarTower.algebraMap_apply]

instance [IsNoetherianRing O] (n : ℕ) : IsNoetherianRing (Rn ϖ π e c D n) :=
  Ideal.Quotient.isNoetherianRing _

/-- The quotient map `R̄ → R n`. -/
abbrev mk (n : ℕ) : Rb π e c D →+* Rn ϖ π e c D n := Ideal.Quotient.mk _

lemma mk_surjective (n : ℕ) : Function.Surjective (mk ϖ π e c D n) :=
  Ideal.Quotient.mk_surjective

lemma algebraMap_O (n : ℕ) (o : O) :
    algebraMap O (Rn ϖ π e c D n) o = mk ϖ π e c D n (algebraMap O (Rb π e c D) o) := rfl

lemma algebraMap_A (n : ℕ) (a : A π e) :
    algebraMap (A π e) (Rn ϖ π e c D n) a = mk ϖ π e c D n (algebraMap (A π e) (Rb π e c D) a) :=
  rfl

lemma IRb_le (n : ℕ) : IRb ϖ π e c D (n + 1) ≤ IRb ϖ π e c D n := Ideal.map_mono (Iv_le ϖ n)

/-- The surjection `R (n+1) → R n`. -/
instance algSucc (n : ℕ) : Algebra (Rn ϖ π e c D (n + 1)) (Rn ϖ π e c D n) :=
  (Ideal.Quotient.factor (IRb_le ϖ π e c D n)).toAlgebra

lemma algebraMap_succ_mk (n : ℕ) (x : Rb π e c D) :
    algebraMap (Rn ϖ π e c D (n + 1)) (Rn ϖ π e c D n) (mk ϖ π e c D (n + 1) x) =
      mk ϖ π e c D n x := rfl

instance (n : ℕ) : IsScalarTower O (Rn ϖ π e c D (n + 1)) (Rn ϖ π e c D n) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance (n : ℕ) : IsScalarTower (A π e) (Rn ϖ π e c D (n + 1)) (Rn ϖ π e c D n) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

lemma surjective_succ (n : ℕ) :
    Function.Surjective (algebraMap (Rn ϖ π e c D (n + 1)) (Rn ϖ π e c D n)) :=
  Ideal.Quotient.factor_surjective (IRb_le ϖ π e c D n)

/-- The element `f = u + v` at level `n`. -/
abbrev fn (n : ℕ) : Rn ϖ π e c D n := NodeChart.fR (π := π) (e := e) (Rn ϖ π e c D n)

lemma hf (n : ℕ) : LevelStep.f' (R' := Rn ϖ π e c D n) (fn ϖ π e c D (n + 1)) = fn ϖ π e c D n :=
  rfl

/-! ### The special fibres -/

variable {k : Type u} [Field k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]

/-- The `k`-algebra structure on a special fibre (`kMap`). -/
instance algK (S : Type u) [CommRing S] [Algebra O S] : Algebra k (S ⧸ J θ (R := S)) :=
  (kMap hθ.out).toAlgebra

lemma algK_θ (S : Type u) [CommRing S] [Algebra O S] (o : O) :
    algebraMap k (S ⧸ J θ (R := S)) (θ o) = Ideal.Quotient.mk _ (algebraMap O S o) :=
  kMap_θ hθ.out o

variable {ϖ} (hϖ : θ ϖ = 0)

omit hθ in
include hϖ in
lemma IRb_le_J (n : ℕ) : IRb ϖ π e c D n ≤ J θ (R := Rb π e c D) := by
  refine Ideal.map_mono ?_
  refine (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
  exact hϖ

omit hθ in
lemma J_eq (n : ℕ) : J θ (R := Rn ϖ π e c D n) =
    (J θ (R := Rb π e c D)).map (mk ϖ π e c D n) := by
  rw [J, J, Ideal.map_map]
  rfl

omit hθ in
lemma J_le_comap (n : ℕ) : J θ (R := Rb π e c D) ≤ (J θ (R := Rn ϖ π e c D n)).comap
    (mk ϖ π e c D n) := by
  rw [J_eq]
  exact Ideal.le_comap_map

/-- `R̄/J → R n/J`. -/
def fwdJ (n : ℕ) : (Rb π e c D ⧸ J θ (R := Rb π e c D)) →+* (Rn ϖ π e c D n ⧸ J θ) :=
  Ideal.quotientMap _ (mk ϖ π e c D n) (J_le_comap π e c D n)

omit hθ in
include hϖ in
lemma IRb_le_ker (n : ℕ) : IRb ϖ π e c D n ≤ RingHom.ker
    (Ideal.Quotient.mk (J θ (R := Rb π e c D))) := fun _ hx ↦
  Ideal.Quotient.eq_zero_iff_mem.mpr (IRb_le_J π e c D hϖ n hx)

/-- `R n → R̄/J`. -/
def toJ (n : ℕ) : Rn ϖ π e c D n →+* (Rb π e c D ⧸ J θ (R := Rb π e c D)) :=
  Ideal.Quotient.lift (IRb ϖ π e c D n) (Ideal.Quotient.mk _) (IRb_le_ker π e c D hϖ n)

omit hθ in
lemma toJ_mk (n : ℕ) (x : Rb π e c D) :
    toJ π e c D hϖ n (mk ϖ π e c D n x) = Ideal.Quotient.mk _ x := rfl

omit hθ in
lemma J_le_ker (n : ℕ) : J θ (R := Rn ϖ π e c D n) ≤ RingHom.ker (toJ π e c D hϖ n) := by
  intro x hx
  rw [J_eq] at hx
  refine (Ideal.map_le_iff_le_comap.mpr ?_) hx
  intro y hy
  rw [Ideal.mem_comap, RingHom.mem_ker, toJ_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hy

/-- `R n/J → R̄/J`. -/
def bwdJ (n : ℕ) : (Rn ϖ π e c D n ⧸ J θ) →+* (Rb π e c D ⧸ J θ (R := Rb π e c D)) :=
  Ideal.Quotient.lift _ (toJ π e c D hϖ n) (J_le_ker π e c D hϖ n)

/-- `R̄/J ≃ R n/J` as rings. -/
def eqvR (n : ℕ) : (Rb π e c D ⧸ J θ (R := Rb π e c D)) ≃+* (Rn ϖ π e c D n ⧸ J θ) :=
  RingEquiv.ofRingHom (fwdJ π e c D n) (bwdJ π e c D hϖ n)
    (Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)))
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl))

omit hθ in
lemma eqvR_mk (n : ℕ) (x : Rb π e c D) :
    eqvR π e c D hϖ n (Ideal.Quotient.mk (J θ (R := Rb π e c D)) x) =
      Ideal.Quotient.mk _ (mk ϖ π e c D n x) := rfl

/-- **`R̄/J ≃ₐ[k] R n/J`**. -/
def eqv (n : ℕ) : (Rb π e c D ⧸ J θ (R := Rb π e c D)) ≃ₐ[k] (Rn ϖ π e c D n ⧸ J θ) :=
  AlgEquiv.ofRingEquiv (f := eqvR π e c D hϖ n) fun x ↦ by
    obtain ⟨o, rfl⟩ := hθ.out x
    rw [algK_θ, algK_θ, eqvR_mk]
    rfl

lemma eqv_mk (n : ℕ) (x : Rb π e c D) :
    eqv π e c D hϖ n (Ideal.Quotient.mk (J θ (R := Rb π e c D)) x) =
      Ideal.Quotient.mk _ (mk ϖ π e c D n x) :=
  eqvR_mk π e c D hϖ n x

/-- The element `f̄ = u + v` of the special fibre of the base chart. -/
abbrev fb : Rb π e c D ⧸ J θ (R := Rb π e c D) :=
  fbar θ (NodeChart.fR (π := π) (e := e) (Rb π e c D))

lemma hfe (n : ℕ) : eqv π e c D hϖ n (fb π e c D) = fbar θ (fn ϖ π e c D n) :=
  eqv_mk π e c D hϖ n _

lemma he (n : ℕ) (r : Rn ϖ π e c D (n + 1)) :
    eqv π e c D hϖ n ((eqv π e c D hϖ (n + 1)).symm (Ideal.Quotient.mk _ r)) =
      Ideal.Quotient.mk _ (algebraMap (Rn ϖ π e c D (n + 1)) (Rn ϖ π e c D n) r) := by
  obtain ⟨x, rfl⟩ := mk_surjective ϖ π e c D (n + 1) r
  rw [show (Ideal.Quotient.mk (J θ) (mk ϖ π e c D (n + 1) x) :
      Rn ϖ π e c D (n + 1) ⧸ J θ) = eqv π e c D hϖ (n + 1) (Ideal.Quotient.mk _ x) from
    (eqv_mk π e c D hϖ (n + 1) x).symm, AlgEquiv.symm_apply_apply, eqv_mk]
  rfl

/-! ### Node coordinates and the coordinate at the marked points -/

lemma hk (n : ℕ) (o : O) : algebraMap k (Rn ϖ π e c D n ⧸ J θ) (θ o) =
    Ideal.Quotient.mk _ (algebraMap O (Rn ϖ π e c D n) o) :=
  algK_θ _ o

lemma hatEquiv_bar (n : ℕ) (x : Rb π e c D) :
    Admissible.hatEquiv (eqv π e c D hϖ n) (hfe π e c D hϖ n)
        (NodeChart.bar θ (π := π) (e := e) x) =
      NodeChart.bar θ (π := π) (e := e) (mk ϖ π e c D n x) := by
  rw [NodeChart.bar, Admissible.hatEquiv_algebraMap, eqv_mk]

variable (hπe : θ (π ^ e) = 0)

/-- **The transported node coordinates are those of the level**:
`Ê_n ∘ φ_{R̄} = φ_{R n}`. -/
lemma φT_eq (n : ℕ) :
    Admissible.φT (h := hfe π e c D hϖ n) (NodeChart.φ (Rb π e c D) hπe) =
      NodeChart.φ (Rn ϖ π e c D n) hπe := by
  refine Node.algHom_ext ?_ ?_
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, NodeChart.φ_u]
    exact hatEquiv_bar π e c D hϖ n _
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, NodeChart.φ_v]
    exact hatEquiv_bar π e c D hϖ n _

variable (τ : Rb π e c D)

/-- The coordinate at the marked points of the base special fibre, `X ↦ τ̄`. -/
abbrev ψb : Polynomial k →ₐ[k] Admissible.Hat (fb (θ := θ) π e c D) :=
  Polynomial.aeval (NodeChart.bar θ (π := π) (e := e) τ)

/-- The coordinate at the marked points at level `n`. -/
abbrev tn (n : ℕ) : FormalPatchLevel.Hat (fn ϖ π e c D n) :=
  algebraMap (Rn ϖ π e c D n) _ (mk ϖ π e c D n τ)

lemma ht (n : ℕ) : ψ θ (fn ϖ π e c D n) (tn π e c D τ n) =
    Admissible.ψT (h := hfe π e c D hϖ n) (ψb π e c D τ) Polynomial.X := by
  rw [NodeChart.ψ_algebraMap, AlgHom.comp_apply, Polynomial.aeval_X, AlgEquiv.coe_toAlgHom,
    hatEquiv_bar]

lemma hct (n : ℕ) : LevelStep.ψ₂ (fn ϖ π e c D (n + 1)) (fn ϖ π e c D n) (hf ϖ π e c D n)
    (tn π e c D τ (n + 1)) = tn π e c D τ n := by
  rw [LevelStep.ψ₂_algebraMap]
  rfl

/-- The node coordinates of index `e'` (`π'^{e'} = π^e`) at level `n`. -/
abbrev χn {π' : O} {e' : ℕ} (h : π' ^ e' = π ^ e) (n : ℕ) :
    A π' e' →ₐ[O] FormalPatchLevel.Hat (fn ϖ π e c D n) :=
  NodeChart.χ (Rn ϖ π e c D n) h

omit hθ in
lemma ψ₂_algebraMap_A (n : ℕ) (a : A π e) :
    LevelStep.ψ₂ (fn ϖ π e c D (n + 1)) (fn ϖ π e c D n) (hf ϖ π e c D n)
      (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D (n + 1))) a) =
        algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)) a := by
  rw [IsScalarTower.algebraMap_apply (A π e) (Rn ϖ π e c D (n + 1)), LevelStep.ψ₂_algebraMap,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

omit hθ in
lemma hcχ {π' : O} {e' : ℕ} (h : π' ^ e' = π ^ e) (n : ℕ) (a : A π' e') :
    LevelStep.ψ₂ (fn ϖ π e c D (n + 1)) (fn ϖ π e c D n) (hf ϖ π e c D n)
      (χn π e c D h (n + 1) a) = χn π e c D h n a :=
  ψ₂_algebraMap_A π e c D n _

/-! ### Flatness of the node coordinates modulo `ϖⁿ⁺¹` -/

section Flat

omit hθ

variable (ϖ)

variable {π' : O} {e' : ℕ} (h : π' ^ e' = π ^ e) (n : ℕ)

/-- The deformation parameter `π'` modulo `ϖⁿ⁺¹`. -/
abbrev πn : O ⧸ Iv ϖ n := KummerFactorQuot.πI (Iv ϖ n) π'

include h in
lemma hlev : πn ϖ (π' := π') n ^ e' = Ideal.Quotient.mk (Iv ϖ n) (π ^ e) := by
  rw [← map_pow, h]

/-- The level-`n` chart as a quadratic node chart over `(O/ϖⁿ⁺¹)[u,v]/(uv − π̄'^{e'})`. -/
abbrev Rlv : Type u :=
  QuadNodeLevel.Rlev (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) c D

/-- **`R n ≃ Rlv`** (`QuadNodeLevel.equiv`). -/
def Elev : Rn ϖ π e c D n ≃+* Rlv ϖ π e c D h n :=
  QuadNodeLevel.equiv (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) c D

lemma algebraMap_A_ι (a : A π e) : algebraMap (A π e) (Rn ϖ π e c D n) a =
    QuadNodeLevel.ι (Iv ϖ n) c D a := by
  rw [algebraMap_A, IsScalarTower.algebraMap_apply (A π e)
    (AdjoinRoot (QuadraticEtale.poly c)) (Rb π e c D)]
  rfl

lemma Elev_algebraMap (a : A π e) : Elev ϖ π e c D h n (algebraMap (A π e) (Rn ϖ π e c D n) a) =
    algebraMap (A (πn ϖ (π' := π') n) e') (Rlv ϖ π e c D h n)
      (QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) a) := by
  rw [algebraMap_A_ι]
  exact QuadNodeLevel.equiv_algebraMap _ _ _ _ c D a

lemma nodeMap_fA : QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n)
    (fA π (e := e)) = fA (πn ϖ (π' := π') n) := by
  simp only [fA, map_add, QuadNodeLevel.nodeMap_u, QuadNodeLevel.nodeMap_v]

lemma map_span : (Ideal.span {fn ϖ π e c D n}).map (Elev ϖ π e c D h n : Rn ϖ π e c D n →+* _) =
    Ideal.span {QuadNode.f (πn ϖ (π' := π') n) e'
      (QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) c)
      (QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) D)} := by
  have hE : (Elev ϖ π e c D h n : Rn ϖ π e c D n →+* _) (fn ϖ π e c D n) =
      QuadNode.f (πn ϖ (π' := π') n) e'
        (QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) c)
        (QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) D) := by
    change Elev ϖ π e c D h n (algebraMap (A π e) (Rn ϖ π e c D n) (fA π)) = _
    rw [Elev_algebraMap ϖ π e c D h n, nodeMap_fA ϖ π e h n]
  rw [Ideal.map_span, Set.image_singleton, hE]

/-- The completions along the nodes: `R̂_n ≃ R̂lv`. -/
def CE : FormalPatchLevel.Hat (fn ϖ π e c D n) ≃+*
    FormalPatchLevel.Hat (QuadNode.f (πn ϖ (π' := π') n) e'
      (QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) c)
      (QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) D)) :=
  CompletionMap.equiv (Elev ϖ π e c D h n) (map_span ϖ π e c D h n)

lemma CE_algebraMap_A (a : A π e) :
    CE ϖ π e c D h n (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)) a) =
      algebraMap (A (πn ϖ (π' := π') n) e') _
        (QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e' (hlev ϖ π e h n) a) :=
  (congrArg (CE ϖ π e c D h n) (IsScalarTower.algebraMap_apply (A π e) (Rn ϖ π e c D n)
    (FormalPatchLevel.Hat (fn ϖ π e c D n)) a)).trans
    ((CompletionMap.equiv_algebraMap (Elev ϖ π e c D h n) (map_span ϖ π e c D h n) _).trans
      ((congrArg _ (Elev_algebraMap ϖ π e c D h n a)).trans
        (IsScalarTower.algebraMap_apply _ _ _ _).symm))

lemma nodeMap_congrEq : (QuadNodeLevel.nodeMap (Iv ϖ n) (πn ϖ (π' := π') n) e'
      (hlev ϖ π e h n)).toRingHom.comp (Node.congrEq h).toAlgHom.toRingHom =
    KummerFactorQuot.redA (Iv ϖ n) π' := by
  refine Node.ringHom_ext (RingHom.ext fun o ↦ ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      Node.baseMap_algebraMap]
    exact IsScalarTower.algebraMap_apply O (O ⧸ Iv ϖ n) _ o
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toAlgHom]
    rw [Node.congrEq_u h, QuadNodeLevel.nodeMap_u, Node.baseMap_u]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toAlgHom]
    rw [Node.congrEq_v h, QuadNodeLevel.nodeMap_v, Node.baseMap_v]

lemma χn_apply (a : A π' e') : χn (ϖ := ϖ) π e c D h n a =
    algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)) (Node.congrEq h a) :=
  NodeChart.χ_apply h a

lemma CE_χn (a : A π' e') :
    CE ϖ π e c D h n (χn (ϖ := ϖ) π e c D h n a) =
      algebraMap (A (πn ϖ (π' := π') n) e') _ (KummerFactorQuot.redA (Iv ϖ n) π' a) := by
  refine (congrArg (CE ϖ π e c D h n) (χn_apply ϖ π e c D h n a)).trans ?_
  refine (CE_algebraMap_A ϖ π e c D h n _).trans ?_
  exact congrArg (algebraMap (A (πn ϖ (π' := π') n) e') _)
    (RingHom.congr_fun (nodeMap_congrEq ϖ π e h n) a)

/-- **The node coordinates of the level `n` are flat modulo `ϖⁿ⁺¹`** (`QuadNode.flat_hat` over
`O/ϖⁿ⁺¹`). -/
theorem kflat [IsNoetherianRing O] :
    KummerFactorQuot.KFlat (Iv ϖ n) (χn (ϖ := ϖ) π e c D h n).toRingHom := by
  refine ⟨(CE ϖ π e c D h n).symm.toRingHom.comp (algebraMap _ _), ?_, ?_⟩
  · exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr (QuadNode.flat_hat _ _ _ _))
      (RingHom.Flat.of_bijective (CE ϖ π e c D h n).symm.bijective)
  · refine RingHom.ext fun a ↦ ?_
    change (CE ϖ π e c D h n).symm (algebraMap _ _ (KummerFactorQuot.redA (Iv ϖ n) π' a)) = _
    rw [← CE_χn ϖ π e c D h n a, RingEquiv.symm_apply_apply]
    rfl

end Flat

/-! ### The tower of patched algebras of the quadratic node chart -/

section Tower

omit hθ in
/-- The kernel of `R (n+1) → R n` is `ϖⁿ⁺¹ R (n+1)`. -/
lemma ker_succ (n : ℕ) : RingHom.ker (algebraMap (Rn ϖ π e c D (n + 1)) (Rn ϖ π e c D n)) =
    (Iv ϖ n).map (algebraMap O (Rn ϖ π e c D (n + 1))) := by
  change RingHom.ker (Ideal.Quotient.factor (IRb_le ϖ π e c D n)) = _
  rw [Ideal.Quotient.factor_ker, Ideal.map_map]
  rfl

omit hθ in
/-- `ϖⁿ⁺¹` kills `R n`. -/
lemma kill (n : ℕ) : (Iv ϖ n).map (algebraMap O (Rn ϖ π e c D n)) = ⊥ := by
  rw [show (algebraMap O (Rn ϖ π e c D n)) =
    (mk ϖ π e c D n).comp (algebraMap O (Rb π e c D)) from rfl, ← Ideal.map_map]
  exact Ideal.map_quotient_self _

omit hθ in
/-- `J` is nilpotent at level `n` if `ker θ ⊆ (ϖ)`. -/
lemma hJ (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) (n : ℕ) :
    J θ (R := Rn ϖ π e c D n) ^ (n + 1) = ⊥ := by
  rw [J, ← Ideal.map_pow, eq_bot_iff]
  refine (Ideal.map_mono (Ideal.pow_right_mono hker (n + 1))).trans ?_
  rw [show (algebraMap O (Rn ϖ π e c D n)) =
    (mk ϖ π e c D n).comp (algebraMap O (Rb π e c D)) from rfl, ← Ideal.map_map,
    Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_bot]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

variable (cov₀ : Admissible.Covering (NodeChart.φ (Rb π e c D) hπe) (ψb (θ := θ) π e c D τ))
  (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = π ^ e)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ})

include hπe hπ' in
lemma hπ (j : cov₀.ι) : θ (π' j) = 0 := NodeChart.θ_π' hπe (cov₀.e_pos j) (hπ' j)

set_option maxHeartbeats 1000000 in
-- unifying the completions of the level charts is slow
lemma hχ (n : ℕ) (j : cov₀.ι) (a : A (π' j) (cov₀.e j)) :
    ψ θ (fn ϖ π e c D n) (χn (ϖ := ϖ) π e c D (hπ' j) n a) =
      Admissible.φT (h := hfe π e c D hϖ n) (NodeChart.φ (Rb π e c D) hπe)
        (Admissible.nodeCongr (cov₀.e_pos j)
          (Node.baseMap θ (hA (hπ π e c D hπe τ cov₀ π' hπ' j)) a)) := by
  have h := NodeChart.hχ hπe (cov₀.e_pos j) (hπ' j) (hk (ϖ := ϖ) π e c D n) a
  rw [← φT_eq π e c D hϖ hπe n] at h
  exact h

variable [IsNoetherianRing O]

omit hθ in
lemma hreg (n : ℕ) (y : FormalPatchLevel.Hat (fn ϖ π e c D n))
    (hy : algebraMap (Rn ϖ π e c D n) _ (fn ϖ π e c D n) * y = 0) : y = 0 := by
  refine KummerFactorQuot.KFlat.eq_zero_of_mul_eq_zero (Iv ϖ n)
    (kflat ϖ π e c D (rfl : π ^ e = π ^ e) n) ?_
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, NodeChart.χ_fA]
  exact hy

/-- **The tower of patched algebras of the quadratic node chart**: the coordinates `χn`, `tn`
on the levels `R n = R̄/ϖⁿ⁺¹R̄` of an admissible covering `cov₀` of the special fibre of `R̄`. -/
def tower : LevelTower.Data (θ := θ) (Rn ϖ π e c D) cov₀ π' where
  f := fn ϖ π e c D
  e := eqv π e c D hϖ
  hfe := hfe π e c D hϖ
  hπ := hπ π e c D hπe τ cov₀ π' hπ'
  χ := fun m j ↦ χn (ϖ := ϖ) π e c D (hπ' j) m
  hχ := hχ π e c D hϖ hπe τ cov₀ π' hπ'
  t := tn π e c D τ
  ht := ht π e c D hϖ τ
  m := fun n ↦ n + 1
  hJ := hJ π e c D hker
  I := Iv ϖ
  hflat := fun m j ↦ kflat ϖ π e c D (hπ' j) m
  hfχ := fun _ j ↦ NodeChart.χ_fA (hπ' j)
  hreg := hreg π e c D
  hq := surjective_succ ϖ π e c D
  hf := hf ϖ π e c D
  he := he π e c D hϖ
  hcχ := fun m j a ↦ hcχ π e c D (hπ' j) m a
  hct := hct π e c D τ

/-- **The level-`n` patched algebra** of the admissible covering `cov₀` on the quadratic node
chart. -/
abbrev G (n : ℕ) : Type u :=
  (tower π e c D hϖ hπe τ cov₀ π' hπ' hker).G hθ.out n

variable (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The transition maps** `G (n+1) → G n` of the Tate tower. -/
abbrev tr (n : ℕ) := (tower π e c D hϖ hπe τ cov₀ π' hπ' hker).tr hθ.out hO n

end Tower

end QuadNodeTower

end

end SemistableReduction
