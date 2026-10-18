/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateTwoChart
import TemperedFundamentalGroups.SemistableReduction.QuadraticNodeChart

/-!
# The chart `u ≠ 0` of the Tate model near the nodes, over `ℙ¹` (Blueprint §12.8, M2.3 (f))

The chart `T1 = O[h'][w]/(G₁)` of the Tate model over `U₁ ⊆ ℙ¹_O` (`TateTwoChart`), localized at
`D = 1 + b₄ w²`, is the quadratic node chart `QuadNode.R ϖ m c D` over the node ring
`A = O[u,v]/(uv − ϖᵐ)` (`π = ε ϖᵐ`, `ε` a unit, `c = ε (1 + b₄ u²) v + b₆ u²`), purely
algebraically (no function field):

* `TateTwoChart.liftT1`: maps out of `T1` are given by elements `s, w` of the target satisfying
  the chart equation `w (s² + s − b₆ w²) = π (1 + b₄ w²)` (`h' ↦ s − t w`, `w ↦ w`);
  `TateTwoChartNode.liftNR`: maps out of the node chart are given by `s, w` satisfying the chart
  equation with `1 + b₄ w²` a unit (`u ↦ w`, `v ↦ (s² + s − b₆ w²)/(ε D)`, `S ↦ s`);
* **`TateTwoChartNode.chartEquiv : T1[1/D] ≃ₐ[O] QuadNode.R ϖ m c D`**, `w ↦ u`, `s ↦ S`
  (`s = h' + t w` is the coordinate `v/u` of the chart);
* **the coordinate comparison** (`chartEquiv_h1`): the `ℙ¹` coordinate `h' = ℓ₀/u` of
  `TateProjection.toP1` is `S − t u` on the node chart; `coordP1` (`X ↦ S − t u`) makes the node
  chart an `O[X]`-algebra compatibly with `T1` (`toNode_comp_algebraMap`).

This is the shared input of the patching over the `ℙ¹` chart `U₁` (M2.3 (f)) and of the flatness
of the patched algebras over `O_n[X]` (3f).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateTwoChart

noncomputable section

variable {O : Type u} [CommRing O] {π b₄ b₆ t κ : O} {S : Type u} [CommRing S] [Algebra O S]

/-- The chart equation of `u ≠ 0` in the coordinates `s = v/u`, `w = w/u`. -/
def ChartEq (π b₄ b₆ : O) (s w : S) : Prop :=
  w * (s ^ 2 + s - algebraMap O S b₆ * w ^ 2) = algebraMap O S π * (1 + algebraMap O S b₄ * w ^ 2)

lemma eval_G1_of (hκ : κ * (t ^ 2 - b₆) = 1) {s w : S} (h : ChartEq π b₄ b₆ s w) :
    (G1 π b₄ t κ).eval₂ ((Polynomial.aeval (s - algebraMap O S t * w) : O[X] →ₐ[O] S) :
      O[X] →+* S) w = 0 := by
  have hk : algebraMap O S κ * (algebraMap O S t ^ 2 - algebraMap O S b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  unfold ChartEq at h
  simp only [G1, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, RingHom.coe_coe,
    map_mul, map_add, map_pow, map_sub, Polynomial.aeval_C, Polynomial.aeval_X]
  simp only [map_ofNat] at h ⊢
  linear_combination algebraMap O S κ * h - w ^ 3 * hk

/-- **Maps out of `T1`**: `h' ↦ s − t w`, `w ↦ w` for `s, w` satisfying the chart equation. -/
def liftT1 (hκ : κ * (t ^ 2 - b₆) = 1) (s w : S) (h : ChartEq π b₄ b₆ s w) :
    T1 π b₄ t κ →ₐ[O] S :=
  AdjoinRoot.liftAlgHom (G1 π b₄ t κ) (Polynomial.aeval (s - algebraMap O S t * w)) w
    (eval_G1_of hκ h)

lemma liftT1_h1 (hκ : κ * (t ^ 2 - b₆) = 1) (s w : S) (h : ChartEq π b₄ b₆ s w) :
    liftT1 hκ s w h (h1 π b₄ t κ) = s - algebraMap O S t * w := by
  simp [liftT1]

lemma liftT1_w1 (hκ : κ * (t ^ 2 - b₆) = 1) (s w : S) (h : ChartEq π b₄ b₆ s w) :
    liftT1 hκ s w h (w1 π b₄ t κ) = w := by
  simp [liftT1]

lemma liftT1_s1 (hκ : κ * (t ^ 2 - b₆) = 1) (s w : S) (h : ChartEq π b₄ b₆ s w) :
    liftT1 hκ s w h (s1 π b₄ t κ) = s := by
  rw [map_add, map_mul, AlgHom.commutes, liftT1_h1, liftT1_w1]
  ring

lemma chartEq_s1 (hκ : κ * (t ^ 2 - b₆) = 1) :
    ChartEq π b₄ b₆ (s1 π b₄ t κ) (w1 π b₄ t κ) :=
  eqn1 π b₄ t κ hκ

lemma chartEq_map {S' : Type u} [CommRing S'] [Algebra O S'] (φ : S →ₐ[O] S') {s w : S}
    (h : ChartEq π b₄ b₆ s w) : ChartEq π b₄ b₆ (φ s) (φ w) := by
  have := congrArg φ h
  simp only [map_mul, map_add, map_sub, map_pow, map_one, AlgHom.commutes] at this
  exact this

end

end TateTwoChart

namespace TateTwoChartNode

open TateTwoChart KummerEtale

noncomputable section

variable {O : Type u} [CommRing O]

/-- `c = ε (1 + b₄ u²) v + b₆ u²` in the node ring `O[u,v]/(uv − ϖᵐ)`. -/
def cN (b₄ b₆ ϖ : O) (m : ℕ) (ε : O) : A ϖ m :=
  algebraMap O _ ε * (1 + algebraMap O _ b₄ * Node.u (ϖ ^ m) ^ 2) * Node.v (ϖ ^ m) +
    algebraMap O _ b₆ * Node.u (ϖ ^ m) ^ 2

/-- `D = 1 + b₄ u²` in the node ring. -/
def DN (b₄ ϖ : O) (m : ℕ) : A ϖ m := 1 + algebraMap O _ b₄ * Node.u (ϖ ^ m) ^ 2

/-- The quadratic node chart of the Tate model. -/
abbrev NR (b₄ b₆ ϖ : O) (m : ℕ) (ε : O) : Type u :=
  QuadNode.R ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)

variable (b₄ b₆ ϖ : O) (m : ℕ) (ε : O)

/-- `u` on the node chart. -/
abbrev uR : NR b₄ b₆ ϖ m ε := algebraMap (A ϖ m) _ (Node.u _)

/-- `v` on the node chart. -/
abbrev vR : NR b₄ b₆ ϖ m ε := algebraMap (A ϖ m) _ (Node.v _)

/-- `S` on the node chart. -/
abbrev SR : NR b₄ b₆ ϖ m ε :=
  algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) _ (AdjoinRoot.root _)

lemma SR_sq : SR b₄ b₆ ϖ m ε ^ 2 + SR b₄ b₆ ϖ m ε =
    algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (cN b₄ b₆ ϖ m ε) := by
  have h : AdjoinRoot.mk (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε))
      (X ^ 2 + X - C (cN b₄ b₆ ϖ m ε)) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  have h' := congrArg (algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (NR b₄ b₆ ϖ m ε)) h
  have hc : algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (NR b₄ b₆ ϖ m ε)
      (AdjoinRoot.of _ (cN b₄ b₆ ϖ m ε)) =
      algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (cN b₄ b₆ ϖ m ε) :=
    (IsScalarTower.algebraMap_apply (A ϖ m) (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) _ _).symm
  simp only [map_sub, map_add, map_pow, map_zero, hc] at h'
  exact sub_eq_zero.1 h'

lemma uR_mul_vR : uR b₄ b₆ ϖ m ε * vR b₄ b₆ ϖ m ε = algebraMap O _ ϖ ^ m := by
  rw [← map_mul, Node.u_mul_v, ← IsScalarTower.algebraMap_apply, map_pow]

lemma algebraMap_cN : algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (cN b₄ b₆ ϖ m ε) =
    algebraMap O _ ε * (1 + algebraMap O _ b₄ * uR b₄ b₆ ϖ m ε ^ 2) * vR b₄ b₆ ϖ m ε +
      algebraMap O _ b₆ * uR b₄ b₆ ϖ m ε ^ 2 := by
  simp only [cN, map_add, map_mul, map_pow, map_one, ← IsScalarTower.algebraMap_apply]

variable {b₄ b₆ ϖ m ε} {π : O}

lemma chartEq_node (hπ : π = ε * ϖ ^ m) : ChartEq π b₄ b₆ (SR b₄ b₆ ϖ m ε) (uR b₄ b₆ ϖ m ε) := by
  have hS := SR_sq b₄ b₆ ϖ m ε
  rw [algebraMap_cN] at hS
  have huv := uR_mul_vR b₄ b₆ ϖ m ε
  unfold ChartEq
  subst hπ
  simp only [map_mul (algebraMap O (NR b₄ b₆ ϖ m ε)), map_pow (algebraMap O (NR b₄ b₆ ϖ m ε))]
  linear_combination uR b₄ b₆ ϖ m ε * hS +
    algebraMap O _ ε * (1 + algebraMap O _ b₄ * uR b₄ b₆ ϖ m ε ^ 2) * huv

/-! ### Maps out of the node chart -/

variable {S : Type u} [CommRing S] [Algebra O S] {εi : O}

/-- The value of `v`: `(s² + s − b₆ w²)/(ε D)`. -/
abbrev vVal (b₄ b₆ : O) (εi : O) (s w : S) (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) : S :=
  (s ^ 2 + s - algebraMap O S b₆ * w ^ 2) * algebraMap O S εi * ↑hD.unit⁻¹

lemma w_mul_vVal (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S} (h : ChartEq π b₄ b₆ s w)
    (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) :
    w * vVal b₄ b₆ εi s w hD = algebraMap O S (ϖ ^ m) := by
  have hDi : (1 + algebraMap O S b₄ * w ^ 2) * ↑hD.unit⁻¹ = 1 := hD.mul_val_inv
  have hε' : algebraMap O S εi * algebraMap O S ε = 1 := by rw [← map_mul, hε, map_one]
  unfold ChartEq at h
  rw [hπ, map_mul] at h
  linear_combination algebraMap O S εi * ↑hD.unit⁻¹ * h +
    algebraMap O S εi * algebraMap O S ε * algebraMap O S (ϖ ^ m) * hDi +
    algebraMap O S (ϖ ^ m) * hε'

/-- The node ring maps to `S`: `u ↦ w`, `v ↦ (s² + s − b₆ w²)/(ε D)`. -/
def nodeLift (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S} (h : ChartEq π b₄ b₆ s w)
    (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) : A ϖ m →ₐ[O] S :=
  Node.lift w (vVal b₄ b₆ εi s w hD) (w_mul_vVal hε hπ h hD)

lemma eval_poly_nodeLift (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S}
    (h : ChartEq π b₄ b₆ s w) (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) :
    (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)).eval₂
      ((nodeLift hε hπ h hD : A ϖ m →ₐ[O] S) : A ϖ m →+* S) s = 0 := by
  have hDi : (1 + algebraMap O S b₄ * w ^ 2) * ↑hD.unit⁻¹ = 1 := hD.mul_val_inv
  have hε' : algebraMap O S εi * algebraMap O S ε = 1 := by rw [← map_mul, hε, map_one]
  simp only [QuadraticEtale.poly, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    RingHom.coe_coe]
  simp only [cN, map_add, map_mul, map_pow, map_one, AlgHom.commutes, nodeLift,
    Node.lift_u, Node.lift_v]
  linear_combination (-(s ^ 2 + s - algebraMap O S b₆ * w ^ 2)) *
    (algebraMap O S εi * algebraMap O S ε * hDi + hε')

/-- `A[S]/(S² + S − c) → S`, `S ↦ s`. -/
def quadLift (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S} (h : ChartEq π b₄ b₆ s w)
    (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) : QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε) →ₐ[O] S :=
  AdjoinRoot.liftAlgHom _ (nodeLift hε hπ h hD) s (eval_poly_nodeLift hε hπ h hD)

lemma quadLift_D (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S} (h : ChartEq π b₄ b₆ s w)
    (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) :
    quadLift hε hπ h hD (AdjoinRoot.of _ (DN b₄ ϖ m)) = 1 + algebraMap O S b₄ * w ^ 2 := by
  simp [quadLift, DN, nodeLift]

lemma isUnit_quadLift_D (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S}
    (h : ChartEq π b₄ b₆ s w) (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) :
    IsUnit (quadLift hε hπ h hD (AdjoinRoot.of _ (DN b₄ ϖ m))) := by
  rw [quadLift_D]; exact hD

/-- **Maps out of the node chart**: `u ↦ w`, `v ↦ (s² + s − b₆ w²)/(ε D)`, `S ↦ s`. -/
def liftNR (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S} (h : ChartEq π b₄ b₆ s w)
    (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) : NR b₄ b₆ ϖ m ε →ₐ[O] S :=
  IsLocalization.Away.liftAlgHom (f := quadLift hε hπ h hD) _ (isUnit_quadLift_D hε hπ h hD)

lemma liftNR_algebraMap (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S}
    (h : ChartEq π b₄ b₆ s w) (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2))
    (a : QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) :
    liftNR hε hπ h hD (algebraMap _ _ a) = quadLift hε hπ h hD a :=
  IsLocalization.Away.lift_eq _ (isUnit_quadLift_D hε hπ h hD) a

lemma liftNR_uR (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S} (h : ChartEq π b₄ b₆ s w)
    (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) : liftNR hε hπ h hD (uR b₄ b₆ ϖ m ε) = w := by
  change liftNR hε hπ h hD (algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (Node.u _)) = w
  rw [IsScalarTower.algebraMap_apply (A ϖ m) (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)),
    liftNR_algebraMap, AdjoinRoot.algebraMap_eq]
  simp [quadLift, nodeLift]

lemma liftNR_vR (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S} (h : ChartEq π b₄ b₆ s w)
    (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) :
    liftNR hε hπ h hD (vR b₄ b₆ ϖ m ε) = vVal b₄ b₆ εi s w hD := by
  change liftNR hε hπ h hD (algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (Node.v _)) = _
  rw [IsScalarTower.algebraMap_apply (A ϖ m) (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)),
    liftNR_algebraMap, AdjoinRoot.algebraMap_eq]
  simp [quadLift, nodeLift]

lemma liftNR_SR (hε : εi * ε = 1) (hπ : π = ε * ϖ ^ m) {s w : S} (h : ChartEq π b₄ b₆ s w)
    (hD : IsUnit (1 + algebraMap O S b₄ * w ^ 2)) : liftNR hε hπ h hD (SR b₄ b₆ ϖ m ε) = s := by
  rw [liftNR_algebraMap]
  simp [quadLift]

/-- Two maps out of the node chart agreeing on `u`, `v`, `S` are equal. -/
lemma algHom_ext_NR {f g : NR b₄ b₆ ϖ m ε →ₐ[O] S} (hu : f (uR b₄ b₆ ϖ m ε) = g (uR b₄ b₆ ϖ m ε))
    (hv : f (vR b₄ b₆ ϖ m ε) = g (vR b₄ b₆ ϖ m ε)) (hS : f (SR b₄ b₆ ϖ m ε) = g (SR b₄ b₆ ϖ m ε)) :
    f = g :=
  IsLocalization.algHom_ext (Submonoid.powers
      (AdjoinRoot.of (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)) (DN b₄ ϖ m)))
    (AdjoinRoot.algHom_ext' (Node.algHom_ext hu hv) hS)

/-! ### The equivalence -/

variable {t κ : O}

/-- `D = 1 + b₄ w²` in `T1`. -/
abbrev DT (π b₄ t κ : O) : T1 π b₄ t κ := 1 + algebraMap O _ b₄ * w1 π b₄ t κ ^ 2

/-- `T1[1/D]`. -/
abbrev T1D (π b₄ t κ : O) : Type u := Localization.Away (DT π b₄ t κ)

lemma isUnit_D_node : IsUnit (1 + algebraMap O (NR b₄ b₆ ϖ m ε) b₄ * uR b₄ b₆ ϖ m ε ^ 2) := by
  have : 1 + algebraMap O (NR b₄ b₆ ϖ m ε) b₄ * uR b₄ b₆ ϖ m ε ^ 2 =
      algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) _ (AdjoinRoot.of _ (DN b₄ ϖ m)) := by
    rw [show algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (NR b₄ b₆ ϖ m ε)
      (AdjoinRoot.of _ (DN b₄ ϖ m)) = algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (DN b₄ ϖ m) from
      (IsScalarTower.algebraMap_apply (A ϖ m) (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) _ _).symm]
    simp only [DN, map_add, map_one, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  rw [this]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- `Φ : T1 → node chart`, `h' ↦ S − t u`, `w ↦ u`. -/
def toNode (b₄ : O) (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) :
    T1 π b₄ t κ →ₐ[O] NR b₄ b₆ ϖ m ε :=
  liftT1 hκ _ _ (chartEq_node hπ)

lemma toNode_DT (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) :
    toNode b₄ hκ hπ (DT π b₄ t κ) = 1 + algebraMap O _ b₄ * uR b₄ b₆ ϖ m ε ^ 2 := by
  simp only [DT, map_add, map_one, map_mul, map_pow, AlgHom.commutes, toNode, liftT1_w1]

lemma isUnit_toNode_DT (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) :
    IsUnit (toNode b₄ hκ hπ (DT π b₄ t κ)) := by
  rw [toNode_DT]; exact isUnit_D_node

/-- `T1[1/D] → node chart`. -/
def toNodeD (b₄ : O) (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) :
    T1D π b₄ t κ →ₐ[O] NR b₄ b₆ ϖ m ε :=
  IsLocalization.Away.liftAlgHom (f := toNode b₄ hκ hπ) _ (isUnit_toNode_DT hκ hπ)

lemma toNodeD_algebraMap (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (a : T1 π b₄ t κ) :
    toNodeD b₄ hκ hπ (algebraMap _ _ a) = toNode b₄ hκ hπ a :=
  IsLocalization.Away.lift_eq _ (isUnit_toNode_DT hκ hπ) a

lemma isUnit_D_T1D :
    IsUnit (1 + algebraMap O (T1D π b₄ t κ) b₄ * algebraMap _ _ (w1 π b₄ t κ) ^ 2) := by
  have : 1 + algebraMap O (T1D π b₄ t κ) b₄ * algebraMap _ _ (w1 π b₄ t κ) ^ 2 =
      algebraMap (T1 π b₄ t κ) _ (DT π b₄ t κ) := by
    simp only [DT, map_add, map_one, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  rw [this]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- `node chart → T1[1/D]`. -/
def ofNode (b₄ : O) (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1) :
    NR b₄ b₆ ϖ m ε →ₐ[O] T1D π b₄ t κ :=
  liftNR hε hπ (chartEq_map (IsScalarTower.toAlgHom O (T1 π b₄ t κ) (T1D π b₄ t κ))
    (chartEq_s1 hκ)) isUnit_D_T1D

lemma ofNode_toNode (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
    (x : T1D π b₄ t κ) : ofNode b₄ hκ hπ hε (toNodeD b₄ hκ hπ x) = x := by
  have : (ofNode b₄ hκ hπ hε).comp (toNodeD b₄ hκ hπ) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (DT π b₄ t κ))
      (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
    · change ofNode b₄ hκ hπ hε (toNodeD b₄ hκ hπ (algebraMap _ _ (h1 π b₄ t κ))) =
        algebraMap _ _ (h1 π b₄ t κ)
      rw [toNodeD_algebraMap, toNode, liftT1_h1, map_sub, map_mul, AlgHom.commutes, ofNode,
        liftNR_SR, liftNR_uR]
      simp only [IsScalarTower.coe_toAlgHom', s1, map_add, map_mul,
        ← IsScalarTower.algebraMap_apply]
      ring
    · change ofNode b₄ hκ hπ hε (toNodeD b₄ hκ hπ (algebraMap _ _ (w1 π b₄ t κ))) =
        algebraMap _ _ (w1 π b₄ t κ)
      rw [toNodeD_algebraMap, toNode, liftT1_w1, ofNode, liftNR_uR]
      rfl
  exact AlgHom.congr_fun this x

lemma toNode_ofNode (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
    (x : NR b₄ b₆ ϖ m ε) : toNodeD b₄ hκ hπ (ofNode b₄ hκ hπ hε x) = x := by
  have : (toNodeD b₄ hκ hπ).comp (ofNode b₄ hκ hπ hε) = AlgHom.id O _ := by
    refine algHom_ext_NR ?_ ?_ ?_
    · change toNodeD b₄ hκ hπ (ofNode b₄ hκ hπ hε (uR b₄ b₆ ϖ m ε)) = uR b₄ b₆ ϖ m ε
      rw [ofNode, liftNR_uR, IsScalarTower.coe_toAlgHom', toNodeD_algebraMap, toNode, liftT1_w1]
    · change toNodeD b₄ hκ hπ (ofNode b₄ hκ hπ hε (vR b₄ b₆ ϖ m ε)) = vR b₄ b₆ ϖ m ε
      rw [ofNode, liftNR_vR]
      have hDi := congrArg (toNodeD b₄ hκ hπ)
        (isUnit_D_T1D (π := π) (b₄ := b₄) (t := t) (κ := κ)).mul_val_inv
      have hS := SR_sq b₄ b₆ ϖ m ε
      rw [algebraMap_cN] at hS
      have hε' : algebraMap O (NR b₄ b₆ ϖ m ε) εi * algebraMap O _ ε = 1 := by
        rw [← map_mul, hε, map_one]
      simp only [vVal, map_mul, map_add, map_sub, map_pow, map_one, AlgHom.commutes,
        IsScalarTower.coe_toAlgHom', toNodeD_algebraMap, toNode, liftT1_w1, liftT1_h1] at hDi ⊢
      linear_combination algebraMap O (NR b₄ b₆ ϖ m ε) εi *
          toNodeD b₄ hκ hπ ↑(isUnit_D_T1D (π := π) (b₄ := b₄) (t := t) (κ := κ)).unit⁻¹ * hS +
        vR b₄ b₆ ϖ m ε * algebraMap O _ εi * algebraMap O _ ε * hDi + vR b₄ b₆ ϖ m ε * hε'
    · change toNodeD b₄ hκ hπ (ofNode b₄ hκ hπ hε (SR b₄ b₆ ϖ m ε)) = SR b₄ b₆ ϖ m ε
      rw [ofNode, liftNR_SR, IsScalarTower.coe_toAlgHom', toNodeD_algebraMap, toNode, liftT1_s1]
  exact AlgHom.congr_fun this x

/-- **The chart `u ≠ 0` of the Tate model, localized at `D = 1 + b₄ w²`, is the quadratic node
chart**: `T1[1/D] ≃ₐ[O] QuadNode.R ϖ m c D` (`w ↦ u`, `s ↦ S`). -/
def chartEquiv (b₄ : O) (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m)
    (hε : εi * ε = 1) :
    T1D π b₄ t κ ≃ₐ[O] NR b₄ b₆ ϖ m ε :=
  AlgEquiv.ofAlgHom (toNodeD b₄ hκ hπ) (ofNode b₄ hκ hπ hε) (AlgHom.ext (toNode_ofNode hκ hπ hε))
    (AlgHom.ext (ofNode_toNode hκ hπ hε))

lemma chartEquiv_algebraMap (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
    (a : T1 π b₄ t κ) : chartEquiv b₄ hκ hπ hε (algebraMap _ _ a) = toNode b₄ hκ hπ a :=
  toNodeD_algebraMap hκ hπ a

/-- **The coordinate comparison**: the `ℙ¹` coordinate `h' = ℓ₀/u` is `S − t u` on the node
chart. -/
lemma chartEquiv_h1 (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1) :
    chartEquiv b₄ hκ hπ hε (algebraMap _ _ (h1 π b₄ t κ)) =
      SR b₄ b₆ ϖ m ε - algebraMap O _ t * uR b₄ b₆ ϖ m ε := by
  rw [chartEquiv_algebraMap, toNode, liftT1_h1]

lemma chartEquiv_w1 (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1) :
    chartEquiv b₄ hκ hπ hε (algebraMap _ _ (w1 π b₄ t κ)) = uR b₄ b₆ ϖ m ε := by
  rw [chartEquiv_algebraMap, toNode, liftT1_w1]

lemma chartEquiv_s1 (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1) :
    chartEquiv b₄ hκ hπ hε (algebraMap _ _ (s1 π b₄ t κ)) = SR b₄ b₆ ϖ m ε := by
  rw [chartEquiv_algebraMap, toNode, liftT1_s1]

variable (b₄ b₆ ϖ m ε t) in
/-- **The node chart over `ℙ¹`**: `O[X] → QuadNode.R ϖ m c D`, `X ↦ S − t u` (the coordinate
`h' = ℓ₀/u` of the chart `U₁` of `ℙ¹_O`). -/
def coordP1 : O[X] →ₐ[O] NR b₄ b₆ ϖ m ε :=
  Polynomial.aeval (SR b₄ b₆ ϖ m ε - algebraMap O _ t * uR b₄ b₆ ϖ m ε)

lemma toNode_comp_algebraMap (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) :
    (toNode b₄ hκ hπ).comp (IsScalarTower.toAlgHom O O[X] (T1 π b₄ t κ)) =
      coordP1 b₄ b₆ ϖ m ε t :=
  Polynomial.algHom_ext (by
    change toNode b₄ hκ hπ (h1 π b₄ t κ) = _
    rw [toNode, liftT1_h1, coordP1, Polynomial.aeval_X])

end

end TateTwoChartNode

end SemistableReduction
