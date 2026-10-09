/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Orbicurve.Model
import TemperedFundamentalGroups.Orbicurve.ZeroSet

/-!
# Stability of `ringAway W 𝒮` under affine automorphisms, and IUT's removed set `E[ℓ] + M`

Let `𝒮 ⊆ W(k̄)` be a set of geometric points and `g = (ε, m)` an affine automorphism such that
`g⁻¹` maps `𝒮` into itself and `±m ∈ 𝒮` (if `m ≠ 0`). Then `pullback W g` maps
`ringAway W 𝒮`, the ring of functions regular on `W ∖ ({0} ∪ 𝒮)`, into itself
(`pullback_mem_ringAway`).

The proof needs no Nullstellensatz. With `D = x - x(m)` (or `D = 1` if `m = 0`), the coordinates
of `g(genericPoint W)` lie in `k[W][D⁻¹]` (`coords_act_genericPoint_mem`), so for `h ∈ k[W]` we
can write `pullback W g h = a / D^N` with `a ∈ k[W]`. Evaluating at a point `Q` with
`D(Q) ≠ 0` (through the localization `k[W][D⁻¹] → k̄`) gives `a(Q) = h(g Q) · D(Q)^N`
(`exists_pullback_eq`). Hence if all zeros of `h` lie in `𝒮`, all zeros of `a` lie in
`g⁻¹(𝒮) ∪ {±m} ⊆ 𝒮`, and `(pullback W g h)⁻¹ = D^N / a ∈ ringAway W 𝒮`.

For a subgroup `A ≤ AffAut W` with `IsAffStableGeom 𝒮 A` this gives the action of `A` on
`ringAway W 𝒮` by `k`-algebra automorphisms. IUT's set `geomRemovedSet W ℓ M = E[ℓ] + M` of
geometric points is stable under `affGroup W M pm`, which acts on
`geomOrbicurveRing W ℓ M = ringAway W (geomRemovedSet W ℓ M)`, the coordinate ring of
`E ∖ (E[ℓ] + M)`.
-/

universe u

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TemperedFundamentalGroups.Orbicurve

noncomputable section

variable {k : Type u} [Field k] [DecidableEq k] {W : WeierstrassCurve k} [W.IsElliptic]
  {T : Set k}

/-! ### Coordinates of `g(pointOf χ)` -/

omit [DecidableEq k] [W.IsElliptic] in
lemma evalHom_congr {A : Type*} [CommRing A] [Algebra k A] {x y x' y' : A}
    (h : (W.toAffine⁄A).Equation x y) (hx : x = x') (hy : y = y') :
    evalHom W x y h = evalHom W x' y' (hx ▸ hy ▸ h) := by
  subst hx hy
  rfl

/-- The coordinates of `g(pointOf χ)` are the images under `χ` of fixed elements of
`ringOfX W T`, if `x(m) ∈ T` for `m ≠ 0`. -/
lemma exists_coords_act (g : AffAut W) (hm : g.m ≠ 0 → xOf g.m ∈ T) :
    ∃ X Y : ringOfX W T, ∀ (L : Type u) [Field L] [DecidableEq L] [Algebra k L]
      (χ : ringOfX W T →ₐ[k] L), g.act L (pointOf χ) ≠ 0 ∧
        xOf (g.act L (pointOf χ)) = χ X ∧ yOf (g.act L (pointOf χ)) = χ Y := by
  by_cases hm0 : g.m = 0
  · exact ⟨_, _, fun L _ _ _ χ => act_pointOf_of_m_eq_zero χ g hm0⟩
  · exact ⟨_, _, fun L _ _ _ χ => act_pointOf χ g hm0 (hm hm0)⟩

omit [DecidableEq k] [W.IsElliptic] in
lemma ringOfX_le {B : Subalgebra k (funField W)} (hx : xGen W ∈ B) (hy : yGen W ∈ B)
    (hT : ∀ a ∈ T, (xGen W - algebraMap k (funField W) a)⁻¹ ∈ B) : ringOfX W T ≤ B := by
  refine Algebra.adjoin_le ?_
  rintro _ ((rfl | rfl) | ⟨a, ha, rfl⟩)
  exacts [hx, hy, hT a ha]

/-! ### The pullback of a regular function -/

section Pullback

variable {D : W.toAffine.CoordinateRing} (hD : D ≠ 0) (hT : ringOfX W T ≤ (locMap D hD).range)

/-- The evaluation `ringOfX W T → k̄` at a point `Q` with `D(Q) ≠ 0`, for
`ringOfX W T ⊆ k[W][D⁻¹]`. -/
def evalRingOfX {Q : GeomPoint W} (hQ : Q ≠ 0) (hQD : evalPt hQ D ≠ 0) :
    ringOfX W T →ₐ[k] AlgebraicClosure k :=
  (evalLoc (evalPt hQ) hQD).comp ((locMapInv hD).comp (Subalgebra.inclusion hT))

omit [DecidableEq k] [W.IsElliptic] in
lemma locMapInv_algebraMap (c : W.toAffine.CoordinateRing) :
    locMapInv hD ⟨algebraMap _ (funField W) c, algebraMap_mem_range_locMap hD c⟩ =
      algebraMap _ _ c := by
  apply injective_locMap hD
  rw [locMap_locMapInv, locMap_algebraMap]

omit [DecidableEq k] [W.IsElliptic] in
lemma evalRingOfX_algebraMap {Q : GeomPoint W} (hQ : Q ≠ 0) (hQD : evalPt hQ D ≠ 0)
    (c : W.toAffine.CoordinateRing) (hc : algebraMap _ (funField W) c ∈ ringOfX W T) :
    evalRingOfX hD hT hQ hQD ⟨_, hc⟩ = evalPt hQ c := by
  rw [evalRingOfX, AlgHom.comp_apply, AlgHom.comp_apply]
  have : Subalgebra.inclusion hT ⟨_, hc⟩ =
      ⟨algebraMap _ (funField W) c, algebraMap_mem_range_locMap hD c⟩ := rfl
  rw [this, locMapInv_algebraMap, evalLoc_algebraMap]

omit [DecidableEq k] in
lemma pointOf_evalRingOfX {Q : GeomPoint W} (hQ : Q ≠ 0) (hQD : evalPt hQ D ≠ 0) :
    pointOf (evalRingOfX hD hT hQ hQD) = Q := by
  refine Point.ext_xOf_yOf (pointOf_ne_zero _) hQ ?_ ?_
  · rw [xOf_pointOf]
    exact (evalRingOfX_algebraMap hD hT hQ hQD (xC W) xGen_mem_ringOfX).trans (evalPt_xC hQ)
  · rw [yOf_pointOf]
    exact (evalRingOfX_algebraMap hD hT hQ hQD (yC W) yGen_mem_ringOfX).trans (evalPt_yC hQ)

include hD hT in
/-- **The pullback of a regular function.** For `h ∈ k[W]`, `pullback W g h = a / D^N` with
`a ∈ k[W]` and `a(Q) = h(g Q) · D(Q)^N` at every affine point `Q` with `D(Q) ≠ 0`. -/
theorem exists_pullback_eq (g : AffAut W) (hm : g.m ≠ 0 → xOf g.m ∈ T)
    (h : W.toAffine.CoordinateRing) :
    ∃ (a : W.toAffine.CoordinateRing) (N : ℕ),
      pullback W g (algebraMap _ _ h) =
        algebraMap _ (funField W) a * (algebraMap _ (funField W) D)⁻¹ ^ N ∧
      ∀ (Q : GeomPoint W) (hQ : Q ≠ 0) (_ : evalPt hQ D ≠ 0),
        ∃ hgQ : g.act _ Q ≠ 0, evalPt hQ a = evalPt hgQ h * evalPt hQ D ^ N := by
  obtain ⟨X, Y, hXY⟩ := exists_coords_act g hm
  obtain ⟨hne, hx, hy⟩ := hXY (funField W) (ringOfX W T).val
  rw [pointOf_val] at hne hx hy
  have heq : (W.toAffine⁄(ringOfX W T)).Equation X Y :=
    (W.toAffine.baseChange_equation (f := (ringOfX W T).val) Subtype.val_injective X Y).mp
      (by rw [← hx, ← hy]; exact equation_xOf_yOf hne)
  set Φ := evalHom W X Y heq
  have hΦ : (ringOfX W T).val.comp Φ =
      (pullback W g).comp (IsScalarTower.toAlgHom k _ (funField W)) := by
    refine coordRing_algHom_ext ?_ ?_
    · simp only [AlgHom.comp_apply, Φ, evalHom_xC, IsScalarTower.coe_toAlgHom',
        algebraMap_xC, pullback_xGen]
      exact hx.symm
    · simp only [AlgHom.comp_apply, Φ, evalHom_yC, IsScalarTower.coe_toAlgHom',
        algebraMap_yC, pullback_yGen]
      exact hy.symm
  have hw : ((Φ h : ringOfX W T) : funField W) = pullback W g (algebraMap _ _ h) :=
    DFunLike.congr_fun hΦ h
  obtain ⟨a, N, hz⟩ := exists_mk' (locMapInv hD (Subalgebra.inclusion hT (Φ h)))
  have hlz := locMap_locMapInv hD (Subalgebra.inclusion hT (Φ h))
  rw [hz, locMap_mk'] at hlz
  refine ⟨a, N, by rw [← hw, hlz]; rfl, fun Q hQ hQD => ?_⟩
  set χ := evalRingOfX hD hT hQ hQD
  have hχ := pointOf_evalRingOfX hD hT hQ hQD
  obtain ⟨hgQ, hgx, hgy⟩ := hXY (AlgebraicClosure k) χ
  rw [hχ] at hgQ hgx hgy
  refine ⟨hgQ, ?_⟩
  have h1 : evalPt hgQ h = χ (Φ h) := by
    rw [← AlgHom.comp_apply χ Φ, comp_evalHom, evalPt, evalHom_congr _ hgx hgy]
  have h2 : χ (Φ h) = evalLoc (evalPt hQ) hQD
      (IsLocalization.mk' _ a (⟨D ^ N, N, rfl⟩ : Submonoid.powers D)) := by
    rw [← hz]
    rfl
  rw [h1, h2, evalLoc_mk'_mul]

omit [DecidableEq k] [W.IsElliptic] in
lemma inv_algebraMap_pow_mem_ringAway {𝒮 : Set (GeomPoint W)} (hD𝒮 : zeroSet W D ⊆ 𝒮)
    (N : ℕ) : (algebraMap _ (funField W) D)⁻¹ ^ N ∈ ringAway W 𝒮 :=
  pow_mem (inv_mem_ringAway hD𝒮) N

include hD hT in
/-- The stability theorem, for an auxiliary `D` whose zeros lie in `𝒮` and with
`ringOfX W T ⊆ k[W][D⁻¹]`. -/
theorem pullback_mem_ringAway_aux {𝒮 : Set (GeomPoint W)} (hD𝒮 : zeroSet W D ⊆ 𝒮)
    {g : AffAut W} (hm : g.m ≠ 0 → xOf g.m ∈ T) (hg : ∀ P ∈ 𝒮, g⁻¹.act _ P ∈ 𝒮) {f : funField W}
    (hf : f ∈ ringAway W 𝒮) : pullback W g f ∈ ringAway W 𝒮 := by
  suffices ringAway W 𝒮 ≤ (ringAway W 𝒮).comap (pullback W g) from this hf
  refine ringAway_le (fun c => ?_) (fun h hh => ?_)
  · obtain ⟨a, N, ha, -⟩ := exists_pullback_eq hD hT g hm c
    rw [Subalgebra.mem_comap, ha]
    exact mul_mem (algebraMap_mem_ringAway a) (inv_algebraMap_pow_mem_ringAway hD𝒮 N)
  · obtain ⟨a, N, ha, hev⟩ := exists_pullback_eq hD hT g hm h
    rw [Subalgebra.mem_comap, map_inv₀, ha, mul_inv, inv_pow, inv_inv]
    refine mul_mem (inv_mem_ringAway fun Q hQ => ?_) (pow_mem (algebraMap_mem_ringAway D) N)
    obtain ⟨hQ0, hQa⟩ := hQ
    by_cases hQD : evalPt hQ0 D = 0
    · exact hD𝒮 ⟨hQ0, hQD⟩
    obtain ⟨hgQ, hev⟩ := hev Q hQ0 hQD
    rw [hQa, eq_comm, mul_eq_zero, or_iff_left (pow_ne_zero _ hQD)] at hev
    have := hg _ (hh ⟨hgQ, hev⟩)
    rwa [AffAut.act_inv_act] at this

end Pullback

/-! ### Stability -/

omit [DecidableEq k] [W.IsElliptic] in
lemma xC_sub_ne_zero (a : k) : xC W - algebraMap k W.toAffine.CoordinateRing a ≠ 0 := by
  intro h
  apply xGen_sub_ne_zero W a
  have := congrArg (algebraMap _ (funField W)) h
  rwa [map_sub, algebraMap_xC, ← IsScalarTower.algebraMap_apply, map_zero] at this

/-- **Stability.** If `g⁻¹` maps `𝒮` into itself and `±m ∈ 𝒮` (for `m ≠ 0`), the pullback along
`g = (ε, m)` preserves the ring `ringAway W 𝒮` of functions regular on `W ∖ ({0} ∪ 𝒮)`. -/
theorem pullback_mem_ringAway {𝒮 : Set (GeomPoint W)} {g : AffAut W}
    (hg : ∀ P ∈ 𝒮, g⁻¹.act _ P ∈ 𝒮)
    (hm : g.m ≠ 0 → bc W (AlgebraicClosure k) g.m ∈ 𝒮 ∧ -bc W (AlgebraicClosure k) g.m ∈ 𝒮)
    {f : funField W} (hf : f ∈ ringAway W 𝒮) : pullback W g f ∈ ringAway W 𝒮 := by
  by_cases hm0 : g.m = 0
  · have hT : ringOfX W ∅ ≤ (locMap (1 : W.toAffine.CoordinateRing) one_ne_zero).range :=
      ringOfX_le (algebraMap_mem_range_locMap _ (xC W))
        (algebraMap_mem_range_locMap _ (yC W)) (fun a ha => ha.elim)
    exact pullback_mem_ringAway_aux one_ne_zero hT (by rw [zeroSet_one]; exact Set.empty_subset _)
      (fun h => absurd hm0 h) hg hf
  · set D := xC W - algebraMap k W.toAffine.CoordinateRing (xOf g.m)
    have hD : D ≠ 0 := xC_sub_ne_zero _
    have hιD : algebraMap _ (funField W) D = xGen W - algebraMap k (funField W) (xOf g.m) := by
      rw [map_sub, algebraMap_xC, ← IsScalarTower.algebraMap_apply]
    have hT : ringOfX W {xOf g.m} ≤ (locMap D hD).range :=
      ringOfX_le (algebraMap_mem_range_locMap _ (xC W)) (algebraMap_mem_range_locMap _ (yC W))
        (fun a ha => by rw [Set.mem_singleton_iff.mp ha, ← hιD]; exact inv_mem_range_locMap hD)
    refine pullback_mem_ringAway_aux hD hT (fun Q hQ => ?_) (fun _ => rfl) hg hf
    obtain ⟨hQ0, hQx⟩ := (mem_zeroSet_xC_sub _).mp hQ
    have hbc : bc W (AlgebraicClosure k) g.m ≠ 0 := by rwa [Ne, bc_eq_zero_iff]
    have hpm : Q = bc W _ g.m ∨ Q = -bc W _ g.m := by
      rw [eq_some_xOf_yOf hQ0, eq_some_xOf_yOf hbc]
      exact Point.X_eq_iff.mp (by rw [hQx, xOf_bc])
    rcases hpm with rfl | rfl
    exacts [(hm hm0).1, (hm hm0).2]

variable (W) in
/-- A set `𝒮 ⊆ W(k̄)` of geometric points is *stable* under a subgroup `A` of affine
automorphisms if it is stable under negation and under every element of `A`, and contains the
translation parts `m ≠ 0` of the elements of `A`. Then `W ∖ ({0} ∪ 𝒮)` is stable under `A`, and
`A` acts on its coordinate ring `ringAway W 𝒮`. -/
class IsAffStableGeom (𝒮 : Set (GeomPoint W)) (A : Subgroup (AffAut W)) : Prop where
  neg_mem : ∀ P ∈ 𝒮, -P ∈ 𝒮
  act_mem : ∀ g ∈ A, ∀ P ∈ 𝒮, g.act _ P ∈ 𝒮
  bc_mem : ∀ g ∈ A, g.m ≠ 0 → bc W (AlgebraicClosure k) g.m ∈ 𝒮

variable (𝒮 : Set (GeomPoint W)) (A : Subgroup (AffAut W)) [IsAffStableGeom W 𝒮 A]

lemma smul_mem_ringAway (g : A) {f : funField W} (hf : f ∈ ringAway W 𝒮) :
    (g : AffAut W) • f ∈ ringAway W 𝒮 := by
  rw [smul_funField_def]
  refine pullback_mem_ringAway (fun P hP => ?_) (fun hm => ?_) hf
  · rw [inv_inv]
    exact IsAffStableGeom.act_mem _ g.2 P hP
  · have := IsAffStableGeom.bc_mem (W := W) (𝒮 := 𝒮) _ (A.inv_mem g.2) hm
    exact ⟨this, IsAffStableGeom.neg_mem (A := A) _ this⟩

/-- The action of a subgroup `A` of affine automorphisms on the coordinate ring of
`W ∖ ({0} ∪ 𝒮)`, for `𝒮` stable under `A`. -/
instance : MulSemiringAction A (ringAway W 𝒮) where
  smul g r := ⟨(g : AffAut W) • (r : funField W), smul_mem_ringAway 𝒮 A g r.2⟩
  one_smul r := Subtype.ext (one_smul (AffAut W) (r : funField W))
  mul_smul g h r := Subtype.ext (mul_smul (g : AffAut W) (h : AffAut W) (r : funField W))
  smul_zero g := Subtype.ext (smul_zero (g : AffAut W))
  smul_add g r s := Subtype.ext (smul_add (g : AffAut W) (r : funField W) s)
  smul_one g := Subtype.ext (smul_one (g : AffAut W))
  smul_mul g r s := Subtype.ext (smul_mul' (g : AffAut W) (r : funField W) s)

@[simp] lemma coe_smul_ringAway (g : A) (r : ringAway W 𝒮) :
    ((g • r : ringAway W 𝒮) : funField W) = (g : AffAut W) • (r : funField W) := rfl

instance : SMulCommClass A k (ringAway W 𝒮) :=
  ⟨fun g c r => Subtype.ext (smul_comm (g : AffAut W) c (r : funField W))⟩

/-! ### IUT's removed set `E[ℓ] + M` -/

section RemovedSetIn

variable (W) (K : Type*) [Field K] [DecidableEq K] [Algebra k K]

/-- The set `E[ℓ] + M ⊆ W(K)` of `K`-points, for an extension `K` of `k`. -/
def removedSetIn (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) : Set (W.toAffine⁄K).Point :=
  {P | ∃ m ∈ M, ℓ • (P - bc W K m) = 0}

variable {W K} {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}

omit [W.IsElliptic] in
lemma zero_mem_removedSetIn : (0 : (W.toAffine⁄K).Point) ∈ removedSetIn W K ℓ M :=
  ⟨0, M.zero_mem, by rw [map_zero, sub_zero, smul_zero]⟩

omit [W.IsElliptic] in
lemma neg_mem_removedSetIn {P : (W.toAffine⁄K).Point} (hP : P ∈ removedSetIn W K ℓ M) :
    -P ∈ removedSetIn W K ℓ M := by
  obtain ⟨m, hm, h⟩ := hP
  refine ⟨-m, M.neg_mem hm, ?_⟩
  rw [map_neg, neg_sub_neg, ← neg_sub, smul_neg, h, neg_zero]

omit [W.IsElliptic] in
lemma act_mem_removedSetIn {pm : Bool} {g : AffAut W} (hg : g ∈ affGroup W M pm)
    {P : (W.toAffine⁄K).Point} (hP : P ∈ removedSetIn W K ℓ M) :
    g.act K P ∈ removedSetIn W K ℓ M := by
  obtain ⟨m, hm, h⟩ := hP
  refine ⟨g.ε • m + g.m, M.add_mem ?_ hg.1, ?_⟩
  · rw [Units.smul_def]
    exact M.zsmul_mem hm _
  · rw [AffAut.act_def, map_add, bc_units_smul, add_sub_add_right_eq_sub, ← smul_sub,
      smul_comm, h, smul_zero]

omit [W.IsElliptic] in
lemma bc_mem_removedSetIn {m : W.toAffine.Point} (hm : m ∈ M) :
    bc W K m ∈ removedSetIn W K ℓ M :=
  ⟨m, hm, by rw [sub_self, smul_zero]⟩

omit [W.IsElliptic] in
/-- The rational points of `removedSetIn W K ℓ M` are those of `removedSet W ℓ M`. -/
lemma bc_mem_removedSetIn_iff {P : W.toAffine.Point} :
    bc W K P ∈ removedSetIn W K ℓ M ↔ P ∈ removedSet W ℓ M := by
  refine exists_congr fun m => and_congr_right fun _ => ?_
  rw [← map_sub, ← map_nsmul, bc_eq_zero_iff]

end RemovedSetIn

variable (W) in
/-- The set `E[ℓ] + M ⊆ W(k̄)` of geometric points removed in IUT's orbicurve `(E, ℓ, M, ±)`
(all of `E[ℓ]`, not only its rational points). -/
abbrev geomRemovedSet (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) : Set (GeomPoint W) :=
  removedSetIn W (AlgebraicClosure k) ℓ M

instance (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) (pm : Bool) :
    IsAffStableGeom W (geomRemovedSet W ℓ M) (affGroup W M pm) where
  neg_mem _ := neg_mem_removedSetIn
  act_mem _ hg _ := act_mem_removedSetIn hg
  bc_mem _ hg _ := bc_mem_removedSetIn hg.1

variable (W) in
/-- The coordinate ring of `Y = E ∖ (E[ℓ] + M)` (all geometric points of `E[ℓ] + M` removed),
the affine curve presenting IUT's orbicurve `(E, ℓ, M, ±)` as `[Y / affGroup W M pm]`. -/
abbrev geomOrbicurveRing (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) :
    Subalgebra k (funField W) :=
  ringAway W (geomRemovedSet W ℓ M)

example (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) (pm : Bool) :
    MulSemiringAction (affGroup W M pm) (geomOrbicurveRing W ℓ M) := inferInstance

example (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) (pm : Bool) :
    SMulCommClass (affGroup W M pm) k (geomOrbicurveRing W ℓ M) := inferInstance

end

end TemperedFundamentalGroups.Orbicurve
