/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.Kummer
import TemperedFundamentalGroups.SemistableReduction.UniqueExtDVR
import TemperedFundamentalGroups.Andre.TateCuspInertia
import ContinuousKummerTheory.Curve.RationalSection

/-!
# `Π^tp_X ↠ G_k` at a base point over a rational point

The tempered fundamental group `Π^tp = temperedPi1 O R A V hV` of the Galois model `D` of an
affine curve `U = Spec R` over a field `k` maps to `G_k = Gal(k̄/k)` through
`Π^tp → Π_U → G_k` (`Kummer.tempToPi` followed by the arithmetic quotient
`KummerTheory.Curve.piToGk`, restriction to the constants `k̄ ⊆ Ω`). This is the map
`Π^tp_X ↠ G_k` of the tempered homotopy exact sequence `1 → Δ^tp → Π^tp → G_k → 1`.

The base point is a valuation subring `V ⊆ Ω` with `V ∩ k = O`. Its decomposition group maps
to `Π^tp` (`galoisToTempered`), but in general only onto a subgroup of `G_k` (for `V` centred at
a closed point with residue field `k' ≠ k` the image is `G_{k'}`). Here `V` lies **over a
`k`-rational point** `x ∈ U(k)`: `V ⊆ A` for a place `A ⊇ k` of `Ω` above `x` (the residues of the
function field at `A` lie in `k`, `hrat`). Then the decomposition group of `V` surjects onto
`G_k` when `O` is a complete discrete valuation ring:

* `ValuationSubring.resVal`: for valuation subrings `V ≤ A` of a field, the image of `V` in the
  residue field `κ(A)` is a valuation subring (`𝔪_A ⊆ V`, `ValuationSubring.mem_of_mem_nonunits`),
  and `V` is the preimage of it (`ValuationSubring.mem_iff_residue_mem_resVal`);
* **`ValuationSubring.smul_mem_iff_of_le`**: if `O` is a complete DVR, `κ(A)` is algebraic over
  `k` and `V ∩ k = O`, every `k`-automorphism `σ` of `Ω` with `σ(A) = A` satisfies `σ(V) = V`:
  `σ(V)` and `V` both refine `A`, and their images in `κ(A)` are extensions of `O`, which are
  unique (`SemistableReduction.CrossingAux.eq_of_comap_eq_dvr`);
* hence `D_A ⊆ D_V`, and `D_A ↠ G_k` for the rational point (continuous-kummer-theory
  `decompositionMap_surjective_of_rational`, `kbarResidue_piToGk_decompToPi`):
  **`Kummer.exists_galoisToTempered_piToGk_eq`** — every `g ∈ G_k` is the image of
  `galoisToTempered σ` for some `σ` in the decomposition group of `V`;
* **`Kummer.piToGk_tempToPi_surjective`**: `Π^tp → G_k` is surjective;
* **`Kummer.exists_mem_ker_character_piToGk_eq`**: for Tate data `T` on `R`, already
  `Π^tp_Y = ker χ ↠ G_k` (Galois elements lie in `Π^tp_Y`, `character_galoisToTempered`).
  This is the hypothesis `hsurj` of the theta-environment theorems of `iut`
  (`Iut/EtaleTheta/Env`), whose `augT` is `piToGk ∘ tempToPi` and whose `Π^tp_Y` is `ker χ`.

The choice of `V` over a rational point is a choice of base point; for an arbitrary `V` the
surjectivity of `Π^tp → G_k` would need the independence of `Π^tp` of the base point (not
formalised).
-/

universe u

open IsLocalRing

open scoped Pointwise

namespace ValuationSubring

section Refine

variable {K : Type*} [Field K] (A V : ValuationSubring K)

/-- `𝔪_A ⊆ V` for a valuation subring `V ≤ A`. -/
theorem mem_of_mem_nonunits (hVA : V ≤ A) {x : K} (hx : x ∈ A.nonunits) : x ∈ V :=
  V.nonunits_subset (nonunits_le_nonunits.mpr hVA hx)

/-- The image `V/𝔪_A ⊆ κ(A)` of a valuation subring `V ≤ A`. -/
def resSub : Subring (ResidueField A) :=
  (V.toSubring.comap A.subtype).map (residue A)

variable {A V}

/-- **`V` is the preimage of its image in `κ(A)`.** -/
theorem mem_iff_residue_mem_resSub (hVA : V ≤ A) (x : A) :
    (x : K) ∈ V ↔ residue A x ∈ resSub A V := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    have hy' : (y : K) ∈ V := hy
    have h0 : residue A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    rw [residue_eq_zero_iff] at h0
    have hm : ((x - y : A) : K) ∈ V :=
      mem_of_mem_nonunits A V hVA (coe_mem_nonunits_iff.mpr h0)
    have : (x : K) = ((x - y : A) : K) + y := by push_cast; ring
    rw [this]
    exact V.toSubring.add_mem hm hy'

variable (A V)

/-- **The image of `V ≤ A` in `κ(A)` is a valuation subring.** -/
def resVal (hVA : V ≤ A) : ValuationSubring (ResidueField A) where
  toSubring := resSub A V
  mem_or_inv_mem' y := by
    obtain ⟨x, rfl⟩ := residue_surjective y
    by_cases hx : residue A x = 0
    · left
      rw [hx]
      exact (resSub A V).zero_mem
    · obtain ⟨u, rfl⟩ := (residue_ne_zero_iff_isUnit x).mp hx
      rcases V.mem_or_inv_mem ((u : A) : K) with h | h
      · left
        exact (mem_iff_residue_mem_resSub hVA _).mp h
      · right
        have hinv : (((u⁻¹ : Aˣ) : A) : K) = ((u : A) : K)⁻¹ := by
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← A.coe_mul, Units.inv_mul, A.coe_one]
        have h' : (((u⁻¹ : Aˣ) : A) : K) ∈ V := by rw [hinv]; exact h
        have := (mem_iff_residue_mem_resSub hVA _).mp h'
        rw [map_units_inv] at this
        exact this

theorem mem_iff_residue_mem_resVal (hVA : V ≤ A) (x : A) :
    (x : K) ∈ V ↔ residue A x ∈ resVal A V hVA :=
  mem_iff_residue_mem_resSub hVA x

variable {k : Type*} [Field k] [Algebra k K] (O : ValuationSubring k)
  (hk : ∀ c : k, algebraMap k K c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k K c, hk c⟩ = algebraMap k (ResidueField A) c)

include hkres in
/-- The image of `V ≤ A` in `κ(A)` lies over `O = V ∩ k`. -/
theorem comap_resVal (hVA : V ≤ A) (hV : V.comap (algebraMap k K) = O) :
    (resVal A V hVA).comap (algebraMap k (ResidueField A)) = O := by
  ext c
  rw [mem_comap, ← hkres, ← mem_iff_residue_mem_resVal A V hVA, ← hV, mem_comap]

include hkres in
/-- **Automorphisms preserving `A` preserve every refinement `V ≤ A` over a complete DVR**:
if `O` is a complete DVR, `κ(A)` is algebraic over `k` and `V ∩ k = O`, then every
`k`-automorphism `σ` with `σ(A) = A` satisfies `σ(V) = V` (the image of `V` in `κ(A)` is the
unique extension of `O`). -/
theorem apply_mem_iff_of_le [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Algebra.IsAlgebraic k (ResidueField A)] (hVA : V ≤ A)
    (hV : V.comap (algebraMap k K) = O) (σ : K ≃ₐ[k] K) (hσA : ∀ x, σ x ∈ A ↔ x ∈ A) (x : K) :
    σ x ∈ V ↔ x ∈ V := by
  set V' : ValuationSubring K := V.comap (σ : K →+* K)
  have hV'A : V' ≤ A := fun y hy => (hσA y).1 (hVA hy)
  have hV' : V'.comap (algebraMap k K) = O := by
    rw [← hV]
    ext c
    simp only [V', mem_comap]
    change σ (algebraMap k K c) ∈ V ↔ _
    rw [σ.commutes]
  have hW : resVal A V' hV'A = resVal A V hVA :=
    TemperedFundamentalGroups.SemistableReduction.CrossingAux.eq_of_comap_eq_dvr O
      (comap_resVal A V' O hk hkres hV'A hV') (comap_resVal A V O hk hkres hVA hV)
  by_cases hxA : x ∈ A
  · have h1 := mem_iff_residue_mem_resVal A V' hV'A ⟨x, hxA⟩
    have h2 := mem_iff_residue_mem_resVal A V hVA ⟨x, hxA⟩
    change x ∈ V' ↔ _
    rw [h1, h2, hW]
  · exact ⟨fun h => absurd ((hσA x).1 (hVA h)) hxA, fun h => absurd (hVA h) hxA⟩

end Refine

/-! ### Existence of a base point refining a place -/

section Compose

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : ValuationSubring (ResidueField A))

/-- The composite valuation subring `{x ∈ A | x̄ ∈ W}` of a valuation subring `A` and a valuation
subring `W` of its residue field. -/
def compose : ValuationSubring K where
  toSubring := (W.toSubring.comap (residue A)).map A.subtype
  mem_or_inv_mem' x := by
    have key : ∀ (y : K) (hy : y ∈ A), residue A ⟨y, hy⟩ ∈ W →
        y ∈ (W.toSubring.comap (residue A)).map A.subtype :=
      fun y hy h => ⟨⟨y, hy⟩, h, rfl⟩
    by_cases hxA : x ∈ A
    · by_cases h0 : residue A ⟨x, hxA⟩ = 0
      · left
        exact key x hxA (by rw [h0]; exact W.zero_mem)
      · rcases W.mem_or_inv_mem (residue A ⟨x, hxA⟩) with h | h
        · left
          exact key x hxA h
        · right
          obtain ⟨u, hu⟩ := (residue_ne_zero_iff_isUnit _).mp h0
          have hinv : (((u⁻¹ : Aˣ) : A) : K) = x⁻¹ := by
            refine eq_inv_of_mul_eq_one_left ?_
            have : (x : K) = ((u : A) : K) := by rw [hu]
            rw [this, ← A.coe_mul, Units.inv_mul, A.coe_one]
          rw [← hinv]
          refine key _ ((u⁻¹ : Aˣ) : A).2 ?_
          rw [Subtype.coe_eta, map_units_inv, hu]
          exact h
    · right
      have hinv : x⁻¹ ∈ A.nonunits := by
        rw [mem_nonunits_iff_or]
        right
        rwa [inv_inv]
      obtain ⟨hA, hm⟩ := mem_nonunits_iff_exists_mem_maximalIdeal.mp hinv
      exact key _ hA (by rw [(residue_eq_zero_iff _).mpr hm]; exact W.zero_mem)

variable {A W}

theorem mem_compose {x : K} : x ∈ compose A W ↔ ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ W := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem compose_le : compose A W ≤ A := fun _ hx => (mem_compose.mp hx).1

variable {k : Type*} [Field k] [Algebra k K] (O : ValuationSubring k)
  (hk : ∀ c : k, algebraMap k K c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k K c, hk c⟩ = algebraMap k (ResidueField A) c)

include hkres in
theorem comap_compose (hW : W.comap (algebraMap k (ResidueField A)) = O) :
    (compose A W).comap (algebraMap k K) = O := by
  ext c
  rw [mem_comap, mem_compose, ← hW, mem_comap, ← hkres]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hk c, h⟩⟩

omit [Algebra k K] in
/-- **Every valuation subring `O` of `k` extends to any field `L ⊇ k`** (Chevalley; Mathlib's
`LocalSubring.exists_le_valuationSubring` applied to the image of `O`). -/
theorem exists_comap_eq {L : Type*} [Field L] [Algebra k L] :
    ∃ W : ValuationSubring L, W.comap (algebraMap k L) = O := by
  set f : O →+* L := (algebraMap k L).comp O.subtype
  obtain ⟨B, hB⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hB
  refine ⟨B, le_antisymm ?_ fun c hc => hle ⟨⟨c, hc⟩, rfl⟩⟩
  intro c hc
  by_contra hcO
  have hc0 : c ≠ 0 := fun h => hcO (h ▸ O.zero_mem)
  have hinvO : c⁻¹ ∈ O := (O.mem_or_inv_mem c).resolve_left hcO
  -- `f c⁻¹ ∈ range f` is a unit in `B`, hence in `range f`, so `c ∈ O`
  set y : (LocalSubring.range f).toSubring := ⟨f ⟨c⁻¹, hinvO⟩, ⟨⟨c⁻¹, hinvO⟩, rfl⟩⟩
  have hunitB : IsUnit (Subring.inclusion hle y) := by
    refine IsUnit.of_mul_eq_one (⟨algebraMap k L c, hc⟩ : B) ?_
    apply Subtype.ext
    change algebraMap k L c⁻¹ * algebraMap k L c = 1
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have hunit : IsUnit y := (hloc.map_nonunit y) hunitB
  obtain ⟨z, hz⟩ := hunit.exists_right_inv
  obtain ⟨⟨d, hd⟩, hdz⟩ := z.2
  have hval : algebraMap k L (c⁻¹ * d) = 1 := by
    have := congrArg Subtype.val hz
    rw [map_mul]
    change algebraMap k L c⁻¹ * (z : L) = 1 at this
    rw [← hdz] at this
    exact this
  have hcd : c⁻¹ * d = 1 := (algebraMap k L).injective (by rw [hval, map_one])
  have : c = d := by
    have h := congrArg (c * ·) hcd
    simp only [mul_inv_cancel_left₀ hc0, mul_one] at h
    exact h.symm
  exact hcO (this ▸ hd)

include hkres in
/-- **A base point over a place**: every place `A` of `K` containing `k` is refined by a
valuation subring `V ≤ A` with `V ∩ k = O`. -/
theorem exists_le_comap_eq : ∃ V : ValuationSubring K, V ≤ A ∧ V.comap (algebraMap k K) = O := by
  obtain ⟨W, hW⟩ := exists_comap_eq O (L := ResidueField A)
  exact ⟨compose A W, compose_le, comap_compose O hk hkres hW⟩

end Compose

end ValuationSubring

namespace TemperedFundamentalGroups

namespace Kummer

noncomputable section

open KummerTheory KummerTheory.Curve AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)
  (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)]
  (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)
  (hHL : D.HL = D.H) (hVA : V ≤ A)
  [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
include hHL in
/-- In the scheme case `H_L = H`, an automorphism of `Ω` over the field `F = Ω^H` fixes the
coordinate ring `R`. -/
theorem fixes_R (σ : Ω ≃ₐ[F D] Ω) (r : D.R) :
    σ (algebraMap D.R Ω r) = algebraMap D.R Ω r := by
  have hmem : algebraMap D.R Ω r ∈ F D := by
    have h := Pi1.Orbifold.CoordRing.algebraMap_mem r
    change algebraMap D.R Ω r ∈ IntermediateField.fixedField D.HL at h
    rw [hHL] at h
    exact h
  exact σ.commutes ⟨_, hmem⟩

/-- An automorphism of `Ω` over `F` as an `R`-algebra automorphism (scheme case). -/
def toRAut (σ : Ω ≃ₐ[F D] Ω) : Ω ≃ₐ[D.R] Ω :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fixes_R D hHL σ)

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
@[simp]
theorem toRAut_apply (σ : Ω ≃ₐ[F D] Ω) (x : Ω) : toRAut D hHL σ x = σ x := rfl

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
include hk hkres hVA hV in
/-- **`D_A ⊆ D_V`** for a refinement `V ≤ A` over a complete DVR. -/
theorem toRAut_mem_decompositionGroup (σ : A.decompositionSubgroup (F D)) :
    toRAut D hHL σ.1 ∈ decompositionGroup D.R V := by
  have hσA : ∀ x, σ.1 x ∈ A ↔ x ∈ A := by
    intro x
    have h := ValuationSubring.smul_mem_pointwise_smul_iff (g := σ.1) (S := A) (x := x)
    rw [MulAction.mem_stabilizer_iff.mp σ.2] at h
    exact h
  haveI : Algebra.IsAlgebraic k (ResidueField A) := Algebra.IsIntegral.isAlgebraic
  intro x
  exact ValuationSubring.apply_mem_iff_of_le A V O hk hkres hVA hV
    ((σ.1 : Ω ≃ₐ[F D] Ω).restrictScalars k) hσA x

omit [Algebra.IsIntegral k (ResidueField A)] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] in
include hkres in
/-- The image in `G_k` of `galoisToTempered (σ|_R)` is the restriction of `σ ∈ D_A` to `k̄`,
read through the reduction `k̄ ≅ κ(A)`. -/
theorem kbarResidue_piToGk_tempToPi (σ : A.decompositionSubgroup (F D))
    (hσ : toRAut D hHL σ.1 ∈ decompositionGroup D.R V) (y : kbar k Ω) :
    kbarResidue A hk (piToGk D (tempToPi D O V hV
        (galoisToTempered O D.R D.A hV ⟨toRAut D hHL σ.1, hσ⟩)) y) =
      Decomposition.decompositionMap (F D) A hk hkres σ (kbarResidue A hk y) := by
  rw [tempToPi_galoisToTempered, piToGk_mk, kbarResidue_apply, kbarResidue_apply,
    Decomposition.decompositionMap_residue]
  congr 1
  apply Subtype.ext
  change algebraMap (kbar k Ω) Ω (hToGk D _ y) = σ.1 (y : Ω)
  rw [algebraMap_hToGk_apply, galoisToH_apply, toRAut_apply]

include hrat hk hkres hVA hV hHL in
/-- **Every `g ∈ G_k` comes from a Galois element of the base point `V`**, when `V` lies over a
`k`-rational point (`V ≤ A`, `hrat`) and `O` is a complete DVR. -/
theorem exists_galoisToTempered_piToGk_eq (g : Gk k Ω) :
    ∃ σ : decompositionGroup D.R V,
      piToGk D (tempToPi D O V hV (galoisToTempered O D.R D.A hV σ)) = g := by
  set e := kbarEquiv A hk hkres
  obtain ⟨σ, hσ⟩ := decompositionMap_surjective_of_rational D A hk hkres hrat
    (e.symm.trans (g.trans e))
  have hmem := toRAut_mem_decompositionGroup D O V hV A hk hkres hHL hVA σ
  refine ⟨⟨_, hmem⟩, AlgEquiv.ext fun y => ?_⟩
  apply (kbarResidue A hk).injective
  rw [kbarResidue_piToGk_tempToPi D O V hV A hk hkres hHL σ hmem, hσ]
  change e (g (e.symm (kbarResidue A hk y))) = kbarResidue A hk (g y)
  rw [show kbarResidue A hk y = e y from rfl, e.symm_apply_apply]
  rfl

include hrat hk hkres hVA hV hHL in
/-- **`Π^tp → G_k` is surjective** at a base point over a rational point. -/
theorem piToGk_tempToPi_surjective :
    Function.Surjective ((piToGk D).comp (tempToPi D O V hV)) := fun g => by
  obtain ⟨σ, hσ⟩ := exists_galoisToTempered_piToGk_eq D O V hV A hk hkres hrat hHL hVA g
  exact ⟨_, hσ⟩

include hrat hk hkres hVA hV hHL in
/-- **`Π^tp_Y ↠ G_k`** ([EtTh] §1, the exact sequence `1 → Δ^tp_Y → Π^tp_Y → G_k → 1` used
throughout [EtTh] §2): for Tate data `T` on `R`, every `g ∈ G_k` is the image of an element of
`Π^tp_Y = ker χ`, namely of a Galois element of the base point. This is the hypothesis `hsurj` of
the theta-environment theorems of `iut` (`augT = piToGk ∘ tempToPi`, `piY = ker χ`). -/
theorem exists_mem_ker_character_piToGk_eq [IsReduced D.R] [Subsingleton D.A]
    (T : TateObject.Data O D.R) (g : Gk k Ω) :
    ∃ h ∈ (TateObject.character (A := D.A) T V hV).ker,
      piToGk D (tempToPi D O V hV h) = g := by
  obtain ⟨σ, hσ⟩ := exists_galoisToTempered_piToGk_eq D O V hV A hk hkres hrat hHL hVA g
  exact ⟨_, character_galoisToTempered hV T σ, hσ⟩

/-! ### The tempered homotopy exact sequence `1 → Δ^tp → Π^tp → G_k → 1` -/

omit [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] in
/-- **The geometric tempered fundamental group** `Δ^tp = Ker(Π^tp → G_k)`. -/
def deltaTemp : Subgroup (TempPi D O V hV) := ((piToGk D).comp (tempToPi D O V hV)).ker

omit [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] in
theorem mem_deltaTemp (γ : TempPi D O V hV) :
    γ ∈ deltaTemp D O V hV ↔ piToGk D (tempToPi D O V hV γ) = 1 := Iff.rfl

omit [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] in
instance deltaTemp_normal : (deltaTemp D O V hV).Normal := MonoidHom.normal_ker _

include hrat hk hkres hVA hV hHL in
/-- **`Π^tp = Δ^tp · D_V`** at a base point over a rational point: every element of `Π^tp` is a
geometric element times a Galois element of the base point. -/
theorem exists_mem_deltaTemp_mul_galoisToTempered (γ : TempPi D O V hV) :
    ∃ δ ∈ deltaTemp D O V hV, ∃ σ : decompositionGroup D.R V,
      γ = δ * galoisToTempered O D.R D.A hV σ := by
  obtain ⟨σ, hσ⟩ := exists_galoisToTempered_piToGk_eq D O V hV A hk hkres hrat hHL hVA
    (piToGk D (tempToPi D O V hV γ))
  refine ⟨γ * (galoisToTempered O D.R D.A hV σ)⁻¹, ?_, σ, by group⟩
  change ((piToGk D).comp (tempToPi D O V hV)) (γ * (galoisToTempered O D.R D.A hV σ)⁻¹) = 1
  rw [map_mul, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hσ, mul_inv_cancel]

include hrat hk hkres hVA hV hHL in
/-- **The exact sequence `1 → Δ^tp_Y → Π^tp_Y → G_k → 1`** for Tate data `T` on `R`
(`Π^tp_Y = ker χ`, `Δ^tp_Y = Δ^tp ∩ Π^tp_Y`): the kernel of `Π^tp_Y → G_k` is `Δ^tp_Y` (by
definition) and the map is surjective (`exists_mem_ker_character_piToGk_eq`). -/
theorem deltaTemp_inf_ker_character [IsReduced D.R] [Subsingleton D.A]
    (T : TateObject.Data O D.R) :
    (((piToGk D).comp (tempToPi D O V hV)).comp
        (TateObject.character (A := D.A) T V hV).ker.subtype).ker =
      (deltaTemp D O V hV).subgroupOf (TateObject.character (A := D.A) T V hV).ker ∧
    Function.Surjective (((piToGk D).comp (tempToPi D O V hV)).comp
        (TateObject.character (A := D.A) T V hV).ker.subtype) := by
  refine ⟨rfl, fun g => ?_⟩
  obtain ⟨h, hh, hg⟩ := exists_mem_ker_character_piToGk_eq D O V hV A hk hkres hrat hHL hVA T g
  exact ⟨⟨h, hh⟩, hg⟩

end

end Kummer

end TemperedFundamentalGroups
