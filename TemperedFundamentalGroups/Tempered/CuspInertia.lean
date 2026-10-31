/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.Kummer
import TemperedFundamentalGroups.SemistableReduction.CompositeValuation
import ContinuousKummerTheory.Curve.Residue

/-!
# Inertia groups of places in the tempered fundamental group

Let `W ⊆ Ω` be a valuation subring of the field of the geometric point (for a curve over `k`: a
place `W ⊇ k` of `Ω`, e.g. one centred on a cusp). Its **inertia group** in `Aut_R(Ω)` is
`inertiaGroup R W`: the `σ` with `σ(W) = W` acting trivially on the residue field of `W`
(`σ, σ⁻¹ ∈ inertiaSet R W`). For a base point `V ≤ W` (a composite of `W` with a valuation
of its residue field; such `V` over `O` exist, `exists_le_comap_eq`), every inertia element
preserves `V` (`inertiaGroup_le_decompositionGroup`), so `galoisToTempered` gives

* **`inertiaToTempered`** `: I_W → Π^tp` and its image **`inertiaTempered`** `= I^tp_W ≤ Π^tp`
  (the inertia group of `W` in the tempered fundamental group, for the base point `V`);
* `temperedToEtale_inertiaToTempered`: compatibility with the Galois action on `π₁ᵉᵗ`;
* change of level: `temperedPi1Map_galoisToTempered` (naturality of the Galois elements along maps
  of orbifolds) and **`temperedPi1Map_inertiaToTempered`**, `map_inertiaTempered_le`;
* for a curve in the Galois model (`Kummer` namespace, `D : GaloisData k t`):
  `mem_inertiaGroup_iff` (for `Ω` algebraic over `k(t)`, `σ ∈ I_W` iff `σ ∈ inertiaSet R W`),
  **`tempToPi_inertiaToTempered`** (`tempToPi` maps `σ` to `σ ∈ H`), **`tempToPi_inertiaTempered`**
  (the image of `I^tp_W` in `Π_U` is the image of `I_W ∩ H_L`), and
  **`evalTriv_kummerMapTempered_inertia`**: on `I^tp_W` the tempered Kummer class `κ^tp_n(u)` is
  evaluated by the étale Kummer class `κ_n(u)` on `I_W ∩ H` (so the cusp statements of
  `continuous-kummer-theory` hold verbatim on `I^tp_W`).

This is requirement T1 of the étale theta track (`MR14-plan.md`, run 10). It does not use the
semistable models of `Spec R` (the inertia elements act on tempered fibres as Galois elements of the
base point). Injectivity of `I_W → Π^tp` is not proved here (it is the injectivity of the cusp
inertia into `π₁ᵉᵗ(U)`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

/-! ### The inertia group of a place -/

namespace CuspInertia

variable {P Ω : Type u} [Field Ω] [CommRing P] [Algebra P Ω] {W : ValuationSubring Ω}

variable (P) in
/-- The `P`-automorphisms `σ` of `Ω` acting trivially on the residue field of `W`:
`v_W(σ a − a) < 1` for all `a ∈ W` (`GaloisPi1.inertia W` for a ring `P`). -/
def inertiaSet (W : ValuationSubring Ω) : Set (Ω ≃ₐ[P] Ω) :=
  {σ | ∀ a ∈ W, W.valuation (σ a - a) < 1}

/-- Inertia elements map `W` into itself. -/
theorem mem_of_mem_inertia {σ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertiaSet P W) {a : Ω}
    (ha : a ∈ W) : σ a ∈ W := by
  rw [← W.valuation_le_one_iff] at ha ⊢
  have h : σ a = (σ a - a) + a := by ring
  rw [h]
  exact Valuation.map_add_le _ (hσ a ((W.valuation_le_one_iff _).mp ha)).le ha

theorem one_mem_inertia : (1 : Ω ≃ₐ[P] Ω) ∈ inertiaSet P W := fun a _ => by
  simp [AlgEquiv.one_apply]

theorem mul_mem_inertia {σ τ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertiaSet P W)
    (hτ : τ ∈ inertiaSet P W) : σ * τ ∈ inertiaSet P W := fun a ha => by
  have h : (σ * τ) a - a = (σ (τ a) - τ a) + (τ a - a) := by rw [AlgEquiv.mul_apply]; ring
  rw [h]
  exact Valuation.map_add_lt _ (hσ _ (mem_of_mem_inertia hτ ha)) (hτ a ha)

theorem pow_mem_inertia {σ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertiaSet P W) (m : ℕ) :
    σ ^ m ∈ inertiaSet P W := by
  induction m with
  | zero => rw [pow_zero]; exact one_mem_inertia
  | succ m ih => rw [pow_succ]; exact mul_mem_inertia ih hσ

/-- On an algebraic extension of fields, `σ⁻¹ a = σ ^ m a` for some `m` (the orbit of `a` lies in
the finite set of roots of its minimal polynomial). -/
theorem exists_pow_apply_eq_inv_apply {P : Type u} [Field P] [Algebra P Ω]
    [Algebra.IsIntegral P Ω] (σ : Ω ≃ₐ[P] Ω) (a : Ω) : ∃ m : ℕ, (σ ^ m) a = σ⁻¹ a := by
  classical
  have hint : IsIntegral P a := Algebra.IsIntegral.isIntegral a
  set S := (minpoly P a).rootSet Ω
  have hS : ∀ j : ℕ, (σ ^ j) a ∈ S := fun j => by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
  haveI : Finite S := (Polynomial.rootSet_finite _ _).to_subtype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun j : ℕ => (⟨(σ ^ j) a, hS j⟩ : S))
  have heq' : (σ ^ i) a = (σ ^ j) a := congrArg Subtype.val heq
  have key : ∀ i j : ℕ, i < j → (σ ^ i) a = (σ ^ j) a → ∃ d : ℕ, (σ ^ (d + 1)) a = a := by
    intro i j hlt h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    refine ⟨d, (σ ^ i).injective ?_⟩
    rw [← AlgEquiv.mul_apply, ← pow_add, h]
    congr 2
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (σ ^ (d + 1)) a = a := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h heq'
    · exact key j i h heq'.symm
  refine ⟨d, ?_⟩
  rw [pow_succ', AlgEquiv.mul_apply] at hd
  calc (σ ^ d) a = σ.symm (σ ((σ ^ d) a)) := (σ.symm_apply_apply _).symm
    _ = σ⁻¹ a := by rw [hd]; rfl

end CuspInertia

section Generic

open CuspInertia SemistableReduction

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  {V : ValuationSubring Ω} (hV : V.comap (algebraMap K Ω) = O)

variable (R) in
/-- **The inertia group of a place `W`** in `Aut_R(Ω)`: the `σ` with `σ(W) = W` acting trivially
on the residue field of `W` (both `σ` and `σ⁻¹` in `inertiaSet R W`). -/
def inertiaGroup (W : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[R] Ω) where
  carrier := {σ | σ ∈ inertiaSet R W ∧ σ⁻¹ ∈ inertiaSet R W}
  mul_mem' := fun {σ τ} hσ hτ => ⟨mul_mem_inertia hσ.1 hτ.1, by
    rw [mul_inv_rev]; exact mul_mem_inertia hτ.2 hσ.2⟩
  one_mem' := ⟨one_mem_inertia, by rw [inv_one]; exact one_mem_inertia⟩
  inv_mem' := fun {σ} hσ => ⟨hσ.2, by rw [inv_inv]; exact hσ.1⟩

theorem mem_inertiaGroup {W : ValuationSubring Ω} {σ : Ω ≃ₐ[R] Ω} :
    σ ∈ inertiaGroup R W ↔ σ ∈ inertiaSet R W ∧ σ⁻¹ ∈ inertiaSet R W := Iff.rfl

/-- Inertia elements of `W` preserve every valuation subring `V ≤ W`. -/
theorem mem_of_mem_inertia_of_le {W : ValuationSubring Ω} (hVW : V ≤ W) {σ : Ω ≃ₐ[R] Ω}
    (hσ : σ ∈ inertiaSet R W) {x : Ω} (hx : x ∈ V) : σ x ∈ V := by
  have hd : V.valuation (σ x - x) < 1 :=
    CompositeValuation.valuation_lt_one_of_le hVW (hσ x (hVW hx))
  have h : σ x = (σ x - x) + x := by ring
  rw [h]
  exact V.add_mem _ _ ((V.valuation_le_one_iff _).1 hd.le) hx

/-- **Inertia lies in the decomposition group of every base point `V ≤ W`.** -/
theorem inertiaGroup_le_decompositionGroup {W : ValuationSubring Ω} (hVW : V ≤ W) :
    inertiaGroup R W ≤ decompositionGroup R V := by
  intro σ hσ x
  rw [mem_inertiaGroup] at hσ
  refine ⟨fun hx => ?_, mem_of_mem_inertia_of_le hVW hσ.1⟩
  have := mem_of_mem_inertia_of_le hVW hσ.2 hx
  rwa [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at this

variable (O A) in
/-- **The inertia group of `W` in the tempered fundamental group** (base point `V ≤ W`):
`σ ↦ galoisToTempered σ`. -/
def inertiaToTempered {W : ValuationSubring Ω} (hVW : V ≤ W) :
    inertiaGroup R W →* temperedPi1 O R A V hV :=
  (galoisToTempered O R A hV).comp
    (Subgroup.inclusion (inertiaGroup_le_decompositionGroup hVW))

variable (O A) in
/-- **`I^tp_W ≤ Π^tp`**: the image of the inertia group of `W`. -/
def inertiaTempered {W : ValuationSubring Ω} (hVW : V ≤ W) : Subgroup (temperedPi1 O R A V hV) :=
  (inertiaToTempered O A hV hVW).range

theorem inertiaToTempered_apply {W : ValuationSubring Ω} (hVW : V ≤ W) (σ : inertiaGroup R W) :
    inertiaToTempered O A hV hVW σ =
      galoisToTempered O R A hV ⟨σ, inertiaGroup_le_decompositionGroup hVW σ.2⟩ := rfl

theorem inertiaToTempered_mem {W : ValuationSubring Ω} (hVW : V ≤ W) (σ : inertiaGroup R W) :
    inertiaToTempered O A hV hVW σ ∈ inertiaTempered O A hV hVW :=
  ⟨σ, rfl⟩

/-- `I^tp_W` maps to the Galois action of `I_W` on `π₁ᵉᵗ`. -/
theorem temperedToEtale_inertiaToTempered [SMulCommClass A K R] {W : ValuationSubring Ω}
    (hVW : V ≤ W) (σ : inertiaGroup R W) :
    temperedToEtale O R A V hV (inertiaToTempered O A hV hVW σ) =
      galoisToEtale R A Ω (σ : Ω ≃ₐ[R] Ω) :=
  temperedToEtale_galoisToTempered hV _

/-! ### Base points inside a place -/

/-- **A base point inside a place**: for a place `W ⊇ K` and a valuation subring `O ⊆ K` there is
a valuation subring `V ≤ W` of `Ω` with `V ∩ K = O` (a composite of `W` with a valuation of its
residue field over `O`, `CompositeValuation.exists_le_dominates`). -/
theorem exists_le_comap_eq (W : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ W)
    (O : ValuationSubring K) :
    ∃ V : ValuationSubring Ω, V ≤ W ∧ V.comap (algebraMap K Ω) = O := by
  obtain ⟨R, hRW, hOR, hm⟩ := CompositeValuation.exists_le_dominates W
    ((algebraMap K Ω).comp O.subtype) (fun a => hk a)
  refine ⟨R, hRW, ?_⟩
  ext c
  rw [ValuationSubring.mem_comap]
  refine ⟨fun hc => ?_, fun hc => hOR ⟨c, hc⟩⟩
  by_contra hcO
  have hc0 : c ≠ 0 := by rintro rfl; exact hcO O.zero_mem
  have hinv : c⁻¹ ∈ O := (O.mem_or_inv_mem c).resolve_left hcO
  have hlt : O.valuation c⁻¹ < 1 := by
    rw [CentreGerms.valuation_lt_one_iff_inv, inv_inv]
    exact .inr hcO
  have h1 := hm ⟨c⁻¹, hinv⟩ ((O.valuation_lt_one_iff _).2 hlt)
  rw [CentreGerms.valuation_lt_one_iff_inv] at h1
  rcases h1 with h | h
  · exact inv_ne_zero hc0 ((algebraMap K Ω).injective (by simpa using h))
  · apply h
    simpa [map_inv₀] using hc

end Generic

/-! ### Change of level -/

section Naturality

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] (μ : OrbMap R A R' A')
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  {V : ValuationSubring Ω} (hV : V.comap (algebraMap K Ω) = O)

/-- An `R'`-automorphism of `Ω` preserving `V` is an `R`-automorphism preserving `V`. -/
def decompRestrict (σ : decompositionGroup R' V) : decompositionGroup R V :=
  ⟨(σ : Ω ≃ₐ[R'] Ω).restrictScalars R, fun x => σ.2 x⟩

@[simp]
theorem decompRestrict_apply (σ : decompositionGroup R' V) (x : Ω) :
    ((decompRestrict σ : decompositionGroup R V) : Ω ≃ₐ[R] Ω) x = (σ : Ω ≃ₐ[R'] Ω) x := rfl

/-- **`galoisToTempered` is natural** in maps of orbifolds: the image of the Galois element of
`σ` in `Π^tp([Spec R'/A'])` is the Galois element of `σ` in `Π^tp([Spec R/A])`. -/
theorem temperedPi1Map_galoisToTempered (σ : decompositionGroup R' V) :
    temperedPi1Map μ V hV (galoisToTempered O R' A' hV σ) =
      galoisToTempered O R A hV (decompRestrict σ) := by
  apply FibreAut.ext
  intro X x
  induction x using Quotient.inductionOn with
  | h q =>
    rw [temperedPi1Map_app]
    change TempObj.bcFibreEquiv μ V hV X
        ((galoisToTempered O R' A' hV σ).app (X.baseChange μ)
          (Quotient.mk _ (TempObj.bcPreExt μ V hV X q))) = _
    rw [galoisToTempered_app_mk, galoisToTempered_app_mk]
    change Quotient.mk'' (TempObj.bcPreRes μ V hV X _) = Quotient.mk'' _
    congr 1
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    ext y
    change (σ : Ω ≃ₐ[R'] Ω) (X.Lv.L.bcExt μ q.1.1 (X.Lv.L.bcι μ y)) = (σ : Ω ≃ₐ[R'] Ω) (q.1.1 y)
    rw [← FiniteLevel.bcRes_apply, FiniteLevel.bcRes_bcExt]

/-- An inertia element over `R'` is an inertia element over `R`. -/
def inertiaRestrict {W : ValuationSubring Ω} (σ : inertiaGroup R' W) : inertiaGroup R W :=
  ⟨(σ : Ω ≃ₐ[R'] Ω).restrictScalars R, fun a ha => (mem_inertiaGroup.1 σ.2).1 a ha,
    fun a ha => (mem_inertiaGroup.1 σ.2).2 a ha⟩

@[simp]
theorem inertiaRestrict_apply {W : ValuationSubring Ω} (σ : inertiaGroup R' W) (x : Ω) :
    ((inertiaRestrict σ : inertiaGroup R W) : Ω ≃ₐ[R] Ω) x = (σ : Ω ≃ₐ[R'] Ω) x := rfl

/-- **Cusp inertia is compatible with a change of level**: `Π^tp([Spec R'/A']) → Π^tp([Spec R/A])`
maps the inertia element `σ` of `W` over `R'` to `σ` over `R`. -/
theorem temperedPi1Map_inertiaToTempered {W : ValuationSubring Ω} (hVW : V ≤ W)
    (σ : inertiaGroup R' W) :
    temperedPi1Map μ V hV (inertiaToTempered O A' hV hVW σ) =
      inertiaToTempered O A hV hVW (inertiaRestrict σ) := by
  rw [inertiaToTempered_apply, temperedPi1Map_galoisToTempered]
  rfl

/-- The image of `I^tp_W` of the level `R'` lies in `I^tp_W` of `R`. -/
theorem map_inertiaTempered_le {W : ValuationSubring Ω} (hVW : V ≤ W) :
    (inertiaTempered O A' hV hVW).map (temperedPi1Map μ V hV) ≤ inertiaTempered O A hV hVW := by
  rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
  exact ⟨inertiaRestrict σ, (temperedPi1Map_inertiaToTempered μ hV hVW σ).symm⟩

end Naturality

/-! ### Curves in the Galois model: the image in `Π_U` and Kummer classes -/

namespace Kummer

open groupCohomology AffOrbicurve KummerTheory KummerTheory.Curve CuspInertia

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω]
  (O : ValuationSubring k) {V W : ValuationSubring Ω} (hV : V.comap (algebraMap k Ω) = O)
  (hVW : V ≤ W)

omit [CharZero k] in
variable {D} in
theorem galoisToH_pow_apply (σ : Ω ≃ₐ[D.R] Ω) (m : ℕ) (x : Ω) :
    (((galoisToH σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) ^ m) x = (σ ^ m) x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]; rfl

omit [CharZero k] in
variable {D} in
/-- For `Ω` algebraic over `k(t)`, `σ ∈ I_W` iff `σ` acts trivially on the residue field. -/
theorem mem_inertiaGroup_iff {σ : Ω ≃ₐ[D.R] Ω} :
    σ ∈ inertiaGroup D.R W ↔ σ ∈ inertiaSet D.R W := by
  refine ⟨fun h => (mem_inertiaGroup.1 h).1, fun h => mem_inertiaGroup.2 ⟨h, fun a ha => ?_⟩⟩
  haveI : Algebra.IsIntegral (K₀ k t) Ω := inferInstance
  obtain ⟨m, hm⟩ := exists_pow_apply_eq_inv_apply
    ((galoisToH σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) a
  rw [galoisToH_pow_apply] at hm
  have hinv : (σ⁻¹ : Ω ≃ₐ[D.R] Ω) a =
      (((galoisToH σ : D.H) : Ω ≃ₐ[K₀ k t] Ω))⁻¹ a := rfl
  rw [hinv, ← hm]
  exact pow_mem_inertia h m a ha

omit [CharZero k] in
variable {D} in
/-- The inertia set of `W` only depends on the underlying maps: `σ ∈ I_W` iff `σ ∈ H` is. -/
theorem galoisToH_mem_inertia_iff {σ : Ω ≃ₐ[D.R] Ω} :
    ((galoisToH σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W ↔
      σ ∈ inertiaSet D.R W := Iff.rfl

omit [CharZero k] in
variable {D} in
/-- An element of `H_L` as an `R`-automorphism of `Ω`. -/
def ofHL (h : Ω ≃ₐ[K₀ k t] Ω) (hh : h ∈ D.HL) : Ω ≃ₐ[D.R] Ω :=
  AlgEquiv.ofRingEquiv (f := h.toRingEquiv) fun r =>
    (IntermediateField.mem_fixedField_iff _ _).1 (CoordRing.algebraMap_mem r) _ hh

omit [CharZero k] in
variable {D} in
theorem galoisToH_ofHL (h : D.H) (hh : (h : Ω ≃ₐ[K₀ k t] Ω) ∈ D.HL) :
    galoisToH (ofHL (h : Ω ≃ₐ[K₀ k t] Ω) hh) = h :=
  Subtype.ext (AlgEquiv.ext fun _ => rfl)

/-- **`tempToPi` on `I^tp_W`**: the inertia element `σ` maps to `σ ∈ H`. -/
theorem tempToPi_inertiaToTempered (σ : inertiaGroup D.R W) :
    tempToPi D O V hV (inertiaToTempered O D.A hV hVW σ) =
      ((galoisToH (σ : Ω ≃ₐ[D.R] Ω) : D.H) : Pi D) :=
  tempToPi_galoisToTempered D O V hV _

/-- **The image of `I^tp_W` in `Π_U`** is the image of `I_W ∩ H_L` (the inertia elements of `H`
fixing the function field `L` of `U`). -/
theorem tempToPi_inertiaTempered :
    (tempToPi D O V hV : TempPi D O V hV → Pi D) ''
        (inertiaTempered (R := D.R) O D.A hV hVW : Set (TempPi D O V hV)) =
      {g | ∃ h : D.H, (h : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W ∧
        (h : Ω ≃ₐ[K₀ k t] Ω) ∈ D.HL ∧ (h : Pi D) = g} := by
  ext g
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨galoisToH (σ : Ω ≃ₐ[D.R] Ω), (mem_inertiaGroup.1 σ.2).1, galoisToH_mem_HL _,
      (tempToPi_inertiaToTempered D O hV hVW σ).symm⟩
  · rintro ⟨h, hW, hL, rfl⟩
    have hσ : ofHL (h : Ω ≃ₐ[K₀ k t] Ω) hL ∈ inertiaGroup D.R W :=
      mem_inertiaGroup_iff.2 hW
    refine ⟨_, ⟨⟨_, hσ⟩, rfl⟩, ?_⟩
    rw [tempToPi_inertiaToTempered]
    exact congrArg _ (galoisToH_ofHL h hL)

variable {D} in
/-- `I_W` acts trivially on `μ_n` (`W ⊇ k`), through `H`. -/
theorem galoisToH_inertia_smul_mu (hk : ∀ c : k, algebraMap k Ω c ∈ W) (σ : inertiaGroup D.R W)
    (n : ℕ) [NeZero n] (ζ : Mu n Ω) : (galoisToH (σ : Ω ≃ₐ[D.R] Ω) : Pi D) • ζ = ζ :=
  pi_inertia_smul_mu hk (galoisToH_mem_inertia_iff.2 (mem_inertiaGroup.1 σ.2).1) n ζ

/-- `I^tp_W` acts trivially on `μ_n` (`W ⊇ k`). -/
theorem inertiaToTempered_smul_mu (hk : ∀ c : k, algebraMap k Ω c ∈ W) (σ : inertiaGroup D.R W)
    (n : ℕ) [NeZero n] (ζ : Mu n Ω) : inertiaToTempered O D.A hV hVW σ • ζ = ζ := by
  change tempToPi D O V hV (inertiaToTempered O D.A hV hVW σ) • ζ = ζ
  rw [tempToPi_inertiaToTempered]
  exact galoisToH_inertia_smul_mu hk σ n ζ

variable [IsSepClosed Ω]

/-- **The tempered Kummer class on `I^tp_W`**: evaluating `κ^tp_n(u)` at the tempered inertia
element of `σ ∈ I_W` is evaluating the étale Kummer class `κ_n(u)` at `σ ∈ I_W ∩ H`. -/
theorem evalTriv_kummerMapTempered_inertia (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (σ : inertiaGroup D.R W) (n : ℕ) [NeZero n] (u : units D) :
    ContH1.evalTriv (inertiaToTempered O D.A hV hVW σ)
        (inertiaToTempered_smul_mu D O hV hVW hk σ n) (kummerMapTempered D O V hV n u) =
      ContH1.evalTriv ((galoisToH (σ : Ω ≃ₐ[D.R] Ω) : D.H) : Pi D)
        (galoisToH_inertia_smul_mu hk σ n) (kummerMap D n u) := by
  rw [kummerMapTempered, MonoidHom.comp_apply]
  induction kummerMap D n u using ContH1.induction_on with
  | h c =>
    rw [ContH1.map_mk, ContH1.evalTriv_mk, ContH1.evalTriv_mk, ContH1.cocyclesMap_apply,
      MonoidHom.id_apply, tempToPi_inertiaToTempered]

end Kummer

end

end TemperedFundamentalGroups
