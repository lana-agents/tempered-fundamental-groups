/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraOfRings
import FormalSchemes.ChartModuleAlgebra
import TemperedFundamentalGroups.SemistableReduction.TowerSystem

/-!
# Adic systems of chart algebras from towers of two-chart rings (Blueprint §12.8, M2.3 → M2.4)

The algebraization theorem of `formal-schemes` (`ProjectiveLine.AdicChartAlgSystem.
exists_algebraization`, Grothendieck existence for coherent algebras on `ℙ¹_A`) takes an adic
system of chart algebras. Here such a system is built from rings:

* `TwoChartMap D D'`: a morphism of two-chart rings (`ProjectiveLine.TwoChartRings`): `A`-algebra
  maps on the two charts and on the overlap, compatible with the chart coordinates and the
  restrictions; `TwoChartMap.toHom` the induced morphism of chart modules, and
  **`TwoChartMap.isHom`**: it is a morphism of chart algebras (`AlgStr.IsHom`);
* `TwoChartTower.trLe`: for a tower `D : ℕ → TwoChartRings A` with successor maps
  `s n : D (n+1) → D n`, the composite maps `D n → D m` (`m ≤ n`, `TowerSystem.trLe` on each
  component);
* **`TwoChartTower.system`**: if the successor maps are surjective on both charts with kernels
  `Iⁿ` (on `D (n+1)`), `Iⁿ` kills `D n`, and the charts are finite over `A[X]`, the tower is an
  adic system of chart algebras (`AdicChartAlgSystem I`) — the input of `exists_algebraization`;
* **`TwoChartTower.systemShift`**: the same for towers whose level `n` is killed by `Iⁿ⁺¹` (kernels
  `Iⁿ⁺¹`), shifted by the zero two-chart rings (`shift`, `zero`, `toZero`).
-/

universe u

open Polynomial

namespace SemistableReduction

open ProjectiveLine ProjectiveLine.ChartModule ProjectiveLine.BTensor

variable {A : Type u} [CommRing A]

/-- **A morphism of two-chart rings.** -/
structure TwoChartMap (D D' : TwoChartRings A) where
  /-- on `Spec A[X]` -/
  f0 : D.R0 →ₐ[A] D'.R0
  /-- on `Spec A[Y]` -/
  f1 : D.R1 →ₐ[A] D'.R1
  /-- on the overlap -/
  f01 : D.R01 →ₐ[A] D'.R01
  hx : f0 D.x = D'.x
  hy : f1 D.y = D'.y
  hu : f01 D.u = D'.u
  h0 : ∀ a, f01 (D.ρ0 a) = D'.ρ0 (f0 a)
  h1 : ∀ a, f01 (D.ρ1 a) = D'.ρ1 (f1 a)

namespace TwoChartMap

variable {D D' : TwoChartRings A} (φ : TwoChartMap D D')

/-- The induced morphism of chart modules. -/
noncomputable def toHom : ChartModule.Hom D.chartModule D'.chartModule where
  f0 := φ.f0.toLinearMap
  f1 := φ.f1.toLinearMap
  f01 := φ.f01.toLinearMap
  comm_x0 m := by
    change φ.f0 (D.x * m) = D'.x * φ.f0 m
    rw [map_mul, φ.hx]
  comm_x1 m := by
    change φ.f1 (D.y * m) = D'.y * φ.f1 m
    rw [map_mul, φ.hy]
  comm_t z := by
    change φ.f01 (D.u * z) = D'.u * φ.f01 z
    rw [map_mul, φ.hu]
  comm_r0 m := φ.h0 m
  comm_r1 m := φ.h1 m

lemma toHom_f0 (m : D.R0) : φ.toHom.f0 m = φ.f0 m := rfl

lemma toHom_f1 (m : D.R1) : φ.toHom.f1 m = φ.f1 m := rfl

lemma toHom_f01 (m : D.R01) : φ.toHom.f01 m = φ.f01 m := rfl

/-- **A morphism of two-chart rings is a morphism of chart algebras.** -/
theorem isHom : D.algStr.IsHom D'.algStr φ.toHom := by
  refine ⟨ChartModule.Hom.ext' ?_ ?_ ?_, Subtype.ext ?_⟩
  · refine LinearMap.ext fun w ↦ ?_
    induction w using BTensor.induction_on with
    | h0 => simp
    | htm a b =>
      change φ.f0 (TwoChartRings.bmul A D.x (tm _ _ a b)) =
        TwoChartRings.bmul A D'.x (tm _ _ (φ.f0 a) (φ.f0 b))
      simp
    | hadd x y hx hy => simp only [map_add, hx, hy]
  · refine LinearMap.ext fun w ↦ ?_
    induction w using BTensor.induction_on with
    | h0 => simp
    | htm a b =>
      change φ.f1 (TwoChartRings.bmul A D.y (tm _ _ a b)) =
        TwoChartRings.bmul A D'.y (tm _ _ (φ.f1 a) (φ.f1 b))
      simp
    | hadd x y hx hy => simp only [map_add, hx, hy]
  · refine LinearMap.ext fun w ↦ ?_
    induction w using BTensor.induction_on with
    | h0 => simp
    | htm a b =>
      change φ.f01 (TwoChartRings.bmul A (D.u : D.R01) (tm _ _ a b)) =
        TwoChartRings.bmul A (D'.u : D'.R01) (tm _ _ (φ.f01 a) (φ.f01 b))
      simp
    | hadd x y hx hy => simp only [map_add, hx, hy]
  · change ((φ.f0 1, φ.f1 1) : D'.R0 × D'.R1) = (1, 1)
    rw [map_one, map_one]

end TwoChartMap

namespace TwoChartTower

variable (D : ℕ → TwoChartRings A) (s : ∀ n, TwoChartMap (D (n + 1)) (D n))

/-- The transition map on `Spec A[X]`. -/
noncomputable def tr0 {m n : ℕ} (h : m ≤ n) : (D n).R0 →ₐ[A] (D m).R0 :=
  { TowerSystem.trLe (G := fun k ↦ (D k).R0) (fun k ↦ (s k).f0.toRingHom) h with
    commutes' := fun a ↦ RingHom.congr_fun (TowerSystem.trLe_comp_a
      (fun k ↦ algebraMap A (D k).R0) (fun k ↦ (s k).f0.comp_algebraMap) h) a }

/-- The transition map on `Spec A[Y]`. -/
noncomputable def tr1 {m n : ℕ} (h : m ≤ n) : (D n).R1 →ₐ[A] (D m).R1 :=
  { TowerSystem.trLe (G := fun k ↦ (D k).R1) (fun k ↦ (s k).f1.toRingHom) h with
    commutes' := fun a ↦ RingHom.congr_fun (TowerSystem.trLe_comp_a
      (fun k ↦ algebraMap A (D k).R1) (fun k ↦ (s k).f1.comp_algebraMap) h) a }

/-- The transition map on the overlap. -/
noncomputable def tr01 {m n : ℕ} (h : m ≤ n) : (D n).R01 →ₐ[A] (D m).R01 :=
  { TowerSystem.trLe (G := fun k ↦ (D k).R01) (fun k ↦ (s k).f01.toRingHom) h with
    commutes' := fun a ↦ RingHom.congr_fun (TowerSystem.trLe_comp_a
      (fun k ↦ algebraMap A (D k).R01) (fun k ↦ (s k).f01.comp_algebraMap) h) a }

lemma tr0_apply {m n : ℕ} (h : m ≤ n) (a : (D n).R0) :
    tr0 D s h a = TowerSystem.trLe (G := fun k ↦ (D k).R0) (fun k ↦ (s k).f0.toRingHom) h a :=
  rfl

lemma tr1_apply {m n : ℕ} (h : m ≤ n) (a : (D n).R1) :
    tr1 D s h a = TowerSystem.trLe (G := fun k ↦ (D k).R1) (fun k ↦ (s k).f1.toRingHom) h a :=
  rfl

lemma tr01_apply {m n : ℕ} (h : m ≤ n) (a : (D n).R01) :
    tr01 D s h a =
      TowerSystem.trLe (G := fun k ↦ (D k).R01) (fun k ↦ (s k).f01.toRingHom) h a :=
  rfl

/-- **The transition map** `D n → D m` of the tower. -/
noncomputable def trLe {m n : ℕ} (h : m ≤ n) : TwoChartMap (D n) (D m) where
  f0 := tr0 D s h
  f1 := tr1 D s h
  f01 := tr01 D s h
  hx := TowerSystem.trLe_apply_of (G := fun k ↦ (D k).R0) (x := fun k ↦ (D k).x)
    (fun k ↦ (s k).hx) h
  hy := TowerSystem.trLe_apply_of (G := fun k ↦ (D k).R1) (x := fun k ↦ (D k).y)
    (fun k ↦ (s k).hy) h
  hu := TowerSystem.trLe_apply_of (G := fun k ↦ (D k).R01)
    (x := fun k ↦ ((D k).u : (D k).R01)) (fun k ↦ (s k).hu) h
  h0 a := TowerSystem.trLe_comm (G := fun k ↦ (D k).R0) (H := fun k ↦ (D k).R01)
    (fun k ↦ (D k).ρ0.toRingHom) (fun k ↦ (s k).h0) h a
  h1 a := TowerSystem.trLe_comm (G := fun k ↦ (D k).R1) (H := fun k ↦ (D k).R01)
    (fun k ↦ (D k).ρ1.toRingHom) (fun k ↦ (s k).h1) h a

lemma trLe_comp {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) :
    (trLe D s h₁).toHom.comp (trLe D s h₂).toHom = (trLe D s (h₁.trans h₂)).toHom :=
  ChartModule.Hom.ext'
    (LinearMap.ext fun a ↦ TowerSystem.trLe_apply_trLe (G := fun k ↦ (D k).R0) _ h₁ h₂ a)
    (LinearMap.ext fun a ↦ TowerSystem.trLe_apply_trLe (G := fun k ↦ (D k).R1) _ h₁ h₂ a)
    (LinearMap.ext fun a ↦ TowerSystem.trLe_apply_trLe (G := fun k ↦ (D k).R01) _ h₁ h₂ a)

lemma trLe_refl (n : ℕ) : (trLe D s (le_refl n)).toHom = ChartModule.Hom.id _ :=
  ChartModule.Hom.ext'
    (LinearMap.ext fun a ↦ RingHom.congr_fun (TowerSystem.trLe_refl (G := fun k ↦ (D k).R0) _ n) a)
    (LinearMap.ext fun a ↦ RingHom.congr_fun (TowerSystem.trLe_refl (G := fun k ↦ (D k).R1) _ n) a)
    (LinearMap.ext fun a ↦
      RingHom.congr_fun (TowerSystem.trLe_refl (G := fun k ↦ (D k).R01) _ n) a)

variable {D s} (I : Ideal A)
  (hs0 : ∀ n, Function.Surjective (s n).f0) (hs1 : ∀ n, Function.Surjective (s n).f1)
  (hker0 : ∀ n, RingHom.ker (s n).f0 = (I ^ n).map (algebraMap A (D (n + 1)).R0))
  (hker1 : ∀ n, RingHom.ker (s n).f1 = (I ^ n).map (algebraMap A (D (n + 1)).R1))
  (hkill0 : ∀ n, (I ^ n).map (algebraMap A (D n).R0) = ⊥)
  (hkill1 : ∀ n, (I ^ n).map (algebraMap A (D n).R1) = ⊥)

include hs0 hker0 hkill0 in
lemma ker_tr0 {m n : ℕ} (h : m ≤ n) :
    RingHom.ker (tr0 D s h) = (I ^ m).map (algebraMap A (D n).R0) :=
  TowerSystem.ker_trLe (G := fun k ↦ (D k).R0) (fun k ↦ algebraMap A (D k).R0)
    (fun k ↦ (s k).f0.comp_algebraMap) hs0 (J := fun k ↦ I ^ k)
    (fun _ _ hab ↦ Ideal.pow_le_pow_right hab) hker0 hkill0 h

include hs1 hker1 hkill1 in
lemma ker_tr1 {m n : ℕ} (h : m ≤ n) :
    RingHom.ker (tr1 D s h) = (I ^ m).map (algebraMap A (D n).R1) :=
  TowerSystem.ker_trLe (G := fun k ↦ (D k).R1) (fun k ↦ algebraMap A (D k).R1)
    (fun k ↦ (s k).f1.comp_algebraMap) hs1 (J := fun k ↦ I ^ k)
    (fun _ _ hab ↦ Ideal.pow_le_pow_right hab) hker1 hkill1 h

/-- The kernel of an `A`-algebra map, as an `A`-submodule, is `J • ⊤` if it is the ideal
generated by `J`. -/
lemma ker_toLinearMap {R S : Type u} [CommRing R] [Algebra A R] [CommRing S] [Algebra A S]
    (f : R →ₐ[A] S) {J : Ideal A} (hf : RingHom.ker f = J.map (algebraMap A R)) :
    LinearMap.ker f.toLinearMap = J • (⊤ : Submodule A R) := by
  rw [Ideal.smul_top_eq_map, ← hf]
  rfl

/-- `J • ⊤ = ⊥` if `J` kills `R`. -/
lemma smul_top_eq_bot {R : Type u} [CommRing R] [Algebra A R] {J : Ideal A}
    (hJ : J.map (algebraMap A R) = ⊥) : J • (⊤ : Submodule A R) = ⊥ := by
  rw [Ideal.smul_top_eq_map, hJ]
  rfl

variable (D s)

/-- **A tower of two-chart rings is an adic system of chart algebras** on `ℙ¹_A`: successor maps
surjective on both charts with kernels `Iⁿ`, levels killed by `Iⁿ`, charts finite over
`A[X]`. -/
noncomputable def system
    (hfin0 : ∀ n, Module.Finite A[X] (Module.AEval' (D n).chartModule.x0))
    (hfin1 : ∀ n, Module.Finite A[X] (Module.AEval' (D n).chartModule.x1)) :
    AdicChartAlgSystem I where
  M n := (D n).chartModule
  tr h := (trLe D s h).toHom
  tr_comp h₁ h₂ := trLe_comp D s h₁ h₂
  surj0 h := TowerSystem.surjective_trLe (G := fun k ↦ (D k).R0) _ hs0 h
  surj1 h := TowerSystem.surjective_trLe (G := fun k ↦ (D k).R1) _ hs1 h
  ker0 h := ker_toLinearMap _ (ker_tr0 I hs0 hker0 hkill0 h)
  ker1 h := ker_toLinearMap _ (ker_tr1 I hs1 hker1 hkill1 h)
  tr_refl n := trLe_refl D s n
  kill0 n := smul_top_eq_bot (hkill0 n)
  kill1 n := smul_top_eq_bot (hkill1 n)
  fin0 := hfin0
  fin1 := hfin1
  alg n := (D n).algStr
  isHom_tr h := (trLe D s h).isHom


/-! ### Towers whose levels are killed by `Iⁿ⁺¹`

`AdicChartSystem` indexes level `n` by `Iⁿ` (so level `0` is zero). A tower `E` whose level `n` is
killed by `Iⁿ⁺¹` (e.g. the patched algebras modulo `ϖⁿ⁺¹`) is shifted by putting the zero
two-chart rings in front (`TwoChartTower.shift`). -/

/-- The zero two-chart rings. -/
noncomputable def zero (A : Type u) [CommRing A] : TwoChartRings A where
  R0 := PUnit
  R1 := PUnit
  R01 := PUnit
  x := 0
  y := 0
  u := 1
  ρ0 := AlgHom.id A PUnit
  ρ1 := AlgHom.id A PUnit
  ρ0_x := Subsingleton.elim _ _
  ρ1_y := Subsingleton.elim _ _
  exists0 _ := ⟨0, 0, Subsingleton.elim _ _⟩
  ker0 _ _ := ⟨0, Subsingleton.elim _ _⟩
  exists1 _ := ⟨0, 0, Subsingleton.elim _ _⟩
  ker1 _ _ := ⟨0, Subsingleton.elim _ _⟩

/-- The `A`-algebra map to the zero ring. -/
def toPUnit (R : Type u) [CommRing R] [Algebra A R] : R →ₐ[A] PUnit.{u + 1} where
  toFun _ := PUnit.unit
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The map to the zero two-chart rings. -/
noncomputable def toZero (D : TwoChartRings A) : TwoChartMap D (zero A) where
  f0 := toPUnit D.R0
  f1 := toPUnit D.R1
  f01 := toPUnit D.R01
  hx := @Subsingleton.elim PUnit _ _ _
  hy := @Subsingleton.elim PUnit _ _ _
  hu := @Subsingleton.elim PUnit _ _ _
  h0 _ := @Subsingleton.elim PUnit _ _ _
  h1 _ := @Subsingleton.elim PUnit _ _ _

variable (E : ℕ → TwoChartRings A) (e : ∀ n, TwoChartMap (E (n + 1)) (E n))

/-- The shifted tower: `0, E 0, E 1, …`. -/
noncomputable def shift : ℕ → TwoChartRings A
  | 0 => zero A
  | n + 1 => E n

/-- The successor maps of the shifted tower. -/
noncomputable def shiftMap : ∀ n, TwoChartMap (shift E (n + 1)) (shift E n)
  | 0 => toZero (E 0)
  | n + 1 => e n

lemma finite_aeval_of_subsingleton {M : Type u} [AddCommGroup M] [Module A M] [Subsingleton M]
    (φ : M →ₗ[A] M) : Module.Finite A[X] (Module.AEval' φ) := by
  haveI : Subsingleton (Module.AEval' φ) := (Module.AEval'.of φ).symm.injective.subsingleton
  exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩

lemma map_eq_bot_of_subsingleton {R : Type u} [CommRing R] [Algebra A R] [Subsingleton R]
    (J : Ideal A) : J.map (algebraMap A R) = ⊥ :=
  Subsingleton.elim _ _

/-- **A tower of two-chart rings with level `n` killed by `Iⁿ⁺¹` gives an adic system of chart
algebras** (level `n + 1` of the system is `E n`). -/
noncomputable def systemShift
    (he0 : ∀ n, Function.Surjective (e n).f0) (he1 : ∀ n, Function.Surjective (e n).f1)
    (hker0 : ∀ n, RingHom.ker (e n).f0 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R0))
    (hker1 : ∀ n, RingHom.ker (e n).f1 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R1))
    (hkill0 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R0) = ⊥)
    (hkill1 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R1) = ⊥)
    (hfin0 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x0))
    (hfin1 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x1)) :
    AdicChartAlgSystem I :=
  system (shift E) (shiftMap E e) I
    (fun n ↦ match n with
      | 0 => fun _ ↦ ⟨0, @Subsingleton.elim PUnit _ _ _⟩
      | n + 1 => he0 n)
    (fun n ↦ match n with
      | 0 => fun _ ↦ ⟨0, @Subsingleton.elim PUnit _ _ _⟩
      | n + 1 => he1 n)
    (fun n ↦ match n with
      | 0 => by
        rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
        exact eq_top_iff.mpr fun _ _ ↦ RingHom.mem_ker.mpr (@Subsingleton.elim PUnit _ _ _)
      | n + 1 => hker0 n)
    (fun n ↦ match n with
      | 0 => by
        rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
        exact eq_top_iff.mpr fun _ _ ↦ RingHom.mem_ker.mpr (@Subsingleton.elim PUnit _ _ _)
      | n + 1 => hker1 n)
    (fun n ↦ match n with
      | 0 => map_eq_bot_of_subsingleton (R := PUnit) _
      | n + 1 => hkill0 n)
    (fun n ↦ match n with
      | 0 => map_eq_bot_of_subsingleton (R := PUnit) _
      | n + 1 => hkill1 n)
    (fun n ↦ match n with
      | 0 => finite_aeval_of_subsingleton (M := PUnit) _
      | n + 1 => hfin0 n)
    (fun n ↦ match n with
      | 0 => finite_aeval_of_subsingleton (M := PUnit) _
      | n + 1 => hfin1 n)

end TwoChartTower

end SemistableReduction
