/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Datum
import TemperedFundamentalGroups.SemistableReduction.AlgStrRingHom01
import TemperedFundamentalGroups.SemistableReduction.TwoChartMapOfCharts

/-!
# Maps of covers from maps of their normalisations over `T1` (generic; MR12 I3)

For covers `C`, `C'` (`TateS6.CovData` over two-chart rings `D` with `D.R1` a domain and `K` its
fraction field) and a ring map `g : C.B₁ → C'.B₁` of the normalisations of `D.R1` that is the
identity on `D.R1`:

* `TateS6.CovData.injective_of_map1`: `g` is injective (its kernel contracts to `0` in `D.R1`
  and `C.B₁` is integral over `D.R1`);
* **`TateS6.CovData.ofMap1`**: the `K`-algebra map `C.L → C'.L` extending `g` (`C.L` is the
  fraction field of `C.B₁`);
* **`TateS6.CovData.map1_ofMap1`**: `map1 (ofMap1 g) = g`;
* **`TateS6.CovData.ofHom`**: the map of covers induced by a morphism of chart algebras
  `Φ : C.P → C'.P` of the normalisations which is the identity on `D.R1`, with
  **`map1_ofHom`**, **`map0_ofHom`**: its maps of normalisations are the components of `Φ`.

This is the step "chart algebra map of the normalisations → map of covers" of I3 surjectivity.
-/

universe u

namespace SemistableReduction

namespace TateS6

noncomputable section

namespace CovData

variable {A : Type u} [CommRing A] {K : Type u} [Field K] {D : ProjectiveLine.TwoChartRings A}
  {Rn Rc : Type u} [CommRing Rn] [CommRing Rc] [Algebra D.R1 K] [Algebra Rn K] [Algebra Rc K]
  [Algebra D.R0 Rc] {toN : D.R1 → Rn} {dT : D.R1} {c0 : D.R0} {ϖ1 : D.R1} {ϖ0 : D.R0}
  {I0 : Ideal D.R0} {q e : ℕ} {C C' : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e}
  [IsDomain D.R1] [IsFractionRing D.R1 K]

variable (g : C.B₁ →+* C'.B₁)
  (hg : ∀ a, g (algebraMap D.R1 C.B₁ a) = algebraMap D.R1 C'.B₁ a)

include hg in
/-- A map of normalisations over `D.R1` is injective. -/
lemma injective_of_map1 : Function.Injective g := by
  haveI : Algebra.IsIntegral D.R1 C.B₁ := IsIntegralClosure.isIntegral_algebra D.R1 C.L
  haveI : IsDomain C.B₁ := (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _
  rw [injective_iff_map_eq_zero]
  intro b hb
  have hk : RingHom.ker g = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := D.R1) ?_
    refine eq_bot_iff.2 fun a ha ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hg] at ha
    have h1 : algebraMap D.R1 C'.L a = 0 := by
      rw [IsScalarTower.algebraMap_apply D.R1 C'.B₁ C'.L, ha, map_zero]
    rw [IsScalarTower.algebraMap_apply D.R1 K C'.L] at h1
    have h2 := (FaithfulSMul.algebraMap_injective K C'.L) (h1.trans (map_zero _).symm)
    exact (Submodule.mem_bot _).2 ((IsFractionRing.injective D.R1 K) (h2.trans (map_zero _).symm))
  rw [← RingHom.mem_ker, hk] at hb
  exact hb

/-- `C.L` is the fraction field of `C.B₁`. -/
lemma isFractionRing_B₁ : IsFractionRing C.B₁ C.L := by
  haveI : Algebra.IsAlgebraic K C.L := Algebra.IsAlgebraic.of_finite K C.L
  haveI : IsDomain C.B₁ := (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _
  exact IsIntegralClosure.isFractionRing_of_finite_extension D.R1 K C.L C.B₁

/-- **The map of covers extending a map of normalisations over `D.R1`.** -/
def ofMap1 : C.L →ₐ[K] C'.L :=
  haveI := isFractionRing_B₁ (C := C)
  haveI : Algebra.IsIntegral D.R1 C.B₁ := IsIntegralClosure.isIntegral_algebra D.R1 C.L
  haveI : IsDomain C.B₁ := (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _
  { IsFractionRing.lift (K := C.L) (g := (algebraMap C'.B₁ C'.L).comp g)
      ((IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L).comp
        (injective_of_map1 g hg)) with
    commutes' := fun k ↦ by
      have h : ((IsFractionRing.lift (K := C.L) (g := (algebraMap C'.B₁ C'.L).comp g)
          ((IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L).comp
            (injective_of_map1 g hg))).comp (algebraMap K C.L)) = algebraMap K C'.L := by
        refine IsLocalization.ringHom_ext (nonZeroDivisors D.R1) (RingHom.ext fun a ↦ ?_)
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply D.R1 K C.L,
          IsScalarTower.algebraMap_apply D.R1 C.B₁ C.L, IsFractionRing.lift_algebraMap,
          RingHom.comp_apply, hg, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      exact RingHom.congr_fun h k }

include hg in
lemma ofMap1_algebraMap (b : C.B₁) :
    ofMap1 g hg (algebraMap C.B₁ C.L b) = algebraMap C'.B₁ C'.L (g b) := by
  haveI := isFractionRing_B₁ (C := C)
  haveI : Algebra.IsIntegral D.R1 C.B₁ := IsIntegralClosure.isIntegral_algebra D.R1 C.L
  haveI : IsDomain C.B₁ := (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _
  exact IsFractionRing.lift_algebraMap (K := C.L) (g := (algebraMap C'.B₁ C'.L).comp g)
    ((IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L).comp
    (injective_of_map1 g hg)) b

include hg in
/-- **`map1` of the extension is the given map.** -/
lemma map1_ofMap1 (b : C.B₁) : map1 (ofMap1 g hg) b = g b :=
  IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L (by
    rw [algebraMap_map1, ofMap1_algebraMap])

/-! ### Maps of covers from morphisms of chart algebras of the normalisations -/

variable (Φ : ProjectiveLine.ChartModule.Hom C.P.chartModule C'.P.chartModule)
  (hΦ : C.P.algStr.IsHom C'.P.algStr Φ)
  (hΦ1 : ∀ a, Φ.f1 (algebraMap D.R1 C.B₁ a) = algebraMap D.R1 C'.B₁ a)

/-- The ring map `C.B₁ → C'.B₁` of a morphism of chart algebras `C.P → C'.P`. -/
def ring1OfHom : C.B₁ →+* C'.B₁ :=
  C'.P.ring1Equiv.toRingHom.comp (hΦ.ringHom1.comp C.P.ring1Equiv.symm.toRingHom)

omit [IsDomain D.R1] [IsFractionRing D.R1 K] in
lemma ring1OfHom_apply (b : C.B₁) : ring1OfHom Φ hΦ b = Φ.f1 b := rfl

/-- **The map of covers induced by a morphism of chart algebras of the normalisations** which
is the identity on `D.R1`. -/
def ofHom : C.L →ₐ[K] C'.L :=
  ofMap1 (ring1OfHom Φ hΦ) hΦ1

include hΦ1 in
/-- **`map1` of `ofHom Φ` is `Φ` on `B₁`.** -/
lemma map1_ofHom (b : C.B₁) : map1 (ofHom Φ hΦ hΦ1) b = Φ.f1 b :=
  map1_ofMap1 (ring1OfHom Φ hΦ) hΦ1 b

include hΦ1 in
/-- `Φ` on the overlap is `ofHom Φ` on the generic fibre. -/
lemma val_f01_ofHom (z : C.P.R01) :
    Subtype.val (p := (· ∈ integralClosure D.R01 C'.L)) (Φ.f01 z) =
      ofHom Φ hΦ hΦ1 (Subtype.val (p := (· ∈ integralClosure D.R01 C.L)) z) := by
  letI := C.P.ρ1.toRingHom.toAlgebra
  haveI := C.P.isLocalization_ρ1
  let g₁ : C.P.R01 →+* C'.L := (integralClosure D.R01 C'.L).val.toRingHom.comp
    (C'.P.ring01Equiv.toRingHom.comp (hΦ.ringHom01'.comp C.P.ring01Equiv.symm.toRingHom))
  let g₂ : C.P.R01 →+* C'.L :=
    (ofHom Φ hΦ hΦ1 : C.L →+* C'.L).comp (integralClosure D.R01 C.L).val.toRingHom
  have h : g₁ = g₂ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers C.P.y) (RingHom.ext fun b ↦ ?_)
    change Subtype.val (p := (· ∈ integralClosure D.R01 C'.L)) (Φ.f01 (C.P.ρ1 b)) =
      ofHom Φ hΦ hΦ1 (Subtype.val (p := (· ∈ integralClosure D.R01 C.L)) (C.P.ρ1 b))
    have e : Φ.f01 (C.P.ρ1 b) = C'.P.ρ1 (Φ.f1 b) := Φ.comm_r1 b
    rw [e]
    change algebraMap C'.B₁ C'.L (Φ.f1 b) = ofHom Φ hΦ hΦ1 (algebraMap C.B₁ C.L b)
    rw [← map1_ofHom Φ hΦ hΦ1, algebraMap_map1]
  exact RingHom.congr_fun h z

include hΦ1 in
/-- **`map0` of `ofHom Φ` is `Φ` on `B₀`.** -/
lemma map0_ofHom (b : C.B₀) : map0 (ofHom Φ hΦ hΦ1) b = Φ.f0 b := by
  refine IsIntegralClosure.algebraMap_injective C'.B₀ D.R0 C'.L ?_
  rw [algebraMap_map0]
  have e : Φ.f01 (C.P.ρ0 b) = C'.P.ρ0 (Φ.f0 b) := Φ.comm_r0 b
  have e2 := val_f01_ofHom Φ hΦ hΦ1 (C.P.ρ0 b)
  rw [e] at e2
  exact e2.symm

omit [IsDomain D.R1] in
/-- **Krull's intersection theorem on the normalisation of `D.R1`**: if `C.B₁` is Noetherian and
`a ∈ D.R1` lies in a prime of `D.R1`, then `⋂ₙ aⁿ⁺¹ C.B₁ = 0`. -/
theorem eq_zero_of_mem_span_pow (C : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e)
    [IsNoetherianRing C.B₁] (a : D.R1) (P : Ideal D.R1) [P.IsPrime] (ha : a ∈ P) (b : C.B₁)
    (hb : ∀ n, b ∈ Ideal.span {algebraMap D.R1 C.B₁ a} ^ (n + 1)) : b = 0 := by
  haveI : Algebra.IsIntegral D.R1 C.B₁ := IsIntegralClosure.isIntegral_algebra D.R1 C.L
  haveI : IsDomain C.B₁ := (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _
  have hinj : Function.Injective (algebraMap D.R1 C.B₁) := by
    intro a a' h
    have h' := congrArg (algebraMap C.B₁ C.L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply D.R1 K C.L, IsScalarTower.algebraMap_apply D.R1 K C.L] at h'
    exact (IsFractionRing.injective D.R1 K) ((FaithfulSMul.algebraMap_injective K C.L) h')
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := C.B₁) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  have hJ : Ideal.span {algebraMap D.R1 C.B₁ a} ≠ ⊤ := by
    intro hJ
    refine hQ.ne_top (eq_top_iff.2 (hJ ▸ ?_))
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have h1 : a ∈ Q.comap (algebraMap D.R1 C.B₁) := hQP.symm ▸ ha
    exact Ideal.mem_comap.1 h1
  refine (Submodule.mem_bot _).1 ((Ideal.iInf_pow_eq_bot_of_isDomain _ hJ).le
    ((Submodule.mem_iInf _).2 fun i ↦ ?_))
  cases i with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n => exact hb n

omit [IsDomain D.R1] in
/-- **Krull's intersection theorem on the second chart of `C.P`**: if `C.B₁` is Noetherian and
`ϖ ∈ A` lies in a prime of `D.R1`, then `⋂ₙ ϖⁿ⁺¹ C.B₁ = 0`. -/
theorem eq_zero_of_mem_pow (C : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e)
    [IsNoetherianRing C.B₁] (ϖ : A) (P : Ideal D.R1) [P.IsPrime]
    (hϖ : algebraMap A D.R1 ϖ ∈ P) (b : C.P.R1)
    (hb : ∀ n, b ∈ (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap A C.P.R1)) : b = 0 :=
  eq_zero_of_mem_span_pow C (algebraMap A D.R1 ϖ) P hϖ b fun n ↦ by
    have h := hb n
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h
    exact h

end CovData

end

end TateS6

end SemistableReduction
