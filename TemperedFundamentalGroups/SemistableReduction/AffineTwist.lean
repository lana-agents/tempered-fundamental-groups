/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothVertex

/-!
# The affine twist `x ↦ (x - a) / c` and smooth points over arbitrary residue discs

Blueprint §9.9, S7(c) for the disc chart `DRint a c F'` of §9.10 L2 (`DiscCount`). For `c ≠ 0`
let `σ = aff a c` be the `C`-automorphism of `C(x)` with `σ(x) = t = (x - a) / c`, and `Aff a c F'`
the field `F'` with its `C(x)`-algebra structure twisted by `σ` (`x` acts as `t`).

* `aff_mem_discRing_iff`: `σ` maps the vertex chart `O_C[x]` onto the disc chart `O_C[t]`;
* `drintEquiv`: hence the integral closures `DRint a c F'` and `DRint 0 1 (Aff a c F')` coincide
  (as subsets of `F'`); `coe_drintEquiv`;
* `xF_aff`: the coordinate of the twist is `t`;
* **`exists_eq_of_uniformizer`**: S7(c) on `DRint a c F'` (transport of
  `SmoothVertex.exists_eq_of_uniformizer`): for an extension `v` of the Gauss point of the twist
  (i.e. of `w_{a,|c|}`), a zero `Q` of `t̄` on `κ(v)` whose point is not the point of another
  zero of `t̄`, and `t' ∈ R'` reducing to a uniformizer at `Q`, every `a ∈ O_Q` is `ρ y / ρ s`
  with `s ∉ P'`.
-/

open Polynomial WithZero
open scoped NNReal

namespace SemistableReduction

namespace AffineTwist

open GaussFibre DiscCount SmoothVertex PlaceNorm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

section Aut

variable {a c : C} (hc0 : c ≠ 0)

include hc0 in
lemma aeval_gaussCoord_injective :
    Function.Injective (aeval (gaussCoord a c) : C[X] →ₐ[C] RatFunc C) :=
  (injective_iff_map_eq_zero _).2 fun _ h ↦ (isGaussCoord_disc (a := a) hc0).aeval_eq_zero_iff.1 h

/-- The algebra endomorphism `x ↦ (x - a) / c` of `C(x)`. -/
noncomputable def affHom (a c : C) (hc0 : c ≠ 0) : RatFunc C →ₐ[C] RatFunc C :=
  RatFunc.liftAlgHom (aeval (gaussCoord a c))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_gaussCoord_injective hc0))

lemma affHom_algebraMap (p : C[X]) :
    affHom a c hc0 (algebraMap C[X] (RatFunc C) p) = aeval (gaussCoord a c) p := by
  have := RatFunc.liftAlgHom_apply_div (aeval (gaussCoord a c))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_gaussCoord_injective hc0)) p 1
  simpa [affHom] using this

lemma affHom_X : affHom a c hc0 RatFunc.X = gaussCoord a c := by
  simpa using affHom_algebraMap hc0 Polynomial.X

lemma affHom_comp {a' c' : C} (hc0' : c' ≠ 0)
    (hX : affHom a c hc0 (gaussCoord a' c') = RatFunc.X) (φ : RatFunc C) :
    affHom a c hc0 (affHom a' c' hc0' φ) = φ := by
  have hp (p : C[X]) : affHom a c hc0 (affHom a' c' hc0' (algebraMap C[X] (RatFunc C) p)) =
      algebraMap C[X] (RatFunc C) p := by
    rw [affHom_algebraMap, ← Polynomial.aeval_algHom_apply, hX, RatFunc.aeval_X_left_eq_algebraMap]
  rw [← RatFunc.num_div_denom φ, map_div₀, map_div₀, hp, hp]

lemma affHom_gaussCoord {a' c' : C} :
    affHom a c hc0 (gaussCoord a' c') =
      algebraMap C (RatFunc C) c'⁻¹ * (gaussCoord a c - algebraMap C (RatFunc C) a') := by
  rw [gaussCoord, affHom_algebraMap, gaussLin, map_mul, map_sub, aeval_C, aeval_C, aeval_X]

omit [IsUltrametricDist C] in
lemma gaussCoord_eq :
    gaussCoord a c = algebraMap C (RatFunc C) c⁻¹ * (RatFunc.X - algebraMap C (RatFunc C) a) := by
  rw [gaussCoord, gaussLin, map_mul, map_sub, ratFunc_algebraMap_C, ratFunc_algebraMap_C,
    RatFunc.algebraMap_X]

/-- `x ↦ c x + a` undoes `x ↦ (x - a) / c`. -/
lemma affHom_affHom (φ : RatFunc C) :
    affHom a c hc0 (affHom (-a / c) c⁻¹ (inv_ne_zero hc0) φ) = φ := by
  refine affHom_comp hc0 (inv_ne_zero hc0) ?_ φ
  rw [affHom_gaussCoord, gaussCoord_eq]
  have hc : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
  simp only [map_div₀, map_neg, map_inv₀, inv_inv]
  field_simp
  ring

lemma affHom_affHom' (φ : RatFunc C) :
    affHom (-a / c) c⁻¹ (inv_ne_zero hc0) (affHom a c hc0 φ) = φ := by
  refine affHom_comp (inv_ne_zero hc0) hc0 ?_ φ
  rw [affHom_gaussCoord, gaussCoord_eq]
  have hc : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
  simp only [map_div₀, map_neg, map_inv₀, inv_inv]
  field_simp
  ring

/-- The automorphism `x ↦ (x - a) / c` of `C(x)`. -/
noncomputable def aff (a c : C) (hc0 : c ≠ 0) : RatFunc C ≃ₐ[C] RatFunc C :=
  AlgEquiv.ofAlgHom (affHom a c hc0) (affHom (-a / c) c⁻¹ (inv_ne_zero hc0))
    (AlgHom.ext (affHom_affHom hc0)) (AlgHom.ext (affHom_affHom' hc0))

lemma aff_apply (φ : RatFunc C) : aff a c hc0 φ = affHom a c hc0 φ := rfl

/-- `σ` maps the vertex chart `O_C[x]` onto the disc chart `O_C[t]`. -/
lemma aff_mem_discRing_iff {f : RatFunc C} :
    aff a c hc0 f ∈ discRing a c ↔ f ∈ discRing (0 : C) 1 := by
  constructor
  · intro h
    obtain ⟨Q, hQ, hQf⟩ := mem_polyChart_iff.1 h
    refine mem_discRing_iff.2 ⟨Q, hQ, ?_⟩
    apply (aff a c hc0).injective
    rw [← hQf, aff_apply, affHom_algebraMap]
  · intro h
    obtain ⟨Q, hQ, rfl⟩ := mem_discRing_iff.1 h
    exact mem_polyChart_iff.2 ⟨Q, hQ, by rw [aff_apply, affHom_algebraMap]⟩

end Aut

/-! ### The twist -/

section Twist

/-- `F'` with its `C(x)`-algebra structure twisted by `x ↦ (x - a) / c`. -/
def Aff (_a c : C) (_hc0 : c ≠ 0) (F' : Type*) : Type _ := F'

variable {a c : C} (hc0 : c ≠ 0) {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

instance : Field (Aff a c hc0 F') := inferInstanceAs (Field F')

noncomputable instance : Algebra (RatFunc C) (Aff a c hc0 F') :=
  ((algebraMap (RatFunc C) F').comp (aff a c hc0).toRingHom).toAlgebra

/-- The identity `F' → Aff a c F'`. -/
noncomputable def toAff : F' ≃+* Aff a c hc0 F' := RingEquiv.refl F'

lemma algebraMap_aff_apply (φ : RatFunc C) :
    algebraMap (RatFunc C) (Aff a c hc0 F') φ =
      toAff hc0 (algebraMap (RatFunc C) F' (aff a c hc0 φ)) := rfl

section Instances

variable [Algebra C F'] [IsScalarTower C (RatFunc C) F']

instance : Algebra C (Aff a c hc0 F') := inferInstanceAs (Algebra C F')

instance : IsScalarTower C (RatFunc C) (Aff a c hc0 F') :=
  IsScalarTower.of_algebraMap_eq fun b ↦ by
    rw [algebraMap_aff_apply, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rfl

end Instances

lemma finrank_aff :
    Module.finrank (RatFunc C) (Aff a c hc0 F') = Module.finrank (RatFunc C) F' :=
  (Algebra.finrank_eq_of_equiv_equiv (aff a c hc0).symm.toRingEquiv (toAff hc0) (by
    ext φ
    change toAff hc0 (algebraMap (RatFunc C) F' (aff a c hc0 ((aff a c hc0).symm φ))) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl)).symm

instance [FiniteDimensional (RatFunc C) F'] : FiniteDimensional (RatFunc C) (Aff a c hc0 F') :=
  Module.finite_of_finrank_pos (by rw [finrank_aff]; exact Module.finrank_pos)

/-- The integral closures of the disc chart in `F'` and of the vertex chart in the twist
coincide. -/
lemma isIntegral_toAff_iff (y : F') :
    IsIntegral (discRing (0 : C) 1) (toAff hc0 y : Aff a c hc0 F') ↔
      IsIntegral (discRing a c) y := by
  let φ : discRing (0 : C) 1 →+* discRing a c :=
    { toFun := fun f ↦ ⟨aff a c hc0 f, (aff_mem_discRing_iff hc0).2 f.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun f g ↦ Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun f g ↦ Subtype.ext (map_add _ _ _) }
  let φ' : discRing a c →+* discRing (0 : C) 1 :=
    { toFun := fun g ↦ ⟨(aff a c hc0).symm g,
        (aff_mem_discRing_iff hc0).1 (by rw [AlgEquiv.apply_symm_apply]; exact g.2)⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun f g ↦ Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun f g ↦ Subtype.ext (map_add _ _ _) }
  constructor
  · intro h
    exact IsIntegral.map_of_comp_eq φ (toAff hc0).symm.toRingHom (by ext f; rfl) h
  · intro h
    refine IsIntegral.map_of_comp_eq φ' (toAff hc0).toRingHom (RingHom.ext fun g ↦ ?_) h
    change toAff hc0 (algebraMap (RatFunc C) F' (aff a c hc0 ((aff a c hc0).symm g))) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl

/-- The integral closures of the disc chart `O_C[t]` in `F'` and of the vertex chart `O_C[x]` in
the twist coincide. -/
noncomputable def drintEquiv : DRint a c F' ≃+* DRint (0 : C) 1 (Aff a c hc0 F') where
  toFun y := ⟨toAff hc0 y.1, (isIntegral_toAff_iff hc0 y.1).2 y.2⟩
  invFun y := ⟨(toAff hc0).symm y.1, (isIntegral_toAff_iff hc0 ((toAff hc0).symm y.1)).1
    (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := Subtype.ext <| by
    change toAff hc0 ((x : F') * (y : F')) = toAff hc0 (x : F') * toAff hc0 (y : F')
    exact map_mul (toAff hc0) _ _
  map_add' x y := Subtype.ext <| by
    change toAff hc0 ((x : F') + (y : F')) = toAff hc0 (x : F') + toAff hc0 (y : F')
    exact map_add (toAff hc0) _ _

lemma coe_drintEquiv (y : DRint a c F') :
    ((drintEquiv hc0 y : DRint (0 : C) 1 (Aff a c hc0 F')) : Aff a c hc0 F') =
      toAff hc0 (y : F') := rfl

/-- The coordinate of the twist is `t = (x - a) / c`. -/
lemma xF_aff [Algebra C F'] [IsScalarTower C (RatFunc C) F'] :
    GaussFibre.xF C (Aff a c hc0 F') =
      toAff hc0 (algebraMap (RatFunc C) F' (gaussCoord a c)) := by
  change toAff hc0 (algebraMap (RatFunc C) F' (aff a c hc0 RatFunc.X)) = _
  rw [aff_apply, affHom_X]

end Twist

/-! ### Extensions of `w_{a,|c|}` -/

section Ext

variable [IsAlgClosed C] {a c : C} (hc0 : c ≠ 0) {F' : Type*} [Field F']
  [Algebra (RatFunc C) F']

/-- `w_{0,1} ∘ σ⁻¹ = w_{a,|c|}`. -/
lemma gauss1_aff_symm (φ : RatFunc C) :
    gauss1 C ((aff a c hc0).symm φ) =
      gaussRat (NormedField.valuation (K := C)) a (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0)) φ :=
  by
  set w₁ := (gauss1 C).comap (aff a c hc0).symm.toRingEquiv.toRingHom
  change w₁ φ = _
  congr 1
  refine valuation_ratFunc_ext_of_linear (fun b ↦ ?_) fun b ↦ ?_
  · change gauss1 C ((aff a c hc0).symm (algebraMap C (RatFunc C) b)) = _
    rw [AlgEquiv.commutes, gauss1_algebraMap_C, gaussRat_algebraMap_C, NormedField.valuation_apply]
  · change gauss1 C ((aff a c hc0).symm (algebraMap C[X] (RatFunc C) (X - Polynomial.C b))) = _
    have hsymm : (aff a c hc0).symm (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) =
        algebraMap C[X] (RatFunc C) (Polynomial.C c * X + Polynomial.C (a - b)) := by
      apply (aff a c hc0).injective
      rw [AlgEquiv.apply_symm_apply, aff_apply, affHom_algebraMap, map_add, map_mul, aeval_C,
        aeval_X, aeval_C, gaussCoord_eq, map_sub, map_sub, ratFunc_algebraMap_C,
        RatFunc.algebraMap_X]
      have hc : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
      rw [map_inv₀]
      field_simp
      ring
    rw [hsymm, gauss1_algebraMap, gaussRat_algebraMap, gauss_X_sub_C]
    apply le_antisymm
    · refine Gauss.sup_le_iff.2 fun i ↦ ?_
      simp only [Gauss.term, coeff_add, coeff_C_mul, coeff_X, coeff_C, Units.val_one, one_pow,
        mul_one, NormedField.valuation_apply, Units.val_mk0]
      rcases i with _ | _ | i
      · simp
      · simp
      · simp
    · refine max_le ?_ ?_
      · have := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1)
          (Polynomial.C c * X + Polynomial.C (a - b)) 0
        simpa [Gauss.term] using this
      · have := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1)
          (Polynomial.C c * X + Polynomial.C (a - b)) 1
        simpa [Gauss.term] using this

lemma gaussRat_aff (φ : RatFunc C) :
    gaussRat (NormedField.valuation (K := C)) a (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0))
      (aff a c hc0 φ) = gauss1 C φ := by
  rw [← gauss1_aff_symm hc0, AlgEquiv.symm_apply_apply]

/-- Extensions of `w_{a,|c|}` to `F'` are the extensions of `w_{0,1}` to the twist. -/
noncomputable def extAff :
    GaussStability.GaussExtension a (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0)) F' ≃
      Ext C (Aff a c hc0 F') where
  toFun v := ⟨v.1.comap (toAff hc0).symm.toRingHom, Valuation.ext fun φ ↦ by
    rw [Valuation.comap_apply, Valuation.comap_apply, algebraMap_aff_apply]
    change v.1 ((toAff hc0).symm (toAff hc0 (algebraMap (RatFunc C) F' (aff a c hc0 φ)))) = _
    rw [RingEquiv.symm_apply_apply, ← Valuation.comap_apply, v.2, gaussRat_aff]⟩
  invFun v := ⟨v.1.comap (toAff hc0).toRingHom, Valuation.ext fun φ ↦ by
    rw [Valuation.comap_apply, Valuation.comap_apply]
    have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u ((aff a c hc0).symm φ)) v.2
    simp only [Valuation.comap_apply, algebraMap_aff_apply, AlgEquiv.apply_symm_apply] at this
    change v.1 (toAff hc0 (algebraMap (RatFunc C) F' φ)) = _
    rw [this, gauss1_aff_symm]⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Ext

/-! ### S7(c) on the disc chart `DRint a c F'` -/

section Smooth


variable [IsAlgClosed C] {a c : C} (hc0 : c ≠ 0) {F' : Type*} [Field F']
  [Algebra (RatFunc C) F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **S7(c) on the disc chart** `R' = DRint a c F'` (integral closure of `O_C[t]`,
`t = (x - a) / c`). Let `v` be an extension of `w_{a,|c|}` (seen on the twist, `extAff`), `Q` a
zero of `t̄` on `κ(v)` whose point `P'` (`placeIdealD`, pulled back along `drintEquiv`) is not the
point of any other zero of `t̄`, and `t' ∈ R'` reducing to a uniformizer at `Q`. Then every
`α ∈ O_Q` is `ρ y / ρ s` with `y, s ∈ R'`, `s ∉ P'`: the local ring of the reduction at `P'` is
`O_Q` (`δ = 0` on the branch). -/
theorem exists_eq_of_uniformizer (v : Ext C (Aff a c hc0 F'))
    {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Aff a c hc0 F')) v))
    (hoth : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C (Aff a c hc0 F')) v)), R ≠ Q →
      placeIdealD v hR ≠ placeIdealD v hQ)
    {t' : DRint a c F'} (ht : Q.valuation (redD v (drintEquiv hc0 t')) = exp (-1))
    {α : IsLocalRing.ResidueField v.1.valuationSubring} (hα : α ∈ Q.V) :
    ∃ y s : DRint a c F', drintEquiv hc0 s ∉ placeIdealD v hQ ∧
      redD v (drintEquiv hc0 y) = α * redD v (drintEquiv hc0 s) := by
  obtain ⟨y, s, hs, hys⟩ := SmoothVertex.exists_eq_of_uniformizer hp hp1 v hQ hoth ht hα
  refine ⟨(drintEquiv hc0).symm y, (drintEquiv hc0).symm s, ?_, ?_⟩ <;>
    simpa only [RingEquiv.apply_symm_apply]

end Smooth

end AffineTwist

end SemistableReduction
