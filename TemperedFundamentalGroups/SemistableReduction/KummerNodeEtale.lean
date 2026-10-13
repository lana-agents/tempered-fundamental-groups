/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.Node

/-!
# The Kummer covering of a node: `μ_e`-action, étale away from the node (§12.8, M2.1)

The local model of an admissible covering of a semistable curve at a node is the Kummer map
`Node.kummer π e : Node O (π ^ e) → Node O π`, `u ↦ u^e`, `v ↦ v^e` (`Node.lean`: injective,
finite; `TameLocal.lean`: the target is the normalization of the source in the Kummer extension).
Writing `A = Node O (π^e)` (`uv = π^e`) and `B = Node O π` (`st = π`, with `s = u_B`, `t = v_B`),
its special fibre is the covering `s^e = u`, `t^e = v` of the two branches of `uv = 0`, ramified
with index `e` on both branches. Here:

* `rot ζ` for `ζ^e = 1` (`ζ` a unit of `O`): **the `μ_e`-action** `s ↦ ζs`, `t ↦ ζ⁻¹t` by
  `A`-algebra maps (`rot_s`, `rot_t`, `rot_mul`, `rot_one`);
* **étale away from the node** (`etale`): for `e` invertible in `O`, `B_s` is standard étale over
  `A_u` (the branch `v = 0` removed): `B_s ≅ A_u[X]/(X^e − u)` (`presentation`, with the explicit
  inverse `χ`: `s ↦ X`, `t ↦ πX^{e−1}u⁻¹`), and `X^e − u` is separable since `e` and `u` are
  units (`pair`). By the symmetry `s ↔ t`, the same holds over `A_v`.
-/

universe w

namespace SemistableReduction

namespace KummerEtale

noncomputable section

variable {O : Type w} [CommRing O] (π : O) (e : ℕ)

/-- The node ring `A = O[u, v]/(uv − π^e)`. -/
abbrev A : Type w := Node O (π ^ e)

/-- The node ring `B = O[s, t]/(st − π)`. -/
abbrev B : Type w := Node O π

instance : Algebra (A π e) (B π) := Node.kummerAlgebra π e

instance : IsScalarTower O (A π e) (B π) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ ((Node.kummer π e).commutes r).symm

lemma algebraMap_u : algebraMap (A π e) (B π) (Node.u (π ^ e)) = Node.u π ^ e :=
  Node.kummer_u π e

lemma algebraMap_v : algebraMap (A π e) (B π) (Node.v (π ^ e)) = Node.v π ^ e :=
  Node.kummer_v π e

lemma kummer_eq (a : A π e) : Node.kummer π e a = algebraMap (A π e) (B π) a := rfl

/-! ### The `μ_e`-action -/

/-- `s ↦ ζs`, `t ↦ ζ⁻¹t` as an `O`-algebra map. -/
def rotO (ζ : Oˣ) : B π →ₐ[O] B π :=
  Node.lift ((ζ : O) • Node.u π) (((ζ⁻¹ : Oˣ) : O) • Node.v π) (by
    rw [smul_mul_smul_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul,
      Node.u_mul_v])

@[simp] lemma rotO_fst (ζ : Oˣ) : rotO π ζ (Node.u π) = (ζ : O) • Node.u π := Node.lift_u _ _ _

@[simp] lemma rotO_snd (ζ : Oˣ) : rotO π ζ (Node.v π) = ((ζ⁻¹ : Oˣ) : O) • Node.v π :=
  Node.lift_v _ _ _

lemma rotO_mul (ζ η : Oˣ) : rotO π (ζ * η) = (rotO π ζ).comp (rotO π η) := by
  refine Node.algHom_ext ?_ ?_
  · simp [mul_smul, smul_comm (ζ : O) (η : O)]
  · simp [mul_smul]

lemma rotO_one : rotO π 1 = AlgHom.id O (B π) := Node.algHom_ext (by simp) (by simp)

/-- `rotO ζ` is `A`-linear when `ζ^e = 1`. -/
lemma rotO_comp_kummer {ζ : Oˣ} (hζ : ζ ^ e = 1) :
    (rotO π ζ).comp (Node.kummer π e) = Node.kummer π e := by
  have hζ' : (ζ⁻¹ : Oˣ) ^ e = 1 := by rw [inv_pow, hζ, inv_one]
  refine Node.algHom_ext ?_ ?_
  · change rotO π ζ (Node.kummer π e (Node.u (π ^ e))) = Node.kummer π e (Node.u (π ^ e))
    simp only [Node.kummer_u, map_pow, rotO_fst, smul_pow, ← Units.val_pow_eq_pow_val, hζ,
      Units.val_one, one_smul]
  · change rotO π ζ (Node.kummer π e (Node.v (π ^ e))) = Node.kummer π e (Node.v (π ^ e))
    simp only [Node.kummer_v, map_pow, rotO_snd, smul_pow, ← Units.val_pow_eq_pow_val, hζ',
      Units.val_one, one_smul]

/-- **The `μ_e`-action** `s ↦ ζs`, `t ↦ ζ⁻¹t` by `A`-algebra maps. -/
def rot {ζ : Oˣ} (hζ : ζ ^ e = 1) : B π →ₐ[A π e] B π :=
  { rotO π ζ with
    commutes' := fun a => AlgHom.congr_fun (rotO_comp_kummer π e hζ) a }

@[simp] lemma rot_s {ζ : Oˣ} (hζ : ζ ^ e = 1) : rot π e hζ (Node.u π) = (ζ : O) • Node.u π :=
  rotO_fst π ζ

@[simp] lemma rot_t {ζ : Oˣ} (hζ : ζ ^ e = 1) :
    rot π e hζ (Node.v π) = ((ζ⁻¹ : Oˣ) : O) • Node.v π :=
  rotO_snd π ζ

/-- The `μ_e`-action is an action: `rot (ζη) = rot ζ ∘ rot η`. -/
lemma rot_mul {ζ η : Oˣ} (hζ : ζ ^ e = 1) (hη : η ^ e = 1) :
    rot π e (show (ζ * η) ^ e = 1 by rw [mul_pow, hζ, hη, one_mul]) =
      (rot π e hζ).comp (rot π e hη) :=
  AlgHom.restrictScalars_injective O (rotO_mul π ζ η)

/-- `rot 1 = id`. -/
lemma rot_one : rot π e (one_pow e) = AlgHom.id (A π e) (B π) :=
  AlgHom.restrictScalars_injective O (rotO_one π)

/-! ### Étale away from the node -/

section Etale


/-- `A_u`: the node ring with `u` inverted (the branch `v = 0` removed). -/
abbrev Au : Type w := Localization.Away (Node.u (π ^ e) : A π e)

/-- `B_s`: the covering ring with `s` inverted. -/
abbrev Bs : Type w := Localization.Away (Node.u π : B π)

lemma isUnit_s : IsUnit (algebraMap (B π) (Bs π) (Node.u π)) :=
  IsLocalization.Away.algebraMap_isUnit _

lemma isUnit_image_u :
    IsUnit ((algebraMap (B π) (Bs π)).comp (algebraMap (A π e) (B π)) (Node.u (π ^ e))) := by
  rw [RingHom.comp_apply, algebraMap_u, map_pow]
  exact (isUnit_s π).pow e

/-- The map `A_u → B_s`. -/
def auToBs : Au π e →+* Bs π :=
  IsLocalization.Away.lift (Node.u (π ^ e)) (isUnit_image_u π e)

instance : Algebra (Au π e) (Bs π) := (auToBs π e).toAlgebra

/-- `u` as a unit of `A_u`. -/
def uUnit : (Au π e)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (Node.u (π ^ e) : A π e) (S := Au π e)).unit

variable {e}

omit [CommRing O] in
/-- The derivative condition for `X^e − c`. -/
lemma cond_aux {S : Type*} [CommRing S] {n : ℕ} (hn : 0 < n) (c ci w : S)
    (hc : c * ci = 1) (hw : (n : S) * c * w = 1) :
    Polynomial.derivative (Polynomial.X ^ n - Polynomial.C c) * (Polynomial.C w * Polynomial.X) +
      (Polynomial.X ^ n - Polynomial.C c) * Polynomial.C (-ci) = 1 := by
  have hX : (Polynomial.X : Polynomial S) ^ (n - 1) * Polynomial.X = Polynomial.X ^ n :=
    pow_sub_one_mul hn.ne' _
  have hwc : (n : S) * w = ci := by linear_combination ci * hw - (n : S) * w * hc
  have hwc' : Polynomial.C (n : S) * Polynomial.C w = Polynomial.C ci := by
    rw [← map_mul, hwc]
  have hc' : Polynomial.C c * Polynomial.C ci = (1 : Polynomial S) := by
    rw [← map_mul, hc, map_one]
  rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero,
    map_neg]
  linear_combination (Polynomial.C (n : S) * Polynomial.C w) * hX +
    Polynomial.X ^ n * hwc' + hc'

/-- **The standard étale pair** `(X^e − u, 1)` over `A_u` (for `e` invertible). -/
def pair (he : 0 < e) (heu : IsUnit (e : O)) : StandardEtalePair (Au π e) where
  f := Polynomial.X ^ e - Polynomial.C (uUnit π e : Au π e)
  monic_f := Polynomial.monic_X_pow_sub_C _ he.ne'
  g := 1
  cond := by
    have heA : IsUnit (e : Au π e) := by
      have := heu.map (algebraMap O (Au π e))
      rwa [map_natCast] at this
    refine ⟨Polynomial.C (↑(heA.unit * uUnit π e)⁻¹ : Au π e) * Polynomial.X,
      Polynomial.C (-↑(uUnit π e)⁻¹), 0, ?_⟩
    rw [pow_zero]
    refine cond_aux he _ _ _ (Units.mul_inv _) ?_
    have h : (e : Au π e) * ↑(uUnit π e) = ↑(heA.unit * uUnit π e) := by
      rw [Units.val_mul, heA.unit_spec]
    rw [h, Units.mul_inv]

variable (he : 0 < e) (heu : IsUnit (e : O))

lemma auToBs_algebraMap (a : A π e) :
    auToBs π e (algebraMap (A π e) (Au π e) a) = algebraMap (B π) (Bs π) (Node.kummer π e a) :=
  IsLocalization.Away.lift_eq _ _ a

lemma uUnit_val : (uUnit π e : Au π e) = algebraMap (A π e) (Au π e) (Node.u (π ^ e)) :=
  IsUnit.unit_spec _

/-- `s` is a root of `X^e − u` in `B_s`. -/
lemma hasMap_s : (pair π he heu).HasMap (algebraMap (B π) (Bs π) (Node.u π)) := by
  refine ⟨?_, by simp [pair]⟩
  simp only [pair, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [sub_eq_zero, uUnit_val]
  change _ = auToBs π e _
  rw [auToBs_algebraMap, ← map_pow]
  congr 1
  exact (algebraMap_u π e).symm

/-- `X` in the standard étale algebra. -/
abbrev XR : (pair π he heu).Ring := (pair π he heu).X

/-- `u` in the standard étale algebra. -/
abbrev uR : (pair π he heu).Ringˣ :=
  Units.map (algebraMap (Au π e) (pair π he heu).Ring) (uUnit π e)

lemma XR_pow : XR π he heu ^ e = (uR π he heu : (pair π he heu).Ring) := by
  have h : Polynomial.aeval (XR π he heu)
      (Polynomial.X ^ e - Polynomial.C (uUnit π e : Au π e)) = 0 := (pair π he heu).hasMap_X.1
  rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, sub_eq_zero] at h
  exact h

/-- The structure map `O → P.Ring`. -/
abbrev φO : O →+* (pair π he heu).Ring :=
  (algebraMap (Au π e) (pair π he heu).Ring).comp
    ((algebraMap (A π e) (Au π e)).comp (algebraMap O (A π e)))

/-- The image of `t`: `π · X^{e−1} · u⁻¹`. -/
abbrev yR : (pair π he heu).Ring :=
  φO π he heu π * XR π he heu ^ (e - 1) * ↑(uR π he heu)⁻¹

lemma XR_mul_yR : XR π he heu * yR π he heu = φO π he heu π := by
  have hX : XR π he heu * XR π he heu ^ (e - 1) = XR π he heu ^ e := by
    rw [← pow_succ', Nat.sub_add_cancel he]
  calc XR π he heu * yR π he heu
      = φO π he heu π * (XR π he heu * XR π he heu ^ (e - 1)) * ↑(uR π he heu)⁻¹ := by ring
    _ = φO π he heu π := by rw [hX, XR_pow, mul_assoc, Units.mul_inv, mul_one]

/-- `B → P.Ring`, `s ↦ X`, `t ↦ π X^{e−1} u⁻¹`. -/
def χ₀ : B π →+* (pair π he heu).Ring :=
  Ideal.Quotient.lift (Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π})
    (MvPolynomial.eval₂Hom (φO π he heu) ![XR π he heu, yR π he heu])
    (fun p hp => by
      have hle : Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π} ≤
          RingHom.ker (MvPolynomial.eval₂Hom (φO π he heu) ![XR π he heu, yR π he heu]) := by
        rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
        simp [XR_mul_yR]
      exact hle hp)

lemma χ₀_fst : χ₀ π he heu (Node.u π) = XR π he heu := by simp [χ₀, Node.u]

lemma χ₀_snd : χ₀ π he heu (Node.v π) = yR π he heu := by simp [χ₀, Node.v]

lemma χ₀_algebraMap (r : O) : χ₀ π he heu (algebraMap O (B π) r) = φO π he heu r := by
  change χ₀ π he heu (Ideal.Quotient.mk _ (MvPolynomial.C r)) = _
  simp [χ₀]

lemma isUnit_χ₀_fst : IsUnit (χ₀ π he heu (Node.u π)) := by
  rw [χ₀_fst]
  have : IsUnit (XR π he heu ^ e) := by rw [XR_pow]; exact Units.isUnit _
  exact (isUnit_pow_iff he.ne').1 this

/-- **The inverse** `B_s → P.Ring`. -/
def χ : Bs π →+* (pair π he heu).Ring :=
  IsLocalization.Away.lift (Node.u π) (isUnit_χ₀_fst π he heu)

lemma χ_algebraMap (b : B π) : χ π he heu (algebraMap (B π) (Bs π) b) = χ₀ π he heu b :=
  IsLocalization.Away.lift_eq _ _ b

/-- `lift s` sends `u` to `s^e`. -/
lemma lift_uR : (pair π he heu).lift _ (hasMap_s π he heu) (uR π he heu : (pair π he heu).Ring) =
    algebraMap (B π) (Bs π) (Node.u π) ^ e := by
  change (pair π he heu).lift _ (hasMap_s π he heu)
    (algebraMap (Au π e) (pair π he heu).Ring (uUnit π e)) = _
  rw [AlgHom.commutes, uUnit_val]
  change auToBs π e _ = _
  rw [auToBs_algebraMap, ← map_pow, ← algebraMap_u]
  rfl

/-- **`lift s ∘ χ = id`.** -/
lemma lift_χ (z : Bs π) : (pair π he heu).lift _ (hasMap_s π he heu) (χ π he heu z) = z := by
  set L := (pair π he heu).lift _ (hasMap_s π he heu)
  have key : (L.toRingHom.comp (χ π he heu)).comp (algebraMap (B π) (Bs π)) =
      algebraMap (B π) (Bs π) := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
    · change L (χ π he heu (algebraMap (B π) (Bs π) (algebraMap O (B π) r))) =
        algebraMap (B π) (Bs π) (algebraMap O (B π) r)
      rw [χ_algebraMap, χ₀_algebraMap]
      change L (algebraMap (Au π e) _ (algebraMap (A π e) (Au π e) (algebraMap O (A π e) r))) = _
      rw [AlgHom.commutes]
      change auToBs π e _ = _
      rw [auToBs_algebraMap, AlgHom.commutes]
    · fin_cases i
      · change L (χ π he heu (algebraMap (B π) (Bs π) (Node.u π))) =
          algebraMap (B π) (Bs π) (Node.u π)
        rw [χ_algebraMap, χ₀_fst]
        exact (pair π he heu).lift_X _ _
      · change L (χ π he heu (algebraMap (B π) (Bs π) (Node.v π))) =
          algebraMap (B π) (Bs π) (Node.v π)
        rw [χ_algebraMap, χ₀_snd]
        set a := algebraMap (B π) (Bs π) (Node.u π)
        have hv : L ↑(uR π he heu)⁻¹ * a ^ e = 1 := by
          rw [← lift_uR π he heu, ← map_mul, Units.inv_mul, map_one]
        have hπ : L (φO π he heu π) = a * algebraMap (B π) (Bs π) (Node.v π) := by
          change L (algebraMap (Au π e) _ (algebraMap (A π e) (Au π e) (algebraMap O (A π e) π)))
            = _
          rw [AlgHom.commutes]
          change auToBs π e _ = _
          rw [auToBs_algebraMap, AlgHom.commutes, ← map_mul, Node.u_mul_v]
        have hX : L (XR π he heu) = a := (pair π he heu).lift_X _ _
        have hpow : a * a ^ (e - 1) = a ^ e := by rw [← pow_succ', Nat.sub_add_cancel he]
        simp only [yR, map_mul, map_pow, hπ, hX]
        linear_combination (algebraMap (B π) (Bs π) (Node.v π)) * (L ↑(uR π he heu)⁻¹) * hpow +
          (algebraMap (B π) (Bs π) (Node.v π)) * hv
  have hL : L.toRingHom.comp (χ π he heu) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (Node.u π)) (by rw [key]; rfl)
  exact RingHom.congr_fun hL z

/-- `yR^e = v` in `P.Ring`. -/
lemma yR_pow : yR π he heu ^ e =
    algebraMap (Au π e) (pair π he heu).Ring (algebraMap (A π e) (Au π e) (Node.v (π ^ e))) := by
  set V := algebraMap (Au π e) (pair π he heu).Ring (algebraMap (A π e) (Au π e) (Node.v (π ^ e)))
  set U : (pair π he heu).Ring := ↑(uR π he heu)
  set Ui : (pair π he heu).Ring := ↑(uR π he heu)⁻¹
  have hinv : U * Ui = 1 := Units.mul_inv _
  have hUV : U * V = φO π he heu π ^ e := by
    have h := congrArg (fun a => algebraMap (Au π e) (pair π he heu).Ring
      (algebraMap (A π e) (Au π e) a)) (Node.u_mul_v (π ^ e))
    simp only [map_mul, map_pow] at h
    rw [show U = algebraMap (Au π e) (pair π he heu).Ring (uUnit π e) from rfl, uUnit_val]
    rw [h]
    rfl
  have hXp : (XR π he heu ^ (e - 1)) ^ e = U ^ (e - 1) := by
    rw [← pow_mul (XR π he heu), mul_comm (e - 1) e, pow_mul (XR π he heu) e (e - 1), XR_pow]
  have hpe : U ^ e * Ui ^ e = 1 := by rw [← mul_pow, hinv, one_pow]
  have hpu : U ^ (e - 1) * U = U ^ e := by rw [← pow_succ, Nat.sub_add_cancel he]
  have hyU : yR π he heu ^ e * U = φO π he heu π ^ e := by
    simp only [yR, mul_pow, hXp]
    linear_combination φO π he heu π ^ e * Ui ^ e * hpu + φO π he heu π ^ e * hpe
  have hUunit : IsUnit U := Units.isUnit _
  apply hUunit.mul_right_cancel
  rw [hyU, mul_comm V, hUV]

/-- **`χ` is `A_u`-linear.** -/
lemma χ_auToBs (c : Au π e) :
    χ π he heu (algebraMap (Au π e) (Bs π) c) = algebraMap (Au π e) (pair π he heu).Ring c := by
  have key : ((χ π he heu).comp (auToBs π e)).comp (algebraMap (A π e) (Au π e)) =
      (algebraMap (Au π e) (pair π he heu).Ring).comp (algebraMap (A π e) (Au π e)) := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
    · change χ π he heu (auToBs π e (algebraMap (A π e) (Au π e) (algebraMap O (A π e) r))) =
        φO π he heu r
      rw [auToBs_algebraMap, χ_algebraMap, AlgHom.commutes, χ₀_algebraMap]
    · fin_cases i
      · change χ π he heu (auToBs π e (algebraMap (A π e) (Au π e) (Node.u (π ^ e)))) =
          algebraMap (Au π e) _ (algebraMap (A π e) (Au π e) (Node.u (π ^ e)))
        rw [auToBs_algebraMap, χ_algebraMap, ← uUnit_val]
        change χ₀ π he heu (Node.kummer π e (Node.u (π ^ e))) = ↑(uR π he heu)
        rw [← XR_pow, ← χ₀_fst, ← map_pow]
        exact congrArg _ (Node.lift_u _ _ _)
      · change χ π he heu (auToBs π e (algebraMap (A π e) (Au π e) (Node.v (π ^ e)))) =
          algebraMap (Au π e) _ (algebraMap (A π e) (Au π e) (Node.v (π ^ e)))
        rw [auToBs_algebraMap, χ_algebraMap, ← yR_pow, ← χ₀_snd, ← map_pow]
        exact congrArg _ (Node.lift_v _ _ _)
  have h := IsLocalization.ringHom_ext (Submonoid.powers (Node.u (π ^ e))) key
  exact RingHom.congr_fun h c

/-- `χ` as an `A_u`-algebra map. -/
def χAlg : Bs π →ₐ[Au π e] (pair π he heu).Ring :=
  { χ π he heu with commutes' := χ_auToBs π he heu }

/-- **`χ ∘ lift s = id`.** -/
lemma χ_lift (w : (pair π he heu).Ring) :
    χ π he heu ((pair π he heu).lift _ (hasMap_s π he heu) w) = w := by
  have h : (χAlg π he heu).comp ((pair π he heu).lift _ (hasMap_s π he heu)) = AlgHom.id _ _ := by
    refine (pair π he heu).hom_ext ?_
    rw [AlgHom.comp_apply, (pair π he heu).lift_X, AlgHom.id_apply]
    change χ π he heu (algebraMap (B π) (Bs π) (Node.u π)) = _
    rw [χ_algebraMap, χ₀_fst]
  exact AlgHom.congr_fun h w

/-- **The standard étale presentation of `B_s` over `A_u`.** -/
def presentation : StandardEtalePresentation (Au π e) (Bs π) where
  P := pair π he heu
  x := algebraMap (B π) (Bs π) (Node.u π)
  hasMap := hasMap_s π he heu
  lift_bijective := Function.bijective_iff_has_inverse.2
    ⟨χ π he heu, χ_lift π he heu, lift_χ π he heu⟩

include he heu in
/-- **The Kummer covering is étale away from the node** (over `A_u`, `u` invertible): `B_s` is
standard étale over `A_u` (for `e` invertible in `O`). -/
theorem etale : Algebra.Etale (Au π e) (Bs π) :=
  haveI : Algebra.IsStandardEtale (Au π e) (Bs π) := ⟨⟨presentation π he heu⟩⟩
  inferInstance

end Etale

end

end KummerEtale

end SemistableReduction
