/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspCoverAbhyankar

/-!
# Tame covers of the cusp chart are Kummer (MR12 T2 S3)

Let `O` be a discrete valuation ring with uniformizer `ϖ` and fraction field `K`. The **cusp
chart** is `N = O[t]` with the cusp point `𝔪 = (ϖ, t)` (`Cusp.cuspIdeal`) on the horizontal
divisor `t = 0`.

## The Kummer form at a cusp

* `Cusp.CuspField O d = Frac O[y]`, an `O[t]`-algebra via the Kummer map `t ↦ y ^ d`
  (`Cusp.KPoly O d = O[y]`, `Polynomial.expand`);
* the **cusp Kummer factor** `Cusp.CuspFactor O d N₁ = N₁ ⊗_{O[t]} Frac O[y]` over an
  `O[t]`-algebra `N₁`, and its normalisation `Cusp.CuspNormalFactor O d N₁ = N₁ ⊗_{O[t]} O[y]`
  `= N₁[y] ⧸ (y ^ d - t)`: for `N₁` smooth over `O[t]` the latter is the integral closure of
  `N₁` in the former (`Cusp.cuspFactorEquiv`, from `O[y]` normal and normalisation commuting
  with smooth base change), the cusp analogue of `kummerFactorEquiv`;
* **`IsCuspKummerAt O t F' 𝔪`** (the analogue of `IsKummerAt` for nodes): for an `O`-algebra `N`
  with `t ∈ N`, an `N`-algebra `F'` and a prime `𝔪` of `N`, there are an étale `N`-algebra `N₁`
  with a prime `𝔫` over `𝔪` and `t₁ = η t ∈ 𝔫` (`η` a unit) with `O[X] → N₁`, `X ↦ t₁` étale
  (an `O[X]`-algebra structure on `N₁` compatible with `O`, sending `X` to `t₁`), such that
  `N₁ ⊗_N F' ≅ ∏ᵢ N₁ ⊗_{O[X]} Frac O[y]` (`X ↦ y ^ dᵢ`, `dᵢ > 0`).

## Main result

**`Cusp.isCuspKummerAt_chart`**: let `char K = 0` (`CharZero O`), `e ≥ 1` with a primitive
`e`-th root of unity in `K(T ^ e)` (the function field of the chart, `t ↦ T ^ e`), and
`L / K(T ^ e)` finite Galois of degree dividing `e` whose normalisation over the local ring
`R = O[t]_𝔪` is unramified over every prime of `R` other than `𝔪` and the horizontal divisor
`(t)`. Then `IsCuspKummerAt O t L 𝔪`.

Proof: the generic "S4-local" (`NodeCover.exists_etale_tensor_algEquiv_pi_of_etale`, with
`q = 1`, `M = M' = e`) for the finite local map `R → R_e = O[t']_{(ϖ, t')}`, `t ↦ t' ^ e`, with
`hEt` from purity and Abhyankar (`Cusp.etale_integralClosure`), gives an étale neighbourhood of
the closed point of `R` with function field `E` and `E ⊗ L ≅ ∏ E ⊗ K(T ^ e)(T ^ n)`, `n e' = e`;
it descends to an étale domain `N₁` over `O[t]` (`EtaleDescent`), the base change is cancelled
(`tensorEquivPiOfEquiv`) and `K(T ^ e)(T ^ n) = K(T ^ n) ≅ Frac O[y]` (`y ↦ T ^ n`) compatibly
with `t ↦ y ^ e'` (`Cusp.adjoinPowCuspEquiv`). This is the same assembly as
`NodeCover.isKummerAt_node` for the node.

## Hypotheses

`CharZero O` is used only at the horizontal divisor (residue field `K`): there the Galois
extension is tame and residue extensions are separable. The degree condition `[L : K(T ^ e)] ∣ e`
makes the ramification indices at `(t)` divide `e` (Abhyankar's lemma); no condition on the
residue characteristic of `O` is needed.
-/

open Polynomial IsLocalRing IntermediateField Module TensorProduct

universe u

namespace SemistableReduction

namespace Cusp

section KummerField

variable (O : Type u) [CommRing O] (d : ℕ)

/-- The function field `Frac O[y]` of the Kummer cover `t = y ^ d` of the cusp chart `O[t]`,
as an algebra over `O[t]` (`t ↦ y ^ d`). -/
def CuspField : Type u := FractionRing (KPoly O d)

noncomputable instance : CommRing (CuspField O d) :=
  inferInstanceAs (CommRing (FractionRing (KPoly O d)))

noncomputable instance : Algebra (KPoly O d) (CuspField O d) :=
  inferInstanceAs (Algebra (KPoly O d) (FractionRing (KPoly O d)))

instance : IsFractionRing (KPoly O d) (CuspField O d) :=
  inferInstanceAs (IsFractionRing (KPoly O d) (FractionRing (KPoly O d)))

noncomputable instance : Algebra O[X] (CuspField O d) :=
  ((algebraMap (KPoly O d) (CuspField O d)).comp (algebraMap O[X] (KPoly O d))).toAlgebra

instance : IsScalarTower O[X] (KPoly O d) (CuspField O d) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable (N₁ : Type u) [CommRing N₁] [Algebra O[X] N₁]

/-- The **cusp Kummer factor** `N₁ ⊗_{O[t]} Frac O[y]` (`t ↦ y ^ d`). -/
abbrev CuspFactor : Type u := N₁ ⊗[O[X]] CuspField O d

/-- Its normalisation `N₁ ⊗_{O[t]} O[y] = N₁[y] ⧸ (y ^ d - t)`. -/
abbrev CuspNormalFactor : Type u := N₁ ⊗[O[X]] KPoly O d

variable {O d}

/-- `O[y]` is the integral closure of `O[t]` in `Frac O[y]` (`t ↦ y ^ d`). -/
theorem KPoly.isIntegralClosure [IsDomain O] [IsDiscreteValuationRing O] [NeZero d] :
    IsIntegralClosure (KPoly O d) O[X] (CuspField O d) := by
  haveI : IsIntegrallyClosed (KPoly O d) := inferInstanceAs (IsIntegrallyClosed O[X])
  haveI : Algebra.IsIntegral O[X] (KPoly O d) := Algebra.IsIntegral.of_finite _ _
  exact IsIntegralClosure.of_isIntegrallyClosed _ _ _

/-- **Étale-local normalisation of a cusp Kummer factor.** For a smooth (e.g. étale) `O[t]`-algebra
`N₁`, the integral closure of `N₁` in `N₁ ⊗_{O[t]} Frac O[y]` is `N₁ ⊗_{O[t]} O[y]`. -/
noncomputable def cuspFactorEquiv [IsDomain O] [IsDiscreteValuationRing O] [NeZero d]
    [Algebra.Smooth O[X] N₁] :
    CuspNormalFactor O d N₁ ≃ₐ[N₁] integralClosure N₁ (CuspFactor O d N₁) :=
  haveI := KPoly.isIntegralClosure (O := O) (d := d)
  (Algebra.TensorProduct.congr AlgEquiv.refl
    (IsIntegralClosure.equiv O[X] (KPoly O d) (CuspField O d)
      (integralClosure O[X] (CuspField O d)))).trans
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure O[X] N₁ (CuspField O d))
      TensorProduct.toIntegralClosure_bijective_of_smooth)

end KummerField

end Cusp

open Cusp in
/-- **The cover `F'` of `N` is Kummer at the cusp point `𝔪`** (the analogue of `IsKummerAt` at a
smooth point on the horizontal divisor `t = 0`): étale-locally at `𝔪` the base is the cusp chart
`O[X] → N₁`, `X ↦ t₁` (étale), with `t₁ ∈ 𝔫` a unit multiple of `t`, and `F'` is a product of
Kummer covers `t₁ = y ^ dᵢ` of it. -/
def IsCuspKummerAt (O : Type u) [CommRing O] {N : Type u} [CommRing N] [Algebra O N] (t : N)
    (F' : Type u) [CommRing F'] [Algebra N F'] (𝔪 : Ideal N) : Prop :=
  ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : Algebra N N₁) (_ : Algebra.Etale N N₁) (𝔫 : Ideal N₁)
    (_ : 𝔫.IsPrime) (_ : 𝔫.comap (algebraMap N N₁) = 𝔪),
    letI : Algebra O N₁ := ((algebraMap N N₁).comp (algebraMap O N)).toAlgebra
    ∃ (t₁ : N₁) (_ : Algebra O[X] N₁), IsScalarTower O O[X] N₁ ∧ algebraMap O[X] N₁ X = t₁ ∧
      Algebra.Etale O[X] N₁ ∧ t₁ ∈ 𝔫 ∧ (∃ η : N₁, IsUnit η ∧ t₁ = η * algebraMap N N₁ t) ∧
      ∃ (r : ℕ) (d : Fin r → ℕ) (_ : ∀ i, 0 < d i),
        Nonempty (N₁ ⊗[N] F' ≃ₐ[N₁] ∀ i, CuspFactor O (d i) N₁)

namespace Cusp

section Chart

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {e : ℕ} [NeZero e]

local notation "𝔎" => FractionRing O
local notation "R" => Localization.AtPrime (cuspIdeal O)
local notation "R_e" => Localization.AtPrime (KPoly.ideal O e)
local notation "𝕂" => 𝔎⟮(RatFunc.X : RatFunc 𝔎) ^ e⟯

attribute [local instance 2000] adjoinPowAlgebra locAdjoinPowAlgebra kPolyRatFuncAlgebra
  locRatFuncAlgebra localKummerAlgebra

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search through the intermediate fields of `K(T)` is slow.
/-- `K(T ^ e)(T ^ n) ≅ Frac O[y]` (`T ^ n ↦ y`) for `n e' = e`, compatibly with `t ↦ T ^ e` and
`t ↦ y ^ e'`. -/
noncomputable def adjoinPowCuspEquiv {n e' : ℕ} (hn : 0 < n) (h : n * e' = e) :
    letI : Algebra O[X] ((𝕂)⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯) :=
      ((algebraMap 𝕂 ((𝕂)⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯)).comp (algebraMap O[X] 𝕂)).toAlgebra
    (𝕂)⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯ ≃ₐ[O[X]] CuspField O e' :=
  letI : Algebra O[X] ((𝕂)⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯) :=
    ((algebraMap 𝕂 ((𝕂)⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯)).comp (algebraMap O[X] 𝕂)).toAlgebra
  letI : Algebra (KPoly O e') 𝔎⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯ := adjoinPowAlgebra O n
  haveI : IsFractionRing (KPoly O e') 𝔎⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯ :=
    isFractionRing_adjoinPow (O := O) hn
  AlgEquiv.ofRingEquiv (f := (Node.adjoinPowEquiv (O := O) h).trans
    (FractionRing.algEquiv (KPoly O e') 𝔎⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯).symm.toRingEquiv)
    fun f ↦ by
      change (FractionRing.algEquiv (KPoly O e') 𝔎⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯).symm
        (Node.adjoinPowEquiv (O := O) h (algebraMap 𝕂 _ (algebraMap O[X] 𝕂 f))) =
          algebraMap (KPoly O e') (FractionRing (KPoly O e')) (algebraMap O[X] (KPoly O e') f)
      rw [AlgEquiv.symm_apply_eq, AlgEquiv.commutes]
      apply Subtype.ext
      change toRatFunc O e f = toRatFunc O n (expand O e' f)
      rw [toRatFunc_expand, mul_comm, h]

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search through the intermediate fields of `K(T)` is slow.
set_option maxHeartbeats 1000000 in
-- The many tensor product, localization and intermediate field structures make this slow.
/-- **Tame covers of the cusp chart are Kummer** (MR12 T2 S3). Let `O` be a discrete valuation
ring of characteristic zero with uniformizer `ϖ`, `e ≥ 1`, `K(T ^ e)` the function field of the
cusp chart `O[t]` (`t ↦ T ^ e`), containing a primitive `e`-th root of unity, and `L / K(T ^ e)`
finite Galois of degree dividing `e` whose normalisation `B` over the local ring `R` of the cusp
point is unramified over every prime of `R` other than the cusp point and the horizontal divisor
`(t)`. Then `L` is Kummer at the cusp point: étale-locally it is a product of Kummer covers
`t = y ^ e'`, `e' ∣ e`. -/
theorem isCuspKummerAt_chart [CharZero O] {ϖ : O} (hϖ : Irreducible ϖ) {ζ : 𝕂}
    (hζ : IsPrimitiveRoot ζ e) (L : Type u) [Field L] [Algebra 𝕂 L] [FiniteDimensional 𝕂 L]
    [IsGalois 𝕂 L] (hd : finrank 𝕂 L ∣ e) [Algebra O[X] L] [IsScalarTower O[X] 𝕂 L]
    [Algebra R L] [IsScalarTower O[X] R L]
    (B : Type u) [CommRing B] [Algebra R B] [Algebra B L] [IsScalarTower R B L]
    [IsIntegralClosure B R L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap R B) ≠ maximalIdeal R →
      Q.comap (algebraMap R B) ≠ Ideal.span {algebraMap O[X] R X} →
        Algebra.IsUnramifiedAt R Q) :
    IsCuspKummerAt O (X : O[X]) L (cuspIdeal O) := by
  classical
  have he : 0 < e := Nat.pos_of_neZero e
  letI := locAdjoinPowAlgebra O e
  haveI := isFractionRing_loc_adjoinPow O e
  haveI := isScalarTower_poly_loc_adjoinPow O e
  haveI : IsFractionRing O[X] 𝕂 := isFractionRing_adjoinPow (O := O) he
  letI := locRatFuncAlgebra' O e
  haveI := isScalarTower_loc_adjoinPow_ratFunc O e
  haveI : IsFractionRing R_e (RatFunc 𝔎) := isFractionRing_locE O e
  haveI : IsScalarTower R R_e (RatFunc 𝔎) := isScalarTower_loc O e
  haveI : IsNoetherianRing R_e := isNoetherianRing_locE O e
  haveI : IsIntegrallyClosed R_e := isIntegrallyClosed_locE O e
  haveI : IsNoetherianRing R := isNoetherianRing_loc O
  haveI : IsIntegrallyClosed R := isIntegrallyClosed_loc O
  haveI := localKummer_finite O e
  haveI : IsScalarTower R 𝕂 L := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext
      (cuspIdeal O).primeCompl (RingHom.ext fun x ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply O[X] R L x,
      ← IsScalarTower.algebraMap_apply O[X] R 𝕂 x,
      ← IsScalarTower.algebraMap_apply O[X] 𝕂 L x]
  -- "S4-local" with `q = 1`: the splitting over an étale neighbourhood of the closed point
  obtain ⟨R', _, _, _, P, _, hP, E, _, _, ⟨φ⟩, e', he', r, ⟨Φ⟩⟩ :=
    NodeCover.exists_etale_tensor_algEquiv_pi_of_etale (R_M := R) (R_1 := R_e) (M := e)
      (q := 1) (M' := e) (one_mul e) one_pos he (residueField_map_localKummer_bijective O e)
      𝕂 (RatFunc 𝔎) (X := RatFunc.X) (x := ⟨RatFunc.X ^ e, mem_adjoin_simple_self 𝔎 _⟩) rfl
      (Node.adjoin_X_eq_top (O := O) e) (Node.finrank_adjoin_X_pow (O := O) e) hζ L
      (Nat.coprime_one_right _)
      fun L₁ _ _ _ _ _ _ _ _ _ _ hgen ↦ etale_integralClosure L L₁ hϖ hd B hunr hgen
  obtain ⟨n, hn⟩ : ∃ n, 1 * (e / e') = n := ⟨_, rfl⟩
  rw [hn] at Φ
  have hne : n * e' = e := by rw [← hn, one_mul, Nat.div_mul_cancel he']
  have he'0 : 0 < e' := Nat.pos_of_dvd_of_pos he' he
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h ↦ NeZero.ne e (by rw [← hne, h, zero_mul])
  -- descent to an étale domain `N₁` over the chart
  obtain ⟨N₁, _, _, _, _, 𝔫, _, h𝔫, eL, heL⟩ :=
    EtaleDescent.exists_etale_isDomain_localization_equiv (cuspIdeal O) P
  have h𝔫' : 𝔫.comap (algebraMap O[X] N₁) = cuspIdeal O := by
    have h1 : P.comap (algebraMap R R') = maximalIdeal R := hP.over.symm
    rw [h𝔫, ← Ideal.comap_comap, h1]
    exact Localization.AtPrime.under_maximalIdeal
  -- the generic fibre of `N₁` is the function field `E` of the neighbourhood
  have hEfield : IsField (𝕂 ⊗[R] Localization.AtPrime P) :=
    MulEquiv.isField (Field.toIsField E) φ.toRingEquiv.toMulEquiv
  obtain ⟨θ⟩ := nonempty_tensor_algEquiv_of_localization_equiv (A := O[X]) (B := R)
    (C := Localization.AtPrime P) (N₁ := N₁) 𝔫 eL (fun a ↦ by
      rw [← IsScalarTower.algebraMap_apply O[X] N₁ (Localization.AtPrime 𝔫) a, heL,
        IsScalarTower.algebraMap_apply R R' (Localization.AtPrime P)]) hEfield
  -- the splitting of `N₁ ⊗_{O[t]} L`
  letI : Algebra O[X] ((𝕂)⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯) :=
    ((algebraMap 𝕂 ((𝕂)⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯)).comp (algebraMap O[X] 𝕂)).toAlgebra
  haveI : IsScalarTower O[X] 𝕂 ((𝕂)⟮(RatFunc.X : RatFunc 𝔎) ^ n⟯) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let Ψ₁ := tensorEquivPiOfEquiv (θ.trans φ) Φ
  let χ := adjoinPowCuspEquiv (O := O) (e := e) hn0 hne
  let Ψ : N₁ ⊗[O[X]] L ≃ₐ[N₁] (Fin r → CuspFactor O e' N₁) :=
    Ψ₁.trans (AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.congr AlgEquiv.refl χ)
  -- the chart `O[X] → N₁`, `X ↦ t₁`
  letI algO : Algebra O N₁ := ((algebraMap O[X] N₁).comp (algebraMap O O[X])).toAlgebra
  haveI : IsScalarTower O O[X] N₁ := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨t₁, ht₁def⟩ : ∃ t, t = algebraMap O[X] N₁ X := ⟨_, rfl⟩
  have ht₁ : t₁ ∈ 𝔫 := by
    have := X_mem_cuspIdeal (O := O)
    rw [← h𝔫'] at this
    rw [ht₁def]
    exact this
  exact ⟨N₁, inferInstance, inferInstance, inferInstance, 𝔫, inferInstance, h𝔫', t₁,
    inferInstance, inferInstance, ht₁def.symm, inferInstance, ht₁,
    ⟨1, isUnit_one, by rw [one_mul, ht₁def]⟩, r, fun _ ↦ e', fun _ ↦ he'0, ⟨Ψ⟩⟩

end Chart

end Cusp

end SemistableReduction
