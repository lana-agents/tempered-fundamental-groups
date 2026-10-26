/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspCover
import TemperedFundamentalGroups.SemistableReduction.KummerTame

/-!
# Tame Kummer covers of cusps with the given coordinate, at the level of the normalisation

The cusp analogue of `KummerTame`. `IsCuspKummerAt O t F' 𝔪` (`CuspCover`) allows the étale-local
cusp coordinate `t₁ = η t` to differ from the given one by a unit and records no bound on the
local degrees `dᵢ`. The covers produced by `Cusp.isCuspKummerAt_chart` are better: `η = 1` and
`dᵢ ∣ e`. We record this in a separate predicate (`IsCuspKummerAt` is unchanged):

* **`Cusp.IsTameCuspKummerAt O e t F' 𝔪`**: there are an étale `N`-algebra `N₁` and a prime `𝔫`
  over `𝔪` containing `t`, with an étale chart `O[X] → N₁`, `X ↦ t`, and an `N₁`-algebra
  isomorphism `N₁ ⊗_N F' ≅ ∏ᵢ N₁ ⊗_{O[X]} Frac O[y]` (`X ↦ y ^ dᵢ`, `0 < dᵢ ∣ e`). It implies
  `IsCuspKummerAt` (`Cusp.IsTameCuspKummerAt.isCuspKummerAt`) and descends along étale maps
  (`Cusp.IsTameCuspKummerAt.comap_of_*`).
* **`Cusp.IsCuspNormAt O e t B 𝔪`** (the normalisation-level predicate): the same with the
  normalisation `B` of `N` in `F'` and the normalised factors `N₁ ⊗_{O[X]} O[y]`
  (`CuspNormalFactor`). **`Cusp.IsTameCuspKummerAt.isCuspNormAt`**: normalisation commutes with
  étale base change and the normalisation of a cusp Kummer factor is `N₁ ⊗_{O[X]} O[y]`
  (`Cusp.cuspFactorEquiv`).
* **`Cusp.isTameCuspKummerAt_chart`**: the tame form of `Cusp.isCuspKummerAt_chart`.
-/

open Polynomial IsLocalRing IntermediateField Module TensorProduct

universe u

namespace SemistableReduction.Cusp

section Split

variable (O : Type u) [CommRing O] (e : ℕ) {N₁ : Type u} [CommRing N₁] [Algebra O N₁]
  (t₁ : N₁) (𝔫 : Ideal N₁) (Z : Type u) [CommRing Z] [Algebra N₁ Z]

/-- The splitting of an `N₁`-algebra `Z` into cusp Kummer factors over an étale cusp chart
`O[X] → N₁`, `X ↦ t₁ ∈ 𝔫`, with local degrees `0 < dᵢ ∣ e`. -/
def CuspSplit : Prop :=
  ∃ (_ : Algebra O[X] N₁), IsScalarTower O O[X] N₁ ∧ algebraMap O[X] N₁ X = t₁ ∧
    Algebra.Etale O[X] N₁ ∧ t₁ ∈ 𝔫 ∧
    ∃ (r : ℕ) (d : Fin r → ℕ) (_ : ∀ i, 0 < d i) (_ : ∀ i, d i ∣ e),
      Nonempty (Z ≃ₐ[N₁] ∀ i, CuspFactor O (d i) N₁)

/-- The splitting of an `N₁`-algebra `Z` into normalised cusp Kummer factors
`N₁ ⊗_{O[X]} O[y]` over an étale cusp chart `O[X] → N₁`, `X ↦ t₁ ∈ 𝔫`, with local degrees
`0 < dᵢ ∣ e`. -/
def CuspNormSplit : Prop :=
  ∃ (_ : Algebra O[X] N₁), IsScalarTower O O[X] N₁ ∧ algebraMap O[X] N₁ X = t₁ ∧
    Algebra.Etale O[X] N₁ ∧ t₁ ∈ 𝔫 ∧
    ∃ (r : ℕ) (d : Fin r → ℕ) (_ : ∀ i, 0 < d i) (_ : ∀ i, d i ∣ e),
      Nonempty (Z ≃ₐ[N₁] ∀ i, CuspNormalFactor O (d i) N₁)

variable {O e t₁ 𝔫 Z}

lemma CuspSplit.of_algEquiv {Z' : Type u} [CommRing Z'] [Algebra N₁ Z'] (φ : Z' ≃ₐ[N₁] Z)
    (h : CuspSplit O e t₁ 𝔫 Z) : CuspSplit O e t₁ 𝔫 Z' := by
  obtain ⟨_, hT, hX, hE, ht, r, d, hd, hde, ⟨Φ⟩⟩ := h
  exact ⟨_, hT, hX, hE, ht, r, d, hd, hde, ⟨φ.trans Φ⟩⟩

lemma CuspNormSplit.of_algEquiv {Z' : Type u} [CommRing Z'] [Algebra N₁ Z']
    (φ : Z' ≃ₐ[N₁] Z) (h : CuspNormSplit O e t₁ 𝔫 Z) : CuspNormSplit O e t₁ 𝔫 Z' := by
  obtain ⟨_, hT, hX, hE, ht, r, d, hd, hde, ⟨Φ⟩⟩ := h
  exact ⟨_, hT, hX, hE, ht, r, d, hd, hde, ⟨φ.trans Φ⟩⟩

end Split

section Data

variable (O : Type u) [CommRing O] (e : ℕ) {N : Type u} [CommRing N] (t : N)
  (F' : Type u) [CommRing F'] [Algebra N F'] (N₁ : Type u) [CommRing N₁] [Algebra N N₁]
  (𝔫 : Ideal N₁)

/-- The data of `IsTameCuspKummerAt` over a fixed étale neighbourhood `N₁ ⊇ 𝔫`, with the
structure map `f : O → N₁` as a variable. -/
def TameCuspKummerAtData (f : O →+* N₁) : Prop :=
  letI : Algebra O N₁ := f.toAlgebra
  CuspSplit O e (algebraMap N N₁ t) 𝔫 (N₁ ⊗[N] F')

variable {O e t F' N₁ 𝔫}

lemma TameCuspKummerAtData.of_eq {f g : O →+* N₁} (hfg : f = g)
    (h : TameCuspKummerAtData O e t F' N₁ 𝔫 f) : TameCuspKummerAtData O e t F' N₁ 𝔫 g :=
  hfg ▸ h

/-- Descent of the data along `N' → N` when `N₁ ⊗_{N'} F' = N₁ ⊗_N F'`. -/
lemma TameCuspKummerAtData.comap {N' : Type u} [CommRing N'] [Algebra N' N] [Algebra N' F']
    [IsScalarTower N' N F'] [Algebra N' N₁] [IsScalarTower N' N N₁]
    [CompatibleSMul N' N N₁ F'] {t : N'} {f : O →+* N₁}
    (h : TameCuspKummerAtData O e (algebraMap N' N t) F' N₁ 𝔫 f) :
    TameCuspKummerAtData O e t F' N₁ 𝔫 f := by
  letI : Algebra O N₁ := f.toAlgebra
  have et : algebraMap N N₁ (algebraMap N' N t) = algebraMap N' N₁ t :=
    (IsScalarTower.algebraMap_apply N' N N₁ t).symm
  unfold TameCuspKummerAtData at h ⊢
  rw [et] at h
  exact h.of_algEquiv (Algebra.TensorProduct.equivOfCompatibleSMul N N' N₁ N₁ F')

end Data

/-- **The cover `F'` of `N` is tamely Kummer at the cusp point `𝔪` with respect to the coordinate
`t`**: `IsCuspKummerAt` with `t₁ = t` (the étale chart `O[X] → N₁` sends `X` to `t`) and local
degrees dividing `e`. -/
def IsTameCuspKummerAt (O : Type u) [CommRing O] (e : ℕ) {N : Type u} [CommRing N] [Algebra O N]
    (t : N) (F' : Type u) [CommRing F'] [Algebra N F'] (𝔪 : Ideal N) : Prop :=
  ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : Algebra N N₁) (_ : Algebra.Etale N N₁) (𝔫 : Ideal N₁)
    (_ : 𝔫.IsPrime) (_ : 𝔫.comap (algebraMap N N₁) = 𝔪),
    TameCuspKummerAtData O e t F' N₁ 𝔫 ((algebraMap N N₁).comp (algebraMap O N))

section Descent

variable {O : Type u} [CommRing O] {e : ℕ} {N' N : Type u} [CommRing N'] [CommRing N]
  [Algebra O N'] [Algebra O N] [Algebra N' N] [IsScalarTower O N' N] {t : N'}
  {F' : Type u} [CommRing F'] [Algebra N F'] [Algebra N' F'] [IsScalarTower N' N F']
  {𝔪 : Ideal N}

/-- Forgetting `η = 1` and `dᵢ ∣ e`. -/
theorem IsTameCuspKummerAt.isCuspKummerAt {t : N} (h : IsTameCuspKummerAt O e t F' 𝔪) :
    IsCuspKummerAt O t F' 𝔪 := by
  obtain ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', _, hT, hX, hE', ht, r, d, hd, -, ⟨Φ⟩⟩ := h
  exact ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', _, _, hT, hX, hE', ht, ⟨1, isUnit_one, (one_mul _).symm⟩,
    r, d, hd, ⟨Φ⟩⟩

/-- Enlarging the bound `e` on the local degrees. -/
theorem IsTameCuspKummerAt.mono {e' : ℕ} (hee' : e ∣ e') {t : N}
    (h : IsTameCuspKummerAt O e t F' 𝔪) : IsTameCuspKummerAt O e' t F' 𝔪 := by
  obtain ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', _, hT, hX, hE', ht, r, d, hd, hde, ⟨Φ⟩⟩ := h
  exact ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', _, hT, hX, hE', ht, r, d, hd, fun i ↦ (hde i).trans hee',
    ⟨Φ⟩⟩

/-- **Descent of `IsTameCuspKummerAt` along an étale map `N' → N`** with
`N₁ ⊗_{N'} F' = N₁ ⊗_N F'`. -/
theorem IsTameCuspKummerAt.comap_of_compatibleSMul [Algebra.Etale N' N]
    (hc : ∀ (N₁ : Type u) [CommRing N₁] [Algebra N N₁] [Algebra N' N₁] [IsScalarTower N' N N₁],
      CompatibleSMul N' N N₁ F')
    (h : IsTameCuspKummerAt O e (algebraMap N' N t) F' 𝔪) :
    IsTameCuspKummerAt O e t F' (𝔪.comap (algebraMap N' N)) := by
  obtain ⟨N₁, _, _, _, 𝔫, _, h𝔫, h⟩ := h
  letI : Algebra N' N₁ := ((algebraMap N N₁).comp (algebraMap N' N)).toAlgebra
  haveI : IsScalarTower N' N N₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI := hc N₁
  have hf : (algebraMap N N₁).comp (algebraMap O N) = (algebraMap N' N₁).comp (algebraMap O N') :=
    RingHom.ext fun x ↦ by
      change algebraMap N N₁ (algebraMap O N x) =
        algebraMap N N₁ (algebraMap N' N (algebraMap O N' x))
      rw [← IsScalarTower.algebraMap_apply O N' N]
  refine ⟨N₁, inferInstance, inferInstance, Algebra.Etale.comp N' N N₁, 𝔫, inferInstance, ?_,
    (h.of_eq hf).comap⟩
  rw [IsScalarTower.algebraMap_eq N' N N₁, ← Ideal.comap_comap, h𝔫]

/-- **Descent of `IsTameCuspKummerAt` along a localization `N' → N = M⁻¹ N'`**. -/
theorem IsTameCuspKummerAt.comap_of_isLocalization (M : Submonoid N') [IsLocalization M N]
    [Algebra.Etale N' N] (h : IsTameCuspKummerAt O e (algebraMap N' N t) F' 𝔪) :
    IsTameCuspKummerAt O e t F' (𝔪.comap (algebraMap N' N)) :=
  h.comap_of_compatibleSMul fun N₁ _ _ _ _ ↦
    IsLocalization.tensorProduct_compatibleSMul (A := N) M N₁ F'

/-- **Transport of `IsTameCuspKummerAt` along an isomorphism `N' ≅ N`.** -/
theorem IsTameCuspKummerAt.comap_of_bijective (hb : Function.Bijective (algebraMap N' N))
    (h : IsTameCuspKummerAt O e (algebraMap N' N t) F' 𝔪) :
    IsTameCuspKummerAt O e t F' (𝔪.comap (algebraMap N' N)) :=
  haveI : Algebra.Etale N' N := RingHom.etale_algebraMap.mp (RingHom.Etale.of_bijective hb)
  h.comap_of_compatibleSMul fun _ _ _ _ _ ↦ CompatibleSMul.of_algebraMap_surjective _ _ hb.2

end Descent

section Norm

variable (O : Type u) [CommRing O] (e : ℕ) {N : Type u} [CommRing N] (t : N)
  (B : Type u) [CommRing B] [Algebra N B] (N₁ : Type u) [CommRing N₁] [Algebra N N₁]
  (𝔫 : Ideal N₁)

/-- The data of `IsCuspNormAt` over a fixed étale neighbourhood `N₁ ⊇ 𝔫`. -/
def CuspNormData (f : O →+* N₁) : Prop :=
  letI : Algebra O N₁ := f.toAlgebra
  CuspNormSplit O e (algebraMap N N₁ t) 𝔫 (N₁ ⊗[N] B)

/-- **The normalisation `B` of `N` in a cover is tamely Kummer at the cusp point `𝔪`** (the
normalisation-level predicate): étale-locally at `𝔪`, `N` is the cusp chart `O[X]` with `X ↦ t`
and `B` is a product of Kummer covers `O[X] → O[y]`, `X ↦ y ^ dᵢ`, `0 < dᵢ ∣ e`. -/
def IsCuspNormAt [Algebra O N] (𝔪 : Ideal N) : Prop :=
  ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : Algebra N N₁) (_ : Algebra.Etale N N₁) (𝔫 : Ideal N₁)
    (_ : 𝔫.IsPrime) (_ : 𝔫.comap (algebraMap N N₁) = 𝔪),
    CuspNormData O e t B N₁ 𝔫 ((algebraMap N N₁).comp (algebraMap O N))

variable {O e t B N₁ 𝔫}

/-- The data pass to an isomorphic normalisation. -/
lemma CuspNormData.of_algEquiv {B' : Type u} [CommRing B'] [Algebra N B'] (φ : B ≃ₐ[N] B')
    {f : O →+* N₁} (h : CuspNormData O e t B N₁ 𝔫 f) : CuspNormData O e t B' N₁ 𝔫 f :=
  letI : Algebra O N₁ := f.toAlgebra
  CuspNormSplit.of_algEquiv (Algebra.TensorProduct.congr AlgEquiv.refl φ).symm h

variable [IsDomain O] [IsDiscreteValuationRing O]

/-- **From the cover to its normalisation.** If `F'` is tamely Kummer at the cusp point, its
normalisation over `N` is (`CuspNormData`): normalisation commutes with étale base change, and the
normalisation of a cusp Kummer factor is `N₁ ⊗_{O[X]} O[y]` (`cuspFactorEquiv`). -/
theorem TameCuspKummerAtData.cuspNormData {F' : Type u} [CommRing F'] [Algebra N F']
    [Algebra.Etale N N₁] {f : O →+* N₁} (h : TameCuspKummerAtData O e t F' N₁ 𝔫 f) :
    CuspNormData O e t (integralClosure N F') N₁ 𝔫 f := by
  classical
  letI : Algebra O N₁ := f.toAlgebra
  obtain ⟨_, hT, hX, hE, ht, r, d, hd, hde, ⟨Φ⟩⟩ := h
  let Ψ₀ : N₁ ⊗[N] (integralClosure N F') ≃ₐ[N₁] integralClosure N₁ (N₁ ⊗[N] F') :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure N N₁ F')
      TensorProduct.toIntegralClosure_bijective_of_smooth
  let Ψ₃ : ∀ i, integralClosure N₁ (CuspFactor O (d i) N₁) ≃ₐ[N₁]
      CuspNormalFactor O (d i) N₁ := fun i ↦
    haveI : NeZero (d i) := ⟨(hd i).ne'⟩
    (cuspFactorEquiv (O := O) (d := d i) N₁).symm
  exact ⟨_, hT, hX, hE, ht, r, d, hd, hde, ⟨Ψ₀.trans (Φ.mapIntegralClosure.trans
    (integralClosurePiEquiv.trans (AlgEquiv.piCongrRight Ψ₃)))⟩⟩

/-- **`IsTameCuspKummerAt` ⇒ `IsCuspNormAt`** for any normalisation `B` of `N` in `F'`. -/
theorem IsTameCuspKummerAt.isCuspNormAt [Algebra O N] {F' : Type u} [CommRing F']
    [Algebra N F'] [Algebra B F'] [IsScalarTower N B F'] [IsIntegralClosure B N F']
    {𝔪 : Ideal N} (h : IsTameCuspKummerAt O e t F' 𝔪) : IsCuspNormAt O e t B 𝔪 := by
  obtain ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', h⟩ := h
  exact ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', h.cuspNormData.of_algEquiv
    (IsIntegralClosure.equiv N (integralClosure N F') F' B)⟩

end Norm

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
set_option maxHeartbeats 1000000 in
-- The many tensor product, localization and intermediate field structures make this slow.
/-- **Tame covers of the cusp chart are tamely Kummer** (the tame form of
`isCuspKummerAt_chart`, with the same hypotheses). Étale-locally at the cusp point, `L` is a
product of Kummer covers `t = y ^ e'`, `e' ∣ e`, of the étale chart `O[X] → N₁`, `X ↦ t`. -/
theorem isTameCuspKummerAt_chart [CharZero O] {ϖ : O} (hϖ : Irreducible ϖ) {ζ : 𝕂}
    (hζ : IsPrimitiveRoot ζ e) (L : Type u) [Field L] [Algebra 𝕂 L] [FiniteDimensional 𝕂 L]
    [IsGalois 𝕂 L] (hd : finrank 𝕂 L ∣ e) [Algebra O[X] L] [IsScalarTower O[X] 𝕂 L]
    [Algebra R L] [IsScalarTower O[X] R L]
    (B : Type u) [CommRing B] [Algebra R B] [Algebra B L] [IsScalarTower R B L]
    [IsIntegralClosure B R L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap R B) ≠ maximalIdeal R →
      Q.comap (algebraMap R B) ≠ Ideal.span {algebraMap O[X] R X} →
        Algebra.IsUnramifiedAt R Q) :
    IsTameCuspKummerAt O e (X : O[X]) L (cuspIdeal O) := by
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
  -- the chart `O[X] → N₁`, `X ↦ X` (`η = 1`), with all local degrees `e' ∣ e`
  letI algO : Algebra O N₁ := ((algebraMap O[X] N₁).comp (algebraMap O O[X])).toAlgebra
  haveI : IsScalarTower O O[X] N₁ := IsScalarTower.of_algebraMap_eq' rfl
  have hX : algebraMap O[X] N₁ X ∈ 𝔫 := by
    have := X_mem_cuspIdeal (O := O)
    rw [← h𝔫'] at this
    exact this
  exact ⟨N₁, inferInstance, inferInstance, inferInstance, 𝔫, inferInstance, h𝔫', inferInstance,
    inferInstance, rfl, inferInstance, hX, r, fun _ ↦ e', fun _ ↦ he'0, fun _ ↦ he', ⟨Ψ⟩⟩

end Chart

end SemistableReduction.Cusp
