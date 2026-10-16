/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.Galois
import TemperedFundamentalGroups.Tempered.BaseChangeEtale
import ContinuousKummerTheory.Curve.Etale

/-!
# Kummer classes on the tempered fundamental group

Let `U = Spec R` (more generally `[Spec R / A]`) be an affine curve in the Galois model of
`pi1` (`Pi1.Orbifold.GaloisData D`, with `R = D.R`, `A = D.A`). `continuous-kummer-theory` gives the
Kummer maps `κ_U : Γ(U, 𝒪^×) → H¹(π₁ᵉᵗ(U), μ_n)` and `H¹(π₁ᵉᵗ(U), Ẑ(1))`
(`KummerTheory.Curve.kummerMapEtale`). Pulling back along the comparison homomorphism
`temperedToEtale : Π^tp_U → π₁ᵉᵗ(U)` gives the **Kummer classes on the tempered fundamental group**
(the algebraic part of "Kummer theory on tempered coverings", roadmap item MR5, for MR14):

* `TemperedFundamentalGroups.Kummer.kummerMapTempered D O V hV n` and `kummerMapTemperedZHat`;
* `kummerMapTempered_galoisToTempered`: on the Galois elements `galoisToTempered σ`
  (`σ ∈ Aut_R(Ω)` preserving `V`), every representative of `κ^tp(u)` is the Kummer cocycle
  `σ ↦ σ(u^{1/n}) / u^{1/n}` up to a coboundary. This is the comparison of the tempered Kummer class
  with the Kummer classes of values (decomposition groups) used in [EtTh] Prop. 1.4(iii);
* `map_temperedPi1Map_kummerMapTempered`: naturality along maps of orbifolds
  (`temperedPi1Map`), via `temperedToEtale_temperedPi1Map`.

The Kummer classes of functions on genuinely tempered (infinite) coverings, e.g. the theta
function on `Ÿ`, are not treated here (they need rings of functions on tempered coverings).
-/

universe u

open groupCohomology AffOrbicurve KummerTheory KummerTheory.Curve

namespace TemperedFundamentalGroups

namespace Kummer

noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω]
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)

/-- The tempered fundamental group of `[Spec D.R / D.A]`. -/
abbrev TempPi : Type u := temperedPi1 O D.R D.A V hV

/-- `Π^tp → π₁ᵉᵗ ≅ Π_U` (Galois model). -/
def tempToPi : TempPi D O V hV →* Pi D :=
  (etaleToPi D).comp (temperedToEtale O D.R D.A V hV)

theorem continuous_tempToPi : Continuous (tempToPi D O V hV) :=
  (continuous_etaleToPi D).comp (continuous_temperedToEtale O D.R D.A V hV)

instance instMulDistribMulActionTempMu (n : ℕ) [NeZero n] :
    MulDistribMulAction (TempPi D O V hV) (Mu n Ω) :=
  MulDistribMulAction.compHom _ (tempToPi D O V hV)

instance instMulDistribMulActionTempZHatOne (K : Type*) [Field K] :
    MulDistribMulAction (TempPi D O V hV) (ZHatOne K Ω) :=
  MulDistribMulAction.compHom _ (tempToPi D O V hV)

/-- Pull-back `H¹(Π_U, μ_n) → H¹(Π^tp, μ_n)`. -/
abbrev toTempMu (n : ℕ) [NeZero n] :
    ContH1 (Pi D) (Mu n Ω) →* ContH1 (TempPi D O V hV) (Mu n Ω) :=
  ContH1.map (tempToPi D O V hV) (continuous_tempToPi D O V hV) (MonoidHom.id _) continuous_id
    fun _ _ => rfl

/-- Pull-back `H¹(Π_U, Ẑ(1)) → H¹(Π^tp, Ẑ(1))`. -/
abbrev toTempZHat (K : Type*) [Field K] :
    ContH1 (Pi D) (ZHatOne K Ω) →* ContH1 (TempPi D O V hV) (ZHatOne K Ω) :=
  ContH1.map (tempToPi D O V hV) (continuous_tempToPi D O V hV) (MonoidHom.id _) continuous_id
    fun _ _ => rfl

/-! ### Galois elements -/

omit [CharZero k] in
variable {D} in
/-- An `R`-algebra automorphism of `Ω` fixes the function field `L` of `R`. -/
theorem fixes_L (σ : Ω ≃ₐ[D.R] Ω) {x : Ω} (hx : x ∈ D.L) : σ x = x := by
  haveI := isFractionRing_coordRing t D.L
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (coordRing k t D.L) (⟨x, hx⟩ : D.L)
  have hx' : x = algebraMap D.R Ω a / algebraMap D.R Ω b := by
    have := congrArg (fun z : D.L => (z : Ω)) hab
    simp only [IntermediateField.coe_div] at this
    exact this.symm
  rw [hx', map_div₀, σ.commutes, σ.commutes]

variable {D} in
/-- `σ ∈ Aut_R(Ω)` as an element of `H` (it fixes `L`, hence lies in `H_L ≤ H`). -/
def galoisToH (σ : Ω ≃ₐ[D.R] Ω) : D.H :=
  ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => fixes_L σ (D.L.algebraMap_mem x),
    D.le (by
      rw [← Pi1.Orbifold.GaloisData.fixingSubgroup_L]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => fixes_L σ hx)⟩

omit [CharZero k] in
variable {D} in
@[simp]
theorem galoisToH_apply (σ : Ω ≃ₐ[D.R] Ω) (x : Ω) :
    ((galoisToH σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) x = σ x := rfl

omit [CharZero k] in
variable {D} in
theorem galoisToH_mem_HL (σ : Ω ≃ₐ[D.R] Ω) :
    ((galoisToH σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) ∈ D.HL := by
  rw [← Pi1.Orbifold.GaloisData.fixingSubgroup_L]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => fixes_L σ hx

omit [CharZero k] in
theorem galoisToEtale_eq (σ : Ω ≃ₐ[D.R] Ω) :
    galoisToEtale D.R D.A Ω σ = D.toEtalePi1 (galoisToH σ) := by
  apply Pi1.Orbifold.FibreAut.ext
  intro X f
  apply AlgHom.ext
  intro b
  rw [Pi1.Orbifold.GaloisData.toEtalePi1_app,
    Pi1.Orbifold.GaloisData.fibreSmul_of_mem D (galoisToH_mem_HL σ)]
  rfl

theorem etaleToPi_toEtalePi1 (h : D.H) : etaleToPi D (D.toEtalePi1 h) = (h : Pi D) := by
  have : D.toEtalePi1 h = D.equivPi1.symm (h : D.H ⧸ GaloisPi1.kernel D.H D.S) := by
    apply Pi1.Orbifold.FibreAut.ext
    intro X f
    rw [Pi1.Orbifold.GaloisData.equivPi1_symm_mk_app]
    rfl
  rw [this]
  exact D.equivPi1.apply_symm_apply _

theorem tempToPi_galoisToTempered (σ : decompositionGroup D.R V) :
    tempToPi D O V hV (galoisToTempered O D.R D.A hV σ) =
      ((galoisToH (σ : Ω ≃ₐ[D.R] Ω)) : Pi D) := by
  rw [tempToPi, MonoidHom.comp_apply, temperedToEtale_galoisToTempered, galoisToEtale_eq,
    etaleToPi_toEtalePi1]

variable [IsSepClosed Ω]

/-- **The `μ_n`-valued Kummer map on the tempered fundamental group**. -/
def kummerMapTempered (n : ℕ) [NeZero n] : units D →* ContH1 (TempPi D O V hV) (Mu n Ω) :=
  (toTempMu D O V hV n).comp (kummerMap D n)

/-- **The `Ẑ(1)`-valued Kummer map on the tempered fundamental group**. -/
def kummerMapTemperedZHat : units D →* ContH1 (TempPi D O V hV) (ZHatOne (F D) Ω) :=
  (toTempZHat D O V hV (F D)).comp (kummerMapZHat D)

/-- **The tempered Kummer class on Galois elements**: for every representative `c` of `κ^tp(u)`
there is `M ∈ μ_n` such that `c(σ) = σ(α)/α · σ(M)/M` for all Galois elements `σ`
(`α = u^{1/n}`): on the decomposition group, `κ^tp(u)` is the Kummer class of `u`. -/
theorem kummerMapTempered_galoisToTempered (n : ℕ) [NeZero n] (u : units D)
    (c : ContH1.cocycles (TempPi D O V hV) (Mu n Ω))
    (hc : ContH1.mk c = kummerMapTempered D O V hV n u) :
    ∃ M : Mu n Ω, ∀ σ : decompositionGroup D.R V,
      c (galoisToTempered O D.R D.A hV σ) =
        kummerFun (kummerRoot n (F D) Ω u) (smul_pow_of_pow_eq (kummerRoot_pow n (F D) Ω u))
          (toGalF D (galoisToH (σ : Ω ≃ₐ[D.R] Ω))) *
          (galoisToH (σ : Ω ≃ₐ[D.R] Ω) • M / M) := by
  -- a representative `c₀` of `κ_U(u)` on `Π_U`
  obtain ⟨c₀, hc₀⟩ := ContH1.mk_surjective (kummerMap D n u)
  -- `c₀` inflated to `H` is cohomologous to the explicit Kummer cocycle
  have hinf : ContH1.mk (ContH1.cocyclesMap (QuotientGroup.mk' _) QuotientGroup.continuous_mk
      (MonoidHom.id _) continuous_id (fun _ _ => rfl) c₀) =
      ContH1.mk (ContH1.cocyclesMap (toGalF D) continuous_toGalF (MonoidHom.id _) continuous_id
        (fun _ _ => rfl) (kummerCocycle (kummerRoot n (F D) Ω u)
          (smul_pow_of_pow_eq (kummerRoot_pow n (F D) Ω u)))) := by
    have := inflation_kummerMap n u
    rw [← hc₀] at this
    exact this
  rw [ContH1.mk_eq_mk_iff] at hinf
  obtain ⟨m, hm⟩ := hinf
  -- `c` is cohomologous to `c₀ ∘ tempToPi`
  have htemp : ContH1.mk c = ContH1.mk (ContH1.cocyclesMap (tempToPi D O V hV)
      (continuous_tempToPi D O V hV) (MonoidHom.id _) continuous_id (fun _ _ => rfl) c₀) := by
    rw [hc, kummerMapTempered, MonoidHom.comp_apply, ← hc₀]
    rfl
  rw [ContH1.mk_eq_mk_iff] at htemp
  obtain ⟨m', hm'⟩ := htemp
  refine ⟨m * m', fun σ => ?_⟩
  set h := galoisToH (σ : Ω ≃ₐ[D.R] Ω)
  have e1 := hm' (galoisToTempered O D.R D.A hV σ)
  have e2 := hm h
  have hact : ∀ x : Mu n Ω, galoisToTempered O D.R D.A hV σ • x = h • x := by
    intro x
    change (tempToPi D O V hV (galoisToTempered O D.R D.A hV σ)) • x = h • x
    rw [tempToPi_galoisToTempered]
    rfl
  simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply] at e1 e2
  rw [hact, tempToPi_galoisToTempered] at e1
  change h • m / m = c₀ (h : Pi D) / _ at e2
  rw [eq_div_iff_mul_eq'] at e1 e2
  rw [← e1, ← e2, smul_mul']
  simp only [div_eq_mul_inv, mul_inv, kummerCocycle_apply]
  ac_rfl

/-! ### Naturality along maps of orbifolds -/

section Naturality

variable {R' : Type u} [CommRing R'] [Algebra k R'] [Algebra D.R R'] [IsScalarTower k D.R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' k R']
  [Algebra R' Ω] [IsScalarTower k R' Ω] [IsScalarTower D.R R' Ω] (μ : OrbMap D.R D.A R' A')

/-- The composite `Π^tp([Spec R'/A']) → π₁ᵉᵗ([Spec R'/A']) → π₁ᵉᵗ([Spec R/A]) ≅ Π_U`. -/
def tempToPi' : temperedPi1 O R' A' V hV →* Pi D :=
  (etaleToPi D).comp ((etalePi1Map μ Ω).comp (temperedToEtale O R' A' V hV))

omit [IsSepClosed Ω] in
theorem tempToPi'_eq : tempToPi' D O V hV μ = (tempToPi D O V hV).comp (temperedPi1Map μ V hV) := by
  ext γ : 1
  simp only [tempToPi', tempToPi, MonoidHom.comp_apply, temperedToEtale_temperedPi1Map]

omit [IsSepClosed Ω] [IsScalarTower k D.R R'] in
theorem continuous_tempToPi' : Continuous (tempToPi' D O V hV μ) :=
  (continuous_etaleToPi D).comp ((continuous_etalePi1Map μ Ω).comp
    (continuous_temperedToEtale O R' A' V hV))

/-- **Naturality**: the pull-back of `κ^tp(u)` along `temperedPi1Map μ` is the pull-back of the
étale Kummer class along `etalePi1Map μ ∘ temperedToEtale` (with the action of
`Π^tp([Spec R'/A'])` on `μ_n` through `Π_U`). -/
theorem map_temperedPi1Map_kummerMapTempered (n : ℕ) [NeZero n] (u : units D) :
    letI : MulDistribMulAction (temperedPi1 O R' A' V hV) (Mu n Ω) :=
      MulDistribMulAction.compHom _ (tempToPi' D O V hV μ)
    ContH1.map (temperedPi1Map μ V hV) (continuous_temperedPi1Map μ V hV) (MonoidHom.id _)
        continuous_id (fun γ x => by
          change (tempToPi D O V hV (temperedPi1Map μ V hV γ)) • x = tempToPi' D O V hV μ γ • x
          rw [tempToPi'_eq]; rfl)
        (kummerMapTempered D O V hV n u) =
      ContH1.map (tempToPi' D O V hV μ) (continuous_tempToPi' D O V hV μ) (MonoidHom.id _)
        continuous_id (fun _ _ => rfl) (kummerMap D n u) := by
  rw [kummerMapTempered, MonoidHom.comp_apply]
  induction kummerMap D n u using ContH1.induction_on with
  | h c =>
    simp only [ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext γ
    simp only [ContH1.cocyclesMap_apply, MonoidHom.id_apply]
    rw [tempToPi'_eq]
    rfl

end Naturality

end

end Kummer

end TemperedFundamentalGroups
