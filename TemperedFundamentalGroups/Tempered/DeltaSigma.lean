/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Profinite.ProSigma
import TemperedFundamentalGroups.Tempered.GaloisSurjective

/-!
# The pro-`Σ` geometric tempered fundamental group `Δ^{tp,Σ}`

Let `Σ` be a set of primes (a predicate `P : ℕ → Prop`). For the geometric tempered fundamental
group `Δ^tp = Ker(Π^tp → G_k)` (`Kummer.deltaTemp`), [SemiAnbd] Remark 3.10.1 (`semianbd.txt`
l.2191–2213) defines the *pro-`Σ` tempered fundamental group* through the tempered coverings
dominated by combinatorial coverings of finite étale Galois coverings of `Σ`-integer degree, and
the proof of [SemiAnbd] Cor 3.11 (l.2259–2290) shows that its kernel `I^Σ = Ker(Δ ↠ Δ^Σ)` equals
`J^Σ = Ker(Δ → (Δ^∧)^Σ)`, the intersection of the open normal subgroups of `Σ`-integer index
(`Pi1.Profinite.sigmaKernel`). We take the group-theoretic description as the definition:

* **`Kummer.deltaTempSigma P`** `= Δ^tp ⧸ sigmaKernel P Δ^tp` (`Pi1.Profinite.MaxProSigma`), with
  the quotient topology;
* `Kummer.sigmaKerTemp P`: the `Σ`-kernel of `Δ^tp` as a subgroup of `Π^tp`; it is **normal in
  `Π^tp`** (`sigmaKerTemp_normal`: conjugation by `Π^tp` is a continuous automorphism of the normal
  subgroup `Δ^tp`, and the `Σ`-kernel is characteristic, `sigmaKernel_map_continuousMulEquiv`);
* **`Kummer.piTempSigma P`** `= Π^tp ⧸ J^Σ`, with `deltaTempSigmaToPi : Δ^{tp,Σ} → Π^tp ⧸ J^Σ`
  injective (`deltaTempSigmaToPi_injective`), onto the kernel of `Π^tp ⧸ J^Σ → G_k`
  (`range_deltaTempSigmaToPi`), and `Π^tp ⧸ J^Σ ↠ G_k` at a base point over a rational point
  (`piTempSigmaToGk_surjective`): the exact sequence `1 → Δ^{tp,Σ} → Π^tp/J^Σ → G_k → 1`;
* functoriality in isomorphisms (the "compatible with `γ`" of the proof of [SemiAnbd] Cor 3.11):
  **`maxProSigmaCongr`** (`G ≃ₜ* H` induces `G^Σ ≃ₜ* H^Σ`, `maxProSigmaCongr_mk`, `_refl`, `_trans`)
  and `ContinuousMulEquiv.subgroupCongr'` (an isomorphism mapping `Δ₁` onto `Δ₂` restricts), so that
  an isomorphism `Π^tp[α] ≃ₜ* Π^tp[β]` preserving the geometric subgroups induces
  `Δ^{tp,Σ}[α] ≃ₜ* Δ^{tp,Σ}[β]` (`deltaTempSigmaCongr`).

The comparison `Δ^{tp,Σ} ≃ₜ* π^temp(G^Σ)` (MR13 C1, the rest of the proof of [SemiAnbd] Cor 3.11)
is not part of this file.
-/

universe u

open Pi1.Profinite

namespace TemperedFundamentalGroups

section Generic

variable (P : ℕ → Prop) {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The preimage of an open normal subgroup of `Σ`-index under a continuous surjective
homomorphism is an open normal subgroup of `Σ`-index. -/
theorem isSigmaOpenNormal_comap {f : G →* H} (hf : Continuous f) (hs : Function.Surjective f)
    {N : Subgroup H} (hN : IsSigmaOpenNormal P H N) : IsSigmaOpenNormal P G (N.comap f) := by
  refine ⟨hN.1.preimage hf, @Subgroup.Normal.comap _ _ _ _ _ hN.2.1 f, ?_⟩
  rw [Subgroup.index_comap_of_surjective N hs]
  exact hN.2.2

/-- A continuous surjective homomorphism maps the `Σ`-kernel into the `Σ`-kernel. -/
theorem sigmaKernel_le_comap {f : G →* H} (hf : Continuous f) (hs : Function.Surjective f) :
    sigmaKernel P G ≤ (sigmaKernel P H).comap f := fun _ hg =>
  mem_sigmaKernel_iff.2 fun N hN =>
    mem_sigmaKernel_iff.1 hg (N.comap f) (isSigmaOpenNormal_comap P hf hs hN)

/-- **The `Σ`-kernel is characteristic**: a topological group isomorphism maps it onto the
`Σ`-kernel. -/
theorem sigmaKernel_map_continuousMulEquiv (e : G ≃ₜ* H) :
    (sigmaKernel P G).map (e : G →* H) = sigmaKernel P H := by
  refine le_antisymm ?_ fun h hh => ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact sigmaKernel_le_comap P e.continuous e.surjective
  · refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
    exact sigmaKernel_le_comap P (f := (e.symm : H →* G)) e.symm.continuous e.symm.surjective hh

/-- **Functoriality of the maximal pro-`Σ` quotient in isomorphisms**: `G ≃ₜ* H` induces
`G^Σ ≃ₜ* H^Σ`. -/
noncomputable def maxProSigmaCongr [IsTopologicalGroup G] [IsTopologicalGroup H] (e : G ≃ₜ* H) :
    MaxProSigma P G ≃ₜ* MaxProSigma P H where
  toMulEquiv := QuotientGroup.congr _ _ e.toMulEquiv (sigmaKernel_map_continuousMulEquiv P e)
  continuous_toFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact (MaxProSigma.continuous_mk (P := P) (G := H)).comp e.continuous
  continuous_invFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact (MaxProSigma.continuous_mk (P := P) (G := G)).comp e.symm.continuous

@[simp]
theorem maxProSigmaCongr_mk [IsTopologicalGroup G] [IsTopologicalGroup H] (e : G ≃ₜ* H) (g : G) :
    maxProSigmaCongr P e (MaxProSigma.mk g) = MaxProSigma.mk (e g) := rfl

theorem maxProSigmaCongr_refl [IsTopologicalGroup G] :
    maxProSigmaCongr P (ContinuousMulEquiv.refl G) = ContinuousMulEquiv.refl _ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

theorem maxProSigmaCongr_trans {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup G]
    [IsTopologicalGroup H] [IsTopologicalGroup K] (e : G ≃ₜ* H) (e' : H ≃ₜ* K) :
    maxProSigmaCongr P (e.trans e') = (maxProSigmaCongr P e).trans (maxProSigmaCongr P e') := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

/-- An isomorphism of topological groups mapping a subgroup `A` onto `B` restricts to
`A ≃ₜ* B`. -/
noncomputable def ContinuousMulEquiv.subgroupCongr' (e : G ≃ₜ* H) {A : Subgroup G}
    {B : Subgroup H} (h : A.map (e : G →* H) = B) : A ≃ₜ* B where
  toMulEquiv := ((e.toMulEquiv.subgroupMap A).trans (MulEquiv.subgroupCongr h))
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem ContinuousMulEquiv.coe_subgroupCongr'_apply (e : G ≃ₜ* H) {A : Subgroup G}
    {B : Subgroup H} (h : A.map (e : G →* H) = B) (a : A) :
    ((ContinuousMulEquiv.subgroupCongr' e h a : B) : H) = e a := rfl

/-- Conjugation by `g` as a continuous automorphism of a normal subgroup. -/
noncomputable def conjNormalCont [IsTopologicalGroup G] (A : Subgroup G) [A.Normal] (g : G) :
    A ≃ₜ* A where
  toMulEquiv := MulAut.conjNormal g
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const)

@[simp]
theorem coe_conjNormalCont_apply [IsTopologicalGroup G] (A : Subgroup G) [A.Normal] (g : G)
    (a : A) : ((conjNormalCont A g a : A) : G) = g * a * g⁻¹ := rfl

/-- **The `Σ`-kernel of a normal subgroup is normal in the ambient group.** -/
theorem sigmaKernel_map_subtype_normal [IsTopologicalGroup G] (A : Subgroup G) [A.Normal] :
    ((sigmaKernel P A).map A.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hx
  have h := sigmaKernel_map_continuousMulEquiv P (conjNormalCont A g)
  have hmem : conjNormalCont A g a ∈ sigmaKernel P A := h ▸ ⟨a, ha, rfl⟩
  exact ⟨_, hmem, rfl⟩

end Generic

namespace Kummer

noncomputable section

open KummerTheory KummerTheory.Curve AffOrbicurve IsLocalRing

variable (P : ℕ → Prop)
variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  (O : ValuationSubring k) (V : ValuationSubring Ω) (hV : V.comap (algebraMap k Ω) = O)

/-- **The pro-`Σ` geometric tempered fundamental group** `Δ^{tp,Σ} = Δ^tp ⧸ J^Σ`, `J^Σ` the
intersection of the open normal subgroups of `Σ`-integer index of `Δ^tp` ([SemiAnbd] Rem 3.10.1
and the equality `I^Σ = J^Σ` of the proof of Cor 3.11). -/
abbrev deltaTempSigma : Type u := MaxProSigma P (deltaTemp D O V hV)

/-- The `Σ`-kernel `J^Σ` of `Δ^tp`, as a subgroup of `Π^tp`. -/
def sigmaKerTemp : Subgroup (TempPi D O V hV) :=
  (sigmaKernel P (deltaTemp D O V hV)).map (deltaTemp D O V hV).subtype

/-- **`J^Σ` is normal in `Π^tp`.** -/
instance sigmaKerTemp_normal : (sigmaKerTemp P D O V hV).Normal :=
  sigmaKernel_map_subtype_normal P _

theorem sigmaKerTemp_le_deltaTemp : sigmaKerTemp P D O V hV ≤ deltaTemp D O V hV := by
  rintro _ ⟨a, -, rfl⟩
  exact a.2

/-- **`Π^tp ⧸ J^Σ`**, the extension of `G_k` by `Δ^{tp,Σ}`. -/
abbrev piTempSigma : Type u := TempPi D O V hV ⧸ sigmaKerTemp P D O V hV

/-- The quotient map `Π^tp → Π^tp ⧸ J^Σ`. -/
abbrev piTempSigmaMk : TempPi D O V hV →* piTempSigma P D O V hV := QuotientGroup.mk' _

/-- The map `Π^tp ⧸ J^Σ → G_k`. -/
def piTempSigmaToGk : piTempSigma P D O V hV →* Gk k Ω :=
  QuotientGroup.lift _ ((piToGk D).comp (tempToPi D O V hV))
    (sigmaKerTemp_le_deltaTemp P D O V hV)

@[simp]
theorem piTempSigmaToGk_mk (γ : TempPi D O V hV) :
    piTempSigmaToGk P D O V hV (piTempSigmaMk P D O V hV γ) = piToGk D (tempToPi D O V hV γ) :=
  rfl

/-- The map `Δ^{tp,Σ} → Π^tp ⧸ J^Σ`. -/
def deltaTempSigmaToPi : deltaTempSigma P D O V hV →* piTempSigma P D O V hV :=
  QuotientGroup.map _ _ (deltaTemp D O V hV).subtype fun a ha => ⟨a, ha, rfl⟩

@[simp]
theorem deltaTempSigmaToPi_mk (a : deltaTemp D O V hV) :
    deltaTempSigmaToPi P D O V hV (MaxProSigma.mk a) = piTempSigmaMk P D O V hV a := rfl

theorem continuous_deltaTempSigmaToPi : Continuous (deltaTempSigmaToPi P D O V hV) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    (continuous_quot_mk.comp continuous_subtype_val)

/-- **`Δ^{tp,Σ} → Π^tp ⧸ J^Σ` is injective.** -/
theorem deltaTempSigmaToPi_injective : Function.Injective (deltaTempSigmaToPi P D O V hV) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H a =>
  have h1 : (piTempSigmaMk P D O V hV a) = 1 := hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨b, hb, hba⟩ := h1
  change (QuotientGroup.mk a : deltaTempSigma P D O V hV) = 1
  rw [QuotientGroup.eq_one_iff, ← Subtype.ext hba]
  exact hb

/-- **The image of `Δ^{tp,Σ}` is the kernel of `Π^tp ⧸ J^Σ → G_k`.** -/
theorem range_deltaTempSigmaToPi :
    (deltaTempSigmaToPi P D O V hV).range = (piTempSigmaToGk P D O V hV).ker := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H γ =>
  constructor
  · rintro ⟨y, hy⟩
    induction y using QuotientGroup.induction_on with
    | H a =>
    rw [MonoidHom.mem_ker, ← hy]
    exact a.2
  · intro h
    exact ⟨MaxProSigma.mk ⟨γ, h⟩, rfl⟩

variable (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)]
  (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)
  (hHL : D.HL = D.H) (hVA : V ≤ A)
  [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]

include hrat hk hkres hVA hHL in
/-- **`Π^tp ⧸ J^Σ ↠ G_k`** at a base point over a rational point
(`piToGk_tempToPi_surjective`): with `deltaTempSigmaToPi_injective` and
`range_deltaTempSigmaToPi` the exact sequence `1 → Δ^{tp,Σ} → Π^tp/J^Σ → G_k → 1`. -/
theorem piTempSigmaToGk_surjective : Function.Surjective (piTempSigmaToGk P D O V hV) := by
  intro g
  obtain ⟨γ, hγ⟩ := piToGk_tempToPi_surjective D O V hV A hk hkres hrat hHL hVA g
  exact ⟨piTempSigmaMk P D O V hV γ, hγ⟩

end

end Kummer

section Congr

variable (P : ℕ → Prop) {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]

/-- **An isomorphism of tempered groups preserving the geometric subgroups induces an
isomorphism of their maximal pro-`Σ` quotients** (the compatibility with `γ` in the proof of
[SemiAnbd] Cor 3.11). Applied to `Δ = Kummer.deltaTemp …` it gives
`Δ^{tp,Σ}[α] ≃ₜ* Δ^{tp,Σ}[β]` (`Kummer.deltaTempSigma`). -/
noncomputable def deltaTempSigmaCongr (γ : G₁ ≃ₜ* G₂) {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂}
    (h : Δ₁.map (γ : G₁ →* G₂) = Δ₂) : MaxProSigma P Δ₁ ≃ₜ* MaxProSigma P Δ₂ :=
  maxProSigmaCongr P (ContinuousMulEquiv.subgroupCongr' γ h)

@[simp]
theorem deltaTempSigmaCongr_mk (γ : G₁ ≃ₜ* G₂) {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂}
    (h : Δ₁.map (γ : G₁ →* G₂) = Δ₂) (a : Δ₁) :
    deltaTempSigmaCongr P γ h (MaxProSigma.mk a) =
      MaxProSigma.mk (ContinuousMulEquiv.subgroupCongr' γ h a) := rfl

end Congr

end TemperedFundamentalGroups
