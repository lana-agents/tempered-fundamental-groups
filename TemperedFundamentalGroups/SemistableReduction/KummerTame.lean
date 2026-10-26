/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerTateChartTransfer

/-!
# Tame Kummer covers of nodes with the given coordinates, at the level of the normalisation

(MR12 T2 S5.0.) `IsKummerAt ϖ n u v F' 𝔪` (`KummerNode`) allows the étale-local node coordinates
`u₁ = η u`, `v₁ = η' v` to differ from the given ones by units, and records no bound on the local
degrees `dᵢ`. The covers produced by S4 (`NodeCover.isKummerAt_of_etale` and its consumers) are
better: `η = η' = 1` and `dᵢ ∣ M'` for the tame part `M'` of the thickness `n = q M'`. The formal
Kummer form of an admissible covering (`Admissible.Covering`, split with respect to the given
coordinates) needs exactly this, so we record it in a separate predicate (lead decision D4 after
continuation 28: `IsKummerAt` is unchanged):

* **`IsTameKummerAt ϖ n M' u v F' 𝔪`**: there are an étale `N`-algebra `N₁`, a prime `𝔫` over `𝔪`
  containing `u, v`, such that `O[u, v]/(uv − ϖⁿ) → N₁`, `u ↦ u`, `v ↦ v` is étale, and an
  `N₁`-algebra isomorphism `N₁ ⊗_N F' ≅ ∏ᵢ N₁ ⊗_{O[u,v]/(uv − ϖⁿ)} Frac (O[w,z]/(wz − ϖ^{mᵢ}))`
  (`u ↦ w^{dᵢ}`, `v ↦ z^{dᵢ}`, `mᵢ dᵢ = n`, `dᵢ ∣ M'`). It implies `IsKummerAt`
  (`IsTameKummerAt.isKummerAt`) and descends along étale maps (`IsTameKummerAt.comap_of_*`,
  as `IsKummerAt.comap_of_*`).
* **`IsKummerNormAt ϖ n M' u v B 𝔪`** (the normalisation-level predicate): the same with the
  normalisation `B` of `N` in `F'` and the normalised factors
  `N₁ ⊗_{O[u,v]/(uv − ϖⁿ)} O[w,z]/(wz − ϖ^{mᵢ})` (`KummerNodeFactor`).
  **`IsTameKummerAt.isKummerNormAt`**: normalisation commutes with étale base change and the
  normalisation of a Kummer factor is the Kummer node (`kummerFactorEquiv`), exactly as in
  `IsKummerAt.isAnnulusAt`.
-/

universe u

open TensorProduct

namespace SemistableReduction

section Split

variable {O : Type u} [CommRing O] (ϖ : O) (n M' : ℕ) {N₁ : Type u} [CommRing N₁] [Algebra O N₁]
  (u₁ v₁ : N₁) (𝔫 : Ideal N₁) (X : Type u) [CommRing X] [Algebra N₁ X]

/-- The splitting of an `N₁`-algebra `X` into Kummer factors over the node chart `u₁, v₁` of
`N₁` (`u₁ v₁ = ϖⁿ`, étale), with local degrees `dᵢ ∣ M'`. -/
def KummerSplit : Prop :=
  ∃ (huv : u₁ * v₁ = algebraMap O N₁ (ϖ ^ n)),
    (Node.lift _ _ huv).toRingHom.Etale ∧ u₁ ∈ 𝔫 ∧ v₁ ∈ 𝔫 ∧
    ∃ (r : ℕ) (m d : Fin r → ℕ) (_ : ∀ i, 0 < d i) (_ : ∀ i, d i ∣ M')
      (hmd : ∀ i, m i * d i = n),
      Nonempty (X ≃ₐ[N₁] ∀ i, @KummerFactor O _ (ϖ ^ m i) (d i) N₁ _
        (nodeAlgebra N₁ (ϖ ^ m i) (d i) (by rw [← pow_mul, hmd i]; exact huv)))

/-- The splitting of an `N₁`-algebra `X` into normalised Kummer factors (Kummer nodes) over the
node chart `u₁, v₁` of `N₁`, with local degrees `dᵢ ∣ M'`. -/
def KummerNodeSplit : Prop :=
  ∃ (huv : u₁ * v₁ = algebraMap O N₁ (ϖ ^ n)),
    (Node.lift _ _ huv).toRingHom.Etale ∧ u₁ ∈ 𝔫 ∧ v₁ ∈ 𝔫 ∧
    ∃ (r : ℕ) (m d : Fin r → ℕ) (_ : ∀ i, 0 < d i) (_ : ∀ i, d i ∣ M')
      (hmd : ∀ i, m i * d i = n),
      Nonempty (X ≃ₐ[N₁] ∀ i, @KummerNodeFactor O _ (ϖ ^ m i) (d i) N₁ _
        (nodeAlgebra N₁ (ϖ ^ m i) (d i) (by rw [← pow_mul, hmd i]; exact huv)))

variable {ϖ n M' u₁ v₁ 𝔫 X}

lemma KummerSplit.of_algEquiv {X' : Type u} [CommRing X'] [Algebra N₁ X'] (e : X' ≃ₐ[N₁] X)
    (h : KummerSplit ϖ n M' u₁ v₁ 𝔫 X) : KummerSplit ϖ n M' u₁ v₁ 𝔫 X' := by
  obtain ⟨huv, het, hu, hv, r, m, d, hd, hdM, hmd, ⟨Φ⟩⟩ := h
  exact ⟨huv, het, hu, hv, r, m, d, hd, hdM, hmd, ⟨e.trans Φ⟩⟩

lemma KummerNodeSplit.of_algEquiv {X' : Type u} [CommRing X'] [Algebra N₁ X']
    (e : X' ≃ₐ[N₁] X) (h : KummerNodeSplit ϖ n M' u₁ v₁ 𝔫 X) :
    KummerNodeSplit ϖ n M' u₁ v₁ 𝔫 X' := by
  obtain ⟨huv, het, hu, hv, r, m, d, hd, hdM, hmd, ⟨Φ⟩⟩ := h
  exact ⟨huv, het, hu, hv, r, m, d, hd, hdM, hmd, ⟨e.trans Φ⟩⟩

end Split

section Data

variable {O : Type u} [CommRing O] (ϖ : O) (n M' : ℕ) {N : Type u} [CommRing N] (u v : N)
  (F' : Type u) [CommRing F'] [Algebra N F'] (N₁ : Type u) [CommRing N₁] [Algebra N N₁]
  (𝔫 : Ideal N₁)

/-- The data of `IsTameKummerAt` over a fixed étale neighbourhood `N₁ ⊇ 𝔫`, with the structure map
`f : O → N₁` as a variable. -/
def TameKummerAtData (f : O →+* N₁) : Prop :=
  letI : Algebra O N₁ := f.toAlgebra
  KummerSplit ϖ n M' (algebraMap N N₁ u) (algebraMap N N₁ v) 𝔫 (N₁ ⊗[N] F')

variable {ϖ n M' u v F' N₁ 𝔫}

lemma TameKummerAtData.of_eq {f g : O →+* N₁} (hfg : f = g)
    (h : TameKummerAtData ϖ n M' u v F' N₁ 𝔫 f) : TameKummerAtData ϖ n M' u v F' N₁ 𝔫 g :=
  hfg ▸ h

/-- Forgetting `η = η' = 1` and `dᵢ ∣ M'`. -/
lemma TameKummerAtData.kummerAtData {f : O →+* N₁} (h : TameKummerAtData ϖ n M' u v F' N₁ 𝔫 f) :
    KummerAtData ϖ n u v F' N₁ 𝔫 f := by
  letI : Algebra O N₁ := f.toAlgebra
  obtain ⟨huv, het, hu, hv, r, m, d, hd, -, hmd, ⟨Φ⟩⟩ := h
  exact ⟨_, _, huv, het, hu, hv, ⟨1, 1, isUnit_one, isUnit_one, (one_mul _).symm,
    (one_mul _).symm⟩, r, m, d, hd, hmd, ⟨Φ⟩⟩

/-- Descent of the data along `N' → N` when `N₁ ⊗_{N'} F' = N₁ ⊗_N F'`. -/
lemma TameKummerAtData.comap {N' : Type u} [CommRing N'] [Algebra N' N] [Algebra N' F']
    [IsScalarTower N' N F'] [Algebra N' N₁] [IsScalarTower N' N N₁]
    [CompatibleSMul N' N N₁ F'] {u v : N'} {f : O →+* N₁}
    (h : TameKummerAtData ϖ n M' (algebraMap N' N u) (algebraMap N' N v) F' N₁ 𝔫 f) :
    TameKummerAtData ϖ n M' u v F' N₁ 𝔫 f := by
  letI : Algebra O N₁ := f.toAlgebra
  have eu : algebraMap N N₁ (algebraMap N' N u) = algebraMap N' N₁ u :=
    (IsScalarTower.algebraMap_apply N' N N₁ u).symm
  have ev : algebraMap N N₁ (algebraMap N' N v) = algebraMap N' N₁ v :=
    (IsScalarTower.algebraMap_apply N' N N₁ v).symm
  unfold TameKummerAtData at h ⊢
  rw [eu, ev] at h
  exact h.of_algEquiv (Algebra.TensorProduct.equivOfCompatibleSMul N N' N₁ N₁ F')

end Data

variable {O : Type u} [CommRing O]

/-- **The cover `F'` of `N` is tamely Kummer at `𝔪` with respect to the coordinates `u, v`**:
`IsKummerAt` with `u₁ = u`, `v₁ = v` and local degrees dividing `M'`. -/
def IsTameKummerAt (ϖ : O) (n M' : ℕ) {N : Type u} [CommRing N] [Algebra O N] (u v : N)
    (F' : Type u) [CommRing F'] [Algebra N F'] (𝔪 : Ideal N) : Prop :=
  ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : Algebra N N₁) (_ : Algebra.Etale N N₁) (𝔫 : Ideal N₁)
    (_ : 𝔫.IsPrime) (_ : 𝔫.comap (algebraMap N N₁) = 𝔪),
    TameKummerAtData ϖ n M' u v F' N₁ 𝔫 ((algebraMap N N₁).comp (algebraMap O N))

section Descent

variable {ϖ : O} {n M' : ℕ} {N' N : Type u} [CommRing N'] [CommRing N]
  [Algebra O N'] [Algebra O N] [Algebra N' N] [IsScalarTower O N' N] {u v : N'}
  {F' : Type u} [CommRing F'] [Algebra N F'] [Algebra N' F'] [IsScalarTower N' N F']
  {𝔪 : Ideal N}

theorem IsTameKummerAt.isKummerAt {u v : N} (h : IsTameKummerAt ϖ n M' u v F' 𝔪) :
    IsKummerAt ϖ n u v F' 𝔪 := by
  obtain ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', h⟩ := h
  exact (isKummerAt_iff ϖ n u v F' 𝔪).2 ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', h.kummerAtData⟩

/-- **Descent of `IsTameKummerAt` along an étale map `N' → N`** with
`N₁ ⊗_{N'} F' = N₁ ⊗_N F'`. -/
theorem IsTameKummerAt.comap_of_compatibleSMul [Algebra.Etale N' N]
    (hc : ∀ (N₁ : Type u) [CommRing N₁] [Algebra N N₁] [Algebra N' N₁] [IsScalarTower N' N N₁],
      CompatibleSMul N' N N₁ F')
    (h : IsTameKummerAt ϖ n M' (algebraMap N' N u) (algebraMap N' N v) F' 𝔪) :
    IsTameKummerAt ϖ n M' u v F' (𝔪.comap (algebraMap N' N)) := by
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

/-- **Descent of `IsTameKummerAt` along a localization `N' → N = M⁻¹ N'`**. -/
theorem IsTameKummerAt.comap_of_isLocalization (M : Submonoid N') [IsLocalization M N]
    [Algebra.Etale N' N]
    (h : IsTameKummerAt ϖ n M' (algebraMap N' N u) (algebraMap N' N v) F' 𝔪) :
    IsTameKummerAt ϖ n M' u v F' (𝔪.comap (algebraMap N' N)) :=
  h.comap_of_compatibleSMul fun N₁ _ _ _ _ ↦
    IsLocalization.tensorProduct_compatibleSMul (A := N) M N₁ F'

/-- **Transport of `IsTameKummerAt` along an isomorphism `N' ≅ N`.** -/
theorem IsTameKummerAt.comap_of_bijective (hb : Function.Bijective (algebraMap N' N))
    (h : IsTameKummerAt ϖ n M' (algebraMap N' N u) (algebraMap N' N v) F' 𝔪) :
    IsTameKummerAt ϖ n M' u v F' (𝔪.comap (algebraMap N' N)) :=
  haveI : Algebra.Etale N' N := RingHom.etale_algebraMap.mp (RingHom.Etale.of_bijective hb)
  h.comap_of_compatibleSMul fun _ _ _ _ _ ↦ CompatibleSMul.of_algebraMap_surjective _ _ hb.2

end Descent

section Norm

variable (ϖ : O) (n M' : ℕ) {N : Type u} [CommRing N] (u v : N)
  (B : Type u) [CommRing B] [Algebra N B] (N₁ : Type u) [CommRing N₁] [Algebra N N₁]
  (𝔫 : Ideal N₁)

/-- The data of `IsKummerNormAt` over a fixed étale neighbourhood `N₁ ⊇ 𝔫`. -/
def KummerNormData (f : O →+* N₁) : Prop :=
  letI : Algebra O N₁ := f.toAlgebra
  KummerNodeSplit ϖ n M' (algebraMap N N₁ u) (algebraMap N N₁ v) 𝔫 (N₁ ⊗[N] B)

/-- **The normalisation `B` of `N` in a cover is tamely Kummer at `𝔪`** (the normalisation-level
predicate): étale-locally at `𝔪`, `N` is the node `O[u, v]/(uv − ϖⁿ)` with the given coordinates
and `B` is a product of Kummer nodes `O[w, z]/(wz − ϖ^{mᵢ})`, `u = w^{dᵢ}`, `v = z^{dᵢ}`,
`dᵢ ∣ M'`. -/
def IsKummerNormAt [Algebra O N] (𝔪 : Ideal N) : Prop :=
  ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : Algebra N N₁) (_ : Algebra.Etale N N₁) (𝔫 : Ideal N₁)
    (_ : 𝔫.IsPrime) (_ : 𝔫.comap (algebraMap N N₁) = 𝔪),
    KummerNormData ϖ n M' u v B N₁ 𝔫 ((algebraMap N N₁).comp (algebraMap O N))

variable {ϖ n M' u v B N₁ 𝔫}

/-- The data pass to an isomorphic normalisation. -/
lemma KummerNormData.of_algEquiv {B' : Type u} [CommRing B'] [Algebra N B'] (e : B ≃ₐ[N] B')
    {f : O →+* N₁} (h : KummerNormData ϖ n M' u v B N₁ 𝔫 f) :
    KummerNormData ϖ n M' u v B' N₁ 𝔫 f :=
  letI : Algebra O N₁ := f.toAlgebra
  KummerNodeSplit.of_algEquiv (Algebra.TensorProduct.congr AlgEquiv.refl e).symm h

variable [IsDomain O] [IsIntegrallyClosed O]

/-- **From the cover to its normalisation.** If `F'` is tamely Kummer at `𝔪`, its normalisation
`B` over `N` is (`IsKummerNormAt`): normalisation commutes with étale base change, and the
normalisation of a Kummer factor is the Kummer node (`kummerFactorEquiv`). -/
theorem TameKummerAtData.kummerNormData (hϖ : ϖ ≠ 0) {F' : Type u} [CommRing F'] [Algebra N F']
    [Algebra.Etale N N₁] {f : O →+* N₁} (h : TameKummerAtData ϖ n M' u v F' N₁ 𝔫 f) :
    KummerNormData ϖ n M' u v (integralClosure N F') N₁ 𝔫 f := by
  classical
  letI : Algebra O N₁ := f.toAlgebra
  obtain ⟨huv, het, hu, hv, r, m, d, hd, hdM, hmd, ⟨e⟩⟩ := h
  have hi : ∀ i, algebraMap N N₁ u * algebraMap N N₁ v = algebraMap O N₁ ((ϖ ^ m i) ^ d i) :=
    fun i ↦ by rw [← pow_mul, hmd i]; exact huv
  have hfi : ∀ i, (Node.lift _ _ (hi i)).toRingHom.Etale := fun i ↦
    lift_etale_of_eq (by rw [← pow_mul, hmd i]) huv (hi i) het
  let Ψ₀ : N₁ ⊗[N] (integralClosure N F') ≃ₐ[N₁] integralClosure N₁ (N₁ ⊗[N] F') :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure N N₁ F')
      TensorProduct.toIntegralClosure_bijective_of_smooth
  let Ψ₃ : ∀ i, integralClosure N₁
      (@KummerFactor O _ (ϖ ^ m i) (d i) N₁ _ (nodeAlgebra N₁ _ _ (hi i))) ≃ₐ[N₁]
      @KummerNodeFactor O _ (ϖ ^ m i) (d i) N₁ _ (nodeAlgebra N₁ _ _ (hi i)) := fun i ↦
    letI := nodeAlgebra N₁ (ϖ ^ m i) (d i) (hi i)
    haveI : Algebra.Etale (Node O ((ϖ ^ m i) ^ d i)) N₁ := hfi i
    (kummerFactorEquiv (c := ϖ ^ m i) (d := d i) N₁ (pow_ne_zero _ hϖ) (hd i)).symm
  exact ⟨huv, het, hu, hv, r, m, d, hd, hdM, hmd, ⟨Ψ₀.trans (e.mapIntegralClosure.trans
    (integralClosurePiEquiv.trans (AlgEquiv.piCongrRight Ψ₃)))⟩⟩

/-- **`IsTameKummerAt` ⇒ `IsKummerNormAt`** for any normalisation `B` of `N` in `F'`. -/
theorem IsTameKummerAt.isKummerNormAt (hϖ : ϖ ≠ 0) [Algebra O N] {F' : Type u} [CommRing F']
    [Algebra N F'] [Algebra B F'] [IsScalarTower N B F'] [IsIntegralClosure B N F']
    {𝔪 : Ideal N} (h : IsTameKummerAt ϖ n M' u v F' 𝔪) : IsKummerNormAt ϖ n M' u v B 𝔪 := by
  obtain ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', h⟩ := h
  exact ⟨N₁, _, _, hE, 𝔫, h𝔫, h𝔫', (h.kummerNormData hϖ).of_algEquiv
    (IsIntegralClosure.equiv N (integralClosure N F') F' B)⟩

end Norm

end SemistableReduction
