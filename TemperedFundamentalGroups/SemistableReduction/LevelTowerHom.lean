/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalPatchHom
import TemperedFundamentalGroups.SemistableReduction.LevelTowerFst
import TemperedFundamentalGroups.SemistableReduction.EtaleNil

/-!
# Maps of the patched levels (Blueprint §12.8, M2.3)

MR12 I3, generic core: maps of the patched levels. For two admissible coverings `cov₀`, `cov₀'`
of the same special chart and a map `φ : cov₀.C → cov₀'.C` of the special-fibre coverings:

* `LevelTower.pMapOf`: for formally étale lifts `P`, `P'` of `C_f`, `C'_f` (`σ : P/JP ≃ C_f`), the
  unique lift `P → P'` of `φ_f` (`σ_pMapOf`, uniqueness `eq_pMapOf`, `pMapOf_id`, `pMapOf_comp`);
  `LevelTower.levelMapOf`: the induced map of patched algebras
  (`FormalPatchLevel.patchMap`, with `fst_levelMapOf`, `snd_levelMapOf`, `eq_levelMapOf`,
  `levelMapOf_id`, `levelMapOf_comp`);
* `LevelTower.transportMap`: `φ` as an algebra map of the transported coverings over a level
  `S/J` (and over `S`, `transportMapR`);
* **`LevelTower.pMap D D' φ`**, **`LevelTower.levelMap D D' φ g hκ`**: the maps `P → P'` and
  `G → G'` of the patched algebras at one level, for an NF-map `g : NF → NF'` compatible with `φ`
  under `kappaF` (`hκ`); `σP_pMap`, `eq_pMap`, `fst_levelMap`, `eq_levelMap`, `ext_level`;
* **`LevelTower.tr_levelMap`**: the level maps commute with the transition maps of the towers
  (`tr' ∘ levelMap (n+1) = levelMap n ∘ tr`), via `LevelStep.ρP₂_pMapOf` (the étale parts) and
  `LevelStep.Tmap_NfMap`.
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

noncomputable section

namespace LevelTower

/-! ### Maps of étale lifts and of patched algebras at one level (abstract) -/

section Abstract

variable {S : Type u} [CommRing S] (f : S) (J : Ideal S) {m : ℕ} (hJ : J ^ m = ⊥)
  {P P' P'' : Type u} [CommRing P] [Algebra S P] [Algebra.FormallyEtale S P]
  [CommRing P'] [Algebra S P'] [Algebra.FormallyEtale S P']
  [CommRing P''] [Algebra S P''] [Algebra.FormallyEtale S P'']
  {C C' C'' : Type u} [CommRing C] [Algebra S C] [CommRing C'] [Algebra S C']
  [CommRing C''] [Algebra S C'']
  (σ : (P ⧸ J.map (algebraMap S P)) ≃ₐ[S] Localization.Away (algebraMap S C f))
  (σ' : (P' ⧸ J.map (algebraMap S P')) ≃ₐ[S] Localization.Away (algebraMap S C' f))
  (σ'' : (P'' ⧸ J.map (algebraMap S P'')) ≃ₐ[S] Localization.Away (algebraMap S C'' f))

omit [Algebra.FormallyEtale S P'] in
/-- **The lift `P → P'` of `φ_f : C_f → C'_f`** (`P` formally étale, `J` nilpotent). -/
def pMapOf (φ : C →ₐ[S] C') : P →ₐ[S] P' :=
  EtaleNil.lift J hJ (σ'.symm.toAlgHom.comp ((FormalPatchLevel.NfMap f φ).comp
    (σ.toAlgHom.comp (Ideal.Quotient.mkₐ S _))))

omit [Algebra.FormallyEtale S P'] in
/-- **`pMapOf φ` reduces to `φ_f`.** -/
lemma σ_pMapOf (φ : C →ₐ[S] C') (x : P) :
    σ' (Ideal.Quotient.mk _ (pMapOf f J hJ σ σ' φ x)) =
      FormalPatchLevel.NfMap f φ (σ (Ideal.Quotient.mk _ x)) := by
  have h := EtaleNil.mk_lift J hJ (σ'.symm.toAlgHom.comp ((FormalPatchLevel.NfMap f φ).comp
    (σ.toAlgHom.comp (Ideal.Quotient.mkₐ S _)))) x
  change σ' (Ideal.Quotient.mk _ (EtaleNil.lift _ _ _ x)) = _
  rw [h]
  exact σ'.apply_symm_apply _

omit [Algebra.FormallyEtale S P'] in
/-- **Uniqueness**: an `S`-algebra map `P → P'` reducing to `φ_f` is `pMapOf φ`. -/
lemma eq_pMapOf (φ : C →ₐ[S] C') (p : P →ₐ[S] P')
    (hp : ∀ x, σ' (Ideal.Quotient.mk _ (p x)) =
      FormalPatchLevel.NfMap f φ (σ (Ideal.Quotient.mk _ x))) :
    p = pMapOf f J hJ σ σ' φ :=
  EtaleNil.ext J hJ fun x ↦ σ'.injective (by rw [hp, σ_pMapOf])

omit [Algebra.FormallyEtale S P'] [Algebra.FormallyEtale S P''] in
lemma pMapOf_id : pMapOf f J hJ σ σ (AlgHom.id S C) = AlgHom.id S P :=
  (eq_pMapOf f J hJ σ σ _ _ fun x ↦ by rw [FormalPatchLevel.NfMap_id]; rfl).symm

omit [Algebra.FormallyEtale S P''] in
lemma pMapOf_comp (φ : C →ₐ[S] C') (φ' : C' →ₐ[S] C'') :
    pMapOf f J hJ σ σ'' (φ'.comp φ) = (pMapOf f J hJ σ' σ'' φ').comp (pMapOf f J hJ σ σ' φ) :=
  (eq_pMapOf f J hJ σ σ'' _ _ fun x ↦ by
    rw [AlgHom.comp_apply, σ_pMapOf, σ_pMapOf, FormalPatchLevel.NfMap_comp,
      AlgHom.comp_apply]).symm

variable {N N' N'' : Type u} [CommRing N] [Algebra S N] [Algebra (FormalPatchLevel.Hat f) N]
  [IsScalarTower S (FormalPatchLevel.Hat f) N]
  [CommRing N'] [Algebra S N'] [Algebra (FormalPatchLevel.Hat f) N']
  [IsScalarTower S (FormalPatchLevel.Hat f) N']
  [CommRing N''] [Algebra S N''] [Algebra (FormalPatchLevel.Hat f) N'']
  [IsScalarTower S (FormalPatchLevel.Hat f) N'']
  (κ : (FormalPatchLevel.Hat f ⊗[S] C) ≃ₐ[FormalPatchLevel.Hat f]
    (N ⧸ FormalPatchLevel.JN J N))
  (κ' : (FormalPatchLevel.Hat f ⊗[S] C') ≃ₐ[FormalPatchLevel.Hat f]
    (N' ⧸ FormalPatchLevel.JN J N'))
  (κ'' : (FormalPatchLevel.Hat f ⊗[S] C'') ≃ₐ[FormalPatchLevel.Hat f]
    (N'' ⧸ FormalPatchLevel.JN J N''))
  {m' m'' : ℕ} (hJ' : J ^ m' = ⊥) (hJ'' : J ^ m'' = ⊥)

/-- **The map of patched algebras** induced by `φ : C → C'` and a compatible `g : N → N'`. -/
def levelMapOf (φ : C →ₐ[S] C') (g : N →ₐ[S] N')
    (hκ : ∀ c : C, κ' ((1 : FormalPatchLevel.Hat f) ⊗ₜ φ c) =
      FormalPatchLevel.NMapQuot J g (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c))) :
    FormalPatchLevel.patch f J hJ (FormalPatchLevel.alphaOfEquiv f J
        (FormalPatchLevel.specialFibreEquiv f J σ κ)) →ₐ[S]
      FormalPatchLevel.patch f J hJ' (FormalPatchLevel.alphaOfEquiv f J
        (FormalPatchLevel.specialFibreEquiv f J σ' κ')) :=
  FormalPatchLevel.patchMap f J hJ _ _ (pMapOf f J hJ σ σ' φ) g
    (FormalPatchLevel.comp_alphaOfEquiv f J σ κ σ' κ' _ φ g (σ_pMapOf f J hJ σ σ' φ) hκ)


@[simp] lemma fst_levelMapOf (φ : C →ₐ[S] C') (g : N →ₐ[S] N')
    (hκ : ∀ c : C, κ' ((1 : FormalPatchLevel.Hat f) ⊗ₜ φ c) =
      FormalPatchLevel.NMapQuot J g (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)))
    (x : FormalPatchLevel.patch f J hJ (FormalPatchLevel.alphaOfEquiv f J
        (FormalPatchLevel.specialFibreEquiv f J σ κ))) :
    (levelMapOf f J hJ σ σ' κ κ' hJ' φ g hκ x).1.1 = pMapOf f J hJ σ σ' φ x.1.1 :=
  rfl

@[simp] lemma snd_levelMapOf (φ : C →ₐ[S] C') (g : N →ₐ[S] N')
    (hκ : ∀ c : C, κ' ((1 : FormalPatchLevel.Hat f) ⊗ₜ φ c) =
      FormalPatchLevel.NMapQuot J g (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)))
    (x : FormalPatchLevel.patch f J hJ (FormalPatchLevel.alphaOfEquiv f J
        (FormalPatchLevel.specialFibreEquiv f J σ κ))) :
    (levelMapOf f J hJ σ σ' κ κ' hJ' φ g hκ x).1.2 = g x.1.2 :=
  rfl

/-- **Uniqueness**: a map of patched algebras with first component `pMapOf φ` is `levelMapOf`
(`N'` without `f`-torsion). -/
theorem eq_levelMapOf (hN' : ∀ x : N', algebraMap S N' f * x = 0 → x = 0)
    (φ : C →ₐ[S] C') (g : N →ₐ[S] N')
    (hκ : ∀ c : C, κ' ((1 : FormalPatchLevel.Hat f) ⊗ₜ φ c) =
      FormalPatchLevel.NMapQuot J g (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)))
    (ψ : FormalPatchLevel.patch f J hJ (FormalPatchLevel.alphaOfEquiv f J
        (FormalPatchLevel.specialFibreEquiv f J σ κ)) →ₐ[S]
      FormalPatchLevel.patch f J hJ' (FormalPatchLevel.alphaOfEquiv f J
        (FormalPatchLevel.specialFibreEquiv f J σ' κ')))
    (hψ : ∀ x, (ψ x).1.1 = pMapOf f J hJ σ σ' φ x.1.1) :
    ψ = levelMapOf f J hJ σ σ' κ κ' hJ' φ g hκ :=
  FormalPatchLevel.ext_of_fst f J hJ' _ hN' hψ

omit [IsScalarTower S (FormalPatchLevel.Hat f) N] in
/-- The compatibility `hκ` for the identity. -/
lemma compat_id (c : C) :
    κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ AlgHom.id S C c) =
      FormalPatchLevel.NMapQuot J (AlgHom.id S N) (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)) := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c))
  rw [AlgHom.id_apply, ← hy]
  rfl

omit [IsScalarTower S (FormalPatchLevel.Hat f) N] [IsScalarTower S (FormalPatchLevel.Hat f) N']
  [IsScalarTower S (FormalPatchLevel.Hat f) N''] in
/-- The compatibility `hκ` for a composition. -/
lemma compat_comp (φ : C →ₐ[S] C') (g : N →ₐ[S] N') (φ' : C' →ₐ[S] C'') (g' : N' →ₐ[S] N'')
    (hκ : ∀ c : C, κ' ((1 : FormalPatchLevel.Hat f) ⊗ₜ φ c) =
      FormalPatchLevel.NMapQuot J g (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)))
    (hκ' : ∀ c : C', κ'' ((1 : FormalPatchLevel.Hat f) ⊗ₜ φ' c) =
      FormalPatchLevel.NMapQuot J g' (κ' ((1 : FormalPatchLevel.Hat f) ⊗ₜ c))) (c : C) :
    κ'' ((1 : FormalPatchLevel.Hat f) ⊗ₜ (φ'.comp φ) c) =
      FormalPatchLevel.NMapQuot J (g'.comp g) (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)) := by
  rw [AlgHom.comp_apply, hκ', hκ]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c))
  rw [← hy]
  rfl

omit [Algebra.FormallyEtale S P'] [Algebra.FormallyEtale S P''] in
lemma levelMapOf_id
    (hκ : ∀ c : C, κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ AlgHom.id S C c) =
      FormalPatchLevel.NMapQuot J (AlgHom.id S N) (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c))) :
    levelMapOf f J hJ σ σ κ κ hJ (AlgHom.id S C) (AlgHom.id S N) hκ = AlgHom.id S _ :=
  AlgHom.ext fun x ↦ Subtype.ext (Prod.ext
    (congrArg (fun p : P →ₐ[S] P ↦ p x.1.1) (pMapOf_id f J hJ σ)) rfl)

lemma levelMapOf_comp (φ : C →ₐ[S] C') (g : N →ₐ[S] N') (φ' : C' →ₐ[S] C'')
    (g' : N' →ₐ[S] N'')
    (hκ : ∀ c : C, κ' ((1 : FormalPatchLevel.Hat f) ⊗ₜ φ c) =
      FormalPatchLevel.NMapQuot J g (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)))
    (hκ' : ∀ c : C', κ'' ((1 : FormalPatchLevel.Hat f) ⊗ₜ φ' c) =
      FormalPatchLevel.NMapQuot J g' (κ' ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)))
    (hκ'' : ∀ c : C, κ'' ((1 : FormalPatchLevel.Hat f) ⊗ₜ (φ'.comp φ) c) =
      FormalPatchLevel.NMapQuot J (g'.comp g) (κ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c))) :
    (levelMapOf f J hJ' σ' σ'' κ' κ'' hJ'' φ' g' hκ').comp
        (levelMapOf f J hJ σ σ' κ κ' hJ' φ g hκ) =
      levelMapOf f J hJ σ σ'' κ κ'' hJ'' (φ'.comp φ) (g'.comp g) hκ'' :=
  AlgHom.ext fun x ↦ Subtype.ext (Prod.ext
    (congrArg (fun p : P →ₐ[S] P'' ↦ p x.1.1) (pMapOf_comp f J hJ σ σ' σ'' φ φ')).symm rfl)

end Abstract

/-! ### The transported map of special-fibre coverings -/

section Transport

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {S : Type u} [CommRing S] [Algebra O S] [Algebra k (S ⧸ J θ (R := S))] {g : S}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀} {e : R₀ ≃ₐ[k] (S ⧸ J θ (R := S))}
  (h : e f₀ = fbar θ g)
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ cov₀' cov₀'' : Admissible.Covering φ₀ ψ₀}

/-- **A map of special-fibre coverings is a map of the transported coverings** over `S/J`
(the same function). -/
def transportMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) :
    (cov₀.transport (h := h)).C →ₐ[S ⧸ J θ (R := S)] (cov₀'.transport (h := h)).C where
  toRingHom := φ.toRingHom
  commutes' r := φ.commutes (e.symm r)

/-- The transported map over the level `S`. -/
def transportMapR (φ : cov₀.C →ₐ[R₀] cov₀'.C) :
    (cov₀.transport (h := h)).C →ₐ[S] (cov₀'.transport (h := h)).C :=
  (transportMap h φ).restrictScalars S

lemma transportMapR_apply (φ : cov₀.C →ₐ[R₀] cov₀'.C) (c : (cov₀.transport (h := h)).C) :
    transportMapR h φ c = φ c :=
  rfl

lemma transportMapR_id :
    transportMapR h (AlgHom.id R₀ cov₀.C) = AlgHom.id S (cov₀.transport (h := h)).C :=
  AlgHom.ext fun _ ↦ rfl

lemma transportMapR_comp (φ : cov₀.C →ₐ[R₀] cov₀'.C) (φ' : cov₀'.C →ₐ[R₀] cov₀''.C) :
    transportMapR h (φ'.comp φ) = (transportMapR h φ').comp (transportMapR h φ) :=
  AlgHom.ext fun _ ↦ rfl

end Transport

/-! ### Compatibility with the reduction of the étale parts -/

section Step

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {R' : Type u} [CommRing R'] [Algebra O R']
  [Algebra R R'] (f : R) (f₂ : R') (hf : LevelStep.f' (R' := R') f = f₂)
  [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {e₁ : R₀ ≃ₐ[k] (R ⧸ J θ (R := R))} {e₂ : R₀ ≃ₐ[k] (R' ⧸ J θ (R := R'))}
  (h₁ : e₁ f₀ = fbar θ f) (h₂ : e₂ f₀ = fbar θ f₂)
  (he : ∀ r : R, e₂ (e₁.symm (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (algebraMap R R' r))
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  (cov₀ cov₀' : Admissible.Covering φ₀ ψ₀)

/-- **`Tmap` commutes with the localized transported maps.** -/
lemma Tmap_NfMap (φ : cov₀.C →ₐ[R₀] cov₀'.C)
    (y : Localization.Away (algebraMap R (cov₀.transport (h := h₁)).C f)) :
    LevelStep.Tmap f f₂ hf h₁ h₂ he cov₀' (FormalPatchLevel.NfMap f (transportMapR h₁ φ) y) =
      FormalPatchLevel.NfMap f₂ (transportMapR h₂ φ) (LevelStep.Tmap f f₂ hf h₁ h₂ he cov₀ y) := by
  have key : (LevelStep.Tmap f f₂ hf h₁ h₂ he cov₀').comp
        (FormalPatchLevel.NfMap f (transportMapR h₁ φ)).toRingHom =
      (FormalPatchLevel.NfMap f₂ (transportMapR h₂ φ)).toRingHom.comp
        (LevelStep.Tmap f f₂ hf h₁ h₂ he cov₀) :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R (cov₀.transport (h := h₁)).C f))
      (RingHom.ext fun c ↦ by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [FormalPatchLevel.NfMap_algebraMap, LevelStep.Tmap_algebraMap,
          LevelStep.Tmap_algebraMap, FormalPatchLevel.NfMap_algebraMap]
        rfl)
  exact RingHom.congr_fun key y

variable {P Q : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  [CommRing Q] [Algebra R Q] [Algebra.FormallyEtale R Q]
  {P' Q' : Type u} [CommRing P'] [Algebra R' P'] [Algebra.FormallyEtale R' P'] [Algebra R P']
  [IsScalarTower R R' P'] [CommRing Q'] [Algebra R' Q'] [Algebra R Q'] [IsScalarTower R R' Q']
  {m m' : ℕ} (hJ : J θ (R := R) ^ m = ⊥) (hJ' : J θ (R := R') ^ m' = ⊥)
  (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R]
    Localization.Away (algebraMap R (cov₀.transport (h := h₁)).C f))
  (σQ : (Q ⧸ (J θ).map (algebraMap R Q)) ≃ₐ[R]
    Localization.Away (algebraMap R (cov₀'.transport (h := h₁)).C f))
  (σP' : (P' ⧸ (J θ).map (algebraMap R' P')) ≃ₐ[R']
    Localization.Away (algebraMap R' (cov₀.transport (h := h₂)).C f₂))
  (σQ' : (Q' ⧸ (J θ).map (algebraMap R' Q')) ≃ₐ[R']
    Localization.Away (algebraMap R' (cov₀'.transport (h := h₂)).C f₂))

/-- **The lifted maps commute with the reduction of the étale parts** `ρP₂`. -/
theorem ρP₂_pMapOf (φ : cov₀.C →ₐ[R₀] cov₀'.C) (p : P) :
    LevelStep.ρP₂ f f₂ hf h₁ h₂ he cov₀' hJ' σQ σQ'
        (pMapOf f (J θ) hJ σP σQ (transportMapR h₁ φ) p) =
      pMapOf f₂ (J θ) hJ' σP' σQ' (transportMapR h₂ φ)
        (LevelStep.ρP₂ f f₂ hf h₁ h₂ he cov₀ hJ' σP σP' p) := by
  haveI := EtaleNil.isAdicComplete (J θ (R := R')) hJ' Q'
  have key : (LevelStep.ρP₂ f f₂ hf h₁ h₂ he cov₀' hJ' σQ σQ').comp
        (pMapOf f (J θ) hJ σP σQ (transportMapR h₁ φ)) =
      ((pMapOf f₂ (J θ) hJ' σP' σQ' (transportMapR h₂ φ)).restrictScalars R).comp
        (LevelStep.ρP₂ f f₂ hf h₁ h₂ he cov₀ hJ' σP σP') :=
    EtaleLift.ext_of_comp_eq (EtaleNil.JB (J θ (R := R')) Q') (AlgHom.ext fun x ↦
      σQ'.injective (by
        change σQ' (Ideal.Quotient.mk _ (LevelStep.ρP₂ f f₂ hf h₁ h₂ he cov₀' hJ' σQ σQ'
            (pMapOf f (J θ) hJ σP σQ (transportMapR h₁ φ) x))) =
          σQ' (Ideal.Quotient.mk _ (pMapOf f₂ (J θ) hJ' σP' σQ' (transportMapR h₂ φ)
            (LevelStep.ρP₂ f f₂ hf h₁ h₂ he cov₀ hJ' σP σP' x)))
        rw [LevelStep.σP_ρP₂, σ_pMapOf, σ_pMapOf, LevelStep.σP_ρP₂, Tmap_NfMap]))
  exact AlgHom.congr_fun key p

end Step

/-! ### Maps of the patched levels -/

section Level

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ cov₀' cov₀'' : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  {πL'' : cov₀''.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ) {n : ℕ}
  (D : Level R cov₀ πL hfe n) (D' : Level R cov₀' πL' hfe n) (D'' : Level R cov₀'' πL'' hfe n)

/-- **The map of étale lifts** `D.P → D'.P` at level `n` induced by `φ : cov₀.C → cov₀'.C`. -/
def pMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) : D.P →ₐ[R n] D'.P :=
  pMapOf (f n) (J θ) D.hJ D.σP D'.σP (transportMapR (hfe n) φ)

omit [∀ n, IsNoetherianRing (R n)] in
/-- **`pMap φ` reduces to `φ_f`.** -/
lemma σP_pMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (x : D.P) :
    D'.σP (Ideal.Quotient.mk _ (pMap D D' φ x)) =
      FormalPatchLevel.NfMap (f n) (transportMapR (hfe n) φ) (D.σP (Ideal.Quotient.mk _ x)) :=
  σ_pMapOf (f n) (J θ) D.hJ D.σP D'.σP _ x

omit [∀ n, IsNoetherianRing (R n)] in
/-- **Uniqueness of `pMap`.** -/
lemma eq_pMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (p : D.P →ₐ[R n] D'.P)
    (hp : ∀ x, D'.σP (Ideal.Quotient.mk _ (p x)) =
      FormalPatchLevel.NfMap (f n) (transportMapR (hfe n) φ) (D.σP (Ideal.Quotient.mk _ x))) :
    p = pMap D D' φ :=
  eq_pMapOf (f n) (J θ) D.hJ D.σP D'.σP _ p hp

omit [∀ n, IsNoetherianRing (R n)] in
lemma pMap_id : pMap D D (AlgHom.id R₀ cov₀.C) = AlgHom.id (R n) D.P := by
  unfold pMap
  rw [transportMapR_id]
  exact pMapOf_id (f n) (J θ) D.hJ D.σP

omit [∀ n, IsNoetherianRing (R n)] in
lemma pMap_comp (φ : cov₀.C →ₐ[R₀] cov₀'.C) (φ' : cov₀'.C →ₐ[R₀] cov₀''.C) :
    pMap D D'' (φ'.comp φ) = (pMap D' D'' φ').comp (pMap D D' φ) := by
  unfold pMap
  rw [transportMapR_comp]
  exact pMapOf_comp (f n) (J θ) D.hJ D.σP D'.σP D''.σP _ _

/-- **The compatibility of an NF-map `g` with `φ` under `kappaF`** (the hypothesis `hκ` of
`FormalPatchLevel.comp_alphaOfEquiv`). -/
def KappaCompat (φ : cov₀.C →ₐ[R₀] cov₀'.C) (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M) :
    Prop :=
  ∀ c : (cov₀.transport (h := hfe n)).C,
    kappaF D'.L D'.M hθ ((1 : FormalPatchLevel.Hat (f n)) ⊗ₜ transportMapR (hfe n) φ c) =
      FormalPatchLevel.NMapQuot (J θ) g (kappaF D.L D.M hθ ((1 : FormalPatchLevel.Hat (f n)) ⊗ₜ c))

/-- **The map of patched algebras** `D.G → D'.G` at level `n`. -/
def levelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M)
    (hκ : KappaCompat hθ D D' φ g) : D.G hθ →ₐ[R n] D'.G hθ :=
  levelMapOf (f n) (J θ) D.hJ D.σP D'.σP (kappaF D.L D.M hθ) (kappaF D'.L D'.M hθ) D'.hJ
    (transportMapR (hfe n) φ) g hκ

@[simp] lemma fst_levelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C)
    (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M) (hκ : KappaCompat hθ D D' φ g) (x : D.G hθ) :
    (levelMap hθ D D' φ g hκ x).1.1 = pMap D D' φ x.1.1 :=
  rfl

@[simp] lemma snd_levelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C)
    (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M) (hκ : KappaCompat hθ D D' φ g) (x : D.G hθ) :
    (levelMap hθ D D' φ g hκ x).1.2 = g x.1.2 :=
  rfl

/-- **Maps into a patched level are determined by their first component.** -/
theorem ext_level {M : Type*} [CommRing M] [Algebra (R n) M] {ψ₁ ψ₂ : M →ₐ[R n] D'.G hθ}
    (h : ∀ x, (ψ₁ x).1.1 = (ψ₂ x).1.1) : ψ₁ = ψ₂ :=
  FormalPatchLevel.ext_of_fst (f n) (J θ) D'.hJ _
    (noTorsion_NFall D'.L D'.M D'.hflat D'.hidem D'.hfχ D'.hcidem D'.hreg) h

/-- **Uniqueness of `levelMap`**: a map `D.G → D'.G` with first component `pMap φ` is
`levelMap φ g hκ`. -/
theorem eq_levelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M)
    (hκ : KappaCompat hθ D D' φ g) (ψ : D.G hθ →ₐ[R n] D'.G hθ)
    (hψ : ∀ x, (ψ x).1.1 = pMap D D' φ x.1.1) : ψ = levelMap hθ D D' φ g hκ :=
  ext_level hθ D' hψ

lemma kappaCompat_id : KappaCompat hθ D D (AlgHom.id R₀ cov₀.C) (AlgHom.id (R n) _) :=
  compat_id (f n) (J θ) (kappaF D.L D.M hθ)

lemma kappaCompat_comp (φ : cov₀.C →ₐ[R₀] cov₀'.C) (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M)
    (φ' : cov₀'.C →ₐ[R₀] cov₀''.C) (g' : NFall D'.L D'.M →ₐ[R n] NFall D''.L D''.M)
    (hκ : KappaCompat hθ D D' φ g) (hκ' : KappaCompat hθ D' D'' φ' g') :
    KappaCompat hθ D D'' (φ'.comp φ) (g'.comp g) :=
  compat_comp (f n) (J θ) (kappaF D.L D.M hθ) (kappaF D'.L D'.M hθ) (kappaF D''.L D''.M hθ)
    (transportMapR (hfe n) φ) g (transportMapR (hfe n) φ') g' hκ hκ'

lemma levelMap_id (hκ : KappaCompat hθ D D (AlgHom.id R₀ cov₀.C) (AlgHom.id (R n) _)) :
    levelMap hθ D D (AlgHom.id R₀ cov₀.C) (AlgHom.id (R n) _) hκ = AlgHom.id (R n) _ :=
  AlgHom.ext fun x ↦ Subtype.ext (Prod.ext
    (congrArg (fun p : D.P →ₐ[R n] D.P ↦ p x.1.1) (pMap_id D)) rfl)

lemma levelMap_comp (φ : cov₀.C →ₐ[R₀] cov₀'.C) (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M)
    (φ' : cov₀'.C →ₐ[R₀] cov₀''.C) (g' : NFall D'.L D'.M →ₐ[R n] NFall D''.L D''.M)
    (hκ : KappaCompat hθ D D' φ g) (hκ' : KappaCompat hθ D' D'' φ' g')
    (hκ'' : KappaCompat hθ D D'' (φ'.comp φ) (g'.comp g)) :
    (levelMap hθ D' D'' φ' g' hκ').comp (levelMap hθ D D' φ g hκ) =
      levelMap hθ D D'' (φ'.comp φ) (g'.comp g) hκ'' :=
  AlgHom.ext fun x ↦ Subtype.ext (Prod.ext
    (congrArg (fun p : D.P →ₐ[R n] D''.P ↦ p x.1.1) (pMap_comp D D' D'' φ φ')).symm rfl)

end Level

/-! ### Compatibility with the transition maps of the towers -/

section Tower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ cov₀' : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ)
  [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hq : ∀ n, Function.Surjective (algebraMap (R (n + 1)) (R n)))
  (hf : ∀ n, LevelStep.f' (R' := R n) (f (n + 1)) = f n)
  (he : ∀ n (r : R (n + 1)), e n ((e (n + 1)).symm (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (algebraMap (R (n + 1)) (R n) r))
  (D : ∀ n, Level R cov₀ πL hfe n)
  (hχχ : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.χ j a) = (D n).L.χ j a)
  (hεε : ∀ n j, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.ε j) = (D n).L.ε j)
  (hδδ : ∀ n i, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).M.δ i) = (D n).M.δ i)
  (htt : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (D (n + 1)).M.t = (D n).M.t)
  (D' : ∀ n, Level R cov₀' πL' hfe n)
  (hχχ' : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D' (n + 1)).L.χ j a) =
    (D' n).L.χ j a)
  (hεε' : ∀ n j, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D' (n + 1)).L.ε j) = (D' n).L.ε j)
  (hδδ' : ∀ n i, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D' (n + 1)).M.δ i) = (D' n).M.δ i)
  (htt' : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (D' (n + 1)).M.t = (D' n).M.t)

omit [∀ n, IsNoetherianRing (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
/-- **The maps of étale lifts commute with the reductions** `ρPn` of the towers. -/
theorem ρPn_pMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (n : ℕ) (p : (D (n + 1)).P) :
    ρPn hf he D' n (pMap (D (n + 1)) (D' (n + 1)) φ p) = pMap (D n) (D' n) φ (ρPn hf he D n p) :=
  letI := algP D n
  letI := algP D' n
  haveI : IsScalarTower (R (n + 1)) (R n) (D n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (R (n + 1)) (R n) (D' n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  ρP₂_pMapOf (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) cov₀ cov₀' (D (n + 1)).hJ
    (D n).hJ (D (n + 1)).σP (D' (n + 1)).σP (D n).σP (D' n).σP φ p

/-- **The level maps commute with the transition maps of the towers**:
`tr' ∘ levelMap (n+1) = levelMap n ∘ tr`. -/
theorem tr_levelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C)
    (g : ∀ n, NFall (D n).L (D n).M →ₐ[R n] NFall (D' n).L (D' n).M)
    (hκ : ∀ n, KappaCompat hθ (D n) (D' n) φ (g n)) (n : ℕ) (x : (D (n + 1)).G hθ) :
    tr hθ hO hq hf he D' hχχ' hεε' hδδ' htt' n
        (levelMap hθ (D (n + 1)) (D' (n + 1)) φ (g (n + 1)) (hκ (n + 1)) x) =
      levelMap hθ (D n) (D' n) φ (g n) (hκ n) (tr hθ hO hq hf he D hχχ hεε hδδ htt n x) :=
  FormalGlueing.eq_of_fst_eq (f := f n) (NFall (D' n).L (D' n).M) _
    (noTorsion_NFall (D' n).L (D' n).M (D' n).hflat (D' n).hidem (D' n).hfχ (D' n).hcidem
      (D' n).hreg)
    ((tr_fst_eq hθ hO hq hf he D' hχχ' hεε' hδδ' htt' n _).trans
      ((ρPn_pMap hf he D D' φ n x.1.1).trans
        (congrArg (pMap (D n) (D' n) φ) (tr_fst_eq hθ hO hq hf he D hχχ hεε hδδ htt n x).symm)))

end Tower

/-! ### Bundled towers -/

namespace Data

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (T : Data (θ := θ) R cov₀ πL) (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The transition maps of a bundled tower are those of its levels** (so `tr_levelMap`
applies to bundled towers with the same `f`, `e`). -/
lemma tr_eq_tr (n : ℕ) :
    T.tr hθ hO n = LevelTower.tr hθ hO T.hq T.hf T.he T.level T.hcχ
      (hεε_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg T.hf T.he)
      (hδδ_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg T.hf T.he) T.hct n :=
  rfl

end Data

end LevelTower

end

end SemistableReduction
