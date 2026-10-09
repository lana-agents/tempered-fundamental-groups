/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Final
import TemperedFundamentalGroups.SemistableReduction.PiIdem

/-!
# The component clause of `StrongComponentA` for the W10 assembly

Blueprint §10.3.8 (StrongComponentA (c)). In the W10 assembly (`W10Assembly`), `c'` is the
disjoint union of the projective models of the components `𝔪` of `E ⊗_K B`, and `c` its multi-`θ`
base change. For a nonzero primitive idempotent `ε` of `E ⊗_K B`:

* `exists_component`: `ε` is the unit of one component `𝔪` (`Φ : E ⊗_K B ≅ Π 𝔪, D 𝔪`);
* `Qequiv`: `(E ⊗_K B) ⧸ (1 − ε) ≅ D 𝔪`, and `isFractionRing_D`: `Comp 𝔪` is its fraction field;
* `j₁`, `j₁_sigmaι`: the generic point of the `𝔪`-summand, compatible with `jC`;
* `πh_eq_of_fix`, `exists_stab_act`: the stabiliser of `ε` fixes `𝔪` and acts on the summand;
* **`component_clause`**: the component clause of `Statement.StrongComponentA` for `c`, given
  semistability, split nodes, no loops, connected special fibres and unfoldedness of the summands.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits Polynomial TensorProduct

namespace SemistableReduction

namespace W10Assembly

open TemperedFundamentalGroups W10Fields ProjScheme ZariskiModel

attribute [local instance] polyAlgebra compAlgO

section Clause

variable {K : Type u} [Field K] (O : ValuationSubring K)
  {B : Type u} [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B]
  [Algebra K B] [IsScalarTower K K[X] B]
  {E : Type u} [Field E] [Algebra K E] (O' : ValuationSubring E)
  (hO' : O'.comap (algebraMap K E) = O) [IsReduced (BX K E B)]
  (hn : IsIntegrallyClosedIn (BX K E B) (LX K E B))
  (n : MaximalSpectrum (LX K E B) → ℕ) {g : ∀ 𝔪, Fin (n 𝔪 + 1) → Comp K E B 𝔪}
  (hg : ∀ 𝔪 j, g 𝔪 j ≠ 0)
  (hroot : ∀ 𝔪, LocallyDominates (algebraMap O' (Comp K E B 𝔪)).range (RingHom.id _)
    (D K E B 𝔪).subtype (g 𝔪))
  {r : ℕ} (θ : Fin r → O') (hθ0 : ∀ s, (θ s : E) ≠ 0)
  (hθint : ∀ s, letI := algebraOO' O E O' hO'; IsIntegral O (θ s))
  (hθgen : ∀ y : O', (y : E) ∈ Subring.closure
    ((((algebraMap K E).comp O.subtype).range : Set E) ∪ Set.range fun s ↦ (θ s : E)))

/-- `E ⊗_K B ≅ Π 𝔪, D 𝔪`. -/
noncomputable def Φ : TensorProduct K E B ≃+* (∀ 𝔪, D K E B 𝔪) :=
  (tensorEquiv K E B).toRingEquiv.trans (piD hn)

lemma ψ_eq_Φ (z : TensorProduct K E B) (𝔪 : MaximalSpectrum (LX K E B)) :
    ψ (K := K) (B := B) (E := E) z 𝔪 = (Φ hn z 𝔪 : Comp K E B 𝔪) := rfl

instance (𝔪 : MaximalSpectrum (LX K E B)) : IsDomain (D K E B 𝔪) := inferInstance

open Classical in
/-- A nonzero primitive idempotent of `E ⊗_K B` is the unit of one component. -/
lemma exists_component {ε : TensorProduct K E B} (he : IsIdempotentElem ε) (h0 : ε ≠ 0)
    (hprim : ∀ f : TensorProduct K E B, IsIdempotentElem f → f * ε = 0 ∨ f * ε = ε) :
    ∃ 𝔪, Φ hn ε = Pi.single 𝔪 1 := by
  refine PiIdem.exists_eq_single (he.map (Φ hn)) (fun h => h0 ((Φ hn).injective
    (h.trans (map_zero _).symm))) fun f hf => ?_
  rcases hprim ((Φ hn).symm f) (hf.map (Φ hn).symm) with h | h
  · left
    have := congrArg (Φ hn) h
    rwa [map_mul, RingEquiv.apply_symm_apply, map_zero] at this
  · right
    have := congrArg (Φ hn) h
    rwa [map_mul, RingEquiv.apply_symm_apply] at this

open Classical in
/-- `(E ⊗_K B) ⧸ (1 − ε) ≅ D 𝔪` for `ε` the unit of the component `𝔪`. -/
noncomputable def Qequiv {ε : TensorProduct K E B} {𝔪 : MaximalSpectrum (LX K E B)}
    (h𝔪 : Φ hn ε = Pi.single 𝔪 1) :
    (TensorProduct K E B ⧸ Ideal.span {1 - ε}) ≃+* D K E B 𝔪 :=
  (Ideal.quotientEquiv _ (Ideal.span {1 - Pi.single 𝔪 1}) (Φ hn)
    (by
      rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
      exact congrArg (fun z => Ideal.span {1 - z}) h𝔪.symm)).trans
    (PiIdem.quotSingleEquiv 𝔪)

open Classical in
lemma Qequiv_mk {ε : TensorProduct K E B} {𝔪 : MaximalSpectrum (LX K E B)}
    (h𝔪 : Φ hn ε = Pi.single 𝔪 1) (z : TensorProduct K E B) :
    Qequiv hn h𝔪 (Ideal.Quotient.mk _ z) = Φ hn z 𝔪 := rfl

/-- The point `Spec (D 𝔪) ⟶` (the `𝔪`-summand of `c'`). -/
noncomputable def homC (𝔪 : MaximalSpectrum (LX K E B)) :
    Spec (CommRingCat.of (D K E B 𝔪)) ⟶ (projModelCode O' (hg 𝔪)).scheme :=
  homOfLocal (R₁ := (algebraMap O' (Comp K E B 𝔪)).range) (RingHom.id _) Subtype.val_injective
    rfl (hg 𝔪) (hroot 𝔪)

open Classical in
/-- **`j₁ : Spec ((E ⊗_K B) ⧸ (1 − ε)) ⟶ c₁`.** -/
noncomputable def j₁ {ε : TensorProduct K E B} {𝔪 : MaximalSpectrum (LX K E B)}
    (h𝔪 : Φ hn ε = Pi.single 𝔪 1) :
    Spec (CommRingCat.of (TensorProduct K E B ⧸ Ideal.span {1 - ε})) ⟶
      (projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))).scheme :=
  Spec.map (CommRingCat.ofHom (Qequiv hn h𝔪).symm.toRingHom) ≫ homC O' n hg hroot 𝔪 ≫
    (eComp O O' hO' n hg θ hθ0 hθint hθgen 𝔪).inv

open Classical in
theorem j₁_sigmaι {ε : TensorProduct K E B} {𝔪 : MaximalSpectrum (LX K E B)}
    (h𝔪 : Φ hn ε = Pi.single 𝔪 1) :
    j₁ O O' hO' hn n hg hroot θ hθ0 hθint hθgen h𝔪 ≫
        ModelCode.sigmaι (fun 𝔪 ↦ projModelCode O
          (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))) 𝔪 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - ε}))) ≫
        jC O O' hO' hn n hg hroot θ hθ0 hθint hθgen := by
  have hring : ((Ideal.Quotient.mk (Ideal.span {1 - ε})).comp
      ((tensorEquiv K E B).symm.toRingEquiv.toRingHom : BX K E B →+* TensorProduct K E B)).comp
        (piD hn).symm.toRingHom =
      ((Qequiv hn h𝔪).symm.toRingHom).comp (Pi.evalRingHom (fun 𝔪 ↦ D K E B 𝔪) 𝔪) := by
    refine RingHom.ext fun z => ?_
    apply (Qequiv hn h𝔪).injective
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply, Pi.evalRingHom_apply]
    rw [Qequiv_mk]
    change Φ hn ((Φ hn).symm z) 𝔪 = z 𝔪
    rw [RingEquiv.apply_symm_apply]
  rw [jC, jc']
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    reassoc_of% SpecMap_eval_jSigma, e, sigmaι_sigmaIsoOfIso_inv, j₁, homC]
  simp only [Category.assoc]

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] [Algebra K B] [IsScalarTower K K[X] B]
  [IsReduced (BX K E B)] in
/-- The summand isomorphism lies over `Spec O' ⟶ Spec O`. -/
theorem eComp_toSpec (𝔪 : MaximalSpectrum (LX K E B)) :
    (eComp O O' hO' n hg θ hθ0 hθint hθgen 𝔪).hom ≫ (projModelCode O' (hg 𝔪)).toSpec ≫
      Spec.map (CommRingCat.ofHom (algOO' O E O' hO')) =
      (projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))).toSpec := by
  letI := algebraOO' O E O' hO'
  haveI := isScalarTower_comp O B E O' hO' 𝔪
  exact baseChangeIsoFin_toSpec _ _ _ _ _ _ _ _

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] [Algebra K B] [IsScalarTower K K[X] B]
  [IsReduced (BX K E B)] in
lemma SpecMap_subtype_homC (𝔪 : MaximalSpectrum (LX K E B)) :
    Spec.map (CommRingCat.ofHom (D K E B 𝔪).subtype) ≫ homC O' n hg hroot 𝔪 =
      genericPt O' (hg 𝔪) := by
  rw [homC, SpecMap_comp_homOfLocal]
  simp

instance isDominant_homC (𝔪 : MaximalSpectrum (LX K E B)) :
    IsDominant (homC O' n hg hroot 𝔪) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (D K E B 𝔪).subtype) ≫ homC O' n hg hroot 𝔪) :=
    by rw [SpecMap_subtype_homC]; infer_instance
  exact IsDominant.of_comp (Spec.map (CommRingCat.ofHom (D K E B 𝔪).subtype)) _

open Classical in
instance isSchemeTheoreticallyDominant_j₁ {ε : TensorProduct K E B}
    {𝔪 : MaximalSpectrum (LX K E B)} (h𝔪 : Φ hn ε = Pi.single 𝔪 1) :
    IsSchemeTheoreticallyDominant (j₁ O O' hO' hn n hg hroot θ hθ0 hθint hθgen h𝔪) := by
  have : IsIso (CommRingCat.ofHom (Qequiv hn h𝔪).symm.toRingHom) :=
    (Qequiv hn h𝔪).symm.toCommRingCatIso.isIso_hom
  have : IsDominant (j₁ O O' hO' hn n hg hroot θ hθ0 hθint hθgen h𝔪) := by
    unfold j₁; infer_instance
  exact .of_isDominant _

omit [Module.IsTorsionFree K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [IsReduced (BX K E B)]
  in
/-- Transport along an equality of components. -/
lemma exists_comp_sigmaι {X : Scheme.{u}} {k 𝔪 : MaximalSpectrum (LX K E B)} (h : k = 𝔪)
    (M : X ⟶ (projModelCode O' (hg k)).scheme) :
    ∃ ψ : X ⟶ (projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))).scheme,
      M ≫ (eComp O O' hO' n hg θ hθ0 hθint hθgen k).inv ≫ ModelCode.sigmaι
        (fun 𝔪 ↦ projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))) k =
      ψ ≫ ModelCode.sigmaι
        (fun 𝔪 ↦ projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))) 𝔪 := by
  subst h
  exact ⟨_, (Category.assoc _ _ _).symm⟩

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] [Algebra K B] [IsScalarTower K K[X] B]
  [IsReduced (BX K E B)] in
/-- `Comp 𝔪` is the fraction field of `D 𝔪`. -/
lemma isFractionRing_D [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B]
    (𝔪 : MaximalSpectrum (LX K E B)) : IsFractionRing (D K E B 𝔪) (Comp K E B 𝔪) := by
  haveI : FaithfulSMul (D K E B 𝔪) (Comp K E B 𝔪) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj
    (Algebra.algebraMapSubmonoid (BX K E B) (nonZeroDivisors E[X])) y
  obtain ⟨q, hq, hqs⟩ := s.2
  have hs0 : Ideal.Quotient.mk 𝔪.asIdeal (algebraMap (BX K E B) (LX K E B) s) ≠ 0 := by
    rw [← hqs, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply E[X] (RatFunc E) (LX K E B)]
    change algebraMap (RatFunc E) (Comp K E B 𝔪) (algebraMap E[X] (RatFunc E) q) ≠ 0
    exact (_root_.map_ne_zero _).2
      ((map_ne_zero_iff _ (IsFractionRing.injective E[X] (RatFunc E))).2
      (nonZeroDivisors.ne_zero hq))
  refine ⟨⟨_, b, rfl⟩, ⟨_, s, rfl⟩, ?_⟩
  change _ = Ideal.Quotient.mk 𝔪.asIdeal (algebraMap (BX K E B) (LX K E B) b) /
    Ideal.Quotient.mk 𝔪.asIdeal (algebraMap (BX K E B) (LX K E B) s)
  rw [eq_div_iff hs0, ← map_mul, hbs]

section Stab

variable {G : Type u} [Group G] [MulSemiringAction G B] [SMulCommClass G K B]
  (β : G →* (B ≃ₐ[K[X]] B))
  (hβ : ∀ g, (β g).restrictScalars K = MulSemiringAction.toAlgAut G K B g)

include hβ in
open Classical in
/-- An element of `G × Gal(E/K)` fixing the unit `ε` of the component `𝔪` fixes `𝔪`. -/
theorem πh_eq_of_fix {ε : TensorProduct K E B} {𝔪 : MaximalSpectrum (LX K E B)}
    (h𝔪 : Φ hn ε = Pi.single 𝔪 1) (gσ : H (K := K) G E)
    (hfix : Algebra.TensorProduct.congr (gσ.2⁻¹) (MulSemiringAction.toAlgAut G K B gσ.1⁻¹) ε =
      ε) : πh β gσ 𝔪 = 𝔪 := by
  have h1 := ψ_congr β gσ⁻¹ ε
  have hα : αH (G := G) gσ⁻¹ = gσ.2⁻¹ := rfl
  have hβ' : (βH β gσ⁻¹).restrictScalars K = MulSemiringAction.toAlgAut G K B gσ.1⁻¹ := hβ _
  rw [hα, hβ', hfix] at h1
  have h2 := RingHom.congr_fun (sigmaRingHom_φh β gσ) (ψ (K := K) (B := B) (E := E) ε)
  have h4 : ψ (K := K) (B := B) (E := E) ε =
      sigmaRingHom (πh β gσ) (φh β gσ) (ψ (K := K) (B := B) (E := E) ε) :=
    h1.trans (by rw [h2]; rfl)
  have h3 := congrFun h4 𝔪
  change ψ (K := K) (B := B) (E := E) ε 𝔪 =
    φh β gσ 𝔪 (ψ (K := K) (B := B) (E := E) ε (πh β gσ 𝔪)) at h3
  rw [ψ_eq_Φ hn, ψ_eq_Φ hn, h𝔪] at h3
  by_contra hne
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h3
  simp at h3

variable (hσO' : ∀ σ : E ≃ₐ[K] E, ∀ y ∈ O', σ y ∈ O')
  (hact : ∀ (h : H (K := K) G E) (𝔫 : MaximalSpectrum (LX K E B)),
    ∀ Q ∈ (projModel (algebraMap O' (Comp K E B 𝔫)).range (g 𝔫)).points, ∃ i,
      ∀ y ∈ projChart (algebraMap O' (Comp K E B (πh β h 𝔫))).range (g (πh β h 𝔫)) i,
        φh β h 𝔫 y ∈ Q)

omit [Algebra K B] [IsScalarTower K K[X] B] [MulSemiringAction G B] [SMulCommClass G K B] in
/-- The stabiliser of a component acts on its summand. -/
theorem exists_stab_act {𝔪 : MaximalSpectrum (LX K E B)} (gσ : H (K := K) G E)
    (hfix : πh β gσ 𝔪 = 𝔪) :
    ∃ ψ : (projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))).scheme ⟶
        (projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))).scheme,
      ψ ≫ ModelCode.sigmaι
          (fun 𝔪 ↦ projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))) 𝔪 =
        ModelCode.sigmaι
          (fun 𝔪 ↦ projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))) 𝔪 ≫
          (act O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen gσ).hom := by
  obtain ⟨ψ, hψ⟩ := exists_comp_sigmaι O O' hO' n hg θ hθ0 hθint hθgen hfix
    ((eComp O O' hO' n hg θ hθ0 hθint hθgen 𝔪).hom ≫
      homOfLocalProj (R₁ := (algebraMap O' (Comp K E B (πh β gσ 𝔪))).range)
        (R₂ := (algebraMap O' (Comp K E B 𝔪)).range) rfl rfl (hg (πh β gσ 𝔪)) (hg 𝔪)
        (φh β gσ 𝔪) (locallyDominates_act O' β hσO' n hact gσ 𝔪))
  refine ⟨ψ, ?_⟩
  rw [← hψ, act_hom, actC, e, reassoc_of% sigmaι_sigmaIsoOfIso, actc',
    reassoc_of% sigmaι_homSigmaLocal, sigmaι_sigmaIsoOfIso_inv]
  simp only [Category.assoc]

include hβ in
open Classical in
/-- **The component clause of `StrongComponentA`** for the W10 assembly: for a nonzero primitive
idempotent `ε` of `E ⊗_K B` (the unit of a component `𝔪`), the `𝔪`-summand of `c` with its
generic point and the stabiliser action, given semistability, split nodes, no loops,
connectedness of the special fibre and unfoldedness of the summands. -/
theorem component_clause (ϖ' : O') (xB : B)
    (hss : ∀ 𝔪, TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ'
      (projModelCode O' (hg 𝔪)))
    (hsp : ∀ 𝔪, TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ'
      (projModelCode O' (hg 𝔪)))
    (hnl : ∀ 𝔪, TemperedFundamentalGroups.SemistableReduction.ModelCode.NoLoops
      (projModelCode O' (hg 𝔪)))
    (hconn : ∀ 𝔪, ConnectedSpace (specialFibre
      (projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))).toSpec))
    (hunf : ∀ 𝔪, TemperedFundamentalGroups.SemistableReduction.ModelCode.IsUnfolded O'
      (ψ (K := K) (B := B) (E := E) (1 ⊗ₜ xB) 𝔪) (projModelCode O' (hg 𝔪))
      (genericPt O' (hg 𝔪)))
    (ε : TensorProduct K E B) (he : IsIdempotentElem ε) (h0 : ε ≠ 0)
    (hprim : ∀ f : TensorProduct K E B, IsIdempotentElem f → f * ε = 0 ∨ f * ε = ε) :
    ∃ (c₁' : TemperedFundamentalGroups.ModelCode O')
      (c₁ : TemperedFundamentalGroups.ModelCode O)
      (e₁ : c₁.scheme ≅ c₁'.scheme) (ι₁ : c₁.scheme ⟶ (c O O' n hg θ hθ0).scheme)
      (j₁ : Spec (CommRingCat.of (TensorProduct K E B ⧸ Ideal.span {1 - ε})) ⟶ c₁.scheme),
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ' c₁' ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ' c₁' ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.NoLoops c₁' ∧
      e₁.hom ≫ c₁'.toSpec ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap K E).restrict O O' (fun x hx => by
          rw [← hO'] at hx; exact hx))) = c₁.toSpec ∧
      IsOpenImmersion ι₁ ∧ ι₁ ≫ (c O O' n hg θ hθ0).toSpec = c₁.toSpec ∧
      IsSchemeTheoreticallyDominant j₁ ∧
      j₁ ≫ ι₁ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - ε}))) ≫
        jC O O' hO' hn n hg hroot θ hθ0 hθint hθgen ∧
      (∀ gσ : G × (E ≃ₐ[K] E), Algebra.TensorProduct.congr (gσ.2⁻¹)
          (MulSemiringAction.toAlgAut G K B gσ.1⁻¹) ε = ε →
        ∃ ψ : c₁.scheme ⟶ c₁.scheme,
          ψ ≫ ι₁ = ι₁ ≫ (act O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen gσ).hom) ∧
      ConnectedSpace (specialFibre c₁.toSpec) ∧
      ∃ (L₁ : Type u) (_ : Field L₁)
        (_ : Algebra (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁)
        (_ : IsFractionRing (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁)
        (_ : Algebra E L₁) (_ : Algebra O' L₁) (_ : IsScalarTower O' E L₁)
        (j₁' : Spec (CommRingCat.of L₁) ⟶ c₁'.scheme),
        algebraMap E L₁ = (algebraMap (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁).comp
          ((Ideal.Quotient.mk (Ideal.span {1 - ε})).comp
            Algebra.TensorProduct.includeLeftRingHom) ∧
        TemperedFundamentalGroups.SemistableReduction.ModelCode.IsUnfolded O'
          (algebraMap (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁
            (Ideal.Quotient.mk _ (1 ⊗ₜ xB))) c₁' j₁' ∧
        j₁' = Spec.map (CommRingCat.ofHom
          (algebraMap (TensorProduct K E B ⧸ Ideal.span {1 - ε}) L₁)) ≫ j₁ ≫ e₁.hom := by
  obtain ⟨𝔪, h𝔪⟩ := exists_component hn he h0 hprim
  letI algQ : Algebra (TensorProduct K E B ⧸ Ideal.span {1 - ε}) (Comp K E B 𝔪) :=
    ((D K E B 𝔪).subtype.comp (Qequiv hn h𝔪).toRingHom).toAlgebra
  have halgQ : ∀ z, algebraMap (TensorProduct K E B ⧸ Ideal.span {1 - ε}) (Comp K E B 𝔪)
      (Ideal.Quotient.mk _ z) =
      ψ (K := K) (B := B) (E := E) z 𝔪 := fun z => rfl
  haveI : IsFractionRing (TensorProduct K E B ⧸ Ideal.span {1 - ε}) (Comp K E B 𝔪) := by
    haveI := isFractionRing_D (K := K) (B := B) (E := E) 𝔪
    haveI : FaithfulSMul (TensorProduct K E B ⧸ Ideal.span {1 - ε}) (Comp K E B 𝔪) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2
      (Subtype.val_injective.comp (Qequiv hn h𝔪).injective)
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D K E B 𝔪) z
    refine ⟨(Qequiv hn h𝔪).symm a, (Qequiv hn h𝔪).symm b, ?_⟩
    change _ = ((Qequiv hn h𝔪 ((Qequiv hn h𝔪).symm a) : D K E B 𝔪) : Comp K E B 𝔪) /
      ((Qequiv hn h𝔪 ((Qequiv hn h𝔪).symm b) : D K E B 𝔪) : Comp K E B 𝔪)
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rfl
  refine ⟨projModelCode O' (hg 𝔪),
    projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪)),
    eComp O O' hO' n hg θ hθ0 hθint hθgen 𝔪, ModelCode.sigmaι (fun 𝔪 ↦ projModelCode O
      (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))) 𝔪,
    j₁ O O' hO' hn n hg hroot θ hθ0 hθint hθgen h𝔪, hss 𝔪, hsp 𝔪, hnl 𝔪,
    eComp_toSpec O O' hO' n hg θ hθ0 hθint hθgen 𝔪, inferInstance,
    ModelCode.sigmaι_toSpec (fun 𝔪 ↦ projModelCode O
      (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))) 𝔪, inferInstance,
    j₁_sigmaι O O' hO' hn n hg hroot θ hθ0 hθint hθgen h𝔪,
    fun gσ hfix => exists_stab_act O O' hO' n hg θ hθ0 hθint hθgen β hσO' hact gσ
      (πh_eq_of_fix hn β hβ h𝔪 gσ hfix), hconn 𝔪, Comp K E B 𝔪, inferInstance, algQ,
    inferInstance, inferInstance, inferInstance, inferInstance, genericPt O' (hg 𝔪), ?_, ?_, ?_⟩
  · refine RingHom.ext fun e₀ => ?_
    change _ = ψ (K := K) (B := B) (E := E) (e₀ ⊗ₜ 1) 𝔪
    rw [ψ_tmul_one]
  · rw [halgQ]
    exact hunf 𝔪
  · have : CommRingCat.ofHom (Qequiv hn h𝔪).symm.toRingHom ≫
        CommRingCat.ofHom (algebraMap (TensorProduct K E B ⧸ Ideal.span {1 - ε})
          (Comp K E B 𝔪)) = CommRingCat.ofHom (D K E B 𝔪).subtype := by
      ext z
      change (((Qequiv hn h𝔪) ((Qequiv hn h𝔪).symm z) : D K E B 𝔪) : Comp K E B 𝔪) = z
      rw [RingEquiv.apply_symm_apply]
    simp only [j₁, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Spec.map_comp_assoc, this, SpecMap_subtype_homC]

end Stab

end Clause

end W10Assembly

end SemistableReduction
