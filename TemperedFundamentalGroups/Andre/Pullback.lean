/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TheoremA

/-!
# Pulling back tempered coverings along morphisms of levels with models

Blueprint §10. Let `ℓ : Lv' ⟶ Lv` be a morphism of levels with models whose model morphism is
equivariant (`LevelHom.IsEquivariant`, field (iv) of `LevelHom.IsRefinement`), and let `P` be an
`H`-equivariant covering space of the special fibre `Z` of `Lv`. The fibre product
`P' = Z' ×_Z P` along the induced map `ψ_s : Z' → Z` of special fibres is an `H'`-equivariant
covering space of `Z'`, coded inside `Z' × ℕ` (`CoveringCode.pullback`).

## Main results

* `IsCoveringMap.fibreProd_fst`: the pullback of a covering map along a continuous map is a
  covering map.
* `CoveringCode.pullback`, `CoveringCode.pullbackFst`, `CoveringCode.pullbackLift`: the pullback
  of an equivariant covering code, its projection and its universal property.
* `TempObj.pullbackObj ℓ hℓ P`, `TempObj.pullbackHom ℓ hℓ P : pullbackObj ℓ hℓ P ⟶ ⟨Lv, P⟩`: the
  pullback in the tempered category.
* `TempObj.bijective_pullbackHom`: along a refinement, the fibre functor maps `pullbackHom` to a
  bijection.
* `TempObj.pullbackLift`, `TempObj.pullbackLift_comp`, `TempObj.pullbackHom_ext`: the universal
  property of `pullbackHom` among morphisms with prescribed level and model components.
* `TempObj.isCartesianHom_pullbackHom`: `pullbackHom` is cartesian (`IsCartesianHom`).
* `TempObj.pullbackIdIso`: pulling back along the identity gives an isomorphic object.
* `pullback_input`: the field `AndreInput.pullback` of Theorem A.
* `LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant`: the model morphism is automatically
  equivariant when `j'` is scheme-theoretically dominant (the models are separated).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology

namespace TemperedFundamentalGroups

section FibreProd

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]

/-- **The pullback of a covering map** `f : E → X` along a continuous map `g : Y → X` is a
covering map: the first projection `Y ×_X E → Y` of the topological fibre product. -/
theorem IsCoveringMap.fibreProd_fst {f : E → X} (hf : IsCoveringMap f) {g : Y → X}
    (hg : Continuous g) : IsCoveringMap (fun x : {x : Y × E // g x.1 = f x.2} => x.1.1) := by
  intro y
  obtain ⟨hI, U, hyU, hU, hfU, H, hH⟩ := hf (g y)
  have hfst : Continuous (fun x : {x : Y × E // g x.1 = f x.2} => x.1.1) := by fun_prop
  have hmem : ∀ x : (fun x : {x : Y × E // g x.1 = f x.2} => x.1.1) ⁻¹' (g ⁻¹' U),
      x.1.1.2 ∈ f ⁻¹' U := fun x => by
    change f x.1.1.2 ∈ U
    rw [← x.1.2]
    exact x.2
  have hHf : ∀ p : U × _, f (H.symm p).1 = p.1.1 := fun p => by
    rw [← hH, H.apply_symm_apply]
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := f ⁻¹' {g y})
    ⟨hI, g ⁻¹' U, hyU, hU.preimage hg, (hU.preimage hg).preimage hfst,
    { toFun := fun x => (⟨x.1.1.1, x.2⟩, (H ⟨x.1.1.2, hmem x⟩).2)
      invFun := fun p => ⟨⟨(p.1.1, (H.symm (⟨g p.1.1, p.1.2⟩, p.2)).1),
        (hHf (⟨g p.1.1, p.1.2⟩, p.2)).symm⟩, p.1.2⟩
      left_inv := fun x => ?_
      right_inv := fun p => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun _ => rfl⟩
  · have e : ((⟨g x.1.1.1, x.2⟩ : U), (H ⟨x.1.1.2, hmem x⟩).2) = H ⟨x.1.1.2, hmem x⟩ :=
      Prod.ext (Subtype.ext (by rw [hH]; exact x.1.2)) rfl
    apply Subtype.ext; apply Subtype.ext
    simp only
    rw [e, H.symm_apply_apply]
  · simp
  · refine Continuous.prodMk (Continuous.subtype_mk (by fun_prop) _) ?_
    exact continuous_snd.comp (H.continuous.comp (Continuous.subtype_mk (by fun_prop) _))
  · refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk (by fun_prop) ?_) _) _
    refine continuous_subtype_val.comp (H.symm.continuous.comp (Continuous.prodMk ?_ ?_))
    · exact Continuous.subtype_mk (hg.comp (by fun_prop)) _
    · fun_prop

end FibreProd

namespace CoveringCode

variable {Z : Type u} [TopologicalSpace Z] {G : Type u} [Group G] {ρ : G →* (Z ≃ₜ Z)}
  {Z' : Type u} [TopologicalSpace Z'] {G' : Type u} [Group G'] {ρ' : G' →* (Z' ≃ₜ Z')}

section Carrier

variable (P : CoveringCode ρ) (ψ : Z' → Z)

/-- The points `(z', n)` of `Z' × ℕ` with `(ψ z', n) ∈ P`: the fibre product `Z' ×_Z P`, coded. -/
def pullbackCarrier : Set (Z' × ℕ) := {x | (ψ x.1, x.2) ∈ P.carrier}

/-- The point of `P` under a point of the pullback. -/
def pullbackPt (x : pullbackCarrier P ψ) : P.carrier := ⟨(ψ x.1.1, x.1.2), x.2⟩

/-- The topological fibre product `Z' ×_Z P`. -/
abbrev FibreProd : Type u := {x : Z' × P.carrier // ψ x.1 = P.proj x.2}

/-- The coded pullback is in bijection with the topological fibre product. -/
def pullbackEquiv : pullbackCarrier P ψ ≃ FibreProd P ψ where
  toFun x := ⟨(x.1.1, pullbackPt P ψ x), rfl⟩
  invFun y := ⟨(y.1.1, y.1.2.1.2), by
    change (ψ y.1.1, y.1.2.1.2) ∈ P.carrier
    rw [y.2]
    exact y.1.2.2⟩
  left_inv _ := rfl
  right_inv y := Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext y.2 rfl)))

/-- The topology on the coded pullback, making it homeomorphic to the fibre product. -/
@[implicit_reducible]
def pullbackTop : TopologicalSpace (pullbackCarrier P ψ) :=
  TopologicalSpace.induced (pullbackEquiv P ψ) inferInstance

omit [TopologicalSpace Z'] in
lemma pullback_ext {x y : pullbackCarrier P ψ} (h₁ : x.1.1 = y.1.1) (h₂ : x.1.2 = y.1.2) :
    x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

end Carrier

section Pullback

variable (P : CoveringCode ρ) {ψ : Z' → Z}

/-- The coded pullback is homeomorphic to the fibre product. -/
def pullbackHomeomorph (ψ : Z' → Z) :
    @Homeomorph (pullbackCarrier P ψ) (FibreProd P ψ) (pullbackTop P ψ) _ :=
  @Equiv.toHomeomorphOfIsInducing _ _ (pullbackTop P ψ) _ (pullbackEquiv P ψ)
    (IsInducing.induced _)

lemma continuous_pullback_iff {T : Type*} [TopologicalSpace T] {f : T → pullbackCarrier P ψ} :
    Continuous[_, pullbackTop P ψ] f ↔ Continuous (fun t => (pullbackEquiv P ψ (f t)).1) :=
  continuous_induced_rng.trans
    ⟨fun h => continuous_subtype_val.comp h, fun h => Continuous.subtype_mk h _⟩

lemma continuous_pullbackEquiv : Continuous[pullbackTop P ψ, _] (pullbackEquiv P ψ) :=
  continuous_induced_dom

lemma continuous_pullback_fst :
    Continuous[pullbackTop P ψ, _] (fun x : pullbackCarrier P ψ => x.1.1) :=
  letI := pullbackTop P ψ
  (continuous_fst.comp (continuous_subtype_val.comp (continuous_pullbackEquiv P)) :
    Continuous fun x => (pullbackEquiv P ψ x).1.1)

lemma continuous_pullbackPt : Continuous[pullbackTop P ψ, _] (pullbackPt P ψ) :=
  letI := pullbackTop P ψ
  (continuous_snd.comp (continuous_subtype_val.comp (continuous_pullbackEquiv P)) :
    Continuous fun x => (pullbackEquiv P ψ x).1.2)

lemma isCoveringMap_pullback (hψ : Continuous ψ) :
    @IsCoveringMap _ _ (pullbackTop P ψ) _ (fun x : pullbackCarrier P ψ => x.1.1) :=
  @IsCoveringMap.comp_homeomorph _ _ _ _ _ (IsCoveringMap.fibreProd_fst P.isCoveringMap hψ) _
    (pullbackTop P ψ) (pullbackHomeomorph P ψ)

/-- A map into the coded pullback from compatible maps to `Z'` and to `P`. -/
def pullbackLiftFun {Q : Type*} (μ : Q → Z') (k : Q → P.carrier) (hk : ∀ q, (k q).1.1 = ψ (μ q))
    (q : Q) : pullbackCarrier P ψ :=
  ⟨(μ q, (k q).1.2), by
    change (ψ (μ q), (k q).1.2) ∈ P.carrier
    rw [← hk]
    exact (k q).2⟩

omit [TopologicalSpace Z'] in
lemma pullbackPt_liftFun {Q : Type*} (μ : Q → Z') (k : Q → P.carrier)
    (hk : ∀ q, (k q).1.1 = ψ (μ q)) (q : Q) :
    pullbackPt P ψ (pullbackLiftFun P μ k hk q) = k q :=
  Subtype.ext (Prod.ext (hk q).symm rfl)

lemma continuous_pullbackLiftFun {Q : Type*} [TopologicalSpace Q] {μ : Q → Z'}
    {k : Q → P.carrier} (hk : ∀ q, (k q).1.1 = ψ (μ q)) (hμ : Continuous μ)
    (hkc : Continuous k) : Continuous[_, pullbackTop P ψ] (pullbackLiftFun P μ k hk) := by
  refine (continuous_pullback_iff P).2 ?_
  change Continuous fun q => (μ q, pullbackPt P ψ (pullbackLiftFun P μ k hk q))
  simp_rw [pullbackPt_liftFun]
  exact hμ.prodMk hkc

variable (r : G' →* G) (hρ : ∀ g z, ψ (ρ' g z) = ρ (r g) (ψ z))
include hρ

/-- The action of `G'` on the coded pullback: `(z', p) ↦ (g • z', r g • p)`. -/
def pullbackActFun (g : G') (x : pullbackCarrier P ψ) : pullbackCarrier P ψ :=
  ⟨(ρ' g x.1.1, (P.act (r g) (pullbackPt P ψ x)).1.2), by
    have h : ψ (ρ' g x.1.1) = (P.act (r g) (pullbackPt P ψ x)).1.1 := by
      rw [hρ, P.act_fst]; rfl
    change (ψ (ρ' g x.1.1), (P.act (r g) (pullbackPt P ψ x)).1.2) ∈ P.carrier
    rw [h]
    exact (P.act (r g) (pullbackPt P ψ x)).2⟩

lemma pullbackPt_actFun (g : G') (x : pullbackCarrier P ψ) :
    pullbackPt P ψ (pullbackActFun P r hρ g x) = P.act (r g) (pullbackPt P ψ x) :=
  Subtype.ext (Prod.ext (by
    change ψ (ρ' g x.1.1) = _
    rw [hρ, P.act_fst]
    rfl) rfl)

lemma pullbackActFun_one (x : pullbackCarrier P ψ) : pullbackActFun P r hρ 1 x = x :=
  pullback_ext P ψ (by simp [pullbackActFun]) (by simp [pullbackActFun, pullbackPt])

lemma pullbackActFun_mul (g h : G') (x : pullbackCarrier P ψ) :
    pullbackActFun P r hρ (g * h) x = pullbackActFun P r hρ g (pullbackActFun P r hρ h x) := by
  refine pullback_ext P ψ (by simp [pullbackActFun]) ?_
  change (P.act (r (g * h)) _).1.2 =
    (P.act (r g) (pullbackPt P ψ (pullbackActFun P r hρ h x))).1.2
  rw [pullbackPt_actFun, map_mul, map_mul, Homeomorph.mul_apply]

lemma continuous_pullbackActFun (g : G') :
    Continuous[pullbackTop P ψ, pullbackTop P ψ] (pullbackActFun P r hρ g) := by
  letI := pullbackTop P ψ
  rw [continuous_pullback_iff]
  refine Continuous.prodMk ((ρ' g).continuous.comp (continuous_pullback_fst P)) ?_
  change Continuous[pullbackTop P ψ, _] fun x => pullbackPt P ψ (pullbackActFun P r hρ g x)
  simp_rw [pullbackPt_actFun]
  exact (P.act (r g)).continuous.comp (continuous_pullbackPt P)

/-- **The pullback** `Z' ×_Z P` of an equivariant covering code `P` along an equivariant
continuous map `ψ : Z' → Z` (equivariant along `r : G' →* G`), coded inside `Z' × ℕ`. -/
def pullback (hψ : Continuous ψ) : CoveringCode ρ' :=
  letI := pullbackTop P ψ
  { carrier := pullbackCarrier P ψ
    top := pullbackTop P ψ
    isCoveringMap := isCoveringMap_pullback P hψ
    act :=
      { toFun g :=
          { toFun := pullbackActFun P r hρ g
            invFun := pullbackActFun P r hρ g⁻¹
            left_inv x := by rw [← pullbackActFun_mul, inv_mul_cancel, pullbackActFun_one]
            right_inv x := by rw [← pullbackActFun_mul, mul_inv_cancel, pullbackActFun_one]
            continuous_toFun := continuous_pullbackActFun P r hρ g
            continuous_invFun := continuous_pullbackActFun P r hρ g⁻¹ }
        map_one' := Homeomorph.ext fun x => pullbackActFun_one P r hρ x
        map_mul' g h := Homeomorph.ext fun x => pullbackActFun_mul P r hρ g h x }
    act_fst _ _ := rfl }

end Pullback

section PullbackHom

variable (P : CoveringCode ρ) {ψ : Z' → Z} (r : G' →* G) (hρ : ∀ g z, ψ (ρ' g z) = ρ (r g) (ψ z))
  (hψ : Continuous ψ)

lemma pullback_act_fst (g : G') (x : (P.pullback r hρ hψ).carrier) :
    ((P.pullback r hρ hψ).act g x).1.1 = ρ' g x.1.1 := rfl

lemma pullback_act_snd (g : G') (x : (P.pullback r hρ hψ).carrier) :
    ((P.pullback r hρ hψ).act g x).1.2 = (P.act (r g) (pullbackPt P ψ x)).1.2 := rfl

lemma pullbackPt_act (g : G') (x : (P.pullback r hρ hψ).carrier) :
    pullbackPt P ψ ((P.pullback r hρ hψ).act g x) = P.act (r g) (pullbackPt P ψ x) :=
  pullbackPt_actFun P r hρ g x

/-- The projection `Z' ×_Z P → P`, a morphism of covering codes over `ψ`. -/
def pullbackFst : Hom (P.pullback r hρ hψ) P ψ r where
  toFun := pullbackPt P ψ
  continuous_toFun := continuous_pullbackPt P
  fst_toFun _ := rfl
  toFun_act := pullbackPt_act P r hρ hψ

variable {Z'' : Type u} [TopologicalSpace Z''] {G'' : Type u} [Group G'']
  {ρ'' : G'' →* (Z'' ≃ₜ Z'')} (Q : CoveringCode ρ'') {μ : Z'' → Z'} {r' : G'' →* G'}

/-- **The universal property of the pullback**: a morphism `Q → P` over `ψ ∘ μ` factors through
`Z' ×_Z P`, for an equivariant continuous `μ : Z'' → Z'`. -/
def pullbackLift (hμ : Continuous μ) (hμρ : ∀ g z, μ (ρ'' g z) = ρ' (r' g) (μ z))
    (k : Hom Q P (ψ ∘ μ) (r.comp r')) : Hom Q (P.pullback r hρ hψ) μ r' where
  toFun := pullbackLiftFun P (fun q => μ q.1.1) k.toFun k.fst_toFun
  continuous_toFun :=
    continuous_pullbackLiftFun P (μ := fun q => μ q.1.1) k.fst_toFun
      (by exact hμ.comp Q.continuous_proj) k.continuous_toFun
  fst_toFun _ := rfl
  toFun_act g q := by
    refine pullback_ext P ψ ?_ ?_
    · change μ (Q.act g q).1.1 = ρ' (r' g) (μ q.1.1)
      rw [Q.act_fst, hμρ]
    · rw [pullback_act_snd, pullbackPt_liftFun]
      change (k.toFun (Q.act g q)).1.2 = _
      rw [k.toFun_act]
      rfl

lemma pullbackLift_comp (hμ : Continuous μ) (hμρ : ∀ g z, μ (ρ'' g z) = ρ' (r' g) (μ z))
    (k : Hom Q P (ψ ∘ μ) (r.comp r')) (q : Q.carrier) :
    (pullbackFst P r hρ hψ).toFun ((pullbackLift P r hρ hψ Q hμ hμρ k).toFun q) = k.toFun q :=
  pullbackPt_liftFun P (fun q : Q.carrier => μ q.1.1) k.toFun k.fst_toFun q

/-- Morphisms into the pullback are determined by their composite with the projection. -/
lemma pullback_hom_ext {r₁ r₂ : G'' →* G'} (l₁ : Hom Q (P.pullback r hρ hψ) μ r₁)
    (l₂ : Hom Q (P.pullback r hρ hψ) μ r₂)
    (h : ∀ q, pullbackPt P ψ (l₁.toFun q) = pullbackPt P ψ (l₂.toFun q)) :
    l₁.toFun = l₂.toFun :=
  funext fun q => pullback_ext P ψ (by rw [l₁.fst_toFun, l₂.fst_toFun])
    (congrArg (fun y : P.carrier => y.1.2) (h q))

end PullbackHom

end CoveringCode

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace LevelHom

variable {Lv' Lv : Level O R A} (ℓ : LevelHom O R A Lv' Lv)

/-- The map of special fibres `ψ_s : Z' → Z` induced by a morphism of levels with models. -/
def ψs : Lv'.Z → Lv.Z := specialFibreMap ℓ.ψ ℓ.ψ_toSpec

lemma coe_ψs (z : Lv'.Z) : (ℓ.ψs z : Lv.c.scheme) = ℓ.ψ (z : Lv'.c.scheme) :=
  coe_specialFibreMap _ _ _

lemma continuous_ψs : Continuous ℓ.ψs := continuous_specialFibreMap _ _

variable {ℓ} in
/-- An equivariant morphism of levels with models is equivariant on special fibres. -/
lemma IsEquivariant.ψs_ρs (hℓ : ℓ.IsEquivariant) (h' : Lv'.L.H) (z : Lv'.Z) :
    ℓ.ψs (Lv'.ρs h' z) = Lv.ρs (ℓ.φ.r h') (ℓ.ψs z) := by
  apply Subtype.ext
  rw [coe_ψs, Level.ρs_apply, Level.ρs_apply, coe_ψs, ← Scheme.Hom.comp_apply, hℓ h',
    Scheme.Hom.comp_apply]

omit [Algebra K Ω] [IsScalarTower K R Ω] in
variable {ℓ} in
lemma IsRefinement.isEquivariant (hR : ℓ.IsRefinement Ω) : ℓ.IsEquivariant := hR.equivariant

/-- The specialization of geometric points is compatible with morphisms of levels with models. -/
lemma ψ_sp (t : Lv'.L.B →ₐ[R] Ω) :
    ℓ.ψ (Lv'.sp V hV t : Lv'.c.scheme) = (Lv.sp V hV (t.comp ℓ.φ.f) : Lv.c.scheme) := by
  unfold Level.sp
  rw [← coe_sp_comp (hV := hV) ℓ.ψ ℓ.ψ_toSpec]
  congr 2
  rw [Level.point, Level.point, Category.assoc, ℓ.j_ψ, ← Category.assoc, ← Spec.map_comp]
  rfl

end LevelHom

namespace TempObj

variable {Lv' Lv : Level O R A} (ℓ : LevelHom O R A Lv' Lv) (hℓ : ℓ.IsEquivariant)
  (P : CoveringCode Lv.ρs)

/-- **The pullback** of the tempered covering `(Lv, P)` along an equivariant morphism of levels
with models `ℓ : Lv' ⟶ Lv`: the level `Lv'` with the covering `Z' ×_Z P` of its special fibre. -/
def pullbackObj : TempObj O R A :=
  ⟨Lv', P.pullback ℓ.φ.r hℓ.ψs_ρs ℓ.continuous_ψs⟩

/-- **The cartesian morphism** `pullbackObj ℓ hℓ P ⟶ (Lv, P)`, with components `ℓ` and the
projection `Z' ×_Z P → P`. -/
def pullbackHom : Hom (pullbackObj ℓ hℓ P) (⟨Lv, P⟩ : TempObj O R A) where
  φ := ℓ.φ
  ψ := ℓ.ψ
  ψ_toSpec := ℓ.ψ_toSpec
  j_ψ := ℓ.j_ψ
  h := CoveringCode.pullbackPt P ℓ.ψs
  continuous_h := CoveringCode.continuous_pullbackPt P
  fst_h x := ℓ.coe_ψs x.1.1
  h_act := CoveringCode.pullbackPt_actFun P ℓ.φ.r hℓ.ψs_ρs

@[simp] lemma ofTempHom_pullbackHom : LevelHom.ofTempHom (pullbackHom ℓ hℓ P) = ℓ := rfl

lemma pullbackHom_h (x : (pullbackObj ℓ hℓ P).P.carrier) :
    (pullbackHom ℓ hℓ P).h x = CoveringCode.pullbackPt P ℓ.ψs x := rfl

variable {ℓ hℓ P}

section Lift

variable {W : TempObj O R A} {μ : LevelHom O R A W.Lv Lv'} (hμ : μ.IsEquivariant)
  {g : W ⟶ ⟨Lv, P⟩} (hg : LevelHom.ofTempHom g = μ.comp ℓ)

include hg in
lemma pullbackLift_aux (x : W.P.carrier) : (g.h x).1.1 = ℓ.ψs (μ.ψs x.1.1) := by
  have hψ : g.ψ = μ.ψ ≫ ℓ.ψ := congrArg LevelHom.ψ hg
  apply Subtype.ext
  rw [g.fst_h, hψ, Scheme.Hom.comp_apply, LevelHom.coe_ψs, LevelHom.coe_ψs]

variable (hℓ) in
/-- **The universal property of `pullbackHom`**: a morphism `g : W ⟶ (Lv, P)` whose level and
model components are those of `μ ≫ ℓ`, for an equivariant `μ`, factors through the pullback. -/
def pullbackLift : Hom W (pullbackObj ℓ hℓ P) where
  φ := μ.φ
  ψ := μ.ψ
  ψ_toSpec := μ.ψ_toSpec
  j_ψ := μ.j_ψ
  h := CoveringCode.pullbackLiftFun P (fun x => μ.ψs x.1.1) g.h (pullbackLift_aux hg)
  continuous_h := CoveringCode.continuous_pullbackLiftFun P (pullbackLift_aux hg)
    (by exact μ.continuous_ψs.comp W.P.continuous_proj) g.continuous_h
  fst_h x := μ.coe_ψs x.1.1
  h_act a x := by
    refine CoveringCode.pullback_ext P ℓ.ψs ?_ ?_
    · change μ.ψs (W.P.act a x).1.1 = Lv'.ρs (μ.φ.r a) (μ.ψs x.1.1)
      rw [W.P.act_fst, hμ.ψs_ρs]
    · have hφ : g.φ = μ.φ ≫ ℓ.φ := congrArg LevelHom.φ hg
      change (g.h (W.P.act a x)).1.2 = (P.act (ℓ.φ.r (μ.φ.r a)) (CoveringCode.pullbackPt P ℓ.ψs
        (CoveringCode.pullbackLiftFun P (fun x => μ.ψs x.1.1) g.h (pullbackLift_aux hg) x))).1.2
      rw [CoveringCode.pullbackPt_liftFun, g.h_act, hφ]
      rfl

@[simp] lemma ofTempHom_pullbackLift :
    LevelHom.ofTempHom (pullbackLift hℓ hμ hg) = μ := rfl

@[reassoc (attr := simp)]
lemma pullbackLift_comp : pullbackLift hℓ hμ hg ≫ pullbackHom ℓ hℓ P = g :=
  Hom.ext (congrArg LevelHom.φ hg).symm (congrArg LevelHom.ψ hg).symm
    (funext (CoveringCode.pullbackPt_liftFun P _ _ (pullbackLift_aux hg)))

end Lift

/-- Morphisms into the pullback are determined by their level and model components and their
composite with `pullbackHom`. -/
lemma pullbackHom_ext {W : TempObj O R A} {k₁ k₂ : W ⟶ pullbackObj ℓ hℓ P} (hφ : k₁.φ = k₂.φ)
    (hψ : k₁.ψ = k₂.ψ) (h : k₁ ≫ pullbackHom ℓ hℓ P = k₂ ≫ pullbackHom ℓ hℓ P) : k₁ = k₂ :=
  Hom.ext hφ hψ (funext fun x => CoveringCode.pullback_ext P ℓ.ψs
    (Subtype.ext (by rw [k₁.fst_h, k₂.fst_h, hψ]))
    (congrArg (fun y : P.carrier => y.1.2) (congrFun (congrArg Hom.h h) x)))

variable (ℓ hℓ P)

/-- `pullbackHom` is cartesian. -/
lemma isCartesianHom_pullbackHom : IsCartesianHom (pullbackHom ℓ hℓ P) :=
  fun _ _ hμ _ hg => ⟨pullbackLift hℓ hμ hg, rfl, pullbackLift_comp hμ hg⟩

/-- **`Φ`-bijectivity**: along a refinement, the fibre functor maps the pullback morphism to a
bijection. -/
theorem bijective_pullbackHom (hR : ℓ.IsRefinement Ω) :
    Function.Bijective ((tempFibre O R A V hV).map (pullbackHom ℓ hℓ P)) := by
  change Function.Bijective (fibreMap V hV (pullbackHom ℓ hℓ P))
  constructor
  · intro a b hab
    obtain ⟨q₁, rfl⟩ := Quotient.mk_surjective a
    obtain ⟨q₂, rfl⟩ := Quotient.mk_surjective b
    obtain ⟨g, hg⟩ := Quotient.exact hab
    obtain ⟨h', hh'⟩ : ∃ h' : (pullbackObj ℓ hℓ P).Lv.L.H0, (ℓ.φ.r h'.1 : Lv.L.H) = g :=
      hR.surj_H0 g
    set m := pullbackHom ℓ hℓ P
    have h₃ : preMap V hV m (h' • q₂) = preMap V hV m q₁ := by
      rw [preMap_smul, ← hg]
      congr 1
      exact Subtype.ext hh'
    have e₁ : (h' • q₂).1.1.comp ℓ.φ.f = q₁.1.1.comp ℓ.φ.f := congrArg (fun q => q.1.1) h₃
    have e₂ : CoveringCode.pullbackPt P ℓ.ψs (h' • q₂).1.2 =
        CoveringCode.pullbackPt P ℓ.ψs q₁.1.2 := congrArg (fun q => q.1.2) h₃
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k : (pullbackObj ℓ hℓ P).Lv.L.H0, ℓ.φ.r k.1 = 1 ∧
        FiniteLevel.fibreAct Ω (pullbackObj ℓ hℓ P).Lv.L k (h' • q₂).1.1 = q₁.1.1 :=
      hR.trans_fibre _ _ e₁
    have hk : k • h' • q₂ = q₁ := by
      refine Subtype.ext (Prod.ext hk₂ (CoveringCode.pullback_ext P ℓ.ψs ?_ ?_))
      · apply Subtype.ext
        have h1 := Level.sp_fibreAct V hV (pullbackObj ℓ hℓ P).Lv k (h' • q₂).1.1
        rw [hk₂, ← (h' • q₂).2, ← q₁.2] at h1
        exact (Level.ρs_apply _ _ _).trans h1.symm
      · change (P.act (ℓ.φ.r k.1) (CoveringCode.pullbackPt P ℓ.ψs (h' • q₂).1.2)).1.2 = _
        rw [hk₁, e₂, map_one]
        rfl
    exact Quotient.sound ⟨k * h', by simp only [mul_smul, hk]⟩
  · intro b
    obtain ⟨q, rfl⟩ := Quotient.mk_surjective b
    obtain ⟨t', ht'⟩ := hR.surj_fibre q.1.1
    have hz : ℓ.ψs (Lv'.sp V hV t') = q.1.2.1.1 :=
      Subtype.ext (by rw [LevelHom.coe_ψs, LevelHom.ψ_sp, ht', q.2])
    let x : (pullbackObj ℓ hℓ P).P.carrier := ⟨(Lv'.sp V hV t', q.1.2.1.2), by
      change (ℓ.ψs _, _) ∈ P.carrier
      rw [hz]
      exact q.1.2.2⟩
    refine ⟨Quotient.mk _ ⟨(t', x), rfl⟩, ?_⟩
    change Quotient.mk _ (preMap V hV _ _) = _
    congr 1
    exact Subtype.ext (Prod.ext ht' (Subtype.ext (Prod.ext hz rfl)))

/-- Pulling back along the identity gives an isomorphic object. -/
def pullbackIdIso (hid : (LevelHom.id Lv).IsEquivariant) (P : CoveringCode Lv.ρs) :
    pullbackObj (LevelHom.id Lv) hid P ≅ (⟨Lv, P⟩ : TempObj O R A) where
  hom := pullbackHom (LevelHom.id Lv) hid P
  inv := pullbackLift hid hid (g := 𝟙 _) (by rw [LevelHom.ofTempHom_id, LevelHom.id_comp])
  hom_inv_id := pullbackHom_ext (Category.comp_id _) (Category.comp_id _) (by
    rw [Category.assoc, pullbackLift_comp, Category.id_comp]
    exact Category.comp_id _)
  inv_hom_id := pullbackLift_comp _ _

end TempObj

variable (O R A) in
/-- **The pullback input for Theorem A** (`AndreInput.pullback`): tempered coverings pull back
along refinements, by a cartesian morphism which is bijective on fibres. -/
theorem pullback_input : ∀ (X : TempObj O R A) (Lv' : Level O R A) (ℓ : LevelHom O R A Lv' X.Lv),
    ℓ.IsRefinement Ω → ∃ (P' : CoveringCode Lv'.ρs) (m : (⟨Lv', P'⟩ : TempObj O R A) ⟶ X),
      LevelHom.ofTempHom m = ℓ ∧ Function.Bijective ((tempFibre O R A V hV).map m) ∧
        IsCartesianHom m :=
  fun X _ ℓ hR => ⟨_, TempObj.pullbackHom ℓ hR.equivariant X.P, rfl,
    TempObj.bijective_pullbackHom V hV ℓ hR.equivariant X.P hR,
    TempObj.isCartesianHom_pullbackHom ℓ hR.equivariant X.P⟩

end

section Dominant

open Limits

/-- Two morphisms `f g : X ⟶ Y` over a separated `s : Y ⟶ Z` agree if they agree after
precomposition with a scheme-theoretically dominant `ι : W ⟶ X`. (Mathlib's
`ext_of_isDominant_of_isSeparated` assumes `X` reduced and `ι` dominant instead.) -/
lemma ext_of_isSchemeTheoreticallyDominant_of_isSeparated {W X Y Z : Scheme.{u}} {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hι : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let W' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g (by exact h.symm)
  let ι' : W' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have hl : ι' ≫ f' = ι' ≫ g' := by ext1; exact hι
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    refine le_bot_iff.1 ?_
    have hc : (equalizer.lift ι' hl).left ≫ (equalizer.ι f' g').left = ι := by
      rw [← Over.comp_left, equalizer.lift_ι]
      rfl
    have hle := Scheme.Hom.le_ker_comp (equalizer.lift ι' hl).left (equalizer.ι f' g').left
    rw [hc] at hle
    exact hle.trans ι.ker_eq_bot.le
  have := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  change f'.left = g'.left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- **Equivariance is automatic** (field (iv) of `LevelHom.IsRefinement`) when `j'` is
scheme-theoretically dominant: the models are separated over `O`. -/
lemma LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant {Lv' Lv : Level O R A}
    (ℓ : LevelHom O R A Lv' Lv) [IsSchemeTheoreticallyDominant Lv'.j] : ℓ.IsEquivariant := by
  intro h'
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated Lv.c.toSpec ?_ Lv'.j ?_
  · rw [Category.assoc, Category.assoc, ℓ.ψ_toSpec, Lv'.ρ_toSpec, Lv.ρ_toSpec, ℓ.ψ_toSpec]
  · rw [← Category.assoc, ← Lv'.ρ_j h', Category.assoc, ℓ.j_ψ, ← Category.assoc, ← Spec.map_comp,
      ← Category.assoc, ℓ.j_ψ, Category.assoc, ← Lv.ρ_j, ← Category.assoc, ← Spec.map_comp]
    congr 2
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    refine RingHom.ext fun y => ?_
    apply (h' : SemilinearAut R A Lv'.L.B).σ.injective
    change (h' : SemilinearAut R A Lv'.L.B).σ ((h' : SemilinearAut R A Lv'.L.B).σ.symm
      (ℓ.φ.f y)) = (h' : SemilinearAut R A Lv'.L.B).σ (ℓ.φ.f
        ((ℓ.φ.r h' : SemilinearAut R A Lv.L.B).σ.symm y))
    rw [RingEquiv.apply_symm_apply, ← ℓ.φ.f_σ, RingEquiv.apply_symm_apply]

end Dominant


end TemperedFundamentalGroups
