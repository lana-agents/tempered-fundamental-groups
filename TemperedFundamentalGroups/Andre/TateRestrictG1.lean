/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictLoop
import TemperedFundamentalGroups.Andre.TateCrossing

/-!
# Generic points and (G1) for the restricted Tate object (Blueprint §10.3.8, `v(q) = 1`)

For a member `Q` with `a : Q.U ⟶ X₀'` (restricted Tate object, `π = √ϖ` over `O' = O_{K(√ϖ)}`):

* `Pres.psiK`: `K' → L₁`, `√ϖ ↦ t`; `Pres.toFR`: the embedding of the function field of the Tate
  curve over `O'` into `L₁` (`TateNormal.toField`, `x` transcendental over `K`, hence over `K'`);
* `Pres.genericR`: `j₁ ≫ e⁻¹ ≫ ψ ≫ isoR = Spec(toFR) ≫ genericPt` (through the chart point
  `jChart`, `TateNormal.SpecMap_jChart_eq`);
* `Pres.psi_surjective_R` **(S1')**: `a.ψ` is surjective (its image is closed and contains the
  generic point of the integral model);
* `TateRestrict.exists_closure_eq_C`, `exists_closure_eq_E`, `exists_two_points`,
  `not_E_eq_singleton`: the 2-gon `C ∪ E'` pulled back along `ΦR`;
* `Pres.exists_image_eq_C_R`, `Pres.exists_tree_tateNuG_R` **(G1')**.
-/

universe u

open CategoryTheory AlgebraicGeometry SemistableReduction.ProjScheme

namespace TemperedFundamentalGroups.TateNormal

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  (π b₄ b₆ : O) [Fact (Squarefree (dpoly π b₄ b₆))]

local notation "L" => TateField π b₄ b₆

variable {M : Type u} [Field M] (ψ : K →+* M) {x y : M} (hπ : ψ (π : K) ≠ 0)
  (heq : y ^ 2 + x * y = x ^ 3 + (ψ.comp O.subtype) (π ^ 2 * b₄) * x +
    (ψ.comp O.subtype) (π ^ 2 * b₆))
  (hx : letI := ψ.toAlgebra; Transcendental K x)

/-- **The chart point through `L`**: a point `Spec M ⟶ Spec T ⟶` (Tate model) of the chart
`w = 1` whose coordinates are those of `toField` is the generic point composed with `toField`. -/
lemma SpecMap_jChart_eq {T : Type u} [CommRing T] (φ : O →+* T) {xT yT : T}
    (heqT : yT ^ 2 + xT * yT = xT ^ 3 + φ (π ^ 2 * b₄) * xT + φ (π ^ 2 * b₆))
    (hπT : IsUnit (φ π)) (hπ0 : π ≠ 0) (g : T →+* M) (hg : g.comp φ = ψ.comp O.subtype)
    (hgx : g xT = x) (hgy : g yT = y) :
    Spec.map (CommRingCat.ofHom g) ≫ jChart π b₄ b₆ φ heqT hπT hπ0 =
      Spec.map (CommRingCat.ofHom (toField π b₄ b₆ ψ hπ heq hx)) ≫
        genericPt O (hcoords π b₄ b₆ hπ0) := by
  rw [genericPt_eq_chartι _ rfl _ 2, jChart, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  have hu : g ↑hπT.unit⁻¹ = (ψ (O.subtype π))⁻¹ := by
    rw [map_units_inv]
    exact congrArg _ (RingHom.congr_fun hg π)
  have key : g.comp (tateHomR π b₄ b₆ φ heqT hπT) =
      tateHom π b₄ b₆ (ψ.comp O.subtype) heq hπ := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun o ↦ ?_) ?_) ?_
    · simp only [RingHom.comp_apply, tateHomR, AdjoinRoot.lift_of, tateHom,
        Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom]
      exact RingHom.congr_fun hg o
    · simp only [RingHom.comp_apply, tateHomR, AdjoinRoot.lift_of, tateHom,
        Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom, map_mul, hgx, div_eq_mul_inv]
      rw [hu]
    · simp only [tateHomR, RingHom.comp_apply, AdjoinRoot.lift_root, tateHom, map_mul, hgy,
        div_eq_mul_inv]
      rw [hu]
  refine RingHom.ext fun z ↦ ?_
  obtain ⟨r, rfl⟩ := (chartTwoEquiv π b₄ b₆).surjective z
  simp only [RingHom.comp_apply, chartHomR, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply, Subring.coe_subtype, chartTwoEquiv_apply, toField_algebraMap]
  exact RingHom.congr_fun key r

end

end TemperedFundamentalGroups.TateNormal

namespace TemperedFundamentalGroups

noncomputable section

open TempObj TateRestrict RamifiedQuadratic SemistableReduction.W10Apply CurveConfig

attribute [local instance] TateNormal.algK

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (hϖ : Irreducible ϖ)
  [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero K]
  (b₄ b₆ : O)
  [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)))]
  (R : Type u) [CommRing R] [Algebra K R] {x y : R}
  (heqR : y ^ 2 + x * y = x ^ 3 + algebraMap K R (ϖ * b₄) * x + algebraMap K R (ϖ * b₆))
  (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A] {xW : R}

namespace TateRestrict

include heqR in
lemma jR_isoR : jR hϖ R b₄ b₆ heqR ≫ (isoR hϖ b₄ b₆).hom =
    TateNormal.jChart (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (φB hϖ R)
      (equation_B hϖ R b₄ b₆ heqR) (by rw [φB_sO]; exact isUnit_t hϖ R) (sO_ne_zero hϖ) := by
  rw [jR, jO, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end TateRestrict

namespace Pres

variable {Y : TempObj O R A} (Q : Pres xW Y) {R A}
  (a : Q.U ⟶ TateRestrict.X₀' hϖ b₄ b₆ R heqR A)

/-- `K' → L₁`, `√ϖ ↦ t`, through the level of `X₀'`. -/
def psiK : K' ϖ →+* Q.D.L₁ :=
  (algebraMap Q.Lv.L.B Q.D.L₁).comp (RingHom.comp a.φ.f.toRingHom (κ hϖ R).toRingHom)

lemma psiK_algebraMap (k : K) :
    Q.psiK hϖ b₄ b₆ heqR a (algebraMap K (K' ϖ) k) = Q.rhoL (algebraMap K R k) := by
  simp only [psiK, RingHom.comp_apply, rhoL]
  congr 1
  have h1 : (κ hϖ R).toRingHom (algebraMap K (K' ϖ) k) =
      algebraMap R (BR (ϖ := ϖ) R) (algebraMap K R k) :=
    ((κ hϖ R).commutes k).trans (IsScalarTower.algebraMap_apply K R (BR (ϖ := ϖ) R) k)
  exact (congrArg a.φ.f h1).trans (a.φ.f.commutes _)

lemma psiK_O' (o : O) : Q.psiK hϖ b₄ b₆ heqR a ((sO ϖ ^ 2 * algebraMap O (O' ϖ) o : O' ϖ) : K' ϖ) =
    Q.rhoL (algebraMap K R (ϖ * o)) := by
  have : ((sO ϖ ^ 2 : O' ϖ) : K' ϖ) = algebraMap K (K' ϖ) ϖ := s_sq
  have h2 : ((algebraMap O (O' ϖ) o : O' ϖ) : K' ϖ) = algebraMap K (K' ϖ) o := rfl
  rw [MulMemClass.coe_mul, this, h2, ← map_mul, Q.psiK_algebraMap hϖ b₄ b₆ heqR a]

lemma equation_psiK : Q.rhoL y ^ 2 + Q.rhoL x * Q.rhoL y = Q.rhoL x ^ 3 +
    ((Q.psiK hϖ b₄ b₆ heqR a).comp (O' ϖ).subtype) (sO ϖ ^ 2 * algebraMap O (O' ϖ) b₄) *
      Q.rhoL x + ((Q.psiK hϖ b₄ b₆ heqR a).comp (O' ϖ).subtype)
        (sO ϖ ^ 2 * algebraMap O (O' ϖ) b₆) := by
  rw [RingHom.comp_apply, RingHom.comp_apply]
  erw [psiK_O', psiK_O']
  have := congrArg Q.rhoL heqR
  simp only [map_add, map_mul, map_pow] at this ⊢
  exact this

lemma psiK_sO_ne_zero : Q.psiK hϖ b₄ b₆ heqR a ((sO ϖ : O' ϖ) : K' ϖ) ≠ 0 :=
  (map_ne_zero _).2 fun h ↦ sO_ne_zero hϖ (Subtype.ext h)

variable [IsDomain R]

lemma transcendental_psiK (hx : Transcendental K x) :
    letI := (Q.psiK hϖ b₄ b₆ heqR a).toAlgebra
    Transcendental (K' ϖ) (Q.rhoL x) := by
  letI := Q.D.algKL
  letI := (Q.psiK hϖ b₄ b₆ heqR a).toAlgebra
  haveI : IsScalarTower K (K' ϖ) Q.D.L₁ :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (Q.psiK_algebraMap hϖ b₄ b₆ heqR a k).symm
  let f : R →ₐ[K] Q.D.L₁ := { Q.rhoL with commutes' := fun _ ↦ rfl }
  have h : Transcendental K (Q.rhoL x) := fun h ↦
    hx ((isAlgebraic_algHom_iff f Q.rhoL_injective).1 h)
  exact h.extendScalars (K' ϖ)

/-- The embedding of the function field of the Tate curve over `O'` into `L₁`. -/
abbrev toFR (hx : Transcendental K x) :
    TateNormal.TateField (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) →+* Q.D.L₁ :=
  TateNormal.toField (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)
    (Q.psiK hϖ b₄ b₆ heqR a) (Q.psiK_sO_ne_zero hϖ b₄ b₆ heqR a) (Q.equation_psiK hϖ b₄ b₆ heqR a)
    (Q.transcendental_psiK hϖ b₄ b₆ heqR a hx)

/-- **The generic points are compatible** (restricted Tate object). -/
theorem genericR (hx : Transcendental K x) :
    Q.D.j₁ ≫ Q.D.e.inv ≫ a.ψ ≫ (isoR hϖ b₄ b₆).hom =
      Spec.map (CommRingCat.ofHom (Q.toFR hϖ b₄ b₆ heqR a hx)) ≫
        genericPt (O' ϖ) (TateNormal.hcoords (sO ϖ) (algebraMap O (O' ϖ) b₄)
          (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ)) := by
  have h1 : Q.D.j₁ ≫ Q.D.e.inv ≫ a.ψ ≫ (isoR hϖ b₄ b₆).hom =
      Spec.map (CommRingCat.ofHom (algebraMap Q.Lv.L.B Q.D.L₁)) ≫
        Spec.map (CommRingCat.ofHom a.φ.f.toRingHom) ≫ TateNormal.jChart (sO ϖ)
          (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (φB hϖ R)
          (equation_B hϖ R b₄ b₆ heqR) (by rw [φB_sO]; exact isUnit_t hϖ R) (sO_ne_zero hϖ) := by
    rw [Q.D.hj, ← jR_isoR hϖ b₄ b₆ R heqR]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (Spec.map (CommRingCat.ofHom (algebraMap Q.Lv.L.B Q.D.L₁)) ≫ ·)
      ((reassoc_of% a.j_ψ) (isoR hϖ b₄ b₆).hom)
  rw [h1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine TateNormal.SpecMap_jChart_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl ?_ ?_
  · exact congrArg _ (a.φ.f.commutes x)
  · exact congrArg _ (a.φ.f.commutes y)

/-- **(S1') The model map onto the restricted Tate model is surjective**, when `x` is
transcendental over `K`. -/
theorem psi_surjective_R (hx : Transcendental K x) : Function.Surjective a.ψ := by
  have hdense := (isDominant_genericPt (O := O' ϖ)
    (TateNormal.hcoords (sO ϖ) (algebraMap O (O' ϖ) b₄)
    (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).denseRange
  obtain ⟨η⟩ : Nonempty (Spec (CommRingCat.of Q.D.L₁)) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨z₀, hz₀'⟩ : ∃ z₀, z₀ = a.ψ (Q.D.e.inv (Q.D.j₁ η)) := ⟨_, rfl⟩
  have hz₀ : (isoR hϖ b₄ b₆).hom z₀ = genericPt (O' ϖ) (TateNormal.hcoords (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))
        (Spec.map (CommRingCat.ofHom (Q.toFR hϖ b₄ b₆ heqR a hx)) η) := by
    rw [hz₀']
    have h := congrArg (fun φ ↦ φ η) (Q.genericR hϖ b₄ b₆ heqR a hx)
    simp only [Scheme.Hom.comp_apply] at h
    exact h
  have e : ∀ w, (isoR hϖ b₄ b₆).inv ((isoR hϖ b₄ b₆).hom w) = w := fun w ↦ by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
  have hcl : ∀ z, z ∈ closure {z₀} := fun z ↦ by
    have h1 : (isoR hϖ b₄ b₆).hom z ∈ closure {(isoR hϖ b₄ b₆).hom z₀} := by
      rw [hz₀]
      refine closure_mono ?_ (hdense.closure_eq ▸ Set.mem_univ _)
      rintro _ ⟨p, rfl⟩
      exact congrArg _ (PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans
        (Ideal.eq_bot_of_prime _).symm))
    have h2 := map_mem_closure (isoR hϖ b₄ b₆).inv.continuous h1 (t := {z₀}) (by
      rintro _ rfl
      exact e z₀)
    rwa [e] at h2
  haveI : UniversallyClosed (a.ψ ≫ (TateRestrict.X₀' hϖ b₄ b₆ R heqR A).Lv.c.toSpec) := by
    rw [a.ψ_toSpec]; infer_instance
  haveI : UniversallyClosed a.ψ := UniversallyClosed.of_comp_of_isSeparated a.ψ
    (TateRestrict.X₀' hϖ b₄ b₆ R heqR A).Lv.c.toSpec
  intro z
  exact a.ψ.isClosedMap.isClosed_range.closure_subset_iff.2
    (Set.singleton_subset_iff.2 ⟨_, hz₀'.symm⟩) (hcl z)

omit [Subsingleton A] [IsDomain R] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero K] in
/-- A model map surjective on schemes is surjective on special fibres. -/
lemma tateMapG_surjective_of {X₀ X : TempObj O R A} (P : Pres xW X) (a : X ⟶ X₀)
    (hs : Function.Surjective (P.iso.inv ≫ a).ψ) : Function.Surjective (P.tateMapG a) := by
  intro z
  obtain ⟨u, hu⟩ := hs z.1
  have hu' : u ∈ specialFibre P.Lv.c.toSpec := by
    have h3 : P.U.Lv.c.toSpec u = X₀.Lv.c.toSpec ((P.iso.inv ≫ a).ψ u) := by
      rw [← Scheme.Hom.comp_apply, (P.iso.inv ≫ a).ψ_toSpec]
    exact (mem_specialFibre _ _).2 (h3.trans (hu ▸ (mem_specialFibre _ _).1 z.2))
  exact ⟨⟨u, hu'⟩, Subtype.ext hu⟩

end Pres

namespace TateCovering.Decomp

variable {Z Z' : Type u} [TopologicalSpace Z] [TopologicalSpace Z'] (Φ : Z ≃ₜ Z') (D : Decomp Z')

/-- A generic point of `C` not on `E` pulls back along a homeomorphism. -/
lemma exists_closure_comap_C (h : ∃ z, closure {z} = D.C ∧ z ∉ D.E) :
    ∃ z, closure {z} = (D.comap Φ).C ∧ z ∉ (D.comap Φ).E := by
  obtain ⟨z, hC, hE⟩ := h
  refine ⟨Φ.symm z, ?_, fun h ↦ hE (by
    have h' : Φ (Φ.symm z) ∈ D.E := h
    rwa [Φ.apply_symm_apply] at h')⟩
  rw [← Set.image_singleton, Homeomorph.image_symm, ← Homeomorph.preimage_closure, hC]
  rfl

/-- A generic point of `E` not on `C` pulls back along a homeomorphism. -/
lemma exists_closure_comap_E (h : ∃ z, closure {z} = D.E ∧ z ∉ D.C) :
    ∃ z, closure {z} = (D.comap Φ).E ∧ z ∉ (D.comap Φ).C := by
  obtain ⟨z, hE, hC⟩ := h
  refine ⟨Φ.symm z, ?_, fun h ↦ hC (by
    have h' : Φ (Φ.symm z) ∈ D.C := h
    rwa [Φ.apply_symm_apply] at h')⟩
  rw [← Set.image_singleton, Homeomorph.image_symm, ← Homeomorph.preimage_closure, hE]
  rfl

lemma mem_comap_Cp {z : Z} : z ∈ (D.comap Φ).Cp ↔ Φ z ∈ D.Cp := Iff.rfl

lemma mem_comap_Cq {z : Z} : z ∈ (D.comap Φ).Cq ↔ Φ z ∈ D.Cq := Iff.rfl

end TateCovering.Decomp

namespace TateModel

variable {O : Type u} [CommRing O] [IsLocalRing O] {π b₄ b₆ : O}
  (hπ : π ∈ IsLocalRing.maximalIdeal O)

lemma decomp_C_closure : ∃ z, closure {z} = (decomp (b₄ := b₄) (b₆ := b₆) hπ).C ∧
    z ∉ (decomp (b₄ := b₄) (b₆ := b₆) hπ).E :=
  exists_closure_eq_Cset hπ

lemma decomp_E_closure (hb : IsUnit b₆) :
    ∃ z, closure {z} = (decomp (b₄ := b₄) (b₆ := b₆) hπ).E ∧
      z ∉ (decomp (b₄ := b₄) (b₆ := b₆) hπ).C :=
  exists_closure_eq_Eset hπ hb

lemma decomp_Cp : (decomp (b₄ := b₄) (b₆ := b₆) hπ).Cp = {pZ π b₄ b₆ hπ} := Cp_eq hπ

lemma decomp_Cq : (decomp (b₄ := b₄) (b₆ := b₆) hπ).Cq = {qZ π b₄ b₆ hπ} := Cq_eq hπ

end TateModel

namespace TateRestrict

lemma decompR_eq : decompR hϖ b₄ b₆ = (TateModel.decomp (b₄ := algebraMap O (O' ϖ) b₄)
    (b₆ := algebraMap O (O' ϖ) b₆) (sO_mem hϖ)).comap (ΦR hϖ b₄ b₆) := rfl

/-- **(S2) The line `C` of the restricted special fibre** has a generic point not on `E'`. -/
lemma exists_closure_eq_C : ∃ z, closure {z} = (decompR hϖ b₄ b₆).C ∧
    z ∉ (decompR hϖ b₄ b₆).E := by
  rw [decompR_eq]
  exact TateCovering.Decomp.exists_closure_comap_C _ _ (TateModel.decomp_C_closure _)

/-- The conic `E'` of the restricted special fibre has a generic point not on `C` (`b₆` a
unit). -/
lemma exists_closure_eq_E (hb : IsUnit b₆) : ∃ z, closure {z} = (decompR hϖ b₄ b₆).E ∧
    z ∉ (decompR hϖ b₄ b₆).C := by
  rw [decompR_eq]
  exact TateCovering.Decomp.exists_closure_comap_E _ _ (TateModel.decomp_E_closure _ (hb.map _))

lemma nonempty_Cp : (decompR hϖ b₄ b₆).Cp.Nonempty := by
  rw [decompR_eq]
  exact TateCovering.Decomp.nonempty_comap_Cp _ (by
    rw [TateModel.decomp_Cp]; exact Set.singleton_nonempty _)

lemma nonempty_Cq : (decompR hϖ b₄ b₆).Cq.Nonempty := by
  rw [decompR_eq]
  exact TateCovering.Decomp.nonempty_comap_Cq _ (by
    rw [TateModel.decomp_Cq]; exact Set.singleton_nonempty _)

/-- Two distinct points on `C ∩ E'`. -/
lemma exists_two_points : ∃ p q, p ∈ (decompR hϖ b₄ b₆).C ∩ (decompR hϖ b₄ b₆).E ∧
    q ∈ (decompR hϖ b₄ b₆).C ∩ (decompR hϖ b₄ b₆).E ∧ p ≠ q := by
  obtain ⟨p, hp⟩ := nonempty_Cp hϖ b₄ b₆
  obtain ⟨q, hq⟩ := nonempty_Cq hϖ b₄ b₆
  refine ⟨p, q, (decompR hϖ b₄ b₆).Cp_subset_inter hp, ?_, fun h ↦
    Set.disjoint_left.1 (decompR hϖ b₄ b₆).disjoint hp (h ▸ hq)⟩
  rw [(decompR hϖ b₄ b₆).inter]
  exact Or.inr hq

/-- **The conic `E'` of the restricted special fibre is not a point.** -/
lemma not_E_eq_singleton : ¬ ∃ y, (decompR hϖ b₄ b₆).E = {y} := by
  rintro ⟨y, hy⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_two_points hϖ b₄ b₆
  have hp' := hp.2
  have hq' := hq.2
  rw [hy] at hp' hq'
  exact hpq (hp'.trans hq'.symm)

end TateRestrict

namespace Pres

variable [IsDomain R] {X : TempObj O R A} (P : Pres xW X) {R A}

/-- **(G1') Some component of a member maps onto the line `C` of the restricted Tate model**
(`v(q) = 1`), when `x` is transcendental over `K`. -/
theorem exists_image_eq_C_R (hx : Transcendental K x)
    (a : X ⟶ TateRestrict.X₀' hϖ b₄ b₆ R heqR A) :
    ∃ i : irreducibleComponents P.Lv.Z,
      P.tateMapG a '' (curveConfig P.Lv.Z P.hdim).C i = (decompR hϖ b₄ b₆).C ∧
        P.tateNuG a i := by
  obtain ⟨z, hC, hE⟩ := exists_closure_eq_C hϖ b₄ b₆
  obtain ⟨i, hi⟩ := P.exists_image_eq_closureG a (tateMapG_surjective_of P a
    (P.psi_surjective_R hϖ b₄ b₆ heqR (P.iso.inv ≫ a) hx)) (decompR hϖ b₄ b₆).isClosed_E
    (hC ▸ (decompR hϖ b₄ b₆).union) hE
  replace hi := hi.trans hC
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_two_points hϖ b₄ b₆
  exact ⟨i, hi, P.not_contr_of_image_eqG a hi hp.1 hq.1 hpq⟩

/-- **(G1'), tree form**: a component vertex of the tree of the universal covering of a member
whose component is not contracted over the restricted Tate model. -/
theorem exists_tree_tateNuG_R (hx : Transcendental K x)
    (a : X ⟶ TateRestrict.X₀' hϖ b₄ b₆ R heqR A) :
    ∃ t₁ : (curveConfig P.Lv.Z P.hdim).Tree
        (universalCovering.root P.hdim P.z₀),
      IsComp t₁ ∧ P.tateNuG a (lab t₁) := by
  obtain ⟨i, -, hi⟩ := P.exists_image_eq_C_R hϖ b₄ b₆ heqR hx a
  obtain ⟨t₁, ht, hl⟩ := P.exists_tree_lab_eq i
  exact ⟨t₁, ht, hl ▸ hi⟩

end Pres

end

end TemperedFundamentalGroups
