/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.WHarmonicWeight
import TemperedFundamentalGroups.FibreFunctor.LengthLimit

/-!
# The length function on the Galois objects over W-model levels (Blueprint §10.3.6, items 2–4)

Scheme case. A member `G` of `galClassW O R A Ω (Level.IsW x)` is isomorphic to the Galois object
`U_Lv = universalObj Lv hdim z₀` of a level `Lv` with W-model data `D` (`Pres`: a chosen such
presentation). A point `γ ∈ Φ(U_Lv)` is a pair `(t, p)` of a geometric point `t` of the level
and a point `p` of the universal covering `Z̃` of the special fibre `Z = Lv.Z` over the
specialization of `t` (`H⁰` is trivial); `Pres.vtx γ` is the vertex of the tree of `Z̃` carrying
`p`.

* `lenW ϖ p γ`: for a pointed member `p = (G, g)`, the length (`CurveConfig.tlen`, weights the
  x-lengths `WData.weight`) between the vertices of `g` and `γ`;
* `lenW_self`: `lenW ϖ p p.g = 0`;
* `finite_lenW_le`: finitely many `γ` have length `≤ ℓ₀` for `ℓ₀ ≠ ⊤` (finitely many geometric
  points, finitely many vertices at bounded length: x-lengths of nodes are positive (X0));
* `lenW_map_le`: lengths do not increase along pointed morphisms (`CurveConfig.tlen_map_le`, with
  the harmonic weights of `WData.isHarmonicWeight` and the closedness of model maps).

Inputs: `Statement.HarmonicX` (targeted) and `Statement.NodeOfTwoComponents`
(`SemistableReduction/TwoComponents.lean`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open scoped ENNReal

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) {x : R}

section Closed

/-- Model maps are closed on special fibres (the models are proper over `O`). -/
lemma isClosedMap_specialFibreMap [IsLocalRing O] {X Y : TempObj O R A} (m : X ⟶ Y) :
    IsClosedMap (specialFibreMap m.ψ m.ψ_toSpec) := by
  haveI : UniversallyClosed (m.ψ ≫ Y.Lv.c.toSpec) := by rw [m.ψ_toSpec]; infer_instance
  haveI : UniversallyClosed m.ψ := UniversallyClosed.of_comp_of_isSeparated m.ψ Y.Lv.c.toSpec
  intro C hC
  have hZ : IsClosed (specialFibre X.Lv.c.toSpec) :=
    (IsLocalRing.isClosed_singleton_closedPoint O).preimage X.Lv.c.toSpec.continuous
  have h₁ : IsClosed ((↑) '' C : Set X.Lv.c.scheme) := hZ.isClosedMap_subtype_val _ hC
  have h₂ := m.ψ.isClosedMap _ h₁
  convert h₂.preimage continuous_subtype_val using 1
  ext z
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    exact ⟨y, hy, Subtype.ext hz⟩

end Closed

/-- **A presentation of a member of `galClassW`**: a level with trivial `H` whose special fibre is
a connected curve, W-model data on it, and an isomorphism with its Galois object. -/
structure Pres (x : R) (X : TempObj O R A) where
  /-- The level. -/
  Lv : Level O R A
  [sub : Subsingleton Lv.L.H]
  [noeth : NoetherianSpace Lv.Z]
  [t0 : T0Space Lv.Z]
  [qs : QuasiSober Lv.Z]
  [conn : ConnectedSpace Lv.Z]
  hdim : topologicalKrullDim Lv.Z ≤ 1
  /-- The base point of the universal covering. -/
  z₀ : Lv.Z
  /-- The W-model data. -/
  D : WData x Lv
  /-- The identification with the Galois object. -/
  iso : X ≅ universalObj Lv hdim z₀

attribute [instance] Pres.sub Pres.noeth Pres.t0 Pres.qs Pres.conn

namespace Pres

variable {X : TempObj O R A}

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma nonempty (hX : galClassW O R A Ω (Level.IsW x) X) : Nonempty (Pres x X) := by
  obtain ⟨Lv, _, _, _, _, _, hdim, z₀, hP, -, -, -, -, -, -, ⟨iso⟩⟩ := hX
  obtain ⟨D⟩ := WData.nonempty_of_isW hP
  exact ⟨⟨Lv, hdim, z₀, D, iso⟩⟩

variable (P : Pres x X)

/-- The Galois object. -/
abbrev U : TempObj O R A := universalObj P.Lv P.hdim P.z₀

/-- The universal covering of the special fibre. -/
abbrev E : Type u := universalCovering P.Lv.Z P.hdim P.z₀

/-- The identification `Ind_1^H Z̃ ≃ P(U)`. -/
abbrev Θ' : IndSpace P.Lv P.E ≃ₜ P.U.P.carrier :=
  Θ P.Lv (universalCovering.isUniversalCovering.{u, u, u} P.hdim P.z₀)
    (universalCovering.isUniversalCovering.{u, u, u} P.hdim P.z₀).countable_fibre

/-- The point of the universal covering of a point of the covering space of `U`. -/
def ecov (y : P.U.P.carrier) : P.E := (P.Θ'.symm y).2

lemma Θ'_ecov (y : P.U.P.carrier) : P.Θ' ⟨1, P.ecov y⟩ = y := by
  conv_rhs => rw [← P.Θ'.apply_symm_apply y]
  congr 1
  exact Sigma.ext (Subsingleton.elim _ _) HEq.rfl

lemma ecov_Θ' (e : P.E) : P.ecov (P.Θ' ⟨1, e⟩) = e := by
  simp [ecov]

lemma continuous_ecov : Continuous P.ecov :=
  (continuous_sigma fun _ => continuous_id).comp P.Θ'.symm.continuous

/-- The vertex of the tree of a point of the fibre. -/
def vtx (u : (tempFibre O R A V hV).obj P.U) : (curveConfig P.Lv.Z P.hdim).Tree
    (universalCovering.root P.hdim P.z₀) :=
  (P.ecov (Quotient.out u : PreFibre Ω V hV P.U).1.2).1.2

/-- In the scheme case the representative of a class of the fibre of `U` is the given pair. -/
lemma out_mk (q : PreFibre Ω V hV P.U) :
    (Quotient.out (Quotient.mk _ q : (tempFibre O R A V hV).obj P.U) :
      PreFibre Ω V hV P.U) = q := by
  have h := Quotient.mk_out (s := MulAction.orbitRel P.U.Lv.L.H0 (PreFibre Ω V hV P.U)) q
  obtain ⟨g, hg⟩ := h
  have hg1 : g = 1 := Subtype.ext (@Subsingleton.elim _ P.sub _ _)
  subst hg1
  exact hg.symm.trans (one_smul _ q)

end Pres

section Map

variable {X Y : TempObj O R A} (P : Pres x X) (Q : Pres x Y)

/-- The map of universal coverings induced by a morphism of Galois objects. -/
def covMap (m : P.U ⟶ Q.U) (e : P.E) : Q.E := Q.ecov (m.h (P.Θ' ⟨1, e⟩))

lemma continuous_covMap (m : P.U ⟶ Q.U) : Continuous (covMap P Q m) :=
  Q.continuous_ecov.comp (m.continuous_h.comp
    (P.Θ'.continuous.comp (continuous_sigmaMk (σ := fun _ : P.Lv.L.H => P.E))))

lemma covMap_fst (m : P.U ⟶ Q.U) (e : P.E) :
    (covMap P Q m e).1.1 = specialFibreMap m.ψ m.ψ_toSpec e.1.1 := by
  apply Subtype.ext
  have h₁ := m.fst_h (P.Θ' ⟨1, e⟩)
  rw [← Q.Θ'_ecov (m.h (P.Θ' ⟨1, e⟩))] at h₁
  erw [Θ_fst, Θ_fst, indProj_one, indProj_one] at h₁
  exact h₁

lemma vtx_map (m : P.U ⟶ Q.U) (u : (tempFibre O R A V hV).obj P.U) :
    Q.vtx V hV ((tempFibre O R A V hV).map m u) =
      (covMap P Q m (P.ecov (Quotient.out u : PreFibre Ω V hV P.U).1.2)).1.2 := by
  conv_lhs => rw [← Quotient.out_eq u]
  change (Q.ecov (Quotient.out (Quotient.mk _ (preMap V hV m (Quotient.out u))) :
    PreFibre Ω V hV Q.U).1.2).1.2 = _
  rw [Q.out_mk V hV]
  change (Q.ecov (m.h (Quotient.out u : PreFibre Ω V hV P.U).1.2)).1.2 = _
  rw [covMap, P.Θ'_ecov]

end Map

section Length

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- **Positive lower bound of the weights of the special points** ((X0) of `HarmonicX`). -/
lemma WData.exists_weight_pos (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {X : TempObj O R A} (D : WData x X.Lv) [NoetherianSpace X.Lv.Z] [T0Space X.Lv.Z]
    [QuasiSober X.Lv.Z] (hdim : topologicalKrullDim X.Lv.Z ≤ 1) :
    ∃ μ : ℝ≥0∞, μ ≠ 0 ∧ ∀ s ∈ (curveConfig X.Lv.Z hdim).S, μ ≤ D.weight ϖ s := by
  obtain ⟨H0, -⟩ := WData.isHarmonicX hX ϖ hϖ (𝟙 X) D D
  have hpos : ∀ s ∈ (curveConfig X.Lv.Z hdim).S, D.weight ϖ s ≠ 0 := fun s hs => by
    have hnode := D.isNodePt_of_mem_S hN hs
    obtain ⟨hex, hl⟩ := H0 _ hnode
    rw [D.weight_of_exists ϖ hex, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact_mod_cast hl _ hex.choose_spec
  rcases (curveConfig X.Lv.Z hdim).S.eq_empty_or_nonempty with hS | hS
  · exact ⟨1, one_ne_zero, fun s hs => by rw [hS] at hs; exact hs.elim⟩
  · obtain ⟨s₀, hs₀, hmin⟩ :=
      Set.exists_min_image _ (D.weight ϖ) (curveConfig X.Lv.Z hdim).finite_S hS
    exact ⟨_, hpos s₀ hs₀, hmin⟩

/-- The length between two fibre elements of a member with a presentation. -/
def Pres.len (ϖ : O) {X : TempObj O R A} (P : Pres x X) (g γ : (tempFibre O R A V hV).obj X) :
    ℝ≥0∞ :=
  CurveConfig.tlen (P.D.weight ϖ) (P.vtx V hV ((tempFibre O R A V hV).map P.iso.hom g))
    (P.vtx V hV ((tempFibre O R A V hV).map P.iso.hom γ))

variable (x) in
/-- **The length of a fibre element of a pointed member of `galClassW`**: the tree length, with
the x-lengths of the nodes as weights, between the vertices of the universal covering carrying
the base point and the element (through a chosen presentation). -/
def lenW (ϖ : O) (p : PtGal (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x)))
    (γ : (tempFibre O R A V hV).obj p.G) : ℝ≥0∞ :=
  (Classical.choice (Pres.nonempty p.mem)).len V hV ϖ p.g γ

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
@[simp] lemma lenW_self (ϖ : O)
    (p : PtGal (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x))) :
    lenW V hV x ϖ p p.g = 0 :=
  CurveConfig.tlen_self _ _

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- In the fibre of `U`, an element is determined by its geometric point and its vertex. -/
lemma Pres.injective_out_vtx {X : TempObj O R A} (P : Pres x X)
    {u u' : (tempFibre O R A V hV).obj P.U}
    (ht : (Quotient.out u : PreFibre Ω V hV P.U).1.1 = (Quotient.out u' : PreFibre Ω V hV P.U).1.1)
    (hv : P.vtx V hV u = P.vtx V hV u') : u = u' := by
  have h₁ := proj_eq_sp V hV (Quotient.out u : PreFibre Ω V hV P.U)
    (P.Θ'_ecov (Quotient.out u : PreFibre Ω V hV P.U).1.2).symm
  have h₂ := proj_eq_sp V hV (Quotient.out u' : PreFibre Ω V hV P.U)
    (P.Θ'_ecov (Quotient.out u' : PreFibre Ω V hV P.U).1.2).symm
  have he : P.ecov (Quotient.out u : PreFibre Ω V hV P.U).1.2 =
      P.ecov (Quotient.out u' : PreFibre Ω V hV P.U).1.2 := by
    refine CurveConfig.Cover.ext ?_ hv
    exact h₁.trans ((congrArg (P.Lv.sp V hV) ht).trans h₂.symm)
  have hq : (Quotient.out u : PreFibre Ω V hV P.U) = Quotient.out u' := by
    apply Subtype.ext
    refine Prod.ext ht ?_
    rw [← P.Θ'_ecov (Quotient.out u : PreFibre Ω V hV P.U).1.2,
      ← P.Θ'_ecov (Quotient.out u' : PreFibre Ω V hV P.U).1.2, he]
  rw [← Quotient.out_eq u, ← Quotient.out_eq u', hq]

/-- **Finiteness**: only finitely many fibre elements have length `≤ ℓ₀ ≠ ⊤`. -/
theorem Pres.finite_len_le (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {X : TempObj O R A} (P : Pres x X) (g : (tempFibre O R A V hV).obj X) {ℓ₀ : ℝ≥0∞}
    (hℓ₀ : ℓ₀ ≠ ⊤) : {γ | P.len V hV ϖ g γ ≤ ℓ₀}.Finite := by
  classical
  haveI := P.Lv.L.finite
  haveI := P.Lv.L.etale
  obtain ⟨μ, hμ0, hμ⟩ := WData.exists_weight_pos hX hN ϖ hϖ (X := P.U) P.D P.hdim
  have hT := CurveConfig.finite_tlen_le hμ0 hμ
    (P.vtx V hV ((tempFibre O R A V hV).map P.iso.hom g)) hℓ₀
  let S : Set ((tempFibre O R A V hV).obj P.U) := {u | CurveConfig.tlen (P.D.weight ϖ)
    (P.vtx V hV ((tempFibre O R A V hV).map P.iso.hom g)) (P.vtx V hV u) ≤ ℓ₀}
  let F : (tempFibre O R A V hV).obj P.U → (P.Lv.L.B →ₐ[R] Ω) × _ := fun u =>
    ((Quotient.out u : PreFibre Ω V hV P.U).1.1, P.vtx V hV u)
  have hF : Set.InjOn F S := fun u _ u' _ h =>
    P.injective_out_vtx V hV (Prod.mk.inj h).1 (Prod.mk.inj h).2
  have hS : S.Finite := Set.Finite.of_finite_image
    ((Set.finite_univ.prod hT).subset (by rintro _ ⟨u, hu, rfl⟩; exact ⟨trivial, hu⟩)) hF
  refine (hS.preimage (f := (tempFibre O R A V hV).map P.iso.hom) fun γ _ γ' _ h => ?_).subset
    fun γ hγ => hγ
  have := congrArg ((tempFibre O R A V hV).map P.iso.inv) h
  rwa [Functor.map_hom_inv'_apply, Functor.map_hom_inv'_apply] at this

/-- **Finiteness** for `lenW`. -/
theorem finite_lenW_le (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    (p : PtGal (tempFibre O R A V hV) (galClassW O R A Ω (Level.IsW x))) {ℓ₀ : ℝ≥0∞}
    (hℓ₀ : ℓ₀ ≠ ⊤) : {γ | lenW V hV x ϖ p γ ≤ ℓ₀}.Finite :=
  (Classical.choice (Pres.nonempty p.mem)).finite_len_le V hV hX hN ϖ hϖ p.g hℓ₀

end Length


end

end TemperedFundamentalGroups
