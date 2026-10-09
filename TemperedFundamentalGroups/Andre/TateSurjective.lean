/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.HeightW
import TemperedFundamentalGroups.Andre.TateModelNormal

/-!
# Model maps of members onto the Tate model are surjective on special fibres (G1, S1)

Let `T` be the data of the Tate object with `x` transcendental over `K`, and let `P : Pres x X`
present a member with a morphism `a : X ⟶ X₀`. The model map `ψ : 𝒯_P → 𝒯` (`𝒯 = V(F) ⊆ ℙ²_O`)
is universally closed, and its image contains `j(η)`, the image of the generic point of `Spec B`.
Since `x` is transcendental, `j(η) = [x : y : π]` generalizes every point of `V(F)`: a homogeneous
`h` with `h(x, y, π) = 0` vanishes at `[a : b : 1]` (via the injective map
`O[X][Y]/(f) → Frac B`, `X ↦ x / π`, `Y ↦ y / π`, `TateNormal.tateHom_injective`), hence is a
multiple of `F` (`TateNormal.F_dvd_of_eval_eq_zero`). So `ψ` is surjective, and so is the map of
special fibres:

* `Pres.tateMap_surjective` **(S1)**.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace TemperedFundamentalGroups.TateNormal

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (π b₄ b₆ : O) [Fact (Squarefree (dpoly π b₄ b₆))]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) O
local notation "L" => TateField π b₄ b₆

variable {M : Type u} [Field M] (φ : O →+* M) {x y : M}

/-- The map `O[X][Y]/(f) → M`, `X ↦ x / π`, `Y ↦ y / π`. -/
def tateHom (heq : y ^ 2 + x * y = x ^ 3 + φ (π ^ 2 * b₄) * x + φ (π ^ 2 * b₆))
    (hπ : φ π ≠ 0) : TateRing π b₄ b₆ →+* M :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom φ (x / φ π)) (y / φ π) (by
    rw [eval₂_fpoly]
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, cpoly, Polynomial.eval₂_add,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_mul] at heq ⊢
    field_simp
    simp only [map_pow] at heq
    linear_combination heq)

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma tateHom_of (heq : y ^ 2 + x * y = x ^ 3 + φ (π ^ 2 * b₄) * x + φ (π ^ 2 * b₆))
    (hπ : φ π ≠ 0) (p : Polynomial O) :
    tateHom π b₄ b₆ φ heq hπ (AdjoinRoot.of _ p) = p.eval₂ φ (x / φ π) :=
  AdjoinRoot.lift_of _

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma tateHom_root (heq : y ^ 2 + x * y = x ^ 3 + φ (π ^ 2 * b₄) * x + φ (π ^ 2 * b₆))
    (hπ : φ π ≠ 0) : tateHom π b₄ b₆ φ heq hπ (bA π b₄ b₆) = y / φ π :=
  AdjoinRoot.lift_root _

/-- `tateHom` is injective when `x / π` is transcendental over `O`. -/
lemma tateHom_injective (heq : y ^ 2 + x * y = x ^ 3 + φ (π ^ 2 * b₄) * x + φ (π ^ 2 * b₆))
    (hπ : φ π ≠ 0) (hx : ∀ p : Polynomial O, p.eval₂ φ (x / φ π) = 0 → p = 0) :
    Function.Injective (tateHom π b₄ b₆ φ heq hπ) := by
  haveI : Module.Finite (Polynomial O) (TateRing π b₄ b₆) :=
    (AdjoinRoot.powerBasis' (fpoly_monic π b₄ b₆)).finite
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker (tateHom π b₄ b₆ φ heq hπ) = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := Polynomial O) ?_
    refine eq_bot_iff.2 fun p hp => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, AdjoinRoot.algebraMap_eq, tateHom_of] at hp
    exact hx p hp
  have : a ∈ RingHom.ker (tateHom π b₄ b₆ φ heq hπ) := ha
  rwa [hker] at this

/-- **A homogeneous polynomial vanishing at `[x : y : π]` vanishes at `[a : b : 1]`**, when
`x / π` is transcendental over `O`. -/
lemma eval_coords_eq_zero (heq : y ^ 2 + x * y = x ^ 3 + φ (π ^ 2 * b₄) * x + φ (π ^ 2 * b₆))
    (hπ : φ π ≠ 0) (hx : ∀ p : Polynomial O, p.eval₂ φ (x / φ π) = 0 → p = 0)
    {h : MvPolynomial (Fin (2 + 1)) O} {n : ℕ} (hh : h.IsHomogeneous n)
    (h0 : TateModel.evalPt π φ x y h = 0) :
    MvPolynomial.eval₂ (algebraMap O L) (coords π b₄ b₆) h = 0 := by
  set θ := tateHom π b₄ b₆ φ heq hπ
  set v : Fin (2 + 1) → TateRing π b₄ b₆ := ![AdjoinRoot.of _ Polynomial.X, bA π b₄ b₆, 1]
  have hc : coords π b₄ b₆ = fun i => algebraMap (TateRing π b₄ b₆) L (v i) := by
    funext i
    fin_cases i
    · simp [v, coords, aL, AdjoinRoot.algebraMap_eq,
        IsScalarTower.algebraMap_apply (Polynomial O) (TateRing π b₄ b₆) L]
    · simp [v, coords, bL]
    · simp [v, coords]
  have hO : algebraMap O L = (algebraMap (TateRing π b₄ b₆) L).comp
      (algebraMap O (TateRing π b₄ b₆)) := IsScalarTower.algebraMap_eq _ _ _
  have hθO : θ.comp (algebraMap O (TateRing π b₄ b₆)) = φ := by
    ext c
    rw [RingHom.comp_apply, AdjoinRoot.algebraMap_eq', RingHom.comp_apply, tateHom_of]
    simp
  have key : θ (MvPolynomial.eval₂ (algebraMap O (TateRing π b₄ b₆)) v h) = 0 := by
    rw [MvPolynomial.hom_eval₂, hθO]
    have h1 := eval₂_mul_of_isHomogeneous hh φ (θ ∘ v) (φ π)
    have h2 : (fun i => φ π * (θ ∘ v) i) = ![x, y, φ π] := by
      funext i
      fin_cases i
      · simp [θ, v, tateHom_of, mul_div_cancel₀ _ hπ]
      · simp [θ, v, tateHom_root, mul_div_cancel₀ _ hπ]
      · simp [θ, v]
    rw [h2] at h1
    have h3 : TateModel.evalPt π φ x y h = MvPolynomial.eval₂ φ ![x, y, φ π] h := rfl
    rw [h3, h1] at h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hπ)
  have key' := tateHom_injective π b₄ b₆ φ heq hπ hx (key.trans (map_zero θ).symm)
  have := MvPolynomial.eval₂_comp_left (algebraMap (TateRing π b₄ b₆) L)
    (algebraMap O (TateRing π b₄ b₆)) v h
  rw [key', map_zero] at this
  rw [hc, hO]
  exact this.symm


omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
/-- Membership of a homogeneous element of positive degree in the image of a point under
`[x : y : π] : Spec T → ℙ²_O`. -/
lemma mem_toProj_iff {T : Type u} [CommRing T] (φ : O →+* T) (x y : T) (hπ : IsUnit (φ π))
    (s : Spec (CommRingCat.of T)) {h : MvPolynomial (Fin (2 + 1)) O} {n : ℕ} (hn : 0 < n)
    (hh : h ∈ 𝒜 n) :
    h ∈ (TateModel.toProj π φ x y hπ s).asHomogeneousIdeal ↔
      TateModel.evalPt π φ x y h ∈ s.asIdeal := by
  have e := Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 (TateModel.evalΓ π φ x y)
    (TateModel.map_irrelevant_evalΓ π φ x y hπ) hn hh
  have e' := SetLike.ext_iff.1 e s
  change _ ↔ s ∈ (Spec (CommRingCat.of T)).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of T)).inv (TateModel.evalPt π φ x y h)) at e'
  rw [basicOpen_eq_of_affine] at e'
  rw [← not_iff_not]
  exact e'

omit [Fact (Squarefree (dpoly π b₄ b₆))] in
/-- **The image of a point specializes to every point of `V(F)`** if the homogeneous
polynomials vanishing at `[x : y : π]` there vanish at the generic point `[a : b : 1]`. -/
lemma toProj_le {T : Type u} [CommRing T] (φ : O →+* T) (x y : T) (hπ : IsUnit (φ π))
    (hπ0 : π ≠ 0) (s : Spec (CommRingCat.of T))
    (hgen : ∀ (h : MvPolynomial (Fin (2 + 1)) O) (n : ℕ), h.IsHomogeneous n →
      TateModel.evalPt π φ x y h ∈ s.asIdeal →
      MvPolynomial.eval₂ (algebraMap O L) (coords π b₄ b₆) h = 0)
    (z : projSpace O 2) (hz : TateModel.F π b₄ b₆ ∈ z.asHomogeneousIdeal) :
    (TateModel.toProj π φ x y hπ s).asHomogeneousIdeal ≤ z.asHomogeneousIdeal := by
  intro h hh
  rw [← sum_homogeneousComponent h]
  refine Ideal.sum_mem _ fun n _ => ?_
  set g := homogeneousComponent n h
  have hg : g.IsHomogeneous n := homogeneousComponent_isHomogeneous n h
  have hgI : g ∈ (TateModel.toProj π φ x y hπ s).asHomogeneousIdeal :=
    homogeneousComponent_mem_of_mem (TateModel.toProj π φ x y hπ s).asHomogeneousIdeal.isHomogeneous
      hh n
  have hgX : g * X 2 ∈ (TateModel.toProj π φ x y hπ s).asHomogeneousIdeal :=
    Ideal.mul_mem_right _ _ hgI
  rw [mem_toProj_iff π φ x y hπ s (n := n + 1) n.succ_pos
    ((mem_homogeneousSubmodule _ _).2 (hg.mul (isHomogeneous_X _ _)))] at hgX
  have hev : TateModel.evalPt π φ x y (g * X 2) =
      TateModel.evalPt π φ x y g * φ π := by
    simp [TateModel.evalPt]
  rw [hev] at hgX
  have hs := s.isPrime
  have hπs : φ π ∉ s.asIdeal := fun h' => hs.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hπ)
  have hg0 := hgen g n hg ((hs.mem_or_mem hgX).resolve_right hπs)
  obtain ⟨q, hq⟩ := F_dvd_of_eval_eq_zero π b₄ b₆ hπ0 hg hg0
  rw [hq]
  exact Ideal.mul_mem_right _ _ hz

end

end TemperedFundamentalGroups.TateNormal

namespace TemperedFundamentalGroups

noncomputable section

open TempObj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A flat algebra over a domain which is nonzero has injective structure map. -/
lemma algebraMap_injective_of_flat {R B : Type*} [CommRing R] [IsDomain R] [CommRing B]
    [Nontrivial B] [Algebra R B] [Module.Flat R B] : Function.Injective (algebraMap R B) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra h0
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
    (mem_nonZeroDivisors_of_ne_zero h0)
  have h1 : (1 : B) = 0 := hreg (by simp [Algebra.smul_def, hr])
  exact one_ne_zero h1

/-- If `x ∈ R` is transcendental over `K` and `ρ : R → M` is injective, then `ρ(x) / c` is
transcendental over `O` for `0 ≠ c ∈ O`. -/
lemma eval₂_div_eq_zero {K : Type u} [Field K] {O : ValuationSubring K} {R : Type u}
    [CommRing R] [Algebra K R] {M : Type u} [Field M] (ρ : R →+* M)
    (hρ : Function.Injective ρ) {x : R} (hx : Transcendental K x) {c : O} (hc : c ≠ 0)
    (p : Polynomial O)
    (hp : p.eval₂ ((ρ.comp (algebraMap K R)).comp O.subtype) (ρ x / ρ (algebraMap K R c)) = 0) :
    p = 0 := by
  have hc' : (c : K) ≠ 0 := fun h => hc (Subtype.ext h)
  set q : Polynomial K := (p.map O.subtype).comp (Polynomial.C (c : K)⁻¹ * Polynomial.X)
  have hq : Polynomial.aeval x q = 0 := by
    apply hρ
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_comp,
      Polynomial.eval₂_map]
    have hpt : Polynomial.eval₂ (ρ.comp (algebraMap K R)) (ρ x)
        (Polynomial.C (c : K)⁻¹ * Polynomial.X) = ρ x / ρ (algebraMap K R c) := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, map_inv₀,
        div_eq_inv_mul]
      rfl
    rw [hpt]
    exact hp
  have hq0 : q = 0 := (transcendental_iff.1 hx) q hq
  rcases Polynomial.comp_eq_zero_iff.1 hq0 with h | ⟨-, h⟩
  · exact Polynomial.map_injective _ Subtype.val_injective (h.trans (Polynomial.map_zero _).symm)
  · have := congrArg (Polynomial.coeff · 1) h
    exact (hc (by simpa using this)).elim

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] {x : R} (T : TateObject.Data O R)

namespace Pres

variable [IsDiscreteValuationRing O] [IsDomain R] {X : TempObj O R A} (P : Pres x X)

/-- **(S1) The model map of a member onto the Tate model is surjective on special fibres**, when
`x` is transcendental over `K` and `d = X² + 4 (π X³ + π b₄ X + b₆)` is squarefree. -/
theorem tateMap_surjective (hd : Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))
    (hx : Transcendental K T.x) (a : X ⟶ TateObject.X₀ (A := A) T) :
    Function.Surjective (P.tateMap T a) := by
  haveI : Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆)) := ⟨hd⟩
  haveI := P.D.isDomain
  set f := P.iso.inv ≫ a
  set Bt := (TateObject.unitLevel R A).B
  set φt : O →+* Bt := levelStructureMap O R A (TateObject.unitLevel R A)
  set M := FractionRing P.Lv.L.B
  haveI : IsDomain P.U.Lv.L.B := P.D.isDomain
  set fφ : Bt →+* P.U.Lv.L.B := (f.φ.f : (TateObject.X₀ (A := A) T).Lv.L.B →+* P.U.Lv.L.B)
  set g : Bt →+* M := (algebraMap P.Lv.L.B M).comp fφ
  let ξ : Spec (CommRingCat.of P.U.Lv.L.B) := ⟨⊥, Ideal.isPrime_bot⟩
  set s := Spec.map (CommRingCat.ofHom fφ) ξ
  -- `ψ (j ξ) = j_𝒯 (s)`
  have hw : f.ψ (P.U.Lv.j ξ) = (TateObject.X₀ (A := A) T).Lv.j s := by
    rw [← Scheme.Hom.comp_apply, f.j_ψ, Scheme.Hom.comp_apply]
    rfl
  -- `ρ : R → M` is injective
  set ρ : R →+* M := g.comp (algebraMap R Bt)
  have hρ : Function.Injective ρ := by
    haveI := P.Lv.L.etale
    haveI := P.Lv.L.finite
    have h1 : ρ = (algebraMap P.Lv.L.B M).comp (algebraMap R P.Lv.L.B) := by
      ext r
      exact congrArg (algebraMap P.Lv.L.B M) (f.φ.f.commutes r)
    rw [h1, RingHom.coe_comp]
    exact (IsFractionRing.injective P.Lv.L.B M).comp
      (algebraMap_injective_of_flat (R := R) (B := P.Lv.L.B))
  have hgφ : g.comp φt = (ρ.comp (algebraMap K R)).comp O.subtype := rfl
  have hπM : (g.comp φt) T.π ≠ 0 := ((T.isUnit_π (A := A)).map g).ne_zero
  have heqM : g (algebraMap R Bt T.y) ^ 2 + g (algebraMap R Bt T.x) * g (algebraMap R Bt T.y) =
      g (algebraMap R Bt T.x) ^ 3 + (g.comp φt) (T.π ^ 2 * T.b₄) * g (algebraMap R Bt T.x) +
        (g.comp φt) (T.π ^ 2 * T.b₆) := by
    have e := congrArg g (T.equation_B (A := A))
    simp only [map_add, map_mul, map_pow] at e
    simp only [RingHom.comp_apply, map_mul, map_pow]
    linear_combination e
  have hxM : ∀ p : Polynomial O,
      p.eval₂ (g.comp φt) (g (algebraMap R Bt T.x) / (g.comp φt) T.π) = 0 → p = 0 :=
    fun p hp => eval₂_div_eq_zero ρ hρ hx T.π_ne_zero p hp
  -- `j_𝒯 (s)` specializes to every point of the model
  have hgen : ∀ (h : MvPolynomial (Fin (2 + 1)) O) (n : ℕ), h.IsHomogeneous n →
      TateModel.evalPt T.π φt (algebraMap R Bt T.x) (algebraMap R Bt T.y) h ∈ s.asIdeal →
      MvPolynomial.eval₂ (algebraMap O (TateNormal.TateField T.π T.b₄ T.b₆))
        (TateNormal.coords T.π T.b₄ T.b₆) h = 0 := by
    intro h n hh hs
    have hs' : fφ
        (TateModel.evalPt T.π φt (algebraMap R Bt T.x) (algebraMap R Bt T.y) h) = 0 :=
      Ideal.mem_bot.1 hs
    refine TateNormal.eval_coords_eq_zero T.π T.b₄ T.b₆ (g.comp φt) heqM hπM hxM hh ?_
    have e : g (TateModel.evalPt T.π φt (algebraMap R Bt T.x) (algebraMap R Bt T.y) h) =
        TateModel.evalPt T.π (g.comp φt) (g (algebraMap R Bt T.x)) (g (algebraMap R Bt T.y))
          h := by
      simp only [TateModel.evalPt, coe_eval₂Hom]
      rw [MvPolynomial.hom_eval₂]
      congr 1
      funext i
      fin_cases i <;> simp
    rw [← e]
    exact (congrArg (algebraMap P.Lv.L.B M) hs').trans (map_zero _)
  have hsp : ∀ z : (TateObject.X₀ (A := A) T).Lv.c.scheme,
      (TateObject.X₀ (A := A) T).Lv.j s ⤳ z := by
    intro z
    have hι : TateModel.ι T.π T.b₄ T.b₆ ((TateObject.X₀ (A := A) T).Lv.j s) =
        TateModel.toProj T.π φt (algebraMap R Bt T.x) (algebraMap R Bt T.y) (T.isUnit_π) s := by
      rw [← TateModel.toModel_ι T.π T.b₄ T.b₆ φt (T.equation_B (A := A)) (T.isUnit_π)]
      rfl
    have hle := TateNormal.toProj_le T.π T.b₄ T.b₆ φt _ _ T.isUnit_π T.π_ne_zero s hgen
      (TateModel.ι T.π T.b₄ T.b₆ z) (TateModel.F_mem T.π T.b₄ T.b₆ z)
    rw [← hι] at hle
    exact (TateModel.ι T.π T.b₄ T.b₆).isEmbedding.isInducing.specializes_iff.1
      (specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1 hle))
  -- the image of `ψ` is closed
  haveI : UniversallyClosed (f.ψ ≫ (TateObject.X₀ (A := A) T).Lv.c.toSpec) := by
    rw [f.ψ_toSpec]; infer_instance
  haveI : UniversallyClosed f.ψ :=
    UniversallyClosed.of_comp_of_isSeparated f.ψ (TateObject.X₀ (A := A) T).Lv.c.toSpec
  have hrange : IsClosed (Set.range f.ψ) := f.ψ.isClosedMap.isClosed_range
  intro z
  have hz : z.1 ∈ Set.range f.ψ := by
    refine hrange.closure_subset_iff.2 (Set.singleton_subset_iff.2 ⟨_, hw⟩) ?_
    exact specializes_iff_mem_closure.1 (hsp z.1)
  obtain ⟨u, hu⟩ := hz
  have hu' : u ∈ specialFibre P.Lv.c.toSpec := by
    have h2 : f.ψ u ∈ specialFibre (TateObject.X₀ (A := A) T).Lv.c.toSpec := by
      rw [hu]
      exact z.2
    have h3 : P.U.Lv.c.toSpec u = (TateObject.X₀ (A := A) T).Lv.c.toSpec (f.ψ u) := by
      rw [← Scheme.Hom.comp_apply, f.ψ_toSpec]
    exact (mem_specialFibre _ _).2 (h3.trans ((mem_specialFibre _ _).1 h2))
  exact ⟨⟨u, hu'⟩, Subtype.ext hu⟩

end Pres

end

end TemperedFundamentalGroups
