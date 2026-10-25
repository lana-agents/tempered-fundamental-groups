/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.CoverImage
import EllipticCurves.FunctionField.MulByNCoordinateRingGalois
import Pi1.Profinite.SigmaIndex
import Pi1.Profinite.ProSigma
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Algebra.Module.Submodule.Union

/-!
# The Galois cover `E ∖ E[ℓ] → E ∖ {0}` given by multiplication by `ℓ`

Let `W` be an elliptic curve over a field `F` and `ℓ` an index with `(2 : F) ≠ 0`, `(ℓ : F) ≠ 0`.
`MulByNCover W ℓ = F[W][1/ψ_ℓ]` (the functions on `Y = E ∖ E[ℓ]`) is a finite étale
`F[W]`-algebra through `[ℓ]^*` (`F[W]` = functions on `E ∖ {0}`), on which `E[ℓ]` acts by
translations; when all of `E[ℓ]` is `F`-rational (`#E[ℓ] = ℓ²`, as in IUT I Def 3.1(c)) this action
makes `E[ℓ]` the Galois group (`isGaloisGroup_mulByNCover_of_card`). This file applies the general
cover results of `TemperedFundamentalGroups.Tempered.CoverImage` to this cover. The Galois
statements assume `F` infinite (automatic in characteristic `0`), used to compare geometric points.

## General results (scheme case, trivial groups)

* `Algebra.IsInvariant.exists_eq_comp_toAlgHom`: if a finite group `G` acts on `B` with invariants
  `A`, and `A` contains an infinite field `k`, then any two `A`-algebra maps `t s : B → Ω` to a
  domain differ by an element of `G`: `t = s ∘ g`.
* `normal_range_temperedPi1Map_of_isInvariant`: for such a Galois cover `R → R'` the image of
  `temperedPi1 O R' A' V hV` in `temperedPi1 O R A V hV` is normal.
* `index_range_temperedPi1Map_dvd_card`: if moreover `G` is commutative, the index of the image
  divides `#G` (the image is the kernel of a homomorphism to `G ⧸ D`, `D` the stabilizer of the
  base point).
* `exists_isSigmaOpenNormal_comap_le`: if `#G` is a `Σ`-integer, every open normal subgroup of
  `Σ`-integer index of `temperedPi1 O R' A' V hV` contains the preimage of an open normal subgroup
  of `Σ`-integer index of `temperedPi1 O R A V hV`.

## Multiplication by `ℓ`

* `mulByN_temperedPi1Map_injective`, `isOpenEmbedding_mulByN_temperedPi1Map`,
  `finiteIndex_range_mulByN_temperedPi1Map`: `π^temp(Y) → π^temp(E ∖ {0})` is an open embedding
  with image of finite index;
* `normal_range_mulByN_temperedPi1Map` (`#E[ℓ] = ℓ²`): the image is normal;
* `index_range_mulByN_temperedPi1Map_dvd` (`#E[ℓ] = ℓ²`): its index divides `ℓ²`, and
  `isSigmaNat_index_range_mulByN_temperedPi1Map`: it is a `Σ`-integer when `ℓ` is;
* `exists_isSigmaOpenNormal_comap_le_mulByN` (the `Σ`-transfer): every open normal subgroup of
  `Σ`-integer index of `π^temp(Y)` contains the preimage of an open normal subgroup of `Σ`-integer
  index of `π^temp(E ∖ {0})`.
-/

universe u

open CategoryTheory Pi1.Orbifold Pi1.Profinite Polynomial

set_option linter.unusedSectionVars false

/-- **Geometric points of a Galois extension differ by the Galois group**: if a finite group `G`
acts on `B` with invariants `A` (`Algebra.IsInvariant`), and `A` contains an infinite field `k`,
then any two `A`-algebra maps `t s : B → Ω` to a domain satisfy `t = s ∘ g` for some `g ∈ G`.
Pointwise, `t b` is a root of `∏_g (X - s (g • b))`; the sets `{b | t b = s (g • b)}` are
`k`-subspaces covering `B`, so one of them is everything. -/
theorem Algebra.IsInvariant.exists_eq_comp_toAlgHom {A B Ω : Type*} (k : Type*) (G : Type*)
    [CommRing A] [CommRing B] [Algebra A B] [Field k] [Infinite k] [Algebra k A] [Algebra k B]
    [IsScalarTower k A B] [CommRing Ω] [IsDomain Ω] [Algebra A Ω] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (t s : B →ₐ[A] Ω) : ∃ g : G, t = s.comp (MulSemiringAction.toAlgHom A B g) := by
  classical
  cases nonempty_fintype G
  have hpt (b : B) : ∃ g : G, t b = s (g • b) := by
    obtain ⟨p, hp⟩ := Polynomial.mem_lifts _ |>.1 (Algebra.IsInvariant.charpoly_mem_lifts A B G b)
    have h0 : aeval (t b) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_def, ← Polynomial.eval_map, hp,
        MulSemiringAction.eval_charpoly, map_zero]
    have h1 : aeval (t b) p = ∏ g : G, (t b - s (g • b)) := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← s.comp_algebraMap, ← Polynomial.map_map,
        hp, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod]
      simp
    rw [h1, Finset.prod_eq_zero_iff] at h0
    obtain ⟨g, -, hg⟩ := h0
    exact ⟨g, sub_eq_zero.1 hg⟩
  let p : G → Submodule k B := fun g => Subalgebra.toSubmodule
    ((AlgHom.equalizer t (s.comp (MulSemiringAction.toAlgHom A B g))).restrictScalars k)
  by_contra! hne
  have htop : ∀ g, p g ≠ ⊤ := fun g hg => hne g (AlgHom.ext fun b => by
    have : b ∈ p g := hg ▸ Submodule.mem_top
    exact this)
  obtain ⟨b, hb⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p htop
  obtain ⟨g, hg⟩ := hpt b
  exact hb g hg

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [Subsingleton A]
  [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  [Algebra.Etale R R'] [Module.Finite R R']
  {A' : Type u} [Group A'] [Subsingleton A'] [MulSemiringAction A' R']
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

variable (R A R' A') in
/-- The map of (trivial) orbifolds `Spec R' → Spec R` of an injective `R → R'`, with the trivial
homomorphism `A' →* A`. -/
def coverOrbMap (h : Function.Injective (algebraMap R R')) : OrbMap R A R' A' where
  α := 1
  map_smul a r := by simp [Subsingleton.elim a 1]
  injective := h

section Galois

variable [SMulCommClass A K R] (μ : OrbMap R A R' A') (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G R'] [SMulCommClass G R R'] [Algebra.IsInvariant R R' G] [Infinite K]

variable (K) in
include K in
/-- Every geometric point `R' → Ω` over `R` is the base point composed with an element of `G`. -/
theorem exists_eq_ofId_comp_toAlgHom (t : R' →ₐ[R] Ω) :
    ∃ g : G, t = ((Algebra.ofId R' Ω).restrictScalars R).comp
      (MulSemiringAction.toAlgHom R R' g) :=
  Algebra.IsInvariant.exists_eq_comp_toAlgHom K G t _

include G in
/-- **The image of the tempered fundamental group of a Galois cover is normal.** -/
theorem normal_range_temperedPi1Map_of_isInvariant :
    (temperedPi1Map (O := O) μ V hV).range.Normal :=
  normal_range_temperedPi1Map V hV μ fun t =>
    (exists_eq_ofId_comp_toAlgHom (Ω := Ω) K G t).elim fun _ hg => ⟨_, hg⟩

end Galois

section Index

variable [SMulCommClass A K R]

/-- A fibre element of the cover `Spec R' → Spec R`, as a geometric point `R' → Ω` over `R`. -/
def coverFibreHom (x : TempObj.Fibre Ω V hV (coverObj O R A R')) : R' →ₐ[R] Ω :=
  (etaleToTempFibreEquiv O R A V hV (coverEt R A R') x).comp (coverE R A R').symm.toAlgHom

lemma coverFibreHom_injective :
    Function.Injective (coverFibreHom (O := O) (R := R) (A := A) (R' := R') V hV) := by
  intro x y h
  apply (etaleToTempFibreEquiv O R A V hV (coverEt R A R')).injective
  refine AlgHom.ext fun b => ?_
  have := AlgHom.congr_fun h (coverE R A R' b)
  simpa [coverFibreHom] using this

lemma coverFibreHom_coverFibrePt (b : R') :
    coverFibreHom (O := O) (R := R) (A := A) (R' := R') V hV (coverFibrePt V hV) b =
      algebraMap R' Ω b := by
  simp [coverFibreHom, coverFibrePt, coverPt]

lemma coverFibreHom_fibreMap (τ : R' →ₐ[R] R') (x : TempObj.Fibre Ω V hV (coverObj O R A R'))
    (b : R') :
    coverFibreHom V hV (TempObj.fibreMap V hV ((etaleToTemp O R A).map (coverEndEt τ)) x) b =
      coverFibreHom V hV x (τ b) := by
  rw [coverFibreHom, etaleToTempFibreEquiv_map]
  simp [coverFibreHom, coverEndEt]

variable (R' Ω) (G : Type*) [CommGroup G] [MulSemiringAction G R']

/-- The elements of `G` fixing the base point `R' → Ω` (the decomposition group). -/
def basePtStab : Subgroup G where
  carrier := {g | ∀ b : R', algebraMap R' Ω (g • b) = algebraMap R' Ω b}
  one_mem' b := by rw [one_smul]
  mul_mem' {g h} hg hh b := by rw [mul_smul, hg, hh]
  inv_mem' {g} hg b := by
    change algebraMap R' Ω (g⁻¹ • b) = algebraMap R' Ω b
    rw [← hg (g⁻¹ • b), smul_inv_smul]

variable {R' Ω G}

lemma mk_eq_mk_basePtStab_iff {g h : G} :
    (g : G ⧸ basePtStab R' Ω G) = h ↔
      ∀ b : R', algebraMap R' Ω (g • b) = algebraMap R' Ω (h • b) := by
  rw [QuotientGroup.eq]
  refine ⟨fun hk b => ?_, fun H b => ?_⟩
  · have := hk (g • b)
    rw [smul_smul, mul_comm g⁻¹ h, inv_mul_cancel_right] at this
    exact this.symm
  · have := H (g⁻¹ • b)
    rw [smul_inv_smul, smul_smul] at this
    change algebraMap R' Ω ((g⁻¹ * h) • b) = algebraMap R' Ω b
    rw [mul_comm]
    exact this.symm

variable [Finite G] [SMulCommClass G R R'] [Algebra.IsInvariant R R' G] [Infinite K]

variable (R R') in
/-- The image of the base point of the cover under `γ`. -/
def coverAppPt (γ : temperedPi1 O R A V hV) : TempObj.Fibre Ω V hV (coverObj O R A R') :=
  γ.app (coverObj O R A R') (coverFibrePt V hV)

lemma app_fibreMap (γ : temperedPi1 O R A V hV) (m : coverObj O R A R' ⟶ coverObj O R A R')
    (x : TempObj.Fibre Ω V hV (coverObj O R A R')) :
    γ.app (coverObj O R A R') (TempObj.fibreMap V hV m x) =
      TempObj.fibreMap V hV m (γ.app (coverObj O R A R') x) :=
  FibreAut.app_naturality γ m x

variable (R' G) in
lemma exists_coverFibreHom_app (γ : temperedPi1 O R A V hV) :
    ∃ g : G, ∀ b : R', coverFibreHom V hV (coverAppPt R R' V hV γ) b = algebraMap R' Ω (g • b) := by
  obtain ⟨g, hg⟩ :=
    exists_eq_ofId_comp_toAlgHom K G (coverFibreHom V hV (coverAppPt R R' V hV γ))
  exact ⟨g, fun b => by rw [hg]; rfl⟩

variable (R' G) in
/-- The element of `G` moving the base point of the cover to its image under `γ`. -/
def coverClass (γ : temperedPi1 O R A V hV) : G := (exists_coverFibreHom_app R' V hV G γ).choose

lemma coverClass_spec (γ : temperedPi1 O R A V hV) (b : R') :
    coverFibreHom V hV (coverAppPt R R' V hV γ) b = algebraMap R' Ω (coverClass R' V hV G γ • b) :=
  (exists_coverFibreHom_app R' V hV G γ).choose_spec b

lemma coverAppPt_eq (γ : temperedPi1 O R A V hV) :
    coverAppPt R R' V hV γ = TempObj.fibreMap V hV
      ((etaleToTemp O R A).map (coverEndEt (MulSemiringAction.toAlgHom R R'
        (coverClass R' V hV G γ)))) (coverFibrePt V hV) := by
  refine coverFibreHom_injective V hV (AlgHom.ext fun b => ?_)
  rw [coverFibreHom_fibreMap, coverFibreHom_coverFibrePt, coverClass_spec (G := G)]
  rfl

variable (R' G) in
/-- **The class homomorphism** `π^temp(Spec R) → G ⧸ D`: `γ` moves the base point of the cover by
the class of `coverClass γ`. Its kernel is the image of `π^temp(Spec R')`. -/
def coverClassHom : temperedPi1 O R A V hV →* G ⧸ basePtStab R' Ω G where
  toFun γ := (coverClass R' V hV G γ : G ⧸ basePtStab R' Ω G)
  map_one' := by
    rw [← QuotientGroup.mk_one, mk_eq_mk_basePtStab_iff]
    intro b
    rw [← coverClass_spec (G := G), one_smul]
    exact coverFibreHom_coverFibrePt V hV b
  map_mul' γ δ := by
    rw [← QuotientGroup.mk_mul, mk_eq_mk_basePtStab_iff]
    intro b
    have h : coverAppPt R R' V hV (γ * δ) =
      γ.app (coverObj O R A R') (coverAppPt R R' V hV δ) := rfl
    rw [← coverClass_spec (G := G), h, coverAppPt_eq V hV (G := G) δ, app_fibreMap,
      coverFibreHom_fibreMap, MulSemiringAction.toAlgHom_apply]
    change coverFibreHom V hV (coverAppPt R R' V hV γ) _ = _
    rw [coverClass_spec (G := G), mul_smul]

theorem ker_coverClassHom (μ : OrbMap R A R' A') :
    (coverClassHom R' V hV G).ker = (temperedPi1Map (O := O) μ V hV).range := by
  ext γ
  rw [MonoidHom.mem_ker, mem_range_temperedPi1Map]
  change (coverClass R' V hV G γ : G ⧸ basePtStab R' Ω G) = ((1 : G) : G ⧸ basePtStab R' Ω G) ↔
    coverAppPt R R' V hV γ = coverFibrePt V hV
  rw [mk_eq_mk_basePtStab_iff, ← (coverFibreHom_injective V hV).eq_iff]
  refine ⟨fun h => AlgHom.ext fun b => ?_, fun h b => ?_⟩
  · rw [coverClass_spec (G := G), h, one_smul, coverFibreHom_coverFibrePt]
  · rw [← coverClass_spec (G := G), h, one_smul, coverFibreHom_coverFibrePt]

/-- **The index of the image divides `#G`** for a cover with commutative Galois group `G`. -/
theorem index_range_temperedPi1Map_dvd_card (μ : OrbMap R A R' A') :
    (temperedPi1Map (O := O) μ V hV).range.index ∣ Nat.card G := by
  rw [← ker_coverClassHom V hV (G := G) μ, Subgroup.index_ker]
  exact (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

/-- **The `Σ`-transfer**: for a cover with commutative Galois group `G` of `Σ`-integer order, every
open normal subgroup of `Σ`-integer index of `π^temp(Spec R')` contains the preimage of an open
normal subgroup of `Σ`-integer index of `π^temp(Spec R)`. -/
theorem exists_isSigmaOpenNormal_comap_le (μ : OrbMap R A R' A') (P : ℕ → Prop)
    (hG : IsSigmaNat P (Nat.card G)) {N : Subgroup (temperedPi1 O R' A' V hV)}
    (hN : IsSigmaOpenNormal P _ N) :
    ∃ K : Subgroup (temperedPi1 O R A V hV), IsSigmaOpenNormal P _ K ∧
      K.comap (temperedPi1Map μ V hV) ≤ N := by
  haveI := normal_range_temperedPi1Map_of_isInvariant V hV μ G
  haveI := finiteIndex_range_temperedPi1Map V hV μ
  haveI := hN.2.1
  haveI : N.FiniteIndex := ⟨hN.2.2.1⟩
  have hidx := hG.of_dvd (index_range_temperedPi1Map_dvd_card V hV (G := G) μ)
  obtain ⟨K, hKn, hKo, hKf, hle, hKP⟩ := Subgroup.exists_open_normal_comap_le_of_sigma P
    (isOpenEmbedding_temperedPi1Map V hV μ) hidx.2 hN.1 hN.2.2.2
  exact ⟨K, ⟨hKo, hKn, hKf.index_ne_zero, hKP⟩, hle⟩

end Index

end

end TemperedFundamentalGroups

namespace TemperedFundamentalGroups

noncomputable section

section MulByN

open WeierstrassCurve.Affine.CoordinateRing

variable {F : Type u} [Field F] {O : ValuationSubring F} (W : WeierstrassCurve.Affine F) (ℓ : ℕ)
  [NeZero (2 : F)] [NeZero (ℓ : F)] [W.IsElliptic]
  {A : Type u} [Group A] [Subsingleton A] [MulSemiringAction A W.CoordinateRing]
  [SMulCommClass A F W.CoordinateRing]
  {A' : Type u} [Group A'] [Subsingleton A'] [MulSemiringAction A' (MulByNCover W ℓ)]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [Algebra W.CoordinateRing Ω]
  [IsScalarTower F W.CoordinateRing Ω] [Algebra (MulByNCover W ℓ) Ω]
  [IsScalarTower F (MulByNCover W ℓ) Ω] [IsScalarTower W.CoordinateRing (MulByNCover W ℓ) Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap F Ω) = O)

variable (A A') in
/-- **Multiplication by `ℓ`**, `Y = E ∖ E[ℓ] → E ∖ {0}`, as a map of (trivial) orbifolds:
`[ℓ]^* : F[W] → F[W][1/ψ_ℓ]`. -/
def mulByNOrbMap : OrbMap W.CoordinateRing A (MulByNCover W ℓ) A' :=
  coverOrbMap _ _ _ _ (algebraMap_mulByNCover_injective W ℓ)

/-- **`π^temp(Y) → π^temp(E ∖ {0})` is injective.** -/
theorem mulByN_temperedPi1Map_injective :
    Function.Injective (temperedPi1Map (O := O) (mulByNOrbMap W ℓ A A') V hV) :=
  temperedPi1Map_injective V hV _

/-- **`π^temp(Y)` is an open subgroup of `π^temp(E ∖ {0})`**: the map is an open embedding. -/
theorem isOpenEmbedding_mulByN_temperedPi1Map :
    Topology.IsOpenEmbedding (temperedPi1Map (O := O) (mulByNOrbMap W ℓ A A') V hV) :=
  isOpenEmbedding_temperedPi1Map V hV _

/-- **The image of `π^temp(Y)` has finite index.** -/
theorem finiteIndex_range_mulByN_temperedPi1Map :
    (temperedPi1Map (O := O) (mulByNOrbMap W ℓ A A') V hV).range.FiniteIndex :=
  finiteIndex_range_temperedPi1Map V hV _

open Classical in
lemma card_torsionNMul (hcard : Nat.card (W.torsion ℓ) = ℓ ^ 2) :
    Nat.card (TorsionNMul W ℓ) = ℓ ^ 2 :=
  (Nat.card_congr Multiplicative.toAdd).trans hcard

open Classical in
lemma finite_torsionNMul (hcard : Nat.card (W.torsion ℓ) = ℓ ^ 2) : Finite (TorsionNMul W ℓ) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_torsionNMul W ℓ hcard]; exact pow_ne_zero 2 (ne_zero_of_neZero_cast (F := F) ℓ))

variable [Infinite F]

open Classical in
/-- **The image of `π^temp(Y)` is normal** when `E[ℓ]` is `F`-rational (`#E[ℓ] = ℓ²`). -/
theorem normal_range_mulByN_temperedPi1Map (hcard : Nat.card (W.torsion ℓ) = ℓ ^ 2) :
    (temperedPi1Map (O := O) (mulByNOrbMap W ℓ A A') V hV).range.Normal := by
  haveI := finite_torsionNMul W ℓ hcard
  haveI := isInvariant_mulByNCover_of_card W ℓ hcard
  exact normal_range_temperedPi1Map_of_isInvariant V hV _ (TorsionNMul W ℓ)

open Classical in
/-- **The index of `π^temp(Y)` in `π^temp(E ∖ {0})` divides `ℓ²`** when `E[ℓ]` is `F`-rational. -/
theorem index_range_mulByN_temperedPi1Map_dvd (hcard : Nat.card (W.torsion ℓ) = ℓ ^ 2) :
    (temperedPi1Map (O := O) (mulByNOrbMap W ℓ A A') V hV).range.index ∣ ℓ ^ 2 := by
  haveI := finite_torsionNMul W ℓ hcard
  haveI := isInvariant_mulByNCover_of_card W ℓ hcard
  rw [← card_torsionNMul W ℓ hcard]
  exact index_range_temperedPi1Map_dvd_card V hV (G := TorsionNMul W ℓ) _

open Classical in
/-- **The index of `π^temp(Y)` in `π^temp(E ∖ {0})` is a `Σ`-integer** when `ℓ` is one and
`E[ℓ]` is `F`-rational. -/
theorem isSigmaNat_index_range_mulByN_temperedPi1Map (hcard : Nat.card (W.torsion ℓ) = ℓ ^ 2)
    {P : ℕ → Prop} (hℓ : IsSigmaNat P ℓ) :
    IsSigmaNat P (temperedPi1Map (O := O) (mulByNOrbMap W ℓ A A') V hV).range.index :=
  (sq ℓ ▸ hℓ.mul hℓ).of_dvd (index_range_mulByN_temperedPi1Map_dvd W ℓ V hV hcard)

open Classical in
/-- **The `Σ`-transfer for `[ℓ] : E ∖ E[ℓ] → E ∖ {0}`**: if `ℓ` is a `Σ`-integer and `E[ℓ]` is
`F`-rational, every open normal subgroup of `Σ`-integer index of `π^temp(Y)` contains the preimage
of an open normal subgroup of `Σ`-integer index of `π^temp(E ∖ {0})`. -/
theorem exists_isSigmaOpenNormal_comap_le_mulByN (hcard : Nat.card (W.torsion ℓ) = ℓ ^ 2)
    {P : ℕ → Prop} (hℓ : IsSigmaNat P ℓ)
    {N : Subgroup (temperedPi1 O (MulByNCover W ℓ) A' V hV)} (hN : IsSigmaOpenNormal P _ N) :
    ∃ K : Subgroup (temperedPi1 O W.CoordinateRing A V hV), IsSigmaOpenNormal P _ K ∧
      K.comap (temperedPi1Map (mulByNOrbMap W ℓ A A') V hV) ≤ N := by
  haveI := finite_torsionNMul W ℓ hcard
  haveI := isInvariant_mulByNCover_of_card W ℓ hcard
  refine exists_isSigmaOpenNormal_comap_le V hV (G := TorsionNMul W ℓ) _ P ?_ hN
  rw [card_torsionNMul W ℓ hcard, sq]
  exact hℓ.mul hℓ

end MulByN

end

end TemperedFundamentalGroups
