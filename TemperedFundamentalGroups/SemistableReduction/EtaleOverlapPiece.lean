/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlapGlue

/-!
# The étale piece over the second chart restricted to the overlap (Blueprint §12.8, M2.3 (f))

Two level charts `Bn` (over `U₁`) and `B'n` (over `U₀`) of a model of `ℙ¹` with overlap
`Wn = Bn[1/x₁] = B'n[1/x₀]`, all algebras over `O` (with an ideal `K ⊆ O`, the kernel of the
reduction; `J = K·`). An étale piece `E0` over `D(c₀) ⊆ Spec B'n` (formally étale over `B'n`,
`σE0 : E0/J ≃ C0[1/c̄₀]` for a special-fibre covering `C0` over `Bs'`), restricted to the overlap:

* `OverlapPiece.M x₀ E0 = E0[1/x₀]`, with its `Wn`-algebra structure `algWM` and its
  `Bn`-algebra structure `algBM`; **`formallyEtale_M`**: `M` is formally étale over `Bn`;
* the special fibre: for a special-fibre covering `C1` over `Bs` (the special fibre of `Bn`) and
  a **chart description of one special-fibre covering**, i.e. an isomorphism
  `ω : C0[1/x̄₀] ≃ₐ[Ws] C1[1/x̄₁]` over the special fibre `Ws` of the overlap,
  **`γM : C1 → M/JM`** (a `Bn`-algebra map) and **`isLocalization_γM`**: `M/JM = C1[1/ḡ]` for
  `g` with `c₀ x₁² = g` on the overlap and `x₁ ∣ g`.

This is the input `M`, `γM` of `NodeEtaleGlue.Input.glueM` (Tate case: `x₁ = h'`, `x₀ = h`,
`c₀ = 1 + h`, `g = h'(1 + h')`).
-/

universe u

namespace SemistableReduction

namespace OverlapPiece

noncomputable section

open EtaleNil

/-- The ideal `J = K·X` of an `O`-algebra `X` does not depend on the base. -/
lemma JB_map {O R X : Type u} [CommRing O] [CommRing R] [CommRing X] [Algebra O R] [Algebra R X]
    [Algebra O X] [IsScalarTower O R X] (K : Ideal O) :
    JB (K.map (algebraMap O R)) X = K.map (algebraMap O X) := by
  rw [JB, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- A localization transported along an isomorphism of the base. -/
lemma RingHomAway_base_equiv {S S' T : Type u} [CommRing S] [CommRing S'] [CommRing T]
    (e : S ≃+* S') (f : S →+* T) (x : S) (h : letI := f.toAlgebra; IsLocalization.Away x T) :
    letI := (f.comp e.symm.toRingHom).toAlgebra; IsLocalization.Away (e x) T := by
  letI := f.toAlgebra
  have h' := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers x) T e
  rw [Submonoid.map_powers] at h'
  exact h'

variable {O : Type u} [CommRing O] (K : Ideal O)
  {Bn B'n Wn : Type u} [CommRing Bn] [CommRing B'n] [CommRing Wn]
  [Algebra O Bn] [Algebra O B'n] [Algebra O Wn]
  [Algebra Bn Wn] [Algebra B'n Wn] [IsScalarTower O Bn Wn] [IsScalarTower O B'n Wn]
  (x0 : B'n) (hW0 : IsLocalization.Away x0 Wn)
  (E0 : Type u) [CommRing E0] [Algebra B'n E0] [Algebra O E0] [IsScalarTower O B'n E0]

/-- **The étale piece restricted to the overlap**: `E0[1/x₀]`. -/
abbrev M : Type u := Localization.Away (algebraMap B'n E0 x0)

lemma isUnit_x0 : IsUnit (algebraMap B'n (M x0 E0) x0) := by
  rw [IsScalarTower.algebraMap_apply B'n E0 (M x0 E0)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- `M` over the overlap `Wn = B'n[1/x₀]`. -/
@[reducible] def algWM : Algebra Wn (M x0 E0) :=
  haveI := hW0
  (IsLocalization.Away.lift x0 (S := Wn) (g := algebraMap B'n (M x0 E0))
    (isUnit_x0 x0 E0)).toAlgebra

lemma algWM_algebraMap (y : B'n) :
    (letI := algWM x0 hW0 E0; algebraMap Wn (M x0 E0) (algebraMap B'n Wn y)) =
      algebraMap B'n (M x0 E0) y :=
  haveI := hW0
  IsLocalization.Away.lift_eq x0 (isUnit_x0 x0 E0) y

lemma towerW : letI := algWM x0 hW0 E0; IsScalarTower B'n Wn (M x0 E0) :=
  letI := algWM x0 hW0 E0
  IsScalarTower.of_algebraMap_eq fun y ↦ (algWM_algebraMap x0 hW0 E0 y).symm

/-- `M` over `Bn` (through the overlap). -/
@[reducible] def algBM : Algebra Bn (M x0 E0) :=
  letI := algWM x0 hW0 E0
  ((algebraMap Wn (M x0 E0)).comp (algebraMap Bn Wn)).toAlgebra

lemma towerBW : letI := algWM x0 hW0 E0; letI := algBM x0 hW0 E0 (Bn := Bn)
    IsScalarTower Bn Wn (M x0 E0) :=
  letI := algWM x0 hW0 E0
  letI := algBM x0 hW0 E0 (Bn := Bn)
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

lemma towerOW : letI := algWM x0 hW0 E0; IsScalarTower O Wn (M x0 E0) := by
  letI := algWM x0 hW0 E0
  refine IsScalarTower.of_algebraMap_eq fun o ↦ ?_
  rw [IsScalarTower.algebraMap_apply O B'n Wn, algWM_algebraMap,
    ← IsScalarTower.algebraMap_apply O B'n (M x0 E0)]

lemma towerOB : letI := algBM x0 hW0 E0 (Bn := Bn); IsScalarTower O Bn (M x0 E0) := by
  letI := algWM x0 hW0 E0
  letI := algBM x0 hW0 E0 (Bn := Bn)
  haveI := towerOW x0 hW0 E0 (O := O)
  refine IsScalarTower.of_algebraMap_eq fun o ↦ ?_
  change _ = algebraMap Wn (M x0 E0) (algebraMap Bn Wn (algebraMap O Bn o))
  rw [← IsScalarTower.algebraMap_apply O Bn Wn, ← IsScalarTower.algebraMap_apply O Wn (M x0 E0)]

/-- `E0[1/x₀]` is formally étale over `B'n` if `E0` is. -/
theorem formallyEtale_loc [Algebra.FormallyEtale B'n E0] :
    Algebra.FormallyEtale B'n (M x0 E0) := by
  haveI : Algebra.FormallyEtale E0 (M x0 E0) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (algebraMap B'n E0 x0))
  exact Algebra.FormallyEtale.comp B'n E0 (M x0 E0)

variable {x1 : Bn} (hW1 : IsLocalization.Away x1 Wn)

include hW1 in
/-- **`M` is formally étale over `Bn`** if it is formally étale over `B'n`. -/
theorem formallyEtale_M [Algebra.FormallyEtale B'n (M x0 E0)] :
    letI := algBM x0 hW0 E0 (Bn := Bn)
    Algebra.FormallyEtale Bn (M x0 E0) := by
  letI := algWM x0 hW0 E0
  letI := algBM x0 hW0 E0 (Bn := Bn)
  haveI := towerW x0 hW0 E0
  haveI := towerBW x0 hW0 E0 (Bn := Bn)
  haveI := hW0
  haveI : Algebra.FormallyUnramified B'n Wn :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers x0)
  haveI : Algebra.FormallyEtale Wn (M x0 E0) := Algebra.FormallyEtale.of_restrictScalars (R := B'n)
  haveI := hW1
  haveI : Algebra.FormallyEtale Bn Wn := Algebra.FormallyEtale.of_isLocalization
    (Submonoid.powers x1)
  exact Algebra.FormallyEtale.comp Bn Wn (M x0 E0)

/-! ### The special fibre of an étale piece restricted to the overlap -/

variable {Bs Bs' Ws : Type u} [CommRing Bs] [CommRing Bs'] [CommRing Ws] [Algebra Bs Ws]
  [Algebra Bs' Ws] (qB : Bn →+* Bs) (qB' : B'n →+* Bs') (qW : Wn →+* Ws)
  {C1 C0 : Type u} [CommRing C1] [CommRing C0] [Algebra Bs C1] [Algebra Bs' C0]
  (x1s : Bs) (x0s c0s : Bs') (gs : Bs)
  [Algebra Ws (Localization.Away (algebraMap Bs C1 x1s))]
  [IsScalarTower Bs Ws (Localization.Away (algebraMap Bs C1 x1s))]
  [Algebra Ws (Localization.Away (algebraMap Bs' C0 x0s))]
  [IsScalarTower Bs' Ws (Localization.Away (algebraMap Bs' C0 x0s))]
  (ω : Localization.Away (algebraMap Bs' C0 x0s) ≃ₐ[Ws] Localization.Away (algebraMap Bs C1 x1s))
  (σE0 : letI := ((algebraMap Bs' C0).comp qB').toAlgebra
    (E0 ⧸ JB (K.map (algebraMap O B'n)) E0) ≃ₐ[B'n] Localization.Away (algebraMap Bs' C0 c0s))

/-- `C0 → C0[1/c̄₀] ≃ E0/J → M/J`. -/
def ℓ0 : C0 →+* M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0) :=
  letI := ((algebraMap Bs' C0).comp qB').toAlgebra
  (red (K.map (algebraMap O B'n)) (IsScalarTower.toAlgHom B'n E0 (M x0 E0))).toRingHom.comp
    (σE0.symm.toRingEquiv.toRingHom.comp (algebraMap C0 _))

omit [Algebra O E0] [IsScalarTower O B'n E0] in
lemma ℓ0_algebraMap (y : B'n) : ℓ0 K x0 E0 qB' c0s σE0 (algebraMap Bs' C0 (qB' y)) =
    Ideal.Quotient.mk _ (algebraMap B'n (M x0 E0) y) := by
  letI := ((algebraMap Bs' C0).comp qB').toAlgebra
  change red (K.map (algebraMap O B'n)) (IsScalarTower.toAlgHom B'n E0 (M x0 E0))
    (σE0.symm (algebraMap B'n _ y)) = _
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply B'n E0 (E0 ⧸ _)]
  change Ideal.Quotient.mk _ (algebraMap E0 (M x0 E0) (algebraMap B'n E0 y)) = _
  rw [← IsScalarTower.algebraMap_apply]

omit [Algebra O E0] [IsScalarTower O B'n E0] in
/-- `M/J = C0[1/(c̄₀ x̄₀)]`. -/
lemma isLocalization_ℓ0 (hx0 : qB' x0 = x0s) :
    letI := (ℓ0 K x0 E0 qB' c0s σE0).toAlgebra
    IsLocalization.Away (algebraMap Bs' C0 c0s * algebraMap Bs' C0 x0s)
      (M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0)) := by
  letI := ((algebraMap Bs' C0).comp qB').toAlgebra
  have h1 := RingHomAway.equiv (algebraMap C0 _) σE0.symm.toRingEquiv (algebraMap Bs' C0 c0s)
    (RingHomAway.of_algebra _)
  have h2 : letI := (red (K.map (algebraMap O B'n))
      (IsScalarTower.toAlgHom B'n E0 (M x0 E0))).toRingHom.toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (JB _ E0) (algebraMap B'n E0 x0))
        (M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0)) :=
    isLocalization_red _ (algebraMap B'n E0 x0)
  have e : (σE0.symm.toRingEquiv.toRingHom.comp (algebraMap C0 _)) (algebraMap Bs' C0 x0s) =
      Ideal.Quotient.mk (JB (K.map (algebraMap O B'n)) E0) (algebraMap B'n E0 x0) := by
    rw [← hx0]
    change σE0.symm (algebraMap B'n _ x0) = _
    rw [AlgEquiv.commutes]
    rfl
  rw [← e] at h2
  exact RingHomAway.comp _ _ _ _ h1 h2

/-! ### The special fibre of `M` from any special-fibre map `C0 → M/J`

Everything below only uses a ring map `l0 : C0 → M/J` compatible with the reduction of
`B'n → M` (`hl0`) exhibiting `M/J` as `C0[1/(c̄₀ x̄₀)]` (`hl0loc`); for an étale piece this is
`ℓ0` (from `σE0`), for a formal patch with cusp factors it comes from the étale lift on `D(f)`. -/

variable (l0 : C0 →+* M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0))
  (hl0loc : letI := l0.toAlgebra
    IsLocalization.Away (algebraMap Bs' C0 c0s * algebraMap Bs' C0 x0s)
      (M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0)))

omit [Algebra O E0] [IsScalarTower O B'n E0] in
include hl0loc in
lemma isUnit_l0 : IsUnit (l0 (algebraMap Bs' C0 x0s)) := by
  letI := l0.toAlgebra
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0))
    (algebraMap Bs' C0 c0s * algebraMap Bs' C0 x0s)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

/-- `C0[1/x̄₀] → M/J`. -/
def ℓx : Localization.Away (algebraMap Bs' C0 x0s) →+*
    M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0) :=
  IsLocalization.Away.lift (algebraMap Bs' C0 x0s) (isUnit_l0 K x0 E0 x0s c0s l0 hl0loc)

omit [Algebra O E0] [IsScalarTower O B'n E0] in
lemma ℓx_algebraMap (c : C0) : ℓx K x0 E0 x0s c0s l0 hl0loc (algebraMap C0 _ c) = l0 c :=
  IsLocalization.Away.lift_eq _ _ c

omit [Algebra O E0] [IsScalarTower O B'n E0] in
/-- `M/J = C0[1/x̄₀][1/c̄₀]`. -/
lemma isLocalization_ℓx :
    letI := (ℓx K x0 E0 x0s c0s l0 hl0loc).toAlgebra
    IsLocalization.Away (algebraMap C0 (Localization.Away (algebraMap Bs' C0 x0s))
      (algebraMap Bs' C0 c0s)) (M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0)) := by
  have h := hl0loc
  rw [mul_comm] at h
  have hc : (ℓx K x0 E0 x0s c0s l0 hl0loc).comp (algebraMap C0 _) = l0 :=
    IsLocalization.Away.lift_comp _ _
  rw [← hc] at h
  exact RingHomAway.of_comp _ _ _ _ (RingHomAway.of_algebra _) h

/-- `C1[1/x̄₁] ≃ C0[1/x̄₀] → M/J` (through the chart description `ω`). -/
def ℓ1 : Localization.Away (algebraMap Bs C1 x1s) →+*
    M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0) :=
  (ℓx K x0 E0 x0s c0s l0 hl0loc).comp ω.toRingEquiv.symm.toRingHom

omit [Algebra Bs Ws] [IsScalarTower Bs Ws (Localization.Away ((algebraMap Bs C1) x1s))] in
lemma ω_c0 : ω (algebraMap C0 _ (algebraMap Bs' C0 c0s)) =
    algebraMap Ws (Localization.Away (algebraMap Bs C1 x1s)) (algebraMap Bs' Ws c0s) := by
  rw [← IsScalarTower.algebraMap_apply Bs' C0 (Localization.Away (algebraMap Bs' C0 x0s)),
    IsScalarTower.algebraMap_apply Bs' Ws (Localization.Away (algebraMap Bs' C0 x0s)),
    AlgEquiv.commutes]

omit [Algebra Bs Ws] [IsScalarTower Bs Ws (Localization.Away ((algebraMap Bs C1) x1s))]
  [Algebra O E0] [IsScalarTower O B'n E0] in
/-- `M/J = C1[1/x̄₁][1/c̄₀]`. -/
lemma isLocalization_ℓ1 :
    letI := (ℓ1 K x0 E0 x1s x0s c0s ω l0 hl0loc).toAlgebra
    IsLocalization.Away (algebraMap Ws (Localization.Away (algebraMap Bs C1 x1s))
      (algebraMap Bs' Ws c0s)) (M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0)) := by
  have h := RingHomAway_base_equiv ω.toRingEquiv (ℓx K x0 E0 x0s c0s l0 hl0loc) _
    (isLocalization_ℓx K x0 E0 x0s c0s l0 hl0loc)
  have e : ω.toRingEquiv (algebraMap C0 _ (algebraMap Bs' C0 c0s)) =
      algebraMap Ws (Localization.Away (algebraMap Bs C1 x1s)) (algebraMap Bs' Ws c0s) :=
    ω_c0 x1s x0s c0s ω
  rw [e] at h
  exact h

variable {kc : ℕ} (hcg : algebraMap Bs' Ws c0s * algebraMap Bs Ws x1s ^ kc = algebraMap Bs Ws gs)
  (hxg : x1s ∣ gs)

/-- `C1 → M/J` (over `B'n`-quotients). -/
def γ0 : C1 →+* M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0) :=
  (ℓ1 K x0 E0 x1s x0s c0s ω l0 hl0loc).comp (algebraMap C1 _)

omit [Algebra O E0] [IsScalarTower O B'n E0] in
include hcg hxg in
/-- **`M/J = C1[1/ḡ]`.** -/
lemma isLocalization_γ0 :
    letI := (γ0 K x0 E0 x1s x0s c0s ω l0 hl0loc).toAlgebra
    IsLocalization.Away (algebraMap Bs C1 gs)
      (M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0)) := by
  set C1x := Localization.Away (algebraMap Bs C1 x1s)
  set X1 : C1x := algebraMap C1 C1x (algebraMap Bs C1 x1s)
  letI := (ℓ1 K x0 E0 x1s x0s c0s ω l0 hl0loc).toAlgebra
  haveI := isLocalization_ℓ1 K x0 E0 x1s x0s c0s ω l0 hl0loc
  have hX : IsUnit (algebraMap C1x (M x0 E0 ⧸ JB (K.map (algebraMap O B'n)) (M x0 E0))
      (X1 ^ kc)) :=
    ((IsLocalization.Away.algebraMap_isUnit (algebraMap Bs C1 x1s)).pow kc).map _
  have h2 := OverlapFibre.away_mul_of_isUnit (T := M x0 E0 ⧸ JB (K.map (algebraMap O B'n))
    (M x0 E0)) (X1 ^ kc) (algebraMap Ws C1x (algebraMap Bs' Ws c0s)) hX
  have hg : X1 ^ kc * algebraMap Ws C1x (algebraMap Bs' Ws c0s) =
      algebraMap C1 C1x (algebraMap Bs C1 gs) := by
    have := congrArg (algebraMap Ws C1x) hcg
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply Bs Ws C1x,
      ← IsScalarTower.algebraMap_apply Bs Ws C1x,
      IsScalarTower.algebraMap_apply Bs C1 C1x, IsScalarTower.algebraMap_apply Bs C1 C1x] at this
    rw [← this, mul_comm]
  rw [hg] at h2
  have h3 := RingHomAway.comp (algebraMap C1 C1x) (ℓ1 K x0 E0 x1s x0s c0s ω l0 hl0loc) _ _
    (RingHomAway.of_algebra (algebraMap Bs C1 x1s)) h2
  exact RingHomAway.of_dvd _ _ _ 1 (by rw [pow_one]; exact map_dvd _ hxg) h3

/-! ### `γM` as a map of `Bn`-algebras -/

variable (hq1 : ∀ r, qW (algebraMap Bn Wn r) = algebraMap Bs Ws (qB r))
  (hq0 : ∀ y, qW (algebraMap B'n Wn y) = algebraMap Bs' Ws (qB' y))
  (hl0 : ∀ y, l0 (algebraMap Bs' C0 (qB' y)) = Ideal.Quotient.mk _ (algebraMap B'n (M x0 E0) y))

omit [Algebra O Wn] [IsScalarTower O B'n Wn] [Algebra O E0] [IsScalarTower O B'n E0]
  in
include hq0 hl0 in
/-- `Ws → C0[1/x̄₀] → M/J` is the reduction of `Wn → M`. -/
lemma ℓx_qW (w : Wn) : ℓx K x0 E0 x0s c0s l0 hl0loc
    (algebraMap Ws (Localization.Away (algebraMap Bs' C0 x0s)) (qW w)) =
      Ideal.Quotient.mk _ (letI := algWM x0 hW0 E0; algebraMap Wn (M x0 E0) w) := by
  letI := algWM x0 hW0 E0
  haveI := hW0
  have : ((ℓx K x0 E0 x0s c0s l0 hl0loc).comp
      (algebraMap Ws (Localization.Away (algebraMap Bs' C0 x0s)))).comp qW =
      (Ideal.Quotient.mk (JB (K.map (algebraMap O B'n)) (M x0 E0))).comp
        (algebraMap Wn (M x0 E0)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers x0) (RingHom.ext fun y ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [hq0, ← IsScalarTower.algebraMap_apply Bs' Ws,
      IsScalarTower.algebraMap_apply Bs' C0 (Localization.Away (algebraMap Bs' C0 x0s)),
      ℓx_algebraMap, hl0, algWM_algebraMap]
  exact RingHom.congr_fun this w

/-- The two ideals `J` of `M` (over `B'n` and over `Bn`) agree. -/
lemma JB_eq : JB (K.map (algebraMap O B'n)) (M x0 E0) =
    (letI := algBM x0 hW0 E0 (Bn := Bn); JB (K.map (algebraMap O Bn)) (M x0 E0)) := by
  letI := algBM x0 hW0 E0 (Bn := Bn)
  haveI := towerOB x0 hW0 E0 (O := O) (Bn := Bn)
  rw [JB_map, JB_map]

/-- **`γM : C1 → M/JM`**, a map of `Bn`-algebras. -/
def γM : letI := ((algebraMap Bs C1).comp qB).toAlgebra
    letI := algBM x0 hW0 E0 (Bn := Bn)
    C1 →ₐ[Bn] M x0 E0 ⧸ JB (K.map (algebraMap O Bn)) (M x0 E0) :=
  letI := ((algebraMap Bs C1).comp qB).toAlgebra
  letI := algBM x0 hW0 E0 (Bn := Bn)
  { ((Ideal.quotEquivOfEq (JB_eq K x0 hW0 E0 (Bn := Bn))).toRingHom.comp
      (γ0 K x0 E0 x1s x0s c0s ω l0 hl0loc) : C1 →+* _) with
    commutes' := fun r ↦ by
      letI := algWM x0 hW0 E0
      change Ideal.quotEquivOfEq (JB_eq K x0 hW0 E0 (Bn := Bn))
        (ℓ1 K x0 E0 x1s x0s c0s ω l0 hl0loc (algebraMap C1 _ (algebraMap Bs C1 (qB r)))) =
          Ideal.Quotient.mk _ (algebraMap Wn (M x0 E0) (algebraMap Bn Wn r))
      rw [← IsScalarTower.algebraMap_apply Bs C1,
        IsScalarTower.algebraMap_apply Bs Ws (Localization.Away (algebraMap Bs C1 x1s)), ← hq1]
      change Ideal.quotEquivOfEq _ (ℓx K x0 E0 x0s c0s l0 hl0loc (ω.symm (algebraMap Ws _ _))) = _
      rw [AlgEquiv.commutes, ℓx_qW K x0 hW0 E0 qB' qW x0s c0s l0 hl0loc hq0 hl0]
      rfl }

include hcg hxg in
/-- **`M/JM = C1[1/ḡ]`** (the input of `NodeEtaleGlue.Input.glueM`). -/
theorem isLocalization_γM :
    letI := ((algebraMap Bs C1).comp qB).toAlgebra
    letI := algBM x0 hW0 E0 (Bn := Bn)
    letI := (γM K x0 hW0 E0 qB qB' qW x1s x0s c0s ω l0 hl0loc hq1 hq0 hl0).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap Bs C1 gs)
      (M x0 E0 ⧸ JB (K.map (algebraMap O Bn)) (M x0 E0)) :=
  RingHomAway.equiv _ (Ideal.quotEquivOfEq (JB_eq K x0 hW0 E0 (Bn := Bn))) _
    (isLocalization_γ0 K x0 E0 x1s x0s c0s gs ω l0 hl0loc hcg hxg)

end

end OverlapPiece

end SemistableReduction
