/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Orbifold.EtaleOfAlgebra
import TemperedFundamentalGroups.Andre.QuadraticLevel

/-!
# Involutions of the étale fundamental group fix all square roots of units

Let `K` be a field in which `2 ≠ 0` and `-1` is a sum of squares (e.g. a complete discretely
valued field of residue characteristic `p > 0`, `Setup/NegOneSumSq.lean`), `R` a `K`-algebra,
`A` trivial, and `Ω` an algebraically closed field with a map `R → Ω`. For an element `g` of the
étale fundamental group `etalePi1 R A Ω` and a finite étale `R`-algebra `B`, `ptAct g B` is the
action of `g` on the geometric points `B →ₐ[R] Ω` (through the coded object
`EquivEtale.ofAlgebra`); it is natural in `B` (`ptAct_comp`).

**Main result** (`fixQ_of_mul_self_eq_one`): **if `g² = 1`, then `g` fixes the geometric points
of every Kummer covering `R[√c]`, `c ∈ Rˣ`.** In particular an involution of `π₁` never acts by
the deck involution of a Kummer double covering. The proof is elementary (Artin–Schreier style):

* `QE a = S[X]/(X² − a)`: finite, étale for `2, a` units (`QE.etale`); the points of `QE c` over
  `R` are swapped by the involution `QE.σ`, so `g` either fixes or swaps them all
  (`fixQ_or_swapQ`).
* **`g` swaps the points of `R[√−1]`** (`not_swapQ_neg_one`): then the set of `x ∈ Kˣ` whose
  square roots are fixed contains the squares and is closed under sums (`fixQ_add`: for points
  `P` of `R[√x, √y, i, √(√x + √y i)]` and `P' = g P`, the product `P(w) · P'(w)` is a square root
  of `x + y` fixed by `g`, by naturality along the conjugation `i ↦ −i` and `g² = 1`), so it
  contains `−1`, a contradiction;
* **`g` fixes the points of `R[√−1]`** (`fixQ_of_fixQ_neg_one`): if `g` swapped `±√c`, a fourth
  root `w` of `c` would satisfy `g w = ±i w` and `g² w = −w` (naturality along `w ↦ ±i w`).
-/

universe u

open Polynomial CategoryTheory Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

namespace EtaleInvolution

/-! ### Quadratic extensions `S[X]/(X² − a)` -/

section Quad

variable {S : Type u} [CommRing S]

/-- **The quadratic extension** `S[X]/(X² − a)`. -/
abbrev QE (a : S) : Type u := AdjoinRoot (QuadraticLevel.f a)

namespace QE

/-- The square root of `a`. -/
def rt (a : S) : QE a := AdjoinRoot.root _

lemma rt_sq (a : S) : rt a ^ 2 = algebraMap S (QE a) a := by
  have h := AdjoinRoot.eval₂_root (QuadraticLevel.f a)
  simp only [QuadraticLevel.f, eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.1 h

instance (a : S) : Module.Finite S (QE a) :=
  (AdjoinRoot.powerBasis' (QuadraticLevel.monic_f a)).finite

lemma hasMap (a : S) (h2 : IsUnit (2 : S)) (ha : IsUnit a) :
    (QuadraticLevel.pair h2 ha).HasMap (rt a) := by
  refine ⟨?_, by simp [QuadraticLevel.pair]⟩
  change aeval (rt a) (QuadraticLevel.f a) = 0
  rw [rt, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-- `QE a ≃` the standard étale algebra of `(X² − a, 1)`. -/
def equivStandard {a : S} (h2 : IsUnit (2 : S)) (ha : IsUnit a) :
    (QuadraticLevel.pair h2 ha).Ring ≃ₐ[S] QE a :=
  AlgEquiv.ofAlgHom ((QuadraticLevel.pair h2 ha).lift (rt a) (hasMap a h2 ha))
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId S _) (QuadraticLevel.pair h2 ha).X (by
      have := (QuadraticLevel.pair h2 ha).hasMap_X.1
      rwa [aeval_def] at this))
    (AdjoinRoot.algHom_ext (by simp [rt]))
    ((QuadraticLevel.pair h2 ha).hom_ext (by simp [rt]))

/-- **`QE a` is étale** for `2, a` units. -/
lemma etale {a : S} (h2 : IsUnit (2 : S)) (ha : IsUnit a) : Algebra.Etale S (QE a) :=
  Algebra.Etale.of_equiv (equivStandard h2 ha)

variable {R : Type u} [CommRing R] [Algebra R S]

/-- Lifting along `S → QE a` with a chosen square root. -/
def lift {T : Type u} [CommRing T] [Algebra R T] {a : S} (φ : S →ₐ[R] T) (x : T)
    (hx : x ^ 2 = φ a) : QE a →ₐ[R] T :=
  AdjoinRoot.liftAlgHom _ φ x (by
    simp only [QuadraticLevel.f, eval₂_sub, eval₂_X_pow, eval₂_C]
    rw [hx]
    exact sub_self _)

@[simp] lemma lift_rt {T : Type u} [CommRing T] [Algebra R T] {a : S} (φ : S →ₐ[R] T) (x : T)
    (hx : x ^ 2 = φ a) : lift φ x hx (rt a) = x :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp] lemma lift_algebraMap {T : Type u} [CommRing T] [Algebra R T] {a : S} (φ : S →ₐ[R] T)
    (x : T) (hx : x ^ 2 = φ a) (s : S) : lift φ x hx (algebraMap S (QE a) s) = φ s :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ _

/-- The inclusion `S → QE a` as an `R`-algebra map. -/
abbrev ι (a : S) : S →ₐ[R] QE a := IsScalarTower.toAlgHom R S (QE a)

lemma ι_apply (a : S) (s : S) : ι (R := R) a s = algebraMap S (QE a) s := rfl

@[simp] lemma lift_ι {T : Type u} [CommRing T] [Algebra R T] {a : S} (φ : S →ₐ[R] T)
    (x : T) (hx : x ^ 2 = φ a) (s : S) : lift φ x hx (ι (R := R) a s) = φ s :=
  lift_algebraMap φ x hx s

/-- `R`-algebra maps out of `QE a` agree if they agree on `S` and on the square root. -/
lemma hom_ext {T : Type u} [CommRing T] [Algebra R T] {a : S} {f g : QE a →ₐ[R] T}
    (hS : f.comp (ι a) = g.comp (ι a)) (hr : f (rt a) = g (rt a)) : f = g :=
  AdjoinRoot.algHom_ext' hS hr

lemma rt_isUnit {a : S} (ha : IsUnit a) : IsUnit (rt a) := by
  have h : IsUnit (rt a ^ 2) := by
    rw [rt_sq]
    exact ha.map _
  exact isUnit_of_mul_isUnit_left (by rwa [sq] at h)

end QE

end Quad

/-! ### Kummer coverings of `R`: points, the involution -/

section Kummer

variable {R : Type u} [CommRing R]

namespace QE

/-- The involution `√c ↦ −√c` of `R[√c]`. -/
def σ (c : R) : QE c →ₐ[R] QE c :=
  lift (Algebra.ofId R _) (-rt c) (by rw [neg_sq, rt_sq]; rfl)

@[simp] lemma σ_rt (c : R) : σ c (rt c) = -rt c := lift_rt _ _ _

lemma σ_σ (c : R) : (σ c).comp (σ c) = AlgHom.id R _ :=
  AdjoinRoot.algHom_ext (by
    change σ c (σ c (rt c)) = rt c
    rw [σ_rt, map_neg, σ_rt, neg_neg])

/-- Points of `R[√c]` are determined by the image of the square root. -/
lemma pt_ext {T : Type u} [CommRing T] [Algebra R T] {c : R} {t t' : QE c →ₐ[R] T}
    (h : t (rt c) = t' (rt c)) : t = t' :=
  AdjoinRoot.algHom_ext h

/-- Points of `R[√c]` in a domain: the two square roots. -/
lemma pt_eq_or {T : Type u} [CommRing T] [IsDomain T] [Algebra R T] {c : R}
    (t t' : QE c →ₐ[R] T) : t' = t ∨ t' = t.comp (σ c) := by
  have h : t' (rt c) ^ 2 = t (rt c) ^ 2 := by
    rw [← map_pow, ← map_pow, rt_sq, AlgHom.commutes, AlgHom.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact Or.inl (pt_ext h)
  · refine Or.inr (pt_ext ?_)
    rw [h, AlgHom.comp_apply, σ_rt, map_neg]

lemma pt_rt_ne_zero {T : Type u} [CommRing T] [Nontrivial T] [Algebra R T] {c : R}
    (hc : IsUnit c) (t : QE c →ₐ[R] T) : t (rt c) ≠ 0 :=
  ((rt_isUnit hc).map t).ne_zero

lemma comp_σ_ne {T : Type u} [CommRing T] [IsDomain T] [Algebra R T] {c : R} (hc : IsUnit c)
    (h2 : (2 : T) ≠ 0) (t : QE c →ₐ[R] T) : t.comp (σ c) ≠ t := by
  intro h
  have h' := congrArg (fun φ : QE c →ₐ[R] T ↦ φ (rt c)) h
  simp only [AlgHom.comp_apply, σ_rt, map_neg] at h'
  have : (2 : T) * t (rt c) = 0 := by linear_combination -h'
  exact pt_rt_ne_zero hc t ((mul_eq_zero.1 this).resolve_left h2)

end QE

end Kummer

/-! ### The action of `π₁ᵉᵗ` on geometric points of finite étale algebras -/

section PtAct

variable {R : Type u} [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [CommRing Ω] [Algebra R Ω]

/-- The coded object of a finite étale `R`-algebra with the trivial action of `A`. -/
def etObj (B : Type u) [CommRing B] [Algebra R B] (he : Algebra.Etale R B)
    (hf : Module.Finite R B) : EquivEtale R A :=
  EquivEtale.ofAlgebra (1 : A →* SemilinearAut R A B) fun _ ↦ Subsingleton.elim _ _

/-- The coded object is isomorphic to `B`. -/
def etEquiv (B : Type u) [CommRing B] [Algebra R B] (he : Algebra.Etale R B)
    (hf : Module.Finite R B) : (etObj A B he hf).B ≃ₐ[R] B :=
  EquivEtale.ofAlgebraEquiv _ _

lemma etObj_act (B : Type u) [CommRing B] [Algebra R B] (he : Algebra.Etale R B)
    (hf : Module.Finite R B) (a : A) : (etObj A B he hf).act a = 1 := by
  change SemilinearAut.congr _ ((1 : A →* SemilinearAut R A B) a) = 1
  rw [MonoidHom.one_apply, map_one]

/-- The morphism of coded objects induced by an `R`-algebra map. -/
def etHom {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (he : Algebra.Etale R B) (hf : Module.Finite R B) (he' : Algebra.Etale R B')
    (hf' : Module.Finite R B') (f : B →ₐ[R] B') : etObj A B' he' hf' ⟶ etObj A B he hf where
  f := ((etEquiv A B' he' hf').symm.toAlgHom.comp f).comp (etEquiv A B he hf).toAlgHom
  f_act a y := by
    rw [etObj_act, etObj_act]
    rfl

variable {A}

/-- The action of `g` on the fibre of a coded object, as a map of points. -/
def appAlg (g : etalePi1 R A Ω) (X : EquivEtale R A) (x : X.B →ₐ[R] Ω) : X.B →ₐ[R] Ω :=
  g.app X x

omit [Subsingleton A] in
lemma appAlg_naturality (g : etalePi1 R A Ω) {X Y : EquivEtale R A} (m : X ⟶ Y)
    (x : X.B →ₐ[R] Ω) : appAlg g Y (x.comp m.f) = (appAlg g X x).comp m.f :=
  FibreAut.app_naturality g m x

omit [Subsingleton A] in
lemma appAlg_mul (g h : etalePi1 R A Ω) (X : EquivEtale R A) (x : X.B →ₐ[R] Ω) :
    appAlg (g * h) X x = appAlg g X (appAlg h X x) := rfl

omit [Subsingleton A] in
lemma appAlg_one (X : EquivEtale R A) (x : X.B →ₐ[R] Ω) : appAlg 1 X x = x := rfl

/-- **The action of `g ∈ π₁ᵉᵗ` on the geometric points of a finite étale `R`-algebra.** -/
def ptAct (g : etalePi1 R A Ω) (B : Type u) [CommRing B] [Algebra R B] (he : Algebra.Etale R B)
    (hf : Module.Finite R B) (t : B →ₐ[R] Ω) : B →ₐ[R] Ω :=
  (appAlg g (etObj A B he hf) (t.comp (etEquiv A B he hf).toAlgHom)).comp
    (etEquiv A B he hf).symm.toAlgHom

/-- **Naturality** of the action on points. -/
lemma ptAct_comp (g : etalePi1 R A Ω) {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B']
    [Algebra R B'] (he : Algebra.Etale R B) (hf : Module.Finite R B) (he' : Algebra.Etale R B')
    (hf' : Module.Finite R B') (f : B →ₐ[R] B') (t : B' →ₐ[R] Ω) :
    ptAct g B he hf (t.comp f) = (ptAct g B' he' hf' t).comp f := by
  have h := appAlg_naturality g (etHom A he hf he' hf' f)
    (t.comp (etEquiv A B' he' hf').toAlgHom)
  have hx : (t.comp (etEquiv A B' he' hf').toAlgHom).comp (etHom A he hf he' hf' f).f =
      (t.comp f).comp (etEquiv A B he hf).toAlgHom := by
    change (t.comp (etEquiv A B' he' hf').toAlgHom).comp
      (((etEquiv A B' he' hf').symm.toAlgHom.comp f).comp (etEquiv A B he hf).toAlgHom) = _
    ext b
    simp
  rw [hx] at h
  ext b
  simp only [ptAct, AlgHom.comp_apply]
  rw [h]
  change (appAlg g (etObj A B' he' hf') (t.comp (etEquiv A B' he' hf').toAlgHom))
      ((etEquiv A B' he' hf').symm (f ((etEquiv A B he hf) ((etEquiv A B he hf).symm b)))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

lemma ptAct_mul (g h : etalePi1 R A Ω) (B : Type u) [CommRing B] [Algebra R B]
    (he : Algebra.Etale R B) (hf : Module.Finite R B) (t : B →ₐ[R] Ω) :
    ptAct (g * h) B he hf t = ptAct g B he hf (ptAct h B he hf t) := by
  unfold ptAct
  rw [appAlg_mul]
  congr 2
  ext b
  simp

/-- An involution acts by an involution on points. -/
lemma ptAct_ptAct {g : etalePi1 R A Ω} (hg : g * g = 1) (B : Type u) [CommRing B]
    [Algebra R B] (he : Algebra.Etale R B) (hf : Module.Finite R B) (t : B →ₐ[R] Ω) :
    ptAct g B he hf (ptAct g B he hf t) = t := by
  rw [← ptAct_mul, hg]
  ext b
  simp [ptAct, appAlg_one]

/-- The point of `R` itself is fixed. -/
lemma ptAct_self (g : etalePi1 R A Ω) (he : Algebra.Etale R R) (hf : Module.Finite R R)
    (t : R →ₐ[R] Ω) : ptAct g R he hf t = t :=
  Subsingleton.elim _ _

end PtAct

/-! ### Fixing or swapping the square roots -/

section FixSwap

lemma two_isUnit_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (h2 : IsUnit (2 : R)) :
    IsUnit (2 : S) := by
  have := h2.map (algebraMap R S)
  rwa [map_ofNat] at this

namespace QE

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]

lemma etale_trans (he : Algebra.Etale R S) {a : S} (h2 : IsUnit (2 : S)) (ha : IsUnit a) :
    Algebra.Etale R (QE a) :=
  haveI := QE.etale h2 ha
  Algebra.Etale.comp R S (QE a)

lemma finite_trans (hf : Module.Finite R S) (a : S) : Module.Finite R (QE a) :=
  Module.Finite.trans S (QE a)

end QE

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra R Ω]

/-- `g` **fixes** the geometric points of the Kummer covering `R[√c]`. -/
def FixQ (g : etalePi1 R A Ω) {c : R} (h2 : IsUnit (2 : R)) (hc : IsUnit c) : Prop :=
  ∀ t : QE c →ₐ[R] Ω, ptAct g (QE c) (QE.etale h2 hc) inferInstance t = t

/-- `g` **swaps** the geometric points of the Kummer covering `R[√c]`. -/
def SwapQ (g : etalePi1 R A Ω) {c : R} (h2 : IsUnit (2 : R)) (hc : IsUnit c) : Prop :=
  ∀ t : QE c →ₐ[R] Ω, ptAct g (QE c) (QE.etale h2 hc) inferInstance t = t.comp (QE.σ c)

variable (g : etalePi1 R A Ω) {c : R} (h2 : IsUnit (2 : R)) (hc : IsUnit c)

lemma ptAct_comp_σ (t : QE c →ₐ[R] Ω) :
    ptAct g (QE c) (QE.etale h2 hc) inferInstance (t.comp (QE.σ c)) =
      (ptAct g (QE c) (QE.etale h2 hc) inferInstance t).comp (QE.σ c) :=
  ptAct_comp g _ _ _ _ _ _

/-- Fixing one point of `R[√c]` is fixing all. -/
lemma fixQ_of_fix {t : QE c →ₐ[R] Ω} (ht : ptAct g (QE c) (QE.etale h2 hc) inferInstance t = t) :
    FixQ g h2 hc := by
  intro t'
  rcases QE.pt_eq_or t t' with rfl | rfl
  · exact ht
  · rw [ptAct_comp_σ g h2 hc, ht]

/-- **`g` fixes or swaps the points of `R[√c]`.** -/
lemma fixQ_or_swapQ : FixQ g h2 hc ∨ SwapQ g h2 hc := by
  by_cases h : FixQ g h2 hc
  · exact Or.inl h
  · refine Or.inr ?_
    obtain ⟨t₁, ht₁⟩ : ∃ t₁ : QE c →ₐ[R] Ω,
        ptAct g (QE c) (QE.etale h2 hc) inferInstance t₁ ≠ t₁ := by
      by_contra hc'
      push Not at hc'
      exact h hc'
    have hs : ptAct g (QE c) (QE.etale h2 hc) inferInstance t₁ = t₁.comp (QE.σ c) :=
      (QE.pt_eq_or t₁ _).resolve_left ht₁
    intro t
    rcases QE.pt_eq_or t₁ t with rfl | rfl
    · exact hs
    · rw [ptAct_comp_σ g h2 hc, hs, AlgHom.comp_assoc, QE.σ_σ, AlgHom.comp_id]

/-- Fixing and swapping exclude each other as soon as there is a point. -/
lemma not_fixQ_and_swapQ (h2Ω : (2 : Ω) ≠ 0) (t : QE c →ₐ[R] Ω) :
    ¬ (FixQ g h2 hc ∧ SwapQ g h2 hc) := fun ⟨hF, hS⟩ ↦
  QE.comp_σ_ne hc h2Ω t ((hS t).symm.trans (hF t))

lemma fixQ_congr {c' : R} (hcc : c = c') (hc' : IsUnit c') : FixQ g h2 hc ↔ FixQ g h2 hc' := by
  subst hcc
  rfl

/-- Extending a point to `S[√a]` in an algebraically closed field. -/
def QE.extend [IsAlgClosed Ω] {S : Type u} [CommRing S] [Algebra R S] (φ : S →ₐ[R] Ω) (a : S) :
    QE a →ₐ[R] Ω :=
  QE.lift φ (IsAlgClosed.exists_pow_nat_eq (φ a) two_pos).choose
    (IsAlgClosed.exists_pow_nat_eq (φ a) two_pos).choose_spec

/-- A point of `R[√c]` in an algebraically closed field. -/
def QE.pt [IsAlgClosed Ω] (c : R) : QE c →ₐ[R] Ω :=
  QE.extend (Algebra.ofId R Ω) c

end FixSwap

/-! ### First case: `g` fixes `√−1` -/

section CaseFix

namespace Quartic

variable (R : Type u) [CommRing R]

/-- `S₁ = R[i]`. -/
abbrev S1 : Type u := QE (-1 : R)

variable {R} (c : R)

/-- `S₂ = S₁[√c]`. -/
abbrev S2 : Type u := QE (algebraMap R (S1 R) c)

/-- `S₃ = S₂[c^{1/4}]`. -/
abbrev S3 : Type u := QE (QE.rt (algebraMap R (S1 R) c))

/-- `i ∈ S₁`. -/
abbrev i : S1 R := QE.rt (-1 : R)

/-- `√c ∈ S₂`. -/
abbrev s : S2 c := QE.rt _

/-- `c^{1/4} ∈ S₃`. -/
abbrev w : S3 c := QE.rt _

/-- `S₁ → S₂`. -/
abbrev ι21 : S1 R →ₐ[R] S2 c := QE.ι _

/-- `S₂ → S₃`. -/
abbrev ι32 : S2 c →ₐ[R] S3 c := QE.ι _

lemma i_sq : i (R := R) ^ 2 = -1 := by
  rw [QE.rt_sq, map_neg, map_one]

lemma ι32_s_sq : ι32 c (s c) ^ 2 = algebraMap R (S3 c) c := by
  rw [← map_pow, QE.rt_sq]
  simp only [IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply]

lemma w_sq : w c ^ 2 = ι32 c (s c) := QE.rt_sq _

/-- `R[√c] → S₃`, `√c ↦ w²`. -/
def jc : QE c →ₐ[R] S3 c := QE.lift (Algebra.ofId R _) (ι32 c (s c)) (ι32_s_sq c)

/-- The involution `√c ↦ −√c` of `S₂` over `S₁`. -/
def σ2 : S2 c →ₐ[R] S2 c :=
  QE.lift (ι21 c) (-s c) (by rw [neg_sq, QE.rt_sq]; rfl)

lemma σ2_ι21 (x : S1 R) : σ2 c (ι21 c x) = ι21 c x := QE.lift_algebraMap _ _ _ _

/-- **`w ↦ e w`** (`e² = −1`), `√c ↦ −√c`. -/
def μ (e : S1 R) (he : e ^ 2 = -1) : S3 c →ₐ[R] S3 c :=
  QE.lift ((ι32 c).comp (σ2 c)) (ι32 c (ι21 c e) * w c) (by
    rw [mul_pow, ← map_pow, ← map_pow, he, w_sq, AlgHom.comp_apply, σ2, QE.lift_rt, map_neg,
      map_neg, map_one, map_neg, map_one]
    ring)

lemma μ_w (e : S1 R) (he : e ^ 2 = -1) : μ c e he (w c) = ι32 c (ι21 c e) * w c :=
  QE.lift_rt _ _ _

lemma μ_ι32 (e : S1 R) (he : e ^ 2 = -1) (x : S2 c) : μ c e he (ι32 c x) = ι32 c (σ2 c x) :=
  QE.lift_algebraMap _ _ _ _

lemma μ_ι (e : S1 R) (he : e ^ 2 = -1) (x : S1 R) :
    μ c e he (ι32 c (ι21 c x)) = ι32 c (ι21 c x) := by
  rw [μ_ι32, σ2_ι21]

lemma μ_s (e : S1 R) (he : e ^ 2 = -1) : μ c e he (ι32 c (s c)) = -ι32 c (s c) := by
  rw [μ_ι32, σ2, QE.lift_rt, map_neg]

/-- Points of `S₃` are determined by `i`, `√c`, `w`. -/
lemma ext3 {T : Type u} [CommRing T] [Algebra R T] {f f' : S3 c →ₐ[R] T}
    (hi : f (ι32 c (ι21 c i)) = f' (ι32 c (ι21 c i))) (hs : f (ι32 c (s c)) = f' (ι32 c (s c)))
    (hw : f (w c) = f' (w c)) : f = f' := by
  refine QE.hom_ext (QE.hom_ext ?_ hs) hw
  exact QE.pt_ext hi

end Quartic

open Quartic

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra R Ω]

/-- **First case**: if `g² = 1` fixes the points of `R[√−1]`, it fixes those of `R[√c]` for every
unit `c` (otherwise `g w = ±i w` and `g² w = −w` for a fourth root `w` of `c`). -/
theorem fixQ_of_fixQ_neg_one [IsAlgClosed Ω] (g : etalePi1 R A Ω) (hg : g * g = 1)
    (h2 : IsUnit (2 : R)) {c : R} (hc : IsUnit c)
    (hi : FixQ g h2 (isUnit_one.neg : IsUnit (-1 : R))) : FixQ g h2 hc := by
  rcases fixQ_or_swapQ g h2 hc with h | hS
  · exact h
  exfalso
  have hu1 : IsUnit (-1 : R) := isUnit_one.neg
  have e1 : Algebra.Etale R (S1 R) := QE.etale h2 hu1
  have h2S1 : IsUnit (2 : S1 R) := two_isUnit_map h2
  have hcS1 : IsUnit (algebraMap R (S1 R) c) := hc.map _
  have e2 : Algebra.Etale R (S2 c) := QE.etale_trans e1 h2S1 hcS1
  have f2 : Module.Finite R (S2 c) := QE.finite_trans inferInstance _
  have h2S2 : IsUnit (2 : S2 c) := two_isUnit_map h2S1
  have hs : IsUnit (s c) := QE.rt_isUnit hcS1
  have e3 : Algebra.Etale R (S3 c) := QE.etale_trans e2 h2S2 hs
  have f3 : Module.Finite R (S3 c) := QE.finite_trans f2 _
  have h2Ω : (2 : Ω) ≠ 0 := (two_isUnit_map (S := Ω) h2).ne_zero
  -- a point `P` of `S₃` and its image `P'`
  let P : S3 c →ₐ[R] Ω := QE.extend (QE.extend (QE.pt (-1 : R)) _) _
  set P' := ptAct g (S3 c) e3 f3 P with hP'def
  have hPi : P'.comp ((ι32 c).comp (ι21 c)) = P.comp ((ι32 c).comp (ι21 c)) := by
    rw [← ptAct_comp g e1 inferInstance e3 f3]
    exact hi _
  have hPs : P' (ι32 c (s c)) = -P (ι32 c (s c)) := by
    have h := ptAct_comp g (QE.etale h2 hc) inferInstance e3 f3 (jc c) P
    rw [hS] at h
    have h' := congrArg (fun φ : QE c →ₐ[R] Ω ↦ φ (QE.rt c)) h
    simp only [AlgHom.comp_apply, QE.σ_rt, map_neg, jc, QE.lift_rt] at h'
    exact h'.symm
  have hι : P (ι32 c (ι21 c i)) ^ 2 = -1 := by
    rw [← map_pow, ← map_pow, ← map_pow, i_sq, map_neg, map_neg, map_neg, map_one, map_one,
      map_one]
  have hw2 : P' (w c) ^ 2 = (P (ι32 c (ι21 c i)) * P (w c)) ^ 2 := by
    rw [← map_pow, w_sq, hPs, mul_pow, hι, ← map_pow, w_sq]
    ring
  obtain ⟨e, he, hPe⟩ : ∃ e : S1 R, e ^ 2 = -1 ∧
      P' (w c) = P (ι32 c (ι21 c e)) * P (w c) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hw2 with h | h
    · exact ⟨i, i_sq, h⟩
    · refine ⟨-i, by rw [neg_sq, i_sq], ?_⟩
      rw [h, map_neg, map_neg, map_neg, neg_mul]
  have hP' : P' = P.comp (μ c e he) := by
    refine ext3 c ?_ ?_ ?_
    · rw [AlgHom.comp_apply, μ_ι]
      exact congrArg (fun φ : S1 R →ₐ[R] Ω ↦ φ i) hPi
    · rw [AlgHom.comp_apply, μ_s, map_neg, hPs]
    · rw [AlgHom.comp_apply, μ_w, map_mul, hPe]
  have hPP := ptAct_ptAct hg (S3 c) e3 f3 P
  rw [← hP'def, hP', ptAct_comp g e3 f3 e3 f3 (μ c e he) P, ← hP'def, hP'] at hPP
  have h' := congrArg (fun φ : S3 c →ₐ[R] Ω ↦ φ (w c)) hPP
  simp only [AlgHom.comp_apply, μ_w, map_mul, μ_ι] at h'
  have h'' : P (w c) * 2 = 0 := by
    have hι' : P (ι32 c (ι21 c e)) ^ 2 = -1 := by
      rw [← map_pow, ← map_pow, ← map_pow, he, map_neg, map_neg, map_neg, map_one, map_one, map_one]
    linear_combination (-1 : Ω) * h' + P (w c) * hι'
  have hw0 : P (w c) ≠ 0 := ((QE.rt_isUnit hs).map P).ne_zero
  exact hw0 ((mul_eq_zero.1 h'').resolve_right h2Ω)

end CaseFix

/-! ### Second case: `g` swaps `√−1` -/

section CaseSwap

namespace Biquad

variable {K : Type u} [Field K] (R : Type u) [CommRing R] [Algebra K R] (x y : K)

/-- `T₁ = R[√x]`. -/
abbrev T1 : Type u := QE (algebraMap K R x)

/-- `√x ∈ T₁`. -/
abbrev u : T1 R x := QE.rt _

/-- `T₂ = T₁[√y]`. -/
abbrev T2 : Type u := QE (algebraMap R (T1 R x) (algebraMap K R y))

/-- `√y ∈ T₂`. -/
abbrev v : T2 R x y := QE.rt _

/-- `T₃ = T₂[i]`. -/
abbrev T3 : Type u := QE (-1 : T2 R x y)

/-- `i ∈ T₃`. -/
abbrev ii : T3 R x y := QE.rt _

/-- `T₁ → T₂`. -/
abbrev ι21 : T1 R x →ₐ[R] T2 R x y := QE.ι _

/-- `T₂ → T₃`. -/
abbrev ι32 : T2 R x y →ₐ[R] T3 R x y := QE.ι _

/-- `√x ∈ T₃`. -/
abbrev uu : T3 R x y := ι32 R x y (ι21 R x y (u R x))

/-- `√y ∈ T₃`. -/
abbrev vv : T3 R x y := ι32 R x y (v R x y)

/-- `T₄ = T₃[√(√x + √y i)]`. -/
abbrev T4 : Type u := QE (uu R x y + vv R x y * ii R x y)

/-- `w = √(√x + √y i) ∈ T₄`. -/
abbrev w : T4 R x y := QE.rt _

/-- `T₃ → T₄`. -/
abbrev ι43 : T3 R x y →ₐ[R] T4 R x y := QE.ι _

/-- `T₅ = T₄[√(√x − √y i)]`. -/
abbrev T5 : Type u := QE (ι43 R x y (uu R x y - vv R x y * ii R x y))

/-- `w' = √(√x − √y i) ∈ T₅`. -/
abbrev w' : T5 R x y := QE.rt _

/-- `T₄ → T₅`. -/
abbrev ι54 : T4 R x y →ₐ[R] T5 R x y := QE.ι _

lemma uu_sq : uu R x y ^ 2 = algebraMap R _ (algebraMap K R x) := by
  rw [← map_pow, ← map_pow, QE.rt_sq, AlgHom.commutes, AlgHom.commutes]

lemma vv_sq : vv R x y ^ 2 = algebraMap R _ (algebraMap K R y) := by
  rw [← map_pow, QE.rt_sq]
  exact (AlgHom.commutes _ _).trans (by rw [IsScalarTower.algebraMap_apply R (T1 R x)])

lemma ii_sq : ii R x y ^ 2 = -1 := by
  rw [QE.rt_sq, map_neg, map_one]

lemma mul_conj : (uu R x y + vv R x y * ii R x y) * (uu R x y - vv R x y * ii R x y) =
    algebraMap R _ (algebraMap K R (x + y)) := by
  have h : (uu R x y + vv R x y * ii R x y) * (uu R x y - vv R x y * ii R x y) =
      uu R x y ^ 2 - vv R x y ^ 2 * ii R x y ^ 2 := by ring
  rw [h, uu_sq, vv_sq, ii_sq, map_add, map_add]
  ring

/-- The conjugation `i ↦ −i` of `T₃` over `T₂`. -/
def conj3 : T3 R x y →ₐ[R] T3 R x y :=
  QE.lift (ι32 R x y) (-ii R x y) (by rw [neg_sq, QE.rt_sq]; rfl)

lemma conj3_ι32 (z : T2 R x y) : conj3 R x y (ι32 R x y z) = ι32 R x y z :=
  QE.lift_algebraMap _ _ _ _

lemma conj3_ii : conj3 R x y (ii R x y) = -ii R x y := QE.lift_rt _ _ _

lemma conj3_conj :
    conj3 R x y (uu R x y + vv R x y * ii R x y) = uu R x y - vv R x y * ii R x y := by
  rw [map_add, map_mul, conj3_ι32, conj3_ι32, conj3_ii]
  ring

/-- **`ψ : T₄ → T₅`**: `√x ↦ √x`, `√y ↦ √y`, `i ↦ −i`, `w ↦ w'`. -/
def ψ : T4 R x y →ₐ[R] T5 R x y :=
  QE.lift (((ι54 R x y).comp (ι43 R x y)).comp (conj3 R x y)) (w' R x y) (by
    rw [QE.rt_sq, AlgHom.comp_apply, AlgHom.comp_apply, conj3_conj]
    rfl)

lemma ψ_ι43 (z : T3 R x y) : ψ R x y (ι43 R x y z) = ι54 R x y (ι43 R x y (conj3 R x y z)) :=
  QE.lift_algebraMap _ _ _ _

lemma ψ_w : ψ R x y (w R x y) = w' R x y := QE.lift_rt _ _ _

/-- `R[√y] → T₄`. -/
def jy : QE (algebraMap K R y) →ₐ[R] T4 R x y :=
  QE.lift (Algebra.ofId R _) (ι43 R x y (vv R x y)) (by
    rw [← map_pow, vv_sq]
    exact AlgHom.commutes _ _)

/-- `R[√−1] → T₄`. -/
def jm : QE (-1 : R) →ₐ[R] T4 R x y :=
  QE.lift (Algebra.ofId R _) (ι43 R x y (ii R x y)) (by
    rw [← map_pow, ii_sq, map_neg, map_one, map_neg, map_one])

/-- `R[√x] = T₁ → T₄`. -/
abbrev ju : T1 R x →ₐ[R] T4 R x y := ((ι43 R x y).comp (ι32 R x y)).comp (ι21 R x y)

/-- `R[√(x + y)] → T₅`, `√(x + y) ↦ w w'`. -/
def jxy : QE (algebraMap K R (x + y)) →ₐ[R] T5 R x y :=
  QE.lift (Algebra.ofId R _) (ι54 R x y (w R x y) * w' R x y) (by
    rw [mul_pow, ← map_pow, QE.rt_sq, QE.rt_sq]
    change ι54 R x y (ι43 R x y _) * ι54 R x y (ι43 R x y _) = _
    rw [← map_mul, ← map_mul, mul_conj, AlgHom.commutes, AlgHom.commutes]
    rfl)

/-- Points of `T₄` are determined by `√x`, `√y`, `i`, `w`. -/
lemma ext4 {T : Type u} [CommRing T] [Algebra R T] {f f' : T4 R x y →ₐ[R] T}
    (hu : f (ι43 R x y (uu R x y)) = f' (ι43 R x y (uu R x y)))
    (hv : f (ι43 R x y (vv R x y)) = f' (ι43 R x y (vv R x y)))
    (hi : f (ι43 R x y (ii R x y)) = f' (ι43 R x y (ii R x y))) (hw : f (w R x y) = f' (w R x y)) :
    f = f' :=
  QE.hom_ext (QE.hom_ext (QE.hom_ext (QE.pt_ext hu) hv) hi) hw

end Biquad

open Biquad

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra R Ω]

lemma isUnit_algebraMap {x : K} (hx : x ≠ 0) : IsUnit (algebraMap K R x) :=
  (Ne.isUnit hx).map _

/-- The core of `fixQ_add`, for an abstract tower `T₄ → T₅` with the relevant elements and maps
(`T₄ = R[√x, √y, i, w]`, `w² = √x + √y i`, `T₅ = T₄[w']`, `w'² = √x − √y i`, `ψ` the
conjugation). -/
theorem fixQ_add_core (g : etalePi1 R A Ω) (hg : g * g = 1) (h2 : IsUnit (2 : R))
    (hm : SwapQ g h2 (isUnit_one.neg : IsUnit (-1 : R))) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) (hfx : FixQ g h2 (isUnit_algebraMap (R := R) hx))
    (hfy : FixQ g h2 (isUnit_algebraMap (R := R) hy))
    {T4 T5 : Type u} [CommRing T4] [Algebra R T4] [CommRing T5] [Algebra R T5]
    (e4 : Algebra.Etale R T4) (f4 : Module.Finite R T4) (e5 : Algebra.Etale R T5)
    (f5 : Module.Finite R T5) (au av ai w : T4) (w' : T5) (ι ψ : T4 →ₐ[R] T5)
    (ju : QE (algebraMap K R x) →ₐ[R] T4) (hju : ju (QE.rt _) = au)
    (jy : QE (algebraMap K R y) →ₐ[R] T4) (hjy : jy (QE.rt _) = av)
    (jm : QE (-1 : R) →ₐ[R] T4) (hjm : jm (QE.rt _) = ai)
    (jxy : QE (algebraMap K R (x + y)) →ₐ[R] T5) (hjxy : jxy (QE.rt _) = ι w * w')
    (hψu : ψ au = ι au) (hψv : ψ av = ι av) (hψi : ψ ai = -ι ai) (hψw : ψ w = w')
    (hw : w ^ 2 = au + av * ai)
    (hext : ∀ f f' : T4 →ₐ[R] Ω, f au = f' au → f av = f' av → f ai = f' ai → f w = f' w →
      f = f')
    (hlift : ∀ (P : T4 →ₐ[R] Ω) (z : Ω), z ^ 2 = P (au - av * ai) →
      ∃ P5 : T5 →ₐ[R] Ω, P5.comp ι = P ∧ P5 w' = z)
    (P : T4 →ₐ[R] Ω) : FixQ g h2 (isUnit_algebraMap (R := R) hxy) := by
  obtain ⟨P', hP'def⟩ : ∃ P', P' = ptAct g T4 e4 f4 P := ⟨_, rfl⟩
  have hu : P' au = P au := by
    have h := ptAct_comp g (QE.etale h2 (isUnit_algebraMap hx)) inferInstance e4 f4 ju P
    rw [hfx, ← hP'def] at h
    have h' := congrArg (fun φ : QE (algebraMap K R x) →ₐ[R] Ω ↦ φ (QE.rt _)) h
    simp only [AlgHom.comp_apply, hju] at h'
    exact h'.symm
  have hv : P' av = P av := by
    have h := ptAct_comp g (QE.etale h2 (isUnit_algebraMap hy)) inferInstance e4 f4 jy P
    rw [hfy, ← hP'def] at h
    have h' := congrArg (fun φ : QE (algebraMap K R y) →ₐ[R] Ω ↦ φ (QE.rt _)) h
    simp only [AlgHom.comp_apply, hjy] at h'
    exact h'.symm
  have hi : P' ai = -P ai := by
    have h := ptAct_comp g (QE.etale h2 isUnit_one.neg) inferInstance e4 f4 jm P
    rw [hm, ← hP'def] at h
    have h' := congrArg (fun φ : QE (-1 : R) →ₐ[R] Ω ↦ φ (QE.rt _)) h
    simp only [AlgHom.comp_apply, QE.σ_rt, map_neg, hjm] at h'
    exact h'.symm
  have hP'w : P' w ^ 2 = P (au - av * ai) := by
    rw [← map_pow, hw, map_add, map_mul, map_sub, map_mul, hu, hv, hi]
    ring
  obtain ⟨P5, hP5ι, hP5w⟩ := hlift P (P' w) hP'w
  have hP5z (z : T4) : P5 (ι z) = P z := congrArg (fun φ : T4 →ₐ[R] Ω ↦ φ z) hP5ι
  have hP5ψ : P5.comp ψ = P' := by
    refine hext _ _ ?_ ?_ ?_ ?_
    · rw [AlgHom.comp_apply, hψu, hP5z, hu]
    · rw [AlgHom.comp_apply, hψv, hP5z, hv]
    · rw [AlgHom.comp_apply, hψi, map_neg, hP5z, hi]
    · rw [AlgHom.comp_apply, hψw, hP5w]
  obtain ⟨Q5, hQ5def⟩ : ∃ Q5, Q5 = ptAct g T5 e5 f5 P5 := ⟨_, rfl⟩
  have hQι : Q5.comp ι = P' := by
    rw [hQ5def, ← ptAct_comp g e4 f4 e5 f5, hP5ι, hP'def]
  have hQψ : Q5.comp ψ = P := by
    rw [hQ5def, ← ptAct_comp g e4 f4 e5 f5, hP5ψ, hP'def, ptAct_ptAct hg]
  -- the fixed point of `R[√(x + y)]`
  refine fixQ_of_fix g h2 (isUnit_algebraMap hxy) (t := P5.comp jxy) ?_
  rw [ptAct_comp g _ _ e5 f5, ← hQ5def]
  refine QE.pt_ext ?_
  simp only [AlgHom.comp_apply, hjxy, map_mul]
  have h1 : Q5 (ι w) = P' w := congrArg (fun φ : T4 →ₐ[R] Ω ↦ φ w) hQι
  have h2' : Q5 w' = P w := by
    rw [← hψw]
    exact congrArg (fun φ : T4 →ₐ[R] Ω ↦ φ w) hQψ
  rw [h1, h2', hP5z, hP5w, mul_comm]

/-- **Sums of fixed square roots**: if `g² = 1` swaps `±√−1` and fixes `±√x`, `±√y`, it fixes
`±√(x + y)` (`P(w) · (gP)(w)` is a square root of `x + y` fixed by `g`). -/
theorem fixQ_add [IsAlgClosed Ω] (g : etalePi1 R A Ω) (hg : g * g = 1) (h2 : IsUnit (2 : R))
    (hm : SwapQ g h2 (isUnit_one.neg : IsUnit (-1 : R))) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) (hfx : FixQ g h2 (isUnit_algebraMap (R := R) hx))
    (hfy : FixQ g h2 (isUnit_algebraMap (R := R) hy)) :
    FixQ g h2 (isUnit_algebraMap (R := R) hxy) := by
  have e1 : Algebra.Etale R (T1 R x) := QE.etale h2 (isUnit_algebraMap hx)
  have e2 : Algebra.Etale R (T2 R x y) :=
    QE.etale_trans e1 (two_isUnit_map h2) ((isUnit_algebraMap hy).map _)
  have f2 : Module.Finite R (T2 R x y) := QE.finite_trans inferInstance _
  have h2T2 : IsUnit (2 : T2 R x y) := two_isUnit_map (two_isUnit_map (S := T1 R x) h2)
  have e3 : Algebra.Etale R (T3 R x y) := QE.etale_trans e2 h2T2 isUnit_one.neg
  have f3 : Module.Finite R (T3 R x y) := QE.finite_trans f2 _
  have h2T3 : IsUnit (2 : T3 R x y) := two_isUnit_map h2T2
  have hmc : IsUnit ((uu R x y + vv R x y * ii R x y) * (uu R x y - vv R x y * ii R x y)) := by
    rw [mul_conj]
    exact (isUnit_algebraMap hxy).map _
  have e4 : Algebra.Etale R (T4 R x y) :=
    QE.etale_trans e3 h2T3 (isUnit_of_mul_isUnit_left hmc)
  have f4 : Module.Finite R (T4 R x y) := QE.finite_trans f3 _
  have e5 : Algebra.Etale R (T5 R x y) :=
    QE.etale_trans e4 (two_isUnit_map h2T3) ((isUnit_of_mul_isUnit_right hmc).map _)
  have f5 : Module.Finite R (T5 R x y) := QE.finite_trans f4 _
  have hju : ju R x y (QE.rt _) = ι43 R x y (uu R x y) := rfl
  have hψu : ψ R x y (ι43 R x y (uu R x y)) = ι54 R x y (ι43 R x y (uu R x y)) :=
    (ψ_ι43 R x y _).trans (congrArg (fun z ↦ ι54 R x y (ι43 R x y z)) (conj3_ι32 R x y _))
  have hψv : ψ R x y (ι43 R x y (vv R x y)) = ι54 R x y (ι43 R x y (vv R x y)) :=
    (ψ_ι43 R x y _).trans (congrArg (fun z ↦ ι54 R x y (ι43 R x y z)) (conj3_ι32 R x y _))
  have hψi : ψ R x y (ι43 R x y (ii R x y)) = -ι54 R x y (ι43 R x y (ii R x y)) :=
    ((ψ_ι43 R x y _).trans (congrArg (fun z ↦ ι54 R x y (ι43 R x y z)) (conj3_ii R x y))).trans
      ((congrArg (ι54 R x y) (map_neg (ι43 R x y) _)).trans (map_neg (ι54 R x y) _))
  have hw : w R x y ^ 2 = ι43 R x y (uu R x y) + ι43 R x y (vv R x y) * ι43 R x y (ii R x y) :=
    (QE.rt_sq _).trans ((QE.ι_apply (R := R) _ _).symm.trans ((map_add (ι43 R x y) _ _).trans
      (congrArg (ι43 R x y (uu R x y) + ·) (map_mul (ι43 R x y) _ _))))
  have hlift : ∀ (P : T4 R x y →ₐ[R] Ω) (z : Ω),
      z ^ 2 = P (ι43 R x y (uu R x y) - ι43 R x y (vv R x y) * ι43 R x y (ii R x y)) →
      ∃ P5 : T5 R x y →ₐ[R] Ω, P5.comp (ι54 R x y) = P ∧ P5 (w' R x y) = z := by
    intro P z hz
    have hz' : z ^ 2 = P (ι43 R x y (uu R x y - vv R x y * ii R x y)) := by
      rw [hz, map_sub (ι43 R x y), map_mul (ι43 R x y)]
    exact ⟨QE.lift P z hz', AlgHom.ext fun t ↦ QE.lift_ι P z hz' t, QE.lift_rt _ _ _⟩
  exact fixQ_add_core g hg h2 hm hx hy hxy hfx hfy e4 f4 e5 f5 (ι43 R x y (uu R x y))
    (ι43 R x y (vv R x y)) (ι43 R x y (ii R x y)) (w R x y) (w' R x y) (ι54 R x y) (ψ R x y)
    (ju R x y) hju (jy R x y) (QE.lift_rt _ _ _) (jm R x y) (QE.lift_rt _ _ _) (jxy R x y)
    (QE.lift_rt _ _ _) hψu hψv hψi (ψ_w R x y) hw (fun f f' ↦ ext4 R x y) hlift
    (QE.extend (QE.extend (QE.extend (QE.pt (algebraMap K R x)) _) _) _)

end CaseSwap

/-! ### The main result -/

section Main

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra R Ω]

/-- Nonzero squares of `K` have fixed square roots (they are constant). -/
theorem fixQ_sq (g : etalePi1 R A Ω) (h2 : IsUnit (2 : R)) {a : K} (ha : a * a ≠ 0) :
    FixQ g h2 (isUnit_algebraMap (R := R) ha) := by
  let f : QE (algebraMap K R (a * a)) →ₐ[R] R :=
    QE.lift (AlgHom.id R R) (algebraMap K R a) (by rw [sq, map_mul]; rfl)
  refine fixQ_of_fix g h2 _ (t := (Algebra.ofId R Ω).comp f) ?_
  rw [ptAct_comp g _ _ inferInstance inferInstance f, ptAct_self]

/-- **If `g² = 1` swaps `±√−1`, all nonzero sums of squares of `K` have fixed square roots.** -/
theorem fixQ_of_isSumSq [IsAlgClosed Ω] (g : etalePi1 R A Ω) (hg : g * g = 1)
    (h2 : IsUnit (2 : R)) (hm : SwapQ g h2 (isUnit_one.neg : IsUnit (-1 : R))) {s : K}
    (hs : IsSumSq s) (hs0 : s ≠ 0) : FixQ g h2 (isUnit_algebraMap (R := R) hs0) := by
  induction hs with
  | zero => exact absurd rfl hs0
  | @sq_add a t ht ih =>
    by_cases ht0 : t = 0
    · subst ht0
      have ha : a * a ≠ 0 := by rwa [add_zero] at hs0
      exact (fixQ_congr g h2 (isUnit_algebraMap ha) (by rw [add_zero])
        (isUnit_algebraMap hs0)).1 (fixQ_sq g h2 ha)
    · by_cases ha : a * a = 0
      · exact (fixQ_congr g h2 (isUnit_algebraMap ht0) (by rw [ha, zero_add])
          (isUnit_algebraMap hs0)).1 (ih ht0)
      · exact fixQ_add g hg h2 hm ha ht0 hs0 (fixQ_sq g h2 ha) (ih ht0)

/-- **Involutions of `π₁ᵉᵗ` fix all square roots of units**: if `−1` is a sum of squares in
`K`, `2` is a unit of `R` and `g² = 1`, then `g` fixes the geometric points of `R[√c]` for every
unit `c` of `R`. -/
theorem fixQ_of_mul_self_eq_one [IsAlgClosed Ω] (hK : IsSumSq (-1 : K)) (g : etalePi1 R A Ω)
    (hg : g * g = 1) (h2 : IsUnit (2 : R)) {c : R} (hc : IsUnit c) : FixQ g h2 hc := by
  refine fixQ_of_fixQ_neg_one g hg h2 hc ?_
  rcases fixQ_or_swapQ g h2 (isUnit_one.neg : IsUnit (-1 : R)) with h | hS
  · exact h
  · exfalso
    have h1 : (-1 : K) ≠ 0 := neg_ne_zero.2 one_ne_zero
    have hF := fixQ_of_isSumSq g hg h2 hS hK h1
    rw [fixQ_congr g h2 _ (by rw [map_neg, map_one]) isUnit_one.neg] at hF
    have h2Ω : (2 : Ω) ≠ 0 := (two_isUnit_map (S := Ω) h2).ne_zero
    exact not_fixQ_and_swapQ g h2 isUnit_one.neg h2Ω (QE.pt _) ⟨hF, hS⟩

/-- **An involution of `π₁ᵉᵗ` never acts on a Kummer double covering by its deck involution.** -/
theorem not_swapQ_of_mul_self_eq_one [IsAlgClosed Ω] (hK : IsSumSq (-1 : K))
    (g : etalePi1 R A Ω) (hg : g * g = 1) (h2 : IsUnit (2 : R)) {c : R} (hc : IsUnit c) :
    ¬ SwapQ g h2 hc := fun hS ↦
  not_fixQ_and_swapQ g h2 hc (two_isUnit_map (S := Ω) h2).ne_zero (QE.pt c)
    ⟨fixQ_of_mul_self_eq_one hK g hg h2 hc, hS⟩

end Main

end EtaleInvolution

end

end TemperedFundamentalGroups
