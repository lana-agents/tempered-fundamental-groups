/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.AdmissibleCuspPatch
import TemperedFundamentalGroups.SemistableReduction.CuspNormalForm

/-!
# Maps of formal cusp models lift to the levels (MR12 I3, generic core, layer 3)

MR12 I3, generic core layer 3: maps of formal cusp models lift to the levels.

Let `cov`, `cov'` be two admissible coverings of the same chart (`Admissible.Covering`) with only
cusp factors (no Kummer factors at the nodes), and `NFall L M`, `NFall L' M'` their lifted formal
models at a level `O` (`AdmissibleLift.NFall`, the cusp factors
`CPiece f δ̃ t̃ e = (R̂/(1 − δ̃))[X]/(X^e − t̃)` over the same lift `t̃` of the coordinate at the
marked points). A map `Φ : ∏_i CuspPiece_i → ∏_{i'} CuspPiece'_{i'}` of the formal models at the
special fibre lifts to a map `g : NFall L M → NFall L' M'` of `R̂`-algebras reducing to `Φ`
(**`AdmissibleLift.exists_cuspNFMap`**), provided the bases `A_{i'} = R̂'/(1 − δ_{i'})` of the
target factors satisfy the hypotheses of the Kummer normal form (`CuspNormalForm`): `t` is a
nonzerodivisor on `A_{i'}`, `A_{i'}/(t)` is reduced and `A_{i'}` is `t`-adically separated.

The construction ([Mzk1] §3.9 (1′A): morphisms of tamely ramified coverings near the marked points
are Kummer):

* `E_i = Φ(1_i)` are complete orthogonal idempotents; they lift to complete orthogonal
  idempotents `Ẽ_i` along the nilpotent ideal `J`
  (Mathlib `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`);
* `y_i = Φ(X_i)` satisfies `y_i^{e_i} = t E_i`, so on each target factor `y_i = X'^{e'/e_i} u`
  with `u^{e_i} = E_i` (`CuspNormalForm.exists_normalForm`); `u E_i + (1 − E_i)` is an `e_i`-th
  root of unity, which lifts (`CuspNormalForm.exists_pow_eq_one_lift`, `e_i` invertible);
* `g` sends `X_i` to `Ẽ_i X̃'^{e'/e_i} ṽ_i` (`CuspHom.pieceMap`, through the decomposition
  `S ≃ ∏_i S/(1 − Ẽ_i)`, Mathlib `CompleteOrthogonalIdempotents.bijective_pi`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace AdmissibleLift

noncomputable section

namespace CuspHom

/-! ### Generic algebra -/

section Nil

variable {S T : Type*} [CommRing S] [CommRing T] (ρ : S →+* T)
  (hN : ∀ x ∈ RingHom.ker ρ, IsNilpotent x)

include hN in
/-- An idempotent in a nilpotent kernel vanishes. -/
lemma idem_eq_zero {a : S} (ha : IsIdempotentElem a) (h : ρ a = 0) : a = 0 :=
  ha.eq_zero_of_isNilpotent (hN a (RingHom.mem_ker.mpr h))

include hN in
/-- Units lift along surjections with nilpotent kernel. -/
lemma isUnit_of_map (hρ : Function.Surjective ρ) {a : S} (h : IsUnit (ρ a)) : IsUnit a := by
  obtain ⟨b, hb⟩ := hρ ↑(h.unit⁻¹)
  have h1 : a * b - 1 ∈ RingHom.ker ρ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hb, IsUnit.mul_val_inv, sub_self]
  have h2 : IsUnit (a * b) := by
    have h3 := (hN _ h1).isUnit_add_one
    rwa [sub_add_cancel] at h3
  exact isUnit_of_mul_isUnit_left h2

end Nil

lemma pow_eq_zero_of_mem_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {J : Ideal R} {n : ℕ} (hJ : J ^ n = ⊥) {x : S} (hx : x ∈ J.map φ) : x ^ n = 0 := by
  have h := Ideal.pow_mem_pow hx n
  rw [← Ideal.map_pow, hJ, Ideal.map_bot, Ideal.mem_bot] at h
  exact h

/-- `(u E + (1 − E))^e = 1` if `u^e = E` and `E` is idempotent. -/
lemma pow_corner_add {T : Type*} [CommRing T] {E u : T} (hE : E * E = E) {e : ℕ} (he : 0 < e)
    (hu : u ^ e = E) : (u * E + (1 - E)) ^ e = 1 := by
  have key : ∀ m : ℕ, (u * E + (1 - E)) ^ (m + 1) = u ^ (m + 1) * E + (1 - E) := by
    intro m
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]
    | succ m ih =>
      rw [pow_succ, ih]
      linear_combination (u ^ (m + 2) - u ^ (m + 1) - u + 1) * hE
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, (Nat.sub_add_cancel he).symm⟩
  rw [key, hu]
  linear_combination hE

/-- Two additive and multiplicative maps out of `AdjoinRoot q` agreeing on the base and the root
agree. -/
lemma adjoinRoot_ext {A T : Type*} [CommRing A] [CommRing T] {q : A[X]}
    (F₁ F₂ : AdjoinRoot q → T)
    (hadd₁ : ∀ a b, F₁ (a + b) = F₁ a + F₁ b) (hadd₂ : ∀ a b, F₂ (a + b) = F₂ a + F₂ b)
    (hmul₁ : ∀ a b, F₁ (a * b) = F₁ a * F₁ b) (hmul₂ : ∀ a b, F₂ (a * b) = F₂ a * F₂ b)
    (hof : ∀ c, F₁ (AdjoinRoot.of q c) = F₂ (AdjoinRoot.of q c))
    (hroot : F₁ (AdjoinRoot.root q) = F₂ (AdjoinRoot.root q)) (a : AdjoinRoot q) :
    F₁ a = F₂ a := by
  induction a using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C c => rw [AdjoinRoot.mk_C]; exact hof c
    | add p r hp hr => rw [map_add, hadd₁, hadd₂, hp, hr]
    | monomial m c h =>
      have e : AdjoinRoot.mk q (C c * X ^ (m + 1)) =
          AdjoinRoot.mk q (C c * X ^ m) * AdjoinRoot.root q := by
        rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
      rw [e, hmul₁, hmul₂, h, hroot]

/-- Ring maps out of a finite product agreeing on each factor agree. -/
lemma pi_ringHom_ext {κ : Type*} [Finite κ] [DecidableEq κ] {P : κ → Type*}
    [∀ i, CommRing (P i)] {T : Type*} [CommRing T] (φ₁ φ₂ : (∀ i, P i) →+* T)
    (h : ∀ i (a : P i), φ₁ (Pi.single i a) = φ₂ (Pi.single i a)) (z : ∀ i, P i) :
    φ₁ z = φ₂ z := by
  cases nonempty_fintype κ
  rw [← Finset.univ_sum_single z, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ h i (z i)

lemma single_map_add {κ : Type*} [DecidableEq κ] {P : κ → Type*} [∀ i, CommRing (P i)]
    {T : Type*} [CommRing T] (φ : (∀ i, P i) →+* T) (i : κ) (a b : P i) :
    φ (Pi.single i (a + b)) = φ (Pi.single i a) + φ (Pi.single i b) := by
  rw [Pi.single_add, map_add]

lemma single_map_mul {κ : Type*} [DecidableEq κ] {P : κ → Type*} [∀ i, CommRing (P i)]
    {T : Type*} [CommRing T] (φ : (∀ i, P i) →+* T) (i : κ) (a b : P i) :
    φ (Pi.single i (a * b)) = φ (Pi.single i a) * φ (Pi.single i b) := by
  rw [Pi.single_mul, map_mul]

lemma single_pow {κ : Type*} [DecidableEq κ] {P : κ → Type*} [∀ i, CommRing (P i)] (i : κ)
    (a : P i) {m : ℕ} (hm : 0 < m) : (Pi.single i a : ∀ i, P i) ^ m = Pi.single i (a ^ m) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  induction m with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ m ih => rw [pow_succ, ih (Nat.succ_pos m), ← Pi.single_mul, ← pow_succ]

/-! ### Corners of complete orthogonal idempotents -/

section Corner

variable {S : Type*} [CommRing S] {κ : Type*} {E : κ → S}

lemma mk_self (i : κ) : Ideal.Quotient.mk (Ideal.span {1 - E i}) (E i) = 1 :=
  (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨-1, by ring⟩)).trans (map_one _)

lemma mk_ne (hE : OrthogonalIdempotents E) {i j : κ} (hji : j ≠ i) (w : S) :
    Ideal.Quotient.mk (Ideal.span {1 - E j}) (E i * w) = 0 := by
  have h0 : E i * E j = 0 := hE.ortho hji.symm
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨E i * w, by linear_combination (-w) * h0⟩

end Corner

/-! ### Maps out of a product of cusp factors -/

section PieceMap

variable {R : Type u} [CommRing R] (f : R) {S : Type u} [CommRing S]
  [Algebra (FormalPatchLevel.Hat f) S] {κ : Type} [Fintype κ]
  (δ : κ → FormalPatchLevel.Hat f) (t : FormalPatchLevel.Hat f) (e : κ → ℕ)
  {E : κ → S} (y : κ → S)
  (hδ : ∀ i, algebraMap (FormalPatchLevel.Hat f) S (1 - δ i) * E i = 0)
  (hy : ∀ i, y i ^ e i * E i = algebraMap (FormalPatchLevel.Hat f) S t * E i)

/-- `R̂/(1 − δ_i) → S/(1 − E_i)`. -/
def baseMap (i : κ) : CBase f (δ i) →+* S ⧸ Ideal.span {1 - E i} :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (algebraMap _ S)) fun a ha ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have h1 : Ideal.Quotient.mk (Ideal.span {1 - E i})
        (algebraMap (FormalPatchLevel.Hat f) S (1 - δ i)) = 0 := by
      calc _ = Ideal.Quotient.mk (Ideal.span {1 - E i})
              (algebraMap (FormalPatchLevel.Hat f) S (1 - δ i)) *
            Ideal.Quotient.mk (Ideal.span {1 - E i}) (E i) := by rw [mk_self, mul_one]
        _ = 0 := by rw [← map_mul, hδ i, map_zero]
    rw [RingHom.comp_apply, map_mul, map_mul, h1, mul_zero]

omit [Fintype κ] in
include hy in
lemma eval_root (i : κ) : (cpoly f (δ i) t (e i)).eval₂ (baseMap f δ hδ i)
    (Ideal.Quotient.mk (Ideal.span {1 - E i}) (y i)) = 0 := by
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, baseMap, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  calc _ = Ideal.Quotient.mk (Ideal.span {1 - E i}) (y i ^ e i) *
          Ideal.Quotient.mk (Ideal.span {1 - E i}) (E i) -
        Ideal.Quotient.mk (Ideal.span {1 - E i}) (algebraMap _ S t) := by
          rw [mk_self, mul_one, map_pow]
    _ = 0 := by rw [← map_mul, hy i, map_mul, mk_self, mul_one, sub_self]

/-- The factor `i`: `R̂/(1 − δ_i)[X]/(X^{e_i} − t) → S/(1 − E_i)`, `X ↦ y_i`. -/
def rootMap (i : κ) : CPiece f (δ i) t (e i) →+* S ⧸ Ideal.span {1 - E i} :=
  AdjoinRoot.lift (baseMap f δ hδ i) (Ideal.Quotient.mk _ (y i)) (eval_root f δ t e y hδ hy i)

variable {f δ t e y}
variable (hE : CompleteOrthogonalIdempotents E)

/-- The ring map `∏_i R̂/(1 − δ_i)[X]/(X^{e_i} − t) → S`, `1_i ↦ E_i`, `X_i ↦ E_i y_i`. -/
def pieceRingHom : (∀ i, CPiece f (δ i) t (e i)) →+* S :=
  (RingEquiv.ofBijective _ hE.bijective_pi).symm.toRingHom.comp
    (RingHom.pi fun i ↦ (rootMap f δ t e y hδ hy i).comp (Pi.evalRingHom _ i))

lemma pieceRingHom_eq {z : ∀ i, CPiece f (δ i) t (e i)} {s : S}
    (h : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - E i}) s = rootMap f δ t e y hδ hy i (z i)) :
    pieceRingHom hδ hy hE z = s := by
  change (RingEquiv.ofBijective _ hE.bijective_pi).symm
    ((RingHom.pi fun i ↦ (rootMap f δ t e y hδ hy i).comp (Pi.evalRingHom _ i)) z) = s
  rw [RingEquiv.symm_apply_eq]
  funext i
  exact (h i).symm

lemma pieceRingHom_algebraMap (a : FormalPatchLevel.Hat f) :
    pieceRingHom hδ hy hE (algebraMap _ _ a) = algebraMap (FormalPatchLevel.Hat f) S a := by
  refine pieceRingHom_eq hδ hy hE fun i ↦ ?_
  change _ = rootMap f δ t e y hδ hy i (AdjoinRoot.of _ (Ideal.Quotient.mk _ a))
  rw [rootMap, AdjoinRoot.lift_of, baseMap, Ideal.Quotient.lift_mk]
  rfl

/-- The `R̂`-algebra map `∏_i R̂/(1 − δ_i)[X]/(X^{e_i} − t) → S`, `1_i ↦ E_i`, `X_i ↦ E_i y_i`. -/
def pieceMap : (∀ i, CPiece f (δ i) t (e i)) →ₐ[FormalPatchLevel.Hat f] S :=
  { pieceRingHom hδ hy hE with commutes' := pieceRingHom_algebraMap hδ hy hE }

lemma pieceMap_apply (z : ∀ i, CPiece f (δ i) t (e i)) :
    pieceMap hδ hy hE z = pieceRingHom hδ hy hE z := rfl

lemma pieceMap_single_one [DecidableEq κ] (i : κ) :
    pieceMap hδ hy hE (Pi.single i 1) = E i := by
  refine pieceRingHom_eq hδ hy hE fun j ↦ ?_
  by_cases hji : j = i
  · subst hji
    rw [Pi.single_eq_same, map_one, mk_self]
  · rw [Pi.single_eq_of_ne hji, map_zero, ← mul_one (E i), mk_ne hE.1 hji]

lemma pieceMap_single_root [DecidableEq κ] (i : κ) :
    pieceMap hδ hy hE (Pi.single i (AdjoinRoot.root _)) = E i * y i := by
  refine pieceRingHom_eq hδ hy hE fun j ↦ ?_
  by_cases hji : j = i
  · subst hji
    rw [Pi.single_eq_same, map_mul, mk_self, one_mul, rootMap, AdjoinRoot.lift_root]
  · rw [Pi.single_eq_of_ne hji, map_zero, mk_ne hE.1 hji]

end PieceMap

/-- The hypotheses of the Kummer normal form on a base `A` with coordinate `t`: `t` is a
nonzerodivisor, `A/(t)` is reduced, and `A` is `t`-adically separated. -/
def NFHyp (A : Type u) [CommRing A] (t : A) : Prop :=
  IsSMulRegular A t ∧ IsReduced (A ⧸ Ideal.span {t}) ∧ ∀ a : A, (∀ m : ℕ, t ^ m ∣ a) → a = 0

end CuspHom

/-! ### The reduction of a product of lifted cusp factors -/

section Red

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  {R : Type u} [CommRing R] [Algebra O R] (f : R) [Algebra k (R ⧸ J θ)]
  (ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f))

lemma cuspEquiv_root [IsNoetherianRing R] (δ t : FormalPatchLevel.Hat f)
    (δb : Admissible.Hat (fbar θ f)) (hδ : ψ θ f δ = δb) (ht : ψ θ f t = ψc X) (e : ℕ) :
    cuspEquiv θ f ψc δ t δb hδ ht e (Ideal.Quotient.mk _ (AdjoinRoot.root (cpoly f δ t e))) =
      AdjoinRoot.root _ := by
  have h1 : AdjoinRoot.root (cpoly f δ t e) = AdjoinRoot.mk (cpoly f δ t e) X := rfl
  rw [cuspEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, h1, Ideal.quotEquivOfEq_mk,
    AlgEquiv.coe_ringEquiv, AdjoinRoot.quotEquivQuotMap_apply_mk]
  erw [Ideal.quotientEquiv_mk]
  rw [Polynomial.map_X, Polynomial.mapEquiv_apply, Polynomial.map_X]
  rfl

/-- An idempotent of a lifted cusp factor reducing to `0` is `0`. -/
lemma cuspEquiv_idem_eq_zero [IsNoetherianRing R] {n : ℕ} (hJ : J θ (R := R) ^ n = ⊥)
    {δ t : FormalPatchLevel.Hat f} {δb : Admissible.Hat (fbar θ f)} {hδ : ψ θ f δ = δb}
    {ht : ψ θ f t = ψc X} {e : ℕ} {a : CPiece f δ t e} (ha : IsIdempotentElem a)
    (h : cuspEquiv θ f ψc δ t δb hδ ht e (Ideal.Quotient.mk _ a) = 0) : a = 0 := by
  have h1 : a ∈ JC θ f δ t e := Ideal.Quotient.eq_zero_iff_mem.mp
    ((map_eq_zero_iff _ (cuspEquiv θ f ψc δ t δb hδ ht e).injective).mp h)
  exact ha.eq_zero_of_isNilpotent ⟨n, CuspHom.pow_eq_zero_of_mem_map _ hJ h1⟩

variable {κ : Type} [Fintype κ] (cidem : κ → Admissible.Hat (fbar θ f)) (ce : κ → ℕ)
  (δ : κ → FormalPatchLevel.Hat f) (hδ : ∀ i, ψ θ f (δ i) = cidem i)
  (t : FormalPatchLevel.Hat f) (ht : ψ θ f t = ψc X)

/-- The reduction `∏_i CPiece_i → ∏_i CuspPiece_i` (componentwise `cuspEquiv`). -/
def redPi [IsNoetherianRing R] :
    (∀ i, CPiece f (δ i) t (ce i)) →+* ∀ i, Admissible.CuspPiece ψc (cidem i) (ce i) :=
  RingHom.pi fun i ↦ (cuspEquiv θ f ψc (δ i) t (cidem i) (hδ i) ht (ce i)).toRingHom.comp
    ((Ideal.Quotient.mk _).comp (Pi.evalRingHom _ i))

variable [IsNoetherianRing R]

omit [Fintype κ] in
lemma redPi_apply (z : ∀ i, CPiece f (δ i) t (ce i)) (i : κ) :
    redPi θ f ψc cidem ce δ hδ t ht z i =
      cuspEquiv θ f ψc (δ i) t (cidem i) (hδ i) ht (ce i) (Ideal.Quotient.mk _ (z i)) := rfl

omit [Fintype κ] in
lemma surjective_redPi : Function.Surjective (redPi θ f ψc cidem ce δ hδ t ht) := fun y ↦ by
  choose a ha using fun i ↦
    (cuspEquiv θ f ψc (δ i) t (cidem i) (hδ i) ht (ce i)).surjective (y i)
  choose b hb using fun i ↦ Ideal.Quotient.mk_surjective (a i)
  exact ⟨b, funext fun i ↦ by rw [redPi_apply, hb, ha]⟩

omit [Fintype κ] in
lemma nil_redPi {n : ℕ} (hJ : J θ (R := R) ^ n = ⊥) :
    ∀ x ∈ RingHom.ker (redPi θ f ψc cidem ce δ hδ t ht), IsNilpotent x := fun x hx ↦ by
  have h : ∀ i, x i ^ n = 0 := fun i ↦ by
    have h1 : cuspEquiv θ f ψc (δ i) t (cidem i) (hδ i) ht (ce i)
        (Ideal.Quotient.mk _ (x i)) = 0 := congrFun (RingHom.mem_ker.mp hx) i
    exact CuspHom.pow_eq_zero_of_mem_map _ hJ (Ideal.Quotient.eq_zero_iff_mem.mp
      ((map_eq_zero_iff _ (RingEquiv.injective _)).mp h1))
  exact ⟨n, funext fun i ↦ (Pi.pow_apply x n i).trans (h i)⟩

omit [Fintype κ] in
lemma redPi_single [DecidableEq κ] (i : κ) (a : CPiece f (δ i) t (ce i)) :
    redPi θ f ψc cidem ce δ hδ t ht (Pi.single i a) =
      Pi.single i (cuspEquiv θ f ψc (δ i) t (cidem i) (hδ i) ht (ce i)
        (Ideal.Quotient.mk _ a)) := by
  funext j
  by_cases hji : j = i
  · subst hji
    rw [redPi_apply, Pi.single_eq_same, Pi.single_eq_same]
  · rw [redPi_apply, Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hji, map_zero, map_zero]

omit [Fintype κ] in
lemma redPi_algebraMap (a : FormalPatchLevel.Hat f) :
    redPi θ f ψc cidem ce δ hδ t ht (algebraMap _ _ a) =
      algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f a) :=
  funext fun i ↦ cuspEquiv_algebraMap θ f ψc (δ i) t (cidem i) (hδ i) ht (ce i) a

end Red

/-! ### The Kummer normal form of `Φ(X_i)` at the special fibre -/

section Special

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  {κ κ' : Type} [DecidableEq κ]
  {cidem : κ → Admissible.Hat (fbar θ f)} {ce : κ → ℕ}
  {cidem' : κ' → Admissible.Hat (fbar θ f)} {ce' : κ' → ℕ}
  (Φ : (∀ i, Admissible.CuspPiece ψc (cidem i) (ce i)) →ₐ[Admissible.Hat (fbar θ f)]
    ∀ i', Admissible.CuspPiece ψc (cidem' i') (ce' i'))

lemma isIdempotentElem_single (i : κ) :
    IsIdempotentElem (Pi.single i 1 : ∀ i, Admissible.CuspPiece ψc (cidem i) (ce i)) := by
  rw [IsIdempotentElem, ← Pi.single_mul, one_mul]

lemma pow_Phi_root (i : κ) (hce : 0 < ce i) :
    Φ (Pi.single i (AdjoinRoot.root _)) ^ ce i =
      Φ (Pi.single i 1) * algebraMap (Admissible.Hat (fbar θ f)) _ (ψc X) := by
  have hx : (Pi.single i (AdjoinRoot.root _) : ∀ i, Admissible.CuspPiece ψc (cidem i) (ce i)) ^
      ce i = Pi.single i 1 * algebraMap (Admissible.Hat (fbar θ f)) _ (ψc X) := by
    rw [CuspHom.single_pow i _ hce, CuspNormalForm.root_pow, ← Pi.single_mul_left, one_mul]
    rfl
  rw [← map_pow, hx, map_mul, AlgHom.commutes]

lemma Phi_root_mul_one (i : κ) :
    Φ (Pi.single i (AdjoinRoot.root _)) * Φ (Pi.single i 1) =
      Φ (Pi.single i (AdjoinRoot.root _)) := by
  rw [← map_mul, ← Pi.single_mul, mul_one]

/-- **The Kummer normal form of `Φ(X_i)`**: on each target factor `Φ(X_i) = X'^{e'/e_i} u` with
`u^{e_i} = Φ(1_i)`, and `e_i ∣ e'` where `Φ(1_i)` does not vanish. -/
lemma special_nf (hce' : ∀ i', 0 < ce' i')
    (hnf : ∀ i', CuspHom.NFHyp (Admissible.Hat (fbar θ f) ⧸ Ideal.span {1 - cidem' i'})
      (Ideal.Quotient.mk _ (ψc X)))
    (i : κ) (hce : 0 < ce i) :
    ∃ u : ∀ i', Admissible.CuspPiece ψc (cidem' i') (ce' i'),
      Φ (Pi.single i (AdjoinRoot.root _)) =
        (fun i' ↦ AdjoinRoot.root _ ^ (ce' i' / ce i)) * u ∧
      u ^ ce i = Φ (Pi.single i 1) ∧ ∀ i', Φ (Pi.single i 1) i' ≠ 0 → ce i ∣ ce' i' := by
  have hE : IsIdempotentElem (Φ (Pi.single i 1)) := (isIdempotentElem_single i).map Φ
  have hpow := pow_Phi_root Φ i hce
  have h := fun i' ↦ CuspNormalForm.exists_normalForm
    (CuspNormalForm.isSMulRegular_root _ (hce' i') (hnf i').1)
    (CuspNormalForm.isReduced_quot_root _ (hce' i') (hnf i').2.1)
    (CuspNormalForm.separated_root _ (hce' i') (hnf i').2.2) hce
    (E := Φ (Pi.single i 1) i') (congrFun hE i') (y := Φ (Pi.single i (AdjoinRoot.root _)) i')
    (calc Φ (Pi.single i (AdjoinRoot.root _)) i' ^ ce i
          = (Φ (Pi.single i (AdjoinRoot.root _)) ^ ce i) i' := (Pi.pow_apply _ _ _).symm
        _ = Φ (Pi.single i 1) i' * AdjoinRoot.of _ (Ideal.Quotient.mk _ (ψc X)) :=
          congrFun hpow i'
        _ = AdjoinRoot.root _ ^ ce' i' * Φ (Pi.single i 1) i' := by
          rw [← CuspNormalForm.root_pow, mul_comm])
  choose u hu1 hu2 hu3 using h
  exact ⟨u, funext hu1, funext hu2, hu3⟩

end Special

/-! ### Lifting maps of products of cusp factors -/

section Lift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)} [IsNoetherianRing R]
  {κ κ' : Type} [DecidableEq κ]
  {cidem : κ → Admissible.Hat (fbar θ f)} {ce : κ → ℕ} {δ : κ → FormalPatchLevel.Hat f}
  {t : FormalPatchLevel.Hat f}
  {cidem' : κ' → Admissible.Hat (fbar θ f)} {ce' : κ' → ℕ}
  {δ' : κ' → FormalPatchLevel.Hat f} (hδ' : ∀ i', ψ θ f (δ' i') = cidem' i')
  (Φ : (∀ i, Admissible.CuspPiece ψc (cidem i) (ce i)) →ₐ[Admissible.Hat (fbar θ f)]
    ∀ i', Admissible.CuspPiece ψc (cidem' i') (ce' i'))
  {n : ℕ} (hJ : J θ (R := R) ^ n = ⊥)

include hJ in
/-- The idempotents `Φ(1_i)` lift to complete orthogonal idempotents. -/
lemma exists_idem [Fintype κ] (ht : ψ θ f t = ψc X) :
    ∃ Et : κ → ∀ i', CPiece f (δ' i') t (ce' i'), CompleteOrthogonalIdempotents Et ∧
      ∀ i, redPi θ f ψc cidem' ce' δ' hδ' t ht (Et i) = Φ (Pi.single i 1) := by
  obtain ⟨Et, hEt, hEtρ⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (redPi θ f ψc cidem' ce' δ' hδ' t ht) (nil_redPi θ f ψc cidem' ce' δ' hδ' t ht hJ)
    ((CompleteOrthogonalIdempotents.single _).map Φ.toRingHom)
    fun i ↦ RingHom.mem_range.mpr (surjective_redPi θ f ψc cidem' ce' δ' hδ' t ht _)
  exact ⟨Et, hEt, fun i ↦ congrFun hEtρ i⟩

include hJ in
/-- The lifted idempotent `Ẽ_i` lies over the part selected by `δ̃_i`. -/
lemma one_sub_mul_idem (hδ : ∀ i, ψ θ f (δ i) = cidem i) (ht : ψ θ f t = ψc X)
    (hδidem : ∀ i, IsIdempotentElem (δ i)) {Et : κ → ∀ i', CPiece f (δ' i') t (ce' i')}
    (hEt : ∀ i, IsIdempotentElem (Et i))
    (hEti : ∀ i, redPi θ f ψc cidem' ce' δ' hδ' t ht (Et i) = Φ (Pi.single i 1)) (i : κ) :
    algebraMap (FormalPatchLevel.Hat f) (∀ i', CPiece f (δ' i') t (ce' i')) (1 - δ i) * Et i =
      0 := by
  let ρ := redPi θ f ψc cidem' ce' δ' hδ' t ht
  refine CuspHom.idem_eq_zero ρ (nil_redPi θ f ψc cidem' ce' δ' hδ' t ht hJ)
    (((hδidem i).one_sub.map (algebraMap _ _)).mul (hEt i)) ?_
  have h0 : algebraMap (Admissible.Hat (fbar θ f)) (∀ i, Admissible.CuspPiece ψc (cidem i) (ce i))
      (ψ θ f (1 - δ i)) * Pi.single i 1 = 0 := by
    funext j
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases hji : j = i
    · subst hji
      rw [Pi.single_eq_same, mul_one, map_sub, map_one, hδ j]
      change AdjoinRoot.of _ (Ideal.Quotient.mk _ (1 - cidem j)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
    · rw [Pi.single_eq_of_ne hji, mul_zero]
  calc ρ (algebraMap _ _ (1 - δ i) * Et i)
      = algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f (1 - δ i)) * Φ (Pi.single i 1) :=
        (map_mul ρ _ _).trans (congrArg₂ (· * ·)
          (redPi_algebraMap θ f ψc cidem' ce' δ' hδ' t ht (1 - δ i)) (hEti i))
    _ = Φ (algebraMap _ _ (ψ θ f (1 - δ i)) * Pi.single i 1) :=
        ((map_mul Φ _ _).trans (congrArg (· * Φ (Pi.single i 1)) (Φ.commutes _))).symm
    _ = 0 := (congrArg Φ h0).trans (map_zero Φ)

include hJ in
/-- **The lifted root**: an element `ỹ` with `ỹ^{e_i} Ẽ_i = t̃ Ẽ_i` and `Ẽ_i ỹ` reducing to
`Φ(X_i)`, namely `X̃'^{e'/e_i} ṽ` for a lift `ṽ` of the root of unity `u E_i + (1 − E_i)`. -/
lemma exists_root_lift (ht : ψ θ f t = ψc X) (hce' : ∀ i', 0 < ce' i')
    (hnf : ∀ i', CuspHom.NFHyp (Admissible.Hat (fbar θ f) ⧸ Ideal.span {1 - cidem' i'})
      (Ideal.Quotient.mk _ (ψc X)))
    {i : κ} (hce : 0 < ce i) (hce0 : (ce i : k) ≠ 0) {Et : ∀ i', CPiece f (δ' i') t (ce' i')}
    (hEt : IsIdempotentElem Et)
    (hEti : redPi θ f ψc cidem' ce' δ' hδ' t ht Et = Φ (Pi.single i 1)) :
    ∃ y : ∀ i', CPiece f (δ' i') t (ce' i'),
      y ^ ce i * Et = algebraMap (FormalPatchLevel.Hat f) _ t * Et ∧
      redPi θ f ψc cidem' ce' δ' hδ' t ht (Et * y) = Φ (Pi.single i (AdjoinRoot.root _)) := by
  let ρ := redPi θ f ψc cidem' ce' δ' hδ' t ht
  have hρs := surjective_redPi θ f ψc cidem' ce' δ' hδ' t ht
  have hρN := nil_redPi θ f ψc cidem' ce' δ' hδ' t ht hJ
  have hE : IsIdempotentElem (Φ (Pi.single i 1)) := (isIdempotentElem_single i).map Φ
  obtain ⟨u, hu1, hu2, hu3⟩ := special_nf Φ hce' hnf i hce
  obtain ⟨w, hw⟩ := hρs (u * Φ (Pi.single i 1) + (1 - Φ (Pi.single i 1)))
  have hT : IsUnit ((ce i : ℕ) : ∀ i', Admissible.CuspPiece ψc (cidem' i') (ce' i')) := by
    have h1 := (isUnit_iff_ne_zero.mpr hce0).map
      (algebraMap k (∀ i', Admissible.CuspPiece ψc (cidem' i') (ce' i')))
    rwa [map_natCast] at h1
  have hS : IsUnit ((ce i : ℕ) : ∀ i', CPiece f (δ' i') t (ce' i')) :=
    CuspHom.isUnit_of_map ρ hρN hρs (by rw [map_natCast]; exact hT)
  have hw1 : w ^ ce i - 1 ∈ RingHom.ker ρ := RingHom.mem_ker.mpr <|
    calc ρ (w ^ ce i - 1) = ρ w ^ ce i - 1 := by rw [map_sub, map_pow, map_one]
      _ = 0 := by rw [hw, CuspHom.pow_corner_add hE.eq hce hu2, sub_self]
  obtain ⟨v, hv1, hv2⟩ := CuspNormalForm.exists_pow_eq_one_lift hρN hce hS w hw1
  have hvρ : ρ v = ρ w := by
    have h1 := RingHom.mem_ker.mp hv1
    rwa [map_sub, sub_eq_zero] at h1
  let D : ∀ i', CPiece f (δ' i') t (ce' i') := fun i' ↦
    AdjoinRoot.root (cpoly f (δ' i') t (ce' i')) ^ (ce' i' / ce i)
  let Db : ∀ i', Admissible.CuspPiece ψc (cidem' i') (ce' i') := fun i' ↦
    AdjoinRoot.root _ ^ (ce' i' / ce i)
  have hu1' : Φ (Pi.single i (AdjoinRoot.root _)) = Db * u := hu1
  have hD : ρ D = Db := funext fun i' ↦ by
    change cuspEquiv θ f ψc (δ' i') t (cidem' i') (hδ' i') ht (ce' i')
      (Ideal.Quotient.mk _ (AdjoinRoot.root (cpoly f (δ' i') t (ce' i')) ^ (ce' i' / ce i))) = _
    rw [map_pow, map_pow, cuspEquiv_root]
  refine ⟨D * v, ?_, ?_⟩
  · rw [mul_pow, hv2, mul_one]
    funext i'
    rw [Pi.mul_apply, Pi.mul_apply, Pi.pow_apply]
    by_cases hd : ce i ∣ ce' i'
    · congr 1
      change (AdjoinRoot.root (cpoly f (δ' i') t (ce' i')) ^ (ce' i' / ce i)) ^ ce i =
        AdjoinRoot.of _ (Ideal.Quotient.mk _ t)
      rw [← pow_mul, Nat.div_mul_cancel hd, CuspNormalForm.root_pow]
    · have hE0 : Φ (Pi.single i 1) i' = 0 := by_contra fun h ↦ hd (hu3 i' h)
      have hEt0 : Et i' = 0 := cuspEquiv_idem_eq_zero θ f ψc hJ (ht := ht) (congrFun hEt i')
        ((congrFun hEti i').trans hE0)
      rw [hEt0, mul_zero, mul_zero]
  · have hyE := Phi_root_mul_one Φ i
    calc ρ (Et * (D * v)) = ρ Et * (ρ D * ρ v) :=
          (map_mul ρ _ _).trans (congrArg (ρ Et * ·) (map_mul ρ _ _))
      _ = Φ (Pi.single i 1) * (Db * (u * Φ (Pi.single i 1) + (1 - Φ (Pi.single i 1)))) :=
          congrArg₂ (· * ·) hEti (congrArg₂ (· * ·) hD (hvρ.trans hw))
      _ = Φ (Pi.single i (AdjoinRoot.root _)) := by
          linear_combination (Db * u - Db) * hE.eq - Φ (Pi.single i 1) * hu1' + hyE

/-- **The constructed map reduces to `Φ`.** -/
lemma redPi_pieceMap [Fintype κ] (hδ : ∀ i, ψ θ f (δ i) = cidem i) (ht : ψ θ f t = ψc X)
    {Et : κ → ∀ i', CPiece f (δ' i') t (ce' i')} (hEt : CompleteOrthogonalIdempotents Et)
    {y : κ → ∀ i', CPiece f (δ' i') t (ce' i')}
    (hδS : ∀ i, algebraMap (FormalPatchLevel.Hat f) _ (1 - δ i) * Et i = 0)
    (hyS : ∀ i, y i ^ ce i * Et i = algebraMap (FormalPatchLevel.Hat f) _ t * Et i)
    (hEti : ∀ i, redPi θ f ψc cidem' ce' δ' hδ' t ht (Et i) = Φ (Pi.single i 1))
    (hroot : ∀ i, redPi θ f ψc cidem' ce' δ' hδ' t ht (Et i * y i) =
      Φ (Pi.single i (AdjoinRoot.root _)))
    (z : ∀ i, CPiece f (δ i) t (ce i)) :
    redPi θ f ψc cidem' ce' δ' hδ' t ht (CuspHom.pieceMap hδS hyS hEt z) =
      Φ (redPi θ f ψc cidem ce δ hδ t ht z) := by
  let ρ := redPi θ f ψc cidem' ce' δ' hδ' t ht
  let ρ₀ := redPi θ f ψc cidem ce δ hδ t ht
  let G := CuspHom.pieceMap hδS hyS hEt
  have hcomp : ∀ i (a : CPiece f (δ i) t (ce i)),
      (ρ.comp G.toRingHom) (Pi.single i a) = (Φ.toRingHom.comp ρ₀) (Pi.single i a) :=
    fun i a ↦ by
    refine CuspHom.adjoinRoot_ext (fun a ↦ (ρ.comp G.toRingHom) (Pi.single i a))
      (fun a ↦ (Φ.toRingHom.comp ρ₀) (Pi.single i a))
      (CuspHom.single_map_add (ρ.comp G.toRingHom) i)
      (CuspHom.single_map_add (Φ.toRingHom.comp ρ₀) i)
      (CuspHom.single_map_mul (ρ.comp G.toRingHom) i)
      (CuspHom.single_map_mul (Φ.toRingHom.comp ρ₀) i)
      (fun c ↦ ?_) ?_ a
    · obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective c
      have hs : (Pi.single i (AdjoinRoot.of _ (Ideal.Quotient.mk _ h)) :
          ∀ i, CPiece f (δ i) t (ce i)) = Pi.single i 1 * algebraMap _ _ h := by
        rw [← Pi.single_mul_left, one_mul]
        rfl
      have h1 : ρ₀ (Pi.single i 1) = Pi.single i 1 :=
        (redPi_single θ f ψc cidem ce δ hδ t ht i 1).trans (by rw [map_one, map_one])
      change ρ (G (Pi.single i _)) = Φ (ρ₀ (Pi.single i _))
      rw [hs]
      calc ρ (G (Pi.single i 1 * algebraMap _ _ h))
          = ρ (Et i * algebraMap _ _ h) := congrArg ρ ((map_mul G _ _).trans
            (congrArg₂ (· * ·) (CuspHom.pieceMap_single_one hδS hyS hEt i) (G.commutes h)))
        _ = ρ (Et i) * ρ (algebraMap _ _ h) := map_mul ρ _ _
        _ = Φ (Pi.single i 1) * algebraMap _ _ (ψ θ f h) := congrArg₂ (· * ·) (hEti i)
            (redPi_algebraMap θ f ψc cidem' ce' δ' hδ' t ht h)
        _ = Φ (Pi.single i 1 * algebraMap _ _ (ψ θ f h)) :=
            ((map_mul Φ _ _).trans (congrArg (Φ (Pi.single i 1) * ·) (Φ.commutes _))).symm
        _ = Φ (ρ₀ (Pi.single i 1 * algebraMap _ _ h)) := congrArg Φ
            (((map_mul ρ₀ _ _).trans (congrArg₂ (· * ·) h1
              (redPi_algebraMap θ f ψc cidem ce δ hδ t ht h))).symm)
    · change ρ (G (Pi.single i _)) = Φ (ρ₀ (Pi.single i _))
      calc ρ (G (Pi.single i (AdjoinRoot.root _))) = ρ (Et i * y i) :=
            congrArg ρ (CuspHom.pieceMap_single_root hδS hyS hEt i)
        _ = Φ (Pi.single i (AdjoinRoot.root _)) := hroot i
        _ = Φ (ρ₀ (Pi.single i (AdjoinRoot.root _))) := congrArg Φ
            ((redPi_single θ f ψc cidem ce δ hδ t ht i _).trans (congrArg (Pi.single i)
              (cuspEquiv_root θ f ψc (δ i) t (cidem i) (hδ i) ht (ce i)))).symm
  exact CuspHom.pi_ringHom_ext (ρ.comp G.toRingHom) (Φ.toRingHom.comp ρ₀) hcomp z

omit [DecidableEq κ] in
include hJ in
/-- **Maps of products of cusp factors lift to the levels.** A map `Φ` of `R̂'`-algebras
`∏_i CuspPiece_i → ∏_{i'} CuspPiece'_{i'}` at the special fibre lifts to a map of `R̂`-algebras
`∏_i CPiece_i → ∏_{i'} CPiece'_{i'}` (the lifted cusp factors over the same `t̃`, with idempotent
`δ̃_i`), if `J` is nilpotent, the indices `e_i` are invertible in `k`, and the target bases satisfy
the hypotheses of the Kummer normal form. -/
theorem exists_cuspPiMap [Finite κ] (hδ : ∀ i, ψ θ f (δ i) = cidem i) (ht : ψ θ f t = ψc X)
    {t' : FormalPatchLevel.Hat f} (ht' : ψ θ f t' = ψc X) (htt : t' = t)
    (hce : ∀ i, 0 < ce i) (hce0 : ∀ i, (ce i : k) ≠ 0) (hce' : ∀ i', 0 < ce' i')
    (hδidem : ∀ i, IsIdempotentElem (δ i))
    (hnf : ∀ i', CuspHom.NFHyp (Admissible.Hat (fbar θ f) ⧸ Ideal.span {1 - cidem' i'})
      (Ideal.Quotient.mk _ (ψc X))) :
    ∃ G : (∀ i, CPiece f (δ i) t (ce i)) →ₐ[FormalPatchLevel.Hat f]
        ∀ i', CPiece f (δ' i') t' (ce' i'),
      ∀ z, redPi θ f ψc cidem' ce' δ' hδ' t' ht' (G z) =
        Φ (redPi θ f ψc cidem ce δ hδ t ht z) := by
  classical
  cases nonempty_fintype κ
  subst htt
  obtain ⟨Et, hEt, hEti⟩ := exists_idem hδ' Φ hJ ht'
  choose y hy1 hy2 using fun i ↦
    exists_root_lift hδ' Φ hJ ht' hce' hnf (hce i) (hce0 i) (hEt.idem i) (hEti i)
  have hδS := one_sub_mul_idem hδ' Φ hJ hδ ht' hδidem hEt.idem hEti
  exact ⟨CuspHom.pieceMap hδS hy1 hEt, redPi_pieceMap hδ' Φ hδ ht' hEt hδS hy1 hEti hy2⟩

end Lift

/-! ### The lifted formal models `NFall` -/

namespace CuspHom

section Sum

variable {A : Type*} [CommRing A] {ι κ : Type} {P : ι ⊕ κ → Type*} [∀ s, CommRing (P s)]
  [∀ s, Algebra A (P s)]

variable (A P) in
/-- The projection `∏_{ι ⊕ κ} P_s → ∏_κ P_{inr i}`. -/
def toInr : (∀ s, P s) →ₐ[A] ∀ i, P (.inr i) := AlgHom.pi fun i ↦ Pi.evalAlgHom A P (.inr i)

/-- `∏_κ P_{inr i} → ∏_{ι ⊕ κ} P_s` for empty `ι`. -/
def ofInrFun [IsEmpty ι] (z : ∀ i, P (.inr i)) : ∀ s, P s
  | .inl j => isEmptyElim j
  | .inr i => z i

variable (A P) in
/-- `∏_κ P_{inr i} ≅ ∏_{ι ⊕ κ} P_s` for empty `ι`, as an algebra map. -/
def ofInr [IsEmpty ι] : (∀ i, P (.inr i)) →ₐ[A] ∀ s, P s where
  toFun := ofInrFun
  map_one' := funext fun s ↦ match s with
    | .inl j => isEmptyElim j
    | .inr _ => rfl
  map_mul' _ _ := funext fun s ↦ match s with
    | .inl j => isEmptyElim j
    | .inr _ => rfl
  map_zero' := funext fun s ↦ match s with
    | .inl j => isEmptyElim j
    | .inr _ => rfl
  map_add' _ _ := funext fun s ↦ match s with
    | .inl j => isEmptyElim j
    | .inr _ => rfl
  commutes' _ := funext fun s ↦ match s with
    | .inl j => isEmptyElim j
    | .inr _ => rfl

lemma ofInr_inr [IsEmpty ι] (z : ∀ i, P (.inr i)) (i : κ) : ofInr A P z (.inr i) = z i := rfl

end Sum

end CuspHom

section NF

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ φ' : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  {cov : Admissible.Covering φ ψc} {cov' : Admissible.Covering φ' ψc}
  {πL : cov.ι → O} {πL' : cov'.ι → O}
  (L : KummerLift cov πL) (M : CuspLift cov) (L' : KummerLift cov' πL') (M' : CuspLift cov')

/-- The cusp components of the reduction `κ3F` are `redPi`. -/
lemma kappa3F_snd [IsNoetherianRing R] (hθ : Function.Surjective θ) (x : NFall L M) :
    (kappa3F L M hθ (Ideal.Quotient.mk _ x)).2 =
      redPi θ f ψc cov.cidem cov.ce M.δ M.hδ M.t M.ht
        (CuspHom.toInr (FormalPatchLevel.Hat f) (NF L M) x) := rfl

/-- **Maps of formal cusp models lift to the levels.** For two admissible coverings `cov`, `cov'`
of the same chart, `cov'` without Kummer factors at the nodes, lift data `M`, `M'` of their cusp
factors over the same lift `t̃` of the coordinate at the marked points (with idempotent `δ̃_i`),
`J` nilpotent, and target bases `R̂'/(1 − δ_{i'})` satisfying the hypotheses of the Kummer normal
form, every map `Φ` of the formal cusp models at the special fibre lifts to a map
`g : NFall L M → NFall L' M'` of `R̂`-algebras whose reduction is `Φ` on the cusp components. -/
theorem exists_cuspNFMap [IsNoetherianRing R] (hθ : Function.Surjective θ) {n : ℕ}
    (hJ : J θ (R := R) ^ n = ⊥) [IsEmpty cov'.ι] (hMt : M'.t = M.t)
    (hcidem : ∀ i, IsIdempotentElem (M.δ i))
    (hnf : ∀ i', CuspHom.NFHyp (Admissible.Hat (fbar θ f) ⧸ Ideal.span {1 - cov'.cidem i'})
      (Ideal.Quotient.mk _ (ψc X)))
    (Φ : (∀ i, Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i)) →ₐ[Admissible.Hat (fbar θ f)]
      ∀ i', Admissible.CuspPiece ψc (cov'.cidem i') (cov'.ce i')) :
    ∃ g : NFall L M →ₐ[FormalPatchLevel.Hat f] NFall L' M', ∀ x,
      (kappa3F L' M' hθ (Ideal.Quotient.mk _ (g x))).2 =
        Φ (kappa3F L M hθ (Ideal.Quotient.mk _ x)).2 := by
  obtain ⟨G, hG⟩ := exists_cuspPiMap M'.hδ Φ hJ M.hδ M.ht M'.ht hMt cov.ce_pos cov.ce_ne_zero
    cov'.ce_pos hcidem hnf
  refine ⟨(CuspHom.ofInr (FormalPatchLevel.Hat f) (NF L' M')).comp
    (G.comp (CuspHom.toInr (FormalPatchLevel.Hat f) (NF L M))), fun x ↦ ?_⟩
  exact (hG (CuspHom.toInr (FormalPatchLevel.Hat f) (NF L M) x)).trans
    (congrArg Φ (kappa3F_snd L M hθ x).symm)

end NF

end

end AdmissibleLift

end SemistableReduction
