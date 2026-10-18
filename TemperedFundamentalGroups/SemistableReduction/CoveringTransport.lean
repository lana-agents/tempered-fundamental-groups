/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.RingHom.Etale
import TemperedFundamentalGroups.SemistableReduction.AdmissibleCovering
import TemperedFundamentalGroups.SemistableReduction.CompletionMap

/-!
# Transport of admissible coverings along isomorphisms of charts (Blueprint §12.8, M2.3)

The special fibres `R_n/J_n` of the level-`n` charts of the model are different, isomorphic,
`k`-algebras. One admissible covering of the special fibre (`Admissible.Covering`) is patched at
every level; for this it is transported along the isomorphisms of special fibres.

**`Admissible.Covering.transport cov`**: for a `k`-algebra isomorphism `e : R₁ ≃ R₂` of charts,
`h : e f = f₂` (so that the target can be named independently of `e`) and an admissible
covering `cov` of `(R₁, f, φ, ψ)`, an admissible covering of `(R₂, f₂, Ê ∘ φ, Ê ∘ ψ)`,
`Ê : R̂₁ ≃ R̂₂` the induced isomorphism of completions
(`Admissible.hatEquiv`, from `CompletionMap.equiv`): the same algebra `C` (an `R₂`-algebra through
`e⁻¹`), the transported idempotents and the same ramification indices; the formal Kummer
isomorphism is transported through `R̂₂ ⊗_{R₂} C ≃ R̂₁ ⊗_{R₁} C` (`tensorEquiv`) and the
isomorphisms of the Kummer and cusp factors (`pieceEquiv`, `cuspEquiv`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace Admissible

noncomputable section

variable {k : Type u} [Field k] {R₁ : Type u} [CommRing R₁] [Algebra k R₁]
  {R₂ : Type u} [CommRing R₂] [Algebra k R₂] (e : R₁ ≃ₐ[k] R₂) {f : R₁} {f₂ : R₂}
  (h : e f = f₂)

include h in
lemma map_span_e :
    (Ideal.span {f}).map ((e.toRingEquiv : R₁ ≃+* R₂) : R₁ →+* R₂) = Ideal.span {f₂} := by
  rw [Ideal.map_span, Set.image_singleton, ← h]
  rfl

/-- The isomorphism `R̂₁ ≃ R̂₂` of the completions along `f` and `e f`. -/
def hatEquiv : Hat f ≃ₐ[k] Hat f₂ :=
  AlgEquiv.ofRingEquiv (f := CompletionMap.equiv e.toRingEquiv (map_span_e e h)) fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k R₁ (Hat f),
      CompletionMap.equiv_algebraMap e.toRingEquiv (map_span_e e h),
      IsScalarTower.algebraMap_apply k R₂ (Hat f₂)]
    congr 1
    exact e.commutes c

lemma hatEquiv_algebraMap (r : R₁) :
    hatEquiv e h (algebraMap R₁ (Hat f) r) = algebraMap R₂ (Hat f₂) (e r) :=
  CompletionMap.equiv_algebraMap e.toRingEquiv (map_span_e e h) r

/-! ### The factors -/

variable {e h}

/-- The isomorphism of the bases of Kummer factors. -/
def baseEquiv (ε : Hat f) :
    (Hat f ⧸ Ideal.span {1 - ε}) ≃+* (Hat f₂ ⧸ Ideal.span {1 - hatEquiv e h ε}) :=
  Ideal.quotientEquiv _ _ (hatEquiv e h).toRingEquiv (by
    rw [Ideal.map_span, Set.image_singleton]
    simp)

lemma baseEquiv_mk (ε x : Hat f) :
    baseEquiv (h := h) ε (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (hatEquiv e h x) :=
  Ideal.quotientEquiv_mk _ _ _ _ _

variable (φ : Node k (0 : k) →ₐ[k] Hat f) (ψ : Polynomial k →ₐ[k] Hat f)

/-- The transported node coordinates `Ê ∘ φ`. -/
abbrev φT : Node k (0 : k) →ₐ[k] Hat f₂ := (hatEquiv e h).toAlgHom.comp φ

/-- The transported coordinate `Ê ∘ ψ` at the marked points. -/
abbrev ψT : Polynomial k →ₐ[k] Hat f₂ := (hatEquiv e h).toAlgHom.comp ψ

/-- The isomorphism of the bases of Kummer factors, over the node ring. -/
def pieceBaseEquiv (ε : Hat f) {n : ℕ} (hn : 0 < n) :
    PieceBase φ ε hn ≃ₐ[KummerEtale.A (0 : k) n] PieceBase (φT (h := h) φ) (hatEquiv e h ε) hn :=
  AlgEquiv.ofRingEquiv (f := baseEquiv ε) fun a ↦ by
    change baseEquiv ε (Ideal.Quotient.mk _ (φ _)) = Ideal.Quotient.mk _ (hatEquiv e h (φ _))
    exact baseEquiv_mk ε _

/-- **The isomorphism of Kummer factors.** -/
def kummerPieceEquiv (ε : Hat f) {n : ℕ} (hn : 0 < n) :
    KummerPiece φ ε hn ≃+* KummerPiece (φT (h := h) φ) (hatEquiv e h ε) hn :=
  (Algebra.TensorProduct.congr (R := KummerEtale.A (0 : k) n) (A := PieceBase φ ε hn)
    (C := PieceBase (φT (h := h) φ) (hatEquiv e h ε) hn) (B := KummerEtale.B (0 : k))
    (D := KummerEtale.B (0 : k)) (pieceBaseEquiv (h := h) φ ε hn) AlgEquiv.refl).toRingEquiv

lemma kummerPieceEquiv_algebraMap (ε : Hat f) {n : ℕ} (hn : 0 < n) (x : Hat f) :
    kummerPieceEquiv (h := h) φ ε hn (algebraMap (Hat f) (KummerPiece φ ε hn) x) =
      algebraMap (Hat f₂) (KummerPiece (φT (h := h) φ) (hatEquiv e h ε) hn)
        (hatEquiv e h x) := by
  change kummerPieceEquiv (h := h) φ ε hn
      (algebraMap (Hat f) (PieceBase φ ε hn) x ⊗ₜ[KummerEtale.A (0 : k) n]
        (1 : KummerEtale.B (0 : k))) =
    algebraMap (Hat f₂) (PieceBase (φT (h := h) φ) (hatEquiv e h ε) hn) (hatEquiv e h x)
      ⊗ₜ[KummerEtale.A (0 : k) n] (1 : KummerEtale.B (0 : k))
  rw [kummerPieceEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

lemma map_cuspPoly (δ : Hat f) (n : ℕ) :
    Polynomial.mapEquiv (baseEquiv (h := h) δ)
        (Polynomial.X ^ n -
          Polynomial.C (Ideal.Quotient.mk (Ideal.span {1 - δ}) (ψ Polynomial.X))) =
      Polynomial.X ^ n - Polynomial.C (Ideal.Quotient.mk (Ideal.span {1 - hatEquiv e h δ})
        (ψT (h := h) ψ Polynomial.X)) := by
  simp only [Polynomial.mapEquiv_apply, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, RingHom.coe_coe, baseEquiv_mk]
  rfl

/-- **The isomorphism of cusp factors.** -/
def cuspPieceEquiv (δ : Hat f) (n : ℕ) :
    CuspPiece ψ δ n ≃+* CuspPiece (ψT (h := h) ψ) (hatEquiv e h δ) n :=
  Ideal.quotientEquiv _ _ (Polynomial.mapEquiv (baseEquiv (h := h) δ)) (by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p ↦ Ideal.span {p}) (map_cuspPoly ψ δ n).symm)

lemma cuspPieceEquiv_algebraMap (δ : Hat f) (n : ℕ) (x : Hat f) :
    cuspPieceEquiv (h := h) ψ δ n (algebraMap (Hat f) (CuspPiece ψ δ n) x) =
      algebraMap (Hat f₂) (CuspPiece (ψT (h := h) ψ) (hatEquiv e h δ) n)
        (hatEquiv e h x) := by
  change cuspPieceEquiv (h := h) ψ δ n
      (Ideal.Quotient.mk _ (Polynomial.C (Ideal.Quotient.mk _ x))) =
    Ideal.Quotient.mk _ (Polynomial.C (Ideal.Quotient.mk _ (hatEquiv e h x)))
  rw [cuspPieceEquiv]
  change Ideal.Quotient.mk _ (Polynomial.mapEquiv (baseEquiv (h := h) δ)
    (Polynomial.C (Ideal.Quotient.mk _ x))) = _
  simp only [Polynomial.mapEquiv_apply, Polynomial.map_C, RingHom.coe_coe, baseEquiv_mk]

/-! ### The tensor product -/

variable (e) (C : Type u) [CommRing C] [Algebra R₁ C]

/-- `C` as an `R₂`-algebra, through `e⁻¹`. -/
abbrev algT : Algebra R₂ C := ((algebraMap R₁ C).comp (e.symm : R₂ →+* R₁)).toAlgebra

/-- `R̂₂ ⊗_{R₂} C` as an `R₁`-algebra, through `e`. -/
abbrev algT₂ : letI := algT e C
    Algebra R₁ (Hat f₂ ⊗[R₂] C) :=
  letI := algT e C
  ((algebraMap R₂ (Hat f₂ ⊗[R₂] C)).comp (e : R₁ →+* R₂)).toAlgebra

/-- `R̂₂ ⊗_{R₂} C → R̂₁ ⊗_{R₁} C`... as an `R₁`-algebra map `R̂₁ ⊗_{R₁} C → R̂₂ ⊗_{R₂} C`. -/
def tensorFwd : letI := algT e C; letI := algT₂ (f₂ := f₂) e C
    (Hat f ⊗[R₁] C) →ₐ[R₁] (Hat f₂ ⊗[R₂] C) :=
  letI := algT e C
  letI := algT₂ (f₂ := f₂) e C
  Algebra.TensorProduct.lift
    { (Algebra.TensorProduct.includeLeftRingHom.comp (hatEquiv e h).toRingEquiv.toRingHom) with
      commutes' := fun r ↦ by
        change Algebra.TensorProduct.includeLeftRingHom (hatEquiv e h (algebraMap R₁ _ r)) = _
        rw [hatEquiv_algebraMap]
        change algebraMap R₂ (Hat f₂) (e r) ⊗ₜ[R₂] (1 : C) =
          algebraMap R₂ (Hat f₂ ⊗[R₂] C) (e r)
        rw [Algebra.TensorProduct.algebraMap_apply] }
    { (Algebra.TensorProduct.includeRight (R := R₂) (A := Hat f₂) (B := C)).toRingHom with
      commutes' := fun r ↦ by
        change (1 : Hat f₂) ⊗ₜ[R₂] (algebraMap R₁ C r) =
          algebraMap R₂ (Hat f₂ ⊗[R₂] C) (e r)
        rw [Algebra.TensorProduct.algebraMap_apply']
        change _ = (1 : Hat f₂) ⊗ₜ[R₂] algebraMap R₁ C (e.symm (e r))
        rw [AlgEquiv.symm_apply_apply] }
    fun _ _ ↦ Commute.all _ _

lemma tensorFwd_tmul (x : Hat f) (c : C) :
    letI := algT e C
    tensorFwd (h := h) e C (x ⊗ₜ c) = hatEquiv e h x ⊗ₜ c := by
  letI := algT e C
  simp only [tensorFwd, Algebra.TensorProduct.lift_tmul]
  change (hatEquiv e h x ⊗ₜ[R₂] (1 : C)) * ((1 : Hat f₂) ⊗ₜ c) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- `R̂₁ ⊗_{R₁} C` as an `R₂`-algebra, through `e⁻¹`. -/
abbrev algT₁ : Algebra R₂ (Hat f ⊗[R₁] C) :=
  ((algebraMap R₁ (Hat f ⊗[R₁] C)).comp (e.symm : R₂ →+* R₁)).toAlgebra

/-- The left factor of the inverse map. -/
def bwdLeft : letI := algT₁ (f := f) e C
    Hat f₂ →ₐ[R₂] Hat f ⊗[R₁] C :=
  letI := algT₁ (f := f) e C
  { (Algebra.TensorProduct.includeLeftRingHom.comp
        (hatEquiv e h).symm.toRingEquiv.toRingHom) with
    commutes' := fun r ↦ by
      change Algebra.TensorProduct.includeLeftRingHom
        ((hatEquiv e h).symm (algebraMap R₂ _ r)) = _
      have : (hatEquiv e h).symm (algebraMap R₂ (Hat f₂) r) =
          algebraMap R₁ (Hat f) (e.symm r) := by
        rw [AlgEquiv.symm_apply_eq, hatEquiv_algebraMap, AlgEquiv.apply_symm_apply]
      rw [this]
      rfl }

/-- The right factor of the inverse map. -/
def bwdRight : letI := algT e C; letI := algT₁ (f := f) e C
    C →ₐ[R₂] Hat f ⊗[R₁] C :=
  letI := algT e C
  letI := algT₁ (f := f) e C
  { (Algebra.TensorProduct.includeRight (R := R₁) (A := Hat f) (B := C)).toRingHom with
    commutes' := fun r ↦ by
      change (1 : Hat f) ⊗ₜ[R₁] (algebraMap R₁ C (e.symm r)) =
        algebraMap R₁ (Hat f) (e.symm r) ⊗ₜ[R₁] (1 : C)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Hat f),
        TensorProduct.smul_tmul] }

/-- The inverse map `R̂₂ ⊗_{R₂} C → R̂₁ ⊗_{R₁} C`. -/
def tensorBwd : letI := algT e C
    (Hat f₂ ⊗[R₂] C) →+* (Hat f ⊗[R₁] C) :=
  letI := algT e C
  letI := algT₁ (f := f) e C
  (Algebra.TensorProduct.lift (bwdLeft (h := h) e C) (bwdRight (f := f) e C)
    fun _ _ ↦ Commute.all _ _).toRingHom

lemma tensorBwd_tmul (x : Hat f₂) (c : C) :
    letI := algT e C
    tensorBwd (h := h) e C (x ⊗ₜ c) = (hatEquiv e h).symm x ⊗ₜ c := by
  letI := algT e C
  letI := algT₁ (f := f) e C
  change Algebra.TensorProduct.lift (bwdLeft (h := h) e C) (bwdRight (f := f) e C)
    (fun _ _ ↦ Commute.all _ _) (x ⊗ₜ c) = _
  rw [Algebra.TensorProduct.lift_tmul]
  change ((hatEquiv e h).symm x ⊗ₜ[R₁] (1 : C)) * ((1 : Hat f) ⊗ₜ c) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **`R̂₂ ⊗_{R₂} C ≃ R̂₁ ⊗_{R₁} C`.** -/
def tensorEquiv : letI := algT e C
    (Hat f₂ ⊗[R₂] C) ≃+* (Hat f ⊗[R₁] C) :=
  letI := algT e C
  letI := algT₂ (f₂ := f₂) e C
  RingEquiv.ofRingHom (tensorBwd (h := h) e C) (tensorFwd (h := h) e C).toRingHom
    (RingHom.ext fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        change tensorBwd (h := h) e C (tensorFwd (h := h) e C (x ⊗ₜ c)) = x ⊗ₜ c
        rw [tensorFwd_tmul, tensorBwd_tmul, AlgEquiv.symm_apply_apply]
      | add a b ha hb => rw [map_add, ha, hb, map_add])
    (RingHom.ext fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        change tensorFwd (h := h) e C (tensorBwd (h := h) e C (x ⊗ₜ c)) = x ⊗ₜ c
        rw [tensorBwd_tmul, tensorFwd_tmul, AlgEquiv.apply_symm_apply]
      | add a b ha hb => rw [map_add, ha, hb, map_add])

lemma tensorEquiv_tmul (x : Hat f₂) (c : C) :
    letI := algT e C
    tensorEquiv (h := h) e C (x ⊗ₜ c) = (hatEquiv e h).symm x ⊗ₜ c :=
  tensorBwd_tmul e C x c

lemma tensorEquiv_algebraMap (x : Hat f₂) :
    letI := algT e C
    tensorEquiv (h := h) e C (algebraMap (Hat f₂) (Hat f₂ ⊗[R₂] C) x) =
      algebraMap (Hat f) (Hat f ⊗[R₁] C) ((hatEquiv e h).symm x) := by
  letI := algT e C
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorEquiv_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

/-! ### The transported covering -/

variable {e}

theorem finite_algT [hC : Module.Finite R₁ C] : letI := algT e C; Module.Finite R₂ C := by
  letI := algT e C
  obtain ⟨s, hs⟩ := hC.fg_top
  refine ⟨⟨s, Submodule.eq_top_iff'.mpr fun c ↦ ?_⟩⟩
  have hc : c ∈ Submodule.span R₁ (s : Set C) := hs ▸ Submodule.mem_top
  induction hc using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx =>
    have h : r • x = e r • x := by
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
      change _ = algebraMap R₁ C (e.symm (e r))
      rw [AlgEquiv.symm_apply_apply]
    rw [h]
    exact Submodule.smul_mem _ _ hx

variable (h) in
include h in
theorem etale_algT (hC : (Localization.awayMap (algebraMap R₁ C) f).Etale) :
    letI := algT e C; (Localization.awayMap (algebraMap R₂ C) f₂).Etale := by
  subst h
  letI := algT e C
  have hfC : algebraMap R₂ C (e f) = algebraMap R₁ C f := by
    change algebraMap R₁ C (e.symm (e f)) = _
    rw [AlgEquiv.symm_apply_apply]
  let s₁ : Localization.Away (e f) ≃+* Localization.Away f :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (e f))
      (T := Submonoid.powers f) _ _ e.symm.toRingEquiv (by
        rw [Submonoid.map_powers]
        congr 1
        exact e.symm_apply_apply f)
  let t : Localization.Away (algebraMap R₁ C f) ≃+* Localization.Away (algebraMap R₂ C (e f)) :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (algebraMap R₁ C f))
      (T := Submonoid.powers (algebraMap R₂ C (e f))) _ _ (RingEquiv.refl C) (by
        rw [Submonoid.map_powers, hfC]
        rfl)
  have key : Localization.awayMap (algebraMap R₂ C) (e f) =
      t.toRingHom.comp ((Localization.awayMap (algebraMap R₁ C) f).comp s₁.toRingHom) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (e f)) (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, s₁, t,
      IsLocalization.ringEquivOfRingEquiv_eq, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  rw [key]
  exact RingHom.Etale.respectsIso.1 _ t
    (RingHom.Etale.respectsIso.2 _ s₁ hC)

variable {φ ψ} (cov : Covering φ ψ)

/-- The transported Kummer and cusp factors. -/
def piecesEquiv :
    ((∀ j, KummerPiece φ (cov.idem j) (cov.e_pos j)) × (∀ i, CuspPiece ψ (cov.cidem i) (cov.ce i)))
      ≃+* ((∀ j, KummerPiece (φT (h := h) φ) (hatEquiv e h (cov.idem j)) (cov.e_pos j)) ×
        (∀ i, CuspPiece (ψT (h := h) ψ) (hatEquiv e h (cov.cidem i)) (cov.ce i))) :=
  RingEquiv.prodCongr
    (RingEquiv.piCongrRight fun j ↦ kummerPieceEquiv (h := h) φ (cov.idem j) (cov.e_pos j))
    (RingEquiv.piCongrRight fun i ↦ cuspPieceEquiv (h := h) ψ (cov.cidem i) (cov.ce i))

lemma piecesEquiv_algebraMap (x : Hat f) :
    piecesEquiv (h := h) cov (algebraMap (Hat f) _ x) =
      algebraMap (Hat f₂) _ (hatEquiv e h x) := by
  refine Prod.ext (funext fun j ↦ ?_) (funext fun i ↦ ?_)
  · exact kummerPieceEquiv_algebraMap (h := h) φ (cov.idem j) (cov.e_pos j) x
  · exact cuspPieceEquiv_algebraMap (h := h) ψ (cov.cidem i) (cov.ce i) x

/-- The transported formal Kummer isomorphism. -/
def kummerT : letI := algT e cov.C
    (Hat f₂ ⊗[R₂] cov.C) ≃ₐ[Hat f₂]
      ((∀ j, KummerPiece (φT (h := h) φ) (hatEquiv e h (cov.idem j)) (cov.e_pos j)) ×
        (∀ i, CuspPiece (ψT (h := h) ψ) (hatEquiv e h (cov.cidem i)) (cov.ce i))) :=
  letI := algT e cov.C
  AlgEquiv.ofRingEquiv (f := (tensorEquiv (h := h) e cov.C).trans
      (cov.kummer.toRingEquiv.trans (piecesEquiv (h := h) cov))) fun x ↦ by
    have h1 := tensorEquiv_algebraMap (h := h) e cov.C x
    have h2 := piecesEquiv_algebraMap (h := h) cov ((hatEquiv e h).symm x)
    rw [AlgEquiv.apply_symm_apply] at h2
    rw [RingEquiv.trans_apply, h1, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
    have h3 := cov.kummer.commutes ((hatEquiv e h).symm x)
    exact (congrArg (piecesEquiv (h := h) cov) h3).trans h2

/-- **Transport of an admissible covering** along an isomorphism of charts `e : R₁ ≃ R₂`: the same
algebra `C` (over `R₂` through `e⁻¹`), the idempotents transported by `Ê : R̂₁ ≃ R̂₂`, the same
ramification indices. -/
def Covering.transport : Covering (φT (h := h) φ) (ψT (h := h) ψ) where
  C := cov.C
  commRing := cov.commRing
  algebra := algT e cov.C
  finite := by
    haveI := cov.finite
    exact finite_algT cov.C
  etale := etale_algT h cov.C cov.etale
  ι := cov.ι
  idem j := hatEquiv e h (cov.idem j)
  isIdempotentElem_idem j := (cov.isIdempotentElem_idem j).map _
  e := cov.e
  e_pos := cov.e_pos
  e_ne_zero := cov.e_ne_zero
  κ := cov.κ
  cidem i := hatEquiv e h (cov.cidem i)
  isIdempotentElem_cidem i := (cov.isIdempotentElem_cidem i).map _
  ce := cov.ce
  ce_pos := cov.ce_pos
  ce_ne_zero := cov.ce_ne_zero
  kummer := kummerT (h := h) cov

lemma transport_kummer_one_tmul (c : cov.C) :
    (cov.transport (h := h)).kummer
        ((1 : Hat f₂) ⊗ₜ[R₂] (@id (cov.transport (h := h)).C c)) =
      piecesEquiv (h := h) cov (cov.kummer ((1 : Hat f) ⊗ₜ[R₁] c)) := by
  letI := algT e cov.C
  change piecesEquiv (h := h) cov (cov.kummer (tensorEquiv (h := h) e cov.C
    ((1 : Hat f₂) ⊗ₜ[R₂] (@id (cov.transport (h := h)).C c)))) = _
  rw [tensorEquiv_tmul, map_one]
  rfl

end

end Admissible

end SemistableReduction
