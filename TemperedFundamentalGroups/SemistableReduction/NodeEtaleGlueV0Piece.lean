/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlapPiece
import TemperedFundamentalGroups.SemistableReduction.AdmissibleLift

/-!
# The piece of a covering over a basic open of the second chart (Blueprint §12.8, M2.3 (f))

The covering over the second chart `V₀ = Spec B0'` of a model of `ℙ¹` is glued from its
restriction to the overlap with the first chart and a **piece over a basic open `D(c₀)`**. This
file isolates what the assembly (`NodeEtaleGlue.Overlap`) and the tower need from that piece, as
the structure **`NodeEtaleGlue.Piece0`**: at every level `n` of `V₀` (charts `B' n`)

* an algebra `P n` over `B' n` in which `c₀` is a unit, finite over `D(c₀)` (`hfinP`);
* its restriction `Loc0 (B' n) (P n) x₀ = P n[1/x₀]` to the overlap is formally étale over
  `B' n`, with a special-fibre map `ℓ0 n : C0 → P n[1/x₀]/J` (`C0` the special-fibre covering
  over `V₀`) exhibiting the special fibre as `C0[1/(c̄₀ x̄₀)]`;
* successor maps `sP n : P (n+1) → P n` (surjective, kernel `ϖⁿ⁺¹`) and their localizations
  `sM n`, compatible with `ℓ0`.

Instances: **`Piece0.ofEtale`**, the étale lifts of a covering étale over `D(c̄₀)` (coverings
étale outside the nodes); a formal patch with cusp factors (coverings tamely ramified over marked
points in `D(c₀) ∖ D(x₀)`).
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

namespace NodeEtaleGlue

/-- The restriction `P[1/x₀]` of a piece `P` over a level `B` of the second chart to the
overlap. -/
abbrev Loc0 {B0' : Type u} [CommRing B0'] (B : Type u) [CommRing B] [Algebra B0' B]
    (P : Type u) [CommRing P] [Algebra B P] (x0 : B0') : Type u :=
  Localization.Away (algebraMap B P (algebraMap B0' B x0))

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  {B0' : Type u} [CommRing B0'] (B' : ℕ → Type u) [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] (qB' : ∀ n, B' n →+* Bs') (C0 : Type u) [CommRing C0]
  [Algebra Bs' C0] (x0 c0 : B0') (x0s c0s : Bs') (ϖ : O)

/-- **A piece of a covering over the basic open `D(c₀)` of the second chart**, with its levels,
successor maps and restrictions to the overlap `D(c₀ x₀)`. -/
structure Piece0 where
  /-- the piece at level `n` -/
  P : ℕ → Type u
  [commRingP : ∀ n, CommRing (P n)]
  [algP : ∀ n, Algebra (B' n) (P n)]
  [algOP : ∀ n, Algebra O (P n)]
  [towerOP : ∀ n, IsScalarTower O (B' n) (P n)]
  /-- the piece lives over `D(c₀)` -/
  hcP : ∀ n, IsUnit (algebraMap (B' n) (P n) (algebraMap B0' (B' n) c0))
  /-- finiteness over `D(c₀)` -/
  hfinP : ∀ n, ∃ s : Finset (P n), ∀ p : P n, ∃ k : ℕ,
    algebraMap B0' (B' n) c0 ^ k • p ∈ Submodule.span (B' n) (s : Set (P n))
  /-- on the overlap the piece is formally étale -/
  [etaleM : ∀ n, Algebra.FormallyEtale (B' n) (Loc0 (B' n) (P n) x0)]
  /-- the special fibre on the overlap: `C0 → P[1/x₀]/J`, a localization away from `c̄₀ x̄₀` -/
  ℓ0 : ∀ n, C0 →+* Loc0 (B' n) (P n) x0 ⧸ EtaleNil.JB (J θ (R := B' n)) (Loc0 (B' n) (P n) x0)
  hℓ0 : ∀ n (y : B' n), ℓ0 n (algebraMap Bs' C0 (qB' n y)) =
    Ideal.Quotient.mk _ (algebraMap (B' n) (Loc0 (B' n) (P n) x0) y)
  hℓ0loc : ∀ n, letI := (ℓ0 n).toAlgebra
    IsLocalization.Away (algebraMap Bs' C0 c0s * algebraMap Bs' C0 x0s)
      (Loc0 (B' n) (P n) x0 ⧸ EtaleNil.JB (J θ (R := B' n)) (Loc0 (B' n) (P n) x0))
  /-- the successor maps -/
  sP : ∀ n, P (n + 1) →+* P n
  hsP : ∀ n (x : B' (n + 1)), sP n (algebraMap (B' (n + 1)) (P (n + 1)) x) =
    algebraMap (B' n) (P n) (algebraMap (B' (n + 1)) (B' n) x)
  hsPs : ∀ n, Function.Surjective (sP n)
  hkP : ∀ n, RingHom.ker (sP n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (P (n + 1)))
  /-- the successor maps on the overlap -/
  sM : ∀ n, Loc0 (B' (n + 1)) (P (n + 1)) x0 →+* Loc0 (B' n) (P n) x0
  hsM : ∀ n (p : P (n + 1)), sM n (algebraMap (P (n + 1)) (Loc0 (B' (n + 1)) (P (n + 1)) x0) p) =
    algebraMap (P n) (Loc0 (B' n) (P n) x0) (sP n p)
  hℓ0succ : ∀ n (c : C0) (m : Loc0 (B' (n + 1)) (P (n + 1)) x0),
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' (n + 1))) (Loc0 (B' (n + 1)) (P (n + 1)) x0)) m =
      ℓ0 (n + 1) c →
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' n)) (Loc0 (B' n) (P n) x0)) (sM n m) = ℓ0 n c

attribute [instance] Piece0.commRingP Piece0.algP Piece0.algOP Piece0.towerOP Piece0.etaleM

/-! ### The étale instance -/

namespace Piece0

variable {θ B' qB' C0 x0 c0 x0s c0s ϖ}
  [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)] [∀ n, IsScalarTower O (B' (n + 1)) (B' n)]
  (E0 : ℕ → Type u) [∀ n, CommRing (E0 n)] [∀ n, Algebra (B' n) (E0 n)] [∀ n, Algebra O (E0 n)]
  [∀ n, IsScalarTower O (B' n) (E0 n)] [∀ n, Algebra.FormallyEtale (B' n) (E0 n)]
  (σE0 : ∀ n, letI := ((algebraMap Bs' C0).comp (qB' n)).toAlgebra
    (E0 n ⧸ EtaleNil.JB (J θ (R := B' n)) (E0 n)) ≃ₐ[B' n]
      Localization.Away (algebraMap Bs' C0 c0s))
  (hcE0 : ∀ n, IsUnit (algebraMap (B' n) (E0 n) (algebraMap B0' (B' n) c0)))
  (hfinE0 : ∀ n, ∃ s : Finset (E0 n), ∀ p : E0 n, ∃ k : ℕ,
    algebraMap B0' (B' n) c0 ^ k • p ∈ Submodule.span (B' n) (s : Set (E0 n)))
  (hx0 : ∀ n, qB' n (algebraMap B0' (B' n) x0) = x0s)
  (sE0 : ∀ n, E0 (n + 1) →+* E0 n)
  (hsE0 : ∀ n (x : B' (n + 1)), sE0 n (algebraMap (B' (n + 1)) (E0 (n + 1)) x) =
    algebraMap (B' n) (E0 n) (algebraMap (B' (n + 1)) (B' n) x))
  (hσE0 : ∀ n (x : E0 (n + 1)), σE0 n (Ideal.Quotient.mk _ (sE0 n x)) =
    σE0 (n + 1) (Ideal.Quotient.mk _ x))
  (hsE0s : ∀ n, Function.Surjective (sE0 n))
  (hkE0 : ∀ n, RingHom.ker (sE0 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (E0 (n + 1))))

omit [∀ n, Algebra O (E0 n)] [∀ n, IsScalarTower O (B' n) (E0 n)]
  [∀ n, Algebra.FormallyEtale (B' n) (E0 n)] in
include hsE0 in
lemma isUnit_sME (n : ℕ) : IsUnit (((algebraMap (E0 n) (Loc0 (B' n) (E0 n) x0)).comp (sE0 n))
    (algebraMap (B' (n + 1)) (E0 (n + 1)) (algebraMap B0' (B' (n + 1)) x0))) := by
  rw [RingHom.comp_apply, hsE0, ← IsScalarTower.algebraMap_apply B0' (B' (n + 1)) (B' n)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The successor maps of the étale lifts localized away from `x₀`. -/
def sME (n : ℕ) : Loc0 (B' (n + 1)) (E0 (n + 1)) x0 →+* Loc0 (B' n) (E0 n) x0 :=
  IsLocalization.Away.lift
    (algebraMap (B' (n + 1)) (E0 (n + 1)) (algebraMap B0' (B' (n + 1)) x0))
    (isUnit_sME E0 sE0 hsE0 n)

omit [∀ n, Algebra O (E0 n)] [∀ n, IsScalarTower O (B' n) (E0 n)]
  [∀ n, Algebra.FormallyEtale (B' n) (E0 n)] in
lemma sME_algebraMap (n : ℕ) (e : E0 (n + 1)) :
    sME E0 sE0 hsE0 n (algebraMap (E0 (n + 1)) (Loc0 (B' (n + 1)) (E0 (n + 1)) x0) e) =
      algebraMap (E0 n) (Loc0 (B' n) (E0 n) x0) (sE0 n e) :=
  IsLocalization.Away.lift_eq _ (isUnit_sME E0 sE0 hsE0 n) e

/-- The special-fibre map of the étale piece on the overlap (`OverlapPiece.ℓ0`). -/
abbrev ℓ0E (n : ℕ) : C0 →+* Loc0 (B' n) (E0 n) x0 ⧸
    EtaleNil.JB (J θ (R := B' n)) (Loc0 (B' n) (E0 n) x0) :=
  OverlapPiece.ℓ0 (RingHom.ker θ) (algebraMap B0' (B' n) x0) (E0 n) (qB' n) c0s (σE0 n)

omit [∀ n, Algebra.FormallyEtale (B' n) (E0 n)] in
include hσE0 in
lemma ℓ0E_succ (n : ℕ) (c : C0) (m : Loc0 (B' (n + 1)) (E0 (n + 1)) x0)
    (hm : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' (n + 1))) (Loc0 (B' (n + 1)) (E0 (n + 1))
      x0)) m = ℓ0E E0 σE0 (n + 1) c) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' n)) (Loc0 (B' n) (E0 n) x0))
      (sME E0 sE0 hsE0 n m) = ℓ0E E0 σE0 n c := by
  letI := ((algebraMap Bs' C0).comp (qB' (n + 1))).toAlgebra
  letI := ((algebraMap Bs' C0).comp (qB' n)).toAlgebra
  -- `sME` respects `J`, so it induces a map on the quotients; compare on `C0`
  have hJ : EtaleNil.JB (J θ (R := B' (n + 1))) (Loc0 (B' (n + 1)) (E0 (n + 1)) x0) ≤
      (EtaleNil.JB (J θ (R := B' n)) (Loc0 (B' n) (E0 n) x0)).comap (sME E0 sE0 hsE0 n) := by
    rw [OverlapPiece.JB_map, OverlapPiece.JB_map, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    intro o ho
    rw [Ideal.mem_comap, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply O (E0 (n + 1)) (Loc0 (B' (n + 1)) (E0 (n + 1)) x0),
      sME_algebraMap, IsScalarTower.algebraMap_apply O (B' (n + 1)) (E0 (n + 1)), hsE0,
      ← IsScalarTower.algebraMap_apply O (B' (n + 1)) (B' n),
      ← IsScalarTower.algebraMap_apply O (B' n) (E0 n),
      ← IsScalarTower.algebraMap_apply O (E0 n) (Loc0 (B' n) (E0 n) x0)]
    exact Ideal.mem_map_of_mem _ ho
  have key : (Ideal.quotientMap _ (sME E0 sE0 hsE0 n) hJ) (ℓ0E E0 σE0 (n + 1) c) =
      ℓ0E E0 σE0 n c := by
    obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective
      ((σE0 (n + 1)).symm (algebraMap C0 (Localization.Away (algebraMap Bs' C0 c0s)) c))
    have h1 : (σE0 n).symm (algebraMap C0 (Localization.Away (algebraMap Bs' C0 c0s)) c) =
        Ideal.Quotient.mk _ (sE0 n e) := by
      apply (σE0 n).injective
      rw [AlgEquiv.apply_symm_apply, hσE0, he, AlgEquiv.apply_symm_apply]
    unfold ℓ0E OverlapPiece.ℓ0
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.coe_ringEquiv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [h1, ← he, EtaleNil.red_mk, EtaleNil.red_mk, Ideal.quotientMap_mk,
      IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom', sME_algebraMap]
  rw [← key, ← hm, Ideal.quotientMap_mk]

/-- **The étale piece**: étale lifts `E0 n` of a covering `C0` étale over `D(c̄₀)`. -/
def ofEtale : Piece0 θ B' qB' C0 x0 c0 x0s c0s ϖ where
  P := E0
  hcP := hcE0
  hfinP := hfinE0
  etaleM := fun n ↦ OverlapPiece.formallyEtale_loc (algebraMap B0' (B' n) x0) (E0 n)
  ℓ0 := ℓ0E E0 σE0
  hℓ0 := fun n y ↦ OverlapPiece.ℓ0_algebraMap (RingHom.ker θ) (algebraMap B0' (B' n) x0) (E0 n)
    (qB' n) c0s (σE0 n) y
  hℓ0loc := fun n ↦ OverlapPiece.isLocalization_ℓ0 (RingHom.ker θ) (algebraMap B0' (B' n) x0)
    (E0 n) (qB' n) x0s c0s (σE0 n) (hx0 n)
  sP := sE0
  hsP := hsE0
  hsPs := hsE0s
  hkP := hkE0
  sM := sME E0 sE0 hsE0
  hsM := sME_algebraMap E0 sE0 hsE0
  hℓ0succ := ℓ0E_succ E0 σE0 sE0 hsE0 hσE0

end Piece0

end NodeEtaleGlue

end

end SemistableReduction
