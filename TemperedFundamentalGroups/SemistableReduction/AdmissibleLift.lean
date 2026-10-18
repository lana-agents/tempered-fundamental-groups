/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.AdmissibleCovering
import TemperedFundamentalGroups.SemistableReduction.CompletionQuot
import TemperedFundamentalGroups.SemistableReduction.TensorQuotTensor
import TemperedFundamentalGroups.SemistableReduction.NodeBaseChange
import TemperedFundamentalGroups.SemistableReduction.FormalPatchLevel
import TemperedFundamentalGroups.SemistableReduction.TensorQuotBase

/-!
# The Kummer factors of a formal model reduce to those of an admissible covering

(Blueprint §12.8, M2.3 (d'), step κ3.)

Setting: a level ring `O` with a surjection `θ : O → k` onto the residue field, a chart `R` over
`O` (Noetherian), `f ∈ R` cutting out the nodes, `R̂` the `f`-adic completion, `J = (ker θ) R`, and
the special fibre `R/J` (a `k`-algebra) with its completion `R̂' = (R/J)^∧` along `f̄`. The
completion map `ψ : R̂ → R̂'` (`AdmissibleLift.ψ`) is surjective with kernel `J R̂`
(`CompletionQuot`).

An admissible covering of the special fibre (`Admissible.Covering`) has Kummer factors
`(R̂'/(1 − ε)) ⊗_{k[u,v]/(uv)} k[s,t]/(st)` (`Admissible.KummerPiece φ ε`). A **lift** of such a
factor to the level `O` consists of

* `π ∈ O` with `θ π = 0` (the deformation parameter: `uv = π^e` upstairs),
* formal node coordinates `χ : O[u,v]/(uv − π^e) → R̂` over `O` reducing to `φ`
  (`ψ ∘ χ = φ ∘ (u, v ↦ u, v)`, hypothesis `hχ`),
* an idempotent `ε̃ ∈ R̂` with `ψ ε̃ = ε`;

the lifted factor is `(R̂/(1 − ε̃)) ⊗_{O[u,v]/(uv−π^e)} O[s,t]/(st − π)` (`LPiece`, the Kummer
algebra of `KummerFactor`). **`AdmissibleLift.pieceEquiv`**: modulo `ker θ` it is the Kummer factor
of the covering, `s ⊗ b ↦ σ s ⊗ β b` (`pieceEquiv_mk_tmul`), with `σ : R̂/(1 − ε̃) → R̂'/(1 − ε)`
induced by `ψ` and `β` the reduction of the node ring (`Node.baseMap`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace AdmissibleLift

noncomputable section

open KummerEtale

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  {R : Type u} [CommRing R] [Algebra O R] (f : R)

/-- The ideal `J = (ker θ) R` of the special fibre of the chart. -/
abbrev J : Ideal R := (RingHom.ker θ).map (algebraMap O R)

/-- The image of `f` in the special fibre `R/J`. -/
abbrev fbar : R ⧸ J θ (R := R) := Ideal.Quotient.mk (J θ) f

lemma map_span_f : (Ideal.span {f}).map (Ideal.Quotient.mk (J θ)) = Ideal.span {fbar θ f} := by
  rw [Ideal.map_span, Set.image_singleton]

/-- The completion map `ψ : R̂ → R̂' = (R/J)^∧`. -/
abbrev ψ : FormalPatchLevel.Hat f →ₐ[R] AdicCompletion (Ideal.span {fbar θ f}) (R ⧸ J θ) :=
  CompletionQuot.ψ (Ideal.span {f}) (J θ) _ (map_span_f θ f)

lemma surjective_ψ : Function.Surjective (ψ θ f) := CompletionQuot.surjective_ψ _ _ _ _

lemma ker_ψ [IsNoetherianRing R] :
    RingHom.ker (ψ θ f) = (J θ).map (algebraMap R (FormalPatchLevel.Hat f)) :=
  CompletionQuot.ker_ψ ..

lemma ψ_algebraMap_J {r : R} (hr : r ∈ J θ) : ψ θ f (algebraMap R _ r) = 0 := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (R ⧸ J θ),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-! ### The lifted base `R̂/(1 − ε̃)` of a Kummer factor -/

variable {π : O} {e : ℕ}

/-- `R̂/(1 − ε̃)`, an algebra over the node ring `O[u,v]/(uv − π^e)` through `χ`. -/
def LPiece (_χ : A π e →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f) : Type u :=
  FormalPatchLevel.Hat f ⧸ Ideal.span {1 - ε}

namespace LPiece

variable (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)

instance : CommRing (LPiece f χ ε) := Ideal.Quotient.commRing _

instance : Algebra (FormalPatchLevel.Hat f) (LPiece f χ ε) := Ideal.Quotient.algebra _

instance : Algebra R (LPiece f χ ε) := Ideal.Quotient.algebra _

instance : IsScalarTower R (FormalPatchLevel.Hat f) (LPiece f χ ε) :=
  Ideal.Quotient.isScalarTower _ _ _

instance : Algebra (A π e) (LPiece f χ ε) :=
  ((Ideal.Quotient.mk (Ideal.span {1 - ε})).comp χ.toRingHom).toAlgebra

lemma algebraMap_A (a : A π e) :
    algebraMap (A π e) (LPiece f χ ε) a = Ideal.Quotient.mk (Ideal.span {1 - ε}) (χ a) := rfl

instance : SMulCommClass (A π e) (FormalPatchLevel.Hat f) (LPiece f χ ε) :=
  ⟨fun a s x ↦ by
    change algebraMap (A π e) (LPiece f χ ε) a *
        (algebraMap (FormalPatchLevel.Hat f) (LPiece f χ ε) s * x) =
      algebraMap (FormalPatchLevel.Hat f) (LPiece f χ ε) s *
        (algebraMap (A π e) (LPiece f χ ε) a * x)
    ring⟩

end LPiece

/-! ### Reduction of a lifted Kummer factor -/

variable [Algebra k (R ⧸ J θ)]
  (φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)) (he : 0 < e)
  (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)
  (εb : Admissible.Hat (fbar θ f)) (hε : ψ θ f ε = εb)

omit [Algebra k (R ⧸ J θ)] in
include hε in
lemma span_le_comap :
    Ideal.span {1 - ε} ≤ (Ideal.span {1 - εb}).comap (ψ θ f).toRingHom := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_one, hε]
  exact Ideal.subset_span rfl

/-- `σ : R̂/(1 − ε̃) → R̂'/(1 − ε)`, induced by `ψ`. -/
def σ : LPiece f χ ε →+* Admissible.PieceBase φ εb he :=
  Ideal.quotientMap (Ideal.span {1 - εb}) (ψ θ f).toRingHom (span_le_comap θ f ε εb hε)

lemma σ_mk (x : FormalPatchLevel.Hat f) :
    σ θ f φ he χ ε εb hε (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ψ θ f x) :=
  Ideal.quotientMap_mk

lemma surjective_σ : Function.Surjective (σ θ f φ he χ ε εb hε) :=
  Ideal.quotientMap_surjective (surjective_ψ θ f)

/-- **The kernel of `σ` is `J·R̂/(1 − ε̃)`.** -/
lemma ker_σ [IsNoetherianRing R] :
    RingHom.ker (σ θ f φ he χ ε εb hε) = (J θ).map (algebraMap R (LPiece f χ ε)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, σ_mk] at hx
    change (Ideal.Quotient.mk (Ideal.span {1 - εb}) (ψ θ f y) :
      Admissible.Hat (fbar θ f) ⧸ Ideal.span {1 - εb}) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, rfl⟩ := surjective_ψ θ f z
    have hker : y - w * (1 - ε) ∈ RingHom.ker (ψ θ f) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_sub, map_one, hε, hz, sub_self]
    rw [ker_ψ] at hker
    have heq : (Ideal.Quotient.mk (Ideal.span {1 - ε}) y : LPiece f χ ε) =
        Ideal.Quotient.mk (Ideal.span {1 - ε}) (y - w * (1 - ε)) := by
      have h1 : (Ideal.Quotient.mk (Ideal.span {1 - ε}) (1 - ε) : LPiece f χ ε) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [map_sub, map_mul, h1, mul_zero, sub_zero]
    rw [heq]
    have hmap : ((J θ).map (algebraMap R (FormalPatchLevel.Hat f))).map
        (Ideal.Quotient.mk (Ideal.span {1 - ε})) = (J θ).map (algebraMap R (LPiece f χ ε)) := by
      rw [Ideal.map_map]
      rfl
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hker
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change σ θ f φ he χ ε εb hε (Ideal.Quotient.mk _ (algebraMap R _ r)) = 0
    rw [σ_mk, ψ_algebraMap_J θ f hr, map_zero]
    rfl

/-! ### The reduction equivalence of a Kummer factor -/

variable {θ} (hθ : Function.Surjective θ) (hπ : θ π = 0)

include hπ in
lemma hA : θ (π ^ e) = (0 : k) ^ e := by rw [map_pow, hπ]

variable (hχ : ∀ a, ψ θ f (χ a) = φ (Admissible.nodeCongr he (Node.baseMap θ (hA hπ) a)))

/-- The lifted Kummer factor `(R̂/(1 − ε̃)) ⊗_{O[u,v]/(uv−π^e)} O[s,t]/(st − π)`. -/
abbrev N : Type u := LPiece f χ ε ⊗[A π e] B π

/-- `N` as an `R`-algebra, through `R̂`. -/
instance : Algebra R (N f χ ε) := Algebra.compHom _ (algebraMap R (FormalPatchLevel.Hat f))

instance : @IsScalarTower R (FormalPatchLevel.Hat f) (N f χ ε) _ Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The ideal `(ker θ)·O[u,v]/(uv − π^e)`. -/
abbrev K : Ideal (A π e) := (RingHom.ker θ).map (algebraMap O (A π e))

lemma algebraMap_LPiece_comp :
    (algebraMap R (LPiece f χ ε)).comp (algebraMap O R) =
      (algebraMap (A π e) (LPiece f χ ε)).comp (algebraMap O (A π e)) := by
  refine RingHom.ext fun o ↦ ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, LPiece.algebraMap_A, AlgHom.commutes]
  rfl

lemma algebraMap_N_comp :
    (algebraMap R (N f χ ε)).comp (algebraMap O R) =
      (algebraMap (A π e) (N f χ ε)).comp (algebraMap O (A π e)) := by
  refine RingHom.ext fun o ↦ ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
    ← RingHom.comp_apply (algebraMap (A π e) (LPiece f χ ε)),
    ← algebraMap_LPiece_comp f χ ε, RingHom.comp_apply]
  rfl

omit [Algebra k (R ⧸ J θ)] in
/-- `J N = (ker θ) N` is the ideal `K N` of `TensorQuotTensor`. -/
lemma JN_eq : (J θ).map (algebraMap R (N f χ ε)) =
    TensorQuotTensor.KT (K (θ := θ) (π := π) (e := e)) (S := LPiece f χ ε) (B := B π) := by
  rw [TensorQuotTensor.KT, K, Ideal.map_map, Ideal.map_map, algebraMap_N_comp]

/-- The reduction `O[s,t]/(st − π) → k[s,t]/(st)`. -/
abbrev βr : B π →+* B (0 : k) := Node.baseMap θ hπ

/-- The algebra structure `O[u,v]/(uv − π^e) → k[u,v]/(uv)` (reduction). -/
abbrev algAA : Algebra (A π e) (A (0 : k) e) := (Node.baseMap θ (hA hπ)).toAlgebra

/-- `O[u,v]/(uv − π^e) → R̂'/(1 − ε)` through the reduction. -/
abbrev algAS : Algebra (A π e) (Admissible.PieceBase φ εb he) :=
  ((algebraMap (A (0 : k) e) (Admissible.PieceBase φ εb he)).comp
    (Node.baseMap θ (hA hπ))).toAlgebra

/-- `O[u,v]/(uv − π^e) → k[s,t]/(st)` through the reduction. -/
abbrev algAB : Algebra (A π e) (B (0 : k)) :=
  ((algebraMap (A (0 : k) e) (B (0 : k))).comp (Node.baseMap θ (hA (e := e) hπ))).toAlgebra

/-- **The reduction of a lifted Kummer factor**: `N/(ker θ)N ≃ (R̂'/(1 − ε)) ⊗ k[s,t]/(st)`. -/
def pieceEquiv [IsNoetherianRing R] :
    (N f χ ε ⧸ TensorQuotTensor.KT (K (θ := θ) (π := π) (e := e)) (S := LPiece f χ ε)
      (B := B π)) ≃+* Admissible.KummerPiece φ εb he :=
  letI := algAA (e := e) hπ
  letI := algAS f φ he εb hπ
  letI := algAB (e := e) hπ
  haveI : IsScalarTower (A π e) (A (0 : k) e) (Admissible.PieceBase φ εb he) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (A π e) (A (0 : k) e) (B (0 : k)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let σₐ : LPiece f χ ε →ₐ[A π e] Admissible.PieceBase φ εb he :=
    { σ θ f φ he χ ε εb hε with
      commutes' := fun a ↦ by
        change σ θ f φ he χ ε εb hε (Ideal.Quotient.mk _ (χ a)) = _
        rw [σ_mk, hχ]
        rfl }
  let βₐ : B π →ₐ[A π e] B (0 : k) :=
    { βr hπ with
      commutes' := fun a ↦
        RingHom.congr_fun (Node.baseMap_comp_kummer θ hπ e) a }
  TensorQuotTensor.equiv (σ := σₐ) (β := βₐ) (K (θ := θ) (π := π) (e := e))
    (Node.ker_baseMap (hA hπ) hθ) (Node.surjective_baseMap (hA hπ) hθ)
    (surjective_σ θ f φ he χ ε εb hε) (Node.surjective_baseMap hπ hθ)
    (by
      change RingHom.ker (σ θ f φ he χ ε εb hε) = _
      rw [ker_σ, K, Ideal.map_map, Ideal.map_map, algebraMap_LPiece_comp])
    (by
      change RingHom.ker (Node.baseMap θ hπ) = _
      rw [Node.ker_baseMap hπ hθ, K, Ideal.map_map, ← IsScalarTower.algebraMap_eq])

lemma pieceEquiv_mk_tmul [IsNoetherianRing R] (s : LPiece f χ ε) (b : B π) :
    pieceEquiv f φ he χ ε εb hε hθ hπ hχ (Ideal.Quotient.mk _ (s ⊗ₜ b)) =
      σ θ f φ he χ ε εb hε s ⊗ₜ[A (0 : k) e] βr hπ b := by
  letI := algAA (e := e) hπ
  letI := algAS f φ he εb hπ
  letI := algAB (e := e) hπ
  haveI : IsScalarTower (A π e) (A (0 : k) e) (Admissible.PieceBase φ εb he) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (A π e) (A (0 : k) e) (B (0 : k)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact TensorQuotTensor.equiv_mk_tmul ..

/-! ### Finite products -/

namespace PiQuot

variable {T : Type u} [CommRing T] (I : Ideal T) {ι : Type} [Finite ι] (M : ι → Type u)
  [∀ j, CommRing (M j)] [∀ j, Algebra T (M j)]

omit [Finite ι] in
/-- `∏_j M_j → ∏_j M_j/I M_j`. -/
def toPi : (∀ j, M j) →+* ∀ j, M j ⧸ I.map (algebraMap T (M j)) :=
  RingHom.pi fun j ↦ (Ideal.Quotient.mk _).comp (Pi.evalRingHom M j)

omit [Finite ι] in
lemma surjective_toPi : Function.Surjective (toPi I M) := fun y ↦
  ⟨fun j ↦ (Ideal.Quotient.mk_surjective (y j)).choose,
    funext fun j ↦ (Ideal.Quotient.mk_surjective (y j)).choose_spec⟩

omit [Finite ι] in
lemma single_mem [DecidableEq ι] (j : ι) {y : M j} (hy : y ∈ I.map (algebraMap T (M j))) :
    Pi.single j y ∈ I.map (algebraMap T (∀ j, M j)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, rfl⟩ := hz
    have : (Pi.single j (algebraMap T (M j) r) : ∀ j, M j) =
        algebraMap T (∀ j, M j) r * Pi.single j 1 := by
      funext i
      by_cases h : i = j
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr)
  | zero => simp
  | add a b _ _ ha hb => rw [Pi.single_add]; exact Ideal.add_mem _ ha hb
  | smul c a _ ha => rw [smul_eq_mul, Pi.single_mul]; exact Ideal.mul_mem_left _ _ ha

/-- **The kernel of `∏_j M_j → ∏_j M_j/I M_j` is `I ∏_j M_j`.** -/
lemma ker_toPi : RingHom.ker (toPi I M) = I.map (algebraMap T (∀ j, M j)) := by
  classical
  cases nonempty_fintype ι
  apply le_antisymm
  · intro x hx
    have hx' : ∀ j, x j ∈ I.map (algebraMap T (M j)) := fun j ↦
      Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (RingHom.mem_ker.mp hx) j)
    rw [← Finset.univ_sum_single x]
    exact Ideal.sum_mem _ fun j _ ↦ single_mem I M j (hx' j)
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    funext j
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)

/-- **`(∏_j M_j)/I ≃ ∏_j M_j/I M_j`.** -/
def equiv : ((∀ j, M j) ⧸ I.map (algebraMap T (∀ j, M j))) ≃+*
    ∀ j, M j ⧸ I.map (algebraMap T (M j)) :=
  (Ideal.quotEquivOfEq (ker_toPi I M).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_toPi I M))

lemma equiv_mk (x : ∀ j, M j) (j : ι) :
    equiv I M (Ideal.Quotient.mk _ x) j = Ideal.Quotient.mk _ (x j) := rfl

end PiQuot

/-! ### The comparison `κ` for an admissible covering of a chart without marked points -/

variable {f φ} {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  (cov : Admissible.Covering φ ψc)

/-- The covering of the special fibre as an `R`-algebra. -/
instance : Algebra R cov.C := Algebra.compHom cov.C (algebraMap R (R ⧸ J θ))

instance : IsScalarTower R (R ⧸ J θ) cov.C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- **Lift data** of the Kummer factors of an admissible covering to the level `O`: deformation
parameters `π_j` (`θ π_j = 0`), formal node coordinates `χ_j` over `O` reducing to `φ`, and
idempotents `ε̃_j` of `R̂` lifting those of the covering. -/
structure KummerLift where
  /-- The deformation parameter of the factor `j` (`uv = π_j^{e_j}` upstairs). -/
  π : cov.ι → O
  hπ : ∀ j, θ (π j) = 0
  /-- Formal node coordinates of the factor `j` at the level `O`. -/
  χ : ∀ j, A (π j) (cov.e j) →ₐ[O] FormalPatchLevel.Hat f
  /-- The lifted idempotents. -/
  ε : cov.ι → FormalPatchLevel.Hat f
  hε : ∀ j, ψ θ f (ε j) = cov.idem j
  hχ : ∀ j a, ψ θ f (χ j a) =
    φ (Admissible.nodeCongr (cov.e_pos j) (Node.baseMap θ (hA (hπ j)) a))

variable {cov} (L : KummerLift cov)

/-- The lifted formal model `N = ∏_j (R̂/(1 − ε̃_j)) ⊗ O[s,t]/(st − π_j)`. -/
abbrev NL : Type u := ∀ j, N f (L.χ j) (L.ε j)

/-- **`N/JN ≃ ∏_j KummerPiece`** (step κ3). -/
def kappa3 [IsNoetherianRing R] :
    (NL L ⧸ (J θ).map (algebraMap R (NL L))) ≃+*
      ∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j) :=
  (PiQuot.equiv (J θ) _).trans (RingEquiv.piCongrRight fun j ↦
    (Ideal.quotEquivOfEq (JN_eq f (L.χ j) (L.ε j))).trans
      (pieceEquiv f φ (cov.e_pos j) (L.χ j) (L.ε j) (cov.idem j) (L.hε j) hθ (L.hπ j) (L.hχ j)))

lemma kappa3_algebraMap [IsNoetherianRing R] (x : FormalPatchLevel.Hat f) (j : cov.ι) :
    kappa3 hθ L (Ideal.Quotient.mk _ (algebraMap (FormalPatchLevel.Hat f) (NL L) x)) j =
      algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f x) := by
  change pieceEquiv f φ (cov.e_pos j) (L.χ j) (L.ε j) (cov.idem j) (L.hε j) hθ (L.hπ j) (L.hχ j)
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x ⊗ₜ 1)) = _
  rw [pieceEquiv_mk_tmul, σ_mk, map_one]
  rfl

/-- The ring isomorphism underlying `κ`. -/
def kappaRing [IsNoetherianRing R] [IsEmpty cov.κ] :
    (FormalPatchLevel.Hat f ⊗[R] cov.C) ≃+* (NL L ⧸ (J θ).map (algebraMap R (NL L))) :=
  (((TensorQuotBase.equiv (C := cov.C) (surjective_ψ θ f) (ker_ψ θ f)).trans
    cov.kummer.toRingEquiv).trans (RingEquiv.prodZeroRing _ _).symm).trans (kappa3 hθ L).symm

lemma kappa3_kappaRing [IsNoetherianRing R] [IsEmpty cov.κ]
    (y : FormalPatchLevel.Hat f ⊗[R] cov.C) :
    kappa3 hθ L (kappaRing hθ L y) = (RingEquiv.prodZeroRing _ _).symm
      (cov.kummer (TensorQuotBase.equiv (C := cov.C) (surjective_ψ θ f) (ker_ψ θ f) y)) := by
  rw [kappaRing, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

lemma kummer_algebraMap [IsNoetherianRing R] [IsEmpty cov.κ] (x : FormalPatchLevel.Hat f) :
    (RingEquiv.prodZeroRing _ _).symm (cov.kummer (TensorQuotBase.equiv (C := cov.C)
      (surjective_ψ θ f) (ker_ψ θ f) (x ⊗ₜ 1))) =
      algebraMap (Admissible.Hat (fbar θ f)) (∀ j, Admissible.KummerPiece φ (cov.idem j)
        (cov.e_pos j)) (ψ θ f x) := by
  rw [TensorQuotBase.equiv_tmul]
  have h2 : (ψ θ f x ⊗ₜ[R ⧸ J θ] (1 : cov.C)) =
      algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f x) := rfl
  rw [h2, AlgEquiv.commutes]
  rfl

/-- **The comparison `κ : R̂ ⊗_R C ≃ N/JN`** of the completed special-fibre covering with the
reduction of the lifted formal model (an admissible covering of a chart without marked points). -/
def kappa [IsNoetherianRing R] [IsEmpty cov.κ] :
    (FormalPatchLevel.Hat f ⊗[R] cov.C) ≃ₐ[FormalPatchLevel.Hat f]
      (NL L ⧸ (J θ).map (algebraMap R (NL L))) :=
  AlgEquiv.ofRingEquiv (f := kappaRing hθ L) fun x ↦ by
    apply (kappa3 hθ L).injective
    rw [kappa3_kappaRing]
    have h1 : algebraMap (FormalPatchLevel.Hat f) (NL L ⧸ (J θ).map (algebraMap R (NL L))) x =
        Ideal.Quotient.mk _ (algebraMap (FormalPatchLevel.Hat f) (NL L) x) := rfl
    have h0 : algebraMap (FormalPatchLevel.Hat f) (FormalPatchLevel.Hat f ⊗[R] cov.C) x =
        x ⊗ₜ 1 := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h0, kummer_algebraMap, h1]
    funext j
    rw [kappa3_algebraMap, Pi.algebraMap_apply]

end

end AdmissibleLift

end SemistableReduction
