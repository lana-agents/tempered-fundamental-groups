/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TemperedFundamentalGroups.SemistableReduction.AdmissibleCuspPatch
import TemperedFundamentalGroups.SemistableReduction.CompletionSurj

/-!
# Reduction of the lifted formal models from level `n + 1` to level `n` (Blueprint §12.8, M2.3)

For the compatibility of the level-`n` patchings (`FormalGlueingQuot.equiv`) one needs the
reduction `ρN : N → N'` of the formal models, surjective with kernel `IN`. Setting: a chart `R`
over `O`, an `R`-algebra `R'` over `O` with surjective structure map `q : R → R'` (the next lower
level, kernel `I`), `f ∈ R`, the completion map `ψ : R̂ → R'^∧` along `q f` (`CompletionSurj.ψ`).
The lift data at the two levels share the deformation parameters `π_j ∈ O` and are related by
`ψ ∘ χ_j = χ'_j`, `ψ ε̃_j = ε̃'_j`, `ψ δ̃_i = δ̃'_i`, `ψ t̃ = t̃'`.

* `KummerReduce.σb`: `R̂/(1 − ε̃) → R'^∧/(1 − ε̃')`, surjective, kernel `I·R̂/(1 − ε̃)` (`ker_σb`,
  from `CompletionSurj.ker_ψ`);
* **`KummerReduce.ρ`** for one Kummer factor `N = (R̂/(1 − ε̃)) ⊗_{O[u,v]/(uv−π^e)} O[s,t]/(st − π)`
  (`AdmissibleLift.N`): `σb ⊗ id`, `surjective_ρ`, **`ker_ρ`** (`= I N`, Mathlib
  `Algebra.TensorProduct.rTensor_ker`);
* **`KummerReduce.ρc`** for one cusp factor `(R̂/(1 − δ̃))[X]/(X^e − t̃)` (`AdmissibleLift.CPiece`):
  induced by `σb` on polynomials, `surjective_ρc`, **`ker_ρc`** (`= I·CPiece`, via
  `Polynomial.ker_mapRingHom`);
* **`KummerReduce.ρF`** for the full lifted model `∏_{ι ⊕ κ}` (`AdmissibleLift.NFr`): factorwise,
  `surjective_ρF`, **`ker_ρF`** (`= I·∏`, `ker_pi`), `ρF_algebraMap` (`R`-linear over `q`),
  `ρF_smul` (semilinear over `ψ`)

— the hypotheses `hρN`, `hρNs`, `hρNk` of `FormalGlueingQuot.equiv`.
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

open KummerEtale

namespace KummerReduce

noncomputable section

open AdmissibleLift

/-! ### Kernels of products of maps -/

section Pi

variable {T : Type u} [CommRing T] (I : Ideal T) {ι : Type} [Finite ι] {M M' : ι → Type u}
  [∀ j, CommRing (M j)] [∀ j, Algebra T (M j)] [∀ j, CommRing (M' j)]

/-- The product `∏_j M_j → ∏_j M'_j` of ring maps. -/
def piMap (g : ∀ j, M j →+* M' j) : (∀ j, M j) →+* ∀ j, M' j :=
  RingHom.pi fun j ↦ (g j).comp (Pi.evalRingHom M j)

omit [Finite ι] in
lemma piMap_apply (g : ∀ j, M j →+* M' j) (x : ∀ j, M j) (j : ι) : piMap g x j = g j (x j) := rfl

omit [∀ j, Algebra T (M j)] [Finite ι] in
lemma surjective_piMap (g : ∀ j, M j →+* M' j) (hg : ∀ j, Function.Surjective (g j)) :
    Function.Surjective (piMap g) := fun y ↦
  ⟨fun j ↦ (hg j (y j)).choose, funext fun j ↦ (hg j (y j)).choose_spec⟩

/-- **The kernel of a product of maps with kernels `I M_j` is `I ∏_j M_j`.** -/
lemma ker_piMap (g : ∀ j, M j →+* M' j)
    (hg : ∀ j, RingHom.ker (g j) = I.map (algebraMap T (M j))) :
    RingHom.ker (piMap g) = I.map (algebraMap T (∀ j, M j)) := by
  classical
  cases nonempty_fintype ι
  apply le_antisymm
  · intro x hx
    have hx' : ∀ j, x j ∈ I.map (algebraMap T (M j)) := fun j ↦ by
      rw [← hg j, RingHom.mem_ker]
      exact congrFun (RingHom.mem_ker.mp hx) j
    rw [← Finset.univ_sum_single x]
    exact Ideal.sum_mem _ fun j _ ↦ PiQuot.single_mem I M j (hx' j)
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    funext j
    rw [piMap_apply]
    exact (hg j).ge (Ideal.mem_map_of_mem _ hr)

end Pi

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R]
  {R' : Type u} [CommRing R'] [Algebra O R'] [Algebra R R'] (f : R)

/-- The image of `f` in `R'`. -/
abbrev f' : R' := algebraMap R R' f

/-- The completion map `ψ : R̂ → R'^∧`. -/
abbrev ψI : FormalPatchLevel.Hat f →ₐ[R] FormalPatchLevel.Hat (f' (R' := R') f) :=
  CompletionSurj.ψ f

/-- The kernel `I` of `R → R'`. -/
abbrev I : Ideal R := RingHom.ker (algebraMap R R')

/-! ### The bases `R̂/(1 − ε̃)` -/

section Base

variable {f} (ε : FormalPatchLevel.Hat f) (ε' : FormalPatchLevel.Hat (f' (R' := R') f))
  (hε : ψI f ε = ε')

include hε in
lemma span_le :
    Ideal.span {1 - ε} ≤ (Ideal.span {1 - ε'}).comap (ψI (R' := R') f).toRingHom := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_one, hε]
  exact Ideal.subset_span rfl

/-- `σb : R̂/(1 − ε̃) → R'^∧/(1 − ε̃')`. -/
def σb : FormalPatchLevel.Hat f ⧸ Ideal.span {1 - ε} →+*
    FormalPatchLevel.Hat (f' (R' := R') f) ⧸ Ideal.span {1 - ε'} :=
  Ideal.quotientMap _ (ψI (R' := R') f).toRingHom (span_le ε ε' hε)

lemma σb_mk (x : FormalPatchLevel.Hat f) :
    σb ε ε' hε (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ψI (R' := R') f x) :=
  Ideal.quotientMap_mk

variable (hq : Function.Surjective (algebraMap R R'))

include hq in
lemma surjective_σb : Function.Surjective (σb ε ε' hε) :=
  Ideal.quotientMap_surjective (CompletionSurj.surjective_ψ hq)

include hq in
/-- **`ker σb = I·R̂/(1 − ε̃)`.** -/
lemma ker_σb [IsNoetherianRing R] :
    RingHom.ker (σb ε ε' hε) =
      (I (R' := R')).map (algebraMap R (FormalPatchLevel.Hat f ⧸ Ideal.span {1 - ε})) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, σb_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, rfl⟩ := CompletionSurj.surjective_ψ hq z
    have hker : y - w * (1 - ε) ∈ RingHom.ker (ψI (R' := R') f) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_sub, map_one, hε]
      change ψI (R' := R') f y - ψI (R' := R') f w * (1 - ε') = 0
      rw [← hz, sub_self]
    rw [CompletionSurj.ker_ψ hq] at hker
    have heq : (Ideal.Quotient.mk (Ideal.span {1 - ε}) y) =
        Ideal.Quotient.mk (Ideal.span {1 - ε}) (y - w * (1 - ε)) := by
      have h1 : (Ideal.Quotient.mk (Ideal.span {1 - ε}) (1 - ε)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [map_sub, map_mul, h1, mul_zero, sub_zero]
    rw [heq]
    have hmap : ((I (R' := R')).map (algebraMap R (FormalPatchLevel.Hat f))).map
        (Ideal.Quotient.mk (Ideal.span {1 - ε})) =
          (I (R' := R')).map (algebraMap R (FormalPatchLevel.Hat f ⧸ Ideal.span {1 - ε})) := by
      rw [Ideal.map_map]
      rfl
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hker
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change σb ε ε' hε (Ideal.Quotient.mk _ (algebraMap R _ r)) = 0
    rw [σb_mk, AlgHom.commutes, show algebraMap R (FormalPatchLevel.Hat (f' (R' := R') f)) r =
      algebraMap R' _ (algebraMap R R' r) from rfl, RingHom.mem_ker.mp hr, map_zero, map_zero]

end Base

/-! ### One Kummer factor -/

section Kummer

variable {f} {π : O} {e : ℕ} (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)
  (χ' : A π e →ₐ[O] FormalPatchLevel.Hat (f' (R' := R') f))
  (ε' : FormalPatchLevel.Hat (f' (R' := R') f))
  (hχ : ∀ a, ψI f (χ a) = χ' a) (hε : ψI f ε = ε')

/-- `σ : R̂/(1 − ε̃) → R'^∧/(1 − ε̃')` over the node ring. -/
def σI : LPiece f χ ε →ₐ[A π e] LPiece (f' (R' := R') f) χ' ε' :=
  { σb ε ε' hε with
    commutes' := fun a ↦ by
      change σb ε ε' hε (Ideal.Quotient.mk _ (χ a)) = Ideal.Quotient.mk _ (χ' a)
      rw [σb_mk, hχ] }

lemma σI_mk (x : FormalPatchLevel.Hat f) :
    σI χ ε χ' ε' hχ hε (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ψI (R' := R') f x) :=
  σb_mk ε ε' hε x

/-- **The reduction `ρ : N → N'`** of a lifted Kummer factor. -/
def ρ : N f χ ε →ₐ[A π e] N (f' (R' := R') f) χ' ε' :=
  Algebra.TensorProduct.map (σI χ ε χ' ε' hχ hε) (AlgHom.id (A π e) (B π))

lemma ρ_tmul (s : LPiece f χ ε) (b : B π) :
    ρ χ ε χ' ε' hχ hε (s ⊗ₜ b) = σI χ ε χ' ε' hχ hε s ⊗ₜ b := rfl

variable (hq : Function.Surjective (algebraMap R R'))

include hq in
lemma surjective_ρ : Function.Surjective (ρ χ ε χ' ε' hχ hε) :=
  Algebra.TensorProduct.map_surjective _ _ (surjective_σb ε ε' hε hq) Function.surjective_id

include hq in
/-- **The kernel of `ρ` is `I N`.** -/
theorem ker_ρ [IsNoetherianRing R] :
    RingHom.ker (ρ χ ε χ' ε' hχ hε) = (I (R' := R')).map (algebraMap R (N f χ ε)) := by
  have h := Algebra.TensorProduct.rTensor_ker (σI χ ε χ' ε' hχ hε) (R := A π e) (C := B π)
    (surjective_σb ε ε' hε hq)
  change RingHom.ker (Algebra.TensorProduct.map (σI χ ε χ' ε' hχ hε)
    (AlgHom.id (A π e) (B π))) = _
  rw [h]
  have hk : RingHom.ker (σI χ ε χ' ε' hχ hε) = RingHom.ker (σb ε ε' hε) := rfl
  rw [hk, ker_σb ε ε' hε hq]
  change Ideal.map (Algebra.TensorProduct.includeLeft (R := A π e) (S := A π e)
    (A := LPiece f χ ε) (B := B π)).toRingHom
      ((I (R' := R')).map (algebraMap R (LPiece f χ ε))) = _
  rw [Ideal.map_map]
  rfl

lemma ρ_algebraMapHat (x : FormalPatchLevel.Hat f) :
    ρ χ ε χ' ε' hχ hε (algebraMap (FormalPatchLevel.Hat f) (N f χ ε) x) =
      algebraMap (FormalPatchLevel.Hat (f' (R' := R') f)) (N (f' (R' := R') f) χ' ε')
        (ψI (R' := R') f x) := by
  change ρ χ ε χ' ε' hχ hε (Ideal.Quotient.mk _ x ⊗ₜ 1) = _
  rw [ρ_tmul, σI_mk]
  rfl

end Kummer

/-! ### One cusp factor -/

section Cusp

variable {f} (δ : FormalPatchLevel.Hat f) (δ' : FormalPatchLevel.Hat (f' (R' := R') f))
  (hδ : ψI f δ = δ') (t : FormalPatchLevel.Hat f) (t' : FormalPatchLevel.Hat (f' (R' := R') f))
  (ht : ψI f t = t') (e : ℕ)

include ht in
lemma map_cpoly : (cpoly f δ t e).map (σb δ δ' hδ) = cpoly (f' (R' := R') f) δ' t' e := by
  rw [cpoly, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, σb_mk,
    ht]

include ht in
lemma span_cpoly_le : Ideal.span {cpoly f δ t e} ≤
    (Ideal.span {cpoly (f' (R' := R') f) δ' t' e}).comap (mapRingHom (σb δ δ' hδ)) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, coe_mapRingHom,
    map_cpoly δ δ' hδ t t' ht e]
  exact Ideal.subset_span rfl

/-- **The reduction `ρc : CPiece → CPiece'`** of a lifted cusp factor. -/
def ρc : CPiece f δ t e →+* CPiece (f' (R' := R') f) δ' t' e :=
  Ideal.quotientMap _ (mapRingHom (σb δ δ' hδ)) (span_cpoly_le δ δ' hδ t t' ht e)

lemma ρc_mk (p : (CBase f δ)[X]) :
    ρc δ δ' hδ t t' ht e (AdjoinRoot.mk _ p) = AdjoinRoot.mk _ (p.map (σb δ δ' hδ)) :=
  Ideal.quotientMap_mk

lemma ρc_algebraMapHat (x : FormalPatchLevel.Hat f) :
    ρc δ δ' hδ t t' ht e (algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) x) =
      algebraMap (FormalPatchLevel.Hat (f' (R' := R') f))
        (CPiece (f' (R' := R') f) δ' t' e) (ψI (R' := R') f x) := by
  change ρc δ δ' hδ t t' ht e (AdjoinRoot.mk _ (C (Ideal.Quotient.mk _ x))) =
    AdjoinRoot.mk _ (C (Ideal.Quotient.mk _ (ψI (R' := R') f x)))
  rw [ρc_mk, Polynomial.map_C, σb_mk]

variable (hq : Function.Surjective (algebraMap R R'))

include hq in
lemma surjective_ρc : Function.Surjective (ρc δ δ' hδ t t' ht e) :=
  Ideal.quotientMap_surjective (Polynomial.map_surjective _ (surjective_σb δ δ' hδ hq))

include hq in
/-- **The kernel of `ρc` is `I·CPiece`.** -/
theorem ker_ρc [IsNoetherianRing R] :
    RingHom.ker (ρc δ δ' hδ t t' ht e) =
      (I (R' := R')).map ((algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e)).comp
        (algebraMap R (FormalPatchLevel.Hat f))) := by
  have hJ : (I (R' := R')).map ((algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e)).comp
      (algebraMap R (FormalPatchLevel.Hat f))) =
      ((RingHom.ker (σb δ δ' hδ)).map C).map (AdjoinRoot.mk (cpoly f δ t e)) := by
    rw [ker_σb δ δ' hδ hq, Ideal.map_map, Ideal.map_map]
    rfl
  rw [hJ]
  apply le_antisymm
  · intro x hx
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [RingHom.mem_ker, ρc_mk, AdjoinRoot.mk_eq_zero] at hx
    obtain ⟨h', hh'⟩ := hx
    obtain ⟨h, rfl⟩ := Polynomial.map_surjective _ (surjective_σb δ δ' hδ hq) h'
    have hmem : p - cpoly f δ t e * h ∈ RingHom.ker (mapRingHom (σb δ δ' hδ)) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul,
        map_cpoly δ δ' hδ t t' ht e, hh', sub_self]
    rw [Polynomial.ker_mapRingHom] at hmem
    have heq : AdjoinRoot.mk (cpoly f δ t e) p =
        AdjoinRoot.mk (cpoly f δ t e) (p - cpoly f δ t e * h) := by
      rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero]
    rw [heq]
    exact Ideal.mem_map_of_mem _ hmem
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, ρc_mk, AdjoinRoot.mk_eq_zero]
    have : p.map (σb δ δ' hδ) = 0 := by
      rw [← coe_mapRingHom, ← RingHom.mem_ker, Polynomial.ker_mapRingHom]
      exact hp
    rw [this]
    exact dvd_zero _

end Cusp

/-! ### The full lifted model -/

section Full

variable {f} {ι κ : Type} {π : ι → O} {e : ι → ℕ}
  (χ : ∀ j, A (π j) (e j) →ₐ[O] FormalPatchLevel.Hat f) (ε : ι → FormalPatchLevel.Hat f)
  (δ : κ → FormalPatchLevel.Hat f) (t : FormalPatchLevel.Hat f) (ce : κ → ℕ)
  (χ' : ∀ j, A (π j) (e j) →ₐ[O] FormalPatchLevel.Hat (f' (R' := R') f))
  (ε' : ι → FormalPatchLevel.Hat (f' (R' := R') f))
  (δ' : κ → FormalPatchLevel.Hat (f' (R' := R') f)) (t' : FormalPatchLevel.Hat (f' (R' := R') f))
  (hχ : ∀ j a, ψI f (χ j a) = χ' j a) (hε : ∀ j, ψI f (ε j) = ε' j)
  (hδ : ∀ i, ψI f (δ i) = δ' i) (ht : ψI f t = t')

/-- The factorwise reductions. -/
def ρs : ∀ s, NFr χ ε δ t ce s →+* NFr χ' ε' δ' t' ce s
  | .inl j => (ρ (χ j) (ε j) (χ' j) (ε' j) (hχ j) (hε j)).toRingHom
  | .inr i => ρc (δ i) (δ' i) (hδ i) t t' ht (ce i)

/-- **The reduction `ρF : NF → NF'`** of the full lifted formal model. -/
def ρF : (∀ s, NFr χ ε δ t ce s) →+* ∀ s, NFr χ' ε' δ' t' ce s :=
  piMap (ρs χ ε δ t ce χ' ε' δ' t' hχ hε hδ ht)

lemma ρF_algebraMapHat (x : FormalPatchLevel.Hat f) :
    ρF χ ε δ t ce χ' ε' δ' t' hχ hε hδ ht (algebraMap (FormalPatchLevel.Hat f) _ x) =
      algebraMap (FormalPatchLevel.Hat (f' (R' := R') f)) _ (ψI (R' := R') f x) := by
  funext s
  cases s with
  | inl j => exact ρ_algebraMapHat (χ j) (ε j) (χ' j) (ε' j) (hχ j) (hε j) x
  | inr i => exact ρc_algebraMapHat (δ i) (δ' i) (hδ i) t t' ht (ce i) x

lemma ρF_smul (s : FormalPatchLevel.Hat f) (x : ∀ s, NFr χ ε δ t ce s) :
    ρF χ ε δ t ce χ' ε' δ' t' hχ hε hδ ht (s • x) =
      ψI (R' := R') f s • ρF χ ε δ t ce χ' ε' δ' t' hχ hε hδ ht x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ρF_algebraMapHat]

lemma ρF_algebraMap (r : R) :
    ρF χ ε δ t ce χ' ε' δ' t' hχ hε hδ ht (algebraMap R _ r) =
      algebraMap R' (∀ s, NFr χ' ε' δ' t' ce s) (algebraMap R R' r) := by
  have h1 : algebraMap R (∀ s, NFr χ ε δ t ce s) r =
      algebraMap (FormalPatchLevel.Hat f) _ (algebraMap R _ r) := rfl
  rw [h1, ρF_algebraMapHat, AlgHom.commutes]
  rfl

variable (hq : Function.Surjective (algebraMap R R'))

include hq in
lemma surjective_ρF : Function.Surjective (ρF χ ε δ t ce χ' ε' δ' t' hχ hε hδ ht) :=
  surjective_piMap _ fun s ↦ match s with
    | .inl j => surjective_ρ (χ j) (ε j) (χ' j) (ε' j) (hχ j) (hε j) hq
    | .inr i => surjective_ρc (δ i) (δ' i) (hδ i) t t' ht (ce i) hq

include hq in
/-- **The kernel of `ρF` is `I·NF`.** -/
theorem ker_ρF [IsNoetherianRing R] [Finite ι] [Finite κ] :
    RingHom.ker (ρF χ ε δ t ce χ' ε' δ' t' hχ hε hδ ht) =
      (I (R' := R')).map (algebraMap R (∀ s, NFr χ ε δ t ce s)) :=
  ker_piMap _ _ fun s ↦ match s with
    | .inl j => ker_ρ (χ j) (ε j) (χ' j) (ε' j) (hχ j) (hε j) hq
    | .inr i => ker_ρc (δ i) (δ' i) (hδ i) t t' ht (ce i) hq

end Full

end

end KummerReduce

end SemistableReduction
