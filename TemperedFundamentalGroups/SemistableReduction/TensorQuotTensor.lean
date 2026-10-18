/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Reduction of a tensor product along compatible surjections (Blueprint §12.8, M2.3 (d'), κ3)

Let `S`, `B` be `A`-algebras, `A'` an `A`-algebra with `A → A'` surjective with kernel `K`,
`S'`, `B'` `A'`-algebras, and `σ : S → S'`, `β : B → B'` surjective `A`-algebra maps with kernels
`KS` and `KB`. Then (**`TensorQuotTensor.equiv`**)

  `(S ⊗_A B)/K(S ⊗_A B) ≃+* S' ⊗_{A'} B'`,  `s ⊗ b ↦ σ s ⊗ β b` (`equiv_mk_tmul`).

This is the reduction of a Kummer factor `(R̂/(1 − ε̃)) ⊗_{O[u,v]/(uv−π^e)} O[s,t]/(st−π)` of the
formal model modulo `ϖ` to the Kummer factor `(R̂'/(1 − ε)) ⊗_{k[u,v]/(uv)} k[s,t]/(st)` of an
admissible covering of the special fibre (`Admissible.KummerPiece`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace TensorQuotTensor

noncomputable section

variable {A S B A' S' B' : Type u} [CommRing A] [CommRing S] [CommRing B] [Algebra A S]
  [Algebra A B] [CommRing A'] [CommRing S'] [CommRing B'] [Algebra A' S'] [Algebra A' B']
  [Algebra A A'] [Algebra A S'] [Algebra A B'] [IsScalarTower A A' S'] [IsScalarTower A A' B']
  (σ : S →ₐ[A] S') (β : B →ₐ[A] B')

variable (A') in
/-- The forward map `S ⊗_A B → S' ⊗_{A'} B'`, `s ⊗ b ↦ σ s ⊗ β b`. -/
def fwd₀ : S ⊗[A] B →ₐ[A] S' ⊗[A'] B' :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : S' →ₐ[A'] S' ⊗[A'] B').restrictScalars A).comp σ)
    (((Algebra.TensorProduct.includeRight : B' →ₐ[A'] S' ⊗[A'] B').restrictScalars A).comp β)
    fun _ _ ↦ Commute.all _ _

variable (A') in
lemma fwd₀_tmul (s : S) (b : B) : fwd₀ A' σ β (s ⊗ₜ b) = σ s ⊗ₜ[A'] β b := by
  simp [fwd₀]

variable (K : Ideal A) (hν : RingHom.ker (algebraMap A A') = K)

/-- The ideal `K (S ⊗_A B)`. -/
abbrev KT : Ideal (S ⊗[A] B) := K.map (algebraMap A (S ⊗[A] B))

include hν in
lemma KT_le : KT K (S := S) (B := B) ≤ RingHom.ker (fwd₀ A' σ β).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, IsScalarTower.algebraMap_apply A A' (S' ⊗[A'] B')]
  rw [← hν] at ha
  rw [RingHom.mem_ker.mp ha, map_zero]

/-- The forward map on the quotient. -/
def fwd : S ⊗[A] B ⧸ KT K (S := S) (B := B) →+* S' ⊗[A'] B' :=
  Ideal.Quotient.lift _ (fwd₀ A' σ β).toRingHom fun _ hx ↦ KT_le σ β K hν hx

lemma fwd_mk_tmul (s : S) (b : B) :
    fwd σ β K hν (Ideal.Quotient.mk _ (s ⊗ₜ b)) = σ s ⊗ₜ[A'] β b := by
  rw [fwd, Ideal.Quotient.lift_mk]
  exact fwd₀_tmul A' σ β s b

/-! ### The inverse map -/

/-- Descend a ring map along a surjection whose kernel it kills. -/
def desc {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z] (g : X →+* Y)
    (hg : Function.Surjective g) (h : X →+* Z) (hk : RingHom.ker g ≤ RingHom.ker h) : Y →+* Z :=
  (Ideal.Quotient.lift (RingHom.ker g) h hk).comp
    (RingHom.quotientKerEquivOfSurjective hg).symm.toRingHom

lemma desc_apply {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z] (g : X →+* Y)
    (hg : Function.Surjective g) (h : X →+* Z) (hk : RingHom.ker g ≤ RingHom.ker h) (x : X) :
    desc g hg h hk (g x) = h x := by
  have : (RingHom.quotientKerEquivOfSurjective hg).symm (g x) = Ideal.Quotient.mk _ x := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  simp only [desc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  erw [this, Ideal.Quotient.lift_mk]

variable {σ β} (hνs : Function.Surjective (algebraMap A A')) (hσs : Function.Surjective σ)
  (hβs : Function.Surjective β)
  (hσk : RingHom.ker σ = K.map (algebraMap A S)) (hβk : RingHom.ker β = K.map (algebraMap A B))

variable (S B) in
include hν in
lemma ker_le_A : RingHom.ker (algebraMap A A') ≤ RingHom.ker
    ((Ideal.Quotient.mk (KT K (S := S) (B := B))).comp (algebraMap A (S ⊗[A] B))) := by
  rw [hν]
  intro a ha
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha

variable (S B) in
/-- `A' → (S ⊗_A B)/K`. -/
def νQ : A' →+* S ⊗[A] B ⧸ KT K (S := S) (B := B) :=
  desc (algebraMap A A') hνs _ (ker_le_A S B K hν)

lemma νQ_apply (a : A) : νQ S B K hν hνs (algebraMap A A' a) =
    Ideal.Quotient.mk (KT K (S := S) (B := B)) (algebraMap A (S ⊗[A] B) a) :=
  desc_apply _ hνs _ _ a

include hσk in
lemma ker_le_S : RingHom.ker σ ≤ RingHom.ker
    ((Ideal.Quotient.mk (KT K (S := S) (B := B))).comp
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B)) := by
  rw [hσk, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  have : (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B) (algebraMap A S a) =
      algebraMap A (S ⊗[A] B) a := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.algebraMap_apply]
  rw [this]
  exact Ideal.mem_map_of_mem _ ha

include hβk in
lemma ker_le_B : RingHom.ker β ≤ RingHom.ker
    ((Ideal.Quotient.mk (KT K (S := S) (B := B))).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B).toRingHom) := by
  rw [hβk, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ ha

/-- `S' → (S ⊗_A B)/K`, `σ s ↦ s ⊗ 1`. -/
def σQ : S' →+* S ⊗[A] B ⧸ KT K (S := S) (B := B) :=
  desc σ.toRingHom hσs _ (ker_le_S K hσk)

/-- `B' → (S ⊗_A B)/K`, `β b ↦ 1 ⊗ b`. -/
def βQ : B' →+* S ⊗[A] B ⧸ KT K (S := S) (B := B) :=
  desc β.toRingHom hβs _ (ker_le_B K hβk)

lemma σQ_apply (s : S) : σQ K hσs hσk (σ s) = Ideal.Quotient.mk _ (s ⊗ₜ[A] (1 : B)) :=
  desc_apply σ.toRingHom hσs _ _ s

lemma βQ_apply (b : B) : βQ K hβs hβk (β b) = Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[A] b) :=
  desc_apply β.toRingHom hβs _ _ b

lemma σQ_commutes (a : A) :
    σQ K hσs hσk (algebraMap A' S' (algebraMap A A' a)) = νQ S B K hν hνs (algebraMap A A' a) := by
  rw [← IsScalarTower.algebraMap_apply, ← σ.commutes, σQ_apply, νQ_apply,
    Algebra.TensorProduct.algebraMap_apply]

lemma βQ_commutes (a : A) :
    βQ K hβs hβk (algebraMap A' B' (algebraMap A A' a)) = νQ S B K hν hνs (algebraMap A A' a) := by
  rw [← IsScalarTower.algebraMap_apply, ← β.commutes, βQ_apply, νQ_apply,
    ← (Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B).commutes]
  rfl

variable (S B) in
/-- The `A'`-algebra structure on `(S ⊗_A B)/K`. -/
abbrev algQ : Algebra A' (S ⊗[A] B ⧸ KT K (S := S) (B := B)) := (νQ S B K hν hνs).toAlgebra

/-- `σQ` as an `A'`-algebra map. -/
def σQₐ : letI := algQ S B K hν hνs; S' →ₐ[A'] S ⊗[A] B ⧸ KT K (S := S) (B := B) :=
  letI := algQ S B K hν hνs
  { σQ K hσs hσk with
    commutes' := fun a' ↦ by
      obtain ⟨a, rfl⟩ := hνs a'
      exact σQ_commutes K hν hνs hσs hσk a }

/-- `βQ` as an `A'`-algebra map. -/
def βQₐ : letI := algQ S B K hν hνs; B' →ₐ[A'] S ⊗[A] B ⧸ KT K (S := S) (B := B) :=
  letI := algQ S B K hν hνs
  { βQ K hβs hβk with
    commutes' := fun a' ↦ by
      obtain ⟨a, rfl⟩ := hνs a'
      exact βQ_commutes K hν hνs hβs hβk a }

/-- The inverse map `S' ⊗_{A'} B' → (S ⊗_A B)/K`. -/
def bwd : S' ⊗[A'] B' →+* S ⊗[A] B ⧸ KT K (S := S) (B := B) :=
  letI := algQ S B K hν hνs
  (Algebra.TensorProduct.lift (σQₐ K hν hνs hσs hσk) (βQₐ K hν hνs hβs hβk)
    fun _ _ ↦ Commute.all _ _).toRingHom

lemma bwd_tmul (s : S) (b : B) :
    bwd K hν hνs hσs hβs hσk hβk (σ s ⊗ₜ[A'] β b) = Ideal.Quotient.mk _ (s ⊗ₜ b) := by
  letI := algQ S B K hν hνs
  change (Algebra.TensorProduct.lift (σQₐ K hν hνs hσs hσk) (βQₐ K hν hνs hβs hβk)
    fun _ _ ↦ Commute.all _ _) (σ s ⊗ₜ[A'] β b) = _
  rw [Algebra.TensorProduct.lift_tmul]
  change σQ K hσs hσk (σ s) * βQ K hβs hβk (β b) = _
  rw [σQ_apply, βQ_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **`(S ⊗_A B)/K ≃ S' ⊗_{A'} B'`.** -/
def equiv : S ⊗[A] B ⧸ KT K (S := S) (B := B) ≃+* S' ⊗[A'] B' :=
  RingEquiv.ofRingHom (fwd σ β K hν) (bwd K hν hνs hσs hβs hσk hβk)
    (by
      refine RingHom.ext fun x ↦ ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s' b' =>
        obtain ⟨s, rfl⟩ := hσs s'
        obtain ⟨b, rfl⟩ := hβs b'
        change fwd σ β K hν (bwd K hν hνs hσs hβs hσk hβk (σ s ⊗ₜ[A'] β b)) = σ s ⊗ₜ[A'] β b
        rw [bwd_tmul, fwd_mk_tmul]
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy])
    (by
      refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_)
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s b =>
        change bwd K hν hνs hσs hβs hσk hβk (fwd σ β K hν (Ideal.Quotient.mk _ (s ⊗ₜ b))) =
          Ideal.Quotient.mk _ (s ⊗ₜ b)
        rw [fwd_mk_tmul, bwd_tmul]
      | add x y hx hy => simp only [map_add, RingHom.comp_apply] at hx hy ⊢; rw [hx, hy])

lemma equiv_mk_tmul (s : S) (b : B) :
    equiv K hν hνs hσs hβs hσk hβk (Ideal.Quotient.mk _ (s ⊗ₜ b)) = σ s ⊗ₜ[A'] β b :=
  fwd_mk_tmul σ β K hν s b

end

end TensorQuotTensor

end SemistableReduction
