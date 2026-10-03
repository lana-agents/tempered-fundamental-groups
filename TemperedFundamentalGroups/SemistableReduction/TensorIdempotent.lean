/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Idempotents of `L ⊗_C F` over an algebraically closed field

Blueprint §9.11 (the `no_split` bridge). For a field `C` and a `C`-vector space `F`, an element `t`
of `R ⊗[C] F` is determined by its coordinates `coord φ t ∈ R` along the linear functionals
`φ : F →ₗ[C] C` (`eq_zero_of_forall_coord_eq_zero`). If `C` is algebraically closed and `F`, `L` are
field extensions of `C`, then `L ⊗[C] F` has no idempotents besides `0` and `1`
(`eq_zero_or_eq_one_of_isIdempotentElem`).

Proof: write `z = Σ yᵢ ⊗ fᵢ` and lift it to `Z = Σ Xᵢ ⊗ fᵢ` over the polynomial ring
`R = C[Xᵢ]`, with `ψ : R → L`, `Xᵢ ↦ yᵢ`. The coordinates of `Z² - Z` lie in the prime
`P = ker ψ`. At every point `x` of the zero locus of `P` the specialization of `Z` is an
idempotent of the field `F`, hence `0` or `1`. So `p_φ (p_μ - μ 1)` (`p_φ` the coordinates of `Z`)
vanishes on the zero locus, lies in `P` by the Nullstellensatz, and `ψ` gives
`coord φ z · (coord μ z - μ 1) = 0` in the domain `L`.

`exists_tendsto_of_approx_idempotent` is the form used by `GaussFibre.no_split`: Cauchy sequences
of coordinates of approximate idempotents in a fixed finite family of `F`, over an algebraically
closed normed field `C` that need not be complete, converge to the coordinates of `0` or `1`
(the limit is taken in the completion `Ĉ`, and `Σ Aᵦ ⊗ uᵦ ∈ Ĉ ⊗[C] F` is an idempotent).
-/

open TensorProduct

namespace SemistableReduction

namespace TensorIdempotent

variable {C : Type*} [Field C]

section Coord

variable {R F : Type*} [CommRing R] [Algebra C R] [AddCommGroup F] [Module C F]

/-- The coordinate of `t ∈ R ⊗[C] F` along a functional `φ` of `F`. -/
noncomputable def coord (φ : F →ₗ[C] C) : R ⊗[C] F →ₗ[C] R :=
  (TensorProduct.rid C R).toLinearMap ∘ₗ φ.lTensor R

@[simp]
lemma coord_tmul (φ : F →ₗ[C] C) (r : R) (f : F) :
    coord φ (r ⊗ₜ[C] f) = φ f • r := by
  simp [coord]

lemma coord_map {S : Type*} [CommRing S] [Algebra C S] (g : R →ₐ[C] S) (φ : F →ₗ[C] C)
    (t : R ⊗[C] F) :
    g (coord φ t) = coord φ (TensorProduct.map g.toLinearMap LinearMap.id t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r f => simp
  | add x y hx hy => simp [hx, hy]

/-- An element of `R ⊗[C] F` with all coordinates zero is zero. -/
lemma eq_zero_of_forall_coord_eq_zero {t : R ⊗[C] F} (h : ∀ φ : F →ₗ[C] C, coord φ t = 0) :
    t = 0 := by
  classical
  set b := Module.Free.chooseBasis C F
  set B := Algebra.TensorProduct.basis R b
  have hrepr (i) (t : R ⊗[C] F) : B.repr t i = coord (b.coord i) t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r f =>
      simp only [B, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
        Finsupp.mapRange_apply, coord_tmul, Module.Basis.coord_apply, smul_eq_mul,
        Algebra.smul_def]
      ring
    | add x y hx hy => simp [hx, hy]
  refine B.repr.injective ?_
  ext i
  rw [hrepr, h, map_zero, Finsupp.zero_apply]

/-- Rearranging a quadratic expression `Σ Aᵦ A_γ ⊗ y_{βγ} - Σ Aᵦ ⊗ y_β` along a finite family
`w` in which the `y` are expanded. -/
lemma sum_sub_sum_tmul_eq {J K : Type*} [Fintype J] [Fintype K] (A : J → R) (y2 : J → J → F)
    (y1 : J → F) (w : K → F) (κ2 : J → J → K → C) (κ1 : J → K → C)
    (h2 : ∀ β γ, y2 β γ = ∑ t, κ2 β γ t • w t) (h1 : ∀ β, y1 β = ∑ t, κ1 β t • w t) :
    ∑ β, ∑ γ, (A β * A γ) ⊗ₜ[C] y2 β γ - ∑ β, A β ⊗ₜ[C] y1 β =
      ∑ t, (∑ β, ∑ γ, A β * A γ * algebraMap C R (κ2 β γ t) -
        ∑ β, A β * algebraMap C R (κ1 β t)) ⊗ₜ[C] w t := by
  have hs (r : R) (c : C) (f : F) : r ⊗ₜ[C] (c • f) = (r * algebraMap C R c) ⊗ₜ[C] f := by
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  simp only [h2, h1, TensorProduct.tmul_sum, hs, TensorProduct.sub_tmul, TensorProduct.sum_tmul,
    Finset.sum_sub_distrib]
  congr 1
  · exact (Finset.sum_congr rfl fun β _ ↦ Finset.sum_comm).trans Finset.sum_comm
  · exact Finset.sum_comm

end Coord

/-- Expanding `(1 ⊗ H) (Z² - Z)` for `Z = Σ Aᵦ ⊗ uᵦ`. -/
lemma one_tmul_mul_sq_sub {R F J : Type*} [CommRing R] [Algebra C R] [CommRing F] [Algebra C F]
    [Fintype J] (A : J → R) (u : J → F) (H : F) :
    ((1 : R) ⊗ₜ[C] H) * ((∑ β, A β ⊗ₜ[C] u β) * (∑ β, A β ⊗ₜ[C] u β) - ∑ β, A β ⊗ₜ[C] u β) =
      ∑ β, ∑ γ, (A β * A γ) ⊗ₜ[C] (H * (u β * u γ)) - ∑ β, A β ⊗ₜ[C] (H * u β) := by
  rw [Finset.sum_mul_sum, mul_sub, Finset.mul_sum, Finset.mul_sum]
  simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

lemma coord_one {R F : Type*} [CommRing R] [Algebra C R] [Ring F] [Algebra C F]
    (φ : F →ₗ[C] C) : coord φ (1 : R ⊗[C] F) = algebraMap C R (φ 1) := by
  rw [Algebra.TensorProduct.one_def, coord_tmul, Algebra.smul_def, mul_one]

/-- **Idempotents of `L ⊗[C] F`**: for `C` algebraically closed and `F`, `L` fields over `C`, every
idempotent of `L ⊗[C] F` is `0` or `1`. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem [IsAlgClosed C] {F L : Type*} [Field F]
    [Algebra C F] [Field L] [Algebra C L] {z : L ⊗[C] F} (hz : IsIdempotentElem z) :
    z = 0 ∨ z = 1 := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset z
  set R := MvPolynomial S C
  set ψ : R →ₐ[C] L := MvPolynomial.aeval fun i ↦ i.1.1
  set Z : R ⊗[C] F := ∑ i : S, MvPolynomial.X i ⊗ₜ[C] i.1.2
  have hZ : TensorProduct.map ψ.toLinearMap LinearMap.id Z = z := by
    rw [hS, ← Finset.sum_coe_sort S]
    simp only [Z, ψ, map_sum, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      LinearMap.id_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    exact MvPolynomial.aeval_X (R := C) (fun i : S ↦ i.1.1) i
  set P : Ideal R := RingHom.ker ψ
  haveI : P.IsPrime := RingHom.ker_isPrime ψ
  set p : (F →ₗ[C] C) → R := fun φ ↦ coord φ Z
  have hψp (φ : F →ₗ[C] C) : ψ (p φ) = coord φ z := by
    rw [coord_map, hZ]
  have hmap (g : R →ₐ[C] L) (T T' : R ⊗[C] F) :
      TensorProduct.map g.toLinearMap LinearMap.id (T * T') =
        TensorProduct.map g.toLinearMap LinearMap.id T *
          TensorProduct.map g.toLinearMap LinearMap.id T' :=
    map_mul (Algebra.TensorProduct.map g (AlgHom.id C F)) T T'
  -- the coordinates of `Z² - Z` lie in `P`
  have hq (φ : F →ₗ[C] C) : coord φ (Z * Z - Z) ∈ P := by
    rw [RingHom.mem_ker, coord_map,
      show TensorProduct.map ψ.toLinearMap LinearMap.id (Z * Z - Z) = z * z - z by
        rw [map_sub, hmap, hZ], hz.eq, sub_self, map_zero]
  -- at every point of the zero locus, `Z` specializes to `0` or `1`
  have hpt (x : S → C) (hx : x ∈ MvPolynomial.zeroLocus C P) :
      (∀ φ, MvPolynomial.aeval x (p φ) = 0) ∨ ∀ φ, MvPolynomial.aeval x (p φ) = φ 1 := by
    set ex : R →ₐ[C] C := MvPolynomial.aeval x
    set Zx : C ⊗[C] F := TensorProduct.map ex.toLinearMap LinearMap.id Z
    have hmapx (T T' : R ⊗[C] F) :
        TensorProduct.map ex.toLinearMap LinearMap.id (T * T') =
          TensorProduct.map ex.toLinearMap LinearMap.id T *
            TensorProduct.map ex.toLinearMap LinearMap.id T' :=
      map_mul (Algebra.TensorProduct.map ex (AlgHom.id C F)) T T'
    have hidem : Zx * Zx = Zx := by
      rw [← sub_eq_zero]
      refine eq_zero_of_forall_coord_eq_zero fun φ ↦ ?_
      have := (MvPolynomial.mem_zeroLocus_iff.1 hx) _ (hq φ)
      rw [show (MvPolynomial.aeval x) (coord φ (Z * Z - Z)) = ex (coord φ (Z * Z - Z)) from rfl,
        coord_map, map_sub, hmapx] at this
      exact this
    have hlid : IsIdempotentElem (Algebra.TensorProduct.lid C F Zx) := by
      rw [IsIdempotentElem, ← map_mul, hidem]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hlid with h0 | h1
    · left
      intro φ
      have : Zx = 0 := (Algebra.TensorProduct.lid C F).injective (by rw [h0, map_zero])
      rw [show (MvPolynomial.aeval x) (p φ) = ex (coord φ Z) from rfl, coord_map]
      rw [show TensorProduct.map ex.toLinearMap LinearMap.id Z = Zx from rfl, this, map_zero]
    · right
      intro φ
      have : Zx = 1 := (Algebra.TensorProduct.lid C F).injective (by rw [h1, map_one])
      rw [show (MvPolynomial.aeval x) (p φ) = ex (coord φ Z) from rfl, coord_map]
      rw [show TensorProduct.map ex.toLinearMap LinearMap.id Z = Zx from rfl, this, coord_one]
      rfl
  -- hence `p φ (p μ - μ 1) ∈ P`
  have hmem (φ μ : F →ₗ[C] C) : p φ * (p μ - algebraMap C R (μ 1)) ∈ P := by
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := C) P]
    intro x hx
    rw [map_mul, map_sub, AlgHom.commutes]
    rcases hpt x hx with h | h
    · rw [h φ, zero_mul]
    · rw [h μ, Algebra.algebraMap_self, RingHom.id_apply, sub_self, mul_zero]
  have hL (φ μ : F →ₗ[C] C) : coord φ z * (coord μ z - algebraMap C L (μ 1)) = 0 := by
    have := hmem φ μ
    rw [RingHom.mem_ker, map_mul, map_sub, AlgHom.commutes, hψp,
      hψp] at this
    exact this
  by_cases h0 : ∀ φ : F →ₗ[C] C, coord φ z = 0
  · exact Or.inl (eq_zero_of_forall_coord_eq_zero h0)
  · push Not at h0
    obtain ⟨φ, hφ⟩ := h0
    right
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_coord_eq_zero fun μ ↦ ?_
    rw [map_sub, coord_one]
    exact (mul_eq_zero.1 (hL φ μ)).resolve_left hφ

section Limit

open Filter Topology

variable {C : Type*} [NontriviallyNormedField C] [IsAlgClosed C]

local notation "Ĉ" => UniformSpace.Completion C

/-- **Limits of approximate idempotents.** Let `u : J → F` be a `C`-linearly independent family in
a field `F` over an algebraically closed normed field `C` (not necessarily complete), with
`1 = Σ cᵦ uᵦ`, and let `H ≠ 0` and a finite family `w` be such that `H uᵦ u_γ` and `H uᵦ` are
`C`-combinations of the `w` (coefficients `κ₂`, `κ₁`). If `aₙ : J → C` are Cauchy sequences whose
"idempotency defects" `Σ aᵦ a_γ κ₂ - Σ aᵦ κ₁` tend to `0` along every `w`-coordinate, then
`aₙ → ε c` for `ε = 0` or `ε = 1`. The limit is taken in the completion `Ĉ`; the limit element
`Σ Aᵦ ⊗ uᵦ` is an idempotent of `Ĉ ⊗[C] F`, hence `0` or `1`. -/
theorem exists_tendsto_of_approx_idempotent {F J T : Type*} [Field F] [Algebra C F] [Fintype J]
    [Fintype T] (u : J → F) (hli : LinearIndependent C u) (c : J → C)
    (hone : (1 : F) = ∑ β, c β • u β) (H : F) (hH : H ≠ 0) (w : T → F) (κ2 : J → J → T → C)
    (κ1 : J → T → C) (hy2 : ∀ β γ, H * (u β * u γ) = ∑ t, κ2 β γ t • w t)
    (hy1 : ∀ β, H * u β = ∑ t, κ1 β t • w t) (a : ℕ → J → C)
    (hcauchy : ∀ β, CauchySeq fun n ↦ a n β)
    (hsmall : ∀ t, Tendsto (fun n ↦ ∑ β, ∑ γ, a n β * a n γ * κ2 β γ t -
      ∑ β, a n β * κ1 β t) atTop (𝓝 0)) :
    ∃ ε : C, (ε = 0 ∨ ε = 1) ∧ ∀ β, Tendsto (fun n ↦ a n β) atTop (𝓝 (ε * c β)) := by
  classical
  have hcoe (x : C) : algebraMap C Ĉ x = (x : Ĉ) := rfl
  -- the limits in the completion
  choose A hA using fun β ↦ cauchySeq_tendsto_of_complete
    ((UniformSpace.Completion.uniformContinuous_coe C).comp_cauchySeq (hcauchy β))
  set G : T → (J → Ĉ) → Ĉ := fun t B ↦ ∑ β, ∑ γ, B β * B γ * algebraMap C Ĉ (κ2 β γ t) -
    ∑ β, B β * algebraMap C Ĉ (κ1 β t)
  have hG (t : T) : G t A = 0 := by
    have h1 : Tendsto (fun n ↦ G t fun β ↦ (a n β : Ĉ)) atTop (𝓝 (G t A)) :=
      (tendsto_finsetSum _ fun β _ ↦ tendsto_finsetSum _ fun γ _ ↦
        ((hA β).mul (hA γ)).mul_const _).sub (tendsto_finsetSum _ fun β _ ↦ (hA β).mul_const _)
    have h2 : Tendsto (fun n ↦ G t fun β ↦ (a n β : Ĉ)) atTop (𝓝 0) := by
      have := ((UniformSpace.Completion.continuous_coe C).tendsto 0).comp (hsmall t)
      rw [UniformSpace.Completion.coe_zero] at this
      refine this.congr fun n ↦ ?_
      simp only [Function.comp_apply, G, ← hcoe, _root_.map_sub, map_sum, map_mul]
    exact tendsto_nhds_unique h1 h2
  -- the limit is an idempotent of `Ĉ ⊗[C] F`
  set z : Ĉ ⊗[C] F := ∑ β, A β ⊗ₜ[C] u β
  have hz : IsIdempotentElem z := by
    have h := one_tmul_mul_sq_sub (C := C) A u H
    rw [sum_sub_sum_tmul_eq (C := C) A _ _ w κ2 κ1 hy2 hy1] at h
    simp only [show ∀ t, (∑ β, ∑ γ, A β * A γ * algebraMap C Ĉ (κ2 β γ t) -
      ∑ β, A β * algebraMap C Ĉ (κ1 β t)) = 0 from hG, TensorProduct.zero_tmul,
      Finset.sum_const_zero] at h
    have hu : ((1 : Ĉ) ⊗ₜ[C] H⁻¹) * ((1 : Ĉ) ⊗ₜ[C] H) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hH,
        Algebra.TensorProduct.one_def]
    have h2 := congrArg (((1 : Ĉ) ⊗ₜ[C] H⁻¹) * ·) h
    simp only [mul_zero, ← mul_assoc, hu, one_mul] at h2
    exact sub_eq_zero.1 h2
  -- coordinate functionals
  have hdual (β : J) : ∃ l : F →ₗ[C] C, ∀ γ, l (u γ) = if γ = β then 1 else 0 := by
    obtain ⟨l, hl⟩ := LinearMap.exists_extend ((Module.Basis.span hli).coord β)
    refine ⟨l, fun γ ↦ ?_⟩
    have : l (u γ) = (Module.Basis.span hli).coord β (Module.Basis.span hli γ) := by
      rw [← hl, Module.Basis.span_apply]
      rfl
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hcoord (l : F →ₗ[C] C) (β : J) (hl : ∀ γ, l (u γ) = if γ = β then 1 else 0) :
      coord l z = A β := by
    simp only [z, map_sum, coord_tmul, hl, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_eq_single β (fun γ _ hγ ↦ if_neg hγ) (fun h ↦ absurd (Finset.mem_univ β) h),
      if_pos rfl]
  obtain ⟨ε, hε, hAε⟩ : ∃ ε : C, (ε = 0 ∨ ε = 1) ∧ ∀ β, A β = ((ε * c β : C) : Ĉ) := by
    rcases eq_zero_or_eq_one_of_isIdempotentElem hz with h0 | h1
    · refine ⟨0, Or.inl rfl, fun β ↦ ?_⟩
      obtain ⟨l, hl⟩ := hdual β
      rw [← hcoord l β hl, h0, map_zero, zero_mul, UniformSpace.Completion.coe_zero]
    · refine ⟨1, Or.inr rfl, fun β ↦ ?_⟩
      obtain ⟨l, hl⟩ := hdual β
      rw [← hcoord l β hl, h1, coord_one, hone, map_sum, one_mul, hcoe]
      simp only [hl, map_smul, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single β (fun γ _ hγ ↦ if_neg hγ) (fun h ↦ absurd (Finset.mem_univ β) h),
        if_pos rfl]
  refine ⟨ε, hε, fun β ↦ ?_⟩
  have h := tendsto_iff_dist_tendsto_zero.1 ((hAε β) ▸ hA β)
  simp only [Function.comp_apply, UniformSpace.Completion.dist_eq] at h
  exact tendsto_iff_dist_tendsto_zero.2 h

end Limit

end TensorIdempotent

end SemistableReduction
