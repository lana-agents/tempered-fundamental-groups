/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspKummerTameLocal
import TemperedFundamentalGroups.SemistableReduction.CuspKummerTameSplit
import TemperedFundamentalGroups.SemistableReduction.FormalCuspEtale

/-!
# The tame Kummer form of a finite flat algebra over a complete DVR-like ring (S6, core)

Let `T` be a local ring, `(s)`-adically Hausdorff with `𝔪_T = (s)`, `s` regular, whose residue
field is a quotient of an algebraically closed field `k` with `(N : k) ≠ 0`, and let `D` be a
finite flat `𝔪_T D`-adically complete `T`-algebra such that at every maximal ideal `Q` of `D`
there are `π ∈ Q`, `0 < e ∣ N` with `Q D_Q = π D_Q` and `s = unit · πᵉ` in `D_Q` (all checked by
elements). Then (**`exists_algEquiv_pi_adjoinRoot`**)

  `D ≃ₐ[T] ∏ᵢ T[Y]/(Y^{dᵢ} − s)`,   `0 < dᵢ ∣ N`.

Proof: `D ≅ ∏_Q D ⧸ (1 − ε_Q)` with local factors (`exists_idempotents_maximalSpectrum`); every
factor is finite, flat (a retract of `D`), complete (a retract of `D`), its residue field is `k`
(`IsAlgClosed.ringHom_bijective_of_isIntegral`) and its maximal ideal is `(π)`, so it is
`T[Y]/(Yᵉ − s)` by `nonempty_algEquiv_adjoinRoot`.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

namespace FormalKummer

section Factor

variable {T D : Type*} [CommRing T] [CommRing D] [Algebra T D] {ε : D}
  (hε : IsIdempotentElem ε)
include hε

/-- Multiplication by `ε` on the factor `D ⧸ (1 − ε)`: a `T`-linear section of the projection. -/
noncomputable def factorIncl : (D ⧸ Ideal.span {1 - ε}) →ₗ[T] D :=
  ((Ideal.span {1 - ε}).liftQ (LinearMap.mulLeft D ε) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.mulLeft_apply, mul_sub, mul_one, hε.eq, sub_self])).restrictScalars T

theorem factorIncl_mk (d : D) :
    factorIncl (T := T) hε (Ideal.Quotient.mk _ d) = ε * d := rfl

theorem mk_factorIncl (x : D ⧸ Ideal.span {1 - ε}) :
    Ideal.Quotient.mk _ (factorIncl (T := T) hε x) = x := by
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [factorIncl_mk, Ideal.Quotient.eq]
  refine Ideal.mem_span_singleton'.mpr ⟨-d, ?_⟩
  ring

theorem factorIncl_injective : Function.Injective (factorIncl (T := T) hε) :=
  Function.LeftInverse.injective (mk_factorIncl hε)

/-- A direct factor of a flat algebra is flat. -/
theorem flat_factor [Module.Flat T D] : Module.Flat T (D ⧸ Ideal.span {1 - ε}) :=
  Module.Flat.of_retract (factorIncl hε) (Ideal.Quotient.mkₐ T _).toLinearMap
    (LinearMap.ext fun x ↦ mk_factorIncl hε x)

/-- A direct factor of a complete algebra is complete. -/
theorem isAdicComplete_factor (I : Ideal T) [IsAdicComplete (I.map (algebraMap T D)) D] :
    IsAdicComplete (I.map (algebraMap T (D ⧸ Ideal.span {1 - ε}))) (D ⧸ Ideal.span {1 - ε}) := by
  haveI : IsAdicComplete I D := (IsAdicComplete.map_algebraMap_iff _ _).mp ‹_›
  refine (IsAdicComplete.map_algebraMap_iff _ _).mpr ?_
  haveI := isHausdorff_of_injective I (factorIncl hε) (factorIncl_injective hε)
  haveI := CompleteFinite.isPrecomplete_of_surjective I
    (Ideal.Quotient.mkₐ T (Ideal.span {1 - ε})).toLinearMap
    (fun x ↦ Ideal.Quotient.mk_surjective x)
  exact { toIsHausdorff := ‹_›, toIsPrecomplete := ‹_› }

end Factor

/-- `N` is invertible in `T` if it is non-zero in the residue field `k`. -/
theorem isUnit_natCast_of_residue {k T : Type*} [Field k] [CommRing T] [IsLocalRing T]
    (ρ : k →+* T) {N : ℕ} (hN : (N : k) ≠ 0) : IsUnit (N : T) := by
  rw [← notMem_maximalIdeal]
  intro h
  letI := Ideal.Quotient.field (maximalIdeal T)
  apply hN
  apply ((Ideal.Quotient.mk (maximalIdeal T)).comp ρ).injective
  rw [map_zero, RingHom.comp_apply, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
  exact h

section Core

variable {k T : Type*} [Field k] [IsAlgClosed k] [CommRing T] [IsLocalRing T]
  (ρ : k →+* T) (hρ : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal T)).comp ρ))
include hρ

/-- `N`-th roots modulo `𝔪_T`. -/
theorem exists_pow_sub_mem_of_residue {N : ℕ} (hN : (N : k) ≠ 0) (t : T) :
    ∃ t' : T, t' ^ N - t ∈ maximalIdeal T := by
  obtain ⟨c, hc⟩ := hρ (Ideal.Quotient.mk _ t)
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hN0)
  refine ⟨ρ c', ?_⟩
  rw [← Ideal.Quotient.eq, ← map_pow, hc']
  exact hc

/-- **The residue fields of a finite `T`-algebra are `k`**. -/
theorem exists_sub_mem_of_residue {D : Type*} [CommRing D] [Algebra T D] [Module.Finite T D]
    (Q : Ideal D) [Q.IsMaximal] (hJQ : (maximalIdeal T).map (algebraMap T D) ≤ Q) (d : D) :
    ∃ t : T, d - algebraMap T D t ∈ Q := by
  letI := Ideal.Quotient.field (maximalIdeal T)
  let e : k ≃+* T ⧸ maximalIdeal T := RingEquiv.ofBijective _
    ⟨((Ideal.Quotient.mk (maximalIdeal T)).comp ρ).injective, hρ⟩
  let h : T →+* k := e.symm.toRingHom.comp (Ideal.Quotient.mk _)
  let g : k →+* D ⧸ Q := (Ideal.Quotient.mk Q).comp ((algebraMap T D).comp ρ)
  have hgh : g.comp h = (Ideal.Quotient.mk Q).comp (algebraMap T D) := by
    ext t
    have h1 : Ideal.Quotient.mk (maximalIdeal T) (ρ (h t)) = Ideal.Quotient.mk _ t := by
      change e (e.symm _) = _
      rw [RingEquiv.apply_symm_apply]
    rw [Ideal.Quotient.eq] at h1
    change Ideal.Quotient.mk Q (algebraMap T D (ρ (h t))) = Ideal.Quotient.mk Q (algebraMap T D t)
    rw [Ideal.Quotient.eq, ← map_sub]
    exact hJQ (Ideal.mem_map_of_mem _ h1)
  have hint : g.IsIntegral := by
    intro x
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hpd⟩ := Algebra.IsIntegral.isIntegral (R := T) d
    refine ⟨p.map h, hp.map h, ?_⟩
    rw [eval₂_map, hgh, ← hom_eval₂, hpd, map_zero]
  obtain ⟨c, hc⟩ := (IsAlgClosed.ringHom_bijective_of_isIntegral g hint).2
    (Ideal.Quotient.mk Q d)
  refine ⟨ρ c, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact hc.symm

end Core

section Assemble

variable {T D : Type*} [CommRing T] [IsLocalRing T] [IsHausdorff (maximalIdeal T) T]
  [CommRing D] [Algebra T D] [Module.Finite T D] [Module.Flat T D]
  [IsAdicComplete ((maximalIdeal T).map (algebraMap T D)) D]
  {s : T} (hmax : maximalIdeal T = Ideal.span {s}) (hs : IsSMulRegular T s)
  {N : ℕ} (hNu : IsUnit (N : T)) (hroot : ∀ t : T, ∃ t' : T, t' ^ N - t ∈ maximalIdeal T)
include hmax hs hNu hroot

/-- **One local factor**: `D ⧸ (1 − ε) ≃ T[Y]/(Yᵉ − s)` if `Q` is the only maximal ideal avoiding
the idempotent `ε` and `(π, e)` are uniformizer data at `Q`. -/
theorem exists_factor_equiv {ε : D} (hε : IsIdempotentElem ε) (Q : Ideal D) [Q.IsMaximal]
    (hQε : ε ∉ Q) (huniq : ∀ Q' : Ideal D, Q'.IsMaximal → ε ∉ Q' → Q' = Q)
    (hres : ∀ d : D, ∃ t : T, d - algebraMap T D t ∈ Q)
    (hQ : ∃ (π : D) (e : ℕ), 0 < e ∧ e ∣ N ∧ π ∈ Q ∧
      (∃ g ∉ Q, ∀ x ∈ Q, ∃ c, g * x = π * c) ∧
      ∃ a ∉ Q, ∃ w ∉ Q, w * algebraMap T D s = a * π ^ e) :
    ∃ e : ℕ, 0 < e ∧ e ∣ N ∧
      Nonempty (AdjoinRoot (X ^ e - C s) ≃ₐ[T] D ⧸ Ideal.span {1 - ε}) := by
  haveI := isLocalRing_quotient_one_sub hε Q hQε huniq
  have hmB := maximalIdeal_quotient_one_sub hε Q hQε
  have hle : Ideal.span {1 - ε} ≤ Q := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact one_sub_mem_of_notMem hε hQε
  have hmem (d : D) : Ideal.Quotient.mk (Ideal.span {1 - ε}) d ∈
      maximalIdeal (D ⧸ Ideal.span {1 - ε}) ↔ d ∈ Q := by
    rw [hmB, Ideal.mem_quotient_iff_mem hle]
  have hunit (x : D) (hx : x ∉ Q) : IsUnit (Ideal.Quotient.mk (Ideal.span {1 - ε}) x) := by
    rw [← notMem_maximalIdeal, hmem]
    exact hx
  haveI : Module.Finite T (D ⧸ Ideal.span {1 - ε}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ T _).toLinearMap Ideal.Quotient.mk_surjective
  haveI := flat_factor (T := T) hε
  haveI := isAdicComplete_factor hε (maximalIdeal T)
  obtain ⟨π, e, he, ⟨m, hm⟩, hπQ, ⟨g, hgQ, hg⟩, a, haQ, w, hwQ, haw⟩ := hQ
  have heu : IsUnit (e : T) := by
    rw [hm, Nat.cast_mul] at hNu
    exact isUnit_of_mul_isUnit_left hNu
  have hroot' (t : T) : ∃ t' : T, t' ^ e - t ∈ maximalIdeal T := by
    obtain ⟨t', ht'⟩ := hroot t
    refine ⟨t' ^ m, ?_⟩
    rw [← pow_mul, mul_comm, ← hm]
    exact ht'
  have hresB (b : D ⧸ Ideal.span {1 - ε}) : ∃ t : T,
      b - algebraMap T _ t ∈ maximalIdeal (D ⧸ Ideal.span {1 - ε}) := by
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨t, ht⟩ := hres d
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.mk_algebraMap, ← map_sub, hmem]
    exact ht
  set mk := Ideal.Quotient.mk (Ideal.span {1 - ε}) with hmk
  have hπ : maximalIdeal (D ⧸ Ideal.span {1 - ε}) = Ideal.span {mk π} := by
    refine le_antisymm (fun x hx ↦ ?_) ((Ideal.span_singleton_le_iff_mem _).mpr
      ((hmem π).mpr hπQ))
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, hc⟩ := hg d ((hmem d).mp hx)
    refine Ideal.mem_span_singleton'.mpr ⟨↑(hunit g hgQ).unit⁻¹ * mk c, ?_⟩
    have h1 : mk g * mk d = mk π * mk c := by rw [← map_mul, hc, map_mul]
    have h2 : ↑(hunit g hgQ).unit⁻¹ * mk g = 1 := IsUnit.val_inv_mul _
    linear_combination (↑(hunit g hgQ).unit⁻¹ : D ⧸ Ideal.span {1 - ε}) * h1.symm + mk d * h2
  have hu : IsUnit (mk a * ↑(hunit w hwQ).unit⁻¹) :=
    (hunit a haQ).mul (Units.isUnit _)
  have hsπ : algebraMap T (D ⧸ Ideal.span {1 - ε}) s =
      mk a * ↑(hunit w hwQ).unit⁻¹ * mk π ^ e := by
    have h1 : mk w * algebraMap T (D ⧸ Ideal.span {1 - ε}) s = mk a * mk π ^ e := by
      rw [← Ideal.Quotient.mk_algebraMap, ← map_mul, haw, map_mul, map_pow]
    have h2 : ↑(hunit w hwQ).unit⁻¹ * mk w = 1 := IsUnit.val_inv_mul _
    linear_combination (↑(hunit w hwQ).unit⁻¹ : D ⧸ Ideal.span {1 - ε}) * h1 -
      algebraMap T (D ⧸ Ideal.span {1 - ε}) s * h2
  exact ⟨e, he, ⟨m, hm⟩, nonempty_algEquiv_adjoinRoot hmax hs he heu hroot' hresB hπ hu hsπ⟩

/-- **The tame Kummer form of a complete finite flat algebra** (abstract form; residue fields
and roots given by hypotheses). -/
theorem exists_algEquiv_pi_adjoinRoot_of_roots
    (hres : ∀ Q : Ideal D, Q.IsMaximal → ∀ d : D, ∃ t : T, d - algebraMap T D t ∈ Q)
    (hQ : ∀ Q : Ideal D, Q.IsMaximal → ∃ (π : D) (e : ℕ), 0 < e ∧ e ∣ N ∧ π ∈ Q ∧
      (∃ g ∉ Q, ∀ x ∈ Q, ∃ c, g * x = π * c) ∧
      ∃ a ∉ Q, ∃ w ∉ Q, w * algebraMap T D s = a * π ^ e) :
    ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, 0 < d i) ∧ (∀ i, d i ∣ N) ∧
      Nonempty (D ≃ₐ[T] ∀ i, AdjoinRoot (X ^ d i - C s)) := by
  set J := (maximalIdeal T).map (algebraMap T D) with hJ
  have hJQ (Q : Ideal D) (hQ : Q.IsMaximal) : J ≤ Q := fun x hx ↦
    Ideal.mem_sInf.mp (IsAdicComplete.le_jacobson_bot J hx) ⟨bot_le, hQ⟩
  letI := Ideal.Quotient.field (maximalIdeal T)
  haveI : Module.Finite T (D ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ T _).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (T ⧸ maximalIdeal T) (D ⧸ J) :=
    Module.Finite.of_restrictScalars_finite T _ _
  haveI : IsArtinianRing (D ⧸ J) := IsArtinianRing.of_finite (T ⧸ maximalIdeal T) _
  have hcm (Q : Ideal D) (hQ : Q.IsMaximal) :
      (Q.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr (hJQ Q hQ)]
  haveI : Finite (MaximalSpectrum D) := by
    refine Finite.of_injective (β := PrimeSpectrum (D ⧸ J)) (fun Q ↦ ⟨Q.asIdeal.map
      (Ideal.Quotient.mk J), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hJQ Q.asIdeal Q.isMaximal)⟩) ?_
    intro Q Q' h
    have h' := congrArg (fun P : PrimeSpectrum (D ⧸ J) ↦ P.asIdeal.comap (Ideal.Quotient.mk J)) h
    simp only [hcm Q.asIdeal Q.isMaximal, hcm Q'.asIdeal Q'.isMaximal] at h'
    exact MaximalSpectrum.ext h'
  haveI := Fintype.ofFinite (MaximalSpectrum D)
  obtain ⟨ε, hε, hεQ⟩ := exists_idempotents_maximalSpectrum J
  have hfac (Q : MaximalSpectrum D) : ∃ e : ℕ, 0 < e ∧ e ∣ N ∧
      Nonempty (AdjoinRoot (X ^ e - C s) ≃ₐ[T] D ⧸ Ideal.span {1 - ε Q}) := by
    have hQε : ε Q ∉ Q.asIdeal := fun h ↦ (hεQ Q Q).mp h rfl
    have huniq (Q' : Ideal D) (hQ' : Q'.IsMaximal) (h : ε Q ∉ Q') : Q' = Q.asIdeal := by
      have := (hεQ Q ⟨Q', hQ'⟩).not.mp h
      rw [not_not] at this
      rw [this]
    exact exists_factor_equiv hmax hs hNu hroot (hε.idem Q) Q.asIdeal hQε huniq
      (hres Q.asIdeal Q.isMaximal) (hQ Q.asIdeal Q.isMaximal)
  choose e he heN Φ using hfac
  let Ψ : D ≃ₐ[T] ∀ Q : MaximalSpectrum D, D ⧸ Ideal.span {1 - ε Q} :=
    AlgEquiv.ofBijective (AlgHom.pi fun Q ↦ Ideal.Quotient.mkₐ T _) hε.bijective_pi
  let σ := Fintype.equivFin (MaximalSpectrum D)
  exact ⟨Fintype.card (MaximalSpectrum D), fun i ↦ e (σ.symm i), fun i ↦ he _, fun i ↦ heN _,
    ⟨Ψ.trans ((AlgEquiv.piCongrRight fun Q ↦ (Φ Q).some.symm).trans
      (AlgEquiv.piCongrLeft' T (fun Q ↦ AdjoinRoot (X ^ e Q - C s)) σ))⟩⟩

end Assemble

/-- **The tame Kummer form of a complete finite flat algebra over a complete DVR-like ring**
with residue field a quotient of an algebraically closed field `k`. -/
theorem exists_algEquiv_pi_adjoinRoot {k T D : Type*} [Field k] [IsAlgClosed k] [CommRing T]
    [IsLocalRing T] [IsHausdorff (maximalIdeal T) T] [CommRing D] [Algebra T D]
    [Module.Finite T D] [Module.Flat T D]
    [IsAdicComplete ((maximalIdeal T).map (algebraMap T D)) D]
    (ρ : k →+* T) (hρ : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal T)).comp ρ))
    {s : T} (hmax : maximalIdeal T = Ideal.span {s}) (hs : IsSMulRegular T s)
    {N : ℕ} (hN : (N : k) ≠ 0)
    (hQ : ∀ Q : Ideal D, Q.IsMaximal → ∃ (π : D) (e : ℕ), 0 < e ∧ e ∣ N ∧ π ∈ Q ∧
      (∃ g ∉ Q, ∀ x ∈ Q, ∃ c, g * x = π * c) ∧
      ∃ a ∉ Q, ∃ w ∉ Q, w * algebraMap T D s = a * π ^ e) :
    ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, 0 < d i) ∧ (∀ i, d i ∣ N) ∧
      Nonempty (D ≃ₐ[T] ∀ i, AdjoinRoot (X ^ d i - C s)) :=
  exists_algEquiv_pi_adjoinRoot_of_roots hmax hs (isUnit_natCast_of_residue ρ hN)
    (exists_pow_sub_mem_of_residue ρ hρ hN)
    (fun Q _ d ↦ exists_sub_mem_of_residue ρ hρ Q (fun x hx ↦
      Ideal.mem_sInf.mp (IsAdicComplete.le_jacobson_bot _ hx) ⟨bot_le, ‹_›⟩) d) hQ

end FormalKummer

end SemistableReduction
