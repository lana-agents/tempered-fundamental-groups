/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspKummerTameCore

/-!
# The one-dimensional tame Kummer lemma at a point (S6)

Let `R` be a Noetherian `k`-algebra (`k` algebraically closed), `𝔪` a `k`-rational maximal
ideal of `R`, `s ∈ 𝔪` a regular element generating `𝔪` locally (`g s ∈ … `, the form of
`P1Three.exists_uniformizer`), and `C` a finite flat `R`-algebra such that at every prime `P` of `C`
over `𝔪` there are `π ∈ P` and `0 < e ∣ N` (`N` invertible in `k`) with `P C_P = π C_P` and
`s = unit · πᵉ` in `C_P` (tameness). Then (**`FormalKummer.exists_cuspLoc_of_tame`**)

  `R̂_𝔪 ⊗_R C ≃ₐ[R̂_𝔪] ∏ᵢ R̂_𝔪[t]/(t^{dᵢ} − s)`,   `0 < dᵢ ∣ N`,

which is literally the local input `Ψ j` of `FormalKummer.assembleCuspEquiv`
(`CuspLoc 𝔪 s j e = AdjoinRoot (X ^ e - C (algebraMap R (T 𝔪 j) s))`).

Proof: `T := R̂_𝔪` is local, complete, with maximal ideal `𝔪 T = (s)` (`g` is a unit in `T`) and
residue field `k`; `D := T ⊗_R C` is finite flat over `T` and complete (it is the completion of
the finite `R`-module `C`, `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`); a maximal
ideal `Q` of `D` lies over the prime `P = Q ∩ C` over `𝔪`, and `Q = P D + s D`, so the
uniformizer data at `P` give uniformizer data at `Q`. Conclude by
`FormalKummer.exists_algEquiv_pi_adjoinRoot`.
-/

universe u

open Polynomial IsLocalRing TensorProduct

namespace SemistableReduction

namespace FormalKummer

/-- **The one-dimensional tame Kummer lemma** (S6): the formal local form
`R̂_𝔪 ⊗_R C ≅ ∏ᵢ R̂_𝔪[t]/(t^{dᵢ} − s)` at a `k`-rational point `𝔪` with local parameter `s`,
for a finite flat `R`-algebra `C` which is tamely ramified over `𝔪` (explicit uniformizers `π` and
ramification indices `e ∣ N` at the primes over `𝔪`, `N` invertible in `k`). -/
theorem exists_cuspLoc_of_tame {k : Type*} {R C : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    [Algebra k R] [IsNoetherianRing R] [CommRing C] [Algebra R C] [Module.Finite R C]
    [Module.Flat R C] (𝔪 : Ideal R) [𝔪.IsMaximal]
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap k R)))
    {s : R} (hs : s ∈ 𝔪) (hsreg : IsSMulRegular R s)
    (hU : ∃ g ∉ 𝔪, ∀ r ∈ 𝔪, ∃ r', g * r = s * r')
    {N : ℕ} (hN : (N : k) ≠ 0)
    (hP : ∀ P ∈ 𝔪.primesOver C, ∃ (π : C) (e : ℕ), 0 < e ∧ e ∣ N ∧ π ∈ P ∧
      (∃ g ∉ P, ∀ x ∈ P, ∃ c, g * x = π * c) ∧
      (∃ a ∉ P, ∃ w ∉ P, w * algebraMap R C s = a * π ^ e)) :
    ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, 0 < d i) ∧ (∀ i, d i ∣ N) ∧
      Nonempty (AdicCompletion 𝔪 R ⊗[R] C ≃ₐ[AdicCompletion 𝔪 R]
        ∀ i, AdjoinRoot (X ^ d i - Polynomial.C (algebraMap R (AdicCompletion 𝔪 R) s))) := by
  have fg : 𝔪.FG := IsNoetherian.noetherian 𝔪
  set 𝔪h := 𝔪.map (algebraMap R (AdicCompletion 𝔪 R)) with h𝔪h
  haveI : IsAdicComplete 𝔪h (AdicCompletion 𝔪 R) := AdicCompletion.isAdicComplete_self 𝔪 fg
  haveI : 𝔪h.IsMaximal := AdicCompletion.isMaximal_map_of_le 𝔪 𝔪 le_rfl fg
  haveI := isLocalRing_of_isAdicComplete_maximal 𝔪h
  have hm : maximalIdeal (AdicCompletion 𝔪 R) = 𝔪h := (eq_maximalIdeal ‹_›).symm
  have hev (x : R) : AdicCompletion.evalOneₐ 𝔪 (algebraMap R _ x) = Ideal.Quotient.mk 𝔪 x :=
    RingHom.congr_fun (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk 𝔪) x
  have hmem (t : AdicCompletion 𝔪 R) : t ∈ 𝔪h ↔ AdicCompletion.evalOneₐ 𝔪 t = 0 := by
    rw [h𝔪h, ← AdicCompletion.ker_evalOneₐ_eq_map 𝔪 fg, RingHom.mem_ker]
    rfl
  -- every element of `T` is congruent to an element of `R`
  have hresT (t : AdicCompletion 𝔪 R) : ∃ r : R, t - algebraMap R _ r ∈ 𝔪h := by
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ 𝔪 t)
    exact ⟨r, by rw [hmem, map_sub, hev, hr, sub_self]⟩
  -- the residue field of `T` is `k`
  let ρ : k →+* AdicCompletion 𝔪 R := (algebraMap R _).comp (algebraMap k R)
  have hρ : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal (AdicCompletion 𝔪 R))).comp ρ) := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨r, hr⟩ := hresT t
    obtain ⟨c, hc⟩ := hres (Ideal.Quotient.mk 𝔪 r)
    refine ⟨c, ?_⟩
    change Ideal.Quotient.mk _ (algebraMap R _ (algebraMap k R c)) = _
    rw [Ideal.Quotient.eq, hm]
    have h1 : algebraMap k R c - r ∈ 𝔪 := Ideal.Quotient.eq.mp hc
    have : algebraMap R (AdicCompletion 𝔪 R) (algebraMap k R c) - t =
        algebraMap R _ (algebraMap k R c - r) - (t - algebraMap R _ r) := by
      rw [map_sub]
      ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_map_of_mem _ h1) hr
  -- `𝔪 T = (s)`
  have hgu (g : R) (hg : g ∉ 𝔪) : IsUnit (algebraMap R (AdicCompletion 𝔪 R) g) := by
    rw [← notMem_maximalIdeal, hm, hmem, hev]
    intro h
    exact hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hmax : maximalIdeal (AdicCompletion 𝔪 R) =
      Ideal.span {algebraMap R (AdicCompletion 𝔪 R) s} := by
    rw [hm]
    refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hs))
    rw [h𝔪h, Ideal.map_le_iff_le_comap]
    intro r hr
    obtain ⟨g, hg, hgr⟩ := hU
    obtain ⟨r', hr'⟩ := hgr r hr
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨↑(hgu g hg).unit⁻¹ * algebraMap R _ r', ?_⟩
    have h1 : algebraMap R (AdicCompletion 𝔪 R) g * algebraMap R _ r =
        algebraMap R _ s * algebraMap R _ r' := by
      rw [← map_mul, hr', map_mul]
    have h2 : ↑(hgu g hg).unit⁻¹ * algebraMap R (AdicCompletion 𝔪 R) g = 1 :=
      IsUnit.val_inv_mul _
    linear_combination (-(↑(hgu g hg).unit⁻¹ : AdicCompletion 𝔪 R)) * h1 +
      algebraMap R (AdicCompletion 𝔪 R) r * h2
  haveI : IsHausdorff (maximalIdeal (AdicCompletion 𝔪 R)) (AdicCompletion 𝔪 R) := by
    rw [hm]
    infer_instance
  have hsT : IsSMulRegular (AdicCompletion 𝔪 R) (algebraMap R (AdicCompletion 𝔪 R) s) :=
    hsreg.of_flat
  -- `T ⊗_R C` is complete
  haveI : IsAdicComplete ((maximalIdeal (AdicCompletion 𝔪 R)).map
      (algebraMap (AdicCompletion 𝔪 R) (AdicCompletion 𝔪 R ⊗[R] C)))
      (AdicCompletion 𝔪 R ⊗[R] C) := by
    rw [IsAdicComplete.map_algebraMap_iff, hm, h𝔪h, IsAdicComplete.map_algebraMap_iff]
    haveI : IsAdicComplete 𝔪 (AdicCompletion 𝔪 C) := AdicCompletion.isAdicComplete fg
    exact isAdicComplete_of_linearEquiv 𝔪
      ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian 𝔪 C).restrictScalars R)
  -- the uniformizer data at the maximal ideals of `T ⊗_R C`
  let ι : C →ₐ[R] AdicCompletion 𝔪 R ⊗[R] C := Algebra.TensorProduct.includeRight
  have hsD : algebraMap (AdicCompletion 𝔪 R) (AdicCompletion 𝔪 R ⊗[R] C)
      (algebraMap R (AdicCompletion 𝔪 R) s) = ι (algebraMap R C s) := by
    rw [ι.commutes]
    exact (IsScalarTower.algebraMap_apply R (AdicCompletion 𝔪 R) _ s).symm
  have hdec (x : AdicCompletion 𝔪 R ⊗[R] C) : ∃ (c₀ : C) (y : AdicCompletion 𝔪 R ⊗[R] C),
      x = ι c₀ + algebraMap (AdicCompletion 𝔪 R) _ (algebraMap R _ s) * y := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by rw [map_zero, mul_zero, add_zero]⟩
    | tmul t c =>
      obtain ⟨r, hr⟩ := hresT t
      rw [← hm, hmax, Ideal.mem_span_singleton'] at hr
      obtain ⟨z, hz⟩ := hr
      refine ⟨r • c, z ⊗ₜ c, ?_⟩
      have ht : t = algebraMap R (AdicCompletion 𝔪 R) r + algebraMap R _ s * z := by
        linear_combination -hz
      rw [ht, add_tmul]
      congr 1
      · change _ = (1 : AdicCompletion 𝔪 R) ⊗ₜ[R] (r • c)
        rw [← smul_tmul, Algebra.algebraMap_eq_smul_one]
      · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add x y hx hy =>
      obtain ⟨c₀, y₀, hx⟩ := hx
      obtain ⟨c₁, y₁, hy⟩ := hy
      exact ⟨c₀ + c₁, y₀ + y₁, by rw [hx, hy, map_add]; ring⟩
  have hQ : ∀ Q : Ideal (AdicCompletion 𝔪 R ⊗[R] C), Q.IsMaximal → ∃ (π : _) (e : ℕ),
      0 < e ∧ e ∣ N ∧ π ∈ Q ∧ (∃ g ∉ Q, ∀ x ∈ Q, ∃ c, g * x = π * c) ∧
      ∃ a ∉ Q, ∃ w ∉ Q, w * algebraMap (AdicCompletion 𝔪 R) _ (algebraMap R _ s) =
        a * π ^ e := by
    intro Q hQ
    have hJQ : (maximalIdeal (AdicCompletion 𝔪 R)).map
        (algebraMap (AdicCompletion 𝔪 R) (AdicCompletion 𝔪 R ⊗[R] C)) ≤ Q := fun x hx ↦
      Ideal.mem_sInf.mp (IsAdicComplete.le_jacobson_bot _ hx) ⟨bot_le, hQ⟩
    have hsQ : ι (algebraMap R C s) ∈ Q := by
      rw [← hsD]
      exact hJQ (Ideal.mem_map_of_mem _ (hmax ▸ Ideal.mem_span_singleton_self _))
    haveI : (Q.comap ι).IsPrime := Ideal.comap_isPrime ι Q
    have hlies : 𝔪 = (Q.comap ι).comap (algebraMap R C) := by
      refine Ideal.IsMaximal.eq_of_le ‹_› (Ideal.comap_isPrime (algebraMap R C) _).ne_top ?_
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap, ι.commutes,
        IsScalarTower.algebraMap_apply R (AdicCompletion 𝔪 R)]
      exact hJQ (Ideal.mem_map_of_mem _ (hm ▸ Ideal.mem_map_of_mem _ hr))
    obtain ⟨π, e, he, heN, hπP, ⟨g, hgP, hg⟩, a, haP, w, hwP, haw⟩ :=
      hP (Q.comap ι) ⟨inferInstance, ⟨hlies⟩⟩
    refine ⟨ι π, e, he, heN, hπP, ⟨ι g * ι w, fun h ↦ ?_, fun x hx ↦ ?_⟩, ι a, haP, ι w, hwP,
      ?_⟩
    · exact ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hgP hwP)
    · obtain ⟨c₀, y, rfl⟩ := hdec x
      have hc₀ : c₀ ∈ Q.comap ι := by
        rw [Ideal.mem_comap]
        have := Ideal.sub_mem _ hx (Ideal.mul_mem_right y _ (hsD ▸ hsQ))
        rwa [add_sub_cancel_right] at this
      obtain ⟨c₁, hc₁⟩ := hg c₀ hc₀
      have h1 : ι g * ι c₀ = ι π * ι c₁ := by rw [← map_mul, hc₁, map_mul]
      have h2 : ι w * ι (algebraMap R C s) = ι a * ι π ^ e := by
        rw [← map_mul, haw, map_mul, map_pow]
      have h3 : ι π ^ e = ι π * ι π ^ (e - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel he]
      refine ⟨ι w * ι c₁ + ι g * ι a * ι π ^ (e - 1) * y, ?_⟩
      rw [hsD]
      linear_combination ι w * h1 + ι g * y * h2 + ι g * ι a * y * h3
    · rw [hsD, ← map_mul, haw, map_mul, map_pow]
  exact exists_algEquiv_pi_adjoinRoot ρ hρ hmax hsT hN hQ

end FormalKummer

end SemistableReduction
