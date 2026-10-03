/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.FunctionField
import Mathlib.FieldTheory.SeparableClosure

/-!
# Finiteness of integral closures in function fields over perfect fields

Blueprint §9.9, S7.7. Let `k` be a perfect field and `L` a finite extension of `k(X)`. Then the
integral closure of `k[X]` in `L` is a finite `k[X]`-module (`isNoetherian_integralClosure`), also
when `L / k(X)` is inseparable (the wild case of the residue curves).

Proof: let `L_s` be the separable closure of `k(X)` in `L`; `L / L_s` is purely inseparable with
some exponent, so `z ↦ z^q` maps the integral closure `B` of `k[X]` in `L` into the integral
closure `B_s` of `k[X]` in `L_s`, which is finite (Mathlib, separable case). The map is linear for
the action of `k[X]` on `B_s` twisted by `f ↦ f^q`, for which `B_s` is still finite because `k` is
perfect (`exists_sum_pow_mul_X_pow`: every polynomial is `Σ_{j < q} c_j^q Xʲ`).
-/

open Polynomial

namespace SemistableReduction

namespace CurveIntegralClosure

section Decomposition

variable {k : Type*} [Field k] (p : ℕ) [ExpChar k p] [PerfectField k]

/-- Over a perfect field of exponential characteristic `p`, every polynomial is
`Σ_{j < q} c_j^q Xʲ` (`q = pᵉ`). -/
theorem exists_sum_pow_mul_X_pow (e : ℕ) (g : k[X]) :
    ∃ c : Fin (p ^ e) → k[X], g = ∑ j, iterateFrobenius k[X] p e (c j) * X ^ (j : ℕ) := by
  have hq : 0 < p ^ e := pow_pos (expChar_pos k p) e
  induction g using Polynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨c, hc⟩ := hf
    obtain ⟨c', hc'⟩ := hg
    refine ⟨c + c', ?_⟩
    rw [hc, hc', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Pi.add_apply, map_add, add_mul]
  | monomial n a =>
    set a' := (iterateFrobeniusEquiv k p e).symm a
    have ha' : iterateFrobenius k p e a' = a := by
      rw [← coe_iterateFrobeniusEquiv, RingEquiv.apply_symm_apply]
    set j₀ : Fin (p ^ e) := ⟨n % p ^ e, Nat.mod_lt _ hq⟩
    refine ⟨fun j ↦ if j = j₀ then Polynomial.C a' * X ^ (n / p ^ e) else 0, ?_⟩
    rw [Finset.sum_eq_single j₀ (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp only [↓reduceIte]
    rw [iterateFrobenius_def] at ha'
    rw [iterateFrobenius_def, mul_pow, ← C_pow, ← pow_mul, ha', mul_assoc, ← pow_add,
      C_mul_X_pow_eq_monomial]
    have hn : n / p ^ e * p ^ e + n % p ^ e = n := Nat.div_add_mod' n (p ^ e)
    simp only [j₀, hn]

end Decomposition

section Twist

/-- `L` with the `k[X]`-action twisted by `f ↦ f^{pᵉ}`. -/
@[nolint unusedArguments]
def Tw (k : Type*) [Field k] (_p _e : ℕ) (L : Type*) : Type _ := L

variable (k : Type*) [Field k] (p : ℕ) [ExpChar k p] (e : ℕ) (L : Type*)

variable {L} [Field L] [Algebra k[X] L]

instance : AddCommGroup (Tw k p e L) := inferInstanceAs (AddCommGroup L)

noncomputable instance : Module k[X] (Tw k p e L) :=
  Module.compHom L (iterateFrobenius k[X] p e)

/-- The identity `L → Tw L`. -/
def toTw : L ≃+ Tw k p e L := AddEquiv.refl L

variable {k p e}

lemma smul_toTw (f : k[X]) (z : L) :
    f • toTw k p e z = toTw k p e (iterateFrobenius k[X] p e f • z) := rfl

end Twist

variable {k : Type*} [Field k] [PerfectField k] {L : Type*} [Field L] [Algebra (RatFunc k) L]
  [Algebra k[X] L] [IsScalarTower k[X] (RatFunc k) L] [FiniteDimensional (RatFunc k) L]

/-- **Finiteness of the integral closure** of `k[X]` in a finite extension `L` of `k(X)`, for
`k` perfect. -/
theorem isNoetherian_integralClosure : IsNoetherian k[X] (integralClosure k[X] L) := by
  classical
  obtain ⟨p, hp⟩ := ExpChar.exists k
  haveI : ExpChar k[X] p := expChar_of_injective_algebraMap (algebraMap k k[X]).injective p
  haveI : ExpChar L p := expChar_of_injective_ringHom
    ((algebraMap k[X] L).comp (algebraMap k k[X])).injective p
  -- the separable closure
  set Ks := separableClosure (RatFunc k) L
  letI : Algebra k[X] Ks :=
    ((algebraMap (RatFunc k) Ks).comp (algebraMap k[X] (RatFunc k))).toAlgebra
  haveI : IsScalarTower k[X] (RatFunc k) Ks := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k[X] Ks L := IsScalarTower.of_algebraMap_eq fun f ↦ by
    rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) L]
    rfl
  haveI : IsNoetherian k[X] (integralClosure k[X] Ks) :=
    IsIntegralClosure.isNoetherian k[X] (RatFunc k) Ks (integralClosure k[X] Ks)
  -- generators of the integral closure in `Ks`, viewed in `L`
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (R := k[X]) (⊤ : Submodule k[X]
    (integralClosure k[X] Ks)))
  set G' : Finset L := G.image fun g ↦ (((g : integralClosure k[X] Ks) : Ks) : L)
  have hGs (z : Ks) (hz : IsIntegral k[X] z) : (z : L) ∈ Submodule.span k[X] (G' : Set L) := by
    have hmem : (⟨z, hz⟩ : integralClosure k[X] Ks) ∈ Submodule.span k[X] (G : Set _) := by
      rw [hG]; trivial
    have := Submodule.mem_map_of_mem (f := (IsScalarTower.toAlgHom k[X] Ks L).toLinearMap.comp
      (integralClosure k[X] Ks).val.toLinearMap) hmem
    rw [Submodule.map_span] at this
    have hset : ((IsScalarTower.toAlgHom k[X] Ks L).toLinearMap.comp
        (integralClosure k[X] Ks).val.toLinearMap) '' (G : Set _) = (G' : Set L) := by
      simp only [G', Finset.coe_image]
      rfl
    rw [hset] at this
    exact this
  -- the exponent of `L / Ks`
  haveI : IsPurelyInseparable Ks L := separableClosure.isPurelyInseparable (RatFunc k) L
  set e := IsPurelyInseparable.exponent Ks L
  have hexp (z : L) : z ^ p ^ e ∈ (algebraMap Ks L).range := by
    have := IsPurelyInseparable.exponent_def Ks z
    rwa [ringExpChar.eq Ks p] at this
  -- the twisted finite module
  set S : Set (Tw k p e L) := (fun z : (Fin (p ^ e)) × G' ↦
    toTw k p e ((X : k[X]) ^ (z.1 : ℕ) • ((z.2 : L)))) '' Set.univ
  set N : Submodule k[X] (Tw k p e L) := Submodule.span k[X] S
  have hNfg : N.FG := ⟨(Set.toFinite S).toFinset, by simp [N]⟩
  haveI : IsNoetherian k[X] N := isNoetherian_of_fg_of_noetherian N hNfg
  -- the Frobenius map into `N`
  have hmapN (b : integralClosure k[X] L) : toTw k p e ((b : L) ^ p ^ e) ∈ N := by
    obtain ⟨z, hz⟩ := hexp b
    have hzi : IsIntegral k[X] z := by
      have hb : IsIntegral k[X] ((b : L) ^ p ^ e) := b.2.pow _
      rw [← hz] at hb
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom k[X] Ks L)
        (algebraMap Ks L).injective).1 hb
    have hspan := hGs z hzi
    change algebraMap Ks L z ∈ _ at hspan
    rw [hz] at hspan
    obtain ⟨f, -, hf⟩ := (Submodule.mem_span_finset).1 hspan
    rw [← hf, map_sum]
    refine Submodule.sum_mem _ fun g hg ↦ ?_
    obtain ⟨c, hc⟩ := exists_sum_pow_mul_X_pow p e (f g)
    rw [hc, Finset.sum_smul, map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    have : toTw k p e ((iterateFrobenius k[X] p e (c j) * (X : k[X]) ^ (j : ℕ)) • g) =
        c j • toTw k p e ((X : k[X]) ^ (j : ℕ) • g) := by
      rw [smul_toTw, mul_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, ⟨g, hg⟩), trivial, rfl⟩)
  -- the injective linear map
  let φ : integralClosure k[X] L →ₗ[k[X]] N :=
    { toFun := fun b ↦ ⟨toTw k p e ((b : L) ^ p ^ e), hmapN b⟩
      map_add' := fun a b ↦ by
        apply Subtype.ext
        simp only [Subalgebra.coe_add, Submodule.coe_add]
        rw [add_pow_expChar_pow, map_add]
      map_smul' := fun f b ↦ by
        apply Subtype.ext
        simp only [Subalgebra.coe_smul, RingHom.id_apply, Submodule.coe_smul]
        rw [smul_toTw, Algebra.smul_def, Algebra.smul_def, mul_pow, ← map_pow,
          ← iterateFrobenius_def] }
  refine isNoetherian_of_injective φ fun a b h ↦ ?_
  have h' : (a : L) ^ p ^ e = (b : L) ^ p ^ e := congrArg (fun y : N ↦ ((y : Tw k p e L) : L)) h
  rw [← iterateFrobenius_def, ← iterateFrobenius_def] at h'
  exact Subtype.ext ((iterateFrobenius L p e).injective h')

end CurveIntegralClosure

end SemistableReduction
