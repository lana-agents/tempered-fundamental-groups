/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerNode

/-!
# Maps into a Kummer node factor are balanced (MR12 I5(b), generic core)

Let `KNF = N ⊗_{O[u,v]/(uv − c^d)} O[w, z]/(wz − c)` be a Kummer node factor over a smooth algebra
`N` of the node (`KummerNodeFactor`), `O` an integrally closed domain and `c ≠ 0`. If `σ, τ ∈ KNF`
are supported on an idempotent `ε` and satisfy

  `σ^e = ε w^d`,  `σ τ = ε (w z)^D`  (`d = e D`)

(the images of the coordinates `w₀, z₀` of a Kummer node `w₀ z₀ = c^D`, `w₀^e = u`, under a map
of Kummer node factors), then (**`KummerNodeFactor.exists_twist`**) there is `α ∈ KNF` with
`α^e = 1`, `σ = ε α w^D` and `τ = ε α^{e − 1} z^D`: the twists of the two branches are inverse
to each other. This is the balance condition of the special-fibre normal form (`NodeHom.Balanced`)
before reduction.

Proof: in the Kummer factor `N ⊗ Frac(O[w,z]/(wz − c))`, where `w` is invertible,
`α₀ = σ w^{−D} + (1 − ε)` satisfies `α₀^e = 1`; it is integral over `N`, hence lies in `KNF`
(normalisation commutes with smooth base change, `kummerFactorEquiv`).
-/

universe u

open TensorProduct

namespace SemistableReduction

noncomputable section

/-- `(a + f)^n = a^n + f` for `a f = 0`, `f` idempotent and `n > 0`. -/
lemma add_pow_of_mul_eq_zero {R : Type*} [CommRing R] {a f : R} (haf : a * f = 0)
    (hf : IsIdempotentElem f) {n : ℕ} (hn : 0 < n) : (a + f) ^ n = a ^ n + f := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp
    rw [pow_succ, ih hn']
    have h1 : a ^ n * f = 0 := by
      obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_lt hn'
      rw [pow_succ, mul_assoc, haf, mul_zero]
    linear_combination h1 + haf + hf.eq

namespace KummerNodeFactor

variable {O : Type u} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] {c : O} {d : ℕ}
  (N : Type u) [CommRing N] [Algebra (Node O (c ^ d)) N]

/-- The inclusion of the Kummer node factor into the Kummer factor. -/
abbrev incl : KummerNodeFactor (c := c) (d := d) N →ₐ[N] KummerFactor (c := c) (d := d) N :=
  Algebra.TensorProduct.map (AlgHom.id N N)
    (IsScalarTower.toAlgHom (Node O (c ^ d)) (KNode c d) (KummerField c d))

variable [Algebra.Smooth (Node O (c ^ d)) N]

lemma kummerFactorEquiv_val (hc : c ≠ 0) (hd : 0 < d) (a : KummerNodeFactor (c := c) (d := d) N) :
    (kummerFactorEquiv N hc hd a : KummerFactor (c := c) (d := d) N) = incl N a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]
  | tmul n y =>
    haveI : IsIntegralClosure (KNode c d) (Node O (c ^ d)) (KummerField c d) :=
      Node.kummer_isIntegralClosure hc hd
    change (n ⊗ₜ[Node O (c ^ d)] ((kummerIntegralClosureEquiv hc hd y :
      integralClosure (Node O (c ^ d)) (KummerField c d)) : KummerField c d)) =
      n ⊗ₜ[Node O (c ^ d)] (algebraMap (KNode c d) (KummerField c d) y)
    exact congrArg (n ⊗ₜ[Node O (c ^ d)] ·)
      (IsIntegralClosure.algebraMap_equiv (Node O (c ^ d)) (KNode c d) (KummerField c d)
        (integralClosure (Node O (c ^ d)) (KummerField c d)) y)
  | add a b ha hb => rw [map_add, Subalgebra.coe_add, ha, hb, map_add]

lemma incl_injective (hc : c ≠ 0) (hd : 0 < d) : Function.Injective (incl (c := c) (d := d) N) :=
  fun a b h ↦ (kummerFactorEquiv N hc hd).injective (Subtype.val_injective
    ((kummerFactorEquiv_val N hc hd a).trans (h.trans (kummerFactorEquiv_val N hc hd b).symm)))

lemma mem_range_incl (hc : c ≠ 0) (hd : 0 < d) {x : KummerFactor (c := c) (d := d) N}
    (hx : IsIntegral N x) : ∃ a, incl N a = x :=
  ⟨(kummerFactorEquiv N hc hd).symm ⟨x, hx⟩, by
    rw [← kummerFactorEquiv_val N hc hd, AlgEquiv.apply_symm_apply]⟩

omit [IsIntegrallyClosed O] in
/-- The coordinate `w` is invertible in the Kummer field. -/
lemma isUnit_u (hc : c ≠ 0) : IsUnit (algebraMap (KNode c d) (KummerField c d) (KNode.u c d)) := by
  haveI : IsDomain (Node O c) := Node.isDomain hc
  have hu : (Node.u c : Node O c) ≠ 0 := fun h ↦ by
    have h1 := congrArg (Node.laurent c 1) h
    rw [Node.laurent_u, map_zero] at h1
    exact (LaurentPolynomial.isUnit_T (R := FractionRing O) ((1 : ℕ) : ℤ)).ne_zero h1
  exact IsLocalization.map_units (FractionRing (Node O c))
    (⟨Node.u c, mem_nonZeroDivisors_of_ne_zero hu⟩ : nonZeroDivisors (Node O c))

/-- **The twists of a map into a Kummer node factor are balanced.** If `σ, τ` are supported on
an idempotent `ε` with `σ^e = ε w^d` and `σ τ = ε (w z)^D`, `d = e D`, then `σ = ε α w^D` and
`τ = ε α^{e−1} z^D` for an `e`-th root of unity `α`. -/
theorem exists_twist (hc : c ≠ 0) (hd : 0 < d) {e D : ℕ} (he : 0 < e) (hde : d = e * D)
    {ε σ τ : KummerNodeFactor (c := c) (d := d) N} (hε : IsIdempotentElem ε) (hσ : ε * σ = σ)
    (hτ : ε * τ = τ) (hσe : σ ^ e = ε * ((1 : N) ⊗ₜ KNode.u c d) ^ d)
    (hστ : σ * τ = ε * ((1 : N) ⊗ₜ KNode.u c d * (1 : N) ⊗ₜ KNode.v c d) ^ D) :
    ∃ α : KummerNodeFactor (c := c) (d := d) N, α ^ e = 1 ∧
      σ = ε * α * ((1 : N) ⊗ₜ KNode.u c d) ^ D ∧
      τ = ε * α ^ (e - 1) * ((1 : N) ⊗ₜ KNode.v c d) ^ D := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, (Nat.sub_add_cancel he).symm⟩
  set ι := incl (c := c) (d := d) N
  obtain ⟨wi, hwi⟩ := (isUnit_u (d := d) hc).exists_right_inv
  set U := ι ((1 : N) ⊗ₜ KNode.u c d)
  set V := ι ((1 : N) ⊗ₜ KNode.v c d)
  set W : KummerFactor (c := c) (d := d) N := (1 : N) ⊗ₜ wi
  have hUW : U * W = 1 := by
    change (1 : N) ⊗ₜ[Node O (c ^ d)] (algebraMap (KNode c d) (KummerField c d)
      (KNode.u c d)) * (1 : N) ⊗ₜ wi = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hwi]
    rfl
  set a := ι σ * W ^ D
  set f := 1 - ι ε
  have hεi : IsIdempotentElem (ι ε) := hε.map ι
  have hσi : ι ε * ι σ = ι σ := by rw [← map_mul ι, hσ]
  have hτi : ι ε * ι τ = ι τ := by rw [← map_mul ι, hτ]
  have haf : a * f = 0 := by
    change ι σ * W ^ D * (1 - ι ε) = 0
    linear_combination (-(W ^ D)) * hσi
  have hae : a ^ (e' + 1) = ι ε := by
    have h1 : ι σ ^ (e' + 1) = ι ε * U ^ d := by
      rw [← map_pow ι, hσe, map_mul ι, map_pow ι]
    have hUd : U ^ d = (U ^ D) ^ (e' + 1) := by rw [← pow_mul, mul_comm D, ← hde]
    change (ι σ * W ^ D) ^ (e' + 1) = ι ε
    rw [mul_pow, h1, hUd, mul_assoc, ← mul_pow, ← mul_pow, hUW, one_pow, one_pow, mul_one]
  set α₀ := a + f
  have hα₀ : α₀ ^ (e' + 1) = 1 := by
    rw [add_pow_of_mul_eq_zero haf hεi.one_sub (Nat.succ_pos e'), hae]
    ring
  obtain ⟨α, hα⟩ := mem_range_incl N hc hd (x := α₀)
    (IsIntegral.of_pow (Nat.succ_pos e') (by rw [hα₀]; exact isIntegral_one))
  have hUWD : U ^ D * W ^ D = 1 := by rw [← mul_pow, hUW, one_pow]
  have hσ' : ι σ = ι ε * α₀ * U ^ D := by
    change ι σ = ι ε * (ι σ * W ^ D + (1 - ι ε)) * U ^ D
    linear_combination (-(W ^ D * U ^ D)) * hσi - ι σ * hUWD + U ^ D * hεi.eq
  have hστi : ι σ * ι τ = ι ε * (U * V) ^ D := by
    rw [← map_mul ι, hστ, map_mul ι, map_pow ι, map_mul ι]
  refine ⟨α, incl_injective N hc hd ?_, incl_injective N hc hd ?_, incl_injective N hc hd ?_⟩
  · rw [map_pow ι, hα, hα₀, map_one]
  · rw [map_mul ι, map_mul ι, map_pow ι, hα]
    exact hσ'
  · rw [map_mul ι, map_mul ι, map_pow ι, map_pow ι, hα, Nat.add_sub_cancel]
    linear_combination (-1 : KummerFactor (c := c) (d := d) N) * hτi - (ι ε * ι τ) * hα₀ -
      (ι ε * ι τ * α₀ ^ (e' + 1)) * hUWD + (ι ε * α₀ ^ e' * V ^ D) * hUWD -
      (α₀ ^ e' * W ^ D * ι τ) * hσ' + (α₀ ^ e' * W ^ D) * hστi

end KummerNodeFactor

end

end SemistableReduction
