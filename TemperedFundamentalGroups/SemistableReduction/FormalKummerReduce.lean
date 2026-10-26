/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerTame
import TemperedFundamentalGroups.SemistableReduction.QuadNodeTower

/-!
# Reduction of a Kummer splitting to the special fibre (MR12 T2 S5.4, step K0)

Let `θ : O → k` be surjective onto a field (the residue map of the level ring), `J = (ker θ)·`
the ideal of the special fibre in every `O`-algebra (`AdmissibleLift.J`), with the `k`-algebra
structure `QuadNodeTower.algK` on `S/J`. Let `N₁` be an `O`-algebra with elements `u₁, v₁`,
`u₁ v₁ = c ^ d`, `θ c = 0`. Then the normalised Kummer factor
`N₁ ⊗_{O[u,v]/(uv − c^d)} O[s,t]/(st − c)` (`KummerNodeFactor`, `u ↦ s^d`, `v ↦ t^d`) reduces to
the Kummer factor of the special fibre (**`FormalKummer.factorEquiv`**):

  `(N₁ ⊗ O[s,t]/(st − c))/J ≃ (N₁/J) ⊗_{k[u,v]/(uv)} k[s,t]/(st)`,

`k[u,v]/(uv) → N₁/J` through `ū₁, v̄₁` (`FormalKummer.barAlg`). This is
`TensorQuotTensor.equiv` with the reductions `N₁ → N₁/J` and `Node.baseMap` (as in
`AdmissibleLift.pieceEquiv`). For a splitting `Φ : X ≅ ∏ᵢ KummerNodeFactor` of an `N₁`-algebra `X`
(the base change of the normalisation of a chart to an étale neighbourhood, `KummerNodeSplit`),
**`FormalKummer.splitEquiv`**: `X/J ≃ ∏ᵢ (N₁/J) ⊗_{k[u,v]/(uv)} k[s,t]/(st)`, compatible with the
maps from `N₁` (`splitEquiv_algebraMap`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

namespace FormalKummer

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)]

section Factor

variable {N₁ : Type u} [CommRing N₁] [Algebra O N₁] {u₁ v₁ : N₁} {c : O} {d : ℕ}

omit hθ in
lemma θ_pow (hc : θ c = 0) : θ (c ^ d) = (0 : k) ^ d := by rw [map_pow, hc]

include hθ in
lemma bar_mul (h : u₁ * v₁ = algebraMap O N₁ (c ^ d)) (hc : θ c = 0) :
    Ideal.Quotient.mk (J θ (R := N₁)) u₁ * Ideal.Quotient.mk (J θ (R := N₁)) v₁ =
      algebraMap k (N₁ ⧸ J θ (R := N₁)) ((0 : k) ^ d) := by
  rw [← map_mul, h, ← θ_pow hc, QuadNodeTower.algK_θ]

/-- `k[u,v]/(uv − 0^d) → N₁/J`, `u ↦ ū₁`, `v ↦ v̄₁`. -/
def bar (h : u₁ * v₁ = algebraMap O N₁ (c ^ d)) (hc : θ c = 0) :
    A (0 : k) d →ₐ[k] N₁ ⧸ J θ (R := N₁) :=
  Node.lift _ _ (bar_mul h hc)

/-- The algebra structure `k[u,v]/(uv) → N₁/J` of `bar`. -/
abbrev barAlg (h : u₁ * v₁ = algebraMap O N₁ (c ^ d)) (hc : θ c = 0) :
    Algebra (A (0 : k) d) (N₁ ⧸ J θ (R := N₁)) :=
  (bar h hc).toRingHom.toAlgebra

variable (h : u₁ * v₁ = algebraMap O N₁ (c ^ d)) (hc : θ c = 0)

/-- The reduction `O[u,v]/(uv − c^d) → k[u,v]/(uv − 0^d)` as an algebra. -/
abbrev algAA : Algebra (A c d) (A (0 : k) d) := (Node.baseMap θ (θ_pow (d := d) hc)).toAlgebra

/-- `O[u,v]/(uv − c^d) → k[s,t]/(st)` through the reduction. -/
abbrev algAB : Algebra (A c d) (B (0 : k)) :=
  ((algebraMap (A (0 : k) d) (B (0 : k))).comp (Node.baseMap θ (θ_pow (d := d) hc))).toAlgebra

lemma nodeAlgebra_O (o : O) :
    (Node.lift u₁ v₁ h) (algebraMap O (A c d) o) = algebraMap O N₁ o :=
  (Node.lift u₁ v₁ h).commutes o

/-- The reduction `N₁ → N₁/J` is compatible with the node charts. -/
lemma mk_lift (a : A c d) :
    Ideal.Quotient.mk (J θ (R := N₁)) (Node.lift u₁ v₁ h a) =
      bar h hc (Node.baseMap θ (θ_pow (d := d) hc) a) := by
  have := Node.ringHom_ext (f := (Ideal.Quotient.mk (J θ (R := N₁))).comp
      (Node.lift u₁ v₁ h).toRingHom)
    (g := (bar h hc).toRingHom.comp (Node.baseMap θ (θ_pow (d := d) hc)))
    (RingHom.ext fun o ↦ by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
        Node.baseMap_algebraMap, QuadNodeTower.algK_θ])
    (by simp [bar]) (by simp [bar])
  exact RingHom.congr_fun this a

/-- The ideal `(ker θ)·O[u,v]/(uv − c^d)`. -/
abbrev K : Ideal (A c d) := (RingHom.ker θ).map (algebraMap O (A c d))

omit hθ in
lemma map_K : letI := nodeAlgebra N₁ c d h
    (K (θ := θ) (c := c) (d := d)).map (algebraMap (A c d) N₁) = J θ := by
  letI := nodeAlgebra N₁ c d h
  rw [K, Ideal.map_map, J]
  congr 1
  exact RingHom.ext fun o ↦ nodeAlgebra_O h o

/-- **The reduction of a normalised Kummer factor** to the special fibre:
`(N₁ ⊗_{O[u,v]/(uv − c^d)} O[s,t]/(st − c))/K ≃ (N₁/J) ⊗_{k[u,v]/(uv)} k[s,t]/(st)`. -/
def factorEquiv :
    letI := nodeAlgebra N₁ c d h
    (KummerNodeFactor (c := c) (d := d) N₁ ⧸
        TensorQuotTensor.KT (K (θ := θ) (c := c) (d := d)) (S := N₁) (B := KNode c d)) ≃+*
      (letI := barAlg h hc; (N₁ ⧸ J θ (R := N₁)) ⊗[A (0 : k) d] B (0 : k)) :=
  letI := nodeAlgebra N₁ c d h
  letI := barAlg h hc
  letI := algAA (d := d) (θ := θ) hc
  letI := algAB (d := d) (θ := θ) hc
  haveI : IsScalarTower (A c d) (A (0 : k) d) (N₁ ⧸ J θ (R := N₁)) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ mk_lift h hc a
  haveI : IsScalarTower (A c d) (A (0 : k) d) (B (0 : k)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let σₐ : N₁ →ₐ[A c d] N₁ ⧸ J θ (R := N₁) := Ideal.Quotient.mkₐ (A c d) (J θ (R := N₁))
  let βₐ : KNode c d →ₐ[A c d] B (0 : k) :=
    { (Node.baseMap θ hc : Node O c →+* Node k (0 : k)) with
      commutes' := fun a ↦ RingHom.congr_fun (Node.baseMap_comp_kummer θ hc d) a }
  TensorQuotTensor.equiv (σ := σₐ) (β := βₐ) (K (θ := θ) (c := c) (d := d))
    (Node.ker_baseMap (θ_pow hc) hθ.out) (Node.surjective_baseMap (θ_pow hc) hθ.out)
    Ideal.Quotient.mk_surjective (Node.surjective_baseMap hc hθ.out)
    (by
      change RingHom.ker (Ideal.Quotient.mk (J θ (R := N₁))) = _
      rw [Ideal.mk_ker]
      exact (map_K h).symm)
    (by
      change RingHom.ker (Node.baseMap θ hc) = _
      rw [Node.ker_baseMap hc hθ.out, K, Ideal.map_map]
      congr 1
      exact RingHom.ext fun o ↦ ((Node.kummer c d).commutes o).symm)

lemma factorEquiv_mk_tmul (x : N₁) (b : KNode c d) :
    letI := nodeAlgebra N₁ c d h
    letI := barAlg h hc
    factorEquiv h hc (Ideal.Quotient.mk _ (x ⊗ₜ b)) =
      Ideal.Quotient.mk (J θ (R := N₁)) x ⊗ₜ[A (0 : k) d]
        (Node.baseMap θ hc : Node O c →+* Node k (0 : k)) b :=
  letI := nodeAlgebra N₁ c d h
  letI := barAlg h hc
  letI := algAA (d := d) (θ := θ) hc
  letI := algAB (d := d) (θ := θ) hc
  haveI : IsScalarTower (A c d) (A (0 : k) d) (N₁ ⧸ J θ (R := N₁)) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ mk_lift h hc a
  haveI : IsScalarTower (A c d) (A (0 : k) d) (B (0 : k)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  TensorQuotTensor.equiv_mk_tmul ..

omit hθ in
/-- The ideal `K` of a Kummer factor is generated by `J ⊆ N₁`. -/
lemma KT_eq :
    letI := nodeAlgebra N₁ c d h
    TensorQuotTensor.KT (K (θ := θ) (c := c) (d := d)) (S := N₁) (B := KNode c d) =
      (J θ (R := N₁)).map (algebraMap N₁ (KummerNodeFactor (c := c) (d := d) N₁)) := by
  letI := nodeAlgebra N₁ c d h
  rw [TensorQuotTensor.KT, IsScalarTower.algebraMap_eq (A c d) N₁
    (KummerNodeFactor (c := c) (d := d) N₁), ← Ideal.map_map, map_K h]

end Factor

section Split

variable {N₁ : Type u} [CommRing N₁] [Algebra O N₁] {u₁ v₁ : N₁} {ϖ : O} {n : ℕ}
  {X : Type u} [CommRing X] [Algebra N₁ X] {r : ℕ} {m d : Fin r → ℕ}
  (huv : u₁ * v₁ = algebraMap O N₁ (ϖ ^ n)) (hmd : ∀ i, m i * d i = n)

include huv hmd in
lemma huv_i (i : Fin r) : u₁ * v₁ = algebraMap O N₁ ((ϖ ^ m i) ^ d i) := by
  rw [← pow_mul, hmd i]; exact huv

variable (hc : ∀ i, θ (ϖ ^ m i) = 0)

/-- The ideal `J X` generated by `J ⊆ N₁`. -/
abbrev JX : Ideal X := (J θ (R := N₁)).map (algebraMap N₁ X)

/-- The reduced factors `(N₁/J) ⊗_{k[u,v]/(uv)} k[s,t]/(st)`. -/
abbrev RedFactor (i : Fin r) : Type u :=
  letI := barAlg (huv_i huv hmd i) (hc i)
  (N₁ ⧸ J θ (R := N₁)) ⊗[A (0 : k) (d i)] B (0 : k)

omit hθ in
/-- `J` generates corresponding ideals under an `N₁`-algebra isomorphism. -/
lemma JX_eq_map {Y : Type u} [CommRing Y] [Algebra N₁ Y] (Φ : X ≃ₐ[N₁] Y) :
    JX (θ := θ) (N₁ := N₁) (X := Y) =
      (JX (θ := θ) (N₁ := N₁) (X := X)).map (Φ : X →+* Y) := by
  have h : algebraMap N₁ Y = (Φ : X →+* Y).comp (algebraMap N₁ X) :=
    RingHom.ext fun a ↦ (Φ.commutes a).symm
  change (J θ (R := N₁)).map (algebraMap N₁ Y) = ((J θ (R := N₁)).map (algebraMap N₁ X)).map _
  rw [Ideal.map_map (algebraMap N₁ X), ← h]

/-- The normalised Kummer factors `N₁ ⊗_{O[u,v]/(uv − ϖ^n)} O[s,t]/(st − ϖ^{mᵢ})`. -/
abbrev KFac (i : Fin r) : Type u :=
  @KummerNodeFactor O _ (ϖ ^ m i) (d i) N₁ _ (nodeAlgebra N₁ (ϖ ^ m i) (d i) (huv_i huv hmd i))

/-- **The reduction of a Kummer splitting**: for `Φ : X ≅ ∏ᵢ KummerNodeFactor` (over `N₁`),
`X/J ≃ ∏ᵢ (N₁/J) ⊗_{k[u,v]/(uv)} k[s,t]/(st)`. -/
def splitEquiv (Φ : X ≃ₐ[N₁] ∀ i, KFac huv hmd i) :
    (X ⧸ JX (θ := θ) (N₁ := N₁) (X := X)) ≃+* ∀ i, RedFactor (θ := θ) huv hmd hc i :=
  (Ideal.quotientEquiv _ _ Φ.toRingEquiv (JX_eq_map Φ)).trans
    ((PiQuot.equiv (J θ (R := N₁)) (KFac huv hmd)).trans
      (RingEquiv.piCongrRight fun i ↦
        (Ideal.quotEquivOfEq (KT_eq (huv_i huv hmd i)).symm).trans
          (factorEquiv (huv_i huv hmd i) (hc i))))

lemma splitEquiv_algebraMap (Φ : X ≃ₐ[N₁] ∀ i, KFac huv hmd i) (x : N₁) (i : Fin r) :
    splitEquiv huv hmd hc Φ
        ((Ideal.Quotient.mk (JX (θ := θ) (N₁ := N₁) (X := X))) (algebraMap N₁ X x)) i =
      letI := barAlg (huv_i huv hmd i) (hc i)
      Ideal.Quotient.mk (J θ (R := N₁)) x ⊗ₜ[A (0 : k) (d i)] (1 : B (0 : k)) := by
  letI : ∀ i, Algebra (A (ϖ ^ m i) (d i)) N₁ := fun i ↦
    nodeAlgebra N₁ (ϖ ^ m i) (d i) (huv_i huv hmd i)
  have h1 : Φ (algebraMap N₁ X x) i = x ⊗ₜ (1 : KNode (ϖ ^ m i) (d i)) := by
    rw [Φ.commutes]
    rfl
  change factorEquiv (huv_i huv hmd i) (hc i) (Ideal.quotEquivOfEq
    (KT_eq (huv_i huv hmd i)).symm
    (Ideal.Quotient.mk ((J θ (R := N₁)).map (algebraMap N₁ (KFac huv hmd i)))
      (Φ (algebraMap N₁ X x) i))) = _
  rw [Ideal.quotEquivOfEq_mk, h1, factorEquiv_mk_tmul]
  letI := barAlg (huv_i huv hmd i) (hc i)
  exact congrArg (_ ⊗ₜ[A (0 : k) (d i)] ·) (map_one (Node.baseMap θ (hc i)))

end Split

end

end FormalKummer

end SemistableReduction
