/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerLocal
import TemperedFundamentalGroups.SemistableReduction.CompletionEtale

/-!
# The formal Kummer form of the special fibre at a node (MR12 T2 S5.4, local step)

Let `R` be an `O`-algebra (a chart of the model), `B` an `R`-algebra (the normalisation of the
chart in a cover), `θ : O → k` the residue map, `J = (ker θ)·` and `R̄ = R/J`, `C = B/JB` the
special fibres. Suppose that, over an étale `R`-algebra `N₁` with a prime `𝔫` over the node `𝔪`,
`N₁ ⊗_R B` splits into normalised Kummer factors with respect to the node coordinates `x, y` of
`R` (`KummerNodeSplit`, the body of `IsKummerNormAt` with `u₁ = x`, `v₁ = y`), and that the
residue field extension at `𝔫` is trivial. Then (**`FormalKummer.nodeEquiv`**)

  `R̂_𝔪 ⊗_{R̄} C ≅ ∏ᵢ R̂_𝔪 ⊗_{k[u,v]/(uv)} k[s,t]/(st)`   (`u ↦ x̄ ↦ sᵈⁱ`, `v ↦ ȳ ↦ tᵈⁱ`)

as `R̂_𝔪`-algebras, `R̂_𝔪` the `𝔪̄`-adic completion of `R̄`. Proof:

* `(N₁ ⊗_R B)/J ≅ N̄₁ ⊗_{R̄} C` (`TensorQuotTensor.equiv`) and the reduction of the splitting
  (`FormalKummer.splitEquiv`) give `Φ̄ : N̄₁ ⊗_{R̄} C ≅ ∏ᵢ N̄₁ ⊗_{k[u,v]/(uv)} k[s,t]/(st)`
  (**`FormalKummer.redSplitEquiv`**);
* `N̄₁ = N₁/J` is formally étale over `R̄`, so the completions of `R̄` at `𝔪̄` and of `N̄₁` at `𝔫̄`
  agree (`CompletionEtale.equiv`, trivial residue field extension); this gives an `R̄`-algebra
  map `g : N̄₁ → R̂_𝔪`;
* base change of `Φ̄` along `g` (`FormalKummer.baseChangeEquiv`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

namespace FormalKummer

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {B : Type u} [CommRing B] [Algebra R B]
  {N₁ : Type u} [CommRing N₁] [Algebra R N₁] [Algebra O N₁] [IsScalarTower O R N₁]

section Special

variable (θ R N₁ B)

/-- The special fibre `R̄ = R/J` of the chart. -/
abbrev Rs : Type u := R ⧸ J θ (R := R)

/-- The special fibre `C = B/JB` of the cover. -/
abbrev Cs : Type u := B ⧸ (J θ (R := R)).map (algebraMap R B)

/-- The special fibre `N̄₁ = N₁/J` of the étale neighbourhood. -/
abbrev Ns : Type u := N₁ ⧸ J θ (R := N₁)

lemma J_N₁_eq :
    (J θ (R := R)).map (algebraMap R N₁) = J θ (R := N₁) := by
  rw [J, J, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

lemma J_le_comap : J θ (R := R) ≤ (J θ (R := N₁)).comap (algebraMap R N₁) := by
  rw [← Ideal.map_le_iff_le_comap, J_N₁_eq]

/-- `R̄ → N̄₁`. -/
abbrev algRN : Algebra (Rs θ R) (Ns θ N₁) :=
  Ideal.Quotient.algebraQuotientOfLEComap (J_le_comap θ R N₁)

end Special

attribute [local instance] algRN

lemma algebraMap_RN (r : R) :
    algebraMap (Rs θ R) (Ns θ N₁) (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R N₁ r) := rfl

instance : IsScalarTower R (Rs θ R) (Ns θ N₁) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- **The special fibre of an étale neighbourhood is formally étale over that of the chart.** -/
theorem formallyEtale_Ns [Algebra.FormallyEtale R N₁] :
    Algebra.FormallyEtale (Rs θ R) (Ns θ N₁) := by
  haveI : Algebra.FormallyEtale (Rs θ R) (N₁ ⧸ (J θ (R := R)).map (algebraMap R N₁)) :=
    .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor N₁ (J θ (R := R))).symm
  refine .of_equiv (AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq (J_N₁_eq θ R N₁)) ?_)
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/-! ### The reduced splitting -/

section Red

variable {x y : R} {ϖ : O} {n : ℕ} {r : ℕ} {m d : Fin r → ℕ}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) (hmd : ∀ i, m i * d i = n)
  (hc : ∀ i, θ (ϖ ^ m i) = 0)

include hxy in
lemma huvN :
    algebraMap R N₁ x * algebraMap R N₁ y = algebraMap O N₁ (ϖ ^ n) := by
  rw [← map_mul, hxy, ← IsScalarTower.algebraMap_apply]

lemma ker_mk_N₁ :
    RingHom.ker (Ideal.Quotient.mkₐ R (J θ (R := N₁))) =
      (J θ (R := R)).map (algebraMap R N₁) := by
  rw [J_N₁_eq]
  exact Ideal.mk_ker

lemma ker_mk_B :
    RingHom.ker (Ideal.Quotient.mkₐ R ((J θ (R := R)).map (algebraMap R B))) =
      (J θ (R := R)).map (algebraMap R B) :=
  Ideal.mk_ker

instance : IsScalarTower R (Rs θ R) (Cs θ R B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- `(N₁ ⊗_R B)/J ≅ N̄₁ ⊗_{R̄} C`. -/
def tensorQuot :
    (N₁ ⊗[R] B) ⧸ TensorQuotTensor.KT (J θ (R := R)) (S := N₁) (B := B) ≃+*
      Ns θ N₁ ⊗[Rs θ R] Cs θ R B :=
  TensorQuotTensor.equiv (σ := Ideal.Quotient.mkₐ R (J θ (R := N₁)))
    (β := Ideal.Quotient.mkₐ R ((J θ (R := R)).map (algebraMap R B))) (J θ (R := R))
    Ideal.mk_ker Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective
    Ideal.Quotient.mk_surjective (ker_mk_N₁ (θ := θ) (R := R) (N₁ := N₁))
    (ker_mk_B (θ := θ) (R := R) (B := B))

lemma tensorQuot_mk_tmul (a : N₁) (b : B) :
    tensorQuot (θ := θ) (Ideal.Quotient.mk _ (a ⊗ₜ b)) =
      (Ideal.Quotient.mk _ a : Ns θ N₁) ⊗ₜ[Rs θ R] (Ideal.Quotient.mk _ b : Cs θ R B) :=
  TensorQuotTensor.equiv_mk_tmul ..

lemma KT_eq_JX :
    TensorQuotTensor.KT (J θ (R := R)) (S := N₁) (B := B) =
      JX (θ := θ) (N₁ := N₁) (X := N₁ ⊗[R] B) := by
  rw [TensorQuotTensor.KT, JX, ← J_N₁_eq θ R N₁, Ideal.map_map (algebraMap R N₁),
    ← IsScalarTower.algebraMap_eq]

variable [hθ : Fact (Function.Surjective θ)]

/-- **The reduced Kummer splitting** `N̄₁ ⊗_{R̄} C ≅ ∏ᵢ N̄₁ ⊗_{k[u,v]/(uv)} k[s,t]/(st)`. -/
def redSplitEquiv (Φ : N₁ ⊗[R] B ≃ₐ[N₁] ∀ i, KFac (huvN (N₁ := N₁) hxy) hmd i) :
    Ns θ N₁ ⊗[Rs θ R] Cs θ R B ≃ₐ[Ns θ N₁] ∀ i, RedFactor (huvN (N₁ := N₁) hxy) hmd hc i :=
  AlgEquiv.ofRingEquiv (f := (tensorQuot (θ := θ)).symm.trans
    ((Ideal.quotEquivOfEq (KT_eq_JX (θ := θ) (R := R) (N₁ := N₁) (B := B))).trans
      (splitEquiv _ hmd hc Φ))) (by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h1 : (tensorQuot (θ := θ)).symm (algebraMap (Ns θ N₁) (Ns θ N₁ ⊗[Rs θ R] Cs θ R B)
        (Ideal.Quotient.mk _ a)) = Ideal.Quotient.mk _ (a ⊗ₜ (1 : B)) := by
      rw [RingEquiv.symm_apply_eq, tensorQuot_mk_tmul, map_one]
      rfl
    simp only [RingEquiv.trans_apply]
    rw [h1, Ideal.quotEquivOfEq_mk]
    funext i
    exact splitEquiv_algebraMap _ hmd hc Φ a i)

end Red

/-! ### The chart map `k[u,v]/(uv) → R̄` and the formal Kummer form at the node -/

section Chart

variable {S : Type u} [CommRing S] [Algebra k S] {x y : S}

/-- `k[u,v]/(uv − 0^e) → S`, `u ↦ x`, `v ↦ y`, for `x y = 0`, `0 < e`. -/
def chartMap (h : x * y = 0) {e : ℕ} (he : 0 < e) : A (0 : k) e →ₐ[k] S :=
  Node.lift x y (by rw [h, zero_pow he.ne', map_zero])

@[simp] lemma chartMap_u (h : x * y = 0) {e : ℕ} (he : 0 < e) :
    chartMap h he (Node.u ((0 : k) ^ e)) = x := Node.lift_u ..

@[simp] lemma chartMap_v (h : x * y = 0) {e : ℕ} (he : 0 < e) :
    chartMap h he (Node.v ((0 : k) ^ e)) = y := Node.lift_v ..

/-- The algebra structure `k[u,v]/(uv) → T` through `S → T`. -/
abbrev chartAlg (h : x * y = 0) {e : ℕ} (he : 0 < e) (T : Type u) [CommRing T] [Algebra S T] :
    Algebra (A (0 : k) e) T :=
  ((algebraMap S T).comp (chartMap h he).toRingHom).toAlgebra

end Chart

section Node

attribute [local instance] algRN

variable [hθ : Fact (Function.Surjective θ)]

variable {x y : R} {ϖ : O} {n : ℕ} {r : ℕ} {m d : Fin r → ℕ}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) (hmd : ∀ i, m i * d i = n)
  (hc : ∀ i, θ (ϖ ^ m i) = 0) (hd : ∀ i, 0 < d i) (hn : θ (ϖ ^ n) = 0)

include hxy hn in
lemma xy_bar : (Ideal.Quotient.mk _ x : Rs θ R) * Ideal.Quotient.mk _ y = 0 := by
  rw [← map_mul, hxy, ← QuadNodeTower.algK_θ, hn, map_zero]

/-- The node structure `k[u,v]/(uv) → N̄₁` of the reduced splitting is the chart map. -/
lemma barAlg_eq (i : Fin r) (a : A (0 : k) (d i)) :
    (bar (huv_i (huvN (N₁ := N₁) hxy) hmd i) (hc i)) a =
      algebraMap (Rs θ R) (Ns θ N₁) (chartMap (xy_bar hxy hn) (hd i) a) := by
  have := Node.ringHom_ext (O := k) (a := (0 : k) ^ d i)
    (f := (bar (huv_i (huvN (N₁ := N₁) hxy) hmd i) (hc i)).toRingHom)
    (g := (algebraMap (Rs θ R) (Ns θ N₁)).comp (chartMap (xy_bar hxy hn) (hd i)).toRingHom)
    (RingHom.ext fun c ↦ by
      obtain ⟨o, rfl⟩ := hθ.out c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
        QuadNodeTower.algK_θ]
      exact congrArg _ (IsScalarTower.algebraMap_apply O R N₁ o))
    (by simp [bar, chartMap]; rfl) (by simp [bar, chartMap]; rfl)
  exact RingHom.congr_fun this a

variable (𝔪s : Ideal (Rs θ R)) (𝔫s : Ideal (Ns θ N₁))
  (hcomap : 𝔫s.comap (algebraMap (Rs θ R) (Ns θ N₁)) = 𝔪s)
  (hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔫s).comp (algebraMap (Rs θ R) (Ns θ N₁))))

/-- The `R̄`-algebra map `N̄₁ → N̂₁ ≅ R̂_𝔪` (trivial residue field extension). -/
def toHat [Algebra.FormallyEtale R N₁] :
    Ns θ N₁ →ₐ[Rs θ R] AdicCompletion 𝔪s (Rs θ R) :=
  haveI := formallyEtale_Ns (θ := θ) (R := R) (N₁ := N₁)
  { (CompletionEtale.equiv 𝔪s 𝔫s hcomap hsurj).symm.toRingHom.comp
      (algebraMap (Ns θ N₁) (AdicCompletion 𝔫s (Ns θ N₁))) with
    commutes' := fun z ↦ by
      change (CompletionEtale.equiv 𝔪s 𝔫s hcomap hsurj).symm _ = _
      rw [RingEquiv.symm_apply_eq, CompletionEtale.equiv_algebraMap] }

/-- **The formal Kummer form of the special fibre at a node**: for a Kummer splitting
`Φ : N₁ ⊗_R B ≅ ∏ᵢ KummerNodeFactor` with respect to the node coordinates `x, y` of `R` over an
étale `N₁` whose special fibre has trivial residue field extension at `𝔫̄` over `𝔪̄`,
`R̂_𝔪 ⊗_{R̄} C ≅ ∏ᵢ R̂_𝔪 ⊗_{k[u,v]/(uv)} k[s,t]/(st)` (`u ↦ x̄`, `v ↦ ȳ`). -/
def nodeEquiv [Algebra.FormallyEtale R N₁]
    (Φ : N₁ ⊗[R] B ≃ₐ[N₁] ∀ i, KFac (huvN (N₁ := N₁) hxy) hmd i) :
    letI : ∀ i, Algebra (A (0 : k) (d i)) (AdicCompletion 𝔪s (Rs θ R)) := fun i ↦
      chartAlg (xy_bar hxy hn) (hd i) _
    AdicCompletion 𝔪s (Rs θ R) ⊗[Rs θ R] Cs θ R B ≃ₐ[AdicCompletion 𝔪s (Rs θ R)]
      ∀ i, AdicCompletion 𝔪s (Rs θ R) ⊗[A (0 : k) (d i)] KummerEtale.B (0 : k) :=
  letI : ∀ i, Algebra (A (0 : k) (d i)) (AdicCompletion 𝔪s (Rs θ R)) := fun i ↦
    chartAlg (xy_bar hxy hn) (hd i) _
  letI : ∀ i, Algebra (A (0 : k) (d i)) (Ns θ N₁) := fun i ↦
    barAlg (huv_i (huvN (N₁ := N₁) hxy) hmd i) (hc i)
  baseChangeEquiv (toHat 𝔪s 𝔫s hcomap hsurj)
    (fun i ↦ (chartMap (xy_bar hxy hn) (hd i)).toRingHom)
    (fun i a ↦ barAlg_eq hxy hmd hc hd hn i a) (fun _ _ ↦ rfl)
    (redSplitEquiv hxy hmd hc Φ)

end Node

end

end FormalKummer

end SemistableReduction
