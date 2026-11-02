/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerPieceBranch
import TemperedFundamentalGroups.SemistableReduction.CuspInputHom
import TemperedFundamentalGroups.SemistableReduction.NodeQuot
import TemperedFundamentalGroups.SemistableReduction.TateGlue1

/-!
# The node normal form hypotheses on the Tate node chart (MR12 I3, layer 3, Tate node chart)

`Admissible.kummerPiece_nfHyp_s`, `kummerPiece_nfHyp_t`, `kummerPiece_hinter`
(`KummerPieceBranch`) reduce the node normal form hypotheses of a Kummer factor
`(R̂/(1 − ε)) ⊗_A B` to three facts on the base `P = R̂/(1 − ε)`, `R̂` the `f̄`-adic completion of
the special fibre `R/J` of a chart over the node ring, with formal node coordinates `ū, v̄`:
(1) `ū` satisfies `CuspHom.NFHyp` on `P/(v̄)`, (2) symmetrically, (3) `(ū) ∩ (v̄) = 0` in `P`.
We prove them for every idempotent `ε` of a chart `R` over `A = O[u,v]/(uv − π^e)` which is flat
over `A` and Noetherian, with `θ(π^e) = 0`, provided `(R/J)/(ū, v̄)` is reduced (`NodeRed`):

* **`NodeNF.mem_map_sup_of_flat`**: colon ideals `(I : t) ⊆ (s) + I` survive flat base change
  (equational criterion of flatness);
* `NodeNF.mem_sup_of_u_sq_mul`: `(I : u²) ⊆ (v) + I` on the node ring for `π^e ∈ I`
  (`Node.quotEquiv` and the branch `u ↦ X`, `v ↦ 0` of `O[u,v]/(uv)`); so `(0 : ū²) ⊆ (v̄)` on `R/J`
  (`mem_span_special_v`, flatness of `R` over `A`) and on `R̂` (`hat_mem_span_v`, flatness of the
  completion of a Noetherian ring);
* `NodeNF.nfHyp_corner_quot`, `inter_corner`: in a ring with `uv = 0`, `(0 : u²) ⊆ (v)`,
  `(u + v)`-adically separated and `(H/(v))/(u)` reduced, the hypotheses hold on `(H/(1 − δ))/(v)`
  (`CuspHom.nfHyp_corner`); `isReduced_completion_quot`: `R̂/(v̄)/(ū)` embeds into `(R/J)/(ū, v̄)`;
* **`NodeNF.pieceBase_nfHyp_u`, `pieceBase_nfHyp_v`, `pieceBase_inter`**: the three facts;
* `NodeNF.nodeRed_quadNode`: for the quadratic node chart `(A[S]/(S² + S − c))[1/D]` with
  `c, D − 1 ∈ (u, v)`, `(R/J)/(ū, v̄) = k[S]/(S² + S)` is reduced (in every characteristic).

Tate (`TateGlue1`): `cN, DN − 1 ∈ (u, v)`, so **`TateGlue1.pieceBase_nfHyp_u`, `pieceBase_nfHyp_v`,
`pieceBase_inter`** hold for every idempotent of the Tate node chart's `R̂`, and
**`TateGlue1.cov₀_nfHyp_s`, `cov₀_nfHyp_t`, `cov₀_hinter`** give the conclusions of
`kummerPiece_nfHyp_s/t`, `kummerPiece_hinter` for all Kummer factors of a covering `cov₀`.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace NodeNF

/-! ### Colon ideals under flat base change -/

/-- If `C` is flat over `S` and `(I : t) ⊆ (s) + I` in `S`, then `(I C : t) ⊆ (s) C + I C`. -/
theorem mem_map_sup_of_flat {S C : Type*} [CommRing S] [CommRing C] [Algebra S C]
    [Module.Flat S C] (I : Ideal S) {s t : S}
    (h : ∀ x : S, t * x ∈ I → x ∈ Ideal.span {s} ⊔ I) {y : C}
    (hy : algebraMap S C t * y ∈ I.map (algebraMap S C)) :
    y ∈ (Ideal.span {s} ⊔ I).map (algebraMap S C) := by
  have hy' : algebraMap S C t * y ∈ Submodule.span C (algebraMap S C '' I) := hy
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp hy'
  choose a ha hga using fun i ↦ (g i).2
  let F : Option (Fin n) → S := fun o ↦ o.elim t fun i ↦ -a i
  let Y : Option (Fin n) → C := fun o ↦ o.elim y c
  have hrel : ∑ o, F o • Y o = 0 := by
    rw [Fintype.sum_option]
    change t • y + ∑ i, (-a i) • c i = 0
    rw [Algebra.smul_def, ← hg]
    simp only [smul_eq_mul, Algebra.smul_def, ← hga, mul_comm (c _), map_neg, neg_mul,
      Finset.sum_neg_distrib, add_neg_cancel]
  obtain ⟨k, α, z, hx, hα⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := S) (M := C) hrel
  rw [show y = ∑ j, α none j • z j from hx none]
  refine Ideal.sum_mem _ fun j _ ↦ ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h _ ?_))
  have h1 := hα j
  rw [Fintype.sum_option] at h1
  simp only [F, Option.elim, neg_mul, Finset.sum_neg_distrib] at h1
  rw [show t * α none j = ∑ i, a i * α (some i) j by linear_combination h1]
  exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_right _ _ (ha i)

/-- `(0 : t²) ⊆ (s)` passes to the completion of a Noetherian ring (flatness). -/
theorem mem_span_completion {B : Type u} [CommRing B] [IsNoetherianRing B] (g : B) {s t : B}
    (h : ∀ z : B, t ^ 2 * z = 0 → z ∈ Ideal.span {s}) {x : AdicCompletion (Ideal.span {g}) B}
    (hx : algebraMap B _ t ^ 2 * x = 0) : x ∈ Ideal.span {algebraMap B _ s} := by
  have hy : algebraMap B (AdicCompletion (Ideal.span {g}) B) (t ^ 2) * x ∈
      (⊥ : Ideal B).map (algebraMap B _) := by
    rw [Ideal.map_bot, map_pow, hx]
    exact Ideal.zero_mem _
  have := mem_map_sup_of_flat ⊥ (fun z hz ↦ by
    rw [sup_bot_eq]
    exact h z ((Submodule.mem_bot _).mp hz)) hy
  rwa [sup_bot_eq, Ideal.map_span, Set.image_singleton] at this

/-! ### The node `k[u,v]/(uv)` -/

section Node

variable {O : Type*} [CommRing O] {a : O}

/-- The branch `u ↦ X`, `v ↦ 0` of the node `O[u,v]/(uv)`. -/
noncomputable def evU (ha : a = 0) : Node O a →ₐ[O] O[X] :=
  Node.lift X 0 (by rw [mul_zero, ha, map_zero])

/-- `u²x = 0` implies `x ∈ (v)` on `O[u,v]/(uv)`. -/
theorem mem_span_v_of_u_sq_mul (ha : a = 0) {x : Node O a} (hx : Node.u a ^ 2 * x = 0) :
    x ∈ Ideal.span {Node.v a} := by
  let ψ : Node O a →ₐ[O] Node O a := (Polynomial.aeval (Node.u a)).comp (evU ha)
  have hψ : (Ideal.Quotient.mkₐ O (Ideal.span {Node.v a})).comp ψ =
      Ideal.Quotient.mkₐ O (Ideal.span {Node.v a}) := by
    refine Node.algHom_ext ?_ ?_
    · simp [ψ, evU]
    · simp only [AlgHom.comp_apply, ψ, evU, Node.lift_v, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)).symm
  have h0 : evU ha x = 0 := by
    have := congrArg (evU ha) hx
    rw [map_mul, map_pow, evU, Node.lift_u, map_zero] at this
    exact (Polynomial.monic_X_pow 2).mul_right_eq_zero_iff.mp this
  have := DFunLike.congr_fun hψ x
  simp only [AlgHom.comp_apply, ψ, h0, map_zero, Ideal.Quotient.mkₐ_eq_mk] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm

/-- The swap `u ↔ v` of the node. -/
noncomputable def swap : Node O a →ₐ[O] Node O a :=
  Node.lift (Node.v a) (Node.u a) (by rw [mul_comm, Node.u_mul_v])

lemma swap_swap (x : Node O a) : swap (swap x) = x := by
  have h : (swap (a := a)).comp swap = AlgHom.id O _ :=
    Node.algHom_ext (by simp [swap]) (by simp [swap])
  exact DFunLike.congr_fun h x

/-- `v²x = 0` implies `x ∈ (u)` on `O[u,v]/(uv)`. -/
theorem mem_span_u_of_v_sq_mul (ha : a = 0) {x : Node O a} (hx : Node.v a ^ 2 * x = 0) :
    x ∈ Ideal.span {Node.u a} := by
  have h : Node.u a ^ 2 * swap x = 0 := by
    have := congrArg swap hx
    rwa [map_mul, map_pow, swap, Node.lift_v, map_zero] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (mem_span_v_of_u_sq_mul ha h)
  rw [← swap_swap x, ← hc, map_mul, show swap (Node.v a) = Node.u a from Node.lift_v ..]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

variable (I : Ideal O) (haI : a ∈ I)
include haI

/-- `(I : u²) ⊆ (v) + I` on `O[u,v]/(uv − a)`, `a ∈ I`. -/
theorem mem_sup_of_u_sq_mul {x : Node O a} (hx : Node.u a ^ 2 * x ∈ Node.IN I a) :
    x ∈ Ideal.span {Node.v a} ⊔ Node.IN I a := by
  let E := Node.quotEquiv I a
  have ha' : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr haI
  have h1 : Node.u _ ^ 2 * E (Ideal.Quotient.mk _ x) = 0 := by
    rw [← Node.quotEquiv_u, ← map_pow, ← map_mul, ← map_pow, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (mem_span_v_of_u_sq_mul ha' h1)
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (E.symm c)
  have h2 : Ideal.Quotient.mk (Node.IN I a) x = Ideal.Quotient.mk _ (d * Node.v a) :=
    E.injective (by rw [map_mul, map_mul, Node.quotEquiv_v, hd, E.apply_symm_apply, hc])
  rw [Ideal.Quotient.eq] at h2
  rw [show x = d * Node.v a + (x - d * Node.v a) by ring]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _
    (Ideal.mem_span_singleton_self _))) (Ideal.mem_sup_right h2)

/-- `(I : v²) ⊆ (u) + I` on `O[u,v]/(uv − a)`, `a ∈ I`. -/
theorem mem_sup_of_v_sq_mul {x : Node O a} (hx : Node.v a ^ 2 * x ∈ Node.IN I a) :
    x ∈ Ideal.span {Node.u a} ⊔ Node.IN I a := by
  let E := Node.quotEquiv I a
  have ha' : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr haI
  have h1 : Node.v _ ^ 2 * E (Ideal.Quotient.mk _ x) = 0 := by
    rw [← Node.quotEquiv_v, ← map_pow, ← map_mul, ← map_pow, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (mem_span_u_of_v_sq_mul ha' h1)
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (E.symm c)
  have h2 : Ideal.Quotient.mk (Node.IN I a) x = Ideal.Quotient.mk _ (d * Node.u a) :=
    E.injective (by rw [map_mul, map_mul, Node.quotEquiv_u, hd, E.apply_symm_apply, hc])
  rw [Ideal.Quotient.eq] at h2
  rw [show x = d * Node.u a + (x - d * Node.u a) by ring]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _
    (Ideal.mem_span_singleton_self _))) (Ideal.mem_sup_right h2)

end Node


/-! ### Generic: a ring with `uv = 0`, `(0 : u²) ⊆ (v)` and `(u + v)`-adically separated -/

section Ring

variable {H : Type*} [CommRing H] {u v : H}

lemma add_pow_mul (huv : u * v = 0) (m : ℕ) : (u + v) ^ m * u = u ^ (m + 1) := by
  induction m with
  | zero => rw [pow_zero, one_mul, zero_add, pow_one]
  | succ m ih =>
    rw [pow_succ, mul_assoc, add_mul, mul_comm v u, huv, add_zero, ← mul_assoc, ih,
      ← pow_succ]

variable (huv : u * v = 0) (hann : ∀ x : H, u ^ 2 * x = 0 → x ∈ Ideal.span {v})
  (hsep : ∀ a : H, (∀ m : ℕ, (u + v) ^ m ∣ a) → a = 0)
include huv hann

lemma eq_of_mul_sub_mem {x y : H} (h : u * x - u * y ∈ Ideal.span {v}) :
    x - y ∈ Ideal.span {v} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  refine hann _ ?_
  linear_combination -u * hc + c * huv

lemma isSMulRegular_quot :
    IsSMulRegular (H ⧸ Ideal.span {v}) (Ideal.Quotient.mk (Ideal.span {v}) u) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [smul_eq_mul, ← map_mul] at hab
  rw [Ideal.Quotient.eq] at hab ⊢
  exact eq_of_mul_sub_mem huv hann hab

include hsep in
lemma sep_quot (a : H ⧸ Ideal.span {v})
    (ha : ∀ m : ℕ, Ideal.Quotient.mk (Ideal.span {v}) u ^ m ∣ a) : a = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hua : u * a = 0 := hsep _ fun m ↦ by
    obtain ⟨c, hc⟩ := ha m
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq] at hc
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hc
    refine ⟨u * c, ?_⟩
    rw [← mul_assoc, add_pow_mul huv, pow_succ]
    linear_combination -u * hd + d * huv
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hann _ (by rw [pow_two, mul_assoc, hua, mul_zero])

variable {δ : H} (hδ : IsIdempotentElem δ)
include hδ

/-- **The node normal form hypotheses on `(H/(1 − δ))/(v)` for `u`.** -/
theorem nfHyp_corner_quot (hsep : ∀ a : H, (∀ m : ℕ, (u + v) ^ m ∣ a) → a = 0)
    (hred : IsReduced ((H ⧸ Ideal.span {v}) ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span {v}) u})) :
    AdmissibleLift.CuspHom.NFHyp ((H ⧸ Ideal.span {1 - δ}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - δ}) v})
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {1 - δ}) u)) := by
  have h := AdmissibleLift.CuspHom.nfHyp_corner (hδ.map (Ideal.Quotient.mk (Ideal.span {v})))
    (isSMulRegular_quot huv hann) hred (sep_quot huv hann hsep)
  have h1 : Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {v}) δ} =
      (Ideal.span {1 - δ}).map (Ideal.Quotient.mk (Ideal.span {v})) := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  have h2 : (Ideal.span {v}).map (Ideal.Quotient.mk (Ideal.span {1 - δ})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - δ}) v} := by
    rw [Ideal.map_span, Set.image_singleton]
  exact h.of_ringEquiv ((Ideal.quotEquivOfEq h1).trans
    ((DoubleQuot.quotQuotEquivComm _ _).trans (Ideal.quotEquivOfEq h2)))

/-- **The branches meet in `0` on `H/(1 − δ)`.** -/
theorem inter_corner (p : H ⧸ Ideal.span {1 - δ})
    (hpu : p ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - δ}) u})
    (hpv : p ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - δ}) v}) : p = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective p
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hpu
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hpv
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
  rw [← map_mul, ← sub_eq_zero, ← map_sub, AdmissibleLift.CuspHom.mk_eq_zero_iff hδ] at hc hd
  rw [AdmissibleLift.CuspHom.mk_eq_zero_iff hδ]
  have h1 : u ^ 2 * (δ * c) = 0 := by linear_combination u * hc - u * hd + δ * d * huv
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp (hann _ h1)
  linear_combination -hc - u * hg + g * huv

end Ring

/-! ### Reducedness of `B̂/(p, q)` for the `(p + q)`-adic completion -/

section Completion

variable {B : Type*} [CommRing B] {f p q : B}

lemma span_le_sup (hf : f = p + q) : Ideal.span {f} ≤ Ideal.span {p} ⊔ Ideal.span {q} := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hf]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self p))
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self q))

/-- The reduction `B̂ → B/(p, q)` of the `f`-adic completion, `f = p + q`. -/
noncomputable def redMap (hf : f = p + q) :
    AdicCompletion (Ideal.span {f}) B →+* B ⧸ (Ideal.span {p} ⊔ Ideal.span {q}) :=
  (Ideal.Quotient.factor (span_le_sup hf)).comp
    (AdicCompletion.evalOneₐ (Ideal.span {f})).toRingHom

lemma evalOneₐ_algebraMap (b : B) :
    AdicCompletion.evalOneₐ (Ideal.span {f})
      (algebraMap B (AdicCompletion (Ideal.span {f}) B) b) =
      Ideal.Quotient.mk _ b :=
  AlgHom.commutes _ b

lemma redMap_algebraMap (hf : f = p + q) (b : B) :
    redMap hf (algebraMap B _ b) = Ideal.Quotient.mk _ b := by
  rw [redMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    evalOneₐ_algebraMap, Ideal.Quotient.factor_mk]

/-- **`B̂/(q)/(p)` is reduced** if `B/(p, q)` is (`B̂` the `(p + q)`-adic completion). -/
theorem isReduced_completion_quot (hf : f = p + q)
    (hred : IsReduced (B ⧸ (Ideal.span {p} ⊔ Ideal.span {q}))) :
    IsReduced ((AdicCompletion (Ideal.span {f}) B ⧸
      Ideal.span {algebraMap B (AdicCompletion (Ideal.span {f}) B) q}) ⧸
      Ideal.span {Ideal.Quotient.mk
        (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {f}) B) q})
        (algebraMap B (AdicCompletion (Ideal.span {f}) B) p)}) := by
  have hq0 : Ideal.Quotient.mk (Ideal.span {p} ⊔ Ideal.span {q}) q = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self q))
  have hp0 : Ideal.Quotient.mk (Ideal.span {p} ⊔ Ideal.span {q}) p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_span_singleton_self p))
  let Ψ1 := Ideal.Quotient.lift _ (redMap hf) fun x hx ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, redMap_algebraMap, hq0, mul_zero]
  let Ψ2 := Ideal.Quotient.lift _ Ψ1 fun x hx ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, Ideal.Quotient.lift_mk, redMap_algebraMap, hp0, mul_zero]
  refine isReduced_of_injective Ψ2 ((injective_iff_map_eq_zero Ψ2).mpr fun w hw ↦ ?_)
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hx : redMap hf x = 0 := hw
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (Ideal.span {f}) x)
  have hb0 : b ∈ Ideal.span {p} ⊔ Ideal.span {q} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hx, redMap, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hb, Ideal.Quotient.factor_mk]
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Submodule.mem_sup.mp hb0
  obtain ⟨c1, rfl⟩ := Ideal.mem_span_singleton'.mp hb1
  obtain ⟨c2, rfl⟩ := Ideal.mem_span_singleton'.mp hb2
  have hk : x - algebraMap B _ (c1 * p + c2 * q) ∈
      RingHom.ker (AdicCompletion.evalOneₐ (Ideal.span {f})).toRingHom := by
    rw [RingHom.mem_ker, map_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      evalOneₐ_algebraMap, ← hb, sub_self]
  rw [AdicCompletion.ker_evalOneₐ_eq_map _ (Submodule.fg_span_singleton _), Ideal.map_span,
    Set.image_singleton] at hk
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hk
  have hxe : x = algebraMap B _ p * (algebraMap B _ c1 + d) +
      algebraMap B _ q * (algebraMap B _ c2 + d) := by
    have hpq : algebraMap B (AdicCompletion (Ideal.span {f}) B) f =
        algebraMap B _ p + algebraMap B _ q := by rw [← map_add, ← hf]
    rw [hpq] at hd
    simp only [map_add, map_mul] at hd
    linear_combination -hd
  have hq1 : Ideal.Quotient.mk (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {f}) B) q})
      (algebraMap B _ q) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [hxe, map_add, map_mul, map_mul, hq1, zero_mul, add_zero, map_mul,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), zero_mul]

end Completion

/-! ### A flat chart over the node ring -/

section Chart

open KummerEtale AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {π : O} {e : ℕ}
  {R : Type u} [CommRing R] [Algebra O R] [Algebra (A π e) R] [IsScalarTower O (A π e) R]

lemma J_eq_map :
    J θ (R := R) = (Node.IN (RingHom.ker θ) (π ^ e)).map (algebraMap (A π e) R) := by
  rw [Node.IN, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

variable [Module.Flat (A π e) R] (hπe : θ (π ^ e) = 0)
include hπe

/-- `(0 : ū²) ⊆ (v̄)` on the special fibre `R/J` of a flat chart over the node ring. -/
theorem mem_span_special_v {z : R ⧸ J θ}
    (hz : Ideal.Quotient.mk (J θ) (algebraMap (A π e) R (Node.u _)) ^ 2 * z = 0) :
    z ∈ Ideal.span {Ideal.Quotient.mk (J θ (R := R)) (algebraMap (A π e) R (Node.v _))} := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hy : algebraMap (A π e) R (Node.u _ ^ 2) * y ∈
      (Node.IN (RingHom.ker θ) (π ^ e)).map (algebraMap (A π e) R) := by
    rw [← J_eq_map, ← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_pow]
    exact hz
  have h := mem_map_sup_of_flat _
    (fun x hx ↦ mem_sup_of_u_sq_mul _ (RingHom.mem_ker.mpr hπe) hx) hy
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, ← J_eq_map] at h
  obtain ⟨p, hp, j, hj, rfl⟩ := Submodule.mem_sup.mp h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, add_zero, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- `(0 : v̄²) ⊆ (ū)` on the special fibre `R/J` of a flat chart over the node ring. -/
theorem mem_span_special_u {z : R ⧸ J θ}
    (hz : Ideal.Quotient.mk (J θ) (algebraMap (A π e) R (Node.v _)) ^ 2 * z = 0) :
    z ∈ Ideal.span {Ideal.Quotient.mk (J θ (R := R)) (algebraMap (A π e) R (Node.u _))} := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hy : algebraMap (A π e) R (Node.v _ ^ 2) * y ∈
      (Node.IN (RingHom.ker θ) (π ^ e)).map (algebraMap (A π e) R) := by
    rw [← J_eq_map, ← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_pow]
    exact hz
  have h := mem_map_sup_of_flat _
    (fun x hx ↦ mem_sup_of_v_sq_mul _ (RingHom.mem_ker.mpr hπe) hx) hy
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, ← J_eq_map] at h
  obtain ⟨p, hp, j, hj, rfl⟩ := Submodule.mem_sup.mp h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, add_zero, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

variable [IsNoetherianRing R] [Algebra k (R ⧸ J θ)]

omit [Module.Flat (A π e) R] [IsNoetherianRing R] in
/-- The formal node coordinates `ū, v̄` and `f̄ = ū + v̄`. -/
lemma φ_add :
    NodeChart.φ R hπe (Node.u 0) + NodeChart.φ R hπe (Node.v 0) =
      algebraMap (R ⧸ J θ) _ (fbar θ (NodeChart.fR (π := π) (e := e) R)) := by
  rw [NodeChart.φ_u, NodeChart.φ_v, NodeChart.bar, NodeChart.bar, ← map_add, ← map_add,
    ← map_add]

omit [Module.Flat (A π e) R] [IsNoetherianRing R] in
lemma φ_u_mul_φ_v : NodeChart.φ R hπe (Node.u 0) * NodeChart.φ R hπe (Node.v 0) = 0 := by
  rw [← map_mul, Node.u_mul_v, AlgHom.commutes]
  exact map_zero (algebraMap k _)

theorem hat_mem_span_v {x : Admissible.Hat (fbar θ (NodeChart.fR (π := π) (e := e) R))}
    (hx : NodeChart.φ R hπe (Node.u 0) ^ 2 * x = 0) :
    x ∈ Ideal.span {NodeChart.φ R hπe (Node.v 0)} := by
  rw [NodeChart.φ_v]
  rw [NodeChart.φ_u] at hx
  exact mem_span_completion _ (fun z hz ↦ mem_span_special_v hπe hz) hx

theorem hat_mem_span_u {x : Admissible.Hat (fbar θ (NodeChart.fR (π := π) (e := e) R))}
    (hx : NodeChart.φ R hπe (Node.v 0) ^ 2 * x = 0) :
    x ∈ Ideal.span {NodeChart.φ R hπe (Node.u 0)} := by
  rw [NodeChart.φ_u]
  rw [NodeChart.φ_v] at hx
  exact mem_span_completion _ (fun z hz ↦ mem_span_special_u hπe hz) hx

omit [Module.Flat (A π e) R] [IsNoetherianRing R] in
theorem hat_sep (a : Admissible.Hat (fbar θ (NodeChart.fR (π := π) (e := e) R)))
    (ha : ∀ m : ℕ,
      (NodeChart.φ R hπe (Node.u 0) + NodeChart.φ R hπe (Node.v 0)) ^ m ∣ a) :
    a = 0 := by
  rw [φ_add] at ha
  refine IsHausdorff.haus (inferInstance : IsHausdorff
    (Ideal.span {fbar θ (NodeChart.fR (π := π) (e := e) R)})
    (Admissible.Hat (fbar θ (NodeChart.fR (π := π) (e := e) R)))) a fun m ↦ ?_
  obtain ⟨c, rfl⟩ := ha m
  rw [SModEq.zero, ← map_pow, ← Algebra.smul_def]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m)
    Submodule.mem_top

end Chart


/-! ### The base hypotheses on `R̂/(1 − ε)` -/

section Piece

open KummerEtale AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {π : O} {e : ℕ}
  {R : Type u} [CommRing R] [Algebra O R] [Algebra (A π e) R] [IsScalarTower O (A π e) R]
  [Module.Flat (A π e) R] [IsNoetherianRing R] [Algebra k (R ⧸ J θ)] (hπe : θ (π ^ e) = 0)

/-- The reduced special fibre at the nodes: `(R/J)/(ū, v̄)` is reduced. -/
abbrev NodeRed (θ : O →+* k) (π : O) (e : ℕ) (R : Type u) [CommRing R] [Algebra O R]
    [Algebra (A π e) R] : Prop :=
  IsReduced ((R ⧸ J θ) ⧸
    (Ideal.span {Ideal.Quotient.mk (J θ (R := R)) (algebraMap (A π e) R (Node.u _))} ⊔
      Ideal.span {Ideal.Quotient.mk (J θ (R := R)) (algebraMap (A π e) R (Node.v _))}))

include hπe

omit [Module.Flat (A π e) R] [IsNoetherianRing R] in
lemma hat_isReduced_v (hred : NodeRed θ π e R) :
    IsReduced ((Admissible.Hat (fbar θ (NodeChart.fR (π := π) (e := e) R)) ⧸
      Ideal.span {NodeChart.φ R hπe (Node.v 0)}) ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span {NodeChart.φ R hπe (Node.v 0)})
        (NodeChart.φ R hπe (Node.u 0))}) := by
  rw [NodeChart.φ_u, NodeChart.φ_v]
  exact isReduced_completion_quot (by rw [← map_add, ← map_add]) hred

omit [Module.Flat (A π e) R] [IsNoetherianRing R] in
lemma hat_isReduced_u (hred : NodeRed θ π e R) :
    IsReduced ((Admissible.Hat (fbar θ (NodeChart.fR (π := π) (e := e) R)) ⧸
      Ideal.span {NodeChart.φ R hπe (Node.u 0)}) ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span {NodeChart.φ R hπe (Node.u 0)})
        (NodeChart.φ R hπe (Node.v 0))}) := by
  rw [NodeRed, sup_comm] at hred
  rw [NodeChart.φ_u, NodeChart.φ_v]
  exact isReduced_completion_quot (by rw [← map_add, ← map_add, add_comm]) hred

variable (ε : Admissible.Hat (fbar θ (NodeChart.fR (π := π) (e := e) R))) {e' : ℕ}
  (he : 0 < e')

omit [Module.Flat (A π e) R] [IsNoetherianRing R] in
lemma nodeMap_u : Admissible.PieceBase.nodeMap (NodeChart.φ R hπe) ε he (Node.u ((0 : k) ^ e')) =
    Ideal.Quotient.mk (Ideal.span {1 - ε}) (NodeChart.φ R hπe (Node.u 0)) := by
  change Ideal.Quotient.mk _ (NodeChart.φ R hπe (Admissible.nodeCongr he (Node.u _))) = _
  rw [NodeChart.nodeCongr_u]

omit [Module.Flat (A π e) R] [IsNoetherianRing R] in
lemma nodeMap_v : Admissible.PieceBase.nodeMap (NodeChart.φ R hπe) ε he (Node.v ((0 : k) ^ e')) =
    Ideal.Quotient.mk (Ideal.span {1 - ε}) (NodeChart.φ R hπe (Node.v 0)) := by
  change Ideal.Quotient.mk _ (NodeChart.φ R hπe (Admissible.nodeCongr he (Node.v _))) = _
  rw [NodeChart.nodeCongr_v]

variable {ε} (hε : IsIdempotentElem ε)
include hε

/-- **Hypothesis (1)**: `ū` satisfies the cusp normal form hypotheses on
`(R̂/(1 − ε))/(v̄)`. -/
theorem pieceBase_nfHyp_u (hred : NodeRed θ π e R) :
    CuspHom.NFHyp (Admissible.PieceBase (NodeChart.φ R hπe) ε he ⧸
        Ideal.span
          {Admissible.PieceBase.nodeMap (NodeChart.φ R hπe) ε he (Node.v ((0 : k) ^ e'))})
      (Ideal.Quotient.mk _
        (Admissible.PieceBase.nodeMap (NodeChart.φ R hπe) ε he (Node.u ((0 : k) ^ e')))) := by
  rw [nodeMap_u, nodeMap_v]
  exact nfHyp_corner_quot (φ_u_mul_φ_v hπe) (fun x hx ↦ hat_mem_span_v hπe hx) hε
    (hat_sep hπe) (hat_isReduced_v hπe hred)

/-- **Hypothesis (2)**: `v̄` satisfies the cusp normal form hypotheses on
`(R̂/(1 − ε))/(ū)`. -/
theorem pieceBase_nfHyp_v (hred : NodeRed θ π e R) :
    CuspHom.NFHyp (Admissible.PieceBase (NodeChart.φ R hπe) ε he ⧸
        Ideal.span
          {Admissible.PieceBase.nodeMap (NodeChart.φ R hπe) ε he (Node.u ((0 : k) ^ e'))})
      (Ideal.Quotient.mk _
        (Admissible.PieceBase.nodeMap (NodeChart.φ R hπe) ε he (Node.v ((0 : k) ^ e')))) := by
  rw [nodeMap_u, nodeMap_v]
  exact nfHyp_corner_quot (by rw [mul_comm]; exact φ_u_mul_φ_v hπe)
    (fun x hx ↦ hat_mem_span_u hπe hx) hε
    (fun a ha ↦ hat_sep hπe a fun m ↦ by rw [add_comm]; exact ha m) (hat_isReduced_u hπe hred)

/-- **Hypothesis (3)**: `(ū) ∩ (v̄) = 0` in `R̂/(1 − ε)`. -/
theorem pieceBase_inter (p : Admissible.PieceBase (NodeChart.φ R hπe) ε he)
    (hpu : p ∈ Ideal.span
      {Admissible.PieceBase.nodeMap (NodeChart.φ R hπe) ε he (Node.u ((0 : k) ^ e'))})
    (hpv : p ∈ Ideal.span
      {Admissible.PieceBase.nodeMap (NodeChart.φ R hπe) ε he (Node.v ((0 : k) ^ e'))}) :
    p = 0 := by
  rw [nodeMap_u] at hpu
  rw [nodeMap_v] at hpv
  exact inter_corner (φ_u_mul_φ_v hπe) (fun x hx ↦ hat_mem_span_v hπe hx) hε p hpu hpv

end Piece


/-! ### The quadratic node chart -/

section Quad

open KummerEtale AdmissibleLift

lemma isReduced_of_surjective_squarefree {k B : Type*} [Field k] [CommRing B] (f : k[X] →+* B)
    (hf : Function.Surjective f) {g : k[X]} (hg : Squarefree g) (hfg : f g = 0) : IsReduced B := by
  have hd : Submodule.IsPrincipal.generator (RingHom.ker f) ∣ g :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd (RingHom.ker f)).1 hfg
  rw [← RingHom.ker_isRadical_iff_reduced_of_surjective hf,
    ← Submodule.IsPrincipal.span_singleton_generator (RingHom.ker f),
    ← isRadical_iff_span_singleton]
  exact (hg.squarefree_of_dvd hd).isRadical

lemma squarefree_X_sq_add_X {k : Type*} [Field k] : Squarefree (X ^ 2 + X : k[X]) := by
  refine Polynomial.Separable.squarefree ⟨-4, 2 * X + 1, ?_⟩
  have hd : derivative (X ^ 2 + X : k[X]) = 2 * X + 1 := by
    simp only [derivative_add, derivative_X_pow, derivative_X]
    norm_num
    exact map_ofNat C 2
  rw [hd]
  ring

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {π : O} {e : ℕ}

omit hθ in
lemma root_sq_add_root (c : A π e) (R' : Type*) [CommRing R'] [Algebra (A π e) R']
    [Algebra (QuadNode.Q π e c) R'] [IsScalarTower (A π e) (QuadNode.Q π e c) R'] :
    algebraMap (QuadNode.Q π e c) (R') (AdjoinRoot.root _) ^ 2 +
      algebraMap (QuadNode.Q π e c) (R') (AdjoinRoot.root _) =
      algebraMap (A π e) (R') c := by
  have h : AdjoinRoot.mk (QuadraticEtale.poly c) (X ^ 2 + X - C c) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  have h' := congrArg (algebraMap (QuadNode.Q π e c) (R')) h
  rw [map_sub, map_add, map_pow (algebraMap (QuadNode.Q π e c) (R')),
    map_zero (algebraMap (QuadNode.Q π e c) (R')),
    show algebraMap (QuadNode.Q π e c) (R') (AdjoinRoot.of _ c) =
      algebraMap (A π e) (R') c from
      (IsScalarTower.algebraMap_apply (A π e) (QuadNode.Q π e c) _ c).symm, sub_eq_zero] at h'
  exact h'

omit hθ in
/-- A ring map out of `O[u,v]/(uv − a)` lands in a subring containing the images of `O`, `u`,
`v`. -/
lemma node_mem {T : Type*} [CommRing T] (g : A π e →+* T) (F' : Subring T)
    (hO : ∀ o : O, g (algebraMap O (A π e) o) ∈ F') (hu : g (Node.u (π ^ e)) ∈ F')
    (hv : g (Node.v (π ^ e)) ∈ F') (a : A π e) : g a ∈ F' := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C o =>
    exact hO o
  | add p q hp hq =>
    rw [map_add, map_add]
    exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine mul_mem hp ?_
    fin_cases i
    · exact hu
    · exact hv

/-- A ring map out of `A'[X]/(f)` lands in a subring containing the images of `A'` and the
root. -/
lemma adjoinRoot_mem {A' T : Type*} [CommRing A'] [CommRing T] {f : A'[X]}
    (g : AdjoinRoot f →+* T) (F' : Subring T) (hA : ∀ a, g (AdjoinRoot.of f a) ∈ F')
    (hr : g (AdjoinRoot.root f) ∈ F') (q : AdjoinRoot f) : g q ∈ F' := by
  induction q using AdjoinRoot.induction_on with
  | ih p => ?_
  induction p using Polynomial.induction_on with
  | C a =>
    rw [AdjoinRoot.mk_C]
    exact hA a
  | add p q hp hq =>
    rw [map_add, map_add]
    exact add_mem hp hq
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X, map_mul]
    exact mul_mem ih hr

/-- A ring map out of `Q[1/d]` with `d ↦ 1` lands in a subring containing the image of `Q`. -/
lemma away_mem {Q' R' T : Type*} [CommRing Q'] [CommRing R'] [CommRing T] [Algebra Q' R']
    (d : Q') [IsLocalization.Away d R'] (g : R' →+* T) (F' : Subring T)
    (hd : g (algebraMap Q' R' d) = 1) (hQ : ∀ q, g (algebraMap Q' R' q) ∈ F') (r : R') :
    g r ∈ F' := by
  obtain ⟨⟨q, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers d) r
  obtain ⟨n, hn⟩ := s.2
  have hspec := congrArg g (IsLocalization.mk'_spec R' q s)
  rw [map_mul, ← hn, map_pow (algebraMap Q' R'), map_pow g, hd, one_pow, mul_one] at hspec
  change g (IsLocalization.mk' R' q s) ∈ F'
  rw [hspec]
  exact hQ q

/-- **The quadratic node chart has reduced special fibre at the nodes** if `c` and `D − 1` lie in
`(u, v)`: then `(R/J)/(ū, v̄) = k[S]/(S² + S)`. -/
theorem nodeRed_of {c D : A π e} (R' : Type u) [CommRing R'] [Algebra O R'] [Algebra (A π e) R']
    [IsScalarTower O (A π e) R'] [Algebra (QuadNode.Q π e c) R']
    [IsScalarTower (A π e) (QuadNode.Q π e c) R']
    [IsLocalization.Away (AdjoinRoot.of (QuadraticEtale.poly c) D) R']
    (hc : c ∈ Ideal.span {Node.u (π ^ e)} ⊔ Ideal.span {Node.v (π ^ e)})
    (hD : D - 1 ∈ Ideal.span {Node.u (π ^ e)} ⊔ Ideal.span {Node.v (π ^ e)}) :
    NodeRed θ π e R' := by
  set K : Ideal (R' ⧸ J θ) :=
    Ideal.span {Ideal.Quotient.mk (J θ) (algebraMap (A π e) _ (Node.u _))} ⊔
      Ideal.span {Ideal.Quotient.mk (J θ) (algebraMap (A π e) _ (Node.v _))}
  set πB : R' →+* (R' ⧸ J θ) ⧸ K :=
    (Ideal.Quotient.mk K).comp (Ideal.Quotient.mk (J θ)) with hπB
  have hle : Ideal.span {Node.u (π ^ e)} ⊔ Ideal.span {Node.v (π ^ e)} ≤
      RingHom.ker (πB.comp (algebraMap (A π e) (R'))) := by
    refine sup_le ?_ ?_ <;> rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      RingHom.mem_ker, RingHom.comp_apply, hπB, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hA0 : ∀ a ∈ Ideal.span {Node.u (π ^ e)} ⊔ Ideal.span {Node.v (π ^ e)},
      πB (algebraMap (A π e) (R') a) = 0 := fun a ha ↦ hle ha
  set S : R' := algebraMap (QuadNode.Q π e c) R' (AdjoinRoot.root _) with hS
  set F : k[X] →+* (R' ⧸ J θ) ⧸ K :=
    Polynomial.eval₂RingHom ((Ideal.Quotient.mk K).comp (kMap hθ.out)) (πB S) with hF
  have hO (o : O) : πB (algebraMap O (R') o) ∈ F.range := by
    refine ⟨C (θ o), ?_⟩
    rw [hF, Polynomial.coe_eval₂RingHom, eval₂_C, RingHom.comp_apply, kMap_θ, hπB,
      RingHom.comp_apply]
  have hArange (a : A π e) : πB (algebraMap (A π e) (R') a) ∈ F.range :=
    node_mem (πB.comp (algebraMap (A π e) (R'))) F.range
      (fun o ↦ by
        rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply O (A π e) R' o]
        exact hO o)
      (by rw [RingHom.comp_apply, hA0 _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))]
          exact zero_mem _)
      (by rw [RingHom.comp_apply, hA0 _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))]
          exact zero_mem _) a
  have hQrange (q : QuadNode.Q π e c) :
      πB (algebraMap (QuadNode.Q π e c) (R') q) ∈ F.range :=
    adjoinRoot_mem (πB.comp (algebraMap (QuadNode.Q π e c) (R'))) F.range
      (fun a ↦ by
        have h := hArange a
        rw [IsScalarTower.algebraMap_apply (A π e) (QuadNode.Q π e c) R' a] at h
        exact h)
      ⟨X, by rw [hF, Polynomial.coe_eval₂RingHom, eval₂_X, RingHom.comp_apply]; rfl⟩ q
  have hD1 : πB (algebraMap (QuadNode.Q π e c) (R')
      (AdjoinRoot.of (QuadraticEtale.poly c) D)) = 1 := by
    rw [show algebraMap (QuadNode.Q π e c) (R') (AdjoinRoot.of _ D) =
      algebraMap (A π e) (R') D from
      (IsScalarTower.algebraMap_apply (A π e) (QuadNode.Q π e c) _ D).symm,
      show D = 1 + (D - 1) by ring, map_add (algebraMap (A π e) (R')),
      map_add πB, hA0 _ hD, add_zero, map_one (algebraMap (A π e) (R')),
      map_one πB]
  have hsurj : Function.Surjective F := by
    intro b
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact RingHom.mem_range.mp
      (away_mem (AdjoinRoot.of (QuadraticEtale.poly c) D) πB F.range hD1 hQrange r)
  have hFg : F (X ^ 2 + X) = 0 := by
    have h1 : F (X ^ 2 + X) = πB (S ^ 2 + S) := by
      rw [hF, Polynomial.coe_eval₂RingHom, eval₂_add, eval₂_X_pow, eval₂_X, map_add πB,
        map_pow πB]
    rw [h1, hS, root_sq_add_root c R', hA0 _ hc]
  exact isReduced_of_surjective_squarefree F hsurj squarefree_X_sq_add_X hFg

/-- **The quadratic node chart has reduced special fibre at the nodes.** -/
theorem nodeRed_quadNode (c D : A π e)
    (hc : c ∈ Ideal.span {Node.u (π ^ e)} ⊔ Ideal.span {Node.v (π ^ e)})
    (hD : D - 1 ∈ Ideal.span {Node.u (π ^ e)} ⊔ Ideal.span {Node.v (π ^ e)}) :
    NodeRed θ π e (QuadNode.R π e c D) :=
  nodeRed_of (D := D) (QuadNode.R π e c D) hc hD

end Quad

end NodeNF

/-! ### The Tate node chart -/

namespace TateGlue1

open TateTwoChartNode KummerEtale AdmissibleLift NodeNF

variable {O : Type u} [CommRing O] [IsNoetherianRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ ε : O} {m : ℕ}

omit [IsNoetherianRing O] in
lemma cN_mem :
    cN b₄ b₆ ϖ m ε ∈ Ideal.span {Node.u (ϖ ^ m)} ⊔ Ideal.span {Node.v (ϖ ^ m)} :=
  Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_left (Ideal.mul_mem_left _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) 2 two_pos)))

omit [IsNoetherianRing O] in
lemma DN_sub_one_mem :
    DN b₄ ϖ m - 1 ∈ Ideal.span {Node.u (ϖ ^ m)} ⊔ Ideal.span {Node.v (ϖ ^ m)} := by
  rw [DN, add_sub_cancel_left]
  exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _
    (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) 2 two_pos))

omit [IsNoetherianRing O] in
/-- **The Tate node chart has reduced special fibre at the nodes.** -/
theorem nodeRed : NodeRed θ ϖ m (Rb b₄ b₆ ϖ m ε) :=
  nodeRed_quadNode _ _ cN_mem DN_sub_one_mem

variable (hπe : θ (ϖ ^ m) = 0)
  {εi : Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) (Rb b₄ b₆ ϖ m ε)))}
  (hεi : IsIdempotentElem εi) {e : ℕ} (he : 0 < e)
include hεi

/-- **Hypothesis (1) of `Admissible.kummerPiece_nfHyp_s` at the Tate node chart**, for every
idempotent `ε` of `R̂`. -/
theorem pieceBase_nfHyp_u :
    CuspHom.NFHyp (Admissible.PieceBase (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) εi he ⧸
        Ideal.span {Admissible.PieceBase.nodeMap (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) εi he
          (Node.v ((0 : k) ^ e))})
      (Ideal.Quotient.mk _ (Admissible.PieceBase.nodeMap
        (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) εi he (Node.u ((0 : k) ^ e)))) :=
  NodeNF.pieceBase_nfHyp_u hπe he hεi nodeRed

/-- **Hypothesis (2) of `Admissible.kummerPiece_nfHyp_t` at the Tate node chart.** -/
theorem pieceBase_nfHyp_v :
    CuspHom.NFHyp (Admissible.PieceBase (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) εi he ⧸
        Ideal.span {Admissible.PieceBase.nodeMap (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) εi he
          (Node.u ((0 : k) ^ e))})
      (Ideal.Quotient.mk _ (Admissible.PieceBase.nodeMap
        (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) εi he (Node.v ((0 : k) ^ e)))) :=
  NodeNF.pieceBase_nfHyp_v hπe he hεi nodeRed

/-- **Hypothesis (3) of `Admissible.kummerPiece_hinter` at the Tate node chart.** -/
theorem pieceBase_inter (p : Admissible.PieceBase (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) εi he)
    (hpu : p ∈ Ideal.span {Admissible.PieceBase.nodeMap (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe)
      εi he (Node.u ((0 : k) ^ e))})
    (hpv : p ∈ Ideal.span {Admissible.PieceBase.nodeMap (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe)
      εi he (Node.v ((0 : k) ^ e))}) : p = 0 :=
  NodeNF.pieceBase_inter hπe he hεi p hpu hpv

/-! ### The Kummer factors of `cov₀` -/

variable {ψ : Polynomial k →ₐ[k]
    Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) (Rb b₄ b₆ ϖ m ε)))}
  (cov₀ : Admissible.Covering (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) ψ) (j : cov₀.ι)

omit hεi in
/-- **The `s`-branch of a Kummer factor of the Tate covering `cov₀`** satisfies the cusp normal
form hypotheses. -/
theorem cov₀_nfHyp_s :
    CuspHom.NFHyp (Admissible.KummerPiece (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) (cov₀.idem j)
        (cov₀.e_pos j) ⧸
        Ideal.span {(1 : Admissible.PieceBase (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe)
          (cov₀.idem j) (cov₀.e_pos j)) ⊗ₜ[A (0 : k) (cov₀.e j)] Node.v (0 : k)})
      (Ideal.Quotient.mk _ ((1 : Admissible.PieceBase (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe)
        (cov₀.idem j) (cov₀.e_pos j)) ⊗ₜ[A (0 : k) (cov₀.e j)] Node.u (0 : k))) :=
  Admissible.kummerPiece_nfHyp_s _ _ _
    (pieceBase_nfHyp_u hπe (cov₀.isIdempotentElem_idem j) (cov₀.e_pos j))

omit hεi in
/-- **The `t`-branch of a Kummer factor of the Tate covering `cov₀`.** -/
theorem cov₀_nfHyp_t :
    CuspHom.NFHyp (Admissible.KummerPiece (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) (cov₀.idem j)
        (cov₀.e_pos j) ⧸
        Ideal.span {(1 : Admissible.PieceBase (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe)
          (cov₀.idem j) (cov₀.e_pos j)) ⊗ₜ[A (0 : k) (cov₀.e j)] Node.u (0 : k)})
      (Ideal.Quotient.mk _ ((1 : Admissible.PieceBase (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe)
        (cov₀.idem j) (cov₀.e_pos j)) ⊗ₜ[A (0 : k) (cov₀.e j)] Node.v (0 : k))) :=
  Admissible.kummerPiece_nfHyp_t _ _ _
    (pieceBase_nfHyp_v hπe (cov₀.isIdempotentElem_idem j) (cov₀.e_pos j))

omit hεi in
/-- **The two branches of a Kummer factor of the Tate covering `cov₀` meet in `0`.** -/
theorem cov₀_hinter
    (z : Admissible.KummerPiece (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe) (cov₀.idem j)
      (cov₀.e_pos j))
    (hzs : z ∈ Ideal.span {(1 : Admissible.PieceBase (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe)
      (cov₀.idem j) (cov₀.e_pos j)) ⊗ₜ[A (0 : k) (cov₀.e j)] Node.u (0 : k)})
    (hzt : z ∈ Ideal.span {(1 : Admissible.PieceBase (NodeChart.φ (Rb b₄ b₆ ϖ m ε) hπe)
      (cov₀.idem j) (cov₀.e_pos j)) ⊗ₜ[A (0 : k) (cov₀.e j)] Node.v (0 : k)}) : z = 0 :=
  Admissible.kummerPiece_hinter _ _ _
    (pieceBase_inter hπe (cov₀.isIdempotentElem_idem j) (cov₀.e_pos j)) z hzs hzt

end TateGlue1

end SemistableReduction
