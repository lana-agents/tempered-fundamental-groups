/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.OverlapKaehler

/-!
# Killing the differentials of a patch factor by factor (Blueprint §12.8, M2.5 (f), T1b)

`LevelTower.Level.kills_G` asks the killing constant `c` to be a multiple of the cusp coordinate
`t` on **every** cusp factor. A cusp factor of index `1` is `R̂/(1 − δ)` itself (unramified), so
there no condition is needed, and on a factor selected by `δ` it suffices that `c` is a multiple
of `t` modulo `1 − δ`. This is what makes the generic fibre étale at points of `V(t)` over which
the covering is unramified (in the Tate case the two points `[0 : ±√b₆ : 1]` of the cusp chart
`D(1 + h)`, which lie in `V(h)` but are not cusps).

* **`AdmissibleLift.kills_CPiece_one`**: a cusp factor of index `1` has no differentials over `R̂`;
* **`AdmissibleLift.kills_CPiece'`**: `c` kills the differentials of a cusp factor `(δ, t, e)` if
  `e = 1` or `c ∈ (t) + (1 − δ)`;
* **`LevelTower.Level.kills_G'`**, **`NodeEtaleGlue.PatchInput.kills_piece'`**: the patched
  algebras with this factor-wise condition.
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale

noncomputable section

namespace AdmissibleLift

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R] (f : R)

/-- **A cusp factor of index `1` is unramified**: `1` kills the differentials of
`(R̂/(1 − δ))[X]/(X − t)` over `R̂`. -/
theorem kills_CPiece_one (δ t : FormalPatchLevel.Hat f) :
    KaehlerLocal.Kills (FormalPatchLevel.Hat f) (1 : CPiece f δ t 1) := by
  haveI : Subsingleton Ω[(CBase f δ)⁄(FormalPatchLevel.Hat f)] :=
    KaehlerLocal.subsingleton_of_surjective _ _ Ideal.Quotient.mk_surjective
  refine KaehlerLocal.kills_of_base _ (CBase f δ) ?_
  have hroot : AdjoinRoot.root (cpoly f δ t 1) =
      algebraMap (CBase f δ) (CPiece f δ t 1) (Ideal.Quotient.mk _ t) := by
    have h := AdjoinRoot.eval₂_root (cpoly f δ t 1)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero,
      pow_one] at h
    exact h
  exact KaehlerLocal.kills_of_adjoin _ (s := {AdjoinRoot.root (cpoly f δ t 1)})
    AdjoinRoot.adjoinRoot_eq_top fun x hx ↦ by
      rw [Set.mem_singleton_iff.1 hx, hroot, Derivation.map_algebraMap, smul_zero]

/-- **The differentials of a lifted cusp factor, factor-wise**: `c` kills them if the index is
`1`, or if `c` is a multiple of the cusp coordinate `t` modulo `1 − δ`. -/
theorem kills_CPiece' (δ t : FormalPatchLevel.Hat f) {e : ℕ} (he : IsUnit (e : O)) (he0 : e ≠ 0)
    {c : FormalPatchLevel.Hat f} (hc : e = 1 ∨ ∃ r s, c = t * r + (1 - δ) * s) :
    KaehlerLocal.Kills (FormalPatchLevel.Hat f)
      (algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) c) := by
  rcases hc with rfl | ⟨r, s, rfl⟩
  · intro ω
    have h := kills_CPiece_one f δ t ω
    rw [one_smul] at h
    rw [h, smul_zero]
  · have h0 : algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e) (1 - δ) = 0 := by
      rw [IsScalarTower.algebraMap_apply (FormalPatchLevel.Hat f) (CBase f δ) (CPiece f δ t e)]
      have : algebraMap (FormalPatchLevel.Hat f) (CBase f δ) (1 - δ) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
      rw [this, map_zero]
    rw [map_add, map_mul (algebraMap _ _) (1 - δ), h0, zero_mul, add_zero]
    exact kills_CPiece f δ t he he0 ⟨r, rfl⟩

end AdmissibleLift

namespace IdemSplit

variable {S : Type*} [CommRing S]

/-- **An idempotent over `z = 0` modulo `t`** (pure algebra): if `z (1 + z w) ∈ (t)` (so that
modulo `t` the ring splits into the parts `z = 0` and `1 + z w = 0`), `δ` is idempotent and
`z δ ∈ (t) + N` for a nilpotent ideal `N`, then `z δ ∈ (t)`. -/
theorem mul_mem_span {t z w δ : S} {N : Ideal S} {m : ℕ} (hN : N ^ m = ⊥)
    (hza : z * (1 + z * w) ∈ Ideal.span {t}) (hδ : IsIdempotentElem δ)
    (hzδ : z * δ ∈ Ideal.span {t} ⊔ N) : z * δ ∈ Ideal.span {t} := by
  rcases m with _ | m
  · rw [pow_zero, Ideal.one_eq_top] at hN
    have : (1 : S) = 0 := by
      have h1 : (1 : S) ∈ (⊤ : Ideal S) := Submodule.mem_top
      rw [hN] at h1
      exact h1
    rw [show z * δ = 0 by rw [← one_mul (z * δ), this, zero_mul]]
    exact Ideal.zero_mem _
  set π := Ideal.Quotient.mk (Ideal.span {t})
  have hπ0 : ∀ {x : S}, x ∈ Ideal.span {t} ↔ π x = 0 := fun {_} ↦
    Ideal.Quotient.eq_zero_iff_mem.symm
  -- `y = - w z δ` is idempotent modulo `t` and lies in `N` modulo `t`
  have hy : IsIdempotentElem (π (-(w * (z * δ)))) := by
    have e : (-(w * (z * δ))) * (-(w * (z * δ))) - (-(w * (z * δ))) =
        w * δ * (z * (1 + z * w)) := by
      have : δ * δ = δ := hδ
      linear_combination (w * w * z * z) * this
    have h0 : π ((-(w * (z * δ))) * (-(w * (z * δ))) - (-(w * (z * δ)))) = 0 := by
      rw [e, map_mul, hπ0.1 hza, mul_zero]
    rw [map_sub, sub_eq_zero, map_mul] at h0
    exact h0
  have hyN : π (-(w * (z * δ))) ∈ N.map π := by
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hzδ
    have : π (z * δ) = π b := by rw [← hab, map_add, hπ0.1 ha, zero_add]
    rw [map_neg, map_mul, this, ← map_mul]
    exact (N.map π).neg_mem (Ideal.mem_map_of_mem π (N.mul_mem_left w hb))
  have hy0 : π (-(w * (z * δ))) = 0 := by
    have hpow : π (-(w * (z * δ))) ^ (m + 1) = π (-(w * (z * δ))) := hy.pow_succ_eq m
    rw [← hpow]
    have : π (-(w * (z * δ))) ^ (m + 1) ∈ (N.map π) ^ (m + 1) := Ideal.pow_mem_pow hyN _
    rw [← Ideal.map_pow, hN, Ideal.map_bot] at this
    exact this
  rw [hπ0]
  have e : z * δ = (z * (1 + z * w)) * δ + z * (-(w * (z * δ))) := by ring
  have h1 : π (z * (1 + z * w) * δ) = 0 := by rw [map_mul, hπ0.1 hza, zero_mul]
  have h2 : π (z * -(w * (z * δ))) = 0 := by rw [map_mul, hy0, mul_zero]
  rw [e, map_add, h1, h2, add_zero]

end IdemSplit

namespace LevelTower

open AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

include hO in
/-- **The differentials of the patched level algebra, factor-wise** (`Level.kills_G` with the
cusp condition only on the ramified factors, and only modulo `1 − δᵢ`). -/
theorem Level.kills_G' {n : ℕ} (D : Level R cov₀ πL hfe n) {c : R n}
    (hK : ∀ j, ∃ r, algebraMap (R n) (FormalPatchLevel.Hat (f n)) c =
      algebraMap O (FormalPatchLevel.Hat (f n)) (πL j) ^
        ((cov₀.transport (h := hfe n)).e j - 1) * r)
    (hC : ∀ i : (cov₀.transport (h := hfe n)).κ, cov₀.ce i = 1 ∨ ∃ r s,
      algebraMap (R n) (FormalPatchLevel.Hat (f n)) c = D.M.t * r + (1 - D.M.δ i) * s) :
    KaehlerLocal.Kills (R n) (algebraMap (R n) (D.G hθ) c) := by
  obtain ⟨hfin, hloc, hbc⟩ := Level.spec hθ hO D
  refine GlueKaehler.kills_glued (f n) (NFall D.L D.M) _ hfin hloc hbc ?_
  rw [IsScalarTower.algebraMap_apply (R n) (FormalPatchLevel.Hat (f n)) (NFall D.L D.M)]
  refine KaehlerLocal.kills_pi _ (NF D.L D.M) fun s ↦ ?_
  rcases s with j | i
  · exact kills_N (f n) (D.L.χ j) (D.L.ε j)
      (hO _ (by rw [map_natCast]; exact (cov₀.transport (h := hfe n)).e_ne_zero j)) (hK j)
  · exact kills_CPiece' (f n) (D.M.δ i) D.M.t
      (hO _ (by rw [map_natCast]; exact (cov₀.transport (h := hfe n)).ce_ne_zero i))
      ((cov₀.transport (h := hfe n)).ce_pos i).ne' (hC i)

/-- **The lifted cusp idempotents over `z = 0`**: let `z ∈ R n` reduce to `z₀` on the special
fibre, with `z (1 + z w) ∈ (t)` in `R̂ n` (the zero locus of `t` splits into `z = 0` and
`1 + z w = 0`). If on the special fibre `z₀ · cidemᵢ` is a multiple of the coordinate `ψ₀ X` at
the marked points (the factor `i` lies over `z = 0`), then in `R̂ n` the element `z` is a multiple
of `t` modulo `1 − δᵢ`, for the lifted idempotent `δᵢ` of the level. -/
theorem Level.exists_eq_t_mul {n : ℕ}
    (D : Level R cov₀ πL hfe n) {z w : R n} {z₀ : R₀}
    (hz : e n z₀ = Ideal.Quotient.mk _ z)
    (hza : algebraMap (R n) (FormalPatchLevel.Hat (f n)) z *
      (1 + algebraMap (R n) (FormalPatchLevel.Hat (f n)) z *
        algebraMap (R n) (FormalPatchLevel.Hat (f n)) w) ∈ Ideal.span {D.M.t})
    (i : cov₀.κ)
    (hspec : ∃ r, algebraMap R₀ (Admissible.Hat f₀) z₀ * cov₀.cidem i = ψ₀ Polynomial.X * r) :
    ∃ r s, algebraMap (R n) (FormalPatchLevel.Hat (f n)) z = D.M.t * r + (1 - D.M.δ i) * s := by
  set Z := algebraMap (R n) (FormalPatchLevel.Hat (f n)) z
  have hδ : IsIdempotentElem (D.M.δ i) := D.hcidem i
  obtain ⟨r₀, hr₀⟩ := hspec
  obtain ⟨r, hr⟩ := surjective_ψ θ (f n) (Admissible.hatEquiv (e n) (hfe n) r₀)
  have hψZ : ψ θ (f n) Z = Admissible.hatEquiv (e n) (hfe n)
      (algebraMap R₀ (Admissible.Hat f₀) z₀) := by
    rw [Admissible.hatEquiv_algebraMap, hz, AlgHom.commutes,
      IsScalarTower.algebraMap_apply (R n) (R n ⧸ J θ), Ideal.Quotient.algebraMap_eq]
  have hker : Z * D.M.δ i - D.M.t * r ∈ RingHom.ker (ψ θ (f n)) := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_mul, hψZ, D.M.hδ i, D.M.ht, hr]
    change Admissible.hatEquiv (e n) (hfe n) (algebraMap R₀ (Admissible.Hat f₀) z₀) *
        Admissible.hatEquiv (e n) (hfe n) (cov₀.cidem i) -
      Admissible.hatEquiv (e n) (hfe n) (ψ₀ Polynomial.X) *
        Admissible.hatEquiv (e n) (hfe n) r₀ = 0
    rw [← map_mul, ← map_mul, hr₀, sub_self]
  have hN : (RingHom.ker (ψ θ (f n))) ^ D.m = ⊥ := by
    rw [ker_ψ, ← Ideal.map_pow, D.hJ, Ideal.map_bot]
  have hzδ : Z * D.M.δ i ∈ Ideal.span {D.M.t} ⊔ RingHom.ker (ψ θ (f n)) := by
    have : Z * D.M.δ i = D.M.t * r + (Z * D.M.δ i - D.M.t * r) := by ring
    rw [this]
    exact Submodule.add_mem_sup (Ideal.mem_span_singleton'.2 ⟨r, mul_comm _ _⟩) hker
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (IdemSplit.mul_mem_span hN hza hδ hzδ)
  exact ⟨q, Z, by rw [mul_comm D.M.t q, hq]; ring⟩

end LevelTower

namespace NodeEtaleGlue

namespace PatchInput

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  (D : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

include hO in
/-- **The differentials of a formal patch without nodes, factor-wise**: an element `d ∈ B' n`
whose image in `R̂ n` is, on every ramified cusp factor `i`, a multiple of the cusp coordinate
modulo `1 − δᵢ` kills the differentials of the piece `G n` over `B' n`. -/
theorem kills_piece' [IsEmpty cov₀.ι] (d : B' n)
    (hC : ∀ i : cov₀.κ, cov₀.ce i = 1 ∨ ∃ r s, algebraMap (D.R n)
      (FormalPatchLevel.Hat (D.T.f n)) (algebraMap (B' n) (D.R n) d) =
        D.T.t n * r + (1 - (D.T.level n).M.δ i) * s) :
    KaehlerLocal.Kills (B' n) (algebraMap (B' n) ((D.piece hθ hO).P n) d) := by
  haveI : Algebra.FormallyUnramified (B' n) (D.R n) :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers (algebraMap B0' (B' n) c0))
  refine KaehlerLocal.kills_of_base (B' n) (D.R n) (S := D.G hθ n) ?_
  exact (D.T.level n).kills_G' hθ hO (fun j ↦ isEmptyElim j) hC

end PatchInput

end NodeEtaleGlue

end

end SemistableReduction
