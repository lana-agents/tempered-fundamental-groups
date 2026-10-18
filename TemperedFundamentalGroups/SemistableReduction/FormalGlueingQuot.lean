/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Ideal.Over
import TemperedFundamentalGroups.SemistableReduction.FormalGlueing
import TemperedFundamentalGroups.SemistableReduction.CompletionQuot
import TemperedFundamentalGroups.SemistableReduction.FormalPatchLevel

/-!
# Formal glueing commutes with reduction (Blueprint §12.8, M2.3 (e'))

The formal patching produces at each level `n` a glued algebra `G_n = P_n ×_{Q_n} N_n` over the
chart `R_n` of the model modulo `ϖⁿ⁺¹`. To obtain an adic system (input of Grothendieck existence,
`AdicChartAlgSystem`) one needs `G_{n+1}/ϖⁿ⁺¹ ≅ G_n`. Generic statement
(**`FormalGlueingQuot.equiv`**): for `R` Noetherian, `f ∈ R`, an ideal `I ⊆ R`, `R' = R/I`,
glueing data `(P, N, α)` over `R`
(completion `R̂` along `f`) and `(P', N', α')` over `R'` (completion `R̂'` along `f̄`), and
surjective reductions `ρP : P → P'`, `ρN : N → N'` with kernels `IP`, `IN`, `ρN` semilinear over
the completion map `ψ : R̂ → R̂'` (`CompletionQuot`) and compatible with `α`, `α'`:

  `G/IG ≃ₐ[R/I] G'`   (`G = P ×_Q N`, `G' = P' ×_{Q'} N'`),

compatibly with the projections. Proof: `G/IG` with the induced maps to `P'` and `N'` satisfies the
hypotheses of the uniqueness of formal glueing over `R'` (`FormalGlueing.bijective_liftGlued`,
the full faithfulness in Stacks, Theorem 15.91.18, Tag 05ES): it localizes to `P'` away from `f̄`
(elementwise, from `G_f = P`), and its base change to `R̂'` is `N'`
(`IsBaseChange.of_comp` with `R̂ ⊗_R G = N` and `isBaseChange_of_surjective`: a surjection with
kernel `KN` is the base change along `S → S/K`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalGlueingQuot

noncomputable section

/-! ### Base change along a surjection -/

/-- **A surjection with kernel `K N` is the base change along a surjection `S → S'` with
kernel `K`.** -/
theorem isBaseChange_of_surjective {S S' N N' : Type*} [CommRing S] [CommRing S'] [Algebra S S']
    [AddCommGroup N] [Module S N] [AddCommGroup N'] [Module S N'] [Module S' N']
    [IsScalarTower S S' N'] (hS : Function.Surjective (algebraMap S S')) (ρ : N →ₗ[S] N')
    (hρ : Function.Surjective ρ)
    (hker : ∀ n, ρ n = 0 → n ∈ (RingHom.ker (algebraMap S S')) • (⊤ : Submodule S N)) :
    IsBaseChange S' ρ := by
  have hone : ∀ x : S' ⊗[S] N, ∃ n : N, x = (1 : S') ⊗ₜ n := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul s' n =>
      obtain ⟨s, rfl⟩ := hS s'
      refine ⟨s • n, ?_⟩
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by rw [tmul_add]⟩
  have hinj : Function.Injective (ρ.liftBaseChange S') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨n, rfl⟩ := hone x
    rw [LinearMap.liftBaseChange_tmul, one_smul] at hx
    refine Submodule.smul_induction_on (hker n hx) (fun k hk m _ ↦ ?_) (fun a b ha hb ↦ ?_)
    · rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, RingHom.mem_ker.mp hk,
        zero_tmul]
    · rw [tmul_add, ha, hb, add_zero]
  have hsurj : Function.Surjective (ρ.liftBaseChange S') := fun y ↦ by
    obtain ⟨n, rfl⟩ := hρ y
    exact ⟨1 ⊗ₜ n, by rw [LinearMap.liftBaseChange_tmul, one_smul]⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective (ρ.liftBaseChange S') ⟨hinj, hsurj⟩)
    fun n ↦ by simp

/-! ### The setting -/

variable {R : Type u} [CommRing R] (f : R) (I : Ideal R)

/-- The `f`-adic completion `R̂`. -/
abbrev H : Type u := AdicCompletion (Ideal.span {f}) R

/-- The image `f̄` of `f` in `R/I`. -/
abbrev fq : R ⧸ I := Ideal.Quotient.mk I f

/-- The completion `R̂'` of `R/I` along `f̄`. -/
abbrev H' : Type u := AdicCompletion (Ideal.span {fq f I}) (R ⧸ I)

lemma map_span : (Ideal.span {f}).map (Ideal.Quotient.mk I) = Ideal.span {fq f I} := by
  rw [Ideal.map_span, Set.image_singleton]

/-- The completion map `ψ : R̂ → R̂'`. -/
abbrev ψ : H f →ₐ[R] H' f I := CompletionQuot.ψ (Ideal.span {f}) I _ (map_span f I)

variable
  {P : Type u} [CommRing P] [Algebra R P]
  {N : Type u} [CommRing N] [Algebra R N] [Algebra (H f) N] [IsScalarTower R (H f) N]
  {Q : Type u} [CommRing Q] [Algebra R Q] [Algebra N Q] [IsScalarTower R N Q]
  [Algebra (H f) Q] [IsScalarTower R (H f) Q] [IsScalarTower (H f) N Q]
  [IsLocalization.Away (algebraMap R N f) Q]
  (α : P →ₐ[R] Q)
  {P' : Type u} [CommRing P'] [Algebra (R ⧸ I) P']
  {N' : Type u} [CommRing N'] [Algebra (R ⧸ I) N'] [Algebra (H' f I) N']
  [IsScalarTower (R ⧸ I) (H' f I) N']
  {Q' : Type u} [CommRing Q'] [Algebra (R ⧸ I) Q'] [Algebra N' Q'] [IsScalarTower (R ⧸ I) N' Q']
  [Algebra (H' f I) Q'] [IsScalarTower (R ⧸ I) (H' f I) Q'] [IsScalarTower (H' f I) N' Q']
  [IsLocalization.Away (algebraMap (R ⧸ I) N' (fq f I)) Q']
  (α' : P' →ₐ[R ⧸ I] Q')
  (ρP : P →+* P') (ρN : N →+* N')

variable (N) in
/-- The glued algebra `G = P ×_Q N`. -/
abbrev G : Subalgebra R (P × N) := FormalGlueing.glued N α

variable (N) in
/-- The ideal `I G`. -/
abbrev IG : Ideal (G N α) := I.map (algebraMap R (G N α))

variable {f I α α' ρP ρN}
variable (hρP : ∀ r : R, ρP (algebraMap R P r) = algebraMap (R ⧸ I) P' (Ideal.Quotient.mk I r))
  (hρN : ∀ (s : H f) (n : N), ρN (s • n) = ψ f I s • ρN n)

include hρP in
lemma ρP_IG {x : G N α} (hx : x ∈ IG I N α) : ρP (x : P × N).1 = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, rfl⟩ := hy
    change ρP (algebraMap R P r) = 0
    rw [hρP, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  | zero => exact map_zero ρP
  | add a b _ _ ha hb =>
    change ρP ((a : P × N).1 + (b : P × N).1) = 0
    rw [map_add, ha, hb, add_zero]
  | smul c a _ ha =>
    change ρP ((c : P × N).1 * (a : P × N).1) = 0
    rw [map_mul, ha, mul_zero]

include hρN in
lemma ρN_algebraMap (r : R) : ρN (algebraMap R N r) =
    algebraMap (R ⧸ I) N' (Ideal.Quotient.mk I r) := by
  have h1 : algebraMap R N r = algebraMap R (H f) r • (1 : N) := by
    rw [Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply]
  rw [h1, hρN, map_one, AlgHom.commutes, Algebra.smul_def, mul_one,
    IsScalarTower.algebraMap_apply (R ⧸ I) (H' f I) N']
  rfl

omit [Algebra (H f) Q] [IsScalarTower R (H f) Q] [IsScalarTower (H f) N Q]
  [IsLocalization.Away ((algebraMap R N) f) Q] in
include hρN in
lemma ρN_IG {x : G N α} (hx : x ∈ IG I N α) : ρN (x : P × N).2 = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, rfl⟩ := hy
    change ρN (algebraMap R N r) = 0
    rw [ρN_algebraMap hρN, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  | zero => exact map_zero ρN
  | add a b _ _ ha hb =>
    change ρN ((a : P × N).2 + (b : P × N).2) = 0
    rw [map_add, ha, hb, add_zero]
  | smul c a _ ha =>
    change ρN ((c : P × N).2 * (a : P × N).2) = 0
    rw [map_mul, ha, mul_zero]

variable (N α) in
/-- The map `G/IG → P'`. -/
def φ₁ : G N α ⧸ IG I N α →ₐ[R ⧸ I] P' :=
  { Ideal.Quotient.lift (IG I N α) (ρP.comp (FormalGlueing.fst N α).toRingHom)
      (fun _ hx ↦ ρP_IG hρP hx) with
    commutes' := fun r ↦ by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      exact hρP r }

variable (N α) in
/-- The map `G/IG → N'`. -/
def φ₂ : G N α ⧸ IG I N α →ₐ[R ⧸ I] N' :=
  { Ideal.Quotient.lift (IG I N α) (ρN.comp (FormalGlueing.snd N α).toRingHom)
      (fun _ hx ↦ ρN_IG hρN hx) with
    commutes' := fun r ↦ by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      exact ρN_algebraMap hρN r }

variable (N α) in
lemma φ₁_mk (g : G N α) : φ₁ N α hρP (Ideal.Quotient.mk _ g) = ρP (g : P × N).1 := rfl

omit [Algebra (H f) Q] [IsScalarTower R (H f) Q] [IsScalarTower (H f) N Q]
  [IsLocalization.Away ((algebraMap R N) f) Q] in
variable (N α) in
lemma φ₂_mk (g : G N α) : φ₂ N α hρN (Ideal.Quotient.mk _ g) = ρN (g : P × N).2 := rfl

variable (hcompat : ∀ (p : P) (n : N), α p = algebraMap N Q n →
  α' (ρP p) = algebraMap N' Q' (ρN n))

omit [Algebra (H f) Q] [IsScalarTower R (H f) Q] [IsScalarTower (H f) N Q]
  [IsLocalization.Away ((algebraMap R N) f) Q] [IsScalarTower (R ⧸ I) N' Q']
  [Algebra (H' f I) Q'] [IsScalarTower (R ⧸ I) (H' f I) Q'] [IsScalarTower (H' f I) N' Q']
  [IsLocalization.Away ((algebraMap (R ⧸ I) N') (fq f I)) Q'] in
include hcompat in
lemma hφ (x : G N α ⧸ IG I N α) :
    α' (φ₁ N α hρP x) = algebraMap N' Q' (φ₂ N α hρN x) := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hcompat _ _ g.2

variable (hfP : IsUnit (algebraMap R P f))

omit [Algebra (H f) N] [IsScalarTower R (H f) N] [Algebra (H f) Q] [IsScalarTower R (H f) Q]
  [IsScalarTower (H f) N Q] in
include hfP hρP in
lemma h₁ (hρPs : Function.Surjective ρP) (p' : P') :
    ∃ (x : G N α ⧸ IG I N α) (k : ℕ), φ₁ N α hρP x = fq f I ^ k • p' := by
  letI := FormalGlueing.algebraFst N α
  haveI := FormalGlueing.isLocalization_fst f N α hfP
  obtain ⟨p, rfl⟩ := hρPs p'
  obtain ⟨⟨g, _, k, rfl⟩, hg⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R (G N α) f)) p
  refine ⟨Ideal.Quotient.mk _ g, k, ?_⟩
  have hg' : (g : P × N).1 = p * algebraMap R P f ^ k := by
    have h2 : algebraMap (G N α) P (algebraMap R (G N α) f ^ k) = algebraMap R P f ^ k := by
      rw [map_pow]
      rfl
    rw [← h2]
    exact hg.symm
  rw [φ₁_mk, hg', map_mul, map_pow, hρP, Algebra.smul_def, map_pow, mul_comm]

omit [Algebra (H f) N] [IsScalarTower R (H f) N] [Algebra (H f) Q] [IsScalarTower R (H f) Q]
  [IsScalarTower (H f) N Q] in
include hfP in
/-- Elements of `IP` are, up to a power of `f`, images of elements of `IG`. -/
lemma exists_IG {y : P} (hy : y ∈ I.map (algebraMap R P)) :
    ∃ (K : ℕ) (h : G N α), h ∈ IG I N α ∧ algebraMap R P f ^ K * y = (h : P × N).1 := by
  letI := FormalGlueing.algebraFst N α
  haveI := FormalGlueing.isLocalization_fst f N α hfP
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, rfl⟩ := hz
    exact ⟨0, algebraMap R (G N α) r, Ideal.mem_map_of_mem _ hr, by rw [pow_zero, one_mul]; rfl⟩
  | zero => exact ⟨0, 0, Ideal.zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨K₁, h₁, hh₁, e₁⟩ := ha
    obtain ⟨K₂, h₂, hh₂, e₂⟩ := hb
    refine ⟨K₁ + K₂, algebraMap R (G N α) f ^ K₂ * h₁ + algebraMap R (G N α) f ^ K₁ * h₂,
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hh₁) (Ideal.mul_mem_left _ _ hh₂), ?_⟩
    change _ = (algebraMap R P f) ^ K₂ * (h₁ : P × N).1 + (algebraMap R P f) ^ K₁ * (h₂ : P × N).1
    rw [← e₁, ← e₂]
    ring
  | smul c a _ ha =>
    obtain ⟨K, h, hh, e⟩ := ha
    obtain ⟨⟨g, _, k, rfl⟩, hg⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap R (G N α) f)) c
    refine ⟨k + K, g * h, Ideal.mul_mem_left _ _ hh, ?_⟩
    change _ = (g : P × N).1 * (h : P × N).1
    have hg' : (g : P × N).1 = c * algebraMap R P f ^ k := by
      have h2 : algebraMap (G N α) P (algebraMap R (G N α) f ^ k) = algebraMap R P f ^ k := by
        rw [map_pow]
        rfl
      rw [← h2]
      exact hg.symm
    rw [hg', ← e, smul_eq_mul]
    ring

variable (hρPk : RingHom.ker ρP = I.map (algebraMap R P))

omit [Algebra (H f) N] [IsScalarTower R (H f) N] [Algebra (H f) Q] [IsScalarTower R (H f) Q]
  [IsScalarTower (H f) N Q] in
include hfP hρPk in
lemma h₁' (x : G N α ⧸ IG I N α) (hx : φ₁ N α hρP x = 0) : ∃ k : ℕ, fq f I ^ k • x = 0 := by
  letI := FormalGlueing.algebraFst N α
  haveI := FormalGlueing.isLocalization_fst f N α hfP
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [φ₁_mk] at hx
  have hmem : (g : P × N).1 ∈ I.map (algebraMap R P) := by rw [← hρPk]; exact hx
  obtain ⟨K, h, hh, e⟩ := exists_IG (N := N) (α := α) hfP hmem
  have h0 : algebraMap (G N α) P (algebraMap R (G N α) f ^ K * g - h) = 0 := by
    change (algebraMap R P f) ^ K * (g : P × N).1 - (h : P × N).1 = 0
    rw [e, sub_self]
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap R (G N α) f)) P _).mp h0
  refine ⟨m + K, ?_⟩
  rw [Algebra.smul_def, show fq f I ^ (m + K) = Ideal.Quotient.mk I (f ^ (m + K)) from
    (map_pow _ _ _).symm, Ideal.Quotient.algebraMap_quotient_map_quotient, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  have : (algebraMap R (G N α) (f ^ (m + K))) * g =
      algebraMap R (G N α) f ^ m * h := by
    rw [mul_sub, sub_eq_zero] at hm
    rw [map_pow, pow_add, mul_assoc, hm]
  rw [this]
  exact Ideal.mul_mem_left _ _ hh

/-! ### The base change to the completion -/

variable (hN : ∀ n : N, algebraMap R N f * n = 0 → n = 0) (hα : IsBaseChange (H f) α.toLinearMap)

include hfP hN hα in
/-- **`(G/IG)` base-changes to `N'` along `R/I → R̂'`.** -/
theorem h₂ [IsNoetherianRing R] (hρNs : Function.Surjective ρN)
    (hρNk : RingHom.ker ρN = I.map (algebraMap R N)) :
    IsBaseChange (H' f I) (φ₂ N α hρN).toLinearMap := by
  letI : Algebra (H f) (H' f I) := (ψ f I).toRingHom.toAlgebra
  haveI : IsScalarTower R (H f) (H' f I) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((ψ f I).commutes r).symm
  letI : Module (H f) N' := Module.compHom N' (ψ f I).toRingHom
  haveI : IsScalarTower (H f) (H' f I) N' := ⟨fun s t n ↦ mul_smul (ψ f I s) t n⟩
  letI : Module R N' := Module.compHom N' (algebraMap R (R ⧸ I))
  haveI : IsScalarTower R (R ⧸ I) N' := ⟨fun r s n ↦ mul_smul (algebraMap R (R ⧸ I) r) s n⟩
  haveI : IsScalarTower R (H' f I) N' := ⟨fun r t n ↦ by
    change (algebraMap R (H' f I) r * t) • n = (algebraMap R (R ⧸ I) r) • (t • n)
    rw [mul_smul, ← algebraMap_smul (H' f I) (algebraMap R (R ⧸ I) r) (t • n)]
    rfl⟩
  haveI : IsScalarTower R (H f) N' := ⟨fun r s n ↦ by
    change (ψ f I (r • s)) • n = r • (ψ f I s • n)
    rw [map_smul, smul_assoc]⟩
  let ρNH : N →ₗ[H f] N' := { toFun := ρN, map_add' := map_add ρN, map_smul' := hρN }
  have hρNH : IsBaseChange (H' f I) ρNH := by
    have hsψ : Function.Surjective (algebraMap (H f) (H' f I)) := fun y ↦
      CompletionQuot.surjective_ψ (Ideal.span {f}) I _ (map_span f I) y
    refine isBaseChange_of_surjective hsψ ρNH hρNs fun n hn ↦ ?_
    have hker : RingHom.ker (algebraMap (H f) (H' f I)) =
        I.map (algebraMap R (H f)) :=
      CompletionQuot.ker_ψ (Ideal.span {f}) I _ (map_span f I)
    rw [hker, ← FormalPatchLevel.mem_map_iff_mem_smul_top, ← hρNk]
    exact hn
  have hc := IsBaseChange.comp (FormalGlueing.isBaseChange_snd_completion f N α hfP hN hα) hρNH
  have hmk : IsBaseChange (R ⧸ I) (Ideal.Quotient.mkₐ R (IG I N α)).toLinearMap := by
    refine isBaseChange_of_surjective Ideal.Quotient.mk_surjective _ Ideal.Quotient.mk_surjective
      fun g hg ↦ ?_
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, Ideal.smul_top_eq_map,
      Submodule.restrictScalars_mem]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hg
  refine IsBaseChange.of_comp hmk ?_
  have heq : ((φ₂ N α hρN).toLinearMap.restrictScalars R).comp
      (Ideal.Quotient.mkₐ R (IG I N α)).toLinearMap =
      (ρNH.restrictScalars R).comp (FormalGlueing.snd N α).toLinearMap :=
    LinearMap.ext fun g ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, φ₂_mk]
      rfl
  rw [heq]
  exact hc

/-! ### The comparison -/

variable [IsNoetherianRing R] (hfP' : IsUnit (algebraMap (R ⧸ I) P' (fq f I)))
  (hN' : ∀ n : N', algebraMap (R ⧸ I) N' (fq f I) * n = 0 → n = 0)
  (hα' : IsBaseChange (H' f I) α'.toLinearMap)
  (hρPs : Function.Surjective ρP) (hρNs : Function.Surjective ρN)
  (hρNk : RingHom.ker ρN = I.map (algebraMap R N))

/-- **Formal glueing commutes with reduction**: `G/IG ≃ G'`. -/
def equiv : (G N α ⧸ IG I N α) ≃ₐ[R ⧸ I] FormalGlueing.glued N' α' :=
  AlgEquiv.ofBijective
    (FormalGlueing.liftGlued N' α' (φ₁ N α hρP) (φ₂ N α hρN) (hφ hρP hρN hcompat))
    (FormalGlueing.bijective_liftGlued N' α' (H' f I) hfP' (FormalGlueing.completion_eq_add _)
      hN' hα' (FormalGlueing.completion_dvd _) _ _ _ (h₁ hρP hfP hρPs) (h₁' hρP hfP hρPk)
      (h₂ hρN hfP hN hα hρNs hρNk))

lemma equiv_mk_fst (g : G N α) :
    ((equiv hρP hρN hcompat hfP hρPk hN hα hfP' hN' hα' hρPs hρNs hρNk
      (Ideal.Quotient.mk _ g) : FormalGlueing.glued N' α') : P' × N').1 = ρP (g : P × N).1 := rfl

lemma equiv_mk_snd (g : G N α) :
    ((equiv hρP hρN hcompat hfP hρPk hN hα hfP' hN' hα' hρPs hρNs hρNk
      (Ideal.Quotient.mk _ g) : FormalGlueing.glued N' α') : P' × N').2 = ρN (g : P × N).2 := rfl

end

end FormalGlueingQuot

end SemistableReduction
