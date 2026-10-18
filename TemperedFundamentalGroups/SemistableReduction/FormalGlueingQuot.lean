/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Ideal.Over
import TemperedFundamentalGroups.SemistableReduction.FormalGlueing
import TemperedFundamentalGroups.SemistableReduction.CompletionSurj
import TemperedFundamentalGroups.SemistableReduction.FormalPatchLevel

/-!
# Formal glueing commutes with base change along a surjection (Blueprint §12.8, M2.3 (e'))

The formal patching produces at each level `n` a glued algebra `G_n = P_n ×_{Q_n} N_n` over the
chart `R_n` of the model modulo `ϖⁿ`. To obtain an adic system (input of Grothendieck existence,
`AdicChartAlgSystem`) one needs `R_n ⊗_{R_{n+1}} G_{n+1} ≅ G_n`. Generic statement
(**`FormalGlueingQuot.equiv`**): for `R` Noetherian, `f ∈ R`, an `R`-algebra `R'` with surjective
structure map `q : R → R'` (kernel `I`), glueing data `(P, N, α)` over `R` (completion `R̂` along
`f`) and `(P', N', α')` over `R'` (completion `R̂'` along `q f`), and surjective reductions
`ρP : P → P'`, `ρN : N → N'` with kernels `IP`, `IN`, `ρN` semilinear over the completion map
`ψ : R̂ → R̂'` (`CompletionSurj.ψ`) and compatible with `α`, `α'`:

  `R' ⊗_R G ≃ₐ[R'] G'`   (`G = P ×_Q N`, `G' = P' ×_{Q'} N'`),

compatibly with the projections (`equiv_tmul_fst`, `equiv_tmul_snd`). Proof: `R' ⊗_R G` with the
induced maps to `P'` and `N'` satisfies the hypotheses of the uniqueness of formal glueing over `R'`
(`FormalGlueing.bijective_liftGlued`, the full faithfulness in Stacks, Theorem 15.91.18,
Tag 05ES): it localizes to `P'` away from `q f` (elementwise, from `G_f = P`), and its base change
to `R̂'` is `N'` (`IsBaseChange.of_comp` with `R̂ ⊗_R G = N` and `isBaseChange_of_surjective`: a
surjection with kernel `KN` is the base change along `S → S/K`).
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

/-! ### Base change along a surjection of rings -/

section Tensor

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']
  (hq : Function.Surjective (algebraMap R R')) {M : Type u} [CommRing M] [Algebra R M]

include hq in
/-- Every element of `R' ⊗_R M` is `1 ⊗ m` (`R → R'` surjective). -/
lemma exists_one_tmul (x : R' ⊗[R] M) : ∃ m : M, x = (1 : R') ⊗ₜ m := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s' n =>
    obtain ⟨s, rfl⟩ := hq s'
    refine ⟨s • n, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by rw [tmul_add]⟩

/-- `1 ⊗ y = 0` in `R' ⊗_R M` for `y ∈ (ker q) M`. -/
lemma one_tmul_eq_zero {y : M} (hy : y ∈ (RingHom.ker (algebraMap R R')).map (algebraMap R M)) :
    (1 : R') ⊗ₜ[R] y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, rfl⟩ := hz
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      RingHom.mem_ker.mp hr, zero_tmul]
  | zero => exact tmul_zero _ _
  | add a b _ _ ha hb => rw [tmul_add, ha, hb, add_zero]
  | smul c a _ ha =>
    rw [smul_eq_mul, ← one_mul (1 : R'), ← Algebra.TensorProduct.tmul_mul_tmul, ha, mul_zero]

end Tensor

/-! ### The setting -/

variable {R : Type u} [CommRing R] (f : R) {R' : Type u} [CommRing R'] [Algebra R R']

/-- The `f`-adic completion `R̂`. -/
abbrev H : Type u := AdicCompletion (Ideal.span {f}) R

/-- The image `q f` of `f` in `R'`. -/
abbrev fq : R' := CompletionSurj.fq (R' := R') f

/-- The completion `R̂'` of `R'` along `q f`. -/
abbrev H' : Type u := CompletionSurj.H' (R' := R') f

/-- The kernel `I` of `q : R → R'`. -/
abbrev I : Ideal R := RingHom.ker (algebraMap R R')

/-- The completion map `ψ : R̂ → R̂'`. -/
abbrev ψ : H f →ₐ[R] H' (R' := R') f := CompletionSurj.ψ f

variable
  {P : Type u} [CommRing P] [Algebra R P]
  {N : Type u} [CommRing N] [Algebra R N] [Algebra (H f) N] [IsScalarTower R (H f) N]
  {Q : Type u} [CommRing Q] [Algebra R Q] [Algebra N Q] [IsScalarTower R N Q]
  [Algebra (H f) Q] [IsScalarTower R (H f) Q] [IsScalarTower (H f) N Q]
  [IsLocalization.Away (algebraMap R N f) Q]
  (α : P →ₐ[R] Q)
  {P' : Type u} [CommRing P'] [Algebra R' P']
  {N' : Type u} [CommRing N'] [Algebra R' N'] [Algebra (H' (R' := R') f) N']
  [IsScalarTower R' (H' (R' := R') f) N']
  {Q' : Type u} [CommRing Q'] [Algebra R' Q'] [Algebra N' Q'] [IsScalarTower R' N' Q']
  [Algebra (H' (R' := R') f) Q'] [IsScalarTower R' (H' (R' := R') f) Q']
  [IsScalarTower (H' (R' := R') f) N' Q']
  [IsLocalization.Away (algebraMap R' N' (fq (R' := R') f)) Q']
  (α' : P' →ₐ[R'] Q')
  (ρP : P →+* P') (ρN : N →+* N')

variable (N) in
/-- The glued algebra `G = P ×_Q N`. -/
abbrev G : Subalgebra R (P × N) := FormalGlueing.glued N α

variable (R' N) in
/-- The ideal `I G`. -/
abbrev IG : Ideal (G N α) := (I (R' := R')).map (algebraMap R (G N α))

variable {f α α' ρP ρN}
variable (hρP : ∀ r : R, ρP (algebraMap R P r) = algebraMap R' P' (algebraMap R R' r))
  (hρN : ∀ (s : H f) (n : N), ρN (s • n) = ψ (R' := R') f s • ρN n)

include hρP in
lemma ρP_IG {x : G N α} (hx : x ∈ IG R' N α) : ρP (x : P × N).1 = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, rfl⟩ := hy
    change ρP (algebraMap R P r) = 0
    rw [hρP, RingHom.mem_ker.mp hr, map_zero]
  | zero => exact map_zero ρP
  | add a b _ _ ha hb =>
    change ρP ((a : P × N).1 + (b : P × N).1) = 0
    rw [map_add, ha, hb, add_zero]
  | smul c a _ ha =>
    change ρP ((c : P × N).1 * (a : P × N).1) = 0
    rw [map_mul, ha, mul_zero]

include hρN in
lemma ρN_algebraMap (r : R) : ρN (algebraMap R N r) =
    algebraMap R' N' (algebraMap R R' r) := by
  have h1 : algebraMap R N r = algebraMap R (H f) r • (1 : N) := by
    rw [Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply]
  rw [h1, hρN, map_one, AlgHom.commutes, Algebra.smul_def, mul_one,
    IsScalarTower.algebraMap_apply R' (H' (R' := R') f) N']
  rfl

/-! ### The maps out of `R' ⊗_R G` -/

variable (R' N α) in
/-- `G → P'`, `g ↦ ρP(g₁)`, over `R`. -/
def gP : letI : Algebra R P' := Algebra.compHom P' (algebraMap R R')
    G N α →ₐ[R] P' :=
  letI : Algebra R P' := Algebra.compHom P' (algebraMap R R')
  { ρP.comp (FormalGlueing.fst N α).toRingHom with
    commutes' := fun r ↦ hρP r }

variable (R' N α) in
/-- `G → N'`, `g ↦ ρN(g₂)`, over `R`. -/
def gN : letI : Algebra R N' := Algebra.compHom N' (algebraMap R R')
    G N α →ₐ[R] N' :=
  letI : Algebra R N' := Algebra.compHom N' (algebraMap R R')
  { ρN.comp (FormalGlueing.snd N α).toRingHom with
    commutes' := fun r ↦ ρN_algebraMap hρN r }

variable (N α) in
/-- The map `R' ⊗_R G → P'`. -/
def φ₁ : R' ⊗[R] G N α →ₐ[R'] P' :=
  letI : Algebra R P' := Algebra.compHom P' (algebraMap R R')
  haveI : IsScalarTower R R' P' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId R' P') (gP R' N α hρP) fun _ _ ↦ Commute.all _ _

variable (N α) in
/-- The map `R' ⊗_R G → N'`. -/
def φ₂ : R' ⊗[R] G N α →ₐ[R'] N' :=
  letI : Algebra R N' := Algebra.compHom N' (algebraMap R R')
  haveI : IsScalarTower R R' N' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId R' N') (gN R' N α hρN) fun _ _ ↦ Commute.all _ _

variable (N α) in
lemma φ₁_tmul (r : R') (g : G N α) :
    φ₁ N α hρP (r ⊗ₜ g) = algebraMap R' P' r * ρP (g : P × N).1 := by
  letI : Algebra R P' := Algebra.compHom P' (algebraMap R R')
  haveI : IsScalarTower R R' P' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact Algebra.TensorProduct.lift_tmul _ _ _ r g

omit [Algebra (H f) Q] [IsScalarTower R (H f) Q] [IsScalarTower (H f) N Q]
  [IsLocalization.Away ((algebraMap R N) f) Q] in
variable (N α) in
lemma φ₂_tmul (r : R') (g : G N α) :
    φ₂ N α hρN (r ⊗ₜ g) = algebraMap R' N' r * ρN (g : P × N).2 := by
  letI : Algebra R N' := Algebra.compHom N' (algebraMap R R')
  haveI : IsScalarTower R R' N' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact Algebra.TensorProduct.lift_tmul _ _ _ r g

variable (N α) in
lemma φ₁_one_tmul (g : G N α) : φ₁ N α hρP ((1 : R') ⊗ₜ g) = ρP (g : P × N).1 := by
  rw [φ₁_tmul, map_one, one_mul]

omit [Algebra (H f) Q] [IsScalarTower R (H f) Q] [IsScalarTower (H f) N Q]
  [IsLocalization.Away ((algebraMap R N) f) Q] in
variable (N α) in
lemma φ₂_one_tmul (g : G N α) : φ₂ N α hρN ((1 : R') ⊗ₜ g) = ρN (g : P × N).2 := by
  rw [φ₂_tmul, map_one, one_mul]

variable (hq : Function.Surjective (algebraMap R R'))

variable (hcompat : ∀ (p : P) (n : N), α p = algebraMap N Q n →
  α' (ρP p) = algebraMap N' Q' (ρN n))

omit [Algebra (H f) Q] [IsScalarTower R (H f) Q] [IsScalarTower (H f) N Q]
  [IsLocalization.Away ((algebraMap R N) f) Q] [IsScalarTower R' N' Q']
  [Algebra (H' (R' := R') f) Q'] [IsScalarTower R' (H' (R' := R') f) Q']
  [IsScalarTower (H' (R' := R') f) N' Q']
  [IsLocalization.Away ((algebraMap R' N') (fq (R' := R') f)) Q'] in
include hcompat hq in
lemma hφ (x : R' ⊗[R] G N α) :
    α' (φ₁ N α hρP x) = algebraMap N' Q' (φ₂ N α hρN x) := by
  obtain ⟨g, rfl⟩ := exists_one_tmul hq x
  rw [φ₁_one_tmul, φ₂_one_tmul]
  exact hcompat _ _ g.2

variable (hfP : IsUnit (algebraMap R P f))

omit [Algebra (H f) N] [IsScalarTower R (H f) N] [Algebra (H f) Q] [IsScalarTower R (H f) Q]
  [IsScalarTower (H f) N Q] in
include hfP in
lemma h₁ (hρPs : Function.Surjective ρP) (p' : P') :
    ∃ (x : R' ⊗[R] G N α) (k : ℕ), φ₁ N α hρP x = fq (R' := R') f ^ k • p' := by
  letI := FormalGlueing.algebraFst N α
  haveI := FormalGlueing.isLocalization_fst f N α hfP
  obtain ⟨p, rfl⟩ := hρPs p'
  obtain ⟨⟨g, _, k, rfl⟩, hg⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R (G N α) f)) p
  refine ⟨(1 : R') ⊗ₜ g, k, ?_⟩
  have hg' : (g : P × N).1 = p * algebraMap R P f ^ k := by
    have h2 : algebraMap (G N α) P (algebraMap R (G N α) f ^ k) = algebraMap R P f ^ k := by
      rw [map_pow]
      rfl
    rw [← h2]
    exact hg.symm
  rw [φ₁_one_tmul, hg', map_mul, map_pow, hρP, Algebra.smul_def, map_pow, mul_comm]

omit [Algebra (H f) N] [IsScalarTower R (H f) N] [Algebra (H f) Q] [IsScalarTower R (H f) Q]
  [IsScalarTower (H f) N Q] in
include hfP in
/-- Elements of `IP` are, up to a power of `f`, images of elements of `IG`. -/
lemma exists_IG {y : P} (hy : y ∈ (I (R' := R')).map (algebraMap R P)) :
    ∃ (K : ℕ) (h : G N α), h ∈ IG R' N α ∧ algebraMap R P f ^ K * y = (h : P × N).1 := by
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

variable (hρPk : RingHom.ker ρP = (I (R' := R')).map (algebraMap R P))

omit [Algebra (H f) N] [IsScalarTower R (H f) N] [Algebra (H f) Q] [IsScalarTower R (H f) Q]
  [IsScalarTower (H f) N Q] in
include hfP hρPk hq in
lemma h₁' (x : R' ⊗[R] G N α) (hx : φ₁ N α hρP x = 0) :
    ∃ k : ℕ, fq (R' := R') f ^ k • x = 0 := by
  letI := FormalGlueing.algebraFst N α
  haveI := FormalGlueing.isLocalization_fst f N α hfP
  obtain ⟨g, rfl⟩ := exists_one_tmul hq x
  rw [φ₁_one_tmul] at hx
  have hmem : (g : P × N).1 ∈ (I (R' := R')).map (algebraMap R P) := by rw [← hρPk]; exact hx
  obtain ⟨K, h, hh, e⟩ := exists_IG (N := N) (α := α) hfP hmem
  have h0 : algebraMap (G N α) P (algebraMap R (G N α) f ^ K * g - h) = 0 := by
    change (algebraMap R P f) ^ K * (g : P × N).1 - (h : P × N).1 = 0
    rw [e, sub_self]
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap R (G N α) f)) P _).mp h0
  refine ⟨m + K, ?_⟩
  have h1 : fq (R' := R') f ^ (m + K) • ((1 : R') ⊗ₜ[R] g) =
      (1 : R') ⊗ₜ[R] (algebraMap R (G N α) (f ^ (m + K)) * g) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_pow]
  have : (algebraMap R (G N α) (f ^ (m + K))) * g =
      algebraMap R (G N α) f ^ m * h := by
    rw [mul_sub, sub_eq_zero] at hm
    rw [map_pow, pow_add, mul_assoc, hm]
  rw [h1, this]
  exact one_tmul_eq_zero (Ideal.mul_mem_left _ _ hh)

/-! ### The base change to the completion -/

variable (hN : ∀ n : N, algebraMap R N f * n = 0 → n = 0) (hα : IsBaseChange (H f) α.toLinearMap)

include hfP hN hα hq in
/-- **`R' ⊗_R G` base-changes to `N'` along `R' → R̂'`.** -/
theorem h₂ [IsNoetherianRing R] (hρNs : Function.Surjective ρN)
    (hρNk : RingHom.ker ρN = (I (R' := R')).map (algebraMap R N)) :
    IsBaseChange (H' (R' := R') f) (φ₂ N α hρN).toLinearMap := by
  letI : Algebra (H f) (H' (R' := R') f) := (ψ (R' := R') f).toRingHom.toAlgebra
  haveI : IsScalarTower R (H f) (H' (R' := R') f) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((ψ (R' := R') f).commutes r).symm
  letI : Module (H f) N' := Module.compHom N' (ψ (R' := R') f).toRingHom
  haveI : IsScalarTower (H f) (H' (R' := R') f) N' := ⟨fun s t n ↦ mul_smul (ψ f s) t n⟩
  letI : Algebra R N' := Algebra.compHom N' (algebraMap R R')
  haveI : IsScalarTower R R' N' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R R' (H' (R' := R') f) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (H' (R' := R') f) N' := ⟨fun r t n ↦ by
    rw [Algebra.smul_def r t, mul_smul, IsScalarTower.algebraMap_apply R R' (H' (R' := R') f),
      algebraMap_smul]
    rfl⟩
  haveI : IsScalarTower R (H f) N' := ⟨fun r s n ↦ by
    change (ψ (R' := R') f (r • s)) • n = r • (ψ (R' := R') f s • n)
    rw [map_smul, smul_assoc]⟩
  let ρNH : N →ₗ[H f] N' := { toFun := ρN, map_add' := map_add ρN, map_smul' := hρN }
  have hρNH : IsBaseChange (H' (R' := R') f) ρNH := by
    have hsψ : Function.Surjective (algebraMap (H f) (H' (R' := R') f)) := fun y ↦
      CompletionSurj.surjective_ψ hq y
    refine isBaseChange_of_surjective hsψ ρNH hρNs fun n hn ↦ ?_
    have hker : RingHom.ker (algebraMap (H f) (H' (R' := R') f)) =
        (I (R' := R')).map (algebraMap R (H f)) :=
      CompletionSurj.ker_ψ hq
    rw [hker, ← FormalPatchLevel.mem_map_iff_mem_smul_top, ← hρNk]
    exact hn
  have hc := IsBaseChange.comp (FormalGlueing.isBaseChange_snd_completion f N α hfP hN hα) hρNH
  have hmk : IsBaseChange R' (TensorProduct.mk R R' (G N α) 1) :=
    TensorProduct.isBaseChange R (G N α) R'
  refine IsBaseChange.of_comp hmk ?_
  have heq : ((φ₂ N α hρN).toLinearMap.restrictScalars R) ∘ₗ (TensorProduct.mk R R' (G N α) 1) =
      (ρNH.restrictScalars R).comp (FormalGlueing.snd N α).toLinearMap :=
    LinearMap.ext fun g ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
        TensorProduct.mk_apply, φ₂_one_tmul]
      rfl
  rw [heq]
  exact hc

/-! ### The comparison -/

variable [IsNoetherianRing R] (hfP' : IsUnit (algebraMap R' P' (fq (R' := R') f)))
  (hN' : ∀ n : N', algebraMap R' N' (fq (R' := R') f) * n = 0 → n = 0)
  (hα' : IsBaseChange (H' (R' := R') f) α'.toLinearMap)
  (hρPs : Function.Surjective ρP) (hρNs : Function.Surjective ρN)
  (hρNk : RingHom.ker ρN = (I (R' := R')).map (algebraMap R N))

/-- **Formal glueing commutes with base change along a surjection**: `R' ⊗_R G ≃ G'`. -/
def equiv : (R' ⊗[R] G N α) ≃ₐ[R'] FormalGlueing.glued N' α' :=
  haveI : IsNoetherianRing R' := isNoetherianRing_of_surjective R R' (algebraMap R R') hq
  AlgEquiv.ofBijective
    (FormalGlueing.liftGlued N' α' (φ₁ N α hρP) (φ₂ N α hρN) (hφ hρP hρN hq hcompat))
    (FormalGlueing.bijective_liftGlued N' α' (H' (R' := R') f) hfP'
      (FormalGlueing.completion_eq_add _) hN' hα' (FormalGlueing.completion_dvd _) _ _ _
      (h₁ hρP hfP hρPs) (h₁' hρP hq hfP hρPk) (h₂ hρN hq hfP hN hα hρNs hρNk))

lemma equiv_tmul_fst (g : G N α) :
    ((equiv hρP hρN hq hcompat hfP hρPk hN hα hfP' hN' hα' hρPs hρNs hρNk
      ((1 : R') ⊗ₜ g) : FormalGlueing.glued N' α') : P' × N').1 = ρP (g : P × N).1 :=
  φ₁_one_tmul N α hρP g

lemma equiv_tmul_snd (g : G N α) :
    ((equiv hρP hρN hq hcompat hfP hρPk hN hα hfP' hN' hα' hρPs hρNs hρNk
      ((1 : R') ⊗ₜ g) : FormalGlueing.glued N' α') : P' × N').2 = ρN (g : P × N).2 :=
  φ₂_one_tmul N α hρN g

end

end FormalGlueingQuot

end SemistableReduction
