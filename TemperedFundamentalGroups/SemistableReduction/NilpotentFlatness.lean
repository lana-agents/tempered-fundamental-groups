/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# The local flatness criterion for a nilpotent ideal

Let `S` be a commutative ring, `I ⊆ S` a nilpotent ideal and `M` an `S`-module. If
`I ⊗_S M → M` is injective (i.e. `Tor₁^S(S/I, M) = 0`) and `M/IM` is flat over `S/I`, then `M`
is flat over `S` (Stacks, Lemma 10.99.8, Tag 051C, last statement). We give a `Tor`-free proof.

* `flat_of_isNilpotent`: the criterion above;
* `flat_of_pow_succ_eq_zero`: the case of a principal ideal `(ϖ)` with `ϖ ^ (n + 1) = 0`, where
  `Tor₁ = 0` is replaced by: every `m` with `ϖ • m = 0` lies in `ϖ ^ n • M`;
* `flat_of_flat_fibre`: the *critère de platitude par fibres*, nilpotent case
  (Stacks, Lemma 10.101.8, Tag 06A5, for `S' = S`): for `R → S`, a nilpotent ideal `J ⊆ R` and an
  `S`-module `M` flat over `R` with `M/JM` flat over `S/JS`, `M` is flat over `S`;
* `flat_quotient_polynomial`: for an `A[X]`-module `M`, if `M / IⁿM` is flat over `A / Iⁿ` and
  `M / I M` is flat over `A[X] / I A[X]`, then `M / (I A[X])ⁿ M` is flat over `A[X] / (I A[X])ⁿ`.

The proof of `flat_of_isNilpotent` is a dévissage: an inclusion `A ≤ B` of submodules is "good"
if `A ⊗ M → B ⊗ M` is injective; good inclusions compose, the chain `A ⊔ Iᵏ B` reduces to the case
`I B ≤ A`, a free cover of `B` reduces to a flat ambient module `F`, and there one compares
`(I ⊗ F) ⊗ M → F ⊗ M` (injective by the `Tor₁` hypothesis) with the reduction mod `I`.
-/

open TensorProduct Function

namespace SemistableReduction.NilpotentFlatness

section Criterion

variable {S : Type*} [CommRing S] (I : Ideal S) (M : Type*) [AddCommGroup M] [Module S M]

/-- An injective map between modules killed by `I` stays injective after `⊗_S M` when
`(S ⧸ I) ⊗_S M` is flat over `S ⧸ I`. -/
theorem rTensor_injective_of_isTorsionBySet
    [Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] M)]
    {X Y : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
    (hX : Module.IsTorsionBySet S X I) (hY : Module.IsTorsionBySet S Y I)
    (g : X →ₗ[S] Y) (hg : Injective g) : Injective (g.rTensor M) := by
  letI := hX.module
  letI := hY.module
  let g' : X →ₗ[S ⧸ I] Y :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        rintro ⟨a⟩ x
        exact g.map_smul a x }
  let eX := AlgebraTensorModule.cancelBaseChange S (S ⧸ I) (S ⧸ I) X M
  let eY := AlgebraTensorModule.cancelBaseChange S (S ⧸ I) (S ⧸ I) Y M
  have key : ∀ t, g.rTensor M (eX t) = eY (g'.rTensor ((S ⧸ I) ⊗[S] M) t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul x u =>
      induction u with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul a m =>
        simp only [eX, eY, AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul]
        congr 1
        exact g'.map_smul a x
  have hg' : Injective (g'.rTensor ((S ⧸ I) ⊗[S] M)) :=
    Module.Flat.rTensor_preserves_injective_linearMap g' hg
  intro z w h
  obtain ⟨z, rfl⟩ := eX.surjective z
  obtain ⟨w, rfl⟩ := eX.surjective w
  rw [key, key] at h
  rw [hg' (eY.injective h)]

/-- If `I ⊗_S M → M` is injective and `F` is flat, then `(I ⊗_S F) ⊗_S M → F ⊗_S M` is
injective. -/
theorem rTensor_mul_injective (hI : Injective (I.subtype.rTensor M))
    (F : Type*) [AddCommGroup F] [Module S F] [Module.Flat S F] :
    Injective (((TensorProduct.lid S F).toLinearMap ∘ₗ I.subtype.rTensor F).rTensor M) := by
  have h : (((TensorProduct.lid S F).toLinearMap ∘ₗ I.subtype.rTensor F).rTensor M) =
      (LinearEquiv.rTensor M (TensorProduct.lid S F)).toLinearMap ∘ₗ
        ((TensorProduct.rightComm S S M F).toLinearMap ∘ₗ
          (I.subtype.rTensor M).rTensor F ∘ₗ
            (TensorProduct.rightComm S I F M).toLinearMap) := by
    apply TensorProduct.ext_threefold
    intro x y z
    rfl
  rw [h, LinearMap.coe_comp, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.injective _).comp ((LinearEquiv.injective _).comp
    ((Module.Flat.rTensor_preserves_injective_linearMap _ hI).comp (LinearEquiv.injective _)))

variable {I M}

/-- Reduced step: for a flat `F` and `A ≤ F` with `I • ⊤ ≤ A`, `A ⊗_S M → F ⊗_S M` is injective. -/
theorem rTensor_subtype_injective_of_flat [Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] M)]
    (hI : Injective (I.subtype.rTensor M))
    {F : Type*} [AddCommGroup F] [Module S F] [Module.Flat S F] (A : Submodule S F)
    (hA : I • (⊤ : Submodule S F) ≤ A) : Injective (A.subtype.rTensor M) := by
  set μ : I ⊗[S] F →ₗ[S] F := (TensorProduct.lid S F).toLinearMap ∘ₗ I.subtype.rTensor F
    with hμ
  have hμA : ∀ z, μ z ∈ A := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact A.add_mem ha hb
    | tmul i f => exact hA (by simpa [μ] using Submodule.smul_mem_smul i.2 (Submodule.mem_top))
  set μ' : I ⊗[S] F →ₗ[S] A := μ.codRestrict A hμA
  have hsub : A.subtype ∘ₗ μ' = μ := rfl
  -- the quotients by the image of `μ` are killed by `I`
  have hkill : ∀ i ∈ I, ∀ f : F, i • f ∈ LinearMap.range μ := fun i hi f ↦
    ⟨⟨i, hi⟩ ⊗ₜ f, by simp [μ]⟩
  let q := (LinearMap.range μ').mkQ
  let q' := (LinearMap.range μ).mkQ
  have hle : LinearMap.range μ' ≤ (LinearMap.range μ).comap A.subtype := by
    rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  let φ := (LinearMap.range μ').mapQ (LinearMap.range μ) A.subtype hle
  have hφ : Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, eq_bot_iff]
    intro x hx
    obtain ⟨a, ⟨z, hz⟩, rfl⟩ := hx
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, Subtype.ext hz⟩
  have hX : Module.IsTorsionBySet S (A ⧸ LinearMap.range μ') I := by
    rintro x ⟨i, hi⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    obtain ⟨z, hz⟩ := hkill i hi x
    exact ⟨z, Subtype.ext hz⟩
  have hY : Module.IsTorsionBySet S (F ⧸ LinearMap.range μ) I := by
    rintro x ⟨i, hi⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hkill i hi x
  have hφinj := rTensor_injective_of_isTorsionBySet I M hX hY φ hφ
  have hcomm : φ ∘ₗ q = q' ∘ₗ A.subtype := rfl
  have hex : Exact (μ'.rTensor M) (q.rTensor M) :=
    rTensor_exact M (LinearMap.exact_map_mkQ_range μ') (Submodule.mkQ_surjective _)
  have hμinj := rTensor_mul_injective I M hI F
  rw [← hμ] at hμinj
  rw [injective_iff_map_eq_zero]
  intro y hy
  have h1 : q.rTensor M y = 0 := by
    apply hφinj
    rw [← LinearMap.rTensor_comp_apply, hcomm, LinearMap.rTensor_comp_apply, hy, map_zero,
      map_zero]
  obtain ⟨z, rfl⟩ := (hex y).mp h1
  rw [← LinearMap.rTensor_comp_apply, hsub] at hy
  rw [hμinj (hy.trans (map_zero _).symm), map_zero]

/-- Step of the dévissage: if `A ≤ B` and `I • ⊤ ≤ A`, then `A ⊗_S M → B ⊗_S M` is
injective. -/
theorem rTensor_subtype_injective_of_smul_le [Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] M)]
    (hI : Injective (I.subtype.rTensor M))
    {B : Type*} [AddCommGroup B] [Module S B] (A : Submodule S B)
    (hA : I • (⊤ : Submodule S B) ≤ A) : Injective (A.subtype.rTensor M) := by
  let π : (B →₀ S) →ₗ[S] B := Finsupp.linearCombination S id
  have hπ : Surjective π := fun b ↦ ⟨Finsupp.single b 1, by simp [π]⟩
  let A' := A.comap π
  have hA' : I • (⊤ : Submodule S (B →₀ S)) ≤ A' := by
    rw [Submodule.smul_le]
    intro r hr x _
    rw [Submodule.mem_comap, map_smul]
    exact hA (Submodule.smul_mem_smul hr Submodule.mem_top)
  let K := LinearMap.ker π
  let πA : A' →ₗ[S] A := π.restrict (fun _ h ↦ h)
  have hπA : Surjective πA := by
    rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := hπ a
    exact ⟨⟨x, ha⟩, rfl⟩
  have hKA : K ≤ A' := fun k hk ↦ by
    simp only [A', Submodule.mem_comap, LinearMap.mem_ker.mp hk, zero_mem]
  let kA := Submodule.inclusion hKA
  have hc1 : π ∘ₗ A'.subtype = A.subtype ∘ₗ πA := rfl
  have hc2 : A'.subtype ∘ₗ kA = K.subtype := rfl
  have hc3 : πA ∘ₗ kA = 0 := by
    ext k
    exact LinearMap.mem_ker.mp k.2
  have hex : Exact (K.subtype.rTensor M) (π.rTensor M) :=
    rTensor_exact M (LinearMap.exact_subtype_ker_map π) hπ
  have hR := rTensor_subtype_injective_of_flat hI A' hA'
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := LinearMap.rTensor_surjective M hπA x
  have h1 : π.rTensor M (A'.subtype.rTensor M x) = 0 := by
    rw [← LinearMap.rTensor_comp_apply, hc1, LinearMap.rTensor_comp_apply, hx]
  obtain ⟨k, hk⟩ := (hex _).mp h1
  have h2 : x = kA.rTensor M k := by
    apply hR
    rw [← hk, ← LinearMap.rTensor_comp_apply, hc2]
  rw [h2, ← LinearMap.rTensor_comp_apply, hc3, LinearMap.rTensor_zero, LinearMap.zero_apply]

/-- Step of the dévissage, for injective maps: if `f : A → B` is injective with
`I • ⊤ ≤ range f`, then `f ⊗ M` is injective. -/
theorem rTensor_injective_of_smul_le_range [Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] M)]
    (hI : Injective (I.subtype.rTensor M))
    {A B : Type*} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    (f : A →ₗ[S] B) (hf : Injective f) (hA : I • (⊤ : Submodule S B) ≤ LinearMap.range f) :
    Injective (f.rTensor M) := by
  have h : f = (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap := rfl
  rw [h, LinearMap.rTensor_comp, LinearMap.coe_comp]
  exact (rTensor_subtype_injective_of_smul_le hI _ hA).comp
    (LinearEquiv.rTensor M (LinearEquiv.ofInjective f hf)).injective

/-- Step of the dévissage, for submodules `A ≤ B` with `I • B ≤ A`. -/
theorem rTensor_inclusion_injective [Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] M)]
    (hI : Injective (I.subtype.rTensor M)) {P : Type*} [AddCommGroup P] [Module S P]
    {A B : Submodule S P} (h : A ≤ B) (hIB : I • B ≤ A) :
    Injective ((Submodule.inclusion h).rTensor M) := by
  refine rTensor_injective_of_smul_le_range hI _ (Submodule.inclusion_injective h) ?_
  rw [Submodule.smul_le]
  rintro r hr ⟨b, hb⟩ -
  exact ⟨⟨r • b, hIB (Submodule.smul_mem_smul hr hb)⟩, rfl⟩

/-- Composition of good inclusions along a decreasing chain. -/
theorem rTensor_inclusion_injective_chain {P : Type*} [AddCommGroup P] [Module S P]
    {B : Submodule S P} (D : ℕ → Submodule S P) (hDB : ∀ k, D k ≤ B)
    (hD : ∀ k, D (k + 1) ≤ D k)
    (h0 : Injective ((Submodule.inclusion (hDB 0)).rTensor M))
    (hstep : ∀ k, Injective ((Submodule.inclusion (hD k)).rTensor M)) (k : ℕ) :
    Injective ((Submodule.inclusion (hDB k)).rTensor M) := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    have : Submodule.inclusion (hDB (k + 1)) =
        Submodule.inclusion (hDB k) ∘ₗ Submodule.inclusion (hD k) := by
      ext; rfl
    rw [this, LinearMap.rTensor_comp, LinearMap.coe_comp]
    exact ih.comp (hstep k)

/-- The dévissage: if `I ^ N = ⊥`, `A ≤ B` then `A ⊗ M → B ⊗ M` is injective. -/
theorem rTensor_inclusion_injective_of_pow_eq_bot [Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] M)]
    (hI : Injective (I.subtype.rTensor M)) {N : ℕ} (hN : I ^ N = ⊥)
    {P : Type*} [AddCommGroup P] [Module S P] {A B : Submodule S P} (h : A ≤ B) :
    Injective ((Submodule.inclusion h).rTensor M) := by
  have hD : ∀ k, A ⊔ I ^ (k + 1) • B ≤ A ⊔ I ^ k • B := fun k ↦
    sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right k.le_succ)) _
  have hDI : ∀ k, I • (A ⊔ I ^ k • B) ≤ A ⊔ I ^ (k + 1) • B := fun k ↦ by
    rw [Submodule.smul_sup]
    refine sup_le_sup Submodule.smul_le_right ?_
    rw [← Submodule.mul_smul, pow_succ']
  have hDB : ∀ k, A ⊔ I ^ k • B ≤ B := fun k ↦ sup_le h Submodule.smul_le_right
  have h0 : I • B ≤ A ⊔ I ^ 0 • B := by
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact Submodule.smul_le_right.trans le_sup_right
  have hgood := rTensor_inclusion_injective_chain (M := M) (fun k ↦ A ⊔ I ^ k • B) hDB hD
    (rTensor_inclusion_injective hI _ h0) (fun k ↦ rTensor_inclusion_injective hI _ (hDI k)) N
  have hDN : A ⊔ I ^ N • B ≤ A := sup_le le_rfl (by rw [hN, Submodule.bot_smul]; exact bot_le)
  have hAD : A ≤ A ⊔ I ^ N • B := le_sup_left
  have hlast : Injective ((Submodule.inclusion hAD).rTensor M) :=
    rTensor_inclusion_injective hI _ (Submodule.smul_le_right.trans hDN)
  have : Submodule.inclusion h = Submodule.inclusion (hDB N) ∘ₗ Submodule.inclusion hAD := by
    ext; rfl
  rw [this, LinearMap.rTensor_comp, LinearMap.coe_comp]
  exact hgood.comp hlast

/-- **Local flatness criterion for a nilpotent ideal** (Stacks, Lemma 10.99.8, Tag 051C, last
statement): if `I` is nilpotent, `I ⊗_S M → M` is injective (`Tor₁^S(S/I, M) = 0`) and
`(S ⧸ I) ⊗_S M` is flat over `S ⧸ I`, then `M` is flat over `S`. -/
theorem flat_of_isNilpotent (hnil : IsNilpotent I) (hI : Injective (I.subtype.rTensor M))
    [Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] M)] : Module.Flat S M := by
  obtain ⟨N, hN⟩ := hnil
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  have : J.subtype = (⊤ : Ideal S).subtype ∘ₗ Submodule.inclusion (le_top : J ≤ ⊤) := by
    ext; rfl
  rw [this, LinearMap.rTensor_comp, LinearMap.coe_comp]
  have htop : Injective ((⊤ : Ideal S).subtype.rTensor M) := by
    have : (⊤ : Ideal S).subtype = (Submodule.topEquiv (R := S) (M := S)).toLinearMap := by
      ext; rfl
    rw [this]
    exact (LinearEquiv.rTensor M Submodule.topEquiv).injective
  exact htop.comp (rTensor_inclusion_injective_of_pow_eq_bot hI hN _)

end Criterion

section Principal

variable {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M] [Module S M]

/-- For a principal ideal `(ϖ)` with `ϖ ^ (n + 1) = 0`, the map `(ϖ) ⊗_S M → M` is injective as
soon as every `m` with `ϖ • m = 0` is a multiple `ϖ ^ n • m'`. -/
theorem rTensor_span_singleton_injective (ϖ : S) (n : ℕ) (hϖ : ϖ ^ (n + 1) = 0)
    (hM : ∀ m : M, ϖ • m = 0 → ∃ m', m = ϖ ^ n • m') :
    Injective ((Ideal.span {ϖ}).subtype.rTensor M) := by
  set I := Ideal.span {ϖ}
  let g : I := ⟨ϖ, Ideal.mem_span_singleton_self ϖ⟩
  have hgen : ∀ z : I ⊗[S] M, ∃ m, z = g ⊗ₜ m := by
    intro z
    induction z with
    | zero => exact ⟨0, by simp⟩
    | add a b ha hb =>
      obtain ⟨m₁, rfl⟩ := ha
      obtain ⟨m₂, rfl⟩ := hb
      exact ⟨m₁ + m₂, by rw [tmul_add]⟩
    | tmul x m =>
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp x.2
      refine ⟨s • m, ?_⟩
      have : x = s • g := Subtype.ext (by simp [g, hs])
      rw [this, smul_tmul]
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨m, rfl⟩ := hgen z
  have h0 : ϖ • m = 0 := by
    have := congrArg (TensorProduct.lid S M) hz
    simpa [g] using this
  obtain ⟨m', rfl⟩ := hM m h0
  rw [← smul_tmul]
  have : ϖ ^ n • g = 0 := Subtype.ext (by simp [g, ← pow_succ, hϖ])
  rw [this, zero_tmul]

/-- **Flatness criterion for a principal nilpotent ideal.** Let `ϖ ∈ S` with `ϖ ^ (n + 1) = 0`
and let `M` be an `S`-module such that every element killed by `ϖ` lies in `ϖ ^ n M` and
`M / ϖ M` is flat over `S / ϖ`. Then `M` is flat over `S`. (This is `flat_of_isNilpotent` for
`I = (ϖ)`, the first hypothesis giving `Tor₁^S(S/ϖ, M) = 0`.) -/
theorem flat_of_pow_succ_eq_zero (ϖ : S) (n : ℕ) (hϖ : ϖ ^ (n + 1) = 0)
    (hM : ∀ m : M, ϖ • m = 0 → ∃ m', m = ϖ ^ n • m')
    [Module.Flat (S ⧸ Ideal.span {ϖ}) ((S ⧸ Ideal.span {ϖ}) ⊗[S] M)] : Module.Flat S M :=
  flat_of_isNilpotent (I := Ideal.span {ϖ})
    ⟨n + 1, by rw [Ideal.span_singleton_pow, hϖ, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]⟩
    (rTensor_span_singleton_injective ϖ n hϖ hM)

omit [AddCommGroup M] [Module S M] in
/-- The annihilator condition `ann(a) ⊆ (aⁿ)` passes from `A` to `A[X]` (for `C a`). -/
theorem polynomial_mem_span_of_C_mul_eq_zero {A : Type*} [CommRing A] (a : A) (n : ℕ)
    (h : ∀ b : A, a * b = 0 → b ∈ Ideal.span {a ^ n}) (p : Polynomial A)
    (hp : Polynomial.C a * p = 0) : p ∈ Ideal.span {Polynomial.C a ^ n} := by
  rw [← map_pow, ← Set.image_singleton, ← Ideal.map_span, Ideal.mem_map_C_iff]
  intro i
  apply h
  rw [← Polynomial.coeff_C_mul, hp, Polynomial.coeff_zero]

end Principal

section Fibre

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal R)
  (M : Type*) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- If `J ⊗_R M → M` is injective, then `JS ⊗_S M → M` is injective (Stacks, Tag 06A5,
proof). -/
theorem rTensor_map_subtype_injective_of_injective (hRinj : Injective (J.subtype.rTensor M)) :
    Injective ((J.map (algebraMap R S)).subtype.rTensor M) := by
  set I := J.map (algebraMap R S)
  let jmap : J →ₗ[R] I :=
    { toFun := fun j ↦ ⟨algebraMap R S j, Ideal.mem_map_of_mem _ j.2⟩
      map_add' := fun x y ↦ Subtype.ext (by simp)
      map_smul' := fun r x ↦ Subtype.ext (by simp [Algebra.smul_def]) }
  let α : J ⊗[R] M →ₗ[R] I ⊗[S] M := TensorProduct.lift
    (LinearMap.mk₂ R (fun j m ↦ jmap j ⊗ₜ[S] m) (fun _ _ _ ↦ by simp [add_tmul])
      (fun r j m ↦ by simp [TensorProduct.smul_tmul'])
      (fun _ _ _ ↦ by simp [tmul_add])
      (fun r j m ↦ by
        rw [← algebraMap_smul S r m, TensorProduct.tmul_smul, algebraMap_smul]))
  let β : I ⊗[S] M →ₗ[S] M := (TensorProduct.lid S M).toLinearMap ∘ₗ I.subtype.rTensor M
  have hβα : ∀ t, β (α t) = TensorProduct.lid R M (J.subtype.rTensor M t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul j m => simp [α, β, jmap]
  have hα : Surjective α := by
    intro z
    induction z with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | tmul x m =>
      obtain ⟨x, hx⟩ := x
      induction hx using Submodule.span_induction generalizing m with
      | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        exact ⟨⟨j, hj⟩ ⊗ₜ m, by simp [α, jmap]⟩
      | zero => exact ⟨0, by rw [map_zero]; exact (zero_tmul _ _).symm.trans (by congr 1)⟩
      | add y z hy hz ihy ihz =>
        obtain ⟨a, ha⟩ := ihy m
        obtain ⟨b, hb⟩ := ihz m
        exact ⟨a + b, by rw [map_add, ha, hb, ← add_tmul]; rfl⟩
      | smul s y hy ih =>
        obtain ⟨a, ha⟩ := ih (s • m)
        refine ⟨a, ?_⟩
        rw [ha, ← smul_tmul]
        rfl
  have hβ : Injective β := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨t, rfl⟩ := hα z
    rw [hβα] at hz
    have : t = 0 := hRinj ((TensorProduct.lid R M).injective (hz.trans (map_zero _).symm))
    rw [this, map_zero]
  exact Injective.of_comp (f := TensorProduct.lid S M) hβ

/-- If `M` is flat over `R`, then `JS ⊗_S M → M` is injective (Stacks, Tag 06A5, proof). -/
theorem rTensor_map_subtype_injective [Module.Flat R M] :
    Injective ((J.map (algebraMap R S)).subtype.rTensor M) :=
  rTensor_map_subtype_injective_of_injective J M
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)

/-- **Critère de platitude par fibres, nilpotent case** (Stacks, Lemma 10.101.8, Tag 06A5, with
`S' = S`): let `R → S` be a ring map, `J ⊆ R` a nilpotent ideal and `M` an `S`-module which is
flat over `R` and such that `M / JM` is flat over `S / JS`. Then `M` is flat over `S`. -/
theorem flat_of_flat_fibre (hJ : IsNilpotent J) [Module.Flat R M]
    [Module.Flat (S ⧸ J.map (algebraMap R S)) ((S ⧸ J.map (algebraMap R S)) ⊗[S] M)] :
    Module.Flat S M := by
  obtain ⟨N, hN⟩ := hJ
  have hN' : J.map (algebraMap R S) ^ N = 0 := by
    rw [← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot]
    rfl
  exact flat_of_isNilpotent (M := M) ⟨N, hN'⟩ (rTensor_map_subtype_injective J M)

end Fibre

section Polynomial

open Polynomial

/-- Flatness of a base change `Q ⊗_T M` over `Q` only depends on `Q` up to `T`-algebra
isomorphism. -/
theorem flat_tensor_of_algEquiv {T Q P : Type*} [CommRing T] [CommRing Q] [CommRing P]
    [Algebra T Q] [Algebra T P] (e : Q ≃ₐ[T] P) (M : Type*) [AddCommGroup M] [Module T M]
    [Module.Flat P (P ⊗[T] M)] : Module.Flat Q (Q ⊗[T] M) := by
  letI : Algebra P Q := e.symm.toRingHom.toAlgebra
  haveI : IsScalarTower T P Q := IsScalarTower.of_algebraMap_eq fun t ↦ (e.symm.commutes t).symm
  exact Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange T P Q Q M).symm

variable {A : Type*} [CommRing A]
  (M : Type*) [AddCommGroup M] [Module A[X] M] [Module A M] [IsScalarTower A A[X] M]

/-- For an ideal `L ⊆ A`, the `A[X]`-submodule `L A[X] • M` is `L • M`. -/
theorem restrictScalars_map_C_smul_top (L : Ideal A) :
    ((L.map C : Ideal A[X]) • (⊤ : Submodule A[X] M)).restrictScalars A =
      L • (⊤ : Submodule A M) := by
  have hC : ∀ (l : A) (m : M), C l • m = l • m := fun l m ↦ by
    rw [← Polynomial.algebraMap_eq, algebraMap_smul]
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx (fun p hp m hm ↦ ?_) (fun _ _ hx hy ↦ add_mem hx hy)
    clear hm
    induction hp using Submodule.span_induction generalizing m with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      rw [hC]
      exact Submodule.smul_mem_smul hl Submodule.mem_top
    | zero => rw [zero_smul]; exact zero_mem _
    | add y z _ _ hy hz => rw [add_smul]; exact add_mem (hy m) (hz m)
    | smul q y _ hy => rw [smul_eq_mul, mul_comm, mul_smul]; exact hy _
  · rw [Submodule.smul_le]
    intro l hl m _
    rw [Submodule.restrictScalars_mem, ← hC]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem C hl) Submodule.mem_top

variable (I : Ideal A) (n : ℕ)

/-- **Flatness over `A[X] ⧸ (I A[X]) ^ n`** from flatness of the reduction mod `I ^ n` over
`A ⧸ I ^ n` and flatness of the reduction mod `I` over `A[X] ⧸ I A[X]` (an application of
`flat_of_isNilpotent`, via `flat_of_flat_fibre`'s argument with `R = A ⧸ I ^ n`). -/
theorem flat_quotient_polynomial [Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] M)]
    [Module.Flat (A[X] ⧸ I.map C) ((A[X] ⧸ I.map C) ⊗[A[X]] M)] :
    Module.Flat (A[X] ⧸ I.map C ^ n) ((A[X] ⧸ I.map C ^ n) ⊗[A[X]] M) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (A[X] ⧸ I.map C ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact Module.Flat.of_free
  set K := I.map C ^ n with hK
  have hKI : K ≤ I.map C := Ideal.pow_le_self hn.ne'
  set Q := A[X] ⧸ K
  set I' : Ideal Q := (I.map C).map (Ideal.Quotient.mkₐ A[X] K) with hI'
  have hnil : IsNilpotent I' := ⟨n, by
    rw [hI', ← Ideal.map_pow, ← hK]
    change Ideal.map (Ideal.Quotient.mk K) K = 0
    rw [Ideal.map_quotient_self]
    rfl⟩
  haveI := flat_tensor_of_algEquiv (DoubleQuot.quotQuotEquivQuotOfLEₐ A[X] hKI) M
  haveI : Module.Flat (Q ⧸ I') ((Q ⧸ I') ⊗[Q] (Q ⊗[A[X]] M)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A[X] Q (Q ⧸ I') (Q ⧸ I') M)
  -- the `Tor`-condition, through `R = A ⧸ I ^ n`
  have hle : I ^ n ≤ (K).comap (algebraMap A A[X]) := by
    rw [hK, ← Ideal.map_pow, Polynomial.algebraMap_eq]
    exact Ideal.le_comap_map
  letI : Algebra (A ⧸ I ^ n) Q := Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower A (A ⧸ I ^ n) Q := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (A ⧸ I ^ n) Q (Q ⊗[A[X]] M) := inferInstance
  haveI : IsScalarTower A (A ⧸ I ^ n) (Q ⊗[A[X]] M) := inferInstance
  have hsub : (K • (⊤ : Submodule A[X] M)).restrictScalars A = I ^ n • (⊤ : Submodule A M) := by
    rw [hK, ← Ideal.map_pow]
    exact restrictScalars_map_C_smul_top M (I ^ n)
  let eA : (Q ⊗[A[X]] M) ≃ₗ[A] (A ⧸ I ^ n) ⊗[A] M :=
    ((quotTensorEquivQuotSMul M K).restrictScalars A ≪≫ₗ
      (Submodule.Quotient.restrictScalarsEquiv A (K • ⊤)).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hsub) ≪≫ₗ (quotTensorEquivQuotSMul M (I ^ n)).symm
  haveI : Module.Flat (A ⧸ I ^ n) (Q ⊗[A[X]] M) :=
    Module.Flat.of_linearEquiv (eA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
  have hTor := rTensor_map_subtype_injective (S := Q) (I.map (Ideal.Quotient.mk (I ^ n)))
    (Q ⊗[A[X]] M)
  have heq : (I.map (Ideal.Quotient.mk (I ^ n))).map (algebraMap (A ⧸ I ^ n) Q) = I' := by
    rw [hI', Ideal.map_map]
    change _ = Ideal.map (Ideal.Quotient.mk K) (Ideal.map C I)
    rw [Ideal.map_map]
    rfl
  rw [heq] at hTor
  exact flat_of_isNilpotent hnil hTor

end Polynomial

end SemistableReduction.NilpotentFlatness
