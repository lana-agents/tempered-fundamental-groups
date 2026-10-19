/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.Module

/-!
# `ϖ`-purity of levels: flatness over `O/ϖᴺ` elementwise (Blueprint §12.8, M2.3 → M2.4, step 3f)

The level-`n` coverings of the M2 patching are modules over `O/ϖⁿ⁺¹` built from many pieces
(étale lifts, Zariski glueings, formal glueings, Kummer and cusp factors). Their flatness over
`O/ϖᴺ` (`N = n + 1`) is the first hypothesis of the fibrewise flatness criterion
(`NilpotentFlatness`). To avoid putting `O/ϖᴺ`-module structures on all pieces, we work with the
elementwise form (for `O` with `ϖ` a nonzerodivisor, this is flatness over the principal
Artinian ring `O/ϖᴺ`):

* **`PowFlat ϖ N M`**: for `i ≤ N`, `ϖⁱ m = 0` implies `m ∈ ϖᴺ⁻ⁱ M`.

Permanence properties:

* `PowFlat.quotient`: `T/ϖᴺT` for `T` without `ϖ`-torsion (the chart levels);
* **`PowFlat.of_flat`**: flat modules over a `PowFlat` ring killed by `ϖᴺ` (étale lifts,
  localizations, completions, base changes);
* `PowFlat.of_linearEquiv`, `PowFlat.prod`, `PowFlat.pi` (products of Kummer and cusp factors);
* **`PowFlat.of_isLocalizedModule_span`**: Zariski-local (glueing along basic opens);
* **`PowFlat.of_away_of_isBaseChange`**: from the localization away from `f` and the base change
  to the `f`-adic completion, for finite modules over a Noetherian ring (formal glueing at the
  nodes): an element killed by `fᴷ` whose image in the completion vanishes is zero (Krull).
-/

universe u v w

open TensorProduct

namespace SemistableReduction

/-- **`ϖ`-purity of exponent `N`**: `ϖⁱ m = 0` implies `m ∈ ϖᴺ⁻ⁱ M` for `i ≤ N` (for a module
killed by `ϖᴺ` over `O` with `ϖ` a nonzerodivisor: flatness over `O/ϖᴺ`). -/
def PowFlat {O : Type u} [CommRing O] (ϖ : O) (N : ℕ) (M : Type v) [AddCommGroup M]
    [Module O M] : Prop :=
  ∀ i ≤ N, ∀ m : M, ϖ ^ i • m = 0 → ∃ m' : M, m = ϖ ^ (N - i) • m'

namespace PowFlat

variable {O : Type u} [CommRing O] {ϖ : O} {N : ℕ}

/-- `PowFlat` is invariant under `O`-linear isomorphisms. -/
theorem of_linearEquiv {M : Type v} [AddCommGroup M] [Module O M] {M' : Type w} [AddCommGroup M']
    [Module O M'] (e : M ≃ₗ[O] M') (h : PowFlat ϖ N M) : PowFlat ϖ N M' := by
  intro i hi m hm
  obtain ⟨m', hm'⟩ := h i hi (e.symm m) (by rw [← map_smul, hm, map_zero])
  exact ⟨e m', by rw [← map_smul, ← hm', LinearEquiv.apply_symm_apply]⟩

/-- Binary products. -/
theorem prod {M : Type v} [AddCommGroup M] [Module O M] {M' : Type w} [AddCommGroup M']
    [Module O M'] (h : PowFlat ϖ N M) (h' : PowFlat ϖ N M') : PowFlat ϖ N (M × M') := by
  intro i hi m hm
  obtain ⟨a, ha⟩ := h i hi m.1 (congrArg Prod.fst hm)
  obtain ⟨b, hb⟩ := h' i hi m.2 (congrArg Prod.snd hm)
  exact ⟨(a, b), Prod.ext ha hb⟩

/-- Products. -/
theorem pi {ι : Type w} {M : ι → Type v} [∀ j, AddCommGroup (M j)] [∀ j, Module O (M j)]
    (h : ∀ j, PowFlat ϖ N (M j)) : PowFlat ϖ N (∀ j, M j) := by
  intro i hi m hm
  choose a ha using fun j ↦ h j i hi (m j) (congrFun hm j)
  exact ⟨a, funext ha⟩

/-- **The levels of a chart**: `T/ϖᴺT` for an `O`-algebra `T` on which `ϖ` is a nonzerodivisor. -/
theorem quotient {T : Type v} [CommRing T] [Algebra O T] (hreg : IsSMulRegular T ϖ)
    (K : Ideal T) (hK : K = Ideal.span {algebraMap O T ϖ ^ N}) : PowFlat ϖ N (T ⧸ K) := by
  intro i hi m hm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O T (T ⧸ K), Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hK, Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  refine ⟨Ideal.Quotient.mk K y, ?_⟩
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O T (T ⧸ K), Ideal.Quotient.algebraMap_eq,
    ← map_mul]
  congr 1
  apply hreg.pow i
  change ϖ ^ i • x = ϖ ^ i • (algebraMap O T (ϖ ^ (N - i)) * y)
  rw [Algebra.smul_def, Algebra.smul_def, ← hy, map_pow, map_pow, ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hi, mul_comm]

/-- **Flat modules over a `PowFlat` ring killed by `ϖᴺ` are `PowFlat`.** -/
theorem of_flat {B : Type v} [CommRing B] [Algebra O B] (hB : PowFlat ϖ N B)
    (hkill : algebraMap O B ϖ ^ N = 0) {M : Type w} [AddCommGroup M] [Module B M] [Module O M]
    [IsScalarTower O B M] [Module.Flat B M] : PowFlat ϖ N M := by
  intro i hi m hm
  set b := algebraMap O B ϖ
  have hex : Function.Exact (LinearMap.mulLeft B (b ^ (N - i)))
      (LinearMap.mulLeft B (b ^ i)) := by
    intro x
    simp only [LinearMap.mulLeft_apply, Set.mem_range]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hB i hi x (by rw [Algebra.smul_def, map_pow]; exact hx)
      exact ⟨y, by rw [hy, Algebra.smul_def, map_pow]⟩
    · rintro ⟨y, rfl⟩
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi, hkill, zero_mul]
  have hex' := Module.Flat.lTensor_exact M hex
  have key : ∀ (c : B) (z : M ⊗[B] B),
      TensorProduct.rid B M ((LinearMap.mulLeft B c).lTensor M z) =
        c • TensorProduct.rid B M z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [mul_smul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hz : (LinearMap.mulLeft B (b ^ i)).lTensor M ((TensorProduct.rid B M).symm m) = 0 := by
    apply (TensorProduct.rid B M).injective
    rw [key, LinearEquiv.apply_symm_apply, map_zero, ← map_pow, algebraMap_smul]
    exact hm
  obtain ⟨y, hy⟩ := (hex' _).1 hz
  refine ⟨TensorProduct.rid B M y, ?_⟩
  have := congrArg (TensorProduct.rid B M) hy
  rw [key, LinearEquiv.apply_symm_apply] at this
  rw [← this, ← map_pow, algebraMap_smul]

/-- **`PowFlat` is Zariski-local**: if the localizations of `M` away from the elements of a set
generating the unit ideal are `PowFlat`, so is `M`. -/
theorem of_isLocalizedModule_span {R : Type v} [CommRing R] [Algebra O R]
    {M : Type w} [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M]
    (s : Set R) (hs : Ideal.span s = ⊤) (Ml : s → Type w) [∀ a, AddCommGroup (Ml a)]
    [∀ a, Module R (Ml a)] [∀ a, Module O (Ml a)] [∀ a, IsScalarTower O R (Ml a)]
    (g : ∀ a : s, M →ₗ[R] Ml a) [∀ a : s, IsLocalizedModule (Submonoid.powers (a : R)) (g a)]
    (h : ∀ a, PowFlat ϖ N (Ml a)) : PowFlat ϖ N M := by
  intro i hi m hm
  let W : Submodule R M := Submodule.span R (Set.range (fun x : M ↦ ϖ ^ (N - i) • x))
  have hW : ∀ x ∈ W, ∃ y : M, x = ϖ ^ (N - i) • y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨y, rfl⟩ := hx; exact ⟨y, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by simp⟩
    | smul r x _ hx => obtain ⟨a, rfl⟩ := hx; exact ⟨r • a, by rw [smul_comm]⟩
  apply hW
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem W s hs m fun a ↦ ?_
  obtain ⟨z, hz⟩ := h a i hi (g a m) (by rw [← LinearMap.map_smul_of_tower, hm, map_zero])
  obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers (a : R)) (g a) z
  have h1 : g a ((a : R) ^ k • m) = g a (ϖ ^ (N - i) • y) := by
    have hy' : (a : R) ^ k • z = g a y := hy
    rw [map_smul, hz, smul_comm, hy', LinearMap.map_smul_of_tower]
  obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (a : R)) h1
  refine ⟨l + k, ?_⟩
  change (a : R) ^ l • (a : R) ^ k • m = (a : R) ^ l • ϖ ^ (N - i) • y at hl
  rw [pow_add, mul_smul, hl, smul_comm]
  exact Submodule.subset_span ⟨_, rfl⟩

/-- **Krull**: over a Noetherian ring, an element of a finite module killed by a power of `f`
whose image in the base change to the `f`-adic completion vanishes is zero. -/
theorem eq_zero_of_pow_smul_of_tmul {R : Type v} [CommRing R] [IsNoetherianRing R] (f : R)
    {X : Type w} [AddCommGroup X] [Module R X] [Module.Finite R X] {x : X} {K : ℕ}
    (hK : f ^ K • x = 0)
    (h0 : (1 : AdicCompletion (Ideal.span {f}) R) ⊗ₜ[R] x = 0) : x = 0 := by
  have h1 : AdicCompletion.of (Ideal.span {f}) X x = 0 := by
    have := congrArg (AdicCompletion.ofTensorProduct (Ideal.span {f}) X) h0
    rwa [AdicCompletion.ofTensorProduct_tmul, one_smul, map_zero] at this
  have hmem : x ∈ (⨅ i : ℕ, Ideal.span {f} ^ i • ⊤ : Submodule R X) := by
    refine Submodule.mem_iInf _ |>.2 fun i ↦ ?_
    have := congrArg (fun z ↦ z.1 i) h1
    simp only [AdicCompletion.of_apply] at this
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  obtain ⟨⟨r, hr⟩, hrx⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff _ x).1 hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  have hpow : ∀ n : ℕ, (c * f) ^ n • x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hrx, ih]
  rw [← hpow K, mul_pow, mul_smul, hK, smul_zero]

/-- **`PowFlat` from `D(f)` and the formal neighbourhood of `V(f)`** (formal glueing at the
nodes): for a finite module `G` over a Noetherian ring `R`, if the localization `P = G_f` and the
base change `N = R̂ ⊗_R G` to the `f`-adic completion are `PowFlat`, so is `G`. -/
theorem of_away_of_isBaseChange {R : Type v} [CommRing R] [IsNoetherianRing R] [Algebra O R]
    (f : R) {G : Type w} [AddCommGroup G] [Module R G] [Module.Finite R G] [Module O G]
    [IsScalarTower O R G] {P : Type w} [AddCommGroup P] [Module R P] [Module O P]
    [IsScalarTower O R P] (gP : G →ₗ[R] P) [IsLocalizedModule (Submonoid.powers f) gP]
    {Nm : Type w} [AddCommGroup Nm] [Module R Nm] [Module (AdicCompletion (Ideal.span {f}) R) Nm]
    [IsScalarTower R (AdicCompletion (Ideal.span {f}) R) Nm] [Module O Nm] [IsScalarTower O R Nm]
    (gN : G →ₗ[R] Nm) (hbc : IsBaseChange (AdicCompletion (Ideal.span {f}) R) gN)
    (hP : PowFlat ϖ N P) (hN : PowFlat ϖ N Nm) : PowFlat ϖ N G := by
  intro i hi m hm
  set c : R := algebraMap O R (ϖ ^ (N - i))
  let W : Submodule R G := LinearMap.range (LinearMap.lsmul R G c)
  suffices hx : Submodule.Quotient.mk (p := W) m = 0 by
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero W).1 hx
    exact ⟨y, by rw [← hy, LinearMap.lsmul_apply]; exact algebraMap_smul R _ y⟩
  -- the image of `m` is killed by a power of `f`
  obtain ⟨p, hp⟩ := hP i hi (gP m) (by rw [← LinearMap.map_smul_of_tower, hm, map_zero])
  obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers f) gP p
  have hy' : f ^ k • p = gP y := hy
  have h1 : gP (f ^ k • m) = gP (c • y) := by
    rw [map_smul, hp, smul_comm, hy', ← LinearMap.map_smul_of_tower]
    simp only [c, algebraMap_smul]
  obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h1
  change f ^ l • f ^ k • m = f ^ l • c • y at hl
  have hK : f ^ (l + k) • Submodule.Quotient.mk (p := W) m = 0 := by
    rw [← Submodule.Quotient.mk_smul, pow_add, mul_smul, hl, Submodule.Quotient.mk_eq_zero]
    exact ⟨f ^ l • y, by rw [LinearMap.lsmul_apply, smul_comm]⟩
  refine eq_zero_of_pow_smul_of_tmul f hK ?_
  -- the image of `m` in the completion vanishes
  obtain ⟨ν, hν⟩ := hN i hi (gN m) (by rw [← LinearMap.map_smul_of_tower, hm, map_zero])
  set e := hbc.equiv
  have hkill : ∀ t : AdicCompletion (Ideal.span {f}) R ⊗[R] G,
      (W.mkQ.lTensor (AdicCompletion (Ideal.span {f}) R)) (c • t) = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a g =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, LinearMap.lTensor_tmul,
        Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W (x := c • g)).2 ⟨g, rfl⟩,
        TensorProduct.tmul_zero]
    | add a b ha hb => rw [smul_add, map_add, ha, hb, add_zero]
  have h2 : (1 : AdicCompletion (Ideal.span {f}) R) ⊗ₜ[R] m = c • e.symm ν := by
    apply e.injective
    rw [IsBaseChange.equiv_tmul, one_smul, LinearMapClass.map_smul_of_tower,
      LinearEquiv.apply_symm_apply, hν]
    exact (algebraMap_smul R _ ν).symm
  have := congrArg (W.mkQ.lTensor (AdicCompletion (Ideal.span {f}) R)) h2
  rwa [hkill, LinearMap.lTensor_tmul] at this

end PowFlat

end SemistableReduction
