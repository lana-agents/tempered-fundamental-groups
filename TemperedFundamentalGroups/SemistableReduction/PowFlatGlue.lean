/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.PowFlatPatch
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Patch

/-!
# `ϖ`-purity of the glued coverings (Blueprint §12.8, M2.4, step 3f)

* `PowFlat.of_isLocalizedModule_two` (Zariski glueing along `D(a) ∪ D(b)`), **`PowFlat.glued`**
  (`ZariskiTwo.glued`), `of_isLocalizedModule`, `localization` (localizations);
* `PowFlat.input_R`, `input_E`, `input_G`, **`PowFlat.input_Y`**: the covering `Y n` of an
  `NodeEtaleGlue.Input` over the first chart (stated with explicit instances, since `Y0` is a `def`
  whose additive structure only unifies with that of its algebra structure at default
  transparency);
* **`PowFlat.etale`** (étale pieces, `Piece0.ofEtale`), **`PowFlat.patchInput`**,
  `patchInput_piece` (the cusp patches `PatchInput.piece`).
-/

universe u v w

namespace SemistableReduction

namespace PowFlat

/-! ### Zariski glueing along two basic opens -/

section Two

variable {O : Type u} [CommRing O] {ϖ : O} {N : ℕ} {R : Type v} [CommRing R] [Algebra O R]
  {M : Type w} [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M]

/-- The local step of `of_isLocalizedModule_two`: an element killed by `ϖⁱ` lies in `ϖᴺ⁻ⁱ M`
after multiplication by a power of `c`, if `M_c` is `PowFlat`. -/
lemma exists_pow_smul_mem {i : ℕ} (hi : i ≤ N) {m : M} (hm : ϖ ^ i • m = 0) (c : R)
    {Mc : Type w} [AddCommGroup Mc] [Module R Mc] [Module O Mc] [IsScalarTower O R Mc]
    (g : M →ₗ[R] Mc) [IsLocalizedModule (Submonoid.powers c) g] (h : PowFlat ϖ N Mc) :
    ∃ k : ℕ, c ^ k • m ∈
      Submodule.span R (Set.range (fun x : M ↦ ϖ ^ (N - i) • x)) := by
  obtain ⟨z, hz⟩ := h i hi (g m) (by rw [← LinearMap.map_smul_of_tower, hm, map_zero])
  obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers c) g z
  have h1 : g (c ^ k • m) = g (ϖ ^ (N - i) • y) := by
    have hy' : c ^ k • z = g y := hy
    rw [map_smul, hz, smul_comm, hy', LinearMap.map_smul_of_tower]
  obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c) h1
  refine ⟨l + k, ?_⟩
  change c ^ l • c ^ k • m = c ^ l • ϖ ^ (N - i) • y at hl
  rw [pow_add, mul_smul, hl]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self y))

/-- **`PowFlat` is local for a covering by two basic opens** `D(a) ∪ D(b)`. -/
theorem of_isLocalizedModule_two (a b : R) (hab : Ideal.span {a, b} = ⊤)
    {Ma : Type w} [AddCommGroup Ma] [Module R Ma] [Module O Ma] [IsScalarTower O R Ma]
    {Mb : Type w} [AddCommGroup Mb] [Module R Mb] [Module O Mb] [IsScalarTower O R Mb]
    (ga : M →ₗ[R] Ma) [IsLocalizedModule (Submonoid.powers a) ga]
    (gb : M →ₗ[R] Mb) [IsLocalizedModule (Submonoid.powers b) gb]
    (ha : PowFlat ϖ N Ma) (hb : PowFlat ϖ N Mb) : PowFlat ϖ N M := by
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
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem W {a, b} hab m fun r ↦ ?_
  rcases r with ⟨r, hr⟩
  rcases hr with rfl | hr
  · exact exists_pow_smul_mem hi hm r ga ha
  · rw [Set.mem_singleton_iff] at hr
    subst hr
    exact exists_pow_smul_mem hi hm r gb hb

/-- **Localizations of `PowFlat` modules are `PowFlat`.** -/
theorem of_isLocalizedModule {M' : Type w} [AddCommGroup M'] [Module R M'] [Module O M']
    [IsScalarTower O R M'] (S : Submonoid R) (g : M →ₗ[R] M') [IsLocalizedModule S g]
    (h : PowFlat ϖ N M) : PowFlat ϖ N M' := by
  intro i hi m hm
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj S g m
  have hx' : s.1 • m = g x := hx
  have h1 : g (ϖ ^ i • x) = g 0 := by
    rw [LinearMap.map_smul_of_tower, ← hx', smul_comm, hm, smul_zero, map_zero]
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) h1
  rw [smul_zero, smul_comm] at ht
  obtain ⟨y, hy⟩ := h i hi _ ht
  refine ⟨IsLocalizedModule.mk' g y (t * s), ?_⟩
  rw [← algebraMap_smul R (ϖ ^ (N - i)), ← IsLocalizedModule.mk'_smul, algebraMap_smul, ← hy]
  symm
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, Submonoid.smul_def, LinearMap.map_smul,
    ← hx', Submonoid.coe_mul, mul_smul]

/-- **Localizations of `PowFlat` algebras** (stated for algebras, so that it applies to algebras
whose additive structure only unifies with the one of their algebra structure at default
transparency, such as `NodeEtaleGlue.Y0`). -/
theorem localization {w : R} {A : Type w} [CommRing A] [Algebra R A] (h : PowFlat w N A)
    (S : Submonoid R) {A' : Type w} [CommRing A'] [Algebra R A'] [Algebra A A']
    [IsScalarTower R A A'] [IsLocalization (Algebra.algebraMapSubmonoid A S) A'] :
    PowFlat w N A' := by
  haveI : IsLocalizedModule S (IsScalarTower.toAlgHom R A A').toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  exact of_isLocalizedModule (O := R) S (IsScalarTower.toAlgHom R A A').toLinearMap h

end Two

/-- **The glued algebra** `Ba ×_{Bab} Bb` of a Zariski glueing along `D(a) ∪ D(b)`. -/
theorem glued {R : Type u} [CommRing R] {w : R} {N : ℕ} (a b : R)
    (hab : Ideal.span {a, b} = ⊤) {Ba Bb Bab : Type u} [CommRing Ba] [CommRing Bb] [CommRing Bab]
    [Algebra R Ba] [Algebra R Bb] [Algebra R Bab] {ρa : Ba →ₐ[R] Bab} {ρb : Bb →ₐ[R] Bab}
    (ha : IsUnit (algebraMap R Ba a))
    (hb : letI := ρb.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Bb a) Bab)
    (hb' : IsUnit (algebraMap R Bb b))
    (ha' : letI := ρa.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Ba b) Bab)
    (hA : PowFlat w N Ba) (hB : PowFlat w N Bb) : PowFlat w N (ZariskiTwo.glued ρa ρb) := by
  haveI := ZariskiTwo.isLocalizedModule_fst (ρa := ρa) a ha hb
  haveI := ZariskiTwo.isLocalizedModule_snd (ρb := ρb) b hb' ha'
  exact of_isLocalizedModule_two (O := R) a b hab (ZariskiTwo.fst ρa ρb).toLinearMap
    (ZariskiTwo.snd ρa ρb).toLinearMap hA hB

/-! ### The covering over the first chart (`NodeEtaleGlue.Input`) -/

section Input

open NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O} (I : Input θ cov₀ πL)
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {ϖ : O} {N : ℕ} {n : ℕ}
  (hB : PowFlat ϖ N (I.B n)) (hw : algebraMap O (I.B n) ϖ ^ N = 0)

include hB hw in
/-- The node charts `R n = B n[1/a]`. -/
theorem input_R : PowFlat ϖ N (I.R n) := by
  haveI : Module.Flat (I.B n) (I.R n) := IsLocalization.flat _ (Submonoid.powers (I.a n))
  exact of_flat (B := I.B n) hB hw

include hB hw in
/-- The étale pieces `E n` over `D(b)` (finite over `B n[1/b]`), as modules over themselves. -/
theorem input_E [IsNoetherianRing (I.B n)]
    (hfinE : ∃ s : Finset (I.E n), ∀ p : I.E n, ∃ k : ℕ,
      algebraMap I.B0 (I.B n) I.b0 ^ k • p ∈ Submodule.span (I.B n) (s : Set (I.E n))) :
    PowFlat (algebraMap (I.B n) (I.E n) (algebraMap O (I.B n) ϖ)) N (I.E n) := by
  haveI := flat_of_away (I.hbE n) hfinE
  exact flat_self (algebraMap_of hB) hw

include hB hw in
include hO in
/-- The node patches `G n` over the node charts, as `B0`-modules (`w ∈ B0` mapping to `ϖ`). -/
theorem input_G [IsDomain O] (hπ : ∀ j, πL j ≠ 0) (hϖ : ϖ ≠ 0)
    (hI : I.T.I n = Ideal.span {ϖ ^ N}) {w : I.B0}
    (hwB : algebraMap I.B0 (I.B n) w = algebraMap O (I.B n) ϖ) :
    letI := alg0G I.T hθ I.B I.B0 n
    PowFlat w N (I.T.G hθ n) := by
  letI := alg0G I.T hθ I.B I.B0 n
  have hwR : algebraMap O (I.R n) ϖ ^ N = 0 := by
    rw [IsScalarTower.algebraMap_apply O (I.B n) (I.R n), ← map_pow, hw, map_zero]
  have h := PowFlat.data_of_isDomain hθ hO I.T hπ n hϖ (input_R I hB hw) hwR hI
  refine of_addEquiv (AddEquiv.refl _) (fun x ↦ ?_) h
  rw [AddEquiv.refl_apply, AddEquiv.refl_apply, Algebra.smul_def, Algebra.smul_def]
  congr 1
  change algebraMap (I.R n) (I.T.G hθ n) (algebraMap (I.B n) (I.R n)
    (algebraMap I.B0 (I.B n) w)) = algebraMap (I.R n) (I.T.G hθ n) (algebraMap O (I.R n) ϖ)
  rw [hwB, ← IsScalarTower.algebraMap_apply O (I.B n) (I.R n)]

include hO hB hw in
/-- **The covering `Y n` over the first chart is `PowFlat`** (as a `B0`-module, `w ∈ B0` mapping
to `ϖ`): glued from the node patch `G n` over `D(a)` and the étale piece `E n` over `D(b)`.
(The instances are explicit: `Y0` is a `def`, and unifying its additive structure with the one
of its algebra structure fails at instance transparency.) -/
theorem input_Y [IsDomain O] [IsNoetherianRing (I.B n)] (hπ : ∀ j, πL j ≠ 0) (hϖ : ϖ ≠ 0)
    (hI : I.T.I n = Ideal.span {ϖ ^ N})
    (hfinE : ∃ s : Finset (I.E n), ∀ p : I.E n, ∃ k : ℕ,
      algebraMap I.B0 (I.B n) I.b0 ^ k • p ∈ Submodule.span (I.B n) (s : Set (I.E n)))
    {w : I.B0} (hwB : algebraMap I.B0 (I.B n) w = algebraMap O (I.B n) ϖ) :
    @PowFlat I.B0 _ w N (I.Y hθ n) _ Algebra.toModule := by
  have hG := input_G I hθ hO hB hw hπ hϖ hI hwB
  have hE0 := input_E I hB hw hfinE
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  have hE : PowFlat w N (I.E n) := by
    refine of_addEquiv (AddEquiv.refl _) (fun x ↦ ?_) hE0
    change algebraMap (I.B n) (I.E n) (algebraMap I.B0 (I.B n) w) * x = _
    rw [hwB]
    rfl
  haveI := locFst I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv
    I.hJB I.B0 (fun _ ↦ rfl) n
  haveI := locSnd I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
    I.hdiv I.hbb I.hJB I.B0 (fun _ ↦ rfl) n
  have h := of_isLocalizedModule_two (O := I.B0) I.a0 I.b0 I.hab
    (ZariskiTwo.fst (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hJB I.B0 n) (ρb0 I.B I.a I.E I.B0 n)).toLinearMap
    (ZariskiTwo.snd (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
      I.hdiv I.hJB I.B0 n) (ρb0 I.B I.a I.E I.B0 n)).toLinearMap hG hE
  refine @of_addEquiv N I.B0 _ w (I.Y hθ n) _ Algebra.toModule I.B0 _ w _ _ _ ?_ ?_ h
  · exact AddEquiv.refl _
  · exact fun _ ↦ rfl

end Input

/-! ### The pieces over the second chart (`NodeEtaleGlue.Piece0`) -/

/-- **Étale pieces**: a formally étale algebra `E` over a Noetherian `PowFlat` ring `B` killed by
`ϖᴺ`, finite over `B[1/c]` (`Piece0.ofEtale`, the étale lifts `E n` of `Input`). -/
theorem etale {O : Type u} [CommRing O] {ϖ : O} {N : ℕ} {B : Type u} [CommRing B]
    [IsNoetherianRing B] [Algebra O B] (hB : PowFlat ϖ N B) (hw : algebraMap O B ϖ ^ N = 0)
    {E : Type u} [CommRing E] [Algebra B E] [Algebra O E] [IsScalarTower O B E]
    [Algebra.FormallyEtale B E] {c : B} (hc : IsUnit (algebraMap B E c))
    (hfin : ∃ s : Finset E, ∀ p : E, ∃ k : ℕ, c ^ k • p ∈ Submodule.span B (s : Set E)) :
    PowFlat ϖ N E := by
  haveI := flat_of_away hc hfin
  exact of_flat (B := B) hB hw

section Patch

open NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}

/-- **The patch pieces** (`PatchInput.piece`: a tower of patched algebras with cusp factors on
`R n = B' n[1/c₀]`) are `PowFlat`. -/
theorem patchInput [IsDomain O] (D : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL)
    (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (hπ : ∀ j, πL j ≠ 0)
    (hϖ : ϖ ≠ 0) {N n : ℕ} (hB : PowFlat ϖ N (B' n)) (hw : algebraMap O (B' n) ϖ ^ N = 0)
    (hI : D.T.I n = Ideal.span {ϖ ^ N}) : PowFlat ϖ N (D.G hθ n) := by
  haveI : Module.Flat (B' n) (D.R n) :=
    IsLocalization.flat _ (Submonoid.powers (algebraMap B0' (B' n) c0))
  have hR : PowFlat ϖ N (D.R n) := of_flat (B := B' n) hB hw
  have hwR : algebraMap O (D.R n) ϖ ^ N = 0 := by
    rw [IsScalarTower.algebraMap_apply O (B' n) (D.R n), ← map_pow, hw, map_zero]
  have h : PowFlat (algebraMap O (D.R n) ϖ) N (D.G hθ n) :=
    PowFlat.data_of_isDomain hθ hO D.T hπ n hϖ hR hwR hI
  exact of_algebraMap h

/-- The pieces `(PatchInput.piece D).P n`. -/
theorem patchInput_piece [IsDomain O] [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)]
    [∀ n, IsScalarTower O (B' (n + 1)) (B' n)] (D : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL)
    (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (hπ : ∀ j, πL j ≠ 0)
    (hϖ : ϖ ≠ 0) {N n : ℕ} (hB : PowFlat ϖ N (B' n)) (hw : algebraMap O (B' n) ϖ ^ N = 0)
    (hI : D.T.I n = Ideal.span {ϖ ^ N}) : PowFlat ϖ N ((D.piece hθ hO).P n) :=
  patchInput D hθ hO hπ hϖ hB hw hI

end Patch

end PowFlat

end SemistableReduction
