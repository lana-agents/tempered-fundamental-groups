/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.PowFlat
import TemperedFundamentalGroups.SemistableReduction.LevelTowerMk

/-!
# `ϖ`-purity of the patched algebras of a level tower (Blueprint §12.8, M2.4, step 3f)

The patched algebra `G n = P ×_{N_f} NF` of `LevelTower` (formal glueing of the étale lift `P`
over `D(f n)` with the lifted formal model `NF = ∏ Kummer factors × ∏ cusp factors` along
`V(f n)`) is `PowFlat ϖ N` (`N = n + 1` at level `n`) if the chart `R n` is:

* `PowFlat.of_addEquiv`, `of_algebraMap`, `algebraMap_of`: transport along additive
  isomorphisms compatible with the actions of `ϖ`, and change of the scalar ring;
* `PowFlat.of_surjective`: quotients `T/ϖᴺ` of `ϖ`-torsion-free algebras (as images);
  **`PowFlat.node`**: the reduced Kummer algebras `(O/ϖᴺ)[s,t]/(st − π̄)` over a domain;
* `PowFlat.flat_of_away`: the étale lifts (formally étale, finite over `R_f`) are flat;
* `PowFlat.flat_self`: flat algebras over a `PowFlat` ring killed by `ϖᴺ`;
* **`PowFlat.patch`**: the patched algebra (`of_away_of_isBaseChange`);
* `PowFlat.hat`, `PowFlat.cPiece` (cusp factors, free over `R̂/(1 − δ̃)`), **`PowFlat.kPiece`**
  (Kummer factors `≃ B_I ⊗_{A_I} R̂/(1 − ε̃)`, flat over `B_I`; `KummerFactorQuot.equiv`);
* **`PowFlat.level`**, **`PowFlat.data`**, **`PowFlat.data_of_isDomain`**: the patched algebras
  of a `LevelTower.Level` / `LevelTower.Data` (over a domain `O`, `I n = (ϖᴺ)`, `π_j ≠ 0`).
-/

universe u v w

open TensorProduct

namespace SemistableReduction

namespace PowFlat

variable {N : ℕ}

/-- Transport along an additive isomorphism compatible with the actions of `ϖ` and `ϖ'`. -/
theorem of_addEquiv {O : Type u} [CommRing O] {ϖ : O} {M : Type v} [AddCommGroup M] [Module O M]
    {O' : Type*} [CommRing O'] {ϖ' : O'} {M' : Type w} [AddCommGroup M'] [Module O' M']
    (e : M ≃+ M') (he : ∀ m, e (ϖ • m) = ϖ' • e m) (h : PowFlat ϖ' N M') : PowFlat ϖ N M := by
  have hpow : ∀ (i : ℕ) (m : M), e (ϖ ^ i • m) = ϖ' ^ i • e m := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro m; rw [pow_succ', mul_smul, he, ih, ← mul_smul, ← pow_succ']
  intro i hi m hm
  obtain ⟨m', hm'⟩ := h i hi (e m) (by rw [← hpow, hm, map_zero])
  refine ⟨e.symm m', e.injective ?_⟩
  rw [hpow, AddEquiv.apply_symm_apply, hm']

/-- Restriction of scalars: `PowFlat` for `algebraMap O R ϖ` gives `PowFlat` for `ϖ`. -/
theorem of_algebraMap {O : Type u} [CommRing O] {ϖ : O} {R : Type*} [CommRing R] [Algebra O R]
    {M : Type w} [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower O R M]
    (h : PowFlat (algebraMap O R ϖ) N M) : PowFlat ϖ N M :=
  of_addEquiv (AddEquiv.refl M) (fun m ↦ (algebraMap_smul R ϖ m).symm) h

/-- Extension of scalars: `PowFlat` for `ϖ` gives `PowFlat` for `algebraMap O R ϖ`. -/
theorem algebraMap_of {O : Type u} [CommRing O] {ϖ : O} {R : Type*} [CommRing R] [Algebra O R]
    {M : Type w} [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower O R M]
    (h : PowFlat ϖ N M) : PowFlat (algebraMap O R ϖ) N M :=
  of_addEquiv (AddEquiv.refl M) (fun m ↦ algebraMap_smul R ϖ m) h

/-- **Images of `ϖ`-torsion-free algebras** with kernel `(ϖᴺ)`. -/
theorem of_surjective {O : Type u} [CommRing O] {ϖ : O} {T : Type v} [CommRing T] [Algebra O T]
    (hreg : IsSMulRegular T ϖ) {S : Type w} [CommRing S] [Algebra O S] (φ : T →ₐ[O] S)
    (hφ : Function.Surjective φ) (hK : RingHom.ker φ = Ideal.span {algebraMap O T ϖ ^ N}) :
    PowFlat ϖ N S := by
  intro i hi m hm
  obtain ⟨x, rfl⟩ := hφ m
  rw [← map_smul, ← RingHom.mem_ker, hK, Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  refine ⟨φ y, ?_⟩
  rw [← map_smul]
  congr 1
  apply hreg.pow i
  change ϖ ^ i • x = ϖ ^ i • ϖ ^ (N - i) • y
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hi, ← hy, Algebra.smul_def, map_pow, mul_comm]

section Node

open KummerEtale

/-- `ϖ` is a nonzerodivisor on the node `O[u,v]/(uv − c)` over a domain, for `c ≠ 0`. -/
theorem node_isSMulRegular {O : Type u} [CommRing O] [IsDomain O] {c : O} (hc : c ≠ 0) {ϖ : O}
    (hϖ : ϖ ≠ 0) : IsSMulRegular (Node O c) ϖ := by
  intro x y hxy
  apply Node.laurent_injective hc one_pos
  have h := congrArg (Node.laurent c 1) hxy
  simp only [map_smul] at h
  rw [Algebra.smul_def, Algebra.smul_def] at h
  refine mul_left_cancel₀ ?_ h
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) (LaurentPolynomial (FractionRing O)),
    LaurentPolynomial.algebraMap_apply]
  intro h0
  rw [← LaurentPolynomial.algebraMap_apply, map_eq_zero_iff _
    (algebraMap (FractionRing O) (LaurentPolynomial (FractionRing O))).injective,
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective O (FractionRing O))] at h0
  exact hϖ h0

/-- The base change `O[u,v]/(uv − c) → (O/I)[u,v]/(uv − c̄)` as an `O`-algebra map. -/
noncomputable def nodeRed {O : Type u} [CommRing O] (I : Ideal O) (c : O) :
    Node O c →ₐ[O] Node (O ⧸ I) (Ideal.Quotient.mk I c) :=
  { Node.baseMap (Ideal.Quotient.mk I) (a := c) rfl with
    commutes' := fun o ↦ Node.baseMap_algebraMap _ _ o }

/-- **The reduced node is `PowFlat`**: `(O/ϖᴺ)[u,v]/(uv − c̄)` for a domain `O`, `c, ϖ ≠ 0`. -/
theorem node {O : Type u} [CommRing O] [IsDomain O] {c : O} (hc : c ≠ 0) {ϖ : O} (hϖ : ϖ ≠ 0)
    {N : ℕ} (I : Ideal O) (hI : I = Ideal.span {ϖ ^ N}) :
    PowFlat ϖ N (Node (O ⧸ I) (Ideal.Quotient.mk I c)) := by
  refine of_surjective (node_isSMulRegular hc hϖ) (nodeRed I c)
    (Node.surjective_baseMap rfl Ideal.Quotient.mk_surjective) ?_
  change RingHom.ker (Node.baseMap (Ideal.Quotient.mk I) (a := c) rfl) = _
  rw [Node.ker_baseMap rfl Ideal.Quotient.mk_surjective, Ideal.mk_ker, hI, Ideal.map_span,
    Set.image_singleton, map_pow]

end Node

/-! ### Étale lifts -/

/-- A formally étale `R`-algebra which is finite over `R_f` (in the form of `Level.hP`) is of
finite type over `R`. -/
theorem finiteType_of_away {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
    {f : R} (hfP : IsUnit (algebraMap R P f))
    (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P)) :
    Algebra.FiniteType R P := by
  classical
  obtain ⟨s, hs⟩ := hP
  obtain ⟨g, hg⟩ := hfP.exists_left_inv
  refine ⟨⟨insert g s, eq_top_iff.mpr fun p _ ↦ ?_⟩⟩
  obtain ⟨k, hk⟩ := hs p
  have h1 : f ^ k • p ∈ Subalgebra.toSubmodule
      (Algebra.adjoin R ((insert g s : Finset P) : Set P)) :=
    Submodule.span_le.mpr (fun x hx ↦ Algebra.subset_adjoin (Finset.mem_insert_of_mem hx)) hk
  have hg' : g ∈ Algebra.adjoin R ((insert g s : Finset P) : Set P) :=
    Algebra.subset_adjoin (Finset.mem_insert_self g s)
  have : p = g ^ k * (f ^ k • p) := by
    rw [Algebra.smul_def, map_pow, ← mul_assoc, ← mul_pow, hg, one_pow, one_mul]
  rw [this]
  exact mul_mem (pow_mem hg' k) h1

/-- **The étale lifts are flat**: a formally étale `R`-algebra over a Noetherian ring, finite over
`R_f`, is flat (étale). -/
theorem flat_of_away {R : Type u} [CommRing R] [IsNoetherianRing R] {P : Type v} [CommRing P]
    [Algebra R P] [Algebra.FormallyEtale R P] {f : R} (hfP : IsUnit (algebraMap R P f))
    (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P)) :
    Module.Flat R P := by
  haveI := finiteType_of_away hfP hP
  haveI : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Smooth R P := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.flat_of_isNoetherianRing R P

/-! ### The patched algebra -/

/-- **`PowFlat` of a patched algebra** `G = P ×_{N_f} N` (over a Noetherian chart `R` with
`wᴺ = 0`, `R` itself `PowFlat`): from the finiteness of `G`, the base change property along `V(f)`
and `PowFlat` of `N` (the étale lift `P` is flat). -/
theorem patch {R : Type u} [CommRing R] [IsNoetherianRing R] {w : R} {N : ℕ}
    (hR : PowFlat w N R) (hw : w ^ N = 0) (f : R) (J : Ideal R) {m : ℕ} (hJ : J ^ m = ⊥)
    {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
    {NN : Type u} [CommRing NN] [Algebra R NN] [Algebra (FormalPatchLevel.Hat f) NN]
    [IsScalarTower R (FormalPatchLevel.Hat f) NN]
    (α₀ : P →ₐ[R] FormalPatchLevel.Nf f NN ⧸ FormalPatchLevel.JNf f J NN)
    (hfin : Module.Finite R (FormalPatchLevel.patch f J hJ α₀))
    (hbc : IsBaseChange (FormalPatchLevel.Hat f)
      (FormalGlueing.snd NN (FormalPatchLevel.lift f J hJ α₀)).toLinearMap)
    (hfP : IsUnit (algebraMap R P f))
    (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P))
    (hN : PowFlat w N NN) : PowFlat w N (FormalPatchLevel.patch f J hJ α₀) := by
  haveI := flat_of_away hfP hP
  haveI := FormalGlueing.isLocalizedModule_fst NN (FormalPatchLevel.lift f J hJ α₀) hfP
  have hRR : PowFlat w N P := of_flat (B := R) (by simpa using hR) (by simpa using hw)
  exact of_away_of_isBaseChange f
    (FormalGlueing.fst NN (FormalPatchLevel.lift f J hJ α₀)).toLinearMap
    (FormalGlueing.snd NN (FormalPatchLevel.lift f J hJ α₀)).toLinearMap hbc hRR hN

/-- **Flat algebras over a `PowFlat` ring**, as modules over themselves. -/
theorem flat_self {A : Type u} [CommRing A] {a : A} {N : ℕ} (hA : PowFlat a N A) (ha : a ^ N = 0)
    {S : Type v} [CommRing S] [Algebra A S] [Module.Flat A S] :
    PowFlat (algebraMap A S a) N S :=
  of_addEquiv (O' := A) (ϖ' := a) (AddEquiv.refl S)
    (fun x ↦ by rw [AddEquiv.refl_apply, AddEquiv.refl_apply, smul_eq_mul, Algebra.smul_def])
    (of_flat (B := A) (by simpa using hA) (by simpa using ha))

/-! ### The factors of the lifted formal model -/

section Pieces

open AdmissibleLift KummerEtale

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {w : R} {N : ℕ}
  (hR : PowFlat w N R) (hw : w ^ N = 0) (f : R)

include hR hw in
/-- The `f`-adic completion of the chart. -/
theorem hat : PowFlat (algebraMap R (FormalPatchLevel.Hat f) w) N (FormalPatchLevel.Hat f) :=
  flat_self hR hw

include hR hw in
/-- **The lifted cusp factors** `(R̂/(1 − δ̃))[X]/(Xᵉ − t̃)`. -/
theorem cPiece {δ : FormalPatchLevel.Hat f} (hδ : IsIdempotentElem δ) (t : FormalPatchLevel.Hat f)
    {e : ℕ} (he : 0 < e) :
    PowFlat (algebraMap (FormalPatchLevel.Hat f) (CPiece f δ t e)
      (algebraMap R (FormalPatchLevel.Hat f) w)) N (CPiece f δ t e) := by
  haveI : Module.Flat (FormalPatchLevel.Hat f) (CBase f δ) :=
    FormalPatchProd.flat_quotient_one_sub hδ
  haveI : Module.Free (CBase f δ) (CPiece f δ t e) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C _ he.ne')).basis
  haveI : Module.Flat (FormalPatchLevel.Hat f) (CPiece f δ t e) :=
    Module.Flat.trans _ (CBase f δ) _
  exact flat_self (hat hR hw f) (by rw [← map_pow, hw, map_zero])

variable {O : Type u} [CommRing O] [Algebra O R] {π : O} {e : ℕ}

omit [IsNoetherianRing R] in
/-- The image of `ϖ` under `S ⊗_A B ≃ B_I ⊗_{A_I} S` (`KummerFactorQuot.equiv` and the
commutativity of `⊗`). -/
lemma kummer_image (I : Ideal O) (χ : A π e →ₐ[O] FormalPatchLevel.Hat f)
    (ε : FormalPatchLevel.Hat f)
    (g : A (KummerFactorQuot.πI I π) e →+* FormalPatchLevel.Hat f)
    (hg : g.comp (KummerFactorQuot.redA I π) = χ.toRingHom) (ϖ : O) :
    letI := LPiece.algI χ ε I g
    (Algebra.TensorProduct.comm (A (KummerFactorQuot.πI I π) e) (LPiece f χ ε)
      (B (KummerFactorQuot.πI I π)))
      (KummerFactorQuot.equiv I π (LPiece f χ ε) (LPiece.hgI χ ε I g hg)
        (algebraMap (FormalPatchLevel.Hat f) (AdmissibleLift.N f χ ε)
          (algebraMap R (FormalPatchLevel.Hat f) (algebraMap O R ϖ)))) =
      algebraMap (B (KummerFactorQuot.πI I π)) _
        (algebraMap O (B (KummerFactorQuot.πI I π)) ϖ) := by
  letI := LPiece.algI χ ε I g
  have h1 : algebraMap (FormalPatchLevel.Hat f) (LPiece f χ ε)
      (algebraMap R (FormalPatchLevel.Hat f) (algebraMap O R ϖ)) =
      algebraMap (A (KummerFactorQuot.πI I π) e) (LPiece f χ ε)
        (algebraMap (O ⧸ I) _ (Ideal.Quotient.mk I ϖ)) := by
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ (g _)
    congr 1
    rw [← Node.baseMap_algebraMap (Ideal.Quotient.mk I) (KummerFactorQuot.hpow I π),
      ← RingHom.comp_apply g, hg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  change (Algebra.TensorProduct.comm _ _ _)
    (KummerFactorQuot.equiv I π (LPiece f χ ε) (LPiece.hgI χ ε I g hg) (_ ⊗ₜ 1)) = _ ⊗ₜ 1
  rw [KummerFactorQuot.equiv_tmul, map_one, Algebra.TensorProduct.comm_tmul, h1,
    Algebra.algebraMap_eq_smul_one (A := LPiece f χ ε), ← TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply O (O ⧸ I) (B (KummerFactorQuot.πI I π)) ϖ]
  rfl

omit [IsNoetherianRing R] in
include hR hw in
/-- **The lifted Kummer factors** `(R̂/(1 − ε̃)) ⊗_A B` (node coordinates flat modulo `I`, the
reduced Kummer algebra `B_I` `PowFlat`, `ϖᴺ ∈ I`). -/
theorem kPiece (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) {ε : FormalPatchLevel.Hat f}
    (hε : IsIdempotentElem ε) {I : Ideal O} (hχ : KummerFactorQuot.KFlat I χ.toRingHom)
    {ϖ : O} (hϖ : w = algebraMap O R ϖ) (hB : PowFlat ϖ N (B (KummerFactorQuot.πI I π)))
    (hϖI : ϖ ^ N ∈ I) :
    PowFlat (algebraMap (FormalPatchLevel.Hat f) (AdmissibleLift.N f χ ε)
      (algebraMap R (FormalPatchLevel.Hat f) w)) N (AdmissibleLift.N f χ ε) := by
  obtain ⟨g, hgf, hg⟩ := hχ
  letI := LPiece.algI χ ε I g
  haveI := LPiece.flatI χ I g hgf hε
  subst hϖ
  let Φ := (KummerFactorQuot.equiv I π (LPiece f χ ε) (LPiece.hgI χ ε I g hg)).trans
    (Algebra.TensorProduct.comm (A (KummerFactorQuot.πI I π) e) (LPiece f χ ε)
      (B (KummerFactorQuot.πI I π))).toRingEquiv
  have hkill : algebraMap O (B (KummerFactorQuot.πI I π)) ϖ ^ N = 0 := by
    rw [← map_pow, IsScalarTower.algebraMap_apply O (O ⧸ I),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hϖI, map_zero]
  refine of_addEquiv Φ.toAddEquiv (fun x ↦ ?_) (flat_self (algebraMap_of hB) hkill)
  exact (Φ.map_mul _ x).trans (congrArg (· * Φ x) (kummer_image f I χ ε g hg ϖ))

omit [IsNoetherianRing R] in
/-- `PowFlat` of a factor of the lifted formal model as an `R`-module from `PowFlat` as a module
over itself. -/
lemma nf_of_self {ι κ : Type} {πs : ι → O} {es : ι → ℕ}
    (χ : ∀ j, A (πs j) (es j) →ₐ[O] FormalPatchLevel.Hat f) (ε : ι → FormalPatchLevel.Hat f)
    (δ : κ → FormalPatchLevel.Hat f) (t : FormalPatchLevel.Hat f) (ce : κ → ℕ) (s : ι ⊕ κ)
    (h : PowFlat (algebraMap (FormalPatchLevel.Hat f) (NFr χ ε δ t ce s)
      (algebraMap R (FormalPatchLevel.Hat f) w)) N (NFr χ ε δ t ce s)) :
    PowFlat w N (NFr χ ε δ t ce s) :=
  of_addEquiv (O' := NFr χ ε δ t ce s) (AddEquiv.refl _)
    (fun x ↦ (Algebra.smul_def (algebraMap R (FormalPatchLevel.Hat f) w) x :)) h

end Pieces

section Level

open AdmissibleLift KummerEtale LevelTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}

/-- **`PowFlat` of the patched algebra at level `n`**: from `PowFlat` of the chart `R n` (killed
by `ϖᴺ`) and of the reduced Kummer algebras `B_I = (O/I)[s,t]/(st − π̄_j)` (`ϖᴺ ∈ I`). -/
theorem level (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ}
    (D : Level R cov₀ πL hfe n) {ϖ : O} {N : ℕ} (hR : PowFlat ϖ N (R n))
    (hw : algebraMap O (R n) ϖ ^ N = 0)
    (hB : ∀ j, PowFlat ϖ N (B (KummerFactorQuot.πI D.I (πL j)))) (hϖI : ϖ ^ N ∈ D.I) :
    PowFlat (algebraMap O (R n) ϖ) N (D.G hθ) := by
  have hR' : PowFlat (algebraMap O (R n) ϖ) N (R n) := algebraMap_of hR
  have hN : PowFlat (algebraMap O (R n) ϖ) N (NFall D.L D.M) := by
    refine pi fun s ↦ nf_of_self (f n) _ _ _ _ _ s ?_
    rcases s with j | i
    · exact kPiece hR' hw (f n) (D.L.χ j) (D.hidem j) (D.hflat j) rfl (hB j) hϖI
    · exact cPiece hR' hw (f n) (D.hcidem i) D.M.t (cov₀.ce_pos i)
  exact patch hR' hw (f n) (J θ) D.hJ _ (Level.spec hθ hO D).1 (Level.spec hθ hO D).2.2 D.hfP
    D.hP hN

variable [∀ n, Algebra (R (n + 1)) (R n)]

/-- **`PowFlat` of the patched algebras of a tower** (`LevelTower.Data`). -/
theorem data (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
    (T : Data (θ := θ) R cov₀ πL) (n : ℕ) {ϖ : O} {N : ℕ} (hR : PowFlat ϖ N (R n))
    (hw : algebraMap O (R n) ϖ ^ N = 0)
    (hB : ∀ j, PowFlat ϖ N (B (KummerFactorQuot.πI (T.I n) (πL j)))) (hϖI : ϖ ^ N ∈ T.I n) :
    PowFlat (algebraMap O (R n) ϖ) N (T.G hθ n) :=
  level hθ hO (T.level n) hR hw hB hϖI

/-- **`PowFlat` of the patched algebras of a tower over a domain** with `I n = (ϖᴺ)` and nonzero
deformation parameters. -/
theorem data_of_isDomain [IsDomain O] (hθ : Function.Surjective θ)
    (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (T : Data (θ := θ) R cov₀ πL) (hπ : ∀ j, πL j ≠ 0)
    (n : ℕ) {ϖ : O} (hϖ : ϖ ≠ 0) {N : ℕ} (hR : PowFlat ϖ N (R n))
    (hw : algebraMap O (R n) ϖ ^ N = 0) (hI : T.I n = Ideal.span {ϖ ^ N}) :
    PowFlat (algebraMap O (R n) ϖ) N (T.G hθ n) :=
  data hθ hO T n hR hw (fun j ↦ node (hπ j) hϖ (T.I n) hI)
    (hI ▸ Ideal.mem_span_singleton_self _)

end Level

end PowFlat

end SemistableReduction
