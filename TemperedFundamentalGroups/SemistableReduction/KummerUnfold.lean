/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalLevelNode

/-!
# Element formulas for the special-fibre formal Kummer forms (MR12 T2 S6, step G2)

The special-fibre formal Kummer forms `FormalKummer.nodeEquivOf` (at a node `𝔪`) and
`FormalKummer.kummerEquivOf` (along all nodes of a chart) are built from the chosen splitting
`D.Φ : N₁ ⊗_R B ≅ ∏ᵢ N₁ ⊗_{O[u,v]/(uv − ϖⁿ)} O[s,t]/(st − ϖ^{mᵢ})` by reduction modulo `J`,
base change along `N̄₁ → R̂_𝔪` and assembly. We unfold these constructions on pure tensors
`1 ⊗ b̄`: in every case the result is the reduction `FormalLevel.redTensorMap g` of `D.Φ (1 ⊗ b)`
(`n ⊗ b' ↦ g n ⊗ b̄'`) along an explicit ring map `g` out of `N₁`.

* **`FormalKummer.baseChangeEquiv_one_tmul`**: `baseChangeEquiv g Φ (1 ⊗ c)ᵢ` is the image of
  `Φ (1 ⊗ c)ᵢ` under `g ⊗ id` (`homA`);
* **`FormalKummer.splitEquiv_mk`**, **`FormalKummer.redSplitEquiv_mk_tmul`**: the reduced
  splittings are `redTensorMap` along `N₁ → N₁/J`;
* **`FormalKummer.nodeEquivOf_one_tmul`**: `nodeEquivOf (1 ⊗ b̄)ᵢ = redTensorMap g₀ (D.Φ (1 ⊗ b)ᵢ)`
  for `g₀ = hatOf : N₁ → N̄₁ → R̂_𝔪` (`toHatOf` is the map `toHat` used inside `nodeEquivOf`);
* **`FormalKummer.hatOfₐ_eq_hatLift`**: `g₀` is the canonical lift `FormalLevel.hatLift` of the
  residue map `N₁ → N₁/𝔫 ≅ R/𝔪 → R̄/𝔪̄` (`resOf`), so it is characterised by its residue map and
  the special-fibre Kummer form is comparable with the level forms `FormalLevel.nodeEquiv`;
* **`FormalKummer.kummerEquivOf_one_tmul`**: the `(j, i)`-th component of `kummerEquivOf (1 ⊗ b̄)`
  is `redTensorMap gⱼ ((D j).Φ (1 ⊗ b)ᵢ)` for `gⱼ = pieceOf`, `hatOf` followed by
  `R̂_{𝔪ⱼ} ≅ R̂/(1 − εⱼ)` (`pieceEquiv`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

namespace FormalKummer

noncomputable section

section BaseChange

variable {R N T C : Type u} [CommRing R] [CommRing N] [CommRing T] [CommRing C]
  [Algebra R N] [Algebra R T] [Algebra R C] (g : N →ₐ[R] T)
  {ι : Type} [Fintype ι] [DecidableEq ι] {A Bk : ι → Type u} [∀ i, CommRing (A i)]
  [∀ i, CommRing (Bk i)] [∀ i, Algebra (A i) (Bk i)] [∀ i, Algebra (A i) N]
  [∀ i, Algebra (A i) T] (α : ∀ i, A i →+* R)
  (hN : ∀ i a, algebraMap (A i) N a = algebraMap R N (α i a))
  (hT : ∀ i a, algebraMap (A i) T a = algebraMap R T (α i a))

omit [Fintype ι] [DecidableEq ι] in
/-- `g : N → T` as an `Aᵢ`-algebra map. -/
def homA (i : ι) : N →ₐ[A i] T :=
  { g.toRingHom with
    commutes' := fun a ↦ by
      change g (algebraMap (A i) N a) = _
      rw [hN, hT, g.commutes] }

omit [Fintype ι] [DecidableEq ι] in
lemma homA_apply (i : ι) (z : N) : homA g α hN hT i z = g z := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma cancelBaseChange_one_tmul (i : ι) (z : N ⊗[A i] Bk i) :
    letI := algNT g
    haveI := isScalarTower_A g α hN hT i
    Algebra.TensorProduct.cancelBaseChange (A i) N T T (Bk i) ((1 : T) ⊗ₜ z) =
      Algebra.TensorProduct.map (homA g α hN hT i) (AlgHom.id (A i) (Bk i)) z := by
  letI := algNT g
  haveI := isScalarTower_A g α hN hT i
  induction z using TensorProduct.induction_on with
  | zero => rw [tmul_zero, map_zero, map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

/-- **`baseChangeEquiv` on pure tensors `1 ⊗ c`**: the image of `Φ (1 ⊗ c)` under
`N ⊗_{Aᵢ} Bᵢ → T ⊗_{Aᵢ} Bᵢ` (induced by `g`). -/
theorem baseChangeEquiv_one_tmul (Φ : N ⊗[R] C ≃ₐ[N] ∀ i, N ⊗[A i] Bk i) (c : C) (i : ι) :
    baseChangeEquiv g α hN hT Φ ((1 : T) ⊗ₜ c) i =
      Algebra.TensorProduct.map (homA g α hN hT i) (AlgHom.id (A i) (Bk i))
        (Φ ((1 : N) ⊗ₜ c) i) := by
  letI := algNT g
  haveI : IsScalarTower R N T := IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  haveI := isScalarTower_A g α hN hT
  rw [← cancelBaseChange_one_tmul]
  simp only [baseChangeEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply,
    Algebra.TensorProduct.piRight_tmul, AlgEquiv.piCongrRight_apply]
  rfl

end BaseChange

section Red

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k) {c : O} {d : ℕ}
  (hc : θ c = 0) {N : Type u} [CommRing N] [Algebra (A c d) N]
  {T T' : Type u} [CommRing T] [Algebra (A (0 : k) d) T] [CommRing T']
  [Algebra (A (0 : k) d) T']

/-- Composing the reduction `redTensorMap g` with `ψ ⊗ id` gives `redTensorMap (ψ ∘ g)`. -/
lemma map_redTensorMap (ψ : T →ₐ[A (0 : k) d] T') (g : N →+* T)
    (hg : ∀ a, g (algebraMap (A c d) N a) =
      algebraMap (A (0 : k) d) T (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc) a))
    (hg' : ∀ a, ((ψ : T →+* T').comp g) (algebraMap (A c d) N a) =
      algebraMap (A (0 : k) d) T' (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc) a))
    (z : N ⊗[A c d] KNode c d) :
    Algebra.TensorProduct.map ψ (AlgHom.id (A (0 : k) d) (B (0 : k)))
        (FormalLevel.redTensorMap θ hc g hg z) =
      FormalLevel.redTensorMap θ hc ((ψ : T →+* T').comp g) hg' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul n b =>
    rw [FormalLevel.redTensorMap_tmul, FormalLevel.redTensorMap_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end Red

section Split

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)]
  {N₁ : Type u} [CommRing N₁] [Algebra O N₁] {u₁ v₁ : N₁} {ϖ : O} {n : ℕ}
  {X : Type u} [CommRing X] [Algebra N₁ X] {r : ℕ} {m d : Fin r → ℕ}
  (huv : u₁ * v₁ = algebraMap O N₁ (ϖ ^ n)) (hmd : ∀ i, m i * d i = n)
  (hc : ∀ i, θ (ϖ ^ m i) = 0)

/-- **`factorEquiv` is the reduction `redTensorMap` along `N₁ → N₁/J`.** -/
lemma factorEquiv_mk {c : O} {d : ℕ} (h : u₁ * v₁ = algebraMap O N₁ (c ^ d)) (hc : θ c = 0)
    (z : letI := nodeAlgebra N₁ c d h; KummerNodeFactor (c := c) (d := d) N₁) :
    letI := nodeAlgebra N₁ c d h
    letI := barAlg h hc
    factorEquiv h hc (Ideal.Quotient.mk _ z) =
      FormalLevel.redTensorMap θ hc (Ideal.Quotient.mk (J θ (R := N₁))) (mk_lift h hc) z := by
  letI := nodeAlgebra N₁ c d h
  letI := barAlg h hc
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rw [factorEquiv_mk_tmul, FormalLevel.redTensorMap_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- **`splitEquiv` on classes**: the `i`-th component of the reduced splitting of `x̄` is the
reduction `redTensorMap` (along `N₁ → N₁/J`) of `Φ x`. -/
theorem splitEquiv_mk (Φ : X ≃ₐ[N₁] ∀ i, KFac huv hmd i) (x : X) (i : Fin r) :
    letI := nodeAlgebra N₁ (ϖ ^ m i) (d i) (huv_i huv hmd i)
    letI := barAlg (huv_i huv hmd i) (hc i)
    splitEquiv huv hmd hc Φ (Ideal.Quotient.mk _ x) i =
      FormalLevel.redTensorMap θ (hc i) (Ideal.Quotient.mk (J θ (R := N₁)))
        (mk_lift (huv_i huv hmd i) (hc i)) (Φ x i) := by
  change factorEquiv (huv_i huv hmd i) (hc i) (Ideal.quotEquivOfEq
    (KT_eq (huv_i huv hmd i)).symm
    (Ideal.Quotient.mk ((J θ (R := N₁)).map (algebraMap N₁ (KFac huv hmd i))) (Φ x i))) = _
  rw [Ideal.quotEquivOfEq_mk, factorEquiv_mk]

end Split

section RedSplit

attribute [local instance] algRN

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]
  {N₁ : Type u} [CommRing N₁] [Algebra R N₁] [Algebra O N₁] [IsScalarTower O R N₁]
  {x y : R} {ϖ : O} {n r : ℕ} {m d : Fin r → ℕ}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) (hmd : ∀ i, m i * d i = n)
  (hc : ∀ i, θ (ϖ ^ m i) = 0)

/-- **The reduced splitting on pure tensors `ā ⊗ b̄`**: the reduction of `Φ (a ⊗ b)`. -/
theorem redSplitEquiv_mk_tmul
    (Φ : N₁ ⊗[R] B ≃ₐ[N₁] ∀ i, KFac (huvN (N₁ := N₁) hxy) hmd i) (a : N₁) (b : B)
    (i : Fin r) :
    letI := nodeAlgebra N₁ (ϖ ^ m i) (d i) (huv_i (huvN (N₁ := N₁) hxy) hmd i)
    letI := barAlg (huv_i (huvN (N₁ := N₁) hxy) hmd i) (hc i)
    redSplitEquiv hxy hmd hc Φ
        ((Ideal.Quotient.mk _ a : Ns θ N₁) ⊗ₜ (Ideal.Quotient.mk _ b : Cs θ R B)) i =
      FormalLevel.redTensorMap θ (hc i) (Ideal.Quotient.mk (J θ (R := N₁)))
        (mk_lift _ (hc i)) (Φ (a ⊗ₜ b) i) := by
  have h1 : (tensorQuot (θ := θ)).symm
      ((Ideal.Quotient.mk _ a : Ns θ N₁) ⊗ₜ (Ideal.Quotient.mk _ b : Cs θ R B)) =
        Ideal.Quotient.mk _ (a ⊗ₜ b) := by
    rw [RingEquiv.symm_apply_eq, tensorQuot_mk_tmul]
  simp only [redSplitEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, h1,
    Ideal.quotEquivOfEq_mk]
  exact splitEquiv_mk _ hmd hc Φ _ i

end RedSplit

section NodeOf

attribute [local instance] algRN

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]

/-- The `O`-algebra structure of the étale neighbourhood of `KummerNormAtData` (through `R`). -/
abbrev KummerNormAtData.algO {ϖ : O} {n M' : ℕ} {x y : R} {𝔪 : Ideal R}
    (D : KummerNormAtData ϖ n M' x y B 𝔪) : Algebra O D.N₁ :=
  ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra

attribute [local instance] KummerNormAtData.algO

instance KummerNormAtData.isScalarTower_algO {ϖ : O} {n M' : ℕ} {x y : R} {𝔪 : Ideal R}
    (D : KummerNormAtData ϖ n M' x y B 𝔪) : IsScalarTower O R D.N₁ :=
  IsScalarTower.of_algebraMap_eq' rfl

variable [IsSepClosed k] {ϖ : O} {n M' : ℕ} {x y : R}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
  (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
  (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
  (D : KummerNormAtData ϖ n M' x y B 𝔪)

omit hθ [IsSepClosed k] in
include hϖ hn0 in
lemma hn_of : θ (ϖ ^ n) = 0 := by rw [map_pow, hϖ, zero_pow hn0.ne']

omit hθ [IsSepClosed k] [𝔪.IsMaximal] in
include hϖ hn0 in
lemma hc_of (i : Fin D.r) : θ (ϖ ^ D.m i) = 0 := by
  have : 0 < D.m i := Nat.pos_of_ne_zero fun h0 ↦ hn0.ne' (by
    rw [← D.hmd i]; exact (congrArg (· * D.d i) h0).trans (zero_mul _))
  rw [map_pow, hϖ, zero_pow this.ne']

omit hθ [IsSepClosed k] [𝔪.IsMaximal] in
include hJ in
lemma hcomap_of : (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁)))).comap
    (algebraMap (Rs θ R) (Ns θ D.N₁)) = sIdeal (θ := θ) 𝔪 := by
  have hJ𝔫 : J θ (R := D.N₁) ≤ D.𝔫 := by
    rw [← J_N₁_eq θ R D.N₁, Ideal.map_le_iff_le_comap, D.comap_eq]
    exact hJ
  ext z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.mem_comap, algebraMap_RN, Ideal.mem_quotient_iff_mem hJ𝔫,
    Ideal.mem_quotient_iff_mem hJ, ← Ideal.mem_comap, D.comap_eq]

include hJ hres in
/-- The residue field extension of the étale neighbourhood is trivial (`k` separably closed). -/
lemma hsurj0_of : Function.Surjective ((Ideal.Quotient.mk D.𝔫).comp (algebraMap R D.N₁)) := by
  have hρ : Function.Surjective ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R))) := by
    intro z
    obtain ⟨o, ho⟩ := hres z
    refine ⟨θ o, ?_⟩
    rw [RingHom.comp_apply, QuadNodeTower.algK_θ, Ideal.Quotient.factor_mk]
    exact ho
  exact EtaleResidue.surjective_of_isSepClosed' 𝔪 D.𝔫 D.comap_eq
    ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R))) hρ

include hJ hres in
lemma hsurj_of : Function.Surjective
    ((Ideal.Quotient.mk (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁))))).comp
      (algebraMap (Rs θ R) (Ns θ D.N₁))) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := hsurj0_of 𝔪 hJ hres D (Ideal.Quotient.mk D.𝔫 z)
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  simp only [RingHom.comp_apply] at ha ⊢
  rw [Ideal.Quotient.eq] at ha ⊢
  rw [algebraMap_RN, ← map_sub]
  exact Ideal.mem_map_of_mem _ ha

/-- **The map `N̄₁ → R̂_𝔪` used in `nodeEquivOf`** (`toHat` for the chosen data `D`). -/
def toHatOf : Ns θ D.N₁ →ₐ[Rs θ R] Tn θ 𝔪 :=
  toHat (sIdeal 𝔪) _ (hcomap_of 𝔪 hJ D) (hsurj_of 𝔪 hJ hres D)

/-- `nodeEquivOf` is `nodeEquiv` along `toHatOf`. -/
lemma nodeEquivOf_eq :
    nodeEquivOf hxy hϖ hn0 𝔪 hJ hres D =
      nodeEquiv hxy D.hmd (hc_of hϖ hn0 𝔪 D) D.hd (hn_of hϖ hn0) (sIdeal 𝔪) _
        (hcomap_of 𝔪 hJ D) (hsurj_of 𝔪 hJ hres D) D.Φ :=
  rfl

/-- **The map `g₀ : N₁ → N̄₁ → R̂_𝔪`** through which `nodeEquivOf` is the base change of `D.Φ`. -/
def hatOf : D.N₁ →+* Tn θ 𝔪 :=
  (toHatOf 𝔪 hJ hres D).toRingHom.comp (Ideal.Quotient.mk (J θ (R := D.N₁)))

lemma hatOf_apply (z : D.N₁) :
    hatOf 𝔪 hJ hres D z = toHatOf 𝔪 hJ hres D (Ideal.Quotient.mk _ z) := rfl

/-- `g₀` is compatible with the node rings (`u, v ↦ x, y`). -/
lemma hatOf_node (i : Fin D.r) (a : A (ϖ ^ D.m i) (D.d i)) :
    letI := nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)
    letI := chartAlg (k := k) (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) (D.hd i) (Tn θ 𝔪)
    hatOf 𝔪 hJ hres D (algebraMap (A (ϖ ^ D.m i) (D.d i)) D.N₁ a) =
      algebraMap (A (0 : k) (D.d i)) (Tn θ 𝔪)
        (Node.baseMap θ (FormalKummer.θ_pow (d := D.d i) (hc_of hϖ hn0 𝔪 D i)) a) := by
  rw [hatOf_apply]
  refine (congrArg (toHatOf 𝔪 hJ hres D)
    ((mk_lift (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i) (hc_of hϖ hn0 𝔪 D i) a).trans
      (barAlg_eq hxy D.hmd (hc_of hϖ hn0 𝔪 D) D.hd (hn_of hϖ hn0) i _))).trans ?_
  rw [AlgHom.commutes]
  rfl

/-- **The special-fibre Kummer form at a node on `1 ⊗ b̄`**: the reduction of `D.Φ (1 ⊗ b)` along
`g₀ = hatOf : N₁ → R̂_𝔪`. -/
theorem nodeEquivOf_one_tmul (b : B) (i : Fin D.r) :
    letI := nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)
    letI : ∀ i, Algebra (A (0 : k) (D.d i)) (Tn θ 𝔪) := fun i ↦
      chartAlg (k := k) (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) (D.hd i) (Tn θ 𝔪)
    nodeEquivOf hxy hϖ hn0 𝔪 hJ hres D ((1 : Tn θ 𝔪) ⊗ₜ Ideal.Quotient.mk _ b) i =
      FormalLevel.redTensorMap θ (hc_of hϖ hn0 𝔪 D i) (hatOf 𝔪 hJ hres D)
        (hatOf_node hxy hϖ hn0 𝔪 hJ hres D i) (D.Φ ((1 : D.N₁) ⊗ₜ b) i) := by
  letI : ∀ i, Algebra (A (0 : k) (D.d i)) (Tn θ 𝔪) := fun i ↦
    chartAlg (k := k) (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) (D.hd i) (Tn θ 𝔪)
  letI : ∀ i, Algebra (A (0 : k) (D.d i)) (Ns θ D.N₁) := fun i ↦
    barAlg (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i) (hc_of hϖ hn0 𝔪 D i)
  rw [nodeEquivOf_eq, nodeEquiv, baseChangeEquiv_one_tmul,
    ← map_one (Ideal.Quotient.mk (J θ (R := D.N₁))), redSplitEquiv_mk_tmul, map_redTensorMap]
  rfl

omit hθ [IsSepClosed k] [𝔪.IsMaximal] in
lemma le_comap_sIdeal : 𝔪 ≤ (sIdeal (θ := θ) 𝔪).comap (algebraMap R (Rs θ R)) :=
  fun _ ha ↦ Ideal.mem_map_of_mem _ ha

/-- `g₀ = hatOf` as an `R`-algebra map `N₁ → R̂_𝔪`. -/
def hatOfₐ : D.N₁ →ₐ[R] Tn θ 𝔪 :=
  { hatOf 𝔪 hJ hres D with
    commutes' := fun a ↦ by
      change toHatOf 𝔪 hJ hres D (algebraMap (Rs θ R) (Ns θ D.N₁) (Ideal.Quotient.mk _ a)) = _
      rw [AlgHom.commutes]
      rfl }

/-- The residue map `N₁ → N₁/𝔫 ≅ R/𝔪 → R̄/𝔪̄` at the chosen point `𝔫` of `D`. -/
def resOf : D.N₁ →ₐ[R] Rs θ R ⧸ sIdeal (θ := θ) 𝔪 :=
  FormalLevel.resMap D.comap_eq (hsurj0_of 𝔪 hJ hres D) (le_comap_sIdeal 𝔪)

lemma resHat_toHat_eq_zero {w : D.N₁} (hw : w ∈ D.𝔫) :
    FormalLevel.resHat (sIdeal (θ := θ) 𝔪) (toHatOf 𝔪 hJ hres D (Ideal.Quotient.mk _ w)) = 0 := by
  haveI := formallyEtale_Ns (θ := θ) (R := R) (N₁ := D.N₁)
  set E := CompletionEtale.equiv (sIdeal (θ := θ) 𝔪) _ (hcomap_of 𝔪 hJ D) (hsurj_of 𝔪 hJ hres D)
  have hE : ∀ Y, E.symm Y = CompletionEtale.inv _ _ (hcomap_of 𝔪 hJ D)
      (hsurj_of 𝔪 hJ hres D) Y := fun Y ↦ by
    rw [RingEquiv.symm_apply_eq]
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    rw [CompletionEtale.equiv_apply, CompletionMap.evalₐ_map,
      ← CompletionEtale.quotPowEquiv_apply (hcomap_of 𝔪 hJ D) (hsurj_of 𝔪 hJ hres D),
      CompletionEtale.evalₐ_inv, AlgEquiv.apply_symm_apply]
  have h1 : toHatOf 𝔪 hJ hres D (Ideal.Quotient.mk _ w) = E.symm (algebraMap (Ns θ D.N₁)
      (AdicCompletion (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁)))) (Ns θ D.N₁))
      (Ideal.Quotient.mk _ w)) := rfl
  have hw' : (Ideal.Quotient.mk (J θ (R := D.N₁)) w) ∈
      (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁)))) ^ 1 := by
    rw [pow_one]; exact Ideal.mem_map_of_mem _ hw
  rw [h1, hE, FormalLevel.resHat, AlgHom.comp_apply, CompletionEtale.evalₐ_inv,
    AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, Algebra.algebraMap_self,
    RingHom.id_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hw', map_zero, map_zero]

/-- **`g₀` is the canonical lift `FormalLevel.hatLift` of the residue map at `𝔫`**: this makes
the special-fibre Kummer form comparable with the level Kummer forms `FormalLevel.nodeEquiv`. -/
theorem hatOfₐ_eq_hatLift :
    hatOfₐ 𝔪 hJ hres D = FormalLevel.hatLift (resOf 𝔪 hJ hres D) := by
  refine FormalLevel.hatLift_unique _ _ fun z ↦ ?_
  obtain ⟨a, ha⟩ := hsurj0_of 𝔪 hJ hres D (Ideal.Quotient.mk D.𝔫 z)
  rw [RingHom.comp_apply, Ideal.Quotient.eq] at ha
  obtain ⟨w, hw, rfl⟩ : ∃ w ∈ D.𝔫, z = algebraMap R D.N₁ a - w := ⟨_, ha, by ring⟩
  have h2 : FormalLevel.resHat (sIdeal (θ := θ) 𝔪) (hatOfₐ 𝔪 hJ hres D (algebraMap R D.N₁ a)) =
      resOf 𝔪 hJ hres D (algebraMap R D.N₁ a) := by
    rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply R (Rs θ R),
      AlgHom.commutes]
    rfl
  have h3 : resOf 𝔪 hJ hres D w = 0 := FormalLevel.resMap_eq_zero _ _ _ hw
  have h4 : FormalLevel.resHat (sIdeal (θ := θ) 𝔪) (hatOfₐ 𝔪 hJ hres D w) = 0 :=
    resHat_toHat_eq_zero 𝔪 hJ hres D hw
  rw [map_sub, map_sub, map_sub, h2, h3, h4]

end NodeOf

section Assemble

attribute [local instance] algRN KummerNormAtData.algO

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]
  [IsSepClosed k] [IsNoetherianRing R] {ϖ : O} {n M' : ℕ} {x y : R}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
  {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
  (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
  (hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
  (D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j)) {f : Rs θ R}
  (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
  (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
  (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
  (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
  (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
  (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y))

/-- **The map `gⱼ : N₁ → R̂/(1 − εⱼ)`** of the `(j, i)`-th Kummer piece of `kummerEquivOf`:
`hatOf` followed by `R̂_{𝔪ⱼ} ≅ R̂/(1 − εⱼ)` (`pieceEquiv`). -/
def pieceOf (j : ι) (i : Fin (D j).r) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    (D j).N₁ →+* Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D j).hd i) :=
  haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  letI := chartAlg (k := k) (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) ((D j).hd i) (Tn θ (𝔪 j))
  (pieceEquiv hinj hf hrad (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) φ hφu hφv
    (fun j ↦ (D j).hd) j i).toAlgHom.toRingHom.comp (hatOf (𝔪 j) (hJ j) (hres j) (D j))

/-- `gⱼ` is compatible with the node rings. -/
lemma pieceOf_node (j : ι) (i : Fin (D j).r) (a : A (ϖ ^ (D j).m i) ((D j).d i)) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    letI := nodeAlgebra (D j).N₁ (ϖ ^ (D j).m i) ((D j).d i)
      (huv_i (huvN (N₁ := (D j).N₁) hxy) (D j).hmd i)
    pieceOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j i
        (algebraMap (A (ϖ ^ (D j).m i) ((D j).d i)) (D j).N₁ a) =
      algebraMap (A (0 : k) ((D j).d i))
        (Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D j).hd i))
        (Node.baseMap θ (FormalKummer.θ_pow (d := (D j).d i) (hc_of hϖ hn0 (𝔪 j) (D j) i)) a) := by
  haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  letI := chartAlg (k := k) (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) ((D j).hd i) (Tn θ (𝔪 j))
  rw [pieceOf, RingHom.comp_apply, hatOf_node hxy hϖ hn0 (𝔪 j) (hJ j) (hres j) (D j) i]
  exact (pieceEquiv hinj hf hrad (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) φ hφu hφv
    (fun j ↦ (D j).hd) j i).commutes _

/-- **The special-fibre Kummer form of a chart on `1 ⊗ b̄`**: its `(j, i)`-th component is the
reduction of `(D j).Φ (1 ⊗ b)` along `gⱼ = pieceOf : N₁ → R̂/(1 − εⱼ)`. -/
theorem kummerEquivOf_one_tmul (b : B) (j : ι) (i : Fin (D j).r) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    letI := nodeAlgebra (D j).N₁ (ϖ ^ (D j).m i) ((D j).d i)
      (huv_i (huvN (N₁ := (D j).N₁) hxy) (D j).hmd i)
    kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv
        ((1 : Admissible.Hat f) ⊗ₜ Ideal.Quotient.mk _ b) ⟨j, i⟩ =
      FormalLevel.redTensorMap θ (hc_of hϖ hn0 (𝔪 j) (D j) i)
        (pieceOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j i)
        (pieceOf_node hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j i)
        ((D j).Φ ((1 : (D j).N₁) ⊗ₜ b) i) := by
  haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  letI : ∀ i, Algebra (A (0 : k) ((D j).d i)) (Tn θ (𝔪 j)) := fun i ↦
    chartAlg (k := k) (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) ((D j).hd i) (Tn θ (𝔪 j))
  change (Algebra.TensorProduct.congr (pieceEquiv hinj hf hrad
      (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) φ hφu hφv (fun j ↦ (D j).hd) j i) AlgEquiv.refl)
    (nodeEquivOf hxy hϖ hn0 (𝔪 j) (hJ j) (hres j) (D j)
      (hatEquiv hinj hf hrad 1 j ⊗ₜ Ideal.Quotient.mk _ b) i) = _
  rw [map_one, Pi.one_apply, nodeEquivOf_one_tmul, Algebra.TensorProduct.congr_apply,
    AlgEquiv.refl_toAlgHom, map_redTensorMap]
  rfl

end Assemble

end

end FormalKummer

end SemistableReduction
