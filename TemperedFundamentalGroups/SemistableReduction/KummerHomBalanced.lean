/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerUnfold
import TemperedFundamentalGroups.SemistableReduction.KummerNodeTwist

/-!
# Maps of covers induce balanced maps of formal Kummer forms (MR12 I5(b), generic)

Let `R` be a chart over `O` with node coordinates `x y = ϖⁿ`, `B`, `B'` two `R`-algebras (the
normalisations of the chart in two covers) with chosen Kummer data `D`, `D'` at the nodes
`𝔪ⱼ` (`KummerNormAtData`), and `g : B → B'` an `R`-algebra map. The special-fibre formal Kummer
forms `kummerEquivOf` of `B` and `B'` turn the reduction of `g` into a map of Kummer pieces
(**`FormalKummer.kummerHom`**). We show that it is balanced on every piece
(**`FormalKummer.exists_kummerHom_twist`**): on the piece `(j, i)` (degree `d`) and a target
piece `(j, i')` (degree `d'`, `d ∣ d'`)

  `s ↦ Φ(1) ζ s'^{d'/d}`,  `t ↦ Φ(1) ζ^{d − 1} t'^{d'/d}`,  `ζ^d = 1`,

and pieces at different nodes do not interact (`kummerHom_single_one_ne`).

Proof. Over the common étale neighbourhood `N₂ = N₁' ⊗_R N₁` of the node, the splittings `D.Φ`,
`D'.Φ` base change to splittings of `N₂ ⊗ B`, `N₂ ⊗ B'` (`baseChangeEquiv`), and `g` becomes a map
`Ψ₂` of products of Kummer node factors. Its components are balanced before reduction
(`KummerNodeFactor.exists_twist`: `w₀ z₀ = ϖ^{n/d} = (w z)^{d'/d}`, normality of the Kummer node
factors), and the reduction of `Ψ₂` along `N₂ → R̂/(1 − εⱼ)` is `kummerHom` on the pieces at the
node `j` (`kummerEquivOf_one_tmul`, `baseChangeEquiv_one_tmul`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

namespace FormalKummer

noncomputable section

/-! ### Reductions of algebra maps -/

section Cs

variable {R : Type u} [CommRing R] (I : Ideal R) {B B' : Type u} [CommRing B] [CommRing B']
  [Algebra R B] [Algebra R B']

/-- The reduction `B/IB → B'/IB'` of an `R`-algebra map. -/
def quotHom (g : B →ₐ[R] B') :
    (B ⧸ I.map (algebraMap R B)) →ₐ[R ⧸ I] (B' ⧸ I.map (algebraMap R B')) where
  toRingHom := Ideal.quotientMap _ (g : B →+* B') (by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.coe_coe, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hr)
  commutes' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.quotientMap _ (g : B →+* B') _ (algebraMap (R ⧸ I) (B ⧸ I.map (algebraMap R B))
      (Ideal.Quotient.mk I x)) = _
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.quotientMap_mk, RingHom.coe_coe,
      AlgHom.commutes]

@[simp]
lemma quotHom_mk (g : B →ₐ[R] B') (b : B) :
    quotHom I g (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (g b) := rfl

end Cs

/-! ### The base changed splittings over a ring receiving the étale neighbourhood -/

section Side

attribute [local instance] algRN KummerNormAtData.algO

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] {ϖ : O} {n M' : ℕ} {x y : R}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) {𝔪 : Ideal R} (D : KummerNormAtData ϖ n M' x y B 𝔪)
  {N₂ : Type u} [CommRing N₂] [Algebra R N₂] (ι : D.N₁ →ₐ[R] N₂)

/-- The node map `O[u,v]/(uv − ϖⁿ) → R`. -/
abbrev nodeR (i : Fin D.r) : A (ϖ ^ D.m i) (D.d i) →ₐ[O] R :=
  Node.lift x y (by rw [← pow_mul, D.hmd i]; exact hxy)

/-- The node structure of the étale neighbourhood is the node map of the chart. -/
lemma algebraMap_node (i : Fin D.r) (a : A (ϖ ^ D.m i) (D.d i)) :
    letI := nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)
    algebraMap (A (ϖ ^ D.m i) (D.d i)) D.N₁ a = algebraMap R D.N₁ (nodeR hxy D i a) := by
  letI := nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)
  have h : Node.lift (algebraMap R D.N₁ x) (algebraMap R D.N₁ y)
      (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i) =
      (IsScalarTower.toAlgHom O R D.N₁).comp (nodeR hxy D i) :=
    Node.algHom_ext (by simp) (by simp)
  exact DFunLike.congr_fun h a

/-- The node structures of `N₂` (through `ι`). -/
abbrev algOf (i : Fin D.r) : Algebra (A (ϖ ^ D.m i) (D.d i)) N₂ :=
  (ι.toRingHom.comp (@algebraMap _ _ _ _
    (nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)))).toAlgebra

/-- **The splitting `D.Φ` base changed to `N₂`.** -/
def split₂ :
    letI := fun i ↦ algOf hxy D ι i
    N₂ ⊗[R] B ≃ₐ[N₂] ∀ i, N₂ ⊗[A (ϖ ^ D.m i) (D.d i)] KNode (ϖ ^ D.m i) (D.d i) :=
  letI := fun i ↦ algOf hxy D ι i
  letI := fun i ↦ nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)
  baseChangeEquiv ι (fun i ↦ (nodeR hxy D i).toRingHom) (algebraMap_node hxy D)
    (fun i a ↦ (congrArg ι (algebraMap_node hxy D i a)).trans (ι.commutes _)) D.Φ

lemma split₂_one_tmul (b : B) (i : Fin D.r) :
    letI := fun i ↦ algOf hxy D ι i
    letI := fun i ↦ nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)
    split₂ hxy D ι ((1 : N₂) ⊗ₜ b) i =
      Algebra.TensorProduct.map
        (homA ι (fun i ↦ (nodeR hxy D i).toRingHom) (algebraMap_node hxy D)
          (fun i a ↦ (congrArg ι (algebraMap_node hxy D i a)).trans (ι.commutes _)) i)
        (AlgHom.id _ _) (D.Φ ((1 : D.N₁) ⊗ₜ b) i) := by
  letI := fun i ↦ algOf hxy D ι i
  letI := fun i ↦ nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)
  exact baseChangeEquiv_one_tmul _ _ _ _ _ _ _

lemma algOf_u (i : Fin D.r) :
    letI := algOf hxy D ι i
    algebraMap (A (ϖ ^ D.m i) (D.d i)) N₂ (Node.u _) = algebraMap R N₂ x := by
  change ι (@algebraMap _ _ _ _
    (nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)) _) = _
  rw [algebraMap_node hxy D i, Node.lift_u, ι.commutes]

lemma algOf_O (i : Fin D.r) (o : O) :
    letI := algOf hxy D ι i
    algebraMap (A (ϖ ^ D.m i) (D.d i)) N₂ (algebraMap O _ o) =
      algebraMap R N₂ (algebraMap O R o) := by
  change ι (@algebraMap _ _ _ _
    (nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)) _) = _
  rw [algebraMap_node hxy D i, AlgHom.commutes, AlgHom.commutes]

lemma one_tmul_algebraMap {N : Type u} [CommRing N] {c : O} {d : ℕ} [Algebra (A c d) N]
    (a : A c d) :
    ((1 : N) ⊗ₜ[A c d] algebraMap (A c d) (KNode c d) a) =
      algebraMap N (N ⊗[A c d] KNode c d) (algebraMap (A c d) N a) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]

lemma one_tmul_u_pow (i : Fin D.r) :
    letI := algOf hxy D ι i
    ((1 : N₂) ⊗ₜ[A (ϖ ^ D.m i) (D.d i)] KNode.u (ϖ ^ D.m i) (D.d i)) ^ D.d i =
      algebraMap N₂ _ (algebraMap R N₂ x) := by
  letI := algOf hxy D ι i
  rw [Algebra.TensorProduct.tmul_pow, one_pow, KNode.u_pow, one_tmul_algebraMap, algOf_u]

lemma one_tmul_u_mul_v (i : Fin D.r) :
    letI := algOf hxy D ι i
    (1 : N₂) ⊗ₜ[A (ϖ ^ D.m i) (D.d i)] KNode.u (ϖ ^ D.m i) (D.d i) *
        (1 : N₂) ⊗ₜ[A (ϖ ^ D.m i) (D.d i)] KNode.v (ϖ ^ D.m i) (D.d i) =
      algebraMap N₂ _ (algebraMap R N₂ (algebraMap O R (ϖ ^ D.m i))) := by
  letI := algOf hxy D ι i
  have h : KNode.u (ϖ ^ D.m i) (D.d i) * KNode.v (ϖ ^ D.m i) (D.d i) =
      algebraMap (A (ϖ ^ D.m i) (D.d i)) (KNode (ϖ ^ D.m i) (D.d i))
        (algebraMap O (A (ϖ ^ D.m i) (D.d i)) (ϖ ^ D.m i)) := by
    change Node.u _ * Node.v _ = Node.kummer _ _ _
    exact (Node.u_mul_v _).trans ((Node.kummer _ _).commutes _).symm
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, h, one_tmul_algebraMap, algOf_O]

/-- The node structures of `N₂` are étale if `N₂` is étale over the neighbourhood. -/
lemma etale_algOf [Algebra D.N₁ N₂] [Algebra.Etale D.N₁ N₂]
    (hι : algebraMap D.N₁ N₂ = ι.toRingHom) (i : Fin D.r) :
    letI := algOf hxy D ι i
    Algebra.Etale (A (ϖ ^ D.m i) (D.d i)) N₂ := by
  letI := nodeAlgebra D.N₁ (ϖ ^ D.m i) (D.d i) (huv_i (huvN (N₁ := D.N₁) hxy) D.hmd i)
  letI := algOf hxy D ι i
  haveI : Algebra.Etale (A (ϖ ^ D.m i) (D.d i)) D.N₁ := RingHom.etale_algebraMap.mp
    (lift_etale_of_eq (by rw [← pow_mul, D.hmd i]) D.huv _ D.het)
  haveI : IsScalarTower (A (ϖ ^ D.m i) (D.d i)) D.N₁ N₂ :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by rw [hι]; rfl
  exact Algebra.Etale.comp (A (ϖ ^ D.m i) (D.d i)) D.N₁ N₂

end Side

/-! ### Reductions along `N₂ → R̂/(1 − εⱼ)` -/

section Red

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k) {c : O} {d : ℕ}
  (hc : θ c = 0) {N N' : Type u} [CommRing N] [CommRing N'] [Algebra (A c d) N] [Algebra (A c d) N']
  {T : Type u} [CommRing T] [Algebra (A (0 : k) d) T]

lemma redTensorMap_congr {g g' : N →+* T} (h : g = g')
    (hg : ∀ a, g (algebraMap (A c d) N a) =
      algebraMap (A (0 : k) d) T (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc) a))
    (hg' : ∀ a, g' (algebraMap (A c d) N a) =
      algebraMap (A (0 : k) d) T (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc) a)) :
    FormalLevel.redTensorMap θ hc g hg = FormalLevel.redTensorMap θ hc g' hg' := by
  subst h; rfl

/-- `redTensorMap g ∘ (ι ⊗ id) = redTensorMap (g ∘ ι)`. -/
lemma redTensorMap_map (ι : N' →ₐ[A c d] N) (g : N →+* T)
    (hg : ∀ a, g (algebraMap (A c d) N a) =
      algebraMap (A (0 : k) d) T (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc) a))
    (z : N' ⊗[A c d] KNode c d) :
    FormalLevel.redTensorMap θ hc g hg (Algebra.TensorProduct.map ι (AlgHom.id _ _) z) =
      FormalLevel.redTensorMap θ hc (g.comp (ι : N' →+* N))
        (fun a ↦ (congrArg g (ι.commutes a)).trans (hg a)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, FormalLevel.redTensorMap_tmul,
      FormalLevel.redTensorMap_tmul]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

lemma redTensorMap_algebraMap_mul (g : N →+* T)
    (hg : ∀ a, g (algebraMap (A c d) N a) =
      algebraMap (A (0 : k) d) T (Node.baseMap θ (FormalKummer.θ_pow (d := d) hc) a))
    (a : N) (z : N ⊗[A c d] KNode c d) :
    FormalLevel.redTensorMap θ hc g hg (algebraMap N _ a * z) =
      (g a ⊗ₜ[A (0 : k) d] (1 : B (0 : k))) * FormalLevel.redTensorMap θ hc g hg z := by
  rw [map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    FormalLevel.redTensorMap_tmul]
  erw [map_one]

end Red


/-! ### Algebra maps out of `Â ⊗ C` into products -/

section Helpers

lemma algEquiv_tmul_apply {A S C : Type*} [CommRing A] [CommRing S] [CommRing C] [Algebra S A]
    [Algebra S C] {ι : Type*} {P : ι → Type*} [∀ p, CommRing (P p)] [∀ p, Algebra A (P p)]
    (κ : A ⊗[S] C ≃ₐ[A] ∀ p, P p) (h : A) (c : C) (p : ι) :
    κ (h ⊗ₜ c) p = algebraMap A (P p) h * κ (1 ⊗ₜ c) p := by
  have e : h ⊗ₜ[S] c = algebraMap A (A ⊗[S] C) h * (1 ⊗ₜ c) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e, map_mul, AlgEquiv.commutes, Pi.mul_apply, Pi.algebraMap_apply]

lemma kummerPiece_algebraMap {k : Type u} [Field k] {R₀ : Type u} [CommRing R₀] [Algebra k R₀]
    {f₀ : R₀} (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀) (ε : Admissible.Hat f₀) {e : ℕ}
    (he : 0 < e) (h : Admissible.Hat f₀) :
    algebraMap (Admissible.Hat f₀) (Admissible.KummerPiece φ ε he) h =
      algebraMap (Admissible.Hat f₀) (Admissible.PieceBase φ ε he) h ⊗ₜ[A (0 : k) e]
        (1 : KummerEtale.B (0 : k)) :=
  rfl

end Helpers

/-! ### Idempotents of the completion along the nodes -/

section Idem

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S] [IsNoetherianRing S]
  {f : S} {ι : Type} [Finite ι] [DecidableEq ι] {𝔫 : ι → Ideal S} [∀ j, (𝔫 j).IsMaximal]
  (hinj : Function.Injective 𝔫) (hf : ∀ j, f ∈ 𝔫 j)
  (hrad : ⨅ j, 𝔫 j ≤ (Ideal.span {f}).radical)
  (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f) (j : ι)

/-- The image of `εⱼ h` in the base of a piece at another node vanishes. -/
lemma mk_idem_mul_eq_zero {j' : ι} (hj : j' ≠ j) (h : Admissible.Hat f) :
    Ideal.Quotient.mk (Ideal.span {1 - CompletionProd.idem hinj hf hrad j'})
      (CompletionProd.idem hinj hf hrad j * h) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  refine ⟨CompletionProd.idem hinj hf hrad j * h, ?_⟩
  have h0 := CompletionProd.idem_mul_idem hinj hf hrad hj
  linear_combination (-h) * h0

/-- The image of `εⱼ h` in the base of a piece at the node `j` is the image of `h`. -/
lemma mk_idem_mul (h : Admissible.Hat f) :
    Ideal.Quotient.mk (Ideal.span {1 - CompletionProd.idem hinj hf hrad j})
      (CompletionProd.idem hinj hf hrad j * h) =
    Ideal.Quotient.mk (Ideal.span {1 - CompletionProd.idem hinj hf hrad j}) h := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  exact ⟨-h, by ring⟩

lemma pieceBase_idem_mul_eq_zero {j' : ι} (hj : j' ≠ j) {e : ℕ} (he : 0 < e)
    (h : Admissible.Hat f) :
    algebraMap (Admissible.Hat f) (Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j') he)
      (CompletionProd.idem hinj hf hrad j * h) = 0 :=
  mk_idem_mul_eq_zero hinj hf hrad j hj h

lemma pieceBase_idem_mul {e : ℕ} (he : 0 < e) (h : Admissible.Hat f) :
    algebraMap (Admissible.Hat f) (Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) he)
      (CompletionProd.idem hinj hf hrad j * h) =
    algebraMap (Admissible.Hat f) (Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) he)
      h :=
  mk_idem_mul hinj hf hrad j h

end Idem

/-! ### The special-fibre Kummer form on elements supported at one node -/

section Node

set_option linter.unusedSectionVars false

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
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]
  (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
  (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
  (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
  (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
  (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
  (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y))
  (j : ι) {N₂ : Type u} [CommRing N₂] [Algebra R N₂] (ιN : (D j).N₁ →ₐ[R] N₂)
  (hT : N₂ →ₐ[R] Tn θ (𝔪 j))
  (hTι : hT.comp ιN = hatOfₐ (𝔪 j) (hJ j) (hres j) (D j))

/-- The map `N₂ → R̂_{𝔪ⱼ} ≅ R̂/(1 − εⱼ)` onto the base of the `(j, i)`-th piece. -/
def pieceOf₂ (i : Fin (D j).r) :
    N₂ →+* Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D j).hd i) :=
  letI := chartAlg (k := k) (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) ((D j).hd i) (Tn θ (𝔪 j))
  (pieceEquiv hinj hf hrad (xy_bar (θ := θ) hxy (hn_of hϖ hn0)) φ hφu hφv
    (fun j ↦ (D j).hd) j i).toAlgHom.toRingHom.comp hT.toRingHom

include hTι in
lemma pieceOf₂_comp (i : Fin (D j).r) :
    (pieceOf₂ hxy hϖ hn0 𝔪 D hinj hf hrad φ hφu hφv j hT i).comp ιN.toRingHom =
      pieceOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j i := by
  ext z
  change (CompletionProd.quotEquiv hinj hf hrad j).symm (hT (ιN z)) =
    (CompletionProd.quotEquiv hinj hf hrad j).symm (hatOfₐ (𝔪 j) (hJ j) (hres j) (D j) z)
  rw [← AlgHom.comp_apply, hTι]

include hTι in
lemma pieceOf₂_node (i : Fin (D j).r) (a : A (ϖ ^ (D j).m i) ((D j).d i)) :
    letI := algOf hxy (D j) ιN i
    pieceOf₂ hxy hϖ hn0 𝔪 D hinj hf hrad φ hφu hφv j hT i
        (algebraMap (A (ϖ ^ (D j).m i) ((D j).d i)) N₂ a) =
      algebraMap (A (0 : k) ((D j).d i))
        (Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D j).hd i))
        (Node.baseMap θ (FormalKummer.θ_pow (d := (D j).d i) (hc_of hϖ hn0 (𝔪 j) (D j) i)) a) := by
  rw [← pieceOf_node hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j i a,
    ← pieceOf₂_comp hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j ιN hT hTι i]
  rfl

/-- **The reduction `N₂ ⊗ O[s,t]/(st − ϖ^{mᵢ}) → KummerPiece`** along `pieceOf₂`. -/
def red₂ (i : Fin (D j).r) :
    letI := algOf hxy (D j) ιN i
    N₂ ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i) →+*
      Admissible.KummerPiece φ (CompletionProd.idem hinj hf hrad j) ((D j).hd i) :=
  letI := algOf hxy (D j) ιN i
  FormalLevel.redTensorMap θ (hc_of hϖ hn0 (𝔪 j) (D j) i)
    (pieceOf₂ hxy hϖ hn0 𝔪 D hinj hf hrad φ hφu hφv j hT i)
    (pieceOf₂_node hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j ιN hT hTι i)

/-- **`kummerEquivOf` of an element supported at the node `j` vanishes at the other nodes.** -/
lemma kummerEquivOf_idem_tmul_ne (h : Admissible.Hat f) (c : Cs θ R B) {j' : ι} (hj : j' ≠ j)
    (i : Fin (D j').r) :
    kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv
      ((CompletionProd.idem hinj hf hrad j * h) ⊗ₜ c) ⟨j', i⟩ = 0 := by
  rw [algEquiv_tmul_apply, kummerPiece_algebraMap,
    pieceBase_idem_mul_eq_zero hinj hf hrad φ j hj, zero_tmul, zero_mul]

include hTι in
/-- **`kummerEquivOf` on `εⱼ ĥ ⊗ b̄` at the node `j`** is the reduction of the base changed
splitting of `n ⊗ b`, when `ĥ` lifts the image of `n` in `R̂_{𝔪ⱼ}`. -/
lemma kummerEquivOf_idem_tmul (n₂ : N₂) (b : B) (h : Admissible.Hat f)
    (hh : Ideal.Quotient.mk (Ideal.span {1 - CompletionProd.idem hinj hf hrad j}) h =
      (CompletionProd.quotEquiv hinj hf hrad j).symm (hT n₂)) (i : Fin (D j).r) :
    letI := fun i ↦ algOf hxy (D j) ιN i
    kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv
        ((CompletionProd.idem hinj hf hrad j * h) ⊗ₜ Ideal.Quotient.mk _ b) ⟨j, i⟩ =
      red₂ hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j ιN hT hTι i
        (split₂ hxy (D j) ιN (n₂ ⊗ₜ b) i) := by
  letI := fun i ↦ algOf hxy (D j) ιN i
  letI := fun i ↦ nodeAlgebra (D j).N₁ (ϖ ^ (D j).m i) ((D j).d i)
    (huv_i (huvN (N₁ := (D j).N₁) hxy) (D j).hmd i)
  have hc' : (pieceOf₂ hxy hϖ hn0 𝔪 D hinj hf hrad φ hφu hφv j hT i).comp
      (homA ιN (fun i ↦ (nodeR hxy (D j) i).toRingHom) (algebraMap_node hxy (D j))
        (fun i a ↦ (congrArg ιN (algebraMap_node hxy (D j) i a)).trans (ιN.commutes _)) i :
          (D j).N₁ →+* N₂) =
      pieceOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j i :=
    pieceOf₂_comp hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j ιN hT hTι i
  have hR : red₂ hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j ιN hT hTι i
      (split₂ hxy (D j) ιN (n₂ ⊗ₜ b) i) =
      (pieceOf₂ hxy hϖ hn0 𝔪 D hinj hf hrad φ hφu hφv j hT i n₂ ⊗ₜ[A (0 : k) ((D j).d i)]
        (1 : KummerEtale.B (0 : k))) *
      FormalLevel.redTensorMap θ (hc_of hϖ hn0 (𝔪 j) (D j) i)
        (pieceOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j i)
        (pieceOf_node hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j i)
        ((D j).Φ ((1 : (D j).N₁) ⊗ₜ b) i) := by
    rw [algEquiv_tmul_apply, split₂_one_tmul, red₂, redTensorMap_algebraMap_mul,
      redTensorMap_map, redTensorMap_congr θ _ hc' _
        (pieceOf_node hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j i)]
    rfl
  rw [algEquiv_tmul_apply, kummerEquivOf_one_tmul, kummerPiece_algebraMap,
    pieceBase_idem_mul hinj hf hrad φ j, hR,
    show algebraMap (Admissible.Hat f) (Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j)
      ((D j).hd i)) h = pieceOf₂ hxy hϖ hn0 𝔪 D hinj hf hrad φ hφu hφv j hT i n₂ from hh]

end Node

/-! ### Maps of covers -/

section Hom

set_option linter.unusedSectionVars false

attribute [local instance] algRN KummerNormAtData.algO

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
  [IsSepClosed k] [IsNoetherianRing R] {ϖ : O} {n M' : ℕ} {x y : R}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
  {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
  (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
  (hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
  (D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j))
  (D' : ∀ j, KummerNormAtData ϖ n M' x y B' (𝔪 j)) {f : Rs θ R}
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]
  (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
  (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
  (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
  (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
  (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
  (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y))
  (g : B →ₐ[R] B')

/-- **The map of special-fibre formal Kummer forms induced by `g : B → B'`.** -/
def kummerHom :
    (∀ p : (Σ j, Fin (D j).r), Admissible.KummerPiece φ (CompletionProd.idem hinj hf hrad p.1)
      ((D p.1).hd p.2)) →ₐ[Admissible.Hat f]
    ∀ p : (Σ j, Fin (D' j).r), Admissible.KummerPiece φ (CompletionProd.idem hinj hf hrad p.1)
      ((D' p.1).hd p.2) :=
  (kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id _ _) (quotHom (J θ (R := R)) g)).comp
      (kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv).symm.toAlgHom)

lemma kummerHom_kummerEquivOf (z : Admissible.Hat f ⊗[Rs θ R] Cs θ R B) :
    kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g
        (kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv z) =
      kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv
        (Algebra.TensorProduct.map (AlgHom.id (Admissible.Hat f) (Admissible.Hat f))
          (quotHom (J θ (R := R)) g) z) := by
  change kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv
    (Algebra.TensorProduct.map (AlgHom.id (Admissible.Hat f) (Admissible.Hat f))
      (quotHom (J θ (R := R)) g) ((kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv).symm
        (kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv z))) = _
  rw [AlgEquiv.symm_apply_apply]

/-- **Pieces at different nodes do not interact.** -/
lemma kummerHom_single_one_ne (j : ι) (i : Fin (D j).r) {j' : ι} (hj : j' ≠ j)
    (i' : Fin (D' j').r) :
    kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g (Pi.single ⟨j, i⟩ 1)
      ⟨j', i'⟩ = 0 := by
  have hm : ∀ {e : ℕ} (he : 0 < e), algebraMap (Admissible.Hat f)
      (Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) he)
      (CompletionProd.idem hinj hf hrad j) = 1 := fun he ↦ by
    simpa using pieceBase_idem_mul hinj hf hrad φ j he 1
  have hm0 : ∀ {e : ℕ} (he : 0 < e), algebraMap (Admissible.Hat f)
      (Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j') he)
      (CompletionProd.idem hinj hf hrad j) = 0 := fun he ↦ by
    simpa using pieceBase_idem_mul_eq_zero hinj hf hrad φ j hj he 1
  have h1 : (Pi.single ⟨j, i⟩ 1 : ∀ p : (Σ j, Fin (D j).r), Admissible.KummerPiece φ
      (CompletionProd.idem hinj hf hrad p.1) ((D p.1).hd p.2)) =
      algebraMap (Admissible.Hat f) _ (CompletionProd.idem hinj hf hrad j) * Pi.single ⟨j, i⟩ 1 :=
          by
    funext p
    rw [Pi.mul_apply, Pi.algebraMap_apply]
    rcases eq_or_ne p ⟨j, i⟩ with rfl | hp
    · rw [Pi.single_eq_same, mul_one, kummerPiece_algebraMap, hm]
      rfl
    · rw [Pi.single_eq_of_ne hp, mul_zero]
  rw [h1, map_mul, AlgHom.commutes, Pi.mul_apply, Pi.algebraMap_apply, kummerPiece_algebraMap, hm0,
    zero_tmul, zero_mul]

/-! #### The common étale neighbourhood of a node -/

variable {𝔪} in
/-- The common étale neighbourhood `N₁' ⊗_R N₁` of the node `j`. -/
abbrev Nb (j : ι) : Type u := (D' j).N₁ ⊗[R] (D j).N₁

variable {𝔪} in
/-- `N₁ → N₁' ⊗_R N₁`. -/
abbrev ι₁ (j : ι) : (D j).N₁ →ₐ[R] Nb D D' j := Algebra.TensorProduct.includeRight

variable {𝔪} in
/-- `N₁' → N₁' ⊗_R N₁`. -/
abbrev ι₂ (j : ι) : (D' j).N₁ →ₐ[R] Nb D D' j := Algebra.TensorProduct.includeLeft

/-- `N₁' ⊗_R N₁ → R̂_{𝔪ⱼ}`. -/
abbrev hatNb (j : ι) : Nb D D' j →ₐ[R] Tn θ (𝔪 j) :=
  Algebra.TensorProduct.lift (hatOfₐ (𝔪 j) (hJ j) (hres j) (D' j))
    (hatOfₐ (𝔪 j) (hJ j) (hres j) (D j)) fun _ _ ↦ Commute.all _ _

omit [Fintype ι] [DecidableEq ι] in
lemma hatNb_ι₁ (j : ι) :
    (hatNb 𝔪 hJ hres D D' j).comp (ι₁ D D' j) = hatOfₐ (𝔪 j) (hJ j) (hres j) (D j) :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

omit [Fintype ι] [DecidableEq ι] in
lemma hatNb_ι₂ (j : ι) :
    (hatNb 𝔪 hJ hres D D' j).comp (ι₂ D D' j) = hatOfₐ (𝔪 j) (hJ j) (hres j) (D' j) :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

variable {𝔪} in
/-- **The map of Kummer node factors over the common neighbourhood** induced by `g`. -/
def homNb (j : ι) :
    letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
    letI := fun i' ↦ algOf hxy (D' j) (ι₂ D D' j) i'
    (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i)) →ₐ[Nb D D'
        j]
      ∀ i', Nb D D' j ⊗[A (ϖ ^ (D' j).m i') ((D' j).d i')]
        KNode (ϖ ^ (D' j).m i') ((D' j).d i') :=
  letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
  letI := fun i' ↦ algOf hxy (D' j) (ι₂ D D' j) i'
  (split₂ hxy (D' j) (ι₂ D D' j)).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id (Nb D D' j) (Nb D D' j)) g).comp
      (split₂ hxy (D j) (ι₁ D D' j)).symm.toAlgHom)

set_option maxHeartbeats 1000000 in
-- products of base changed Kummer node factors over the common neighbourhood
set_option synthInstance.maxHeartbeats 200000 in
/-- **The reduction of `homNb` is `kummerHom`** on elements supported on one piece. -/
theorem kummerHom_single_red (j : ι) (i : Fin (D j).r) (i' : Fin (D' j).r)
    (z : letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
      Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i)) :
    letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
    letI := fun i' ↦ algOf hxy (D' j) (ι₂ D D' j) i'
    kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g
        (Pi.single ⟨j, i⟩ (red₂ hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j (ι₁ D D' j)
          (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₁ 𝔪 hJ hres D D' j) i z)) ⟨j, i'⟩ =
      red₂ hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv j (ι₂ D D' j)
          (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₂ 𝔪 hJ hres D D' j) i'
        (homNb hxy D D' g j (Pi.single i z) i') := by
  letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
  letI := fun i' ↦ algOf hxy (D' j) (ι₂ D D' j) i'
  obtain ⟨w, hw⟩ := (split₂ hxy (D j) (ι₁ D D' j)).surjective (Pi.single i z)
  have key : ∀ w : Nb D D' j ⊗[R] B, ∃ X : Admissible.Hat f ⊗[Rs θ R] Cs θ R B,
      (∀ i, kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv X ⟨j, i⟩ =
        red₂ hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j (ι₁ D D' j)
          (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₁ 𝔪 hJ hres D D' j) i
          (split₂ hxy (D j) (ι₁ D D' j) w i)) ∧
      (∀ j', j' ≠ j → ∀ i, kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv X
        ⟨j', i⟩ = 0) ∧
      (∀ i', kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv
        (Algebra.TensorProduct.map (AlgHom.id (Admissible.Hat f) (Admissible.Hat f))
          (quotHom (J θ (R := R)) g) X) ⟨j, i'⟩ =
        red₂ hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv j (ι₂ D D' j)
          (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₂ 𝔪 hJ hres D D' j) i'
          (split₂ hxy (D' j) (ι₂ D D' j)
            (Algebra.TensorProduct.map (AlgHom.id (Nb D D' j) (Nb D D' j)) g w) i')) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, fun i ↦ by simp only [map_zero, Pi.zero_apply],
        fun j' _ i ↦ by simp only [map_zero, Pi.zero_apply],
        fun i' ↦ by simp only [map_zero, Pi.zero_apply]⟩
    | tmul n₂ b =>
      obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective
        ((CompletionProd.quotEquiv hinj hf hrad j).symm (hatNb 𝔪 hJ hres D D' j n₂))
      refine ⟨(CompletionProd.idem hinj hf hrad j * h) ⊗ₜ Ideal.Quotient.mk _ b,
        fun i ↦ kummerEquivOf_idem_tmul hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j
          (ι₁ D D' j) (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₁ 𝔪 hJ hres D D' j) n₂ b h hh i,
        fun j' hj i ↦ kummerEquivOf_idem_tmul_ne hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv
          j h _ hj i, fun i' ↦ ?_⟩
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgHom.id_apply, quotHom_mk]
      exact kummerEquivOf_idem_tmul hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv j
        (ι₂ D D' j) (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₂ 𝔪 hJ hres D D' j) n₂ (g b) h hh i'
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨X₁, a₁, b₁, c₁⟩ := h₁
      obtain ⟨X₂, a₂, b₂, c₂⟩ := h₂
      refine ⟨X₁ + X₂, fun i ↦ ?_, fun j' hj i ↦ ?_, fun i' ↦ ?_⟩
      · rw [map_add, Pi.add_apply, a₁, a₂, map_add, Pi.add_apply, map_add]
      · rw [map_add, Pi.add_apply, b₁ j' hj, b₂ j' hj, add_zero]
      · rw [map_add, map_add, Pi.add_apply, c₁, c₂, map_add, map_add, Pi.add_apply, map_add]
  obtain ⟨X, hX1, hX2, hX3⟩ := key w
  have hXs : kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv X =
      Pi.single ⟨j, i⟩ (red₂ hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j (ι₁ D D' j)
        (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₁ 𝔪 hJ hres D D' j) i z) := by
    funext ⟨j', i''⟩
    by_cases hj : j' = j
    · subst hj
      rw [hX1, hw]
      rcases eq_or_ne i'' i with rfl | hi
      · rw [Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hi, map_zero, Pi.single_eq_of_ne (fun h ↦ hi (by cases h; rfl))]
    · rw [hX2 j' hj, Pi.single_eq_of_ne (fun h ↦ hj (by cases h; rfl))]
  have hΨ : homNb hxy D D' g j (Pi.single i z) = split₂ hxy (D' j) (ι₂ D D' j)
      (Algebra.TensorProduct.map (AlgHom.id (Nb D D' j) (Nb D D' j)) g w) := by
    rw [← hw]
    change split₂ hxy (D' j) (ι₂ D D' j) (Algebra.TensorProduct.map
      (AlgHom.id (Nb D D' j) (Nb D D' j)) g ((split₂ hxy (D j) (ι₁ D D' j)).symm
        (split₂ hxy (D j) (ι₁ D D' j) w))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [← hXs, kummerHom_kummerEquivOf, hX3, hΨ]

set_option maxHeartbeats 1000000 in
-- products of base changed Kummer node factors over the common neighbourhood
set_option synthInstance.maxHeartbeats 200000 in
variable {𝔪} in
omit [Fintype ι] [DecidableEq ι] in
lemma homNb_single_algebraMap (j : ι) (i : Fin (D j).r) (i' : Fin (D' j).r) (a : Nb D D' j) :
    letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
    letI := fun i' ↦ algOf hxy (D' j) (ι₂ D D' j) i'
    homNb hxy D D' g j (Pi.single i (algebraMap (Nb D D' j) (Nb D D' j ⊗[A (ϖ ^ (D j).m i)
        ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i)) a) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i)
        ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' =
      algebraMap (Nb D D' j) _ a * homNb hxy D D' g j (Pi.single i 1 : (∀ i, Nb D D' j ⊗[A (ϖ ^
          (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' := by
  letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
  letI := fun i' ↦ algOf hxy (D' j) (ι₂ D D' j) i'
  have h : (Pi.single i (algebraMap (Nb D D' j) _ a) : ∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i)
      ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i)) = algebraMap _ _ a * Pi.single i 1 := by
    funext i''
    rw [Pi.mul_apply, Pi.algebraMap_apply]
    rcases eq_or_ne i'' i with rfl | h
    · rw [Pi.single_eq_same, Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]
  rw [h, map_mul, AlgHom.commutes, Pi.mul_apply, Pi.algebraMap_apply]

set_option maxHeartbeats 1000000 in
-- products of base changed Kummer node factors over the common neighbourhood
set_option synthInstance.maxHeartbeats 200000 in
variable {𝔪} in
omit [Fintype ι] [DecidableEq ι] in
lemma homNb_single_mul (j : ι) (i : Fin (D j).r) (i' : Fin (D' j).r)
    (a b : letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
      Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i)) :
    letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
    letI := fun i' ↦ algOf hxy (D' j) (ι₂ D D' j) i'
    homNb hxy D D' g j (Pi.single i (a * b) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)]
        KNode (ϖ ^ (D j).m i) ((D j).d i))) i' =
      homNb hxy D D' g j (Pi.single i a : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode
          (ϖ ^ (D j).m i) ((D j).d i))) i' *
        homNb hxy D D' g j (Pi.single i b : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode
            (ϖ ^ (D j).m i) ((D j).d i))) i' := by
  rw [Pi.single_mul, map_mul, Pi.mul_apply]

set_option maxHeartbeats 1000000 in
-- products of base changed Kummer node factors over the common neighbourhood
set_option synthInstance.maxHeartbeats 200000 in
variable {𝔪} in
omit [Fintype ι] [DecidableEq ι] in
lemma homNb_single_pow (j : ι) (i : Fin (D j).r) (i' : Fin (D' j).r)
    (a : letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
      Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i)) (e : ℕ) :
    letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
    letI := fun i' ↦ algOf hxy (D' j) (ι₂ D D' j) i'
    homNb hxy D D' g j (Pi.single i (a ^ (e + 1)) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d
        i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' =
      homNb hxy D D' g j (Pi.single i a : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode
          (ϖ ^ (D j).m i) ((D j).d i))) i' ^ (e + 1) := by
  induction e with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ e ih => rw [pow_succ, homNb_single_mul hxy D D' g j i i', ih, ← pow_succ]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
-- products of base changed Kummer node factors over the common neighbourhood
set_option synthInstance.maxHeartbeats 200000 in
/-- **Maps of covers are balanced on the Kummer pieces** (I5(b), generic): on the piece
`(j, i)` of degree `d` and a target piece `(j, i')` of degree `d'` with `d ∣ d'`,
`s ↦ Φ(1) ζ s'^{d'/d}` and `t ↦ Φ(1) ζ^{d−1} t'^{d'/d}` with `ζ^d = 1`. -/
theorem exists_kummerHom_twist [IsDomain O] [IsIntegrallyClosed O] (hϖ0 : ϖ ≠ 0) (j : ι)
    (i : Fin (D j).r) (i' : Fin (D' j).r) (hdvd : (D j).d i ∣ (D' j).d i') :
    ∃ ζ : Admissible.KummerPiece φ (CompletionProd.idem hinj hf hrad j) ((D' j).hd i'),
      ζ ^ (D j).d i = 1 ∧
      kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g
          (Pi.single ⟨j, i⟩ ((1 : Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j)
            ((D j).hd i)) ⊗ₜ Node.u (0 : k))) ⟨j, i'⟩ =
        kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g (Pi.single ⟨j, i⟩ 1)
            ⟨j, i'⟩ * ζ *
          ((1 : Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D' j).hd i')) ⊗ₜ
            Node.u (0 : k)) ^ ((D' j).d i' / (D j).d i) ∧
      kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g
          (Pi.single ⟨j, i⟩ ((1 : Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j)
            ((D j).hd i)) ⊗ₜ Node.v (0 : k))) ⟨j, i'⟩ =
        kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g (Pi.single ⟨j, i⟩ 1)
            ⟨j, i'⟩ * ζ ^ ((D j).d i - 1) *
          ((1 : Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D' j).hd i')) ⊗ₜ
            Node.v (0 : k)) ^ ((D' j).d i' / (D j).d i) := by
  letI := fun i ↦ algOf hxy (D j) (ι₁ D D' j) i
  letI := fun i' ↦ algOf hxy (D' j) (ι₂ D D' j) i'
  haveI : Algebra.Etale (A (ϖ ^ (D' j).m i') ((D' j).d i')) (Nb D D' j) :=
    etale_algOf hxy (D' j) (ι₂ D D' j) rfl i'
  obtain ⟨D₀, hD₀⟩ := hdvd
  obtain ⟨e, he⟩ : ∃ e, (D j).d i = e + 1 := ⟨(D j).d i - 1, (Nat.sub_add_cancel ((D j).hd i)).symm⟩
  set Ψ := homNb hxy D D' g j
  have hε : IsIdempotentElem (Ψ (Pi.single i 1 : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)]
      KNode (ϖ ^ (D j).m i) ((D j).d i))) i') := by
    change _ * _ = _
    rw [← homNb_single_mul hxy D D' g j i i' 1 1, mul_one]
  have hσ : Ψ (Pi.single i 1 : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m
      i) ((D j).d i))) i' *
      Ψ (Pi.single i ((1 : Nb D D' j) ⊗ₜ KNode.u _ _) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i)
          ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' =
      Ψ (Pi.single i ((1 : Nb D D' j) ⊗ₜ KNode.u _ _) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i)
          ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' := by
    rw [← homNb_single_mul hxy D D' g j i i' 1, one_mul]
  have hτ : Ψ (Pi.single i 1 : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m
      i) ((D j).d i))) i' *
      Ψ (Pi.single i ((1 : Nb D D' j) ⊗ₜ KNode.v _ _) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i)
          ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' =
      Ψ (Pi.single i ((1 : Nb D D' j) ⊗ₜ KNode.v _ _) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i)
          ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' := by
    rw [← homNb_single_mul hxy D D' g j i i' 1, one_mul]
  have hu1 : ((1 : Nb D D' j) ⊗ₜ[A (ϖ ^ (D j).m i) ((D j).d i)] KNode.u (ϖ ^ (D j).m i)
      ((D j).d i)) ^ (e + 1) = algebraMap (Nb D D' j) (Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)]
          KNode (ϖ ^ (D j).m i) ((D j).d i)) (algebraMap R (Nb D D' j) x) :=
    (congrArg (fun n ↦ ((1 : Nb D D' j) ⊗ₜ[A (ϖ ^ (D j).m i) ((D j).d i)] KNode.u
      (ϖ ^ (D j).m i) ((D j).d i)) ^ n) he).symm.trans (one_tmul_u_pow hxy (D j) (ι₁ D D' j) i)
  have hσe : Ψ (Pi.single i ((1 : Nb D D' j) ⊗ₜ KNode.u _ _) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i)
      ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' ^ (D j).d i =
      Ψ (Pi.single i 1 : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i)
          ((D j).d i))) i' * ((1 : Nb D D' j) ⊗ₜ KNode.u _ _) ^ (D' j).d i' := by
    refine (congrArg (fun n ↦ Ψ (Pi.single i ((1 : Nb D D' j) ⊗ₜ KNode.u _ _) : (∀ i, Nb D D' j
        ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' ^ n)
      he).trans ?_
    rw [← homNb_single_pow hxy D D' g j i i' ((1 : Nb D D' j) ⊗ₜ KNode.u _ _) e, hu1,
      one_tmul_u_pow hxy (D' j) (ι₂ D D' j) i', homNb_single_algebraMap hxy D D' g j i i']
    exact mul_comm _ _
  have hm : (D j).m i = (D' j).m i' * D₀ := by
    change n / (D j).d i = n / (D' j).d i' * D₀
    refine Nat.div_eq_of_eq_mul_left ((D j).hd i) ?_
    have h2 := (D' j).hmd i'
    change n / (D' j).d i' * (D' j).d i' = n at h2
    calc n = n / (D' j).d i' * (D' j).d i' := h2.symm
      _ = _ := by rw [hD₀]; ring
  have hστ : Ψ (Pi.single i ((1 : Nb D D' j) ⊗ₜ KNode.u _ _) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i)
      ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' *
      Ψ (Pi.single i ((1 : Nb D D' j) ⊗ₜ KNode.v _ _) : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i)
          ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))) i' =
      Ψ (Pi.single i 1 : (∀ i, Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i)
          ((D j).d i))) i' *
        ((1 : Nb D D' j) ⊗ₜ KNode.u _ _ * (1 : Nb D D' j) ⊗ₜ KNode.v _ _) ^ D₀ := by
    rw [← homNb_single_mul hxy D D' g j i i' ((1 : Nb D D' j) ⊗ₜ KNode.u _ _)
        ((1 : Nb D D' j) ⊗ₜ KNode.v _ _), one_tmul_u_mul_v hxy (D j) (ι₁ D D' j) i,
      one_tmul_u_mul_v hxy (D' j) (ι₂ D D' j) i', homNb_single_algebraMap hxy D D' g j i i']
    refine (mul_comm _ _).trans (congrArg _ ?_)
    simp only [← map_pow, ← pow_mul, hm]
  obtain ⟨α, hα, hσα, hτα⟩ := KummerNodeFactor.exists_twist (Nb D D' j)
    (pow_ne_zero _ hϖ0) ((D' j).hd i') ((D j).hd i) hD₀ hε hσ hτ hσe hστ
  have hdiv : (D' j).d i' / (D j).d i = D₀ := by
    rw [hD₀, Nat.mul_div_cancel_left _ ((D j).hd i)]
  have r1 : red₂ hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j (ι₁ D D' j)
      (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₁ 𝔪 hJ hres D D' j) i 1 = 1 := map_one _
  have ru : red₂ hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j (ι₁ D D' j)
      (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₁ 𝔪 hJ hres D D' j) i
      ((1 : Nb D D' j) ⊗ₜ KNode.u _ _) =
      (1 : Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D j).hd i)) ⊗ₜ
        Node.u (0 : k) := by
    rw [red₂, FormalLevel.redTensorMap_tmul, map_one]
    exact congrArg _ (Node.baseMap_u _ _)
  have rv : red₂ hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv j (ι₁ D D' j)
      (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₁ 𝔪 hJ hres D D' j) i
      ((1 : Nb D D' j) ⊗ₜ KNode.v _ _) =
      (1 : Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D j).hd i)) ⊗ₜ
        Node.v (0 : k) := by
    rw [red₂, FormalLevel.redTensorMap_tmul, map_one]
    exact congrArg _ (Node.baseMap_v _ _)
  have ru' : red₂ hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv j (ι₂ D D' j)
      (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₂ 𝔪 hJ hres D D' j) i'
      ((1 : Nb D D' j) ⊗ₜ KNode.u _ _) =
      (1 : Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D' j).hd i')) ⊗ₜ
        Node.u (0 : k) := by
    rw [red₂, FormalLevel.redTensorMap_tmul, map_one]
    exact congrArg _ (Node.baseMap_u _ _)
  have rv' : red₂ hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv j (ι₂ D D' j)
      (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₂ 𝔪 hJ hres D D' j) i'
      ((1 : Nb D D' j) ⊗ₜ KNode.v _ _) =
      (1 : Admissible.PieceBase φ (CompletionProd.idem hinj hf hrad j) ((D' j).hd i')) ⊗ₜ
        Node.v (0 : k) := by
    rw [red₂, FormalLevel.redTensorMap_tmul, map_one]
    exact congrArg _ (Node.baseMap_v _ _)
  have h1 := (congrArg (fun z ↦ kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g
      (Pi.single ⟨j, i⟩ z) ⟨j, i'⟩) r1.symm).trans
    (kummerHom_single_red hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g j i i'
      ((1 : Nb D D' j ⊗[A (ϖ ^ (D j).m i) ((D j).d i)] KNode (ϖ ^ (D j).m i) ((D j).d i))))
  have hu := (congrArg (fun z ↦ kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g
      (Pi.single ⟨j, i⟩ z) ⟨j, i'⟩) ru.symm).trans
    (kummerHom_single_red hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g j i i'
      ((1 : Nb D D' j) ⊗ₜ KNode.u _ _))
  have hv := (congrArg (fun z ↦ kummerHom hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g
      (Pi.single ⟨j, i⟩ z) ⟨j, i'⟩) rv.symm).trans
    (kummerHom_single_red hxy hϖ hn0 𝔪 hJ hres D D' hinj hf hrad φ hφu hφv g j i i'
      ((1 : Nb D D' j) ⊗ₜ KNode.v _ _))
  refine ⟨red₂ hxy hϖ hn0 𝔪 hJ hres D' hinj hf hrad φ hφu hφv j (ι₂ D D' j)
      (hatNb 𝔪 hJ hres D D' j) (hatNb_ι₂ 𝔪 hJ hres D D' j) i' α, ((map_pow _ α _).symm.trans
          (congrArg _ hα)).trans (map_one _), ?_, ?_⟩
  · rw [hu, h1, hdiv, hσα, map_mul, map_mul]
    exact congrArg _ ((map_pow _ _ _).trans (congrArg (· ^ D₀) ru'))
  · rw [hv, h1, hdiv, hτα, map_mul, map_mul]
    exact congrArg₂ (· * ·) (congrArg _ (map_pow _ _ _))
      ((map_pow _ _ _).trans (congrArg (· ^ D₀) rv'))

end Hom

end

end FormalKummer

end SemistableReduction
