/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerTame
import TemperedFundamentalGroups.SemistableReduction.SmoothBaseChange

/-!
# Base change of étale-local Kummer data along `O → O'` (MR12 S5.7 (c), part 1)

For the finite-`k` route of S5.7 the étale-local Kummer data of S3 over `O` are base changed to a
finite unramified extension `O'` whose residue field contains the residue fields of the chosen
étale neighbourhoods, so that over `O'` the neighbourhoods have trivial residue field extensions
(`IsKummerNormAtRes`). This file contains the ring-level steps, for a ring map `ψ : N₁ → N₁'` over
`O → O'` (e.g. `N₁' = O' ⊗_O N₁`):

* **`KummerBaseChange.nonempty_equiv`**: the Kummer node factor base changes,
  `N₁' ⊗_{O[u,v]/(uv − c^d)} O[w,z]/(wz − c)` is
  `N₁' ⊗_{O'[u,v]/(uv − c'^d)} O'[w,z]/(wz − c')`
  (explicit inverse maps; `nonempty_equiv'` with `Node O c` and `Node.kummerAlgebra`);
* **`KummerBaseChange.kummerNodeSplit_baseChange`**: a splitting `KummerNodeSplit` of `X` over `N₁`
  gives one of `N₁' ⊗_{N₁} X` over `N₁'`, given the étaleness of the base-changed node chart and a
  prime `𝔫'` over `𝔫`;
* **`KummerBaseChange.resPrime`**: for `ι : N₁ → k'` compatible with a surjection `θ' : O' → k'`,
  the prime `ker (O' ⊗_O N₁ → k')` lies over `ker ι` (`comap_resPrime`) and its residue field is
  reached from `O'` (`surjective_resPrime`): the point with trivial residue field extension
  upstairs.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace KummerBaseChange

noncomputable section

/-- Ring maps out of the node agreeing on `O`, `u`, `v` are equal. -/
lemma node_ringHom_ext {O : Type*} [CommRing O] {a : O} {S : Type*} [Semiring S]
    {f g : Node O a →+* S} (hC : ∀ r, f (algebraMap O _ r) = g (algebraMap O _ r))
    (hu : f (Node.u a) = g (Node.u a)) (hv : f (Node.v a) = g (Node.v a)) : f = g := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r ↦ hC r) fun i ↦ ?_)
  fin_cases i
  · exact hu
  · exact hv

lemma one_tmul_algebraMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (r : R) :
    (1 : A) ⊗ₜ[R] (algebraMap R B r) = (algebraMap R A r) ⊗ₜ[R] (1 : B) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

variable {O O' : Type u} [CommRing O] [CommRing O'] [Algebra O O']
  {N₁ N₁' : Type u} [CommRing N₁] [CommRing N₁'] [Algebra O N₁] [Algebra O' N₁']
  (ψ : N₁ →+* N₁')
  (hψ : ∀ a : O, ψ (algebraMap O N₁ a) = algebraMap O' N₁' (algebraMap O O' a))

include hψ in
lemma huv' {c : O} {d : ℕ} {u₁ v₁ : N₁} (h : u₁ * v₁ = algebraMap O N₁ (c ^ d)) :
    ψ u₁ * ψ v₁ = algebraMap O' N₁' (algebraMap O O' c ^ d) := by
  rw [← map_mul, h, hψ, map_pow]

variable {c : O} {d : ℕ} {u₁ v₁ : N₁} (h : u₁ * v₁ = algebraMap O N₁ (c ^ d))

/-- The `Node O (c ^ d)`-algebra structure on `N₁'` through `ψ`. -/
abbrev algS : Algebra (Node O (c ^ d)) N₁' := (ψ.comp (Node.lift u₁ v₁ h).toRingHom).toAlgebra

lemma baseAlg_u (c : O) : Node.baseAlg (O' := O') c (Node.u c) = Node.u (algebraMap O O' c) :=
  Node.lift_u _ _ _

lemma baseAlg_v (c : O) : Node.baseAlg (O' := O') c (Node.v c) = Node.v (algebraMap O O' c) :=
  Node.lift_v _ _ _

set_option maxHeartbeats 800000 in
-- many tensor product and algebra structures
include hψ in
/-- **Base change of a Kummer node factor** (with `Node O c` and the Kummer algebra structure
`Node.kummerAlgebra`). -/
theorem nonempty_equiv' :
    letI := algS ψ h
    letI := nodeAlgebra N₁' (algebraMap O O' c) d (huv' ψ hψ h)
    letI := Node.kummerAlgebra c d
    letI := Node.kummerAlgebra (algebraMap O O' c) d
    Nonempty (N₁' ⊗[Node O (c ^ d)] Node O c ≃ₐ[N₁']
      N₁' ⊗[Node O' (algebraMap O O' c ^ d)] Node O' (algebraMap O O' c)) := by
  letI := algS ψ h
  letI := nodeAlgebra N₁' (algebraMap O O' c) d (huv' ψ hψ h)
  letI := Node.kummerAlgebra c d
  letI := Node.kummerAlgebra (algebraMap O O' c) d
  have hT1 : ∀ y : Node O' (algebraMap O O' c ^ d),
      ((1 : N₁') ⊗ₜ[Node O' (algebraMap O O' c ^ d)] Node.kummer (algebraMap O O' c) d y :
        N₁' ⊗[Node O' (algebraMap O O' c ^ d)] Node O' (algebraMap O O' c)) =
      algebraMap _ N₁' y ⊗ₜ 1 := fun y ↦ one_tmul_algebraMap y
  have hS1 : ∀ y : Node O (c ^ d), ((1 : N₁') ⊗ₜ[Node O (c ^ d)] Node.kummer c d y :
      N₁' ⊗[Node O (c ^ d)] Node O c) = algebraMap _ N₁' y ⊗ₜ 1 :=
    fun y ↦ one_tmul_algebraMap y
  have hlift' : ∀ r : O', algebraMap (Node O' (algebraMap O O' c ^ d)) N₁' (algebraMap O' _ r) =
      algebraMap O' N₁' r := fun r ↦ (Node.lift (ψ u₁) (ψ v₁) (huv' ψ hψ h)).commutes r
  have hu' : algebraMap (Node O' (algebraMap O O' c ^ d)) N₁' (Node.u _) = ψ u₁ :=
    Node.lift_u (ψ u₁) (ψ v₁) (huv' ψ hψ h)
  have hv' : algebraMap (Node O' (algebraMap O O' c ^ d)) N₁' (Node.v _) = ψ v₁ :=
    Node.lift_v (ψ u₁) (ψ v₁) (huv' ψ hψ h)
  -- the forward map, as a `Node O (c ^ d)`-algebra map
  letI aT : Algebra (Node O (c ^ d))
      (N₁' ⊗[Node O' (algebraMap O O' c ^ d)] Node O' (algebraMap O O' c)) :=
    ((algebraMap N₁' _).comp (algebraMap _ N₁')).toAlgebra
  let bK : Node O c →+* Node O' (algebraMap O O' c) := (Node.baseAlg (O' := O') c).toRingHom
  have bK_const : ∀ r : O, bK (algebraMap O (Node O c) r) =
      algebraMap O' (Node O' (algebraMap O O' c)) (algebraMap O O' r) := fun r ↦
    ((Node.baseAlg (O' := O') c).commutes r).trans
      (IsScalarTower.algebraMap_apply O O' (Node O' (algebraMap O O' c)) r)
  have bK_u : bK (Node.u c) = Node.u _ := baseAlg_u c
  have bK_v : bK (Node.v c) = Node.v _ := baseAlg_v c
  let gF₀ : Node O c →+* N₁' ⊗[Node O' (algebraMap O O' c ^ d)] Node O' (algebraMap O O' c) :=
    (Algebra.TensorProduct.includeRight).toRingHom.comp bK
  have gF₀_apply : ∀ x, gF₀ x = (1 : N₁') ⊗ₜ bK x := fun _ ↦ rfl
  have hgF : ∀ x : Node O (c ^ d), gF₀ (Node.kummer c d x) = algebraMap (Node O (c ^ d)) _ x := by
    intro x
    refine congrArg (fun f ↦ f x)
      (node_ringHom_ext (f := gF₀.comp (Node.kummer c d).toRingHom)
        (g := algebraMap (Node O (c ^ d)) _) (fun r ↦ ?_) ?_ ?_)
    · change (1 : N₁') ⊗ₜ bK (Node.kummer c d (algebraMap O _ r)) =
        algebraMap N₁' _ (ψ (Node.lift u₁ v₁ h (algebraMap O _ r)))
      rw [AlgHom.commutes (Node.kummer c d), bK_const, AlgHom.commutes (Node.lift u₁ v₁ h), hψ,
        ← (Node.kummer (algebraMap O O' c) d).commutes, hT1, hlift']
      rfl
    · change (1 : N₁') ⊗ₜ bK (Node.kummer c d (Node.u _)) =
        algebraMap N₁' _ (ψ (Node.lift u₁ v₁ h (Node.u _)))
      rw [Node.kummer_u, map_pow bK, Node.lift_u, bK_u, ← Node.kummer_u, hT1, hu']
      rfl
    · change (1 : N₁') ⊗ₜ bK (Node.kummer c d (Node.v _)) =
        algebraMap N₁' _ (ψ (Node.lift u₁ v₁ h (Node.v _)))
      rw [Node.kummer_v, map_pow bK, Node.lift_v, bK_v, ← Node.kummer_v, hT1, hv']
      rfl
  let gF : Node O c →ₐ[Node O (c ^ d)]
      N₁' ⊗[Node O' (algebraMap O O' c ^ d)] Node O' (algebraMap O O' c) :=
    { gF₀ with commutes' := hgF }
  let fF : N₁' →ₐ[Node O (c ^ d)]
      N₁' ⊗[Node O' (algebraMap O O' c ^ d)] Node O' (algebraMap O O' c) :=
    { algebraMap N₁' _ with commutes' := fun _ ↦ rfl }
  haveI := IsScalarTower.of_algebraMap_eq (R := Node O (c ^ d)) (S := Node O (c ^ d))
    (A := N₁' ⊗[Node O' (algebraMap O O' c ^ d)] Node O' (algebraMap O O' c)) fun _ ↦ rfl
  let F : N₁' ⊗[Node O (c ^ d)] Node O c →+*
      N₁' ⊗[Node O' (algebraMap O O' c ^ d)] Node O' (algebraMap O O' c) :=
    (Algebra.TensorProduct.lift fF gF fun _ _ ↦ Commute.all _ _).toRingHom
  have F_tmul : ∀ (a : N₁') (b : Node O c), F (a ⊗ₜ b) = algebraMap N₁' _ a * gF₀ b :=
    fun _ _ ↦ rfl
  -- the backward map, as a `Node O' (c' ^ d)`-algebra map
  letI aS : Algebra O' (N₁' ⊗[Node O (c ^ d)] Node O c) :=
    ((algebraMap N₁' _).comp (algebraMap O' N₁')).toAlgebra
  have hwz : ((1 : N₁') ⊗ₜ[Node O (c ^ d)] Node.u c : N₁' ⊗[Node O (c ^ d)] Node O c) *
      (1 ⊗ₜ Node.v c) = algebraMap O' _ (algebraMap O O' c) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Node.u_mul_v,
      ← (Node.kummer c d).commutes, hS1]
    change ψ (Node.lift u₁ v₁ h (algebraMap O _ c)) ⊗ₜ 1 = _
    rw [AlgHom.commutes, hψ]
    rfl
  let gG₀ : Node O' (algebraMap O O' c) →ₐ[O'] N₁' ⊗[Node O (c ^ d)] Node O c :=
    Node.lift _ _ hwz
  letI aS' : Algebra (Node O' (algebraMap O O' c ^ d)) (N₁' ⊗[Node O (c ^ d)] Node O c) :=
    ((algebraMap N₁' _).comp (algebraMap _ N₁')).toAlgebra
  have hgG : ∀ x : Node O' (algebraMap O O' c ^ d),
      gG₀ (Node.kummer (algebraMap O O' c) d x) =
        algebraMap (Node O' (algebraMap O O' c ^ d)) _ x := by
    intro x
    refine congrArg (fun f ↦ f x)
      (node_ringHom_ext (f := gG₀.toRingHom.comp (Node.kummer (algebraMap O O' c) d).toRingHom)
        (g := algebraMap (Node O' (algebraMap O O' c ^ d)) _) (fun r ↦ ?_) ?_ ?_)
    · change gG₀ (Node.kummer (algebraMap O O' c) d (algebraMap O' _ r)) =
        algebraMap N₁' _ (algebraMap _ N₁' (algebraMap O' _ r))
      rw [AlgHom.commutes, AlgHom.commutes, hlift']
      rfl
    · change gG₀ (Node.kummer (algebraMap O O' c) d (Node.u _)) =
        algebraMap N₁' _ (algebraMap _ N₁' (Node.u _))
      rw [Node.kummer_u, map_pow gG₀, Node.lift_u, hu', Algebra.TensorProduct.tmul_pow, one_pow,
        ← Node.kummer_u, hS1]
      change ψ (Node.lift u₁ v₁ h (Node.u _)) ⊗ₜ 1 = _
      rw [Node.lift_u]
      rfl
    · change gG₀ (Node.kummer (algebraMap O O' c) d (Node.v _)) =
        algebraMap N₁' _ (algebraMap _ N₁' (Node.v _))
      rw [Node.kummer_v, map_pow gG₀, Node.lift_v, hv', Algebra.TensorProduct.tmul_pow, one_pow,
        ← Node.kummer_v, hS1]
      change ψ (Node.lift u₁ v₁ h (Node.v _)) ⊗ₜ 1 = _
      rw [Node.lift_v]
      rfl
  let gG : Node O' (algebraMap O O' c) →ₐ[Node O' (algebraMap O O' c ^ d)]
      N₁' ⊗[Node O (c ^ d)] Node O c :=
    { gG₀.toRingHom with commutes' := hgG }
  let fG : N₁' →ₐ[Node O' (algebraMap O O' c ^ d)] N₁' ⊗[Node O (c ^ d)] Node O c :=
    { algebraMap N₁' _ with commutes' := fun _ ↦ rfl }
  haveI := IsScalarTower.of_algebraMap_eq (R := Node O' (algebraMap O O' c ^ d))
    (S := Node O' (algebraMap O O' c ^ d)) (A := N₁' ⊗[Node O (c ^ d)] Node O c) fun _ ↦ rfl
  let G : N₁' ⊗[Node O' (algebraMap O O' c ^ d)] Node O' (algebraMap O O' c) →+*
      N₁' ⊗[Node O (c ^ d)] Node O c :=
    (Algebra.TensorProduct.lift fG gG fun _ _ ↦ Commute.all _ _).toRingHom
  have G_tmul : ∀ (a : N₁') (b : Node O' (algebraMap O O' c)),
      G (a ⊗ₜ b) = algebraMap N₁' _ a * gG₀ b := fun _ _ ↦ rfl
  have F_alg : ∀ a : N₁', F (algebraMap N₁' _ a) = algebraMap N₁' _ a := fun a ↦ by
    change F (a ⊗ₜ 1) = _
    rw [F_tmul, map_one, mul_one]
  have G_alg : ∀ a : N₁', G (algebraMap N₁' _ a) = algebraMap N₁' _ a := fun a ↦ by
    change G (a ⊗ₜ 1) = _
    rw [G_tmul, map_one, mul_one]
  have hFG : F.comp G = RingHom.id _ := by
    refine Algebra.TensorProduct.ringHom_ext (RingHom.ext fun a ↦ ?_)
      (RingHom.ext fun b ↦ ?_)
    · change F (G (algebraMap N₁' _ a)) = algebraMap N₁' _ a
      rw [G_alg, F_alg]
    change F (G ((1 : N₁') ⊗ₜ b)) = (1 : N₁') ⊗ₜ b
    rw [G_tmul, map_one, one_mul]
    refine congrArg (fun f ↦ f b)
      (node_ringHom_ext (f := F.comp gG₀.toRingHom)
        (g := (Algebra.TensorProduct.includeRight : Node O' (algebraMap O O' c) →ₐ[Node O'
          (algebraMap O O' c ^ d)] _).toRingHom) (fun r ↦ ?_) ?_ ?_)
    · change F (gG₀ (algebraMap O' _ r)) =
        (1 : N₁') ⊗ₜ algebraMap O' (Node O' (algebraMap O O' c)) r
      rw [AlgHom.commutes]
      change F (algebraMap N₁' _ (algebraMap O' N₁' r)) = _
      rw [F_alg, ← (Node.kummer (algebraMap O O' c) d).commutes, hT1, hlift']
      rfl
    · change F (gG₀ (Node.u _)) = (1 : N₁') ⊗ₜ (Node.u (algebraMap O O' c))
      rw [Node.lift_u, F_tmul, map_one, one_mul, gF₀_apply, bK_u]
    · change F (gG₀ (Node.v _)) = (1 : N₁') ⊗ₜ (Node.v (algebraMap O O' c))
      rw [Node.lift_v, F_tmul, map_one, one_mul, gF₀_apply, bK_v]
  have hGF : G.comp F = RingHom.id _ := by
    refine Algebra.TensorProduct.ringHom_ext (RingHom.ext fun a ↦ ?_)
      (RingHom.ext fun b ↦ ?_)
    · change G (F (algebraMap N₁' _ a)) = algebraMap N₁' _ a
      rw [F_alg, G_alg]
    change G (F ((1 : N₁') ⊗ₜ b)) = (1 : N₁') ⊗ₜ b
    rw [F_tmul, map_one, one_mul]
    refine congrArg (fun f ↦ f b)
      (node_ringHom_ext (f := G.comp gF₀)
        (g := (Algebra.TensorProduct.includeRight :
          Node O c →ₐ[Node O (c ^ d)] _).toRingHom) (fun r ↦ ?_) ?_ ?_)
    · change G ((1 : N₁') ⊗ₜ bK (algebraMap O _ r)) = (1 : N₁') ⊗ₜ algebraMap O (Node O c) r
      rw [bK_const, ← (Node.kummer (algebraMap O O' c) d).commutes, hT1, hlift']
      change G (algebraMap N₁' _ (algebraMap O' N₁' (algebraMap O O' r))) = _
      rw [G_alg, ← (Node.kummer c d).commutes, hS1, ← hψ]
      change _ = ψ (Node.lift u₁ v₁ h (algebraMap O _ r)) ⊗ₜ 1
      rw [AlgHom.commutes]
      rfl
    · change G ((1 : N₁') ⊗ₜ bK (Node.u c)) = (1 : N₁') ⊗ₜ (Node.u c)
      rw [bK_u, G_tmul, map_one, one_mul]
      exact Node.lift_u _ _ _
    · change G ((1 : N₁') ⊗ₜ bK (Node.v c)) = (1 : N₁') ⊗ₜ (Node.v c)
      rw [bK_v, G_tmul, map_one, one_mul]
      exact Node.lift_v _ _ _
  exact ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom F G hFG hGF) F_alg⟩

include hψ in
/-- **Base change of a Kummer node factor**: for `ψ : N₁ → N₁'` over `O → O'` and `c' = c` in
`O'`, `N₁' ⊗_{O[u,v]/(uv − c^d)} O[w,z]/(wz − c)` is
`N₁' ⊗_{O'[u,v]/(uv − c'^d)} O'[w,z]/(wz − c')` (`nonempty_equiv'`). -/
theorem nonempty_equiv (c' : O') (hc : algebraMap O O' c = c') :
    letI := algS ψ h
    letI := nodeAlgebra N₁' c' d (hc ▸ huv' ψ hψ h)
    Nonempty (N₁' ⊗[Node O (c ^ d)] KNode c d ≃ₐ[N₁'] N₁' ⊗[Node O' (c' ^ d)] KNode c' d) := by
  subst hc
  exact nonempty_equiv' ψ hψ h

variable {ψ} in
include hψ in
/-- **Kummer node splittings base change**: a splitting of `X` over `N₁` into Kummer node
factors gives one of `N₁' ⊗_{N₁} X` over `N₁'` (for `O → O'`, `ψ : N₁ → N₁'`), given the
étaleness of the base-changed node chart and a prime `𝔫'` over `𝔫`. -/
theorem kummerNodeSplit_baseChange {ϖ : O} {n M' : ℕ} {𝔫 : Ideal N₁}
    {X : Type u} [CommRing X] [Algebra N₁ X]
    (hX : KummerNodeSplit ϖ n M' u₁ v₁ 𝔫 X) {𝔫' : Ideal N₁'} (h𝔫 : 𝔫 ≤ 𝔫'.comap ψ)
    (het : ∀ huv : ψ u₁ * ψ v₁ = algebraMap O' N₁' (algebraMap O O' ϖ ^ n),
      (Node.lift (ψ u₁) (ψ v₁) huv).toRingHom.Etale) :
    letI := ψ.toAlgebra
    KummerNodeSplit (algebraMap O O' ϖ) n M' (ψ u₁) (ψ v₁) 𝔫' (N₁' ⊗[N₁] X) := by
  letI := ψ.toAlgebra
  obtain ⟨huv, -, hu, hv, r, m, d, hd, hdM, hmd, ⟨Φ⟩⟩ := hX
  have huv₁ : ψ u₁ * ψ v₁ = algebraMap O' N₁' (algebraMap O O' ϖ ^ n) := huv' ψ hψ huv
  refine ⟨huv₁, het huv₁, h𝔫 hu, h𝔫 hv, r, m, d, hd, hdM, hmd, ⟨?_⟩⟩
  refine (Algebra.TensorProduct.congr AlgEquiv.refl Φ).trans
    ((Algebra.TensorProduct.piRight N₁ N₁' N₁' _).trans (AlgEquiv.piCongrRight fun i ↦ ?_))
  have hi : u₁ * v₁ = algebraMap O N₁ ((ϖ ^ m i) ^ d i) := by rw [← pow_mul, hmd i]; exact huv
  letI := nodeAlgebra N₁ (ϖ ^ m i) (d i) hi
  letI := algS ψ hi
  haveI : IsScalarTower (Node O ((ϖ ^ m i) ^ d i)) N₁ N₁' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine (Algebra.TensorProduct.cancelBaseChange (Node O ((ϖ ^ m i) ^ d i)) N₁ N₁' N₁'
    (KNode (ϖ ^ m i) (d i))).trans ?_
  exact (nonempty_equiv ψ hψ hi (algebraMap O O' ϖ ^ m i) (map_pow _ _ _)).some

end

section ResiduePrime

variable {O O' N : Type*} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing N] [Algebra O N]
  {k' : Type*} [Field k'] (θ' : O' →+* k') (ι : N →+* k')
  (hc : ∀ a : O, ι (algebraMap O N a) = θ' (algebraMap O O' a))

/-- The map `O' ⊗_O N → k'`, `a ⊗ x ↦ θ' a · ι x`. -/
noncomputable def resLift : O' ⊗[O] N →+* k' :=
  letI : Algebra O k' := (θ'.comp (algebraMap O O')).toAlgebra
  (Algebra.TensorProduct.productMap
    { θ' with commutes' := fun _ ↦ rfl } { ι with commutes' := hc }).toRingHom

lemma resLift_tmul (a : O') (x : N) : resLift θ' ι hc (a ⊗ₜ x) = θ' a * ι x := by
  simp [resLift]

/-- **The point of `O' ⊗_O N` over `𝔫 = ker ι` with residue field `k'`**: the kernel of
`resLift`. -/
noncomputable def resPrime : Ideal (O' ⊗[O] N) := RingHom.ker (resLift θ' ι hc)

instance : (resPrime θ' ι hc).IsPrime := RingHom.ker_isPrime _

lemma comap_resPrime : (resPrime θ' ι hc).comap
    (Algebra.TensorProduct.includeRight : N →ₐ[O] O' ⊗[O] N).toRingHom = RingHom.ker ι := by
  ext x
  simp [resPrime, resLift_tmul]

lemma surjective_resPrime (hθ' : Function.Surjective θ') :
    Function.Surjective ((Ideal.Quotient.mk (resPrime θ' ι hc)).comp
      (algebraMap O' (O' ⊗[O] N))) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := hθ' (resLift θ' ι hc x)
  refine ⟨a, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq, resPrime, RingHom.mem_ker, map_sub,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    resLift_tmul, map_one, mul_one, ha, sub_self]

end ResiduePrime

end KummerBaseChange

end SemistableReduction
