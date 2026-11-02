/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspPieceHom

/-!
# Maps of formal node models lift to the levels (MR12 I3, generic core)

The node analogue of `CuspPieceHom`. Let `cov`, `cov'` be admissible coverings of the same chart
(`Admissible.Covering`) and `L`, `L'` lift data of their Kummer factors at a level `O`
(`AdmissibleLift.KummerLift`), with lifted factors
`N_j = (R̂/(1 − ε̃_j)) ⊗_{O[u,v]/(uv − π_j^{e_j})} O[s,t]/(st − π_j)` (`u ↦ s^{e_j}`,
`v ↦ t^{e_j}`), reducing to the Kummer factors `KummerPiece_j` of `cov` (`redN`, componentwise
`pieceEquiv`).

At the special fibre the twists of a map `Φ : ∏_j KummerPiece_j → ∏_{j'} KummerPiece'_{j'}` on
the two branches of a node are independent of each other (`NodeNormalForm`); a lift has to respect
`st = π_j`, which ties them together. We take this as an explicit hypothesis on `Φ`, the
**balanced normal form** (`NodeHom.BalancedAt`, `NodeHom.Balanced`): for each source factor `j`
there are an `e_j`-th root of unity `ζ` and `η_{j'} ∈ O` with, on every target factor `j'` met by
`E = Φ(1_j)`, `e_j ∣ e'_{j'}`, `π_j = η_{j'} π'^{d}` and `η_{j'}^{e_j} = 1` (`d = e'_{j'}/e_j`), and
`Φ(s_j) = E ζ s'^{d}`, `Φ(t_j) = E ζ^{e_j − 1} η t'^{d}`.

* **`AdmissibleLift.NodeHom.exists_nodePiMap`**: if the lifted node coordinates agree
  (`χ_j(u) = c_u = χ'_{j'}(u)`, `χ_j(v) = c_v = χ'_{j'}(v)`), the `ε̃_j` are idempotent and `J` is
  nilpotent, every balanced `Φ` lifts to an `R̂`-algebra map `G : ∏_j N_j → ∏_{j'} N'_{j'}` with
  `redN' ∘ G = Φ ∘ redN`;
* **`AdmissibleLift.exists_nodeNFMap`**: the same for the lifted formal models `NFall` (target
  without cusp factors), compatible with `kappa3F` on the node components.

The construction mirrors `CuspPieceHom`: the idempotents `Φ(1_j)` lift to complete orthogonal
idempotents `Ẽ_j` (Mathlib `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`), `ζ` lifts to
`ζ̃` with `ζ̃^{e_j} = 1` (`CuspNormalForm.exists_pow_eq_one_lift`, `e_j` invertible), and on the
factor `j` the map is `s ↦ Ẽ_j ζ̃ s'^{d}`, `t ↦ Ẽ_j ζ̃^{e_j − 1} η t'^{d}` (`NodeHom.factorMap`,
assembled by `NodeHom.pieceMap` through `S ≃ ∏_j S/(1 − Ẽ_j)`, Mathlib
`CompleteOrthogonalIdempotents.bijective_pi`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace AdmissibleLift

noncomputable section

open KummerEtale

namespace NodeHom

/-! ### Generic algebra -/

section Generic

variable {A L B T : Type*} [CommRing A] [CommRing L] [CommRing B] [CommRing T]
  [Algebra A L] [Algebra A B]

/-- The ring map `L ⊗_A B → T`, `x ⊗ y ↦ α x · β y`, for `α`, `β` agreeing on `A`. -/
def tensorRingHom (α : L →+* T) (β : B →+* T)
    (h : α.comp (algebraMap A L) = β.comp (algebraMap A B)) : L ⊗[A] B →+* T :=
  letI : Algebra A T := (β.comp (algebraMap A B)).toAlgebra
  (Algebra.TensorProduct.lift (S := A) { α with commutes' := fun a ↦ RingHom.congr_fun h a }
    { β with commutes' := fun _ ↦ rfl } fun _ _ ↦ Commute.all _ _).toRingHom

lemma tensorRingHom_tmul (α : L →+* T) (β : B →+* T)
    (h : α.comp (algebraMap A L) = β.comp (algebraMap A B)) (x : L) (y : B) :
    tensorRingHom α β h (x ⊗ₜ y) = α x * β y := rfl

/-- Two additive and multiplicative maps out of `L ⊗_A B` agreeing on `x ⊗ 1` and `1 ⊗ y`
agree. -/
lemma tensor_fun_ext (F₁ F₂ : L ⊗[A] B → T)
    (hadd₁ : ∀ a b, F₁ (a + b) = F₁ a + F₁ b) (hadd₂ : ∀ a b, F₂ (a + b) = F₂ a + F₂ b)
    (hmul₁ : ∀ a b, F₁ (a * b) = F₁ a * F₁ b) (hmul₂ : ∀ a b, F₂ (a * b) = F₂ a * F₂ b)
    (hL : ∀ x : L, F₁ (x ⊗ₜ 1) = F₂ (x ⊗ₜ 1)) (hB : ∀ y : B, F₁ (1 ⊗ₜ y) = F₂ (1 ⊗ₜ y))
    (z : L ⊗[A] B) : F₁ z = F₂ z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    have h0 : (0 : L ⊗[A] B) = (0 : L) ⊗ₜ (1 : B) := (TensorProduct.zero_tmul _ _).symm
    rw [h0]
    exact hL 0
  | tmul x y =>
    have h1 : x ⊗ₜ[A] y = (x ⊗ₜ 1) * (1 ⊗ₜ y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1, hmul₁, hmul₂, hL, hB]
  | add a b ha hb => rw [hadd₁, hadd₂, ha, hb]

lemma one_tmul_mul (b b' : B) :
    (1 : L) ⊗ₜ[A] (b * b') = ((1 : L) ⊗ₜ[A] b) * ((1 : L) ⊗ₜ[A] b') := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

lemma one_tmul_pow (b : B) (m : ℕ) : ((1 : L) ⊗ₜ[A] b) ^ m = (1 : L) ⊗ₜ[A] (b ^ m) := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow]

lemma one_tmul_algebraMap' (a : A) :
    (1 : L) ⊗ₜ[A] algebraMap A B a = algebraMap A L a ⊗ₜ[A] (1 : B) :=
  (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm

variable {O : Type*} [CommRing O] {a : O}

/-- The ring map out of the node `O[u,v]/(uv − a)`, `u ↦ x`, `v ↦ y`, over `c : O → T`. -/
def nodeRingHom (c : O →+* T) (x y : T) (h : x * y = c a) : Node O a →+* T :=
  letI : Algebra O T := c.toAlgebra
  (Node.lift x y h).toRingHom

lemma nodeRingHom_u (c : O →+* T) (x y : T) (h : x * y = c a) :
    nodeRingHom c x y h (Node.u a) = x :=
  letI : Algebra O T := c.toAlgebra
  Node.lift_u x y h

lemma nodeRingHom_v (c : O →+* T) (x y : T) (h : x * y = c a) :
    nodeRingHom c x y h (Node.v a) = y :=
  letI : Algebra O T := c.toAlgebra
  Node.lift_v x y h

lemma nodeRingHom_algebraMap (c : O →+* T) (x y : T) (h : x * y = c a) (o : O) :
    nodeRingHom c x y h (algebraMap O (Node O a) o) = c o :=
  letI : Algebra O T := c.toAlgebra
  (Node.lift x y h).commutes o

/-- Ring maps out of the node agreeing on `O`, `u` and `v` are equal. -/
lemma nodeRingHom_ext {g₁ g₂ : Node O a →+* T}
    (hC : ∀ o, g₁ (algebraMap O (Node O a) o) = g₂ (algebraMap O (Node O a) o))
    (hu : g₁ (Node.u a) = g₂ (Node.u a)) (hv : g₁ (Node.v a) = g₂ (Node.v a)) : g₁ = g₂ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r ↦ hC r) fun i ↦ ?_)
  fin_cases i
  · exact hu
  · exact hv

/-- Two additive and multiplicative maps out of the node agreeing on `O`, `u` and `v` agree. -/
lemma node_fun_ext (F₁ F₂ : Node O a → T)
    (hadd₁ : ∀ a b, F₁ (a + b) = F₁ a + F₁ b) (hadd₂ : ∀ a b, F₂ (a + b) = F₂ a + F₂ b)
    (hmul₁ : ∀ a b, F₁ (a * b) = F₁ a * F₁ b) (hmul₂ : ∀ a b, F₂ (a * b) = F₂ a * F₂ b)
    (hC : ∀ o, F₁ (algebraMap O (Node O a) o) = F₂ (algebraMap O (Node O a) o))
    (hu : F₁ (Node.u a) = F₂ (Node.u a)) (hv : F₁ (Node.v a) = F₂ (Node.v a)) (x : Node O a) :
    F₁ x = F₂ x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r => exact hC r
  | add p q hp hq => rw [map_add, hadd₁, hadd₂, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, hmul₁, hmul₂, hp]
    fin_cases i
    · exact congrArg (F₂ _ * ·) hu
    · exact congrArg (F₂ _ * ·) hv

end Generic

/-! ### The map out of one lifted node factor -/

section Factor

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R] (f : R)
  {π : O} {e : ℕ} (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)
  {T : Type*} [CommRing T] (α : FormalPatchLevel.Hat f →+* T) (hε : α (1 - ε) = 0)
  (σ τ : T) (hστ : σ * τ = α (algebraMap O (FormalPatchLevel.Hat f) π))
  (hσ : σ ^ e = α (χ (Node.u (π ^ e)))) (hτ : τ ^ e = α (χ (Node.v (π ^ e))))

/-- `R̂/(1 − ε̃) → T` induced by `α`. -/
def lbase : LPiece f χ ε →+* T :=
  Ideal.Quotient.lift _ α fun a ha ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hε, mul_zero]

lemma lbase_mk (a : FormalPatchLevel.Hat f) :
    lbase f χ ε α hε (Ideal.Quotient.mk _ a) = α a := rfl

/-- `O[s,t]/(st − π) → T`, `s ↦ σ`, `t ↦ τ`. -/
def bmap : B π →+* T :=
  nodeRingHom (α.comp (algebraMap O (FormalPatchLevel.Hat f))) σ τ hστ

include hσ hτ in
lemma lbase_comp :
    (lbase f χ ε α hε).comp (algebraMap (A π e) (LPiece f χ ε)) =
      (bmap f α σ τ hστ).comp (algebraMap (A π e) (B π)) := by
  refine nodeRingHom_ext (fun o ↦ ?_) ?_ ?_
  · change α (χ (algebraMap O (A π e) o)) = bmap f α σ τ hστ (algebraMap (A π e) (B π)
      (algebraMap O (A π e) o))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    exact (nodeRingHom_algebraMap (α.comp (algebraMap O (FormalPatchLevel.Hat f))) σ τ hστ o).symm
  · change α (χ (Node.u (π ^ e))) = bmap f α σ τ hστ (algebraMap (A π e) (B π) (Node.u (π ^ e)))
    rw [algebraMap_u]
    calc α (χ (Node.u (π ^ e))) = σ ^ e := hσ.symm
      _ = bmap f α σ τ hστ (Node.u π) ^ e := by rw [bmap, nodeRingHom_u]
      _ = bmap f α σ τ hστ (Node.u π ^ e) := (map_pow _ _ _).symm
  · change α (χ (Node.v (π ^ e))) = bmap f α σ τ hστ (algebraMap (A π e) (B π) (Node.v (π ^ e)))
    rw [algebraMap_v]
    calc α (χ (Node.v (π ^ e))) = τ ^ e := hτ.symm
      _ = bmap f α σ τ hστ (Node.v π) ^ e := by rw [bmap, nodeRingHom_v]
      _ = bmap f α σ τ hστ (Node.v π ^ e) := (map_pow _ _ _).symm

/-- **The map out of a lifted node factor** `(R̂/(1 − ε̃)) ⊗ O[s,t]/(st − π) → T`, given by `α` on
`R̂` and `s ↦ σ`, `t ↦ τ` (for `στ = π`, `σ^e = χ(u)`, `τ^e = χ(v)`). -/
def factorMap : N f χ ε →+* T :=
  tensorRingHom (lbase f χ ε α hε) (bmap f α σ τ hστ) (lbase_comp f χ ε α hε σ τ hστ hσ hτ)

lemma factorMap_tmul (x : LPiece f χ ε) (b : B π) :
    factorMap f χ ε α hε σ τ hστ hσ hτ (x ⊗ₜ b) = lbase f χ ε α hε x * bmap f α σ τ hστ b :=
  rfl

lemma factorMap_algebraMap (a : FormalPatchLevel.Hat f) :
    factorMap f χ ε α hε σ τ hστ hσ hτ (algebraMap (FormalPatchLevel.Hat f) (N f χ ε) a) =
      α a := by
  change lbase f χ ε α hε (Ideal.Quotient.mk _ a) * bmap f α σ τ hστ 1 = α a
  rw [map_one, mul_one, lbase_mk]

lemma factorMap_s :
    factorMap f χ ε α hε σ τ hστ hσ hτ ((1 : LPiece f χ ε) ⊗ₜ Node.u π) = σ := by
  rw [factorMap_tmul, map_one, one_mul, bmap, nodeRingHom_u]

lemma factorMap_t :
    factorMap f χ ε α hε σ τ hστ hσ hτ ((1 : LPiece f χ ε) ⊗ₜ Node.v π) = τ := by
  rw [factorMap_tmul, map_one, one_mul, bmap, nodeRingHom_v]

end Factor

/-! ### Maps out of a product of lifted node factors -/

section Assemble

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R] {f : R}
  {S : Type u} [CommRing S] [Algebra (FormalPatchLevel.Hat f) S] {κ : Type} [Fintype κ]
  {π : κ → O} {e : κ → ℕ} {χ : ∀ i, A (π i) (e i) →ₐ[O] FormalPatchLevel.Hat f}
  {ε : κ → FormalPatchLevel.Hat f} {E : κ → S} {y z : κ → S}
  (hε : ∀ i, algebraMap (FormalPatchLevel.Hat f) S (1 - ε i) * E i = 0)
  (hyz : ∀ i, y i * z i * E i =
    algebraMap (FormalPatchLevel.Hat f) S (algebraMap O (FormalPatchLevel.Hat f) (π i)) * E i)
  (hy : ∀ i, y i ^ e i * E i =
    algebraMap (FormalPatchLevel.Hat f) S (χ i (Node.u (π i ^ e i))) * E i)
  (hz : ∀ i, z i ^ e i * E i =
    algebraMap (FormalPatchLevel.Hat f) S (χ i (Node.v (π i ^ e i))) * E i)

omit [Algebra (FormalPatchLevel.Hat f) S] [Fintype κ] in
lemma mk_eq_of_mul_eq (i : κ) {w w' : S} (h : w * E i = w' * E i) :
    Ideal.Quotient.mk (Ideal.span {1 - E i}) w = Ideal.Quotient.mk _ w' :=
  calc _ = Ideal.Quotient.mk (Ideal.span {1 - E i}) w * Ideal.Quotient.mk _ (E i) := by
        rw [CuspHom.mk_self, mul_one]
    _ = _ := by rw [← map_mul, h, map_mul, CuspHom.mk_self, mul_one]

omit [Fintype κ] in
variable (E) in
/-- `R̂ → S/(1 − E_i)`. -/
abbrev corner (i : κ) : FormalPatchLevel.Hat f →+* S ⧸ Ideal.span {1 - E i} :=
  (Ideal.Quotient.mk _).comp (algebraMap _ S)

omit [Fintype κ] in
/-- The factor `i`: `(R̂/(1 − ε̃_i)) ⊗ O[s,t]/(st − π_i) → S/(1 − E_i)`, `s ↦ y_i`, `t ↦ z_i`. -/
def factor (i : κ) : N f (χ i) (ε i) →+* S ⧸ Ideal.span {1 - E i} :=
  factorMap f (χ i) (ε i) (corner E i)
    ((mk_eq_of_mul_eq i ((hε i).trans (zero_mul _).symm)).trans (map_zero _))
    (Ideal.Quotient.mk _ (y i)) (Ideal.Quotient.mk _ (z i))
    ((map_mul _ _ _).symm.trans (mk_eq_of_mul_eq i (hyz i)))
    ((map_pow _ _ _).symm.trans (mk_eq_of_mul_eq i (hy i)))
    ((map_pow _ _ _).symm.trans (mk_eq_of_mul_eq i (hz i)))

omit [Fintype κ] in
lemma factor_algebraMap (i : κ) (a : FormalPatchLevel.Hat f) :
    factor hε hyz hy hz i (algebraMap _ _ a) = Ideal.Quotient.mk _ (algebraMap _ S a) :=
  factorMap_algebraMap ..

omit [Fintype κ] in
lemma factor_s (i : κ) :
    factor hε hyz hy hz i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ Node.u (π i)) =
      Ideal.Quotient.mk _ (y i) :=
  factorMap_s ..

omit [Fintype κ] in
lemma factor_t (i : κ) :
    factor hε hyz hy hz i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ Node.v (π i)) =
      Ideal.Quotient.mk _ (z i) :=
  factorMap_t ..

variable (hE : CompleteOrthogonalIdempotents E)

/-- The ring map `∏_i N_i → S`, `1_i ↦ E_i`, `s_i ↦ E_i y_i`, `t_i ↦ E_i z_i`. -/
def pieceRingHom : (∀ i, N f (χ i) (ε i)) →+* S :=
  (RingEquiv.ofBijective _ hE.bijective_pi).symm.toRingHom.comp
    (RingHom.pi fun i ↦ (factor hε hyz hy hz i).comp (Pi.evalRingHom _ i))

lemma pieceRingHom_eq {w : ∀ i, N f (χ i) (ε i)} {s : S}
    (h : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - E i}) s = factor hε hyz hy hz i (w i)) :
    pieceRingHom hε hyz hy hz hE w = s := by
  change (RingEquiv.ofBijective _ hE.bijective_pi).symm
    ((RingHom.pi fun i ↦ (factor hε hyz hy hz i).comp (Pi.evalRingHom _ i)) w) = s
  rw [RingEquiv.symm_apply_eq]
  funext i
  exact (h i).symm

lemma pieceRingHom_algebraMap (a : FormalPatchLevel.Hat f) :
    pieceRingHom hε hyz hy hz hE (algebraMap _ _ a) =
      algebraMap (FormalPatchLevel.Hat f) S a :=
  pieceRingHom_eq hε hyz hy hz hE fun i ↦ (factor_algebraMap hε hyz hy hz i a).symm

/-- **The map out of a product of lifted node factors**: the `R̂`-algebra map
`∏_i N_i → S`, `1_i ↦ E_i`, `s_i ↦ E_i y_i`, `t_i ↦ E_i z_i`. -/
def pieceMap : (∀ i, N f (χ i) (ε i)) →ₐ[FormalPatchLevel.Hat f] S :=
  { pieceRingHom hε hyz hy hz hE with commutes' := pieceRingHom_algebraMap hε hyz hy hz hE }

lemma pieceMap_apply (w : ∀ i, N f (χ i) (ε i)) :
    pieceMap hε hyz hy hz hE w = pieceRingHom hε hyz hy hz hE w := rfl

lemma pieceMap_single_one [DecidableEq κ] (i : κ) :
    pieceMap hε hyz hy hz hE (Pi.single i 1) = E i := by
  refine pieceRingHom_eq hε hyz hy hz hE fun j ↦ ?_
  by_cases hji : j = i
  · subst hji
    rw [Pi.single_eq_same, map_one, CuspHom.mk_self]
  · rw [Pi.single_eq_of_ne hji, map_zero, ← mul_one (E i), CuspHom.mk_ne hE.1 hji]

lemma pieceMap_single_s [DecidableEq κ] (i : κ) :
    pieceMap hε hyz hy hz hE (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ Node.u (π i))) =
      E i * y i := by
  refine pieceRingHom_eq hε hyz hy hz hE fun j ↦ ?_
  by_cases hji : j = i
  · subst hji
    rw [Pi.single_eq_same, map_mul, CuspHom.mk_self, one_mul, factor_s]
  · rw [Pi.single_eq_of_ne hji, map_zero, CuspHom.mk_ne hE.1 hji]

lemma pieceMap_single_t [DecidableEq κ] (i : κ) :
    pieceMap hε hyz hy hz hE (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ Node.v (π i))) =
      E i * z i := by
  refine pieceRingHom_eq hε hyz hy hz hE fun j ↦ ?_
  by_cases hji : j = i
  · subst hji
    rw [Pi.single_eq_same, map_mul, CuspHom.mk_self, one_mul, factor_t]
  · rw [Pi.single_eq_of_ne hji, map_zero, CuspHom.mk_ne hE.1 hji]

end Assemble

/-! ### Ring maps out of a product of lifted node factors are determined on generators -/

section Ext

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R] {f : R}
  {κ : Type} [Finite κ] [DecidableEq κ]
  {π : κ → O} {e : κ → ℕ} {χ : ∀ i, A (π i) (e i) →ₐ[O] FormalPatchLevel.Hat f}
  {ε : κ → FormalPatchLevel.Hat f} {T : Type*} [CommRing T]

omit [Finite κ] [DecidableEq κ] in
lemma one_tmul_algebraMap (i : κ) (o : O) :
    (1 : LPiece f (χ i) (ε i)) ⊗ₜ[A (π i) (e i)] algebraMap O (B (π i)) o =
      algebraMap (FormalPatchLevel.Hat f) (N f (χ i) (ε i))
        (algebraMap O (FormalPatchLevel.Hat f) o) := by
  rw [IsScalarTower.algebraMap_apply O (A (π i) (e i)) (B (π i)), Algebra.algebraMap_eq_smul_one,
    ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, LPiece.algebraMap_A,
    AlgHom.commutes]
  rfl

/-- **Ring maps out of `∏_i N_i` agreeing on `R̂`, `1_i`, `s_i`, `t_i` are equal.** -/
lemma ringHom_ext (g₁ g₂ : (∀ i, N f (χ i) (ε i)) →+* T)
    (halg : ∀ a, g₁ (algebraMap (FormalPatchLevel.Hat f) _ a) =
      g₂ (algebraMap (FormalPatchLevel.Hat f) _ a))
    (h1 : ∀ i, g₁ (Pi.single i 1) = g₂ (Pi.single i 1))
    (hs : ∀ i, g₁ (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ Node.u (π i))) =
      g₂ (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ Node.u (π i))))
    (ht : ∀ i, g₁ (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ Node.v (π i))) =
      g₂ (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ Node.v (π i))))
    (w : ∀ i, N f (χ i) (ε i)) : g₁ w = g₂ w := by
  refine CuspHom.pi_ringHom_ext g₁ g₂ (fun i a ↦ ?_) w
  have hL : ∀ c : FormalPatchLevel.Hat f,
      g₁ (Pi.single i (algebraMap (FormalPatchLevel.Hat f) (N f (χ i) (ε i)) c)) =
        g₂ (Pi.single i (algebraMap (FormalPatchLevel.Hat f) (N f (χ i) (ε i)) c)) := fun c ↦ by
    have hc : (Pi.single i (algebraMap (FormalPatchLevel.Hat f) (N f (χ i) (ε i)) c) :
        ∀ i, N f (χ i) (ε i)) = Pi.single i 1 * algebraMap (FormalPatchLevel.Hat f) _ c := by
      rw [← Pi.single_mul_left, one_mul]
      rfl
    rw [hc, map_mul, map_mul, h1, halg]
  refine tensor_fun_ext (fun a ↦ g₁ (Pi.single i a)) (fun a ↦ g₂ (Pi.single i a))
    (CuspHom.single_map_add g₁ i) (CuspHom.single_map_add g₂ i)
    (CuspHom.single_map_mul g₁ i) (CuspHom.single_map_mul g₂ i) (fun x ↦ ?_) (fun b ↦ ?_) a
  · obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hL c
  · have hm : ∀ b b' : B (π i), (1 : LPiece f (χ i) (ε i)) ⊗ₜ[A (π i) (e i)] (b * b') =
        ((1 : LPiece f (χ i) (ε i)) ⊗ₜ b) * ((1 : LPiece f (χ i) (ε i)) ⊗ₜ b') := fun b b' ↦
      one_tmul_mul b b'
    refine node_fun_ext (fun b ↦ g₁ (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ b)))
      (fun b ↦ g₂ (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ b)))
      (fun b b' ↦ by simp only [TensorProduct.tmul_add, CuspHom.single_map_add])
      (fun b b' ↦ by simp only [TensorProduct.tmul_add, CuspHom.single_map_add])
      (fun b b' ↦ (congrArg (fun x ↦ g₁ (Pi.single i x)) (hm b b')).trans
        (CuspHom.single_map_mul g₁ i _ _))
      (fun b b' ↦ (congrArg (fun x ↦ g₂ (Pi.single i x)) (hm b b')).trans
        (CuspHom.single_map_mul g₂ i _ _))
      (fun o ↦ ?_) (hs i) (ht i) b
    change g₁ (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ algebraMap O (B (π i)) o)) =
      g₂ (Pi.single i ((1 : LPiece f (χ i) (ε i)) ⊗ₜ algebraMap O (B (π i)) o))
    rw [one_tmul_algebraMap]
    exact hL _

end Ext

/-! ### Generators of a lifted node factor -/

section Gen

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R] (f : R)
  {π : O} {e : ℕ} (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)

lemma one_tmul_algebraMapA (a : A π e) :
    (1 : LPiece f χ ε) ⊗ₜ[A π e] algebraMap (A π e) (B π) a =
      algebraMap (FormalPatchLevel.Hat f) (N f χ ε) (χ a) :=
  one_tmul_algebraMap' a

/-- `s^e = χ(u)` in `N`. -/
lemma s_pow :
    ((1 : LPiece f χ ε) ⊗ₜ[A π e] Node.u π) ^ e =
      algebraMap (FormalPatchLevel.Hat f) (N f χ ε) (χ (Node.u (π ^ e))) := by
  refine (one_tmul_pow (Node.u π) e).trans ?_
  rw [← algebraMap_u, one_tmul_algebraMapA]

/-- `t^e = χ(v)` in `N`. -/
lemma t_pow :
    ((1 : LPiece f χ ε) ⊗ₜ[A π e] Node.v π) ^ e =
      algebraMap (FormalPatchLevel.Hat f) (N f χ ε) (χ (Node.v (π ^ e))) := by
  refine (one_tmul_pow (Node.v π) e).trans ?_
  rw [← algebraMap_v, one_tmul_algebraMapA]

/-- `st = π` in `N`. -/
lemma s_mul_t :
    ((1 : LPiece f χ ε) ⊗ₜ[A π e] Node.u π) * ((1 : LPiece f χ ε) ⊗ₜ[A π e] Node.v π) =
      algebraMap (FormalPatchLevel.Hat f) (N f χ ε) (algebraMap O (FormalPatchLevel.Hat f) π) := by
  refine (one_tmul_mul (Node.u π) (Node.v π)).symm.trans ?_
  rw [Node.u_mul_v, IsScalarTower.algebraMap_apply O (A π e) (B π), one_tmul_algebraMapA,
    AlgHom.commutes]

end Gen

/-! ### The reduction of a product of lifted node factors -/

section Red

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  {cov : Admissible.Covering φ ψc} {πL : cov.ι → O} (L : KummerLift cov πL)
  [IsNoetherianRing R] (hθ : Function.Surjective θ)

/-- `N_j/J N_j ≃ KummerPiece_j`. -/
def redjEquiv (j : cov.ι) :
    (N f (L.χ j) (L.ε j) ⧸ (J θ).map (algebraMap R (N f (L.χ j) (L.ε j)))) ≃+*
      Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j) :=
  (Ideal.quotEquivOfEq (JN_eq f (L.χ j) (L.ε j))).trans
    (pieceEquiv f φ (cov.e_pos j) (L.χ j) (L.ε j) (cov.idem j) (L.hε j) hθ (L.hπ j) (L.hχ j))

/-- The reduction `N_j → KummerPiece_j` of the factor `j`. -/
def redj (j : cov.ι) :
    N f (L.χ j) (L.ε j) →+* Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j) :=
  (redjEquiv L hθ j).toRingHom.comp (Ideal.Quotient.mk _)

lemma redj_tmul (j : cov.ι) (x : LPiece f (L.χ j) (L.ε j)) (b : B (πL j)) :
    redj L hθ j (x ⊗ₜ b) = σ θ f φ (cov.e_pos j) (L.χ j) (L.ε j) (cov.idem j) (L.hε j) x ⊗ₜ[
      A (0 : k) (cov.e j)] βr (L.hπ j) b :=
  pieceEquiv_mk_tmul f φ (cov.e_pos j) (L.χ j) (L.ε j) (cov.idem j) (L.hε j) hθ (L.hπ j)
    (L.hχ j) x b

lemma redj_algebraMap (j : cov.ι) (a : FormalPatchLevel.Hat f) :
    redj L hθ j (algebraMap (FormalPatchLevel.Hat f) (N f (L.χ j) (L.ε j)) a) =
      algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f a) := by
  change pieceEquiv f φ (cov.e_pos j) (L.χ j) (L.ε j) (cov.idem j) (L.hε j) hθ (L.hπ j) (L.hχ j)
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a ⊗ₜ 1)) = _
  rw [pieceEquiv_mk_tmul, σ_mk, map_one]
  rfl

lemma redj_s (j : cov.ι) :
    redj L hθ j ((1 : LPiece f (L.χ j) (L.ε j)) ⊗ₜ Node.u (πL j)) =
      (1 : Admissible.PieceBase φ (cov.idem j) (cov.e_pos j)) ⊗ₜ Node.u (0 : k) := by
  rw [redj_tmul, map_one, βr, Node.baseMap_u]

lemma redj_t (j : cov.ι) :
    redj L hθ j ((1 : LPiece f (L.χ j) (L.ε j)) ⊗ₜ Node.v (πL j)) =
      (1 : Admissible.PieceBase φ (cov.idem j) (cov.e_pos j)) ⊗ₜ Node.v (0 : k) := by
  rw [redj_tmul, map_one, βr, Node.baseMap_v]

lemma redj_pow_eq_zero {n : ℕ} (hJ : J θ (R := R) ^ n = ⊥) (j : cov.ι)
    {x : N f (L.χ j) (L.ε j)} (hx : redj L hθ j x = 0) : x ^ n = 0 := by
  have h1 : redjEquiv L hθ j (Ideal.Quotient.mk _ x) = 0 := hx
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem] at h1
  exact CuspHom.pow_eq_zero_of_mem_map _ hJ h1

lemma surjective_redj (j : cov.ι) : Function.Surjective (redj L hθ j) :=
  (redjEquiv L hθ j).surjective.comp Ideal.Quotient.mk_surjective

/-- The reduction `∏_j N_j → ∏_j KummerPiece_j` (componentwise `pieceEquiv`). -/
def redN : NL L →+* ∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j) :=
  RingHom.pi fun j ↦ (redj L hθ j).comp (Pi.evalRingHom _ j)

lemma redN_apply (z : NL L) (j : cov.ι) : redN L hθ z j = redj L hθ j (z j) := rfl

lemma surjective_redN : Function.Surjective (redN L hθ) := fun w ↦ by
  choose a ha using fun j ↦ surjective_redj L hθ j (w j)
  exact ⟨a, funext fun j ↦ ha j⟩

lemma nil_redN {n : ℕ} (hJ : J θ (R := R) ^ n = ⊥) :
    ∀ x ∈ RingHom.ker (redN L hθ), IsNilpotent x := fun x hx ↦
  ⟨n, funext fun j ↦ (Pi.pow_apply x n j).trans
    (redj_pow_eq_zero L hθ hJ j (congrFun (RingHom.mem_ker.mp hx) j))⟩

lemma redN_single [DecidableEq cov.ι] (j : cov.ι) (a : N f (L.χ j) (L.ε j)) :
    redN L hθ (Pi.single j a) = Pi.single j (redj L hθ j a) := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [redN_apply, Pi.single_eq_same, Pi.single_eq_same]
  · rw [redN_apply, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, map_zero]

lemma redN_algebraMap (a : FormalPatchLevel.Hat f) :
    redN L hθ (algebraMap _ _ a) = algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f a) :=
  funext fun j ↦ redj_algebraMap L hθ j a

end Red


/-! ### Twisted coordinates on a target factor -/

section Twist

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R] {f : R}
  {π' : O} {e' : ℕ} {χ' : A π' e' →ₐ[O] FormalPatchLevel.Hat f} {ε' : FormalPatchLevel.Hat f}
  {ej d : ℕ} {vj : N f χ' ε'} (hv : vj ^ ej = 1)

include hv in
/-- `(v s^d)^{e_j} = χ'(u)` for `v^{e_j} = 1`, `d e_j = e'`. -/
lemma pow_s_twist (hd : d * ej = e') :
    (vj * ((1 : LPiece f χ' ε') ⊗ₜ[A π' e'] Node.u π') ^ d) ^ ej =
      algebraMap (FormalPatchLevel.Hat f) (N f χ' ε') (χ' (Node.u (π' ^ e'))) := by
  rw [mul_pow, hv, one_mul, ← pow_mul, hd, s_pow]

include hv in
/-- `(v^{e_j − 1} η t^d)^{e_j} = χ'(v)` for `v^{e_j} = η^{e_j} = 1`, `d e_j = e'`. -/
lemma pow_t_twist (hd : d * ej = e') {η : O} (hη : η ^ ej = 1) :
    (vj ^ (ej - 1) * (algebraMap (FormalPatchLevel.Hat f) (N f χ' ε')
        (algebraMap O (FormalPatchLevel.Hat f) η) *
        ((1 : LPiece f χ' ε') ⊗ₜ[A π' e'] Node.v π') ^ d)) ^ ej =
      algebraMap (FormalPatchLevel.Hat f) (N f χ' ε') (χ' (Node.v (π' ^ e'))) := by
  rw [mul_pow, mul_pow, ← pow_mul, mul_comm (ej - 1), pow_mul, hv, one_pow, one_mul,
    ← map_pow, ← map_pow, hη, map_one, map_one, one_mul, ← pow_mul, hd, t_pow]

include hv in
/-- `(v s^d)(v^{e_j − 1} η t^d) = η π'^d`. -/
lemma s_mul_t_twist (hej : 0 < ej) {η πj : O} (hπ : πj = η * π' ^ d) :
    vj * ((1 : LPiece f χ' ε') ⊗ₜ[A π' e'] Node.u π') ^ d *
      (vj ^ (ej - 1) * (algebraMap (FormalPatchLevel.Hat f) (N f χ' ε')
        (algebraMap O (FormalPatchLevel.Hat f) η) *
        ((1 : LPiece f χ' ε') ⊗ₜ[A π' e'] Node.v π') ^ d)) =
      algebraMap (FormalPatchLevel.Hat f) (N f χ' ε')
        (algebraMap O (FormalPatchLevel.Hat f) πj) := by
  have h1 : vj * vj ^ (ej - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hej, hv]
  have h2 : algebraMap (FormalPatchLevel.Hat f) (N f χ' ε')
      (algebraMap O (FormalPatchLevel.Hat f) πj) =
      algebraMap (FormalPatchLevel.Hat f) (N f χ' ε') (algebraMap O (FormalPatchLevel.Hat f) η) *
        (((1 : LPiece f χ' ε') ⊗ₜ[A π' e'] Node.u π') *
          ((1 : LPiece f χ' ε') ⊗ₜ[A π' e'] Node.v π')) ^ d := by
    rw [hπ, map_mul (algebraMap O (FormalPatchLevel.Hat f)),
      map_mul (algebraMap (FormalPatchLevel.Hat f) (N f χ' ε')),
      map_pow (algebraMap O (FormalPatchLevel.Hat f)),
      map_pow (algebraMap (FormalPatchLevel.Hat f) (N f χ' ε')), s_mul_t]
  rw [h2, mul_pow]
  linear_combination (algebraMap (FormalPatchLevel.Hat f) (N f χ' ε')
    (algebraMap O (FormalPatchLevel.Hat f) η) *
    ((1 : LPiece f χ' ε') ⊗ₜ[A π' e'] Node.u π') ^ d *
    ((1 : LPiece f χ' ε') ⊗ₜ[A π' e'] Node.v π') ^ d) * h1

end Twist

/-! ### The balanced normal form at the special fibre -/

section Balanced

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ φ' : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc ψc' : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}

/-- The factor `j` of the special-fibre model of an admissible covering. -/
abbrev KP (cov : Admissible.Covering φ ψc) (j : cov.ι) : Type u :=
  Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)

/-- The coordinate `s = 1 ⊗ s` of the factor `j`. -/
abbrev sK (cov : Admissible.Covering φ ψc) (j : cov.ι) : KP cov j :=
  (1 : Admissible.PieceBase φ (cov.idem j) (cov.e_pos j)) ⊗ₜ Node.u (0 : k)

/-- The coordinate `t = 1 ⊗ t` of the factor `j`. -/
abbrev tK (cov : Admissible.Covering φ ψc) (j : cov.ι) : KP cov j :=
  (1 : Admissible.PieceBase φ (cov.idem j) (cov.e_pos j)) ⊗ₜ Node.v (0 : k)

variable {cov : Admissible.Covering φ ψc} {cov' : Admissible.Covering φ' ψc'} [DecidableEq cov.ι]

/-- **Balanced normal form of `Φ` on the source factor `j`**, with twist `ζ` (an `e_j`-th root
of unity) and deformation ratios `η_{j'}`: on each target factor `j'` met by `Φ(1_j)`,
`e_j ∣ e'_{j'}`, `π_j = η_{j'} π'^{e'_{j'}/e_j}` with `η_{j'}^{e_j} = 1`, and
`Φ(s_j) = Φ(1_j) ζ s'^{e'/e_j}`, `Φ(t_j) = Φ(1_j) ζ^{e_j − 1} η t'^{e'/e_j}`. The two branch
twists of a map at the special fibre are independent; balance is the condition for lifting. -/
def BalancedAt (πL : cov.ι → O) (πL' : cov'.ι → O)
    (Φ : (∀ j, KP cov j) →ₐ[Admissible.Hat (fbar θ f)] ∀ j', KP cov' j') (j : cov.ι)
    (ζ : ∀ j', KP cov' j') (η : cov'.ι → O) : Prop :=
  ζ ^ cov.e j = 1 ∧
    (∀ j', Φ (Pi.single j 1) j' ≠ 0 → cov.e j ∣ cov'.e j' ∧
      πL j = η j' * πL' j' ^ (cov'.e j' / cov.e j) ∧ η j' ^ cov.e j = 1) ∧
    Φ (Pi.single j (sK cov j)) =
      Φ (Pi.single j 1) * ζ * (fun j' ↦ sK cov' j' ^ (cov'.e j' / cov.e j)) ∧
    Φ (Pi.single j (tK cov j)) = Φ (Pi.single j 1) * ζ ^ (cov.e j - 1) * (fun j' ↦
      algebraMap (Admissible.Hat (fbar θ f)) (KP cov' j')
        (ψ θ f (algebraMap O (FormalPatchLevel.Hat f) (η j'))) *
        tK cov' j' ^ (cov'.e j' / cov.e j))

/-- **`Φ` is balanced**: it has a balanced normal form on every source factor. -/
def Balanced (πL : cov.ι → O) (πL' : cov'.ι → O)
    (Φ : (∀ j, KP cov j) →ₐ[Admissible.Hat (fbar θ f)] ∀ j', KP cov' j') : Prop :=
  ∀ j, ∃ ζ η, BalancedAt πL πL' Φ j ζ η

end Balanced

/-! ### Lifting balanced maps -/

section Lift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ φ' : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc ψc' : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  {cov : Admissible.Covering φ ψc} {cov' : Admissible.Covering φ' ψc'} [DecidableEq cov.ι]
  {πL : cov.ι → O} {πL' : cov'.ι → O} (L : KummerLift cov πL) (L' : KummerLift cov' πL')
  [IsNoetherianRing R] (hθ : Function.Surjective θ) {n : ℕ} (hJ : J θ (R := R) ^ n = ⊥)
  (Φ : (∀ j, KP cov j) →ₐ[Admissible.Hat (fbar θ f)] ∀ j', KP cov' j')

include hJ in
/-- The idempotents `Φ(1_j)` lift to complete orthogonal idempotents. -/
lemma exists_idem :
    ∃ Et : cov.ι → NL L', CompleteOrthogonalIdempotents Et ∧
      ∀ j, redN L' hθ (Et j) = Φ (Pi.single j 1) := by
  obtain ⟨Et, hEt, hEtρ⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (redN L' hθ) (nil_redN L' hθ hJ)
    ((CompleteOrthogonalIdempotents.single _).map Φ.toRingHom)
    fun i ↦ RingHom.mem_range.mpr (surjective_redN L' hθ _)
  exact ⟨Et, hEt, fun j ↦ congrFun hEtρ j⟩

include hJ in
/-- The lifted idempotent `Ẽ_j` lies over the part selected by `ε̃_j`. -/
lemma one_sub_mul_idem (hidem : ∀ j, IsIdempotentElem (L.ε j)) {Et : cov.ι → NL L'}
    (hEt : ∀ j, IsIdempotentElem (Et j)) (hEti : ∀ j, redN L' hθ (Et j) = Φ (Pi.single j 1))
    (j : cov.ι) :
    algebraMap (FormalPatchLevel.Hat f) (NL L') (1 - L.ε j) * Et j = 0 := by
  let ρ := redN L' hθ
  refine CuspHom.idem_eq_zero ρ (nil_redN L' hθ hJ)
    (((hidem j).one_sub.map (algebraMap _ _)).mul (hEt j)) ?_
  have h0 : algebraMap (Admissible.Hat (fbar θ f)) (∀ j, KP cov j) (ψ θ f (1 - L.ε j)) *
      Pi.single j 1 = 0 := by
    funext i
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same, mul_one, map_sub, map_one, L.hε i]
      have h3 : algebraMap (Admissible.Hat (fbar θ f))
          (Admissible.PieceBase φ (cov.idem i) (cov.e_pos i)) (1 - cov.idem i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      change algebraMap (Admissible.Hat (fbar θ f))
          (Admissible.PieceBase φ (cov.idem i) (cov.e_pos i)) (1 - cov.idem i) ⊗ₜ[
            A (0 : k) (cov.e i)] (1 : B (0 : k)) = 0
      rw [h3, TensorProduct.zero_tmul]
    · rw [Pi.single_eq_of_ne hij, mul_zero]
  calc ρ (algebraMap _ _ (1 - L.ε j) * Et j)
      = algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f (1 - L.ε j)) * Φ (Pi.single j 1) :=
        (map_mul ρ _ _).trans (congrArg₂ (· * ·) (redN_algebraMap L' hθ (1 - L.ε j)) (hEti j))
    _ = Φ (algebraMap _ _ (ψ θ f (1 - L.ε j)) * Pi.single j 1) :=
        ((map_mul Φ _ _).trans (congrArg (· * Φ (Pi.single j 1)) (Φ.commutes _))).symm
    _ = 0 := (congrArg Φ h0).trans (map_zero Φ)

/-- The lifted coordinate `y = v s'^{d}` on the target factors. -/
def yL (d : cov'.ι → ℕ) (v : NL L') : NL L' :=
  v * fun j' ↦ ((1 : LPiece f (L'.χ j') (L'.ε j')) ⊗ₜ Node.u (πL' j')) ^ d j'

/-- The lifted coordinate `z = v^m η t'^{d}` on the target factors. -/
def zL (d : cov'.ι → ℕ) (η : cov'.ι → O) (m : ℕ) (v : NL L') : NL L' :=
  v ^ m * fun j' ↦ algebraMap (FormalPatchLevel.Hat f) (N f (L'.χ j') (L'.ε j'))
    (algebraMap O (FormalPatchLevel.Hat f) (η j')) *
    ((1 : LPiece f (L'.χ j') (L'.ε j')) ⊗ₜ Node.v (πL' j')) ^ d j'

omit [DecidableEq cov.ι] [IsNoetherianRing R] in
lemma yL_apply (d : cov'.ι → ℕ) (v : NL L') (j' : cov'.ι) :
    yL L' d v j' = v j' * ((1 : LPiece f (L'.χ j') (L'.ε j')) ⊗ₜ Node.u (πL' j')) ^ d j' :=
  rfl

omit [DecidableEq cov.ι] [IsNoetherianRing R] in
lemma zL_apply (d : cov'.ι → ℕ) (η : cov'.ι → O) (m : ℕ) (v : NL L') (j' : cov'.ι) :
    zL L' d η m v j' = v j' ^ m * (algebraMap (FormalPatchLevel.Hat f) (N f (L'.χ j') (L'.ε j'))
      (algebraMap O (FormalPatchLevel.Hat f) (η j')) *
      ((1 : LPiece f (L'.χ j') (L'.ε j')) ⊗ₜ Node.v (πL' j')) ^ d j') :=
  rfl

omit [DecidableEq cov.ι] in
lemma redN_yL (d : cov'.ι → ℕ) (v : NL L') :
    redN L' hθ (yL L' d v) = redN L' hθ v * fun j' ↦ sK cov' j' ^ d j' := by
  rw [yL, map_mul]
  congr 1
  funext j'
  simp only [redN_apply]
  rw [map_pow (redj L' hθ j'), redj_s]

omit [DecidableEq cov.ι] in
lemma redN_zL (d : cov'.ι → ℕ) (η : cov'.ι → O) (m : ℕ) (v : NL L') :
    redN L' hθ (zL L' d η m v) = redN L' hθ v ^ m * fun j' ↦
      algebraMap (Admissible.Hat (fbar θ f)) (KP cov' j')
        (ψ θ f (algebraMap O (FormalPatchLevel.Hat f) (η j'))) * tK cov' j' ^ d j' := by
  rw [zL, map_mul, map_pow]
  congr 1
  funext j'
  simp only [redN_apply]
  rw [map_mul, map_pow (redj L' hθ j'), redj_algebraMap, redj_t]

lemma pi_mul3_eq {ι : Type*} {P : ι → Type*} [∀ i, CommRing (P i)] {y z E c : ∀ i, P i}
    (h : ∀ i, y i * z i * E i = c i * E i) : y * z * E = c * E := funext h

lemma pi_pow_mul_eq {ι : Type*} {P : ι → Type*} [∀ i, CommRing (P i)] {y E c : ∀ i, P i}
    {m : ℕ} (h : ∀ i, y i ^ m * E i = c i * E i) : y ^ m * E = c * E := funext h

include hJ in
/-- **The lifted coordinates** of the source factor `j`: `y = ζ̃ s'^{e'/e_j}` and
`z = ζ̃^{e_j − 1} η t'^{e'/e_j}` (`ζ̃` a lift of `ζ` with `ζ̃^{e_j} = 1`) satisfy the relations of
the factor `j` on `Ẽ_j`, and `Ẽ_j y`, `Ẽ_j z` reduce to `Φ(s_j)`, `Φ(t_j)`. -/
lemma exists_gen_lift {cu cv : FormalPatchLevel.Hat f}
    (hu : ∀ j, L.χ j (Node.u (πL j ^ cov.e j)) = cu)
    (hv : ∀ j, L.χ j (Node.v (πL j ^ cov.e j)) = cv)
    (hu' : ∀ j', L'.χ j' (Node.u (πL' j' ^ cov'.e j')) = cu)
    (hv' : ∀ j', L'.χ j' (Node.v (πL' j' ^ cov'.e j')) = cv)
    (j : cov.ι) {ζ : ∀ j', KP cov' j'} {η : cov'.ι → O} (hb : BalancedAt πL πL' Φ j ζ η)
    {Et : NL L'} (hEt : IsIdempotentElem Et) (hEti : redN L' hθ Et = Φ (Pi.single j 1)) :
    ∃ y z : NL L',
      y * z * Et = algebraMap (FormalPatchLevel.Hat f) (NL L')
        (algebraMap O (FormalPatchLevel.Hat f) (πL j)) * Et ∧
      y ^ cov.e j * Et =
        algebraMap (FormalPatchLevel.Hat f) (NL L') (L.χ j (Node.u (πL j ^ cov.e j))) * Et ∧
      z ^ cov.e j * Et =
        algebraMap (FormalPatchLevel.Hat f) (NL L') (L.χ j (Node.v (πL j ^ cov.e j))) * Et ∧
      redN L' hθ (Et * y) = Φ (Pi.single j (sK cov j)) ∧
      redN L' hθ (Et * z) = Φ (Pi.single j (tK cov j)) := by
  obtain ⟨hζ, hdiv, hs, ht⟩ := hb
  have hρs := surjective_redN L' hθ
  have hρN := nil_redN L' hθ hJ
  have he := cov.e_pos j
  obtain ⟨w, hw⟩ := hρs ζ
  have hT : IsUnit ((cov.e j : ℕ) : ∀ j', KP cov' j') := by
    have h1 := ((isUnit_iff_ne_zero.mpr (cov.e_ne_zero j)).map
      (algebraMap k (Admissible.Hat (fbar θ f)))).map
      (algebraMap (Admissible.Hat (fbar θ f)) (∀ j', KP cov' j'))
    rwa [map_natCast, map_natCast] at h1
  have hS : IsUnit ((cov.e j : ℕ) : NL L') :=
    CuspHom.isUnit_of_map (redN L' hθ) hρN hρs (by rw [map_natCast]; exact hT)
  have hw1 : w ^ cov.e j - 1 ∈ RingHom.ker (redN L' hθ) := RingHom.mem_ker.mpr <| by
    rw [map_sub, map_pow, map_one, hw, hζ, sub_self]
  obtain ⟨v, hv1, hv2⟩ := CuspNormalForm.exists_pow_eq_one_lift hρN he hS w hw1
  have hvρ : redN L' hθ v = ζ := by
    have h1 := RingHom.mem_ker.mp hv1
    rwa [map_sub, sub_eq_zero, hw] at h1
  have hEt0 : ∀ j', Φ (Pi.single j 1) j' = 0 → Et j' = 0 := fun j' h ↦
    IsIdempotentElem.eq_zero_of_isNilpotent (congrFun hEt j')
      ⟨n, redj_pow_eq_zero L' hθ hJ j' ((congrFun hEti j').trans h)⟩
  have hvj : ∀ j', v j' ^ cov.e j = 1 := fun j' ↦ congrFun hv2 j'
  let d : cov'.ι → ℕ := fun j' ↦ cov'.e j' / cov.e j
  refine ⟨yL L' d v, zL L' d η (cov.e j - 1) v, pi_mul3_eq fun j' ↦ ?_,
    pi_pow_mul_eq fun j' ↦ ?_, pi_pow_mul_eq fun j' ↦ ?_, ?_, ?_⟩
  · rw [yL_apply, zL_apply, Pi.algebraMap_apply]
    by_cases hE : Φ (Pi.single j 1) j' = 0
    · rw [hEt0 j' hE, mul_zero, mul_zero]
    obtain ⟨_, hπ, _⟩ := hdiv j' hE
    exact congrArg (· * Et j') (s_mul_t_twist (hvj j') he hπ)
  · rw [yL_apply, Pi.algebraMap_apply]
    by_cases hE : Φ (Pi.single j 1) j' = 0
    · rw [hEt0 j' hE, mul_zero, mul_zero]
    obtain ⟨hd, _, _⟩ := hdiv j' hE
    exact congrArg (· * Et j') ((pow_s_twist (hvj j') (Nat.div_mul_cancel hd)).trans
      (by rw [hu', hu]))
  · rw [zL_apply, Pi.algebraMap_apply]
    by_cases hE : Φ (Pi.single j 1) j' = 0
    · rw [hEt0 j' hE, mul_zero, mul_zero]
    obtain ⟨hd, _, hη⟩ := hdiv j' hE
    exact congrArg (· * Et j') ((pow_t_twist (hvj j') (Nat.div_mul_cancel hd) hη).trans
      (by rw [hv', hv]))
  · rw [hs, map_mul, redN_yL, hEti, hvρ]
    exact (mul_assoc _ _ _).symm
  · rw [ht, map_mul, redN_zL, hEti, hvρ]
    exact (mul_assoc _ _ _).symm

include hJ in
/-- **Balanced maps of products of node factors lift to the levels.** Let `L`, `L'` be lift data
of two admissible coverings with the same lifted node coordinates (`χ_j(u) = c_u`,
`χ_j(v) = c_v`, `χ'_{j'}(u) = c_u`, `χ'_{j'}(v) = c_v`), idempotent `ε̃_j`, and `J` nilpotent.
Every balanced map `Φ : ∏_j KummerPiece_j → ∏_{j'} KummerPiece'_{j'}` at the special fibre lifts
to a map `G : ∏_j N_j → ∏_{j'} N'_{j'}` of `R̂`-algebras reducing to `Φ`. -/
theorem exists_nodePiMap {cu cv : FormalPatchLevel.Hat f}
    (hu : ∀ j, L.χ j (Node.u (πL j ^ cov.e j)) = cu)
    (hv : ∀ j, L.χ j (Node.v (πL j ^ cov.e j)) = cv)
    (hu' : ∀ j', L'.χ j' (Node.u (πL' j' ^ cov'.e j')) = cu)
    (hv' : ∀ j', L'.χ j' (Node.v (πL' j' ^ cov'.e j')) = cv)
    (hidem : ∀ j, IsIdempotentElem (L.ε j)) (hbal : Balanced πL πL' Φ) :
    ∃ G : NL L →ₐ[FormalPatchLevel.Hat f] NL L',
      ∀ z, redN L' hθ (G z) = Φ (redN L hθ z) := by
  obtain ⟨Et, hEt, hEti⟩ := exists_idem L' hθ hJ Φ
  choose ζ η hb using hbal
  choose y z hyz hy hz hys hzt using fun j ↦
    exists_gen_lift L L' hθ hJ Φ hu hv hu' hv' j (hb j) (hEt.idem j) (hEti j)
  have hε := one_sub_mul_idem L L' hθ hJ Φ hidem hEt.idem hEti
  let G := pieceMap hε hyz hy hz hEt
  refine ⟨G, fun w ↦ ringHom_ext ((redN L' hθ).comp G.toRingHom)
    (Φ.toRingHom.comp (redN L hθ)) (fun a ↦ ?_) (fun j ↦ ?_) (fun j ↦ ?_) (fun j ↦ ?_) w⟩
  · change redN L' hθ (G (algebraMap _ _ a)) = Φ (redN L hθ (algebraMap _ _ a))
    rw [G.commutes, redN_algebraMap, redN_algebraMap, AlgHom.commutes]
  · change redN L' hθ (G (Pi.single j 1)) = Φ (redN L hθ (Pi.single j 1))
    rw [pieceMap_single_one, hEti, redN_single, map_one]
  · change redN L' hθ (G (Pi.single j _)) = Φ (redN L hθ (Pi.single j _))
    rw [pieceMap_single_s, hys, redN_single, redj_s]
  · change redN L' hθ (G (Pi.single j _)) = Φ (redN L hθ (Pi.single j _))
    rw [pieceMap_single_t, hzt, redN_single, redj_t]

end Lift

/-! ### The lifted formal models `NFall` -/

section Sum

variable {A : Type*} [CommRing A] {ι κ : Type} {P : ι ⊕ κ → Type*} [∀ s, CommRing (P s)]
  [∀ s, Algebra A (P s)]

variable (A P) in
/-- The projection `∏_{ι ⊕ κ} P_s → ∏_ι P_{inl j}`. -/
def toInl : (∀ s, P s) →ₐ[A] ∀ j, P (.inl j) := AlgHom.pi fun j ↦ Pi.evalAlgHom A P (.inl j)

/-- `∏_ι P_{inl j} → ∏_{ι ⊕ κ} P_s` for empty `κ`. -/
def ofInlFun [IsEmpty κ] (z : ∀ j, P (.inl j)) : ∀ s, P s
  | .inl j => z j
  | .inr i => isEmptyElim i

variable (A P) in
/-- `∏_ι P_{inl j} ≅ ∏_{ι ⊕ κ} P_s` for empty `κ`, as an algebra map. -/
def ofInl [IsEmpty κ] : (∀ j, P (.inl j)) →ₐ[A] ∀ s, P s where
  toFun := ofInlFun
  map_one' := funext fun s ↦ match s with
    | .inl _ => rfl
    | .inr i => isEmptyElim i
  map_mul' _ _ := funext fun s ↦ match s with
    | .inl _ => rfl
    | .inr i => isEmptyElim i
  map_zero' := funext fun s ↦ match s with
    | .inl _ => rfl
    | .inr i => isEmptyElim i
  map_add' _ _ := funext fun s ↦ match s with
    | .inl _ => rfl
    | .inr i => isEmptyElim i
  commutes' _ := funext fun s ↦ match s with
    | .inl _ => rfl
    | .inr i => isEmptyElim i

end Sum

section NF

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ φ' : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc ψc' : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  {cov : Admissible.Covering φ ψc} {cov' : Admissible.Covering φ' ψc'}
  {πL : cov.ι → O} {πL' : cov'.ι → O}
  (L : KummerLift cov πL) (M : CuspLift cov) (L' : KummerLift cov' πL') (M' : CuspLift cov')

/-- The node components of the reduction `κ3F` are `redN`. -/
lemma kappa3F_fst [IsNoetherianRing R] (hθ : Function.Surjective θ) (x : NFall L M) :
    (kappa3F L M hθ (Ideal.Quotient.mk _ x)).1 =
      redN L hθ (toInl (FormalPatchLevel.Hat f) (NF L M) x) := rfl

end NF

end NodeHom

section NF

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ φ' : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc ψc' : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  {cov : Admissible.Covering φ ψc} {cov' : Admissible.Covering φ' ψc'}
  {πL : cov.ι → O} {πL' : cov'.ι → O}
  (L : KummerLift cov πL) (M : CuspLift cov) (L' : KummerLift cov' πL') (M' : CuspLift cov')

open NodeHom in
/-- **Balanced maps of formal node models lift to the levels.** For two admissible coverings
`cov`, `cov'` of the same chart, `cov'` without cusp factors, lift data `L`, `L'` with the same
lifted node coordinates `c_u`, `c_v` and idempotent `ε̃_j`, and `J` nilpotent, every balanced map
`Φ` of the formal node models at the special fibre (`NodeHom.Balanced`) lifts to a map
`g : NFall L M → NFall L' M'` of `R̂`-algebras whose reduction is `Φ` on the node components. -/
theorem exists_nodeNFMap [IsNoetherianRing R] (hθ : Function.Surjective θ) {n : ℕ}
    (hJ : J θ (R := R) ^ n = ⊥) [IsEmpty cov'.κ] [DecidableEq cov.ι]
    {cu cv : FormalPatchLevel.Hat f}
    (hu : ∀ j, L.χ j (Node.u (πL j ^ cov.e j)) = cu)
    (hv : ∀ j, L.χ j (Node.v (πL j ^ cov.e j)) = cv)
    (hu' : ∀ j', L'.χ j' (Node.u (πL' j' ^ cov'.e j')) = cu)
    (hv' : ∀ j', L'.χ j' (Node.v (πL' j' ^ cov'.e j')) = cv)
    (hidem : ∀ j, IsIdempotentElem (L.ε j))
    (Φ : (∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)) →ₐ[Admissible.Hat (fbar θ f)]
      ∀ j', Admissible.KummerPiece φ' (cov'.idem j') (cov'.e_pos j'))
    (hbal : Balanced πL πL' Φ) :
    ∃ g : NFall L M →ₐ[FormalPatchLevel.Hat f] NFall L' M', ∀ x,
      (kappa3F L' M' hθ (Ideal.Quotient.mk _ (g x))).1 =
        Φ (kappa3F L M hθ (Ideal.Quotient.mk _ x)).1 := by
  obtain ⟨G, hG⟩ := exists_nodePiMap L L' hθ hJ Φ hu hv hu' hv' hidem hbal
  refine ⟨(ofInl (FormalPatchLevel.Hat f) (NF L' M')).comp
    (G.comp (toInl (FormalPatchLevel.Hat f) (NF L M))), fun x ↦ ?_⟩
  exact (hG (toInl (FormalPatchLevel.Hat f) (NF L M) x)).trans
    (congrArg Φ (kappa3F_fst L M hθ x).symm)

end NF

end

end AdmissibleLift

end SemistableReduction
