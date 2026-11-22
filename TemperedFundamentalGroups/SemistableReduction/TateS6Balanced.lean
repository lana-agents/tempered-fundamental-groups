/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6SurjCov
import TemperedFundamentalGroups.SemistableReduction.TateNodeBalanced

/-!
# The special-fibre data of maps of covers are balanced (MR12, interface I5(b))

* `IsIntegralClosure.intMap` (generic): the map of integral closures induced by an algebra map of
  the ambient rings; `NodeEtaleGlue.Special.covMap_eq` (generic): the map of node coverings
  `covMap f` is the unique map compatible with `ι₀`;
* **`TateS6.covBalanced_datumHom`** (I5(b)): for every `K`-algebra map `f : C.L → C'.L` of tame
  covers, the morphism of special-fibre data `datumHom f` is balanced at the nodes
  (`CovBalanced`): its node map is the reduction of the map `C.Bn → C'.Bn` of normalisations of
  the node chart (`covMap_eq`), balanced at the special chart by
  `TateTwoChartNode.covNR_balancedK`, hence at every level (`nodeBalanced_of_balancedK`);
* **`TateS6.mem_mrange_galHom_iff`**: an endomorphism of the special-fibre datum of `C` comes from
  `Gal(C.L/K)` iff it is balanced; with `galEquiv`,
  **`Gal(C.L/K) ≃* Aut_bal(datum C)`** (`TateS6.galEquivBal`).
-/

universe u

open Polynomial

namespace SemistableReduction

/-! ### Generic -/

namespace IsIntegralClosure

variable {R L L' B B' : Type*} [CommRing R] [CommRing L] [CommRing L'] [Algebra R L]
  [Algebra R L'] [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] [Algebra B L]
  [Algebra B' L'] [IsScalarTower R B L] [IsScalarTower R B' L'] [IsIntegralClosure B R L]
  [IsIntegralClosure B' R L']

/-- **The map of integral closures** induced by an `R`-algebra map `f : L → L'`. -/
noncomputable def intMap (f : L →ₐ[R] L') : B →ₐ[R] B' where
  toFun b := IsIntegralClosure.mk' B' (f (algebraMap B L b))
    ((IsIntegralClosure.isIntegral R L b).algebraMap.map f)
  map_one' := IsIntegralClosure.algebraMap_injective B' R L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_one, map_one, map_one])
  map_mul' x y := IsIntegralClosure.algebraMap_injective B' R L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_mul, map_mul, map_mul,
      IsIntegralClosure.algebraMap_mk', IsIntegralClosure.algebraMap_mk'])
  map_zero' := IsIntegralClosure.algebraMap_injective B' R L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_zero, map_zero, map_zero])
  map_add' x y := IsIntegralClosure.algebraMap_injective B' R L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_add, map_add, map_add,
      IsIntegralClosure.algebraMap_mk', IsIntegralClosure.algebraMap_mk'])
  commutes' r := IsIntegralClosure.algebraMap_injective B' R L' (by
    rw [IsIntegralClosure.algebraMap_mk', ← IsScalarTower.algebraMap_apply, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply])

lemma algebraMap_intMap (f : L →ₐ[R] L') (b : B) :
    algebraMap B' L' (intMap (B := B) (B' := B') f b) = f (algebraMap B L b) :=
  IsIntegralClosure.algebraMap_mk' (R := R) B' _
    ((IsIntegralClosure.isIntegral R L b).algebraMap.map f)

/-- `intMap f` is compatible with maps `B₁ → B`, `B₁' → B'` into the integral closures and a map
`m : B₁ → B₁'` compatible with `f`. -/
lemma intMap_algebraMap {B₁ B₁' : Type*} [CommRing B₁] [CommRing B₁'] [Algebra B₁ B] [Algebra B₁ L]
    [IsScalarTower B₁ B L] [Algebra B₁' B'] [Algebra B₁' L'] [IsScalarTower B₁' B' L']
    (f : L →ₐ[R] L') (m : B₁ → B₁') (hm : ∀ b, algebraMap B₁' L' (m b) = f (algebraMap B₁ L b))
    (b : B₁) :
    intMap (B := B) (B' := B') f (algebraMap B₁ B b) = algebraMap B₁' B' (m b) :=
  IsIntegralClosure.algebraMap_injective B' R L' (by
    rw [algebraMap_intMap, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hm])

end IsIntegralClosure

namespace FormalKummer

/-- Reductions of maps compatible with the inclusions of quotients. -/
lemma quotHom_comp_eq {R B₁ B B₁' B' : Type u} [CommRing R] [CommRing B₁] [CommRing B]
    [CommRing B₁'] [CommRing B'] [Algebra R B] [Algebra R B'] (I : Ideal R) {I₁ : Ideal B₁}
    {I₁' : Ideal B₁'} (ι₀ : B₁ ⧸ I₁ → B ⧸ I.map (algebraMap R B))
    (ι₀' : B₁' ⧸ I₁' → B' ⧸ I.map (algebraMap R B')) (j : B₁ → B) (j' : B₁' → B')
    (hι : ∀ b, ι₀ (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (j b))
    (hι' : ∀ b, ι₀' (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (j' b)) (m : B₁ → B₁')
    (f₁ : B₁ ⧸ I₁ → B₁' ⧸ I₁') (hf : ∀ b, f₁ (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (m b))
    (g : B →ₐ[R] B') (hg : ∀ b, g (j b) = j' (m b)) (c : B₁ ⧸ I₁) :
    quotHom I g (ι₀ c) = ι₀' (f₁ c) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [hι, hf, hι', quotHom_mk, hg]

end FormalKummer

namespace NodeEtaleGlue.Special

variable {k : Type u} [Field k] {Bs : Type u} [CommRing Bs] {R₀ : Type u} [CommRing R₀]
  [Algebra k R₀] {f₀ : R₀} {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀'}
  {φs : Bs →+* R₀} {abar bbar : Bs}
  (Sp : Special Bs cov₀ φs abar bbar) (Sp' : Special Bs cov₀' φs abar bbar)
  (hloc : letI := φs.toAlgebra; IsLocalization.Away abar R₀)

/-- **`covMap f` is the unique map of node coverings compatible with `ι₀`.** -/
lemma covMap_eq (f : Sp.C1 →ₐ[Bs] Sp'.C1) (φ : cov₀.C →ₐ[R₀] cov₀'.C)
    (h : ∀ c, φ (Sp.ι₀ c) = Sp'.ι₀ (f c)) : Sp.covMap Sp' hloc f = φ := by
  letI := Sp.ι₀.toAlgebra
  haveI := Sp.hι
  refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
    (Submonoid.powers (algebraMap Bs Sp.C1 abar)) (RingHom.ext fun c ↦ ?_))
  change Sp.covMap Sp' hloc f (Sp.ι₀ c) = φ (Sp.ι₀ c)
  rw [covMap_ι₀, h]

end NodeEtaleGlue.Special


namespace TateGlue1

open TateTwoChart TateTwoChartNode AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ}

set_option maxHeartbeats 1000000 in
-- comparison of the node coverings of two covers
/-- **The node map of the reduction of an `NR`-algebra map `g` of normalisations is balanced**
(I5(b) at `special1`): `covMap f₁` is the reduction of `g` (`covMap_eq`), balanced at the special
chart by `covNR_balancedK`, hence at every level. -/
theorem balanced_of_quotHom [IsDomain O] [IsDiscreteValuationRing O]
    [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) [NeZero m]
    (hκ : κ * (t ^ 2 - b₆) = 1) (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
    {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M') (hM'k : (M' : k) ≠ 0)
    (K : Type u) [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K]
    [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
    (hK : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) K (toNode b₄ hκ rfl x) =
      algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) K x)
    {ζ : K} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (Module.finrank K L).Coprime q) [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L]
    [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K L] [Algebra (NR b₄ b₆ ϖ m ε) L]
    [IsScalarTower (NR b₄ b₆ ϖ m ε) K L]
    (B₁ : Type u) [CommRing B₁] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁] [Algebra B₁ L]
    [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) B₁ L]
    [IsIntegralClosure B₁ (T1 (ε * ϖ ^ m) b₄ t κ) L]
    (B : Type u) [CommRing B] [Algebra (NR b₄ b₆ ϖ m ε) B] [Algebra B L]
    [IsScalarTower (NR b₄ b₆ ϖ m ε) B L] [Algebra B₁ B] [IsScalarTower B₁ B L]
    [IsLocalization.Away
      (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁ (DT (ε * ϖ ^ m) b₄ t κ)) B]
    (hB : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) B (toNode b₄ hκ rfl x) =
      algebraMap B₁ B (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁ x))
    [Fact (NodeNbhdRational θ b₄ b₆ ϖ m ε M' B)]
    (hunr : ∀ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal],
      algebraMap O (T1 (ε * ϖ ^ m) b₄ t κ) ϖ ∈ P → ∀ (Q : Ideal B₁) [Q.IsPrime],
        Q.comap (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁) < P →
          Algebra.IsUnramifiedAt (T1 (ε * ϖ ^ m) b₄ t κ) Q)
    (L' : Type u) [Field L'] [Algebra K L'] [FiniteDimensional K L'] [IsGalois K L']
    (hL' : (Module.finrank K L').Coprime q) [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L']
    [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K L'] [Algebra (NR b₄ b₆ ϖ m ε) L']
    [IsScalarTower (NR b₄ b₆ ϖ m ε) K L']
    (B₁' : Type u) [CommRing B₁'] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁'] [Algebra B₁' L']
    [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) B₁' L']
    [IsIntegralClosure B₁' (T1 (ε * ϖ ^ m) b₄ t κ) L']
    (B' : Type u) [CommRing B'] [Algebra (NR b₄ b₆ ϖ m ε) B'] [Algebra B' L']
    [IsScalarTower (NR b₄ b₆ ϖ m ε) B' L'] [Algebra B₁' B'] [IsScalarTower B₁' B' L']
    [IsLocalization.Away
      (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁' (DT (ε * ϖ ^ m) b₄ t κ)) B']
    (hB' : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) B' (toNode b₄ hκ rfl x) =
      algebraMap B₁' B' (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁' x))
    [Fact (NodeNbhdRational θ b₄ b₆ ϖ m ε M' B')]
    (hunr' : ∀ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal],
      algebraMap O (T1 (ε * ϖ ^ m) b₄ t κ) ϖ ∈ P → ∀ (Q : Ideal B₁') [Q.IsPrime],
        Q.comap (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁') < P →
          Algebra.IsUnramifiedAt (T1 (ε * ϖ ^ m) b₄ t κ) Q)
    (hπe : θ (ϖ ^ m) = 0) (τ : Rb b₄ b₆ ϖ m ε)
    [IsEmpty (covTate hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ B hB hunr hπe τ).κ]
    (g : B →ₐ[NR b₄ b₆ ϖ m ε] B')
    (f₁ : (special1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ B hB hunr hπe τ).C1 →ₐ[T1s
        θ (ε * ϖ ^ m) b₄ t κ] (special1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L' hL' B₁' B'
        hB' hunr' hπe τ).C1)
    (hcomp : ∀ c, FormalKummer.quotHom (J θ (R := NR b₄ b₆ ϖ m ε)) g ((special1 hϖ hker hκ hε h3
        hE hqM hq hM' hM'k K hK hζ L hL B₁ B hB hunr hπe τ).ι₀ c) =
      (special1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L' hL' B₁' B' hB' hunr' hπe τ).ι₀
          (f₁ c)) :
    Balanced hκ rfl hε (special1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ B hB hunr hπe
        τ) (special1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L' hL' B₁' B' hB' hunr' hπe τ)
        (RingHom.mem_ker.1 (hker ▸ Ideal.mem_span_singleton_self ϖ))
      (fun j ↦ ϖ ^ (m / (covTate hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ B hB hunr hπe
          τ).e j)) (fun j ↦ ϖ ^ (m / (covTate hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L' hL'
          B₁' B' hB' hunr' hπe τ).e j)) f₁ := by
  haveI := isFractionRing_NR hϖ hκ hε h3 hE K hK
  haveI := isIntegralClosure_B hϖ hκ hε K hK L B₁ B
  haveI := isIntegralClosure_B hϖ hκ hε K hK L' B₁' B'
  have hbal := covNR_balancedK hϖ hker (.of_mul_eq_one_right εi hε) h3 hE hqM hq hM' hM'k K hζ
    L hL B (hunr_B hκ hε B₁ B hB hunr) L' hL' B' (hunr_B hκ hε B₁' B' hB' hunr') hπe
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ) g
  have hcov : covMap hκ rfl hε (special1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ B hB
      hunr hπe τ) (special1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L' hL' B₁' B' hB' hunr'
      hπe τ) f₁ =
      FormalKummer.quotHom (J θ (R := NR b₄ b₆ ϖ m ε)) g :=
    NodeEtaleGlue.Special.covMap_eq _ _ (isLocalization_toNodeJ hκ rfl hε) f₁ _ hcomp
  intro n
  refine LevelTower.nodeBalanced_of_balancedK (d := instDecidableEqCovNRι hϖ hker
    (.of_mul_eq_one_right εi hε) h3 hE hqM hq hM' hM'k K hζ L hL B
    (hunr_B hκ hε B₁ B hB hunr) hπe
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)) _
    (fun n o ↦ QuadNodeTower.algK_θ _ o) _ ?_ n
  rw [hcov]
  exact hbal

end TateGlue1

namespace TateS6

open TateTwoChart TateTwoChartNode TateGlue0 TateLevel AdmissibleLift

noncomputable section

section Functor

set_option linter.unusedSectionVars false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m] [hsq : Fact (IsSquare (θ b₆))]
  (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
  {hκ : κ * (t ^ 2 - b₆) = 1} (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) (hb₆ : IsUnit b₆)
  {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M') (hM'k : (M' : k) ≠ 0)
  [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
  {K : Type u} [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K]
  [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
  (hK : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) K (toNode b₄ hκ rfl x) =
    algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) K x)
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (RcT (ε * ϖ ^ m) b₄ t κ) K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ M') {ζe : K} (hζe : IsPrimitiveRoot ζe e)
  (τ : TateGlue1.Rb b₄ b₆ ϖ m ε)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 (ε * ϖ ^ m) b₄ t κ) (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) (h0 (ε * ϖ ^ m) b₄ t
        κ))))

set_option hygiene false in
/-- The chart instances of a Tate cover `C`, stated over the concrete Tate charts. -/
local macro "cov_inst " C:term : tactic => `(tactic| (
  letI : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).algT1
  haveI : IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K ($C).L := ($C).towT1
  letI : Algebra (T0 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).algT0
  haveI : IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).towT0
  letI : Algebra (T01 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).algT01
  haveI : IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) (T01 (ε * ϖ ^ m) b₄ t κ) ($C).L :=
    Cov.towT01 $C
  letI : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) ($C).B₁ := ($C).algB₁
  haveI : IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) ($C).B₁ ($C).L := ($C).towB₁
  haveI : IsIntegralClosure ($C).B₁ (T1 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).intB₁
  haveI : IsLocalization.Away (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) ($C).B₁
    (DT (ε * ϖ ^ m) b₄ t κ)) ($C).Bn := ($C).locBn
  letI : Algebra (T0 (ε * ϖ ^ m) b₄ t κ) ($C).B₀ := ($C).algB₀
  haveI : IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) ($C).B₀ ($C).L := ($C).towB₀
  haveI : IsIntegralClosure ($C).B₀ (T0 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).intB₀
  haveI : IsLocalization.Away (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) ($C).B₀
    (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ)) ($C).Bc := ($C).locBc))

set_option hygiene false in
/-- `datumHom` with the fixed Tate data of this section. -/
local notation "𝔥" f:max => datumHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ f

set_option hygiene false in
/-- The datum of a cover, with the fixed Tate data of this section. -/
local notation "𝔇" C:max => datum hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C

set_option maxHeartbeats 1000000 in
-- the node chart data of two covers
/-- **I5(b): the special-fibre datum of a map of covers is balanced at the nodes.** -/
theorem covBalanced_datumHom {C C' : Cov ϖ b₄ b₆ t κ ε m hκ q e K} [CovRational θ M' C]
    [CovRational θ M' C'] (f : C.L →ₐ[K] C'.L) :
    CovBalanced hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ (C := C) (C' := C')
      (𝔥 f) := by
  cov_inst C
  cov_inst C'
  haveI := TateGlue1.isFractionRing_NR hϖ hκ hε h3 hE K hK
  haveI := TateGlue1.isIntegralClosure_B hϖ hκ hε K hK C.L C.B₁ C.Bn
  haveI := TateGlue1.isIntegralClosure_B hϖ hκ hε K hK C'.L C'.B₁ C'.Bn
  have hcomp := FormalKummer.quotHom_comp_eq (J θ (R := NR b₄ b₆ ϖ m ε))
    (TateS5.sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ C.hL C.hBn C.hunr₁ τ).ι₀
    (TateS5.sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ C'.hL C'.hBn C'.hunr₁ τ).ι₀
    (algebraMap C.B₁ C.Bn) (algebraMap C'.B₁ C'.Bn) (fun _ ↦ rfl) (fun _ ↦ rfl) (CovData.map1 f)
        (𝔥 f).f₁ (fun _ ↦ rfl)
    (IsIntegralClosure.intMap (B := C.Bn) (B' := C'.Bn) (f.restrictScalars (NR b₄ b₆ ϖ m ε)))
    (IsIntegralClosure.intMap_algebraMap _ _ (CovData.algebraMap_map1 f))
  unfold CovBalanced
  exact TateGlue1.balanced_of_quotHom hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ C.L C.hL C.B₁
    C.Bn C.hBn C.hunr₁ C'.L C'.hL C'.B₁ C'.Bn C'.hBn C'.hunr₁ (TateS5.θ_pow hker) τ _ _ hcomp

/-- **An endomorphism of the special-fibre datum of a tame cover comes from `Gal(C.L/K)` iff it
is balanced** (I3 surjectivity `mem_mrange_galHom` and I5(b) `covBalanced_datumHom`). -/
theorem mem_mrange_galHom_iff [IsAdicComplete (Ideal.span {ϖ}) O] (h2 : (2 : k) ≠ 0)
    (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) [CovRational θ M' C]
    (F : Datum.Hom (𝔇 C) (𝔇 C)) :
    F ∈ MonoidHom.mrange (galHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C) ↔
      CovBalanced hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ F := by
  refine ⟨fun h ↦ ?_, mem_mrange_galHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀
    h2 C F⟩
  obtain ⟨σ, rfl⟩ := h
  simp only [galHom, MonoidHom.coe_mk, OneHom.coe_mk]
  exact covBalanced_datumHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ (C := C)
    (C' := C) (σ : C.L →ₐ[K] C.L)

/-- **The balanced automorphisms of the special-fibre datum of a tame cover**: the image of
`galHom`, which consists exactly of the balanced endomorphisms (`mem_autBal_iff`). -/
abbrev autBal (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) [CovRational θ M' C] :
    Submonoid (Datum.Hom (𝔇 C) (𝔇 C)) :=
  MonoidHom.mrange (galHom hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C)

theorem mem_autBal_iff [IsAdicComplete (Ideal.span {ϖ}) O] (h2 : (2 : k) ≠ 0)
    (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) [CovRational θ M' C]
    (F : Datum.Hom (𝔇 C) (𝔇 C)) :
    F ∈ autBal hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C ↔
      CovBalanced hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ F :=
  mem_mrange_galHom_iff hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ h2 C F

/-- **`Gal(C.L/K) ≃* Aut_bal(datum C)`** (`galEquiv`; the image of `galHom` is the set of balanced
endomorphisms, `mem_autBal_iff`). -/
def galEquivBal (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) [CovRational θ M' C] :
    (C.L ≃ₐ[K] C.L) ≃* autBal hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C :=
  galEquiv hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C

end Functor

end

end TateS6

end SemistableReduction
