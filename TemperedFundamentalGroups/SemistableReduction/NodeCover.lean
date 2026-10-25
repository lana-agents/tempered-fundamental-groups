/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.Purity
import TemperedFundamentalGroups.SemistableReduction.NodeCoverField
import TemperedFundamentalGroups.SemistableReduction.NodeCoverLocal
import TemperedFundamentalGroups.SemistableReduction.NodeCoverFunctionField

/-!
# Prime-to-`p` Galois covers at a node of arbitrary thickness (T2 S4)

This file assembles the lemma "S4-local" of the MR12 plan, the generalisation of [Mzk1] §3.12
to nodes `x y = s ^ M` of arbitrary thickness `M` (also `p ∣ M`, `p` the residue
characteristic), a special case of Kato's log purity theorem [MzkExt] Thm. 3.3 (with Lemmas 3.1,
3.2 and 4.2). Write `R_M` for the node of thickness `M` at its closed point, `K_M` for its
function field and `W_M` for its punctured spectrum. The proof runs through the regular node
`R_1` (`X Y = s`) via the Kummer map `x ↦ X ^ M`, `y ↦ Y ^ M`, which identifies `W_1` with the
preimage of `W_M` (`Node.eq_closedPoint_of_comap_kummer`) and `K_1 / K_M` with `K(T) / K(T ^ M)`
of degree `M` (`Node.finrank_adjoin_X_pow`).

* `NodeCover.etale_of_isUnramifiedAt`: **purity on `R_1`** (SGA 1, Exp. X, Cor. 3.2 / 3.3): the
  normalisation of `R_1` in a finite separable extension of `K_1` which is unramified over the
  punctured spectrum `W_1` is étale over `R_1`. Unconditional.
* `NodeCover.finrank_eq_one_of_split`: if moreover every finite étale `R_1`-algebra which is a
  domain is trivial (the property of a strictly henselian `R_1` used in step (2) of "S4-local";
  passed as the explicit hypothesis `hsplit`), the extension is trivial.
* `NodeCover.eq_adjoin_of_isGalois`: **the field step** (steps (3), (4)): a Galois subextension
  `L ⊆ K_1` of `K_M` of degree `e` prime to `q` (`M = q M'`, `K` containing a primitive
  `M'`-th root of unity) satisfies `e ∣ M'` and `L = K_M(T ^ n)`, `n = q (M' / e)`, i.e.
  `L = K(T ^ n)` (`NodeCover.restrictScalars_adjoin_pow`), the function field of the node of
  thickness `n = M / e`. Unconditional.
* `NodeCover.isIntegralClosure_adjoin_pow`: **step (4), normalisation**: the integral closure of
  `R_M` (thickness `n e`) in `K(T ^ n)` is the node of thickness `n` (via `Node.kummer`;
  `Node.kummer_isIntegralClosure` transported to the function field `K(T ^ n)`). Unconditional.
* `NodeCover.finrank_eq_one_of_split_node`: step (2) for the regular node `R_1`: under `hsplit`,
  a finite separable extension `L₁` of `K_1` whose normalisation over `R_1` is unramified over
  `W_1` is trivial; with `NodeCover.eq_adjoin_of_isGalois` every Galois subextension of
  `L₁ / K_M` of degree prime to `q` is `K_M(T ^ n)`, `n = M / [L : K_M]`, `[L : K_M] ∣ M'`.

## The remaining inputs

* `hsplit` (strict henselianity of `R_1`): Lean has no strict henselisation; the Zariski local
  ring `R_1` itself does not satisfy `hsplit`.
* The base change step of (1): for an extension `L / K_M` whose normalisation over `R_M` is
  étale over `W_M`, the normalisation of `R_1` in the compositum `L K_1` is unramified over
  `W_1` (étale base change and normality) is not formalised here;
  `NodeCover.finrank_eq_one_of_split_node` takes the unramifiedness over `W_1` as its
  hypothesis `hunr`.

## References

* [SGA 1] A. Grothendieck, *Revêtements étales et groupe fondamental*, Exp. X, Cor. 3.2, 3.3.
* [MzkExt] S. Mochizuki, *Extending families of curves over log regular schemes*, J. reine angew.
  Math. 511 (1999), Thm. 3.3, Lemmas 3.1, 3.2, 4.2.
* [Mzk1] S. Mochizuki, *Semi-graphs of anabelioids*, §3.12, §3.13.
-/

open IsLocalRing IntermediateField Module

universe v

namespace SemistableReduction.NodeCover

section Purity

variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  {B : Type v} [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
  [IsIntegralClosure B A L]

omit [IsNoetherianRing A] [IsIntegrallyClosed A] [FiniteDimensional K L] in
variable (K L) in
include K L in
/-- If the normalisation `B` of `A` in a finite extension `L` of `K = Frac A` is trivial
(`A → B` surjective), then `L = K`. -/
theorem finrank_eq_one_of_surjective (h : Function.Surjective (algebraMap A B)) :
    finrank K L = 1 := by
  have := IsIntegralClosure.isLocalization A K L B
  rw [finrank_eq_one_iff_of_nonzero' (1 : L) one_ne_zero]
  intro z
  obtain ⟨⟨b, _, m, hm, rfl⟩, hz⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B
    (nonZeroDivisors A)) z
  obtain ⟨a, rfl⟩ := h b
  have hm0 : algebraMap A L m ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L, map_ne_zero_iff _ (algebraMap K L).injective,
      map_ne_zero_iff _ (IsFractionRing.injective A K)]
    exact nonZeroDivisors.ne_zero hm
  refine ⟨algebraMap A K a / algebraMap A K m, ?_⟩
  simp only [← IsScalarTower.algebraMap_apply] at hz
  rw [Algebra.smul_def, mul_one, map_div₀, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, div_eq_iff hm0, hz]

variable (K L) in
include K L in
/-- **Covers of the punctured spectrum of a split `R_1`** (step (2) of "S4-local"). Let `A` be a
Noetherian integrally closed local domain with maximal ideal `(x, y)`, `x` prime, `y ∉ (x)` (e.g.
the regular node `R_1`), and let `L / Frac A` be finite separable such that the normalisation
`B` of `A` in `L` is unramified over the punctured spectrum. If every finite étale `A`-algebra
which is a domain is trivial (`hsplit`; this holds when `A` is strictly henselian), then
`L = Frac A`. -/
theorem finrank_eq_one_of_split {x y : A} (hx : Prime x) (hy : y ∉ Ideal.span {x})
    (hm : maximalIdeal A = Ideal.span {x, y})
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsUnramifiedAt A Q)
    (hsplit : ∀ (C : Type v) [CommRing C] [IsDomain C] [Algebra A C] [Module.Finite A C]
      [Algebra.Etale A C], Function.Surjective (algebraMap A C)) :
    finrank K L = 1 := by
  have : Algebra.Etale A B :=
    Purity.etale_of_isUnramifiedAt_of_maximalIdeal_eq_span_pair K L hx hy hm hunr
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : IsDomain B := Function.Injective.isDomain (algebraMap B L)
    (IsIntegralClosure.algebraMap_injective B A L)
  exact finrank_eq_one_of_surjective K L (hsplit B)

end Purity

section Node

open Node

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {s : O}
  (hs : Irreducible s)

include hs

/-- **Purity on the regular node `R_1`** (SGA 1, Exp. X, Cor. 3.2, case `dim = 2`; step (2) of
"S4-local"). Let `R` be the localization of the node `O[X, Y] ⧸ (X Y - s)` at its closed point
`(X, Y)`, `O` a discrete valuation ring with uniformizer `s`. The normalisation `B` of `R` in a
finite separable extension `L` of `Frac R` which is unramified over the punctured spectrum
`W_1 = Spec R ∖ {(X, Y)}` is étale over `R`. -/
theorem etale_of_isUnramifiedAt (R : Type*) [CommRing R] [Algebra (Node O s) R]
    [(closedPoint s s).IsPrime] [IsLocalization.AtPrime R (closedPoint s s)] [IsLocalRing R]
    (K L : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra B L] [IsScalarTower R B L]
    [IsIntegralClosure B R L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap R B) ≠ maximalIdeal R →
      Algebra.IsUnramifiedAt R Q) :
    Algebra.Etale R B := by
  have := ThicknessOne.isDomain R hs.ne_zero
  have := ThicknessOne.isNoetherianRing (s := s) R
  have := ThicknessOne.isIntegrallyClosed R hs.ne_zero
  have hm := ThicknessOne.maximalIdeal_eq (s := s) R
  exact Purity.etale_of_isUnramifiedAt_of_maximalIdeal_eq_span_pair K L
    (ThicknessOne.prime_u R hs) (ThicknessOne.v_notMem_span_u R hs) hm hunr

end Node

section Field

variable {O : Type*} [CommRing O] [IsDomain O]

local notation "K" => FractionRing O

/-- `K(T ^ M)(T ^ n) = K(T ^ n)` for `n ∣ M`. -/
theorem restrictScalars_adjoin_pow {M n : ℕ} (h : n ∣ M) :
    (K⟮(RatFunc.X : RatFunc K) ^ M⟯⟮(RatFunc.X : RatFunc K) ^ n⟯).restrictScalars K =
      K⟮(RatFunc.X : RatFunc K) ^ n⟯ := by
  rw [adjoin_simple_adjoin_simple]
  refine le_antisymm (adjoin_le_iff.mpr ?_) (adjoin.mono _ _ _ (by simp))
  rintro y (rfl | rfl)
  · obtain ⟨k, rfl⟩ := h
    rw [pow_mul]
    exact pow_mem (mem_adjoin_simple_self K _) k
  · exact mem_adjoin_simple_self K _

/-- **The field step of "S4-local"** (steps (3) and (4)). Let `M = q M'` with `0 < q, M'` and
let `K` contain a primitive `M'`-th root of unity. Every intermediate field `L` of
`K(T) / K(T ^ M)` which is Galois over `K(T ^ M)` of degree `e` prime to `q` satisfies `e ∣ M'`
and `L = K(T ^ M)(T ^ (q (M' / e)))`. -/
theorem eq_adjoin_of_isGalois {q M' : ℕ} (hq : 0 < q) (hM' : 0 < M') {ζ : K}
    (hζ : IsPrimitiveRoot ζ M')
    (L : IntermediateField K⟮(RatFunc.X : RatFunc K) ^ (q * M')⟯ (RatFunc K))
    [IsGalois K⟮(RatFunc.X : RatFunc K) ^ (q * M')⟯ L]
    (hL : Nat.Coprime (finrank K⟮(RatFunc.X : RatFunc K) ^ (q * M')⟯ L) q) :
    finrank K⟮(RatFunc.X : RatFunc K) ^ (q * M')⟯ L ∣ M' ∧
      L = K⟮(RatFunc.X : RatFunc K) ^ (q * M')⟯⟮(RatFunc.X : RatFunc K) ^
        (q * (M' / finrank K⟮(RatFunc.X : RatFunc K) ^ (q * M')⟯ L))⟯ := by
  have hE : finrank K⟮(RatFunc.X : RatFunc K) ^ (q * M')⟯ (RatFunc K) = q * M' :=
    Node.finrank_adjoin_X_pow _
  have : FiniteDimensional K⟮(RatFunc.X : RatFunc K) ^ (q * M')⟯ (RatFunc K) :=
    Module.finite_of_finrank_pos (by rw [hE]; positivity)
  exact eq_adjoin_pow_of_isGalois hq hM'
    (hζ.map_of_injective (algebraMap K K⟮(RatFunc.X : RatFunc K) ^ (q * M')⟯).injective)
    (x := ⟨_, mem_adjoin_simple_self K _⟩) rfl (Node.adjoin_X_eq_top _) hE L hL

variable {s : O} {n e : ℕ}

/-- **Normalisation in the Kummer subfield** (step (4) of "S4-local"). For `s ≠ 0` and
`0 < n, e`, the node `Node O (s ^ n)` (`u ↦ T ^ n`) is the integral closure of the node of
thickness `(s ^ n) ^ e` (via the Kummer map `u ↦ u ^ e`, `v ↦ v ^ e`) in `K(T ^ n)`. -/
theorem isIntegralClosure_adjoin_pow [IsIntegrallyClosed O] (hs : s ≠ 0) (hn : 0 < n)
    (he : 0 < e) :
    letI := Node.kummerAlgebra (s ^ n) e
    letI := Node.adjoinPowAlgebra s n
    letI : Algebra (Node O ((s ^ n) ^ e)) K⟮(RatFunc.X : RatFunc K) ^ n⟯ :=
      ((Node.toAdjoinPow s n).comp (Node.kummer (s ^ n) e).toRingHom).toAlgebra
    IsIntegralClosure (Node O (s ^ n)) (Node O ((s ^ n) ^ e)) K⟮(RatFunc.X : RatFunc K) ^ n⟯ := by
  letI := Node.kummerAlgebra (s ^ n) e
  letI := Node.adjoinPowAlgebra s n
  letI : Algebra (Node O ((s ^ n) ^ e)) K⟮(RatFunc.X : RatFunc K) ^ n⟯ :=
    ((Node.toAdjoinPow s n).comp (Node.kummer (s ^ n) e).toRingHom).toAlgebra
  have : IsScalarTower (Node O ((s ^ n) ^ e)) (Node O (s ^ n)) K⟮(RatFunc.X : RatFunc K) ^ n⟯ :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have := Node.isDomain (pow_ne_zero n hs)
  have := Node.isIntegrallyClosed (pow_ne_zero n hs)
  have := Node.isFractionRing_adjoin_pow hs hn
  have := Node.kummer_isIntegral (s ^ n) he
  exact IsIntegralClosure.of_isIntegrallyClosed _ _ _

end Field

section Assembly

open Node

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {s : O}

/-- **Step (2) of "S4-local" on the regular node, under `hsplit`.** Let `R` be the localization
of the node `O[X, Y] ⧸ (X Y - s)` at `(X, Y)` (`O` a discrete valuation ring with uniformizer
`s`), `L₁ / Frac R` finite separable such that the normalisation `B` of `R` in `L₁` is unramified
over the punctured spectrum `W_1`. If every finite étale `R`-algebra which is a domain is trivial
(`hsplit`, strict henselianity of `R`), then `L₁ = Frac R`. Together with
`NodeCover.eq_adjoin_of_isGalois` (applied to `Frac R = K(T)`, `Node.isFractionRing_ratFunc`) this
gives "S4-local": every Galois subextension of `L₁ / K(T ^ M)` of degree `e` prime to `q` is
`K(T ^ (M / e))`, `e ∣ M'`, whose normalisation is the node of thickness `M / e`
(`NodeCover.isIntegralClosure_adjoin_pow`). -/
theorem finrank_eq_one_of_split_node (hs : Irreducible s)
    (R : Type*) [CommRing R] [Algebra (Node O s) R] [(closedPoint s s).IsPrime]
    [IsLocalization.AtPrime R (closedPoint s s)] [IsLocalRing R]
    (K₁ : Type*) [Field K₁] [Algebra R K₁] [IsFractionRing R K₁]
    (L₁ : Type*) [Field L₁] [Algebra K₁ L₁] [Algebra R L₁]
    [IsScalarTower R K₁ L₁] [FiniteDimensional K₁ L₁] [Algebra.IsSeparable K₁ L₁]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra B L₁] [IsScalarTower R B L₁]
    [IsIntegralClosure B R L₁]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap R B) ≠ maximalIdeal R →
      Algebra.IsUnramifiedAt R Q)
    (hsplit : ∀ (C : Type v) [CommRing C] [IsDomain C] [Algebra R C] [Module.Finite R C]
      [Algebra.Etale R C], Function.Surjective (algebraMap R C)) :
    finrank K₁ L₁ = 1 := by
  have := ThicknessOne.isDomain R hs.ne_zero
  have := ThicknessOne.isNoetherianRing (s := s) R
  have := ThicknessOne.isIntegrallyClosed R hs.ne_zero
  exact finrank_eq_one_of_split K₁ L₁ (ThicknessOne.prime_u R hs)
    (ThicknessOne.v_notMem_span_u R hs) (ThicknessOne.maximalIdeal_eq (s := s) R) hunr hsplit

end Assembly

end SemistableReduction.NodeCover
