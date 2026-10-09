/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.AbhyankarInequality
import TemperedFundamentalGroups.SemistableReduction.ChartLocalization
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization

/-!
# Domination of models with nested vertex sets (M10)

Blueprint §9.6 (W5), §9.12 (O5/O7 sub-obligation M10). Let `O` be a discrete valuation ring of
`K`, `F / K` a field of transcendence degree `≤ 1`, `X` a proper separated normal Zariski model
of finite type over `O` whose charts have fraction field `F`, and `Y` a proper Zariski model of
finite type (not necessarily normal). If every valuation `W` of `F` over `O` whose center on `Y`
has residue field transcendental over `κ(O)` (the local rings of `Y` at the generic points of the
components of its special fibre) is a vertex of `X`, then `X` dominates `Y`: every local ring of
`X` contains a chart of `Y` (`ZariskiModel.dominates_of_vertexSet_subset`).

Proof (valuative, via Mathlib's algebraic Zariski main theorem). Let `A = O_P` be a point of `X`,
`W₀` a valuation subring dominating it, `B = R[s] ⊆ W₀` a chart of `Y` (properness), and
`C = A[s]`, of finite type over the noetherian normal local ring `A`.
* If `C` is quasi-finite over `A` at the center `q` of `W₀`, Zariski's main theorem gives
  `r ∉ q` integral over `A` with every `r^m x` (`x ∈ C`) integral over `A`; as `A` is normal,
  `r` is a unit of `A` and `C = A`, so `B ⊆ A` (`le_of_quasiFiniteAt`).
* Otherwise some prime `Q` of `C` over `𝔪_A` is not maximal
  (`quasiFiniteAt_of_forall_isMaximal`: a fibre of maximal primes is finite and discrete), so
  `C / Q` is not algebraic over `κ(A)` and some generator `z ∈ s` is transcendental modulo `Q`
  (`exists_forall_aeval_notMem_of_not_isMaximal`). A valuation subring `W` dominating `C_Q`
  dominates `A`. If `P` lies on the special fibre, `W ∩ K = O` and `z` has transcendental residue,
  so `W` is a vertex of `X`; then `A = W ⊇ B`. If `P` lies on the generic fibre, `W` is trivial
  on `K`, has transcendental residue field and is nontrivial on `A`, contradicting
  `trdeg_K F ≤ 1` (`false_of_trdeg_le_one`).
-/

open Polynomial IsLocalRing Cardinal

namespace SemistableReduction

/-! ### Commutative algebra -/

section Algebra

/-- If every prime in the fibre through `q` is maximal, then the (noetherian, finite type)
`R`-algebra `S` is quasi-finite at `q`: the fibre is finite (its points are minimal over
`(q ∩ R) S`) and consists of closed points, hence is discrete. -/
theorem quasiFiniteAt_of_forall_isMaximal {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [IsNoetherianRing S] (q : Ideal S) [q.IsPrime]
    (h : ∀ Q : Ideal S, Q.IsPrime → Q.comap (algebraMap R S) = q.comap (algebraMap R S) →
      Q.IsMaximal) : Algebra.QuasiFiniteAt R q := by
  let qq : PrimeSpectrum S := ⟨q, inferInstance⟩
  refine (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber qq).2 ?_
  set Fb := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {PrimeSpectrum.comap (algebraMap R S) qq}
  set I : Ideal S := (q.comap (algebraMap R S)).map (algebraMap R S)
  have hmem : ∀ x : Fb, x.1.asIdeal.comap (algebraMap R S) = q.comap (algebraMap R S) :=
    fun x ↦ congrArg PrimeSpectrum.asIdeal x.2
  have hmax : ∀ x : Fb, x.1.asIdeal.IsMaximal := fun x ↦ h _ x.1.2 (hmem x)
  have hmin : ∀ x : Fb, x.1.asIdeal ∈ I.minimalPrimes := by
    intro x
    have hle : I ≤ x.1.asIdeal := by
      rw [Ideal.map_le_iff_le_comap, hmem x]
    refine ⟨⟨x.1.2, hle⟩, fun J ⟨hJ, hIJ⟩ hJx ↦ ?_⟩
    have hc : J.comap (algebraMap R S) = q.comap (algebraMap R S) := by
      refine le_antisymm ?_ ?_
      · rw [← hmem x]; exact Ideal.comap_mono hJx
      · rw [← Ideal.map_le_iff_le_comap]; exact hIJ
    exact ((h J hJ hc).eq_of_le x.1.2.ne_top hJx).ge
  haveI : Finite Fb := by
    have := (Ideal.finite_minimalPrimes_of_isNoetherianRing S I).to_subtype
    refine Finite.of_injective (β := I.minimalPrimes) (fun x ↦ ⟨x.1.asIdeal, hmin x⟩) ?_
    intro x y hxy
    exact Subtype.ext (PrimeSpectrum.ext (congrArg Subtype.val hxy))
  haveI : T1Space Fb := by
    refine ⟨fun x ↦ ?_⟩
    have hx : IsClosed ({x.1} : Set (PrimeSpectrum S)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (hmax x)
    have := hx.preimage (continuous_subtype_val (p := (· ∈ Fb)))
    convert this using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact Subtype.ext_iff
  exact isOpen_discrete _

/-- If `S = R[t]` and `Q` is a non-maximal prime of `S` lying over a maximal ideal of `R`, some
generator `z ∈ t` is transcendental modulo `Q` over the residue field of `R`: no polynomial with a
coefficient outside `Q ∩ R` vanishes at `z` modulo `Q`. (Otherwise `S / Q` is integral over the
field `R / (Q ∩ R)`, hence a field.) -/
theorem exists_forall_aeval_notMem_of_not_isMaximal {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (t : Set S) (ht : Algebra.adjoin R t = ⊤) (Q : Ideal S) [Q.IsPrime]
    (hmax : (Q.comap (algebraMap R S)).IsMaximal) (hQm : ¬ Q.IsMaximal) :
    ∃ z ∈ t, ∀ p : R[X], (∃ i, p.coeff i ∉ Q.comap (algebraMap R S)) → aeval z p ∉ Q := by
  set m := Q.comap (algebraMap R S)
  letI : Algebra (R ⧸ m) (S ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap le_rfl
  by_contra! H
  have hint : ∀ y ∈ (Ideal.Quotient.mk Q) '' t, IsIntegral (R ⧸ m) y := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨p, ⟨i, hi⟩, hp⟩ := H z hz
    have hF : IsField (R ⧸ m) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hmax
    letI := hF.toField
    have halg : IsAlgebraic (R ⧸ m) (Ideal.Quotient.mk Q z) := by
      refine ⟨p.map (Ideal.Quotient.mk m), fun h0 ↦ ?_, ?_⟩
      · have := congrArg (coeff · i) h0
        simp only [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem] at this
        exact hi this
      · rw [aeval_def, eval₂_map]
        change eval₂ ((Ideal.quotientMap Q (algebraMap R S) le_rfl).comp
          (Ideal.Quotient.mk m)) _ p = 0
        rw [Ideal.quotientMap_comp_mk, ← hom_eval₂, ← aeval_def, Ideal.Quotient.eq_zero_iff_mem]
        exact hp
    exact halg.isIntegral
  have htop : ∀ y : S ⧸ Q, y ∈ Algebra.adjoin (R ⧸ m) ((Ideal.Quotient.mk Q) '' t) := by
    rintro ⟨c⟩
    change Ideal.Quotient.mk Q c ∈ _
    have hc : c ∈ Algebra.adjoin R t := ht ▸ Algebra.mem_top
    induction hc using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap a =>
      have : Ideal.Quotient.mk Q (algebraMap R S a) =
          algebraMap (R ⧸ m) (S ⧸ Q) (Ideal.Quotient.mk m a) := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add x y hx hy ihx ihy => simpa using Subalgebra.add_mem _ ihx ihy
    | mul x y hx hy ihx ihy => simpa using Subalgebra.mul_mem _ ihx ihy
  haveI := Algebra.IsIntegral.adjoin hint
  haveI : Algebra.IsIntegral (R ⧸ m) (S ⧸ Q) :=
    ⟨fun y ↦ (Algebra.IsIntegral.isIntegral (R := R ⧸ m) (⟨y, htop y⟩ :
        Algebra.adjoin (R ⧸ m) ((Ideal.Quotient.mk Q) '' t))).map (Subalgebra.val _)⟩
  have hF : IsField (R ⧸ m) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hmax
  letI := hF.toField
  have hfield : IsField (S ⧸ Q) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap (R ⧸ m) (S ⧸ Q)).injective).1 hF
  exact hQm (Ideal.Quotient.maximal_of_isField Q hfield)

end Algebra

/-! ### Transcendence degree one -/

/-- If `trdeg_K F ≤ 1`, a valuation subring `W` of `F` in which some `z` has residue
transcendental over `K` (every nonzero `p(z)`, `p ∈ K[X]`, is a `W`-unit) is trivial on `F`: no
nonzero `a` has `W(a) < 1`. Otherwise `z` and `a` are algebraically independent over `K` (in
`Σ cⱼ(z) aʲ` the terms have the distinct values `W(a)ʲ`). -/
theorem false_of_trdeg_le_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hF : Algebra.trdeg K F ≤ 1) (W : ValuationSubring F) {z a : F}
    (hz : ∀ p : K[X], p ≠ 0 → W.valuation (aeval z p) = 1) (ha0 : a ≠ 0)
    (ha : W.valuation a < 1) : False := by
  set xs : Unit → F := fun _ ↦ z
  have hind : AlgebraicIndependent K xs := by
    refine algebraicIndependent_unique_type_iff.2 fun ⟨p, hp0, hp⟩ ↦ ?_
    have := hz p hp0
    rw [hp, map_zero] at this
    exact zero_ne_one this
  have hwa : W.valuation a ≠ 0 := by simpa using ha0
  have htrans : Transcendental (Algebra.adjoin K (Set.range xs)) a := by
    rintro ⟨Q, hQ0, hQa⟩
    have hval : ∀ j ∈ Q.support, W.valuation (Q.coeff j : F) = 1 := by
      intro j hj
      have hmem : (Q.coeff j : F) ∈ (aeval (R := K) z).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]
        have : Set.range xs = {z} := Set.range_const
        rw [← this]
        exact (Q.coeff j).2
      obtain ⟨p, hp⟩ := (AlgHom.mem_range _).1 hmem
      have hp0 : p ≠ 0 := by
        rintro rfl
        rw [map_zero, eq_comm, ZeroMemClass.coe_eq_zero] at hp
        exact Polynomial.mem_support_iff.1 hj hp
      rw [← hp]
      exact hz p hp0
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hQa
    refine sum_ne_zero_of_valuation_ne (w := W.valuation)
      (Polynomial.support_nonempty.2 hQ0) _ ?_ ?_ hQa
    · intro j hj
      change W.valuation ((Q.coeff j : F) * a ^ j) ≠ 0
      rw [map_mul, map_pow, hval j hj, one_mul]
      exact pow_ne_zero _ hwa
    · have key : ∀ j k : ℕ, j < k → W.valuation a ^ j ≠ W.valuation a ^ k := by
        intro j k hjk heq
        have hk : W.valuation a ^ k = W.valuation a ^ j * W.valuation a ^ (k - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hjk.le]
        rw [hk] at heq
        have h1 : W.valuation a ^ (k - j) = 1 :=
          (mul_eq_left₀ (pow_ne_zero _ hwa)).1 heq.symm
        exact (pow_lt_one₀ zero_le ha (Nat.sub_pos_of_lt hjk).ne').ne h1
      intro j hj k hk hjk
      change W.valuation ((Q.coeff j : F) * a ^ j) ≠ W.valuation ((Q.coeff k : F) * a ^ k)
      rw [map_mul, map_pow, map_mul, map_pow, hval j hj, hval k hk, one_mul, one_mul]
      rcases Nat.lt_or_gt_of_ne hjk with h | h
      · exact key j k h
      · exact (key k j h).symm
  have hpair := (AlgebraicIndependent.option_iff (x := xs) (a := a)).2 ⟨hind, htrans⟩
  have hcard := hpair.lift_cardinalMk_le_trdeg
  have h2 : lift.{0} (Algebra.trdeg K F) ≤ 1 := by simpa using hF
  have := hcard.trans h2
  simp at this

/-! ### Subrings of `F` -/

section Subring

variable {F : Type*} [Field F]

/-- The center of `W` on `A[s]`, as an ideal of the subalgebra. -/
def adjCenter (A : Subring F) (s : Finset F) (W : ValuationSubring F)
    (h : (Algebra.adjoin A (s : Set F)).toSubring ≤ W.toSubring) :
    Ideal (Algebra.adjoin A (s : Set F)) :=
  centerIdeal (Algebra.adjoin A (s : Set F)).toSubring W h

instance (A : Subring F) (s : Finset F) (W : ValuationSubring F)
    (h : (Algebra.adjoin A (s : Set F)).toSubring ≤ W.toSubring) : (adjCenter A s W h).IsPrime :=
  inferInstanceAs (centerIdeal _ W h).IsPrime

lemma mem_adjCenter {A : Subring F} {s : Finset F} {W : ValuationSubring F}
    {h : (Algebra.adjoin A (s : Set F)).toSubring ≤ W.toSubring}
    (c : Algebra.adjoin A (s : Set F)) :
    c ∈ adjCenter A s W h ↔ W.valuation (c : F) < 1 :=
  mem_centerIdeal_iff h c

/-- **Zariski's main theorem, birational form.** Let `A ⊆ F` be integrally closed in `F`, with
the `W`-units of `A` invertible in `A` (a local ring dominated by `W`). If `A[s] ⊆ W` is
quasi-finite over `A` at the center of `W`, then `A[s] = A`. -/
theorem le_of_quasiFiniteAt {A : Subring F} (hA : ∀ x : F, IsIntegral A x → x ∈ A)
    {W : ValuationSubring F} (hunit : ∀ a ∈ A, W.valuation a = 1 → a⁻¹ ∈ A) (s : Finset F)
    (h : (Algebra.adjoin A (s : Set F)).toSubring ≤ W.toSubring)
    [Algebra.QuasiFiniteAt A (adjCenter A s W h)] :
    ∀ x ∈ Algebra.adjoin A (s : Set F), x ∈ A := by
  set C := Algebra.adjoin A (s : Set F)
  haveI : Algebra.FiniteType A C :=
    (Subalgebra.fg_iff_finiteType C).1 (Subalgebra.fg_adjoin_finset s)
  obtain ⟨r, hr, hri, hm⟩ := Algebra.zariskisMainProperty_iff.1
    (Algebra.ZariskisMainProperty.of_finiteType (R := A) (S := C)
      (adjCenter A s W h))
  have hrA : (r : F) ∈ A := hA _ (hri.map (IsScalarTower.toAlgHom A C F))
  have hrv : W.valuation (r : F) = 1 := by
    rw [mem_adjCenter, not_lt] at hr
    exact le_antisymm ((W.valuation_le_one_iff _).2 (h r.2)) hr
  have hr0 : (r : F) ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hrv
    exact zero_ne_one hrv
  have hrinv := hunit _ hrA hrv
  intro x hx
  obtain ⟨m, hmx⟩ := hm ⟨x, hx⟩
  have hxA : (r : F) ^ m * x ∈ A := hA _ (hmx.map (IsScalarTower.toAlgHom A C F))
  have : x = (r : F)⁻¹ ^ m * ((r : F) ^ m * x) := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hr0, one_pow, one_mul]
  rw [this]
  exact A.mul_mem (A.pow_mem hrinv m) hxA

/-- `A[s]`, as a subring: the subring generated by `A` and `s`. -/
lemma toSubring_adjoin_eq_closure (A : Subring F) (s : Set F) :
    (Algebra.adjoin A s).toSubring = Subring.closure ((A : Set F) ∪ s) := by
  rw [Algebra.adjoin_eq_ring_closure]
  congr
  ext x
  exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- The generators of `A[s]`, as elements of the subalgebra, generate it. -/
lemma adjoin_preimage_eq_top (A : Subring F) (s : Set F) :
    Algebra.adjoin A {z : Algebra.adjoin A s | (z : F) ∈ s} = ⊤ := by
  apply Subalgebra.map_injective (f := (Algebra.adjoin A s).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  congr
  ext x
  exact ⟨fun ⟨z, hz, h⟩ ↦ h ▸ hz, fun hx ↦ ⟨⟨x, Algebra.subset_adjoin hx⟩, hx, rfl⟩⟩

end Subring

/-! ### Domination -/

section Domination

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {O : ValuationSubring K}

/-- A valuation subring of `F` over the discrete valuation ring `O` in which a uniformizer is not
a unit restricts to `O` on `K`. -/
lemma comap_eq_of_valuation_lt_one [IsDiscreteValuationRing O] {W : ValuationSubring F}
    (hW : baseRing F O ≤ W.toSubring) {ϖ : O} (hϖ : Irreducible ϖ)
    (hϖW : W.valuation (algebraMap K F ϖ) < 1) : W.comap (algebraMap K F) = O := by
  refine le_antisymm (fun x hx ↦ ?_) (baseRing_le_iff.1 hW)
  by_contra hxO
  have hxi : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
  have hx0 : x ≠ 0 := by rintro rfl; exact hxO O.zero_mem
  have hxi0 : (⟨x⁻¹, hxi⟩ : O) ≠ 0 := fun h ↦ hx0 (inv_eq_zero.1 (congrArg Subtype.val h))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxi0 hϖ
  have hu' : x⁻¹ = (u : O) * (ϖ : K) ^ n := by
    simpa using congrArg Subtype.val hu
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · apply hxO
    have : x = ((u⁻¹ : Oˣ) : O) := by
      rw [← inv_inv x, hu', pow_zero, mul_one]
      exact (eq_inv_of_mul_eq_one_left (by
        rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl)).symm
    rw [this]
    exact Subtype.prop _
  · have huW : W.valuation (algebraMap K F (u : O)) = 1 := by
      have hu0 : ((u : O) : K) ≠ 0 := by simp
      have hui : ((u : O) : K)⁻¹ = ((u⁻¹ : Oˣ) : O) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hu0]
        exact congrArg Subtype.val (Units.inv_mul u)
      refine (valuation_eq_one_iff_mem_and_inv_mem W).2 ⟨by simp,
        hW (algebraMap_mem_baseRing (u : O).2), ?_⟩
      rw [← map_inv₀, hui]
      exact hW (algebraMap_mem_baseRing (Subtype.prop _))
    have hlt : W.valuation (algebraMap K F x⁻¹) < 1 := by
      rw [hu', map_mul, map_mul, huW, one_mul, map_pow, map_pow]
      exact pow_lt_one₀ zero_le hϖW hn.ne'
    have h1 : W.valuation (algebraMap K F x⁻¹) = 1 := by
      refine (valuation_eq_one_iff_mem_and_inv_mem W).2 ⟨by simpa using hx0,
        hW (algebraMap_mem_baseRing hxi), ?_⟩
      rw [← map_inv₀, inv_inv]
      exact hx
    exact absurd h1 hlt.ne

/-- The local rings of a model of finite type over a discrete valuation ring are noetherian. -/
lemma isNoetherianRing_localAt [IsDiscreteValuationRing O] {A₀ : Subring F}
    (hA₀ : ∃ s : Finset F, A₀ = Subring.closure ((baseRing F O : Set F) ∪ s))
    {W : ValuationSubring F} (hA₀W : A₀ ≤ W.toSubring) : IsNoetherianRing (localAt A₀ W) := by
  obtain ⟨s, rfl⟩ := hA₀
  set R := baseRing F O
  haveI : IsNoetherianRing R := by
    haveI : IsNoetherianRing O.toSubring := inferInstanceAs (IsNoetherianRing O)
    exact isNoetherianRing_of_ringEquiv _
      (O.toSubring.equivMapOfInjective (algebraMap K F) (algebraMap K F).injective)
  haveI : IsNoetherianRing (Algebra.adjoin R (s : Set F)) :=
    isNoetherianRing_of_fg (Subalgebra.fg_adjoin_finset s)
  haveI : IsNoetherianRing (Subring.closure ((baseRing F O : Set F) ∪ s)) :=
    isNoetherianRing_of_ringEquiv _
      (RingEquiv.subringCongr (toSubring_adjoin_eq_closure R (s : Set F)))
  rw [localAt_eq_localSubringOfPrime hA₀W]
  exact IsLocalization.isNoetherianRing (centerIdeal _ W hA₀W).primeCompl _ inferInstance

/-- Units of a subring `A ⊆ W` are `W`-units. -/
lemma valuation_coe_eq_one_of_isUnit {W : ValuationSubring F} {A : Subring F}
    (hAW : A ≤ W.toSubring) {x : A} (hx : IsUnit x) : W.valuation (x : F) = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 : ((u : A) : F) * ((u⁻¹ : Aˣ) : A) = 1 := congrArg Subtype.val u.mul_inv
  have h0 : ((u : A) : F) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  refine valuation_eq_one_of_mem_of_inv_mem h0 (hAW (u : A).2) ?_
  rw [inv_eq_of_mul_eq_one_right h1]
  exact hAW (Subtype.prop _)

/-- Evaluating `p` at `z ∈ F` after mapping the coefficients along `ψ : S → A ⊆ F`. -/
lemma aeval_map_codRestrict {S : Type*} [CommRing S] [Algebra S F] {A : Subring F}
    (h : ∀ x : S, algebraMap S F x ∈ A) (p : S[X]) (z : F) :
    aeval z (p.map ((algebraMap S F).codRestrict A h)) = aeval z p := by
  rw [aeval_def, aeval_def, eval₂_map]
  rfl

variable [IsDiscreteValuationRing O]

/-- **M10: domination of models with nested vertex sets.** Let `X` be a separated normal Zariski
model of finite type over the discrete valuation ring `O` whose charts have fraction field `F`
(`trdeg_K F ≤ 1`), and `Y` a proper Zariski model of finite type. If every valuation subring `W`
of `F` with `W ∩ K = O` whose center on `Y` has residue field transcendental over `κ(O)` (some
element `z` of a chart `B ⊆ W` of `Y` has transcendental residue: `W` dominates the local ring of
`Y` at the generic point of a component of the special fibre) is a vertex of `X`, then `X`
dominates `Y`: every local ring of `X` contains a chart of `Y`. -/
theorem ZariskiModel.dominates_of_vertexSet_subset (hF : Algebra.trdeg K F ≤ 1)
    {X Y : ZariskiModel (baseRing F O)} (hXs : X.IsSeparated) (hXn : X.IsNormal)
    (hXf : X.IsFiniteType) (hXF : ∀ A ∈ X.charts, ∀ x : F, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x = a / b)
    (hY : Y.IsProper) (hYf : Y.IsFiniteType)
    (hV : ∀ W : ValuationSubring F, W.comap (algebraMap K F) = O → ∀ B ∈ Y.charts,
      B ≤ W.toSubring → ∀ z ∈ B, IsResidueTranscendental O W z → W ∈ X.vertexSet) :
    ∀ P ∈ X.points, ∃ B ∈ Y.charts, B ≤ P := by
  rintro _ ⟨A₀, hA₀, W₀, hA₀W₀, rfl⟩
  set A := localAt A₀ W₀
  have hAW₀ : A ≤ W₀.toSubring := localAt_le hA₀W₀
  have hA₀A : A₀ ≤ A := le_localAt
  have hRA : baseRing F O ≤ A := (X.le_chart A₀ hA₀).trans hA₀A
  have hAint : ∀ x : F, IsIntegral A x → x ∈ A := fun x hx ↦ isIntegral_mem_localAt (hXn A₀ hA₀) hx
  have hunit : ∀ a ∈ A, W₀.valuation a = 1 → a⁻¹ ∈ A := fun a ha hv ↦ inv_mem_localAt_of_mem ha hv
  haveI : IsNoetherianRing A := isNoetherianRing_localAt (hXf A₀ hA₀) hA₀W₀
  obtain ⟨B, hB, hBW₀⟩ := hY W₀ (hRA.trans hAW₀)
  obtain ⟨s, rfl⟩ := hYf B hB
  refine ⟨_, hB, ?_⟩
  have hBA : (∀ x ∈ s, x ∈ A) → Subring.closure ((baseRing F O : Set F) ∪ s) ≤ A := fun h ↦
    Subring.closure_le.2 (Set.union_subset hRA fun x hx ↦ h x hx)
  have hCeq := toSubring_adjoin_eq_closure A (s : Set F)
  have hsW₀ : ∀ x ∈ s, x ∈ W₀ := fun x hx ↦ hBW₀ (Subring.subset_closure (Or.inr hx))
  have hCW₀ : (Algebra.adjoin A (s : Set F)).toSubring ≤ W₀.toSubring := by
    rw [hCeq]
    exact Subring.closure_le.2 (Set.union_subset hAW₀ fun x hx ↦ hsW₀ x hx)
  have hAC : A ≤ (Algebra.adjoin A (s : Set F)).toSubring := by
    rw [hCeq]
    exact fun x hx ↦ Subring.subset_closure (Or.inl hx)
  have hBC : Subring.closure ((baseRing F O : Set F) ∪ s) ≤
      (Algebra.adjoin A (s : Set F)).toSubring := by
    rw [hCeq]
    exact Subring.closure_mono (Set.union_subset_union_left _ hRA)
  haveI : Algebra.FiniteType A (Algebra.adjoin A (s : Set F)) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
  haveI : IsNoetherianRing (Algebra.adjoin A (s : Set F)) :=
    Algebra.FiniteType.isNoetherianRing A _
  -- Case 1: quasi-finite, Zariski's main theorem
  by_cases hq : Algebra.QuasiFiniteAt A (adjCenter A s W₀ hCW₀)
  · exact hBA fun x hx ↦ le_of_quasiFiniteAt hAint hunit s hCW₀ x (Algebra.subset_adjoin hx)
  -- Case 2: a non-maximal prime in the closed fibre
  obtain ⟨Q, hQp, hQc, hQm⟩ : ∃ Q : Ideal (Algebra.adjoin A (s : Set F)), Q.IsPrime ∧
      Q.comap (algebraMap A _) = (adjCenter A s W₀ hCW₀).comap (algebraMap A _) ∧
      ¬ Q.IsMaximal := by
    by_contra! H
    exact hq (quasiFiniteAt_of_forall_isMaximal _ fun Q hQ hc ↦ H Q hQ hc)
  have hm : ∀ a : A, algebraMap A _ a ∈ Q ↔ W₀.valuation (a : F) < 1 := fun a ↦ by
    rw [← Ideal.mem_comap, hQc, Ideal.mem_comap, mem_adjCenter]
    rfl
  have hmax : (Q.comap (algebraMap A (Algebra.adjoin A (s : Set F)))).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 ↦ ?_, fun J x hmJ hx hxJ ↦ ?_⟩
    · have := (hm 1).1 h1
      simp at this
    · have hv : W₀.valuation (x : F) = 1 := le_antisymm
        ((W₀.valuation_le_one_iff _).2 (hAW₀ x.2)) (not_lt.1 ((hm x).not.1 hx))
      have hx0 : (x : F) ≠ 0 := fun h0 ↦ by simp [h0] at hv
      have : (1 : A) = ⟨_, hunit _ x.2 hv⟩ * x := Subtype.ext (by simp [inv_mul_cancel₀ hx0])
      rw [this]
      exact J.mul_mem_left _ hxJ
  obtain ⟨z, hzs, hz⟩ := exists_forall_aeval_notMem_of_not_isMaximal _
    (adjoin_preimage_eq_top A (s : Set F)) Q hmax hQm
  obtain ⟨W, hCW, hWQ⟩ := exists_centerIdeal_eq (Algebra.adjoin A (s : Set F)).toSubring Q
  have hWA : ∀ a ∈ A, W.valuation a < 1 ↔ W₀.valuation a < 1 := fun a ha ↦ by
    rw [← hm ⟨a, ha⟩, ← hWQ, mem_centerIdeal_iff]
    rfl
  have hAW : A ≤ W.toSubring := hAC.trans hCW
  have hloc : localAt A₀ W = A := by
    have key : ∀ t ∈ A₀, W.valuation t = 1 ↔ W₀.valuation t = 1 := fun t ht ↦ by
      have htA : t ∈ A := hA₀A ht
      have h1 := (W.valuation_le_one_iff t).2 (hAW htA)
      have h2 := (W₀.valuation_le_one_iff t).2 (hAW₀ htA)
      have e1 : W.valuation t = 1 ↔ ¬ W.valuation t < 1 :=
        ⟨fun h ↦ h ▸ lt_irrefl _, fun h ↦ le_antisymm h1 (not_lt.1 h)⟩
      have e2 : W₀.valuation t = 1 ↔ ¬ W₀.valuation t < 1 :=
        ⟨fun h ↦ h ▸ lt_irrefl _, fun h ↦ le_antisymm h2 (not_lt.1 h)⟩
      rw [e1, e2, hWA t htA]
    ext x
    simp only [mem_localAt]
    exact exists_congr fun t ↦ and_congr_right fun ht ↦ and_congr_left' (key t ht)
  -- `z` has transcendental residue in `W`
  have hzW : ∀ p : A[X], (∃ i, IsUnit (p.coeff i)) → W.valuation (aeval (z : F) p) = 1 := by
    rintro p ⟨i, hi⟩
    have hnot := hz p ⟨i, fun h ↦ by
      have := (hm _).1 h
      rw [valuation_coe_eq_one_of_isUnit hAW₀ hi] at this
      exact lt_irrefl _ this⟩
    rw [← hWQ, mem_centerIdeal_iff, not_lt] at hnot
    have hval : ((aeval z p : Algebra.adjoin A (s : Set F)) : F) = aeval (z : F) p :=
      (aeval_algHom_apply (Algebra.adjoin A (s : Set F)).val z p).symm
    rw [← hval]
    exact le_antisymm ((W.valuation_le_one_iff _).2 (hCW (aeval z p).2)) hnot
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖA : algebraMap K F ϖ ∈ A := hRA (algebraMap_mem_baseRing ϖ.2)
  by_cases hϖ1 : W₀.valuation (algebraMap K F ϖ) < 1
  · -- special fibre: `W` is a vertex of `X`, so `A = W ⊇ B`
    have hWO : W.comap (algebraMap K F) = O :=
      comap_eq_of_valuation_lt_one (hRA.trans hAW) hϖ ((hWA _ hϖA).2 hϖ1)
    have hzB : (z : F) ∈ Subring.closure ((baseRing F O : Set F) ∪ s) :=
      Subring.subset_closure (Or.inr hzs)
    have hO : ∀ o : O, algebraMap O F o ∈ A := fun o ↦ hRA (algebraMap_mem_baseRing o.2)
    have htr : IsResidueTranscendental O W z := by
      refine ⟨hCW z.2, fun P hP ↦ ?_⟩
      have hP' : aeval (z : F) (P.map (algebraMap O K)) = aeval (z : F) P := by
        rw [aeval_map_algebraMap]
      rw [hP', ← aeval_map_codRestrict hO]
      obtain ⟨i, hi⟩ : ∃ i, (P.map (residue O)).coeff i ≠ 0 := by
        by_contra! H
        exact hP (Polynomial.ext fun i ↦ by simpa using H i)
      rw [coeff_map, residue_ne_zero_iff_isUnit] at hi
      exact hzW _ ⟨i, by rw [coeff_map]; exact hi.map _⟩
    have hvert := hV W hWO _ hB (hBC.trans hCW) z hzB htr
    have hWeq := localAt_eq_of_mem_vertexSet hXs hvert hA₀ (hA₀A.trans hAW)
    rw [hloc] at hWeq
    rw [hWeq]
    exact hBC.trans hCW
  · -- generic fibre
    have hϖu : W₀.valuation (algebraMap K F ϖ) = 1 :=
      le_antisymm ((W₀.valuation_le_one_iff _).2 (hAW₀ hϖA)) (not_lt.1 hϖ1)
    have hϖi := hunit _ hϖA hϖu
    by_cases ha : ∃ a ∈ A, a ≠ 0 ∧ W₀.valuation a < 1
    · exfalso
      obtain ⟨a, haA, ha0, hav⟩ := ha
      have hK : ∀ k : K, algebraMap K F k ∈ A := by
        intro k
        by_cases hk : k ∈ O
        · exact hRA (algebraMap_mem_baseRing hk)
        have hki : k⁻¹ ∈ O := (O.mem_or_inv_mem k).resolve_left hk
        have hk0 : (⟨k⁻¹, hki⟩ : O) ≠ 0 := fun h ↦ by
          have : k⁻¹ = 0 := congrArg Subtype.val h
          rw [inv_eq_zero] at this
          exact hk (this ▸ O.zero_mem)
        obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hk0 hϖ
        have hu' : k⁻¹ = (u : O) * (ϖ : K) ^ n := by simpa using congrArg Subtype.val hu
        have hkk : k = ((u⁻¹ : Oˣ) : O) * ((ϖ : K)⁻¹) ^ n := by
          have hu0 : ((u : O) : K) ≠ 0 := by simp
          have hui : ((u⁻¹ : Oˣ) : O) = ((u : O) : K)⁻¹ := by
            rw [← mul_eq_one_iff_eq_inv₀ hu0]
            exact congrArg Subtype.val (Units.inv_mul u)
          rw [hui, inv_pow, ← mul_inv, ← hu', inv_inv]
        rw [hkk, map_mul, map_pow, map_inv₀]
        exact A.mul_mem (hRA (algebraMap_mem_baseRing (Subtype.prop _))) (A.pow_mem hϖi n)
      refine false_of_trdeg_le_one hF W (z := (z : F)) (fun p hp0 ↦ ?_) ha0
        ((hWA a haA).2 hav)
      rw [← aeval_map_codRestrict hK]
      obtain ⟨i, hi⟩ : ∃ i, p.coeff i ≠ 0 := by
        by_contra! H
        exact hp0 (Polynomial.ext fun i ↦ by simpa using H i)
      exact hzW _ ⟨i, by rw [coeff_map]; exact (Ne.isUnit hi).map _⟩
    · -- `A` is a field, hence `A = F`
      push Not at ha
      intro x _
      obtain ⟨a, haA, b, hbA, hb0, rfl⟩ := hXF A₀ hA₀ x
      have hbv : W₀.valuation b = 1 := le_antisymm
        ((W₀.valuation_le_one_iff _).2 (hAW₀ (hA₀A hbA))) (ha b (hA₀A hbA) hb0)
      rw [div_eq_mul_inv]
      exact A.mul_mem (hA₀A haA) (hunit b (hA₀A hbA) hbv)

end Domination

end SemistableReduction
