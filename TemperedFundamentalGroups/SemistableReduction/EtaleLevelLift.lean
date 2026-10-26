/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleTower
import TemperedFundamentalGroups.SemistableReduction.EtaleSpecialFibre

/-!
# The levels of an étale cover are the étale lifts of its special fibre (Blueprint §12.8, M2.3)

Setting of `EtaleTower`: a chart `T` over `O`, levels `Tn n = T/ϖⁿ⁺¹T`, special fibre
`Ts = T/(ker θ)T`, `b ∈ T`.

* **`EtaleTower.Lift.equiv`**: any two étale lifts `L L' : Lift T hϖ C b n` of a special-fibre
  covering `C` at level `n` are isomorphic over `Tn n`, compatibly with the identifications `σ`
  (`Lift.σ_equiv`), by a unique such isomorphism (`Lift.eq_equiv`) (`EtaleLift.algEquivOfQuot`).
* For a `T`-algebra `B` with special fibre `CB = B/JB` and levels `Pn n = (B/ϖⁿ⁺¹B)[1/b]`:
  `levelσ : Pn n/J ≃ (CB)[1/b̄]`, and **`levelLift`**: if `Pn n` is formally étale over `Tn n` and
  `B` is finite over `T`, then `Pn n` is an étale lift of `CB` at level `n`. Hence
  **`levelEquiv L : Pn n ≃ₐ[Tn n] L.E`** for every lift `L` (e.g. `EtaleTower.lift`), with
  `σ_levelEquiv`.
* Étaleness of `Pn n` over `Tn n`: **`etale_Pn_of_away`** from `B_b` étale over `T`, and
  **`etale_Pn_of_isEtaleAt_maximal`** from étaleness of `B` over `T` at the maximal ideals of `B`
  containing `JB` and not containing `b` (`T` Noetherian, `B` finite, `B/JB` Jacobson), via
  `EtaleQuot.etale_quot_of_isEtaleAt_maximal` and `isJacobsonRing_of_ker_le_nilradical`.
-/

universe u

namespace SemistableReduction

open AdmissibleLift

/-- **Jacobson rings lift along nil thickenings**: if `f : R → R'` is surjective with kernel in
the nilradical and `R'` is Jacobson, then `R` is Jacobson. -/
theorem isJacobsonRing_of_ker_le_nilradical {R R' : Type*} [CommRing R] [CommRing R']
    (f : R →+* R') (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical R)
    [IsJacobsonRing R'] : IsJacobsonRing R := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  have hkP : RingHom.ker f ≤ P := hker.trans (nilradical_le_prime P)
  haveI : (P.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hkP
  have hcm : (P.map f).comap f = P := Ideal.comap_map_of_surjective' f hf P ▸
    sup_eq_left.mpr hkP
  rw [← hcm, ← Ideal.comap_jacobson_of_surjective hf,
    (isJacobsonRing_iff_prime_eq.mp inferInstance) _ inferInstance]

namespace EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {ϖ : O}
  {T : Type u} [CommRing T] [Algebra O T] {hϖ : θ ϖ = 0}
  {C : Type u} [CommRing C] [Algebra (Ts θ T) C] {b : T}

/-! ### Uniqueness of the étale lifts at a level -/

namespace Lift

variable (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) {n : ℕ}

/-- **Two étale lifts of `C` at level `n` are isomorphic**: the lift of `σ'⁻¹ ∘ σ`
(`EtaleLift.algEquivOfQuot`; `J` is nilpotent on `Tn n`). -/
def equiv (L L' : Lift T hϖ C b n) : L.E ≃ₐ[Tn ϖ T n] L'.E :=
  letI := algC T hϖ C n
  haveI := EtaleNil.isAdicComplete (J θ (R := Tn ϖ T n)) (hJ hker n) L.E
  haveI := EtaleNil.isAdicComplete (J θ (R := Tn ϖ T n)) (hJ hker n) L'.E
  EtaleLift.algEquivOfQuot (J θ (R := Tn ϖ T n)) (L.σ.trans L'.σ.symm)

/-- **`Lift.equiv` is compatible with the identifications `σ`.** -/
lemma σ_equiv (L L' : Lift T hϖ C b n) (x : L.E) :
    letI := algC T hϖ C n
    L'.σ (Ideal.Quotient.mk _ (equiv hker L L' x)) = L.σ (Ideal.Quotient.mk _ x) := by
  letI := algC T hϖ C n
  haveI := EtaleNil.isAdicComplete (J θ (R := Tn ϖ T n)) (hJ hker n) L.E
  haveI := EtaleNil.isAdicComplete (J θ (R := Tn ϖ T n)) (hJ hker n) L'.E
  have h := congrArg (fun f ↦ f x)
    (EtaleLift.mkₐ_comp_algEquivOfQuot (J θ (R := Tn ϖ T n)) (L.σ.trans L'.σ.symm))
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
  exact (congrArg L'.σ h).trans (L'.σ.apply_symm_apply _)

/-- **Uniqueness**: an algebra map `L.E → L'.E` compatible with the `σ` is `Lift.equiv`. -/
lemma eq_equiv (L L' : Lift T hϖ C b n) (φ : L.E →ₐ[Tn ϖ T n] L'.E)
    (hφ : letI := algC T hϖ C n;
      ∀ x, L'.σ (Ideal.Quotient.mk _ (φ x)) = L.σ (Ideal.Quotient.mk _ x)) :
    φ = (equiv hker L L').toAlgHom := by
  letI := algC T hϖ C n
  refine EtaleNil.ext (J θ (R := Tn ϖ T n)) (hJ hker n) fun x ↦ L'.σ.injective ?_
  change L'.σ (Ideal.Quotient.mk _ (φ x)) = L'.σ (Ideal.Quotient.mk _ (equiv hker L L' x))
  rw [hφ, σ_equiv]

end Lift

/-! ### The levels of a cover -/

section Level

variable (θ ϖ T) (B : Type u) [CommRing B] [Algebra T B]

/-- The ideal `ϖⁿ⁺¹T` (so that `Tn n = T/In n`). -/
abbrev In (n : ℕ) : Ideal T := (Iv ϖ n).map (algebraMap O T)

/-- **The level `n` of `B` over `D(b)`**: `(B/ϖⁿ⁺¹B)[1/b]`. -/
abbrev Pn (b : T) (n : ℕ) : Type u :=
  Localization.Away (Ideal.Quotient.mk ((In ϖ T n).map (algebraMap T B)) (algebraMap T B b))

/-- **The special fibre `B/JB`** of `B` (`FormalKummer.Cs θ T B`). -/
abbrev CB : Type u := B ⧸ (J θ (R := T)).map (algebraMap T B)

variable {θ ϖ T B}

include hϖ in
lemma In_map_le (n : ℕ) :
    (In ϖ T n).map (algebraMap T B) ≤ (J θ (R := T)).map (algebraMap T B) :=
  Ideal.map_mono (Ideal.map_mono (Iv_le_ker hϖ n))

variable (hϖ)

/-- The reduction `B/ϖⁿ⁺¹B → B/JB`. -/
abbrev red (n : ℕ) : (B ⧸ (In ϖ T n).map (algebraMap T B)) →+* CB θ T B :=
  Ideal.Quotient.factor (In_map_le (hϖ := hϖ) n)

variable (b)

/-- The map `B/JB → Pn n/J`. -/
def γ (n : ℕ) : CB θ T B →+* Pn ϖ T B b n ⧸ JE θ ϖ T n (Pn ϖ T B b n) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp
    ((algebraMap (B ⧸ (In ϖ T n).map (algebraMap T B)) (Pn ϖ T B b n)).comp
      (Ideal.Quotient.mk _))) (by
    intro a ha
    rw [← RingHom.mem_ker]
    refine (Ideal.map_le_iff_le_comap.mpr ?_) ha
    intro t ht
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Ideal.Quotient.mk _ (algebraMap (Tn ϖ T n) (Pn ϖ T B b n)
      (Ideal.Quotient.mk _ t)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_map_of_mem _ ?_
    have hJ : J θ (R := Tn ϖ T n) = (J θ (R := T)).map (Ideal.Quotient.mk _) := by
      rw [J, J, Ideal.map_map]
      rfl
    rw [hJ]
    exact Ideal.mem_map_of_mem _ ht)

lemma γ_mk (n : ℕ) (x : B) :
    γ (θ := θ) (ϖ := ϖ) (B := B) b n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _
      (algebraMap (B ⧸ (In ϖ T n).map (algebraMap T B)) (Pn ϖ T B b n) (Ideal.Quotient.mk _ x)) :=
  rfl

include hϖ in
/-- `Pn n/J` is the localization of `B/JB` away from `b̄`. -/
lemma isLocalization_γ (n : ℕ) :
    letI := (γ (θ := θ) (ϖ := ϖ) (B := B) b n).toAlgebra
    IsLocalization.Away (algebraMap (Ts θ T) (CB θ T B) (Ideal.Quotient.mk _ b))
      (Pn ϖ T B b n ⧸ JE θ ϖ T n (Pn ϖ T B b n)) := by
  letI := (γ (θ := θ) (ϖ := ϖ) (B := B) b n).toAlgebra
  have h := IsLocalization.of_surjective
    (M := Submonoid.powers (Ideal.Quotient.mk ((In ϖ T n).map (algebraMap T B))
      (algebraMap T B b))) (S := Pn ϖ T B b n)
    (red hϖ n) (Ideal.Quotient.factor_surjective _)
    (Ideal.Quotient.mk (JE θ ϖ T n (Pn ϖ T B b n))) Ideal.Quotient.mk_surjective
    (by
      refine RingHom.ext fun x ↦ ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
    (by
      rw [Ideal.mk_ker, Ideal.Quotient.factor_ker]
      refine le_of_eq ?_
      simp only [JE, EtaleNil.JB, J, Ideal.map_map]
      congr 1)
  rw [Submonoid.map_powers] at h
  exact h

variable (B)

/-- **`σ` for the levels of `B`**: `Pn n/J ≃ (B/JB)[1/b̄]` over `Tn n`. -/
def levelσ (n : ℕ) :
    letI := algC T hϖ (CB θ T B) n
    (Pn ϖ T B b n ⧸ JE θ ϖ T n (Pn ϖ T B b n)) ≃ₐ[Tn ϖ T n] Cb θ T (CB θ T B) b :=
  letI := algC T hϖ (CB θ T B) n
  letI := (γ (θ := θ) (ϖ := ϖ) (B := B) b n).toAlgebra
  haveI := isLocalization_γ (B := B) hϖ b n
  let e : (Pn ϖ T B b n ⧸ JE θ ϖ T n (Pn ϖ T B b n)) ≃ₐ[CB θ T B] Cb θ T (CB θ T B) b :=
    IsLocalization.algEquiv (Submonoid.powers
      (algebraMap (Ts θ T) (CB θ T B) (Ideal.Quotient.mk _ b))) _ _
  { e.toRingEquiv with
    commutes' := fun r ↦ by
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective r
      have h1 : algebraMap (Tn ϖ T n) (Pn ϖ T B b n ⧸ JE θ ϖ T n (Pn ϖ T B b n))
          (Ideal.Quotient.mk _ t) = algebraMap (CB θ T B) _
            (Ideal.Quotient.mk _ (algebraMap T B t)) := rfl
      have h2 : algebraMap (Tn ϖ T n) (Cb θ T (CB θ T B) b) (Ideal.Quotient.mk _ t) =
          algebraMap (CB θ T B) _ (Ideal.Quotient.mk _ (algebraMap T B t)) := rfl
      change e _ = _
      rw [h1, h2, AlgEquiv.commutes] }

lemma levelσ_mk (n : ℕ) (x : B) :
    letI := algC T hϖ (CB θ T B) n
    levelσ hϖ b B n (Ideal.Quotient.mk _ (algebraMap (B ⧸ (In ϖ T n).map (algebraMap T B))
      (Pn ϖ T B b n) (Ideal.Quotient.mk _ x))) =
      algebraMap (CB θ T B) (Cb θ T (CB θ T B) b) (Ideal.Quotient.mk _ x) := by
  letI := algC T hϖ (CB θ T B) n
  letI := (γ (θ := θ) (ϖ := ϖ) (B := B) b n).toAlgebra
  haveI := isLocalization_γ (B := B) hϖ b n
  exact (IsLocalization.algEquiv (Submonoid.powers
    (algebraMap (Ts θ T) (CB θ T B) (Ideal.Quotient.mk _ b))) _ _).commutes
    (Ideal.Quotient.mk _ x)

/-- `b` is a unit in `Pn n`. -/
lemma isUnit_b (n : ℕ) : IsUnit (algebraMap (Tn ϖ T n) (Pn ϖ T B b n) (Ideal.Quotient.mk _ b)) :=
  IsLocalization.Away.algebraMap_isUnit
    (Ideal.Quotient.mk ((In ϖ T n).map (algebraMap T B)) (algebraMap T B b))

/-- `Pn n` is finite over `(Tn n)[1/b]`, in the form of `Lift.hfin`. -/
lemma hfin_Pn [Module.Finite T B] (n : ℕ) :
    ∃ s : Finset (Pn ϖ T B b n), ∀ p : Pn ϖ T B b n, ∃ k : ℕ,
      (Ideal.Quotient.mk _ b : Tn ϖ T n) ^ k • p ∈
        Submodule.span (Tn ϖ T n) (s : Set (Pn ϖ T B b n)) := by
  set Bn := B ⧸ (In ϖ T n).map (algebraMap T B)
  haveI : Module.Finite T Bn :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom T B Bn).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (Tn ϖ T n) Bn := Module.Finite.of_restrictScalars_finite T _ _
  obtain ⟨s₀, hs₀⟩ := Module.Finite.fg_top (R := Tn ϖ T n) (M := Bn)
  classical
  refine ⟨s₀.image (algebraMap Bn (Pn ϖ T B b n)), fun p ↦ ?_⟩
  obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hx⟩ := IsLocalization.surj
    (Submonoid.powers (Ideal.Quotient.mk ((In ϖ T n).map (algebraMap T B)) (algebraMap T B b))) p
  refine ⟨k, ?_⟩
  have hmem : x ∈ Submodule.span (Tn ϖ T n) (s₀ : Set Bn) := hs₀ ▸ Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem
    (f := (IsScalarTower.toAlgHom (Tn ϖ T n) Bn (Pn ϖ T B b n)).toLinearMap) hmem
  rw [Submodule.map_span] at h2
  have hp : (Ideal.Quotient.mk _ b : Tn ϖ T n) ^ k • p = algebraMap Bn (Pn ϖ T B b n) x := by
    rw [Algebra.smul_def, ← hx, mul_comm, map_pow, map_pow]
    rfl
  rw [hp, Finset.coe_image]
  exact h2

variable {B}

/-- **The levels of a cover are étale lifts of its special fibre**: if `B` is finite over `T` and
`Pn n = (B/ϖⁿ⁺¹B)[1/b]` is formally étale over `Tn n`, then `Pn n` is an étale lift of
`B/JB` over `D(b)` at level `n` (with `σ = levelσ`). -/
def levelLift [Module.Finite T B] (n : ℕ) [Algebra.FormallyEtale (Tn ϖ T n) (Pn ϖ T B b n)] :
    Lift T hϖ (CB θ T B) b n where
  E := Pn ϖ T B b n
  σ := levelσ hϖ b B n
  hb := isUnit_b b B n
  hfin := hfin_Pn b B n

variable (hker : RingHom.ker θ ≤ Ideal.span {ϖ})

/-- **The level `n` of `B` is the étale lift `L`** (e.g. `L = EtaleTower.lift T hϖ C b hker hC n`
with `C = B/JB`): `(B/ϖⁿ⁺¹B)[1/b] ≃ₐ[Tn n] L.E`, compatible with the reductions to `C[1/b̄]`
(`σ_levelEquiv`) and unique as such (`eq_levelEquiv`). -/
def levelEquiv [Module.Finite T B] (n : ℕ) [Algebra.FormallyEtale (Tn ϖ T n) (Pn ϖ T B b n)]
    (L : Lift T hϖ (CB θ T B) b n) : Pn ϖ T B b n ≃ₐ[Tn ϖ T n] L.E :=
  Lift.equiv hker (levelLift hϖ b n) L

/-- **`levelEquiv` commutes with the maps to `C[1/b̄]`**: the class of `x ∈ B` goes to the
element of `L.E` whose reduction is `σ⁻¹(x̄)`. -/
lemma σ_levelEquiv [Module.Finite T B] (n : ℕ) [Algebra.FormallyEtale (Tn ϖ T n) (Pn ϖ T B b n)]
    (L : Lift T hϖ (CB θ T B) b n) (x : B) :
    letI := algC T hϖ (CB θ T B) n
    L.σ (Ideal.Quotient.mk _ (levelEquiv hϖ b hker n L (algebraMap
      (B ⧸ (In ϖ T n).map (algebraMap T B)) (Pn ϖ T B b n) (Ideal.Quotient.mk _ x)))) =
      algebraMap (CB θ T B) (Cb θ T (CB θ T B) b) (Ideal.Quotient.mk _ x) :=
  (Lift.σ_equiv hker (levelLift hϖ b n) L _).trans (levelσ_mk hϖ b B n x)

/-- `levelEquiv` is compatible with the identifications `σ` (general form). -/
lemma σ_levelEquiv' [Module.Finite T B] (n : ℕ)
    [Algebra.FormallyEtale (Tn ϖ T n) (Pn ϖ T B b n)] (L : Lift T hϖ (CB θ T B) b n)
    (p : Pn ϖ T B b n) :
    letI := algC T hϖ (CB θ T B) n
    L.σ (Ideal.Quotient.mk _ (levelEquiv hϖ b hker n L p)) =
      levelσ hϖ b B n (Ideal.Quotient.mk _ p) :=
  Lift.σ_equiv hker (levelLift hϖ b n) L p

/-- **Uniqueness of `levelEquiv`.** -/
lemma eq_levelEquiv [Module.Finite T B] (n : ℕ) [Algebra.FormallyEtale (Tn ϖ T n) (Pn ϖ T B b n)]
    (L : Lift T hϖ (CB θ T B) b n) (φ : Pn ϖ T B b n →ₐ[Tn ϖ T n] L.E)
    (hφ : letI := algC T hϖ (CB θ T B) n;
      ∀ p, L.σ (Ideal.Quotient.mk _ (φ p)) = levelσ hϖ b B n (Ideal.Quotient.mk _ p)) :
    φ = (levelEquiv hϖ b hker n L).toAlgHom :=
  Lift.eq_equiv hker (levelLift hϖ b n) L φ hφ

/-! ### Étaleness of the levels -/

/-- **From étaleness over `D(b)`**: `B_b` étale over `T` ⇒ `Pn n` étale over `Tn n`. -/
theorem etale_Pn_of_away (n : ℕ) [Algebra.Etale T (Localization.Away (algebraMap T B b))] :
    Algebra.Etale (Tn ϖ T n) (Pn ϖ T B b n) :=
  EtaleQuot.etale_quot_away (In ϖ T n) (algebraMap T B b)

include hϖ hker in
/-- **From étaleness at the closed points of the special fibre over `D(b)`**: `T` Noetherian, `B`
finite over `T` with Jacobson special fibre `B/JB`, `B` étale over `T` at every maximal ideal
`Q ⊇ JB` with `b ∉ Q` ⇒ `Pn n` étale over `Tn n` for every `n`. -/
theorem etale_Pn_of_isEtaleAt_maximal [IsNoetherianRing T] [Module.Finite T B]
    [IsJacobsonRing (CB θ T B)]
    (h : ∀ (Q : Ideal B) [Q.IsMaximal], (J θ (R := T)).map (algebraMap T B) ≤ Q →
      algebraMap T B b ∉ Q → Algebra.IsEtaleAt T Q) (n : ℕ) :
    Algebra.Etale (Tn ϖ T n) (Pn ϖ T B b n) := by
  set I := (In ϖ T n).map (algebraMap T B)
  haveI : Algebra.FinitePresentation T B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Module.Finite T (B ⧸ I) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom T B (B ⧸ I)).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (Tn ϖ T n) (B ⧸ I) := Module.Finite.of_restrictScalars_finite T _ _
  haveI : Algebra.FinitePresentation (Tn ϖ T n) (B ⧸ I) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- `B/JB` is `B/ϖⁿ⁺¹B` modulo a nilpotent ideal
  have hnil : (J θ (R := T)).map (algebraMap T B) ^ (n + 1) ≤ I := by
    rw [← Ideal.map_pow]
    refine Ideal.map_mono ?_
    rw [J, ← Ideal.map_pow]
    exact Ideal.map_mono (Ideal.pow_right_mono hker (n + 1))
  haveI : IsJacobsonRing (B ⧸ I) := by
    refine isJacobsonRing_of_ker_le_nilradical (red hϖ n) (Ideal.Quotient.factor_surjective _)
      fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hy : y ∈ (J θ (R := T)).map (algebraMap T B) := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [mem_nilradical]
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hnil (Ideal.pow_mem_pow hy (n + 1))
  refine EtaleQuot.etale_quot_of_isEtaleAt_maximal (In ϖ T n) (algebraMap T B b)
    fun Q _ hIQ hbQ ↦ h Q ?_ hbQ
  -- a prime containing `ϖⁿ⁺¹` contains `ϖ`, hence `JB`
  have hϖQ : algebraMap T B (algebraMap O T ϖ) ∈ Q := by
    refine (inferInstance : Q.IsMaximal).isPrime.mem_of_pow_mem (n + 1) ?_
    rw [← map_pow, ← map_pow]
    refine hIQ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ?_))
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) (n + 1)
  rw [Ideal.map_le_iff_le_comap, J, Ideal.map_le_iff_le_comap]
  refine hker.trans ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact hϖQ

end Level

end

end EtaleTower

end SemistableReduction
