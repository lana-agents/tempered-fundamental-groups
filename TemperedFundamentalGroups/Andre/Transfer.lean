/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Tempered.Category

/-!
# Restriction from the orbifold `[Y/A]` to the scheme `Y` (Blueprint §10.3.2, T1)

Let `A` act on `R` and let `A'` be a trivial group acting on `R` (the scheme case). A level
`(B, H)` of `[Spec R / A]` gives the level `(B, H⁰)` of `[Spec R / A']`: the elements of
`H⁰ = ker (H → A)` are `R`-linear, hence semilinear over `1 ∈ A'`. Keeping the model, the map
`j`, the restriction of `ρ` to `H⁰` and the covering space with the action restricted to `H⁰`
gives the **restriction functor** `resFunctor : TempObj O R A ⥤ TempObj O R A'`. The fibre
functor only sees `H⁰`, so `resFunctor ⋙ tempFibre A' ≅ tempFibre A` (`resFibreIso`), and
restriction of automorphisms along it is a continuous homomorphism
`temperedPi1 (Y) →* temperedPi1 ([Y/A])` (`restrictHom`, `continuous_restrictHom`).

We also prove the group-theoretic core of T4 (`exists_open_normal_infinite_quotient`): if a
topological group `Γ` has an open subgroup `U` of finite index with a continuous surjection
`U → ℤ` (`ℤ` discrete), then `Γ` has an open normal subgroup with infinite quotient.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]
  (A' : Type u) [Group A'] [Subsingleton A'] [MulSemiringAction A' R]

namespace FiniteLevel

/-- The elements of `H⁰`, as automorphisms semilinear over `1 ∈ A'`. -/
def resHom (L : FiniteLevel R A) : L.H0 →* SemilinearAut R A' L.B where
  toFun g := ⟨1, (g : SemilinearAut R A L.B).σ, fun r => by
    rw [one_smul]
    exact SemilinearAut.σ_algebraMap_of_a_eq_one (mem_H0.1 g.2) r⟩
  map_one' := rfl
  map_mul' _ _ := SemilinearAut.ext (mul_one 1).symm rfl

omit [Subsingleton A'] in
lemma resHom_injective (L : FiniteLevel R A) : Function.Injective (resHom A' L) :=
  fun g h hgh => Subtype.ext (Subtype.ext (SemilinearAut.ext
    ((mem_H0.1 g.2).trans (mem_H0.1 h.2).symm) (by
      have := congrArg SemilinearAut.σ hgh
      exact this)))

/-- **The restricted level** `(B, H⁰)` of `[Spec R / A']`. -/
def res (L : FiniteLevel R A) : FiniteLevel R A' where
  toEtaleCode := L.toEtaleCode
  H := (resHom A' L).range
  surjective _ := ⟨1, Subgroup.one_mem _, Subsingleton.elim _ _⟩

/-- `H⁰ ≅ H(res L)`. -/
def resEquiv (L : FiniteLevel R A) : L.H0 ≃* (L.res A').H :=
  MonoidHom.ofInjective (resHom_injective A' L)

lemma σ_resEquiv (L : FiniteLevel R A) (g : L.H0) :
    (resEquiv A' L g).1.σ = g.1.1.σ := rfl

lemma σ_resEquiv_symm (L : FiniteLevel R A) (g : (L.res A').H) :
    ((resEquiv A' L).symm g).1.1.σ = g.1.σ := by
  conv_rhs => rw [← (resEquiv A' L).apply_symm_apply g]
  rfl

lemma mem_res_H0 (L : FiniteLevel R A) (g : (L.res A').H) : g ∈ (L.res A').H0 :=
  mem_H0.2 (Subsingleton.elim _ _)

variable {A'} in
/-- The group homomorphism of restricted levels. -/
def resR {L L' : FiniteLevel R A} (φ : L ⟶ L') : (L.res A').H →* (L'.res A').H :=
  ((resEquiv A' L').toMonoidHom.comp
    ((φ.r.restrict L.H0).codRestrict L'.H0 fun g => r_mem_H0 φ g.2)).comp
    (resEquiv A' L).symm.toMonoidHom

lemma resEquiv_symm_resR {L L' : FiniteLevel R A} (φ : L ⟶ L') (g : (L.res A').H) :
    (resEquiv A' L').symm (resR φ g) =
      ⟨φ.r ((resEquiv A' L).symm g), r_mem_H0 φ ((resEquiv A' L).symm g).2⟩ :=
  (resEquiv A' L').symm_apply_apply _

lemma resR_id (L : FiniteLevel R A) : resR (A' := A') (𝟙 L) = MonoidHom.id _ := by
  ext g : 1
  exact (resEquiv A' L).apply_symm_apply g

lemma resR_comp {L L' L'' : FiniteLevel R A} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    resR (A' := A') (φ ≫ ψ) = (resR ψ).comp (resR φ) := by
  ext g : 1
  apply (resEquiv A' L'').symm.injective
  rw [MonoidHom.comp_apply, resEquiv_symm_resR, resEquiv_symm_resR, resEquiv_symm_resR]
  rfl

/-- **The restriction of a morphism of levels.** -/
def Hom.res {L L' : FiniteLevel R A} (φ : L ⟶ L') : L.res A' ⟶ L'.res A' where
  f := φ.f
  r := resR φ
  r_a _ := Subsingleton.elim _ _
  f_σ g y := by
    have h := φ.f_σ ((resEquiv A' L).symm g).1 y
    have h1 := σ_resEquiv_symm A' L g
    have h2 := σ_resEquiv_symm A' L' (resR φ g)
    rw [resEquiv_symm_resR] at h2
    change φ.f ((resR φ g).1.σ y) = g.1.σ (φ.f y)
    rw [← h1, ← h2]
    exact h

end FiniteLevel

variable [Algebra K R]

namespace Level

/-- **The restricted level with a model**: same model and `j`, action restricted to `H⁰`. -/
def res (Lv : Level O R A) : Level O R A' where
  L := Lv.L.res A'
  c := Lv.c
  j := Lv.j
  j_toSpec := Lv.j_toSpec
  ρ := Lv.ρ.comp (Lv.L.H0.subtype.comp (Lv.L.resEquiv A').symm.toMonoidHom)
  ρ_toSpec _ := Lv.ρ_toSpec _
  ρ_j g := by
    have h := Lv.ρ_j ((Lv.L.resEquiv A').symm g : Lv.L.H)
    rw [FiniteLevel.σ_resEquiv_symm] at h
    exact h

lemma res_ρs (Lv : Level O R A) (g : (Lv.res A').L.H) :
    (Lv.res A').ρs g = Lv.ρs ((Lv.L.resEquiv A').symm g : Lv.L.H) := rfl

end Level

namespace TempObj

/-- The covering space with the action restricted to `H⁰`. -/
def resP (Lv : Level O R A) (P : CoveringCode Lv.ρs) : CoveringCode (Lv.res A').ρs where
  carrier := P.carrier
  top := P.top
  isCoveringMap := P.isCoveringMap
  act := P.act.comp (Lv.L.H0.subtype.comp (Lv.L.resEquiv A').symm.toMonoidHom)
  act_fst _ x := P.act_fst _ x

/-- **The restriction of an object** of the tempered category of `[Y/A]` to `Y`. -/
def res (X : TempObj O R A) : TempObj O R A' := ⟨X.Lv.res A', resP A' X.Lv X.P⟩

variable {A'} in
/-- **The restriction of a morphism.** -/
def Hom.res {X Y : TempObj O R A} (m : X ⟶ Y) : X.res A' ⟶ Y.res A' where
  φ := FiniteLevel.Hom.res A' m.φ
  ψ := m.ψ
  ψ_toSpec := m.ψ_toSpec
  j_ψ := m.j_ψ
  h := m.h
  continuous_h := m.continuous_h
  fst_h := m.fst_h
  h_act g x := by
    change m.h (X.P.act _ x) = Y.P.act (((Y.Lv.L.resEquiv A').symm
      (FiniteLevel.resR m.φ g) : Y.Lv.L.H0) : Y.Lv.L.H) (m.h x)
    rw [m.h_act, FiniteLevel.resEquiv_symm_resR]
    rfl

end TempObj

variable (O R A) in
/-- **The restriction functor** `TempObj(R, A) ⥤ TempObj(R, A')` (Blueprint §10.3.2, T1). -/
def resFunctor : TempObj O R A ⥤ TempObj O R A' where
  obj X := X.res A'
  map m := TempObj.Hom.res m
  map_id X := TempObj.Hom.ext (FiniteLevel.Hom.ext rfl (FiniteLevel.resR_id A' X.Lv.L)) rfl rfl
  map_comp m n :=
    TempObj.Hom.ext (FiniteLevel.Hom.ext rfl (FiniteLevel.resR_comp A' m.φ n.φ)) rfl rfl

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace TempObj

/-- A pair `(t, p)` for `X`, seen as a pair for the restriction of `X`. -/
def toResPre (X : TempObj O R A) (q : PreFibre Ω V hV X) : PreFibre Ω V hV (X.res A') := q

lemma res_smul (X : TempObj O R A) (g : X.Lv.L.H0) (q : PreFibre Ω V hV X) :
    (⟨X.Lv.L.resEquiv A' g, FiniteLevel.mem_res_H0 A' _ _⟩ : (X.res A').Lv.L.H0) •
      toResPre A' V hV X q = toResPre A' V hV X (g • q) := by
  apply Subtype.ext
  change (FiniteLevel.fibreAct Ω X.Lv.L g q.1.1,
    X.P.act (((X.Lv.L.resEquiv A').symm (X.Lv.L.resEquiv A' g) : X.Lv.L.H0) : X.Lv.L.H)
      q.1.2) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The fibres of an object and of its restriction agree. -/
def resFibreEquiv (X : TempObj O R A) : Fibre Ω V hV (X.res A') ≃ Fibre Ω V hV X :=
  Quotient.congr (Equiv.refl _) fun q q' => by
    change q ∈ MulAction.orbit (X.res A').Lv.L.H0 q' ↔
      q ∈ MulAction.orbit X.Lv.L.H0 (α := PreFibre Ω V hV X) q'
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨(X.Lv.L.resEquiv A').symm g.1, ?_⟩
      have h := res_smul A' V hV X ((X.Lv.L.resEquiv A').symm g.1) q'
      have hg : (⟨X.Lv.L.resEquiv A' ((X.Lv.L.resEquiv A').symm g.1),
          FiniteLevel.mem_res_H0 A' _ _⟩ : (X.res A').Lv.L.H0) = g :=
        Subtype.ext (MulEquiv.apply_symm_apply _ _)
      rw [hg] at h
      exact h.symm
    · rintro ⟨g, rfl⟩
      exact ⟨_, res_smul A' V hV X g q'⟩

end TempObj

variable (O R A) in
/-- **The fibre functor is unchanged by restriction**: `Res ⋙ Φ_{A'} ≅ Φ_A`. -/
def resFibreIso : resFunctor O R A A' ⋙ tempFibre O R A' V hV ≅ tempFibre O R A V hV :=
  NatIso.ofComponents (fun X => (TempObj.resFibreEquiv A' V hV X).toIso) fun m => by
    ext x
    induction x using Quotient.inductionOn
    rfl

variable (O R A) in
/-- **The homomorphism `temperedPi1(Y) →* temperedPi1([Y/A])`** given by restriction of
automorphisms of the fibre functor along `resFunctor`. -/
def restrictHom : temperedPi1 O R A' V hV →* temperedPi1 O R A V hV :=
  FibreAut.restrict (resFunctor O R A A') (resFibreIso O R A A' V hV)

lemma continuous_restrictHom : Continuous (restrictHom O R A A' V hV) :=
  FibreAut.continuous_restrict _ _

end

/-! ### T4: an infinite discrete quotient from a finite-index subgroup with a `ℤ`-character -/

section Group

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **An infinite discrete quotient.** If `U` is an open subgroup of finite index of a
topological group `Γ` and `χ : U →* ℤ` is continuous and surjective (`ℤ` discrete), then `Γ` has
an open normal subgroup `M` (the normal core of `ker χ`) with `Γ ⧸ M` infinite. -/
theorem exists_open_normal_infinite_quotient (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    [U.FiniteIndex] (χ : U →* Multiplicative ℤ) (hχ : Continuous χ)
    (hsurj : Function.Surjective χ) :
    ∃ M : Subgroup Γ, IsOpen (M : Set Γ) ∧ M.Normal ∧ Infinite (Γ ⧸ M) := by
  classical
  -- `K = ker χ ⊆ U ⊆ Γ` is open and normal in `U`.
  let K : Subgroup Γ := χ.ker.map U.subtype
  have hK : IsOpen (K : Set Γ) := by
    have h1 : IsOpen (χ.ker : Set U) := by
      have : (χ.ker : Set U) = χ ⁻¹' {1} := rfl
      rw [this]
      exact (isOpen_discrete _).preimage hχ
    obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.1 h1
    have : (K : Set Γ) = W ∩ U := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨?_, k.2⟩
        have : k ∈ (Subtype.val ⁻¹' W : Set U) := by rw [hWe]; exact hk
        exact this
      · rintro ⟨hxW, hxU⟩
        refine ⟨⟨x, hxU⟩, ?_, rfl⟩
        rw [← hWe]
        exact hxW
    rw [this]
    exact hW.inter hU
  have hKn : ∀ u ∈ U, ∀ k ∈ K, u * k * u⁻¹ ∈ K := by
    rintro u hu _ ⟨k, hk, rfl⟩
    refine ⟨⟨u, hu⟩ * k * ⟨u, hu⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hk ⊢
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one]
  -- The normal core `M` of `K` is the intersection over coset representatives of `Γ ⧸ U`.
  let M : Subgroup Γ := K.normalCore
  have hsub : (⋂ q : Γ ⧸ U, (fun x => q.out⁻¹ * x * q.out) ⁻¹' (K : Set Γ)) ⊆ M := by
    intro x hx g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g⁻¹
    have hx' := hx (QuotientGroup.mk g⁻¹)
    generalize (QuotientGroup.mk g⁻¹ : Γ ⧸ U).out = c at hh hx'
    have hg : g = h * c⁻¹ := by rw [hh, mul_inv_rev, inv_inv, mul_inv_cancel_left]
    change g * x * g⁻¹ ∈ K
    subst hg
    convert hKn h h.2 _ hx' using 1
    group
  have hM : IsOpen (M : Set Γ) := by
    refine Subgroup.isOpen_of_mem_nhds M (g := 1) (Filter.mem_of_superset
      ((isOpen_iInter_of_finite fun q => hK.preimage (by fun_prop)).mem_nhds ?_) hsub)
    simp only [Set.mem_iInter, Set.mem_preimage, mul_one, inv_mul_cancel, SetLike.mem_coe]
    exact fun _ => K.one_mem
  refine ⟨M, hM, Subgroup.normalCore_normal K, ?_⟩
  choose u hu using hsurj
  refine Infinite.of_injective
    (fun n : Multiplicative ℤ => (QuotientGroup.mk (u n : Γ) : Γ ⧸ M)) fun n m hnm => ?_
  rw [QuotientGroup.eq] at hnm
  obtain ⟨k, hk, hk'⟩ := Subgroup.normalCore_le K hnm
  have hk'' : k = (u n)⁻¹ * u m := Subtype.ext (by simpa using hk')
  rw [SetLike.mem_coe, MonoidHom.mem_ker, hk'', map_mul, map_inv, hu, hu] at hk
  exact (inv_mul_eq_one.1 hk)

end Group

end TemperedFundamentalGroups
