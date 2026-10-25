/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Etale.StandardEtale
import TemperedFundamentalGroups.SemistableReduction.EtaleLocalDomain

/-!
# Descending étale neighbourhoods of a localization

MR12 T2 S4 route (a): one works over an étale neighbourhood of the local ring `A_𝔭` of the node
and then descends it to an étale neighbourhood of `Spec A` (the chart). This file proves the
required "limit argument".

## Main results

* `exists_etale_localization_equiv`: if `R'` is étale over `A_𝔭` and `P` is a prime of `R'`,
  there are an étale `A`-algebra `N₁` and a prime `𝔫` of `N₁` lying over the same prime of `A`
  as `P`, with `(N₁)_𝔫 ≅ R'_P` compatibly with the maps from `A`.
* `exists_etale_isDomain_localization_equiv`: if `A` is moreover a Noetherian integrally closed
  domain, `N₁` can be taken to be a domain.
* `isField_tensor_fractionRing`, `isFractionRing_tensor_fractionRing`: for an étale domain `N`
  over a domain `A`, the generic fibre `N ⊗_A Frac A` is a field and a fraction field of `N`.

## Proof sketch

By Stacks 00UE (`Algebra.IsEtaleAt.exists_isStandardEtale`) some `R'_f`, `f ∉ P`, is standard
étale over `A_𝔭`, given by a pair `(F, G)`. Clearing the finitely many denominators of `F` and
`G` by one `t ∉ 𝔭` gives a standard étale pair `(F₀, G₀ F₀')` over `A[1/t]` whose base change
to `A_𝔭` presents `R'_f` (replacing `G` by `G F'` does not change the algebra, and makes the
invertibility condition on `F'` automatic). Its ring `N₁` is étale over `A`, and
`R'_f ≅ A_𝔭 ⊗_{A[1/t]} N₁` is a localization of `N₁`, so the local rings agree. For the domain
statement, the kernel of `N₁ → (N₁)_𝔫` is finitely generated, hence killed by one `g ∉ 𝔫`;
then `N₁[1/g]` embeds into its local ring at `𝔫`, which is a domain by
`SemistableReduction.isDomain_localization_of_etale`.
-/

open Polynomial TensorProduct

namespace SemistableReduction.EtaleDescent

universe u

section Lift

variable {A : Type u} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime]

/-- For `t ∉ 𝔭`, the canonical algebra structure of `A[1/t]` acting on `A_𝔭`. -/
noncomputable abbrev awayAlgebra {t : A} (ht : t ∉ 𝔭) :
    Algebra (Localization.Away t) (Localization.AtPrime 𝔭) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers t) 𝔭.primeCompl
    (Submonoid.powers_le.mpr ht)

lemma awayAlgebra_isScalarTower {t : A} (ht : t ∉ 𝔭) :
    letI := awayAlgebra 𝔭 ht
    IsScalarTower A (Localization.Away t) (Localization.AtPrime 𝔭) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _

/-- Finitely many elements of `A_𝔭` all come from a single `A[1/t]` with `t ∉ 𝔭`. -/
lemma exists_notMem_forall_mem_range (s : Finset (Localization.AtPrime 𝔭)) :
    ∃ (t : A) (ht : t ∉ 𝔭), ∀ x ∈ s,
      x ∈ Set.range (algebraMap (Localization.Away t) (Localization.AtPrime 𝔭)
        (self := awayAlgebra 𝔭 ht)) := by
  obtain ⟨⟨b, hb⟩, H⟩ := IsLocalization.exist_integer_multiples_of_finset 𝔭.primeCompl s
  have hb' : b ∉ 𝔭 := hb
  refine ⟨b, hb', fun x hx ↦ ?_⟩
  letI := awayAlgebra 𝔭 hb'
  have := awayAlgebra_isScalarTower 𝔭 hb'
  obtain ⟨r, hr⟩ := H x hx
  refine ⟨IsLocalization.mk' _ r (⟨b, Submonoid.mem_powers b⟩ : Submonoid.powers b), ?_⟩
  have h₁ := congrArg (algebraMap (Localization.Away b) (Localization.AtPrime 𝔭))
    (IsLocalization.mk'_spec (Localization.Away b) r
      (⟨b, Submonoid.mem_powers b⟩ : Submonoid.powers b))
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h₁
  refine (IsLocalization.map_units (Localization.AtPrime 𝔭)
    (⟨b, hb⟩ : 𝔭.primeCompl)).mul_right_cancel ?_
  rw [h₁, hr, Algebra.smul_def, mul_comm]

end Lift

section Pair

variable {R : Type*} [CommRing R]

/-- Replacing `g` by `g * f'` does not change a standard étale algebra. -/
noncomputable def StandardEtalePair.ringEquivOfMul (P₁ P₂ : StandardEtalePair R)
    (hf : P₁.f = P₂.f) (hg : P₁.g = P₂.g * derivative P₂.f) : P₁.Ring ≃ₐ[R] P₂.Ring := by
  have h₁ : P₁.HasMap P₂.X := by
    refine ⟨by rw [hf]; exact P₂.hasMap_X.1, ?_⟩
    rw [hg, map_mul]
    exact P₂.hasMap_X.2.mul P₂.hasMap_X.isUnit_derivative_f
  have h₂ : P₂.HasMap P₁.X := by
    refine ⟨by rw [← hf]; exact P₁.hasMap_X.1, ?_⟩
    have := P₁.hasMap_X.2
    rw [hg, map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  exact .ofAlgHom (P₁.lift _ h₁) (P₂.lift _ h₂) (P₂.hom_ext (by simp)) (P₁.hom_ext (by simp))

end Pair


section Descent

variable {A : Type u} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime]

/-- A standard étale algebra over `A_𝔭` is the base change of a standard étale algebra over some
`A[1/t]` with `t ∉ 𝔭`. -/
lemma exists_standardEtalePair (S : Type u) [CommRing S] [Algebra (Localization.AtPrime 𝔭) S]
    [Algebra.IsStandardEtale (Localization.AtPrime 𝔭) S] :
    ∃ (t : A) (ht : t ∉ 𝔭), letI := awayAlgebra 𝔭 ht
      ∃ P₀ : StandardEtalePair (Localization.Away t),
        Nonempty (Localization.AtPrime 𝔭 ⊗[Localization.Away t] P₀.Ring ≃ₐ[Localization.AtPrime 𝔭]
          S) := by
  classical
  let Q : StandardEtalePresentation (Localization.AtPrime 𝔭) S :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨t, ht, H⟩ := exists_notMem_forall_mem_range 𝔭 (Q.f.coeffs ∪ Q.g.coeffs)
  refine ⟨t, ht, ?_⟩
  letI := awayAlgebra 𝔭 ht
  have hl : ∀ p : (Localization.AtPrime 𝔭)[X], p.coeffs ⊆ Q.f.coeffs ∪ Q.g.coeffs →
      p ∈ lifts (algebraMap (Localization.Away t) (Localization.AtPrime 𝔭)) := by
    intro p hp
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases h : p.coeff n = 0
    · exact ⟨0, by simp [h]⟩
    · exact H _ (hp (coeff_mem_coeffs h))
  obtain ⟨F₀, hF₀, -, hmon⟩ :=
    lifts_and_natDegree_eq_and_monic (hl Q.f Finset.subset_union_left) Q.monic_f
  obtain ⟨G₀, hG₀⟩ := (mem_lifts _).mp (hl Q.g Finset.subset_union_right)
  let P₀ : StandardEtalePair (Localization.Away t) :=
    ⟨F₀, hmon, G₀ * derivative F₀, ⟨G₀, 0, 1, by ring⟩⟩
  let Pb : StandardEtalePresentation (Localization.Away t) P₀.Ring :=
    ⟨P₀, P₀.X, P₀.hasMap_X, by
      simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩
  let e₁ := (Pb.baseChange (T := Localization.AtPrime 𝔭)).equivRing
  let e₂ := StandardEtalePair.ringEquivOfMul (P₀.map (algebraMap _ (Localization.AtPrime 𝔭)))
    Q.P (by simp [P₀, hF₀]) (by simp [P₀, hG₀, ← derivative_map, hF₀])
  exact ⟨P₀, ⟨e₁.trans (e₂.trans Q.equivRing.symm)⟩⟩

end Descent

section Main

variable {A : Type u} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime]

/-- **Descending an étale neighbourhood of `A_𝔭`.** Let `R'` be an étale `A_𝔭`-algebra and `P` a
prime of `R'`. Then there is an étale `A`-algebra `N₁` and a prime `𝔫` of `N₁` over the same prime
of `A` as `P`, whose local ring is isomorphic to `R'_P`, compatibly with the maps from `A`. -/
theorem exists_etale_localization_equiv {R' : Type u} [CommRing R']
    [Algebra (Localization.AtPrime 𝔭) R'] [Algebra.Etale (Localization.AtPrime 𝔭) R']
    (P : Ideal R') [P.IsPrime] :
    ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : Algebra A N₁) (_ : Algebra.Etale A N₁)
      (𝔫 : Ideal N₁) (_ : 𝔫.IsPrime),
      𝔫.comap (algebraMap A N₁) =
        P.comap ((algebraMap (Localization.AtPrime 𝔭) R').comp (algebraMap A _)) ∧
      ∃ e : Localization.AtPrime 𝔫 ≃+* Localization.AtPrime P, ∀ a : A,
        e (algebraMap A _ a) =
          algebraMap R' _ (algebraMap (Localization.AtPrime 𝔭) R' (algebraMap A _ a)) := by
  have : Algebra.IsEtaleAt (Localization.AtPrime 𝔭) P :=
    Algebra.FormallyEtale.comp (Localization.AtPrime 𝔭) R' (Localization.AtPrime P)
  obtain ⟨f, hfP, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := Localization.AtPrime 𝔭) P
  obtain ⟨t, ht, H⟩ := exists_standardEtalePair 𝔭 (Localization.Away f)
  letI := awayAlgebra 𝔭 ht
  have := awayAlgebra_isScalarTower 𝔭 ht
  obtain ⟨P₀, ⟨e⟩⟩ := H
  letI algAN : Algebra A P₀.Ring :=
    ((algebraMap (Localization.Away t) P₀.Ring).comp (algebraMap A _)).toAlgebra
  have : IsScalarTower A (Localization.Away t) P₀.Ring := .of_algebraMap_eq' rfl
  have : Algebra.Etale A (Localization.Away t) := .of_isLocalizationAway t
  have : Algebra.Etale A P₀.Ring := .comp A (Localization.Away t) P₀.Ring
  letI : Algebra P₀.Ring (Localization.AtPrime 𝔭 ⊗[Localization.Away t] P₀.Ring) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra P₀.Ring (Localization.Away f) :=
    (e.toRingHom.comp (algebraMap P₀.Ring (Localization.AtPrime 𝔭 ⊗[_] P₀.Ring))).toAlgebra
  have hle : Submonoid.powers t ≤ 𝔭.primeCompl := Submonoid.powers_le.mpr ht
  have : IsLocalization (𝔭.primeCompl.map (algebraMap A (Localization.Away t)))
      (Localization.AtPrime 𝔭) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  have : IsLocalization (Algebra.algebraMapSubmonoid P₀.Ring
      (𝔭.primeCompl.map (algebraMap A (Localization.Away t))))
      (Localization.AtPrime 𝔭 ⊗[Localization.Away t] P₀.Ring) :=
    IsLocalization.tensorRight _ _
  have : IsLocalization (Algebra.algebraMapSubmonoid P₀.Ring
      (𝔭.primeCompl.map (algebraMap A (Localization.Away t)))) (Localization.Away f) :=
    IsLocalization.isLocalization_of_algEquiv _ { e with commutes' := fun _ ↦ rfl }
  have hdisj : Disjoint (Submonoid.powers f : Set R') P :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfP
  let Pf : Ideal (Localization.Away f) := P.map (algebraMap R' _)
  have : Pf.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ P ‹_› hdisj
  have hPf : Pf.comap (algebraMap R' _) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› hdisj
  let 𝔫 : Ideal P₀.Ring := Pf.comap (algebraMap P₀.Ring (Localization.Away f))
  have : IsLocalization.AtPrime (Localization.AtPrime Pf) 𝔫 :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid P₀.Ring
        (𝔭.primeCompl.map (algebraMap A (Localization.Away t)))) (Localization.AtPrime Pf) Pf
  let e₁ : Localization.AtPrime 𝔫 ≃ₐ[P₀.Ring] Localization.AtPrime Pf :=
    IsLocalization.algEquiv 𝔫.primeCompl _ _
  have : IsLocalization.AtPrime (Localization.AtPrime Pf) P := by
    have := IsLocalization.isLocalization_atPrime_localization_atPrime (.powers f) Pf
    have hc : P.primeCompl = (Pf.comap (algebraMap R' _)).primeCompl := by
      ext x
      rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPf]
    change IsLocalization P.primeCompl _
    rw [hc]
    exact this
  let e₂ : Localization.AtPrime Pf ≃ₐ[R'] Localization.AtPrime P :=
    IsLocalization.algEquiv P.primeCompl _ _
  have hcomm : ∀ a : A, algebraMap P₀.Ring (Localization.Away f) (algebraMap A P₀.Ring a) =
      algebraMap R' _ (algebraMap (Localization.AtPrime 𝔭) R' (algebraMap A _ a)) := by
    intro a
    have key : (1 : Localization.AtPrime 𝔭) ⊗ₜ[Localization.Away t]
        algebraMap (Localization.Away t) P₀.Ring (algebraMap A _ a) =
        algebraMap (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔭 ⊗[_] P₀.Ring)
          (algebraMap A _ a) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        IsScalarTower.algebraMap_apply A (Localization.Away t) (Localization.AtPrime 𝔭),
        Algebra.TensorProduct.tmul_one_eq_one_tmul]
    calc _ = e (algebraMap (Localization.AtPrime 𝔭) _ (algebraMap A _ a)) := congrArg e key
      _ = _ := by
        rw [e.commutes,
          IsScalarTower.algebraMap_apply (Localization.AtPrime 𝔭) R' (Localization.Away f)]
  refine ⟨P₀.Ring, inferInstance, algAN, inferInstance, 𝔫, inferInstance, ?_,
    e₁.toRingEquiv.trans e₂.toRingEquiv, fun a ↦ ?_⟩
  · have : (algebraMap P₀.Ring (Localization.Away f)).comp (algebraMap A P₀.Ring) =
        (algebraMap R' _).comp ((algebraMap (Localization.AtPrime 𝔭) R').comp (algebraMap A _)) :=
      RingHom.ext hcomm
    rw [Ideal.comap_comap, this, ← Ideal.comap_comap, hPf]
  · change e₂ (e₁ (algebraMap P₀.Ring _ (algebraMap A P₀.Ring a))) = _
    rw [e₁.commutes, IsScalarTower.algebraMap_apply P₀.Ring (Localization.Away f), hcomm,
      ← IsScalarTower.algebraMap_apply, e₂.commutes]

end Main

section Domain

variable {A : Type u} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime]

/-- Over a Noetherian normal domain, the étale neighbourhood of
`exists_etale_localization_equiv` can be taken to be a domain. -/
theorem exists_etale_isDomain_localization_equiv [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] {R' : Type u} [CommRing R']
    [Algebra (Localization.AtPrime 𝔭) R'] [Algebra.Etale (Localization.AtPrime 𝔭) R']
    (P : Ideal R') [P.IsPrime] :
    ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : IsDomain N₁) (_ : Algebra A N₁)
      (_ : Algebra.Etale A N₁) (𝔫 : Ideal N₁) (_ : 𝔫.IsPrime),
      𝔫.comap (algebraMap A N₁) =
        P.comap ((algebraMap (Localization.AtPrime 𝔭) R').comp (algebraMap A _)) ∧
      ∃ e : Localization.AtPrime 𝔫 ≃+* Localization.AtPrime P, ∀ a : A,
        e (algebraMap A _ a) =
          algebraMap R' _ (algebraMap (Localization.AtPrime 𝔭) R' (algebraMap A _ a)) := by
  obtain ⟨N₁, _, _, _, 𝔫, _, h𝔫, e, he⟩ := exists_etale_localization_equiv 𝔭 P
  have : IsNoetherianRing N₁ := Algebra.FiniteType.isNoetherianRing A N₁
  -- the kernel of `N₁ → N₁_𝔫` is killed by a single `g ∉ 𝔫`
  let I := RingHom.ker (algebraMap N₁ (Localization.AtPrime 𝔫))
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
  have hS' : ∀ x : S, ∃ m : 𝔫.primeCompl, (m : N₁) * x = 0 := by
    intro x
    have hx : (x : N₁) ∈ I := by
      rw [← hS]
      exact Submodule.subset_span x.2
    exact (IsLocalization.map_eq_zero_iff 𝔫.primeCompl _ _).mp hx
  choose s hs using hS'
  let g : N₁ := ∏ x : S, (s x : N₁)
  have hg𝔫 : g ∈ 𝔫.primeCompl := prod_mem fun x _ ↦ (s x).2
  have hgI : ∀ y ∈ I, g * y = 0 := by
    intro y hy
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ : (s ⟨x, hx⟩ : N₁) ∣ g := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
      rw [hc, mul_comm _ c, mul_assoc, hs ⟨x, hx⟩, mul_zero]
    | zero => exact mul_zero g
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  -- localise away from `g`
  let N₂ := Localization.Away g
  have : Algebra.Etale N₁ N₂ := .of_isLocalizationAway g
  have : Algebra.Etale A N₂ := .comp A N₁ N₂
  have hdisj : Disjoint (Submonoid.powers g : Set N₁) 𝔫 :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hg𝔫
  let 𝔫₂ : Ideal N₂ := 𝔫.map (algebraMap N₁ N₂)
  have : 𝔫₂.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ 𝔫 ‹_› hdisj
  have h𝔫₂ : 𝔫₂.comap (algebraMap N₁ N₂) = 𝔫 :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers g) _ ‹_› hdisj
  have : IsLocalization.AtPrime (Localization.AtPrime 𝔫₂) 𝔫 := by
    have := IsLocalization.isLocalization_atPrime_localization_atPrime (.powers g) 𝔫₂
    have hc : 𝔫.primeCompl = (𝔫₂.comap (algebraMap N₁ _)).primeCompl := by
      ext x
      rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, h𝔫₂]
    change IsLocalization 𝔫.primeCompl _
    rw [hc]
    exact this
  let e₃ : Localization.AtPrime 𝔫₂ ≃ₐ[N₁] Localization.AtPrime 𝔫 :=
    IsLocalization.algEquiv 𝔫.primeCompl _ _
  have : IsDomain (Localization.AtPrime 𝔫₂) := isDomain_localization_of_etale A 𝔫₂
  have hinj : Function.Injective (algebraMap N₂ (Localization.AtPrime 𝔫₂)) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
    have hy : algebraMap N₁ (Localization.AtPrime 𝔫₂) y = 0 := by
      rw [IsScalarTower.algebraMap_apply N₁ N₂, ← IsLocalization.mk'_spec N₂ y m, map_mul, hz,
        zero_mul]
    have hyI : y ∈ I := by
      obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff 𝔫.primeCompl _ _).mp hy
      exact (IsLocalization.map_eq_zero_iff 𝔫.primeCompl _ _).mpr ⟨c, hc⟩
    exact (IsLocalization.mk'_eq_zero_iff y m).mpr
      ⟨⟨g, Submonoid.mem_powers g⟩, hgI y hyI⟩
  have : IsDomain N₂ := hinj.isDomain _
  refine ⟨N₂, inferInstance, inferInstance, inferInstance, inferInstance, 𝔫₂, inferInstance, ?_,
    e₃.toRingEquiv.trans e, fun a ↦ ?_⟩
  · rw [IsScalarTower.algebraMap_eq A N₁ N₂, ← Ideal.comap_comap, h𝔫₂, h𝔫]
  · rw [← he]
    change e (e₃ (algebraMap N₁ _ (algebraMap A N₁ a))) = _
    rw [e₃.commutes]
    rfl

end Domain

section FractionField

variable {A N : Type*} [CommRing A] [IsDomain A] [CommRing N] [IsDomain N] [Algebra A N]
  [Algebra.Etale A N]

omit [IsDomain A] in
variable (A N) in
lemma algebraMapSubmonoid_le_nonZeroDivisors :
    Algebra.algebraMapSubmonoid N (nonZeroDivisors A) ≤ nonZeroDivisors N := by
  rintro _ ⟨a, ha, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h ↦ one_ne_zero (α := N) ?_
  refine Module.Flat.isSMulRegular_of_nonZeroDivisors (M := N) ha ?_
  simp [Algebra.smul_def, h]

instance : IsLocalization (Algebra.algebraMapSubmonoid N (nonZeroDivisors A))
    (N ⊗[A] FractionRing A) :=
  IsLocalization.tensor (S := N) (FractionRing A) (nonZeroDivisors A)

variable (A N) in
/-- The generic fibre `N ⊗_A K` of an étale domain `N` over a domain `A` is a field. -/
theorem isField_tensor_fractionRing : IsField (N ⊗[A] FractionRing A) := by
  have : IsDomain (N ⊗[A] FractionRing A) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (algebraMapSubmonoid_le_nonZeroDivisors A N)
  let φ := (Algebra.TensorProduct.comm A N (FractionRing A)).toRingEquiv
  have : IsDomain (FractionRing A ⊗[A] N) := φ.toMulEquiv.isDomain_iff.mp inferInstance
  have : Module.Finite (FractionRing A) (FractionRing A ⊗[A] N) := by
    have : Module.Free (FractionRing A) (FractionRing A ⊗[A] N) :=
      Module.Free.of_divisionRing _ _
    exact Algebra.FormallyUnramified.finite_of_free _ _
  have : IsArtinianRing (FractionRing A ⊗[A] N) := IsArtinianRing.of_finite (FractionRing A) _
  exact MulEquiv.isField (IsArtinianRing.isField_of_isDomain _) φ.toMulEquiv

variable (A N) in
/-- The generic fibre `N ⊗_A K` of an étale domain `N` over a domain `A` is a fraction field
of `N`. -/
theorem isFractionRing_tensor_fractionRing : IsFractionRing N (N ⊗[A] FractionRing A) := by
  letI := (isField_tensor_fractionRing A N).toField
  have hinj := IsLocalization.injective (N ⊗[A] FractionRing A)
    (algebraMapSubmonoid_le_nonZeroDivisors A N)
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid N (nonZeroDivisors A)) _
    (algebraMapSubmonoid_le_nonZeroDivisors A N) fun r hr ↦ ?_
  refine IsUnit.mk0 _ fun h ↦ nonZeroDivisors.ne_zero hr (hinj ?_)
  rw [h, map_zero]

end FractionField

end SemistableReduction.EtaleDescent
