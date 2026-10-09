/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.NonzeroCharacter

/-!
# Non-degeneracy of `temperedPi1 [Y/A]` from a nontrivial character, for any target

`InducedTate.exists_open_normal_infinite_quotient_of_ne_one_gen`: the argument of
`InducedTate.exists_open_normal_infinite_quotient_of_ne_one` for any object `Z` of `[Spec R / A]`
whose fibre elements over a common geometric point are related by endomorphisms of `Z`, and any
deck torsor `X₀` of the scheme case with a morphism `X₀ ⟶ Res Z` injective on fibres.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

namespace InducedTate

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} {R : Type u} [CommRing R] [Algebra K R]
  (A : Type u) [Group A] [MulSemiringAction A R]
  (A' : Type u) [Group A'] [Subsingleton A'] [MulSemiringAction A' R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Non-degeneracy of `temperedPi1 [Spec R / A]` from a nontrivial deck character**, for any
object `Z` whose fibre elements over a common geometric point are related by endomorphisms, and
any deck torsor `X₀` with a morphism `ι : X₀ ⟶ Res Z` injective on fibres. -/
theorem exists_open_normal_infinite_quotient_of_ne_one_gen (Z : TempObj O R A)
    (hdeck : ∀ q q' : TempObj.PreFibre Ω V hV Z, q.1.1 = q'.1.1 →
      ∃ e : Z ⟶ Z, (tempFibre O R A V hV).map e ⟦q⟧ = ⟦q'⟧)
    (X₀ : TempObj O R A') (δ : Multiplicative ℤ →* Aut X₀)
    (x₀ : (tempFibre O R A' V hV).obj X₀)
    (htors : FibreAut.IsDeckTorsor (F := tempFibre O R A' V hV) X₀ δ)
    (ι : X₀ ⟶ (resFunctor O R A A').obj Z)
    (hι : Function.Injective ((tempFibre O R A' V hV).map ι))
    (hχ : ∃ τ, FibreAut.deckCharacter X₀ δ x₀ htors τ ≠ 1) :
    ∃ N : Subgroup (temperedPi1 O R A V hV), IsOpen (N : Set (temperedPi1 O R A V hV)) ∧
      N.Normal ∧ Infinite (temperedPi1 O R A V hV ⧸ N) := by
  classical
  haveI := Z.Lv.L.finite
  let F := tempFibre O R A V hV
  let S : Set (Σ c, F.obj c) :=
    Set.range fun t : {t : Z.Lv.L.B →ₐ[R] Ω // ∃ q : TempObj.PreFibre Ω V hV Z, q.1.1 = t} =>
      (⟨Z, ⟦t.2.choose⟧⟩ : Σ c, F.obj c)
  have hS : S.Finite := Set.finite_range _
  let M := FibreAut.stabilizer F hS.toFinset
  -- `M` acts trivially on the whole fibre of `Z`.
  have hfix : ∀ γ ∈ M, ∀ z : F.obj Z, γ.app Z z = z := by
    intro γ hγ z
    induction z using Quotient.inductionOn with | h q => ?_
    have hex : ∃ q' : TempObj.PreFibre Ω V hV Z, q'.1.1 = q.1.1 := ⟨q, rfl⟩
    obtain ⟨e, he⟩ := hdeck hex.choose q hex.choose_spec
    have hmem : (⟨Z, ⟦hex.choose⟧⟩ : Σ c, F.obj c) ∈ hS.toFinset :=
      (Set.Finite.mem_toFinset hS).2 ⟨⟨q.1.1, hex⟩, rfl⟩
    have hq₀ : γ.app Z ⟦hex.choose⟧ = ⟦hex.choose⟧ := hγ _ hmem
    rw [← he, FibreAut.app_naturality, hq₀]
  have hnorm : M.Normal := ⟨fun γ hγ g p hp => by
    obtain ⟨t, rfl⟩ := (Set.Finite.mem_toFinset hS).1 hp
    change (g * γ * g⁻¹).app Z _ = _
    rw [FibreAut.mul_app, FibreAut.mul_app, hfix γ hγ, FibreAut.app_inv_app]⟩
  -- An element of `temperedPi1 Y` whose image lies in `M` has trivial character.
  let e := resFibreIso O R A A' V hV
  have key : ∀ τ, restrictHom O R A A' V hV τ ∈ M →
      FibreAut.deckCharacter X₀ δ x₀ htors τ = 1 := by
    intro τ hτ
    let y := (tempFibre O R A' V hV).map ι x₀
    have h1 : e.hom.app Z (τ.app ((resFunctor O R A A').obj Z) y) = e.hom.app Z y := by
      have := hfix _ hτ (e.hom.app Z y)
      rwa [restrictHom, FibreAut.restrict_app, Iso.hom_inv_id_app_apply] at this
    have h2 : τ.app ((resFunctor O R A A').obj Z) y = y := by
      have := congrArg (e.inv.app Z) h1
      rwa [Iso.hom_inv_id_app_apply, Iso.hom_inv_id_app_apply] at this
    have h3 : (tempFibre O R A' V hV).map ι (τ.app _ x₀) = y :=
      (FibreAut.app_naturality τ ι x₀).symm.trans h2
    have h4 := hι h3
    exact FibreAut.deckCharacterFun_eq X₀ δ x₀ htors
      (by rw [FibreAut.deckAct_one]; exact h4.symm)
  obtain ⟨τ, hτ⟩ := hχ
  refine ⟨M, FibreAut.isOpen_stabilizer _ _, hnorm, Infinite.of_injective
    (fun k : ℤ =>
      (QuotientGroup.mk (restrictHom O R A A' V hV (τ ^ k)) : temperedPi1 O R A V hV ⧸ M))
    fun k m hkm => ?_⟩
  rw [QuotientGroup.eq, ← map_inv, ← map_mul] at hkm
  have h := key _ hkm
  rw [map_mul, map_inv, map_zpow, map_zpow, ← zpow_neg, ← zpow_add] at h
  have := multiplicativeInt_zpow_eq_one hτ h
  omega

end

end InducedTate

end TemperedFundamentalGroups
