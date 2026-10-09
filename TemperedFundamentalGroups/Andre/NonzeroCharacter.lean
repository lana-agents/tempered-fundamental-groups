/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TransferTate

/-!
# Non-degeneracy from a nontrivial `ℤ`-character (Blueprint §10.3.2, §10.3.6)

`InducedTate.exists_open_normal_infinite_quotient_of_surjective` needs the character
`temperedPi1 Y → ℤ` of `X₀` to be surjective. Here only a **nontrivial** value is needed: if
`χ(τ) ≠ 1` for one `τ`, then `χ` has image `nℤ` with `n ≠ 0`, and the same argument (the powers
`τ ^ k` have pairwise distinct images in the quotient by the kernel `N` of the action on the fibre
of `Ind X₀`) shows that `temperedPi1 [Y/A]` has an open normal subgroup with infinite quotient.

This is the form Theorem B takes when the special fibre map `Z(𝒴) → Z(𝒯_Tate)` of a W-model
over the Tate model only has fibres with finitely many connected components (so the Tate loop
lifts to `Z(𝒴)` only up to a finite index `n`).

* `TateObject.character_zpow_ne_one`: a nontrivial value of a character to `ℤ` has
  infinite order.
* `InducedTate.exists_open_normal_infinite_quotient_of_ne_one`.
* `TateOrbicurve.nondegenerate_of_character_ne_one`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

/-- In `Multiplicative ℤ`, a nontrivial element has infinite order. -/
lemma multiplicativeInt_zpow_eq_one {x : Multiplicative ℤ} (hx : x ≠ 1) {k : ℤ}
    (h : x ^ k = 1) : k = 0 := by
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_zpow, toAdd_one, smul_eq_mul] at h'
  rcases mul_eq_zero.1 h' with hk | hk
  · exact hk
  · exact absurd (by rw [← ofAdd_toAdd x, hk, ofAdd_zero]) hx

namespace InducedTate

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} {R : Type u} [CommRing R] [Algebra K R]
  [IsReduced R] (A : Type u) [Group A] [Finite A] [MulSemiringAction A R] [SMulCommClass A K R]
  (A' : Type u) [Group A'] [Subsingleton A'] [MulSemiringAction A' R] (D : TateObject.Data O R)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Non-degeneracy of `temperedPi1 [Y/A]` from a nontrivial character.** If the character
`temperedPi1 Y → ℤ` of `X₀` takes one value `≠ 1`, then `temperedPi1 [Spec R / A]` has an open
normal subgroup with infinite quotient: the kernel of its action on the fibre of `Ind X₀`. -/
theorem exists_open_normal_infinite_quotient_of_ne_one
    (hχ : ∃ τ, TateObject.character (A := A') D V hV τ ≠ 1) :
    ∃ N : Subgroup (temperedPi1 O R A V hV), IsOpen (N : Set (temperedPi1 O R A V hV)) ∧
      N.Normal ∧ Infinite (temperedPi1 O R A V hV ⧸ N) := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  let Z := indObj A A' D
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
    have h₀ : hex.choose.1.1 = q.1.1 := hex.choose_spec
    have hbase : hex.choose.1.2.1.1 = q.1.2.1.1 := Subtype.ext (hex.choose.2.trans
      ((congrArg (fun t => (Z.Lv.sp V hV t : Z.Lv.c.scheme)) h₀).trans q.2.symm))
    obtain ⟨d, hd, -⟩ :=
      (TateObject.decomp (A := A') D).existsUnique_deckCode _ (indLv_ρs A A' D) hbase
    have hmem : (⟨Z, ⟦hex.choose⟧⟩ : Σ c, F.obj c) ∈ hS.toFinset :=
      (Set.Finite.mem_toFinset hS).2 ⟨⟨q.1.1, hex⟩, rfl⟩
    have hq₀ : γ.app Z ⟦hex.choose⟧ = ⟦hex.choose⟧ := hγ _ hmem
    have hdeck : F.map (indDeck A A' D d) ⟦hex.choose⟧ = ⟦q⟧ := by
      change (⟦TempObj.preMap V hV (indDeck A A' D d) hex.choose⟧ : F.obj Z) = ⟦q⟧
      exact congrArg _ (Subtype.ext (Prod.ext ((AlgHom.comp_id _).trans h₀) hd))
    rw [← hdeck, FibreAut.app_naturality, hq₀]
  have hnorm : M.Normal := ⟨fun γ hγ g p hp => by
    obtain ⟨t, rfl⟩ := (Set.Finite.mem_toFinset hS).1 hp
    change (g * γ * g⁻¹).app Z _ = _
    rw [FibreAut.mul_app, FibreAut.mul_app, hfix γ hγ, FibreAut.app_inv_app]⟩
  -- An element of `temperedPi1 Y` whose image lies in `M` has trivial character.
  let x₀ := TateObject.basePoint (A := A') D V hV
  let e := resFibreIso O R A A' V hV
  have key : ∀ τ, restrictHom O R A A' V hV τ ∈ M → TateObject.character D V hV τ = 1 := by
    intro τ hτ
    let y := (tempFibre O R A' V hV).map (ι A A' D) x₀
    have h1 : e.hom.app Z (τ.app ((resFunctor O R A A').obj Z) y) = e.hom.app Z y := by
      have := hfix _ hτ (e.hom.app Z y)
      rwa [restrictHom, FibreAut.restrict_app, Iso.hom_inv_id_app_apply] at this
    have h2 : τ.app ((resFunctor O R A A').obj Z) y = y := by
      have := congrArg (e.inv.app Z) h1
      rwa [Iso.hom_inv_id_app_apply, Iso.hom_inv_id_app_apply] at this
    have h3 : (tempFibre O R A' V hV).map (ι A A' D) (τ.app _ x₀) = y :=
      (FibreAut.app_naturality τ (ι A A' D) x₀).symm.trans h2
    have h4 := fibreMap_ι_injective A A' D V hV h3
    exact FibreAut.deckCharacterFun_eq (TateObject.X₀ (A := A') D) (TateObject.deck D)
      (TateObject.basePoint D V hV) (TateObject.isDeckTorsor D V hV)
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

namespace TateOrbicurve

open Orbicurve

variable {K : Type u} [Field K] {O : ValuationSubring K} {W : WeierstrassCurve K} [DecidableEq K]
  (A : Type u) [Group A] [Finite A] (A' : Type u) [Group A'] [Subsingleton A']
  {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}
  [MulSemiringAction A (geomOrbicurveRing W ℓ M)] [SMulCommClass A K (geomOrbicurveRing W ℓ M)]
  [MulSemiringAction A' (geomOrbicurveRing W ℓ M)]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra (geomOrbicurveRing W ℓ M) Ω]
  [IsScalarTower K (geomOrbicurveRing W ℓ M) Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Non-degeneracy for IUT's orbicurve `[Y/A]` from a nontrivial character**: for
`Y = E_q ∖ (E[ℓ] + M)` and a finite group `A` acting `K`-linearly on `Y`, if the continuous
character `temperedPi1 Y → ℤ` of the Tate curve takes a value `≠ 1` (i.e. has image `nℤ`,
`n ≠ 0`), then `temperedPi1 [Y/A]` has an open normal subgroup with infinite quotient. -/
theorem nondegenerate_of_character_ne_one {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal O)
    (hne : ∃ τ, character A' ℓ M V hV hW hπ hπm τ ≠ 1) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) :=
  InducedTate.exists_open_normal_infinite_quotient_of_ne_one A A' (data hW hπ hπm ℓ M) V hV hne

end TateOrbicurve

end TemperedFundamentalGroups
