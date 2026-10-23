/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Filtration

/-!
# Local criteria for killing the Kähler differentials (Blueprint §12.8, M2.5 (f))

Generic algebra for the uniform bound on the differentials of the level rings of the algebraized
coverings: "`c` kills `Ω[S⁄R]`" (`KaehlerLocal.Kills R S c`) is checked

* on generators (**`KaehlerLocal.kills_of_adjoin`**): if `c • d x = 0` for a set of algebra
  generators `x` (Leibniz rule);
* after a formally unramified change of the base (**`KaehlerLocal.kills_of_base`**): for
  `R → R' → S` with `Ω[R'⁄R] = 0` (e.g. `R'` a quotient or a localization of `R`),
  `Ω[S⁄R] = Ω[S⁄R']` (`KaehlerDifferential.exact_mapBaseChange_map`);
* Zariski-locally on `S` (**`KaehlerLocal.kills_of_away`**): on the localizations `S[1/aⱼ]` for
  elements generating the unit ideal (`Ω[S[1/a]⁄R] = Ω[S⁄R][1/a]`); this includes finite
  products (localizations at idempotents);
* on a formal patch (**`KaehlerLocal.kills_of_patch`**): for a finite `R`-algebra `G` over a
  Noetherian `R`, `f ∈ R`, from `G[1/f]` and from an `R̂`-algebra `NF` which is the base change
  of `G` to the `f`-adic completion `R̂` (`Ω[NF⁄R̂] = R̂ ⊗ Ω[G⁄R]`, the Krull intersection
  theorem and `f`-torsion).

The local computations: **`KaehlerLocal.kummer_kills`** (`s t = π`, `sᵉ`, `tᵉ` in the base, `e`
invertible: `π^(e-1)` kills `d s` and `d t`) and **`KaehlerLocal.root_kills`** (`t'ᵉ = t` in the
base, `e` invertible: `t` kills `d t'`).
-/

universe u

open TensorProduct

namespace KaehlerLocal

variable (R : Type u) {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- `c` kills the module of differentials `Ω[S⁄R]`. -/
def Kills (c : S) : Prop := ∀ ω : Ω[S⁄R], c • ω = 0

/-- **Killing the differentials on algebra generators.** -/
theorem kills_of_adjoin {c : S} {s : Set S} (hs : Algebra.adjoin R s = ⊤)
    (hc : ∀ x ∈ s, c • KaehlerDifferential.D R S x = 0) : Kills R c := by
  have hall : ∀ x : S, c • KaehlerDifferential.D R S x = 0 := by
    intro x
    have hx : x ∈ Algebra.adjoin R s := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hc x hx
    | algebraMap r => rw [Derivation.map_algebraMap, smul_zero]
    | add x y _ _ hx hy => rw [map_add, smul_add, hx, hy, add_zero]
    | mul x y _ _ hx hy =>
      rw [Derivation.leibniz, smul_add, smul_comm c x, smul_comm c y, hx, hy, smul_zero,
        smul_zero, add_zero]
  intro ω
  have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact hall x
  | zero => exact smul_zero c
  | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
  | smul a y _ hy => rw [smul_comm, hy, smul_zero]

/-- **Changing the base along a formally unramified map**: for `R → R' → S` with
`Ω[R'⁄R] = 0`, an element killing `Ω[S⁄R']` kills `Ω[S⁄R]`. -/
theorem kills_of_base (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' S]
    [IsScalarTower R R' S] [Subsingleton Ω[R'⁄R]] {c : S} (hc : Kills R' c) : Kills R c := by
  intro ω
  have h0 : KaehlerDifferential.map R R' S S (c • ω) = 0 := by rw [map_smul]; exact hc _
  obtain ⟨y, hy⟩ := (KaehlerDifferential.exact_mapBaseChange_map R R' S (c • ω)).1 h0
  rw [← hy, Subsingleton.elim y 0, map_zero]

/-- `Ω[R'⁄R] = 0` for a surjective `R → R'`. -/
lemma subsingleton_of_surjective (R' : Type u) [CommRing R'] [Algebra R R']
    (h : Function.Surjective (algebraMap R R')) : Subsingleton Ω[R'⁄R] :=
  KaehlerDifferential.subsingleton_of_surjective R R' h

/-- An element of a module killed by powers of a family generating the unit ideal is zero. -/
lemma eq_zero_of_pow_smul {M : Type u} [AddCommGroup M] [Module S M] {ι : Type*} {a : ι → S}
    (ha : Ideal.span (Set.range a) = ⊤) {z : M} (hz : ∀ j, ∃ k : ℕ, a j ^ k • z = 0) :
    z = 0 := by
  let I : Ideal S := LinearMap.ker (LinearMap.toSpanSingleton S M z)
  have hrad : ∀ j, a j ∈ I.radical := fun j ↦ by
    obtain ⟨k, hk⟩ := hz j
    exact ⟨k, hk⟩
  have htop : I.radical = ⊤ := by
    rw [eq_top_iff, ← ha, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hrad j
  have h1 : (1 : S) ∈ I := by
    rw [Ideal.radical_eq_top.1 htop]
    trivial
  simpa [I] using h1

/-- **Killing the differentials Zariski-locally on `S`**: for `aⱼ ∈ S` generating the unit ideal
and localizations `Sⱼ = S[1/aⱼ]`, if the image of `c` kills every `Ω[Sⱼ⁄R]`, then `c` kills
`Ω[S⁄R]`. -/
theorem kills_of_away {ι : Type*} {a : ι → S} (ha : Ideal.span (Set.range a) = ⊤)
    (S' : ι → Type u) [∀ j, CommRing (S' j)] [∀ j, Algebra S (S' j)] [∀ j, Algebra R (S' j)]
    [∀ j, IsScalarTower R S (S' j)] [∀ j, IsLocalization.Away (a j) (S' j)] {c : S}
    (hc : ∀ j, Kills R (algebraMap S (S' j) c)) : Kills R c := by
  intro ω
  refine eq_zero_of_pow_smul ha fun j ↦ ?_
  have h0 : KaehlerDifferential.map R R S (S' j) (c • ω) =
      KaehlerDifferential.map R R S (S' j) 0 := by
    rw [map_smul, map_zero, ← algebraMap_smul (S' j) c]
    exact hc j _
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (a j)) h0
  exact ⟨k, by simpa [Submonoid.smul_def] using hk⟩

/-! ### Formal patches -/

section Patch

variable {R} [IsNoetherianRing R] (f : R) {G : Type u} [CommRing G] [Algebra R G]
  [Module.Finite R G] (P : Type u) [CommRing P] [Algebra G P] [Algebra R P] [IsScalarTower R G P]
  [IsLocalization.Away (algebraMap R G f) P] (NF : Type u) [CommRing NF] [Algebra G NF]
  [Algebra (AdicCompletion (Ideal.span {f}) R) NF] [Algebra R NF] [IsScalarTower R G NF]
  [IsScalarTower R (AdicCompletion (Ideal.span {f}) R) NF]
  [Algebra.IsPushout R (AdicCompletion (Ideal.span {f}) R) G NF]

/-- **Killing the differentials on a formal patch**: for a finite algebra `G` over a Noetherian
ring `R`, `f ∈ R`, the localization `P = G[1/f]` and the base change `NF = R̂ ⊗_R G` to the
`f`-adic completion, a constant `c ∈ R` killing `Ω[P⁄R]` and `Ω[NF⁄R̂]` kills `Ω[G⁄R]`. -/
theorem kills_of_patch {c : R} (hP : Kills R (algebraMap R P c))
    (hN : Kills (AdicCompletion (Ideal.span {f}) R) (algebraMap R NF c)) :
    Kills R (algebraMap R G c) := by
  intro ω
  set z := algebraMap R G c • ω with hz
  -- `f`-torsion, from `P`
  have hzP : KaehlerDifferential.map R R G P z = KaehlerDifferential.map R R G P 0 := by
    rw [hz, map_smul, map_zero, ← algebraMap_smul P (algebraMap R G c),
      ← IsScalarTower.algebraMap_apply R G P]
    exact hP _
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    IsLocalizedModule.exists_of_eq (S := Submonoid.powers (algebraMap R G f)) hzP
  have hk' : f ^ k • z = 0 := by
    rw [smul_zero] at hk
    rw [← algebraMap_smul G, map_pow]
    exact hk
  -- `z ∈ ⋂ fⁿ Ω`, from `NF`
  have hzN : (KaehlerDifferential.map R (AdicCompletion (Ideal.span {f}) R) G NF) z = 0 := by
    rw [hz, map_smul, ← algebraMap_smul NF (algebraMap R G c),
      ← IsScalarTower.algebraMap_apply R G NF]
    exact hN _
  have hb := KaehlerDifferential.isBaseChange R (AdicCompletion (Ideal.span {f}) R) G NF
  have h1 : (1 : AdicCompletion (Ideal.span {f}) R) ⊗ₜ[R] z = 0 := by
    apply hb.equiv.injective
    rw [IsBaseChange.equiv_tmul, one_smul, map_zero]
    exact hzN
  haveI : Module.Finite R Ω[G⁄R] := Module.Finite.trans G Ω[G⁄R]
  have hof := congrArg (AdicCompletion.ofTensorProduct (Ideal.span {f}) Ω[G⁄R]) h1
  rw [AdicCompletion.ofTensorProduct_tmul, one_smul, map_zero] at hof
  have hmem : z ∈ (⨅ i : ℕ, Ideal.span {f} ^ i • ⊤ : Submodule R Ω[G⁄R]) := by
    refine Submodule.mem_iInf _ |>.2 fun n ↦ ?_
    have := congrArg (fun y ↦ y.1 n) hof
    simp only [AdicCompletion.of_apply] at this
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  obtain ⟨⟨r, hr⟩, hrz⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff _ z).1 hmem
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  have : ∀ j : ℕ, z = (s * f) ^ j • z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hrz, ← ih]
  rw [this k, mul_pow, mul_smul, hk', smul_zero]

end Patch

/-! ### Local computations -/

section Local

variable {R} {C : Type u} [CommRing C] [Algebra R C]

/-- `xᵉ` in the base and `e` invertible: `x^(e-1)` kills `d x`. -/
lemma pow_pred_smul_D {x : C} {e : ℕ} (he : IsUnit (e : C))
    (hx : x ^ e ∈ Set.range (algebraMap R C)) :
    x ^ (e - 1) • KaehlerDifferential.D R C x = 0 := by
  obtain ⟨r, hr⟩ := hx
  have h := (KaehlerDifferential.D R C).leibniz_pow x e
  rw [← hr, Derivation.map_algebraMap, eq_comm, ← Nat.cast_smul_eq_nsmul C] at h
  exact he.smul_left_cancel.1 (h.trans (smul_zero _).symm)

/-- **The differentials of a Kummer algebra** `s t = π`, `sᵉ, tᵉ` in the base, `e` invertible:
`π^(e-1)` kills `d s` and `d t`. -/
theorem kummer_kills {s t : C} {π : R} {e : ℕ} (he : IsUnit (e : C))
    (hs : s ^ e ∈ Set.range (algebraMap R C)) (ht : t ^ e ∈ Set.range (algebraMap R C))
    (hst : s * t = algebraMap R C π) :
    algebraMap R C π ^ (e - 1) • KaehlerDifferential.D R C s = 0 ∧
      algebraMap R C π ^ (e - 1) • KaehlerDifferential.D R C t = 0 := by
  rw [← hst, mul_pow]
  refine ⟨?_, ?_⟩
  · rw [mul_comm, mul_smul, pow_pred_smul_D he hs, smul_zero]
  · rw [mul_smul, pow_pred_smul_D he ht, smul_zero]

/-- **The differentials of a root** `t'ᵉ = t`, `e` invertible: `t` kills `d t'`. -/
theorem root_kills {t' : C} {t : R} {e : ℕ} (he : IsUnit (e : C)) (he0 : e ≠ 0)
    (ht : t' ^ e = algebraMap R C t) :
    algebraMap R C t • KaehlerDifferential.D R C t' = 0 := by
  have h := pow_pred_smul_D he ⟨t, ht.symm⟩
  rw [← ht, ← Nat.succ_pred_eq_of_ne_zero he0, pow_succ', mul_smul, Nat.pred_eq_sub_one, h,
    smul_zero]

end Local

end KaehlerLocal
