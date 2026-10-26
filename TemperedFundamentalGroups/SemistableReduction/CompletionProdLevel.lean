/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CompletionProd
import TemperedFundamentalGroups.SemistableReduction.AdmissibleLift
import TemperedFundamentalGroups.SemistableReduction.CoveringTransport

/-!
# Naturality of the node idempotents of lemma F (Blueprint §12.8, M2.3)

Lemma F (`CompletionProd`) splits the `f`-adic completion of a Noetherian ring into the local
completions at the nodes `𝔪 j`, with idempotents `CompletionProd.idem j`. Here:

* **`CompletionProd.map_idem`**: for a ring map `g : R₁ → R₂` with `g(f₁) ⊆ (f₂)` and
  `g(𝔪₁ j) ⊆ 𝔪₂ j`, the completion map `CompletionMap.map g` sends `idem₁ j` to `idem₂ j`
  (`equiv_map_idem` for ring isomorphisms, `Admissible.hatEquiv_idem` for `k`-algebra
  isomorphisms);
* **nilpotent thickenings**: for a surjection `q : R' → R''` with nilpotent kernel, the pull-backs
  `q⁻¹(𝔪'' j)` of node data for `q f'` are node data for `f'` (`isMaximal_comap`,
  `injective_comap`, `mem_comap`, `iInf_comap_le_radical`), and `map_idem_comap`;
* **`CompletionQuot.ψ_eq_map`**: the completion map `ψ : R̂ → (R/J)^∧` is `CompletionMap.map` of
  the quotient map;
* **`AdmissibleLift.ψ_idem`** (and `ψ_idem_comap`): the reduction `ψ` of the level idempotents is
  the transport (`Admissible.hatEquiv`) of the idempotents of the special fibre, i.e. the
  hypothesis `hε` of the lift data `AdmissibleLift.KummerLift`.
-/

universe u v w

namespace SemistableReduction

namespace CompletionMap

variable {R₁ : Type u} [CommRing R₁] {R₂ : Type v} [CommRing R₂] {I₁ : Ideal R₁} {I₂ : Ideal R₂}

lemma map_congr {g g' : R₁ →+* R₂} (hg : g = g') (h : I₁.map g ≤ I₂) (h' : I₁.map g' ≤ I₂)
    (x : AdicCompletion I₁ R₁) : map g h x = map g' h' x := by
  subst hg
  rfl

end CompletionMap

namespace CompletionQuot

variable {R : Type u} [CommRing R] (I J : Ideal R) (I' : Ideal (R ⧸ J))
  (hI : I.map (Ideal.Quotient.mk J) = I')

/-- **`ψ` is the completion map of `R → R/J`.** -/
theorem ψ_eq_map (x : AdicCompletion I R) :
    ψ I J I' hI x = CompletionMap.map (Ideal.Quotient.mk J) hI.le x := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [ψ, AdicCompletion.evalₐ_liftAlgHom, CompletionMap.evalₐ_map, lev, AlgHom.comp_apply]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr, Ideal.quotientMap_mk]
  rfl

end CompletionQuot

namespace CompletionProd

open Function

/-! ### Naturality of the idempotents -/

section Naturality

variable {R₁ : Type u} [CommRing R₁] {R₂ : Type w} [CommRing R₂] {ι : Type v}
  {f₁ : R₁} {𝔪₁ : ι → Ideal R₁} {f₂ : R₂} {𝔪₂ : ι → Ideal R₂}
  (g : R₁ →+* R₂) (hg : (Ideal.span {f₁}).map g ≤ Ideal.span {f₂})
  (hm : ∀ j, (𝔪₁ j).map g ≤ 𝔪₂ j)

include hm in
lemma proj_map (hf₁ : ∀ j, f₁ ∈ 𝔪₁ j) (hf₂ : ∀ j, f₂ ∈ 𝔪₂ j) (i : ι)
    (x : AdicCompletion (Ideal.span {f₁}) R₁) :
    proj hf₂ i (CompletionMap.map g hg x) = CompletionMap.map g (hm i) (proj hf₁ i x) := by
  rw [proj, proj, CompletionMap.map_comp, CompletionMap.map_comp]
  exact CompletionMap.map_congr (by rw [RingHom.id_comp, RingHom.comp_id]) _ _ x

variable [Finite ι] [DecidableEq ι] [IsNoetherianRing R₁] [IsNoetherianRing R₂]
  [∀ j, (𝔪₁ j).IsMaximal] [∀ j, (𝔪₂ j).IsMaximal]
  (hinj₁ : Injective 𝔪₁) (hf₁ : ∀ j, f₁ ∈ 𝔪₁ j) (hrad₁ : ⨅ j, 𝔪₁ j ≤ (Ideal.span {f₁}).radical)
  (hinj₂ : Injective 𝔪₂) (hf₂ : ∀ j, f₂ ∈ 𝔪₂ j) (hrad₂ : ⨅ j, 𝔪₂ j ≤ (Ideal.span {f₂}).radical)

include hm in
/-- **Naturality of the idempotents of lemma F**: if `g(f₁) ⊆ (f₂)` and `g(𝔪₁ j) ⊆ 𝔪₂ j`, the
completion map of `g` sends `idem₁ j` to `idem₂ j`. -/
theorem map_idem (j : ι) :
    CompletionMap.map g hg (idem hinj₁ hf₁ hrad₁ j) = idem hinj₂ hf₂ hrad₂ j := by
  refine (equiv hinj₂ hf₂ hrad₂).injective ?_
  rw [equiv_idem]
  funext i
  change proj hf₂ i (CompletionMap.map g hg (idem hinj₁ hf₁ hrad₁ j)) = _
  rw [proj_map g hg hm hf₁ hf₂,
    show proj hf₁ i (idem hinj₁ hf₁ hrad₁ j) = Pi.single (M := fun i ↦ AdicCompletion (𝔪₁ i) R₁)
      j 1 i from congrFun (equiv_idem hinj₁ hf₁ hrad₁ j) i]
  by_cases hij : i = j
  · subst hij
    simp only [Pi.single_eq_same, map_one]
  · simp only [Pi.single_eq_of_ne hij, map_zero]

/-- **The idempotents of lemma F under a ring isomorphism** `e` with `e(f₁) = (f₂)` and
`e(𝔪₁ j) ⊆ 𝔪₂ j`. -/
theorem equiv_map_idem (e : R₁ ≃+* R₂)
    (he : (Ideal.span {f₁}).map (e : R₁ →+* R₂) = Ideal.span {f₂})
    (hme : ∀ j, (𝔪₁ j).map (e : R₁ →+* R₂) ≤ 𝔪₂ j) (j : ι) :
    CompletionMap.equiv e he (idem hinj₁ hf₁ hrad₁ j) = idem hinj₂ hf₂ hrad₂ j :=
  map_idem (e : R₁ →+* R₂) he.le hme hinj₁ hf₁ hrad₁ hinj₂ hf₂ hrad₂ j

end Naturality

/-! ### Nilpotent thickenings -/

section Thickening

variable {R' : Type u} [CommRing R'] {R'' : Type w} [CommRing R''] (q : R' →+* R'')
  (hq : Surjective q) {f' : R'} {f'' : R''} (hqf : q f' = f'') {ι : Type v}
  (𝔪'' : ι → Ideal R'')

include hq in
/-- The pull-back of a node along a surjection is a maximal ideal. -/
lemma isMaximal_comap [∀ j, (𝔪'' j).IsMaximal] (j : ι) : ((𝔪'' j).comap q).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective q hq

include hq in
lemma injective_comap (hinj'' : Injective 𝔪'') : Injective fun j ↦ (𝔪'' j).comap q :=
  (Ideal.comap_injective_of_surjective q hq).comp hinj''

include hqf in
lemma mem_comap (hf'' : ∀ j, f'' ∈ 𝔪'' j) (j : ι) : f' ∈ (𝔪'' j).comap q := by
  rw [Ideal.mem_comap, hqf]
  exact hf'' j

include hqf in
lemma map_span_le : (Ideal.span {f'}).map q ≤ Ideal.span {f''} := by
  rw [Ideal.map_span, Set.image_singleton, hqf]

include hq hqf in
/-- For a surjection `q` with nilpotent kernel, the radical condition of lemma F lifts. -/
lemma iInf_comap_le_radical (hker : RingHom.ker q ≤ nilradical R')
    (hrad'' : ⨅ j, 𝔪'' j ≤ (Ideal.span {f''}).radical) :
    ⨅ j, (𝔪'' j).comap q ≤ (Ideal.span {f'}).radical := by
  rw [← Ideal.comap_iInf]
  refine (Ideal.comap_mono hrad'').trans ?_
  rw [Ideal.comap_radical, ← hqf, ← Set.image_singleton, ← Ideal.map_span,
    Ideal.comap_map_of_surjective q hq, ← RingHom.ker_eq_comap_bot, Ideal.radical_le_radical_iff]
  exact sup_le Ideal.le_radical (hker.trans (Ideal.radical_mono bot_le))

variable [Finite ι] [DecidableEq ι] [IsNoetherianRing R'] [IsNoetherianRing R'']
  [∀ j, (𝔪'' j).IsMaximal] [∀ j, ((𝔪'' j).comap q).IsMaximal]
  (hker : RingHom.ker q ≤ nilradical R') (hinj'' : Injective 𝔪'') (hf'' : ∀ j, f'' ∈ 𝔪'' j)
  (hrad'' : ⨅ j, 𝔪'' j ≤ (Ideal.span {f''}).radical)

/-- **Idempotents of lemma F along a nilpotent thickening** `q : R' ↠ R''`: the idempotents for
the pulled-back nodes `q⁻¹(𝔪'' j)` reduce to those for the nodes `𝔪'' j`. (The instance
`[∀ j, ((𝔪'' j).comap q).IsMaximal]` is provided by `isMaximal_comap`.) -/
theorem map_idem_comap (j : ι) :
    CompletionMap.map q (map_span_le q hqf)
        (idem (injective_comap q hq 𝔪'' hinj'') (mem_comap q hqf 𝔪'' hf'')
          (iInf_comap_le_radical q hq hqf 𝔪'' hker hrad'') j) =
      idem hinj'' hf'' hrad'' j :=
  map_idem q _ (fun _ ↦ Ideal.map_comap_le) _ _ _ hinj'' hf'' hrad'' j

end Thickening

end CompletionProd

namespace Admissible

variable {k : Type u} [Field k] {R₁ : Type u} [CommRing R₁] [Algebra k R₁] [IsNoetherianRing R₁]
  {R₂ : Type u} [CommRing R₂] [Algebra k R₂] [IsNoetherianRing R₂] (e : R₁ ≃ₐ[k] R₂)
  {f₁ : R₁} {f₂ : R₂} (h : e f₁ = f₂) {ι : Type v} [Finite ι] [DecidableEq ι]
  {𝔪₁ : ι → Ideal R₁} {𝔪₂ : ι → Ideal R₂} [∀ j, (𝔪₁ j).IsMaximal] [∀ j, (𝔪₂ j).IsMaximal]
  (hinj₁ : Function.Injective 𝔪₁) (hf₁ : ∀ j, f₁ ∈ 𝔪₁ j)
  (hrad₁ : ⨅ j, 𝔪₁ j ≤ (Ideal.span {f₁}).radical)
  (hinj₂ : Function.Injective 𝔪₂) (hf₂ : ∀ j, f₂ ∈ 𝔪₂ j)
  (hrad₂ : ⨅ j, 𝔪₂ j ≤ (Ideal.span {f₂}).radical)

/-- **`hatEquiv` maps the idempotents of lemma F to each other** (if `e(𝔪₁ j) ⊆ 𝔪₂ j`). -/
theorem hatEquiv_idem (hm : ∀ j, (𝔪₁ j).map e ≤ 𝔪₂ j) (j : ι) :
    hatEquiv e h (CompletionProd.idem hinj₁ hf₁ hrad₁ j) =
      CompletionProd.idem hinj₂ hf₂ hrad₂ j := by
  rw [hatEquiv_apply]
  exact CompletionProd.map_idem _ _ (fun j ↦ by rw [Ideal.map_coe]; exact hm j) hinj₁ hf₁ hrad₁
    hinj₂ hf₂ hrad₂ j

end Admissible

namespace AdmissibleLift

open Function

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  {R : Type u} [CommRing R] [Algebra O R] [Algebra k (R ⧸ J θ)]
  {Rb : Type u} [CommRing Rb] [Algebra k Rb] (e : Rb ≃ₐ[k] R ⧸ J θ)

/-- The reduction `R → R/J ≃ R̄` of a chart to (a model `R̄` of) its special fibre. -/
abbrev red : R →+* Rb := (e.symm.toRingEquiv : R ⧸ J θ →+* Rb).comp (Ideal.Quotient.mk (J θ))

lemma surjective_red : Surjective (red θ e) :=
  e.symm.surjective.comp Ideal.Quotient.mk_surjective

lemma ker_red : RingHom.ker (red θ e) = J θ := by
  rw [RingHom.ker_comp_of_injective _ e.symm.injective, Ideal.mk_ker]

variable {f : R} {fb : Rb} (h : e fb = fbar θ f)

include h in
lemma red_f : red θ e f = fb := by
  change e.symm (fbar θ f) = fb
  rw [← h, e.symm_apply_apply]

variable [IsNoetherianRing R] [IsNoetherianRing Rb] {ι : Type v} [Finite ι] [DecidableEq ι]
  {𝔪 : ι → Ideal Rb} [∀ j, (𝔪 j).IsMaximal] (hinj : Injective 𝔪) (hf : ∀ j, fb ∈ 𝔪 j)
  (hrad : ⨅ j, 𝔪 j ≤ (Ideal.span {fb}).radical)
  {𝔪' : ι → Ideal R} [∀ j, (𝔪' j).IsMaximal] (hinj' : Injective 𝔪') (hf' : ∀ j, f ∈ 𝔪' j)
  (hrad' : ⨅ j, 𝔪' j ≤ (Ideal.span {f}).radical)

/-- **The level idempotents reduce to the transported special-fibre idempotents**: if the level
nodes `𝔪' j` reduce into the nodes `𝔪 j` of `R̄ ≃ R/J`, then `ψ (idem' j) = Ê (idem j)`
(`Ê = Admissible.hatEquiv e h`); this is the hypothesis `hε` of `KummerLift`. -/
theorem ψ_idem (hm : ∀ j, (𝔪' j).map (red θ e) ≤ 𝔪 j) (j : ι) :
    ψ θ f (CompletionProd.idem hinj' hf' hrad' j) =
      Admissible.hatEquiv e h (CompletionProd.idem hinj hf hrad j) := by
  rw [← CompletionProd.map_idem (red θ e) (CompletionProd.map_span_le _ (red_f θ e h)) hm hinj'
    hf' hrad' hinj hf hrad j, Admissible.hatEquiv_apply, CompletionMap.map_comp,
    CompletionQuot.ψ_eq_map]
  refine CompletionMap.map_congr ?_ _ _ _
  ext x
  simp

/-- **`ψ_idem` for the pulled-back nodes** `𝔪' j = red⁻¹(𝔪 j)`, when `J` is nil (e.g. `ker θ`
nilpotent); the instance `[∀ j, ((𝔪 j).comap (red θ e)).IsMaximal]` is provided by
`CompletionProd.isMaximal_comap`. -/
theorem ψ_idem_comap [∀ j, ((𝔪 j).comap (red θ e)).IsMaximal] (hJ : J θ ≤ nilradical R)
    (j : ι) :
    ψ θ f (CompletionProd.idem (CompletionProd.injective_comap _ (surjective_red θ e) 𝔪 hinj)
        (CompletionProd.mem_comap _ (red_f θ e h) 𝔪 hf)
        (CompletionProd.iInf_comap_le_radical _ (surjective_red θ e) (red_f θ e h) 𝔪
          ((ker_red θ e).le.trans hJ) hrad) j) =
      Admissible.hatEquiv e h (CompletionProd.idem hinj hf hrad j) :=
  ψ_idem θ e h hinj hf hrad _ _ _ (fun _ ↦ Ideal.map_comap_le) j

end AdmissibleLift

end SemistableReduction
