/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DefectTower
import TemperedFundamentalGroups.SemistableReduction.UnramifiedRoot

/-!
# Unramified extensions and the unramified closure

Blueprint §9.4, C2 (remaining part). Let `u` be a valuation on `M`, extended by a valuation `w`
on a finite extension `N`. We write `κ_u`, `κ_w` for the residue fields.

* `hasExtension_comap_tower`: for a tower `M ⊆ K ⊆ N`, `u` is extended by the restriction of
  `w` to `K`.
* `hensel_lift`: over a Henselian valuation ring of `w`, a simple root in `κ_w` of the reduction
  of a monic `q` over the valuation ring of `u` lifts to a root of `q`.
* `unramified_of_root_separable`: a root `y` of a monic `q` whose reduction is irreducible and
  separable, with `[N : M] ≤ deg q`, gives an unramified extension (`e = 1`, `f = [N : M]`) with
  separable residue field extension.
* `exists_adjoin_eq_top_of_unramified`: conversely, if `f(w | u) = [N : M]` and `κ_w / κ_u` is
  separable, then `N = M(y)` for some `y` in the valuation ring whose residue generates `κ_w`;
  `exists_unramified_generator`: if moreover the valuation ring of `w` is Henselian, `y` can be
  chosen as a root of a monic lift `q` of the minimal polynomial of `ȳ`.
* `exists_unramifiedClosure`: if the valuation rings of all intermediate fields of `N / M` (and of
  `N`) are Henselian, there is an intermediate field `K` (the *unramified closure* of `M` in `N`)
  such that `K / M` is unramified with separable residue field extension, the residue field of
  `K` is the separable closure of `κ_u` in `κ_w`, and every intermediate field that is unramified
  over `M` with separable residue field extension is contained in `K`.
-/

open IsLocalRing Valuation Polynomial
open scoped IntermediateField

namespace SemistableReduction

namespace FundamentalInequality

section Tower

variable {M K N : Type*} [Field M] [Field K] [Field N] [Algebra M K] [Algebra K N] [Algebra M N]
  [IsScalarTower M K N] {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₁] (u : Valuation M Γ₀) (w : Valuation N Γ₁)
  [u.HasExtension w]

/-- For a tower `M ⊆ K ⊆ N`, a valuation `u` on `M` extended by `w` on `N` is extended by the
restriction of `w` to `K`. -/
instance hasExtension_comap_tower : u.HasExtension (w.comap (algebraMap K N)) :=
  ⟨by
    rw [comap_comap_algebraMap]
    exact HasExtension.val_isEquiv_comap⟩

/-- The valuation rings of a tower of valuations form a scalar tower. -/
instance isScalarTower_valuationSubring {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [u.HasExtension v] [v.HasExtension w] :
    IsScalarTower u.valuationSubring v.valuationSubring w.valuationSubring :=
  IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext (by
    simp only [HasExtension.coe_algebraMap_valuationSubring_eq]
    exact IsScalarTower.algebraMap_apply M K N x)

end Tower

variable {M N : Type*} [Field M] [Field N] [Algebra M N]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  {u : Valuation M Γ₀} {w : Valuation N Γ₁} [u.HasExtension w]

local notation "O_u" => u.valuationSubring
local notation "O_w" => w.valuationSubring
local notation "κ_u" => ResidueField u.valuationSubring
local notation "κ_w" => ResidueField w.valuationSubring

/-- Every monic polynomial over the residue field lifts to a monic polynomial of the same degree
over the valuation ring. -/
lemma exists_monic_lift {p : κ_u[X]} (hp : p.Monic) :
    ∃ q : O_u[X], q.map (residue O_u) = p ∧ q.natDegree = p.natDegree ∧ q.Monic := by
  refine lifts_and_natDegree_eq_and_monic ?_ hp
  rw [lifts_iff_coeff_lifts]
  exact fun n ↦ residue_surjective _

/-- Reduction commutes with evaluation, for a polynomial over the smaller valuation ring. -/
lemma residue_eval_map (q : O_u[X]) (y : O_w) :
    residue O_w ((q.map (algebraMap O_u O_w)).eval y) =
      aeval (residue O_w y) (q.map (residue O_u)) := by
  rw [eval_map_algebraMap, residue_aeval]

/-- **Hensel lifting of simple roots.** If the valuation ring of `w` is Henselian and `ȳ ∈ κ_w` is
a simple root of the reduction of a monic `q` over the valuation ring of `u`, then `q` has a root
`y` in the valuation ring of `w` with residue `ȳ`. -/
theorem hensel_lift [HenselianLocalRing O_w] {q : O_u[X]} (hq : q.Monic) {y₀ : κ_w}
    (hroot : aeval y₀ (q.map (residue O_u)) = 0)
    (hsimple : aeval y₀ (derivative (q.map (residue O_u))) ≠ 0) :
    ∃ y : O_w, aeval y q = 0 ∧ residue O_w y = y₀ := by
  obtain ⟨a₀, rfl⟩ := residue_surjective y₀
  obtain ⟨y, hy, hya⟩ := HenselianLocalRing.is_henselian (q.map (algebraMap O_u O_w))
    (hq.map _) a₀
    (by rw [← residue_eq_zero_iff, residue_eval_map, hroot])
    (by
      rw [← residue_ne_zero_iff_isUnit, derivative_map, residue_eval_map, ← derivative_map]
      exact hsimple)
  refine ⟨y, by rw [aeval_def, ← eval_map]; exact hy, ?_⟩
  rw [← sub_eq_zero, ← _root_.map_sub, residue_eq_zero_iff]
  exact hya

/-- The degree of the residue `ȳ` of `y` over `κ_u` is at most the degree of `M(y)` over `M`. -/
theorem natDegree_minpoly_residue_le [FiniteDimensional M N] (y : O_w) :
    (minpoly κ_u (residue O_w y)).natDegree ≤ Module.finrank M M⟮(y : N)⟯ := by
  set K := M⟮(y : N)⟯
  have hli : LinearIndependent κ_u
      (fun i : Fin (minpoly κ_u (residue O_w y)).natDegree ↦ residue O_w (y ^ (i : ℕ))) := by
    simpa only [map_pow] using linearIndependent_pow (K := κ_u) (residue O_w y)
  have hli' := linearIndependent_of_residue (K := M) hli
  have hmem (i : ℕ) : ((y ^ i : O_w) : N) ∈ K := by
    push_cast
    exact pow_mem (IntermediateField.mem_adjoin_simple_self M (y : N)) i
  have hK : LinearIndependent M
      (fun i : Fin (minpoly κ_u (residue O_w y)).natDegree ↦
        (⟨((y ^ (i : ℕ) : O_w) : N), hmem i⟩ : K)) :=
    LinearIndependent.of_comp K.val.toLinearMap hli'
  simpa using hK.fintype_card_le_finrank

/-- **Unramified extensions generated by a root, separable case.** If `y` is a root of a monic `q`
whose reduction is irreducible and separable, and `[N : M] ≤ deg q`, then `e(w | u) = 1`,
`f(w | u) = [N : M]`, `κ_w / κ_u` is separable and generated by `ȳ`. -/
theorem unramified_of_root_separable [FiniteDimensional M N] {q : O_u[X]} (hq : q.Monic)
    (hirr : Irreducible (q.map (residue O_u))) (hsep : (q.map (residue O_u)).Separable)
    {y : O_w} (hy : aeval y q = 0) (hdeg : Module.finrank M N ≤ q.natDegree) :
    ramificationIdx M w = 1 ∧ inertiaDeg u w = Module.finrank M N ∧
      Algebra.IsSeparable κ_u κ_w ∧ κ_u⟮residue O_w y⟯ = ⊤ := by
  obtain ⟨he, hf⟩ := unramified_of_root hq hirr hy hdeg
  have : Module.Finite κ_u κ_w := finite_residueField
  have hmin := minpoly_residue_eq hq hirr hy
  have hint : IsIntegral κ_u (residue O_w y) := Algebra.IsIntegral.isIntegral _
  have htop : κ_u⟮residue O_w y⟯ = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_le le_top ?_
    rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, hmin,
      hq.natDegree_map, ← inertiaDeg, hf]
    exact hdeg
  have hysep : IsSeparable κ_u (residue O_w y) := by
    rw [IsSeparable, hmin]
    exact hsep
  have : Algebra.IsSeparable κ_u κ_u⟮residue O_w y⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hysep
  rw [htop] at this
  exact ⟨he, hf, AlgEquiv.Algebra.isSeparable IntermediateField.topEquiv, htop⟩

/-- If `f(w | u) = [N : M]` and `κ_w / κ_u` is separable, then `N = M(y)` for some `y` in the
valuation ring of `w` whose residue generates `κ_w` over `κ_u`. -/
theorem exists_adjoin_eq_top_of_unramified [FiniteDimensional M N]
    (hf : inertiaDeg u w = Module.finrank M N) [Algebra.IsSeparable κ_u κ_w] :
    ∃ y : O_w, M⟮(y : N)⟯ = ⊤ ∧ κ_u⟮residue O_w y⟯ = ⊤ := by
  have : Module.Finite κ_u κ_w := finite_residueField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element κ_u κ_w
  obtain ⟨y, rfl⟩ := residue_surjective α
  refine ⟨y, IntermediateField.eq_of_le_of_finrank_le le_top ?_, hα⟩
  rw [IntermediateField.finrank_top', ← hf, inertiaDeg, ← IntermediateField.finrank_top', ← hα,
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _)]
  exact natDegree_minpoly_residue_le y

/-- **Unramified extensions are generated by Hensel lifts of separable generators.** If the
valuation ring of `w` is Henselian, `f(w | u) = [N : M]` and `κ_w / κ_u` is separable, then there
are `y` in the valuation ring of `w` and a monic `q` over the valuation ring of `u` with
`q(y) = 0`, `q̄` the minimal polynomial of `ȳ`, `deg q = [N : M]`, `N = M(y)` and
`κ_w = κ_u(ȳ)`. -/
theorem exists_unramified_generator [FiniteDimensional M N] [HenselianLocalRing O_w]
    (hf : inertiaDeg u w = Module.finrank M N) [Algebra.IsSeparable κ_u κ_w] :
    ∃ (y : O_w) (q : O_u[X]), q.Monic ∧ aeval y q = 0 ∧
      q.map (residue O_u) = minpoly κ_u (residue O_w y) ∧ q.natDegree = Module.finrank M N ∧
      M⟮(y : N)⟯ = ⊤ ∧ κ_u⟮residue O_w y⟯ = ⊤ := by
  have : Module.Finite κ_u κ_w := finite_residueField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element κ_u κ_w
  have hint : IsIntegral κ_u α := Algebra.IsIntegral.isIntegral _
  obtain ⟨q, hqmap, hqdeg, hq⟩ := exists_monic_lift (minpoly.monic hint)
  have hsep : (minpoly κ_u α).Separable := Algebra.IsSeparable.isSeparable κ_u α
  obtain ⟨y, hy, rfl⟩ := hensel_lift hq (y₀ := α) (by rw [hqmap, minpoly.aeval])
    (by rw [hqmap]; exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _))
  have hdeg : q.natDegree = Module.finrank M N := by
    rw [hqdeg, ← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top', ← hf,
      inertiaDeg]
  refine ⟨y, q, hq, hy, hqmap, hdeg, IntermediateField.eq_of_le_of_finrank_le le_top ?_, hα⟩
  rw [IntermediateField.finrank_top', ← hdeg, hqdeg]
  exact natDegree_minpoly_residue_le y

section Closure

/-- The image of a separable element under an algebra homomorphism of fields is separable. -/
lemma isSeparable_algHom_apply {F E E' : Type*} [Field F] [Field E] [Field E'] [Algebra F E]
    [Algebra F E'] (f : E →ₐ[F] E') {x : E} (hx : IsSeparable F x) : IsSeparable F (f x) := by
  rwa [IsSeparable, minpoly.algHom_eq f f.injective]

/-- The element `y` of an intermediate field `K`, as an element of the valuation ring of the
restriction of `w` to `K`. -/
def toValuationSubringComap (K : IntermediateField M N) (y : O_w) (hy : (y : N) ∈ K) :
    (w.comap (algebraMap K N)).valuationSubring :=
  ⟨⟨y, hy⟩, by
    change w (y : N) ≤ 1
    exact y.2⟩

lemma algebraMap_toValuationSubringComap (K : IntermediateField M N) (y : O_w)
    (hy : (y : N) ∈ K) :
    algebraMap (w.comap (algebraMap K N)).valuationSubring O_w
      (toValuationSubringComap K y hy) = y :=
  rfl

lemma algebraMap_valuationSubring_comap_injective (K : IntermediateField M N) :
    Function.Injective (algebraMap (w.comap (algebraMap K N)).valuationSubring O_w) :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun t : O_w ↦ (t : N)) h))

variable [FiniteDimensional M N]

set_option synthInstance.maxHeartbeats 80000 in
-- the instance `Algebra κ_u (separableClosure κ_u κ_w)` is slow to find for residue fields
/-- **The unramified closure.** Suppose the valuation rings of `w` and of its restrictions to all
intermediate fields of `N / M` are Henselian. Then there is an intermediate field `K` such that
`K / M` is unramified (`e = 1`, `f = [K : M]`) with separable residue field extension, the image
of the residue field of `K` in `κ_w` is the separable closure of `κ_u` in `κ_w`, and every
intermediate field `K'` with `f(K' | M) = [K' : M]` and separable residue field extension is
contained in `K`. -/
theorem exists_unramifiedClosure [HenselianLocalRing O_w]
    (hH : ∀ K : IntermediateField M N,
      HenselianLocalRing (w.comap (algebraMap K N)).valuationSubring) :
    ∃ K : IntermediateField M N,
      (ramificationIdx M (w.comap (algebraMap K N)) = 1 ∧
        inertiaDeg u (w.comap (algebraMap K N)) = Module.finrank M K ∧
        Algebra.IsSeparable κ_u (ResidueField (w.comap (algebraMap K N)).valuationSubring)) ∧
      (IsScalarTower.toAlgHom κ_u (ResidueField (w.comap (algebraMap K N)).valuationSubring)
          κ_w).fieldRange = separableClosure κ_u κ_w ∧
      ∀ K' : IntermediateField M N,
        inertiaDeg u (w.comap (algebraMap K' N)) = Module.finrank M K' →
        Algebra.IsSeparable κ_u (ResidueField (w.comap (algebraMap K' N)).valuationSubring) →
        K' ≤ K := by
  have : Module.Finite κ_u κ_w := finite_residueField
  obtain ⟨s, hs⟩ := Field.exists_primitive_element κ_u (separableClosure κ_u κ_w)
  have hsint : IsIntegral κ_u (s : κ_w) := Algebra.IsIntegral.isIntegral _
  have hssep : IsSeparable κ_u (s : κ_w) := s.2
  obtain ⟨q, hqmap, hqdeg, hq⟩ := exists_monic_lift (minpoly.monic hsint)
  obtain ⟨y, hy, hys⟩ := hensel_lift hq (y₀ := (s : κ_w)) (by rw [hqmap, minpoly.aeval])
    (by rw [hqmap]; exact hssep.aeval_derivative_ne_zero (minpoly.aeval _ _))
  set K := M⟮(y : N)⟯ with hK
  have hyK : (y : N) ∈ K := IntermediateField.mem_adjoin_simple_self M (y : N)
  set yK := toValuationSubringComap K y hyK
  have hyK0 : aeval yK q = 0 := by
    apply algebraMap_valuationSubring_comap_injective K
    rw [← aeval_algebraMap_apply, algebraMap_toValuationSubringComap, hy, map_zero]
  have hdegK : Module.finrank M K ≤ q.natDegree := by
    have hyint : IsIntegral M (y : N) := Algebra.IsIntegral.isIntegral _
    rw [hK, IntermediateField.adjoin.finrank hyint]
    have hroot : aeval (y : N) (q.map (algebraMap O_u M)) = 0 := by
      rw [aeval_map_algebraMap, show (y : N) = algebraMap O_w N y from rfl,
        aeval_algebraMap_apply, hy, map_zero]
    have := natDegree_le_of_dvd (minpoly.dvd M (y : N) hroot)
      ((hq.map (algebraMap O_u M)).ne_zero)
    rwa [hq.natDegree_map] at this
  have hirr : Irreducible (q.map (residue O_u)) := by
    rw [hqmap]; exact minpoly.irreducible hsint
  have hsep : (q.map (residue O_u)).Separable := by
    rw [hqmap]; exact hssep
  obtain ⟨he, hf, hKsep, hKtop⟩ :=
    unramified_of_root_separable (u := u) (w := w.comap (algebraMap K N)) hq hirr hsep hyK0 hdegK
  -- the residue of `yK` maps to `s`
  have hres : IsScalarTower.toAlgHom κ_u (ResidueField (w.comap (algebraMap K N)).valuationSubring)
      κ_w (residue _ yK) = (s : κ_w) := by
    rw [IsScalarTower.toAlgHom_apply]
    exact hys
  have hrange : (IsScalarTower.toAlgHom κ_u
      (ResidueField (w.comap (algebraMap K N)).valuationSubring) κ_w).fieldRange =
        separableClosure κ_u κ_w := by
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      exact isSeparable_algHom_apply _ (Algebra.IsSeparable.isSeparable κ_u r)
    · have hS : separableClosure κ_u κ_w = κ_u⟮(s : κ_w)⟯ := by
        have := congrArg (IntermediateField.map (separableClosure κ_u κ_w).val) hs
        rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
          IntermediateField.fieldRange_val] at this
        exact this.symm
      rw [hS, IntermediateField.adjoin_simple_le_iff, ← hres]
      exact ⟨_, rfl⟩
  refine ⟨K, ⟨he, hf, hKsep⟩, hrange, fun K' hf' hsep' ↦ ?_⟩
  -- a generator of `K'` lies in `K`
  have : HenselianLocalRing (w.comap (algebraMap K' N)).valuationSubring := hH K'
  obtain ⟨y', q', hq', hy', hq'map, -, hy'top, -⟩ :=
    exists_unramified_generator (u := u) (w := w.comap (algebraMap K' N)) hf'
  set φ' := IsScalarTower.toAlgHom κ_u
    (ResidueField (w.comap (algebraMap K' N)).valuationSubring) κ_w
  set φ := IsScalarTower.toAlgHom κ_u
    (ResidueField (w.comap (algebraMap K N)).valuationSubring) κ_w
  have hint' : IsIntegral κ_u (residue _ y') := Algebra.IsIntegral.isIntegral _
  have hsep'' : (minpoly κ_u (residue _ y')).Separable :=
    Algebra.IsSeparable.isSeparable κ_u _
  obtain ⟨r, hr⟩ : ∃ r, φ r = φ' (residue _ y') := by
    have : φ' (residue _ y') ∈ φ.fieldRange := by
      rw [hrange]
      exact isSeparable_algHom_apply _ (Algebra.IsSeparable.isSeparable κ_u _)
    obtain ⟨r, hr⟩ := this
    exact ⟨r, hr⟩
  have : HenselianLocalRing (w.comap (algebraMap K N)).valuationSubring := hH K
  obtain ⟨z, hz, hzr⟩ := hensel_lift (u := u) (w := w.comap (algebraMap K N)) hq' (y₀ := r)
    (by
      rw [← map_eq_zero_iff φ φ.toRingHom.injective, ← aeval_algHom_apply, hr,
        aeval_algHom_apply, hq'map, minpoly.aeval,
        map_zero])
    (by
      intro h0
      apply hsep''.aeval_derivative_ne_zero (minpoly.aeval κ_u (residue _ y'))
      rw [← map_eq_zero_iff φ' φ'.toRingHom.injective, ← aeval_algHom_apply, ← hr,
        aeval_algHom_apply, ← hq'map, h0, map_zero])
  -- `y'` and `z` are roots of `q'` in the valuation ring of `w` with the same residue
  set a : O_w := algebraMap (w.comap (algebraMap K' N)).valuationSubring O_w y'
  set b : O_w := algebraMap (w.comap (algebraMap K N)).valuationSubring O_w z
  have hresa : residue O_w a = φ' (residue _ y') := by
    rw [IsScalarTower.toAlgHom_apply]
    rfl
  have hresb : residue O_w b = φ (residue _ z) := by
    rw [IsScalarTower.toAlgHom_apply]
    rfl
  have hab : a = b := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := q'.map (algebraMap O_u O_w))
      ?_ ?_ ?_ ?_
    · rw [eval_map_algebraMap, aeval_algebraMap_apply, hy', map_zero]
    · rw [eval_map_algebraMap, aeval_algebraMap_apply, hz, map_zero]
    · intro hu
      apply (residue_ne_zero_iff_isUnit _).2 hu
      rw [_root_.map_sub, hresa, hresb, hzr, hr, sub_self]
    · rw [← residue_ne_zero_iff_isUnit, derivative_map, residue_eval_map, hresa,
        aeval_algHom_apply, ← derivative_map, hq'map]
      exact (map_ne_zero_iff _ φ'.toRingHom.injective).2
        (hsep''.aeval_derivative_ne_zero (minpoly.aeval κ_u _))
  have hy'K : ((y' : K') : N) ∈ K := by
    have : ((y' : K') : N) = ((z : K) : N) := congrArg (fun t : O_w ↦ (t : N)) hab
    rw [this]
    exact (z : K).2
  have hK' : K' = M⟮((y' : K') : N)⟯ := by
    have := congrArg (IntermediateField.map K'.val) hy'top
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this.symm
  rw [hK', IntermediateField.adjoin_simple_le_iff]
  exact hy'K

end Closure

end FundamentalInequality

end SemistableReduction
