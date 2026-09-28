/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Unramified

/-!
# Defect is invariant under unramified base change

Blueprint §9.4, C4. Let `M ⊆ E ⊆ P` and `M ⊆ N ⊆ P` be finite extensions with `P = E · N`, and
`w` a valuation on `P` whose restrictions to the intermediate fields of `P / E`, to `N` and to `P`
have Henselian valuation rings (e.g. `M` complete of rank one, `UniqueExtension`). If `N / M` is
unramified with separable residue field extension, then `d(E / M) = d(P / N)`:

`[E : M] · e(P | N) f(P | N) = [P : N] · e(E | M) f(E | M)` (`defect_eq_of_unramified`),

in particular `E / M` is defectless iff `P / N` is (`defectless_iff_of_unramified`).

The key step is `unramified_of_adjoin_simple_root`: if `P = E(y)` for a root `y` of a monic `q`
over the valuation ring of `E` whose reduction has `ȳ` as a simple root, then `P / E` is
unramified with separable residue field extension. (Lift the minimal polynomial `r̄` of `ȳ` over
`κ_E`, which is separable, to `r` and take a Hensel root `z` of `r` with `z̄ = ȳ`; a Hensel root of
`q` in `E(z)` with residue `ȳ` equals `y` by uniqueness of simple roots, so `E(z) = P`, and
`P = E(z)` is unramified by `unramified_of_root_separable`.)
-/

open IsLocalRing Valuation Polynomial
open scoped IntermediateField

namespace SemistableReduction

namespace FundamentalInequality

section Root

variable {E P : Type*} [Field E] [Field P] [Algebra E P]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  {u : Valuation E Γ₀} {w : Valuation P Γ₁} [u.HasExtension w]

local notation "O_u" => u.valuationSubring
local notation "O_w" => w.valuationSubring
local notation "κ_u" => ResidueField u.valuationSubring
local notation "κ_w" => ResidueField w.valuationSubring

/-- **Simple roots descend to Henselian intermediate fields.** Let `K` be an intermediate field
with Henselian valuation ring, `y` in the valuation ring of `w` a root of a monic `q` over the
valuation ring of `u` with `ȳ` a simple root of `q̄`. If `ȳ` lies in (the image of) the residue
field of `K`, then `y ∈ K`. -/
theorem mem_of_root_of_residue_mem (K : IntermediateField E P)
    [HenselianLocalRing (w.comap (algebraMap K P)).valuationSubring] {q : O_u[X]} (hq : q.Monic)
    {y : O_w} (hy : aeval y q = 0)
    (hsimple : aeval (residue O_w y) (derivative (q.map (residue O_u))) ≠ 0)
    {r : ResidueField (w.comap (algebraMap K P)).valuationSubring}
    (hr : algebraMap _ κ_w r = residue O_w y) : (y : P) ∈ K := by
  set φ := IsScalarTower.toAlgHom κ_u
    (ResidueField (w.comap (algebraMap K P)).valuationSubring) κ_w
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hr' : φ r = residue O_w y := hr
  have hroot : aeval (residue O_w y) (q.map (residue O_u)) = 0 := by
    rw [← residue_aeval, hy, map_zero]
  obtain ⟨z, hz, hzr⟩ := hensel_lift (u := u) (w := w.comap (algebraMap K P)) hq (y₀ := r)
    (by rw [← map_eq_zero_iff φ hφ, ← aeval_algHom_apply, hr', hroot])
    (by
      intro h0
      apply hsimple
      rw [← hr', aeval_algHom_apply, h0, map_zero])
  set b : O_w := algebraMap (w.comap (algebraMap K P)).valuationSubring O_w z
  have hresb : residue O_w b = residue O_w y := by
    rw [← hr', ← hzr]
    rfl
  have hyb : y = b := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := q.map (algebraMap O_u O_w))
      ?_ ?_ ?_ ?_
    · rw [eval_map_algebraMap, hy]
    · rw [eval_map_algebraMap, aeval_algebraMap_apply, hz, map_zero]
    · intro hu
      apply (residue_ne_zero_iff_isUnit _).2 hu
      rw [_root_.map_sub, hresb, sub_self]
    · rw [← residue_ne_zero_iff_isUnit, derivative_map, residue_eval_map, ← derivative_map]
      exact hsimple
  rw [hyb]
  exact (z : K).2

variable [FiniteDimensional E P]

/-- **Adjoining a simple root of a reduction gives an unramified extension.** If the valuation
rings of `w` and of its restrictions to the intermediate fields of `P / E` are Henselian, and
`P = E(y)` for a root `y` of a monic `q` over the valuation ring of `u` such that `ȳ` is a simple
root of `q̄`, then `e(w | E) = 1`, `f(w | u) = [P : E]` and `κ_w / κ_u` is separable. -/
theorem unramified_of_adjoin_simple_root [HenselianLocalRing O_w]
    (hH : ∀ K : IntermediateField E P,
      HenselianLocalRing (w.comap (algebraMap K P)).valuationSubring)
    {q : O_u[X]} (hq : q.Monic) {y : O_w} (hy : aeval y q = 0)
    (hsimple : aeval (residue O_w y) (derivative (q.map (residue O_u))) ≠ 0)
    (hgen : E⟮(y : P)⟯ = ⊤) :
    ramificationIdx E w = 1 ∧ inertiaDeg u w = Module.finrank E P ∧
      Algebra.IsSeparable κ_u κ_w := by
  have : Module.Finite κ_u κ_w := finite_residueField
  set yb := residue O_w y
  have hint : IsIntegral κ_u yb := Algebra.IsIntegral.isIntegral _
  have hroot : aeval yb (q.map (residue O_u)) = 0 := by
    rw [← residue_aeval, hy, map_zero]
  -- the minimal polynomial of `ȳ` is separable
  have hdvd : minpoly κ_u yb ∣ q.map (residue O_u) := minpoly.dvd _ _ hroot
  have hrsep : (minpoly κ_u yb).Separable := by
    rw [separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
    intro h0
    obtain ⟨s, hs⟩ := hdvd
    apply hsimple
    rw [hs, derivative_mul, h0, zero_mul, zero_add, map_mul, minpoly.aeval, zero_mul]
  obtain ⟨r, hrmap, -, hr⟩ := exists_monic_lift (minpoly.monic hint)
  obtain ⟨z, hz, hzy⟩ := hensel_lift hr (y₀ := yb) (by rw [hrmap, minpoly.aeval])
    (by rw [hrmap]; exact hrsep.aeval_derivative_ne_zero (minpoly.aeval _ _))
  -- `y ∈ E(z)`, hence `E(z) = P`
  set K := E⟮(z : P)⟯
  have hzK : (z : P) ∈ K := IntermediateField.mem_adjoin_simple_self E (z : P)
  have : HenselianLocalRing (w.comap (algebraMap K P)).valuationSubring := hH K
  have hyK : (y : P) ∈ K :=
    mem_of_root_of_residue_mem K hq hy hsimple
      (r := residue _ (toValuationSubringComap K z hzK)) hzy
  have hKtop : K = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
    exact hyK
  have hdeg : Module.finrank E P ≤ r.natDegree := by
    have hzint : IsIntegral E (z : P) := Algebra.IsIntegral.isIntegral _
    have hrz : aeval (z : P) (r.map (algebraMap O_u E)) = 0 := by
      rw [aeval_map_algebraMap, show (z : P) = algebraMap O_w P z from rfl,
        aeval_algebraMap_apply, hz, map_zero]
    rw [← IntermediateField.finrank_top', ← hKtop, IntermediateField.adjoin.finrank hzint]
    have := natDegree_le_of_dvd (minpoly.dvd E (z : P) hrz) (hr.map (algebraMap O_u E)).ne_zero
    rwa [hr.natDegree_map] at this
  obtain ⟨he, hf, hsep, -⟩ := unramified_of_root_separable hr
    (by rw [hrmap]; exact minpoly.irreducible hint) (by rw [hrmap]; exact hrsep) hz hdeg
  exact ⟨he, hf, hsep⟩

end Root

section BaseChange

variable {M E N P : Type*} [Field M] [Field E] [Field N] [Field P]
  [Algebra M E] [Algebra M N] [Algebra E P] [Algebra N P] [Algebra M P]
  [IsScalarTower M E P] [IsScalarTower M N P]
  [FiniteDimensional M E] [FiniteDimensional M N] [FiniteDimensional E P] [FiniteDimensional N P]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation P Γ)

local notation "wM" => w.comap (algebraMap M P)
local notation "wE" => w.comap (algebraMap E P)
local notation "wN" => w.comap (algebraMap N P)

/-- `f = [N : M]` forces `e = 1`. -/
lemma ramificationIdx_eq_one_of_inertiaDeg_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₁] {v : Valuation K Γ₀} {v' : Valuation L Γ₁}
    [v.HasExtension v'] (hf : inertiaDeg v v' = Module.finrank K L) :
    ramificationIdx K v' = 1 := by
  have h := ramificationIdx_mul_inertiaDeg_le (K := K) (v := v) (w := v')
  have he := Nat.pos_of_ne_zero (ramificationIdx_ne_zero (K := K) v')
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  rw [hf] at h
  exact le_antisymm ((Nat.le_div_iff_mul_le hn).2 h |>.trans (Nat.div_self hn).le) he

/-- **Defect is invariant under unramified base change** (Kuhlmann [K6]). Let `P` be generated
over `E` by `N`, let `N / M` be unramified (`f(N | M) = [N : M]`) with separable residue field
extension, and let the valuation rings of `w`, of its restriction to `N` and of its restrictions to
the intermediate fields of `P / E` be Henselian. Then
`[E : M] · e(P | N) f(P | N) = [P : N] · e(E | M) f(E | M)`, i.e. `d(E / M) = d(P / N)`. -/
theorem defect_eq_of_unramified [HenselianLocalRing w.valuationSubring]
    [HenselianLocalRing (wN).valuationSubring]
    (hH : ∀ K : IntermediateField E P,
      HenselianLocalRing (w.comap (algebraMap K P)).valuationSubring)
    (hunr : inertiaDeg (wM) (wN) = Module.finrank M N)
    [Algebra.IsSeparable (ResidueField (wM).valuationSubring) (ResidueField (wN).valuationSubring)]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap N P)) = ⊤) :
    Module.finrank M E * (ramificationIdx N w * inertiaDeg (wN) w) =
      Module.finrank N P * (ramificationIdx M (wE) * inertiaDeg (wM) (wE)) := by
  -- a Hensel generator of `N / M`
  obtain ⟨y, q, hq, hy, hqmin, -, hytop, -⟩ :=
    exists_unramified_generator (u := wM) (w := wN) hunr
  -- its image in `P`, and `q` over the valuation ring of `E`
  set yP : w.valuationSubring := algebraMap (wN).valuationSubring w.valuationSubring y
  set qE := q.map (algebraMap (wM).valuationSubring (wE).valuationSubring)
  have hqE : qE.Monic := hq.map _
  have hyP : aeval yP qE = 0 := by
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, hy, map_zero]
  have hint : IsIntegral (ResidueField (wM).valuationSubring)
      (residue (wN).valuationSubring y) := Algebra.IsIntegral.isIntegral _
  have hsepN : (minpoly (ResidueField (wM).valuationSubring)
      (residue (wN).valuationSubring y)).Separable := Algebra.IsSeparable.isSeparable _ _
  have hsimple : aeval (residue w.valuationSubring yP)
      (derivative (qE.map (residue (wE).valuationSubring))) ≠ 0 := by
    have hmap : qE.map (residue (wE).valuationSubring) =
        (q.map (residue (wM).valuationSubring)).map
          (algebraMap (ResidueField (wM).valuationSubring)
            (ResidueField (wE).valuationSubring)) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      rfl
    have hres : residue w.valuationSubring yP =
        algebraMap (ResidueField (wN).valuationSubring) (ResidueField w.valuationSubring)
          (residue (wN).valuationSubring y) := rfl
    rw [hmap, derivative_map, aeval_map_algebraMap, hres, aeval_algebraMap_apply, hqmin]
    exact (map_ne_zero_iff _ (algebraMap (ResidueField (wN).valuationSubring)
      (ResidueField w.valuationSubring)).injective).2
      (hsepN.aeval_derivative_ne_zero
        (minpoly.aeval (ResidueField (wM).valuationSubring) (residue (wN).valuationSubring y)))
  -- `P = E(y)`
  have hgen' : E⟮(yP : P)⟯ = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨n, rfl⟩
    have hn : n ∈ M⟮(y : N)⟯ := by rw [hytop]; trivial
    have hmap := congrArg (IntermediateField.map (IsScalarTower.toAlgHom M N P)) hytop
    have hle : IntermediateField.map (IsScalarTower.toAlgHom M N P) M⟮(y : N)⟯ ≤
        (E⟮(yP : P)⟯).restrictScalars M := by
      rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.mem_adjoin_simple_self E (yP : P)
    exact hle ⟨n, hn, rfl⟩
  obtain ⟨heP, hfP, -⟩ := unramified_of_adjoin_simple_root (u := wE) (w := w) hH hqE hyP hsimple
    hgen'
  have heN : ramificationIdx M (wN) = 1 := ramificationIdx_eq_one_of_inertiaDeg_eq hunr
  -- multiplicativity in the towers `M ⊆ E ⊆ P` and `M ⊆ N ⊆ P`
  have h₁ := ramificationIdx_tower (K := M) (L := E) w
  have h₂ := ramificationIdx_tower (K := M) (L := N) w
  have h₃ := inertiaDeg_tower (wM) (wE) w
  have h₄ := inertiaDeg_tower (wM) (wN) w
  have hdE := Module.finrank_mul_finrank M E P
  have hdN := Module.finrank_mul_finrank M N P
  have hNpos : 0 < Module.finrank M N := Module.finrank_pos
  refine Nat.eq_of_mul_eq_mul_right hNpos ?_
  calc Module.finrank M E * (ramificationIdx N w * inertiaDeg (wN) w) * Module.finrank M N
      = Module.finrank M E * (ramificationIdx M w * inertiaDeg (wM) w) := by
        rw [h₂, h₄, heN, hunr]; ring
    _ = Module.finrank M E * Module.finrank E P *
          (ramificationIdx M (wE) * inertiaDeg (wM) (wE)) := by
        rw [h₁, h₃, heP, hfP]; ring
    _ = Module.finrank N P * (ramificationIdx M (wE) * inertiaDeg (wM) (wE)) *
          Module.finrank M N := by
        rw [hdE, ← hdN]; ring

/-- **Defectlessness is invariant under unramified base change**: under the hypotheses of
`defect_eq_of_unramified`, `E / M` is defectless iff `P / N` is. -/
theorem defectless_iff_of_unramified [HenselianLocalRing w.valuationSubring]
    [HenselianLocalRing (wN).valuationSubring]
    (hH : ∀ K : IntermediateField E P,
      HenselianLocalRing (w.comap (algebraMap K P)).valuationSubring)
    (hunr : inertiaDeg (wM) (wN) = Module.finrank M N)
    [Algebra.IsSeparable (ResidueField (wM).valuationSubring) (ResidueField (wN).valuationSubring)]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap N P)) = ⊤) :
    ramificationIdx M (wE) * inertiaDeg (wM) (wE) = Module.finrank M E ↔
      ramificationIdx N w * inertiaDeg (wN) w = Module.finrank N P := by
  have h := defect_eq_of_unramified w hH hunr hgen
  have hE : 0 < Module.finrank M E := Module.finrank_pos
  have hP : 0 < Module.finrank N P := Module.finrank_pos
  constructor
  · intro hd
    rw [hd, mul_comm (Module.finrank N P)] at h
    exact Nat.eq_of_mul_eq_mul_left hE h
  · intro hd
    rw [hd, mul_comm (Module.finrank M E)] at h
    exact (Nat.eq_of_mul_eq_mul_left hP h).symm

end BaseChange

end FundamentalInequality

end SemistableReduction
