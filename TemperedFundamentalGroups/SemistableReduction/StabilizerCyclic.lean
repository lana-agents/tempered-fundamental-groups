/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Tame stabilisers of regular points of curves are cyclic (MR12, interface I5(c), generic)

Let `k` be a field, `C` a `k`-algebra and `y` a prime of `C` with residue field `k` whose local
ring `A = C_y` is a discrete valuation ring and into which `C` embeds. A finite group `G` acting
faithfully on `C` by `k`-algebra automorphisms fixing `y`, of order invertible in `k`, is cyclic
(**`StabilizerCyclic.isCyclic_of_faithful`**): the action on the cotangent line `m/m²` of `A`
(the character `σ ↦ (σ π / π) mod m` for a uniformizer `π`) is faithful, so `G` embeds into the
units of the residue field.

Faithfulness on the cotangent line is **`StabilizerCyclic.eq_of_iterate_eq`**: on a Noetherian
local `k`-algebra `A` with residue field `k`, a `k`-linear local endomorphism `σ` with `σⁿ = 1`,
`n` invertible in `k`, which is trivial on `m/m²`, is the identity (by induction `σ − 1` maps
`A` into `mʳ` and `m` into `mʳ⁺¹`, using `n (σ − 1) a ≡ ∑_{i<n} (σ − 1)(σⁱ a) = σⁿ a − a = 0`
modulo `mʳ⁺¹` (`natCast_mul_sub_mem`), and Krull's intersection theorem).

This is the input "special cusp stabilisers are (pro)cyclic" of MR13's C2: applied to the
stabiliser of a special point `y` of the covering over the cusp chart (where the local ring is a
discrete valuation ring with residue field `k`), the stabiliser is cyclic.
-/

namespace SemistableReduction

namespace StabilizerCyclic

open IsLocalRing

section Telescope

variable {A : Type*} [CommRing A] (σ : A →+* A)

/-- **Telescoping**: if `σⁿ = 1`, `S` is `σ`-stable and `(σ − 1)²` maps `S` into an ideal `J`, then
`n (σ − 1)` maps `S` into `J`. -/
theorem natCast_mul_sub_mem {n : ℕ} (hσn : ∀ a, σ^[n] a = a) (S : Set A)
    (hS : ∀ s ∈ S, σ s ∈ S) (J : Ideal A)
    (hJ : ∀ s ∈ S, σ (σ s - s) - (σ s - s) ∈ J) {s : A} (hs : s ∈ S) :
    (n : A) * (σ s - s) ∈ J := by
  have hit : ∀ i, σ^[i] s ∈ S := by
    intro i
    induction i with
    | zero => exact hs
    | succ i ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  have hstep : ∀ i, (σ (σ^[i] s) - σ^[i] s) - (σ s - s) ∈ J := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : (σ (σ^[i + 1] s) - σ^[i + 1] s) - (σ s - s) =
          (σ (σ (σ^[i] s) - σ^[i] s) - (σ (σ^[i] s) - σ^[i] s)) +
            ((σ (σ^[i] s) - σ^[i] s) - (σ s - s)) := by
        rw [Function.iterate_succ_apply', map_sub]
        ring
      rw [e]
      exact J.add_mem (hJ _ (hit i)) ih
  have hsum : ∑ i ∈ Finset.range n, (σ (σ^[i] s) - σ^[i] s) = 0 := by
    have h := Finset.sum_range_sub (fun i ↦ σ^[i] s) n
    simp only [Function.iterate_succ_apply'] at h
    rw [h, hσn, Function.iterate_zero_apply, sub_self]
  have hmem : ∑ i ∈ Finset.range n, ((σ (σ^[i] s) - σ^[i] s) - (σ s - s)) ∈ J :=
    J.sum_mem fun i _ ↦ hstep i
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, zero_sub,
    nsmul_eq_mul] at hmem
  exact (J.neg_mem_iff).mp hmem

end Telescope

section Local

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]

/-- **A tame automorphism trivial on the cotangent space is the identity**: on a Noetherian local
`k`-algebra with residue field `k`, a `k`-linear local endomorphism `σ` with `σⁿ = 1` (`n`
invertible in `k`) and `σ x − x ∈ m²` for `x ∈ m` is the identity. -/
theorem eq_of_iterate_eq (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ maximalIdeal A)
    (σ : A →+* A) (hk : ∀ c : k, σ (algebraMap k A c) = algebraMap k A c)
    (hm : ∀ x ∈ maximalIdeal A, σ x ∈ maximalIdeal A) {n : ℕ} (hn : (n : k) ≠ 0)
    (hσn : ∀ a, σ^[n] a = a)
    (h2 : ∀ x ∈ maximalIdeal A, σ x - x ∈ maximalIdeal A ^ 2) (a : A) : σ a = a := by
  set m := maximalIdeal A with hmdef
  have hnu : IsUnit (n : A) := by
    rw [← map_natCast (algebraMap k A)]
    exact (isUnit_iff_ne_zero.mpr hn).map _
  have cancel : ∀ (J : Ideal A) (x : A), (n : A) * x ∈ J → x ∈ J :=
    fun J x h ↦ (J.unit_mul_mem_iff_mem hnu).mp h
  have hD1 : ∀ a, σ a - a ∈ m := by
    intro a
    obtain ⟨c, hc⟩ := hres a
    have e : σ a - a = σ (a - algebraMap k A c) - (a - algebraMap k A c) := by
      rw [map_sub, hk]
      ring
    rw [e]
    exact m.sub_mem (hm _ hc) hc
  have key : ∀ r, 1 ≤ r → (∀ a, σ a - a ∈ m ^ r) ∧ (∀ x ∈ m, σ x - x ∈ m ^ (r + 1)) := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => exact ⟨fun a ↦ by rw [pow_one]; exact hD1 a, h2⟩
    | succ r hr ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hle : m ^ r ≤ m := Ideal.pow_le_self (by omega)
      have new1 : ∀ a, σ a - a ∈ m ^ (r + 1) := fun a ↦
        cancel _ _ (natCast_mul_sub_mem σ hσn Set.univ (fun _ _ ↦ trivial) _
          (fun s _ ↦ ih2 _ (hle (ih1 s))) trivial)
      have hDD : ∀ z ∈ m ^ (r + 1), σ z - z ∈ m ^ (r + 1 + 1) := by
        intro z hz
        rw [pow_succ'] at hz
        refine Submodule.mul_induction_on hz ?_ ?_
        · intro y hy w hw
          have e : σ (y * w) - y * w = σ y * (σ w - w) + (σ y - y) * w := by
            rw [map_mul]
            ring
          rw [e]
          refine Ideal.add_mem _ ?_ ?_
          · have h := Ideal.mul_mem_mul (hm y hy) (ih2 w (hle hw))
            rwa [← pow_succ'] at h
          · have h := Ideal.mul_mem_mul (ih2 y hy) hw
            rw [← pow_add] at h
            exact Ideal.pow_le_pow_right (by omega) h
        · intro z₁ z₂ h₁ h₂
          have e : σ (z₁ + z₂) - (z₁ + z₂) = (σ z₁ - z₁) + (σ z₂ - z₂) := by
            rw [map_add]
            ring
          rw [e]
          exact Ideal.add_mem _ h₁ h₂
      exact ⟨new1, fun x hx ↦ cancel _ _ (natCast_mul_sub_mem σ hσn m hm _
        (fun s hs ↦ hDD _ (ih2 s hs)) hx)⟩
  have hbot : σ a - a ∈ ⨅ i : ℕ, m ^ i := by
    refine Submodule.mem_iInf _ |>.mpr fun i ↦ ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · exact (key i hi).1 a
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing m (maximalIdeal.isMaximal A).ne_top] at hbot
  exact sub_eq_zero.mp ((Submodule.mem_bot A).mp hbot)

end Local

section Character

variable {k A G : Type*} [Field k] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Algebra k A] [Group G] (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ maximalIdeal A)
  (ρ : G → A →+* A) (hρ1 : ∀ a, ρ 1 a = a) (hρmul : ∀ g h a, ρ (g * h) a = ρ g (ρ h a))
  (hρk : ∀ g (c : k), ρ g (algebraMap k A c) = algebraMap k A c)
  (hρm : ∀ g, ∀ x ∈ maximalIdeal A, ρ g x ∈ maximalIdeal A)
  {π : A} (hπ : Irreducible π)

omit [Algebra k A] [Group G] in
lemma residue_eq_iff (a b : A) : residue A a = residue A b ↔ a - b ∈ maximalIdeal A :=
  Ideal.Quotient.eq

omit [Algebra k A] [Group G] in
include hπ in
lemma maximalIdeal_eq_span : maximalIdeal A = Ideal.span {π} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ

omit [Algebra k A] [Group G] in
include hπ hρm in
lemma exists_mul_eq (g : G) : ∃ u, ρ g π = π * u := by
  have h : ρ g π ∈ maximalIdeal A := hρm g π
    ((maximalIdeal_eq_span hπ).symm ▸ Ideal.mem_span_singleton_self π)
  rw [maximalIdeal_eq_span hπ, Ideal.mem_span_singleton'] at h
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [← hu, mul_comm]⟩

omit [Algebra k A] [Group G] in
/-- The unit `u` with `ρ g π = π u`. -/
noncomputable def unitOf (g : G) : A := Classical.choose (exists_mul_eq ρ hρm hπ g)

omit [Algebra k A] [Group G] in
lemma unitOf_spec (g : G) : ρ g π = π * unitOf ρ hρm hπ g :=
  Classical.choose_spec (exists_mul_eq ρ hρm hπ g)

omit [Algebra k A] [Group G] in
lemma eq_unitOf {g : G} {u : A} (h : ρ g π = π * u) : u = unitOf ρ hρm hπ g :=
  mul_left_cancel₀ hπ.ne_zero (h.symm.trans (unitOf_spec ρ hρm hπ g))

omit [Group G] in
include hres hρk hρm in
lemma residue_map (g : G) (a : A) : residue A (ρ g a) = residue A a := by
  obtain ⟨c, hc⟩ := hres a
  rw [residue_eq_iff]
  have e : ρ g a - a = ρ g (a - algebraMap k A c) - (a - algebraMap k A c) := by
    rw [map_sub, hρk]
    ring
  rw [e]
  exact (maximalIdeal A).sub_mem (hρm g _ hc) hc

/-- **The cotangent character** `g ↦ (ρ g π / π) mod m`. -/
noncomputable def character : G →* ResidueField A where
  toFun g := residue A (unitOf ρ hρm hπ g)
  map_one' := by
    rw [← eq_unitOf ρ hρm hπ (u := 1) (by rw [hρ1, mul_one]), map_one]
  map_mul' g h := by
    have e : ρ (g * h) π = π * (unitOf ρ hρm hπ g * ρ g (unitOf ρ hρm hπ h)) := by
      rw [hρmul, unitOf_spec ρ hρm hπ h, map_mul, unitOf_spec ρ hρm hπ g, mul_assoc]
    rw [← eq_unitOf ρ hρm hπ e, map_mul, residue_map hres ρ hρk hρm g]

/-- **An element with trivial cotangent character acts trivially on `m/m²`.** -/
lemma sub_mem_sq_of_character_eq_one {g : G}
    (hg : character hres ρ hρ1 hρmul hρk hρm hπ g = 1) :
    ∀ x ∈ maximalIdeal A, ρ g x - x ∈ maximalIdeal A ^ 2 := by
  intro x hx
  rw [maximalIdeal_eq_span hπ, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, rfl⟩ := hx
  have hu : unitOf ρ hρm hπ g - 1 ∈ maximalIdeal A := by
    rw [← residue_eq_iff, map_one]
    exact hg
  have hy : ρ g y - y ∈ maximalIdeal A := by
    rw [← residue_eq_iff]
    exact residue_map hres ρ hρk hρm g y
  have e : ρ g (y * π) - y * π =
      π * ((unitOf ρ hρm hπ g - 1) * ρ g y + (ρ g y - y)) := by
    rw [map_mul, unitOf_spec ρ hρm hπ g]
    ring
  rw [e, pow_two]
  refine Ideal.mul_mem_mul ?_ ((maximalIdeal A).add_mem
    ((maximalIdeal A).mul_mem_right _ hu) hy)
  rw [maximalIdeal_eq_span hπ]
  exact Ideal.mem_span_singleton_self π

end Character

section Stabilizer

variable {k C G : Type*} [Field k] [CommRing C] [Algebra k C] [Group G]
  (ρ : G →* (C ≃ₐ[k] C)) (y : Ideal C) [y.IsPrime]
  (hfix : ∀ g, y = y.comap (ρ g : C →+* C))

/-- The action on the local ring `C_y`. -/
noncomputable def locAct (g : G) : Localization.AtPrime y →+* Localization.AtPrime y :=
  Localization.localRingHom y y (ρ g : C →+* C) (hfix g)

lemma locAct_algebraMap (g : G) (c : C) :
    locAct ρ y hfix g (algebraMap C _ c) = algebraMap C _ (ρ g c) :=
  Localization.localRingHom_to_map _ _ _ _ c

lemma locAct_mul (g h : G) (a : Localization.AtPrime y) :
    locAct ρ y hfix (g * h) a = locAct ρ y hfix g (locAct ρ y hfix h a) := by
  have e : locAct ρ y hfix (g * h) = (locAct ρ y hfix g).comp (locAct ρ y hfix h) :=
    Localization.localRingHom_unique _ _ _ _ fun c ↦ by
      rw [RingHom.comp_apply, locAct_algebraMap, locAct_algebraMap]
      change _ = algebraMap C _ (ρ (g * h) c)
      rw [map_mul, AlgEquiv.mul_apply]
  rw [e, RingHom.comp_apply]

lemma locAct_one (a : Localization.AtPrime y) : locAct ρ y hfix 1 a = a := by
  have e : locAct ρ y hfix 1 = RingHom.id _ :=
    Localization.localRingHom_unique _ _ _ _ fun c ↦ by
      rw [RingHom.id_apply]
      change _ = algebraMap C _ (ρ 1 c)
      rw [map_one, AlgEquiv.one_apply]
  rw [e, RingHom.id_apply]

lemma locAct_iterate (g : G) (n : ℕ) (a : Localization.AtPrime y) :
    (locAct ρ y hfix g)^[n] a = locAct ρ y hfix (g ^ n) a := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, locAct_one]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', locAct_mul]

lemma locAct_algebraMap_k (g : G) (c : k) :
    locAct ρ y hfix g (algebraMap k _ c) = algebraMap k _ c := by
  rw [IsScalarTower.algebraMap_apply k C (Localization.AtPrime y), locAct_algebraMap,
    AlgEquiv.commutes]

lemma locAct_mem (g : G) :
    ∀ x ∈ maximalIdeal (Localization.AtPrime y),
      locAct ρ y hfix g x ∈ maximalIdeal (Localization.AtPrime y) := fun x hx ↦
  haveI : IsLocalHom (locAct ρ y hfix g) := Localization.isLocalHom_localRingHom y y _ (hfix g)
  map_nonunit (locAct ρ y hfix g) x hx

omit [Group G] in
/-- The residue field of `C_y` is `k` if `C ⧸ y` is. -/
lemma residue_surj (hres : ∀ c : C, ∃ a : k, c - algebraMap k C a ∈ y)
    (a : Localization.AtPrime y) :
    ∃ c : k, a - algebraMap k _ c ∈ maximalIdeal (Localization.AtPrime y) := by
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq y.primeCompl a
  obtain ⟨a₀, ha₀⟩ := hres x
  obtain ⟨b₀, hb₀⟩ := hres s
  have hb : b₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hb₀
    exact s.2 hb₀
  refine ⟨a₀ / b₀, ?_⟩
  have hs : IsUnit (algebraMap C (Localization.AtPrime y) s) := IsLocalization.map_units _ s
  have hmem : algebraMap C (Localization.AtPrime y) (x - algebraMap k C (a₀ / b₀) * s) ∈
      maximalIdeal (Localization.AtPrime y) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y) y]
    have e : x - algebraMap k C (a₀ / b₀) * s = (x - algebraMap k C a₀) -
        algebraMap k C (a₀ / b₀) * (s - algebraMap k C b₀) := by
      rw [mul_sub, ← map_mul, div_mul_cancel₀ a₀ hb]
      ring
    rw [e]
    exact y.sub_mem ha₀ (y.mul_mem_left _ hb₀)
  refine ((maximalIdeal (Localization.AtPrime y)).mul_unit_mem_iff_mem hs).mp ?_
  have e : (IsLocalization.mk' (Localization.AtPrime y) x s - algebraMap k _ (a₀ / b₀)) *
      algebraMap C _ s = algebraMap C _ (x - algebraMap k C (a₀ / b₀) * s) := by
    rw [sub_mul, IsLocalization.mk'_spec, map_sub, map_mul,
      IsScalarTower.algebraMap_apply k C (Localization.AtPrime y)]
  rw [e]
  exact hmem

include hfix in
/-- **I5(c), generic: a tame finite group acting faithfully on a curve and fixing a regular point
with residue field `k` is cyclic.** `G` acts on `C` by `k`-algebra automorphisms fixing the prime
`y`, faithfully, `|G|` is invertible in `k`, the local ring `C_y` is a discrete valuation ring
with residue field `k` and `C → C_y` is injective. -/
theorem isCyclic_of_faithful [Finite G] (hG : (Nat.card G : k) ≠ 0) (hρ : Function.Injective ρ)
    [IsDomain (Localization.AtPrime y)] [IsDiscreteValuationRing (Localization.AtPrime y)]
    (hres : ∀ c : C, ∃ a : k, c - algebraMap k C a ∈ y)
    (hinj : Function.Injective (algebraMap C (Localization.AtPrime y))) : IsCyclic G := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime y)
  have hres' := residue_surj y hres
  refine isCyclic_of_injective_ringHom (character hres' (locAct ρ y hfix) (locAct_one ρ y hfix)
    (locAct_mul ρ y hfix) (locAct_algebraMap_k ρ y hfix) (locAct_mem ρ y hfix) hπ) ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  have h2 := sub_mem_sq_of_character_eq_one hres' (locAct ρ y hfix) (locAct_one ρ y hfix)
    (locAct_mul ρ y hfix) (locAct_algebraMap_k ρ y hfix) (locAct_mem ρ y hfix) hπ hg
  have hid : ∀ a, locAct ρ y hfix g a = a := eq_of_iterate_eq hres' (locAct ρ y hfix g)
    (locAct_algebraMap_k ρ y hfix g) (locAct_mem ρ y hfix g) hG
    (fun a ↦ by rw [locAct_iterate, pow_card_eq_one', locAct_one]) h2
  apply hρ
  rw [map_one]
  refine AlgEquiv.ext fun c ↦ hinj ?_
  rw [← locAct_algebraMap ρ y hfix, hid, AlgEquiv.one_apply]

end Stabilizer

end StabilizerCyclic

end SemistableReduction
