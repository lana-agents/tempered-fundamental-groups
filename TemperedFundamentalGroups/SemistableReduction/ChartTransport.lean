/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChartPoints

/-!
# Locality of the local `δ`-invariants

Blueprint §9.12, O12 / R5, step (1)(a)–(b) of the plan (abstract part). Two affine charts
`Λ ⊆ Π_{j ∈ J} κ j` and `Λ' ⊆ Π_{j' ∈ J'} κ' j'` which agree after inverting `u ∈ Λ` (resp.
`u' ∈ Λ'`) have the same closed points away from `u`, with the same branches and the same local
`δ`-invariants. The components of `Λ` are identified with some components of `Λ'` by an injection
`ι : J → J'` and isomorphisms `e j : κ j ≃ κ' (ι j)` (`CompEmb`).

* `CurvePlace.map`: transport of places along isomorphisms of function fields
  (`valuation_map`: normalized valuations correspond);
* `CompEmb.Φ`, `CompEmb.Ψ`: the induced maps `Π κ → Π κ'` (zero off the image) and `Π κ' → Π κ`;
* `IsLocalIso`: `u'^N Φ(Λ) ⊆ Λ'`, `u^N Ψ(Λ') ⊆ Λ`, and `u`, `u'` are units at corresponding
  branches;
* **`IsLocalIso.dl_trI`**: for a closed point `𝔫 ∌ u` of `Λ`, the closed point `trI 𝔫` of `Λ'`
  has the transported branches and the same `δ` at every jet order;
* **`IsLocalIso.finsum_dl_eq`**: sums of `δ` over corresponding sets of closed points agree.
-/

open WithZero

namespace SemistableReduction

/-! ### Valuations with values in `ℤᵐ⁰` -/

section ZVal

/-- Two equivalent valuations with values in `ℤᵐ⁰` which both attain `exp (-1)` are equal. -/
theorem Valuation.eq_of_isEquiv_of_exp_neg_one {K : Type*} [Field K] {v₁ v₂ : Valuation K ℤᵐ⁰}
    (h : v₁.IsEquiv v₂) (h₁ : ∃ π, v₁ π = exp (-1)) (h₂ : ∃ π, v₂ π = exp (-1)) : v₁ = v₂ := by
  obtain ⟨π₁, hπ₁⟩ := h₁
  obtain ⟨π₂, hπ₂⟩ := h₂
  have hmax {v : Valuation K ℤᵐ⁰} {x : K} (hx : v x < 1) : v x ≤ exp (-1) :=
    WithZero.le_exp_of_lt_exp_add_one (by simpa using hx)
  have hlt1 : v₁ π₁ < 1 := by rw [hπ₁]; rw [← exp_zero, exp_lt_exp]; norm_num
  have hlt2 : v₂ π₂ < 1 := by rw [hπ₂]; rw [← exp_zero, exp_lt_exp]; norm_num
  have h21 : v₂ π₁ < 1 := by
    have := (h.lt_iff_lt (x := π₁) (y := 1)).1 (by rwa [map_one])
    rwa [map_one] at this
  have h12 : v₁ π₂ < 1 := by
    have := (h.lt_iff_lt (x := π₂) (y := 1)).2 (by rwa [map_one])
    rwa [map_one] at this
  have hle : v₂ π₁ ≤ v₂ π₂ := (hmax h21).trans hπ₂.ge
  have heq1 : v₁ π₁ = v₁ π₂ := le_antisymm (h.le_iff_le.2 hle) ((hmax h12).trans hπ₁.ge)
  have hv₂π₁ : v₂ π₁ = exp (-1) := by rw [← hπ₂]; exact h.eq_iff.1 heq1
  refine Valuation.ext fun f ↦ ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hf1 : v₁ f ≠ 0 := (Valuation.ne_zero_iff _).2 hf
  set n := log (v₁ f)
  have hπ0 : π₁ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ₁
    exact exp_ne_zero hπ₁.symm
  have hfv : v₁ f = v₁ (π₁ ^ (-n)) := by
    rw [map_zpow₀, hπ₁, ← exp_zsmul, show ((-n) • (-1 : ℤ)) = n by simp, exp_log hf1]
  rw [hfv, h.eq_iff.1 hfv, map_zpow₀, map_zpow₀, hπ₁, hv₂π₁]

end ZVal

/-! ### Transport of places -/

namespace CurvePlace

variable {k κ κ' : Type*} [Field k] [Field κ] [Field κ'] [Algebra k κ] [Algebra k κ']

/-- The place `Q` transported along `e : κ ≃ κ'`. -/
def map (e : κ ≃ₐ[k] κ') (Q : CurvePlace k κ) : CurvePlace k κ' where
  V := Q.V.comap e.symm.toRingEquiv.toRingHom
  algebraMap_mem c := by
    change e.symm (algebraMap k κ' c) ∈ Q.V
    rw [AlgEquiv.commutes]
    exact Q.algebraMap_mem c
  ne_top h := Q.ne_top (by
    refine eq_top_iff.2 fun x _ ↦ ?_
    have : e x ∈ Q.V.comap e.symm.toRingEquiv.toRingHom := h ▸ trivial
    change e.symm (e x) ∈ Q.V at this
    rwa [AlgEquiv.symm_apply_apply] at this)

lemma mem_map_V (e : κ ≃ₐ[k] κ') (Q : CurvePlace k κ) {a : κ'} :
    a ∈ (Q.map e).V ↔ e.symm a ∈ Q.V := Iff.rfl

lemma map_map_symm (e : κ ≃ₐ[k] κ') (Q : CurvePlace k κ') : (Q.map e.symm).map e = Q := by
  have : ((Q.map e.symm).map e).V = Q.V := by
    ext a
    rw [mem_map_V, mem_map_V, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]
  cases h : (Q.map e.symm).map e
  cases Q
  rw [h] at this
  simp only at this
  subst this
  rfl

lemma map_symm_map (e : κ ≃ₐ[k] κ') (Q : CurvePlace k κ) : (Q.map e).map e.symm = Q := by
  simpa using map_map_symm e.symm Q

lemma map_injective (e : κ ≃ₐ[k] κ') : Function.Injective (map (k := k) e) := fun Q Q' h ↦ by
  rw [← map_symm_map e Q, h, map_symm_map]

variable [IsAlgClosed k] [IsCurveFunctionField k κ] [IsCurveFunctionField k κ']

/-- **Transport of normalized valuations.** -/
theorem valuation_map (e : κ ≃ₐ[k] κ') (Q : CurvePlace k κ) (a : κ') :
    (Q.map e).valuation a = Q.valuation (e.symm a) := by
  set v₂ : Valuation κ' ℤᵐ⁰ := Q.valuation.comap e.symm.toRingEquiv.toRingHom
  have heq : (Q.map e).valuation = v₂ := by
    refine Valuation.eq_of_isEquiv_of_exp_neg_one ?_ (Q.map e).exists_valuation_eq_exp_neg_one ?_
    · refine (Valuation.isEquiv_iff_valuationSubring _ _).2 ?_
      ext x
      rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
        valuation_le_one_iff]
      change x ∈ (Q.map e).V ↔ Q.valuation (e.symm x) ≤ 1
      rw [mem_map_V, valuation_le_one_iff]
    · obtain ⟨π, hπ⟩ := Q.exists_valuation_eq_exp_neg_one
      refine ⟨e π, ?_⟩
      change Q.valuation (e.symm (e π)) = _
      rw [AlgEquiv.symm_apply_apply, hπ]
  rw [heq]
  rfl

lemma valuation_map_apply (e : κ ≃ₐ[k] κ') (Q : CurvePlace k κ) (a : κ) :
    (Q.map e).valuation (e a) = Q.valuation a := by
  rw [valuation_map, AlgEquiv.symm_apply_apply]

end CurvePlace

namespace ChartLocal

open DeltaCount CurvePlace

/-! ### Embeddings of families of components -/

section Emb

variable (k : Type*) [Field k] {J J' : Type*} (κ : J → Type*) (κ' : J' → Type*)
  [∀ j, Field (κ j)] [∀ j, Algebra k (κ j)] [∀ j, Field (κ' j)] [∀ j, Algebra k (κ' j)]

/-- An identification of the components `κ j` with some of the components `κ' j'`. -/
structure CompEmb where
  /-- The map on indices. -/
  ι : J → J'
  inj : Function.Injective ι
  /-- The isomorphisms of components. -/
  e : ∀ j, κ j ≃ₐ[k] κ' (ι j)

variable {k κ κ'} (E : CompEmb k κ κ')

namespace CompEmb

open Classical in
/-- `Π κ → Π κ'`, zero off the image of `ι`. -/
noncomputable def Φ (a : Π j, κ j) : Π j', κ' j' := fun j' ↦
  if h : ∃ j, E.ι j = j' then h.choose_spec ▸ E.e h.choose (a h.choose) else 0

lemma Φ_apply (a : Π j, κ j) (j : J) : E.Φ a (E.ι j) = E.e j (a j) := by
  have key : ∀ (j₀ : J) (h : E.ι j₀ = E.ι j),
      (h ▸ E.e j₀ (a j₀) : κ' (E.ι j)) = E.e j (a j) := by
    intro j₀ h
    obtain rfl := E.inj h
    rfl
  have hex : ∃ j₀, E.ι j₀ = E.ι j := ⟨j, rfl⟩
  rw [Φ, dif_pos hex]
  exact key _ hex.choose_spec

lemma Φ_apply_of_not {a : Π j, κ j} {j' : J'} (h : ¬ ∃ j, E.ι j = j') : E.Φ a j' = 0 := by
  rw [Φ, dif_neg h]

/-- `Π κ' → Π κ`. -/
def Ψ (a' : Π j', κ' j') : Π j, κ j := fun j ↦ (E.e j).symm (a' (E.ι j))

lemma Ψ_apply (a' : Π j', κ' j') (j : J) : E.Ψ a' j = (E.e j).symm (a' (E.ι j)) := rfl

@[simp] lemma Ψ_Φ (a : Π j, κ j) : E.Ψ (E.Φ a) = a := by
  funext j
  rw [Ψ_apply, Φ_apply, AlgEquiv.symm_apply_apply]

lemma Φ_ext {a : Π j, κ j} {a' : Π j', κ' j'} (h₁ : ∀ j, E.e j (a j) = a' (E.ι j))
    (h₂ : ∀ j', (¬ ∃ j, E.ι j = j') → a' j' = 0) : E.Φ a = a' := by
  funext j'
  by_cases h : ∃ j, E.ι j = j'
  · obtain ⟨j, rfl⟩ := h
    rw [Φ_apply, h₁]
  · rw [Φ_apply_of_not E h, h₂ j' h]

lemma Φ_add (a b : Π j, κ j) : E.Φ (a + b) = E.Φ a + E.Φ b :=
  E.Φ_ext (fun j ↦ by simp [Φ_apply]) fun j' h ↦ by
    simp [Φ_apply_of_not E h]

lemma Φ_mul (a b : Π j, κ j) : E.Φ (a * b) = E.Φ a * E.Φ b :=
  E.Φ_ext (fun j ↦ by simp [Φ_apply]) fun j' h ↦ by
    simp [Φ_apply_of_not E h]

lemma Φ_zero : E.Φ 0 = 0 :=
  E.Φ_ext (fun j ↦ by simp) fun _ _ ↦ rfl

lemma Φ_smul (c : k) (a : Π j, κ j) : E.Φ (c • a) = c • E.Φ a :=
  E.Φ_ext (fun j ↦ by simp [Φ_apply]) fun j' h ↦ by
    simp [Φ_apply_of_not E h]

lemma Ψ_add (a b : Π j', κ' j') : E.Ψ (a + b) = E.Ψ a + E.Ψ b := by
  funext j; simp [Ψ_apply]

lemma Ψ_mul (a b : Π j', κ' j') : E.Ψ (a * b) = E.Ψ a * E.Ψ b := by
  funext j; simp [Ψ_apply]

lemma Ψ_pow (a : Π j', κ' j') (n : ℕ) : E.Ψ (a ^ n) = E.Ψ a ^ n := by
  funext j; simp [Ψ_apply]

lemma Ψ_smul (c : k) (a : Π j', κ' j') : E.Ψ (c • a) = c • E.Ψ a := by
  funext j; simp [Ψ_apply]

lemma Ψ_zero : E.Ψ 0 = 0 := by
  funext j; simp [Ψ_apply]

/-- `Φ` as a linear map. -/
noncomputable def ΦL : (Π j, κ j) →ₗ[k] (Π j', κ' j') where
  toFun := E.Φ
  map_add' := E.Φ_add
  map_smul' := E.Φ_smul

/-- `Ψ` as a linear map. -/
def ΨL : (Π j', κ' j') →ₗ[k] (Π j, κ j) where
  toFun := E.Ψ
  map_add' := E.Ψ_add
  map_smul' := E.Ψ_smul

/-- The transport of a branch. -/
def pmap (b : Branch k κ) : Branch k κ' := ⟨E.ι b.1, b.2.map (E.e b.1)⟩

lemma pmap_fst (b : Branch k κ) : (E.pmap b).1 = E.ι b.1 := rfl

lemma pmap_injective : Function.Injective E.pmap := by
  rintro ⟨j₁, Q₁⟩ ⟨j₂, Q₂⟩ h
  simp only [pmap, Sigma.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain rfl := E.inj h1
  simp only [heq_eq_eq] at h2
  rw [map_injective _ h2]

lemma exists_pmap_eq {b' : Branch k κ'} (h : ∃ j, E.ι j = b'.1) : ∃ b, E.pmap b = b' := by
  obtain ⟨j', Q'⟩ := b'
  obtain ⟨j, rfl⟩ := h
  exact ⟨⟨j, Q'.map (E.e j).symm⟩, by simp [pmap, map_map_symm]⟩

variable [IsAlgClosed k] [∀ j, IsCurveFunctionField k (κ j)] [∀ j, IsCurveFunctionField k (κ' j)]

lemma val_Φ (b : Branch k κ) (a : Π j, κ j) :
    (E.pmap b).2.valuation (E.Φ a (E.pmap b).1) = b.2.valuation (a b.1) := by
  obtain ⟨j, Q⟩ := b
  change (Q.map (E.e j)).valuation (E.Φ a (E.ι j)) = Q.valuation (a j)
  rw [Φ_apply]
  exact valuation_map_apply _ _ _

lemma val_Ψ (b : Branch k κ) (a' : Π j', κ' j') :
    b.2.valuation (E.Ψ a' b.1) = (E.pmap b).2.valuation (a' (E.pmap b).1) := by
  obtain ⟨j, Q⟩ := b
  change Q.valuation ((E.e j).symm (a' (E.ι j))) = (Q.map (E.e j)).valuation (a' (E.ι j))
  exact (valuation_map _ _ _).symm

lemma mem_V_Φ (b : Branch k κ) (a : Π j, κ j) :
    E.Φ a (E.pmap b).1 ∈ (E.pmap b).2.V ↔ a b.1 ∈ b.2.V := by
  rw [← valuation_le_one_iff, ← valuation_le_one_iff, val_Φ]

lemma mem_V_Ψ (b : Branch k κ) (a' : Π j', κ' j') :
    E.Ψ a' b.1 ∈ b.2.V ↔ a' (E.pmap b).1 ∈ (E.pmap b).2.V := by
  rw [← valuation_le_one_iff, ← valuation_le_one_iff, val_Ψ]

end CompEmb

end Emb

/-! ### Charts which agree after inverting `u` -/

section Local

variable {k : Type*} [Field k] [IsAlgClosed k] {J J' : Type*} {κ : J → Type*} {κ' : J' → Type*}
  [∀ j, Field (κ j)] [∀ j, Algebra k (κ j)] [∀ j, IsCurveFunctionField k (κ j)]
  [∀ j, Field (κ' j)] [∀ j, Algebra k (κ' j)] [∀ j, IsCurveFunctionField k (κ' j)]
  {z : Π j, κ j} {Λ : Subring (Π j, κ j)} {z' : Π j', κ' j'} {Λ' : Subring (Π j', κ' j')}

/-- The charts `Λ` and `Λ'` agree after inverting `u ∈ Λ` and `u' ∈ Λ'` (which are units at
corresponding branches). -/
structure IsLocalIso (hΛ : IsChart k z Λ) (hΛ' : IsChart k z' Λ') (E : CompEmb k κ κ')
    (u : Π j, κ j) (u' : Π j', κ' j') : Prop where
  mem_u : u ∈ Λ
  mem_u' : u' ∈ Λ'
  fwd : ∀ a ∈ Λ, ∃ N : ℕ, u' ^ N * E.Φ a ∈ Λ'
  bwd : ∀ a' ∈ Λ', ∃ N : ℕ, u ^ N * E.Ψ a' ∈ Λ
  unit : ∀ b : Branch k κ, z b.1 ∈ b.2.V → b.2.valuation (u b.1) = 1 →
    b.2.valuation (E.Ψ u' b.1) = 1
  unit' : ∀ b' : Branch k κ', z' b'.1 ∈ b'.2.V → b'.2.valuation (u' b'.1) = 1 →
    b'.2.valuation (E.Φ u b'.1) = 1

open Classical in
/-- The closed point of `Λ'` corresponding to a closed point `𝔫` of `Λ`: the centre of the
transport of a branch of `𝔫`. -/
noncomputable def trI (hΛ : IsChart k z Λ) (hΛ' : IsChart k z' Λ') (E : CompEmb k κ κ')
    (𝔫 : Ideal Λ) : Ideal Λ' :=
  if h : ∃ b, b ∈ brs hΛ 𝔫 then centerOf hΛ' (E.pmap h.choose) else ⊤

namespace IsLocalIso

variable {hΛ : IsChart k z Λ} {hΛ' : IsChart k z' Λ'} {E : CompEmb k κ κ'}
  {u : Π j, κ j} {u' : Π j', κ' j'} (H : IsLocalIso hΛ hΛ' E u u')
include H

lemma fwd' {a : Π j, κ j} (ha : a ∈ Λ) : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → u' ^ N * E.Φ a ∈ Λ' := by
  obtain ⟨N₀, h⟩ := H.fwd a ha
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have : u' ^ N * E.Φ a = u' ^ (N - N₀) * (u' ^ N₀ * E.Φ a) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]
  rw [this]
  exact mul_mem (pow_mem H.mem_u' _) h

lemma bwd' {a' : Π j', κ' j'} (ha : a' ∈ Λ') : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → u ^ N * E.Ψ a' ∈ Λ := by
  obtain ⟨N₀, h⟩ := H.bwd a' ha
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have : u ^ N * E.Ψ a' = u ^ (N - N₀) * (u ^ N₀ * E.Ψ a') := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]
  rw [this]
  exact mul_mem (pow_mem H.mem_u _) h

/-- At a branch where `u` is a unit, `z'` is regular at the transported branch. -/
lemma z'_mem {b : Branch k κ} (hz : z b.1 ∈ b.2.V) (hub : b.2.valuation (u b.1) = 1) :
    z' (E.pmap b).1 ∈ (E.pmap b).2.V := by
  obtain ⟨N, hN⟩ := H.bwd z' hΛ'.mem
  have h1 := b.2.valuation_le_one_iff.2 (hΛ.le hN b.1 b.2 hz)
  rw [Pi.mul_apply, map_mul, Pi.pow_apply, map_pow, hub, one_pow, one_mul] at h1
  exact (E.mem_V_Ψ b z').1 (b.2.valuation_le_one_iff.1 h1)

lemma u'_unit {b : Branch k κ} (hz : z b.1 ∈ b.2.V) (hub : b.2.valuation (u b.1) = 1) :
    (E.pmap b).2.valuation (u' (E.pmap b).1) = 1 := by
  rw [← E.val_Ψ]; exact H.unit b hz hub

/-- A branch of `Λ'` at which `u'` is a unit is a transported branch, at which `u` is a unit. -/
lemma exists_pmap {b' : Branch k κ'} (hz : z' b'.1 ∈ b'.2.V)
    (hub : b'.2.valuation (u' b'.1) = 1) :
    ∃ b, E.pmap b = b' ∧ z b.1 ∈ b.2.V ∧ b.2.valuation (u b.1) = 1 := by
  have h1 := H.unit' b' hz hub
  have hex : ∃ j, E.ι j = b'.1 := by
    by_contra h
    rw [E.Φ_apply_of_not h, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨b, rfl⟩ := E.exists_pmap_eq hex
  rw [E.val_Φ] at h1
  refine ⟨b, rfl, ?_, h1⟩
  obtain ⟨N, hN⟩ := H.fwd z hΛ.mem
  have h2 := (E.pmap b).2.valuation_le_one_iff.2 (hΛ'.le hN (E.pmap b).1 (E.pmap b).2 hz)
  rw [Pi.mul_apply, map_mul, Pi.pow_apply, map_pow, hub, one_pow, one_mul, E.val_Φ] at h2
  exact b.2.valuation_le_one_iff.1 h2

variable {𝔫 : Ideal Λ}

lemma mem_centerOf_pmap_iff (h𝔫 : 𝔫 ≠ ⊤) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) {b : Branch k κ}
    (hb : b ∈ brs hΛ 𝔫) (a' : Λ') {N : ℕ} (hN : u ^ N * E.Ψ a' ∈ Λ) :
    a' ∈ centerOf hΛ' (E.pmap b) ↔ (⟨_, hN⟩ : Λ) ∈ 𝔫 := by
  have hz := mem_V_of_mem_brs hΛ h𝔫 hb
  have hub := valuation_eq_one_of_notMem hΛ h𝔫 hb hu𝔫
  rw [centerOf_eq hΛ' (H.z'_mem hz hub), mem_center, mem_iff_of_mem_brs hΛ h𝔫 hb]
  change _ ↔ b.2.valuation ((u ^ N * E.Ψ a') b.1) < 1
  rw [Pi.mul_apply, map_mul, Pi.pow_apply, map_pow, hub, one_pow, one_mul, E.val_Ψ]

lemma centerOf_pmap_eq (h𝔫 : 𝔫 ≠ ⊤) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) {b₁ b₂ : Branch k κ}
    (hb₁ : b₁ ∈ brs hΛ 𝔫) (hb₂ : b₂ ∈ brs hΛ 𝔫) :
    centerOf hΛ' (E.pmap b₁) = centerOf hΛ' (E.pmap b₂) := by
  ext a'
  obtain ⟨N, hN⟩ := H.bwd a'.1 a'.2
  rw [H.mem_centerOf_pmap_iff h𝔫 hu𝔫 hb₁ a' hN, H.mem_centerOf_pmap_iff h𝔫 hu𝔫 hb₂ a' hN]

lemma trI_eq (h𝔫 : 𝔫 ≠ ⊤) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) {b : Branch k κ}
    (hb : b ∈ brs hΛ 𝔫) : trI hΛ hΛ' E 𝔫 = centerOf hΛ' (E.pmap b) := by
  classical
  have h : ∃ b, b ∈ brs hΛ 𝔫 := ⟨b, hb⟩
  rw [trI, dif_pos h]
  exact H.centerOf_pmap_eq h𝔫 hu𝔫 h.choose_spec hb

variable [Finite J]

lemma trI_isMaximal (h𝔫 : 𝔫.IsMaximal) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) :
    (trI hΛ hΛ' E 𝔫).IsMaximal := by
  obtain ⟨b, hb⟩ := exists_mem_brs hΛ h𝔫
  have hz := mem_V_of_mem_brs hΛ h𝔫.ne_top hb
  have hub := valuation_eq_one_of_notMem hΛ h𝔫.ne_top hb hu𝔫
  rw [H.trI_eq h𝔫.ne_top hu𝔫 hb, centerOf_eq hΛ' (H.z'_mem hz hub)]
  exact center_isMaximal hΛ' _ _

lemma u'_notMem_trI (h𝔫 : 𝔫.IsMaximal) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) :
    (⟨u', H.mem_u'⟩ : Λ') ∉ trI hΛ hΛ' E 𝔫 := by
  obtain ⟨b, hb⟩ := exists_mem_brs hΛ h𝔫
  have hz := mem_V_of_mem_brs hΛ h𝔫.ne_top hb
  have hub := valuation_eq_one_of_notMem hΛ h𝔫.ne_top hb hu𝔫
  rw [H.trI_eq h𝔫.ne_top hu𝔫 hb, centerOf_eq hΛ' (H.z'_mem hz hub), mem_center]
  change ¬ (E.pmap b).2.valuation (u' (E.pmap b).1) < 1
  rw [H.u'_unit hz hub]
  exact lt_irrefl _

/-- An element of `Λ` lies in `𝔫` iff its transport lies in `trI 𝔫`. -/
lemma mem_iff_mem_trI (h𝔫 : 𝔫.IsMaximal) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) (a : Λ) (a' : Λ')
    (ha : ∀ b : Branch k κ, z b.1 ∈ b.2.V → b.2.valuation (u b.1) = 1 →
      (b.2.valuation (a.1 b.1) < 1 ↔ (E.pmap b).2.valuation (a'.1 (E.pmap b).1) < 1)) :
    a ∈ 𝔫 ↔ a' ∈ trI hΛ hΛ' E 𝔫 := by
  obtain ⟨b, hb⟩ := exists_mem_brs hΛ h𝔫
  have hz := mem_V_of_mem_brs hΛ h𝔫.ne_top hb
  have hub := valuation_eq_one_of_notMem hΛ h𝔫.ne_top hb hu𝔫
  rw [H.trI_eq h𝔫.ne_top hu𝔫 hb, centerOf_eq hΛ' (H.z'_mem hz hub), mem_center,
    mem_iff_of_mem_brs hΛ h𝔫.ne_top hb]
  exact ha b hz hub

/-- **The branches of the transported point** are the transported branches. -/
theorem brs_trI (h𝔫 : 𝔫.IsMaximal) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) :
    brs hΛ' (trI hΛ hΛ' E 𝔫) = E.pmap '' brs hΛ 𝔫 := by
  obtain ⟨b₀, hb₀⟩ := exists_mem_brs hΛ h𝔫
  have hz₀ := mem_V_of_mem_brs hΛ h𝔫.ne_top hb₀
  have hub₀ := valuation_eq_one_of_notMem hΛ h𝔫.ne_top hb₀ hu𝔫
  have hmax' := H.trI_isMaximal h𝔫 hu𝔫
  ext b'
  constructor
  · intro hb'
    have hz' := mem_V_of_mem_brs hΛ' hmax'.ne_top hb'
    have hu' := valuation_eq_one_of_notMem hΛ' hmax'.ne_top hb' (H.u'_notMem_trI h𝔫 hu𝔫)
    obtain ⟨b, rfl, hz, hub⟩ := H.exists_pmap hz' hu'
    refine ⟨b, ?_, rfl⟩
    rw [mem_brs, centerOf_eq hΛ hz]
    ext a
    rw [mem_center]
    obtain ⟨N₀, hN₀⟩ := H.fwd' a.2
    have hN := hN₀ N₀ le_rfl
    have key (c : Branch k κ) (hzc : z c.1 ∈ c.2.V) (huc : c.2.valuation (u c.1) = 1) :
        (E.pmap c).2.valuation ((u' ^ N₀ * E.Φ a.1) (E.pmap c).1) =
          c.2.valuation (a.1 c.1) := by
      rw [Pi.mul_apply, map_mul, Pi.pow_apply, map_pow, H.u'_unit hzc huc, one_pow, one_mul,
        E.val_Φ]
    rw [← key b hz hub, ← mem_iff_of_mem_brs hΛ' hmax'.ne_top hb' ⟨_, hN⟩,
      H.trI_eq h𝔫.ne_top hu𝔫 hb₀, centerOf_eq hΛ' (H.z'_mem hz₀ hub₀), mem_center]
    change (E.pmap b₀).2.valuation ((u' ^ N₀ * E.Φ a.1) (E.pmap b₀).1) < 1 ↔ a ∈ 𝔫
    rw [key b₀ hz₀ hub₀, mem_iff_of_mem_brs hΛ h𝔫.ne_top hb₀]
  · rintro ⟨b, hb, rfl⟩
    exact (H.trI_eq h𝔫.ne_top hu𝔫 hb).symm

/-- The transport of the local ring. -/
lemma Φ_mem_locSet (h𝔫 : 𝔫.IsMaximal) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) {a : Π j, κ j}
    (ha : a ∈ locSet 𝔫) : E.Φ a ∈ locSet (trI hΛ hΛ' E 𝔫) := by
  obtain ⟨s, hs, hsa⟩ := ha
  obtain ⟨N₁, hN₁⟩ := H.fwd' s.2
  obtain ⟨N₂, hN₂⟩ := H.fwd' hsa
  set N := max N₁ N₂
  obtain ⟨b₀, hb₀⟩ := exists_mem_brs hΛ h𝔫
  have hz₀ := mem_V_of_mem_brs hΛ h𝔫.ne_top hb₀
  have hub₀ := valuation_eq_one_of_notMem hΛ h𝔫.ne_top hb₀ hu𝔫
  refine ⟨⟨_, hN₁ N (le_max_left _ _)⟩, ?_, ?_⟩
  · rw [H.trI_eq h𝔫.ne_top hu𝔫 hb₀, centerOf_eq hΛ' (H.z'_mem hz₀ hub₀), mem_center]
    change ¬ (E.pmap b₀).2.valuation ((u' ^ N * E.Φ s.1) (E.pmap b₀).1) < 1
    rw [Pi.mul_apply, map_mul, Pi.pow_apply, map_pow, H.u'_unit hz₀ hub₀, one_pow, one_mul,
      E.val_Φ, valuation_eq_one_of_notMem hΛ h𝔫.ne_top hb₀ hs]
    exact lt_irrefl _
  · change u' ^ N * E.Φ s.1 * E.Φ a ∈ Λ'
    rw [mul_assoc, ← E.Φ_mul]
    exact hN₂ N (le_max_right _ _)

lemma Ψ_mem_locSet (h𝔫 : 𝔫.IsMaximal) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) {a' : Π j', κ' j'}
    (ha : a' ∈ locSet (trI hΛ hΛ' E 𝔫)) : E.Ψ a' ∈ locSet 𝔫 := by
  obtain ⟨s, hs, hsa⟩ := ha
  obtain ⟨N₁, hN₁⟩ := H.bwd' s.2
  obtain ⟨N₂, hN₂⟩ := H.bwd' hsa
  set N := max N₁ N₂
  obtain ⟨b₀, hb₀⟩ := exists_mem_brs hΛ h𝔫
  refine ⟨⟨_, hN₁ N (le_max_left _ _)⟩, ?_, ?_⟩
  · rw [← H.mem_centerOf_pmap_iff h𝔫.ne_top hu𝔫 hb₀, ← H.trI_eq h𝔫.ne_top hu𝔫 hb₀]
    exact hs
  · change u ^ N * E.Ψ s.1 * E.Ψ a' ∈ Λ
    rw [mul_assoc, ← E.Ψ_mul]
    exact hN₂ N (le_max_right _ _)

/-- **Equality of the local `δ`-invariants** at corresponding points. -/
theorem dl_trI [Finite J'] (h𝔫 : 𝔫.IsMaximal) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) (M : ℕ) :
    dl k κ' hΛ' (trI hΛ hΛ' E 𝔫) M = dl k κ hΛ 𝔫 M := by
  classical
  have hmax' := H.trI_isMaximal h𝔫 hu𝔫
  set S := brsF hΛ 𝔫
  set S' := brsF hΛ' (trI hΛ hΛ' E 𝔫)
  have hS' (b' : Branch k κ') : b' ∈ S' ↔ ∃ b ∈ S, E.pmap b = b' := by
    rw [mem_brsF hΛ' hmax'.ne_top, H.brs_trI h𝔫 hu𝔫]
    simp only [Set.mem_image]
    exact exists_congr fun b ↦ and_congr_left' (mem_brsF hΛ h𝔫.ne_top).symm
  set L := locSpace k 𝔫
  set L' := locSpace k (trI hΛ hΛ' E 𝔫)
  have hΦL : L.map E.ΦL ≤ L' := by
    refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 fun a ha ↦ ?_)
    exact subset_locSpace _ (H.Φ_mem_locSet h𝔫 hu𝔫 ha)
  have hΨL : L'.map E.ΨL ≤ L := by
    refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 fun a ha ↦ ?_)
    exact subset_locSpace _ (H.Ψ_mem_locSet h𝔫 hu𝔫 ha)
  have hΦK (a : Π j, κ j) (ha : a ∈ jetKer k κ M S) : E.Φ a ∈ jetKer k κ' M S' := by
    intro b' hb'
    obtain ⟨b, hb, rfl⟩ := (hS' b').1 hb'
    rw [E.val_Φ]; exact ha b hb
  have hΨK (a : Π j', κ' j') (ha : a ∈ jetKer k κ' M S') : E.Ψ a ∈ jetKer k κ M S := by
    intro b hb
    rw [E.val_Ψ]; exact ha _ ((hS' _).2 ⟨b, hb, rfl⟩)
  have hΦreg (a : Π j, κ j) (ha : a ∈ regAt k κ S) : E.Φ a ∈ regAt k κ' S' := by
    intro b' hb'
    obtain ⟨b, hb, rfl⟩ := (hS' b').1 hb'
    rw [E.mem_V_Φ]; exact ha b hb
  have hΨreg (a : Π j', κ' j') (ha : a ∈ regAt k κ' S') : E.Ψ a ∈ regAt k κ S := by
    intro b hb
    rw [E.mem_V_Ψ]; exact ha _ ((hS' _).2 ⟨b, hb, rfl⟩)
  set N' := (L' ⊔ jetKer k κ' M S').comap (regAt k κ' S').subtype
  set f : regAt k κ S →ₗ[k] regAt k κ' S' ⧸ N' :=
    N'.mkQ ∘ₗ (E.ΦL.restrict fun a ha ↦ hΦreg a ha)
  have hf (a : regAt k κ S) : f a = N'.mkQ ⟨E.Φ a, hΦreg a a.2⟩ := rfl
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨a', rfl⟩ := N'.mkQ_surjective q
    refine ⟨⟨E.Ψ a', hΨreg a' a'.2⟩, ?_⟩
    rw [hf, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
      Submodule.mem_comap]
    refine Submodule.mem_sup_right fun b' hb' ↦ ?_
    obtain ⟨b, -, rfl⟩ := (hS' b').1 hb'
    obtain ⟨j, Q⟩ := b
    change (Q.map (E.e j)).valuation (E.Φ (E.Ψ a') (E.ι j) - a'.1 (E.ι j)) ≤ _
    rw [E.Φ_apply, E.Ψ_apply, AlgEquiv.apply_symm_apply, sub_self, map_zero]
    exact zero_le
  have hker : LinearMap.ker f = (L ⊔ jetKer k κ M S).comap (regAt k κ S).subtype := by
    ext a
    rw [LinearMap.mem_ker, hf, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_subtype]
    change E.Φ a.1 ∈ L' ⊔ jetKer k κ' M S' ↔ a.1 ∈ L ⊔ jetKer k κ M S
    constructor
    · intro h
      obtain ⟨l, hl, kk, hk, hlk⟩ := Submodule.mem_sup.1 h
      have : a.1 = E.Ψ l + E.Ψ kk := by rw [← E.Ψ_add, hlk, E.Ψ_Φ]
      rw [this]
      exact add_mem (Submodule.mem_sup_left (hΨL ⟨l, hl, rfl⟩))
        (Submodule.mem_sup_right (hΨK kk hk))
    · intro h
      obtain ⟨l, hl, kk, hk, hlk⟩ := Submodule.mem_sup.1 h
      rw [← hlk, E.Φ_add]
      exact add_mem (Submodule.mem_sup_left (hΦL ⟨l, hl, rfl⟩))
        (Submodule.mem_sup_right (hΦK kk hk))
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)
  exact e.finrank_eq.symm

theorem dinf_trI [Finite J'] (h𝔫 : 𝔫.IsMaximal) (hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫) :
    dinf k κ' hΛ' (trI hΛ hΛ' E 𝔫) = dinf k κ hΛ 𝔫 := by
  rw [dinf, dinf]
  exact iSup_congr fun M ↦ H.dl_trI h𝔫 hu𝔫 M

/-- **Sums of local `δ`-invariants** over corresponding sets of closed points agree. -/
theorem finsum_eq [Finite J'] (P : Ideal Λ → Prop) (P' : Ideal Λ' → Prop)
    (hP : ∀ 𝔫 : Ideal Λ, 𝔫.IsMaximal → (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫 →
      (P 𝔫 ↔ P' (trI hΛ hΛ' E 𝔫)))
    (f : Ideal Λ → ℕ) (f' : Ideal Λ' → ℕ)
    (hf : ∀ 𝔫 : Ideal Λ, 𝔫.IsMaximal → (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫 → f' (trI hΛ hΛ' E 𝔫) = f 𝔫) :
    ∑ᶠ (𝔫 : Ideal Λ) (_ : 𝔫 ∈ {𝔫 : Ideal Λ | 𝔫.IsMaximal ∧ (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫 ∧ P 𝔫}),
        f 𝔫 =
      ∑ᶠ (𝔫' : Ideal Λ') (_ : 𝔫' ∈ {𝔫' : Ideal Λ' | 𝔫'.IsMaximal ∧
        (⟨u', H.mem_u'⟩ : Λ') ∉ 𝔫' ∧ P' 𝔫'}), f' 𝔫' := by
  refine finsum_mem_eq_of_bijOn (trI hΛ hΛ' E) ⟨?_, ?_, ?_⟩ fun 𝔫 h𝔫 ↦ (hf 𝔫 h𝔫.1 h𝔫.2.1).symm
  · rintro 𝔫 ⟨h1, h2, h3⟩
    exact ⟨H.trI_isMaximal h1 h2, H.u'_notMem_trI h1 h2, (hP 𝔫 h1 h2).1 h3⟩
  · rintro 𝔫₁ ⟨h1, h2, -⟩ 𝔫₂ ⟨h1', h2', -⟩ heq
    obtain ⟨b, hb⟩ := exists_mem_brs hΛ h1
    have hb' : E.pmap b ∈ brs hΛ' (trI hΛ hΛ' E 𝔫₂) := by
      rw [← heq, H.brs_trI h1 h2]; exact ⟨b, hb, rfl⟩
    rw [H.brs_trI h1' h2'] at hb'
    obtain ⟨b₂, hb₂, hbb⟩ := hb'
    rw [E.pmap_injective hbb] at hb₂
    rw [← (show centerOf hΛ b = 𝔫₁ from hb), ← (show centerOf hΛ b = 𝔫₂ from hb₂)]
  · rintro 𝔫' ⟨h1, h2, h3⟩
    obtain ⟨j', Q', hQ', hc⟩ := exists_center_eq hΛ' 𝔫'
    have hb' : (⟨j', Q'⟩ : Branch k κ') ∈ brs hΛ' 𝔫' := by
      rw [mem_brs, centerOf_eq hΛ' hQ']; exact hc
    have hu' := valuation_eq_one_of_notMem hΛ' h1.ne_top hb' h2
    obtain ⟨b, hbb, hz, hub⟩ := H.exists_pmap hQ' hu'
    set 𝔫 := centerOf hΛ b
    have hb : b ∈ brs hΛ 𝔫 := rfl
    have hmax : 𝔫.IsMaximal := by
      rw [show 𝔫 = _ from centerOf_eq hΛ hz]; exact center_isMaximal _ _ _
    have hu𝔫 : (⟨u, H.mem_u⟩ : Λ) ∉ 𝔫 := by
      rw [mem_iff_of_mem_brs hΛ hmax.ne_top hb]
      change ¬ b.2.valuation (u b.1) < 1
      rw [hub]; exact lt_irrefl _
    have htr : trI hΛ hΛ' E 𝔫 = 𝔫' := by
      rw [H.trI_eq hmax.ne_top hu𝔫 hb, hbb]; exact hb'
    refine ⟨𝔫, ⟨hmax, hu𝔫, (hP 𝔫 hmax hu𝔫).2 (htr ▸ h3)⟩, htr⟩

end IsLocalIso

end Local

end ChartLocal

end SemistableReduction
