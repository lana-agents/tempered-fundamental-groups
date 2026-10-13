/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.DihedralLine

/-!
# Characters detected at one level; the explicit Tate model towers (Blueprint §12.10, M4)

Let `T` be a tree tower over `Γ` and `χ : Γ →* M` a homomorphism which is **detected at a level
`j₀` with finite vertex stabilizers**: `χ g = 1` as soon as `g` acts trivially on the tree at
`j₀` (for André's tower: `χ` continuous to a discrete group, e.g. the character of the
`ℤ`-covering `Y` of a Tate curve, `Andre/TateEstrangement.lean`), and the stabilizers of the
vertices of the tree at `j₀` are finite.

* **`isOfFinOrder_of_elliptic`**: an elliptic element (fixing a vertex at every level) has
  `χ g` of finite order; for torsion-free `M` (`eq_one_of_elliptic`, e.g. `M = ℤ`,
  `isOfFinOrder_multiplicative_int`) **elliptic elements lie in `ker χ`**;
* **`hyperbolicAt_of_ne_one`**, **`estrangedElt_of_ne_one`**: every `g` with `χ g ≠ 1` (`M`
  torsion-free) fixes no vertex at `j₀` and is estranged, at all levels below `j₀`, wild ones
  included; `estrangedOn_iff_ker`: estrangement only has to be checked on `ker χ`;
* powers: the fixed set of `g` is contained in that of `g ^ n`, so `EstrangedElt.of_pow`
  (`g ^ n` estranged ⇒ `g` estranged) and `Elliptic.pow`.

**The explicit Tate model towers.** The graph part of the explicit Tate coverings is the line of
`SemiAnbd/DihedralLine.lean`, on which a group acts through a homomorphism `χ : Γ →* D_∞`.
`DihedralLine.estrangedElt_comap_iff`: **in the pulled back line tower, `g` is estranged iff
`χ g ≠ 1`**; the elements of `ker χ` fix the whole line at every level (the line has vertices at
distance `3`, `dist_ge`). For the deck group `ℤ × ℤ/2` of `Ÿ → X` (the `ℤ`-covering `Y` followed
by the double covering `Ü² = U`), the involution acts trivially on the dual graph (it fixes the
skeleton of `G_m` pointwise; in the repository's `TateObject.Yddot` it acts trivially on the
covering space of the special fibre), so `ℤ × ℤ/2` acts on the line through the translations
of the first factor (`yddotHom`, `yddotTower`): `yddot_estrangedElt_iff` (estranged iff the
`ℤ`-component is nontrivial), **`not_estranged_yddot`** (the involution `(0, 1)` is not
estranged: the explicit Tate levels cannot detect the Kummer part), and all system stabilizers
coincide with `{0} × ℤ/2` (`mem_stab_yddot`), so the correspondence between systems and maximal
finite subgroups of [SemiAnbd] Thm. 3.7(iv) is not injective in this model.
-/

universe u v w x

open CategoryTheory SimpleGraph DihedralGroup TemperedFundamentalGroups.TreeGeom

namespace TemperedFundamentalGroups

namespace TreeTower

variable {Γ : Type x} [Group Γ] {J : Type u} [Category.{v} J] {T : TreeTower.{u, v, w} Γ J}

/-! ### Powers -/

/-- The fixed set of `g` is contained in that of `g ^ n`. -/
lemma SmallFixAt.of_pow {k : J} {g : Γ} {n : ℕ} (h : T.SmallFixAt k (g ^ n)) :
    T.SmallFixAt k g := fun x y hx hy ↦
  h x y ((T.fixAt k x).pow_mem (mem_fixAt.2 hx) n) ((T.fixAt k y).pow_mem (mem_fixAt.2 hy) n)

/-- **If `g ^ n` is estranged, so is `g`.** -/
lemma EstrangedElt.of_pow {g : Γ} {n : ℕ} (h : T.EstrangedElt (g ^ n)) : T.EstrangedElt g :=
  fun j ↦ (h j).imp fun _ ⟨f, hk⟩ ↦ ⟨f, hk.of_pow⟩

/-- Powers of elliptic elements are elliptic. -/
lemma Elliptic.pow {g : Γ} (h : T.Elliptic g) (n : ℕ) : T.Elliptic (g ^ n) := fun j ↦
  (h j).imp fun v hv ↦ (T.fixAt j v).pow_mem (mem_fixAt.2 hv) n

/-! ### Characters detected at a level -/

section Character

variable {M : Type*} [Group M] (χ : Γ →* M) {j₀ : J}

/-- If `χ` is detected at `j₀` and the vertex stabilizers at `j₀` are finite, an element fixing
a vertex at `j₀` has `χ g` of finite order. -/
theorem isOfFinOrder_of_fixed (hχ : ∀ g, T.ρ j₀ g = 1 → χ g = 1)
    (hfin : ∀ v : T.V j₀, {h : T.G j₀ | h • v = v}.Finite) {g : Γ} {v : T.V j₀}
    (hv : T.ρ j₀ g • v = v) : IsOfFinOrder (χ g) := by
  haveI : Finite (MulAction.stabilizer (T.G j₀) v) := (hfin v).to_subtype
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1
    (isOfFinOrder_of_finite (⟨T.ρ j₀ g, hv⟩ : MulAction.stabilizer (T.G j₀) v))
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩
  rw [← map_pow]
  apply hχ
  rw [map_pow]
  have := congrArg Subtype.val hpow
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at this

/-- **Elliptic elements have `χ g` of finite order.** -/
theorem isOfFinOrder_of_elliptic (hχ : ∀ g, T.ρ j₀ g = 1 → χ g = 1)
    (hfin : ∀ v : T.V j₀, {h : T.G j₀ | h • v = v}.Finite) {g : Γ} (he : T.Elliptic g) :
    IsOfFinOrder (χ g) := by
  obtain ⟨v, hv⟩ := he j₀
  exact isOfFinOrder_of_fixed χ hχ hfin hv

/-- **For torsion-free `M`, elliptic elements lie in `ker χ`.** -/
theorem eq_one_of_elliptic (hM : ∀ m : M, IsOfFinOrder m → m = 1)
    (hχ : ∀ g, T.ρ j₀ g = 1 → χ g = 1) (hfin : ∀ v : T.V j₀, {h : T.G j₀ | h • v = v}.Finite)
    {g : Γ} (he : T.Elliptic g) : χ g = 1 :=
  hM _ (isOfFinOrder_of_elliptic χ hχ hfin he)

/-- **For torsion-free `M`, an element with `χ g ≠ 1` fixes no vertex at `j₀`.** -/
theorem hyperbolicAt_of_ne_one (hM : ∀ m : M, IsOfFinOrder m → m = 1)
    (hχ : ∀ g, T.ρ j₀ g = 1 → χ g = 1) (hfin : ∀ v : T.V j₀, {h : T.G j₀ | h • v = v}.Finite)
    {g : Γ} (hg : χ g ≠ 1) : T.HyperbolicAt j₀ g := fun _ hv ↦
  hg (hM _ (isOfFinOrder_of_fixed χ hχ hfin hv))

variable [IsCofilteredOrEmpty J]

/-- **Elements detected by a torsion-free character are estranged** (at all levels below `j₀`,
wild ones included). -/
theorem estrangedElt_of_ne_one (hM : ∀ m : M, IsOfFinOrder m → m = 1)
    (hχ : ∀ g, T.ρ j₀ g = 1 → χ g = 1) (hfin : ∀ v : T.V j₀, {h : T.G j₀ | h • v = v}.Finite)
    {g : Γ} (hg : χ g ≠ 1) : T.EstrangedElt g :=
  estrangedElt_of_hyperbolicAt (hyperbolicAt_of_ne_one χ hM hχ hfin hg)

/-- **Estrangement only has to be checked on `ker χ`.** -/
theorem estrangedOn_iff_ker (hM : ∀ m : M, IsOfFinOrder m → m = 1)
    (hχ : ∀ g, T.ρ j₀ g = 1 → χ g = 1) (hfin : ∀ v : T.V j₀, {h : T.G j₀ | h • v = v}.Finite)
    (S : Set Γ) : T.EstrangedOn S ↔ T.EstrangedOn (S ∩ (χ.ker : Set Γ)) := by
  refine ⟨fun h ↦ h.mono Set.inter_subset_left, fun h g hg hg1 ↦ ?_⟩
  by_cases hk : χ g = 1
  · exact h g ⟨hg, hk⟩ hg1
  · exact estrangedElt_of_ne_one χ hM hχ hfin hk

end Character

end TreeTower

/-- `ℤ` is torsion-free. -/
lemma isOfFinOrder_multiplicative_int {m : Multiplicative ℤ} (h : IsOfFinOrder m) : m = 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h2 : (n : ℤ) * Multiplicative.toAdd m = 0 := by
    have := congrArg Multiplicative.toAdd hpow
    rwa [toAdd_pow, toAdd_one, nsmul_eq_mul] at this
  rcases mul_eq_zero.1 h2 with h3 | h3
  · omega
  · exact Multiplicative.toAdd.injective h3

namespace DihedralLine

/-! ### Distances on the line -/

lemma natAbs_le_length {x y : ℤ} (p : lineGraph.Walk x y) : (x - y).natAbs ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [lineGraph_adj] at h
    rw [Walk.length_cons]
    omega

/-- On the line, the distance is at least the difference. -/
lemma dist_ge (x y : ℤ) : (x - y).natAbs ≤ lineGraph.dist x y := by
  obtain ⟨p, hp⟩ := (isTree_lineGraph.connected.preconnected x y).exists_walk_length_eq_dist
  rw [← hp]
  exact natAbs_le_length p

/-! ### Pulled back line towers -/

variable {J : Type u} [Category.{v} J] {Γ : Type x} [Group Γ]

/-- **In the line tower pulled back along `χ : Γ →* D_∞`, `g` is estranged iff `χ g ≠ 1`**: a
nontrivial element of `D_∞` fixes at most one vertex, an element of `ker χ` fixes the whole
line. -/
theorem estrangedElt_comap_iff [Nonempty J] (χ : Γ →* DihedralGroup 0) {g : Γ} :
    ((tower J).comap χ).EstrangedElt g ↔ χ g ≠ 1 := by
  constructor
  · intro h h1
    obtain ⟨k, -, hk⟩ := h (Classical.arbitrary J)
    have hk' : ∀ x y : ℤ, χ g • x = x → χ g • y = y → lineGraph.dist x y ≤ 2 := hk
    rw [h1] at hk'
    have := (dist_ge 0 3).trans (hk' 0 3 (one_smul _ _) (one_smul _ _))
    norm_num at this
  · intro h j
    refine ⟨j, 𝟙 j, TreeTower.smallFixAt_of_lineAt (lineAt (J := J) j) ?_⟩
    by_contra hc
    push Not at hc
    exact h (eq_one_of_forall_smul_eq hc)

/-! ### The model of the `Ÿ`-levels -/

/-- The translations: `ℤ →* D_∞`, `d ↦ r d` (translation by `2d` on the line). -/
def tateLineHom : Multiplicative ℤ →* DihedralGroup 0 where
  toFun d := r (ofZ (Multiplicative.toAdd d))
  map_one' := rfl
  map_mul' d e := by
    rw [r_mul_r]
    rfl

lemma tateLineHom_eq_one {d : Multiplicative ℤ} : tateLineHom d = 1 ↔ d = 1 := by
  constructor
  · intro h
    have := r.inj (h.trans one_def)
    exact Multiplicative.toAdd.injective this
  · rintro rfl
    rfl

/-- The deck group `ℤ × ℤ/2` of `Ÿ → X` on the line: translations through the `ℤ`-component,
the involution acting trivially (it fixes the dual graph). -/
def yddotHom : Multiplicative ℤ × Multiplicative (ZMod 2) →* DihedralGroup 0 :=
  tateLineHom.comp (MonoidHom.fst _ _)

/-- **The model tower of the `Ÿ`-levels of the Tate curve.** -/
abbrev yddotTower (J : Type u) [Category.{v} J] :
    TreeTower.{u, v, 0} (Multiplicative ℤ × Multiplicative (ZMod 2)) J :=
  (tower J).comap yddotHom

lemma yddotHom_eq_one {d : Multiplicative ℤ × Multiplicative (ZMod 2)} :
    yddotHom d = 1 ↔ d.1 = 1 :=
  tateLineHom_eq_one

/-- In the `Ÿ`-model, an element is estranged iff its `ℤ`-component is nontrivial. -/
theorem yddot_estrangedElt_iff [Nonempty J] {d : Multiplicative ℤ × Multiplicative (ZMod 2)} :
    (yddotTower J).EstrangedElt d ↔ d.1 ≠ 1 := by
  rw [estrangedElt_comap_iff, Ne, yddotHom_eq_one]

/-- **The involution of `Ÿ → Y` is not estranged in the explicit model**: it is nontrivial and
fixes the whole line at every level. -/
theorem not_estrangedElt_involution [Nonempty J] :
    ¬ (yddotTower J).EstrangedElt (1, Multiplicative.ofAdd (1 : ZMod 2)) := by
  rw [yddot_estrangedElt_iff, not_not]

/-- **The `Ÿ`-model tower is not estranged.** -/
theorem not_estranged_yddot [Nonempty J] : ¬ (yddotTower J).Estranged := fun h ↦
  not_estrangedElt_involution (J := J) (h _ (by decide))

/-- In the `Ÿ`-model, the stabilizer of every (constant) system is `{0} × ℤ/2`. -/
theorem mem_stab_yddot [Nonempty J] (x : ℤ) {d : Multiplicative ℤ × Multiplicative (ZMod 2)} :
    d ∈ TreeTower.stab ((tower J).comapSys yddotHom (vsys x)) ↔ d.1 = 1 := by
  rw [TreeTower.stab_comap, Subgroup.mem_comap, mem_stab_vsys, ← yddotHom_eq_one]
  refine ⟨fun h ↦ h.resolve_right fun h' ↦ ?_, Or.inl⟩
  change tateLineHom d.1 = _ at h'
  cases h'

end DihedralLine

end TemperedFundamentalGroups
