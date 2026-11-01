/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.CurveTower
import TemperedFundamentalGroups.Andre.Functoriality
import TemperedFundamentalGroups.Andre.TateCuspInertia

/-!
# The `Π^tp`-sets of components and cusps (MR18 T7c, tfg side)

For the elliptic prime set `P = components ⊕ cusps` of [EtTh] Prop 3.2(i) (a `Π^tp`-set: the
irreducible components of the special fibres and the cusps of the universal tempered covering),
this file packages what tfg provides.

* **Components, general curve** (`TreeTower` level): for any tree tower `T` over `Γ`, the
  verticial systems `CompSys T` (compatible families of component vertices of the trees of the
  dual graphs) and the edge systems `NodeSys T` (nodes) are `Γ`-sets, with stabilizers the
  verticial / edge-like subgroups (`stabilizer_compSys`, `stabilizer_nodeSys`). The components of
  the covering attached to `H ≤ Γ` are the `H`-orbits `CompOf T H` (combinatorial notion: the
  quotient of the limit tree; no comparison with schematic components of finite coverings is
  claimed). For curves, `piTower` is `andreTower` pulled back along `andreRestrict :
  temperedPi1 →* andreGroup` (Theorem A); `Comp V hV hp hR` is the `temperedPi1`-set of
  components, with compact stabilizers (`isCompact_stabilizer_comp`). Nonemptiness of
  `CompSys` is not proved in tfg and not claimed.
* **Cusps**: `Π^tp` does not act on places of `Ω` (only the decomposition group of the base point
  `V` does), so no geometric global cusp set exists in tfg. For a family of cusp places
  `W i ≥ V` we use the standard group-theoretic model `CuspSet = Σ i, Π^tp ⧸ D_i` with
  `D_i = N(I^tp_{W i})` the normalizer of the cusp inertia `inertiaTempered` (the decomposition
  group of a cusp is the normalizer of its inertia in the geometric situation, [SemiAnbd] /
  [EtTh] §1). The stabilizer of the base cusp `i` is `D_i` and contains `I^tp_{W i}`
  (`inertiaTempered_le_stabilizer_cusp`). **Identifying `CuspSet` with the cusps of the
  universal tempered covering is not proved** (it needs the injectivity of cusp inertia and the
  commensurable terminality of `D_i`); it stays an obligation of MR18 T7c.
* **The Tate case**: `TateComp = Bool × ℤ` (the components `C × {n}` and `E′ × {n}` of
  `TateCovering.Decomp`, `sheetC`, `sheetE`), on which `Π^tp` acts through
  `TateObject.character` by translation of the sheet index; the stabilizer of every component is
  `ker character = Π^tp_Y` (`stabilizer_tateComp`), Galois elements and cusp inertia fix all
  components (`galoisToTempered_smul_tateComp`, `inertiaTempered_le_stabilizer_tateComp`).
  `TatePrime = TateComp ⊕ CuspSet` is the resulting `Π^tp`-set of primes.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

namespace CompCusp

open GaloisLimit

/-! ### Components and nodes of a tree tower -/

section Tower

variable {Γ : Type*} [Group Γ] {J : Type*} [Category J] (T : TreeTower Γ J)

/-- **The components**: systems of vertices of component kind at every level. -/
def CompSys : Type _ := {s : T.Sys // TreeTower.IsVert s}

/-- **The nodes**: systems of vertices of edge kind at every level. -/
def NodeSys : Type _ := {s : T.Sys // ∀ j, T.kind j (s.1 j) = false}

variable {T}

instance : MulAction Γ (CompSys T) where
  smul g s := ⟨g • s.1, s.2.smul g⟩
  one_smul s := Subtype.ext (one_smul Γ s.1)
  mul_smul g h s := Subtype.ext (mul_smul g h s.1)

instance : MulAction Γ (NodeSys T) where
  smul g s := ⟨g • s.1, fun j => by rw [TreeTower.smul_apply, T.kind_smul]; exact s.2 j⟩
  one_smul s := Subtype.ext (one_smul Γ s.1)
  mul_smul g h s := Subtype.ext (mul_smul g h s.1)

lemma CompSys.coe_smul (g : Γ) (s : CompSys T) : (g • s).1 = g • s.1 := rfl

lemma NodeSys.coe_smul (g : Γ) (s : NodeSys T) : (g • s).1 = g • s.1 := rfl

/-- The stabilizer of a component is its **verticial subgroup**. -/
lemma stabilizer_compSys (s : CompSys T) : MulAction.stabilizer Γ s = TreeTower.stab s.1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, TreeTower.stab, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The stabilizer of a node is its **edge-like subgroup**. -/
lemma stabilizer_nodeSys (s : NodeSys T) : MulAction.stabilizer Γ s = TreeTower.stab s.1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, TreeTower.stab, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

variable (T) in
/-- **The components of the covering attached to `H ≤ Γ`**: the `H`-orbits of components. -/
abbrev CompOf (H : Subgroup Γ) : Type _ := MulAction.orbitRel.Quotient H (CompSys T)

/-- The component of the covering for `H` below a component of the universal covering. -/
abbrev compOf (H : Subgroup Γ) (s : CompSys T) : CompOf T H := Quotient.mk _ s

lemma compOf_eq_iff {H : Subgroup Γ} {s s' : CompSys T} :
    compOf H s = compOf H s' ↔ ∃ h ∈ H, h • s' = s := by
  constructor
  · intro e
    obtain ⟨h, hh⟩ := Quotient.exact e
    exact ⟨h, h.2, hh⟩
  · rintro ⟨h, hH, rfl⟩
    exact Quotient.sound ⟨⟨h, hH⟩, rfl⟩

end Tower

/-! ### The components of a curve, as a `temperedPi1`-set -/

section Curve

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A] [Finite A] [SMulCommClass A K R]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

/-- **The tree tower on `Π^tp`**: `andreTower` pulled back along `andreRestrict` (Theorem A). -/
def piTower : TreeTower.{u, u, u} (temperedPi1 O R A V hV)
    (PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) :=
  (andreTower (R := R) (A := A) V hV hp hR).comap (andreRestrict O R A V hV)

/-- **The `Π^tp`-set of components** of the universal tempered covering. -/
abbrev Comp : Type u := CompSys (piTower (R := R) (A := A) V hV hp hR)

/-- **The `Π^tp`-set of nodes** of the universal tempered covering. -/
abbrev Node : Type u := NodeSys (piTower (R := R) (A := A) V hV hp hR)

/-- **Decomposition groups of components are compact.** -/
theorem isCompact_stabilizer_comp (s : Comp (R := R) (A := A) V hV hp hR) :
    IsCompact (SetLike.coe (MulAction.stabilizer (temperedPi1 O R A V hV) s)) := by
  rw [stabilizer_compSys]
  have h := isCompact_stab_andreTower (R := R) (A := A) V hV hp hR s.1
  have e : TreeTower.stab s.1 = (TreeTower.stab ((curveTower (R := R) (A := A) V hV hp hR).comapSys
      (andreGroupHomeoLim (R := R) (A := A) V hV hp hR).toMulEquiv.toMonoidHom s.1)).comap
      (andreRestrict O R A V hV) :=
    (andreTower (R := R) (A := A) V hV hp hR).stab_comap _ s.1
  rw [e]
  have h' := h.image (andreEquiv' (R := R) (A := A) V hV hp hR).symm.continuous
  convert h' using 1
  ext g
  simp only [Subgroup.coe_comap, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hg
    refine ⟨_, hg, ?_⟩
    rw [← andreEquiv'_apply V hV hp hR]
    exact (andreEquiv' (R := R) (A := A) V hV hp hR).symm_apply_apply g
  · rintro ⟨γ, hγ, rfl⟩
    change andreRestrict O R A V hV ((andreEquiv' (R := R) (A := A) V hV hp hR).symm γ) ∈ _
    rw [← andreEquiv'_apply V hV hp hR, ContinuousMulEquiv.apply_symm_apply]
    exact hγ

end Curve

/-! ### Cusps -/

section Cusp

open CuspInertia

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  {V : ValuationSubring Ω} (hV : V.comap (algebraMap K Ω) = O)
  {ι : Type u} (W : ι → ValuationSubring Ω) (hVW : ∀ i, V ≤ W i)

variable (O R A) in
/-- The decomposition group of the cusp `W i` in `Π^tp`: the normalizer of its inertia. -/
def cuspDecomp (i : ι) : Subgroup (temperedPi1 O R A V hV) :=
  Subgroup.normalizer
    ((inertiaTempered (R := R) O A hV (hVW i) : Subgroup (temperedPi1 O R A V hV)) :
      Set (temperedPi1 O R A V hV))

variable (O R A) in
/-- **The `Π^tp`-set of cusps** over the cusp places `W i`: `Σ i, Π^tp ⧸ D_i`. -/
def CuspSet : Type u := Σ i : ι, temperedPi1 O R A V hV ⧸ cuspDecomp O R A hV W hVW i

instance : MulAction (temperedPi1 O R A V hV) (CuspSet O R A hV W hVW) where
  smul g x := ⟨x.1, g • x.2⟩
  one_smul x := Sigma.ext rfl (heq_of_eq (one_smul _ x.2))
  mul_smul g h x := Sigma.ext rfl (heq_of_eq (mul_smul g h x.2))

variable (O R A) in
/-- The base cusp over `W i`. -/
def baseCusp (i : ι) : CuspSet O R A hV W hVW :=
  ⟨i, ((1 : temperedPi1 O R A V hV) : temperedPi1 O R A V hV ⧸ cuspDecomp O R A hV W hVW i)⟩

lemma smul_cusp_mk (g : temperedPi1 O R A V hV) (i : ι)
    (x : temperedPi1 O R A V hV ⧸ cuspDecomp O R A hV W hVW i) :
    g • (⟨i, x⟩ : CuspSet O R A hV W hVW) = ⟨i, g • x⟩ := rfl

/-- **The stabilizer of the base cusp `i` is `D_i`.** -/
theorem stabilizer_baseCusp (i : ι) :
    MulAction.stabilizer (temperedPi1 O R A V hV) (baseCusp O R A hV W hVW i) =
      cuspDecomp O R A hV W hVW i := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← MulAction.stabilizer_quotient (cuspDecomp O R A hV W hVW i),
    MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · intro h
    exact Sigma.ext rfl (heq_of_eq h)

/-- **Cusp inertia fixes its cusp.** -/
theorem inertiaTempered_le_stabilizer_cusp (i : ι) :
    inertiaTempered (R := R) O A hV (hVW i) ≤
      MulAction.stabilizer (temperedPi1 O R A V hV) (baseCusp O R A hV W hVW i) := by
  rw [stabilizer_baseCusp]
  exact Subgroup.le_normalizer

end Cusp

/-! ### The Tate case -/

section Tate

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) (D : TateObject.Data O R)

/-- The components of the Tate `ℤ`-covering `Y`: `C × {n}` (`true`) and `E′ × {n}` (`false`). -/
def TateComp (_D : TateObject.Data O R) (_V : ValuationSubring Ω) : Type := Bool × ℤ

/-- `Π^tp` acts on the components through `TateObject.character` (translation of the sheets). -/
instance : MulAction (temperedPi1 O R A V hV) (TateComp D V) where
  smul g x := (x.1, x.2 + Multiplicative.toAdd (TateObject.character (A := A) D V hV g))
  one_smul x := by
    change (x.1, x.2 + Multiplicative.toAdd (TateObject.character (A := A) D V hV 1)) = x
    rw [map_one, toAdd_one, add_zero]
    rfl
  mul_smul g h x := by
    change (x.1, x.2 + Multiplicative.toAdd (TateObject.character (A := A) D V hV (g * h))) =
      (x.1, x.2 + Multiplicative.toAdd (TateObject.character (A := A) D V hV h) +
        Multiplicative.toAdd (TateObject.character (A := A) D V hV g))
    rw [map_mul, toAdd_mul, add_assoc, add_comm (Multiplicative.toAdd _)]

lemma tateComp_smul_def (g : temperedPi1 O R A V hV) (x : TateComp D V) :
    g • x = ((x.1, x.2 + Multiplicative.toAdd (TateObject.character (A := A) D V hV g)) :
      Bool × ℤ) := rfl

/-- **The stabilizer of every component is `Π^tp_Y = ker χ`.** -/
theorem stabilizer_tateComp (x : TateComp D V) :
    MulAction.stabilizer (temperedPi1 O R A V hV) x =
      (TateObject.character (A := A) D V hV).ker := by
  ext g
  rw [MulAction.mem_stabilizer_iff, tateComp_smul_def, MonoidHom.mem_ker]
  constructor
  · intro h
    have h2 := congrArg Prod.snd h
    simp only [add_eq_left] at h2
    exact h2
  · intro h
    change (x.1, x.2 + Multiplicative.toAdd (TateObject.character (A := A) D V hV g)) = x
    rw [h, toAdd_one, add_zero]
    rfl

/-- **Galois elements fix every component.** -/
theorem galoisToTempered_smul_tateComp (σ : decompositionGroup R V) (x : TateComp D V) :
    galoisToTempered O R A hV σ • x = x := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_tateComp, MonoidHom.mem_ker]
  exact character_galoisToTempered hV D σ

/-- **Cusp inertia fixes every component.** -/
theorem inertiaTempered_le_stabilizer_tateComp {W : ValuationSubring Ω} (hVW : V ≤ W)
    (x : TateComp D V) :
    inertiaTempered O A hV hVW ≤ MulAction.stabilizer (temperedPi1 O R A V hV) x := by
  rw [stabilizer_tateComp]
  exact inertiaTempered_le_ker_character hV D hVW

/-- **The `Π^tp`-set of primes of the Tate covering**: components `⊕` cusps. -/
abbrev TatePrime {ι : Type u} (W : ι → ValuationSubring Ω) (hVW : ∀ i, V ≤ W i) : Type u :=
  TateComp D V ⊕ CuspSet O R A hV W hVW

example {ι : Type u} (W : ι → ValuationSubring Ω) (hVW : ∀ i, V ≤ W i) :
    MulAction (temperedPi1 O R A V hV) (TatePrime (A := A) V hV D W hVW) := inferInstance

end Tate

end CompCusp

end

end TemperedFundamentalGroups
