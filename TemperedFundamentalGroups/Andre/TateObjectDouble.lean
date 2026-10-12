/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateObject
import TemperedFundamentalGroups.Andre.QuadraticLevel
import TemperedFundamentalGroups.Tempered.Galois

/-!
# The double covering `Ÿ → Y` of the `ℤ`-covering of the Tate curve ([EtTh], §1)

In [EtTh] §1 the tempered covering `Ÿ → Y → X` of the Tate curve `X = E_q ∖ {0}` is the
`ℤ`-covering `Y` followed by the double covering `Ü ↦ Ü² = U`; equivalently
`Ÿ = Y ×_X X'` for the double covering `X' → X` given by the `2`-isogeny
`E_{√q} → E_q` (`u ↦ u²` on `K^×/√q^ℤ → K^×/q^ℤ`). In terms of functions, `X'` is the Kummer
covering `√(x − e)` of `X`, where `e` is the `x`-coordinate of the `2`-torsion point `√q` (the
generator of the kernel of the dual isogeny).

This file constructs `Ÿ` as an object of the tempered category, **under the hypothesis that `2`
and `x − e` are units of `R`** (`DoubleData`). This holds if `Spec R` avoids the `2`-torsion point
`(e, ·)`, e.g. for `E ∖ E[2]`, but not for `X = E ∖ {0}` itself, where the Kummer presentation is
not étale at `(e, ·)` (the isogeny is, but its coordinate ring is not `R[t]/(t² − (x − e))`
there).

* `quadLevel`: the level `R[t]/(t² − c)` with **trivial** group `H` (so that its involution
  `t ↦ −t` is a deck transformation of the covering rather than part of the level).
* `level₂`, `Yddot`: the level with the same Tate model as `Y` (`j` through `Spec R`), and the
  object `Ÿ` with the same `ℤ`-covering of the special fibre as `Y = X₀`.
* `deck₂ : ℤ × ℤ/2 →* Aut Ÿ` (`deckHom₂`: `ℤ` acting on the covering space, `ℤ/2` by the
  involution) **acts simply transitively on the fibre** (`isDeckTorsor₂`), whence the continuous
  character `character₂ : Π^tp_X → ℤ × ℤ/2`.
* `proj : Ÿ ⟶ X₀` and **`character_eq_fst`**: `χ_Y = pr₁ ∘ χ_Ÿ`.
* `piYddot := ker character₂` (`Π^tp_Ÿ`, the stabilizer of the base point, `mem_piYddot_iff`):
  open (`isOpen_piYddot`), normal in `Π^tp_X`, contained in `Π^tp_Y = ker character`
  (`piYddot_le_ker_character`), with `Π^tp_Y/Π^tp_Ÿ ↪ ℤ/2` (`mem_piYddot_iff_of_mem`):
  **index `≤ 2`** (`relIndex_le_two`), and index `2` as soon as some element of `Π^tp_Y` acts on
  the fibre of `X'` by the involution (`relIndex_eq_two`).
* **`relIndex_eq_two_of_galois`**: the elements of the decomposition group of `V` lie in
  `Π^tp_Y` (`character_galois`, through `galoisToTempered`) and act on `Ÿ` by `(0, 1)` if they
  move `√c` (`character₂_galois`); so `[Π^tp_Y : Π^tp_Ÿ] = 2` whenever `X'` is not split at
  `V`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

namespace TateObject

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A]

/-! ### The quadratic level with trivial group -/

/-- **The level `R[t]/(t² − c)` with trivial group `H`.** -/
abbrev quadLevel {c : R} (h2 : IsUnit (2 : R)) (hc : IsUnit c) : FiniteLevel R A where
  n := 1
  I := QuadraticLevel.I c
  etale := QuadraticLevel.etale h2 hc
  finite := QuadraticLevel.finite c
  H := ⊥
  surjective _ := ⟨1, Subgroup.one_mem _, Subsingleton.elim _ _⟩

lemma quadLevel_H_eq_one {c : R} {h2 : IsUnit (2 : R)} {hc : IsUnit c}
    (g : (quadLevel (A := A) h2 hc).H) : g = 1 :=
  Subtype.ext (Subgroup.mem_bot.1 g.2)

/-! ### The data -/

variable (O R) in
/-- **The data of `Ÿ`**: Tate data with an element `e` (the `x`-coordinate of the `2`-torsion
point `√q`) such that `2` and `x − e` are units of `R`. -/
structure DoubleData extends Data O R where
  /-- The `x`-coordinate of the `2`-torsion point. -/
  e : R
  two_unit : IsUnit (2 : R)
  c_unit : IsUnit (x - e)

variable (D : DoubleData O R)

/-- The Kummer parameter `c = x − e`. -/
abbrev DoubleData.c : R := D.x - D.e

/-- The level of `X'`. -/
abbrev level' : FiniteLevel R A := quadLevel (A := A) D.two_unit D.c_unit

/-- `R ≅ B(unitLevel) → B(X')`. -/
def unitToQuad : (unitLevel R A).B →ₐ[R] (level' (A := A) D).B :=
  (Algebra.ofId R _).comp (unitEquiv R).toAlgHom

/-- The involution `t ↦ −t` of `B(X')`. -/
abbrev σ' : (level' (A := A) D).B ≃ₐ[R] (level' (A := A) D).B := QuadraticLevel.σ D.c

lemma level'_H_eq_one (g : (level' (A := A) D).H) : g = 1 :=
  Subtype.ext (Subgroup.mem_bot.1 g.2)

lemma σ'_comp_unitToQuad (ε : (level' (A := A) D).B →ₐ[R] (level' (A := A) D).B) :
    ε.comp (unitToQuad (A := A) D) = unitToQuad D :=
  (subsingleton_fibre (A := A)).elim _ _

/-! ### The deck transformations `ℤ × ℤ/2` -/

/-- `σ^ε` for `ε ∈ ℤ/2`. -/
def σPow (ε : Multiplicative (ZMod 2)) :
    (level' (A := A) D).B →ₐ[R] (level' (A := A) D).B :=
  if Multiplicative.toAdd ε = 0 then AlgHom.id R _ else (σ' (A := A) D).toAlgHom

lemma σPow_mul (ε δ : Multiplicative (ZMod 2)) :
    (σPow (A := A) D δ).comp (σPow D ε) = σPow D (ε * δ) := by
  apply AlgHom.ext
  intro b
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  simp only [σPow, toAdd_mul, AlgHom.comp_apply]
  rcases h01 (Multiplicative.toAdd ε) with h | h <;>
    rcases h01 (Multiplicative.toAdd δ) with h' | h'
  · simp [h, h']
  · simp [h, h']
  · simp [h, h']
  · simp only [h, h', h11, one_ne_zero, if_false, if_true]
    exact QuadraticLevel.σ_σ D.c b

lemma σPow_one : σPow (A := A) D 1 = AlgHom.id R _ := by
  simp [σPow]

variable [IsReduced R]

/-- **The level of `Ÿ`**: `X'` with the Tate model of `Y`, `j` factoring through `Spec R`. -/
abbrev level₂ : Level O R A where
  L := level' (A := A) D
  c := TateModel.model D.π D.b₄ D.b₆
  j := Spec.map (CommRingCat.ofHom (unitToQuad (A := A) D).toRingHom) ≫
    (level (A := A) D.toData).j
  j_toSpec := by
    have h := (level (A := A) D.toData).j_toSpec
    change _ ≫ (level (A := A) D.toData).j ≫ (level (A := A) D.toData).c.toSpec = _
    rw [h]
    change Spec.map (CommRingCat.ofHom (unitToQuad (A := A) D).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (levelStructureMap O R A (unitLevel R A))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    change (unitToQuad (A := A) D) (algebraMap R _ (algebraMap K R a)) = _
    exact AlgHom.commutes _ _
  ρ := 1
  ρ_toSpec _ := Category.id_comp _
  ρ_j g := by
    rw [level'_H_eq_one D g, map_one]
    change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    convert Category.id_comp _
    rw [← Spec.map_id]
    rfl

lemma level₂_ρs (g : (level₂ (A := A) D).L.H) : (level₂ (A := A) D).ρs g = 1 := by
  have h1 : g = 1 := level'_H_eq_one D g
  rw [h1, map_one]

/-- **The object `Ÿ`**: the `ℤ`-covering of the special fibre of the Tate model, over `X'`. -/
abbrev Yddot : TempObj O R A where
  Lv := level₂ D
  P := (decomp (A := A) D.toData).toCode _ (level₂_ρs D)

/-- The `j`-compatibility of `σ^ε`: `Spec σ^ε ≫ j = j`. -/
lemma spec_σPow_j (ε : Multiplicative (ZMod 2)) :
    Spec.map (CommRingCat.ofHom (σPow (A := A) D ε).toRingHom) ≫ (level₂ (A := A) D).j =
      (level₂ (A := A) D).j := by
  change _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  exact congrArg AlgHom.toRingHom (σ'_comp_unitToQuad (A := A) D (σPow D ε))

/-- The level endomorphism `σ^ε` of `X'`. -/
def levelHom (ε : Multiplicative (ZMod 2)) : (level' (A := A) D) ⟶ (level' (A := A) D) where
  f := σPow D ε
  r := MonoidHom.id _
  r_a _ := rfl
  f_σ g y := by
    rw [level'_H_eq_one D g]
    rfl

/-- **The deck transformation `(d, ε)` of `Ÿ`.** -/
def deckHom₂ (d : Multiplicative ℤ × Multiplicative (ZMod 2)) :
    Yddot (A := A) D ⟶ Yddot (A := A) D where
  φ := levelHom D d.2
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := by
    rw [Category.comp_id]
    exact (spec_σPow_j D d.2).symm
  h := (decomp (A := A) D.toData).deckCode _ (level₂_ρs D) d.1
  continuous_h := ((decomp (A := A) D.toData).deckCode _ (level₂_ρs D) d.1).continuous
  fst_h _ := rfl
  h_act g x := by
    have h1 : g = 1 := level'_H_eq_one D g
    rw [h1, map_one, map_one]
    rfl

lemma deckHom₂_mul (d e : Multiplicative ℤ × Multiplicative (ZMod 2)) :
    deckHom₂ (A := A) D e ≫ deckHom₂ D d = deckHom₂ D (d * e) := by
  refine TempObj.Hom.ext ?_ (Category.id_comp _) ?_
  · refine FiniteLevel.Hom.ext ?_ rfl
    change (σPow D e.2).comp (σPow D d.2) = σPow D (d * e).2
    rw [σPow_mul, Prod.snd_mul, mul_comm]
  · rw [TempObj.comp_h]
    change ((decomp (A := A) D.toData).deckCode _ (level₂_ρs D) d.1) ∘
        ((decomp (A := A) D.toData).deckCode _ (level₂_ρs D) e.1) =
      (decomp (A := A) D.toData).deckCode _ (level₂_ρs D) (d * e).1
    rw [Prod.fst_mul, map_mul]
    rfl

lemma deckHom₂_one : deckHom₂ (A := A) D 1 = 𝟙 _ := by
  refine TempObj.Hom.ext ?_ rfl ?_
  · refine FiniteLevel.Hom.ext ?_ rfl
    exact σPow_one D
  · change ((decomp (A := A) D.toData).deckCode _ (level₂_ρs D) 1 : _ → _) = id
    rw [map_one]
    rfl

/-- **The deck action** `ℤ × ℤ/2 →* Aut Ÿ`. -/
def deck₂ : Multiplicative ℤ × Multiplicative (ZMod 2) →* Aut (Yddot (A := A) D) where
  toFun d :=
    { hom := deckHom₂ D d
      inv := deckHom₂ D d⁻¹
      hom_inv_id := by rw [deckHom₂_mul, inv_mul_cancel, deckHom₂_one]
      inv_hom_id := by rw [deckHom₂_mul, mul_inv_cancel, deckHom₂_one] }
  map_one' := by
    ext1
    exact deckHom₂_one D
  map_mul' d e := by
    ext1
    rw [Aut.Aut_mul_def, Iso.trans_hom]
    exact (deckHom₂_mul D d e).symm

/-! ### The fibre of `Ÿ` -/

section Fibre

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma point_comp_σPow (ε : Multiplicative (ZMod 2)) (t : (level' (A := A) D).B →ₐ[R] Ω) :
    (level₂ (A := A) D).point (t.comp (σPow D ε)) = (level₂ (A := A) D).point t := by
  unfold Level.point
  have e : CommRingCat.ofHom (t.comp (σPow (A := A) D ε)).toRingHom =
      CommRingCat.ofHom (σPow (A := A) D ε).toRingHom ≫ CommRingCat.ofHom t.toRingHom := rfl
  change Spec.map (CommRingCat.ofHom (t.comp (σPow (A := A) D ε)).toRingHom) ≫
    (level₂ (A := A) D).j = Spec.map (CommRingCat.ofHom t.toRingHom) ≫ (level₂ (A := A) D).j
  rw [e, Spec.map_comp, Category.assoc, spec_σPow_j]

lemma sp_comp_σPow (ε : Multiplicative (ZMod 2)) (t : (level' (A := A) D).B →ₐ[R] Ω) :
    (level₂ (A := A) D).sp V hV (t.comp (σPow D ε)) = (level₂ (A := A) D).sp V hV t := by
  unfold Level.sp
  have key : ∀ {x y : Spec (CommRingCat.of Ω) ⟶ (level₂ (A := A) D).c.scheme} (_ : x = y)
      (hx : x ≫ (level₂ (A := A) D).c.toSpec = Spec.map (CommRingCat.ofHom (valToField O)))
      (hy : y ≫ (level₂ (A := A) D).c.toSpec = Spec.map (CommRingCat.ofHom (valToField O))),
      TemperedFundamentalGroups.sp (level₂ (A := A) D).c.toSpec V hV x hx =
        TemperedFundamentalGroups.sp (level₂ (A := A) D).c.toSpec V hV y hy := by
    intro x y h hx hy
    subst h
    rfl
  exact key (point_comp_σPow (A := A) D ε t) _ _

omit [IsReduced R] [Algebra K Ω] [IsScalarTower K R Ω] in
include D in
/-- `2` and `c` are nonzero in `Ω`. -/
lemma two_ne_zero_Ω : (2 : Ω) ≠ 0 := by
  have := D.two_unit.map (algebraMap R Ω)
  rw [map_ofNat] at this
  exact this.ne_zero

omit [IsReduced R] [Algebra K Ω] [IsScalarTower K R Ω] in
lemma c_ne_zero_Ω : algebraMap R Ω D.c ≠ 0 := (D.c_unit.map (algebraMap R Ω)).ne_zero

omit [IsReduced R] [Algebra K Ω] [IsScalarTower K R Ω] in
/-- A geometric point is not fixed by the involution. -/
lemma comp_σ_ne (t : QuadraticLevel.B D.c →ₐ[R] Ω) :
    t.comp (QuadraticLevel.σ D.c).toAlgHom ≠ t := by
  intro h
  have hx : t (QuadraticLevel.σ D.c (QuadraticLevel.x D.c)) = t (QuadraticLevel.x D.c) :=
    congrArg (fun φ : QuadraticLevel.B D.c →ₐ[R] Ω => φ (QuadraticLevel.x D.c)) h
  rw [QuadraticLevel.σ_x, map_neg] at hx
  have h0 : t (QuadraticLevel.x D.c) = 0 := by
    have : (2 : Ω) * t (QuadraticLevel.x D.c) = 0 := by linear_combination -hx
    exact (mul_eq_zero.1 this).resolve_left (two_ne_zero_Ω D)
  apply c_ne_zero_Ω (Ω := Ω) D
  rw [← AlgHom.commutes t D.c, ← QuadraticLevel.x_sq, map_pow, h0, zero_pow two_ne_zero]

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

omit [IsReduced R] in
lemma σPow_ofAdd_zero : σPow (A := A) D (Multiplicative.ofAdd 0) = AlgHom.id R _ := by
  simp [σPow]

omit [IsReduced R] in
lemma σPow_ofAdd_one : σPow (A := A) D (Multiplicative.ofAdd 1) = (σ' (A := A) D).toAlgHom := by
  simp [σPow]

omit [IsReduced R] [Algebra K Ω] [IsScalarTower K R Ω] in
/-- `ε ↦ t ∘ σ^ε` is injective. -/
lemma comp_σPow_injective (t : (level' (A := A) D).B →ₐ[R] Ω) {ε δ : Multiplicative (ZMod 2)}
    (h : t.comp (σPow D ε) = t.comp (σPow D δ)) : ε = δ := by
  rcases zmod2_cases (Multiplicative.toAdd ε) with he | he <;>
    rcases zmod2_cases (Multiplicative.toAdd δ) with hd | hd
  · exact Multiplicative.toAdd.injective (he.trans hd.symm)
  · exfalso
    rw [show ε = Multiplicative.ofAdd 0 from he, show δ = Multiplicative.ofAdd 1 from hd,
      σPow_ofAdd_zero, σPow_ofAdd_one] at h
    exact comp_σ_ne D t (by rw [← h]; rfl)
  · exfalso
    rw [show ε = Multiplicative.ofAdd 1 from he, show δ = Multiplicative.ofAdd 0 from hd,
      σPow_ofAdd_zero, σPow_ofAdd_one] at h
    exact comp_σ_ne D t h
  · exact Multiplicative.toAdd.injective (he.trans hd.symm)

omit [IsReduced R] [Algebra K Ω] [IsScalarTower K R Ω] in
/-- Every geometric point is `t ∘ σ^ε`. -/
lemma exists_eq_comp_σPow (t t' : (level' (A := A) D).B →ₐ[R] Ω) :
    ∃ ε, t' = t.comp (σPow (A := A) D ε) := by
  rcases QuadraticLevel.eq_or_eq_comp_σ D.c t t' with h | h
  · exact ⟨Multiplicative.ofAdd 0, by rw [σPow_ofAdd_zero, h]; rfl⟩
  · exact ⟨Multiplicative.ofAdd 1, by rw [σPow_ofAdd_one, h]⟩

/-- The action of the deck transformations on the fibre. -/
lemma deckAct_mk (e : Multiplicative ℤ × Multiplicative (ZMod 2))
    (q : TempObj.PreFibre Ω V hV (Yddot (A := A) D)) :
    FibreAut.deckAct (F := tempFibre O R A V hV) (Yddot (A := A) D) (deck₂ D) e
      (⟦q⟧ : (tempFibre O R A V hV).obj (Yddot (A := A) D)) =
      (⟦TempObj.preMap V hV (deckHom₂ D e) q⟧ :
        (tempFibre O R A V hV).obj (Yddot (A := A) D)) := rfl

/-- `H⁰` of `Ÿ` is trivial, so the fibre is the set of pairs `(t, p)`. -/
lemma mk_eq_mk_iff {q q' : TempObj.PreFibre Ω V hV (Yddot (A := A) D)} :
    (⟦q⟧ : (tempFibre O R A V hV).obj (Yddot (A := A) D)) = ⟦q'⟧ ↔ q = q' := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hg1 : g = 1 := Subtype.ext (level'_H_eq_one D g.1)
    subst hg1
    have : q' = q := by simpa using hg
    exact this.symm
  · rintro rfl
    rfl

/-- **The deck group `ℤ × ℤ/2` acts simply transitively on the fibre of `Ÿ`.** -/
theorem isDeckTorsor₂ :
    FibreAut.IsDeckTorsor (F := tempFibre O R A V hV) (Yddot (A := A) D) (deck₂ D) := by
  intro x y
  induction x using Quotient.inductionOn with | h q => ?_
  induction y using Quotient.inductionOn with | h q' => ?_
  obtain ⟨ε, hε⟩ := exists_eq_comp_σPow (A := A) D q.1.1 q'.1.1
  have hsp : q.1.2.1.1 = q'.1.2.1.1 := Subtype.ext (q.2.trans (by
    rw [q'.2, hε]
    exact congrArg Subtype.val (sp_comp_σPow (A := A) D V hV ε q.1.1).symm))
  obtain ⟨d, hd, hu⟩ := (decomp (A := A) D.toData).existsUnique_deckCode _ (level₂_ρs D) hsp
  refine ⟨(d, ε), ?_, fun e he => ?_⟩
  · change FibreAut.deckAct (F := tempFibre O R A V hV) (Yddot (A := A) D) (deck₂ D) (d, ε)
      ⟦q⟧ = ⟦q'⟧
    rw [deckAct_mk]
    exact (mk_eq_mk_iff D V hV).2 (Subtype.ext (Prod.ext hε.symm hd))
  · change FibreAut.deckAct (F := tempFibre O R A V hV) (Yddot (A := A) D) (deck₂ D) e
      ⟦q⟧ = ⟦q'⟧ at he
    rw [deckAct_mk] at he
    replace he := (mk_eq_mk_iff D V hV).1 he
    have h1 := congrArg (fun r : TempObj.PreFibre Ω V hV (Yddot (A := A) D) => r.1.1) he
    have h2 := congrArg (fun r : TempObj.PreFibre Ω V hV (Yddot (A := A) D) => r.1.2) he
    refine Prod.ext (hu e.1 h2) ?_
    exact comp_σPow_injective (A := A) D q.1.1 (h1.trans hε)

variable {V hV}

/-- A geometric point of `X'` (a square root `s` of `c` in `Ω`). -/
def t₀ (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) : (level' (A := A) D).B →ₐ[R] Ω :=
  QuadraticLevel.lift D.c s (by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hs, sub_self])

variable (V hV)

/-- **The base point of the fibre of `Ÿ`.** -/
def basePoint₂ (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) :
    (tempFibre O R A V hV).obj (Yddot (A := A) D) :=
  ⟦⟨(t₀ D s hs, ⟨((level₂ (A := A) D).sp V hV (t₀ D s hs), 0), Set.mem_univ _⟩), rfl⟩⟧

/-- **The character `Π^tp_X → ℤ × ℤ/2`** of the deck torsor `Ÿ`. -/
def character₂ (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) :
    temperedPi1 O R A V hV →* Multiplicative ℤ × Multiplicative (ZMod 2) :=
  FibreAut.deckCharacter (Yddot (A := A) D) (deck₂ D) (basePoint₂ (A := A) D V hV s hs)
    (isDeckTorsor₂ D V hV)

/-- **`Π^tp_Ÿ`**: the kernel of `character₂`. -/
def piYddot (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) : Subgroup (temperedPi1 O R A V hV) :=
  (character₂ (A := A) D V hV s hs).ker

instance (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) : (piYddot (A := A) D V hV s hs).Normal :=
  MonoidHom.normal_ker _

/-- **`Π^tp_Ÿ` is the stabilizer of the base point of the fibre of `Ÿ`.** -/
lemma mem_piYddot_iff (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)
    (α : temperedPi1 O R A V hV) :
    α ∈ piYddot (A := A) D V hV s hs ↔ α.app (Yddot (A := A) D) (basePoint₂ (A := A) D V hV s hs) =
      basePoint₂ (A := A) D V hV s hs := by
  rw [piYddot, MonoidHom.mem_ker]
  have h := FibreAut.deckAct_deckCharacter (F := tempFibre O R A V hV) (Yddot (A := A) D)
    (deck₂ D) (basePoint₂ (A := A) D V hV s hs) (isDeckTorsor₂ D V hV) α
  change FibreAut.deckAct _ _ (character₂ (A := A) D V hV s hs α) _ = _ at h
  constructor
  · intro h1
    rw [← h, h1, FibreAut.deckAct_one]
  · intro h1
    exact ((isDeckTorsor₂ (A := A) D V hV) (basePoint₂ (A := A) D V hV s hs)
      (basePoint₂ (A := A) D V hV s hs)).unique (h.trans h1) (FibreAut.deckAct_one _ _ _)

/-- **`Π^tp_Ÿ` is open.** -/
lemma isOpen_piYddot (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) :
    IsOpen (piYddot (A := A) D V hV s hs : Set (temperedPi1 O R A V hV)) := by
  have := FibreAut.isOpen_stabilizer_singleton (tempFibre O R A V hV) (Yddot (A := A) D)
    (basePoint₂ (A := A) D V hV s hs)
  convert this using 1
  ext α
  exact mem_piYddot_iff D V hV s hs α

end Fibre

/-! ### The projection `Ÿ → Y` and `Π^tp_Ÿ ⊆ Π^tp_Y` -/

section Proj

/-- The level morphism `X' → (R, 1)`. -/
def levelProj : (level' (A := A) D) ⟶ (unitLevel R A) where
  f := unitToQuad D
  r := 1
  r_a g := by
    rw [level'_H_eq_one D g]
    rfl
  f_σ g y := by
    rw [level'_H_eq_one D g]
    rfl

/-- **The projection `Ÿ → Y = X₀`.** -/
def proj : Yddot (A := A) D ⟶ X₀ (A := A) D.toData where
  φ := levelProj D
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := Category.comp_id _
  h := id
  continuous_h := continuous_id
  fst_h _ := rfl
  h_act g x := by
    rw [level'_H_eq_one D g]
    rfl

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- The projection maps the base point to the base point. -/
lemma proj_basePoint (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) :
    (tempFibre O R A V hV).map (proj D) (basePoint₂ (A := A) D V hV s hs) =
      basePoint D.toData V hV := by
  have ht : (t₀ (A := A) D s hs).comp (unitToQuad D) =
      (Algebra.ofId R Ω).comp (unitEquiv R).toAlgHom := (subsingleton_fibre (A := A)).elim _ _
  have hsp : ((level₂ (A := A) D).sp V hV (t₀ (A := A) D s hs) : (level₂ (A := A) D).c.scheme) =
      ((level (A := A) D.toData).sp V hV ((Algebra.ofId R Ω).comp (unitEquiv R).toAlgHom) :
        (level (A := A) D.toData).c.scheme) := by
    have h := TempObj.ψ_sp V hV (proj (A := A) D) (t₀ (A := A) D s hs)
    have e : (t₀ (A := A) D s hs).comp (proj (A := A) D).φ.f =
        (Algebra.ofId R Ω).comp (unitEquiv R).toAlgHom := ht
    rw [e] at h
    exact h
  exact congrArg (Quotient.mk _) (Subtype.ext (Prod.ext ht
    (Subtype.ext (Prod.ext (Subtype.ext hsp) rfl))))

/-- The projection intertwines the deck transformations. -/
lemma proj_deckAct (e : Multiplicative ℤ × Multiplicative (ZMod 2))
    (x : (tempFibre O R A V hV).obj (Yddot (A := A) D)) :
    (tempFibre O R A V hV).map (proj D)
        (FibreAut.deckAct (F := tempFibre O R A V hV) (Yddot (A := A) D) (deck₂ D) e x) =
      FibreAut.deckAct (F := tempFibre O R A V hV) (X₀ (A := A) D.toData) (deck D.toData) e.1
        ((tempFibre O R A V hV).map (proj D) x) := by
  induction x using Quotient.inductionOn with | h q => ?_
  change (⟦TempObj.preMap V hV (proj (A := A) D) (TempObj.preMap V hV (deckHom₂ D e) q)⟧ :
    (tempFibre O R A V hV).obj (X₀ (A := A) D.toData)) =
      ⟦TempObj.preMap V hV (deckHom D.toData e.1) (TempObj.preMap V hV (proj (A := A) D) q)⟧
  congr 1
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  exact (subsingleton_fibre (A := A)).elim _ _

/-- **`χ_Y = pr₁ ∘ χ_Ÿ`.** -/
theorem character_eq_fst (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)
    (α : temperedPi1 O R A V hV) :
    character (A := A) D.toData V hV α = (character₂ (A := A) D V hV s hs α).1 := by
  refine FibreAut.deckCharacterFun_eq (X₀ (A := A) D.toData) (deck D.toData)
    (basePoint D.toData V hV) (isDeckTorsor D.toData V hV) ?_
  have h₂ := FibreAut.deckAct_deckCharacter (F := tempFibre O R A V hV) (Yddot (A := A) D)
    (deck₂ D) (basePoint₂ (A := A) D V hV s hs) (isDeckTorsor₂ D V hV) α
  rw [← proj_basePoint D V hV s hs, ← proj_deckAct]
  have h₃ : FibreAut.deckAct (F := tempFibre O R A V hV) (Yddot (A := A) D) (deck₂ D)
      (character₂ (A := A) D V hV s hs α) (basePoint₂ (A := A) D V hV s hs) =
      α.app (Yddot (A := A) D) (basePoint₂ (A := A) D V hV s hs) := h₂
  rw [h₃]
  exact (FibreAut.app_naturality α (proj D) _).symm

/-- **`Π^tp_Ÿ ⊆ Π^tp_Y`.** -/
theorem piYddot_le_ker_character (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) :
    piYddot (A := A) D V hV s hs ≤ (character (A := A) D.toData V hV).ker := by
  intro α hα
  rw [MonoidHom.mem_ker, character_eq_fst D V hV s hs, (MonoidHom.mem_ker.1 hα)]
  rfl

/-- **On `Π^tp_Y`, membership in `Π^tp_Ŷ` is the triviality of the `ℤ/2`-component.** -/
theorem mem_piYddot_iff_of_mem (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)
    {α : temperedPi1 O R A V hV} (hα : α ∈ (character (A := A) D.toData V hV).ker) :
    α ∈ piYddot (A := A) D V hV s hs ↔ (character₂ (A := A) D V hV s hs α).2 = 1 := by
  rw [piYddot, MonoidHom.mem_ker]
  have h1 : (character₂ (A := A) D V hV s hs α).1 = 1 := by
    rw [← character_eq_fst D V hV s hs]
    exact hα
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Prod.ext h1 h

/-- The `ℤ/2`-component on `Π^tp_Y`. -/
def sndOnPiY (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) :
    (character (A := A) D.toData V hV).ker →* Multiplicative (ZMod 2) :=
  (MonoidHom.snd _ _).comp ((character₂ (A := A) D V hV s hs).comp (Subgroup.subtype _))

lemma ker_sndOnPiY (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) :
    (sndOnPiY (A := A) D V hV s hs).ker =
      (piYddot (A := A) D V hV s hs).subgroupOf (character (A := A) D.toData V hV).ker := by
  ext ⟨α, hα⟩
  rw [Subgroup.mem_subgroupOf, mem_piYddot_iff_of_mem D V hV s hs hα, MonoidHom.mem_ker]
  rfl

/-- **`[Π^tp_Y : Π^tp_Ÿ] ≤ 2`.** -/
theorem relIndex_le_two (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) :
    (piYddot (A := A) D V hV s hs).relIndex (character (A := A) D.toData V hV).ker ≤ 2 := by
  rw [Subgroup.relIndex, ← ker_sndOnPiY, Subgroup.index_ker]
  calc Nat.card (Set.range (sndOnPiY (A := A) D V hV s hs))
      ≤ Nat.card (Multiplicative (ZMod 2)) := Finite.card_subtype_le _
    _ = 2 := by simp [Nat.card_eq_fintype_card]

/-- **`[Π^tp_Y : Π^tp_Ÿ] = 2` as soon as some element of `Π^tp_Y` acts on `X'` by the
involution** (equivalently, `Y ×_X X'` is connected; not proved here). -/
theorem relIndex_eq_two (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)
    (h : ∃ α ∈ (character (A := A) D.toData V hV).ker, (character₂ (A := A) D V hV s hs α).2 ≠ 1) :
    (piYddot (A := A) D V hV s hs).relIndex (character (A := A) D.toData V hV).ker = 2 := by
  obtain ⟨α, hα, hne⟩ := h
  rw [Subgroup.relIndex, ← ker_sndOnPiY, Subgroup.index_ker]
  have hsurj : Function.Surjective (sndOnPiY (A := A) D V hV s hs) := by
    intro y
    rcases zmod2_cases (Multiplicative.toAdd y) with hy | hy
    · exact ⟨1, by rw [map_one]; exact (Multiplicative.toAdd.injective hy).symm⟩
    · refine ⟨⟨α, hα⟩, ?_⟩
      change (character₂ (A := A) D V hV s hs α).2 = y
      rcases zmod2_cases (Multiplicative.toAdd (character₂ (A := A) D V hV s hs α).2) with
        h0 | h1
      · exact absurd (Multiplicative.toAdd.injective h0) hne
      · exact Multiplicative.toAdd.injective (h1.trans hy.symm)
  rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
  simp [Nat.card_eq_fintype_card]

end Proj

/-! ### Index `2` from the Galois action -/

section GaloisIndex

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Galois elements lie in `Π^tp_Y`**: they act trivially on the fibre of `Y` (its level is
`R` itself). -/
theorem character_galois (σ : decompositionGroup R V) :
    character (A := A) D.toData V hV (galoisToTempered O R A hV σ) = 1 := by
  refine FibreAut.deckCharacterFun_eq (X₀ (A := A) D.toData) (deck D.toData)
    (basePoint D.toData V hV) (isDeckTorsor D.toData V hV) ?_
  rw [FibreAut.deckAct_one]
  change (basePoint D.toData V hV : (tempFibre O R A V hV).obj (X₀ (A := A) D.toData)) =
    ⟦TempObj.preGalois hV (X₀ (A := A) D.toData) σ σ.2 _⟧
  exact congrArg (Quotient.mk _) (Subtype.ext (Prod.ext
    ((subsingleton_fibre (A := A)).elim _ _) rfl))

/-- **A Galois element with `σ(√c) = −√c` swaps the sheets of `X'`**:
`χ_Ÿ(σ) = (0, 1)`. -/
theorem character₂_galois (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c) (σ : decompositionGroup R V)
    (hσ : (σ : Ω ≃ₐ[R] Ω) s = -s) :
    character₂ (A := A) D V hV s hs (galoisToTempered O R A hV σ) =
      (1, Multiplicative.ofAdd 1) := by
  refine FibreAut.deckCharacterFun_eq (Yddot (A := A) D) (deck₂ D)
    (basePoint₂ (A := A) D V hV s hs) (isDeckTorsor₂ D V hV) ?_
  change (⟦TempObj.preMap V hV (deckHom₂ D (1, Multiplicative.ofAdd 1)) _⟧ :
    (tempFibre O R A V hV).obj (Yddot (A := A) D)) =
    ⟦TempObj.preGalois hV (Yddot (A := A) D) σ σ.2 _⟧
  refine (mk_eq_mk_iff D V hV).2 (Subtype.ext (Prod.ext ?_ ?_))
  · change (t₀ (A := A) D s hs).comp (σPow D (Multiplicative.ofAdd 1)) =
      ((σ : Ω ≃ₐ[R] Ω) : Ω →ₐ[R] Ω).comp (t₀ (A := A) D s hs)
    rw [σPow_ofAdd_one]
    refine QuadraticLevel.algHom_ext D.c ?_
    change (t₀ (A := A) D s hs) (QuadraticLevel.σ D.c (QuadraticLevel.x D.c)) =
      (σ : Ω ≃ₐ[R] Ω) ((t₀ (A := A) D s hs) (QuadraticLevel.x D.c))
    rw [QuadraticLevel.σ_x, map_neg]
    have hx : (t₀ (A := A) D s hs) (QuadraticLevel.x D.c) = s := QuadraticLevel.lift_x _ _ _
    rw [hx]
    exact hσ.symm
  · change ((decomp (A := A) D.toData).deckCode _ (level₂_ρs D) 1) _ = _
    rw [map_one]
    rfl

/-- **`[Π^tp_Y : Π^tp_Ÿ] = 2`** as soon as some element of the decomposition group of `V` moves
`√c`, i.e. the Kummer covering `X'` is not split at the valuation `V`. -/
theorem relIndex_eq_two_of_galois (s : Ω) (hs : s ^ 2 = algebraMap R Ω D.c)
    (h : ∃ σ : decompositionGroup R V, (σ : Ω ≃ₐ[R] Ω) s = -s) :
    (piYddot (A := A) D V hV s hs).relIndex (character (A := A) D.toData V hV).ker = 2 := by
  obtain ⟨σ, hσ⟩ := h
  refine relIndex_eq_two D V hV s hs ⟨galoisToTempered O R A hV σ,
    character_galois D V hV σ, ?_⟩
  rw [character₂_galois D V hV s hs σ hσ]
  decide

end GaloisIndex

end

end TateObject

end TemperedFundamentalGroups
