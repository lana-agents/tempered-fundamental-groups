/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.LevelClass
import TemperedFundamentalGroups.Andre.OrbStageGroup

/-!
# The stage groups of orbifold Galois objects on level classes (Blueprint §11.3, G6.10)

For an orbifold Galois object `U = OrbGal.obj D hX hp hc` (`Ind_1^S Z̃` over the induced level
`(Π_{x : S} B^{(α x)}, S)`, `B` Galois over `R`):

* `stageLevelO : Π_U →* Perm (F_L / H⁰)`: the action on level classes (`stageCls`);
  **`ker_stageLevelO`: its kernel is the deck group of `Z̃`** (`range deckStageO`);
* `twGroup D = S ×_A SemilinearAut R A B = {(x, γ) | γ.a = α x}` and the anti-homomorphism
  `twPerm : (twGroup D)ᵐᵒᵖ →* Perm (F_L / H⁰)`, `[t] ↦ [t ∘ twF x γ]` (`twF x' γ' ∘ twF x γ =`
  `twF (x' x) (γ' γ)` acting on the right); **`mem_ker_twPerm`: its kernel is
  `{(x, 1) | α x = 1}`**; **`range_stageLevelO`: `range stageLevelO = range twPerm`**;
* hence (`(twGroup D) / {(x, 1) | x ∈ ker α} ≅ SemilinearAut R A B`, `α` being surjective)
  **`stageSemilinO : Π_U →* (SemilinearAut R A B)ᵐᵒᵖ`**, surjective with kernel the deck
  group (`stageGroupO_extension`), and `stageQuotEquivO : Π_U ⧸ deck ≃* (SemilinearAut R A B)ᵐᵒᵖ`:
  the exact sequence `1 → π₁(Z̃ → Z₁) → Π_U → (SemilinearAut R A B)ᵐᵒᵖ → 1`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit OrbGal

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  {A₁ : Type u} [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]

namespace OrbGal

variable {X₁ : TempObj O R A₁} (D : IndData (μ₁ A A₁) X₁) [Subsingleton X₁.Lv.L.H]
  (hX : IndFaithful X₁) {E : Type u} [TopologicalSpace E] {p : E → X₁.Lv.Z}
  (hp : IsUniversalCovering.{u, u, u, u} p) (hc : ∀ z, (p ⁻¹' {z}).Countable)

/-! ### Twisted pairs -/

/-- **The group of twisted pairs** `S ×_A SemilinearAut R A B = {(x, γ) | γ.a = α x}`. -/
def twGroup : Subgroup (D.S × SemilinearAut R A X₁.Lv.L.B) where
  carrier := {g | g.2.a = D.α g.1}
  mul_mem' {g h} hg hh := by
    change (g.2 * h.2).a = D.α (g.1 * h.1)
    rw [SemilinearAut.mul_a, map_mul, hg, hh]
  one_mem' := by
    change (1 : SemilinearAut R A X₁.Lv.L.B).a = D.α 1
    rw [map_one, SemilinearAut.one_a]
  inv_mem' {g} hg := by
    change (g.2⁻¹).a = D.α g.1⁻¹
    rw [SemilinearAut.inv_a, map_inv, hg]

lemma mem_twGroup (g : D.S × SemilinearAut R A X₁.Lv.L.B) : g ∈ twGroup D ↔ g.2.a = D.α g.1 :=
  Iff.rfl

lemma twF_mul (x x' : D.S) (γ γ' : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α x)
    (hγ' : γ'.a = D.α x') (h : (γ * γ').a = D.α (x * x')) :
    twF D (x * x') (γ * γ') h = (twF D x γ hγ).comp (twF D x' γ' hγ') :=
  AlgHom.ext fun z => D.ext_ev fun y => by
    rw [AlgHom.comp_apply, ev_twF, ev_twF, ev_twF, mul_assoc]
    rfl

lemma twF_one (h : (1 : SemilinearAut R A X₁.Lv.L.B).a = D.α 1) :
    twF D 1 1 h = AlgHom.id R D.level.B :=
  AlgHom.ext fun z => D.ext_ev fun y => by
    rw [ev_twF, mul_one]
    rfl

variable {D} in
/-- The twisted map `[t] ↦ [t ∘ twF x γ]` of level classes of `OrbGal.obj`. -/
def levelTw (g : twGroup D) :
    LevelCls Ω (obj D hX hp hc) → LevelCls Ω (obj D hX hp hc) :=
  Quotient.map (fun t => t.comp (twF D g.1.1 g.1.2 g.2)) fun t t' ⟨k, hk⟩ => by
    let k' : D.level.H0 := k
    let tt : D.level.B →ₐ[R] Ω := t
    refine ⟨⟨(twφ D g.1.1 g.1.2 g.2 hX).r k', FiniteLevel.r_mem_H0 _ k'.2⟩, ?_⟩
    rw [← hk]
    exact (FiniteLevel.fibreAct_comp Ω (twφ D g.1.1 g.1.2 g.2 hX) k' tt).symm

lemma levelTw_mk (g : twGroup D) (t : (obj D hX hp hc).Lv.L.B →ₐ[R] Ω) :
    levelTw hX hp hc g (Quotient.mk _ t) = Quotient.mk _ (t.comp (twF D g.1.1 g.1.2 g.2)) :=
  rfl

lemma levelTw_mul (g h : twGroup D) (c : LevelCls Ω (obj D hX hp hc)) :
    levelTw hX hp hc (g * h) c = levelTw hX hp hc h (levelTw hX hp hc g c) := by
  induction c using Quotient.inductionOn with | h t => ?_
  change Quotient.mk _ (t.comp (twF D (g.1.1 * h.1.1) (g.1.2 * h.1.2) (g * h).2)) = _
  rw [twF_mul D _ _ _ _ g.2 h.2]
  rfl

lemma levelTw_one (c : LevelCls Ω (obj D hX hp hc)) : levelTw hX hp hc 1 c = c := by
  induction c using Quotient.inductionOn with | h t => ?_
  change Quotient.mk _ (t.comp (twF D 1 1 (1 : twGroup D).2)) = _
  rw [twF_one]
  rfl

variable (Ω) in
/-- **The action of the twisted pairs on level classes**, `[t] ↦ [t ∘ twF x γ]` (a right
action, hence a homomorphism out of the opposite group). -/
def twPerm : (twGroup D)ᵐᵒᵖ →* Equiv.Perm (LevelCls Ω (obj D hX hp hc)) where
  toFun g :=
    { toFun := levelTw hX hp hc g.unop
      invFun := levelTw hX hp hc g.unop⁻¹
      left_inv := fun c => by rw [← levelTw_mul, mul_inv_cancel, levelTw_one]
      right_inv := fun c => by rw [← levelTw_mul, inv_mul_cancel, levelTw_one] }
  map_one' := Equiv.ext fun c => levelTw_one D hX hp hc c
  map_mul' g h := Equiv.ext fun c => levelTw_mul D hX hp hc h.unop g.unop c

lemma twPerm_apply (g : (twGroup D)ᵐᵒᵖ) (c : LevelCls Ω (obj D hX hp hc)) :
    twPerm Ω D hX hp hc g c = levelTw hX hp hc g.unop c := rfl

/-- Untwisted pairs `(x, 1)`, `x ∈ ker α`, act on `F_L` through `H⁰` (by `gS x' = y x y⁻¹` on a
point on the copy `y`). -/
lemma exists_fibreAct_twF (x : D.S) (hx : D.α x = 1) (h : (1 : SemilinearAut R A X₁.Lv.L.B).a =
    D.α x) (t : (obj D hX hp hc).Lv.L.B →ₐ[R] Ω) :
    ∃ k : (obj D hX hp hc).Lv.L.H0, FiniteLevel.fibreAct Ω _ k t = t.comp (twF D x 1 h) := by
  let tt : D.level.B →ₐ[R] Ω := t
  obtain ⟨y, hy⟩ := D.exists_idem (tt : D.level.B →+* Ω)
  have hmem : gS D hX (y * x * y⁻¹) ∈ (D.lv hX).L.H0 := by
    rw [FiniteLevel.mem_H0]
    change D.α (y * x * y⁻¹) = 1
    rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  refine ⟨⟨_, hmem⟩, AlgHom.ext fun z => ?_⟩
  change tt (_) = tt (twF D x 1 h z)
  refine (D.onCopy_ev (tt : D.level.B →+* Ω) y hy _).symm.trans
    (Eq.trans ?_ (D.onCopy_ev (tt : D.level.B →+* Ω) y hy (twF D x 1 h z)))
  congr 1
  have h1 := IndData.ev_equivT_symm D hX (y * x * y⁻¹, 1) y z
  rw [map_one, inv_one, mul_one] at h1
  refine h1.trans ?_
  rw [ev_twF, inv_mul_cancel_right]
  rfl

variable [IsSchemeTheoreticallyDominant X₁.Lv.j]
  (hidem : ∀ e : X₁.Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
  (t₀ : X₁.Lv.L.B →ₐ[R] Ω)

include hidem t₀ in
/-- **The kernel of `twPerm` is `{(x, 1) | α x = 1}`** (rigidity of maps into the connected
`B`, `tw_level_eq`). -/
theorem mem_ker_twPerm (g : (twGroup D)ᵐᵒᵖ) :
    g ∈ (twPerm Ω D hX hp hc).ker ↔ D.α g.unop.1.1 = 1 ∧ g.unop.1.2 = 1 := by
  obtain ⟨⟨⟨x, γ⟩, hγ⟩⟩ := g
  change twPerm Ω D hX hp hc _ = 1 ↔ D.α x = 1 ∧ γ = 1
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h (Quotient.mk _ (t₀.comp D.ev₁))
    obtain ⟨k, hk⟩ := Quotient.exact h1
    obtain ⟨hx, hγ1⟩ := tw_level_eq D hX hidem t₀ x γ hγ k hk
    exact ⟨hx, SemilinearAut.ext (hγ.trans hx) (RingEquiv.ext hγ1)⟩
  · rintro ⟨hx, rfl⟩
    refine Equiv.ext fun c => ?_
    induction c using Quotient.inductionOn with | h t => ?_
    obtain ⟨k, hk⟩ := exists_fibreAct_twF D hX hp hc x hx hγ t
    exact (Quotient.sound ⟨k, hk⟩ : (Quotient.mk (levelSetoid Ω (obj D hX hp hc)) t) =
      Quotient.mk _ (t.comp (twF D x 1 hγ))).symm

/-! ### The projection to `SemilinearAut R A B` -/

/-- The projection `(x, γ) ↦ γ` of twisted pairs (on opposite groups). -/
def twSnd : (twGroup D)ᵐᵒᵖ →* (SemilinearAut R A X₁.Lv.L.B)ᵐᵒᵖ :=
  MonoidHom.op ((MonoidHom.snd _ _).comp (twGroup D).subtype)

lemma twSnd_apply (g : (twGroup D)ᵐᵒᵖ) : twSnd D g = MulOpposite.op g.unop.1.2 := rfl

/-- Every semilinear automorphism is part of a twisted pair (`α` is surjective). -/
lemma twSnd_surjective : Function.Surjective (twSnd D) := fun γ => by
  obtain ⟨x, hx⟩ := D.α_surj γ.unop.a
  exact ⟨MulOpposite.op ⟨(x, γ.unop), hx.symm⟩, rfl⟩

include hidem t₀ in
/-- `twPerm` and the projection to `SemilinearAut R A B` have the same kernel
`{(x, 1) | α x = 1}`. -/
lemma ker_twSnd : (twSnd D).ker = (twPerm Ω D hX hp hc).ker := by
  ext g
  rw [mem_ker_twPerm D hX hp hc hidem t₀, MonoidHom.mem_ker, twSnd_apply,
    MulOpposite.op_eq_one_iff]
  constructor
  · intro h
    refine ⟨?_, h⟩
    rw [← g.unop.2, h, SemilinearAut.one_a]
  · exact fun h => h.2

variable (hbase : ∃ (t₀ : X₁.Lv.L.B →ₐ[R] Ω) (e₀ : E), p e₀ = X₁.Lv.sp V hV t₀)

include hidem hbase in
/-- **The image of `twPerm` is `(SemilinearAut R A B)ᵐᵒᵖ`**:
`range twPerm ≅ (twGroup D)ᵐᵒᵖ / ker ≅ (SemilinearAut R A B)ᵐᵒᵖ`. -/
def twRangeEquiv : (twPerm Ω D hX hp hc).range ≃* (SemilinearAut R A X₁.Lv.L.B)ᵐᵒᵖ :=
  (QuotientGroup.quotientKerEquivRange _).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_twSnd D hX hp hc hidem
      hbase.choose).symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ (twSnd_surjective D)))

lemma twRangeEquiv_apply (g : (twGroup D)ᵐᵒᵖ) :
    twRangeEquiv V hV D hX hp hc hidem hbase ⟨twPerm Ω D hX hp hc g, g, rfl⟩ = twSnd D g := by
  have h : (QuotientGroup.quotientKerEquivRange (twPerm Ω D hX hp hc)).symm
      ⟨twPerm Ω D hX hp hc g, g, rfl⟩ = (g : (twGroup D)ᵐᵒᵖ ⧸ (twPerm Ω D hX hp hc).ker) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  change QuotientGroup.quotientKerEquivOfSurjective _ (twSnd_surjective D)
    (QuotientGroup.quotientMulEquivOfEq _ ((QuotientGroup.quotientKerEquivRange _).symm _)) = _
  rw [h]
  rfl

/-! ### The action of the stage group on level classes -/

section Stage

variable [ConnectedSpace X₁.Lv.Z]
  (hgal : ∀ t t' : X₁.Lv.L.B →ₐ[R] Ω, ∃ σ : X₁.Lv.L.B ≃ₐ[R] X₁.Lv.L.B,
    t.comp (σ : X₁.Lv.L.B →ₐ[R] X₁.Lv.L.B) = t')
  (hsym : ∀ a : A, ∃ γ : SemilinearAut R A X₁.Lv.L.B, γ.a = a)
  (hact : ∀ γ : SemilinearAut R A X₁.Lv.L.B, ∃ ψ : X₁.Lv.c.scheme ⟶ X₁.Lv.c.scheme,
    ψ ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec ∧
    X₁.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)

/-- `SameLevel` is equality of level classes. -/
lemma sameLevel_iff (u v : Fibre Ω V hV (obj D hX hp hc)) :
    SameLevel V hV D hX hp hc u v ↔
      levelCls V hV (obj D hX hp hc) u = levelCls V hV (obj D hX hp hc) v := by
  constructor
  · rintro ⟨q, q', rfl, rfl, k, hk⟩
    exact Quotient.sound ⟨k, hk⟩
  · intro h
    obtain ⟨q, rfl⟩ := Quotient.mk_surjective u
    obtain ⟨q', rfl⟩ := Quotient.mk_surjective v
    obtain ⟨k, hk⟩ := Quotient.exact h
    exact ⟨q, q', rfl, rfl, k, hk⟩

include hact hbase in
/-- **Every twisted pair is realised by an automorphism** of `OrbGal.obj` (`twIso`, by lifting
the model automorphism to `Z̃`). -/
lemma exists_twIso (x : D.S) (γ : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α x) :
    ∃ a : obj D hX hp hc ≅ obj D hX hp hc, a.hom.φ.f = twF D x γ hγ := by
  obtain ⟨-, e₀, -⟩ := hbase
  haveI : Nonempty E := ⟨e₀⟩
  obtain ⟨eψ, heψ, hj, hj'⟩ := exists_modelIso hact γ
  obtain ⟨e₂, he₂⟩ := hp.isCoveringMap.surjective_of_connectedSpace
    (specialFibreHomeomorph eψ heψ (p e₀))
  obtain ⟨τ, hτ, -⟩ := exists_lift_homeo hp (specialFibreHomeomorph eψ heψ) he₂
  exact ⟨twIso D hX hp hc x γ hγ eψ heψ hj hj' τ hτ, rfl⟩

include hgal hsym in
/-- Every geometric point of the induced level is a twisted translate of `t₀ ∘ ev₁`. -/
lemma exists_tw_eq (t : (obj D hX hp hc).Lv.L.B →ₐ[R] Ω) :
    ∃ (x : D.S) (γ : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α x),
      (t₀.comp D.ev₁).comp (twF D x γ hγ) = t := by
  let tt : D.level.B →ₐ[R] Ω := t
  obtain ⟨x', hx'⟩ := D.exists_idem (tt : D.level.B →+* Ω)
  obtain ⟨γ₀, hγ₀⟩ := hsym (D.α x')
  obtain ⟨γ, hγ, hγt⟩ := exists_semilinear_comp hgal t₀ (D.α x') γ₀ hγ₀ _
    (onCopy_algebraMap D tt x' hx')
  refine ⟨x', γ, hγ, AlgHom.ext fun y => ?_⟩
  change t₀ (D.ev 1 (twF D x' γ hγ y)) = tt y
  rw [ev_twF, one_mul]
  exact (RingHom.congr_fun hγt _).trans (IndData.onCopy_ev _ _ _ _ _)

include hgal hsym hact hbase in
/-- **Every level class of `OrbGal.obj` is the class of a point of its fibre.** -/
theorem levelCls_surjective_obj : Function.Surjective (levelCls V hV (obj D hX hp hc)) := by
  obtain ⟨t₀, e₀, he₀⟩ := id hbase
  intro c
  induction c using Quotient.inductionOn with | h t => ?_
  obtain ⟨x, γ, hγ, ht⟩ := exists_tw_eq D hX hp hc t₀ hgal hsym t
  obtain ⟨a, ha⟩ := exists_twIso V hV D hX hp hc hbase hact x γ hγ
  refine ⟨fibreMap V hV a.hom (Quotient.mk _ (basePre D hX hp hc V hV t₀ e₀ he₀)), ?_⟩
  rw [levelCls_fibreMap]
  change Quotient.mk _ ((t₀.comp D.ev₁).comp a.hom.φ.f) = _
  rw [ha]
  exact congrArg _ ht

end Stage

end OrbGal

end

end TemperedFundamentalGroups
