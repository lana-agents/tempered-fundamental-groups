/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Main

/-!
# S8.C: the Galois hull of a finite family and the lift of semilinear automorphisms

Blueprint §9.12, O6.6. For a finite family `F' k` of finite extensions of `C(x)`, the **Galois
hull** `galoisHull C F'` is the compositum, inside an algebraic closure `Ω` of `C(x)`, of the normal
closures of the `F' k`: a finite Galois extension of `C(x)` into which every `F' k` embeds
(`exists_embedding`).

* `exists_factor`: a ring homomorphism from a finite product of fields to a field factors through
  one projection;
* `exists_lift`: every ring automorphism `σ` of `Π k, F' k` which is semilinear over an
  automorphism `τ` of `C` (acting on coefficients of `C(x)`) lifts to a `τ`-semilinear
  automorphism of the Galois hull (via an extension `ρ` of `τ` to `Ω`, which maps the hull onto
  itself because `σ` permutes the factors by semilinear isomorphisms).

`S8CDescent` (open interface, A6 + node analogue) is the descent of semistability from the hull to
the members; `s8cReduction_of_descent` assembles `S8A.S8CReduction`.
-/

universe u v

open IntermediateField

namespace SemistableReduction

namespace S8A

section Factor

variable {κ : Type*} [Finite κ] {F : κ → Type*} [∀ k, Field (F k)]
  {L : Type*} [Field L]

/-- **Ring homomorphisms from a finite product of fields to a field factor through a
projection.** -/
lemma exists_factor (f : (Π k, F k) →+* L) : ∃ j, ∃ g : F j →+* L, ∀ x, f x = g (x j) := by
  classical
  haveI := Fintype.ofFinite κ
  -- some idempotent `Pi.single j 1` maps to `1`
  have hsum : ∑ j, (Pi.single j 1 : Π k, F k) = 1 := Finset.univ_sum_single 1
  obtain ⟨j, hj⟩ : ∃ j, f (Pi.single j 1) ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg f hsum
    rw [map_sum, Finset.sum_eq_zero fun j _ ↦ h j, map_one] at this
    exact zero_ne_one this
  have hidem : f (Pi.single j 1) = 1 := by
    have h2 : f (Pi.single j 1) * f (Pi.single j 1) = f (Pi.single j 1) := by
      rw [← map_mul, ← Pi.single_mul, one_mul]
    exact (mul_left_eq_self₀.1 (by rw [mul_comm]; exact h2)).resolve_right hj
  let g : F j →+* L :=
    { toFun := fun y ↦ f (Pi.single j y)
      map_one' := hidem
      map_mul' := fun y y' ↦ by rw [Pi.single_mul, map_mul]
      map_zero' := by simp
      map_add' := fun y y' ↦ by rw [Pi.single_add, map_add] }
  refine ⟨j, g, fun x ↦ ?_⟩
  change f x = f (Pi.single j (x j))
  have : x * Pi.single j 1 = Pi.single j (x j) := by
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [← this, map_mul, hidem, mul_one]

end Factor

variable (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
  {κ : Type} [Finite κ] (F' : κ → Type v) [∀ k, Field (F' k)]
  [∀ k, Algebra (RatFunc C) (F' k)] [∀ k, Algebra C (F' k)]
  [∀ k, IsScalarTower C (RatFunc C) (F' k)] [∀ k, FiniteDimensional (RatFunc C) (F' k)]

/-- The algebraic closure of `C(x)` in which the hull is formed. -/
abbrev Ωc : Type u := AlgebraicClosure (RatFunc C)

/-- **The Galois hull** of a finite family of finite extensions of `C(x)`. -/
noncomputable def galoisHull : IntermediateField (RatFunc C) (Ωc C) :=
  ⨆ k, normalClosure (RatFunc C) (F' k) (Ωc C)

instance : FiniteDimensional (RatFunc C) (galoisHull C F') := by
  unfold galoisHull; infer_instance

instance : Normal (RatFunc C) (galoisHull C F') := by
  unfold galoisHull; infer_instance

instance : IsGalois (RatFunc C) (galoisHull C F') := { }

omit [(k : κ) → Algebra C (F' k)] [IsUltrametricDist C] [IsAlgClosed C] [Finite κ] in
/-- Every member embeds into the hull. -/
lemma exists_embedding (k : κ) : Nonempty (F' k →ₐ[RatFunc C] galoisHull C F') := by
  have f : F' k →ₐ[RatFunc C] Ωc C := IsAlgClosed.lift
  have hf : f.fieldRange ≤ galoisHull C F' :=
    (f.fieldRange_le_normalClosure).trans (le_iSup (fun k ↦ normalClosure (RatFunc C) (F' k)
      (Ωc C)) k)
  exact ⟨f.codRestrict (galoisHull C F').toSubalgebra fun x ↦ hf ⟨x, rfl⟩⟩

section Lift

variable {C F'} (τ : C ≃+* C) (σ : (Π k, F' k) ≃+* (Π k, F' k))
  (hσ : ∀ (φ : RatFunc C) (k : κ), σ (fun k' ↦ algebraMap (RatFunc C) (F' k') φ) k =
    algebraMap (RatFunc C) (F' k) (ratFuncMap τ.toRingHom φ))

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
  [∀ (k : κ), IsScalarTower C (RatFunc C) (F' k)]
  [∀ (k : κ), FiniteDimensional (RatFunc C) (F' k)] in
omit [(k : κ) → Algebra C (F' k)] in
include hσ in
/-- `σ` permutes the factors by bijective semilinear homomorphisms. -/
lemma exists_factor_sigma (k : κ) : ∃ j, ∃ g : F' j →+* F' k, (∀ x, σ x k = g (x j)) ∧
    Function.Bijective g ∧ ∀ φ, g (algebraMap (RatFunc C) (F' j) φ) =
      algebraMap (RatFunc C) (F' k) (ratFuncMap τ.toRingHom φ) := by
  classical
  obtain ⟨j, g, hg⟩ := exists_factor ((Pi.evalRingHom F' k).comp σ.toRingHom)
  refine ⟨j, g, fun x ↦ hg x, ⟨g.injective, fun y ↦ ?_⟩, fun φ ↦ ?_⟩
  · refine ⟨σ.symm (Pi.single k y) j, ?_⟩
    rw [← hg]
    simp
  · rw [← hσ φ k]
    have := hg (fun k' ↦ algebraMap (RatFunc C) (F' k') φ)
    simpa using this.symm

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
  [∀ (k : κ), IsScalarTower C (RatFunc C) (F' k)]
  [∀ (k : κ), FiniteDimensional (RatFunc C) (F' k)] in
omit [(k : κ) → Algebra C (F' k)] in
include hσ in
/-- Every factor is the source of some factor map. -/
lemma exists_eq_factor (j₀ : κ) : ∃ k, Classical.choose (exists_factor_sigma τ σ hσ k) = j₀ := by
  classical
  by_contra h
  push Not at h
  have hx : (Pi.single j₀ 1 : Π k, F' k) ≠ 0 := by
    intro h0
    have := congrFun h0 j₀
    simp at this
  apply hx
  apply σ.injective
  ext k
  obtain ⟨g, hg, -⟩ := Classical.choose_spec (exists_factor_sigma τ σ hσ k)
  rw [hg, Pi.single_eq_of_ne (h k), map_zero, map_zero, Pi.zero_apply]

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
  [∀ (k : κ), IsScalarTower C (RatFunc C) (F' k)]
  [∀ (k : κ), FiniteDimensional (RatFunc C) (F' k)] in
omit [(k : κ) → Algebra C (F' k)] in
include hσ in
/-- **The hull is stable** under every extension `ρ` of the action of `τ` on `C(x)`. -/
lemma map_mem_galoisHull (ρ : Ωc C ≃+* Ωc C)
    (hρ : ∀ φ, ρ (algebraMap (RatFunc C) (Ωc C) φ) =
      algebraMap (RatFunc C) (Ωc C) (ratFuncMap τ.toRingHom φ))
    {x : Ωc C} (hx : x ∈ galoisHull C F') : ρ x ∈ galoisHull C F' := by
  classical
  let H : IntermediateField (RatFunc C) (Ωc C) :=
    { (galoisHull C F').toSubfield.comap ρ.toRingHom with
      algebraMap_mem' := fun φ ↦ by
        change ρ (algebraMap (RatFunc C) (Ωc C) φ) ∈ galoisHull C F'
        rw [hρ]
        exact (galoisHull C F').algebraMap_mem _ }
  have hle : galoisHull C F' ≤ H := by
    refine iSup_le fun k₀ ↦ normalClosure_le_iff.2 fun f ↦ ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨k, hk⟩ := exists_eq_factor τ σ hσ k₀
    obtain ⟨g, -, hbij, hgφ⟩ := Classical.choose_spec (exists_factor_sigma τ σ hσ k)
    revert y f
    rw [← hk]
    intro f y
    set e := RingEquiv.ofBijective g hbij
    have he : ∀ φ, e.symm (algebraMap (RatFunc C) (F' k) φ) =
        algebraMap (RatFunc C) _ ((Transport.ratFuncEquiv τ).symm φ) := fun φ ↦ by
      rw [RingEquiv.symm_apply_eq]
      change _ = g _
      rw [hgφ, ← Transport.ratFuncEquiv_apply, RingEquiv.apply_symm_apply]
    let h'' : F' k →ₐ[RatFunc C] Ωc C :=
      { toRingHom := ρ.toRingHom.comp (f.toRingHom.comp e.symm.toRingHom)
        commutes' := fun φ ↦ by
          change ρ (f (e.symm (algebraMap (RatFunc C) (F' k) φ))) = _
          rw [he, f.commutes, hρ, ← Transport.ratFuncEquiv_apply, RingEquiv.apply_symm_apply] }
    have hy : ρ (f y) = h'' (e y) := by
      change ρ (f y) = ρ (f (e.symm (e y)))
      rw [RingEquiv.symm_apply_apply]
    change ρ (f y) ∈ galoisHull C F'
    rw [hy]
    exact (h''.fieldRange_le_normalClosure.trans (le_iSup (fun k ↦ normalClosure (RatFunc C)
      (F' k) (Ωc C)) k)) ⟨e y, rfl⟩
  exact hle hx

omit [IsUltrametricDist C] [IsAlgClosed C] [∀ (k : κ), IsScalarTower C (RatFunc C) (F' k)]
  [∀ (k : κ), FiniteDimensional (RatFunc C) (F' k)] in
omit [(k : κ) → Algebra C (F' k)] in
include hσ in
/-- **Lift of semilinear automorphisms to the Galois hull.** -/
theorem exists_lift : ∃ σ'' : galoisHull C F' ≃+* galoisHull C F',
    IsSemilinear C (galoisHull C F') τ σ'' := by
  let ρ : Ωc C ≃+* Ωc C := IsAlgClosure.equivOfEquiv (Ωc C) (Ωc C) (Transport.ratFuncEquiv τ)
  have hρ : ∀ φ, ρ (algebraMap (RatFunc C) (Ωc C) φ) =
      algebraMap (RatFunc C) (Ωc C) (ratFuncMap τ.toRingHom φ) := fun φ ↦
    IsAlgClosure.equivOfEquiv_algebraMap _ _ _ φ
  have hρ' : ∀ φ, ρ.symm (algebraMap (RatFunc C) (Ωc C) φ) =
      algebraMap (RatFunc C) (Ωc C) (ratFuncMap τ.symm.toRingHom φ) := fun φ ↦
    IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ _ φ
  have hσ' : ∀ (φ : RatFunc C) (k : κ), σ.symm (fun k' ↦ algebraMap (RatFunc C) (F' k') φ) k =
      algebraMap (RatFunc C) (F' k) (ratFuncMap τ.symm.toRingHom φ) := by
    intro φ k
    have : σ (fun k' ↦ algebraMap (RatFunc C) (F' k') (ratFuncMap τ.symm.toRingHom φ)) =
        fun k' ↦ algebraMap (RatFunc C) (F' k') φ := by
      funext k'
      rw [hσ, ← Transport.ratFuncEquiv_apply]
      exact congrArg _ ((Transport.ratFuncEquiv τ).apply_symm_apply φ)
    rw [← this, RingEquiv.symm_apply_apply]
  refine ⟨{ toFun := fun x ↦ ⟨ρ x, map_mem_galoisHull τ σ hσ ρ hρ x.2⟩
            invFun := fun x ↦ ⟨ρ.symm x, map_mem_galoisHull τ.symm σ.symm hσ' ρ.symm hρ' x.2⟩
            left_inv := fun x ↦ Subtype.ext (ρ.symm_apply_apply _)
            right_inv := fun x ↦ Subtype.ext (ρ.apply_symm_apply _)
            map_mul' := fun x y ↦ Subtype.ext (map_mul ρ _ _)
            map_add' := fun x y ↦ Subtype.ext (map_add ρ _ _) }, fun φ ↦ Subtype.ext ?_⟩
  exact hρ φ

end Lift

end S8A

end SemistableReduction

namespace SemistableReduction

namespace S8A

/-- **S8.C, descent** ([AW Prop 2.1], L1 A6 and its node analogue; open interface, Blueprint §9.12
O6.6): a Gauss tree semistable for the Galois hull of a finite family is semistable for every
member. -/
def S8CDescent : Prop :=
  ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
    (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
    ∀ (κ : Type) [Fintype κ] (F' : κ → Type v) [∀ k, Field (F' k)]
    [∀ k, Algebra (RatFunc C) (F' k)] [∀ k, Algebra C (F' k)]
    [∀ k, IsScalarTower C (RatFunc C) (F' k)] [∀ k, FiniteDimensional (RatFunc C) (F' k)]
    (ι : Type) [Fintype ι] (a c : ι → C) (hc : ∀ i, c i ≠ 0),
    W7.IsSemistableTree a c hc (galoisHull C F') → ∀ k, W7.IsSemistableTree a c hc (F' k)

/-- **S8.C from the descent interface**: the Galois hull and the lift `exists_lift`. -/
theorem s8cReduction_of_descent (h : S8CDescent.{u, v}) : S8CReduction.{u, v} := by
  intro C _ _ _ _ p hp hp1 κ _ F' _ _ _ _ _
  refine ⟨galoisHull C F', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, fun ι _ a c hc hV k ↦ h C p hp hp1 κ F' ι a c hc hV k, ?_⟩
  rintro τ - ⟨σ, hσ⟩
  exact exists_lift τ σ hσ

end S8A

/-- **W7 from the local interfaces** (S8.B, R5, finiteness of bad balls, `∞`, EdgeRepair, and
the S8.C descent); transport and the Galois lift are proved. -/
theorem W7.statement_of_interfaces' (hG : S8A.GaloisInputs.{u}) (hD : S8A.S8CDescent.{u, v}) :
    W7.Statement.{u, v} :=
  W7.statement_of_interfaces hG (S8A.s8cReduction_of_descent hD)

end SemistableReduction
