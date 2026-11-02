/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Etale.Basic
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoEtale

/-!
# Re-charting an algebra given on two old charts to a new chart (generic commutative algebra)

A coherent algebra on a scheme covered by two affine opens `Spec P`, `Spec Q` is given by a
`P`-algebra `D`, a `Q`-algebra `E` and an identification over the overlap. A new affine open
`Spec R` (e.g. the chart `t ≠ ∞` of `ℙ¹` after a Möbius transformation `t = ā h' / (h' + 1 − ā)` of
the coordinate `h'` of the old charts) that is not contained in either old chart is covered by
`D(a) ⊆ Spec P` and `D(b) ⊆ Spec Q` with `(a, b) = R`; the sections of the algebra over `Spec R` are
the **equaliser of the two chart algebras**

  `ReChart.glued = (Ra ⊗_P D) ×_{Rab ⊗_P D} (Rb ⊗_Q E)`  (`Ra = R[1/a]`, `Rb = R[1/b]`,
  `Rab = R[1/ab]`),

where the overlap identification is given as `ω : Rab ⊗_Q E ≃ₐ[Rab] Rab ⊗_P D` (the restriction of
the old overlap identification to `Spec Rab`). This is `ZariskiTwo.glued` for the base-changed
pieces. Nothing about the shape of `D`, `E` is used (MR13 (e2): the vertex covering of the Tate
special fibre, given in the coordinates `h'`, `h = 1/h'` of the normalisation, is re-charted to
the datum `S0` over `V₀ = Spec k[t]` of `P1Three`).

* `ReChart.isLocalization_bc` / `isLocalization_away_bc`: base change along a localization is a
  localization (`S' = S_M` ⟹ `S' ⊗_P D = (S ⊗_P D)_M`), via Mathlib's
  `IsLocalization.tensorProduct_tensorProduct`;
* `ReChart.etale_tensor`: if `Pu ⊗_P D` is étale over `Pu = P[1/u]` and `u` is a unit in `T`,
  then `T ⊗_P D` is étale over `T` (`Algebra.TensorProduct.cancelBaseChange`);
* **`ReChart.isLocalization_fst`**, **`isLocalization_snd`**: `C[1/a] = Ra ⊗_P D`,
  `C[1/b] = Rb ⊗_Q E` for `C = ReChart.glued`;
* **`ReChart.finite_glued`**: `C` is finite over `R` if `D`, `E` are finite over `P`, `Q` and
  `(a, b) = R`;
* **`ReChart.isLocalization_toT`**: `C[1/(a c)] = T ⊗_P D` for `T = Ra[1/c]` (e.g. the overlap
  `V₀ ∩ V₁ = D(X̄)` of `P1Three`, `X̄ = (t − ā) · t (t − 1)`).
-/

universe u

open TensorProduct

namespace ReChart

noncomputable section

/-! ### Base change of a piece along a localization -/

section Base

variable (P : Type u) [CommRing P] (S S' : Type u) [CommRing S] [CommRing S'] [Algebra P S]
  [Algebra P S'] [Algebra S S'] [IsScalarTower P S S'] (D : Type u) [CommRing D] [Algebra P D]

/-- The base change `S ⊗_P D → S' ⊗_P D` along `S → S'`. -/
def bc : S ⊗[P] D →ₐ[S] S' ⊗[P] D :=
  Algebra.TensorProduct.map (Algebra.ofId S S') (AlgHom.id P D)

@[simp] lemma bc_tmul (s : S) (d : D) : bc P S S' D (s ⊗ₜ d) = algebraMap S S' s ⊗ₜ d := rfl

/-- `S' ⊗_P D` as an algebra over `S ⊗_P D` through `bc`. -/
@[reducible] def algBc : Algebra (S ⊗[P] D) (S' ⊗[P] D) := (bc P S S' D).toRingHom.toAlgebra

lemma towerBc : letI := algBc P S S' D
    IsScalarTower S (S ⊗[P] D) (S' ⊗[P] D) :=
  letI := algBc P S S' D
  IsScalarTower.of_algebraMap_eq fun x ↦ ((bc P S S' D).commutes x).symm

/-- **Base change along a localization is a localization**: if `S' = S_M`, then
`S' ⊗_P D = (S ⊗_P D)_M`. -/
theorem isLocalization_bc (M : Submonoid S) [IsLocalization M S'] :
    letI := algBc P S S' D
    IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[P] D) M) (S' ⊗[P] D) := by
  letI := algBc P S S' D
  haveI := towerBc P S S' D
  refine IsLocalization.tensorProduct_tensorProduct P D M S' (RingHom.ext fun d ↦ ?_)
  change bc P S S' D (1 ⊗ₜ d) = 1 ⊗ₜ d
  rw [bc_tmul, map_one]

/-- The same, away from an element. -/
theorem isLocalization_away_bc (s : S) [IsLocalization.Away s S'] :
    letI := algBc P S S' D
    IsLocalization.Away (algebraMap S (S ⊗[P] D) s) (S' ⊗[P] D) := by
  letI := algBc P S S' D
  have h := isLocalization_bc P S S' D (Submonoid.powers s)
  rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h

end Base

/-! ### Étaleness of a base-changed piece -/

section Etale

variable (P Pu : Type u) [CommRing P] [CommRing Pu] [Algebra P Pu] (u : P)
  [IsLocalization.Away u Pu] (T : Type u) [CommRing T] [Algebra P T]
  (D : Type u) [CommRing D] [Algebra P D]

/-- **Base change of a piece étale over `D(u)`** to a ring in which `u` is a unit is étale. -/
theorem etale_tensor (hu : IsUnit (algebraMap P T u)) [Algebra.Etale Pu (Pu ⊗[P] D)] :
    Algebra.Etale T (T ⊗[P] D) := by
  letI : Algebra Pu T := (IsLocalization.Away.lift u hu).toAlgebra
  haveI : IsScalarTower P Pu T := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.Away.lift_eq u hu x).symm
  haveI : Algebra.Etale T (T ⊗[Pu] (Pu ⊗[P] D)) := Algebra.Etale.baseChange Pu _ T
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange P Pu T T D)

end Etale

/-! ### Glueing two base-changed pieces over a new chart -/

section Glue

variable {R : Type u} [CommRing R] (a b : R)
  (Ra Rb Rab : Type u) [CommRing Ra] [CommRing Rb] [CommRing Rab]
  [Algebra R Ra] [Algebra R Rb] [Algebra R Rab] [Algebra Ra Rab] [Algebra Rb Rab]
  [IsScalarTower R Ra Rab] [IsScalarTower R Rb Rab]
  (P Q : Type u) [CommRing P] [CommRing Q] [Algebra P Ra] [Algebra Q Rb] [Algebra P Rab]
  [Algebra Q Rab] [IsScalarTower P Ra Rab] [IsScalarTower Q Rb Rab]
  (D E : Type u) [CommRing D] [CommRing E] [Algebra P D] [Algebra Q E]
  (ω : Rab ⊗[Q] E ≃ₐ[Rab] Rab ⊗[P] D)

/-- The restriction of the first piece to the overlap. -/
def ρa : Ra ⊗[P] D →ₐ[R] Rab ⊗[P] D := (bc P Ra Rab D).restrictScalars R

/-- The restriction of the second piece to the overlap, followed by the overlap identification. -/
def ρb : Rb ⊗[Q] E →ₐ[R] Rab ⊗[P] D :=
  (ω.toAlgHom.restrictScalars R).comp ((bc Q Rb Rab E).restrictScalars R)

/-- **The re-charted algebra**: the sections over the new chart `Spec R = D(a) ∪ D(b)` of the
algebra given by `D` on the old chart `P` and `E` on the old chart `Q`, i.e. the equaliser
`(Ra ⊗_P D) ×_{Rab ⊗_P D} (Rb ⊗_Q E)`. -/
abbrev glued : Subalgebra R ((Ra ⊗[P] D) × (Rb ⊗[Q] E)) :=
  ZariskiTwo.glued (ρa Ra Rab P D (R := R)) (ρb Rb Rab P Q D E ω (R := R))

lemma ρa_tmul (r : Ra) (d : D) : ρa Ra Rab P D (R := R) (r ⊗ₜ d) = algebraMap Ra Rab r ⊗ₜ d := rfl

lemma ρb_tmul (r : Rb) (e : E) :
    ρb Rb Rab P Q D E ω (R := R) (r ⊗ₜ e) = ω (algebraMap Rb Rab r ⊗ₜ e) := rfl

variable [IsLocalization.Away a Ra] [IsLocalization.Away b Rb]
  [IsLocalization.Away (algebraMap R Ra b) Rab] [IsLocalization.Away (algebraMap R Rb a) Rab]

include a in
lemma isUnit_a : IsUnit (algebraMap R (Ra ⊗[P] D) a) := by
  rw [IsScalarTower.algebraMap_apply R Ra (Ra ⊗[P] D)]
  exact (IsLocalization.Away.algebraMap_isUnit a).map _

include b in
lemma isUnit_b : IsUnit (algebraMap R (Rb ⊗[Q] E) b) := by
  rw [IsScalarTower.algebraMap_apply R Rb (Rb ⊗[Q] E)]
  exact (IsLocalization.Away.algebraMap_isUnit b).map _

lemma isLocalization_ρa : letI := (ρa Ra Rab P D (R := R)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (Ra ⊗[P] D) b) (Rab ⊗[P] D) := by
  have h := isLocalization_away_bc P Ra Rab D (algebraMap R Ra b)
  rwa [← IsScalarTower.algebraMap_apply R Ra (Ra ⊗[P] D)] at h

lemma isLocalization_ρb : letI := (ρb Rb Rab P Q D E ω (R := R)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (Rb ⊗[Q] E) a) (Rab ⊗[P] D) := by
  letI := algBc Q Rb Rab E
  have h := isLocalization_away_bc Q Rb Rab E (algebraMap R Rb a)
  rw [← IsScalarTower.algebraMap_apply R Rb (Rb ⊗[Q] E)] at h
  letI := (ρb Rb Rab P Q D E ω (R := R)).toRingHom.toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := ω.toRingEquiv) fun _ ↦ rfl)

/-- **The re-charted algebra restricts to the first piece**: `C[1/a] = Ra ⊗_P D`. -/
theorem isLocalization_fst :
    letI := ZariskiTwo.algebraFst (ρa := ρa Ra Rab P D (R := R))
      (ρb := ρb Rb Rab P Q D E ω (R := R))
    IsLocalization.Away (algebraMap R (glued Ra Rb Rab P Q D E ω (R := R)) a) (Ra ⊗[P] D) :=
  ZariskiTwo.isLocalization_fst a (isUnit_a a Ra P D (R := R))
    (isLocalization_ρb a Rb Rab P Q D E ω)

/-- **The re-charted algebra restricts to the second piece**: `C[1/b] = Rb ⊗_Q E`. -/
theorem isLocalization_snd :
    letI := ZariskiTwo.algebraSnd (ρa := ρa Ra Rab P D (R := R))
      (ρb := ρb Rb Rab P Q D E ω (R := R))
    IsLocalization.Away (algebraMap R (glued Ra Rb Rab P Q D E ω (R := R)) b) (Rb ⊗[Q] E) :=
  ZariskiTwo.isLocalization_snd (isUnit_b b Rb Q E (R := R))
    (isLocalization_ρa b Ra Rab P D (R := R))

/-- **Finiteness**: the re-charted algebra of finite pieces is finite. -/
theorem finite_glued (hab : Ideal.span {a, b} = ⊤) [Module.Finite P D] [Module.Finite Q E] :
    Module.Finite R (glued Ra Rb Rab P Q D E ω (R := R)) :=
  ZariskiTwo.finite_glued' hab (isUnit_a a Ra P D (R := R)) (isLocalization_ρb a Rb Rab P Q D E ω)
    (isUnit_b b Rb Q E (R := R)) (isLocalization_ρa b Ra Rab P D (R := R)) Ra Rb

end Glue

/-! ### Further localizations of the re-charted algebra -/

section Away

variable {R : Type u} [CommRing R] (a b : R)
  (Ra Rb Rab : Type u) [CommRing Ra] [CommRing Rb] [CommRing Rab]
  [Algebra R Ra] [Algebra R Rb] [Algebra R Rab] [Algebra Ra Rab] [Algebra Rb Rab]
  [IsScalarTower R Ra Rab] [IsScalarTower R Rb Rab]
  (P Q : Type u) [CommRing P] [CommRing Q] [Algebra P Ra] [Algebra Q Rb] [Algebra P Rab]
  [Algebra Q Rab] [IsScalarTower P Ra Rab] [IsScalarTower Q Rb Rab]
  (D E : Type u) [CommRing D] [CommRing E] [Algebra P D] [Algebra Q E]
  (ω : Rab ⊗[Q] E ≃ₐ[Rab] Rab ⊗[P] D)
  (c : R) (T : Type u) [CommRing T] [Algebra R T] [Algebra Ra T] [IsScalarTower R Ra T]
  [Algebra P T] [IsScalarTower P Ra T]

/-- The restriction of the re-charted algebra to `D(a c) ⊆ D(a)`, through the first piece. -/
def toT : glued Ra Rb Rab P Q D E ω (R := R) →ₐ[R] T ⊗[P] D :=
  ((bc P Ra T D).restrictScalars R).comp (ZariskiTwo.fst _ _)

lemma toT_apply (x : glued Ra Rb Rab P Q D E ω (R := R)) :
    toT Ra Rb Rab P Q D E ω T (R := R) x = bc P Ra T D x.1.1 := rfl

variable [IsLocalization.Away a Ra] [IsLocalization.Away b Rb]
  [IsLocalization.Away (algebraMap R Ra b) Rab] [IsLocalization.Away (algebraMap R Rb a) Rab]
  [IsLocalization.Away (algebraMap R Ra c) T]

/-- **Localizations inside the first piece**: if `T = Ra[1/c]`, then
`C[1/(a c)] = T ⊗_P D`. -/
theorem isLocalization_toT :
    letI := (toT Ra Rb Rab P Q D E ω T (R := R)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (glued Ra Rb Rab P Q D E ω (R := R)) (a * c)) (T ⊗[P] D) := by
  letI := ZariskiTwo.algebraFst (ρa := ρa Ra Rab P D (R := R))
    (ρb := ρb Rb Rab P Q D E ω (R := R))
  haveI := isLocalization_fst a Ra Rb Rab P Q D E ω
  letI := algBc P Ra T D
  letI := (toT Ra Rb Rab P Q D E ω T (R := R)).toRingHom.toAlgebra
  haveI : IsScalarTower (glued Ra Rb Rab P Q D E ω (R := R)) (Ra ⊗[P] D) (T ⊗[P] D) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h := isLocalization_away_bc P Ra T D (algebraMap R Ra c)
  have hc : algebraMap Ra (Ra ⊗[P] D) (algebraMap R Ra c) =
      algebraMap (glued Ra Rb Rab P Q D E ω (R := R)) (Ra ⊗[P] D)
        (algebraMap R (glued Ra Rb Rab P Q D E ω (R := R)) c) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact ((ZariskiTwo.fst _ _).commutes c).symm
  rw [hc] at h
  rw [map_mul]
  exact IsLocalization.Away.mul' (Ra ⊗[P] D) (T ⊗[P] D) _ _

end Away

end

end ReChart
