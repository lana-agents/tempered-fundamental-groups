/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelTowerMk
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwo

/-!
# Regular elements of the base on the pieces of a covering (Blueprint §12.8, M2.4, step 3f)

The special fibre of a level of the M2 patching is torsion-free over `k[X]` because every nonzero
polynomial in the coordinate is a nonzerodivisor on the base chart and stays one on all pieces
of the construction. Permanence of "`g ∈ R` acts regularly" (`IsSMulRegular`):

* `RegularPieces.finiteType_of_span_pow`, **`flat_of_span_pow`**: a formally étale algebra over a
  Noetherian ring which is finitely generated as a module up to powers of an element inverted in
  it is of finite type, hence étale, hence flat (the étale lifts `P`, `E n`, `E0 n`);
* `RegularPieces.isSMulRegular_of_flat`: flat algebras;
* `RegularPieces.isSMulRegular_subalgebra_prod`: subalgebras of products (formal glueings
  `FormalGlueing.glued`, Zariski glueings `ZariskiTwo.glued`);
* `RegularPieces.isSMulRegular_of_away`: a ring on which `f` is a nonzerodivisor, from its
  localization away from `f`;
* **`AdmissibleLift.isSMulRegular_NFall`**: the lifted formal model `NF` (its localization `NF_f`
  is flat over the completion `R̂`, which is flat over the Noetherian `R`, and `f` is a
  nonzerodivisor on `NF`);
* **`LevelTower.Level.isSMulRegular_G`**, **`LevelTower.Data.isSMulRegular_G`**: the patched
  algebras.
-/

universe u v

open TensorProduct

namespace SemistableReduction

namespace RegularPieces

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

/-- An algebra in which `b` is invertible and which is finitely generated as a module up to
powers of `b` is of finite type. -/
theorem finiteType_of_span_pow (b : R) (hb : IsUnit (algebraMap R S b)) (s : Finset S)
    (hs : ∀ p : S, ∃ k : ℕ, b ^ k • p ∈ Submodule.span R (s : Set S)) :
    Algebra.FiniteType R S := by
  classical
  refine ⟨⟨insert (↑hb.unit⁻¹ : S) s, eq_top_iff.mpr fun p _ ↦ ?_⟩⟩
  obtain ⟨k, hk⟩ := hs p
  have hsub : Submodule.span R (s : Set S) ≤
      Subalgebra.toSubmodule (Algebra.adjoin R ((insert (↑hb.unit⁻¹ : S) s : Finset S) : Set S)) :=
    Submodule.span_le.mpr fun x hx ↦ Algebra.subset_adjoin (by simp [hx])
  have hu : (↑hb.unit⁻¹ : S) ∈ Algebra.adjoin R ((insert (↑hb.unit⁻¹ : S) s : Finset S) : Set S) :=
    Algebra.subset_adjoin (by simp)
  have hp : p = (↑hb.unit⁻¹ : S) ^ k * (b ^ k • p) := by
    rw [Algebra.smul_def, map_pow, ← mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, one_mul]
  rw [hp]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hu _) (hsub hk)

/-- **A formally étale algebra over a Noetherian ring, finitely generated as a module up to powers
of an element inverted in it, is flat** (it is étale). -/
theorem flat_of_span_pow [IsNoetherianRing R] [Algebra.FormallyEtale R S] (b : R)
    (hb : IsUnit (algebraMap R S b)) (s : Finset S)
    (hs : ∀ p : S, ∃ k : ℕ, b ^ k • p ∈ Submodule.span R (s : Set S)) : Module.Flat R S := by
  haveI := finiteType_of_span_pow b hb s hs
  haveI : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  haveI : Algebra.Etale R S := {}
  infer_instance

/-- Regular elements stay regular on flat algebras. -/
theorem isSMulRegular_of_flat [Module.Flat R S] {g : R} (hg : IsSMulRegular R g) :
    IsSMulRegular S g :=
  (isSMulRegular_algebraMap_iff (A := S) (M := S)).mp hg.of_flat

/-- Regular elements on both factors are regular on a subalgebra of the product. -/
theorem isSMulRegular_subalgebra_prod {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (T : Subalgebra R (A × B)) {g : R} (hA : IsSMulRegular A g) (hB : IsSMulRegular B g) :
    IsSMulRegular T g := fun x y hxy ↦ by
  have h := congrArg Subtype.val hxy
  exact Subtype.ext (Prod.ext (hA (congrArg Prod.fst h)) (hB (congrArg Prod.snd h)))

/-- A ring element `s` is regular on `S` if `f` is a nonzerodivisor on `S` and `s` is regular on
the localization away from `f`. -/
theorem isSMulRegular_of_away (f s : S) (hf : ∀ y : S, f * y = 0 → y = 0)
    (hs : IsSMulRegular (Localization.Away f) (algebraMap S (Localization.Away f) s)) :
    IsSMulRegular S s := fun y z hyz ↦ by
  have hyz' : s * (y - z) = 0 := by
    rw [mul_sub, sub_eq_zero]
    exact hyz
  have h0 : algebraMap S (Localization.Away f) (y - z) = 0 := by
    apply hs
    change algebraMap S (Localization.Away f) s * algebraMap S _ (y - z) =
      algebraMap S (Localization.Away f) s * 0
    rw [mul_zero, ← map_mul, hyz', map_zero]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).mp h0
  have hk' : ∀ k : ℕ, f ^ k * (y - z) = 0 → y - z = 0 := fun k ↦ by
    induction k with
    | zero => simp
    | succ k ih => exact fun h ↦ ih (hf _ (by rw [← mul_assoc, ← pow_succ']; exact h))
  exact sub_eq_zero.mp (hk' k hk)

end RegularPieces

namespace AdmissibleLift

open KummerEtale

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  {cov : Admissible.Covering φ ψc} {πL : cov.ι → O} (L : KummerLift cov πL) (M : CuspLift cov)

/-- **Regular elements of a Noetherian chart are regular on the lifted formal model `NF`**: `NF_f`
is flat over `R̂`, `R̂` is flat over `R`, and `f` is a nonzerodivisor on `NF`. -/
theorem isSMulRegular_NFall [IsNoetherianRing R] (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
    {I : Ideal O} (hflat : ∀ j, KummerFactorQuot.KFlat I (L.χ j).toRingHom)
    (hidem : ∀ j, IsIdempotentElem (L.ε j))
    (hf : ∀ j, L.χ j (fA (πL j)) = algebraMap R (FormalPatchLevel.Hat f) f)
    (hcidem : ∀ i, IsIdempotentElem (M.δ i))
    (hreg : ∀ y : FormalPatchLevel.Hat f, algebraMap R _ f * y = 0 → y = 0)
    {g : R} (hg : IsSMulRegular R g) : IsSMulRegular (NFall L M) g := by
  have hHat : IsSMulRegular (FormalPatchLevel.Hat f) (algebraMap R (FormalPatchLevel.Hat f) g) :=
    hg.of_flat
  haveI := flat_NFall L M hO hflat hidem hf hcidem
  have hNf := hHat.of_flat (S := FormalPatchLevel.Nf f (NFall L M))
  have h := RegularPieces.isSMulRegular_of_away (algebraMap R (NFall L M) f)
    (algebraMap R (NFall L M) g) (noTorsion_NFall L M hflat hidem hf hcidem hreg) hNf
  exact (isSMulRegular_algebraMap_iff (A := NFall L M) (M := NFall L M)).mp h

end AdmissibleLift

namespace LevelTower

open KummerEtale AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

include hO in
/-- **Regular elements of the chart are regular on the patched algebra** `G ⊆ P × NF`: the étale
lift `P` is flat over `R n` (`RegularPieces.flat_of_span_pow`), and `NF` by
`AdmissibleLift.isSMulRegular_NFall`. -/
theorem Level.isSMulRegular_G {n : ℕ} (D : Level R cov₀ πL hfe n) {g : R n}
    (hg : IsSMulRegular (R n) g) : IsSMulRegular (D.G hθ) g := by
  haveI := RegularPieces.flat_of_span_pow (f n) D.hfP D.hP.choose D.hP.choose_spec
  exact RegularPieces.isSMulRegular_subalgebra_prod _
    (RegularPieces.isSMulRegular_of_flat hg)
    (isSMulRegular_NFall D.L D.M hO D.hflat D.hidem D.hfχ D.hcidem D.hreg hg)

variable [∀ n, Algebra (R (n + 1)) (R n)]

include hO in
/-- **Regular elements of the chart are regular on the patched algebras of a tower.** -/
theorem Data.isSMulRegular_G (T : Data (θ := θ) R cov₀ πL) {n : ℕ} {g : R n}
    (hg : IsSMulRegular (R n) g) : IsSMulRegular (T.G hθ n) g :=
  Level.isSMulRegular_G hθ hO (T.level n) hg

end LevelTower

end SemistableReduction
