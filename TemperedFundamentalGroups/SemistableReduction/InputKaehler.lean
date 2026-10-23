/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelKaehler
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueInput

/-!
# The differentials of the glued level coverings over the base chart (Blueprint §12.8, M2.5 (f))

* **`ZariskiTwo.kills_glued`**: for the glueing `Ba ×_{Bab} Bb` along a cover `D(a) ∪ D(b)` of
  `Spec R`, a constant killing `Ω[Ba⁄R]` and `Ω[Bb⁄R]` kills the differentials of the glued
  algebra (`KaehlerLocal.kills_of_away₂`);
* **`NodeEtaleGlue.Input.kills_Y`**: the covering `Y n = G n ×_{E n[1/a]} E n` over the base
  chart `B0` (`NodeEtaleGlue.Input.Y`): if `B0 → B n` is surjective, a constant of `B0` whose image
  kills the differentials of the patched node algebra `G n` over the node chart `R n = B n[1/a]`
  kills `Ω[Y n⁄B0]` (the étale pieces `E n` are unramified over `B n`, and
  `Ω[R n⁄B0] = 0`).
-/

universe u

namespace KaehlerLocal

variable (R : Type u) {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The image of `c ω` in a localization `S[1/a]` killed by `c` is killed by a power of `a`. -/
lemma exists_pow_smul_eq_zero {a : S} (S' : Type u) [CommRing S'] [Algebra S S'] [Algebra R S']
    [IsScalarTower R S S'] [IsLocalization.Away a S'] {c : S}
    (hc : Kills R (algebraMap S S' c)) (ω : Ω[S⁄R]) : ∃ k : ℕ, a ^ k • (c • ω) = 0 := by
  have h0 : KaehlerDifferential.map R R S S' (c • ω) = KaehlerDifferential.map R R S S' 0 := by
    rw [map_smul, map_zero, ← algebraMap_smul S' c]
    exact hc _
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers a) h0
  exact ⟨k, by simpa [Submonoid.smul_def] using hk⟩

/-- **Killing the differentials on a cover by two basic opens** `D(a) ∪ D(b)` of `Spec S`. -/
theorem kills_of_away₂ {a b : S} (hab : Ideal.span {a, b} = ⊤) (Sa Sb : Type u) [CommRing Sa]
    [CommRing Sb] [Algebra S Sa] [Algebra S Sb] [Algebra R Sa] [Algebra R Sb]
    [IsScalarTower R S Sa] [IsScalarTower R S Sb] [IsLocalization.Away a Sa]
    [IsLocalization.Away b Sb] {c : S} (ha : Kills R (algebraMap S Sa c))
    (hb : Kills R (algebraMap S Sb c)) : Kills R c := by
  intro ω
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero R (a := a) Sa ha ω
  obtain ⟨l, hl⟩ := exists_pow_smul_eq_zero R (a := b) Sb hb ω
  refine eq_zero_of_pow_smul (a := fun i : Bool ↦ if i then a else b) ?_ fun i ↦ ?_
  · rw [← hab]
    congr 1
    ext x
    simp only [Set.mem_range, Bool.exists_bool, Bool.false_eq_true, ↓reduceIte,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · cases i
    · exact ⟨l, hl⟩
    · exact ⟨k, hk⟩

end KaehlerLocal

namespace ZariskiTwo

variable {R : Type u} [CommRing R] {a b : R}
  {Ba Bb Bab : Type u} [CommRing Ba] [CommRing Bb] [CommRing Bab]
  [Algebra R Ba] [Algebra R Bb] [Algebra R Bab] (ρa : Ba →ₐ[R] Bab) (ρb : Bb →ₐ[R] Bab)

/-- **The differentials of a Zariski glueing**: a constant killing `Ω[Ba⁄R]` and `Ω[Bb⁄R]`
kills the differentials of `Ba ×_{Bab} Bb` (`Ba`, `Bb` its localizations away from `a`, `b`). -/
theorem kills_glued (hab : Ideal.span {a, b} = ⊤)
    (hfst : IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap)
    (hsnd : IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap) {c : R}
    (ha : KaehlerLocal.Kills R (algebraMap R Ba c))
    (hb : KaehlerLocal.Kills R (algebraMap R Bb c)) :
    KaehlerLocal.Kills R (algebraMap R (glued ρa ρb) c) := by
  letI := algebraFst (ρa := ρa) (ρb := ρb)
  letI := algebraSnd (ρa := ρa) (ρb := ρb)
  haveI : IsScalarTower R (glued ρa ρb) Ba :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((fst ρa ρb).commutes r).symm
  haveI : IsScalarTower R (glued ρa ρb) Bb :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((snd ρa ρb).commutes r).symm
  haveI : IsLocalization.Away (algebraMap R (glued ρa ρb) a) Ba := by
    have := isLocalizedModule_iff_isLocalization.mp hfst
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this
  haveI : IsLocalization.Away (algebraMap R (glued ρa ρb) b) Bb := by
    have := isLocalizedModule_iff_isLocalization.mp hsnd
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this
  have hab' : Ideal.span {algebraMap R (glued ρa ρb) a, algebraMap R (glued ρa ρb) b} = ⊤ := by
    have := congrArg (Ideal.map (algebraMap R (glued ρa ρb))) hab
    rwa [Ideal.map_span, Ideal.map_top, Set.image_pair] at this
  refine KaehlerLocal.kills_of_away₂ R hab' Ba Bb ?_ ?_
  · rw [← IsScalarTower.algebraMap_apply]
    exact ha
  · rw [← IsScalarTower.algebraMap_apply]
    exact hb

end ZariskiTwo

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

include hO in
/-- **The differentials of the glued level covering over the base chart**: for `B0 → B n`
surjective, a constant `c ∈ B0` whose image kills `Ω[G n⁄R n]` (the patched node algebra over the
node chart) kills `Ω[Y n⁄B0]`. -/
theorem Input.kills_Y (I : Input θ cov₀ πL)
    (hsurj : ∀ n, Function.Surjective (algebraMap I.B0 (I.B n))) (n : ℕ) {c : I.B0}
    (hG : KaehlerLocal.Kills (I.R n) (algebraMap (I.R n) (I.T.G hθ n)
      (algebraMap (I.B n) (I.R n) (algebraMap I.B0 (I.B n) c)))) :
    KaehlerLocal.Kills I.B0 (algebraMap I.B0 (I.Y hθ n) c) := by
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  haveI : Algebra.FormallyUnramified I.B0 (I.B n) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId I.B0 (I.B n)) (hsurj n)
  haveI : Subsingleton Ω[(I.B n)⁄I.B0] := inferInstance
  have hGa : KaehlerLocal.Kills I.B0 (algebraMap I.B0 (I.T.G hθ n) c) := by
    letI : Algebra I.B0 (I.R n) := ((algebraMap (I.B n) (I.R n)).comp
      (algebraMap I.B0 (I.B n))).toAlgebra
    haveI : IsScalarTower I.B0 (I.B n) (I.R n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    haveI : IsScalarTower I.B0 (I.R n) (I.T.G hθ n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    haveI : Algebra.FormallyUnramified (I.B n) (I.R n) :=
      Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers (I.a n))
    haveI : Algebra.FormallyUnramified I.B0 (I.R n) :=
      Algebra.FormallyUnramified.comp I.B0 (I.B n) (I.R n)
    exact KaehlerLocal.kills_of_base I.B0 (I.R n) hG
  have hEb : KaehlerLocal.Kills I.B0 (algebraMap I.B0 (I.E n) c) := by
    haveI : IsScalarTower I.B0 (I.B n) (I.E n) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact KaehlerLocal.kills_of_base I.B0 (I.B n) fun _ ↦ Subsingleton.elim _ _
  exact ZariskiTwo.kills_glued _ _ I.hab
    (locFst I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv I.hJB
      I.B0 (fun _ ↦ rfl) n)
    (locSnd I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv
      I.hbb I.hJB I.B0 (fun _ ↦ rfl) n) hGa hEb

end NodeEtaleGlue

end

end SemistableReduction
