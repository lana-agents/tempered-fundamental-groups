/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleNilLoc
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlap
import TemperedFundamentalGroups.SemistableReduction.AwayDvd
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoLoc

/-!
# An étale algebra over an overlap is the localized glueing (Blueprint §12.8, M2.3 (f))

Setting of `EtaleOverlap` and `OverlapFibre` over a level chart `R` (`J` nilpotent): the node chart
`A = R[1/a]`, the patched algebra `G` with `fst : G → P` (away from `f`), the étale lift `P` over
`A` with `σP : P/JP ≃ Cc[1/f]`, the étale piece `E` over `D(b)` with `σE : E/JE ≃ C1[1/b]`, the
overlap `Bab = E[1/a]` and `κ : P → Bab` (`EtaleOverlap.κ`), `ρa = κ ∘ fst`. The glueing is over a
base `B0 → R` (`a`, `b` images of `a0`, `b0 ∈ B0` with `(a0, b0) = 1`).

For `g ∈ B0` with `f ∣ gᵏ` in `A` (the overlap `D(g)` misses the nodes) and localizations
`Gg`, `Pg`, `Eg`, `Babg` of the pieces away from `g`:

* `EtaleOverlap.γP`, `γE`, `γB`: the special fibres of `Pg`, `Eg`, `Babg` as `C1`-algebras;
  `isLocalization_γP` (away from `g a`), `isLocalization_γE` (away from `g b`);
* **`EtaleOverlap.glueEquiv`**: a formally étale `R`-algebra `M` with `γM : C1 → M/JM` a
  localization away from `g` (`M/JM = C1[1/g]`) is the glueing `Gg ×_{Babg} Eg` (with any
  `B0`-algebra maps `ρa' : Gg → Babg`, `ρb' : Eg → Babg` extending `ρa` and `E → Bab`):
  `M ≃ₐ[B0] ZariskiTwo.glued ρa' ρb'`
  (`EtaleNil.liftLoc`, `ZariskiTwo.bijective_lift`).

This identifies the étale piece of a covering over `D(x₀) ∩ D(c₀) ⊆ V₀` with the restriction of
the covering over `V₁` (Tate case: `g = h(1 + h)`, `M = E0[1/h₀]`).
-/

universe u

namespace SemistableReduction

/-! ### Localizations along ring homomorphisms -/

namespace RingHomAway

variable {C S T : Type u} [CommRing C] [CommRing S] [CommRing T]

/-- A localization of algebras as a localization along the ring homomorphism. -/
theorem of_algebra [Algebra C S] (x : C) [h : IsLocalization.Away x S] :
    letI := (algebraMap C S).toAlgebra; IsLocalization.Away x S := by
  letI := (algebraMap C S).toAlgebra
  exact ⟨h.toIsLocalizationMap⟩

/-- Composition of localizations. -/
theorem comp (f1 : C →+* S) (f2 : S →+* T) (x y : C)
    (h1 : letI := f1.toAlgebra; IsLocalization.Away x S)
    (h2 : letI := f2.toAlgebra; IsLocalization.Away (f1 y) T) :
    letI := (f2.comp f1).toAlgebra; IsLocalization.Away (x * y) T := by
  letI := f1.toAlgebra
  letI := f2.toAlgebra
  letI := (f2.comp f1).toAlgebra
  haveI : IsScalarTower C S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact IsLocalization.Away.mul' S T x y

/-- The second step of a composite localization. -/
theorem of_comp (f1 : C →+* S) (f2 : S →+* T) (x y : C)
    (h1 : letI := f1.toAlgebra; IsLocalization.Away x S)
    (h : letI := (f2.comp f1).toAlgebra; IsLocalization.Away (x * y) T) :
    letI := f2.toAlgebra; IsLocalization.Away (f1 y) T := by
  letI := f1.toAlgebra
  letI := f2.toAlgebra
  letI := (f2.comp f1).toAlgebra
  haveI : IsScalarTower C S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact OverlapFibre.away_of_mul (R := C) (S := S) (T := T) x y

/-- A localization followed by an isomorphism. -/
theorem equiv (f1 : C →+* S) (e : S ≃+* T) (x : C)
    (h1 : letI := f1.toAlgebra; IsLocalization.Away x S) :
    letI := ((e : S →+* T).comp f1).toAlgebra; IsLocalization.Away x T := by
  letI := f1.toAlgebra
  letI := ((e : S →+* T).comp f1).toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers x)
    { e with commutes' := fun _ ↦ rfl }

/-- `C[1/(x y)] = C[1/y]` if `x ∣ yᵏ`. -/
theorem of_dvd (f1 : C →+* S) (x y : C) (k : ℕ) (hd : x ∣ y ^ k)
    (h : letI := f1.toAlgebra; IsLocalization.Away (x * y) S) :
    letI := f1.toAlgebra; IsLocalization.Away y S := by
  letI := f1.toAlgebra
  exact AwayDvd.away_of_dvd x y k hd

/-- Rewriting the element. -/
theorem congr (f1 : C →+* S) {x y : C} (hxy : x = y)
    (h : letI := f1.toAlgebra; IsLocalization.Away x S) :
    letI := f1.toAlgebra; IsLocalization.Away y S := hxy ▸ h

/-- Rewriting the map. -/
theorem congr_map {f1 f2 : C →+* S} (hf : f1 = f2) (x : C)
    (h : letI := f1.toAlgebra; IsLocalization.Away x S) :
    letI := f2.toAlgebra; IsLocalization.Away x S := hf ▸ h

end RingHomAway

namespace EtaleOverlap

noncomputable section

open EtaleNil

variable {R : Type u} [CommRing R] (J : Ideal R) {m : ℕ} (hJ : J ^ m = ⊥) (a b : R)
  {A : Type u} [CommRing A] [Algebra R A] [IsLocalization.Away a A]
  {P : Type u} [CommRing P] [Algebra A P] [Algebra R P] [IsScalarTower R A P]
  [Algebra.FormallyEtale A P]
  {E : Type u} [CommRing E] [Algebra R E]
  {C1 : Type u} [CommRing C1] [Algebra R C1]
  {Cc : Type u} [CommRing Cc] [Algebra A Cc] [Algebra R Cc] [IsScalarTower R A Cc]
  (ι : C1 →ₐ[R] Cc) (f : A)
  (σP : (P ⧸ EtaleNil.JB J P) ≃ₐ[R] Localization.Away (algebraMap A Cc f))
  {Lb : Type u} [CommRing Lb] [Algebra C1 Lb] [Algebra R Lb] [IsScalarTower R C1 Lb]
  (σE : (E ⧸ EtaleNil.JB J E) ≃ₐ[R] Lb)
  (hι : letI := (ι : C1 →+* Cc).toAlgebra; IsLocalization.Away (algebraMap R C1 a) Cc)
  (hb : IsUnit (algebraMap R E b)) {k : ℕ} (hdiv : f ∣ algebraMap R A b ^ k)
  (gR : R)
  {Pg : Type u} [CommRing Pg] [Algebra P Pg] [Algebra R Pg] [IsScalarTower R P Pg]
  [IsLocalization.Away (algebraMap R P gR) Pg]
  {Eg : Type u} [CommRing Eg] [Algebra E Eg] [Algebra R Eg] [IsScalarTower R E Eg]
  [IsLocalization.Away (algebraMap R E gR) Eg]
  {Babg : Type u} [CommRing Babg] [Algebra (Bab a E) Babg] [Algebra R Babg]
  [IsScalarTower R (Bab a E) Babg] [IsLocalization.Away (algebraMap R (Bab a E) gR) Babg]

/-! ### The special fibres of the localized pieces -/

/-- `C1 → Eg/J`: `C1 → C1[1/b] ≃ E/JE → Eg/J`. -/
def γE : C1 →ₐ[R] Eg ⧸ JB J Eg :=
  (red J (IsScalarTower.toAlgHom R E Eg)).comp
    (σE.symm.toAlgHom.comp (IsScalarTower.toAlgHom R C1 Lb))

/-- `C1 → Pg/J`: `C1 → Cc → Cc[1/f] ≃ P/JP → Pg/J`. -/
def γP : C1 →ₐ[R] Pg ⧸ JB J Pg :=
  (red J (IsScalarTower.toAlgHom R P Pg)).comp (σP.symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom R Cc (Localization.Away (algebraMap A Cc f))).comp ι))

/-- `C1 → Babg/J`: `OverlapFibre.γ1` followed by the localization. -/
def γB : C1 →ₐ[R] Babg ⧸ JB J Babg :=
  (red J (IsScalarTower.toAlgHom R (Bab a E) Babg)).comp (OverlapFibre.γ1 J a C1 σE)

variable [IsLocalization.Away (algebraMap R C1 b) Lb]

/-- **`Eg/J = C1[1/(g b)]`.** -/
theorem isLocalization_γE :
    letI : Algebra C1 (Eg ⧸ JB J Eg) := (γE J σE : C1 →ₐ[R] Eg ⧸ JB J Eg).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R C1 gR * algebraMap R C1 b) (Eg ⧸ JB J Eg) := by
  rw [mul_comm]
  -- `C1 → E/JE` is a localization away from `b`
  have h1 := RingHomAway.equiv (algebraMap C1 Lb) σE.symm.toRingEquiv (algebraMap R C1 b)
    (RingHomAway.of_algebra _)
  -- `E/JE → Eg/J` is a localization away from `g`
  have h2 : letI := (red J (IsScalarTower.toAlgHom R E Eg)).toRingHom.toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (JB J E) (algebraMap R E gR)) (Eg ⧸ JB J Eg) :=
    isLocalization_red J (algebraMap R E gR)
  have e : (σE.symm.toRingEquiv.toRingHom.comp (algebraMap C1 Lb)) (algebraMap R C1 gR) =
      Ideal.Quotient.mk (JB J E) (algebraMap R E gR) := by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact σE.symm.commutes gR
  rw [← e] at h2
  exact RingHomAway.comp _ _ _ _ h1 h2

omit [IsLocalization.Away a A] [Algebra A P] [IsScalarTower R A P] [Algebra.FormallyEtale A P] in
include hι in
/-- **`Pg/J = C1[1/(g a)]`** (if `f ∣ gᵏ`: `D(g)` misses the nodes). -/
theorem isLocalization_γP {k' : ℕ} (hfg : f ∣ algebraMap R A gR ^ k') :
    letI : Algebra C1 (Pg ⧸ JB J Pg) :=
      (γP J ι f σP : C1 →ₐ[R] Pg ⧸ JB J Pg).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R C1 gR * algebraMap R C1 a) (Pg ⧸ JB J Pg) := by
  rw [mul_comm]
  set Lf := Localization.Away (algebraMap A Cc f)
  -- `Cc → P/JP` is a localization away from `f`
  have h1 := RingHomAway.equiv (algebraMap Cc Lf) σP.symm.toRingEquiv (algebraMap A Cc f)
    (RingHomAway.of_algebra _)
  -- `P/JP → Pg/J` is a localization away from `g`
  have h2 : letI := (red J (IsScalarTower.toAlgHom R P Pg)).toRingHom.toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (JB J P) (algebraMap R P gR)) (Pg ⧸ JB J Pg) :=
    isLocalization_red J (algebraMap R P gR)
  have e : (σP.symm.toRingEquiv.toRingHom.comp (algebraMap Cc Lf)) (algebraMap R Cc gR) =
      Ideal.Quotient.mk (JB J P) (algebraMap R P gR) := by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact σP.symm.commutes gR
  rw [← e] at h2
  have h3 := RingHomAway.comp _ _ _ _ h1 h2
  -- `f ∣ gᵏ` in `Cc`
  have hd : algebraMap A Cc f ∣ algebraMap R Cc gR ^ k' := by
    rw [IsScalarTower.algebraMap_apply R A Cc, ← map_pow]
    exact map_dvd _ hfg
  have h4 := RingHomAway.of_dvd _ _ _ k' hd h3
  -- compose with `ι : C1 → Cc` (away from `a`)
  have e2 : (ι : C1 →+* Cc) (algebraMap R C1 gR) = algebraMap R Cc gR := ι.commutes gR
  rw [← e2] at h4
  exact RingHomAway.comp (ι : C1 →+* Cc) ((red J (IsScalarTower.toAlgHom R P Pg)).toRingHom.comp
    (σP.symm.toRingEquiv.toRingHom.comp (algebraMap Cc Lf))) _ _ hι h4

/-! ### The overlap map localized at `g` -/

/-- The special-fibre map of the overlap (`OverlapFibre.χ`). -/
abbrev χo := OverlapFibre.χ J a b ι f σP σE hι hb hdiv

/-- **`κ` localized at `g`**: `Pg → Babg`. -/
def κg : Pg →ₐ[R] Babg :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap R P gR))
    (f := (IsScalarTower.toAlgHom R (Bab a E) Babg).comp
      (κ J hJ a A (χo J a b ι f σP σE hι hb hdiv)))
    (fun y ↦ by
      obtain ⟨_, n, rfl⟩ := y
      simp only [map_pow, AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply R (Bab a E) Babg]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Babg)
        (algebraMap R (Bab a E) gR)).pow n)

omit [IsLocalization.Away ((algebraMap R C1) b) Lb] in
lemma κg_algebraMap (p : P) : κg J hJ a b ι f σP σE hι hb hdiv gR (Pg := Pg) (Babg := Babg)
    (algebraMap P Pg p) =
      algebraMap (Bab a E) Babg (κ J hJ a A (χo J a b ι f σP σE hι hb hdiv) p) :=
  IsLocalization.lift_eq _ _

/-- The localization map `E → Bab` localized at `g`: `Eg → Babg`. -/
def ρEg : Eg →ₐ[R] Babg :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap R E gR))
    (f := (IsScalarTower.toAlgHom R (Bab a E) Babg).comp (IsScalarTower.toAlgHom R E (Bab a E)))
    (fun y ↦ by
      obtain ⟨_, n, rfl⟩ := y
      simp only [map_pow, AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply R (Bab a E) Babg]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Babg)
        (algebraMap R (Bab a E) gR)).pow n)

lemma ρEg_algebraMap (x : E) : ρEg a gR (E := E) (Eg := Eg) (Babg := Babg) (algebraMap E Eg x) =
    algebraMap (Bab a E) Babg (algebraMap E (Bab a E) x) :=
  IsLocalization.lift_eq _ _

omit [IsLocalization.Away ((algebraMap R C1) b) Lb] in
/-- **Compatibility of the special fibres with `κg`.** -/
lemma red_κg_γP (c : C1) : red J (κg J hJ a b ι f σP σE hι hb hdiv gR (Pg := Pg) (Babg := Babg))
    (γP J ι f σP c) = γB J a σE c := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (σP.symm (algebraMap Cc _ (ι c)))
  have h1 : γP J ι f σP (Pg := Pg) c = Ideal.Quotient.mk _ (algebraMap P Pg y) := by
    change red J (IsScalarTower.toAlgHom R P Pg) (σP.symm (algebraMap Cc _ (ι c))) = _
    rw [← hy]
    rfl
  rw [h1, red_mk, κg_algebraMap]
  change _ = red J (IsScalarTower.toAlgHom R (Bab a E) Babg) (OverlapFibre.γ1 J a C1 σE c)
  rw [← OverlapFibre.γc_ι J a ι σE hι, ← OverlapFibre.μ_algebraMap J a b ι f σE hι hb hdiv]
  have h2 : OverlapFibre.μ J a b ι f σE hι hb hdiv (algebraMap Cc _ (ι c)) =
      Ideal.Quotient.mk _ (κ J hJ a A (χo J a b ι f σP σE hι hb hdiv) y) := by
    rw [← red_mk, red_κ, hy]
    change _ = OverlapFibre.μ J a b ι f σE hι hb hdiv (σP (σP.symm _))
    rw [AlgEquiv.apply_symm_apply]
  rw [h2]
  rfl

/-- **Compatibility of the special fibres with `ρEg`.** -/
lemma red_ρEg_γE (c : C1) : red J (ρEg a gR (E := E) (Eg := Eg) (Babg := Babg)) (γE J σE c) =
    γB J a σE c := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (σE.symm (algebraMap C1 Lb c))
  have h1 : γE J σE (Eg := Eg) c = Ideal.Quotient.mk _ (algebraMap E Eg y) := by
    change red J (IsScalarTower.toAlgHom R E Eg) (σE.symm (algebraMap C1 Lb c)) = _
    rw [← hy]
    rfl
  rw [h1, red_mk, ρEg_algebraMap]
  change _ = red J (IsScalarTower.toAlgHom R (Bab a E) Babg)
    (OverlapFibre.redE J a (σE.symm (algebraMap C1 Lb c)))
  rw [← hy]
  rfl

variable [Algebra.FormallyEtale R E]

/-! ### Formal étaleness of the localized pieces -/

variable (A) in
include a A P gR in
lemma formallyEtale_Pg : Algebra.FormallyEtale R Pg := by
  haveI := formallyEtale_P a A (P := P)
  haveI : Algebra.FormallyEtale P Pg :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (algebraMap R P gR))
  exact Algebra.FormallyEtale.comp R P Pg

include E gR in
lemma formallyEtale_Eg : Algebra.FormallyEtale R Eg := by
  haveI : Algebra.FormallyEtale E Eg :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (algebraMap R E gR))
  exact Algebra.FormallyEtale.comp R E Eg

/-! ### The comparison -/

variable {B0 : Type u} [CommRing B0] [Algebra B0 R] (a0 b0 : B0)
  (hab : Ideal.span {a0, b0} = ⊤)
  (ha0 : algebraMap B0 R a0 = a) (hb0 : algebraMap B0 R b0 = b)
  {G : Type u} [CommRing G] [Algebra A G] [Algebra R G] [IsScalarTower R A G]
  (fst : G →ₐ[A] P)
  (hfst : letI := fst.toRingHom.toAlgebra; IsLocalization.Away (algebraMap A G f) P)
  {k' : ℕ} (hfg : f ∣ algebraMap R A gR ^ k')
  {Gg : Type u} [CommRing Gg] [Algebra G Gg] [Algebra R Gg] [IsScalarTower R G Gg]
  [IsLocalization.Away (algebraMap R G gR) Gg]

/-- `G → P → Pg`. -/
def fstg : G →ₐ[R] Pg := (IsScalarTower.toAlgHom R P Pg).comp (fst.restrictScalars R)

omit [Algebra.FormallyEtale A P] in
include hfst hfg in
/-- `Pg = G[1/g]` (`f ∣ gᵏ`). -/
lemma isLocalization_fstg :
    letI := (fstg (R := R) fst (Pg := Pg)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R G gR) Pg := by
  have h2 : letI := (algebraMap P Pg).toAlgebra
      IsLocalization.Away ((fst : G →+* P) (algebraMap R G gR)) Pg := by
    have e : (fst : G →+* P) (algebraMap R G gR) = algebraMap R P gR := by
      rw [RingHom.coe_coe, IsScalarTower.algebraMap_apply R A G, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply]
    rw [e]
    exact RingHomAway.of_algebra _
  have h3 := RingHomAway.comp (fst : G →+* P) (algebraMap P Pg) _ _ hfst h2
  have hd : algebraMap A G f ∣ algebraMap R G gR ^ k' := by
    rw [IsScalarTower.algebraMap_apply R A G, ← map_pow]
    exact map_dvd _ hfg
  exact RingHomAway.of_dvd _ _ _ k' hd h3

/-- **`Gg ≃ Pg`**: the patched algebra and the étale lift agree away from the nodes. -/
def eG : Gg ≃ₐ[R] Pg :=
  letI := (fstg (R := R) fst (Pg := Pg)).toRingHom.toAlgebra
  haveI := isLocalization_fstg f gR fst hfst hfg (Pg := Pg)
  { IsLocalization.algEquiv (Submonoid.powers (algebraMap R G gR)) Gg Pg with
    commutes' := fun r ↦ by
      letI := (fstg (R := R) fst (Pg := Pg)).toRingHom.toAlgebra
      haveI := isLocalization_fstg f gR fst hfst hfg (Pg := Pg)
      change IsLocalization.algEquiv (Submonoid.powers (algebraMap R G gR)) Gg Pg
        (algebraMap R Gg r) = _
      rw [IsScalarTower.algebraMap_apply R G Gg, AlgEquiv.commutes]
      exact (fstg (R := R) fst (Pg := Pg)).commutes r }

omit [Algebra.FormallyEtale A P] in
lemma eG_algebraMap (x : G) :
    eG f gR fst hfst hfg (Pg := Pg) (Gg := Gg) (algebraMap G Gg x) =
      fstg (R := R) fst (Pg := Pg) x := by
  letI := (fstg (R := R) fst (Pg := Pg)).toRingHom.toAlgebra
  haveI := isLocalization_fstg f gR fst hfst hfg (Pg := Pg)
  exact (IsLocalization.algEquiv (Submonoid.powers (algebraMap R G gR)) Gg Pg).commutes x

omit [IsLocalization.Away ((algebraMap R C1) b) Lb] [Algebra.FormallyEtale R E] [Algebra B0 R] in
/-- **The overlap map of the localized glueing is `κg` on `Pg`.** -/
lemma ρa'_eq [Algebra B0 Gg] [Algebra B0 Babg] (ρa' : Gg →ₐ[B0] Babg)
    (hρa : ∀ x : G, ρa' (algebraMap G Gg x) =
      algebraMap (Bab a E) Babg (ρa J hJ a (χo J a b ι f σP σE hι hb hdiv) fst x))
    (y : Gg) : ρa' y = κg J hJ a b ι f σP σE hι hb hdiv gR (Pg := Pg) (Babg := Babg)
      (eG f gR fst hfst hfg (Pg := Pg) (Gg := Gg) y) := by
  have : (ρa' : Gg →+* Babg) = (κg J hJ a b ι f σP σE hι hb hdiv gR (Pg := Pg)
      (Babg := Babg) : Pg →+* Babg).comp (eG f gR fst hfst hfg (Pg := Pg) (Gg := Gg) :
        Gg →+* Pg) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R G gR))
      (RingHom.ext fun x ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [hρa, eG_algebraMap]
    change _ = κg J hJ a b ι f σP σE hι hb hdiv gR (algebraMap P Pg (fst x))
    rw [κg_algebraMap]
    rfl
  exact RingHom.congr_fun this y

omit [Algebra.FormallyEtale R E] [Algebra B0 R] in
/-- **The overlap map of `Eg` is `ρEg`.** -/
lemma ρb'_eq [Algebra B0 Eg] [Algebra B0 Babg] (ρb' : Eg →ₐ[B0] Babg)
    (hρb : ∀ x : E, ρb' (algebraMap E Eg x) =
      algebraMap (Bab a E) Babg (algebraMap E (Bab a E) x))
    (y : Eg) : ρb' y = ρEg a gR (E := E) (Eg := Eg) (Babg := Babg) y := by
  have : (ρb' : Eg →+* Babg) = (ρEg a gR (E := E) (Eg := Eg) (Babg := Babg) : Eg →+* Babg) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R E gR))
      (RingHom.ext fun x ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [hρb, ρEg_algebraMap]
  exact RingHom.congr_fun this y

variable {M : Type u} [CommRing M] [Algebra R M] [Algebra.FormallyEtale R M]
  (γM : C1 →ₐ[R] M ⧸ JB J M)
  (hM : letI := γM.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R C1 gR) (M ⧸ JB J M))

variable (A) in
/-- **The étale lift `M → Pg`.** -/
def φP : M →ₐ[R] Pg :=
  liftLoc J hJ γM (γP J ι f σP (Pg := Pg)) (algebraMap R C1 gR) a
    hM (isLocalization_γP J a ι f σP hι gR (Pg := Pg) hfg)

/-- **The étale lift `M → Eg`.** -/
def φE : M →ₐ[R] Eg :=
  liftLoc J hJ γM (γE J σE (Eg := Eg)) (algebraMap R C1 gR) b
    hM (isLocalization_γE J b σE gR (Eg := Eg))

/-- **`M → Pg` is a localization away from `a`.** -/
theorem isLocalization_φP :
    letI := (φP J hJ a A ι f σP hι gR hfg γM hM (Pg := Pg)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R M a) Pg :=
  haveI := formallyEtale_Pg a A gR (P := P) (Pg := Pg)
  isLocalization_liftLoc J hJ γM (γP J ι f σP (Pg := Pg)) (algebraMap R C1 gR) a
    hM (isLocalization_γP J a ι f σP hι gR (Pg := Pg) hfg)
    (by
      rw [IsScalarTower.algebraMap_apply R P Pg, IsScalarTower.algebraMap_apply R A P]
      exact ((IsLocalization.Away.algebraMap_isUnit a).map _).map _)

include hb in
/-- **`M → Eg` is a localization away from `b`.** -/
theorem isLocalization_φE :
    letI := (φE J hJ b σE gR γM hM (Eg := Eg)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R M b) Eg :=
  haveI := formallyEtale_Eg gR (E := E) (Eg := Eg)
  isLocalization_liftLoc J hJ γM (γE J σE (Eg := Eg)) (algebraMap R C1 gR) b
    hM (isLocalization_γE J b σE gR (Eg := Eg))
    (by rw [IsScalarTower.algebraMap_apply R E Eg]; exact hb.map _)

omit [Algebra.FormallyEtale R E] in
include hb hdiv in
/-- **The two lifts agree on the overlap**: `κg ∘ φP = ρEg ∘ φE`. -/
theorem κg_φP : (κg J hJ a b ι f σP σE hι hb hdiv gR (Pg := Pg) (Babg := Babg)).comp
    (φP J hJ a A ι f σP hι gR hfg γM hM (Pg := Pg)) =
      (ρEg a gR (E := E) (Eg := Eg) (Babg := Babg)).comp (φE J hJ b σE gR γM hM (Eg := Eg)) := by
  refine ext_of_comp J hJ γM (algebraMap R C1 gR) hM
    fun c ↦ ?_
  rw [red_comp, red_comp, AlgHom.comp_apply, AlgHom.comp_apply]
  unfold φP φE
  rw [red_liftLoc_comp, red_liftLoc_comp, red_κg_γP, red_ρEg_γE]
/-! ### The glueing over `B0` -/

variable [Algebra B0 M] [IsScalarTower B0 R M] [Algebra B0 Gg] [IsScalarTower B0 R Gg]
  [Algebra B0 Eg] [IsScalarTower B0 R Eg] [Algebra B0 Babg]
  (ρa' : Gg →ₐ[B0] Babg) (ρb' : Eg →ₐ[B0] Babg)
  (hρa : ∀ x : G, ρa' (algebraMap G Gg x) =
    algebraMap (Bab a E) Babg (ρa J hJ a (χo J a b ι f σP σE hι hb hdiv) fst x))
  (hρb : ∀ x : E, ρb' (algebraMap E Eg x) =
    algebraMap (Bab a E) Babg (algebraMap E (Bab a E) x))

/-- The map `M → Gg` over `B0`. -/
def φa : M →ₐ[B0] Gg :=
  (((eG f gR fst hfst hfg (Pg := Pg) (Gg := Gg)).symm.toAlgHom).comp
    (φP J hJ a A ι f σP hι gR hfg γM hM (Pg := Pg))).restrictScalars B0

/-- The map `M → Eg` over `B0`. -/
def φb : M →ₐ[B0] Eg := (φE J hJ b σE gR γM hM (Eg := Eg)).restrictScalars B0

include ha0 in
theorem isLocalizedModule_φa : IsLocalizedModule (Submonoid.powers a0)
    (φa J hJ a ι f σP hι gR fst hfst hfg γM hM (Pg := Pg) (Gg := Gg)).toLinearMap := by
  refine ZariskiTwo.isLocalizedModule_of_away a0 _ ?_
  have h := RingHomAway.equiv (φP J hJ a A ι f σP hι gR hfg γM hM (Pg := Pg) : M →+* Pg)
    (eG f gR fst hfst hfg (Pg := Pg) (Gg := Gg)).symm.toRingEquiv _
    (isLocalization_φP J hJ a ι f σP hι gR hfg γM hM (Pg := Pg))
  have e : algebraMap R M a = algebraMap B0 M a0 := by
    rw [← ha0, ← IsScalarTower.algebraMap_apply]
  exact RingHomAway.congr _ e h

include hb0 hb in
theorem isLocalizedModule_φb : IsLocalizedModule (Submonoid.powers b0)
    (φb J hJ b σE gR γM hM (Eg := Eg) (B0 := B0)).toLinearMap := by
  refine ZariskiTwo.isLocalizedModule_of_away b0 _ ?_
  have e : algebraMap R M b = algebraMap B0 M b0 := by
    rw [← hb0, ← IsScalarTower.algebraMap_apply]
  exact RingHomAway.congr _ e (isLocalization_φE J hJ b σE hb gR γM hM (Eg := Eg))

omit [Algebra.FormallyEtale R E] in
include hρa hρb in
/-- **The maps to the pieces are compatible on the overlap.** -/
theorem φa_φb (x : M) :
    ρa' (φa J hJ a ι f σP hι gR fst hfst hfg γM hM (Pg := Pg) (Gg := Gg) (B0 := B0) x) =
    ρb' (φb J hJ b σE gR γM hM (Eg := Eg) (B0 := B0) x) := by
  change ρa' ((eG f gR fst hfst hfg (Pg := Pg) (Gg := Gg)).symm
    (φP J hJ a A ι f σP hι gR hfg γM hM (Pg := Pg) x)) = ρb' (φE J hJ b σE gR γM hM (Eg := Eg) x)
  rw [ρa'_eq J hJ a b ι f σP σE hι hb hdiv gR fst hfst hfg (Pg := Pg) ρa' hρa,
    AlgEquiv.apply_symm_apply,
    ρb'_eq a gR ρb' hρb]
  exact AlgHom.congr_fun (κg_φP J hJ a b ι f σP σE hι hb hdiv gR hfg γM hM) x

variable [IsLocalizedModule (Submonoid.powers a0) (ZariskiTwo.fst ρa' ρb').toLinearMap]
  [IsLocalizedModule (Submonoid.powers b0) (ZariskiTwo.snd ρa' ρb').toLinearMap]

/-- **An étale `M` over the overlap with `M/JM = C1[1/g]` is the localized glueing**
`Gg ×_{Babg} Eg` (Stacks, Lemma 10.24.1, Tag 00EK, via `ZariskiTwo.bijective_lift`). -/
def glueEquiv : M ≃ₐ[B0] ZariskiTwo.glued ρa' ρb' :=
  haveI := isLocalizedModule_φa J hJ a ι f σP hι gR a0 ha0 fst hfst hfg γM hM (Pg := Pg) (Gg := Gg)
  haveI := isLocalizedModule_φb J hJ b σE hb gR b0 hb0 γM hM (Eg := Eg)
  ZariskiTwo.liftEquiv a0 b0 hab _ _ (φa_φb J hJ a b ι f σP σE hι hb hdiv gR fst hfst hfg γM hM
    (Pg := Pg) ρa' ρb' hρa hρb)

end

end EtaleOverlap

end SemistableReduction
