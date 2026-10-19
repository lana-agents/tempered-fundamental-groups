/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoMap
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlapFibre

/-!
# Localizations of two-piece glueings (Blueprint §12.8, M2.3 (f))

For a glueing `glued ρa ρb = Ba ×_{Bab} Bb` over `R` (pieces on `D(a)`, `D(b)`, `a, b`
generating the unit ideal) and `c ∈ R`:

* `ZariskiTwo.isLocalizedModule_of_away`, `ZariskiTwo.away_of_isLocalizedModule`: the two forms
  of "`φ : M → B` is a localization away from `c`" (`R`-linear / as an algebra over `M`);
* `ZariskiTwo.pieceL`, `isLocalizedModule_pieceL`: `M → X` away from `d` and `X → X'` away from
  `c` give `M[1/c] → X'` away from `d`;
* **`ZariskiTwo.isLocalization_map`**: if the maps of pieces `sa : Ba → Ba'`, `sb : Bb → Bb'`
  are localizations away from `c`, then so is the induced map of glued algebras
  `glued ρa ρb → glued ρa' ρb'` (both glueings with pieces on `D(a)`, `D(b)`; localization
  commutes with the glueing; via
  `ZariskiTwo.bijective_lift` for `(glued ρa ρb)[1/c]`);
* **`ZariskiTwo.isLocalization_mapL`**: the glueing of the localized pieces `ρaL c`, `ρbL c`
  (`Ba[1/c] → Bab[1/c] ← Bb[1/c]`) is `(glued ρa ρb)[1/c]`, with pieces on `D(a)`, `D(b)`
  (`isLocalizedModule_fstL`, `isLocalizedModule_sndL`).
-/

universe u

namespace ZariskiTwo

variable {R : Type u} [CommRing R]

section Conv

variable {M B : Type u} [CommRing M] [Algebra R M] [CommRing B] [Algebra R B] (c : R)
  (φ : M →ₐ[R] B)

/-- A localization of algebras away from `c` is a localization of modules. -/
theorem isLocalizedModule_of_away
    (h : letI := φ.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R M c) B) :
    IsLocalizedModule (Submonoid.powers c) φ.toLinearMap := by
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R M B := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid M (Submonoid.powers c)) B := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact h
  exact isLocalizedModule_iff_isLocalization.mpr this

/-- A localization of modules away from `c` is a localization of algebras. -/
theorem away_of_isLocalizedModule [h : IsLocalizedModule (Submonoid.powers c) φ.toLinearMap] :
    letI := φ.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R M c) B := by
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R M B := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have h' := (isLocalizedModule_iff_isLocalization (S := Submonoid.powers c) (A := M)
    (Aₛ := B)).mp h
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h'
  exact h'

end Conv

variable (a b : R)
  {Ba Bb Bab : Type u} [CommRing Ba] [CommRing Bb] [CommRing Bab]
  [Algebra R Ba] [Algebra R Bb] [Algebra R Bab]
  {ρa : Ba →ₐ[R] Bab} {ρb : Bb →ₐ[R] Bab}
  {Ba' Bb' Bab' : Type u} [CommRing Ba'] [CommRing Bb'] [CommRing Bab']
  [Algebra R Ba'] [Algebra R Bb'] [Algebra R Bab']
  {ρa' : Ba' →ₐ[R] Bab'} {ρb' : Bb' →ₐ[R] Bab'}
  (sa : Ba →ₐ[R] Ba') (sb : Bb →ₐ[R] Bb') (sab : Bab →ₐ[R] Bab')
  (hsa : ∀ x, ρa' (sa x) = sab (ρa x)) (hsb : ∀ x, ρb' (sb x) = sab (ρb x)) (c : R)

section Piece

variable {M X X' : Type u} [CommRing M] [CommRing X] [CommRing X'] [Algebra R M] [Algebra R X]
  [Algebra R X'] (d : R) (p : M →ₐ[R] X) (s : X →ₐ[R] X')
  (hs : letI := s.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R X c) X')

include hs in
lemma isUnit_c : IsUnit ((s.comp p) (algebraMap R M c)) := by
  rw [AlgHom.commutes]
  letI := s.toRingHom.toAlgebra
  haveI := hs
  have h := IsLocalization.Away.algebraMap_isUnit (S := X') (algebraMap R X c)
  rwa [show algebraMap X X' (algebraMap R X c) = algebraMap R X' c from s.commutes c] at h

/-- The extension `M[1/c] → X'` of `s ∘ p`. -/
noncomputable def pieceL : Localization.Away (algebraMap R M c) →ₐ[R] X' :=
  { IsLocalization.Away.lift (algebraMap R M c) (g := ((s.comp p : M →ₐ[R] X') : M →+* X'))
      (isUnit_c c p s hs) with
    commutes' := fun r ↦ by
      change IsLocalization.Away.lift _ _ (algebraMap M _ (algebraMap R _ r)) = _
      rw [IsLocalization.Away.lift_eq]
      exact (s.comp p).commutes r }

lemma pieceL_algebraMap (x : M) : pieceL c p s hs (algebraMap _ _ x) = s (p x) :=
  IsLocalization.Away.lift_eq _ (isUnit_c c p s hs) x

include hs in
/-- If `p` is a localization away from `d` and `s` away from `c`, the extension
`M[1/c] → X'` is a localization away from `d`. -/
theorem isLocalizedModule_pieceL [IsLocalizedModule (Submonoid.powers d) p.toLinearMap] :
    IsLocalizedModule (Submonoid.powers d) (pieceL c p s hs).toLinearMap := by
  letI : Algebra M X := p.toRingHom.toAlgebra
  haveI : IsLocalization.Away (algebraMap R M d) X := away_of_isLocalizedModule d p
  letI : Algebra X X' := s.toRingHom.toAlgebra
  letI : Algebra M X' := (s.comp p).toRingHom.toAlgebra
  haveI : IsScalarTower M X X' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsLocalization.Away (algebraMap M X (algebraMap R M c)) X' := by
    rw [show algebraMap M X (algebraMap R M c) = algebraMap R X c from p.commutes c]
    exact hs
  haveI h1 : IsLocalization.Away (algebraMap R M c * algebraMap R M d) X' := by
    rw [mul_comm]
    exact IsLocalization.Away.mul' X X' _ _
  letI : Algebra (Localization.Away (algebraMap R M c)) X' := (pieceL c p s hs).toRingHom.toAlgebra
  haveI : IsScalarTower M (Localization.Away (algebraMap R M c)) X' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (pieceL_algebraMap c p s hs x).symm
  have h3 : IsLocalization.Away (algebraMap M (Localization.Away (algebraMap R M c))
      (algebraMap R M d)) X' :=
    SemistableReduction.OverlapFibre.away_of_mul (algebraMap R M c) (algebraMap R M d)
  refine isLocalizedModule_of_away d (pieceL c p s hs) ?_
  rwa [IsScalarTower.algebraMap_apply R M (Localization.Away (algebraMap R M c)) d]

end Piece

variable (hab : Ideal.span {a, b} = ⊤)
  [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers a) (fst ρa' ρb').toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa' ρb').toLinearMap]
  (hla : letI := sa.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Ba c) Ba')
  (hlb : letI := sb.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Bb c) Bb')

include hsa hsb in
lemma pieceL_compat (x : Localization.Away (algebraMap R (glued ρa ρb) c)) :
    ρa' (pieceL c (fst ρa ρb) sa hla x) = ρb' (pieceL c (snd ρa ρb) sb hlb x) := by
  have h : (ρa' : Ba' →+* Bab').comp (pieceL c (fst ρa ρb) sa hla).toRingHom =
      (ρb' : Bb' →+* Bab').comp (pieceL c (snd ρa ρb) sb hlb).toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R (glued ρa ρb) c))
      (RingHom.ext fun p ↦ ?_)
    change ρa' (pieceL c (fst ρa ρb) sa hla (algebraMap _ _ p)) =
      ρb' (pieceL c (snd ρa ρb) sb hlb (algebraMap _ _ p))
    rw [pieceL_algebraMap, pieceL_algebraMap, hsa, hsb]
    exact congrArg sab p.2
  exact RingHom.congr_fun h x

include hab hla hlb in
/-- **Localization commutes with the glueing**: if the maps of pieces are localizations away from
`c`, so is the induced map of glued algebras. -/
theorem isLocalization_map :
    letI := (map sa sb sab hsa hsb).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (glued ρa ρb) c) (glued ρa' ρb') := by
  set Gl := glued ρa ρb
  set N := Localization.Away (algebraMap R Gl c)
  haveI := isLocalizedModule_pieceL c a (fst ρa ρb) sa hla
  haveI := isLocalizedModule_pieceL c b (snd ρa ρb) sb hlb
  have hbij := bijective_lift a b hab (pieceL c (fst ρa ρb) sa hla) (pieceL c (snd ρa ρb) sb hlb)
    (pieceL_compat sa sb sab hsa hsb c hla hlb)
  letI := (map sa sb sab hsa hsb).toRingHom.toAlgebra
  let e0 := AlgEquiv.ofBijective (lift (pieceL c (fst ρa ρb) sa hla) (pieceL c (snd ρa ρb) sb hlb)
    (pieceL_compat sa sb sab hsa hsb c hla hlb)) hbij
  have he : ∀ p : Gl, e0 (algebraMap Gl N p) = algebraMap Gl (glued ρa' ρb') p := fun p ↦ by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact pieceL_algebraMap c (fst ρa ρb) sa hla p
    · exact pieceL_algebraMap c (snd ρa ρb) sb hlb p
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap R Gl c))
    { e0 with commutes' := he }

section Loc

variable {X : Type u} [CommRing X] [Algebra R X]

/-- The localization `X[1/c]` of an `R`-algebra. -/
abbrev Lc (X : Type u) [CommRing X] [Algebra R X] : Type u := Localization.Away (algebraMap R X c)

/-- The localization map `X → X[1/c]`. -/
abbrev lc (X : Type u) [CommRing X] [Algebra R X] : X →ₐ[R] Lc c X := IsScalarTower.toAlgHom R X _

lemma isLocalization_lc :
    letI := (lc c X).toRingHom.toAlgebra; IsLocalization.Away (algebraMap R X c) (Lc c X) := by
  have h : IsLocalization.Away (algebraMap R X c) (Lc c X) := Localization.isLocalization
  letI := (lc c X).toRingHom.toAlgebra
  exact ⟨h.toIsLocalizationMap⟩

/-- `ρa` localized at `c`. -/
noncomputable abbrev ρaL : Lc c Ba →ₐ[R] Lc c Bab := pieceL c ρa (lc c Bab) (isLocalization_lc c)

/-- `ρb` localized at `c`. -/
noncomputable abbrev ρbL : Lc c Bb →ₐ[R] Lc c Bab := pieceL c ρb (lc c Bab) (isLocalization_lc c)

/-- The map from the glueing to the glueing of the localized pieces. -/
noncomputable abbrev mapL : glued ρa ρb →ₐ[R] glued (ρaL (ρa := ρa) c) (ρbL (ρb := ρb) c) :=
  map (lc c Ba) (lc c Bb) (lc c Bab)
    (fun x ↦ pieceL_algebraMap c ρa (lc c Bab) (isLocalization_lc c) x)
    (fun x ↦ pieceL_algebraMap c ρb (lc c Bab) (isLocalization_lc c) x)

variable (ha : IsUnit (algebraMap R Ba a))
  (hb : letI := ρb.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Bb a) Bab)
  (hb' : IsUnit (algebraMap R Bb b))
  (ha' : letI := ρa.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R Ba b) Bab)

omit [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap] in
include ha hb in
/-- The localized glueing has its first piece on `D(a)`. -/
theorem isLocalizedModule_fstL :
    IsLocalizedModule (Submonoid.powers a)
      (fst (ρaL (ρa := ρa) c) (ρbL (ρb := ρb) c)).toLinearMap :=
  haveI := isLocalizedModule_of_away a ρb hb
  isLocalizedModule_fst a (by rw [IsScalarTower.algebraMap_apply R Ba (Lc c Ba)]; exact ha.map _)
    (away_of_isLocalizedModule a _ (h := isLocalizedModule_pieceL c a ρb (lc c Bab)
      (isLocalization_lc c)))

omit [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap] in
include hb' ha' in
/-- The localized glueing has its second piece on `D(b)`. -/
theorem isLocalizedModule_sndL :
    IsLocalizedModule (Submonoid.powers b)
      (snd (ρaL (ρa := ρa) c) (ρbL (ρb := ρb) c)).toLinearMap :=
  haveI := isLocalizedModule_of_away b ρa ha'
  isLocalizedModule_snd b (by rw [IsScalarTower.algebraMap_apply R Bb (Lc c Bb)]; exact hb'.map _)
    (away_of_isLocalizedModule b _ (h := isLocalizedModule_pieceL c b ρa (lc c Bab)
      (isLocalization_lc c)))

include hab ha hb hb' ha' in
/-- **The glueing of the localized pieces is the localization of the glueing.** -/
theorem isLocalization_mapL :
    letI := (mapL c (ρa := ρa) (ρb := ρb)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (glued ρa ρb) c)
      (glued (ρaL (ρa := ρa) c) (ρbL (ρb := ρb) c)) := by
  haveI := isLocalizedModule_fstL a c (ρa := ρa) ha hb
  haveI := isLocalizedModule_sndL b c (ρb := ρb) hb' ha'
  exact isLocalization_map a b (lc c Ba) (lc c Bb) (lc c Bab)
    (fun x ↦ pieceL_algebraMap c ρa (lc c Bab) (isLocalization_lc c) x)
    (fun x ↦ pieceL_algebraMap c ρb (lc c Bab) (isLocalization_lc c) x) c hab
    (isLocalization_lc c) (isLocalization_lc c)

end Loc

end ZariskiTwo
