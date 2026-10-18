/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwo

/-!
# Maps of two-piece glueings and their kernels (Blueprint §12.8, M2.3 (f), tower)

For two glueings `glued ρa ρb = Ba ×_{Bab} Bb` and `glued ρa' ρb'` over the same base `R` and
the same basic opens `D(a)`, `D(b)` (`a, b` generating the unit ideal), and compatible
`R`-algebra maps of the pieces `sa : Ba → Ba'`, `sb : Bb → Bb'`, `sab : Bab → Bab'`:

* `ZariskiTwo.map`: the induced map of glued algebras;
* **`ZariskiTwo.surjective_map`**, **`ZariskiTwo.ker_map`**: if `sa`, `sb` are surjective with
  kernels `K Ba`, `K Bb` for an ideal `K` of `R`, then the glued map is surjective with kernel
  `K · glued` (the quotient `glued/K` has localizations `Ba/K = Ba'`, `Bb/K = Bb'`, so it is the
  glueing of `Ba'`, `Bb'` by `ZariskiTwo.bijective_lift`).

This gives the successor maps of a tower of glued algebras (levels `ϖⁿ⁺¹`).
-/

universe u

namespace ZariskiTwo

variable {R : Type u} [CommRing R] (a b : R)
  {Ba Bb Bab : Type u} [CommRing Ba] [CommRing Bb] [CommRing Bab]
  [Algebra R Ba] [Algebra R Bb] [Algebra R Bab]
  {ρa : Ba →ₐ[R] Bab} {ρb : Bb →ₐ[R] Bab}
  {Ba' Bb' Bab' : Type u} [CommRing Ba'] [CommRing Bb'] [CommRing Bab']
  [Algebra R Ba'] [Algebra R Bb'] [Algebra R Bab']
  {ρa' : Ba' →ₐ[R] Bab'} {ρb' : Bb' →ₐ[R] Bab'}
  (sa : Ba →ₐ[R] Ba') (sb : Bb →ₐ[R] Bb') (sab : Bab →ₐ[R] Bab')
  (hsa : ∀ x, ρa' (sa x) = sab (ρa x)) (hsb : ∀ x, ρb' (sb x) = sab (ρb x))

/-- **The map of glued algebras** induced by compatible maps of the pieces. -/
def map : glued ρa ρb →ₐ[R] glued ρa' ρb' :=
  lift ((sa).comp (fst ρa ρb)) ((sb).comp (snd ρa ρb)) fun p ↦ by
    simp only [AlgHom.comp_apply, fst_apply, snd_apply, hsa, hsb]
    exact congrArg sab p.2

@[simp] lemma fst_map (p : glued ρa ρb) :
    fst ρa' ρb' (map sa sb sab hsa hsb p) = sa (fst ρa ρb p) := rfl

@[simp] lemma snd_map (p : glued ρa ρb) :
    snd ρa' ρb' (map sa sb sab hsa hsb p) = sb (snd ρa ρb p) := rfl

variable (K : Ideal R)

/-- The ideal `K · glued`. -/
abbrev KG : Ideal (glued ρa ρb) := K.map (algebraMap R (glued ρa ρb))

lemma map_KG_fst : (KG (ρa := ρa) (ρb := ρb) K).map (fst ρa ρb : glued ρa ρb →+* Ba) =
    K.map (algebraMap R Ba) := by
  rw [Ideal.map_map]
  congr 1

lemma map_KG_snd : (KG (ρa := ρa) (ρb := ρb) K).map (snd ρa ρb : glued ρa ρb →+* Bb) =
    K.map (algebraMap R Bb) := by
  rw [Ideal.map_map]
  congr 1

/-- A surjective `R`-algebra map with kernel `K` from a localization: the induced map from the
quotient `M/KM` of the source of a localization `φ : M → B` is a localization. -/
lemma isLocalizedModule_quot {M B B' : Type u} [CommRing M] [Algebra R M] [CommRing B]
    [Algebra R B] [CommRing B'] [Algebra R B'] (c : R) (φ : M →ₐ[R] B)
    [hφ : IsLocalizedModule (Submonoid.powers c) φ.toLinearMap] (s : B →ₐ[R] B')
    (hs : Function.Surjective s) (hk : RingHom.ker s = K.map (algebraMap R B))
    (ψ : M ⧸ K.map (algebraMap R M) →ₐ[R] B')
    (hψ : ∀ x, ψ (Ideal.Quotient.mk _ x) = s (φ x)) :
    IsLocalizedModule (Submonoid.powers c) ψ.toLinearMap := by
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R M B := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid M (Submonoid.powers c)) B := by
    have h := (isLocalizedModule_iff_isLocalization (S := Submonoid.powers c) (A := M)
      (Aₛ := B)).mp
    exact h hφ
  letI := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower R (M ⧸ K.map (algebraMap R M)) B' :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  refine isLocalizedModule_iff_isLocalization.mpr ?_
  have h := IsLocalization.of_surjective (M := Algebra.algebraMapSubmonoid M (Submonoid.powers c))
    (S := B) (R' := M ⧸ K.map (algebraMap R M)) (S' := B') (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective (s : B →+* B') hs (RingHom.ext fun x ↦ (hψ x).symm) (by
      rw [show RingHom.ker (s : B →+* B') = K.map (algebraMap R B) from hk, Ideal.mk_ker,
        Ideal.map_map]
      refine le_of_eq (congrArg (Ideal.map · K) ?_)
      exact (φ.comp_algebraMap).symm)
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, Submonoid.map_powers] at h
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  exact h

variable (hab : Ideal.span {a, b} = ⊤)
  [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers a) (fst ρa' ρb').toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa' ρb').toLinearMap]
  (hsa' : Function.Surjective sa) (hsb' : Function.Surjective sb)
  (hka : RingHom.ker sa = K.map (algebraMap R Ba)) (hkb : RingHom.ker sb = K.map (algebraMap R Bb))

omit [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers a) (fst ρa' ρb').toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa' ρb').toLinearMap] in
include hka hkb in
lemma map_algebraMap {r : R} (hr : r ∈ K) : map sa sb sab hsa hsb (algebraMap R _ r) = 0 := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change sa (algebraMap R Ba r) = 0
    rw [← RingHom.mem_ker, hka]
    exact Ideal.mem_map_of_mem _ hr
  · change sb (algebraMap R Bb r) = 0
    rw [← RingHom.mem_ker, hkb]
    exact Ideal.mem_map_of_mem _ hr

omit [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers a) (fst ρa' ρb').toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa' ρb').toLinearMap] in
include hka hkb in
lemma KG_le_ker : KG (ρa := ρa) (ρb := ρb) K ≤ RingHom.ker (map sa sb sab hsa hsb) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  exact map_algebraMap sa sb sab hsa hsb K hka hkb hr

/-- The map `glued/K → glued'` induced by `map`. -/
def mapQ : (glued ρa ρb ⧸ KG (ρa := ρa) (ρb := ρb) K) →ₐ[R] glued ρa' ρb' :=
  Ideal.Quotient.liftₐ _ (map sa sb sab hsa hsb) fun _ hx ↦
    KG_le_ker sa sb sab hsa hsb K hka hkb hx

omit [IsLocalizedModule (Submonoid.powers a) (fst ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa ρb).toLinearMap]
  [IsLocalizedModule (Submonoid.powers a) (fst ρa' ρb').toLinearMap]
  [IsLocalizedModule (Submonoid.powers b) (snd ρa' ρb').toLinearMap] in
lemma mapQ_mk (p : glued ρa ρb) :
    mapQ sa sb sab hsa hsb K hka hkb (Ideal.Quotient.mk _ p) = map sa sb sab hsa hsb p := rfl

include hab hsa' hsb' in
/-- **`glued/K` is the glueing of the pieces of the target**. -/
theorem bijective_mapQ : Function.Bijective (mapQ sa sb sab hsa hsb K hka hkb) := by
  set ψ := mapQ sa sb sab hsa hsb K hka hkb
  haveI : IsLocalizedModule (Submonoid.powers a) ((fst ρa' ρb').comp ψ).toLinearMap :=
    isLocalizedModule_quot K a (fst ρa ρb) sa hsa' hka _ fun _ ↦ rfl
  haveI : IsLocalizedModule (Submonoid.powers b) ((snd ρa' ρb').comp ψ).toLinearMap :=
    isLocalizedModule_quot K b (snd ρa ρb) sb hsb' hkb _ fun _ ↦ rfl
  have h := bijective_lift a b hab ((fst ρa' ρb').comp ψ) ((snd ρa' ρb').comp ψ)
    (fun x ↦ fst_snd ρa' ρb' (ψ x))
  have he : ⇑(lift ((fst ρa' ρb').comp ψ) ((snd ρa' ρb').comp ψ)
      (fun x ↦ fst_snd ρa' ρb' (ψ x))) = ψ := funext fun x ↦ rfl
  rwa [he] at h

include hab hsa' hsb' hka hkb in
/-- **The glued map is surjective.** -/
theorem surjective_map : Function.Surjective (map sa sb sab hsa hsb) :=
  ((bijective_mapQ a b sa sb sab hsa hsb K hab hsa' hsb' hka hkb).2.comp
    Ideal.Quotient.mk_surjective : _)

include hab hsa' hsb' hka hkb in
/-- **The kernel of the glued map is `K · glued`.** -/
theorem ker_map : RingHom.ker (map sa sb sab hsa hsb) = KG (ρa := ρa) (ρb := ρb) K := by
  refine le_antisymm (fun x hx ↦ ?_) (KG_le_ker sa sb sab hsa hsb K hka hkb)
  rw [RingHom.mem_ker] at hx
  have h0 : mapQ sa sb sab hsa hsb K hka hkb (Ideal.Quotient.mk _ x) =
      mapQ sa sb sab hsa hsb K hka hkb 0 := by
    rw [mapQ_mk, hx, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    ((bijective_mapQ a b sa sb sab hsa hsb K hab hsa' hsb' hka hkb).1 h0)

end ZariskiTwo
