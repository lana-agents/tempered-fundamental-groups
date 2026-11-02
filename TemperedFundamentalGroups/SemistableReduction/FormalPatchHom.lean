/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalPatchReduction

/-!
# Maps of patched algebras (Blueprint §12.8, M2.3)

MR12 I3 / generic core: maps of patched algebras. The level-`n` formal patch
`FormalPatchLevel.patch f J hJ α₀ = P ×_{N_f} N` is functorial in the patching data:

* `FormalPatchLevel.NfMap g : N_f → N'_f` for an `R`-algebra map `g : N → N'` (`f ↦ f`), with
  `NfMap_algebraMap`, `NfMap_id`, `NfMap_comp`, and the induced map modulo `J`,
  `FormalPatchLevel.NfMapQuot g : N_f/J → N'_f/J` (`NfMapQuot_mk`, `NfMapQuot_comp_mkₐ`);
* **`FormalPatchLevel.lift_comp`**: maps `p : P → P'`, `g : N → N'` compatible with the patching
  data modulo `J` (`NfMapQuot g ∘ α₀ = α₀' ∘ p`) are compatible with the lifts
  `α = lift α₀ : P → N_f` (uniqueness of lifts out of the formally étale `P` into the
  `J`-adically complete `N'_f`, `EtaleLift.ext_of_comp_eq`);
* **`FormalPatchLevel.patchMap p g h : patch α₀ → patch α₀'`**, `(x, y) ↦ (p x, g y)`, with
  `fst_patchMap`, `snd_patchMap`, `patchMap_id`, `patchMap_comp`;
* **uniqueness**: for `N'` without `f`-torsion, maps into a patched algebra are determined by
  their first component (`ext_of_fst`), so every map `φ` with `fst ∘ φ = p ∘ fst` is
  `patchMap p g h` (`eq_patchMap`);
* **the special-fibre form of the compatibility** (`FormalPatchLevel.comp_alphaOfEquiv`): for
  `α₀ = alphaOfEquiv (specialFibreEquiv σ κ)`, `α₀' = alphaOfEquiv (specialFibreEquiv σ' κ')`
  and a map of special-fibre coverings `φ : C → C'`, the hypothesis of `lift_comp` follows from
  `σ' ∘ p = φ_f ∘ σ` (on `P/JP`) and `κ' ∘ (R̂ ⊗ φ) = g ∘ κ` (modulo `J`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalPatchLevel

/-! ### Maps of localizations -/

section NfMap

variable {R : Type u} [CommRing R] (f : R) (J : Ideal R)
  {N N' N'' : Type u} [CommRing N] [Algebra R N] [CommRing N'] [Algebra R N']
  [CommRing N''] [Algebra R N'']

lemma isUnit_NfMap (g : N →ₐ[R] N') :
    IsUnit ((IsScalarTower.toAlgHom R N' (Nf f N')).comp g (algebraMap R N f)) := by
  rw [AlgHom.comp_apply, AlgHom.commutes, IsScalarTower.coe_toAlgHom']
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The map `N_f → N'_f` induced by an `R`-algebra map `g : N → N'`. -/
noncomputable def NfMap (g : N →ₐ[R] N') : Nf f N →ₐ[R] Nf f N' :=
  IsLocalization.Away.liftAlgHom (algebraMap R N f) (isUnit_NfMap f g)

lemma NfMap_algebraMap (g : N →ₐ[R] N') (x : N) :
    NfMap f g (algebraMap N (Nf f N) x) = algebraMap N' (Nf f N') (g x) :=
  IsLocalization.Away.lift_eq _ (isUnit_NfMap f g) x

lemma NfMap_ext {φ ψ : Nf f N →ₐ[R] Nf f N'}
    (h : ∀ x : N, φ (algebraMap N (Nf f N) x) = ψ (algebraMap N (Nf f N) x)) : φ = ψ :=
  AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext
    (Submonoid.powers (algebraMap R N f)) (RingHom.ext h)

lemma NfMap_id : NfMap f (AlgHom.id R N) = AlgHom.id R (Nf f N) :=
  NfMap_ext f fun x ↦ NfMap_algebraMap f _ x

lemma NfMap_comp (g : N →ₐ[R] N') (g' : N' →ₐ[R] N'') :
    NfMap f (g'.comp g) = (NfMap f g').comp (NfMap f g) :=
  NfMap_ext f fun x ↦ by
    rw [NfMap_algebraMap, AlgHom.comp_apply, AlgHom.comp_apply, NfMap_algebraMap,
      NfMap_algebraMap]

lemma JNf_le_comap (g : N →ₐ[R] N') : JNf f J N ≤ (JNf f J N').comap (NfMap f g) :=
  Ideal.map_le_iff_le_comap.mpr fun r hr ↦ by
    change NfMap f g (algebraMap R (Nf f N) r) ∈ JNf f J N'
    rw [AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hr

/-- The map `N_f/J → N'_f/J` induced by an `R`-algebra map `g : N → N'`. -/
noncomputable def NfMapQuot (g : N →ₐ[R] N') : Nf f N ⧸ JNf f J N →ₐ[R] Nf f N' ⧸ JNf f J N' :=
  Ideal.quotientMapₐ (JNf f J N') (NfMap f g) (JNf_le_comap f J g)

lemma NfMapQuot_mk (g : N →ₐ[R] N') (x : Nf f N) :
    NfMapQuot f J g (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (NfMap f g x) :=
  rfl

lemma NfMapQuot_comp_mkₐ (g : N →ₐ[R] N') :
    (NfMapQuot f J g).comp (Ideal.Quotient.mkₐ R (JNf f J N)) =
      (Ideal.Quotient.mkₐ R (JNf f J N')).comp (NfMap f g) :=
  AlgHom.ext fun _ ↦ rfl

lemma NfMapQuot_comp (g : N →ₐ[R] N') (g' : N' →ₐ[R] N'') :
    NfMapQuot f J (g'.comp g) = (NfMapQuot f J g').comp (NfMapQuot f J g) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ (NfMap f (g'.comp g) x) =
    Ideal.Quotient.mk _ (NfMap f g' (NfMap f g x))
  rw [NfMap_comp, AlgHom.comp_apply]

lemma NfMapQuot_id : NfMapQuot f J (AlgHom.id R N) = AlgHom.id R _ := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ (NfMap f (AlgHom.id R N) x) = Ideal.Quotient.mk _ x
  rw [NfMap_id, AlgHom.id_apply]

end NfMap

/-! ### Compatibility of the lifts -/

section Lift

variable {R : Type u} [CommRing R] (f : R) (J : Ideal R) {n : ℕ} (hJ : J ^ n = ⊥)
  {P P' P'' : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  [CommRing P'] [Algebra R P'] [Algebra.FormallyEtale R P']
  [CommRing P''] [Algebra R P''] [Algebra.FormallyEtale R P'']
  {N N' N'' : Type u} [CommRing N] [Algebra R N] [CommRing N'] [Algebra R N']
  [CommRing N''] [Algebra R N'']
  (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N) (α₀' : P' →ₐ[R] Nf f N' ⧸ JNf f J N')
  (α₀'' : P'' →ₐ[R] Nf f N'' ⧸ JNf f J N'')

omit [Algebra.FormallyEtale R P] [Algebra.FormallyEtale R P'] [Algebra.FormallyEtale R P''] in
/-- Compatible data compose. -/
lemma comp_compat {p : P →ₐ[R] P'} {g : N →ₐ[R] N'} {p' : P' →ₐ[R] P''} {g' : N' →ₐ[R] N''}
    (h : (NfMapQuot f J g).comp α₀ = α₀'.comp p)
    (h' : (NfMapQuot f J g').comp α₀' = α₀''.comp p') :
    (NfMapQuot f J (g'.comp g)).comp α₀ = α₀''.comp (p'.comp p) := by
  rw [NfMapQuot_comp, AlgHom.comp_assoc, h, ← AlgHom.comp_assoc, h', AlgHom.comp_assoc]

omit [Algebra.FormallyEtale R P] [Algebra.FormallyEtale R P'] [Algebra.FormallyEtale R P''] in
lemma id_compat : (NfMapQuot f J (AlgHom.id R N)).comp α₀ = α₀.comp (AlgHom.id R P) := by
  rw [NfMapQuot_id, AlgHom.id_comp, AlgHom.comp_id]

omit [Algebra.FormallyEtale R P''] in
/-- **Compatibility of the lifts**: maps compatible with the patching data modulo `J` are
compatible with the lifts `P → N_f`. -/
theorem lift_comp (p : P →ₐ[R] P') (g : N →ₐ[R] N')
    (h : (NfMapQuot f J g).comp α₀ = α₀'.comp p) :
    (NfMap f g).comp (lift f J hJ α₀) = (lift f J hJ α₀').comp p := by
  haveI := isAdicComplete_JNf f J hJ (N := N')
  refine EtaleLift.ext_of_comp_eq (JNf f J N') ?_
  rw [← AlgHom.comp_assoc, ← NfMapQuot_comp_mkₐ, AlgHom.comp_assoc, mkₐ_comp_lift, h,
    ← AlgHom.comp_assoc, mkₐ_comp_lift]

omit [Algebra.FormallyEtale R P''] in
lemma lift_comp_apply (p : P →ₐ[R] P') (g : N →ₐ[R] N')
    (h : (NfMapQuot f J g).comp α₀ = α₀'.comp p) (x : P) :
    NfMap f g (lift f J hJ α₀ x) = lift f J hJ α₀' (p x) :=
  congrArg (fun φ : P →ₐ[R] Nf f N' ↦ φ x) (lift_comp f J hJ α₀ α₀' p g h)

/-! ### Maps of patched algebras -/

omit [Algebra.FormallyEtale R P''] in
/-- **The map of patched algebras** `(x, y) ↦ (p x, g y)`. -/
noncomputable def patchMap (p : P →ₐ[R] P') (g : N →ₐ[R] N')
    (h : (NfMapQuot f J g).comp α₀ = α₀'.comp p) :
    patch f J hJ α₀ →ₐ[R] patch f J hJ α₀' :=
  FormalGlueing.liftGlued N' (lift f J hJ α₀')
    (p.comp (FormalGlueing.fst N (lift f J hJ α₀)))
    (g.comp (FormalGlueing.snd N (lift f J hJ α₀))) fun x ↦ by
      change lift f J hJ α₀' (p x.1.1) = algebraMap N' (Nf f N') (g x.1.2)
      rw [← lift_comp_apply f J hJ α₀ α₀' p g h, (FormalGlueing.mem_glued N _).mp x.2,
        NfMap_algebraMap]

omit [Algebra.FormallyEtale R P''] in
@[simp] lemma fst_patchMap (p : P →ₐ[R] P') (g : N →ₐ[R] N')
    (h : (NfMapQuot f J g).comp α₀ = α₀'.comp p) (x : patch f J hJ α₀) :
    FormalGlueing.fst N' (lift f J hJ α₀') (patchMap f J hJ α₀ α₀' p g h x) =
      p (FormalGlueing.fst N (lift f J hJ α₀) x) :=
  rfl

omit [Algebra.FormallyEtale R P''] in
@[simp] lemma snd_patchMap (p : P →ₐ[R] P') (g : N →ₐ[R] N')
    (h : (NfMapQuot f J g).comp α₀ = α₀'.comp p) (x : patch f J hJ α₀) :
    FormalGlueing.snd N' (lift f J hJ α₀') (patchMap f J hJ α₀ α₀' p g h x) =
      g (FormalGlueing.snd N (lift f J hJ α₀) x) :=
  rfl

omit [Algebra.FormallyEtale R P'] [Algebra.FormallyEtale R P''] in
lemma patchMap_id (h : (NfMapQuot f J (AlgHom.id R N)).comp α₀ = α₀.comp (AlgHom.id R P)) :
    patchMap f J hJ α₀ α₀ (AlgHom.id R P) (AlgHom.id R N) h = AlgHom.id R _ :=
  AlgHom.ext fun _ ↦ rfl

lemma patchMap_comp (p : P →ₐ[R] P') (g : N →ₐ[R] N') (p' : P' →ₐ[R] P'')
    (g' : N' →ₐ[R] N'') (h : (NfMapQuot f J g).comp α₀ = α₀'.comp p)
    (h' : (NfMapQuot f J g').comp α₀' = α₀''.comp p')
    (h'' : (NfMapQuot f J (g'.comp g)).comp α₀ = α₀''.comp (p'.comp p)) :
    (patchMap f J hJ α₀' α₀'' p' g' h').comp (patchMap f J hJ α₀ α₀' p g h) =
      patchMap f J hJ α₀ α₀'' (p'.comp p) (g'.comp g) h'' :=
  AlgHom.ext fun _ ↦ rfl

/-! ### Uniqueness -/

omit [Algebra.FormallyEtale R P] in
/-- **Maps into a patched algebra are determined by their first component** (`N'` without
`f`-torsion). -/
theorem ext_of_fst (hN' : ∀ x : N', algebraMap R N' f * x = 0 → x = 0) {M : Type*} [CommRing M]
    [Algebra R M] {φ ψ : M →ₐ[R] patch f J hJ α₀'}
    (h : ∀ x, FormalGlueing.fst N' (lift f J hJ α₀') (φ x) =
      FormalGlueing.fst N' (lift f J hJ α₀') (ψ x)) : φ = ψ :=
  AlgHom.ext fun x ↦ FormalGlueing.eq_of_fst_eq (f := f) N' (lift f J hJ α₀') hN' (h x)

omit [Algebra.FormallyEtale R P''] in
/-- **Uniqueness of maps of patched algebras**: a map with first component `p` is
`patchMap p g h` (`N'` without `f`-torsion). -/
theorem eq_patchMap (hN' : ∀ x : N', algebraMap R N' f * x = 0 → x = 0) (p : P →ₐ[R] P')
    (g : N →ₐ[R] N') (h : (NfMapQuot f J g).comp α₀ = α₀'.comp p)
    (φ : patch f J hJ α₀ →ₐ[R] patch f J hJ α₀')
    (hφ : ∀ x, FormalGlueing.fst N' (lift f J hJ α₀') (φ x) =
      p (FormalGlueing.fst N (lift f J hJ α₀) x)) :
    φ = patchMap f J hJ α₀ α₀' p g h :=
  ext_of_fst f J hJ α₀' hN' hφ

end Lift

/-! ### The compatibility from the special fibre -/

section SpecialFibre

variable {R : Type u} [CommRing R] (f : R) (J : Ideal R)
  {P P' : Type u} [CommRing P] [Algebra R P] [CommRing P'] [Algebra R P']
  {C C' : Type u} [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
  {N N' : Type u} [CommRing N] [Algebra R N] [Algebra (Hat f) N] [IsScalarTower R (Hat f) N]
  [CommRing N'] [Algebra R N'] [Algebra (Hat f) N'] [IsScalarTower R (Hat f) N']

omit [Algebra (Hat f) N] [IsScalarTower R (Hat f) N] in
lemma JN_le_comap (g : N →ₐ[R] N') : JN J N ≤ (JN J N').comap g :=
  Ideal.map_le_iff_le_comap.mpr fun r hr ↦ by
    change g (algebraMap R N r) ∈ JN J N'
    rw [AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hr

/-- The map `N/JN → N'/JN'` induced by an `R`-algebra map `g : N → N'`. -/
noncomputable def NMapQuot (g : N →ₐ[R] N') : N ⧸ JN J N →ₐ[R] N' ⧸ JN J N' :=
  Ideal.quotientMapₐ (JN J N') g (JN_le_comap J g)

omit [Algebra (Hat f) N] [IsScalarTower R (Hat f) N] [Algebra (Hat f) N']
  [IsScalarTower R (Hat f) N'] in
lemma NMapQuot_mk (g : N →ₐ[R] N') (x : N) :
    NMapQuot J g (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (g x) :=
  rfl

omit [Algebra (Hat f) N] [IsScalarTower R (Hat f) N] [Algebra (Hat f) N']
  [IsScalarTower R (Hat f) N'] in
lemma isUnit_algebraMap_quot (k : ℕ) :
    IsUnit (algebraMap R (Nf f N' ⧸ JNf f J N') f ^ k) := by
  refine IsUnit.pow k ?_
  rw [IsScalarTower.algebraMap_apply R (Nf f N') (Nf f N' ⧸ JNf f J N'),
    IsScalarTower.algebraMap_apply R N' (Nf f N')]
  exact (IsLocalization.Away.algebraMap_isUnit _).map _

/-- **The compatibility of `lift_comp` from the special fibre**: for the patching data of
special-fibre coverings `C`, `C'` (`σ : P/JP ≃ C_f`, `κ : R̂ ⊗ C ≃ N/JN`, same for `'`), maps
`p : P → P'`, `φ : C → C'`, `g : N → N'` with `σ' ∘ p = φ_f ∘ σ` and `κ' ∘ (R̂ ⊗ φ) = g ∘ κ`
are compatible with the patching data modulo `J`. -/
theorem comp_alphaOfEquiv
    (σ : (P ⧸ J.map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R C f))
    (κ : (Hat f ⊗[R] C) ≃ₐ[Hat f] (N ⧸ JN J N))
    (σ' : (P' ⧸ J.map (algebraMap R P')) ≃ₐ[R] Localization.Away (algebraMap R C' f))
    (κ' : (Hat f ⊗[R] C') ≃ₐ[Hat f] (N' ⧸ JN J N'))
    (p : P →ₐ[R] P') (φ : C →ₐ[R] C') (g : N →ₐ[R] N')
    (hσ : ∀ x : P, σ' (Ideal.Quotient.mk _ (p x)) = NfMap f φ (σ (Ideal.Quotient.mk _ x)))
    (hκ : ∀ c : C, κ' ((1 : Hat f) ⊗ₜ φ c) = NMapQuot J g (κ ((1 : Hat f) ⊗ₜ c))) :
    (NfMapQuot f J g).comp (alphaOfEquiv f J (specialFibreEquiv f J σ κ)) =
      (alphaOfEquiv f J (specialFibreEquiv f J σ' κ')).comp p := by
  ext x
  set α₀ := alphaOfEquiv f J (specialFibreEquiv f J σ κ)
  set α₀' := alphaOfEquiv f J (specialFibreEquiv f J σ' κ')
  obtain ⟨k, c, hc⟩ := IsLocalization.Away.surj (algebraMap R C f) (σ (Ideal.Quotient.mk _ x))
  obtain ⟨m, hm⟩ := Ideal.Quotient.mk_surjective (κ ((1 : Hat f) ⊗ₜ c))
  set y : P := algebraMap R P f ^ k * x
  have hy : σ (Ideal.Quotient.mk _ y) = algebraMap C _ c := by
    rw [← hc, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, Ideal.Quotient.mk_algebraMap,
      map_mul, map_pow, AlgEquiv.commutes, mul_comm]
  have hy' : σ' (Ideal.Quotient.mk _ (p y)) = algebraMap C' _ (φ c) := by
    rw [hσ, hy, NfMap_algebraMap]
  have hm' : κ' ((1 : Hat f) ⊗ₜ φ c) = Ideal.Quotient.mk _ (g m) := by
    rw [hκ, ← hm, NMapQuot_mk]
  have e1 : α₀ y = Ideal.Quotient.mk _ (algebraMap N (Nf f N) m) :=
    alphaOfEquiv_spec f J σ κ y c m hy hm.symm
  have e2 : α₀' (p y) = Ideal.Quotient.mk _ (algebraMap N' (Nf f N') (g m)) :=
    alphaOfEquiv_spec f J σ' κ' (p y) (φ c) (g m) hy' hm'
  have key : algebraMap R (Nf f N' ⧸ JNf f J N') f ^ k * NfMapQuot f J g (α₀ x) =
      algebraMap R (Nf f N' ⧸ JNf f J N') f ^ k * α₀' (p x) := by
    have h1 : NfMapQuot f J g (α₀ y) = α₀' (p y) := by
      rw [e1, e2, NfMapQuot_mk, NfMap_algebraMap]
    simpa only [y, map_mul, map_pow, AlgHom.commutes] using h1
  exact (isUnit_algebraMap_quot f J k).mul_left_cancel key

end SpecialFibre

end FormalPatchLevel

end SemistableReduction
