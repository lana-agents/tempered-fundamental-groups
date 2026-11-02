/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspPieceHom
import TemperedFundamentalGroups.SemistableReduction.LevelTowerHom
import TemperedFundamentalGroups.SemistableReduction.CuspInput

/-!
# Maps of cusp pieces (MR12 I3, generic core, layer 3 assembly)

A map of cusp-only special-fibre coverings lifts to the patched levels and to the cusp pieces
`CuspTower.cuspPiece` of the M2 construction ([Mzk1] §3.9 (1′A): near the marked points the
coverings are Kummer, and maps between Kummer coverings are Kummer).

* `AdmissibleLift.CuspHom.nfHyp_corner`, **`nfHyp_completion`**: the hypotheses `NFHyp` of the
  Kummer normal form hold on every idempotent factor of the `s`-adic completion of a Noetherian
  ring `B` in which `s` is a nonzerodivisor with `B/(s)` reduced (`NFHyp.of_ringEquiv`: they
  transport along isomorphisms).
* `AdmissibleLift.cuspPhi`: the map of formal cusp models induced by a map `φ : C → C'` of
  coverings without nodes (`kummer' ∘ (R̂ ⊗ φ) ∘ kummer⁻¹`); **`AdmissibleLift.exists_cuspKappa`**:
  an NF-map `g : NF → NF'` compatible with `φ` under `κ` (`kappaF`).
* `LevelTower.CuspNF`, **`LevelTower.cuspLevelMap`**: the map `D.G → D'.G` of patched levels of
  cusp-only coverings induced by `φ` (first component `pMap φ`, so independent of the choice of the
  NF-map), `cuspLevelMap_id/comp`, **`tr_cuspLevelMap`** (compatibility with the towers).
* `CuspTower.covMap`: a morphism `φ₀ : C0 → C0'` of the special data `CuspSpecial` induces the map
  `C0[1/c̄₀] → C0'[1/c̄₀]` of the coverings over `D(c₀)`; **`CuspTower.pieceMap`** : the maps of the
  levels `(cuspPiece Sc).P n → (cuspPiece Sc').P n`, commuting with `sP` (**`sP_pieceMap`**), with
  the structure maps, and functorial (`pieceMap_id`, `pieceMap_comp`);
  **`CuspTower.cuspNFc_of`**: the hypothesis `CuspNF` from `x̄₀` regular on `Ts[1/c̄₀]` with
  reduced quotient.
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

noncomputable section

namespace AdmissibleLift

namespace CuspHom

/-! ### The hypotheses of the Kummer normal form -/

section NF

variable {A A' : Type u} [CommRing A] [CommRing A']

/-- `NFHyp` transports along ring isomorphisms. -/
theorem NFHyp.of_ringEquiv (e : A ≃+* A') {t : A} (h : NFHyp A t) : NFHyp A' (e t) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hspan : Ideal.span {e t} = (Ideal.span {t}).map (e : A →+* A') := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  refine ⟨fun a b hab ↦ e.symm.injective (h1 ?_), ?_, fun a ha ↦ e.symm.injective ?_⟩
  · simp only [smul_eq_mul] at hab ⊢
    have := congrArg e.symm hab
    rwa [map_mul, map_mul, e.symm_apply_apply] at this
  · exact isReduced_of_injective
      ((Ideal.quotientEquiv _ _ e hspan).symm : A' ⧸ Ideal.span {e t} →+* A ⧸ Ideal.span {t})
      (Ideal.quotientEquiv _ _ e hspan).symm.injective
  · rw [map_zero]
    refine h3 _ fun m ↦ ?_
    obtain ⟨c, hc⟩ := ha m
    exact ⟨e.symm c, by rw [hc, map_mul, map_pow, e.symm_apply_apply]⟩

variable {H : Type u} [CommRing H]

omit [CommRing A] [CommRing A'] in
lemma mk_eq_zero_iff {δ : H} (hδ : IsIdempotentElem δ) (a : H) :
    Ideal.Quotient.mk (Ideal.span {1 - δ}) a = 0 ↔ δ * a = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rw [← mul_assoc, mul_sub, mul_one, hδ.eq, sub_self, zero_mul]
  · intro h
    exact ⟨a, by rw [sub_mul, one_mul, h, sub_zero]⟩

omit [CommRing A] [CommRing A'] in
/-- **The hypotheses of the Kummer normal form on an idempotent factor** `H/(1 − δ)` follow from
those on `H`. -/
theorem nfHyp_corner {t δ : H} (hδ : IsIdempotentElem δ) (hreg : IsSMulRegular H t)
    (hred : IsReduced (H ⧸ Ideal.span {t}))
    (hsep : ∀ a : H, (∀ m : ℕ, t ^ m ∣ a) → a = 0) :
    NFHyp (H ⧸ Ideal.span {1 - δ}) (Ideal.Quotient.mk _ t) := by
  have hz : ∀ x : H, t * x = 0 → x = 0 := fun x hx ↦ hreg (by
    change t * x = t * 0
    rw [hx, mul_zero])
  refine ⟨fun a b hab ↦ ?_, ⟨fun y hy ↦ ?_⟩, fun a ha ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff hδ]
    refine hz _ ?_
    have h1 : Ideal.Quotient.mk (Ideal.span {1 - δ}) (t * (a - b)) = 0 := by
      rw [map_mul, map_sub, mul_sub, sub_eq_zero]
      exact hab
    rw [mk_eq_zero_iff hδ] at h1
    rw [← h1]
    ring
  · obtain ⟨m, hm⟩ := hy
    have hm1 : y ^ (m + 1) = 0 := by rw [pow_succ, hm, zero_mul]
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hm1
    obtain ⟨c, hc⟩ := hm1
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub, mk_eq_zero_iff hδ] at hc
    have h2 : Ideal.Quotient.mk (Ideal.span {t}) (δ * a) = 0 := by
      refine hred.eq_zero _ ⟨m + 1, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      refine ⟨δ * c, ?_⟩
      rw [mul_pow, hδ.pow_succ_eq m]
      linear_combination hc
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
    obtain ⟨d, hd⟩ := h2
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ d, ?_⟩
    rw [← map_mul, ← sub_eq_zero, ← map_sub, mk_eq_zero_iff hδ]
    have hδa : δ * (δ * a) = δ * a := by rw [← mul_assoc, hδ.eq]
    linear_combination δ * hd - hδa
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [mk_eq_zero_iff hδ]
    refine hsep _ fun m ↦ ?_
    obtain ⟨c, hc⟩ := ha m
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub, mk_eq_zero_iff hδ] at hc
    exact ⟨δ * c, by linear_combination hc⟩

omit [CommRing A] [CommRing A'] in
/-- **The hypotheses of the Kummer normal form on the idempotent factors of an `s`-adic
completion**: `B` Noetherian, `s` a nonzerodivisor on `B` and `B/(s)` reduced. -/
theorem nfHyp_completion {B : Type u} [CommRing B] [IsNoetherianRing B] (s : B)
    (hs : IsSMulRegular B s) (hred : IsReduced (B ⧸ Ideal.span {s}))
    {δ : AdicCompletion (Ideal.span {s}) B} (hδ : IsIdempotentElem δ) :
    NFHyp (AdicCompletion (Ideal.span {s}) B ⧸ Ideal.span {1 - δ})
      (Ideal.Quotient.mk _ (algebraMap B _ s)) := by
  refine nfHyp_corner hδ (hs.of_flat (S := AdicCompletion (Ideal.span {s}) B)) ?_ ?_
  · have hker : RingHom.ker (AdicCompletion.evalOneₐ (Ideal.span {s})).toRingHom =
        Ideal.span {algebraMap B (AdicCompletion (Ideal.span {s}) B) s} := by
      rw [AdicCompletion.ker_evalOneₐ_eq_map _ (Submodule.fg_span_singleton s), Ideal.map_span,
        Set.image_singleton]
    let eq := (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective
      (f := (AdicCompletion.evalOneₐ (Ideal.span {s})).toRingHom)
      (AdicCompletion.evalOneₐ_surjective _))
    exact isReduced_of_injective (eq : _ →+* B ⧸ Ideal.span {s}) eq.injective
  · intro a ha
    refine IsHausdorff.haus (inferInstance :
      IsHausdorff (Ideal.span {s}) (AdicCompletion (Ideal.span {s}) B)) a fun m ↦ ?_
    obtain ⟨c, rfl⟩ := ha m
    rw [SModEq.zero, ← map_pow, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self s) m)
      Submodule.mem_top

end NF

end CuspHom

/-! ### The NF-map induced by a map of cusp-only coverings -/

section Kappa

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ φ' : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}
  {cov : Admissible.Covering φ ψc} {cov' : Admissible.Covering φ' ψc}
  {πL : cov.ι → O} {πL' : cov'.ι → O}
  (L : KummerLift cov πL) (M : CuspLift cov) (L' : KummerLift cov' πL') (M' : CuspLift cov')

/-- The inclusion of the cusp factors into all factors of a covering without nodes. -/
def cuspIncl [IsEmpty cov.ι] :
    (∀ i, Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i)) →ₐ[Admissible.Hat (fbar θ f)]
      ((∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)) ×
        (∀ i, Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i))) :=
  (AlgHom.pi fun j ↦ isEmptyElim j).prod (AlgHom.id _ _)

lemma cuspIncl_snd [IsEmpty cov.ι]
    (z : (∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)) ×
      (∀ i, Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i))) :
    cuspIncl (cov := cov) z.2 = z :=
  Prod.ext (funext fun j ↦ isEmptyElim j) rfl

/-- **The map of formal cusp models induced by a map `φc : C → C'` of coverings without nodes**:
`kummer' ∘ (R̂ ⊗ φc) ∘ kummer⁻¹` on the cusp factors. -/
def cuspPhi [IsEmpty cov.ι] (φc : cov.C →ₐ[R ⧸ J θ] cov'.C) :
    (∀ i, Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i)) →ₐ[Admissible.Hat (fbar θ f)]
      ∀ i', Admissible.CuspPiece ψc (cov'.cidem i') (cov'.ce i') :=
  (AlgHom.snd _ _ _).comp (cov'.kummer.toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id _ _) φc).comp
      (cov.kummer.symm.toAlgHom.comp cuspIncl)))

lemma cuspPhi_kummer [IsEmpty cov.ι] (φc : cov.C →ₐ[R ⧸ J θ] cov'.C)
    (w : Admissible.Hat (fbar θ f) ⊗[R ⧸ J θ] cov.C) :
    cuspPhi φc (cov.kummer w).2 =
      (cov'.kummer (Algebra.TensorProduct.map
        (AlgHom.id (Admissible.Hat (fbar θ f)) (Admissible.Hat (fbar θ f))) φc w)).2 := by
  change (cov'.kummer (Algebra.TensorProduct.map
    (AlgHom.id (Admissible.Hat (fbar θ f)) (Admissible.Hat (fbar θ f))) φc
    (cov.kummer.symm (cuspIncl (cov.kummer w).2)))).2 = _
  rw [cuspIncl_snd, AlgEquiv.symm_apply_apply]

lemma kappa3F_kappaF [IsNoetherianRing R] (hθ : Function.Surjective θ) (c : cov.C) :
    kappa3F L M hθ (kappaF L M hθ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)) =
      cov.kummer ((1 : Admissible.Hat (fbar θ f)) ⊗ₜ c) := by
  change kappa3F L M hθ ((kappa3F L M hθ).symm (cov.kummer (TensorQuotBase.equiv
    (C := cov.C) (surjective_ψ θ f) (ker_ψ θ f) ((1 : FormalPatchLevel.Hat f) ⊗ₜ c)))) = _
  rw [RingEquiv.apply_symm_apply, TensorQuotBase.equiv_tmul, map_one]

/-- **An NF-map compatible with a map of cusp-only coverings**: for `φc : C → C'` (coverings
without nodes, lift data over the same `t̃`, target bases satisfying `NFHyp`) there is a map
`g : NF → NF'` of `R̂`-algebras with `κ'(1 ⊗ φc c) = g(κ(1 ⊗ c))` modulo `J`. -/
theorem exists_cuspKappa [IsNoetherianRing R] (hθ : Function.Surjective θ) {n : ℕ}
    (hJ : J θ (R := R) ^ n = ⊥) [IsEmpty cov.ι] [IsEmpty cov'.ι] (hMt : M'.t = M.t)
    (hcidem : ∀ i, IsIdempotentElem (M.δ i))
    (hnf : ∀ i', CuspHom.NFHyp (Admissible.Hat (fbar θ f) ⧸ Ideal.span {1 - cov'.cidem i'})
      (Ideal.Quotient.mk _ (ψc X)))
    (φc : cov.C →ₐ[R ⧸ J θ] cov'.C) :
    ∃ g : NFall L M →ₐ[FormalPatchLevel.Hat f] NFall L' M', ∀ (c : cov.C) (x : NFall L M),
      Ideal.Quotient.mk _ x = kappaF L M hθ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c) →
      Ideal.Quotient.mk _ (g x) = kappaF L' M' hθ ((1 : FormalPatchLevel.Hat f) ⊗ₜ φc c) := by
  obtain ⟨g, hg⟩ := exists_cuspNFMap L M L' M' hθ hJ hMt hcidem hnf (cuspPhi φc)
  refine ⟨g, fun c x hx ↦ (kappa3F L' M' hθ).injective (Prod.ext (funext fun j ↦ isEmptyElim j)
    ?_)⟩
  rw [hg, hx, kappa3F_kappaF, kappa3F_kappaF, cuspPhi_kummer, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]

end Kappa

end AdmissibleLift

/-! ### Maps of patched levels of cusp-only coverings -/

namespace LevelTower

open AdmissibleLift

section CuspLevel

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' φ₀'' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {cov₀'' : Admissible.Covering φ₀'' ψ₀} {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  {πL'' : cov₀''.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}

variable (ψ₀) in
/-- **The hypotheses of the Kummer normal form for the cusp factors of a covering** (on the
special chart). -/
def CuspNF {φ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} (cov : Admissible.Covering φ ψ₀) :
    Prop :=
  ∀ i, CuspHom.NFHyp (Admissible.Hat f₀ ⧸ Ideal.span {1 - cov.cidem i})
    (Ideal.Quotient.mk _ (ψ₀ Polynomial.X))

omit [∀ n, IsNoetherianRing (R n)] in
lemma cuspNF_transport (hnf : CuspNF ψ₀ cov₀') (n : ℕ) (i : cov₀'.κ) :
    CuspHom.NFHyp (Admissible.Hat (fbar θ (f n)) ⧸
        Ideal.span {1 - (cov₀'.transport (h := hfe n)).cidem i})
      (Ideal.Quotient.mk _ (Admissible.ψT (h := hfe n) ψ₀ Polynomial.X)) := by
  have h := (hnf i).of_ringEquiv (Admissible.baseEquiv (h := hfe n) (cov₀'.cidem i))
  rwa [Admissible.baseEquiv_mk] at h

variable (hθ : Function.Surjective θ) {n : ℕ}
  (D : Level R cov₀ πL hfe n) (D' : Level R cov₀' πL' hfe n) (D'' : Level R cov₀'' πL'' hfe n)
  [IsEmpty cov₀.ι] [IsEmpty cov₀'.ι] [IsEmpty cov₀''.ι]

/-- **An NF-map compatible with a map of cusp-only coverings exists at every level.** -/
theorem exists_kappaCompat_cusp (φ : cov₀.C →ₐ[R₀] cov₀'.C) (hMt : D'.M.t = D.M.t)
    (hnf : CuspNF ψ₀ cov₀') : ∃ g, KappaCompat hθ D D' φ g := by
  haveI : IsEmpty (cov₀.transport (h := hfe n)).ι := ‹IsEmpty cov₀.ι›
  haveI : IsEmpty (cov₀'.transport (h := hfe n)).ι := ‹IsEmpty cov₀'.ι›
  obtain ⟨g, hg⟩ := exists_cuspKappa D.L D.M D'.L D'.M hθ D.hJ hMt D.hcidem
    (cuspNF_transport hnf n) (transportMap (hfe n) φ)
  refine ⟨g.restrictScalars (R n), fun c ↦ ?_⟩
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (kappaF D.L D.M hθ ((1 : FormalPatchLevel.Hat (f n)) ⊗ₜ c))
  rw [← hx, FormalPatchLevel.NMapQuot_mk]
  exact (hg c x hx).symm

/-- **The map of patched levels of cusp-only coverings** induced by `φ : cov₀.C → cov₀'.C`. -/
def cuspLevelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (hMt : D'.M.t = D.M.t) (hnf : CuspNF ψ₀ cov₀') :
    D.G hθ →ₐ[R n] D'.G hθ :=
  levelMap hθ D D' φ (exists_kappaCompat_cusp hθ D D' φ hMt hnf).choose
    (exists_kappaCompat_cusp hθ D D' φ hMt hnf).choose_spec

@[simp] lemma fst_cuspLevelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (hMt : D'.M.t = D.M.t)
    (hnf : CuspNF ψ₀ cov₀') (x : D.G hθ) :
    (cuspLevelMap hθ D D' φ hMt hnf x).1.1 = pMap D D' φ x.1.1 :=
  rfl

/-- `cuspLevelMap` is `levelMap` for every compatible NF-map. -/
lemma cuspLevelMap_eq (φ : cov₀.C →ₐ[R₀] cov₀'.C) (hMt : D'.M.t = D.M.t)
    (hnf : CuspNF ψ₀ cov₀') (g : NFall D.L D.M →ₐ[R n] NFall D'.L D'.M)
    (hκ : KappaCompat hθ D D' φ g) :
    cuspLevelMap hθ D D' φ hMt hnf = levelMap hθ D D' φ g hκ :=
  eq_levelMap hθ D D' φ g hκ _ fun _ ↦ rfl

lemma cuspLevelMap_id (φ : cov₀.C →ₐ[R₀] cov₀.C) (hMt : D.M.t = D.M.t) (hnf : CuspNF ψ₀ cov₀)
    (hφ : φ = AlgHom.id R₀ cov₀.C) :
    cuspLevelMap hθ D D φ hMt hnf = AlgHom.id (R n) _ := by
  subst hφ
  exact ext_level hθ D fun x ↦ by
    rw [fst_cuspLevelMap, pMap_id]
    rfl

lemma cuspLevelMap_comp (φ : cov₀.C →ₐ[R₀] cov₀'.C) (φ' : cov₀'.C →ₐ[R₀] cov₀''.C)
    (φ'' : cov₀.C →ₐ[R₀] cov₀''.C)
    (hMt : D'.M.t = D.M.t) (hMt' : D''.M.t = D'.M.t) (hMt'' : D''.M.t = D.M.t)
    (hnf' : CuspNF ψ₀ cov₀') (hnf'' : CuspNF ψ₀ cov₀'') (hφ : φ'' = φ'.comp φ) :
    (cuspLevelMap hθ D' D'' φ' hMt' hnf'').comp (cuspLevelMap hθ D D' φ hMt hnf') =
      cuspLevelMap hθ D D'' φ'' hMt'' hnf'' := by
  subst hφ
  exact ext_level hθ D'' fun x ↦ by
    rw [AlgHom.comp_apply, fst_cuspLevelMap, fst_cuspLevelMap, fst_cuspLevelMap,
      pMap_comp D D' D'' φ φ', AlgHom.comp_apply]

end CuspLevel

section CuspTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀}
  {πL : cov₀.ι → O} {πL' : cov₀'.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ)
  [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hq : ∀ n, Function.Surjective (algebraMap (R (n + 1)) (R n)))
  (hf : ∀ n, LevelStep.f' (R' := R n) (f (n + 1)) = f n)
  (he : ∀ n (r : R (n + 1)), e n ((e (n + 1)).symm (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (algebraMap (R (n + 1)) (R n) r))
  (D : ∀ n, Level R cov₀ πL hfe n)
  (hχχ : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.χ j a) = (D n).L.χ j a)
  (hεε : ∀ n j, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.ε j) = (D n).L.ε j)
  (hδδ : ∀ n i, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).M.δ i) = (D n).M.δ i)
  (htt : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (D (n + 1)).M.t = (D n).M.t)
  (D' : ∀ n, Level R cov₀' πL' hfe n)
  (hχχ' : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D' (n + 1)).L.χ j a) =
    (D' n).L.χ j a)
  (hεε' : ∀ n j, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D' (n + 1)).L.ε j) = (D' n).L.ε j)
  (hδδ' : ∀ n i, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D' (n + 1)).M.δ i) = (D' n).M.δ i)
  (htt' : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (D' (n + 1)).M.t = (D' n).M.t)
  [IsEmpty cov₀.ι] [IsEmpty cov₀'.ι]

/-- **The maps of patched levels of cusp-only coverings commute with the transition maps.** -/
theorem tr_cuspLevelMap (φ : cov₀.C →ₐ[R₀] cov₀'.C) (hMt : ∀ n, (D' n).M.t = (D n).M.t)
    (hnf : CuspNF ψ₀ cov₀') (n : ℕ) (x : (D (n + 1)).G hθ) :
    tr hθ hO hq hf he D' hχχ' hεε' hδδ' htt' n
        (cuspLevelMap hθ (D (n + 1)) (D' (n + 1)) φ (hMt (n + 1)) hnf x) =
      cuspLevelMap hθ (D n) (D' n) φ (hMt n) hnf (tr hθ hO hq hf he D hχχ hεε hδδ htt n x) :=
  tr_levelMap hθ hO hq hf he D hχχ hεε hδδ htt D' hχχ' hεε' hδδ' htt' φ
    (fun n ↦ (exists_kappaCompat_cusp hθ (D n) (D' n) φ (hMt n) hnf).choose)
    (fun n ↦ (exists_kappaCompat_cusp hθ (D n) (D' n) φ (hMt n) hnf).choose_spec) n x

end CuspTower

end LevelTower

/-! ### Maps of cusp pieces from morphisms of the special data -/

namespace CuspTower

open TateLevel AdmissibleLift EtaleTower

variable {O : Type u} [CommRing O] {T0' : Type u} [CommRing T0'] [Algebra O T0'] {c0 x0 : T0'}
  {k : Type u} [Field k] {θ : O →+* k}

lemma isUnit_φsC_c0 : IsUnit (φsC T0' c0 θ (Ideal.Quotient.mk _ c0)) := by
  rw [φsC, Ideal.quotientMap_mk]
  exact (IsLocalization.Away.algebraMap_isUnit c0).map _

/-- **`Ts θ (Rc T0' c0)` is `Ts θ T0'[1/c̄₀]`.** -/
lemma isLocalization_φsC : letI := (φsC T0' c0 θ).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (J θ (R := T0')) c0) (Ts θ (Rc T0' c0)) :=
  TateLevel.isLocalization_quotMap (R := T0') (S := Rc T0' c0) c0 (RingHom.ker θ)

variable [hθ : Fact (Function.Surjective θ)] (Sc Sc' Sc'' : CuspSpecial T0' c0 x0 (θ := θ))

lemma isUnit_ι₀_c0 (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) :
    IsUnit ((Sc'.ι₀.comp (φ0 : Sc.C0 →+* Sc'.C0))
      (algebraMap (Ts θ T0') Sc.C0 (Ideal.Quotient.mk _ c0))) := by
  rw [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes, Sc'.hι₀]
  exact isUnit_φsC_c0.map _

/-- The ring map `C0[1/c̄₀] → C0'[1/c̄₀]` induced by `φ0 : C0 → C0'`. -/
def covMapR (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) : Sc.cov.C →+* Sc'.cov.C :=
  letI := Sc.ι₀.toAlgebra
  haveI := Sc.hι
  IsLocalization.Away.lift (algebraMap (Ts θ T0') Sc.C0 (Ideal.Quotient.mk _ c0))
    (isUnit_ι₀_c0 Sc Sc' φ0)

lemma covMapR_ι₀ (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (x : Sc.C0) :
    covMapR Sc Sc' φ0 (Sc.ι₀ x) = Sc'.ι₀ (φ0 x) :=
  letI := Sc.ι₀.toAlgebra
  haveI := Sc.hι
  IsLocalization.Away.lift_eq _ (isUnit_ι₀_c0 Sc Sc' φ0) x

/-- **The map of coverings over `D(c₀)` induced by a morphism `φ0 : C0 → C0'` of cusp special
data.** -/
def covMap (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) :
    Sc.cov.C →ₐ[Ts θ (Rc T0' c0)] Sc'.cov.C :=
  { covMapR Sc Sc' φ0 with
    commutes' := fun r ↦ by
      letI := (φsC T0' c0 θ).toAlgebra
      haveI : IsLocalization.Away (Ideal.Quotient.mk (J θ (R := T0')) c0)
          (Ts θ (Rc T0' c0)) := isLocalization_φsC
      have h := IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (J θ) c0))
        (S := Ts θ (Rc T0' c0)) (j := (covMapR Sc Sc' φ0).comp (algebraMap _ Sc.cov.C))
        (k := algebraMap _ Sc'.cov.C) (RingHom.ext fun x ↦ by
          change covMapR Sc Sc' φ0 (algebraMap _ Sc.cov.C (φsC T0' c0 θ x)) =
            algebraMap _ Sc'.cov.C (φsC T0' c0 θ x)
          rw [← Sc.hι₀, covMapR_ι₀, AlgHom.commutes, Sc'.hι₀])
      exact RingHom.congr_fun h r }

lemma covMap_ι₀ (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (x : Sc.C0) :
    covMap Sc Sc' φ0 (Sc.ι₀ x) = Sc'.ι₀ (φ0 x) :=
  covMapR_ι₀ Sc Sc' φ0 x

/-- Maps out of `C0[1/c̄₀]` are determined on `C0`. -/
lemma covMap_ext {φ ψ : Sc.cov.C →ₐ[Ts θ (Rc T0' c0)] Sc'.cov.C}
    (h : ∀ x, φ (Sc.ι₀ x) = ψ (Sc.ι₀ x)) : φ = ψ := by
  letI := Sc.ι₀.toAlgebra
  haveI := Sc.hι
  exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
    (Submonoid.powers (algebraMap (Ts θ T0') Sc.C0 (Ideal.Quotient.mk _ c0)))
    (RingHom.ext fun x ↦ h x))

lemma covMap_id : covMap Sc Sc (AlgHom.id _ Sc.C0) = AlgHom.id _ Sc.cov.C :=
  covMap_ext Sc Sc fun x ↦ covMap_ι₀ Sc Sc _ x

lemma covMap_comp (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (φ0' : Sc'.C0 →ₐ[Ts θ T0'] Sc''.C0) :
    covMap Sc Sc'' (φ0'.comp φ0) = (covMap Sc' Sc'' φ0').comp (covMap Sc Sc' φ0) :=
  covMap_ext Sc Sc'' fun x ↦ by
    rw [covMap_ι₀, AlgHom.comp_apply, AlgHom.comp_apply, covMap_ι₀, covMap_ι₀]

/-- **The hypotheses of the Kummer normal form for the cusp factors** of the covering of the
special data over `D(c₀)`. -/
abbrev CuspNFc : Prop :=
  LevelTower.CuspNF (ψb (θ := θ) _ (sC T0' c0 x0) (sC T0' c0 x0)) Sc.cov

/-- **`CuspNFc` holds if `x̄₀` is a nonzerodivisor on `Ts[1/c̄₀]` with reduced quotient.** -/
theorem cuspNFc_of [IsNoetherianRing T0']
    (hs : IsSMulRegular (Ts θ (Rc T0' c0)) (fbar θ (sC T0' c0 x0)))
    (hred : IsReduced (Ts θ (Rc T0' c0) ⧸ Ideal.span {fbar θ (sC T0' c0 x0)})) :
    CuspNFc Sc := fun i ↦ by
  have h := CuspHom.nfHyp_completion (fbar θ (sC T0' c0 x0)) hs hred
    (Sc.cov.isIdempotentElem_cidem i)
  rwa [show (ψb (θ := θ) _ (sC T0' c0 x0) (sC T0' c0 x0)) X =
      algebraMap _ _ (fbar θ (sC T0' c0 x0)) from Polynomial.aeval_X _]

variable {ϖ : O} (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing T0']
  (hx : ∀ n, IsSMulRegular (Tn ϖ T0' n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O T0')) x0 : Tn ϖ T0' n))

/-- **The maps of the levels of the cusp towers** induced by a morphism `φ0 : C0 → C0'` of cusp
special data. -/
def pieceMap (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (n : ℕ) :
    (cuspTower Sc hϖ hker hx).G hθ.out n →ₐ[Tn ϖ (Rc T0' c0) n]
      (cuspTower Sc' hϖ hker hx).G hθ.out n :=
  LevelTower.cuspLevelMap hθ.out ((cuspTower Sc hϖ hker hx).level n)
    ((cuspTower Sc' hϖ hker hx).level n) (covMap Sc Sc' φ0) rfl hnf

lemma pieceMap_id (hnf : CuspNFc Sc) (n : ℕ) :
    pieceMap Sc Sc hϖ hker hx hnf (AlgHom.id _ Sc.C0) n = AlgHom.id _ _ :=
  LevelTower.cuspLevelMap_id hθ.out _ _ rfl hnf (covMap_id Sc)

lemma pieceMap_comp (hnf' : CuspNFc Sc') (hnf'' : CuspNFc Sc'')
    (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (φ0' : Sc'.C0 →ₐ[Ts θ T0'] Sc''.C0) (n : ℕ) :
    (pieceMap Sc' Sc'' hϖ hker hx hnf'' φ0' n).comp (pieceMap Sc Sc' hϖ hker hx hnf' φ0 n) =
      pieceMap Sc Sc'' hϖ hker hx hnf'' (φ0'.comp φ0) n :=
  LevelTower.cuspLevelMap_comp hθ.out ((cuspTower Sc hϖ hker hx).level n)
    ((cuspTower Sc' hϖ hker hx).level n) ((cuspTower Sc'' hϖ hker hx).level n)
    (covMap Sc Sc' φ0) (covMap Sc' Sc'' φ0') (covMap Sc Sc'' (φ0'.comp φ0)) rfl rfl rfl hnf' hnf''
    (covMap_comp Sc Sc' Sc'' φ0 φ0')

variable (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The maps of the cusp pieces commute with the successor maps.** -/
theorem sP_pieceMap (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (n : ℕ)
    (x : (cuspPiece Sc hϖ hker hx hO).P (n + 1)) :
    (cuspPiece Sc' hϖ hker hx hO).sP n (pieceMap Sc Sc' hϖ hker hx hnf φ0 (n + 1) x) =
      pieceMap Sc Sc' hϖ hker hx hnf φ0 n ((cuspPiece Sc hϖ hker hx hO).sP n x) :=
  let T := cuspTower Sc hϖ hker hx
  let T' := cuspTower Sc' hϖ hker hx
  LevelTower.tr_cuspLevelMap hθ.out hO T.hq T.hf T.he T.level T.hcχ
    (LevelTower.hεε_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg
      T.hf T.he)
    (LevelTower.hδδ_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg
      T.hf T.he) T.hct
    T'.level T'.hcχ
    (LevelTower.hεε_mk T'.hfe T'.hπ T'.χ T'.hχ T'.t T'.ht T'.hJ T'.hflat T'.hfχ T'.hreg
      T'.hf T'.he)
    (LevelTower.hδδ_mk T'.hfe T'.hπ T'.χ T'.hχ T'.t T'.ht T'.hJ T'.hflat T'.hfχ T'.hreg
      T'.hf T'.he) T'.hct
    (covMap Sc Sc' φ0) (fun _ ↦ rfl) hnf n x

/-- `pieceMap` is compatible with the structure maps from the levels of the chart. -/
lemma pieceMap_algebraMapB (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (n : ℕ)
    (y : Tn ϖ T0' n) :
    pieceMap Sc Sc' hϖ hker hx hnf φ0 n
        (algebraMap (Tn ϖ T0' n) ((cuspPiece Sc hϖ hker hx hO).P n) y) =
      algebraMap (Tn ϖ T0' n) ((cuspPiece Sc' hϖ hker hx hO).P n) y :=
  (pieceMap Sc Sc' hϖ hker hx hnf φ0 n).commutes _

/-- `pieceMap` is compatible with the structure maps from `O`. -/
lemma pieceMap_algebraMapO (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (n : ℕ)
    (o : O) :
    pieceMap Sc Sc' hϖ hker hx hnf φ0 n (algebraMap O ((cuspPiece Sc hϖ hker hx hO).P n) o) =
      algebraMap O ((cuspPiece Sc' hϖ hker hx hO).P n) o :=
  (pieceMap Sc Sc' hϖ hker hx hnf φ0 n).commutes _

end CuspTower

end

end SemistableReduction
