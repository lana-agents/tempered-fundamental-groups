/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalLevelCompat
import TemperedFundamentalGroups.SemistableReduction.FormalKummerCov
import TemperedFundamentalGroups.SemistableReduction.LevelTowerData
import TemperedFundamentalGroups.SemistableReduction.PatchUnique

/-!
# The level patches of the M2 lift of a normalisation (MR12 T2 S6, step G3, generic)

Let `R` be a chart over `O` with node coordinates `x y = ϖⁿ`, `B` an `R`-algebra (the
normalisation of the chart in a tame cover) with chosen Kummer data `D j` at the nodes, and
`cov₀ = FormalKummer.covOf …` the admissible covering `B/JB` of the special fibre. For a level
datum `lv : LevelTower.Level Rt cov₀ πK hfe l` of the M2 lift (a level ring `Rt l`, its
formally étale piece `P` over `D(f)` with `σP`, Kummer lift data `L` with node coordinates `χL`
and lifted idempotents `L.ε`), we identify the patched algebra `lv.G` with `Rt l ⊗_R B`
(**`FormalLevel.levelPatchEquiv`**), via `FormalPatchLevel.patchEquivOfCompat`:

* **`exists_φ₁`** (étale side): if `(Rt l ⊗_R B)[1/f]` is formally étale over `Rt l`, it is
  `P` (uniqueness of étale lifts, `EtaleLift.algEquivOfQuot`), compatibly with `σP` and the
  reduction `ρ : Rt l ⊗_R B → B/JB` (`EtaleIso`: `ρ` is surjective with kernel `J`);
* **`φ₂`**, **`isBaseChange_φ₂`** (formal side): `R̂ ⊗ (Rt l ⊗_R B) ≅ R̂ ⊗_R B ≅ NF` by the level
  formal Kummer form `FormalLevel.levelEquiv` (the lifted idempotents are the Lemma F
  idempotents, `hεL`, so the factors agree up to `NCongr`);
* **`kappaF_one_tmul_ρ`** (compatibility): `κ (1 ⊗ ρ z) = φ₂ z mod J`, from
  `FormalLevel.levelEquiv_compat` and `Admissible.transport_kummer_one_tmul`.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalLevel

noncomputable section

open KummerEtale FormalKummer AdmissibleLift

namespace EtaleIso

variable {A M C P : Type*} [CommRing A] [CommRing M] [Algebra A M] [CommRing C] [Algebra A C]
  [CommRing P] [Algebra A P] (I : Ideal A) (f : A) (ρ : M →ₐ[A] C)
  (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = I.map (algebraMap A M))

/-- The map `C ≅ M/ker ρ → M_f/IM_f`. -/
def γ : C →+* Localization.Away (algebraMap A M f) ⧸
    I.map (algebraMap A (Localization.Away (algebraMap A M f))) :=
  (Ideal.Quotient.lift (RingHom.ker ρ) ((Ideal.Quotient.mk _).comp
    (algebraMap M (Localization.Away (algebraMap A M f)))) (by
      intro z hz
      rw [hker] at hz
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
        IsScalarTower.algebraMap_eq A M (Localization.Away (algebraMap A M f)), ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ hz)).comp
    (Ideal.quotientKerAlgEquivOfSurjective hρ).symm.toRingEquiv.toRingHom

include hker in
lemma γ_ρ (z : M) : γ I f ρ hρ hker (ρ z) =
    Ideal.Quotient.mk _ (algebraMap M (Localization.Away (algebraMap A M f)) z) := by
  have : (Ideal.quotientKerAlgEquivOfSurjective hρ).symm (ρ z) = Ideal.Quotient.mk _ z :=
    (AlgEquiv.symm_apply_eq _).mpr rfl
  simp only [γ, RingHom.comp_apply]
  erw [this]
  rfl

lemma isLocalization_γ :
    letI := (γ I f ρ hρ hker).toAlgebra
    IsLocalization.Away (algebraMap A C f) (Localization.Away (algebraMap A M f) ⧸
      I.map (algebraMap A (Localization.Away (algebraMap A M f)))) := by
  letI := (γ I f ρ hρ hker).toAlgebra
  have h := IsLocalization.of_surjective (M := Submonoid.powers (algebraMap A M f))
    (S := Localization.Away (algebraMap A M f)) ρ.toRingHom hρ (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective
    (RingHom.ext fun z ↦ (γ_ρ I f ρ hρ hker z).symm)
    (by
      rw [Ideal.mk_ker, AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom, hker, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq])
  rw [Submonoid.map_powers] at h
  simpa using h

/-- **`τ : M_f/IM_f ≃ C_f`.** -/
def τ : (Localization.Away (algebraMap A M f) ⧸
      I.map (algebraMap A (Localization.Away (algebraMap A M f)))) ≃ₐ[A]
    Localization.Away (algebraMap A C f) :=
  letI := (γ I f ρ hρ hker).toAlgebra
  haveI := isLocalization_γ I f ρ hρ hker
  haveI : IsScalarTower A C (Localization.Away (algebraMap A M f) ⧸
      I.map (algebraMap A (Localization.Away (algebraMap A M f)))) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = γ I f ρ hρ hker (algebraMap A C a)
      rw [← ρ.commutes, γ_ρ, ← IsScalarTower.algebraMap_apply]
      rfl
  (IsLocalization.algEquiv (Submonoid.powers (algebraMap A C f)) _ _).restrictScalars A

lemma τ_mk (z : M) : τ I f ρ hρ hker (Ideal.Quotient.mk _
    (algebraMap M (Localization.Away (algebraMap A M f)) z)) =
      algebraMap C (Localization.Away (algebraMap A C f)) (ρ z) := by
  letI := (γ I f ρ hρ hker).toAlgebra
  haveI := isLocalization_γ I f ρ hρ hker
  rw [← γ_ρ I f ρ hρ hker z]
  exact (IsLocalization.algEquiv (Submonoid.powers (algebraMap A C f)) _ _).commutes (ρ z)

include hρ hker in
theorem exists_φ₁ [Algebra.FormallyEtale A P]
    (σP : (P ⧸ I.map (algebraMap A P)) ≃ₐ[A] Localization.Away (algebraMap A C f))
    {m : ℕ} (hI : I ^ m = ⊥)
    [Algebra.FormallyEtale A (Localization.Away (algebraMap A M f))] :
    ∃ φ₁ : M →ₐ[A] P,
      (letI := φ₁.toRingHom.toAlgebra;
        IsLocalization.Away (algebraMap A M f) P) ∧
      ∀ z, σP (Ideal.Quotient.mk _ (φ₁ z)) = algebraMap _ _ (ρ z) := by
  haveI : IsAdicComplete (I.map (algebraMap A P)) P :=
    CompleteFinite.isAdicComplete_of_pow_eq_bot _ (n := m)
      (by rw [← Ideal.map_pow, hI, Ideal.map_bot])
  haveI : IsAdicComplete (I.map (algebraMap A (Localization.Away (algebraMap A M f))))
      (Localization.Away (algebraMap A M f)) :=
    CompleteFinite.isAdicComplete_of_pow_eq_bot _ (n := m)
      (by rw [← Ideal.map_pow, hI, Ideal.map_bot])
  let Φ := EtaleLift.algEquivOfQuot I ((τ I f ρ hρ hker).trans σP.symm)
  refine ⟨Φ.toAlgHom.comp (IsScalarTower.toAlgHom A M _), ?_, fun z ↦ ?_⟩
  · letI := (Φ.toAlgHom.comp (IsScalarTower.toAlgHom A M
      (Localization.Away (algebraMap A M f)))).toRingHom.toAlgebra
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap A M f))
      (AlgEquiv.ofRingEquiv (f := Φ.toRingEquiv) fun _ ↦ rfl)
  · have h := congrArg (fun g ↦ g (algebraMap M (Localization.Away (algebraMap A M f)) z))
      (EtaleLift.mkₐ_comp_algEquivOfQuot I ((τ I f ρ hρ hker).trans σP.symm))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
    change σP (Ideal.Quotient.mk _ (Φ _)) = _
    erw [h, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    exact τ_mk I f ρ hρ hker z

end EtaleIso

section KappaGeneric

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] [Algebra k (R ⧸ J θ (R := R))] [IsNoetherianRing R]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀} {e₁ : R₀ ≃ₐ[k] (R ⧸ J θ (R := R))}
  (f : R) (h₁ : e₁ f₀ = fbar θ f) {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀} (cov₀ : Admissible.Covering φ₀ ψ₀)
  (hθ' : Function.Surjective θ) {πL : cov₀.ι → O}
  (L : KummerLift (cov₀.transport (h := h₁)) πL) (M : CuspLift (cov₀.transport (h := h₁)))

/-- **`κ` on `1 ⊗ c`**: its reduction `kappa3F` is the transported special-fibre Kummer form. -/
lemma kappa3F_kappaF_one_tmul (c : cov₀.C) :
    kappa3F L M hθ' (kappaF L M hθ' ((1 : FormalPatchLevel.Hat f) ⊗ₜ[R]
        (@id (cov₀.transport (h := h₁)).C c))) =
      Admissible.piecesEquiv (h := h₁) cov₀ (cov₀.kummer ((1 : Admissible.Hat f₀) ⊗ₜ c)) := by
  change kappa3F L M hθ' ((kappa3F L M hθ').symm _) = _
  rw [RingEquiv.apply_symm_apply]
  change (cov₀.transport (h := h₁)).kummer (TensorQuotBase.equiv _ _
    ((1 : FormalPatchLevel.Hat f) ⊗ₜ[R] (@id (cov₀.transport (h := h₁)).C c))) = _
  rw [TensorQuotBase.equiv_tmul, map_one]
  exact Admissible.transport_kummer_one_tmul (h := h₁) cov₀ c

end KappaGeneric

attribute [local instance] KummerNormAtData.algO

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ϖ : O} {n M' : ℕ} {x y : R}
  (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
  {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
  (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
  (hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
  (D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j)) {g : R}
  (hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
  (hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j))
  (hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical)
  (φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g))
  (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
  (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y))
  (ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g))
  (hfin : Module.Finite (Rs θ R) (Cs θ R B))
  (het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale)
  (hk : ∀ j i, ((D j).d i : k) ≠ 0)
  -- the tower of levels
  (Rt : ℕ → Type u) [∀ l, CommRing (Rt l)] [∀ l, Algebra O (Rt l)]
  [∀ l, IsNoetherianRing (Rt l)] [∀ l, Algebra R (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
  {f : ∀ l, Rt l} {e : ∀ l, Rs θ R ≃ₐ[k] (Rt l ⧸ J θ (R := Rt l))}
  (hfe : ∀ l, e l (fbar θ g) = fbar θ (f l))
  (he : ∀ l (r : R), e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Rt l) r))

/-- The covering of the special fibre defined by `B` (`covOf`), abbreviated. -/
abbrev cov₀ : Admissible.Covering φ ψc :=
  covOf hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk

lemma cov₀_kummer_fst (w : Admissible.Hat (fbar θ g) ⊗[Rs θ R] Cs θ R B) (p : Σ j, Fin (D j).r) :
    ((cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk).kummer w).1 p =
      kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv w p := rfl

/-- The deformation parameters `ϖ^{mᵢ}` of the Kummer factors. -/
abbrev πK : (Σ j, Fin (D j).r) → O := fun p ↦ ϖ ^ (D p.1).m p.2

variable (l : ℕ)

/-- The transported covering at level `l` (ring `C = B/JB`, an `Rt l`-algebra via `e l⁻¹`). -/
abbrev covL :=
  (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk).transport (h := hfe l)

/-- `C = B/JB` as an `R`-algebra through `Rt l`. -/
abbrev algRC : Algebra R (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk
    Rt hfe l).C :=
  Algebra.compHom _ (algebraMap R (Rt l))

/-- The reduction `B → C = B/JB` as an `R`-algebra map (`C` an `R`-algebra through `Rt l`). -/
def mkC : letI := algRC hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l
    B →ₐ[R] (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l).C :=
  letI := algRC hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l
  { (Ideal.Quotient.mk ((J θ (R := R)).map (algebraMap R B)) : B →+* Cs θ R B) with
    commutes' := fun r ↦ by
      change Ideal.Quotient.mk _ (algebraMap R B r) =
        algebraMap (Rs θ R) (Cs θ R B) ((e l).symm (Ideal.Quotient.mk _ (algebraMap R (Rt l) r)))
      rw [← he l r, AlgEquiv.symm_apply_apply]
      rfl }

/-- **The reduction `ρ : Rt l ⊗_R B → C = B/JB`** (`r ⊗ b ↦ r̄ · b̄`). -/
def ρ : Rt l ⊗[R] B →ₐ[Rt l]
    (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l).C :=
  letI := algRC hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l
  haveI : IsScalarTower R (Rt l)
      (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l).C :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (mkC hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l)
    fun _ _ ↦ Commute.all _ _

omit [∀ l, IsNoetherianRing (Rt l)] [∀ l, IsScalarTower O R (Rt l)] in
lemma ρ_tmul (r : Rt l) (b : B) :
    ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l (r ⊗ₜ b) =
      algebraMap (Rt l) _ r * (show (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc
        hfin het hk Rt hfe l).C from Ideal.Quotient.mk _ b) := by
  letI := algRC hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l
  haveI : IsScalarTower R (Rt l)
      (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l).C :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _


omit [∀ l, IsNoetherianRing (Rt l)] [∀ l, IsScalarTower O R (Rt l)] in
lemma ρ_surjective : Function.Surjective
    (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l) := by
  intro c
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (show Cs θ R B from c)
  refine ⟨1 ⊗ₜ b, ?_⟩
  rw [ρ_tmul, map_one, one_mul]
  exact hb

omit [∀ l, IsNoetherianRing (Rt l)] in
lemma ker_ρ : RingHom.ker (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk
    Rt hfe he l) =
    (J θ (R := Rt l)).map (algebraMap (Rt l) (Rt l ⊗[R] B)) := by
  have hJR : ∀ r ∈ J θ (R := R), algebraMap R (Rt l) r ∈ J θ (R := Rt l) := by
    intro r hr
    have hle : (J θ (R := R)).map (algebraMap R (Rt l)) ≤ J θ (R := Rt l) := by
      rw [J, J, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hle (Ideal.mem_map_of_mem _ hr)
  set I' := (J θ (R := Rt l)).map (algebraMap (Rt l) (Rt l ⊗[R] B)) with hI'
  let ψ : (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk
    Rt hfe l).C →+* (Rt l ⊗[R] B) ⧸ I' := Ideal.Quotient.lift _ ((Ideal.Quotient.mk I').comp
    (Algebra.TensorProduct.includeRight (R := R) (A := Rt l) (B := B)).toRingHom) (by
      intro b hb
      rw [← RingHom.mem_ker]
      refine (Ideal.map_le_iff_le_comap.mpr ?_) hb
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      change (1 : Rt l) ⊗ₜ[R] algebraMap R B r ∈ I'
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
      exact Ideal.mem_map_of_mem (algebraMap (Rt l) (Rt l ⊗[R] B)) (hJR r hr))
  have hψ : ∀ z, ψ (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk
      Rt hfe he l z) = Ideal.Quotient.mk I' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul r b =>
      rw [ρ_tmul, map_mul]
      obtain ⟨r', hr'⟩ := Ideal.Quotient.mk_surjective ((e l).symm (Ideal.Quotient.mk _ r))
      have h1 : algebraMap (Rt l) (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin
          het hk Rt hfe l).C r = (show (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc
          hfin het hk Rt hfe l).C from Ideal.Quotient.mk _ (algebraMap R B r')) := by
        change algebraMap (Rs θ R) (Cs θ R B) ((e l).symm (Ideal.Quotient.mk _ r)) = _
        rw [← hr']
        rfl
      have h2 : Ideal.Quotient.mk (J θ (R := Rt l)) (algebraMap R (Rt l) r') =
          Ideal.Quotient.mk _ r := by
        rw [← he, hr', AlgEquiv.apply_symm_apply]
      rw [h1]
      change Ideal.Quotient.mk I' ((1 : Rt l) ⊗ₜ algebraMap R B r') *
        Ideal.Quotient.mk I' ((1 : Rt l) ⊗ₜ b) = _
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Ideal.Quotient.eq,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one, ← TensorProduct.sub_tmul]
      have hm : (algebraMap R (Rt l) r' - r) ⊗ₜ[R] b = algebraMap (Rt l) (Rt l ⊗[R] B)
          (algebraMap R (Rt l) r' - r) * ((1 : Rt l) ⊗ₜ b) := by
        change _ = (algebraMap R (Rt l) r' - r) ⊗ₜ[R] (1 : B) * ((1 : Rt l) ⊗ₜ b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hm]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.mp h2))
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  ext z
  constructor
  · intro hz
    rw [RingHom.mem_ker] at hz
    have h := hψ z
    rw [hz, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h.symm
  · intro hz
    refine (Ideal.map_le_iff_le_comap.mpr ?_) hz
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    change algebraMap (Rs θ R) (Cs θ R B) ((e l).symm (Ideal.Quotient.mk _ a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]


omit [∀ l, IsNoetherianRing (Rt l)] in
variable {l} in
/-- **The étale side of the level-`l` patch** (S6 G3): if `(Rt l ⊗_R B)[1/f]` is
formally étale over `Rt l`, it maps isomorphically onto the étale lift `P` of the level datum,
compatibly with `σP` and `ρ`. -/
theorem exists_φ₁ (lv : LevelTower.Level Rt
      (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk) (πK 𝔪 D) hfe l)
    [Algebra.FormallyEtale (Rt l) (Localization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (f l)))] :
    ∃ φ₁ : Rt l ⊗[R] B →ₐ[Rt l] lv.P,
      (letI := φ₁.toRingHom.toAlgebra;
        IsLocalization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (f l)) lv.P) ∧
      ∀ z, lv.σP (Ideal.Quotient.mk _ (φ₁ z)) = algebraMap _ _
        (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l z) := by
  exact EtaleIso.exists_φ₁ (J θ (R := Rt l)) (f l)
    (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l)
    (ρ_surjective hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l)
    (ker_ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l) lv.σP lv.hJ

/-! ### The formal side -/

/-- `N f χ ε₁ ≃ N f χ ε₂` for `ε₁ = ε₂`. -/
def NCongr {R' : Type u} [CommRing R'] [Algebra O R'] {f' : R'} {π : O} {d : ℕ}
    (χ : A π d →ₐ[O] FormalPatchLevel.Hat f') {ε₁ ε₂ : FormalPatchLevel.Hat f'} (h : ε₁ = ε₂) :
    AdmissibleLift.N f' χ ε₁ ≃ₐ[FormalPatchLevel.Hat f'] AdmissibleLift.N f' χ ε₂ := by
  subst h; exact AlgEquiv.refl

omit hθ [IsSepClosed k] in
lemma pieceEquiv_NCongr {R' : Type u} [CommRing R'] [Algebra O R'] [IsNoetherianRing R']
    [Algebra k (R' ⧸ J θ (R := R'))] {f' : R'}
    (φ' : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f')) {π : O} {d : ℕ} (hd : 0 < d)
    (χ : A π d →ₐ[O] FormalPatchLevel.Hat f') {ε₁ ε₂ : FormalPatchLevel.Hat f'} (h : ε₁ = ε₂)
    (εb : Admissible.Hat (fbar θ f')) (hε₁ : ψ θ f' ε₁ = εb) (hε₂ : ψ θ f' ε₂ = εb)
    (hθ' : Function.Surjective θ) (hπ : θ π = 0)
    (hχ : ∀ a, ψ θ f' (χ a) = φ' (Admissible.nodeCongr hd (Node.baseMap θ (hA hπ) a)))
    (z : AdmissibleLift.N f' χ ε₁) :
    pieceEquiv f' φ' hd χ ε₂ εb hε₂ hθ' hπ hχ (Ideal.Quotient.mk _ (NCongr χ h z)) =
      pieceEquiv f' φ' hd χ ε₁ εb hε₁ hθ' hπ hχ (Ideal.Quotient.mk _ z) := by
  subst h; rfl

variable {l} (lv : LevelTower.Level Rt (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc
    hfin het hk) (πK 𝔪 D) hfe l)

/-- The node coordinates of the level datum, with their node rings `O[u,v]/(uv − ϖⁿ)`. -/
abbrev χL (p : Σ j, Fin (D j).r) :
    A (ϖ ^ (D p.1).m p.2) ((D p.1).d p.2) →ₐ[O] FormalPatchLevel.Hat (f l) :=
  lv.L.χ p

variable {𝔪' : ι → Ideal (Rt l)} [∀ j, (𝔪' j).IsMaximal] (hinj : Function.Injective 𝔪')
  (hf : ∀ j, f l ∈ 𝔪' j) (hrad : ⨅ j, 𝔪' j ≤ (Ideal.span {f l}).radical)
  (r : ∀ j, (D j).N₁ →ₐ[R] Rt l ⧸ 𝔪' j)
  (hχL : ∀ p a, χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv p a =
    algebraMap R (FormalPatchLevel.Hat (f l)) (chart hxy (D p.1) p.2 a))
  (hεL : ∀ p, CompletionProd.idem hinj hf hrad p.1 = lv.L.ε p)

/-- The level formal Kummer form with the lifted idempotents of the level datum. -/
def PhiP : FormalPatchLevel.Hat (f l) ⊗[R] B ≃ₐ[FormalPatchLevel.Hat (f l)]
    ∀ p : (Σ j, Fin (D j).r), AdmissibleLift.N (f l) (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ
        hφu hφv ψc hfin het hk Rt hfe lv p) (lv.L.ε p) :=
  (levelEquiv hxy hinj hf hrad D r (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin
      het hk Rt hfe lv) hχL
    (fun j ↦ CompletionProd.idem hinj hf hrad j) (fun _ ↦ rfl)).trans
    (AlgEquiv.piCongrRight fun p ↦ NCongr (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc
        hfin het hk Rt hfe lv p) (hεL p))

/-- `∏_p N_p ≃ NFall` (no cusp factors). -/
def toNFall : (∀ p : (Σ j, Fin (D j).r),
      AdmissibleLift.N (f l) (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk
          Rt hfe lv p) (lv.L.ε p)) ≃ₐ[FormalPatchLevel.Hat (f l)]
    NFall lv.L lv.M where
  toFun x s := match s with
    | .inl p => x p
    | .inr i => (show Empty from i).elim
  invFun y p := y (.inl p)
  left_inv _ := rfl
  right_inv _ := funext fun s ↦ match s with
    | .inl _ => rfl
    | .inr i => (show Empty from i).elim
  map_mul' _ _ := funext fun s ↦ match s with
    | .inl _ => rfl
    | .inr i => (show Empty from i).elim
  map_add' _ _ := funext fun s ↦ match s with
    | .inl _ => rfl
    | .inr i => (show Empty from i).elim
  commutes' _ := funext fun s ↦ match s with
    | .inl _ => rfl
    | .inr i => (show Empty from i).elim

/-- **The formal side `R̂ ⊗_{Rt l} (Rt l ⊗_R B) ≃ NF`** of the level-`l` patch. -/
def PhiT : FormalPatchLevel.Hat (f l) ⊗[Rt l] (Rt l ⊗[R] B) ≃ₐ[FormalPatchLevel.Hat (f l)]
    NFall lv.L lv.M :=
  (Algebra.TensorProduct.cancelBaseChange R (Rt l) (FormalPatchLevel.Hat (f l))
    (FormalPatchLevel.Hat (f l)) B).trans
    ((PhiP hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv hinj hf hrad
        r hχL hεL).trans (toNFall hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk
            Rt hfe lv))

/-- `φ₂ : Rt l ⊗_R B → NF`, `z ↦ PhiT (1 ⊗ z)`. -/
def φ₂ : Rt l ⊗[R] B →ₐ[Rt l] NFall lv.L lv.M where
  toFun z := PhiT hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv hinj
      hf hrad r hχL hεL ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ z)
  map_one' := by rw [← Algebra.TensorProduct.one_def, map_one]
  map_mul' z w := by rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_zero' := by rw [TensorProduct.tmul_zero, map_zero]
  map_add' z w := by rw [TensorProduct.tmul_add, map_add]
  commutes' c := by
    have h1 : (1 : FormalPatchLevel.Hat (f l)) ⊗ₜ[Rt l] algebraMap (Rt l) (Rt l ⊗[R] B) c =
        algebraMap (FormalPatchLevel.Hat (f l)) _ (algebraMap (Rt l) _ c) := by
      rw [Algebra.algebraMap_eq_smul_one c, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
            Algebra.smul_def, mul_one]
    rw [h1, AlgEquiv.commutes]
    rfl

omit [∀ l, IsScalarTower O R (Rt l)] in
theorem isBaseChange_φ₂ : IsBaseChange (FormalPatchLevel.Hat (f l))
    (φ₂ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv hinj hf hrad r
        hχL hεL).toLinearMap :=
  IsBaseChange.of_equiv (PhiT hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt
      hfe lv hinj hf hrad r hχL hεL).toLinearEquiv fun _ ↦ rfl

omit [∀ l, IsScalarTower O R (Rt l)] in
lemma φ₂_apply (z : Rt l ⊗[R] B) :
    φ₂ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv hinj hf hrad r
        hχL hεL z = PhiT hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv
            hinj hf hrad r hχL hεL ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ z) := rfl

omit [∀ l, IsScalarTower O R (Rt l)] in
lemma φ₂_one_tmul (b : B) :
    φ₂ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv hinj hf hrad r
        hχL hεL ((1 : Rt l) ⊗ₜ b) =
      toNFall hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv (PhiP hxy
          hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv hinj hf hrad r hχL
              hεL ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ b)) := by
  rw [φ₂_apply, PhiT, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

variable (hm : ∀ j, (𝔪' j).map (red θ (e l)) ≤ sIdeal (θ := θ) (𝔪 j))
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] (hr : ∀ j, ∀ z ∈ (D j).𝔫, r j z = 0)

set_option maxHeartbeats 1000000 in
-- the comparison unfolds the transported covering `covOf … |>.transport`
set_option maxRecDepth 20000 in
omit [∀ l, IsScalarTower O R (Rt l)] in
include he hm hr in
/-- **`κ` on `1 ⊗ b̄`** (the hypothesis `hκ` of `patchEquivOfCompat` on generators). -/
theorem kappaF_one_tmul (b : B) :
    kappaF lv.L lv.M hθ.out ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ
        (@id (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l).C
            (Ideal.Quotient.mk _ b))) =
      Ideal.Quotient.mk _ (φ₂ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt
          hfe lv hinj hf hrad r hχL hεL ((1 : Rt l) ⊗ₜ b)) := by
  apply (kappa3F lv.L lv.M hθ.out).injective
  have hL : kappa3F lv.L lv.M hθ.out (kappaF lv.L lv.M hθ.out ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ
        (@id (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l).C
            (Ideal.Quotient.mk _ b)))) =
      Admissible.piecesEquiv (h := hfe l) (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv
          ψc hfin het hk)
        ((cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk).kummer ((1 :
            Admissible.Hat (fbar θ g)) ⊗ₜ
          (@id (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk).C
              (Ideal.Quotient.mk _ b)))) := by
    exact kappa3F_kappaF_one_tmul (f l) (hfe l) (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu
        hφv ψc hfin het hk) hθ.out lv.L lv.M _
  rw [hL, φ₂_one_tmul]
  refine Prod.ext (funext fun p ↦ ?_) (funext fun i ↦ (show Empty from i).elim)
  have hεψ : ψ θ (f l) (CompletionProd.idem hinj hf hrad p.1) =
      Admissible.hatEquiv (e l) (hfe l) (CompletionProd.idem hinjk hfk hradk p.1) :=
    (congrArg _ (hεL p)).trans (lv.L.hε p)
  have hχ' : ∀ a, ψ θ (f l) (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt
      hfe lv p a) = Admissible.φT (h := hfe l) φ
      (Admissible.nodeCongr ((D p.1).hd p.2)
        (Node.baseMap θ (hA (hc_of hϖ hn0 (𝔪 p.1) (D p.1) p.2)) a)) := lv.L.hχ p
  have h1 := levelEquiv_compat hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv (e l) (he l)
    (hfe l) hinj hf hrad hm r hr (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het
        hk Rt hfe lv) hχL
    (fun j ↦ CompletionProd.idem hinj hf hrad j) (fun _ ↦ rfl) b p hεψ hχ'
  have h2 := pieceEquiv_NCongr (Admissible.φT (h := hfe l) φ) ((D p.1).hd p.2)
    (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv p) (hεL p) _ hεψ
        (lv.L.hε p) hθ.out
    (hc_of hϖ hn0 (𝔪 p.1) (D p.1) p.2) hχ'
    (levelEquiv hxy hinj hf hrad D r (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin
        het hk Rt hfe lv) hχL
      (fun j ↦ CompletionProd.idem hinj hf hrad j) (fun _ ↦ rfl) ((1 : FormalPatchLevel.Hat (f l))
          ⊗ₜ b) p)
  have hR : (kappa3F lv.L lv.M hθ.out (Ideal.Quotient.mk _ (toNFall hxy hϖ hn0 𝔪 hJ hres D hinjk
      hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv
      (PhiP hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv hinj hf hrad
          r hχL hεL ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ b))))).1 p =
      pieceEquiv (f l) (Admissible.φT (h := hfe l) φ) ((D p.1).hd p.2) (χL hxy hϖ hn0 𝔪 hJ hres D
          hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv p)
        (lv.L.ε p) _ (lv.L.hε p) hθ.out (hc_of hϖ hn0 (𝔪 p.1) (D p.1) p.2) hχ'
        (Ideal.Quotient.mk _ (NCongr (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin
            het hk Rt hfe lv p) (hεL p)
          (levelEquiv hxy hinj hf hrad D r (χL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc
              hfin het hk Rt hfe lv) hχL
            (fun j ↦ CompletionProd.idem hinj hf hrad j) (fun _ ↦ rfl)
            ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ b) p))) := rfl
  exact Eq.trans rfl (h1.symm.trans (h2.symm.trans hR.symm))


omit [∀ l, IsNoetherianRing (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
lemma ρ_one_tmul (b : B) :
    ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l ((1 : Rt l) ⊗ₜ
        b) =
      @id (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe l).C
          (Ideal.Quotient.mk _ b) := by
  rw [ρ_tmul, map_one, one_mul]
  rfl

set_option maxHeartbeats 1000000 in
-- the comparison unfolds the transported covering `covOf … |>.transport`
set_option maxRecDepth 20000 in
omit [∀ l, IsScalarTower O R (Rt l)] in
include he hm hr in
/-- **The hypothesis `hκ` of `patchEquivOfCompat`**: `κ (1 ⊗ ρ z) = φ₂ z mod J`. -/
theorem kappaF_one_tmul_ρ (z : Rt l ⊗[R] B) :
    kappaF lv.L lv.M hθ.out ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ
        ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l z) =
      Ideal.Quotient.mk _ (φ₂ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt
          hfe lv hinj hf hrad r hχL hεL z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
  | add z w hz hw => rw [map_add, TensorProduct.tmul_add, map_add, hz, hw, map_add, map_add]
  | tmul c b =>
    have hz : (c ⊗ₜ[R] b : Rt l ⊗[R] B) = algebraMap (Rt l) _ c * ((1 : Rt l) ⊗ₜ b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hmul : ∀ x y : (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt
        hfe l).C, (1 : FormalPatchLevel.Hat (f l)) ⊗ₜ[Rt l] (x * y) =
        ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ[Rt l] x) * ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ y) :=
      fun x y ↦ by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hc : (1 : FormalPatchLevel.Hat (f l)) ⊗ₜ[Rt l]
        algebraMap (Rt l) (covL hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt
            hfe l).C c =
        algebraMap (FormalPatchLevel.Hat (f l)) _ (algebraMap (Rt l) _ c) := by
      rw [Algebra.algebraMap_eq_smul_one c, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.smul_def, mul_one]
    rw [hz, map_mul, AlgHom.commutes, hmul, map_mul, hc, AlgEquiv.commutes, map_mul,
      AlgHom.commutes, map_mul, ρ_one_tmul, kappaF_one_tmul hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk
          φ hφu hφv ψc hfin het hk Rt hfe he lv hinj hf hrad r hχL
        hεL hm hr b]
    rfl

set_option maxRecDepth 20000 in
/-- **S6 G3 (generic): the level-`l` patched algebra of the M2 lift is `Rt l ⊗_R B`.** For a
chart `R` with nodes `x y = ϖⁿ`, the special-fibre covering `covOf …` defined by an
`R`-algebra `B` (with chosen Kummer data `D` at the nodes), and a level datum `lv` of a tower
`Rt` (formal node coordinates `χL` = the chart coordinates `hχL`, level nodes `𝔪'` reducing
into the special-fibre nodes `hm`, lifted idempotents = the Lemma F idempotents `hεL`), if
`(Rt l ⊗_R B)[1/f]` is formally étale over `Rt l`, then `Rt l ⊗_R B` is the patched algebra
`lv.G` (`FormalPatchLevel.patchEquivOfCompat`). -/
def levelPatchEquiv (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
    [Algebra.FormallyEtale (Rt l) (Localization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (f l)))] :
    Rt l ⊗[R] B ≃ₐ[Rt l] lv.G hθ.out :=
  haveI := flat_NFall lv.L lv.M hO lv.hflat lv.hidem lv.hfχ lv.hcidem
  FormalPatchLevel.patchEquivOfCompat (f l) (J θ) lv.hJ lv.σP (kappaF lv.L lv.M hθ.out)
    (exists_φ₁ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he
        lv).choose (φ₂ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv
            hinj hf hrad r hχL hεL)
    (ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he l) (exists_φ₁ hxy
        hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he lv).choose_spec.1
    (exists_φ₁ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he
        lv).choose_spec.2
    (kappaF_one_tmul_ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe he
        lv hinj hf hrad r hχL hεL hm hr) lv.hfP
    (noTorsion_NFall lv.L lv.M lv.hflat lv.hidem lv.hfχ lv.hcidem lv.hreg)
    (isBaseChange_φ₂ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk Rt hfe lv
        hinj hf hrad r hχL hεL)

end

end FormalLevel

end SemistableReduction
