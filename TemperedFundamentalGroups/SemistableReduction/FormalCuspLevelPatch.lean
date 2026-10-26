/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalCuspLevel
import TemperedFundamentalGroups.SemistableReduction.FormalLevelPatch

/-!
# The level patches of the M2 lift over a chart without nodes (MR12 T2 S6, step G2c/G3, cusps)

Let `R` be a chart over `O` with the coordinate `s` at the marked points, `B` an `R`-algebra (the
normalisation of the chart in a tame cover) and `D j` local formal cusp forms of the special fibre
`C = B/JB` at the marked points `𝔪 j` (`FormalKummer.PointCuspFormData`). They define the
admissible covering **`FormalCuspLevel.covCuspOf`** of the special fibre without nodes, whose
formal Kummer form is `FormalKummer.cuspEquivOf` (`TateCuspCov.covCusp` is of this form). For a
level datum `lv : LevelTower.Level Rt cov₀ πL hfe l` of its M2 lift (a level ring `Rt l`, the
étale lift `P` over `D(f)` with `σP`, cusp lift data `lv.M`), level points `𝔪' j` over the `𝔪 j`
and level forms `Ψ j` of the `D j` (`FormalCuspLevel.LevelPointForm`: `levelCuspForm` at the cusp,
`levelEtaleForm` at points where the cover is étale), we identify the patched algebra `lv.G` with
`Rt l ⊗_R B` (**`FormalCuspLevel.levelPatchEquiv`**), via `FormalPatchLevel.patchEquivOfCompat`:

* `exists_φ₁` (étale side, `FormalLevel.EtaleIso.exists_φ₁`): `(Rt l ⊗_R B)[1/f]` is `P`;
* `φ₂`, `isBaseChange_φ₂` (formal side): `R̂ ⊗ (Rt l ⊗_R B) ≅ R̂ ⊗_R B ≅ NF` by the level formal
  cusp form `FormalCuspLevel.levelCuspEquiv` (cusp lift `t̃ = s`, `htL`; lifted idempotents = the
  Lemma F idempotents, `hδL`);
* `kappaF_one_tmul_ρ` (compatibility): `κ (1 ⊗ ρ z) = φ₂ z mod J`, from
  `FormalCuspLevel.levelCuspEquiv_compat`.
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

namespace FormalCuspLevel

noncomputable section

open FormalKummer AdmissibleLift FormalLevel

/-- **The admissible covering of the special fibre without nodes** defined by local formal cusp
forms `D j` at the marked points (`FormalKummer.cuspEquivOf`). -/
def covCuspOf {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
    [Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
    {B : Type u} [CommRing B] [Algebra R B] [IsNoetherianRing R]
    {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
    (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j) {s : R} {E : ι → ℕ}
    (D : ∀ j, PointCuspFormData (θ := θ) (B := B) s (E j) (𝔪 j)) {fk : Rs θ R}
    (hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
    (hfk : ∀ j, fk ∈ sIdeal (θ := θ) (𝔪 j))
    (hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fk}).radical)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat fk) (ψ : Polynomial k →ₐ[k] Admissible.Hat fk)
    (hψ : ψ X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s))
    (hfin : Module.Finite (Rs θ R) (Cs θ R B))
    (het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) fk).Etale)
    (hk : ∀ j i, ((D j).d i : k) ≠ 0) :
    Admissible.Covering φ₀ ψ :=
  haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  { C := Cs θ R B
    finite := hfin
    etale := het
    ι := Empty
    idem := Empty.elim
    isIdempotentElem_idem := fun j ↦ j.elim
    e := Empty.elim
    e_pos := fun j ↦ j.elim
    e_ne_zero := fun j ↦ j.elim
    κ := Σ j, Fin (D j).r
    cidem := fun p ↦ CompletionProd.idem hinjk hfk hradk p.1
    isIdempotentElem_cidem := fun p ↦ CompletionProd.isIdempotentElem_idem _ _ _ p.1
    ce := fun p ↦ (D p.1).d p.2
    ce_pos := fun p ↦ (D p.1).hd p.2
    ce_ne_zero := fun p ↦ hk p.1 p.2
    kummer := (cuspEquivOf 𝔪 hJ D hinjk hfk hradk ψ hψ).trans AlgEquiv.uniqueProd.symm }

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
  (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j) {s : R} {E : ι → ℕ}
  (D : ∀ j, PointCuspFormData (θ := θ) (B := B) s (E j) (𝔪 j)) {g : R}
  (hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
  (hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j))
  (hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g))
  (ψk : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g))
  (hψ : ψk X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s))
  (hfin : Module.Finite (Rs θ R) (Cs θ R B))
  (het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale)
  (hk : ∀ j i, ((D j).d i : k) ≠ 0)
  -- the tower of levels
  (Rt : ℕ → Type u) [∀ l, CommRing (Rt l)] [∀ l, Algebra O (Rt l)]
  [∀ l, IsNoetherianRing (Rt l)] [∀ l, Algebra R (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
  {f : ∀ l, Rt l} {e : ∀ l, Rs θ R ≃ₐ[k] (Rt l ⧸ J θ (R := Rt l))}
  (hfe : ∀ l, e l (fbar θ g) = fbar θ (f l))
  (he : ∀ l (r : R), e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Rt l) r))

/-- The covering of the special fibre defined by the cusp forms (`covCuspOf`), abbreviated. -/
abbrev cov₀ : Admissible.Covering φ₀ ψk :=
  covCuspOf 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk

variable (l : ℕ)

/-- The transported covering at level `l` (ring `C = B/JB`, an `Rt l`-algebra via `e l⁻¹`). -/
abbrev covL :=
  (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk).transport (h := hfe l)

/-- `C = B/JB` as an `R`-algebra through `Rt l`. -/
abbrev algRC : Algebra R (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C :=
  Algebra.compHom _ (algebraMap R (Rt l))

/-- The reduction `B → C = B/JB` as an `R`-algebra map (`C` an `R`-algebra through `Rt l`). -/
def mkC : letI := algRC 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l
    B →ₐ[R] (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C :=
  letI := algRC 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l
  { (Ideal.Quotient.mk ((J θ (R := R)).map (algebraMap R B)) : B →+* Cs θ R B) with
    commutes' := fun r ↦ by
      change Ideal.Quotient.mk _ (algebraMap R B r) =
        algebraMap (Rs θ R) (Cs θ R B) ((e l).symm (Ideal.Quotient.mk _ (algebraMap R (Rt l) r)))
      rw [← he l r, AlgEquiv.symm_apply_apply]
      rfl }

/-- **The reduction `ρ : Rt l ⊗_R B → C = B/JB`** (`r ⊗ b ↦ r̄ · b̄`). -/
def ρ : Rt l ⊗[R] B →ₐ[Rt l] (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C :=
  letI := algRC 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l
  haveI : IsScalarTower R (Rt l)
      (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (mkC 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l) fun _ _ ↦ Commute.all _ _

omit [IsSepClosed k] [∀ l, IsNoetherianRing (Rt l)] [∀ l, IsScalarTower O R (Rt l)] in
lemma ρ_tmul (r : Rt l) (b : B) :
    ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l (r ⊗ₜ b) =
      algebraMap (Rt l) _ r * (@id (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C
        (Ideal.Quotient.mk _ b)) := by
  letI := algRC 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l
  haveI : IsScalarTower R (Rt l)
      (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

omit [IsSepClosed k] [∀ l, IsNoetherianRing (Rt l)] [∀ l, IsScalarTower O R (Rt l)] in
lemma ρ_surjective :
    Function.Surjective (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l) := by
  intro c
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (@id (Cs θ R B) c)
  refine ⟨1 ⊗ₜ b, ?_⟩
  rw [ρ_tmul, map_one, one_mul]
  exact hb

omit [IsSepClosed k] [∀ l, IsNoetherianRing (Rt l)] in
lemma ker_ρ : RingHom.ker (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l) =
    (J θ (R := Rt l)).map (algebraMap (Rt l) (Rt l ⊗[R] B)) := by
  have hJR : ∀ r ∈ J θ (R := R), algebraMap R (Rt l) r ∈ J θ (R := Rt l) := by
    intro r hr
    have hle : (J θ (R := R)).map (algebraMap R (Rt l)) ≤ J θ (R := Rt l) := by
      rw [J, J, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hle (Ideal.mem_map_of_mem _ hr)
  set I' := (J θ (R := Rt l)).map (algebraMap (Rt l) (Rt l ⊗[R] B)) with hI'
  let ψk' : (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C →+*
      (Rt l ⊗[R] B) ⧸ I' := Ideal.Quotient.lift _ ((Ideal.Quotient.mk I').comp
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
  have hψ' : ∀ z, ψk' (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l z) =
      Ideal.Quotient.mk I' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul r b =>
      rw [ρ_tmul, map_mul]
      obtain ⟨r', hr'⟩ := Ideal.Quotient.mk_surjective ((e l).symm (Ideal.Quotient.mk _ r))
      have h1 : algebraMap (Rt l) (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C r =
          (@id (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C
            (Ideal.Quotient.mk _ (algebraMap R B r'))) := by
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
    have h := hψ' z
    rw [hz, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h.symm
  · intro hz
    refine (Ideal.map_le_iff_le_comap.mpr ?_) hz
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    change algebraMap (Rs θ R) (Cs θ R B) ((e l).symm (Ideal.Quotient.mk _ a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]

variable (πL : (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk).ι → O)

omit [IsSepClosed k] [∀ l, IsNoetherianRing (Rt l)] in
variable {l} in
/-- **The étale side of the level-`l` patch**: if `(Rt l ⊗_R B)[1/f]` is formally étale over
`Rt l`, it maps isomorphically onto the étale lift `P` of the level datum, compatibly with `σP`
and `ρ`. -/
theorem exists_φ₁ (lv : LevelTower.Level Rt
      (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL hfe l)
    [Algebra.FormallyEtale (Rt l) (Localization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (f l)))] :
    ∃ φ₁ : Rt l ⊗[R] B →ₐ[Rt l] lv.P,
      (letI := φ₁.toRingHom.toAlgebra;
        IsLocalization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (f l)) lv.P) ∧
      ∀ z, lv.σP (Ideal.Quotient.mk _ (φ₁ z)) = algebraMap _ _
        (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l z) :=
  EtaleIso.exists_φ₁ (J θ (R := Rt l)) (f l)
    (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l)
    (ρ_surjective 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l)
    (ker_ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l) lv.σP lv.hJ

/-! ### The formal side -/

variable {l} (lv : LevelTower.Level Rt (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL hfe l)
  {𝔪' : ι → Ideal (Rt l)} [∀ j, (𝔪' j).IsMaximal] (hinj : Function.Injective 𝔪')
  (hf : ∀ j, f l ∈ 𝔪' j) (hrad : ⨅ j, 𝔪' j ≤ (Ideal.span {f l}).radical)
  (hm : ∀ j, (𝔪' j).map (red θ (e l)) ≤ sIdeal (θ := θ) (𝔪 j))
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]
  (Ψ : ∀ j, LevelPointForm (redHat 𝔪 (e l) (he l) hm j) (D j))
  (htL : lv.M.t = algebraMap R (FormalPatchLevel.Hat (f l)) s)
  (hδL : ∀ p, lv.M.δ p = CompletionProd.idem hinj hf hrad p.1)

/-- The level formal cusp form with the lift data of the level datum. -/
def PhiP : FormalPatchLevel.Hat (f l) ⊗[R] B ≃ₐ[FormalPatchLevel.Hat (f l)]
    ∀ p : (Σ j, Fin (D j).r), CPiece (f l) (lv.M.δ p) lv.M.t ((D p.1).d p.2) :=
  levelCuspEquiv 𝔪 D (e l) (he l) hinj hf hrad hm Ψ lv.M.t htL lv.M.δ hδL

/-- `∏_p CPiece_p ≃ NFall` (no node factors). -/
def toNFall : (∀ p : (Σ j, Fin (D j).r), CPiece (f l) (lv.M.δ p) lv.M.t ((D p.1).d p.2))
    ≃ₐ[FormalPatchLevel.Hat (f l)] NFall lv.L lv.M where
  toFun x s := match s with
    | .inl j => (show Empty from j).elim
    | .inr p => x p
  invFun y p := y (.inr p)
  left_inv _ := rfl
  right_inv _ := funext fun s ↦ match s with
    | .inl j => (show Empty from j).elim
    | .inr _ => rfl
  map_mul' _ _ := funext fun s ↦ match s with
    | .inl j => (show Empty from j).elim
    | .inr _ => rfl
  map_add' _ _ := funext fun s ↦ match s with
    | .inl j => (show Empty from j).elim
    | .inr _ => rfl
  commutes' _ := funext fun s ↦ match s with
    | .inl j => (show Empty from j).elim
    | .inr _ => rfl

/-- **The formal side `R̂ ⊗_{Rt l} (Rt l ⊗_R B) ≃ NF`** of the level-`l` patch. -/
def PhiT : FormalPatchLevel.Hat (f l) ⊗[Rt l] (Rt l ⊗[R] B) ≃ₐ[FormalPatchLevel.Hat (f l)]
    NFall lv.L lv.M :=
  (Algebra.TensorProduct.cancelBaseChange R (Rt l) (FormalPatchLevel.Hat (f l))
    (FormalPatchLevel.Hat (f l)) B).trans
    ((PhiP 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf hrad hm Ψ htL
      hδL).trans (toNFall 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe πL lv))

/-- `φ₂ : Rt l ⊗_R B → NF`, `z ↦ PhiT (1 ⊗ z)`. -/
def φ₂ : Rt l ⊗[R] B →ₐ[Rt l] NFall lv.L lv.M where
  toFun z := PhiT 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf hrad hm Ψ
    htL hδL ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ z)
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

omit [IsSepClosed k] [∀ l, IsScalarTower O R (Rt l)]
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
theorem isBaseChange_φ₂ : IsBaseChange (FormalPatchLevel.Hat (f l))
    (φ₂ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf hrad hm Ψ htL
      hδL).toLinearMap :=
  IsBaseChange.of_equiv (PhiT 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf
    hrad hm Ψ htL hδL).toLinearEquiv fun _ ↦ rfl

omit [IsSepClosed k] [∀ l, IsScalarTower O R (Rt l)]
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
lemma φ₂_one_tmul (b : B) :
    φ₂ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf hrad hm Ψ htL hδL
        ((1 : Rt l) ⊗ₜ b) =
      toNFall 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe πL lv
        (PhiP 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf hrad hm Ψ htL hδL
          ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ b)) := by
  change PhiT 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf hrad hm Ψ
    htL hδL ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ ((1 : Rt l) ⊗ₜ b)) = _
  rw [PhiT, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

set_option maxHeartbeats 1000000 in
-- the comparison unfolds the transported covering `covCuspOf … |>.transport`
set_option maxRecDepth 20000 in
omit [IsSepClosed k] [∀ l, IsScalarTower O R (Rt l)] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **`κ` on `1 ⊗ b̄`** (the hypothesis `hκ` of `patchEquivOfCompat` on generators). -/
theorem kappaF_one_tmul (b : B) :
    kappaF lv.L lv.M hθ.out ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ
        (@id (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C
            (Ideal.Quotient.mk _ b))) =
      Ideal.Quotient.mk _ (φ₂ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf
        hrad hm Ψ htL hδL ((1 : Rt l) ⊗ₜ b)) := by
  haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  apply (kappa3F lv.L lv.M hθ.out).injective
  have hL := kappa3F_kappaF_one_tmul (f l) (hfe l)
    (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) hθ.out lv.L lv.M
    (@id (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk).C (Ideal.Quotient.mk _ b))
  refine hL.trans ?_
  rw [φ₂_one_tmul]
  refine Prod.ext (funext fun j ↦ (show Empty from j).elim) (funext fun p ↦ ?_)
  have h1 := levelCuspEquiv_compat 𝔪 hJ D hinjk hfk hradk ψk hψ (e l) (he l) (hfe l) hinj hf hrad
    hm Ψ lv.M.t htL lv.M.δ hδL b p (lv.M.hδ p) lv.M.ht
  exact h1.symm

omit [IsSepClosed k] [∀ l, IsNoetherianRing (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
lemma ρ_one_tmul (b : B) :
    ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he (l := l) ((1 : Rt l) ⊗ₜ b) =
      @id (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C
          (Ideal.Quotient.mk _ b) := by
  rw [ρ_tmul, map_one, one_mul]

set_option maxHeartbeats 1000000 in
-- the comparison unfolds the transported covering `covCuspOf … |>.transport`
set_option maxRecDepth 20000 in
omit [IsSepClosed k] [∀ l, IsScalarTower O R (Rt l)] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **The hypothesis `hκ` of `patchEquivOfCompat`**: `κ (1 ⊗ ρ z) = φ₂ z mod J`. -/
theorem kappaF_one_tmul_ρ (z : Rt l ⊗[R] B) :
    kappaF lv.L lv.M hθ.out ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ
        ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l z) =
      Ideal.Quotient.mk _ (φ₂ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf
        hrad hm Ψ htL hδL z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
  | add z w hz hw => rw [map_add, TensorProduct.tmul_add, map_add, hz, hw, map_add, map_add]
  | tmul c b =>
    have hz : (c ⊗ₜ[R] b : Rt l ⊗[R] B) = algebraMap (Rt l) _ c * ((1 : Rt l) ⊗ₜ b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hmul : ∀ x y : (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C,
        (1 : FormalPatchLevel.Hat (f l)) ⊗ₜ[Rt l] (x * y) =
        ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ[Rt l] x) * ((1 : FormalPatchLevel.Hat (f l)) ⊗ₜ y) :=
      fun x y ↦ by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hc : (1 : FormalPatchLevel.Hat (f l)) ⊗ₜ[Rt l]
        algebraMap (Rt l) (covL 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe l).C c =
        algebraMap (FormalPatchLevel.Hat (f l)) _ (algebraMap (Rt l) _ c) := by
      rw [Algebra.algebraMap_eq_smul_one c, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.smul_def, mul_one]
    rw [hz, map_mul, AlgHom.commutes, hmul, map_mul, hc, AlgEquiv.commutes, map_mul,
      AlgHom.commutes, map_mul, ρ_one_tmul, kappaF_one_tmul 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin
        het hk Rt hfe he πL lv hinj hf hrad hm Ψ htL hδL b]
    rfl

set_option maxRecDepth 20000 in
/-- **S6 G2c/G3 (generic, cusps): the level-`l` patched algebra of the M2 lift of a covering
without nodes is `Rt l ⊗_R B`.** For a chart `R` with the coordinate `s` at the marked points, the
special-fibre covering `covCuspOf …` defined by an `R`-algebra `B` (local formal cusp forms `D j`
at the marked points) and a level datum `lv` of a tower `Rt` (cusp coordinate `t̃ = s`, `htL`;
level points `𝔪'` reducing into the special-fibre points, `hm`; lifted idempotents = the Lemma F
idempotents, `hδL`; level forms `Ψ j` of the `D j`), if `(Rt l ⊗_R B)[1/f]` is formally étale over
`Rt l`, then `Rt l ⊗_R B` is the patched algebra `lv.G` (`FormalPatchLevel.patchEquivOfCompat`). -/
def levelPatchEquiv (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
    [Algebra.FormallyEtale (Rt l) (Localization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (f l)))] :
    Rt l ⊗[R] B ≃ₐ[Rt l] lv.G hθ.out :=
  haveI := flat_NFall lv.L lv.M hO lv.hflat lv.hidem lv.hfχ lv.hcidem
  FormalPatchLevel.patchEquivOfCompat (f l) (J θ) lv.hJ lv.σP (kappaF lv.L lv.M hθ.out)
    (exists_φ₁ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv).choose
    (φ₂ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf hrad hm Ψ htL hδL)
    (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he l)
    (exists_φ₁ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv).choose_spec.1
    (exists_φ₁ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv).choose_spec.2
    (kappaF_one_tmul_ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf hrad hm
      Ψ htL hδL) lv.hfP
    (noTorsion_NFall lv.L lv.M lv.hflat lv.hidem lv.hfχ lv.hcidem lv.hreg)
    (isBaseChange_φ₂ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt hfe he πL lv hinj hf hrad hm Ψ
      htL hδL)

end

end FormalCuspLevel

end SemistableReduction
