/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NormOverlapLevel
import TemperedFundamentalGroups.SemistableReduction.TateOmegaNormCWitness

/-!
# Morphisms of special-fibre pairs and naturality of the overlap datum (MR12, interface I2)

A *special-fibre pair* over rings `S₀`, `S₁` with elements `a₀ ∈ S₀`, `a₁ ∈ S₁` is a pair of
algebras `C₀`, `C₁` with an identification `ω : C₀[1/a₀] → C₁[1/a₁]` (in the Tate case, `S₀`,
`S₁` are the special fibres of the two charts, `a₀ = h̄`, `a₁ = h̄'`, and `ω` is the overlap
datum `TateGlue0.OmegaC`). This file is generic:

* `OmegaPair.awayMap`: `C[1/s] → C'[1/s]` induced by an `S`-algebra map `C → C'`
  (`awayMap_algebraMap`, `awayMap_id`, `awayMap_comp`);
* **`OmegaPair.Hom`**: a morphism of pairs, i.e. algebra maps `f₁ : C₁ → C₁'`, `f₀ : C₀ → C₀'`
  with `ω' ∘ f₀ = f₁ ∘ ω` on `C₀` (hence on `C₀[1/a₀]`, `Hom.comm`), `Hom.id`, `Hom.comp`,
  `Hom.ext`;
* `OmegaPair.csMap`: the reduction `B/IB → B'/IB'` over `R/I` of a map `B → B'` over `R`;
* **`NormOverlap.omegaEquiv_mul_pow_field`**, **`NormOverlap.omegaEquiv_natural`**: the overlap
  datum `NormOverlap.omegaEquiv` of the normalisations `B₀`, `B₁` of `A₀`, `A₁` in a field `L` is
  characterised by `ω(b̄₀) · ā₁ⁿ = b̄₁` whenever `b₀ a₁ⁿ = b₁` in `L`, and it is natural for ring
  maps `L → L'` compatible with `A₀`, `A₁` (and the induced maps of normalisations);
* `NormOverlap.awayMap_awayCongr_symm`; **`TateGlue0.omegaNorm_natural`**,
  **`TateGlue0.omegaNormC_natural`** (the Tate instances).
-/

universe u

namespace SemistableReduction

namespace OmegaPair

noncomputable section

section Away

variable {S C C' C'' : Type u} [CommRing S] [CommRing C] [CommRing C'] [CommRing C'']
  [Algebra S C] [Algebra S C'] [Algebra S C''] (s : S)

/-- **`C[1/s] → C'[1/s]`** induced by an `S`-algebra map `f : C → C'`. -/
def awayMap (f : C →ₐ[S] C') :
    Localization.Away (algebraMap S C s) →+* Localization.Away (algebraMap S C' s) :=
  IsLocalization.map (M := Submonoid.powers (algebraMap S C s))
    (T := Submonoid.powers (algebraMap S C' s)) _ (f : C →+* C')
    (Submonoid.powers_le.2 ⟨1, by simp⟩)

@[simp]
lemma awayMap_algebraMap (f : C →ₐ[S] C') (c : C) :
    awayMap s f (algebraMap C _ c) = algebraMap C' _ (f c) :=
  IsLocalization.map_eq _ _

lemma awayMap_id : awayMap s (AlgHom.id S C) = RingHom.id _ :=
  IsLocalization.ringHom_ext (Submonoid.powers (algebraMap S C s)) (RingHom.ext fun c ↦ by
    rw [RingHom.comp_apply, awayMap_algebraMap]
    rfl)

lemma awayMap_comp (f : C →ₐ[S] C') (g : C' →ₐ[S] C'') :
    awayMap s (g.comp f) = (awayMap s g).comp (awayMap s f) :=
  IsLocalization.ringHom_ext (Submonoid.powers (algebraMap S C s)) (RingHom.ext fun c ↦ by
    simp only [RingHom.comp_apply, awayMap_algebraMap, AlgHom.comp_apply])

end Away

section Pair

variable {S₀ S₁ : Type u} [CommRing S₀] [CommRing S₁] (a₀ : S₀) (a₁ : S₁)
  {C₀ C₁ C₀' C₁' C₀'' C₁'' C₀''' C₁''' : Type u} [CommRing C₀] [CommRing C₁] [CommRing C₀']
  [CommRing C₁'] [CommRing C₀''] [CommRing C₁''] [CommRing C₀'''] [CommRing C₁''']
  [Algebra S₀ C₀] [Algebra S₁ C₁] [Algebra S₀ C₀'] [Algebra S₁ C₁'] [Algebra S₀ C₀'']
  [Algebra S₁ C₁''] [Algebra S₀ C₀'''] [Algebra S₁ C₁''']

/-- **A morphism of special-fibre pairs** `(C₀, C₁, ω) → (C₀', C₁', ω')`: algebra maps
`f₁ : C₁ → C₁'`, `f₀ : C₀ → C₀'` with `ω' ∘ f₀ = f₁ ∘ ω` on `C₀` (`ω`, `ω'` the overlap
identifications `C₀[1/a₀] → C₁[1/a₁]`). -/
structure Hom
    (ω : Localization.Away (algebraMap S₀ C₀ a₀) → Localization.Away (algebraMap S₁ C₁ a₁))
    (ω' : Localization.Away (algebraMap S₀ C₀' a₀) → Localization.Away (algebraMap S₁ C₁' a₁)) where
  /-- the map of the coverings over the chart `S₁` -/
  f₁ : C₁ →ₐ[S₁] C₁'
  /-- the map of the coverings over the chart `S₀` -/
  f₀ : C₀ →ₐ[S₀] C₀'
  hω : ∀ c, ω' (algebraMap C₀' _ (f₀ c)) = awayMap a₁ f₁ (ω (algebraMap C₀ _ c))

variable {a₀ a₁}
  {ω : Localization.Away (algebraMap S₀ C₀ a₀) → Localization.Away (algebraMap S₁ C₁ a₁)}
  {ω' : Localization.Away (algebraMap S₀ C₀' a₀) → Localization.Away (algebraMap S₁ C₁' a₁)}
  {ω'' : Localization.Away (algebraMap S₀ C₀'' a₀) → Localization.Away (algebraMap S₁ C₁'' a₁)}
  {ω''' : Localization.Away (algebraMap S₀ C₀''' a₀) →
    Localization.Away (algebraMap S₁ C₁''' a₁)}

namespace Hom

@[ext]
lemma ext {φ ψ : Hom a₀ a₁ ω ω'} (h₁ : φ.f₁ = ψ.f₁) (h₀ : φ.f₀ = ψ.f₀) : φ = ψ := by
  cases φ; cases ψ; cases h₁; cases h₀; rfl

variable (a₀ a₁ ω) in
/-- The identity morphism. -/
def id : Hom a₀ a₁ ω ω where
  f₁ := AlgHom.id S₁ C₁
  f₀ := AlgHom.id S₀ C₀
  hω c := by rw [awayMap_id]; rfl

/-- Composition of morphisms. -/
def comp (ψ : Hom a₀ a₁ ω' ω'') (φ : Hom a₀ a₁ ω ω') : Hom a₀ a₁ ω ω'' where
  f₁ := ψ.f₁.comp φ.f₁
  f₀ := ψ.f₀.comp φ.f₀
  hω c := by
    rw [AlgHom.comp_apply, ψ.hω, φ.hω, awayMap_comp, RingHom.comp_apply]

@[simp] lemma id_f₁ : (id a₀ a₁ ω).f₁ = AlgHom.id S₁ C₁ := rfl
@[simp] lemma id_f₀ : (id a₀ a₁ ω).f₀ = AlgHom.id S₀ C₀ := rfl
@[simp] lemma comp_f₁ (ψ : Hom a₀ a₁ ω' ω'') (φ : Hom a₀ a₁ ω ω') :
    (ψ.comp φ).f₁ = ψ.f₁.comp φ.f₁ := rfl
@[simp] lemma comp_f₀ (ψ : Hom a₀ a₁ ω' ω'') (φ : Hom a₀ a₁ ω ω') :
    (ψ.comp φ).f₀ = ψ.f₀.comp φ.f₀ := rfl

lemma comp_id (φ : Hom a₀ a₁ ω ω') : φ.comp (id a₀ a₁ ω) = φ := ext rfl rfl

lemma id_comp (φ : Hom a₀ a₁ ω ω') : (id a₀ a₁ ω').comp φ = φ := ext rfl rfl

lemma comp_assoc (χ : Hom a₀ a₁ ω'' ω''') (ψ : Hom a₀ a₁ ω' ω'') (φ : Hom a₀ a₁ ω ω') :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := ext rfl rfl

/-- For ring maps `ω`, `ω'` the compatibility holds on all of `C₀[1/a₀]`. -/
lemma comm
    {ω : Localization.Away (algebraMap S₀ C₀ a₀) →+* Localization.Away (algebraMap S₁ C₁ a₁)}
    {ω' : Localization.Away (algebraMap S₀ C₀' a₀) →+*
      Localization.Away (algebraMap S₁ C₁' a₁)}
    (φ : Hom a₀ a₁ ω ω') (x : Localization.Away (algebraMap S₀ C₀ a₀)) :
    ω' (awayMap a₀ φ.f₀ x) = awayMap a₁ φ.f₁ (ω x) := by
  have h : ω'.comp (awayMap a₀ φ.f₀) = (awayMap a₁ φ.f₁).comp ω :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap S₀ C₀ a₀)) (RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply, awayMap_algebraMap]
      exact φ.hω c)
  exact RingHom.congr_fun h x

end Hom

end Pair

section Cs

variable {R B B' B'' : Type u} [CommRing R] [CommRing B] [CommRing B'] [CommRing B'']
  [Algebra R B] [Algebra R B'] [Algebra R B''] (I : Ideal R)

lemma map_le_comap (g : B →+* B') (hg : ∀ r, g (algebraMap R B r) = algebraMap R B' r) :
    I.map (algebraMap R B) ≤ (I.map (algebraMap R B')).comap g :=
  Ideal.map_le_iff_le_comap.2 fun r hr ↦ by
    rw [Ideal.mem_comap, Ideal.mem_comap, hg]
    exact Ideal.mem_map_of_mem _ hr

/-- **The reduction `B/IB → B'/IB'` over `R/I`** of a ring map `g : B → B'` over `R`. -/
def csMap (g : B →+* B') (hg : ∀ r, g (algebraMap R B r) = algebraMap R B' r) :
    (B ⧸ I.map (algebraMap R B)) →ₐ[R ⧸ I] (B' ⧸ I.map (algebraMap R B')) where
  toRingHom := Ideal.quotientMap _ g (map_le_comap I g hg)
  commutes' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.quotientMap _ g _ (algebraMap (R ⧸ I) (B ⧸ I.map (algebraMap R B))
      (Ideal.Quotient.mk I x)) = _
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.quotientMap_mk, hg]

@[simp]
lemma csMap_mk (g : B →+* B') (hg : ∀ r, g (algebraMap R B r) = algebraMap R B' r) (b : B) :
    csMap I g hg (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (g b) :=
  rfl

lemma csMap_id : csMap I (RingHom.id B) (fun _ ↦ rfl) = AlgHom.id _ _ :=
  AlgHom.ext fun x ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

lemma csMap_comp (g : B →+* B') (hg : ∀ r, g (algebraMap R B r) = algebraMap R B' r)
    (g' : B' →+* B'') (hg' : ∀ r, g' (algebraMap R B' r) = algebraMap R B'' r) :
    csMap I (g'.comp g) (fun r ↦ by rw [RingHom.comp_apply, hg, hg']) =
      (csMap I g' hg').comp (csMap I g hg) :=
  AlgHom.ext fun x ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

lemma csMap_eq_id (g : B →+* B) (hg : ∀ r, g (algebraMap R B r) = algebraMap R B r)
    (h : ∀ b, g b = b) : csMap I g hg = AlgHom.id _ _ :=
  AlgHom.ext fun x ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [csMap_mk, h]
    rfl

lemma csMap_eq_comp (g : B →+* B') (hg : ∀ r, g (algebraMap R B r) = algebraMap R B' r)
    (g' : B' →+* B'') (hg' : ∀ r, g' (algebraMap R B' r) = algebraMap R B'' r)
    (g'' : B →+* B'') (hg'' : ∀ r, g'' (algebraMap R B r) = algebraMap R B'' r)
    (h : ∀ b, g'' b = g' (g b)) : csMap I g'' hg'' = (csMap I g' hg').comp (csMap I g hg) :=
  AlgHom.ext fun x ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AlgHom.comp_apply, csMap_mk, csMap_mk, csMap_mk, h]

end Cs

end

end OmegaPair

namespace NormOverlap

noncomputable section

section AwaySpec

variable {O A W B : Type u} [CommRing O] [CommRing A] [CommRing W] [CommRing B]
  [Algebra O A] [Algebra O W] [Algebra A W] [IsScalarTower O A W] [Algebra A B]
  (a : A) [IsLocalization.Away a W] (I : Ideal O)
  [Algebra (A ⧸ I.map (algebraMap O A)) (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
    (W ⧸ I.map (algebraMap O W))]

/-- `awayEquiv` on the image of `B/JB`. -/
lemma awayEquiv_algebraMap_mk
    (hS : ∀ x : A, algebraMap (A ⧸ I.map (algebraMap O A)) (W ⧸ I.map (algebraMap O W))
      (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A W x)) (b : B) :
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
      (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
    letI := algW (B := B) (W := W) a
    awayEquiv (B := B) a I hS (algebraMap _ (Localization.Away (algebraMap
        (A ⧸ I.map (algebraMap O A)) (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
        (Ideal.Quotient.mk _ a))) (Ideal.Quotient.mk ((I.map (algebraMap O A)).map (algebraMap A B))
        b)) =
      Ideal.Quotient.mk ((I.map (algebraMap O W)).map
        (algebraMap W (Localization.Away (algebraMap A B a))))
        (algebraMap B (Localization.Away (algebraMap A B a)) b) := by
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B ⧸ (I.map (algebraMap O A)).map (algebraMap A B))
    (Ideal.Quotient.mk (I.map (algebraMap O A)) a)
  letI := algW (B := B) (W := W) a
  haveI := AwayAlg.tower (C := B) (W := W) a
  letI := (qmap (B := B) (W := W) a I).toAlgebra
  haveI : IsLocalization.Away (algebraMap (A ⧸ I.map (algebraMap O A))
      (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a))
      (Localization.Away (algebraMap A B a) ⧸ (I.map (algebraMap O W)).map
        (algebraMap W (Localization.Away (algebraMap A B a)))) :=
    NormAway.isLocalization_quotMap (R := W) (I.map (algebraMap O A)) (I.map (algebraMap O W))
      (map_eq I) a
  exact ((IsLocalization.algEquiv (Submonoid.powers (algebraMap (A ⧸ I.map (algebraMap O A))
      (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a)))
    (Localization.Away (algebraMap (A ⧸ I.map (algebraMap O A))
        (B ⧸ (I.map (algebraMap O A)).map (algebraMap A B)) (Ideal.Quotient.mk _ a)))
    (Localization.Away (algebraMap A B a) ⧸ (I.map (algebraMap O W)).map
        (algebraMap W (Localization.Away (algebraMap A B a))))).commutes
      (Ideal.Quotient.mk _ b)).trans (NormAway.quotMap_mk (R := W) (I.map (algebraMap O A))
        (I.map (algebraMap O W)) (map_eq I) b)

end AwaySpec

/-- Every element of `B₀` becomes integral over `A₁` after multiplication by a power of `a₁`
(`W = A₁[1/a₁]` contains `A₀`). -/
lemma exists_mul_pow_eq_field (A₀ W : Type u) {A₁ B₀ B₁ L : Type u} [CommRing A₀] [CommRing A₁]
    [CommRing W] [CommRing B₀] [CommRing B₁] [Field L] [Algebra A₀ W] [Algebra A₁ W]
    [Algebra A₀ L] [Algebra A₁ L] [Algebra W L] [IsScalarTower A₀ W L] [IsScalarTower A₁ W L]
    [Algebra A₀ B₀] [Algebra B₀ L] [IsScalarTower A₀ B₀ L] [IsIntegralClosure B₀ A₀ L]
    [Algebra A₁ B₁] [Algebra B₁ L] [IsScalarTower A₁ B₁ L] [IsIntegralClosure B₁ A₁ L]
    (a₁ : A₁) [IsLocalization.Away a₁ W] (b₀ : B₀) :
    ∃ (b₁ : B₁) (n : ℕ), algebraMap B₀ L b₀ * algebraMap A₁ L a₁ ^ n = algebraMap B₁ L b₁ := by
  have hW : IsIntegral W (algebraMap B₀ L b₀) :=
    ((IsIntegralClosure.isIntegral A₀ L b₀).map (IsScalarTower.toAlgHom A₀ B₀ L)).tower_top
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers a₁) _ hW
  obtain ⟨b₁, hb₁⟩ := (IsIntegralClosure.isIntegral_iff (A := B₁) (R := A₁)).1 hn
  refine ⟨b₁, n, ?_⟩
  rw [hb₁, Submonoid.smul_def, Algebra.smul_def, mul_comm, map_pow]


/-- **`awayCongr` commutes with `awayMap`**: for `e : C ≃ D`, `e' : C' ≃ D'` and maps
`f : C → C'`, `g : D → D'` with `e' ∘ f = g ∘ e`, `f ∘ e⁻¹ = e'⁻¹ ∘ g` after inverting `s`. -/
lemma awayMap_awayCongr_symm {S Ws C D C' D' : Type u} [CommRing S] [CommRing Ws] [CommRing C]
    [CommRing D] [CommRing C'] [CommRing D'] [Algebra S Ws] [Algebra S C] [Algebra S D]
    [Algebra S C'] [Algebra S D'] (s : S) [IsLocalization.Away s Ws] (e : C ≃ₐ[S] D)
    (e' : C' ≃ₐ[S] D') (f : C →ₐ[S] C') (g : D →ₐ[S] D') (h : ∀ x, e' (f x) = g (e x))
    (y : Localization.Away (algebraMap S D s)) :
    letI := AwayAlg.alg (W := Ws) (C := C) s; letI := AwayAlg.alg (W := Ws) (C := D) s
    letI := AwayAlg.alg (W := Ws) (C := C') s; letI := AwayAlg.alg (W := Ws) (C := D') s
    OmegaPair.awayMap s f ((awayCongr (Ws := Ws) s e).symm y) =
      (awayCongr (Ws := Ws) s e').symm (OmegaPair.awayMap s g y) := by
  letI := AwayAlg.alg (W := Ws) (C := C) s
  letI := AwayAlg.alg (W := Ws) (C := D) s
  letI := AwayAlg.alg (W := Ws) (C := C') s
  letI := AwayAlg.alg (W := Ws) (C := D') s
  have key : (OmegaPair.awayMap s f).comp ((awayCongr (Ws := Ws) s e).symm :
      Localization.Away (algebraMap S D s) →+* Localization.Away (algebraMap S C s)) =
      ((awayCongr (Ws := Ws) s e').symm :
        Localization.Away (algebraMap S D' s) →+* Localization.Away (algebraMap S C' s)).comp
        (OmegaPair.awayMap s g) :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap S D s)) (RingHom.ext fun d ↦ by
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [awayCongr_symm_algebraMap, OmegaPair.awayMap_algebraMap, OmegaPair.awayMap_algebraMap,
        awayCongr_symm_algebraMap]
      congr 1
      apply e'.injective
      rw [AlgEquiv.apply_symm_apply, h, AlgEquiv.apply_symm_apply])
  exact RingHom.congr_fun key y

section Main

variable {O A₀ A₁ W B₀ B₁ : Type u} {L : Type u} [CommRing O] [CommRing A₀] [CommRing A₁]
  [CommRing W] [CommRing B₀] [CommRing B₁] [Field L]
  [Algebra O A₀] [Algebra O A₁] [Algebra O W] [Algebra A₀ W] [Algebra A₁ W]
  [IsScalarTower O A₀ W] [IsScalarTower O A₁ W]
  [Algebra A₀ L] [Algebra A₁ L] [Algebra W L] [IsScalarTower A₀ W L] [IsScalarTower A₁ W L]
  [Algebra A₀ B₀] [Algebra B₀ L] [IsScalarTower A₀ B₀ L] [IsIntegralClosure B₀ A₀ L]
  [Algebra A₁ B₁] [Algebra B₁ L] [IsScalarTower A₁ B₁ L] [IsIntegralClosure B₁ A₁ L]
  (a₀ : A₀) (a₁ : A₁) [IsLocalization.Away a₀ W] [IsLocalization.Away a₁ W] (I : Ideal O)
  [Algebra (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))]
  [Algebra (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
    (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
    (W ⧸ I.map (algebraMap O W))]
  (hS₀ : ∀ x : A₀, algebraMap (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))
    (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₀ W x))
  (hS₁ : ∀ x : A₁, algebraMap (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))
    (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₁ W x))
  (ha₀ : algebraMap A₀ L a₀ ≠ 0) (ha₁ : algebraMap A₁ L a₁ ≠ 0)

include hS₀ hS₁ ha₀ ha₁ in
/-- **The overlap datum on generators**: if `b₀ · a₁ⁿ = b₁` in `L`, then
`ω(b̄₀) · ā₁ⁿ = b̄₁` in `(B₁/J)[1/ā₁]`. -/
theorem omegaEquiv_mul_pow_field (b₀ : B₀) (b₁ : B₁) (n : ℕ)
    (h : algebraMap B₀ L b₀ * algebraMap A₁ L a₁ ^ n = algebraMap B₁ L b₁) :
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀))
      (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
      (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
    omegaEquiv (B₀ := B₀) (B₁ := B₁) (L := L) a₀ a₁ I hS₀ hS₁ ha₀ ha₁
        (algebraMap _ _ (Ideal.Quotient.mk ((I.map (algebraMap O A₀)).map (algebraMap A₀ B₀))
          b₀)) *
      algebraMap _ (Localization.Away (algebraMap (A₁ ⧸ I.map (algebraMap O A₁))
        (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) (Ideal.Quotient.mk _ a₁)))
        (Ideal.Quotient.mk ((I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
          (algebraMap A₁ B₁ a₁)) ^ n =
      algebraMap _ (Localization.Away (algebraMap (A₁ ⧸ I.map (algebraMap O A₁))
        (B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) (Ideal.Quotient.mk _ a₁)))
        (Ideal.Quotient.mk ((I.map (algebraMap O A₁)).map (algebraMap A₁ B₁)) b₁) := by
  letI := algW (B := B₀) (W := W) a₀
  letI := algL (B := B₀) a₀ ha₀
  haveI := towerL (B := B₀) a₀ ha₀
  haveI := towerWL (B := B₀) (W := W) a₀ ha₀
  haveI := isIntegralClosure_away (B := B₀) (W := W) a₀ ha₀
  letI := algW (B := B₁) (W := W) a₁
  letI := algL (B := B₁) a₁ ha₁
  haveI := towerL (B := B₁) a₁ ha₁
  haveI := towerWL (B := B₁) (W := W) a₁ ha₁
  haveI := isIntegralClosure_away (B := B₁) (W := W) a₁ ha₁
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀))
    (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
    (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
  apply (awayEquiv (B := B₁) a₁ I hS₁).injective
  rw [map_mul, map_pow]
  change (awayEquiv (B := B₁) a₁ I hS₁) ((awayEquiv (B := B₁) a₁ I hS₁).symm
    (quotEquiv _ (IsIntegralClosure.equiv (R := W) (B := L)
      (A := Localization.Away (algebraMap A₀ B₀ a₀)) (Localization.Away (algebraMap A₁ B₁ a₁)))
      (awayEquiv (B := B₀) a₀ I hS₀ (algebraMap _ _ (Ideal.Quotient.mk _ b₀))))) * _ = _
  rw [AlgEquiv.apply_symm_apply, awayEquiv_algebraMap_mk, awayEquiv_algebraMap_mk,
    awayEquiv_algebraMap_mk, quotEquiv_mk, ← map_pow, ← map_mul]
  congr 1
  apply IsIntegralClosure.algebraMap_injective (Localization.Away (algebraMap A₁ B₁ a₁)) W L
  rw [map_mul, map_pow, IsIntegralClosure.algebraMap_equiv,
    ← IsScalarTower.algebraMap_apply B₀ (Localization.Away (algebraMap A₀ B₀ a₀)) L,
    ← IsScalarTower.algebraMap_apply B₁ (Localization.Away (algebraMap A₁ B₁ a₁)) L,
    ← IsScalarTower.algebraMap_apply B₁ (Localization.Away (algebraMap A₁ B₁ a₁)) L,
    ← IsScalarTower.algebraMap_apply A₁ B₁ L]
  exact h

end Main

section Natural

variable {O A₀ A₁ W B₀ B₁ B₀' B₁' : Type u} {L L' : Type u} [CommRing O] [CommRing A₀]
  [CommRing A₁] [CommRing W] [CommRing B₀] [CommRing B₁] [CommRing B₀'] [CommRing B₁'] [Field L]
  [Field L']
  [Algebra O A₀] [Algebra O A₁] [Algebra O W] [Algebra A₀ W] [Algebra A₁ W]
  [IsScalarTower O A₀ W] [IsScalarTower O A₁ W]
  [Algebra A₀ L] [Algebra A₁ L] [Algebra W L] [IsScalarTower A₀ W L] [IsScalarTower A₁ W L]
  [Algebra A₀ B₀] [Algebra B₀ L] [IsScalarTower A₀ B₀ L] [IsIntegralClosure B₀ A₀ L]
  [Algebra A₁ B₁] [Algebra B₁ L] [IsScalarTower A₁ B₁ L] [IsIntegralClosure B₁ A₁ L]
  [Algebra A₀ L'] [Algebra A₁ L'] [Algebra W L'] [IsScalarTower A₀ W L'] [IsScalarTower A₁ W L']
  [Algebra A₀ B₀'] [Algebra B₀' L'] [IsScalarTower A₀ B₀' L'] [IsIntegralClosure B₀' A₀ L']
  [Algebra A₁ B₁'] [Algebra B₁' L'] [IsScalarTower A₁ B₁' L'] [IsIntegralClosure B₁' A₁ L']
  (a₀ : A₀) (a₁ : A₁) [IsLocalization.Away a₀ W] [IsLocalization.Away a₁ W] (I : Ideal O)
  [Algebra (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))]
  [Algebra (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
    (W ⧸ I.map (algebraMap O W))]
  [IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
    (W ⧸ I.map (algebraMap O W))]
  (hS₀ : ∀ x : A₀, algebraMap (A₀ ⧸ I.map (algebraMap O A₀)) (W ⧸ I.map (algebraMap O W))
    (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₀ W x))
  (hS₁ : ∀ x : A₁, algebraMap (A₁ ⧸ I.map (algebraMap O A₁)) (W ⧸ I.map (algebraMap O W))
    (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A₁ W x))
  (ha₀ : algebraMap A₀ L a₀ ≠ 0) (ha₁ : algebraMap A₁ L a₁ ≠ 0)
  (ha₀' : algebraMap A₀ L' a₀ ≠ 0) (ha₁' : algebraMap A₁ L' a₁ ≠ 0)
  (f : L →+* L') (hf₁ : ∀ x, f (algebraMap A₁ L x) = algebraMap A₁ L' x)
  (g₀ : B₀ →+* B₀') (hg₀ : ∀ x, g₀ (algebraMap A₀ B₀ x) = algebraMap A₀ B₀' x)
  (hg₀L : ∀ b, algebraMap B₀' L' (g₀ b) = f (algebraMap B₀ L b))
  (g₁ : B₁ →+* B₁') (hg₁ : ∀ x, g₁ (algebraMap A₁ B₁ x) = algebraMap A₁ B₁' x)
  (hg₁L : ∀ b, algebraMap B₁' L' (g₁ b) = f (algebraMap B₁ L b))

include hf₁ hg₀L hg₁L in
/-- **Naturality of the overlap datum of normalisations**: for a ring map `f : L → L'` over
`A₁` and maps `g₀ : B₀ → B₀'`, `g₁ : B₁ → B₁'` of the normalisations compatible with `f`,
`ω' ∘ ḡ₀ = ḡ₁ ∘ ω` on `B₀/J`. -/
theorem omegaEquiv_natural (c : B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀)) :
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀))
      (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
      (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B₀' ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀'))
      (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
    letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
      (C := B₁' ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁'))
      (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
    omegaEquiv (B₀ := B₀') (B₁ := B₁') (L := L') a₀ a₁ I hS₀ hS₁ ha₀' ha₁'
        (algebraMap _ _ (OmegaPair.csMap _ g₀ hg₀ c)) =
      OmegaPair.awayMap (Ideal.Quotient.mk _ a₁) (OmegaPair.csMap _ g₁ hg₁)
        (omegaEquiv (B₀ := B₀) (B₁ := B₁) (L := L) a₀ a₁ I hS₀ hS₁ ha₀ ha₁
          (algebraMap _ _ c)) := by
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₀ ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀))
    (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₁ ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁))
    (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₀' ⧸ (I.map (algebraMap O A₀)).map (algebraMap A₀ B₀'))
    (Ideal.Quotient.mk (I.map (algebraMap O A₀)) a₀)
  letI := AwayAlg.alg (W := W ⧸ I.map (algebraMap O W))
    (C := B₁' ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁'))
    (Ideal.Quotient.mk (I.map (algebraMap O A₁)) a₁)
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b₁, n, h⟩ := exists_mul_pow_eq_field A₀ W (B₀ := B₀) (B₁ := B₁) (L := L) a₁ b₀
  have h' : algebraMap B₀' L' (g₀ b₀) * algebraMap A₁ L' a₁ ^ n = algebraMap B₁' L' (g₁ b₁) := by
    rw [hg₀L, hg₁L, ← hf₁, ← map_pow, ← map_mul, h]
  have e := omegaEquiv_mul_pow_field (B₀ := B₀) (B₁ := B₁) (L := L) a₀ a₁ I hS₀ hS₁ ha₀ ha₁ b₀ b₁
    n h
  have e' := omegaEquiv_mul_pow_field (B₀ := B₀') (B₁ := B₁') (L := L') a₀ a₁ I hS₀ hS₁ ha₀' ha₁'
    (g₀ b₀) (g₁ b₁) n h'
  have hu : IsUnit (algebraMap _ (Localization.Away (algebraMap (A₁ ⧸ I.map (algebraMap O A₁))
      (B₁' ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁')) (Ideal.Quotient.mk _ a₁)))
      (Ideal.Quotient.mk ((I.map (algebraMap O A₁)).map (algebraMap A₁ B₁'))
        (algebraMap A₁ B₁' a₁))) := by
    have h0 := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap
      (A₁ ⧸ I.map (algebraMap O A₁)) (B₁' ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁'))
      (Ideal.Quotient.mk _ a₁))) (algebraMap (A₁ ⧸ I.map (algebraMap O A₁))
        (B₁' ⧸ (I.map (algebraMap O A₁)).map (algebraMap A₁ B₁')) (Ideal.Quotient.mk _ a₁))
    rwa [Ideal.Quotient.algebraMap_quotient_map_quotient] at h0
  refine (hu.pow n).mul_left_injective ?_
  have e2 := congrArg (OmegaPair.awayMap (Ideal.Quotient.mk _ a₁)
    (OmegaPair.csMap (I.map (algebraMap O A₁)) g₁ hg₁)) e
  rw [map_mul, map_pow, OmegaPair.awayMap_algebraMap, OmegaPair.awayMap_algebraMap,
    OmegaPair.csMap_mk, OmegaPair.csMap_mk, hg₁] at e2
  rw [OmegaPair.csMap_mk]
  exact e'.trans e2.symm

end Natural

end

end NormOverlap


namespace TateGlue0

open TateTwoChart TateLevel AdmissibleLift

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k) {π b₄ t κ : O}
  {L L' : Type u} [Field L] [Algebra (T0 π b₄ t κ) L] [Algebra (T1 π b₄ t κ) L]
  [Algebra (T01 π b₄ t κ) L] [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L]
  [Field L'] [Algebra (T0 π b₄ t κ) L'] [Algebra (T1 π b₄ t κ) L']
  [Algebra (T01 π b₄ t κ) L'] [IsScalarTower (T1 π b₄ t κ) (T01 π b₄ t κ) L']
  {B₀ B₁ B₀' B₁' : Type u} [CommRing B₀] [CommRing B₁] [CommRing B₀'] [CommRing B₁']
  [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L] [IsScalarTower (T0 π b₄ t κ) B₀ L]
  [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
  [Algebra (T1 π b₄ t κ) B₁] [Algebra B₁ L] [IsScalarTower (T1 π b₄ t κ) B₁ L]
  [IsIntegralClosure B₁ (T1 π b₄ t κ) L]
  [Algebra (T0 π b₄ t κ) B₀'] [Algebra B₀' L'] [IsScalarTower (T0 π b₄ t κ) B₀' L']
  [IsIntegralClosure B₀' (T0 π b₄ t κ) L']
  [Algebra (T1 π b₄ t κ) B₁'] [Algebra B₁' L'] [IsScalarTower (T1 π b₄ t κ) B₁' L']
  [IsIntegralClosure B₁' (T1 π b₄ t κ) L']
  (hρ : ∀ x, algebraMap (T01 π b₄ t κ) L (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L x)
  (h₀ : algebraMap (T0 π b₄ t κ) L (h0 π b₄ t κ) ≠ 0)
  (h₁ : algebraMap (T1 π b₄ t κ) L (h1 π b₄ t κ) ≠ 0)
  (hρ' : ∀ x, algebraMap (T01 π b₄ t κ) L' (rho0 π b₄ t κ x) = algebraMap (T0 π b₄ t κ) L' x)
  (h₀' : algebraMap (T0 π b₄ t κ) L' (h0 π b₄ t κ) ≠ 0)
  (h₁' : algebraMap (T1 π b₄ t κ) L' (h1 π b₄ t κ) ≠ 0)
  (f : L →+* L') (hf₁ : ∀ x, f (algebraMap (T1 π b₄ t κ) L x) = algebraMap (T1 π b₄ t κ) L' x)
  (g₀ : B₀ →+* B₀')
  (hg₀ : ∀ x, g₀ (algebraMap (T0 π b₄ t κ) B₀ x) = algebraMap (T0 π b₄ t κ) B₀' x)
  (hg₀L : ∀ b, algebraMap B₀' L' (g₀ b) = f (algebraMap B₀ L b))
  (g₁ : B₁ →+* B₁')
  (hg₁ : ∀ x, g₁ (algebraMap (T1 π b₄ t κ) B₁ x) = algebraMap (T1 π b₄ t κ) B₁' x)
  (hg₁L : ∀ b, algebraMap B₁' L' (g₁ b) = f (algebraMap B₁ L b))

include hf₁ hg₀L hg₁L in
/-- **Naturality of the overlap datum `omegaNorm`** for a ring map `f : L → L'` over `T1` and
maps of the normalisations `g₀ : B₀ → B₀'`, `g₁ : B₁ → B₁'` compatible with `f`. -/
theorem omegaNorm_natural (c : FormalKummer.Cs θ (T0 π b₄ t κ) B₀) :
    omegaNorm θ hρ' h₀' h₁' (algebraMap (FormalKummer.Cs θ (T0 π b₄ t κ) B₀')
        (Localization.Away (algebraMap (EtaleTower.Ts θ (T0 π b₄ t κ))
          (FormalKummer.Cs θ (T0 π b₄ t κ) B₀')
          (Ideal.Quotient.mk (J θ (R := T0 π b₄ t κ)) (h0 π b₄ t κ))))
        (OmegaPair.csMap (J θ (R := T0 π b₄ t κ)) g₀ hg₀ c)) =
      OmegaPair.awayMap (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ))
        (OmegaPair.csMap (J θ (R := T1 π b₄ t κ)) g₁ hg₁)
        (omegaNorm θ hρ h₀ h₁ (algebraMap (FormalKummer.Cs θ (T0 π b₄ t κ) B₀)
          (Localization.Away (algebraMap (EtaleTower.Ts θ (T0 π b₄ t κ))
            (FormalKummer.Cs θ (T0 π b₄ t κ) B₀)
            (Ideal.Quotient.mk (J θ (R := T0 π b₄ t κ)) (h0 π b₄ t κ)))) c)) := by
  letI := algT0T01 (π := π) (b₄ := b₄) (t := t) (κ := κ)
  haveI := towerT0T01 (π := π) (b₄ := b₄) (t := t) (κ := κ)
  haveI := isLocalization_rho0 π b₄ t κ
  haveI : IsScalarTower (T0 π b₄ t κ) (T01 π b₄ t κ) L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hρ x).symm
  haveI : IsScalarTower (T0 π b₄ t κ) (T01 π b₄ t κ) L' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hρ' x).symm
  letI := alg0s θ π b₄ t κ
  letI := alg1s θ π b₄ t κ
  haveI := isLocalization_alg0s θ π b₄ t κ
  haveI := isLocalization_alg1s θ π b₄ t κ
  exact NormOverlap.omegaEquiv_natural (W := T01 π b₄ t κ) (B₀ := B₀) (B₁ := B₁) (L := L)
    (B₀' := B₀') (B₁' := B₁') (L' := L') (h0 π b₄ t κ) (h1 π b₄ t κ) (RingHom.ker θ)
    (fun _ ↦ rfl) (fun _ ↦ rfl) h₀ h₁ h₀' h₁' f hf₁ g₀ hg₀ hg₀L g₁ hg₁ hg₁L c


section OmegaC

open TateTwoChartNode KummerEtale

variable [Fact (Function.Surjective θ)] {ϖ b₆ ε : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ cov₀' : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (Sp' : TateGlue1.Special1 hκ hπ hπe τ cov₀')
  (e₁ : Sp.C1 ≃ₐ[TateGlue1.T1s θ π b₄ t κ] FormalKummer.Cs θ (T1 π b₄ t κ) B₁)
  (e₁' : Sp'.C1 ≃ₐ[TateGlue1.T1s θ π b₄ t κ] FormalKummer.Cs θ (T1 π b₄ t κ) B₁')
  (f₁ : Sp.C1 →ₐ[TateGlue1.T1s θ π b₄ t κ] Sp'.C1)
  (hf : ∀ x, e₁' (f₁ x) = OmegaPair.csMap (J θ (R := T1 π b₄ t κ)) g₁ hg₁ (e₁ x))

include hf₁ hg₀L hg₁L hf in
/-- **Naturality of the overlap datum `omegaNormC`** (covering `Sp` over `V₁` identified with
`B₁/J` by `e₁`) for maps `f₁ : Sp.C1 → Sp'.C1` compatible with the reductions of `g₁`. -/
theorem omegaNormC_natural (c : FormalKummer.Cs θ (T0 π b₄ t κ) B₀) :
    omegaNormC hκ hπ Sp' e₁' hρ' h₀' h₁' (algebraMap (FormalKummer.Cs θ (T0 π b₄ t κ) B₀')
        (Localization.Away (algebraMap (EtaleTower.Ts θ (T0 π b₄ t κ))
          (FormalKummer.Cs θ (T0 π b₄ t κ) B₀')
          (Ideal.Quotient.mk (J θ (R := T0 π b₄ t κ)) (h0 π b₄ t κ))))
        (OmegaPair.csMap (J θ (R := T0 π b₄ t κ)) g₀ hg₀ c)) =
      OmegaPair.awayMap (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (h1 π b₄ t κ)) f₁
        (omegaNormC hκ hπ Sp e₁ hρ h₀ h₁ (algebraMap (FormalKummer.Cs θ (T0 π b₄ t κ) B₀)
          (Localization.Away (algebraMap (EtaleTower.Ts θ (T0 π b₄ t κ))
            (FormalKummer.Cs θ (T0 π b₄ t κ) B₀)
            (Ideal.Quotient.mk (J θ (R := T0 π b₄ t κ)) (h0 π b₄ t κ)))) c)) := by
  have h := omegaNorm_natural θ hρ h₀ h₁ hρ' h₀' h₁' f hf₁ g₀ hg₀ hg₀L g₁ hg₁ hg₁L c
  letI := alg1s θ π b₄ t κ
  haveI := isLocalization_alg1s θ π b₄ t κ
  exact (congrArg _ h).trans (NormOverlap.awayMap_awayCongr_symm (Ws := T01s θ π b₄ t κ)
    (Ideal.Quotient.mk _ (h1 π b₄ t κ)) e₁ e₁' f₁ _ hf _).symm

end OmegaC

end

end TateGlue0

end SemistableReduction
