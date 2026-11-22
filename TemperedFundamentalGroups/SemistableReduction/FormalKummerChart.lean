/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerAssemble
import TemperedFundamentalGroups.SemistableReduction.EtaleResidue

/-!
# The formal Kummer form of the special fibre of a chart (MR12 T2 S5.4)

Let `R` be a Noetherian `O`-algebra (a chart of a model over the level ring `O`, residue map
`θ : O → k` onto a separably closed field), `x, y ∈ R` with `x y = ϖⁿ` (`θ ϖ = 0`, `n ≥ 1`) the
node coordinates, `B` an `R`-algebra (the normalisation of the chart in a cover) and `𝔪ⱼ` finitely
many `k`-rational maximal ideals of `R` over `ϖ` (the nodes). If `B` is tamely Kummer at every
`𝔪ⱼ` (`IsKummerNormAt ϖ n M' x y B 𝔪ⱼ`, e.g. from `IsTameKummerAt.isKummerNormAt`), and the nodes
are exactly the zero set of `f̄` on the special fibre `R̄ = R/J`, then
(**`FormalKummer.exists_kummer`**) the special fibre `C = B/JB` is formally Kummer along `V(f̄)`:

  `R̂ ⊗_{R̄} C ≅ ∏_{(j, i)} (R̂/(1 − εⱼ)) ⊗_{k[u,v]/(uv)} k[s,t]/(st)`  (`u ↦ s^{dⱼᵢ}`, `dⱼᵢ ∣ M'`)

with respect to any formal node coordinates `φ : k[u,v]/(uv) → R̂` with `φ u = x̄`, `φ v = ȳ`:
the `kummer` field of `Admissible.Covering` (lead decision D1 after continuation 28: the split form
holds after a finite separable constant extension; here the residue field is separably closed, so
the étale neighbourhoods of `IsKummerNormAt` have trivial residue field extensions,
`EtaleResidue.surjective_of_isSepClosed'`).

Proof: `FormalKummer.nodeEquiv` at every node, assembled by `FormalKummer.assembleEquiv`.

**Residue hypothesis (S5.7, refactor of `[IsSepClosed k]`):** the chosen data
`KummerNormAtData` carry the triviality of the residue field extension of the étale
neighbourhood (`resSurj`); the formal Kummer forms `nodeEquivOf`, `kummerEquivOf` and everything
built on them need no assumption on `k`. Separable closedness enters only where the data are
chosen (`KummerNormAtData.ofIsKummerNormAt`, `ofIsKummerNormAtK`; same for `CuspNormAtData`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

section Res

variable {O : Type u} [CommRing O] (ϖ : O) (n M' : ℕ) {N : Type u} [CommRing N] (u v : N)
  (B : Type u) [CommRing B] [Algebra N B]

/-- **`IsKummerNormAt` over an étale neighbourhood with trivial residue field extension** (S5.7):
as `IsKummerNormAt`, and moreover `N → N₁/𝔫` is surjective. This is the form in which the formal
Kummer forms use the étale-local Kummer data; it follows from `IsKummerNormAt` when the residue
field at `𝔪` is separably closed (`IsKummerNormAt.isKummerNormAtRes`), and over a finite residue
field after a finite unramified base change. -/
def IsKummerNormAtRes [Algebra O N] (𝔪 : Ideal N) : Prop :=
  ∃ (N₁ : Type u) (_ : CommRing N₁) (_ : Algebra N N₁) (_ : Algebra.Etale N N₁) (𝔫 : Ideal N₁)
    (_ : 𝔫.IsPrime) (_ : 𝔫.comap (algebraMap N N₁) = 𝔪),
    Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap N N₁)) ∧
      KummerNormData ϖ n M' u v B N₁ 𝔫 ((algebraMap N N₁).comp (algebraMap O N))

variable {ϖ n M' u v B}

lemma IsKummerNormAtRes.isKummerNormAt [Algebra O N] {𝔪 : Ideal N}
    (h : IsKummerNormAtRes ϖ n M' u v B 𝔪) : IsKummerNormAt ϖ n M' u v B 𝔪 := by
  obtain ⟨N₁, i₁, i₂, i₃, 𝔫, i₄, h𝔫, -, hd⟩ := h
  exact ⟨N₁, i₁, i₂, i₃, 𝔫, i₄, h𝔫, hd⟩

/-- **At a point with separably closed residue field** (a quotient of a separably closed `K'`),
`IsKummerNormAt` gives `IsKummerNormAtRes` (`EtaleResidue.surjective_of_isSepClosed'`). -/
lemma IsKummerNormAt.isKummerNormAtRes [Algebra O N] {𝔪 : Ideal N} [𝔪.IsMaximal] {K' : Type*}
    [Field K'] [IsSepClosed K'] (ρ : K' →+* N ⧸ 𝔪) (hρ : Function.Surjective ρ)
    (h : IsKummerNormAt ϖ n M' u v B 𝔪) : IsKummerNormAtRes ϖ n M' u v B 𝔪 := by
  obtain ⟨N₁, i₁, i₂, i₃, 𝔫, i₄, h𝔫, hd⟩ := h
  exact ⟨N₁, i₁, i₂, i₃, 𝔫, i₄, h𝔫, EtaleResidue.surjective_of_isSepClosed' 𝔪 𝔫 h𝔫 ρ hρ, hd⟩

end Res

namespace FormalKummer

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B]

attribute [local instance] algRN

/-- The special fibre of an ideal containing `J`. -/
abbrev sIdeal (𝔪 : Ideal R) : Ideal (Rs θ R) := 𝔪.map (Ideal.Quotient.mk (J θ (R := R)))

variable (θ) in
/-- The completion of the special fibre at a node. -/
abbrev Tn (𝔪 : Ideal R) : Type u := AdicCompletion (sIdeal (θ := θ) 𝔪) (Rs θ R)

/-- **The data of `IsKummerNormAt` as a type** (refactor R1): an étale neighbourhood `N₁ ⊇ 𝔫`
of `𝔪`, the node relation `x y = ϖⁿ` there, and the splitting `Φ` of `N₁ ⊗_R B` into Kummer
nodes. Choosing these data once (`KummerNormAtData.ofIsKummerNormAt`) makes the formal Kummer
forms `nodeEquivOf`, `kummerEquivOf` definitions in terms of `Φ`, so that their lifts to the
levels `O/ϖⁿ⁺¹` (S6) can be compared with them. -/
structure KummerNormAtData (ϖ : O) (n M' : ℕ) (x y : R) (B : Type u) [CommRing B] [Algebra R B]
    (𝔪 : Ideal R) where
  /-- The étale neighbourhood. -/
  N₁ : Type u
  [commRing : CommRing N₁]
  [algebra : Algebra R N₁]
  [etale : Algebra.Etale R N₁]
  /-- The point of `N₁` over `𝔪`. -/
  𝔫 : Ideal N₁
  [isPrime : 𝔫.IsPrime]
  comap_eq : 𝔫.comap (algebraMap R N₁) = 𝔪
  /-- The number of Kummer factors. -/
  r : ℕ
  /-- The local degrees. -/
  d : Fin r → ℕ
  hd : ∀ i, 0 < d i
  hdM : ∀ i, d i ∣ M'
  /-- The Kummer nodes are `uv = ϖ^{n / dᵢ}`: `dᵢ ∣ n`. -/
  hmd : ∀ i, n / d i * d i = n
  huv : letI : Algebra O N₁ := ((algebraMap R N₁).comp (algebraMap O R)).toAlgebra
    algebraMap R N₁ x * algebraMap R N₁ y = algebraMap O N₁ (ϖ ^ n)
  /-- The node chart `O[u, v]/(uv − ϖⁿ) → N₁` is étale. -/
  het : letI : Algebra O N₁ := ((algebraMap R N₁).comp (algebraMap O R)).toAlgebra
    (Node.lift _ _ huv).toRingHom.Etale
  /-- The residue field extension at `𝔫` is trivial (S5.7: the only residue hypothesis of the
  formal Kummer forms; from a separably closed residue field, `ofIsKummerNormAt`). -/
  resSurj : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R N₁))
  /-- The Kummer splitting. -/
  Φ : letI : Algebra O N₁ := ((algebraMap R N₁).comp (algebraMap O R)).toAlgebra
    N₁ ⊗[R] B ≃ₐ[N₁] ∀ i, @KummerNodeFactor O _ (ϖ ^ (n / d i)) (d i) N₁ _
      (nodeAlgebra N₁ (ϖ ^ (n / d i)) (d i) (by rw [← pow_mul, hmd i]; exact huv))

attribute [instance] KummerNormAtData.commRing KummerNormAtData.algebra KummerNormAtData.etale
  KummerNormAtData.isPrime

/-- The exponents `mᵢ = n / dᵢ` of the Kummer nodes `uv = ϖ^{mᵢ}` (so that the deformation
parameters `ϖ^(n / dᵢ)` of the M2 lift are definitionally those of the splitting). -/
abbrev KummerNormAtData.m {ϖ : O} {n M' : ℕ} {x y : R} {𝔪 : Ideal R}
    (D : KummerNormAtData ϖ n M' x y B 𝔪) (i : Fin D.r) : ℕ :=
  n / D.d i

/-- **The chosen data of `IsKummerNormAtRes`** (an étale neighbourhood with trivial residue field
extension; no assumption on the residue field). -/
def KummerNormAtData.ofIsKummerNormAtRes {ϖ : O} {n M' : ℕ} {x y : R} {𝔪 : Ideal R}
    (h : IsKummerNormAtRes ϖ n M' x y B 𝔪) : KummerNormAtData ϖ n M' x y B 𝔪 :=
  Classical.choice (by
    obtain ⟨N₁, _, _, _, 𝔫, _, h𝔫, hsurj, huv, het, -, -, r, m, d, hd, hdM, hmd, ⟨Φ⟩⟩ := h
    obtain rfl : m = fun i ↦ n / d i :=
      funext fun i ↦ (Nat.div_eq_of_eq_mul_left (hd i) (hmd i).symm).symm
    exact ⟨{ N₁ := N₁, 𝔫 := 𝔫, comap_eq := h𝔫, r := r, d := d, hd := hd,
             hdM := hdM, hmd := hmd, huv := huv, het := het, resSurj := hsurj, Φ := Φ }⟩)

/-- **The chosen data of `IsKummerNormAt`**, at a point `𝔪` whose residue field is a quotient of
a separably closed field `K'` (`ρ`), so that the residue field extension of the étale
neighbourhood is trivial (`IsKummerNormAt.isKummerNormAtRes`). -/
def KummerNormAtData.ofIsKummerNormAt {ϖ : O} {n M' : ℕ} {x y : R} {𝔪 : Ideal R} [𝔪.IsMaximal]
    {K' : Type*} [Field K'] [IsSepClosed K'] (ρ : K' →+* R ⧸ 𝔪) (hρ : Function.Surjective ρ)
    (h : IsKummerNormAt ϖ n M' x y B 𝔪) : KummerNormAtData ϖ n M' x y B 𝔪 :=
  ofIsKummerNormAtRes (h.isKummerNormAtRes ρ hρ)

/-- The residue map `k → R/𝔪` at a `k`-rational point `𝔪 ⊇ J` is surjective. -/
lemma factor_comp_surjective {𝔪 : Ideal R} (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R))) :
    Function.Surjective ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R))) := by
  intro z
  obtain ⟨o, ho⟩ := hres z
  refine ⟨θ o, ?_⟩
  rw [RingHom.comp_apply, QuadNodeTower.algK_θ, Ideal.Quotient.factor_mk]
  exact ho

/-- **The chosen data of `IsKummerNormAt` at a `k`-rational point `𝔪 ⊇ J`** (`k` separably
closed; `ofIsKummerNormAt` for the residue map `k → R/𝔪`). -/
def KummerNormAtData.ofIsKummerNormAtK [IsSepClosed k] {ϖ : O} {n M' : ℕ} {x y : R}
    {𝔪 : Ideal R} [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
    (h : IsKummerNormAt ϖ n M' x y B 𝔪) : KummerNormAtData ϖ n M' x y B 𝔪 :=
  ofIsKummerNormAt ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R)))
    (factor_comp_surjective hJ hres) h

set_option linter.unusedVariables false in
-- `hres` is no longer used (S5.7: the residue hypothesis is `D.resSurj`); it is kept so that the
-- downstream spellings `nodeEquivOf … 𝔪 hJ hres D` are unchanged
/-- **The local formal Kummer form at a node**, defined from the data `D` (`nodeEquiv` for the
splitting `D.Φ`; the residue field extension of `D` is trivial, `D.resSurj`). -/
def nodeEquivOf {ϖ : O} {n M' : ℕ} {x y : R}
    (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
    (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
    (D : KummerNormAtData ϖ n M' x y B 𝔪) :
    letI : ∀ i, Algebra (A (0 : k) (D.d i)) (Tn θ 𝔪) :=
      fun i ↦ (chartAlg (k := k)
        (xy_bar (θ := θ) hxy (by rw [map_pow, hϖ, zero_pow hn0.ne'])) (D.hd i) _)
    Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B ≃ₐ[Tn θ 𝔪]
      ∀ i, Tn θ 𝔪 ⊗[A (0 : k) (D.d i)] KummerEtale.B (0 : k) :=
  letI : Algebra O D.N₁ := ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra
  haveI : IsScalarTower O R D.N₁ := IsScalarTower.of_algebraMap_eq' rfl
  have hn : θ (ϖ ^ n) = 0 := by rw [map_pow, hϖ, zero_pow hn0.ne']
  have hc : ∀ i, θ (ϖ ^ D.m i) = 0 := fun i ↦ by
    have : 0 < D.m i := Nat.pos_of_ne_zero fun h0 ↦ hn0.ne' (by
      rw [← D.hmd i]; exact (congrArg (· * D.d i) h0).trans (zero_mul _))
    rw [map_pow, hϖ, zero_pow this.ne']
  have hJ𝔫 : J θ (R := D.N₁) ≤ D.𝔫 := by
    rw [← J_N₁_eq θ R D.N₁, Ideal.map_le_iff_le_comap, D.comap_eq]
    exact hJ
  have hcomap : (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁)))).comap
      (algebraMap (Rs θ R) (Ns θ D.N₁)) = sIdeal (θ := θ) 𝔪 := by
    ext z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.mem_comap, algebraMap_RN, Ideal.mem_quotient_iff_mem hJ𝔫,
      Ideal.mem_quotient_iff_mem hJ, ← Ideal.mem_comap, D.comap_eq]
  have hsurj0 := D.resSurj
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk (D.𝔫.map (Ideal.Quotient.mk (J θ (R := D.N₁))))).comp
        (algebraMap (Rs θ R) (Ns θ D.N₁))) := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hsurj0 (Ideal.Quotient.mk D.𝔫 z)
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    simp only [RingHom.comp_apply] at ha ⊢
    rw [Ideal.Quotient.eq] at ha ⊢
    rw [algebraMap_RN, ← map_sub]
    exact Ideal.mem_map_of_mem _ ha
  nodeEquiv hxy D.hmd hc D.hd hn (sIdeal 𝔪) _ hcomap hsurj D.Φ

/-- **The local formal Kummer form at a node with separably closed residue field.** -/
theorem exists_nodeEquiv [IsSepClosed k] {ϖ : O} {n M' : ℕ} {x y : R}
    (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
    (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
    (h : IsKummerNormAt ϖ n M' x y B 𝔪) :
    ∃ (r : ℕ) (d : Fin r → ℕ) (hd : ∀ i, 0 < d i), (∀ i, d i ∣ M') ∧
      Nonempty (letI : ∀ i, Algebra (A (0 : k) (d i)) (Tn θ 𝔪) :=
          fun i ↦ (chartAlg (k := k)
            (xy_bar (θ := θ) hxy (by rw [map_pow, hϖ, zero_pow hn0.ne'])) (hd i) _)
        Tn θ 𝔪 ⊗[Rs θ R] Cs θ R B ≃ₐ[Tn θ 𝔪]
          ∀ i, Tn θ 𝔪 ⊗[A (0 : k) (d i)] KummerEtale.B (0 : k)) :=
  let D := KummerNormAtData.ofIsKummerNormAtK hJ hres h
  ⟨D.r, D.d, D.hd, D.hdM, ⟨nodeEquivOf hxy hϖ hn0 𝔪 hJ hres D⟩⟩

omit hθ in
lemma isMaximal_sIdeal (𝔪 : Ideal R) [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪) :
    (sIdeal (θ := θ) 𝔪).IsMaximal := by
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    ‹_›).resolve_left fun h ↦ ?_
  have h1 : Ideal.Quotient.mk (J θ (R := R)) 1 ∈ sIdeal (θ := θ) 𝔪 := by
    rw [sIdeal, h]; exact Submodule.mem_top
  rw [Ideal.mem_quotient_iff_mem hJ] at h1
  exact Ideal.IsMaximal.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h1)

/-- **The formal Kummer form of the special fibre of a chart along its nodes**, defined from chosen
data `D j` at the nodes (`assembleEquiv` of `nodeEquivOf`). -/
def kummerEquivOf [IsNoetherianRing R] {ϖ : O} {n M' : ℕ} {x y : R}
    (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
    {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
    (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
    (hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
    (D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j)) {f : Rs θ R}
    (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
    (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
    (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
    (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
    (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
    (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y)) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    Admissible.Hat f ⊗[Rs θ R] Cs θ R B ≃ₐ[Admissible.Hat f]
      ∀ p : (Σ j, Fin (D j).r), Admissible.KummerPiece φ
        (CompletionProd.idem hinj hf hrad p.1) ((D p.1).hd p.2) :=
  haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
  assembleEquiv hinj hf hrad (xy_bar (θ := θ) hxy (by rw [map_pow, hϖ, zero_pow hn0.ne'])) φ
    hφu hφv (fun j ↦ (D j).hd) fun j ↦ nodeEquivOf hxy hϖ hn0 (𝔪 j) (hJ j) (hres j) (D j)

/-- **The formal Kummer form of the special fibre of a chart along its nodes**, from étale-local
Kummer data with trivial residue field extensions (`IsKummerNormAtRes`; no assumption on `k`). -/
theorem exists_kummer_of_res [IsNoetherianRing R] {ϖ : O} {n M' : ℕ} {x y : R}
    (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
    {ι : Type} [Finite ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
    (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
    (hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
    (hK : ∀ j, IsKummerNormAtRes ϖ n M' x y B (𝔪 j)) {f : Rs θ R}
    (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
    (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
    (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
    (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
    (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
    (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y)) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    ∃ (r : ι → ℕ) (d : ∀ j, Fin (r j) → ℕ) (hd : ∀ j i, 0 < d j i), (∀ j i, d j i ∣ M') ∧
      Nonempty (Admissible.Hat f ⊗[Rs θ R] Cs θ R B ≃ₐ[Admissible.Hat f]
        ∀ p : (Σ j, Fin (r j)), Admissible.KummerPiece φ
          (CompletionProd.idem hinj hf hrad p.1) (hd p.1 p.2)) := by
  haveI := Fintype.ofFinite ι
  let D := fun j ↦ KummerNormAtData.ofIsKummerNormAtRes (hK j)
  exact ⟨fun j ↦ (D j).r, fun j ↦ (D j).d, fun j ↦ (D j).hd, fun j ↦ (D j).hdM,
    ⟨kummerEquivOf hxy hϖ hn0 𝔪 hJ hres D hinj hf hrad φ hφu hφv⟩⟩

/-- **`IsKummerNormAt` ⇒ `IsKummerNormAtRes` at a `k`-rational point `𝔪 ⊇ J`** (`k` separably
closed). -/
lemma isKummerNormAtRes_of_isSepClosed [IsSepClosed k] {ϖ : O} {n M' : ℕ} {x y : R}
    {𝔪 : Ideal R} [𝔪.IsMaximal] (hJ : J θ (R := R) ≤ 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap O R)))
    (h : IsKummerNormAt ϖ n M' x y B 𝔪) : IsKummerNormAtRes ϖ n M' x y B 𝔪 :=
  h.isKummerNormAtRes ((Ideal.Quotient.factor hJ).comp (algebraMap k (Rs θ R)))
    (factor_comp_surjective hJ hres)

/-- **The formal Kummer form of the special fibre of a chart along its nodes** (separably closed
residue field). -/
theorem exists_kummer [IsSepClosed k] [IsNoetherianRing R] {ϖ : O} {n M' : ℕ} {x y : R}
    (hxy : x * y = algebraMap O R (ϖ ^ n)) (hϖ : θ ϖ = 0) (hn0 : 0 < n)
    {ι : Type} [Finite ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
    (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j)
    (hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R)))
    (hK : ∀ j, IsKummerNormAt ϖ n M' x y B (𝔪 j)) {f : Rs θ R}
    (hinj : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
    (hf : ∀ j, f ∈ sIdeal (θ := θ) (𝔪 j))
    (hrad : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {f}).radical)
    (φ : Node k (0 : k) →ₐ[k] Admissible.Hat f)
    (hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x))
    (hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y)) :
    haveI := fun j ↦ isMaximal_sIdeal (θ := θ) (𝔪 j) (hJ j)
    ∃ (r : ι → ℕ) (d : ∀ j, Fin (r j) → ℕ) (hd : ∀ j i, 0 < d j i), (∀ j i, d j i ∣ M') ∧
      Nonempty (Admissible.Hat f ⊗[Rs θ R] Cs θ R B ≃ₐ[Admissible.Hat f]
        ∀ p : (Σ j, Fin (r j)), Admissible.KummerPiece φ
          (CompletionProd.idem hinj hf hrad p.1) (hd p.1 p.2)) :=
  exists_kummer_of_res hxy hϖ hn0 𝔪 hJ hres
    (fun j ↦ isKummerNormAtRes_of_isSepClosed (hJ j) (hres j) (hK j)) hinj hf hrad φ hφu hφv

end

end FormalKummer

end SemistableReduction
