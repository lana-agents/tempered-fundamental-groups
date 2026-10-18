/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.AdmissiblePatch
import TemperedFundamentalGroups.SemistableReduction.AdmissibleEtaleLift
import TemperedFundamentalGroups.SemistableReduction.QuadNodeLift

/-!
# Level-`n` patching on a chart over the node ring (Blueprint §12.8, M2.3, Tate case)

The quadratic node chart `R = (A[S]/(S² + S − c))[1/D]` over `A = O[u,v]/(uv − π^e)` is the Tate
chart near its two nodes at the level `O` (`QuadNodeLevel.equiv`,
`TemperedFundamentalGroups.TateNormal.quadChartEquiv`); `f = u + v` cuts out the nodes. We work
with any chart `R` over the node ring `A` (`NodeChart`), with `R̂` (completion along `f`) flat over
`A` — for the quadratic node chart this is `QuadNode.flat_hat`, and `R` is Noetherian
(`QuadNode.nodeChart_hyps`). Let `θ : O → k` be the residue map of the (local, Noetherian) level
ring, `J = (ker θ) R` nilpotent, and `θ(π^e) = 0` (the special fibre is the node `uv = 0`).

* `AdmissibleLift.kMap hθ : k → R/J` (`O/ker θ ≅ k`), with `kMap_θ`: a `k`-algebra structure on
  `R/J` compatible with `θ` (hypothesis `hk`).
* **`NodeChart.φ`**: the formal node coordinates `k[u,v]/(uv) → (R/J)^∧`, `u, v ↦ ū, v̄`, of the
  special fibre.
* **`NodeChart.kummerLift`**: for an admissible covering `cov` of the special fibre (w.r.t. `φ`),
  deformation parameters `π'_j` with `π'_j^{e_j} = π^e` and lifted idempotents `ε̃_j`, the lift
  data `AdmissibleLift.KummerLift cov` with `χ_j = NodeChart.χ` (`u, v ↦ u, v`); the reduction
  condition `hχ` is checked on `O`, `u`, `v` (`Node.ringHom_ext`).
* **`NodeChart.patch_spec`**: for an admissible covering without marked points there are lift data
  and a formally étale `R`-algebra `P` over `D(f)` with `P/JP ≃ C_f` (`AwayLift.exists_lift`) such
  that the patched algebra of `AdmissibleLift.patch_spec` is finite over `R`, equal to `P` on
  `D(f)` and to the lifted Kummer model `∏_j (R̂/(1 − ε̃_j)) ⊗ O[s,t]/(st − π'_j)` on the formal
  neighbourhood of the nodes.
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift

noncomputable section

namespace AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R]

lemma ker_le_comap_J : RingHom.ker θ ≤ (J θ (R := R)).comap (algebraMap O R) :=
  fun _ hx ↦ Ideal.mem_map_of_mem _ hx

/-- The `k`-algebra structure of the special fibre `R/J` (`O/ker θ ≅ k`). -/
def kMap (hθ : Function.Surjective θ) : k →+* R ⧸ J θ (R := R) :=
  (Ideal.quotientMap (J θ) (algebraMap O R) ker_le_comap_J).comp
    (RingHom.quotientKerEquivOfSurjective hθ).symm.toRingHom

lemma kMap_θ (hθ : Function.Surjective θ) (o : O) :
    kMap hθ (θ o) = Ideal.Quotient.mk (J θ (R := R)) (algebraMap O R o) := by
  have h : (RingHom.quotientKerEquivOfSurjective hθ).symm (θ o) = Ideal.Quotient.mk _ o := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  rw [kMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h,
    Ideal.quotientMap_mk]

end AdmissibleLift

namespace NodeChart

/-! ### A chart over the node ring (generic) -/

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {π : O} {e : ℕ}
  {R : Type u} [CommRing R] [Algebra O R] [Algebra (A π e) R] [IsScalarTower O (A π e) R]

variable (R) in
/-- The element `f = u + v` of a chart over the node ring. -/
abbrev fR : R := algebraMap (A π e) R (fA π)

variable (θ) in
/-- The image in `(R/J)^∧` of an element of the chart. -/
abbrev bar (x : R) : Admissible.Hat (fbar θ (fR (π := π) (e := e) R)) :=
  algebraMap (R ⧸ J θ) _ (Ideal.Quotient.mk _ x)

omit [IsScalarTower O (A π e) R] in
lemma bar_algebraMap_O {o : O} (ho : θ o = 0) :
    bar θ (π := π) (e := e) (algebraMap O R o) = 0 := by
  have hJ : algebraMap O R o ∈ J θ (R := R) := Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ho)
  simp only [bar, Ideal.Quotient.eq_zero_iff_mem.mpr hJ, map_zero]

variable [Algebra k (R ⧸ J θ)] (hπe : θ (π ^ e) = 0)

include hπe in
lemma bar_u_mul_bar_v :
    bar θ (π := π) (e := e) (algebraMap (A π e) R (Node.u _)) *
      bar θ (π := π) (e := e) (algebraMap (A π e) R (Node.v _)) =
      algebraMap k (Admissible.Hat (fbar θ (fR (π := π) (e := e) R))) 0 := by
  rw [map_zero, bar, bar, ← map_mul, ← map_mul, ← map_mul, Node.u_mul_v,
    ← IsScalarTower.algebraMap_apply]
  exact bar_algebraMap_O hπe

variable (R) in
/-- **The formal node coordinates of the special fibre** `k[u,v]/(uv) → (R/J)^∧`. -/
def φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ (fR (π := π) (e := e) R)) :=
  Node.lift _ _ (bar_u_mul_bar_v (R := R) hπe)

lemma φ_u : φ R hπe (Node.u _) = bar θ (algebraMap (A π e) R (Node.u _)) :=
  Node.lift_u ..

lemma φ_v : φ R hπe (Node.v _) = bar θ (algebraMap (A π e) R (Node.v _)) :=
  Node.lift_v ..

omit [Algebra O R] [IsScalarTower O (A π e) R] [Algebra k (R ⧸ J θ)] in
lemma nodeCongr_u {e' : ℕ} (he : 0 < e') :
    Admissible.nodeCongr (k := k) he (Node.u _) = Node.u _ := by
  rw [Admissible.nodeCongr, AlgEquiv.ofAlgHom_apply]
  exact Node.lift_u _ _ _

omit [Algebra O R] [IsScalarTower O (A π e) R] [Algebra k (R ⧸ J θ)] in
lemma nodeCongr_v {e' : ℕ} (he : 0 < e') :
    Admissible.nodeCongr (k := k) he (Node.v _) = Node.v _ := by
  rw [Admissible.nodeCongr, AlgEquiv.ofAlgHom_apply]
  exact Node.lift_v _ _ _

omit [Algebra (A π e) R] [IsScalarTower O (A π e) R] [Algebra k (R ⧸ J θ)] in
lemma ψ_algebraMap {g : R} (x : R) :
    AdmissibleLift.ψ θ g (algebraMap R _ x) =
      algebraMap (R ⧸ J θ) _ (Ideal.Quotient.mk _ x) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (R ⧸ J θ)]
  rfl

variable {π' : O} {e' : ℕ} (he' : 0 < e') (h : π' ^ e' = π ^ e)

omit [Algebra k (R ⧸ J θ)] in
include h hπe he' in
lemma θ_π' : θ π' = 0 := by
  have : θ π' ^ e' = 0 := by rw [← map_pow, h, hπe]
  exact pow_eq_zero_iff he'.ne' |>.mp this

variable (R) in
/-- Formal node coordinates of index `e'` (`π'^{e'} = π^e`), `u, v ↦ u, v`. -/
def χ : A π' e' →ₐ[O] FormalPatchLevel.Hat (fR (π := π) (e := e) R) :=
  (IsScalarTower.toAlgHom O (A π e) (FormalPatchLevel.Hat (fR (π := π) (e := e) R))).comp
    (Node.congrEq h).toAlgHom

omit [Algebra k (R ⧸ J θ)] in
/-- The coordinates `χ` are flat if `R̂` is flat over the node ring. -/
theorem flat_χ [Module.Flat (A π e) (FormalPatchLevel.Hat (fR (π := π) (e := e) R))] :
    (χ R h).toRingHom.Flat := by
  have h1 : (algebraMap (A π e) (FormalPatchLevel.Hat (fR (π := π) (e := e) R))).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Node.congrEq h).bijective) h1

omit [Algebra k (R ⧸ J θ)] in
/-- `χ(u + v) = f`. -/
theorem χ_fA : χ R h (fA π') = algebraMap R (FormalPatchLevel.Hat (fR (π := π) (e := e) R))
    (fR (π := π) (e := e) R) := by
  rw [← IsScalarTower.algebraMap_apply]
  simp [χ, fA]

/-- **The reduction condition `hχ`** of the node coordinates. -/
theorem hχ (hk : ∀ o : O, algebraMap k (R ⧸ J θ) (θ o) =
      Ideal.Quotient.mk _ (algebraMap O R o)) (a : A π' e') :
    AdmissibleLift.ψ θ (fR (π := π) (e := e) R) (χ R h a) =
      φ R hπe (Admissible.nodeCongr he' (Node.baseMap θ (hA (θ_π' hπe he' h)) a)) := by
  have := Node.ringHom_ext
    (f := (AdmissibleLift.ψ θ (fR (π := π) (e := e) R)).toRingHom.comp (χ R h).toRingHom)
    (g := (φ R hπe).toRingHom.comp ((Admissible.nodeCongr he').toAlgHom.toRingHom.comp
      (Node.baseMap θ (hA (θ_π' hπe he' h)))))
    (RingHom.ext fun o ↦ ?_) ?_ ?_
  · exact RingHom.congr_fun this a
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      Node.baseMap_algebraMap]
    rw [IsScalarTower.algebraMap_apply k (R ⧸ J θ), hk,
      IsScalarTower.algebraMap_apply O R (FormalPatchLevel.Hat (fR (π := π) (e := e) R)),
      ψ_algebraMap]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Node.baseMap_u]
    simp only [nodeCongr_u, φ_u, χ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Node.congrEq_u,
      IsScalarTower.coe_toAlgHom']
    rw [IsScalarTower.algebraMap_apply (A π e) R, ψ_algebraMap]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Node.baseMap_v]
    simp only [nodeCongr_v, φ_v, χ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Node.congrEq_v,
      IsScalarTower.coe_toAlgHom']
    rw [IsScalarTower.algebraMap_apply (A π e) R, ψ_algebraMap]

variable {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ (fR (π := π) (e := e) R))}
  (cov : Admissible.Covering (φ R hπe) ψc)

/-- **The lift data** of an admissible covering of the special fibre of a chart over the node
ring: deformation parameters `π'_j` with `π'_j^{e_j} = π^e`, the node coordinates `χ_j`, and
lifted idempotents `ε̃_j`. -/
def kummerLift (hk : ∀ o : O, algebraMap k (R ⧸ J θ) (θ o) =
      Ideal.Quotient.mk _ (algebraMap O R o))
    (π' : cov.ι → O) (hπ' : ∀ j, π' j ^ cov.e j = π ^ e)
    (ε : cov.ι → FormalPatchLevel.Hat (fR (π := π) (e := e) R))
    (hε : ∀ j, AdmissibleLift.ψ θ (fR (π := π) (e := e) R) (ε j) = cov.idem j) :
    KummerLift cov π' where
  hπ j := θ_π' hπe (cov.e_pos j) (hπ' j)
  χ j := χ R (hπ' j)
  ε := ε
  hε := hε
  hχ j := hχ hπe (cov.e_pos j) (hπ' j) hk

/-- **Level-`n` patching of an admissible covering of the special fibre of a chart over the
node ring** (no marked points; `R̂` flat over the node ring). -/
theorem patch_spec [IsNoetherianRing R]
    [Module.Flat (A π e) (FormalPatchLevel.Hat (fR (π := π) (e := e) R))]
    [IsEmpty cov.κ] (hθ : Function.Surjective θ)
    (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ} (hJ : J θ (R := R) ^ n = ⊥)
    (hk : ∀ o : O, algebraMap k (R ⧸ J θ) (θ o) = Ideal.Quotient.mk _ (algebraMap O R o))
    (π' : cov.ι → O) (hπ' : ∀ j, π' j ^ cov.e j = π ^ e) :
    ∃ (L : KummerLift cov π') (P : Type u) (_ : CommRing P) (_ : Algebra R P)
      (_ : Algebra.FormallyEtale R P)
      (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R]
        Localization.Away (algebraMap R cov.C (fR (π := π) (e := e) R))),
      IsUnit (algebraMap R P (fR (π := π) (e := e) R)) ∧
      let α₀ := FormalPatchLevel.alphaOfEquiv (fR (π := π) (e := e) R) (J θ)
        (FormalPatchLevel.specialFibreEquiv (fR (π := π) (e := e) R) (J θ) σP (kappa hθ L))
      Module.Finite R (FormalPatchLevel.patch (fR (π := π) (e := e) R) (J θ) hJ α₀) ∧
        (letI := FormalGlueing.algebraFst (NL L)
            (FormalPatchLevel.lift (fR (π := π) (e := e) R) (J θ) hJ α₀);
          IsLocalization.Away (algebraMap R
            (FormalPatchLevel.patch (fR (π := π) (e := e) R) (J θ) hJ α₀)
              (fR (π := π) (e := e) R)) P) ∧
        IsBaseChange (FormalPatchLevel.Hat (fR (π := π) (e := e) R))
          (FormalGlueing.snd (NL L)
            (FormalPatchLevel.lift (fR (π := π) (e := e) R) (J θ) hJ α₀)).toLinearMap := by
  have hε := fun j ↦ exists_idem_lift θ hJ (cov.isIdempotentElem_idem j)
  choose ε hεi hεψ using hε
  let L := kummerLift hπe cov hk π' hπ' ε hεψ
  haveI : Module.Finite (R ⧸ J θ) cov.C := cov.finite
  obtain ⟨P, _, _, _, hfP, hP, ⟨σP⟩⟩ :=
    AwayLift.exists_lift (J θ) (fR (π := π) (e := e) R) hJ (C := cov.C) cov.etale
  refine ⟨L, P, inferInstance, inferInstance, inferInstance, σP, hfP, ?_⟩
  exact AdmissibleLift.patch_spec L hθ hO hJ (fun j ↦ flat_χ (hπ' j)) hεi
    (fun j ↦ χ_fA (hπ' j)) σP hfP hP

end NodeChart

namespace QuadNode

variable {O : Type u} [CommRing O] (π : O) (e : ℕ) (c D : A π e)

/-- The quadratic node chart satisfies the hypotheses of `NodeChart.patch_spec`. -/
theorem nodeChart_hyps [IsNoetherianRing O] : IsNoetherianRing (R π e c D) ∧
    IsScalarTower O (A π e) (R π e c D) ∧
    Module.Flat (A π e) (FormalPatchLevel.Hat (NodeChart.fR (π := π) (e := e) (R π e c D))) :=
  ⟨inferInstance, inferInstance, flat_hat π e c D⟩

end QuadNode


end

end SemistableReduction
