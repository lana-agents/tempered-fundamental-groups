/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DenseCompletion

/-!
# Extensions of a rank-one valuation to a finite separable extension

Blueprint §9.4, B2–B4. Let `F` be a non-archimedean normed field and `K` a complete
nontrivially normed field containing `F` densely (`[NormedAlgebra F K]`,
`DenseRange (algebraMap F K)`, e.g. the completion `\hat F`). Let `F' / F` be finite separable,
`F' = F(α)` with `P = minpoly F α` (`pb`), and `P = ∏ⱼ Pⱼ` the factorization of `P` over `K`
into distinct monic irreducibles (`factors`).

* `Local K g = K[X]/(g)` with the spectral norm is a complete non-archimedean normed field,
  and `toLocal g : F' →ₐ[F] Local K g` (`α ↦ root g`) has dense image (`denseRange_toLocal`);
* `extValuation g`: the valuation `x ↦ ‖toLocal g x‖` of `F'`; it extends the norm valuation of
  `F` (`extValuation_comap`);
* **B3** `extensionEquiv`: `g ↦ extValuation g` is a bijection from the factors onto the real
  valuations of `F'` extending the norm valuation of `F` (`Extension F F'`). Surjectivity
  (`exists_eq_extValuation`) completes `(F', w)`, extends `K → \hat F'_w` by continuity and uses
  the uniqueness of the spectral norm; injectivity (`extValuation_injective`) approximates a
  Chinese remainder idempotent by elements of `F'`;
* **B2** `ramificationIdx_extValuation`, `inertiaDeg_extValuation`: `e` and `f` of
  `extValuation g` are those of the complete extension `Local K g / K`;
* **B4** `finsum_ramificationIdx_mul_inertiaDeg`: if every finite extension of `K` is defectless,
  then `Σ_{w | v} e(w | v) f(w | v) = [F' : F]`.
-/

open Polynomial IsLocalRing Valuation NNReal UniqueFactorizationMonoid Topology

namespace SemistableReduction

open FundamentalInequality DenseCompletion

universe u

namespace LocalGlobal

section Extension

/-- A continuous isometric extension: if `i : F → K` is isometric with dense image and
`j : F → E` is isometric into a complete normed field, then `j` extends to an isometric
`ψ : K → E`. -/
lemma exists_isometric_extension {F K E : Type*} [NormedField F] [NormedField K] [NormedField E]
    [CompleteSpace E] (i : F →+* K) (hi : ∀ x, ‖i x‖ = ‖x‖) (hd : DenseRange i) (j : F →+* E)
    (hj : ∀ x, ‖j x‖ = ‖x‖) :
    ∃ ψ : K →+* E, (∀ x, ψ (i x) = j x) ∧ ∀ y, ‖ψ y‖ = ‖y‖ := by
  have ue := (AddMonoidHomClass.isometry_of_norm i hi).isUniformInducing
  have uj := (AddMonoidHomClass.isometry_of_norm j hj).uniformContinuous
  let ψ := IsDenseInducing.extendRingHom ue hd uj
  have hψ : ∀ x, ψ (i x) = j x := fun x ↦
    IsDenseInducing.extend_eq (ue.isDenseInducing hd) uj.continuous x
  have hc : Continuous ψ := (uniformContinuous_uniformly_extend ue hd uj).continuous
  refine ⟨ψ, hψ, fun y ↦ ?_⟩
  induction y using hd.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp hc) continuous_norm
  | ih x => rw [hψ, hj, hi]

end Extension

section Local

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The field `K[X]/(g)` for an irreducible `g`, with the spectral norm. -/
def Local (g : K[X]) : Type _ := AdjoinRoot g

variable {K} (g : K[X]) [hg : Fact (Irreducible g)]

noncomputable instance : Field (Local K g) := inferInstanceAs (Field (AdjoinRoot g))

noncomputable instance {R : Type*} [CommRing R] [Algebra R K] : Algebra R (Local K g) :=
  inferInstanceAs (Algebra R (AdjoinRoot g))

instance {R : Type*} [CommRing R] [Algebra R K] : IsScalarTower R K (Local K g) :=
  inferInstanceAs (IsScalarTower R K (AdjoinRoot g))

instance : FiniteDimensional K (Local K g) :=
  (AdjoinRoot.powerBasis (f := g) hg.out.ne_zero).finite

omit [IsUltrametricDist K] [CompleteSpace K] in
lemma finrank_local : Module.finrank K (Local K g) = g.natDegree := by
  exact (AdjoinRoot.powerBasis (f := g) hg.out.ne_zero).finrank.trans
    (AdjoinRoot.powerBasis_dim _)

noncomputable instance : NontriviallyNormedField (Local K g) :=
  spectralNorm.nontriviallyNormedField K (Local K g)

noncomputable instance : NormedAlgebra K (Local K g) := spectralNorm.normedAlgebra K (Local K g)

instance : CompleteSpace (Local K g) := spectralNorm.completeSpace K (Local K g)

instance : IsUltrametricDist (Local K g) := IsUltrametricDist.of_normedAlgebra K

lemma norm_local (x : Local K g) : ‖x‖ = spectralNorm K (Local K g) x := rfl

/-- The class of `X` in `Local K g`. -/
noncomputable def root : Local K g := AdjoinRoot.root g

omit [IsUltrametricDist K] [CompleteSpace K] in
lemma aeval_root : aeval (root g) g = 0 := by
  change aeval (AdjoinRoot.root g : AdjoinRoot g) g = 0
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

end Local

section Global

variable (F K F' : Type*) [NormedField F] [IsUltrametricDist F]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K]
  [Field F'] [Algebra F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- A power basis `1, α, …, α^(n-1)` of `F' / F`. -/
noncomputable def pb : PowerBasis F F' := Field.powerBasisOfFiniteOfSeparable F F'

/-- The minimal polynomial `P` of the primitive element `α`, as a polynomial over `K`. -/
noncomputable def minpolyK : K[X] := (minpoly F (pb F F').gen).map (algebraMap F K)

open Classical in
/-- The monic irreducible factors of `P` over `K`. -/
noncomputable def factors : Finset K[X] := (normalizedFactors (minpolyK F K F')).toFinset

/-- The real valuations of `F'` extending the norm valuation of `F`. -/
def Extension : Type _ :=
  {w : Valuation F' ℝ≥0 // w.comap (algebraMap F F') = NormedField.valuation (K := F)}

instance (w : Extension F F') : (NormedField.valuation (K := F)).HasExtension w.1 :=
  hasExtension_of_comap_eq w.2

variable {F K F'}

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma monic_minpolyK : (minpolyK F K F').Monic :=
  (minpoly.monic (Algebra.IsIntegral.isIntegral _)).map _

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma natDegree_minpolyK : (minpolyK F K F').natDegree = Module.finrank F F' := by
  rw [minpolyK, natDegree_map, PowerBasis.natDegree_minpoly, PowerBasis.finrank]

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma minpolyK_ne_zero : minpolyK F K F' ≠ 0 := (monic_minpolyK).ne_zero

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma squarefree_minpolyK : Squarefree (minpolyK F K F') :=
  (Polynomial.Separable.map (f := algebraMap F K)
    (Algebra.IsSeparable.isSeparable F (pb F F').gen)).squarefree

open Classical in
omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma mem_factors {g : K[X]} : g ∈ factors F K F' ↔ g ∈ normalizedFactors (minpolyK F K F') :=
  Multiset.mem_toFinset

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma irreducible_of_mem_factors {g : K[X]} (hg : g ∈ factors F K F') : Irreducible g := by
  classical
  exact irreducible_of_normalized_factor g (mem_factors.1 hg)

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma monic_of_mem_factors {g : K[X]} (hg : g ∈ factors F K F') : g.Monic := by
  classical
  rw [← normalize_normalized_factor g (mem_factors.1 hg)]
  exact monic_normalize (irreducible_of_mem_factors hg).ne_zero

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma dvd_of_mem_factors {g : K[X]} (hg : g ∈ factors F K F') : g ∣ minpolyK F K F' := by
  classical
  exact dvd_of_mem_normalizedFactors (mem_factors.1 hg)

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma prod_factors : ∏ g ∈ factors F K F', g = minpolyK F K F' := by
  classical
  have hnd := (squarefree_iff_nodup_normalizedFactors
    (minpolyK_ne_zero (F := F) (K := K) (F' := F'))).1
    (squarefree_minpolyK (F := F) (K := K) (F' := F'))
  refine eq_of_monic_of_associated (monic_prod_of_monic _ _ fun g hg ↦ monic_of_mem_factors hg)
    monic_minpolyK ?_
  rw [Finset.prod_eq_multiset_prod, factors, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']
  exact prod_normalizedFactors minpolyK_ne_zero

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
/-- `Σⱼ deg Pⱼ = [F' : F]`. -/
lemma sum_natDegree_factors :
    ∑ g ∈ factors F K F', g.natDegree = Module.finrank F F' := by
  rw [← natDegree_prod_of_monic _ _ fun g hg ↦ monic_of_mem_factors hg, prod_factors,
    natDegree_minpolyK]

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma isCoprime_of_mem_factors {g h : K[X]} (hg : g ∈ factors F K F') (hh : h ∈ factors F K F')
    (hgh : g ≠ h) : IsCoprime g h := by
  rw [(irreducible_of_mem_factors hg).coprime_iff_not_dvd]
  intro hd
  exact hgh (eq_of_monic_of_associated (monic_of_mem_factors hg) (monic_of_mem_factors hh)
    ((irreducible_of_mem_factors hg).associated_of_dvd (irreducible_of_mem_factors hh) hd))

variable (F K F') in
/-- The factors, as a type. -/
abbrev Factor : Type _ := {g : K[X] // g ∈ factors F K F'}

instance (g : Factor F K F') : Fact (Irreducible g.1) := ⟨irreducible_of_mem_factors g.2⟩

variable (g : Factor F K F')

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma aeval_root_minpolyK : aeval (root g.1) (minpolyK F K F') = 0 := by
  obtain ⟨q, hq⟩ := dvd_of_mem_factors g.2
  rw [hq, map_mul, aeval_root, zero_mul]

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma aeval_root_minpoly : aeval (root g.1) (minpoly F (pb F F').gen) = 0 := by
  rw [← aeval_map_algebraMap K, ← minpolyK, aeval_root_minpolyK]

/-- The embedding `F' → K[X]/(g)`, `α ↦ root g`. -/
noncomputable def toLocal : F' →ₐ[F] Local K g.1 :=
  (pb F F').lift (root g.1) (aeval_root_minpoly g)

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma toLocal_gen : toLocal g (pb F F').gen = root g.1 := PowerBasis.lift_gen _ _ _

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma toLocal_algebraMap (x : F) :
    toLocal g (algebraMap F F' x) = algebraMap K (Local K g.1) (algebraMap F K x) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F K]

/-- The valuation `x ↦ ‖toLocal g x‖` of `F'`. -/
noncomputable def extValuation : Valuation F' ℝ≥0 :=
  (NormedField.valuation (K := Local K g.1)).comap (toLocal g : F' →+* Local K g.1)

omit [IsUltrametricDist F] in
lemma extValuation_apply (x : F') : extValuation g x = ‖toLocal g x‖₊ := rfl

lemma extValuation_comap :
    (extValuation g).comap (algebraMap F F') = NormedField.valuation (K := F) := by
  ext x
  rw [comap_apply, extValuation_apply, toLocal_algebraMap, NormedField.valuation_apply]
  have h1 : ‖algebraMap K (Local K g.1) (algebraMap F K x)‖ = ‖algebraMap F K x‖ :=
    norm_algebraMap' _ _
  have h2 : ‖algebraMap F K x‖ = ‖x‖ := norm_algebraMap' _ _
  simp only [coe_nnnorm]
  rw [h1, h2]

instance : (NormedField.valuation (K := F)).HasExtension (extValuation g) :=
  hasExtension_of_comap_eq (extValuation_comap g)

/-- `extValuation g` as an extension of the norm valuation of `F`. -/
noncomputable def extension : Extension F F' := ⟨extValuation g, extValuation_comap g⟩

/-! ### Density -/

/-- `c ↦ Σ_{n < d} cₙ yⁿ` for `d = deg P`. -/
noncomputable def sumPow {E : Type*} [Ring E] [Algebra K E] (y : E)
    (c : Fin (minpolyK F K F').natDegree → K) : E :=
  ∑ n, c n • y ^ (n : ℕ)

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma continuous_sumPow {E : Type*} [NormedRing E] [NormedAlgebra K E] (y : E) :
    Continuous (sumPow (F := F) (K := K) (F' := F') y) :=
  continuous_finsetSum _ fun n _ ↦ (continuous_apply n).smul continuous_const

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
/-- Every element of `K[X]/(Q)`-type algebras is a `sumPow` of a root of `P`. -/
lemma sumPow_modByMonic {E : Type*} [Ring E] [Nontrivial E] [Algebra K E] {y : E}
    (hy : aeval y (minpolyK F K F') = 0) (p : K[X]) :
    sumPow (F := F) (K := K) (F' := F') y (fun n ↦ (p %ₘ minpolyK F K F').coeff n) = aeval y p := by
  have hQ1 : minpolyK F K F' ≠ 1 := by
    rintro h
    rw [h, map_one] at hy
    exact one_ne_zero hy
  have hlt := natDegree_modByMonic_lt p monic_minpolyK hQ1
  have h := congrArg (aeval y) (modByMonic_add_div p (minpolyK F K F'))
  rw [map_add, map_mul, hy, zero_mul, add_zero, aeval_eq_sum_range' hlt] at h
  rw [← h, sumPow, Finset.sum_range]

omit [IsUltrametricDist F] in
lemma toLocal_sum (a : Fin (minpolyK F K F').natDegree → F) :
    toLocal g (∑ n, a n • (pb F F').gen ^ (n : ℕ)) =
      sumPow (F := F) (K := K) (F' := F') (root g.1) (fun n ↦ algebraMap F K (a n)) := by
  simp only [map_sum, map_smul, map_pow, toLocal_gen, sumPow, algebraMap_smul]

variable [hd : Fact (DenseRange (algebraMap F K))]

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
lemma denseRange_piMap :
    DenseRange (Pi.map fun (_ : Fin (minpolyK F K F').natDegree) ↦ algebraMap F K) :=
  DenseRange.piMap fun _ ↦ hd.out

omit [IsUltrametricDist F] in
/-- **`F'` is dense in `K[X]/(g)`.** -/
theorem denseRange_toLocal : DenseRange (toLocal g) := by
  have hs : Function.Surjective (sumPow (F := F) (K := K) (F' := F') (root g.1)) := by
    intro y
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    exact ⟨_, (sumPow_modByMonic (aeval_root_minpolyK g) p).trans (AdjoinRoot.aeval_eq p)⟩
  have := hs.denseRange.comp denseRange_piMap (continuous_sumPow _)
  refine this.mono ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨_, toLocal_sum g a⟩

/-! ### Injectivity -/

omit [IsUltrametricDist F] in
/-- **B3, injectivity.** Distinct factors give distinct extensions. -/
theorem extValuation_injective {g h : Factor F K F'} (hgh : extValuation g = extValuation h) :
    g = h := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := isCoprime_of_mem_factors g.2 h.2 (fun e ↦ hne (Subtype.ext e))
  -- `t = b h` is `1` at `root g` and `0` at `root h`
  set t := b * h.1
  have htg : aeval (root g.1) t = 1 := by
    have := congrArg (aeval (root g.1)) hab
    rwa [map_add, map_mul, aeval_root, mul_zero, zero_add, map_one] at this
  have hth : aeval (root h.1) t = 0 := by rw [map_mul, aeval_root, mul_zero]
  let Φ : (Fin (minpolyK F K F').natDegree → K) → Local K g.1 × Local K h.1 :=
    fun c ↦ (sumPow (F := F) (K := K) (F' := F') (root g.1) c,
      sumPow (F := F) (K := K) (F' := F') (root h.1) c)
  have hΦ : Continuous Φ := (continuous_sumPow _).prodMk (continuous_sumPow _)
  set c₀ := fun n : Fin (minpolyK F K F').natDegree ↦ (t %ₘ minpolyK F K F').coeff n
  have hc₀ : Φ c₀ ∈ Metric.ball (1 : Local K g.1) 1 ×ˢ Metric.ball (0 : Local K h.1) 1 := by
    simp only [Φ, c₀, sumPow_modByMonic (aeval_root_minpolyK g),
      sumPow_modByMonic (aeval_root_minpolyK h), htg, hth]
    exact ⟨Metric.mem_ball_self one_pos, Metric.mem_ball_self one_pos⟩
  have hU : IsOpen (Φ ⁻¹' (Metric.ball (1 : Local K g.1) 1 ×ˢ Metric.ball (0 : Local K h.1) 1)) :=
    (Metric.isOpen_ball.prod Metric.isOpen_ball).preimage hΦ
  obtain ⟨a, hmem⟩ := denseRange_piMap.exists_mem_open hU ⟨c₀, hc₀⟩
  obtain ⟨h1, h2⟩ := Set.mem_prod.1 (Set.mem_preimage.1 hmem)
  set x := ∑ n, a n • (pb F F').gen ^ (n : ℕ)
  have hx1 : ‖toLocal g x‖ = 1 := by
    rw [toLocal_sum]
    rw [Metric.mem_ball, dist_eq_norm] at h1
    exact (norm_eq_of_norm_sub_lt (by rwa [norm_one])).trans norm_one
  have hx2 : ‖toLocal h x‖ < 1 := by
    rw [toLocal_sum]
    rwa [Metric.mem_ball, dist_zero_right] at h2
  have := congrArg (fun v ↦ (v x : ℝ)) hgh
  simp only [extValuation_apply, coe_nnnorm] at this
  rw [hx1] at this
  exact hx2.ne this.symm

/-! ### Surjectivity -/

/-- **B3, surjectivity.** Every extension of the norm valuation of `F` to `F'` is
`extValuation g` for a factor `g`. -/
theorem exists_eq_extValuation (w : Extension F F') :
    ∃ g : Factor F K F', extValuation g = w.1 := by
  -- the completion of `(F', w)`
  let E := UniformSpace.Completion (WithAbs w.1.toAbsoluteValue)
  let ι : F' →+* E := UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv w.1.toAbsoluteValue).symm.toRingHom
  have hι (x : F') : ‖ι x‖ = w.1 x := by
    change ‖((WithAbs.toAbs _ x : WithAbs w.1.toAbsoluteValue) : E)‖ = _
    rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]
    rfl
  have hw (x : F) : w.1 (algebraMap F F' x) = ‖x‖₊ := by
    rw [← comap_apply, w.2, NormedField.valuation_apply]
  obtain ⟨ψ, hψ, hψn⟩ := exists_isometric_extension (algebraMap F K) (norm_algebraMap' K)
    hd.out (ι.comp (algebraMap F F')) (fun x ↦ by rw [RingHom.comp_apply, hι, hw, coe_nnnorm])
  have hψc : ψ.comp (algebraMap F K) = ι.comp (algebraMap F F') := RingHom.ext hψ
  -- `ι α` is a root of some factor
  have hroot : eval₂ ψ (ι (pb F F').gen) (minpolyK F K F') = 0 := by
    rw [minpolyK, eval₂_map, hψc, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  rw [← prod_factors, eval₂_finsetProd, Finset.prod_eq_zero_iff] at hroot
  obtain ⟨g, hg, hg0⟩ := hroot
  let g' : Factor F K F' := ⟨g, hg⟩
  haveI : Fact (Irreducible g) := ⟨irreducible_of_mem_factors hg⟩
  refine ⟨g', ?_⟩
  -- the embedding `lam : K[X]/(g) → E`
  let lam : Local K g →+* E := AdjoinRoot.lift ψ (ι (pb F F').gen) hg0
  have hlamK (k : K) : lam (algebraMap K (Local K g) k) = ψ k := AdjoinRoot.lift_of hg0
  have hlam (x : F') : lam (toLocal g' x) = ι x := by
    obtain ⟨p, -, rfl⟩ := (pb F F').exists_eq_aeval x
    rw [← aeval_algHom_apply, toLocal_gen, aeval_def, hom_eval₂, aeval_def, hom_eval₂]
    congr 1
    · ext c
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [IsScalarTower.algebraMap_apply F K (Local K g), hlamK, hψ]
      rfl
    · exact AdjoinRoot.lift_root hg0
  -- the norm of `E` pulls back to the spectral norm
  let A : AbsoluteValue (Local K g) ℝ :=
    { toFun y := ‖lam y‖
      map_mul' _ _ := by rw [map_mul, norm_mul]
      nonneg' _ := norm_nonneg _
      eq_zero' _ := by rw [_root_.norm_eq_zero, map_eq_zero_iff lam lam.injective]
      add_le' _ _ := by rw [map_add]; exact norm_add_le _ _ }
  have hA (k : K) : A (algebraMap K (Local K g) k) = ‖k‖ := by
    change ‖lam _‖ = _
    rw [hlamK, hψn]
  ext x
  have h1 := spectralNorm_unique_field_norm_ext hA (toLocal g' x)
  change ‖lam _‖ = _ at h1
  rw [hlam, hι] at h1
  rw [extValuation_apply, coe_nnnorm, norm_local, ← h1]

/-- **B3.** The factors of `P` over `K` are in bijection with the extensions of the norm
valuation of `F` to `F'`. -/
noncomputable def extensionEquiv : Factor F K F' ≃ Extension F F' :=
  Equiv.ofBijective extension
    ⟨fun _ _ h ↦ extValuation_injective (congrArg Subtype.val h),
      fun w ↦ (exists_eq_extValuation w).imp fun _ h ↦ Subtype.ext h⟩

variable (K) in
include hd in
/-- There are only finitely many extensions. -/
theorem finite_extension : Finite (Extension F F') := Finite.of_equiv _ (extensionEquiv (K := K))

variable (K) in
include hd in
/-- The number of extensions is the number of factors of `P` over `K`. -/
theorem card_extension : Nat.card (Extension F F') = (factors F K F').card := by
  rw [← Nat.card_congr (extensionEquiv (K := K)), Nat.card_eq_fintype_card, Fintype.card_coe]

/-! ### Ramification and inertia -/

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra.IsSeparable F F'] hd in
lemma nnnorm_algebraMap_eq (x : F) : NormedField.valuation x = ‖algebraMap F K x‖₊ := by
  rw [NormedField.valuation_apply, NNReal.eq_iff, coe_nnnorm, coe_nnnorm, norm_algebraMap']

omit [IsUltrametricDist F] in
/-- **B2.** The ramification index of `extValuation g` is that of `K[X]/(g)` over `K`. -/
theorem ramificationIdx_extValuation :
    ramificationIdx F (extValuation g) =
      ramificationIdx K (NormedField.valuation (K := Local K g.1)) :=
  ramificationIdx_eq_of_denseRange (toLocal_algebraMap g) hd.out (denseRange_toLocal g)
    (extValuation_apply g)

/-- **B2.** The inertia degree of `extValuation g` is that of `K[X]/(g)` over `K`. -/
theorem inertiaDeg_extValuation :
    inertiaDeg (NormedField.valuation (K := F)) (extValuation g) =
      inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := Local K g.1)) :=
  inertiaDeg_eq_of_denseRange (toLocal_algebraMap g) hd.out (denseRange_toLocal g)
    nnnorm_algebraMap_eq (extValuation_apply g)

/-- **B4. W4 from local stability.** If `K[X]/(g)` is defectless over `K` for every factor `g`
(e.g. if every finite extension of `K` is defectless), then the fundamental equality
`Σ_{w | v} e(w | v) f(w | v) = [F' : F]` holds. -/
theorem finsum_ramificationIdx_mul_inertiaDeg
    (hloc : ∀ g : Factor F K F',
      ramificationIdx K (NormedField.valuation (K := Local K g.1)) *
        inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := Local K g.1)) =
          Module.finrank K (Local K g.1)) :
    ∑ᶠ w : Extension F F', ramificationIdx F w.1 * inertiaDeg (NormedField.valuation (K := F)) w.1 =
      Module.finrank F F' := by
  rw [← finsum_comp_equiv (extensionEquiv (K := K)) (f := fun w : Extension F F' ↦
      ramificationIdx F w.1 * inertiaDeg (NormedField.valuation (K := F)) w.1),
    finsum_eq_sum_of_fintype,
    ← sum_natDegree_factors (K := K), ← Finset.sum_coe_sort (factors F K F') natDegree]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  change ramificationIdx F (extValuation g) * inertiaDeg _ (extValuation g) = _
  rw [ramificationIdx_extValuation, inertiaDeg_extValuation, hloc, finrank_local]

end Global

/-- **B4**, with the hypothesis that every finite extension of `K` is defectless. -/
theorem finsum_ramificationIdx_mul_inertiaDeg_of_defectless {F F' : Type*} {K : Type u}
    [NormedField F]
    [IsUltrametricDist F] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra F K] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] [Fact (DenseRange (algebraMap F K))]
    (hK : ∀ (L : Type u) [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
      [FiniteDimensional K L], ramificationIdx K (NormedField.valuation (K := L)) *
        inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := L)) =
          Module.finrank K L) :
    ∑ᶠ w : Extension F F', ramificationIdx F w.1 * inertiaDeg (NormedField.valuation (K := F)) w.1 =
      Module.finrank F F' :=
  finsum_ramificationIdx_mul_inertiaDeg (K := K) fun g ↦ hK (Local K g.1)

/-- **B4** for the completion: if every finite extension of `\hat F` is defectless, then
`Σ_{w | v} e(w | v) f(w | v) = [F' : F]` for every finite separable `F' / F`. -/
theorem finsum_ramificationIdx_mul_inertiaDeg_completion {F : Type u} {F' : Type*}
    [NontriviallyNormedField F] [IsUltrametricDist F] [Field F'] [Algebra F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (hK : ∀ (L : Type u) [NormedField L] [IsUltrametricDist L]
      [NormedAlgebra (UniformSpace.Completion F) L]
      [FiniteDimensional (UniformSpace.Completion F) L],
      ramificationIdx (UniformSpace.Completion F) (NormedField.valuation (K := L)) *
        inertiaDeg (NormedField.valuation (K := UniformSpace.Completion F))
          (NormedField.valuation (K := L)) = Module.finrank (UniformSpace.Completion F) L) :
    ∑ᶠ w : Extension F F', ramificationIdx F w.1 * inertiaDeg (NormedField.valuation (K := F)) w.1 =
      Module.finrank F F' :=
  haveI : Fact (DenseRange (algebraMap F (UniformSpace.Completion F))) :=
    ⟨denseRange_algebraMap_completion F⟩
  finsum_ramificationIdx_mul_inertiaDeg_of_defectless hK

end LocalGlobal

end SemistableReduction
