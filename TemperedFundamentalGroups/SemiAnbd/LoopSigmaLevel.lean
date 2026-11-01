/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.SemidirectProduct
import Pi1.Profinite.ProSigma
import TemperedFundamentalGroups.SemiAnbd.LoopProfinite
import TemperedFundamentalGroups.SemiAnbd.OneGonTower

/-!
# `Σ`-quotients of `π^temp(G^Σ)` and the levels of the tree tower (group side of MR13 C1 (v))

For a loop of groups (`SemiAnbd/LoopTower.lean`, vertex group `Π`, branches `b₀, b₁ : E → Π`) every
open normal subgroup `M` of the tempered fundamental group `π^temp = loopGroup b₀ b₁` determines a
**level** `LoopTower.levelOf M = (vertexIncl)⁻¹(M)` (an open normal subgroup of `Π` with
`b₀⁻¹ = b₁⁻¹`, because `b₁(x) = t b₀(x) t⁻¹` in `π^temp`, `vertexIncl_branch₁`). In the
geometric situation of [SemiAnbd] Ex 3.10 / Cor 3.11 (`semianbd.txt` l.2054–2290), the
open normal subgroups of `Σ`-index of `π^temp(G^Σ)` are the Galois coverings of `Σ`-degree (via the
S5/S6 correspondence, admissible coverings of the special fibre), and `levelOf M` is the kernel of
the action of the vertex group on the covering of the vertex; the level group `H_{levelOf M}` is
the Galois group of the universal combinatorial covering.

For the stable `1`-gon (`oneGonSigma P`, vertex group `Π^Σ_{0,3}`, `b₀ = ⟨c₀⟩`, `b₁ = ⟨c₁⁻¹⟩`):

* **`oneGon_exists_sigmaOpenNormal`**: for every level `N` there is an open normal subgroup `M` of
  `Σ`-integer index of `oneGonTempered P` with `levelOf M ≤ N` — the levels of `Σ`-coverings are
  cofinal among all levels. Construction: the wreath product `Γ = Q^{ℤ/ℓ} ⋊ ℤ/ℓ` (`Q = Π/N`, `ℓ ∈ Σ`
  a prime) with `Π → Q^{ℤ/ℓ}`, `π ↦ (χᵢ(π))ᵢ`, `χᵢ` the composites of `Π → Q` with the
  endomorphisms `c₀ ↦ Sᵢ`, `c₁ ↦ Sᵢ₋₁⁻¹` of `Π_{0,3}` (`S₀ = c₀`, `S₋₁ = c₁⁻¹`, else `1`), so that
  the shift realises `b₀(x) ↦ b₁(x)` (`chi_branch₁`); this is the `Σ`-version of
  [SemiAnbd] Prop 2.5(ii) (l.1186) for the `1`-gon (there the Galois closure of a degree-`M`
  covering is not of `Σ`-order);
* **`oneGon_vertexIncl_sigma_injective`**: the vertex group `Π^Σ_{0,3}` injects into the maximal
  pro-`Σ` quotient of `π^temp(G^Σ)` ([SemiAnbd] Prop 2.5(i), l.1182, pro-`Σ` form, for the
  `1`-gon); equivalently `(vertexIncl)⁻¹(J^Σ) = 1`.

Generic: `ProSigmaCompletion.map_comp`, `map_id` (density of `Γ → Γ^Σ`).
-/

universe u

open Pi1 Pi1.Profinite Pi1.SurfaceGroup HNNExtension

namespace Pi1.Profinite.ProSigmaCompletion

variable {P : ℕ → Prop} {Γ Γ' Γ'' : Type u} [Group Γ] [Group Γ'] [Group Γ'']

/-- Functoriality of the pro-`Σ` completion: composition. -/
theorem map_comp_apply (φ : Γ →* Γ') (ψ : Γ' →* Γ'') (x : ProSigmaCompletion P Γ) :
    map (P := P) ψ (map φ x) = map (ψ.comp φ) x := by
  have h := (denseRange_eta (P := P) (Γ := Γ)).equalizer
    ((continuous_map (P := P) ψ).comp (continuous_map φ)) (continuous_map (ψ.comp φ))
    (funext fun y => by simp [map_eta])
  exact congrFun h x

/-- Functoriality of the pro-`Σ` completion: identity. -/
theorem map_id_apply (x : ProSigmaCompletion P Γ) : map (P := P) (MonoidHom.id Γ) x = x := by
  have h := (denseRange_eta (P := P) (Γ := Γ)).equalizer (continuous_map (MonoidHom.id Γ))
    continuous_id (funext fun y => by simp [map_eta])
  exact congrFun h x

end Pi1.Profinite.ProSigmaCompletion

namespace TemperedFundamentalGroups

namespace LoopTower

noncomputable section

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [IsTopologicalGroup Pv]
  [Group E] {b₀ b₁ : E →* Pv}

omit [IsTopologicalGroup Pv] in
/-- **`b₁(x) = t b₀(x) t⁻¹` in `π^temp`.** -/
theorem vertexIncl_branch₁ (x : E) :
    vertexIncl b₀ b₁ (b₁ x) = tLoop * vertexIncl b₀ b₁ (b₀ x) * tLoop⁻¹ := by
  refine Subtype.ext (funext fun N => ?_)
  change proj N (vertexIncl b₀ b₁ (b₁ x)) = proj N (tLoop * vertexIncl b₀ b₁ (b₀ x) * tLoop⁻¹)
  rw [map_mul, map_mul, map_inv, proj_vertexIncl, proj_vertexIncl]
  change of (branch₁ N x) = t * of (branch₀ N x) * t⁻¹
  rw [show (branch₀ N x) = ((⟨branch₀ N x, x, rfl⟩ : (branch₀ N).range) : levelQuot N) from rfl,
    t_mul_of, levelEquiv_apply, mul_inv_cancel_right]

/-- **The level of an open normal subgroup of `π^temp`**: its preimage in the vertex group. -/
def levelOf (M : Subgroup (loopGroup b₀ b₁)) [hM : M.Normal]
    (hMo : IsOpen (M : Set (loopGroup b₀ b₁))) : Level b₀ b₁ :=
  ⟨M.comap (vertexIncl b₀ b₁), hM.comap _, hMo.preimage continuous_vertexIncl, by
    ext x
    simp only [Subgroup.mem_comap]
    constructor
    · intro h
      rw [vertexIncl_branch₁]
      exact hM.conj_mem _ h _
    · intro h
      rw [vertexIncl_branch₁] at h
      have h' := hM.conj_mem _ h tLoop⁻¹
      simpa [mul_assoc] using h'⟩

@[simp] theorem levelOf_coe (M : Subgroup (loopGroup b₀ b₁)) [M.Normal]
    (hMo : IsOpen (M : Set (loopGroup b₀ b₁))) :
    (levelOf M hMo).1 = M.comap (vertexIncl b₀ b₁) := rfl

theorem levelOf_mono {M M' : Subgroup (loopGroup b₀ b₁)} [M.Normal] [M'.Normal]
    (hMo : IsOpen (M : Set (loopGroup b₀ b₁))) (hM'o : IsOpen (M' : Set (loopGroup b₀ b₁)))
    (h : M ≤ M') : levelOf M hMo ≤ levelOf M' hM'o :=
  Subgroup.comap_mono h

end

end LoopTower

/-! ### The `1`-gon: `Σ`-quotients of `π^temp(G^Σ)` see every level -/

namespace OneGonSigmaLevel

noncomputable section

open LoopTower

variable {P : ℕ → Prop}

section Wreath

variable (Q : Type) [Group Q] (ℓ : ℕ)

/-- The shift action of `ℤ/ℓ` on `Q^{ℤ/ℓ}`: `(k • f)(i) = f(i - k)`. -/
def shiftAut : Multiplicative (ZMod ℓ) →* MulAut (ZMod ℓ → Q) where
  toFun k :=
    { toFun := fun f i => f (i - k.toAdd)
      invFun := fun f i => f (i + k.toAdd)
      left_inv := fun f => funext fun i => by simp
      right_inv := fun f => funext fun i => by simp
      map_mul' := fun _ _ => rfl }
  map_one' := by
    ext f i
    simp
  map_mul' a b := by
    ext f i
    change f (i - (a * b).toAdd) = f (i - a.toAdd - b.toAdd)
    rw [toAdd_mul, sub_add_eq_sub_sub]

@[simp] theorem shiftAut_apply (k : Multiplicative (ZMod ℓ)) (f : ZMod ℓ → Q) (i : ZMod ℓ) :
    shiftAut Q ℓ k f i = f (i - k.toAdd) := rfl

/-- The wreath product `Q ≀ ℤ/ℓ = Q^{ℤ/ℓ} ⋊ ℤ/ℓ`. -/
abbrev Wreath : Type := (ZMod ℓ → Q) ⋊[shiftAut Q ℓ] Multiplicative (ZMod ℓ)

instance [Finite Q] [NeZero ℓ] : Finite (Wreath Q ℓ) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem isSigmaNat_pow {n : ℕ} (hn : IsSigmaNat P n) (m : ℕ) : IsSigmaNat P (n ^ m) := by
  induction m with
  | zero => simpa using isSigmaNat_one
  | succ m ih => rw [pow_succ]; exact ih.mul hn

theorem isSigmaNat_card_wreath [Finite Q] [NeZero ℓ] (hQ : IsSigmaNat P (Nat.card Q))
    (hℓ : ℓ.Prime) (hP : P ℓ) : IsSigmaNat P (Nat.card (Wreath Q ℓ)) := by
  rw [SemidirectProduct.card, Nat.card_fun, Nat.card_zmod]
  refine (isSigmaNat_pow hQ ℓ).mul ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact ⟨hℓ.ne_zero, fun p hp hpℓ => ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 hpℓ) ▸ hP⟩

end Wreath

variable (ℓ : ℕ)

/-- `Sᵢ`: `c₀` at `0`, `c₁⁻¹` at `-1`, else `1`. -/
def sGen (i : ZMod ℓ) : SurfaceGroup 0 3 :=
  if i = 0 then cusp 0 else if i = -1 then (cusp 1)⁻¹ else 1

/-- The endomorphism `c₀ ↦ Sᵢ`, `c₁ ↦ Sᵢ₋₁⁻¹`, `c₂ ↦ Sᵢ₋₁ Sᵢ⁻¹` of `Π_{0,3}`. -/
def sHom (i : ZMod ℓ) : SurfaceGroup 0 3 →* SurfaceGroup 0 3 :=
  SurfaceGroup.lift Fin.elim0 Fin.elim0
    ![sGen ℓ i, (sGen ℓ (i - 1))⁻¹, sGen ℓ (i - 1) * (sGen ℓ i)⁻¹]
    (by simp [SurfaceGen.commProd, SurfaceGen.ordProd, List.ofFn_succ])

theorem sHom_cusp0 (i : ZMod ℓ) : sHom ℓ i (cusp 0) = sGen ℓ i := by
  simp [sHom]

theorem sHom_cusp1_inv (i : ZMod ℓ) : sHom ℓ i (cusp 1)⁻¹ = sGen ℓ (i - 1) := by
  simp [sHom]

theorem sHom_zero [Fact ℓ.Prime] : sHom ℓ 0 = MonoidHom.id _ := by
  have hne : (-1 : ZMod ℓ) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have hs0 : sGen ℓ 0 = cusp 0 := by simp [sGen]
  have hs1 : sGen ℓ (0 - 1) = (cusp 1)⁻¹ := by simp [sGen, hne]
  have h2 := SurfaceGroup.relation (g := 0) (r := 3)
  simp only [SurfaceGen.commProd, SurfaceGen.ordProd, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, one_mul, mul_one] at h2
  change cusp 0 * (cusp 1 * cusp 2) = 1 at h2
  refine SurfaceGroup.hom_ext (fun i => i.elim0) (fun i => i.elim0) fun j => ?_
  rw [MonoidHom.id_apply, sHom, SurfaceGroup.lift_cusp]
  match j with
  | ⟨0, _⟩ => exact hs0
  | ⟨1, _⟩ =>
    change (sGen ℓ (0 - 1))⁻¹ = cusp 1
    rw [hs1, inv_inv]
  | ⟨2, _⟩ =>
    change sGen ℓ (0 - 1) * (sGen ℓ 0)⁻¹ = cusp 2
    rw [hs1, hs0, ← mul_inv_rev, inv_eq_iff_mul_eq_one, mul_assoc]
    exact h2

variable (P) (N : Level (oneGonB₀ P) (oneGonB₁ P))

/-- `χᵢ : Π^Σ_{0,3} → Q = Π^Σ_{0,3} ⧸ N`. -/
def chi (i : ZMod ℓ) : proSigma P 0 3 →* levelQuot N :=
  (QuotientGroup.mk' N.1).comp (ProSigmaCompletion.map (sHom ℓ i))

theorem chi_zero [Fact ℓ.Prime] (π : proSigma P 0 3) : chi P ℓ N 0 π = (π : levelQuot N) := by
  simp only [chi, MonoidHom.comp_apply, sHom_zero, ProSigmaCompletion.map_id_apply,
    QuotientGroup.mk'_apply]

/-- **`χᵢ ∘ b₁ = χᵢ₋₁ ∘ b₀`.** -/
theorem chi_branch₁ (i : ZMod ℓ) (x : ProSigmaCompletion P (Multiplicative ℤ)) :
    chi P ℓ N i (oneGonB₁ P x) = chi P ℓ N (i - 1) (oneGonB₀ P x) := by
  simp only [chi, MonoidHom.comp_apply, oneGonB₀, oneGonB₁, ProSigmaCompletion.map_comp_apply]
  congr 3
  refine MonoidHom.ext fun n => ?_
  simp only [MonoidHom.comp_apply, zpowersHom_apply, map_zpow, oneGonGen]
  rw [sHom_cusp1_inv, sHom_cusp0]

/-- `F = (χᵢ)ᵢ : Π^Σ_{0,3} → Q^{ℤ/ℓ}`. -/
def chiPi : proSigma P 0 3 →* (ZMod ℓ → levelQuot N) where
  toFun π i := chi P ℓ N i π
  map_one' := funext fun _ => map_one _
  map_mul' _ _ := funext fun _ => map_mul _ _ _

theorem chiPi_branch₁ (x : ProSigmaCompletion P (Multiplicative ℤ)) :
    chiPi P ℓ N (oneGonB₁ P x) =
      shiftAut (levelQuot N) ℓ (Multiplicative.ofAdd 1) (chiPi P ℓ N (oneGonB₀ P x)) :=
  funext fun i => chi_branch₁ P ℓ N i x

theorem isOpen_ker_chi (i : ZMod ℓ) : IsOpen ((chi P ℓ N i).ker : Set (proSigma P 0 3)) := by
  have : ((chi P ℓ N i).ker : Set (proSigma P 0 3)) =
      ProSigmaCompletion.map (sHom ℓ i) ⁻¹' (N.1 : Set (proSigma P 0 3)) := by
    ext π
    simp [chi, QuotientGroup.eq_one_iff]
  rw [this]
  exact N.2.2.1.preimage (ProSigmaCompletion.continuous_map _)

theorem ker_chiPi_eq : ((chiPi P ℓ N).ker : Set (proSigma P 0 3)) =
    ⋂ i, ((chi P ℓ N i).ker : Set (proSigma P 0 3)) := by
  ext π
  simp [chiPi, funext_iff]

variable [NeZero ℓ]

/-- The level `K = ker F` (the shift relation makes `b₀⁻¹ K = b₁⁻¹ K`). -/
def levelK : Level (oneGonB₀ P) (oneGonB₁ P) :=
  ⟨(chiPi P ℓ N).ker, MonoidHom.normal_ker _, by
    rw [ker_chiPi_eq]
    exact isOpen_iInter_of_finite fun i => isOpen_ker_chi P ℓ N i, by
    ext x
    simp only [Subgroup.mem_comap, MonoidHom.mem_ker, chiPi_branch₁]
    exact (MulEquiv.map_eq_one_iff _).symm⟩

/-- The descended map `Q_K → Q ≀ ℤ/ℓ`. -/
def fBar : levelQuot (levelK P ℓ N) →* Wreath (levelQuot N) ℓ :=
  QuotientGroup.lift _ (SemidirectProduct.inl.comp (chiPi P ℓ N)) fun π hπ => by
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hπ ⊢
    rw [hπ, map_one]

@[simp] theorem fBar_mk (π : proSigma P 0 3) :
    fBar P ℓ N (π : levelQuot (levelK P ℓ N)) = SemidirectProduct.inl (chiPi P ℓ N π) := rfl

/-- The map of the level group `H_K → Q ≀ ℤ/ℓ` (`t ↦` the shift). -/
def hBar : levelGroup (levelK P ℓ N) →* Wreath (levelQuot N) ℓ :=
  HNNExtension.lift (fBar P ℓ N) (SemidirectProduct.inr (Multiplicative.ofAdd 1)) (by
    rintro ⟨_, x, rfl⟩
    have h := levelEquiv_apply (levelK P ℓ N) x
    change _ * fBar P ℓ N (branch₀ (levelK P ℓ N) x) =
      fBar P ℓ N ((levelEquiv (levelK P ℓ N) ⟨branch₀ (levelK P ℓ N) x, x, rfl⟩ :
        (branch₁ (levelK P ℓ N)).range) : levelQuot (levelK P ℓ N)) * _
    rw [h]
    change _ * SemidirectProduct.inl (chiPi P ℓ N (oneGonB₀ P x)) =
      SemidirectProduct.inl (chiPi P ℓ N (oneGonB₁ P x)) * _
    rw [chiPi_branch₁]
    exact SemidirectProduct.ext (by simp) (by simp))

/-- **The `Σ`-quotient `ρ : π^temp(G^Σ) → Q ≀ ℤ/ℓ`.** -/
def rho : oneGonTempered P →* Wreath (levelQuot N) ℓ :=
  (hBar P ℓ N).comp (proj (levelK P ℓ N))

theorem rho_vertexIncl (π : proSigma P 0 3) :
    rho P ℓ N (vertexIncl _ _ π) = SemidirectProduct.inl (chiPi P ℓ N π) := by
  simp [rho, hBar, HNNExtension.lift_of]

theorem isOpen_ker_rho : IsOpen ((rho P ℓ N).ker : Set (oneGonTempered P)) := by
  letI : TopologicalSpace (Wreath (levelQuot N) ℓ) := ⊥
  haveI : DiscreteTopology (Wreath (levelQuot N) ℓ) := ⟨rfl⟩
  exact (isOpen_discrete {1}).preimage
    (continuous_comp_proj (levelK P ℓ N) (hBar P ℓ N))

end

end OneGonSigmaLevel

open LoopTower OneGonSigmaLevel

variable {P : ℕ → Prop}

/-- **The levels of `Σ`-quotients of `π^temp(G^Σ)` are cofinal** (the stable `1`-gon): for every
level `N` of `oneGonTower P` there is an open normal subgroup `M` of `Σ`-integer index of
`π^temp(G^Σ) = oneGonTempered P` whose level is contained in `N`. -/
theorem oneGon_exists_sigmaOpenNormal {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ)
    (N : Level (oneGonB₀ P) (oneGonB₁ P)) :
    ∃ M : Subgroup (oneGonTempered P), IsSigmaOpenNormal P (oneGonTempered P) M ∧
      M.comap (vertexIncl _ _) ≤ N.1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Finite (levelQuot N) := by
    haveI := N.1.finiteIndex_of_finite_quotient
    exact Subgroup.finite_quotient_of_finiteIndex
  have hQ : IsSigmaNat P (Nat.card (levelQuot N)) :=
    ProSigmaCompletion.isSigmaNat_index N.1 N.2.2.1
  refine ⟨(rho P ℓ N).ker, ⟨isOpen_ker_rho P ℓ N, MonoidHom.normal_ker _, ?_⟩, ?_⟩
  · rw [Subgroup.index_ker]
    exact (isSigmaNat_card_wreath _ ℓ hQ hℓ hP).of_dvd (Subgroup.card_subgroup_dvd_card _)
  · intro π hπ
    have h1 : rho P ℓ N (vertexIncl _ _ π) = 1 := hπ
    rw [rho_vertexIncl] at h1
    have h2 := congrFun (SemidirectProduct.inl_injective (h1.trans (map_one _).symm)) 0
    change chi P ℓ N 0 π = 1 at h2
    rw [chi_zero, QuotientGroup.eq_one_iff] at h2
    exact h2

/-- **The vertex group `Π^Σ_{0,3}` injects into the maximal pro-`Σ` quotient of
`π^temp(G^Σ)`** (the stable `1`-gon; [SemiAnbd] Prop 2.5(i), pro-`Σ` form). -/
theorem oneGon_vertexIncl_sigma_injective {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    Function.Injective ((MaxProSigma.mk (P := P) (G := oneGonTempered P)).comp
      (vertexIncl (oneGonB₀ P) (oneGonB₁ P))) := by
  rw [injective_iff_map_eq_one]
  intro π hπ
  by_contra hne
  obtain ⟨N, hN⟩ := oneGon_sep π hne
  obtain ⟨M, hM, hMN⟩ := oneGon_exists_sigmaOpenNormal hℓ hP N
  have hmem : vertexIncl _ _ π ∈ sigmaKernel P (oneGonTempered P) :=
    (QuotientGroup.eq_one_iff _).1 hπ
  exact hN (hMN (sigmaKernel_le hM hmem))

end TemperedFundamentalGroups
