/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.LoopSigmaLevel
import TemperedFundamentalGroups.SemiAnbd.TreeUnipotent

/-!
# `π^temp(G^Σ)` of the stable `1`-gon injects into its maximal pro-`Σ` quotient

**`oneGon_sigmaKernel_eq_bot`**: for `Σ` containing a prime `ℓ`, the `Σ`-kernel `J^Σ` (the
intersection of the open normal subgroups of `Σ`-integer index) of `π^temp(G^Σ) = oneGonTempered P`
is trivial. This is the combinatorial half of the equality `I^Σ = J^Σ` in the proof of
[SemiAnbd] Cor 3.11 (`semianbd.txt` l.2271–2283: "`J^Σ ⊆ I^Σ` follows from the fact that free
discrete groups inject into their pro-`Σ` completions [cf. Remark 1.7.1]").

**Proof.** For `g ≠ 1` choose a level `N` with `g_N ≠ 1` and pass to the level `K = levelK N` of
`SemiAnbd/LoopSigmaLevel.lean`, where the wreath quotient `ψ = hBar : H_K → Q_N ≀ ℤ/ℓ` (of
`Σ`-order) is injective on the vertex group `Q_K` (`OneGonSigmaLevel.hBar_comp_of_injective`).
If `ψ(g_K) ≠ 1` we are done. Otherwise `g_K` lies in `F = ker ψ`, which acts freely on the
Bass–Serre tree of `H_K` (`HNNExtension.eq_one_of_smul_eq_self`); by
`TreeUnipotent.exists_normal_pow_mem` there is `U ⊴ F` with `F ⧸ U` an `ℓ`-group and `g_K ∉ U`,
and the normal core of `U` in `H_K` has `Σ`-integer index (`isSigmaNat_index_normalCore`).
-/

open Pi1 Pi1.Profinite HNNExtension

namespace TemperedFundamentalGroups

/-- **Normal cores of `ℓ`-subgroups of a `Σ`-index normal subgroup.** If `F ⊴ G` has `Σ`-integer
index and `U ≤ F` has finite index with `f ^ (ℓ ^ m) ∈ U` for `f ∈ F` (`ℓ ∈ Σ`), then the normal
core of `U` has `Σ`-integer index. -/
theorem isSigmaNat_index_normalCore {P : ℕ → Prop} {G : Type*} [Group G] {F U : Subgroup G}
    [hFn : F.Normal] (hUF : U ≤ F) [U.FiniteIndex] {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) {m : ℕ}
    (hpow : ∀ f ∈ F, f ^ (ℓ ^ m) ∈ U) (hF : IsSigmaNat P F.index) :
    IsSigmaNat P U.normalCore.index := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hWF : U.normalCore ≤ F := U.normalCore_le.trans hUF
  rw [← Subgroup.relIndex_mul_index hWF]
  refine IsSigmaNat.mul ?_ hF
  have hpowW : ∀ f ∈ F, f ^ (ℓ ^ m) ∈ U.normalCore := fun f hf b ↦ by
    have := hpow (b * f * b⁻¹) (hFn.conj_mem f hf b)
    rwa [conj_pow] at this
  haveI : (U.normalCore.subgroupOf F).Normal := Subgroup.normal_subgroupOf
  haveI : Finite (F ⧸ U.normalCore.subgroupOf F) := Subgroup.finite_quotient_of_finiteIndex
  have hpg : IsPGroup ℓ (F ⧸ U.normalCore.subgroupOf F) := fun x ↦ by
    induction x using QuotientGroup.induction_on with
    | H f =>
      refine ⟨m, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact hpowW f f.2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
  rw [Subgroup.relIndex, Subgroup.index, hk]
  exact OneGonSigmaLevel.isSigmaNat_pow
    ⟨hℓ.ne_zero, fun p hp hpℓ ↦ (Nat.prime_dvd_prime_iff_eq hp hℓ).1 hpℓ ▸ hP⟩ k

namespace HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}
  {Γ : Type*} [Group Γ] (ψ : HNNExtension G A B φ →* Γ)

/-- **The kernel of a quotient injective on the vertex group acts freely on the Bass–Serre
tree.** -/
theorem eq_one_of_smul_eq_self (hψ : Function.Injective (ψ.comp of)) (f : ψ.ker)
    (x : BSVertex φ) (hx : f • x = x) : f = 1 := by
  have key : ∀ k : HNNExtension G A B φ, k⁻¹ * (f : HNNExtension G A B φ)⁻¹ * k ∈
      vertexSubgroup φ → f = 1 := by
    rintro k ⟨q, hq⟩
    have h1 : ψ (of q) = 1 := by
      rw [hq, map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.1 f.2, inv_one, mul_one,
        inv_mul_cancel]
    have h2 : q = 1 := hψ (h1.trans (map_one _).symm)
    rw [h2, map_one] at hq
    have h3 : (f : HNNExtension G A B φ)⁻¹ = 1 := by
      have := congrArg (fun y ↦ k * y * k⁻¹) hq
      simpa [mul_assoc] using this.symm
    exact Subtype.ext (inv_eq_one.1 h3)
  rcases x with y | y
  · induction y using QuotientGroup.induction_on with
    | H k =>
      refine key k ?_
      have hx' : (((f : HNNExtension G A B φ) * k : HNNExtension G A B φ) :
          HNNExtension G A B φ ⧸ vertexSubgroup φ) =
          (k : HNNExtension G A B φ ⧸ vertexSubgroup φ) :=
        Sum.inl_injective hx
      have := QuotientGroup.eq.1 hx'
      simpa [mul_inv_rev, mul_assoc] using this
  · induction y using QuotientGroup.induction_on with
    | H k =>
      refine key k ?_
      have hx' : (((f : HNNExtension G A B φ) * k : HNNExtension G A B φ) :
          HNNExtension G A B φ ⧸ edgeSubgroup φ) = (k : HNNExtension G A B φ ⧸ edgeSubgroup φ) :=
        Sum.inr_injective hx
      obtain ⟨b, -, hb⟩ := QuotientGroup.eq.1 hx'
      exact ⟨b, by rw [hb]; simp [mul_inv_rev, mul_assoc]⟩

/-- The bipartition of the Bass–Serre tree (vertex cosets / edge cosets). -/
theorem isLeft_ne_of_adj {x y : BSVertex φ} (h : (bassSerreGraph φ).Adj x y) :
    x.isLeft ≠ y.isLeft := by
  rcases x with x | x <;> rcases y with y | y
  · exact absurd h (not_adj_inl_inl x y)
  · simp
  · simp
  · exact absurd h (not_adj_inr_inr x y)

theorem isLeft_smul (g : HNNExtension G A B φ) (x : BSVertex φ) : (g • x).isLeft = x.isLeft := by
  rcases x with x | x <;> rfl

end HNNExtension

namespace OneGonSigmaLevel

open LoopTower

variable {P : ℕ → Prop} (ℓ : ℕ) [Fact ℓ.Prime] (N : Level (oneGonB₀ P) (oneGonB₁ P))

theorem fBar_injective : Function.Injective (fBar P ℓ N) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H π =>
    rw [fBar_mk] at hx
    rw [QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_ker.2 (SemidirectProduct.inl_injective (hx.trans (map_one _).symm))

/-- The wreath quotient is injective on the vertex group of the level `K`. -/
theorem hBar_comp_of_injective : Function.Injective ((hBar P ℓ N).comp of) := by
  have : (hBar P ℓ N).comp of = fBar P ℓ N :=
    MonoidHom.ext fun q ↦ by rw [MonoidHom.comp_apply]; exact HNNExtension.lift_of _ _ _ q
  rw [this]
  exact fBar_injective ℓ N

theorem levelK_le : levelK P ℓ N ≤ N := fun π hπ ↦ by
  have h0 := congrFun (MonoidHom.mem_ker.1 hπ) 0
  change chi P ℓ N 0 π = 1 at h0
  rwa [chi_zero, QuotientGroup.eq_one_iff] at h0

end OneGonSigmaLevel

open LoopTower OneGonSigmaLevel

variable {P : ℕ → Prop}

/-- **`π^temp(G^Σ)` of the stable `1`-gon injects into its maximal pro-`Σ` quotient**: its
`Σ`-kernel is trivial, for every `Σ` containing a prime `ℓ` ([SemiAnbd] Cor 3.11, proof of
`I^Σ = J^Σ`, combinatorial side). -/
theorem oneGon_sigmaKernel_eq_bot {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    sigmaKernel P (oneGonTempered P) = ⊥ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  by_contra hne
  obtain ⟨N, hN⟩ : ∃ N, proj N g ≠ 1 := by
    by_contra! h
    exact hne (Subtype.ext (funext h))
  set K := levelK P ℓ N
  have hK : proj K g ≠ 1 := fun h1 ↦ hN (by rw [← levelMap_proj (levelK_le ℓ N) g, h1, map_one])
  haveI : Finite (levelQuot N) := by
    haveI := N.1.finiteIndex_of_finite_quotient
    exact Subgroup.finite_quotient_of_finiteIndex
  have hQ : IsSigmaNat P (Nat.card (levelQuot N)) :=
    ProSigmaCompletion.isSigmaNat_index N.1 N.2.2.1
  set ψ := hBar P ℓ N
  have hF : IsSigmaNat P ψ.ker.index := by
    rw [Subgroup.index_ker]
    exact (isSigmaNat_card_wreath _ ℓ hQ hℓ hP).of_dvd (Subgroup.card_subgroup_dvd_card _)
  -- a normal subgroup of `Σ`-integer index of the level group avoiding `g_K`
  obtain ⟨W, hWn, hWi, hWg⟩ : ∃ W : Subgroup (levelGroup K), W.Normal ∧
      IsSigmaNat P W.index ∧ proj K g ∉ W := by
    by_cases hgF : proj K g ∈ ψ.ker
    · obtain ⟨U, m, -, hUi, hU, hpow⟩ := TreeUnipotent.exists_normal_pow_mem (F := ψ.ker)
        (isTree_bassSerreGraph (φ := levelEquiv K))
        (fun (f : ψ.ker) x y ↦ bassSerreGraph_adj_smul (f : levelGroup K) x y)
        Sum.isLeft (fun _ _ ↦ HNNExtension.isLeft_ne_of_adj)
        (fun (f : ψ.ker) x ↦ HNNExtension.isLeft_smul (f : levelGroup K) x)
        (HNNExtension.eq_one_of_smul_eq_self ψ (hBar_comp_of_injective ℓ N)) ℓ
        (Sum.inl ((1 : levelGroup K) : levelGroup K ⧸ vertexSubgroup (levelEquiv K)))
        ⟨proj K g, hgF⟩ (fun h1 ↦ hK (congrArg Subtype.val h1))
      set U' := U.map ψ.ker.subtype
      haveI : U'.FiniteIndex := ⟨by
        rw [Subgroup.index_map_subtype]
        exact mul_ne_zero hUi.index_ne_zero hF.1⟩
      refine ⟨U'.normalCore, inferInstance,
        isSigmaNat_index_normalCore (m := m) (Subgroup.map_subtype_le U) hℓ hP
          (fun f hf ↦ ⟨⟨f, hf⟩ ^ (ℓ ^ m), hpow _, by simp⟩) hF, fun h ↦ hU ?_⟩
      obtain ⟨u, hu, hu'⟩ := Subgroup.normalCore_le U' h
      have hu2 : u = ⟨proj K g, hgF⟩ := Subtype.ext hu'
      exact hu2 ▸ hu
    · exact ⟨ψ.ker, MonoidHom.normal_ker _, hF, hgF⟩
  -- pull back to `π^temp`
  haveI : W.FiniteIndex := ⟨hWi.1⟩
  haveI : Finite (levelGroup K ⧸ W) := Subgroup.finite_quotient_of_finiteIndex
  have hM : IsSigmaOpenNormal P (oneGonTempered P) (W.comap (proj K)) := by
    refine ⟨?_, Subgroup.normal_comap _, ?_⟩
    · have : ((W.comap (proj K) : Subgroup (oneGonTempered P)) : Set (oneGonTempered P)) =
          ⋃ y ∈ (W : Set (levelGroup K)), {x | proj K x = y} := by
        ext x; simp
      rw [this]
      exact isOpen_biUnion fun y _ ↦ isOpen_proj_fiber K y
    · have hker : W.comap (proj K) = ((QuotientGroup.mk' W).comp (proj K)).ker := by
        ext x; simp [QuotientGroup.eq_one_iff]
      rw [hker, Subgroup.index_ker]
      refine hWi.of_dvd ?_
      rw [Subgroup.index]
      exact Subgroup.card_subgroup_dvd_card _
  exact hWg (sigmaKernel_le hM hg)

/-- The vertex-free form: **`π^temp(G^Σ) → (π^temp(G^Σ))^Σ` is injective.** -/
theorem oneGon_maxProSigma_mk_injective {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) :
    Function.Injective (MaxProSigma.mk (P := P) (G := oneGonTempered P)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ sigmaKernel P (oneGonTempered P) := (QuotientGroup.eq_one_iff _).1 hg
  rw [oneGon_sigmaKernel_eq_bot hℓ hP] at this
  exact this

end TemperedFundamentalGroups
