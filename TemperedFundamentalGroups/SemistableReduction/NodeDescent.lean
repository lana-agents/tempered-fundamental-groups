/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeLocalRing

/-!
# Descent of ordinary double points along essentially étale maps (W8′, XL1, part B)

Blueprint §9.7 (XL1). Let `D → E` be a local homomorphism of noetherian local domains which is
flat, formally unramified and essentially of finite type (e.g. the Zariski local ring of a
model at a node and the local ring of an étale node chart). If `E` is an ordinary double point
`IsOrdinaryDoublePoint ϖ u v (ϖ, v) (ϖ, u)` with `u v = ϖ ^ n`, and the special fibre of `D` has
two distinct minimal primes (no loops), then `D` is an ordinary double point as well
(`IsOrdinaryDoublePoint.descent`): its branches are `𝔮ᵢ = 𝔔ᵢ ∩ D`, `𝔮ᵢ E = 𝔔ᵢ`, and
`𝔮₂ = (ϖ, u')`, `𝔮₁ = (ϖ, v')` for suitable `u', v' ∈ D`.

* `isReduced_of_flat_of_formallyUnramified`: flat, formally unramified and essentially of finite
  type over a domain implies reduced (embed into the generic fibre, which is reduced being
  unramified over a field);
* the branch ideals extend: `𝔮ᵢ E` is reduced with unique minimal prime `𝔔ᵢ` (going down);
* generators by Nakayama in `E` and faithfully flat descent of ideals.
-/

open IsLocalRing TensorProduct

namespace SemistableReduction

/-- **Flat and unramified over a domain is reduced.** -/
theorem isReduced_of_flat_of_formallyUnramified {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra.FormallyUnramified R S]
    [Algebra.EssFiniteType R S] : IsReduced S := by
  let K := FractionRing R
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S) := by
    have := Algebra.TensorProduct.includeLeft_injective (R := R) (A := S) (B := K) (S := R)
      (IsFractionRing.injective R K)
    intro a b hab
    apply this
    have e := congrArg (Algebra.TensorProduct.comm R K S) hab
    simpa using e
  haveI : IsReduced (K ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective _ hinj

section Inf

variable {O E : Type*} [CommRing O] [CommRing E] [IsLocalRing E] [Algebra O E]

/-- In an ordinary double point `u v = ϖ ^ n` the two branches meet in `(ϖ)`. -/
theorem IsOrdinaryDoublePoint.inf_eq {ϖ : O} {u v : E} {n : ℕ} (hn : 1 ≤ n)
    (huv : u * v = algebraMap O E ϖ ^ n)
    (hE : IsOrdinaryDoublePoint ϖ u v (Ideal.span {algebraMap O E ϖ, v})
      (Ideal.span {algebraMap O E ϖ, u})) :
    Ideal.span {algebraMap O E ϖ, v} ⊓ Ideal.span {algebraMap O E ϖ, u} =
      Ideal.span {algebraMap O E ϖ} := by
  haveI := hE.isPrime₂
  apply le_antisymm
  · rintro z ⟨hz₁, hz₂⟩
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hz₁
    have hb : b ∈ Ideal.span {algebraMap O E ϖ, u} := by
      have : b * v ∈ Ideal.span {algebraMap O E ϖ, u} := by
        have := sub_mem hz₂ (Ideal.mul_mem_left _ a (Ideal.subset_span (Set.mem_insert _ _)))
        simpa using this
      exact (hE.isPrime₂.mem_or_mem this).resolve_right hE.notMem₂
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hb
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine Ideal.mem_span_singleton'.mpr ⟨a + c * v + d * algebraMap O E ϖ ^ k, ?_⟩
    linear_combination (-d) * huv
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ⟨Ideal.subset_span (Set.mem_insert _ _), Ideal.subset_span (Set.mem_insert _ _)⟩

end Inf

section Descent

variable {D E : Type*} [CommRing D] [CommRing E] [IsLocalRing D] [IsLocalRing E]
  [IsNoetherianRing E] [Algebra D E] [Module.Flat D E] [IsLocalHom (algebraMap D E)]
  [Algebra.FormallyUnramified D E] [Algebra.EssFiniteType D E]

omit [IsLocalRing D] [IsLocalRing E] [IsNoetherianRing E] [IsLocalHom (algebraMap D E)] in
/-- **Branch ideals extend**: if `𝔮 = 𝔔 ∩ D` is a prime of `D` minimal over `p` (which also lies
in another such prime `𝔮'` with `𝔮' = 𝔔' ∩ D`), and every prime of `E` containing `p` contains
`𝔔` or `𝔔'`, then `𝔮 E = 𝔔`. -/
theorem map_comap_eq_of_branch {p : D} {𝔔 𝔔' : Ideal E} [h𝔔 : 𝔔.IsPrime] [𝔔'.IsPrime]
    (hbr : ∀ P : Ideal E, P.IsPrime → algebraMap D E p ∈ P → 𝔔 ≤ P ∨ 𝔔' ≤ P)
    (hp : algebraMap D E p ∈ 𝔔) (hp' : algebraMap D E p ∈ 𝔔')
    (hmin : ∀ Q : Ideal D, Q.IsPrime → p ∈ Q → Q ≤ 𝔔.comap (algebraMap D E) →
      Q = 𝔔.comap (algebraMap D E))
    (hne : 𝔔'.comap (algebraMap D E) ≠ 𝔔.comap (algebraMap D E)) :
    (𝔔.comap (algebraMap D E)).map (algebraMap D E) = 𝔔 := by
  set 𝔮 := 𝔔.comap (algebraMap D E)
  haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  haveI : IsDomain (D ⧸ 𝔮) := Ideal.Quotient.isDomain _
  -- `E ⧸ 𝔮 E` is reduced
  haveI : Module.Flat (D ⧸ 𝔮) (E ⧸ 𝔮.map (algebraMap D E)) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor E 𝔮).toLinearEquiv
  haveI : IsReduced (E ⧸ 𝔮.map (algebraMap D E)) :=
    isReduced_of_flat_of_formallyUnramified (R := D ⧸ 𝔮)
  have hrad : (𝔮.map (algebraMap D E)).IsRadical :=
    (Ideal.isRadical_iff_quotient_reduced _).mpr inferInstance
  have hle : 𝔮.map (algebraMap D E) ≤ 𝔔 := Ideal.map_comap_le
  -- the minimal primes over `𝔮 E` are all `𝔔`
  have hminP : ∀ P ∈ (𝔮.map (algebraMap D E)).minimalPrimes, P = 𝔔 := by
    intro P hP
    have hPp : P.IsPrime := hP.1.1
    have hPle : 𝔮.map (algebraMap D E) ≤ P := hP.1.2
    have hcomap : P.comap (algebraMap D E) = 𝔮 := by
      refine le_antisymm ?_ (Ideal.le_comap_of_map_le hPle)
      by_contra hlt
      have hlt' : 𝔮 < P.comap (algebraMap D E) :=
        lt_of_le_of_ne (Ideal.le_comap_of_map_le hPle) (fun h ↦ hlt (h ▸ le_rfl))
      haveI : (P.comap (algebraMap D E)).IsPrime := Ideal.comap_isPrime _ _
      haveI : P.LiesOver (P.comap (algebraMap D E)) := ⟨rfl⟩
      obtain ⟨P', hP'lt, hP'p, hP'o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt P hlt'
      have : 𝔮.map (algebraMap D E) ≤ P' := by
        rw [Ideal.map_le_iff_le_comap]; exact le_of_eq hP'o.over
      exact (not_le_of_gt hP'lt) (hP.2 ⟨hP'p, this⟩ hP'lt.le)
    have hpP : algebraMap D E p ∈ P := hPle (Ideal.mem_map_of_mem _ (by
      rw [Ideal.mem_comap]; exact hp))
    rcases hbr P hPp hpP with h | h
    · exact le_antisymm (hP.2 ⟨h𝔔, hle⟩ h) h
    · exfalso
      have h1 : 𝔔'.comap (algebraMap D E) ≤ 𝔮 := by
        rw [← hcomap]; exact Ideal.comap_mono h
      have h2 : p ∈ 𝔔'.comap (algebraMap D E) := by
        rw [Ideal.mem_comap]; exact hp'
      exact hne (hmin _ (Ideal.comap_isPrime _ _) h2 h1)
  rw [← hrad.radical, ← Ideal.sInf_minimalPrimes]
  apply le_antisymm
  · obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le hle
    exact sInf_le_of_le hP (hminP P hP).le
  · exact le_sInf fun P hP ↦ (hminP P hP).ge

omit [IsLocalRing D] [Module.Flat D E] [IsLocalHom (algebraMap D E)]
  [Algebra.FormallyUnramified D E] [Algebra.EssFiniteType D E] in
/-- **Generators by Nakayama**: if `𝔮 E = (p, a)` and residue classes of `E` come from `D`, then
`𝔮 E = (p, a')` for some `a' ∈ 𝔮`. -/
theorem exists_mem_span_pair_eq (hres : ∀ e : E, ∃ d : D, e - algebraMap D E d ∈ maximalIdeal E)
    {𝔮 : Ideal D} {pE a : E} (h : 𝔮.map (algebraMap D E) = Ideal.span {pE, a})
    (hpE : pE ∈ 𝔮.map (algebraMap D E)) :
    ∃ a' ∈ 𝔮, Ideal.span {pE, algebraMap D E a'} = Ideal.span {pE, a} := by
  classical
  have ha : a ∈ 𝔮.map (algebraMap D E) := by rw [h]; exact Ideal.subset_span (by simp)
  rw [Ideal.map, Submodule.mem_span_set'] at ha
  obtain ⟨k, c, g, hcg⟩ := ha
  choose w hw hwg using fun i ↦ (g i).2
  choose d hd using fun i ↦ hres (c i)
  refine ⟨∑ i, d i * w i, Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hw i), ?_⟩
  set a' := ∑ i, d i * w i
  have hdiff : a - algebraMap D E a' ∈ maximalIdeal E • Ideal.span {pE, a} := by
    have e : a - algebraMap D E a' = ∑ i, (c i - algebraMap D E (d i)) * (g i : E) := by
      conv_lhs => rw [← hcg]
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_eq_mul, map_mul, hwg i]; ring
    rw [e]
    refine Submodule.sum_mem _ fun i _ ↦ Ideal.mul_mem_mul (hd i) ?_
    rw [← h, ← hwg i]
    exact Ideal.mem_map_of_mem _ (hw i)
  have ha'mem : algebraMap D E a' ∈ Ideal.span {pE, a} := by
    rw [← h]; exact Ideal.mem_map_of_mem _ (Ideal.sum_mem _ fun i _ ↦
      Ideal.mul_mem_left _ _ (hw i))
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact ha'mem
  · refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]) ?_
    rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz <;> rw [hz]
    · exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))
    · have h' := Submodule.add_mem_sup
        (Ideal.subset_span (s := {pE, algebraMap D E a'})
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hdiff
      rwa [add_sub_cancel] at h'

variable {O : Type*} [CommRing O] [Algebra O D] [Algebra O E] [IsScalarTower O D E]

/-- **Descent of ordinary double points** along a flat, unramified, essentially finite local map
`D → E`, given that the special fibre of `D` has two distinct minimal primes `P₁ ≠ P₂` (no
loops). -/
theorem IsOrdinaryDoublePoint.descent {ϖ : O} {u v : E} {n : ℕ} (hn : 1 ≤ n)
    (huv : u * v = algebraMap O E ϖ ^ n)
    (hE : IsOrdinaryDoublePoint ϖ u v (Ideal.span {algebraMap O E ϖ, v})
      (Ideal.span {algebraMap O E ϖ, u}))
    (P₁ P₂ : Ideal D) [P₁.IsPrime] [P₂.IsPrime] (hP₁ : algebraMap O D ϖ ∈ P₁)
    (hP₂ : algebraMap O D ϖ ∈ P₂)
    (hmin₁ : ∀ Q : Ideal D, Q.IsPrime → algebraMap O D ϖ ∈ Q → Q ≤ P₁ → Q = P₁)
    (hmin₂ : ∀ Q : Ideal D, Q.IsPrime → algebraMap O D ϖ ∈ Q → Q ≤ P₂ → Q = P₂)
    (hne : P₁ ≠ P₂) :
    ∃ u' v' : D,
      IsOrdinaryDoublePoint ϖ u' v'
        ((Ideal.span {algebraMap O E ϖ, v}).comap (algebraMap D E))
        ((Ideal.span {algebraMap O E ϖ, u}).comap (algebraMap D E)) ∧
      Ideal.span {algebraMap O E ϖ, algebraMap D E u'} = Ideal.span {algebraMap O E ϖ, u} ∧
      Ideal.span {algebraMap O E ϖ, algebraMap D E v'} = Ideal.span {algebraMap O E ϖ, v} := by
  classical
  haveI : Module.FaithfullyFlat D E := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI := hE.isPrime₁
  haveI := hE.isPrime₂
  set p := algebraMap O D ϖ with hp_def
  have hpE : algebraMap D E p = algebraMap O E ϖ := (IsScalarTower.algebraMap_apply O D E ϖ).symm
  set 𝔔₁ := Ideal.span {algebraMap O E ϖ, v}
  set 𝔔₂ := Ideal.span {algebraMap O E ϖ, u}
  set 𝔮₁ := 𝔔₁.comap (algebraMap D E)
  set 𝔮₂ := 𝔔₂.comap (algebraMap D E)
  haveI h𝔮₁ : 𝔮₁.IsPrime := Ideal.comap_isPrime _ _
  haveI h𝔮₂ : 𝔮₂.IsPrime := Ideal.comap_isPrime _ _
  have hcm : ∀ I : Ideal D, (I.map (algebraMap D E)).comap (algebraMap D E) = I :=
    Ideal.comap_map_eq_self_of_faithfullyFlat
  have hp₁ : p ∈ 𝔮₁ := by rw [Ideal.mem_comap, hpE]; exact hE.mem₁
  have hp₂ : p ∈ 𝔮₂ := by rw [Ideal.mem_comap, hpE]; exact hE.mem₂
  -- the two branches meet in `(ϖ)`
  have hinf : 𝔮₁ ⊓ 𝔮₂ = Ideal.span {p} := by
    rw [← Ideal.comap_inf, hE.inf_eq hn huv, ← hpE, ← Set.image_singleton, ← Ideal.map_span,
      hcm]
  have hbrD : ∀ Q : Ideal D, Q.IsPrime → p ∈ Q → 𝔮₁ ≤ Q ∨ 𝔮₂ ≤ Q := by
    intro Q hQ hpQ
    have : 𝔮₁ * 𝔮₂ ≤ Q := Ideal.mul_le_inf.trans (hinf ▸ (Ideal.span_le.mpr (by simpa)))
    exact hQ.mul_le.mp this
  -- the branches are `P₁, P₂`, hence distinct and minimal
  have hbr₁ := hbrD P₁ inferInstance hP₁
  have hbr₂ := hbrD P₂ inferInstance hP₂
  have key : 𝔮₁ ≠ 𝔮₂ ∧ (∀ Q : Ideal D, Q.IsPrime → p ∈ Q → Q ≤ 𝔮₁ → Q = 𝔮₁) ∧
      (∀ Q : Ideal D, Q.IsPrime → p ∈ Q → Q ≤ 𝔮₂ → Q = 𝔮₂) := by
    rcases hbr₁ with h₁ | h₁ <;> rcases hbr₂ with h₂ | h₂
    · exact absurd ((hmin₁ _ h𝔮₁ hp₁ h₁).symm.trans (hmin₂ _ h𝔮₁ hp₁ h₂)) hne
    · have e₁ := hmin₁ _ h𝔮₁ hp₁ h₁
      have e₂ := hmin₂ _ h𝔮₂ hp₂ h₂
      refine ⟨fun h ↦ hne (e₁.symm.trans (h.trans e₂)), ?_, ?_⟩
      · rw [e₁]; exact hmin₁
      · rw [e₂]; exact hmin₂
    · have e₁ := hmin₁ _ h𝔮₂ hp₂ h₁
      have e₂ := hmin₂ _ h𝔮₁ hp₁ h₂
      refine ⟨fun h ↦ hne (e₁.symm.trans (h.symm.trans e₂)), ?_, ?_⟩
      · rw [e₂]; exact hmin₂
      · rw [e₁]; exact hmin₁
    · exact absurd ((hmin₁ _ h𝔮₂ hp₂ h₁).symm.trans (hmin₂ _ h𝔮₂ hp₂ h₂)) hne
  obtain ⟨hne𝔮, hmin𝔮₁, hmin𝔮₂⟩ := key
  -- the branch ideals extend
  have hbrE : ∀ P : Ideal E, P.IsPrime → algebraMap D E p ∈ P → 𝔔₁ ≤ P ∨ 𝔔₂ ≤ P := by
    intro P hP hpP
    rw [hpE] at hpP
    exact hE.branches P hP hpP
  have hpE₁ : algebraMap D E p ∈ 𝔔₁ := by rw [hpE]; exact hE.mem₁
  have hpE₂ : algebraMap D E p ∈ 𝔔₂ := by rw [hpE]; exact hE.mem₂
  have hmap₁ : 𝔮₁.map (algebraMap D E) = 𝔔₁ :=
    map_comap_eq_of_branch hbrE hpE₁ hpE₂ hmin𝔮₁ (Ne.symm hne𝔮)
  have hmap₂ : 𝔮₂.map (algebraMap D E) = 𝔔₂ :=
    map_comap_eq_of_branch (fun P hP hpP ↦ (hbrE P hP hpP).symm) hpE₂ hpE₁ hmin𝔮₂ hne𝔮
  -- generators
  have hresE : ∀ e : E, ∃ d : D, e - algebraMap D E d ∈ maximalIdeal E := fun e ↦ by
    obtain ⟨o, ho⟩ := hE.residue e
    exact ⟨algebraMap O D o, by rwa [← IsScalarTower.algebraMap_apply]⟩
  obtain ⟨u', hu'𝔮, hu'⟩ := exists_mem_span_pair_eq hresE (𝔮 := 𝔮₂) (a := u) hmap₂
    (by rw [hmap₂]; exact hE.mem₂)
  obtain ⟨v', hv'𝔮, hv'⟩ := exists_mem_span_pair_eq hresE (𝔮 := 𝔮₁) (a := v) hmap₁
    (by rw [hmap₁]; exact hE.mem₁)
  have hspan : ∀ a : D, Ideal.span {algebraMap O E ϖ, algebraMap D E a} =
      (Ideal.span {p, a}).map (algebraMap D E) := fun a ↦ by
    rw [Ideal.map_span, Set.image_pair, hpE]
  have he𝔮₂ : 𝔮₂ = Ideal.span {p, u'} := by
    rw [← hcm (Ideal.span {p, u'}), ← hspan, hu']
  have he𝔮₁ : 𝔮₁ = Ideal.span {p, v'} := by
    rw [← hcm (Ideal.span {p, v'}), ← hspan, hv']
  -- the maximal ideal
  have hmaxE : maximalIdeal E = 𝔔₁ ⊔ 𝔔₂ := by
    rw [hE.maximalIdeal_eq]
    apply le_antisymm
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz <;> rw [hz]
      · exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))
      · exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
      · exact Ideal.mem_sup_left (Ideal.subset_span (by simp))
    · apply sup_le <;> apply Ideal.span_mono <;> intro z hz <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢ <;> tauto
  have hmaxD : maximalIdeal D = 𝔮₁ ⊔ 𝔮₂ := by
    have h1 : (maximalIdeal D).map (algebraMap D E) = maximalIdeal E :=
      Algebra.FormallyUnramified.map_maximalIdeal
    rw [← hcm (maximalIdeal D), h1, hmaxE, ← hmap₁, ← hmap₂, ← Ideal.map_sup, hcm]
  have hu'₁ : u' ∉ 𝔮₁ := fun h ↦ hne𝔮 (hmin𝔮₁ 𝔮₂ h𝔮₂ hp₂ (by
    rw [he𝔮₂, Ideal.span_le]; intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hp₁
    · exact h)).symm
  have hv'₂ : v' ∉ 𝔮₂ := fun h ↦ hne𝔮 (hmin𝔮₂ 𝔮₁ h𝔮₁ hp₁ (by
    rw [he𝔮₁, Ideal.span_le]; intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hp₂
    · exact h))
  have hu'v' : u' * v' ∈ Ideal.span {p} := by
    rw [← hinf]
    exact ⟨Ideal.mul_mem_left _ _ hv'𝔮, Ideal.mul_mem_right _ _ hu'𝔮⟩
  have hred : ∀ (a b : D) (𝔮 : Ideal D), 𝔮 = Ideal.span {p, b} → a * b ∈ Ideal.span {p} →
      ∀ z ∈ 𝔮, a * z ∈ Ideal.span {p} := by
    intro a b 𝔮 h𝔮 hab z hz
    rw [h𝔮] at hz
    obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hz
    obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp hab
    exact Ideal.mem_span_singleton'.mpr ⟨a * α + β * γ, by linear_combination β * hγ⟩
  refine ⟨u', v', ?_, hu', hv'⟩
  exact
    { maximalIdeal_eq := by
        rw [hmaxD, he𝔮₁, he𝔮₂]
        apply le_antisymm
        · apply sup_le <;> apply Ideal.span_mono <;> intro z hz <;>
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢ <;> tauto
        · rw [Ideal.span_le]
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hz | hz | hz <;> rw [hz]
          · exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))
          · exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
          · exact Ideal.mem_sup_left (Ideal.subset_span (by simp))
      residue := fun z ↦ by
        obtain ⟨o, ho⟩ := hE.residue (algebraMap D E z)
        refine ⟨o, (mem_maximalIdeal _).mpr fun hu ↦ ?_⟩
        have := hu.map (algebraMap D E)
        rw [map_sub, ← IsScalarTower.algebraMap_apply] at this
        exact (mem_maximalIdeal _).mp ho this
      mul_mem := hu'v'
      isPrime₁ := h𝔮₁
      isPrime₂ := h𝔮₂
      mem₁ := hp₁
      mem₂ := hp₂
      notMem₁ := hu'₁
      notMem₂ := hv'₂
      reduced₁ := fun z hz ↦ ⟨u', hu'₁, hred u' v' 𝔮₁ he𝔮₁ hu'v' z hz⟩
      reduced₂ := fun z hz ↦ ⟨v', hv'₂, hred v' u' 𝔮₂ he𝔮₂ (by rwa [mul_comm]) z hz⟩
      branches := fun Q hQ hpQ ↦ hbrD Q hQ hpQ }

omit [Module.Flat D E] [IsLocalHom (algebraMap D E)] [Algebra.FormallyUnramified D E]
  [Algebra.EssFiniteType D E] in
/-- **An exact node on the Zariski local ring.** If `D → E` is as in `descent`, `D` is an ordinary
double point with coordinates `u', v'` whose branches extend to those of the node `u v = ϖ ^ n` of
`E` (`(ϖ, u') E = (ϖ, u) E`), then `D` has node coordinates `u₀ ≡ u'`, `v₀` with `u₀ v₀ = ϖ ^ n`
exactly (the same thickness), differing from `u, v` by units of `E`. -/
theorem IsOrdinaryDoublePoint.exists_node_of_flat [IsDomain O] [IsDiscreteValuationRing O]
    [IsDomain E] [IsIntegrallyClosed E] {ϖ : O} (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap O E ϖ ≠ 0) {u v : E} {n : ℕ} (hn : 1 ≤ n)
    (huv : u * v = algebraMap O E ϖ ^ n)
    (hE : IsOrdinaryDoublePoint ϖ u v (Ideal.span {algebraMap O E ϖ, v})
      (Ideal.span {algebraMap O E ϖ, u}))
    {u' v' : D} (hD : IsOrdinaryDoublePoint ϖ u' v'
      ((Ideal.span {algebraMap O E ϖ, v}).comap (algebraMap D E))
      ((Ideal.span {algebraMap O E ϖ, u}).comap (algebraMap D E)))
    (hu' : Ideal.span {algebraMap O E ϖ, algebraMap D E u'} = Ideal.span {algebraMap O E ϖ, u}) :
    ∃ u₀ v₀ : D, u₀ * v₀ = algebraMap O D ϖ ^ n ∧
      maximalIdeal D = Ideal.span {algebraMap O D ϖ, u₀, v₀} ∧
      u₀ - u' ∈ Ideal.span {algebraMap O D ϖ} ∧
      (∃ ε : Eˣ, algebraMap D E u₀ = ε * u) ∧ (∃ ε' : Eˣ, algebraMap D E v₀ = ε' * v) := by
  classical
  haveI := hE.isPrime₁
  haveI := hE.isPrime₂
  set p := algebraMap O D ϖ with hp_def
  set pE := algebraMap O E ϖ with hpE_def
  have hpE : algebraMap D E p = pE := (IsScalarTower.algebraMap_apply O D E ϖ).symm
  set 𝔔₁ := Ideal.span {pE, v}
  set 𝔔₂ := Ideal.span {pE, u}
  have hpmax : p ∈ maximalIdeal D := by
    rw [hD.maximalIdeal_eq]; exact Ideal.subset_span (Set.mem_insert _ _)
  have hu'max : u' ∈ maximalIdeal D := by
    rw [hD.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hu0 : u ≠ 0 := fun h ↦ hE.notMem₁ (h ▸ zero_mem _)
  -- branch 2 of `E`
  obtain ⟨hR₂, hmax₂⟩ := isDiscreteValuationRing_of_reduced hϖ0 hE.mem₂ hE.reduced₂
  let L₂ := Localization.AtPrime 𝔔₂
  let ι₂ := algebraMap E L₂
  have hinj₂ : Function.Injective ι₂ :=
    IsLocalization.injective L₂ 𝔔₂.primeCompl_le_nonZeroDivisors
  have hp₂ : algebraMap O L₂ ϖ = ι₂ pE := IsScalarTower.algebraMap_apply O E L₂ ϖ
  have hϖ₂ne : ι₂ pE ≠ 0 := fun h ↦ hϖ0 (hinj₂ (by rw [h, map_zero]))
  have hϖ₂ : Irreducible (ι₂ pE) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hϖ₂ne (hp₂ ▸ hmax₂)
  have hunit₂ : ∀ z ∉ 𝔔₂, IsUnit (ι₂ z) := fun z hz ↦
    IsLocalization.map_units L₂ (⟨z, hz⟩ : 𝔔₂.primeCompl)
  have hu₂ : ∃ μ : L₂ˣ, ι₂ u = μ * ι₂ pE ^ n := by
    refine ⟨(hunit₂ v hE.notMem₂).unit⁻¹, ?_⟩
    calc ι₂ u = ↑(hunit₂ v hE.notMem₂).unit⁻¹ * (ι₂ u * ι₂ v) := by
          rw [mul_comm (ι₂ u), ← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = _ := by rw [← map_mul, huv, map_pow]
  obtain ⟨μu, hμu⟩ := hu₂
  -- branch 1 of `E`
  obtain ⟨hR', huirr⟩ := hE.isDiscreteValuationRing_quotient
  let π := Ideal.Quotient.mk 𝔔₁
  have hπu : π u ≠ 0 := huirr.ne_zero
  have hord : ∀ {i j : ℕ}, (π u) ^ i ∣ (π u) ^ j → i ≤ j := fun h ↦
    (pow_dvd_pow_iff hπu huirr.not_isUnit).mp h
  have hπp : π pE = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hE.mem₁
  obtain ⟨e, he⟩ : ∃ e : (E ⧸ 𝔔₁)ˣ, π (algebraMap D E u') = e * π u := by
    have h1 : algebraMap D E u' ∈ Ideal.span {pE, u} := by
      have : algebraMap D E u' ∈ Ideal.span {pE, algebraMap D E u'} :=
        Ideal.subset_span (by simp)
      rwa [hu'] at this
    have h2 : u ∈ Ideal.span {pE, algebraMap D E u'} := by
      rw [hu']; exact Ideal.subset_span (by simp)
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h1
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp h2
    have e1 : π (algebraMap D E u') = π b * π u := by
      rw [← hab, map_add, map_mul, map_mul, hπp, mul_zero, zero_add]
    have e2 : π u = π d * π (algebraMap D E u') := by
      rw [← hcd, map_add, map_mul, map_mul, hπp, mul_zero, zero_add]
    have hbd : π b * π d = 1 := by
      have : π u * (π b * π d - 1) = 0 := by
        calc π u * (π b * π d - 1) = π d * (π b * π u) - π u := by ring
          _ = 0 := by rw [← e1, ← e2, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hπu)
    exact ⟨⟨π b, π d, hbd, by rw [mul_comm]; exact hbd⟩, e1⟩
  -- Krull in `E`: monomials in `u` and a second element with known valuations
  have hKrull : ∀ (z : E) (a : ℕ), (∃ μ : L₂ˣ, ι₂ z = μ * ι₂ pE ^ a) →
      ∀ i j : ℕ, n * i ≤ a * j → ∃ g : E, u ^ i * g = z ^ j := by
    intro z a ⟨μ, hμ⟩ i j hij
    refine exists_mul_eq_of_forall_dvr (pow_ne_zero _ hu0) fun 𝔔 h𝔔 hdvr ↦ ?_
    by_cases hp𝔔 : pE ∈ 𝔔
    · rcases hE.eq_or_eq_of_isDiscreteValuationRing hϖ0 hdvr hp𝔔 with h | h <;> subst 𝔔
      · exact Or.inl ⟨1, by
          rw [mul_one]; exact fun h ↦ hE.notMem₁ (hE.isPrime₁.mem_of_pow_mem _ h)⟩
      · right
        rw [map_pow, map_pow]
        exact dvd_of_eq_unit_mul_pow hμu hμ (by rw [mul_comm i, mul_comm j]; exact hij)
    · left
      refine ⟨v ^ i, ?_⟩
      rw [← mul_pow, huv, ← pow_mul]
      exact fun h ↦ hp𝔔 (h𝔔.mem_of_pow_mem _ h)
  -- Newton in `D`
  obtain ⟨u₁, v₁, c, g, hu, hv, huv₁⟩ := exists_newton ϖ hD.residue hD.maximalIdeal_eq hD.mul_mem n
  have hπu₁ : π (algebraMap D E u₁) = e * π u := by
    rw [← he, ← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have : algebraMap D E (u₁ - u') ∈ Ideal.span {pE} := by
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu
      rw [← ha, map_mul, ← hp_def, hpE]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    exact (Ideal.span_singleton_le_iff_mem _).mpr hE.mem₁ this
  have hu₁₁ : algebraMap D E u₁ ∉ 𝔔₁ := fun h ↦ by
    have : π (algebraMap D E u₁) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [hπu₁] at this
    exact hπu ((Units.mul_right_eq_zero e).mp this)
  have hv'₂ : algebraMap D E v' ∉ 𝔔₂ := hD.notMem₂
  have hv₁₂ : algebraMap D E v₁ ∉ 𝔔₂ := fun h ↦ by
    have hd : algebraMap D E (v₁ - v') ∈ 𝔔₂ := by
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hv
      rw [← ha, map_mul, ← hp_def, hpE]
      exact Ideal.mul_mem_left _ _ hE.mem₂
    rw [map_sub] at hd
    have := sub_mem h hd
    rw [sub_sub_cancel] at this
    exact hv'₂ this
  have hu₁0 : algebraMap D E u₁ ≠ 0 := fun h ↦ hu₁₁ (h ▸ zero_mem _)
  -- the constant term has valuation `≤ n`
  have hc : c ∉ Ideal.span {ϖ ^ (n + 1)} := by
    intro hcm
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hcm
    have hι0 : ι₂ (algebraMap D E u₁) ≠ 0 := fun h ↦ hu₁0 (hinj₂ (by rw [h, map_zero]))
    obtain ⟨a, μ, hμ⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hι0 hϖ₂
    have ha : n + 1 ≤ a := by
      have huv' : u₁ * v₁ = p ^ (n + 1) * (algebraMap O D c' + g) := by
        rw [huv₁, map_mul, map_pow]; ring
      have h1 : ι₂ pE ^ (n + 1) ∣ ι₂ (algebraMap D E u₁) * ι₂ (algebraMap D E v₁) := by
        rw [← map_mul, ← map_mul, huv', map_mul, map_mul, map_pow, map_pow, hpE]
        exact dvd_mul_right _ _
      rw [hμ, mul_assoc, mul_comm (ι₂ pE ^ a), ← mul_assoc] at h1
      have h2 : ι₂ pE ^ (n + 1) ∣ ι₂ pE ^ a :=
        (Units.dvd_mul_left (u := μ * (hunit₂ _ hv₁₂).unit)).mp (by
          simpa only [Units.val_mul, IsUnit.unit_spec] using h1)
      exact (pow_dvd_pow_iff hϖ₂ne hϖ₂.not_isUnit).mp h2
    obtain ⟨g₀, hg₀⟩ := hKrull _ a ⟨μ, hμ⟩ a n (by rw [mul_comm])
    have := congrArg π hg₀
    rw [map_mul, map_pow, map_pow, hπu₁, mul_pow] at this
    have hdvd : (π u) ^ a ∣ (π u) ^ n :=
      ⟨π g₀ * ↑(e ^ n)⁻¹, by
        have h1 : (↑e : E ⧸ 𝔔₁) ^ n * ↑(e ^ n)⁻¹ = 1 := by
          rw [← Units.val_pow_eq_pow_val, Units.mul_inv]
        linear_combination (-(π u) ^ n) * h1 - (↑(e ^ n)⁻¹ : E ⧸ 𝔔₁) * this⟩
    have := hord hdvd
    omega
  have hc0 : c ≠ 0 := fun h ↦ hc (h ▸ zero_mem _)
  obtain ⟨n', w', hw'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  have hn'n : n' ≤ n := by
    by_contra hlt
    exact hc (Ideal.mem_span_singleton'.mpr ⟨w' * ϖ ^ (n' - (n + 1)), by
      rw [hw', mul_assoc, ← pow_add]; congr 2; omega⟩)
  set U := algebraMap O D w' + p ^ (n + 1 - n') * g with hU_def
  have hU : IsUnit U := by
    by_contra hc'
    have hUm : U ∈ maximalIdeal D := (mem_maximalIdeal U).mpr hc'
    have : algebraMap O D w' ∈ maximalIdeal D := by
      have := sub_mem hUm (Ideal.mul_mem_right g _ (Ideal.pow_mem_of_mem _ hpmax _
        (by omega : 0 < n + 1 - n')))
      rwa [hU_def, add_sub_cancel_right] at this
    exact this (w'.isUnit.map (algebraMap O D))
  have huvU : u₁ * v₁ = p ^ n' * U := by
    have hpow : p ^ (n + 1) = p ^ n' * p ^ (n + 1 - n') := by
      rw [← pow_add]; congr 1; omega
    rw [huv₁, hw', map_mul, map_pow, hU_def, ← hp_def, hpow]
    ring
  set v₂ := v₁ * ↑hU.unit⁻¹ with hv₂_def
  have huv₂ : u₁ * v₂ = p ^ n' := by
    rw [hv₂_def, ← mul_assoc, huvU, mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hv₂₂ : algebraMap D E v₂ ∉ 𝔔₂ := fun h ↦ by
    have : algebraMap D E v₂ * algebraMap D E U ∈ 𝔔₂ := Ideal.mul_mem_right _ _ h
    rw [← map_mul, hv₂_def, mul_assoc, IsUnit.val_inv_mul, mul_one] at this
    exact hv₁₂ this
  -- `ι₂ u₁ = unit * ϖ ^ n'`
  have hu₁₂ : ∃ μ : L₂ˣ, ι₂ (algebraMap D E u₁) = μ * ι₂ pE ^ n' := by
    refine ⟨(hunit₂ _ hv₂₂).unit⁻¹, ?_⟩
    calc ι₂ (algebraMap D E u₁) = ↑(hunit₂ _ hv₂₂).unit⁻¹ *
          (ι₂ (algebraMap D E u₁) * ι₂ (algebraMap D E v₂)) := by
          rw [mul_comm (ι₂ _), ← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = _ := by rw [← map_mul, ← map_mul, huv₂, map_pow, map_pow, hpE]
  -- reverse Krull: `u₁ ^ j ∣ u ^ i` when `n' j ≤ n i`
  have hKrull' : ∀ i j : ℕ, n' * j ≤ n * i → ∃ g : E, algebraMap D E u₁ ^ j * g = u ^ i := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := hu₁₂
    refine exists_mul_eq_of_forall_dvr (pow_ne_zero _ hu₁0) fun 𝔔 h𝔔 hdvr ↦ ?_
    by_cases hp𝔔 : pE ∈ 𝔔
    · rcases hE.eq_or_eq_of_isDiscreteValuationRing hϖ0 hdvr hp𝔔 with h | h <;> subst 𝔔
      · exact Or.inl ⟨1, by
          rw [mul_one]; exact fun h ↦ hu₁₁ (hE.isPrime₁.mem_of_pow_mem _ h)⟩
      · right
        rw [map_pow, map_pow]
        exact dvd_of_eq_unit_mul_pow hμ hμu (by rw [mul_comm j, mul_comm i]; exact hij)
    · left
      refine ⟨algebraMap D E v₂ ^ j, ?_⟩
      rw [← mul_pow, ← map_mul, huv₂, map_pow, hpE, ← pow_mul]
      exact fun h ↦ hp𝔔 (h𝔔.mem_of_pow_mem _ h)
  -- `n' = n`
  have hnn' : n' = n := by
    obtain ⟨μ, hμ⟩ := hu₁₂
    obtain ⟨g₁, hg₁⟩ := hKrull _ n' ⟨μ, hμ⟩ n' n (le_of_eq (by ring))
    obtain ⟨g₂, hg₂⟩ := hKrull' n' n (le_of_eq (by ring))
    have h1 := congrArg π hg₁
    rw [map_mul, map_pow, map_pow, hπu₁, mul_pow] at h1
    have h2 := congrArg π hg₂
    rw [map_mul, map_pow, map_pow, hπu₁, mul_pow] at h2
    apply le_antisymm
    · -- `(π u) ^ n' ∣ (π u) ^ n`
      refine hord ⟨π g₁ * ↑(e ^ n)⁻¹, ?_⟩
      have h3 : (↑e : E ⧸ 𝔔₁) ^ n * ↑(e ^ n)⁻¹ = 1 := by
        rw [← Units.val_pow_eq_pow_val, Units.mul_inv]
      linear_combination (-(π u) ^ n) * h3 - (↑(e ^ n)⁻¹ : E ⧸ 𝔔₁) * h1
    · exact hord ⟨↑e ^ n * π g₂, by rw [← h2]; ring⟩
  subst hnn'
  -- units
  obtain ⟨g₃, hg₃⟩ := hKrull _ n' hu₁₂ 1 1 le_rfl
  obtain ⟨g₄, hg₄⟩ := hKrull' 1 1 le_rfl
  simp only [pow_one] at hg₃ hg₄
  have hg34 : g₃ * g₄ = 1 := by
    have : u * (g₃ * g₄) = u * 1 := by
      rw [mul_one, ← mul_assoc, hg₃, hg₄]
    exact mul_left_cancel₀ hu0 this
  let ε : Eˣ := ⟨g₃, g₄, hg34, by rw [mul_comm]; exact hg34⟩
  refine ⟨u₁, v₂, huv₂, ?_, hu, ⟨ε, by rw [← hg₃, mul_comm]⟩, ⟨ε⁻¹, ?_⟩⟩
  · rw [hD.maximalIdeal_eq, hv₂_def, span_triple_mul_unit,
      span_triple_eq (by rw [← neg_sub]; exact neg_mem hu) (by rw [← neg_sub]; exact neg_mem hv)]
  · -- `u₁ v₂ = u v` and `u₁ = ε u`
    have h1 : u * (g₃ * algebraMap D E v₂) = u * v := by
      rw [← mul_assoc, hg₃, ← map_mul, huv₂, map_pow, hpE, huv]
    have h2 := mul_left_cancel₀ hu0 h1
    change algebraMap D E v₂ = g₄ * v
    rw [← h2, ← mul_assoc, mul_comm g₄, hg34, one_mul]

end Descent

end SemistableReduction
