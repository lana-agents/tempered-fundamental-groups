/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TwoComponents
import TemperedFundamentalGroups.SemistableReduction.NodeLocalRing

/-!
# Node reflection (Blueprint §12.7, missing theorem M1)

Let `ψ : c₁ ⟶ c₂` be a morphism of projective models over discrete valuation rings `O₁`, `O₂`
(compatible with uniformizers: `ψ^*(ϖ₂) ^ a = ϖ₁ ^ m · unit`, e.g. both models over a common
`O`), `c₂` semistable. If `z` is a smooth point of the special fibre of `c₁` and `η` is a generic
point of a component of the special fibre through `z`, and `ψ z` is a node, then `ψ η = ψ z`:
**a component whose image is not the node `ψ z` meets `ψ⁻¹(ψ z)` only in node points.**

Proof (local commutative algebra, no Zariski main theorem needed). Pull the node chart
`u v = ϖ₂ ^ n` at `ψ z` back to a common étale neighbourhood `E` of `z` and of a point of
`O₁[X]` (`E = C_z ⊗ C_y`, base change). In the local ring `E_𝔰`, `ϖ₁` generates a prime ideal
(the special fibre of an étale neighbourhood of `O₁[X]` is étale over the normal domain `κ[X]`)
and is a non-zero-divisor (flatness), so `u^a v^a = ϖ₁ ^ N · unit` with `u, v` in the maximal
ideal forces `u, v ∈ ϖ₁ E_𝔰` (`mem_span_of_mul_eq_pow_mul`). The prime `P = ϖ₁ E_𝔰 ∩ E` lies over
the generic point `η` (going down for the flat map to `E`, and minimality of `η`), and over the
singular point of the node in the node chart (`u, v ∈ P`, quasi-finiteness of étale maps). Hence
`ψ η = ψ z`.

* `mem_span_of_mul_eq_pow_mul`: divisibility in a local ring with a prime regular element;
* `exists_prime_of_etale_polynomial`: the prime `ϖ E_𝔰 ∩ E` of an étale neighbourhood of
  `O[X]`, least among the primes over the special fibre inside `𝔰`, containing both factors of
  every factorization `a b = ϖ ^ N · unit` inside `𝔰`;
* `eq_of_le_of_u_v_mem`: in an étale neighbourhood of a node, a generization of a point over the
  singular point still containing `u, v` is the point itself;
* **`comap_eq_of_isNodeAt`** (ring form of M1) and **`ModelCode.map_eq_of_isNodePt`** (scheme
  form); `ModelCode.appTop_rel_of_comp_eq` (the relation of uniformizers from a common base).
-/

universe u

open Polynomial IsLocalRing TensorProduct CategoryTheory AlgebraicGeometry

namespace SemistableReduction

/-- **Divisibility at a prime regular element of a local ring**: if `p` generates a prime ideal
and is a non-zero-divisor, and `a b = p ^ N ε` with `ε` a unit and `a, b` in the maximal ideal,
then `p ∣ b`. -/
theorem mem_span_of_mul_eq_pow_mul {D : Type*} [CommRing D] [IsLocalRing D] {p : D}
    (hp : (Ideal.span {p}).IsPrime) (hreg : ∀ x : D, p * x = 0 → x = 0) :
    ∀ (N : ℕ) {a b ε : D}, IsUnit ε → a ∈ maximalIdeal D → b ∈ maximalIdeal D →
      a * b = p ^ N * ε → b ∈ Ideal.span {p} := by
  intro N
  induction N with
  | zero =>
    intro a b ε hε ha _ hab
    rw [pow_zero, one_mul] at hab
    exact absurd (isUnit_of_mul_isUnit_left (hab ▸ hε)) ((mem_maximalIdeal a).1 ha)
  | succ N ih =>
    intro a b ε hε ha hb hab
    have hmem : a * b ∈ Ideal.span {p} := by
      rw [hab, pow_succ]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self p))
    rcases hp.mem_or_mem hmem with h | h
    · obtain ⟨a₁, rfl⟩ := Ideal.mem_span_singleton'.1 h
      have h₁ : a₁ * b = p ^ N * ε := by
        rw [← sub_eq_zero]
        apply hreg
        linear_combination hab
      by_cases ha₁ : a₁ ∈ maximalIdeal D
      · exact ih hε ha₁ hb h₁
      · rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at ha₁
        rcases N with _ | N
        · rw [pow_zero, one_mul] at h₁
          exact absurd (isUnit_of_mul_isUnit_right (h₁ ▸ hε)) ((mem_maximalIdeal b).1 hb)
        · obtain ⟨w, rfl⟩ := ha₁
          have hb' : b = p * (↑w⁻¹ * p ^ N * ε) := by
            calc b = ↑w⁻¹ * (↑w * b) := by rw [← mul_assoc, Units.inv_mul, one_mul]
              _ = _ := by rw [h₁]; ring
          rw [hb']
          exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self p)
    · exact h

/-- **The special fibre prime of an étale neighbourhood of `O[X]`.** Let `f : O[X] → E` be étale,
`O` a domain in which `ϖ ≠ 0` generates a maximal ideal, and `𝔰` a prime of `E` containing `ϖ`.
The prime `P = ϖ E_𝔰 ∩ E` is contained in every prime `Q ⊆ 𝔰` containing `ϖ`, and contains both
factors of every factorization `a b = ϖ ^ N ε` with `a, b ∈ 𝔰`, `ε ∉ 𝔰`. -/
theorem exists_prime_of_etale_polynomial {O E : Type*} [CommRing O] [IsDomain O] {ϖ : O}
    (hϖ : (Ideal.span {ϖ}).IsMaximal) (hϖ0 : ϖ ≠ 0) [CommRing E] (f : O[X] →+* E)
    (hf : f.Etale) (𝔰 : Ideal E) [𝔰.IsPrime] (hϖ𝔰 : f (C ϖ) ∈ 𝔰) :
    ∃ P : Ideal E, P.IsPrime ∧ P ≤ 𝔰 ∧ f (C ϖ) ∈ P ∧
      (∀ Q : Ideal E, Q.IsPrime → Q ≤ 𝔰 → f (C ϖ) ∈ Q → P ≤ Q) ∧
      ∀ (N : ℕ) (a b ε : E), a ∈ 𝔰 → b ∈ 𝔰 → ε ∉ 𝔰 → a * b = f (C ϖ) ^ N * ε →
        a ∈ P ∧ b ∈ P := by
  letI : Algebra O[X] E := f.toAlgebra
  haveI : Algebra.Etale O[X] E := hf
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  let I : Ideal O[X] := Ideal.span {C ϖ}
  have hI : I = (Ideal.span {ϖ}).map C := by
    rw [Ideal.map_span, Set.image_singleton]
  let e : O[X] ⧸ I ≃+* (O ⧸ Ideal.span {ϖ})[X] :=
    (Ideal.quotientEquivAlgOfEq O hI).toRingEquiv.trans
      (Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.span {ϖ})).symm
  haveI : IsDomain (O[X] ⧸ I) := e.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed (O[X] ⧸ I) := IsIntegrallyClosed.of_equiv e.symm
  have hIle : I.map (algebraMap O[X] E) ≤ 𝔰 := by
    rw [Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
    exact hϖ𝔰
  obtain ⟨hPL, -⟩ := isPrime_map_localization_of_etale I 𝔰 hIle
  let L := Localization.AtPrime 𝔰
  set p : L := algebraMap O[X] L (C ϖ) with hp
  have hpE : algebraMap E L (f (C ϖ)) = p := by
    rw [hp, IsScalarTower.algebraMap_apply O[X] E L]
    rfl
  have hPLeq : I.map (algebraMap O[X] L) = Ideal.span {p} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hPLeq] at hPL
  -- `ϖ` is a non-zero-divisor of `L`
  haveI : Module.Flat O[X] L := Module.Flat.trans O[X] E L
  have hCϖ : (C ϖ : O[X]) ∈ nonZeroDivisors O[X] :=
    mem_nonZeroDivisors_of_ne_zero (C_ne_zero.2 hϖ0)
  have hreg : ∀ x : L, p * x = 0 → x = 0 := fun x hx ↦ by
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := L) hCϖ
    apply h
    simp only [Algebra.smul_def, mul_zero]
    exact hx
  refine ⟨(Ideal.span {p}).comap (algebraMap E L), Ideal.comap_isPrime _ _, ?_, ?_, ?_, ?_⟩
  · calc _ ≤ (maximalIdeal L).comap (algebraMap E L) :=
          Ideal.comap_mono (le_maximalIdeal hPL.ne_top)
      _ = 𝔰 := Localization.AtPrime.under_maximalIdeal ..
  · rw [Ideal.mem_comap, hpE]
    exact Ideal.mem_span_singleton_self p
  · intro Q hQ hQ𝔰 hϖQ
    have hdisj : Disjoint (𝔰.primeCompl : Set E) Q := by
      rw [Set.disjoint_left]
      intro x hx hxQ
      exact hx (hQ𝔰 hxQ)
    calc _ ≤ (Q.map (algebraMap E L)).comap (algebraMap E L) := by
          refine Ideal.comap_mono ?_
          rw [Ideal.span_le, Set.singleton_subset_iff, ← hpE]
          exact Ideal.mem_map_of_mem _ hϖQ
      _ = Q := IsLocalization.under_map_of_isPrime_disjoint 𝔰.primeCompl L hQ hdisj
  · intro N a b ε ha hb hε hab
    have hmax : ∀ y ∈ 𝔰, algebraMap E L y ∈ maximalIdeal L := fun y hy ↦ by
      rw [← Localization.AtPrime.under_maximalIdeal (I := 𝔰)] at hy
      exact hy
    have hunit : IsUnit (algebraMap E L ε) :=
      IsLocalization.map_units L (⟨ε, hε⟩ : 𝔰.primeCompl)
    have hab' : algebraMap E L a * algebraMap E L b = p ^ N * algebraMap E L ε := by
      rw [← map_mul, hab, map_mul, map_pow, hpE]
    have hba' : algebraMap E L b * algebraMap E L a = p ^ N * algebraMap E L ε := by
      rw [mul_comm, hab']
    exact ⟨mem_span_of_mul_eq_pow_mul hPL hreg N hunit (hmax b hb) (hmax a ha) hba',
      mem_span_of_mul_eq_pow_mul hPL hreg N hunit (hmax a ha) (hmax b hb) hab'⟩

/-- **Generizations in an étale neighbourhood of a node.** If `f : O[u, v] ⧸ (u v - ϖ ^ n) → C`
is étale and `𝔮' ⊆ 𝔮` are primes of `C` both containing `u` and `v`, then `𝔮' = 𝔮` (both lie
over the singular point, and étale maps are quasi-finite). -/
theorem eq_of_le_of_u_v_mem {O C : Type u} [CommRing O] [IsLocalRing O] {ϖ : O}
    (hϖ : maximalIdeal O ≤ Ideal.span {ϖ}) {n : ℕ} [CommRing C] {f : Node O (ϖ ^ n) →+* C}
    (hf : f.Etale) {𝔮 𝔮' : Ideal C} [𝔮.IsPrime] [𝔮'.IsPrime] (hle : 𝔮' ≤ 𝔮)
    (hu : f (Node.u (ϖ ^ n)) ∈ 𝔮') (hv : f (Node.v (ϖ ^ n)) ∈ 𝔮') : 𝔮' = 𝔮 := by
  letI : Algebra (Node O (ϖ ^ n)) C := f.toAlgebra
  haveI : Algebra.Etale (Node O (ϖ ^ n)) C := hf
  refine Algebra.QuasiFinite.eq_of_le_of_under_eq (R := Node O (ϖ ^ n)) 𝔮' 𝔮 hle ?_
  refine le_antisymm (Ideal.comap_mono hle) fun x hx ↦ ?_
  change f x ∈ 𝔮 at hx
  change f x ∈ 𝔮'
  obtain ⟨o, ho⟩ := Node.exists_sub_mem_span (ϖ ^ n) x
  have hspan : ∀ y ∈ Ideal.span {Node.u (ϖ ^ n), Node.v (ϖ ^ n)}, f y ∈ 𝔮' := by
    intro y hy
    have : Ideal.span {Node.u (ϖ ^ n), Node.v (ϖ ^ n)} ≤ 𝔮'.comap f := by
      rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · exact hu
      · exact hv
    exact this hy
  have h1 := hspan _ ho
  rw [map_sub] at h1
  suffices f (algebraMap O _ o) ∈ 𝔮' by simpa using 𝔮'.add_mem h1 this
  by_cases hunit : IsUnit o
  · exfalso
    have h2 := 𝔮.sub_mem hx (hle (hspan _ ho))
    rw [map_sub, sub_sub_cancel] at h2
    exact ‹𝔮.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 ((hunit.map _).map _))
  · obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hϖ ((mem_maximalIdeal _).2 hunit))
    rw [← hr, map_mul, map_mul]
    refine Ideal.mul_mem_left _ _ (‹𝔮'.IsPrime›.mem_of_pow_mem n ?_)
    rw [← map_pow, ← map_pow, ← Node.u_mul_v, map_mul]
    exact Ideal.mul_mem_right _ _ hu

/-- **Node reflection, ring form (M1).** Let `φ : B → A` be a ring map, `A` an `O₁`-algebra
which is étale-locally `O₁[X]` at a prime `𝔭 ∋ ϖ₁` (a smooth point of the special fibre) and
`B` an `O₂`-algebra with a node of thickness `n` at `φ⁻¹ 𝔭`, the uniformizers being related by
`φ(ϖ₂) ^ a = ϖ₁ ^ m ε` (`a ≥ 1`, `ε` a unit). If `q ⊆ 𝔭` is a minimal prime over `ϖ₁` (the
generic point of the component through `𝔭`), then `φ⁻¹ q = φ⁻¹ 𝔭`. -/
theorem comap_eq_of_isNodeAt {O₁ O₂ A B : Type u} [CommRing O₁] [IsDomain O₁] [CommRing O₂]
    [IsLocalRing O₂] [CommRing A] [CommRing B] [Algebra O₁ A] [Algebra O₂ B]
    {ϖ₁ : O₁} (hϖ₁ : (Ideal.span {ϖ₁}).IsMaximal) (hϖ₁0 : ϖ₁ ≠ 0) {ϖ₂ : O₂}
    (hϖ₂ : maximalIdeal O₂ ≤ Ideal.span {ϖ₂}) (φ : B →+* A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (hs : IsEtaleLocallyAt O₁ O₁[X] 𝔭) {n : ℕ} (hn : IsNodeAt ϖ₂ n (𝔭.comap φ))
    {a m : ℕ} {ε : A} (ha : 1 ≤ a) (hε : IsUnit ε)
    (hrel : φ (algebraMap O₂ B ϖ₂) ^ a = algebraMap O₁ A ϖ₁ ^ m * ε)
    {q : Ideal A} [q.IsPrime] (hq : q ≤ 𝔭) (hϖq : algebraMap O₁ A ϖ₁ ∈ q)
    (hmin : ∀ Q : Ideal A, Q.IsPrime → algebraMap O₁ A ϖ₁ ∈ Q → Q ≤ q → Q = q) :
    q.comap φ = 𝔭.comap φ := by
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hc, hO, hu, hv⟩ := hn
  obtain ⟨Cz, _, gz, fz, 𝔮z, hgz, hfz, h𝔮z, hcz, hOz⟩ := hs
  letI : Algebra B C := g.toAlgebra
  letI : Algebra B Cz := (gz.comp φ).toAlgebra
  have hlies : 𝔮z.comap (algebraMap B Cz) = 𝔮.comap (algebraMap B C) := by
    change 𝔮z.comap (gz.comp φ) = 𝔮.comap g
    rw [← Ideal.comap_comap, hcz, hc]
  obtain ⟨𝔰, h𝔰, h𝔰₁, h𝔰₂⟩ := exists_isPrime_tensorProduct 𝔮z 𝔮 hlies
  let E := Cz ⊗[B] C
  let iL : Cz →+* E := Algebra.TensorProduct.includeLeftRingHom
  let iR : C →+* E := (Algebra.TensorProduct.includeRight : C →ₐ[B] E).toRingHom
  have hiL : iL.Etale := RingHom.Etale.isStableUnderBaseChange.tensorProduct Cz hg
  let θ : A →+* E := iL.comp gz
  have hθ : θ.Etale := RingHom.Etale.stableUnderComposition _ _ hgz hiL
  let f₂ : O₁[X] →+* E := iL.comp fz
  have hf₂ : f₂.Etale := RingHom.Etale.stableUnderComposition _ _ hfz hiL
  have h𝔰A : 𝔰.comap θ = 𝔭 := by
    change 𝔰.comap (iL.comp gz) = 𝔭
    rw [← Ideal.comap_comap, h𝔰₁, hcz]
  have hθO : ∀ o, f₂ (Polynomial.C o) = θ (algebraMap O₁ A o) := fun o ↦ by
    change iL (fz (algebraMap O₁ O₁[X] o)) = iL (gz (algebraMap O₁ A o))
    rw [← RingHom.comp_apply fz, hOz, RingHom.comp_apply]
  have hθφ : ∀ b, θ (φ b) = iR (g b) := fun b ↦ by
    change (gz (φ b)) ⊗ₜ[B] (1 : C) = (1 : Cz) ⊗ₜ[B] g b
    change (algebraMap B Cz b) ⊗ₜ[B] (1 : C) = (1 : Cz) ⊗ₜ[B] algebraMap B C b
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hϖ𝔰 : f₂ (Polynomial.C ϖ₁) ∈ 𝔰 := by
    rw [hθO, ← Ideal.mem_comap, h𝔰A]
    exact hq hϖq
  obtain ⟨P, hP, hP𝔰, hϖP, hPmin, hPdiv⟩ :=
    exists_prime_of_etale_polynomial hϖ₁ hϖ₁0 f₂ hf₂ 𝔰 hϖ𝔰
  -- going down from `𝔭` to `q`
  have hQ : ∃ Q : Ideal E, Q.IsPrime ∧ Q ≤ 𝔰 ∧ Q.comap θ = q := by
    letI : Algebra A E := θ.toAlgebra
    haveI : Algebra.Etale A E := hθ
    haveI : 𝔰.LiesOver 𝔭 := ⟨h𝔰A.symm⟩
    obtain ⟨Q, hQ𝔰, hQ, hQl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := 𝔭) 𝔰 hq
    exact ⟨Q, hQ, hQ𝔰, hQl.over.symm⟩
  obtain ⟨Q, hQ, hQ𝔰, hQq⟩ := hQ
  have hϖQ : f₂ (Polynomial.C ϖ₁) ∈ Q := by
    rw [hθO, ← Ideal.mem_comap, hQq]
    exact hϖq
  have hPQ := hPmin Q hQ hQ𝔰 hϖQ
  have hPA : P.comap θ = q := hmin _ (Ideal.comap_isPrime _ _)
    (by rw [Ideal.mem_comap, ← hθO]; exact hϖP) (hQq ▸ Ideal.comap_mono hPQ)
  -- the pulled back coordinates lie in `P`
  set uE := iR (f (Node.u (ϖ₂ ^ n)))
  set vE := iR (f (Node.v (ϖ₂ ^ n)))
  have huvE : uE * vE = θ (φ (algebraMap O₂ B ϖ₂)) ^ n := by
    rw [← map_mul, ← map_mul, Node.u_mul_v, ← RingHom.comp_apply f, hO, RingHom.comp_apply,
      map_pow, map_pow, hθφ, map_pow]
  have hrelE : uE ^ a * vE ^ a = f₂ (Polynomial.C ϖ₁) ^ (m * n) * θ ε ^ n := by
    rw [← mul_pow, huvE, ← pow_mul, mul_comm n a, pow_mul, ← map_pow, hrel, map_mul, mul_pow,
      map_pow, hθO, ← pow_mul]
  have hmem𝔰 : ∀ y, y ∈ 𝔮 → iR y ∈ 𝔰 := fun y hy ↦ by
    rw [← Ideal.mem_comap, h𝔰₂]
    exact hy
  have hpos : a ≠ 0 := by omega
  obtain ⟨huP, hvP⟩ := hPdiv (m * n) _ _ _ (Ideal.pow_mem_of_mem 𝔰 (hmem𝔰 _ hu) a (by omega))
    (Ideal.pow_mem_of_mem 𝔰 (hmem𝔰 _ hv) a (by omega))
    (fun h ↦ h𝔰.ne_top (Ideal.eq_top_of_isUnit_mem _ h ((hε.map θ).pow n))) hrelE
  have huP' : uE ∈ P := hP.mem_of_pow_mem a huP
  have hvP' : vE ∈ P := hP.mem_of_pow_mem a hvP
  -- `P` lies over the node
  haveI : (P.comap iR).IsPrime := Ideal.comap_isPrime _ _
  have hPC : P.comap iR = 𝔮 := by
    refine eq_of_le_of_u_v_mem hϖ₂ hf ?_ huP' hvP'
    rw [← h𝔰₂]
    exact Ideal.comap_mono hP𝔰
  calc q.comap φ = (P.comap θ).comap φ := by rw [hPA]
    _ = (P.comap iR).comap g := by
      rw [Ideal.comap_comap, Ideal.comap_comap]
      congr 1
      exact RingHom.ext hθφ
    _ = 𝔭.comap φ := by rw [hPC, hc]

end SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

open _root_.SemistableReduction

/-- The global sections of a model given by the elements of the base. -/
noncomputable def globHom {O : Type u} [CommRing O] (c : TemperedFundamentalGroups.ModelCode O) :
    O →+* Γ(c.scheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ c.toSpec.appTop).hom

lemma algebraMap_eq_globHom {O : Type u} [CommRing O] (c : TemperedFundamentalGroups.ModelCode O)
    (U : c.scheme.Opens) (o : O) :
    letI := sectionsAlgebra c U
    algebraMap O Γ(c.scheme, U) o = (c.scheme.presheaf.map (homOfLE le_top).op).hom (globHom c o) :=
  rfl

lemma appTop_res {X Y : Scheme.{u}} (ψ : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (h : V ≤ ψ ⁻¹ᵁ U)
    (s : Γ(Y, ⊤)) :
    (X.presheaf.map (homOfLE le_top).op).hom (ψ.appTop.hom s) =
      (ψ.appLE U V h).hom ((Y.presheaf.map (homOfLE le_top).op).hom s) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rfl

section Base

variable {O₁ O₂ : Type u} [CommRing O₁] [CommRing O₂]
  {c₁ : TemperedFundamentalGroups.ModelCode O₁} {c₂ : TemperedFundamentalGroups.ModelCode O₂}
lemma appTop_globHom {O₀ : Type u} [CommRing O₀] (ι₁ : O₀ →+* O₁) (ι₂ : O₀ →+* O₂)
    (ψ : c₁.scheme ⟶ c₂.scheme)
    (hψ : ψ ≫ c₂.toSpec ≫ Spec.map (CommRingCat.ofHom ι₂) =
      c₁.toSpec ≫ Spec.map (CommRingCat.ofHom ι₁)) (o : O₀) :
    ψ.appTop.hom (globHom c₂ (ι₂ o)) = globHom c₁ (ι₁ o) := by
  have h := congrArg Scheme.Hom.appTop hψ
  simp only [Scheme.Hom.comp_appTop] at h
  have key : CommRingCat.ofHom ι₂ ≫ (Scheme.ΓSpecIso (CommRingCat.of O₂)).inv ≫
      c₂.toSpec.appTop ≫ ψ.appTop = CommRingCat.ofHom ι₁ ≫
        (Scheme.ΓSpecIso (CommRingCat.of O₁)).inv ≫ c₁.toSpec.appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, ← Category.assoc (CommRingCat.ofHom ι₁),
      Scheme.ΓSpecIso_inv_naturality, Category.assoc, Category.assoc, ← h]
    simp only [Category.assoc]
  exact congrArg (fun φ ↦ φ.hom o) key

/-- The relation of uniformizers along a morphism of models over a common base. -/
theorem exists_rel_of_comp_eq {O₀ : Type u} [CommRing O₀] (ι₁ : O₀ →+* O₁) (ι₂ : O₀ →+* O₂)
    (ψ : c₁.scheme ⟶ c₂.scheme)
    (hψ : ψ ≫ c₂.toSpec ≫ Spec.map (CommRingCat.ofHom ι₂) =
      c₁.toSpec ≫ Spec.map (CommRingCat.ofHom ι₁)) {ϖ₀ : O₀} {ϖ₁ : O₁} {ϖ₂ : O₂} {a m : ℕ}
    {ε₁ : O₁} {ε₂ : O₂} (hε₁ : IsUnit ε₁) (hε₂ : IsUnit ε₂) (h₁ : ι₁ ϖ₀ = ϖ₁ ^ m * ε₁)
    (h₂ : ι₂ ϖ₀ = ϖ₂ ^ a * ε₂) :
    ∃ ε : Γ(c₁.scheme, ⊤), IsUnit ε ∧
      ψ.appTop.hom (globHom c₂ ϖ₂) ^ a = globHom c₁ ϖ₁ ^ m * ε := by
  have h := appTop_globHom ι₁ ι₂ ψ hψ ϖ₀
  rw [h₁, h₂, map_mul, map_mul, map_pow, map_pow, map_mul, map_pow] at h
  obtain ⟨w, hw⟩ := hε₂.map (ψ.appTop.hom.comp (globHom c₂))
  rw [RingHom.comp_apply] at hw
  rw [← hw] at h
  refine ⟨globHom c₁ ε₁ * ↑w⁻¹, (hε₁.map _).mul (Units.isUnit _), ?_⟩
  calc _ = ψ.appTop.hom (globHom c₂ ϖ₂) ^ a * ↑w * ↑w⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [h, mul_assoc]

end Base

variable {O₁ O₂ : Type u} [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁]
  [CommRing O₂] [IsDomain O₂] [IsDiscreteValuationRing O₂]
  {c₁ : TemperedFundamentalGroups.ModelCode O₁} {c₂ : TemperedFundamentalGroups.ModelCode O₂}

/-- **Node reflection (M1).** Let `ψ : c₁ ⟶ c₂` be a morphism of projective models over discrete
valuation rings with `ψ^*(ϖ₂) ^ a = ϖ₁ ^ m ε` (`a ≥ 1`, `ε` a unit), `c₂` semistable. If `z` is a
smooth point of the special fibre of `c₁`, `η` a generization of `z` which is a generic point of
the special fibre (a component through `z`) and `ψ z` a node point, then `ψ η = ψ z`. -/
theorem map_eq_of_isNodePt {ϖ₁ : O₁} (hϖ₁ : Irreducible ϖ₁) {ϖ₂ : O₂} (hϖ₂ : Irreducible ϖ₂)
    (hc₂ : IsSemistable ϖ₂ c₂) (ψ : c₁.scheme ⟶ c₂.scheme) {a m : ℕ} {ε : Γ(c₁.scheme, ⊤)}
    (ha : 1 ≤ a) (hε : IsUnit ε)
    (hrel : ψ.appTop.hom (globHom c₂ ϖ₂) ^ a = globHom c₁ ϖ₁ ^ m * ε)
    {z η : c₁.scheme} (hz : z ∈ Z c₁) (hzs : ¬ IsNodePt c₁ z) (hηz : η ⤳ z)
    (hηZ : η ∈ Z c₁) (hmin : ∀ x ∈ Z c₁, x ⤳ η → x = η) (hy : IsNodePt c₂ (ψ z)) :
    ψ η = ψ z := by
  obtain ⟨n, -, hnt⟩ := exists_isNodeOfThickness hc₂ hy
  obtain ⟨U', hU', hyU', -⟩ := hc₂ (ψ z)
  have hnode := hnt.isNodeAt hU' hyU'
  have hsm : IsSmoothPt c₁ z := by
    by_contra h
    exact hzs ⟨hz, h⟩
  obtain ⟨U₀, hU₀, hz₀, hloc⟩ := hsm
  obtain ⟨f₀, hf₀ψ, hzV⟩ := hU₀.exists_basicOpen_le (V := ψ ⁻¹ᵁ U') ⟨z, hyU'⟩ hz₀
  set V := c₁.scheme.basicOpen f₀ with hVdef
  have hV : IsAffineOpen V := hU₀.basicOpen f₀
  have hVU₀ : V ≤ U₀ := c₁.scheme.basicOpen_le f₀
  letI := sectionsAlgebra c₁ U₀
  letI := sectionsAlgebra c₁ V
  letI := sectionsAlgebra c₂ U'
  have hsV : IsEtaleLocallyAt O₁ O₁[X] (hV.primeIdealOf ⟨z, hzV⟩).asIdeal := by
    refine IsEtaleLocallyAt.of_etale (restrictAlgHom c₁ hVU₀) (restrict_etale hU₀ f₀ rfl hVU₀)
      _ ?_
    rw [restrictAlgHom_toRingHom, comap_primeIdealOf_restrict hU₀ hV hVU₀ hzV]
    exact hloc
  set φ := (ψ.appLE U' V hf₀ψ).hom
  have hηV : η ∈ V := hηz.mem_open V.isOpen hzV
  have hcz := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE U' hU' V hV hf₀ψ hzV)
  have hcη := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE U' hU' V hV hf₀ψ hηV)
  rw [PrimeSpectrum.comap_asIdeal] at hcz hcη
  have hind : Topology.IsInducing hV.fromSpec := hV.fromSpec.isOpenEmbedding.isInducing
  set 𝔭 := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
  set q := (hV.primeIdealOf ⟨η, hηV⟩).asIdeal
  have hq : q ≤ 𝔭 := by
    have : hV.fromSpec (hV.primeIdealOf ⟨η, hηV⟩) ⤳ hV.fromSpec (hV.primeIdealOf ⟨z, hzV⟩) := by
      rw [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf]; exact hηz
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr (hind.specializes_iff.mp this)
  have hϖq : algebraMap O₁ Γ(c₁.scheme, V) ϖ₁ ∈ q := (mem_Z_iff hϖ₁ hV hηV).mp hηZ
  have hminq : ∀ Q : Ideal Γ(c₁.scheme, V), Q.IsPrime → algebraMap O₁ _ ϖ₁ ∈ Q → Q ≤ q →
      Q = q := by
    intro Q hQ hϖQ hQle
    let p : PrimeSpectrum Γ(c₁.scheme, V) := ⟨Q, hQ⟩
    set x := hV.fromSpec p
    have hxV : x ∈ V := by
      have : x ∈ Set.range hV.fromSpec := Set.mem_range_self p
      rwa [hV.range_fromSpec] at this
    have hpx : hV.primeIdealOf ⟨x, hxV⟩ = p := by
      apply hV.fromSpec.isOpenEmbedding.injective
      rw [hV.fromSpec_primeIdealOf]
    have hxη : x ⤳ η := by
      have : p ⤳ hV.primeIdealOf ⟨η, hηV⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hQle
      have := hind.specializes_iff.mpr this
      rwa [hV.fromSpec_primeIdealOf] at this
    have hxZ : x ∈ Z c₁ := by
      rw [mem_Z_iff hϖ₁ hV hxV, hpx]; exact hϖQ
    have hx := hmin x hxZ hxη
    have : p = hV.primeIdealOf ⟨η, hηV⟩ := by
      rw [← hpx]; congr 1; exact Subtype.ext hx
    exact congrArg PrimeSpectrum.asIdeal this
  have hrelV : φ (algebraMap O₂ Γ(c₂.scheme, U') ϖ₂) ^ a =
      algebraMap O₁ Γ(c₁.scheme, V) ϖ₁ ^ m *
        (c₁.scheme.presheaf.map (homOfLE le_top).op).hom ε := by
    rw [algebraMap_eq_globHom, algebraMap_eq_globHom, ← appTop_res ψ hf₀ψ, ← map_pow, hrel,
      map_mul, map_pow]
  have hmaxϖ₁ : (Ideal.span {ϖ₁}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ₁
  have hϖ₂le : IsLocalRing.maximalIdeal O₂ ≤ Ideal.span {ϖ₂} :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₂).mp hϖ₂).le
  have key := comap_eq_of_isNodeAt hmaxϖ₁ hϖ₁.ne_zero hϖ₂le φ hsV (n := n) (hcz ▸ hnode) ha
    (hε.map _) hrelV hq hϖq hminq
  rw [hcz, hcη] at key
  have hpt : hU'.primeIdealOf ⟨ψ η, hf₀ψ hηV⟩ = hU'.primeIdealOf ⟨ψ z, hf₀ψ hzV⟩ :=
    PrimeSpectrum.ext key
  have := congrArg hU'.fromSpec hpt
  rwa [hU'.fromSpec_primeIdealOf, hU'.fromSpec_primeIdealOf] at this

end TemperedFundamentalGroups.SemistableReduction.ModelCode
