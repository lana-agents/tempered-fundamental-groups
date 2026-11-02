/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerChart

/-!
# The Kummer factors at a node are the points of the normalisation over the node
(MR12, interface I5(a))

Let `R → N₁` be an étale neighbourhood of a maximal ideal `𝔪 ⊆ R` with a point `𝔫` over `𝔪`
and trivial residue field extension, and `B` an `R`-algebra with a splitting
`N₁ ⊗_R B ≃ ∏ᵢ N₁ ⊗_{O[u,v]/(uv - cᵢ^{dᵢ})} O[w,z]/(wz - cᵢ)` into Kummer nodes (the data
`FormalKummer.KummerNormAtData`). Then the primes of `B` over `𝔪` are in bijection with the
factors (**`FormalKummer.KummerNormAtData.primesEquiv`**). Generic steps:

* `KummerPrimes.PrimesOver S p`: the primes of `S` lying over `p`; `primesOverCongr` (transport
  along algebra equivalences), `primesOverPi` (primes of a finite product: `Σ i`, from
  `PrimeSpectrum.sigmaToPi_bijective`);
* **`KummerPrimes.primesOverBaseChange`**: for `𝔫` over `𝔪` with `R → N₁ ⧸ 𝔫` surjective, the
  primes of `N₁ ⊗_R B` over `𝔫` are the primes of `B` over `𝔪` (by `P ↦ P ∩ B`);
* `KummerPrimes.primesOverAway`: the primes of `B₁[1/s]` over a prime `𝔪` of `R[1/s]` are the
  primes of `B₁` over `𝔪 ∩ R`;
* **`KummerPrimes.uniquePrimesOverKummerNodeFactor`**: a Kummer node factor
  `N₁ ⊗_{O[u,v]/(uv - c^d)} O[w,z]/(wz - c)` has exactly one prime over a prime `𝔫` of `N₁`
  containing `u`, `v` and `c` (it contains `w`, `z`, and modulo `(w, z)` the factor is a quotient
  of `N₁`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace KummerPrimes

/-- **The primes of `S` lying over `p`.** -/
abbrev PrimesOver {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) : Type _ :=
  {P : Ideal S // P.IsPrime ∧ P.comap (algebraMap R S) = p}

section Transport

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']

/-- Primes over `p` transported along an algebra equivalence (`P ↦ e(P)`). -/
def primesOverCongr (e : S ≃ₐ[R] S') (p : Ideal R) : PrimesOver S p ≃ PrimesOver S' p where
  toFun P := ⟨P.1.comap (e.symm : S' →+* S), by haveI := P.2.1; infer_instance, by
    have h : (e.symm : S' →+* S).comp (algebraMap R S') = algebraMap R S :=
      RingHom.ext fun r ↦ e.symm.commutes r
    rw [Ideal.comap_comap, h]
    exact P.2.2⟩
  invFun P := ⟨P.1.comap (e : S →+* S'), by haveI := P.2.1; infer_instance, by
    have h : (e : S →+* S').comp (algebraMap R S) = algebraMap R S' :=
      RingHom.ext fun r ↦ e.commutes r
    rw [Ideal.comap_comap, h]
    exact P.2.2⟩
  left_inv P := Subtype.ext (Ideal.ext fun x ↦ by simp [Ideal.mem_comap])
  right_inv P := Subtype.ext (Ideal.ext fun x ↦ by simp [Ideal.mem_comap])

lemma primesOverCongr_apply (e : S ≃ₐ[R] S') (p : Ideal R) (P : PrimesOver S p) :
    (primesOverCongr e p P).1 = P.1.comap (e.symm : S' →+* S) :=
  rfl

end Transport

section Pi

variable {R : Type*} [CommRing R] {ι : Type*} (F : ι → Type*) [∀ i, CommRing (F i)]
  [∀ i, Algebra R (F i)]

lemma comap_sigmaToPi (i : ι) (q : PrimeSpectrum (F i)) :
    (PrimeSpectrum.sigmaToPi F ⟨i, q⟩).asIdeal.comap (algebraMap R (∀ i, F i)) =
      q.asIdeal.comap (algebraMap R (F i)) := by
  rw [PrimeSpectrum.sigmaToPi_apply, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap]
  rfl

/-- **The primes of a finite product over `p`** are the primes of the factors over `p`. -/
noncomputable def primesOverPi [Finite ι] (p : Ideal R) :
    PrimesOver (∀ i, F i) p ≃ Σ i, PrimesOver (F i) p :=
  ({ toFun := fun P ↦ ⟨⟨P.1, P.2.1⟩, P.2.2⟩
     invFun := fun x ↦ ⟨x.1.asIdeal, x.1.isPrime, x.2⟩
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl } :
    PrimesOver (∀ i, F i) p ≃ {x : PrimeSpectrum (∀ i, F i) //
      x.asIdeal.comap (algebraMap R (∀ i, F i)) = p}).trans <|
  ((Equiv.ofBijective _ (PrimeSpectrum.sigmaToPi_bijective F)).subtypeEquiv
    (p := fun s ↦ (PrimeSpectrum.sigmaToPi F s).asIdeal.comap (algebraMap R (∀ i, F i)) = p)
    (fun _ ↦ Iff.rfl)).symm.trans <|
  { toFun := fun s ↦ ⟨s.1.1, s.1.2.asIdeal, s.1.2.isPrime,
      (comap_sigmaToPi F s.1.1 s.1.2).symm.trans s.2⟩
    invFun := fun x ↦ ⟨⟨x.1, ⟨x.2.1, x.2.2.1⟩⟩,
      (comap_sigmaToPi F x.1 ⟨x.2.1, x.2.2.1⟩).trans x.2.2.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

end Pi

section BaseChange

variable {R N₁ B : Type*} [CommRing R] [CommRing N₁] [CommRing B] [Algebra R N₁] [Algebra R B]
  {𝔪 : Ideal R} {𝔫 : Ideal N₁}

/-- Modulo `𝔫 (N₁ ⊗_R B)`, every element of `N₁ ⊗_R B` comes from `B` if `R → N₁ ⧸ 𝔫` is
surjective. -/
lemma exists_sub_mem_map
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R N₁)))
    (x : N₁ ⊗[R] B) : ∃ b : B, x - Algebra.TensorProduct.includeRight b ∈
      𝔫.map (algebraMap N₁ (N₁ ⊗[R] B)) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
    obtain ⟨r, hr⟩ := hres (Ideal.Quotient.mk 𝔫 a)
    have hr' : a - algebraMap R N₁ r ∈ 𝔫 := by
      rw [← Ideal.Quotient.eq]; exact hr.symm
    refine ⟨r • b, ?_⟩
    have : a ⊗ₜ[R] b - Algebra.TensorProduct.includeRight (r • b) =
        algebraMap N₁ (N₁ ⊗[R] B) (a - algebraMap R N₁ r) * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.includeRight_apply, ← TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one, ← TensorProduct.sub_tmul,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr')
  | add x y hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    refine ⟨b + b', ?_⟩
    rw [map_add, add_sub_add_comm]
    exact add_mem hb hb'

variable (h𝔫 : 𝔫.comap (algebraMap R N₁) = 𝔪)
  (hres : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R N₁)))

include h𝔫 in
lemma comap_includeRight (P : PrimesOver (N₁ ⊗[R] B) 𝔫) :
    (P.1.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] N₁ ⊗[R] B).toRingHom).comap
      (algebraMap R B) = 𝔪 := by
  have h : (Algebra.TensorProduct.includeRight : B →ₐ[R] N₁ ⊗[R] B).toRingHom.comp
      (algebraMap R B) = (algebraMap N₁ (N₁ ⊗[R] B)).comp (algebraMap R N₁) :=
    RingHom.ext fun r ↦ by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply R N₁ (N₁ ⊗[R] B)]
  rw [Ideal.comap_comap, h, ← Ideal.comap_comap, P.2.2, h𝔫]

/-- `P ↦ P ∩ B`. -/
def primesOverRestrict (P : PrimesOver (N₁ ⊗[R] B) 𝔫) : PrimesOver B 𝔪 :=
  ⟨P.1.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] N₁ ⊗[R] B).toRingHom,
    by haveI := P.2.1; infer_instance, comap_includeRight h𝔫 P⟩

/-- The residue fields of `𝔪` and `𝔫` agree. -/
noncomputable def residueEquiv : R ⧸ 𝔪 ≃+* N₁ ⧸ 𝔫 :=
  RingEquiv.ofBijective (Ideal.quotientMap 𝔫 (algebraMap R N₁) h𝔫.ge)
    ⟨Ideal.quotientMap_injective' h𝔫.le, fun x ↦ by
      obtain ⟨r, hr⟩ := hres x
      exact ⟨Ideal.Quotient.mk 𝔪 r, by rw [Ideal.quotientMap_mk]; exact hr⟩⟩

lemma residueEquiv_mk (r : R) :
    residueEquiv h𝔫 hres (Ideal.Quotient.mk 𝔪 r) = Ideal.Quotient.mk 𝔫 (algebraMap R N₁ r) :=
  rfl

/-- For `Q` over `𝔪`: `N₁ → N₁ ⧸ 𝔫 ≅ R ⧸ 𝔪 → B ⧸ Q`. -/
noncomputable def toQuot (Q : PrimesOver B 𝔪) : N₁ →ₐ[R] B ⧸ Q.1 :=
  { toRingHom := (Ideal.quotientMap Q.1 (algebraMap R B) Q.2.2.ge).comp
      ((residueEquiv h𝔫 hres).symm.toRingHom.comp (Ideal.Quotient.mk 𝔫))
    commutes' := fun r ↦ by
      change Ideal.quotientMap Q.1 (algebraMap R B) Q.2.2.ge
        ((residueEquiv h𝔫 hres).symm (Ideal.Quotient.mk 𝔫 (algebraMap R N₁ r))) = _
      rw [← residueEquiv_mk h𝔫 hres, RingEquiv.symm_apply_apply, Ideal.quotientMap_mk]
      rfl }

lemma toQuot_eq_zero_iff (Q : PrimesOver B 𝔪) (a : N₁) : toQuot h𝔫 hres Q a = 0 ↔ a ∈ 𝔫 := by
  change Ideal.quotientMap Q.1 (algebraMap R B) Q.2.2.ge
    ((residueEquiv h𝔫 hres).symm (Ideal.Quotient.mk 𝔫 a)) = 0 ↔ _
  rw [← map_zero (Ideal.quotientMap Q.1 (algebraMap R B) Q.2.2.ge),
    (Ideal.quotientMap_injective' Q.2.2.le).eq_iff, ← map_zero (residueEquiv h𝔫 hres).symm,
    (residueEquiv h𝔫 hres).symm.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The map `N₁ ⊗_R B → B ⧸ Q` (`toQuot` on `N₁`, the quotient map on `B`). -/
noncomputable def extendMap (Q : PrimesOver B 𝔪) : N₁ ⊗[R] B →ₐ[R] B ⧸ Q.1 :=
  Algebra.TensorProduct.productMap (toQuot h𝔫 hres Q) (Ideal.Quotient.mkₐ R Q.1)

lemma extendMap_tmul (Q : PrimesOver B 𝔪) (a : N₁) (b : B) :
    extendMap h𝔫 hres Q (a ⊗ₜ[R] b) = toQuot h𝔫 hres Q a * Ideal.Quotient.mk Q.1 b := by
  rw [extendMap, Algebra.TensorProduct.productMap_apply_tmul, Ideal.Quotient.mkₐ_eq_mk]

/-- The prime of `N₁ ⊗_R B` over `𝔫` and `Q`: the kernel of `N₁ ⊗_R B → B ⧸ Q`. -/
noncomputable def primesOverExtend (Q : PrimesOver B 𝔪) : PrimesOver (N₁ ⊗[R] B) 𝔫 :=
  ⟨RingHom.ker (extendMap h𝔫 hres Q).toRingHom, by
    haveI := Q.2.1
    exact RingHom.ker_isPrime _, Ideal.ext fun a ↦ by
      rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      change extendMap h𝔫 hres Q (a ⊗ₜ[R] 1) = 0 ↔ _
      rw [extendMap_tmul, map_one, mul_one, toQuot_eq_zero_iff]⟩

lemma restrict_extend (Q : PrimesOver B 𝔪) :
    primesOverRestrict h𝔫 (primesOverExtend h𝔫 hres Q) = Q := by
  refine Subtype.ext (Ideal.ext fun b ↦ ?_)
  change extendMap h𝔫 hres Q (1 ⊗ₜ[R] b) = 0 ↔ _
  rw [extendMap_tmul, map_one, one_mul, Ideal.Quotient.eq_zero_iff_mem]

lemma mem_iff_of_restrict (P : PrimesOver (N₁ ⊗[R] B) 𝔫) (x : N₁ ⊗[R] B) (b : B)
    (hb : x - Algebra.TensorProduct.includeRight b ∈ 𝔫.map (algebraMap N₁ (N₁ ⊗[R] B))) :
    x ∈ P.1 ↔ b ∈ (primesOverRestrict h𝔫 P).1 := by
  have hle : 𝔫.map (algebraMap N₁ (N₁ ⊗[R] B)) ≤ P.1 :=
    Ideal.map_le_iff_le_comap.2 P.2.2.ge
  change _ ↔ Algebra.TensorProduct.includeRight b ∈ P.1
  constructor
  · intro hx
    have := P.1.sub_mem hx (hle hb)
    rwa [sub_sub_cancel] at this
  · intro h
    have := P.1.add_mem (hle hb) h
    rwa [sub_add_cancel] at this

include hres in
lemma restrict_injective : Function.Injective (primesOverRestrict (B := B) h𝔫) := by
  intro P P' h
  refine Subtype.ext (Ideal.ext fun x ↦ ?_)
  obtain ⟨b, hb⟩ := exists_sub_mem_map hres x
  rw [mem_iff_of_restrict h𝔫 P x b hb, mem_iff_of_restrict h𝔫 P' x b hb, h]

/-- **Primes over `𝔫` of an étale base change with trivial residue field extension**: the primes
of `N₁ ⊗_R B` over `𝔫` are the primes of `B` over `𝔪` (`P ↦ P ∩ B`). -/
noncomputable def primesOverBaseChange : PrimesOver (N₁ ⊗[R] B) 𝔫 ≃ PrimesOver B 𝔪 :=
  Equiv.ofBijective (primesOverRestrict h𝔫) ⟨restrict_injective h𝔫 hres,
    fun Q ↦ ⟨primesOverExtend h𝔫 hres Q, restrict_extend h𝔫 hres Q⟩⟩

lemma primesOverBaseChange_apply (P : PrimesOver (N₁ ⊗[R] B) 𝔫) :
    (primesOverBaseChange h𝔫 hres P).1 =
      P.1.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] N₁ ⊗[R] B).toRingHom :=
  rfl

end BaseChange

section Away

variable {R Rn B₁ Bn : Type*} [CommRing R] [CommRing Rn] [CommRing B₁] [CommRing Bn]
  [Algebra R Rn] [Algebra R B₁] [Algebra Rn Bn] [Algebra B₁ Bn] (s : R)
  [IsLocalization.Away s Rn] [IsLocalization.Away (algebraMap R B₁ s) Bn]
  (h : ∀ x, algebraMap Rn Bn (algebraMap R Rn x) = algebraMap B₁ Bn (algebraMap R B₁ x))
  (𝔪 : Ideal Rn) [𝔪.IsPrime]

include h in
lemma comap_comap_away (Q : Ideal Bn) :
    (Q.comap (algebraMap B₁ Bn)).comap (algebraMap R B₁) =
      (Q.comap (algebraMap Rn Bn)).comap (algebraMap R Rn) := by
  rw [Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  exact (RingHom.ext h).symm

include s in
lemma disjoint_powers (Q₁ : PrimesOver B₁ (𝔪.comap (algebraMap R Rn))) :
    Disjoint (Submonoid.powers (algebraMap R B₁ s) : Set B₁) Q₁.1 := by
  haveI := Q₁.2.1
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨n, rfl⟩ hn
  have hs : s ∈ Q₁.1.comap (algebraMap R B₁) := Q₁.2.1.mem_of_pow_mem n hn
  rw [Q₁.2.2, Ideal.mem_comap] at hs
  exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ hs
    (IsLocalization.Away.algebraMap_isUnit s))

/-- **Primes over a prime of a localization `Rn = R[1/s]`** in `Bn = B₁[1/s]`: the primes of
`B₁` over its contraction to `R`. -/
noncomputable def primesOverAway :
    PrimesOver Bn 𝔪 ≃ PrimesOver B₁ (𝔪.comap (algebraMap R Rn)) where
  toFun Q := ⟨Q.1.comap (algebraMap B₁ Bn), by haveI := Q.2.1; infer_instance, by
    rw [comap_comap_away h, Q.2.2]⟩
  invFun Q₁ := ⟨Q₁.1.map (algebraMap B₁ Bn),
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (algebraMap R B₁ s)) Bn Q₁.1
      Q₁.2.1 (disjoint_powers s 𝔪 Q₁), by
    refine (IsLocalization.orderEmbedding (Submonoid.powers s) Rn).injective ?_
    change Ideal.comap _ (Ideal.comap _ _) = Ideal.comap _ _
    rw [← comap_comap_away h, show Ideal.comap (algebraMap B₁ Bn)
      (Ideal.map (algebraMap B₁ Bn) Q₁.1) = Q₁.1 from IsLocalization.under_map_of_isPrime_disjoint
        (Submonoid.powers (algebraMap R B₁ s)) Bn Q₁.2.1 (disjoint_powers s 𝔪 Q₁), Q₁.2.2]⟩
  left_inv Q := Subtype.ext (IsLocalization.map_under (Submonoid.powers (algebraMap R B₁ s)) Bn
    Q.1)
  right_inv Q₁ := Subtype.ext (IsLocalization.under_map_of_isPrime_disjoint
    (Submonoid.powers (algebraMap R B₁ s)) Bn Q₁.2.1 (disjoint_powers s 𝔪 Q₁))

lemma primesOverAway_apply (Q : PrimesOver Bn 𝔪) :
    (primesOverAway s h 𝔪 Q).1 = Q.1.comap (algebraMap B₁ Bn) :=
  rfl

end Away

section Factor

/-- Every element of the node `O[u,v]/(uv - a)` is a constant modulo `(u, v)`. -/
lemma node_exists_sub_mem {O : Type*} [CommRing O] (a : O) (y : Node O a) :
    ∃ o : O, y - algebraMap O (Node O a) o ∈ Ideal.span {Node.u a, Node.v a} := by
  have hy : y ∈ Submodule.span O (Set.range (Node.monomial a)) := by
    rw [Node.span_eq_top]; trivial
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, rfl⟩ := hz
    rcases s with ((_ | i) | j)
    · exact ⟨1, by simp [Node.monomial]⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, sub_zero]
      simp only [Node.monomial, Sum.elim_inl, pow_succ]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · refine ⟨0, ?_⟩
      rw [map_zero, sub_zero]
      simp only [Node.monomial, Sum.elim_inr, pow_succ]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨o, ho⟩ := hx
    obtain ⟨o', ho'⟩ := hy
    exact ⟨o + o', by rw [map_add, add_sub_add_comm]; exact add_mem ho ho'⟩
  | smul r x _ hx =>
    obtain ⟨o, ho⟩ := hx
    exact ⟨r * o, by
      rw [map_mul, Algebra.smul_def, ← mul_sub]; exact Ideal.mul_mem_left _ _ ho⟩

variable {O : Type u} [CommRing O] {N₁ : Type u} [CommRing N₁] [Algebra O N₁] {c : O} {d : ℕ}
  [Algebra (Node O (c ^ d)) N₁] [IsScalarTower O (Node O (c ^ d)) N₁]

/-- The ideal `(w, z)` of the Kummer node factor. -/
noncomputable abbrev wzIdeal : Ideal (KummerNodeFactor (c := c) (d := d) N₁) :=
  (Ideal.span {KNode.u c d, KNode.v c d}).map
    (Algebra.TensorProduct.includeRight : KNode c d →ₐ[Node O (c ^ d)] _)

lemma algebraMap_KNode (o : O) : algebraMap O (KNode c d) o =
    algebraMap (Node O (c ^ d)) (KNode c d) (algebraMap O (Node O (c ^ d)) o) :=
  ((Node.kummer c d).commutes o).symm

/-- Modulo `(w, z)`, every element of the Kummer node factor comes from `N₁`. -/
lemma kummerNodeFactor_exists_sub_mem (x : KummerNodeFactor (c := c) (d := d) N₁) :
    ∃ a : N₁, x - algebraMap N₁ _ a ∈ wzIdeal (c := c) (d := d) (N₁ := N₁) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a y =>
    obtain ⟨o, ho⟩ := node_exists_sub_mem c y
    refine ⟨a * algebraMap O N₁ o, ?_⟩
    have : a ⊗ₜ[Node O (c ^ d)] y - algebraMap N₁ (KummerNodeFactor (c := c) (d := d) N₁)
        (a * algebraMap O N₁ o) = (a ⊗ₜ 1) * Algebra.TensorProduct.includeRight
          (y - algebraMap O (KNode c d) o) := by
      have h1 : a ⊗ₜ[Node O (c ^ d)] algebraMap (Node O (c ^ d)) (KNode c d)
          (algebraMap O (Node O (c ^ d)) o) = (a * algebraMap (Node O (c ^ d)) N₁
            (algebraMap O (Node O (c ^ d)) o)) ⊗ₜ[Node O (c ^ d)] (1 : KNode c d) := by
        rw [Algebra.algebraMap_eq_smul_one (A := KNode c d), ← TensorProduct.smul_tmul,
          Algebra.smul_def, mul_comm a]
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul, TensorProduct.tmul_sub, algebraMap_KNode, h1,
        ← IsScalarTower.algebraMap_apply O (Node O (c ^ d)) N₁]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ho)
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨a + a', by rw [map_add, add_sub_add_comm]; exact add_mem ha ha'⟩

variable {𝔫 : Ideal N₁} [𝔫.IsPrime] (hu : algebraMap (Node O (c ^ d)) N₁ (Node.u (c ^ d)) ∈ 𝔫)
  (hv : algebraMap (Node O (c ^ d)) N₁ (Node.v (c ^ d)) ∈ 𝔫) (hc : algebraMap O N₁ c ∈ 𝔫)
  (hd : 0 < d)

omit [Algebra O N₁] [IsScalarTower O (Node O (c ^ d)) N₁] [𝔫.IsPrime] in
include hu hv in
lemma wzIdeal_le (P : PrimesOver (KummerNodeFactor (c := c) (d := d) N₁) 𝔫) :
    wzIdeal (c := c) (d := d) (N₁ := N₁) ≤ P.1 := by
  have key : ∀ r : Node O (c ^ d), algebraMap (Node O (c ^ d)) N₁ r ∈ 𝔫 →
      Algebra.TensorProduct.includeRight (A := N₁) (algebraMap (Node O (c ^ d)) (KNode c d) r)
        ∈ P.1 := fun r hr ↦ by
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    have : algebraMap N₁ (KummerNodeFactor (c := c) (d := d) N₁)
        (algebraMap (Node O (c ^ d)) N₁ r) ∈ P.1 := by
      rw [← Ideal.mem_comap, P.2.2]; exact hr
    rwa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
  refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
  rintro _ (rfl | rfl)
  · refine P.2.1.mem_of_pow_mem d ?_
    rw [← map_pow, KNode.u_pow]
    exact key _ hu
  · refine P.2.1.mem_of_pow_mem d ?_
    rw [← map_pow, KNode.v_pow]
    exact key _ hv

omit [Algebra O N₁] [IsScalarTower O (Node O (c ^ d)) N₁] [𝔫.IsPrime] in
include hu hv in
lemma mem_iff_of_wz (P : PrimesOver (KummerNodeFactor (c := c) (d := d) N₁) 𝔫)
    (x : KummerNodeFactor (c := c) (d := d) N₁) (a : N₁)
    (ha : x - algebraMap N₁ _ a ∈ wzIdeal (c := c) (d := d) (N₁ := N₁)) : x ∈ P.1 ↔ a ∈ 𝔫 := by
  have hle := wzIdeal_le hu hv P
  have hP : a ∈ 𝔫 ↔ algebraMap N₁ _ a ∈ P.1 := by rw [← Ideal.mem_comap, P.2.2]
  rw [hP]
  constructor
  · intro hx
    have := P.1.sub_mem hx (hle ha)
    rwa [sub_sub_cancel] at this
  · intro h
    have := P.1.add_mem (hle ha) h
    rwa [sub_add_cancel] at this

omit [𝔫.IsPrime] in
include hc in
lemma algebraMap_c_quot : (0 : N₁ ⧸ 𝔫) * 0 = algebraMap O (N₁ ⧸ 𝔫) c := by
  rw [mul_zero, ← Ideal.Quotient.mk_algebraMap, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
  exact hc

include hu hv hc hd in
/-- The map `KNode c d → N₁ ⧸ 𝔫`, `w, z ↦ 0`, over `O[u,v]/(uv - c^d)`. -/
noncomputable def knodeToQuot : KNode c d →ₐ[Node O (c ^ d)] N₁ ⧸ 𝔫 :=
  have key : (Node.lift (S := N₁ ⧸ 𝔫) 0 0 (algebraMap_c_quot hc)).comp (Node.kummer c d) =
      (Ideal.Quotient.mkₐ O 𝔫).comp (IsScalarTower.toAlgHom O (Node O (c ^ d)) N₁) :=
    Node.algHom_ext (by
      rw [AlgHom.comp_apply, Node.kummer_u, map_pow, Node.lift_u, zero_pow hd.ne',
        AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk, eq_comm,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hu) (by
      rw [AlgHom.comp_apply, Node.kummer_v, map_pow, Node.lift_v, zero_pow hd.ne',
        AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk, eq_comm,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hv)
  { (Node.lift (S := N₁ ⧸ 𝔫) 0 0 (algebraMap_c_quot hc)).toRingHom with
    commutes' := fun r ↦ DFunLike.congr_fun key r }

/-- The map of the Kummer node factor to `N₁ ⧸ 𝔫` (`w, z ↦ 0`). -/
noncomputable def kummerNodeFactorToQuot :
    KummerNodeFactor (c := c) (d := d) N₁ →ₐ[N₁] N₁ ⧸ 𝔫 :=
  Algebra.TensorProduct.lift (Algebra.ofId N₁ (N₁ ⧸ 𝔫)) (knodeToQuot hu hv hc hd)
    (fun _ _ ↦ Commute.all _ _)

/-- **A Kummer node factor has exactly one prime over `𝔫`** (`u, v, c ∈ 𝔫`). -/
@[reducible] noncomputable def uniquePrimesOverKummerNodeFactor :
    Unique (PrimesOver (KummerNodeFactor (c := c) (d := d) N₁) 𝔫) where
  default := ⟨RingHom.ker (kummerNodeFactorToQuot hu hv hc hd).toRingHom,
    RingHom.ker_isPrime _, Ideal.ext fun a ↦ by
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change kummerNodeFactorToQuot hu hv hc hd (algebraMap N₁ _ a) = 0 ↔ _
      rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]⟩
  uniq P := Subtype.ext (Ideal.ext fun x ↦ by
    obtain ⟨a, ha⟩ := kummerNodeFactor_exists_sub_mem (c := c) (d := d) (N₁ := N₁) x
    rw [mem_iff_of_wz hu hv P x a ha]
    exact (mem_iff_of_wz hu hv _ x a ha).symm)

end Factor

end KummerPrimes

namespace FormalKummer

open KummerPrimes

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] {ϖ : O} {n M' : ℕ} {x y : R} {𝔪 : Ideal R}

/-- The node algebra structure of the `i`-th factor of `KummerNormAtData`. -/
lemma KummerNormAtData.isScalarTower_node (D : KummerNormAtData ϖ n M' x y B 𝔪) (i : Fin D.r) :
    letI : Algebra O D.N₁ := ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra
    letI := nodeAlgebra D.N₁ (ϖ ^ (n / D.d i)) (D.d i)
      (by rw [← pow_mul, D.hmd i]; exact D.huv)
    IsScalarTower O (Node O ((ϖ ^ (n / D.d i)) ^ D.d i)) D.N₁ :=
  letI : Algebra O D.N₁ := ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra
  letI := nodeAlgebra D.N₁ (ϖ ^ (n / D.d i)) (D.d i)
    (by rw [← pow_mul, D.hmd i]; exact D.huv)
  IsScalarTower.of_algebraMap_eq fun o ↦ ((Node.lift _ _ _).commutes o).symm

/-- **I5(a), generic: the Kummer factors of `KummerNormAtData` at `𝔪` are the primes of `B`
over `𝔪`** (`x, y, ϖ ∈ 𝔪`, `n > 0`, trivial residue field extension at `𝔫`). -/
noncomputable def KummerNormAtData.primesEquiv (D : KummerNormAtData ϖ n M' x y B 𝔪)
    (hres : Function.Surjective ((Ideal.Quotient.mk D.𝔫).comp (algebraMap R D.N₁)))
    (hx : x ∈ 𝔪) (hy : y ∈ 𝔪) (hϖ : algebraMap O R ϖ ∈ 𝔪) (hn : 0 < n) :
    PrimesOver B 𝔪 ≃ Fin D.r :=
  letI : Algebra O D.N₁ := ((algebraMap R D.N₁).comp (algebraMap O R)).toAlgebra
  have hmem : ∀ r, r ∈ 𝔪 → algebraMap R D.N₁ r ∈ D.𝔫 := fun r hr ↦ by
    rw [← Ideal.mem_comap, D.comap_eq]; exact hr
  (primesOverBaseChange D.comap_eq hres).symm.trans <| (primesOverCongr D.Φ D.𝔫).trans <|
    (primesOverPi _ D.𝔫).trans <|
    @Equiv.sigmaUnique _ _ fun i ↦
      letI := nodeAlgebra D.N₁ (ϖ ^ (n / D.d i)) (D.d i)
        (by rw [← pow_mul, D.hmd i]; exact D.huv)
      haveI := D.isScalarTower_node i
      uniquePrimesOverKummerNodeFactor (c := ϖ ^ (n / D.d i)) (d := D.d i)
        (by
          simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            Node.lift_u]
          exact hmem x hx)
        (by
          simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            Node.lift_v]
          exact hmem y hy)
        (by
          rw [map_pow]
          refine Ideal.pow_mem_of_mem _ (hmem _ hϖ) _ (Nat.pos_of_ne_zero fun h0 ↦ ?_)
          have := D.hmd i
          rw [h0, zero_mul] at this
          exact hn.ne this)
        (D.hd i)

end FormalKummer

end SemistableReduction
