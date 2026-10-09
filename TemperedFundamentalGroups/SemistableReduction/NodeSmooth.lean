/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeThickness

/-!
# Away from its singular point, a node is smooth (W8′, H3b)

Blueprint §9.7. `O[u, v] ⧸ (u v - c)` localized away from `u` is `O[X]` localized away from `X`
(`Node.awayUEquiv`). Hence an `O`-algebra which is étale-locally at `𝔭` a node at a point where
`u` or `v` is a unit is étale-locally `O[X]` at `𝔭` (`isEtaleLocallyAt_polynomial_of_notMem`); so at
a non-smooth point every étale node chart is at the singular point (`IsNodeAt`), and the
thickness of such a point is `≥ 1`.
-/

universe u

open Polynomial

namespace SemistableReduction

variable {O : Type u} [CommRing O] (c : O)

namespace Node

/-- The swap `u ↔ v` of the node. -/
noncomputable def swap : Node O c →ₐ[O] Node O c :=
  lift (v c) (u c) (by rw [mul_comm, u_mul_v])

@[simp] lemma swap_u : swap c (u c) = v c := lift_u ..

@[simp] lemma swap_v : swap c (v c) = u c := lift_v ..

lemma swap_swap : (swap c).comp (swap c) = AlgHom.id O (Node O c) :=
  algHom_ext (by simp) (by simp)

lemma swap_bijective : Function.Bijective (swap c) :=
  Function.bijective_iff_has_inverse.mpr ⟨swap c, fun x ↦ AlgHom.congr_fun (swap_swap c) x,
    fun x ↦ AlgHom.congr_fun (swap_swap c) x⟩

/-- `O[X]` localized away from `X`. -/
abbrev PX : Type u := Localization.Away (X : O[X])

/-- The node localized away from `u`. -/
abbrev NU : Type u := Localization.Away (u c)

/-- `O[X]_X → O[u, v]_u`, `X ↦ u`. -/
noncomputable def toNU : PX (O := O) →ₐ[O] NU c :=
  IsLocalization.Away.liftAlgHom (X : O[X]) (f := aeval (algebraMap (Node O c) (NU c) (u c)))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (S := NU c) (u c))

/-- `O[u, v]_u → O[X]_X`, `u ↦ X`, `v ↦ c X⁻¹`. -/
noncomputable def ofNU : NU c →ₐ[O] PX (O := O) :=
  IsLocalization.Away.liftAlgHom (u c)
    (f := lift (algebraMap O[X] (PX (O := O)) X)
      (algebraMap O (PX (O := O)) c * IsLocalization.Away.invSelf (X : O[X])) (by
        rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]))
    (by rw [lift_u]; exact IsLocalization.Away.algebraMap_isUnit _)

lemma toNU_algebraMap_X : toNU c (algebraMap O[X] (PX (O := O)) X) =
    algebraMap (Node O c) (NU c) (u c) := by
  rw [toNU, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
  simp

lemma ofNU_algebraMap (x : Node O c) : ofNU c (algebraMap (Node O c) (NU c) x) =
    lift (algebraMap O[X] (PX (O := O)) X)
      (algebraMap O (PX (O := O)) c * IsLocalization.Away.invSelf (X : O[X])) (by
        rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]) x := by
  rw [ofNU, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
  rfl

lemma ofNU_comp_toNU : (ofNU c).comp (toNU c) = AlgHom.id O (PX (O := O)) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (X : O[X]))
  refine Polynomial.algHom_ext ?_
  change ofNU c (toNU c (algebraMap O[X] (PX (O := O)) X)) = algebraMap O[X] (PX (O := O)) X
  rw [toNU_algebraMap_X, ofNU_algebraMap, lift_u]

lemma toNU_comp_ofNU : (toNU c).comp (ofNU c) = AlgHom.id O (NU c) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (u c))
  refine algHom_ext ?_ ?_
  · change toNU c (ofNU c (algebraMap (Node O c) (NU c) (u c))) = algebraMap (Node O c) (NU c) (u c)
    rw [ofNU_algebraMap, lift_u, toNU_algebraMap_X]
  · change toNU c (ofNU c (algebraMap (Node O c) (NU c) (v c))) = algebraMap (Node O c) (NU c) (v c)
    rw [ofNU_algebraMap, lift_v, map_mul, AlgHom.commutes]
    have hw : algebraMap (Node O c) (NU c) (u c) *
        toNU c (IsLocalization.Away.invSelf (X : O[X])) = 1 := by
      rw [← toNU_algebraMap_X, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have huv : algebraMap (Node O c) (NU c) (u c) * algebraMap (Node O c) (NU c) (v c) =
        algebraMap O (NU c) c := by
      rw [← map_mul, u_mul_v, ← IsScalarTower.algebraMap_apply]
    rw [← huv]
    linear_combination (algebraMap (Node O c) (NU c) (v c)) * hw

/-- `O[u, v] ⧸ (u v - c)` localized away from `u` is `O[X]` localized away from `X`. -/
noncomputable def awayUEquiv : PX (O := O) ≃ₐ[O] NU c :=
  AlgEquiv.ofAlgHom (toNU c) (ofNU c) (toNU_comp_ofNU c) (ofNU_comp_toNU c)

end Node

variable {c} {A : Type u} [CommRing A] [Algebra O A]

/-- **A node chart at a point where `u` is a unit is a smooth chart.** -/
theorem isEtaleLocallyAt_polynomial_of_u_notMem {𝔭 : Ideal A} {C : Type u} [CommRing C]
    {g : A →+* C} {f : Node O c →+* C} {𝔮 : Ideal C} (hg : g.Etale) (hf : f.Etale)
    (h𝔮 : 𝔮.IsPrime) (hc : 𝔮.comap g = 𝔭) (hO : f.comp (algebraMap O _) = g.comp (algebraMap O A))
    (hu : f (Node.u c) ∉ 𝔮) : IsEtaleLocallyAt O O[X] 𝔭 := by
  classical
  set C' := Localization.Away (f (Node.u c))
  letI : Algebra (Node O c) C := f.toAlgebra
  haveI : Algebra.Etale (Node O c) C := RingHom.etale_algebraMap.mp hf
  -- `Node_u → C_{f u}`
  set ι : Node.NU c →+* C' := IsLocalization.Away.map (Node.NU c) C' f (Node.u c)
  letI : Algebra (Node.NU c) C' := ι.toAlgebra
  haveI : IsScalarTower (Node O c) (Node.NU c) C' :=
    IsScalarTower.of_algebraMap_eq (R := Node O c) (S := Node.NU c) (A := C') fun x ↦ by
      rw [IsScalarTower.algebraMap_apply (Node O c) C C']
      change _ = ι (algebraMap _ _ x)
      simp only [ι, IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
  haveI : Algebra.Etale C C' := Algebra.Etale.of_isLocalizationAway (f (Node.u c))
  haveI : Algebra.Etale (Node O c) C' := Algebra.Etale.comp (Node O c) C C'
  haveI : Algebra.Etale (Node O c) (Node.NU c) := Algebra.Etale.of_isLocalizationAway (Node.u c)
  haveI : Algebra.Etale (Node.NU c) C' := Algebra.Etale.of_restrictScalars (Node O c) _ _
  have hι : ι.Etale := RingHom.etale_algebraMap.mpr inferInstance
  have hloc : (algebraMap C C').Etale := RingHom.etale_algebraMap.mpr inferInstance
  have hX : (algebraMap O[X] (Node.PX (O := O))).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (X : O[X]))
  have he : (Node.awayUEquiv c).toAlgHom.toRingHom.Etale :=
    RingHom.Etale.of_bijective (Node.awayUEquiv c).bijective
  have hd : Disjoint (Submonoid.powers (f (Node.u c)) : Set C) 𝔮 := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hu (h𝔮.mem_of_pow_mem k hk)
  refine ⟨C', inferInstance, (algebraMap C C').comp g,
    ι.comp ((Node.awayUEquiv c).toAlgHom.toRingHom.comp (algebraMap O[X] (Node.PX (O := O)))),
    𝔮.map (algebraMap C C'), RingHom.Etale.stableUnderComposition _ _ hg hloc,
    RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.stableUnderComposition _ _ hX he) hι,
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (f (Node.u c))) C' 𝔮 h𝔮 hd, ?_,
    ?_⟩
  · rw [← Ideal.comap_comap]
    change Ideal.comap g ((𝔮.map (algebraMap C C')).under C) = 𝔭
    rw [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (f (Node.u c))) C' h𝔮 hd,
      hc]
  · ext o
    have e1 : (Node.awayUEquiv c) (algebraMap O[X] (Node.PX (O := O)) (algebraMap O O[X] o)) =
        algebraMap (Node O c) (Node.NU c) (algebraMap O (Node O c) o) := by
      rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, IsScalarTower.algebraMap_apply O
        (Node O c) (Node.NU c)]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
    erw [e1]
    simp only [ι, IsLocalization.Away.map, IsLocalization.map_eq]
    rw [← RingHom.comp_apply f, hO, RingHom.comp_apply]

/-- **A node chart at a point where `u` or `v` is a unit is a smooth chart.** -/
theorem isEtaleLocallyAt_polynomial_of_notMem {𝔭 : Ideal A} {C : Type u} [CommRing C]
    {g : A →+* C} {f : Node O c →+* C} {𝔮 : Ideal C} (hg : g.Etale) (hf : f.Etale)
    (h𝔮 : 𝔮.IsPrime) (hc : 𝔮.comap g = 𝔭) (hO : f.comp (algebraMap O _) = g.comp (algebraMap O A))
    (huv : f (Node.u c) ∉ 𝔮 ∨ f (Node.v c) ∉ 𝔮) : IsEtaleLocallyAt O O[X] 𝔭 := by
  rcases huv with hu | hv
  · exact isEtaleLocallyAt_polynomial_of_u_notMem hg hf h𝔮 hc hO hu
  · refine isEtaleLocallyAt_polynomial_of_u_notMem (f := f.comp (Node.swap c).toRingHom) hg
      (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective
        (Node.swap_bijective c)) hf) h𝔮 hc ?_ (by simpa using hv)
    rw [RingHom.comp_assoc, ← hO]
    congr 1
    ext o
    exact (Node.swap c).commutes o

/-- At a point which is not smooth, an étale node chart is at the singular point. -/
theorem isNodeAt_of_not_smooth {ϖ : O} {n : ℕ} {𝔭 : Ideal A}
    (h : IsEtaleLocallyAt O (Node O (ϖ ^ n)) 𝔭) (hs : ¬ IsEtaleLocallyAt O O[X] 𝔭) :
    IsNodeAt ϖ n 𝔭 := by
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hc, hO⟩ := h
  refine ⟨C, inferInstance, g, f, 𝔮, hg, hf, h𝔮, hc, hO, ?_, ?_⟩
  · by_contra hu
    exact hs (isEtaleLocallyAt_polynomial_of_notMem hg hf h𝔮 hc hO (.inl hu))
  · by_contra hv
    exact hs (isEtaleLocallyAt_polynomial_of_notMem hg hf h𝔮 hc hO (.inr hv))

/-- The thickness of a node point is positive. -/
theorem IsNodeAt.pos {ϖ : O} {n : ℕ} {𝔭 : Ideal A} (h : IsNodeAt ϖ n 𝔭) : 0 < n := by
  obtain ⟨C, _, g, f, 𝔮, -, -, h𝔮, -, -, hu, -⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    apply h𝔮.ne_top
    rw [Ideal.eq_top_iff_one]
    have : f (Node.u (ϖ ^ 0)) * f (Node.v (ϖ ^ 0)) = 1 := by
      rw [← map_mul, Node.u_mul_v]
      simp
    rw [← this]
    exact Ideal.mul_mem_right _ _ hu
  · exact hn

/-- **A non-smooth semistable point is a node of a unique thickness `n ≥ 1`.** -/
theorem exists_unique_isNodeAt [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {𝔭 : Ideal A} [𝔭.IsPrime] (h : IsSemistableAt ϖ 𝔭)
    (hs : ¬ IsEtaleLocallyAt O O[X] 𝔭) : ∃! n, IsNodeAt ϖ n 𝔭 := by
  rcases h with ⟨n, hn⟩ | h
  · exact ⟨n, isNodeAt_of_not_smooth hn hs, fun m hm ↦ hm.unique hϖ (isNodeAt_of_not_smooth hn hs)⟩
  · exact absurd h hs

end SemistableReduction
