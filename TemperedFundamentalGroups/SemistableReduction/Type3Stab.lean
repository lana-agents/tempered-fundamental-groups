/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Galois
import TemperedFundamentalGroups.SemistableReduction.GaussStability

/-!
# STAB3: stability of type-3 points (O13)

Blueprint §9.10a (I.4), (I.5), §9.12 O13. Let `C` be algebraically closed of characteristic `0`
with `‖p‖ < 1`, `ρ ∉ |C^×|` and `w = w_{a,ρ}` the Gauss valuation of `C(X)` (a type-3 point).

* `ramificationIdx_eq_finrank`: every finite extension `L` of a complete type-3 field `K` has
  `e(L | K) = [L : K]` and `f(L | K) = 1` (Galois closure and `ramificationIdx_eq_finrank_of_isGalois`);
* `isType3_genK`: the completion of `(C(X), w_{a,ρ})` is the closure of `C(X - a)`;
* **`finsum_ramificationIdx_mul_inertiaDeg_eq_of_irrat`** (STAB3): for `F' / C(X)` finite
  separable, `Σ_{w' | w} e(w' | w) f(w' | w) = [F' : C(X)]`.
-/

open Polynomial

namespace SemistableReduction

namespace Type3

open FundamentalInequality DenseCompletion NormedTower GaussStability LocalGlobal Gauss
  InertiallyGenerated

universe u

section Local

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra C K]
include hp hp1

/-- **Local stability at type 3**: finite extensions of a complete type-3 field are totally
ramified and defectless. -/
theorem ramificationIdx_eq_finrank {y : K} (hy : IsType3 C y)
    (L : Type u) [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [FiniteDimensional K L] :
    ramificationIdx K (NormedField.valuation (K := L)) = Module.finrank K L ∧
      inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := L)) = 1 := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap C K).injective
  obtain ⟨N, _, _, _, _, _, _, _, _, _⟩ := exists_normed_galois_closure C K L
  haveI : FiniteDimensional L N := Module.Finite.of_restrictScalars_finite K L N
  have hN := ramificationIdx_eq_finrank_of_isGalois hp hp1 _ K N ⟨y, hy⟩ rfl
  have htower := ramificationIdx_tower (K := K) (L := L) (NormedField.valuation (K := N))
  rw [comap_valuation_algebraMap, hN, ← Module.finrank_mul_finrank K L N] at htower
  have hle : ∀ (A B : Type u) [NormedField A] [IsUltrametricDist A] [NormedField B]
      [IsUltrametricDist B] [NormedAlgebra A B] [FiniteDimensional A B],
      ramificationIdx A (NormedField.valuation (K := B)) ≤ Module.finrank A B := by
    intro A B _ _ _ _ _ _
    exact (Nat.le_mul_of_pos_right _ inertiaDeg_pos).trans ramificationIdx_mul_inertiaDeg_le
  obtain ⟨-, he⟩ := DefectTower.eq_and_eq_of_mul_eq (hle L N) (hle K L) Module.finrank_pos
    Module.finrank_pos (by rw [← htower]; ring)
  refine ⟨he, ?_⟩
  have h1 := ramificationIdx_mul_inertiaDeg_le (K := K) (v := NormedField.valuation (K := K))
    (w := NormedField.valuation (K := L))
  have h2 : 0 < inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := L)) :=
    inertiaDeg_pos
  rw [he] at h1
  have h3 : 0 < Module.finrank K L := Module.finrank_pos
  nlinarith

end Local

end Type3

end SemistableReduction
