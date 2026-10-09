/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeTwo

/-!
# Lattice reduction for several Gauss points

Blueprint §9.9, S7.4. Let `F / C` be a function field of one variable and `S` a finite set of
type-2 valuations of `F`, with the norm `‖f‖_S = max_{W ∈ S} W(f)` (`mnorm`).

* `TypeTwo.red`: the reduction `F → κ(W)` (residue on `{W ≤ 1}`, `0` elsewhere), additive and
  `O_C`-linear on `{W ≤ 1}`;
* `exists_orthonormal_of_isometry`: a finite-dimensional `V ⊆ F` with a linear isometry into
  `(C^J, sup)` has an orthonormal basis;
* `exists_isometry_coord`: for a coordinate `x` (transcendental over `C`) all of whose Gauss
  extensions lie in `S`, every finite-dimensional `V ⊆ F` embeds isometrically into some
  `(C^n, sup)` for `max` over these extensions (G6.3–G6.4 in the coordinate `x`);
* **S7.4** `finrank_le_of_red_mem`: if `S` is the set of all extensions of the Gauss points of
  finitely many coordinates `xᵢ`, then for every finite-dimensional `V ⊆ F` and every
  finite-dimensional `k`-subspace `W ⊆ Π_{W ∈ S} κ(W)` containing the reductions of
  `{f ∈ V | ‖f‖_S ≤ 1}`, `dim_C V ≤ dim_k W`.
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra C F]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

namespace TypeTwo

/-- The reduction of `f` at a type-2 valuation `W` (`0` if `W(f) > 1`). -/
noncomputable def red (W : TypeTwo C F) (f : F) : ResidueField W.val.valuationSubring :=
  if h : W.val f ≤ 1 then residue W.val.valuationSubring ⟨f, h⟩ else 0

section Red

variable {W : TypeTwo C F} {f g : F}

lemma red_of_le (h : W.val f ≤ 1) : W.red f = residue W.val.valuationSubring ⟨f, h⟩ := dif_pos h

lemma red_add (hf : W.val f ≤ 1) (hg : W.val g ≤ 1) : W.red (f + g) = W.red f + W.red g := by
  have hfg : W.val (f + g) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le hf hg)
  rw [red_of_le hf, red_of_le hg, red_of_le hfg, ← map_add]
  rfl

lemma red_mul (hf : W.val f ≤ 1) (hg : W.val g ≤ 1) : W.red (f * g) = W.red f * W.red g := by
  have hfg : W.val (f * g) ≤ 1 := by rw [map_mul]; exact mul_le_one' hf hg
  rw [red_of_le hf, red_of_le hg, red_of_le hfg, ← map_mul]
  rfl

@[simp]
lemma red_zero : W.red (0 : F) = 0 := by
  rw [red_of_le (by simp)]
  exact map_zero _

lemma red_sum {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, W.val (f i) ≤ 1) :
    W.red (∑ i ∈ s, f i) = ∑ i ∈ s, W.red (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, red_add (hf a (Finset.mem_insert_self a s))
      ((Valuation.map_sum_le _ fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

lemma red_eq_zero_iff (hf : W.val f ≤ 1) : W.red f = 0 ↔ W.val f < 1 := by
  rw [red_of_le hf, ← not_iff_not, ← ne_eq, residue_ne_zero_iff_valuation_eq_one]
  exact ⟨fun h ↦ by simp [h], fun h ↦ le_antisymm hf (not_lt.1 h)⟩

lemma red_smul (c : C) (hc : ‖c‖₊ ≤ 1) (hf : W.val f ≤ 1) :
    W.red (c • f) = residue (HenselComplete.integers C) ⟨c, by simpa using hc⟩ • W.red f := by
  have hc' : W.val (algebraMap C F c) ≤ 1 := by rwa [valuation_algebraMap]
  rw [Algebra.smul_def, red_mul hc' hf, Algebra.smul_def, red_of_le hc']
  rfl

end Red

end TypeTwo

/-- The max norm `‖f‖_S = max_{W ∈ S} W(f)` over a finite set of type-2 valuations. -/
noncomputable def mnorm (S : Finset (TypeTwo C F)) (f : F) : ℝ≥0 := S.sup fun W ↦ W.val f

lemma le_mnorm {S : Finset (TypeTwo C F)} {W : TypeTwo C F} (hW : W ∈ S) (f : F) :
    W.val f ≤ mnorm S f :=
  Finset.le_sup (f := fun W : TypeTwo C F ↦ W.val f) hW

lemma mnorm_le_iff {S : Finset (TypeTwo C F)} {f : F} {r : ℝ≥0} :
    mnorm S f ≤ r ↔ ∀ W ∈ S, W.val f ≤ r :=
  Finset.sup_le_iff

section Orthonormal

omit [IsUltrametricDist C] in
lemma supNorm_comp_equiv {J J' : Type*} [Fintype J] [Fintype J'] (e : J ≃ J') (v : J' → C) :
    supNorm (v ∘ e) = supNorm v := by
  refine le_antisymm (supNorm_le_iff.2 fun j ↦ le_supNorm v (e j))
    (supNorm_le_iff.2 fun j ↦ ?_)
  have := le_supNorm (v ∘ e) (e.symm j)
  simpa using this

/-- **Orthonormal bases from an isometry** into `(C^J, sup)`. -/
theorem exists_orthonormal_of_isometry (ν : F → ℝ≥0) (V : Submodule C F)
    [FiniteDimensional C V] {J : Type*} [Fintype J] (T : V →ₗ[C] (J → C))
    (hT : ∀ f : V, supNorm (T f) = ν f) (hν : ∀ f : F, ν f = 0 → f = 0) :
    ∃ g : Fin (Module.finrank C V) → F, (∀ l, g l ∈ V) ∧
      ∀ c : Fin (Module.finrank C V) → C, ν (∑ l, c l • g l) = Finset.univ.sup fun l ↦ ‖c l‖₊ := by
  classical
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    have h := hT f
    rw [LinearMap.mem_ker.1 hf, show supNorm (0 : J → C) = 0 from supNorm_eq_zero.2 rfl] at h
    exact (Submodule.mem_bot C).2 (Subtype.ext (hν _ h.symm))
  obtain ⟨u, huU, hu⟩ := exists_orthonormal_pi (Module.finrank C V) (LinearMap.range T)
    (LinearMap.finrank_range_of_inj hinj)
  choose a ha using fun l ↦ LinearMap.mem_range.1 (huU l)
  refine ⟨fun l ↦ (a l : F), fun l ↦ (a l).2, fun c ↦ ?_⟩
  have h1 : ∑ l, c l • (a l : F) = ((∑ l, c l • a l : V) : F) := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [h1, ← hT, map_sum]
  simp only [map_smul, ha]
  exact hu c

end Orthonormal

section Coordinate

variable [IsAlgClosed C] [CharZero C] [IsCurveFunctionField C F]
  {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

/-- `W` lies over the Gauss point `w_{0,1}` of the coordinate `x`. -/
def IsOver {x : F} (hx : Transcendental C x) (W : TypeTwo C F) : Prop :=
  W.val.comap (coordAlgHom hx).toRingHom = gauss1 C

include hp hp1 in
/-- The Gauss point of a coordinate has an extension. -/
lemma exists_isOver {x : F} (hx : Transcendental C x) : ∃ W : TypeTwo C F, IsOver hx W := by
  letI : Algebra (RatFunc C) F := (coordAlgHom hx).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom hx).commutes c).symm
  have hxF : xF C F = x := xF_coord hx
  haveI := finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ hx)
  haveI : Finite (Ext C F) := finite_ext (F := F) hp hp1
  letI : Fintype (Ext C F) := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_orthonormal_basis ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := F) hp hp1)
  obtain ⟨v⟩ := nonempty_ext_of_orthonormal hb
  exact ⟨⟨v.1, by
    ext c
    rw [comap_apply, valuation_algebraMap_C', NormedField.valuation_apply], by
    letI := hasExtension_C (F := F) v
    exact Algebra.transcendental_def.2 ⟨_, transcendental_red_x v⟩⟩, v.2⟩

open Classical in
include hp hp1 in
/-- **Isometric coordinates for one Gauss point** (G6.3–G6.4 in the coordinate `x`): if `S`
contains all extensions of the Gauss point of `x`, every finite-dimensional `V ⊆ F` embeds into
some `(C^n, sup)` isometrically for the max over these extensions. -/
theorem exists_isometry_coord {x : F} (hx : Transcendental C x) (S : Finset (TypeTwo C F))
    (hS : ∀ W, IsOver hx W → W ∈ S) (V : Submodule C F) [FiniteDimensional C V] :
    ∃ (n : ℕ) (T : V →ₗ[C] (Fin n → C)), ∀ f : V,
      supNorm (T f) = (S.filter (IsOver hx)).sup fun W ↦ W.val f := by
  classical
  letI : Algebra (RatFunc C) F := (coordAlgHom hx).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom hx).commutes c).symm
  have hxF : xF C F = x := xF_coord hx
  haveI := finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ hx)
  haveI : Finite (Ext C F) := finite_ext (F := F) hp hp1
  letI : Fintype (Ext C F) := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_orthonormal_basis ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := F) hp hp1)
  obtain ⟨M, T, γ, hγ, hT⟩ := exists_isometry b hb V
  -- the extensions of `w_{0,1}` are the type-2 valuations over `x`
  let htt : Ext C F → TypeTwo C F := fun v ↦ ⟨v.1, by
      ext c
      rw [comap_apply, valuation_algebraMap_C', NormedField.valuation_apply], by
      letI := hasExtension_C (F := F) v
      exact Algebra.transcendental_def.2 ⟨_, transcendental_red_x v⟩⟩
  have hgn (f : F) : gnorm C f = (S.filter (IsOver hx)).sup fun W ↦ W.val f := by
    refine le_antisymm (Finset.sup_le fun v _ ↦ ?_) (Finset.sup_le fun W hW ↦ ?_)
    · have hW : IsOver hx (htt v) := v.2
      exact Finset.le_sup (f := fun W : TypeTwo C F ↦ W.val f)
        (Finset.mem_filter.2 ⟨hS _ hW, hW⟩)
    · exact le_gnorm ⟨W.val, (Finset.mem_filter.1 hW).2⟩ f
  set e := Fintype.equivFin (OIndex C F × Fin (M + 1))
  refine ⟨Fintype.card (OIndex C F × Fin (M + 1)),
    (LinearMap.funLeft C C e.symm).comp (γ⁻¹ • T), fun f ↦ ?_⟩
  have h1 : supNorm (((LinearMap.funLeft C C e.symm).comp (γ⁻¹ • T)) f) =
      supNorm ((γ⁻¹ • T) f) := supNorm_comp_equiv e.symm ((γ⁻¹ • T) f)
  rw [h1, LinearMap.smul_apply, supNorm_smul, hT, ← mul_assoc, nnnorm_inv,
    inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hγ), one_mul, hgn]

open Classical in
include hp hp1 in
/-- **Isometric coordinates for several Gauss points**: if `S` is the set of all extensions of
the Gauss points of finitely many coordinates `xᵢ`, every finite-dimensional `V ⊆ F` embeds
isometrically into `(C^J, sup)` for `‖·‖_S`. -/
theorem exists_isometry_mnorm {I : Type*} [Finite I] (x : I → F)
    (hx : ∀ i, Transcendental C (x i)) (S : Finset (TypeTwo C F))
    (hS : ∀ W, W ∈ S ↔ ∃ i, IsOver (hx i) W) (V : Submodule C F) [FiniteDimensional C V] :
    ∃ (n : ℕ) (T : V →ₗ[C] (Fin n → C)), ∀ f : V,
      supNorm (T f) = mnorm S f := by
  classical
  haveI := Fintype.ofFinite I
  choose n T hT using fun i ↦ exists_isometry_coord hp hp1 (hx i) S
    (fun W hW ↦ (hS W).2 ⟨i, hW⟩) V
  set T₀ : V →ₗ[C] ((Σ i, Fin (n i)) → C) := LinearMap.pi fun j ↦
    (LinearMap.proj j.2).comp (T j.1)
  set e := Fintype.equivFin (Σ i, Fin (n i))
  refine ⟨Fintype.card (Σ i, Fin (n i)), (LinearMap.funLeft C C e.symm).comp T₀, fun f ↦ ?_⟩
  have h0 : supNorm (((LinearMap.funLeft C C e.symm).comp T₀) f) = supNorm (T₀ f) :=
    supNorm_comp_equiv e.symm (T₀ f)
  have h1 : supNorm (T₀ f) = Finset.univ.sup fun i ↦ supNorm (T i f) := by
    simp only [T₀, LatticeReduction.supNorm, LinearMap.pi_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_proj, Function.eval]
    rw [← Finset.univ_sigma_univ, Finset.sup_sigma]
  rw [h0, h1]
  simp only [hT]
  refine le_antisymm (Finset.sup_le fun i _ ↦ Finset.sup_le fun W hW ↦
    le_mnorm (Finset.mem_filter.1 hW).1 _) (Finset.sup_le fun W hW ↦ ?_)
  obtain ⟨i, hi⟩ := (hS W).1 hW
  exact le_trans (Finset.le_sup (f := fun W : TypeTwo C F ↦ W.val f)
    (Finset.mem_filter.2 ⟨hW, hi⟩))
    (Finset.le_sup (f := fun i ↦ (S.filter (IsOver (hx i))).sup fun W ↦ W.val (f : F))
      (Finset.mem_univ i))

include hp hp1 in
/-- **S7.4** (reduction dimension for several Gauss points): if `S` is the set of all extensions
of the Gauss points of finitely many coordinates, then for every finite-dimensional `V ⊆ F` and
every finite-dimensional `k`-subspace `W ⊆ Π_{W ∈ S} κ(W)` containing the reductions of the
elements of `V` with `‖f‖_S ≤ 1`, `dim V ≤ dim W`. -/
theorem finrank_le_of_red_mem {I : Type*} [Finite I] [Nonempty I] (x : I → F)
    (hx : ∀ i, Transcendental C (x i)) (S : Finset (TypeTwo C F))
    (hS : ∀ W, W ∈ S ↔ ∃ i, IsOver (hx i) W) (V : Submodule C F) [FiniteDimensional C V]
    (Wk : Submodule 𝓀 (Π W : S, ResidueField W.1.val.valuationSubring)) [FiniteDimensional 𝓀 Wk]
    (hVW : ∀ f ∈ V, mnorm S f ≤ 1 → (fun W : S ↦ W.1.red f) ∈ Wk) :
    Module.finrank C V ≤ Module.finrank 𝓀 Wk := by
  classical
  obtain ⟨n, T, hT⟩ := exists_isometry_mnorm hp hp1 x hx S hS V
  have hSne : S.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨W, hW⟩ := exists_isOver hp hp1 (hx i)
    exact ⟨W, (hS W).2 ⟨i, hW⟩⟩
  have hν (f : F) (h : mnorm S f = 0) : f = 0 := by
    obtain ⟨W, hW⟩ := hSne
    have := le_mnorm hW f
    rw [h, nonpos_iff_eq_zero, Valuation.zero_iff] at this
    exact this
  obtain ⟨g, hgV, hg⟩ := exists_orthonormal_of_isometry (mnorm S) V T hT hν
  have hg1 (l : Fin (Module.finrank C V)) : mnorm S (g l) = 1 := by
    have := hg (Pi.single l 1)
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    rw [this]
    refine le_antisymm (Finset.sup_le fun l' _ ↦ ?_) ?_
    · split_ifs <;> simp
    · simpa using Finset.le_sup (f := fun l' ↦ ‖(if l' = l then (1 : C) else 0)‖₊)
        (Finset.mem_univ l)
  set v : Fin (Module.finrank C V) → Wk := fun l ↦
    ⟨fun W ↦ W.1.red (g l), hVW _ (hgV l) (hg1 l).le⟩
  have hli : LinearIndependent 𝓀 v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc l
    choose d hd using fun l ↦ residue_surjective (c l)
    have hd1 (l : Fin (Module.finrank C V)) : ‖(d l : C)‖₊ ≤ 1 := by
      have := (HenselComplete.mem_integers_iff _).1 (d l).2
      exact_mod_cast this
    set s := ∑ l, (d l : C) • g l
    have hs : ∀ W ∈ S, W.val s < 1 := by
      intro W hW
      have hw (l : Fin (Module.finrank C V)) : W.val ((d l : C) • g l) ≤ 1 := by
        rw [Algebra.smul_def, map_mul, TypeTwo.valuation_algebraMap]
        exact mul_le_one' (hd1 l) ((le_mnorm hW _).trans (hg1 l).le)
      have hs1 : W.val s ≤ 1 := Valuation.map_sum_le _ fun l _ ↦ hw l
      refine (TypeTwo.red_eq_zero_iff hs1).1 ?_
      rw [TypeTwo.red_sum _ _ fun l _ ↦ hw l]
      have := congrArg (fun y : Wk ↦
        (y : Π W : S, ResidueField W.1.val.valuationSubring) ⟨W, hW⟩) hc
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        v, ZeroMemClass.coe_zero, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [TypeTwo.red_smul _ (hd1 l) ((le_mnorm hW _).trans (hg1 l).le), ← hd l]
    have hsn : mnorm S s < 1 := by
      obtain ⟨W, hW, hWs⟩ := Finset.exists_mem_eq_sup S hSne fun W ↦ W.val s
      rw [mnorm, hWs]
      exact hs W hW
    rw [hg fun l ↦ (d l : C)] at hsn
    have hlt : ‖(d l : C)‖₊ < 1 :=
      (Finset.le_sup (f := fun l ↦ ‖(d l : C)‖₊) (Finset.mem_univ l)).trans_lt hsn
    rw [← hd l]
    refine (residue_eq_zero_iff _).2 ?_
    rw [Valuation.mem_maximalIdeal_iff]
    simpa using hlt
  exact hli.fintype_card_le_finrank.trans_eq' (by simp)

end Coordinate

end SemistableReduction
