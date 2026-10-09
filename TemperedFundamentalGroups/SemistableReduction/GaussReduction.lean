/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LatticeReduction

/-!
# Reduction to the residue curves over the Gauss point

Blueprint §9.5, G6.4. Let `F / C(X)` be finite and `C → F` compatible. For an extension `w` of the
Gauss valuation (`GaussFibre.Ext C F`), `red f w ∈ κ(w)` is the residue of `f` (if `w(f) ≤ 1`).

* `red_add`, `red_mul`, `red_sum`, `red_smul`, `red_algebraMap_mul`, `red_eq_zero_iff`: the
  reduction is a ring homomorphism on `{w ≤ 1}`, compatible with the residue fields `k` of `C`
  and `κ(w_{0,1})` of `C(X)`;
* **G6.4** `finrank_le_of_red_mem`: if `F` has an orthonormal `C(X)`-basis (G6.3), then for every
  finite-dimensional `C`-subspace `V ⊆ F` and every finite-dimensional `k`-subspace
  `W ⊆ Π_w κ(w)` containing the reductions of `{f ∈ V | gnorm f ≤ 1}`, `dim_C V ≤ dim_k W`
  (the reductions of an orthonormal basis of `V` are `k`-independent).
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

lemma valuation_algebraMap_C' (w : Ext C F) (c : C) : w.1 (algebraMap C F c) = ‖c‖₊ := by
  rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, valuation_algebraMap_C]

instance hasExtension_C (w : Ext C F) : (NormedField.valuation (K := C)).HasExtension w.1 :=
  hasExtension_of_comap_eq (by
    ext c
    rw [comap_apply, valuation_algebraMap_C', NormedField.valuation_apply])

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
variable (C) in
/-- The reduction of `f` at an extension `w` of the Gauss valuation (`0` if `w(f) > 1`). -/
noncomputable def red (f : F) (w : Ext C F) : ResidueField w.1.valuationSubring :=
  if h : w.1 f ≤ 1 then residue w.1.valuationSubring ⟨f, h⟩ else 0

section Red

omit [Algebra C F] [IsScalarTower C (RatFunc C) F]

variable {w : Ext C F} {f g : F}

lemma red_of_le (h : w.1 f ≤ 1) : red C f w = residue w.1.valuationSubring ⟨f, h⟩ := dif_pos h

lemma red_add (hf : w.1 f ≤ 1) (hg : w.1 g ≤ 1) : red C (f + g) w = red C f w + red C g w := by
  have hfg : w.1 (f + g) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le hf hg)
  rw [red_of_le hf, red_of_le hg, red_of_le hfg, ← map_add]
  rfl

lemma red_mul (hf : w.1 f ≤ 1) (hg : w.1 g ≤ 1) : red C (f * g) w = red C f w * red C g w := by
  have hfg : w.1 (f * g) ≤ 1 := by rw [map_mul]; exact mul_le_one' hf hg
  rw [red_of_le hf, red_of_le hg, red_of_le hfg, ← map_mul]
  rfl

lemma red_neg (hf : w.1 f ≤ 1) : red C (-f) w = -red C f w := by
  have hf' : w.1 (-f) ≤ 1 := by rwa [Valuation.map_neg]
  rw [red_of_le hf, red_of_le hf', ← _root_.map_neg]
  rfl

lemma red_sub (hf : w.1 f ≤ 1) (hg : w.1 g ≤ 1) : red C (f - g) w = red C f w - red C g w := by
  have hg' : w.1 (-g) ≤ 1 := by rwa [Valuation.map_neg]
  rw [sub_eq_add_neg, red_add hf hg', red_neg hg, sub_eq_add_neg]

@[simp]
lemma red_zero : red C (0 : F) w = 0 := by
  rw [red_of_le (by simp)]
  exact map_zero _

@[simp]
lemma red_one : red C (1 : F) w = 1 := by
  rw [red_of_le (by simp)]
  exact map_one _

lemma red_sum {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, w.1 (f i) ≤ 1) :
    red C (∑ i ∈ s, f i) w = ∑ i ∈ s, red C (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, red_add (hf a (Finset.mem_insert_self a s))
      ((Valuation.map_sum_le _ fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

lemma red_eq_zero_iff (hf : w.1 f ≤ 1) : red C f w = 0 ↔ w.1 f < 1 := by
  rw [red_of_le hf, ← not_iff_not, ← ne_eq, residue_ne_zero_iff_valuation_eq_one]
  exact ⟨fun h ↦ by simp [h], fun h ↦ le_antisymm hf (not_lt.1 h)⟩

lemma red_algebraMap_mul (φ : RatFunc C) (hφ : gauss1 C φ ≤ 1) (hf : w.1 f ≤ 1) :
    red C (algebraMap (RatFunc C) F φ * f) w =
      algebraMap (ResidueField (gauss1 C).valuationSubring) (ResidueField w.1.valuationSubring)
        (residue _ ⟨φ, hφ⟩) * red C f w := by
  have hφ' : w.1 (algebraMap (RatFunc C) F φ) ≤ 1 := by rwa [valuation_algebraMap]
  rw [red_mul hφ' hf, red_of_le hφ']
  rfl

end Red

lemma red_smul {w : Ext C F} {f : F} (c : C) (hc : ‖c‖₊ ≤ 1) (hf : w.1 f ≤ 1) :
    red C (c • f) w = residue (HenselComplete.integers C) ⟨c, by simpa using hc⟩ • red C f w := by
  have hc' : w.1 (algebraMap C F c) ≤ 1 := by rwa [valuation_algebraMap_C']
  rw [Algebra.smul_def, red_mul hc' hf, Algebra.smul_def, red_of_le hc']
  rfl

/-- **G6.4** (reduction dimension). If `F` has an orthonormal `C(X)`-basis, then for every
finite-dimensional `C`-subspace `V ⊆ F` and every finite-dimensional `k`-subspace `W` of
`Π_w κ(w)` containing the reductions of the elements of `V` of norm `≤ 1`, `dim V ≤ dim W`. -/
theorem finrank_le_of_red_mem [Fintype (Ext C F)] [Nonempty (Ext C F)] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (RatFunc C) F)
    (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
    (V : Submodule C F) [FiniteDimensional C V]
    (W : Submodule 𝓀 (Π w : Ext C F, ResidueField w.1.valuationSubring)) [FiniteDimensional 𝓀 W]
    (hVW : ∀ f ∈ V, gnorm C f ≤ 1 → (fun w ↦ red C f w) ∈ W) :
    Module.finrank C V ≤ Module.finrank 𝓀 W := by
  classical
  obtain ⟨g, hgV, hg⟩ := exists_orthonormal_submodule b hb V
  have hg1 (l : Fin (Module.finrank C V)) : gnorm C (g l) = 1 := by
    have := hg (Pi.single l 1)
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    rw [this]
    refine le_antisymm (Finset.sup_le fun l' _ ↦ ?_) ?_
    · split_ifs <;> simp
    · simpa using Finset.le_sup (f := fun l' ↦ ‖(if l' = l then (1 : C) else 0)‖₊)
        (Finset.mem_univ l)
  set v : Fin (Module.finrank C V) → W := fun l ↦ ⟨fun w ↦ red C (g l) w, hVW _ (hgV l) (hg1 l).le⟩
  have hli : LinearIndependent 𝓀 v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc l
    choose d hd using fun l ↦ residue_surjective (c l)
    have hd1 (l : Fin (Module.finrank C V)) : ‖(d l : C)‖₊ ≤ 1 := by
      have := (HenselComplete.mem_integers_iff _).1 (d l).2
      exact_mod_cast this
    set s := ∑ l, (d l : C) • g l
    have hs : ∀ w : Ext C F, w.1 s < 1 := by
      intro w
      have hw (l : Fin (Module.finrank C V)) : w.1 ((d l : C) • g l) ≤ 1 := by
        rw [Algebra.smul_def, map_mul, valuation_algebraMap_C']
        exact mul_le_one' (hd1 l) ((le_gnorm w _).trans (hg1 l).le)
      have hs1 : w.1 s ≤ 1 := Valuation.map_sum_le _ fun l _ ↦ hw l
      refine (red_eq_zero_iff hs1).1 ?_
      rw [red_sum _ _ fun l _ ↦ hw l]
      have := congrArg (fun x : W ↦
        (x : Π w : Ext C F, ResidueField w.1.valuationSubring) w) hc
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        v, ZeroMemClass.coe_zero, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [red_smul _ (hd1 l) ((le_gnorm w _).trans (hg1 l).le), ← hd l]
    have hsn : gnorm C s < 1 := (gnorm_lt_iff one_pos).2 hs
    rw [hg fun l ↦ (d l : C)] at hsn
    have hlt : ‖(d l : C)‖₊ < 1 :=
      (Finset.le_sup (f := fun l ↦ ‖(d l : C)‖₊) (Finset.mem_univ l)).trans_lt hsn
    rw [← hd l]
    refine (residue_eq_zero_iff _).2 ?_
    rw [Valuation.mem_maximalIdeal_iff]
    simpa using hlt
  exact hli.fintype_card_le_finrank.trans_eq' (by simp)

end GaussFibre

end SemistableReduction
