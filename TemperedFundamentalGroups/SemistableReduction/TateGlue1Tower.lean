/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue1
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueInput

/-!
# The tower of Tate coverings over the chart `V₁` (Blueprint §12.8, M2.3 (f))

For a special-fibre covering `Sp : TateGlue1.Special1` (étale outside the nodes on `V₁`):

* **`TateGlue1.input : NodeEtaleGlue.Input`**: the node patches `QuadNodeTower.G n` on `D(D)`, the
  étale lifts `E1 n` on `D(w)` with their successor maps (`sE`, `hsE`, `hσE`), the cover
  `1 = D − b₄ w · w` (`span_DT_w1`) and the kernels `ϖⁿ⁺¹` (`hkR`, `hkE`), over the chart `T1`.

So `(input ..).Y n` is the covering of the level `n` over `V₁ = Spec T1n n`, the glueing
`G n ×_{E1 n[1/D]} E1 n`, and `(input ..).Ymap n : Y (n+1) → Y n` is surjective with kernel
`ϖⁿ⁺¹ Y (n+1)` (`NodeEtaleGlue.Input.surjective_Ymap`, `NodeEtaleGlue.Input.ker_Ymap`).

Implementation note: statements about the concrete coverings should be derived from the generic
statements about an `Input` (as above), not re-elaborated at the Tate types: instance problems on
the concrete patched algebras `G n` and glueings unfold the level structures and are very slow.
-/

universe u

namespace SemistableReduction

namespace TateGlue1

open TateTwoChart TateTwoChartNode TateLevel KummerEtale AdmissibleLift

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
  {hπe : θ (ϖ ^ m) = 0} {τ : Rb b₄ b₆ ϖ m ε}
  {cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (hϖ : θ ϖ = 0) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (Sp : Special1 hκ hπ hπe τ cov₀) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (hm : m ≠ 0)

/-! ### The data of `NodeEtaleGlueTower` for the Tate charts -/

omit [IsNoetherianRing O] in
lemma towerT1 (n : ℕ) :
    IsScalarTower (T1 π b₄ t κ) (B ϖ π b₄ t κ (n + 1)) (B ϖ π b₄ t κ n) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

omit [IsNoetherianRing O] in
lemma hBR (n : ℕ) (x : B ϖ π b₄ t κ (n + 1)) :
    (letI := instBR ϖ b₄ hκ hπ;
      algebraMap (R b₄ b₆ ϖ m ε (n + 1)) (R b₄ b₆ ϖ m ε n)
        (algebraMap (B ϖ π b₄ t κ (n + 1)) (R b₄ b₆ ϖ m ε (n + 1)) x)) =
      (letI := instBR ϖ b₄ hκ hπ;
        algebraMap (B ϖ π b₄ t κ n) (R b₄ b₆ ϖ m ε n)
          (algebraMap (B ϖ π b₄ t κ (n + 1)) (B ϖ π b₄ t κ n) x)) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change algebraMap (R b₄ b₆ ϖ m ε (n + 1)) (R b₄ b₆ ϖ m ε n)
    (toRn b₄ hκ hπ (n + 1) (Ideal.Quotient.mk _ y)) = toRn b₄ hκ hπ n (Ideal.Quotient.mk _ y)
  rw [toRn_mk, toRn_mk]
  rfl

/-- The successor maps of the étale lifts `E1`. -/
def sE (n : ℕ) : (E1 hκ hπ hϖ hker Sp (n + 1)).E →+* (E1 hκ hπ hϖ hker Sp n).E :=
  letI := EtaleTower.algE (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) (E1 hκ hπ hϖ hker Sp n)
  (EtaleTower.succ (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) hker (E1 hκ hπ hϖ hker Sp (n + 1))
    (E1 hκ hπ hϖ hker Sp n) : (E1 hκ hπ hϖ hker Sp (n + 1)).E →+* _)

lemma hsE (n : ℕ) (x : B ϖ π b₄ t κ (n + 1)) :
    sE hκ hπ hϖ hker Sp n (algebraMap _ (E1 hκ hπ hϖ hker Sp (n + 1)).E x) =
      algebraMap (B ϖ π b₄ t κ n) _ (algebraMap (B ϖ π b₄ t κ (n + 1)) (B ϖ π b₄ t κ n) x) :=
  letI := EtaleTower.algE (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) (E1 hκ hπ hϖ hker Sp n)
  (EtaleTower.succ (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) hker (E1 hκ hπ hϖ hker Sp (n + 1))
    (E1 hκ hπ hϖ hker Sp n)).commutes x

lemma hσE (n : ℕ) (x : (E1 hκ hπ hϖ hker Sp (n + 1)).E) :
    (letI := EtaleTower.algC (T1 π b₄ t κ) hϖ Sp.C1 n;
      (E1 hκ hπ hϖ hker Sp n).σ (Ideal.Quotient.mk _ (sE hκ hπ hϖ hker Sp n x))) =
      (letI := EtaleTower.algC (T1 π b₄ t κ) hϖ Sp.C1 (n + 1);
        (E1 hκ hπ hϖ hker Sp (n + 1)).σ (Ideal.Quotient.mk _ x)) :=
  EtaleTower.σ_succ (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) hker _ _ x

omit [IsNoetherianRing O] in
/-- `1 = D − b₄ w · w`: the opens `D(D)`, `D(w)` cover `Spec T1`. -/
lemma span_DT_w1 : Ideal.span {DT π b₄ t κ, w1 π b₄ t κ} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : (1 : T1 π b₄ t κ) = DT π b₄ t κ - (algebraMap O _ b₄ * w1 π b₄ t κ) * w1 π b₄ t κ := by
    rw [DT]; ring
  rw [h]
  exact Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert _ _))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))

/-- The ideal `ϖⁿ⁺¹ T1` of the base chart. -/
abbrev K1 (ϖ π b₄ t κ : O) (n : ℕ) : Ideal (T1 π b₄ t κ) := (Iv ϖ n).map (algebraMap O _)

lemma hkE (n : ℕ) : RingHom.ker (sE hκ hπ hϖ hker Sp n) =
    (K1 ϖ π b₄ t κ n).map ((algebraMap (B ϖ π b₄ t κ (n + 1)) (E1 hκ hπ hϖ hker Sp (n + 1)).E).comp
      (algebraMap (T1 π b₄ t κ) (B ϖ π b₄ t κ (n + 1)))) := by
  exact EtaleTower.ker_succ_base (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) hker _ _

omit [IsNoetherianRing O] in
/-- The kernels of the transition maps of the node charts: `ϖⁿ⁺¹ T1 · Rn (n+1)`. -/
lemma hkR (n : ℕ) : letI := instBR ϖ b₄ hκ hπ
    RingHom.ker (algebraMap (R b₄ b₆ ϖ m ε (n + 1)) (R b₄ b₆ ϖ m ε n)) =
      (K1 ϖ π b₄ t κ n).map ((algebraMap (B ϖ π b₄ t κ (n + 1)) (R b₄ b₆ ϖ m ε (n + 1))).comp
        (algebraMap (T1 π b₄ t κ) (B ϖ π b₄ t κ (n + 1)))) := by
  letI := instBR ϖ b₄ hκ hπ
  rw [QuadNodeTower.ker_succ, Ideal.map_map]
  congr 1
  ext o
  change _ = toRn b₄ hκ hπ (n + 1) (algebraMap O (T1n ϖ π b₄ t κ (n + 1)) o)
  rw [toRn_algebraMap]

/-- **The Tate covering over `V₁` as an input of the glueing** (`NodeEtaleGlue.Input`). -/
def input : NodeEtaleGlue.Input θ cov₀ π' where
  R := R b₄ b₆ ϖ m ε
  T := tower hπe τ cov₀ hϖ π' hπ' hker
  B := B ϖ π b₄ t κ
  algBR := instBR ϖ b₄ hκ hπ
  towerOBR := towerOBR (ϖ := ϖ) (b₄ := b₄) hκ hπ
  B0 := T1 π b₄ t κ
  towerB0 := towerT1
  a0 := DT π b₄ t κ
  b0 := w1 π b₄ t κ
  hab := span_DT_w1
  away := isLocalization_BR (ϖ := ϖ) (b₄ := b₄) hκ hπ hε
  Bs := T1s θ π b₄ t κ
  qB := qB hϖ
  φs := toNodeJ hκ hπ
  hφs := hφs hκ hπ hπe τ cov₀ hϖ π' hπ' hker
  C1 := Sp.C1
  ι₀ := Sp.ι₀
  hι₀ := Sp.hι₀
  abar := Ideal.Quotient.mk _ (DT π b₄ t κ)
  bbar := Ideal.Quotient.mk _ (w1 π b₄ t κ)
  ha := fun _ ↦ rfl
  hι := Sp.hι
  hbb := fun _ ↦ rfl
  E := fun n ↦ (E1 hκ hπ hϖ hker Sp n).E
  σE := fun n ↦ (E1 hκ hπ hϖ hker Sp n).σ
  hbE := fun n ↦ (E1 hκ hπ hϖ hker Sp n).hb
  kdiv := fun n ↦ 2 * (n + 1)
  hdiv := fun n ↦ TateOverlap.fn_dvd_w hκ hπ hm n
  mB := fun n ↦ n + 1
  hJB := fun n ↦ EtaleTower.hJ hker n
  hBR := hBR hκ hπ
  sE := sE hκ hπ hϖ hker Sp
  hsE := hsE hκ hπ hϖ hker Sp
  hσE := hσE hκ hπ hϖ hker Sp
  hsEs := fun n ↦ by
    letI := EtaleTower.algE (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) (E1 hκ hπ hϖ hker Sp n)
    exact EtaleTower.surjective_succ (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) hker _ _
  K := K1 ϖ π b₄ t κ
  hkR := hkR hκ hπ
  hkE := hkE hκ hπ hϖ hker Sp

end

end TateGlue1

end SemistableReduction
