/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Tower
import TemperedFundamentalGroups.SemistableReduction.TwoChartNormMap

/-!
# Maps of glued levels (Blueprint §12.8, M2.3 (f); MR12 I3, generic core layer 4)

The Galois action on the lifts of coverings (Tate curve, `ℙ¹ ∖ {0,1,a}`) acts by maps between the
glued levels of two (different) coverings. For two inputs `I`, `I'` (`NodeEtaleGlue.Input`, with
different special-fibre coverings, hence different bases as terms) and overlaps
`V : Overlap I`, `V' : Overlap I'`, this file builds the maps of the glued levels from maps of the
pieces. All maps are ring maps with explicit compatibilities with the distinguished elements and
the base `O` (in the applications the base maps are identities and the compatibilities are
`AlgHom.commutes`).

* `ZariskiTwo.hmap`: the map of glued algebras `Ba ×_{Bab} Bb → Ba' ×_{Bab'} Bb'` over different
  bases, `fst_hmap`, `snd_hmap`, `hmap_algebraMap`, and `ZariskiTwo.hmapₐ` (over a common `A`);
* (a) **`Input.yMap`**: the map `Y n → Y' n` from maps `g : G n → G' n` of the node patches and
  `e : E n → E' n` of the étale pieces compatible on `E n[1/a]` (`Input.eab`),
  `yMap_algebraMap`, **`Input.yMap_succ`** (compatibility with `Ymap`);
* `TwoChartGlue.twoChartMap`: the morphism of two-chart rings glued from maps of the pieces
  (generic, over abstract rings);
* (b) **`Overlap.twoChartMap`**: from `y : Y n → Y' n` and `p : P0 n → P0' n` compatible on the
  overlaps `M n` (`Overlap.mM`), the morphism of two-chart rings
  `twoChart n → twoChart' n`, with components `y`, `Overlap.mQ` (on `Q n = Y n[1/x₁]`) and the
  glued map on `R0 = Q n ×_{M n} P0 n` (`twoChartMap_f1`, `twoChartMap_f01`, `twoChartMap_fst`,
  `twoChartMap_snd`);
* (c) **`Overlap.succ_comp_twoChartMap`**: for families compatible with the successor maps,
  `succ' n ∘ twoChartMap (n+1) = twoChartMap n ∘ succ n`.
-/

universe u

/-! ### Maps of glued algebras over different bases -/

namespace ZariskiTwo

variable {R : Type u} [CommRing R]
  {Ba Bb Bab : Type u} [CommRing Ba] [CommRing Bb] [CommRing Bab]
  [Algebra R Ba] [Algebra R Bb] [Algebra R Bab]
  {ρa : Ba →ₐ[R] Bab} {ρb : Bb →ₐ[R] Bab}
  {R' : Type u} [CommRing R']
  {Ba' Bb' Bab' : Type u} [CommRing Ba'] [CommRing Bb'] [CommRing Bab']
  [Algebra R' Ba'] [Algebra R' Bb'] [Algebra R' Bab']
  {ρa' : Ba' →ₐ[R'] Bab'} {ρb' : Bb' →ₐ[R'] Bab'}
  (sa : Ba →+* Ba') (sb : Bb →+* Bb') (sab : Bab →+* Bab')
  (hsa : ∀ x, ρa' (sa x) = sab (ρa x)) (hsb : ∀ x, ρb' (sb x) = sab (ρb x))

include hsa hsb in
lemma hmap_mem (p : glued ρa ρb) : (sa p.1.1, sb p.1.2) ∈ glued ρa' ρb' := by
  change ρa' (sa p.1.1) = ρb' (sb p.1.2)
  rw [hsa, hsb]
  exact congrArg sab p.2

/-- **The map of glued algebras over different bases** induced by compatible ring maps of the
pieces. -/
def hmap : glued ρa ρb →+* glued ρa' ρb' where
  toFun p := ⟨(sa p.1.1, sb p.1.2), hmap_mem sa sb sab hsa hsb p⟩
  map_one' := Subtype.ext (Prod.ext (map_one sa) (map_one sb))
  map_mul' p q := Subtype.ext (Prod.ext (map_mul sa p.1.1 q.1.1) (map_mul sb p.1.2 q.1.2))
  map_zero' := Subtype.ext (Prod.ext (map_zero sa) (map_zero sb))
  map_add' p q := Subtype.ext (Prod.ext (map_add sa p.1.1 q.1.1) (map_add sb p.1.2 q.1.2))

@[simp] lemma fst_hmap (p : glued ρa ρb) :
    fst ρa' ρb' (hmap sa sb sab hsa hsb p) = sa (fst ρa ρb p) := rfl

@[simp] lemma snd_hmap (p : glued ρa ρb) :
    snd ρa' ρb' (hmap sa sb sab hsa hsb p) = sb (snd ρa ρb p) := rfl

/-- The map of glued algebras is compatible with a map of the bases compatible with the maps of
the pieces. -/
lemma hmap_algebraMap (β : R →+* R') (ha : ∀ r, sa (algebraMap R Ba r) = algebraMap R' Ba' (β r))
    (hb : ∀ r, sb (algebraMap R Bb r) = algebraMap R' Bb' (β r)) (r : R) :
    hmap sa sb sab hsa hsb (algebraMap R (glued ρa ρb) r) =
      algebraMap R' (glued ρa' ρb') (β r) :=
  Subtype.ext (Prod.ext (ha r) (hb r))

/-- `hmap` as a map of algebras over a common base `A` of `R`, `R'`. -/
def hmapₐ {A : Type u} [CommRing A] [Algebra A R] [Algebra A R'] [Algebra A Ba] [Algebra A Bb]
    [Algebra A Ba'] [Algebra A Bb'] [IsScalarTower A R Ba] [IsScalarTower A R Bb]
    [IsScalarTower A R' Ba'] [IsScalarTower A R' Bb'] (fa : Ba →ₐ[A] Ba') (fb : Bb →ₐ[A] Bb')
    (hfa : ∀ x, ρa' (fa x) = sab (ρa x)) (hfb : ∀ x, ρb' (fb x) = sab (ρb x)) :
    glued ρa ρb →ₐ[A] glued ρa' ρb' :=
  { hmap (fa : Ba →+* Ba') (fb : Bb →+* Bb') sab hfa hfb with
    commutes' := fun r ↦ Subtype.ext (Prod.ext (fa.commutes r) (fb.commutes r)) }

lemma hmapₐ_apply {A : Type u} [CommRing A] [Algebra A R] [Algebra A R'] [Algebra A Ba]
    [Algebra A Bb] [Algebra A Ba'] [Algebra A Bb'] [IsScalarTower A R Ba] [IsScalarTower A R Bb]
    [IsScalarTower A R' Ba'] [IsScalarTower A R' Bb'] (fa : Ba →ₐ[A] Ba') (fb : Bb →ₐ[A] Bb')
    (hfa : ∀ x, ρa' (fa x) = sab (ρa x)) (hfb : ∀ x, ρb' (fb x) = sab (ρb x))
    (p : glued ρa ρb) :
    hmapₐ sab fa fb hfa hfb p = hmap (fa : Ba →+* Ba') (fb : Bb →+* Bb') sab hfa hfb p := rfl

end ZariskiTwo

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {R₀' : Type u} [CommRing R₀'] [Algebra k R₀'] {f₀' : R₀'}
  {φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀'} {ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀'}
  {cov₀' : Admissible.Covering φ₀' ψ₀'} {πL' : cov₀'.ι → O}

/-! ### (a) Maps of the coverings over the first chart -/

namespace Input

variable (I : Input θ cov₀ πL) (I' : Input θ cov₀' πL') (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

/-- **The map of overlaps** `E n[1/a] → E' n[1/a']` induced by `e : E n → E' n` with
`e (a) = a'`. -/
def eab (e : I.E n →+* I'.E n)
    (he : e (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I'.B n) (I'.E n) (I'.a n)) :
    EtaleOverlap.Bab (I.a n) (I.E n) →+* EtaleOverlap.Bab (I'.a n) (I'.E n) :=
  IsLocalization.Away.lift (algebraMap (I.B n) (I.E n) (I.a n))
    (g := (algebraMap (I'.E n) (EtaleOverlap.Bab (I'.a n) (I'.E n))).comp e) (by
      rw [RingHom.comp_apply, he]
      exact IsLocalization.Away.algebraMap_isUnit _)

lemma eab_algebraMap (e : I.E n →+* I'.E n)
    (he : e (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I'.B n) (I'.E n) (I'.a n))
    (x : I.E n) :
    I.eab I' n e he (algebraMap (I.E n) (EtaleOverlap.Bab (I.a n) (I.E n)) x) =
      algebraMap (I'.E n) (EtaleOverlap.Bab (I'.a n) (I'.E n)) (e x) :=
  IsLocalization.Away.lift_eq _ _ x

/-- **The map of the coverings over the first chart** `Y n → Y' n` induced by maps of the node
patches `g` and of the étale pieces `e` compatible on the overlap `E n[1/a]`
(`ZariskiTwo.hmap`). -/
def yMap (g : I.T.G hθ n →+* I'.T.G hθ n) (e : I.E n →+* I'.E n)
    (he : e (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I'.B n) (I'.E n) (I'.a n))
    (hg : ∀ x, ρa0 I'.T hθ I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha I'.hι I'.E I'.σE
      I'.hbE I'.hdiv I'.hJB I'.B0 n (g x) =
      I.eab I' n e he (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
        I.hdiv I.hJB I.B0 n x)) :
    I.Y hθ n →+* I'.Y hθ n :=
  letI := alg0G I.T hθ I.B I.B0 n
  letI := alg0 I.B I.B0 n (I.E n)
  letI := alg0 I.B I.B0 n (EtaleOverlap.Bab (I.a n) (I.E n))
  letI := alg0G I'.T hθ I'.B I'.B0 n
  letI := alg0 I'.B I'.B0 n (I'.E n)
  letI := alg0 I'.B I'.B0 n (EtaleOverlap.Bab (I'.a n) (I'.E n))
  ZariskiTwo.hmap g e (I.eab I' n e he) hg fun x ↦ (I.eab_algebraMap I' n e he x).symm

variable (g : I.T.G hθ n →+* I'.T.G hθ n) (e : I.E n →+* I'.E n)
  (he : e (algebraMap (I.B n) (I.E n) (I.a n)) = algebraMap (I'.B n) (I'.E n) (I'.a n))
  (hg : ∀ x, ρa0 I'.T hθ I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha I'.hι I'.E I'.σE
      I'.hbE I'.hdiv I'.hJB I'.B0 n (g x) =
      I.eab I' n e he (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
        I.hdiv I.hJB I.B0 n x))

/-- The first component of `yMap` is `g`. -/
lemma yMap_fst (z : I.Y hθ n) : (I.yMap I' hθ n g e he hg z).1.1 = g z.1.1 := rfl

/-- The second component of `yMap` is `e`. -/
lemma yMap_snd (z : I.Y hθ n) : (I.yMap I' hθ n g e he hg z).1.2 = e z.1.2 := rfl

/-- `yMap` is compatible with a map `β` of the bases `B0 → B0'` compatible with `g` and `e`. -/
lemma yMap_algebraMap (β : I.B0 →+* I'.B0)
    (hgβ : ∀ b, g (letI := alg0G I.T hθ I.B I.B0 n; algebraMap I.B0 (I.T.G hθ n) b) =
      (letI := alg0G I'.T hθ I'.B I'.B0 n; algebraMap I'.B0 (I'.T.G hθ n) (β b)))
    (heβ : ∀ b, e (letI := alg0 I.B I.B0 n (I.E n); algebraMap I.B0 (I.E n) b) =
      (letI := alg0 I'.B I'.B0 n (I'.E n); algebraMap I'.B0 (I'.E n) (β b))) (b : I.B0) :
    I.yMap I' hθ n g e he hg (algebraMap I.B0 (I.Y hθ n) b) =
      algebraMap I'.B0 (I'.Y hθ n) (β b) :=
  Subtype.ext (Prod.ext (hgβ b) (heβ b))

/-- **The maps of the coverings commute with the successor maps** if the maps of the node patches
and of the étale pieces do. -/
theorem yMap_succ (g : ∀ n, I.T.G hθ n →+* I'.T.G hθ n) (e : ∀ n, I.E n →+* I'.E n)
    (he : ∀ n, e n (algebraMap (I.B n) (I.E n) (I.a n)) =
      algebraMap (I'.B n) (I'.E n) (I'.a n))
    (hg : ∀ n x, ρa0 I'.T hθ I'.B I'.qB I'.φs I'.hφs I'.ι₀ I'.hι₀ I'.a I'.b I'.ha I'.hι I'.E I'.σE
      I'.hbE I'.hdiv I'.hJB I'.B0 n (g n x) =
      I.eab I' n (e n) (he n) (ρa0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E
        I.σE I.hbE I.hdiv I.hJB I.B0 n x))
    (hgS : ∀ n x, I'.T.tr hθ hO n (g (n + 1) x) = g n (I.T.tr hθ hO n x))
    (heS : ∀ n x, I'.sE n (e (n + 1) x) = e n (I.sE n x)) (n : ℕ) (z : I.Y hθ (n + 1)) :
    I'.Ymap hθ hO n (I.yMap I' hθ (n + 1) (g (n + 1)) (e (n + 1)) (he (n + 1)) (hg (n + 1)) z) =
      I.yMap I' hθ n (g n) (e n) (he n) (hg n) (I.Ymap hθ hO n z) :=
  Subtype.ext (Prod.ext (hgS n z.1.1) (heS n z.1.2))

end Input

end NodeEtaleGlue

/-! ### Maps of two-chart rings glued from maps of the pieces (generic) -/

namespace TwoChartGlue

variable {A : Type u} [CommRing A]
  {B0 : Type u} [CommRing B0] [Algebra A B0]
  {Y1 : Type u} [CommRing Y1] [Algebra A Y1]
  {Q : Type u} [CommRing Q] [Algebra A Q] [Algebra B0 Q] [IsScalarTower A B0 Q]
  {P0b P0ab : Type u} [CommRing P0b] [CommRing P0ab] [Algebra B0 P0b] [Algebra B0 P0ab]
  [Algebra A P0b] [Algebra A P0ab] [IsScalarTower A B0 P0b] [IsScalarTower A B0 P0ab]
  {B0' : Type u} [CommRing B0'] [Algebra A B0']
  {Y1' : Type u} [CommRing Y1'] [Algebra A Y1']
  {Q' : Type u} [CommRing Q'] [Algebra A Q'] [Algebra B0' Q'] [IsScalarTower A B0' Q']
  {P0b' P0ab' : Type u} [CommRing P0b'] [CommRing P0ab'] [Algebra B0' P0b'] [Algebra B0' P0ab']
  [Algebra A P0b'] [Algebra A P0ab'] [IsScalarTower A B0' P0b'] [IsScalarTower A B0' P0ab']

omit [Algebra A B0] [IsScalarTower A B0 Q] [Algebra A B0'] [IsScalarTower A B0' Q'] in
/-- A map of the overlaps sending `y` to `y'` sends the inverse `x₀` of `y` to `x₀'`. -/
lemma map_x0 (y : Y1) (ι : Y1 →ₐ[A] Q) (x0 : B0) (hxy : algebraMap B0 Q x0 * ι y = 1)
    (y' : Y1') (ι' : Y1' →ₐ[A] Q') (x0' : B0') (hxy' : algebraMap B0' Q' x0' * ι' y' = 1)
    (fY : Y1 →ₐ[A] Y1') (fQ : Q →ₐ[A] Q') (hfy : fY y = y') (hfι : ∀ a, fQ (ι a) = ι' (fY a)) :
    fQ (algebraMap B0 Q x0) = algebraMap B0' Q' x0' := by
  have h1 : fQ (algebraMap B0 Q x0) * ι' y' = 1 := by
    rw [← hfy, ← hfι, ← map_mul, hxy, map_one]
  calc fQ (algebraMap B0 Q x0) = fQ (algebraMap B0 Q x0) * (algebraMap B0' Q' x0' * ι' y') := by
        rw [hxy', mul_one]
    _ = (fQ (algebraMap B0 Q x0) * ι' y') * algebraMap B0' Q' x0' := by ring
    _ = algebraMap B0' Q' x0' := by rw [h1, one_mul]

/-- **The morphism of two-chart rings glued from maps of the pieces**: `fY` on `Y1`, `fQ` on the
overlap `Q`, and on `R0 = Q ×_{P0ab} P0b` the glued map of `fQ` and `fP` (compatible on `P0ab`
through `fM`). -/
def twoChartMap (y : Y1) (ι : Y1 →ₐ[A] Q)
    (hι : letI := (ι : Y1 →+* Q).toAlgebra; IsLocalization.Away y Q)
    (x0 : B0) (hxy : algebraMap B0 Q x0 * ι y = 1)
    (ρ0a : Q →ₐ[B0] P0ab) (ρ0b : P0b →ₐ[B0] P0ab)
    (hb0 : letI := (ρ0b : P0b →+* P0ab).toAlgebra; IsLocalization.Away (algebraMap B0 P0b x0) P0ab)
    (y' : Y1') (ι' : Y1' →ₐ[A] Q')
    (hι' : letI := (ι' : Y1' →+* Q').toAlgebra; IsLocalization.Away y' Q')
    (x0' : B0') (hxy' : algebraMap B0' Q' x0' * ι' y' = 1)
    (ρ0a' : Q' →ₐ[B0'] P0ab') (ρ0b' : P0b' →ₐ[B0'] P0ab')
    (hb0' : letI := (ρ0b' : P0b' →+* P0ab').toAlgebra;
      IsLocalization.Away (algebraMap B0' P0b' x0') P0ab')
    (fY : Y1 →ₐ[A] Y1') (fQ : Q →ₐ[A] Q') (fP : P0b →ₐ[A] P0b') (fM : P0ab →+* P0ab')
    (hfy : fY y = y') (hfι : ∀ a, fQ (ι a) = ι' (fY a))
    (hfP : fP (algebraMap B0 P0b x0) = algebraMap B0' P0b' x0')
    (hfa : ∀ q, ρ0a' (fQ q) = fM (ρ0a q)) (hfb : ∀ e, ρ0b' (fP e) = fM (ρ0b e)) :
    TwoChartMap (twoChart y ι hι x0 hxy ρ0a ρ0b hb0)
      (twoChart y' ι' hι' x0' hxy' ρ0a' ρ0b' hb0') where
  f0 := ZariskiTwo.hmapₐ fM fQ fP hfa hfb
  f1 := fY
  f01 := fQ
  hx := Subtype.ext (Prod.ext (map_x0 y ι x0 hxy y' ι' x0' hxy' fY fQ hfy hfι) hfP)
  hy := hfy
  hu := map_x0 y ι x0 hxy y' ι' x0' hxy' fY fQ hfy hfι
  h0 _ := rfl
  h1 a := hfι a

end TwoChartGlue

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {R₀' : Type u} [CommRing R₀'] [Algebra k R₀'] {f₀' : R₀'}
  {φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀'} {ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀'}
  {cov₀' : Admissible.Covering φ₀' ψ₀'} {πL' : cov₀'.ι → O}

/-! ### (b) Maps of the two-chart rings at level `n` -/

namespace Overlap

variable {I : Input θ cov₀ πL} {I' : Input θ cov₀' πL'} (V : Overlap I) (V' : Overlap I')
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

/-- **The map of `Q n = Y n[1/x₁]`** induced by `y : Y n → Y' n` with `y (x₁) = x₁'`. -/
def mQ (y : I.Y hθ n →+* I'.Y hθ n)
    (hy1 : y (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1) :
    V.Q hθ n →+* V'.Q hθ n :=
  IsLocalization.Away.lift (algebraMap I.B0 (I.Y hθ n) V.x1)
    (g := (algebraMap (I'.Y hθ n) (V'.Q hθ n)).comp y) (by
      rw [RingHom.comp_apply, hy1]
      exact IsLocalization.Away.algebraMap_isUnit _)

lemma mQ_algebraMap (y : I.Y hθ n →+* I'.Y hθ n)
    (hy1 : y (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (z : I.Y hθ n) :
    V.mQ V' hθ n y hy1 (algebraMap (I.Y hθ n) (V.Q hθ n) z) =
      algebraMap (I'.Y hθ n) (V'.Q hθ n) (y z) :=
  IsLocalization.Away.lift_eq _ _ z

/-- **The map of the overlaps `M n = P0 n[1/x₀]`** induced by `p : P0 n → P0' n` with
`p (x₀) = x₀'`. -/
def mM (p : V.P0.P n →+* V'.P0.P n)
    (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0)) :
    V.M n →+* V'.M n :=
  IsLocalization.Away.lift (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0))
    (g := (algebraMap (V'.P0.P n) (V'.M n)).comp p) (by
      rw [RingHom.comp_apply, hp0]
      exact IsLocalization.Away.algebraMap_isUnit _)

lemma mM_algebraMap (p : V.P0.P n →+* V'.P0.P n)
    (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (e : V.P0.P n) :
    V.mM V' n p hp0 (algebraMap (V.P0.P n) (V.M n) e) = algebraMap (V'.P0.P n) (V'.M n) (p e) :=
  IsLocalization.Away.lift_eq _ _ e

variable (y : I.Y hθ n →+* I'.Y hθ n)
  (hy1 : y (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
  (hyO : ∀ o : O, y (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
    (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o))
  (p : V.P0.P n →+* V'.P0.P n)
  (hp0 : p (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
    algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
  (hpO : ∀ o : O, p (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
  (hψ : ∀ z, V'.ψ hθ hO n (y z) = V.mM V' n p hp0 (V.ψ hθ hO n z))

include hψ in
/-- **The maps of the pieces are compatible with `ρ0a`**: `ρ0a' ∘ mQ = mM ∘ ρ0a`. -/
lemma ρ0aR_mQ (q : V.Q hθ n) :
    V'.ρ0aR hθ hO n (V.mQ V' hθ n y hy1 q) = V.mM V' n p hp0 (V.ρ0aR hθ hO n q) := by
  have : (V'.ρ0aR hθ hO n).comp (V.mQ V' hθ n y hy1) =
      (V.mM V' n p hp0).comp (V.ρ0aR hθ hO n) := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (algebraMap I.B0 (I.Y hθ n) V.x1)) (RingHom.ext fun z ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [mQ_algebraMap, ρ0aR_algebraMap, ρ0aR_algebraMap, hψ]
  exact RingHom.congr_fun this q

/-- **The maps of the pieces are compatible with `ρ0b`**: `ρ0b' ∘ p = mM ∘ ρ0b`. -/
lemma ρ0b_mM (e : V.P0.P n) : V'.ρ0b n (p e) = V.mM V' n p hp0 (V.ρ0b n e) :=
  (V.mM_algebraMap V' n p hp0 e).symm

/-- `y` as a map of `O`-algebras. -/
def yO : letI := V.algOY hθ n; letI := V'.algOY hθ n; I.Y hθ n →ₐ[O] I'.Y hθ n :=
  letI := V.algOY hθ n
  letI := V'.algOY hθ n
  { y with commutes' := hyO }

include hyO in
lemma mQ_algOQ (o : O) : V.mQ V' hθ n y hy1 (letI := V.algOQ hθ n; algebraMap O (V.Q hθ n) o) =
    (letI := V'.algOQ hθ n; algebraMap O (V'.Q hθ n) o) := by
  rw [V.algOQ_apply hθ n, mQ_algebraMap, hyO, V'.algOQ_apply hθ n]

/-- `mQ` as a map of `O`-algebras. -/
def mQO : letI := V.algOQ hθ n; letI := V'.algOQ hθ n; V.Q hθ n →ₐ[O] V'.Q hθ n :=
  letI := V.algOQ hθ n
  letI := V'.algOQ hθ n
  { V.mQ V' hθ n y hy1 with commutes' := V.mQ_algOQ V' hθ n y hy1 hyO }

/-- `p` as a map of `O`-algebras. -/
def pO : V.P0.P n →ₐ[O] V'.P0.P n := { p with commutes' := hpO }

/-- **The morphism of two-chart rings at level `n`** induced by `y : Y n → Y' n` and
`p : P0 n → P0' n` compatible on the overlaps `M n`: `f1 = y`, `f01 = mQ`, and on
`R0 = Q n ×_{M n} P0 n` the glued map of `mQ` and `p`. -/
def twoChartMap : TwoChartMap (A := O) (V.twoChart hθ hO n) (V'.twoChart hθ hO n) := by
  letI := V.alg0'Q hθ n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  letI := V.alg0'E n
  haveI := V.towerOE n
  letI := V.alg0'M n
  haveI := V.towerOM n
  letI := V.algOY hθ n
  letI := V'.alg0'Q hθ n
  letI := V'.algOQ hθ n
  haveI := V'.towerOQ hθ n
  letI := V'.alg0'E n
  haveI := V'.towerOE n
  letI := V'.alg0'M n
  haveI := V'.towerOM n
  letI := V'.algOY hθ n
  exact TwoChartGlue.twoChartMap (algebraMap I.B0 (I.Y hθ n) V.x1) (V.ιQ hθ n)
    (RingHomAway.of_algebra _) V.x0 (V.hxy hθ n) (V.ρ0a hθ hO n) (V.ρ0b n)
    (V.isLocalization_ρ0b n)
    (algebraMap I'.B0 (I'.Y hθ n) V'.x1) (V'.ιQ hθ n)
    (RingHomAway.of_algebra _) V'.x0 (V'.hxy hθ n) (V'.ρ0a hθ hO n) (V'.ρ0b n)
    (V'.isLocalization_ρ0b n)
    (V.yO V' hθ n y hyO) (V.mQO V' hθ n y hy1 hyO) (V.pO V' n p hpO) (V.mM V' n p hp0)
    hy1 (fun z ↦ V.mQ_algebraMap V' hθ n y hy1 z) hp0
    (fun q ↦ V.ρ0aR_mQ V' hθ hO n y hy1 p hp0 hψ q) (fun e ↦ V.ρ0b_mM V' n p hp0 e)

lemma twoChartMap_f1 (z : I.Y hθ n) :
    (V.twoChartMap V' hθ hO n y hy1 hyO p hp0 hpO hψ).f1 z = y z := rfl

lemma twoChartMap_f01 (q : V.Q hθ n) :
    (V.twoChartMap V' hθ hO n y hy1 hyO p hp0 hpO hψ).f01 q = V.mQ V' hθ n y hy1 q := rfl

lemma twoChartMap_fst (a : (V.twoChart hθ hO n).R0) :
    (letI := V'.alg0'Q hθ n; letI := V'.alg0'E n; letI := V'.alg0'M n
      ZariskiTwo.fst (V'.ρ0a hθ hO n) (V'.ρ0b n)
        ((V.twoChartMap V' hθ hO n y hy1 hyO p hp0 hpO hψ).f0 a)) =
      V.mQ V' hθ n y hy1 (letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
        ZariskiTwo.fst (V.ρ0a hθ hO n) (V.ρ0b n) a) := rfl

lemma twoChartMap_snd (a : (V.twoChart hθ hO n).R0) :
    (letI := V'.alg0'Q hθ n; letI := V'.alg0'E n; letI := V'.alg0'M n
      ZariskiTwo.snd (V'.ρ0a hθ hO n) (V'.ρ0b n)
        ((V.twoChartMap V' hθ hO n y hy1 hyO p hp0 hpO hψ).f0 a)) =
      p (letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
        ZariskiTwo.snd (V.ρ0a hθ hO n) (V.ρ0b n) a) := rfl

/-! ### (c) Compatibility with the successor maps -/

lemma qmap_mQ (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
    (hy1 : ∀ n, y n (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (hyS : ∀ n z, I'.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z)) (n : ℕ)
    (q : V.Q hθ (n + 1)) :
    V'.qmap hθ hO n (V.mQ V' hθ (n + 1) (y (n + 1)) (hy1 (n + 1)) q) =
      V.mQ V' hθ n (y n) (hy1 n) (V.qmap hθ hO n q) := by
  have : (V'.qmap hθ hO n : V'.Q hθ (n + 1) →+* V'.Q hθ n).comp
      (V.mQ V' hθ (n + 1) (y (n + 1)) (hy1 (n + 1))) =
      (V.mQ V' hθ n (y n) (hy1 n)).comp (V.qmap hθ hO n : V.Q hθ (n + 1) →+* V.Q hθ n) := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (algebraMap I.B0 (I.Y hθ (n + 1)) V.x1)) (RingHom.ext fun z ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [mQ_algebraMap, qmap_algebraMap, qmap_algebraMap, mQ_algebraMap, hyS]
  exact RingHom.congr_fun this q

/-- **The morphisms of two-chart rings commute with the successor maps**:
`succ' n ∘ twoChartMap (n+1) = twoChartMap n ∘ succ n`, if the maps `y n` commute with `Ymap`
and the maps `p n` with the successor maps `sP` of the pieces. -/
theorem succ_comp_twoChartMap (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
    (hy1 : ∀ n, y n (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (hyO : ∀ n (o : O), y n (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o))
    (p : ∀ n, V.P0.P n →+* V'.P0.P n)
    (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ n (o : O), p n (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
    (hψ : ∀ n z, V'.ψ hθ hO n (y n z) = V.mM V' n (p n) (hp0 n) (V.ψ hθ hO n z))
    (hyS : ∀ n z, I'.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z))
    (hpS : ∀ n e, V'.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e)) (n : ℕ) :
    (V'.succ hθ hO n).comp (V.twoChartMap V' hθ hO (n + 1) (y (n + 1)) (hy1 (n + 1))
      (hyO (n + 1)) (p (n + 1)) (hp0 (n + 1)) (hpO (n + 1)) (hψ (n + 1))) =
      (V.twoChartMap V' hθ hO n (y n) (hy1 n) (hyO n) (p n) (hp0 n) (hpO n) (hψ n)).comp
        (V.succ hθ hO n) :=
  TwoChartMap.ext_of_f0_f1
    (AlgHom.ext fun a ↦ Subtype.ext (Prod.ext (V.qmap_mQ V' hθ hO y hy1 hyS n a.1.1)
      (hpS n a.1.2)))
    (AlgHom.ext fun z ↦ hyS n z)

/-- `succ_comp_twoChartMap` for the induced morphisms of chart modules. -/
theorem succ_comp_twoChartMap_toHom (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
    (hy1 : ∀ n, y n (algebraMap I.B0 (I.Y hθ n) V.x1) = algebraMap I'.B0 (I'.Y hθ n) V'.x1)
    (hyO : ∀ n (o : O), y n (letI := V.algOY hθ n; algebraMap O (I.Y hθ n) o) =
      (letI := V'.algOY hθ n; algebraMap O (I'.Y hθ n) o))
    (p : ∀ n, V.P0.P n →+* V'.P0.P n)
    (hp0 : ∀ n, p n (algebraMap (V.B' n) (V.P0.P n) (algebraMap V.B0' (V.B' n) V.x0)) =
      algebraMap (V'.B' n) (V'.P0.P n) (algebraMap V'.B0' (V'.B' n) V'.x0))
    (hpO : ∀ n (o : O), p n (algebraMap O (V.P0.P n) o) = algebraMap O (V'.P0.P n) o)
    (hψ : ∀ n z, V'.ψ hθ hO n (y n z) = V.mM V' n (p n) (hp0 n) (V.ψ hθ hO n z))
    (hyS : ∀ n z, I'.Ymap hθ hO n (y (n + 1) z) = y n (I.Ymap hθ hO n z))
    (hpS : ∀ n e, V'.P0.sP n (p (n + 1) e) = p n (V.P0.sP n e)) (n : ℕ) :
    (V'.succ hθ hO n).toHom.comp (V.twoChartMap V' hθ hO (n + 1) (y (n + 1)) (hy1 (n + 1))
      (hyO (n + 1)) (p (n + 1)) (hp0 (n + 1)) (hpO (n + 1)) (hψ (n + 1))).toHom =
      (V.twoChartMap V' hθ hO n (y n) (hy1 n) (hyO n) (p n) (hp0 n) (hpO n) (hψ n)).toHom.comp
        (V.succ hθ hO n).toHom := by
  rw [← TwoChartMap.toHom_comp, ← TwoChartMap.toHom_comp,
    V.succ_comp_twoChartMap V' hθ hO y hy1 hyO p hp0 hpO hψ hyS hpS n]

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
