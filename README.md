# tempered-fundamental-groups

Tempered fundamental groups, developed over integral models.

## Goals

Formalise the tempered fundamental group and its relation to the metric graph of a Mumford curve.

The development follows Emmanuel Lepage, *Tempered fundamental group and metric graph of a Mumford
curve* (<https://arxiv.org/abs/0811.3169>), and Yves André's definition, but works with
**algebraic integral models instead of rigid or Berkovich geometry**: the formal completion of a
proper `O`-model along its special fibre has the special fibre as underlying space, and its
Zariski-locally trivial coverings are the covering spaces of that space (`Blueprint.md` §2, §7).

`Blueprint.md` is the detailed record: definitions, lemma chains with their status, and what
was cited rather than proved. This README is a summary of it.

## Main results

All results below are proved on `main` without `sorry`. `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`.

* **The tempered fundamental group** `TemperedFundamentalGroups.temperedPi1 O R A V hV`
  (`Tempered/Category.lean`) of an affine orbifold `[Spec R / A]` over a field `K` with a
  valuation subring `O`. It is a topological group in `Type u`: the automorphisms of the fibre
  functor on tempered coverings. A tempered covering is presented by a *level* (a finite étale
  `R`-algebra with a lift of the `A`-action), a *projective `O`-model* of the level, and an
  equivariant covering space of the special fibre of the model.
  `TemperedFundamentalGroups.temperedToEtale` (`Tempered/Comparison.lean`) is the continuous
  comparison homomorphism to the étale fundamental group `Pi1.Orbifold.etalePi1 R A Ω` from `pi1`.
* **Semistable reduction** `TemperedFundamentalGroups.SemistableReduction.Statement.strongA`
  (`SemistableReduction/StrongAProof.lean`; W10 via W7, Blueprint §9). The setting is a complete
  discretely valued field `K` of characteristic `0` with residue characteristic `p > 0` and perfect
  residue field, and a smooth `K`-domain `R` of dimension `1`. Every finite étale `R`-algebra `B`
  with a finite group `G` acting has an equivariant semistable projective model over the valuation
  ring of a finite Galois extension `K'/K`. This model dominates any given finite family of models.
  The proof follows Arzdorf–Wewers: Gauss-valued trees, local uniformization at type 3 and type 4
  points, stability at type 3 points, and descent.
* **Theorem A: André's identification** `TemperedFundamentalGroups.andreEquiv'`
  (`Andre/TheoremAFinal.lean`, Blueprint §10.5):
  `temperedPi1 O R A V hV ≃ₜ* andreGroup O R A V hV`. Here `andreGroup` (`Andre/Defs.lean`) is the
  automorphism group of the fibre functor restricted to coverings presented through *semistable*
  models, which is André's definition read off from semistable models. The hypotheses are:
  `O` a complete DVR, `K` of characteristic `0`, mixed characteristic (`(p : O) ∈ 𝔪_O` for a
  prime `p`), perfect residue field, `R` a smooth `K`-domain with `ringKrullDim R = 1`, `A` finite
  and acting `K`-linearly, and `Ω` algebraically closed. The conditional form
  `andreEquiv (hW : Statement.StrongA)` is in `Andre/Refinement.lean`.
* **Theorem B: the tempered group is not degenerate** for IUT's Tate orbicurves
  (Blueprint §10.3.8). `TemperedFundamentalGroups.TateOrbicurve.nondegenerate_of_normalForm`
  (`Andre/TateRestrictIUT.lean`) applies to `Y = E ∖ (E[ℓ] + M)` for a Tate curve in normal form
  `y² + xy = x³ + a₄x + a₆` with `ϖ^m ∣ a₄`, `a₆ = ϖ^m ε` (`ε` a unit, `m ≥ 1`), with `ℓ ≥ 1`,
  `M` finite, mixed characteristic and perfect residue field. It shows that
  `temperedPi1 [Y/A]` has an open normal subgroup with infinite quotient. The case `m ≥ 2` is
  `TateOrbicurve.nondegenerate_of_goodTate` (`Andre/TheoremBGoodTate.lean`; it holds for every `W`
  with `HasGoodTatePresentation W O`). The case `m = 1` is `TateOrbicurve.nondegenerate_of_isTate1`,
  which uses a ramified quadratic base change. The proof builds a `ℤ`-covering of the special fibre of the Tate
  model (a polygon), and lifts crossings of its nodes to the models of other coverings
  (`SemistableReduction.crossingX1`).
* **Zariski connectedness for model codes**
  `TemperedFundamentalGroups.SemistableReduction.Statement.zariskiConnected`
  (`SemistableReduction/ZariskiConnectedProof.lean`). A projective model over the valuation ring
  of a finite extension of a complete discretely valued field, with a scheme-theoretically dominant
  generic point, has a connected special fibre. It is deduced from Zariski's connectedness theorem
  `AlgebraicGeometry.ProjectiveSpace.isPreconnected_closedFibre` in `oka`. Theorem B uses it.

### Not covered

These are recorded in Blueprint §9.12 and §10.4. None of them is targeted.

* The identification with André's group (Theorem A) needs a *complete* base. For a henselian `K`
  that is not complete, `temperedPi1` is defined but not identified with André's group.
* Semistable reduction, and hence Theorem A, is proved only for mixed characteristic with perfect
  residue field. Equal characteristic `0` and imperfect residue fields are not covered.
* Theorem B is stated for Weierstrass equations in Tate normal form. Other equations of the same
  curve would need a change of variables, transported through `geomOrbicurveRing` and
  `temperedPi1`.

## Dependencies

Lean 4 `leanprover/lean4:v4.32.0`, Mathlib `v4.32.0`, and (`lakefile.toml`):

* [`pi1`](https://github.com/lana-agents/pi1) at `7647d28`: the étale fundamental group of an affine
  orbifold `Pi1.Orbifold.etalePi1` (profinite as `etalePi1Profinite`; for trivial `A` it is `≃ₜ*`
  Mathlib's `Aut (CommAlgCat.FiniteEtale.fiber R Ω)` by `etalePi1EquivAutFiber`; for a Galois
  presentation it is `GaloisData.equivPi1`), the fibre-functor topology `Pi1.Orbifold.FibreAut`,
  and the coded finite étale algebras (`EtaleCode`, `SemilinearAut`).
* [`elliptic-curves`](https://github.com/lana-agents/elliptic-curves) at `bebec3f`: finiteness of
  torsion (`finite_torsion_of_charZero`), which shows that the removed set `E[ℓ] + M` of the model
  orbicurves is finite.
* [`oka`](https://github.com/lana-agents/oka) at `405aadd`: Serre's finiteness theorem on projective
  space and Zariski's connectedness theorem (`ProjectiveSpace.isPreconnected_closedFibre`).

The downstream consumer is [`iut`](https://github.com/lana-agents/iut), which uses Theorem A
(`andreEquiv'`) in `Iut/Anabelian/TemperedAndre.lean`.

## Layout

Library sources live under `TemperedFundamentalGroups/`:

* `Setup/`, `Models/`, `Tempered/`: levels, models, specialization, the tempered category and
  `temperedPi1`;
* `FibreFunctor/`: fibre-functor automorphism groups, realization along full subcategories,
  Galois limits and characters;
* `Topology/`: covering spaces of special fibres, universal coverings and lengths;
* `SemistableReduction/`: semistable reduction (W4–W10) and Zariski connectedness;
* `Andre/`: André's group, Theorem A, and Theorem B with the Tate objects;
* `Orbicurve/`: IUT's model orbicurves `E ∖ (E[ℓ] + M)`.

Every file must be imported from the root module `TemperedFundamentalGroups.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib TemperedFundamentalGroups --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#7](https://taxis.lana.merten.dev/issues/7)

License: Apache 2.0 (see `LICENSE`).
