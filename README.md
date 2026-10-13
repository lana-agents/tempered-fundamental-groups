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
* **Functoriality** `TemperedFundamentalGroups.temperedPi1Map μ`
  (`Tempered/BaseChange.lean`, Blueprint §11). A map of affine orbifolds
  `μ : OrbMap R A R' A'` (`[Spec R' / A'] → [Spec R / A]`: an injective `K`-algebra map `R → R'`
  and a compatible group homomorphism `A' →* A`; finite étale covers, removal of points, orbifold
  covers) induces a continuous homomorphism `temperedPi1 O R' A' V hV →* temperedPi1 O R A V hV`,
  by base change of tempered coverings (`TempObj.bcFunctor`, `R' ⊗_R B` with `H ×_A A'`). For a
  finite étale cover `Spec R' → Spec R` (trivial groups) it is an open embedding with image of
  finite index (`isOpenEmbedding_temperedPi1Map`), the stabilizer of the base point of the cover
  (`temperedPi1Map_injective`, `mem_range_temperedPi1Map`, `finiteIndex_range_temperedPi1Map`,
  `Tempered/CoverImage.lean`). The same holds for an orbifold cover `[Spec R / A'] → [Spec R / A]`
  (`R = R'`, `A` finite, `R` a noetherian domain, `A'` acting faithfully, `A` acting
  `K`-linearly): `temperedPi1Map_injective_orbifold`, `isOpenEmbedding_temperedPi1Map_orbifold`,
  `range_temperedPi1Map_orbifold`, `finiteIndex_range_temperedPi1Map_orbifold`
  (`Tempered/OrbifoldCover.lean`, via induced coverings `Tempered/Induced*.lean`), and for the
  composite `Spec R' → Spec R → [Spec R / A]` (`temperedPi1Map_injective_mixed`,
  `isOpenEmbedding_temperedPi1Map_mixed`, `finiteIndex_range_temperedPi1Map_mixed`,
  `Tempered/MixedCover.lean`). The restriction `restrictHom` of T1 is the special case
  `Y → [Y/A]` (`restrictHom_eq_temperedPi1Map`, `Andre/TransferCompare.lean`).
  Changing the valued field `(K, O) → (K', O')` gives the continuous homomorphism
  `temperedPi1FieldMap : temperedPi1 O' R' A' →* temperedPi1 O R A` (`Tempered/FieldChange.lean`;
  models are base-changed to `O'`, `Models/BaseChange.lean`, and replaced by the image of the
  generic fibre, `Models/Image.lean`). It factors as the pure field change followed by
  `temperedPi1Map μ` (`temperedPi1FieldMap_comp`, `temperedPi1FieldMap_eq_comp`), so its image fixes
  the base point of a finite étale `Spec R' → Spec R` (e.g. `R' = K' ⊗_K R`)
  (`Tempered/FieldChangeImage.lean`). If `O'` is finite over `O`, the pure field change is an
  isomorphism of topological groups `temperedPi1FieldEquiv` (`Tempered/FieldChangePure.lean`, via
  restriction of scalars of models along a closed immersion `ℙᵐ_{O'} ⟶ ℙᴺ_O`,
  `Models/RestrictScalars.lean`, and the criterion `FibreFunctor/SectionRestrict.lean`). This
  holds whenever `O` is a complete DVR and `K'/K` is finite separable (`valMap_finite`,
  `Tempered/FieldChangeFinite.lean`: the integral closure of a complete DVR is local and is the
  unique valuation ring over it, `Setup/CompleteDVRExtension.lean`), giving the unconditional
  `temperedPi1FieldEquiv'`. Hence `temperedPi1FieldMap hO μ` has the same image as
  `temperedPi1Map μ` (`range_temperedPi1FieldMap_eq`): an open embedding onto the finite-index
  stabilizer for `Spec R' → Spec R` finite étale (`isOpenEmbedding_temperedPi1FieldMap'`,
  `range_temperedPi1FieldMap'`, `finiteIndex_range_temperedPi1FieldMap'`), for orbifold covers
  and the mixed case (`*_temperedPi1FieldMap_orbifold`, `*_mixed`,
  `Tempered/FieldChangeOrbifold.lean`), and an open subgroup of finite index for finite étale maps
  of orbifolds `[Spec R' / A'] → [Spec R / A]` (`isOpen_range_temperedPi1FieldMap_etaleOrb`,
  `finiteIndex_range_temperedPi1FieldMap_etaleOrb`), where `temperedPi1Map` and the field change are
  open embeddings (`isOpenEmbedding_temperedPi1Map_etaleOrb`,
  `isOpenEmbedding_temperedPi1FieldMap_etaleOrb`, `Tempered/EtaleOrbCover.lean`). With Theorem A on
  both sides André's groups agree, `andreFieldEquiv'` (`Andre/FieldChange.lean`); the direct
  field change `andreFieldMap` (restriction of scalars of semistable coverings,
  `Andre/FieldChangeDirect.lean`) is its inverse (`andreFieldEquivDirect_symm`).
  The comparison maps are natural: `temperedToEtale_temperedPi1Map` (with `etalePi1Map μ`,
  `Tempered/BaseChangeEtale.lean`) and `andreEquiv'_temperedPi1Map` (with `andreGroupMap μ`,
  `Andre/Functoriality.lean`).
* **Zariski connectedness for model codes**
  `TemperedFundamentalGroups.SemistableReduction.Statement.zariskiConnected`
  (`SemistableReduction/ZariskiConnectedProof.lean`). A projective model over the valuation ring
  of a finite extension of a complete discretely valued field, with a scheme-theoretically dominant
  generic point, has a connected special fibre. It is deduced from Zariski's connectedness theorem
  `AlgebraicGeometry.ProjectiveSpace.isPreconnected_closedFibre` in `oka`. Theorem B uses it.
* **Maps of dual graphs** (Blueprint §11.2, G4, `Andre/DualGraphMap.lean`). The bundled
  `SemistableReduction.ModelCode.IsDualGraphMap ψ` for a morphism of models `ψ : c ⟶ c'`:
  components go to components or points (`vertexMap`; for every closed `ψ` by
  `contracted_or_mem_components`), nodes to nodes or to smooth points on one component
  (`edgeMap`), compatibly with incidence, with edge lifting along crossing walks. Maps of
  unfolded split semistable W-models are such maps, harmonic for the x-lengths
  (`SemistableReduction.isHarmonicDualGraphMap_of_harmonicX`).
* **André's group as a limit of stage groups** (Blueprint §11.3, G6.1–G6.2).
  `TemperedFundamentalGroups.andreGroupEquivLim` (`Andre/StageLimit.lean`):
  `andreGroup ≃* stageLimit` (`andreGroupHomeoLim`: `≃ₜ*`), the inverse limit over pointed Galois objects `U_Lv` over semistable
  W-model levels of their stage groups `Π_Lv` (permutations of the fibre induced by `Aut U_Lv`),
  from the group form of K1 `GaloisLimit.fibreAutEquiv` (`FibreFunctor/GaloisGroupLimit.lean`).
  Each `Π_Lv` is an extension of `Aut_R(B)ᵒᵖ` by the deck group of the tree covering of the dual
  graph (`stageGroup_extension`, `Andre/StageGroup.lean`), which is the combinatorial
  fundamental group of the dual graph: `deckLoopEquiv : deckGroup ≃* Loop` with the group of
  reduced closed walks at the root under concatenation and reduction
  (`Andre/DualGraphPi1.lean`, `Topology/DualGraphPi1.lean`).
  For an orbifold `[Spec R / A]` (`A` finite, acting `K`-linearly; Blueprint §11.3, G6.7–G6.9):
  `andreGroupHomeoLimO : andreGroup ≃ₜ* stageLimitO` (`Andre/OrbStageLimit.lean`), over the
  orbifold Galois objects `galClassO` (`Ind_1^S Z̃` over levels induced from scheme levels that
  are Galois over `[Spec R / A]`, `Andre/OrbGalois*.lean`, with Galois closures over
  `[Spec R / A]`, `Andre/OrbClosure.lean`); the deck group of `Z̃` is the kernel of the action of
  each stage group on level classes (`mem_range_deckStageO_iff`, `Andre/OrbStageGroup.lean`), and
  `stageGroupO_extension` (`Andre/OrbStageLevel.lean`) gives `1 → deck → Π_U →
  (SemilinearAut R A B)ᵐᵒᵖ → 1`, the image on level classes being the action of
  `S ×_A SemilinearAut R A B` modulo `ker α × 1`; transition maps preserve deck groups and induce
  the maps of trees (`Andre/OrbStageFunctor.lean`).
* **Semi-graphs of anabelioids and tree towers** (Blueprint §12, IUT wall P13; [SemiAnbd] §§1–3,
  Thm. 3.7; [CombGC] Prop. 1.5). Semi-graphs (`SemiAnbd/SemiGraph.lean`) and semi-graphs of
  anabelioids in group form with their category of finite coverings `B(𝒢)`, the fundamental group
  `SemiGraphOfAnabelioids.Pi` (automorphisms of the fibre functor) and the verticial homomorphisms
  (`SemiAnbd/Anabelioid.lean`; anabelioids are Mathlib's Galois categories, `anabelioidEquiv`).
  Groups acting on trees: the gate lemma, the centre of a finite set and the **fixed point theorem**
  `TreeGeom.exists_fixed` (a group acting without inversions with a finite invariant set fixes a
  vertex; `SemiAnbd/TreeFixedPoint.lean`). **Tree towers** (`SemiAnbd/TreeTower.lean`): a group `Γ`
  with homomorphisms to groups acting on trees and equivariant non-expanding maps of trees, the
  shape of `lim Π_Lv`; verticial subgroups `TreeTower.stab s` of compatible systems of vertices are
  **commensurably terminal** (`commensurator_stab`) and pairwise incomparable (`eq_of_stab_le`) when
  edge stabilizers have infinite index (`HI`, implied by elevatedness, `HI_of_elevated`); subgroups
  with bounded displacement fix a system (`exists_le_stab_of_bounded`); in functorial **estranged**
  towers every nontrivial subgroup with finite images (e.g. compact) lies in a verticial subgroup
  (`exists_isVert_le_stab_of_estranged`, [SemiAnbd] Thm. 3.7(iii),
  `SemiAnbd/TreeTowerCompact.lean`); isomorphisms mapping verticial subgroups onto verticial
  subgroups induce equivariant bijections of vertex systems (`nonempty_vertexCorrespondence`), and
  the tree-tower form of the combinatorial Grothendieck conjecture,
  `isGraphic_iff_isGroupTheoreticallyVerticial` (`SemiAnbd/CombGC.lean`), holds under a stated
  PSC-type adjacency hypothesis, which follows from estrangement, no branch inversions and
  nontrivial edge-like subgroups (`pscAdj_of_estranged`, `isGraphic_iff_of_estranged`). **For
  curves**: the tree covering of the dual graph is a tree (`CurveConfig.isTree_treeGraph`), its
  combinatorial `π₁` and the deck groups have no torsion, finite subgroups of stage groups embed
  into `Aut_R(B)ᵒᵖ` (`Andre/StageTorsion.lean`); stage groups act on the trees (`UData.stageTree`,
  `Andre/StageTree.lean`), giving the tree tower `andreTower` on André's group
  (`Andre/StageTower.lean`, `Andre/CurveTower.lean`), whose verticial and edge-like subgroups are
  **compact** (`isCompact_stab_andreTower`); its trees are locally finite, its maps are functorial
  up to one step and functorial along non-contracting morphisms (`stageTower_map_comp_eq_or_adj`,
  `isFunctorial_restrict_stageTower`, `Andre/CurveTowerFunctor.lean`), so on any cofiltered
  non-contracting subsystem of levels that is estranged, every nontrivial compact subgroup of
  André's group fixes a compatible system of vertices and (with no branch inversions and nontrivial
  edge-like subgroups) `PSCAdj` holds (`exists_le_stab_restrict_andreTower`,
  `pscAdj_restrict_andreTower`). Every transition map of André's tower *reflects nodes* (a point
  on a single component goes to a node only if its component does; **M1**, proved by local
  commutative algebra at étale node charts: `ModelCode.map_eq_of_isNodePt`,
  `SemistableReduction/NodeReflection.lean`, `reflectsNodes_curveData`,
  `Andre/CurveTowerNodes.lean`), so the maps preserve sheets and **André's tower is functorial on
  all levels** (`isFunctorial_andreTower_galW`); and the stage groups act **without branch
  inversions** (**M3**: the two branches of a node of an unfolded W-model restrict to Gauss points
  of the x-line of different radii, which automorphisms over the x-line preserve;
  `exists_branches_not_swapped`, `noBranchSwap_andreTower`, `Andre/CurveTowerBranches.lean`).
  Hence, if the tower is estranged, every nontrivial compact subgroup of André's group (or of a
  subgroup such as the geometric one) fixes a compatible system of vertices of all levels and
  maximal compact subgroups are stabilizers of systems
  (`exists_le_stab_andreTower_of_estranged`, `exists_le_stab_andreTower_of_le_estranged`,
  `exists_eq_stab_of_maximal_of_estranged`), and with nontrivial edge-like subgroups `PSCAdj` and
  CG3' hold for André's group, also between the André groups of two curves
  (`pscAdj_andreTower_of_estranged'`, `isGraphic_iff_andreTower_andreTower`). Not covered: the
  profinite statements (no profinite trees), the comparison of verticial subgroups with
  fundamental groups of components (no analytic or log geometry), and the remaining geometric
  inputs for curves, stated as missing theorems M2 and M4 (Blueprint §12.5 C10, C12, §12.7):
  specialization of admissible coverings (for `HI` of hyperbolic components, estrangement and
  nontrivial edge-like subgroups of the tame part) and estrangement for wild coverings.
  Estrangement and nontrivial edge-like subgroups are not proved for any curve. **M4 (wild
  estrangement)** is stated precisely (Blueprint §12.10, `SemiAnbd/Estrangement.lean`,
  `Andre/WildEstrangement.lean`): for a set `P` of (tame) levels, `WildEstrangement Δ P` asks
  that the nontrivial elements of `Δ` acting trivially on all trees of `P`-levels have fixed sets
  of diameter `≤ 2` at cofinally many levels; with `TameEstrangement Δ P` it is equivalent to the
  estrangement hypothesis of the consumers (`estranged_comap_andreTower_iff`,
  `exists_le_stab_andreTower_of_tame_wild`, `isGraphic_iff_andreTower_of_tame_wild`). Proved
  around it: M4 forces the wild kernel to act nontrivially on non-tame levels below every level
  (`WildEstranged.exists_not_mem`), and for towers of line trees (dual graph a cycle, as for the
  Tate curve's `2`-gon) estrangement is equivalent to faithfulness at cofinal finite levels
  (`estranged_iff_of_lineAt`). M4 itself is open (research-level, of the nature of resolution of
  non-singularities).
* **The double covering `Ÿ → Y` of [EtTh] §1** (`Andre/TateObjectDouble.lean`, Blueprint B6′):
  for Tate data with `2` and `x − e` units in `R` (`e` the `x`-coordinate of the `2`-torsion point
  `√q`; the `2`-isogeny covering `E_{√q} → E_q` is `R[t]/(t² − (x − e))`), the object `Yddot` with
  deck group `ℤ × ℤ/2` acting simply transitively on its fibre (`isDeckTorsor₂`), the continuous
  character `character₂` and `piYddot` (`Π^tp_Ÿ`, open normal, `≤ Π^tp_Y`, of index `≤ 2` in it:
  `relIndex_le_two`; index `2` given an element of `Π^tp_Y` swapping the sheets of `X'`,
  `relIndex_eq_two`, e.g. a decomposition-group element moving `√(x − e)`:
  `relIndex_eq_two_of_galois`). Not covered: the case `X = E ∖ {0}` itself, where the Kummer
  presentation is not étale at the `2`-torsion point.
* **Temp-slimness** (Blueprint §12.9; [SemiAnbd] Ex. 3.10, the hypothesis of [EtTh]
  Prop. 2.11(ii) and Cor. 2.19(i)). `TempSlim P` (every open subgroup has trivial centralizer),
  invariant under `≃ₜ*` and inherited by open subgroups (`SemiAnbd/TempSlim.lean`); extensions
  (`TempSlim.of_extension`); Mochizuki's argument `TempSlim.of_commensurator_eq`: one compact,
  commensurably terminal, temp-slim subgroup suffices, so for tree towers
  `TreeTower.tempSlim_of_HI`. For curves (`Andre/TempSlim.lean`): `tempSlim_temperedPi1`,
  `tempSlim_ker_character` (`Π^tp_Y`), `tempSlim_piYddot` (`Π^tp_Ÿ`), **conditional** on
  `VerticialTempSlim` (some system of André's tower with `HI` and a temp-slim verticial
  subgroup), which needs M2 and the slimness of the decomposition groups of components; not
  proved for any curve.

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
* `SemiAnbd/`: semi-graphs of anabelioids, groups acting on trees, tree towers and the
  combinatorial Grothendieck conjecture;
* `Orbicurve/`: IUT's model orbicurves `E ∖ (E[ℓ] + M)`.

Every file must be imported from the root module `TemperedFundamentalGroups.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
bash scripts/mk_all.sh TemperedFundamentalGroups   # regenerate the root module (keeping its header) after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`scripts/mk_all.sh --check`, i.e. `mk_all --check` below the root
  module's copyright header), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#7](https://taxis.lana.merten.dev/issues/7)

License: Apache 2.0 (see `LICENSE`).
