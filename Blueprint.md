# Blueprint: the tempered fundamental group via integral models

Status legend: **[L]** formalized in Lean in this repository (no `sorry`/`axiom`), **[P]** planned
in Lean, **[C]** cited from the literature and *not* formalized (the precise statement is
recorded here so that the gap is visible), **[✗]** out of reach with the present libraries.

## 0. Target

The consumer is `Iut.Anabelian.TemperedPi1Theory Pi1` (lana-agents/iut,
`Iut/Anabelian/Geometry.lean`): for every model orbicurve `X = (E, ℓ, M, ±)` over a field `k`
a topological group `tempPi1 X : Type u` and a continuous homomorphism
`tempPi1 X →* Pi1.pi1 X` to the étale fundamental group supplied by the sibling construction.
The interface is weak (a trivial instance type-checks), so the requirement is that
`tempPi1 X` *is* André's tempered fundamental group of `X` for the curves IUT uses: Tate
curves minus torsion `(E_q/M) ∖ (E_q[ℓ]/M)` over complete discretely valued fields `K` of
characteristic 0 (residue characteristic 2 allowed), and their `{±1}`-quotients.

## 1. André's definition and Lepage's formula

Let `K` be a complete non-archimedean field and `X` a smooth `K`-variety.

* A morphism of `K`-analytic spaces `S → X^an` is an *étale covering* (de Jong) if `X^an` is
  covered by opens over which it is a disjoint union of finite étale maps.
* It is *tempered* (André, *Period mappings*, III.2.1.1) if it becomes a topological covering
  after pullback along some finite étale `T → X`.
* `π₁^temp(X, x̄) := Aut(F_x̄)` for the fibre functor on tempered coverings, with the topology
  for which the stabilizers of points of fibres form a basis of open subgroups.
* (Lepage, §1.1, citing André III.2.1.5) If `(S_i)` is a cofinal system of pointed Galois
  finite étale covers and `S_i^∞` the universal topological covering of `S_i^an`, then
  `π₁^temp(X, x̄) ≅ lim_i Gal(S_i^∞ / X)`.

Two facts make a model-theoretic description possible:

* (André III.1.1.4) Topological coverings of `S^an` extend uniquely across a nowhere dense
  Zariski closed subset. Hence for a curve `S = S̄ ∖ D` one may compute topological
  coverings on the *proper* curve `S̄`.
* (Raynaud, Berkovich) For a proper curve `C/K`, `C^an` is (up to maximal Hausdorff quotient)
  the inverse limit of the special fibres `|𝒞_s|` of its proper models `𝒞/O_K`, and
  topological coverings of `C^an` are exactly the pullbacks along the specialization map of
  the Zariski covering spaces of `|𝒞_s|` for sufficiently fine models (semistable models with
  loop-free dual graph suffice, e.g. by Berkovich's retraction onto the skeleton).

## 2. Why integral models and not Berkovich/rigid spaces or formal generic fibres

`formal-schemes` provides affine formal schemes, gluing, completions along closed subsets (affine
case), separatedness, fibre products over an affine base and a formal Tate model (period `q²`).
It does not provide Raynaud generic fibres, étale morphisms of formal schemes, normalization of
formal schemes, Grothendieck existence, or admissible blow-ups. A literal "formal model +
generic fibre" definition is therefore not available.

It is also not needed: for a proper `O_K`-scheme `𝒞`, the formal completion `𝒞^` along the
special fibre has underlying space `|𝒞_s|`, and a Zariski-locally trivial covering of the
formal scheme `𝒞^` is the same thing as a covering space of the topological space `|𝒞_s|`
(the structure sheaf is pulled back along the local homeomorphism). By formal GAGA every
formal model of a proper curve is algebraizable. So "topological coverings of `C^an` read off
from formal models" is literally "covering spaces of `|𝒞_s|` for proper `O_K`-models `𝒞`",
which is expressible with Mathlib's schemes. This is the definition used below. The
formal-scheme vocabulary enters through `|𝒞^| = |𝒞_s|`; nothing of `formal-schemes` is
imported by the core, and it is not a Lake dependency yet.

## 3. The definition formalized here

### 3.1 Base data (`Setup/Valuation.lean`, `Setup/Orbifold.lean`)

* a field `K` with a valuation subring `O ⊆ K` (the ring of integers);
* a field `Ω` with a valuation subring `V ⊆ Ω` and `K → Ω` with `V ∩ K = O` (a geometric
  point with a chosen extension of the valuation — it fixes the specialization of geometric
  points; the definitions only need a field, the étale and tempered groups are the usual ones
  when `Ω` is algebraically closed, e.g. the algebraic closure of the function field of `Y`);
* the curve as an orbifold `[Y/A]`: an affine `K`-scheme `Y = Spec R` with a group `A`
  acting on `R` by `K`-algebra automorphisms (for IUT: `Y = E ∖ S` with `S = E[ℓ] + M` the
  full closed subset of geometric points, `A = M` or `M ⋊ {±1}`; `A` trivial gives the scheme
  `Y`);
* a geometric point `ȳ : R → Ω` (an `R`-algebra structure on `Ω` compatible with `K`).

`AffineOrbifold k` bundles `R, A, Ω, ȳ`; the valuation `V` is chosen by Chevalley's extension
theorem (`ValuationSubring.exists_comap_eq`) and `O` defaults to `canonicalValuationSubring k`.

No completeness is required by the definition; it is the tempered group of `Y_{K^}` when `O`
is henselian.

### 3.2 Levels (finite étale covers of `[Y/A]` with a model)

A *level* (`FiniteLevel`) is

* a finite étale `R`-algebra `B` (so `T = Spec B → Y` is finite étale), presented as
  `MvPolynomial (Fin n) R ⧸ I` so that levels form a `Type u`;
* a subgroup `H` of `G_B = {(a, σ) : a ∈ A, σ ∈ Aut_ring(B), σ ∘ (R → B) = (R → B) ∘ a}`
  surjecting onto `A` (the lift of the `A`-action to `T` that is used); `H⁰ = ker(H → A)`.

No Galois condition and no base point are needed: `(P ×_{sp} T^an)/H⁰` (below) is an
`A`-equivariant tempered covering of `Y^an` for every level, and Galois levels are cofinal.

A *level with a model* (`Level`) adds:

* a proper `O`-scheme `𝒯` given as a closed subscheme of `ℙ^m_O = Proj O[x₀..x_m]`
  (projective models are cofinal among normal proper models of curves: Lichtenbaum; codes
  keep everything in `Type u`);
* a morphism `j : Spec B → 𝒯` over `Spec O`;
* an action `ρ : H →* Aut 𝒯` over `Spec O` with `j` equivariant (`g` acts on `Spec B` by
  `Spec(σ_g⁻¹)`).

No flatness, normality or open-immersion hypothesis is imposed: any such datum produces a
genuine topological covering of `T^an` (pull back along `j^an` and specialization), and the
refinement argument of §4 shows that the extra models do not change the automorphism group.

### 3.3 Specialization (`Models/Specialization.lean`)

For a proper (universally closed and separated suffices) `𝒯 → Spec O` and a geometric point
`t : Spec Ω → 𝒯` over `Spec K → Spec O`, the valuative criterion gives a unique lift
`Spec V → 𝒯`; `sp(t)` is the image of the closed point. It lies in the special fibre
`|𝒯_s| = 𝒯 ×_O k` (as a subspace of `|𝒯|`) and is natural for morphisms of models.

### 3.4 Objects, morphisms, fibre functor (`Tempered/Category.lean`)

An object over a level with a model `L` is an `H`-equivariant covering space `P → |𝒯_s|`,
coded with carrier a subset of `|𝒯_s| × ℕ` (connected covering spaces of a noetherian space have
countable fibres, so this loses nothing up to isomorphism; §4).

A morphism `(L', P') → (L, P)` is: an `R`-algebra map `f : B → B'` with a compatible group
homomorphism `r : H' → H` over `A`, a morphism of models `ψ : 𝒯' → 𝒯` over `O` with
`j ∘ Spec f = ψ ∘ j'`, and a continuous `r`-equivariant map `h : P' → P` over `ψ_s`.

The fibre functor is
`Φ(L, P) = {(t, p) : t ∈ Hom_R(B, Ω), p ∈ P, p ↦ sp(j ∘ t)} / H⁰`, the fibre over `ȳ` of the
realization `(P ×_{sp} T^an)/H⁰`, an `A`-equivariant tempered covering of `Y^an`.
`Φ(f, ψ, h)[(t, p)] = [(t ∘ f, h p)]` (well defined by uniqueness of specialization and
equivariance).

### 3.5 The groups

* `temperedPi1 := Aut Φ`, with the group topology whose basic open subgroups are the
  stabilizers of finitely many fibre elements (pointwise convergence on discrete fibres). It
  is a Hausdorff, totally separated, non-archimedean (prodiscrete) topological group.
* `etalePi1 := Aut` of the fibre functor `B ↦ Hom_R(B, Ω)` on `A`-equivariant finite étale
  `R`-algebras (`Pi1/Orbifold/Etale.lean` of the `pi1` dependency). This is the étale fundamental group of `[Y/A]` by
  definition (SGA 1 V for `A = 1`; equivariant covers for the quotient stack). It is compact
  (profinite) since the fibres are finite.
* `temperedToEtale : temperedPi1 →* etalePi1` (`Tempered/Comparison.lean`) is restriction along
  the strict functor "level `(B, image of A)`, trivial model `Spec O`, one-sheeted covering",
  which commutes with the fibre functors. It is continuous.

## 4. Why this is André's group (the identification chain)

Let `R : 𝒞 → Temp_A(Y)` be the realization functor, `Φ ≅ F_ȳ ∘ R`.

1. **[C]** (Raynaud–Berkovich comparison) Pulling back a covering space of `|𝒯_s|` along
   `sp ∘ j^an` is a topological covering of `T^an`; every topological covering of `T^an`
   arises this way for a sufficiently fine `G_T`-equivariant projective model (semistable
   reduction of `T̄` after a finite extension, descended to `O_K` by taking quotients; blow-ups to
   remove loops; Lichtenbaum for projectivity; André III.1.1.4 to pass from `T` to `T̄`).
2. **[C]** (André III.2.1.5 / Lepage §1.1) every `A`-equivariant tempered covering is split by
   some Galois cover of `[Y/A]`, and `π₁^temp = lim Gal(T^∞/[Y/A])`.
3. **[P]** (formal) If a functor `R` with `Φ ≅ F ∘ R` is essentially surjective and every
   morphism between realizations is realized after refinement, then whiskering
   `Aut F → Aut Φ` is an isomorphism of topological groups. Refinements exist because levels
   are directed (common Galois covers; closure of the diagonal image in a product of
   projective models, which is again projective by the Segre embedding).
4. **[P]** (countable fibres) Every connected covering space of a noetherian topological space
   has countable fibres; hence the carrier restriction `⊆ |𝒯_s| × ℕ` gives an equivalent
   category after adding coproducts, and does not change `Aut Φ`.

Steps 1–2 are where Berkovich geometry would enter; they are the precise content of
"owner-accepted formal-model definition à la Lepage". The definition itself uses no
semistable reduction.

### Semistable reduction and the Schottky route

* The *definition* does not need semistable reduction; only the identification step 1
  (essential surjectivity of `R`) does.
* For `Y` itself (a Tate curve minus torsion) the Schottky/Tate uniformization makes
  topological coverings explicit: the special fibre of a model with an `n`-gon (`n ≥ 2`)
  reduction carries the `ℤ`-covering of the uniformization `𝔾_m → E_q`.
* It does **not** avoid semistable reduction for the tempered group: tempered coverings are
  topological coverings of *arbitrary* finite étale covers `T → Y`, and these are curves of
  arbitrary genus which are in general not Mumford curves (their special fibres have
  components of positive genus). No explicit cofinal family of covers with explicit stable
  models is known. The Schottky route suffices only for specific quotients (e.g. the
  `ℤ`-quotient `π₁^temp(E_q ∖ 0) ↠ ℤ` used for the étale theta function), not for the group.

## 5. Lemma chain (Lean), with status

| # | Statement | File | Status |
|---|-----------|------|--------|
| A1 | Pointwise-convergence group topology on `Aut F`, `F : C ⥤ Type`; stabilizers are an open basis; `T2`, totally separated | `pi1`: `Pi1/Orbifold/FibreAut.lean` | [L] |
| A2 | Restriction along `G : C' ⥤ C` with `G ⋙ F ≅ F'` gives a continuous hom `Aut F → Aut F'` | same | [L] |
| A3 | If every `F c` is finite, `Aut F` is compact (profinite) | same | [L] |
| B1 | `ℙ^m_O := Proj O[x₀..x_m]`, proper over `Spec O`; model codes are proper; `ℙ⁰_O ≅ Spec O` | `Models/Projective.lean` | [L] |
| B2 | Special fibre as a subspace; functoriality | `Models/Specialization.lean` | [L] |
| B3 | Specialization of `Ω`-points via the valuative criterion; uniqueness; naturality | same | [L] |
| C1 | Covering codes over a space, `G`-equivariance, fibres, trivial coverings | `Topology/CoveringCode.lean` | [L] |
| D1 | Levels `(B, H)`, `G_B`, `H⁰`, action on geometric fibres | `Tempered/Level.lean` | [L] |
| D2 | The category `TempObj`, fibre functor `tempFibre`, `temperedPi1 := Aut` | `Tempered/Category.lean` | [L] |
| D3 | `etalePi1` on `A`-equivariant finite étale algebras; functor `etaleToTemp`; continuous `temperedToEtale` | `pi1`: `Pi1/Orbifold/Etale.lean`; `Tempered/Comparison.lean` | [L] |
| E1 | `etalePi1` is profinite; for `A = 1` it is `≃ₜ*` to Mathlib's `Aut (CommAlgCat.FiniteEtale.fiber R Ω)` | `pi1`: `Pi1/Orbifold/EtaleProfinite.lean`, `EtaleMathlib.lean` | [L] |
| E2 | (untargeted extension) imperfect residue fields: smoothness of the E-charts at non-separable closed points (geometrically regular ⇒ smooth, descent of smoothness) | — | not planned |
| E2 | Step 3 of §4: restriction along a realization (essentially surjective, morphisms realized after refinement) is `≃ₜ*` | `FibreFunctor/Realization.lean` | [L] (abstract lemma; its hypotheses for André's category are steps 1–2, [C]) |
| E3 | Countable fibres of connected coverings of noetherian spaces (step 4) | `Topology/CountableFibres.lean` | [L] (topological lemma; the resulting equivalence of categories after adding coproducts is argued, not formalized) |
| E4 | Galois elements: the decomposition group `{σ ∈ Aut_R(Ω) : σV = V}` acts on `temperedPi1` (`[(t,p)] ↦ [(σ∘t, p)]`, specialization is Galois invariant), compatibly with its action on `etalePi1` | `Tempered/Galois.lean`, `Models/Specialization.lean` (`sp_galois`) | [L] |
| F1 | Orbicurve presentation: `Y = E ∖ S` with `S = E[ℓ] + M ⊆ E(k̄)` (all geometric points, for every field `k`): `R = ringAway W S` = `k[E]` with the inverses of the functions vanishing only on `S` adjoined; `A = M` or `M ⋊ {±1}` acting by translations and negation (stability without Nullstellensatz); exactness: `R = k[E][Ψ(x)⁻¹]` with `Z(Ψ(x)) = S ∖ {0}` whenever `S` is finite (Nullstellensatz in `k[E]`), proved finite for `ℓ ≥ 1`, `M` finite, in char `0` and in char `p ∤ 2ℓ`; `orbicurveOrbifold` | `Orbicurve/` (`ZeroSet`, `GeomStable`, `Exact`, `GeomModel`, `Orbifold`) | [L] |
| F2 | Canonical valuation on `k` (the henselian DVR if one exists, else trivial); Chevalley extension to `Ω`; pointed affine orbifolds | `Setup/Valuation.lean`, `Setup/Orbifold.lean`, `Setup/Schmidt.lean` | [L], including canonicity (F. K. Schmidt for henselian DVRs: `canonicalValuationSubring_eq_of_isHenselianDVR`) |
| F3 | `TemperedPi1Theory` instance from the above and a continuous comparison `etalePi1 → Pi1.pi1` (the identity if the étale theory uses `AffineOrbifold.etalePi1Profinite`) | iut branch `wp-tempered-iut`, `Iut/Anabelian/Tempered.lean` (`temperedTheory Pi1 C`) | [L] modulo the comparison `C`, which needs the sibling's étale construction |
| G1 | Non-degeneracy witness: `π₁^temp(E_q ∖ E[ℓ]) ↠ ℤ` (discrete, not profinite) | `FibreFunctor/Character.lean` (the continuous character `Aut Φ → D` of any deck torsor; surjectivity criterion) | character [L]; surjectivity [✗], see §5.1 |
| G2 | Steps 1–2 of §4 | — | [✗] (needs Berkovich spaces / semistable reduction) |

### 5.1 The non-degeneracy witness (G1): what is proved and the precise obstruction

*Proved.* If an object `X₀` of `TempObj` carries deck transformations `δ : ℤ →* Aut X₀` acting
simply transitively on `Φ(X₀)` (e.g. the universal covering of a cycle of `P¹`'s in the special
fibre of a model), then `α ↦ (the translation by which α acts on Φ(X₀))` is a continuous
homomorphism `temperedPi1 → ℤ` (`FibreAut.deckCharacter`), and it is surjective iff some `α`
moves the base point by the generator (`deckCharacter_surjective_iff`). The Galois elements
(`galoisToTempered`) cannot provide this: they form a compact image, whose image in the discrete
group `ℤ` is finite, hence `0`.

*Obstruction.* An element of `Aut Φ` must be given on **every** object — every finite étale
cover `T` of `[Y/A]`, every projective model of `T`, every equivariant covering of its special
fibre — compatibly. Constructing the element realizing the generator of `ℤ` therefore requires the
Galois theory of `TempObj`:
1. directedness of levels (common Galois covers; common refinements of models: closure of the
   diagonal image in a product of projective models, re-embedded by Segre — algebraic, feasible);
2. for a fixed level, `Aut Φ|_level = π₁^orb(H ↷ |𝒯_s|)` (covering-space theory of noetherian
   spaces with a finite group action — topological, feasible);
3. surjectivity of the transition maps `π₁(|𝒯'_s|) → π₁(|𝒯_s|)` under refinement — needs connected
   fibres of `𝒯' → 𝒯` on special fibres (Zariski's connectedness for *normal* models), so the
   index system must be restricted to normal models (normalization of projective models inside
   the codes — feasible but substantial);
4. existence of an element of the inverse limit of these (discrete, infinite) groups lifting the
   generator: the index system is uncountable (all models over an uncountable `K_v`), so
   Mittag-Leffler does not apply; the argument of André/Lepage uses that for each `T` the
   groups `π₁(|𝒯_s|)` **stabilize** once `𝒯` is semistable with loop-free dual graph, i.e. the
   **semistable reduction theorem** for all finite étale covers `T` (steps 1–2 of §4). This is
   the genuine blocker.
5. independently, an explicit object `X₀`: a projective `O`-model of the Tate curve (or of a
   finite étale cover of `E_q ∖ E[ℓ]`) whose special fibre contains a cycle, e.g. the blow-up of
   the Weierstrass model at the node, written as a closed subscheme of `ℙ^m_O` with the map from
   `Y` — explicit but heavy commutative algebra.

## 6. Interface findings (iut)

* `TemperedPi1Theory` receives only `[Field k]`. The tempered group depends on the valuation.
  A field has at most one henselian discrete valuation ring (F. K. Schmidt, formalized in
  `Setup/Schmidt.lean`), so a canonical choice exists (F2), but the interface would be more honest if
  it carried the valued-field structure of `K_v`.
* `tempPi1 X : Type u` forces a smallness argument: `Aut` of a fibre functor on a large category
  lives in `Type (u+1)`. The codes of §3.2/§3.4 make `𝒞` a `Type u` category, so `Aut Φ : Type u`
  without a `Small` argument. The sibling étale construction (`ProfiniteGrp.{u}`) needs the same
  kind of argument.
* `tempToEtale` goes to an arbitrary `Pi1.pi1`; a genuine map exists only for the genuine
  étale construction. The instance is therefore built against the sibling's `EtalePi1Theory`
  plus an identification `π₁^fin ≅ Pi1.pi1` (E1).

## 7. What `formal-schemes` would have to provide for a literally formal-scheme version

Generic fibres of admissible formal schemes (or at least the specialization map from
`Ω`-points), Grothendieck existence for proper formal curves, and normalization of formal
schemes. With those, `𝒯` in §3.2 could be replaced by an admissible formal model and `|𝒯_s|`
by `|𝒯|`; the rest is unchanged. The existing formal Tate model (a Néron 2-gon, period `q²`)
together with the covering `𝔾 → 𝔾/q^{2ℤ}` is precisely a level-`Y` object of §3.4 for
`E_{q²}` once algebraized; it is the natural input for G1.

## 8. Estimate

* A1–A3, B1–B3, C1, D1–D3: the definition, topology, comparison map — 2–4k lines. In progress.
* E1–E3: Galois-theoretic identifications — 4–8k lines.
* F1–F3: orbicurve presentation (translations on the coordinate ring are the main cost) —
  3–6k lines, shared with the étale π₁ work.
* G1: the `ℤ`-quotient for Tate curves — 10k+ lines (Galois theory of `𝒞`, explicit model).
* G2: not feasible without Berkovich geometry or the semistable reduction theorem for curves;
  it is a literature citation in this design.

## 9. Semistable reduction of finite étale covers of `E_q ∖ S` (the common blocker)

**What is needed.** Let `K` be a complete discretely valued field of characteristic `0` with
residue characteristic `p ≥ 0` (IUT: finite extensions of `ℚ_p`, `p = 2` allowed), `E_q` a Tate
curve, `S ⊆ E_q(K̄)` finite and Galois stable, `Y = E_q ∖ S`. Both the non-degeneracy witness
(§5.1, step 4) and André's identification (§4, steps 1–2) need:

> **(SSR)** for every finite étale `T → Y` there is a finite extension `K'/K` such that the smooth
> compactification `T̄_{K'}` has a semistable model over `O_{K'}` (in which the closure of the
> boundary `T̄ ∖ T` consists of disjoint sections in the smooth locus), and these models can be
> chosen compatibly with a given model of `Ȳ` (dominating the normalization of a model of `Ȳ` in
> `T̄`).

`T` is an arbitrary curve (arbitrary genus, arbitrary — in particular wild — ramification of
`T̄ → Ē_q` over `S`); no special structure of `Y` survives in `T` except that `Y` itself is a
Mumford curve. So (SSR) is the full semistable reduction theorem for curves, in the form
"(potential) semistable reduction of an arbitrary smooth projective curve over `K`", plus the
compatibility (which follows from the existence of the *stable* model and its functoriality,
Liu–Lorenzini).

### 9.1 Routes

| Route | Idea | Needs (not in Mathlib / our libraries) | Coverage |
|---|---|---|---|
| **Deligne–Mumford via Jacobians** (DM 1969, Grothendieck SGA 7 IX) | `C` has semistable reduction iff `Jac(C)` has semiabelian reduction; for abelian varieties inertia acts quasi-unipotently on `T_ℓ` (Grothendieck's monodromy theorem), unipotently after a finite extension | Jacobians (Picard scheme), Néron models (and Raynaud's `Pic⁰` of a regular model = identity component of the Néron model), `ℓ`-adic cohomology/Tate modules of Jacobians, Grothendieck's orthogonality/criterion | complete; the heaviest by far |
| **Artin–Winters** (Liu, *Algebraic Geometry and Arithmetic Curves*, Ch. 10) | take a regular model (Lipman desingularization of excellent surfaces), base change by a tame extension of degree `N` (`N` divisible enough), resolve again; the combinatorics of intersection matrices of fibres forces semistability after finitely many steps (uses a bound on the multiplicities via `g`) | Lipman's resolution of 2-dimensional excellent schemes, intersection theory on regular arithmetic surfaces, Castelnuovo contraction, adjunction; in residue char `p` the wild part uses the `p`-rank bound | complete (char-0 generic fibre); very heavy |
| **Temkin / valuation-theoretic** (Temkin, *Stable modification of relative curves*, 2010; also Ducros, Baldassarri–Poineau) | work over `C = K̄^`: the curve's Berkovich/Zariski–Riemann space; the genus formula `g = Σ_x g(x) + b₁(Γ) + …` over type-2 points; finiteness of points with positive residue genus; the `stability` of `C` (Grauert–Remmert: complete algebraically closed fields are *defectless*) gives that finitely many type-2 points carry all genus; a semistable vertex set exists; descend to a finite `K'` | defectlessness (stability) of complete algebraically closed fields, reduction of type-2 points (residue curves of divisorial valuations of `K̄(C)`), Riemann–Hurwitz for residue curves / genus inequality, Berkovich skeleta or Zariski–Riemann spaces | complete; mostly valuation theory + curves over fields — no arithmetic surfaces |
| **Coleman; Liu's "via stable models of covers"** | reduce to covers of `ℙ¹`, analyse by wide opens / residue-disc covers | rigid analytic geometry (wide opens), Coleman's `p`-adic integration-level analysis | complete; needs rigid geometry |
| **Lehr–Matignon, Obus–Wewers, Rüth (Mac Lane valuations)** | explicit semistable reduction of cyclic `p`-covers / superelliptic curves via inductive valuations | Mac Lane's inductive valuations, explicit Newton-polygon computations | only special covers (cyclic, superelliptic) — not all `T` |
| **Tame route** (Raynaud; Grothendieck–Murre; Liu Prop. 10.4.xx; Saïdi) | if `T → Y` has degree prime to `p`, the normalization of a semistable model of `Ȳ` (marked at `S`) in `T̄`, after the tame base change `π ↦ π^{1/m}`, is semistable: locally it is the normalization of a node `uv = π^n` or of a smooth point in a Kummer extension `u^{1/m}` — toric computations (Abhyankar's lemma) | normalization of explicit toric rings, Abhyankar's lemma, Zariski–Nagata purity for the smooth locus, the tame specialization theorem (SGA 1 XIII) to know `T` is Kummer-like at the nodes | only covers of degree prime to `p` (enough for the pro-`p'` tempered group of Mochizuki, **not** for André's full group) |
| **Mumford-curve specific (Schottky)** | `Y^an = (𝔾_m ∖ …)/q^ℤ`; covers `T` that are topological or have good reduction are explicit | Schottky uniformization of `Y` | only topological covers and "good" finite covers; a general `T` is not a Mumford curve, so this does not give (SSR) |

### 9.2 Assessment and plan

* No route avoids a large development. The **tame route** is the only one whose inputs are
  concrete commutative algebra; it gives (SSR) for `p ∤ deg(T/Y)` (and suffices for the
  pro-`p'` tempered group and for Mochizuki's combinatorial description), and is a sub-step of
  every other route (all of them finish by a tame base change). The **Temkin route** is the most
  plausible complete route in the long run: it needs valuation theory of function fields of curves
  (residue curves of divisorial valuations, defectlessness of `C_p`), which fits Mathlib's
  existing valuation library and the `ValuationSubring` machinery already used here, and no
  arithmetic surfaces, Néron models or rigid geometry.
* Implementation starts with the **local tame lemma** (common to the tame and Temkin routes):
  over a normal domain `O'` with `ϖ ∈ O'`, the integral closure of the node
  `O'[u, v]/(uv − ϖ^{mn})` in the Kummer extension obtained by adjoining `w` with `w^m = u` is
  the node `O'[w, z]/(wz − ϖ^n)` (`z = v^{1/m} = ϖ^n / w`), and the analogous statement at a
  smooth point `O'[u]` with the branch divisor `u = 0`. Status: **proved** for `O'` an
  integrally closed domain and `ϖ^n` replaced by any `c ≠ 0` (`SemistableReduction/Node`,
  `NodeNormal`, `TameLocal`: `Node.kummer_isIntegralClosure`, `smoothKummer_isIntegralClosure`).
* Order after that: (i) Abhyankar's lemma for DVRs (tame extensions become unramified after
  adjoining roots of the uniformizer) — **proved** (`SemistableReduction/RootOfUniformizer`,
  `RootOfUnit`, `AbhyankarLocal`, `Abhyankar`): for `O` a DVR, `L/K` finite separable, `B` the
  integral closure, tame at every maximal ideal with `e(𝔓) ∣ e`, `e ∈ O^×`, and `F = L[y]`,
  `y^e = ϖ`, the integral closure `B'` of `O` in `F` is étale over the DVR
  `O' = O[Y]/(Y^e − ϖ)` (`Abhyankar.etale`; also `isUnramifiedAt`, `ramificationIdx_eq_one`,
  `maximalIdeal_atPrime_eq_span`). No henselization: at `𝔔 | 𝔓`, `ϖ = uπ^n` in `B_𝔓`,
  `z = y^m/π` has `z^n = u`, and `B_𝔓[y, z] mod y` is a quotient of `κ(𝔓)[X]/(X^n − ū)`
  (`Abhyankar.maximalIdeal_eq_span_and_isSeparable_of_pow_eq`). Also for the whole base change:
  the integral closure of `O'` in `L ⊗_K K' = L[Y] ⧸ (Y ^ e − ϖ)` (and in any reduced finite
  `L`-algebra generated by a root of `ϖ`) is étale over `O'`
  (`SemistableReduction/AbhyankarProduct`: `Abhyankar.etale_integralClosure`,
  `etale_integralClosure_adjoinRoot`; via `IsArtinianRing.equivPi` and `integralClosurePiEquiv`);
  (ii) normalization of a semistable model in a tame cover is
  semistable after tame base change (local-to-global via the `ModelCode` framework and Mathlib's
  relative normalization). Status of the ring-level layers: (a) **done**
  (`SemistableReduction/LocalModel`): `IsEtaleLocallyAt O M 𝔭` (common étale neighbourhood),
  `IsSemistableAt ϖ 𝔭` (étale-locally `Node O (ϖ ^ n)` or `O[u]`), `IsSemistable`; the models are
  semistable, semistability ascends along étale maps (`of_etale`, via
  `exists_isPrime_tensorProduct`) and descends from étale neighbourhoods; (b) **done**
  (`SemistableReduction/EtaleBaseChange`): for `A → A'` étale and `B` the integral closure of `A`
  in `L`, `A' ⊗_A B` is the integral closure of `A'` in `A' ⊗_A L`
  (`isIntegralClosure_tensorProduct`, from Mathlib's smooth base change of integral closures);
  (c) the local structure of a tame cover at a node / on the branch divisor is to come from the
  valuative route (no Kummer/tame-purity hypothesis is introduced); (iii) defectlessness of `C_p`-type fields and residue curves of
  divisorial valuations (Temkin route); (iv) the genus formula and finiteness of type-2 points of
  positive genus; (v) (SSR).

### 9.3 The wild case: choice of route and lemma-level blueprint

**Choice.** Deligne–Mumford needs Jacobians, Néron models, Raynaud's `Pic⁰` theorem and
`ℓ`-adic cohomology of abelian varieties: several independent libraries, none started. The
"cover-specific" routes (Lehr–Matignon, Obus–Wewers, Raynaud's `p`-cyclic analysis) only treat
special Galois groups; an induction along a solvable filtration fails because Galois groups of
covers of `E_q ∖ S` are arbitrary finite groups (every finite group occurs over `K̄(E)`), and
already the `ℤ/p` step needs the full degeneration-data theory. We therefore follow the
**valuative route** (Temkin, *Stable modification of relative curves*, J. Alg. Geom. 2010; Ducros;
Baldassarri–Poineau; exposition: Temkin's "Topological transcendence degree"), in the form
"semistable vertex sets" (Baker–Payne–Rabinoff, *On the structure of non-archimedean analytic
curves*, 2013) transported to valuation language. Everything is valuation theory of the function
field `F = C(T̄)` of a curve over `C = \widehat{K̄}`, plus the model/valuation dictionary.

Notation: `C` complete algebraically closed, `O_C`, `k = O_C/𝔪` (algebraically closed);
`F/C` a function field of one variable. A **type-2 valuation** of `F` is a valuation `w`
extending `v_C` with value group `|C^×|` and residue field `κ(w)` of transcendence degree 1
over `k` (a function field of a curve over `k`, the **residue curve** `C_w`).

| # | Statement | Remarks / inputs |
|---|---|---|
| W1 | Gauss valuations on `C(x)`: `w_{a,r}(Σ c_i (x−a)^i) = min (v(c_i) + i·r)`, `r ∈ v(C^×)`; they are valuations with residue field `k(x̄)` | explicit; Mathlib has `Polynomial` Gauss norms over normed fields |
| W2 | Every type-2 valuation of `C(x)` is a Gauss valuation `w_{a,r}` | uses: `C` algebraically closed (factor into linear factors) |
| W3 | (**Abhyankar inequality**) for any valuation `w` of `F` extending `v_C`: `trdeg_k κ(w) + rank_ℚ(Γ_w/Γ_C) ≤ 1` | Mathlib-level valuation theory; residue transcendence bounded by the transcendence degree |
| W4 | (**Stability / defectlessness**, Grauert–Remmert) for a finite extension `F'/F` and a type-2 valuation `w` of `F`: `Σ_{w'|w} [κ(w'):κ(w)]·e(w'|w) = [F':F]` | the key analytic input; proof via the `C`-Banach space `F' ⊗ \hat F_w` having an orthogonal basis — Temkin gives an algebraic proof using W2 + Hensel |
| W5 | Model/valuation dictionary: a normal proper `O_C`-model `𝒞` of `T̄` ↔ the finite set of type-2 valuations given by the generic points of `𝒞_s` ("vertex set"); every finite set of type-2 valuations containing a nonempty set is the vertex set of a unique normal model | Bosch–Lütkebohmert; algebraic: normalize a model in which the valuations are divisorial. **Formalized** as Zariski models (§9.6): joins of Gauss lines and their normalizations (M1–M6 proved) |
| W6 | Genus formula: for a finite vertex set `V`, `g(T̄) = Σ_{w ∈ V} g(C_w) + b₁(Γ_V) + (contributions of the complement)`, and `Σ_{w type 2} g(C_w) ≤ g(T̄)`; hence only finitely many `w` have `g(C_w) > 0` | Riemann–Hurwitz for the residue curves + W4 (for `F/C(x)` of degree `d`, `Σ_{w'|w_{a,r}}` of residue degrees `= d`) |
| W7 | (**Semistable vertex set**) there is a finite `V` containing all `w` with `g(C_w) > 0` such that every "connected component of the complement" is an open disc or annulus; in valuation language: every type-2 `w ∉ V` has residue curve `ℙ¹` and at most two "directions" towards `V` | W2 + W6 + a local analysis of residue curves of `F` over `w_{a,r}` via W4 |
| W8 | The model with vertex set `V` (W5) is semistable | local computation at nodes: the complement annuli give local rings `O_C[u,v]/(uv − c)` |
| W9 | Descent: the vertex set, the model and its semistability are defined over a finite extension `K'/K` | §9.8: D1–D3c proved (Gauss data, tree model + its semistability over a DVR, vertex sets of normalizations); D3d–e (residue fields, descent of semistability of normalizations) open |
| W10 | (SSR) for every finite étale `T → Y`, plus compatibility with a model of `Ȳ` (vertex sets pull back: the preimage of `V_Y` in `T̄` is contained in a vertex set of `T̄`) | W7 applied to `V ⊇ preimage` |

Realistic size: W1–W3 small/medium (weeks of agent time), W4 large (the heart; Temkin's
algebraic proof ~20 pages), W5 large (needs blow-ups or the `ModelCode`+normalization
dictionary), W6–W8 large, W9–W10 medium. Status: **W1–W3 proved; W4 proved in mixed characteristic** (`char C = 0`, residue characteristic `p`; §9.4, `SemistableReduction/GaussStability`); **W5: the valuative dictionary (M1–M6) and the semistable tree of `ℙ¹`s (M7) proved** (§9.6); normality and finite type of normalizations over a DVR (M8) proved; the scheme realization (M9) open.
dictionary), W6–W8 large, W9–W10 medium. Status: **W1–W3 proved; W4 proved in mixed characteristic** (`char C = 0`, residue characteristic `p`; §9.4, `SemistableReduction/GaussStability`). **W6 proved** (§9.5): Riemann–Roch spaces and genus (Part R); the genus reduction inequality `Σ g(κ(wᵢ)) ≤ g(F)` for finitely many distinct type-2 valuations and the finiteness of positive-genus type-2 points (`SemistableReduction/TypeTwo`), with the `b₁` refinement over one Gauss point (`SemistableReduction/GenusBetti`).
* W1 (`SemistableReduction/Gauss.lean`): `gauss v a r : Valuation K[X] Γ₀` (multiplicative
  convention, `w(Σ cᵢ(X−a)ⁱ) = max v(cᵢ)·rⁱ`, Gauss lemma `Gauss.sup_mul`), `gaussRat v a r` on
  `RatFunc K` extending `v`; for `v c = r` the residue of `(X − a)/c` is transcendental over
  `κ(v)` (`transcendental_residue_gaussGen`) and generates `κ(w)` (`adjoin_residue_gaussGen_eq_top`).
* W2 (`SemistableReduction/GaussClassification.lean`): `eq_gaussRat` — `K` algebraically closed,
  `w` on `K(X)` with `w|_K = v`, value group `v(K^×)`, `κ(w)` transcendental over `κ(v)` ⇒
  `w = gaussRat v a r`.
* W3 (`SemistableReduction/AbhyankarInequality.lean`): `trdeg_residueField_le`
  (`trdeg_{κ(v)} κ(w) ≤ trdeg_K L` for any extension `w` of `v`), `exists_pow_eq_of_transcendental`
  (`trdeg_K L ≤ 1`, `κ(w)` transcendental ⇒ `Γ_w/Γ_v` torsion), `exists_eq_of_transcendental`
  (`K` alg. closed ⇒ `Γ_w = Γ_v`); `eq_gaussRat'` combines W2 and W3 (no value-group hypothesis).

### 9.4 W4: stability of Gauss-valued rational function fields

**Statement (W4).** `C` algebraically closed, complete for a rank-one valuation `v` (residue field
`k`, algebraically closed; value group `Γ_C` divisible), `F = C(x)`, `w = w_{a,r}` a Gauss
valuation with `r ∈ Γ_C` (after `x ↦ (x − a)/c` we may take `w = w_{0,1}`; residue field `k(x̄)`,
value group `Γ_C`). For every finite `F'/F`: `Σ_{w'|w} e(w'|w) f(w'|w) = [F':F]`. Since `Γ_C` is
divisible, `e(w'|w) = 1` for all `w'` (proved: `ramificationIdx_eq_one_of_divisible`), so W4 says
`Σ_{w'|w} [κ(w') : k(x̄)] = [F':F]`. The case `char k = 0` is Ostrowski's lemma (no defect in
residue characteristic 0); the IUT application (`C = \widehat{\bar K}`, `K/ℚ_p` finite) is the
**mixed characteristic** case `char C = 0`, `char k = p`, which is also the hardest.

**Route comparison.**

| Route | Core mechanism | Infrastructure it needs (Mathlib status) | Verdict |
|---|---|---|---|
| (i) BGR §5.3.2 (Grauert–Remmert, Gruson) | weakly cartesian normed spaces over `C⟨X⟩`, Weierstrass division, "stable" normed fields, `\widehat{Q(T_n)}` | Tate algebras, Weierstrass preparation/division, cartesian/weakly cartesian normed spaces, orthogonal bases (none in Mathlib) | a second library (affinoid algebra theory) before the proof starts; rejected |
| (ii) Temkin, *Stable modification* §4 ("critical cosets" `b + S_{a,s}`) | reduce a defect to an immediate degree-`p` extension of a finite moderately ramified extension; normal form `T^p − aT + b` (both characteristics at once); orthogonal *Schauder* bases `{1} ⊔ U ⊔ U^p ⊔ …` built over a discretely valued `k₀ ⊂ C` with `k̃₀ = k`; closed discs in `𝔸^{1,an}` | Berkovich discs (can be replaced by root estimates + Krasner, which Mathlib has), perturbation lemmas `epsclose`/`fin`, Schauder bases of Banach spaces over a DVR, `\hat⊗`, moderately ramified closure | uniform in the characteristic, but analytic (completed tensor products, Schauder bases); rejected as primary, its critical-coset formulation is kept as a fallback for step F |
| (iii) Kuhlmann, *Elimination of ramification I* (TAMS 2010) §§2–5 | henselized function fields; Galois degree-`p` steps; normal forms of Artin–Schreier (char `p`) and Kummer (char 0) extensions in terms of a lifted *Frobenius-closed basis* of the residue function field (LFC); "inertially generated" fields and change of generator | valuation theory only: henselization, ramification field, Galois theory, Hensel's lemma; no analysis | algebraic, matches our `Valuation`/`ValuationSubring` setting; **chosen**, specialised to `K = C` algebraically closed, rank one, residue-transcendental |
| (iv) Ohm (1983/89), Matignon–Ohm | deduced from BGR 5.3.2 Prop. 3 | same as (i) | rejected |

**Choice and adaptations.** Kuhlmann's route restricted to the case needed here (`K = C`
algebraically closed of rank one, `F = C(x)`, `x` residue-transcendental), with two changes that
fit Mathlib better:

1. **Completion instead of henselization.** Mathlib has completions of valued/normed fields,
   the spectral norm (unique extension of the absolute value to algebraic extensions of a complete
   field), Krasner's lemma (`IsKrasner.of_completeSpace`) and approximation of monic polynomials
   over dense subfields (`Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_…`), but
   no henselization. In rank one the completion `\hat F` plays the role of `F^h` (Kuhlmann
   Lemma 2.3/Thm 2.8: `F^h ⊂ \hat F` dense, same finite extensions up to completion).
2. **Inertia group instead of absolute ramification field.** Kuhlmann reduces to degree-`p`
   steps inside `F^r` (needs: `Gal(F^sep/F^r)` is pro-`p`, and `d(E|F) = d(E.N|N)` for `N ⊂ F^r`,
   his [K6]). Here `Γ_F = Γ_C` is divisible, so tame = unramified, and for a finite Galois
   `N/M` it suffices that the inertia group `T` is a `p`-group and `N^T/M` is unramified
   (elementary Kummer argument, D2 below); the remaining extension is a tower of Galois
   extensions of degree `p` (`p`-groups are supersolvable). The base-change invariance is only
   needed for unramified `N`, where it is Hensel's lemma (D4).

Notation below: all valued fields have rank one; `M` henselian means the valuation ring is a
`HenselianLocalRing`; "defectless `L/M`" means `e·f = [L:M]` (unique extension).

**Lemma-level plan.** Sizes are rough Lean line counts.

*A. General valuation theory (route independent).* File `SemistableReduction/FundamentalInequality`.

| # | Statement | Status / API | Size |
|---|---|---|---|
| A1 | `valuation_sum_eq_sup`: `x₁…x_n ∈ O_w` with residues independent over `κ(v)` ⇒ `w(Σ aᵢxᵢ) = max w(aᵢ)` | **proved** (`Valuation.HasExtension`, `IsLocalRing.residue`) | done |
| A2 | `linearIndependent_mul`: residue-independent `xᵢ` and `πⱼ` with values in distinct classes mod `Γ_K` ⇒ `{πⱼ xᵢ}` `K`-independent; `ramificationIdx_mul_inertiaDeg_le`: `e·f ≤ [L:K]` | **proved** (`Subgroup.relIndex`, `Module.finBasis`) | done |
| A3 | `exists_pow_valuation_eq` (values of algebraic elements are torsion mod `Γ_K`), `ramificationIdx_eq_one_of_divisible(')` (`Γ_K` divisible ⇒ `e = 1`) | **proved** (`minpoly`, `pow_left_inj`) | done |
| A4 | towers: `e`, `f` multiplicative in `K ⊂ L ⊂ M`; defectless `M/K` ⇔ `M/L` and `L/K` defectless | **proved** (`SemistableReduction/DefectTower`: `ramificationIdx_tower`, `inertiaDeg_tower`, `defectless_tower_iff`) | done |
| A4' | finiteness for finite `L/K`: `f < ∞`, `e ≠ 0` | **proved** (`finite_residueField`, `ramificationIdx_ne_zero`) | done |
| A5 | distinct extensions of `v` to an algebraic `L` are incomparable; for the global statement: the extensions of `w` to `F'` are finitely many (`≤ [F':F]`) | **not needed**: B3 was done with the bijection; finiteness and `#{w'} = #{Pⱼ}` are `LocalGlobal.finite_extension`, `card_extension` | — |

*B. Global ↔ local (completion).* `F'/F` finite separable (in char `p` reduce first to the
separable case: `F'·F^{1/q} / F^{1/q}` is separable for `q` = inseparable degree, `F^{1/q} = C(x^{1/q})`
is again Gauss-valued with residue `k(x̄^{1/q})`, and sub-extensions of defectless extensions are
defectless by A2).

| # | Statement | API | Size |
|---|---|---|---|
| B1 | `\hat F` := completion of `(C(x), w)`: complete rank-one, `Γ_{\hat F} = Γ_C`, residue `k(x̄)` (dense subfield ⇒ same values and residues) | **proved** in general (`SemistableReduction/DenseCompletion`): for `j : A → B` with dense image into a non-archimedean normed field, `valueGroup_eq_of_denseRange`, `residueEquiv`; hence `ramificationIdx_eq_of_denseRange`, `inertiaDeg_eq_of_denseRange`; for `UniformSpace.Completion F`: ultrametric, nontrivially normed, `completion_valueGroup`, `completionResidueEquiv`; `Valuation.toAbsoluteValue` + `WithAbs` turn a real (e.g. Gauss) valuation into a normed field (`valuation_withAbs`) | done |
| B2 | `F' = F[X]/(P)`, `P = Π Pⱼ` over `\hat F` (distinct, separable); each `\hat F[X]/(Pⱼ)` with the spectral norm is complete, contains `F'` densely, so it is the completion `\hat F'_{wⱼ}` of `F'` at the induced valuation `wⱼ`; `e`, `f` agree | **proved** (`SemistableReduction/LocalGlobal`, any non-archimedean `F`, complete nontrivially normed `K ⊇ F` dense, `F'/F` finite separable): `factors`, `prod_factors`, `sum_natDegree_factors`, `Local K g` (spectral norm), `toLocal`, `denseRange_toLocal`, `extValuation`, `ramificationIdx_extValuation`, `inertiaDeg_extValuation` | done |
| B3 | `j ↦ wⱼ` is a bijection onto the extensions of `w` (kernel of `\hat F ⊗ F' → \hat F'_{w'}` is one `(Pⱼ)`; uniqueness of the extension of a complete rank-one valuation) | **proved**: `extensionEquiv : Factor F K F' ≃ Extension F F'` (extensions = real valuations of `F'` restricting to the norm valuation); surjectivity `exists_eq_extValuation` (complete `(F', w)`, extend `K →` completion by continuity, `spectralNorm_unique_field_norm_ext`), injectivity `extValuation_injective` (approximate a CRT idempotent by elements of `F'`) | done |
| B4 | **W4 from local stability**: if every finite extension of `\hat F` is defectless then `Σ_{w'} e f = Σⱼ deg Pⱼ = [F':F]` | **proved**: `finsum_ramificationIdx_mul_inertiaDeg` (hypothesis on the `Local K g`), `…_of_defectless`, `…_completion` (for `K = UniformSpace.Completion F`) | done |

*C. Hensel toolkit for complete rank-one fields.*

| # | Statement | Size |
|---|---|---|
| C1 | complete rank-one ⇒ `HenselianLocalRing O` (Newton iteration; Mathlib only has the `𝔪`-adic version, useless for dense value groups) | **proved** (`SemistableReduction/HenselComplete`: `henselianLocalRing` for any complete `IsUltrametricDist` normed field) |
| C2 | **proved** (`UnramifiedRoot`: `natDegree_le_inertiaDeg`, `unramified_of_root`; `SemistableReduction/Unramified`: `hensel_lift`, `unramified_of_root_separable` (root of a monic `q` with irreducible separable `q̄`, `[N:M] ≤ deg q` ⇒ `e = 1`, `f = [N:M]`, `κ_N/κ_M` separable, generated by `ȳ`), `exists_adjoin_eq_top_of_unramified` / `exists_unramified_generator` (conversely, `f = [N:M]` with separable `κ_N/κ_M` ⇒ `N = M(y)` with `y` a Hensel root of a monic lift of the minimal polynomial of a primitive `ȳ`), `exists_unramifiedClosure` (if the valuation rings of `N` and of all intermediate fields are Henselian: an intermediate `K` with `K/M` unramified, residue field = separable closure of `κ_M` in `κ_N`, containing every intermediate field `K'` with `f(K'/M) = [K':M]` and `κ_{K'}/κ_M` separable; this is also the uniqueness of unramified lifts inside `N`)). The existence of an unramified lift of an *abstract* finite separable `κ'/κ_M` (outside a given `N`) is not formalized (not needed: G2 only uses the closure inside `M`) | done |
| C3 | **proved** (`SemistableReduction/UniqueExtension`, for `K` complete non-archimedean with `u = NormedField.valuation`, `L/K` algebraic, `w` any extension of `u`): `valuation_le_one_iff` (`w x ≤ 1 ↔ ‖x‖_sp ≤ 1`, spectral norm; via the dominance lemma `not_aeval_eq_zero_of_dominant`), hence `valuationSubring_eq`/`isEquiv` (uniqueness of the extension), `valuation_algEquiv_apply` (`w ∘ σ = w` for `σ ∈ Aut(L/K)`); for `L/K` finite: `L` is complete for the spectral norm (Mathlib `spectralNorm.completeSpace`) and `henselianLocalRing_valuationSubring` (with C1); tower versions `henselianLocalRing_comap`, `valuation_algEquiv_apply'` for `K ⊆ M ⊆ N` (the Henselian/invariance hypotheses of C2, C4, D1–D3) | done |
| C4 | **proved** (`SemistableReduction/UnramifiedBaseChange`): `defect_eq_of_unramified` — for `M ⊆ E, N ⊆ P` finite with `P = E·N`, `N/M` unramified (`f = [N:M]`, separable residue extension) and Henselian valuation rings on `P`, `N` and the intermediate fields of `P/E`: `[E:M]·e(P/N)f(P/N) = [P:N]·e(E/M)f(E/M)`, i.e. `d(E/M) = d(E·N/N)`; `defectless_iff_of_unramified`. Key step `unramified_of_adjoin_simple_root`: `P = E(y)`, `ȳ` a simple root of `q̄` ⇒ `P/E` unramified with separable residue extension (Hensel root of the separable `minpoly ȳ` over `κ_E` plus uniqueness of simple Hensel roots, `mem_of_root_of_residue_mem`); no linear disjointness is needed | done |

*D. Reduction to Galois steps of degree `p`.*

| # | Statement | API | Size |
|---|---|---|---|
| D1 | **proved** (`SemistableReduction/Inertia`, hypothesis `hσ : ∀ σ x, w (σ x) = w x`, supplied by C3 `valuation_algEquiv_apply'`): `galAction` (`G = Aut(N/M)` acts on `O_N`), `residueHom : G →* Aut(κ_N/κ_M)`, `inertia u hσ` its kernel, `mem_inertia_iff` (`σ ∈ T ↔ ∀ x ∈ O_N, w(σx − x) < 1`); for `N/M` finite Galois `residueHom_surjective`, `normal_residueField` | `Ideal.Quotient.stabilizerHom_surjective`, `Algebra.IsInvariant` | done |
| D2 | **proved** (Kummer step `UnramifiedRoot.kummer_unramified`; `SemistableReduction/Inertia`: `notMem_inertia_of_orderOf_eq_prime`, `isPGroup_inertia` — if `Γ_M` is divisible and `M` contains a primitive `ℓ`-th root of unity for every prime `ℓ` invertible in `κ_M`, then `T` is a `ringChar κ_M`-group). The proof needs no Hensel: an element `σ ∈ T` of prime order `ℓ ≠ p` has an eigenvector `σθ = ζθ` (`minpoly_algEquiv_toLinearMap`), normalized to `w θ = 1` by divisibility, and `w(σθ − θ) < 1` forces `ζ̄ = 1`, contradicting `Σ ζ^i = 0`, `ℓ ≠ 0` in `κ_M` | `minpoly_algEquiv_toLinearMap`, `Module.End.hasEigenvalue_of_isRoot` | done |
| D3 | **proved** (`SemistableReduction/Inertia`): `isPurelyInseparable_residueField_fixedField` (`κ_N/κ_{N^T}` purely inseparable: D1 for `N/N^T` has trivial image, and a normal extension with trivial automorphism group has separable degree 1), `unramified_fixedField_inertia` (`e(N^T/M) = 1`, `f(N^T/M) = [N^T:M]`, `κ_{N^T}/κ_M` separable: `|Aut(κ_N/κ_M)| = [G:T] = [N^T:M]` is the separable degree of `κ_N/κ_M`, which equals that of `κ_{N^T}/κ_M` and is `≤ f(N^T/M) ≤ [N^T:M]`) | D1, `Normal.algHomEquivAut`, separable degree | done |
| D4 | **proved** (`SemistableReduction/PGroupChain`): `exists_normal_relIndex_eq` (a proper subgroup of a finite `p`-group is normal of index `p` in a larger subgroup; Sylow `exists_subgroup_card_pow_succ` + `normal_of_index_eq_minFac_card`), `exists_chain` (`H = H₀ ≤ H₁ ≤ ⋯ ≤ H_m = T`, `Hᵢ ◁ H_{i+1}` of index `p`) | `IsPGroup`, Sylow | done |

*E. Frobenius-closed bases of the residue function field* (`char k = p`, `k` algebraically
closed, `κ` a function field of one variable over `k`).

| # | Statement | Size |
|---|---|---|
| E1 | a "pole-order" function `‖·‖ : κ → ℕ` with `‖f+g‖ ≤ max`, `‖cf‖ ≤ ‖f‖` (`c ∈ k`), `‖f^p‖ = p‖f‖`, `‖f‖ = 0 ⇔ f ∈ k`: maximal pole order over the places of `κ/k` (needs: places are DVRs, only finitely many poles, a non-constant has a pole — Chevalley extension `ValuationSubring`) — shared with W3/W5/W6 (residue curves) | **proved** (`SemistableReduction/CurvePlace`: `IsCurveFunctionField`, `CurvePlace` = valuation subrings `≠ κ` containing `k`, `CurvePlace.isDiscreteValuationRing`, normalized `CurvePlace.valuation : Valuation κ ℤᵐ⁰`, `poleOrder`, `poleNorm` with `poleNorm_add_le`, `poleNorm_smul_le`, `poleNorm_pow`, `poleNorm_eq_zero_iff`; finiteness of poles is replaced by a uniform bound on pole orders, `CurvePlace.exists_valuation_le`: `ord_P(x − α), ord_P(x⁻¹) ≤ [κ : k(x)]` by the fundamental inequality) |
| E2 | (Temkin, Lemma `basislem`; Kuhlmann [K5, Thm 10]) there is `U ⊂ κ` with `B = {1} ⊔ U ⊔ U^p ⊔ U^{p²} ⊔ …` a `k`-basis of `κ` and `Span_k U ∩ κ^p = 0` (choose `U_n` lifting a basis of `V_n/V_{n−1}`, `V_n` = image of `{‖f‖ ≤ n}` in `κ/κ^p`; termination by `‖fᵢ‖ ≤ ‖f‖/pⁱ`); consequences: `Span U ∩ ℘(κ) = 0`, `Span U ∩ (κ^p + k) = 0` (Kuhlmann Lemma 4.8) | **proved** (`SemistableReduction/FrobeniusBasis`: structure `FrobeniusBasis k κ p` = family `u : ι → κ` with a `Module.Basis (Option (ℕ × ι)) k κ` given by `none ↦ 1`, `(i, q) ↦ u_q ^ p ^ i`, `eq_zero_of_eq_pow` (`Span u ∩ κ^p = 0`), `eq_zero_of_eq_pow_sub` (`Span u ∩ ℘(κ) = 0`), `eq_zero_of_eq_pow_add_algebraMap`, `u_notMem_pthPowers`; existence `IsFrobeniusNorm.nonempty_frobeniusBasis` for any `k` perfect with an abstract norm `IsFrobeniusNorm`, and `nonempty_frobeniusBasis` for function fields of one variable over algebraically closed `k` via `isFrobeniusNorm_poleNorm`; `℘`-part by the norm: `f = g^p − g ≠ 0` gives `p‖g‖ ≤ ‖g‖`) |

*F. Degree-`p` Galois extensions of inertially generated fields.* `M` is **inertially generated**
if `M` is a finite unramified extension of `\widehat{C(z)} ⊂ M` for some `z ∈ M` with `z̄`
transcendental over `k` (Kuhlmann §2.4). Then `Γ_M = Γ_C`, `κ_M/k(z̄)` finite separable.

| # | Statement | Size |
|---|---|---|
| F1 | (char 0) a discretely valued subfield `K₀ ⊂ C` with `v(K₀^×) = ℤ·v(p)` and residue field `k` (Zorn over such subfields: a maximal one has residue field `k`, since transcendental residues lift by A1, separable ones by Hensel in `C` + A2, purely inseparable ones by `p`-th roots in `C` + A2). In char `p` instead: a coefficient field `k ↪ C` (Teichmüller) and `κ_M ↪ M` by Hensel (Kuhlmann Lemma 4.10) | **proved** (char 0; `SemistableReduction/DiscreteCoefficients`): `exists_isDiscrete_residueSubfield_eq_top` (`K₀` with `‖K₀^×‖ ⊆ ‖p‖^ℤ`, `residueSubfield K₀ = ⊤`; Zorn from `ℚ`, `isDiscrete_bot`); general tools: `residueSubfield`, A1 over subfields `norm_sum_eq_sup'`, `isDiscrete_adjoin_of_transcendental`, `isDiscrete_adjoin_of_root` (the algebraic case needs no Hensel/separability: a lift of the minimal polynomial has a root near any lift, `exists_root_norm_sub_lt_one`), `isAlgClosed_residueField`. The char `p` variant (Teichmüller coefficient field) is not done (F3 skipped) |
| F2 | (LFC, Kuhlmann Lemmas 4.9–4.11) lift `B` of E2 to `𝓑 ⊂ M`: a valuation basis (orthonormal: `|Σ cᵦ b| = max |cᵦ|`, from A1) with `𝓑^p ⊂ 𝓑` whose `C`-span is dense in `M`; density from the discreteness of `K₀`/the coefficient field (iterating residue approximations converges) | **proved** (char 0; `SemistableReduction/InertiallyGenerated`): `IsInertiallyGenerated C z` (`‖z‖ ≤ 1`, `z̄` transcendental over `k`, `M` finite over `M₁ = genClosure C z` (closure of `C(z)`), `κ_M/κ_{M₁}` finite separable, `[M:M₁] ≤ [κ_M:κ_{M₁}]`); Gauss norm `nnnorm_aeval_eq`, `residueSubfield_genClosure` (`κ_{M₁} = k(z̄)`); **F2** `nonempty_liftedFrobeniusBasis` (`C` algebraically closed of char 0, `M` complete): `K₀` (F1) → `K₁ = K₀(z)` → Hensel lift `y'` of a primitive `ȳ` of `κ_M/k(z̄)` → `F₀ = K₁(y')` discrete with residue field `κ_M`; lifts `u_q ∈ F₀` of a Frobenius-closed basis (E2); density: `mem_topologicalClosure_of_isDiscrete` (`p`-adic expansion in `F₀`), `inv_mem_topologicalClosure` (closure of `C[F₀]` is a field), `M = M₁[y']` by A1 over `M₁` and the degree bound |
| F3 | **Artin–Schreier normal form** (char `p`, Kuhlmann Prop. 4.12): `E = M(ϑ)`, `ϑ^p − ϑ = a`; modulo `℘(M)` and elements of value `< 1` (Hensel) write `a = Σ cᵢuᵢ`, `uᵢ ∈ U` (push `c u^{p^i} ↦ c^{1/p} u^{p^{i−1}}`, `C` perfect); then the residue extension has degree `p` (inseparable if some `|cᵢ| > 1`, separable otherwise), so `E/M` is defectless | **skipped** (only needed for `char C = p`; the IUT case is char 0). The residue tests of F4 (`le_inertiaDeg_of_insep/_of_sep`, `irreducible_X_pow_sub_X_sub_C`) and the Frobenius-basis bookkeeping would carry over; missing: a coefficient field `k ↪ C` and `κ_M ↪ M` (char-`p` F1/F2) |
| F4 | **Kummer normal form** (char 0, `ζ_p ∈ C`, Kuhlmann Prop. 4.13 + Lemmas 2.10–2.12 on `p`-th roots of 1-units: `1 + b` is a `p`-th power if `v(b) > p v(p)/(p−1)`; substitution `X = γY + 1`, `γ^{p−1} = −p`): `E = M(ϑ)`, `ϑ^p = r·u`, `r = 1` or `r̄ ∉ κ^p`, `u = 1 + Σ cᵢuᵢ` in normal form; then `[κ_E : κ_M] = p`, so `E/M` is defectless | **proved** for any complete `M ⊇ C` (`C` algebraically closed) with a lifted Frobenius-closed basis (`KummerNormalForm.LiftedFrobeniusBasis`: `B` of E2, lifts `u_q`, dense `C`-span of `{1} ⊔ {u_q^{p^n}}`). `SemistableReduction/PthPower`: normed Hensel `exists_root`, Lemma 2.11 `exists_pow_eq_one_add`, Cor. 2.12 a/d `exists_eq_mul_pow`, `exists_eq_mul_pow_of_pow`. `SemistableReduction/KummerNormalForm`: Artin–Schreier irreducibility `irreducible_X_pow_sub_X_sub_C`; residue tests `le_inertiaDeg_of_insep`/`le_inertiaDeg_of_sep` (`χ = (ϑ−1)/t` root of a monic integral polynomial with reduction `X^p − w̄` resp. `X^p − X − w̄`); orthonormality `nnnorm_val` (A1); the procedure `phase1_step`/`phase1` (all `p`-th-power terms with `‖c‖ ≥ ‖p‖` removed at once, error contracts by `max ρ ‖p^{1/p}‖ < 1`, re-expanded by density — this replaces Kuhlmann's monomial bookkeeping, which does not apply to products of basis elements), `remove_const`, `phase2` (Cor. 2.12 d, induction on Frobenius depth), `visible_of_leading`, `exists_visible`; **F4**: `le_inertiaDeg_of_pow_eq` (`f ≥ p`), `defectless_of_pow_eq` (`e = 1`, `f = [E:M] = p`) |
| F5 | **(DP)** every Galois extension of degree `p` of an inertially generated `M` (and, in char `p`, every purely inseparable one: Kuhlmann Prop. 3.1) is defectless | F3/F4 | **proved** in char 0 (`SemistableReduction/KummerDefectless`: `defectless_of_isGalois`, `ramificationIdx_eq_one_and_inertiaDeg_eq`: for `C` algebraically closed of char 0 with `‖p‖ < 1`, `M` complete and inertially generated, `E/M` Galois of degree `p`, any valuation `w` on `E` extending the norm of `M`: `e = 1`, `f = [E:M] = p`; Kummer theory `exists_root_adjoin_eq_top_of_isCyclic` + F2 + F4). The char `p` and purely inseparable parts are not done (F3 skipped) |

*G. Assembly (Kuhlmann §5, residue-transcendental case).*

| # | Statement | Size |
|---|---|---|
| G1 | an inertially generated `M` has no proper immediate finite extension: for `E/M` immediate, `N` its Galois closure, `M₀ = N^T` (D3; unramified, so inertially generated with the same `z`); `d(E/M) = d(E·M₀/M₀)` (C4); `E·M₀ = N^H` with a D4-chain from `H` to `T`, the top step is Galois of degree `p` over `M₀` hence defectless (F5), so `d(E·M₀/M₀) < [E·M₀:M₀] ≤ [E:M]` | **proved** (char 0; `SemistableReduction/NoImmediate`, adapters in `SemistableReduction/NormedTower`; all fields normed, valuations `NormedField.valuation`): `IsGaussComplete C x` (`K` = closure of `C(x)`, `‖x‖ ≤ 1`, `x̄` transcendental; e.g. `genField C z`, `isGaussComplete_genField`); `isInertiallyGenerated_of_unramified` (a finite unramified `B/K` is inertially generated by `x`); `exists_norm_eq`/`exists_valuation_pow_eq` (values of inertially generated fields = values of `C`, via F2); wild step `eq_bot_of_isPurelyInseparable` (`M₀` inertially generated, `N/M₀` Galois with purely inseparable residue extension, `f(X/M₀) = 1` ⇒ `X = M₀`; D2 + D4 + F5); **G1'** `inertiaDeg_eq_finrank_of_isSeparable` (`K` Gauss-complete, `B/K` finite with `κ_B/κ_K` separable ⇒ `f(B/K) = [B:K]`: `B ⊆ K_T` because `K_T(B) ⊆ B(y)` (`y` a Hensel generator of `K_T/K`, C4 key step) has residues separable over `κ_K`, hence in `κ_{K_T}`, and the wild step applies over `K_T`, which is inertially generated); **G1** `finrank_eq_one_of_immediate` (any valuation `w` on `E` with `f(w/M) = 1`, via C3 `valuationSubring_eq`). The C4 base change is not needed (replaced by the residue-separability argument) |
| G2 | every finite `M/\hat F` is inertially generated: choose `z ∈ O_M` with `κ_M/k(z̄)` separable (a separating transcendence basis of `κ_M/k`, `k` perfect); `M` is finite over the closure `\widehat{C(z)}` of `C(z)` in `M` (take a dense function field `F_M ⊂ M` via Krasner + polynomial approximation and `z ∈ F_M`; the restriction of the valuation to `C(z)` is the Gauss valuation — W1/W2); `M` is immediate over the unramified closure `M'` of `\widehat{C(z)}` (C2, `Γ_M = Γ_C`), so `M = M'` by G1 | **proved** (char 0; `SemistableReduction/ChangeOfGenerator`): **G2** `exists_isInertiallyGenerated` (`M ⊇ C` complete, `‖z‖ ≤ 1`, `z̄` transcendental, `M` finite over `genClosure C z` ⇒ `∃ z'`, `IsInertiallyGenerated C z'`); `exists_transcendental_isSeparable` (separating element, from Mathlib's `exists_isTranscendenceBasis_and_isSeparable_of_perfectField` and a cardinality count of transcendence bases); `exists_isAlgebraic_adjoin_eq_top` (Krasner: `M = \widehat{C(z)}(θ)` with `θ` algebraic over `C(z)`, via Mathlib's approximation of monic polynomials over dense subfields, continuity of roots and `IsKrasner`, in the algebraic closure of `M` with the spectral norm); exchange `isAlgebraic_adjoin_of_isAlgebraic` and `isAlgebraic_adjoin_trans` (the algebraic matroid); `M` finite over `\widehat{C(z')}` since `\widehat{C(z')}(z, θ)` is complete, hence closed, and contains the dense `C(z, θ)`; then G1' |
| G3 | **local stability**: every finite `E/\hat F` is defectless — Galois closure `N`, `N^T/\hat F` unramified (D3), `N/N^T` a D4-tower of Galois degree-`p` steps whose bases are finite over `\hat F`, hence inertially generated (G2), hence defectless (F5); multiplicativity (A4) | **proved** (char 0; `SemistableReduction/LocalStability`): `IsGaussFinite C B` (finite over the closure of `C(z)`, `z̄` transcendental; passes to finite extensions, `IsGaussFinite.of_finite`); `exists_intermediateField_inertiaDeg_eq` (reduction step: `N^T ≠ B` unramified by D3, or else `Gal(N/B)` is a `p`-group (D2, with the values of `B` those of `C`) and the fixed field of a normal subgroup of index `p` (D4) is defectless by F5, `B` being inertially generated by G2); `inertiaDeg_eq_finrank_of_isGalois` (strong induction on `[N:B]`, the bases change along the induction); **G3** `ramificationIdx_eq_one_and_inertiaDeg_eq` (normed `L/K`) and `ramificationIdx_mul_inertiaDeg_eq` (any valuation `w` on `E/K` extending that of `K`), `K` Gauss-complete, via the normed Galois closure and A4 |
| G4 | **W4** = B4 + G3 | **proved** (char 0; `SemistableReduction/GaussStability`): `GaussField a r` (= `WithAbs w_{a,r}`, a nontrivially normed `C`-algebra), `isGaussComplete_genK` (its completion is Gauss-complete, generated by `(X − a)/c`, W1), `finsum_ramificationIdx_mul_inertiaDeg_eq_withAbs` (B4 `…_completion` + G3) and **W4** `finsum_ramificationIdx_mul_inertiaDeg_eq`: `C` algebraically closed, char 0, `‖p‖ < 1` (completeness of `C` is not needed), `v c = r`, `F'/C(X)` finite separable ⇒ `∑ᶠ w' : GaussExtension a r F', e(w'/w)·f(w'/w) = [F' : C(X)]` (sum over the real valuations of `F'` restricting to `gaussRat v a r`) |

**Estimate.** A ≈ 1.2k (0.6k done), B ≈ 1.7k, C ≈ 1.4k, D ≈ 1.1k, E ≈ 1.3k (E1 overlaps with
the residue-curve infrastructure W3/W5/W6), F ≈ 3.2k (F4, the mixed-characteristic Kummer normal
form, is the single largest and most delicate item), G ≈ 1.0k: **≈ 11k lines** in total, i.e.
of the order of the whole Abhyankar/tame development several times over. The critical path for
the IUT application is A → C → D → (E, F1, F2, F4) → G → B; F3 and the inseparable parts of B/F5 are
only needed for `char C = p`.

**Status. W4 is proved in mixed characteristic (the IUT case)**: G1–G4 (`SemistableReduction/NormedTower`, `SemistableReduction/NoImmediate`, `SemistableReduction/ChangeOfGenerator`, `SemistableReduction/LocalStability`, `SemistableReduction/GaussStability`; main theorem `GaussStability.finsum_ramificationIdx_mul_inertiaDeg_eq`). Only the equal-characteristic case (`char C = p`: F3, the inseparable parts of B/F5) remains open. A1–A3 proved (`SemistableReduction/FundamentalInequality`: `valuation_sum_eq_sup`, F (mixed characteristic, the IUT case) proved: F1 (`SemistableReduction/DiscreteCoefficients`), F2 (`SemistableReduction/InertiallyGenerated`, with the definition `IsInertiallyGenerated`), F4 (`SemistableReduction/PthPower`, `SemistableReduction/KummerNormalForm`), F5 (`SemistableReduction/KummerDefectless`); F3 (char `p`) skipped. Note for G2: `IsInertiallyGenerated C z` asks for `‖z‖ ≤ 1` with `z̄` transcendental over `k`, `[M : M₁] < ∞`, `κ_M/κ_{M₁}` finite separable and `[M : M₁] ≤ [κ_M : κ_{M₁}]` (`M₁ = genClosure C z`; `κ_{M₁} = k(z̄)` is `residueSubfield_genClosure`), stated with `DiscreteCoefficients.residueSubfield` for residue fields of subfields.
`linearIndependent_of_residue`, `linearIndependent_mul`, `ramificationIdx_mul_inertiaDeg_le`,
`exists_pow_valuation_eq`, `ramificationIdx_eq_one_of_divisible`); A4 proved (`SemistableReduction/DefectTower`); C1 proved (`SemistableReduction/HenselComplete`); E1 proved (`SemistableReduction/CurvePlace`); E2 proved (`SemistableReduction/FrobeniusBasis`). B1 proved (`SemistableReduction/DenseCompletion`); B2–B4 proved (`SemistableReduction/LocalGlobal`), for any non-archimedean normed field `F` and finite separable `F'/F`; A5 not needed. For the Gauss valuation take `F = WithAbs (gaussRat v a r).toAbsoluteValue` with `v = NormedField.valuation` of `C` (real-valued). Remaining in B for char `p`: the reduction of inseparable `F'/F` to the separable case. C2 proved (`SemistableReduction/UnramifiedRoot`, `SemistableReduction/Unramified`); C3 proved (`SemistableReduction/UniqueExtension`); C4 proved (`SemistableReduction/UnramifiedBaseChange`); D1–D3 proved (`SemistableReduction/Inertia`); D4 proved (`SemistableReduction/PGroupChain`). Layers C and D are complete; the Henselian and Galois-invariance hypotheses of C2/C4/D1–D3 are discharged over a complete base by C3 (`henselianLocalRing_valuationSubring`, `henselianLocalRing_comap`, `valuation_algEquiv_apply'`).

### 9.7 The W10 interface

**Targeted W10 statement: `Statement.StrongA`** (`SemistableReduction/StrongA.lean`). This is the
exact form that Theorem A (`andreEquiv`, branch `wp-andre`) consumes.

* **Inputs:** `K` complete discretely valued of characteristic `0` and **mixed characteristic**
  (`(p : O) ∈ 𝔪_O` for a prime `p`) with **perfect residue field**; `R` a smooth **domain** of dimension `1` (without
  equidimensionality the statement is false: `R = K[t] × K`);
  `B` finite étale over `R`; a finite group `G` acting `K`-linearly on `B`; finitely many
  `O`-models `c₀ i` with maps `j₀ i` over `O`.
* **Outputs:**
  * a finite Galois `K'/K`, with `O'` a DVR over `O` and a uniformizer `ϖ'`;
  * a semistable `c' : ModelCode O'`, and `c : ModelCode O` isomorphic to `c'` over `O`;
  * a scheme-theoretically dominant `j : Spec (K' ⊗ B) ⟶ c` over `O`;
  * a `G × Gal(K'/K)`-action on `c` over `O`, with `j` equivariant;
  * domination of the `c₀ i`, compatible with the `j₀ i`.
* **No x-line input:** the W10 proof builds a finite x-line internally, by Noether
  normalization (`exists_finite_aeval`, `Setup/NoetherLine.lean`).
* **`StrongComponent → StrongA`** is proved (`Statement.strongA_of_strongComponent`).

`Statement`, `Strong`, `Simultaneous`, `StrongComponent`, `HarmonicGeneral` and `HarmonicX` are
**untargeted**: they are kept for Theorem B, which is parked (Blueprint §10.3.7).

`SemistableReduction.Statement : Prop` (`SemistableReduction/Statement.lean`) is the exact form of
W10 targeted by the W-chain and consumed by §4 (André identification) and §5.1 (non-degeneracy):
for a henselian discretely valued `K` of characteristic `0`, a smooth affine curve `Spec R` over
`K` and a finite étale `R`-algebra `B`, there are a finite `K'/K` (valuation subring `O'` over
`O`, uniformizer `ϖ'`), a projective `O'`-model `c` (`ModelCode O'`) that is semistable
(`ModelCode.IsSemistable ϖ' c`: every point has an affine neighbourhood étale-locally a node or
`O'[u]`), and an open immersion `Spec (K' ⊗_K B) ⟶ c` over `Spec O'`. It is a definition only;
downstream branches may take `(h : Statement)` as a hypothesis **as an intermediate**; nothing
merged as genuine may depend on it until W10 is proved. Refinements of the statement (domination of
a given model, equivariance for `Aut_Y(T)`, compatibility in towers) will be added as further
named `Prop`s here when the consumers need them.

`Statement.Strong` (same file) adds the clauses requested by the André identification (§10 on
branch `wp-andre`): `K'/K` Galois; the semistable model as a projective `O`-model `c` (isomorphic
over `O` to the semistable `O'`-model); `j` scheme-theoretically dominant; an action of
`G × Gal(K'/K)` on `c` over `O` with `j` equivariant; domination of finitely many given models;
`dim` of the special fibre `≤ 1`. **W8′** (see below): for compatible
semistable models `𝒯 → 𝒯'`, node thicknesses `n_x/e(K''/K)`, the induced map of dual graphs is
harmonic (nodes to nodes or to points of components), `Y`-lengths `d_x·n_x` are preserved, and
every node of `𝒯'_s` on the image of a component `v` is hit by a node on `v`.

**W8′: harmonic maps of dual graphs** (branch `wp-w8prime`; consumer: Theorem B, B5).

*Dual graphs* (`SemistableReduction/DualGraph.lean`), read off on the special fibre
`Z c = specialFibre c.toSpec` of a `ModelCode`: vertices `components c` (maximal irreducible
subsets of `Z c`); edges the node points `IsNodePt c x` (in `Z c`, not étale-locally `O[u]`) with
thickness `IsNodeOfThickness ϖ c x n` (étale-locally `Node O (ϖ ^ n)`); incidence `x ∈ v`, walks
`Walk c` (`Joins`: self-loops only for nodes on a single component), cycles. Splitness
`IsSplit ϖ c` (`HasSplitNodes`: an étale node chart at a point with residue field `κ(O)`;
`HasGeomIrreducibleComponents`) makes this the geometric dual graph; it is an output of
`Statement.Strong`/`Statement.Simultaneous`. Local degrees `HasLocalDegree ϖ ψ x d`: étale-locally
`ψ^* u' = ε ϖ^a u^d`, `ψ^* v' = ε' ϖ^b v^d`.

*Statements* (`Statement.lean`): `ModelCode.IsHarmonic ϖ ψ` (finite `ψ`: thickness well defined
and `≥ 1`, a node of thickness `n'` maps to a node of thickness `d n'` or to a smooth point on one
component, components onto components, points over nodes are nodes), a clause of
`Statement.Simultaneous`; **`Statement.HarmonicGeneral`** (targeted; `ψ` finite on generic fibres
between split semistable models): (H1) every component over a branch at a node `x'` of
thickness `n'` starts a walk crossing `x'` to the other branch with `∑ dᵢ nᵢ = n'`; (H2) every
crossing walk has `∑ dᵢ nᵢ ≤ n'`; (H3) a node not over a node maps to a point of a single
component. `Statement.Harmonic` (finite `ψ`) and `Statement.Modification` (birational `ψ`) are
superseded and not targeted.

*Proof plan.*

| # | Statement | Status |
|---|---|---|
| H0 | **interfaces** `IsKummerAt` (tame: étale-locally a product of Kummer covers `u₁ = w^{dᵢ}` of the base node, coordinates unit multiples of the Zariski ones) and `IsAnnulusAt ϖ x y d 𝔭` (`AnnulusAt.lean`, shared with W7: étale-locally the singular point of `Node O (ϖ^n)` with `x = ε u'^d`, `y = ε' v'^d`) | **done** |
| H1 | `IsKummerAt.isAnnulusAt`: normalization commutes with étale base change (Mathlib `toIntegralClosure_bijective_of_smooth`) + local tame lemma (`Node.kummer_isIntegralClosure`, any `d`, incl. `p ∣ d`) | **proved** (`KummerNode.lean`) |
| H2 | `IsAnnulusAt.thickness_eq`: `x y = ϖ^N` ⇒ `N = d n`, `n ≥ 1` (flatness of étale charts over the domain `Node`) | **proved** (`AnnulusThickness.lean`) |
| H3 | thickness well defined: `n = min {k : ϖᵏ ∈ J_𝔭}` for the ideal `J` generated by the coordinates of the relations among two minimal generators of `Ω_{A_𝔭/O}` (for `Node`: `J = (u, v)`, relation `v du + u dv`; `Ω` of an étale neighbourhood is the base change, `tensorKaehlerEquivOfFormallyEtale`; independence of the minimal generating pair over a local ring; faithful flatness of local étale maps) | planned, 0.6k |
| H4 | finite case at the Zariski level (W5 models): a point of the normalization over a node chart of the Gauss tree with `IsAnnulusAt` is a node of thickness `N/d`, over a node: the two branches map to the two branches; points over smooth points are smooth (`IsAnnulusAt` / smoothness from W7); components onto components (normalization of a Gauss tree: vertex set = preimage, M6) | planned, 0.5k |
| H5 | **targeted form `Statement.HarmonicW`** (superseded for B5 by `Statement.HarmonicX`, below) (W-models over one x-line, `WModel.lean`; two bases `O' ⊆ O''`, ramification `e`): the arbitrary-model `HarmonicGeneral` needs étale-local positions (fibre products of schemes), so it is untargeted. For W-models positions are global: `pos(W) = W(s)` for the base edge coordinate `s ∈ K(x)`; a node with `s = ε ϖ^α u^d` spans `[α, α + d n]` (`exponent_eq_of_chart`, `IsBranchNode.positions`), so (H2) is the telescoping inequality (`abs_sub_le_sum_of_branchNodes`, **proved** at valuation level, `ZariskiHarmonic.lean`); (H1) monotone walks by edge lifting (points of the normalization over base nodes are nodes, W7 (c); finiteness of `𝒳'_V → 𝒳_V`); (H3) from W7 (c). Input from W7's S9: `IsBranchNode` (node coordinates and the two branch vertices) at every point over a base edge | valuative core done; Zariski assembly planned, 1k |
| H6 | scheme transfer (M9b/M9c: `chartOpen`, `chartEquiv`, `exists_projModelCode_normalization`): node points / components / thicknesses / local degrees of `projModelCode` = those of the Zariski model; discharges `IsHarmonic` (`Simultaneous`) and `HarmonicW` | planned, 1.5k |

**`Statement.HarmonicX`: intrinsic x-lengths (targeted; supersedes `HarmonicW` for B5).**
`HarmonicW` does not serve Theorem B (B5): members of its index system come from independent W10
calls over incomparable bases `K₁`, `K₂`; lengths pulled back from a fixed base vanish on nodes
over smooth points (an annulus mapped by `z ↦ z + ϖ/z` into a disc); degree multiplicativity
would need its own clause. `HarmonicW` stays a targeted intermediate but is **superseded for
B5**. Instead every node gets an **intrinsic x-length** (`XLength.lean`, `XHarmonic.lean`; agreed
with the B5 consumer):

* *Definition (valuation-theoretic, W5 dictionary, no Berkovich spaces).* A node `y` of a model
  of `L` over `O'` with sections `u, v` near `y`, vanishing at `y`, `u v = ϖ'ⁿ`, at the germs
  `P = germs c j y ⊆ L` (`ModelCode.germs`: images of sections near `y`, the Zariski point),
  joins its two branches. Its *interpolating monomial valuations* are the `U_s ⊇ P`,
  `0 ≤ s ≤ n` rational, with `U_s(u) = U_s(ϖ')^s` and transcendental residue of
  `u^{den s}/ϖ'^{num s}` (`IsMonomialPt`; `U_0`, `U_n` the branches). Restricted to the x-line
  they are Gauss valuations `w_{a,r}` (W2; `IsXGauss`, centres `a` algebraic over `K'`, taken in
  `F̄ = AlgebraicClosure L` through extensions `U'_s` of `U_s`, so that folded paths turning into
  non-rational directions are covered), with normalised log radius `ρ` (`r = |ϖ₀|^ρ`,
  `v(ϖ₀) = 1` for the base `O`). **`λ` = total variation of `ρ` along `s ↦ U_s|K̄'(x)`** = sum of
  `|Δ log radius|` over the finitely many monotone pieces, folds included (in the x-tree every
  edge changes the radius, so path length = TV of the log radius). Formally `IsXLength … λ :=
  IsGreatest {∑ |ρ_{i+1} − ρ_i| : chains 0 = s₀ < … < s_m = n}` (`XChain`), on schemes
  `ModelCode.IsXLength ϖ₀ O' ϖ' c j x y λ`.
* *Proved* (`XLength.lean`, `XHarmonic.lean`): `IsLogValue.unique`, `IsXGauss.rho_unique` (the
  radius does not depend on the centre), `IsXLength.unique`, `IsXLength.nonneg`,
  `IsXLength.le_of_chain`, `IsXLength.abs_sub_le` (`λ ≥ |ρ(W₂) − ρ(W₁)|`), `germs_iso` (germs
  invariant under isomorphisms of models compatible with the generic points).
* *Statement* `Statement.HarmonicX`: `K` complete discretely valued, char `0`; `K₁`, `K₂`
  arbitrary finite over `K`; `c` a W-model of `L₁` over `O₁`, `c'` a W-model of `L₂ ⊆ L₁` over
  `O₂`, same x-line `x ∈ L₂`; `ψ : c ⟶ c'` over `Spec O`, `j ≫ ψ = Spec(L₂ → L₁) ≫ j'`; both split,
  semistable, `NoLoops`. Conclusion `ModelCode.IsHarmonicX`: (X0) every node of `c` has an
  x-length and it is `> 0`; (X1) for a node `y'` of `c'` on `w₁' ≠ w₂'` and every component `v`
  over `w₁'` a crossing walk (`Walk.Crosses`) from `v` to a component over `w₂'` with
  `∑ λ(xᵢ) = λ'(y')`; (X2) every such crossing walk has `∑ λ(xᵢ) ≥ λ'(y')`; (X3) a node not over
  a node maps to a point on exactly one component.

**Status: PARKED** (Theorem B is parked; `Statement.HarmonicX` is only needed if B resumes). What is
proved and what remains is recorded row by row below and in the following summary.

*Done* (wp-tempered-hx; XL1 on wp-w8prime):
* XL0, the definitions; XL1 `ModelCode.exists_nodeGerm` (W8′, wp-w8prime `WModelGerm.lean`);
* XL2 interior: uniqueness `NodeGerm.eq_of_isMonomialPt` (`MonomialUnique`), existence
  `NodeGerm.exists_isMonomialPt` (`MonomialExists`, flatness over the node + Chevalley);
* XL3/XL4 unfolded, ring level (`XGauss`, `XLengthUnfolded`): Gauss formula over `K̄` from residue
  transcendence (`valuation_aeval_eq_sup_of_residue`); Gauss centres minimise the distance, so the
  x-radius is centre independent across constant fields (`valuation_sub_le_of_residue`);
  `UnfoldedNodeGerm.isXGauss` (radius `(ord β + α + e s)/e₀`), `UnfoldedNodeGerm.isXLength`
  (`λ = e n / e₀`), `exists_isXLength_pos` (X0 at ring level);
* XL7 (`XHarmonicGlue`): `germs_map`, `map_genericPoint`;
* XL8 interior restriction (`XResidue`, `XLift`): `NodeGerm.isMonomialPt_comap` (monomial points
  of a node over a node restrict to monomial points at `(r + p s) f₂ / f₁`),
  `IsResidueTranscendental.of_algebraic` / `of_pow` / `comap`, `IsLogValue.comap`;
* XL6 partial (W8′, wp-w8prime `NodeBranches.lean`): `IsOrdinaryDoublePoint.eq_unit_mul_of_dvd`
  (the divisor lemma `t = ε ϖ^α w^e`), `dvd_of_branches`, `swap`.

*Remaining* (≈ 3–3.5k lines):
* XL6: the branch valuation subrings `D_{𝔔ᵢ}` with uniqueness of the endpoint monomial points, the
  residue conditions of `UnfoldedNodeGerm`, and the base coordinate `t ∈ P` from `IsUnfolded`
  (Gauss-chart combinatorics), ≈ 0.6k;
* XL5: invariance of `IsXLength` under `u ↦ ε u^k, n ↦ k n` and under `u ↔ v`, ≈ 0.3k;
* component glue (C1) (germs at the generic point of a component are a DVR with a `K'`-rational
  Gauss centre) and (C2) (the branches of a node are its components), ≈ 0.4k;
* X2 (XL9) scheme assembly: telescoping of radii along the walk (centre independence at the ends),
  ≈ 0.3k given the above;
* X1 (XL8) edge lifting: the walk construction (a point of a component over `y'` is a node; zeros
  of the residue of `u'^D/ϖ^N` on contracted components are nodes with higher position; positions
  increase strictly), ≈ 1.5–2k;
* X3 (XL10), ≈ 0.3k.

*Proof plan* (all statements about valuation subrings of `L₁ ⊇ L₂`; scheme ↔ Zariski via H6):

| # | Statement | Inputs | Status |
|---|---|---|---|
| XL0 | definitions, uniqueness, telescoping lower bound, `germs_iso`, `IsMonomialPt.param_unique`; `IsMonomialPt` requires `U(ϖ') < 1`; `IsWModel` requires `L / K'(x)` algebraic (`IsWModelOf`); **`ModelCode.IsUnfolded`** (every node over a node of the Gauss tree, W7 (c)) | — | **done** |
| XL1 | **Zariski node coordinates**: at a node `y` of a W-model with split nodes and no loops, `germs c j y` is a local subring `P ⊆ L` with `NodeGerm O' ϖ P u v n` (`n` the thickness, `u v = ϖⁿ` exactly), `ϖ, u, v ∈ 𝔪_P`, `u` transcendental over `K'`, `P` flat over the node via `(u, v)` (image in `O'[u, v]`), and `u, v` sections over an open `V ∋ y` vanishing at `y` (the `ModelCode.IsXLength` data): `ModelCode.exists_nodeGerm` (`WModelGerm`; W-model charts `exists_wChart`, `WModelChart`: charts of `projModel` generate `L`); ring level `exists_nodeGerm_of_split` (`NodeGermL`) from `exists_exact_node_of_split` (`NodeGerm`: ODP by descent from the étale chart, `NodeDescent`) and `flat_node_of_isOrdinaryDoublePoint`; no loops gives two minimal primes (`NoLoopsPrimes`). Branch valuation subrings `W₁, W₂` and their uniqueness (XL1 (c)/(d)) not done | H3, H6, S9 | **done** (except (c)/(d)); parked |
| XL2 | **monomial points exist and are unique** (interior `0 < s < n`): uniqueness `NodeGerm.eq_of_isMonomialPt` (`MonomialUnique`: monomial points restrict to Gauss points on `K[u]`, `valuation_aeval_eq_sup_of_monomial`, exponent form `gaussExp`; approximation `P = A + J_N` from `P = O + (ϖ, u, v) P`; lower bound from a polynomial relation over `K[u]`; no completions); existence `NodeGerm.exists_isMonomialPt` (`MonomialExists`: a Gauss point of radius one in `g = u^d/ϖ^m`, properness of `𝔪_P + 𝔪_{U₀}` in `P[O_w]` from flatness of `P` over the node by the equational criterion, Chevalley). Endpoints `s = 0, n`: the branches (XL1 (c)/(d)) | `NodeGerm` (XL1), Mathlib flatness, `LocalSubring` | **interior done**; endpoints from XL1 |
| XL3 | **piecewise linearity**: for `f ∈ K̄'(x)ˣ`, `s ↦ log U_s(f)` is continuous, piecewise linear with integer slopes and finitely many breaks (Laurent expansion `Node.laurent` in the étale node chart: `U_s(Σ αᵢ uⁱ + Σ βⱼ vʲ) = max(|αᵢ| |ϖ|^{s i}, |βⱼ| |ϖ|^{(n−s) j})`; alternatively S1 + S2 for the norm to `K'(u)`); hence `s ↦ U_s|K̄'(x)` is a path with finitely many monotone pieces, every `U_s` has Gauss data (W2 over `K̄'`), and the chain through the breakpoints attains the supremum: **existence of `λ`** | S1, S2, `Node.laurent`, W2 | planned, 0.5k |
| XL4 | **(X0) positivity**: the `U_s` are pairwise distinct (`U_s(u)` differ) and each Gauss point of `K'(x)` has at most `[L : K'(x)]` extensions (W4), so the path is not constant on any interval; by XL3 a path of constant radius is constant (`s ↦ U_s(x − a)` continuous with values `max(r, |a − a_s|)`), so `λ = 0` is impossible | XL2, XL3, W4 | planned, 0.2k |
| XL5 | **well-definedness on schemes**: two coordinate systems `(u, v, n)`, `(u', v', n')` at `y` with chains give the same path up to an affine reparametrisation (`u' = ε ϖ^β u^γ`; divisors supported on the two branches; non-genuine choices admit no chain), so the same `λ`; transport along isomorphisms over `O'` (`germs_iso` + `appLE` of the sections; requested by B5 for Galois objects carried through `e : c ≅ c'`) | XL1, XL2 | planned, parked (Theorem B parked). Analysis: a chain for `(u', v', n')` forces `(u', v', n') = (ε u^k, ε⁻¹ v^k, k n)` up to swap (a factor `ϖ` in `u'` leaves no monomial point at `s = 0`), so XL5 = invariance of `IsXLength` under `u ↦ ε u^k, n ↦ k n` (`s ↦ s / k`) and `u ↔ v` (`s ↦ n − s`); ring input `IsOrdinaryDoublePoint.eq_unit_mul_of_dvd` (`NodeBranches`) |
| XL6 | **unfolded nodes** (all nodes of W7-produced models, W7 (c)): a node over a node of the base Gauss tree (`IsBranchNode`, `x − a = ε ϖ^α u^d`) has monotone path = the base edge: `λ = d n / e(O'/O)` = position difference (`IsBranchNode.positions`, `exponent_eq_of_chart`) | ZariskiHarmonic, AnnulusThickness | ring level in progress, parked: divisors of powers of `ϖ` on the node are `ε ϖ^α u^e` or `ε ϖ^α v^e` (`IsOrdinaryDoublePoint.eq_unit_mul_of_dvd`, Krull on the branch DVRs `dvd_of_branches`; normality of `P` by faithfully flat descent `isIntegrallyClosed_of_faithfullyFlat`, `NodeBranches`). Open: the target `UnfoldedNodeGerm` (HX, `XLengthUnfolded`): branch valuation subrings and their uniqueness, residue transcendence, and `t = (x − a)/β ∈ P` with `ϖ^m / t ∈ P` from `IsUnfolded` (Gauss-chart combinatorics) |
| XL7 | **restriction commutes**: for `U` a valuation of `L₁`, `(U ∩ L₂)` restricted to `K(x)` is `U` restricted to `K(x)`; the generic point of a component `v` of `c` with `ψ '' v = w'` has valuation ring `W_v ∩ L₂ = W_{w'}` (local map of DVRs of `L₁ ⊇ L₂`; domination ⇒ equality) | `ZariskiNormalization.comap_*` | planned, 0.1k |
| XL8 | **(X1) lifting**: the monomial points `U'_s` of `y'` (in `L₂`) lift, starting from `W_v` over `W_{w₁'}`, to a path of valuations of `L₁` centred at points over `y'`: over each open interval the extensions centred at a fixed point of `c` vary continuously and do not branch (tube degree constant, S5, applied to `L₁ / K₂'(u')`); finiteness of `c → c'` on generic fibres gives finitely many pieces, each the monomial path of a node `xᵢ` of `c` (XL2 uniqueness) or a vertex (an inner component, contracted to `y'` since centred at `y'`); nodes distinct (monotone in `s`). `x`-images coincide (XL7), TV is additive under concatenation: `∑ λ(xᵢ) = λ'(y')` | XL2, XL3, XL7, S5 | planned, 0.8k |
| XL9 | **(X2) no shortening**: the concatenated monomial paths of a crossing walk restrict to a path `Γ` in the closed tube of `y'` from `W_{w₁'}` to `W_{w₂'}` (inner components and nodes are centred over `y'`); `s(U) = log_{|ϖ'|} U(u')` is continuous along `Γ` and every `U` with `s(U) = s` is `U'_s` or lies in a disc hanging at `U'_s` (attached only there), so `Γ` passes through `U'_{s₁}, …, U'_{s_m}` in this order for every partition; hence `TV(x ∘ Γ) ≥ ∑ d(x(U'_{sᵢ}), x(U'_{sᵢ₊₁}))` and `∑ λ(xᵢ) = TV(x ∘ Γ) ≥ λ'(y')`. For unfolded `y'` (XL6) this is just the triangle inequality for positions (`abs_sub_le_sum_of_branchNodes`) | XL3, XL7, `IsXLength.le_of_chain` | planned, 0.6k |
| XL10 | **(X3)**: `ψ y ∈ Z c'` (`ψ` over `O`); not a node ⇒ smooth; a point of `Z` lies on some component (Zorn, `exists_preirreducible` in the subspace `Z`) and a smooth point on at most one (minimal primes of `O_{Z,y}` inject into those of a local étale neighbourhood of `κ[u]`, a domain; flat ⇒ going down) | DualGraph, LocalModel | planned, parked (Theorem B parked) |

**Scope (decided):** `Statement.HarmonicX` assumes `ModelCode.IsUnfolded` for `c` and `c'` (W7 (c), to be
output by W10's component clause for B5); λ keeps the folded-inclusive definition. Then XL3 is the
monotone case of XL6 (`t = ε u^e ϖ^α` at the base node: `ρ(s)` linear, centre `K'`-rational, Gauss data
over `K̄` from residue transcendence of `t ^ d / ϖ ^ N`), X2 is the triangle inequality for the tree
distance of `K'`-rational Gauss points, X1 is monotone edge lifting. **Untargeted extension:** the
folded case (nodes over smooth points of the Gauss tree): piecewise linearity and continuity of the
restricted path over `K̄` (turning into directions not defined over `K'`), ≈ 2–3k lines.

**W10 clause (done in the statement).** `Statement.StrongComponent`'s component clause now outputs
`ModelCode.IsUnfolded O' x₁ c₁' j₁'` (x₁ the image of the input `x ∈ R` in `L₁`) in place of
`IsWModel` (recovered by `IsUnfolded.isWModel`). Obligation on the W7 side (targeted): `IsWModelOf`
from W9/M9c (`L₁ / K'(x)` algebraic from `R` finite over `K[x]`) and the node condition from W7 (c)
(smoothness over smooth points of the base Gauss tree). Consumers destructuring the old `IsWModel`
conjunct apply `.isWModel`.

Estimate: ≈ 3.7k lines on top of W7 S5/S6 and H6. Split: XL1, XL5, XL6, XL10 and the H6 glue on the
W8′ branch (`NodeDeformation.exists_node`, `eq_or_eq_of_isDiscreteValuationRing`, `NodeLemma`);
XL2–XL4, XL7–XL9 on `wp-tempered-hx`.
### 9.7a W10 assembly: `W7.Statement → Statement.StrongA` (owner: W10 assembler, O7)

Inputs of StrongA: `K`, `O`, `R`, `B`, `G` acting on `R` and `B`, the models `c₀ i`, `j₀ i`.

1. **x-line.** `exists_finite_aeval_invariant` gives a `G`-invariant `x` with `R` finite over `K[x]`.
   Then `B` is finite over `K[x]`, and `B ⊗_{K[x]} K(x) = Π F_k` with `F_k / K(x)` finite. This
   needs `R` equidimensional (open point A below).
2. **Fields.** `C = K̄` with the spectral norm (`UniqueExtension`). The components `F'_l` of the
   `F_k ⊗_{K(x)} C(x)` are permuted by `Gal(C/K)`.
3. **W7.** Apply it to the family `(F'_l)` with `V₀` the union of:
   * the discs from O9: the restrictions to `C(x)` of the residue-transcendental centres of the
     models `projModel f_i` attached to the `c₀ i` (`f_i` are the coordinates of `j₀ i`);
   * their `Gal(C/K)`-orbits.

   Equivariance makes the resulting `V` `Gal`-stable.
4. **Descent.** Take `E / K` finite Galois containing the tree data, with D3c, D3d and S7.9
   holding. Over `O_E`:
   * the node charts are semistable by O1 (`IsNodeODP ⇒ IsOrdinaryDoublePoint ⇒` S9);
   * smooth, generic-fibre and component-generic points by the W10 descent helper.

   The normalization `𝒳'_{V,E}` of the `E`-tree model in each component of `Π F_k ⊗_K E` is
   semistable, of finite type (M8b) and projective (M9c, `projModelCode`).
5. **Scheme.**
   * `c' := ModelCode.sigma` of the component codes over `O_E`; semistable by
     `isSemistable_sigma`.
   * `c` over `O` with `e : c ≅ c'` (`baseChangeIso`, componentwise).
   * `act` from `actOfDominates`/`actOfGenericPt`: `G` fixes `x`, so it preserves the charts;
     `Gal(E/K)` preserves `V`.
   * `dom i` from M10 (`dominates_of_vertexSet_subset`, with `hV` by step 3), `homOfDominates`,
     and the closed immersion `projModelCode f_i ↪ c₀ i`.
   * `j`: `B_E` is the integral closure of `E[x]` in `Π F_k ⊗ E`, i.e. the root chart of
     `𝒳'_{V,E}` with `ϖ` inverted. So `j : Spec(E ⊗ B) → c` is the open immersion of the generic
     fibre of that chart; it is scheme-theoretically dominant (W10Scheme).

Open points (decision by the lead):
* (A) **Resolved:** `[IsDomain R]` added to StrongA (and to `andreEquiv`).
* (B) **Resolved:** StrongA requires mixed characteristic. Equal characteristic `0` is an
  untargeted extension (§9.12, E1).
* (D) **Resolved:** StrongA requires a perfect residue field: closed points of special fibres are
  made rational by unramified extensions `E'/E`, and semistability descends along the étale
  `B_E → B_E ⊗ O_{E'}` (normalization commutes with smooth base change). Imperfect residue
  fields: untargeted extension (§9.12, E2).
* (C) The normed structures on `K` and `K̄` from the complete DVR `O`.

### 9.6 W5: models and vertex sets

**Formulation (decision).** Models are formalized *birationally*, as Zariski's abstract varieties
(Zariski–Samuel II, Ch. VI §17): a **Zariski model** of a field `F` over a subring `R ⊆ F` is a
finite set of *charts*, subrings `A ⊆ F` containing `R` (`ZariskiModel R`). Its points are the
local rings `localAt A W = A_{𝔪_W ∩ A}` of the charts at the centers of valuation subrings
`W ⊇ A` of `F` (every prime of `A` is such a center, Chevalley); two charts are glued along their
common local rings. This fits the existing infrastructure: `ValuationSubring` (W1–W4), ring-level
local models (`LocalModel.lean`: `IsSemistableAt` is a property of a chart at a prime), Mathlib's
`LocalSubring.ofPrime`, integral closures, and it needs neither gluing of schemes nor blow-ups.
Scheme-theoretic properties are replaced by their valuative criteria:

* *separated* (`IsSeparated`): a valuation subring dominates at most one point, i.e. for charts
  `A, B ⊆ W`, `B ⊆ localAt A W` (Zariski's irredundance = valuative criterion of separatedness);
* *proper* (`IsProper`): every valuation subring `W ⊇ R` of `F` contains a chart (existence part
  of the valuative criterion; with finite type and separatedness this is properness);
* *normal* (`IsNormal`): charts integrally closed in `F`; *finite type* (`IsFiniteType`);
  flatness over `O` is automatic (charts are torsion free subrings of `F ⊇ K`).

The **specialization** of a valuation subring `W ⊇ R` (in particular of a `K̄`-point composed
with an extension of `v`) is its center `ZariskiModel.center W = localAt A W` (any chart
`A ⊆ W`). Over a valuation subring `O ⊆ K ⊆ F` (base ring `baseRing F O`), the **vertex set** is
the set of *type-2* valuation subrings `W` of `F` over `O` (`W ∩ K = O`, residue field
transcendental over `κ(O)`) which are points of the model; for normal models of finite type over a
DVR the type-2 condition is automatic (dimension theory; not formalized, and not needed: all
vertices produced are type 2).

**Case needed.** M1–M6, M7a and M9a hold for an *arbitrary* valuation ring `O` (any rank,
discrete or not) and arbitrary `K`; no completeness, algebraic closedness or discreteness is used.
M7b, M7c and M8a (the explicit tree) assume `O` of rank at most one (both `O_C`,
`C = \widehat{\bar K}`, and discrete `O_{K'}` qualify); the semistability statement M7c uses
thicknesses `ϖⁿ` as in `LocalModel.lean` (so a DVR, or a fixed `ϖ` over `O_C`); M8b (finite type
of normalizations) assumes `O` noetherian, i.e. a DVR `O_{K'}` (after the descent W9).

| # | Statement | Status / API | Size |
|---|---|---|---|
| M1 | `localAt A W`; `localAt_le`, `localAt_mono`, `inv_mem_localAt`; **gluing lemma** `localAt_eq_of_le` (`A ≤ B ≤ localAt A W ⇒ localAt B W = localAt A W`); `localAt_eq_localSubringOfPrime` (= Mathlib's `LocalSubring.ofPrime A (𝔪_W ∩ A)`, `centerIdeal`); `ZariskiModel`, `points`, `IsSeparated`, `IsProper`, `IsNormal`, `IsFiniteType`, `center` (`center_eq`, `center_le`, `mem_points_iff`), `specialFibre`, `vertexSet` (`mem_vertexSet_iff`: type 2, `W ∩ K = O`, `center W = W`) | **proved** (`SemistableReduction/ZariskiModel`) | 0.35k |
| M2 | Gauss coordinates `IsGaussCoord v w y` (`F = K(y)`, `w(Q(y)) = max v(Qᵢ)`), stable under `y ↦ y⁻¹`; chart `O[y] = {Q(y) : max v(Qᵢ) ≤ 1}` (`mem_polyChart_iff`); `localAt O[y] O_w = O_w` (generic point); for nontrivial `v`, `O_w` is the *only* valuation subring over `O` that is a local ring of `O[y]` (`eq_of_localAt_eq`: at a closed point `q(y)` and `ϖ` are incomparable — Gauss lemma + irreducible factor); `line v y` = `ℙ¹_O` (charts `O[y], O[y⁻¹]`): proper, separated, finite type, `line_vertexSet = {O_w}`; `gaussModel v a c` for `w_{a,r}` on `K(X)` (`isGaussCoord_gaussCoord`) | **proved** (`SemistableReduction/GaussModel`) | 0.4k |
| M3 | compatibility with `Models/Specialization.lean`: for `X → Spec O` universally closed + separated and a chart `ι : Spec A ⟶ X` over `Spec O`, an `Ω`-point factoring through `ι` via `φ : A → V` specializes to `ι(φ⁻¹ 𝔪_V)` (`sp_eq_of_chart`); for `A ⊆ F`, `j : F → Ω`, `φ⁻¹ 𝔪_V = 𝔪_W ∩ A` with `W = j⁻¹ V` (`asIdeal_comap_closedPoint`), whose local ring is `localAt A W`. So on any scheme glued from the charts (M9), scheme specialization = `center` | **proved** (`SemistableReduction/ChartSpecialization`) | 0.1k |
| M3b | reduction of geometric points: a place `D ⊇ K` of `F` with `ρ : D → Ω` (residue embedding) and `V ⊆ Ω` over `O` give the composite valuation subring `ρ⁻¹(V)` of `F` over `O` (`compositeValuationSubring`, `comap_compositeValuationSubring`); its specialization is the reduction of the point; specializations of valuations over `O` lie in the special fibre (`center_mem_specialFibre`) | **proved** (`SemistableReduction/PointReduction`) | 0.1k |
| M4 | type 2: `IsResidueTranscendental O W z` (`P(z)` a `W`-unit for all `P ∈ O[X]` with `P̄ ≠ 0`) ⇔ `Transcendental κ(O) z̄` (`isResidueTranscendental_iff`, residue algebra via the local map `toVal : O → W`); **residue generation** `exists_isResidueTranscendental_of_localAt_eq(_of_isIntegral)`: if a type-2 `W` is the local ring of a chart `C` integral over the ring generated by `O` and `S`, some `s ∈ S` has transcendental residue (residues of `C` are algebraic over `κ(O)(S̄)`); `eq_of_isResidueTranscendental`: `W ∩ K = O` and `ȳ` transcendental ⇒ `W = O_w` (cf. W2, no algebraic closedness) | **proved** (`ZariskiModel`, `GaussModel`) | 0.25k |
| M5 | **joins** `iJoin M` (charts `R ⊔ ⨆ Aᵢ`; the closure of the diagonal in the product): proper, separated, finite type preserved; `lines v y` (join of `ℙ¹_O` in Gauss coordinates `y i`): **vertex set exactly `{O_{w i}}`** (`lines_vertexSet`); `gaussJoinModel v a c`: every finite family of Gauss valuations `w_{a i, r i}` of `K(X)` is the vertex set of a proper separated finite-type model (`gaussJoinModel_vertexSet`) — W5 (ii)+(iii) on `ℙ¹` | **proved** (`ZariskiModel`, `GaussModel`) | 0.2k |
| M6 | **normalization** in an algebraic `F'/F` (`normalization F'`, charts = integral closures `normChart F' A`): proper, separated, normal (`integralClosure_le_localAt` via `scaleRoots`; `map_localAt_le`); **Kaplansky's lemma** `mem_or_inv_mem_localAt`; **Prüfer** `localAt_normChart_eq` (the integral closure of a valuation ring `W` localized at the center of `W' ⊇ W` is `W'`); **vertex set of the normalization of a join of Gauss lines = the valuation subrings of `F'` over the given Gauss valuations** (`lines_normalization_vertexSet`, `gaussJoinModel_normalization_vertexSet`) — W5 (ii) in the form used by W7–W10 (a vertex set of `F'` is the preimage of a vertex set of `K(x)`) | **proved** (`SemistableReduction/ZariskiNormalization`) | 0.5k |
| M7a | **annulus model** (two concentric discs, the local model at an edge of the tree): charts `O[y⁻¹]`, the node `O[y, c/y]`, `O[y/c]`; proper, separated, finite type, vertex set `{O_{w₁}, O_{w₂}}` (`annulus_vertexSet`); `O[y, c/y] ≅ Node O c` (`range_nodeLift`, `nodeLift_injective` via `Node.laurent` and Laurent evaluation at the transcendental `y`), hence normal (`isIntegrallyClosed_nodeChart`); `O[z] ≅ O[X]`; for `c = ϖⁿ` every chart is semistable in the sense of `LocalModel.IsSemistable` (`annulus_isSemistable`); on `K(X)`: `gaussAnnulusModel` (`_vertexSet`, `_isSemistable`) | **proved** (`SemistableReduction/AnnulusModel`) | 0.5k |
| M7b | **general convex trees**: `DiscLE`, `IsConvex` (closed under joins `D(a,r) ∨ D(b,s) = D(a, max(r,s,|a−b|))`), `IsReduced`, root; for `O` of rank ≤ 1 every point of the join model of a convex family is the point of a **standard chart** — a line chart `O[t i]`, `O[(t ρ)⁻¹]` or a node chart `O[u, (c j/c m)/u]`, `u = (x − a j)/c m`, for `D j ⊊ D m` (`GaussTree.exists_standard_localAt_eq`, `center_lines_eq`, `gaussJoinModel_center_eq`). Proof: the discs containing `W` form a chain (`discLE_or_discLE_of_mem`), `m` = the smallest; the center is a node iff `W` lies in the residue disc of a child (the child of maximal radius contains all discs below `m` in that residue disc, by convexity: `discLE_of_residue`); the other coordinates are units or inverses of units of the local ring (affine relations L1–L4) | **proved** (`SemistableReduction/GaussTree`) | 0.7k |
| M7c | **the tree of `ℙ¹`s is semistable**: `A[1/e]` is a localization away (`awayChart`, `isLocalization_awayChart`, étale); charts of finite type with the same local ring at `W` have a common basic open `B[1/u] = C[1/u']` (`exists_awayChart_eq`), so `IsEtaleLocallyAt`/`IsSemistableAt` transfer (`isSemistableAt_of_localAt_eq`); primes of charts are centers (`exists_centerIdeal_eq`, Chevalley); standard charts are `≅ O[X]` / `≅ Node O ϖⁿ` (`polyChart_isSemistable`, `nodeChart_isSemistable`). **`gaussJoinModel_isSemistable`**: for a convex reduced family over `O` of rank ≤ 1 with thicknesses `c j / c m = ϖⁿ`, every chart of `gaussJoinModel` is semistable (`LocalModel.IsSemistable`) | **proved** (`SemistableReduction/ChartLocalization`, `GaussTreeSemistable`) | 0.45k |
| M8 | **normality and finite type**: conductor argument `mem_of_forall_mem_localAt` (normality is local, `isIntegral_mem_of_forall`); `O[z]` (Gauss coordinate) has fraction field `F` and is integrally closed (`≅ O[X]`, Mathlib's `IsIntegrallyClosed R[X]`), node charts too; **`gaussJoinModel_isNormal`** (convex, rank ≤ 1); for `O` noetherian (a DVR) and `F'/K(X)` finite separable, **`gaussJoinModel_normalization_isFiniteType`** (charts noetherian via `isNoetherianRing_of_fg`, integral closures finite by `IsIntegralClosure.finite`) | **proved** (`SemistableReduction/GaussTreeNormal`, `GaussTreeFinite`) | 0.35k |
| M9a | the **projective model** of a finite family of nonzero functions `f : ι → F` (`projModel`, charts `R[f j / f i : j]`, the standard opens of the closure of `Spec F → ℙ^ι_R`): proper, separated, finite type. Lines are `f = (1, y)`, joins of lines are Segre families | **proved** (`SemistableReduction/ProjModel`) | 0.1k |
| M9b | **scheme realization of `projModel f` as a `ModelCode`** (`f : Fin (m+1) → F` nonzero, `O → F` with image `R`, any ring `O`): `toProj O hf : Spec F ⟶ ℙᵐ_O` (on `D₊(x_i) = Spec (O[x]_{x_i})₀` the map `a/x_iⁿ ↦ a(f)/f_iⁿ`, `awayEval`; independent of `i`, `toProj_eq`; over `Spec O`, `toProj_toSpec`); `projModelCode O hf := ⟨m, (toProj O hf).ker⟩` (scheme-theoretic image = closure); the opens `chartOpen i = D₊(x_i)` cover it (`exists_mem_chartOpen`) and `Γ(chartOpen i) ≃ₐ[O] R[f j / f i]` (`chartEquiv`, from `range_chartHom'`, `chartHom'_injective`, `chartHom'_algebraMap`); `chartι : Spec R[f j/f i] ⟶` model, open immersion over `Spec O` (`chartι_toSpec`), through which the generic point factors (`toImage_eq_SpecMap_comp_chartι`). **Transfer**: charts semistable ⇒ `ModelCode.IsSemistable` (`projModelCode_isSemistable`); **specialization**: `sp` of the `Ω`-point `Spec Ω → Spec F →` model is `chartι` of the center `𝔪_W ∩ R[f/f_i]`, `W = j⁻¹V` (`sp_projModelCode`, with M3 `asIdeal_comap_closedPoint`, `localAt_eq_localSubringOfPrime`). Joins of lines are projective: `lines v y = projModel (segre y)` (`lines_eq_projModel`, Segre family `∏_{σ i} y i`) | **proved** (`SemistableReduction/ProjScheme`, `SegreModel`) | 0.7k |
| M9c | **normalizations of projective models are projective**: for the normalization `M'` in `F'` of `projModel O f` (`f` finite nonempty, nonzero) of finite type (M8b), explicit homogeneous coordinates `normCoord` (`f k f iᴺ`, `b f i^{N+1}` for generators `b` of the charts `B_i` of `M'`; degree shifting `exists_mul_pow_mem_normChart`: `b (f_i/f_j)^e ∈ B_j`, via `scaleRoots`) with chart at `f_j^{N+1}` *equal* to `B_j` (`projChart_normCoord`); `exists_projModelCode_normalization`: there is `g : Fin (n+1) → F'` with `charts M' ⊆ charts (projModel g)`, the same points (`points_projModel_eq`), and: charts of `M'` semistable ⇒ `projModelCode O g` semistable (`projChart_isSemistable_of_normalization` via M7c's `isSemistableAt_of_localAt_eq`). With `lines_eq_projModel` this applies to `gaussJoinModel` (`gaussJoinModel_eq_projModel`) | **proved** (`SemistableReduction/ProjNormalization`, `ProjNormalizationCode`) | 0.6k |
| M10 | **domination of models with nested vertex sets** (`ZariskiModel.dominates_of_vertexSet_subset`): over a DVR `O`, `trdeg_K F ≤ 1`, `X` separated, normal, of finite type with charts of fraction field `F`, `Y` proper of finite type (not necessarily normal, e.g. `projModel f`); if every `W` with `W ∩ K = O` whose center on `Y` has transcendental residue (`∃ z ∈ B ⊆ W`, `IsResidueTranscendental O W z`) is a vertex of `X`, then every point of `X` contains a chart of `Y`. Proof: Mathlib's algebraic Zariski main theorem for `A[s] ⊇ A = O_P` (`le_of_quasiFiniteAt`); otherwise a non-maximal prime of the closed fibre (`quasiFiniteAt_of_forall_isMaximal`) gives a generator with transcendental residue (`exists_forall_aeval_notMem_of_not_isMaximal`), hence a vertex valuation of `Y` centered at `P` (special fibre) or a contradiction with `trdeg ≤ 1` (generic fibre, `false_of_trdeg_le_one`). No dimension theory, no normalization of `Y`. Open: finiteness of the set of such `W` (needs Krull–Akizuki-type finiteness). The full W5 (every finite set of type-2 valuations is the vertex set of a unique normal model) remains unplanned | **proved** (`SemistableReduction/ModelDomination`) | 0.5k |

**Downstream API.** W6 (genus formula) sums over `vertexSet` of `normalization` of `gaussJoinModel`
(= the extensions of the Gauss valuations, M6; W4 counts them). W7 produces a finite set of Gauss
valuations of `K(x)`; M5/M6 give the model, M7 + the local analysis of W8 its semistability; W9
descends it; W10 turns it into a `ModelCode` (M9). The reduction map for points is `center`
(valuation-theoretic) and `sp` (scheme-theoretic), equal by M3.

**Estimate.** Done: M1–M8 ≈ 4k lines (the valuative dictionary, normalization, the semistable
normal tree of `ℙ¹`s, finite type of its normalizations over a DVR). So over a DVR `O_{K'}`: for a
convex family `V'` of Gauss points of `K(x)` and `F'/K(x)` finite separable, the normalization of
`gaussJoinModel` in `F'` is a normal proper separated Zariski model of finite type with vertex set
the valuations over `V'` (W5 (ii) in the form used downstream). M9b+M9c (≈ 1.3k) give the scheme/projectivity
bridge to `ModelCode`: a semistable normalization of a projective (e.g. Gauss-join) model is a
semistable `ModelCode`, with scheme specialization = Zariski center. The W8 local analysis can now reuse
M6 (local rings of the normalization = localizations of integral closures of the standard local
rings) and M7c (transfer from local rings to `IsSemistableAt`).

`Statement.Simultaneous` (same file): for a tower `B' / B / R` of finite étale algebras, semistable
`O'`-models `c` of `K' ⊗ B` and `c'` of `K' ⊗ B'` with a finite morphism `c' ⟶ c` compatible with
the open immersions (simultaneous semistable reduction; produced by W7 via preimages of vertex
sets and normalization, M6). Requested by W8′ (finite maps only: with contracted components the
length clause fails).
### 9.5 W6: genus

Notation: `k` algebraically closed, `κ / k` a function field of one variable
(`IsCurveFunctionField k κ`), `CurvePlace k κ` its places (E1). `C`, `O_C`, `k` as in §9.3,
`F / C` a function field of one variable; a **type-2 valuation** of `F` is a real valuation `w`
extending `v_C` whose residue field `κ(w)` is transcendental over `k` (then `Γ_w = Γ_C` by W3 and
`κ(w)` is finite over `k(x̄)` for any `x` with `x̄` transcendental, so `κ(w)` is a function field
of one variable over `k`).

**Part R: Riemann–Roch spaces and genus over an algebraically closed field** (Stichtenoth,
*Algebraic Function Fields and Codes*, §§1.3–1.4, specialised to `k` algebraically closed, where
every place has degree `1`). All proved.

| # | Statement | Status / API |
|---|---|---|
| R1 | **Weak approximation** for finitely many pairwise incomparable valuations (any `Γ`): `u` with `v_i(u) < 1 < v_j(u)` (induction, `y ↦ y + z^r` with `r` avoiding finitely many exponents), then `(1 + u^s)⁻¹` | **proved** (`SemistableReduction/WeakApproximation`: `Incomparable`, `exists_lt_one_and_one_lt`, `valuation_inv_one_add_pow`); for places: `CurvePlace.incomparable` (DVRs of Krull dimension 1), `exists_valuation_sub_one_lt_one`, `exists_valuation_eq_and_le` (prescribed order at `P`, high order at finitely many `Q`) |
| R2 | `κ` is finite over `k(f)` for every `f ∉ k`; the residue field of every place is `k` | **proved** (`SemistableReduction/CurveDivisor`: `IsCurveFunctionField.isAlgebraic_adjoin` (exchange lemma of G2), `IsCurveFunctionField.finiteDimensional_adjoin` (`EssFiniteType` + algebraic), `transcendental_of_notMem_range`, `CurvePlace.exists_valuation_sub_lt_one` (otherwise `k(f) ⊆ O_P`, hence `κ ⊆ O_P`)) |
| R3 | for `f ∉ k`: `∑_{P ∈ S} ord_P(1/f)^+ ≤ [κ : k(f)]` for every finite set `S` of places, so `f` has finitely many poles; divisors, pole divisor, principal divisor | **proved** (`CurvePlace.sum_poleOrder_le`: the `w_{P,j}` of R1 with `ord_P = j < e_P` and high order at the other poles are `k(f)`-independent, the coefficients having a common order at all zeros of `1/f` (`exists_zpow_of_mem_adjoin`); `finite_setOf_notMem`; `CurveDivisor k κ := CurvePlace k κ →₀ ℤ`, `deg = Finsupp.degree`, `poleDivisor k f`, `divisor k f = (1/f)_∞ − (f)_∞`, `valuation_eq_exp_neg_divisor`, `divisor_mul`, `divisor_inv`) |
| R4 | `L(D) = {f | v_P(f) ≤ exp (D P)}`, `ℓ(D) = dim_k L(D) < ∞`, `ℓ(D') ≤ ℓ(D) + deg(D' − D)` for `D ≤ D'`, `ℓ(0) = 1`, `ℓ(D + (z)) = ℓ(D)` | **proved** (`SemistableReduction/RiemannRoch`: `rrSpace`, `ell`, `exists_rrSpace_add_single_le` (step `D → D + P`, uses R2), `finiteDimensional_rrSpace`, `ell_le_ell_add_degree`, `ell_zero`, `rrSpace_zero`, `mem_rrSpace_iff_le`, `ell_add_divisor`) |
| R5 | `deg (x)_∞ = [κ : k(x)]` for `x ∉ k`; principal divisors have degree `0` | **proved** (`degree_poleDivisor`: `≤` is R3, `≥` from `(m+1)[κ:k(x)] ≤ ℓ(m(x)_∞ + ∑ (uᵢ)_∞) ≤ 1 + m·deg (x)_∞ + deg ∑(uᵢ)_∞` for a basis `u` (`card_mul_le_ell`); `degree_divisor`). No integrality or fundamental equality needed |
| R6 | genus `g = sup_D (deg D + 1 − ℓ(D))` is finite; **Riemann's inequality** `ℓ(D) ≥ deg D + 1 − g`; `g(k(x)) = 0` | **proved** (`riemannDefect`, `riemannDefect_mono`, `riemannDefect_add_divisor`, `riemannDefect_nsmul_poleDivisor_le` (bounded on multiples of `(x)_∞`), `exists_add_divisor_le` (every `D` is equivalent to a divisor `≤ m(x)_∞`, Stichtenoth 1.4.15), `bddAbove_riemannDefect`, `genus`, `riemannDefect_le_genus`, `riemann_inequality`, `exists_riemannDefect_eq_genus`, `genus_eq_zero_of_adjoin_eq_top`, `isCurveFunctionField_ratFunc`, `genus_ratFunc`) |
| R7 | `ℓ(D) = deg D + 1 − g` for `deg D ≥ c` (no canonical divisor needed: `g` is attained at some `D₀`, and `D ~ D' ≥ D₀` once `ℓ(D − D₀) > 0`) | **proved** (`ell_eq_of_le_degree`) |

**Part G: the genus reduction inequality** `Σᵢ g(κ(wᵢ)) ≤ g(F)` for distinct type-2 `w₁, …, w_n`.

*Choice of proof.* The inequality is `p_a(𝒳_s) = g(F)` plus `p_a(𝒳_s) ≥ Σ g(components)` for the
normalization `𝒳` of `ℙ¹_{O_C}` in `F` (for a coordinate `x` in which all `wᵢ` lie over the Gauss
point). We transport this to valuations and Riemann–Roch spaces of `F` and of the residue curves,
comparing `L(m(x)_∞)` with its reductions (Matignon, *Genre et genre résiduel des corps de
fonctions valués*, Manuscripta Math. 58 (1987); Green–Matignon–Pop, *On valued function fields
I*, §3). The analytic proofs (Baker–Payne–Rabinoff genus formula) presuppose semistable
reduction and are circular here.

| # | Statement | Proof / inputs | Status |
|---|---|---|---|
| G6.1 | (common coordinate) there is `x ∈ F` with `wᵢ(x) = 1` and `x̄` transcendental in every `κ(wᵢ)`; then `wᵢ|_{C(x)} = w_{0,1}` for all `i`, so the `wᵢ` are among the extensions `w'₁, …, w'_s` of the Gauss valuation, and it suffices to prove `Σ_{j ≤ s} g(κ_j) ≤ g(F)` | distinct type-2 valuations are incomparable (rank one), R1 for real valuations; A1 for `Σ cⱼ xʲ` | **proved** (`TypeTwo`: structure `TypeTwo C F`, `valuation_aeval_eq_sup` (A1), `TypeTwo.exists_val_eq` (W3), `TypeTwo.eq_of_le`/`incomparable`, `TypeTwo.exists_common_coordinate`, `coordAlgHom`, `comap_eq_gauss1`, `toExt`) |
| G6.2 | `e(w'_j) = 1`, `Σ_j f_j = N := [F : C(x)]`, `κ_j / k(x̄)` finite, `κ_j` a curve function field | W4 (`GaussStability`), A3, A4' | **proved** (`GaussFibre`: `ramificationIdx_eq_one`, `finite_ext`, `sum_inertiaDeg_eq`; `ResidueCurve.isCurveFunctionField`, `finrank_adjoin_red_x`, `transcendental_red_x`) |
| G6.3 | (orthonormal basis) `b₁, …, b_N ∈ F` with `‖Σ φᵢ bᵢ‖ = maxᵢ |φᵢ|_{Gauss}` for `‖·‖ = max_j w'_j` | lift `k(x̄)`-bases of the `κ_j`, separate the `w'_j` by R1; residues independent ⇒ norm is the max (A1 for several valuations) | **proved** (`GaussFibre.exists_orthonormal_basis`) |
| G6.4 | (reduction dimension) for every finite-dimensional `C`-subspace `V ⊆ F`, the image `ρ(V°) ⊆ ⊕_j κ_j` of `V° = {‖f‖ ≤ 1}` has `k`-dimension `dim_C V` | clear denominators (Gauss is multiplicative): `qV ⊆ ⊕ᵢ C[x]_{≤M} bᵢ ≅ (C^{N(M+1)}, max)`, reduced row echelon form with maximal-entry pivots gives an orthonormal basis. No completeness or spherical completeness of `C` needed | **proved** (`LatticeReduction.exists_orthonormal_pi`, `exists_orthonormal_submodule`; `GaussReduction.finrank_le_of_red_mem`) |
| G6.5 | (integrality) `f` integral over `C[x]` with `‖f‖ ≤ 1` ⇒ `f` integral over `O_C[x]` ⇒ `f̄_j` integral over `k[x̄]`; the same at `∞`; hence `ρ(L(m(x)_∞)°) ⊆ W_m := ⊕_j L_{κ_j}(m(x̄)_∞)` | conjugates of `f` in a normal closure: `W(σf) = (W∘σ)(f) ≤ 1` since `W∘σ|_F` is some `w'_j` | **proved** (`ResidueCurve.red_mem_of_isIntegral` via the characteristic polynomial in the orthonormal basis instead of normal closures; `InfinityChart.red_mem_of_isIntegral_inv`; `GenusCount.red_mem_rrSpace`) |
| G6.6 | (counting) for `m ≫ 0`: `dim ρ(L(m(x)_∞)°) = mN + 1 − g`, `dim W_m = mN + s − Σ g_j`; hence `Σ g_j ≤ g + (s − 1) − codim_{W_m} ρ(L(m(x)_∞)°)`, in particular the **weak inequality** `Σ_j (g_j − 1) ≤ g − 1` | G6.4, G6.5, R5 (`deg (x)_∞ = N`, `deg (x̄)_∞ = f_j`), R7 on `F` and on each `κ_j` | **proved** (`GenusCount.ell_le_sum_ell`, weak inequality `sum_genus_le_add_card`) |
| G6.7 | (gluing conditions) for places `Q ∈ κ_j`, `Q' ∈ κ_{j'}` centred on the same maximal ideal of `𝓡 = ` integral closure of `O_C[x]` (resp. of `O_C[1/x]`, evaluating `f/xᵐ`), `f̄_j(Q) = f̄_{j'}(Q')` on `ρ(L(m(x)_∞)°)`; the conditions along a spanning forest of the incidence graph `Γ` (components, closed points of `𝒳_s`) are independent on `W_m` for `m ≫ 0` (R7 on `κ_j`: evaluation at finitely many places is surjective): `codim ≥ s − c(Γ)` | G6.5 | **proved** (`GraphCount.add_card_sub_one_le_finrank` (spanning tree, triangular functionals), `SharpGenus.glue`, `exists_glue`, `ell_add_card_sub_one_le`) |
| G6.8 | **(connectedness)** `Γ` is connected, i.e. `𝒳_s` is connected (Zariski) | G8.1–G8.5 below | **proved** (`Connectedness.no_split`; G8.1 `SharpGenus.cut` via `exists_edge_or_indicator` (CRT)) |
| G6.9 | consequences: `Σ g(κ(wᵢ)) ≤ g(F)`; at most `g(F)` type-2 valuations have positive genus residue curve (W7 input) | G6.1 + G6.6–G6.8 | **proved** (`SharpGenus.sum_genus_le` over one Gauss point; `TypeTwo.sum_genus_le`: `Σᵢ g(κ(wᵢ)) ≤ g(F)` for any finite set of distinct type-2 valuations; `TypeTwo.card_le_genus`: at most `g(F)` have positive genus; `TypeTwo.isCurveFunctionField`) |

*G6.8 (connectedness).* Equivalently: `H^0(𝒳_s, O) = k`, i.e. the reductions of `𝓡` and of
`𝓡_∞ = ` integral closure of `O_C[1/x]` meet in `k` inside `⊕_j κ_j`; equivalently the Čech
module `𝓡_{01}/(𝓡 + 𝓡_∞)` (`⊗ C = H^1(X, O)`, of dimension `g`) is torsion free. This is
Zariski's connectedness theorem for `𝒳 → Spec O_C`; the counts G6.4–G6.7 alone do not exclude a
disconnected `𝒳_s`. **Chosen proof** (elementary "GAGA for `ℙ¹`" by traces; `C` complete):
suppose `Γ` splits as `J₀ ⊔ J₁` (both nonempty, no common closed point in either chart).

| # | Step | Inputs |
|---|---|---|
| G8.1 | the kernels of `𝓡̄ → ⊕_{J₀} κ_j` and `𝓡̄ → ⊕_{J₁} κ_j` are comaximal (a maximal ideal containing both lies on a `J₀`- and a `J₁`-component: prime avoidance, and every maximal ideal of `𝓡̄/𝔭_j` is centred by a place of `κ_j`, Chevalley); CRT gives `e ∈ 𝓡` with `ē = (1_{J₀}, 0_{J₁})`, similarly `e' ∈ 𝓡_∞` | G6.5, `ValuationSubring` extension |
| G8.2 | the characteristic polynomial `χ_e ∈ O_C[x][T]` reduces to `(T − 1)^{N₀} T^{N₁}` (`N_i = Σ_{J_i} f_j ≥ 1`; reduce the matrix of `e` in the orthonormal basis of G6.3); for every `C`-point `P` of `F` over `α ∈ O_C`, `e(P) ≡ 1` or `≡ 0`; this partitions the fibres over `|α| ≤ 1` into `U₀ ⊔ U₁` with `N₀`, `N₁` points (with multiplicity); likewise over `|α| ≥ 1` with `e'`, and both agree over `|α| = 1` (maximum principle: `‖e − e'‖ < 1` and integrality over `O_C[x, 1/x]` bound values at points) | Part R for `F / C` (places = `C`-points), charpoly specialization `χ_h(α, T) = Π_{P|α} (T − h(P))^{e_P}` |
| G8.3 | for `y ∈ L(d(x)_∞)°`: `p_n := Tr_{F/C(x)}(N^n(e)·y) ∈ O_C[x]` (`N(t) = 3t² − 2t³`, `‖N^{n+1}(e) − N^n(e)‖ ≤ ‖e² − e‖^{2^n}`) is Cauchy for the Gauss norm, with pointwise limit `τ_y(α) = Σ_{P ∈ U₀, P|α} e_P y(P)` (trace specialization); at `∞`, `q_n := Tr(N^n(e')·y/x^d) ∈ O_C[1/x]` with limit `τ_y(α)/α^d` | G6.5, trace specialization |
| G8.4 | (Liouville) a restricted power series `Σ aᵢ xⁱ` and `x^d Σ bᵢ x^{-i}` agreeing on `|α| = 1` coincide with a polynomial of degree `≤ d` (a restricted Laurent series vanishing on the unit circle is `0`: reduce a maximal-norm part, `k` infinite); hence `τ_y ∈ C[x]`, and `y ↦ τ_y` is `C[x]`-linear | completeness of `C` (limits of coefficients) |
| G8.5 | trace duality: `τ_y = Tr(z y)` for some `z ∈ F`; at an étale fibre, interpolation (R7) gives `z(P) = 1_{U₀}(P)`, so `z² = z`, `z ∈ {0, 1}`, contradicting `N₀, N₁ ≥ 1` | nondegenerate trace form (char 0), R7 |

**Sharp form: proved.** `TypeTwo.sum_genus_le` (`C` complete, algebraically closed, char `0`,
residue characteristic `p`): for any finite set of distinct type-2 valuations, `Σ g(κ(wᵢ)) ≤ g(F)`;
`TypeTwo.card_le_genus`: at most `g(F)` type-2 valuations have residue curves of positive genus.

**`b₁(Γ)` refinement** (`GenusBetti`): `CurvePlace.exists_interpolating` (R7: prescribed exact
order at one place, higher order at finitely many others); edges with their branches (`GEdge`:
places `Q` of `κ(w)`, `Q'` of `κ(w')` through a common closed point of a chart, with the twist
`tau`); `exists_ell_add_le` and `sum_genus_add_le`: if the second branch of each of the edges
`e₀, …, e_{n-1}` is new (not a branch of an earlier edge, nor its own first branch), then
`Σ_w g(κ(w)) + n ≤ g(F) + #{w} − 1` over the Gauss point; for the nodes of a semistable special
fibre (each node an edge with two new branches) this is `Σ_w g(κ(w)) + b₁(Γ) ≤ g(F)`. No
connectedness is needed for this count. Not yet done: the transfer of the `b₁` form from one
Gauss point to an arbitrary finite vertex set (needs the edges of the dual graph of a vertex set,
i.e. W5).

**Status.** Part R complete (`SemistableReduction/WeakApproximation`,
`SemistableReduction/CurveDivisor`, `SemistableReduction/RiemannRoch`). Part G complete
(`GaussFibre`, `LatticeReduction`, `GaussReduction`, `ResidueCurve`, `InfinityChart`,
`GenusCount`, `Connectedness`, `SpecialFibre`, `GraphCount`, `SharpGenus`, `TypeTwo`,
`GenusBetti`). Original estimate: estimate G6.1–G6.7 ≈ 1.5–2k lines, G6.8 ≈ 2–2.5k lines (C-points and
charpoly/trace specialization for `F / C`, Newton traces, Laurent comparison, trace duality),
G6.9 small. Fallback if G6.8 stalls: restructure W7 along Temkin's valuative proof (*Stable
modification of relative curves*, §§3–5: finiteness of the vertex set from quasi-compactness of
the Riemann–Zariski space and local uniformization, genus only for contracting to the stable
model).

**W7→W8 interface (agreed).** W8 (node analysis, branch `wp-w8prime`) proves semistability and
harmonicity at a node of the normalization under the ring-level hypothesis `IsKummerAt` (file
`SemistableReduction/KummerNode.lean`): étale-locally at the node, `F'` is a product of twisted
pure Kummer extensions `T^{d_i} = ε_i·u` in the node coordinate. W7 must produce `IsKummerAt` at
every node of the chosen vertex set. Tame case: Abhyankar's lemma. Wild case (`p ∣ d`): this is
the **annulus theorem** (Bosch–Lütkebohmert: for a suitable vertex set, the preimage of an open
annulus of the base is a disjoint union of annuli mapping by `u' ↦ ε u'^d`) — the analytic heart
of W7, planned in §9.9.
### 9.8 W9: descent

**Setting.** `K` henselian discretely valued of characteristic `0`, `C ⊇ K` algebraically closed
and algebraic over `K` (e.g. `AlgebraicClosure K` with the unique extension `v` of the valuation;
W4 needs only algebraic closedness), `K ⊆ K' ⊆ C` finite subextensions with `v' = v|_{K'}`
(`O' = O_C ∩ K'`, a DVR, unique extension to `C` since `K'` is henselian). Embeddings are ring
homomorphisms `φ : K' → C`, `ratFuncMap φ : K'(X) → C(X)` (`X ↦ X`); models over `O'` are
compared with models over `O_C` by the **base change of Zariski models**
`ZariskiModel.baseChange ψ R M` (charts `R ⊔ ψ(A)`, the images of `A ⊗_{O'} O_C`).

| # | Statement | Status / API |
|---|---|---|
| D1 | **Gauss data descend.** `ratFuncMap φ (gaussCoord a c) = gaussCoord (φ a) (φ c)`; `gaussRat v (φ a) r` restricts to `gaussRat (v.comap φ) a r` (`gaussRat_comap`, `comap_valuationSubring_gaussRat`; via `Gauss.sup_map`, `gauss_map`); finitely many centres/radii lie in a finite subextension (`exists_gaussDescent`, `K' = K(a_i, c_i)`, `v(c_i) = r_i`); residue fields: the local map `O_{w'} → O_w` sends `x̄'` to `x̄` (`residue_gaussGen_map`), so `κ(w) = k(x̄)` is generated over `k` by the image of `κ(w') = κ(O')(x̄')` (`adjoin_residue_gaussGen_map_eq_top`) | **proved** (`SemistableReduction/GaussDescent`) |
| D2 | **The tree model descends.** `baseChange` commutes with joins (`iJoin_baseChange`), `O_C ⊔ φ(O'[y]) = O_C[φ y]` (`sup_map_polyChart`), lines and joins of lines base-change (`line_baseChange`, `lines_baseChange`), hence `gaussJoinModel_baseChange`: the tree model over `O'` base-changes to the tree model over `O_C`; packaged with D1 as `exists_gaussJoinModel_descent`. Convexity/reducedness descend (`isConvex_comap_iff`, `isReduced_comap_iff`). **Semistability over `O'`**: rescaling radii by units of `O` does not change the model (`polyChart_mul_unit`, `gaussJoinModel_mul_unit`); a DVR has rank one (`eq_or_eq_top_of_le`) and every `c ≠ 0` is a unit times `ϖ^n`, `n ∈ ℤ` (`exists_valuation_div_zpow_eq_one`), so the tree model of any convex reduced family over a DVR is semistable for its uniformizer (`gaussJoinModel_isSemistable_of_isDiscreteValuationRing`; node charts `O'[u, ϖ'^n/u]`). The radii must lie in `v(K'^×)`: this is what forces ramified `K'` | **proved** (`GaussDescent`) |
| D3a | **Unique extension of Gauss valuations along `K'(X) → C(X)`**: a valuation subring `W` of `C(X)` with `W ∩ C = O_C` and `W ∩ K'(X) = O_{w'_{a,r}}` (`a`, `c ∈ K'`, `v(c) = r`) is `O_{w_{a,r}}` (`eq_gaussRat_of_comap_eq`). Proof: the residue of `(X − a)/c` is transcendental over `κ(O')` (D1), `κ(O_C)/κ(O')` is algebraic (`isAlgebraic_residueField`, from `not_isResidueTranscendental_of_isAlgebraic`), so it is transcendental over `κ(O_C)`; conclude by `IsGaussCoord.eq_of_isResidueTranscendental` (M4/W2) | **proved** (`SemistableReduction/VertexDescent`) |
| D3b | **Vertex sets restrict onto each other.** `L'/K'(X)`, `L/C(X)` fields, `χ : L' → L` compatible with `ratFuncMap φ`: restriction along `χ` maps the vertex set of the normalization in `L` of the tree model over `O_C` *onto* the vertex set of the normalization in `L'` of the tree model over `O'` (`vertexSet_mapsTo`, `vertexSet_surjOn`); surjectivity: Chevalley extension of `W'` to `L`, its restriction to `C(X)` lies over `O_C` (unique extension `O' ⊆ O_C`) and over `w'_i`, hence is `w_i` by D3a. The unique-extension property is a hypothesis `huniq` (for henselian `K'` it is the standard characterization of henselianity; not formalized: Mathlib's `HenselianLocalRing` only covers monic simple roots, and the non-monic Hensel factorization needed is absent) | **proved** (`VertexDescent`: `comap_comap_eq_gaussRat`, `exists_comap_eq_gaussRat`, `vertexSet_mapsTo`, `vertexSet_surjOn`) |
| D3c | **Injectivity after enlarging `K'`**: if `L` is the directed union of subfields `E_j` (e.g. `E_j = L'·K_j`, `K_j ⊇ K'` finite), restriction to some `E_j` is injective on any finite set of valuation subrings of `L` (`exists_injOn_comap`). The vertex set over `C` is finite (W4: `≤ [L : C(X)]` points over each `w_i`), so with D3b: **for `K_j` large the vertex sets over `C` and over `K_j` are in bijection** by restriction. (Equivalently: `Gal(C/K')` permutes the finitely many vertices over `C`; the stabilizers are open, and over the fixed field of their intersection every vertex is fixed, so restriction is injective.) | **proved** (`exists_injOn_comap`; combined with D3b: `exists_vertexSet_bijOn`, a `Set.BijOn` for some `j`, `huniq` for each `K_j` reduces to the base by `eq_of_comap_eq_of_tower`); finiteness of the vertex set over `C` is a hypothesis (from W4/B3) |
| D3d | **Residue fields at the vertices.** For `L` finite over `C(X)` and a vertex `W` over `w_{a,r}`, `κ(W)` is generated over `k` by the residues of finitely many elements of `W` (`exists_finset_adjoin_residue`: `κ(W)` is finite over `κ(w_{a,r}) = k(x̄)` by `FundamentalInequality.finite_residueField`); hence for `L = ⋃ E_j` directed and a finite vertex set there is one `j` with `κ(W)` generated over `k` by the residues of `W ∩ E_j` for all vertices (`exists_adjoin_residue_eq_top`, via `exists_subset_subfield`). Ramification compatibility is not formalized (not needed for generator descent) | **proved** (`SemistableReduction/ResidueDescent`) |
| D3e | **Generator descent** (replaces descent of rings/normality, which would need Raynaud–Gruson and limit arguments). W7/W8 work over `C` and must *expose finitely many elements* witnessing semistability of the normalization `M_C` of the tree model in `F'·C`: (i) the Gauss data `a_i, c_i` (centres, radii; D1); (ii) for each chart, finitely many generators of the normalization chart over the tree chart (integral elements); (iii) at each node: the node coordinates `u', v'` with `u'v' = ε·c`, the units `ε, ε'` and the thickness parameter `c` (`IsAnnulusAt`); (iv) at each smooth or branch point: the étale-chart data (coordinates, units, the Kummer generator and its equation, `IsKummerAt`) — all elements of `F'·C` integral over the tree charts. **Generic lemma (proved):** `exists_isIntegral_of_le_iSup` (finitely many elements integral over a subring contained in a directed union of subrings `A_j` are integral over one `A_j`: the monic equations have coefficients in some `A_j`) and `exists_mem_and_isIntegral` (with `L = ⋃ E_j`: the elements lie in one `E_j = F'·K_j` and are integral over the tree chart `A_j` over `O_j`; the tree chart over `O_C` is the union of those over `O_j` by D2, `sup_map_polyChart`). Then the node/étale interface holds verbatim over the DVR `O_j` (the defining identities are identities in `E_j`), and W8's node lemma over a noetherian DVR gives semistability of the normalization over `O_j` directly; thicknesses are made powers of `ϖ_j` as in D2. No descent of rings, normality or flatness is needed | generic lemma **proved** (`ResidueDescent`); assembly waits for the W7/W8 interface |

**Downstream (W10).** For a finite étale `T → Y`: W7 gives Gauss data over `C`; D1/D2 descend the
tree model to `O'` (semistable over the DVR `O'` after enlarging `K'` so that the radii are in
`v(K'^×)`); D3a–c identify the vertex sets of the normalizations over `O_j` and `O_C`; D3d–e give
the semistable `O_j`-model, turned into a `ModelCode` by M9b/M9c.

### 9.9 W7: semistable vertex sets and the annulus theorem

**Setting.** `C` algebraically closed, complete, `char C = 0`, residue field `k` of
characteristic `p` (as W4); `F' / C(x)` finite separable of degree `n`; `w_s = w_{0,s}` the
Gauss points of the segment `s ∈ (r₁, r₂)` (`gaussRat v 0 s`). Model language as in §9.6: a
convex reduced Gauss tree `V` of `C(x)` (M7), its join model `𝒳_V` (semistable, M7c) and the
normalization `𝒳'_V` of `𝒳_V` in `F'` (M6: vertex set `V'` = all extensions of the `w ∈ V`).
An **edge** of `V` is a node chart `R = O_C[u, c/u]` (`u = (x − a)/c_m`, M7b); its *tube* is
the set of valuations of `C(x)` centred at the node, i.e. the open annulus `|c| < |u| < 1`
(Gauss points `w_{a, s}` on the open segment and everything in their residue discs).

**Target (W7).** A finite convex `V` such that
* (a) every type-2 `w'` of `F'` with `g(κ(w')) > 0` lies over `V` (W6: `TypeTwo.card_le_genus`,
  at most `g(F')` of them, on `wp-tempered-w6`), and every type-2 `w'` with *branching* (more
  than two essential directions, see (A3)) lies over `V`;
* (b) the branch points of `F'/C(x)` (zeros/poles of the discriminant of a primitive element,
  and `∞`) are separated by `V` (each lies in its own residue disc of `V`, and `V` contains the
  Gauss points `w_{α, |α − β|}` of pairs of branch points);
* (c) **(annulus theorem)** at every point `P'` of `𝒳'_V` over a node of `𝒳_V`, the local ring
  of the normalization is étale-locally a node `O_C[u', c'/u']` with `u = ε u'^d`, `ε` a unit
  and `d` the multiplicity (and over each open disc of the complement, the preimage is a
  disjoint union of discs, i.e. `𝒳'_V` is smooth at the points over smooth points).

**Interface correction (W7 → W8): `IsKummerAt` is false in the wild case.** Example: `F' = C(u)`,
`x = u^p + p u`. The branch points are `∞` and `x = (p − 1) u`, `u^{p−1} = −1` (all on
`|x| = 1`), so `A = {|p|^{p/(p−1)} < |x| < 1}` contains none; its preimage
`{|p|^{1/(p−1)} < |u| < 1}` is an open annulus (Newton polygon of `u^p + pu − x`), mapped with
degree `p`, residue extension `x̄ = ū^p` (purely inseparable) at every `w_s`, so every type-2
point over `A` is rational with two directions. The normalization of the node at `A` is the node
in `u`. But it is not a Kummer extension `T^p = ε x` with `ε` a unit of the (henselized) base
node: for such an extension the different of `\hat F'_{w'} / \hat F_{w_s}` is `|p|` for all `s`
(`O_{w'} = O_{w}[T']`, `T' = T/c^{1/p}`, `|x ∂_x ε| ≤ |ε − ε(0)| < 1`), while for
`x = u^p + pu` it is `|f'(u)|·|u|/|x| = |p|·s^{(1−p)/p}`, not constant (Cohen–Temkin–Trushin,
*Morphisms of Berkovich curves and the different function*, §3.4; Berkovich: only *tame* étale
covers of annuli are Kummer). Hence:
* `IsKummerAt` (W8, `KummerNode.lean`) remains the right hypothesis **only in the tame case**
  (`p ∤ d`, Abhyankar's lemma, §9.2 (i));
* in the wild case W7 must deliver the node itself: **`IsAnnulusAt`** — the local ring of the
  normalization at `P'` and `Node O_C c'` have a common étale neighbourhood (this is
  `LocalModel.IsSemistableAt`), together with the multiplicity datum `u = ε u'^d` for
  harmonicity (W8′). W8's node analysis then reduces to bookkeeping in the wild case.

**Choice of route for (c).** The literature proofs of the wild annulus theorem all rest on the
local structure of Berkovich curves (Bosch–Lütkebohmert, *Stable reduction and uniformization
of abelian varieties I*, §2–§5: reductions of affinoids and the reduced fibre theorem;
Baker–Payne–Rabinoff, *On the structure of non-archimedean analytic curves*: complements of a
semistable vertex set, which presupposes semistable reduction; Temkin, *Stable modification of
relative curves* §3–§5: local uniformization of one-dimensional valued field extensions;
Cohen–Temkin–Trushin: the different function is piecewise monomial). The route closest to the
existing infrastructure (W4, W5 M6/M7, W6 G6.4–G6.8) is the **tube-degree + δ-count** route:

| # | Statement | Inputs | Status | Size |
|---|---|---|---|---|
| S1 | **units of a base annulus**: `φ ∈ C(x)ˣ` with no zero/pole of absolute value in `S` is `c xᵐ (1 + g)` with `w_s(g) < 1` for `s ∈ S`; `w_s(φ) = |c| sᵐ` (`IsMonomialOn`, a subgroup) | Gauss lemma, `C` alg. closed | **proved** (`AnnulusUnit`) | 0.15k |
| S2 | **norm formula**: `w(N_{F'/C(x)} y) = Π_{w' ∣ w} w'(y)^{f(w')}` for a Gauss point `w` (W4: `e = 1`, local degree `= f`); hence `s ↦ Π_{w' ∣ w_s} w'(y)^{f(w')}` is piecewise monomial (S1 applied to `N(y)`), and so is every elementary symmetric function of the multiset `{w'(y)}` (charpoly coefficients; Newton polygon) | `LocalGlobal` (`Local K g`, `toLocal`), `Algebra.norm_eq_prod_embeddings`, `spectralNorm` = function of the minimal polynomial | **proved** in the general local–global form (`NormFormula`: `algebraMap_norm_eq_prod` `N(y) = ∏_g N_{Local K g/K}(toLocal g y)` via `embeddingOf_bijective`, `norm_algebraNorm_local`, `norm_algebraMap_norm_eq_prod` `‖N y‖ = ∏_g extValuation g (y)^{deg g}`); Gauss-point form proved (`GaussNorm`: `factorEquiv`, `natDegree_eq_ramificationIdx_mul_inertiaDeg` (local degree `= e f`, W4 termwise), `gaussRat_norm_eq_prod`: `w_{a,r}(N y) = ∏_{w'} w'(y)^{e(w') f(w')}`) | 0.4k |
| S3 | **two directions**: genus `0`, `z ∉ k` with one zero `P` and one pole `Q` ⇒ `κ = k(t)`, `(t) = P − Q`, `z = λ tᵈ`, `d = [κ : k(z)]` | R5–R7 | **proved** (`TwoDirections`) | 0.2k |
| S4 | **points over the node** (replaces the completion plan): the node chart `nodeRing c = O_C[x, c/x]` (= `AnnulusModel.nodeChart`) is integrally closed with fraction field `C(x)`, so characteristic polynomials of elements of `R' = integralClosure (nodeRing c) F'` lift to `nodeRing c` (`exists_lift_normPoly`); every element of `nodeRing c` is a constant plus something of value `< 1` on the whole open segment (`exists_const`), the node ideal `tubeIdeal c` is maximal; elements of `R'` have value `≤ 1` at all extensions over the open segment; the **centre** `{y ∈ R' : w'(y) < 1}` of each extension is a maximal ideal over the node (`center_isMaximal`) | `AnnulusModel`, Mathlib `minpoly.isIntegrallyClosed_eq_field_fractions'`, `Valuation.Integers` | **proved** (`GaussTube`, `TubePoints`) | 0.4k |
| S5 | **tube degree is constant**: the *tube count* `Σ_{g : ‖toLocal g y‖ < 1} deg g = natTrailingDegree (P mod 𝔭)` for any `y` with `‖y‖ ≤ 1` at all extensions and a lift `P ∈ A[X]` of its characteristic polynomial (`TubeCount.sum_natDegree_eq_natTrailingDegree`; the characteristic polynomial is the product of the local ones, `normPoly_map_eq_prod`, and residue orders add, `IsResOrder.mul`); along the open segment `𝔭 = tubeIdeal c` for every radius, so `Σ_{w' ∣ w_{0,s}, w'(y) < 1} e f` does not depend on `s` (`GaussTube.sum_ramificationIdx_mul_inertiaDeg_eq`); with a separating element `e ≡ 1` at `P'`, `e ∈` the other (finitely many) centres: **`tubeDegree_eq`** — `d_{P'} = Σ_{centre w' = P'} e f` is the same at all radii of the open segment (in `|C^×|`) | S2, S4, W4 | **proved** (`TubeCount`, `GaussTube`, `TubePoints`) | 0.7k |
| S6 | **matching at the vertices**: `d_{P'} = Σ_{(v, Q) at P'} ord_Q(x̄)` over the branches `Q` (zeros of `x̄` on the residue curves `κ(v)`, `v ∣ w_{0,1}`) of the outer component through `P'`. Proof: (i) **residue of the norm at the Gauss point** `res N(z) = ∏_v N_{κ(v)/κ(w_{0,1})}(z̄_v)` — the reduced matrix of `z` in the orthonormal basis of G6.3 is block diagonal (`GaussFibre.exists_orthonormal_basis'` now exposes the residues of the basis; `Matrix.det_blockDiagonal''` for blocks of varying size); (ii) **norm specialization at a place**: for `x ∈ κ ∖ k` and `f` regular at the zeros `Q` of `x`, `N_{κ/k(x)}(f)(0) = ∏_Q f(Q)^{ord_Q x}`, by a *ramified orthonormal basis* `b_{Q,j}` (`ord_Q b_{Q,j} = j`, high order at the other zeros): the key valuation computation gives independence, integrality of coordinates and triangularity of the reduced matrix of `f` — **no separability is needed**, so the Frobenius twist is unnecessary; (iii) glue: node chart elements are constants plus elements vanishing at all branches (`exists_const_red`); branch reductions `placeHom`, maximal ideals `placeIdeal` over the node; values at `x̄ = 0` of elements of `κ(w_{0,1})` are independent of the residue curve (`res_algebraMap_eq`); the reduction of the characteristic polynomial at a branch is `∏_v ∏_Q (X − ȳ(Q))^{ord_Q x̄}` (`map_lift_eq_prod`); with a separating element for `P'` among the centres and branch ideals: **`tubeDegree_eq_vertexDegree`** | S5, G6.3, R5 | **proved** (`ResidueNorm`, `PlaceNorm`, `VertexMatch` for the outer vertex; `InnerVertex` for the inner vertex: the inversion `x ↦ c/x` exchanges `w_{0,s}` and `w_{0,|c|/s}` and preserves the node chart, the twist `Inv c F'` makes the inner vertex the outer one, `tubeDegree_eq_vertexDegree_inv`) | 1.8k |
| S7 | **δ-count**: for the normalization `𝒳'_V`, `g(F') = Σ_{w' ∈ V'} g(κ(w')) + b₁(Γ_{V'}) + Σ_{P'} δ'_{P'}` with `δ'_{P'} = δ_{P'} − (r_{P'} − 1) ≥ 0` (`r` = number of branches), `δ'_{P'} = 0` iff the special fibre has an ordinary double (resp. smooth) point at `P'`; this is G6.6 with **equality** (the codimension of `ρ(L(m(x)_∞)°)` in `⊕ L_{κ_j}(m(x̄)_∞)` is the total `δ` of the special fibre: the gluing conditions of G6.7 at all branches of all closed points, independent for `m ≫ 0`) | G6.4–G6.8 (W6), R7 | planned (shares W6's sharp form) | 1.5k |
| S8 | **upper bound / local Riemann–Hurwitz**: for `V` satisfying (a), (b) and the two-direction condition on every type-2 point over every edge (S3) and the one-direction condition in every disc, `g(F') ≤ Σ_{V'} g + b₁(Γ_{V'})`; proof by comparing Riemann–Hurwitz for `F'/C(x)` (`2g − 2 = −2n + deg Diff`, char 0: tame at type-1 points) with Riemann–Hurwitz for the residue curves `κ(w')/k(x̄)` (wild/inseparable: Hurwitz with the residue different) through the **different function** along the edges (piecewise monomial by S2 applied to `y = P'(θ)` with `θ` a primitive element integral at the tube; slope at a vertex in direction `Q` = local contribution of `Q` to the residue different — CTT Thm 4.6.4 / 3.4, in valuative form). With S7: `δ' = 0` everywhere | S2, S3, S5, S6, CTT §3–§4 | planned (**hard core**) | 2–3k |
| S9 | **node lemma** (over a DVR `O`, for a normal chart `B` of finite type): if the special fibre has an ordinary double point at `𝔭` (`IsOrdinaryDoublePoint` on `B_𝔭`: maximal ideal `(ϖ, u', v')`, residue field that of `O`, `u' v' ∈ (ϖ)`, branches `𝔔₁ ∌ u'`, `𝔔₂ ∌ v'` with `e = 1`, no other components through `𝔭`), `s x ≡ η u'^d` mod `(ϖ, v')` (`s, η ∉ 𝔭`) and `y ∉ 𝔔₂`, then `IsAnnulusAt ϖ x y d 𝔭` (`isAnnulusAt_of_isOrdinaryDoublePoint`). Proof: finite Newton iteration in `B_𝔭` (`B_𝔭 = O + (ϖ, u, v)`) to `u v = c + ϖ^{N+2} g`; a Krull-divisor argument (`KrullDVR`) and the order on the outer branch bound `v(c) ≤ N`, so `u v = ϖⁿ · unit` exactly, `N = d n`, `x = ε u^d`, `y = ε' v^d` (`IsOrdinaryDoublePoint.exists_node`); the node embeds (`Node.lift_injective`, coordinates transcendental); `B_t` is unramified hence étale over the node at `𝔭` (`formallyUnramified_of_map_maximalIdeal`, `isEtaleAt_of_isUnramifiedAt` via Mathlib's unramified local structure, `EtaleLocalDomain`). No completion is used (over `O_C` the `𝔪`-adic completion collapses, `𝔪_C = 𝔪_C²`) | S6, `Node`, Mathlib ZMT / unramified local structure | **proved** (`NodeLemma`, `NodeDeformation`, `UnramifiedNode`, `KrullDVR`, `EtaleLocalDomain`; `wp-w7-s9`) | 1.3k |
| S10 | **choice of `V`** (a), (b): restrictions of the `≤ g(F')` positive-genus points (W2 + W6), the separating Gauss points of the branch points, and the finitely many breakpoints of the different function on the convex hull (S2/S8; outside the convex hull of the branch points every disc is mapped by discs, `d_{P'} = 1` beyond the last breakpoint); convex closure (M7b). **Also `ModelCode.NoLoops`** (requested by W10): every node point lies on two *distinct* components — achieved by subdividing every loop edge by an interior Gauss point of its annulus (a vertex in the middle of the segment; the tube degrees are unchanged by S5) | W2, W6, S2, S8 | planned | 0.6k |

**Tame case shortcut.** If `p ∤ [F' : C(x)]` (or more generally `p ∤ d_{P'}` for all `P'`),
S7–S8 are not needed: over the tube, `F'` is a product of Kummer extensions `T^d = φ` with `φ`
in normal form S1 (`p ∤ m` after a unit change), so `IsKummerAt` holds and W8's
`Node.kummer_isIntegralClosure` applies. This covers the pro-`p'` applications.

**Estimate and status.** S1, S3 and the general form of S2 proved (≈ 0.6k: `AnnulusUnit`, `TwoDirections`, `NormFormula`). The remainder ≈ **8–10k lines**, the core being
S7–S8 (a valuative local Riemann–Hurwitz formula / the different function of
Cohen–Temkin–Trushin) and S4–S6 (completed node rings and their decompositions; Mathlib has
adic completions and Hensel's lemma for adically complete rings, but no henselization). This is
substantially larger than the original W7 estimate; the alternative (Temkin's local
uniformization at type-5 points plus gluing of annuli along the segment) has the same core
(local structure of directions at type-2 points) and no smaller prerequisites.

**Targeted W10 Props (and the base).** The W-chain targets exactly: `Statement`, `Statement.Strong`,
`Statement.Simultaneous` (incl. the W8′ harmonic output clauses to be added there), all stated for
**complete** discretely valued `K` of characteristic `0` (`[IsAdicComplete (maximalIdeal O) O]`;
changed from henselian, since unique extension of valuations is proved for complete bases only).
`Statement.Harmonic` and `Statement.Modification` are **not targeted**; anything consuming them
must be re-planned on `Statement.Simultaneous`, or the needed birational clause (e.g. thicknesses
along the chain over a node add up) must first be added to the targeted list here. Consequence for
§4/§10: the identification with André's group (Theorem A) is claimed only for complete base fields;
for henselian non-complete `K` the tempered group is defined but not identified.
**Finiteness over `O_C` (resolved for S4–S6).** The integral closure `R'` of the node chart over
the non-noetherian `O_C` is *not* shown to be finite (finiteness is essentially equivalent to the
stabilization of normalizations under base change, i.e. part of the theorem). S4–S6 are therefore
formulated without it and without completions: points over the node are the centres of the
(finitely many, W4) extensions of the Gauss points, separated by products of elements of
maximal ideals, and tube degrees are computed by the tube count, whose right side
(`natTrailingDegree (P mod 𝔭)`) is algebraic. S7–S9 work with finitely many vertices and points,
so they can stay over `O_C`; where a noetherian argument is unavoidable (S7's `δ`-count uses
lengths of the special fibre), it is run over a DVR `O_E` after picking the field of definition
of the finitely many witnesses below (W9 D1–D3c).

**S9 over a DVR (replaces the earlier witness form).** The earlier plan stated S9 over `O_C` in
"witness form" with a birational chart `A' = O_C[u', v'][1/h]` and `F' = C(x)(u')`; this is false
in general (it forces `F'` rational: a node point is only *étale*-locally a node), and over `O_C`
the completion argument collapses and `R'` is not known to be of finite type (Mathlib's unramified
local structure needs it). S9 is therefore stated and proved over a DVR `O = O_E` for a normal chart
`B` of finite type (`isAnnulusAt_of_isOrdinaryDoublePoint`). Its hypotheses are special-fibre
statements delivered by S7/S8 over `O_E` (agreed with the S7 agent): `𝔭B_𝔭 = (ϖ, u', v')`,
`κ(𝔭) = κ(O_E)`, `u'v' ∈ ϖB_𝔭` (the reduced special fibre is the fibre product of the two branch
rings), the branches `𝔔₁, 𝔔₂` with `e = 1` and no others, `x ≡ η u'^d` on the outer branch (S6),
`y` a unit on the inner branch. The exact node identity `u v = ϖⁿ` is *produced* by S9 (Newton
iteration), not assumed. The étale neighbourhood is a basic open of `B_t` which is standard étale
over the node (Mathlib `IsEtaleAt.exists_isStandardEtale` gives explicit witnesses if W10 needs
them). **Branch data for W8′ H5**: the output coordinates satisfy `u ∉ 𝔔₁`, `v ∉ 𝔔₂`,
`u v = ϖⁿ`, and the only DVR primes of `B_𝔭` containing `ϖ` are `𝔔₁, 𝔔₂`
(`IsOrdinaryDoublePoint.eq_or_eq_of_isDiscreteValuationRing`), i.e. `IsBranchNode` with the
uniqueness of the two branch vertices (the translation to `ZariskiHarmonic.IsBranchNode` on
subrings of the function field is part of H5's assembly).

**S7 plan (δ-count; lemma level).** The count runs over `C`, because Riemann–Roch (Part R) exists
only over algebraically closed fields. The local structure is deduced over `C` and then transferred
to the DVR `O_E` of W9, where S9 consumes it (agreed with S9: hypotheses (h2), (h3) below). Notation:
`V` a convex Gauss tree with node charts, `V'` the extensions, `ρ` the reduction to the residue
curves `κ(w')` (`ρ_{w'}(y)` is the residue at `w'`), `R'_e = Rint` the integral closure of the
node chart of an edge `e` (normalized so that `e` joins `w_{0,1}` and `w_{0,|c|}`), and `P'` a
maximal ideal of `R'_e` over the node. Its branches are the pairs `(w', Q)`, where `Q` is a place
of `κ(w')` centred at `P'` (`placeIdeal`, S6). `Õ_{P'} = Π_{(w',Q)} O_Q`, `Ō_{P'} = ρ(R'_{e,P'})`,
the jet kernel is `K_M = {ord_Q ≥ M at every branch}`, and
`δ^{(M)}_{P'} = dim_k Õ/(Ō + K_M)`.

| # | Statement | Proof / inputs |
|---|---|---|
| S7.1 | **jet interpolation**: for `D` of large degree with `D(Q) = 0` on a finite set `S` of places, every family of targets `τ_Q ∈ O_Q` is matched to order `M` by some `f ∈ L(D)` | `exists_interpolating` (R7) yields `f_{Q,n}` of exact order `n` at `Q` and order `≥ M` at `S ∖ {Q}`. Correct the error one order at a time with `c = res((τ_Q − f)/f_{Q,n})` |
| S7.2 | **abstract δ-count**: `R ⊆ W = Π_j L(D_j)` (`deg D_j ≫ 0`). Points `p` have pairwise disjoint branch sets and condition spaces `Ō_p` with `R ⊆ Ō_p + K_{M,p}`. If `n_p` elements of `Õ_p` are independent modulo `Ō_p + K_{M,p}`, then `dim R + Σ_p n_p ≤ dim W` | S7.1 lifts the independent jets to elements of `W` that vanish to order `M` at the other points; linear algebra |
| S7.3 | `δ^{(M)} ≥ r − 1` for `M ≥ 1` (all residues of elements of `Ō` agree: `ρ(y)(Q) = y mod P'`); `δ^{(M)}` is monotone in `M` | the indicators of `r − 1` branches |
| S7.4 | **lattice reduction for several Gauss points**: for a finite set `V` of Gauss points and a finite-dimensional `U ⊆ F'`, `dim_k ρ(U°) = dim_C U` for `‖·‖ = max_{w ∈ V} gnorm_w` | for each `w`, G6.4 gives `T_w : U → C^{J_w}` with `‖T_w f‖ = |γ_w| gnorm_w f`. The map `(γ_w⁻¹ T_w)_w` is isometric into the sup norm; `exists_orthonormal_of_linearMap`. Needs the coordinate change `x ↦ (x − a)/c` (type synonym, as `Inv` in `InnerVertex`) |
| S7.5 | **the divisor**: `D_m = m Σ_{w ∈ V} (x − a_w)_0`, where the direction `x̄_w = 0` at `w` points to no vertex. For `f ∈ L(D_m)` with `‖f‖_V ≤ 1`, `ρ_{w'}(f) ∈ L_{κ(w')}(m (x̄_w)_0)`; at a node point, `f·h ∈ R'_e` for some `h ∈ R'_e ∖ P'` | G6.5 in the coordinate `x_w` with the twist `Π_u ((x − a_u)/λ_u)^m`; `∞` at the root via `x_w⁻¹`. The node chart needs the **maximum principle**: `y` integral over `C[x, x⁻¹]` with `w'(y) ≤ 1` at the extensions of both end points lies in `R'_e` (charpoly coefficients are Laurent polynomials bounded at both radii) |
| S7.6 | **δ-count over `C`**: for every finite set of node points and every `M`, `Σ_{V'} g(κ(w')) + Σ_{P'} δ^{(M)}_{P'} ≤ g(F') + #V' − 1`. With `b₁ = Σ_{P'} (r_{P'} − 1) − #V' + 1` this is `g(F') ≥ Σ g + b₁ + Σ δ'^{(M)}`; with S8 (`g(F') ≤ Σ g + b₁`, same `b₁`) every `δ'^{(M)}_{P'} = 0` | S7.2 with `R = ρ(L(D_m)°)`, S7.4 (`dim R = ℓ(D_m)`), R7 on `F'` and on the `κ(w')`, `deg D_m = m #V N` |
| S7.7 | **finiteness and conductor over `C`**: `Λ = ρ(R'_e)` is finite over `k[X, Y]/(XY)` (a submodule of the finite product of the integral closures of `k[x̄]`, `k[ȳ]` in the `κ(w')`; `k` perfect, separating element + Frobenius); a nonzerodivisor `s ∈ Λ` lies in the conductor, so `K_M ⊆ Ō` for `M ≫ 0` and `δ = δ^{(M)}` | `ChangeOfGenerator.exists_transcendental_isSeparable`, `IsIntegralClosure.finite` |
| S7.8 | **ordinary double point over `C`**: if `r = 2` and `δ' = 0`, then `Ō = {(a, b) : a(Q₁) = b(Q₂)}`, and for every `u', v' ∈ P'` with `w'₂(u') < 1`, `ord_{Q₁} ū' = 1`, `w'₁(v') < 1`, `ord_{Q₂} v̄' = 1`: `P' R'_{P'} = (u', v') + 𝔪_C R'_{P'}`. Also `x ≡ η u'^d` modulo `ker ρ`, `η ∉ P'`, by S6 | `ker ρ = 𝔪_C R'_{P'}` (the value group is `|C^×|` and the maximum principle of S7.5) |
| S7.9 | **transfer to `O_E`** (S9's (h2), (h3)): `E` large enough that (i) the vertices biject (D3c); (ii) `e_E = 1` and `f_E = f_C` (D3d gives `f_C ≤ f_E`, and the fundamental inequality gives `Σ e_E f_E ≤ N = Σ f_C`); (iii) `Λ_C = k·ρ(B_E)` (the finitely many generators of S7.7 descend, D3e); (iv) the branches and `κ(𝔭)` are `κ_E`-rational. Then `B/ϖB ↪ Π κ_E(w')` (reduced, (ii)), and `Λ_E ⊗ k = Λ_C` with `Λ_C ∩ Π κ_E(w') = Λ_E` (linear disjointness from (ii)). So `Ō_E` is the fibre product, and (h2) `𝔭 B_𝔭 = (ϖ, u', v') B_𝔭` holds for every `u', v'` as in S7.8 (Nakayama is not even needed: `ker ρ = ϖ B_𝔭` by e = 1 and the maximum principle over `E`), and (h3)(B) `x ≡ η u'^d mod ϖ B_𝔭` | D3a–D3e, `FundamentalInequality` |

Not delivered by S7: S9's (h1) `u' v' = ϖⁿ·unit` is not a special-fibre statement (δ' = 0 only gives
`u' v' ∈ ϖ B_𝔭`). Estimate: S7.1–S7.3 ≈ 0.4k, S7.4–S7.6 ≈ 1.2k, S7.7–S7.8 ≈ 0.6k, S7.9 ≈ 0.8k.
Files: `DeltaCount` (S7.1–S7.3).

**S7 status (wp-tempered-s7).** Proved over `C`: S7.1–S7.6 and S7.8, plus the conductor/closedness
part of S7.7.
- Files: `DeltaCount`, `DeltaGenus`, `MultiGauss`, `LatticeReduction`, `NodeMaximum`,
  `CurveIntegralClosure`, `CurveGenerators`, `ConductorLocal`, `NodeSide`, `NodeDouble`,
  `NodePoints`, `TreeData`, `TreeDivisor`, `TreeReduction`, `TreeNode`, `TreeCount`, `TreePoints`.
- The tree instantiation is over `TreeCount.TreeData` (vertices `(aᵢ, cᵢ)`, edges `par`/`chi`,
  free directions `bᵢ`). The node points of an edge `e` (`TreeData.NP`) are the points of
  `Rint c_e F` (chart `x_e = (x₀ − a_{χe})/c_{πe}`, `c_e = c_{χe}/c_{πe}`) that have an outer
  branch. `TreeData.Sp P` collects the outer and inner branches through `P`. The condition space
  `TreeData.Oc P` holds the fractions `y/s` of `R'_e` with `s ∉ P'`.
- `TreeData.delta_count`: `Σ_W g(κ(W)) + Σ_P (r_P − 1) ≤ g(F) + #S − 1`.
- `TreeData.jets_of_le`: under the reverse inequality, `eqRes ≤ Oc ⊔ K_M` at every node point.
- `TreeData.isNodeODP_of_le`: under the reverse inequality, every point with one outer and one
  inner branch is `GaussTube.IsNodeODP`. It goes through `GaussTube.isNodeODP_of_jets`, which
  uses `NodeDouble.exists_fp`.
- S7.9 (transfer to `O_E`) was reassigned to L3/R4/O1.

**Estimate and status.** Proved: S1, S2 (general and Gauss-point form), S3, S4, S5, S6 (outer
vertex) (`AnnulusUnit`, `NormFormula`, `GaussNorm`, `TwoDirections`, `TubeCount`, `GaussTube`,
`TubePoints`, `ResidueNorm`, `PlaceNorm`, `VertexMatch`; ≈ 3.3k lines) and the interface
`AnnulusAt`, plus `InnerVertex` (≈ 0.4k). Remaining: S7 (≈ 1.5k),
S8 (the hard core, ≈ 2–3k: a valuative local Riemann–Hurwitz formula / the different function of
Cohen–Temkin–Trushin), S9 (≈ 0.8k, witness form), S10 (≈ 0.6k): ≈ 6–7k lines.

**Targeted list update.** `Statement.StrongComponent` (`SemistableReduction/StrongComponent.lean`,
requested by Theorem B's domination step) supersedes `Statement.Strong`: identical except that the
connected-special-fibre clause is replaced by the component clause (for every primitive idempotent
`ε` of `K' ⊗_K B` a clopen split semistable sub-model with connected special fibre, stable under the
stabiliser of `ε`). The targeted W10 Props are now `Statement`, `Statement.StrongComponent`
(to be extended by `ModelCode.NoLoops` when it lands), `Statement.Simultaneous` (with
`IsHarmonic`) and `Statement.HarmonicGeneral` (with `NoLoops` hypothesis, (H2) as `≥`).
`Statement.Strong` is kept for reference, untargeted.

**S8 analysis (2026-10): the different-function route is circular; revised plan.**

*Finding.* Cohen–Temkin–Trushin (arXiv 1408.2949) work throughout with skeletons, i.e. they
*assume* the semistable reduction theorem (§3.5 "Global structure": "the semistable reduction
theorem asserts that any nice compact curve possesses a skeleton"). Every global statement about
the different function that S8 was to use depends on it: the restrictions on slopes (§4.2,
`restrictth`, proof via simultaneous semistable reduction along an interval), the triviality of
`δ_f` off a skeleton and `R_y = 0` at type-4 points (`deltatrivth`), and the genus formulas
(`genusth`, `genusth2`, `coverdisclem`). Only the *local* Riemann–Hurwitz formula at a single type-2
point (`prop:local_RH`) is skeleton-free, and it says nothing about genus hidden away from the type-2
points one looks at. CTT state the logical status themselves (remark after `unramparam`, §2.1): the
semistable reduction theorem is equivalent to Temkin's *uniformization of one-dimensional valued
fields* (every one-dimensional analytic `C`-field has an unramified parameter; Temkin, *Stable
modification of relative curves*, Thm `fieldunif1` of §2, proved in §6; "direct though involved"). Hence:

* the S8 row as planned (RH for `F'/C(x)` + RH for the residue curves + the different along the
  edges) cannot give `g(F') ≤ Σ g + b₁`: all three are compatible with genus hidden at non-type-2
  limit points (types 4 and 5), and the different is piecewise monomial with *finitely many*
  breakpoints only once a skeleton exists. The pointwise hypotheses of the S8 row (two directions
  over edges, one direction in discs, at every type-2 point) do not help for the same reason;
* the S10 claim "outside the convex hull of the branch points every disc is mapped by discs" is
  **false** in the wild case. Example (Matignon type): `p ∤ m ≥ 2`, `λ^{p−1} = −p`,
  `F' = C(x, y)`, `y^p = 1 + λ^p x^m`. The branch points are `∞` and the zeros of `1 + λ^p x^m`, on
  `|x| = R = |p|^{−p/(m(p−1))} > 1`, so `w_{0,1}` lies in the residue disc of `w_{0,R}` towards
  `0`, off the hull. With `y = 1 + λz` the equation becomes `z^p − z + (terms of norm < 1) = x^m`,
  so the residue curve over `w_{0,1}` is the Artin–Schreier curve `z̄^p − z̄ = x̄^m` of genus
  `(p−1)(m−1)/2 > 0`: the preimage of a branch-point-free disc carries genus.

*What is (and is not) needed.* With S7.6 (`g(F') ≥ Σ_{V'} g + b₁ + Σ_{P'} δ'_{P'}`) the hidden genus
`h(V) = g(F') − Σ_{V'} g − b₁(Γ_{V'})` is `≥ 0`, non-increasing under refinement of `V`, and local.
S8 must show `inf_V h(V) = 0`; this is the analytic genus formula, i.e. the content of the
semistable reduction theorem, and has to be proved, not quoted. Neither a Riemann–Hurwitz formula
nor the different function is needed for it. (A characteristic-free Riemann–Hurwitz formula in
Euler-characteristic form, `Σ_j (g(κ_j) − 1) + n = −Σ_u [O'_u : ⟨b⟩_{O_u}]` for a basis `b` of a
product of function fields `κ_j` over `k(t)`, proved from `ell_eq_of_le_degree` by comparing
`B ∩ tᵐ N` for `O_∞`-lattices `N`, localizes `h(V)` into lattice defects of the discs and annuli of
`V` without S7; it is a reformulation, not a proof, and is not pursued.)

*Revised lemma-level plan for S8 (existence form, merges S8 and S10).* **Superseded** (2026-10)
by the [AW] structure S8.A–S8.C of §9.10 ("Decision"); kept for the record.

| # | Statement | Inputs / remarks | Size |
|---|---|---|---|
| S8.0 | **limit valuations of `C(x)`**: every valuation `w` of `C(x)` extending `v_C` is approximated by Gauss points: for every polynomial `f` there is `a` with `w(f) = w_{a', w(x − a')}(f)` for all `a'` with `w(x − a') ≤ w(x − a)`; if `inf_a w(x − a)` is attained, `w = w_{a, w(x−a)}` (types 2, 3), otherwise `w` is the limit of a nested sequence of Gauss points (type 4) | factor into linear factors (as W2) | 0.2k, **proved** (`GaussLimit`) |
| S8.1 | **compactness (König)**: if `h(V) > 0` for every finite `V ⊇ V₀`, there is a limit point `ξ` (type 1, 3, 4, or a type-5 direction at a type-2 point) every neighbourhood of which (disc or annulus of some refinement) carries hidden genus | `h` is additive over the discs/annuli of `V` (S7 localization) and integer-valued; refinements split it | 0.8k |
| S8.2 | **type 1** (char 0): around `a ∈ P¹(C)` there is `s₀` such that the preimage of the disc `|x − a| < s₀` is a disjoint union of discs `y_P^{e_P} = (x − a)·ε_P` | Puiseux/algebraic power series converge (Eisenstein bounds); tube count S5 in the small disc | 1k |
| S8.3 | **type 5** (directions at a type-2 point `z`): for `z'` close to `z` in direction `u` the annulus `(z', z)` carries no hidden genus | W4 at `z`, separating residue parameter (Temkin `fieldunif1`(iii)), S5/S6 | 0.8k |
| S8.4 | **type 3** (Gauss points of irrational radius) | W4 for `r ∉ |C^×|` (cartesian, `e > 1` possible) | 0.6k |
| S8.5 | **type 4** (the core): a one-dimensional field of type 4 over `C` has an unramified parameter; hence a small disc around the type-4 point carries no hidden genus | Temkin 2010 §6.1–6.3 (immediate degree-`p` extensions, critical cosets `b + S_{a,s}`, uniformization of fields topologically generated by one element); alternative: Arzdorf–Wewers (arXiv 1211.4624: Galois closure, inertia at a type-4 point is a `p`-group, reduction to `p`-cyclic Kummer covers analysed with Matignon's `p`-Taylor expansions; needs Bosch–Lütkebohmert Lemma 2.4) | 4–6k |
| S8.6 | **assembly**: finitely many neighbourhoods of S8.2–S8.5 cover the limit points (S8.1), so some finite `V` has `h(V) = 0`; with S7, `δ' = 0` at every node point | S8.1–S8.5, S7 | 0.4k |

Revised estimate for S8 (with S10): **8–10k lines**, dominated by S8.5, which needs the theory of
type-4 valuations (completions of `C(x)` at non-Gauss valuations, immediate extensions) that the
project does not have yet. The tame case (all residue extensions over the relevant points of
degree prime to `p`, e.g. Galois group of order prime to `p`) needs none of this (Kummer, §9.2 (i)).

**S8.1–S8.4: lemma-level plan (2026-10, branch `wp-tempered-s81`).**

**Status: superseded by the Arzdorf–Wewers global structure (§9.10)**, which replaces the
compactness argument S8.1 and absorbs S8.2/S8.4. Kept as proved and possibly reusable: S8.1
(`DiscLimit`: limit valuations of nested discs, germs of annuli) and S8.2a (`SplitDisc`: Hensel
with a scaling in the completion of `E(x)` at an arbitrary valuation, splitting over small discs
at unramified classical points, local degree one). The rest of this plan is not pursued; the
type-5 analysis S8.3 reappears as §9.10 L3 (Bosch–Lütkebohmert Lemma 2.4).

*Interface with S7.* S7 (`DeltaGenus`, branch `wp-tempered-s7`) proves, for a fixed vertex set,
`Σ_{V'} g + b₁ + Σ_{P'} δ'_{P'} ≤ g(F')` with `b₁ = Σ_{P'}(r_{P'} − 1) − #V' + 1`
(`sum_genus_add_sum_card_sub_one_le`) and "`h(V) ≤ 0` ⇒ every `δ'_{P'} = 0`"
(`card_le_of_indep`). It does **not** give monotonicity of `h` under refinement or its locality
(both need the equality `g = Σ g + b₁ + Σ δ'`, i.e. S8 itself). Hence S8.1 is formulated without
`h`: it is the valuation-theoretic limit construction for nested pieces (discs, annuli) of
`P¹_C`, and the assembly S8.6 works with a predicate "the piece `U` is *good*" (its preimage
is a disjoint union of discs, resp. annuli), which is hereditary for sub-pieces, together with
S7's bound `Σ δ' ≤ h(V)` (finitely many bad pieces for a fixed `V`) and an S9-type bridge
"good piece ⇔ `δ' = 0` at the points over it".

*S8.1 (compactness: limits of nested pieces).* `K` algebraically closed with a valuation `v`
(any value group), pieces are closed discs `D(a, r) = {w : w(X − a) ≤ r}`.

| # | Statement | Inputs | Size |
|---|---|---|---|
| S8.1a | **eventual limits of valuations**: a sequence of valuations `wₙ` of a ring which is eventually constant at every element has a limit valuation `w` (`w f = wₙ f` for `n ≫ 0`) | — | 0.05k, **proved** (`DiscLimit.limit`) |
| S8.1b | **type 4**: for nested discs `D(aₙ, rₙ)` (`r_{n+1} ≤ rₙ`, `v(a_{n+1} − aₙ) ≤ rₙ`) without a common point of `K`, `w_{aₙ,rₙ}(f)` is eventually constant for every `f ∈ K(X)`; the limit `w` extends `v`, lies in every disc (`w(X − aₙ) ≤ rₙ`), is the **unique** valuation extending `v` with this property, and is not a Gauss valuation; `w(X − b) = v(b − a_m)` as soon as `b ∉ D(a_m, r_m)` | S8.1a, W1, `valuation_ratFunc_ext_of_linear` | 0.2k, **proved** (`DiscLimit`: `isEventuallyConst_gaussRat`, `limitVal`, `limitVal_lin_le`, `eq_limitVal`, `limitVal_ne_gaussRat`) |
| S8.1c | **common point**: if `b ∈ ⋂ D(aₙ, rₙ)` then `w_{aₙ,rₙ} = w_{b,rₙ}`; **type 1**: if moreover `rₙ` tends to `0` (below every unit), no valuation extending `v` lies in all discs, and `w_{aₙ,rₙ}(p) = v(p(b))` for `n ≫ 0` whenever `p(b) ≠ 0` | W1 | 0.1k, **proved** (`gaussRat_eq_of_le`, `not_forall_le_of_tendsto_zero`, `eventually_gaussRat_eq_eval`) |
| S8.1d | **types 3 and 5 (germs at a radius)**: for `φ ≠ 0` and a radius `ρ`, `φ` is monomial (S1) on a one-sided interval `(ρ, ρ')` (resp. `(ρ', ρ)`), and on a two-sided interval `(ρ₁, ρ₂) ∋ ρ` if `ρ ∉ v(K^×)` (no zero or pole of `φ` has absolute value `ρ`) | S1 (`AnnulusUnit`) | 0.1k, **proved** (`exists_isMonomialOn_above`, `_below`, `_around`) |

*S8.2 (type 1, `char C = 0`).*

| # | Statement | Inputs | Size |
|---|---|---|---|
| S8.2a | **split over a small disc at an unramified point**: `P ∈ C[x][Y]` monic in `Y`, `P(a, Y)` separable of degree `n`. There is `s₀ > 0` such that for **every** real valuation `w` of `C(x)` extending the norm of `C` with `w(x − a) < s₀` (any type), `P` has `n` distinct roots in the completion `\hat{C(x)}_w`; hence (B3) `w` has exactly `n` extensions to `F' = C(x)[Y]/(P)`, each of local degree `1` (`e = f = 1`, completions equal) | Hensel in the completion (`PthPower.exists_root`), `LocalGlobal` | 0.4k |
| S8.2b | **Kummer base change**: for `a ∈ C` and `E` divisible by all ramification indices over `x = a`, every factor of `F' ⊗ C(t)`, `t^E = x − a`, is unramified over `t = 0` (Abhyankar's lemma at the DVR `C[x]_{(x−a)}`, residue field `C` of characteristic `0`, so tame); hence it has a generator integral over `C[t]` with separable reduction at `t = 0`, and S8.2a applies in the `t`-disc | `Abhyankar`, S8.2a | 0.5k |
| S8.2c | **descent**: for `w` in the `x`-disc `|x − a| < s₀^E` the extensions of `w` to `F'` are restrictions of those of its extensions to the `t`-line; for a Gauss point the residue curves are subfields of `k(t̄)` containing `k(x̄)`, hence rational (Lüroth), with one point over `x̄ = 0` | S8.2b | 0.3k |

*S8.3 (type 5: a direction at a type-2 point; after a coordinate change `z = w_{0,1}`, direction
`x̄ = 0`).*

| # | Statement | Inputs | Size |
|---|---|---|---|
| S8.3a | **direction parameter**: for `w' ∣ w_{0,1}` and a place `Q` of `κ(w')` with `x̄(Q) = 0`, `e_Q = ord_Q x̄`, some `t ∈ F'` has `w'(t) = 1`, `t̄` a uniformizer at `Q`; `w'` restricts to the Gauss point `w^{(t)}_{0,1}` of `C(t)` | A1/`TypeTwo.valuation_aeval_eq_sup`, W2, R5 | 0.2k |
| S8.3b | **tube degree one**: choosing `t̄` with `Q` its only zero among the branches through the point `P'` of the `t`-node (Riemann–Roch R7, separation `TubePoints.exists_separating`), S6 for `F'/C(t)` gives tube degree `1` at `P'`: for `ρ` close to `1` exactly one extension of `w^{(t)}_{0,ρ}` is centred at `P'`, with `e = f = 1` and residue curve `k(t̄)` (two directions) | S5, S6 (`VertexMatch`, `InnerVertex`) | 0.5k |
| S8.3c | `x = ε t^{e_Q}` with `ε` a unit along `(ρ₀, 1)` (finitely many zeros/poles of `x / t^{e_Q}`, norm formula S2): the `t`-annulus maps onto the `x`-annulus `(ρ₀^{e_Q}, 1)` with degree `e_Q` | S1, S2 | 0.3k |

*S8.4 (type 3: `w_{a,r}`, `r ∉ |C^×|`).*

| # | Statement | Inputs | Size |
|---|---|---|---|
| S8.4a | **dominant monomials**: `w_{a,r}(Σ cᵢ (x − a)^i)` is attained at a unique `i`; residue field `k`, value group `|C^×| · r^ℤ`; extensions `w'` to `F'` have `f = 1` and `Γ_{w'} = |C^×| · ρ^ℤ` with `ρ^{e(w')} ∈ r · |C^×|` | W1, A3 | 0.2k |
| S8.4b | **stability at irrational radius** (W4 for type 3): `Σ_{w' ∣ w_{a,r}} e(w') = [F' : C(x)]`. Route as G1–G3: tame part `H((c(x − a))^{1/m})` is again of type 3; wild part a tower of Galois degree-`p` Kummer steps over type-3 fields, defectless because modulo `p`-th powers a `1`-unit has a dominant monomial `d yⁿ` with `p ∤ n` (orthogonal basis `{yⁿ}`, F4 simplified), so `e = p`; finiteness over the closure of `C(y)` as in G2 | G1–G3 pattern, `PthPower`, `LocalGlobal` B4 | 1.5k (the 0.6k of the S8 table was too low) |
| S8.4c | **no visible genus near `r`**: the finitely many type-2 points of positive genus (`TypeTwo.card_le_genus`) project to rational radii, so a small annulus `(r₁, r₂) ∋ r` avoids them | W6 | 0.2k |
| S8.4d | **unramified parameter**: `y ∈ F'` with `w'(y)` generating `Γ_{w'}` modulo `|C^×|`: by S8.4b for `F'/C(y)` the completion of `F'` at `w'` is that of `C(y)`; with S5 on a small `y`-annulus this gives tube degree `1` | S8.4b, S5 | 0.4k |

Order of work: S8.1a–d, S8.2a, S8.2b–c, S8.3a, S8.4a, S8.4c; then S8.3b–c and S8.4b, d.
`Statement.HarmonicX` (`XHarmonic.lean`, intrinsic x-lengths, arbitrary bases; §9.7) is added to
the targeted list and supersedes `Statement.HarmonicW` for Theorem B (B5).

**S7⁺ (genus equality; the "≤" direction).** S7 gives `p_a(𝒳_s) ≤ g(F)` (special-fibre sections
contain the reductions of the generic ones). S7⁺ gives the reverse: every section of the special
fibre lifts. The proof uses no S8 input and no completeness of `C`. It needs `C` algebraically
closed with `char C = 0` (`[CharZero C]`, for the trace form) and W4 (`e = 1`, so the norms take
values in `|C^×|`). Setting: the GaussFibre framework, i.e. `F / C(t)` finite for an arbitrary
transcendental `t ∈ F`, vertex set `Ext C F` (all extensions of the Gauss point of `C(t)`), and
charts `𝓡₀ = intRing t`, `𝓡_∞ = intRing t⁻¹` with reductions `Λ₀ = redRing t`, `Λ_∞ = redRing t⁻¹`.
Below, `x = t`.

| # | Statement | Proof / inputs |
|---|---|---|
| S7⁺.1 | **trace bound**: for an orthonormal basis `b ⊆ 𝓡₀` (G6.3, made integral), there is `Δ₀ ∈ O_C[x]` with Gauss norm `1` such that `Δ₀·φᵢ ∈ O_C[x]` for the coordinates `φ` of every `a ∈ 𝓡₀`. Hence `Δ̄₀ Λ₀ ⊆ ⊕ k[x̄] b̄ᵢ`, and `Λ₀` is a **finite free `k[x̄]`-module of rank `N`** | `Tr(a bⱼ) ∈ O_C[x]` (`exists_trace_eq`, `gauss1_trace_le`); Gram matrix `G`, `det G = γΔ₀`, `adj G`; then divide by `γ` (Gauss norm `≤ 1`). Over a PID: `Submodule.basisOfPid` |
| S7⁺.2 | **chart basis**: lifts `sᵢ ∈ 𝓡₀` of a `k[x̄]`-basis of `Λ₀` are an orthonormal `C(x)`-basis of `F` | if `‖Σφᵢsᵢ‖ < max|φᵢ|`, clear denominators to get a `k[x̄]`-relation among the `s̄ᵢ`; count `N` from `b` |
| S7⁺.3 | **no poles in the closed disc** (fibre argument): the coordinates of every `a ∈ 𝓡₀` in the basis `s` are `p/q` with `q` having no root in `|α| ≤ 1` and Gauss norm `≤ 1` | at a root `α` of `q` with `|α| ≤ 1`, `Σ pᵢ(α) sᵢ ∈ (x − α)·A₀`; normalized, `v = Σcᵢsᵢ/(x − α) ∈ 𝓡₀` (norm `1`), so `(x̄ − ᾱ) v̄ = Σ c̄ᵢ s̄ᵢ` contradicts the basis property; cancel `(x − α)`, induct on the roots. The same holds for `t⁻¹` (generic coordinate `ζ ∈ {X, X⁻¹}`) |
| S7⁺.4 | **Laurent split on the circle**: `φ = p/(q_out q_in)` (roots `|α| > 1`, resp. `< 1`) with `|φ| ≤ 1` is `φ₊ + φ₋`, `φ₊` regular on `|x| ≤ 1`, `φ₋` regular on `|x| ≥ 1` with `φ₋(∞) = 0`, both of Gauss norm `≤ 1` | Mathlib partial fractions (`div_eq_quo_add_rem_div_add_rem_div`); norm: `q̄_in = x̄^d`, `q̄_out = 1`, so `p̄ = P̄₊ x̄^d + r̄₂` with `deg r̄₂ < d` (degree separation) |
| S7⁺.5 | **lifting of sections** (integral Serre vanishing): there is `m₀` such that for `m ≥ m₀`, `a ∈ 𝓡₀`, `b ∈ 𝓡_∞` with `ā = x̄ᵐ b̄`, some `f ∈ L(m(x)_∞)` with `‖f‖ ≤ 1` has `f̄ = ā` | `d = a − xᵐb = Σχᵢsᵢ` with `χᵢ` regular on the circle (S7⁺.3 for `a`, for `b` in the basis `t`, and for `tⱼ`, `x^{-k}sᵢ`), `|χ| = ‖d‖ < 1`; split `γ⁻¹χ = χ₊ + χ₋` (S7⁺.4), `f = a − γΣχ₊sᵢ = xᵐb + γΣχ₋sᵢ`; `f ∈ A₀` and `x^{-m}f ∈ A_∞` by coprime denominators (roots `|α| > 1` vs `|α| < 1`), and `L(m(x)_∞) = A₀ ∩ xᵐA_∞` |
| S7⁺.6 | **genus formula with total δ**: for `m ≫ 0`, `g(F) = 1 + Σ_w (g(κ(w)) − 1) + codim_{Π L(m(x̄)_∞)} H_m` with `H_m = Λ₀ ∩ x̄ᵐΛ_∞` | S7⁺.5, `dim ρ(L_m°) = ℓ(L_m)` (G6.4 and independence of lifts), R7 on `F` and on the `κ(w)`, R5 |
| S7⁺.7 | **localization**: `codim H_m ≤ Σ_y δ_y^{(M)}` for `M ≫ 0` (points `y` = maximal ideals of `Λ₀`, and of `Λ_∞` over `x̄ = ∞`; `O_y = {a : ∃ s ∈ Λ ∖ y, s a ∈ Λ}`), i.e. `W_m ∩ ⋂_y (O_y + K_{M,y}) ⊆ H_m`. With S7.6 this gives the equality `g = 1 + Σ(g_w − 1) + Σ_y δ_y`, and the `δ'` form consumed by `card_le_of_indep` | conductor element `σ ∈ Λ₀` (finiteness of `Π_w Õ_w`, S7.7 `CurveIntegralClosure`); `K_M ⊆ O_y` at the finitely many `y ∋ σ` (CRT in `Λ₀`); `a ∈ O_y ∀ y ⇒ a ∈ Λ₀` |
| S7⁺.8 | **Gauss trees** (bridge; re-scoped as M10): for a finite convex Gauss tree `V` of `C(x)`, a `t ∈ C(x)` with `t⁻¹(w_{0,1}) = V`, and the identification of the normalization of `P¹_t` in `F` with `𝒳'_V` (M10-type uniqueness: a normal model is determined by its vertex set) | open; needed by R5 for `V` and `V ∪ {w_D}` |

**Status (S7⁺.1–S7⁺.7 proved, no S8 input, no completeness of `C`).**
`ChartBasis` (`IsCoord`, `exists_trace_bound`, `exists_chartBasis`, `exists_disc_coords`),
`LaurentSplit` (`exists_laurent_split`), `SectionLift` (`exists_lift`), `SectionGenus`
(`secSpace`, `secSpace_le_piRR`, `exists_finrank_secSpace_eq`, `genus_add_card_sub_one_eq`),
`ChartLocal` (abstract affine charts `IsChart`: `center_isMaximal`, `exists_center_eq`, `locSpace`,
local–global principle `mem_of_forall_mem_sup`, `delta`, counting lemmas
`finrank_le_finrank_add_sum_quot` / `finrank_add_sum_le_of_surj`, twisted jets
`exists_jet_twist`), `SectionLocal` (`exists_red_eq`, `exists_conductor`, `isChart_x`,
`isChart_x_inv`, **`exists_genus_eq_sum_delta`**: for `M ≫ 0`,
`g(F) + #{w} - 1 = Σ_w g(κ(w)) + Σ_y δ_y^{(M)}`, `y` over the closed points of the charts at `0` and
`∞` containing the conductor; every `y` with `δ_y ≠ 0` is among them). ≈ 3.9k lines.
S7⁺.8 is re-scoped as M10 (domination of models with nested vertex sets), not started.

### 9.10 S8.5: local uniformization at type-4 points (Arzdorf–Wewers)

**Sources** (in `.sources/`, gitignored): Arzdorf–Wewers, *Another proof of the semistable
reduction theorem*, arXiv 1211.4624 (`aw/ssredneu.tex`; cited **[AW]**); K. Arzdorf,
*Semistable reduction of prime-cyclic Galois covers*, Diss. Hannover 2012 (`arzdorf/thesis.pdf`,
`thesis.txt`; cited **[KA]**), which contains the proofs of the `p`-cyclic cases that [AW] only
sketches (Matignon's `p`-Taylor expansion in the "formal" form [KA §2.2.2]); Temkin, *Stable
modification of relative curves*, arXiv 0707.3953 §6 (`src-0707.3953/t.tex`; fallback, see the
end of this section); Bosch–Lütkebohmert, *Stable reduction and uniformization of abelian
varieties I*, Math. Ann. 270 (1985), Lemma 2.4 (only through [AW, Lemma 2.4/`BLlem`]).

**What [AW] prove at a type-4 point.** [AW, Thm 2.6 (`diskthm`)]: for a Galois cover
`φ : Y → X` of an open disc with `Y` not a disc, the set `𝒟` of *exhausting* affinoid discs
`D ⊆ X` (`Y ∖ φ⁻¹(D)` a disjoint union of open annuli) has a minimum. For solvable `G` this is
[AW §3] (induction on `|G|`, base cases `ℤ/p` over discs [KA Thm 2.1] and annuli [KA Thm 4.2]).
For general `G` [AW §4] takes the limit point `x = lim_{D ∈ 𝒟} x_D` (`𝒟` is totally ordered,
[AW Lemma 2.7(iii)]) and rules out its four types. **Type 4 is case (4)**: `⋂ 𝒟 = ∅`; for small
`D ∈ 𝒟` the preimage `φ⁻¹(D)` splits into one piece per point of `φ⁻¹(x)` (Berkovich: the local
ring at `x` is henselian), but `φ⁻¹(D)` is connected for exhausting `D` [AW Lemma 4.1(ii)], so
`φ⁻¹(x)` is one point `y`, `G = G_y`, and `G_y` is solvable (at a type-4 point it is the inertia
group of an immediate extension, a `p`-group); then the solvable case gives a minimum of `𝒟`,
contradicting `⋂ 𝒟 = ∅`. So the type-4 case costs: (i) the **Galois reduction**, (ii) the
**splitting** near a type-4 point, (iii) **`G_y` is a `p`-group**, and (iv) the **solvable
(`p`-group) case** of the disc theorem, which in turn needs the `p`-cyclic Kummer analysis over
discs *and annuli*. Everything else of [AW §4] is about types 1–3.

**Target statement (S8.5).** Notation: `ξ` a type-4 valuation of `C(x)` over `v_C` (S8.0,
`GaussLimit.forall_ne_gaussRat`): Gauss points `w_n = w_{a_n, r_n}` with `r_n` strictly
decreasing to `inf_a ξ(x − a)` (not attained), `ξ(f) = w_n(f)` for `n ≥ n_f`
(`GaussLimit.exists_forall_eq_gaussRat`); `U_n = {|x − a_{n+1}| < r_n}` the residue class of `w_n`
containing `ξ` (an open disc), `x_n` its residue point on the residue line of `w_n`, `R_n` the
local ring of the model `{w_n}` at `x_n` (`= O_C[t_n]_{(𝔪, t_n)}`, `t_n = (x − a_{n+1})/c_n`,
`|c_n| = r_n`), `D'_n` its integral closure in `F'` (semi-local; its maximal ideals over
`(𝔪, t_n)` are the points `y` over `x_n` of the normalization of any convex `V ∋ w_n` without
vertices in `U_n`). **S8.5:** *for `F'/C(x)` finite separable there is `N` such that every point
`y` of `D'_N` over `x_N` is a smooth point of the special fibre (one branch, `δ_y = 0`)*; in
particular the hidden genus of `U_N` vanishes (S7 localization), which is what S8.1/S8.6 consume.

**Decision (coordinator, 2026-10): [AW]'s global structure replaces S8.1–S8.4/S8.6.** The
targeted chain for W7 is now: **S7** (δ-count, `wp-tempered-s7`) + **S8 = [AW]** + **S9** (node
lemma) ⇒ W7. S8 in [AW] form:

| # | Statement | Inputs |
|---|---|---|
| S8.A | **improvement induction** [AW §2.4–2.5, Prop 2.8]: start with `V₀ = {w_{0,1}}` (`ℙ¹_{O}`); while the normalization of `𝒳_V` has a non-semistable point over a *critical* point `x` (a smooth point of `𝒳_{V,s}`: admissibility is preserved), add the Gauss point of the minimal exhausting disc of S8.B in the residue class of `x`; the measure `(δ_x, −m_x)` (`m ≤ δ + 1`) decreases lexicographically (R5), so the process stops with all points over `𝒳_{V,s}` semistable | R5, S8.B, S7 |
| S8.B | **disc theorem** [AW Thm 2.6]: for a Galois cover of an open residue disc `U` whose component is not a disc, the exhausting discs `D ⊆ U` have a minimum. Solvable / `p`-group case: L6. General case: the exhausting discs are totally ordered (R3/R4, [AW Lemma 2.7(iii)]); their limit (`DiscLimit`, branch `wp-tempered-s81`, = former S8.1) is of type 1, 2, 3 or 4 [AW Prop 4.2]; type 2 ⇒ L6 for the stabilizer; types 1, 3 ⇒ the stabilizer of the point over the limit is solvable and the limit is ruled out as in [AW §4.4] (= former S8.2 type 1 splitting, S8.4 type 3; at type 3 the decomposition group equals the inertia group (A4) and is solvable: wild part a `p`-group, tame quotient abelian); **type 4 ⇒ L7** | L2, L6, L7, `DiscLimit`, S8.2a, S8.4a/b |
| S8.C | **Galois reduction for the assembly** [AW Prop 2.1 (`relprop1`)]: a semistable `V` for the Galois closure is semistable for every intermediate field (Liu 10.3.48; smooth points: A6, nodes: the analogue of A6 with two branches) | A1, A2, A6, S9 |

Former rows: S8.1 → limits in S8.B (proved part `DiscLimit` kept); S8.2 → case (1) of S8.B;
S8.3 → R4 (BL Lemma 2.4); S8.4 → case (3) of S8.B; S8.6 → S8.A. The hidden-genus function
`h(V)` and König compactness are no longer needed. **Interface requirement on S7:** R5's
comparison formula [AW (2.3)] `δ_y = m_y − |S| + Σ_{V ∈ S} g_V + Σ_{y'} δ_{y'}` needs the genus
formula `g = 1 + Σ (g_V − 1) + Σ_y δ_y` *with equality* for the two models involved (or a local
version of it); S7 currently provides `≤` only (`DeltaGenus`: `g ≥ 1 + Σ(g_V − 1) + Σ δ_y`), and the reverse
inequality is the H⁰ base-change statement (reductions of `L(D)°` fill all special-fibre sections
with the local conditions; analogue of G6.8's trace/Laurent machinery). **New row S7⁺ (≈ 2.5k,
unassigned): `g = 1 + Σ(g_V − 1) + Σ δ_y` for normalizations of Gauss-tree models.** No local
substitute is known: already `δ_y ≥ Σ g_V + Σ δ_{y'} + |S| − m_y` is a lifting statement (gap
conditions on the exceptional fibre `W`). The S8.5 target below is used in the form "type 4
limits of exhausting discs do not occur" (T2′).

**L1. Galois reduction and quotients** (`SemistableReduction/GaloisReduction.lean`: A1–A5
**proved**, ≈ 0.45k lines; A6 waits for S7's `δ`).
`F''/F` finite Galois with group `G` (`F = C(x)` or an intermediate field), `H ≤ G`,
`E = F''^H`.

| # | Statement | Inputs | Size |
|---|---|---|---|
| A1 | **transitivity** (**proved**, `exists_smul_eq`): two valuation subrings `W''₁, W''₂` of `F''` with the same restriction to `F` are conjugate, `W''₂ = σ(W''₁)` for some `σ ∈ G` | integral closure `D` of `W = W''ᵢ ∩ F` in `F''` with the `G`-action, `Algebra.IsInvariant W D G` (`IsGalois.mem_bot_iff_fixed`), Mathlib `Algebra.IsInvariant.exists_smul_of_under_eq` on the centres, `localAt_normChart_eq` (Prüfer: `W''ᵢ` = localization of `D` at its centre) | 0.2k |
| A2 | **quotient charts** (**proved**: `algebraMap_mem_normChart_iff`, `algEquiv_mem_normChart_iff`, `mem_normChart_iff_forall_algEquiv`, fibres `comap_fixedField_eq_iff`; the surjectivity of restriction is Chevalley, as in `vertexSet_surjOn`): for a tower `F ⊆ E ⊆ F''`, `normChart E A` is the preimage of `normChart F'' A` (integrality is tested in `F''`); `normChart F'' A` is `G`-stable and its `H`-invariants are `normChart E A`; the vertex set of the normalization in `E` is the image of that in `F''` under restriction (`lines_normalization_vertexSet` + Chevalley extension), with fibres the `H`-orbits (A1 for `F''/E`) | `ZariskiNormalization`, A1 | 0.3k |
| A3 | **decomposition group** (**proved**: `valuation_apply_eq`, `decompositionGroup`, `decompositionField`, `valuation_decompositionField_apply`): `D_{W''} = {σ : σ(W'') = W''}`; for `σ ∈ D_{W''}`, `W''.valuation (σ x) = W''.valuation x` (an order automorphism of finite order of a linearly ordered group is trivial); hence the hypothesis `hσ` of `Inertia` holds for `F''/F''^{D_{W''}}` | `Inertia` (D1) | 0.2k |
| A4 | **inertia = decomposition at a residually algebraically closed point** (**proved**: `inertia_eq_top`, `exists_pow_eq_of_divisible`, `isPGroup_of_isAlgClosed`, `isPGroup_decompositionGroup`): if `κ(W ∩ F)` is algebraically closed (types 3, 4), `residueHom` has trivial target, so `T = D_{W''}`; with D2 (`isPGroup_inertia`: value group of `W ∩ F''^{D}` divisible — W4 `ramificationIdx_eq_one_of_divisible'` transports divisibility of `v(C^×) = ξ(C(x)^×)` up the finite extension — and `ζ_ℓ ∈ C`) the decomposition group of a type-4 point is a `p`-group | D2, A3 | 0.3k |
| A5 | **Kummer tower** (**proved** for one step: `exists_kummer_generator`): a D4 chain (`PGroupChain.exists_chain`) from `1` to `D_{W''}` gives `F''^{D} = L₀ ⊆ L₁ ⊆ ⋯ ⊆ L_m = F''` with `L_{i+1}/L_i` Galois cyclic of degree `p`, hence (`ζ_p ∈ C`) `L_{i+1} = L_i(y)`, `y^p = f_i` | D4, Mathlib `FieldTheory/KummerExtension` (`isCyclic_tfae`) | 0.2k |
| A6 | **smooth points descend to quotients** (needed because S8.5 is proved for the Galois closure `F''` and used for `F' = F''^H`): if every point of `D''` over `y ∈ D_E` is smooth, so is `y`. Proof: `P''` over `y` with stabilizer `H_{P''}`, unique branch `Q''` on the residue curve `κ''` of `w''`; `|H_{w''}| = [κ'' : κ']` (W4: `e = 1`, no defect, A1) and `H_{w''}` permutes the branches over the branch `Q'` of `y` transitively with stabilizer `H_{P''}`, so `e(Q''|Q') = |H_{P''}|`; for `s ∈ D''` a parameter at `P''` and a unit at the other points over `y` (CRT), `t = N_{F''/E}(s) ∈ D_E` has `ord_{Q''} t̄ = |H_{P''}|`, hence `ord_{Q'} t̄ = 1`; one branch + an element reducing to a uniformizer of it ⇒ `δ_y = 0` ([KA Lemma 1.28] in algebraic form: conductor argument). *Wild caveat*: `D_E ⊗ k ≠ (D'' ⊗ k)^H` in general (`s ↦ ζ_p s`), so the naive invariant-of-special-fibre argument is wrong; the norm argument avoids it | A1, W4, R5 (`degree_poleDivisor`: `Σ e = [κ'' : κ']`), S7 (`δ`), finiteness of the residue normalization | 0.6k; **S7(c) input proved**: `SmoothPoint` (abstract one-branch closedness/jets/uniformizer ⇒ `ρ(R)_P = O_Q`), `SmoothVertex` (vertex chart `DRint 0 1`, maximum principle, reduction, span/fractions/τ), `AffineTwist.exists_eq_of_uniformizer` (on `DRint a c F'`: a reduction to a uniformizer at the only zero `Q` of `t̄` with point `P'` ⇒ every `a ∈ O_Q` is `ρ y/ρ s`, `s ∉ P'`) — **owner: S8.A agent** (`S8Descent.lean`, with the node analogue, as `S8CDescent` O6.6) |

**L2. Splitting at a type-4 point** (replaces Berkovich's "the local ring at `x` is henselian"). **Done**
(`DiscCount`, `Splitting`, ≈ 0.95k lines).

| # | Statement | Inputs | Size |
|---|---|---|---|
| B1 | **disc count is constant on the disc** (**proved**, `DiscCount.sum_natDegree_eq_natTrailingDegree`, `mem_discIdeal_iff`, for the polynomial chart `O_C[t]`, `t = (x − a)/c`): for every rank-one `ν` of `C(x)` centred at `x_n` (types 1–4 inside `U_n`) the centre of `ν` on `R_n ∩ O_C[t_n]` is `(𝔪, t_n)`; hence for `s ∈ D'_n` the count `Σ_{ν' ∣ ν, ν'(s) < 1} [\hat F'_{ν'} : \hat C(x)_ν]` equals `natTrailingDegree (χ_s mod (𝔪, t_n))`, independent of `ν` | S5 machinery verbatim: `LocalGlobal` (any non-archimedean normed `F`, here `F = (C(x), ν)`), `TubeCount.sum_natDegree_eq_natTrailingDegree`, `GaussTube.exists_lift_normPoly` (chart integrally closed) | 0.3k |
| B2 | **disc degree** (**proved**, `DiscCount.discDegree_eq`; centres `center_isMaximal`) `d_y := Σ_{ν' ∣ ν centred at y} [\hat F'_{ν'} : \hat C(x)_ν]` is independent of `ν` (B1 with a separating `s`: in the centre `y`, a unit at the other points over `x_n`; centres are maximal, S4 `center_isMaximal` for the disc chart); `Σ_y d_y = [F' : C(x)]` | B1, R1 (CRT), S4 | 0.3k |
| B3 | **separation for large `n`** (**proved**, `Splitting.exists_center_ne`; on the polynomial chart: the separating element is made integral over `C[x]` by a polynomial multiple normalized to `ξ`-value 1, `exists_nnnorm_eq`): distinct extensions `ξ'₁ ≠ ξ'₂` of `ξ` have distinct centres on `D'_n` for `n ≫ 0` (an `e ∈ F'` with `ξ'₁(e) < 1`, `ξ'₂(e − 1) < 1`, `ξ'(e) ≤ 1` for all `ξ' ∣ ξ` (R1, B3 of §9.4); the coefficients of `χ_e` lie in `R_n` once `U_n` avoids their poles (finitely many classical points, `⋂ U_n = ∅`) and `w_n = ξ` on them (S8.0)) | S8.0, R1 | 0.3k |
| B4 | **splitting** (**proved**: `DiscCount.discDegree_pos` (B4a, every point over `x_n` has positive disc degree at every disc valuation), `Splitting.exists_center_eq`, `exists_center_injective`, `finite_extensions`): for `n ≫ 0`, `ξ' ↦ centre of ξ'` is a bijection from the extensions of `ξ` onto the points `y` over `x_n`, and `d_y = [\hat F'_{ξ'} : \hat C(x)_ξ]`; for `F'` Galois, the stabilizer of `y` is the decomposition group of `ξ'`, a `p`-group (A4) | B2, B3, every `y` over `x_n` is the centre of a valuation over `ξ` (B2: `d_y ≥ 1` computed at `w_{n+1}`, every point of the special fibre lies on a component — G8.1) | 0.3k |

**L3. Discs, annuli and improvements in valuative form** (the rigid notions of [AW §2–3]).
Over `O_C` (not noetherian) completions of local rings are avoided wherever possible; where
[AW]/[KA] use complete noetherian local rings (L3–L5), the finitely many data are descended to
a DVR `O_E`, `E/K` finite (W9 D1–D3e), after which `E` may be enlarged finitely ([AW] does the
same). *Permanence* ([AW Prop 2.3], Epp) is automatic over `C` (`e = 1` at all type-2 points,
value group divisible) and is achieved over `E` by W9 D3 (vertex sets and residue fields
stabilize).

| # | Statement | Inputs | Size |
|---|---|---|---|
| R0 | **local rings of residue classes**: for a smooth point `y` (descended to `O_E`), `\hat{(D'_E)}_y ≅ O_E[[s]]` for `s ∈ D'_E` reducing to a uniformizer of the branch ([KA Lemma 1.28 + 1.29]: a local map of complete noetherian local rings inducing isomorphisms on residue fields and cotangent spaces is an isomorphism); for an ordinary double point `≅ O_E[[u, v]]/(uv − c)` ([KA Lemma 1.30], [Liu 10.3.20]) — the node case is S9 | Mathlib `AdicCompletion`, `PowerSeries`, S9 | 0.6k |
| R1 | **recognition of discs**: one branch + `t` with `v_η(t) = (0, 1)` (rank-two boundary valuation `v_η` = Gauss valuation composed with `ord` at the branch) ⇒ disc with parameter `t` [KA Lemma 1.28]; algebraic form = A6's conductor argument | A6 | **proved** in algebraic form (`BranchRecognition.maximalIdeal_eq_span_of_branch`: `D` local noetherian normal over a DVR, one reduced branch `𝔔` with a finite normalization `V` (kernel `𝔔`, residue field that of `D`) in which `t̄` generates the maximal ideal ⇒ `𝔪_D = (ϖ, t)`; via `mem_span_of_forall_mem` (`(ϖ) = ⋂ 𝔔`, Krull) and Nakayama `surjective_of_finite`); consumed by A6 after descent |
| R2 | **recognition of annuli**: two branches, `N_{B/A}(w) = t^m u`, `gcd(m, n) = 1` ⇒ annulus of thickness `ε/n` [KA Lemmas 1.30, 1.31] | S9 node lemma, R0 | 0.4k; [KA 1.30] **proved** in algebraic form (`BranchRecognition.isOrdinaryDoublePoint_of_branches`: two reduced branches with finite normalizations in which `ū'`, `v̄'` are uniformizers, `u' v' ∈ (ϖ)` ⇒ `IsOrdinaryDoublePoint ϖ u' v' 𝔔₁ 𝔔₂`, the input of `NodeLemma.isAnnulusAt_of_isOrdinaryDoublePoint`); the norm form [KA 1.31] remains (it needs the branch orders of the base parameter, `ord_{Q₁} t̄ = n`, i.e. S6 locally, or R0 on the formal side) |
| R3 | **exhausting discs / separating boundary domains** as statements about Gauss trees: `D = D(a, ρ) ⊆ U_n` is exhausting iff, in the normalization of `{w_n, w_{a,ρ}}`, all points over the node are ordinary double points (S9 / `IsAnnulusAt`); boundary domains likewise for annuli [AW §3.1, KA Def. 1.26] | M7a/M7b, S9 | 0.3k; **proved over `C` (definitions + recognition)**: `AffineTwist.IsExhausting a hc0 hc' hc0' F'` (every maximal ideal of `Rint c' (Aff a c F')` over `tubeIdeal c'` is `GaussTube.IsNodeODP`: one outer, one inner branch (`outerBranches`, `innerBranches`), local ring reaches the fibre product exactly); recognition `isNodeODP_of_params` from parameters of the two branches ([KA 1.30] over `C`, `NodeRecognition.exists_jet₂` + `NodeDouble.exists_fp`); the twist `AffineTwist` (`x ↦ (x − a)/c`, `drintEquiv`, `extAff`) puts the disc chart `DRint a c` and the node chart in `t` on the standard charts. Upward closure (R4(i)) not done: it needs the local structure of the tube of an ODP (S9 over `C`: the extensions of the Gauss points inside the tube are Gauss points in the node coordinate) |
| R4 | **BL Lemma 2.4** (as used in [AW Lemma 2.4/`BLlem`, Lemma 2.7]): (i) a disc containing an exhausting disc is exhausting; (ii) there is `ε₀ < 1` such that all discs of radius `≥ ε₀` are exhausting; (iii) over a thickness-0 closed annulus `{|t| = ε}` with `D(0, ε)` exhausting the preimage is a disjoint union of thickness-0 annuli, so residue classes of it pull back to disjoint unions of discs. Valuative proof: (ii) is S8.3 (a type-5 direction at `w_n`: the annulus between `w_n` and a nearby Gauss point carries no hidden genus / has annulus preimage), (i) and (iii) follow from S5/S6 (tube degrees, one branch per side) | S8.3, S5, S6 | 0.4k; **(i) proved over `C` modulo the open obligation O1** (`GaussTube.isNodeODP_of_le`, `NodeUpward`/`NodeUpwardMain`): for `|c'| < |c''| < 1`, a point `P''` of `Rint c'' F'` over the node lying over a point `P'` of `Rint c' F'` with one outer branch and exact node data `NodeData` is `IsNodeODP` (outer branches of `P''` ⊆ those of `P'`; every point is a centre, `exists_center_eq`; S6 at both vertices; at an inner branch `(c''/x)‾ = λ v̄₀^d`, so the vertex count `d` forces one inner branch with `v̄₀` a uniformizer; parameters `σ_u u` and `σ σ_v (κ/γ) v`, `κ^d = c''`). **(ii) proved over `C`, unconditionally** (`NearBoundary`: `GaussTube.belowGerm`, `exists_near_isNodeODP`, `exists_near_nodeData`): near the outer boundary the exact node data are constructed directly (germ bridge `isGermLE_of_red`, integrality near the boundary `exists_valuation_le_one_near` via residue norms + Lagrange interpolation, pole clearing `exists_tau_near`, residue lifting `exists_lift_red`, reusable `nonempty_nodeData_of_coord`), so (ii) needs neither O1 nor `DefinedOverDVR`; (iii) open |
| O1 | **open obligation (interim hypothesis of R4)**: under `DefinedOverDVR C F'` (`DefinedOverDVR.lean`), every `IsNodeODP` point `P'` of `Rint c F'` with outer branch `b₁` admits `GaussTube.NodeData hc P' b₁` (descent to `O_E` (S7.9) + `IsOrdinaryDoublePoint.exists_node`). R4 counts as done for the targeted chain only once O1 is proved | owner: W8′ agent (`ExactNodeData.lean`, branch `wp-tempered-o1`) | — |
| R5 | **improvements** [AW Def 2.5, Lemma 2.6, Lemma 2.9]: genus formula `g = 1 + Σ(g_V − 1) + Σ δ_y` (S7), the comparison (`improveeq1`) `δ_y = m_y − |S| + Σ_{V ∈ S} g_V + Σ_{y' ∈ U} δ_{y'}` for the modification at an exhausting disc; *not an improvement* ⇒ unique singular point `y'`, rational unibranch components; *minimal exhausting* ⇔ improvement; termination measure `(δ, −m)` with `m ≤ δ + 1` | S7, G6.7 (`δ` as gluing conditions) | 0.6k |

**L4. `p`-cyclic Kummer covers of a disc** ([KA §2], mixed characteristic, `ζ_p ∈ C`).
**Decision (2026-10): no completions of local rings (no R0); power series over the field `C`
(complete, algebraically closed — the S7/S8 setting), Gauss norms `PowerSeries.gaussNorm`.**
The base of a Kummer step is a degree-one disc point `P'` of an intermediate field `L/C(x)`
(B5); its functions are identified with power series by the **bridge** (`DiscGerm`, **proved**):
for `y ∈ R'` there is `G = Σ aᵢ tⁱ`, `|aᵢ| ≤ 1`, with `Σ_{i<N} aᵢ tⁱ → y` at the extension centred
at `P'` of every disc valuation (any type), and `w'(y) = sup_i |aᵢ| |l|^i` at the Gauss point
`w_{a,|lc|}` (`exists_germ`, `exists_germ_gaussNorm`; construction by traces
`Tr(Nⁿ(e) y) ∈ O_C[t]` of the idempotent iteration `N(u) = 3u² − 2u³` of a separating `e`, whose
coefficients converge — no Hensel, no completion of local rings). In the rows below `A = O_C⟦t⟧`
(power series with integral coefficients, Gauss norms at radii `< 1`), `f ∈ A^×` the germ of the
Kummer generator; statements about the cover are transported back to valuations by the bridge.

| # | Statement | Inputs | Size |
|---|---|---|---|
| K1 | **best approximation** [KA Prop 2.2, Cor 2.4/2.5, 2.16, 2.23] (**power-series part proved**, `CriticalRadius.exists_precise`, over any algebraically closed ultrametric `C`, no completeness): at a radius `‖l‖ < 1` (where suprema are attained, `exists_dom`) either `f` is approximable by `p`-th powers up to every bound `> A = ‖γ‖^p` (degenerate: split or Artin–Schreier at the Gauss point), or there is a *precise* `h`: `g = f - h^p`, `g₀ = 0`, `Dom (term g l) M m` (maximum `M > A` first attained at `m`, `p ∤ m`), `p`-indices strictly below the segment `P'₀P_m`; `(M, m)` is independent of the precise `h` (K2 both ways). `pBound_eq`: `pBound = A^(1 - 1/p^(n+1))`. *Over `C` the boundary data of the open disc need not be attained, so the analysis is done at a radius `< 1`*; the cover-side statements (`B = A[w]`, one boundary point, disc iff `m = 1`) are transported in K6 | (revised: no normality of `A[w]`) for `h ∈ A` the bridge puts `f - h^p` into the completions at the Gauss points `w_{a,|lc|}`; the extension of the degree-one point there is `K(φ(f)^{1/p})` and its residue extension is read off by F4 (`KummerNormalForm`) at each radius | 0.7k |
| K2 | **recognizing best approximations** (**proved**, `KummerDisc.not_better`, over `C` without attained suprema) [KA Lemma 2.7, Rem 2.8]: `p ∤ m̃` ⇒ `v_η(f − h̃^p) = (μ, m)`; stable under algebraic base change | binomial expansion | 0.1k |
| K3 | **formal `p`-Taylor expansion** (**proved**, `PTaylor.exists_pTaylor`, over the coefficient field `C`; Matignon [Mat03], [KA Def 2.9, Lemma 2.10, Prop 2.12]): for every level `n` there are `h ∈ A^×` with `f − h^p = Σ a'ᵢ tⁱ`, `a'₀ = 0`, `v(a'_{pj}) ≥ ν_n = 1 + 1/p + ⋯ + 1/pⁿ`. *Only this part of Matignon's theory is used* (no equidistant geometry, no global `p`-Taylor polynomials). Over `O_C` it is elementary (`C` perfect: `b_j = a_{pj}^{1/p}`, induction on `n` with the binomial estimate `v(binom(p, j)) ≥ 1`); over `O_E` it needs the explicit finite extensions of [KA Lemma 2.10] (`p`-power roots of a uniformizer) | `PowerSeries` over `O_C`/`O_E` | 0.4k |
| K4 | **level suffices** [KA Cor 2.16, 2.23, Prop 2.28, Def 2.30] (**proved**, `CriticalRadius.exists_crit` for sequences, `exists_critRadius` for series): for precise data the modified Newton polygon (virtual start `(0, A)`) has critical radius `θ₀ ∈ |C^×|` (`‖l₀‖`): on `(‖l₀‖, 1)` the index `m` strictly dominates with value `> A`; at `‖l₀‖` all terms are `≤`, `p`-indices `<`, and either value `= A` (Artin–Schreier, `P_l = P'₀`) or value `> A` with smallest dominant index `k`, `0 < k < m`, `p ∤ k` | finite maxima (no Newton polygons of power series needed) | 0.6k |
| K5 | **good centre** [KA Prop 2.31] (**proved**, `GoodCentre.exists_good_centre`, ≈ 1.2k lines, over algebraically closed `C`, no completeness): for a polynomial `f` (the germ enters through DiscGerm's polynomial approximants, which give the same local Kummer extensions inside `|t| ≤ ‖l‖`) with data `(M, m)`, `m ≥ 2`, `p ∤ m`, `A < M ≤ 1`, there are `‖τ‖ < 1` and `h` with `f(τ + s) − h^p` precise with the same data and **linear coefficient `0`**. Proof replaces KA's integral extensions of `O⟦T⟧` + Weierstrass by: the generic truncated `p`-Taylor algorithm with symbolic roots over `C[T]` (`genH`, `genE`), the iterated `μ_p`-norm of the linear coefficient (`normAll`, a polynomial in the centre), its estimate `‖a(τ) − f'(τ)^(p^N)‖ < M^(p^N)` on the closed disc (all root choices, `conc_inv`), maximum modulus and Gauss's lemma ⇒ `a` has a root `‖τ‖ < 1`; at the root some root choice kills the linear coefficient | finite maxima; no Newton polygons of power series | 0.6k |
| K6 | **minimal exhausting disc** [KA Prop 2.33 = AW Prop 3.4]: `D = {v(t) ≥ ρ₀}` is exhausting (on `X ∖ D`: `f − h^p = c₁^p t^m u₁`, R2) and minimal: on `D` the reduction is `w̄^p + c̄ w̄ = ḡ` (Artin–Schreier, genus `(p−1)(m−1)/2 > 0`) if `P_l = P'₀`, else `w̄^p = ḡ` with `t̄^l ∣ ḡ`, `1 < l < m`, `p ∤ lm`, singular at ≥ 2 zeros of `dḡ`; R5 ⇒ improvement | K1–K5, R2, R5, W4 F4 (`KummerNormalForm`: the residue extension at the Gauss point of `D`) | 0.6k |

**L5. `p`-cyclic Kummer covers of an annulus** ([KA §4], [AW §3.3] only sketches it: "the
annulus case uses the same methods, but is slightly more complicated"). `A = O[[t, s]]/(ts − c)`,
`f = c' t^m u` (Laurent series), separating boundary domains: [KA Thm 4.2]. Same steps as K1–K6
with formal Laurent series (`p`-Taylor for Laurent series [KA §4.5.1, uses the stronger estimate
of Lemma 2.10], two boundary valuations, [KA Lemma 1.33] for maximality). Estimate **1.5–2k**.
Needed only inside the induction step of L6 (the quotient `Y/H` may be an annulus over a disc);
see the fallback paragraph for avoiding it at type 4.

**L6. The `p`-group (solvable) case** [AW Prop 3.1 (`solvprop`) §3.2, §3.5].

| # | Statement | Inputs | Size |
|---|---|---|---|
| P1 | reduction to `≤ 1` branch point (disc) / `0` (annulus) by passing to the maximal branch-point-free boundary domain and induction on the number of branch points [AW §3.2] | R3, R4 | 0.3k |
| P2 | `ℓ ≠ p` and the trivial cases [AW §3.3] (tame Kummer, Hensel) — for `p`-groups only the `ℓ = p` case occurs, but the branch-point argument of P1 uses the "no branch point" claim of [AW §3.3] | Kummer, W8 `KummerNode` | 0.2k |
| P3 | **induction step** [AW §3.5]: `H ◁ G` of index `p` (D4), `Z = Y/H` (A2: an intermediate field), the maximal separating boundary domain of `Z → X`, a component `Y₁` over it with stabilizer `G₁`, `H₁ = G₁ ∩ H`, the `H₁`-cover `Y₁ → Z₁` (disc or annulus); uniqueness ⇒ `G₁/H₁`-stability; the image is maximal separating for `φ` | A1, A2, K6, L5 | 0.4k |

**L7. Type-4 conclusion.**

| # | Statement | Inputs | Size |
|---|---|---|---|
| T1 | for `F''` Galois and `n ≫ 0` (B4), the component `Y_n` of the preimage of `U_n` through `ξ''` is a Galois cover of `U_n` with group `D_{ξ''}`, a `p`-group (A4) | B4, A4 | 0.1k |
| T2 | **descent**: apply L6 to `Y_n → U_n`: either `Y_n` is a disc (done), or there is a minimal exhausting disc `D_min ⊂ U_n` (a type-2 point). If `ξ ∉ D_min`, then `U_{n'} ⊆ U_n ∖ D_min` for `n' ≫ 0` (`⋂ U_n = ∅` and discs are nested or disjoint), whose preimage is a union of annuli; R4(iii) ⇒ the points over `x_{n'}` are smooth. If `ξ ∈ D_min`, then `U_{n'}` lies in the residue class `X'` of `D_min` containing `ξ`, the component over `X'` is again a `p`-group cover of a disc, and its point has strictly smaller `(δ, −m)` (R5: minimal ⇒ improvement). The measure is well-founded (`m ≤ δ + 1`), so after finitely many steps the component is a disc | L6, R4, R5, S8.0 | 0.4k |
| T0 | **exhausting discs have connected preimage** [AW Lemma 2.7(i), 4.1(ii)]: for `D` exhausting, the components over the Gauss point of `D` form a connected special fibre `W` whose points over the outer direction are smooth, so `W°` is connected; hence all `w' ∣ w_D` are centred at the same point over the residue point of any `w_n` with `D ⊆ U_n` | `Connectedness` (G6.8), B2, R3 | 0.3k |
| T2′ | **[AW] case (4)** (the form used by S8.B): if the exhausting discs of a Galois cover `Y → U` (`Y` not a disc) shrink to a type-4 `ξ`, then for `D ⊆ U_n` exhausting, T0 + B4 give a single point over `x_n`, so `G = D_{ξ''}` is a `p`-group (A4) and L6 gives a minimum — contradicting `⋂ D = ∅`. (T2 is the equivalent formulation for the pointwise target above.) | T0, B4, A4, L6 | 0.2k |
| T3 | **S8.5 for arbitrary `F'`**: Galois closure `F''`, T2 for every point over `ξ`, A6 for `F' = F''^H` | A6, T2 | 0.1k |

**How type-4 valuations are handled.** Never through a model containing `ξ` (impossible: `ξ` is
not a vertex of any finite tree). `ξ` enters only (a) through S8.0 (`w_n(f) = ξ(f)` for
`n ≥ n_f`), used in B3 and T2 to transfer finitely many inequalities from `ξ` to `w_n`; and
(b) through its completion `\hat C(x)_ξ` in B1/B2, where `LocalGlobal`/`TubeCount` already work
for any rank-one valued field (no Gauss hypothesis); the local degree `[\hat F'_{ξ'} : \hat C(x)_ξ]`
is a defect (`e = f = 1`), no stability/defectlessness of `\hat C(x)_ξ` is needed (it is false).
New completion infrastructure: none for L1–L2; complete noetherian local rings
`O_E[[t]]`, `O_E[[u, v]]/(uv − c)` for L3–L5 (R0), and formal power/Laurent series over `O_E`.

**Where Temkin §6 is the fallback.** (1) *If L5 (annuli, [KA §4]) turns out too costly*: at a
type-4 point the annulus base case can be avoided by inducting along the Kummer tower A5 instead
of [AW §3.5]: each step `L_{i+1}/L_i` is `ℤ/p` with a *unique* point over the restricted type-4
point, and Temkin's analysis of an immediate degree-`p` extension of a type-4 field (§6.3, proof of
Thm `fieldunif`, case `a = 0`: `L = \hat{C(α)}` for `α` with `|α^p + b| < s = inf|b + K^p|`,
Lemmas `epsclose`, `fin`, `212lem`, `lemrank1`) gives a generator; together with B4 for
`F'/C(α)` ("local degree 1 ⇒ smooth points") this yields the disc property without annuli. The
price is a comparison of the neighbourhood bases of `ξ'` in `x`- and `α`-coordinates (hidden
genus must be shown to be monotone under inclusions of residue classes taken in different
coordinates: ≈ 0.8k); estimated 2.5k instead of L5 + P3. (2) *Henselian splitting*: if B3/B4 run
into trouble, Temkin's Lemma `fin` (close isometric embeddings have the same degree) gives the
continuity of local degrees directly. (3) [AW Lemma 4.3] (types 1, 3: `G_y` solvable via
Berkovich's quasi-completeness) is not needed for type 4 (A4 is purely algebraic).

**Estimate.** L1 1.8k, L2 1.2k, L3 2.3k, L4 2.9k, L5 1.5–2k, L6 0.9k, L7 0.6k: **≈ 11–12k
lines** for S8.5 (previous estimate 4–6k was based on Temkin §6 alone and did not count the
disc/annulus infrastructure). With the structural remark above, S8.1, S8.2, S8.4 and S8.6 shrink
to ≈ 1k together (AW §2.5, §4 cases (1)–(3)), so S8 as a whole: **≈ 13–15k**.

### 9.11 The field `C`: algebraic closure vs. its completion (open, found 2026-10)

*Finding.* Two settings for the coefficient field `C` coexist on the targeted chain:
* W9 descent (`GaussDescent`, `ResidueDescent`, D3e) needs `C` **algebraic** over `K`
  (`[Algebra.IsAlgebraic K C]`: Gauss data and the finitely many generators lie in a finite
  subextension; the tree chart over `O_C` is the union of those over the `O_j`);
* W6 sharp genus (`TypeTwo`, `SharpGenus`, `Connectedness`) and S8.5 (`DiscGerm`, the power-series
  bridge of L4) assume `C` **complete** (`[CompleteSpace C] [IsAlgClosed C]`).
No field satisfies both (for `K` discretely valued, `K̄` is not complete), and Mathlib does not
prove that the completion `\widehat{K̄}` is algebraically closed (`PadicComplex` has no
`IsAlgClosed` instance). The W10 assembly therefore needs a bridge:

| # | Statement | Status |
|---|---|---|
| C0 | `IsAlgClosed (UniformSpace.Completion K̄)` for `K̄` algebraically closed nonarchimedean valued of characteristic `0` (continuity of roots + Krasner) | **proved** (`SemistableReduction/CompletionAlgClosed`: `UniformSpace.Completion.isAlgClosed`, from Mathlib's `IsAlgClosed.of_denseRange`; instances `IsUltrametricDist`, `CharZero`, `NontriviallyNormedField` on the completion) |
| C1 | (dropped by the revised decision below) **Transfer `K̄ → Ĉ`**: for `F'/K̄(x)` finite, `F'_Ĉ = F' ⊗_{K̄(x)} Ĉ(x)` (a field); restriction is a bijection between type-2 points of `F'_Ĉ` with radius in `|K̄^×|` and type-2 points of `F'` (centres approximated by density, W2), with residue fields equal; consequently vertex sets, residue genera, `δ`, and the node/smooth-point data (`IsNodeODP`, exact node data) transfer, and the generators exposed for D3e can be chosen in `F'` | open |
**Decision (coordinator, 2026-10).** C0 first (generic, upstreamable; then W4/W6/DiscGerm apply to
`Ĉ = \widehat{K̄}` while W9 works over `K̄`); C1 only as a thin transfer layer where the W10 assembly
needs it; C2 (dropping completeness) only where it is trivially unused. Owner: agent `cbridge`
(branch `wp-tempered-cbridge`).

**Phase 1 finding and revised decision (2026-10).** C0 is essentially in Mathlib
(`IsAlgClosed.of_denseRange`; only the instances `IsUltrametricDist`, `NontriviallyNormedField`,
`CharZero` of the completion are missing). Completeness of `C` is genuinely used only in W6's
`no_split` (`Connectedness`; inherited by `SharpGenus`, `TypeTwo`) and in `DiscGerm.exists_germ`.
**Targeted setting: `C` algebraically closed (char 0, `‖p‖ < 1`), no completeness**, so W9 descent
works over `K̄` and C1 is not needed. `Ĉ` (algebraically closed by C0) is used inside proofs as an
auxiliary coefficient field: `no_split` over algebraically closed `C` (limits in `F ⊗_C Ĉ`, plus
"`F ⊗_C L` has no nontrivial idempotents"), `DiscGerm` with germs in `PowerSeries Ĉ`, K5 by
Weierstrass over `Ĉ` and approximation of the centre in `C`.

Alternatively C1 is avoided where a `Ĉ`-statement has a proof valid for algebraically closed `C`
(as W4: "completeness of `C` is not needed").

*Where completeness is used (audit, 2026-10).* In W6 only through `GaussFibre.no_split`
(`Connectedness`: the coefficients of the traces `Tr(Nⁿ(e) d_k)` converge in `C`,
`exists_tendsto_sup_sub`); `cut`/`sum_genus_le` (`SharpGenus`) and `TypeTwo.sum_genus_le`/
`card_le_genus` inherit it, W4 and G6.3 (`finite_ext`, `sum_inertiaDeg_eq`,
`exists_orthonormal_basis`) do not use it. In S8.5 only in `DiscGerm.exists_germ` (the germ's
coefficients are limits; they need not lie in `K̄`). **Planned thin bridge (C2′)**: prove
`no_split` for `C` algebraically closed by taking the coefficient limits in `Ĉ` (the limit idempotent
lies in `F ⊗_C Ĉ`, which has no nontrivial idempotents for `C` algebraically closed: Nullstellensatz
points of a finitely generated subalgebra), after which W6 holds over `K̄`; `DiscGerm` with germs in
`PowerSeries Ĉ` when a consumer needs it over `K̄`.

*Status (2026-10).* **`no_split` over algebraically closed `C` proved**, `CompleteSpace C` removed from
`Connectedness`, `SharpGenus`, `TypeTwo` (W6 now holds over `K̄`): `SemistableReduction/
TensorIdempotent` — `eq_zero_or_eq_one_of_isIdempotentElem` (idempotents of `L ⊗[C] F` are `0`, `1`
for fields `F`, `L` over algebraically closed `C`; points of `C[Xᵢ]/ker` by Mathlib's
Nullstellensatz `IsPrime.vanishingIdeal_zeroLocus`), `exists_tendsto_of_approx_idempotent`
(Cauchy coordinates of approximate idempotents in a fixed finite family converge to those of `0` or
`1`; limit in `Ĉ ⊗[C] F`); `GaussFibre.no_split` truncates the traces at degree `D'`, takes a common
denominator `h` of the structure constants and applies it. **`DiscGerm` done**: `exists_germ`,
`exists_germ_gaussNorm` no longer assume `CompleteSpace C` (nor `IsAlgClosed C`); they return the
approximants `Qₙ ∈ O_C[t]` (converging to `y` at every disc valuation) and the germ
`G : PowerSeries Ĉ` (`Qₙ → G` uniformly on `|t| ≤ |l| < 1`, value of `y` at `w_{a,|lc|}` = Gauss
norm of `G`). No `CompleteSpace C` remains in `SemistableReduction`.

### 9.12 Open obligations (must be discharged before anything downstream is called proved)

| # | Obligation | Discharged by | Status |
|---|---|---|---|
| O1 | R4's interim **exact node data** hypothesis (`u v = γ`, `σ x = e u^d`, `ord_{Q₁} ū = 1` at points over the node) | (a1): S7(b)/S7.9 descent to `IsOrdinaryDoublePoint` over `O_E` + `NodeDeformation.exists_node`, under `DefinedOverDVR F'` — owner: W8′ agent (`wp-tempered-o1`) | open |
| O2 | `DefinedOverDVR` passes to intermediate fields of the Galois closure | R4 step 3 | open |
| O5 | S7⁺.8: identification of the normalized `P¹_t`-model with the Gauss-tree model `𝒳'_V` when `t⁻¹(η) = V` (and existence of such `t`), unless R5 is restated on `t`-models | S7⁺ (after S7⁺.7); needed by S8.A (global induction: `h(V) > 0 ⇒ δ > 0` somewhere on `𝒳'_V`), **not** by R5 (R5 runs on the two local `t`-models `P¹_s`, `P¹_{s + c'/s}`) | open |
| O3 | `IsUnfolded` output of `Statement.StrongComponent` | — | **dropped**: the targeted W10 statement is now `Statement.StrongA`, which has no component/W-model clause |
| O6 | S8.A (AW global improvement induction on Gauss trees) ⇒ **`W7.Statement`** (`SemistableReduction/W7Statement.lean`, agreed with S7 and the W10 assembler, 2026-10): for a finite family `F' k / C(x)` (`C` algebraically closed, char 0, `‖p‖ < 1`, not complete) and discs `V₀`, a convex reduced Gauss tree `V ⊇ V₀` (disc-wise, `W7.DiscsLE`) with `W7.IsSemistableTree` for every `F' k` (node points of edge charts `Rint (c_j/c_m) (Aff a_j c_m F')` are `IsNodeODP`; points of vertex charts off the child directions and over `∞` of the root are `SmoothVertex.IsDiscSmooth`; no fixed `ϖ`), and **equivariance**: `τ V₀ = V₀` ⇒ `τ V = V` for isometric `τ ∈ Aut(C)` extending to a `τ`-semilinear automorphism of `Π F' k`. Replaces the monotone form (`h(V) = 0` does not imply semistability: points with `r ≥ 3` branches and `δ = r − 1`). Proof plan: canonical iteration "add `D_min` at all bad points simultaneously" (AW improvement, `D_min` unique), equivariance by transport invariance of `IsNodeODP`/`IsDiscSmooth`/exhausting | S8.A agent (`wp-tempered-s8a`) | statement fixed; **global argument proved modulo the interfaces**: `W7.statement_of_interfaces : GaloisInputs → S8CReduction → W7.Statement` (`S8Main`; `BallTree`, `S8Global`, `S8Assembly`, `S8Equivariance`; axioms: propext, choice, Quot.sound). Open: O6.1–O6.6, O10 |
| O6.1 | `S8A.S8BMinFor` (S8.B, [AW Thm 2.6]): for `F/C(x)` finite Galois, a bad open residue ball `ball b ‖c‖` (`¬ BallGood`) contains a smallest exhausting disc (`IsMinExh`: `EdgeGood D (closedBall b ‖c‖)`, contained in every other) | S8.B agent (`wp-tempered-s8b`): limit argument [AW §4] in `S8BLimit` | **reduced** to O6.1a–h (`S8A.s8bMinFor_of_inputs : S8BLimitInputs C F → S8BMinFor C F`; no Galois hypothesis used) |
| O6.1a | `S8A.R4ExFor`: every residue ball contains an exhausting disc (weakest form of R4(ii)) | R4 agent (`a4a2998`, R4(ii) on `wp-tempered-s81`) | open |
| O6.1b | `S8A.ExhInterFor` ([AW Lemma 2.7(iii)]): two exhausting discs of a bad residue ball intersect | S8.B agent (via O11g and goodness off an exhausting disc; δ-count route shared with `a89e`) | open |
| O6.1c | `S8A.L7For` ([AW §4 case (4)], type 4): pairwise intersecting exhausting discs of a bad ball have a common point (`⋂₀ ExhSet ≠ ∅`; includes limits at points of `Ĉ ∖ C`) | S8.5 agent (`ab3ef`, L7 via B4, T0, A4, L6) | open |
| O6.1d | `S8A.O11For`: the (⇐) direction of O11 verbatim (`ExhaustGluing.isExhausting_iff_of_le`); `S8A.edgeGood_glue` is its `EdgeGood` form | M10/O9 agent (O11) | open |
| O6.1e | `S8A.GoodGluingFor` (O11g): `closedBall a ‖e‖ ⊊ ball a ‖u‖ ⊆ B`, `closedBall a ‖e‖` exhausting in `B`, `ball a ‖u‖` good ⇒ `B` good. Bridge: single-centre O11g `ExhaustGluing.discSmooth_iff_of_le` (`wp-tempered-m10` 1046e8a, under its named hypotheses) + representation independence `S8A.discGood_iff_of_ball_eq` (O6.5) | M10/O9 agent (O11g) + S8.A agent (O6.5) | open |
| O6.1f | `S8A.ClassicalGoodFor` (S8.2, type 1): for every `a ∈ C` the residue balls `ball a ‖c‖`, `‖c‖ ≤ s₀`, are good | S8.B agent (SplitDisc + Kummer base change + DiscCount + `exists_eq_of_uniformizer`) | **reduced** (`ClassicalSmooth.classicalGoodFor_of`, `TypeOneGerm`) to O6.1f(i) `KummerUnramFor` (Kummer base change; owner O1 agent `a79e902`) and O6.1f(iii) `A6For` (A6 in its owner's form; owner S8.5 agent); unramified case (`ballGood_of_unramDatum`) and chart comparison (`PowTransport`) proved |
| O6.1g | `S8A.TypeTwoGermFor` (dual R4(ii), type 2), **chart-wise for a fixed centre** `a₀` (no representation independence of `IsExhausting` needed; the threshold may depend on `a₀`): `∃ ρ' > ‖z‖`, `IsExhausting a₀ d c'` whenever `‖d c'‖ = ‖z‖`, `‖d‖ ≤ ρ'` | S8.B agent (Inv-transport of `IsExhausting` + rescaling (S8.A `isExhausting_iff_of_rescale`) applied to R4(ii)) | **done** (`S8A.typeTwoGermFor`, `TypeTwoGerm.lean`: R4(ii) `GaussTube.belowGerm` for `Inv z (Aff a₀ 1 F)`, rescaling, `nodeGood_of_inv` (`InvSwap`)); needs `[CharZero C]`, `p` with `‖p‖ < 1` |
| O6.1h | `S8A.TypeThreeGermFor` (S8.4, type 3): for `ρ ∉ |C^×|` some `‖c₁‖ < ρ < ρ₂` with `EdgeGood (closedBall a ‖c₁‖) (closedBall a ‖c₂‖)` for `ρ < ‖c₂‖ ≤ ρ₂` | S8.B agent | open. **Status (2026-10):** no existing machinery covers type-3 points (W4/G1–G3 and the R4(ii) germ technique are residue-transcendental). Direct route: (a) dominant monomials at `w_{a,ρ}` (0.2k), (b) defectlessness of the completion at a type-3 point = Kuhlmann's value-transcendental case (C is not spherically complete: algebraic pseudo-Cauchy sequences must converge; adapt `NoImmediate`/`InertiallyGenerated`; 1.5k+, **real mathematical risk**), (c) unramified parameter + germs of norms (0.6k), (d) `NodeData` (`nonempty_nodeData_of_coord`) + `isNodeODP_of_le` + `InvSwap` (0.4k): **3k+**. The Abhyankar equality case does not give (b) (that is the generalized stability theorem). Alternative: AW route via the S8.5 agent's L6 for annuli (p-groups) after a Kummer base change killing the tame part; L5/L6 not started. To check before (b): reduction via `DefinedOverDVR` to a discretely valued base. |
| O6.2 | `S8A.R5MeasureFor` (R5, [AW Lemma 2.6, §2.5]): for `F` Galois, `μ : Set C → ℕ` with `μ B' < μ B` for every bad residue ball `B'` of the smallest exhausting disc of a bad ball `B` (`(δ, −m)` encoded in `ℕ`, `m ≤ δ + 1`) | S8.5 agent (R5 + S7⁺ equality as needed) | open |
| O6.3 | `S8A.FiniteBadFor`: a disc has only finitely many bad residue balls (finitely many non-smooth points over a vertex component) | S7 (S7.7-type conductor finiteness) | open |
| O6.4 | `S8A.InftyGoodFor`: for `‖c‖ ≥ R₀`, every point over the residue class at `∞` of `closedBall 0 ‖c‖` is smooth (chart `c/x`; the assembly centres the root at `0`, `BallTree.famA_eq_zero`) | S8.B agent (type-1 germ at `∞`) | **reduced** (`ClassicalSmooth.inftyGoodFor_of`, `InftyGerm`) to S8.2 for `Inv 1 F`, i.e. to O6.1f(i) `KummerUnramFor` and O6.1f(iii) `A6For` for `Inv 1 F` (S8.B agent) |
| O10 | `S8A.EdgeRepairFor`: for discs `D ⊆ D'`, the breaks `Brk F D D'` (discs strictly between over which no good edge of the segment passes) are finite, and every sub-edge `G₁ ⊊ G₂` of the segment (`D ⊆ G₁`) containing no break is good. Needed because `conv(V₀ ∪ root)` may have bad edges (AW's induction only starts from admissible models; the monotone form is false, example `u² = x`) | M10/O9 agent (`a89e8e036af335e98`), via R4(ii) and dual, type-3 local edges, exhaustion gluing (O11) | open |
| O6.5 | `S8A.TransportFor`: `BallGood`, `EdgeGood` invariant under isometric `τ ∈ Aut(C)` extending to a `τ`-semilinear automorphism of `F` (and under change of representative) | S8.A agent | **done**: `S8A.Transport.transportFor : TransportFor C F` (`S8Transport`; τ-semilinear `semData`, `discGood_semilinear`, `isExhausting_semilinear`); also representative invariance `discGood_iff_of_ball_eq`, rescaling `isExhausting_iff_of_rescale`, `nodeODP_transport_id`. Removed from `GaloisInputs` |
| O6.6 | `S8A.S8CDescent` (S8.C descent, [AW Prop 2.1], L1 A6 + node analogue): for the Galois hull `galoisHull C F'` (compositum of the normal closures of the `F' k` in `AlgebraicClosure C(x)`), `IsSemistableTree V (galoisHull C F') ⇒ IsSemistableTree V (F' k)` for all `k` | S8.5/L1 owner (A6, node analogue) | open; **the rest of S8.C is proved** (`S8Galois`: hull finite Galois, embeddings, lift of semilinear automorphisms `exists_lift`; `s8cReduction_of_descent`; `W7.statement_of_interfaces' : GaloisInputs → S8CDescent → W7.Statement`) |
| O8 | Bridge `TreeData` (S7.5's tree `(a, c, par, chi)` + free directions) ↔ `gaussJoinModel` charts (consumed by W10) | S8.A agent (`TreeBridge`) | **done**: `TreeBridge.treeData` (every convex reduced `(a, c)` over algebraically closed `C` gives tree data with the same `ι, a, c`; edges = minimal strict inclusions `IsEdge`; free points from the infinite residue field); charts as subrings of `F'`: `edgeChart_eq` (S7's `R'_e` = `normChart F' (nodeChart (coord X a_{χe} c_{πe}) c_e)`), `map_rint_aff`, `map_drint_aff`, `drint_eq` (twisted node/vertex charts); vertices: `mem_S_iff`, `valuationSubring_mem_vertexSet` (`S ↪` vertex set of the normalization; surjectivity onto valuation subrings not proved, not needed so far) |
| O4 | §9.11: C0, `no_split` over algebraically closed `C`, `DiscGerm` over `Ĉ`; `CompleteSpace C` removed from the targeted chain | `cbridge` | **done** (C0, `no_split`/W6 over `K̄`, `DiscGerm` with `G : PowerSeries Ĉ`) |
| O9 | Finitely many residue-transcendental centres of a finite-type model over `O` of a curve function field (`[IsCurveFunctionField K F]`, any valuation subring `O`, no properness): `ZariskiModel.finite_residueTranscendental_centres`. No dimension theory and no Krull–Akizuki: some chart generator `t` has transcendental residue (`exists_isResidueTranscendental_of_mem`); `W` restricts on `K(t)` to the Gauss valuation of `t` (`valuation_aeval_eq_of_isResidueTranscendental`, `comap_adjoin_eq_of_isResidueTranscendental`); a valuation subring has finitely many extensions to the finite extension `F/K(t)` (`finite_extensions`: centres in the integral closure `D`, Prüfer, `D/𝔪D` finite-dimensional hence Artinian) | M10 agent (`SemistableReduction/ResidueCentres`) | **done** |
| O10 | **EdgeRepair** in the S8.A form `S8A.EdgeRepairFor` (wp-tempered-s8a 7060859): for a segment `D ⊆ D'` of closed discs the breaks are finite and every sub-edge without a break is good (`EdgeGood`). Needed because the monotone form of W7 is false (S8.A agent: `u² = x`, `V' = {w_{0,1}, w_{b,r}}`, `r < |b| < 1`) and W10 needs `∀ V₀ ∃ V ⊇ V₀` | M10 agent (`SemistableReduction/EdgeRepair`) | **proved modulo named hypotheses**: `EdgeRepair.edgeRepairFor` from (T⇒) `TubeOfExhausting`, (T⇐) `ExhaustingOfTube` (O11/O12), **R4(ii)** `BelowGerm C F` (all `D(a,|cc'|)`, `|e| ≤ |c'| < 1`, exhausting in `|x-a| < |c|`; R4 agent, open), its **dual** `AboveGerm C F` (open; S8.B agent via `Inv`-transport) and the **type-3 germ** `TypeThreeGerm C F` (= `S8A.TypeThreeGermFor`, S8.B agent, open). Under (T⇔) an edge is good iff all radii of its annulus are clean (`Clean`, pointwise in the radius), so the second clause needs no gluing; finiteness by compactness of `[r(D), r(D')]` and density of `|C^×|` |
| O11 | **Gluing** of exhaustion: `D ⊂ D(a,|ce|) ⊂ U' ⊂ U`, `D(a,|ce|)` exhausting in `U` ⇒ (`D` exhausting in `U` ⇔ in `U'`) (S8.5 K6, S8.B, O10); companion **O11g**: same configuration ⇒ (`U` good ⇔ `U'` good) | M10 agent (`SemistableReduction/ExhaustGluing`) | **proved modulo named hypotheses**: `ExhaustGluing.isExhausting_iff_of_le`, `discSmooth_iff_of_le` are formal gluings over overlapping segments of the valuative conditions `TubeCond a c c'` (every Gauss point of the open annulus `|c'| < |t| < 1`, `t = (x-a)/c`: extensions with rational residue curve and one point over `t̄ = ∞`, plus one over `t̄ = 0` on the skeleton, for every centre of the open disc of that radius) and `DiscCond a c` (every Gauss point of `|t| < 1`: rational, one point over `∞`). Consumed: **(T⇒)** `TubeOfExhausting C F'` (exhausting ⇒ `TubeCond`) — **skeleton clause proved** (`TubeSkeleton`: `ExhaustGluing.isTubeCircle_of_exhausting`, `tube_of_ext`; `tubeOfExhausting` assembles (T⇒) from the named hypotheses `NodeDataOfODP C F'` (exact node data at `IsNodeODP` node points of every twist; to be discharged by O1 under `DefinedOverDVR`) and `OffSkeletonOfExhausting C F'` (off-skeleton clause; open, needs the local lemma (L): the residue class of a smooth point is an open disc); open and **(D⇒)** `DiscCondOfSmooth C F'` (good disc ⇒ `DiscCond`); **(T⇐)/(D⇐)** are O12. Also proved: `mem_rint_iff_and` (`Rint c' = Rint e ∩ Rint(c'/u)`) |
| O12 | **(T⇐)** `ExhaustGluing.ExhaustingOfTube C F'`: `∀ a c c' (hc : c ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0), TubeCond F' a hc c' → IsExhausting a hc hc' hc0' F'` (an open annulus satisfying the valuative tube condition has only ordinary double points over its node), and **(D⇐)** `SmoothOfDiscCond C F'`: `∀ a c hc, DiscCond F' a hc → DiscSmooth F' a hc`. Not obtainable from S7's global δ-count for the two-vertex model (the reverse inequality is global); expected from the local improvement formula R5 (`δ_y = m_y − |S| + Σ g_V + Σ δ_{y'}`) | S8.A agent (R5) | M10 agent (from S8.A) | open; **plan** (R5 + O12, agreed with the lead): (1) *local δ-formula* (AW 2.3) by subtracting S7⁺ for `ℙ¹_s` and `ℙ¹_t`, `t = s + c/s`: done so far — `TwoVertex` (`ψ : C(t) → C(x)`, the Gauss point of `t` has exactly the extensions `w_{0,1}`, `w_{0,|c|}`, `extU`/`extD`/`ext_cases`; the twist `TwoV c F'` is finite over `C(X)`) and `SectionLocal.genus_eq_sum_delta_of_conductor` (S7⁺ for arbitrary conductors, so conductors of the two models can be chosen with common points: products `σ τ`); to do — (a) transport of places along residue-field isomorphisms (`CurvePlace` comap; `valuation`, `res`), (b) an abstract locality lemma for `ChartLocal.delta` (branches, centres and `δ` agree at points where the two charts agree after inverting a unit `u`, here `u = s̄` resp. `s̄⁻¹`; inputs: `s^N f ∈ intRing s` for `f ∈ intRing t`, `s^M g ∈ intRing t` for `g ∈ intRing s`), (c) assembly `Σ_{x/s̄=0} δ_x = Σ_node δ + Σ_{D-mid} δ + Σ_{D,∞} δ + Σ_{w∣w_D} g(κ_w) − |S_D|`; (2) (D⇐) from DiscCond + `ClassicalGoodFor` (S8.B, type-1 germ); (3) (T⇐): `f(ρ)` = total δ of `M_ρ` over `t̄ = 0` is ℕ-valued and monotone (`f(r) − f(r') = Σ_P (out_P − 1) + Σ_P (δ_P − r_P + 1)` under TubeCond and (D⇐)), locally constant by the germs (BelowGerm, AboveGerm, TypeThreeGerm), hence `δ_P = r_P − 1`, `r_P = 2`, IsNodeODP by the jets route; (4) R5MeasureFor from the formula (AW Lemma 2.6/2.9). Estimate 6–9k lines |
| O12′ | (lead's note on O12) **(T⇐) valuative tube characterization**: if every intermediate Gauss point of an annulus has extensions with rational residue curves and exactly two branches in the tube directions (plus endpoint branch conditions), every node point of the normalized node chart is `IsNodeODP`. Consumed by O11 (⇐) and O10. The global δ-count does not localize; expected from R5's local formula + S7 jets | S8.A agent (with R5, O6.2) | open |
| O7 | W10 assembly: `W7.Statement` + W9 descent ⇒ **`Statement.StrongA`** (the targeted W10; D3e, S9 over `O_{K'}`, M9, actions, domination) | André agent (`wp-tempered-w10`) | open |
| E1 | (untargeted extension) equal characteristic `0`: a tame W7 (all covers tame, Kummer) to extend `StrongA` and Theorem A to residue characteristic `0` | — | not planned |

