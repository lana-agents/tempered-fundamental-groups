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
| H5 | **targeted form `Statement.HarmonicW`** (W-models over one x-line, `WModel.lean`; two bases `O' ⊆ O''`, ramification `e`): the arbitrary-model `HarmonicGeneral` needs étale-local positions (fibre products of schemes), so it is untargeted. For W-models positions are global: `pos(W) = W(s)` for the base edge coordinate `s ∈ K(x)`; a node with `s = ε ϖ^α u^d` spans `[α, α + d n]` (`exponent_eq_of_chart`, `IsBranchNode.positions`), so (H2) is the telescoping inequality (`abs_sub_le_sum_of_branchNodes`, **proved** at valuation level, `ZariskiHarmonic.lean`); (H1) monotone walks by edge lifting (points of the normalization over base nodes are nodes, W7 (c); finiteness of `𝒳'_V → 𝒳_V`); (H3) from W7 (c). Input from W7's S9: `IsBranchNode` (node coordinates and the two branch vertices) at every point over a base edge | valuative core done; Zariski assembly planned, 1k |
| H6 | scheme transfer (M9b/M9c: `chartOpen`, `chartEquiv`, `exists_projModelCode_normalization`): node points / components / thicknesses / local degrees of `projModelCode` = those of the Zariski model; discharges `IsHarmonic` (`Simultaneous`) and `HarmonicW` | planned, 1.5k |
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
| M10 | the paper's full W5 for arbitrary `F`: every finite nonempty set of type-2 valuations is the vertex set of a unique normal model (needs contraction of the extra components of M6 over `V'`; uniqueness: a normal model is determined by its local rings) | not needed downstream (W7 chooses vertex sets as preimages of `ℙ¹` vertex sets, M6); planned only if required | 1k+ |

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
| S9 | **node lemma**: a closed point `P'` with `δ' = 0`, two branches (from `w'₁`, `w'₂`) and local degree `d` over the node: choose `u' ∈ \hat R'_{P'}` reducing to uniformizers of both branches (possible since the special fibre is an ordinary double point); `O_C[u', c'/u'] → \hat R'_{P'}` is finite of degree `1` (S5 for the subfield `C(u')`, whose Gauss points restrict from `w'_i` by W2), both normal ⇒ isomorphism after completion; descend to an étale neighbourhood (M7c `exists_awayChart_eq`) ⇒ `IsAnnulusAt`; `u = ε u'^d` by S1 for the norm | S5, M7c, `Node` | planned | 0.8k |
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

**S9 in witness form (for W10's generator descent).** The node lemma will be stated as: for a
point `P'` over the node of thickness `c` (`x · (c/x) = c`) with tube degree `d`, there are
**finitely many elements** `u', v', ε, ε', h ∈ F'` and `c' ∈ O_C` such that
1. `u' v' = c'`, `x = ε u'^d`, `c/x = ε' v'^d` (identities in `F'`);
2. `ε, ε', ε⁻¹, ε'⁻¹, h⁻¹` and finitely many listed generators `b_1, …, b_m` of the chart
   `A' := O_C[u', v'][1/h]` are given as explicit polynomials in `u', v', 1/h` with coefficients
   in `O_C` (identities in `F'`), and conversely `u', v'` are integral over `O_C[x, c/x]` via
   explicit monic equations with coefficients in `O_C[x, c/x]`;
3. `F' = C(x)(u')` with an explicit minimal-polynomial identity, and `P'` is the centre of the
   ideal `(u', v', 𝔪)` of `A'`.
4. **branch data for W8′ H5** (`ZariskiHarmonic.IsBranchNode ϖ P u' v' n W₁ W₂` on `wp-w8prime`):
   `u' v' = ϖⁿ` (after rescaling `c'` by a unit), the local ring `P` of the point lies in the
   valuation rings `W₁ = O_{w'₁}` (outer branch, `w'₁(u') = 1`) and `W₂ = O_{w'₂}` (inner branch,
   `w'₂(v') = 1`), and **uniqueness**: `W₁`, `W₂` are the only vertices whose valuation rings
   contain `P` (S6: the tube degree of `P'` equals its vertex degree on each side, and the two
   chosen branches already account for it); the base coordinate is `x = ε ϖ^α u'^d` with `ε` a
   unit of `P`.
Read over any subfield `E` (finite over `K`) containing all coefficients, the same identities
show that `O_E[u', v']/(u'v' − c')[1/h] ≅ A'_E` is a localization of the normalization of the node
chart over `O_E` (normal: a localized node over a DVR, `Node.isIntegrallyClosed`; integral over
the node chart by 2; birational by 3), hence `IsAnnulusAt ϖ_E x (c/x) d 𝔭` with étale maps the
two localizations. (`IsAnnulusAt` is defined in `SemistableReduction/AnnulusAt.lean`, agreed with
W8: `x = ε·u'^d`, `y = ε'·v'^d`, `u', v' ∈ 𝔮`.)

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
