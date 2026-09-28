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
| W5 | Model/valuation dictionary: a normal proper `O_C`-model `𝒞` of `T̄` ↔ the finite set of type-2 valuations given by the generic points of `𝒞_s` ("vertex set"); every finite set of type-2 valuations containing a nonempty set is the vertex set of a unique normal model | Bosch–Lütkebohmert; algebraic: normalize a model in which the valuations are divisorial (blow-ups of `ℙ^m_{O_C}`-codes) |
| W6 | Genus formula: for a finite vertex set `V`, `g(T̄) = Σ_{w ∈ V} g(C_w) + b₁(Γ_V) + (contributions of the complement)`, and `Σ_{w type 2} g(C_w) ≤ g(T̄)`; hence only finitely many `w` have `g(C_w) > 0` | Riemann–Hurwitz for the residue curves + W4 (for `F/C(x)` of degree `d`, `Σ_{w'|w_{a,r}}` of residue degrees `= d`) |
| W7 | (**Semistable vertex set**) there is a finite `V` containing all `w` with `g(C_w) > 0` such that every "connected component of the complement" is an open disc or annulus; in valuation language: every type-2 `w ∉ V` has residue curve `ℙ¹` and at most two "directions" towards `V` | W2 + W6 + a local analysis of residue curves of `F` over `w_{a,r}` via W4 |
| W8 | The model with vertex set `V` (W5) is semistable | local computation at nodes: the complement annuli give local rings `O_C[u,v]/(uv − c)` |
| W9 | Descent: the vertex set, the model and its semistability are defined over a finite extension `K'/K` | the finitely many valuations are determined by finitely many elements of `F`; approximation |
| W10 | (SSR) for every finite étale `T → Y`, plus compatibility with a model of `Ȳ` (vertex sets pull back: the preimage of `V_Y` in `T̄` is contained in a vertex set of `T̄`) | W7 applied to `V ⊇ preimage` |

Realistic size: W1–W3 small/medium (weeks of agent time), W4 large (the heart; Temkin's
algebraic proof ~20 pages), W5 large (needs blow-ups or the `ModelCode`+normalization
dictionary), W6–W8 large, W9–W10 medium. Status: **W1–W3 proved.**
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
| G2 | every finite `M/\hat F` is inertially generated: choose `z ∈ O_M` with `κ_M/k(z̄)` separable (a separating transcendence basis of `κ_M/k`, `k` perfect); `M` is finite over the closure `\widehat{C(z)}` of `C(z)` in `M` (take a dense function field `F_M ⊂ M` via Krasner + polynomial approximation and `z ∈ F_M`; the restriction of the valuation to `C(z)` is the Gauss valuation — W1/W2); `M` is immediate over the unramified closure `M'` of `\widehat{C(z)}` (C2, `Γ_M = Γ_C`), so `M = M'` by G1 | 500 |
| G3 | **local stability**: every finite `E/\hat F` is defectless — Galois closure `N`, `N^T/\hat F` unramified (D3), `N/N^T` a D4-tower of Galois degree-`p` steps whose bases are finite over `\hat F`, hence inertially generated (G2), hence defectless (F5); multiplicativity (A4) | 200 |
| G4 | **W4** = B4 + G3 | 50 |

**Estimate.** A ≈ 1.2k (0.6k done), B ≈ 1.7k, C ≈ 1.4k, D ≈ 1.1k, E ≈ 1.3k (E1 overlaps with
the residue-curve infrastructure W3/W5/W6), F ≈ 3.2k (F4, the mixed-characteristic Kummer normal
form, is the single largest and most delicate item), G ≈ 1.0k: **≈ 11k lines** in total, i.e.
of the order of the whole Abhyankar/tame development several times over. The critical path for
the IUT application is A → C → D → (E, F1, F2, F4) → G → B; F3 and the inseparable parts of B/F5 are
only needed for `char C = p`.

**Status.** G1 proved in mixed characteristic (`SemistableReduction/NoImmediate`, `SemistableReduction/NormedTower`). A1–A3 proved (`SemistableReduction/FundamentalInequality`: `valuation_sum_eq_sup`, F (mixed characteristic, the IUT case) proved: F1 (`SemistableReduction/DiscreteCoefficients`), F2 (`SemistableReduction/InertiallyGenerated`, with the definition `IsInertiallyGenerated`), F4 (`SemistableReduction/PthPower`, `SemistableReduction/KummerNormalForm`), F5 (`SemistableReduction/KummerDefectless`); F3 (char `p`) skipped. Note for G2: `IsInertiallyGenerated C z` asks for `‖z‖ ≤ 1` with `z̄` transcendental over `k`, `[M : M₁] < ∞`, `κ_M/κ_{M₁}` finite separable and `[M : M₁] ≤ [κ_M : κ_{M₁}]` (`M₁ = genClosure C z`; `κ_{M₁} = k(z̄)` is `residueSubfield_genClosure`), stated with `DiscreteCoefficients.residueSubfield` for residue fields of subfields.
`linearIndependent_of_residue`, `linearIndependent_mul`, `ramificationIdx_mul_inertiaDeg_le`,
`exists_pow_valuation_eq`, `ramificationIdx_eq_one_of_divisible`); A4 proved (`SemistableReduction/DefectTower`); C1 proved (`SemistableReduction/HenselComplete`); E1 proved (`SemistableReduction/CurvePlace`); E2 proved (`SemistableReduction/FrobeniusBasis`). B1 proved (`SemistableReduction/DenseCompletion`); B2–B4 proved (`SemistableReduction/LocalGlobal`), for any non-archimedean normed field `F` and finite separable `F'/F`; A5 not needed. For the Gauss valuation take `F = WithAbs (gaussRat v a r).toAbsoluteValue` with `v = NormedField.valuation` of `C` (real-valued). Remaining in B for char `p`: the reduction of inseparable `F'/F` to the separable case. C2 proved (`SemistableReduction/UnramifiedRoot`, `SemistableReduction/Unramified`); C3 proved (`SemistableReduction/UniqueExtension`); C4 proved (`SemistableReduction/UnramifiedBaseChange`); D1–D3 proved (`SemistableReduction/Inertia`); D4 proved (`SemistableReduction/PGroupChain`). Layers C and D are complete; the Henselian and Galois-invariance hypotheses of C2/C4/D1–D3 are discharged over a complete base by C3 (`henselianLocalRing_valuationSubring`, `henselianLocalRing_comap`, `valuation_algEquiv_apply'`).
