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

### 3.1 Base data (`TemperedFundamentalGroups/Setup.lean`)

* a field `K` with a valuation subring `O ⊆ K` (the ring of integers);
* an algebraically closed field `Ω` with a valuation subring `V ⊆ Ω` and `K → Ω` with
  `V ∩ K = O` (a geometric point with a chosen extension of the valuation — it fixes the
  specialization of geometric points);
* the curve as an orbifold `[Y/A]`: an affine `K`-scheme `Y = Spec R` with a finite group `A`
  acting on `R` by `K`-algebra automorphisms (for IUT: `Y = E ∖ E[ℓ]`, `A = M` or `M ⋊ {±1}`;
  `A` trivial gives the scheme `Y`);
* a geometric point `ȳ : R →ₐ[K] Ω`.

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
  `R`-algebras (`Tempered/Etale.lean`). This is the étale fundamental group of `[Y/A]` by
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
| A1 | Pointwise-convergence group topology on `Aut F`, `F : C ⥤ Type`; stabilizers are an open basis; `T2`, totally separated | `FibreFunctor/Topology.lean` | [L] |
| A2 | Restriction along `G : C' ⥤ C` with `G ⋙ F ≅ F'` gives a continuous hom `Aut F → Aut F'` | same | [L] |
| A3 | If every `F c` is finite, `Aut F` is compact (profinite) | same | [L] |
| B1 | `ℙ^m_O := Proj O[x₀..x_m]`, proper over `Spec O`; model codes are proper; `ℙ⁰_O ≅ Spec O` | `Models/Projective.lean` | [L] |
| B2 | Special fibre as a subspace; functoriality | `Models/Specialization.lean` | [L] |
| B3 | Specialization of `Ω`-points via the valuative criterion; uniqueness; naturality | same | [L] |
| C1 | Covering codes over a space, `G`-equivariance, fibres, trivial coverings | `Topology/CoveringCode.lean` | [L] |
| D1 | Levels `(B, H)`, `G_B`, `H⁰`, action on geometric fibres | `Tempered/Level.lean` | [L] |
| D2 | The category `TempObj`, fibre functor `tempFibre`, `temperedPi1 := Aut` | `Tempered/Category.lean` | [L] |
| D3 | `etalePi1` on `A`-equivariant finite étale algebras; functor `etaleToTemp`; continuous `temperedToEtale` | `Tempered/Etale.lean`, `Tempered/Comparison.lean` | [L] |
| E1 | `etalePi1` is profinite; for `A = 1` it is `≃ₜ*` to Mathlib's `Aut (CommAlgCat.FiniteEtale.fiber R Ω)` | `Tempered/EtaleProfinite.lean`, `Tempered/EtaleMathlib.lean` | [L] |
| E2 | Step 3 of §4: restriction along a realization (essentially surjective, morphisms realized after refinement) is `≃ₜ*` | `FibreFunctor/Realization.lean` | [L] (abstract lemma; its hypotheses for André's category are steps 1–2, [C]) |
| E3 | Countable fibres of connected coverings of noetherian spaces (step 4) | — | [P] |
| F1 | Orbicurve presentation: `Y = E ∖ S` with `S = E(k)[ℓ] + M` (rational points; `= E[ℓ]` when `E[ℓ] ⊆ E(k)`, as at all places used by IUT), `A = M` or `M ⋊ {±1}` acting by translations and negation on the function field | `Orbicurve/` | [P] (in progress) |
| F2 | Canonical valuation on `k` (the henselian DVR if one exists, else trivial); Chevalley extension to `Ω`; pointed affine orbifolds | `Setup/Valuation.lean`, `Setup/Orbifold.lean` | [L]; canonicity (F. K. Schmidt) [C] |
| F3 | `TemperedPi1Theory` instance from the above and a continuous comparison `etalePi1 → Pi1.pi1` (the identity if the étale theory uses `AffineOrbifold.etalePi1Profinite`) | iut | [P] |
| G1 | Non-degeneracy witness: `π₁^temp(E_q ∖ E[ℓ]) ↠ ℤ` (discrete, not profinite) | — | [✗] for now: exhibiting elements of `Aut Φ` requires acting compatibly on *all* objects, i.e. the classification of tempered coverings (steps 1–2) or analytic path lifting |
| G2 | Steps 1–2 of §4 | — | [✗] (needs Berkovich spaces / semistable reduction) |

## 6. Interface findings (iut)

* `TemperedPi1Theory` receives only `[Field k]`. The tempered group depends on the valuation.
  For a field that is not separably closed there is at most one henselian rank-one valuation
  (F. K. Schmidt), so a canonical choice exists (F2), but the interface would be more honest if
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
