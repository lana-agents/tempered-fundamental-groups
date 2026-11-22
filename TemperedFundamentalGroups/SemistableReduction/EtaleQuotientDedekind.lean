/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Domain quotients of étale algebras over a Dedekind domain (generic)

MR13 step 7, D1 (S2). Over a Dedekind domain `R`, a domain `C` which is a quotient of an étale
`R`-algebra `E` with `R → C` injective is étale over `R`: it is formally unramified (quotient of
an unramified algebra), finitely presented (`E` is Noetherian) and flat (torsion-free over a
Dedekind domain). Used for the component `(B₁/𝔓_v)[1/ḡ]` of the special fibre of a Galois Tate
cover over the line `ℓ` minus its nodes (`E = (B₁/P_ℓ B₁)[1/ḡ]`, étale by purity).

* **`EtaleQuotientDedekind.etale_of_surjective`**.
-/

namespace SemistableReduction

namespace EtaleQuotientDedekind

variable {R E C : Type*} [CommRing R] [CommRing E] [CommRing C] [Algebra R E] [Algebra R C]

/-- **A domain quotient of an étale algebra over a Dedekind domain, faithful over the base, is
étale.** -/
theorem etale_of_surjective [IsDedekindDomain R] [Algebra.Etale R E] [IsDomain C]
    (f : E →ₐ[R] C) (hf : Function.Surjective f) (hinj : Function.Injective (algebraMap R C)) :
    Algebra.Etale R C := by
  haveI : Algebra.FormallyUnramified R C := .of_surjective f hf
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing R E
  haveI : Algebra.FinitePresentation R C :=
    .of_surjective hf (IsNoetherian.noetherian _)
  haveI : Module.IsTorsionFree R C := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  exact .of_formallyUnramified_of_flat

end EtaleQuotientDedekind

end SemistableReduction
