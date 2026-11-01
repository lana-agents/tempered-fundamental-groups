/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Finiteness
import Pi1.Profinite.ProSigma

/-!
# Topologically finitely generated profinite groups are Hopfian

Route B, item B5 of the MR13 plan (C1 vertex groups): a surjective continuous endomorphism of a
topologically finitely generated profinite group is an isomorphism. Used to show that
`Π^Σ_{0,3} → D_v` is injective once `HNN^Σ(Π^Σ_{0,3}) ≅ Π^Σ_{1,1} ↠ Δ^Σ ≅ Π^Σ_{1,1}` is known.

**Proof.** For `n ≥ 1` the open normal subgroups of index `n` form a finite set: each is the kernel
of a homomorphism with open kernel to `Perm (Fin n)` (the regular representation of the quotient),
and such homomorphisms are determined by their values on a finite topological generating set. A
surjective `f` induces an injective, hence bijective, self-map `V ↦ f⁻¹ V` of this finite set, so
every open normal subgroup contains `ker f`; in a profinite group they intersect in `1`.

* `TemperedFundamentalGroups.IsTopFG`: topological finite generation;
* `IsTopFG.hom_eq_of_eqOn`, `IsTopFG.finite_openNormal_index`;
* **`IsTopFG.injective_of_surjective`**, **`IsTopFG.hopfEquiv`** (the inverse is continuous);
* `IsTopFG.bijective_of_surjective_of_equiv`: a surjection `G ↠ H` onto a group isomorphic to `G`
  is bijective;
* `isTopFG_proSigmaCompletion`: pro-`Σ` completions of finitely generated groups are
  topologically finitely generated.
-/

open Pi1.Profinite

namespace TemperedFundamentalGroups

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Topologically finitely generated**: some finite set generates a dense subgroup. -/
def IsTopFG : Prop := ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤

variable {G}

namespace IsTopFG

/-- Homomorphisms with open kernels agreeing on a topological generating set agree. -/
theorem hom_eq_of_eqOn {S : Set G} (hS : (Subgroup.closure S).topologicalClosure = ⊤)
    {Q : Type*} [Group Q] {f g : G →* Q} (hf : IsOpen (f.ker : Set G))
    (hg : IsOpen (g.ker : Set G)) (h : ∀ s ∈ S, f s = g s) : f = g := by
  have hle : f.ker ⊓ g.ker ≤ f.eqLocus g := fun x hx ↦ by
    change f x = g x
    rw [MonoidHom.mem_ker.1 hx.1, MonoidHom.mem_ker.1 hx.2]
  have hopen : IsOpen (f.eqLocus g : Set G) := Subgroup.isOpen_mono hle (hf.inter hg)
  have hcl : Subgroup.closure S ≤ f.eqLocus g := (Subgroup.closure_le _).2 h
  have htop : (Subgroup.closure S).topologicalClosure ≤ f.eqLocus g :=
    Subgroup.topologicalClosure_minimal _ hcl (Subgroup.isClosed_of_isOpen _ hopen)
  rw [hS] at htop
  exact MonoidHom.ext fun x ↦ htop (Subgroup.mem_top x)

/-- **Finitely many open normal subgroups of a given index.** -/
theorem finite_openNormal_index [CompactSpace G] (hG : IsTopFG G) (n : ℕ) :
    {W : Subgroup G | IsOpen (W : Set G) ∧ W.Normal ∧ W.index = n}.Finite := by
  classical
  obtain ⟨S, hS⟩ := hG
  let C := {φ : G →* Equiv.Perm (Fin n) // IsOpen (φ.ker : Set G)}
  haveI : Finite C := by
    refine Finite.of_injective (fun φ : C ↦ fun s : S ↦ φ.1 s) fun φ ψ h ↦ ?_
    exact Subtype.ext (hom_eq_of_eqOn hS φ.2 ψ.2 fun s hs ↦ congrFun h ⟨s, hs⟩)
  refine (Set.finite_range fun φ : C ↦ φ.1.ker).subset ?_
  rintro W ⟨hWo, hWn, hWi⟩
  haveI := hWn
  haveI : Finite (G ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  let e : G ⧸ W ≃ Fin n := (Finite.equivFin (G ⧸ W)).trans (finCongr hWi)
  let φ : G →* Equiv.Perm (Fin n) := (Equiv.permCongrHom e).toMonoidHom.comp
    ((MulAction.toPermHom (G ⧸ W) (G ⧸ W)).comp (QuotientGroup.mk' W))
  have hker : φ.ker = W := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : MulAction.toPermHom (G ⧸ W) (G ⧸ W) (x : G ⧸ W) = 1 :=
        (Equiv.permCongrHom e).injective (hx.trans (map_one _).symm)
      have h2 := congrArg (fun σ : Equiv.Perm (G ⧸ W) ↦ σ 1) h1
      simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_eq_mul, mul_one,
        Equiv.Perm.coe_one, id_eq] at h2
      exact (QuotientGroup.eq_one_iff x).1 h2
    · intro hx
      have : (x : G ⧸ W) = 1 := (QuotientGroup.eq_one_iff x).2 hx
      simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, this, map_one]
  exact ⟨⟨φ, hker ▸ hWo⟩, hker⟩

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [T2Space G] in
/-- **Hopficity.** A surjective continuous endomorphism of a topologically finitely generated
profinite group is injective. -/
theorem injective_of_surjective (hG : IsTopFG G) {f : G →* G} (hf : Continuous f)
    (hs : Function.Surjective f) : Function.Injective f := by
  -- every open normal subgroup contains `ker f`
  have hker : ∀ W : Subgroup G, IsOpen (W : Set G) → W.Normal → f.ker ≤ W := by
    intro W hWo hWn
    set Sn := {W' : Subgroup G | IsOpen (W' : Set G) ∧ W'.Normal ∧ W'.index = W.index}
    have hfin : Finite Sn := (finite_openNormal_index hG W.index).to_subtype
    let τ : Sn → Sn := fun V ↦ ⟨V.1.comap f, V.2.1.preimage hf,
      by haveI := V.2.2.1; exact Subgroup.normal_comap f,
      (V.1.index_comap_of_surjective hs).trans V.2.2.2⟩
    have hτ : Function.Injective τ := fun V V' h ↦
      Subtype.ext (Subgroup.comap_injective hs (congrArg Subtype.val h))
    obtain ⟨V, hV⟩ := (Finite.injective_iff_surjective.1 hτ) ⟨W, hWo, hWn, rfl⟩
    have : W = V.1.comap f := (congrArg Subtype.val hV).symm
    rw [this]
    exact MonoidHom.ker_le_comap f _
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hne
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := G) (isOpen_compl_singleton (x := x)) (Ne.symm hne)
  exact hH (hker H.toSubgroup H.isOpen' H.isNormal' hx) rfl

/-- **Hopficity, as an isomorphism of topological groups.** -/
noncomputable def hopfEquiv (hG : IsTopFG G) (f : G →* G) (hf : Continuous f)
    (hs : Function.Surjective f) : G ≃ₜ* G :=
  let e := MulEquiv.ofBijective f ⟨hG.injective_of_surjective hf hs, hs⟩
  { e with
    continuous_toFun := hf
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) hf).symm.continuous }

@[simp] theorem hopfEquiv_apply (hG : IsTopFG G) (f : G →* G) (hf : Continuous f)
    (hs : Function.Surjective f) (x : G) : hG.hopfEquiv f hf hs x = f x := rfl

omit [T2Space G] in
/-- A continuous surjection onto a group isomorphic to `G` is bijective. -/
theorem bijective_of_surjective_of_equiv (hG : IsTopFG G) {H : Type*} [Group H]
    [TopologicalSpace H] {f : G →* H} (hf : Continuous f) (hs : Function.Surjective f)
    (e : H ≃ₜ* G) : Function.Bijective f := by
  refine ⟨fun x y h ↦ ?_, hs⟩
  have hinj := hG.injective_of_surjective (f := (e : H →* G).comp f) (e.continuous.comp hf)
    (e.surjective.comp hs)
  exact hinj (by simp [h])

end IsTopFG

/-- **Pro-`Σ` completions of finitely generated groups are topologically finitely generated.** -/
theorem isTopFG_proSigmaCompletion {P : ℕ → Prop} {Γ : Type*} [Group Γ] [hΓ : Group.FG Γ] :
    IsTopFG (ProSigmaCompletion P Γ) := by
  classical
  obtain ⟨S, hS⟩ := hΓ.out
  refine ⟨S.image (ProSigmaCompletion.eta P), ?_⟩
  have hrange : (ProSigmaCompletion.eta P (Γ := Γ)).range ≤
      Subgroup.closure ((S.image (ProSigmaCompletion.eta P) : Finset _) : Set _) := by
    rw [MonoidHom.range_eq_map, ← hS, MonoidHom.map_closure, Finset.coe_image]
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hd := (ProSigmaCompletion.denseRange_eta (P := P) (Γ := Γ))
  have : x ∈ closure (Set.range (ProSigmaCompletion.eta P (Γ := Γ))) := hd.closure_eq ▸ trivial
  exact closure_mono (fun y hy ↦ hrange hy) this

end TemperedFundamentalGroups
