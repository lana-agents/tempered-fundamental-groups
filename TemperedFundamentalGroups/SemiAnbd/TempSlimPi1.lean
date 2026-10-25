/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Surface.Profinite
import TemperedFundamentalGroups.SemiAnbd.TempSlim

/-!
# Temp-slim = slim (bridge to `pi1`)

`TempSlim P` (the centralizer of every open subgroup is trivial) is `pi1`'s
`Pi1.Profinite.IsSlim P` (**`TemperedFundamentalGroups.tempSlim_iff_isSlim`**). In particular the
profinite surface groups `Π̂_{g,r}` of hyperbolic `(g, r)` with `r ≥ 1` are temp-slim
(**`TemperedFundamentalGroups.tempSlim_profiniteSurfaceGroup`**, from `Pi1.SurfaceGroup.isSlim`);
this is [SemiAnbd] Def 2.4(ii) ("verticially slim") at a vertex with `r_v ≥ 1`, for `Σ` = all
primes.
-/

namespace TemperedFundamentalGroups

/-- **`TempSlim` is `pi1`'s `IsSlim`.** -/
theorem tempSlim_iff_isSlim (P : Type*) [Group P] [TopologicalSpace P] :
    TempSlim P ↔ Pi1.Profinite.IsSlim P := by
  refine ⟨fun h U z hz ↦ h.eq_one (H := U.toSubgroup) U.isOpen fun y hy ↦ (hz y hy).symm,
    fun h H hH ↦ ?_⟩
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact h ⟨H, hH⟩ z fun u hu ↦ (Subgroup.mem_centralizer_iff.1 hz u hu).symm

/-- **The profinite surface groups `Π̂_{g,r}` (hyperbolic, `r ≥ 1`) are temp-slim.** -/
theorem tempSlim_profiniteSurfaceGroup {g r : ℕ} (hr : 0 < r)
    (h : Pi1.SurfaceGroup.IsHyperbolic g r) :
    TempSlim (Pi1.ProfiniteSurfaceGroup g r) :=
  (tempSlim_iff_isSlim _).2 (Pi1.SurfaceGroup.isSlim hr h)

end TemperedFundamentalGroups
