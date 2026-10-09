/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The completion of an algebraically closed nonarchimedean field

Blueprint §9.11, C0. Let `C` be a nontrivially normed, nonarchimedean, algebraically closed field
of characteristic `0` (e.g. `K̄` for a discretely valued `K`). Its completion `Ĉ`
(`UniformSpace.Completion C`) is a complete, nontrivially normed, nonarchimedean field of
characteristic `0` (`instIsUltrametricDist`, `instCharZero`, `instNontriviallyNormedField`), and it
is algebraically closed (`isAlgClosed`): `C` is dense in `Ĉ`, so this is Mathlib's
`IsAlgClosed.of_denseRange` (continuity of roots + Krasner).

`isAlgClosed` is a theorem, not an instance, so that it does not fire on every completion; use
`haveI := UniformSpace.Completion.isAlgClosed C`.
-/

namespace UniformSpace.Completion

section NormedField

variable (C : Type*) [NormedField C]

lemma norm_natCast_coe (n : ℕ) : ‖(n : Completion C)‖ = ‖(n : C)‖ := by
  have h : (n : Completion C) = ((n : C) : Completion C) :=
    (map_natCast (Completion.coeRingHom (α := C)) n).symm
  rw [h, norm_coe]

/-- The completion of a nonarchimedean normed field is nonarchimedean. -/
instance instIsUltrametricDist [IsUltrametricDist C] : IsUltrametricDist (Completion C) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
    rw [norm_natCast_coe]
    exact IsUltrametricDist.norm_natCast_le_one C n

/-- The completion of a normed field of characteristic `0` has characteristic `0`. -/
instance instCharZero [CharZero C] : CharZero (Completion C) :=
  charZero_of_injective_algebraMap (R := C) (algebraMap C (Completion C)).injective

end NormedField

section Nontrivially

variable (C : Type*) [NontriviallyNormedField C]

/-- The completion of a nontrivially normed field is nontrivially normed. -/
noncomputable instance instNontriviallyNormedField :
    NontriviallyNormedField (Completion C) where
  non_trivial := by
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm C
    exact ⟨x, by rw [norm_coe]; exact hx⟩

/-- **C0**: the completion of an algebraically closed nonarchimedean normed field of
characteristic `0` is algebraically closed. -/
theorem isAlgClosed [IsUltrametricDist C] [CharZero C] [IsAlgClosed C] :
    IsAlgClosed (Completion C) :=
  IsAlgClosed.of_denseRange (K := C) denseRange_coe

end Nontrivially

end UniformSpace.Completion
