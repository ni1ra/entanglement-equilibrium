/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The local inverse of the normal-coordinate map is `C^∞` at the image of `0` (inverse function
  theorem plus Mathlib's `contDiffAt_symm`). This is smoothness at one point; smoothness on a
  neighbourhood is not proved here.
-/
import EntEq.NormalCoordsGeneral

open scoped ContDiff

namespace EntEq.NormalCoords

variable {n : ℕ}

local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

/-- `xNC s g` restricts to an open partial homeomorphism around `0` whose inverse is `C^∞` at
the image of `0` (pointwise smoothness only). -/
theorem xNC_local_diffeo (g : E → Mat) (hsym : ∀ y, (g y).IsSymm) (s : Fin (n+1) → ℝ) :
    ∃ φ : OpenPartialHomeomorph E E, ⇑φ = xNC s g ∧ (0 : E) ∈ φ.source ∧
      ContDiffAt ℝ ∞ φ.symm (φ 0) := by
  have hstrict := hasStrictFDerivAt_xNC g hsym s
  obtain ⟨hx, -, -⟩ := xNC_jets g hsym s
  have hcd : ContDiff ℝ ∞ (xNC s g) := contDiff_pi.2 hx
  set φ := hstrict.toOpenPartialHomeomorph (xNC s g) with hφ
  have h0 : (0 : E) ∈ φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  refine ⟨φ, rfl, h0, ?_⟩
  have hsymm : φ.symm (φ 0) = 0 := φ.left_inv h0
  apply φ.contDiffAt_symm (φ.map_source h0) (f₀' := ContinuousLinearEquiv.refl ℝ E)
  · rw [hsymm]; exact hstrict.hasFDerivAt
  · rw [hsymm]; exact hcd.contDiffAt

end EntEq.NormalCoords
