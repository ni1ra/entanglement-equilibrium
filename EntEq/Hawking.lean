/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Consistency of the entanglement density `η = 1/(4Għ)` with black-hole thermodynamics.
  For Schwarzschild, surface gravity `κ = c⁴/(4GM)` and the Unruh/Hawking temperature
  `T = ħκ/(2π c k_B)` together with `S = k_B c³ A/(4Għ)`, `A = 16π G²M²/c⁴`, satisfy the first
  law `d(Mc²) = T dS` exactly: the same `η` that gives Newton's constant in Jacobson's
  derivation gives Hawking's temperature.
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace EntEq

/-- Bekenstein–Hawking entropy of a Schwarzschild hole of mass `M`. -/
noncomputable def S_BH (G c ħ kB M : ℝ) : ℝ :=
  kB * c^3 * (16 * Real.pi * G^2 * M^2 / c^4) / (4 * G * ħ)

/-- Hawking temperature from the Unruh formula with `κ = c⁴/(4GM)`. -/
noncomputable def T_H (G c ħ kB M : ℝ) : ℝ := ħ * (c^4 / (4 * G * M)) / (2 * Real.pi * c * kB)

/-- **First law.** `T_H · dS_BH/dM = c²`, i.e. `d(Mc²) = T dS`. -/
theorem first_law_schwarzschild (G c ħ kB M : ℝ) (hG : G ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hk : kB ≠ 0) (hM : M ≠ 0) :
    ∃ dS, HasDerivAt (S_BH G c ħ kB) dS M ∧ T_H G c ħ kB M * dS = c^2 := by
  refine ⟨kB * c^3 * (16 * Real.pi * G^2 * (2 * M) / c^4) / (4 * G * ħ), ?_, ?_⟩
  · unfold S_BH
    have h := ((((hasDerivAt_pow 2 M).const_mul (16 * Real.pi * G^2)).div_const (c^4)).const_mul
      (kB * c^3)).div_const (4 * G * ħ)
    convert h using 1
    push_cast; ring
  · unfold T_H
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

end EntEq
