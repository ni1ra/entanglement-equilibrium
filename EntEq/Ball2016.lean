/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The small-ball computation of Jacobson 2016. For a geodesic ball of radius `ℓ` in `d = m+2`
  spacetime dimensions, the vacuum modular Hamiltonian of a conformal field weights the energy
  density by `(ℓ² − r²)/(2ℓ)` (Casini–Huerta–Myers), so
      δS_ent = (2π/ħ) Ω_{d−2} δ⟨T₀₀⟩ ∫₀^ℓ r^{d−2} (ℓ² − r²)/(2ℓ) dr.
  The geometric input is the area deficit of the ball at fixed volume,
      δA|_V = −Ω_{d−2} ℓ^d G₀₀ / (d² − 1),
  taken here as a hypothesis (it needs Riemann normal coordinates, which Mathlib lacks).
  `ball_weight` proves the integral has exactly the same `ℓ^d/(d²−1)`, and `ball_equilibrium`
  that `δS_gen = η δA + δS_ent = 0` with `η = 1/(4Għ)` gives `G₀₀ = 8πG T₀₀`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

open intervalIntegral

namespace EntEq.Ball

/-- `∫₀^ℓ r^{d−2} (ℓ² − r²)/(2ℓ) dr = ℓ^d/(d² − 1)` with `d = m + 2`. -/
theorem ball_weight (m : ℕ) (ℓ : ℝ) (hℓ : ℓ ≠ 0) :
    ∫ r in (0:ℝ)..ℓ, r^m * (ℓ^2 - r^2) / (2 * ℓ)
      = ℓ^(m+2) / (((m:ℝ) + 2)^2 - 1) := by
  have h1 : ∀ r : ℝ, r^m * (ℓ^2 - r^2) / (2 * ℓ) = (ℓ / 2) * r^m - (1 / (2 * ℓ)) * r^(m+2) := by
    intro r; field_simp; ring
  simp_rw [h1]
  rw [integral_sub, integral_const_mul, integral_const_mul, integral_pow, integral_pow]
  · have hm1 : (m:ℝ) + 1 ≠ 0 := by positivity
    have hm3 : (m:ℝ) + 3 ≠ 0 := by positivity
    have hd : ((m:ℝ) + 2)^2 - 1 = (m + 1) * (m + 3) := by ring
    rw [hd]
    push_cast
    field_simp
    ring
  · exact (continuous_const.mul (continuous_pow m)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_pow (m+2))).intervalIntegrable _ _


/-- **Area deficit at fixed volume, from the volume deficit** (Jacobson 2016, eqs. 3–7).
Premises: the Riemann-normal-coordinate volume deficit of a geodesic ball,
`δV(ℓ) = −Ω ℓ^{d+1} R_s / (6(d−1)(d+1))` (eq. 3), the area deficit at fixed radius is its
`ℓ`-derivative (eq. 4), and the spatial Ricci scalar is `R_s = 2 G₀₀` (eq. 6, a moment of time
symmetry). Restoring the volume with a radius shift costs `(d−2)/ℓ · δV` of area (eq. 5), and
the result is eq. 7: `δA|_V = −Ω ℓ^d G₀₀/(d² − 1)`, here with `d = m + 2`. -/
theorem area_deficit_fixed_volume (m : ℕ) (Ω Rs G00 ℓ : ℝ) (hℓ : ℓ ≠ 0) (hR : Rs = 2 * G00) :
    let d : ℝ := m + 2
    let δV : ℝ → ℝ := fun r => -Ω * r^(m+3) * Rs / (6 * (d - 1) * (d + 1))
    ∃ δAℓ, HasDerivAt δV δAℓ ℓ ∧
      δAℓ - (d - 2) / ℓ * δV ℓ = -Ω * ℓ^(m+2) * G00 / (d^2 - 1) := by
  intro d δV
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hd1 : d - 1 ≠ 0 := ne_of_gt (by simp only [d]; linarith)
  have hd2 : d + 1 ≠ 0 := ne_of_gt (by simp only [d]; linarith)
  refine ⟨-Ω * ((m + 3 : ℕ) * ℓ^(m+2)) * Rs / (6 * (d - 1) * (d + 1)), ?_, ?_⟩
  · have h := (((hasDerivAt_pow (m+3) ℓ).const_mul (-Ω)).mul_const Rs).div_const
      (6 * (d - 1) * (d + 1))
    simpa [δV, mul_assoc] using h
  · simp only [δV, d] at *
    rw [hR]
    have hsq : ((m:ℝ) + 2)^2 - 1 ≠ 0 := by
      have : ((m:ℝ) + 2)^2 - 1 = (m + 1) * (m + 3) := by ring
      rw [this]; positivity
    field_simp
    push_cast
    ring

/-- **Entanglement equilibrium of one small ball.** With `δA = −Ω ℓ^d G₀₀/(d²−1)`,
`δS_ent = (2π/ħ) Ω T₀₀ ∫₀^ℓ r^{d−2}(ℓ²−r²)/(2ℓ) dr` and `η = 1/(4Għ)`, stationarity
`η δA + δS_ent = 0` gives `G₀₀ = 8πG T₀₀`. The ball size `ℓ`, the solid angle `Ω` and the
dimension all cancel. This is the conformal case (`δX = 0`) about a flat reference state
(`λ = 0`); `ball_to_einstein` feeds it `G₀₀ − λ` to cover the general reference curvature. -/
theorem ball_equilibrium (m : ℕ) (ℓ Ω ħ G G00 T00 δA δS : ℝ) (hℓ : 0 < ℓ) (hΩ : Ω ≠ 0)
    (hħ : ħ ≠ 0) (hG : G ≠ 0)
    (hA : δA = -Ω * ℓ^(m+2) * G00 / (((m:ℝ) + 2)^2 - 1))
    (hS : δS = 2 * Real.pi / ħ * Ω * T00 * ∫ r in (0:ℝ)..ℓ, r^m * (ℓ^2 - r^2) / (2 * ℓ))
    (hstat : 1 / (4 * G * ħ) * δA + δS = 0) :
    G00 = 8 * Real.pi * G * T00 := by
  rw [ball_weight m ℓ hℓ.ne'] at hS
  have hd : ((m:ℝ) + 2)^2 - 1 ≠ 0 := by
    have : ((m:ℝ) + 2)^2 - 1 = (m + 1) * (m + 3) := by ring
    rw [this]; positivity
  have hl : ℓ^(m+2) ≠ 0 := pow_ne_zero _ hℓ.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hA, hS] at hstat
  field_simp at hstat
  have : Ω * ℓ^(m+2) * (8 * Real.pi * G * T00 - G00) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hΩ
    · exact absurd h' hl
  · linarith

end EntEq.Ball
