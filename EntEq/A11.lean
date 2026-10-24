/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The numerical factor between Verlinde's `a₀` and the emergent-gravity acceleration scale.

  Verlinde's surface-density relation in `d` spacetime dimensions,
      Σ_D² = a₀ Σ_B / (8πG (d−1)),
  together with the `d`-dimensional Gauss law `Σ = (d−2) g / (8πG (d−3))` for both the
  apparent dark (`D`) and baryonic (`B`) pieces, gives
      g_D² = a_M g_B,   a_M = (d−3)/((d−2)(d−1)) · a₀,
  which is `a₀/6` at `d = 4` (where Gauss reads `Σ = g/(4πG)`). Both the general-`d` factor and the `d = 4` case are checked here. The Gauss law is a hypothesis.

  Numerics: `cH₀/6` for Planck 2018 (`H₀ = 67.36`) and SH0ES 2022 (`73.04`) km/s/Mpc, with
  `c = 299792458 m/s` and `1 Mpc = 3.0856775814913673·10²² m` (a rational truncation; the IAU
  parsec is irrational), and the spread `4π` between the O(1) factors `1` and `1/(4π)`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace EntEq.A11

/-- **General-`d` factor.** If `Σ_D² = a₀ Σ_B/(8πG(d−1))` and both surface densities obey the
`d`-dimensional Gauss law `Σ = (d−2) g/(8πG(d−3))`, with `d > 3` and `G > 0`, then
`g_D² = a₀ g_B (d−3)/((d−2)(d−1))`. -/
theorem gD_sq_general (d G a₀ gB gD SB SD : ℝ) (hd : 3 < d) (hG : 0 < G)
    (hSB : SB = (d - 2) * gB / (8 * Real.pi * G * (d - 3)))
    (hSD : SD = (d - 2) * gD / (8 * Real.pi * G * (d - 3)))
    (hrel : SD ^ 2 = a₀ * SB / (8 * Real.pi * G * (d - 1))) :
    gD ^ 2 = a₀ * gB * (d - 3) / ((d - 2) * (d - 1)) := by
  have h3 : 0 < d - 3 := by linarith
  have h2 : 0 < d - 2 := by linarith
  have h1 : 0 < d - 1 := by linarith
  have hpi := Real.pi_pos
  subst hSB hSD
  rw [div_pow, eq_div_iff (by positivity)] at hrel
  rw [eq_div_iff (by positivity)]
  field_simp at hrel
  -- `hrel` is the target times the positive factor `(d−2)·8πG`; cancel it.
  have hk : 0 < (d - 2) * (8 * Real.pi * G) := by positivity
  apply mul_right_cancel₀ hk.ne'
  nlinarith [hrel]

/-- **Four dimensions.** With `Σ = g/(4πG)` for both pieces and `Σ_D² = a₀ Σ_B/(8πG·3)`,
`g_D² = a₀ g_B/6`. -/
theorem gD_sq_d4 (G a₀ gB gD : ℝ) (hG : 0 < G)
    (hrel : (gD / (4 * Real.pi * G)) ^ 2 = a₀ * (gB / (4 * Real.pi * G)) / (8 * Real.pi * G * 3)) :
    gD ^ 2 = a₀ * gB / 6 := by
  have hpi := Real.pi_pos
  rw [div_pow, eq_div_iff (by positivity)] at hrel
  field_simp at hrel
  have hk : 0 < Real.pi * G := by positivity
  apply mul_right_cancel₀ hk.ne'
  nlinarith [hrel]

/-- The general factor `(d−3)/((d−2)(d−1))` equals `1/6` at `d = 4` and `0` at `d = 3`. -/
theorem factor_values :
    ((4 : ℝ) - 3) / ((4 - 2) * (4 - 1)) = 1 / 6 ∧ ((3 : ℝ) - 3) / ((3 - 2) * (3 - 1)) = 0 := by
  norm_num

/-- Speed of light, m/s. -/
def c : ℚ := 299792458
/-- One megaparsec in metres, rational truncation of `3.0856775814913673·10²²`. -/
def Mpc : ℚ := 30856775814913673 * 10 ^ 6
/-- `c H₀ / 6` in m/s², with `H₀` given in km/s/Mpc. -/
def aM (H0 : ℚ) : ℚ := c * (H0 * 1000 / Mpc) / 6

/-- Planck 2018 (`H₀ = 67.36`): `cH₀/6 ∈ (1.0907, 1.0908)·10⁻¹⁰ m/s²`. -/
theorem aM_planck : 10907 / 10 ^ 14 < aM (6736 / 100) ∧ aM (6736 / 100) < 10908 / 10 ^ 14 := by
  unfold aM c Mpc; norm_num

/-- SH0ES 2022 (`H₀ = 73.04`): `cH₀/6 ∈ (1.1827, 1.1828)·10⁻¹⁰ m/s²`. -/
theorem aM_shoes : 11827 / 10 ^ 14 < aM (7304 / 100) ∧ aM (7304 / 100) < 11828 / 10 ^ 14 := by
  unfold aM c Mpc; norm_num

/-- Ratio to the measured `g† = 1.19·10⁻¹⁰`: about `1.091` (Planck) and `1.006` (SH0ES). -/
theorem ratios :
    (1090 / 1000 : ℚ) < (119 / 10 ^ 12) / aM (6736 / 100)
      ∧ (119 / 10 ^ 12) / aM (6736 / 100) < 1092 / 1000
      ∧ (1006 / 1000 : ℚ) < (119 / 10 ^ 12) / aM (7304 / 100)
      ∧ (119 / 10 ^ 12) / aM (7304 / 100) < 1007 / 1000 := by
  unfold aM c Mpc; norm_num

/-- Bounds on `4π ∈ (12.56, 12.57)`, the ratio of the O(1) factors `1` and `1/(4π)` (a spread of
about 12.6). That these are the relevant choices is a physical reading, not formalised here. -/
theorem factor_spread : 12.56 < 1 / (1 / (4 * Real.pi)) ∧ 1 / (1 / (4 * Real.pi)) < 12.57 := by
  rw [one_div_one_div]
  constructor <;> nlinarith [Real.pi_gt_d4, Real.pi_lt_d4]

end EntEq.A11
