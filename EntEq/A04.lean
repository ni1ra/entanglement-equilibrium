/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  A convention-factor pin: the `β₀` (equivalently `λ_s`) dependence cancels from the
  oscillation-radius ceiling.

  Dictionary (taken as hypotheses, not derived here): `f_G = 1/(1+β₀)`,
  Verwayen's `μ_V² = f_G · m̃` with `m̃ := m²/f_G` (Mistele's bound variable), and
  Verwayen's `r̂_M = r_M/(1+β₀)`. Verwayen's oscillation radius is
      r_C = (1/3) · (18 r̂_M / (μ_V² (1+3|Δ|)))^(1/3),   so   r_C³ = (18/27) r̂_M/(μ_V²(1+3|Δ|)).
  In Lean `m̃` is spelled `mt`. Formalized: the exact `β₀` (equivalently `λ_s`) cancellation, the resulting ceiling on
  `α := m̃ r_M²` from `r_C ≥ x r_M`, and its point-mass form `α ≤ (2/3)(ḡ/a₀)^{3/2}` at `Δ = 0`.

  The point-mass relations `ḡ = GM/r_max²` and `r_M² = GM/a₀` are stated as explicit
  hypotheses.

  Note on evidence: a numerical sweep that computes `ceiling_muV2 = fG * X` and then
  `ceiling_m2fG = ceiling_muV2 / fG` returns `X` for any `fG` by construction, so it cannot
  fail and proves nothing; the symbolic cancellation (`rC_cubed_cancel` below) is the actual
  proof of `λ_s`-independence.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace EntEq.A04

/-- **The `β₀` cancellation.** With `μ_V² = f_G m̃`, `f_G = 1/(1+β₀)` and
`r̂_M = r_M/(1+β₀)`, Verwayen's `r_C³ = (18/27) r̂_M/(μ_V²(1+3Δ))` equals
`(2/3) r_M/(m̃(1+3Δ))`, with no `β₀` left. Here `Δ` stands for `|Δ|`; the
statements only need `1 + 3Δ > 0`, so they also hold for that non-negative value. -/
theorem rC_cubed_cancel (β₀ mt rM Δ : ℝ) (hβ : 0 < 1 + β₀) (hm : 0 < mt) (hΔ : 0 < 1 + 3 * Δ) :
    let fG := 1 / (1 + β₀)
    let μV2 := fG * mt
    let rMhat := rM / (1 + β₀)
    (18 / 27) * rMhat / (μV2 * (1 + 3 * Δ)) = (2 / 3) * rM / (mt * (1 + 3 * Δ)) := by
  intro fG μV2 rMhat
  simp only [fG, μV2, rMhat]
  field_simp
  ring

/-- **Ceiling on `α = m̃ r_M²`.** If `r_C³ = (2/3) r_M/(m̃(1+3Δ))` (the cancelled form above)
and `r_C ≥ x r_M` with `x > 0`, then `m̃ r_M² ≤ (2/3)/(x³(1+3Δ))`. -/
theorem alpha_ceiling (mt rM rC Δ x : ℝ) (hm : 0 < mt) (hrM : 0 < rM) (hΔ : 0 < 1 + 3 * Δ)
    (hx : 0 < x) (hrC : rC ^ 3 = (2 / 3) * rM / (mt * (1 + 3 * Δ))) (hge : x * rM ≤ rC) :
    mt * rM ^ 2 ≤ (2 / 3) / (x ^ 3 * (1 + 3 * Δ)) := by
  have hcube : (x * rM) ^ 3 ≤ rC ^ 3 := by
    apply pow_le_pow_left₀ (by positivity) hge
  rw [hrC] at hcube
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity)] at hcube
  have h : (x ^ 3 * (1 + 3 * Δ) * (mt * rM ^ 2)) * rM ≤ (2 / 3) * rM := by
    nlinarith [hcube]
  nlinarith [h]

/-- **Point-mass form at `Δ = 0`.** Assume a point-mass field: `ḡ = GM/r_max²` at the
radius `r_max`, and the MOND radius `r_M² = GM/a₀`. If `r_C³ = (2/3) r_M/m̃` and
`r_C ≥ r_max`, then `m̃ r_M² ≤ (2/3)(ḡ/a₀)^{3/2}`. -/
theorem alpha_max_point_mass (mt rM rC rmax GM a₀ gbar : ℝ) (hm : 0 < mt) (hrM : 0 < rM)
    (hrmax : 0 < rmax) (hGM : 0 < GM) (ha : 0 < a₀)
    (hg : gbar = GM / rmax ^ 2) (hM : rM ^ 2 = GM / a₀)
    (hrC : rC ^ 3 = (2 / 3) * rM / mt) (hge : rmax ≤ rC) :
    mt * rM ^ 2 ≤ (2 / 3) * (gbar / a₀) ^ ((3 : ℝ) / 2) := by
  set x := rmax / rM with hxdef
  have hx : 0 < x := by positivity
  have hceil := alpha_ceiling mt rM rC 0 x hm hrM (by norm_num) hx
    (by simpa using hrC) (by rw [hxdef, div_mul_cancel₀ _ hrM.ne']; exact hge)
  -- `ḡ/a₀ = (r_M/r_max)²`, so `(ḡ/a₀)^{3/2} = (r_M/r_max)³ = 1/x³`.
  have hratio : gbar / a₀ = (rM / rmax) ^ 2 := by
    rw [hg, div_pow, hM]; field_simp
  have hpow : (gbar / a₀) ^ ((3 : ℝ) / 2) = (rM / rmax) ^ 3 := by
    rw [hratio, ← Real.rpow_natCast (rM / rmax) 2, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hpow]
  rw [mul_zero, add_zero, mul_one] at hceil
  convert hceil using 1
  simp only [hxdef]
  field_simp

end EntEq.A04
