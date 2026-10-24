/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The geometric half of the Unruh temperature. Wick-rotating the Rindler metric
  `−κ²ρ² dt² + dρ²` gives `κ²ρ² dτ² + dρ²`, which is the flat plane in polar coordinates
  `(x, y) = (ρ cos κτ, ρ sin κτ)`: the map pulls `dx² + dy²` back to exactly that metric
  (`polar_pullback`), periodic in `τ` with period `2π/κ` (`polar_period`). If imaginary time
  is identified with period `β`, small circles `ρ = const` have circumference `κρβ`, so the
  geometry is smooth at the horizon (circumference/radius `= 2π`) exactly when `β = 2π/κ`
  (`cone_regular_iff`). The physics premise (KMS: a state periodic in imaginary time with
  period `ħ/(k_B T)` is thermal at `T`) then gives `k_B T = ħκ/2π` (`unruh_temperature`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

open Real

namespace EntEq.Unruh

/-- The polar map `(ρ, τ) ↦ (ρ cos κτ, ρ sin κτ)`. -/
noncomputable def X (κ ρ τ : ℝ) : ℝ := ρ * cos (κ * τ)
noncomputable def Y (κ ρ τ : ℝ) : ℝ := ρ * sin (κ * τ)

/-- **Pull-back of the flat metric.** With `∂_ρ` and `∂_τ` of the polar map,
`g_ρρ = 1`, `g_ρτ = 0`, `g_ττ = κ²ρ²`: the Euclidean Rindler metric. -/
theorem polar_pullback (κ ρ τ : ℝ) :
    let Xρ := deriv (fun r => X κ r τ) ρ
    let Yρ := deriv (fun r => Y κ r τ) ρ
    let Xτ := deriv (fun s => X κ ρ s) τ
    let Yτ := deriv (fun s => Y κ ρ s) τ
    Xρ^2 + Yρ^2 = 1 ∧ Xρ * Xτ + Yρ * Yτ = 0 ∧ Xτ^2 + Yτ^2 = κ^2 * ρ^2 := by
  intro Xρ Yρ Xτ Yτ
  have h1 : Xρ = cos (κ * τ) := by
    simp only [Xρ, X]; rw [deriv_mul_const_field']; simp
  have h2 : Yρ = sin (κ * τ) := by
    simp only [Yρ, Y]; rw [deriv_mul_const_field']; simp
  have h3 : Xτ = -(ρ * κ * sin (κ * τ)) := by
    simp only [Xτ, X]
    have h := ((hasDerivAt_id τ).const_mul κ).cos.const_mul ρ
    simp only [id, mul_one] at h
    rw [h.deriv]; ring
  have h4 : Yτ = ρ * κ * cos (κ * τ) := by
    simp only [Yτ, Y]
    have h := ((hasDerivAt_id τ).const_mul κ).sin.const_mul ρ
    simp only [id, mul_one] at h
    rw [h.deriv]; ring
  rw [h1, h2, h3, h4]
  have hs := sin_sq_add_cos_sq (κ * τ)
  refine ⟨by nlinarith, by ring, by nlinarith⟩

/-- **Period.** For `κ ≠ 0` the polar map is periodic in `τ` with period `2π/κ`. -/
theorem polar_period (κ ρ τ : ℝ) (hκ : κ ≠ 0) :
    X κ ρ (τ + 2 * π / κ) = X κ ρ τ ∧ Y κ ρ (τ + 2 * π / κ) = Y κ ρ τ := by
  have : κ * (τ + 2 * π / κ) = κ * τ + 2 * π := by field_simp
  refine ⟨?_, ?_⟩ <;> simp [X, Y, this]

/-- The polar map has no period shorter than `2π/κ` (for `κ > 0`, `ρ ≠ 0`): the point at
`τ = 0` is not revisited before then. (Regularity itself is `cone_regular_iff`.) -/
theorem polar_period_minimal (κ ρ P : ℝ) (hκ : 0 < κ) (hρ : ρ ≠ 0) (hP : 0 < P)
    (hPlt : P < 2 * π / κ) : (X κ ρ P, Y κ ρ P) ≠ (X κ ρ 0, Y κ ρ 0) := by
  intro h
  simp only [X, Y, Prod.mk.injEq, mul_zero, cos_zero, sin_zero, mul_one] at h
  obtain ⟨hx, -⟩ := h
  have hc : cos (κ * P) = 1 := by
    have := mul_left_cancel₀ hρ (hx.trans (mul_one ρ).symm)
    exact this
  have hpos : 0 < κ * P := mul_pos hκ hP
  have hlt : κ * P < 2 * π := by rwa [lt_div_iff₀ hκ, mul_comm] at hPlt
  have := (cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) hlt).mp hc
  linarith

/-- **No conical singularity.** With imaginary time identified with period `β`, the circle of
radius `ρ > 0` has circumference `κρβ` in the metric `κ²ρ²dτ² + dρ²`; the ratio to `ρ` is `2π`
(the smooth, flat-plane value) iff `β = 2π/κ`. -/
theorem cone_regular_iff (κ ρ β : ℝ) (hκ : κ ≠ 0) (hρ : 0 < ρ) :
    κ * ρ * β / ρ = 2 * π ↔ β = 2 * π / κ := by
  rw [show κ * ρ * β / ρ = κ * β by field_simp]
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp

/-- **Unruh temperature.** Premises: smoothness at the horizon (`β = 2π/κ`, `cone_regular_iff`)
and KMS (imaginary-time period `β = ħ/(k_B T)` means thermal at `T`). Then `k_B T = ħκ/2π`. -/
theorem unruh_temperature (ħ κ kB T β : ℝ) (hκ : κ ≠ 0) (hreg : β = 2 * π / κ)
    (hKMS : β = ħ / (kB * T)) (hT : kB * T ≠ 0) : kB * T = ħ * κ / (2 * π) := by
  have hpi := pi_ne_zero
  have hβ : β ≠ 0 := by rw [hreg]; exact div_ne_zero (mul_ne_zero two_ne_zero hpi) hκ
  have hħ : ħ ≠ 0 := by intro h; apply hβ; rw [hKMS, h, zero_div]
  have h1 : kB * T = ħ / β := by rw [hKMS]; field_simp
  rw [h1, hreg]; field_simp

end EntEq.Unruh
