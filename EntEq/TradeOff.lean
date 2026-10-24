/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The algebraic core of the decoherence-diffusion trade-off test. Oppenheim, Sparaciari, Šoda and
  Weller-Davies (arXiv:2203.01982) prove that complete positivity of any classical-quantum
  dynamics forces the trade-off `2D₂ ⪰ D₁ D₀⁻¹ D₁†`, where `D₀` is the decoherence coefficient
  of the quantum system, `D₂` the diffusion of the classical (gravitational) degrees of freedom
  and `D₁` the drift, fixed for gravity by the Newtonian limit. In the scalar case with
  `D₀ > 0` this is the Schur-complement form of positivity of `[[2D₂, D₁], [D₁, D₀]]`, which
  `psd_two_iff` characterises; `diffusion_lower_bound` gives `2D₂ ≥ D₁²/D₀`: for fixed `D₁ ≠ 0`,
  less decoherence forces more diffusion.
-/
import Mathlib.Tactic

namespace EntEq.TradeOff

/-- A real symmetric 2×2 matrix is positive semidefinite iff `a ≥ 0`, `c ≥ 0`, `ac ≥ b²`. -/
theorem psd_two_iff (a b c : ℝ) :
    (∀ x y : ℝ, 0 ≤ a * x^2 + 2 * b * x * y + c * y^2) ↔ 0 ≤ a ∧ 0 ≤ c ∧ b^2 ≤ a * c := by
  constructor
  · intro h
    have ha := h 1 0
    have hc := h 0 1
    refine ⟨by simpa using ha, by simpa using hc, ?_⟩
    by_cases ha0 : a = 0
    · -- then `2b x + c` must be ≥ 0 for all `x`, forcing `b = 0`
      subst ha0
      by_contra hlt
      push Not at hlt
      have hb : b ≠ 0 := by intro hb; subst hb; simp at hlt
      have h' := h (-(c + 1) / (2 * b)) 1
      have e : 0 * (-(c + 1) / (2 * b))^2 + 2 * b * (-(c + 1) / (2 * b)) * 1 + c * 1^2 = -1 := by
        field_simp; ring
      linarith
    · have hapos : 0 < a := lt_of_le_of_ne (by simpa using ha) (Ne.symm ha0)
      have := h (-b) a
      nlinarith [this]
  · rintro ⟨ha, hc, hb⟩ x y
    by_cases ha0 : a = 0
    · subst ha0
      have : b = 0 := by nlinarith [sq_nonneg b]
      subst this; simp; positivity
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have key : a * (a * x^2 + 2 * b * x * y + c * y^2) = (a * x + b * y)^2 + (a * c - b^2) * y^2 := by
        ring
      have : 0 ≤ a * (a * x^2 + 2 * b * x * y + c * y^2) := by
        rw [key]; exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
      exact (mul_nonneg_iff_of_pos_left hapos).mp this

/-- **Trade-off** (scalar case). If `[[2D₂, D₁], [D₁, D₀]]` is positive semidefinite and the
decoherence coefficient `D₀ > 0`, the diffusion coefficient obeys `2D₂ ≥ D₁²/D₀`: halving the
decoherence doubles the lower bound on the diffusion. (Scalar case with real `D₁`; in general
`D₁²` reads `|D₁|²`.) -/
theorem diffusion_lower_bound (D₀ D₁ D₂ : ℝ) (hD₀ : 0 < D₀)
    (hpsd : ∀ x y : ℝ, 0 ≤ (2 * D₂) * x^2 + 2 * D₁ * x * y + D₀ * y^2) : D₁^2 / D₀ ≤ 2 * D₂ := by
  obtain ⟨-, -, h⟩ := (psd_two_iff (2 * D₂) D₁ D₀).mp hpsd
  rw [div_le_iff₀ hD₀]; linarith

end EntEq.TradeOff
