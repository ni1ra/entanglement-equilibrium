/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The closed-form exponent with its `Q` terms restored, as a theorem about the actual time-dependent equation.
-/
import EntEq.AeST
import EntEq.Comparison

open Set Real

namespace EntEq.AeST

/-- **The closed-form exponent is an upper bound once the `Q` terms are kept.** On Einstein–de Sitter in
`s = ln t` (`t = e^s`, `H = 2/(3t)`), take the reduced equation `χ_ss − χ_s/3 = D(s) χ` with
the full coefficient `D = t² Q M/K_B`, `M = K′ − (2−K_B)(H+Q)`, `Q K′ = 3H²f_c` (dust), a
**constant** `Q₀ ≥ 0` (the regime where `eliminate_E` derives this equation) and
`0 < K_B < 2`. On any interval `[s₀, s₁]` where the mode is positive and which it enters no
steeper than `aⁿ` (`p = 2n/3`), `χ(s) ≤ χ(s₀) e^{p(s−s₀)}`, i.e. `χ ≤ χ₀ (a/a₀)ⁿ` with the
closed-form `n`. (With `Q₀ > 0`, `D → −∞`, so the mode eventually oscillates; the bound covers the
growth phase before that.) -/
theorem aest_growth_le (K f Q₀ : ℝ) (hK0 : 0 < K) (hK2 : K < 2) (hf : 0 ≤ f) (hQ : 0 ≤ Q₀)
    (K' χ χ' χ'' : ℝ → ℝ) (s₀ s₁ : ℝ)
    (hρ : ∀ s ∈ Icc s₀ s₁, Q₀ * K' s = 3 * (2 / (3 * exp s))^2 * f)
    (hχ : ∀ s ∈ Icc s₀ s₁, HasDerivAt χ (χ' s) s) (hχ' : ∀ s ∈ Icc s₀ s₁, HasDerivAt χ' (χ'' s) s)
    (hode : ∀ s ∈ Icc s₀ s₁, χ'' s - χ' s / 3 =
      (exp s)^2 * (Q₀ * (K' s - (2 - K) * (2 / (3 * exp s) + Q₀)) / K) * χ s)
    (hpos : ∀ s ∈ Icc s₀ s₁, 0 < χ s) (hinit : χ' s₀ ≤ (2/3 * nExp K f) * χ s₀) :
    ∀ s ∈ Icc s₀ s₁, χ s ≤ χ s₀ * exp ((2/3 * nExp K f) * (s - s₀)) := by
  set p := 2/3 * nExp K f
  have hc : p^2 - p/3 = 4 * f / (3 * K) := by
    have hs : 0 ≤ 1/9 + 16 * f / (3 * K) := by positivity
    have hsq := Real.sq_sqrt hs
    have hp : p = 1/6 + √(1/9 + 16 * f / (3 * K)) / 2 := by simp only [p, nExp]; ring
    rw [hp]
    have : (1/6 + √(1/9 + 16 * f / (3 * K)) / 2)^2 - (1/6 + √(1/9 + 16 * f / (3 * K)) / 2)/3
        = √(1/9 + 16 * f / (3 * K))^2 / 4 - 1/36 := by ring
    rw [this, hsq]; field_simp; ring
  apply Comparison.growth_upper_bound χ χ' χ'' _ p (4 * f / (3 * K)) s₀ s₁ hc hχ hχ' hode _ hpos
    hinit
  intro s hs
  have hH : 0 < 2 / (3 * exp s) := by positivity
  have hle := coefficient_le K (2 / (3 * exp s)) Q₀ f (K' s) hK0 hK2 hH hQ (hρ s hs)
  have he : 0 < (exp s)^2 := by positivity
  calc (exp s)^2 * (Q₀ * (K' s - (2 - K) * (2 / (3 * exp s) + Q₀)) / K)
      ≤ (exp s)^2 * (3 * (2 / (3 * exp s))^2 * f / K) := mul_le_mul_of_nonneg_left hle he.le
    _ = 4 * f / (3 * K) := by field_simp; ring

end EntEq.AeST
