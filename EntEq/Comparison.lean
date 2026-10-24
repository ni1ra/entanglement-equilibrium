/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  When is the closed-form exponent a bound? In `s = ln t` on Einstein–de Sitter, the reduced equation
  `χ̈ + (2/3t) χ̇ = C(t) χ` becomes `χ_ss − χ_s/3 = D(s) χ` with `D = t² C`; the closed form is
  the case `D ≡ c = 4f_c/(3K_B)`, solved by `e^{ps} = tᵖ = aⁿ` with `p² − p/3 = c`, `n = 3p/2`.
  Writing `χ = e^{ps} u` turns it into `u_ss + (2p − 1/3) u_s = (D − c) u`, and:
  * `growth_lower_bound`: if `D ≥ c` (any extra destabilising effect) and the mode starts at
    least as steep as `aⁿ`, then `χ(s) ≥ χ(s₀) e^{p(s−s₀)}` for all later `s`;
  * `growth_upper_bound`: if `D ≤ c` (for example the dropped `Q` terms, `coefficient_le`)
    and the mode starts no steeper, then `χ(s) ≤ χ(s₀) e^{p(s−s₀)}`.
  Everything is on a finite interval `[s₀, s₁]`, and positivity of the mode there is a
  hypothesis (not derived): when `D` eventually turns negative, as it does in AeST with
  constant `Q > 0`, the mode stops growing and oscillates, and the bounds apply only before.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Set Real

namespace EntEq.Comparison

/-- **Monotonicity lemma.** If `u'' + β u' = E u` on `[s₀, s₁]` with `E · u ≥ 0` there and
`u'(s₀) ≥ 0`, then `u` is non-decreasing on `[s₀, s₁]`. -/
theorem mono_of_forcing (u u' u'' E : ℝ → ℝ) (β s₀ s₁ : ℝ)
    (hu : ∀ s ∈ Icc s₀ s₁, HasDerivAt u (u' s) s) (hu' : ∀ s ∈ Icc s₀ s₁, HasDerivAt u' (u'' s) s)
    (hode : ∀ s ∈ Icc s₀ s₁, u'' s + β * u' s = E s * u s) (hpos : ∀ s ∈ Icc s₀ s₁, 0 ≤ E s * u s)
    (h0 : 0 ≤ u' s₀) : MonotoneOn u (Icc s₀ s₁) := by
  -- `g = e^{βs} u'` is non-decreasing, hence `u' ≥ 0`
  set g := fun s => exp (β * s) * u' s
  have hg : ∀ s ∈ Icc s₀ s₁, HasDerivAt g (exp (β * s) * (E s * u s)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => exp (β * s)) (exp (β * s) * β) s := by
      simpa using ((hasDerivAt_id s).const_mul β).exp
    have := h1.mul (hu' s hs)
    convert this using 1
    rw [← hode s hs]; ring
  have hgmono : MonotoneOn g (Icc s₀ s₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc s₀ s₁)
    · exact fun s hs => (hg s hs).continuousAt.continuousWithinAt
    · rw [interior_Icc]; exact fun s hs => (hg s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro s hs
      rw [(hg s (Ioo_subset_Icc_self hs)).deriv]
      exact mul_nonneg (exp_pos _).le (hpos s (Ioo_subset_Icc_self hs))
  have hu'nn : ∀ s ∈ Icc s₀ s₁, 0 ≤ u' s := by
    intro s hs
    have := hgmono ⟨le_rfl, hs.1.trans hs.2⟩ hs hs.1
    simp only [g] at this
    have hg0 : 0 ≤ exp (β * s₀) * u' s₀ := mul_nonneg (exp_pos _).le h0
    have h2 : 0 ≤ exp (β * s) * u' s := le_trans hg0 this
    exact (mul_nonneg_iff_of_pos_left (exp_pos _)).mp h2
  apply monotoneOn_of_deriv_nonneg (convex_Icc s₀ s₁)
  · exact fun s hs => (hu s hs).continuousAt.continuousWithinAt
  · rw [interior_Icc]; exact fun s hs => (hu s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro s hs
    rw [(hu s (Ioo_subset_Icc_self hs)).deriv]; exact hu'nn s (Ioo_subset_Icc_self hs)

/-- The substitution `u = e^{−ps} χ`: derivatives and the transformed equation. -/
lemma subst (χ χ' χ'' D : ℝ → ℝ) (p c s₀ s₁ : ℝ) (hc : p^2 - p/3 = c)
    (hχ : ∀ s ∈ Icc s₀ s₁, HasDerivAt χ (χ' s) s) (hχ' : ∀ s ∈ Icc s₀ s₁, HasDerivAt χ' (χ'' s) s)
    (hode : ∀ s ∈ Icc s₀ s₁, χ'' s - χ' s / 3 = D s * χ s) :
    let u := fun s => exp (-p * s) * χ s
    let u' := fun s => exp (-p * s) * (χ' s - p * χ s)
    let u'' := fun s => exp (-p * s) * (χ'' s - 2 * p * χ' s + p^2 * χ s)
    (∀ s ∈ Icc s₀ s₁, HasDerivAt u (u' s) s) ∧ (∀ s ∈ Icc s₀ s₁, HasDerivAt u' (u'' s) s) ∧
    (∀ s ∈ Icc s₀ s₁, u'' s + (2 * p - 1/3) * u' s = (D s - c) * u s) := by
  intro u u' u''
  have he : ∀ s, HasDerivAt (fun s => exp (-p * s)) (exp (-p * s) * (-p)) s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul (-p)).exp
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · convert (he s).mul (hχ s hs) using 1; simp only [u']; ring
  · have := (he s).mul ((hχ' s hs).sub ((hχ s hs).const_mul p))
    convert this using 1; simp only [u'', Pi.sub_apply]; ring
  · simp only [u, u', u'']
    have := hode s hs
    rw [← hc]
    have e : χ'' s = D s * χ s + χ' s / 3 := by linarith
    rw [e]; ring

/-- **Lower bound.** If `D ≥ c` on `[s₀, s₁]`, the mode stays positive and starts at least as
steep as `e^{ps}` (`χ'(s₀) ≥ p χ(s₀)`), then `χ(s) ≥ χ(s₀) e^{p(s−s₀)}`: the mode grows at least
as fast as the closed-form `aⁿ`. -/
theorem growth_lower_bound (χ χ' χ'' D : ℝ → ℝ) (p c s₀ s₁ : ℝ) (hc : p^2 - p/3 = c)
    (hχ : ∀ s ∈ Icc s₀ s₁, HasDerivAt χ (χ' s) s) (hχ' : ∀ s ∈ Icc s₀ s₁, HasDerivAt χ' (χ'' s) s)
    (hode : ∀ s ∈ Icc s₀ s₁, χ'' s - χ' s / 3 = D s * χ s)
    (hD : ∀ s ∈ Icc s₀ s₁, c ≤ D s) (hpos : ∀ s ∈ Icc s₀ s₁, 0 < χ s) (hinit : p * χ s₀ ≤ χ' s₀) :
    ∀ s ∈ Icc s₀ s₁, χ s₀ * exp (p * (s - s₀)) ≤ χ s := by
  obtain ⟨hu, hu', hode'⟩ := subst χ χ' χ'' D p c s₀ s₁ hc hχ hχ' hode
  have hm := mono_of_forcing _ _ _ (fun s => D s - c) (2 * p - 1/3) s₀ s₁ hu hu' hode'
    (fun s hs => mul_nonneg (by linarith [hD s hs]) (mul_pos (exp_pos _) (hpos s hs)).le)
    (mul_nonneg (exp_pos _).le (by linarith))
  intro s hs
  have h := hm ⟨le_rfl, hs.1.trans hs.2⟩ hs hs.1
  simp only at h
  have e : exp (p * (s - s₀)) = exp (p * s) * exp (-p * s₀) := by rw [← exp_add]; ring_nf
  have e2 : χ s = exp (p * s) * (exp (-p * s) * χ s) := by
    rw [← mul_assoc, ← exp_add]; simp
  rw [e, e2]
  have := mul_le_mul_of_nonneg_left h (exp_pos (p * s)).le
  linarith

/-- **Upper bound.** If `D ≤ c` on `[s₀, s₁]` (for example when the stabilising `Q` terms are
kept, `AeST.coefficient_le`), the mode stays positive and starts no steeper than `e^{ps}`, then
`χ(s) ≤ χ(s₀) e^{p(s−s₀)}`: while the mode stays positive (assumed, not derived), the `Q`
terms alone can only slow the growth below `aⁿ`. -/
theorem growth_upper_bound (χ χ' χ'' D : ℝ → ℝ) (p c s₀ s₁ : ℝ) (hc : p^2 - p/3 = c)
    (hχ : ∀ s ∈ Icc s₀ s₁, HasDerivAt χ (χ' s) s) (hχ' : ∀ s ∈ Icc s₀ s₁, HasDerivAt χ' (χ'' s) s)
    (hode : ∀ s ∈ Icc s₀ s₁, χ'' s - χ' s / 3 = D s * χ s)
    (hD : ∀ s ∈ Icc s₀ s₁, D s ≤ c) (hpos : ∀ s ∈ Icc s₀ s₁, 0 < χ s) (hinit : χ' s₀ ≤ p * χ s₀) :
    ∀ s ∈ Icc s₀ s₁, χ s ≤ χ s₀ * exp (p * (s - s₀)) := by
  obtain ⟨hu, hu', hode'⟩ := subst χ χ' χ'' D p c s₀ s₁ hc hχ hχ' hode
  have hm := mono_of_forcing (fun s => -(exp (-p * s) * χ s))
    (fun s => -(exp (-p * s) * (χ' s - p * χ s)))
    (fun s => -(exp (-p * s) * (χ'' s - 2 * p * χ' s + p^2 * χ s)))
    (fun s => D s - c) (2 * p - 1/3) s₀ s₁ (fun s hs => (hu s hs).neg) (fun s hs => (hu' s hs).neg)
    (fun s hs => by have := hode' s hs; simp only at this ⊢; linarith)
    (fun s hs => by
      have h1 : D s - c ≤ 0 := by linarith [hD s hs]
      have h2 : 0 < exp (-p * s) * χ s := mul_pos (exp_pos _) (hpos s hs)
      nlinarith)
    (by have := exp_pos (-p * s₀); nlinarith)
  intro s hs
  have h := hm ⟨le_rfl, hs.1.trans hs.2⟩ hs hs.1
  simp only [neg_le_neg_iff] at h
  have e : exp (p * (s - s₀)) = exp (p * s) * exp (-p * s₀) := by rw [← exp_add]; ring_nf
  have e2 : χ s = exp (p * s) * (exp (-p * s) * χ s) := by
    rw [← mul_assoc, ← exp_add]; simp
  rw [e, e2]
  have := mul_le_mul_of_nonneg_left h (exp_pos (p * s)).le
  linarith

end EntEq.Comparison
