/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The algebraic core of the gravity-mediated entanglement test (Bose et al. / Marletto–Vedral,
  "BMV"). Two masses, each in an equal superposition of two positions; after time `τ` each
  branch `ab` has picked up the phase `φ_ab = G m₁ m₂ τ/(ħ d_ab)` from the Newtonian
  interaction, so the joint state has amplitudes `c_ab = e^{iφ_ab}/2`. Its concurrence,
  `C = 2|c_LL c_RR − c_LR c_RL|`, equals `|sin(Δφ/2)|` with
  `Δφ = φ_LL + φ_RR − φ_LR − φ_RL`; the state is entangled unless `Δφ ∈ 2πℤ`. If gravity is a
  quantum channel the witness fires; a classical channel predicts none.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

open Complex Real

namespace EntEq.BMV

/-- `‖e^{iA} − e^{iB}‖ = 2|sin((A − B)/2)|`. -/
theorem norm_exp_sub (A B : ℝ) :
    ‖Complex.exp (A * I) - Complex.exp (B * I)‖ = 2 * |Real.sin ((A - B) / 2)| := by
  have h : ‖Complex.exp (A * I) - Complex.exp (B * I)‖^2 = (2 * |Real.sin ((A - B) / 2)|)^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.exp_mul_I, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
    rw [mul_pow, sq_abs]
    have hc : Real.cos (A - B) = 1 - 2 * Real.sin ((A - B) / 2)^2 := by
      rw [show A - B = 2 * ((A - B) / 2) by ring, Real.cos_two_mul, Real.cos_sq']
      ring_nf
    rw [Real.cos_sub] at hc
    nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, hc]
  have h1 : 0 ≤ ‖Complex.exp (A * I) - Complex.exp (B * I)‖ := norm_nonneg _
  have h2 : 0 ≤ 2 * |Real.sin ((A - B) / 2)| := by positivity
  nlinarith [h, h1, h2, sq_nonneg (‖Complex.exp (A * I) - Complex.exp (B * I)‖ - 2 * |Real.sin ((A - B) / 2)|)]

/-- **Concurrence of the BMV state.** -/
theorem concurrence (φLL φLR φRL φRR : ℝ) :
    let c := fun φ : ℝ => Complex.exp (φ * I) / 2
    2 * ‖c φLL * c φRR - c φLR * c φRL‖ = |Real.sin ((φLL + φRR - φLR - φRL) / 2)| := by
  intro c
  have e1 : c φLL * c φRR = Complex.exp (((φLL + φRR : ℝ)) * I) / 4 := by
    simp only [c]; push_cast; rw [add_mul, Complex.exp_add]; ring
  have e2 : c φLR * c φRL = Complex.exp (((φLR + φRL : ℝ)) * I) / 4 := by
    simp only [c]; push_cast; rw [add_mul, Complex.exp_add]; ring
  rw [e1, e2, ← sub_div, norm_div, norm_exp_sub]
  have : ‖(4 : ℂ)‖ = 4 := by simp
  rw [this, show φLL + φRR - (φLR + φRL) = φLL + φRR - φLR - φRL by ring]
  ring

/-- The witness is silent exactly when `Δφ ∈ 2πℤ`. -/
theorem unentangled_iff (Δφ : ℝ) : |Real.sin (Δφ / 2)| = 0 ↔ ∃ k : ℤ, Δφ = 2 * π * k := by
  rw [abs_eq_zero, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩

end EntEq.BMV
