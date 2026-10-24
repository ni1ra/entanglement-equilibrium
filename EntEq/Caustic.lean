/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The focusing theorem behind the Penrose–Hawking singularity theorems, for a null congruence:
  with the null energy condition `R_kk ≥ 0` and initial convergence `θ(0) = θ₀ < 0`, the
  Raychaudhuri equation forbids a regular solution beyond affine distance `(d−2)/|θ₀|`.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

open Set

namespace EntEq

/-- **Caustic theorem.** Let `θ` be continuous on `[0, s₁]` and solve
`θ′ = −θ²/(d−2) − σ² − R` on `(0, s₁)` with `d > 2`, `R ≥ 0` (null energy condition) and
`θ(0) = θ₀ < 0`. Then necessarily `s₁ < (d−2)/(−θ₀)`: no regular solution reaches that
affine distance, so the congruence develops a caustic (`θ → −∞`) before it. (The proof shows
`1/θ(s) − s/(d−2)` is non-decreasing while `θ < 0`.) -/
theorem caustic (θ σ R : ℝ → ℝ) (d s₁ θ₀ : ℝ) (hd : 2 < d) (hs₁ : 0 ≤ s₁)
    (hθc : ContinuousOn θ (Icc 0 s₁))
    (hθ : ∀ s ∈ Ioo 0 s₁, HasDerivAt θ (-(θ s)^2/(d-2) - (σ s)^2 - R s) s)
    (hR : ∀ s, 0 ≤ R s) (hθ0 : θ 0 = θ₀) (hneg : θ₀ < 0) :
    s₁ < (d - 2) / (-θ₀) := by
  have hd2 : 0 < d - 2 := by linarith
  -- the right-hand side is `≤ −θ²/(d−2) ≤ 0`
  have hle : ∀ s, -(θ s)^2/(d-2) - (σ s)^2 - R s ≤ -(θ s)^2/(d-2) := by
    intro s; nlinarith [sq_nonneg (σ s), hR s]
  have hnp : ∀ s, -(θ s)^2/(d-2) ≤ 0 := fun s => by
    rw [neg_div]; exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) hd2.le)
  -- θ is antitone, hence `θ ≤ θ₀ < 0`
  have hanti : AntitoneOn θ (Icc 0 s₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s₁) hθc
    · rw [interior_Icc]; exact fun s hs => (hθ s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro s hs; rw [(hθ s hs).deriv]; exact (hle s).trans (hnp s)
  have hθneg : ∀ s ∈ Icc 0 s₁, θ s < 0 := by
    intro s hs
    have := hanti ⟨le_refl 0, hs₁⟩ hs hs.1
    rw [hθ0] at this; linarith
  -- `u = 1/θ − s/(d−2)` is monotone
  set u := fun s => (θ s)⁻¹ - s / (d - 2)
  have hmono : MonotoneOn u (Icc 0 s₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 s₁)
    · exact (hθc.inv₀ fun s hs => (hθneg s hs).ne).sub (continuousOn_id.div_const _)
    · rw [interior_Icc]; intro s hs
      have hs' : s ∈ Icc 0 s₁ := Ioo_subset_Icc_self hs
      exact (((hθ s hs).inv (hθneg s hs').ne).sub ((hasDerivAt_id s).div_const _)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro s hs
      have hs' : s ∈ Icc 0 s₁ := Ioo_subset_Icc_self hs
      have hθs := hθneg s hs'
      have hu : HasDerivAt u (-(-(θ s)^2/(d-2) - (σ s)^2 - R s) / (θ s)^2 - 1 / (d - 2)) s := by
        have := ((hθ s hs).inv hθs.ne).sub ((hasDerivAt_id s).div_const (d - 2))
        exact this
      rw [hu.deriv]
      have hsq : 0 < (θ s)^2 := by nlinarith
      have key : -(-(θ s)^2/(d-2) - (σ s)^2 - R s) / (θ s)^2 ≥ 1 / (d - 2) := by
        rw [ge_iff_le, div_le_div_iff₀ hd2 hsq]
        have e : (θ s)^2 / (d-2) * (d-2) = (θ s)^2 := div_mul_cancel₀ _ hd2.ne'
        have e2 : -(-(θ s)^2/(d-2) - (σ s)^2 - R s) * (d - 2)
            = (θ s)^2/(d-2) * (d-2) + ((σ s)^2 + R s) * (d - 2) := by ring
        rw [e2, e]
        nlinarith [mul_nonneg (add_nonneg (sq_nonneg (σ s)) (hR s)) hd2.le]
      simp only [id, one_div] at key ⊢
      linarith
  -- evaluate at `s₁`: `1/θ(s₁) ≥ 1/θ₀ + s₁/(d−2)`, and the left side is negative
  have h := hmono ⟨le_refl 0, hs₁⟩ ⟨hs₁, le_refl s₁⟩ hs₁
  simp only [u, hθ0, zero_div, sub_zero] at h
  have hinv : (θ s₁)⁻¹ < 0 := inv_lt_zero.mpr (hθneg s₁ ⟨hs₁, le_refl _⟩)
  have : θ₀⁻¹ + s₁ / (d - 2) < 0 := by linarith
  rw [lt_div_iff₀ (by linarith)]
  have h2 : s₁ / (d - 2) < -θ₀⁻¹ := by linarith
  rw [div_lt_iff₀ hd2] at h2
  have : -θ₀⁻¹ * (d - 2) * (-θ₀) = d - 2 := by field_simp [hneg.ne]
  nlinarith [mul_lt_mul_of_pos_right h2 (by linarith : (0:ℝ) < -θ₀)]

end EntEq
