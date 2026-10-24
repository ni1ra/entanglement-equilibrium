/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The Riemann-normal-coordinate metric expansion, reduced to the normal-coordinate gauge.
  At the origin of normal coordinates `g = δ`, `Γ = 0`, and the symmetrised derivatives of `Γ`
  vanish (geodesics through the origin are straight lines). Writing
  `h_{ab,cd} = ∂_c∂_d g_ab(0)` (symmetric in `ab` and in `cd`),
  `∂_d Γ_{abc} = ½(h_{ab,cd} + h_{ac,bd} − h_{bc,ad})` and
  `R_{abcd} = ∂_c Γ_{adb} − ∂_d Γ_{acb}` at the origin, the gauge condition
  `∂_dΓ_{abc} + ∂_bΓ_{acd} + ∂_cΓ_{adb} = 0` forces `h_{ab,cd} = −⅓(R_{acbd} + R_{adbc})`, so
  `g_ab(x) = δ_ab − ⅓ R_{acbd} x^c x^d + O(|x|³)`, matching the index pattern `BallVolume`
  assumes (`rncQuad`). Assumed, not proved: that normal coordinates exist (the exponential map),
  that `R` here equals the Riemann tensor of `g` at the origin (true when `Γ(0) = 0`, `g(0) = δ`;
  not linked in Lean to `Curved.riem`), and Taylor's theorem for the `O(|x|³)` remainder.
-/
import Mathlib.Tactic

namespace EntEq.RNC

variable {m : ℕ}

/-- `∂_d Γ_{abc}` at the origin, in terms of the second derivatives of the metric. -/
noncomputable def dΓ (h : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  (h a b c d + h a c b d - h b c a d) / 2

/-- Riemann tensor at the origin (all `Γ` vanish there). -/
noncomputable def R (h : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  dΓ h a d b c - dΓ h a c b d

/-- **Second derivatives of the metric in normal coordinates.** -/
theorem metric_second_derivative (h : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hs1 : ∀ a b c d, h a b c d = h b a c d) (hs2 : ∀ a b c d, h a b c d = h a b d c)
    (hgauge : ∀ a b c d, dΓ h a b c d + dΓ h a c d b + dΓ h a d b c = 0) (a b c d : Fin m) :
    h a b c d = -(1/3) * (R h a c b d + R h a d b c) := by
  have g1 := hgauge a b c d
  have g2 := hgauge b a c d
  simp only [R, dΓ] at *
  have := hs1 a b c d; have := hs1 a c b d; have := hs1 a d b c; have := hs1 b c a d
  have := hs1 b d a c; have := hs1 c d a b; have := hs1 a c d b; have := hs1 a d c b
  have := hs1 b c d a; have := hs1 b d c a; have := hs1 c d b a
  have := hs2 a b c d; have := hs2 a c b d; have := hs2 a d b c; have := hs2 b c a d
  have := hs2 b d a c; have := hs2 c d a b; have := hs2 b a c d; have := hs2 c a b d
  have := hs2 d a b c; have := hs2 c b a d; have := hs2 d b a c; have := hs2 d c a b
  have := hs1 b a d c; have := hs1 c a d b; have := hs1 d a c b; have := hs1 c b d a
  have := hs1 d b c a; have := hs1 d c b a
  linarith

/-- Consequently the quadratic term of the metric is `−⅓ R_{acbd} x^c x^d`. -/
theorem metric_quadratic_term (h : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hs1 : ∀ a b c d, h a b c d = h b a c d) (hs2 : ∀ a b c d, h a b c d = h a b d c)
    (hgauge : ∀ a b c d, dΓ h a b c d + dΓ h a c d b + dΓ h a d b c = 0)
    (x : Fin m → ℝ) (a b : Fin m) :
    (1/2) * ∑ c, ∑ d, h a b c d * x c * x d = -(1/3) * ∑ c, ∑ d, R h a c b d * x c * x d := by
  have key : ∀ c d, h a b c d = -(1/3) * (R h a c b d + R h a d b c) :=
    metric_second_derivative h hs1 hs2 hgauge a b
  simp_rw [key]
  have swap : ∑ c, ∑ d, R h a d b c * x c * x d = ∑ c, ∑ d, R h a c b d * x c * x d := by
    rw [Finset.sum_comm]; congr 1; ext c; congr 1; ext d; ring
  have expand : ∑ c, ∑ d, -(1/3) * (R h a c b d + R h a d b c) * x c * x d
      = -(1/3) * (∑ c, ∑ d, R h a c b d * x c * x d + ∑ c, ∑ d, R h a d b c * x c * x d) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; ext c
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; ext d; ring
  rw [expand, swap]; ring

end EntEq.RNC
