/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The converse directions, so that the equivalences the derivations are quoted for
  ("Clausius on every local horizon ⇔ Einstein", "entanglement equilibrium of every small
  ball ⇔ Einstein") are proved both ways.
-/
import EntEq.Clausius
import EntEq.Ball2016
import EntEq.Equilibrium2016

open Matrix Filter Topology

namespace EntEq

variable {n : ℕ}

/-- **Einstein ⇒ null relation.** If `Ric − ½R g + Λ g = κ T` at a point, then
`Ric(k,k) = κ T(k,k)` for every `g`-null `k`: the trace and `Λ` terms are invisible on the
light cone. -/
theorem einstein_to_null (g Ric T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R Λ κ : ℝ)
    (hE : Ric - (1/2 : ℝ) • (R • g) + Λ • g = κ • T) (k : Fin (n+1) → ℝ) (hk : qf g k = 0) :
    qf Ric k = κ * qf T k := by
  have := congrArg (fun M => qf M k) hE
  simp only [qf, Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at this hk ⊢
  rw [hk] at this
  linarith

/-- **Einstein ⇒ Clausius along a generator.** If `R_kk = 8πG T_kk` along the generator,
the Clausius combination vanishes identically, not just to `o(ε²)`. -/
theorem einstein_to_clausius (T R : ℝ → ℝ) (κ ħ G : ℝ) (hħ : ħ ≠ 0) (hG : G ≠ 0)
    (hE : ∀ s, R s = 8 * Real.pi * G * T s) (ε : ℝ) :
    κ * (∫ s in (0:ℝ)..ε, s * T s)
      - (ħ * κ / (2 * Real.pi)) * (1 / (4 * G * ħ)) * (∫ s in (0:ℝ)..ε, s * R s) = 0 := by
  simp_rw [hE]
  have : (fun s => s * (8 * Real.pi * G * T s)) = fun s => (8 * Real.pi * G) * (s * T s) := by
    ext s; ring
  rw [this, intervalIntegral.integral_const_mul]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Einstein ⇒ ball stationarity.** Substituting `G₀₀ = 8πG T₀₀` into the area deficit makes
the generalized entropy of the small ball stationary: `η δA + δS_ent = 0`. With
`ball_equilibrium`, an equivalence. -/
theorem einstein_to_ball (m : ℕ) (ℓ Ω ħ G T00 : ℝ) (hℓ : 0 < ℓ) (hħ : ħ ≠ 0) (hG : G ≠ 0) :
    1 / (4 * G * ħ) * (-Ω * ℓ^(m+2) * (8 * Real.pi * G * T00) / (((m:ℝ) + 2)^2 - 1))
      + 2 * Real.pi / ħ * Ω * T00 * (∫ r in (0:ℝ)..ℓ, r^m * (ℓ^2 - r^2) / (2 * ℓ)) = 0 := by
  rw [Ball.ball_weight m ℓ hℓ.ne']
  have hd : ((m:ℝ) + 2)^2 - 1 ≠ 0 := by
    have : ((m:ℝ) + 2)^2 - 1 = (m + 1) * (m + 3) := by ring
    rw [this]; positivity
  field_simp
  ring

end EntEq
