/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The 2016 derivation end to end: stationarity of the generalized entropy of every small ball,
  at every point and in every rest frame, gives the Einstein equation with a constant `Λ`.
-/
import EntEq.Ball2016
import EntEq.Equilibrium2016

open Matrix

namespace EntEq

variable {n : ℕ} {M : Type*}

/-- **Entanglement equilibrium ⇒ Einstein (2016).** At each point `x` and each unit timelike
`u`, the ball of radius `ℓ` in `d = m + 2` dimensions has area deficit
`δA = −Ω ℓ^d (G(u,u) − λ(x))/(d²−1)` (Jacobson's eq. 22, `λ` the curvature scale of the
maximally symmetric reference state; `area_deficit_fixed_volume` derives the `λ = 0` form from
the volume deficit) and entanglement change `δS = (2π/ħ) Ω T(u,u) ∫ weight` (conformal
matter, `δX = 0`). If `δS_gen = δA/(4Għ) + δS = 0` for all of them, and the fields satisfy the
hypotheses of `equilibrium_chain`, then `G + Λ g = 8πG T` with `Λ` a spacetime constant. -/
theorem ball_to_einstein (m : ℕ) (_hdim : m + 1 = n) (ℓ Ω ħ G : ℝ) (hℓ : 0 < ℓ) (hΩ : Ω ≠ 0)
    (hħ : ħ ≠ 0) (hG : G ≠ 0)
    {V S W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup S] [Module ℝ S]
    [AddCommGroup W] [Module ℝ W]
    (P : M → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hP : ∀ x, IsUnit (P x).det)
    (evV : V →ₗ[ℝ] (M → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) (hevV : Function.Injective evV)
    (evS : S →ₗ[ℝ] (M → ℝ))
    (mulG : S →ₗ[ℝ] V) (hmulG : ∀ φ x, evV (mulG φ) x = evS φ x • ((P x)ᵀ * eta n * P x))
    (one : S) (div : V →ₗ[ℝ] W) (d : S →ₗ[ℝ] W)
    (hcompat : ∀ φ, div (mulG φ) = d φ) (hconn : ∀ φ, d φ = 0 → ∃ c : ℝ, φ = c • one)
    (Gt T : V) (lam : S) (hGs : ∀ x, (evV Gt x).IsSymm) (hTs : ∀ x, (evV T x).IsSymm)
    (hstat : ∀ x u, qf ((P x)ᵀ * eta n * P x) u = -1 →
      1 / (4 * G * ħ) * (-Ω * ℓ^(m+2) * (qf (evV Gt x) u - evS lam x) / (((m:ℝ) + 2)^2 - 1))
        + 2 * Real.pi / ħ * Ω * qf (evV T x) u
          * (∫ r in (0:ℝ)..ℓ, r^m * (ℓ^2 - r^2) / (2 * ℓ)) = 0)
    (hBianchi : div Gt = 0) (hcons : div T = 0) :
    ∃ Λ : ℝ, Gt + Λ • mulG one = (8 * Real.pi * G) • T := by
  have hEq : ∀ x u, qf ((P x)ᵀ * eta n * P x) u = -1 →
      qf (evV Gt x) u - evS lam x = (8 * Real.pi * G) * qf (evV T x) u := fun x u hu =>
    Ball.ball_equilibrium m ℓ Ω ħ G (qf (evV Gt x) u - evS lam x) (qf (evV T x) u) _ _ hℓ hΩ hħ
      hG rfl rfl (hstat x u hu)
  obtain ⟨hfield, c, hc⟩ := equilibrium_chain P hP evV hevV evS mulG hmulG one div d hcompat
    hconn Gt T lam (8 * Real.pi * G) hGs hTs hEq hBianchi hcons
  refine ⟨c, ?_⟩
  rw [← map_smul, ← hc]; exact hfield

end EntEq
