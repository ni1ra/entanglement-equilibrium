/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  "Λ is an integration constant, not vacuum energy", made precise. The null-cone lemma only
  ever delivers the *trace-free* part of Einstein's equation (unimodular gravity); `Λ`
  reappears as a constant of integration from the Bianchi identity and conservation. Shifting
  `T` by a vacuum energy `ρ_vac g` leaves the trace-free equation unchanged, so the vacuum
  energy cannot gravitate through it.
-/
import EntEq.Bianchi

namespace EntEq

section Abstract

variable {S V W : Type*} [AddCommGroup S] [Module ℝ S] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- **Trace-free Einstein ⇒ full Einstein with an integration constant.** In `D` dimensions,
the trace-free equation `Ric − (R/D) g = κ (T − (trT/D) g)` together with the
contracted Bianchi identity, `∇·T = 0`, `∇g = 0` and connectedness gives
`Ric − ½R g + Λ g = κ T` for a constant `Λ`. The proof only uses that the trace-free equation
says `Ric − κT ∝ g` (the null-cone output); `D` need not be tied to `tr g` here. -/
theorem unimodular_to_einstein
    (div : V →ₗ[ℝ] W) (d : S →ₗ[ℝ] W) (mulG : S →ₗ[ℝ] V) (one : S)
    (hcompat : ∀ φ, div (mulG φ) = d φ) (hconn : ∀ φ, d φ = 0 → ∃ c : ℝ, φ = c • one)
    (Ric T : V) (R trT : S) (κ D : ℝ)
    (hBianchi : div Ric = (1/2 : ℝ) • d R) (hcons : div T = 0)
    (htf : Ric - (1/D) • mulG R = κ • (T - (1/D) • mulG trT)) :
    ∃ Λ : ℝ, Ric - (1/2 : ℝ) • mulG R + Λ • mulG one = κ • T := by
  apply einstein_of_null_relation div d mulG one hcompat hconn Ric T R
    ((1/D) • R - (κ / D) • trT) κ hBianchi hcons
  rw [map_sub, map_smul, map_smul]
  have : Ric = κ • (T - (1/D) • mulG trT) + (1/D) • mulG R := by rw [← htf]; abel
  rw [this, smul_sub, smul_smul]
  rw [show κ * (1/D) = κ / D by ring]
  abel

/-- **Vacuum energy drops out.** Replacing `T` by `T + ρ_vac g` shifts its trace by `D ρ_vac`
when `tr g = D` (the reading of `trT`), and leaves the trace-free source unchanged. -/
theorem vacuum_energy_drops_out (mulG : S →ₗ[ℝ] V) (T : V) (trT : S) (ρ : S) (D : ℝ)
    (hD : D ≠ 0) :
    (T + mulG ρ) - (1/D) • mulG (trT + D • ρ) = T - (1/D) • mulG trT := by
  rw [map_add, map_smul, smul_add, smul_smul, one_div, inv_mul_cancel₀ hD, one_smul]
  abel

end Abstract

/-- **Schwarzschild saturates the Bekenstein bound.** With `E = Mc²`, radius `R = 2GM/c²`
and `S_BH = A k_B c³/(4Għ)`, `A = 4πR²`: `S_BH = 2π k_B E R/(ħ c)`. -/
theorem bekenstein_saturated (G M c ħ kB : ℝ) (hG : G ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    let R := 2 * G * M / c^2
    let A := 4 * Real.pi * R^2
    A * kB * c^3 / (4 * G * ħ) = 2 * Real.pi * kB * (M * c^2) * R / (ħ * c) := by
  intro R A
  simp only [A, R]
  field_simp

end EntEq
