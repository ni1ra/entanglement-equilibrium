/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The saturation-depth theorem for a slaved dark sector, and the exact Khronon saturation
  scale `k_sat = μ a Q̄` (which reduces to `μ a` only as `Q̄ → 1`).

  Fourier space, comoving wavenumber `k`. A slaved dark sector has density contrast
      Δ = −α Υ − β k² Υ / G₄,      G₄ := 4πG a² ρ̄,
  and pressure only from the local piece, `δP/ρ̄ = c_ad² (−α Υ)`. The effective sound speed
  is `c_s² = δP / (ρ̄ Δ)`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic

open Filter Topology

namespace EntEq.A09

/-- Effective sound speed of the slaved sector (the `Υ` amplitude has cancelled). -/
noncomputable def cs2 (c α β G₄ k : ℝ) : ℝ := c * α / (α + β * k^2 / G₄)

/-- Exact closed form at every `k`: `c_s² k²/a² = D_α · k²/(k² + k_sat²)` with
`D_α = c α G₄/(β a²)` and `k_sat² = α G₄/β`. -/
theorem depth_closed_form (c α β G₄ a k : ℝ) (hα : 0 < α) (hβ : 0 < β) (hG : 0 < G₄)
    (ha : a ≠ 0) :
    cs2 c α β G₄ k * k^2 / a^2 = (c * α * G₄ / (β * a^2)) * (k^2 / (k^2 + α * G₄ / β)) := by
  unfold cs2
  have h1 : 0 < α + β * k^2 / G₄ := by positivity
  have h2 : 0 < k^2 + α * G₄ / β := by positivity
  field_simp
  ring

/-- **Depth theorem.** `c_s² k²/a² → c α G₄/(β a²)` as `k → ∞`. -/
theorem depth_limit (c α β G₄ a : ℝ) (hα : 0 < α) (hβ : 0 < β) (hG : 0 < G₄) (ha : a ≠ 0) :
    Tendsto (fun k => cs2 c α β G₄ k * k^2 / a^2) atTop (𝓝 (c * α * G₄ / (β * a^2))) := by
  have hks : 0 < α * G₄ / β := by positivity
  have hfrac : Tendsto (fun k : ℝ => k^2 / (k^2 + α * G₄ / β)) atTop (𝓝 1) := by
    have : Tendsto (fun k : ℝ => 1 - (α * G₄ / β) / (k^2 + α * G₄ / β)) atTop (𝓝 (1 - 0)) := by
      apply tendsto_const_nhds.sub
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ _ ((tendsto_pow_atTop two_ne_zero))
    simp only [sub_zero] at this
    refine this.congr fun k => ?_
    have : 0 < k^2 + α * G₄ / β := by positivity
    field_simp; ring
  have := hfrac.const_mul (c * α * G₄ / (β * a^2))
  simp only [mul_one] at this
  exact this.congr fun k => (depth_closed_form c α β G₄ a k hα hβ hG ha).symm

/-- With the barotropic local coefficient `α = (1+w)/c_ad²` and `G₄ = 4πG a² ρ̄`, the depth is
`4πG ρ̄ (1+w)/β`: it does not depend on `c_ad²`. (A one-line cancellation once `α` has that
form; the content is in `alpha_forced` and in the slaving ansatz.) -/
theorem depth_universal (c w β G ρ a : ℝ) (hc : c ≠ 0) (hβ : β ≠ 0) (ha : a ≠ 0) :
    c * ((1 + w) / c) * (4 * Real.pi * G * a^2 * ρ) / (β * a^2)
      = 4 * Real.pi * G * ρ * (1 + w) / β := by
  field_simp

/-- **Finite-`k` remainder** (gravitational case `β = 1`, `α = (1+w)/c`): self-gravity minus
the pressure response leaves the fraction `k_sat²/(k² + k_sat²)` of self-gravity. -/
theorem self_gravity_remainder (c w G ρ a k : ℝ) (hc : 0 < c) (hw : 0 < 1 + w) (hG : 0 < G)
    (hρ : 0 < ρ) (ha : a ≠ 0) :
    let G₄ := 4 * Real.pi * G * a^2 * ρ
    let ksat2 := (1 + w) / c * G₄
    (1 + w) * 4 * Real.pi * G * ρ - cs2 c ((1 + w) / c) 1 G₄ k * k^2 / a^2
      = (1 + w) * 4 * Real.pi * G * ρ * (ksat2 / (k^2 + ksat2)) := by
  intro G₄ ksat2
  have hG₄ : 0 < G₄ := by positivity
  rw [depth_closed_form c ((1 + w) / c) 1 G₄ a k (by positivity) one_pos hG₄ ha]
  have : 0 < k^2 + (1 + w) / c * G₄ / 1 := by positivity
  have : 0 < k^2 + ksat2 := by positivity
  simp only [ksat2, G₄, div_one] at *
  field_simp
  ring

/-- **Exact cancellation** (T6), the algebra only: subtracting the saturated pressure response
`4πGρ_d(1+w)δ_d` (the `k → ∞` depth of `depth_limit` with `β = 1`) from the total source
leaves only the other species' term. That the response takes its limiting value is the
`k ≫ k_sat` approximation; `self_gravity_remainder` gives the exact finite-`k` leftover. -/
theorem exact_cancellation (w G ρd ρb δd δb : ℝ) :
    (1 + w) * 4 * Real.pi * G * (ρd * δd + ρb * δb) - 4 * Real.pi * G * ρd * (1 + w) * δd
      = (1 + w) * 4 * Real.pi * G * ρb * δb := by ring

/-- **The `k⁴` escape** (E1): a higher-derivative term `γ k⁴` in the response removes the
stall: `c_s² k² → 0`. -/
theorem k4_escape (c α β γ G₄ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hG : 0 < G₄) :
    Tendsto (fun k : ℝ => c * α / (α + β * k^2 / G₄ + γ * k^4) * k^2) atTop (𝓝 0) := by
  -- bound: `0 ≤ k²/(α + βk²/G₄ + γk⁴) ≤ 1/(γ k²)`
  have hlim : Tendsto (fun k : ℝ => (c * α) * (1 / γ * (k^2)⁻¹)) atTop (𝓝 ((c * α) * (1/γ * 0))) :=
    (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)).const_mul (1/γ) |>.const_mul (c*α)
  rw [mul_zero, mul_zero] at hlim
  have key : ∀ k : ℝ, 0 < k → |c * α / (α + β * k^2 / G₄ + γ * k^4) * k^2|
      ≤ |c * α| * (1 / γ * (k^2)⁻¹) := by
    intro k hk
    have hD : 0 < α + β * k^2 / G₄ + γ * k^4 := by positivity
    rw [show c * α / (α + β * k^2 / G₄ + γ * k^4) * k^2
        = c * α * (k^2 / (α + β * k^2 / G₄ + γ * k^4)) by ring, abs_mul]
    gcongr
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hD]
    have hk2 : 0 < k^2 := by positivity
    field_simp
    nlinarith [sq_nonneg k, mul_pos hβ hk2, hα, mul_pos hk2 hk2]
  have hlim' : Tendsto (fun k : ℝ => |c * α| * (1 / γ * (k^2)⁻¹)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)).const_mul (1/γ)
      |>.const_mul (|c*α|)
    simpa using this
  apply squeeze_zero_norm' _ hlim'
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact key k hk

/-- **`α` from background continuity** (F3), all hypotheses explicit. If the background
density is a differentiable function of `Q̄` (chain rule `ρ̇ = ρ′ Q̇`), `Q̇ = −3H c Q` (a choice
of variable) and `ρ̇ = −3H(ρ + P)`, then `Q ρ′/ρ = (1+w)/c`. That `Υ` is normalised by this
`Q̄` is a separate, physical identification. -/
theorem alpha_forced (ρ P Q H c ρ' Qdot ρdot : ℝ) (hρ : ρ ≠ 0) (hH : H ≠ 0) (hc : c ≠ 0)
    (hchain : ρdot = ρ' * Qdot) (hQ : Qdot = -3 * H * c * Q) (hcont : ρdot = -3 * H * (ρ + P)) :
    Q * ρ' / ρ = (1 + P / ρ) / c := by
  have : Q * ρ' * c = ρ + P := by
    have h := hchain.symm.trans hcont
    rw [hQ] at h
    have : -3 * H * (ρ' * c * Q - (ρ + P)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exfalso; apply hH; linarith
    · linarith
  field_simp
  linarith

/-- **Khronon scale, exact.** Quadratic Khronon background `K = μ²(Q−1)²`,
`8πGρ̄ = Q K_Q − K`, `8πG P̄ = K`, `c_ad² = (Q−1)/Q`: then
`k_sat² = 4πG a² ρ̄ (1+w)/c_ad² = μ² a² Q̄²` for every `Q̄ > 1`. So `k_sat = μ a Q̄`, which
equals the late-time value `μ a` only in the limit `Q̄ → 1`. -/
theorem khronon_ksat_exact (μ a Q G : ℝ) (hQ : 1 < Q) (hG : 0 < G) :
    let K := μ^2 * (Q - 1)^2
    let KQ := 2 * μ^2 * (Q - 1)
    let ρ := (Q * KQ - K) / (8 * Real.pi * G)
    let P := K / (8 * Real.pi * G)
    let cad2 := (Q - 1) / Q
    ρ ≠ 0 → 4 * Real.pi * G * a^2 * ρ * (1 + P / ρ) / cad2 = μ^2 * a^2 * Q^2 := by
  intro K KQ ρ P cad2 hρ
  have hQ1 : Q - 1 ≠ 0 := by linarith
  have hQ0 : Q ≠ 0 := by linarith
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hμ : μ ≠ 0 := by
    rintro rfl; apply hρ; simp [ρ, K, KQ]
  have hQ2 : Q + 1 ≠ 0 := by linarith
  have hρ' : ρ = μ^2 * (Q - 1) * (Q + 1) / (8 * Real.pi * G) := by simp only [ρ, K, KQ]; ring
  have hρ0 : μ^2 * (Q - 1) * (Q + 1) ≠ 0 := by positivity
  rw [hρ']
  simp only [cad2, P, K]
  field_simp
  ring

/-- **The exact Khronon saturation scale has a floor.** With the once-integrated background
`Q̄ = 1 + I₀/(2μ²a³)` (the once-integrated Khronon background), `k_sat = μ a Q̄ = μ a + I₀/(2μ a²)`. Writing
`I₀ = μ² a*³` (`a* > 0`), `k_sat(a) ≥ (3/2) μ a*` for every `a > 0`, with equality exactly at
`a = a*`, where `Q̄ = 3/2`. So modes with `k < (3/2) μ a*` are never saturated, and a mode
above the floor is stalled only between the two epochs where `k_sat(a) = k`. The late-time law
`k_sat = μ a` misses both the floor and the early branch; whether `a*` falls in an observable
epoch depends on `I₀/μ²` (not evaluated here). -/
theorem khronon_ksat_floor (μ a astar : ℝ) (hμ : 0 < μ) (ha : 0 < a) (hs : 0 < astar) :
    3 / 2 * μ * astar ≤ μ * a * (1 + μ^2 * astar^3 / (2 * μ^2 * a^3)) ∧
    (μ * a * (1 + μ^2 * astar^3 / (2 * μ^2 * a^3)) = 3 / 2 * μ * astar ↔ a = astar) := by
  have key : μ * a * (1 + μ^2 * astar^3 / (2 * μ^2 * a^3)) - 3 / 2 * μ * astar
      = μ * (a - astar)^2 * (2 * a + astar) / (2 * a^2) := by
    field_simp; ring
  have hpos : 0 ≤ μ * (a - astar)^2 * (2 * a + astar) / (2 * a^2) := by positivity
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have h0 : μ * (a - astar)^2 * (2 * a + astar) / (2 * a^2) = 0 := by linarith
    have hden : (2 * a^2) ≠ 0 := by positivity
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · have h1 : (a - astar)^2 = 0 := by
        rcases mul_eq_zero.mp h0 with h2 | h2
        · rcases mul_eq_zero.mp h2 with h3 | h3
          · exact absurd h3 hμ.ne'
          · exact h3
        · linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      linarith
    · exact absurd h0 hden
  · intro h; subst h; field_simp; ring

end EntEq.A09
