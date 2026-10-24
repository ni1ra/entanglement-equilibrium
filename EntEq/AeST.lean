/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The AeST field-sector overgrowth theorem, built on the published FLRW perturbation
  equations of arXiv:2007.00082.

  In the cold limit `c_ad² → 0` the `(χ, E)` pair obeys
      χ̇ = Q E,     K_B (Ė + H E) = [K′ − (2 − K_B)(H + Q)] χ.
  On a matter-dominated background with `ρ̂ = 3H²f_c`, `Q K′ = ρ̂` and `H ≫ Q`, the growth
  exponent of `χ ∝ aⁿ` is `n = ¼ + ¾ √(1/9 + 16 f_c / (3 K_B))`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Real

namespace EntEq.AeST

/-- The closed-form growth exponent `n(K_B, f_c)`. Meaningful for `K_B > 0`, `f_c ≥ 0`; outside that
domain Lean's conventions (`x/0 = 0`, `√(negative) = 0`) give junk values. Theorems that do
not assume `f_c ≥ 0` (`overgrowth_iff`, `overgrowth_with_Q`) stay true as statements about
`nExp`, but `nExp` is a growth exponent only when `1/9 + 16f/(3K_B) ≥ 0`. The `overgrowth_*` theorems are statements about this function;
the link to AeST is `eliminate_E` + `coefficient_with_Q` + `power_law_solves`. -/
noncomputable def nExp (K f : ℝ) : ℝ := 1/4 + 3/4 * √(1/9 + 16 * f / (3 * K))

/-! ### 1. Eliminating `E`: the second-order equation, with its hidden hypothesis -/

/-- From `χ̇ = Q E` and `K (Ė + H E) = M χ` with **constant** `Q` (the asymptotic AeST
background `φ̇ → Q₀`), `χ̈ + H χ̇ = (Q M / K) χ`. A time-dependent `Q` would add `(Q̇/Q) χ̇`. -/
theorem eliminate_E (χ E E' H M : ℝ → ℝ) (Q K : ℝ) (hK : K ≠ 0)
    (hχ : ∀ t, HasDerivAt χ (Q * E t) t) (hE : ∀ t, HasDerivAt E (E' t) t)
    (hfield : ∀ t, K * (E' t + H t * E t) = M t * χ t) (t : ℝ) :
    deriv (deriv χ) t + H t * deriv χ t = Q * M t / K * χ t := by
  have h1 : deriv χ = fun s => Q * E s := funext fun s => (hχ s).deriv
  have h2 : deriv (deriv χ) t = Q * E' t := by rw [h1]; exact ((hE t).const_mul Q).deriv
  rw [h2, h1]
  have hE' : E' t = M t * χ t / K - H t * E t := by
    field_simp; linarith [hfield t]
  rw [hE']; field_simp; ring

/-- **The coefficient with its `Q` terms kept.** With `M = K′ − (2−K_B)(H+Q)`, `Q K′ = ρ̂`
(dust, `w = 0`) and `ρ̂ = 3H²f_c`: `Q M / K_B = 3H² f_eff / K_B` with
`f_eff = f_c − (2−K_B) q (1+q)/3`, `q = Q/H`. The `H ≫ Q` limit is `q → 0`. -/
theorem coefficient_with_Q (K H Q f K' : ℝ) (hK : K ≠ 0) (hH : H ≠ 0)
    (hρ : Q * K' = 3 * H^2 * f) :
    Q * (K' - (2 - K) * (H + Q)) / K = 3 * H^2 * (f - (2 - K) * (Q/H) * (1 + Q/H) / 3) / K := by
  have : Q * (K' - (2 - K) * (H + Q)) = 3 * H^2 * f - (2 - K) * Q * (H + Q) := by
    rw [mul_sub, hρ]; ring
  rw [this]; field_simp

/-- The dropped `Q` terms are stabilising: for `Q ≥ 0`, `H > 0`, `0 < K_B < 2` the exact
coefficient is at most the `H ≫ Q` value `3H²f_c/K_B`. So `H ≫ Q` is an approximation in the
*destabilising* direction. (Remark, not proved here: the formula does not cover finite `c_ad²`, radiation or
back-reaction.) -/
theorem coefficient_le (K H Q f K' : ℝ) (hK0 : 0 < K) (hK2 : K < 2) (hH : 0 < H) (hQ : 0 ≤ Q)
    (hρ : Q * K' = 3 * H^2 * f) :
    Q * (K' - (2 - K) * (H + Q)) / K ≤ 3 * H^2 * f / K := by
  apply div_le_div_of_nonneg_right _ hK0.le
  have : Q * (K' - (2 - K) * (H + Q)) = 3 * H^2 * f - (2 - K) * Q * (H + Q) := by
    rw [mul_sub, hρ]; ring
  rw [this]
  have : 0 ≤ (2 - K) * Q * (H + Q) := by
    apply mul_nonneg (mul_nonneg (by linarith) hQ); linarith
  linarith

/-! ### 2. The Einstein–de Sitter power law solves the reduced equation -/

/-- With `a = t^{2/3}`, `H = 2/(3t)` and `p = 2n/3`, `χ = aⁿ = t^p` satisfies
`χ̈ + H χ̇ = (3 H² f / K) χ` for every `t > 0`: the closed form is an exact solution. -/
theorem power_law_solves (K f : ℝ) (hK : 0 < K) (hf : 0 ≤ f) (t : ℝ) (ht : 0 < t) :
    let p := 2/3 * nExp K f
    let χ := fun s : ℝ => s ^ p
    let H := 2 / (3 * t)
    deriv (deriv χ) t + H * deriv χ t = 3 * H^2 * f / K * χ t := by
  intro p χ H
  -- the indicial equation `p² − p/3 − 4f/(3K) = 0`
  have hs : 0 ≤ 1/9 + 16 * f / (3 * K) := by positivity
  have hsq := Real.sq_sqrt hs
  have hind : p^2 - p/3 - 4*f/(3*K) = 0 := by
    have hp : p = 1/6 + √(1/9 + 16 * f / (3 * K)) / 2 := by simp only [p, nExp]; ring
    rw [hp]
    have : (1/6 + √(1/9 + 16 * f / (3 * K)) / 2)^2 - (1/6 + √(1/9 + 16 * f / (3 * K)) / 2)/3
        = √(1/9 + 16 * f / (3 * K))^2 / 4 - 1/36 := by ring
    rw [this, hsq]; field_simp; ring
  have d1 : ∀ s, 0 < s → deriv χ s = p * s^(p-1) := fun s hs =>
    (Real.hasDerivAt_rpow_const (Or.inl hs.ne')).deriv
  have d1' : deriv χ =ᶠ[nhds t] fun s => p * s^(p-1) :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs => d1 s hs
  have d2 : deriv (deriv χ) t = p * ((p-1) * t^(p-1-1)) := by
    rw [d1'.deriv_eq]
    exact ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul p).deriv
  rw [d2, d1 t ht]
  simp only [χ, H]
  have e1 : t^(p-1) = t^p / t := by rw [Real.rpow_sub_one ht.ne']
  have e2 : t^(p-1-1) = t^p / t^2 := by
    rw [Real.rpow_sub_one ht.ne', Real.rpow_sub_one ht.ne']; ring
  rw [e1, e2]
  have htp : 0 < t^p := Real.rpow_pos_of_pos ht p
  field_simp
  have : p^2 = p/3 + 4*f/(3*K) := by linarith
  field_simp at this
  nlinarith [this, htp]

/-- `χ = aⁿ` with `a = t^{2/3}` is the same function as `t^p`, `p = 2n/3`. -/
theorem a_pow_n (K f t : ℝ) (ht : 0 ≤ t) :
    (t^(2/3 : ℝ))^(nExp K f) = t^(2/3 * nExp K f) := by
  rw [← Real.rpow_mul ht]

/-! ### 3. The overgrowth bounds -/

/-- `n` is strictly decreasing in `K_B` (for `f_c > 0`). -/
theorem nExp_strictAnti (f : ℝ) (hf : 0 < f) {K₁ K₂ : ℝ} (h1 : 0 < K₁) (h12 : K₁ < K₂) :
    nExp K₂ f < nExp K₁ f := by
  unfold nExp
  have : 16 * f / (3 * K₂) < 16 * f / (3 * K₁) := by
    apply div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)
  have h0 : 0 ≤ 1/9 + 16 * f / (3 * K₂) := by
    have : 0 < 16 * f / (3 * K₂) := div_pos (by linarith) (by linarith)
    linarith
  have := Real.sqrt_lt_sqrt h0 (by linarith : 1/9 + 16 * f / (3 * K₂) < 1/9 + 16 * f / (3 * K₁))
  linarith

/-- **Overgrowth at `f_c = 1`:** on the whole stability window `0 < K_B < 2`, `n > 3/2`. -/
theorem overgrowth_fc_one (K : ℝ) (hK0 : 0 < K) (hK2 : K < 2) : 3/2 < nExp K 1 := by
  have h2 : nExp 2 1 = 3/2 := by
    unfold nExp
    rw [show (1:ℝ)/9 + 16 * 1 / (3 * 2) = (5/3)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  rw [← h2]; exact nExp_strictAnti 1 one_pos hK0 hK2

/-- `3/2` is sharp: it is the infimum of `n(K_B, 1)` on the window, approached as `K_B → 2`. -/
theorem overgrowth_fc_one_sharp (ε : ℝ) (hε : 0 < ε) : ∃ K, 0 < K ∧ K < 2 ∧ nExp K 1 < 3/2 + ε := by
  have hc : ContinuousAt (fun K => nExp K 1) 2 := by
    unfold nExp
    fun_prop (disch := norm_num)
  have h2 : nExp 2 1 = 3/2 := by
    unfold nExp
    rw [show (1:ℝ)/9 + 16 * 1 / (3 * 2) = (5/3)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨2 - min (δ/2) 1, by linarith [min_le_right (δ/2) 1], by
    linarith [lt_min (half_pos hδ) one_pos], ?_⟩
  have hd : dist (2 - min (δ/2) 1) 2 < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by simp [lt_min (half_pos hδ) one_pos])]
    simp only [sub_sub_cancel]; linarith [min_le_left (δ/2) 1]
  have := hball hd
  rw [h2, Real.dist_eq] at this
  linarith [abs_lt.mp this]

/-- **Overgrowth at the realistic matter-era `f_c = 0.78`:** `n > 1.36` on the window. -/
theorem overgrowth_fc_078 (K : ℝ) (hK0 : 0 < K) (hK2 : K < 2) : 1.36 < nExp K 0.78 := by
  have hlt := nExp_strictAnti 0.78 (by norm_num) hK0 hK2
  have h2 : 1.36 < nExp 2 0.78 := by
    unfold nExp
    have : (1.48:ℝ) < √(1/9 + 16 * 0.78 / (3 * 2)) := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  linarith

/-- **Exact threshold.** For `K_B > 0`, `f_c ≥ 0`: the field sector outgrows the CDM mode
(`n > 1`) exactly when `f_c > K_B / 6`. -/
theorem overgrowth_iff (K f : ℝ) (hK : 0 < K) : 1 < nExp K f ↔ K / 6 < f := by
  unfold nExp
  have key : 1 < √(1/9 + 16 * f / (3 * K)) ↔ K / 6 < f := by
    rw [Real.lt_sqrt (by norm_num)]
    constructor
    · intro h
      have : 8/9 < 16 * f / (3 * K) := by linarith
      rw [lt_div_iff₀ (by positivity)] at this; linarith
    · intro h
      have : 8/9 < 16 * f / (3 * K) := by rw [lt_div_iff₀ (by positivity)]; linarith
      linarith
  constructor
  · intro h; exact key.mp (by linarith)
  · intro h; linarith [key.mpr h]

/-- **The whole window.** Overgrowth (`n > 1`) holds for every `K_B ∈ (0, 2)` iff
`f_c ≥ 1/3`. So the theorem needs only that the field carries at least a third of the
critical density; the matter-era value 0.78 clears it by a factor 2.3. -/
theorem overgrowth_window_iff (f : ℝ) (hf : 0 ≤ f) :
    (∀ K, 0 < K → K < 2 → 1 < nExp K f) ↔ 1/3 ≤ f := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    -- pick `K = 6f`, inside the window when `f < 1/3`, where `n = 1` exactly
    by_cases hf0 : f = 0
    · have := (overgrowth_iff 1 f one_pos).mp (h 1 one_pos (by norm_num)); linarith
    · have hfpos : 0 < f := lt_of_le_of_ne hf (Ne.symm hf0)
      have := (overgrowth_iff (6*f) f (by positivity)).mp (h (6*f) (by positivity) (by linarith))
      linarith
  · intro h K hK0 hK2
    exact (overgrowth_iff K f hK0).mpr (by linarith)

/-- Quasi-static reading (`q = Q/H` frozen; on Einstein–de Sitter `q ∝ t`, so this is a
local-in-time diagnostic, not a solution): overgrowth `n(K_B, f_eff) > 1` iff
`f_c − (2−K_B) q(1+q)/3 > K_B/6`. -/
theorem overgrowth_with_Q (K f q : ℝ) (hK : 0 < K) :
    1 < nExp K (f - (2 - K) * q * (1 + q) / 3) ↔ K / 6 < f - (2 - K) * q * (1 + q) / 3 :=
  overgrowth_iff K _ hK

/-! ### 4. The `Q₀` floor -/

/-- With every quantity positive and `K_B < 2`, the overgrowth epoch ends before today,
`a_crit = [3H₀²Ω_c/((2−K_B)Q₀²)]^{1/3} < 1`, iff `Q₀ > H₀ √(3Ω_c/(2−K_B))`. -/
theorem q0_floor (H₀ Ωc Q₀ K : ℝ) (hH : 0 < H₀) (hΩ : 0 < Ωc) (hQ : 0 < Q₀) (hK : K < 2) :
    (3 * H₀^2 * Ωc / ((2 - K) * Q₀^2)) ^ (1/3 : ℝ) < 1 ↔ H₀ * √(3 * Ωc / (2 - K)) < Q₀ := by
  have h2K : 0 < 2 - K := by linarith
  set x := 3 * H₀^2 * Ωc / ((2 - K) * Q₀^2) with hxdef
  have hx : 0 ≤ x := by positivity
  have hroot : x ^ (1/3 : ℝ) < 1 ↔ x < 1 := by
    constructor
    · intro h; by_contra hc; push Not at hc
      linarith [Real.one_le_rpow hc (by norm_num : (0:ℝ) ≤ 1/3)]
    · intro h; exact Real.rpow_lt_one hx h (by norm_num)
  rw [hroot, show H₀ * √(3 * Ωc / (2 - K)) = √(H₀^2 * (3 * Ωc / (2 - K))) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hH.le]]
  rw [Real.sqrt_lt' hQ, hxdef, div_lt_one (by positivity), mul_div_assoc', div_lt_iff₀ h2K]
  constructor <;> intro h <;> linarith

end EntEq.AeST
