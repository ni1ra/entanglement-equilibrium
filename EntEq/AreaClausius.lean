/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Closing the Raychaudhuri → area → Clausius gap. Instead of postulating
  `δA = ∫ s R_kk ds`, the area change is the integrated expansion, `δA(ε) = −∫₀^ε θ`, with
  generators parametrised by `s ≥ 0` running back from the bifurcation point `p`; a positive
  `R_kk` focuses them, so the cross-section at `p` exceeds the past one by `δA > 0`. Only the
  Raychaudhuri equation **at the bifurcation point** is used (`θ(0) = σ(0) = 0` give
  `θ′(0) = −R(0)`), which is all the leading order needs.
-/
import EntEq.Clausius

open Filter Topology intervalIntegral

namespace EntEq

/-- `∫₀^ε θ / ε² → θ′(0)/2` for continuous `θ` with `θ(0) = 0` and a derivative at `0`. -/
theorem integral_second_order (θ : ℝ → ℝ) (θ' : ℝ) (hc : Continuous θ) (h0 : θ 0 = 0)
    (hd : HasDerivAt θ θ' 0) :
    Tendsto (fun ε => (∫ s in (0:ℝ)..ε, θ s) / ε^2) (𝓝[>] 0) (𝓝 (θ' / 2)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT (f' := θ) (g' := fun ε => 2 * ε)
  · exact Eventually.of_forall fun ε => (hc.integral_hasStrictDerivAt 0 ε).hasDerivAt
  · exact Eventually.of_forall fun ε => by simpa using hasDerivAt_pow 2 ε
  · exact eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => by positivity
  · have : Continuous fun ε => ∫ s in (0:ℝ)..ε, θ s :=
      continuous_iff_continuousAt.mpr fun ε => (hc.integral_hasStrictDerivAt 0 ε).hasDerivAt.continuousAt
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  · simpa using ((continuous_pow 2).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  · -- `θ ε / (2ε) = (slope θ 0 ε)/2 → θ'/2`
    have hs := (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0:ℝ))).div_const 2
    refine hs.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    rw [slope_def_field, h0, sub_zero, sub_zero]
    field_simp

/-- **Clausius from Raychaudhuri.** Along a generator, let `θ` solve
`θ′ = −θ²/(d−2) − σ² − R` with `θ(0) = σ(0) = 0` (`θ` continuous), let the area change be
`δA(ε) = −∫₀^ε θ` and the heat flux `δQ(ε) = κ ∫₀^ε s T(s) ds`. If Clausius
`δQ = (ħκ/2π)(1/4Għ) δA` holds to `o(ε²)`, then `R(0) = 8πG T(0)`. -/
theorem clausius_from_raychaudhuri (θ σ R T : ℝ → ℝ) (d κ ħ G : ℝ)
    (hθc : Continuous θ) (hT : Continuous T)
    (hray : HasDerivAt θ (-(θ 0)^2/(d-2) - (σ 0)^2 - R 0) 0) (hθ0 : θ 0 = 0) (hσ0 : σ 0 = 0)
    (hκ : κ ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0)
    (hClausius : Tendsto (fun ε =>
        (κ * (∫ s in (0:ℝ)..ε, s * T s)
          - (ħ * κ / (2 * Real.pi)) * (1 / (4 * G * ħ)) * (-∫ s in (0:ℝ)..ε, θ s)) / ε^2)
        (𝓝[>] 0) (𝓝 0)) :
    R 0 = 8 * Real.pi * G * T 0 := by
  have hlin := raychaudhuri_linear θ σ R d hray hθ0 hσ0
  have hA := integral_second_order θ (-R 0) hθc hθ0 hlin
  have hQ := weighted_integral_limit T hT
  set c := (ħ * κ / (2 * Real.pi)) * (1 / (4 * G * ħ))
  have hsum : Tendsto (fun ε => κ * ((∫ s in (0:ℝ)..ε, s * T s) / ε^2)
      - c * (-((∫ s in (0:ℝ)..ε, θ s) / ε^2))) (𝓝[>] 0)
      (𝓝 (κ * (T 0 / 2) - c * (-(-R 0 / 2)))) :=
    (hQ.const_mul κ).sub (hA.neg.const_mul c)
  have heq : (fun ε => κ * ((∫ s in (0:ℝ)..ε, s * T s) / ε^2)
      - c * (-((∫ s in (0:ℝ)..ε, θ s) / ε^2))) = fun ε =>
      (κ * (∫ s in (0:ℝ)..ε, s * T s) - c * (-∫ s in (0:ℝ)..ε, θ s)) / ε^2 := by
    ext ε; ring
  rw [heq] at hsum
  have h0 := tendsto_nhds_unique hsum hClausius
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [c] at h0
  field_simp at h0
  have : κ * (8 * Real.pi * G * T 0 - R 0) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hκ
  · linarith

end EntEq
