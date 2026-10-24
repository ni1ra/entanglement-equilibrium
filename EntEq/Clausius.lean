/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The analytic steps of Jacobson's 1995 derivation along one null generator of a local Rindler
  horizon, and the full chain (Clausius → null-cone lemma → Bianchi) to the Einstein equation.

  Along the generator, `s ≥ 0` is the affine distance from the bifurcation point `p`,
  `T s = T_ab kᵃkᵇ` and `R s = R_ab kᵃkᵇ`. Jacobson's heat flux and area change are
      δQ(ε) = κ ∫₀^ε s T(s) ds,      δA(ε) = ∫₀^ε s R(s) ds,
  and Clausius with the Unruh temperature reads `δQ = (ħκ/2π) η δA`. It can only hold to the
  leading order `ε²`, so the hypothesis below is that the two sides agree up to `o(ε²)`.
-/
import EntEq.Bianchi
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Topology intervalIntegral Matrix

namespace EntEq

/-- `∫₀^ε s f(s) ds / ε² → f(0)/2` for continuous `f`. -/
theorem weighted_integral_limit (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun ε => (∫ s in (0:ℝ)..ε, s * f s) / ε^2) (𝓝[>] 0) (𝓝 (f 0 / 2)) := by
  have hc : Continuous fun s => s * f s := continuous_id.mul hf
  apply HasDerivAt.lhopital_zero_nhdsGT (f' := fun ε => ε * f ε) (g' := fun ε => 2 * ε)
  · exact Eventually.of_forall fun ε => (hc.integral_hasStrictDerivAt 0 ε).hasDerivAt
  · exact Eventually.of_forall fun ε => by simpa using hasDerivAt_pow 2 ε
  · exact eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => by positivity
  · have : Continuous fun ε => ∫ s in (0:ℝ)..ε, s * f s :=
      (hc.integral_hasStrictDerivAt 0 · |>.hasDerivAt.continuousAt) |> continuous_iff_continuousAt.mpr
    have h0 := this.tendsto 0
    simp only [integral_same] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  · have : Continuous fun ε : ℝ => ε^2 := continuous_pow 2
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  · have hlim : Tendsto (fun ε => f ε / 2) (𝓝[>] 0) (𝓝 (f 0 / 2)) :=
      ((hf.div_const 2).tendsto 0).mono_left nhdsWithin_le_nhds
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    field_simp

/-- **Leading order.** If `∫₀^ε s f(s) ds = o(ε²)` then `f(0) = 0`. -/
theorem leading_order_zero (f : ℝ → ℝ) (hf : Continuous f)
    (h : Tendsto (fun ε => (∫ s in (0:ℝ)..ε, s * f s) / ε^2) (𝓝[>] 0) (𝓝 0)) : f 0 = 0 := by
  have := tendsto_nhds_unique (weighted_integral_limit f hf) h
  linarith

/-- **Clausius on one generator ⇒ `R_kk = 8πG T_kk` at `p`.** With Unruh temperature
`ħκ/2π`, entropy density `η = 1/(4Għ)`, and `δQ = T δS` to leading order, the Ricci and
stress components agree at the bifurcation point. The surface gravity `κ` cancels. -/
theorem clausius_generator (T R : ℝ → ℝ) (hT : Continuous T) (hR : Continuous R)
    (κ ħ G : ℝ) (hκ : κ ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0)
    (hClausius : Tendsto (fun ε =>
        (κ * (∫ s in (0:ℝ)..ε, s * T s)
          - (ħ * κ / (2 * Real.pi)) * (1 / (4 * G * ħ)) * (∫ s in (0:ℝ)..ε, s * R s)) / ε^2)
        (𝓝[>] 0) (𝓝 0)) :
    R 0 = 8 * Real.pi * G * T 0 := by
  set c := (ħ * κ / (2 * Real.pi)) * (1 / (4 * G * ħ))
  have hf : Continuous fun s => κ * T s - c * R s := (hT.const_smul κ).sub (hR.const_smul c)
  have hint : ∀ ε, κ * (∫ s in (0:ℝ)..ε, s * T s) - c * (∫ s in (0:ℝ)..ε, s * R s)
      = ∫ s in (0:ℝ)..ε, s * (κ * T s - c * R s) := by
    intro ε
    have i1 : IntervalIntegrable (fun s => s * T s) MeasureTheory.volume 0 ε :=
      (continuous_id.mul hT).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun s => s * R s) MeasureTheory.volume 0 ε :=
      (continuous_id.mul hR).intervalIntegrable _ _
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (i1.const_mul κ) (i2.const_mul c)]
    congr 1; ext s; ring
  simp only [hint] at hClausius
  have h0 := leading_order_zero _ hf hClausius
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [c] at h0
  field_simp at h0
  have : κ * (8 * Real.pi * G * T 0 - R 0) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hκ
  · linarith

/-- **Raychaudhuri, linearised.** For a null congruence in `d > 2` dimensions,
`θ' = −θ²/(d−2) − σ² − R`. If the generator starts with `θ(0) = 0` and `σ(0) = 0`
(the local Rindler horizon is instantaneously stationary at `p`), then `θ = −s R(0) + o(s)`.
This is a direct substitution; its use is in `clausius_from_raychaudhuri`. -/
theorem raychaudhuri_linear (θ σ R : ℝ → ℝ) (d : ℝ)
    (hθ : HasDerivAt θ (-(θ 0)^2/(d-2) - (σ 0)^2 - R 0) 0) (hθ0 : θ 0 = 0) (hσ0 : σ 0 = 0) :
    HasDerivAt θ (-R 0) 0 := by
  simpa [hθ0, hσ0] using hθ

/-- **Focusing bound.** Let `θ` solve the full Raychaudhuri equation on the open interval
`(0, s₁)`, be continuous on `[0, s₁]`, with `d > 2` and `θ(0) = 0`. Then
`θ(s) ≤ −∫₀^s R` on `[0, s₁]`. Under the null energy condition (`R ≥ 0`) the congruence
focuses; the linear term `−∫R` is exact up to the non-positive `−θ²/(d−2) − σ²` corrections.
(Only a finite interval is assumed: with `R > 0` solutions reach a caustic in finite `s`.) -/
theorem raychaudhuri_focusing (θ σ R : ℝ → ℝ) (d s₁ : ℝ) (hd : 2 < d) (hR : Continuous R)
    (hθc : ContinuousOn θ (Set.Icc 0 s₁))
    (hθ : ∀ s ∈ Set.Ioo 0 s₁, HasDerivAt θ (-(θ s)^2/(d-2) - (σ s)^2 - R s) s)
    (hθ0 : θ 0 = 0) :
    ∀ s ∈ Set.Icc 0 s₁, θ s ≤ -∫ u in (0:ℝ)..s, R u := by
  set h := fun s => θ s + ∫ u in (0:ℝ)..s, R u
  have hI : Continuous fun s => ∫ u in (0:ℝ)..s, R u :=
    continuous_iff_continuousAt.mpr fun s => (hR.integral_hasStrictDerivAt 0 s).hasDerivAt.continuousAt
  have hder : ∀ s ∈ Set.Ioo 0 s₁, HasDerivAt h (-(θ s)^2/(d-2) - (σ s)^2) s := by
    intro s hs
    have := (hθ s hs).add (hR.integral_hasStrictDerivAt 0 s).hasDerivAt
    convert this using 1; ring
  have hanti : AntitoneOn h (Set.Icc 0 s₁) := by
    apply antitoneOn_of_deriv_nonpos (f := h) (convex_Icc 0 s₁) (hθc.add hI.continuousOn)
    · rw [interior_Icc]; exact fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hder s hs).deriv]
      have : 0 ≤ (θ s)^2/(d-2) := div_nonneg (sq_nonneg _) (by linarith)
      rw [neg_div]
      nlinarith [sq_nonneg (σ s)]
  intro s hs
  have := hanti ⟨le_refl 0, hs.1.trans hs.2⟩ hs hs.1
  simp only [h, hθ0, integral_same, add_zero] at this
  linarith

section Chain

variable {n : ℕ} {M : Type*}

lemma eta_det_ne_zero : (eta n).det ≠ 0 := by
  rw [eta, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by split_ifs <;> norm_num

/-- Trace of `g⁻¹ (c g)` is `c (n+1)` for an invertible `g`. -/
lemma trace_inv_smul (g : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hg : IsUnit g.det) (c : ℝ) :
    Matrix.trace (g⁻¹ * (c • g)) / (n + 1) = c := by
  rw [Matrix.mul_smul, Matrix.nonsing_inv_mul g hg, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  push_cast
  field_simp

/-- **The whole 1995 chain at the level of fields.** Points `x : M`; metric `g x = P xᵀ η P x`
(an orthonormal frame at each point). Tensor fields live in a module `V` and scalar fields in
`S` (for example smooth fields), read off pointwise by the linear maps `evV` (injective) and
`evS`. The hypotheses a real geometry supplies: `mulG φ` is the field `φ g`; the trace
`tr X = g⁻¹·X /(n+1)` of a field in `V` is a field in `S`; `div (φ g) = dφ` (metric
compatibility); `dφ = 0 ⇒ φ` constant (connectedness); `div Ric = ½ dR` (contracted Bianchi);
`div T = 0`.

**Assumed, not derived:** the null-direction relation `Ric(k,k) = κₑ T(k,k)` at every point
(`clausius_generator` and `clausius_from_raychaudhuri` derive it along one generator from
Clausius; promoting that to every point and null direction is the physical premise).
`Ric`, `R` and `div` are abstract: that they are the Ricci tensor, its trace and the
Levi-Civita divergence of `g` is the reading. Conclusion: `Ric − ½ R g + Λ g = κₑ T` with
`Λ` **constant**. `flat_clausius` instantiates every hypothesis on Minkowski space. -/
theorem jacobson_chain
    {V S W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup S] [Module ℝ S]
    [AddCommGroup W] [Module ℝ W]
    (P : M → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hP : ∀ x, IsUnit (P x).det)
    (evV : V →ₗ[ℝ] (M → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) (hevV : Function.Injective evV)
    (evS : S →ₗ[ℝ] (M → ℝ))
    (mulG : S →ₗ[ℝ] V) (hmulG : ∀ φ x, evV (mulG φ) x = evS φ x • ((P x)ᵀ * eta n * P x))
    (tr : V →ₗ[ℝ] S)
    (htr : ∀ X x, evS (tr X) x = Matrix.trace (((P x)ᵀ * eta n * P x)⁻¹ * evV X x) / (n + 1))
    (one : S) (div : V →ₗ[ℝ] W) (d : S →ₗ[ℝ] W)
    (hcompat : ∀ φ, div (mulG φ) = d φ) (hconn : ∀ φ, d φ = 0 → ∃ c : ℝ, φ = c • one)
    (Ric T : V) (Rs : S) (κₑ : ℝ)
    (hRic : ∀ x, (evV Ric x).IsSymm) (hT : ∀ x, (evV T x).IsSymm)
    (hClausius : ∀ x k, qf ((P x)ᵀ * eta n * P x) k = 0 →
      qf (evV Ric x) k = κₑ * qf (evV T x) k)
    (hBianchi : div Ric = (1/2 : ℝ) • d Rs) (hcons : div T = 0) :
    ∃ Λ : ℝ, Ric - (1/2 : ℝ) • mulG Rs + Λ • mulG one = κₑ • T := by
  -- pointwise: the null-cone lemma gives a scalar at each point
  have hpt : ∀ x, ∃ c : ℝ, evV (Ric - κₑ • T) x = c • ((P x)ᵀ * eta n * P x) := by
    intro x
    rw [map_sub, map_smul]
    apply null_cone_lemma_lorentzian (P x) _ (hP x) ((hRic x).sub ((hT x).smul κₑ))
    intro k hk
    have := hClausius x k hk
    simp only [Pi.sub_apply, Pi.smul_apply, qf, Matrix.sub_mulVec, dotProduct_sub,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at this ⊢
    linarith
  -- the scalar is the trace, which is a field in `S`
  have hgdet : ∀ x, IsUnit ((P x)ᵀ * eta n * P x).det := by
    intro x
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact ((hP x).mul (isUnit_iff_ne_zero.mpr eta_det_ne_zero)).mul (hP x)
  have hX : mulG (tr (Ric - κₑ • T)) = Ric - κₑ • T := by
    apply hevV
    funext x
    obtain ⟨c, hc⟩ := hpt x
    rw [hmulG, htr, hc, trace_inv_smul _ (hgdet x)]
  exact einstein_of_null_relation div d mulG one hcompat hconn Ric T Rs _ κₑ hBianchi hcons hX.symm

end Chain

end EntEq
