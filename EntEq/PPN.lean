/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The AeST preferred-frame pincer, *conditional* on one unverified physics hypothesis.

  Foster & Jacobson (gr-qc/0509083, eqs. 10–11) give Einstein-aether's preferred-frame PPN
  parameters. Reading AeST's vector term `−(K_B/2) F²` as Einstein-aether with
  `c₁ = K_B, c₂ = 0, c₃ = −K_B, c₄ = 0` gives `α₁ = −4 K_B`. Two physics hypotheses are not
  checked here: (H0) the sign/normalisation match between AeST's action and Foster–Jacobson's
  (supporting evidence: AeST's window `0 < K_B < 2` coincides with Einstein-aether's
  `c₁₄ < 2` for `c₁₄ = K_B`), and (H1) AeST's scalar sector does not change α₁. The bound on
  the exponent also inherits the limits of the closed-form exponent (`c_ad² → 0`, matter era,
  `H ≫ Q`).
  Status (linear-order computations carried out outside Lean): they find `α₁ = α₂ = 0` on
  AeST's stealth branch (`ω ≠ 0`, linear order), where H1 fails, and `α₁ = −4(K_Bλ_s + 2)/(λ_s + 1)` on the
  static branch, which tends to `−4K_B` for large `λ_s`. Which branch applies is open.
-/
import EntEq.AeST

open Real

namespace EntEq.PPN

/-- Foster–Jacobson α₁ (eq. 10). -/
noncomputable def alpha1 (c₁ c₃ c₄ : ℝ) : ℝ := -8 * (c₃^2 + c₁ * c₄) / (2*c₁ - c₁^2 + c₃^2)

/-- `F²`-type aether: `α₁ = −4 K_B`. -/
theorem alpha1_maxwell (K : ℝ) (hK : K ≠ 0) : alpha1 K (-K) 0 = -4 * K := by
  unfold alpha1; field_simp; ring

/-- In the same reading `c₁₂₃ = c₁ + c₂ + c₃ = 0`, the denominator of the first term of
Foster–Jacobson's α₂ (eq. 11): the pure Einstein-aether α₂ formula is singular for AeST, so
AeST's α₂ cannot be borrowed from Einstein-aether; its scalar sector must enter. -/
theorem c123_vanishes (K : ℝ) : K + 0 + (-K) = 0 := by ring

/-- **Conditional pincer.** Under H1, a bound `|α₁| ≤ B` forces `K_B ≤ B/4`, and then the closed-form
exponent satisfies `n ≥ ¼ + ¾ √(1/9 + 64 f_c/(3B))`. -/
theorem pincer (K f B : ℝ) (hK : 0 < K) (hf : 0 < f) (hB : 0 < B)
    (hα : |alpha1 K (-K) 0| ≤ B) :
    K ≤ B / 4 ∧ 1/4 + 3/4 * √(1/9 + 64 * f / (3 * B)) ≤ AeST.nExp K f := by
  rw [alpha1_maxwell K hK.ne', abs_of_neg (by linarith)] at hα
  have hKB : K ≤ B / 4 := by linarith
  refine ⟨hKB, ?_⟩
  unfold AeST.nExp
  have : 64 * f / (3 * B) ≤ 16 * f / (3 * K) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have := Real.sqrt_le_sqrt (by linarith : 1/9 + 64 * f / (3 * B) ≤ 1/9 + 16 * f / (3 * K))
  linarith

/-- With the `|α₁| ≲ 10⁻⁴` bound quoted by Foster–Jacobson and the matter-era `f_c = 0.78`,
H1 would force `K_B ≤ 2.5 × 10⁻⁵` and an overgrowth exponent `n > 300`. -/
theorem pincer_numeric (K : ℝ) (hK : 0 < K) (hα : |alpha1 K (-K) 0| ≤ 1e-4) :
    K ≤ 2.5e-5 ∧ 300 < AeST.nExp K 0.78 := by
  obtain ⟨h1, h2⟩ := pincer K 0.78 1e-4 hK (by norm_num) (by norm_num) hα
  refine ⟨by linarith, lt_of_lt_of_le ?_ h2⟩
  have : (400:ℝ) < √(1/9 + 64 * 0.78 / (3 * 1e-4)) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

end EntEq.PPN
