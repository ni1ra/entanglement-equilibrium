/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  A quantitative null-cone lemma: if Clausius holds only approximately on every null
  direction, the Einstein equation holds approximately, componentwise in an orthonormal frame,
  with a dimension-independent constant. (A first version proved the constant 85/12 from the
  9-ray certificate; an LP study showed 2 is the truth for `c = −X₀₀`, proved here.)
-/
import EntEq.NullCone
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Matrix

namespace EntEq

variable {n : ℕ}

lemma dot_three (i j l : Fin (n+1)) (a b c : ℝ) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (a • e i + b • e j + c • e l) ⬝ᵥ (a • e i + b • e j + c • e l) = a*a + b*b + c*c := by
  simp [dotProduct_add, dotProduct_smul,
    hij, hil, hjl, Ne.symm hij, Ne.symm hil, Ne.symm hjl]

lemma dot_two (i j : Fin (n+1)) (a b : ℝ) (hij : i ≠ j) :
    (a • e i + b • e j + (0:ℝ) • e j) ⬝ᵥ (a • e i + b • e j + (0:ℝ) • e j) = a*a + b*b := by
  simp [dotProduct_add, dotProduct_smul,
    hij, Ne.symm hij]

/-- **Stable null-cone lemma.** If a symmetric `X` satisfies `|X(k,k)| ≤ ε |k|²` (Euclidean
norm in an orthonormal frame) for every null `k`, then `c = −X₀₀` puts every
component of `X − c η` within `2ε`. The rays `√2 e₀ ± eᵢ ± eⱼ` isolate the spatial
off-diagonal entries. For this choice of `c` the constant 2 cannot be lowered
(`null_cone_stable_attained`); a better-chosen `c` can do better on some `X`. The constant does
not depend on the dimension. -/
theorem null_cone_stable_sharp (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hX : X.IsSymm) (ε : ℝ)
    (hε : 0 ≤ ε) (hnull : ∀ k, qf (eta n) k = 0 → |qf X k| ≤ ε * (k ⬝ᵥ k)) :
    ∀ i j, |X i j - (-X 0 0) * eta n i j| ≤ 2 * ε := by
  have hs : ∀ i j, X j i = X i j := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hX i) j
  have step1 : ∀ i : Fin (n+1), i ≠ 0 → |X 0 i| ≤ ε ∧ |X i i + X 0 0| ≤ 2 * ε := by
    intro i hi
    have hp := hnull ((1:ℝ) • e 0 + (1:ℝ) • e i + (0:ℝ) • e i) (by
      rw [qf_three]; simp [eta_apply, hi, Ne.symm hi])
    have hm := hnull ((1:ℝ) • e 0 + (-1:ℝ) • e i + (0:ℝ) • e i) (by
      rw [qf_three]; simp [eta_apply, hi, Ne.symm hi])
    rw [qf_three, dot_two _ _ _ _ (Ne.symm hi)] at hp hm
    have := hs 0 i
    rw [abs_le] at hp hm
    constructor <;> rw [abs_le] <;> constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]
  have r2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have step2 : ∀ i j : Fin (n+1), i ≠ 0 → j ≠ 0 → i ≠ j → |X i j| ≤ 2 * ε := by
    intro i j hi hj hij
    have nul : ∀ a b : ℝ, a * a = 1 → b * b = 1 →
        qf (eta n) (Real.sqrt 2 • e 0 + a • e i + b • e j) = 0 := by
      intro a b ha hb
      rw [qf_three]; simp [eta_apply, hi, hj, hij, Ne.symm hi, Ne.symm hj, Ne.symm hij]
      nlinarith [r2, ha, hb]
    have nrm : ∀ a b : ℝ, a * a = 1 → b * b = 1 →
        (Real.sqrt 2 • e 0 + a • e i + b • e j) ⬝ᵥ (Real.sqrt 2 • e 0 + a • e i + b • e j) = 4 := by
      intro a b ha hb
      rw [dot_three _ _ _ _ _ _ (Ne.symm hi) (Ne.symm hj) hij]; nlinarith [r2, ha, hb]
    have q1 := hnull _ (nul 1 1 (by norm_num) (by norm_num))
    have q2 := hnull _ (nul (-1) (-1) (by norm_num) (by norm_num))
    have q3 := hnull _ (nul 1 (-1) (by norm_num) (by norm_num))
    have q4 := hnull _ (nul (-1) 1 (by norm_num) (by norm_num))
    rw [nrm 1 1 (by norm_num) (by norm_num)] at q1
    rw [nrm (-1) (-1) (by norm_num) (by norm_num)] at q2
    rw [nrm 1 (-1) (by norm_num) (by norm_num)] at q3
    rw [nrm (-1) 1 (by norm_num) (by norm_num)] at q4
    rw [qf_three] at q1 q2 q3 q4
    rw [abs_le] at q1 q2 q3 q4 ⊢
    have := hs 0 i; have := hs 0 j; have := hs i j
    constructor <;> nlinarith [q1.1, q1.2, q2.1, q2.2, q3.1, q3.2, q4.1, q4.2]
  intro a b
  rw [eta_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = 0
    · subst ha; simp; positivity
    · simp only [ha, if_true, if_false]
      have := (step1 a ha).2
      rw [show X a a - -X 0 0 * 1 = X a a + X 0 0 by ring]; exact this
  · simp only [hab, if_false, mul_zero, sub_zero]
    by_cases ha : a = 0
    · subst ha; linarith [(step1 b (Ne.symm hab)).1]
    · by_cases hb : b = 0
      · subst hb; rw [hs]; linarith [(step1 a ha).1]
      · exact step2 a b ha hb hab

/-- The constant `2` cannot be lowered for `c = −X₀₀`: in 1+1 dimensions `X = 2ε e₁e₁ᵀ`
satisfies the hypothesis and has `X₁₁ − c η₁₁ = 2ε` (the choice `c = ε` would give `ε`). -/
theorem null_cone_stable_attained (ε : ℝ) (hε : 0 ≤ ε) :
    let X : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 2 * ε]
    (∀ k, qf (eta 1) k = 0 → |qf X k| ≤ ε * (k ⬝ᵥ k)) ∧ X 1 1 - (-X 0 0) * eta 1 1 1 = 2 * ε := by
  intro X
  constructor
  · intro k hk
    simp only [qf, eta, X, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at hk ⊢
    simp at hk ⊢
    have h1 : k 1 * k 1 = k 0 * k 0 := by linarith
    rw [abs_of_nonneg hε]
    have h2 := abs_mul_abs_self (k 1)
    nlinarith [sq_nonneg (k 0), sq_nonneg (k 1)]
  · simp [X, eta]

end EntEq
