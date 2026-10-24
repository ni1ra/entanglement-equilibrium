/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The null-cone lemma behind Jacobson's derivation of the Einstein equation.

  Minkowski space of dimension `n + 1` is modelled as `Fin (n+1) → ℝ` with index `0` the time
  direction and `η = diag(-1, 1, …, 1)`. A symmetric 2-tensor at a point is a symmetric matrix.
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

open Matrix

namespace EntEq

variable {n : ℕ}

/-- The Minkowski metric `diag(-1, 1, …, 1)` in `n + 1` dimensions. -/
def eta (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.diagonal fun i => if i = 0 then -1 else 1

/-- The quadratic form `M(k, k) = kᵃ M_ab kᵇ`. -/
def qf (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (k : Fin (n+1) → ℝ) : ℝ := k ⬝ᵥ (M *ᵥ k)

/-- Unit coordinate vector. -/
abbrev e (i : Fin (n+1)) : Fin (n+1) → ℝ := Pi.single i 1

lemma qf_three (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i j l : Fin (n+1)) (a b c : ℝ) :
    qf M (a • e i + b • e j + c • e l) =
      a*a*M i i + a*b*M i j + a*c*M i l + b*a*M j i + b*b*M j j + b*c*M j l
        + c*a*M l i + c*b*M l j + c*c*M l l := by
  simp [qf, Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul]
  ring

lemma eta_apply (i j : Fin (n+1)) :
    eta n i j = if i = j then (if i = 0 then -1 else 1) else 0 := by
  simp [eta, Matrix.diagonal_apply]

lemma qf_smul (c : ℝ) (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (k : Fin (n+1) → ℝ) :
    qf (c • M) k = c * qf M k := by
  simp [qf, Matrix.smul_mulVec, dotProduct_smul]

/-- **Null-cone lemma.** A symmetric bilinear form that vanishes on every null vector of
Minkowski space is a multiple of the metric. Holds in every dimension `n + 1 ≥ 1`. -/
theorem null_cone_lemma (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hX : X.IsSymm)
    (hnull : ∀ k, qf (eta n) k = 0 → qf X k = 0) : ∃ c : ℝ, X = c • eta n := by
  have hs : ∀ i j, X j i = X i j := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hX i) j
  -- Step 1: `e₀ ± eᵢ` is null, so `X₀ᵢ = 0` and `Xᵢᵢ = -X₀₀`.
  have step1 : ∀ i : Fin (n+1), i ≠ 0 → X 0 i = 0 ∧ X i i = -X 0 0 := by
    intro i hi
    have hp := hnull ((1:ℝ) • e 0 + (1:ℝ) • e i + (0:ℝ) • e i) (by
      rw [qf_three]; simp [eta_apply, hi, Ne.symm hi])
    have hm := hnull ((1:ℝ) • e 0 + (-1:ℝ) • e i + (0:ℝ) • e i) (by
      rw [qf_three]; simp [eta_apply, hi, Ne.symm hi])
    rw [qf_three] at hp hm
    have := hs 0 i
    constructor <;> linarith
  -- Step 2: `5e₀ + 3eᵢ + 4eⱼ` is null (a rational point on the light cone), so `Xᵢⱼ = 0`.
  have step2 : ∀ i j : Fin (n+1), i ≠ 0 → j ≠ 0 → i ≠ j → X i j = 0 := by
    intro i j hi hj hij
    have h := hnull ((5:ℝ) • e 0 + (3:ℝ) • e i + (4:ℝ) • e j) (by
      rw [qf_three]; simp [eta_apply, hi, hj, hij, Ne.symm hi, Ne.symm hj, Ne.symm hij]; norm_num)
    rw [qf_three] at h
    have := hs 0 i; have := hs 0 j; have := hs i j
    have := step1 i hi; have := step1 j hj
    linarith
  refine ⟨-X 0 0, ?_⟩
  ext a b
  simp only [Matrix.smul_apply, eta_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = 0
    · subst ha; simp
    · simp [ha, (step1 a ha).2]
  · simp only [hab, ite_false, mul_zero]
    by_cases ha : a = 0
    · subst ha; exact (step1 b (Ne.symm hab)).1
    · by_cases hb : b = 0
      · subst hb; rw [hs]; exact (step1 a ha).1
      · exact step2 a b ha hb hab

/-- The converse: every multiple of the metric vanishes on null vectors. -/
theorem null_cone_iff (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hX : X.IsSymm) :
    (∀ k, qf (eta n) k = 0 → qf X k = 0) ↔ ∃ c : ℝ, X = c • eta n := by
  refine ⟨null_cone_lemma X hX, ?_⟩
  rintro ⟨c, rfl⟩ k hk
  rw [qf_smul, hk, mul_zero]

/-- `qf (Aᵀ M A) v = qf M (A v)`: a change of frame. -/
lemma qf_congr (M A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (v : Fin (n+1) → ℝ) :
    qf (Aᵀ * M * A) v = qf M (A *ᵥ v) := by
  simp only [qf, ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **Null-cone lemma for any Lorentzian metric.** If `g = Pᵀ η P` with `P` invertible (an
orthonormal frame exists at the point), a symmetric form vanishing on every `g`-null vector is
`c • g`. This is the form used pointwise on a curved spacetime. -/
theorem null_cone_lemma_lorentzian (P X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hP : IsUnit P.det)
    (hX : X.IsSymm) (hnull : ∀ k, qf (Pᵀ * eta n * P) k = 0 → qf X k = 0) :
    ∃ c : ℝ, X = c • (Pᵀ * eta n * P) := by
  set Q := P⁻¹
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hP
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hP
  have hY : (Qᵀ * X * Q).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose, hX.eq,
      Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := null_cone_lemma (Qᵀ * X * Q) hY (by
    intro k hk
    rw [qf_congr]
    apply hnull
    rw [qf_congr, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    exact hk)
  refine ⟨c, ?_⟩
  have : X = Pᵀ * (Qᵀ * X * Q) * P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hQP,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one]
  rw [this, hc, Matrix.mul_smul, Matrix.smul_mul]

/-- **Timelike-unit lemma** (the 2016 "entanglement equilibrium" version). A symmetric form
that vanishes on every unit timelike vector (`η(u,u) = -1`) is zero. -/
theorem unit_timelike_lemma (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hX : X.IsSymm)
    (hu : ∀ u, qf (eta n) u = -1 → qf X u = 0) : X = 0 := by
  have hs : ∀ i j, X j i = X i j := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hX i) j
  have h00 : X 0 0 = 0 := by
    have h := hu ((1:ℝ) • e 0 + (0:ℝ) • e 0 + (0:ℝ) • e 0) (by rw [qf_three]; simp [eta_apply])
    rw [qf_three] at h; linarith
  -- `(5/4)e₀ ± (3/4)eᵢ` are unit timelike.
  have step1 : ∀ i : Fin (n+1), i ≠ 0 → X 0 i = 0 ∧ X i i = 0 := by
    intro i hi
    have hp := hu ((5/4:ℝ) • e 0 + (3/4:ℝ) • e i + (0:ℝ) • e i) (by
      rw [qf_three]; simp [eta_apply, hi, Ne.symm hi]; norm_num)
    have hm := hu ((5/4:ℝ) • e 0 + (-3/4:ℝ) • e i + (0:ℝ) • e i) (by
      rw [qf_three]; simp [eta_apply, hi, Ne.symm hi]; norm_num)
    rw [qf_three, h00] at hp hm
    have := hs 0 i
    constructor <;> linarith
  -- `3e₀ + 2eᵢ + 2eⱼ` is unit timelike.
  have step2 : ∀ i j : Fin (n+1), i ≠ 0 → j ≠ 0 → i ≠ j → X i j = 0 := by
    intro i j hi hj hij
    have h := hu ((3:ℝ) • e 0 + (2:ℝ) • e i + (2:ℝ) • e j) (by
      rw [qf_three]; simp [eta_apply, hi, hj, hij, Ne.symm hi, Ne.symm hj, Ne.symm hij]; norm_num)
    rw [qf_three] at h
    have := hs 0 i; have := hs 0 j; have := hs i j
    have := step1 i hi; have := step1 j hj
    linarith
  ext a b
  simp only [Matrix.zero_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = 0
    · subst ha; exact h00
    · exact (step1 a ha).2
  · by_cases ha : a = 0
    · subst ha; exact (step1 b (Ne.symm hab)).1
    · by_cases hb : b = 0
      · subst hb; rw [hs]; exact (step1 a ha).1
      · exact step2 a b ha hb hab

/-- If `X(u,u)` takes one value `Λ` on every unit timelike vector, then `X = -Λ η`: in the
2016 argument the cosmological term is fixed pointwise by the constrained variation. -/
theorem unit_timelike_const (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hX : X.IsSymm) (Λ : ℝ)
    (hu : ∀ u, qf (eta n) u = -1 → qf X u = Λ) : X = -Λ • eta n := by
  have hsum : (X + Λ • eta n).IsSymm := by
    have he : (eta n).IsSymm := Matrix.isSymm_diagonal _
    exact hX.add (he.smul Λ)
  have h0 := unit_timelike_lemma (X + Λ • eta n) hsum (by
    intro u hu1
    simp only [qf, Matrix.add_mulVec, dotProduct_add] at *
    have := qf_smul Λ (eta n) u
    simp only [qf] at this
    rw [hu u hu1, this, hu1]; ring)
  rw [neg_smul, eq_neg_iff_add_eq_zero, h0]

end EntEq
