/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Why the trace term in Jacobson's first law is generic.

  Any carrier whose first variation is a linear functional of the stress tensor over a ball at
  rest, `δF = ∑ W_ab δT_ab`, has a weight `W` that is invariant under the ball's spatial
  symmetries. Invariance under the spatial reflections and the spatial coordinate swaps already
  forces `δF = W₀₀ δT₀₀ + W₁₁ ∑ᵢ δTᵢᵢ = (W₀₀ + W₁₁) δT(u,u) + W₁₁ δT^a_a`
  (`carrier_weight_trace_form`): a `u`-independent multiple of the trace, i.e. Jacobson's
  `δX ∝ δT^a_a`. So that structure is a symmetry fact about any such carrier, not a property
  of entanglement; only the coefficients are carrier-specific.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Matrix

namespace EntEq.Carrier

variable {m : ℕ}

/-- Reflection of the spatial coordinate `i` (index `0` is time). -/
def reflect (i : Fin (m+2)) : Matrix (Fin (m+2)) (Fin (m+2)) ℝ :=
  Matrix.diagonal fun a => if a = i then -1 else 1

/-- Off-diagonal entries of a reflection-invariant weight vanish. -/
lemma offdiag_zero (W : Matrix (Fin (m+2)) (Fin (m+2)) ℝ)
    (hR : ∀ j : Fin (m+1), reflect j.succ * W * reflect j.succ = W)
    (a b : Fin (m+2)) (hab : a ≠ b) : W a b = 0 := by
  -- one of `a`, `b` is spatial; reflect it
  have key : ∀ j : Fin (m+1), ∀ c : Fin (m+2), c ≠ j.succ →
      W j.succ c = 0 ∧ W c j.succ = 0 := by
    intro j c hc
    have h := congrArg (fun M => M j.succ c) (hR j)
    have h' := congrArg (fun M => M c j.succ) (hR j)
    simp only [reflect, diagonal_mul, mul_diagonal, if_neg hc, ↓reduceIte, mul_one, one_mul,
      neg_mul] at h h'
    constructor <;> linarith
  rcases Fin.eq_zero_or_eq_succ a with ha | ⟨j, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ b with hb | ⟨k, rfl⟩
    · exact absurd (ha.trans hb.symm) hab
    · exact (key k a (by rw [ha]; exact (Fin.succ_ne_zero k).symm)).2
  · exact (key j b (Ne.symm hab)).1

/-- **The trace form of any rotation-invariant linear carrier.** If the weight `W` of
`δF = ∑ W_ab T_ab` is invariant under every spatial reflection and every swap of two spatial
coordinates, then `δF = (W₀₀ + W₁₁) T₀₀ + W₁₁ (−T₀₀ + ∑ᵢ Tᵢᵢ)`: a multiple of `T(u,u)` plus a
`u`-independent multiple of the trace `T^a_a = −T₀₀ + ∑ᵢ Tᵢᵢ`. -/
theorem carrier_weight_trace_form (W T : Matrix (Fin (m+2)) (Fin (m+2)) ℝ)
    (hR : ∀ j : Fin (m+1), reflect j.succ * W * reflect j.succ = W)
    (hS : ∀ j k : Fin (m+1),
      W.submatrix (Equiv.swap j.succ k.succ) (Equiv.swap j.succ k.succ) = W) :
    ∑ a, ∑ b, W a b * T a b
      = (W 0 0 + W 1 1) * T 0 0 + W 1 1 * (-T 0 0 + ∑ j : Fin (m+1), T j.succ j.succ) := by
  have hdiag : ∀ a, ∑ b, W a b * T a b = W a a * T a a := by
    intro a
    rw [Finset.sum_eq_single a]
    · intro b _ hb; rw [offdiag_zero W hR a b (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hsame : ∀ j : Fin (m+1), W j.succ j.succ = W 1 1 := by
    intro j
    have h := congrArg (fun M => M j.succ j.succ) (hS j 0)
    simp only [submatrix_apply, Equiv.swap_apply_left] at h
    simpa using h.symm
  simp_rw [hdiag]
  rw [Fin.sum_univ_succ]
  simp_rw [hsame]
  rw [← Finset.mul_sum]
  ring

end EntEq.Carrier
