/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The two entanglement inputs of the 2016 argument, in their commuting (classical, finite)
  form: a reference state `q = e^{−K}/Z` (the vacuum restricted to a ball is thermal with
  respect to its modular Hamiltonian `K`, Bisognano–Wichmann / Casini–Huerta–Myers) and an
  arbitrary state `p` on the same finite set of outcomes.

  * `first_law`: `δS = δ⟨K⟩` to first order around `q` (the first law of entanglement).
  * `casini_bekenstein`: `ΔS ≤ Δ⟨K⟩` for every `p` (positivity of relative entropy; with
    `K = 2π H_boost / ħ` this is Casini's form of the Bekenstein bound).

  The quantum (non-commuting density-matrix) versions are not formalized here.
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

open Real Finset

namespace EntEq.Ent

variable {ι : Type*} [Fintype ι]

/-- Shannon (von Neumann, when commuting) entropy. -/
noncomputable def S (p : ι → ℝ) : ℝ := ∑ i, negMulLog (p i)

/-- Expectation of `K`. -/
def avg (K p : ι → ℝ) : ℝ := ∑ i, p i * K i

/-- Partition function and the thermal reference state. -/
noncomputable def Z (K : ι → ℝ) : ℝ := ∑ i, exp (-K i)
noncomputable def gibbs (K : ι → ℝ) (i : ι) : ℝ := exp (-K i) / Z K

lemma Z_pos [Nonempty ι] (K : ι → ℝ) : 0 < Z K :=
  Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty

lemma gibbs_pos [Nonempty ι] (K : ι → ℝ) (i : ι) : 0 < gibbs K i :=
  div_pos (exp_pos _) (Z_pos K)

lemma gibbs_sum [Nonempty ι] (K : ι → ℝ) : ∑ i, gibbs K i = 1 := by
  simp only [gibbs, ← Finset.sum_div]; exact div_self (Z_pos K).ne'

lemma log_gibbs [Nonempty ι] (K : ι → ℝ) (i : ι) : log (gibbs K i) = -K i - log (Z K) := by
  rw [gibbs, log_div (exp_pos _).ne' (Z_pos K).ne', log_exp]

/-- Termwise Gibbs inequality `p log p − p log q ≥ p − q` for `p ≥ 0`, `q > 0`. -/
lemma gibbs_term (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) : p - q ≤ p * log p - p * log q := by
  rcases hp.eq_or_lt with rfl | hp'
  · simp; linarith
  · have h := self_sub_one_le_mul_log (div_nonneg hp hq.le)
    rw [log_div hp'.ne' hq.ne'] at h
    have := mul_le_mul_of_nonneg_left h hq.le
    have e1 : q * (p / q - 1) = p - q := by field_simp
    have e2 : q * (p / q * (log p - log q)) = p * log p - p * log q := by field_simp
    linarith

/-- The thermal state's entropy: `S(q) = ⟨K⟩_q + log Z`. -/
lemma S_gibbs [Nonempty ι] (K : ι → ℝ) : S (gibbs K) = avg K (gibbs K) + log (Z K) := by
  simp only [S, negMulLog, avg, log_gibbs]
  have := gibbs_sum K
  calc ∑ i, -gibbs K i * (-K i - log (Z K))
      = ∑ i, gibbs K i * K i + (∑ i, gibbs K i) * log (Z K) := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]; congr 1; ext i; ring
    _ = _ := by rw [this, one_mul]

/-- **Casini–Bekenstein (commuting form).** For every probability vector `p`,
`S(p) − S(q) ≤ ⟨K⟩_p − ⟨K⟩_q`. -/
theorem casini_bekenstein [Nonempty ι] (K p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    S p - S (gibbs K) ≤ avg K p - avg K (gibbs K) := by
  have hterm : ∀ i, p i - gibbs K i ≤ p i * log (p i) - p i * log (gibbs K i) :=
    fun i => gibbs_term _ _ (hp i) (gibbs_pos K i)
  have hsumineq := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum, gibbs_sum, sub_self] at hsumineq
  have hcross : ∑ i, p i * log (gibbs K i) = -avg K p - log (Z K) := by
    simp only [log_gibbs, avg]
    rw [show (∑ i, p i * (-K i - log (Z K))) = -(∑ i, p i * K i) - (∑ i, p i) * log (Z K) by
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]; congr 1; ext i; ring]
    rw [hsum, one_mul]
  have hS : S p = -∑ i, p i * log (p i) := by
    simp only [S, negMulLog, ← Finset.sum_neg_distrib]; congr 1; ext i; ring
  rw [hS, S_gibbs]
  linarith

/-- **First law of entanglement (commuting form).** Along `p(t) = q + t v` with `∑ v = 0`,
`d S/dt = d⟨K⟩/dt = ∑ vᵢ Kᵢ` at `t = 0`. -/
theorem first_law [Nonempty ι] (K v : ι → ℝ) (hv : ∑ i, v i = 0) :
    HasDerivAt (fun t => S (fun i => gibbs K i + t * v i)) (∑ i, v i * K i) 0 ∧
    HasDerivAt (fun t => avg K (fun i => gibbs K i + t * v i)) (∑ i, v i * K i) 0 := by
  constructor
  · have h : ∀ i, HasDerivAt (fun t => negMulLog (gibbs K i + t * v i))
        ((-log (gibbs K i) - 1) * v i) 0 := by
      intro i
      have hlin : HasDerivAt (fun t : ℝ => gibbs K i + t * v i) (v i) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (gibbs K i)
      have hg : HasDerivAt negMulLog (-log (gibbs K i) - 1) (gibbs K i + 0 * v i) := by
        simpa using hasDerivAt_negMulLog (gibbs_pos K i).ne'
      exact hg.comp (0:ℝ) hlin
    have hS := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)
    convert hS using 1
    · ext t; simp [S]
    · simp only [log_gibbs]
      rw [show (∑ i, (-(-K i - log (Z K)) - 1) * v i)
          = ∑ i, v i * K i + (log (Z K) - 1) * ∑ i, v i by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; ext i; ring]
      rw [hv, mul_zero, add_zero]
  · have h : ∀ i, HasDerivAt (fun t => (gibbs K i + t * v i) * K i) (v i * K i) 0 := by
      intro i
      have hlin : HasDerivAt (fun t : ℝ => gibbs K i + t * v i) (v i) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (gibbs K i)
      exact hlin.mul_const (K i)
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)
    convert this using 1
    ext t; simp [avg]

end EntEq.Ent
