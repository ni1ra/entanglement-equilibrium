/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Why the free scalar in the null-cone lemma is a constant (Λ), and how the Einstein tensor
  appears. Two layers:

  * `einstein_of_null_relation` — the curved-spacetime algebra. Differential geometry enters
    only through stated hypotheses: a linear divergence on symmetric 2-tensor fields, metric
    compatibility `div (φ g) = dφ`, the contracted Bianchi identity `div Ric = ½ dR`, matter
    conservation `div T = 0`, and connectedness (`dφ = 0 → φ` constant).
  * `flat_scalar_const` — a fully concrete instance on Minkowski space `ℝ^(n+1)`, where the
    divergence is built from Mathlib's Fréchet derivative and nothing is assumed.
-/
import EntEq.NullCone
import Mathlib.Analysis.Calculus.MeanValue

open Matrix

namespace EntEq

section Abstract

variable {S V W : Type*} [AddCommGroup S] [Module ℝ S] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- **Jacobson's integration step, abstractly.** Scalars `S`, symmetric 2-tensor fields `V`,
covector fields `W`. `mulG φ` is the tensor field `φ g`, `one` the constant function `1`.
`Ric`, `R` and `div` are abstract: that they are the Ricci tensor, its trace and the
Levi-Civita divergence of `g` is the reading, not a hypothesis Lean sees.
If the null-cone lemma has produced `Ric − κ T = Φ g`, then
`Ric − ½ R g + Λ g = κ T` with `Λ` a *constant*. -/
theorem einstein_of_null_relation
    (div : V →ₗ[ℝ] W) (d : S →ₗ[ℝ] W) (mulG : S →ₗ[ℝ] V) (one : S)
    (hcompat : ∀ φ, div (mulG φ) = d φ)                -- ∇g = 0
    (hconn : ∀ φ, d φ = 0 → ∃ c : ℝ, φ = c • one)      -- connected spacetime
    (Ric T : V) (R Φ : S) (κ : ℝ)
    (hBianchi : div Ric = (1/2 : ℝ) • d R)             -- contracted Bianchi identity
    (hcons : div T = 0)                                 -- ∇ᵃ T_ab = 0
    (hnull : Ric - κ • T = mulG Φ) :                    -- output of the null-cone lemma
    ∃ Λ : ℝ, Ric - (1/2 : ℝ) • mulG R + Λ • mulG one = κ • T := by
  have hd : d (Φ - (1/2 : ℝ) • R) = 0 := by
    have h := congrArg div hnull
    rw [map_sub, map_smul, hcons, smul_zero, sub_zero, hBianchi, hcompat] at h
    rw [map_sub, map_smul, ← h, sub_self]
  obtain ⟨c, hc⟩ := hconn _ hd
  refine ⟨-c, ?_⟩
  have hΦ : Φ = (1/2 : ℝ) • R + c • one := by rw [← hc]; abel
  have : Ric = κ • T + mulG Φ := by rw [← hnull]; abel
  rw [this, hΦ, map_add, map_smul, map_smul, neg_smul]
  abel

/-- The same step with `Λ` already fixed: if `div` of `Φ g` vanishes, `Φ` is constant. -/
theorem scalar_const_of_div_free
    (div : V →ₗ[ℝ] W) (d : S →ₗ[ℝ] W) (mulG : S →ₗ[ℝ] V) (one : S)
    (hcompat : ∀ φ, div (mulG φ) = d φ) (hconn : ∀ φ, d φ = 0 → ∃ c : ℝ, φ = c • one)
    (Φ : S) (h : div (mulG Φ) = 0) : ∃ c : ℝ, Φ = c • one :=
  hconn Φ (by rw [← hcompat]; exact h)

end Abstract

section Flat

variable {n : ℕ}

/-- Coordinate divergence `(∂ᵃ X)_b = Σ_a η^{aa} ∂_a X_ab` on Minkowski space. -/
noncomputable def divFlat (X : (Fin (n+1) → ℝ) → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (x : Fin (n+1) → ℝ) (b : Fin (n+1)) : ℝ :=
  ∑ a, eta n a a * fderiv ℝ (fun y => X y a b) x (e a)

lemma eta_sq (a : Fin (n+1)) : eta n a a * eta n a a = 1 := by
  simp only [eta_apply, ite_true]; split_ifs <;> norm_num

/-- `∂ᵃ(Φ η_ab) = ∂_b Φ`. -/
lemma divFlat_scalar (Φ : (Fin (n+1) → ℝ) → ℝ) (hΦ : Differentiable ℝ Φ) (x) (b) :
    divFlat (fun y => Φ y • eta n) x b = fderiv ℝ Φ x (e b) := by
  unfold divFlat
  have hcoef : ∀ a, fderiv ℝ (fun y => (Φ y • eta n) a b) x = eta n a b • fderiv ℝ Φ x := by
    intro a
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show (fun y => Φ y * eta n a b) = fun y => eta n a b * Φ y from funext fun _ => mul_comm _ _]
    rw [fderiv_const_mul (hΦ x)]
  simp only [hcoef, _root_.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · rw [← mul_assoc, eta_sq, one_mul]
  · intro a _ hab; simp [eta_apply, hab]
  · simp

/-- A linear functional on `ℝ^(n+1)` vanishing on every basis vector is zero. -/
lemma clm_eq_zero_of_basis (L : (Fin (n+1) → ℝ) →L[ℝ] ℝ) (h : ∀ b, L (e b) = 0) : L = 0 := by
  ext v
  have hv : v = ∑ i, v i • e i := by ext j; simp [Pi.single_apply]
  rw [hv, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_smul, h i, smul_zero]

/-- **Flat-space theorem, fully concrete.** On Minkowski space, if a differentiable scalar
`Φ` makes `Φ η` divergence-free, then `Φ` is constant. (Applied to `Φ η = 8πG T − G`, whose
divergence vanishes when `T` and `G` are each divergence-free, this is the flat-space form of
"the null-cone scalar is a constant `Λ`"; `flat_clausius` carries it out.) -/
theorem flat_scalar_const (Φ : (Fin (n+1) → ℝ) → ℝ) (hΦ : Differentiable ℝ Φ)
    (hdiv : ∀ x b, divFlat (fun y => Φ y • eta n) x b = 0) : ∀ x y, Φ x = Φ y := by
  apply is_const_of_fderiv_eq_zero hΦ
  intro x
  apply clm_eq_zero_of_basis
  intro b
  rw [← divFlat_scalar Φ hΦ x b]
  exact hdiv x b

end Flat

end EntEq
