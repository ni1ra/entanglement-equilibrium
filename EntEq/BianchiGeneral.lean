/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
import EntEq.CurvedCoords

/-
  The contracted Bianchi identity for a general metric in coordinates on `ℝ^(n+1)`, using the
  definitions of `CurvedCoords` (`chr`, `riem`, `ricci`, `scal`, `covDiv`).

  * `contracted_alg`: the contraction of the second Bianchi identity to `∇^a R_ab = ½ ∂_b R`,
    as pure index algebra from the symmetries it needs.
  * `Fm_antisymm`: `R^{ab}_cd` is antisymmetric in `a, b` (from metric compatibility and
    `∂_c∂_d g = ∂_d∂_c g`); `bianchi2`: the second Bianchi identity, from the gauge form
    `Σ_cyc (∂_e F_cd + [Γ_e, F_cd]) = 0` of the curvature `F_cd = ∂_cΓ_d − ∂_dΓ_c + [Γ_c, Γ_d]`.
  * `bianchi_general`: `∇^a R_ab = ½ ∂_b R` for every symmetric, everywhere-invertible `g` with
    smooth components; `ricci_symm`: `R_ab = R_ba` for the same class.
  * `curved_clausius_general`: `jacobson_chain` instantiated for every metric `g = Pᵀ η P` with
    `P` smooth and everywhere invertible.

  Everything is global on `ℝ^(n+1)` (no open sets or charts).
-/

open Matrix

namespace EntEq.Curved

variable {n : ℕ}

local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

/-! ### The contraction step, as pure index algebra -/

theorem contracted_alg (G : Fin (n+1) → Fin (n+1) → ℝ) (Γ : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (R : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (dR : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (dG : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (Ric : Fin (n+1) → Fin (n+1) → ℝ) (dRic : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hRic : ∀ b e, Ric b e = ∑ a, R a b a e) (hdRic : ∀ b e k, dRic b e k = ∑ a, dR a b a e k)
    (hG : ∀ a b, G a b = G b a) (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (hR : ∀ a b c d, R a b c d = -R a b d c) (hdR : ∀ a b c d e, dR a b c d e = -dR a b d c e)
    (hdG : ∀ a b e, dG a b e = -∑ f, (Γ a e f * G f b + Γ b e f * G a f))
    (hAS : ∀ a b c d, ∑ f, R a f c d * G f b = -∑ f, R b f c d * G f a)
    (hdAS : ∀ a b c d e, ∑ f, (dR a f c d e * G f b + R a f c d * dG f b e)
      = -∑ f, (dR b f c d e * G f a + R b f c d * dG f a e))
    (hB : ∀ a b c d e, dR a b c d e + dR a b d e c + dR a b e c d
      + ∑ f, (Γ a e f * R f b c d - R a f c d * Γ f e b)
      + ∑ f, (Γ a c f * R f b d e - R a f d e * Γ f c b)
      + ∑ f, (Γ a d f * R f b e c - R a f e c * Γ f d b) = 0)
    (d : Fin (n+1)) :
    ∑ a, ∑ c, G a c * (dRic a d c - ∑ f, Γ f c a * Ric f d - ∑ f, Γ f c d * Ric a f)
    = (1/2 : ℝ) * ∑ b, ∑ e, (dG b e d * Ric b e + G b e * dRic b e d) := by
  have F1' : ∀ b e, ∑ a, R a b e a = -Ric b e := fun b e => by
    rw [hRic, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun a _ => hR a b e a
  have F2' : ∀ b e k, ∑ a, dR a b e a k = -dRic b e k := fun b e k => by
    rw [hdRic, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun a _ => hdR a b e a k
  have Key' : ∀ a d, ∑ e, ∑ b, R a b d e * G b e = ∑ f, G a f * Ric f d := by
    intro a d
    have : ∀ e, ∑ b, R a b d e * G b e = -∑ b, R e b d e * G b a := fun e => hAS a e d e
    simp_rw [this]
    rw [Finset.sum_neg_distrib, Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul, F1' b d, hG]
    ring
  -- contract the second Bianchi identity over `c = a`, against `G^{be}`
  have hK : ∑ a, ∑ b, ∑ e, (G b e * dR a b a d e + G b e * dR a b d e a + G b e * dR a b e a d
      + G b e * ∑ f, (Γ a e f * R f b a d - R a f a d * Γ f e b)
      + G b e * ∑ f, (Γ a a f * R f b d e - R a f d e * Γ f a b)
      + G b e * ∑ f, (Γ a d f * R f b e a - R a f e a * Γ f d b)) = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun e _ => ?_
    linear_combination G b e * hB a b a d e
  simp only [Finset.sum_add_distrib] at hK
  have hT1 : ∑ a, ∑ b, ∑ e, G b e * dR a b a d e = ∑ a, ∑ c, G a c * dRic a d c := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hdRic, Finset.mul_sum]
  have hT3 : ∑ a, ∑ b, ∑ e, G b e * dR a b e a d = -∑ b, ∑ e, G b e * dRic b e d := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.mul_sum, F2']; ring
  have hT2 : ∑ a, ∑ b, ∑ e, G b e * dR a b d e a = ∑ a, ∑ c, G a c * dRic a d c
      + ∑ a, ∑ f, dG f a a * Ric f d - ∑ a, ∑ e, ∑ f, R a f d e * dG f e a := by
    have h1 : ∀ a, ∑ b, ∑ e, G b e * dR a b d e a = ∑ e, (-∑ f, R a f d e * dG f e a
        - ∑ f, dR e f d e a * G f a - ∑ f, R e f d e * dG f a a) := by
      intro a
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      have := hdAS a e d e a
      simp only [Finset.sum_add_distrib] at this
      have h' : ∑ b, G b e * dR a b d e a = ∑ f, dR a f d e a * G f e :=
        Finset.sum_congr rfl fun _ _ => mul_comm _ _
      rw [h']; linarith
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    have h2 : ∑ a, ∑ e, ∑ f, dR e f d e a * G f a = -∑ a, ∑ c, G a c * dRic a d c := by
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_mul, F2']; ring
    have h3 : ∑ a, ∑ e, ∑ f, R e f d e * dG f a a = -∑ a, ∑ f, dG f a a * Ric f d := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← Finset.sum_mul, F1']; ring
    rw [h2, h3]; ring
  have hT4 : ∑ a, ∑ b, ∑ e, G b e * ∑ f, (Γ a e f * R f b a d - R a f a d * Γ f e b)
      = ∑ a, ∑ b, ∑ e, ∑ f, G b e * (Γ a e f * R f b a d)
        - ∑ a, ∑ c, G a c * ∑ f, Γ f c a * Ric f d := by
    have h : ∑ a, ∑ b, ∑ e, ∑ f, G b e * (R a f a d * Γ f e b)
        = ∑ a, ∑ c, G a c * ∑ f, Γ f c a * Ric f d := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [hRic, ← Finset.mul_sum, ← Finset.sum_mul]; ring
    rw [← h, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  have hT5 : ∑ a, ∑ b, ∑ e, G b e * ∑ f, (Γ a a f * R f b d e - R a f d e * Γ f a b)
      = ∑ a, ∑ f, Γ a a f * ∑ h, G f h * Ric h d
        - ∑ a, ∑ e, ∑ f, ∑ h, R a f d e * Γ f a h * G h e := by
    have h1 : ∀ a, ∑ b, ∑ e, G b e * ∑ f, (Γ a a f * R f b d e - R a f d e * Γ f a b)
        = ∑ b, ∑ e, ∑ f, Γ a a f * (R f b d e * G b e)
          - ∑ b, ∑ e, ∑ f, R a f d e * Γ f a b * G b e := by
      intro a
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun f _ => by ring
    have p1 : ∀ a, ∑ b, ∑ e, ∑ f, Γ a a f * (R f b d e * G b e)
        = ∑ f, Γ a a f * ∑ h, G f h * Ric h d := by
      intro a
      rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm,
        Finset.sum_congr rfl fun f _ => Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← Key' f d, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
    have p2 : ∀ a, ∑ b, ∑ e, ∑ f, R a f d e * Γ f a b * G b e
        = ∑ e, ∑ f, ∑ h, R a f d e * Γ f a h * G h e := by
      intro a
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_comm
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun a _ => p1 a, Finset.sum_congr rfl fun a _ => p2 a]
  have hT6 : ∑ a, ∑ b, ∑ e, G b e * ∑ f, (Γ a d f * R f b e a - R a f e a * Γ f d b)
      = ∑ a, ∑ b, ∑ e, ∑ f, G b e * (Γ a d f * R f b e a)
        + ∑ b, ∑ e, ∑ f, G b e * Γ f d b * Ric f e := by
    have h : ∑ a, ∑ b, ∑ e, ∑ f, G b e * (R a f e a * Γ f d b)
        = -∑ b, ∑ e, ∑ f, G b e * Γ f d b * Ric f e := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      have : ∑ a, G b e * (R a f e a * Γ f d b) = G b e * Γ f d b * ∑ a, R a f e a := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, F1']; ring
    have h2 : ∑ a, ∑ b, ∑ e, G b e * ∑ f, (Γ a d f * R f b e a - R a f e a * Γ f d b)
        = ∑ a, ∑ b, ∑ e, ∑ f, G b e * (Γ a d f * R f b e a)
          - ∑ a, ∑ b, ∑ e, ∑ f, G b e * (R a f e a * Γ f d b) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun f _ => by ring
    rw [h2, h]; ring
  have hA1 : ∑ a, ∑ f, dG f a a * Ric f d = -∑ a, ∑ c, G a c * ∑ f, Γ f c a * Ric f d
      - ∑ a, ∑ f, Γ a a f * ∑ h, G f h * Ric h d := by
    have h : ∀ a f, dG f a a * Ric f d
        = -∑ h, Γ f a h * G h a * Ric f d - ∑ h, Γ a a h * G f h * Ric f d := by
      intro a f
      rw [hdG, neg_mul, Finset.sum_mul]
      simp only [add_mul, Finset.sum_add_distrib]; ring
    have q1 : ∑ a, ∑ f, ∑ h, Γ f a h * G h a * Ric f d
        = ∑ a, ∑ c, G a c * ∑ f, Γ f c a * Ric f d := by
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun f _ => by ring
    have q2 : ∑ a, ∑ f, ∑ h, Γ a a h * G f h * Ric f d
        = ∑ a, ∑ f, Γ a a f * ∑ h, G f h * Ric h d := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by rw [hG]; ring
    simp only [h, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [q1, q2]
  have hA2 : ∑ a, ∑ e, ∑ f, R a f d e * dG f e a
      = -∑ a, ∑ e, ∑ f, ∑ h, R a f d e * Γ f a h * G h e
        - ∑ a, ∑ e, ∑ f, ∑ h, R a f d e * Γ e a h * G f h := by
    have h : ∀ a e f, R a f d e * dG f e a
        = -∑ h, R a f d e * Γ f a h * G h e - ∑ h, R a f d e * Γ e a h * G f h := by
      intro a e f
      rw [hdG, mul_neg, Finset.mul_sum]
      simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc]; ring
    simp only [h, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hZ : ∑ b, ∑ e, dG b e d * Ric b e = -∑ b, ∑ e, ∑ f, G b e * Γ f d b * Ric f e
      - ∑ a, ∑ c, G a c * ∑ f, Γ f c d * Ric a f := by
    have h : ∀ b e, dG b e d * Ric b e
        = -∑ f, Γ b d f * G f e * Ric b e - ∑ f, Γ e d f * G b f * Ric b e := by
      intro b e
      rw [hdG, neg_mul, Finset.sum_mul]
      simp only [add_mul, Finset.sum_add_distrib]; ring
    have q1 : ∑ b, ∑ e, ∑ f, Γ b d f * G f e * Ric b e
        = ∑ b, ∑ e, ∑ f, G b e * Γ f d b * Ric f e := by
      rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm,
        Finset.sum_congr rfl fun b _ => Finset.sum_comm]
      exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun e _ =>
        Finset.sum_congr rfl fun b _ => by ring
    have q2 : ∑ b, ∑ e, ∑ f, Γ e d f * G b f * Ric b e
        = ∑ a, ∑ c, G a c * ∑ f, Γ f c d * Ric a f := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by rw [hΓ e d f]; ring
    simp only [h, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [q1, q2]
  have hB13 : ∑ a, ∑ e, ∑ f, ∑ h, R a f d e * Γ e a h * G f h
      = -∑ a, ∑ b, ∑ e, ∑ f, G b e * (Γ a e f * R f b a d) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hΓ i l k, hR l j d i]; ring
  have hB3 : ∑ a, ∑ b, ∑ e, ∑ f, G b e * (Γ a d f * R f b e a)
      = -∑ a, ∑ c, G a c * ∑ f, Γ f c d * Ric a f := by
    have h1 : ∀ a, ∑ b, ∑ e, ∑ f, G b e * (Γ a d f * R f b e a)
        = -∑ f, ∑ h, Γ a d f * G f h * Ric h a := by
      intro a
      rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm,
        Finset.sum_congr rfl fun b _ => Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      have : ∑ e, ∑ b, G b e * (Γ a d f * R f b e a)
          = -(Γ a d f * ∑ e, ∑ b, R f b a e * G b e) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun b _ => by rw [hR f b e a]; ring
      rw [this, Key', Finset.mul_sum]
      congr 1; exact Finset.sum_congr rfl fun h _ => by ring
    have q : ∑ a, ∑ f, ∑ h, Γ a d f * G f h * Ric h a
        = ∑ a, ∑ c, G a c * ∑ f, Γ f c d * Ric a f := by
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm,
        Finset.sum_congr rfl fun b _ => Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [hG h f, hΓ a f d]; ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_neg_distrib, q]
  have hL : ∑ a, ∑ c, G a c * (dRic a d c - ∑ f, Γ f c a * Ric f d - ∑ f, Γ f c d * Ric a f)
      = ∑ a, ∑ c, G a c * dRic a d c - ∑ a, ∑ c, G a c * ∑ f, Γ f c a * Ric f d
        - ∑ a, ∑ c, G a c * ∑ f, Γ f c d * Ric a f := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hRt : ∑ b, ∑ e, (dG b e d * Ric b e + G b e * dRic b e d)
      = ∑ b, ∑ e, dG b e d * Ric b e + ∑ b, ∑ e, G b e * dRic b e d := by
    simp only [Finset.sum_add_distrib]
  rw [hL, hRt]
  rw [hT1, hT2, hT3, hT4, hT5, hT6, hA2, hA1] at hK
  linear_combination (1/2 : ℝ) * hK - (1/2 : ℝ) * hZ - (1/2 : ℝ) * hB13 - (1/2 : ℝ) * hB3

/-! ### Smooth matrix fields and their partial derivatives -/

open scoped ContDiff

/-- A matrix field with smooth components. -/
def Sm (M : E → Mat) : Prop := ∀ a b, ContDiff ℝ ∞ fun y => M y a b

/-- Componentwise partial derivative `∂_c M` of a matrix field at `x`. -/
noncomputable def pdM (M : E → Mat) (x : E) (c : Fin (n+1)) : Mat :=
  Matrix.of fun a b => pd (fun y => M y a b) x c

lemma Sm.add {A B : E → Mat} (hA : Sm A) (hB : Sm B) : Sm fun y => A y + B y :=
  fun a b => by simpa only [Matrix.add_apply] using (hA a b).add (hB a b)

lemma Sm.sub {A B : E → Mat} (hA : Sm A) (hB : Sm B) : Sm fun y => A y - B y :=
  fun a b => by simpa only [Matrix.sub_apply] using (hA a b).sub (hB a b)

lemma Sm.mul {A B : E → Mat} (hA : Sm A) (hB : Sm B) : Sm fun y => A y * B y :=
  fun a b => by
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun f _ => (hA a f).mul (hB f b)

lemma Sm.transpose {A : E → Mat} (hA : Sm A) : Sm fun y => (A y)ᵀ :=
  fun a b => by simpa only [Matrix.transpose_apply] using hA b a

lemma Sm.pd {A : E → Mat} (hA : Sm A) (c : Fin (n+1)) : Sm fun y => pdM A y c :=
  fun a b => by simpa only [pdM, Matrix.of_apply] using contDiff_pd (hA a b) c

lemma Sm.const (A : Mat) : Sm fun _ : E => A := fun _ _ => contDiff_const

lemma contDiff_det {M : E → Mat} (hM : Sm M) : ContDiff ℝ ∞ fun y => (M y).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)

/-- The inverse of a smooth, everywhere invertible matrix field is smooth. -/
lemma Sm.inv {M : E → Mat} (hM : Sm M) (hdet : ∀ y, IsUnit (M y).det) :
    Sm fun y => (M y)⁻¹ := by
  intro a b
  have h : (fun y => (M y)⁻¹ a b) = fun y => ((M y).det)⁻¹ * (M y).adjugate a b := by
    funext y; rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [h]
  refine ((contDiff_det hM).inv fun y => (hdet y).ne_zero).mul ?_
  simp only [Matrix.adjugate_apply]
  apply contDiff_det
  intro i j
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hM i j

lemma pdM_add {A B : E → Mat} (hA : Sm A) (hB : Sm B) (x : E) (c : Fin (n+1)) :
    pdM (fun y => A y + B y) x c = pdM A x c + pdM B x c := by
  ext a b
  simp only [pdM, Matrix.of_apply, Matrix.add_apply]
  exact pd_add (diff_of_smooth (hA a b)) (diff_of_smooth (hB a b))

lemma pdM_sub {A B : E → Mat} (hA : Sm A) (hB : Sm B) (x : E) (c : Fin (n+1)) :
    pdM (fun y => A y - B y) x c = pdM A x c - pdM B x c := by
  ext a b
  simp only [pdM, Matrix.of_apply, Matrix.sub_apply]
  exact pd_sub (diff_of_smooth (hA a b)) (diff_of_smooth (hB a b))

lemma pdM_mul {A B : E → Mat} (hA : Sm A) (hB : Sm B) (x : E) (c : Fin (n+1)) :
    pdM (fun y => A y * B y) x c = pdM A x c * B x + A x * pdM B x c := by
  ext a b
  simp only [pdM, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [pd_sum _ fun f => diff_of_smooth ((hA a f).mul (hB f b)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun f _ =>
    pd_mul (diff_of_smooth (hA a f)) (diff_of_smooth (hB f b))

lemma pdM_transpose (A : E → Mat) (x : E) (c : Fin (n+1)) :
    pdM (fun y => (A y)ᵀ) x c = (pdM A x c)ᵀ := by
  ext a b; simp [pdM]

lemma pd_neg (f : E → ℝ) (x : E) (c : Fin (n+1)) : pd (fun y => -f y) x c = -pd f x c := by
  simp [pd, fderiv_fun_neg]

lemma pd_const (k : ℝ) (x : E) (c : Fin (n+1)) : pd (fun _ : E => k) x c = 0 := by
  simp [pd]

/-! ### Christoffel matrices and the metric -/

/-- `(Γ_c)^a_b = Γ^a_cb`, as a matrix field. -/
noncomputable def Gm (g : E → Mat) (y : E) (c : Fin (n+1)) : Mat :=
  Matrix.of fun a b => chr g y a c b

lemma chr_comm (g : E → Mat) (hs : ∀ y, (g y).IsSymm) (y : E) (a b c : Fin (n+1)) :
    chr g y a b c = chr g y a c b := by
  unfold chr
  congr 1
  exact Finset.sum_congr rfl fun d _ => by rw [dg_symm g hs y d b c]; ring

lemma chr_smooth {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) (a b c : Fin (n+1)) :
    ContDiff ℝ ∞ fun y => chr g y a b c := by
  unfold chr dg
  exact contDiff_const.mul (ContDiff.sum fun d _ => (hg.inv hdet a d).mul
    (((contDiff_pd (hg _ _) _).add (contDiff_pd (hg _ _) _)).sub (contDiff_pd (hg _ _) _)))

lemma Sm.gm {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) (c : Fin (n+1)) :
    Sm fun y => Gm g y c :=
  fun a b => by simpa only [Gm, Matrix.of_apply] using chr_smooth hg hdet a c b

/-- Metric compatibility as a matrix identity: `∂_c g = Γ_cᵀ g + g Γ_c`. -/
lemma pdM_metric (g : E → Mat) (hs : ∀ y, (g y).IsSymm) (hdet : ∀ y, IsUnit (g y).det)
    (y : E) (c : Fin (n+1)) : pdM g y c = (Gm g y c)ᵀ * g y + g y * Gm g y c := by
  ext a b
  simp only [pdM, Gm, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [show pd (fun y => g y a b) y c = dg g y c a b from rfl, metric_compat g hs y (hdet y) c a b]
  congr 1
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

/-- `∂_c g⁻¹ = −(g⁻¹ Γ_cᵀ + Γ_c g⁻¹)`. -/
lemma pdM_inv {g : E → Mat} (hg : Sm g) (hs : ∀ y, (g y).IsSymm) (hdet : ∀ y, IsUnit (g y).det)
    (x : E) (c : Fin (n+1)) :
    pdM (fun y => (g y)⁻¹) x c = -((g x)⁻¹ * (Gm g x c)ᵀ + Gm g x c * (g x)⁻¹) := by
  have h1 : pdM (fun y => (g y)⁻¹ * g y) x c = 0 := by
    have : (fun y => (g y)⁻¹ * g y) = fun _ => 1 :=
      funext fun y => Matrix.nonsing_inv_mul _ (hdet y)
    rw [this]; ext a b; simp [pdM, pd_const]
  rw [pdM_mul (hg.inv hdet) hg, pdM_metric g hs hdet] at h1
  have hGg : (g x)⁻¹ * g x = 1 := Matrix.nonsing_inv_mul _ (hdet x)
  have hgG : g x * (g x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hdet x)
  set D := pdM (fun y => (g y)⁻¹) x c
  set G := (g x)⁻¹
  set A := Gm g x c
  have k1 : D * g x * G = D := by rw [mul_assoc, hgG, mul_one]
  have k2 : G * Aᵀ * g x * G = G * Aᵀ := by rw [mul_assoc, hgG, mul_one]
  have k3 : G * (g x * A) * G = A * G := by rw [← mul_assoc G, hGg, one_mul]
  have e : D * g x * G + G * Aᵀ * g x * G + G * (g x * A) * G = 0 := by
    have := congrArg (· * G) h1
    simp only [zero_mul] at this
    rw [← this]; noncomm_ring
  rw [k1, k2, k3] at e
  rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact e

lemma inv_symm (g : E → Mat) (hs : ∀ y, (g y).IsSymm) (y : E) (a b : Fin (n+1)) :
    (g y)⁻¹ a b = (g y)⁻¹ b a := by
  have h : ((g y)⁻¹)ᵀ = (g y)⁻¹ := by rw [Matrix.transpose_nonsing_inv, (hs y).eq]
  have := congrArg (fun M => M b a) h
  simpa only [Matrix.transpose_apply] using this

/-! ### Curvature as a matrix-valued 2-form -/

/-- `(F_cd)^a_b = R^a_bcd`. -/
noncomputable def Fm (g : E → Mat) (y : E) (c d : Fin (n+1)) : Mat :=
  Matrix.of fun a b => riem g y a b c d

/-- `F_cd = ∂_c Γ_d − ∂_d Γ_c + [Γ_c, Γ_d]`. -/
lemma Fm_eq (g : E → Mat) (y : E) (c d : Fin (n+1)) :
    Fm g y c d = pdM (fun z => Gm g z d) y c - pdM (fun z => Gm g z c) y d
      + Gm g y c * Gm g y d - Gm g y d * Gm g y c := by
  ext a b
  simp [Fm, riem, pdM, Gm, Matrix.mul_apply]

lemma Sm.fm {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) (c d : Fin (n+1)) :
    Sm fun y => Fm g y c d := by
  rw [show (fun y => Fm g y c d) = _ from funext fun y => Fm_eq g y c d]
  exact ((((hg.gm hdet d).pd c).sub ((hg.gm hdet c).pd d)).add
    ((hg.gm hdet c).mul (hg.gm hdet d))).sub ((hg.gm hdet d).mul (hg.gm hdet c))

lemma riem_smooth {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det)
    (a b c d : Fin (n+1)) : ContDiff ℝ ∞ fun y => riem g y a b c d := by
  simpa only [Fm, Matrix.of_apply] using hg.fm hdet c d a b

/-- **Pair antisymmetry from metric compatibility**: `g⁻¹ F_cdᵀ + F_cd g⁻¹ = 0`, i.e. the
curvature with both indices raised, `R^{ab}_cd`, is antisymmetric in `a, b`. Proved from
`∂_c∂_d g = ∂_d∂_c g` and `∂g = Γᵀg + gΓ`. -/
lemma Fm_antisymm {g : E → Mat} (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (x : E) (c d : Fin (n+1)) :
    (g x)⁻¹ * (Fm g x c d)ᵀ + Fm g x c d * (g x)⁻¹ = 0 := by
  have hsym : pdM (fun y => pdM g y d) x c = pdM (fun y => pdM g y c) x d := by
    ext a b; simp only [pdM, Matrix.of_apply]; exact pd_pd_comm _ (hg a b) x d c
  have expand : ∀ c d, pdM (fun y => pdM g y d) x c
      = (pdM (fun y => Gm g y d) x c)ᵀ * g x + (Gm g x d)ᵀ * pdM g x c
        + (pdM g x c * Gm g x d + g x * pdM (fun y => Gm g y d) x c) := by
    intro c d
    rw [show (fun y => pdM g y d) = fun y => (Gm g y d)ᵀ * g y + g y * Gm g y d from
      funext fun y => pdM_metric g hs hdet y d]
    rw [pdM_add ((hg.gm hdet d).transpose.mul hg) (hg.mul (hg.gm hdet d)),
      pdM_mul (hg.gm hdet d).transpose hg, pdM_mul hg (hg.gm hdet d), pdM_transpose]
  rw [expand c d, expand d c, pdM_metric g hs hdet x c, pdM_metric g hs hdet x d] at hsym
  have hGg : (g x)⁻¹ * g x = 1 := Matrix.nonsing_inv_mul _ (hdet x)
  have hgG : g x * (g x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hdet x)
  have key : (Fm g x c d)ᵀ * g x + g x * Fm g x c d = 0 := by
    rw [Fm_eq]
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul]
    rw [← sub_eq_zero] at hsym
    rw [← hsym]; noncomm_ring
  set G := (g x)⁻¹
  set F := Fm g x c d
  have : G * (Fᵀ * g x + g x * F) * G = G * Fᵀ * (g x * G) + (G * g x) * F * G := by noncomm_ring
  rw [key, mul_zero, zero_mul, hgG, hGg, mul_one, one_mul] at this
  exact this.symm

/-- **Second Bianchi identity** in gauge form, for the curvature of `Γ` (no metric needed
beyond smoothness): `Σ_cyc (∂_e F_cd + [Γ_e, F_cd]) = 0`. -/
lemma bianchi2_mat {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) (x : E)
    (c d e : Fin (n+1)) :
    pdM (fun y => Fm g y c d) x e + (Gm g x e * Fm g x c d - Fm g x c d * Gm g x e)
      + (pdM (fun y => Fm g y d e) x c + (Gm g x c * Fm g x d e - Fm g x d e * Gm g x c))
      + (pdM (fun y => Fm g y e c) x d + (Gm g x d * Fm g x e c - Fm g x e c * Gm g x d))
      = 0 := by
  have hA := hg.gm hdet
  have hd : ∀ c d e, pdM (fun y => Fm g y c d) x e
      = pdM (fun y => pdM (fun z => Gm g z d) y c) x e
        - pdM (fun y => pdM (fun z => Gm g z c) y d) x e
        + (pdM (fun y => Gm g y c) x e * Gm g x d + Gm g x c * pdM (fun y => Gm g y d) x e)
        - (pdM (fun y => Gm g y d) x e * Gm g x c + Gm g x d * pdM (fun y => Gm g y c) x e) := by
    intro c d e
    rw [show (fun y => Fm g y c d) = _ from funext fun y => Fm_eq g y c d]
    rw [pdM_sub ((((hA d).pd c).sub ((hA c).pd d)).add ((hA c).mul (hA d))) ((hA d).mul (hA c)),
      pdM_add (((hA d).pd c).sub ((hA c).pd d)) ((hA c).mul (hA d)),
      pdM_sub ((hA d).pd c) ((hA c).pd d), pdM_mul (hA c) (hA d), pdM_mul (hA d) (hA c)]
  have hDD : ∀ e c d, pdM (fun y => pdM (fun z => Gm g z d) y c) x e
      = pdM (fun y => pdM (fun z => Gm g z d) y e) x c := by
    intro e c d
    ext a b
    simp only [pdM, Gm, Matrix.of_apply]
    exact pd_pd_comm _ (chr_smooth hg hdet a d b) x c e
  rw [hd c d e, hd d e c, hd e c d, hDD c e d, hDD d e c, hDD d c e,
    Fm_eq g x c d, Fm_eq g x d e, Fm_eq g x e c]
  noncomm_ring

/-! ### Componentwise consequences -/

lemma pd_sum_mul (A B : E → Fin (n+1) → ℝ) (hA : ∀ f, Differentiable ℝ fun y => A y f)
    (hB : ∀ f, Differentiable ℝ fun y => B y f) (x : E) (e : Fin (n+1)) :
    pd (fun y => ∑ f, A y f * B y f) x e
      = ∑ f, (pd (fun y => A y f) x e * B x f + A x f * pd (fun y => B y f) x e) := by
  have h := pd_sum (x := x) (c := e) (fun f y => A y f * B y f) fun f => (hA f).mul (hB f)
  rw [h]
  exact Finset.sum_congr rfl fun f _ => pd_mul (hA f) (hB f)

lemma riem_antisymm_cd (g : E → Mat) (y : E) (a b c d : Fin (n+1)) :
    riem g y a b c d = -riem g y a b d c := by
  unfold riem; ring

/-- Componentwise pair antisymmetry: `R^a_f cd g^{fb} = −R^b_f cd g^{fa}`. -/
lemma riem_raise_antisymm {g : E → Mat} (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (y : E) (a b c d : Fin (n+1)) :
    ∑ f, riem g y a f c d * (g y)⁻¹ f b = -∑ f, riem g y b f c d * (g y)⁻¹ f a := by
  have h := congrArg (fun M => M a b) (Fm_antisymm hg hs hdet y c d)
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fm, Matrix.of_apply,
    Matrix.zero_apply] at h
  have h2 : ∑ f, (g y)⁻¹ a f * riem g y b f c d = ∑ f, riem g y b f c d * (g y)⁻¹ f a :=
    Finset.sum_congr rfl fun f _ => by rw [inv_symm g hs y a f]; ring
  linarith

/-- The second Bianchi identity, componentwise. -/
lemma bianchi2 {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) (x : E)
    (a b c d e : Fin (n+1)) :
    pd (fun y => riem g y a b c d) x e + pd (fun y => riem g y a b d e) x c
      + pd (fun y => riem g y a b e c) x d
      + ∑ f, (chr g x a e f * riem g x f b c d - riem g x a f c d * chr g x f e b)
      + ∑ f, (chr g x a c f * riem g x f b d e - riem g x a f d e * chr g x f c b)
      + ∑ f, (chr g x a d f * riem g x f b e c - riem g x a f e c * chr g x f d b) = 0 := by
  have h := congrArg (fun M => M a b) (bianchi2_mat hg hdet x c d e)
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fm, Gm, pdM, Matrix.of_apply,
    Matrix.zero_apply] at h
  simp only [Finset.sum_sub_distrib]
  linarith

/-! ### The contracted Bianchi identity for a general metric -/

/-- **Contracted Bianchi identity for any smooth metric**: `∇^a R_ab = ½ ∂_b R`, for every
symmetric, everywhere-invertible matrix field `g` on `ℝ^(n+1)` with smooth components, with
`Γ`, Riemann, Ricci and `R` computed from `g` by the coordinate formulas of `CurvedCoords`. -/
theorem bianchi_general (g : E → Mat) (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (x : E) (b : Fin (n+1)) :
    covDiv g (ricci g) x b = (1/2 : ℝ) * pd (scal g) x b := by
  have hR' : ∀ a b c d, Differentiable ℝ fun y => riem g y a b c d :=
    fun a b c d => diff_of_smooth (riem_smooth hg hdet a b c d)
  have hRic' : ∀ b e, Differentiable ℝ fun y => ricci g y b e := fun b e => by
    simp only [ricci, Matrix.of_apply]
    exact Differentiable.fun_sum fun a _ => hR' a b a e
  have hG' : ∀ a b, Differentiable ℝ fun y => (g y)⁻¹ a b :=
    fun a b => diff_of_smooth (hg.inv hdet a b)
  have hdG : ∀ a b e, pd (fun y => (g y)⁻¹ a b) x e
      = -∑ f, (chr g x a e f * (g x)⁻¹ f b + chr g x b e f * (g x)⁻¹ a f) := by
    intro a b e
    have h := congrArg (fun M => M a b) (pdM_inv hg hs hdet x e)
    simp only [pdM, Gm, Matrix.of_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.transpose_apply] at h
    rw [h, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun f _ => by ring
  have hdAS : ∀ a b c d e,
      ∑ f, (pd (fun y => riem g y a f c d) x e * (g x)⁻¹ f b
        + riem g x a f c d * pd (fun y => (g y)⁻¹ f b) x e)
      = -∑ f, (pd (fun y => riem g y b f c d) x e * (g x)⁻¹ f a
        + riem g x b f c d * pd (fun y => (g y)⁻¹ f a) x e) := by
    intro a b c d e
    have h := congrArg (fun φ => pd φ x e)
      (funext fun y => riem_raise_antisymm hg hs hdet y a b c d)
    rw [pd_neg, pd_sum_mul _ _ (fun f => hR' a f c d) (fun f => hG' f b),
      pd_sum_mul _ _ (fun f => hR' b f c d) (fun f => hG' f a)] at h
    exact h
  have hdR : ∀ a b c d e, pd (fun y => riem g y a b c d) x e
      = -pd (fun y => riem g y a b d c) x e := by
    intro a b c d e
    rw [← pd_neg]
    exact congrArg (fun φ => pd φ x e) (funext fun y => riem_antisymm_cd g y a b c d)
  have hscal : pd (scal g) x b = ∑ c, ∑ e, (pd (fun y => (g y)⁻¹ c e) x b * ricci g x c e
      + (g x)⁻¹ c e * pd (fun y => ricci g y c e) x b) := by
    unfold scal
    have h := pd_sum (x := x) (c := b) (fun c y => ∑ e, (g y)⁻¹ c e * ricci g y c e)
      fun c => Differentiable.fun_sum fun e _ => (hG' c e).mul (hRic' c e)
    rw [h]
    exact Finset.sum_congr rfl fun c _ =>
      pd_sum_mul (fun y e => (g y)⁻¹ c e) (fun y e => ricci g y c e) (hG' c) (hRic' c) x b
  have key := contracted_alg (fun a b => (g x)⁻¹ a b) (chr g x) (riem g x)
    (fun a b c d e => pd (fun y => riem g y a b c d) x e)
    (fun a b e => pd (fun y => (g y)⁻¹ a b) x e)
    (fun b e => ricci g x b e) (fun b e k => pd (fun y => ricci g y b e) x k)
    (fun b e => by simp [ricci])
    (fun b e k => by
      simp only [ricci, Matrix.of_apply]
      exact pd_sum _ fun a => hR' a b a e)
    (inv_symm g hs x) (chr_comm g hs x) (riem_antisymm_cd g x) hdR hdG
    (riem_raise_antisymm hg hs hdet x) hdAS (bianchi2 hg hdet x) b
  rw [hscal, ← key]
  rfl

/-! ### Symmetry of the Ricci tensor -/

/-- `tr F_cd = 0` for a metric connection. -/
lemma trace_Fm {g : E → Mat} (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (x : E) (c d : Fin (n+1)) : (Fm g x c d).trace = 0 := by
  have hGg : (g x)⁻¹ * g x = 1 := Matrix.nonsing_inv_mul _ (hdet x)
  have hgG : g x * (g x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hdet x)
  have h := congrArg (· * g x) (Fm_antisymm hg hs hdet x c d)
  simp only [Matrix.add_mul, zero_mul, Matrix.mul_assoc, hGg, Matrix.mul_one] at h
  have h2 := congrArg Matrix.trace h
  rw [Matrix.trace_add, Matrix.trace_zero, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, hgG,
    Matrix.one_mul, Matrix.trace_transpose] at h2
  linarith

lemma ricci_symm {g : E → Mat} (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (x : E) : (ricci g x).IsSymm := by
  have hpd : ∀ a b c k, pd (fun y => chr g y a b c) x k = pd (fun y => chr g y a c b) x k :=
    fun a b c k => congrArg (fun φ => pd φ x k) (funext fun y => chr_comm g hs y a b c)
  have hsum : ∀ a b c i, ∑ f, chr g x a i f * chr g x f b c = ∑ f, chr g x a i f * chr g x f c b :=
    fun a b c i => Finset.sum_congr rfl fun f _ => by rw [chr_comm g hs x f b c]
  have hpt : ∀ a b d, riem g x a b a d - riem g x a d a b = riem g x a a b d := by
    intro a b d
    unfold riem
    rw [hpd a d b a, hpd a a b d, hpd a a d b, hsum a d b a, hsum a a d b, hsum a a b d]
    ring
  have htr : ∀ b d, ∑ a, riem g x a a b d = 0 := fun b d => by
    have := trace_Fm hg hs hdet x b d
    simpa [Matrix.trace, Fm] using this
  ext b d
  simp only [Matrix.transpose_apply, ricci, Matrix.of_apply]
  have h := htr d b
  rw [← Finset.sum_congr rfl fun a _ => hpt a d b, Finset.sum_sub_distrib] at h
  linarith

/-! ### The Clausius chain on a general curved spacetime -/

open Flat in
/-- `φ ↦ φ g`. -/
noncomputable def mulGen (g : E → Mat) (hg : Sm g) : Ssub n →ₗ[ℝ] Vsub n where
  toFun φ := ⟨fun y => φ.1 y • g y, fun a b => by
    have hφ : Differentiable ℝ φ.1 := φ.2
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hφ.mul (diff_of_smooth (hg a b))⟩
  map_add' φ ψ := by ext y a b; simp [add_mul]
  map_smul' c φ := by ext y a b; simp [mul_assoc]

open Flat in
/-- `X ↦ tr(g⁻¹ X)/(n+1)`. -/
noncomputable def trGen (g : E → Mat) (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) :
    Vsub n →ₗ[ℝ] Ssub n where
  toFun X := ⟨fun y => Matrix.trace ((g y)⁻¹ * X.1 y) / (n + 1), by
    show Differentiable ℝ _
    simp only [div_eq_mul_inv]
    apply Differentiable.mul_const
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ =>
      (diff_of_smooth (hg.inv hdet i j)).mul (X.2 j i)⟩
  map_add' X Y := by ext y; simp [Matrix.mul_add, Matrix.trace_add, add_div]
  map_smul' c X := by ext y; simp [Matrix.trace_smul, mul_div_assoc]

open Flat in
/-- The covariant divergence of `g`, linear on differentiable fields. -/
noncomputable def divGen (g : E → Mat) : Vsub n →ₗ[ℝ] (E → Fin (n+1) → ℝ) where
  toFun X := fun x b => covDiv g X.1 x b
  map_add' X Y := by
    ext x b
    simp only [covDiv, Submodule.coe_add, Pi.add_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [pd_add (X.2 a b) (Y.2 a b)]
    simp only [mul_add, Finset.sum_add_distrib]; ring
  map_smul' k X := by
    ext x b
    simp only [covDiv, Submodule.coe_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [pd_const_mul k (X.2 a b)]
    have h1 : ∑ d, chr g x d c a * (k * X.1 x d b) = k * ∑ d, chr g x d c a * X.1 x d b := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∑ d, chr g x d c b * (k * X.1 x a d) = k * ∑ d, chr g x d c b * X.1 x a d := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h1, h2]; ring

lemma ricci_diff {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) (a b : Fin (n+1)) :
    Differentiable ℝ fun y => ricci g y a b := by
  simp only [ricci, Matrix.of_apply]
  exact Differentiable.fun_sum fun c _ => diff_of_smooth (riem_smooth hg hdet c a c b)

lemma scal_diff {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) :
    Differentiable ℝ (scal g) := by
  unfold scal
  exact Differentiable.fun_sum fun b _ => Differentiable.fun_sum fun d _ =>
    (diff_of_smooth (hg.inv hdet b d)).mul (ricci_diff hg hdet b d)

/-- The metric `Pᵀ η P` of a frame field `P`. -/
noncomputable def gP (P : E → Mat) (x : E) : Mat := (P x)ᵀ * eta n * P x

lemma Sm.gP {P : E → Mat} (hP : Sm P) : Sm (gP P) :=
  (hP.transpose.mul (Sm.const _)).mul hP

lemma gP_symm (P : E → Mat) (x : E) : (gP P x).IsSymm := by
  unfold gP Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, eta_isSymm.eq,
    Matrix.mul_assoc]

lemma gP_det (P : E → Mat) (hP : ∀ x, IsUnit (P x).det) (x : E) : IsUnit (gP P x).det := by
  unfold gP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact ((hP x).mul (isUnit_iff_ne_zero.mpr eta_det_ne_zero)).mul (hP x)

open Flat in
/-- **Clausius on a general curved spacetime.** Take any metric `g = Pᵀ η P` on `ℝ^(n+1)` with
`P` smooth and everywhere invertible, its Christoffel symbols, Ricci tensor and scalar curvature
computed from `g`, and a symmetric stress tensor `T` with differentiable components and zero
covariant divergence. If `Ric(k,k) = κₑ T(k,k)` for every `g`-null `k` at every point, then
`Ric − ½ R g + Λ g = κₑ T` for one constant `Λ`. Metric compatibility (`covDiv_smul_metric`),
the contracted Bianchi identity (`bianchi_general`) and the symmetry of `Ric` (`ricci_symm`)
are proved, not assumed. -/
theorem curved_clausius_general (P : E → Mat) (hPs : Sm P) (hP : ∀ x, IsUnit (P x).det)
    (T : E → Mat) (hTd : ∀ a b, Differentiable ℝ fun y => T y a b) (hTs : ∀ x, (T x).IsSymm)
    (hcons : ∀ x b, covDiv (gP P) T x b = 0) (κₑ : ℝ)
    (hClausius : ∀ x k, qf (gP P x) k = 0 → qf (ricci (gP P) x) k = κₑ * qf (T x) k) :
    ∃ Λ : ℝ, ∀ x, ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x + Λ • gP P x
      = κₑ • T x := by
  have hg := hPs.gP
  have hs := gP_symm P
  have hdet := gP_det P hP
  have hgd : ∀ a b, Differentiable ℝ fun y => gP P y a b := fun a b => diff_of_smooth (hg a b)
  let Tv : Vsub n := ⟨T, hTd⟩
  let Ric : Vsub n := ⟨ricci (gP P), ricci_diff hg hdet⟩
  let Rs : Ssub n := ⟨scal (gP P), scal_diff hg hdet⟩
  obtain ⟨Λ, hΛ⟩ := @jacobson_chain n (Fin (n+1) → ℝ) (Vsub n) (Ssub n)
    ((Fin (n+1) → ℝ) → Fin (n+1) → ℝ) _ _ _ _ _ _ P hP
    (Vsub n).subtype Subtype.val_injective (Ssub n).subtype
    (mulGen (gP P) hg) (fun φ x => rfl) (trGen (gP P) hg hdet) (fun X x => rfl)
    one (divGen (gP P)) dL
    (fun φ => by
      ext x b
      exact covDiv_smul_metric (gP P) hs hdet hgd φ.1 φ.2 x b)
    (fun φ hφ => by
      refine ⟨φ.1 0, ?_⟩
      have hconst := is_const_of_fderiv_eq_zero φ.2 (fun x => clm_eq_zero_of_basis _
        fun b => congrFun (congrFun hφ x) b)
      ext x; simp [Flat.one, hconst x 0])
    Ric Tv Rs κₑ (fun x => ricci_symm hg hs hdet x) hTs
    (fun x k hk => hClausius x k hk)
    (by ext x b; exact bianchi_general (gP P) hg hs hdet x b) (by ext x b; exact hcons x b)
  refine ⟨Λ, fun x => ?_⟩
  have := congrArg (fun v : Vsub n => v.1 x) hΛ
  simpa [mulGen, Flat.one, Tv, Ric, Rs, smul_smul] using this

end EntEq.Curved
