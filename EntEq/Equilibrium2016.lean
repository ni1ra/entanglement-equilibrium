/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Jacobson 2016 ("Entanglement equilibrium and the Einstein equation", arXiv:1505.04753):
  maximal vacuum entanglement at fixed volume of every small geodesic ball gives, for every unit
  timelike `u` at every point, `G(u,u) − Λ = κ T(u,u)` (signature `−+++`, so `g(u,u) = −1`).

  In the paper's eq. (23) the stationarity condition reads
      G(u,u) − λ = κ (T(u,u) + δX),   κ = 2π/(ħη),
  where `λ` is the curvature scale of the maximally symmetric reference state and `δX` the
  conjectured scalar correction for non-conformal matter. Writing `Λ x + ψ x` for
  `λ + κ δX`, the theorems below give (i) the pointwise tensor equation and (ii) that
  conservation forces `λ + κ δX` to be a spacetime constant: the paper's eq. (25), up to the
  sign of `δX` (see `eq24_sign`).
-/
import EntEq.Bianchi

open Matrix

namespace EntEq

variable {n : ℕ}

/-- Timelike-unit lemma in an arbitrary orthonormal frame: if `X(u,u) = c` for every
`g`-unit timelike `u` with `g = Pᵀ η P`, then `X = −c g`. -/
theorem unit_timelike_const_lorentzian (P X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hP : IsUnit P.det) (hX : X.IsSymm) (c : ℝ)
    (hu : ∀ u, qf (Pᵀ * eta n * P) u = -1 → qf X u = c) : X = -c • (Pᵀ * eta n * P) := by
  set Q := P⁻¹
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hP
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hP
  have hY : (Qᵀ * X * Q).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose, hX.eq,
      Matrix.mul_assoc]
  have hc := unit_timelike_const (Qᵀ * X * Q) hY c (by
    intro u hu1
    rw [qf_congr]
    apply hu
    rw [qf_congr, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    exact hu1)
  have : X = Pᵀ * (Qᵀ * X * Q) * P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hQP,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one]
  rw [this, hc, Matrix.mul_smul, Matrix.smul_mul]

variable {M : Type*}

/-- **The 2016 chain.** Tensor fields live in a module `V` and scalar fields in `S` (for
example smooth fields), read off pointwise by `evV` (injective) and `evS`; `mulG L` is the
field `L g`. If at every point `x`, for every unit timelike `u`,
`G(u,u) − L(x) = κ T(u,u)`, then `G + L g = κ T`. If moreover `div G = 0` (Bianchi),
`div T = 0`, `div (φ g) = dφ` and `dφ = 0 ⇒ φ` constant, then `L` is a constant. With
`L = λ + κδX` this is Jacobson's eq. (25): the reference curvature `λ` must vary to absorb a
non-constant `δX`, leaving one constant `Λ`. `Flat.flat_equilibrium` instantiates every
hypothesis on Minkowski space. -/
theorem equilibrium_chain
    {V S W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup S] [Module ℝ S]
    [AddCommGroup W] [Module ℝ W]
    (P : M → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hP : ∀ x, IsUnit (P x).det)
    (evV : V →ₗ[ℝ] (M → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) (hevV : Function.Injective evV)
    (evS : S →ₗ[ℝ] (M → ℝ))
    (mulG : S →ₗ[ℝ] V) (hmulG : ∀ φ x, evV (mulG φ) x = evS φ x • ((P x)ᵀ * eta n * P x))
    (one : S) (div : V →ₗ[ℝ] W) (d : S →ₗ[ℝ] W)
    (hcompat : ∀ φ, div (mulG φ) = d φ) (hconn : ∀ φ, d φ = 0 → ∃ c : ℝ, φ = c • one)
    (Gt T : V) (L : S) (κ : ℝ)
    (hG : ∀ x, (evV Gt x).IsSymm) (hT : ∀ x, (evV T x).IsSymm)
    (hEq : ∀ x u, qf ((P x)ᵀ * eta n * P x) u = -1 →
      qf (evV Gt x) u - evS L x = κ * qf (evV T x) u)
    (hBianchi : div Gt = 0) (hcons : div T = 0) :
    Gt + mulG L = κ • T ∧ ∃ c : ℝ, L = c • one := by
  have hfield : Gt + mulG L = κ • T := by
    apply hevV
    funext x
    have h := unit_timelike_const_lorentzian (P x) (evV Gt x - κ • evV T x) (hP x)
      ((hG x).sub ((hT x).smul κ)) (evS L x) (by
        intro u hu
        have := hEq x u hu
        simp only [qf, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
          smul_eq_mul] at this ⊢
        linarith)
    rw [neg_smul, sub_eq_iff_eq_add] at h
    rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, hmulG, h]; abel
  refine ⟨hfield, ?_⟩
  have hd : d L = 0 := by
    have := congrArg div hfield
    rw [map_add, map_smul, hBianchi, hcons, smul_zero, zero_add, hcompat] at this
    exact this
  exact hconn L hd

/-- **Sign check of Jacobson 2016, eq. (24).** In signature `−+++` a unit timelike `u` has
`g(u,u) = −1`. The paper's tensor form `G + λg = κ(T + δX g)` contracts to
`G(u,u) − λ = κ(T(u,u) − δX)`, whereas its eq. (23) requires `+ κ δX`. So the tensor form of
eq. (23) is `G + λg = κ(T − δX g)`; eqs. (24)–(25) carry a sign slip in `δX`, harmless because
`δX` is an undetermined scalar absorbed into `λ` and `Λ`. -/
theorem eq24_sign (g G T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (lam κ δX : ℝ) (u : Fin (n+1) → ℝ)
    (hu : qf g u = -1) (h24 : G + lam • g = κ • (T + δX • g)) :
    qf G u - lam = κ * (qf T u - δX) := by
  have := congrArg (fun M => qf M u) h24
  simp only [qf, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul] at this hu ⊢
  rw [hu] at this
  linarith

end EntEq
