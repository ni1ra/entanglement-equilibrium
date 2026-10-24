/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
import EntEq.FlatChain
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-
  Curved spacetime in coordinates on `ℝ^(n+1)`, without Mathlib's (absent) Levi-Civita
  connection: Christoffel symbols, covariant divergence, Riemann, Ricci and scalar curvature are
  built from a matrix-valued metric `g` and Fréchet partial derivatives.

  * `covDiv_smul_metric`: `∇·(φ g) = dφ` for any symmetric, everywhere-invertible metric with
    differentiable components and any differentiable `φ` (metric compatibility).
  * `bianchi_conf`: the contracted Bianchi identity `∇^a R_ab = ½ ∂_b R`, proved only for
    conformally flat metrics `g = e^{2w} η` with `w` smooth (any dimension `n+1`); the general
    case is not proved here.
  * `curved_clausius`, `curved_equilibrium`: `jacobson_chain` and `equilibrium_chain`
    instantiated on that conformally flat family, with both `hcompat` and `hBianchi` proved.

  Everything is global on `ℝ^(n+1)` (no open sets or charts).
-/

open Matrix

namespace EntEq.Curved

variable {n : ℕ}

local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

/-- Coordinate partial derivative `∂_c f` at `x`. -/
noncomputable def pd (f : E → ℝ) (x : E) (c : Fin (n+1)) : ℝ := fderiv ℝ f x (e c)

/-- `∂_c g_ab` at `x`. -/
noncomputable def dg (g : E → Mat) (x : E) (c a b : Fin (n+1)) : ℝ := pd (fun y => g y a b) x c

/-- Christoffel symbols `Γ^a_bc = ½ g^{ad}(∂_b g_dc + ∂_c g_db − ∂_d g_bc)`. -/
noncomputable def chr (g : E → Mat) (x : E) (a b c : Fin (n+1)) : ℝ :=
  (1/2 : ℝ) * ∑ d, (g x)⁻¹ a d * (dg g x b d c + dg g x c d b - dg g x d b c)

/-- Covariant divergence of a (0,2) field:
`(∇·X)_b = g^{ac}(∂_c X_ab − Γ^d_ca X_db − Γ^d_cb X_ad)`. -/
noncomputable def covDiv (g : E → Mat) (X : E → Mat) (x : E) (b : Fin (n+1)) : ℝ :=
  ∑ a, ∑ c, (g x)⁻¹ a c *
    (pd (fun y => X y a b) x c - ∑ d, chr g x d c a * X x d b - ∑ d, chr g x d c b * X x a d)

/-- Lowered Christoffel symbol: `g_ed Γ^d_ca = ½(∂_c g_ea + ∂_a g_ec − ∂_e g_ca)`. -/
lemma lower_chr (g : E → Mat) (x : E) (hg : IsUnit (g x).det) (e' c a : Fin (n+1)) :
    ∑ d, g x e' d * chr g x d c a = (1/2 : ℝ) * (dg g x c e' a + dg g x a e' c - dg g x e' c a) := by
  have h1 : g x * (g x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hg
  unfold chr
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ f : Fin (n+1), ∑ d, g x e' d * ((1/2 : ℝ) * ((g x)⁻¹ d f *
      (dg g x c f a + dg g x a f c - dg g x f c a))) =
      (1/2 : ℝ) * (dg g x c f a + dg g x a f c - dg g x f c a) * (g x * (g x)⁻¹) e' f := by
    intro f
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  simp_rw [this, h1, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp

/-- For a symmetric metric, `∂_c g_ab` is symmetric in `a, b`. -/
lemma dg_symm (g : E → Mat) (hs : ∀ y, (g y).IsSymm) (x : E) (c a b : Fin (n+1)) :
    dg g x c a b = dg g x c b a := by
  unfold dg pd
  congr 3
  funext y
  exact (hs y).apply b a

/-- **Metric compatibility** `∇_c g_ab = 0`, as an algebraic identity in `Γ`:
`∂_c g_ab = Γ^d_ca g_db + Γ^d_cb g_ad`. -/
theorem metric_compat (g : E → Mat) (hs : ∀ y, (g y).IsSymm) (x : E) (hg : IsUnit (g x).det)
    (c a b : Fin (n+1)) :
    dg g x c a b = ∑ d, chr g x d c a * g x d b + ∑ d, chr g x d c b * g x a d := by
  have h1 : ∑ d, chr g x d c a * g x d b = ∑ d, g x b d * chr g x d c a :=
    Finset.sum_congr rfl fun d _ => by rw [← (hs x).apply b d]; ring
  have h2 : ∑ d, chr g x d c b * g x a d = ∑ d, g x a d * chr g x d c b :=
    Finset.sum_congr rfl fun d _ => by ring
  rw [h1, h2, lower_chr g x hg, lower_chr g x hg]
  have := dg_symm g hs x
  linarith [this c b a, this a b c, this b a c]

/-- **`∇·(φ g) = dφ`** for a differentiable scalar `φ`, on any symmetric metric with
differentiable, everywhere-invertible components. -/
theorem covDiv_smul_metric (g : E → Mat) (hs : ∀ y, (g y).IsSymm) (hg : ∀ y, IsUnit (g y).det)
    (hgd : ∀ a b, Differentiable ℝ fun y => g y a b) (φ : E → ℝ) (hφ : Differentiable ℝ φ)
    (x : E) (b : Fin (n+1)) :
    covDiv g (fun y => φ y • g y) x b = pd φ x b := by
  have hinner : ∀ a c, pd (fun y => (φ y • g y) a b) x c
      - ∑ d, chr g x d c a * (φ x • g x) d b - ∑ d, chr g x d c b * (φ x • g x) a d
      = pd φ x c * g x a b := by
    intro a c
    have hprod : pd (fun y => (φ y • g y) a b) x c = pd φ x c * g x a b + φ x * dg g x c a b := by
      simp only [pd, dg, Matrix.smul_apply, smul_eq_mul]
      rw [fderiv_fun_mul (hφ x) (hgd a b x)]
      simp; ring
    have h1 : ∑ d, chr g x d c a * (φ x • g x) d b = φ x * ∑ d, chr g x d c a * g x d b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by simp only [Matrix.smul_apply, smul_eq_mul]; ring
    have h2 : ∑ d, chr g x d c b * (φ x • g x) a d = φ x * ∑ d, chr g x d c b * g x a d := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by simp only [Matrix.smul_apply, smul_eq_mul]; ring
    rw [hprod, h1, h2, metric_compat g hs x (hg x) c a b]
    ring
  unfold covDiv
  simp_rw [hinner]
  have h1 : g x * (g x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hg x)
  rw [Finset.sum_comm]
  have : ∀ c, ∑ a, (g x)⁻¹ a c * (pd φ x c * g x a b) = pd φ x c * (g x * (g x)⁻¹) b c := by
    intro c
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [(hs x).apply a b]; ring
  simp_rw [this, h1, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp

/-! ### Smoothness helpers -/

open scoped ContDiff

lemma contDiff_pd {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : Fin (n+1)) :
    ContDiff ℝ ∞ fun y => pd f y a :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma pd_pd (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (x : E) (a b : Fin (n+1)) :
    pd (fun y => pd f y a) x b = fderiv ℝ (fderiv ℝ f) x (e b) (e a) := by
  unfold pd
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  rw [fderiv_clm_apply hc (differentiableAt_const _)]
  simp

/-- Second partial derivatives of a smooth function commute. -/
lemma pd_pd_comm (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (x : E) (a b : Fin (n+1)) :
    pd (fun y => pd f y a) x b = pd (fun y => pd f y b) x a := by
  rw [pd_pd f hf, pd_pd f hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-! ### Conformally flat metrics `g = e^{2w} η` -/

/-- The conformally flat metric `e^{2w(y)} η`. -/
noncomputable def conf (w : E → ℝ) (y : E) : Mat := Real.exp (2 * w y) • eta n

lemma eta_eq (a b : Fin (n+1)) : eta n a b = if a = b then eta n a a else 0 := by
  by_cases h : a = b
  · subst h; simp
  · simp [eta_apply, h]

/-- The signature entries `η_aa = ±1`. -/
def sg (a : Fin (n+1)) : ℝ := eta n a a

lemma sg_sq (a : Fin (n+1)) : sg a * sg a = 1 := eta_sq a

lemma sg_sq2 (a : Fin (n+1)) : sg a ^ 2 = 1 := by rw [sq, sg_sq]

lemma sg_pow4 (a : Fin (n+1)) : sg a ^ 4 = 1 := by
  rw [show sg a ^ 4 = (sg a ^ 2) ^ 2 by ring, sg_sq2]; simp

lemma eta_sg (a b : Fin (n+1)) : eta n a b = if a = b then sg a else 0 := eta_eq a b

lemma eta_isSymm : (eta n).IsSymm := Matrix.isSymm_diagonal _

lemma conf_symm (w : E → ℝ) (y : E) : (conf w y).IsSymm := eta_isSymm.smul _

lemma conf_left_inv (w : E → ℝ) (y : E) :
    (Real.exp (-2 * w y) • eta n) * conf w y = 1 := by
  rw [conf, Matrix.smul_mul, Matrix.mul_smul, Flat.eta_mul_self, smul_smul, ← Real.exp_add]
  simp

lemma conf_inv (w : E → ℝ) (y : E) : (conf w y)⁻¹ = Real.exp (-2 * w y) • eta n :=
  Matrix.inv_eq_left_inv (conf_left_inv w y)

lemma conf_det (w : E → ℝ) (y : E) : IsUnit (conf w y).det :=
  Matrix.isUnit_det_of_left_inverse (conf_left_inv w y)

lemma dg_conf (w : E → ℝ) (hw : Differentiable ℝ w) (x : E) (c a b : Fin (n+1)) :
    dg (conf w) x c a b = 2 * Real.exp (2 * w x) * pd w x c * eta n a b := by
  unfold dg pd conf
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [fderiv_mul_const (((hw.const_mul 2).exp) x)]
  rw [fderiv_exp ((hw.const_mul 2) x), fderiv_const_mul (hw x)]
  simp; ring

/-- Christoffel symbols of `e^{2w} η`:
`Γ^a_bc = δ^a_c ∂_bw + δ^a_b ∂_cw − δ_bc η_aa η_bb ∂_aw`. -/
lemma chr_conf (w : E → ℝ) (hw : Differentiable ℝ w) (x : E) (a b c : Fin (n+1)) :
    chr (conf w) x a b c = (if a = c then 1 else 0) * pd w x b + (if a = b then 1 else 0) * pd w x c
      - (if b = c then 1 else 0) * (sg a * sg b) * pd w x a := by
  unfold chr
  simp only [conf_inv, dg_conf w hw, Matrix.smul_apply, smul_eq_mul]
  have hexp : Real.exp (-2 * w x) * Real.exp (2 * w x) = 1 := by rw [← Real.exp_add]; simp
  have : ∀ d, Real.exp (-2 * w x) * eta n a d *
      (2 * Real.exp (2 * w x) * pd w x b * eta n d c + 2 * Real.exp (2 * w x) * pd w x c * eta n d b
        - 2 * Real.exp (2 * w x) * pd w x d * eta n b c)
      = 2 * (eta n a d * (pd w x b * eta n d c + pd w x c * eta n d b - pd w x d * eta n b c)) := by
    intro d; linear_combination (2 * eta n a d * (pd w x b * eta n d c + pd w x c * eta n d b
        - pd w x d * eta n b c)) * hexp
  simp_rw [this]
  rw [← Finset.mul_sum]
  simp_rw [eta_sg, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hac : a = c <;> by_cases hab : a = b <;> by_cases hbc : b = c <;>
    simp_all <;> (ring_nf; try simp only [sg_sq2]; try ring_nf)

/-! ### Curvature built from `Γ` -/

/-- Riemann tensor `R^a_bcd = ∂_c Γ^a_db − ∂_d Γ^a_cb + Γ^a_cf Γ^f_db − Γ^a_df Γ^f_cb`. -/
noncomputable def riem (g : E → Mat) (x : E) (a b c d : Fin (n+1)) : ℝ :=
  pd (fun y => chr g y a d b) x c - pd (fun y => chr g y a c b) x d
    + ∑ f, chr g x a c f * chr g x f d b - ∑ f, chr g x a d f * chr g x f c b

/-- Ricci tensor `R_bd = R^a_bad`. -/
noncomputable def ricci (g : E → Mat) (x : E) : Mat := Matrix.of fun b d => ∑ a, riem g x a b a d

/-- Scalar curvature `R = g^{bd} R_bd`. -/
noncomputable def scal (g : E → Mat) (x : E) : ℝ := ∑ b, ∑ d, (g x)⁻¹ b d * ricci g x b d

lemma sum_ite_irrel' (p : Prop) [Decidable p] (f : Fin (n+1) → ℝ) :
    ∑ i, (if p then f i else 0) = if p then ∑ i, f i else 0 := by
  split_ifs <;> simp

lemma pd_lin3 (f₁ f₂ f₃ : E → ℝ) (h₁ : Differentiable ℝ f₁) (h₂ : Differentiable ℝ f₂)
    (h₃ : Differentiable ℝ f₃) (k₁ k₂ k₃ : ℝ) (x : E) (c : Fin (n+1)) :
    pd (fun y => k₁ * f₁ y + k₂ * f₂ y - k₃ * f₃ y) x c
      = k₁ * pd f₁ x c + k₂ * pd f₂ x c - k₃ * pd f₃ x c := by
  unfold pd
  have hA : DifferentiableAt ℝ (fun y => k₁ * f₁ y + k₂ * f₂ y) x :=
    ((h₁.const_mul k₁).add (h₂.const_mul k₂)) x
  have h₁' : DifferentiableAt ℝ (fun y => k₁ * f₁ y) x := (h₁.const_mul k₁) x
  have h₂' : DifferentiableAt ℝ (fun y => k₂ * f₂ y) x := (h₂.const_mul k₂) x
  have h₃' : DifferentiableAt ℝ (fun y => k₃ * f₃ y) x := (h₃.const_mul k₃) x
  rw [fderiv_fun_sub hA h₃', fderiv_fun_add h₁' h₂', fderiv_const_mul (h₁ x),
    fderiv_const_mul (h₂ x), fderiv_const_mul (h₃ x)]
  simp

/-- `∂_e Γ^a_bc` for `e^{2w} η`. -/
lemma pd_chr_conf (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (x : E) (a b c e' : Fin (n+1)) :
    pd (fun y => chr (conf w) y a b c) x e'
      = (if a = c then 1 else 0) * pd (fun y => pd w y b) x e'
        + (if a = b then 1 else 0) * pd (fun y => pd w y c) x e'
        - (if b = c then 1 else 0) * (sg a * sg b) * pd (fun y => pd w y a) x e' := by
  have hd : Differentiable ℝ w := hw.differentiable (by simp)
  have hfun : (fun y => chr (conf w) y a b c) = fun y =>
      (if a = c then 1 else 0) * pd w y b + (if a = b then 1 else 0) * pd w y c
        - (if b = c then 1 else 0) * (sg a * sg b) * pd w y a :=
    funext fun y => chr_conf w hd y a b c
  rw [hfun]
  exact pd_lin3 _ _ _ ((contDiff_pd hw b).differentiable (by simp))
    ((contDiff_pd hw c).differentiable (by simp)) ((contDiff_pd hw a).differentiable (by simp))
    _ _ _ x e'

/-- Ricci tensor of `e^{2w} η` in `n+1` dimensions:
`R_bd = −(n−1)(∂_b∂_d w − ∂_b w ∂_d w) − η_bd (□w + (n−1)|∂w|²)`. -/
lemma ricci_conf (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (x : E) (b d : Fin (n+1)) :
    ricci (conf w) x b d = -((n : ℝ) - 1) * (pd (fun y => pd w y d) x b - pd w x b * pd w x d)
      - (if b = d then sg b else 0) * (∑ c, sg c * pd (fun y => pd w y c) x c
          + ((n : ℝ) - 1) * ∑ c, sg c * pd w x c ^ 2) := by
  have hd : Differentiable ℝ w := hw.differentiable (by simp)
  simp only [ricci, riem, Matrix.of_apply, pd_chr_conf w hw]
  simp only [chr_conf w hd]
  by_cases hbd : b = d
  · subst hbd
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul, sub_mul, mul_add, mul_sub,
      ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sum_ite_irrel']
    have s1 : ∑ c, sg c * sg b * pd (fun y => pd w y c) x c
        = sg b * ∑ c, sg c * pd (fun y => pd w y c) x c := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    have s2 : ∑ c, pd w x c * (sg c * sg b * pd w x c) = sg b * ∑ c, sg c * pd w x c ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    have s3 : ∑ c, sg c * sg c * pd w x c * (sg c * sg b * pd w x c)
        = sg b * ∑ c, sg c * pd w x c ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by
        linear_combination (sg b * sg c * pd w x c ^ 2) * sg_sq c
    have s4 : ∑ c, sg c * sg b * pd w x c * pd w x c = sg b * ∑ c, sg c * pd w x c ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [s1, s2, s3, s4]
    push_cast
    ring_nf; simp only [sg_sq2, sg_pow4]; ring_nf
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul, sub_mul, mul_add, mul_sub,
      ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, hbd, Ne.symm hbd, ite_false, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, sum_ite_irrel']
    rw [pd_pd_comm w hw x b d]
    push_cast
    ring_nf; simp only [sg_sq2]; ring_nf

/-- Covariant divergence for `e^{2w} η`, for a field symmetric at `x`. -/
lemma covDiv_conf (w : E → ℝ) (hw : Differentiable ℝ w) (X : E → Mat) (x : E)
    (hX : (X x).IsSymm) (b : Fin (n+1)) :
    covDiv (conf w) X x b = Real.exp (-2 * w x) *
      (∑ a, sg a * pd (fun y => X y a b) x a + ((n : ℝ) - 1) * ∑ a, sg a * pd w x a * X x a b
        - pd w x b * ∑ a, sg a * X x a a) := by
  unfold covDiv
  simp only [conf_inv, chr_conf w hw, Matrix.smul_apply, smul_eq_mul, eta_sg]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul, sub_mul, mul_add, mul_sub,
      ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sum_ite_irrel']
  set K := Real.exp (-2 * w x)
  set SB := ∑ i, sg i * pd w x i * X x i b
  have t1 : ∑ a, K * sg a * pd (fun y => X y a b) x a = K * ∑ a, sg a * pd (fun y => X y a b) x a := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have t2 : ∑ a, K * sg a * (pd w x a * X x a b) = K * SB := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have t3 : ∑ a : Fin (n+1), K * sg a * ∑ i, sg i * sg a * pd w x i * X x i b = K * ((n : ℝ) + 1) * SB := by
    have : ∀ a : Fin (n+1), K * sg a * ∑ i, sg i * sg a * pd w x i * X x i b = K * SB := by
      intro a
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by linear_combination (K * sg i * pd w x i * X x i b) * sg_sq a
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have t4 : ∑ a, K * sg a * (pd w x b * X x a a) = K * (pd w x b * ∑ a, sg a * X x a a) := by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have t5 : K * sg b * ∑ i, sg i * sg b * pd w x i * X x b i = K * SB := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hX.apply i b]; linear_combination (K * sg i * pd w x i * X x i b) * sg_sq b
  rw [t1, t2, t3, t4, t5]
  ring

/-! ### Calculus of `pd` -/


lemma pd_add {f g : E → ℝ} {x : E} {c : Fin (n+1)}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    pd (fun y => f y + g y) x c = pd f x c + pd g x c := by
  simp [pd, fderiv_fun_add (hf x) (hg x)]

lemma pd_sub {f g : E → ℝ} {x : E} {c : Fin (n+1)}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    pd (fun y => f y - g y) x c = pd f x c - pd g x c := by
  simp [pd, fderiv_fun_sub (hf x) (hg x)]

lemma pd_mul {f g : E → ℝ} {x : E} {c : Fin (n+1)}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    pd (fun y => f y * g y) x c = pd f x c * g x + f x * pd g x c := by
  simp [pd, fderiv_fun_mul (hf x) (hg x)]; ring

lemma pd_const_mul {f : E → ℝ} {x : E} {c : Fin (n+1)} (k : ℝ) (hf : Differentiable ℝ f) :
    pd (fun y => k * f y) x c = k * pd f x c := by
  simp [pd, fderiv_const_mul (hf x)]

lemma pd_sq {f : E → ℝ} {x : E} {c : Fin (n+1)} (hf : Differentiable ℝ f) :
    pd (fun y => f y ^ 2) x c = 2 * f x * pd f x c := by
  simp only [sq]; rw [pd_mul hf hf]; ring

lemma pd_exp {f : E → ℝ} {x : E} {c : Fin (n+1)} (hf : Differentiable ℝ f) :
    pd (fun y => Real.exp (f y)) x c = Real.exp (f x) * pd f x c := by
  simp [pd, fderiv_exp (hf x)]

lemma pd_sum {x : E} {c : Fin (n+1)} (F : Fin (n+1) → E → ℝ)
    (hF : ∀ i, Differentiable ℝ (F i)) :
    pd (fun y => ∑ i, F i y) x c = ∑ i, pd (F i) x c := by
  unfold pd
  rw [fderiv_fun_sum (fun i _ => hF i x)]
  simp



attribute [fun_prop] contDiff_pd

lemma diff_of_smooth {f : E → ℝ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

/-- Third partial derivatives of a smooth function: `∂_a∂_a∂_b w = ∂_b∂_a∂_a w`. -/
lemma pd3_comm (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (x : E) (a b : Fin (n+1)) :
    pd (fun y => pd (fun z => pd w z b) y a) x a = pd (fun y => pd (fun z => pd w z a) y a) x b := by
  have : (fun y => pd (fun z => pd w z b) y a) = fun y => pd (fun z => pd w z a) y b :=
    funext fun y => pd_pd_comm w hw y b a
  rw [this]
  exact pd_pd_comm (fun z => pd w z a) (contDiff_pd hw a) x b a

/-- `∂_c R_ab` for `e^{2w} η`. -/
lemma pd_ricci_conf (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (x : E) (a b c : Fin (n+1)) :
    pd (fun y => ricci (conf w) y a b) x c =
      -((n : ℝ) - 1) * (pd (fun y => pd (fun z => pd w z b) y a) x c
          - (pd (fun y => pd w y a) x c * pd w x b + pd w x a * pd (fun y => pd w y b) x c))
      - (if a = b then sg a else 0) * (∑ e', sg e' * pd (fun y => pd (fun z => pd w z e') y e') x c
          + ((n : ℝ) - 1) * ∑ e', sg e' * (2 * pd w x e' * pd (fun y => pd w y e') x c)) := by
  have hfun : (fun y => ricci (conf w) y a b) = fun y =>
      -((n : ℝ) - 1) * (pd (fun y => pd w y b) y a - pd w y a * pd w y b)
      - (if a = b then sg a else 0) * (∑ e', sg e' * pd (fun y => pd w y e') y e'
          + ((n : ℝ) - 1) * ∑ e', sg e' * pd w y e' ^ 2) :=
    funext fun y => ricci_conf w hw y a b
  rw [hfun]
  have hd := diff_of_smooth hw
  rw [pd_sub (by fun_prop (disch := simp)) (by fun_prop (disch := simp)),
    pd_const_mul _ (by fun_prop (disch := simp)), pd_const_mul _ (by fun_prop (disch := simp)),
    pd_sub (by fun_prop (disch := simp)) (by fun_prop (disch := simp)),
    pd_mul (by fun_prop (disch := simp)) (by fun_prop (disch := simp)),
    pd_add (by fun_prop (disch := simp)) (by fun_prop (disch := simp)),
    pd_sum _ (fun _ => by fun_prop (disch := simp)), pd_const_mul _ (by fun_prop (disch := simp)),
    pd_sum _ (fun _ => by fun_prop (disch := simp))]
  have u1 : ∀ i, pd (fun y => sg i * pd (fun y => pd w y i) y i) x c
      = sg i * pd (fun y => pd (fun z => pd w z i) y i) x c := fun i =>
    pd_const_mul _ (diff_of_smooth (contDiff_pd (contDiff_pd hw i) i))
  have u2 : ∀ i, pd (fun y => sg i * pd w y i ^ 2) x c
      = sg i * (2 * pd w x i * pd (fun y => pd w y i) x c) := fun i => by
    rw [pd_const_mul _ (by fun_prop (disch := simp)), pd_sq (diff_of_smooth (contDiff_pd hw i))]
  simp only [u1, u2]

/-- Scalar curvature of `e^{2w} η`: `R = −n e^{−2w} (2□w + (n−1)|∂w|²)`. -/
lemma scal_conf (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (x : E) :
    scal (conf w) x = -(n : ℝ) * Real.exp (-2 * w x) *
      (2 * ∑ c, sg c * pd (fun y => pd w y c) x c + ((n : ℝ) - 1) * ∑ c, sg c * pd w x c ^ 2) := by
  simp only [scal, conf_inv, Matrix.smul_apply, smul_eq_mul, eta_sg, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ricci_conf w hw]
  set K := Real.exp (-2 * w x)
  set bx := ∑ c, sg c * pd (fun y => pd w y c) x c
  set sq := ∑ c, sg c * pd w x c ^ 2
  have h : ∀ b : Fin (n+1), K * sg b * (-((n : ℝ) - 1) * (pd (fun y => pd w y b) x b
      - pd w x b * pd w x b) - sg b * (bx + ((n : ℝ) - 1) * sq))
      = -((n : ℝ) - 1) * K * (sg b * pd (fun y => pd w y b) x b)
        + ((n : ℝ) - 1) * K * (sg b * pd w x b ^ 2) - K * (bx + ((n : ℝ) - 1) * sq) := by
    intro b; linear_combination (-K * (bx + ((n : ℝ) - 1) * sq)) * sg_sq b
  rw [Finset.sum_congr rfl fun b _ => h b]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- `∂_b R` for `e^{2w} η`. -/
lemma pd_scal_conf (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (x : E) (b : Fin (n+1)) :
    pd (scal (conf w)) x b = -(n : ℝ) * (Real.exp (-2 * w x) * (-2 * pd w x b) *
      (2 * ∑ c, sg c * pd (fun y => pd w y c) x c + ((n : ℝ) - 1) * ∑ c, sg c * pd w x c ^ 2)
      + Real.exp (-2 * w x) * (2 * ∑ c, sg c * pd (fun y => pd (fun z => pd w z c) y c) x b
        + ((n : ℝ) - 1) * ∑ c, sg c * (2 * pd w x c * pd (fun y => pd w y c) x b))) := by
  have hfun : scal (conf w) = fun y => -(n : ℝ) * (Real.exp (-2 * w y) *
      (2 * ∑ c, sg c * pd (fun y => pd w y c) y c + ((n : ℝ) - 1) * ∑ c, sg c * pd w y c ^ 2)) :=
    funext fun y => by rw [scal_conf w hw y]; ring
  rw [hfun]
  have hd := diff_of_smooth hw
  rw [pd_const_mul _ (by fun_prop (disch := simp)),
    pd_mul (by fun_prop (disch := simp)) (by fun_prop (disch := simp)),
    pd_exp (by fun_prop (disch := simp)), pd_const_mul _ hd,
    pd_add (by fun_prop (disch := simp)) (by fun_prop (disch := simp)),
    pd_const_mul _ (by fun_prop (disch := simp)), pd_const_mul _ (by fun_prop (disch := simp)),
    pd_sum _ (fun _ => by fun_prop (disch := simp)), pd_sum _ (fun _ => by fun_prop (disch := simp))]
  have u1 : ∀ i, pd (fun y => sg i * pd (fun y => pd w y i) y i) x b
      = sg i * pd (fun y => pd (fun z => pd w z i) y i) x b := fun i =>
    pd_const_mul _ (diff_of_smooth (contDiff_pd (contDiff_pd hw i) i))
  have u2 : ∀ i, pd (fun y => sg i * pd w y i ^ 2) x b
      = sg i * (2 * pd w x i * pd (fun y => pd w y i) x b) := fun i => by
    rw [pd_const_mul _ (by fun_prop (disch := simp)), pd_sq (diff_of_smooth (contDiff_pd hw i))]
  simp only [u1, u2]

lemma ricci_conf_symm (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (x : E) : (ricci (conf w) x).IsSymm := by
  ext a b
  simp only [Matrix.transpose_apply, ricci_conf w hw, pd_pd_comm w hw x a b]
  by_cases h : a = b
  · subst h; rfl
  · simp only [h, Ne.symm h, ite_false]; ring

/-- **Contracted Bianchi identity** for conformally flat metrics `e^{2w} η` in `n+1`
dimensions, `w` smooth: `∇^a R_ab = ½ ∂_b R`, with `Γ`, Riemann, Ricci and `R` all computed
from the metric by the coordinate formulas above. -/
theorem bianchi_conf (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (x : E) (b : Fin (n+1)) :
    covDiv (conf w) (ricci (conf w)) x b = (1/2 : ℝ) * pd (scal (conf w)) x b := by
  rw [covDiv_conf w (diff_of_smooth hw) _ x (ricci_conf_symm w hw x) b, pd_scal_conf w hw x b]
  simp only [pd_ricci_conf w hw]
  simp only [ricci_conf w hw]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, mul_add, mul_sub,
      ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  set A := ∑ e', sg e' * pd (fun y => pd (fun z => pd w z e') y e') x b with hA
  set B := ∑ e', sg e' * pd w x e' * pd (fun y => pd w y e') x b with hB
  set bx := ∑ c, sg c * pd (fun y => pd w y c) x c with hbx
  set sq := ∑ c, sg c * pd w x c ^ 2 with hsq
  set m : ℝ := (n : ℝ) - 1 with hm
  have v1 : ∑ a, sg a * (-m * pd (fun y => pd (fun z => pd w z b) y a) x a) = -m * A := by
    rw [hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [pd3_comm w hw x a b]; ring
  have v2 : ∑ a, sg a * (-m * (pd (fun y => pd w y a) x a * pd w x b)) = -m * pd w x b * bx := by
    rw [hbx, Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  have v3 : ∑ a, sg a * (-m * (pd w x a * pd (fun z => pd w z b) x a)) = -m * B := by
    rw [hB, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [pd_pd_comm w hw x b a]; ring
  have v4 : ∑ e', sg e' * (2 * pd w x e' * pd (fun y => pd w y e') x b) = 2 * B := by
    rw [hB, Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  have v5 : ∑ a, sg a * pd w x a * (-m * pd (fun z => pd w z b) x a) = -m * B := by
    rw [hB, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [pd_pd_comm w hw x b a]; ring
  have v6 : ∑ a, sg a * pd w x a * (-m * (pd w x a * pd w x b)) = -m * pd w x b * sq := by
    rw [hsq, Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  have v7 : ∑ a, sg a * (-m * pd (fun y => pd w y a) x a) = -m * bx := by
    rw [hbx, Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  have v8 : ∑ a, sg a * (-m * (pd w x a * pd w x a)) = -m * sq := by
    rw [hsq, Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  have hss : ∀ X : ℝ, ∑ a : Fin (n+1), sg a * (sg a * X) = ((n : ℝ) + 1) * X := by
    intro X
    have : ∀ a : Fin (n+1), sg a * (sg a * X) = X := fun a => by
      rw [← mul_assoc, sg_sq, one_mul]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  rw [v1, v2, v3, v4, v5, v6, v7, v8, hss, hss, hss]
  ring_nf
  simp only [sg_sq2]
  rw [hm]
  ring

/-! ### The Clausius chain on a conformally flat spacetime -/

open Flat in
/-- `φ ↦ φ e^{2w} η`. -/
noncomputable def mulC (w : E → ℝ) (hw : ContDiff ℝ ∞ w) : Ssub n →ₗ[ℝ] Vsub n where
  toFun φ := ⟨fun y => φ.1 y • conf w y, fun a b => by
    have hd := diff_of_smooth hw
    have hφ : Differentiable ℝ φ.1 := φ.2
    simp only [conf, Matrix.smul_apply, smul_eq_mul]
    fun_prop⟩
  map_add' φ ψ := by ext y a b; simp [add_mul]
  map_smul' c φ := by ext y a b; simp [mul_assoc]

open Flat in
/-- `X ↦ tr(g⁻¹ X)/(n+1)` for `g = e^{2w} η`. -/
noncomputable def trC (w : E → ℝ) (hw : ContDiff ℝ ∞ w) : Vsub n →ₗ[ℝ] Ssub n where
  toFun X := ⟨fun y => Matrix.trace ((conf w y)⁻¹ * X.1 y) / (n + 1), by
    show Differentiable ℝ _
    have hd := diff_of_smooth hw
    simp only [div_eq_mul_inv, conf_inv]
    apply Differentiable.mul_const
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    exact Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ =>
      (by fun_prop : Differentiable ℝ fun y => Real.exp (-2 * w y) * eta n i j).mul (X.2 j i)⟩
  map_add' X Y := by ext y; simp [Matrix.mul_add, Matrix.trace_add, add_div]
  map_smul' c X := by ext y; simp [Matrix.trace_smul, mul_div_assoc]

open Flat in
/-- The covariant divergence of `e^{2w} η`, linear on differentiable fields. -/
noncomputable def divC (w : E → ℝ) : Vsub n →ₗ[ℝ] (E → Fin (n+1) → ℝ) where
  toFun X := fun x b => covDiv (conf w) X.1 x b
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
    have h1 : ∑ d, chr (conf w) x d c a * (k * X.1 x d b) = k * ∑ d, chr (conf w) x d c a * X.1 x d b := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∑ d, chr (conf w) x d c b * (k * X.1 x a d) = k * ∑ d, chr (conf w) x d c b * X.1 x a d := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h1, h2]; ring

lemma conf_eq_P (w : E → ℝ) (x : E) :
    (Real.exp (w x) • (1 : Mat))ᵀ * eta n * (Real.exp (w x) • (1 : Mat)) = conf w x := by
  rw [conf, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, ← Real.exp_add]
  ring_nf

lemma ricci_conf_diff (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (a b : Fin (n+1)) :
    Differentiable ℝ fun y => ricci (conf w) y a b := by
  have hfun : (fun y => ricci (conf w) y a b) = fun y =>
      -((n : ℝ) - 1) * (pd (fun y => pd w y b) y a - pd w y a * pd w y b)
      - (if a = b then sg a else 0) * (∑ e', sg e' * pd (fun y => pd w y e') y e'
          + ((n : ℝ) - 1) * ∑ e', sg e' * pd w y e' ^ 2) :=
    funext fun y => ricci_conf w hw y a b
  rw [hfun]; fun_prop (disch := simp)

lemma scal_conf_diff (w : E → ℝ) (hw : ContDiff ℝ ∞ w) : Differentiable ℝ (scal (conf w)) := by
  have hfun : scal (conf w) = fun y => -(n : ℝ) * Real.exp (-2 * w y) *
      (2 * ∑ c, sg c * pd (fun y => pd w y c) y c + ((n : ℝ) - 1) * ∑ c, sg c * pd w y c ^ 2) :=
    funext fun y => scal_conf w hw y
  have hd := diff_of_smooth hw
  rw [hfun]; fun_prop (disch := simp)

open Flat in
/-- (Globally conformally flat metrics on all of `ℝ^(n+1)`.) **Clausius on a curved (conformally flat) spacetime.** Take the metric `g = e^{2w} η` on
`ℝ^(n+1)` with `w` smooth, its Christoffel symbols, Ricci tensor `Ric` and scalar curvature `R`
computed from `g`, and a symmetric stress tensor `T` with differentiable components and zero
covariant divergence. If `Ric(k,k) = κₑ T(k,k)` for every `g`-null `k` at every point (local
Clausius), then `Ric − ½ R g + Λ g = κₑ T` for one constant `Λ`. Proved by instantiating
`jacobson_chain`, with metric compatibility (`covDiv_smul_metric`) and the contracted Bianchi
identity (`bianchi_conf`) proved, not assumed. -/
theorem curved_clausius (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (T : E → Mat)
    (hTd : ∀ a b, Differentiable ℝ fun y => T y a b) (hTs : ∀ x, (T x).IsSymm)
    (hcons : ∀ x b, covDiv (conf w) T x b = 0) (κₑ : ℝ)
    (hClausius : ∀ x k, qf (conf w x) k = 0 → qf (ricci (conf w) x) k = κₑ * qf (T x) k) :
    ∃ Λ : ℝ, ∀ x, ricci (conf w) x - (1/2 : ℝ) • scal (conf w) x • conf w x + Λ • conf w x
      = κₑ • T x := by
  have hd := diff_of_smooth hw
  let P : E → Mat := fun x => Real.exp (w x) • (1 : Mat)
  have hP : ∀ x, IsUnit (P x).det := fun x => by
    simp only [P, Matrix.det_smul, Matrix.det_one, mul_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (Real.exp_pos _).ne')
  have hPg : ∀ x, (P x)ᵀ * eta n * P x = conf w x := conf_eq_P w
  have hgd : ∀ a b, Differentiable ℝ fun y => conf w y a b := fun a b => by
    simp only [conf, Matrix.smul_apply, smul_eq_mul]; fun_prop
  let Tv : Vsub n := ⟨T, hTd⟩
  let Ric : Vsub n := ⟨ricci (conf w), ricci_conf_diff w hw⟩
  let Rs : Ssub n := ⟨scal (conf w), scal_conf_diff w hw⟩
  obtain ⟨Λ, hΛ⟩ := @jacobson_chain n (Fin (n+1) → ℝ) (Vsub n) (Ssub n)
    ((Fin (n+1) → ℝ) → Fin (n+1) → ℝ) _ _ _ _ _ _ P hP
    (Vsub n).subtype Subtype.val_injective (Ssub n).subtype
    (mulC w hw) (fun φ x => by simp [mulC, hPg]) (trC w hw) (fun X x => by simp [trC, hPg])
    one (divC w) dL
    (fun φ => by
      ext x b
      exact covDiv_smul_metric (conf w) (conf_symm w) (conf_det w) hgd φ.1 φ.2 x b)
    (fun φ hφ => by
      refine ⟨φ.1 0, ?_⟩
      have hconst := is_const_of_fderiv_eq_zero φ.2 (fun x => clm_eq_zero_of_basis _
        fun b => congrFun (congrFun hφ x) b)
      ext x; simp [Flat.one, hconst x 0])
    Ric Tv Rs κₑ (fun x => ricci_conf_symm w hw x) hTs
    (fun x k hk => by rw [hPg] at hk; exact hClausius x k hk)
    (by ext x b; exact bianchi_conf w hw x b) (by ext x b; exact hcons x b)
  refine ⟨Λ, fun x => ?_⟩
  have := congrArg (fun v : Vsub n => v.1 x) hΛ
  simpa [mulC, Flat.one, Tv, Ric, Rs, smul_smul] using this

open Flat in
/-- **Equilibrium (2016 chain) on a conformally flat spacetime.** For `g = e^{2w} η` with `w`
smooth, a conserved symmetric stress tensor `T` and a scalar `L`, both differentiable: if
`G(u,u) − L(x) = κₑ T(u,u)` for every unit timelike `u` (`g(u,u) = −1`) at every point, where
`G = Ric − ½ R g` is computed from `g`, then `G + L g = κₑ T` and `L` is constant. -/
theorem curved_equilibrium (w : E → ℝ) (hw : ContDiff ℝ ∞ w) (T : E → Mat)
    (hTd : ∀ a b, Differentiable ℝ fun y => T y a b) (hTs : ∀ x, (T x).IsSymm)
    (hcons : ∀ x b, covDiv (conf w) T x b = 0) (L : E → ℝ) (hL : Differentiable ℝ L) (κₑ : ℝ)
    (hEq : ∀ x u, qf (conf w x) u = -1 →
      qf (ricci (conf w) x - (1/2 : ℝ) • scal (conf w) x • conf w x) u - L x = κₑ * qf (T x) u) :
    (∀ x, ricci (conf w) x - (1/2 : ℝ) • scal (conf w) x • conf w x + L x • conf w x = κₑ • T x)
      ∧ ∃ c : ℝ, ∀ x, L x = c := by
  let P : E → Mat := fun x => Real.exp (w x) • (1 : Mat)
  have hP : ∀ x, IsUnit (P x).det := fun x => by
    simp only [P, Matrix.det_smul, Matrix.det_one, mul_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (Real.exp_pos _).ne')
  have hPg : ∀ x, (P x)ᵀ * eta n * P x = conf w x := conf_eq_P w
  have hgd : ∀ a b, Differentiable ℝ fun y => conf w y a b := fun a b => by
    have hd := diff_of_smooth hw
    simp only [conf, Matrix.smul_apply, smul_eq_mul]; fun_prop
  have hcompat : ∀ φ, divC w (mulC w hw φ) = dL φ := fun φ => by
    ext x b
    exact covDiv_smul_metric (conf w) (conf_symm w) (conf_det w) hgd φ.1 φ.2 x b
  let Tv : Vsub n := ⟨T, hTd⟩
  let Ric : Vsub n := ⟨ricci (conf w), ricci_conf_diff w hw⟩
  let Rs : Ssub n := ⟨scal (conf w), scal_conf_diff w hw⟩
  let Lv : Ssub n := ⟨L, hL⟩
  have hRic : divC w Ric = (1/2 : ℝ) • dL Rs := by ext x b; exact bianchi_conf w hw x b
  have hG : divC w (Ric - (1/2 : ℝ) • mulC w hw Rs) = 0 := by
    rw [map_sub, map_smul, hcompat, hRic, sub_self]
  have hGeval : ∀ x, (Ric - (1/2 : ℝ) • mulC w hw Rs).1 x
      = ricci (conf w) x - (1/2 : ℝ) • scal (conf w) x • conf w x := fun x => by
    simp [mulC, Ric, Rs]
  obtain ⟨hfield, c, hc⟩ := @equilibrium_chain n (Fin (n+1) → ℝ) (Vsub n) (Ssub n)
    ((Fin (n+1) → ℝ) → Fin (n+1) → ℝ) _ _ _ _ _ _ P hP
    (Vsub n).subtype Subtype.val_injective (Ssub n).subtype
    (mulC w hw) (fun φ x => by simp [mulC, hPg]) Flat.one (divC w) dL hcompat
    (fun φ hφ => by
      refine ⟨φ.1 0, ?_⟩
      have hconst := is_const_of_fderiv_eq_zero φ.2 (fun x => clm_eq_zero_of_basis _
        fun b => congrFun (congrFun hφ x) b)
      ext x; simp [Flat.one, hconst x 0])
    (Ric - (1/2 : ℝ) • mulC w hw Rs) Tv Lv κₑ
    (fun x => by
      rw [Submodule.subtype_apply, hGeval]
      exact (ricci_conf_symm w hw x).sub (((conf_symm w x).smul _).smul _)) hTs
    (fun x u hu => by
      rw [hPg] at hu
      rw [Submodule.subtype_apply, hGeval]
      exact hEq x u hu)
    hG (by ext x b; exact hcons x b)
  refine ⟨fun x => ?_, c, fun x => ?_⟩
  · have := congrArg (fun v : Vsub n => v.1 x) hfield
    simp only [Submodule.coe_add, Pi.add_apply, hGeval] at this
    simpa [mulC, Lv, Tv] using this
  · have := congrArg (fun v : Ssub n => v.1 x) hc
    simpa [Flat.one, Lv] using this

end EntEq.Curved
