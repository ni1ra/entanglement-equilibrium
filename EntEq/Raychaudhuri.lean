/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Raychaudhuri's equation from the metric, in the coordinates of `CurvedCoords`.

  For a vector field `K` write `∇_b K^a = ∂_b K^a + Γ^a_bc K^c`, `θ = ∇_a K^a` (the expansion)
  and `A^a = K^b ∇_b K^a` (the acceleration). Then, at every point and for every smooth `K` on
  every smooth metric,
      K^c ∂_c θ = ∇_a A^a − (∇_a K^b)(∇_b K^a) − R_ab K^a K^b,
  the trace form of Raychaudhuri's equation (`raychaudhuri`). The index algebra
  (`raychaudhuri_alg`) uses only `Γ^a_bc = Γ^a_cb` and `∂_c∂_b = ∂_b∂_c`, so it holds for any
  torsion-free connection. For a hypersurface-orthogonal null geodesic congruence the middle term
  is `θ²/(d−2) + σ² `; at a point where `∇K = 0` and the congruence is geodesic to first order it
  vanishes and `dθ/ds = −R(K,K)` (`raychaudhuri_bifurcation`), which is what the 1995 chain uses.
-/
import EntEq.BianchiGeneral

open Matrix

namespace EntEq.Curved

variable {n : ℕ}

local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

open scoped ContDiff

/-! ### Index algebra -/

section
variable {α : Type*} [Fintype α]
lemma s3_12 (f : α → α → α → ℝ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c :=
  Finset.sum_comm
lemma s3_23 (f : α → α → α → ℝ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm
lemma s4_12 (f : α → α → α → α → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := Finset.sum_comm
lemma s4_23 (f : α → α → α → α → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm
lemma s4_34 (f : α → α → α → α → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
end

/-- **Raychaudhuri's identity as index algebra.** With `k = K(x)`, `dK p q = ∂_p K^q`,
`ddK c b a = ∂_c∂_b K^a`, `Γ a b c = Γ^a_bc` and `dΓ e a b c = ∂_e Γ^a_bc` at one point:
`K^c ∂_c θ = ∇_a A^a − (∇_a K^b)(∇_b K^a) − Ric(K,K)`, each side written out in components. -/
theorem raychaudhuri_alg (k : Fin (n+1) → ℝ) (dK : Fin (n+1) → Fin (n+1) → ℝ)
    (ddK : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ) (Γ : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (dΓ : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdd : ∀ c b a, ddK c b a = ddK b c a) :
    ∑ c, k c * ∑ a, (ddK c a a + ∑ d, (dΓ c a a d * k d + Γ a a d * dK c d))
    = ∑ a, (∑ b, (dK a b * (dK b a + ∑ c, Γ a b c * k c)
          + k b * (ddK a b a + ∑ c, (dΓ a a b c * k c + Γ a b c * dK a c)))
        + ∑ c, Γ a a c * ∑ b, k b * (dK b c + ∑ f, Γ c b f * k f))
    - ∑ a, ∑ b, (dK a b + ∑ c, Γ b a c * k c) * (dK b a + ∑ c, Γ a b c * k c)
    - ∑ b, k b * ∑ d, (∑ a, (dΓ a a d b - dΓ d a a b + ∑ f, Γ a a f * Γ f d b
        - ∑ f, Γ a d f * Γ f a b)) * k d := by
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib, mul_sub,
    sub_mul, Finset.sum_sub_distrib]
  have e1 : ∑ x, ∑ i, k x * ddK x i i = ∑ x, ∑ x_1, k x_1 * ddK x x_1 x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [hdd c a a]
  have e2 : ∑ x, ∑ x_1, ∑ i, k x * (dΓ x x_1 x_1 i * k i)
      = ∑ x, ∑ x_1, ∑ i, k x * (dΓ x_1 i i x * k x_1) := by
    refine (s3_23 _).trans ((s3_12 _).trans ?_)
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ x, ∑ x_1, ∑ i, k x * (Γ x_1 x_1 i * dK x i)
      = ∑ x, ∑ x_1, ∑ i, Γ x x x_1 * (k i * dK i x_1) := by
    refine (s3_12 _).trans ((s3_23 _).trans ?_)
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e4 : ∑ x, ∑ x_1, ∑ i, k x_1 * (dΓ x x x_1 i * k i)
      = ∑ x, ∑ x_1, ∑ i, k x * (dΓ i i x_1 x * k x_1) := by
    refine (s3_12 _).trans ((s3_23 _).trans ((s3_12 _).trans ?_))
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e5 : ∑ x, ∑ x_1, ∑ i, k x_1 * (Γ x x_1 i * dK x i)
      = ∑ x, ∑ x_1, ∑ i, Γ x_1 x i * k i * dK x_1 x := by
    refine (s3_23 _).trans ((s3_12 _).trans ?_)
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by rw [hΓ a b c]; ring
  have e6 : ∑ x, ∑ x_1, ∑ x_2, ∑ i, Γ x x x_1 * (k x_2 * (Γ x_1 x_2 i * k i))
      = ∑ x, ∑ x_1, ∑ x_2, ∑ i, k x * (Γ x_2 x_2 i * Γ i x_1 x * k x_1) := by
    refine (s4_34 _).trans ((s4_23 _).trans ((s4_12 _).trans ((s4_34 _).trans
      ((s4_23 _).trans ?_))))
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e7 : ∑ x, ∑ x_1, ∑ x_2, ∑ i, Γ x_1 x i * k i * (Γ x x_1 x_2 * k x_2)
      = ∑ x, ∑ x_1, ∑ x_2, ∑ i, k x * (Γ x_2 x_1 i * Γ i x_2 x * k x_1) := by
    refine (s4_34 _).trans ((s4_23 _).trans ((s4_12 _).trans ((s4_34 _).trans
      ((s4_23 _).trans ?_))))
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by
        rw [hΓ q p s]; ring
  linarith [e1, e2, e3, e4, e5, e6, e7]

/-! ### Vector fields, expansion, acceleration -/

/-- A vector field with smooth components. -/
def SmV (K : E → E) : Prop := ∀ a, ContDiff ℝ ∞ fun y => K y a

/-- `∇_b K^a = ∂_b K^a + Γ^a_bc K^c`. -/
noncomputable def nabV (g : E → Mat) (K : E → E) (y : E) (b a : Fin (n+1)) : ℝ :=
  pd (fun z => K z a) y b + ∑ c, chr g y a b c * K y c

/-- The expansion `θ = ∇_a K^a`. -/
noncomputable def expansion (g : E → Mat) (K : E → E) (y : E) : ℝ := ∑ a, nabV g K y a a

/-- The acceleration `A^a = K^b ∇_b K^a`. -/
noncomputable def accel (g : E → Mat) (K : E → E) (y : E) : E := fun a => ∑ b, K y b * nabV g K y b a

/-- The divergence `∇_a V^a = ∂_a V^a + Γ^a_ac V^c`. -/
noncomputable def divV (g : E → Mat) (V : E → E) (y : E) : ℝ :=
  ∑ a, (pd (fun z => V z a) y a + ∑ c, chr g y a a c * V y c)


lemma nabV_smooth {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) {K : E → E} (hK : SmV K) (b a : Fin (n+1)) : ContDiff ℝ ∞ fun y => nabV g K y b a :=
  (contDiff_pd (hK a) b).add (ContDiff.sum fun c _ => (chr_smooth hg hdet a b c).mul (hK c))

lemma expansion_smooth {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) {K : E → E} (hK : SmV K) : ContDiff ℝ ∞ (expansion g K) :=
  ContDiff.sum fun a _ => nabV_smooth hg hdet hK a a

lemma accel_smooth {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) {K : E → E} (hK : SmV K) (a : Fin (n+1)) : ContDiff ℝ ∞ fun y => accel g K y a :=
  ContDiff.sum fun b _ => (hK b).mul (nabV_smooth hg hdet hK b a)

/-- `∂_c θ` in components. -/
lemma pd_expansion {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) {K : E → E} (hK : SmV K) (x : E) (c : Fin (n+1)) :
    pd (expansion g K) x c = ∑ a, (pd (fun y => pd (fun z => K z a) y a) x c
      + ∑ d, (pd (fun y => chr g y a a d) x c * K x d
        + chr g x a a d * pd (fun z => K z d) x c)) := by
  unfold expansion
  rw [pd_sum _ fun a => diff_of_smooth (nabV_smooth hg hdet hK a a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold nabV
  rw [pd_add (diff_of_smooth (contDiff_pd (hK a) a))
    (diff_of_smooth (ContDiff.sum fun c _ => (chr_smooth hg hdet a a c).mul (hK c))),
    pd_sum _ fun d => diff_of_smooth ((chr_smooth hg hdet a a d).mul (hK d))]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pd_mul (diff_of_smooth (chr_smooth hg hdet a a d)) (diff_of_smooth (hK d))]

/-- `∂_e (∇_b K^a)` in components. -/
lemma pd_nabV {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) {K : E → E} (hK : SmV K) (x : E) (e' b a : Fin (n+1)) :
    pd (fun y => nabV g K y b a) x e' = pd (fun y => pd (fun z => K z a) y b) x e'
      + ∑ c, (pd (fun y => chr g y a b c) x e' * K x c
        + chr g x a b c * pd (fun z => K z c) x e') := by
  unfold nabV
  rw [pd_add (diff_of_smooth (contDiff_pd (hK a) b))
    (diff_of_smooth (ContDiff.sum fun c _ => (chr_smooth hg hdet a b c).mul (hK c))),
    pd_sum _ fun d => diff_of_smooth ((chr_smooth hg hdet a b d).mul (hK d))]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pd_mul (diff_of_smooth (chr_smooth hg hdet a b d)) (diff_of_smooth (hK d))]

/-- `∂_e A^a` in components. -/
lemma pd_accel {g : E → Mat} (hg : Sm g) (hdet : ∀ y, IsUnit (g y).det) {K : E → E} (hK : SmV K) (x : E) (e' a : Fin (n+1)) :
    pd (fun y => accel g K y a) x e' = ∑ b, (pd (fun z => K z b) x e' * nabV g K x b a
      + K x b * pd (fun y => nabV g K y b a) x e') := by
  unfold accel
  rw [pd_sum _ fun b => diff_of_smooth ((hK b).mul (nabV_smooth hg hdet hK b a))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pd_mul (diff_of_smooth (hK b)) (diff_of_smooth (nabV_smooth hg hdet hK b a))]

/-- **Raychaudhuri's equation** (trace form), for every smooth vector field `K` on every smooth
metric, at every point: `K^c ∂_c θ = ∇_a A^a − (∇_a K^b)(∇_b K^a) − R_ab K^a K^b`. -/
theorem raychaudhuri (g : E → Mat) (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (K : E → E) (hK : SmV K) (x : E) :
    ∑ c, K x c * pd (expansion g K) x c
      = divV g (accel g K) x - ∑ a, ∑ b, nabV g K x a b * nabV g K x b a
        - qf (ricci g x) (K x) := by
  have hL : ∀ c, pd (expansion g K) x c = _ := pd_expansion hg hdet hK x
  simp only [hL]
  unfold divV
  simp only [pd_accel hg hdet hK x, pd_nabV hg hdet hK x]
  unfold qf ricci riem accel nabV
  simp only [dotProduct, mulVec, Matrix.of_apply]
  exact raychaudhuri_alg (K x) (fun p q => pd (fun z => K z q) x p)
    (fun c b a => pd (fun y => pd (fun z => K z a) y b) x c) (fun a b c => chr g x a b c)
    (fun e' a b c => pd (fun y => chr g y a b c) x e') (fun a b c => chr_comm g hs x a b c)
    (fun c b a => pd_pd_comm _ (hK a) x b c)

/-- **Raychaudhuri at the bifurcation point.** If `∇K = 0` at `x` (expansion, shear and twist
all vanish there) and `∂A = 0` at `x` (geodesic to first order), then `K^c ∂_c θ = −R(K,K)`. -/
theorem raychaudhuri_bifurcation (g : E → Mat) (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (K : E → E) (hK : SmV K) (x : E)
    (hB : ∀ b a, nabV g K x b a = 0) (hA : ∀ c a, pd (fun y => accel g K y a) x c = 0) :
    ∑ c, K x c * pd (expansion g K) x c = -qf (ricci g x) (K x) := by
  rw [raychaudhuri g hg hs hdet K hK x]
  have h0 : ∀ a, accel g K x a = 0 := fun a => by simp [accel, hB]
  simp [divV, hA, h0, hB]

end EntEq.Curved
