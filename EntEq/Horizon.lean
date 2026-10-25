/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The 1995 capstone without Raychaudhuri as a hypothesis.

  A *local horizon* through `x` with generator `k` (`IsLocalHorizon`) is a smooth vector field
  `K` with `K(x) = k`, `∇K = 0` at `x` (expansion, shear and twist vanish at the bifurcation
  point) and `∂(K^b∇_b K) = 0` at `x` (the generators are geodesic to first order). These are
  conditions on the 2-jet of `K` at `x`, which is all the leading-order Clausius relation sees.

  * `horizon_exists`: for every point and every vector `k` there is such a `K` (an explicit
    quadratic field), so a premise quantified over all local horizons is never vacuous.
  * `clausius_to_einstein_geom`: if Clausius holds, to `o(ε²)`, for every local horizon and
    every curve leaving `x` along `k` — with `θ` the expansion of `K` itself and the area change
    `−∫θ` — then Einstein's equation holds with a constant `Λ`. Raychaudhuri is proved
    (`raychaudhuri_bifurcation`), not assumed.
  * `einstein_to_clausius_geom`: the converse, so the premise is equivalent to Einstein's
    equation (the referee's M1 still applies: this is a reformulation, now with only
    thermodynamic words in the premise).
-/
import EntEq.Raychaudhuri
import EntEq.AreaClausius

open Filter Topology Matrix

namespace EntEq.Curved

variable {n : ℕ}

local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

open scoped ContDiff

/-- A local horizon through `x` with generator `k`, to the order the leading-order Clausius
relation probes. -/
def IsLocalHorizon (g : E → Mat) (x k : E) (K : E → E) : Prop :=
  SmV K ∧ K x = k ∧ (∀ b a, nabV g K x b a = 0) ∧ (∀ c a, pd (fun y => accel g K y a) x c = 0)

/-! ### Coordinate calculus -/

lemma pd_coord (x : E) (b c : Fin (n+1)) : pd (fun y : E => y c) x b = if b = c then 1 else 0 := by
  unfold pd
  rw [(hasFDerivAt_apply c x).fderiv]
  simp [Pi.single_apply, eq_comm]

lemma diff_coord (c : Fin (n+1)) : Differentiable ℝ fun y : E => y c := differentiable_apply c

lemma pd_z (x y : E) (b c : Fin (n+1)) : pd (fun z : E => z c - x c) y b = if b = c then 1 else 0 := by
  rw [pd_sub (diff_coord c) (differentiable_const _), pd_coord, pd_const, sub_zero]

lemma diff_z (x : E) (c : Fin (n+1)) : Differentiable ℝ fun z : E => z c - x c :=
  (diff_coord c).sub (differentiable_const _)

lemma contDiff_z (x : E) (c : Fin (n+1)) : ContDiff ℝ ∞ fun z : E => z c - x c := by
  fun_prop

/-- `fderiv f x v = Σ_c v^c ∂_c f`. -/
lemma fderiv_eq_sum_pd (f : E → ℝ) (x v : E) : fderiv ℝ f x v = ∑ c, v c * pd f x c := by
  have hv : v = ∑ c, v c • e c := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp [pd, map_smul]

/-- Derivative of a quadratic polynomial centred at `x`. -/
lemma pd_quad (x : E) (c0 : ℝ) (L : Fin (n+1) → ℝ) (Q : Fin (n+1) → Fin (n+1) → ℝ) (y : E)
    (b : Fin (n+1)) :
    pd (fun z : E => c0 + ∑ c, L c * (z c - x c) + ∑ c, ∑ d, Q c d * (z c - x c) * (z d - x d))
      y b = L b + (∑ d, Q b d * (y d - x d) + ∑ c, Q c b * (y c - x c)) := by
  have hz := diff_z x
  have hA : Differentiable ℝ (fun z : E => ∑ c, L c * (z c - x c)) :=
    Differentiable.fun_sum fun c _ => (hz c).const_mul (L c)
  have hB : Differentiable ℝ (fun z : E => ∑ c, ∑ d, Q c d * (z c - x c) * (z d - x d)) :=
    Differentiable.fun_sum fun c _ => Differentiable.fun_sum fun d _ =>
      ((hz c).const_mul (Q c d)).mul (hz d)
  rw [pd_add (f := fun z : E => c0 + ∑ c, L c * (z c - x c))
      (g := fun z : E => ∑ c, ∑ d, Q c d * (z c - x c) * (z d - x d))
      ((differentiable_const c0).add hA) hB,
    pd_add (f := fun _ : E => c0) (g := fun z : E => ∑ c, L c * (z c - x c))
      (differentiable_const c0) hA, pd_const, zero_add]
  have e1 : pd (fun z : E => ∑ c, L c * (z c - x c)) y b = L b := by
    rw [pd_sum (fun c z => L c * (z c - x c)) (fun c => (hz c).const_mul (L c))]
    calc ∑ c, pd (fun z => L c * (z c - x c)) y b = ∑ c, L c * (if b = c then 1 else 0) :=
          Finset.sum_congr rfl fun c _ => by rw [pd_const_mul (L c) (hz c), pd_z]
      _ = L b := by simp
  have e2 : pd (fun z : E => ∑ c, ∑ d, Q c d * (z c - x c) * (z d - x d)) y b
      = ∑ d, Q b d * (y d - x d) + ∑ c, Q c b * (y c - x c) := by
    rw [pd_sum (fun c z => ∑ d, Q c d * (z c - x c) * (z d - x d))
      (fun c => Differentiable.fun_sum fun d _ => ((hz c).const_mul (Q c d)).mul (hz d))]
    have h : ∀ c, pd (fun z : E => ∑ d, Q c d * (z c - x c) * (z d - x d)) y b
        = (if b = c then ∑ d, Q c d * (y d - x d) else 0) + Q c b * (y c - x c) := fun c => by
      rw [pd_sum (fun d z => Q c d * (z c - x c) * (z d - x d))
        (fun d => ((hz c).const_mul (Q c d)).mul (hz d))]
      have : ∀ d, pd (fun z : E => Q c d * (z c - x c) * (z d - x d)) y b
          = (if b = c then Q c d * (y d - x d) else 0)
            + (if b = d then Q c d * (y c - x c) else 0) := fun d => by
        rw [pd_mul ((hz c).const_mul (Q c d)) (hz d), pd_const_mul (Q c d) (hz c), pd_z, pd_z]
        split_ifs <;> ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        sum_ite_irrel' (b = c)]
    simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [e1, e2]

/-- Derivative of an affine function centred at `x`. -/
lemma pd_affine (x : E) (c0 : ℝ) (L : Fin (n+1) → ℝ) (y : E) (b : Fin (n+1)) :
    pd (fun z : E => c0 + ∑ c, L c * (z c - x c)) y b = L b := by
  have h := pd_quad x c0 L (fun _ _ => 0) y b
  simp only [zero_mul, Finset.sum_const_zero, add_zero] at h
  exact h

/-! ### The witness -/


/-- `D^a_d`: the first-order acceleration of the linear field, to be cancelled. -/
noncomputable def hzD (g : E → Mat) (x k : E) (a d : Fin (n+1)) : ℝ :=
  ∑ b, ∑ c, k b * pd (fun y => chr g y a b c) x d * k c
    - ∑ b, ∑ c, ∑ f, k b * chr g x a b c * chr g x c f d * k f

/-- `w_b = k^b / |k|²` (Euclidean), so `w·k = 1` when `k ≠ 0`. -/
noncomputable def hzW (k : E) (b : Fin (n+1)) : ℝ := k b / ∑ f, k f ^ 2

/-- Second-derivative coefficients `C^a_bd`, symmetric in `b, d`, with `k^b C^a_bd = −D^a_d`. -/
noncomputable def hzC (g : E → Mat) (x k : E) (a b d : Fin (n+1)) : ℝ :=
  -(hzD g x k a d * hzW k b + hzD g x k a b * hzW k d)
    + (∑ f, hzD g x k a f * k f) * hzW k b * hzW k d

/-- The witness: `K^a(y) = k^a − Γ^a_bc(x) k^b z^c + ½ C^a_cd z^c z^d`, `z = y − x`. -/
noncomputable def hzK (g : E → Mat) (x k : E) : E → E := fun y a =>
  k a + ∑ c, (-∑ b, chr g x a b c * k b) * (y c - x c)
    + ∑ c, ∑ d, (hzC g x k a c d / 2) * (y c - x c) * (y d - x d)

lemma hzC_symm (g : E → Mat) (x k : E) (a b d : Fin (n+1)) : hzC g x k a b d = hzC g x k a d b := by
  unfold hzC; ring

lemma hzC_contract (g : E → Mat) (x k : E) (a d : Fin (n+1)) : ∑ b, k b * hzC g x k a b d = -hzD g x k a d := by
  by_cases hk : ∑ f, k f ^ 2 = 0
  · have hk0 : ∀ f, k f = 0 := fun f => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (k i))).mp hk f
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    simp [hzD, hk0]
  · have hs : ∑ b, k b * hzW k b = 1 := by
      unfold hzW
      have : ∑ b, k b * (k b / ∑ f, k f ^ 2) = (∑ b, k b ^ 2) / ∑ f, k f ^ 2 := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun b _ => by ring
      rw [this]; exact div_self hk
    unfold hzC
    simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have h1 : ∑ b, k b * (hzD g x k a d * hzW k b) = hzD g x k a d := by
      have : ∑ b, k b * (hzD g x k a d * hzW k b) = hzD g x k a d * ∑ b, k b * hzW k b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, hs, mul_one]
    have h2 : ∑ b, k b * (hzD g x k a b * hzW k d) = (∑ f, hzD g x k a f * k f) * hzW k d := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring
    have h3 : ∑ b, k b * ((∑ f, hzD g x k a f * k f) * hzW k b * hzW k d)
        = (∑ f, hzD g x k a f * k f) * hzW k d := by
      have : ∀ b, k b * ((∑ f, hzD g x k a f * k f) * hzW k b * hzW k d)
          = ((∑ f, hzD g x k a f * k f) * hzW k d) * (k b * hzW k b) := fun b => by ring
      simp only [this, ← Finset.mul_sum, hs, mul_one]
    rw [h1, h2, h3]; ring

lemma hzK_smooth (g : E → Mat) (x k : E) : SmV (hzK g x k) := fun a => by
  unfold hzK
  exact (contDiff_const.add (ContDiff.sum fun c _ =>
    contDiff_const.mul (contDiff_z x c))).add (ContDiff.sum fun c _ => ContDiff.sum fun d _ =>
      (contDiff_const.mul (contDiff_z x c)).mul (contDiff_z x d))

lemma hzK_at (g : E → Mat) (x k : E) : hzK g x k x = k := by
  funext a; simp [hzK]

/-- `∂_b K^a` everywhere. -/
lemma pd_hzK (g : E → Mat) (x k : E) (y : E) (b a : Fin (n+1)) :
    pd (fun z => hzK g x k z a) y b = -∑ b', chr g x a b' b * k b'
      + (∑ d, (hzC g x k a b d / 2) * (y d - x d) + ∑ c, (hzC g x k a c b / 2) * (y c - x c)) := by
  simp only [hzK]
  exact pd_quad x _ _ _ y b

/-- `∂_d∂_b K^a = C^a_bd`. -/
lemma pd_pd_hzK (g : E → Mat) (x k : E) (b a d : Fin (n+1)) :
    pd (fun y => pd (fun z => hzK g x k z a) y b) x d = hzC g x k a b d := by
  have hf : (fun y => pd (fun z => hzK g x k z a) y b) = fun z : E =>
      (-∑ b', chr g x a b' b * k b')
        + ∑ c, (hzC g x k a b c / 2 + hzC g x k a c b / 2) * (z c - x c) := by
    funext z
    rw [pd_hzK, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hf, pd_affine, hzC_symm g x k a d b]; ring

/-- **Local horizons exist** through every point along every vector, on every smooth metric. -/
theorem horizon_exists (g : E → Mat) (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (x k : E) : IsLocalHorizon g x k (hzK g x k) := by
  have hK := hzK_smooth g x k
  have hdk : ∀ c' c, pd (fun z => hzK g x k z c') x c = -∑ b', chr g x c' b' c * k b' :=
    fun c' c => by rw [pd_hzK]; simp
  have hB : ∀ b a, nabV g (hzK g x k) x b a = 0 := fun b a => by
    unfold nabV
    rw [hdk, hzK_at, neg_add_eq_zero]
    exact Finset.sum_congr rfl fun c _ => by rw [chr_comm g hs x a c b]
  refine ⟨hK, hzK_at g x k, hB, fun c a => ?_⟩
  rw [pd_accel hg hdet hK]
  have hterm : ∀ b, pd (fun z => hzK g x k z b) x c * nabV g (hzK g x k) x b a
      + hzK g x k x b * pd (fun y => nabV g (hzK g x k) y b a) x c
      = k b * hzC g x k a b c + k b * ∑ c', (pd (fun y => chr g y a b c') x c * k c'
        + chr g x a b c' * (-∑ f, chr g x c' f c * k f)) := fun b => by
    rw [hB, mul_zero, zero_add, hzK_at, pd_nabV hg hdet hK, pd_pd_hzK, hzK_at, mul_add]
    simp only [hdk]
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_add_distrib, hzC_contract]
  unfold hzD
  have hrest : ∑ b, k b * ∑ c', (pd (fun y => chr g y a b c') x c * k c'
        + chr g x a b c' * (-∑ f, chr g x c' f c * k f))
      = ∑ b, ∑ c', k b * pd (fun y => chr g y a b c') x c * k c'
        - ∑ b, ∑ c', ∑ f, k b * chr g x a b c' * chr g x c' f c * k f := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [mul_add, mul_neg, mul_neg, Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg]
    congr 1
    · ring
    · congr 1; exact Finset.sum_congr rfl fun f _ => by ring
  rw [hrest]; ring

/-- **Every local horizon focuses the same way.** For any local horizon through `x` with
generator `k`, `dθ/ds = −Ric(k,k)` at `x`: the leading-order Clausius relation cannot tell
local horizons apart, so quantifying it over all of them or over one is the same premise. -/
theorem horizon_focusing (g : E → Mat) (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (x k : E) (K : E → E) (hH : IsLocalHorizon g x k K) :
    fderiv ℝ (expansion g K) x k = -qf (ricci g x) k := by
  obtain ⟨hK, hKx, hB, hA⟩ := hH
  rw [fderiv_eq_sum_pd, ← hKx]
  exact raychaudhuri_bifurcation g hg hs hdet K hK x hB hA

lemma expansion_zero (g : E → Mat) (x k : E) (K : E → E) (hH : IsLocalHorizon g x k K) :
    expansion g K x = 0 := by
  simp [expansion, hH.2.2.1]

/-- Along any curve `γ` leaving `x` with velocity `k`, `θ(γ(s))` has derivative `−Ric(k,k)`
at `s = 0`. -/
lemma expansion_along (g : E → Mat) (hg : Sm g) (hs : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (x k : E) (K : E → E) (hH : IsLocalHorizon g x k K)
    (γ : ℝ → E) (hγ0 : γ 0 = x) (hγd : HasDerivAt γ k 0) :
    HasDerivAt (fun s => expansion g K (γ s)) (-qf (ricci g x) k) 0 := by
  have hd : HasFDerivAt (expansion g K) (fderiv ℝ (expansion g K) (γ 0)) (γ 0) :=
    ((expansion_smooth hg hdet hH.1).differentiable (by simp) _).hasFDerivAt
  have := hd.comp_hasDerivAt (0:ℝ) hγd
  rw [hγ0, horizon_focusing g hg hs hdet x k K hH] at this
  exact this

lemma continuous_qf_along (T : E → Mat) (hTd : ∀ a b, Differentiable ℝ fun y => T y a b)
    (K : E → E) (hK : SmV K) (γ : ℝ → E) (hγ : Continuous γ) :
    Continuous fun s => qf (T (γ s)) (K (γ s)) := by
  have h1 : ∀ i, Continuous fun s => K (γ s) i := fun i => (hK i).continuous.comp hγ
  have h2 : ∀ i j, Continuous fun s => T (γ s) i j := fun i j => (hTd i j).continuous.comp hγ
  unfold qf
  simp only [dotProduct, mulVec]
  exact continuous_finsetSum _ fun i _ => (h1 i).mul
    (continuous_finsetSum _ fun j _ => (h2 i j).mul (h1 j))

/-- **Clausius on every local horizon ⇒ Einstein, with Raychaudhuri proved.** On `g = Pᵀ η P`
(`P` smooth, invertible), with `T` symmetric, conserved, with differentiable components, and
`κ, ħ, G ≠ 0`: suppose that at every point `x`, for every null `k`, every local horizon `K`
through `x` with generator `k` and every curve `γ` leaving `x` with velocity `k`, the Clausius
relation `δQ = (ħκ/2π) δA/(4Għ)` holds to `o(ε²)`, with heat flux `δQ = κ∫ s T(K,K)` and area
change `δA = −∫ θ`, `θ` the expansion of `K`. Then `Ric − ½R g + Λ g = 8πG T` with `Λ`
constant. -/
theorem clausius_to_einstein_geom (P : E → Mat) (hPs : Sm P) (hP : ∀ x, IsUnit (P x).det)
    (T : E → Mat) (hTd : ∀ a b, Differentiable ℝ fun y => T y a b) (hTs : ∀ x, (T x).IsSymm)
    (hcons : ∀ x b, covDiv (gP P) T x b = 0) (κ ħ G : ℝ) (hκ : κ ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0)
    (hClausius : ∀ x k, qf (gP P x) k = 0 → ∀ K, IsLocalHorizon (gP P) x k K →
      ∀ γ : ℝ → E, Continuous γ → γ 0 = x → HasDerivAt γ k 0 →
      Tendsto (fun ε =>
        (κ * (∫ s in (0:ℝ)..ε, s * qf (T (γ s)) (K (γ s)))
          - (ħ * κ / (2 * Real.pi)) * (1 / (4 * G * ħ))
            * (-∫ s in (0:ℝ)..ε, expansion (gP P) K (γ s))) / ε^2)
        (𝓝[>] 0) (𝓝 0)) :
    ∃ Λ : ℝ, ∀ x, ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x + Λ • gP P x
      = (8 * Real.pi * G) • T x := by
  apply curved_clausius_general P hPs hP T hTd hTs hcons (8 * Real.pi * G)
  intro x k hk
  have hg := hPs.gP
  have hs := gP_symm P
  have hdet := gP_det P hP
  have key : ∀ K, IsLocalHorizon (gP P) x k K →
      qf (ricci (gP P) x) k = 8 * Real.pi * G * qf (T x) k := by
    intro K hH
    let γ : ℝ → E := fun s => x + s • k
    have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
    have hγ0 : γ 0 = x := by simp only [γ, zero_smul, add_zero]
    have hγd : HasDerivAt γ k 0 := by
      have h := ((hasDerivAt_id (0:ℝ)).smul_const k).const_add x
      rw [one_smul] at h
      exact h
    have hcl := hClausius x k hk K hH γ hγc hγ0 hγd
    have hθd := expansion_along (gP P) hg hs hdet x k K hH γ hγ0 hγd
    have hθ0 : (fun s => expansion (gP P) K (γ s)) 0 = 0 := by
      show expansion (gP P) K (γ 0) = 0
      rw [hγ0]; exact expansion_zero _ x k K hH
    have hθc : Continuous fun s => expansion (gP P) K (γ s) :=
      (expansion_smooth hg hdet hH.1).continuous.comp hγc
    have hTc := continuous_qf_along T hTd K hH.1 γ hγc
    have hray : HasDerivAt (fun s => expansion (gP P) K (γ s))
        (-((fun s => expansion (gP P) K (γ s)) 0)^2/((4:ℝ)-2) - ((fun _ : ℝ => (0:ℝ)) 0)^2
          - (fun _ : ℝ => qf (ricci (gP P) x) k) 0) 0 := by
      rw [hθ0]; convert hθd using 1; ring
    have := clausius_from_raychaudhuri (fun s => expansion (gP P) K (γ s)) (fun _ => 0)
      (fun _ => qf (ricci (gP P) x) k) (fun s => qf (T (γ s)) (K (γ s))) 4 κ ħ G hθc hTc hray
      hθ0 rfl hκ hħ hG hcl
    have hT0 : qf (T (γ 0)) (K (γ 0)) = qf (T x) k := by rw [hγ0, hH.2.1]
    exact this.trans (by rw [hT0])
  exact key _ (horizon_exists (gP P) hg hs hdet x k)

/-- **The converse.** If Einstein's equation holds (any `Λ`), the Clausius relation of
`clausius_to_einstein_geom` holds on every local horizon along every curve. With the forward
theorem, the geometric premise is equivalent to Einstein's equation. -/
theorem einstein_to_clausius_geom (P : E → Mat) (hPs : Sm P) (hP : ∀ x, IsUnit (P x).det)
    (T : E → Mat) (hTd : ∀ a b, Differentiable ℝ fun y => T y a b) (κ ħ G Λ : ℝ)
    (hħ : ħ ≠ 0) (hG : G ≠ 0)
    (hE : ∀ x, ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x + Λ • gP P x
      = (8 * Real.pi * G) • T x) :
    ∀ x k, qf (gP P x) k = 0 → ∀ K, IsLocalHorizon (gP P) x k K →
      ∀ γ : ℝ → E, Continuous γ → γ 0 = x → HasDerivAt γ k 0 →
      Tendsto (fun ε =>
        (κ * (∫ s in (0:ℝ)..ε, s * qf (T (γ s)) (K (γ s)))
          - (ħ * κ / (2 * Real.pi)) * (1 / (4 * G * ħ))
            * (-∫ s in (0:ℝ)..ε, expansion (gP P) K (γ s))) / ε^2)
        (𝓝[>] 0) (𝓝 0) := by
  intro x k hk K hH γ hγc hγ0 hγd
  have hg := hPs.gP
  have hs := gP_symm P
  have hdet := gP_det P hP
  have hnull : qf (ricci (gP P) x) k = 8 * Real.pi * G * qf (T x) k := by
    have := congrArg (fun M => qf M k) (hE x)
    simp only [qf, Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at this hk ⊢
    rw [hk] at this
    linarith
  have hθd := expansion_along (gP P) hg hs hdet x k K hH γ hγ0 hγd
  have hθ0 : (fun s => expansion (gP P) K (γ s)) 0 = 0 := by
    show expansion (gP P) K (γ 0) = 0
    rw [hγ0]; exact expansion_zero _ x k K hH
  have hθc : Continuous fun s => expansion (gP P) K (γ s) :=
    (expansion_smooth hg hdet hH.1).continuous.comp hγc
  have hTc := continuous_qf_along T hTd K hH.1 γ hγc
  have hA := integral_second_order _ _ hθc hθ0 hθd
  have hQ := weighted_integral_limit _ hTc
  set c := (ħ * κ / (2 * Real.pi)) * (1 / (4 * G * ħ))
  have hsum := (hQ.const_mul κ).sub (hA.neg.const_mul c)
  have heq : (fun ε => κ * ((∫ s in (0:ℝ)..ε, s * qf (T (γ s)) (K (γ s))) / ε^2)
      - c * (-((∫ s in (0:ℝ)..ε, expansion (gP P) K (γ s)) / ε^2))) = fun ε =>
      (κ * (∫ s in (0:ℝ)..ε, s * qf (T (γ s)) (K (γ s)))
        - c * (-∫ s in (0:ℝ)..ε, expansion (gP P) K (γ s))) / ε^2 := by
    ext ε; ring
  rw [heq] at hsum
  convert hsum using 2
  simp only [hγ0, hH.2.1, hnull, c]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end EntEq.Curved
