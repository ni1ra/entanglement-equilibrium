/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Existence of coordinates that are normal to second order at a point: this discharges the
  gauge-condition hypothesis of `RNC.metric_second_derivative` (for second-order normal
  coordinates, which is all it uses).

  The change of coordinates is the polynomial
  `x^a = y^a + ½ B^a_bc y^b y^c + (1/6) C^a_bcd y^b y^c y^d`, with
  `B^a_bc = −Γ^a_bc(0)` (`Bc`) and `C^a_bcd = −sym_(bcd)(∂_dΓ^a_bc − 2 Γ^a_be Γ^e_cd)(0)` (`Cc`),
  for a metric with `g(0) = η = diag(s)`, `s_a = ±1` (so `δ` or Minkowski). The coefficient 2
  was first checked by sympy outside Lean (coefficient 1 fails), then proved here.

  Two layers:
  * Taylor data (finite index algebra on numbers, no functions): `pull1`, `pull2` are the
    first and second derivatives at `0` of `g'_ij(y) = ∂_i x^a ∂_j x^b g_ab(x(y))` written in
    terms of the Taylor data of `g` and the coefficients of `x`. `normal_taylor`: the new
    Christoffels vanish and their symmetrised derivative vanishes. `riemann_unchanged`,
    `second_derivative_riemann`: the new second derivatives are `−⅓(R_acbd + R_adbc)` with `R`
    built from the original data (`Rlow`). `normal_coordinates_taylor` first applies a linear
    map `L` with `Lᵀ g0 L = η`, supplied as a hypothesis (Sylvester's theorem is not proved).
  * Genuine functions on `ℝ^(n+1)` (`pd`, `chr`, `riem` from CurvedCoords, `fderiv` chain rule):
    `pd_pullG_zero`, `pd_pd_pullG_zero` prove that the derivatives of the actual pull-back
    metric `pullG` (`= Dxᵀ g(x) Dx`, entrywise) at `0` ARE `pull1`, `pull2`.
    `normal_coordinates`: for a smooth symmetric `g` with `g(0) = diag(s)`, the pull-back along
    `xNC s g` has `g'(0) = diag(s)`, `∂g'(0) = 0`, `Γ'(0) = 0`, symmetrised `∂Γ'(0) = 0`, and
    `∂_c∂_d g'_ab(0) = −⅓(R_acbd + R_adbc)`. `riem_lowered` identifies `Rlow` with
    `s_a · Curved.riem g 0` (needs `g` invertible everywhere), giving `normal_coordinates_riem`.

  Not covered: the genuine-function layer assumes `g(0) = diag(s)` already (no linear step for
  functions); it says nothing about the `O(|y|³)` remainder (Taylor's theorem) or about geodesics
  and the exponential map: these are coordinates normal to second order, which is all `RNC` uses.
  Nor is `xNC` proved to be a local diffeomorphism; its Jacobian at `0` is the identity, so the
  inverse function theorem gives that, but it is not formalized here.
-/
import EntEq.RNC
import EntEq.BianchiGeneral

namespace EntEq.NormalCoords

open EntEq.RNC (dΓ R)

variable {m : ℕ}

/-! ### Taylor data and the jet pull-back -/

/-- `η = diag(s)`. -/
def eta (s : Fin m → ℝ) (a b : Fin m) : ℝ := if a = b then s a else 0

/-- Lowered Christoffel symbol at the point, `Γ_abc = ½(∂_c g_ab + ∂_b g_ac − ∂_a g_bc)`,
from first derivatives `g1 a b c = ∂_c g_ab`. -/
noncomputable def Gam (g1 : Fin m → Fin m → Fin m → ℝ) (a b c : Fin m) : ℝ :=
  (g1 a b c + g1 a c b - g1 b c a) / 2

/-- First derivatives at `0` of the pull-back of Taylor data `(g0, g1)` under
`x^a = y^a + ½ B^a_bc y^b y^c + …`: `∂_k g'_ij = B^a_ik g0_aj + g0_ia B^a_jk + ∂_k g_ij`. -/
def pull1 (g0 : Fin m → Fin m → ℝ) (g1 B : Fin m → Fin m → Fin m → ℝ) (i j k : Fin m) : ℝ :=
  ∑ a, (B a i k * g0 a j + g0 i a * B a j k) + g1 i j k

/-- Second derivatives `∂_k ∂_l g'_ij` at `0` of the pull-back of Taylor data `(g0, g1, g2)`
(`g2 a b c d = ∂_c ∂_d g_ab`) under `x^a = y^a + ½ B^a_bc y^b y^c + (1/6) C^a_bcd y^b y^c y^d`. -/
def pull2 (g0 : Fin m → Fin m → ℝ) (g1 B : Fin m → Fin m → Fin m → ℝ)
    (g2 C : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) : ℝ :=
  ∑ a, (C a i k l * g0 a j + g0 i a * C a j k l)
    + ∑ a, ∑ b, (B a i k * B b j l + B a i l * B b j k) * g0 a b
    + ∑ a, (B a i k * g1 a j l + B a i l * g1 a j k + B a j k * g1 i a l + B a j l * g1 i a k)
    + g2 i j k l + ∑ c, g1 i j c * B c k l

/-! ### The coordinate change -/

/-- `B^a_bc = −Γ^a_bc(0) = −s_a Γ_abc` (raising with `η⁻¹ = η`). -/
noncomputable def Bc (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ) (a b c : Fin m) : ℝ :=
  s a * -Gam g1 a b c

/-- The quadratic part, at dummy index `e`, of `η_aa (∂_dΓ^a_bc − 2Γ^a_be Γ^e_cd)`:
`s_e g1_{ae,d} Γ_ebc + 2 s_e Γ_abe Γ_ecd` (the first term comes from `∂_d η^{ae} = −η g1 η`). -/
noncomputable def KQ (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ) (e a b c d : Fin m) : ℝ :=
  s e * g1 a e d * Gam g1 e b c + 2 * (s e * Gam g1 a b e * Gam g1 e c d)

/-- Lowered `K_abcd = η_aa (∂_dΓ^a_bc − 2 Γ^a_be Γ^e_cd)` at the point. -/
noncomputable def Kt (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  dΓ g2 a b c d - ∑ e, KQ s g1 e a b c d

/-- Lowered cubic coefficient: minus the symmetrisation of `K_a(bcd)` over `b, c, d`. -/
noncomputable def Ct (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  -(Kt s g1 g2 a b c d + Kt s g1 g2 a b d c + Kt s g1 g2 a c b d + Kt s g1 g2 a c d b
    + Kt s g1 g2 a d b c + Kt s g1 g2 a d c b) / 6

/-- `C^a_bcd = −sym_(bcd)(∂_dΓ^a_bc − 2Γ^a_be Γ^e_cd)(0) = s_a Ct_abcd`. -/
noncomputable def Cc (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  s a * Ct s g1 g2 a b c d

/-- The new second derivatives `h_{ij,kl} = ∂_k∂_l g'_ij(0)` in normal coordinates. -/
noncomputable def hNC (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) : Fin m → Fin m → Fin m → Fin m → ℝ :=
  pull2 (eta s) g1 (Bc s g1) g2 (Cc s g1 g2)

/-- Lowered Riemann tensor of the original Taylor data at the point (`g0 = η`):
`R_abcd = ∂_cΓ_adb − ∂_dΓ_acb + s_e(Γ_ead Γ_ecb − Γ_eac Γ_edb)`, the lowering of
`Curved.riem`'s `R^a_bcd = ∂_cΓ^a_db − ∂_dΓ^a_cb + Γ^a_ce Γ^e_db − Γ^a_de Γ^e_cb`. -/
noncomputable def Rlow (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  dΓ g2 a d b c - dΓ g2 a c b d
    + ∑ e, s e * (Gam g1 e a d * Gam g1 e c b - Gam g1 e a c * Gam g1 e d b)

/-- The `RNC` gauge combination: the symmetrisation of `∂_dΓ_abc` over `b, c, d`. -/
noncomputable def gauge (h : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  dΓ h a b c d + dΓ h a c d b + dΓ h a d b c

/-! ### Splitting into a dummy-free part and one dummy sum -/

/-- `sym1 t` symmetrises `t` in its first two slots. -/
noncomputable def sym1 (t : Fin m → Fin m → Fin m → ℝ) (a b c : Fin m) : ℝ :=
  (t a b c + t b a c) / 2

/-- `sym2 u` symmetrises `u` in its first pair and in its second pair. -/
noncomputable def sym2 (u : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  (u a b c d + u b a c d + u a b d c + u b a d c) / 4

lemma sym1_eq {g1 : Fin m → Fin m → Fin m → ℝ} (h : ∀ a b c, g1 a b c = g1 b a c) :
    sym1 g1 = g1 := by
  funext a b c; simp only [sym1, ← h a b c]; ring

lemma sym2_eq {g2 : Fin m → Fin m → Fin m → Fin m → ℝ} (h1 : ∀ a b c d, g2 a b c d = g2 b a c d)
    (h2 : ∀ a b c d, g2 a b c d = g2 a b d c) : sym2 g2 = g2 := by
  funext a b c d; simp only [sym2, ← h1 a b c d, ← h2 a b c d, ← h1 a b d c]; ring

/-- Dummy-free part of `Ct`. -/
noncomputable def CtL (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  -(dΓ g2 a b c d + dΓ g2 a b d c + dΓ g2 a c b d + dΓ g2 a c d b
    + dΓ g2 a d b c + dΓ g2 a d c b) / 6

/-- Summand of the dummy sum in `Ct`. -/
noncomputable def CtQ (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ) (e a b c d : Fin m) : ℝ :=
  (KQ s g1 e a b c d + KQ s g1 e a b d c + KQ s g1 e a c b d + KQ s g1 e a c d b
    + KQ s g1 e a d b c + KQ s g1 e a d c b) / 6

lemma Ct_split (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) :
    Ct s g1 g2 a b c d = CtL g2 a b c d + ∑ e, CtQ s g1 e a b c d := by
  simp only [Ct, Kt, CtL, CtQ, ← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- Dummy-free part of `hNC`. -/
noncomputable def hL (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) : ℝ :=
  CtL g2 j i k l + CtL g2 i j k l + g2 i j k l

/-- Summand (dummy index `e`) of the dummy sum in `hNC`. -/
noncomputable def hQ (s : Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ) (e i j k l : Fin m) : ℝ :=
  CtQ s g1 e j i k l + CtQ s g1 e i j k l
    + s e * (Gam g1 e i k * Gam g1 e j l + Gam g1 e i l * Gam g1 e j k)
    + (Bc s g1 e i k * g1 e j l + Bc s g1 e i l * g1 e j k + Bc s g1 e j k * g1 i e l
      + Bc s g1 e j l * g1 i e k)
    + g1 i j e * Bc s g1 e k l

lemma sum_mul_eta (s f : Fin m → ℝ) (j : Fin m) : ∑ a, f a * eta s a j = f j * s j := by
  simp [eta, mul_ite]

lemma sum_mul_eta' (s f : Fin m → ℝ) (i : Fin m) : ∑ b, f b * eta s i b = f i * s i := by
  simp [eta, mul_ite]

lemma sum_eta_mul (s f : Fin m → ℝ) (i : Fin m) : ∑ a, eta s i a * f a = s i * f i := by
  simp [eta, ite_mul]

lemma hNC_split (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) :
    hNC s g1 g2 i j k l = hL g2 i j k l + ∑ e, hQ s g1 e i j k l := by
  have hC : ∑ a, (Cc s g1 g2 a i k l * eta s a j + eta s i a * Cc s g1 g2 a j k l)
      = Ct s g1 g2 j i k l + Ct s g1 g2 i j k l := by
    rw [Finset.sum_add_distrib, sum_mul_eta, sum_eta_mul]
    simp only [Cc]
    linear_combination (Ct s g1 g2 j i k l) * hs j + (Ct s g1 g2 i j k l) * hs i
  have hB : ∑ a, ∑ b, (Bc s g1 a i k * Bc s g1 b j l + Bc s g1 a i l * Bc s g1 b j k) * eta s a b
      = ∑ e, s e * (Gam g1 e i k * Gam g1 e j l + Gam g1 e i l * Gam g1 e j k) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_mul_eta']
    simp only [Bc]
    linear_combination (s a * (Gam g1 a i k * Gam g1 a j l + Gam g1 a i l * Gam g1 a j k)) * hs a
  simp only [hNC, pull2, hC, hB, Ct_split, hL, hQ, Finset.sum_add_distrib]
  ring

/-- `gauge` is linear: the dummy sum passes through it. -/
lemma gauge_split (f : Fin m → Fin m → Fin m → Fin m → ℝ)
    (q : Fin m → Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) :
    gauge (fun i j k l => f i j k l + ∑ e, q e i j k l) a b c d
      = gauge f a b c d + ∑ e, gauge (q e) a b c d := by
  simp only [gauge, dΓ, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

lemma R_split (f : Fin m → Fin m → Fin m → Fin m → ℝ)
    (q : Fin m → Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) :
    R (fun i j k l => f i j k l + ∑ e, q e i j k l) a b c d
      = R f a b c d + ∑ e, R (q e) a b c d := by
  simp only [R, dΓ, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-! ### Pointwise identities (polynomial identities after symmetrising the data) -/

lemma gauge_hL (u : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) :
    gauge (hL (sym2 u)) a b c d = 0 := by
  simp only [gauge, hL, CtL, dΓ, sym2]
  ring

lemma gauge_hQ (s : Fin m → ℝ) (t : Fin m → Fin m → Fin m → ℝ) (e a b c d : Fin m) :
    gauge (hQ s (sym1 t) e) a b c d = 0 := by
  simp only [gauge, hQ, CtQ, KQ, Bc, Gam, dΓ, sym1]
  ring

lemma hL_symm1 (u : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) :
    hL (sym2 u) i j k l = hL (sym2 u) j i k l := by
  simp only [hL, CtL, dΓ, sym2]; ring

lemma hL_symm2 (u : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) :
    hL (sym2 u) i j k l = hL (sym2 u) i j l k := by
  simp only [hL, CtL, dΓ, sym2]; ring

lemma hQ_symm1 (s : Fin m → ℝ) (t : Fin m → Fin m → Fin m → ℝ) (e i j k l : Fin m) :
    hQ s (sym1 t) e i j k l = hQ s (sym1 t) e j i k l := by
  simp only [hQ, CtQ, KQ, Bc, Gam, sym1]; ring

lemma hQ_symm2 (s : Fin m → ℝ) (t : Fin m → Fin m → Fin m → ℝ) (e i j k l : Fin m) :
    hQ s (sym1 t) e i j k l = hQ s (sym1 t) e i j l k := by
  simp only [hQ, CtQ, KQ, Bc, Gam, sym1]; ring

lemma R_hL (u : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) :
    R (hL (sym2 u)) a b c d = dΓ (sym2 u) a d b c - dΓ (sym2 u) a c b d := by
  simp only [R, hL, CtL, dΓ, sym2]; ring

lemma R_hQ (s : Fin m → ℝ) (t : Fin m → Fin m → Fin m → ℝ) (e a b c d : Fin m) :
    R (hQ s (sym1 t) e) a b c d = s e * (Gam (sym1 t) e a d * Gam (sym1 t) e c b
      - Gam (sym1 t) e a c * Gam (sym1 t) e d b) := by
  simp only [R, hQ, CtQ, KQ, Bc, Gam, dΓ, sym1]; ring

/-! ### Results -/

/-- `η` is its own inverse when `s_a² = 1`, so it serves as `g0⁻¹` below. -/
lemma eta_mul_eta (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1) (a c : Fin m) :
    ∑ b, eta s a b * eta s b c = if a = c then 1 else 0 := by
  rw [sum_eta_mul]; by_cases h : a = c <;> simp [eta, h, hs]

/-- **The new first derivatives vanish**: `∂_k g'_ij(0) = 0`. -/
theorem pull1_zero (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1) (g1 : Fin m → Fin m → Fin m → ℝ)
    (hg1 : ∀ a b c, g1 a b c = g1 b a c) (i j k : Fin m) :
    pull1 (eta s) g1 (Bc s g1) i j k = 0 := by
  simp only [pull1, Finset.sum_add_distrib, sum_mul_eta, sum_eta_mul, Bc, Gam]
  linear_combination (-(g1 j i k + g1 j k i - g1 i k j) / 2) * hs j
    + (-(g1 i j k + g1 i k j - g1 j k i) / 2) * hs i + (1/2) * hg1 i j k

/-- Christoffel symbols `Γ^a_bc = g^{ad} Γ_dbc` of Taylor data, given the inverse metric at the
point. -/
noncomputable def chrT (ginv : Fin m → Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (a b c : Fin m) : ℝ :=
  ∑ d, ginv a d * Gam g1 d b c

/-- `∂_dΓ^a_bc` at the point from Taylor data: `g^{ae} ∂_dΓ_ebc + (∂_d g^{ae}) Γ_ebc`, with
`∂_d g⁻¹ = −g⁻¹ (∂_d g) g⁻¹`. -/
noncomputable def dchrT (ginv : Fin m → Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (a b c d : Fin m) : ℝ :=
  ∑ e, ginv a e * dΓ g2 e b c d
    - ∑ e, ∑ p, ∑ q, ginv a p * g1 p q d * ginv q e * Gam g1 e b c

lemma hNC_fun (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) :
    hNC s g1 g2 = fun i j k l => hL g2 i j k l + ∑ e, hQ s g1 e i j k l :=
  funext fun i => funext fun j => funext fun k => funext fun l => hNC_split s hs g1 g2 i j k l

/-- **The new second derivatives satisfy the `RNC` gauge condition.** -/
theorem gauge_hNC (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (hg1 : ∀ a b c, g1 a b c = g1 b a c)
    (hg2a : ∀ a b c d, g2 a b c d = g2 b a c d) (hg2b : ∀ a b c d, g2 a b c d = g2 a b d c)
    (a b c d : Fin m) : gauge (hNC s g1 g2) a b c d = 0 := by
  rw [hNC_fun s hs, gauge_split]
  have h1 := gauge_hL g2 a b c d
  rw [sym2_eq hg2a hg2b] at h1
  have h2 : ∀ e, gauge (hQ s g1 e) a b c d = 0 := fun e => by
    simpa only [sym1_eq hg1] using gauge_hQ s g1 e a b c d
  simp [h1, h2]

/-- **Normal coordinates to second order (Taylor data).** In the new data `(η, 0, hNC)` the
Christoffel symbols vanish at the point and so does their symmetrised first derivative. -/
theorem normal_taylor (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (hg1 : ∀ a b c, g1 a b c = g1 b a c)
    (hg2a : ∀ a b c d, g2 a b c d = g2 b a c d) (hg2b : ∀ a b c d, g2 a b c d = g2 a b d c) :
    (∀ a b c, chrT (eta s) (pull1 (eta s) g1 (Bc s g1)) a b c = 0) ∧
    (∀ a b c d, dchrT (eta s) (pull1 (eta s) g1 (Bc s g1)) (hNC s g1 g2) a b c d
      + dchrT (eta s) (pull1 (eta s) g1 (Bc s g1)) (hNC s g1 g2) a c d b
      + dchrT (eta s) (pull1 (eta s) g1 (Bc s g1)) (hNC s g1 g2) a d b c = 0) := by
  have hz : pull1 (eta s) g1 (Bc s g1) = fun _ _ _ => 0 :=
    funext fun i => funext fun j => funext fun k => pull1_zero s hs g1 hg1 i j k
  refine ⟨fun a b c => by simp [chrT, hz, Gam], fun a b c d => ?_⟩
  have := gauge_hNC s hs g1 g2 hg1 hg2a hg2b a b c d
  simp only [dchrT, hz, Gam, sum_eta_mul, gauge] at *
  simp only [add_zero, sub_self, zero_div, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  linear_combination s a * this

/-- `hNC` is symmetric in its first pair of indices. -/
theorem hNC_symm1 (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (hg1 : ∀ a b c, g1 a b c = g1 b a c)
    (hg2a : ∀ a b c d, g2 a b c d = g2 b a c d) (hg2b : ∀ a b c d, g2 a b c d = g2 a b d c)
    (i j k l : Fin m) : hNC s g1 g2 i j k l = hNC s g1 g2 j i k l := by
  rw [hNC_split s hs, hNC_split s hs]
  have h1 := hL_symm1 g2 i j k l
  rw [sym2_eq hg2a hg2b] at h1
  have h2 : ∀ e, hQ s g1 e i j k l = hQ s g1 e j i k l := fun e => by
    simpa only [sym1_eq hg1] using hQ_symm1 s g1 e i j k l
  rw [h1, Finset.sum_congr rfl fun e _ => h2 e]

/-- `hNC` is symmetric in its second pair of indices. -/
theorem hNC_symm2 (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (hg1 : ∀ a b c, g1 a b c = g1 b a c)
    (hg2a : ∀ a b c d, g2 a b c d = g2 b a c d) (hg2b : ∀ a b c d, g2 a b c d = g2 a b d c)
    (i j k l : Fin m) : hNC s g1 g2 i j k l = hNC s g1 g2 i j l k := by
  rw [hNC_split s hs, hNC_split s hs]
  have h1 := hL_symm2 g2 i j k l
  rw [sym2_eq hg2a hg2b] at h1
  have h2 : ∀ e, hQ s g1 e i j k l = hQ s g1 e i j l k := fun e => by
    simpa only [sym1_eq hg1] using hQ_symm2 s g1 e i j k l
  rw [h1, Finset.sum_congr rfl fun e _ => h2 e]

/-- **The Riemann tensor is unchanged** by the coordinate change (its Jacobian at the point is the
identity): `RNC.R` of the new second derivatives equals the Riemann tensor `Rlow` of the original
Taylor data. -/
theorem riemann_unchanged (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1)
    (g1 : Fin m → Fin m → Fin m → ℝ) (g2 : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hg1 : ∀ a b c, g1 a b c = g1 b a c)
    (hg2a : ∀ a b c d, g2 a b c d = g2 b a c d) (hg2b : ∀ a b c d, g2 a b c d = g2 a b d c)
    (a b c d : Fin m) : R (hNC s g1 g2) a b c d = Rlow s g1 g2 a b c d := by
  rw [hNC_fun s hs, R_split, Rlow]
  have h1 := R_hL g2 a b c d
  rw [sym2_eq hg2a hg2b] at h1
  have h2 : ∀ e, R (hQ s g1 e) a b c d
      = s e * (Gam g1 e a d * Gam g1 e c b - Gam g1 e a c * Gam g1 e d b) := fun e => by
    simpa only [sym1_eq hg1] using R_hQ s g1 e a b c d
  rw [h1, Finset.sum_congr rfl fun e _ => h2 e]

/-- **Target 3 (Taylor data, `g0 = η`).** After the polynomial change of coordinates, the metric
is `η + 0·y + ½ h y y + O(|y|³)` with `h_{ab,cd} = −⅓(R_acbd + R_adbc)`, `R` the Riemann tensor
of the original data at the point. -/
theorem second_derivative_riemann (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1)
    (g1 : Fin m → Fin m → Fin m → ℝ) (g2 : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hg1 : ∀ a b c, g1 a b c = g1 b a c)
    (hg2a : ∀ a b c d, g2 a b c d = g2 b a c d) (hg2b : ∀ a b c d, g2 a b c d = g2 a b d c)
    (a b c d : Fin m) :
    hNC s g1 g2 a b c d = -(1/3) * (Rlow s g1 g2 a c b d + Rlow s g1 g2 a d b c) := by
  rw [← riemann_unchanged s hs g1 g2 hg1 hg2a hg2b, ← riemann_unchanged s hs g1 g2 hg1 hg2a hg2b]
  exact RNC.metric_second_derivative _ (hNC_symm1 s hs g1 g2 hg1 hg2a hg2b)
    (hNC_symm2 s hs g1 g2 hg1 hg2a hg2b) (gauge_hNC s hs g1 g2 hg1 hg2a hg2b) a b c d

/-- The quadratic term: `½ h_{ab,cd} y^c y^d = −⅓ R_acbd y^c y^d`. -/
theorem quadratic_term_riemann (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1)
    (g1 : Fin m → Fin m → Fin m → ℝ) (g2 : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hg1 : ∀ a b c, g1 a b c = g1 b a c)
    (hg2a : ∀ a b c d, g2 a b c d = g2 b a c d) (hg2b : ∀ a b c d, g2 a b c d = g2 a b d c)
    (y : Fin m → ℝ) (a b : Fin m) :
    (1/2) * ∑ c, ∑ d, hNC s g1 g2 a b c d * y c * y d
      = -(1/3) * ∑ c, ∑ d, Rlow s g1 g2 a c b d * y c * y d := by
  rw [RNC.metric_quadratic_term _ (hNC_symm1 s hs g1 g2 hg1 hg2a hg2b)
    (hNC_symm2 s hs g1 g2 hg1 hg2a hg2b) (gauge_hNC s hs g1 g2 hg1 hg2a hg2b)]
  simp only [riemann_unchanged s hs g1 g2 hg1 hg2a hg2b]

/-! ### First bringing `g0` to `η` by a linear map -/

/-- Pull-back of `g0` under `x = L y` (`x^a = L a i y^i`): `Lᵀ g0 L`. -/
def lin0 (L g0 : Fin m → Fin m → ℝ) (i j : Fin m) : ℝ :=
  ∑ a, ∑ b, L a i * L b j * g0 a b

/-- Pull-back of the first derivatives under `x = L y`. -/
def lin1 (L : Fin m → Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ) (i j k : Fin m) : ℝ :=
  ∑ a, ∑ b, ∑ c, L a i * L b j * L c k * g1 a b c

/-- Pull-back of the second derivatives under `x = L y`. -/
def lin2 (L : Fin m → Fin m → ℝ) (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (i j k l : Fin m) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, L a i * L b j * L c k * L d l * g2 a b c d

lemma lin1_symm (L : Fin m → Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (hg1 : ∀ a b c, g1 a b c = g1 b a c) (i j k : Fin m) : lin1 L g1 i j k = lin1 L g1 j i k := by
  unfold lin1; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [hg1]; ring

lemma lin2_symm1 (L : Fin m → Fin m → ℝ) (g2 : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hg2 : ∀ a b c d, g2 a b c d = g2 b a c d) (i j k l : Fin m) :
    lin2 L g2 i j k l = lin2 L g2 j i k l := by
  unfold lin2; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [hg2]; ring

lemma lin2_symm2 (L : Fin m → Fin m → ℝ) (g2 : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hg2 : ∀ a b c d, g2 a b c d = g2 a b d c) (i j k l : Fin m) :
    lin2 L g2 i j k l = lin2 L g2 i j l k := by
  unfold lin2
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hg2]; ring

/-- **Target 1 + 3 for arbitrary Taylor data.** Given second-order Taylor data `(g0, g1, g2)` of
a metric at a point (symmetric in the metric pair, `g2` symmetric in the derivative pair) and a
linear map `L` with `Lᵀ g0 L = η`, the composite change `x = L(y + ½ B y y + (1/6) C y y y)`, with
`B = Bc`, `C = Cc` built from the linearly pulled-back data `(G1, G2)`, yields Taylor data
`η + 0·y + ½ h y y` with `h_{ab,cd} = −⅓(R_acbd + R_adbc)` and `R` the Riemann tensor of `(η, G1, G2)`
at the point. (The composite's data is taken as the two pull-backs in turn; that pull-backs
compose is the chain rule, not re-proved here.) -/
theorem normal_coordinates_taylor (s : Fin m → ℝ) (hs : ∀ a, s a * s a = 1)
    (g0 : Fin m → Fin m → ℝ) (g1 : Fin m → Fin m → Fin m → ℝ)
    (g2 : Fin m → Fin m → Fin m → Fin m → ℝ) (hg1 : ∀ a b c, g1 a b c = g1 b a c)
    (hg2a : ∀ a b c d, g2 a b c d = g2 b a c d) (hg2b : ∀ a b c d, g2 a b c d = g2 a b d c)
    (L : Fin m → Fin m → ℝ) (hL : lin0 L g0 = eta s) :
    let G1 := lin1 L g1
    let G2 := lin2 L g2
    lin0 L g0 = eta s ∧
    (∀ i j k, pull1 (lin0 L g0) G1 (Bc s G1) i j k = 0) ∧
    (∀ a b c d, pull2 (lin0 L g0) G1 (Bc s G1) G2 (Cc s G1 G2) a b c d
      = -(1/3) * (Rlow s G1 G2 a c b d + Rlow s G1 G2 a d b c)) := by
  intro G1 G2
  have h1 : ∀ a b c, G1 a b c = G1 b a c := lin1_symm L g1 hg1
  have h2a : ∀ a b c d, G2 a b c d = G2 b a c d := lin2_symm1 L g2 hg2a
  have h2b : ∀ a b c d, G2 a b c d = G2 a b d c := lin2_symm2 L g2 hg2b
  refine ⟨hL, fun i j k => ?_, fun a b c d => ?_⟩
  · rw [hL]; exact pull1_zero s hs G1 h1 i j k
  · rw [hL]; exact second_derivative_riemann s hs G1 G2 h1 h2a h2b a b c d

/-! ## Genuine functions: the pull-back of a smooth metric field on `ℝ^(n+1)`

From here on `g : E → Mat` is a smooth metric field (CurvedCoords conventions: `pd`, `chr`), and
the derivatives at `0` of the pulled-back metric are computed with `fderiv` and the chain rule. -/

section Genuine

open EntEq.Curved
open scoped ContDiff

variable {n : ℕ}
local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

lemma pd_coord (b : Fin (n+1)) (z : E) (i : Fin (n+1)) :
    pd (fun y : E => y b) z i = if b = i then 1 else 0 := by
  have : (fun y : E => y b) = ⇑(ContinuousLinearMap.proj b : E →L[ℝ] ℝ) := rfl
  unfold pd; rw [this, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply]

lemma pd_comp (f : E → ℝ) (x : E → E) (hf : Differentiable ℝ f)
    (hx : ∀ c, Differentiable ℝ fun y => x y c) (y : E) (k : Fin (n+1)) :
    pd (fun z => f (x z)) y k = ∑ c, pd f (x y) c * pd (fun z => x z c) y k := by
  have hxd : Differentiable ℝ x := differentiable_pi.2 hx
  have h1 : fderiv ℝ (fun z => f (x z)) y = (fderiv ℝ f (x y)).comp (fderiv ℝ x y) :=
    fderiv_comp y (hf (x y)) (hxd y)
  have h2 : fderiv ℝ x y (e k) = fun c => pd (fun z => x z c) y k := by
    rw [fderiv_pi (fun c => hx c y)]; rfl
  show fderiv ℝ (fun z => f (x z)) y (e k) = _
  rw [h1, ContinuousLinearMap.comp_apply, h2]
  conv_lhs => rw [← Finset.univ_sum_single (fun c => pd (fun z => x z c) y k)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show (Pi.single c (pd (fun z => x z c) y k) : E) = pd (fun z => x z c) y k • e c by
    ext j; simp [Pi.single_apply]]
  rw [map_smul, smul_eq_mul, mul_comm]; rfl

/-- Jacobian entry `∂_i x^a` at `y`. -/
noncomputable def Jx (x : E → E) (a i : Fin (n+1)) (y : E) : ℝ := pd (fun z => x z a) y i

/-- Pull-back metric `g'_ij(y) = ∂_i x^a ∂_j x^b g_ab(x(y))`. -/
noncomputable def pullG (g : E → Mat) (x : E → E) (y : E) : Mat :=
  Matrix.of fun i j => ∑ a, ∑ b, Jx x a i y * Jx x b j y * g (x y) a b

lemma pd_pullG (g : E → Mat) (x : E → E) (hg : Sm g) (hx : ∀ c, ContDiff ℝ ∞ fun y => x y c)
    (y : E) (i j k : Fin (n+1)) :
    pd (fun y => pullG g x y i j) y k = ∑ a, ∑ b,
      (pd (Jx x a i) y k * Jx x b j y * g (x y) a b
        + Jx x a i y * pd (Jx x b j) y k * g (x y) a b
        + Jx x a i y * Jx x b j y * ∑ c, pd (fun z => g z a b) (x y) c * Jx x c k y) := by
  have hJ : ∀ a i, Differentiable ℝ (Jx x a i) := fun a i => diff_of_smooth (contDiff_pd (hx a) i)
  have hgx : ∀ a b, Differentiable ℝ fun y => g (x y) a b := fun a b =>
    diff_of_smooth ((hg a b).comp (contDiff_pi.2 hx))
  simp only [pullG, Matrix.of_apply]
  rw [pd_sum (fun a y => ∑ b, Jx x a i y * Jx x b j y * g (x y) a b)
    (fun a => Differentiable.fun_sum fun b _ => ((hJ a i).fun_mul (hJ b j)).fun_mul (hgx a b))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pd_sum (fun b y => Jx x a i y * Jx x b j y * g (x y) a b)
    (fun b => ((hJ a i).fun_mul (hJ b j)).fun_mul (hgx a b))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pd_mul ((hJ a i).fun_mul (hJ b j)) (hgx a b), pd_mul (hJ a i) (hJ b j),
    pd_comp (fun z => g z a b) x (diff_of_smooth (hg a b)) (fun c => diff_of_smooth (hx c))]
  simp only [Jx]; ring

/-- First derivatives `∂_c g_ab(0)` of a metric field. -/
noncomputable def tg1 (g : E → Mat) (a b c : Fin (n+1)) : ℝ := pd (fun z => g z a b) 0 c

/-- Second derivatives `∂_d ∂_c g_ab(0)` of a metric field. -/
noncomputable def tg2 (g : E → Mat) (a b c d : Fin (n+1)) : ℝ :=
  pd (fun y => pd (fun z => g z a b) y c) 0 d

lemma pd_pullG_zero (g : E → Mat) (x : E → E) (hg : Sm g)
    (hx : ∀ c, ContDiff ℝ ∞ fun y => x y c) (B : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hx0 : x 0 = 0) (hJ0 : ∀ a i, Jx x a i 0 = if a = i then 1 else 0)
    (hB : ∀ a i k, pd (Jx x a i) 0 k = B a i k) (i j k : Fin (n+1)) :
    pd (fun y => pullG g x y i j) 0 k = pull1 (g 0) (tg1 g) B i j k := by
  rw [pd_pullG g x hg hx]
  simp only [hx0, hJ0, hB, pull1, tg1, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, sum_ite_irrel']
  simp only [mul_comm (g 0 i _)]

lemma pd_pd_pullG_zero (g : E → Mat) (x : E → E) (hg : Sm g)
    (hx : ∀ c, ContDiff ℝ ∞ fun y => x y c) (B : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (C : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hx0 : x 0 = 0) (hJ0 : ∀ a i, Jx x a i 0 = if a = i then 1 else 0)
    (hB : ∀ a i k, pd (Jx x a i) 0 k = B a i k)
    (hC : ∀ a i k l, pd (fun y => pd (Jx x a i) y k) 0 l = C a i k l) (i j k l : Fin (n+1)) :
    pd (fun y => pd (fun y => pullG g x y i j) y k) 0 l
      = pull2 (g 0) (tg1 g) B (tg2 g) C i j k l := by
  have hxs : ContDiff ℝ ∞ x := contDiff_pi.2 hx
  have hJ : ∀ a i, Differentiable ℝ (Jx x a i) := fun a i => diff_of_smooth (contDiff_pd (hx a) i)
  have hdJ : ∀ a i k, Differentiable ℝ fun y => pd (Jx x a i) y k := fun a i k =>
    diff_of_smooth (contDiff_pd (contDiff_pd (hx a) i) k)
  have hgx : ∀ a b, Differentiable ℝ fun y => g (x y) a b := fun a b =>
    diff_of_smooth ((hg a b).comp hxs)
  have hdgx : ∀ a b c, Differentiable ℝ fun y => pd (fun z => g z a b) (x y) c := fun a b c =>
    diff_of_smooth ((contDiff_pd (hg a b) c).comp hxs)
  have hS : ∀ a b, Differentiable ℝ fun y => ∑ c, pd (fun z => g z a b) (x y) c * Jx x c k y :=
    fun a b => Differentiable.fun_sum fun c _ => (hdgx a b c).fun_mul (hJ c k)
  have hT1 : ∀ a b, Differentiable ℝ fun y => pd (Jx x a i) y k * Jx x b j y * g (x y) a b :=
    fun a b => ((hdJ a i k).fun_mul (hJ b j)).fun_mul (hgx a b)
  have hT2 : ∀ a b, Differentiable ℝ fun y => Jx x a i y * pd (Jx x b j) y k * g (x y) a b :=
    fun a b => ((hJ a i).fun_mul (hdJ b j k)).fun_mul (hgx a b)
  have hT3 : ∀ a b, Differentiable ℝ fun y => Jx x a i y * Jx x b j y *
      ∑ c, pd (fun z => g z a b) (x y) c * Jx x c k y :=
    fun a b => ((hJ a i).fun_mul (hJ b j)).fun_mul (hS a b)
  have hfun := funext fun y => pd_pullG g x hg hx y i j k
  rw [hfun]
  rw [pd_sum _ (fun a => Differentiable.fun_sum fun b _ =>
    ((hT1 a b).fun_add (hT2 a b)).fun_add (hT3 a b))]
  have inner : ∀ a b, pd (fun y => pd (Jx x a i) y k * Jx x b j y * g (x y) a b
        + Jx x a i y * pd (Jx x b j) y k * g (x y) a b
        + Jx x a i y * Jx x b j y * ∑ c, pd (fun z => g z a b) (x y) c * Jx x c k y) 0 l
      = (C a i k l * (if b = j then 1 else 0) * g 0 a b + B a i k * B b j l * g 0 a b
          + B a i k * (if b = j then 1 else 0) * ∑ c, tg1 g a b c * (if c = l then 1 else 0))
        + (B a i l * B b j k * g 0 a b + (if a = i then 1 else 0) * C b j k l * g 0 a b
          + (if a = i then 1 else 0) * B b j k * ∑ c, tg1 g a b c * (if c = l then 1 else 0))
        + ((B a i l * (if b = j then 1 else 0) + (if a = i then 1 else 0) * B b j l)
            * ∑ c, tg1 g a b c * (if c = k then 1 else 0)
          + (if a = i then 1 else 0) * (if b = j then 1 else 0) * ∑ c,
            ((∑ d, tg2 g a b c d * (if d = l then 1 else 0)) * (if c = k then 1 else 0)
              + tg1 g a b c * B c k l)) := by
    intro a b
    rw [pd_add ((hT1 a b).fun_add (hT2 a b)) (hT3 a b), pd_add (hT1 a b) (hT2 a b),
      pd_mul ((hdJ a i k).fun_mul (hJ b j)) (hgx a b), pd_mul (hdJ a i k) (hJ b j),
      pd_mul ((hJ a i).fun_mul (hdJ b j k)) (hgx a b), pd_mul (hJ a i) (hdJ b j k),
      pd_mul ((hJ a i).fun_mul (hJ b j)) (hS a b), pd_mul (hJ a i) (hJ b j),
      pd_sum _ (fun c => (hdgx a b c).fun_mul (hJ c k))]
    simp only [pd_mul (hdgx a b _) (hJ _ k)]
    rw [pd_comp (fun z => g z a b) x (diff_of_smooth (hg a b)) (fun c => diff_of_smooth (hx c))]
    simp only [pd_comp (fun z => pd (fun z => g z a b) z _) x
      (diff_of_smooth (contDiff_pd (hg a b) _)) (fun c => diff_of_smooth (hx c))]
    have hJ0' : ∀ a i, pd (fun z => x z a) 0 i = if a = i then 1 else 0 := hJ0
    simp only [hx0, hJ0, hJ0', hB, hC, tg1, tg2]
    ring
  rw [Finset.sum_congr rfl fun a _ =>
    (pd_sum _ fun b => ((hT1 a b).fun_add (hT2 a b)).fun_add (hT3 a b)).trans
      (Finset.sum_congr rfl fun b _ => inner a b)]
  simp only [pull2, add_mul, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, sum_ite_irrel']
  simp only [mul_comm (g 0 i _)]
  ring

/-- The polynomial coordinate change `x^a(y) = y^a + ½ B^a_bc y^b y^c + (1/6) C^a_bcd y^b y^c y^d`. -/
noncomputable def xP (B : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (C : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ) (y : E) : E := fun a =>
  y a + (1/2) * ∑ b, ∑ c, B a b c * y b * y c + (1/6) * ∑ b, ∑ c, ∑ d, C a b c d * y b * y c * y d

lemma pd_xP (B : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (C : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hB : ∀ a b c, B a b c = B a c b) (hC1 : ∀ a b c d, C a b c d = C a c b d)
    (hC2 : ∀ a b c d, C a b c d = C a b d c) (y : E) (a i : Fin (n+1)) :
    Jx (xP B C) a i y = (if a = i then 1 else 0) + ∑ c, B a i c * y c
      + (1/2) * ∑ c, ∑ d, C a i c d * y c * y d := by
  unfold Jx xP
  simp (disch := (try intro); fun_prop) only [pd_add, pd_const_mul, pd_sum, pd_mul, pd_coord]
  simp only [add_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_ite_irrel']
  have e1 : ∑ x, B a x i * y x = ∑ x, B a i x * y x :=
    Finset.sum_congr rfl fun x _ => by rw [hB]
  have e2 : ∑ x, ∑ x_2, C a x i x_2 * y x * y x_2 = ∑ x, ∑ x_2, C a i x x_2 * y x * y x_2 :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x_2 _ => by rw [hC1]
  have e3 : ∑ x, ∑ x_1, C a x x_1 i * y x * y x_1 = ∑ x, ∑ x_1, C a i x x_1 * y x * y x_1 :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x_1 _ => by rw [hC2, hC1]
  rw [e1, e2, e3]
  ring

lemma pd_Jx_xP (B : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (C : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hB : ∀ a b c, B a b c = B a c b) (hC1 : ∀ a b c d, C a b c d = C a c b d)
    (hC2 : ∀ a b c d, C a b c d = C a b d c) (y : E) (a i k : Fin (n+1)) :
    pd (Jx (xP B C) a i) y k = B a i k + ∑ d, C a i k d * y d := by
  have h : Jx (xP B C) a i = fun y => (if a = i then 1 else 0) + ∑ c, B a i c * y c
      + (1/2) * ∑ c, ∑ d, C a i c d * y c * y d := funext fun y => pd_xP B C hB hC1 hC2 y a i
  rw [h]
  simp (disch := (try intro); fun_prop) only [pd_add, pd_const_mul, pd_sum, pd_mul, pd_coord,
    pd_const]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_ite_irrel', zero_add]
  have e : ∑ x, C a i x k * y x = ∑ x, C a i k x * y x :=
    Finset.sum_congr rfl fun x _ => by rw [hC2]
  rw [e]; ring

lemma xP_jets (B : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (C : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hB : ∀ a b c, B a b c = B a c b) (hC1 : ∀ a b c d, C a b c d = C a c b d)
    (hC2 : ∀ a b c d, C a b c d = C a b d c) :
    (∀ c, ContDiff ℝ ∞ fun y => xP B C y c) ∧ xP B C 0 = 0 ∧
    (∀ a i, Jx (xP B C) a i 0 = if a = i then 1 else 0) ∧
    (∀ a i k, pd (Jx (xP B C) a i) 0 k = B a i k) ∧
    (∀ a i k l, pd (fun y => pd (Jx (xP B C) a i) y k) 0 l = C a i k l) := by
  refine ⟨fun c => ?_, ?_, fun a i => ?_, fun a i k => ?_, fun a i k l => ?_⟩
  · unfold xP; fun_prop
  · funext a; simp [xP]
  · rw [pd_xP B C hB hC1 hC2]; simp
  · rw [pd_Jx_xP B C hB hC1 hC2]; simp
  · have h : (fun y => pd (Jx (xP B C) a i) y k) = fun y => B a i k + ∑ d, C a i k d * y d :=
      funext fun y => pd_Jx_xP B C hB hC1 hC2 y a i k
    rw [h]
    simp (disch := (try intro); fun_prop) only [pd_add, pd_const_mul, pd_sum, pd_coord,
      pd_const]
    simp

lemma pd_const_mul_at {f : E → ℝ} {y : E} (k : ℝ) (hf : DifferentiableAt ℝ f y) (c : Fin (n+1)) :
    pd (fun z => k * f z) y c = k * pd f y c := by
  simp [pd, fderiv_const_mul hf]

lemma pd_sum_at {y : E} (F : Fin (n+1) → E → ℝ) (hF : ∀ i, DifferentiableAt ℝ (F i) y)
    (c : Fin (n+1)) : pd (fun z => ∑ i, F i z) y c = ∑ i, pd (F i) y c := by
  unfold pd; rw [fderiv_fun_sum (fun i _ => hF i)]; simp

lemma pd_mul_at {f h : E → ℝ} {y : E} (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y)
    (c : Fin (n+1)) : pd (fun z => f z * h z) y c = pd f y c * h y + f y * pd h y c := by
  simp [pd, fderiv_fun_mul hf hh]; ring

/-- Entries of `M⁻¹` are differentiable wherever `det M ≠ 0` (`M` smooth). -/
lemma diffAt_inv_entry {M : E → Mat} (hM : Sm M) {y : E} (h0 : IsUnit (M y).det)
    (a b : Fin (n+1)) : DifferentiableAt ℝ (fun z => (M z)⁻¹ a b) y := by
  have h : (fun z => (M z)⁻¹ a b) = fun z => ((M z).det)⁻¹ * (M z).adjugate a b := by
    funext z; rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  have hadj : ContDiff ℝ ∞ fun z => (M z).adjugate a b := by
    simp only [Matrix.adjugate_apply]
    apply contDiff_det
    intro i j
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact hM i j
  rw [h]
  exact ((diff_of_smooth (contDiff_det hM)) y |>.inv h0.ne_zero).mul (diff_of_smooth hadj y)

/-- For a smooth matrix field whose first derivatives vanish at `0` (invertible there):
`Γ(0) = 0` and `∂_dΓ^a_bc(0) = ½ (M 0)⁻¹_ae (∂_d∂_b M_ec + ∂_d∂_c M_eb − ∂_d∂_e M_bc)`. -/
lemma chr_flat_point {M : E → Mat} (hM : Sm M) (h0 : IsUnit (M 0).det)
    (hd : ∀ c a b, dg M 0 c a b = 0) (a b c d : Fin (n+1)) :
    chr M 0 a b c = 0 ∧
    pd (fun y => chr M y a b c) 0 d = (1/2) * ∑ e', (M 0)⁻¹ a e' *
      (pd (fun y => dg M y b e' c) 0 d + pd (fun y => dg M y c e' b) 0 d
        - pd (fun y => dg M y e' b c) 0 d) := by
  have hdg : ∀ c a b, Differentiable ℝ fun y => dg M y c a b := fun c a b =>
    diff_of_smooth (contDiff_pd (hM a b) c)
  refine ⟨by simp [chr, hd], ?_⟩
  have hS : ∀ e', Differentiable ℝ fun y => dg M y b e' c + dg M y c e' b - dg M y e' b c :=
    fun e' => ((hdg b e' c).fun_add (hdg c e' b)).fun_sub (hdg e' b c)
  unfold chr
  rw [pd_const_mul_at _ (DifferentiableAt.fun_sum fun e' _ =>
      (diffAt_inv_entry hM h0 a e').fun_mul (hS e' 0)),
    pd_sum_at _ (fun e' => (diffAt_inv_entry hM h0 a e').fun_mul (hS e' 0))]
  congr 1
  refine Finset.sum_congr rfl fun e' _ => ?_
  rw [pd_mul_at (diffAt_inv_entry hM h0 a e') (hS e' 0), hd, hd, hd,
    pd_sub ((hdg b e' c).fun_add (hdg c e' b)) (hdg e' b c), pd_add (hdg b e' c) (hdg c e' b)]
  ring

lemma Sm_pullG (g : E → Mat) (x : E → E) (hg : Sm g) (hx : ∀ c, ContDiff ℝ ∞ fun y => x y c) :
    Sm (pullG g x) := by
  intro i j
  simp only [pullG, Matrix.of_apply]
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    ((contDiff_pd (hx a) i).mul (contDiff_pd (hx b) j)).mul ((hg a b).comp (contDiff_pi.2 hx))

lemma pullG_zero (g : E → Mat) (x : E → E) (hx0 : x 0 = 0)
    (hJ0 : ∀ a i, Jx x a i 0 = if a = i then 1 else 0) : pullG g x 0 = g 0 := by
  ext i j
  simp [pullG, hx0, hJ0, ite_mul, Finset.sum_ite_eq']

lemma tg1_symm (g : E → Mat) (hs : ∀ y, (g y).IsSymm) (a b c : Fin (n+1)) :
    tg1 g a b c = tg1 g b a c := dg_symm g hs 0 c a b

lemma tg2_symm1 (g : E → Mat) (hs : ∀ y, (g y).IsSymm) (a b c d : Fin (n+1)) :
    tg2 g a b c d = tg2 g b a c d := by
  unfold tg2
  have : (fun y => pd (fun z => g z a b) y c) = fun y => pd (fun z => g z b a) y c :=
    funext fun y => dg_symm g hs y c a b
  rw [this]

lemma tg2_symm2 (g : E → Mat) (hg : Sm g) (a b c d : Fin (n+1)) :
    tg2 g a b c d = tg2 g a b d c := pd_pd_comm _ (hg a b) 0 c d

lemma Bc_symm (s : Fin (n+1) → ℝ) (g1 : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hg1 : ∀ a b c, g1 a b c = g1 b a c) (a b c : Fin (n+1)) : Bc s g1 a b c = Bc s g1 a c b := by
  simp only [Bc, Gam]; rw [hg1 b c a]; ring

lemma Cc_symm1 (s : Fin (n+1) → ℝ) (g1 : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (g2 : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ) (a b c d : Fin (n+1)) :
    Cc s g1 g2 a b c d = Cc s g1 g2 a c b d := by
  simp only [Cc, Ct]; ring

lemma Cc_symm2 (s : Fin (n+1) → ℝ) (g1 : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (g2 : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ) (a b c d : Fin (n+1)) :
    Cc s g1 g2 a b c d = Cc s g1 g2 a b d c := by
  simp only [Cc, Ct]; ring

/-- The normal-coordinate map for a metric field `g` at `0`, built from its Taylor data. -/
noncomputable def xNC (s : Fin (n+1) → ℝ) (g : E → Mat) : E → E :=
  xP (Bc s (tg1 g)) (Cc s (tg1 g) (tg2 g))

/-- **Target 2 + 3 (genuine functions).** Let `g` be a smooth symmetric metric field on
`ℝ^(n+1)` with `g(0) = diag(s)`, `s_a = ±1`. Pull it back along the polynomial map
`x = xNC s g` (`x^a = y^a − ½Γ^a_bc y^b y^c − (1/6) S^a_bcd y^b y^c y^d`, coefficients from the
derivatives of `g` at `0`), `g'(y) = Dx(y)ᵀ g(x(y)) Dx(y)`. Then `g'(0) = diag(s)`,
the Christoffel symbols of `g'` vanish at `0`, their symmetrised first derivative
`∂_dΓ'^a_bc + ∂_bΓ'^a_cd + ∂_cΓ'^a_db` vanishes at `0`, all first derivatives of `g'` vanish at `0`,
and its second derivatives are `∂_c∂_d g'_ab(0) = −⅓(R_acbd + R_adbc)` with `R = Rlow`, the
Riemann tensor computed from the derivatives of the ORIGINAL `g` at `0`. -/
theorem normal_coordinates (g : E → Mat) (hg : Sm g) (hsym : ∀ y, (g y).IsSymm)
    (s : Fin (n+1) → ℝ) (hs : ∀ a, s a * s a = 1) (hg0 : g 0 = Matrix.diagonal s) :
    pullG g (xNC s g) 0 = Matrix.diagonal s ∧
    (∀ c a b, dg (pullG g (xNC s g)) 0 c a b = 0) ∧
    (∀ a b c, chr (pullG g (xNC s g)) 0 a b c = 0) ∧
    (∀ a b c d, pd (fun y => chr (pullG g (xNC s g)) y a b c) 0 d
      + pd (fun y => chr (pullG g (xNC s g)) y a c d) 0 b
      + pd (fun y => chr (pullG g (xNC s g)) y a d b) 0 c = 0) ∧
    (∀ a b c d, pd (fun y => pd (fun y => pullG g (xNC s g) y a b) y c) 0 d
      = -(1/3) * (Rlow s (tg1 g) (tg2 g) a c b d + Rlow s (tg1 g) (tg2 g) a d b c)) := by
  set G1 := tg1 g
  set G2 := tg2 g
  have h1 : ∀ a b c, G1 a b c = G1 b a c := tg1_symm g hsym
  have h2a : ∀ a b c d, G2 a b c d = G2 b a c d := tg2_symm1 g hsym
  have h2b : ∀ a b c d, G2 a b c d = G2 a b d c := tg2_symm2 g hg
  obtain ⟨hx, hx0, hJ0, hB, hC⟩ := xP_jets (Bc s G1) (Cc s G1 G2) (Bc_symm s G1 h1)
    (Cc_symm1 s G1 G2) (Cc_symm2 s G1 G2)
  set M := pullG g (xNC s g) with hMdef
  have hM : Sm M := Sm_pullG g _ hg hx
  have hg0' : g 0 = eta s := by rw [hg0]; funext a b; simp [Matrix.diagonal_apply, eta]
  have hM0 : M 0 = Matrix.diagonal s := by rw [hMdef, xNC, pullG_zero g _ hx0 hJ0, hg0]
  have hD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [hs]; exact Matrix.diagonal_one
  have hdet : IsUnit (M 0).det := by rw [hM0]; exact Matrix.isUnit_det_of_left_inverse hD
  have hinv : (M 0)⁻¹ = Matrix.diagonal s := by rw [hM0]; exact Matrix.inv_eq_left_inv hD
  -- first derivatives of `g'` at `0`
  have hd : ∀ c a b, dg M 0 c a b = 0 := fun c a b => by
    simp only [dg, hMdef, xNC]
    rw [pd_pullG_zero g _ hg hx _ hx0 hJ0 hB, hg0']
    exact pull1_zero s hs G1 h1 a b c
  -- second derivatives of `g'` at `0`
  have hh : ∀ i j k l, pd (fun y => pd (fun y => M y i j) y k) 0 l = hNC s G1 G2 i j k l :=
    fun i j k l => by
      simp only [hMdef, xNC]
      rw [pd_pd_pullG_zero g _ hg hx _ _ hx0 hJ0 hB hC, hg0']; rfl
  have hdchr : ∀ a b c d, pd (fun y => chr M y a b c) 0 d = s a * dΓ (hNC s G1 G2) a b c d :=
    fun a b c d => by
      rw [(chr_flat_point hM hdet hd a b c d).2, hinv]
      simp only [dg, hh, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, dΓ]
      ring
  refine ⟨hM0, hd, fun a b c => (chr_flat_point hM hdet hd a b c 0).1, fun a b c d => ?_,
    fun a b c d => ?_⟩
  · rw [hdchr, hdchr, hdchr]
    have := gauge_hNC s hs G1 G2 h1 h2a h2b a b c d
    simp only [gauge] at this
    linear_combination s a * this
  · rw [hh]; exact second_derivative_riemann s hs G1 G2 h1 h2a h2b a b c d

/-! ### `Rlow` is the lowered `Curved.riem` of the original metric -/

lemma Gam_pair (t : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ) (a e d : Fin (n+1)) :
    Gam (sym1 t) e d a + Gam (sym1 t) a d e = sym1 t a e d := by
  simp only [Gam, sym1]; ring

lemma riem_body (s : Fin (n+1) → ℝ) (t : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (a b c d e : Fin (n+1)) :
    -(s e * sym1 t a e c * Gam (sym1 t) e d b) + s e * sym1 t a e d * Gam (sym1 t) e c b
      + s e * Gam (sym1 t) a c e * Gam (sym1 t) e d b
      - s e * Gam (sym1 t) a d e * Gam (sym1 t) e c b
      = s e * (Gam (sym1 t) e a d * Gam (sym1 t) e c b - Gam (sym1 t) e a c * Gam (sym1 t) e d b) := by
  simp only [Gam, sym1]; ring

/-- For a smooth symmetric metric with `g(0) = diag(s)`: `Γ^a_bc(0) = s_a Γ_abc`. -/
lemma chr_zero_eq (g : E → Mat) (hsym : ∀ y, (g y).IsSymm) (s : Fin (n+1) → ℝ)
    (hs : ∀ a, s a * s a = 1) (hg0 : g 0 = Matrix.diagonal s) (a b c : Fin (n+1)) :
    chr g 0 a b c = s a * Gam (tg1 g) a b c := by
  have hD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp only [hs]; exact Matrix.diagonal_one
  have hdet : IsUnit (g 0).det := by rw [hg0]; exact Matrix.isUnit_det_of_left_inverse hD
  have h := lower_chr g 0 hdet a b c
  simp only [hg0, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true] at h
  simp only [Gam, tg1]
  rw [show pd (fun z => g z a b) 0 c = dg g 0 c a b from rfl,
    show pd (fun z => g z a c) 0 b = dg g 0 b a c from rfl,
    show pd (fun z => g z b c) 0 a = dg g 0 a b c from rfl, dg_symm g hsym 0 a b c]
  linear_combination (-(chr g 0 a b c)) * hs a + s a * h + (-(s a) / 2) * dg_symm g hsym 0 a b c

/-- `∂_dΓ^a_bc(0) = s_a (∂_dΓ_abc − s_e ∂_d g_ae Γ_ebc)` for the original metric. -/
lemma pd_chr_zero (g : E → Mat) (hg : Sm g) (hsym : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (s : Fin (n+1) → ℝ) (hs : ∀ a, s a * s a = 1)
    (hg0 : g 0 = Matrix.diagonal s) (a b c d : Fin (n+1)) :
    pd (fun y => chr g y a b c) 0 d
      = s a * (dΓ (tg2 g) a b c d - ∑ e, s e * tg1 g a e d * Gam (tg1 g) e b c) := by
  have hD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp only [hs]; exact Matrix.diagonal_one
  have hinv0 : (g 0)⁻¹ = Matrix.diagonal s := by rw [hg0]; exact Matrix.inv_eq_left_inv hD
  have hI : ∀ a e, Differentiable ℝ fun y => (g y)⁻¹ a e := fun a e =>
    diff_of_smooth (hg.inv hdet a e)
  have hdg : ∀ c a b, Differentiable ℝ fun y => dg g y c a b := fun c a b =>
    diff_of_smooth (contDiff_pd (hg a b) c)
  have hS : ∀ e', Differentiable ℝ fun y => dg g y b e' c + dg g y c e' b - dg g y e' b c :=
    fun e' => ((hdg b e' c).fun_add (hdg c e' b)).fun_sub (hdg e' b c)
  have hpinv : ∀ e', pd (fun y => (g y)⁻¹ a e') 0 d
      = -(s a * s e' * (Gam (tg1 g) e' d a + Gam (tg1 g) a d e')) := fun e' => by
    have h := congrArg (fun M => M a e') (pdM_inv hg hsym hdet 0 d)
    simp only [pdM, Matrix.of_apply, hinv0, Matrix.neg_apply, Matrix.add_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Gm, Matrix.transpose_apply] at h
    rw [h, chr_zero_eq g hsym s hs hg0, chr_zero_eq g hsym s hs hg0]; ring
  unfold chr
  rw [pd_const_mul _ (Differentiable.fun_sum fun e' _ => (hI a e').fun_mul (hS e')),
    pd_sum _ (fun e' => (hI a e').fun_mul (hS e'))]
  simp only [pd_mul (hI a _) (hS _), hpinv, pd_sub ((hdg b _ c).fun_add (hdg c _ b)) (hdg _ b c),
    pd_add (hdg b _ c) (hdg c _ b), hinv0, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have e1 : ∀ e', dg g 0 b e' c + dg g 0 c e' b - dg g 0 e' b c = 2 * Gam (tg1 g) e' b c :=
    fun e' => by simp only [dg, Gam, tg1]; ring
  have hsum : ∑ e', -(s a * s e' * (Gam (tg1 g) e' d a + Gam (tg1 g) a d e'))
        * (dg g 0 b e' c + dg g 0 c e' b - dg g 0 e' b c)
      = -(2 * (s a * ∑ e', s e' * tg1 g a e' d * Gam (tg1 g) e' b c)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e' _ => ?_
    have hp := Gam_pair (tg1 g) a e' d
    rw [sym1_eq (tg1_symm g hsym)] at hp
    rw [e1, ← hp]; ring
  rw [hsum]
  simp only [dΓ, dg, tg2]
  ring

/-- **`Rlow` is the Riemann tensor of the original metric**, lowered with `g(0) = diag(s)`:
`s_a · riem g 0 a b c d = Rlow`. -/
theorem riem_lowered (g : E → Mat) (hg : Sm g) (hsym : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (s : Fin (n+1) → ℝ) (hs : ∀ a, s a * s a = 1)
    (hg0 : g 0 = Matrix.diagonal s) (a b c d : Fin (n+1)) :
    s a * riem g 0 a b c d = Rlow s (tg1 g) (tg2 g) a b c d := by
  set G1 := tg1 g
  have h1 : ∀ a b c, G1 a b c = G1 b a c := tg1_symm g hsym
  have e3 : ∀ c d, ∑ f, chr g 0 a c f * chr g 0 f d b
      = s a * ∑ f, s f * Gam G1 a c f * Gam G1 f d b := fun c d => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by
      rw [chr_zero_eq g hsym s hs hg0, chr_zero_eq g hsym s hs hg0]; ring
  have hsum : -(∑ e, s e * G1 a e c * Gam G1 e d b) + ∑ e, s e * G1 a e d * Gam G1 e c b
      + ∑ e, s e * Gam G1 a c e * Gam G1 e d b - ∑ e, s e * Gam G1 a d e * Gam G1 e c b
      = ∑ e, s e * (Gam G1 e a d * Gam G1 e c b - Gam G1 e a c * Gam G1 e d b) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := riem_body s G1 a b c d e
    rwa [sym1_eq h1] at this
  unfold riem
  rw [pd_chr_zero g hg hsym hdet s hs hg0, pd_chr_zero g hg hsym hdet s hs hg0, e3, e3, Rlow]
  linear_combination (dΓ (tg2 g) a d b c - ∑ e, s e * G1 a e c * Gam G1 e d b
      - (dΓ (tg2 g) a c b d - ∑ e, s e * G1 a e d * Gam G1 e c b)
      + ∑ f, s f * Gam G1 a c f * Gam G1 f d b - ∑ f, s f * Gam G1 a d f * Gam G1 f c b) * hs a
    + hsum

/-- **Target 3 with the project's Riemann tensor.** Same as `normal_coordinates`, with the
second derivatives of the pulled-back metric expressed through `Curved.riem g 0` of the original
metric (lowered by `g(0) = diag(s)`): `∂_c∂_d g'_ab(0) = −⅓(s_a riem_acbd + s_a riem_adbc)`.
Assumes `g` invertible everywhere, a proof convenience (`Curved.chr` uses `(g y)⁻¹`); only
invertibility near `0`, which follows from `g 0 = diag(s)`, is really needed. -/
theorem normal_coordinates_riem (g : E → Mat) (hg : Sm g) (hsym : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) (s : Fin (n+1) → ℝ) (hs : ∀ a, s a * s a = 1)
    (hg0 : g 0 = Matrix.diagonal s) (a b c d : Fin (n+1)) :
    pd (fun y => pd (fun y => pullG g (xNC s g) y a b) y c) 0 d
      = -(1/3) * (s a * riem g 0 a c b d + s a * riem g 0 a d b c) := by
  rw [riem_lowered g hg hsym hdet s hs hg0, riem_lowered g hg hsym hdet s hs hg0]
  exact (normal_coordinates g hg hsym s hs hg0).2.2.2.2 a b c d

end Genuine

end EntEq.NormalCoords
