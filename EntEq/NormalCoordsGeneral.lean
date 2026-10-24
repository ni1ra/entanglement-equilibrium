/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Closing two gaps left open in `NormalCoords`.

  * (A) `hasStrictFDerivAt_xNC`: the normal-coordinate map `xNC s g` is strictly differentiable
    at `0` with derivative the identity (it is a polynomial map whose Jacobian at `0` is `1`).
    `xNC_localHomeomorph`: the inverse function theorem then gives an `OpenPartialHomeomorph`
    whose underlying function is `xNC s g` and whose source contains `0`.
  * (B) `sylvester`: a symmetric invertible real matrix `g0` is congruent to `diag(s)`,
    `s_a = ±1`: `Lᵀ g0 L = diag(s)` with `L` invertible (orthogonal diagonalisation by the
    spectral theorem, then rescaling each column by `1/√|λ_a|`).
  * `normal_coordinates_general`: for a smooth symmetric metric field `g`, invertible
    everywhere, with no assumption on `g 0` beyond that, the map `φ = L ∘ xNC s g̃`
    (`g̃(y) = Lᵀ g(L y) L`) has `φ 0 = 0`, strict derivative `L` (invertible) at `0`, is a local
    homeomorphism near `0`, and the pull-back of `g` along `φ` is normal to second order at `0`;
    its second derivatives are `−⅓` of the Riemann tensor of `g̃`, i.e. of `g` written in the
    linearly changed coordinates `y ↦ L y` (the tensorial transformation of `riem` under a
    linear change of coordinates is not proved here).

  Not covered here: Taylor remainders, geodesics and the exponential map. (`InverseSmooth`
  shows the local inverse is `C^∞` at the image of `0`; `RiemannLinear` gives the tensorial law
  of `riem` under the linear change.)
-/
import EntEq.NormalCoords
import Mathlib.Analysis.Matrix.Spectrum

namespace EntEq.NormalCoords

open Matrix

/-! ### (B) Sylvester's step: congruence of a symmetric invertible matrix to `diag(±1)` -/

/-- **Sylvester step.** A real symmetric invertible matrix is congruent to a diagonal matrix of
signs: there are an invertible `L` and `s` with `s_a² = 1` such that `Lᵀ g0 L = diag(s)`. -/
theorem sylvester {m : ℕ} (g0 : Matrix (Fin m) (Fin m) ℝ) (hsym : g0.IsSymm)
    (hdet : IsUnit g0.det) :
    ∃ (L : Matrix (Fin m) (Fin m) ℝ) (s : Fin m → ℝ),
      IsUnit L.det ∧ (∀ a, s a * s a = 1) ∧ Lᵀ * g0 * L = diagonal s := by
  have hA : g0.IsHermitian := by
    unfold Matrix.IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hsym
  set U : Matrix (Fin m) (Fin m) ℝ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
    with hU
  set lam := hA.eigenvalues
  have hstar : (star hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hdiag : Uᵀ * g0 * U = diagonal lam := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply, hstar] at h
    rw [h]; congr 1
  have hUU : Uᵀ * U = 1 := by
    rw [← hstar]; exact Unitary.coe_star_mul_self _
  have hlam : ∀ a, lam a ≠ 0 := by
    intro a ha
    have h := hA.det_eq_prod_eigenvalues
    have : g0.det = 0 := by
      rw [h]; exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [lam] at ha ⊢; exact ha)
    exact hdet.ne_zero this
  set d : Fin m → ℝ := fun a => 1 / Real.sqrt |lam a|
  refine ⟨U * diagonal d, fun a => lam a / |lam a|, ?_, ?_, ?_⟩
  · rw [det_mul]
    refine (isUnit_det_of_left_inverse hUU).mul ?_
    rw [det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    simp only [d, one_div, ne_eq, inv_eq_zero]
    exact (Real.sqrt_pos.2 (abs_pos.2 (hlam a))).ne'
  · intro a
    have : |lam a| ≠ 0 := abs_ne_zero.2 (hlam a)
    rw [div_mul_div_comm, ← abs_mul_abs_self (lam a), div_self (mul_ne_zero this this)]
  · rw [transpose_mul, diagonal_transpose,
      show diagonal d * Uᵀ * g0 * (U * diagonal d) = diagonal d * (Uᵀ * g0 * U) * diagonal d by
        simp only [Matrix.mul_assoc],
      hdiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext a
    have hp : 0 < |lam a| := abs_pos.2 (hlam a)
    have hs : Real.sqrt |lam a| * Real.sqrt |lam a| = |lam a| := Real.mul_self_sqrt hp.le
    have hq : Real.sqrt |lam a| ≠ 0 := (Real.sqrt_pos.2 hp).ne'
    simp only [d]
    field_simp
    rw [Real.sq_sqrt hp.le]; ring

section Genuine

open EntEq.Curved
open scoped ContDiff

variable {n : ℕ}
local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

/-! ### (A) `xNC` is a local diffeomorphism near `0` -/

lemma xNC_jets (g : E → Mat) (hsym : ∀ y, (g y).IsSymm) (s : Fin (n+1) → ℝ) :
    (∀ c, ContDiff ℝ ∞ fun y => xNC s g y c) ∧ xNC s g 0 = 0 ∧
    (∀ a i, Jx (xNC s g) a i 0 = if a = i then 1 else 0) := by
  have h1 := tg1_symm g hsym
  obtain ⟨hx, hx0, hJ0, -, -⟩ := xP_jets (Bc s (tg1 g)) (Cc s (tg1 g) (tg2 g))
    (Bc_symm s _ h1) (Cc_symm1 s _ _) (Cc_symm2 s _ _)
  exact ⟨hx, hx0, hJ0⟩

/-- A smooth map whose Jacobian at `0` is the identity has derivative `id` at `0`. -/
lemma fderiv_eq_id_of_Jx (x : E → E) (hx : ∀ c, Differentiable ℝ fun y => x y c)
    (hJ0 : ∀ a i, Jx x a i 0 = if a = i then 1 else 0) :
    fderiv ℝ x 0 = ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.coe_injective
  refine (Pi.basisFun ℝ (Fin (n+1))).ext fun i => ?_
  rw [Pi.basisFun_apply, ContinuousLinearMap.coe_coe, fderiv_pi (fun c => hx c 0)]
  funext a
  have := hJ0 a i
  simp only [Jx, pd] at this
  simp only [ContinuousLinearMap.pi_apply, this]
  simp [Pi.single_apply, eq_comm]

/-- **(A) Strict derivative of `xNC` at `0` is the identity.** -/
theorem hasStrictFDerivAt_xNC (g : E → Mat) (hsym : ∀ y, (g y).IsSymm)
    (s : Fin (n+1) → ℝ) :
    HasStrictFDerivAt (xNC s g) (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 := by
  obtain ⟨hx, -, hJ0⟩ := xNC_jets g hsym s
  have hcd : ContDiff ℝ ∞ (xNC s g) := contDiff_pi.2 hx
  have h := (hcd.contDiffAt (x := 0)).hasStrictFDerivAt (by simp)
  rwa [fderiv_eq_id_of_Jx _ (fun c => (hx c).differentiable (by simp)) hJ0] at h

/-- **(A) `xNC s g` is a local homeomorphism near `0`** (inverse function theorem). -/
theorem xNC_localHomeomorph (g : E → Mat) (hsym : ∀ y, (g y).IsSymm)
    (s : Fin (n+1) → ℝ) :
    ∃ φ : OpenPartialHomeomorph E E, ⇑φ = xNC s g ∧ (0 : E) ∈ φ.source :=
  ⟨(hasStrictFDerivAt_xNC g hsym s).toOpenPartialHomeomorph _, rfl,
    (hasStrictFDerivAt_xNC g hsym s).mem_toOpenPartialHomeomorph_source⟩

/-! ### Linear change of coordinates for metric fields -/

/-- The metric in the linearly changed coordinates `x = L y`: `g̃(y) = Lᵀ g(L y) L`. -/
noncomputable def linG (L : Mat) (g : E → Mat) (y : E) : Mat := Lᵀ * g (L *ᵥ y) * L

/-- The general normal-coordinate map `φ = L ∘ xNC s g̃`. -/
noncomputable def phiNC (L : Mat) (s : Fin (n+1) → ℝ) (g : E → Mat) (y : E) : E :=
  L *ᵥ xNC s (linG L g) y

lemma contDiff_mulVec (L : Mat) : ContDiff ℝ ∞ (fun y : E => L *ᵥ y) :=
  contDiff_pi.2 fun a => by simp only [mulVec, dotProduct]; fun_prop

lemma Sm_linG (L : Mat) (g : E → Mat) (hg : Sm g) : Sm (linG L g) := by
  intro i j
  have hc : ∀ a b, ContDiff ℝ ∞ fun y => g (L *ᵥ y) a b :=
    fun a b => (hg a b).comp (contDiff_mulVec L)
  simp only [linG, Matrix.mul_apply, transpose_apply]
  exact ContDiff.sum fun a _ =>
    (ContDiff.sum fun b _ => contDiff_const.mul (hc b a)).mul contDiff_const

lemma linG_symm (L : Mat) (g : E → Mat) (hsym : ∀ y, (g y).IsSymm) (y : E) :
    (linG L g y).IsSymm := by
  unfold IsSymm linG
  rw [transpose_mul, transpose_mul, transpose_transpose, (hsym _).eq, Matrix.mul_assoc]

lemma linG_det (L : Mat) (hL : IsUnit L.det) (g : E → Mat) (hdet : ∀ y, IsUnit (g y).det)
    (y : E) : IsUnit (linG L g y).det := by
  simp only [linG, det_mul, det_transpose]
  exact (hL.mul (hdet _)).mul hL

/-- `pullG` in matrix form: `g'(y) = Dx(y)ᵀ g(x(y)) Dx(y)`. -/
lemma pullG_eq_mat (g : E → Mat) (x : E → E) (y : E) :
    pullG g x y
      = (Matrix.of fun a i => Jx x a i y)ᵀ * g (x y) * Matrix.of fun a i => Jx x a i y := by
  ext i j
  simp only [pullG, Matrix.of_apply, Matrix.mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

lemma Jx_mulVec (L : Mat) (x : E → E) (hx : ∀ c, Differentiable ℝ fun y => x y c)
    (a i : Fin (n+1)) (y : E) :
    Jx (fun z => L *ᵥ x z) a i y = ∑ b, L a b * Jx x b i y := by
  unfold Jx
  simp only [mulVec, dotProduct]
  rw [pd_sum (fun b z => L a b * x z b) (fun b => (hx b).const_mul _)]
  exact Finset.sum_congr rfl fun b _ => pd_const_mul _ (hx b)

/-- Pulling `g` back along `L ∘ x` is pulling `g̃ = Lᵀ g(L ·) L` back along `x`. -/
lemma pullG_mulVec (L : Mat) (g : E → Mat) (x : E → E)
    (hx : ∀ c, Differentiable ℝ fun y => x y c) (y : E) :
    pullG g (fun z => L *ᵥ x z) y = pullG (linG L g) x y := by
  rw [pullG_eq_mat, pullG_eq_mat]
  have hJ : (Matrix.of fun a i => Jx (fun z => L *ᵥ x z) a i y)
      = L * Matrix.of fun a i => Jx x a i y := by
    ext a i; simp [Jx_mulVec L x hx, Matrix.mul_apply]
  rw [hJ, linG, transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **Normal coordinates for an arbitrary non-degenerate metric field.** Let `g` be a smooth
symmetric matrix field on `ℝ^(n+1)`, invertible everywhere (no condition on `g 0` beyond that).
Then there are an invertible matrix `L` and signs `s` (`s_a² = 1`) such that, with
`g̃(y) = Lᵀ g(L y) L` and `φ = phiNC L s g = L ∘ xNC s g̃`:
`g̃ 0 = diag(s)`; `φ 0 = 0`; `φ` has strict derivative `L` (a linear equivalence) at `0` and is
a local homeomorphism near `0`; and the pull-back `g' = Dφᵀ g(φ) Dφ` has `g'(0) = diag(s)`,
`∂g'(0) = 0`, `Γ'(0) = 0`, symmetrised `∂Γ'(0) = 0`, and
`∂_c∂_d g'_ab(0) = −⅓(s_a R̃_acbd + s_a R̃_adbc)` with `R̃ = riem g̃ 0`, the Riemann tensor of
`g` in the linear coordinates `x = L y` (rewritten through `riem g 0` in
`RiemannLinear.normal_coordinates_general_riem`). -/
theorem normal_coordinates_general (g : E → Mat) (hg : Sm g) (hsym : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) :
    ∃ (L : Mat) (s : Fin (n+1) → ℝ) (L' : E ≃L[ℝ] E),
      IsUnit L.det ∧ (∀ a, s a * s a = 1) ∧ (∀ v, L' v = L *ᵥ v) ∧
      linG L g 0 = diagonal s ∧ phiNC L s g 0 = 0 ∧
      HasStrictFDerivAt (phiNC L s g) (L' : E →L[ℝ] E) 0 ∧
      (∃ ψ : OpenPartialHomeomorph E E, ⇑ψ = phiNC L s g ∧ (0 : E) ∈ ψ.source) ∧
      pullG g (phiNC L s g) 0 = diagonal s ∧
      (∀ c a b, dg (pullG g (phiNC L s g)) 0 c a b = 0) ∧
      (∀ a b c, chr (pullG g (phiNC L s g)) 0 a b c = 0) ∧
      (∀ a b c d, pd (fun y => chr (pullG g (phiNC L s g)) y a b c) 0 d
        + pd (fun y => chr (pullG g (phiNC L s g)) y a c d) 0 b
        + pd (fun y => chr (pullG g (phiNC L s g)) y a d b) 0 c = 0) ∧
      (∀ a b c d, pd (fun y => pd (fun y => pullG g (phiNC L s g) y a b) y c) 0 d
        = -(1/3) * (s a * riem (linG L g) 0 a c b d + s a * riem (linG L g) 0 a d b c)) := by
  obtain ⟨L, s, hL, hs, hL0⟩ := sylvester (g 0) (hsym 0) (hdet 0)
  set gt := linG L g with hgt
  have hgtS : Sm gt := Sm_linG L g hg
  have hgtsym : ∀ y, (gt y).IsSymm := linG_symm L g hsym
  have hgtdet : ∀ y, IsUnit (gt y).det := linG_det L hL g hdet
  have hgt0 : gt 0 = diagonal s := by simp only [hgt, linG, mulVec_zero, hL0]
  let L' : E ≃L[ℝ] E :=
    (Matrix.toLinearEquiv' L (L.invertibleOfIsUnitDet hL)).toContinuousLinearEquiv
  have hL' : ∀ v, L' v = L *ᵥ v := fun v => rfl
  obtain ⟨hx, hx0, -⟩ := xNC_jets gt hgtsym s
  have hxd : ∀ c, Differentiable ℝ fun y => xNC s gt y c :=
    fun c => (hx c).differentiable (by simp)
  have hpull : pullG g (phiNC L s g) = pullG gt (xNC s gt) :=
    funext fun y => pullG_mulVec L g (xNC s gt) hxd y
  have hstrict : HasStrictFDerivAt (phiNC L s g) (L' : E →L[ℝ] E) 0 := by
    have h := (L' : E →L[ℝ] E).hasStrictFDerivAt.comp (0 : E) (hasStrictFDerivAt_xNC gt hgtsym s)
    rw [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.comp_id] at h
    convert h using 1
    funext y; simp [phiNC, hL', hgt]
  obtain ⟨n0, n1, n2, n3, -⟩ := normal_coordinates gt hgtS hgtsym s hs hgt0
  refine ⟨L, s, L', hL, hs, hL', hgt0, ?_, hstrict,
    ⟨hstrict.toOpenPartialHomeomorph _, rfl, hstrict.mem_toOpenPartialHomeomorph_source⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [phiNC, ← hgt, hx0]
  · rw [hpull]; exact n0
  · rw [hpull]; exact n1
  · rw [hpull]; exact n2
  · rw [hpull]; exact n3
  · rw [hpull]; exact normal_coordinates_riem gt hgtS hgtsym hgtdet s hs hgt0

end Genuine

end EntEq.NormalCoords
