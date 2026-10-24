/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Volume of a small geodesic ball (Jacobson 2016, eq. 3)

In Riemann normal coordinates the spatial metric is `g_ij(x) = δ_ij − (1/3) R_ikjl x^k x^l + O(|x|³)`,
so `√det g = 1 − (1/6) R_kl x^k x^l + O(|x|³)` and the volume of the geodesic ball `B_ℓ` falls
short of the flat value by `δV = −Ω ℓ^{D+2} R/(6 D (D+2)) + O(ℓ^{D+3})`.

**Proved here** (no premises beyond Mathlib):
* `integral_ball_coord_mul`: `∫_{B_ℓ} x_k x_l = δ_kl vol(B_ℓ) ℓ²/(D+2)` on `EuclideanSpace ℝ (Fin D)`,
  via polar coordinates (`integral_fun_norm_addHaar`), a reflection and a coordinate swap.
* `hasDerivAt_sqrt_det_one_add_smul`: `d/dε √det(1 + εA)|₀ = tr A / 2`.
* `hasDerivAt_sqrt_det_rnc`: for `g = 1 − ε M(x)/3` with `M(x)_ij = R_ikjl x^k x^l` (and `ε = t²`
  along the ray `t x`, `rncQuad_smul`), the first-order coefficient of `√det g` is
  `−(1/6) R_kl x^k x^l`, i.e. exactly the correction term of `linDensity (ricci R)`.
* `volume_deficit` / `volume_deficit_spacetime`: integrating that linearized density over `B_ℓ`
  gives `vol(B_ℓ) − Ω ℓ^{D+2} R/(6 D (D+2))` exactly, with `Ω` Mathlib's unit-sphere measure;
  in spacetime dimension `d = D + 1` this is the `δV` that `Ball2016.area_deficit_fixed_volume`
  assumes.

**Not proved (modelling premise):** Mathlib has no Riemannian normal coordinates, so the
expansion `g_ij = δ_ij − (1/3) R_ikjl x^k x^l + O(|x|³)` itself, and the claim that the
`O(|x|³)` remainder of `√det g` contributes only `O(ℓ^{D+3})` to the volume, are not formalized.
The results below compute the leading term exactly given that expansion; no symmetry of the
Ricci array is needed, since only its trace survives.
-/

open MeasureTheory Metric Set

noncomputable section

namespace EntEq.BallVol

local notation "E" D => EuclideanSpace ℝ (Fin D)

lemma integrableOn_ball_of_continuous {D : ℕ} {f : (E D) → ℝ} (hf : Continuous f) (ℓ : ℝ) :
    IntegrableOn f (ball (0 : E D) ℓ) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 ℓ)).mono_set ball_subset_closedBall

/-- Radial moments: `∫_{B_ℓ} |x|^p = D · vol(B_1) · ℓ^{D+p}/(D+p)` (polar coordinates). -/
theorem integral_ball_norm_pow {D : ℕ} (hD : 1 ≤ D) (p : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫ x in ball (0 : E D) ℓ, ‖x‖ ^ p
      = D * volume.real (ball (0 : E D) 1) * (ℓ ^ (D + p) / (D + p)) := by
  have : Nontrivial (E D) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have h1 : ∫ x in ball (0 : E D) ℓ, ‖x‖ ^ p
      = ∫ x : E D, (Iio ℓ).indicator (fun r : ℝ => r ^ p) ‖x‖ := by
    rw [← integral_indicator measurableSet_ball]
    congr 1; ext x
    simp [indicator]
  rw [h1, integral_fun_norm_addHaar volume, finrank_euclideanSpace_fin]
  have h2 : ∫ y in Ioi (0:ℝ), y ^ (D - 1) • (Iio ℓ).indicator (fun r : ℝ => r ^ p) y
      = ∫ y in Ioi (0:ℝ), (Iio ℓ).indicator (fun r : ℝ => r ^ (D - 1 + p)) y := by
    congr 1; ext y
    by_cases hy : y < ℓ <;> simp [indicator, hy, pow_add]
  rw [h2, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hℓ, integral_pow]
  have hp : D - 1 + p + 1 = D + p := by omega
  rw [hp, zero_pow (by omega), sub_zero, nsmul_eq_mul, smul_eq_mul]
  push_cast [Nat.cast_sub hD]
  ring

/-- `vol(B_ℓ) = vol(B_1) ℓ^D`, read off the radial formula with `p = 0`. -/
theorem volume_ball_eq {D : ℕ} (hD : 1 ≤ D) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    volume.real (ball (0 : E D) ℓ) = volume.real (ball (0 : E D) 1) * ℓ ^ D := by
  have h := integral_ball_norm_pow hD 0 hℓ
  simp only [pow_zero, setIntegral_const, smul_eq_mul, mul_one, add_zero] at h
  have : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  rw [h, Nat.cast_zero, add_zero]
  field_simp

/-- `∫_{B_ℓ} |x|² = D/(D+2) · vol(B_ℓ) · ℓ²`. -/
theorem integral_ball_norm_sq {D : ℕ} (hD : 1 ≤ D) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫ x in ball (0 : E D) ℓ, ‖x‖ ^ 2
      = D / (D + 2) * volume.real (ball (0 : E D) ℓ) * ℓ ^ 2 := by
  rw [integral_ball_norm_pow hD 2 hℓ, volume_ball_eq hD hℓ]
  have : (D : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring


/-- A linear isometry fixes the ball, so it leaves integrals over the ball unchanged. -/
lemma setIntegral_ball_comp_isometry {D : ℕ} (T : (E D) ≃ₗᵢ[ℝ] (E D)) (f : (E D) → ℝ) (ℓ : ℝ) :
    ∫ x in ball (0 : E D) ℓ, f (T x) = ∫ x in ball (0 : E D) ℓ, f x := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
    ← T.measurePreserving.integral_comp' (f := T.toMeasurableEquiv)
      ((ball (0 : E D) ℓ).indicator f)]
  congr 1; ext x
  simp [indicator]

/-- The reflection `x_k ↦ −x_k`. -/
def reflect {D : ℕ} (k : Fin D) : (E D) ≃ₗᵢ[ℝ] (E D) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = k then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma reflect_apply {D : ℕ} (k i : Fin D) (x : E D) :
    reflect k x i = if i = k then -x i else x i := by
  by_cases h : i = k <;> simp [reflect, h]

/-- Off-diagonal second moments vanish (reflection `x_k ↦ −x_k`). -/
theorem integral_ball_coord_mul_of_ne {D : ℕ} {k l : Fin D} (hkl : k ≠ l) (ℓ : ℝ) :
    ∫ x in ball (0 : E D) ℓ, x k * x l = 0 := by
  have h := setIntegral_ball_comp_isometry (reflect k) (fun x => x k * x l) ℓ
  simp only [reflect_apply, ite_true, Ne.symm hkl, ite_false, neg_mul, integral_neg] at h
  linarith

/-- All diagonal second moments are equal (coordinate swap). -/
theorem integral_ball_coord_sq_eq {D : ℕ} (k l : Fin D) (ℓ : ℝ) :
    ∫ x in ball (0 : E D) ℓ, x k ^ 2 = ∫ x in ball (0 : E D) ℓ, x l ^ 2 := by
  rw [← setIntegral_ball_comp_isometry
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap k l)) (fun x => x k ^ 2) ℓ]
  congr 1; ext x
  simp

/-- Diagonal second moment: `∫_{B_ℓ} x_k² = vol(B_ℓ) ℓ²/(D+2)`. -/
theorem integral_ball_coord_sq {D : ℕ} (k : Fin D) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫ x in ball (0 : E D) ℓ, x k ^ 2 = volume.real (ball (0 : E D) ℓ) * ℓ ^ 2 / (D + 2) := by
  have hD : 1 ≤ D := by have := k.pos; omega
  have hsum : ∫ x in ball (0 : E D) ℓ, ‖x‖ ^ 2 = ∑ i, ∫ x in ball (0 : E D) ℓ, x i ^ 2 := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    exact integral_finsetSum _ (fun i _ => integrableOn_ball_of_continuous (by fun_prop) ℓ)
  have heq : ∑ i, ∫ x in ball (0 : E D) ℓ, x i ^ 2 = D * ∫ x in ball (0 : E D) ℓ, x k ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => integral_ball_coord_sq_eq i k ℓ)]
    simp
  rw [integral_ball_norm_sq hD hℓ, heq] at hsum
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hD2 : (D : ℝ) + 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hD0
  rw [← hsum]
  field_simp

/-- **Second-moment identity on a Euclidean ball.**
`∫_{B_ℓ} x_k x_l dx = δ_kl · vol(B_ℓ) · ℓ²/(D+2)`, for every dimension `D` and radius `ℓ ≥ 0`. -/
theorem integral_ball_coord_mul {D : ℕ} (k l : Fin D) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫ x in ball (0 : E D) ℓ, x k * x l
      = if k = l then volume.real (ball (0 : E D) ℓ) * ℓ ^ 2 / (D + 2) else 0 := by
  split_ifs with h
  · subst h
    simp_rw [← sq]
    exact integral_ball_coord_sq k hℓ
  · exact integral_ball_coord_mul_of_ne h ℓ

/-! ### First-order determinant -/

/-- `d/dε det(1 + εA)|₀ = tr A`. -/
theorem hasDerivAt_det_one_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : HasDerivAt (fun ε : ℝ => (1 + ε • A).det) A.trace 0 := by
  obtain ⟨q, hq⟩ : ∃ q : Polynomial ℝ,
      ∀ ε : ℝ, (1 + ε • A).det = 1 + A.trace * ε + q.eval ε * ε ^ 2 :=
    ⟨_, fun ε => Matrix.det_one_add_smul ε A⟩
  simp_rw [hq]
  have h := (((hasDerivAt_id' (0:ℝ)).const_mul A.trace).const_add 1).add
    ((q.hasDerivAt 0).mul ((hasDerivAt_id' (0:ℝ)).pow 2))
  convert h using 1
  simp

/-- `√det(1 + εA) = 1 + ε tr A / 2 + o(ε)`, stated as a derivative at `ε = 0`. -/
theorem hasDerivAt_sqrt_det_one_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : HasDerivAt (fun ε : ℝ => √(1 + ε • A).det) (A.trace / 2) 0 := by
  have h := (hasDerivAt_det_one_add_smul A).sqrt (by simp)
  simpa using h

/-! ### Assembly: the Riemann-normal-coordinate metric -/

/-- Ricci contraction `R_kl = Σ_i R_ikil` of a Riemann-type array. -/
def ricci {D : ℕ} (Riem : Fin D → Fin D → Fin D → Fin D → ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  fun k l => ∑ i, Riem i k i l

/-- The quadratic metric perturbation `M(x)_ij = R_ikjl x^k x^l`; the Riemann-normal-coordinate
metric is `g(x) = 1 − M(x)/3 + O(|x|³)`. -/
def rncQuad {D : ℕ} (Riem : Fin D → Fin D → Fin D → Fin D → ℝ) (x : E D) :
    Matrix (Fin D) (Fin D) ℝ :=
  fun i j => ∑ k, ∑ l, Riem i k j l * x k * x l

/-- `M` is quadratic: along the ray `t x`, `M(t x) = t² M(x)`, so `g(t x) = 1 + t² (−M(x)/3)`. -/
lemma rncQuad_smul {D : ℕ} (Riem : Fin D → Fin D → Fin D → Fin D → ℝ) (t : ℝ) (x : E D) :
    rncQuad Riem (t • x) = t ^ 2 • rncQuad Riem x := by
  ext i j
  simp only [rncQuad, Matrix.smul_apply, smul_eq_mul, PiLp.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `tr M(x) = R_kl x^k x^l`. -/
lemma trace_rncQuad {D : ℕ} (Riem : Fin D → Fin D → Fin D → Fin D → ℝ) (x : E D) :
    (rncQuad Riem x).trace = ∑ k, ∑ l, ricci Riem k l * x k * x l := by
  simp only [Matrix.trace, Matrix.diag, rncQuad, ricci, Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun k _ => Finset.sum_comm)

/-- Pointwise first order: with `ε = t²` along the ray `t x`,
`√det(1 − ε M(x)/3) = 1 − ε R_kl x^k x^l / 6 + o(ε)`. -/
theorem hasDerivAt_sqrt_det_rnc {D : ℕ} (Riem : Fin D → Fin D → Fin D → Fin D → ℝ) (x : E D) :
    HasDerivAt (fun ε : ℝ => √(1 + ε • (-(1/3 : ℝ)) • rncQuad Riem x).det)
      (-(1/6) * ∑ k, ∑ l, ricci Riem k l * x k * x l) 0 := by
  convert hasDerivAt_sqrt_det_one_add_smul ((-(1/3 : ℝ)) • rncQuad Riem x) using 1
  rw [Matrix.trace_smul, trace_rncQuad, smul_eq_mul]
  ring

/-- The linearized volume density `1 − (1/6) R_kl x^k x^l`. -/
def linDensity {D : ℕ} (Ric : Matrix (Fin D) (Fin D) ℝ) (x : E D) : ℝ :=
  1 - 1 / 6 * ∑ k, ∑ l, Ric k l * x k * x l

/-- `∫_{B_ℓ} R_kl x^k x^l = tr R · vol(B_ℓ) ℓ²/(D+2)`. -/
theorem integral_ball_ricci_form {D : ℕ} (Ric : Matrix (Fin D) (Fin D) ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫ x in ball (0 : E D) ℓ, ∑ k, ∑ l, Ric k l * x k * x l
      = Ric.trace * (volume.real (ball (0 : E D) ℓ) * ℓ ^ 2 / (D + 2)) := by
  have hint : ∀ k l, IntegrableOn (fun x : E D => Ric k l * x k * x l) (ball 0 ℓ) :=
    fun k l => integrableOn_ball_of_continuous (by fun_prop) ℓ
  have hmom : ∀ k l, ∫ x in ball (0 : E D) ℓ, Ric k l * x k * x l
      = Ric k l * (if k = l then volume.real (ball (0 : E D) ℓ) * ℓ ^ 2 / (D + 2) else 0) := by
    intro k l
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_ball_coord_mul k l hℓ]
  calc ∫ x in ball (0 : E D) ℓ, ∑ k, ∑ l, Ric k l * x k * x l
      = ∑ k, ∫ x in ball (0 : E D) ℓ, ∑ l, Ric k l * x k * x l :=
        integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => hint k l)
    _ = ∑ k, ∑ l, ∫ x in ball (0 : E D) ℓ, Ric k l * x k * x l :=
        Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => hint k l
    _ = ∑ k, ∑ l, Ric k l * (if k = l then
          volume.real (ball (0 : E D) ℓ) * ℓ ^ 2 / (D + 2) else 0) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hmom k l
    _ = _ := by simp [mul_ite, Matrix.trace, Finset.sum_mul]

/-- Integral of the linearized density:
`∫_{B_ℓ} (1 − R_kl x^k x^l/6) = vol(B_ℓ) − (1/6) R vol(B_ℓ) ℓ²/(D+2)`. -/
theorem integral_linDensity {D : ℕ} (Ric : Matrix (Fin D) (Fin D) ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫ x in ball (0 : E D) ℓ, linDensity Ric x
      = volume.real (ball (0 : E D) ℓ)
        - 1 / 6 * Ric.trace * volume.real (ball (0 : E D) ℓ) * ℓ ^ 2 / (D + 2) := by
  unfold linDensity
  rw [integral_sub (integrableOn_ball_of_continuous continuous_const ℓ)
      (integrableOn_ball_of_continuous (by fun_prop) ℓ),
    integral_const_mul, integral_ball_ricci_form Ric hℓ, setIntegral_const, smul_eq_mul, mul_one]
  ring

/-- **Leading-order volume deficit of a small ball** (Jacobson 2016, eq. 3), for the linearized
density. With `Ω` the area of the unit `(D−1)`-sphere (Mathlib's `volume.toSphere`),
`∫_{B_ℓ} (1 − R_kl x^k x^l/6) − vol(B_ℓ) = −Ω ℓ^{D+2} R/(6 D (D+2))`. -/
theorem volume_deficit {D : ℕ} (hD : 1 ≤ D) (Ric : Matrix (Fin D) (Fin D) ℝ) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) :
    (∫ x in ball (0 : E D) ℓ, linDensity Ric x) - volume.real (ball (0 : E D) ℓ)
      = -(volume : Measure (E D)).toSphere.real univ * ℓ ^ (D + 2) * Ric.trace
          / (6 * D * (D + 2)) := by
  rw [integral_linDensity Ric hℓ, volume_ball_eq hD hℓ, Measure.toSphere_real_apply_univ,
    finrank_euclideanSpace_fin]
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  have hD2 : (D : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The same deficit in the form `Ball2016.area_deficit_fixed_volume` assumes: spacetime dimension
`d = m + 2`, spatial dimension `D = m + 1`, `δV(ℓ) = −Ω ℓ^{d+1} R_s/(6(d−1)(d+1))`. -/
theorem volume_deficit_spacetime (m : ℕ) (Ric : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) :
    let d : ℝ := m + 2
    (∫ x in ball (0 : E (m + 1)) ℓ, linDensity Ric x) - volume.real (ball (0 : E (m + 1)) ℓ)
      = -(volume : Measure (E (m + 1))).toSphere.real univ * ℓ ^ (m + 3) * Ric.trace
          / (6 * (d - 1) * (d + 1)) := by
  intro d
  rw [volume_deficit (by omega) Ric hℓ]
  simp only [d]
  push_cast
  ring_nf

end EntEq.BallVol

end
