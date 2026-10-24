/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The null-cone lemma in every indefinite signature.

  Classical fact: the null cone `{k | B k k = 0}` of a nondegenerate *indefinite* symmetric
  bilinear form `B` on a finite-dimensional real vector space determines `B` up to a scalar.
  Equivalently, a symmetric form `A` that vanishes on every `B`-null vector is `c • B`.
  This is the step in Jacobson's derivation of the Einstein equation where `T_ab kᵃ kᵇ ∝
  R_ab kᵃ kᵇ` for all null `k` forces `T_ab - c R_ab ∝ g_ab`; it is also the reason the null
  cone of a metric fixes its conformal class. `EntEq.NullCone` proves it for Lorentzian
  signature `(1, n)`; this file proves it for every signature `(p, q)` with `p, q ≥ 1`, both for
  diagonal matrices and coordinate-free, and shows it fails for definite signature.

  The proof works in a `B`-orthonormal family `bᵢ` with `B bᵢ bᵢ = ±1`:
  * `bᵢ ± bⱼ` is null when the signs differ, so `A bᵢ bⱼ = 0` and `A bᵢ bᵢ = -A bⱼ bⱼ`;
  * `5 bₖ + 3 bᵢ + 4 bⱼ` is null when `bᵢ, bⱼ` share a sign and `bₖ` has the other one,
    so `A bᵢ bⱼ = 0` within a sign block too.
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Matrix LinearMap

namespace EntEq.General

/-- Expanding a bilinear form on a combination of three vectors. -/
lemma bilin_three {V : Type*} [AddCommGroup V] [Module ℝ V] (F : LinearMap.BilinForm ℝ V)
    (x y z : V) (a b c : ℝ) :
    F (a • x + b • y + c • z) (a • x + b • y + c • z) =
      a*a*F x x + a*b*F x y + a*c*F x z + b*a*F y x + b*b*F y y + b*c*F y z
        + c*a*F z x + c*b*F z y + c*c*F z z := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Core lemma.** Let `b` be a family of vectors that is orthonormal for `B` with signs
`s i = ±1`, both signs occurring. If a symmetric form `A` vanishes on every `B`-null vector,
then on this family `A` is a fixed multiple `c` of `B`. -/
theorem core {V ι : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq ι]
    (A B : LinearMap.BilinForm ℝ V) (hA : A.IsSymm) (b : ι → V) (s : ι → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hBb : ∀ i j, B (b i) (b j) = if i = j then s i else 0)
    (hneg : ∃ i, s i = -1) (hpos : ∃ i, s i = 1)
    (hnull : ∀ k, B k k = 0 → A k k = 0) :
    ∃ c : ℝ, ∀ i j, A (b i) (b j) = c * B (b i) (b j) := by
  obtain ⟨i0, hi0⟩ := hneg
  obtain ⟨j0, hj0⟩ := hpos
  have sym : ∀ i j, A (b j) (b i) = A (b i) (b j) := fun i j => hA.eq _ _
  -- Every index has a partner of the opposite sign.
  have opp : ∀ i, ∃ k, s k = -s i := by
    intro i
    rcases hs i with h | h
    · exact ⟨i0, by rw [hi0, h]⟩
    · exact ⟨j0, by rw [hj0, h]; norm_num⟩
  have ne_of_opp : ∀ i k, s k = -s i → k ≠ i := by
    rintro i k h rfl
    rcases hs k with h' | h' <;> rw [h'] at h <;> norm_num at h
  -- Step 1: opposite signs, `bᵢ ± bₖ` null.
  have step1 : ∀ i k, s k = -s i → A (b i) (b k) = 0 ∧ A (b k) (b k) = -A (b i) (b i) := by
    intro i k hk
    have hki := ne_of_opp i k hk
    have hp := hnull ((1:ℝ) • b i + (1:ℝ) • b k + (0:ℝ) • b k) (by
      rw [bilin_three]; norm_num [hBb, hki, Ne.symm hki, hk])
    have hm := hnull ((1:ℝ) • b i + (-1:ℝ) • b k + (0:ℝ) • b k) (by
      rw [bilin_three]; norm_num [hBb, hki, Ne.symm hki, hk])
    rw [bilin_three] at hp hm
    have := sym i k
    constructor <;> linarith
  set c : ℝ := -A (b i0) (b i0) with hc
  -- Step 2: the diagonal is `c • s`.
  have diag : ∀ i, A (b i) (b i) = c * s i := by
    intro i
    rcases hs i with h | h
    · rw [h, mul_one, hc]
      have := (step1 i i0 (by rw [hi0, h])).2
      linarith
    · rw [h, hc]
      have h1 := (step1 i j0 (by rw [hj0, h]; norm_num)).2
      have h2 := (step1 i0 j0 (by rw [hj0, hi0]; norm_num)).2
      linarith
  -- Step 3: off-diagonal entries vanish.
  have off : ∀ i j, i ≠ j → A (b i) (b j) = 0 := by
    intro i j hij
    rcases hs i with hi | hi <;> rcases hs j with hj | hj
    rotate_left
    · exact (step1 i j (by rw [hi, hj])).1
    · exact (step1 i j (by rw [hi, hj]; norm_num)).1
    all_goals
      obtain ⟨k, hk⟩ := opp i
      have hki := ne_of_opp i k hk
      have hkj := ne_of_opp j k (by rw [hk, hi, hj])
      have h := hnull ((5:ℝ) • b k + (3:ℝ) • b i + (4:ℝ) • b j) (by
        rw [bilin_three]
        norm_num [hBb, hki, Ne.symm hki, hkj, Ne.symm hkj, hij, Ne.symm hij, hk, hi, hj])
      rw [bilin_three] at h
      have := sym k i; have := sym k j; have := sym i j
      have := (step1 i k hk).1; have := (step1 j k (by rw [hk, hi, hj])).1
      have := diag i; have := diag j; have := diag k
      rw [hi] at *; rw [hj] at *; rw [hk] at *
      linarith
  refine ⟨c, fun i j => ?_⟩
  rw [hBb]
  by_cases hij : i = j
  · subst hij; rw [diag]; simp
  · simp [hij, off i j hij]

/-! ### Matrix version -/

/-- The quadratic form `M(k, k) = kᵀ M k` of a square matrix. -/
def qf {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (k : ι → ℝ) : ℝ := k ⬝ᵥ (M *ᵥ k)

lemma qf_eq_toBilin' {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (k : ι → ℝ) :
    qf M k = Matrix.toBilin' M k k := by
  rw [Matrix.toBilin'_apply', qf]

/-- **Null-cone lemma for a diagonal sign matrix.** Let `D = diag(s)` with every `s i = ±1`
and both signs present. A symmetric matrix `X` whose quadratic form vanishes on every
`D`-null vector is `c • D`. -/
theorem null_cone_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hneg : ∃ i, s i = -1) (hpos : ∃ i, s i = 1)
    (X : Matrix ι ι ℝ) (hX : X.IsSymm)
    (hnull : ∀ k, qf (diagonal s) k = 0 → qf X k = 0) :
    ∃ c : ℝ, X = c • diagonal s := by
  have hAs : (Matrix.toBilin' X).IsSymm := by
    refine ⟨fun x y => ?_⟩
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hX.eq, dotProduct_comm]
  obtain ⟨c, hc⟩ := core (Matrix.toBilin' X) (Matrix.toBilin' (diagonal s)) hAs
    (fun i => Pi.single i 1) s hs
    (fun i j => by rw [Matrix.toBilin'_single, diagonal_apply])
    hneg hpos (fun k hk => by
      rw [← qf_eq_toBilin'] at hk ⊢; exact hnull k hk)
  refine ⟨c, ?_⟩
  ext i j
  have := hc i j
  rw [Matrix.toBilin'_single, Matrix.toBilin'_single] at this
  rw [this, Matrix.smul_apply, smul_eq_mul]

/-- The metric of signature `(p, q)`: `-1` on the first `p` coordinates, `+1` on the last `q`. -/
def signMetric (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  diagonal (Sum.elim (fun _ => -1) (fun _ => 1))

/-- **Null-cone lemma in signature `(p, q)`, `p, q ≥ 1`.** A symmetric matrix that vanishes on
every null vector of `diag(-1,…,-1, 1,…,1)` is a multiple of that metric. -/
theorem null_cone_signature (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ) (hX : X.IsSymm)
    (hnull : ∀ k, qf (signMetric p q) k = 0 → qf X k = 0) :
    ∃ c : ℝ, X = c • signMetric p q :=
  null_cone_diag _ (fun i => by cases i <;> simp)
    ⟨Sum.inl ⟨0, hp⟩, rfl⟩ ⟨Sum.inr ⟨0, hq⟩, rfl⟩ X hX hnull

/-- **The lemma fails in definite signature.** For the Euclidean metric on `ℝ²` (signature
`(0, 2)`) only the zero vector is null, so `diag(1, 0)` vanishes on the null cone without
being a multiple of the metric. -/
theorem null_cone_fails_definite :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ, X.IsSymm ∧
      (∀ k, qf (1 : Matrix (Fin 2) (Fin 2) ℝ) k = 0 → qf X k = 0) ∧
      ¬ ∃ c : ℝ, X = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨diagonal ![1, 0], isSymm_diagonal _, fun k hk => ?_, ?_⟩
  · simp only [qf, Matrix.one_mulVec, dotProduct, Fin.sum_univ_two] at hk
    have h0 : k 0 = 0 := by nlinarith [mul_self_nonneg (k 0), mul_self_nonneg (k 1)]
    have h1 : k 1 = 0 := by nlinarith [mul_self_nonneg (k 0), mul_self_nonneg (k 1)]
    simp [qf, dotProduct, Fin.sum_univ_two, h0, h1]
  · rintro ⟨c, hc⟩
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    simp at h0 h1
    linarith

/-! ### Coordinate-free version -/

/-- In a `B`-orthogonal basis, `B x x = Σ xᵢ² B(vᵢ, vᵢ)`. -/
lemma self_eq_sum_of_orthogonal {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]
    [DecidableEq ι] (B : LinearMap.BilinForm ℝ V) (v : Module.Basis ι ℝ V) (hv : B.iIsOrtho v)
    (x : V) : B x x = ∑ i, v.repr x i * v.repr x i * B (v i) (v i) := by
  conv_lhs => rw [← v.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [hv hji]; ring) (by simp)]
  ring

/-- **Coordinate-free null-cone lemma.** On a finite-dimensional real vector space, let `B` be
a nondegenerate symmetric bilinear form that is indefinite (it takes both signs). Any symmetric
bilinear form `A` with `A k k = 0` for every `B`-null `k` is a scalar multiple of `B`. -/
theorem null_cone_bilin {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (A B : LinearMap.BilinForm ℝ V) (hA : A.IsSymm) (hB : B.IsSymm) (hBn : B.Nondegenerate)
    (hneg : ∃ x, B x x < 0) (hpos : ∃ x, 0 < B x x)
    (hnull : ∀ k, B k k = 0 → A k k = 0) :
    ∃ c : ℝ, A = c • B := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 hB)
  replace hv : B.iIsOrtho v := hv
  set d : _ → ℝ := fun i => B (v i) (v i) with hd
  have hd0 : ∀ i, d i ≠ 0 := hv.not_isOrtho_basis_self_of_nondegenerate hBn
  have habs : ∀ i, 0 < |d i| := fun i => abs_pos.mpr (hd0 i)
  -- Rescale to a `B`-orthonormal basis: `bᵢ = vᵢ / √|dᵢ|`.
  set r : _ → ℝ := fun i => (Real.sqrt |d i|)⁻¹ with hr
  have hr0 : ∀ i, r i ≠ 0 := fun i => inv_ne_zero (Real.sqrt_pos.mpr (habs i)).ne'
  have hrr : ∀ i, r i * r i = |d i|⁻¹ := fun i => by
    rw [hr, ← mul_inv, Real.mul_self_sqrt (habs i).le]
  let b := v.isUnitSMul (w := r) fun i => (hr0 i).isUnit
  have hbv : ∀ i, b i = r i • v i := fun i => v.isUnitSMul_apply _ i
  set s : _ → ℝ := fun i => d i / |d i| with hs
  have hs1 : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
    rcases lt_or_gt_of_ne (hd0 i) with h | h
    · right; simp only [hs, abs_of_neg h]; field_simp [h.ne]
    · left; simp only [hs, abs_of_pos h]; field_simp [h.ne']
  have hBb : ∀ i j, B (b i) (b j) = if i = j then s i else 0 := fun i j => by
    rw [hbv, hbv]; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp only [ite_true]; rw [← mul_assoc, mul_comm (r i), hrr, hs]
      simp only [hd]; ring
    · simp [hij, hv hij]
  -- Both signs occur among the `dᵢ`, else `B` would be semidefinite.
  have hneg' : ∃ i, s i = -1 := by
    by_contra hcon
    push Not at hcon
    have hpos_i : ∀ i, 0 < d i := fun i => by
      rcases hs1 i with h | h
      · rcases lt_or_gt_of_ne (hd0 i) with h' | h'
        · simp only [hs, abs_of_neg h'] at h; field_simp [h'.ne] at h; linarith
        · exact h'
      · exact absurd h (hcon i)
    obtain ⟨x, hx⟩ := hneg
    rw [self_eq_sum_of_orthogonal B v hv x] at hx
    have : 0 ≤ ∑ i, v.repr x i * v.repr x i * B (v i) (v i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (mul_self_nonneg _) (hpos_i i).le
    linarith
  have hpos' : ∃ i, s i = 1 := by
    by_contra hcon
    push Not at hcon
    have hneg_i : ∀ i, d i < 0 := fun i => by
      rcases hs1 i with h | h
      · exact absurd h (hcon i)
      · rcases lt_or_gt_of_ne (hd0 i) with h' | h'
        · exact h'
        · simp only [hs, abs_of_pos h'] at h; field_simp [h'.ne'] at h; linarith
    obtain ⟨x, hx⟩ := hpos
    rw [self_eq_sum_of_orthogonal B v hv x] at hx
    have : ∑ i, v.repr x i * v.repr x i * B (v i) (v i) ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _)
        (hneg_i i).le
    linarith
  obtain ⟨c, hc⟩ := core A B hA b s hs1 hBb hneg' hpos' hnull
  exact ⟨c, LinearMap.BilinForm.ext_basis b fun i j => by
    rw [hc, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]⟩

/-- The converse direction: every multiple of `B` vanishes on the `B`-null cone. Together with
`null_cone_bilin`, the null cone of an indefinite nondegenerate form determines it up to scale. -/
theorem null_cone_bilin_iff {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (A B : LinearMap.BilinForm ℝ V) (hA : A.IsSymm) (hB : B.IsSymm) (hBn : B.Nondegenerate)
    (hneg : ∃ x, B x x < 0) (hpos : ∃ x, 0 < B x x) :
    (∀ k, B k k = 0 → A k k = 0) ↔ ∃ c : ℝ, A = c • B := by
  refine ⟨null_cone_bilin A B hA hB hBn hneg hpos, ?_⟩
  rintro ⟨c, rfl⟩ k hk
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hk, smul_zero]

end EntEq.General
