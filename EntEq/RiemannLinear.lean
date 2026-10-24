/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
import EntEq.NormalCoordsGeneral

/-!
  Tensor transformation laws under a constant invertible linear change of coordinates
  `x = L y`, for the metric `g̃(y) = Lᵀ g(L y) L` (`linG L g`), at every point `y`.

  * `chr_linG`: `Γ̃^a_bc(y) = Σ (L⁻¹)^a_i L^j_b L^k_c Γ^i_jk(L y)` (needs only `g` smooth and
    `L` invertible; no inhomogeneous term since `L` is constant). Matrix form `Gm_linG`.
  * `riem_linG`: `R̃^a_bcd(y) = Σ (L⁻¹)^a_i L^j_b L^k_c L^l_d R^i_jkl(L y)` (needs `g` smooth
    and invertible everywhere). Matrix form `Fm_linG`.
  * `riemLow_linG`: the lowered tensor `R_ijkl = g_im R^m_jkl` (`riemLow`) is covariant:
    `R̃_abcd(y) = Σ L^i_a L^j_b L^k_c L^l_d R_ijkl(L y)`.
  * `normal_coordinates_general_riem`: the second-derivative conclusion of
    `normal_coordinates_general` rewritten through `riem g 0` (mixed form) and through
    `riemLow g 0` (lowered with `g 0`).

  Only linear (constant-Jacobian) changes are covered; general diffeomorphisms are not.
-/

namespace EntEq.NormalCoords

open Matrix EntEq.Curved
open scoped ContDiff

variable {n : ℕ}
local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

lemma pd_comp_mulVec (L : Mat) (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f (L *ᵥ x))
    (c : Fin (n+1)) :
    pd (fun y => f (L *ᵥ y)) x c = ∑ k, L k c * pd f (L *ᵥ x) k := by
  set ℓ : E →L[ℝ] E := LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  have hℓ : (fun y => L *ᵥ y) = ⇑ℓ := rfl
  have : (fun y => f (L *ᵥ y)) = f ∘ ℓ := rfl
  unfold pd
  rw [this, fderiv_comp x (show DifferentiableAt ℝ f (ℓ x) from hf) ℓ.differentiableAt, ℓ.fderiv]
  have hv : ℓ (e c) = ∑ k, L k c • e k := by
    funext i
    simp [ℓ, mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
  simp only [ContinuousLinearMap.comp_apply, hv, map_sum, map_smul, smul_eq_mul]
  rfl

/-- Partial derivative of a constant matrix field. -/
lemma pdM_const (P : Mat) (x : E) (c : Fin (n+1)) : pdM (fun _ : E => P) x c = 0 := by
  ext a b; simp [pdM, pd_const]

/-- `∂_c (P · A(L y) · Q) = Σ_k L_kc · P (∂_k A)(L y) Q` for constant `P, Q, L`. -/
lemma pdM_sandwich (L P Q : Mat) (A : E → Mat) (hA : Sm A) (y : E) (c : Fin (n+1)) :
    pdM (fun z => P * A (L *ᵥ z) * Q) y c = ∑ k, L k c • (P * pdM A (L *ᵥ y) k * Q) := by
  have hB : Sm fun z => A (L *ᵥ z) := fun a b => (hA a b).comp (contDiff_mulVec L)
  have hPB : Sm fun z => P * A (L *ᵥ z) := (Sm.const P).mul hB
  rw [pdM_mul (A := fun z => P * A (L *ᵥ z)) (B := fun _ => Q) hPB (Sm.const Q),
    pdM_mul (A := fun _ => P) (B := fun z => A (L *ᵥ z)) (Sm.const P) hB, pdM_const, pdM_const]
  have hchain : pdM (fun z => A (L *ᵥ z)) y c = ∑ k, L k c • pdM A (L *ᵥ y) k := by
    ext a b
    simp only [pdM, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact pd_comp_mulVec L _ y (diff_of_smooth (hA a b) _) c
  rw [hchain]
  simp only [zero_mul, mul_zero, zero_add, add_zero, Finset.mul_sum, Finset.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-- `∂_c Σ_j k_j B_j = Σ_j k_j ∂_c B_j` for smooth matrix fields. -/
lemma pdM_sum_smul (k : Fin (n+1) → ℝ) (B : Fin (n+1) → E → Mat) (hB : ∀ j, Sm (B j)) (x : E)
    (c : Fin (n+1)) :
    pdM (fun z => ∑ j, k j • B j z) x c = ∑ j, k j • pdM (B j) x c := by
  ext a b
  simp only [pdM, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [pd_sum _ fun j => (diff_of_smooth (hB j a b)).const_mul (k j)]
  exact Finset.sum_congr rfl fun j _ => pd_const_mul _ (diff_of_smooth (hB j a b))

/-- First derivatives of the metric transform with one factor of `L` per index:
`∂_c g̃_db(y) = Σ L_kc L_pd L_qb (∂_k g_pq)(L y)`. -/
lemma dg_linG (L : Mat) (g : E → Mat) (hg : Sm g) (y : E) (c d b : Fin (n+1)) :
    dg (linG L g) y c d b
      = ∑ k, ∑ p, ∑ q, L k c * L p d * L q b * dg g (L *ᵥ y) k p q := by
  have h := congrFun (congrFun (pdM_sandwich L Lᵀ L g hg y c) d) b
  simp only [pdM, Matrix.of_apply] at h
  change pd (fun z => (Lᵀ * g (L *ᵥ z) * L) d b) y c = _
  rw [h]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by unfold dg; ring

/-- The bracket of the Christoffel formula as a matrix:
`K_c(d, b) = ½(∂_c g_db + ∂_b g_dc − ∂_d g_cb)`, so that `Γ_c = g⁻¹ K_c`. -/
noncomputable def Kmat (g : E → Mat) (y : E) (c : Fin (n+1)) : Mat :=
  Matrix.of fun d b => (1/2 : ℝ) * (dg g y c d b + dg g y b d c - dg g y d c b)

lemma Gm_eq (g : E → Mat) (y : E) (c : Fin (n+1)) : Gm g y c = (g y)⁻¹ * Kmat g y c := by
  ext a b
  simp only [Gm, Kmat, chr, Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

lemma Kmat_linG (L : Mat) (g : E → Mat) (hg : Sm g) (y : E) (c : Fin (n+1)) :
    Kmat (linG L g) y c = ∑ j, L j c • (Lᵀ * Kmat g (L *ᵥ y) j * L) := by
  ext d b
  simp only [Kmat, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, dg_linG L g hg]
  set D := dg g (L *ᵥ y)
  have h2 : ∑ k, ∑ p, ∑ q, L k b * L p d * L q c * D k p q
      = ∑ j, ∑ p, ∑ q, L j c * L p d * L q b * D q p j := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h3 : ∑ k, ∑ p, ∑ q, L k d * L p c * L q b * D k p q
      = ∑ j, ∑ p, ∑ q, L j c * L p d * L q b * D p j q := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  rw [h2, h3]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- **Christoffel symbols under a constant linear change of coordinates** (matrix form). With
`g̃(y) = Lᵀ g(L y) L`, `L` invertible: `Γ̃_c(y) = Σ_j L_jc · L⁻¹ Γ_j(L y) L`, where
`(Γ_c)^a_b = Γ^a_cb`. No inhomogeneous term appears because `L` is constant. -/
theorem Gm_linG (L : Mat) (hL : IsUnit L.det) (g : E → Mat) (hg : Sm g) (y : E)
    (c : Fin (n+1)) :
    Gm (linG L g) y c = ∑ j, L j c • (L⁻¹ * Gm g (L *ᵥ y) j * L) := by
  have hLM : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ hL
  have hinv : (linG L g y)⁻¹ = L⁻¹ * (g (L *ᵥ y))⁻¹ * (L⁻¹)ᵀ := by
    rw [linG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv,
      Matrix.mul_assoc]
  have hMtLt : (L⁻¹)ᵀ * Lᵀ = 1 := by rw [← Matrix.transpose_mul, hLM, Matrix.transpose_one]
  rw [Gm_eq, hinv, Kmat_linG L g hg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, Gm_eq]
  congr 1
  calc L⁻¹ * (g (L *ᵥ y))⁻¹ * (L⁻¹)ᵀ * (Lᵀ * Kmat g (L *ᵥ y) j * L)
      = L⁻¹ * (g (L *ᵥ y))⁻¹ * ((L⁻¹)ᵀ * Lᵀ) * Kmat g (L *ᵥ y) j * L := by
        simp only [Matrix.mul_assoc]
    _ = L⁻¹ * ((g (L *ᵥ y))⁻¹ * Kmat g (L *ᵥ y) j) * L := by
        rw [hMtLt, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma sum3_perm (f : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ x, ∑ y, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, f x y z := Finset.sum_comm

/-- **Christoffel symbols under a constant linear change of coordinates** (components):
`Γ̃^a_bc(y) = Σ (L⁻¹)^a_i L^j_b L^k_c Γ^i_jk(L y)`. -/
theorem chr_linG (L : Mat) (hL : IsUnit L.det) (g : E → Mat) (hg : Sm g) (y : E)
    (a b c : Fin (n+1)) :
    chr (linG L g) y a b c
      = ∑ i, ∑ j, ∑ k, L⁻¹ a i * L j b * L k c * chr g (L *ᵥ y) i j k := by
  have h := congrFun (congrFun (Gm_linG L hL g hg y b) a) c
  simp only [Gm, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply] at h
  rw [h]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum3_perm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-! ### Riemann tensor -/

lemma sum4_perm (f : Fin (n+1) → Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ) :
    ∑ k, ∑ l, ∑ j, ∑ i, f k l j i = ∑ i, ∑ j, ∑ k, ∑ l, f k l j i := by
  calc ∑ k, ∑ l, ∑ j, ∑ i, f k l j i = ∑ k, ∑ j, ∑ l, ∑ i, f k l j i :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, ∑ l, f k l j i :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ∑ l, f k l j i := Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ k, ∑ l, f k l j i := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l j i := Finset.sum_comm

/-- Entries of `Σ_kl L_kc L_ld · P X_kl Q`. -/
lemma entry4 (L P Q : Mat) (X : Fin (n+1) → Fin (n+1) → Mat) (a b c d : Fin (n+1)) :
    (∑ k, ∑ l, (L k c * L l d) • (P * X k l * Q)) a b
      = ∑ i, ∑ j, ∑ k, ∑ l, P a i * Q j b * L k c * L l d * X k l i j := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul]
  conv_lhs => rw [sum4_perm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma pdM_Gm_linG (L : Mat) (hL : IsUnit L.det) (g : E → Mat) (hg : Sm g)
    (hdet : ∀ y, IsUnit (g y).det) (y : E) (c d : Fin (n+1)) :
    pdM (fun z => Gm (linG L g) z d) y c
      = ∑ j, ∑ l, (L j d * L l c) • (L⁻¹ * pdM (fun w => Gm g w j) (L *ᵥ y) l * L) := by
  have hfun : (fun z => Gm (linG L g) z d)
      = fun z => ∑ j, L j d • (L⁻¹ * Gm g (L *ᵥ z) j * L) :=
    funext fun z => Gm_linG L hL g hg z d
  have hS : ∀ j, Sm fun z => L⁻¹ * Gm g (L *ᵥ z) j * L := fun j =>
    ((Sm.const _).mul fun a b => ((hg.gm hdet j) a b).comp (contDiff_mulVec L)).mul (Sm.const _)
  rw [hfun, pdM_sum_smul _ _ hS]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pdM_sandwich L L⁻¹ L _ (hg.gm hdet j), Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ => smul_smul _ _ _

lemma Gm_mul_linG (L : Mat) (hL : IsUnit L.det) (g : E → Mat) (hg : Sm g) (y : E) (c d : Fin (n+1)) :
    Gm (linG L g) y c * Gm (linG L g) y d
      = ∑ k, ∑ l, (L k c * L l d) • (L⁻¹ * (Gm g (L *ᵥ y) k * Gm g (L *ᵥ y) l) * L) := by
  have hLM : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ hL
  have key : ∀ X Y : Mat, L⁻¹ * X * L * (L⁻¹ * Y * L) = L⁻¹ * (X * Y) * L := by
    intro X Y
    calc L⁻¹ * X * L * (L⁻¹ * Y * L) = L⁻¹ * X * (L * L⁻¹) * Y * L := by
          simp only [Matrix.mul_assoc]
      _ = L⁻¹ * (X * Y) * L := by rw [hLM, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [Gm_linG L hL g hg, Gm_linG L hL g hg, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key]

/-- **Riemann tensor under a constant linear change of coordinates** (matrix form). With
`g̃(y) = Lᵀ g(L y) L`, `L` invertible, and `(F_cd)^a_b = R^a_bcd`:
`F̃_cd(y) = Σ_kl L_kc L_ld · L⁻¹ F_kl(L y) L`. -/
theorem Fm_linG (L : Mat) (hL : IsUnit L.det) (g : E → Mat) (hg : Sm g)
    (hdet : ∀ y, IsUnit (g y).det) (y : E) (c d : Fin (n+1)) :
    Fm (linG L g) y c d
      = ∑ k, ∑ l, (L k c * L l d) • (L⁻¹ * Fm g (L *ᵥ y) k l * L) := by
  have h1 : pdM (fun z => Gm (linG L g) z d) y c
      = ∑ k, ∑ l, (L k c * L l d) • (L⁻¹ * pdM (fun w => Gm g w l) (L *ᵥ y) k * L) := by
    rw [pdM_Gm_linG L hL g hg hdet, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have h2 := pdM_Gm_linG L hL g hg hdet y d c
  have h3 := Gm_mul_linG L hL g hg y c d
  have h4 : Gm (linG L g) y d * Gm (linG L g) y c
      = ∑ k, ∑ l, (L k c * L l d) • (L⁻¹ * (Gm g (L *ᵥ y) l * Gm g (L *ᵥ y) k) * L) := by
    rw [Gm_mul_linG L hL g hg, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  rw [Fm_eq, h1, h2, h3, h4]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Fm_eq]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, smul_add, smul_sub]

/-- **Riemann tensor under a constant linear change of coordinates** (components):
`R̃^a_bcd(y) = Σ (L⁻¹)^a_i L^j_b L^k_c L^l_d R^i_jkl(L y)`, with `g̃(y) = Lᵀ g(L y) L`. -/
theorem riem_linG (L : Mat) (hL : IsUnit L.det) (g : E → Mat) (hg : Sm g)
    (hdet : ∀ y, IsUnit (g y).det) (y : E) (a b c d : Fin (n+1)) :
    riem (linG L g) y a b c d
      = ∑ i, ∑ j, ∑ k, ∑ l, L⁻¹ a i * L j b * L k c * L l d * riem g (L *ᵥ y) i j k l := by
  have h := congrFun (congrFun (Fm_linG L hL g hg hdet y c d) a) b
  rw [entry4] at h
  exact h

/-- The fully lowered Riemann tensor `R_ijkl = g_im R^m_jkl`. -/
noncomputable def riemLow (g : E → Mat) (x : E) (i j k l : Fin (n+1)) : ℝ :=
  ∑ m, g x i m * riem g x m j k l

/-- **The lowered Riemann tensor is covariant** under a constant linear change of coordinates:
`R̃_abcd(y) = Σ L^i_a L^j_b L^k_c L^l_d R_ijkl(L y)`. -/
theorem riemLow_linG (L : Mat) (hL : IsUnit L.det) (g : E → Mat) (hg : Sm g)
    (hdet : ∀ y, IsUnit (g y).det) (y : E) (a b c d : Fin (n+1)) :
    riemLow (linG L g) y a b c d
      = ∑ i, ∑ j, ∑ k, ∑ l, L i a * L j b * L k c * L l d * riemLow g (L *ᵥ y) i j k l := by
  have hLM : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ hL
  have hmat : linG L g y * Fm (linG L g) y c d
      = ∑ k, ∑ l, (L k c * L l d) • (Lᵀ * (g (L *ᵥ y) * Fm g (L *ᵥ y) k l) * L) := by
    rw [Fm_linG L hL g hg hdet, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_smul, linG]
    congr 1
    calc Lᵀ * g (L *ᵥ y) * L * (L⁻¹ * Fm g (L *ᵥ y) k l * L)
        = Lᵀ * g (L *ᵥ y) * (L * L⁻¹) * Fm g (L *ᵥ y) k l * L := by simp only [Matrix.mul_assoc]
      _ = Lᵀ * (g (L *ᵥ y) * Fm g (L *ᵥ y) k l) * L := by
        rw [hLM, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h := congrFun (congrFun hmat a) b
  rw [entry4] at h
  simp only [Matrix.mul_apply, Fm, Matrix.of_apply, Matrix.transpose_apply] at h
  unfold riemLow
  rw [h]


/-! ### Normal coordinates: second derivatives in terms of `riem g 0` -/

lemma riemLow_diag (g' : E → Mat) (s : Fin (n+1) → ℝ) (h0 : g' 0 = diagonal s)
    (a b c d : Fin (n+1)) : riemLow g' 0 a b c d = s a * riem g' 0 a b c d := by
  unfold riemLow
  rw [h0]
  simp [Matrix.diagonal_apply]

/-- **Normal coordinates, curvature of the original metric.** Some of the conclusions of
`normal_coordinates_general` (smooth symmetric `g`, invertible everywhere), with the
second-derivative conclusion rewritten through the Riemann tensor of `g` itself at `0`:
for `g' = Dφᵀ g(φ) Dφ`,
`∂_c∂_d g'_ab(0) = −⅓ s_a Σ (L⁻¹)^a_i (L^j_c L^k_b L^l_d R^i_jkl + L^j_d L^k_b L^l_c R^i_jkl)`
with `R = riem g 0`, and equivalently, in lowered form with `R_ijkl = g(0)_im R^m_jkl`,
`∂_c∂_d g'_ab(0) = −⅓ Σ L^i_a L^k_b (L^j_c L^l_d + L^j_d L^l_c) R_ijkl`. -/
theorem normal_coordinates_general_riem (g : E → Mat) (hg : Sm g) (hsym : ∀ y, (g y).IsSymm)
    (hdet : ∀ y, IsUnit (g y).det) :
    ∃ (L : Mat) (s : Fin (n+1) → ℝ) (L' : E ≃L[ℝ] E),
      IsUnit L.det ∧ (∀ a, s a * s a = 1) ∧ (∀ v, L' v = L *ᵥ v) ∧
      Lᵀ * g 0 * L = diagonal s ∧ phiNC L s g 0 = 0 ∧
      HasStrictFDerivAt (phiNC L s g) (L' : E →L[ℝ] E) 0 ∧
      pullG g (phiNC L s g) 0 = diagonal s ∧
      (∀ a b c d, pd (fun y => pd (fun y => pullG g (phiNC L s g) y a b) y c) 0 d
        = -(1/3) * (s a * ∑ i, ∑ j, ∑ k, ∑ l, L⁻¹ a i * L j c * L k b * L l d * riem g 0 i j k l
          + s a * ∑ i, ∑ j, ∑ k, ∑ l, L⁻¹ a i * L j d * L k b * L l c * riem g 0 i j k l)) ∧
      (∀ a b c d, pd (fun y => pd (fun y => pullG g (phiNC L s g) y a b) y c) 0 d
        = -(1/3) * (∑ i, ∑ j, ∑ k, ∑ l, L i a * L j c * L k b * L l d * riemLow g 0 i j k l
          + ∑ i, ∑ j, ∑ k, ∑ l, L i a * L j d * L k b * L l c * riemLow g 0 i j k l)) := by
  obtain ⟨L, s, L', hL, hs, hL', hgt0, hphi0, hstrict, -, hpull0, -, -, -, hdd⟩ :=
    normal_coordinates_general g hg hsym hdet
  have h0 : L *ᵥ (0 : E) = 0 := mulVec_zero L
  refine ⟨L, s, L', hL, hs, hL', by simpa [linG, h0] using hgt0, hphi0, hstrict, hpull0,
    fun a b c d => ?_, fun a b c d => ?_⟩
  · rw [hdd, riem_linG L hL g hg hdet, riem_linG L hL g hg hdet, h0]
  · rw [hdd, ← riemLow_diag _ s hgt0, ← riemLow_diag _ s hgt0, riemLow_linG L hL g hg hdet,
      riemLow_linG L hL g hg hdet, h0]

end EntEq.NormalCoords
