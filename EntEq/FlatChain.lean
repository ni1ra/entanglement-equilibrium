/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Every hypothesis of `jacobson_chain` and `equilibrium_chain` discharged on Minkowski space
  `ℝ^(n+1)`, with differentiable fields, Mathlib's Fréchet derivative and the coordinate
  divergence: the flat case (`Ric = 0`). Curved instances, with a coordinate Levi-Civita
  connection and `Ric`, `R` built from `g`, are in `CurvedCoords` (conformally flat) and
  `BianchiGeneral` (any smooth metric).
-/
import EntEq.Clausius
import EntEq.Equilibrium2016

open Matrix

namespace EntEq.Flat

variable {n : ℕ}

local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

/-- Differentiable scalar fields. -/
def Ssub (n : ℕ) : Submodule ℝ ((Fin (n+1) → ℝ) → ℝ) where
  carrier := {φ | Differentiable ℝ φ}
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := differentiable_const 0
  smul_mem' := fun c _ ha => ha.const_smul c

/-- Tensor fields with differentiable components. -/
def Vsub (n : ℕ) : Submodule ℝ ((Fin (n+1) → ℝ) → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) where
  carrier := {X | ∀ a b, Differentiable ℝ fun y => X y a b}
  add_mem' := fun ha hb a b => (ha a b).add (hb a b)
  zero_mem' := fun _ _ => differentiable_const 0
  smul_mem' := fun c _ ha a b => (ha a b).const_smul c

lemma eta_mul_self : eta n * eta n = 1 := by
  rw [eta, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i; split_ifs <;> norm_num

lemma eta_inv : (eta n)⁻¹ = eta n := Matrix.inv_eq_left_inv eta_mul_self

/-- `φ ↦ φ η`. -/
noncomputable def mulG : Ssub n →ₗ[ℝ] Vsub n where
  toFun φ := ⟨fun y => φ.1 y • eta n, fun a b => by
    simpa [Matrix.smul_apply] using φ.2.mul_const (eta n a b)⟩
  map_add' φ ψ := by ext y a b; simp [add_mul]
  map_smul' c φ := by ext y a b; simp [mul_assoc]

/-- `X ↦ tr(η⁻¹ X)/(n+1)`. -/
noncomputable def trace' : Vsub n →ₗ[ℝ] Ssub n where
  toFun X := ⟨fun y => Matrix.trace ((eta n)⁻¹ * X.1 y) / (n + 1), by
    show Differentiable ℝ _
    simp only [div_eq_mul_inv]
    apply Differentiable.mul_const
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ =>
      (X.2 j i).const_mul _⟩
  map_add' X Y := by ext y; simp [Matrix.mul_add, Matrix.trace_add, add_div]
  map_smul' c X := by ext y; simp [Matrix.trace_smul, mul_div_assoc]

/-- The coordinate divergence, linear on differentiable fields. -/
noncomputable def divL : Vsub n →ₗ[ℝ] (E → Fin (n+1) → ℝ) where
  toFun X := fun x b => divFlat X.1 x b
  map_add' X Y := by
    ext x b
    simp only [divFlat, Submodule.coe_add, Pi.add_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
    congr 1; ext a
    rw [fderiv_fun_add ((X.2 a b) x) ((Y.2 a b) x)]
    simp [mul_add]
  map_smul' c X := by
    ext x b
    simp only [divFlat, Submodule.coe_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    congr 1; ext a
    rw [fderiv_const_mul ((X.2 a b) x)]
    simp; ring

/-- The gradient `dφ`, linear on differentiable scalars. -/
noncomputable def dL : Ssub n →ₗ[ℝ] (E → Fin (n+1) → ℝ) where
  toFun φ := fun x b => fderiv ℝ φ.1 x (e b)
  map_add' φ ψ := by ext x b; simp [fderiv_add (φ.2 x) (ψ.2 x)]
  map_smul' c φ := by ext x b; simp [fderiv_const_smul (φ.2 x)]

/-- The constant field `1`. -/
def one : Ssub n := ⟨fun _ => 1, differentiable_const 1⟩

/-- **Flat-space Clausius.** On Minkowski space, take a symmetric stress tensor with
differentiable components and zero coordinate divergence. If `κₑ T(k,k) = 0` for every null
`k` at every point (local Clausius with zero curvature), then `κₑ T = Λ η` for one constant
`Λ`: flat spacetime admits only constant vacuum energy. Proved by instantiating
`jacobson_chain` with `Ric = 0`. -/
theorem flat_clausius (T : E → Mat) (hTd : ∀ a b, Differentiable ℝ fun y => T y a b)
    (hTs : ∀ x, (T x).IsSymm) (hcons : ∀ x b, divFlat T x b = 0) (κₑ : ℝ)
    (hClausius : ∀ x k, qf (eta n) k = 0 → κₑ * qf (T x) k = 0) :
    ∃ Λ : ℝ, ∀ x, κₑ • T x = Λ • eta n := by
  let Tv : Vsub n := ⟨T, hTd⟩
  have hP : ∀ _x : E, IsUnit ((1 : Mat).det) := fun _ => by simp
  have hg : ∀ x : E, (1 : Mat)ᵀ * eta n * (1 : Mat) = eta n := fun _ => by simp
  obtain ⟨Λ, hΛ⟩ := @jacobson_chain n (Fin (n+1) → ℝ) (Vsub n) (Ssub n) ((Fin (n+1) → ℝ) → Fin (n+1) → ℝ)
    _ _ _ _ _ _ (fun _ => (1 : Mat)) hP
    (Vsub n).subtype Subtype.val_injective (Ssub n).subtype
    mulG (fun φ x => by simp [mulG]) trace' (fun X x => by simp [trace'])
    one divL dL
    (fun φ => by ext x b; exact divFlat_scalar φ.1 φ.2 x b)
    (fun φ hφ => by
      refine ⟨φ.1 0, ?_⟩
      have hconst := is_const_of_fderiv_eq_zero φ.2 (fun x => clm_eq_zero_of_basis _
        fun b => congrFun (congrFun hφ x) b)
      ext x; simp [one, hconst x 0])
    0 Tv 0 κₑ (fun _ => by simp [Matrix.IsSymm]) hTs
    (fun x k hk => by simp [hg] at hk ⊢; rw [hClausius x k hk]; simp [qf])
    (by simp) (by ext x b; exact hcons x b)
  refine ⟨Λ, fun x => ?_⟩
  have := congrArg (fun v : Vsub n => v.1 x) hΛ
  simp [mulG, one, Tv] at this
  exact this.symm
/-- **Flat-space equilibrium (2016 chain on Minkowski space).** Take a conserved symmetric
stress tensor and a scalar `L`, both differentiable. If `−L(x) = κₑ T(u,u)` for every unit
timelike `u` at every point (stationarity with zero curvature), then `κₑ T = −L η` and `L` is
constant. -/
theorem flat_equilibrium (T : E → Mat) (hTd : ∀ a b, Differentiable ℝ fun y => T y a b)
    (hTs : ∀ x, (T x).IsSymm) (hcons : ∀ x b, divFlat T x b = 0) (L : E → ℝ)
    (hL : Differentiable ℝ L) (κₑ : ℝ)
    (hEq : ∀ x u, qf (eta n) u = -1 → -L x = κₑ * qf (T x) u) :
    (∀ x, κₑ • T x = L x • eta n) ∧ ∃ c : ℝ, ∀ x, L x = c := by
  let Tv : Vsub n := ⟨T, hTd⟩
  let Lv : Ssub n := ⟨L, hL⟩
  have hP : ∀ _x : E, IsUnit ((1 : Mat).det) := fun _ => by simp
  have hg : (1 : Mat)ᵀ * eta n * (1 : Mat) = eta n := by simp
  obtain ⟨hfield, c, hc⟩ := @equilibrium_chain n (Fin (n+1) → ℝ) (Vsub n) (Ssub n)
    ((Fin (n+1) → ℝ) → Fin (n+1) → ℝ) _ _ _ _ _ _ (fun _ => (1 : Mat)) hP
    (Vsub n).subtype Subtype.val_injective (Ssub n).subtype
    mulG (fun φ x => by simp [mulG]) one divL dL
    (fun φ => by ext x b; exact divFlat_scalar φ.1 φ.2 x b)
    (fun φ hφ => by
      refine ⟨φ.1 0, ?_⟩
      have hconst := is_const_of_fderiv_eq_zero φ.2 (fun x => clm_eq_zero_of_basis _
        fun b => congrFun (congrFun hφ x) b)
      ext x; simp [one, hconst x 0])
    0 Tv Lv κₑ (fun _ => by simp [Matrix.IsSymm]) hTs
    (fun x u hu => by
      rw [hg] at hu
      simp [qf]
      have := hEq x u hu
      simp [qf, Lv, Tv] at this ⊢
      linarith)
    (by simp) (by ext x b; exact hcons x b)
  refine ⟨fun x => ?_, c, fun x => ?_⟩
  · have := congrArg (fun v : Vsub n => v.1 x) hfield
    simp [mulG, Tv, Lv] at this
    exact this.symm
  · have := congrArg (fun v : Ssub n => v.1 x) hc
    simpa [one, Lv] using this

end EntEq.Flat
