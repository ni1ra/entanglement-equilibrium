/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  How strong must a premise be to give Einstein's equation?

  * `ball_iff_null`: the 2016 premise at a point, "there is a scalar `L` with
    `G(u,u) − L = κ T(u,u)` for every unit timelike `u`" (one equation per rest frame, `L` the
    reference curvature plus any `δX`), is **equivalent** to the 1995 null relation
    `Ric(k,k) = κ T(k,k)` for every null `k`. The free scalar absorbs exactly the one
    direction (multiples of `g`) that null vectors cannot see, so the 2016 form is not weaker.
  * `flat_sector_necessity`: for **any** premise whatsoever (a predicate on metric and matter
    fields) that yields Einstein's equation with a constant `Λ` for every smooth metric and
    conserved symmetric `T`, the premise must force `T(k,k) = 0` for all null `k` on flat
    space with homogeneous matter. On that sector no premise can be weaker than the null
    relation, whatever words it is stated in.
  * `one_frame_insufficient`: a premise that is one number per point (one rest frame, a free
    scalar) does not yield Einstein's equation.
-/
import EntEq.BianchiGeneral
import EntEq.Equilibrium2016

open Matrix

namespace EntEq.Curved

variable {n : ℕ}

local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

lemma qf_sub' (A B : Mat) (v : Fin (n+1) → ℝ) : qf (A - B) v = qf A v - qf B v := by
  simp [qf, Matrix.sub_mulVec, dotProduct_sub]

/-- **The 2016 premise is pointwise equivalent to the 1995 null relation.** At one point with
metric `g = Pᵀ η P`, symmetric `Ric`, `T` and any number `R`: a scalar `L` with
`(Ric − ½R g)(u,u) − L = κ T(u,u)` for every unit timelike `u` exists iff
`Ric(k,k) = κ T(k,k)` for every null `k`. -/
theorem ball_iff_null (P Ric T : Mat) (hP : IsUnit P.det) (hRic : Ric.IsSymm) (hT : T.IsSymm)
    (R κ : ℝ) :
    (∃ L : ℝ, ∀ u, qf (Pᵀ * eta n * P) u = -1 →
      qf (Ric - (1/2 : ℝ) • R • (Pᵀ * eta n * P)) u - L = κ * qf T u)
    ↔ ∀ k, qf (Pᵀ * eta n * P) k = 0 → qf Ric k = κ * qf T k := by
  have hg : (Pᵀ * eta n * P).IsSymm := gP_symm (fun _ : E => P) 0
  constructor
  · rintro ⟨L, hL⟩ k hk
    have hX := unit_timelike_const_lorentzian P (Ric - (1/2 : ℝ) • R • (Pᵀ * eta n * P) - κ • T)
      hP ((hRic.sub ((hg.smul R).smul _)).sub (hT.smul κ)) L (fun u hu => by
        have h := hL u hu
        rw [qf_sub', qf_smul, qf_smul, hu] at h
        rw [qf_sub', qf_sub', qf_smul, qf_smul, qf_smul, hu]
        linarith)
    have h3 := congrArg (fun M => qf M k) hX
    rw [qf_sub', qf_sub', qf_smul, qf_smul, qf_smul, qf_smul, hk] at h3
    linarith
  · intro hN
    obtain ⟨c, hc⟩ := null_cone_lemma_lorentzian P (Ric - κ • T) hP (hRic.sub (hT.smul κ))
      (fun k hk => by rw [qf_sub', qf_smul, hN k hk]; ring)
    refine ⟨(1/2) * R - c, fun u hu => ?_⟩
    have h1 := congrArg (fun M => qf M u) hc
    rw [qf_sub', qf_smul, qf_smul, hu] at h1
    rw [qf_sub', qf_smul, qf_smul, hu]
    linarith

/-! ### Flat space with homogeneous matter -/

lemma chr_const (M : Mat) (y : E) (a b c : Fin (n+1)) : chr (fun _ : E => M) y a b c = 0 := by
  simp [chr, dg, pd_const]

lemma ricci_const (M : Mat) (x : E) : ricci (fun _ : E => M) x = 0 := by
  ext b d
  simp [ricci, riem, chr_const, pd_const]

lemma scal_const (M : Mat) (x : E) : scal (fun _ : E => M) x = 0 := by
  simp [scal, ricci_const]

lemma covDiv_const (M T0 : Mat) (x : E) (b : Fin (n+1)) :
    covDiv (fun _ : E => M) (fun _ : E => T0) x b = 0 := by
  simp [covDiv, chr_const, pd_const]

lemma gP_one : gP (fun _ : E => (1 : Mat)) = fun _ => eta n := by
  funext x; simp [gP]

/-- **No premise can be weaker than the null relation on flat space with homogeneous matter.**
Let `Prem g T` be any condition on a metric field and a matter field. Suppose that for every
smooth `P` with `g = Pᵀ η P` and every differentiable, symmetric, conserved `T`, `Prem g T`
gives `Ric − ½R g + Λ g = κ T` with a constant `Λ`. Then whenever `Prem` holds for Minkowski
space with a constant symmetric `T₀`, `T₀(k,k) = 0` for every null `k`; there `Ric = 0`, so
this is the null relation `Ric(k,k) = κ T₀(k,k)` itself. -/
theorem flat_sector_necessity (Prem : (E → Mat) → (E → Mat) → Prop) (κ : ℝ) (hκ : κ ≠ 0)
    (hderive : ∀ P T : E → Mat, Sm P → (∀ x, IsUnit (P x).det) →
      (∀ a b, Differentiable ℝ fun y => T y a b) → (∀ x, (T x).IsSymm) →
      (∀ x b, covDiv (gP P) T x b = 0) → Prem (gP P) T →
      ∃ Λ : ℝ, ∀ x, ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x + Λ • gP P x = κ • T x)
    (T0 : Mat) (hT0 : T0.IsSymm) (hprem : Prem (fun _ => eta n) (fun _ => T0)) :
    ∀ k, qf (eta n) k = 0 → qf T0 k = 0 := by
  obtain ⟨Λ, hΛ⟩ := hderive (fun _ => 1) (fun _ => T0) (Sm.const 1) (fun _ => by simp)
    (fun _ _ => differentiable_const _) (fun _ => hT0)
    (fun x b => by rw [gP_one]; exact covDiv_const _ _ x b) (by rw [gP_one]; exact hprem)
  have h := hΛ 0
  rw [gP_one] at h
  simp only [ricci_const, scal_const, zero_smul, smul_zero, sub_zero, zero_add] at h
  intro k hk
  have := congrArg (fun M => qf M k) h
  simp only [qf_smul] at this
  rw [hk, mul_zero] at this
  rcases mul_eq_zero.mp this.symm with h' | h'
  · exact absurd h' hκ
  · exact h'

/-- **One number per point is not enough.** The premise "at every point there is a scalar `L`
with `G(e₀,e₀) − L = κ T(e₀,e₀)`" (one rest frame, a free reference curvature) does not yield
Einstein's equation, in any dimension `n + 1 ≥ 2`. -/
theorem one_frame_insufficient (κ : ℝ) (hκ : κ ≠ 0) (hn : 1 ≤ n) :
    ¬ ∀ P T : E → Mat, Sm P → (∀ x, IsUnit (P x).det) →
      (∀ a b, Differentiable ℝ fun y => T y a b) → (∀ x, (T x).IsSymm) →
      (∀ x b, covDiv (gP P) T x b = 0) →
      (∀ x, ∃ L : ℝ, qf (ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x) (e 0) - L
        = κ * qf (T x) (e 0)) →
      ∃ Λ : ℝ, ∀ x, ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x + Λ • gP P x
        = κ • T x := by
  intro hderive
  set i1 : Fin (n+1) := ⟨1, by omega⟩
  have hi1 : i1 ≠ 0 := by simp [i1, Fin.ext_iff]
  let T0 : Mat := Matrix.of fun i j => if i = i1 ∧ j = i1 then 1 else 0
  have hT0 : T0.IsSymm := by
    ext i j; simp only [T0, Matrix.transpose_apply, Matrix.of_apply]; split_ifs <;> simp_all
  have hnull := flat_sector_necessity
    (fun g T => ∀ x, ∃ L : ℝ, qf (ricci g x - (1/2 : ℝ) • scal g x • g x) (e 0) - L
      = κ * qf (T x) (e 0)) κ hκ hderive T0 hT0
    (fun x => ⟨_, sub_sub_cancel _ _⟩)
    ((1:ℝ) • e 0 + (1:ℝ) • e i1 + (0:ℝ) • e i1) (by
      rw [qf_three]; simp [eta_apply, hi1, Ne.symm hi1])
  rw [qf_three] at hnull
  simp [T0, hi1, Ne.symm hi1] at hnull

end EntEq.Curved
