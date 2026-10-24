/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The 1995 derivation as one theorem on an arbitrary smooth spacetime.

  Premise (physics): at every point `x` and for every null direction `k`, the local Rindler
  horizon through `x` with generator `k` has an expansion `θ`, shear `σ`, and profiles
  `R(s)`, `T(s)` along the generator with `R(0) = Ric_x(k,k)`, `T(0) = T_x(k,k)`, the horizon is
  momentarily stationary (`θ(0) = σ(0) = 0`), the Raychaudhuri equation holds at `s = 0`, and
  Clausius `δQ = T_Unruh · δS` with `δS = δA/(4Għ)`, `δA = −∫θ`, holds to `o(ε²)`.
  Plus `∇ᵃT_ab = 0`. Everything else (Raychaudhuri linearisation, the null-cone lemma, metric
  compatibility, the contracted Bianchi identity, the integration constant) is proved.
-/
import EntEq.AreaClausius
import EntEq.BianchiGeneral

open Filter Topology Matrix

namespace EntEq.Curved

variable {n : ℕ}

local notation "E" => (Fin (n+1) → ℝ)
local notation "Mat" => Matrix (Fin (n+1)) (Fin (n+1)) ℝ

/-- **Clausius on every local Rindler horizon ⇒ Einstein's equation, on any smooth spacetime.**
With `g = Pᵀ η P` (`P` smooth, invertible), a conserved symmetric `T` with differentiable
components, surface gravity `κ ≠ 0`, `ħ, G ≠ 0`, and the per-horizon premise above, there is a
constant `Λ` with `Ric − ½ R g + Λ g = 8πG T`. -/
theorem clausius_to_einstein (P : E → Mat) (hPs : Sm P) (hP : ∀ x, IsUnit (P x).det)
    (T : E → Mat) (hTd : ∀ a b, Differentiable ℝ fun y => T y a b) (hTs : ∀ x, (T x).IsSymm)
    (hcons : ∀ x b, covDiv (gP P) T x b = 0) (d κ ħ G : ℝ) (hκ : κ ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0)
    (horizon : ∀ x k, qf (gP P x) k = 0 → ∃ θ σ Rs Ts : ℝ → ℝ,
      Continuous θ ∧ Continuous Ts ∧
      Rs 0 = qf (ricci (gP P) x) k ∧ Ts 0 = qf (T x) k ∧
      HasDerivAt θ (-(θ 0)^2/(d-2) - (σ 0)^2 - Rs 0) 0 ∧ θ 0 = 0 ∧ σ 0 = 0 ∧
      Tendsto (fun ε =>
        (κ * (∫ s in (0:ℝ)..ε, s * Ts s)
          - (ħ * κ / (2 * Real.pi)) * (1 / (4 * G * ħ)) * (-∫ s in (0:ℝ)..ε, θ s)) / ε^2)
        (𝓝[>] 0) (𝓝 0)) :
    ∃ Λ : ℝ, ∀ x, ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x + Λ • gP P x
      = (8 * Real.pi * G) • T x := by
  apply curved_clausius_general P hPs hP T hTd hTs hcons (8 * Real.pi * G)
  intro x k hk
  obtain ⟨θ, σ, Rs, Ts, hθc, hTc, hR0, hT0, hray, hθ0, hσ0, hcl⟩ := horizon x k hk
  rw [← hR0, ← hT0]
  have := clausius_from_raychaudhuri θ σ Rs Ts d κ ħ G hθc hTc hray hθ0 hσ0 hκ hħ hG hcl
  rw [this]

/-- **The 2016 chain on any smooth spacetime.** With `g = Pᵀ η P` (`P` smooth, invertible), a
conserved symmetric `T` and a differentiable scalar `L`, if
`G(u,u) − L = κₑ T(u,u)` for every unit timelike `u` at every point (`G = Ric − ½R g`), then
`G + L g = κₑ T` and `L` is constant (Jacobson 2016, eq. 25–26). -/
theorem curved_equilibrium_general (P : E → Mat) (hPs : Sm P) (hP : ∀ x, IsUnit (P x).det)
    (T : E → Mat) (hTd : ∀ a b, Differentiable ℝ fun y => T y a b) (hTs : ∀ x, (T x).IsSymm)
    (hcons : ∀ x b, covDiv (gP P) T x b = 0) (L : E → ℝ) (hL : Differentiable ℝ L) (κₑ : ℝ)
    (hEq : ∀ x u, qf (gP P x) u = -1 →
      qf (ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x) u - L x = κₑ * qf (T x) u) :
    (∀ x, ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x + L x • gP P x = κₑ • T x)
      ∧ ∃ c : ℝ, ∀ x, L x = c := by
  have hg := hPs.gP
  have hs := gP_symm P
  have hdet := gP_det P hP
  have hgd : ∀ a b, Differentiable ℝ fun y => gP P y a b := fun a b => diff_of_smooth (hg a b)
  have hcompat : ∀ φ, divGen (gP P) (mulGen (gP P) hg φ) = Flat.dL φ := fun φ => by
    ext x b
    exact covDiv_smul_metric (gP P) hs hdet hgd φ.1 φ.2 x b
  let Tv : Flat.Vsub n := ⟨T, hTd⟩
  let Ric : Flat.Vsub n := ⟨ricci (gP P), ricci_diff hg hdet⟩
  let Rs : Flat.Ssub n := ⟨scal (gP P), scal_diff hg hdet⟩
  let Lv : Flat.Ssub n := ⟨L, hL⟩
  have hRic : divGen (gP P) Ric = (1/2 : ℝ) • Flat.dL Rs := by
    ext x b; exact bianchi_general (gP P) hg hs hdet x b
  have hG : divGen (gP P) (Ric - (1/2 : ℝ) • mulGen (gP P) hg Rs) = 0 := by
    rw [map_sub, map_smul, hcompat, hRic, sub_self]
  have hGeval : ∀ x, (Ric - (1/2 : ℝ) • mulGen (gP P) hg Rs).1 x
      = ricci (gP P) x - (1/2 : ℝ) • scal (gP P) x • gP P x := fun x => by
    simp [mulGen, Ric, Rs]
  obtain ⟨hfield, c, hc⟩ := @equilibrium_chain n (Fin (n+1) → ℝ) (Flat.Vsub n) (Flat.Ssub n)
    ((Fin (n+1) → ℝ) → Fin (n+1) → ℝ) _ _ _ _ _ _ P hP
    (Flat.Vsub n).subtype Subtype.val_injective (Flat.Ssub n).subtype
    (mulGen (gP P) hg) (fun φ x => rfl) Flat.one (divGen (gP P)) Flat.dL hcompat
    (fun φ hφ => by
      refine ⟨φ.1 0, ?_⟩
      have hconst := is_const_of_fderiv_eq_zero φ.2 (fun x => clm_eq_zero_of_basis _
        fun b => congrFun (congrFun hφ x) b)
      ext x; simp [Flat.one, hconst x 0])
    (Ric - (1/2 : ℝ) • mulGen (gP P) hg Rs) Tv Lv κₑ
    (fun x => by
      rw [Submodule.subtype_apply, hGeval]
      exact (ricci_symm hg hs hdet x).sub (((hs x).smul _).smul _)) hTs
    (fun x u hu => by
      rw [Submodule.subtype_apply, hGeval]
      exact hEq x u hu)
    hG (by ext x b; exact hcons x b)
  refine ⟨fun x => ?_, c, fun x => ?_⟩
  · have := congrArg (fun v : Flat.Vsub n => v.1 x) hfield
    simp only [Submodule.coe_add, Pi.add_apply, hGeval] at this
    simpa [mulGen, Lv, Tv] using this
  · have := congrArg (fun v : Flat.Ssub n => v.1 x) hc
    simpa [Flat.one, Lv] using this

end EntEq.Curved
