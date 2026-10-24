/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  A local obstruction to a continuous `P(X)` bridge.

  A single kinetic function `P(X)` with a healthy cold/vacuum state at `X* > 0`
  (`P_X(X*) = 0`, timelike kinetic coefficient `K* = P_X + 2 X* P_XX > 0`) has `P_X < 0`
  just below `X*`. With the convention `X = −½ g^{μν}∂_μφ ∂_νφ` (so `X > 0` is timelike and
  `X < 0` spacelike, the MOND regime), `P_X` multiplies the spatial-gradient term, so `P_X < 0`
  is a wrong-sign gradient. Every continuous route from `X*` to any `X < X*` (in particular to a
  spacelike state) passes through it. `PX` stands for the derivative of `P`; only its
  differentiability at `X*` is used.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

open Filter Topology Set

namespace EntEq.B01

/-- **Local sign lemma.** -/
theorem px_negative_left (PX : ℝ → ℝ) (Xs PXXs : ℝ) (hXs : 0 < Xs)
    (hder : HasDerivAt PX PXXs Xs) (hzero : PX Xs = 0) (hK : 0 < PX Xs + 2 * Xs * PXXs) :
    ∃ δ > 0, ∀ x ∈ Ioo (Xs - δ) Xs, PX x < 0 := by
  have hP : 0 < PXXs := by
    rw [hzero, zero_add] at hK
    exact pos_of_mul_pos_right hK (by linarith)
  have hslope := hder.tendsto_slope.mono_left (nhdsLT_le_nhdsNE Xs)
  have hev : ∀ᶠ x in 𝓝[<] Xs, 0 < slope PX Xs x := hslope.eventually (lt_mem_nhds hP)
  obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp hev
  have hl' : l < Xs := hl
  refine ⟨Xs - l, by linarith, fun x hx => ?_⟩
  have hx' : x ∈ Ioo l Xs := ⟨by linarith [hx.1], hx.2⟩
  have hs := hsub hx'
  simp only [mem_ofPred_eq, slope_def_field, hzero, sub_zero] at hs
  have hneg : x - Xs < 0 := by linarith [hx.2]
  by_contra hc
  push Not at hc
  have : PX x / (x - Xs) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hc hneg.le
  linarith

/-- **Bridge obstruction.** Every continuous path from `X*` to some `X < X*` (for example a
spacelike `X < 0`) meets a point where `P_X < 0`. -/
theorem bridge_obstruction (PX : ℝ → ℝ) (Xs PXXs : ℝ) (hXs : 0 < Xs)
    (hder : HasDerivAt PX PXXs Xs) (hzero : PX Xs = 0) (hK : 0 < PX Xs + 2 * Xs * PXXs)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc 0 1)) (h0 : γ 0 = Xs) (h1 : γ 1 < Xs) :
    ∃ t ∈ Icc (0:ℝ) 1, PX (γ t) < 0 := by
  obtain ⟨δ, hδ, hneg⟩ := px_negative_left PX Xs PXXs hXs hder hzero hK
  set y := Xs - min δ (Xs - γ 1) / 2
  have hm : 0 < min δ (Xs - γ 1) := lt_min hδ (by linarith)
  have hy : y ∈ Icc (γ 1) (γ 0) := by
    constructor
    · have : min δ (Xs - γ 1) ≤ Xs - γ 1 := min_le_right _ _
      simp only [y]; linarith
    · rw [h0]; simp only [y]; linarith
  obtain ⟨t, ht, hγt⟩ := intermediate_value_Icc' (zero_le_one) hγ hy
  refine ⟨t, ht, ?_⟩
  rw [hγt]
  apply hneg
  constructor
  · simp only [y]; linarith [min_le_left δ (Xs - γ 1)]
  · simp only [y]; linarith

end EntEq.B01
