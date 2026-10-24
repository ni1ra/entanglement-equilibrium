/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Jacobson 2016's fixed-volume area deficit (eq. 7) from the *linearised* Riemann-normal-
  coordinate metric (`area_deficit_from_riemann`; `linDensity_rnc` ties the density to the
  first-order `√det` of `g = 1 − M/3` built from a Riemann tensor): `BallVol.volume_deficit_spacetime` computes
  the volume deficit of the linearised ball (eq. 3, with `Ω` the actual measure of the unit
  sphere), and `Ball.area_deficit_fixed_volume` turns it into the fixed-volume area deficit.
  Remaining premises: the RNC expansion `g = δ − (1/3) R x x + O(|x|³)` (and that the remainder
  is higher order), and `tr Ric_spatial = 2 G₀₀` (moment of time symmetry, Jacobson's eq. 6).
-/
import EntEq.BallVolume
import EntEq.Ball2016

open MeasureTheory Metric Set

namespace EntEq.BallVol

local notation "E" D => EuclideanSpace ℝ (Fin D)

/-- **Eq. 7 from the RNC expansion.** Let `δV(r)` be the volume deficit of the linearised
geodesic ball of radius `r` in `D = m + 1` spatial dimensions (`d = m + 2`). If the spatial
Ricci trace is `2 G₀₀`, then at every radius `ℓ > 0` the fixed-volume area deficit
`δV′(ℓ) − (d−2)/ℓ · δV(ℓ)` equals `−Ω ℓ^d G₀₀/(d² − 1)`, with `Ω` the measure of the unit
`(D−1)`-sphere. -/
theorem area_deficit_from_rnc (m : ℕ) (Ric : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (G00 ℓ : ℝ) (hℓ : 0 < ℓ) (hR : Ric.trace = 2 * G00) :
    let d : ℝ := m + 2
    let Ω : ℝ := (volume : Measure (E (m + 1))).toSphere.real univ
    let δV : ℝ → ℝ := fun r =>
      (∫ x in ball (0 : E (m + 1)) r, linDensity Ric x) - volume.real (ball (0 : E (m + 1)) r)
    ∃ δAℓ, HasDerivAt δV δAℓ ℓ ∧
      δAℓ - (d - 2) / ℓ * δV ℓ = -Ω * ℓ^(m+2) * G00 / (d^2 - 1) := by
  intro d Ω δV
  obtain ⟨δA, hd, heq⟩ := Ball.area_deficit_fixed_volume m Ω Ric.trace G00 ℓ hℓ.ne' hR
  have hfun : ∀ r, 0 ≤ r → δV r = -Ω * r^(m+3) * Ric.trace / (6 * (d - 1) * (d + 1)) := by
    intro r hr
    exact volume_deficit_spacetime m Ric hr
  refine ⟨δA, ?_, ?_⟩
  · apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hℓ] with r hr
    exact hfun r (le_of_lt hr)
  · rw [hfun ℓ hℓ.le]; exact heq

/-- The linearised density is exactly the RNC one: for a Riemann tensor `Riem`, with
`ε = |x|²`-scaling as in `rncQuad_smul`, `linDensity (ricci Riem) x = 1 + c` where `c` is the
derivative at `ε = 0` of `√det(1 − (ε/3) M(x))`, `M = rncQuad Riem`. -/
theorem linDensity_rnc {D : ℕ} (Riem : Fin D → Fin D → Fin D → Fin D → ℝ) (x : E D) :
    ∃ c, HasDerivAt (fun ε : ℝ => √(1 + ε • (-(1/3 : ℝ)) • rncQuad Riem x).det) c 0 ∧
      linDensity (ricci Riem) x = 1 + c :=
  ⟨_, hasDerivAt_sqrt_det_rnc Riem x, by simp only [linDensity]; ring⟩

/-- **Eq. 7 from a Riemann tensor.** `area_deficit_from_rnc` for the linearised RNC density of
an arbitrary Riemann tensor `Riem` (`linDensity_rnc`), whose spatial Ricci scalar
`tr (ricci Riem)` equals `2 G₀₀`. -/
theorem area_deficit_from_riemann (m : ℕ) (Riem : Fin (m+1) → Fin (m+1) → Fin (m+1) → Fin (m+1) → ℝ)
    (G00 ℓ : ℝ) (hℓ : 0 < ℓ) (hR : (ricci Riem).trace = 2 * G00) :
    let d : ℝ := m + 2
    let Ω : ℝ := (volume : Measure (E (m + 1))).toSphere.real univ
    let δV : ℝ → ℝ := fun r =>
      (∫ x in ball (0 : E (m + 1)) r, linDensity (ricci Riem) x)
        - volume.real (ball (0 : E (m + 1)) r)
    ∃ δAℓ, HasDerivAt δV δAℓ ℓ ∧
      δAℓ - (d - 2) / ℓ * δV ℓ = -Ω * ℓ^(m+2) * G00 / (d^2 - 1) :=
  area_deficit_from_rnc m (ricci Riem) G00 ℓ hℓ hR

end EntEq.BallVol
