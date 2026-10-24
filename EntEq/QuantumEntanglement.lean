/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  Quantum (non-commuting, finite-dimensional) versions of the two entanglement inputs proved
  for commuting states in `EntEq.Entanglement`. States are `n × n` complex matrices; `log` and
  the entropy are defined through Mathlib's continuous functional calculus for Hermitian
  matrices.

  * `klein`, `relEnt_nonneg`: Klein's inequality, `D(ρ‖σ) ≥ 0` for density matrices, `σ > 0`.
  * `casini_bekenstein`: `S(ρ) − S(σ) ≤ Tr(ρK) − Tr(σK)` for the thermal `σ = e^{−K}/Z`.
  * `hasDerivAt_vnS`, `first_law`: `d/dt S(σ + tδ)|₀ = −Tr(δ log σ) = Tr(δK)` for any Hermitian
    traceless `δ`, commuting with `σ` or not.

  Infinite-dimensional (type III) algebras, where the modular Hamiltonian is unbounded, are
  not covered.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import EntEq.Entanglement

open Matrix Filter Topology Real
open scoped ComplexOrder

namespace EntEq.QEnt

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every real function is continuous on the (finite) real spectrum of a complex matrix. -/
lemma contOn (f : ℝ → ℝ) (A : Matrix n n ℂ) : ContinuousOn f (spectrum ℝ A) :=
  Matrix.finite_real_spectrum.continuousOn f

/-- Overlap weight `|⟨aᵢ|bⱼ⟩|²` between the `i`-th eigenvector of `A` and the `j`-th of `B`. -/
noncomputable def wt {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) : ℝ :=
  Complex.normSq ((star (hA.eigenvectorUnitary : Matrix n n ℂ) * hB.eigenvectorUnitary) i j)

/-- Overlap weights are nonnegative. -/
lemma wt_nonneg {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    0 ≤ wt hA hB i j := Complex.normSq_nonneg _

/-- **Double-sum trace formula.** For Hermitian `A`, `B` with eigenvalues `aᵢ`, `bⱼ`,
`Tr(f(A) g(B)) = ∑ᵢⱼ |⟨aᵢ|bⱼ⟩|² f(aᵢ) g(bⱼ)`. -/
lemma trace_cfc_mul_cfc {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    trace (cfc f A * cfc g B) =
      ((∑ i, ∑ j, wt hA hB i j * f (hA.eigenvalues i) * g (hB.eigenvalues j) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, hB.cfc_eq, IsHermitian.cfc, IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Unitary.conjStarAlgAut_apply]
  set U : Matrix n n ℂ := ↑hA.eigenvectorUnitary
  set V : Matrix n n ℂ := ↑hB.eigenvectorUnitary
  set D := diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues : n → ℂ)
  set E := diagonal (RCLike.ofReal ∘ g ∘ hB.eigenvalues : n → ℂ)
  have hcyc : trace (U * D * star U * (V * E * star V)) =
      trace (D * (star U * V) * E * star (star U * V)) := by
    rw [star_mul, star_star, show U * D * star U * (V * E * star V) =
      U * (D * star U * V * E * star V) by simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hcyc]
  set W := star U * V
  have hX : ∀ i k, (D * W * E) i k =
      (f (hA.eigenvalues i) : ℂ) * W i k * (g (hB.eigenvalues k) : ℂ) := by
    intro i k; simp [D, E, mul_diagonal, diagonal_mul]
  have hw : ∀ i j, (wt hA hB i j : ℂ) = W i j * star (W i j) := by
    intro i j; rw [Complex.star_def, Complex.mul_conj]; rfl
  simp only [trace, diag_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hX, star_apply, hw]
  ring

/-- Trace of a matrix function: `Tr f(A) = ∑ᵢ f(aᵢ)` for Hermitian `A`. -/
lemma trace_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    trace (cfc f A) = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← Matrix.mul_assoc,
    UnitaryGroup.star_mul_self, Matrix.one_mul, trace_diagonal]
  push_cast; rfl

/-- The matrix logarithm `log A`, defined by the functional calculus (on Hermitian `A`; it
uses the real `Real.log`, so `log 0 = 0` on a kernel). -/
noncomputable def mlog (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.log A

/-- Von Neumann entropy `S(ρ) = −Tr(ρ log ρ)` (real part of the trace). -/
noncomputable def vnS (ρ : Matrix n n ℂ) : ℝ := -(trace (ρ * mlog ρ)).re

/-- Relative entropy `D(ρ‖σ) = Tr(ρ log ρ − ρ log σ)` (real part of the trace). This is the
standard quantity when `σ` is positive definite, as every theorem below assumes; with `log 0 = 0`
it would be finite where the standard definition is `+∞`. -/
noncomputable def relEnt (ρ σ : Matrix n n ℂ) : ℝ := (trace (ρ * mlog ρ - ρ * mlog σ)).re

/-- **Klein's inequality.** For a positive semidefinite `ρ` and a positive definite `σ`,
`Tr ρ − Tr σ ≤ Tr(ρ log ρ − ρ log σ)`. Proof: in the two eigenbases the difference is
`∑ᵢⱼ |⟨aᵢ|bⱼ⟩|² (aᵢ log aᵢ − aᵢ log bⱼ − aᵢ + bⱼ)`, and every bracket is `≥ 0`. -/
theorem klein {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosDef) :
    (trace ρ).re - (trace σ).re ≤ relEnt ρ σ := by
  have hρH := hρ.1
  have hσH := hσ.1
  have e1 : trace (ρ * mlog ρ) =
      trace (cfc (fun x => x * Real.log x) ρ * cfc (fun _ => (1 : ℝ)) σ) := by
    rw [cfc_const_one ℝ σ hσH.isSelfAdjoint, Matrix.mul_one, cfc_mul (fun x => x) Real.log ρ (contOn _ _) (contOn _ _),
      cfc_id' ℝ ρ hρH.isSelfAdjoint, mlog]
  have e2 : trace (ρ * mlog σ) = trace (cfc (fun x : ℝ => x) ρ * cfc Real.log σ) := by
    rw [cfc_id' ℝ ρ hρH.isSelfAdjoint, mlog]
  have e3 : trace ρ = trace (cfc (fun x : ℝ => x) ρ * cfc (fun _ => (1 : ℝ)) σ) := by
    rw [cfc_const_one ℝ σ hσH.isSelfAdjoint, Matrix.mul_one, cfc_id' ℝ ρ hρH.isSelfAdjoint]
  have e4 : trace σ = trace (cfc (fun _ => (1 : ℝ)) ρ * cfc (fun x : ℝ => x) σ) := by
    rw [cfc_const_one ℝ ρ hρH.isSelfAdjoint, Matrix.one_mul, cfc_id' ℝ σ hσH.isSelfAdjoint]
  rw [relEnt, trace_sub, e1, e2, e3, e4]
  simp only [trace_cfc_mul_cfc hρH hσH, Complex.sub_re, Complex.ofReal_re]
  have hterm : ∀ i j, wt hρH hσH i j * hρH.eigenvalues i * 1 - wt hρH hσH i j * 1 * hσH.eigenvalues j
      ≤ wt hρH hσH i j * (hρH.eigenvalues i * Real.log (hρH.eigenvalues i)) * 1 -
        wt hρH hσH i j * hρH.eigenvalues i * Real.log (hσH.eigenvalues j) := by
    intro i j
    have h := EntEq.Ent.gibbs_term _ _ (hρ.eigenvalues_nonneg i) (hσ.eigenvalues_pos j)
    have := mul_le_mul_of_nonneg_left h (wt_nonneg hρH hσH i j)
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm i j
  simp only [Finset.sum_sub_distrib] at hsum
  linarith

/-- Klein's inequality for states of equal trace (e.g. two density matrices): `D(ρ‖σ) ≥ 0`. -/
theorem relEnt_nonneg {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (htr : trace ρ = trace σ) : 0 ≤ relEnt ρ σ := by
  have := klein hρ hσ; rw [htr, sub_self] at this; exact this

/-- A Hermitian matrix whose real spectrum is positive is positive definite. -/
lemma posDef_of_spectrum {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : spectrum ℝ A ⊆ Set.Ioi 0) : A.PosDef :=
  hA.posDef_iff_eigenvalues_pos.mpr fun i => h (hA.eigenvalues_mem_spectrum_real i)

/-- Partition function `Z = Tr e^{−K}`. -/
noncomputable def Z (K : Matrix n n ℂ) : ℝ := (trace (cfc (fun x => exp (-x)) K)).re

/-- Thermal (modular) state `σ = e^{−K}/Z` of a Hermitian modular Hamiltonian `K`. -/
noncomputable def gibbs (K : Matrix n n ℂ) : Matrix n n ℂ := cfc (fun x => exp (-x) / Z K) K

/-- The partition function of a Hermitian `K` is positive (nonempty index type). -/
lemma Z_pos [Nonempty n] {K : Matrix n n ℂ} (hK : K.IsHermitian) : 0 < Z K := by
  rw [Z, trace_cfc hK, Complex.ofReal_re]
  exact Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty

/-- The thermal state of a Hermitian `K` is positive definite. -/
lemma gibbs_posDef [Nonempty n] {K : Matrix n n ℂ} (hK : K.IsHermitian) : (gibbs K).PosDef := by
  refine posDef_of_spectrum (isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate _ K)) ?_
  rw [gibbs, cfc_map_spectrum _ K hK.isSelfAdjoint (contOn _ _)]
  rintro _ ⟨x, -, rfl⟩
  exact div_pos (exp_pos _) (Z_pos hK)

/-- The thermal state has trace one. -/
lemma trace_gibbs [Nonempty n] {K : Matrix n n ℂ} (hK : K.IsHermitian) : trace (gibbs K) = 1 := by
  have hZ := Z_pos hK
  rw [Z, trace_cfc hK, Complex.ofReal_re] at hZ
  rw [gibbs, trace_cfc hK, ← Finset.sum_div, Z, trace_cfc hK, Complex.ofReal_re,
    div_self hZ.ne', Complex.ofReal_one]

/-- `log σ = −K − log Z` for the thermal state, paired against any `ρ` under the trace. -/
lemma trace_mul_mlog_gibbs [Nonempty n] {K : Matrix n n ℂ} (hK : K.IsHermitian)
    (ρ : Matrix n n ℂ) :
    (trace (ρ * mlog (gibbs K))).re = -(trace (ρ * K)).re - Real.log (Z K) * (trace ρ).re := by
  have hZ := Z_pos hK
  have hlog : mlog (gibbs K) = cfc (fun x => -x - Real.log (Z K)) K := by
    rw [mlog, gibbs, ← cfc_comp Real.log _ K hK.isSelfAdjoint
      ((Matrix.finite_real_spectrum.image _).continuousOn _) (contOn _ _)]
    congr 1; funext x
    simp [Function.comp, Real.log_div (exp_pos _).ne' hZ.ne', Real.log_exp]
  rw [hlog, cfc_sub (fun x : ℝ => -x) (fun _ => Real.log (Z K)) K, cfc_neg (fun x : ℝ => x) K,
    cfc_id' ℝ K hK.isSelfAdjoint, cfc_const _ K hK.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  simp [Matrix.mul_sub, trace_sub, trace_neg, trace_smul]

/-- Entropy of the thermal state: `S(σ) = Tr(σK) + log Z`. -/
lemma vnS_gibbs [Nonempty n] {K : Matrix n n ℂ} (hK : K.IsHermitian) :
    vnS (gibbs K) = (trace (gibbs K * K)).re + Real.log (Z K) := by
  rw [vnS, trace_mul_mlog_gibbs hK, trace_gibbs hK]; simp; ring

/-- **Casini–Bekenstein bound (quantum, finite-dimensional).** For a Hermitian modular
Hamiltonian `K`, thermal state `σ = e^{−K}/Z`, and any density matrix `ρ` (positive
semidefinite, trace one): `S(ρ) − S(σ) ≤ Tr(ρK) − Tr(σK)`. -/
theorem casini_bekenstein [Nonempty n] {K ρ : Matrix n n ℂ} (hK : K.IsHermitian)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    vnS ρ - vnS (gibbs K) ≤ (trace (ρ * K)).re - (trace (gibbs K * K)).re := by
  have hk := klein hρ (gibbs_posDef hK)
  rw [relEnt, trace_sub, Complex.sub_re, trace_mul_mlog_gibbs hK, htr, trace_gibbs hK] at hk
  rw [vnS_gibbs hK, vnS]
  simp at hk
  linarith

section Continuity

/- The operator norm is only used here, to borrow Mathlib's continuity of the functional
calculus and upper hemicontinuity of the spectrum; its topology is the usual one on matrices. -/
open scoped Matrix.Norms.L2Operator

/-- Near a positive definite `σ`, the line `σ + tδ` (with `δ` Hermitian) stays positive
definite, and `log(σ + tδ) → log σ` as `t → 0`. -/
lemma line_posDef_and_tendsto_mlog {σ δ : Matrix n n ℂ} (hσ : σ.PosDef) (hδ : δ.IsHermitian) :
    (∀ᶠ t in 𝓝 (0 : ℝ), (σ + t • δ).PosDef) ∧
      Tendsto (fun t : ℝ => mlog (σ + t • δ)) (𝓝 0) (𝓝 (mlog σ)) := by
  have hline : Tendsto (fun t : ℝ => σ + t • δ) (𝓝 0) (𝓝 σ) := by
    have : Continuous (fun t : ℝ => σ + t • δ) := by fun_prop
    simpa using this.tendsto 0
  have hspec : spectrum ℝ σ ⊆ Set.Ioi 0 := by
    rw [hσ.1.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩; exact hσ.eigenvalues_pos i
  have hev : ∀ᶠ M in 𝓝 σ, spectrum ℝ M ⊆ Set.Ioi 0 :=
    (upperHemicontinuousAt_iff_forall_isOpen.mp
      (upperHemicontinuous_spectrum ℝ (Matrix n n ℂ) σ)) _ isOpen_Ioi hspec
  have hpd : ∀ᶠ t in 𝓝 (0 : ℝ), (σ + t • δ).PosDef := by
    filter_upwards [hline.eventually hev] with t ht
    exact posDef_of_spectrum (hσ.1.add (hδ.smul rfl)) ht
  refine ⟨hpd, ?_⟩
  have hcont := (CFC.continuousOn_log (A := Matrix n n ℂ)) σ ⟨hσ.1.isSelfAdjoint, hσ.isUnit⟩
  refine hcont.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hline, ?_⟩)
  filter_upwards [hpd] with t ht
  exact ⟨ht.1.isSelfAdjoint, ht.isUnit⟩

end Continuity

/-- **First law of entanglement entropy (quantum, general reference state).** Let `σ` be
positive definite and `δ` Hermitian with `Tr δ = 0` (it need not commute with `σ`). Then
`t ↦ S(σ + tδ)` is differentiable at `t = 0` with derivative `−Tr(δ log σ)`.
Proof: Klein's inequality used twice squeezes `S(σ + tδ) − S(σ)` between `−t Tr(δ log σ)` and
`−t Tr(δ log(σ + tδ))`, and `log(σ + tδ) → log σ`. -/
theorem hasDerivAt_vnS {σ δ : Matrix n n ℂ} (hσ : σ.PosDef) (hδ : δ.IsHermitian)
    (htr : trace δ = 0) :
    HasDerivAt (fun t : ℝ => vnS (σ + t • δ)) (-(trace (δ * mlog σ)).re) 0 := by
  obtain ⟨hpd, hlim⟩ := line_posDef_and_tendsto_mlog hσ hδ
  set L : ℝ → ℝ := fun t => (trace (δ * mlog (σ + t • δ))).re with hL
  have hLlim : Tendsto L (𝓝 0) (𝓝 (trace (δ * mlog σ)).re) := by
    have hc : Continuous (fun M : Matrix n n ℂ => (trace (δ * M)).re) :=
      Complex.continuous_re.comp (continuous_const.matrix_mul continuous_id).matrix_trace
    exact (hc.tendsto _).comp hlim
  -- trace bookkeeping along the line
  have htrace : ∀ t : ℝ, ∀ M : Matrix n n ℂ,
      (trace ((σ + t • δ) * M)).re = (trace (σ * M)).re + t * (trace (δ * M)).re := by
    intro t M; simp [Matrix.add_mul, trace_add, trace_smul]
  have htrline : ∀ t : ℝ, (trace (σ + t • δ)).re = (trace σ).re := by
    intro t; simp [trace_add, trace_smul, htr]
  -- the squeeze: `−t L(t) ≤ S(σ+tδ) − S(σ) ≤ −t L(0)`
  have hsq : ∀ᶠ t in 𝓝 (0 : ℝ),
      -t * L t ≤ vnS (σ + t • δ) - vnS σ ∧ vnS (σ + t • δ) - vnS σ ≤ -t * L 0 := by
    filter_upwards [hpd] with t ht
    have k1 := klein hσ.posSemidef ht
    have k2 := klein ht.posSemidef hσ
    rw [relEnt, trace_sub, Complex.sub_re, htrline] at k1 k2
    rw [htrace t (mlog (σ + t • δ)), htrace t (mlog σ)] at k2
    simp only [vnS, hL, zero_smul, add_zero]
    rw [htrace t (mlog (σ + t • δ))]
    constructor <;> nlinarith
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), |L t - L 0| ≤ ε := by
    have := hLlim.eventually (Metric.closedBall_mem_nhds _ hε)
    filter_upwards [this] with t ht
    simpa [Metric.mem_closedBall, Real.dist_eq, hL] using ht
  filter_upwards [hsq, hnear] with t ht hn
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, zero_smul, add_zero]
  have hL0 : L 0 = (trace (δ * mlog σ)).re := by simp [hL]
  rw [← hL0]
  obtain ⟨h1, h2⟩ := ht
  have hab : |vnS (σ + t • δ) - vnS σ - t * -L 0| ≤ |t| * |L t - L 0| := by
    rw [abs_le]
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
      constructor <;> nlinarith [abs_le.mp (le_refl |L t - L 0|), le_abs_self (L t - L 0),
        neg_abs_le (L t - L 0)]
    · rw [abs_of_nonpos h]
      constructor <;> nlinarith [le_abs_self (L t - L 0), neg_abs_le (L t - L 0)]
  calc _ ≤ |t| * |L t - L 0| := hab
    _ ≤ ε * |t| := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hn (abs_nonneg t)

/-- **First law of entanglement (quantum, finite-dimensional).** For a Hermitian modular
Hamiltonian `K`, thermal state `σ = e^{−K}/Z`, and any Hermitian traceless direction `δ`
(not required to commute with `σ`): `d/dt S(σ + tδ) |_{t=0} = Tr(δK)`, i.e. `δS = δ⟨K⟩`. -/
theorem first_law [Nonempty n] {K δ : Matrix n n ℂ} (hK : K.IsHermitian) (hδ : δ.IsHermitian)
    (htr : trace δ = 0) :
    HasDerivAt (fun t : ℝ => vnS (gibbs K + t • δ)) (trace (δ * K)).re 0 := by
  have h := hasDerivAt_vnS (gibbs_posDef hK) hδ htr
  rwa [trace_mul_mlog_gibbs hK, htr, Complex.zero_re, mul_zero, sub_zero, neg_neg] at h

end EntEq.QEnt
