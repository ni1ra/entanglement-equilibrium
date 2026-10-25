# entanglement-equilibrium

A Lean 4 / Mathlib formalisation of three connected topics:

1. the **null-cone lemma**: a symmetric bilinear form that vanishes on the null cone of a
   nondegenerate indefinite form is a multiple of it, with a sharp count of how many null
   vectors are needed;
2. **Jacobson's thermodynamic derivation of Einstein's equation** (1995, Clausius relation on
   local horizons) and the **entanglement-equilibrium chain** (2016, small geodesic balls);
3. **perturbation-level results for AeST and Khronon**, two relativistic completions of MOND,
   stated about the published linear perturbation equations.

The project builds against Mathlib with no `sorry` and no added axioms. Where a result needs a
physical premise, the premise is an explicit hypothesis of the theorem (see
[What is not claimed](#what-is-not-claimed)).

- Lean `v4.36.0-rc1`, Mathlib tag `v4.36.0-rc1` (commit `625d8914199bc567cca9b91f90e8e5afafa5ae51`).
- 42 modules under `EntEq/`.

## What is formalised

### 1. The null-cone lemma (`NullCone`, `NullConeGeneral`, `Certificate`, `Stability`)

- `null_cone_bilin`, `null_cone_bilin_iff` (`NullConeGeneral`): for a nondegenerate symmetric
  bilinear form `B` on a finite-dimensional real vector space that takes both a negative and a
  positive value (indefinite, any signature), a symmetric form `A` with `A k k = 0` for every
  `k` with `B k k = 0` is `c • B` for a real `c`. The converse is immediate.
  `null_cone_fails_definite` gives a counterexample for the Euclidean plane, so indefiniteness
  is needed.
- `null_cone_lemma`, `null_cone_iff` (`NullCone`): the same statement for Minkowski space
  `diag(-1, 1, ..., 1)` in every dimension `n + 1`, proved from the explicit vectors
  `e₀ ± eᵢ` and `5e₀ + 3eᵢ + 4eⱼ`.
- `null_cone_certificate`, `certificate_minimal` (`Certificate`): in `n + 1` dimensions these
  `(n² + 3n)/2` vectors suffice, and no family of fewer vectors does (null or not). In four
  dimensions this is **9 null vectors suffice and 8 do not**.
- `timelike_certificate`, `timelike_certificate_minimal` (`CertificateTimelike`): the
  counterpart for unit timelike vectors, where `X(u,u)` is constant: 10 vectors suffice in four
  dimensions and no 9 do.
- `null_cone_stable_sharp`, `null_cone_stable_attained` (`Stability`): a quantitative version.
  If `|X(k,k)| ≤ ε |k|²` on null `k`, then every component of `X - cη` is within `2ε`
  for `c = -X₀₀`, and the constant 2 is attained. This covers only the pointwise, trace-free
  step, in one orthonormal frame: an approximate null relation gives the trace-free part of
  Einstein's equation to `2ε` at each point. It says nothing about the constancy of `Λ`, which
  needs derivatives of the scalar and is not covered.

### 2. Jacobson 1995: Clausius on every local horizon implies Einstein's equation

**Raychaudhuri's equation is proved from the metric** (`Raychaudhuri`). For a smooth vector
field `K` write `∇_b K^a = ∂_b K^a + Γ^a_bc K^c`, `θ = ∇_a K^a` and `A^a = K^b ∇_b K^a`.
`Curved.raychaudhuri`: for every smooth `K` on every smooth symmetric invertible metric, at
every point,
`K^c ∂_c θ = ∇_a A^a − (∇_a K^b)(∇_b K^a) − R_ab K^a K^b` (the trace form of the equation; the
index algebra `raychaudhuri_alg` needs only a torsion-free connection).
`raychaudhuri_bifurcation`: where `∇K = 0` and `∂A = 0`, `K^c ∂_c θ = −R(K,K)`.

`Curved.clausius_to_einstein_geom` (`Horizon`). Take a smooth metric `g = Pᵀ η P` on `ℝⁿ⁺¹` (a
global smooth frame `P`, invertible everywhere) and a symmetric stress tensor `T` with
differentiable components and `∇ᵃ T_ab = 0`. A *local horizon* through `x` with generator `k`
(`IsLocalHorizon`) is a smooth vector field `K` with `K(x) = k`, `∇K(x) = 0` and
`∂(K^b∇_b K)(x) = 0` (stationary at the bifurcation point, geodesic to first order).
Suppose that at every point `x`, for every null `k`, every local horizon `K` and every curve `γ`
leaving `x` with velocity `k`, Clausius `δQ = T_Unruh · δA / (4Għ)` holds up to `o(ε²)`, with
`δQ = κ ∫ s T(K,K) ds` and `δA = −∫ θ ds`, `θ` the expansion of `K` along `γ`. Then there is a
constant `Λ` with `Ric − ½ R g + Λ g = 8πG T` at every point.

- `horizon_exists`: local horizons exist through every point along every vector (an explicit
  quadratic field), so the premise is never vacuous. `horizon_focusing`: every local horizon
  has `dθ/ds = −Ric(k,k)` at `x`, so quantifying over all of them or over one is the same
  premise.
- `einstein_to_clausius_geom`: the converse. **The premise is equivalent to Einstein's
  equation**, and pointwise to the null relation `Ric(k,k) = 8πG T(k,k)`. The theorem
  restates that relation in thermodynamic words; it does not derive gravity from
  thermodynamics. The Unruh temperature, the area law `S = A/4Għ` and the identification of
  `δQ` with `T(K,K)` enter as fixed coefficients.

The earlier `Curved.clausius_to_einstein` (`Capstone`) is kept. It takes Raychaudhuri at the
bifurcation point as a hypothesis on free functions `θ, σ, R, T`, and its premise is
likewise pointwise equivalent to the null relation.

Everything between the hypotheses and the conclusion is proved: Raychaudhuri, the null-cone
lemma, a coordinate Levi-Civita connection with Riemann, Ricci and scalar curvature
(`CurvedCoords`), metric compatibility and the contracted Bianchi identity for a general
smooth metric (`BianchiGeneral`), and the integration step (`Bianchi`, `Unimodular`). Mathlib
has no Levi-Civita connection or Bianchi identity, so these are built in coordinates.

Related: `flat_clausius`, `flat_equilibrium` (`FlatChain`) discharge every hypothesis on
Minkowski space with Mathlib's Fréchet derivative; `einstein_to_null`, `einstein_to_clausius`,
`einstein_to_ball` (`Converse`) give the algebraic converses; `unimodular_to_einstein`,
`vacuum_energy_drops_out` (`Unimodular`) show the null-cone output is the trace-free equation
and that adding `ρ_vac g` to `T` leaves it unchanged; `caustic` (`Caustic`) is the null
focusing theorem.

### 3. Jacobson 2016: the entanglement-equilibrium chain

- `curved_equilibrium_general` (`Capstone`), `equilibrium_chain` (`Equilibrium2016`): if
  `G(u,u) - L = κₑ T(u,u)` for every unit timelike `u` at every point, then
  `G + L g = κₑ T`, and with `∇ᵃ T_ab = 0` the scalar `L` is a spacetime constant.
- How strong the premise is (`PremiseStrength`). `ball_iff_null`: at a point, "a scalar `L`
  with `G(u,u) − L = κ T(u,u)` for every unit timelike `u`" holds if and only if
  `Ric(k,k) = κ T(k,k)` for every null `k`; the 2016 premise is not weaker than the 1995 one.
  `flat_sector_necessity`: any premise at all that yields Einstein's equation for every smooth
  metric and conserved `T` must force `T(k,k) = 0` on null `k` for Minkowski space with
  constant `T`. `one_frame_insufficient`: one rest frame per point (one number per point) does
  not yield Einstein's equation.
- `ball_weight`, `ball_equilibrium` (`Ball2016`), `ball_to_einstein` (`BallChain`): the
  small-ball computation. The conformal-field modular weight gives
  `∫₀^ℓ r^{d-2} (ℓ² - r²)/(2ℓ) dr = ℓ^d/(d² - 1)`, the same coefficient as the fixed-volume
  area deficit, and stationarity of `η δA + δS_ent` gives `G₀₀ = 8πG T₀₀`.
- `BallVol.*` (`BallVolume`, `BallComposed`): the second moments of a Euclidean ball, and the
  volume and fixed-volume area deficits (Jacobson's eqs. 3 and 7) from the linearised
  Riemann-normal-coordinate metric `g = δ - ⅓ R x x` of an arbitrary Riemann tensor.
- `RNC.*`, `NormalCoords.*` (`RNC`, `NormalCoords`, `NormalCoordsGeneral`, `RiemannLinear`,
  `InverseSmooth`): normal coordinates are constructed to second order for any smooth
  symmetric invertible metric, and the second derivatives of the metric in them are shown to be
  `-⅓(R_acbd + R_adbc)`.
- `QEnt.klein`, `QEnt.relEnt_nonneg`, `QEnt.casini_bekenstein`, `QEnt.first_law`
  (`QuantumEntanglement`): for finite-dimensional density matrices (matrix logarithm through
  Mathlib's continuous functional calculus), Klein's inequality, positivity of relative entropy,
  Casini's form of the Bekenstein bound, and the non-commuting first law of entanglement
  `d/dt S(σ + tδ)|₀ = Tr(δK)`. `Entanglement` has the commuting versions. `QEnt.klein` is the
  unnormalised trace form (`ρ ⪰ 0`, `σ ≻ 0`, with the `Tr ρ − Tr σ` term); Physlib already has
  Klein's inequality for states, `inner_log_sub_log_nonneg` (`QuantumInfo/Entropy/Relative`).
  None of these finite-dimensional results is used by the 1995 or 2016 chains.
- Supporting results: `unruh_temperature` (`Unruh`, the geometric half of the Unruh effect),
  `first_law_schwarzschild` (`Hawking`), `concurrence` (`BMV`, the entanglement witness
  `|sin(Δφ/2)|`) and `diffusion_lower_bound` (`TradeOff`, the scalar decoherence-diffusion
  trade-off).

### 4. AeST and Khronon perturbation results

These are theorems about the reduced linear perturbation equations of the published theories,
Aether Scalar Tensor (AeST, Skordis and Złośnik, arXiv:2007.00082) and relativistic Khronon
(Blanchet and Skordis, arXiv:2404.06584). The equations are taken as the setting of each
theorem; deriving them from the actions is not formalised.

- `AeST.lean`: in the cold limit `c_ad² → 0` the pair `(χ, E)` obeys
  `χ̇ = Q E`, `K_B (Ė + H E) = [K′ - (2 - K_B)(H + Q)] χ`.
  - `eliminate_E`: for constant `Q`, `χ̈ + H χ̇ = (Q M / K_B) χ`. A time-dependent `Q` adds a
    term `(Q̇/Q) χ̇`.
  - `coefficient_with_Q`, `coefficient_le`: keeping the `Q` terms, the coefficient is
    `3H² f_eff / K_B` with `f_eff = f_c - (2 - K_B) q (1 + q)/3`, `q = Q/H`; for `Q ≥ 0`,
    `H > 0`, `0 < K_B < 2` it is at most the `H ≫ Q` value `3H² f_c / K_B`.
  - `power_law_solves`: on Einstein-de Sitter, `χ = aⁿ` with
    `n = ¼ + ¾ √(1/9 + 16 f_c/(3 K_B))` is an exact solution of the reduced equation.
  - `overgrowth_iff`: for `K_B > 0`, `n > 1` if and only if `f_c > K_B/6`.
    `overgrowth_window_iff`: `n > 1` for every `K_B ∈ (0, 2)` if and only if `f_c ≥ 1/3`.
    `overgrowth_fc_one`, `overgrowth_fc_one_sharp`: at `f_c = 1`, `n > 3/2` on the whole
    window and `3/2` is the infimum.
  - `q0_floor`: `a_crit < 1` if and only if `Q₀ > H₀ √(3 Ω_c/(2 - K_B))`.
- `Comparison.lean`, `AeSTBound.lean`: `growth_lower_bound`, `growth_upper_bound` compare a
  solution of `χ_ss - χ_s/3 = D(s) χ` (`s = ln t`) with the closed form on a finite interval,
  and `aest_growth_le` shows that on Einstein-de Sitter, with the full coefficient, constant
  `Q₀ ≥ 0` and `0 < K_B < 2`, a positive mode that enters no steeper than `aⁿ` stays below
  `χ₀ (a/a₀)ⁿ`. Positivity of the mode on the interval is a hypothesis.
- `A09.lean`: for a slaved dark sector with `Δ = -αΥ - β k² Υ/G₄` and pressure from the local
  piece only, `depth_closed_form` and `depth_limit` give the saturation depth
  `c_s² k²/a² → c α G₄/(β a²)`; `khronon_ksat_exact` and `khronon_ksat_floor` show that for a
  quadratic Khronon background the saturation scale is `k_sat = μ a Q̄` (equal to `μ a` only as
  `Q̄ → 1`), with a floor `k_sat ≥ (3/2) μ a*`.
- `A04.lean`, `A11.lean`, `B01.lean`: small algebraic results. `rC_cubed_cancel` shows the
  `β₀` dependence cancels from an oscillation-radius ceiling (the dictionary between the
  variables is a hypothesis); `gD_sq_general` gives the factor `(d-3)/((d-2)(d-1))` in
  `g_D² = a_M g_B` with `a_M = a₀/6` at `d = 4`; `bridge_obstruction` shows that a single
  kinetic function `P(X)` with a healthy state at `X* > 0` has `P_X < 0` on every continuous
  route to some `X < X*`.
- `PPN.lean`: algebra for the Einstein-aether reading of AeST's vector term
  (`α₁ = -4 K_B`), and a conditional bound that depends on a stated physical hypothesis
  (`H1`). Separate linear-order computations outside Lean find `α₁ = α₂ = 0` on AeST's
  `ω ≠ 0` branch at linear order, so this conditional should not be read as a constraint on AeST.

## What is not claimed

- That nature satisfies the premises. The Clausius relation on every local horizon (1995) and
  stationarity of the entanglement of every small ball (2016) are hypotheses of the theorems.
  The Lean results say what follows from them.
- The thermal-state step of the Unruh effect. `unruh_temperature` proves that a conical
  singularity is avoided exactly when imaginary time has period `2π/κ`; that the vacuum is
  thermal with `β = ħ/(k_B T)` (the KMS condition) is a hypothesis.
- The passage from finite-dimensional quantum systems to quantum field theory, including the
  fact that the vacuum modular Hamiltonian of a ball is the conformal boost generator
  (Casini-Huerta-Myers). The weight is taken as an input in `Ball2016`.
- The third-order Taylor remainder of the metric in normal coordinates. It is assumed to be
  higher order. The ball-volume theorems use the matching expansion, and the link between
  `RNC`/`NormalCoords` and `BallVolume` is by reading, not composed in Lean.
- The non-conformal scalar `δX` of the 2016 argument. Lean shows only that, if it is a
  `u`-independent scalar, it is absorbed into `λ` and `Λ`. Whether it is one for a given
  non-conformal field, and how it depends on the state and the ball size, is not addressed.
- That the premises are weaker than the conclusion. They are not: both the 1995 and 2016
  premises are pointwise equivalent to `Ric(k,k) = 8πG T(k,k)` on null `k`
  (`einstein_to_clausius_geom`, `ball_iff_null`), and on flat space no premise can be weaker
  (`flat_sector_necessity`). The theorems turn a thermodynamic statement into Einstein's
  equation and back; whether nature's horizons and balls obey that statement for independent
  reasons is physics, not something Lean settles.
- Any derivation of the AeST or Khronon perturbation equations from their actions, or any
  statement about the nonlinear regime.
- Global geometry. The curved results are on `ℝⁿ⁺¹` with a single global frame.

### Remark on Jacobson 2016, eq. (24)

`eq24_sign` (`Equilibrium2016`) records what appears to be a sign slip in the arXiv version.
Eq. (24), `G + λg = κ(T + δX g)`, contracts in signature `-+++` to
`G(u,u) - λ = κ(T(u,u) - δX)`, whereas eq. (23) has `+δX`; the consistent tensor form is
`κ(T - δX g)`. The contraction is proved in Lean; that it is a slip is a reading of the paper.
It does not affect the result, since `δX` is an undetermined scalar absorbed into `λ`.

## Axiom audit

`AxiomAudit.lean` runs `#print axioms` on the headline theorems. Its output, in
`axiom_audit.txt`, lists only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) for every one of them. The sources contain no `sorry`, no `axiom` declaration and
no `native_decide`. Reproduce with

```text
lake env lean AxiomAudit.lean
```

## Building

```text
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

`lake exe cache get` downloads the prebuilt Mathlib so only this project is compiled.

## References

- T. Jacobson, *Thermodynamics of Spacetime: The Einstein Equation of State*, Phys. Rev. Lett.
  75, 1260 (1995), [arXiv:gr-qc/9504004](https://arxiv.org/abs/gr-qc/9504004).
- T. Jacobson, *Entanglement Equilibrium and the Einstein Equation*, Phys. Rev. Lett. 116,
  201101 (2016), [arXiv:1505.04753](https://arxiv.org/abs/1505.04753).
- C. Skordis and T. Złośnik, *A new relativistic theory for Modified Newtonian Dynamics*,
  Phys. Rev. Lett. 127, 161302 (2021), [arXiv:2007.00082](https://arxiv.org/abs/2007.00082).
- L. Blanchet and C. Skordis, *Relativistic Khronon Theory in agreement with Modified Newtonian
  Dynamics and Large-Scale Cosmology*, JCAP 11 (2024) 040,
  [arXiv:2404.06584](https://arxiv.org/abs/2404.06584).

The Jacobson 1995 chain has also been formalised independently in the QIQT-H project
(github.com/kaplan196883/QIQT-H), including a four-dimensional curved chain with a coordinate
Levi-Civita connection (`jacobson_einstein_from_clausius_integral`), a contracted Bianchi
identity it describes as proved, and a focusing theorem at stationary horizons. This
repository was written independently of it; what differs here is that the chain is in every
dimension, needs no regularity hypothesis on the scalar, and derives Raychaudhuri for an
arbitrary vector field.

## License

Apache-2.0, see [LICENSE](LICENSE).
