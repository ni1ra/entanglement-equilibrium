/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  The 2016 analogue of `Certificate`: how many rest frames must the equilibrium condition be
  checked in? Symmetric forms have dimension `(n+1)(n+2)/2`; the unit timelike vectors `e₀`,
  `(5/4)e₀ ± (3/4)eᵢ` and `3e₀ + 2eᵢ + 2eⱼ` (`0 < i < j`) are exactly that many and force
  `X = 0`, and no smaller family can. In four dimensions: 10 rest frames, one more than the 9
  light rays of 1995. The difference is one dimension, the multiples of `η` that null
  vectors cannot detect (dimension counting; the physical reading in terms of `Λ` is a gloss).
-/
import EntEq.Certificate

open Matrix Module

namespace EntEq

variable {n : ℕ}

/-- **Sufficiency.** A symmetric `X` vanishing on the `(n+1)(n+2)/2` unit timelike vectors of
the certificate is zero. -/
theorem timelike_certificate (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hX : X.IsSymm)
    (h0 : qf X ((1:ℝ) • e 0 + (0:ℝ) • e 0 + (0:ℝ) • e 0) = 0)
    (hpm : ∀ i : Fin (n+1), i ≠ 0 →
      qf X ((5/4:ℝ) • e 0 + (3/4:ℝ) • e i + (0:ℝ) • e i) = 0 ∧
      qf X ((5/4:ℝ) • e 0 + (-3/4:ℝ) • e i + (0:ℝ) • e i) = 0)
    (hpy : ∀ i j : Fin (n+1), i ≠ 0 → i < j → qf X ((3:ℝ) • e 0 + (2:ℝ) • e i + (2:ℝ) • e j) = 0) :
    X = 0 := by
  have hs : ∀ i j, X j i = X i j := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hX i) j
  have h00 : X 0 0 = 0 := by rw [qf_three] at h0; linarith
  have step1 : ∀ i : Fin (n+1), i ≠ 0 → X 0 i = 0 ∧ X i i = 0 := by
    intro i hi
    obtain ⟨hp, hm⟩ := hpm i hi
    rw [qf_three, h00] at hp hm
    have := hs 0 i
    constructor <;> linarith
  have step2 : ∀ i j : Fin (n+1), i ≠ 0 → j ≠ 0 → i ≠ j → X i j = 0 := by
    intro i j hi hj hij
    have key : ∀ a b : Fin (n+1), a ≠ 0 → a < b → X a b = 0 := by
      intro a b ha hab
      have hb : b ≠ 0 := by
        intro h; rw [h] at hab; exact absurd hab (Fin.not_lt_zero a)
      have h := hpy a b ha hab
      rw [qf_three] at h
      have := hs 0 a; have := hs 0 b; have := hs a b
      have := step1 a ha; have := step1 b hb
      linarith
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j hi h
    · rw [hs]; exact key j i hj h
  ext a b
  simp only [Matrix.zero_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = 0
    · subst ha; exact h00
    · exact (step1 a ha).2
  · by_cases ha : a = 0
    · subst ha; exact (step1 b (Ne.symm hab)).1
    · by_cases hb : b = 0
      · subst hb; rw [hs]; exact (step1 a ha).1
      · exact step2 a b ha hb hab

/-- The timelike certificate's size: `1 + 2n + n(n−1)/2 = (n+2)(n+1)/2`. -/
theorem timelike_certificate_size : 1 + 2 * n + n.choose 2 = (n + 2).choose 2 := by
  have := certificate_size (n := n); omega

/-- **Minimality.** For any `m < (n+2)(n+1)/2` vectors some nonzero symmetric `X` vanishes on
all of them. -/
theorem timelike_certificate_minimal (m : ℕ) (k : Fin m → (Fin (n+1) → ℝ))
    (hm : m < (n + 2).choose 2) :
    ∃ X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, X.IsSymm ∧ (∀ r, qf X (k r) = 0) ∧ X ≠ 0 := by
  let L : (Sym2 (Fin (n+1)) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun a r => qf (symOf a) (k r)
      map_add' := fun a b => by
        ext r
        simp only [qf, Pi.add_apply]
        rw [show symOf (a + b) = symOf a + symOf b from rfl, Matrix.add_mulVec, dotProduct_add]
      map_smul' := fun c a => by
        ext r
        simp only [qf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [symOf_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] }
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hdom : finrank ℝ (Sym2 (Fin (n+1)) → ℝ) = (n + 2).choose 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin]
  have hrange : finrank ℝ (LinearMap.range L) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range L)
    simpa using this
  have hker : 0 < finrank ℝ (LinearMap.ker L) := by omega
  have hnb : LinearMap.ker L ≠ ⊥ := by
    intro hb; rw [hb, finrank_bot] at hker; exact absurd hker (lt_irrefl 0)
  obtain ⟨a, ha, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnb
  refine ⟨symOf a, symOf_isSymm a, fun r => congrFun (LinearMap.mem_ker.mp ha) r, ?_⟩
  intro h0
  apply hne
  apply symOf_injective
  rw [h0]; rfl

end EntEq
