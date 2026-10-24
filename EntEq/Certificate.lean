/-
Copyright (c) 2026 ni1ra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ni1ra
-/
/-
  How many light rays must Clausius be checked on? In `n + 1` dimensions the symmetric forms
  modulo the metric have dimension `(n+1)(n+2)/2 − 1 = (n² + 3n)/2`. The explicit certificate
  of `null_cone_lemma` (`e₀ ± eᵢ` and `5e₀ + 3eᵢ + 4eⱼ` for `i < j`) has exactly that many
  vectors, and `certificate_minimal` shows no smaller family of vectors (null or not) can
  force `X ∝ η`. In four dimensions: 9 light rays per point, and 9 is the minimum.
-/
import EntEq.NullCone
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

open Matrix Module

namespace EntEq

variable {n : ℕ}

/-- **Sufficiency of the certificate.** A symmetric `X` vanishing on the `(n² + 3n)/2` null
vectors `e₀ ± eᵢ` (`i ≠ 0`) and `5e₀ + 3eᵢ + 4eⱼ` (`0 < i < j`) is a multiple of `η`. -/
theorem null_cone_certificate (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hX : X.IsSymm)
    (hpm : ∀ i : Fin (n+1), i ≠ 0 →
      qf X ((1:ℝ) • e 0 + (1:ℝ) • e i + (0:ℝ) • e i) = 0 ∧
      qf X ((1:ℝ) • e 0 + (-1:ℝ) • e i + (0:ℝ) • e i) = 0)
    (hpy : ∀ i j : Fin (n+1), i ≠ 0 → i < j → qf X ((5:ℝ) • e 0 + (3:ℝ) • e i + (4:ℝ) • e j) = 0) :
    ∃ c : ℝ, X = c • eta n := by
  have hs : ∀ i j, X j i = X i j := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hX i) j
  have step1 : ∀ i : Fin (n+1), i ≠ 0 → X 0 i = 0 ∧ X i i = -X 0 0 := by
    intro i hi
    obtain ⟨hp, hm⟩ := hpm i hi
    rw [qf_three] at hp hm
    have := hs 0 i
    constructor <;> linarith
  have step2' : ∀ i j : Fin (n+1), i ≠ 0 → i < j → X i j = 0 := by
    intro i j hi hij
    have hj : j ≠ 0 := by
      intro h; rw [h] at hij; exact absurd hij (Fin.not_lt_zero i)
    have h := hpy i j hi hij
    rw [qf_three] at h
    have := hs 0 i; have := hs 0 j; have := hs i j
    have := step1 i hi; have := step1 j hj
    linarith
  have step2 : ∀ i j : Fin (n+1), i ≠ 0 → j ≠ 0 → i ≠ j → X i j = 0 := by
    intro i j hi hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact step2' i j hi h
    · rw [hs]; exact step2' j i hj h
  refine ⟨-X 0 0, ?_⟩
  ext a b
  simp only [Matrix.smul_apply, eta_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = 0
    · subst ha; simp
    · simp [ha, (step1 a ha).2]
  · simp only [hab, ite_false, mul_zero]
    by_cases ha : a = 0
    · subst ha; exact (step1 b (Ne.symm hab)).1
    · by_cases hb : b = 0
      · subst hb; rw [hs]; exact (step1 a ha).1
      · exact step2 a b ha hb hab

/-- The certificate's size: `2n + n(n−1)/2 = (n+2)(n+1)/2 − 1`. -/
theorem certificate_size : 2 * n + n.choose 2 + 1 = (n + 2).choose 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : (k + 1 + 2).choose 2 = (k + 2) + (k + 2).choose 2 := by
      rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.choose_succ_succ, Nat.choose_one_right]
    have h2 : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

/-- Symmetric matrix with coefficients indexed by unordered pairs. -/
def symOf (a : Sym2 (Fin (n+1)) → ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => a s(i, j)

lemma symOf_isSymm (a : Sym2 (Fin (n+1)) → ℝ) : (symOf a).IsSymm := by
  ext i j; simp [symOf, Matrix.transpose_apply, Sym2.eq_swap]

lemma symOf_injective : Function.Injective (symOf (n := n)) := by
  intro a b h
  funext z
  induction z using Sym2.ind with
  | h i j => exact congrFun (congrFun h i) j

lemma symOf_smul (c : ℝ) (a : Sym2 (Fin (n+1)) → ℝ) : symOf (c • a) = c • symOf a := rfl

/-- Coefficients of `η`. -/
def aEta : Sym2 (Fin (n+1)) → ℝ :=
  Sym2.lift ⟨fun i j => eta n i j, fun i j => by
    simp only [eta_apply, eq_comm]; split_ifs <;> simp_all⟩

lemma symOf_aEta : symOf (aEta (n := n)) = eta n := by
  ext i j; simp [symOf, aEta]

/-- **Minimality.** For any `m` vectors with `m + 2 ≤ (n+2)(n+1)/2`, i.e. fewer than the
certificate's `(n+2)(n+1)/2 − 1`, some symmetric `X` vanishes on all of them and is not a
multiple of `η`. Fewer light rays cannot pin down the Einstein equation. -/
theorem certificate_minimal (m : ℕ) (k : Fin m → (Fin (n+1) → ℝ))
    (hm : m + 2 ≤ (n + 2).choose 2) :
    ∃ X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, X.IsSymm ∧ (∀ r, qf X (k r) = 0) ∧
      ∀ c : ℝ, X ≠ c • eta n := by
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
  by_contra hcon
  push Not at hcon
  have hsub : LinearMap.ker L ≤ Submodule.span ℝ {aEta (n := n)} := by
    intro a ha
    have hz : ∀ r, qf (symOf a) (k r) = 0 := fun r => congrFun (LinearMap.mem_ker.mp ha) r
    obtain ⟨c, hc⟩ : ∃ c : ℝ, symOf a = c • eta n := by
      by_contra h'
      push Not at h'
      obtain ⟨c, hc⟩ := hcon (symOf a) (symOf_isSymm a) hz
      exact h' c hc
    rw [Submodule.mem_span_singleton]
    refine ⟨c, symOf_injective ?_⟩
    rw [symOf_smul, symOf_aEta, hc]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hdom : finrank ℝ (Sym2 (Fin (n+1)) → ℝ) = (n + 2).choose 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin]
  have hrange : finrank ℝ (LinearMap.range L) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range L)
    simpa using this
  have hspan : finrank ℝ (Submodule.span ℝ {aEta (n := n)}) ≤ 1 := by
    have := finrank_span_le_card (R := ℝ) ({aEta (n := n)} : Set (Sym2 (Fin (n+1)) → ℝ))
    simpa using this
  have hmono := Submodule.finrank_mono hsub
  omega

end EntEq
