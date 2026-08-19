/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# `π ^ 2` is irrational

The main result of this file is `irrational_pi_sq`, Niven's theorem that `π ^ 2` is irrational.
Mathlib knows `irrational_pi`, but that is strictly weaker: irrationality of `π ^ 2` implies
irrationality of `π`, not conversely.

The proof is Niven's, as presented in
<https://mathscholar.org/2025/02/simple-proofs-pi-is-transcendental/>.

* Put `I n = ∫ x in 0..1, (x - x ^ 2) ^ n * sin (π * x)`.
* Integrating by parts twice turns `π ^ 2 * I (n + 2)` into a combination of `I (n + 1)` and
  `I n` with integer coefficients (`I_rec`).
* Assume `π ^ 2 = a / b` with `a b : ℤ` and `0 < b`. The recursion then says that the integers
  `A n` given by `A 0 = 2`, `A 1 = 4 * b` and
  `A (n + 2) = 2 * (2 * n + 3) * b * A (n + 1) - a * b * A n` satisfy
  `A n * n ! = b ^ n * π ^ (2 * n + 1) * I n` (`A_eq`). This is Niven's assertion that
  `π * ∫ x in 0..1, a ^ n * x ^ n * (1 - x) ^ n / n ! * sin (π * x)` is an integer; there it is
  read off from the auxiliary function
  `g = b ^ n * ∑ k, (-1) ^ k * π ^ (2 * n - 2 * k) * f ^ (2 * k)`, whose telescoping property is
  exactly the recursion used here.
* The integrand of `I n` is positive on `(0, 1)`, so each `A n` is a positive integer, whence
  `1 ≤ A n` (`one_le_A`).
* On `[0, 1]` one has `0 ≤ x - x ^ 2 ≤ 1 / 4` and `sin (π * x) ≤ 1`, so `I n ≤ (1 / 4) ^ n` and
  therefore `A n ≤ π * (a / 4) ^ n / n !` (`A_le`), which tends to `0`. Contradiction.
-/

@[expose] public section

open Filter intervalIntegral MeasureTheory Real Set
open scoped Nat Topology

noncomputable section

/-- The sequence of integrals used for Niven's proof of the irrationality of `π ^ 2`. -/
private def I (n : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, (x - x ^ 2) ^ n * sin (π * x)

private lemma hasDerivAt_pi_mul (x : ℝ) : HasDerivAt (fun y : ℝ => π * y) π x :=
  ((hasDerivAt_id x).const_mul π).congr_deriv (mul_one π)

/-- Integrating by parts twice: if `u` vanishes at both endpoints of `[0, 1]`, then
`∫ u'' * sin (π * x) = -π ^ 2 * ∫ u * sin (π * x)`. -/
private lemma integral_deriv_two_mul_sin {u u' u'' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hc : Continuous u'') (h0 : u 0 = 0) (h1 : u 1 = 0) :
    ∫ x in (0 : ℝ)..1, u'' x * sin (π * x) = -π ^ 2 * ∫ x in (0 : ℝ)..1, u x * sin (π * x) := by
  have hi1 : IntervalIntegrable (fun x => u'' x * sin (π * x)) volume 0 1 :=
    (hc.mul (by fun_prop)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => π ^ 2 * (u x * sin (π * x))) volume 0 1 :=
    (continuous_const.mul ((continuous_iff_continuousAt.2 fun x => (hu x).continuousAt).mul
      (by fun_prop))).intervalIntegrable _ _
  have hF : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => u' y * sin (π * y) - π * (u y * cos (π * y)))
        (u'' x * sin (π * x) + π ^ 2 * (u x * sin (π * x))) x := fun x _ =>
    (((hu' x).mul (hasDerivAt_pi_mul x).sin).sub
      (((hu x).mul (hasDerivAt_pi_mul x).cos).const_mul π)).congr_deriv (by ring)
  have key : (∫ x in (0 : ℝ)..1, u'' x * sin (π * x)) +
      π ^ 2 * ∫ x in (0 : ℝ)..1, u x * sin (π * x) = 0 := by
    rw [← intervalIntegral.integral_const_mul, ← integral_add hi1 hi2,
      integral_eq_sub_of_hasDerivAt hF (hi1.add hi2)]
    simp [h0, h1]
  linarith

private lemma I_zero : I 0 = 2 / π := by
  have hπ : π ≠ 0 := pi_ne_zero
  have h : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => -(cos (π * y) / π)) (sin (π * x)) x := fun x _ =>
    (((hasDerivAt_pi_mul x).cos.div_const π).neg).congr_deriv (by field_simp)
  simp only [I, pow_zero, one_mul]
  rw [integral_eq_sub_of_hasDerivAt h ((by fun_prop :
    Continuous fun x : ℝ => sin (π * x)).intervalIntegrable _ _)]
  simp only [mul_one, mul_zero, cos_pi, cos_zero]
  ring

private lemma hasDerivAt_sub_sq (x : ℝ) : HasDerivAt (fun y : ℝ => y - y ^ 2) (1 - 2 * x) x :=
  ((hasDerivAt_id x).sub (hasDerivAt_pow 2 x)).congr_deriv (by norm_num)

private lemma hasDerivAt_sub_sq_pow (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - y ^ 2) ^ (m + 1))
      (((m : ℝ) + 1) * (x - x ^ 2) ^ m * (1 - 2 * x)) x :=
  ((hasDerivAt_sub_sq x).pow (m + 1)).congr_deriv (by push_cast; ring)

private lemma hasDerivAt_one_sub_two_mul (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2 : ℝ) x :=
  (((hasDerivAt_id x).const_mul (2 : ℝ)).const_sub 1).congr_deriv (by norm_num)

private lemma I_one : π ^ 2 * I 1 = 2 * I 0 := by
  have h := integral_deriv_two_mul_sin (u' := fun y => 1 - 2 * y) hasDerivAt_sub_sq
    hasDerivAt_one_sub_two_mul (by fun_prop) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_const_mul] at h
  simp only [I, pow_zero, pow_one, one_mul]
  linarith

private lemma I_rec (n : ℕ) :
    π ^ 2 * I (n + 2) =
      2 * (n + 2) * (2 * n + 3) * I (n + 1) - (n + 2) * (n + 1) * I n := by
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y - y ^ 2) ^ (n + 2))
      (((n : ℝ) + 2) * ((x - x ^ 2) ^ (n + 1) * (1 - 2 * x))) x := fun x =>
    (hasDerivAt_sub_sq_pow (n + 1) x).congr_deriv (by push_cast; ring)
  have hu' : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => ((n : ℝ) + 2) * ((y - y ^ 2) ^ (n + 1) * (1 - 2 * y)))
      (((n : ℝ) + 2) * ((n : ℝ) + 1) * (x - x ^ 2) ^ n -
        2 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 3) * (x - x ^ 2) ^ (n + 1)) x := fun x =>
    (((hasDerivAt_sub_sq_pow n x).mul (hasDerivAt_one_sub_two_mul x)).const_mul
      ((n : ℝ) + 2)).congr_deriv (by ring)
  have h := integral_deriv_two_mul_sin hu hu' (by fun_prop) (by norm_num) (by norm_num)
  have e : ∀ x : ℝ, (((n : ℝ) + 2) * ((n : ℝ) + 1) * (x - x ^ 2) ^ n -
      2 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 3) * (x - x ^ 2) ^ (n + 1)) * sin (π * x) =
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((x - x ^ 2) ^ n * sin (π * x)) -
      (2 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 3)) * ((x - x ^ 2) ^ (n + 1) * sin (π * x)) :=
    fun x => by ring
  simp only [e] at h
  rw [integral_sub ((by fun_prop : Continuous fun x : ℝ =>
        (((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((x - x ^ 2) ^ n * sin (π * x))).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ =>
        (2 * ((n : ℝ) + 2) * (2 * (n : ℝ) + 3)) *
          ((x - x ^ 2) ^ (n + 1) * sin (π * x))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  simp only [I]
  linarith

private lemma I_pos (n : ℕ) : 0 < I n := by
  refine intervalIntegral_pos_of_pos_on ((by fun_prop : Continuous fun x : ℝ =>
    (x - x ^ 2) ^ n * sin (π * x)).intervalIntegrable _ _) (fun x hx => ?_) one_pos
  obtain ⟨hx0, hx1⟩ := hx
  exact mul_pos (pow_pos (by nlinarith) n)
    (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos]))

private lemma I_le (n : ℕ) : I n ≤ (1 / 4 : ℝ) ^ n := by
  have h : I n ≤ ∫ _x in (0 : ℝ)..1, (1 / 4 : ℝ) ^ n := by
    refine integral_mono_on zero_le_one ((by fun_prop : Continuous fun x : ℝ =>
      (x - x ^ 2) ^ n * sin (π * x)).intervalIntegrable _ _)
      intervalIntegrable_const fun x hx => ?_
    obtain ⟨hx0, hx1⟩ := hx
    have hb : (0 : ℝ) ≤ x - x ^ 2 := by nlinarith
    have hb' : x - x ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    calc (x - x ^ 2) ^ n * sin (π * x) ≤ (x - x ^ 2) ^ n * 1 :=
          mul_le_mul_of_nonneg_left (sin_le_one _) (pow_nonneg hb n)
      _ ≤ (1 / 4 : ℝ) ^ n := by rw [mul_one]; exact pow_le_pow_left₀ hb hb' n
  simpa using h

/-- The integer sequence produced by the recursion `I_rec` under the assumption `π ^ 2 = a / b`. -/
private def A (a b : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => 4 * b
  | n + 2 => 2 * (2 * (n : ℤ) + 3) * b * A a b (n + 1) - a * b * A a b n

private lemma A_eq {a b : ℤ} (hab : (a : ℝ) = b * π ^ 2) (n : ℕ) :
    (A a b n : ℝ) * n ! = (b : ℝ) ^ n * π ^ (2 * n + 1) * I n := by
  have hπ : π ≠ 0 := pi_ne_zero
  induction n using Nat.twoStepInduction with
  | zero => simp [A, I_zero, mul_div_cancel₀ _ hπ]
  | one =>
    have h := I_one
    rw [I_zero] at h
    have h4 : π ^ 3 * I 1 = 4 := by
      rw [show π ^ 3 * I 1 = π * (π ^ 2 * I 1) by ring, h]
      field_simp
      norm_num
    simp only [A, Nat.factorial_one, Nat.cast_one, mul_one, pow_one]
    push_cast
    linear_combination -(b : ℝ) * h4
  | more n ih0 ih1 =>
    have hrec := I_rec n
    have hfac : ((n + 2)! : ℝ) = ((n : ℝ) + 2) * (((n : ℝ) + 1) * n !) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have hfac1 : ((n + 1)! : ℝ) = ((n : ℝ) + 1) * n ! := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac1, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, pow_add] at ih1
    simp only [A]
    rw [hfac, show 2 * (n + 2) + 1 = 2 * n + 1 + 4 by ring, pow_add]
    push_cast
    linear_combination (2 * (2 * (n : ℝ) + 3) * (b : ℝ) * ((n : ℝ) + 2)) * ih1
      - ((a : ℝ) * (b : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) + 1)) * ih0
      - ((b : ℝ) ^ (n + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 1) * π ^ (2 * n + 1) * I n) * hab
      - ((b : ℝ) ^ (n + 2) * π ^ (2 * n + 1) * π ^ 2) * hrec

private lemma one_le_A {a b : ℤ} (hb : (0 : ℝ) < b) (hab : (a : ℝ) = b * π ^ 2) (n : ℕ) :
    (1 : ℝ) ≤ (A a b n : ℝ) := by
  have hfac : (0 : ℝ) < n ! := Nat.cast_pos.mpr n.factorial_pos
  have h1 : (0 : ℝ) < (A a b n : ℝ) * n ! := by
    rw [A_eq hab n]
    exact mul_pos (mul_pos (pow_pos hb n) (pow_pos pi_pos _)) (I_pos n)
  have h2 : (0 : ℤ) < A a b n := (Int.cast_pos (R := ℝ)).mp (by nlinarith)
  exact_mod_cast (by lia : (1 : ℤ) ≤ A a b n)

private lemma A_le {a b : ℤ} (hb : (0 : ℝ) < b) (hab : (a : ℝ) = b * π ^ 2) (n : ℕ) :
    (A a b n : ℝ) ≤ π * ((a : ℝ) / 4) ^ n / n ! := by
  rw [le_div_iff₀ (Nat.cast_pos.mpr n.factorial_pos), A_eq hab n]
  calc (b : ℝ) ^ n * π ^ (2 * n + 1) * I n
      ≤ (b : ℝ) ^ n * π ^ (2 * n + 1) * (1 / 4 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left (I_le n) (by positivity)
    _ = π * ((a : ℝ) / 4) ^ n := by rw [hab]; ring

end

/-- **Niven's theorem**: `π ^ 2` is irrational. -/
theorem irrational_pi_sq : Irrational (π ^ 2) := by
  rintro ⟨q, hq⟩
  obtain ⟨a, b, hb, hab⟩ : ∃ a b : ℤ, 0 < b ∧ π ^ 2 = a / b :=
    ⟨q.num, q.den, mod_cast q.pos, by rw [← hq, Rat.cast_def]; push_cast; ring⟩
  have hb' : (0 : ℝ) < b := mod_cast hb
  have hab' : (a : ℝ) = (b : ℝ) * π ^ 2 := by rw [hab]; field_simp
  have hlim : Tendsto (fun n : ℕ => π * ((a : ℝ) / 4) ^ n / n !) atTop (𝓝 0) := by
    simpa [mul_div_assoc] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop ((a : ℝ) / 4)).const_mul π
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const one_pos).exists
  exact absurd (one_le_A hb' hab' n) (not_le.2 ((A_le hb' hab' n).trans_lt hn))
