module

public import DifferentProofs.BaselProblem.Defs
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.PSeries

@[expose] public section

open Real Complex MeasureTheory intervalIntegral Set

namespace BaselProblem

private lemma neg_pi_lt_pi : (-π : ℝ) < π := neg_lt_self pi_pos

/-- A constant function has vanishing Fourier coefficients at nonzero frequencies. -/
private lemma fourierCoeffOn_one_eq_zero {a b : ℝ} (hab : a < b) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn hab (fun _ : ℝ ↦ (1 : ℂ)) n = 0 := by
  rw [fourierCoeffOn_of_hasDerivAt hab hn (f' := fun _ ↦ 0)
      (fun x _ ↦ hasDerivAt_const x 1) intervalIntegrable_const,
    sub_self, mul_zero, zero_sub, fourierCoeffOn_eq_integral]
  simp

/-- The `n`-th Fourier coefficient of `x ↦ x` on `[-π, π]` has squared norm `1 / n²`.
At `n = 0` both sides are `0` (using `1 / 0 = 0`). -/
private lemma coeff_norm_sq (n : ℤ) :
    ‖fourierCoeffOn neg_pi_lt_pi (fun x ↦ (x : ℂ)) n‖ ^ 2 = 1 / (n : ℝ) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : fourierCoeffOn neg_pi_lt_pi (fun x ↦ (x : ℂ)) 0 = 0 := by
      rw [fourierCoeffOn_eq_integral]
      simp only [neg_zero, fourier_zero, one_smul]
      rw [intervalIntegral.integral_ofReal, integral_id]
      norm_num
    simp [h0]
  · rw [fourierCoeffOn_of_hasDerivAt neg_pi_lt_pi hn (f' := fun _ ↦ 1)
        (fun x _ ↦ by simpa using (hasDerivAt_id x).ofReal_comp) intervalIntegrable_const,
      fourierCoeffOn_one_eq_zero neg_pi_lt_pi hn,
      mul_zero, sub_zero, norm_mul, norm_mul]
    have hf : ∀ x : AddCircle (π - -π), ‖fourier (-n) x‖ = 1 := fun x ↦ Circle.norm_coe _
    simp only [hf, one_mul]
    rw [show ((π : ℂ) - ((-π : ℝ) : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    have hd : ‖(-2 * (π : ℂ) * I * (n : ℂ))‖ = 2 * π * |(n : ℝ)| := by
      simp [abs_of_pos pi_pos]
    rw [hd, show 1 / (2 * π * |(n : ℝ)|) * (2 * π) = 1 / |(n : ℝ)| by field_simp,
      div_pow, one_pow, sq_abs]

theorem BaselProblem_Parseval : BaselProblem := by
  have hL2 : MemLp (fun x : ℝ ↦ (x : ℂ)) 2 (volume.restrict (Ioc (-π) π)) := by
    refine MemLp.of_bound Complex.continuous_ofReal.aestronglyMeasurable π ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hint : ∫ x in (-π)..π, ‖(x : ℂ)‖ ^ 2 = 2 * π ^ 3 / 3 := by
    simp_rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [integral_pow]; ring
  have hsum : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 2) :=
    summable_one_div_nat_pow.mpr one_lt_two
  have hp := tsum_sq_fourierCoeffOn neg_pi_lt_pi hL2
  simp_rw [coeff_norm_sq] at hp
  rw [hint, smul_eq_mul] at hp
  have hconv : ∑' (i : ℤ), (1 : ℝ) / (i : ℝ) ^ 2 = 2 * ∑' (n : ℕ), (1 : ℝ) / (n : ℝ) ^ 2 := by
    rw [Summable.tsum_of_nat_of_neg (f := fun i : ℤ ↦ (1 : ℝ) / (i : ℝ) ^ 2)
        (hsum.congr fun n ↦ by push_cast; ring) (hsum.congr fun n ↦ by push_cast; ring)]
    push_cast
    simp only [neg_sq]
    rw [show (1 : ℝ) / (0 : ℝ) ^ 2 = 0 by norm_num]
    ring
  change ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = π ^ 2 / 6
  have h2S := hconv.symm.trans hp
  rw [show (π - -π)⁻¹ * (2 * π ^ 3 / 3) = π ^ 2 / 3 by field_simp; ring] at h2S
  linarith [h2S]

end BaselProblem
