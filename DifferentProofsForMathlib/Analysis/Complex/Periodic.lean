/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Calculus of the `q`-parameter

The parameter `q = qParam h z = exp (2πiz / h)` is `h`-periodic, and its derivative is
`(2πi / h) q`. These are intended for `Mathlib/Analysis/Complex/Periodic.lean`.
-/

@[expose] public section

open Complex
open scoped Real

namespace Function.Periodic

/-- The `q`-parameter `exp (2πiz / h)` is `h`-periodic. -/
theorem qParam_add_self (h : ℝ) (z : ℂ) : qParam h (z + h) = qParam h z := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [qParam, ofReal_zero, add_zero, div_zero, exp_zero]
  · rw [qParam, qParam, mul_add, add_div, exp_add, mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr hh),
      exp_two_pi_mul_I, mul_one]

/-- The derivative of the `q`-parameter: `d/dz exp (2πiz / h) = (2πi / h) exp (2πiz / h)`. -/
theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (qParam h) (2 * π * I / h * qParam h z) z := by
  have hq : qParam h = fun x ↦ cexp (2 * π * I / h * x) := by
    ext x
    rw [qParam, mul_div_right_comm]
  rw [hq]
  simpa only [mul_comm, id_eq, one_mul] using ((hasDerivAt_id z).const_mul (2 * π * I / h)).cexp

end Function.Periodic
