module

public import DifferentProofs.IntegerRectangle.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The integer-rectangle theorem via a complex double integral

This is de Bruijn's original method, the first of Wagon's fourteen proofs. To a rectangle
`T = [a, b] × [c, d]` attach

```
∫∫_T e^{2πi(x+y)} dx dy = (∫_a^b e^{2πix} dx) · (∫_c^d e^{2πiy} dy).
```

The one-dimensional integral `∫_a^b e^{2πix} dx = (e^{2πib} - e^{2πia}) / (2πi)` vanishes **iff**
`b - a` is an integer, so the double integral over `T` vanishes iff `T` has an integer side. The
integral is additive over the tiling (`IsTiling.setIntegral_eq_sum`), so if every tile has an
integer side the double integral over the ambient rectangle `R` vanishes, forcing `R` to have an
integer side. The complex exponential is what makes the vanishing criterion an exact "integer
side" statement, with no reflected solutions — this is why the complex proof is the cleanest.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace IntegerRectangle.ComplexIntegral

/-- The oscillatory integrand `t ↦ e^{2πit}` in one variable. -/
private noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

private lemma continuous_e : Continuous e := by
  unfold e; fun_prop

private lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- **The key one-dimensional criterion.** The integral of `e^{2πix}` over `[a, b]` vanishes iff
`b - a` is an integer. -/
private lemma integral_Icc_e_eq_zero_iff {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Icc a b, e x) = 0 ↔ ∃ n : ℤ, b - a = n := by
  have hconv : (∫ x in Icc a b, e x) =
      (Complex.exp (2 * Real.pi * Complex.I * b) - Complex.exp (2 * Real.pi * Complex.I * a)) /
        (2 * Real.pi * Complex.I) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact integral_exp_mul_complex two_pi_I_ne_zero
  rw [hconv, div_eq_zero_iff, or_iff_left two_pi_I_ne_zero, sub_eq_zero,
    Complex.exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  constructor
  · intro hn
    have key : (2 * (Real.pi : ℂ) * Complex.I) * ((b : ℂ) - a) =
        (2 * (Real.pi : ℂ) * Complex.I) * n := by linear_combination hn
    exact_mod_cast mul_left_cancel₀ two_pi_I_ne_zero key
  · intro hn
    have : ((b : ℂ) - a) = n := by exact_mod_cast hn
    linear_combination (2 * (Real.pi : ℂ) * Complex.I) * this

/-- **Complex double-integral proof** (de Bruijn) of the integer-rectangle tiling theorem. -/
theorem IntegerRectangleTheorem_ComplexIntegral : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  -- The product integrand `e(z.1) · e(z.2)` is continuous, hence integrable over `R`.
  have hint : IntegrableOn (fun z : ℝ × ℝ => e z.1 * e z.2) R.toSet volume :=
    R.integrableOn_of_continuous
      ((continuous_e.comp continuous_fst).mul (continuous_e.comp continuous_snd))
  -- Each tile has an integer side, so one of its coordinate integrals vanishes.
  have htile : ∀ i, (∫ x in Icc (T i).x₀ (T i).x₁, e x) = 0 ∨
      (∫ y in Icc (T i).y₀ (T i).y₁, e y) = 0 := by
    intro i
    rcases hsides i with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact Or.inl ((integral_Icc_e_eq_zero_iff (T i).hx).mpr ⟨n, hn⟩)
    · exact Or.inr ((integral_Icc_e_eq_zero_iff (T i).hy).mpr ⟨n, hn⟩)
  -- Additivity propagates the dichotomy to `R`; the criterion then gives an integer side.
  rcases hT.prod_integral_dichotomy hint htile with hx | hy
  · exact Or.inl ((integral_Icc_e_eq_zero_iff R.hx).mp hx)
  · exact Or.inr ((integral_Icc_e_eq_zero_iff R.hy).mp hy)

end IntegerRectangle.ComplexIntegral
