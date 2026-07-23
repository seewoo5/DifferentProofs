module

public import DifferentProofs.IntegerRectangle.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The integer-rectangle theorem via a real double integral

Wagon's second proof specializes the complex-integral proof to a real integrand. Placing the
ambient rectangle `R` in standard position (lower-left corner at the origin), one integrates
`sin(2πx) sin(2πy)`; the integral over each tile vanishes, so the integral over `R` vanishes, and
because `R` has a corner at the origin this forces an integer side.

Rather than translate the whole tiling, we translate the *integrand*: we integrate
`sin(2π(x - R.x₀)) sin(2π(y - R.y₀))`, which is the same as placing the origin at `R`'s corner.
The one-dimensional integral of `sin(2π(x - s))` over `[a, b]` is
`(cos(2π(a - s)) - cos(2π(b - s))) / (2π)`. This vanishes whenever `b - a ∈ ℤ` (used for the tiles,
where the shift `s` is irrelevant), and — crucially at the corner, where the lower limit `a` equals
the shift `s` — it vanishes **iff** `b - s ∈ ℤ` (used for `R`, giving an integer side).
-/

@[expose] public section

open MeasureTheory Set Real

namespace IntegerRectangle.RealIntegral

/-- The origin-shifted sine `x ↦ sin(2π(x - s))`; taking `s` to be a corner coordinate of the
ambient rectangle plays the role of putting that rectangle in standard position. -/
private noncomputable def sinShift (s x : ℝ) : ℝ := sin (2 * π * (x - s))

private lemma continuous_sinShift (s : ℝ) : Continuous (sinShift s) :=
  continuous_sin.comp <| (continuous_sub_right s).const_mul (2 * π)

/-- The one-dimensional integral of the shifted sine over `[a, b]`. -/
private lemma integral_Icc_sinShift {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (∫ x in Icc a b, sinShift s x) =
      (cos (2 * π * (a - s)) - cos (2 * π * (b - s))) / (2 * π) := by
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, sinShift]
  rw [intervalIntegral.integral_comp_sub_right (fun x ↦ sin (2 * π * x)) s,
    intervalIntegral.integral_comp_mul_left sin two_pi_pos.ne', integral_sin, smul_eq_mul,
    inv_mul_eq_div]

/-- Over a tile the shift is immaterial: an integer side-length kills the integral. -/
private lemma integral_Icc_sinShift_eq_zero_of_int {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (h : ∃ n : ℤ, b - a = n) : (∫ x in Icc a b, sinShift s x) = 0 := by
  obtain ⟨n, hn⟩ := h
  have hshift : 2 * π * (b - s) = 2 * π * (a - s) + n * (2 * π) := by linear_combination 2 * π * hn
  rw [integral_Icc_sinShift hab, hshift, cos_add_int_mul_two_pi, sub_self, zero_div]

/-- At the corner (lower limit equal to the shift) the integral vanishes **iff** the length is an
integer. This is where the standard-position hypothesis of Wagon's proof is used. -/
private lemma integral_Icc_sinShift_self_eq_zero_iff {b s : ℝ} (hsb : s ≤ b) :
    (∫ x in Icc s b, sinShift s x) = 0 ↔ ∃ n : ℤ, b - s = n := by
  rw [integral_Icc_sinShift hsb, sub_self, mul_zero, cos_zero, div_eq_zero_iff,
    or_iff_left two_pi_pos.ne', sub_eq_zero, eq_comm, cos_eq_one_iff]
  exact exists_congr fun n ↦ by
    rw [mul_comm (2 * π) (b - s), mul_left_inj' two_pi_pos.ne', eq_comm]

/-- **Real double-integral proof** of the integer-rectangle tiling theorem. -/
theorem IntegerRectangleTheorem_RealIntegral : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  have hint : IntegrableOn (fun z : ℝ × ℝ ↦ sinShift R.x₀ z.1 * sinShift R.y₀ z.2) R.toSet volume :=
    R.integrableOn_of_continuous
      ((continuous_sinShift R.x₀).fst'.mul (continuous_sinShift R.y₀).snd')
  have htile := fun i ↦ Or.imp (integral_Icc_sinShift_eq_zero_of_int (T i).hx R.x₀)
    (integral_Icc_sinShift_eq_zero_of_int (T i).hy R.y₀) (hsides i)
  exact (hT.prod_integral_dichotomy hint htile).imp
    (integral_Icc_sinShift_self_eq_zero_iff R.hx).mp
    (integral_Icc_sinShift_self_eq_zero_iff R.hy).mp

end IntegerRectangle.RealIntegral
