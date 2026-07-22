module

public import DifferentProofs.IntegerRectangle.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

private lemma continuous_sinShift (s : ℝ) : Continuous (sinShift s) := by
  unfold sinShift; fun_prop

private lemma two_pi_ne_zero : (2 * π : ℝ) ≠ 0 := by positivity

/-- The one-dimensional integral of the shifted sine over `[a, b]`. -/
private lemma integral_Icc_sinShift {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (∫ x in Icc a b, sinShift s x) =
      (cos (2 * π * (a - s)) - cos (2 * π * (b - s))) / (2 * π) := by
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun x => -cos (2 * π * (x - s)) / (2 * π)) (sinShift s x) x := by
    intro x _
    unfold sinShift
    have h1 : HasDerivAt (fun x : ℝ => 2 * π * (x - s)) (2 * π) x := by
      simpa using ((hasDerivAt_id x).sub_const s).const_mul (2 * π)
    have h2 : HasDerivAt (fun x => cos (2 * π * (x - s))) (-sin (2 * π * (x - s)) * (2 * π)) x :=
      (Real.hasDerivAt_cos _).comp x h1
    convert (h2.neg).div_const (2 * π) using 1
    rw [eq_div_iff two_pi_ne_zero]; ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuous_sinShift s).intervalIntegrable a b)]
  ring

/-- Over a tile the shift is immaterial: an integer side-length kills the integral. -/
private lemma integral_Icc_sinShift_eq_zero_of_int {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (h : ∃ n : ℤ, b - a = n) : (∫ x in Icc a b, sinShift s x) = 0 := by
  obtain ⟨n, hn⟩ := h
  rw [integral_Icc_sinShift hab, div_eq_zero_iff]
  refine Or.inl ?_
  have hshift : 2 * π * (b - s) = 2 * π * (a - s) + n * (2 * π) := by
    linear_combination 2 * π * hn
  rw [hshift, cos_add_int_mul_two_pi, sub_self]

/-- At the corner (lower limit equal to the shift) the integral vanishes **iff** the length is an
integer. This is where the standard-position hypothesis of Wagon's proof is used. -/
private lemma integral_Icc_sinShift_self_eq_zero_iff {b s : ℝ} (hsb : s ≤ b) :
    (∫ x in Icc s b, sinShift s x) = 0 ↔ ∃ n : ℤ, b - s = n := by
  rw [integral_Icc_sinShift hsb, sub_self, mul_zero, Real.cos_zero, div_eq_zero_iff,
    or_iff_left two_pi_ne_zero, sub_eq_zero, eq_comm, Real.cos_eq_one_iff]
  refine exists_congr fun n => ?_
  constructor
  · intro hn
    have : (n : ℝ) * (2 * π) = (b - s) * (2 * π) := by rw [hn]; ring
    have := mul_right_cancel₀ two_pi_ne_zero this
    linarith
  · intro hn; rw [hn]; ring

/-- **Real double-integral proof** of the integer-rectangle tiling theorem. -/
theorem IntegerRectangleTheorem_RealIntegral : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  have hint : IntegrableOn
      (fun z : ℝ × ℝ => sinShift R.x₀ z.1 * sinShift R.y₀ z.2) R.toSet volume :=
    R.integrableOn_of_continuous
      ((continuous_sinShift R.x₀).fst'.mul (continuous_sinShift R.y₀).snd')
  have htile : ∀ i, (∫ x in Icc (T i).x₀ (T i).x₁, sinShift R.x₀ x) = 0 ∨
      (∫ y in Icc (T i).y₀ (T i).y₁, sinShift R.y₀ y) = 0 := by
    intro i
    rcases hsides i with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact Or.inl (integral_Icc_sinShift_eq_zero_of_int (T i).hx R.x₀ ⟨n, hn⟩)
    · exact Or.inr (integral_Icc_sinShift_eq_zero_of_int (T i).hy R.y₀ ⟨n, hn⟩)
  rcases hT.prod_integral_dichotomy hint htile with hx | hy
  · exact Or.inl ((integral_Icc_sinShift_self_eq_zero_iff R.hx).mp hx)
  · exact Or.inr ((integral_Icc_sinShift_self_eq_zero_iff R.hy).mp hy)

end IntegerRectangle.RealIntegral
