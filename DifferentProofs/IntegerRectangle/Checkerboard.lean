module

public import DifferentProofs.IntegerRectangle.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The integer-rectangle theorem via a checkerboard colouring

Wagon's third proof colours the plane like a checkerboard of `½ × ½` squares with a corner at the
lower-left corner of the ambient rectangle `R`, and observes that a rectangle contains equal
amounts of black and white **iff** integrating the sign function
`χ(x, y) = (-1)^{⌊2x⌋} (-1)^{⌊2y⌋}` over it gives `0`. A tile with an integer side contributes `0`,
so `R` contributes `0`, and — because the colouring has a corner at `R`'s corner — this forces an
integer side.

As in the real-integral proof we shift the integrand by `R`'s corner rather than translating the
tiling: the one-dimensional factor is `checker s x = (-1)^{⌊2(x - s)⌋}`, the `½ × ½` checkerboard
placed with a corner at `s`. This is exactly the real-integral proof with the sines replaced by the
`±1` square wave; the square wave is periodic with period `1` and integrates to `0` over any
integer-length interval, while over `[s, b]` its integral is the triangle wave `min(r, 1 - r)`
(`r` the fractional part of `b - s`), which vanishes iff `b - s` is an integer.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace IntegerRectangle.Checkerboard

/-- The one-dimensional checkerboard factor `x ↦ (-1)^{⌊2(x - s)⌋}`, i.e. the `½`-periodic square
wave that is `+1` on `[s, s + ½)`, `-1` on `[s + ½, s + 1)`, and so on. -/
private noncomputable def checker (s x : ℝ) : ℝ := (-1 : ℝ) ^ ⌊2 * (x - s)⌋

/-- The square wave has constant absolute value `1`, since `(-1) ^ k = ±1`. -/
private lemma norm_checker (s x : ℝ) : ‖checker s x‖ = 1 := by
  rw [checker, norm_zpow]; norm_num

private lemma measurable_checker (s : ℝ) : Measurable (checker s) := by
  have h1 : Measurable (fun x : ℝ ↦ 2 * (x - s)) := by fun_prop
  exact Measurable.of_discrete.comp (Int.measurable_floor.comp h1)

/-- The checkerboard factor is interval integrable: it is measurable and bounded by `1`. -/
private lemma intervalIntegrable_checker (s a b : ℝ) :
    IntervalIntegrable (checker s) volume a b := by
  rw [intervalIntegrable_iff]
  refine MeasureTheory.Measure.integrableOn_of_bounded (measure_Ioc_lt_top ..).ne
    (measurable_checker s).aestronglyMeasurable (M := 1) ?_
  exact Filter.Eventually.of_forall (fun x ↦ le_of_eq (norm_checker s x))

/-- The square wave is `1`-periodic: shifting `x` by `1` adds `2` to the floor, and
`(-1) ^ (k + 2) = (-1) ^ k`. -/
private lemma checker_periodic (s : ℝ) : Function.Periodic (checker s) 1 := by
  intro x
  change (-1 : ℝ) ^ ⌊2 * (x + 1 - s)⌋ = (-1 : ℝ) ^ ⌊2 * (x - s)⌋
  rw [show (2 : ℝ) * (x + 1 - s) = 2 * (x - s) + ((2 : ℤ) : ℝ) by push_cast; ring,
    Int.floor_add_intCast, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
    show ((-1 : ℝ) ^ (2 : ℤ)) = 1 by norm_num, mul_one]

/-- Shifting the argument by an integer `n` leaves the square wave unchanged. -/
private lemma checker_add_int (s x : ℝ) (n : ℤ) : checker s (x + n) = checker s x := by
  change (-1 : ℝ) ^ ⌊2 * (x + n - s)⌋ = (-1 : ℝ) ^ ⌊2 * (x - s)⌋
  rw [show (2 : ℝ) * (x + n - s) = 2 * (x - s) + ((2 * n : ℤ) : ℝ) by push_cast; ring,
    Int.floor_add_intCast, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
    Even.neg_one_zpow (even_two_mul n), mul_one]

/-- On the white half `[s, s + ½)` of a tile the wave is `+1` (the floor is `0`). -/
private lemma checker_eq_one {s x : ℝ} (h0 : s ≤ x) (h1 : x < s + 1 / 2) : checker s x = 1 := by
  have : ⌊2 * (x - s)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    constructor <;> [linarith; (push_cast; linarith)]
  rw [checker, this, zpow_zero]

/-- On the black half `[s + ½, s + 1)` of a tile the wave is `-1` (the floor is `1`). -/
private lemma checker_eq_neg_one {s x : ℝ} (h0 : s + 1 / 2 ≤ x) (h1 : x < s + 1) :
    checker s x = -1 := by
  have : ⌊2 * (x - s)⌋ = 1 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  rw [checker, this, zpow_one]

/-- If the wave is constant `c` on the open interval `(a, b)`, its integral there is `(b - a) * c`;
the two missing endpoints form a null set. -/
private lemma integral_checker_Ioo_const {s a b c : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Ioo a b, checker s x = c) : (∫ x in a..b, checker s x) = (b - a) * c := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo h, setIntegral_const,
    Real.volume_real_Ioo_of_le hab, smul_eq_mul]

/-- The integral over one full tile `[s, s + 1]` vanishes: `+½` from the white half cancels `-½`
from the black half. -/
private lemma integral_checker_base (s : ℝ) : (∫ x in s..s + 1, checker s x) = 0 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_checker s s (s + 1 / 2))
      (intervalIntegrable_checker s (s + 1 / 2) (s + 1)),
    integral_checker_Ioo_const (by linarith) (fun x hx ↦ checker_eq_one hx.1.le hx.2),
    integral_checker_Ioo_const (by linarith) (fun x hx ↦ checker_eq_neg_one hx.1.le hx.2)]
  ring

/-- The integral over an interval of integer length `n` (any base point `a`) vanishes: it is `n`
copies of the vanishing tile integral. -/
private lemma integral_checker_add_int (s a : ℝ) (n : ℤ) :
    (∫ x in a..(a + n), checker s x) = 0 := by
  rw [show a + (n : ℝ) = a + n • (1 : ℝ) by rw [zsmul_eq_mul, mul_one],
    (checker_periodic s).intervalIntegral_add_zsmul_eq n a
      (fun t₁ t₂ ↦ intervalIntegrable_checker s t₁ t₂),
    (checker_periodic s).intervalIntegral_add_eq a s, integral_checker_base s, smul_zero]

/-- Translating the base point by an integer `n` does not change a partial-tile integral. -/
private lemma integral_checker_shift (s r : ℝ) (n : ℤ) :
    (∫ x in (s + (n : ℝ))..(s + n + r), checker s x) = ∫ x in s..(s + r), checker s x := by
  rw [show s + (n : ℝ) + r = (s + r) + n by ring,
    ← intervalIntegral.integral_comp_add_right (checker s) (n : ℝ)]
  simp_rw [checker_add_int]

/-- Over `[s, s + r]` with `0 < r < 1` the integral is `min r (1 - r) > 0`; this is the triangle
wave that vanishes only at integer lengths. -/
private lemma integral_checker_pos {s r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < ∫ x in s..s + r, checker s x := by
  rcases le_or_gt r (1 / 2) with hr | hr
  · rw [integral_checker_Ioo_const (by linarith)
        (fun x hx ↦ checker_eq_one hx.1.le (by linarith [hx.2]))]
    have : s + r - s = r := by ring
    rw [this, mul_one]; exact hr0
  · rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_checker s s (s + 1 / 2))
        (intervalIntegrable_checker s (s + 1 / 2) (s + r)),
      integral_checker_Ioo_const (by linarith) (fun x hx ↦ checker_eq_one hx.1.le hx.2),
      integral_checker_Ioo_const (by linarith)
        (fun x hx ↦ checker_eq_neg_one hx.1.le (by linarith [hx.2]))]
    nlinarith

/-- The checkerboard integrand is integrable over any rectangle (it is bounded and measurable). -/
private lemma integrableOn_checker_prod (R : Rectangle) :
    IntegrableOn (fun z : ℝ × ℝ => checker R.x₀ z.1 * checker R.y₀ z.2) R.toSet volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded R.isCompact_toSet.measure_ne_top
    (((measurable_checker R.x₀).comp measurable_fst).mul
      ((measurable_checker R.y₀).comp measurable_snd)).aestronglyMeasurable (M := 1) ?_
  refine Filter.Eventually.of_forall fun z ↦ le_of_eq ?_
  rw [norm_mul, norm_checker, norm_checker, mul_one]

/-- Over a tile the shift is immaterial: an integer side-length gives equal black and white. -/
private lemma integral_Icc_checker_eq_zero_of_int {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (h : ∃ n : ℤ, b - a = n) : (∫ x in Icc a b, checker s x) = 0 := by
  obtain ⟨n, hn⟩ := h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    show b = a + (n : ℝ) by linarith, integral_checker_add_int s a n]

/-- At the corner (lower limit equal to the shift) the colouring integrates to `0` **iff** the
length is an integer. This is where the corner-at-`R` hypothesis of Wagon's proof is used. -/
private lemma integral_Icc_checker_self_eq_zero_iff {b s : ℝ} (hsb : s ≤ b) :
    (∫ x in Icc s b, checker s x) = 0 ↔ ∃ n : ℤ, b - s = n := by
  refine ⟨fun hzero ↦ ?_, fun h ↦ integral_Icc_checker_eq_zero_of_int hsb s h⟩
  by_contra hcon
  obtain ⟨n, r, hr0, hr1, hb⟩ : ∃ (n : ℤ) (r : ℝ), 0 < r ∧ r < 1 ∧ b = s + n + r := by
    refine ⟨⌊b - s⌋, Int.fract (b - s), Int.fract_pos.mpr ?_, Int.fract_lt_one _, ?_⟩
    · exact fun heq ↦ hcon ⟨⌊b - s⌋, heq⟩
    · have := Int.floor_add_fract (b - s); linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsb, hb,
    ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_checker s s (s + n)) (intervalIntegrable_checker s (s + n) (s + n + r)),
    integral_checker_add_int s s n, zero_add, integral_checker_shift s r n] at hzero
  exact absurd hzero (integral_checker_pos hr0 hr1).ne'

/-- **Checkerboard proof** (Rochberg–Stein) of the integer-rectangle tiling theorem. -/
theorem IntegerRectangleTheorem_Checkerboard : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  have hint : IntegrableOn
      (fun z : ℝ × ℝ => checker R.x₀ z.1 * checker R.y₀ z.2) R.toSet volume :=
    integrableOn_checker_prod R
  have htile : ∀ i, (∫ x in Icc (T i).x₀ (T i).x₁, checker R.x₀ x) = 0 ∨
      (∫ y in Icc (T i).y₀ (T i).y₁, checker R.y₀ y) = 0 := by
    intro i
    rcases hsides i with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact Or.inl (integral_Icc_checker_eq_zero_of_int (T i).hx R.x₀ ⟨n, hn⟩)
    · exact Or.inr (integral_Icc_checker_eq_zero_of_int (T i).hy R.y₀ ⟨n, hn⟩)
  rcases hT.prod_integral_dichotomy hint htile with hx | hy
  · exact Or.inl ((integral_Icc_checker_self_eq_zero_iff R.hx).mp hx)
  · exact Or.inr ((integral_Icc_checker_self_eq_zero_iff R.hy).mp hy)

end IntegerRectangle.Checkerboard
