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
private lemma norm_checker (s x : ℝ) : ‖checker s x‖ = 1 := by simp [checker]

private lemma measurable_checker (s : ℝ) : Measurable (checker s) := by unfold checker; fun_prop

/-- The checkerboard factor is interval integrable: it is measurable and bounded by `1`. -/
private lemma intervalIntegrable_checker (s a b : ℝ) :
    IntervalIntegrable (checker s) volume a b :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    (measurable_checker s).aestronglyMeasurable.restrict
    (.of_forall fun x ↦ (norm_checker s x).trans_le norm_one.ge)

/-- The square wave is `1`-periodic: shifting `x` by `1` adds `2` to the floor exponent. -/
private lemma checker_periodic (s : ℝ) : Function.Periodic (checker s) 1 := fun x ↦ by
  unfold checker
  rw [show (2 : ℝ) * (x + 1 - s) = 2 * (x - s) + ((2 : ℤ) : ℝ) by push_cast; ring,
    Int.floor_add_intCast, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  norm_num

/-- Shifting the argument by an integer `n` leaves the square wave unchanged. -/
private lemma checker_add_int (s x : ℝ) (n : ℤ) : checker s (x + n) = checker s x := by
  simpa using (checker_periodic s).int_mul n x

/-- On the white half `[s, s + ½)` of a tile the wave is `+1` (the floor is `0`). -/
private lemma checker_eq_one {s x : ℝ} (h0 : s ≤ x) (h1 : x < s + 1 / 2) : checker s x = 1 := by
  rw [checker, show ⌊2 * (x - s)⌋ = 0 from Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩,
    zpow_zero]

/-- On the black half `[s + ½, s + 1)` of a tile the wave is `-1` (the floor is `1`). -/
private lemma checker_eq_neg_one {s x : ℝ} (h0 : s + 1 / 2 ≤ x) (h1 : x < s + 1) :
    checker s x = -1 := by
  rw [checker, show ⌊2 * (x - s)⌋ = 1 from
    Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩, zpow_one]

/-- If the wave is constant `c` on `(a, b)`, its integral over `[a, b]` is `(b - a) * c`. -/
private lemma integral_checker_Ioo_const {s a b c : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Ioo a b, checker s x = c) : (∫ x in a..b, checker s x) = (b - a) * c := by
  rw [integral_of_le hab, integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo h,
    setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul]

/-- The integral over one full tile `[s, s + 1]` vanishes: the two half-tiles cancel. -/
private lemma integral_checker_base (s : ℝ) : (∫ x in s..s + 1, checker s x) = 0 := by
  rw [← integral_add_adjacent_intervals (intervalIntegrable_checker s s (s + 1 / 2))
      (intervalIntegrable_checker s (s + 1 / 2) (s + 1)),
    integral_checker_Ioo_const (by linarith) (fun x hx ↦ checker_eq_one hx.1.le hx.2),
    integral_checker_Ioo_const (by linarith) (fun x hx ↦ checker_eq_neg_one hx.1.le hx.2)]
  ring

/-- The integral over any interval of integer length `n` vanishes: it is `n` tile integrals. -/
private lemma integral_checker_add_int (s a : ℝ) (n : ℤ) :
    (∫ x in a..a + n, checker s x) = 0 := by
  rw [show a + (n : ℝ) = a + n • (1 : ℝ) by simp,
    (checker_periodic s).intervalIntegral_add_zsmul_eq n a (intervalIntegrable_checker s),
    (checker_periodic s).intervalIntegral_add_eq a s, integral_checker_base s, smul_zero]

/-- Translating the base point by an integer `n` does not change a partial-tile integral. -/
private lemma integral_checker_shift (s r : ℝ) (n : ℤ) :
    (∫ x in (s + (n : ℝ))..(s + n + r), checker s x) = ∫ x in s..(s + r), checker s x := by
  rw [show s + (n : ℝ) + r = (s + r) + n by ring, ← integral_comp_add_right (checker s) (n : ℝ)]
  simp_rw [checker_add_int]

/-- Over `[s, s + r]` with `0 < r < 1` the integral is `min r (1 - r)`, which is positive. -/
private lemma integral_checker_pos {s r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < ∫ x in s..s + r, checker s x := by
  rcases le_or_gt r (1 / 2) with hr | hr
  · rw [integral_checker_Ioo_const (by linarith)
      (fun x hx ↦ checker_eq_one hx.1.le (by linarith [hx.2]))]; linarith
  · rw [← integral_add_adjacent_intervals (intervalIntegrable_checker s s (s + 1 / 2))
        (intervalIntegrable_checker s (s + 1 / 2) (s + r)),
      integral_checker_Ioo_const (by linarith) (fun x hx ↦ checker_eq_one hx.1.le hx.2),
      integral_checker_Ioo_const (by linarith)
        (fun x hx ↦ checker_eq_neg_one hx.1.le (by linarith [hx.2]))]; linarith

/-- The checkerboard integrand is integrable over any rectangle (it is bounded and measurable). -/
private lemma integrableOn_checker_prod (R : Rectangle) :
    IntegrableOn (fun z : ℝ × ℝ ↦ checker R.x₀ z.1 * checker R.y₀ z.2) R.toSet volume :=
  Measure.integrableOn_of_bounded (M := 1) R.isCompact_toSet.measure_ne_top
    (by unfold checker; fun_prop)
    (.of_forall fun z ↦ le_of_eq (by rw [norm_mul, norm_checker, norm_checker, mul_one]))

/-- Over a tile the shift is immaterial: an integer side-length gives equal black and white. -/
private lemma integral_Icc_checker_eq_zero_of_int {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (h : ∃ n : ℤ, b - a = n) : (∫ x in Icc a b, checker s x) = 0 := by
  obtain ⟨n, hn⟩ := h
  rw [integral_Icc_eq_integral_Ioc, ← integral_of_le hab, show b = a + (n : ℝ) by linarith,
    integral_checker_add_int s a n]

/-- At the corner (lower limit equal to the shift) the colouring integrates to `0` **iff** the
length is an integer. This is where the corner-at-`R` hypothesis of Wagon's proof is used. -/
private lemma integral_Icc_checker_self_eq_zero_iff {b s : ℝ} (hsb : s ≤ b) :
    (∫ x in Icc s b, checker s x) = 0 ↔ ∃ n : ℤ, b - s = n := by
  refine ⟨fun hzero ↦ ?_, integral_Icc_checker_eq_zero_of_int hsb s⟩
  by_contra hcon
  obtain ⟨n, r, hr0, hr1, hb⟩ : ∃ (n : ℤ) (r : ℝ), 0 < r ∧ r < 1 ∧ b = s + n + r :=
    ⟨⌊b - s⌋, Int.fract (b - s), Int.fract_pos.mpr fun heq ↦ hcon ⟨⌊b - s⌋, heq⟩,
      Int.fract_lt_one _, by linarith [Int.floor_add_fract (b - s)]⟩
  rw [integral_Icc_eq_integral_Ioc, ← integral_of_le hsb, hb,
    ← integral_add_adjacent_intervals (intervalIntegrable_checker s s (s + n))
      (intervalIntegrable_checker s (s + n) (s + n + r)),
    integral_checker_add_int s s n, zero_add, integral_checker_shift s r n] at hzero
  exact absurd hzero (integral_checker_pos hr0 hr1).ne'

end IntegerRectangle.Checkerboard

open IntegerRectangle IntegerRectangle.Checkerboard in
/-- **Checkerboard proof** (Rochberg–Stein) of the integer-rectangle tiling theorem. -/
theorem IntegerRectangleTheorem_Checkerboard : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  exact (hT.prod_integral_dichotomy (integrableOn_checker_prod R) fun i ↦ (hsides i).imp
      (integral_Icc_checker_eq_zero_of_int (T i).hx R.x₀)
      (integral_Icc_checker_eq_zero_of_int (T i).hy R.y₀)).imp
    (integral_Icc_checker_self_eq_zero_iff R.hx).mp
    (integral_Icc_checker_self_eq_zero_iff R.hy).mp
