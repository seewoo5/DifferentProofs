module

public import DifferentProofs.IntegerRectangle.Tiling.Image
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Nat.Prime.Infinite

/-!
# The integer-rectangle theorem via prime numbers

Wagon's sixth proof (Raphael Robinson). For every prime `p`, the width or the height of `R` is
within `1/p` of an integer; there are infinitely many primes, so one of the two is an integer. To
prove the claim, scale the tiling up by `p` and replace every tile corner `(x, y)` of the scaled
tiling by `(⌊x⌋, ⌊y⌋)`. This gives an integer-sided rectangle tiled by integer-sided rectangles,
each with a side that is a multiple of `p`, since a side of integer length `n` becomes a side of
length `p n`. So the area of the large rectangle is a multiple of `p`, and `p` being prime, so is
one of its sides. The sides of the large rectangle differ from those of the scaled-up rectangle by
less than `1`, so a side of `R` differs from an integer by less than `1/p`.

The rounded tiling moves the lines of the given one in order, the line `x = a` to `x = ⌊p a⌋`
(`scaleFloor`) and the line `y = a` to `y = ⌊p a⌋`, so it is a tiling by `IsTiling.image`, and
its area is additive (`IsTiling.sum_area_image`). A tile, or even `R`, narrower than `1/p` may
round to a segment; a tile then simply drops out of the rounded tiling, and a side of `R` that
rounds to a point is within `1/p` of the integer `0`.
-/

@[expose] public section

namespace IntegerRectangle.Primes

/-- Scaling by `p` and rounding down to the integer lattice. -/
noncomputable def scaleFloor (p : ℕ) (a : ℝ) : ℝ := ⌊a * p⌋

/-- Rounding keeps the order of the lines of a tiling. -/
lemma monotone_scaleFloor (p : ℕ) : Monotone (scaleFloor p) := fun _ _ _ ↦ by
  unfold scaleFloor; gcongr

/-- The one-dimensional core: a side of integer length `n`, scaled by `p`, ends at the integer
shift `p n` of its start, and the shift passes through `⌊·⌋`, so it rounds to length `p n`. -/
private lemma dvd_floor_sub_floor {p : ℕ} {a b : ℝ} :
    (∃ n : ℤ, b - a = n) → (p : ℤ) ∣ ⌊b * p⌋ - ⌊a * p⌋ := fun ⟨n, h⟩ ↦ ⟨n, by
  rw [show b * p = a * p + (p * n : ℤ) by push_cast; linear_combination ↑p * h,
    Int.floor_add_intCast, add_sub_cancel_left]⟩

/-- A side that rounds to a multiple `p m` of `p` has length within `1/p` of `m`: scaled by `p`,
its right end shifted back by `p m` has the floor of its left end, so the two are within `1`. -/
private lemma exists_abs_sub_lt_of_dvd {x₀ x₁ : ℝ} {p : ℕ} (hp : 0 < p) :
    (p : ℤ) ∣ ⌊x₁ * p⌋ - ⌊x₀ * p⌋ → ∃ m : ℤ, |x₁ - x₀ - m| < 1 / p := fun ⟨m, h⟩ ↦ ⟨m, by
  rw [lt_div_iff₀ (by positivity), ← Nat.abs_cast p, ← abs_mul,
    show (x₁ - x₀ - m) * p = x₁ * p - (p * m : ℤ) - x₀ * p by push_cast; ring]
  exact Int.abs_sub_lt_one_of_floor_eq_floor (by rw [Int.floor_sub_intCast]; lia)⟩

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **The area of the rounded rectangle is a multiple of `p`.** The rounded tiles tile the
rounded rectangle, and each has a side whose length is a multiple of `p`, since a side of integer
length `n` rounds to one of length `p n`. -/
theorem dvd_area_round (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) {p : ℕ}
    (hx : ⌊R.x₀ * p⌋ < ⌊R.x₁ * p⌋) (hy : ⌊R.y₀ * p⌋ < ⌊R.y₁ * p⌋) :
    (p : ℤ) ∣ (⌊R.x₁ * p⌋ - ⌊R.x₀ * p⌋) * (⌊R.y₁ * p⌋ - ⌊R.y₀ * p⌋) := by
  have h := hT.sum_area_image ((monotone_scaleFloor p).monotoneOn _)
    ((monotone_scaleFloor p).monotoneOn _) (Int.cast_lt.mpr hx) (Int.cast_lt.mpr hy)
  simp only [scaleFloor] at h
  norm_cast at h
  exact h ▸ Finset.dvd_sum fun i _ ↦ (hsides i).elim (fun hn ↦ (dvd_floor_sub_floor hn).mul_right _)
    fun hn ↦ (dvd_floor_sub_floor hn).mul_left _

/-- **Wagon's claim.** For every prime `p`, some side of the tiled rectangle is within `1/p` of an
integer: a side of the rounded rectangle is a multiple of `p` (`dvd_area_round`), or is `0`. -/
theorem exists_side_near_int (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) {p : ℕ}
    (hp : p.Prime) : (∃ n : ℤ, |R.width - n| < 1 / p) ∨ (∃ n : ℤ, |R.height - n| < 1 / p) := by
  refine .imp (exists_abs_sub_lt_of_dvd hp.pos) (exists_abs_sub_lt_of_dvd hp.pos) ?_
  obtain hx | hx := (Int.cast_le.mp (monotone_scaleFloor p R.hx)).eq_or_lt
  · exact .inl ⟨0, by lia⟩
  obtain hy | hy := (Int.cast_le.mp (monotone_scaleFloor p R.hy)).eq_or_lt
  · exact .inr ⟨0, by lia⟩
  exact (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp (dvd_area_round hT hsides hx hy)

/-- A real number that is not an integer is, for all large `p`, not within `1/p` of an integer: it
keeps the positive distance `|x - round x|` from every integer (`round_le`), and `1/p → 0`. -/
private lemma eventually_not_exists_abs_sub_lt {x : ℝ} (h : ¬∃ n : ℤ, x = n) :
    ∀ᶠ p : ℕ in Filter.atTop, ¬∃ n : ℤ, |x - n| < 1 / p :=
  (tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const (abs_sub_pos.mpr (h ⟨round x, ·⟩))).mono
    fun _ hp ⟨n, hn⟩ ↦ (round_le x n).not_gt (hn.trans hp)

end IntegerRectangle.Primes

open IntegerRectangle IntegerRectangle.Primes in
/-- **Prime-numbers proof** (Robinson) of the integer-rectangle tiling theorem. If neither side of
`R` were an integer, then for all large `p` neither would be within `1/p` of an integer; there are
infinitely many primes, and a large one contradicts Wagon's claim (`exists_side_near_int`). -/
theorem IntegerRectangleTheorem_Primes : IntegerRectangleTheorem := fun _ _ hT hsides ↦ by
  refine or_iff_not_and_not.mpr fun ⟨hw, hh⟩ ↦ ?_
  obtain ⟨N, hN⟩ := ((eventually_not_exists_abs_sub_lt hw).and
    (eventually_not_exists_abs_sub_lt hh)).exists_forall_of_atTop
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  exact not_or.mpr (hN p hNp) (exists_side_near_int hT hsides hp)
