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
lemma monotone_scaleFloor (p : ℕ) : Monotone (scaleFloor p) := fun _ _ h ↦
  Int.cast_le.mpr (Int.floor_mono (mul_le_mul_of_nonneg_right h p.cast_nonneg))

/-- The one-dimensional core: a side of integer length `n`, scaled by `p`, ends at an integer
shift `n·p` of its start, and the shift passes through `⌊·⌋`, leaving floor difference `p·n`. -/
private lemma floor_sub_floor_of_int {p : ℕ} {a b : ℝ} {n : ℤ} (h : b - a = n) :
    ⌊b * p⌋ - ⌊a * p⌋ = p * n := by
  have hb : b * (p : ℝ) = a * p + ((p * n : ℤ) : ℝ) := by
    push_cast
    linear_combination (p : ℝ) * h
  rw [hb, Int.floor_add_intCast, add_sub_cancel_left]

/-- A side whose floor-difference factor is `p·m` has length within `1/p` of `m`: scaled by `p`,
the difference is a difference of two floor remainders, each in `[0, 1)`. -/
private lemma abs_sub_lt_of_floor_sub_floor {x₀ x₁ : ℝ} {p : ℕ} (hp : 0 < p) {m : ℤ}
    (h : ⌊x₁ * p⌋ - ⌊x₀ * p⌋ = p * m) : |x₁ - x₀ - m| < 1 / p := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have h' : (⌊x₁ * p⌋ : ℝ) - ⌊x₀ * p⌋ = p * m := by exact_mod_cast h
  rw [lt_div_iff₀ hp', ← abs_of_pos hp', ← abs_mul, abs_lt]
  constructor <;>
    nlinarith [Int.floor_le (x₁ * (p : ℝ)), Int.lt_floor_add_one (x₁ * (p : ℝ)),
      Int.floor_le (x₀ * (p : ℝ)), Int.lt_floor_add_one (x₀ * (p : ℝ))]

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **The area of the rounded rectangle is a multiple of `p`.** The rounded tiles tile the
rounded rectangle, and each has a side whose length is a multiple of `p`, since a side of integer
length `n` rounds to one of length `p n`. -/
theorem dvd_area_round (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) {p : ℕ}
    (hx : ⌊R.x₀ * p⌋ < ⌊R.x₁ * p⌋) (hy : ⌊R.y₀ * p⌋ < ⌊R.y₁ * p⌋) :
    (p : ℤ) ∣ (⌊R.x₁ * p⌋ - ⌊R.x₀ * p⌋) * (⌊R.y₁ * p⌋ - ⌊R.y₀ * p⌋) := by
  have h := hT.sum_area_image ((monotone_scaleFloor p).monotoneOn _)
    ((monotone_scaleFloor p).monotoneOn _)
    (Int.cast_lt.mpr hx) (Int.cast_lt.mpr hy)
  simp only [scaleFloor] at h
  have h' : ∑ i, (⌊(T i).x₁ * p⌋ - ⌊(T i).x₀ * p⌋) * (⌊(T i).y₁ * p⌋ - ⌊(T i).y₀ * p⌋) =
      (⌊R.x₁ * p⌋ - ⌊R.x₀ * p⌋) * (⌊R.y₁ * p⌋ - ⌊R.y₀ * p⌋) := by
    exact_mod_cast h
  rw [← h']
  exact Finset.dvd_sum fun i _ ↦ (hsides i).elim
    (fun ⟨n, hn⟩ ↦ Dvd.dvd.mul_right ⟨n, floor_sub_floor_of_int hn⟩ _)
    fun ⟨n, hn⟩ ↦ Dvd.dvd.mul_left ⟨n, floor_sub_floor_of_int hn⟩ _

/-- **Wagon's claim.** For every prime `p`, some side of the tiled rectangle is within `1/p` of an
integer: a side of the rounded rectangle is a multiple of `p` (`dvd_area_round`), or is `0`. -/
theorem exists_side_near_int (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) {p : ℕ}
    (hp : p.Prime) :
    (∃ n : ℤ, |R.width - n| < 1 / p) ∨ (∃ n : ℤ, |R.height - n| < 1 / p) := by
  have hle {a b : ℝ} (h : a ≤ b) : ⌊a * p⌋ ≤ ⌊b * p⌋ :=
    Int.floor_mono (mul_le_mul_of_nonneg_right h p.cast_nonneg)
  rcases (hle R.hx).lt_or_eq with hx | hx
  · rcases (hle R.hy).lt_or_eq with hy | hy
    · exact ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp (dvd_area_round hT hsides hx hy)).imp
        (fun ⟨m, hm⟩ ↦ ⟨m, abs_sub_lt_of_floor_sub_floor hp.pos hm⟩)
        fun ⟨m, hm⟩ ↦ ⟨m, abs_sub_lt_of_floor_sub_floor hp.pos hm⟩
    · exact .inr ⟨0, abs_sub_lt_of_floor_sub_floor hp.pos (by rw [hy, sub_self, mul_zero])⟩
  · exact .inl ⟨0, abs_sub_lt_of_floor_sub_floor hp.pos (by rw [hx, sub_self, mul_zero])⟩

/-- A real number that is not an integer keeps a fixed positive distance from every integer. -/
private lemma exists_forall_le_abs_sub {x : ℝ} (h : ¬∃ n : ℤ, x = n) :
    ∃ δ > 0, ∀ n : ℤ, δ ≤ |x - n| :=
  ⟨|x - round x|, abs_sub_pos.mpr fun heq ↦ h ⟨round x, heq⟩, round_le x⟩

end IntegerRectangle.Primes

open IntegerRectangle IntegerRectangle.Primes in
/-- **Prime-numbers proof** (Robinson) of the integer-rectangle tiling theorem. -/
theorem IntegerRectangleTheorem_Primes : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  by_contra hcon
  rw [Rectangle.HasIntegerSide, not_or] at hcon
  obtain ⟨δw, hδw, hw⟩ := exists_forall_le_abs_sub hcon.1
  obtain ⟨δh, hδh, hh⟩ := exists_forall_le_abs_sub hcon.2
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max ⌈1 / δw⌉₊ ⌈1 / δh⌉₊ + 1)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have key : ∀ δ : ℝ, 0 < δ → ⌈1 / δ⌉₊ < p → 1 / (p : ℝ) < δ := fun δ hδ h₀ ↦ by
    have h₁ : 1 / δ < p := (Nat.le_ceil _).trans_lt (by exact_mod_cast h₀)
    rw [div_lt_iff₀ hδ] at h₁
    rw [div_lt_iff₀ hp']
    linarith [mul_comm (p : ℝ) δ]
  have hpw := key δw hδw (lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left _ _)) hple)
  have hph := key δh hδh (lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_right _ _)) hple)
  rcases exists_side_near_int hT hsides hp with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact absurd hn (not_lt.mpr (hpw.le.trans (hw n)))
  · exact absurd hn (not_lt.mpr (hph.le.trans (hh n)))
