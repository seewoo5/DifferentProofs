module

public import DifferentProofs.IntegerRectangle.GridRefinement
public import DifferentProofsForMathlib.Algebra.Order.Floor.Ring

/-!
# The integer-rectangle theorem by counting squares

Wagon's fourth proof, due to Imre Z. Ruzsa and to Peter Gilbert. Wagon builds an auxiliary
tiling: every vertical grid line of the tiling whose x-coordinate is off the integer lattice is
translated to the nearest half-integer line `⌊x⌋ + 1/2`, and likewise for the horizontal lines,
lattice lines staying put. All coordinates of the new picture then lie on the half-unit grid, so
each of its rectangles is a union of `1/2 × 1/2` squares — the cells of the checkerboard of the
third proof — and can simply be counted. A tile with an integer side keeps that side integral
under the translation, hence covers an even number of squares. But if neither side of `R` were an
integer, the translated `R` would have both sides equal to half an odd integer and so cover an odd
number of squares, contradicting the count tile by tile.

Twice the translated coordinate of `x`, measured from a base point `a`, is the integer

```
cellIndex a x = ⌊x - a⌋ + ⌈x - a⌉,
```

the number of half-unit steps from `a` to the translated `x`; it is even exactly when `x - a` is
an integer (`even_cellIndex_iff`). The number of squares of a rectangle is then the product of its
two coordinate increments of `cellIndex` (`cellCount`), that is, the fg-area
(`IntegerRectangle.fgArea`) of the pair `cellIndex a`, `cellIndex b`. So it is additive over a
tiling by `IsTiling.sum_fgArea` (`sum_cellCount`). This additivity is exactly what Wagon's
auxiliary tiling delivers, and taking it from the fg-area avoids constructing that tiling and
proving it is one — the same device as in the polynomial proof. As in the other proofs the grid
is based at the lower-left corner of `R`, which replaces Wagon's "place `R` in standard position".

## Main result

- `IntegerRectangleTheorem_CountingSquares`: Ruzsa's counting-squares proof of the
  integer-rectangle theorem.
-/

@[expose] public section

namespace IntegerRectangle.CountingSquares

/-- The coordinate of `x` on the half-unit grid based at `a`, counted in half-steps: `x` is
translated to `a + ⌊x - a⌋ + 1/2` unless it already sits an integer distance from `a`, in which
case it stays put, and `cellIndex a x` is twice the resulting offset from `a`. -/
noncomputable def cellIndex (a x : ℝ) : ℤ := ⌊x - a⌋ + ⌈x - a⌉

/-- The number of squares of the half-unit grid based at `(a, b)` covered by the translation of a
rectangle: the fg-area of the pair of grid coordinates. -/
noncomputable def cellCount (a b : ℝ) (S : Rectangle) : ℤ :=
  (cellIndex a S.x₁ - cellIndex a S.x₀) * (cellIndex b S.y₁ - cellIndex b S.y₀)

private lemma cellIndex_self (a : ℝ) : cellIndex a a = 0 := by simp [cellIndex]

/-- **The parity criterion.** A grid coordinate is even exactly when the point sits an integer
distance from the base point — the translation moves it to a half-integer line otherwise. -/
theorem even_cellIndex_iff {a x : ℝ} : Even (cellIndex a x) ↔ ∃ n : ℤ, x - a = n := by
  have hle := Int.floor_le_ceil (x - a)
  have hlt := Int.ceil_le_floor_add_one (x - a)
  rw [show (∃ n : ℤ, x - a = (n : ℝ)) ↔ ⌈x - a⌉ = ⌊x - a⌋ by
    simp [Int.ceil_eq_floor_iff_mem, eq_comm], cellIndex, Int.even_iff]
  lia

/-- A side of integer length has an even increment of grid coordinates: the translation shifts
both of its endpoints onto the grid without changing their distance. -/
private lemma even_cellIndex_sub (a : ℝ) {u v : ℝ} {n : ℤ} (h : v - u = n) :
    Even (cellIndex a v - cellIndex a u) := by
  have hv : v - a = u - a + (n : ℝ) := by rw [← h]; ring
  exact ⟨n, by simp only [cellIndex, hv, Int.floor_add_intCast, Int.ceil_add_intCast]; ring⟩

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **The square count is additive over a tiling.** This is what Wagon obtains by translating the
grid lines of the tiling into an auxiliary tiling of the translated rectangle; here it is the
fg-area additivity of the thirteenth proof, applied to the grid coordinates. -/
theorem sum_cellCount (hT : IsTiling R T) (a b : ℝ) :
    ∑ i, cellCount a b (T i) = cellCount a b R := by
  have key := hT.sum_fgArea (fun x ↦ (cellIndex a x : ℝ)) fun y ↦ (cellIndex b y : ℝ)
  simp only [fgArea] at key
  simp only [cellCount]
  exact_mod_cast key

/-- **Counting-squares proof** (Ruzsa, Gilbert) of the integer-rectangle tiling theorem. Base the
half-unit grid at the lower-left corner of `R`. Every tile has an integer side, hence covers an
even number of squares, and therefore so does `R`. The corner of `R` has grid coordinate `0`, so
the square count of `R` is the product of the grid coordinates of its two far edges; one of them
is even, which says that the corresponding side of `R` has integer length. -/
theorem IntegerRectangleTheorem_CountingSquares : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  have hR : Even (cellCount R.x₀ R.y₀ R) := by
    rw [← sum_cellCount hT]
    refine Finset.even_sum _ fun i _ ↦ (hsides i).elim
      (fun ⟨n, hw⟩ ↦ (even_cellIndex_sub R.x₀ (by simpa [Rectangle.width] using hw)).mul_right _)
      fun ⟨n, hh⟩ ↦ (even_cellIndex_sub R.y₀ (by simpa [Rectangle.height] using hh)).mul_left _
  simpa only [Rectangle.HasIntegerSide, Rectangle.width, Rectangle.height, cellCount,
    cellIndex_self, sub_zero, Int.even_mul, even_cellIndex_iff] using hR

end IntegerRectangle.CountingSquares
