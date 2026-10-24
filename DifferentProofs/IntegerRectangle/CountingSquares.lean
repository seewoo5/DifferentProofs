module

public import DifferentProofs.IntegerRectangle.Tiling.Image
public import DifferentProofsForMathlib.Algebra.Order.Floor.Ring

/-!
# The integer-rectangle theorem by counting squares

Wagon's fourth proof, due to Imre Z. Ruzsa and to Peter Gilbert. Place `R` in standard position
and build an auxiliary tiling of a possibly new rectangle `R'` by translating the lines of the
tiling: a vertical line `x = a` with `a` an integer is not moved, and one with `a` not an integer
is moved to the half-integer line `x = ⌊a⌋ + 1/2`, and likewise for the horizontal lines. This may
reduce the number of tiles, which is unimportant. If neither side of `R` were an integer, `R'`
would be a rectangle in standard position with both sides equal to half an odd integer, and so it
would contain an odd number of the `1/2 × 1/2` squares of the checkerboard of the third proof. But
a tile with an integer side keeps that side integral under the translation, so each tile of `R'`
contains an even number of squares.

The lattice is based at the lower-left corner of `R` instead of the origin, which replaces the
standard position. Twice the translated coordinate of `x`, measured from the base point `a`, is
the integer

```
cellIndex a x = ⌊x - a⌋ + ⌈x - a⌉,
```

the number of half-unit steps from `a` to the translated `x`; it is even exactly when `x - a` is
an integer (`even_cellIndex_iff`). The translation `translate a` keeps the order of the lines, so
the translated tiles tile `R'` (`IsTiling.image`). The squares in a rectangle are counted by their
upper right corners (`squares`), and every square of `R'` lies in exactly one of its tiles, which
is the exact partition of a tiling into half-open cells (`card_squares_eq_sum`). The number of
squares of a translated rectangle is the product of the increments of `cellIndex` across its two
sides (`card_squares_image`).

## Main result

- `IntegerRectangleTheorem_CountingSquares`: Ruzsa's counting-squares proof of the
  integer-rectangle theorem.
-/

@[expose] public section

open Finset

namespace IntegerRectangle.CountingSquares

/-! ### Translating the lines of the tiling -/

/-- The coordinate of `x` on the half-unit grid based at `a`, counted in half-steps: `x` is
translated to `a + ⌊x - a⌋ + 1/2` unless it already sits an integer distance from `a`, in which
case it stays put, and `cellIndex a x` is twice the resulting offset from `a`. -/
noncomputable def cellIndex (a x : ℝ) : ℤ := ⌊x - a⌋ + ⌈x - a⌉

/-- The translation of the lines of the tiling, onto the half-unit grid based at `a`. -/
noncomputable def translate (a x : ℝ) : ℝ := a + cellIndex a x / 2

/-- The base point has grid coordinate `0`. -/
private lemma cellIndex_self (a : ℝ) : cellIndex a a = 0 := by
  simp only [cellIndex, sub_self, Int.floor_zero, Int.ceil_zero, add_zero]

/-- The grid coordinate is monotone, floor and ceiling being so. -/
private lemma cellIndex_mono (a : ℝ) : Monotone (cellIndex a) := fun _ _ _ ↦ by
  unfold cellIndex; gcongr

/-- The translation keeps the order of the lines. -/
lemma monotone_translate (a : ℝ) : Monotone (translate a) := fun _ _ _ ↦ by
  unfold translate cellIndex; gcongr

/-- **The parity criterion.** A grid coordinate is even exactly when the point sits an integer
distance from the base point — the translation moves it to a half-integer line otherwise. -/
theorem even_cellIndex_iff {a x : ℝ} : Even (cellIndex a x) ↔ ∃ n : ℤ, x - a = n := by
  rw [← exists_congr fun _ ↦ eq_comm, ← Set.mem_range, ← Int.ceil_eq_floor_iff_mem]
  grind [cellIndex, Int.floor_le_ceil (x - a), Int.ceil_le_floor_add_one (x - a)]

/-- A side of integer length has an even increment of grid coordinates: the translation shifts
both of its endpoints onto the grid without changing their distance. -/
private lemma even_cellIndex_sub (a : ℝ) {u v : ℝ} {n : ℤ} (h : v - u = n) :
    Even (cellIndex a v - cellIndex a u) := by
  obtain rfl := eq_add_of_sub_eq' h
  grind [cellIndex, Int.floor_add_intCast, Int.ceil_add_intCast, add_sub_right_comm]

/-! ### Counting squares -/

/-- The squares of the half-unit grid based at `(a, b)` lying in `S`, counted by their upper right
corners: the pair `(j, k)` stands for the square with upper right corner `(a + j/2, b + k/2)`,
and is counted when that corner lies in the half-open cell of `S`. For a rectangle whose edges are
grid lines, these are exactly the squares inside it. -/
noncomputable def squares (a b : ℝ) (S : Rectangle) : Finset (ℤ × ℤ) :=
  Ioc ⌊2 * (S.x₀ - a)⌋ ⌊2 * (S.x₁ - a)⌋ ×ˢ Ioc ⌊2 * (S.y₀ - b)⌋ ⌊2 * (S.y₁ - b)⌋

/-- A square is counted in `S` exactly when its upper right corner lies in the half-open cell
of `S`. -/
private lemma mem_squares {a b : ℝ} {S : Rectangle} {k : ℤ × ℤ} :
    k ∈ squares a b S ↔ ((a + k.1 / 2, b + k.2 / 2) : ℝ × ℝ) ∈ S.toSetIoc := by
  grind [squares, Rectangle.mem_toSetIoc', Int.floor_lt, Int.le_floor]

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **Every square lies in exactly one tile.** The half-open cells of the tiles partition that of
`R` (`IsTiling.iUnion_toSetIoc`, `IsTiling.pairwiseDisjoint_toSetIoc`), so the squares of `R` are
those of its tiles, each counted once. -/
theorem card_squares_eq_sum (hT : IsTiling R T) (a b : ℝ) :
    #(squares a b R) = ∑ i, #(squares a b (T i)) :=
  (congrArg card (by grind [mem_squares, hT.iUnion_toSetIoc, Set.mem_iUnion])).trans <| card_biUnion
    fun _ _ _ _ h ↦ by grind [disjoint_left, hT.pairwiseDisjoint_toSetIoc h, mem_squares]

/-- The number of squares of the half-unit grid based at `(a, b)` in the translation of a
rectangle: the product of the increments of the grid coordinates across its two sides. -/
noncomputable def cellCount (a b : ℝ) (S : Rectangle) : ℤ :=
  (cellIndex a S.x₁ - cellIndex a S.x₀) * (cellIndex b S.y₁ - cellIndex b S.y₀)

/-- **The squares of a translated rectangle**: its edges are grid lines, and it contains as many
squares as the product of the increments of the grid coordinates across its sides. -/
theorem card_squares_image (a b : ℝ) (S : Rectangle) :
    (#(squares a b (S.image (translate a) (translate b))) : ℤ) = cellCount a b S := by
  have htr (c x : ℝ) : 2 * (translate c x - c) = cellIndex c x := by unfold translate; ring
  simp only [squares, Rectangle.image, min_eq_left, max_eq_right, monotone_translate _ S.hx,
    monotone_translate _ S.hy, htr, Int.floor_intCast, card_product, Nat.cast_mul,
    Int.card_Ioc_of_le, cellIndex_mono _ S.hx, cellIndex_mono _ S.hy, cellCount]

/-- **The squares of `R'` are those of its tiles.** The translated tiles tile the translated
rectangle `R'` (`IsTiling.image`), and every square of `R'` lies in exactly one of them
(`card_squares_eq_sum`); a tile collapsed by the translation has no square. -/
theorem sum_cellCount (hT : IsTiling R T) :
    ∑ i, cellCount R.x₀ R.y₀ (T i) = cellCount R.x₀ R.y₀ R := by
  have hpos {a x : ℝ} (h : a < x) : translate a a < translate a x := by
    unfold translate; gcongr; rw [cellIndex_self, cellIndex]
    lia [Int.ceil_pos.mpr (sub_pos.mpr h), Int.floor_nonneg.mpr (sub_pos.mpr h).le]
  simp only [← card_squares_image, ← Nat.cast_sum, card_squares_eq_sum (hT.image
    ((monotone_translate _).monotoneOn _) ((monotone_translate _).monotoneOn _) (hpos hT.x₀_lt_x₁)
    (hpos hT.y₀_lt_y₁)), sum_prune (f := fun S ↦ #(squares R.x₀ R.y₀ S)) _ fun _ _ ↦ by
      grind [card_eq_zero, mem_squares, Rectangle.mem_toSetIoc', Rectangle.Nondegenerate]]

end IntegerRectangle.CountingSquares

open IntegerRectangle IntegerRectangle.CountingSquares in
/-- **Counting-squares proof** (Ruzsa, Gilbert) of the integer-rectangle tiling theorem. Base the
half-unit grid at the lower-left corner of `R`. Every tile has an integer side, so its translation
contains an even number of squares, and therefore so does the translation of `R`. The corner of
`R` has grid coordinate `0`, so the square count of the translation of `R` is the product of the
grid coordinates of its two far edges; one of them is even, which says that the corresponding
side of `R` has integer length. -/
theorem IntegerRectangleTheorem_CountingSquares : IntegerRectangleTheorem := fun R T hT hsides ↦ by
  have hR : Even (cellCount R.x₀ R.y₀ R) := sum_cellCount hT ▸ even_sum _ fun i _ ↦
    (hsides i).elim (fun ⟨_, hw⟩ ↦ (even_cellIndex_sub _ hw).mul_right _)
      fun ⟨_, hh⟩ ↦ (even_cellIndex_sub _ hh).mul_left _
  simpa only [Rectangle.HasIntegerSide, Rectangle.width, Rectangle.height, cellCount,
    cellIndex_self, sub_zero, Int.even_mul, even_cellIndex_iff] using hR
