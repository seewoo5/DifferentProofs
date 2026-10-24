module

public import DifferentProofs.IntegerRectangle.Tiling.Cells
public import Mathlib.Data.ZMod.Basic

/-!
# The corners of the tiles at a point

Two of Wagon's proofs — the Eulerian path of Paterson and its bipartite-graph variation — count
incidences between the tiles of a tiling and the points of the plane, each tile being joined to
the points that are corners of it. Both read the count at a point off the local picture of how
the tiles fit together there: a corner of `R` is a corner of exactly one tile, and every other
point is a corner of `2` or `4` tiles, or of none. That is `IsTiling.sum_cornerCount_eq`, which
this file proves from the four quadrants at the point.

A tile containing a point *fills* one, two or four of the quadrants there: one if the point is a
corner of the tile, two if it lies inside one of its edges, and four if it lies inside the tile
(`card_quadrants_eq`, `cornerCount_eq_ite`). Each quadrant inside `R` is filled by exactly one
tile (`IsTiling.existsUnique_cell`), so the numbers of quadrants the tiles fill add up to the
number of quadrants inside `R` (`IsTiling.sum_card_quadrants`): four at a point inside `R`, two at
a point inside one of its edges, and one at a corner. The tiles filling a single quadrant, which
are the tiles having the point as a corner, are therefore at most as many as the quadrants inside
`R`, and as many up to an even number.

The number of corners a rectangle has at a point, the four corners being counted with
multiplicity so that degenerate rectangles need no separate treatment, is `cornerCount`, and the
corners themselves are `Rectangle.corner`.
-/

@[expose] public section

open Finset

namespace IntegerRectangle

/-! ### Counting corners at a point -/

/-- The corner of `S` named by `b`: on its right side if `b.1`, on its top side if `b.2`. -/
def Rectangle.corner (S : Rectangle) (b : Bool × Bool) : ℝ × ℝ :=
  (if b.1 then S.x₁ else S.x₀, if b.2 then S.y₁ else S.y₀)

/-- The number of vertical edges of `S` on the line `x = u`: `0` or `1`, and `2` when `S` is
degenerate in the horizontal direction and lies on that line. -/
noncomputable def xCount (S : Rectangle) (u : ℝ) : ℕ :=
  (if S.x₀ = u then 1 else 0) + (if S.x₁ = u then 1 else 0)

/-- The number of horizontal edges of `S` on the line `y = v`. -/
noncomputable def yCount (S : Rectangle) (v : ℝ) : ℕ :=
  (if S.y₀ = v then 1 else 0) + (if S.y₁ = v then 1 else 0)

/-- The number of corners of `S` at the point `(u, v)`, the four corners being counted with
multiplicity: a degenerate rectangle has repeated corners. -/
noncomputable def cornerCount (S : Rectangle) (u v : ℝ) : ℕ := xCount S u * yCount S v

open scoped Classical in
/-- `cornerCount` counts the corners at a point. -/
lemma card_corner_eq (S : Rectangle) (u v : ℝ) :
    #{b | S.corner b = (u, v)} = cornerCount S u v := by
  simp only [card_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  grind [Rectangle.corner, cornerCount, xCount, yCount]

/-! ### The quadrants at a point -/

open scoped Classical in
/-- The quadrants at `(u, v)` that `S` fills: those `b` for which `(u, v)` lies in the cell
`S.cell b.1 b.2`, so that `S` reaches to the left of the point if `b.1` and to its right
otherwise, below the point if `b.2` and above it otherwise. -/
noncomputable def quadrants (S : Rectangle) (u v : ℝ) : Finset (Bool × Bool) :=
  {b | ((u, v) : ℝ × ℝ) ∈ S.cell b.1 b.2}

/-- The number of sides of `t` that the interval `[a, b]` reaches: both at an interior point, one
at an endpoint, and none outside. -/
noncomputable def sides (a b t : ℝ) : ℕ :=
  (if a < t ∧ t ≤ b then 1 else 0) + (if a ≤ t ∧ t < b then 1 else 0)

/-- A rectangle fills, at a point, as many quadrants as the product of the numbers of sides of the
point its two coordinate intervals reach. -/
lemma card_quadrants_eq (S : Rectangle) (u v : ℝ) :
    #(quadrants S u v) = sides S.x₀ S.x₁ u * sides S.y₀ S.y₁ v := by
  simp only [quadrants, card_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  grind [sides, Rectangle.cell]

/-- **A tile fills one quadrant at each of its corners, and two or four at its other points.**
For a nondegenerate rectangle, the quadrants it fills at a point number `0`, `1`, `2` or `4`, and
the point is a corner of it exactly when they number one: along each axis the rectangle reaches
both sides of an interior point, one side of an endpoint, and neither side of a point outside it. -/
lemma cornerCount_eq_ite {S : Rectangle} (hS : S.Nondegenerate) (u v : ℝ) :
    cornerCount S u v = (if #(quadrants S u v) = 1 then 1 else 0) ∧
      (#(quadrants S u v) = 0 ∨ #(quadrants S u v) = 1 ∨ #(quadrants S u v) = 2 ∨
        #(quadrants S u v) = 4) := by
  grind [card_quadrants_eq, cornerCount, xCount, yCount, sides, Rectangle.Nondegenerate]

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **The tiles fill the quadrants inside `R`, each exactly once.** Counted over the tiles, the
quadrants filled at a point are as many as the quadrants at it inside `R`: a quadrant inside `R`
is filled by exactly one tile, and a quadrant a tile fills is inside `R`. -/
theorem IsTiling.sum_card_quadrants (hT : IsTiling R T) (u v : ℝ) :
    ∑ i, #(quadrants (T i) u v) = #(quadrants R u v) := by
  simp only [quadrants, card_filter]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ ↦ ?_)
  split_ifs with hb
  · rw [← card_filter, ← Fintype.existsUnique_iff_card_one]; exact hT.existsUnique_cell _ _ hb
  · exact Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun h ↦ hb (hT.cell_subset _ _ i h)

/-! ### The local picture -/

/-- **The local picture at a point** (Wagon). At a corner of `R` the tiles have exactly one corner
in all, and at any other point of the plane `0`, `2` or `4`.

Counted over the tiles, the quadrants filled at the point are the quadrants inside `R`
(`IsTiling.sum_card_quadrants`): four, two, one or none, according as the point lies inside `R`,
inside one of its edges, at one of its corners, or outside it. A tile having the point as a
corner fills one of them, and any other tile none, two or four (`cornerCount_eq_ite`), so the tiles
having the point as a corner are at most as many as the quadrants inside `R`, and as many up to
an even number. -/
theorem IsTiling.sum_cornerCount_eq (hT : IsTiling R T) (u v : ℝ) :
    ∑ i, cornerCount (T i) u v = cornerCount R u v ∨
      cornerCount R u v = 0 ∧
        (∑ i, cornerCount (T i) u v = 2 ∨ ∑ i, cornerCount (T i) u v = 4) := by
  have hQ : ∑ i, cornerCount (T i) u v + 2 * ∑ i, #(quadrants (T i) u v) / 2 =
      #(quadrants R u v) := by
    rw [← hT.sum_card_quadrants, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by lia [cornerCount_eq_ite (hT.nondegenerate i) u v]
  lia [cornerCount_eq_ite ⟨hT.x₀_lt_x₁, hT.y₀_lt_y₁⟩ u v]

/-- **Corner parity.** At every point of the plane, the tiles have in total a number of corners
congruent modulo `2` to the number of corners of `R` there: away from the corners of `R` it is
even, which is Wagon's "`2` or `4` tiles", and at a corner of `R` it is one. -/
theorem IsTiling.sum_cornerCount_mod_two (hT : IsTiling R T) (u v : ℝ) :
    ((∑ i, cornerCount (T i) u v : ℕ) : ZMod 2) = (cornerCount R u v : ZMod 2) :=
  (ZMod.natCast_eq_natCast_iff' _ _ 2).mpr <| by lia [hT.sum_cornerCount_eq u v]

end IntegerRectangle
