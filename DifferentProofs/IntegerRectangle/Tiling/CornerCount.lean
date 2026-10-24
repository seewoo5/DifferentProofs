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

/-- The number of vertical edges of `S` on the line `x = u`: `0` or `1`, and `2` for a rectangle
degenerate in the horizontal direction. -/
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
  simp only [card_filter, Fintype.sum_prod_type, Fintype.sum_bool, Rectangle.corner,
    cornerCount, xCount, yCount, Prod.mk.injEq]
  split_ifs <;> simp_all

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
  classical
  simp only [quadrants, card_filter, Fintype.sum_prod_type, Fintype.sum_bool, sides,
    Rectangle.mem_cell_tt, Rectangle.mem_cell_tf, Rectangle.mem_cell_ft, Rectangle.mem_cell_ff]
  split_ifs <;> simp_all

/-- Along one axis, a nondegenerate interval reaches both sides of an interior point, one side of
an endpoint, and neither side of a point outside it: the endpoints are the points with exactly
one side reached. -/
private lemma sides_spec {a b t : ℝ} (hab : a < b) :
    ((if a = t then 1 else 0) + (if b = t then 1 else 0) =
      if sides a b t = 1 then 1 else 0) ∧ sides a b t ≤ 2 := by
  unfold sides
  split_ifs <;> grind

/-- **A tile fills one quadrant at each of its corners, and two or four at its other points.**
For a nondegenerate rectangle, the quadrants it fills at a point number `0`, `1`, `2` or `4`, and
the point is a corner of it exactly when they number one. -/
lemma cornerCount_eq_ite {S : Rectangle} (hS : S.Nondegenerate) (u v : ℝ) :
    cornerCount S u v = (if #(quadrants S u v) = 1 then 1 else 0) ∧
      (#(quadrants S u v) = 0 ∨ #(quadrants S u v) = 1 ∨ #(quadrants S u v) = 2 ∨
        #(quadrants S u v) = 4) := by
  obtain ⟨hx, hx₂⟩ := sides_spec (t := u) hS.1
  obtain ⟨hy, hy₂⟩ := sides_spec (t := v) hS.2
  rw [card_quadrants_eq, cornerCount, xCount, yCount, hx, hy]
  generalize sides S.x₀ S.x₁ u = a at hx₂ ⊢
  generalize sides S.y₀ S.y₁ v = b at hy₂ ⊢
  interval_cases a <;> interval_cases b <;> decide

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **The tiles fill the quadrants inside `R`, each exactly once.** Counted over the tiles, the
quadrants filled at a point are as many as the quadrants at it inside `R`: a quadrant inside `R`
is filled by exactly one tile, and a quadrant a tile fills is inside `R`. -/
theorem IsTiling.sum_card_quadrants (hT : IsTiling R T) (u v : ℝ) :
    ∑ i, #(quadrants (T i) u v) = #(quadrants R u v) := by
  classical
  simp only [quadrants, card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  split_ifs with hb
  · obtain ⟨i, hi, huniq⟩ := hT.existsUnique_cell b.1 b.2 hb
    exact (Fintype.sum_eq_single i fun j hj ↦ ite_eq_right fun h ↦ hj (huniq j h)).trans
      (ite_eq_left hi)
  · exact Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun h ↦ hb (hT.cell_subset b.1 b.2 i h)

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
  have hQ := hT.sum_card_quadrants u v
  obtain ⟨hR, hR₄⟩ := cornerCount_eq_ite ⟨hT.x₀_lt_x₁, hT.y₀_lt_y₁⟩ u v
  have hsplit : ∀ i, #(quadrants (T i) u v) =
      cornerCount (T i) u v + 2 * (#(quadrants (T i) u v) / 2) := fun i ↦ by
    obtain ⟨h, h₄⟩ := cornerCount_eq_ite (hT.nondegenerate i) u v
    rw [h]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib, ← Finset.mul_sum] at hQ
  rw [hR]
  split_ifs <;> omega

/-- **Corner parity.** At every point of the plane, the tiles have in total a number of corners
congruent modulo `2` to the number of corners of `R` there: away from the corners of `R` it is
even, which is Wagon's "`2` or `4` tiles", and at a corner of `R` it is one. -/
theorem IsTiling.sum_cornerCount_mod_two (hT : IsTiling R T) (u v : ℝ) :
    ((∑ i, cornerCount (T i) u v : ℕ) : ZMod 2) = (cornerCount R u v : ZMod 2) := by
  rcases hT.sum_cornerCount_eq u v with h | ⟨h₀, h | h⟩ <;> rw [h] <;> simp [h₀] <;> decide

end IntegerRectangle
