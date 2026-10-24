module

public import DifferentProofs.IntegerRectangle.Tiling.Grid
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The integer-rectangle theorem via step functions

Wagon's thirteenth proof, due to Melvin Hochster and Attila Máté. Place the rectangle in standard
position and define a graph `Γ` whose vertices are the points of the x-axis at which some tile has
a vertical boundary, `x₀ < x₁ < ⋯`, and the points of the y-axis that occur as the top or bottom
coordinate of some tile, `y₀ < y₁ < ⋯`. Two vertices on the x-axis are joined when some H-tile
spans the interval between them, and two vertices on the y-axis when some V-tile does. The goal is
to show that the origin lies in the same connected component of `Γ` as `(a, 0)` or `(0, b)`.

Assign distinct numbers to the connected components of `Γ` in an arbitrary way, and define a step
function `f` on `[0, a]` whose value on `(x_i, x_{i+1})` is the number of the component of
`x_{i+1}` less the number of the component of `x_i`. The sum of the values of `f` on the intervals
between two vertices joined by an edge is `0`. Define `g` on `[0, b]` likewise. Now refine the
tiling into a grid by drawing all the lines `x = x_i` and `y = y_i`: `f(x) g(y)` is constant on
each grid rectangle, and its values on the grid rectangles in one tile add up to `0`, being the
product of the sums of `f` and of `g` along the two sides of the tile, one of which vanishes. So
the sum over all the grid rectangles is `0`. But it is the product of the sum of `f` over all the
intervals between consecutive vertices on the x-axis with the sum of `g` over the y-axis, so one of
these vanishes, which says that the origin lies in the same component as `(a, 0)` or as `(0, b)`.
Every edge of `Γ` spans a side of integer length, so that is an integer side of `R`.

## Formalization notes

* The axes are the bottom and left edges of `R`, and the origin its lower-left corner, which
  replaces the standard position. The vertices (`vertices`) are the points `(x, R.y₀)` and
  `(R.x₀, y)` for `x` an abscissa and `y` an ordinate of the grid of the tiling (`Grid.gridX`,
  `Grid.gridY`), and `Γ` (`graph`) is a mathlib `SimpleGraph` on them. A tile with both sides
  integral is both an H-tile and a V-tile and gives an edge on both axes, which changes nothing.
* The components are numbered by an arbitrary injection into `ℕ` (`num`). The function `stepX`
  gives each vertex on the bottom edge the number of its component, so that the value of Wagon's
  `f` on the interval between two consecutive vertices is the increment of `stepX` across it, and
  a sum of values of `f` on consecutive intervals telescopes to an increment of `stepX`; likewise
  `stepY` for `g`.
* The grid refinement is `sum_fgArea`: the products of the increments of `stepX` and
  `stepY` across the grid rectangles, the values of `f(x) g(y)` there, add up tile by tile to the
  products of the increments across the tiles, and over the whole grid to the product of the
  increments across `R`.

## Main result

- `IntegerRectangleTheorem_StepFunction`: Hochster and Máté's step-function proof of the
  integer-rectangle theorem.
-/

@[expose] public section

namespace IntegerRectangle.StepFunction

open Grid

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-! ### The grid refinement

Wagon's refinement of the tiling into a grid, stated for an arbitrary pair of functions
`f, g : ℝ → ℝ` with no regularity whatsoever. Call

```
fgArea f g S = (f S.x₁ - f S.x₀) · (g S.y₁ - g S.y₀)
```

the *fg-area* of a rectangle; for a grid rectangle and the primitives `stepX`, `stepY` of Wagon's
step functions it is the value of `f(x) g(y)` there. Every open grid cell lies in a unique tile
(`Grid.cellTile`), and the cells of a tile fill out a product of index intervals
(`Grid.cellTile_eq_iff`). Summing the fg-area of the cells therefore counts every cell exactly
once, tile by tile, and over a product of index intervals the sum telescopes in both coordinates,
giving the fg-area of the tile, and over the whole grid that of `R` (`sum_fgArea`). -/

/-- The *fg-area* of a rectangle: the increment of `f` across its width times the increment of
`g` across its height. -/
noncomputable def fgArea (f g : ℝ → ℝ) (S : Rectangle) : ℝ :=
  (f S.x₁ - f S.x₀) * (g S.y₁ - g S.y₀)

/-- Double telescoping: summing the product of consecutive differences over a product of index
intervals gives the product of the end differences. -/
private lemma sum_product_sub (F G : ℕ → ℝ) {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∑ p ∈ Finset.Ico a b ×ˢ Finset.Ico c d,
      (F (p.1 + 1) - F p.1) * (G (p.2 + 1) - G p.2) = (F b - F a) * (G d - G c) :=
  ((Finset.sum_product _ _ _).trans
    (Finset.sum_mul_sum (Finset.Ico a b) (Finset.Ico c d)
      (fun j ↦ F (j + 1) - F j) (fun k ↦ G (k + 1) - G k)).symm).trans
    (by rw [Finset.sum_Ico_sub F hab, Finset.sum_Ico_sub G hcd])

open Finset in
/-- **The grid refinement** (Wagon, after Hochster and Máté), for arbitrary `f, g : ℝ → ℝ`:
summing `(f x₁ - f x₀) · (g y₁ - g y₀)` over the tiles of a tiling gives the same quantity for the
tiled rectangle. The tile edges span a grid; every open grid cell lies in exactly one tile, the
cells of a tile fill a product of index intervals, and the sum telescopes in both coordinates. -/
theorem sum_fgArea (hT : IsTiling R T) (f g : ℝ → ℝ) :
    ∑ i, fgArea f g (T i) = fgArea f g R := by
  classical
  have hgrid : ∑ p ∈ range ((gridX R T).sort.length - 1) ×ˢ
        range ((gridY R T).sort.length - 1),
      (f (nth (gridX R T) (p.1 + 1)) - f (nth (gridX R T) p.1)) *
        (g (nth (gridY R T) (p.2 + 1)) - g (nth (gridY R T) p.2)) = fgArea f g R := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    refine (sum_product_sub (fun j ↦ f (nth (gridX R T) j)) (fun k ↦ g (nth (gridY R T) k))
      (Nat.zero_le _) (Nat.zero_le _)).trans ?_
    rw [nth_gridX_zero hT, nth_gridX_last hT, nth_gridY_zero hT, nth_gridY_last hT, fgArea]
  rw [← hgrid, ← Finset.sum_fiberwise _ (cellTile hT)
    (fun p ↦ (f (nth (gridX R T) (p.1 + 1)) - f (nth (gridX R T) p.1)) *
      (g (nth (gridY R T) (p.2 + 1)) - g (nth (gridY R T) p.2)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [filter_cellTile_eq hT i]
  refine ((sum_product_sub (fun j ↦ f (nth (gridX R T) j)) (fun k ↦ g (nth (gridY R T) k))
    (le_of_nth_le_nth (idxL_lt i) (((nth_idxL i).le.trans (T i).hx).trans (nth_idxR i).ge))
    (le_of_nth_le_nth (idxB_lt i)
      (((nth_idxB i).le.trans (T i).hy).trans (nth_idxT i).ge))).trans ?_).symm
  rw [nth_idxL, nth_idxR, nth_idxB, nth_idxT, fgArea]

/-! ### Hochster and Máté's graph -/

/-- The vertices of Hochster and Máté's graph: the points of the bottom edge of `R` below a
vertical edge of the tiling, and the points of the left edge of `R` level with a horizontal one. -/
noncomputable def vertices (R : Rectangle) (T : ι → Rectangle) : Finset (ℝ × ℝ) :=
  gridX R T ×ˢ {R.y₀} ∪ {R.x₀} ×ˢ gridY R T

/-- The vertex of `Γ` on the bottom edge of `R` below the abscissa `x` of the grid. -/
def bot {x : ℝ} (hx : x ∈ gridX R T) : vertices R T :=
  ⟨(x, R.y₀), Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hx, Finset.mem_singleton_self _⟩)⟩

/-- The vertex of `Γ` on the left edge of `R` level with the ordinate `y` of the grid. -/
def left {y : ℝ} (hy : y ∈ gridY R T) : vertices R T :=
  ⟨(R.x₀, y), Finset.mem_union_right _ (Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hy⟩)⟩

/-- **Hochster and Máté's graph** `Γ`. Two vertices on the bottom edge of `R` are joined when an
H-tile spans the interval between them, and two vertices on its left edge when a V-tile does. -/
def graph (R : Rectangle) (T : ι → Rectangle) : SimpleGraph (vertices R T) :=
  SimpleGraph.fromRel fun p q ↦ ∃ i,
    ((T i).IsHTile ∧ p.1 = ((T i).x₀, R.y₀) ∧ q.1 = ((T i).x₁, R.y₀)) ∨
      ((T i).IsVTile ∧ p.1 = (R.x₀, (T i).y₀) ∧ q.1 = (R.x₀, (T i).y₁))

/-- The edge of `Γ` spanned by an H-tile. -/
lemma adj_bot (hT : IsTiling R T) {i : ι} (h : (T i).IsHTile) :
    (graph R T).Adj (bot (tile_x₀_mem_gridX i)) (bot (tile_x₁_mem_gridX i)) :=
  (SimpleGraph.fromRel_adj _ _ _).mpr ⟨fun he ↦ (hT.tile_x₀_lt_x₁ i).ne
    (congrArg (fun p : vertices R T ↦ p.1.1) he), .inl ⟨i, .inl ⟨h, rfl, rfl⟩⟩⟩

/-- The edge of `Γ` spanned by a V-tile. -/
lemma adj_left (hT : IsTiling R T) {i : ι} (h : (T i).IsVTile) :
    (graph R T).Adj (left (tile_y₀_mem_gridY i)) (left (tile_y₁_mem_gridY i)) :=
  (SimpleGraph.fromRel_adj _ _ _).mpr ⟨fun he ↦ (hT.tile_y₀_lt_y₁ i).ne
    (congrArg (fun p : vertices R T ↦ p.1.2) he), .inl ⟨i, .inr ⟨h, rfl, rfl⟩⟩⟩

/-- **The edges of `Γ` have integer length.** Joined vertices differ by a vector with integer
entries: an H-tile spans an interval of integer length along the bottom edge, and a V-tile along
the left edge. -/
lemma fract_eq_of_adj {p q : vertices R T} (h : (graph R T).Adj p q) :
    Int.fract p.1.1 = Int.fract q.1.1 ∧ Int.fract p.1.2 = Int.fract q.1.2 := by
  have hH {i : ι} (h : (T i).IsHTile) : Int.fract (T i).x₀ = Int.fract (T i).x₁ :=
    (Int.fract_eq_fract.mpr h).symm
  have hV {i : ι} (h : (T i).IsVTile) : Int.fract (T i).y₀ = Int.fract (T i).y₁ :=
    (Int.fract_eq_fract.mpr h).symm
  obtain ⟨-, ⟨i, ⟨hi, hp, hq⟩ | ⟨hi, hp, hq⟩⟩ | ⟨i, ⟨hi, hp, hq⟩ | ⟨hi, hp, hq⟩⟩⟩ :=
    (SimpleGraph.fromRel_adj _ _ _).mp h <;> rw [hp, hq] <;>
    first | simp [hH hi] | simp [hV hi]

/-- A walk in `Γ` moves by a vector with integer entries. -/
lemma fract_eq_of_reachable {p q : vertices R T} (h : (graph R T).Reachable p q) :
    Int.fract p.1.1 = Int.fract q.1.1 ∧ Int.fract p.1.2 = Int.fract q.1.2 :=
  Relation.reflTransGen_le_of_equivalence_of_le
    (r := fun p q : vertices R T ↦ Int.fract p.1.1 = Int.fract q.1.1 ∧
      Int.fract p.1.2 = Int.fract q.1.2)
    ⟨fun _ ↦ ⟨rfl, rfl⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h h' ↦ ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩
    (fun _ _ ↦ fract_eq_of_adj) p q ((SimpleGraph.reachable_iff_reflTransGen p q).mp h)

/-! ### The step functions -/

/-- **An arbitrary numbering of the components of `Γ` by distinct numbers.** -/
noncomputable def num (R : Rectangle) (T : ι → Rectangle) : (graph R T).ConnectedComponent → ℕ :=
  (Countable.exists_injective_nat _).choose

lemma num_injective : Function.Injective (num R T) :=
  (Countable.exists_injective_nat _).choose_spec

open scoped Classical in
/-- The number of the component of the vertex below `x`, for `x` an abscissa of the grid. Its
increment across the interval between two consecutive abscissae is the value there of Wagon's
step function `f`, so that sums of values of `f` along consecutive intervals telescope to
increments of `stepX`. -/
noncomputable def stepX (R : Rectangle) (T : ι → Rectangle) (x : ℝ) : ℝ :=
  if hx : x ∈ gridX R T then num R T ((graph R T).connectedComponentMk (bot hx)) else 0

open scoped Classical in
/-- The number of the component of the vertex level with `y`, for `y` an ordinate of the grid,
the counterpart of `stepX` for Wagon's step function `g`. -/
noncomputable def stepY (R : Rectangle) (T : ι → Rectangle) (y : ℝ) : ℝ :=
  if hy : y ∈ gridY R T then num R T ((graph R T).connectedComponentMk (left hy)) else 0

/-- Two abscissae of the grid have the same value of `stepX` exactly when their vertices are in the
same component of `Γ`. -/
lemma stepX_eq_stepX_iff {x x' : ℝ} (hx : x ∈ gridX R T) (hx' : x' ∈ gridX R T) :
    stepX R T x = stepX R T x' ↔ (graph R T).Reachable (bot hx) (bot hx') := by
  rw [stepX, stepX, dite_eq_left hx, dite_eq_left hx', Nat.cast_inj, num_injective.eq_iff,
    SimpleGraph.ConnectedComponent.eq]

/-- Two ordinates of the grid have the same value of `stepY` exactly when their vertices are in the
same component of `Γ`. -/
lemma stepY_eq_stepY_iff {y y' : ℝ} (hy : y ∈ gridY R T) (hy' : y' ∈ gridY R T) :
    stepY R T y = stepY R T y' ↔ (graph R T).Reachable (left hy) (left hy') := by
  rw [stepY, stepY, dite_eq_left hy, dite_eq_left hy', Nat.cast_inj, num_injective.eq_iff,
    SimpleGraph.ConnectedComponent.eq]

/-- **Over the grid rectangles in a tile, `f(x) g(y)` sums to `0`.** That sum is the product of
the increments of `stepX` across the width of the tile and of `stepY` across its height, and the
width of an H-tile is an edge of `Γ`, as is the height of a V-tile. -/
lemma fgArea_eq_zero (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) (i : ι) :
    fgArea (stepX R T) (stepY R T) (T i) = 0 := by
  rw [fgArea, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  refine (hsides i).imp (fun h ↦ ?_) fun h ↦ ?_
  · exact ((stepX_eq_stepX_iff _ _).mpr (adj_bot hT h).reachable).symm
  · exact ((stepY_eq_stepY_iff _ _).mpr (adj_left hT h).reachable).symm

/-- **The corner of `R` lies in the same component of `Γ` as one of its two neighbours.** Over the
whole grid `f(x) g(y)` sums to `0`, tile by tile, and that sum is the product of the increments of
`stepX` across the width of `R` and of `stepY` across its height (`sum_fgArea`). -/
theorem reachable (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) :
    (graph R T).Reachable (bot left_mem_gridX) (bot right_mem_gridX) ∨
      (graph R T).Reachable (left bot_mem_gridY) (left top_mem_gridY) := by
  have h := sum_fgArea hT (stepX R T) (stepY R T)
  rw [Finset.sum_eq_zero fun i _ ↦ fgArea_eq_zero hT hsides i, eq_comm, fgArea, mul_eq_zero,
    sub_eq_zero, sub_eq_zero] at h
  exact h.imp (fun h ↦ (stepX_eq_stepX_iff _ _).mp h.symm)
    fun h ↦ (stepY_eq_stepY_iff _ _).mp h.symm

end IntegerRectangle.StepFunction

open IntegerRectangle IntegerRectangle.StepFunction in
/-- **Step-function proof** (Hochster–Máté) of the integer-rectangle tiling theorem. The corner of
`R` lies in the same component of Hochster and Máté's graph as the corner at the other end of its
bottom edge or of its left edge (`reachable`), and a walk in the graph moves by a vector with
integer entries. -/
theorem IntegerRectangleTheorem_StepFunction : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  refine (reachable hT hsides).imp (fun h ↦ ?_) fun h ↦ ?_
  · exact Int.fract_eq_fract.mp (fract_eq_of_reachable h).1.symm
  · exact Int.fract_eq_fract.mp (fract_eq_of_reachable h).2.symm
