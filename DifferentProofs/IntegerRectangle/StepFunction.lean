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
* The components are numbered by an arbitrary injection into `ℕ` (`num`); `numX` gives each vertex
  on the bottom edge the number of its component, and `numY` each vertex on the left edge. Wagon's
  `f` is `stepX`, a combination of indicators of the intervals between consecutive vertices whose
  value on each is the increment of `numX` across it (`step_of_mem_Ioo`), and `g` is `stepY`.
* The value of `f(x) g(y)` on a grid rectangle is read at its centre (`mid`), and the grid
  refinement (`sum_grid_eq_sum_tiles`) regroups a sum over the grid rectangles tile by tile, each
  grid rectangle lying in exactly one tile (`Grid.cellTile_eq_iff`).

## Main result

- `IntegerRectangleTheorem_StepFunction`: Hochster and Máté's step-function proof of the
  integer-rectangle theorem.
-/

@[expose] public section

namespace IntegerRectangle.StepFunction

open Finset Grid

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-! ### Hochster and Máté's graph -/

/-- The vertices of Hochster and Máté's graph: the points of the bottom edge of `R` below a
vertical edge of the tiling, and the points of the left edge of `R` level with a horizontal one. -/
noncomputable def vertices (R : Rectangle) (T : ι → Rectangle) : Finset (ℝ × ℝ) :=
  gridX R T ×ˢ {R.y₀} ∪ {R.x₀} ×ˢ gridY R T

/-- The vertex of `Γ` on the bottom edge of `R` below the abscissa `x` of the grid. -/
def bot {x : ℝ} (hx : x ∈ gridX R T) : vertices R T :=
  ⟨(x, R.y₀), mem_union_left _ (mk_mem_product hx (mem_singleton_self _))⟩

/-- The vertex of `Γ` on the left edge of `R` level with the ordinate `y` of the grid. -/
def left {y : ℝ} (hy : y ∈ gridY R T) : vertices R T :=
  ⟨(R.x₀, y), mem_union_right _ (mk_mem_product (mem_singleton_self _) hy)⟩

/-- **Hochster and Máté's graph** `Γ`. Two vertices on the bottom edge of `R` are joined when an
H-tile spans the interval between them, and two vertices on its left edge when a V-tile does. -/
def graph (R : Rectangle) (T : ι → Rectangle) : SimpleGraph (vertices R T) :=
  SimpleGraph.fromRel fun p q ↦ ∃ i,
    ((T i).IsHTile ∧ p.1 = ((T i).x₀, R.y₀) ∧ q.1 = ((T i).x₁, R.y₀)) ∨
      ((T i).IsVTile ∧ p.1 = (R.x₀, (T i).y₀) ∧ q.1 = (R.x₀, (T i).y₁))

/-- The edge of `Γ` spanned by an H-tile. -/
private lemma adj_bot (hT : IsTiling R T) {i : ι} (h : (T i).IsHTile) :
    (graph R T).Adj (bot (tile_x₀_mem_gridX i)) (bot (tile_x₁_mem_gridX i)) :=
  ⟨ne_of_apply_ne (·.1.1) (hT.tile_x₀_lt_x₁ i).ne, .inl ⟨i, .inl ⟨h, rfl, rfl⟩⟩⟩

/-- The edge of `Γ` spanned by a V-tile. -/
private lemma adj_left (hT : IsTiling R T) {i : ι} (h : (T i).IsVTile) :
    (graph R T).Adj (left (tile_y₀_mem_gridY i)) (left (tile_y₁_mem_gridY i)) :=
  ⟨ne_of_apply_ne (·.1.2) (hT.tile_y₀_lt_y₁ i).ne, .inl ⟨i, .inr ⟨h, rfl, rfl⟩⟩⟩

/-- **The edges of `Γ` have integer length.** Joined vertices differ by a vector with integer
entries: an H-tile spans an interval of integer length along the bottom edge, and a V-tile along
the left edge. -/
lemma fract_eq_of_adj {p q : vertices R T} (h : (graph R T).Adj p q) :
    Int.fract p.1.1 = Int.fract q.1.1 ∧ Int.fract p.1.2 = Int.fract q.1.2 := by
  obtain ⟨-, ⟨i, ⟨hi, hp, hq⟩ | ⟨hi, hp, hq⟩⟩ | ⟨i, ⟨hi, hp, hq⟩ | ⟨hi, hp, hq⟩⟩⟩ := h <;>
    simp only [hp, hq, Int.fract_eq_fract.mpr hi, and_self]

/-- A walk in `Γ` moves by a vector with integer entries. -/
lemma fract_eq_of_reachable {p q : vertices R T} (h : (graph R T).Reachable p q) :
    Int.fract p.1.1 = Int.fract q.1.1 ∧ Int.fract p.1.2 = Int.fract q.1.2 :=
  ((SimpleGraph.reachable_iff_reflTransGen p q).mp h).rec ⟨rfl, rfl⟩ fun _ hbc ih ↦
    ⟨ih.1.trans (fract_eq_of_adj hbc).1, ih.2.trans (fract_eq_of_adj hbc).2⟩

/-! ### The step functions

Wagon's `f` takes, on the interval between two consecutive vertices of the x-axis, the number of
the component of the right one less that of the left one. It is an instance of `step s F`, the
step function on the gaps of a finite set `s` of reals whose value on the gap between two
consecutive elements is the increment of `F` across it; the values of `step s F` on consecutive
gaps add up to the increment of `F` across all of them (`sum_step`). -/

/-- **An arbitrary numbering of the components of `Γ` by distinct numbers.** -/
noncomputable def num (R : Rectangle) (T : ι → Rectangle) : (graph R T).ConnectedComponent → ℕ :=
  (Countable.exists_injective_nat _).choose

/-- Distinct components of `Γ` get distinct numbers. -/
private lemma num_injective : Function.Injective (num R T) :=
  (Countable.exists_injective_nat _).choose_spec

/-- The number of the component of the vertex below `x`, for `x` an abscissa of the grid. -/
noncomputable def numX (R : Rectangle) (T : ι → Rectangle) (x : ℝ) : ℝ :=
  if hx : x ∈ gridX R T then num R T ((graph R T).connectedComponentMk (bot hx)) else 0

/-- The number of the component of the vertex level with `y`, for `y` an ordinate of the grid. -/
noncomputable def numY (R : Rectangle) (T : ι → Rectangle) (y : ℝ) : ℝ :=
  if hy : y ∈ gridY R T then num R T ((graph R T).connectedComponentMk (left hy)) else 0

/-- Two abscissae of the grid have the same number exactly when their vertices are in the same
component of `Γ`. -/
private lemma numX_eq_numX_iff {x x' : ℝ} (hx : x ∈ gridX R T) (hx' : x' ∈ gridX R T) :
    numX R T x = numX R T x' ↔ (graph R T).Reachable (bot hx) (bot hx') := by
  rw [numX, numX, dite_eq_left hx, dite_eq_left hx', Nat.cast_inj, num_injective.eq_iff,
    SimpleGraph.ConnectedComponent.eq]

/-- Two ordinates of the grid have the same number exactly when their vertices are in the same
component of `Γ`. -/
private lemma numY_eq_numY_iff {y y' : ℝ} (hy : y ∈ gridY R T) (hy' : y' ∈ gridY R T) :
    numY R T y = numY R T y' ↔ (graph R T).Reachable (left hy) (left hy') := by
  rw [numY, numY, dite_eq_left hy, dite_eq_left hy', Nat.cast_inj, num_injective.eq_iff,
    SimpleGraph.ConnectedComponent.eq]

/-- The step function on the gaps of a finite set `s` of reals whose value on the open gap between
consecutive elements `s_j < s_{j+1}` is `F s_{j+1} - F s_j`, and `0` off the gaps. -/
noncomputable def step (s : Finset ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (s.sort.length - 1),
    (Set.Ioo (nth s j) (nth s (j + 1))).indicator (fun _ ↦ F (nth s (j + 1)) - F (nth s j)) x

/-- The step function is constant on each gap of `s`. -/
lemma step_of_mem_Ioo {s : Finset ℝ} (F : ℝ → ℝ) {j : ℕ} (hj : j + 1 < s.sort.length) {x : ℝ}
    (hx : x ∈ Set.Ioo (nth s j) (nth s (j + 1))) :
    step s F x = F (nth s (j + 1)) - F (nth s j) := by
  rw [step, sum_eq_single_of_mem j (mem_range.mpr (by lia)) fun k hk hkj ↦ ?_,
    Set.indicator_of_mem hx]
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨h₀, h₁⟩
  rcases hkj.lt_or_gt with h | h
  · exact (hx.1.trans h₁).not_ge (nth_le_nth h (Nat.lt_of_succ_lt hj))
  · exact (h₀.trans hx.2).not_ge (nth_le_nth h (by have := mem_range.mp hk; lia))

/-- The midpoint of the `j`-th gap of `s`. -/
noncomputable def mid (s : Finset ℝ) (j : ℕ) : ℝ := (nth s j + nth s (j + 1)) / 2

/-- The midpoint of a gap of `s` lies in it. -/
lemma mid_mem_Ioo {s : Finset ℝ} {j : ℕ} (hj : j + 1 < s.sort.length) :
    mid s j ∈ Set.Ioo (nth s j) (nth s (j + 1)) :=
  have h := nth_lt_nth (Nat.lt_succ_self j) hj
  ⟨left_lt_add_div_two.mpr h, add_div_two_lt_right.mpr h⟩

/-- **The values of the step function on consecutive gaps add up to the increment of `F` across
them.** -/
lemma sum_step {s : Finset ℝ} (F : ℝ → ℝ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ s.sort.length - 1) :
    ∑ j ∈ Ico a b, step s F (mid s j) = F (nth s b) - F (nth s a) :=
  (sum_congr rfl fun j hj ↦
    have h : j + 1 < s.sort.length := by have := (mem_Ico.mp hj).2; lia
    step_of_mem_Ioo F h (mid_mem_Ioo h)).trans (sum_Ico_sub (fun j ↦ F (nth s j)) hab)

/-- **Wagon's step function `f`** on the bottom edge of `R`: its value on the interval between
consecutive abscissae `x_j < x_{j+1}` of the grid is the number of the component of `x_{j+1}` less
that of `x_j`. -/
noncomputable def stepX (R : Rectangle) (T : ι → Rectangle) : ℝ → ℝ :=
  step (gridX R T) (numX R T)

/-- **Wagon's step function `g`** on the left edge of `R`, the counterpart of `f`. -/
noncomputable def stepY (R : Rectangle) (T : ι → Rectangle) : ℝ → ℝ :=
  step (gridY R T) (numY R T)

/-- **The values of `f` on the intervals spanned by an H-tile add up to `0`.** The sum telescopes
to the number of the component of the right end of the tile less that of its left end, and the two
ends are joined by an edge of `Γ`. -/
lemma sum_stepX_eq_zero (hT : IsTiling R T) {i : ι} (h : (T i).IsHTile) :
    ∑ j ∈ Ico (idxL R T i) (idxR R T i), stepX R T (mid (gridX R T) j) = 0 := by
  rw [stepX, sum_step _ (idxL_le_idxR i) (Nat.le_sub_one_of_lt (idxR_lt i)), nth_idxR, nth_idxL,
    sub_eq_zero]
  exact (numX_eq_numX_iff _ _).mpr (adj_bot hT h).symm.reachable

/-- **The values of `g` on the intervals spanned by a V-tile add up to `0`.** -/
lemma sum_stepY_eq_zero (hT : IsTiling R T) {i : ι} (h : (T i).IsVTile) :
    ∑ k ∈ Ico (idxB R T i) (idxT R T i), stepY R T (mid (gridY R T) k) = 0 := by
  rw [stepY, sum_step _ (idxB_le_idxT i) (Nat.le_sub_one_of_lt (idxT_lt i)), nth_idxT, nth_idxB,
    sub_eq_zero]
  exact (numY_eq_numY_iff _ _).mpr (adj_left hT h).symm.reachable

/-! ### The grid refinement

Refine the tiling into its grid. A sum over the grid rectangles regroups tile by tile
(`sum_grid_eq_sum_tiles`), and the values of `f(x) g(y)` on the grid rectangles in a tile add up to
`0` (`sum_tile_eq_zero`). So their sum over all the grid rectangles is `0`, and it is the product
of the sums of `f` and of `g` along the two sides of `R` (`reachable`). -/

/-- **The grid refinement.** Every grid rectangle lies in exactly one tile, and the grid rectangles
in a tile form the product of its two index intervals (`Grid.filter_cellTile_eq`), so a sum over
the grid rectangles is the sum, over the tiles, of the sums over the grid rectangles in each. -/
theorem sum_grid_eq_sum_tiles (hT : IsTiling R T) (v : ℕ × ℕ → ℝ) :
    ∑ p ∈ range ((gridX R T).sort.length - 1) ×ˢ range ((gridY R T).sort.length - 1), v p =
      ∑ i, ∑ p ∈ Ico (idxL R T i) (idxR R T i) ×ˢ Ico (idxB R T i) (idxT R T i), v p := by
  classical
  rw [← sum_fiberwise _ (cellTile hT)]
  exact sum_congr rfl fun i _ ↦ by rw [filter_cellTile_eq hT i]

/-- **Over the grid rectangles in a tile, the values of `f(x) g(y)` add up to `0`**, being the
product of the sums of the values of `f` along the width of the tile and of `g` along its height,
one of which vanishes. -/
lemma sum_tile_eq_zero (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) (i : ι) :
    ∑ p ∈ Ico (idxL R T i) (idxR R T i) ×ˢ Ico (idxB R T i) (idxT R T i),
      stepX R T (mid (gridX R T) p.1) * stepY R T (mid (gridY R T) p.2) = 0 := by
  simp only [sum_product, ← sum_mul_sum]
  exact mul_eq_zero.mpr ((hsides i).imp (sum_stepX_eq_zero hT) (sum_stepY_eq_zero hT))

/-- **The corner of `R` lies in the same component of `Γ` as one of its two neighbours.** Over the
whole grid the values of `f(x) g(y)` add up to `0`, tile by tile, and their sum is the product of
the sum of the values of `f` along the bottom edge of `R`, the number of the component of its
lower-right corner less that of its lower-left one, with the corresponding sum of `g`. -/
theorem reachable (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) :
    (graph R T).Reachable (bot left_mem_gridX) (bot right_mem_gridX) ∨
      (graph R T).Reachable (left bot_mem_gridY) (left top_mem_gridY) := by
  have h := (sum_grid_eq_sum_tiles hT fun p ↦
    stepX R T (mid (gridX R T) p.1) * stepY R T (mid (gridY R T) p.2)).trans <|
      Fintype.sum_eq_zero _ (sum_tile_eq_zero hT hsides)
  simp only [sum_product, ← sum_mul_sum, range_eq_Ico, stepX, stepY, sum_step _ zero_le le_rfl,
    nth_gridX_zero hT, nth_gridX_last hT, nth_gridY_zero hT, nth_gridY_last hT] at h
  exact (mul_eq_zero.mp h).imp (fun h ↦ (numX_eq_numX_iff _ _).mp (sub_eq_zero.mp h).symm)
    fun h ↦ (numY_eq_numY_iff _ _).mp (sub_eq_zero.mp h).symm

end IntegerRectangle.StepFunction

open IntegerRectangle IntegerRectangle.StepFunction in
/-- **Step-function proof** (Hochster–Máté) of the integer-rectangle tiling theorem. The corner of
`R` lies in the same component of Hochster and Máté's graph as the corner at the other end of its
bottom edge or of its left edge (`reachable`), and a walk in the graph moves by a vector with
integer entries. -/
theorem IntegerRectangleTheorem_StepFunction : IntegerRectangleTheorem := fun _ _ hT hsides ↦
  (reachable hT hsides).imp (fun h ↦ Int.fract_eq_fract.mp (fract_eq_of_reachable h).1.symm)
    fun h ↦ Int.fract_eq_fract.mp (fract_eq_of_reachable h).2.symm
