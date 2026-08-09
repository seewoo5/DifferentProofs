module

public import DifferentProofs.IntegerRectangle.GridRefinement
public import Mathlib.Data.ZMod.Basic

/-!
# Counting the corners of the tiles of a tiling

Two of Wagon's proofs — the Eulerian path of Paterson and its bipartite-graph variation — count
incidences between the tiles of a tiling and a set of points, each tile being joined to the points
that are corners of it. This file is what they share: the corner count and its two properties.

The number of corners a rectangle has at a point, the four corners being counted with multiplicity
so that degenerate rectangles need no separate treatment, is `cornerCount`. Wagon reads its
behaviour off the local picture — a point other than a corner of `R` is a corner of `2` or `4`
tiles — which is a statement about how tiles fit together around a point. Only the parity is ever
used, and that is `IsTiling.sum_cornerCount_mod_two`:

> at every point of the plane the tiles have, in total, as many corners as `R` does, mod `2`,

which comes from additivity of the fg-area (`IsTiling.sum_fgArea`) applied to the indicator
functions of the two coordinate lines through the point, with no local analysis at all. For those
the fg-area of a rectangle is its corner count at the point with the left and bottom edges counted
negatively (`cornerSign`), which is additive over a tiling for free and which mod `2` is the corner
count itself.

Summing the corner parity over a finite set `Z` of points gives the double count
`IsTiling.even_sum_cornerCount`: if every tile has an even number of corners in `Z`, then so has
`R`. The number of corners a rectangle has in `Z` is read off by `sum_cornerCount_eq`. The two
proofs differ only in the set `Z` they use: a connected component of the graph of designated tile
sides for the seventh proof, a lattice grid for the eighth.
-/

@[expose] public section

namespace IntegerRectangle

/-! ### Counting corners at a point -/

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

/-- The *signed* corner count of `S` at `(u, v)`: the fg-area of `S` for the indicator functions
of the lines `x = u` and `y = v` (`fgArea_indicator`). Reversing the sign at the lower edges is
what makes it additive over a tiling, and mod `2` it still counts the corners
(`cornerSign_cast`). -/
private noncomputable def cornerSign (S : Rectangle) (u v : ℝ) : ℤ :=
  ((if S.x₁ = u then 1 else 0) - (if S.x₀ = u then 1 else 0)) *
    ((if S.y₁ = v then 1 else 0) - (if S.y₀ = v then 1 else 0))

private lemma fgArea_indicator (S : Rectangle) (u v : ℝ) :
    fgArea (fun x ↦ if x = u then 1 else 0) (fun y ↦ if y = v then 1 else 0) S
      = (cornerSign S u v : ℝ) := by
  simp [fgArea, cornerSign]

private lemma cornerSign_cast (S : Rectangle) (u v : ℝ) :
    ((cornerSign S u v : ℤ) : ZMod 2) = (cornerCount S u v : ℕ) := by
  simp only [cornerSign, cornerCount, xCount, yCount]
  split_ifs <;> decide

/-! ### Corner parity -/

variable {ι : Type*} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **Corner parity of a tiling.** At every point of the plane, the tiles of a tiling have in
total a number of corners congruent mod `2` to the number of corners of the tiled rectangle
there. Away from the corners of `R` it says that a point is a corner of evenly many tiles, which
is Wagon's "`2` or `4` tiles"; at a corner of `R` the count is odd.

The signed corner count is the fg-area for the pair of indicator functions of the coordinate lines
through the point, hence additive over the tiling; forgetting the signs is passing to `ZMod 2`. -/
theorem IsTiling.sum_cornerCount_mod_two (hT : IsTiling R T) (u v : ℝ) :
    ((∑ i, cornerCount (T i) u v : ℕ) : ZMod 2) = (cornerCount R u v : ZMod 2) := by
  have h := hT.sum_fgArea (fun x ↦ if x = u then 1 else 0) fun y ↦ if y = v then 1 else 0
  simp only [fgArea_indicator] at h
  have key : ∑ i, cornerSign (T i) u v = cornerSign R u v := by exact_mod_cast h
  simpa [← cornerSign_cast] using congrArg (fun m : ℤ ↦ (m : ZMod 2)) key

/-! ### The double count -/

/-- **The corners of a rectangle in a finite set of points**, counted with multiplicity. -/
theorem sum_cornerCount_eq (S : Rectangle) (Z : Finset (ℝ × ℝ)) :
    ∑ z ∈ Z, cornerCount S z.1 z.2 =
      ((if (S.x₀, S.y₀) ∈ Z then 1 else 0) + (if (S.x₁, S.y₀) ∈ Z then 1 else 0)) +
        ((if (S.x₀, S.y₁) ∈ Z then 1 else 0) + (if (S.x₁, S.y₁) ∈ Z then 1 else 0)) := by
  simp only [cornerCount, xCount, yCount, add_mul, mul_add, ite_zero_mul_ite_zero, mul_one,
    ← Prod.mk.injEq, Prod.mk.eta, Finset.sum_add_distrib, Finset.sum_ite_eq]

/-- **A rectangle with an integer side has `0`, `2` or `4` corners in `Z`.** What is used of the
integer side is that the two ends of each of the two sides in that direction are together in `Z`
or together out of it. -/
theorem even_sum_cornerCount_of_sides (S : Rectangle) {Z : Finset (ℝ × ℝ)}
    (h : (((S.x₀, S.y₀) ∈ Z ↔ (S.x₁, S.y₀) ∈ Z) ∧ ((S.x₀, S.y₁) ∈ Z ↔ (S.x₁, S.y₁) ∈ Z)) ∨
      (((S.x₀, S.y₀) ∈ Z ↔ (S.x₀, S.y₁) ∈ Z) ∧ ((S.x₁, S.y₀) ∈ Z ↔ (S.x₁, S.y₁) ∈ Z))) :
    Even (∑ z ∈ Z, cornerCount S z.1 z.2) := by
  rw [sum_cornerCount_eq]
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h <;> simp only [h₁, h₂] <;> split_ifs <;> decide

/-- **The double count.** Let `T` tile `R` and let `Z` be a finite set of points such that every
tile has an even number of corners in `Z`. Then so has `R`.

Count the incidences between the points of `Z` and the tiles having them as a corner: tile by tile
the total is even by hypothesis, and point by point the corner parity
(`IsTiling.sum_cornerCount_mod_two`) replaces each count by the corresponding count for `R`. -/
theorem IsTiling.even_sum_cornerCount (hT : IsTiling R T) {Z : Finset (ℝ × ℝ)}
    (h : ∀ i, Even (∑ z ∈ Z, cornerCount (T i) z.1 z.2)) :
    Even (∑ z ∈ Z, cornerCount R z.1 z.2) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  push_cast
  calc ∑ z ∈ Z, (cornerCount R z.1 z.2 : ZMod 2)
      = ∑ z ∈ Z, ((∑ i, cornerCount (T i) z.1 z.2 : ℕ) : ZMod 2) :=
        Finset.sum_congr rfl fun z _ ↦ (hT.sum_cornerCount_mod_two z.1 z.2).symm
    _ = ∑ i, ((∑ z ∈ Z, cornerCount (T i) z.1 z.2 : ℕ) : ZMod 2) := by
        push_cast; exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun i _ ↦ ZMod.natCast_eq_zero_iff_even.mpr (h i)

end IntegerRectangle
