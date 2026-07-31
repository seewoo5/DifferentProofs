module

public import DifferentProofs.IntegerRectangle.GridRefinement
public import DifferentProofsForMathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

/-!
# The integer-rectangle theorem via a bipartite graph

Wagon's eighth proof. Place `R` in standard position and form the bipartite graph joining each
lattice point of `ℤ × ℤ` to the tiles having it as a corner. Counting the edges from the tile
side, a tile with an integer side has `0`, `2` or `4` lattice corners, so their total is even.
Counting from the lattice side, the origin is a corner of exactly one tile, while a lattice point
that is not a corner of `R` is a corner of `2` or `4` tiles — so a further corner of `R` must be
a lattice point too, and that is an integer side.

Here `R` is not put in standard position; instead the lattice used is the one through the
lower-left corner of `R`, and rather than the tile corners we sum over *all* its points in `R`
(`latticeIcc`), which changes nothing since a non-corner contributes `0` on both sides. Corners
are counted with multiplicity (`cornerCount`), so degenerate tiles need no separate treatment.

Wagon's local claim — a lattice point is a corner of `2` or `4` tiles unless it is a corner of
`R` — is what needs care: it is a statement about how tiles fit together around a point. We do
not prove it in that form. Instead `sum_cornerCount_mod_two` gives the exact parity statement it
is used for,

> at every point of the plane the tiles have, in total, as many corners as `R` does, mod `2`,

and derives it from additivity of the f-area (`IsTiling.sum_fgArea`) applied to the indicator
functions of the two coordinate lines through the point. For those the f-area of a rectangle is
its corner count at the point with the left and bottom edges counted negatively (`cornerSign`),
which is additive over a tiling for free and which mod `2` is the corner count itself.
-/

@[expose] public section

namespace IntegerRectangle.BipartiteGraph

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

/-- The *signed* corner count of `S` at `(u, v)`: the f-area of `S` for the indicator functions
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

The signed corner count is the f-area for the pair of indicator functions of the coordinate lines
through the point, hence additive over the tiling; forgetting the signs is passing to `ZMod 2`. -/
theorem sum_cornerCount_mod_two (hT : IsTiling R T) (u v : ℝ) :
    ((∑ i, cornerCount (T i) u v : ℕ) : ZMod 2) = (cornerCount R u v : ZMod 2) := by
  have h := hT.sum_fgArea (fun x ↦ if x = u then 1 else 0) fun y ↦ if y = v then 1 else 0
  simp only [fgArea_indicator] at h
  have key : ∑ i, cornerSign (T i) u v = cornerSign R u v := by exact_mod_cast h
  simpa [← cornerSign_cast] using congrArg (fun m : ℤ ↦ (m : ZMod 2)) key

/-! ### The double count -/

private lemma sum_xCount (S : Rectangle) (X : Finset ℝ) :
    ∑ u ∈ X, xCount S u = (if S.x₀ ∈ X then 1 else 0) + (if S.x₁ ∈ X then 1 else 0) := by
  simp [xCount, Finset.sum_add_distrib]

private lemma sum_yCount (S : Rectangle) (Y : Finset ℝ) :
    ∑ v ∈ Y, yCount S v = (if S.y₀ ∈ Y then 1 else 0) + (if S.y₁ ∈ Y then 1 else 0) := by
  simp [yCount, Finset.sum_add_distrib]

/-- Two equivalent conditions contribute an even number of edges. -/
private lemma even_ite_add_ite {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    Even ((if p then 1 else 0) + (if q then 1 else 0) : ℕ) := by
  simp only [h]; exact ⟨_, rfl⟩

/-- **The degree of a rectangle in the incidence graph.** The number of corners of `S` lying on
the grid `X × Y` is the number of its vertical edges over `X` times the number of its horizontal
edges over `Y`. -/
private lemma sum_cornerCount_product (S : Rectangle) (X Y : Finset ℝ) :
    ∑ z ∈ X ×ˢ Y, cornerCount S z.1 z.2 =
      ((if S.x₀ ∈ X then 1 else 0) + (if S.x₁ ∈ X then 1 else 0)) *
        ((if S.y₀ ∈ Y then 1 else 0) + (if S.y₁ ∈ Y then 1 else 0)) := by
  simp only [cornerCount, Finset.sum_product_mul, sum_xCount, sum_yCount]

/-- **Counting the edges of the bipartite graph.** Let `X` and `Y` be finite sets of abscissae
and ordinates, and suppose each tile has either both or neither of its vertical edges over `X`,
or both or neither of its horizontal edges over `Y`. Then the tiled rectangle has an even number
of corners on the grid `X × Y`.

This is the double count: the edges of the graph joining the grid points to the tiles having them
as a corner are counted tile by tile — each tile contributes an even number by hypothesis — and
then point by point, where corner parity (`sum_cornerCount_mod_two`) replaces each count by the
corresponding count for `R`. -/
theorem even_sum_cornerCount (hT : IsTiling R T) {X Y : Finset ℝ}
    (h : ∀ i, ((T i).x₀ ∈ X ↔ (T i).x₁ ∈ X) ∨ ((T i).y₀ ∈ Y ↔ (T i).y₁ ∈ Y)) :
    Even (∑ z ∈ X ×ˢ Y, cornerCount R z.1 z.2) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  push_cast
  calc ∑ z ∈ X ×ˢ Y, (cornerCount R z.1 z.2 : ZMod 2)
      = ∑ z ∈ X ×ˢ Y, ((∑ i, cornerCount (T i) z.1 z.2 : ℕ) : ZMod 2) :=
        Finset.sum_congr rfl fun z _ ↦ (sum_cornerCount_mod_two hT z.1 z.2).symm
    _ = ∑ i, ((∑ z ∈ X ×ˢ Y, cornerCount (T i) z.1 z.2 : ℕ) : ZMod 2) := by
        push_cast; exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun i _ ↦ ZMod.natCast_eq_zero_iff_even.mpr <| by
        rw [sum_cornerCount_product]
        exact (h i).elim (fun hi ↦ (even_ite_add_ite hi).mul_right _)
          fun hi ↦ (even_ite_add_ite hi).mul_left _

/-! ### The lattice through a corner of the tiled rectangle -/

/-- The points of the lattice `a + ℤ` lying in `[a, b]`. -/
noncomputable def latticeIcc (a b : ℝ) : Finset ℝ := (Finset.Icc 0 ⌊b - a⌋).image fun n : ℤ ↦ a + n

/-- A point of `[a, b]` belongs to `latticeIcc a b` exactly when it sits on the lattice `a + ℤ`. -/
private lemma mem_latticeIcc {a b u : ℝ} (h₀ : a ≤ u) (h₁ : u ≤ b) :
    u ∈ latticeIcc a b ↔ ∃ n : ℤ, u - a = n := by
  simp only [latticeIcc, Finset.mem_image, Finset.mem_Icc]
  refine ⟨fun ⟨n, _, hn⟩ ↦ ⟨n, by rw [← hn]; ring⟩, fun ⟨n, hn⟩ ↦ ⟨n, ⟨?_, ?_⟩, by linarith⟩⟩
  · exact_mod_cast hn ▸ sub_nonneg.mpr h₀
  · exact Int.le_floor.mpr (by rw [← hn]; linarith)

/-- Two points of `[a, b]` an integer apart lie on the lattice `a + ℤ` together. -/
private lemma mem_latticeIcc_iff_mem_latticeIcc {a b u w : ℝ} (hu : u ∈ Set.Icc a b)
    (hw : w ∈ Set.Icc a b) {n : ℤ} (hn : w - u = n) :
    u ∈ latticeIcc a b ↔ w ∈ latticeIcc a b := by
  rw [mem_latticeIcc hu.1 hu.2, mem_latticeIcc hw.1 hw.2]
  exact ⟨fun ⟨m, hm⟩ ↦ ⟨m + n, by push_cast; linarith⟩,
    fun ⟨m, hm⟩ ↦ ⟨m - n, by push_cast; linarith⟩⟩

/-! ### The proof -/

/-- **Bipartite-graph proof** (Wagon's variation on Paterson's Eulerian-path proof) of the
integer-rectangle tiling theorem. Take for `X` and `Y` the lattices through the lower-left corner
of `R`, so that a tile with an integer side has both or neither of its edges in that direction on
the lattice, and the double count (`even_sum_cornerCount`) applies: `R` has an even number of
corners on the lattice. Its lower-left corner is one of them, so if neither side of `R` were an
integer it would be the only one. -/
theorem IntegerRectangleTheorem_BipartiteGraph : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  by_contra hcon
  rw [Rectangle.HasIntegerSide, not_or] at hcon
  have hlat : ∀ i, ((T i).x₀ ∈ latticeIcc R.x₀ R.x₁ ↔ (T i).x₁ ∈ latticeIcc R.x₀ R.x₁) ∨
      ((T i).y₀ ∈ latticeIcc R.y₀ R.y₁ ↔ (T i).y₁ ∈ latticeIcc R.y₀ R.y₁) :=
    fun i ↦ (hsides i).imp
      (fun ⟨n, hn⟩ ↦ mem_latticeIcc_iff_mem_latticeIcc
        ⟨hT.le_tile_x₀ i, (T i).hx.trans (hT.tile_x₁_le i)⟩
        ⟨(hT.le_tile_x₀ i).trans (T i).hx, hT.tile_x₁_le i⟩ hn)
      fun ⟨n, hn⟩ ↦ mem_latticeIcc_iff_mem_latticeIcc
        ⟨hT.le_tile_y₀ i, (T i).hy.trans (hT.tile_y₁_le i)⟩
        ⟨(hT.le_tile_y₀ i).trans (T i).hy, hT.tile_y₁_le i⟩ hn
  have key := even_sum_cornerCount hT hlat
  rw [sum_cornerCount_product, if_pos ((mem_latticeIcc le_rfl R.hx).mpr ⟨0, by simp⟩),
    if_neg fun hx ↦ hcon.1 ((mem_latticeIcc R.hx le_rfl).mp hx),
    if_pos ((mem_latticeIcc le_rfl R.hy).mpr ⟨0, by simp⟩),
    if_neg fun hy ↦ hcon.2 ((mem_latticeIcc R.hy le_rfl).mp hy)] at key
  simp at key

end IntegerRectangle.BipartiteGraph
