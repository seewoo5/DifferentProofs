module

public import DifferentProofs.IntegerRectangle.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The grid refinement of a tiling, and additivity of the f-area

Wagon's step-function proof rides on an additivity lemma stated for an *arbitrary* pair of
functions `f, g : ℝ → ℝ`, with no regularity whatsoever. Call

```
fgArea f g S = (f S.x₁ - f S.x₀) · (g S.y₁ - g S.y₀)
```

the *f-area* of a rectangle. Then the f-area is additive over a tiling: `IsTiling.sum_fgArea`.

The proof is Wagon's. The tile edges form a graph; extending its edges across `R` cuts `R` into a
grid, whose vertical lines carry the finitely many x-coordinates of vertical tile edges
(`gridX`) and whose horizontal lines carry the y-coordinates of horizontal ones (`gridY`). No
grid coordinate lies strictly inside an open grid cell, so each open cell clears the edges of any
tile meeting its centre and lies inside a unique tile (`cellTile`); conversely the cells assigned
to a tile fill out the product of two index intervals (`cellTile_eq_iff`), because the tile's own
edges are grid lines. Summing the f-area of the cells therefore counts every cell exactly once,
tile by tile, and over a product of index intervals the sum telescopes in both coordinates —
giving the tile's f-area, and, over the whole grid, the f-area of `R`.

The sorting of the edge coordinates is handled by `Finset.sort`; the little `nth` layer below
turns the sorted list into a total function `ℕ → ℝ`, so that all sums range over `Finset.range`
and `Finset.Ico` in `ℕ` with no dependent index bookkeeping.
-/

@[expose] public section

open Finset Set

namespace IntegerRectangle

/-- The *f-area* of a rectangle in the sense of Wagon — with a separate function per axis, whence
the name: the increment of `f` across the width times the increment of `g` across the height. For
`f = g = id` it is the usual area; for `f = g = Int.fract` it is the quantity driving the
step-function proof. Its virtue is additivity over a tiling (`IsTiling.sum_fgArea`) for
completely arbitrary `f` and `g`. -/
noncomputable def fgArea (f g : ℝ → ℝ) (S : Rectangle) : ℝ :=
  (f S.x₁ - f S.x₀) * (g S.y₁ - g S.y₀)

namespace GridRefinement

/-! ### The sorted enumeration of a finite set of reals -/

/-- The `j`-th element of `s` in increasing order, as a total function of `j` (junk value `0` out
of range). -/
private noncomputable def nth (s : Finset ℝ) (j : ℕ) : ℝ := s.sort.getD j 0

private lemma nth_eq_getElem {s : Finset ℝ} {j : ℕ} (hj : j < s.sort.length) :
    nth s j = s.sort[j] :=
  List.getD_eq_getElem _ _ hj

private lemma nth_lt_nth {s : Finset ℝ} {j k : ℕ} (hjk : j < k) (hk : k < s.sort.length) :
    nth s j < nth s k := by
  rw [nth_eq_getElem (hjk.trans hk), nth_eq_getElem hk]
  exact (s.sortedLT_sort).getElem_lt_getElem_of_lt hjk

private lemma nth_le_nth {s : Finset ℝ} {j k : ℕ} (hjk : j ≤ k) (hk : k < s.sort.length) :
    nth s j ≤ nth s k := by
  rcases hjk.lt_or_eq with h | h
  · exact (nth_lt_nth h hk).le
  · rw [h]

private lemma lt_of_nth_lt_nth {s : Finset ℝ} {j k : ℕ} (hj : j < s.sort.length)
    (h : nth s j < nth s k) : j < k := by
  by_contra hjk
  exact absurd (nth_le_nth (not_lt.mp hjk) hj) (not_le.mpr h)

private lemma le_of_nth_le_nth {s : Finset ℝ} {j k : ℕ} (hj : j < s.sort.length)
    (h : nth s j ≤ nth s k) : j ≤ k := by
  by_contra hjk
  exact absurd (nth_lt_nth (not_le.mp hjk) hj) (not_lt.mpr h)

private lemma nth_mem {s : Finset ℝ} {j : ℕ} (hj : j < s.sort.length) : nth s j ∈ s := by
  rw [nth_eq_getElem hj]
  exact (s.mem_sort (· ≤ ·)).mp (List.getElem_mem _)

private lemma exists_nth_eq {s : Finset ℝ} {a : ℝ} (ha : a ∈ s) :
    ∃ j, ∃ _ : j < s.sort.length, nth s j = a := by
  obtain ⟨j, hj, h⟩ := List.mem_iff_getElem.mp ((s.mem_sort (· ≤ ·)).mpr ha)
  exact ⟨j, hj, (nth_eq_getElem hj).trans h⟩

private lemma nth_zero {s : Finset ℝ} (hs : s.Nonempty) : nth s 0 = s.min' hs := by
  have h : 0 < s.sort.length := by rw [Finset.length_sort]; exact card_pos.mpr hs
  rw [nth_eq_getElem h]
  exact Finset.sorted_zero_eq_min'

private lemma nth_last {s : Finset ℝ} (hs : s.Nonempty) :
    nth s (s.sort.length - 1) = s.max' hs := by
  have h : 0 < s.sort.length := by rw [Finset.length_sort]; exact card_pos.mpr hs
  rw [nth_eq_getElem (Nat.sub_lt h one_pos)]
  exact s.sorted_last_eq_max'_aux (Nat.sub_lt h one_pos) hs

/-- No element of `s` lies strictly between two consecutive elements of `s`. -/
private lemma notMem_Ioo_nth {s : Finset ℝ} {a : ℝ} (ha : a ∈ s) {j : ℕ}
    (hj : j + 1 < s.sort.length) : a ∉ Ioo (nth s j) (nth s (j + 1)) := by
  rintro ⟨h₀, h₁⟩
  obtain ⟨k, hk, rfl⟩ := exists_nth_eq ha
  have := lt_of_nth_lt_nth (Nat.lt_of_succ_lt hj) h₀
  have := lt_of_nth_lt_nth hk h₁
  omega

/-- An interval `[a, b]` with endpoints in `s` whose interior contains a point of the `j`-th open
gap of `s` sandwiches that gap: `a` is at most the gap's left end, `b` at least its right end. -/
private lemma nth_sandwich {s : Finset ℝ} {a b z : ℝ} (ha : a ∈ s) (hb : b ∈ s) {j : ℕ}
    (hj : j + 1 < s.sort.length) (haz : a ≤ z) (hzb : z ≤ b) (hz₀ : nth s j < z)
    (hz₁ : z < nth s (j + 1)) : a ≤ nth s j ∧ nth s (j + 1) ≤ b :=
  ⟨not_lt.mp fun h ↦ notMem_Ioo_nth ha hj ⟨h, haz.trans_lt hz₁⟩,
    not_lt.mp fun h ↦ notMem_Ioo_nth hb hj ⟨hz₀.trans_le hzb, h⟩⟩

/-- Telescoping a sum of consecutive differences along `Ico m n`. -/
private lemma sum_Ico_sub {m n : ℕ} (F : ℕ → ℝ) (h : m ≤ n) :
    ∑ j ∈ Finset.Ico m n, (F (j + 1) - F j) = F n - F m := by
  rw [Finset.sum_Ico_eq_sub _ h, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

/-- Double telescoping: summing the product of consecutive differences over a product of index
intervals gives the product of the end differences. -/
private lemma sum_product_sub (F G : ℕ → ℝ) {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∑ p ∈ Finset.Ico a b ×ˢ Finset.Ico c d,
      (F (p.1 + 1) - F p.1) * (G (p.2 + 1) - G p.2) = (F b - F a) * (G d - G c) :=
  ((Finset.sum_product _ _ _).trans
    (Finset.sum_mul_sum (Finset.Ico a b) (Finset.Ico c d)
      (fun j ↦ F (j + 1) - F j) (fun k ↦ G (k + 1) - G k)).symm).trans
    (by rw [sum_Ico_sub F hab, sum_Ico_sub G hcd])

/-! ### The grid of a tiling -/

variable {ι : Type*} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

open scoped Classical in
/-- The x-coordinates of the vertical lines of the grid: the vertical edges of the tiles and of
the tiled rectangle. -/
private noncomputable def gridX (R : Rectangle) (T : ι → Rectangle) : Finset ℝ :=
  insert R.x₀ (insert R.x₁ ((univ.image fun i ↦ (T i).x₀) ∪ univ.image fun i ↦ (T i).x₁))

open scoped Classical in
/-- The y-coordinates of the horizontal lines of the grid. -/
private noncomputable def gridY (R : Rectangle) (T : ι → Rectangle) : Finset ℝ :=
  insert R.y₀ (insert R.y₁ ((univ.image fun i ↦ (T i).y₀) ∪ univ.image fun i ↦ (T i).y₁))

private lemma left_mem_gridX : R.x₀ ∈ gridX R T := by simp [gridX]

private lemma right_mem_gridX : R.x₁ ∈ gridX R T := by simp [gridX]

private lemma bot_mem_gridY : R.y₀ ∈ gridY R T := by simp [gridY]

private lemma top_mem_gridY : R.y₁ ∈ gridY R T := by simp [gridY]

private lemma tile_x₀_mem_gridX (i : ι) : (T i).x₀ ∈ gridX R T := by simp [gridX]

private lemma tile_x₁_mem_gridX (i : ι) : (T i).x₁ ∈ gridX R T := by simp [gridX]

private lemma tile_y₀_mem_gridY (i : ι) : (T i).y₀ ∈ gridY R T := by simp [gridY]

private lemma tile_y₁_mem_gridY (i : ι) : (T i).y₁ ∈ gridY R T := by simp [gridY]

/-- Every grid x-coordinate lies between the left and right edges of the tiled rectangle. -/
private lemma gridX_mem_Icc (hT : IsTiling R T) {a : ℝ} (ha : a ∈ gridX R T) :
    R.x₀ ≤ a ∧ a ≤ R.x₁ := by
  have ha' : a = R.x₀ ∨ a = R.x₁ ∨ (∃ i, (T i).x₀ = a) ∨ ∃ i, (T i).x₁ = a := by
    simpa [gridX, or_assoc, eq_comm] using ha
  obtain rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ := ha'
  · exact ⟨le_rfl, R.hx⟩
  · exact ⟨R.hx, le_rfl⟩
  · exact ⟨hT.le_tile_x₀ i, (T i).hx.trans (hT.tile_x₁_le i)⟩
  · exact ⟨(hT.le_tile_x₀ i).trans (T i).hx, hT.tile_x₁_le i⟩

/-- Every grid y-coordinate lies between the bottom and the top of the tiled rectangle. -/
private lemma gridY_mem_Icc (hT : IsTiling R T) {a : ℝ} (ha : a ∈ gridY R T) :
    R.y₀ ≤ a ∧ a ≤ R.y₁ := by
  have ha' : a = R.y₀ ∨ a = R.y₁ ∨ (∃ i, (T i).y₀ = a) ∨ ∃ i, (T i).y₁ = a := by
    simpa [gridY, or_assoc, eq_comm] using ha
  obtain rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ := ha'
  · exact ⟨le_rfl, R.hy⟩
  · exact ⟨R.hy, le_rfl⟩
  · exact ⟨hT.le_tile_y₀ i, (T i).hy.trans (hT.tile_y₁_le i)⟩
  · exact ⟨(hT.le_tile_y₀ i).trans (T i).hy, hT.tile_y₁_le i⟩

private lemma nth_gridX_zero (hT : IsTiling R T) : nth (gridX R T) 0 = R.x₀ :=
  (nth_zero ⟨R.x₀, left_mem_gridX⟩).trans <| le_antisymm
    (Finset.min'_le _ _ left_mem_gridX)
    (Finset.le_min' _ _ _ fun _ ha ↦ (gridX_mem_Icc hT ha).1)

private lemma nth_gridX_last (hT : IsTiling R T) :
    nth (gridX R T) ((gridX R T).sort.length - 1) = R.x₁ :=
  (nth_last ⟨R.x₁, right_mem_gridX⟩).trans <| le_antisymm
    (Finset.max'_le _ _ _ fun _ ha ↦ (gridX_mem_Icc hT ha).2)
    (Finset.le_max' _ _ right_mem_gridX)

private lemma nth_gridY_zero (hT : IsTiling R T) : nth (gridY R T) 0 = R.y₀ :=
  (nth_zero ⟨R.y₀, bot_mem_gridY⟩).trans <| le_antisymm
    (Finset.min'_le _ _ bot_mem_gridY)
    (Finset.le_min' _ _ _ fun _ ha ↦ (gridY_mem_Icc hT ha).1)

private lemma nth_gridY_last (hT : IsTiling R T) :
    nth (gridY R T) ((gridY R T).sort.length - 1) = R.y₁ :=
  (nth_last ⟨R.y₁, top_mem_gridY⟩).trans <| le_antisymm
    (Finset.max'_le _ _ _ fun _ ha ↦ (gridY_mem_Icc hT ha).2)
    (Finset.le_max' _ _ top_mem_gridY)

/-! ### Each open grid cell lies inside a unique tile -/

/-- The open cell of the grid with lower-left index `(j, k)`. -/
private def openCell (R : Rectangle) (T : ι → Rectangle) (j k : ℕ) : Set (ℝ × ℝ) :=
  Ioo (nth (gridX R T) j) (nth (gridX R T) (j + 1)) ×ˢ
    Ioo (nth (gridY R T) k) (nth (gridY R T) (k + 1))

/-- **Every open grid cell lies in the interior of exactly one tile.** The cell's centre is
covered by some tile; the tile's edges are grid coordinates and no grid coordinate lies strictly
inside the cell, so the tile's edges clear the whole cell. Uniqueness is disjointness of
interiors. -/
private lemma existsUnique_openCell_subset (hT : IsTiling R T) {j k : ℕ}
    (hj : j + 1 < (gridX R T).sort.length) (hk : k + 1 < (gridY R T).sort.length) :
    ∃! i, openCell R T j k ⊆ interior (T i).toSet := by
  have hxj : nth (gridX R T) j < nth (gridX R T) (j + 1) := nth_lt_nth (Nat.lt_succ_self j) hj
  have hyk : nth (gridY R T) k < nth (gridY R T) (k + 1) := nth_lt_nth (Nat.lt_succ_self k) hk
  set z : ℝ × ℝ :=
    ((nth (gridX R T) j + nth (gridX R T) (j + 1)) / 2,
      (nth (gridY R T) k + nth (gridY R T) (k + 1)) / 2) with hz
  have hzx : nth (gridX R T) j < z.1 ∧ z.1 < nth (gridX R T) (j + 1) :=
    ⟨by rw [hz]; dsimp only; linarith, by rw [hz]; dsimp only; linarith⟩
  have hzy : nth (gridY R T) k < z.2 ∧ z.2 < nth (gridY R T) (k + 1) :=
    ⟨by rw [hz]; dsimp only; linarith, by rw [hz]; dsimp only; linarith⟩
  have hzR : z ∈ R.toSet := Rectangle.mem_toSet.mpr
    ⟨⟨(gridX_mem_Icc hT (nth_mem (Nat.lt_of_succ_lt hj))).1.trans hzx.1.le,
        hzx.2.le.trans (gridX_mem_Icc hT (nth_mem hj)).2⟩,
      (gridY_mem_Icc hT (nth_mem (Nat.lt_of_succ_lt hk))).1.trans hzy.1.le,
      hzy.2.le.trans (gridY_mem_Icc hT (nth_mem hk)).2⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hT.cover.subset hzR)
  obtain ⟨⟨hx₀, hx₁⟩, hy₀, hy₁⟩ := Rectangle.mem_toSet.mp hi
  obtain ⟨hjx₀, hjx₁⟩ := nth_sandwich (tile_x₀_mem_gridX i) (tile_x₁_mem_gridX i) hj hx₀ hx₁
    hzx.1 hzx.2
  obtain ⟨hky₀, hky₁⟩ := nth_sandwich (tile_y₀_mem_gridY i) (tile_y₁_mem_gridY i) hk hy₀ hy₁
    hzy.1 hzy.2
  refine ⟨i, fun w hw ↦ Rectangle.mem_interior_toSet ?_, fun i' hi' ↦ ?_⟩
  · obtain ⟨⟨hw₁, hw₂⟩, hw₃, hw₄⟩ := hw
    exact ⟨⟨hjx₀.trans_lt hw₁, hw₂.trans_le hjx₁⟩, hky₀.trans_lt hw₃, hw₄.trans_le hky₁⟩
  · by_contra hne
    exact Set.disjoint_left.mp (hT.interiorDisjoint hne) (hi' ⟨hzx, hzy⟩)
      (Rectangle.mem_interior_toSet ⟨⟨hjx₀.trans_lt hzx.1, hzx.2.trans_le hjx₁⟩,
        hky₀.trans_lt hzy.1, hzy.2.trans_le hky₁⟩)

private lemma nonempty_index (hT : IsTiling R T) : Nonempty ι := by
  have h : (R.x₀, R.y₀) ∈ R.toSet := Rectangle.mem_toSet.mpr ⟨⟨le_rfl, R.hx⟩, le_rfl, R.hy⟩
  obtain ⟨i, -⟩ := mem_iUnion.mp (hT.cover.subset h)
  exact ⟨i⟩

open scoped Classical in
/-- The tile whose interior contains a given open grid cell (junk value out of range). -/
private noncomputable def cellTile (hT : IsTiling R T) (p : ℕ × ℕ) : ι :=
  if h : p.1 + 1 < (gridX R T).sort.length ∧ p.2 + 1 < (gridY R T).sort.length then
    (existsUnique_openCell_subset hT h.1 h.2).exists.choose
  else (nonempty_index hT).some

private lemma openCell_subset_cellTile (hT : IsTiling R T) {p : ℕ × ℕ}
    (h₁ : p.1 + 1 < (gridX R T).sort.length) (h₂ : p.2 + 1 < (gridY R T).sort.length) :
    openCell R T p.1 p.2 ⊆ interior (T (cellTile hT p)).toSet := by
  rw [cellTile, dif_pos ⟨h₁, h₂⟩]
  exact (existsUnique_openCell_subset hT h₁ h₂).exists.choose_spec

/-! ### The index intervals of a tile -/

/-- The index of a tile's left edge among the sorted grid x-coordinates. -/
private noncomputable def idxL (R : Rectangle) (T : ι → Rectangle) (i : ι) : ℕ :=
  (exists_nth_eq (tile_x₀_mem_gridX (R := R) (T := T) i)).choose

/-- The index of a tile's right edge. -/
private noncomputable def idxR (R : Rectangle) (T : ι → Rectangle) (i : ι) : ℕ :=
  (exists_nth_eq (tile_x₁_mem_gridX (R := R) (T := T) i)).choose

/-- The index of a tile's bottom edge among the sorted grid y-coordinates. -/
private noncomputable def idxB (R : Rectangle) (T : ι → Rectangle) (i : ι) : ℕ :=
  (exists_nth_eq (tile_y₀_mem_gridY (R := R) (T := T) i)).choose

/-- The index of a tile's top edge. -/
private noncomputable def idxT (R : Rectangle) (T : ι → Rectangle) (i : ι) : ℕ :=
  (exists_nth_eq (tile_y₁_mem_gridY (R := R) (T := T) i)).choose

private lemma idxL_lt (i : ι) : idxL R T i < (gridX R T).sort.length :=
  (exists_nth_eq (tile_x₀_mem_gridX i)).choose_spec.choose

private lemma idxR_lt (i : ι) : idxR R T i < (gridX R T).sort.length :=
  (exists_nth_eq (tile_x₁_mem_gridX i)).choose_spec.choose

private lemma idxB_lt (i : ι) : idxB R T i < (gridY R T).sort.length :=
  (exists_nth_eq (tile_y₀_mem_gridY i)).choose_spec.choose

private lemma idxT_lt (i : ι) : idxT R T i < (gridY R T).sort.length :=
  (exists_nth_eq (tile_y₁_mem_gridY i)).choose_spec.choose

private lemma nth_idxL (i : ι) : nth (gridX R T) (idxL R T i) = (T i).x₀ :=
  (exists_nth_eq (tile_x₀_mem_gridX i)).choose_spec.choose_spec

private lemma nth_idxR (i : ι) : nth (gridX R T) (idxR R T i) = (T i).x₁ :=
  (exists_nth_eq (tile_x₁_mem_gridX i)).choose_spec.choose_spec

private lemma nth_idxB (i : ι) : nth (gridY R T) (idxB R T i) = (T i).y₀ :=
  (exists_nth_eq (tile_y₀_mem_gridY i)).choose_spec.choose_spec

private lemma nth_idxT (i : ι) : nth (gridY R T) (idxT R T i) = (T i).y₁ :=
  (exists_nth_eq (tile_y₁_mem_gridY i)).choose_spec.choose_spec

/-- **The fiber of `cellTile` over a tile is the product of its two index intervals.** -/
private lemma cellTile_eq_iff (hT : IsTiling R T) {p : ℕ × ℕ} {i : ι}
    (h₁ : p.1 + 1 < (gridX R T).sort.length) (h₂ : p.2 + 1 < (gridY R T).sort.length) :
    cellTile hT p = i ↔
      (idxL R T i ≤ p.1 ∧ p.1 < idxR R T i) ∧ idxB R T i ≤ p.2 ∧ p.2 < idxT R T i := by
  have hxj : nth (gridX R T) p.1 < nth (gridX R T) (p.1 + 1) :=
    nth_lt_nth (Nat.lt_succ_self _) h₁
  have hyk : nth (gridY R T) p.2 < nth (gridY R T) (p.2 + 1) :=
    nth_lt_nth (Nat.lt_succ_self _) h₂
  constructor
  · rintro rfl
    have hsub := openCell_subset_cellTile hT h₁ h₂
    rw [Rectangle.toSet, interior_prod_eq, interior_Icc, interior_Icc] at hsub
    have hxm : (nth (gridX R T) p.1 + nth (gridX R T) (p.1 + 1)) / 2 ∈
        Ioo (nth (gridX R T) p.1) (nth (gridX R T) (p.1 + 1)) := ⟨by linarith, by linarith⟩
    have hym : (nth (gridY R T) p.2 + nth (gridY R T) (p.2 + 1)) / 2 ∈
        Ioo (nth (gridY R T) p.2) (nth (gridY R T) (p.2 + 1)) := ⟨by linarith, by linarith⟩
    have hxsub : Ioo (nth (gridX R T) p.1) (nth (gridX R T) (p.1 + 1)) ⊆
        Ioo (T (cellTile hT p)).x₀ (T (cellTile hT p)).x₁ := fun x hx ↦
      (hsub (a := (x, (nth (gridY R T) p.2 + nth (gridY R T) (p.2 + 1)) / 2))
        (Set.mem_prod.mpr ⟨hx, hym⟩)).1
    have hysub : Ioo (nth (gridY R T) p.2) (nth (gridY R T) (p.2 + 1)) ⊆
        Ioo (T (cellTile hT p)).y₀ (T (cellTile hT p)).y₁ := fun y hy ↦
      (hsub (a := ((nth (gridX R T) p.1 + nth (gridX R T) (p.1 + 1)) / 2, y))
        (Set.mem_prod.mpr ⟨hxm, hy⟩)).2
    obtain ⟨hx₀, hx₁⟩ := (Set.Ioo_subset_Ioo_iff hxj).mp hxsub
    obtain ⟨hy₀, hy₁⟩ := (Set.Ioo_subset_Ioo_iff hyk).mp hysub
    refine ⟨⟨le_of_nth_le_nth (idxL_lt _) ((nth_idxL _).le.trans hx₀), ?_⟩,
      le_of_nth_le_nth (idxB_lt _) ((nth_idxB _).le.trans hy₀), ?_⟩
    · exact Nat.lt_of_succ_le (le_of_nth_le_nth h₁ (hx₁.trans (nth_idxR _).ge))
    · exact Nat.lt_of_succ_le (le_of_nth_le_nth h₂ (hy₁.trans (nth_idxT _).ge))
  · rintro ⟨⟨hL, hR⟩, hB, hTo⟩
    refine (existsUnique_openCell_subset hT h₁ h₂).unique (openCell_subset_cellTile hT h₁ h₂)
      fun w hw ↦ Rectangle.mem_interior_toSet ?_
    obtain ⟨⟨hw₁, hw₂⟩, hw₃, hw₄⟩ := hw
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (((nth_idxL i).symm.le).trans (nth_le_nth hL (Nat.lt_of_succ_lt h₁))).trans_lt hw₁
    · exact hw₂.trans_le ((nth_le_nth (Nat.succ_le_of_lt hR) (idxR_lt i)).trans (nth_idxR i).le)
    · exact (((nth_idxB i).symm.le).trans (nth_le_nth hB (Nat.lt_of_succ_lt h₂))).trans_lt hw₃
    · exact hw₄.trans_le ((nth_le_nth (Nat.succ_le_of_lt hTo) (idxT_lt i)).trans (nth_idxT i).le)

/-- The cells assigned to a tile form the product of its two index intervals, inside the grid.
The `Decidable` instance is a parameter so the statement rewrites any elaboration of the
fiber. -/
private lemma filter_cellTile_eq (hT : IsTiling R T) (i : ι)
    {dec : DecidablePred fun p ↦ cellTile hT p = i} :
    @Finset.filter _ (fun p ↦ cellTile hT p = i) dec
        (range ((gridX R T).sort.length - 1) ×ˢ range ((gridY R T).sort.length - 1)) =
      Finset.Ico (idxL R T i) (idxR R T i) ×ˢ Finset.Ico (idxB R T i) (idxT R T i) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hp₁, hp₂⟩, hp⟩
    exact (cellTile_eq_iff hT (by omega) (by omega)).mp hp
  · rintro ⟨⟨hL, hR⟩, hB, hTo⟩
    have h₁ : p.1 + 1 < (gridX R T).sort.length := by have := idxR_lt (R := R) (T := T) i; omega
    have h₂ : p.2 + 1 < (gridY R T).sort.length := by have := idxT_lt (R := R) (T := T) i; omega
    exact ⟨⟨by omega, by omega⟩, (cellTile_eq_iff hT h₁ h₂).mpr ⟨⟨hL, hR⟩, hB, hTo⟩⟩

end GridRefinement

/-! ### Additivity of the f-area -/

open GridRefinement in
/-- **The f-area is additive over a tiling** (Wagon, after Hochster and Maté), for arbitrary
`f, g : ℝ → ℝ`: summing `(f x₁ - f x₀) · (g y₁ - g y₀)` over the tiles of a tiling gives the
same quantity for the tiled rectangle. The tile edges span a grid; every open grid cell lies in
exactly one tile, the cells of a tile fill a product of index intervals, and the sum telescopes
in both coordinates. -/
theorem IsTiling.sum_fgArea {ι : Type*} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}
    (hT : IsTiling R T) (f g : ℝ → ℝ) : ∑ i, fgArea f g (T i) = fgArea f g R := by
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

end IntegerRectangle
