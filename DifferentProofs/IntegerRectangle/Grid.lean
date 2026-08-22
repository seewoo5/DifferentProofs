module

public import DifferentProofs.IntegerRectangle.Cells
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.GetD

/-!
# The grid spanned by a tiling

Extending every tile edge across `R` cuts `R` into a grid: its vertical lines carry the
x-coordinates of the vertical tile edges together with those of `R` (`gridX`), its horizontal
lines the y-coordinates of the horizontal ones (`gridY`). Since no grid coordinate lies strictly
inside an open grid cell, each open cell clears the edges of any tile meeting its centre, so it
lies in the interior of a unique tile (`cellTile`); conversely the cells assigned to a tile fill
out a product of two index intervals (`cellTile_eq_iff`), because the tile's own edges are grid
lines.

This is the common combinatorial refinement of a tiling, shared by the proofs that need to count
something cell by cell: the fg-area is summed over it in
`DifferentProofs.IntegerRectangle.GridRefinement`, and the doors of Schmerl's Sperner argument
are counted over its horizontal segments in `DifferentProofs.IntegerRectangle.Sperner`.

The sorting of the edge coordinates is handled by `Finset.sort`; the `nth` layer below turns the
sorted list into a total function `ℕ → ℝ`, so that all sums range over `Finset.range` and
`Finset.Ico` in `ℕ` with no dependent index bookkeeping.
-/

@[expose] public section

open Finset Set

namespace IntegerRectangle.Grid

/-! ### The sorted enumeration of a finite set of reals -/

/-- The `j`-th element of `s` in increasing order, as a total function of `j` (junk value `0` out
of range). -/
noncomputable def nth (s : Finset ℝ) (j : ℕ) : ℝ := s.sort.getD j 0

lemma nth_eq_getElem {s : Finset ℝ} {j : ℕ} (hj : j < s.sort.length) :
    nth s j = s.sort[j] :=
  List.getD_eq_getElem _ _ hj

lemma nth_lt_nth {s : Finset ℝ} {j k : ℕ} (hjk : j < k) (hk : k < s.sort.length) :
    nth s j < nth s k := by
  rw [nth_eq_getElem (hjk.trans hk), nth_eq_getElem hk]
  exact (s.sortedLT_sort).getElem_lt_getElem_of_lt hjk

lemma nth_le_nth {s : Finset ℝ} {j k : ℕ} (hjk : j ≤ k) (hk : k < s.sort.length) :
    nth s j ≤ nth s k := by
  rcases hjk.lt_or_eq with h | h
  · exact (nth_lt_nth h hk).le
  · rw [h]

lemma lt_of_nth_lt_nth {s : Finset ℝ} {j k : ℕ} (hj : j < s.sort.length)
    (h : nth s j < nth s k) : j < k := by
  by_contra hjk
  exact absurd (nth_le_nth (not_lt.mp hjk) hj) (not_le.mpr h)

lemma le_of_nth_le_nth {s : Finset ℝ} {j k : ℕ} (hj : j < s.sort.length)
    (h : nth s j ≤ nth s k) : j ≤ k := by
  by_contra hjk
  exact absurd (nth_lt_nth (not_le.mp hjk) hj) (not_lt.mpr h)

lemma nth_mem {s : Finset ℝ} {j : ℕ} (hj : j < s.sort.length) : nth s j ∈ s := by
  rw [nth_eq_getElem hj]
  exact (s.mem_sort (· ≤ ·)).mp (List.getElem_mem _)

lemma exists_nth_eq {s : Finset ℝ} {a : ℝ} (ha : a ∈ s) :
    ∃ j, ∃ _ : j < s.sort.length, nth s j = a := by
  obtain ⟨j, hj, h⟩ := List.mem_iff_getElem.mp ((s.mem_sort (· ≤ ·)).mpr ha)
  exact ⟨j, hj, (nth_eq_getElem hj).trans h⟩

lemma nth_zero {s : Finset ℝ} (hs : s.Nonempty) : nth s 0 = s.min' hs := by
  have h : 0 < s.sort.length := by rw [Finset.length_sort]; exact card_pos.mpr hs
  rw [nth_eq_getElem h]
  exact Finset.sorted_zero_eq_min'

lemma nth_last {s : Finset ℝ} (hs : s.Nonempty) :
    nth s (s.sort.length - 1) = s.max' hs := by
  have h : 0 < s.sort.length := by rw [Finset.length_sort]; exact card_pos.mpr hs
  rw [nth_eq_getElem (Nat.sub_lt h one_pos)]
  exact s.sorted_last_eq_max'_aux (Nat.sub_lt h one_pos) hs

/-- No element of `s` lies strictly between two consecutive elements of `s`. -/
lemma notMem_Ioo_nth {s : Finset ℝ} {a : ℝ} (ha : a ∈ s) {j : ℕ}
    (hj : j + 1 < s.sort.length) : a ∉ Ioo (nth s j) (nth s (j + 1)) := by
  rintro ⟨h₀, h₁⟩
  obtain ⟨k, hk, rfl⟩ := exists_nth_eq ha
  have := lt_of_nth_lt_nth (Nat.lt_of_succ_lt hj) h₀
  have := lt_of_nth_lt_nth hk h₁
  omega

/-- An interval `[a, b]` with endpoints in `s` whose interior contains a point of the `j`-th open
gap of `s` sandwiches that gap: `a` is at most the gap's left end, `b` at least its right end. -/
lemma nth_sandwich {s : Finset ℝ} {a b z : ℝ} (ha : a ∈ s) (hb : b ∈ s) {j : ℕ}
    (hj : j + 1 < s.sort.length) (haz : a ≤ z) (hzb : z ≤ b) (hz₀ : nth s j < z)
    (hz₁ : z < nth s (j + 1)) : a ≤ nth s j ∧ nth s (j + 1) ≤ b :=
  ⟨not_lt.mp fun h ↦ notMem_Ioo_nth ha hj ⟨h, haz.trans_lt hz₁⟩,
    not_lt.mp fun h ↦ notMem_Ioo_nth hb hj ⟨hz₀.trans_le hzb, h⟩⟩


/-! ### The grid of a tiling -/

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

open scoped Classical in
/-- The x-coordinates of the vertical lines of the grid: the vertical edges of the tiles and of
the tiled rectangle. -/
noncomputable def gridX (R : Rectangle) (T : ι → Rectangle) : Finset ℝ :=
  insert R.x₀ (insert R.x₁ ((univ.image fun i ↦ (T i).x₀) ∪ univ.image fun i ↦ (T i).x₁))

open scoped Classical in
/-- The y-coordinates of the horizontal lines of the grid. -/
noncomputable def gridY (R : Rectangle) (T : ι → Rectangle) : Finset ℝ :=
  insert R.y₀ (insert R.y₁ ((univ.image fun i ↦ (T i).y₀) ∪ univ.image fun i ↦ (T i).y₁))

lemma left_mem_gridX : R.x₀ ∈ gridX R T := by simp [gridX]

lemma right_mem_gridX : R.x₁ ∈ gridX R T := by simp [gridX]

lemma bot_mem_gridY : R.y₀ ∈ gridY R T := by simp [gridY]

lemma top_mem_gridY : R.y₁ ∈ gridY R T := by simp [gridY]

lemma tile_x₀_mem_gridX (i : ι) : (T i).x₀ ∈ gridX R T := by simp [gridX]

lemma tile_x₁_mem_gridX (i : ι) : (T i).x₁ ∈ gridX R T := by simp [gridX]

lemma tile_y₀_mem_gridY (i : ι) : (T i).y₀ ∈ gridY R T := by simp [gridY]

lemma tile_y₁_mem_gridY (i : ι) : (T i).y₁ ∈ gridY R T := by simp [gridY]

/-- Every grid x-coordinate lies between the left and right edges of the tiled rectangle. -/
lemma gridX_mem_Icc (hT : IsTiling R T) {a : ℝ} (ha : a ∈ gridX R T) :
    R.x₀ ≤ a ∧ a ≤ R.x₁ := by
  have ha' : a = R.x₀ ∨ a = R.x₁ ∨ (∃ i, (T i).x₀ = a) ∨ ∃ i, (T i).x₁ = a := by
    simpa [gridX, or_assoc, eq_comm] using ha
  obtain rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ := ha'
  · exact ⟨le_rfl, R.hx⟩
  · exact ⟨R.hx, le_rfl⟩
  · exact ⟨hT.le_tile_x₀ i, (T i).hx.trans (hT.tile_x₁_le i)⟩
  · exact ⟨(hT.le_tile_x₀ i).trans (T i).hx, hT.tile_x₁_le i⟩

/-- Every grid y-coordinate lies between the bottom and the top of the tiled rectangle. -/
lemma gridY_mem_Icc (hT : IsTiling R T) {a : ℝ} (ha : a ∈ gridY R T) :
    R.y₀ ≤ a ∧ a ≤ R.y₁ := by
  have ha' : a = R.y₀ ∨ a = R.y₁ ∨ (∃ i, (T i).y₀ = a) ∨ ∃ i, (T i).y₁ = a := by
    simpa [gridY, or_assoc, eq_comm] using ha
  obtain rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ := ha'
  · exact ⟨le_rfl, R.hy⟩
  · exact ⟨R.hy, le_rfl⟩
  · exact ⟨hT.le_tile_y₀ i, (T i).hy.trans (hT.tile_y₁_le i)⟩
  · exact ⟨(hT.le_tile_y₀ i).trans (T i).hy, hT.tile_y₁_le i⟩

lemma nth_gridX_zero (hT : IsTiling R T) : nth (gridX R T) 0 = R.x₀ :=
  (nth_zero ⟨R.x₀, left_mem_gridX⟩).trans <| le_antisymm
    (Finset.min'_le _ _ left_mem_gridX)
    (Finset.le_min' _ _ _ fun _ ha ↦ (gridX_mem_Icc hT ha).1)

lemma nth_gridX_last (hT : IsTiling R T) :
    nth (gridX R T) ((gridX R T).sort.length - 1) = R.x₁ :=
  (nth_last ⟨R.x₁, right_mem_gridX⟩).trans <| le_antisymm
    (Finset.max'_le _ _ _ fun _ ha ↦ (gridX_mem_Icc hT ha).2)
    (Finset.le_max' _ _ right_mem_gridX)

lemma nth_gridY_zero (hT : IsTiling R T) : nth (gridY R T) 0 = R.y₀ :=
  (nth_zero ⟨R.y₀, bot_mem_gridY⟩).trans <| le_antisymm
    (Finset.min'_le _ _ bot_mem_gridY)
    (Finset.le_min' _ _ _ fun _ ha ↦ (gridY_mem_Icc hT ha).1)

lemma nth_gridY_last (hT : IsTiling R T) :
    nth (gridY R T) ((gridY R T).sort.length - 1) = R.y₁ :=
  (nth_last ⟨R.y₁, top_mem_gridY⟩).trans <| le_antisymm
    (Finset.max'_le _ _ _ fun _ ha ↦ (gridY_mem_Icc hT ha).2)
    (Finset.le_max' _ _ top_mem_gridY)

/-! ### Each open grid cell lies inside a unique tile -/

/-- The open cell of the grid with lower-left index `(j, k)`. -/
def openCell (R : Rectangle) (T : ι → Rectangle) (j k : ℕ) : Set (ℝ × ℝ) :=
  Ioo (nth (gridX R T) j) (nth (gridX R T) (j + 1)) ×ˢ
    Ioo (nth (gridY R T) k) (nth (gridY R T) (k + 1))

/-- **Every open grid cell lies in the interior of exactly one tile.** The cell's centre is
covered by some tile; the tile's edges are grid coordinates and no grid coordinate lies strictly
inside the cell, so the tile's edges clear the whole cell. Uniqueness is disjointness of
interiors. -/
lemma existsUnique_openCell_subset (hT : IsTiling R T) {j k : ℕ}
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

open scoped Classical in
/-- The tile whose interior contains a given open grid cell (junk value out of range). -/
noncomputable def cellTile (hT : IsTiling R T) (p : ℕ × ℕ) : ι :=
  if h : p.1 + 1 < (gridX R T).sort.length ∧ p.2 + 1 < (gridY R T).sort.length then
    (existsUnique_openCell_subset hT h.1 h.2).exists.choose
  else hT.nonempty_index.some

lemma openCell_subset_cellTile (hT : IsTiling R T) {p : ℕ × ℕ}
    (h₁ : p.1 + 1 < (gridX R T).sort.length) (h₂ : p.2 + 1 < (gridY R T).sort.length) :
    openCell R T p.1 p.2 ⊆ interior (T (cellTile hT p)).toSet := by
  rw [cellTile, dif_pos ⟨h₁, h₂⟩]
  exact (existsUnique_openCell_subset hT h₁ h₂).exists.choose_spec

/-! ### The index intervals of a tile -/

/-- The index of a tile's left edge among the sorted grid x-coordinates. -/
noncomputable def idxL (R : Rectangle) (T : ι → Rectangle) (i : ι) : ℕ :=
  (exists_nth_eq (tile_x₀_mem_gridX (R := R) (T := T) i)).choose

/-- The index of a tile's right edge. -/
noncomputable def idxR (R : Rectangle) (T : ι → Rectangle) (i : ι) : ℕ :=
  (exists_nth_eq (tile_x₁_mem_gridX (R := R) (T := T) i)).choose

/-- The index of a tile's bottom edge among the sorted grid y-coordinates. -/
noncomputable def idxB (R : Rectangle) (T : ι → Rectangle) (i : ι) : ℕ :=
  (exists_nth_eq (tile_y₀_mem_gridY (R := R) (T := T) i)).choose

/-- The index of a tile's top edge. -/
noncomputable def idxT (R : Rectangle) (T : ι → Rectangle) (i : ι) : ℕ :=
  (exists_nth_eq (tile_y₁_mem_gridY (R := R) (T := T) i)).choose

lemma idxL_lt (i : ι) : idxL R T i < (gridX R T).sort.length :=
  (exists_nth_eq (tile_x₀_mem_gridX i)).choose_spec.choose

lemma idxR_lt (i : ι) : idxR R T i < (gridX R T).sort.length :=
  (exists_nth_eq (tile_x₁_mem_gridX i)).choose_spec.choose

lemma idxB_lt (i : ι) : idxB R T i < (gridY R T).sort.length :=
  (exists_nth_eq (tile_y₀_mem_gridY i)).choose_spec.choose

lemma idxT_lt (i : ι) : idxT R T i < (gridY R T).sort.length :=
  (exists_nth_eq (tile_y₁_mem_gridY i)).choose_spec.choose

lemma nth_idxL (i : ι) : nth (gridX R T) (idxL R T i) = (T i).x₀ :=
  (exists_nth_eq (tile_x₀_mem_gridX i)).choose_spec.choose_spec

lemma nth_idxR (i : ι) : nth (gridX R T) (idxR R T i) = (T i).x₁ :=
  (exists_nth_eq (tile_x₁_mem_gridX i)).choose_spec.choose_spec

lemma nth_idxB (i : ι) : nth (gridY R T) (idxB R T i) = (T i).y₀ :=
  (exists_nth_eq (tile_y₀_mem_gridY i)).choose_spec.choose_spec

lemma nth_idxT (i : ι) : nth (gridY R T) (idxT R T i) = (T i).y₁ :=
  (exists_nth_eq (tile_y₁_mem_gridY i)).choose_spec.choose_spec

/-- **The fiber of `cellTile` over a tile is the product of its two index intervals.** -/
lemma cellTile_eq_iff (hT : IsTiling R T) {p : ℕ × ℕ} {i : ι}
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
lemma filter_cellTile_eq (hT : IsTiling R T) (i : ι)
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


end IntegerRectangle.Grid
