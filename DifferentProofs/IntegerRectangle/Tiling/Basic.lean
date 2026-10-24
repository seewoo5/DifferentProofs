module

public import DifferentProofs.IntegerRectangle.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Shared core for the integer-rectangle tiling proofs

This file collects the basic facts about a rectangle's point set and about the tiles of a tiling
that the proofs of `IntegerRectangleTheorem` share.

The elementary layer unfolds `Rectangle.toSet` and reads off that every tile of a tiling sits
inside the tiled rectangle (`Rectangle.mem_toSet`, `Rectangle.mem_interior_toSet`,
`IsTiling.tile_subset`, and the four edge bounds `IsTiling.le_tile_x₀` … `IsTiling.tile_y₁_le`),
so that the tiled rectangle, like its tiles, has positive width and height (`IsTiling.x₀_lt_x₁`,
`IsTiling.y₀_lt_y₁`).

It also names Wagon's two kinds of tile. An *H-tile* has integer width and a *V-tile* integer
height (`Rectangle.IsHTile`, `Rectangle.IsVTile`), so the tiles of the theorem are exactly the
rectangles that are one or the other (`Rectangle.hasIntegerSide_iff`). A tile with both sides
integral is both. Proofs that need the two kinds disjoint designate such a tile one way: the
staircase and reducible-link proofs count it as an H-tile, the cut-set proof as a V-tile.

Next, a tiling is turned into an *exact* partition. Closed tiles overlap along shared edges, so a
tiling only partitions the rectangle up to null sets; deleting each tile's left and bottom edges
(`Rectangle.toSetIoc`) repairs this exactly.

* `IsTiling.pairwiseDisjoint_toSetIoc` and `IsTiling.iUnion_toSetIoc` — the half-open cells of a
  tiling partition the half-open cell of the tiled rectangle.
* `IsTiling.measure_toSetIoc` — consequently *every* measure on the plane, not just Lebesgue, is
  additive over a tiling.

The integrals of the first three proofs are taken over the closed tiles instead, and are handled
in `DifferentProofs.IntegerRectangle.Tiling.Integral`.
-/

@[expose] public section

open MeasureTheory Set

namespace IntegerRectangle

namespace Rectangle

/-- The *half-open cell* of a rectangle: the rectangle with its left and bottom edges removed.
Closed tiles of a tiling overlap along shared edges, but their half-open cells do not, so these are
what turn a tiling into an exact partition (`IsTiling.iUnion_toSetIoc`). -/
def toSetIoc (R : Rectangle) : Set (ℝ × ℝ) := Ioc R.x₀ R.x₁ ×ˢ Ioc R.y₀ R.y₁

/-- Membership in a rectangle's half-open cell, unfolded into the four coordinate inequalities. -/
lemma mem_toSetIoc {R : Rectangle} {z : ℝ × ℝ} :
    z ∈ R.toSetIoc ↔ (R.x₀ < z.1 ∧ z.1 ≤ R.x₁) ∧ (R.y₀ < z.2 ∧ z.2 ≤ R.y₁) := Iff.rfl

/-- Membership of a point given by its coordinates, the form in which the four inequalities are
usually needed. -/
lemma mem_toSetIoc' {R : Rectangle} {x y : ℝ} :
    (x, y) ∈ R.toSetIoc ↔ (R.x₀ < x ∧ x ≤ R.x₁) ∧ R.y₀ < y ∧ y ≤ R.y₁ := Iff.rfl

/-- A rectangle's half-open cell is a measurable subset of the plane. -/
lemma measurableSet_toSetIoc (R : Rectangle) : MeasurableSet R.toSetIoc :=
  measurableSet_Ioc.prod measurableSet_Ioc

/-- Membership in a rectangle's point set, unfolded into the four coordinate inequalities. -/
lemma mem_toSet {R : Rectangle} {z : ℝ × ℝ} :
    z ∈ R.toSet ↔ (R.x₀ ≤ z.1 ∧ z.1 ≤ R.x₁) ∧ (R.y₀ ≤ z.2 ∧ z.2 ≤ R.y₁) := Iff.rfl

/-- A point strictly inside all four edges lies in the interior of the rectangle. -/
lemma mem_interior_toSet {R : Rectangle} {z : ℝ × ℝ}
    (h : (R.x₀ < z.1 ∧ z.1 < R.x₁) ∧ (R.y₀ < z.2 ∧ z.2 < R.y₁)) : z ∈ interior R.toSet := by
  rw [Rectangle.toSet, interior_prod_eq, interior_Icc, interior_Icc]
  exact h

/-- A rectangle is nondegenerate exactly when its interior is nonempty. -/
lemma nondegenerate_iff_nonempty_interior {S : Rectangle} :
    S.Nondegenerate ↔ (interior S.toSet).Nonempty := by
  rw [Rectangle.toSet, interior_prod_eq, interior_Icc, interior_Icc, Set.prod_nonempty_iff,
    Set.nonempty_Ioo, Set.nonempty_Ioo, Nondegenerate]

noncomputable instance : DecidablePred Nondegenerate :=
  fun S ↦ inferInstanceAs (Decidable (S.x₀ < S.x₁ ∧ S.y₀ < S.y₁))

/-- A rectangle's width is nonnegative. -/
lemma width_nonneg (R : Rectangle) : 0 ≤ R.width := sub_nonneg.mpr R.hx

/-- A rectangle is an **H-tile**, in Wagon's terms, when its width, its horizontal side, is an
integer. -/
def IsHTile (S : Rectangle) : Prop := ∃ n : ℤ, S.width = n

/-- A rectangle is a **V-tile**, in Wagon's terms, when its height, its vertical side, is an
integer. -/
def IsVTile (S : Rectangle) : Prop := ∃ n : ℤ, S.height = n

/-- A rectangle has an integer side exactly when it is an H-tile or a V-tile. -/
lemma hasIntegerSide_iff {S : Rectangle} : S.HasIntegerSide ↔ S.IsHTile ∨ S.IsVTile := Iff.rfl

/-- A rectangle with an integer side that is not an H-tile is a V-tile. -/
lemma HasIntegerSide.isVTile_of_not_isHTile {S : Rectangle} (h : S.HasIntegerSide)
    (hS : ¬ S.IsHTile) : S.IsVTile :=
  h.resolve_left hS

/-- A rectangle with an integer side that is not a V-tile is an H-tile. -/
lemma HasIntegerSide.isHTile_of_not_isVTile {S : Rectangle} (h : S.HasIntegerSide)
    (hS : ¬ S.IsVTile) : S.IsHTile :=
  h.resolve_right hS

/-- A rectangle is a measurable subset of the plane. -/
lemma measurableSet_toSet (R : Rectangle) : MeasurableSet R.toSet :=
  measurableSet_Icc.prod measurableSet_Icc

/-- A rectangle is a compact subset of the plane. -/
lemma isCompact_toSet (R : Rectangle) : IsCompact R.toSet := isCompact_Icc.prod isCompact_Icc

end Rectangle

section Tiles

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- Each tile of a tiling is contained in the tiled rectangle. -/
lemma IsTiling.tile_subset (hT : IsTiling R T) (i : ι) : (T i).toSet ⊆ R.toSet :=
  (subset_iUnion (fun j ↦ (T j).toSet) i).trans hT.cover.superset

/-- A tiling has at least one tile: the tiled rectangle contains its lower-left corner, and the
tiles cover it. -/
lemma IsTiling.nonempty_index (hT : IsTiling R T) : Nonempty ι := by
  have h : (R.x₀, R.y₀) ∈ R.toSet := Rectangle.mem_toSet.mpr ⟨⟨le_rfl, R.hx⟩, le_rfl, R.hy⟩
  obtain ⟨i, -⟩ := mem_iUnion.mp (hT.cover.subset h)
  exact ⟨i⟩

/-- No tile of a tiling reaches below the base of the tiled rectangle. -/
lemma IsTiling.le_tile_y₀ (hT : IsTiling R T) (i : ι) : R.y₀ ≤ (T i).y₀ :=
  (Rectangle.mem_toSet.mp (hT.tile_subset i (show ((T i).x₀, (T i).y₀) ∈ (T i).toSet from
    Rectangle.mem_toSet.mpr ⟨⟨le_rfl, (T i).hx⟩, ⟨le_rfl, (T i).hy⟩⟩))).2.1

/-- No tile of a tiling reaches above the top of the tiled rectangle. -/
lemma IsTiling.tile_y₁_le (hT : IsTiling R T) (i : ι) : (T i).y₁ ≤ R.y₁ :=
  (Rectangle.mem_toSet.mp (hT.tile_subset i (show ((T i).x₁, (T i).y₁) ∈ (T i).toSet from
    Rectangle.mem_toSet.mpr ⟨⟨(T i).hx, le_rfl⟩, ⟨(T i).hy, le_rfl⟩⟩))).2.2

/-- No tile of a tiling reaches left of the tiled rectangle. -/
lemma IsTiling.le_tile_x₀ (hT : IsTiling R T) (i : ι) : R.x₀ ≤ (T i).x₀ :=
  (Rectangle.mem_toSet.mp (hT.tile_subset i (show ((T i).x₀, (T i).y₀) ∈ (T i).toSet from
    Rectangle.mem_toSet.mpr ⟨⟨le_rfl, (T i).hx⟩, ⟨le_rfl, (T i).hy⟩⟩))).1.1

/-- No tile of a tiling reaches right of the tiled rectangle. -/
lemma IsTiling.tile_x₁_le (hT : IsTiling R T) (i : ι) : (T i).x₁ ≤ R.x₁ :=
  (Rectangle.mem_toSet.mp (hT.tile_subset i (show ((T i).x₁, (T i).y₁) ∈ (T i).toSet from
    Rectangle.mem_toSet.mpr ⟨⟨(T i).hx, le_rfl⟩, ⟨(T i).hy, le_rfl⟩⟩))).1.2

/-- A tile of a tiling has positive width. -/
lemma IsTiling.tile_x₀_lt_x₁ (hT : IsTiling R T) (i : ι) : (T i).x₀ < (T i).x₁ :=
  (hT.nondegenerate i).1

/-- A tile of a tiling has positive height. -/
lemma IsTiling.tile_y₀_lt_y₁ (hT : IsTiling R T) (i : ι) : (T i).y₀ < (T i).y₁ :=
  (hT.nondegenerate i).2

/-- A tiled rectangle has positive width, since its tiles do. -/
lemma IsTiling.x₀_lt_x₁ (hT : IsTiling R T) : R.x₀ < R.x₁ :=
  have ⟨i⟩ := hT.nonempty_index
  (hT.le_tile_x₀ i).trans_lt ((hT.tile_x₀_lt_x₁ i).trans_le (hT.tile_x₁_le i))

/-- A tiled rectangle has positive height, since its tiles do. -/
lemma IsTiling.y₀_lt_y₁ (hT : IsTiling R T) : R.y₀ < R.y₁ :=
  have ⟨i⟩ := hT.nonempty_index
  (hT.le_tile_y₀ i).trans_lt ((hT.tile_y₀_lt_y₁ i).trans_le (hT.tile_y₁_le i))

end Tiles

/-! ### A tiling as an exact partition

Tiles overlap along shared edges, so a tiling is only *almost* a partition of the closed rectangle.
Deleting each tile's left and bottom edges repairs this exactly: the half-open cells of a tiling
partition the half-open cell of the tiled rectangle, with no null sets involved. Consequently
*every* measure on the plane — not just Lebesgue — is additive over a tiling. -/

section Partition

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **Half-open cells of a tiling are pairwise disjoint.** A common point of two cells could be
nudged down and to the left into the interiors of both tiles. -/
theorem IsTiling.pairwiseDisjoint_toSetIoc (hT : IsTiling R T) :
    Pairwise (Function.onFun Disjoint fun i ↦ (T i).toSetIoc) := by
  refine fun i j hij ↦ Set.disjoint_left.mpr fun z hzi hzj ↦ ?_
  obtain ⟨⟨hxi₀, hxi₁⟩, hyi₀, hyi₁⟩ := Rectangle.mem_toSetIoc.mp hzi
  obtain ⟨⟨hxj₀, hxj₁⟩, hyj₀, hyj₁⟩ := Rectangle.mem_toSetIoc.mp hzj
  exact Set.disjoint_left.mp (hT.interiorDisjoint hij)
    (Rectangle.mem_interior_toSet
      (z := ((max (T i).x₀ (T j).x₀ + z.1) / 2, (max (T i).y₀ (T j).y₀ + z.2) / 2)) (by grind))
    (Rectangle.mem_interior_toSet (by grind))

/-- **Half-open cells of a tiling cover the half-open cell of the tiled rectangle.** For the
inclusion that matters, a point of the ambient cell is approached from below-left; finitely many
tiles force one of them to contain the approaching points arbitrarily close in, and that tile's
half-open cell contains the point. -/
theorem IsTiling.iUnion_toSetIoc (hT : IsTiling R T) : ⋃ i, (T i).toSetIoc = R.toSetIoc := by
  refine Set.Subset.antisymm (iUnion_subset fun i z hz ↦ ?_) fun z hz ↦ ?_
  · obtain ⟨⟨hx₀, hx₁⟩, hy₀, hy₁⟩ := Rectangle.mem_toSetIoc.mp hz
    exact Rectangle.mem_toSetIoc.mpr
      ⟨⟨(hT.le_tile_x₀ i).trans_lt hx₀, hx₁.trans (hT.tile_x₁_le i)⟩,
        (hT.le_tile_y₀ i).trans_lt hy₀, hy₁.trans (hT.tile_y₁_le i)⟩
  · obtain ⟨⟨hx₀, hx₁⟩, hy₀, hy₁⟩ := Rectangle.mem_toSetIoc.mp hz
    have hnear := Filter.eventually_of_mem
      (Ioo_mem_nhdsGT (lt_min (sub_pos.mpr hx₀) (sub_pos.mpr hy₀))) fun δ hδ ↦
      mem_iUnion.mp <| hT.cover.subset <| show ((z.1 - δ, z.2 - δ) : ℝ × ℝ) ∈ R.toSet from
        Rectangle.mem_toSet.mpr (by grind [Set.mem_Ioo.mp hδ])
    obtain ⟨i, hi⟩ := Filter.frequently_exists.mp hnear.frequently
    obtain ⟨⟨-, hx₁'⟩, -, hy₁'⟩ := Rectangle.mem_toSet.mp <|
      (T i).isCompact_toSet.isClosed.mem_of_frequently_of_tendsto hi <|
      (Continuous.tendsto' (by fun_prop) 0 z (by simp)).mono_left nhdsWithin_le_nhds
    obtain ⟨δ, hmem, hδ : 0 < δ⟩ := (hi.and_eventually eventually_mem_nhdsWithin).exists
    obtain ⟨⟨hx₀', -⟩, hy₀', -⟩ := Rectangle.mem_toSet.mp hmem
    exact mem_iUnion.mpr ⟨i, Rectangle.mem_toSetIoc.mpr ⟨⟨by linarith, hx₁'⟩, by linarith, hy₁'⟩⟩

/-- **Every measure is additive over a tiling.** The half-open cells partition the ambient
half-open cell, so no null-set bookkeeping is needed and `μ` is arbitrary. -/
theorem IsTiling.measure_toSetIoc (hT : IsTiling R T) (μ : Measure (ℝ × ℝ)) :
    μ R.toSetIoc = ∑ i, μ (T i).toSetIoc := by
  rw [← hT.iUnion_toSetIoc,
    measure_iUnion hT.pairwiseDisjoint_toSetIoc fun i ↦ (T i).measurableSet_toSetIoc,
    tsum_fintype]

end Partition

end IntegerRectangle
