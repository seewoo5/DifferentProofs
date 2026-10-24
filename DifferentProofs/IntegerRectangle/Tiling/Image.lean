module

public import DifferentProofs.IntegerRectangle.Tiling.Grid

/-!
# Moving the lines of a tiling

Three of Wagon's proofs build an auxiliary tiling by moving the lines of the given one. The
counting-squares proof moves every vertical line `x = a` off the integer lattice to the nearest
half-integer line `x = ⌊a⌋ + 1/2`, the polynomial proof moves it to `x = a + t` for a small `t`,
and the prime-number proof scales the tiling by `p` and rounds every corner down to the integer
lattice, moving `x = a` to `x = ⌊p a⌋`; the horizontal lines are moved likewise. In each case the
vertical lines move by one map `φ` and the horizontal ones by one map `ψ`, neither of which changes
the order of the lines, and the moved tiles again tile the moved rectangle — with fewer tiles,
perhaps, since a tile can collapse to a segment, but "this is unimportant" (Wagon).

That is `IsTiling.image`. The image of a rectangle under the coordinate maps `φ` and `ψ` is
`Rectangle.image`, and if `φ` and `ψ` are monotone on the coordinates of the vertical and the
horizontal lines of a tiling (`Grid.gridX`, `Grid.gridY`), then the images of its tiles, the
collapsed ones pruned, tile the image of the tiled rectangle. The proof is by half-open cells: a
point `z` pulls back to the point whose abscissa is the leftmost vertical line whose image is not
to the left of `z` (if there is one), and whose ordinate is the lowest horizontal line whose image
is not below `z`. That point lies in the half-open cell of a tile, or of the tiled rectangle,
exactly when `z` lies in that of its image, so the moved half-open cells are pairwise disjoint and
cover the moved rectangle because those of the tiling are and do. Monotonicity is asked only on
the finitely many coordinates of the tiling, since the polynomial proof moves the lines by a map
that keeps their order but is not monotone on all of `ℝ`.

Since area is additive over a tiling, the areas of the moved tiles add up to the area of the moved
rectangle (`IsTiling.sum_area_image`).
-/

@[expose] public section

open Finset

namespace IntegerRectangle

/-- The image of a rectangle under the coordinate maps `φ` and `ψ`: the rectangle spanned by the
images of its edges. When `φ` and `ψ` do not reverse the order of its coordinates, its edges are
the images of the edges of `S` (`Rectangle.image_x₀` and its siblings). -/
def Rectangle.image (φ ψ : ℝ → ℝ) (S : Rectangle) : Rectangle where
  x₀ := min (φ S.x₀) (φ S.x₁)
  x₁ := max (φ S.x₀) (φ S.x₁)
  y₀ := min (ψ S.y₀) (ψ S.y₁)
  y₁ := max (ψ S.y₀) (ψ S.y₁)
  hx := min_le_max
  hy := min_le_max

namespace Rectangle

variable {φ ψ : ℝ → ℝ} {S : Rectangle}

/-- The left edge of the image of `S`, when `φ` keeps the order of its x-coordinates. -/
lemma image_x₀ (h : φ S.x₀ ≤ φ S.x₁) : (S.image φ ψ).x₀ = φ S.x₀ := min_eq_left h

/-- The right edge of the image of `S`, when `φ` keeps the order of its x-coordinates. -/
lemma image_x₁ (h : φ S.x₀ ≤ φ S.x₁) : (S.image φ ψ).x₁ = φ S.x₁ := max_eq_right h

/-- The bottom edge of the image of `S`, when `ψ` keeps the order of its y-coordinates. -/
lemma image_y₀ (h : ψ S.y₀ ≤ ψ S.y₁) : (S.image φ ψ).y₀ = ψ S.y₀ := min_eq_left h

/-- The top edge of the image of `S`, when `ψ` keeps the order of its y-coordinates. -/
lemma image_y₁ (h : ψ S.y₀ ≤ ψ S.y₁) : (S.image φ ψ).y₁ = ψ S.y₁ := max_eq_right h

/-- The area of the image of a rectangle whose coordinates keep their order. -/
lemma area_image (hx : φ S.x₀ ≤ φ S.x₁) (hy : ψ S.y₀ ≤ ψ S.y₁) :
    (S.image φ ψ).area = (φ S.x₁ - φ S.x₀) * (ψ S.y₁ - ψ S.y₀) := by
  rw [area, width, height, image_x₀ hx, image_x₁ hx, image_y₀ hy, image_y₁ hy]

end Rectangle

/-! ### One axis at a time -/

section Axis

variable {s : Finset ℝ} {φ : ℝ → ℝ}

/-- **A coordinate pulls back across the moved lines.** If `φ` is monotone on `s`, then every `u`
has an `x`, the least `g ∈ s` with `u ≤ φ g` (or a point beyond `s` if there is none), such that
for `a ≤ b` in `s`, `u` lies in the moved half-open interval `Set.uIoc (φ a) (φ b)` exactly when
`x` lies in `(a, b]`. -/
private lemma exists_mem_Ioc_iff (hφ : MonotoneOn φ s) (u : ℝ) :
    ∃ x, ∀ ⦃a b⦄, a ∈ s → b ∈ s → a ≤ b → (u ∈ Set.uIoc (φ a) (φ b) ↔ x ∈ Set.Ioc a b) := by
  suffices ∃ x, ∀ g ∈ s, u ≤ φ g ↔ x ≤ g from this.imp fun x hx a b ha hb hab ↦
    Set.uIoc_of_le (hφ ha hb hab) ▸ and_congr (lt_iff_lt_of_le_iff_le (hx a ha)) (hx b hb)
  by_cases h : ∃ g ∈ s, u ≤ φ g
  · obtain ⟨hxs, hux⟩ := mem_filter.mp (min'_mem _ (filter_nonempty_iff.mpr h))
    exact ⟨_, fun g hg ↦ ⟨fun h ↦ min'_le _ g (mem_filter.mpr ⟨hg, h⟩),
      fun h ↦ hux.trans (hφ hxs hg h)⟩⟩
  · obtain ⟨M, hM⟩ := s.exists_le
    exact ⟨M + 1, by grind⟩

end Axis

/-! ### The moved tiling -/

open Grid

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle} {φ ψ : ℝ → ℝ}

/-- **A point pulls back to the tiling.** If `φ` and `ψ` are monotone on the coordinates of the
vertical and the horizontal lines of the grid of `T`, then every point `z` has a point `w` that
lies in the half-open cell of `R`, or of a tile, exactly when `z` lies in that of its image. -/
private lemma exists_mem_toSetIoc_iff (hφ : MonotoneOn φ (gridX R T))
    (hψ : MonotoneOn ψ (gridY R T)) (z : ℝ × ℝ) :
    ∃ w, (z ∈ (R.image φ ψ).toSetIoc ↔ w ∈ R.toSetIoc) ∧
      ∀ i, z ∈ ((T i).image φ ψ).toSetIoc ↔ w ∈ (T i).toSetIoc := by
  obtain ⟨x, hx⟩ := exists_mem_Ioc_iff hφ z.1
  obtain ⟨y, hy⟩ := exists_mem_Ioc_iff hψ z.2
  exact ⟨(x, y), and_congr (hx left_mem_gridX right_mem_gridX R.hx)
    (hy bot_mem_gridY top_mem_gridY R.hy), fun i ↦
    and_congr (hx (tile_x₀_mem_gridX i) (tile_x₁_mem_gridX i) (T i).hx)
      (hy (tile_y₀_mem_gridY i) (tile_y₁_mem_gridY i) (T i).hy)⟩

/-- **The moved tiles lie in the moved rectangle**, since `φ` and `ψ` keep the image of every
line of the grid between the images of the edges of `R`. -/
private lemma IsTiling.image_tile_subset (hT : IsTiling R T) (hφ : MonotoneOn φ (gridX R T))
    (hψ : MonotoneOn ψ (gridY R T)) (i : ι) : ((T i).image φ ψ).toSet ⊆ (R.image φ ψ).toSet := by
  have hX {g} (hg : g ∈ gridX R T) : φ g ∈ Set.uIcc (φ R.x₀) (φ R.x₁) :=
    Set.Icc_subset_uIcc <| (gridX_mem_Icc hT hg).imp (hφ left_mem_gridX hg) (hφ hg right_mem_gridX)
  have hY {g} (hg : g ∈ gridY R T) : ψ g ∈ Set.uIcc (ψ R.y₀) (ψ R.y₁) :=
    Set.Icc_subset_uIcc <| (gridY_mem_Icc hT hg).imp (hψ bot_mem_gridY hg) (hψ hg top_mem_gridY)
  exact Set.prod_mono (Set.uIcc_subset_uIcc (hX (tile_x₀_mem_gridX i)) (hX (tile_x₁_mem_gridX i)))
    (Set.uIcc_subset_uIcc (hY (tile_y₀_mem_gridY i)) (hY (tile_y₁_mem_gridY i)))

/-- **Distinct moved tiles have disjoint half-open cells**: a common point would pull back to a
common point of the half-open cells of the two tiles. -/
private lemma IsTiling.pairwiseDisjoint_toSetIoc_image (hT : IsTiling R T)
    (hφ : MonotoneOn φ (gridX R T)) (hψ : MonotoneOn ψ (gridY R T)) :
    Pairwise (Function.onFun Disjoint fun i ↦ ((T i).image φ ψ).toSetIoc) :=
  fun i j hij ↦ Set.disjoint_left.mpr fun z hi hj ↦
    have ⟨_, _, h⟩ := exists_mem_toSetIoc_iff hφ hψ z
    Set.disjoint_left.mp (hT.pairwiseDisjoint_toSetIoc hij) ((h i).mp hi) ((h j).mp hj)

/-- **The half-open cells of the moved tiles cover that of the moved rectangle**: a point of it
pulls back to a point of the half-open cell of `R`, which lies in the half-open cell of a tile. -/
private lemma IsTiling.toSetIoc_image_subset_iUnion (hT : IsTiling R T)
    (hφ : MonotoneOn φ (gridX R T)) (hψ : MonotoneOn ψ (gridY R T)) :
    (R.image φ ψ).toSetIoc ⊆ ⋃ i, ((T i).image φ ψ).toSetIoc := fun z hz ↦
  have ⟨_, hR, h⟩ := exists_mem_toSetIoc_iff hφ hψ z
  have ⟨i, hi⟩ := Set.mem_iUnion.mp (hT.iUnion_toSetIoc.ge (hR.mp hz))
  Set.mem_iUnion.mpr ⟨i, (h i).mpr hi⟩

/-- **Moving the lines of a tiling in order gives a tiling.** If `φ` and `ψ` are monotone on the
coordinates of the vertical and the horizontal lines of a tiling of `R`, and the image of `R` is
not degenerate, then the images of the tiles, those that collapse pruned, tile the image of `R`.

The moved tiles lie in the moved rectangle, and every point `z` pulls back to a point that lies in
the half-open cell of a tile, or of `R`, exactly when `z` lies in that of its image. So the
half-open cells of the moved tiles inherit from those of the tiles that they are pairwise disjoint
and cover (`IsTiling.pairwiseDisjoint_toSetIoc`, `IsTiling.iUnion_toSetIoc`), which makes the moved
tiles a tiling once the collapsed ones are pruned (`isTiling_prune_of_toSetIoc`). -/
theorem IsTiling.image (hT : IsTiling R T) (hφ : MonotoneOn φ (gridX R T))
    (hψ : MonotoneOn ψ (gridY R T)) (hx : φ R.x₀ < φ R.x₁) (hy : ψ R.y₀ < ψ R.y₁) :
    IsTiling (R.image φ ψ) (prune fun i ↦ (T i).image φ ψ) :=
  isTiling_prune_of_toSetIoc (min_lt_max.mpr hx.ne) (min_lt_max.mpr hy.ne)
    (hT.image_tile_subset hφ hψ) (hT.pairwiseDisjoint_toSetIoc_image hφ hψ)
    (hT.toSetIoc_image_subset_iUnion hφ hψ)

/-- **The areas of the moved tiles add up to the area of the moved rectangle**, area being
additive over the moved tiling (`IsTiling.image`, `IsTiling.sum_area`); a collapsed tile has no
area. -/
theorem IsTiling.sum_area_image (hT : IsTiling R T) (hφ : MonotoneOn φ (gridX R T))
    (hψ : MonotoneOn ψ (gridY R T)) (hx : φ R.x₀ < φ R.x₁) (hy : ψ R.y₀ < ψ R.y₁) :
    ∑ i, (φ (T i).x₁ - φ (T i).x₀) * (ψ (T i).y₁ - ψ (T i).y₀) =
      (φ R.x₁ - φ R.x₀) * (ψ R.y₁ - ψ R.y₀) := by
  rw [← Rectangle.area_image hx.le hy.le, ← (hT.image hφ hψ hx hy).sum_area,
    sum_prune _ fun _ ↦ Rectangle.area_eq_zero_of_not_nondegenerate]
  exact sum_congr rfl fun i _ ↦ (Rectangle.area_image
    (hφ (tile_x₀_mem_gridX i) (tile_x₁_mem_gridX i) (T i).hx)
    (hψ (tile_y₀_mem_gridY i) (tile_y₁_mem_gridY i) (T i).hy)).symm

end IntegerRectangle
