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
point of the image of `R` lies between the images of two consecutive vertical lines and of two
consecutive horizontal ones, and the tile containing the centre of the grid cell they bound is the
one whose image contains the point. Monotonicity is asked only on the finitely many coordinates of
the tiling, since the polynomial proof moves the lines by a map that keeps their order but is not
monotone on all of `ℝ`.

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

lemma image_x₀ (h : φ S.x₀ ≤ φ S.x₁) : (S.image φ ψ).x₀ = φ S.x₀ := min_eq_left h

lemma image_x₁ (h : φ S.x₀ ≤ φ S.x₁) : (S.image φ ψ).x₁ = φ S.x₁ := max_eq_right h

lemma image_y₀ (h : ψ S.y₀ ≤ ψ S.y₁) : (S.image φ ψ).y₀ = ψ S.y₀ := min_eq_left h

lemma image_y₁ (h : ψ S.y₀ ≤ ψ S.y₁) : (S.image φ ψ).y₁ = ψ S.y₁ := max_eq_right h

/-- The area of the image of a rectangle whose coordinates keep their order. -/
lemma area_image (hx : φ S.x₀ ≤ φ S.x₁) (hy : ψ S.y₀ ≤ ψ S.y₁) :
    (S.image φ ψ).area = (φ S.x₁ - φ S.x₀) * (ψ S.y₁ - ψ S.y₀) := by
  rw [area, width, height, image_x₀ hx, image_x₁ hx, image_y₀ hy, image_y₁ hy]

end Rectangle

/-! ### One axis at a time -/

section Axis

variable {s : Finset ℝ} {φ : ℝ → ℝ}

/-- **Two intervals between coordinates whose images both contain `u` overlap.** If `φ` is
monotone on `s`, and `u` lies in the half-open images `(φ a, φ b]` and `(φ c, φ d]` of two
intervals with endpoints in `s`, then those intervals overlap in an open interval. -/
private lemma max_lt_min (hφ : MonotoneOn φ s) {a b c d u : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hd : d ∈ s) (hab : a < b) (hcd : c < d) (h₁ : φ a < u ∧ u ≤ φ b)
    (h₂ : φ c < u ∧ u ≤ φ d) : max a c < min b d := by
  by_contra h
  push Not at h
  rcases min_le_iff.mp h with h | h <;> rcases le_max_iff.mp h with h | h
  · linarith
  · linarith [hφ hb hc h]
  · linarith [hφ hd ha h]
  · linarith

/-- **A point between the images of two coordinates lies between the images of two consecutive
ones.** If `φ` is monotone on `s` and `φ lo < u ≤ φ hi` for `lo, hi ∈ s`, then `u` lies in the
half-open image `(φ a, φ b]` of an interval `[a, b]` with endpoints in `s` and no point of `s`
inside it. -/
private lemma exists_consecutive (hφ : MonotoneOn φ s) {lo hi u : ℝ} (hlo : lo ∈ s) (hhi : hi ∈ s)
    (h₀ : φ lo < u) (h₁ : u ≤ φ hi) :
    ∃ a ∈ s, ∃ b ∈ s, a < b ∧ φ a < u ∧ u ≤ φ b ∧ ∀ g ∈ s, g ≤ a ∨ b ≤ g := by
  classical
  have hA : (s.filter fun g ↦ φ g < u).Nonempty := ⟨lo, mem_filter.mpr ⟨hlo, h₀⟩⟩
  have hB : (s.filter fun g ↦ u ≤ φ g).Nonempty := ⟨hi, mem_filter.mpr ⟨hhi, h₁⟩⟩
  obtain ⟨ha, hau⟩ := mem_filter.mp ((s.filter fun g ↦ φ g < u).max'_mem hA)
  obtain ⟨hb, hbu⟩ := mem_filter.mp ((s.filter fun g ↦ u ≤ φ g).min'_mem hB)
  refine ⟨_, ha, _, hb, lt_of_not_ge fun h ↦ ?_, hau, hbu, fun g hg ↦ ?_⟩
  · linarith [hφ hb ha h]
  · rcases lt_or_ge (φ g) u with h | h
    · exact .inl (le_max' _ g (mem_filter.mpr ⟨hg, h⟩))
    · exact .inr (min'_le _ g (mem_filter.mpr ⟨hg, h⟩))

end Axis

/-! ### The moved tiling -/

open Grid

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle} {φ ψ : ℝ → ℝ}

/-- **Moving the lines of a tiling in order gives a tiling.** If `φ` and `ψ` are monotone on the
coordinates of the vertical and the horizontal lines of a tiling of `R`, and the image of `R` is
not degenerate, then the images of the tiles, those that collapse pruned, tile the image of `R`.

A point of the half-open cell of the image of `R` lies between the images of two consecutive
vertical lines of the tiling and of two consecutive horizontal ones; the tile containing the
centre of the grid cell they bound reaches across that cell, so the half-open cell of its image
contains the point. And two tiles whose images share a point of their half-open cells overlap in
both directions, so they are the same tile. -/
theorem IsTiling.image (hT : IsTiling R T) (hφ : MonotoneOn φ (gridX R T))
    (hψ : MonotoneOn ψ (gridY R T)) (hx : φ R.x₀ < φ R.x₁) (hy : ψ R.y₀ < ψ R.y₁) :
    IsTiling (R.image φ ψ) (prune fun i ↦ (T i).image φ ψ) := by
  have hTx (i : ι) : φ (T i).x₀ ≤ φ (T i).x₁ :=
    hφ (tile_x₀_mem_gridX i) (tile_x₁_mem_gridX i) (T i).hx
  have hTy (i : ι) : ψ (T i).y₀ ≤ ψ (T i).y₁ :=
    hψ (tile_y₀_mem_gridY i) (tile_y₁_mem_gridY i) (T i).hy
  have hmem (i : ι) {u v : ℝ} :
      ((u, v) : ℝ × ℝ) ∈ ((T i).image φ ψ).toSetIoc ↔
        (φ (T i).x₀ < u ∧ u ≤ φ (T i).x₁) ∧ ψ (T i).y₀ < v ∧ v ≤ ψ (T i).y₁ := by
    rw [Rectangle.mem_toSetIoc', Rectangle.image_x₀ (hTx i), Rectangle.image_x₁ (hTx i),
      Rectangle.image_y₀ (hTy i), Rectangle.image_y₁ (hTy i)]
  refine isTiling_prune_of_toSetIoc ?_ ?_ (fun i ↦ ?_) (fun i j hij ↦ ?_) fun z hz ↦ ?_
  · rwa [Rectangle.image_x₀ hx.le, Rectangle.image_x₁ hx.le]
  · rwa [Rectangle.image_y₀ hy.le, Rectangle.image_y₁ hy.le]
  · -- an image tile lies in the image of `R`
    rintro ⟨u, v⟩ ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    rw [Rectangle.image_x₀ (hTx i)] at h₁
    rw [Rectangle.image_x₁ (hTx i)] at h₂
    rw [Rectangle.image_y₀ (hTy i)] at h₃
    rw [Rectangle.image_y₁ (hTy i)] at h₄
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      simp only [Rectangle.image_x₀ hx.le, Rectangle.image_x₁ hx.le, Rectangle.image_y₀ hy.le,
        Rectangle.image_y₁ hy.le]
    · exact (hφ left_mem_gridX (tile_x₀_mem_gridX i) (hT.le_tile_x₀ i)).trans h₁
    · exact h₂.trans (hφ (tile_x₁_mem_gridX i) right_mem_gridX (hT.tile_x₁_le i))
    · exact (hψ bot_mem_gridY (tile_y₀_mem_gridY i) (hT.le_tile_y₀ i)).trans h₃
    · exact h₄.trans (hψ (tile_y₁_mem_gridY i) top_mem_gridY (hT.tile_y₁_le i))
  · -- two image tiles sharing a point of their half-open cells come from overlapping tiles
    refine Set.disjoint_left.mpr fun ⟨u, v⟩ hi hj ↦ ?_
    obtain ⟨hui, hvi⟩ := (hmem i).mp hi
    obtain ⟨huj, hvj⟩ := (hmem j).mp hj
    have hxo := max_lt_min hφ (tile_x₀_mem_gridX i) (tile_x₁_mem_gridX i) (tile_x₀_mem_gridX j)
      (tile_x₁_mem_gridX j) (hT.tile_x₀_lt_x₁ i) (hT.tile_x₀_lt_x₁ j) hui huj
    have hyo := max_lt_min hψ (tile_y₀_mem_gridY i) (tile_y₁_mem_gridY i) (tile_y₀_mem_gridY j)
      (tile_y₁_mem_gridY j) (hT.tile_y₀_lt_y₁ i) (hT.tile_y₀_lt_y₁ j) hvi hvj
    simp only [max_lt_iff, lt_min_iff] at hxo hyo
    exact Set.disjoint_left.mp (hT.interiorDisjoint hij)
      (Rectangle.mem_interior_toSet (z := ((max (T i).x₀ (T j).x₀ + min (T i).x₁ (T j).x₁) / 2,
        (max (T i).y₀ (T j).y₀ + min (T i).y₁ (T j).y₁) / 2)) (by grind))
      (Rectangle.mem_interior_toSet (by grind))
  · -- a point of the image of `R` lies in the image of the tile across its grid cell
    obtain ⟨u, v⟩ := z
    obtain ⟨⟨hu₀, hu₁⟩, hv₀, hv₁⟩ := hz
    rw [Rectangle.image_x₀ hx.le] at hu₀
    rw [Rectangle.image_x₁ hx.le] at hu₁
    rw [Rectangle.image_y₀ hy.le] at hv₀
    rw [Rectangle.image_y₁ hy.le] at hv₁
    obtain ⟨a, ha, b, hb, hab, hau, hbu, hgx⟩ :=
      exists_consecutive hφ left_mem_gridX right_mem_gridX hu₀ hu₁
    obtain ⟨c, hc, d, hd, hcd, hcv, hdv, hgy⟩ :=
      exists_consecutive hψ bot_mem_gridY top_mem_gridY hv₀ hv₁
    have hw : (((a + b) / 2, (c + d) / 2) : ℝ × ℝ) ∈ R.toSet := by
      have := gridX_mem_Icc hT ha
      have := gridX_mem_Icc hT hb
      have := gridY_mem_Icc hT hc
      have := gridY_mem_Icc hT hd
      exact Rectangle.mem_toSet.mpr ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT.cover.subset hw)
    obtain ⟨⟨hi₀, hi₁⟩, hi₂, hi₃⟩ := Rectangle.mem_toSet.mp hi
    have hxa : (T i).x₀ ≤ a := (hgx _ (tile_x₀_mem_gridX i)).resolve_right fun h ↦ by
      dsimp only at hi₀; linarith
    have hxb : b ≤ (T i).x₁ := (hgx _ (tile_x₁_mem_gridX i)).resolve_left fun h ↦ by
      dsimp only at hi₁; linarith
    have hyc : (T i).y₀ ≤ c := (hgy _ (tile_y₀_mem_gridY i)).resolve_right fun h ↦ by
      dsimp only at hi₂; linarith
    have hyd : d ≤ (T i).y₁ := (hgy _ (tile_y₁_mem_gridY i)).resolve_left fun h ↦ by
      dsimp only at hi₃; linarith
    exact Set.mem_iUnion.mpr ⟨i, (hmem i).mpr
      ⟨⟨(hφ (tile_x₀_mem_gridX i) ha hxa).trans_lt hau,
          hbu.trans (hφ hb (tile_x₁_mem_gridX i) hxb)⟩,
        (hψ (tile_y₀_mem_gridY i) hc hyc).trans_lt hcv,
        hdv.trans (hψ hd (tile_y₁_mem_gridY i) hyd)⟩⟩

/-- **The areas of the moved tiles add up to the area of the moved rectangle**, area being
additive over the moved tiling (`IsTiling.image`, `IsTiling.sum_area`); a collapsed tile has no
area. -/
theorem IsTiling.sum_area_image (hT : IsTiling R T) (hφ : MonotoneOn φ (gridX R T))
    (hψ : MonotoneOn ψ (gridY R T)) (hx : φ R.x₀ < φ R.x₁) (hy : ψ R.y₀ < ψ R.y₁) :
    ∑ i, (φ (T i).x₁ - φ (T i).x₀) * (ψ (T i).y₁ - ψ (T i).y₀) =
      (φ R.x₁ - φ R.x₀) * (ψ R.y₁ - ψ R.y₀) := by
  have h := (hT.image hφ hψ hx hy).sum_area
  rw [sum_prune _ fun _ ↦ Rectangle.area_eq_zero_of_not_nondegenerate,
    Rectangle.area_image hx.le hy.le] at h
  rw [← h]
  exact sum_congr rfl fun i _ ↦ (Rectangle.area_image
    (hφ (tile_x₀_mem_gridX i) (tile_x₁_mem_gridX i) (T i).hx)
    (hψ (tile_y₀_mem_gridY i) (tile_y₁_mem_gridY i) (T i).hy)).symm

end IntegerRectangle
