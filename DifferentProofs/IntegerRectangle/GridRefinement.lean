module

public import DifferentProofs.IntegerRectangle.Grid
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The grid refinement of a tiling, and additivity of the fg-area

Wagon's step-function proof rides on an additivity lemma stated for an *arbitrary* pair of
functions `f, g : ℝ → ℝ`, with no regularity whatsoever. Call

```
fgArea f g S = (f S.x₁ - f S.x₀) · (g S.y₁ - g S.y₀)
```

the *fg-area* of a rectangle, Wagon's name for the `f = g` case; the Lean name `fgArea` records
that each axis gets its own function. The fg-area is additive over a tiling:
`IsTiling.sum_fgArea`.

The proof is Wagon's, and rides on the grid spanned by the tiling
(`DifferentProofs.IntegerRectangle.Grid`): every open grid cell lies in a unique tile
(`Grid.cellTile`), and the cells of a tile fill out a product of index intervals
(`Grid.cellTile_eq_iff`). Summing the fg-area of the cells therefore counts every cell exactly
once, tile by tile, and over a product of index intervals the sum telescopes in both coordinates
— giving the tile's fg-area, and, over the whole grid, the fg-area of `R`.
-/

@[expose] public section

open Finset Set

namespace IntegerRectangle

/-- The *fg-area* of a rectangle in the sense of Wagon — with a separate function per axis, whence
the name: the increment of `f` across the width times the increment of `g` across the height. For
`f = g = id` it is the usual area; for `f = g = Int.fract` it is the quantity driving the
step-function proof. Its virtue is additivity over a tiling (`IsTiling.sum_fgArea`) for
completely arbitrary `f` and `g`. -/
noncomputable def fgArea (f g : ℝ → ℝ) (S : Rectangle) : ℝ :=
  (f S.x₁ - f S.x₀) * (g S.y₁ - g S.y₀)

namespace GridRefinement

/-- Double telescoping: summing the product of consecutive differences over a product of index
intervals gives the product of the end differences. -/
private lemma sum_product_sub (F G : ℕ → ℝ) {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∑ p ∈ Finset.Ico a b ×ˢ Finset.Ico c d,
      (F (p.1 + 1) - F p.1) * (G (p.2 + 1) - G p.2) = (F b - F a) * (G d - G c) :=
  ((Finset.sum_product _ _ _).trans
    (Finset.sum_mul_sum (Finset.Ico a b) (Finset.Ico c d)
      (fun j ↦ F (j + 1) - F j) (fun k ↦ G (k + 1) - G k)).symm).trans
    (by rw [sum_Ico_sub F hab, sum_Ico_sub G hcd])

end GridRefinement

/-! ### Additivity of the fg-area -/

open Grid GridRefinement in
/-- **The fg-area is additive over a tiling** (Wagon, after Hochster and Maté), for arbitrary
`f, g : ℝ → ℝ`: summing `(f x₁ - f x₀) · (g y₁ - g y₀)` over the tiles of a tiling gives the
same quantity for the tiled rectangle. The tile edges span a grid; every open grid cell lies in
exactly one tile, the cells of a tile fill a product of index intervals, and the sum telescopes
in both coordinates. -/
theorem IsTiling.sum_fgArea {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}
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

/-! ### Tilings by tiles all of one designation -/

/-- **A tiling all of whose tiles have integer width tiles a rectangle of integer width.** The
fg-area for the fractional part horizontally and the identity vertically vanishes on every tile,
hence on `R`. -/
theorem intWidth_of_forall {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}
    (hT : IsTiling R T) (hy : R.y₀ < R.y₁)
    (h : ∀ i, ∃ m : ℤ, (T i).width = m) : ∃ m : ℤ, R.width = m := by
  have key := hT.sum_fgArea Int.fract id
  rw [Finset.sum_eq_zero fun i _ ↦ ?_] at key
  · rw [fgArea] at key
    exact Int.fract_eq_fract.mp (by
      have : Int.fract R.x₁ - Int.fract R.x₀ = 0 := by
        rcases mul_eq_zero.mp key.symm with h' | h'
        · exact h'
        · simp only [id] at h'; linarith
      linarith)
  · obtain ⟨m, hm⟩ := h i
    rw [fgArea, Int.fract_eq_fract.mpr ⟨m, by simpa [Rectangle.width] using hm⟩, sub_self,
      zero_mul]

/-- **A tiling all of whose tiles have integer height tiles a rectangle of integer height.** -/
theorem intHeight_of_forall {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}
    (hT : IsTiling R T) (hx : R.x₀ < R.x₁)
    (h : ∀ i, ∃ m : ℤ, (T i).height = m) : ∃ m : ℤ, R.height = m :=
  intWidth_of_forall hT.transpose hx h

end IntegerRectangle
