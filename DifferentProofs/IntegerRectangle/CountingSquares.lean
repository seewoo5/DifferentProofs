module

public import DifferentProofs.IntegerRectangle.Tiling.Image
public import DifferentProofsForMathlib.Algebra.Order.Floor.Ring

/-!
# The integer-rectangle theorem by counting squares

Wagon's fourth proof, due to Imre Z. Ruzsa and to Peter Gilbert. Place `R` in standard position
and build an auxiliary tiling of a possibly new rectangle `R'` by translating the lines of the
tiling: a vertical line `x = a` with `a` an integer is not moved, and one with `a` not an integer
is moved to the half-integer line `x = ⌊a⌋ + 1/2`, and likewise for the horizontal lines. This may
reduce the number of tiles, which is unimportant. If neither side of `R` were an integer, `R'`
would be a rectangle in standard position with both sides equal to half an odd integer, and so it
would contain an odd number of the `1/2 × 1/2` squares of the checkerboard of the third proof. But
a tile with an integer side keeps that side integral under the translation, so each tile of `R'`
contains an even number of squares.

The lattice is based at the lower-left corner of `R` instead of the origin, which replaces the
standard position. Twice the translated coordinate of `x`, measured from the base point `a`, is
the integer

```
cellIndex a x = ⌊x - a⌋ + ⌈x - a⌉,
```

the number of half-unit steps from `a` to the translated `x`; it is even exactly when `x - a` is
an integer (`even_cellIndex_iff`). The translation `translate a` keeps the order of the lines, so
the translated tiles tile `R'` (`IsTiling.image`). The squares in a rectangle are counted by their
upper right corners (`squares`), and every square of `R'` lies in exactly one of its tiles, which
is the exact partition of a tiling into half-open cells (`card_squares_eq_sum`). The number of
squares of a translated rectangle is the product of the increments of `cellIndex` across its two
sides (`card_squares_image`).

## Main result

- `IntegerRectangleTheorem_CountingSquares`: Ruzsa's counting-squares proof of the
  integer-rectangle theorem.
-/

@[expose] public section

open Finset

namespace IntegerRectangle.CountingSquares

/-! ### Translating the lines of the tiling -/

/-- The coordinate of `x` on the half-unit grid based at `a`, counted in half-steps: `x` is
translated to `a + ⌊x - a⌋ + 1/2` unless it already sits an integer distance from `a`, in which
case it stays put, and `cellIndex a x` is twice the resulting offset from `a`. -/
noncomputable def cellIndex (a x : ℝ) : ℤ := ⌊x - a⌋ + ⌈x - a⌉

/-- The translation of the lines of the tiling, onto the half-unit grid based at `a`. -/
noncomputable def translate (a x : ℝ) : ℝ := a + cellIndex a x / 2

private lemma cellIndex_self (a : ℝ) : cellIndex a a = 0 := by simp [cellIndex]

private lemma cellIndex_mono (a : ℝ) : Monotone (cellIndex a) := fun _ _ h ↦
  add_le_add (Int.floor_mono (sub_le_sub_right h a)) (Int.ceil_mono (sub_le_sub_right h a))

/-- The translation keeps the order of the lines. -/
lemma monotone_translate (a : ℝ) : Monotone (translate a) := fun _ _ h ↦ by
  have : (cellIndex a _ : ℝ) ≤ cellIndex a _ := Int.cast_le.mpr (cellIndex_mono a h)
  simp only [translate]
  linarith

/-- **The parity criterion.** A grid coordinate is even exactly when the point sits an integer
distance from the base point — the translation moves it to a half-integer line otherwise. -/
theorem even_cellIndex_iff {a x : ℝ} : Even (cellIndex a x) ↔ ∃ n : ℤ, x - a = n := by
  have hle := Int.floor_le_ceil (x - a)
  have hlt := Int.ceil_le_floor_add_one (x - a)
  rw [show (∃ n : ℤ, x - a = (n : ℝ)) ↔ ⌈x - a⌉ = ⌊x - a⌋ by
    simp [Int.ceil_eq_floor_iff_mem, eq_comm], cellIndex, Int.even_iff]
  lia

/-- A side of integer length has an even increment of grid coordinates: the translation shifts
both of its endpoints onto the grid without changing their distance. -/
private lemma even_cellIndex_sub (a : ℝ) {u v : ℝ} {n : ℤ} (h : v - u = n) :
    Even (cellIndex a v - cellIndex a u) := by
  have hv : v - a = u - a + (n : ℝ) := by rw [← h]; ring
  exact ⟨n, by simp only [cellIndex, hv, Int.floor_add_intCast, Int.ceil_add_intCast]; ring⟩

/-! ### Counting squares -/

/-- The squares of the half-unit grid based at `(a, b)` lying in `S`, counted by their upper right
corners: the pair `(j, k)` stands for the square with upper right corner `(a + j/2, b + k/2)`,
and is counted when that corner lies in the half-open cell of `S`. For a rectangle whose edges are
grid lines, these are exactly the squares inside it. -/
noncomputable def squares (a b : ℝ) (S : Rectangle) : Finset (ℤ × ℤ) :=
  Ioc ⌊2 * (S.x₀ - a)⌋ ⌊2 * (S.x₁ - a)⌋ ×ˢ Ioc ⌊2 * (S.y₀ - b)⌋ ⌊2 * (S.y₁ - b)⌋

/-- A square is counted in `S` exactly when its upper right corner lies in the half-open cell
of `S`. -/
private lemma mem_squares {a b : ℝ} {S : Rectangle} {k : ℤ × ℤ} :
    k ∈ squares a b S ↔ ((a + k.1 / 2, b + k.2 / 2) : ℝ × ℝ) ∈ S.toSetIoc := by
  simp only [squares, mem_product, mem_Ioc, Rectangle.mem_toSetIoc', Int.floor_lt, Int.le_floor]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **Every square lies in exactly one tile.** The half-open cells of the tiles partition that of
`R` (`IsTiling.iUnion_toSetIoc`, `IsTiling.pairwiseDisjoint_toSetIoc`), so the squares of `R` are
those of its tiles, each counted once. -/
theorem card_squares_eq_sum (hT : IsTiling R T) (a b : ℝ) :
    #(squares a b R) = ∑ i, #(squares a b (T i)) := by
  classical
  rw [show squares a b R = univ.biUnion fun i ↦ squares a b (T i) from ext fun k ↦ by
      simp only [mem_biUnion, mem_univ, true_and, mem_squares, ← Set.mem_iUnion,
        hT.iUnion_toSetIoc],
    card_biUnion fun i _ j _ hij ↦ disjoint_left.mpr fun k hi hj ↦
      Set.disjoint_left.mp (hT.pairwiseDisjoint_toSetIoc hij) (mem_squares.mp hi)
        (mem_squares.mp hj)]

/-- The number of squares of the half-unit grid based at `(a, b)` in the translation of a
rectangle: the product of the increments of the grid coordinates across its two sides. -/
noncomputable def cellCount (a b : ℝ) (S : Rectangle) : ℤ :=
  (cellIndex a S.x₁ - cellIndex a S.x₀) * (cellIndex b S.y₁ - cellIndex b S.y₀)

/-- **The squares of a translated rectangle**: its edges are grid lines, and it contains as many
squares as the product of the increments of the grid coordinates across its sides. -/
theorem card_squares_image (a b : ℝ) (S : Rectangle) :
    (#(squares a b (S.image (translate a) (translate b))) : ℤ) = cellCount a b S := by
  have hx := monotone_translate a S.hx
  have hy := monotone_translate b S.hy
  have hcx := cellIndex_mono a S.hx
  have hcy := cellIndex_mono b S.hy
  have hfl (c x : ℝ) : ⌊2 * (translate c x - c)⌋ = cellIndex c x := by
    rw [translate, add_sub_cancel_left, mul_div_cancel₀ _ two_ne_zero, Int.floor_intCast]
  rw [squares, Rectangle.image_x₀ hx, Rectangle.image_x₁ hx, Rectangle.image_y₀ hy,
    Rectangle.image_y₁ hy, hfl, hfl, hfl, hfl, card_product, Int.card_Ioc, Int.card_Ioc,
    Nat.cast_mul, Int.toNat_of_nonneg (sub_nonneg.mpr hcx),
    Int.toNat_of_nonneg (sub_nonneg.mpr hcy), cellCount]

/-- **The squares of `R'` are those of its tiles.** The translated tiles tile the translated
rectangle `R'` (`IsTiling.image`), and every square of `R'` lies in exactly one of them
(`card_squares_eq_sum`); a tile collapsed by the translation has no square. -/
theorem sum_cellCount (hT : IsTiling R T) :
    ∑ i, cellCount R.x₀ R.y₀ (T i) = cellCount R.x₀ R.y₀ R := by
  have hpos (a x : ℝ) (h : a < x) : translate a a < translate a x := by
    have h₁ : 0 < ⌈x - a⌉ := Int.ceil_pos.mpr (sub_pos.mpr h)
    have h₀ : 0 ≤ ⌊x - a⌋ := Int.floor_nonneg.mpr (sub_nonneg.mpr h.le)
    have : (0 : ℝ) < cellIndex a x := Int.cast_pos.mpr (by rw [cellIndex]; lia)
    rw [translate, translate, cellIndex_self, Int.cast_zero, zero_div, add_zero]
    linarith
  have h := card_squares_eq_sum (hT.image ((monotone_translate R.x₀).monotoneOn _)
    ((monotone_translate R.y₀).monotoneOn _) (hpos _ _ hT.x₀_lt_x₁)
    (hpos _ _ hT.y₀_lt_y₁)) R.x₀ R.y₀
  rw [sum_prune (f := fun S ↦ #(squares R.x₀ R.y₀ S)) _ fun S hS ↦ ?_] at h
  · rw [← card_squares_image, h, Nat.cast_sum]
    exact sum_congr rfl fun i _ ↦ (card_squares_image _ _ _).symm
  · rw [Rectangle.Nondegenerate, not_and_or, not_lt, not_lt] at hS
    refine card_eq_zero.mpr (eq_empty_of_forall_notMem fun k hk ↦ ?_)
    obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := mem_squares.mp hk
    dsimp only at h₁ h₂ h₃ h₄
    rcases hS with hS | hS <;> linarith

end IntegerRectangle.CountingSquares

open IntegerRectangle IntegerRectangle.CountingSquares in
/-- **Counting-squares proof** (Ruzsa, Gilbert) of the integer-rectangle tiling theorem. Base the
half-unit grid at the lower-left corner of `R`. Every tile has an integer side, so its translation
contains an even number of squares, and therefore so does the translation of `R`. The corner of
`R` has grid coordinate `0`, so the square count of the translation of `R` is the product of the
grid coordinates of its two far edges; one of them is even, which says that the corresponding
side of `R` has integer length. -/
theorem IntegerRectangleTheorem_CountingSquares : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  have hR : Even (cellCount R.x₀ R.y₀ R) := by
    rw [← sum_cellCount hT]
    refine Finset.even_sum _ fun i _ ↦ (hsides i).elim
      (fun ⟨n, hw⟩ ↦ (even_cellIndex_sub R.x₀ (by simpa [Rectangle.width] using hw)).mul_right _)
      fun ⟨n, hh⟩ ↦ (even_cellIndex_sub R.y₀ (by simpa [Rectangle.height] using hh)).mul_left _
  simpa only [Rectangle.HasIntegerSide, Rectangle.width, Rectangle.height, cellCount,
    cellIndex_self, sub_zero, Int.even_mul, even_cellIndex_iff] using hR
