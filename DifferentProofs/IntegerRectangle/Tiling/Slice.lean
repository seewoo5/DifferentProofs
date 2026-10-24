module

public import DifferentProofs.IntegerRectangle.Tiling.Cells

/-!
# Slicing a tiling along a horizontal line

A horizontal line through a tiling that misses every horizontal tile edge crosses the interiors of
the tiles it meets, and their traces on it, less their left endpoints, partition the trace of the
tiled rectangle less its left endpoint: the widths of those tiles add up to the width of `R`
(`widthSum_slice`). This is the geometric ingredient of the sweep-line proof, which sweeps such a
line up through the tiling.

It also settles a tiling all of whose tiles are H-tiles: the widths crossed by such a line are then
integers, so the width of `R` is one (`intWidth_of_forall`), and transposed, a tiling by V-tiles
has integer height (`intHeight_of_forall`). These are the cases the two inductive proofs treat as
immediate.
-/

@[expose] public section

open MeasureTheory Set

namespace IntegerRectangle

variable {ι : Type} {R : Rectangle} {T : ι → Rectangle} {p q r : ι → Prop}

/-! ### Sums of tile widths -/

section WidthSum

variable [Fintype ι]

open scoped Classical in
/-- The total width of the tiles satisfying `p`. -/
noncomputable def widthSum (T : ι → Rectangle) (p : ι → Prop) : ℝ :=
  ∑ i, if p i then (T i).width else 0

/-- A width sum is nonnegative. -/
lemma widthSum_nonneg (T : ι → Rectangle) (p : ι → Prop) : 0 ≤ widthSum T p :=
  Finset.sum_nonneg fun i _ ↦ by grind [Rectangle.width_nonneg]

/-- Two width sums agree when their predicates do. -/
lemma widthSum_congr (h : ∀ i, p i ↔ q i) : widthSum T p = widthSum T q :=
  congrArg (widthSum T) <| funext fun i ↦ propext (h i)

/-- Splitting a width sum along a disjoint case distinction. -/
lemma widthSum_split (h : ∀ i, p i ↔ q i ∨ r i) (hd : ∀ i, ¬(q i ∧ r i)) :
    widthSum T p = widthSum T q + widthSum T r :=
  (Finset.sum_congr rfl fun i _ ↦ by grind).trans Finset.sum_add_distrib

/-- A width sum over an empty selection vanishes. -/
lemma widthSum_eq_zero (h : ∀ i, ¬ p i) : widthSum T p = 0 :=
  Finset.sum_eq_zero fun i _ ↦ ite_eq_right (h i)

/-- A width sum over H-tiles is an integer. -/
lemma widthSum_isInt (h : ∀ i, p i → (T i).IsHTile) : ∃ n : ℤ, widthSum T p = n := by
  classical
  choose! n hn using h
  exact ⟨∑ i, if p i then n i else 0, by push_cast; grind [widthSum]⟩

end WidthSum

/-! ### The horizontal edges of a tiling -/

/-- The set of heights at which some tile has a horizontal edge. -/
def edgeSet (T : ι → Rectangle) : Set ℝ := (range fun i ↦ (T i).y₀) ∪ range fun i ↦ (T i).y₁

/-- The bottom edge of a tile is at a height in `edgeSet`. -/
lemma tile_y₀_mem_edgeSet (T : ι → Rectangle) (i : ι) : (T i).y₀ ∈ edgeSet T := Or.inl ⟨i, rfl⟩

/-- The top edge of a tile is at a height in `edgeSet`. -/
lemma tile_y₁_mem_edgeSet (T : ι → Rectangle) (i : ι) : (T i).y₁ ∈ edgeSet T := Or.inr ⟨i, rfl⟩

/-- Finitely many tiles have finitely many horizontal edges. -/
lemma finite_edgeSet [Finite ι] (T : ι → Rectangle) : (edgeSet T).Finite :=
  (finite_range _).union (finite_range _)

/-! ### Slicing a tiling along a horizontal line -/

/-- **The slice lemma.** Cut a tiling along a horizontal line `y = t` that lies inside the tiled
rectangle and misses every horizontal tile edge: the widths of the tiles the line crosses add up to
the width of the tiled rectangle.

Length along the line, the measure `volume.prod (Measure.dirac t)`, adds up over the half-open
cells of the tiles, like every measure (`IsTiling.measure_toSetIoc`). The line meets the cell of a
tile, in an interval of the tile's width, exactly when it crosses the tile, as `t` is not a top
edge; and it meets the cell of `R` in an interval of the full width, as it is not the bottom edge
of `R` either: the tile containing `(R.x₀, t)` reaches below it. -/
theorem widthSum_slice [Fintype ι] (hT : IsTiling R T) {t : ℝ} (ht₀ : R.y₀ ≤ t) (ht₁ : t ≤ R.y₁)
    (hgen : t ∉ edgeSet T) : widthSum T (fun i ↦ (T i).y₀ < t ∧ t < (T i).y₁) = R.width := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hT.cover.subset ⟨⟨le_rfl, R.hx⟩, ht₀, ht₁⟩ : (R.x₀, t) ∈ _)
  have ht₀' : R.y₀ < t := by grind [hT.le_tile_y₀ i, tile_y₀_mem_edgeSet T i, hi.2.1]
  rw [← ENNReal.ofReal_eq_ofReal_iff (widthSum_nonneg T _) R.width_nonneg, widthSum,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by grind [Rectangle.width_nonneg]]
  simpa only [Rectangle.width, apply_ite ENNReal.ofReal, ENNReal.ofReal_zero, Rectangle.toSetIoc,
    Measure.prod_prod, Real.volume_Ioc, Measure.dirac_apply, indicator_apply, mem_Ioc,
    (ne_of_mem_of_not_mem (tile_y₁_mem_edgeSet T _) hgen).symm.le_iff_lt, Pi.one_apply, mul_boole,
    ht₀', ht₁, and_self, ite_true, mul_one] using
    (hT.measure_toSetIoc (volume.prod (Measure.dirac t))).symm

/-! ### Tilings by H-tiles, or by V-tiles -/

/-- **A tiling by H-tiles tiles a rectangle of integer width.** A horizontal line through `R`
missing the horizontal edges of the tiles crosses tiles of integer width, which span the width of
`R` (`widthSum_slice`). -/
theorem intWidth_of_forall [Fintype ι] (hT : IsTiling R T) (h : ∀ i, (T i).IsHTile) : R.IsHTile :=
  have ⟨_, ⟨ht₀, ht₁⟩, ht⟩ : ∃ t ∈ Ioo R.y₀ R.y₁, t ∉ edgeSet T :=
    (Ioo_infinite hT.y₀_lt_y₁).exists_notMem_finite (finite_edgeSet T)
  (widthSum_isInt fun i _ ↦ h i).imp fun _ ↦ (widthSum_slice hT ht₀.le ht₁.le ht).symm.trans

/-- **A tiling by V-tiles tiles a rectangle of integer height**: transposed, it is a tiling by
H-tiles. -/
theorem intHeight_of_forall [Fintype ι] (hT : IsTiling R T) (h : ∀ i, (T i).IsVTile) : R.IsVTile :=
  intWidth_of_forall hT.transpose h

end IntegerRectangle
