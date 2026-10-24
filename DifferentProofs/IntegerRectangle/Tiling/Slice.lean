module

public import DifferentProofs.IntegerRectangle.Tiling.Cells
public import DifferentProofsForMathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
# Slicing a tiling along a horizontal line

A horizontal line through a tiling that misses every horizontal tile edge crosses the interiors of
the tiles it meets, so their traces on it overlap only at endpoints, and they cover the full width
of the tiled rectangle: the widths of those tiles add up to the width of `R` (`widthSum_slice`).
This is the geometric ingredient of the sweep-line proof, which sweeps such a line up through the
tiling.

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

lemma widthSum_nonneg (T : ι → Rectangle) (p : ι → Prop) : 0 ≤ widthSum T p :=
  Finset.sum_nonneg fun i _ ↦ by split_ifs <;> simp [Rectangle.width_nonneg]

open scoped Classical in
/-- Two width sums agree when their predicates do. -/
lemma widthSum_congr (h : ∀ i, p i ↔ q i) : widthSum T p = widthSum T q :=
  Finset.sum_congr rfl fun i _ ↦ if_congr (h i) rfl rfl

/-- Splitting a width sum along a disjoint case distinction. -/
lemma widthSum_split (h : ∀ i, p i ↔ q i ∨ r i) (hd : ∀ i, ¬(q i ∧ r i)) :
    widthSum T p = widthSum T q + widthSum T r :=
  (Finset.sum_congr rfl fun i _ ↦ by grind).trans Finset.sum_add_distrib

/-- A width sum over an empty selection vanishes. -/
lemma widthSum_eq_zero (h : ∀ i, ¬ p i) : widthSum T p = 0 :=
  Finset.sum_eq_zero fun i _ ↦ ite_eq_right (h i)

/-- A width sum over H-tiles is an integer. -/
lemma widthSum_isInt (h : ∀ i, p i → (T i).IsHTile) :
    ∃ n : ℤ, widthSum T p = n := by
  classical
  choose! n hn using h
  refine ⟨∑ i, if p i then n i else 0, ?_⟩
  push_cast
  grind [widthSum]

end WidthSum

/-! ### The horizontal edges of a tiling -/

/-- The set of heights at which some tile has a horizontal edge. -/
def edgeSet (T : ι → Rectangle) : Set ℝ :=
  (Set.range fun i ↦ (T i).y₀) ∪ (Set.range fun i ↦ (T i).y₁)

lemma tile_y₀_mem_edgeSet (T : ι → Rectangle) (i : ι) : (T i).y₀ ∈ edgeSet T :=
  Or.inl ⟨i, rfl⟩

lemma tile_y₁_mem_edgeSet (T : ι → Rectangle) (i : ι) : (T i).y₁ ∈ edgeSet T :=
  Or.inr ⟨i, rfl⟩

/-! ### Slicing a tiling along a horizontal line -/

/-- The trace of tile `i` on the horizontal line at height `t`, declared empty unless the line
crosses the tile's interior. -/
private def slice (T : ι → Rectangle) (t : ℝ) (i : ι) : Set ℝ :=
  {x | (T i).y₀ < t ∧ t < (T i).y₁ ∧ (T i).x₀ ≤ x ∧ x ≤ (T i).x₁}

private lemma slice_eq_Icc {t : ℝ} {i : ι} (h : (T i).y₀ < t ∧ t < (T i).y₁) :
    slice T t i = Icc (T i).x₀ (T i).x₁ := by
  ext x
  simp [slice, h.1, h.2, Set.mem_Icc]

private lemma slice_eq_empty {t : ℝ} {i : ι} (h : ¬((T i).y₀ < t ∧ t < (T i).y₁)) :
    slice T t i = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hx ↦ h ⟨hx.1, hx.2.1⟩

/-- **The slice lemma.** Cut a tiling along a horizontal line `y = t` that lies inside the tiled
rectangle and misses every tile edge. The line crosses the interiors of the tiles it meets, so their
traces on it have pairwise-disjoint interiors and cover the full width of the tiled rectangle;
hence the widths of those tiles add up to the width of the tiled rectangle. -/
theorem widthSum_slice [Fintype ι] (hT : IsTiling R T) {t : ℝ} (ht₀ : R.y₀ ≤ t)
    (ht₁ : t ≤ R.y₁) (hgen : t ∉ edgeSet T) :
    widthSum T (fun i ↦ (T i).y₀ < t ∧ t < (T i).y₁) = R.width := by
  classical
  have hcross : ∀ i, ((T i).y₀ ≤ t ∧ t ≤ (T i).y₁) ↔ ((T i).y₀ < t ∧ t < (T i).y₁) := fun i ↦ by
    grind [tile_y₀_mem_edgeSet T i, tile_y₁_mem_edgeSet T i]
  have hunion : ⋃ i, slice T t i = Icc R.x₀ R.x₁ := by
    ext x
    simp only [mem_iUnion]
    refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun hx ↦ ?_⟩
    · exact (Rectangle.mem_toSet.mp (hT.tile_subset i (show (x, t) ∈ (T i).toSet from
        Rectangle.mem_toSet.mpr ⟨⟨hi.2.2.1, hi.2.2.2⟩, ⟨hi.1.le, hi.2.1.le⟩⟩))).1
    · have hz : (x, t) ∈ R.toSet := Rectangle.mem_toSet.mpr ⟨⟨hx.1, hx.2⟩, ⟨ht₀, ht₁⟩⟩
      rw [hT.cover] at hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      obtain ⟨hxi, hti⟩ := Rectangle.mem_toSet.mp hi
      exact ⟨i, ((hcross i).mp hti).1, ((hcross i).mp hti).2, hxi.1, hxi.2⟩
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) (slice T t)) := by
    intro i j hij
    change volume (slice T t i ∩ slice T t j) = 0
    by_cases hi : (T i).y₀ < t ∧ t < (T i).y₁
    · by_cases hj : (T j).y₀ < t ∧ t < (T j).y₁
      · rw [slice_eq_Icc hi, slice_eq_Icc hj]
        refine aedisjoint_Icc_of_disjoint_Ioo (Set.disjoint_left.mpr fun x hx hx' ↦ ?_)
        exact Set.disjoint_left.mp (hT.interiorDisjoint hij)
          (Rectangle.mem_interior_toSet (z := (x, t)) ⟨⟨hx.1, hx.2⟩, hi⟩)
          (Rectangle.mem_interior_toSet (z := (x, t)) ⟨⟨hx'.1, hx'.2⟩, hj⟩)
      · rw [slice_eq_empty hj, Set.inter_empty, measure_empty]
    · rw [slice_eq_empty hi, Set.empty_inter, measure_empty]
  have hnull : ∀ i, NullMeasurableSet (slice T t i) volume := fun i ↦ by
    by_cases hi : (T i).y₀ < t ∧ t < (T i).y₁
    · rw [slice_eq_Icc hi]
      exact measurableSet_Icc.nullMeasurableSet
    · rw [slice_eq_empty hi]
      exact MeasurableSet.empty.nullMeasurableSet
  have hvolR : volume (Icc R.x₀ R.x₁) = ENNReal.ofReal R.width := Real.volume_Icc
  refine (ENNReal.ofReal_eq_ofReal_iff (widthSum_nonneg T _) R.width_nonneg).mp ?_.symm
  rw [widthSum,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by split_ifs <;> simp [Rectangle.width_nonneg],
    ← hvolR, ← hunion, measure_iUnion₀ hdisj hnull, tsum_fintype]
  exact Finset.sum_congr rfl fun i _ ↦ by
    split_ifs with h <;> simp [slice_eq_Icc, slice_eq_empty, h, Real.volume_Icc, Rectangle.width]

/-! ### Tilings by H-tiles, or by V-tiles -/

/-- **A tiling by H-tiles tiles a rectangle of integer width.** A horizontal line through `R`
missing the horizontal edges of the tiles crosses tiles of integer width, which span the width of
`R` (`widthSum_slice`). -/
theorem intWidth_of_forall [Fintype ι] (hT : IsTiling R T) (h : ∀ i, (T i).IsHTile) :
    R.IsHTile := by
  obtain ⟨t, ⟨ht₀, ht₁⟩, ht⟩ : ∃ t ∈ Ioo R.y₀ R.y₁, t ∉ edgeSet T :=
    ((Ioo_infinite hT.y₀_lt_y₁).sdiff ((finite_range _).union (finite_range _))).nonempty
  obtain ⟨n, hn⟩ := widthSum_isInt (T := T) (p := fun i ↦ (T i).y₀ < t ∧ t < (T i).y₁)
    fun i _ ↦ h i
  exact ⟨n, (widthSum_slice hT ht₀.le ht₁.le ht).symm.trans hn⟩

/-- **A tiling by V-tiles tiles a rectangle of integer height**: transposed, it is a tiling by
H-tiles. -/
theorem intHeight_of_forall [Fintype ι] (hT : IsTiling R T) (h : ∀ i, (T i).IsVTile) :
    R.IsVTile :=
  intWidth_of_forall hT.transpose h

end IntegerRectangle
