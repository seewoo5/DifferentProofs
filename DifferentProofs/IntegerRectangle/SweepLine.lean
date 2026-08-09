module

public import DifferentProofs.IntegerRectangle.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The integer-rectangle theorem via a sweep line

Wagon's twelfth proof (Gennady Bachman, Mihalis Yannakakis). Suppose the tiled rectangle `R` has
non-integer height, and run a horizontal line upward through the tiling, recording at each height
`t` the number

```
f(t) = the total width of the tiles the line meets — each tile taken with its bottom edge
       removed — whose top edge sits at non-integer height above the base of R.
```

Below `R` nothing has been entered, so `f = 0`; at the top of `R` every tile touching the top is
counted, since its top edge sits at height `R.height ∉ ℤ`, and those tiles span the full width, so
`f(R.y₁) = R.width`. The content of the proof is that `f` only ever changes by integers, which
forces `R.width` to be an integer.

Two ingredients give that. The first is `widthSum_slice`: a horizontal line missing every tile edge
crosses the *interiors* of the tiles it meets, so their traces on it are pairwise almost disjoint
and their widths add up to `R.width`. Comparing the slices just below and just above a height `c`
strictly inside `R` yields `gain_eq_loss`: the tiles born at `c` have the same total width as the
tiles dying at `c`.

The second is `exists_int_jump`. Between tile edges `f` is constant; crossing a height `c` it gains
the tiles born at `c` and loses those dying there. If `c` is at integer height above `R`'s base then
nothing is lost — a tile dying at `c` has its top edge at integer height, so it was never counted —
and each gained tile has one horizontal edge at integer height and one not, hence non-integer
height, hence integer width by the hypothesis of the theorem. If `c` is not at integer height then
every dying tile is lost, so conservation cancels the losses against the gains and leaves exactly
the tiles born at `c` whose top edge *is* at integer height; those again have integer width.

Rather than sorting the finitely many tile edges, we package the two ingredients as local constancy
of `t ↦ Int.fract (f t)` and use the connectedness of `ℝ`. As in the real-integral and checkerboard
proofs, heights are measured from `R`'s base instead of translating the tiling, which is Wagon's
"place `R` in standard position". Conservation genuinely fails at the single height `R.y₁` — that
failure *is* the theorem — so `f` is frozen there first (`sweepTrunc`).
-/

@[expose] public section

open MeasureTheory Set

namespace IntegerRectangle.SweepLine

variable {ι : Type} {R : Rectangle} {T : ι → Rectangle} {p q r : ι → Prop}

/-! ### Sums of tile widths -/

section WidthSum

variable [Fintype ι]

open scoped Classical in
/-- The total width of the tiles satisfying `p`. -/
noncomputable def widthSum (T : ι → Rectangle) (p : ι → Prop) : ℝ :=
  ∑ i, if p i then (T i).width else 0

private lemma widthSum_nonneg (T : ι → Rectangle) (p : ι → Prop) : 0 ≤ widthSum T p :=
  Finset.sum_nonneg fun i _ ↦ by split_ifs <;> simp [Rectangle.width_nonneg]

open scoped Classical in
/-- Two width sums agree when their predicates do. -/
private lemma widthSum_congr (h : ∀ i, p i ↔ q i) : widthSum T p = widthSum T q :=
  Finset.sum_congr rfl fun i _ ↦ if_congr (h i) rfl rfl

/-- Splitting a width sum along a disjoint case distinction. -/
private lemma widthSum_split (h : ∀ i, p i ↔ q i ∨ r i) (hd : ∀ i, ¬(q i ∧ r i)) :
    widthSum T p = widthSum T q + widthSum T r :=
  (Finset.sum_congr rfl fun i _ ↦ by grind).trans Finset.sum_add_distrib

/-- A width sum over an empty selection vanishes. -/
private lemma widthSum_eq_zero (h : ∀ i, ¬ p i) : widthSum T p = 0 :=
  Finset.sum_eq_zero fun i _ ↦ if_neg (h i)

/-- A width sum over tiles that all have integer width is an integer. -/
private lemma widthSum_isInt (h : ∀ i, p i → ∃ n : ℤ, (T i).width = n) :
    ∃ n : ℤ, widthSum T p = n := by
  classical
  choose! n hn using h
  refine ⟨∑ i, if p i then n i else 0, ?_⟩
  push_cast
  grind [widthSum]

end WidthSum

/-! ### The horizontal edges of a tiling -/

/-- The set of heights at which some tile has a horizontal edge. The sweep function below is
constant between consecutive such heights and can only jump across them. -/
def edgeSet (T : ι → Rectangle) : Set ℝ :=
  (Set.range fun i ↦ (T i).y₀) ∪ (Set.range fun i ↦ (T i).y₁)

private lemma tile_y₀_mem_edgeSet (T : ι → Rectangle) (i : ι) : (T i).y₀ ∈ edgeSet T :=
  Or.inl ⟨i, rfl⟩

private lemma tile_y₁_mem_edgeSet (T : ι → Rectangle) (i : ι) : (T i).y₁ ∈ edgeSet T :=
  Or.inr ⟨i, rfl⟩

/-- **Every height has an edge-free punctured neighbourhood.** The tile edges form a finite, hence
closed, set, so around any `c` there is a radius inside which `c` itself is the only edge. -/
private lemma exists_gap [Finite ι] (T : ι → Rectangle) (c : ℝ) :
    ∃ ε > 0, ∀ y ∈ edgeSet T, |y - c| < ε → y = c :=
  have hfin : (edgeSet T).Finite := (Set.finite_range _).union (Set.finite_range _)
  let ⟨ε, hε, hsub⟩ := (nhds_basis_abs_sub_lt c).mem_iff.mp
    ((hfin.diff (t := {c})).isClosed.compl_mem_nhds fun h ↦ h.2 rfl)
  ⟨ε, hε, fun _ hy hyc ↦ not_not.1 fun hne ↦ hsub hyc ⟨hy, hne⟩⟩

/-- Below `c`, the nearest tile edge is at distance at least `ε`. -/
private lemma le_sub_of_gap {c ε : ℝ} (hgap : ∀ y ∈ edgeSet T, |y - c| < ε → y = c) {y : ℝ}
    (hy : y ∈ edgeSet T) (hlt : y < c) : y ≤ c - ε :=
  le_of_not_gt fun hcon ↦ hlt.ne <| hgap y hy <| abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Above `c`, the nearest tile edge is at distance at least `ε`. -/
private lemma add_le_of_gap {c ε : ℝ} (hgap : ∀ y ∈ edgeSet T, |y - c| < ε → y = c) {y : ℝ}
    (hy : y ∈ edgeSet T) (hlt : c < y) : c + ε ≤ y :=
  le_of_not_gt fun hcon ↦ hlt.ne' <| hgap y hy <| abs_lt.mpr ⟨by linarith, by linarith⟩

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

/-! ### Flow conservation across a height

Slicing just above and just below a height `c` compares the tiles that are born at `c` with those
that die there. The tiles crossed by a line just above `c` are those with bottom edge at or below
`c` and top edge above `c`; the tiles crossed by a line just below `c` are those with bottom edge
below `c` and top edge at or above `c`. Both families have total width `R.width`, and they share the
tiles that strictly straddle `c`. -/

section Conservation

variable [Fintype ι]

/-- Slicing just above `c`: the strictly straddling tiles plus those born at `c`. -/
private lemma straddle_add_gain (hT : IsTiling R T) {c : ℝ} (hc₀ : R.y₀ ≤ c) (hc₁ : c < R.y₁) :
    widthSum T (fun i ↦ (T i).y₀ < c ∧ c < (T i).y₁)
      + widthSum T (fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁) = R.width := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap T c
  rw [← widthSum_slice (t := c + min ε (R.y₁ - c) / 2) hT (by grind) (by grind) fun _ ↦ by grind]
  refine (widthSum_split (fun i ↦ ?_) (fun i h ↦ h.1.1.ne h.2.1)).symm
  have := add_le_of_gap hgap (tile_y₀_mem_edgeSet T i)
  have := add_le_of_gap hgap (tile_y₁_mem_edgeSet T i)
  grind

/-- Slicing just below `c`: the strictly straddling tiles plus those dying at `c`. -/
private lemma straddle_add_loss (hT : IsTiling R T) {c : ℝ} (hc₀ : R.y₀ < c) (hc₁ : c ≤ R.y₁) :
    widthSum T (fun i ↦ (T i).y₀ < c ∧ c < (T i).y₁)
      + widthSum T (fun i ↦ (T i).y₀ < c ∧ c = (T i).y₁) = R.width := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap T c
  rw [← widthSum_slice (t := c - min ε (c - R.y₀) / 2) hT (by grind) (by grind) fun _ ↦ by grind]
  refine (widthSum_split (fun i ↦ ?_) (fun i h ↦ h.1.2.ne h.2.2)).symm
  have := le_sub_of_gap hgap (tile_y₀_mem_edgeSet T i)
  have := le_sub_of_gap hgap (tile_y₁_mem_edgeSet T i)
  grind

/-- **Flow conservation.** At a height strictly inside the tiled rectangle, the tiles born there
have the same total width as the tiles dying there. -/
theorem gain_eq_loss (hT : IsTiling R T) {c : ℝ} (hc₀ : R.y₀ < c) (hc₁ : c < R.y₁) :
    widthSum T (fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁)
      = widthSum T (fun i ↦ (T i).y₀ < c ∧ c = (T i).y₁) := by
  linarith [straddle_add_gain hT hc₀.le hc₁, straddle_add_loss hT hc₀ hc₁.le]

end Conservation

/-! ### The sweep function -/

/-- `IntHeight R y` says that `y` lies an integer distance above the base of `R`. Measuring heights
from `R`'s base is what replaces Wagon's "place `R` in standard position". -/
def IntHeight (R : Rectangle) (y : ℝ) : Prop := ∃ n : ℤ, y - R.y₀ = n

private lemma intHeight_base (R : Rectangle) : IntHeight R R.y₀ := ⟨0, by simp⟩

/-- A tile exactly one of whose horizontal edges is at integer height has non-integer height, so the
hypothesis of the theorem forces its width to be an integer. -/
private lemma width_isInt (hsides : ∀ i, (T i).HasIntegerSide) {i : ι}
    (h : ¬ (IntHeight R (T i).y₀ ↔ IntHeight R (T i).y₁)) : ∃ n : ℤ, (T i).width = n :=
  (hsides i).resolve_right fun ⟨m, hm⟩ ↦ h <|
    have hm' : (T i).y₁ - (T i).y₀ = (m : ℝ) := hm
    ⟨fun ⟨k, hk⟩ ↦ ⟨m + k, by linarith [Int.cast_add (R := ℝ) m k]⟩,
      fun ⟨k, hk⟩ ↦ ⟨k - m, by linarith [Int.cast_sub (R := ℝ) k m]⟩⟩

section Sweep

variable [Fintype ι]

/-- **The sweep function.** The total width of the tiles met by the sweep line `y = t` — each tile
being taken with its bottom edge removed — whose top edge sits at non-integer height. -/
private noncomputable def sweep (R : Rectangle) (T : ι → Rectangle) (t : ℝ) : ℝ :=
  widthSum T (fun i ↦ (T i).y₀ < t ∧ t ≤ (T i).y₁ ∧ ¬ IntHeight R (T i).y₁)

/-- Below the tiled rectangle the sweep function vanishes: no tile has been entered yet. -/
private lemma sweep_eq_zero (hT : IsTiling R T) {t : ℝ} (ht : t ≤ R.y₀) : sweep R T t = 0 :=
  widthSum_eq_zero fun i h ↦ absurd h.1 (not_lt.mpr (ht.trans (hT.le_tile_y₀ i)))

/-- At height `c` the sweep function counts the tiles strictly straddling `c` together with those
dying at `c`. -/
private lemma sweep_at (R : Rectangle) (T : ι → Rectangle) (c : ℝ) :
    sweep R T c = widthSum T (fun i ↦ (T i).y₀ < c ∧ c < (T i).y₁ ∧ ¬ IntHeight R (T i).y₁)
      + widthSum T (fun i ↦ (T i).y₀ < c ∧ c = (T i).y₁ ∧ ¬ IntHeight R (T i).y₁) :=
  widthSum_split (fun _ ↦ by grind) (fun _ h ↦ h.1.2.1.ne h.2.2.1)

/-- Just above `c` the sweep function counts the tiles strictly straddling `c` together with those
born at `c`. -/
private lemma sweep_above {c ε : ℝ} (hgap : ∀ y ∈ edgeSet T, |y - c| < ε → y = c) {t : ℝ}
    (h₀ : c < t) (h₁ : t < c + ε) :
    sweep R T t = widthSum T (fun i ↦ (T i).y₀ < c ∧ c < (T i).y₁ ∧ ¬ IntHeight R (T i).y₁)
      + widthSum T (fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁ ∧ ¬ IntHeight R (T i).y₁) := by
  refine widthSum_split (fun i ↦ ?_) (fun i h ↦ h.1.1.ne h.2.1)
  have := add_le_of_gap hgap (tile_y₀_mem_edgeSet T i)
  have := add_le_of_gap hgap (tile_y₁_mem_edgeSet T i)
  grind

/-- The sweep function is constant on `(c - ε, c]` when that interval is free of tile edges below
`c`: no tile is entered or left along the way. -/
private lemma sweep_eq_of_left {c ε : ℝ} (hgap : ∀ y ∈ edgeSet T, |y - c| < ε → y = c) {t : ℝ}
    (h₀ : c - ε < t) (h₁ : t ≤ c) : sweep R T t = sweep R T c :=
  have key : ∀ y ∈ edgeSet T, (y < t ↔ y < c) := fun _ hy ↦
    ⟨fun h ↦ h.trans_le h₁, fun h ↦ (le_sub_of_gap hgap hy h).trans_lt h₀⟩
  widthSum_congr fun i ↦ and_congr (key _ (tile_y₀_mem_edgeSet T i))
    (and_congr_left' (le_iff_le_iff_lt_iff_lt.mpr (key _ (tile_y₁_mem_edgeSet T i))))

/-! ### The jumps of the sweep function are integers -/

/-- **The sweep function only ever jumps by an integer.** Crossing the height `c` gains the tiles
born there and loses the tiles dying there.

If `c` is at integer height the losses are not counted at all, and each gained tile has an edge at
integer height and one at non-integer height, hence integer width. Otherwise the losses are counted
in full, so flow conservation cancels them against the gains and leaves exactly the tiles born at
`c` whose top edge is at integer height — again tiles with integer width. -/
theorem exists_int_jump (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) {c : ℝ}
    (hc : c < R.y₁) :
    ∃ n : ℤ, widthSum T (fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁ ∧ ¬ IntHeight R (T i).y₁)
      - widthSum T (fun i ↦ (T i).y₀ < c ∧ c = (T i).y₁ ∧ ¬ IntHeight R (T i).y₁) = n := by
  by_cases hint : IntHeight R c
  · have hloss : widthSum T (fun i ↦ (T i).y₀ < c ∧ c = (T i).y₁ ∧ ¬ IntHeight R (T i).y₁) = 0 :=
      widthSum_eq_zero fun i h ↦ h.2.2 (h.2.1 ▸ hint)
    obtain ⟨n, hn⟩ := widthSum_isInt (T := T)
      (p := fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁ ∧ ¬ IntHeight R (T i).y₁)
      fun i h ↦ width_isInt hsides fun hiff ↦ h.2.2 (hiff.mp (h.1.symm ▸ hint))
    exact ⟨n, by rw [hn, hloss, sub_zero]⟩
  · have hloss : widthSum T (fun i ↦ (T i).y₀ < c ∧ c = (T i).y₁ ∧ ¬ IntHeight R (T i).y₁)
        = widthSum T (fun i ↦ (T i).y₀ < c ∧ c = (T i).y₁) :=
      widthSum_congr fun i ↦ ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, h.2 ▸ hint⟩⟩
    rcases le_or_gt R.y₀ c with hle | hlt
    · have hy₀ : R.y₀ < c := hle.lt_of_ne fun heq ↦ hint (heq ▸ intHeight_base R)
      have hsplit : widthSum T (fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁)
          = widthSum T (fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁ ∧ ¬ IntHeight R (T i).y₁)
            + widthSum T (fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁ ∧ IntHeight R (T i).y₁) :=
        widthSum_split (fun i ↦ by grind) (fun _ h ↦ h.1.2.2 h.2.2.2)
      obtain ⟨n, hn⟩ := widthSum_isInt (T := T)
        (p := fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁ ∧ IntHeight R (T i).y₁)
        fun i h ↦ width_isInt hsides fun hiff ↦ hint (h.1 ▸ hiff.mpr h.2.2)
      refine ⟨-n, ?_⟩
      rw [hloss, ← gain_eq_loss hT hy₀ hc, hsplit, hn]
      push_cast
      ring
    · refine ⟨0, ?_⟩
      rw [widthSum_eq_zero (p := fun i ↦ (T i).y₀ = c ∧ c < (T i).y₁ ∧ ¬ IntHeight R (T i).y₁)
          fun i h ↦ by linarith [hT.le_tile_y₀ i, h.1],
        widthSum_eq_zero (p := fun i ↦ (T i).y₀ < c ∧ c = (T i).y₁ ∧ ¬ IntHeight R (T i).y₁)
          fun i h ↦ by linarith [hT.le_tile_y₀ i, h.1]]
      simp

/-- At the top edge of a tiled rectangle of non-integer height, the sweep function has picked up
every tile touching the top, and those tiles span the full width. -/
private lemma sweep_top (hT : IsTiling R T) (hy : R.y₀ < R.y₁) (hnint : ¬ IntHeight R R.y₁) :
    sweep R T R.y₁ = R.width := by
  have h := straddle_add_loss hT hy le_rfl
  rw [widthSum_eq_zero fun i hi ↦ absurd hi.2 (not_lt.mpr (hT.tile_y₁_le i)), zero_add] at h
  exact (widthSum_congr fun i ↦ by grind [hT.tile_y₁_le i]).trans h

/-! ### Constancy of the sweep function modulo `ℤ` -/

/-- The sweep function frozen at the top of `R`. Freezing it makes it locally constant modulo `ℤ`
at every real number, including at `R.y₁` — the one height where flow conservation fails, that
failure being exactly the content of the theorem. -/
private noncomputable def sweepTrunc (R : Rectangle) (T : ι → Rectangle) (t : ℝ) : ℝ :=
  sweep R T (min t R.y₁)

/-- **The frozen sweep function is locally constant modulo `ℤ`.** Away from the tile edges it is
literally constant, and across a tile edge it jumps by an integer. -/
private lemma isLocallyConstant_fract_sweepTrunc (hT : IsTiling R T)
    (hsides : ∀ i, (T i).HasIntegerSide) :
    IsLocallyConstant fun t ↦ Int.fract (sweepTrunc R T t) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro c
  rw [Metric.eventually_nhds_iff]
  rcases lt_or_ge c R.y₁ with hc | hc
  · obtain ⟨ε, hε, hgap⟩ := exists_gap T c
    refine ⟨min ε (R.y₁ - c), lt_min hε (sub_pos.mpr hc), fun {t} ht ↦ ?_⟩
    rw [Real.dist_eq, abs_lt] at ht
    simp only [sweepTrunc, min_eq_left (by grind : t ≤ R.y₁), min_eq_left hc.le]
    rcases le_or_gt t c with hle | hlt
    · rw [sweep_eq_of_left hgap (by grind) hle]
    · obtain ⟨n, hn⟩ := exists_int_jump hT hsides hc
      have hjump : sweep R T t = sweep R T c + (n : ℝ) := by
        rw [sweep_above hgap hlt (by grind), sweep_at]
        linarith
      rw [hjump, Int.fract_add_intCast]
  · obtain ⟨ε, hε, hgap⟩ := exists_gap T R.y₁
    refine ⟨ε, hε, fun {t} ht ↦ ?_⟩
    rw [Real.dist_eq, abs_lt] at ht
    simp only [sweepTrunc, min_eq_right hc]
    rcases le_or_gt R.y₁ t with hle | hlt
    · rw [min_eq_right hle]
    · rw [min_eq_left hlt.le, sweep_eq_of_left hgap (by grind) hlt.le]

end Sweep

/-- **Sweep-line proof** (Bachman–Yannakakis) of the integer-rectangle tiling theorem. -/
theorem IntegerRectangleTheorem_SweepLine : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  refine or_iff_not_imp_right.mpr fun hheight ↦ ?_
  have hy : R.y₀ < R.y₁ := R.hy.lt_of_ne fun h ↦ hheight ⟨0, by simp [Rectangle.height, h]⟩
  have hconst :=
    (isLocallyConstant_fract_sweepTrunc hT hsides).apply_eq_of_preconnectedSpace R.y₁ R.y₀
  simp only [sweepTrunc, min_self, min_eq_left R.hy, sweep_top hT hy hheight,
    sweep_eq_zero hT le_rfl, Int.fract_zero] at hconst
  exact (Int.fract_eq_zero_iff.mp hconst).imp fun n hn ↦ hn.symm

end IntegerRectangle.SweepLine
