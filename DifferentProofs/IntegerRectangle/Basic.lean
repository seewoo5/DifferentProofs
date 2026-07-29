module

public import DifferentProofs.IntegerRectangle.Defs
public import DifferentProofsForMathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Shared core for the integer-rectangle tiling proofs

This file collects what the proofs of `IntegerRectangleTheorem` share: basic facts about a
rectangle's point set and about the tiles of a tiling, and the analytic engine used by the
integral-flavoured proofs.

The elementary layer unfolds `Rectangle.toSet` and reads off that every tile of a tiling sits
inside the tiled rectangle (`Rectangle.mem_toSet`, `Rectangle.mem_interior_toSet`,
`IsTiling.tile_subset`, and the four edge bounds `IsTiling.le_tile_x₀` … `IsTiling.tile_y₁_le`).

Next, a tiling is turned into an *exact* partition. Closed tiles overlap along shared edges, so a
tiling only partitions the rectangle up to null sets; deleting each tile's left and bottom edges
(`Rectangle.toSetIoc`) repairs this exactly.

* `IsTiling.pairwiseDisjoint_toSetIoc` and `IsTiling.iUnion_toSetIoc` — the half-open cells of a
  tiling partition the half-open cell of the tiled rectangle.
* `IsTiling.measure_toSetIoc` — consequently *every* measure on the plane, not just Lebesgue, is
  additive over a tiling.

The complex-integral, real-integral, and checkerboard proofs then all run through one mechanism:
attach to each rectangle the number
`∫∫_R g(x) h(y) dx dy = (∫ g over the width) · (∫ h over the height)`,
which is *additive* over a tiling and *factors* through the two coordinate directions. If each
tile has a vanishing width-integral or height-integral, additivity forces the same for the
ambient rectangle.

* `IsTiling.setIntegral_eq_sum` — additivity of the plane integral over a tiling (the tiles are
  a.e.-disjoint because their pairwise intersections lie in null boundaries).
* `Rectangle.setIntegral_prod_mul` — Fubini factorization of the integral of a separated product
  `g z.1 · h z.2` over a rectangle.
* `IsTiling.prod_integral_dichotomy` — the engine: a per-tile width/height integral dichotomy
  propagates to the ambient rectangle.

The sweep-line proof uses only the elementary layer, not the engine.
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

/-- A rectangle's width is nonnegative. -/
lemma width_nonneg (R : Rectangle) : 0 ≤ R.width := sub_nonneg.mpr R.hx

/-- A rectangle is a measurable subset of the plane. -/
lemma measurableSet_toSet (R : Rectangle) : MeasurableSet R.toSet :=
  measurableSet_Icc.prod measurableSet_Icc

/-- A rectangle is a compact subset of the plane. -/
lemma isCompact_toSet (R : Rectangle) : IsCompact R.toSet := isCompact_Icc.prod isCompact_Icc

/-- A function continuous on the plane is integrable over any rectangle. -/
lemma integrableOn_of_continuous (R : Rectangle) {E : Type*} [NormedAddCommGroup E]
    {F : ℝ × ℝ → E} (hF : Continuous F) : IntegrableOn F R.toSet volume :=
  hF.continuousOn.integrableOn_compact R.isCompact_toSet

end Rectangle

section Tiles

variable {ι : Type*} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- Each tile of a tiling is contained in the tiled rectangle. -/
lemma IsTiling.tile_subset (hT : IsTiling R T) (i : ι) : (T i).toSet ⊆ R.toSet :=
  (subset_iUnion (fun j ↦ (T j).toSet) i).trans hT.cover.superset

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

/-- A tiling has at least one tile, since the tiled rectangle is nonempty. -/
lemma IsTiling.nonempty (hT : IsTiling R T) : Nonempty ι := by
  have hz : ((R.x₀, R.y₀) : ℝ × ℝ) ∈ R.toSet :=
    Rectangle.mem_toSet.mpr ⟨⟨le_rfl, R.hx⟩, ⟨le_rfl, R.hy⟩⟩
  rw [hT.cover] at hz
  exact ⟨(mem_iUnion.mp hz).choose⟩

end Tiles

/-! ### A tiling as an exact partition

Tiles overlap along shared edges, so a tiling is only *almost* a partition of the closed rectangle.
Deleting each tile's left and bottom edges repairs this exactly: the half-open cells of a tiling
partition the half-open cell of the tiled rectangle, with no null sets involved. Consequently
*every* measure on the plane — not just Lebesgue — is additive over a tiling. -/

section Partition

variable {ι : Type*} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **Half-open cells of a tiling are pairwise disjoint.** A common point of two cells could be
nudged down and to the left into the interiors of both tiles. -/
theorem IsTiling.pairwiseDisjoint_toSetIoc (hT : IsTiling R T) :
    Pairwise (Function.onFun Disjoint fun i ↦ (T i).toSetIoc) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun z hzi hzj ↦ ?_
  obtain ⟨⟨hxi₀, hxi₁⟩, hyi₀, hyi₁⟩ := Rectangle.mem_toSetIoc.mp hzi
  obtain ⟨⟨hxj₀, hxj₁⟩, hyj₀, hyj₁⟩ := Rectangle.mem_toSetIoc.mp hzj
  -- Nudging `z` to the midpoint between the higher lower-left corner and `z` itself lands
  -- strictly inside both tiles.
  have hx := max_lt hxi₀ hxj₀
  have hy := max_lt hyi₀ hyj₀
  have hxi := le_max_left (T i).x₀ (T j).x₀
  have hxj := le_max_right (T i).x₀ (T j).x₀
  have hyi := le_max_left (T i).y₀ (T j).y₀
  have hyj := le_max_right (T i).y₀ (T j).y₀
  exact Set.disjoint_left.mp (hT.interiorDisjoint hij)
    (Rectangle.mem_interior_toSet
      (z := ((max (T i).x₀ (T j).x₀ + z.1) / 2, (max (T i).y₀ (T j).y₀ + z.2) / 2))
      ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)
    (Rectangle.mem_interior_toSet
      (z := ((max (T i).x₀ (T j).x₀ + z.1) / 2, (max (T i).y₀ (T j).y₀ + z.2) / 2))
      ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)

/-- **Half-open cells of a tiling cover the half-open cell of the tiled rectangle.** For the
inclusion that matters, a point of the ambient cell is approached from below-left; finitely many
tiles force one of them to contain the approaching points arbitrarily close in, and that tile's
half-open cell contains the point. -/
theorem IsTiling.iUnion_toSetIoc (hT : IsTiling R T) : ⋃ i, (T i).toSetIoc = R.toSetIoc := by
  haveI := hT.nonempty
  refine Set.Subset.antisymm (iUnion_subset fun i z hz ↦ ?_) fun z hz ↦ ?_
  · obtain ⟨⟨hx₀, hx₁⟩, hy₀, hy₁⟩ := Rectangle.mem_toSetIoc.mp hz
    exact Rectangle.mem_toSetIoc.mpr
      ⟨⟨(hT.le_tile_x₀ i).trans_lt hx₀, hx₁.trans (hT.tile_x₁_le i)⟩,
        (hT.le_tile_y₀ i).trans_lt hy₀, hy₁.trans (hT.tile_y₁_le i)⟩
  · obtain ⟨⟨hx₀, hx₁⟩, hy₀, hy₁⟩ := Rectangle.mem_toSetIoc.mp hz
    -- Every small nudge down-and-left stays inside `R`, hence inside some tile.
    have hshift : ∀ δ, 0 < δ → δ ≤ min (z.1 - R.x₀) (z.2 - R.y₀) →
        ∃ i, ((z.1 - δ, z.2 - δ) : ℝ × ℝ) ∈ (T i).toSet := fun δ hδ hδd ↦ by
      have h1 := (le_min_iff.mp hδd).1
      have h2 := (le_min_iff.mp hδd).2
      have hmem : ((z.1 - δ, z.2 - δ) : ℝ × ℝ) ∈ R.toSet :=
        Rectangle.mem_toSet.mpr ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      rw [hT.cover] at hmem
      exact mem_iUnion.mp hmem
    -- Finitely many tiles, so one of them works for arbitrarily small nudges.
    obtain ⟨i, hi⟩ : ∃ i, ∀ η, 0 < η → ∃ δ, 0 < δ ∧ δ < η ∧
        ((z.1 - δ, z.2 - δ) : ℝ × ℝ) ∈ (T i).toSet := by
      by_contra! hcon
      choose η hη hbad using hcon
      set m := min (min (z.1 - R.x₀) (z.2 - R.y₀)) (Finset.univ.inf' Finset.univ_nonempty η) with hm
      have hm0 : 0 < m :=
        lt_min (lt_min (by linarith) (by linarith)) ((Finset.lt_inf'_iff _).mpr fun i _ ↦ hη i)
      obtain ⟨i, hmem⟩ := hshift (m / 2) (by linarith)
        (by have := min_le_left (min (z.1 - R.x₀) (z.2 - R.y₀))
              (Finset.univ.inf' Finset.univ_nonempty η)
            rw [← hm] at this
            linarith)
      refine hbad i (m / 2) (by linarith) ?_ hmem
      have h1 : m ≤ η i := by
        rw [hm]
        exact (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ i))
      linarith
    -- Read off the four inequalities defining membership in this tile's half-open cell.
    refine mem_iUnion.mpr ⟨i, Rectangle.mem_toSetIoc.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · obtain ⟨δ, hδ, -, hmem⟩ := hi 1 one_pos
      have := (Rectangle.mem_toSet.mp hmem).1.1
      simp only at this
      linarith
    · by_contra hcon
      obtain ⟨δ, hδ, hδη, hmem⟩ := hi (z.1 - (T i).x₁) (by linarith [not_le.mp hcon])
      have := (Rectangle.mem_toSet.mp hmem).1.2
      simp only at this
      linarith
    · obtain ⟨δ, hδ, -, hmem⟩ := hi 1 one_pos
      have := (Rectangle.mem_toSet.mp hmem).2.1
      simp only at this
      linarith
    · by_contra hcon
      obtain ⟨δ, hδ, hδη, hmem⟩ := hi (z.2 - (T i).y₁) (by linarith [not_le.mp hcon])
      have := (Rectangle.mem_toSet.mp hmem).2.2
      simp only at this
      linarith

/-- **Every measure is additive over a tiling.** The half-open cells partition the ambient
half-open cell, so no null-set bookkeeping is needed and `μ` is arbitrary. -/
theorem IsTiling.measure_toSetIoc (hT : IsTiling R T) (μ : Measure (ℝ × ℝ)) :
    μ R.toSetIoc = ∑ i, μ (T i).toSetIoc := by
  rw [← hT.iUnion_toSetIoc,
    measure_iUnion hT.pairwiseDisjoint_toSetIoc fun i ↦ (T i).measurableSet_toSetIoc,
    tsum_fintype]

end Partition

/-- If two rectangles have disjoint interiors then, since their intersection lies in the union of
their (null) boundaries, they are almost-everywhere disjoint for the planar Lebesgue measure. -/
lemma aedisjoint_toSet_of_disjoint_interior {A B : Rectangle}
    (h : Disjoint (interior A.toSet) (interior B.toSet)) :
    AEDisjoint volume A.toSet B.toSet := by
  simp only [Rectangle.toSet, interior_prod_eq, interior_Icc, Set.disjoint_prod] at h
  change volume (A.toSet ∩ B.toSet) = 0
  simp only [Rectangle.toSet, Set.prod_inter_prod]
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
  exact mul_eq_zero.mpr (h.imp aedisjoint_Icc_of_disjoint_Ioo aedisjoint_Icc_of_disjoint_Ioo)

/-- **Additivity of the plane integral over a tiling.** If `T` tiles `R` and `f` is integrable on
`R`, then the integral of `f` over `R` is the sum of the integrals over the tiles. -/
theorem IsTiling.setIntegral_eq_sum {ι : Type*} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hT : IsTiling R T) {f : ℝ × ℝ → E}
    (hf : IntegrableOn f R.toSet volume) :
    ∫ z in R.toSet, f z = ∑ i, ∫ z in (T i).toSet, f z := by
  rw [hT.cover, integral_iUnion_ae (fun i ↦ (T i).measurableSet_toSet.nullMeasurableSet)
    (fun i j hij ↦ aedisjoint_toSet_of_disjoint_interior (hT.interiorDisjoint hij))
    (hT.cover ▸ hf), tsum_fintype]

/-- **Fubini factorization for a rectangle.** The integral of a separated product `g z.1 · h z.2`
over a rectangle is the product of the width-integral of `g` and the height-integral of `h`. -/
theorem Rectangle.setIntegral_prod_mul (R : Rectangle) {L : Type*} [RCLike L] (g h : ℝ → L) :
    ∫ z in R.toSet, g z.1 * h z.2 =
      (∫ x in Icc R.x₀ R.x₁, g x) * (∫ y in Icc R.y₀ R.y₁, h y) := by
  rw [Rectangle.toSet, Measure.volume_eq_prod ℝ ℝ, MeasureTheory.setIntegral_prod_mul g h]

/-- **The dichotomy engine.** Suppose `T` tiles `R`, the product `g z.1 · h z.2` is integrable over
`R`, and for every tile at least one of its width-integral of `g` or its height-integral of `h`
vanishes. Then the same dichotomy holds for the ambient rectangle `R`. -/
theorem IsTiling.prod_integral_dichotomy {ι : Type*} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}
    {L : Type*} [RCLike L] {g h : ℝ → L} (hT : IsTiling R T)
    (hint : IntegrableOn (fun z : ℝ × ℝ ↦ g z.1 * h z.2) R.toSet volume)
    (htile : ∀ i, (∫ x in Icc (T i).x₀ (T i).x₁, g x) = 0 ∨
      (∫ y in Icc (T i).y₀ (T i).y₁, h y) = 0) :
    (∫ x in Icc R.x₀ R.x₁, g x) = 0 ∨ (∫ y in Icc R.y₀ R.y₁, h y) = 0 := by
  refine mul_eq_zero.mp ?_
  rw [← R.setIntegral_prod_mul g h, hT.setIntegral_eq_sum hint]
  exact Finset.sum_eq_zero fun i _ ↦
    ((T i).setIntegral_prod_mul g h).trans (mul_eq_zero.mpr (htile i))

end IntegerRectangle
