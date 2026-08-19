module

public import DifferentProofs.IntegerRectangle.Basic

/-!
# Symmetries of a tiling, and the four tiles at a point

Two pieces of bookkeeping shared by the proofs that argue *locally*, about how the tiles fit
together along a line or around a point.

The first is symmetry. Transposing the plane, or reflecting it in a coordinate axis, carries
tilings to tilings (`IsTiling.map` and its three instances `IsTiling.transpose`,
`IsTiling.reflectX`, `IsTiling.reflectY`), so an argument about the left-hand side of a vertical
line also settles the right-hand side, and an argument about vertical lines also settles
horizontal ones.

The second is the *cells* of a rectangle. `IsTiling.iUnion_toSetIoc` says that deleting the left
and bottom edges of every tile turns a tiling into an exact partition, so that each point of the
plane belongs to exactly one tile *as approached from below left*. Deleting instead the right or
the top edge does the same for the other three quadrants: `Rectangle.cell` carries the two choices
as booleans, and `IsTiling.existsUnique_cell` says that a point of the corresponding cell of the
tiled rectangle has exactly one tile in each quadrant.
-/

@[expose] public section

open Set

namespace IntegerRectangle

namespace Rectangle

/-! ### Reflections and the transposition -/

/-- The image of a rectangle under transposing the plane. -/
def transpose (S : Rectangle) : Rectangle where
  x₀ := S.y₀
  x₁ := S.y₁
  y₀ := S.x₀
  y₁ := S.x₁
  hx := S.hy
  hy := S.hx

/-- The image of a rectangle under the reflection `x ↦ -x`. -/
def reflectX (S : Rectangle) : Rectangle where
  x₀ := -S.x₁
  x₁ := -S.x₀
  y₀ := S.y₀
  y₁ := S.y₁
  hx := neg_le_neg S.hx
  hy := S.hy

/-- The image of a rectangle under the reflection `y ↦ -y`. -/
def reflectY (S : Rectangle) : Rectangle where
  x₀ := S.x₀
  x₁ := S.x₁
  y₀ := -S.y₁
  y₁ := -S.y₀
  hx := S.hx
  hy := neg_le_neg S.hy

/-- Transposing the plane. -/
def swapHomeomorph : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.prodComm ℝ ℝ

/-- Reflecting the plane in the vertical axis. -/
def negFstHomeomorph : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ)

/-- Reflecting the plane in the horizontal axis. -/
def negSndHomeomorph : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := (Homeomorph.refl ℝ).prodCongr (Homeomorph.neg ℝ)

@[simp] lemma swapHomeomorph_apply (z : ℝ × ℝ) : swapHomeomorph z = (z.2, z.1) := rfl

@[simp] lemma negFstHomeomorph_apply (z : ℝ × ℝ) : negFstHomeomorph z = (-z.1, z.2) := rfl

@[simp] lemma negSndHomeomorph_apply (z : ℝ × ℝ) : negSndHomeomorph z = (z.1, -z.2) := rfl

lemma transpose_toSet (S : Rectangle) : S.transpose.toSet = swapHomeomorph ⁻¹' S.toSet := by
  ext ⟨a, b⟩
  simp only [toSet, transpose, Set.mem_preimage, swapHomeomorph_apply, Set.mem_prod, Set.mem_Icc]
  tauto

lemma reflectX_toSet (S : Rectangle) : S.reflectX.toSet = negFstHomeomorph ⁻¹' S.toSet := by
  ext ⟨a, b⟩
  simp only [toSet, reflectX, Set.mem_preimage, negFstHomeomorph_apply, Set.mem_prod, Set.mem_Icc,
    neg_le, le_neg]
  tauto

lemma reflectY_toSet (S : Rectangle) : S.reflectY.toSet = negSndHomeomorph ⁻¹' S.toSet := by
  ext ⟨a, b⟩
  simp only [toSet, reflectY, Set.mem_preimage, negSndHomeomorph_apply, Set.mem_prod, Set.mem_Icc,
    neg_le, le_neg]
  tauto

/-! ### The four cells of a rectangle -/

/-- A *cell* of a rectangle: the rectangle with one edge deleted in each direction. The boolean
`sx` selects which vertical edge survives — the right one when `sx = true` — and `sy` does the
same for the horizontal edges. The cell `S.cell true true` is `S.toSetIoc`, the one that turns a
tiling into a partition when a point is approached from below left; the other three cells do the
same for the other three quadrants. -/
def cell (S : Rectangle) (sx sy : Bool) : Set (ℝ × ℝ) :=
  (if sx then Ioc S.x₀ S.x₁ else Ico S.x₀ S.x₁) ×ˢ
    (if sy then Ioc S.y₀ S.y₁ else Ico S.y₀ S.y₁)

lemma cell_true_true (S : Rectangle) : S.cell true true = S.toSetIoc := rfl

@[simp] lemma mem_cell_tt {S : Rectangle} {x y : ℝ} :
    ((x, y) : ℝ × ℝ) ∈ S.cell true true ↔ (S.x₀ < x ∧ x ≤ S.x₁) ∧ S.y₀ < y ∧ y ≤ S.y₁ := Iff.rfl

@[simp] lemma mem_cell_tf {S : Rectangle} {x y : ℝ} :
    ((x, y) : ℝ × ℝ) ∈ S.cell true false ↔ (S.x₀ < x ∧ x ≤ S.x₁) ∧ S.y₀ ≤ y ∧ y < S.y₁ := Iff.rfl

@[simp] lemma mem_cell_ft {S : Rectangle} {x y : ℝ} :
    ((x, y) : ℝ × ℝ) ∈ S.cell false true ↔ (S.x₀ ≤ x ∧ x < S.x₁) ∧ S.y₀ < y ∧ y ≤ S.y₁ := Iff.rfl

@[simp] lemma mem_cell_ff {S : Rectangle} {x y : ℝ} :
    ((x, y) : ℝ × ℝ) ∈ S.cell false false ↔ (S.x₀ ≤ x ∧ x < S.x₁) ∧ S.y₀ ≤ y ∧ y < S.y₁ := Iff.rfl

/-- Reflecting in the vertical axis exchanges the two horizontal choices of cell. -/
lemma mem_reflectX_cell (S : Rectangle) (sy : Bool) (x y : ℝ) :
    ((-x, y) : ℝ × ℝ) ∈ S.reflectX.cell true sy ↔ ((x, y) : ℝ × ℝ) ∈ S.cell false sy := by
  cases sy <;> simp [reflectX, and_comm]

/-- Reflecting in the horizontal axis exchanges the two vertical choices of cell. -/
lemma mem_reflectY_cell (S : Rectangle) (sx : Bool) (x y : ℝ) :
    ((x, -y) : ℝ × ℝ) ∈ S.reflectY.cell sx true ↔ ((x, y) : ℝ × ℝ) ∈ S.cell sx false := by
  cases sx <;> simp [reflectY, and_comm]

/-! ### Dimensions under the symmetries of the plane -/

@[simp] lemma reflectX_width (S : Rectangle) : S.reflectX.width = S.width := by
  simp only [Rectangle.width, Rectangle.reflectX]
  ring

@[simp] lemma reflectX_height (S : Rectangle) : S.reflectX.height = S.height := rfl

@[simp] lemma reflectY_width (S : Rectangle) : S.reflectY.width = S.width := rfl

@[simp] lemma reflectY_height (S : Rectangle) : S.reflectY.height = S.height := by
  simp only [Rectangle.height, Rectangle.reflectY]
  ring

@[simp] lemma transpose_width (S : Rectangle) : S.transpose.width = S.height := rfl

@[simp] lemma transpose_height (S : Rectangle) : S.transpose.height = S.width := rfl

lemma hasIntegerSide_reflectX {S : Rectangle} :
    S.reflectX.HasIntegerSide ↔ S.HasIntegerSide := by simp [Rectangle.HasIntegerSide]

lemma hasIntegerSide_transpose {S : Rectangle} :
    S.transpose.HasIntegerSide ↔ S.HasIntegerSide := by
  simp [Rectangle.HasIntegerSide, or_comm]

end Rectangle

/-! ### Symmetry of tilings -/

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **A homeomorphism of the plane carrying rectangles to rectangles carries tilings to
tilings.** -/
theorem IsTiling.map (hT : IsTiling R T) {f : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)} {g : Rectangle → Rectangle}
    (hg : ∀ S : Rectangle, (g S).toSet = f ⁻¹' S.toSet) : IsTiling (g R) fun i ↦ g (T i) where
  cover := by
    rw [hg, hT.cover, Set.preimage_iUnion]
    exact Set.iUnion_congr fun i ↦ (hg (T i)).symm
  interiorDisjoint i j hij := by
    simp only [hg, ← f.preimage_interior]
    exact (hT.interiorDisjoint hij).preimage f

/-- Transposing the plane carries a tiling to a tiling. -/
theorem IsTiling.transpose (hT : IsTiling R T) : IsTiling R.transpose fun i ↦ (T i).transpose :=
  hT.map Rectangle.transpose_toSet

/-- Reflecting the plane in the vertical axis carries a tiling to a tiling. -/
theorem IsTiling.reflectX (hT : IsTiling R T) : IsTiling R.reflectX fun i ↦ (T i).reflectX :=
  hT.map Rectangle.reflectX_toSet

/-- Reflecting the plane in the horizontal axis carries a tiling to a tiling. -/
theorem IsTiling.reflectY (hT : IsTiling R T) : IsTiling R.reflectY fun i ↦ (T i).reflectY :=
  hT.map Rectangle.reflectY_toSet

/-! ### The tile of a tiling in each quadrant at a point -/

/-- Each point of the half-open cell of the tiled rectangle lies in the half-open cell of exactly
one tile. -/
theorem IsTiling.existsUnique_toSetIoc (hT : IsTiling R T) {z : ℝ × ℝ} (hz : z ∈ R.toSetIoc) :
    ∃! i, z ∈ (T i).toSetIoc :=
  have ⟨i, hi⟩ := Set.mem_iUnion.mp (hT.iUnion_toSetIoc.ge hz)
  ⟨i, hi, fun _ hj ↦ by_contra fun hne ↦
    Set.disjoint_left.mp (hT.pairwiseDisjoint_toSetIoc hne) hj hi⟩

/-- **Each point has exactly one tile of a tiling in each quadrant.** For the four choices of a
pair of edges to delete, a point of the corresponding cell of the tiled rectangle lies in the
corresponding cell of exactly one tile. -/
theorem IsTiling.existsUnique_cell (hT : IsTiling R T) (sx sy : Bool) {x y : ℝ}
    (hz : ((x, y) : ℝ × ℝ) ∈ R.cell sx sy) : ∃! i, ((x, y) : ℝ × ℝ) ∈ (T i).cell sx sy := by
  cases sx <;> cases sy
  · have key : ∀ S : Rectangle, ((x, y) : ℝ × ℝ) ∈ S.cell false false ↔
        ((-x, -y) : ℝ × ℝ) ∈ (S.reflectX.reflectY).toSetIoc := fun S ↦ by
      rw [← Rectangle.cell_true_true, Rectangle.mem_reflectY_cell, Rectangle.mem_reflectX_cell]
    simp only [key] at hz ⊢
    exact hT.reflectX.reflectY.existsUnique_toSetIoc hz
  · have key : ∀ S : Rectangle, ((x, y) : ℝ × ℝ) ∈ S.cell false true ↔
        ((-x, y) : ℝ × ℝ) ∈ S.reflectX.toSetIoc := fun S ↦ by
      rw [← Rectangle.cell_true_true, Rectangle.mem_reflectX_cell]
    simp only [key] at hz ⊢
    exact hT.reflectX.existsUnique_toSetIoc hz
  · have key : ∀ S : Rectangle, ((x, y) : ℝ × ℝ) ∈ S.cell true false ↔
        ((x, -y) : ℝ × ℝ) ∈ S.reflectY.toSetIoc := fun S ↦ by
      rw [← Rectangle.cell_true_true, Rectangle.mem_reflectY_cell]
    simp only [key] at hz ⊢
    exact hT.reflectY.existsUnique_toSetIoc hz
  · exact hT.existsUnique_toSetIoc hz

/-- **Recognising a tiling from its half-open cells.** A family of rectangles inside a
nondegenerate `R` whose half-open cells are pairwise disjoint and cover the half-open cell of `R`
is a tiling of `R`: the cells sit between the interiors and the closed tiles, so they control both
conditions at once. -/
theorem isTiling_of_toSetIoc (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
    (hsub : ∀ i, (T i).toSet ⊆ R.toSet)
    (hdisj : Pairwise (Function.onFun Disjoint fun i ↦ (T i).toSetIoc))
    (hcover : R.toSetIoc ⊆ ⋃ i, (T i).toSetIoc) : IsTiling R T where
  cover := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_subset hsub)
    have hcl : closure R.toSetIoc = R.toSet := by
      rw [Rectangle.toSetIoc, Rectangle.toSet, closure_prod_eq, closure_Ioc hx.ne,
        closure_Ioc hy.ne]
    rw [← hcl]
    exact closure_minimal (hcover.trans (Set.iUnion_mono fun i ↦
      Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self))
      (isClosed_iUnion_of_finite fun i ↦ (T i).isCompact_toSet.isClosed)
  interiorDisjoint i j hij := by
    have h : ∀ k : ι, interior (T k).toSet ⊆ (T k).toSetIoc := fun k ↦ by
      rw [Rectangle.toSet, interior_prod_eq, interior_Icc, interior_Icc]
      exact Set.prod_mono Set.Ioo_subset_Ioc_self Set.Ioo_subset_Ioc_self
    exact (hdisj hij).mono (h i) (h j)

/-- A cell of a tile sits inside the corresponding cell of the tiled rectangle. -/
lemma IsTiling.cell_subset (hT : IsTiling R T) (sx sy : Bool) (i : ι) :
    (T i).cell sx sy ⊆ R.cell sx sy := by
  have h₁ := hT.le_tile_x₀ i
  have h₂ := hT.tile_x₁_le i
  have h₃ := hT.le_tile_y₀ i
  have h₄ := hT.tile_y₁_le i
  rintro ⟨a, b⟩ h
  cases sx <;> cases sy <;>
    exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, by linarith [h.2.1], by linarith [h.2.2]⟩

/-- **A point determines the tile of each of its four quadrants.** Two tiles whose cells for the
same choice of edges share a point are equal. -/
theorem IsTiling.eq_of_mem_cell (hT : IsTiling R T) {sx sy : Bool} {x y : ℝ} {i j : ι}
    (hi : ((x, y) : ℝ × ℝ) ∈ (T i).cell sx sy) (hj : ((x, y) : ℝ × ℝ) ∈ (T j).cell sx sy) :
    i = j :=
  (hT.existsUnique_cell sx sy (hT.cell_subset sx sy i hi)).unique hi hj

/-! ### Proper tilings -/

/-- A family of rectangles is *proper* when each of its members is nondegenerate. Degenerate tiles
are harmless but carry no information, and every tiling can be pruned down to a proper one
(`IsTiling.proper`). -/
def Proper (T : ι → Rectangle) : Prop := ∀ i, (T i).Nondegenerate

omit [Fintype ι] in
/-- Transposing the plane preserves properness. -/
lemma properTranspose (hp : Proper T) : Proper fun i ↦ (T i).transpose :=
  fun i ↦ ⟨(hp i).2, (hp i).1⟩

omit [Fintype ι] in
/-- Reflecting the plane in the vertical axis preserves properness. -/
lemma properReflectX (hp : Proper T) : Proper fun i ↦ (T i).reflectX := fun i ↦
  ⟨by simpa [Rectangle.reflectX] using (hp i).1, (hp i).2⟩

omit [Fintype ι] in
/-- Reflecting the plane in the horizontal axis preserves properness. -/
lemma properReflectY (hp : Proper T) : Proper fun i ↦ (T i).reflectY := fun i ↦
  ⟨(hp i).1, by simpa [Rectangle.reflectY] using (hp i).2⟩

/-- The nondegenerate tiles of a family, reindexed by the indices that carry one. -/
def properTiles (T : ι → Rectangle) (i : {i : ι // (T i).Nondegenerate}) : Rectangle := T i.1

omit [Fintype ι] in
/-- Pruning a family of rectangles leaves a proper one. -/
lemma proper_properTiles (T : ι → Rectangle) : Proper (properTiles T) := fun i ↦ i.2

/-- **Degenerate tiles may be discarded.** The half-open cell of a degenerate rectangle is empty,
so it contributes nothing to the partition and the nondegenerate tiles alone still tile `R`. -/
theorem IsTiling.proper (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) :
    IsTiling R (properTiles T) := by
  refine isTiling_of_toSetIoc hx hy (fun i ↦ hT.tile_subset i.1)
    (fun i j hij ↦ hT.pairwiseDisjoint_toSetIoc (Subtype.coe_ne_coe.mpr hij)) fun z hz ↦ ?_
  obtain ⟨i, hi, -⟩ := hT.existsUnique_toSetIoc hz
  exact Set.mem_iUnion.mpr ⟨⟨i, hi.1.1.trans_le hi.1.2, hi.2.1.trans_le hi.2.2⟩, hi⟩

/-- **Two distinct tiles that overlap in height lie one strictly to the left of the other.** The
point just inside the upper right corner of the leftmost of the two right edges would otherwise
be in the lower-left cell of both. -/
lemma IsTiling.separated_x_of_overlap_y (hT : IsTiling R T) (hp : Proper T) {i j : ι}
    (hij : i ≠ j) (h : max (T i).y₀ (T j).y₀ < min (T i).y₁ (T j).y₁) :
    (T i).x₁ ≤ (T j).x₀ ∨ (T j).x₁ ≤ (T i).x₀ := by
  by_contra hcon
  push Not at hcon
  have ha₁ : (T i).y₀ ≤ max (T i).y₀ (T j).y₀ := le_max_left _ _
  have ha₂ : (T j).y₀ ≤ max (T i).y₀ (T j).y₀ := le_max_right _ _
  have hb₁ : min (T i).y₁ (T j).y₁ ≤ (T i).y₁ := min_le_left _ _
  have hb₂ : min (T i).y₁ (T j).y₁ ≤ (T j).y₁ := min_le_right _ _
  have hc₁ : min (T i).x₁ (T j).x₁ ≤ (T i).x₁ := min_le_left _ _
  have hc₂ : min (T i).x₁ (T j).x₁ ≤ (T j).x₁ := min_le_right _ _
  exact hij (hT.eq_of_mem_cell (sx := true) (sy := true)
    (x := min (T i).x₁ (T j).x₁) (y := min (T i).y₁ (T j).y₁)
    ⟨⟨lt_min (hp i).1 hcon.2, hc₁⟩, by linarith, hb₁⟩
    ⟨⟨lt_min hcon.1 (hp j).1, hc₂⟩, by linarith, hb₂⟩)

end IntegerRectangle
