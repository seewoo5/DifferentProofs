module

public import DifferentProofs.IntegerRectangle.ReducibleLink
public import DifferentProofsForMathlib.Combinatorics.Graph.CombinatorialMap

/-!
# The integer-rectangle theorem by a minimal cut-set

Wagon's eleventh proof, due to Paul Seymour. Seymour's graph `Γ` has the horizontal segments of
the tiling as vertices, the maximal horizontal stretches of tile edges, and one edge for each tile,
joining the segment carrying its bottom edge to the segment carrying its top edge, together with
an exterior edge running round the outside of `R` from its bottom to its top. Drawing each edge up
the vertical bisector of its tile embeds `Γ` in the plane, and the faces of the embedding are the
V-links of the tiling, "in the terminology of the preceding proof", with the two outer faces on
either side of the exterior edge.

Call a tile a V-tile when its height is an integer; by hypothesis the others, the H-tiles, have
integer width. Let `S` consist of the exterior edge and the edges of the H-tiles. If deleting `S`
leaves the bottom of `R` joined to its top, the path climbs across V-tiles and the height of `R`
is an integer (`CutSet.int_sub_y₀_of_reflTransGen`). Otherwise a minimal `S' ⊆ S` cutting the
bottom off from the top is a bond of `Γ` (`Graph.isBond_of_minimal`), and by the well-known
theorem on planar graphs that Wagon cites, its edges form a cycle of the dual graph `Γ*`
(`CombinatorialMap.IsPlanar.isCycle_of_isBond`). The cycle passes through the exterior edge,
which alone joins the bottom to the top, and the rest of it is a path from the left outer face to
the right one across H-tiles, each step moving the abscissa by the integer width of the tile
crossed: the width of `R` is an integer (`CutSet.intWidth_of_not_reflTransGen`).

## The embedding

The drawing is formalized as the rotation system it determines, a `CombinatorialMap` in the sense
of `DifferentProofsForMathlib.Combinatorics.Graph.CombinatorialMap` (`CutSet.seymourMap`). Its
darts are the two ends of each edge (`CutSet.Dart`), and the rotation `CutSet.rot` turns each
dart counterclockwise round its segment: rightwards along the tiles below the segment, round its
right end, leftwards along the tiles above it, and round its left end. The file then proves what
Wagon reads off the picture:

* the darts at a segment form one orbit of the rotation, so the vertices of the rotation system
  are the horizontal segments (`CutSet.sameCycle_of_vert_eq`);
* the darts along a V-link form one orbit of the face permutation, which climbs the link's left
  side and descends its right side, so the faces are the V-links and the two outer faces
  (`CutSet.faceOf_rot_flipEnd`, `CutSet.sameCycle_of_faceOf_eq`);
* the embedding is planar (`CutSet.seymourMap_isPlanar`).

A rotation system is planar, an embedding in the sphere, when it is connected and its Euler
characteristic is `2`. For Seymour's graph this comes out of the Jordan curve property, that an
edge set meeting every face evenly separates the segments (`CutSet.seymourMap_isEdgeCut_of_isEven`):
colour each segment by the parity of the tiles of the set stacked under it. The colour does not
depend on where along the segment it is read, since the tiles a moving column gains and loses abut
V-links lying wholly below the segment, each met evenly (`CutSet.colSum_eq`).

## Formalization notes

* A segment is the class of its points under `CutSet.SegStep`, two points of horizontal edges
  being related when every point between them lies on a horizontal edge (`CutSet.Seg`).
* Wagon takes the planarity of the embedding from the picture; here it is proved, as above.
* Degenerate rectangles are dispatched first, and degenerate tiles are pruned with
  `IsTiling.proper` before the graph is built.
-/

@[expose] public section

open Set

namespace IntegerRectangle

open ReducibleLink

namespace CutSet

variable {ι : Type} {R : Rectangle} {T : ι → Rectangle} {i j k : ι} {p q r : ℝ × ℝ}

/-! ### Horizontal segments -/

/-- The point `p` lies on the bottom edge of the rectangle `S`. -/
def MemBot (S : Rectangle) (p : ℝ × ℝ) : Prop := p.2 = S.y₀ ∧ S.x₀ ≤ p.1 ∧ p.1 ≤ S.x₁

/-- The point `p` lies on the top edge of the rectangle `S`. -/
def MemTop (S : Rectangle) (p : ℝ × ℝ) : Prop := p.2 = S.y₁ ∧ S.x₀ ≤ p.1 ∧ p.1 ≤ S.x₁

/-- The point `p` lies on a horizontal edge of the tiling. -/
def OnEdge (T : ι → Rectangle) (p : ℝ × ℝ) : Prop := ∃ i, MemBot (T i) p ∨ MemTop (T i) p

/-- Two points at the same height with every point between them on a horizontal edge: they lie
on the same horizontal segment of the tiling. -/
def SegStep (T : ι → Rectangle) (p q : ℝ × ℝ) : Prop :=
  p.2 = q.2 ∧ ∀ x ∈ uIcc p.1 q.1, OnEdge T (x, p.2)

lemma SegStep.refl (hp : OnEdge T p) : SegStep T p p := by
  refine ⟨rfl, fun x hx ↦ ?_⟩
  rw [uIcc_self, mem_singleton_iff] at hx
  rw [hx]
  exact hp

lemma SegStep.symm (h : SegStep T p q) : SegStep T q p :=
  ⟨h.1.symm, fun x hx ↦ h.1 ▸ h.2 x (uIcc_comm q.1 p.1 ▸ hx)⟩

lemma SegStep.trans (h₁ : SegStep T p q) (h₂ : SegStep T q r) : SegStep T p r := by
  refine ⟨h₁.1.trans h₂.1, fun x hx ↦ ?_⟩
  rcases uIcc_subset_uIcc_union_uIcc hx with hx | hx
  · exact h₁.2 x hx
  · rw [h₁.1]
    exact h₂.2 x hx

/-- Two points of one bottom edge lie on one segment. -/
lemma segStep_of_memBot (hp : MemBot (T i) p) (hq : MemBot (T i) q) : SegStep T p q := by
  refine ⟨hp.1.trans hq.1.symm, fun x hx ↦ ⟨i, .inl ⟨hp.1, ?_⟩⟩⟩
  rcases mem_uIcc.mp hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨hp.2.1.trans h₁, h₂.trans hq.2.2⟩
  · exact ⟨hq.2.1.trans h₁, h₂.trans hp.2.2⟩

/-- Two points of one top edge lie on one segment. -/
lemma segStep_of_memTop (hp : MemTop (T i) p) (hq : MemTop (T i) q) : SegStep T p q := by
  refine ⟨hp.1.trans hq.1.symm, fun x hx ↦ ⟨i, .inr ⟨hp.1, ?_⟩⟩⟩
  rcases mem_uIcc.mp hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨hp.2.1.trans h₁, h₂.trans hq.2.2⟩
  · exact ⟨hq.2.1.trans h₁, h₂.trans hp.2.2⟩

variable (T) in
/-- Points of horizontal edges, related when they lie on one segment. -/
def segSetoid : Setoid {p : ℝ × ℝ // OnEdge T p} where
  r p q := SegStep T p.1 q.1
  iseqv := ⟨fun p ↦ .refl p.2, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

variable (T) in
/-- A **horizontal segment** of the tiling, a maximal horizontal stretch of tile edges, recorded
as the class of its points: the vertices of Seymour's graph. -/
def Seg : Type := Quotient (segSetoid T)

/-- The segment through a point of a horizontal edge. -/
def Seg.mk (p : ℝ × ℝ) (hp : OnEdge T p) : Seg T := Quotient.mk (segSetoid T) ⟨p, hp⟩

lemma Seg.mk_eq_mk {hp : OnEdge T p} {hq : OnEdge T q} :
    Seg.mk p hp = Seg.mk q hq ↔ SegStep T p q :=
  Quotient.eq (r := segSetoid T)

lemma Seg.exists_mk (s : Seg T) : ∃ p hp, Seg.mk p hp = s :=
  Quotient.inductionOn s fun p ↦ ⟨p.1, p.2, rfl⟩

/-- The height of a segment. -/
def Seg.y : Seg T → ℝ := Quotient.lift (fun p ↦ p.1.2) fun _ _ h ↦ h.1

@[simp] lemma Seg.y_mk (hp : OnEdge T p) : (Seg.mk p hp).y = p.2 := rfl

/-! ### The tiling around a point -/

variable [Fintype ι]

/-- Every point of the bottom edge of `R` lies on the bottom edge of a tile. -/
lemma exists_memBot_of_bot (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
    {z : ℝ} (h₀ : R.x₀ ≤ z) (h₁ : z ≤ R.x₁) : ∃ i, MemBot (T i) ((z, R.y₀) : ℝ × ℝ) := by
  rcases h₁.lt_or_eq with hlt | rfl
  · obtain ⟨i, hi, -⟩ := hT.existsUnique_cell false false
      (Rectangle.mem_cell_ff.mpr ⟨⟨h₀, hlt⟩, le_rfl, hy⟩)
    rcases Rectangle.mem_cell_ff.mp hi with ⟨⟨hx₀, hx₁⟩, hy₀, -⟩
    exact ⟨i, le_antisymm (hT.le_tile_y₀ i) hy₀, hx₀, hx₁.le⟩
  · obtain ⟨i, hi, -⟩ := hT.existsUnique_cell true false
      (Rectangle.mem_cell_tf.mpr ⟨⟨hx, le_rfl⟩, le_rfl, hy⟩)
    rcases Rectangle.mem_cell_tf.mp hi with ⟨⟨hx₀, hx₁⟩, hy₀, -⟩
    exact ⟨i, le_antisymm (hT.le_tile_y₀ i) hy₀, hx₀.le, hx₁⟩

/-- Every point of the top edge of `R` lies on the top edge of a tile. -/
lemma exists_memTop_of_top (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
    {z : ℝ} (h₀ : R.x₀ ≤ z) (h₁ : z ≤ R.x₁) : ∃ i, MemTop (T i) ((z, R.y₁) : ℝ × ℝ) := by
  rcases h₁.lt_or_eq with hlt | rfl
  · obtain ⟨i, hi, -⟩ := hT.existsUnique_cell false true
      (Rectangle.mem_cell_ft.mpr ⟨⟨h₀, hlt⟩, hy, le_rfl⟩)
    rcases Rectangle.mem_cell_ft.mp hi with ⟨⟨hx₀, hx₁⟩, -, hy₁⟩
    exact ⟨i, (le_antisymm (hT.tile_y₁_le i) hy₁).symm, hx₀, hx₁.le⟩
  · obtain ⟨i, hi, -⟩ := hT.existsUnique_cell true true
      (Rectangle.mem_cell_tt.mpr ⟨⟨hx, le_rfl⟩, hy, le_rfl⟩)
    rcases Rectangle.mem_cell_tt.mp hi with ⟨⟨hx₀, hx₁⟩, -, hy₁⟩
    exact ⟨i, (le_antisymm (hT.tile_y₁_le i) hy₁).symm, hx₀.le, hx₁⟩

/-- **The bottom of `R` is one segment.** -/
lemma segStep_bot (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) {z z' : ℝ}
    (hz : z ∈ Icc R.x₀ R.x₁) (hz' : z' ∈ Icc R.x₀ R.x₁) :
    SegStep T ((z, R.y₀) : ℝ × ℝ) (z', R.y₀) := by
  refine ⟨rfl, fun x hx' ↦ ?_⟩
  have := uIcc_subset_Icc hz hz' hx'
  obtain ⟨i, hi⟩ := exists_memBot_of_bot hT hx hy this.1 this.2
  exact ⟨i, .inl hi⟩

/-- **The top of `R` is one segment.** -/
lemma segStep_top (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) {z z' : ℝ}
    (hz : z ∈ Icc R.x₀ R.x₁) (hz' : z' ∈ Icc R.x₀ R.x₁) :
    SegStep T ((z, R.y₁) : ℝ × ℝ) (z', R.y₁) := by
  refine ⟨rfl, fun x hx' ↦ ?_⟩
  have := uIcc_subset_Icc hz hz' hx'
  obtain ⟨i, hi⟩ := exists_memTop_of_top hT hx hy this.1 this.2
  exact ⟨i, .inr hi⟩

/-- Two tiles with their top-left corners at one point coincide. -/
lemma eq_of_x₀_y₁ (hT : IsTiling R T) (hp : Proper T) (h₀ : (T i).x₀ = (T j).x₀)
    (h₁ : (T i).y₁ = (T j).y₁) : i = j :=
  hT.eq_of_mem_cell (sx := false) (sy := true) (x := (T i).x₀) (y := (T i).y₁)
    ⟨⟨le_rfl, (hp i).1⟩, (hp i).2, le_rfl⟩ ⟨⟨h₀.ge, h₀ ▸ (hp j).1⟩, h₁ ▸ (hp j).2, h₁.le⟩

/-- Two tiles with their top-right corners at one point coincide. -/
lemma eq_of_x₁_y₁ (hT : IsTiling R T) (hp : Proper T) (h₀ : (T i).x₁ = (T j).x₁)
    (h₁ : (T i).y₁ = (T j).y₁) : i = j :=
  hT.eq_of_mem_cell (sx := true) (sy := true) (x := (T i).x₁) (y := (T i).y₁)
    ⟨⟨(hp i).1, le_rfl⟩, (hp i).2, le_rfl⟩ ⟨⟨h₀ ▸ (hp j).1, h₀.le⟩, h₁ ▸ (hp j).2, h₁.le⟩

/-- Two tiles with their bottom-left corners at one point coincide. -/
lemma eq_of_x₀_y₀ (hT : IsTiling R T) (hp : Proper T) (h₀ : (T i).x₀ = (T j).x₀)
    (h₁ : (T i).y₀ = (T j).y₀) : i = j :=
  hT.eq_of_mem_cell (sx := false) (sy := false) (x := (T i).x₀) (y := (T i).y₀)
    ⟨⟨le_rfl, (hp i).1⟩, le_rfl, (hp i).2⟩ ⟨⟨h₀.ge, h₀ ▸ (hp j).1⟩, h₁.ge, h₁ ▸ (hp j).2⟩

/-- Two tiles with their bottom-right corners at one point coincide. -/
lemma eq_of_x₁_y₀ (hT : IsTiling R T) (hp : Proper T) (h₀ : (T i).x₁ = (T j).x₁)
    (h₁ : (T i).y₀ = (T j).y₀) : i = j :=
  hT.eq_of_mem_cell (sx := true) (sy := false) (x := (T i).x₁) (y := (T i).y₀)
    ⟨⟨(hp i).1, le_rfl⟩, le_rfl, (hp i).2⟩ ⟨⟨h₀ ▸ (hp j).1, h₀.le⟩, h₁.ge, h₁ ▸ (hp j).2⟩

/-- **A tile's top-right corner is blocked exactly when the tiling goes on to the right below it**,
some tile having its top-left corner there. -/
lemma exists_right_below_iff (hT : IsTiling R T) (hp : Proper T) :
    (∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁) ↔ Blocked T (T i).x₁ (T i).y₁ := by
  have hiSW : (((T i).x₁, (T i).y₁) : ℝ × ℝ) ∈ (T i).cell true true :=
    ⟨⟨(hp i).1, le_rfl⟩, (hp i).2, le_rfl⟩
  refine ⟨fun ⟨k, hk₀, hk₁⟩ ↦ .inr ⟨⟨i, (hp i).1, le_rfl, .inr rfl⟩, k, hk₀.le,
    hk₀ ▸ (hp k).1, .inr hk₁⟩, ?_⟩
  -- A tile leaving the corner to the right above it makes the tile below-right stop there.
  have key : ∀ t, (T t).x₀ ≤ (T i).x₁ → (T i).x₁ < (T t).x₁ → (T t).y₀ = (T i).y₁ →
      ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁ := by
    intro t ht₀ ht₁ ht₂
    obtain ⟨m, ⟨⟨hm₀, hm₁⟩, hm₂, hm₃⟩, -⟩ := hT.existsUnique_cell false true
      (x := (T i).x₁) (y := (T i).y₁)
      ⟨⟨(hT.le_tile_x₀ i).trans (hp i).1.le, ht₁.trans_le (hT.tile_x₁_le t)⟩,
        (hT.le_tile_y₀ i).trans_lt (hp i).2, hT.tile_y₁_le i⟩
    refine ⟨m, le_antisymm hm₀ (not_lt.mp fun h ↦ ?_),
      (le_antisymm hm₃ (not_lt.mp fun h ↦ ?_)).symm⟩
    · have him := hT.eq_of_mem_cell hiSW (⟨⟨h, hm₁.le⟩, hm₂, hm₃⟩ : _ ∈ (T m).cell true true)
      rw [← him] at hm₁
      exact lt_irrefl _ hm₁
    · have htm := hT.eq_of_mem_cell (sx := false) (sy := false)
        (⟨⟨ht₀, ht₁⟩, ht₂.le, ht₂ ▸ (hp t).2⟩ : _ ∈ (T t).cell false false)
        (⟨⟨hm₀, hm₁⟩, hm₂.le, h⟩ : _ ∈ (T m).cell false false)
      rw [htm] at ht₂
      exact absurd ht₂ hm₂.ne
  rintro (⟨t, ht₀, ht₁, ht₂, ht₃⟩ | ⟨-, t, ht₀, ht₁, ht₂ | ht₂⟩)
  · rcases ht₂.lt_or_eq with ht₂ | ht₂
    · have hit := hT.eq_of_mem_cell hiSW (⟨⟨ht₀, ht₁.le⟩, ht₂, ht₃⟩ : _ ∈ (T t).cell true true)
      rw [← hit] at ht₁
      exact absurd ht₁ (lt_irrefl _)
    · exact key t ht₀.le ht₁ ht₂
  · exact key t ht₀ ht₁ ht₂
  · refine ⟨t, le_antisymm ht₀ (not_lt.mp fun h ↦ ?_), ht₂⟩
    have hit := hT.eq_of_mem_cell hiSW
      (⟨⟨h, ht₁.le⟩, ht₂ ▸ (hp t).2, ht₂.ge⟩ : _ ∈ (T t).cell true true)
    rw [← hit] at ht₁
    exact lt_irrefl _ ht₁

/-- **A tile's bottom-left corner is blocked exactly when the tiling goes on to the left above
it**, some tile having its bottom-right corner there. -/
lemma exists_left_above_iff (hT : IsTiling R T) (hp : Proper T) :
    (∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀) ↔ Blocked T (T i).x₀ (T i).y₀ := by
  have hiNE : (((T i).x₀, (T i).y₀) : ℝ × ℝ) ∈ (T i).cell false false :=
    ⟨⟨le_rfl, (hp i).1⟩, le_rfl, (hp i).2⟩
  refine ⟨fun ⟨k, hk₁, hk₀⟩ ↦ .inr ⟨⟨k, hk₁ ▸ (hp k).1, hk₁.ge, .inl hk₀⟩, i, le_rfl, (hp i).1,
    .inl rfl⟩, ?_⟩
  -- A tile arriving at the corner from the left below it makes the tile above-left stop there.
  have key : ∀ t, (T t).x₀ < (T i).x₀ → (T i).x₀ ≤ (T t).x₁ → (T t).y₁ = (T i).y₀ →
      ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀ := by
    intro t ht₀ ht₁ ht₂
    obtain ⟨m, ⟨⟨hm₀, hm₁⟩, hm₂, hm₃⟩, -⟩ := hT.existsUnique_cell true false
      (x := (T i).x₀) (y := (T i).y₀)
      ⟨⟨(hT.le_tile_x₀ t).trans_lt ht₀, (hp i).1.le.trans (hT.tile_x₁_le i)⟩,
        hT.le_tile_y₀ i, (hp i).2.trans_le (hT.tile_y₁_le i)⟩
    refine ⟨m, le_antisymm (not_lt.mp fun h ↦ ?_) hm₁, le_antisymm hm₂ (not_lt.mp fun h ↦ ?_)⟩
    · have him := hT.eq_of_mem_cell hiNE (⟨⟨hm₀.le, h⟩, hm₂, hm₃⟩ : _ ∈ (T m).cell false false)
      rw [← him] at hm₀
      exact lt_irrefl _ hm₀
    · have htm := hT.eq_of_mem_cell (sx := true) (sy := true)
        (⟨⟨ht₀, ht₁⟩, ht₂ ▸ (hp t).2, ht₂.ge⟩ : _ ∈ (T t).cell true true)
        (⟨⟨hm₀, hm₁⟩, h, hm₃.le⟩ : _ ∈ (T m).cell true true)
      rw [htm] at ht₂
      rw [ht₂] at hm₃
      exact lt_irrefl _ hm₃
  rintro (⟨t, ht₀, ht₁, ht₂, ht₃⟩ | ⟨⟨t, ht₀, ht₁, ht₂ | ht₂⟩, -⟩)
  · rcases ht₃.lt_or_eq with ht₃ | ht₃
    · have hit := hT.eq_of_mem_cell hiNE (⟨⟨ht₀.le, ht₁⟩, ht₂, ht₃⟩ : _ ∈ (T t).cell false false)
      rw [← hit] at ht₀
      exact absurd ht₀ (lt_irrefl _)
    · exact key t ht₀ ht₁.le ht₃.symm
  · refine ⟨t, le_antisymm (not_lt.mp fun h ↦ ?_) ht₁, ht₂⟩
    have hit := hT.eq_of_mem_cell hiNE
      (⟨⟨ht₀.le, h⟩, ht₂.le, ht₂ ▸ (hp t).2⟩ : _ ∈ (T t).cell false false)
    rw [← hit] at ht₀
    exact lt_irrefl _ ht₀
  · exact key t ht₀ ht₁ ht₂

/-- Below the top of `R`, an unblocked top-right corner is the bottom-right corner of a tile: the
tile above it stops there too. -/
lemma exists_above_of_not (hT : IsTiling R T) (hp : Proper T)
    (h : ¬ ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁) (hy : (T i).y₁ < R.y₁) :
    ∃ j, (T j).x₁ = (T i).x₁ ∧ (T j).y₀ = (T i).y₁ := by
  obtain ⟨m, ⟨⟨hm₀, hm₁⟩, hm₂, hm₃⟩, -⟩ := hT.existsUnique_cell true false
    (x := (T i).x₁) (y := (T i).y₁)
    ⟨⟨(hT.le_tile_x₀ i).trans_lt (hp i).1, hT.tile_x₁_le i⟩,
      (hT.le_tile_y₀ i).trans (hp i).2.le, hy⟩
  refine ⟨m, le_antisymm (not_lt.mp fun h' ↦ ?_) hm₁, le_antisymm hm₂ (not_lt.mp fun h' ↦ ?_)⟩
  · exact h ((exists_right_below_iff hT hp).mpr (.inl ⟨m, hm₀, h', hm₂, hm₃.le⟩))
  · have him := hT.eq_of_mem_cell (sx := true) (sy := true)
      (⟨⟨(hp i).1, le_rfl⟩, (hp i).2, le_rfl⟩ : _ ∈ (T i).cell true true)
      (⟨⟨hm₀, hm₁⟩, h', hm₃.le⟩ : _ ∈ (T m).cell true true)
    rw [← him] at hm₃
    exact lt_irrefl _ hm₃

/-- Above the bottom of `R`, an unblocked bottom-left corner is the top-left corner of a tile: the
tile below it starts there too. -/
lemma exists_below_of_not (hT : IsTiling R T) (hp : Proper T)
    (h : ¬ ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀) (hy : R.y₀ < (T i).y₀) :
    ∃ m, (T m).x₀ = (T i).x₀ ∧ (T m).y₁ = (T i).y₀ := by
  obtain ⟨m, ⟨⟨hm₀, hm₁⟩, hm₂, hm₃⟩, -⟩ := hT.existsUnique_cell false true
    (x := (T i).x₀) (y := (T i).y₀)
    ⟨⟨hT.le_tile_x₀ i, (hp i).1.trans_le (hT.tile_x₁_le i)⟩, hy,
      (hp i).2.le.trans (hT.tile_y₁_le i)⟩
  refine ⟨m, le_antisymm hm₀ (not_lt.mp fun h' ↦ ?_),
    (le_antisymm hm₃ (not_lt.mp fun h' ↦ ?_)).symm⟩
  · exact h ((exists_left_above_iff hT hp).mpr (.inl ⟨m, h', hm₁, hm₂.le, hm₃⟩))
  · have him := hT.eq_of_mem_cell (sx := false) (sy := false)
      (⟨⟨le_rfl, (hp i).1⟩, le_rfl, (hp i).2⟩ : _ ∈ (T i).cell false false)
      (⟨⟨hm₀, hm₁⟩, hm₂.le, h'⟩ : _ ∈ (T m).cell false false)
    rw [← him] at hm₂
    exact lt_irrefl _ hm₂

/-- A top-right corner after which the tiling neither goes on below nor above is the top-right
corner of `R`. -/
lemma corner_of_not_of_not (hT : IsTiling R T) (hp : Proper T) (hy : R.y₀ < R.y₁)
    (h₁ : ¬ ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁)
    (h₂ : ¬ ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₀ = (T i).y₁) :
    (T i).x₁ = R.x₁ ∧ (T i).y₁ = R.y₁ := by
  have hy₁ : (T i).y₁ = R.y₁ := le_antisymm (hT.tile_y₁_le i) (not_lt.mp fun h ↦
    h₂ (exists_above_of_not hT hp h₁ h))
  refine ⟨le_antisymm (hT.tile_x₁_le i) (not_lt.mp fun h ↦ h₁ ?_), hy₁⟩
  obtain ⟨m, ⟨⟨hm₀, hm₁⟩, hm₂, hm₃⟩, -⟩ := hT.existsUnique_cell false true
    (x := (T i).x₁) (y := (T i).y₁)
    ⟨⟨(hT.le_tile_x₀ i).trans (hp i).1.le, h⟩, hy₁ ▸ hy, (hT.tile_y₁_le i)⟩
  refine ⟨m, le_antisymm hm₀ (not_lt.mp fun h' ↦ ?_),
    le_antisymm (hy₁ ▸ hT.tile_y₁_le m) hm₃⟩
  have him := hT.eq_of_mem_cell (sx := true) (sy := true)
    (⟨⟨(hp i).1, le_rfl⟩, (hp i).2, le_rfl⟩ : _ ∈ (T i).cell true true)
    (⟨⟨h', hm₁.le⟩, hm₂, hm₃⟩ : _ ∈ (T m).cell true true)
  rw [← him] at hm₁
  exact lt_irrefl _ hm₁

/-- A bottom-left corner before which the tiling neither goes on above nor below is the
bottom-left corner of `R`. -/
lemma corner_of_not_of_not' (hT : IsTiling R T) (hp : Proper T) (hy : R.y₀ < R.y₁)
    (h₁ : ¬ ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀)
    (h₂ : ¬ ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₁ = (T i).y₀) :
    (T i).x₀ = R.x₀ ∧ (T i).y₀ = R.y₀ := by
  have hy₀ : (T i).y₀ = R.y₀ := (le_antisymm (hT.le_tile_y₀ i) (not_lt.mp fun h ↦
    h₂ (exists_below_of_not hT hp h₁ h))).symm
  refine ⟨(le_antisymm (hT.le_tile_x₀ i) (not_lt.mp fun h ↦ h₁ ?_)).symm, hy₀⟩
  obtain ⟨m, ⟨⟨hm₀, hm₁⟩, hm₂, hm₃⟩, -⟩ := hT.existsUnique_cell true false
    (x := (T i).x₀) (y := (T i).y₀)
    ⟨⟨h, (hp i).1.le.trans (hT.tile_x₁_le i)⟩, hT.le_tile_y₀ i, hy₀ ▸ hy⟩
  refine ⟨m, le_antisymm (not_lt.mp fun h' ↦ ?_) hm₁,
    le_antisymm hm₂ (hy₀ ▸ hT.le_tile_y₀ m)⟩
  have him := hT.eq_of_mem_cell (sx := false) (sy := false)
    (⟨⟨le_rfl, (hp i).1⟩, le_rfl, (hp i).2⟩ : _ ∈ (T i).cell false false)
    (⟨⟨hm₀.le, h'⟩, hm₂, hm₃⟩ : _ ∈ (T m).cell false false)
  rw [← him] at hm₀
  exact lt_irrefl _ hm₀

/-- Two distinct tiles with their top edges at one height do not overlap horizontally. -/
lemma x₁_le_of_y₁_eq (hT : IsTiling R T) (hp : Proper T) (hij : i ≠ j)
    (hy : (T i).y₁ = (T j).y₁) (hx : (T i).x₀ ≤ (T j).x₀) : (T i).x₁ ≤ (T j).x₀ :=
  not_lt.mp fun h ↦ hij (hT.eq_of_mem_cell (sx := false) (sy := true) (x := (T j).x₀)
    (y := (T j).y₁) ⟨⟨hx, h⟩, hy ▸ (hp i).2, hy.ge⟩ ⟨⟨le_rfl, (hp j).1⟩, (hp j).2, le_rfl⟩)

/-- Two distinct tiles with their bottom edges at one height do not overlap horizontally. -/
lemma x₁_le_of_y₀_eq (hT : IsTiling R T) (hp : Proper T) (hij : i ≠ j)
    (hy : (T i).y₀ = (T j).y₀) (hx : (T i).x₀ ≤ (T j).x₀) : (T i).x₁ ≤ (T j).x₀ :=
  not_lt.mp fun h ↦ hij (hT.eq_of_mem_cell (sx := false) (sy := false) (x := (T j).x₀)
    (y := (T j).y₀) ⟨⟨hx, h⟩, hy.le, hy ▸ (hp i).2⟩ ⟨⟨le_rfl, (hp j).1⟩, le_rfl, (hp j).2⟩)

omit [Fintype ι] in
/-- **A segment reaching left of a point has an edge arriving at the point from the left.** -/
lemma exists_edge_left [Finite ι] {a c y : ℝ} (h : SegStep T ((a, y) : ℝ × ℝ) (c, y))
    (hac : a < c) : ∃ t, (T t).x₀ < c ∧ c ≤ (T t).x₁ ∧ ((T t).y₀ = y ∨ (T t).y₁ = y) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set S := Finset.univ.filter fun t ↦ ((T t).y₀ = y ∨ (T t).y₁ = y) ∧ (T t).x₁ < c
  set M := (insert a (S.image fun t ↦ (T t).x₁)).max' (Finset.insert_nonempty _ _)
  have hM : M < c := by
    refine (Finset.max'_lt_iff _ _).mpr fun z hz ↦ ?_
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hac
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp ht).2.2
  have haM : a ≤ M := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  obtain ⟨t, ht⟩ := h.2 ((M + c) / 2) (mem_uIcc.mpr (.inl ⟨by linarith, by linarith⟩))
  have hedge : ((T t).y₀ = y ∨ (T t).y₁ = y) ∧ (T t).x₀ ≤ (M + c) / 2 ∧ (M + c) / 2 ≤ (T t).x₁ :=
    ht.elim (fun h ↦ ⟨.inl h.1.symm, h.2⟩) fun h ↦ ⟨.inr h.1.symm, h.2⟩
  refine ⟨t, by linarith [hedge.2.1], not_lt.mp fun hlt ↦ ?_, hedge.1⟩
  have := Finset.le_max' (insert a (S.image fun t ↦ (T t).x₁)) (T t).x₁
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge.1, hlt⟩)))
  linarith [hedge.2.2]

omit [Fintype ι] in
/-- **A segment reaching right of a point has an edge leaving the point to the right.** -/
lemma exists_edge_right [Finite ι] {c b y : ℝ} (h : SegStep T ((c, y) : ℝ × ℝ) (b, y))
    (hcb : c < b) : ∃ t, (T t).x₀ ≤ c ∧ c < (T t).x₁ ∧ ((T t).y₀ = y ∨ (T t).y₁ = y) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set S := Finset.univ.filter fun t ↦ ((T t).y₀ = y ∨ (T t).y₁ = y) ∧ c < (T t).x₀
  set m := (insert b (S.image fun t ↦ (T t).x₀)).min' (Finset.insert_nonempty _ _)
  have hm : c < m := by
    refine (Finset.lt_min'_iff _ _).mpr fun z hz ↦ ?_
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hcb
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp ht).2.2
  have hmb : m ≤ b := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  obtain ⟨t, ht⟩ := h.2 ((c + m) / 2) (mem_uIcc.mpr (.inl ⟨by linarith, by linarith⟩))
  have hedge : ((T t).y₀ = y ∨ (T t).y₁ = y) ∧ (T t).x₀ ≤ (c + m) / 2 ∧ (c + m) / 2 ≤ (T t).x₁ :=
    ht.elim (fun h ↦ ⟨.inl h.1.symm, h.2⟩) fun h ↦ ⟨.inr h.1.symm, h.2⟩
  refine ⟨t, not_lt.mp fun hlt ↦ ?_, by linarith [hedge.2.2], hedge.1⟩
  have := Finset.min'_le (insert b (S.image fun t ↦ (T t).x₀)) (T t).x₀
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge.1, hlt⟩)))
  linarith [hedge.2.1]

/-- The tile at the bottom-left corner of `R`. -/
lemma exists_bot_left (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) :
    ∃ k, (T k).x₀ = R.x₀ ∧ (T k).y₀ = R.y₀ := by
  obtain ⟨k, ⟨⟨hk₀, -⟩, hk₂, -⟩, -⟩ := hT.existsUnique_cell false false (x := R.x₀) (y := R.y₀)
    ⟨⟨le_rfl, hx⟩, le_rfl, hy⟩
  exact ⟨k, le_antisymm hk₀ (hT.le_tile_x₀ k), le_antisymm hk₂ (hT.le_tile_y₀ k)⟩

/-- The tile at the bottom-right corner of `R`. -/
lemma exists_bot_right (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) :
    ∃ k, (T k).x₁ = R.x₁ ∧ (T k).y₀ = R.y₀ := by
  obtain ⟨k, ⟨⟨-, hk₁⟩, hk₂, -⟩, -⟩ := hT.existsUnique_cell true false (x := R.x₁) (y := R.y₀)
    ⟨⟨hx, le_rfl⟩, le_rfl, hy⟩
  exact ⟨k, le_antisymm (hT.tile_x₁_le k) hk₁, le_antisymm hk₂ (hT.le_tile_y₀ k)⟩

/-- The tile at the top-left corner of `R`. -/
lemma exists_top_left (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) :
    ∃ k, (T k).x₀ = R.x₀ ∧ (T k).y₁ = R.y₁ := by
  obtain ⟨k, ⟨⟨hk₀, -⟩, -, hk₃⟩, -⟩ := hT.existsUnique_cell false true (x := R.x₀) (y := R.y₁)
    ⟨⟨le_rfl, hx⟩, hy, le_rfl⟩
  exact ⟨k, le_antisymm hk₀ (hT.le_tile_x₀ k), le_antisymm (hT.tile_y₁_le k) hk₃⟩

/-! ### Seymour's graph and its rotation -/

/-- The darts of Seymour's graph: an edge, a tile or `none` for the exterior edge, with one of its
ends, `false` for the bottom end and `true` for the top one. -/
abbrev Dart (ι : Type) := Option ι × Bool

/-- Exchanging the two ends of an edge. -/
def flipEnd : Equiv.Perm (Dart ι) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv d := by simp
  right_inv d := by simp

omit [Fintype ι] in
@[simp] lemma flipEnd_apply (d : Dart ι) : flipEnd d = (d.1, !d.2) := rfl

variable (R T) in
/-- The point at which a dart meets its vertex: the left end of the bottom or top edge of its
tile, or the bottom-left or top-left corner of `R` for the exterior edge. -/
def dartPt : Dart ι → ℝ × ℝ
  | (some i, false) => ((T i).x₀, (T i).y₀)
  | (some i, true) => ((T i).x₀, (T i).y₁)
  | (none, false) => (R.x₀, R.y₀)
  | (none, true) => (R.x₀, R.y₁)

lemma onEdge_dartPt (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) (d : Dart ι) :
    OnEdge T (dartPt R T d) := by
  rcases d with ⟨_ | i, _ | _⟩
  · obtain ⟨i, hi⟩ := exists_memBot_of_bot hT hx hy le_rfl hx.le
    exact ⟨i, .inl hi⟩
  · obtain ⟨i, hi⟩ := exists_memTop_of_top hT hx hy le_rfl hx.le
    exact ⟨i, .inr hi⟩
  · exact ⟨i, .inl ⟨rfl, le_rfl, (T i).hx⟩⟩
  · exact ⟨i, .inr ⟨rfl, le_rfl, (T i).hx⟩⟩

/-- **The vertex of Seymour's graph at a dart**: the horizontal segment carrying the bottom or top
edge of its tile, or the bottom or top of `R` for the exterior edge. -/
noncomputable def vert (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) (d : Dart ι) :
    Seg T :=
  Seg.mk (dartPt R T d) (onEdge_dartPt hT hx hy d)

open scoped Classical in
variable (R T) in
/-- **The rotation of Seymour's graph around its vertices**, read off the tiling with each edge
drawn up the vertical bisector of its tile. Around a segment it runs counterclockwise: rightwards
along the tiles below, round the right end, leftwards along the tiles above, and round the left
end, the exterior edge leaving the bottom of `R` downwards and the top upwards.

* At the top end of a tile `i` it passes to the next tile right below the same segment, the tile
  with its top-left corner at the top-right corner of `i`; failing that, to the rightmost tile
  above the segment, the one with its bottom-right corner there; failing that, to the exterior
  edge, `i` being the top-right tile of `R`.
* At the bottom end of a tile `i` it passes to the next tile left above the same segment;
  failing that, to the leftmost tile below it; failing that, to the exterior edge.
* At the ends of the exterior edge it passes to the bottom-right and the top-left tiles of `R`. -/
noncomputable def rot : Dart ι → Dart ι
  | (some i, true) =>
    if h : ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁ then (some h.choose, true)
    else if h : ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₀ = (T i).y₁ then (some h.choose, false)
    else (none, true)
  | (some i, false) =>
    if h : ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀ then (some h.choose, false)
    else if h : ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₁ = (T i).y₀ then (some h.choose, true)
    else (none, false)
  | (none, false) =>
    if h : ∃ k, (T k).x₁ = R.x₁ ∧ (T k).y₀ = R.y₀ then (some h.choose, false) else (none, false)
  | (none, true) =>
    if h : ∃ k, (T k).x₀ = R.x₀ ∧ (T k).y₁ = R.y₁ then (some h.choose, true) else (none, true)

open scoped Classical in
variable (R T) in
/-- The rotation run backwards: clockwise around each segment. -/
noncomputable def rotInv : Dart ι → Dart ι
  | (some i, true) =>
    if h : ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₁ = (T i).y₁ then (some h.choose, true)
    else if h : ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₀ = (T i).y₁ then (some h.choose, false)
    else (none, true)
  | (some i, false) =>
    if h : ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₀ = (T i).y₀ then (some h.choose, false)
    else if h : ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₁ = (T i).y₀ then (some h.choose, true)
    else (none, false)
  | (none, false) =>
    if h : ∃ k, (T k).x₀ = R.x₀ ∧ (T k).y₀ = R.y₀ then (some h.choose, false) else (none, false)
  | (none, true) =>
    if h : ∃ k, (T k).x₁ = R.x₁ ∧ (T k).y₁ = R.y₁ then (some h.choose, true) else (none, true)

section Rot

variable (hT : IsTiling R T) (hp : Proper T)
include hT hp

lemma rot_top_of_right (hk : (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁) :
    rot R T (some i, true) = (some k, true) := by
  classical
  have h : ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁ := ⟨k, hk⟩
  rw [rot, dite_eq_left h, eq_of_x₀_y₁ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

lemma rot_top_of_above (h₁ : ¬ ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁)
    (hk : (T k).x₁ = (T i).x₁ ∧ (T k).y₀ = (T i).y₁) :
    rot R T (some i, true) = (some k, false) := by
  classical
  have h : ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₀ = (T i).y₁ := ⟨k, hk⟩
  rw [rot, dite_eq_right h₁, dite_eq_left h, eq_of_x₁_y₀ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

omit hT hp in
lemma rot_top_of_not (h₁ : ¬ ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁)
    (h₂ : ¬ ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₀ = (T i).y₁) :
    rot R T (some i, true) = (none, true) := by
  classical
  rw [rot, dite_eq_right h₁, dite_eq_right h₂]

lemma rot_bot_of_left (hk : (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀) :
    rot R T (some i, false) = (some k, false) := by
  classical
  have h : ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀ := ⟨k, hk⟩
  rw [rot, dite_eq_left h, eq_of_x₁_y₀ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

lemma rot_bot_of_below (h₁ : ¬ ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀)
    (hk : (T k).x₀ = (T i).x₀ ∧ (T k).y₁ = (T i).y₀) :
    rot R T (some i, false) = (some k, true) := by
  classical
  have h : ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₁ = (T i).y₀ := ⟨k, hk⟩
  rw [rot, dite_eq_right h₁, dite_eq_left h, eq_of_x₀_y₁ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

omit hT hp in
lemma rot_bot_of_not (h₁ : ¬ ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀)
    (h₂ : ¬ ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₁ = (T i).y₀) :
    rot R T (some i, false) = (none, false) := by
  classical
  rw [rot, dite_eq_right h₁, dite_eq_right h₂]

lemma rot_none_false (hk : (T k).x₁ = R.x₁ ∧ (T k).y₀ = R.y₀) :
    rot R T (none, false) = (some k, false) := by
  classical
  have h : ∃ k, (T k).x₁ = R.x₁ ∧ (T k).y₀ = R.y₀ := ⟨k, hk⟩
  rw [rot, dite_eq_left h, eq_of_x₁_y₀ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

lemma rot_none_true (hk : (T k).x₀ = R.x₀ ∧ (T k).y₁ = R.y₁) :
    rot R T (none, true) = (some k, true) := by
  classical
  have h : ∃ k, (T k).x₀ = R.x₀ ∧ (T k).y₁ = R.y₁ := ⟨k, hk⟩
  rw [rot, dite_eq_left h, eq_of_x₀_y₁ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

lemma rotInv_top_of_left (hk : (T k).x₁ = (T i).x₀ ∧ (T k).y₁ = (T i).y₁) :
    rotInv R T (some i, true) = (some k, true) := by
  classical
  have h : ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₁ = (T i).y₁ := ⟨k, hk⟩
  rw [rotInv, dite_eq_left h, eq_of_x₁_y₁ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

lemma rotInv_top_of_above (h₁ : ¬ ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₁ = (T i).y₁)
    (hk : (T k).x₀ = (T i).x₀ ∧ (T k).y₀ = (T i).y₁) :
    rotInv R T (some i, true) = (some k, false) := by
  classical
  have h : ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₀ = (T i).y₁ := ⟨k, hk⟩
  rw [rotInv, dite_eq_right h₁, dite_eq_left h, eq_of_x₀_y₀ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

omit hT hp in
lemma rotInv_top_of_not (h₁ : ¬ ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₁ = (T i).y₁)
    (h₂ : ¬ ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₀ = (T i).y₁) :
    rotInv R T (some i, true) = (none, true) := by
  classical
  rw [rotInv, dite_eq_right h₁, dite_eq_right h₂]

lemma rotInv_bot_of_right (hk : (T k).x₀ = (T i).x₁ ∧ (T k).y₀ = (T i).y₀) :
    rotInv R T (some i, false) = (some k, false) := by
  classical
  have h : ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₀ = (T i).y₀ := ⟨k, hk⟩
  rw [rotInv, dite_eq_left h, eq_of_x₀_y₀ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

lemma rotInv_bot_of_below (h₁ : ¬ ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₀ = (T i).y₀)
    (hk : (T k).x₁ = (T i).x₁ ∧ (T k).y₁ = (T i).y₀) :
    rotInv R T (some i, false) = (some k, true) := by
  classical
  have h : ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₁ = (T i).y₀ := ⟨k, hk⟩
  rw [rotInv, dite_eq_right h₁, dite_eq_left h, eq_of_x₁_y₁ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

omit hT hp in
lemma rotInv_bot_of_not (h₁ : ¬ ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₀ = (T i).y₀)
    (h₂ : ¬ ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₁ = (T i).y₀) :
    rotInv R T (some i, false) = (none, false) := by
  classical
  rw [rotInv, dite_eq_right h₁, dite_eq_right h₂]

lemma rotInv_none_false (hk : (T k).x₀ = R.x₀ ∧ (T k).y₀ = R.y₀) :
    rotInv R T (none, false) = (some k, false) := by
  classical
  have h : ∃ k, (T k).x₀ = R.x₀ ∧ (T k).y₀ = R.y₀ := ⟨k, hk⟩
  rw [rotInv, dite_eq_left h, eq_of_x₀_y₀ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

lemma rotInv_none_true (hk : (T k).x₁ = R.x₁ ∧ (T k).y₁ = R.y₁) :
    rotInv R T (none, true) = (some k, true) := by
  classical
  have h : ∃ k, (T k).x₁ = R.x₁ ∧ (T k).y₁ = R.y₁ := ⟨k, hk⟩
  rw [rotInv, dite_eq_left h, eq_of_x₁_y₁ hT hp (h.choose_spec.1.trans hk.1.symm)
    (h.choose_spec.2.trans hk.2.symm)]

end Rot

section Rot'

variable (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
include hT hp hx hy

/-- Running the rotation backwards undoes it. -/
lemma rotInv_rot (d : Dart ι) : rotInv R T (rot R T d) = d := by
  rcases d with ⟨_ | i, _ | _⟩
  · obtain ⟨r, hr⟩ := exists_bot_right hT hx hy
    rw [rot_none_false hT hp hr]
    refine rotInv_bot_of_not (fun ⟨k, hk₀, _⟩ ↦ ?_) fun ⟨k, _, hk₁⟩ ↦ ?_
    · linarith [(hp k).1, hT.tile_x₁_le k, hr.1]
    · linarith [(hp k).2, hT.le_tile_y₀ k, hr.2]
  · obtain ⟨m, hm⟩ := exists_top_left hT hx hy
    rw [rot_none_true hT hp hm]
    refine rotInv_top_of_not (fun ⟨k, hk₁, _⟩ ↦ ?_) fun ⟨k, _, hk₀⟩ ↦ ?_
    · linarith [(hp k).1, hT.le_tile_x₀ k, hm.1]
    · linarith [(hp k).2, hT.tile_y₁_le k, hm.2]
  · by_cases h₁ : ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀
    · obtain ⟨k, hk⟩ := h₁
      rw [rot_bot_of_left hT hp hk, rotInv_bot_of_right hT hp ⟨hk.1.symm, hk.2.symm⟩]
    by_cases h₂ : ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₁ = (T i).y₀
    · obtain ⟨m, hm⟩ := h₂
      rw [rot_bot_of_below hT hp h₁ hm]
      refine rotInv_top_of_above hT hp (fun ⟨k, hk₁, hk₂⟩ ↦ h₁ ?_) ⟨hm.1.symm, hm.2.symm⟩
      refine (exists_left_above_iff hT hp).mpr (.inr ⟨⟨k, ?_, ?_, .inr ?_⟩, i, le_rfl, (hp i).1,
        .inl rfl⟩)
      · rw [← hm.1, ← hk₁]
        exact (hp k).1
      · rw [← hm.1, ← hk₁]
      · rw [hk₂, hm.2]
    · obtain ⟨hx₀, hy₀⟩ := corner_of_not_of_not' hT hp hy h₁ h₂
      rw [rot_bot_of_not h₁ h₂, rotInv_none_false hT hp ⟨hx₀, hy₀⟩]
  · by_cases h₁ : ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁
    · obtain ⟨k, hk⟩ := h₁
      rw [rot_top_of_right hT hp hk, rotInv_top_of_left hT hp ⟨hk.1.symm, hk.2.symm⟩]
    by_cases h₂ : ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₀ = (T i).y₁
    · obtain ⟨k, hk⟩ := h₂
      rw [rot_top_of_above hT hp h₁ hk]
      refine rotInv_bot_of_below hT hp (fun ⟨k', hk'₀, hk'₁⟩ ↦ h₁ ?_) ⟨hk.1.symm, hk.2.symm⟩
      refine (exists_right_below_iff hT hp).mpr (.inr ⟨⟨i, (hp i).1, le_rfl, .inr rfl⟩, k', ?_,
        ?_, .inl ?_⟩)
      · rw [hk'₀, hk.1]
      · rw [← hk.1, ← hk'₀]
        exact (hp k').1
      · rw [hk'₁, hk.2]
    · obtain ⟨hx₁, hy₁⟩ := corner_of_not_of_not hT hp hy h₁ h₂
      rw [rot_top_of_not h₁ h₂, rotInv_none_true hT hp ⟨hx₁, hy₁⟩]

lemma rot_injective : Function.Injective (rot R T) :=
  Function.LeftInverse.injective (rotInv_rot hT hp hx hy)

lemma rot_bijective : Function.Bijective (rot R T) :=
  Finite.injective_iff_bijective.mp (rot_injective hT hp hx hy)

omit hp in
lemma vert_eq_vert_iff {d d' : Dart ι} :
    vert hT hx hy d = vert hT hx hy d' ↔ SegStep T (dartPt R T d) (dartPt R T d') :=
  Seg.mk_eq_mk

/-- **The rotation stays at its vertex**: it passes between darts of one segment. -/
lemma vert_rot (d : Dart ι) : vert hT hx hy (rot R T d) = vert hT hx hy d := by
  have hRx : ∀ k, (T k).x₀ ∈ Icc R.x₀ R.x₁ := fun k ↦
    ⟨hT.le_tile_x₀ k, (hp k).1.le.trans (hT.tile_x₁_le k)⟩
  rcases d with ⟨_ | i, _ | _⟩
  · obtain ⟨r, hr⟩ := exists_bot_right hT hx hy
    rw [rot_none_false hT hp hr, vert_eq_vert_iff]
    change SegStep T ((T r).x₀, (T r).y₀) (R.x₀, R.y₀)
    rw [hr.2]
    exact segStep_bot hT hx hy (hRx r) ⟨le_rfl, hx.le⟩
  · obtain ⟨m, hm⟩ := exists_top_left hT hx hy
    rw [rot_none_true hT hp hm, vert_eq_vert_iff]
    change SegStep T ((T m).x₀, (T m).y₁) (R.x₀, R.y₁)
    rw [hm.1, hm.2]
    exact segStep_top hT hx hy ⟨le_rfl, hx.le⟩ ⟨le_rfl, hx.le⟩
  · have hbot : MemBot (T i) ((T i).x₀, (T i).y₀) := ⟨rfl, le_rfl, (T i).hx⟩
    by_cases h₁ : ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀
    · obtain ⟨k, hk⟩ := h₁
      rw [rot_bot_of_left hT hp hk, vert_eq_vert_iff]
      change SegStep T ((T k).x₀, (T k).y₀) ((T i).x₀, (T i).y₀)
      rw [← hk.1, ← hk.2]
      exact segStep_of_memBot ⟨rfl, le_rfl, (T k).hx⟩ ⟨rfl, (T k).hx, le_rfl⟩
    by_cases h₂ : ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₁ = (T i).y₀
    · obtain ⟨m, hm⟩ := h₂
      rw [rot_bot_of_below hT hp h₁ hm, vert_eq_vert_iff]
      change SegStep T ((T m).x₀, (T m).y₁) ((T i).x₀, (T i).y₀)
      rw [hm.1, hm.2]
      exact .refl ⟨i, .inl hbot⟩
    · obtain ⟨hx₀, hy₀⟩ := corner_of_not_of_not' hT hp hy h₁ h₂
      rw [rot_bot_of_not h₁ h₂, vert_eq_vert_iff]
      change SegStep T (R.x₀, R.y₀) ((T i).x₀, (T i).y₀)
      rw [hx₀, hy₀]
      exact .refl ⟨i, .inl (hx₀ ▸ hy₀ ▸ hbot)⟩
  · have htop : MemTop (T i) ((T i).x₀, (T i).y₁) := ⟨rfl, le_rfl, (T i).hx⟩
    by_cases h₁ : ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁
    · obtain ⟨k, hk⟩ := h₁
      rw [rot_top_of_right hT hp hk, vert_eq_vert_iff]
      change SegStep T ((T k).x₀, (T k).y₁) ((T i).x₀, (T i).y₁)
      rw [hk.1, hk.2]
      exact segStep_of_memTop ⟨rfl, (T i).hx, le_rfl⟩ htop
    by_cases h₂ : ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₀ = (T i).y₁
    · obtain ⟨k, hk⟩ := h₂
      rw [rot_top_of_above hT hp h₁ hk, vert_eq_vert_iff]
      change SegStep T ((T k).x₀, (T k).y₀) ((T i).x₀, (T i).y₁)
      refine (segStep_of_memBot (q := ((T k).x₁, (T k).y₀)) ⟨rfl, le_rfl, (T k).hx⟩
        ⟨rfl, (T k).hx, le_rfl⟩).trans ?_
      rw [hk.1, hk.2]
      exact segStep_of_memTop ⟨rfl, (T i).hx, le_rfl⟩ htop
    · obtain ⟨hx₁, hy₁⟩ := corner_of_not_of_not hT hp hy h₁ h₂
      rw [rot_top_of_not h₁ h₂, vert_eq_vert_iff]
      change SegStep T (R.x₀, R.y₁) ((T i).x₀, (T i).y₁)
      rw [hy₁]
      exact segStep_top hT hx hy ⟨le_rfl, hx.le⟩ (hRx i)

end Rot'

/-! ### The vertices are the segments -/

section Vertices

variable (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)

/-- The rotation, as a permutation of the darts. -/
noncomputable def rotPerm : Equiv.Perm (Dart ι) :=
  Equiv.ofBijective (rot R T) (rot_bijective hT hp hx hy)

lemma rotPerm_apply (d : Dart ι) : rotPerm hT hp hx hy d = rot R T d := rfl

lemma sameCycle_rot (d : Dart ι) : (rotPerm hT hp hx hy).SameCycle d (rot R T d) :=
  Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

omit [Fintype ι] in
/-- Two points of one segment after the top edge of a tile `i`, and so after its top-right
corner: an edge leaves that corner to the right. -/
private lemma exists_edge_right_of_top [Finite ι] {z : ℝ}
    (h : SegStep T ((T i).x₀, (T i).y₁) (z, (T i).y₁)) (hz : (T i).x₁ < z) :
    ∃ t, (T t).x₀ ≤ (T i).x₁ ∧ (T i).x₁ < (T t).x₁ ∧
      ((T t).y₀ = (T i).y₁ ∨ (T t).y₁ = (T i).y₁) :=
  exists_edge_right
    ((segStep_of_memTop ⟨rfl, (T i).hx, le_rfl⟩ ⟨rfl, le_rfl, (T i).hx⟩).trans h) hz

include hT hp hx hy

/-- **Along the tiles below a segment the rotation moves right**: from the top end of a tile, it
reaches the top end of every tile below the same segment further right. -/
lemma sameCycle_top {i' : ι}
    (h : vert hT hx hy (some i, true) = vert hT hx hy (some i', true))
    (hle : (T i).x₀ ≤ (T i').x₀) :
    (rotPerm hT hp hx hy).SameCycle (some i, true) (some i', true) := by
  classical
  suffices key : ∀ n i, (Finset.univ.filter fun j ↦ (T i).x₀ < (T j).x₀).card = n →
      vert hT hx hy (some i, true) = vert hT hx hy (some i', true) → (T i).x₀ ≤ (T i').x₀ →
      (rotPerm hT hp hx hy).SameCycle (some i, true) (some i', true) from key _ i rfl h hle
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hn h hle
    rcases eq_or_ne i i' with rfl | hne
    · exact .refl _ _
    have hseg := (vert_eq_vert_iff hT hx hy).mp h
    have hy₁ : (T i).y₁ = (T i').y₁ := hseg.1
    have hx₁ : (T i).x₁ ≤ (T i').x₀ := x₁_le_of_y₁_eq hT hp hne hy₁ hle
    change SegStep T ((T i).x₀, (T i).y₁) ((T i').x₀, (T i').y₁) at hseg
    rw [← hy₁] at hseg
    have hright : ∃ t, (T t).x₀ ≤ (T i).x₁ ∧ (T i).x₁ < (T t).x₁ ∧
        ((T t).y₀ = (T i).y₁ ∨ (T t).y₁ = (T i).y₁) := by
      rcases hx₁.lt_or_eq with hlt | heq
      · exact exists_edge_right_of_top hseg hlt
      · exact ⟨i', heq.ge, heq ▸ (hp i').1, .inr hy₁.symm⟩
    obtain ⟨k, hk⟩ := (exists_right_below_iff hT hp).mpr
      (.inr ⟨⟨i, (hp i).1, le_rfl, .inr rfl⟩, hright⟩)
    have hrot := rot_top_of_right hT hp hk
    refine (sameCycle_rot hT hp hx hy _).trans ?_
    rw [hrot]
    refine ih _ ?_ k rfl (by rw [← hrot, vert_rot hT hp hx hy]; exact h) (hk.1 ▸ hx₁)
    rw [← hn]
    refine Finset.card_lt_card ⟨fun j hj ↦ ?_, fun hsub ↦ ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      linarith [(hp i).1, hk.1]
    · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ k, by linarith [(hp i).1, hk.1]⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact lt_irrefl _ this

/-- **Along the tiles above a segment the rotation moves left**: from the bottom end of a tile, it
reaches the bottom end of every tile above the same segment further left. -/
lemma sameCycle_bot {i' : ι}
    (h : vert hT hx hy (some i, false) = vert hT hx hy (some i', false))
    (hle : (T i').x₀ ≤ (T i).x₀) :
    (rotPerm hT hp hx hy).SameCycle (some i, false) (some i', false) := by
  classical
  suffices key : ∀ n i, (Finset.univ.filter fun j ↦ (T j).x₀ < (T i).x₀).card = n →
      vert hT hx hy (some i, false) = vert hT hx hy (some i', false) → (T i').x₀ ≤ (T i).x₀ →
      (rotPerm hT hp hx hy).SameCycle (some i, false) (some i', false) from key _ i rfl h hle
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hn h hle
    rcases eq_or_ne i i' with rfl | hne
    · exact .refl _ _
    have hseg := (vert_eq_vert_iff hT hx hy).mp h
    have hy₀ : (T i).y₀ = (T i').y₀ := hseg.1
    have hx₁ : (T i').x₁ ≤ (T i).x₀ := x₁_le_of_y₀_eq hT hp hne.symm hy₀.symm hle
    change SegStep T ((T i).x₀, (T i).y₀) ((T i').x₀, (T i').y₀) at hseg
    rw [← hy₀] at hseg
    have hleft : ∃ t, (T t).x₀ < (T i).x₀ ∧ (T i).x₀ ≤ (T t).x₁ ∧
        ((T t).y₀ = (T i).y₀ ∨ (T t).y₁ = (T i).y₀) := by
      rcases hx₁.lt_or_eq with hlt | heq
      · refine exists_edge_left (a := (T i').x₁) ?_ hlt
        refine (segStep_of_memBot (T := T) (i := i') ⟨hy₀, (T i').hx, le_rfl⟩
          ⟨hy₀, le_rfl, (T i').hx⟩).trans hseg.symm
      · exact ⟨i', heq ▸ (hp i').1, heq.ge, .inl hy₀.symm⟩
    obtain ⟨k, hk⟩ := (exists_left_above_iff hT hp).mpr
      (.inr ⟨hleft, i, le_rfl, (hp i).1, .inl rfl⟩)
    have hrot := rot_bot_of_left hT hp hk
    refine (sameCycle_rot hT hp hx hy _).trans ?_
    rw [hrot]
    have hk' : vert hT hx hy (some k, false) = vert hT hx hy (some i', false) := by
      rw [← hrot, vert_rot hT hp hx hy]
      exact h
    have hle' : (T i').x₀ ≤ (T k).x₀ := by
      rcases eq_or_ne k i' with rfl | hki
      · exact le_rfl
      refine not_lt.mp fun hlt ↦ ?_
      have hyk : (T k).y₀ = (T i').y₀ := hk.2.trans hy₀
      have := x₁_le_of_y₀_eq hT hp hki hyk hlt.le
      linarith [hk.1, (hp i').1]
    refine ih _ ?_ k rfl hk' hle'
    rw [← hn]
    refine Finset.card_lt_card ⟨fun j hj ↦ ?_, fun hsub ↦ ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      linarith [(hp k).1, hk.1]
    · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ k, by linarith [(hp k).1, hk.1]⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact lt_irrefl _ this

/-- The top ends of two tiles below one segment lie in one orbit of the rotation. -/
lemma sameCycle_top_top {i' : ι}
    (h : vert hT hx hy (some i, true) = vert hT hx hy (some i', true)) :
    (rotPerm hT hp hx hy).SameCycle (some i, true) (some i', true) := by
  rcases le_total (T i).x₀ (T i').x₀ with hle | hle
  · exact sameCycle_top hT hp hx hy h hle
  · exact (sameCycle_top hT hp hx hy h.symm hle).symm

/-- The bottom ends of two tiles above one segment lie in one orbit of the rotation. -/
lemma sameCycle_bot_bot {i' : ι}
    (h : vert hT hx hy (some i, false) = vert hT hx hy (some i', false)) :
    (rotPerm hT hp hx hy).SameCycle (some i, false) (some i', false) := by
  rcases le_total (T i').x₀ (T i).x₀ with hle | hle
  · exact sameCycle_bot hT hp hx hy h hle
  · exact (sameCycle_bot hT hp hx hy h.symm hle).symm

/-- Round the right end of a segment, the rotation passes from the tiles below it to the tiles
above it. -/
lemma sameCycle_top_bot (h : vert hT hx hy (some i, true) = vert hT hx hy (some j, false)) :
    (rotPerm hT hp hx hy).SameCycle (some i, true) (some j, false) := by
  classical
  obtain ⟨r, hr, hrmax⟩ := (Finset.univ.filter fun i' ↦
    vert hT hx hy (some i', true) = vert hT hx hy (some i, true)).exists_max_image
    (fun i' ↦ (T i').x₀) ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hr' : vert hT hx hy (some r, true) = vert hT hx hy (some i, true) :=
    (Finset.mem_filter.mp hr).2
  refine (sameCycle_top_top hT hp hx hy hr'.symm).trans ?_
  have h₁ : ¬ ∃ k, (T k).x₀ = (T r).x₁ ∧ (T k).y₁ = (T r).y₁ := by
    rintro ⟨k, hk⟩
    have hk' : vert hT hx hy (some k, true) = vert hT hx hy (some i, true) := by
      rw [← rot_top_of_right hT hp hk, vert_rot hT hp hx hy, hr']
    have := hrmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩)
    linarith [(hp r).1, hk.1]
  by_cases h₂ : ∃ k, (T k).x₁ = (T r).x₁ ∧ (T k).y₀ = (T r).y₁
  · obtain ⟨k, hk⟩ := h₂
    have hrot := rot_top_of_above hT hp h₁ hk
    refine (sameCycle_rot hT hp hx hy _).trans ?_
    rw [hrot]
    refine sameCycle_bot_bot hT hp hx hy ?_
    rw [← hrot, vert_rot hT hp hx hy, hr', h]
  · obtain ⟨-, hy₁⟩ := corner_of_not_of_not hT hp hy h₁ h₂
    have hseg := ((vert_eq_vert_iff hT hx hy).mp (hr'.trans h)).1
    change (T r).y₁ = (T j).y₀ at hseg
    linarith [(hp j).2, hT.tile_y₁_le j]

/-- Round the left end of the bottom of `R`, the rotation passes from the tiles above it to the
exterior edge. -/
lemma sameCycle_bot_none (h : vert hT hx hy (some j, false) = vert hT hx hy (none, false)) :
    (rotPerm hT hp hx hy).SameCycle (some j, false) (none, false) := by
  classical
  obtain ⟨l, hl, hlmin⟩ := (Finset.univ.filter fun j' ↦
    vert hT hx hy (some j', false) = vert hT hx hy (some j, false)).exists_min_image
    (fun j' ↦ (T j').x₀) ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hl' : vert hT hx hy (some l, false) = vert hT hx hy (some j, false) :=
    (Finset.mem_filter.mp hl).2
  refine (sameCycle_bot_bot hT hp hx hy hl'.symm).trans ?_
  have h₁ : ¬ ∃ k, (T k).x₁ = (T l).x₀ ∧ (T k).y₀ = (T l).y₀ := by
    rintro ⟨k, hk⟩
    have hk' : vert hT hx hy (some k, false) = vert hT hx hy (some j, false) := by
      rw [← rot_bot_of_left hT hp hk, vert_rot hT hp hx hy, hl']
    have := hlmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩)
    linarith [(hp k).1, hk.1]
  have hy₀ : (T l).y₀ = R.y₀ := ((vert_eq_vert_iff hT hx hy).mp (hl'.trans h)).1
  have h₂ : ¬ ∃ k, (T k).x₀ = (T l).x₀ ∧ (T k).y₁ = (T l).y₀ := by
    rintro ⟨k, -, hk⟩
    linarith [(hp k).2, hT.le_tile_y₀ k]
  rw [← rot_bot_of_not h₁ h₂]
  exact sameCycle_rot hT hp hx hy _

/-- **The darts at a vertex form one orbit of the rotation**: the vertices of the rotation system
are exactly the horizontal segments. -/
theorem sameCycle_of_vert_eq {d d' : Dart ι} (h : vert hT hx hy d = vert hT hx hy d') :
    (rotPerm hT hp hx hy).SameCycle d d' := by
  have hy' := ((vert_eq_vert_iff hT hx hy).mp h).1
  -- the top end of the top-left tile of `R` shares its vertex with the exterior edge
  obtain ⟨m, hm⟩ := exists_top_left hT hx hy
  have htop : (rotPerm hT hp hx hy).SameCycle (none, true) (some m, true) := by
    rw [← rot_none_true hT hp hm]
    exact sameCycle_rot hT hp hx hy _
  have hvtop : vert hT hx hy (some m, true) = vert hT hx hy (none, true) := by
    rw [← rot_none_true hT hp hm, vert_rot hT hp hx hy]
  rcases d with ⟨_ | i, _ | _⟩ <;> rcases d' with ⟨_ | i', _ | _⟩
  all_goals change (dartPt R T _).2 = (dartPt R T _).2 at hy'
  all_goals simp only [dartPt] at hy'
  · exact .refl _ _
  · exact absurd hy' hy.ne
  · exact (sameCycle_bot_none hT hp hx hy h.symm).symm
  · linarith [(hp i').2, hT.le_tile_y₀ i']
  · exact absurd hy' hy.ne'
  · exact .refl _ _
  · linarith [(hp i').2, hT.tile_y₁_le i']
  · exact htop.trans (sameCycle_top_top hT hp hx hy (hvtop.trans h))
  · exact sameCycle_bot_none hT hp hx hy h
  · linarith [(hp i).2, hT.tile_y₁_le i]
  · exact sameCycle_bot_bot hT hp hx hy h
  · exact (sameCycle_top_bot hT hp hx hy h.symm).symm
  · linarith [(hp i).2, hT.le_tile_y₀ i]
  · exact (htop.trans (sameCycle_top_top hT hp hx hy (hvtop.trans h.symm))).symm
  · exact sameCycle_top_bot hT hp hx hy h
  · exact sameCycle_top_top hT hp hx hy h

end Vertices

/-! ### The faces of the embedding -/

variable (R T) in
/-- A **face** of the planar embedding of Seymour's graph: a V-link of the tiling, or one of the
two outer faces into which the exterior edge divides the outside of `R`. -/
inductive Face : Type where
  /-- The outer face along the left edge of `R`. -/
  | left : Face
  /-- The outer face along the right edge of `R`. -/
  | right : Face
  /-- The face along a V-link of the tiling. -/
  | link (l : Link R T) : Face

/-- The abscissa of a face: the common abscissa of the vertical stretch it runs along. -/
def Face.c : Face R T → ℝ
  | .left => R.x₀
  | .right => R.x₁
  | .link l => l.c

/-- The face along the left edge of a tile: the left outer face when the tile reaches the left
edge of `R`, and otherwise the V-link its left edge lies on (`ReducibleLink.exists_link_left`). -/
noncomputable def leftFace (hT : IsTiling R T) (hp : Proper T) (i : ι) : Face R T :=
  if h : (T i).x₀ = R.x₀ then .left
  else .link (exists_link_left hT hp ((hT.le_tile_x₀ i).lt_of_ne fun h' ↦ h h'.symm)).choose

/-- The face along the right edge of a tile. -/
noncomputable def rightFace (hT : IsTiling R T) (hp : Proper T) (i : ι) : Face R T :=
  if h : (T i).x₁ = R.x₁ then .right
  else .link (exists_link_right hT hp ((hT.tile_x₁_le i).lt_of_ne h)).choose

/-- The left face of a tile lies at the abscissa of its left edge. -/
lemma c_leftFace (hT : IsTiling R T) (hp : Proper T) (i : ι) :
    (leftFace hT hp i).c = (T i).x₀ := by
  by_cases h : (T i).x₀ = R.x₀
  · simp only [leftFace, dite_eq_left h]
    exact h.symm
  · simp only [leftFace, dite_eq_right h]
    exact (exists_link_left hT hp ((hT.le_tile_x₀ i).lt_of_ne fun h' ↦ h h'.symm)).choose_spec.1

/-- The right face of a tile lies at the abscissa of its right edge. -/
lemma c_rightFace (hT : IsTiling R T) (hp : Proper T) (i : ι) :
    (rightFace hT hp i).c = (T i).x₁ := by
  by_cases h : (T i).x₁ = R.x₁
  · simp only [rightFace, dite_eq_left h]
    exact h.symm
  · simp only [rightFace, dite_eq_right h]
    exact (exists_link_right hT hp ((hT.tile_x₁_le i).lt_of_ne h)).choose_spec.1

/-- The left face of a tile is the left outer face exactly when the tile reaches the left edge
of `R`. -/
lemma leftFace_eq_left_iff (hT : IsTiling R T) (hp : Proper T) :
    leftFace hT hp i = .left ↔ (T i).x₀ = R.x₀ := by
  unfold leftFace
  split
  · next h => exact iff_of_true rfl h
  · next h => exact iff_of_false nofun h

/-- The right face of a tile is the right outer face exactly when the tile reaches the right
edge of `R`. -/
lemma rightFace_eq_right_iff (hT : IsTiling R T) (hp : Proper T) :
    rightFace hT hp i = .right ↔ (T i).x₁ = R.x₁ := by
  unfold rightFace
  split
  · next h => exact iff_of_true rfl h
  · next h => exact iff_of_false nofun h

/-- The right face of a tile is never the left outer face. -/
lemma rightFace_ne_left (hT : IsTiling R T) (hp : Proper T) (i : ι) :
    rightFace hT hp i ≠ .left := by
  unfold rightFace
  split <;> exact nofun

/-- **The left face of a tile is the V-link carrying its left edge**: `leftFace` lands on a link
exactly when the tile abuts it on its right side. Uniqueness is `Link.eq_of_overlap`. -/
lemma leftFace_eq_link_iff (hT : IsTiling R T) (hp : Proper T) {l : Link R T} :
    leftFace hT hp i = .link l ↔ IsRight l i := by
  by_cases h : (T i).x₀ = R.x₀
  · simp only [leftFace, dite_eq_left h]
    exact iff_of_false nofun fun hcon ↦
      absurd l.x₀_lt (by rw [← hcon.1, h]; exact lt_irrefl _)
  · simp only [leftFace, dite_eq_right h]
    obtain ⟨hc, hlo, hhi⟩ := (exists_link_left hT hp
      ((hT.le_tile_x₀ i).lt_of_ne fun h' ↦ h h'.symm)).choose_spec
    rw [Face.link.injEq]
    constructor
    · rintro rfl
      exact ⟨hc.symm, hlo, hhi⟩
    · rintro ⟨hc', hlo', hhi'⟩
      exact Link.eq_of_overlap (hc.trans hc') (hp i).2 hlo hhi hlo' hhi'

/-- **The right face of a tile is the V-link carrying its right edge**: `rightFace` lands on a
link exactly when the tile abuts it on its left side. -/
lemma rightFace_eq_link_iff (hT : IsTiling R T) (hp : Proper T) {l : Link R T} :
    rightFace hT hp i = .link l ↔ IsLeft l i := by
  by_cases h : (T i).x₁ = R.x₁
  · simp only [rightFace, dite_eq_left h]
    exact iff_of_false nofun fun hcon ↦
      absurd l.lt_x₁ (by rw [← hcon.1, h]; exact lt_irrefl _)
  · simp only [rightFace, dite_eq_right h]
    obtain ⟨hc, hlo, hhi⟩ := (exists_link_right hT hp
      ((hT.tile_x₁_le i).lt_of_ne h)).choose_spec
    rw [Face.link.injEq]
    constructor
    · rintro rfl
      exact ⟨hc.symm, hlo, hhi⟩
    · rintro ⟨hc', hlo', hhi'⟩
      exact Link.eq_of_overlap (hc.trans hc') (hp i).2 hlo hhi hlo' hhi'

/-- A right edge and a left edge on one vertical line, sharing a stretch of positive length, lie on
one face. -/
lemma rightFace_eq_leftFace (hT : IsTiling R T) (hp : Proper T) (hc : (T k).x₁ = (T i).x₀)
    (h : max (T k).y₀ (T i).y₀ < min (T k).y₁ (T i).y₁) :
    rightFace hT hp k = leftFace hT hp i := by
  have hR : (T k).x₁ ≠ R.x₁ := fun h' ↦ by linarith [(hp i).1, hT.tile_x₁_le i]
  have hL : (T i).x₀ ≠ R.x₀ := fun h' ↦ by linarith [(hp k).1, hT.le_tile_x₀ k]
  simp only [rightFace, leftFace, dite_eq_right hR, dite_eq_right hL, Face.link.injEq]
  obtain ⟨hc₁, hlo₁, hhi₁⟩ := (exists_link_right hT hp ((hT.tile_x₁_le k).lt_of_ne hR)).choose_spec
  obtain ⟨hc₂, hlo₂, hhi₂⟩ := (exists_link_left hT hp
    ((hT.le_tile_x₀ i).lt_of_ne fun h' ↦ hL h'.symm)).choose_spec
  exact Link.eq_of_overlap (hc₁.trans (hc.trans hc₂.symm)) h (hlo₁.trans (le_max_left _ _))
    ((min_le_left _ _).trans hhi₁) (hlo₂.trans (le_max_right _ _)) ((min_le_right _ _).trans hhi₂)

/-- The left edges of a tile and of the tile below it on one vertical line lie on one face when
the corner between them is not blocked: the V-link passes through it. -/
lemma leftFace_eq_leftFace (hT : IsTiling R T) (hp : Proper T) {m : ι}
    (hc : (T m).x₀ = (T i).x₀) (hy : (T m).y₁ = (T i).y₀) (hb : ¬ Blocked T (T i).x₀ (T i).y₀) :
    leftFace hT hp m = leftFace hT hp i := by
  by_cases hL : (T i).x₀ = R.x₀
  · rw [(leftFace_eq_left_iff hT hp).mpr (hc.trans hL), (leftFace_eq_left_iff hT hp).mpr hL]
  have hL' : (T m).x₀ ≠ R.x₀ := hc ▸ hL
  simp only [leftFace, dite_eq_right hL, dite_eq_right hL', Face.link.injEq]
  obtain ⟨hc₁, hlo₁, hhi₁⟩ := (exists_link_left hT hp
    ((hT.le_tile_x₀ m).lt_of_ne fun h' ↦ hL' h'.symm)).choose_spec
  set l := (exists_link_left hT hp ((hT.le_tile_x₀ i).lt_of_ne fun h' ↦ hL h'.symm)).choose
  obtain ⟨hc₂, hlo₂, hhi₂⟩ : l.c = (T i).x₀ ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi :=
    (exists_link_left hT hp ((hT.le_tile_x₀ i).lt_of_ne fun h' ↦ hL h'.symm)).choose_spec
  have hlo : l.lo < (T i).y₀ := by
    refine hlo₂.lt_of_ne fun heq ↦ ?_
    rcases l.bot with h' | h'
    · linarith [(hp m).2, hT.le_tile_y₀ m]
    · rw [hc₂, heq] at h'
      exact hb h'
  exact Link.eq_of_overlap (y := max l.lo (T m).y₀) (y' := (T i).y₀) (hc₁.trans (hc.trans hc₂.symm))
    (max_lt hlo (hy ▸ (hp m).2)) (hlo₁.trans (le_max_right _ _)) (hy ▸ hhi₁)
    (le_max_left _ _) ((hp i).2.le.trans hhi₂)

/-- The right edges of a tile and of the tile above it on one vertical line lie on one face when
the corner between them is not blocked. -/
lemma rightFace_eq_rightFace (hT : IsTiling R T) (hp : Proper T)
    (hc : (T j).x₁ = (T i).x₁) (hy : (T j).y₀ = (T i).y₁) (hb : ¬ Blocked T (T i).x₁ (T i).y₁) :
    rightFace hT hp j = rightFace hT hp i := by
  by_cases hR : (T i).x₁ = R.x₁
  · rw [(rightFace_eq_right_iff hT hp).mpr (hc.trans hR), (rightFace_eq_right_iff hT hp).mpr hR]
  have hR' : (T j).x₁ ≠ R.x₁ := hc ▸ hR
  simp only [rightFace, dite_eq_right hR, dite_eq_right hR', Face.link.injEq]
  obtain ⟨hc₁, hlo₁, hhi₁⟩ := (exists_link_right hT hp ((hT.tile_x₁_le j).lt_of_ne hR')).choose_spec
  set l := (exists_link_right hT hp ((hT.tile_x₁_le i).lt_of_ne hR)).choose
  obtain ⟨hc₂, hlo₂, hhi₂⟩ : l.c = (T i).x₁ ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi :=
    (exists_link_right hT hp ((hT.tile_x₁_le i).lt_of_ne hR)).choose_spec
  have hhi : (T i).y₁ < l.hi := by
    refine hhi₂.lt_of_ne fun heq ↦ ?_
    rcases l.top with h' | h'
    · linarith [(hp j).2, hT.tile_y₁_le j]
    · rw [hc₂, ← heq] at h'
      exact hb h'
  exact Link.eq_of_overlap (y := (T i).y₁) (y' := min l.hi (T j).y₁) (hc₁.trans (hc.trans hc₂.symm))
    (lt_min hhi (hy ▸ (hp j).2)) (hy ▸ hlo₁) ((min_le_right _ _).trans hhi₁)
    (hlo₂.trans (hp i).2.le) (min_le_left _ _)

variable (hT : IsTiling R T) (hp : Proper T) in
/-- **The face of a dart**: the face on the left of the tile's edge as it is drawn up from the
bottom end, and on its right as drawn down from the top end; that is, the V-link carrying the left
edge of the tile at its top end and the right edge at its bottom end, or the outer face on either
side of the exterior edge. -/
noncomputable def faceOf : Dart ι → Face R T
  | (some i, true) => leftFace hT hp i
  | (some i, false) => rightFace hT hp i
  | (none, false) => .left
  | (none, true) => .right

/-- **Following a dart to its other end and turning there stays on the same face**: the faces of the
rotation system are labelled by `faceOf`. -/
lemma faceOf_rot_flipEnd (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁)
    (hy : R.y₀ < R.y₁) (d : Dart ι) : faceOf hT hp (rot R T (flipEnd d)) = faceOf hT hp d := by
  rcases d with ⟨_ | i, _ | _⟩
  · obtain ⟨m, hm⟩ := exists_top_left hT hx hy
    change faceOf hT hp (rot R T (none, true)) = _
    rw [rot_none_true hT hp hm]
    exact (leftFace_eq_left_iff hT hp).mpr hm.1
  · obtain ⟨r, hr⟩ := exists_bot_right hT hx hy
    change faceOf hT hp (rot R T (none, false)) = _
    rw [rot_none_false hT hp hr]
    exact (rightFace_eq_right_iff hT hp).mpr hr.1
  · change faceOf hT hp (rot R T (some i, true)) = rightFace hT hp i
    by_cases h₁ : ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁
    · obtain ⟨k, hk⟩ := h₁
      rw [rot_top_of_right hT hp hk]
      refine (rightFace_eq_leftFace hT hp hk.1.symm ?_).symm
      rw [hk.2, min_self]
      exact max_lt (hp i).2 (hk.2 ▸ (hp k).2)
    by_cases h₂ : ∃ k, (T k).x₁ = (T i).x₁ ∧ (T k).y₀ = (T i).y₁
    · obtain ⟨k, hk⟩ := h₂
      rw [rot_top_of_above hT hp h₁ hk]
      exact rightFace_eq_rightFace hT hp hk.1 hk.2 fun hb ↦
        h₁ ((exists_right_below_iff hT hp).mpr hb)
    · rw [rot_top_of_not h₁ h₂]
      exact ((rightFace_eq_right_iff hT hp).mpr (corner_of_not_of_not hT hp hy h₁ h₂).1).symm
  · change faceOf hT hp (rot R T (some i, false)) = leftFace hT hp i
    by_cases h₁ : ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀
    · obtain ⟨k, hk⟩ := h₁
      rw [rot_bot_of_left hT hp hk]
      refine rightFace_eq_leftFace hT hp hk.1 ?_
      rw [hk.2, max_self]
      exact lt_min (hk.2 ▸ (hp k).2) (hp i).2
    by_cases h₂ : ∃ k, (T k).x₀ = (T i).x₀ ∧ (T k).y₁ = (T i).y₀
    · obtain ⟨m, hm⟩ := h₂
      rw [rot_bot_of_below hT hp h₁ hm]
      exact leftFace_eq_leftFace hT hp hm.1 hm.2 fun hb ↦ h₁ ((exists_left_above_iff hT hp).mpr hb)
    · rw [rot_bot_of_not h₁ h₂]
      exact ((leftFace_eq_left_iff hT hp).mpr (corner_of_not_of_not' hT hp hy h₁ h₂).1).symm

/-- Below the top of `R`, an unblocked top-left corner of a tile is the bottom-left corner of the
tile above it. -/
lemma exists_above_right (hT : IsTiling R T) (hp : Proper T)
    (hb : ¬ Blocked T (T i).x₀ (T i).y₁) (hy : (T i).y₁ < R.y₁) :
    ∃ g, (T g).x₀ = (T i).x₀ ∧ (T g).y₀ = (T i).y₁ := by
  obtain ⟨g, ⟨⟨hg₀, hg₁⟩, hg₂, hg₃⟩, -⟩ := hT.existsUnique_cell false false
    (x := (T i).x₀) (y := (T i).y₁)
    ⟨⟨hT.le_tile_x₀ i, (hp i).1.trans_le (hT.tile_x₁_le i)⟩,
      (hT.le_tile_y₀ i).trans (hp i).2.le, hy⟩
  refine ⟨g, le_antisymm hg₀ (not_lt.mp fun h ↦ hb (.inl ⟨g, h, hg₁, hg₂, hg₃.le⟩)),
    le_antisymm hg₂ (not_lt.mp fun h ↦ ?_)⟩
  have hgi := hT.eq_of_mem_cell (sx := false) (sy := true)
    (⟨⟨le_rfl, (hp i).1⟩, (hp i).2, le_rfl⟩ : _ ∈ (T i).cell false true)
    (⟨⟨hg₀, hg₁⟩, h, hg₃.le⟩ : _ ∈ (T g).cell false true)
  rw [← hgi] at hg₃
  exact lt_irrefl _ hg₃

/-! ### The faces are the V-links -/

section Faces

variable (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)

/-- The face permutation of the rotation system: to the other end of the edge, then round the
vertex there. -/
noncomputable abbrev facePerm : Equiv.Perm (Dart ι) := rotPerm hT hp hx hy * flipEnd

lemma sameCycle_face_step (d : Dart ι) :
    (facePerm hT hp hx hy).SameCycle d (rot R T (flipEnd d)) :=
  Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

include hT hp hx hy

/-- **The face permutation climbs the left side of a V-link**: from the bottom end of a tile
abutting the link on the left it reaches the bottom end of the topmost such tile. -/
lemma sameCycle_left_side (l : Link R T) {t : ι} (ht : IsLeft l t) (hth : (T t).y₁ = l.hi) :
    ∀ i, IsLeft l i → (facePerm hT hp hx hy).SameCycle (some i, false) (some t, false) := by
  classical
  suffices key : ∀ n i, (Finset.univ.filter fun j ↦ (T i).y₁ < (T j).y₁).card = n → IsLeft l i →
      (facePerm hT hp hx hy).SameCycle (some i, false) (some t, false) from
    fun i hi ↦ key _ i rfl hi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hn hi
    rcases hi.2.2.lt_or_eq with hlt | heq
    · have hb : ¬ Blocked T (T i).x₁ (T i).y₁ := by
        rw [hi.1]
        exact l.free _ (hi.2.1.trans_lt (hp i).2) hlt
      have h₁ : ¬ ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁ :=
        fun h ↦ hb ((exists_right_below_iff hT hp).mp h)
      obtain ⟨j, hj⟩ := exists_above_of_not hT hp h₁ (hlt.trans_le l.le_y₁)
      have hrot := rot_top_of_above hT hp h₁ hj
      have hjl : IsLeft l j := by
        rw [← rightFace_eq_link_iff hT hp, rightFace_eq_rightFace hT hp hj.1 hj.2 hb,
          rightFace_eq_link_iff hT hp]
        exact hi
      refine (sameCycle_face_step hT hp hx hy _).trans ?_
      change (facePerm hT hp hx hy).SameCycle (rot R T (some i, true)) _
      rw [hrot]
      refine ih _ ?_ j rfl hjl
      rw [← hn]
      refine Finset.card_lt_card ⟨fun k hk ↦ ?_, fun hsub ↦ ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        linarith [(hp j).2, hj.2]
      · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ j, by linarith [(hp j).2, hj.2]⟩)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact lt_irrefl _ this
    · rw [eq_of_x₁_y₁ hT hp (hi.1.trans ht.1.symm) (heq.trans hth.symm)]

/-- **The face permutation descends the right side of a V-link**: from the top end of the topmost
tile abutting the link on the right it reaches the top end of every tile abutting it there. -/
lemma sameCycle_right_side (l : Link R T) {u : ι} (hu : IsRight l u) (huh : (T u).y₁ = l.hi) :
    ∀ i, IsRight l i → (facePerm hT hp hx hy).SameCycle (some u, true) (some i, true) := by
  classical
  suffices key : ∀ n i, (Finset.univ.filter fun j ↦ (T i).y₁ < (T j).y₁).card = n → IsRight l i →
      (facePerm hT hp hx hy).SameCycle (some u, true) (some i, true) from
    fun i hi ↦ key _ i rfl hi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hn hi
    rcases hi.2.2.lt_or_eq with hlt | heq
    · have hb : ¬ Blocked T (T i).x₀ (T i).y₁ := by
        rw [hi.1]
        exact l.free _ (hi.2.1.trans_lt (hp i).2) hlt
      obtain ⟨g, hg⟩ := exists_above_right hT hp hb (hlt.trans_le l.le_y₁)
      have hb' : ¬ Blocked T (T g).x₀ (T g).y₀ := by rw [hg.1, hg.2]; exact hb
      have h₁ : ¬ ∃ k, (T k).x₁ = (T g).x₀ ∧ (T k).y₀ = (T g).y₀ :=
        fun h ↦ hb' ((exists_left_above_iff hT hp).mp h)
      have hrot := rot_bot_of_below hT hp h₁ (k := i) ⟨hg.1.symm, hg.2.symm⟩
      have hgl : IsRight l g := by
        rw [← leftFace_eq_link_iff hT hp, ← leftFace_eq_leftFace hT hp hg.1.symm hg.2.symm hb',
          leftFace_eq_link_iff hT hp]
        exact hi
      refine (ih _ ?_ g rfl hgl).trans ?_
      · rw [← hn]
        refine Finset.card_lt_card ⟨fun k hk ↦ ?_, fun hsub ↦ ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          linarith [(hp g).2, hg.2]
        · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ g, by linarith [(hp g).2, hg.2]⟩)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact lt_irrefl _ this
      · rw [← hrot]
        exact sameCycle_face_step hT hp hx hy (some g, true)
    · rw [eq_of_x₀_y₁ hT hp (hi.1.trans hu.1.symm) (heq.trans huh.symm)]

/-- **Over the top of a V-link the face permutation passes from its left side to its right
side.** -/
lemma sameCycle_top_of_link (l : Link R T) {t u : ι} (ht : IsLeft l t) (hth : (T t).y₁ = l.hi)
    (hu : IsRight l u) (huh : (T u).y₁ = l.hi) :
    (facePerm hT hp hx hy).SameCycle (some t, false) (some u, true) := by
  have h₁ : ∃ k, (T k).x₀ = (T t).x₁ ∧ (T k).y₁ = (T t).y₁ := by
    rcases l.top with htop | hb
    · by_contra h₁
      have h₂ : ¬ ∃ k, (T k).x₁ = (T t).x₁ ∧ (T k).y₀ = (T t).y₁ := fun ⟨k, _, hk⟩ ↦ by
        linarith [(hp k).2, hT.tile_y₁_le k]
      have := (corner_of_not_of_not hT hp hy h₁ h₂).1
      linarith [ht.1, l.lt_x₁]
    · refine (exists_right_below_iff hT hp).mpr ?_
      rw [ht.1, hth]
      exact hb
  obtain ⟨k, hk⟩ := h₁
  have hku : k = u := by
    have hkl : IsRight l k := by
      rw [← leftFace_eq_link_iff hT hp, ← rightFace_eq_leftFace hT hp hk.1.symm (by
        rw [hk.2, min_self]; exact max_lt (hp t).2 (hk.2 ▸ (hp k).2)), rightFace_eq_link_iff hT hp]
      exact ht
    exact eq_of_x₀_y₁ hT hp (hkl.1.trans hu.1.symm) (hk.2.trans (hth.trans huh.symm))
  rw [← hku, ← rot_top_of_right hT hp hk]
  exact sameCycle_face_step hT hp hx hy (some t, false)

/-- **The face permutation descends the left edge of `R`** to the exterior edge. -/
lemma sameCycle_left_outer : ∀ i, (T i).x₀ = R.x₀ →
    (facePerm hT hp hx hy).SameCycle (some i, true) (none, false) := by
  classical
  suffices key : ∀ n i, (Finset.univ.filter fun j ↦ (T j).y₀ < (T i).y₀).card = n →
      (T i).x₀ = R.x₀ → (facePerm hT hp hx hy).SameCycle (some i, true) (none, false) from
    fun i hi ↦ key _ i rfl hi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hn hi
    have h₁ : ¬ ∃ k, (T k).x₁ = (T i).x₀ ∧ (T k).y₀ = (T i).y₀ := fun ⟨k, hk, _⟩ ↦ by
      linarith [(hp k).1, hT.le_tile_x₀ k]
    refine (sameCycle_face_step hT hp hx hy _).trans ?_
    change (facePerm hT hp hx hy).SameCycle (rot R T (some i, false)) _
    rcases (hT.le_tile_y₀ i).lt_or_eq with hlt | heq
    · obtain ⟨m, hm⟩ := exists_below_of_not hT hp h₁ hlt
      rw [rot_bot_of_below hT hp h₁ hm]
      refine ih _ ?_ m rfl (hm.1.trans hi)
      rw [← hn]
      refine Finset.card_lt_card ⟨fun k hk ↦ ?_, fun hsub ↦ ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        linarith [(hp m).2, hm.2]
      · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ m, by linarith [(hp m).2, hm.2]⟩)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact lt_irrefl _ this
    · rw [rot_bot_of_not h₁ fun ⟨k, _, hk⟩ ↦ by linarith [(hp k).2, hT.le_tile_y₀ k]]

/-- **The face permutation climbs the right edge of `R`** to the exterior edge. -/
lemma sameCycle_right_outer : ∀ i, (T i).x₁ = R.x₁ →
    (facePerm hT hp hx hy).SameCycle (some i, false) (none, true) := by
  classical
  suffices key : ∀ n i, (Finset.univ.filter fun j ↦ (T i).y₁ < (T j).y₁).card = n →
      (T i).x₁ = R.x₁ → (facePerm hT hp hx hy).SameCycle (some i, false) (none, true) from
    fun i hi ↦ key _ i rfl hi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hn hi
    have h₁ : ¬ ∃ k, (T k).x₀ = (T i).x₁ ∧ (T k).y₁ = (T i).y₁ := fun ⟨k, hk, _⟩ ↦ by
      linarith [(hp k).1, hT.tile_x₁_le k]
    refine (sameCycle_face_step hT hp hx hy _).trans ?_
    change (facePerm hT hp hx hy).SameCycle (rot R T (some i, true)) _
    rcases (hT.tile_y₁_le i).lt_or_eq with hlt | heq
    · obtain ⟨j, hj⟩ := exists_above_of_not hT hp h₁ hlt
      rw [rot_top_of_above hT hp h₁ hj]
      refine ih _ ?_ j rfl (hj.1.trans hi)
      rw [← hn]
      refine Finset.card_lt_card ⟨fun k hk ↦ ?_, fun hsub ↦ ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        linarith [(hp j).2, hj.2]
      · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ j, by linarith [(hp j).2, hj.2]⟩)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact lt_irrefl _ this
    · rw [rot_top_of_not h₁ fun ⟨k, _, hk⟩ ↦ by linarith [(hp k).2, hT.tile_y₁_le k]]

omit hx hy in
/-- The topmost tile abutting a V-link on the left. -/
lemma exists_isLeft_top (l : Link R T) : ∃ t, IsLeft l t ∧ (T t).y₁ = l.hi := by
  obtain ⟨t, ht, -, h⟩ := exists_isLeft hT hp l l.lo_lt_hi le_rfl
  exact ⟨t, ht, le_antisymm ht.2.2 h⟩

omit hx hy in
/-- The topmost tile abutting a V-link on the right. -/
lemma exists_isRight_top (l : Link R T) : ∃ u, IsRight l u ∧ (T u).y₁ = l.hi := by
  obtain ⟨u, hu, -, h⟩ := exists_isRight hT hp l l.lo_lt_hi le_rfl
  exact ⟨u, hu, le_antisymm hu.2.2 h⟩

/-- **The darts of a face form one orbit of the face permutation**: the faces of the rotation
system are exactly the V-links and the two outer faces. -/
theorem sameCycle_of_faceOf_eq {d d' : Dart ι} (h : faceOf hT hp d = faceOf hT hp d') :
    (facePerm hT hp hx hy).SameCycle d d' := by
  classical
  -- A dart standing for each face.
  let canon : Face R T → Dart ι
    | .left => (none, false)
    | .right => (none, true)
    | .link l => (some (exists_isLeft_top hT hp l).choose, false)
  have key : ∀ d, (facePerm hT hp hx hy).SameCycle d (canon (faceOf hT hp d)) := by
    rintro ⟨_ | i, _ | _⟩
    · exact .refl _ _
    · exact .refl _ _
    · change (facePerm hT hp hx hy).SameCycle (some i, false) (canon (rightFace hT hp i))
      by_cases hR : (T i).x₁ = R.x₁
      · rw [(rightFace_eq_right_iff hT hp).mpr hR]
        exact sameCycle_right_outer hT hp hx hy i hR
      · obtain ⟨l, hl⟩ : ∃ l, rightFace hT hp i = .link l :=
          ⟨_, by simp only [rightFace, dite_eq_right hR]; rfl⟩
        rw [hl]
        obtain ⟨ht, hth⟩ := (exists_isLeft_top hT hp l).choose_spec
        exact sameCycle_left_side hT hp hx hy l ht hth i ((rightFace_eq_link_iff hT hp).mp hl)
    · change (facePerm hT hp hx hy).SameCycle (some i, true) (canon (leftFace hT hp i))
      by_cases hL : (T i).x₀ = R.x₀
      · rw [(leftFace_eq_left_iff hT hp).mpr hL]
        exact sameCycle_left_outer hT hp hx hy i hL
      · obtain ⟨l, hl⟩ : ∃ l, leftFace hT hp i = .link l :=
          ⟨_, by simp only [leftFace, dite_eq_right hL]; rfl⟩
        rw [hl]
        obtain ⟨ht, hth⟩ := (exists_isLeft_top hT hp l).choose_spec
        obtain ⟨u, hu, huh⟩ := exists_isRight_top hT hp l
        exact ((sameCycle_right_side hT hp hx hy l hu huh i
          ((leftFace_eq_link_iff hT hp).mp hl)).symm.trans
          (sameCycle_top_of_link hT hp hx hy l ht hth hu huh).symm)
  exact (key d).trans (h ▸ (key d').symm)

end Faces

/-! ### Seymour's graph as a combinatorial map -/

omit [Fintype ι] in
/-- A function invariant under a permutation is constant on its cycles. -/
lemma eq_of_sameCycle {α β : Type*} {f : Equiv.Perm α} {g : α → β}
    (hg : ∀ a, g (f a) = g a) {a b : α} (h : f.SameCycle a b) : g a = g b := by
  obtain ⟨k, rfl⟩ := h
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply, hg, ih]
  | pred k ih =>
    rw [ih, ← hg ((f ^ (-(k : ℤ) - 1)) a), ← Equiv.Perm.mul_apply, ← zpow_one_add,
      add_sub_cancel]

section Map

variable (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)

lemma vert_surjective : Function.Surjective (vert hT hx hy) := by
  intro s
  obtain ⟨p, hp, rfl⟩ := Seg.exists_mk s
  obtain ⟨i, hi | hi⟩ := hp
  · exact ⟨(some i, false), Seg.mk_eq_mk.mpr (segStep_of_memBot ⟨rfl, le_rfl, (T i).hx⟩ hi)⟩
  · exact ⟨(some i, true), Seg.mk_eq_mk.mpr (segStep_of_memTop ⟨rfl, le_rfl, (T i).hx⟩ hi)⟩

include hT hp in
lemma faceOf_surjective : Function.Surjective (faceOf hT hp) := by
  rintro (_ | _ | l)
  · exact ⟨(none, false), rfl⟩
  · exact ⟨(none, true), rfl⟩
  · obtain ⟨t, ht, -⟩ := exists_isLeft_top hT hp l
    exact ⟨(some t, false), (rightFace_eq_link_iff hT hp).mpr ht⟩

/-- **Seymour's graph, embedded in the plane**: the combinatorial map whose vertices are the
horizontal segments of the tiling, whose edges are the tiles and the exterior edge, each tile
joining the segments of its bottom and top edges, and whose rotation `rot` is read off the tiling.
Its faces are the V-links and the two outer faces on either side of the exterior edge. -/
noncomputable def seymourMap : CombinatorialMap (Seg T) (Option ι) (Face R T) (Dart ι) where
  vertexPerm := rotPerm hT hp hx hy
  edgePerm := flipEnd
  vert := vert hT hx hy
  edge := Prod.fst
  face := faceOf hT hp
  edgePerm_edgePerm d := by simp
  edgePerm_ne d := by simp [Prod.ext_iff]
  vert_eq_vert_iff d d' := ⟨sameCycle_of_vert_eq hT hp hx hy,
    eq_of_sameCycle (vert_rot hT hp hx hy)⟩
  edge_eq_edge_iff := by
    rintro ⟨e, b⟩ ⟨e', b'⟩
    cases b <;> cases b' <;> simp [eq_comm]
  face_eq_face_iff d d' := ⟨sameCycle_of_faceOf_eq hT hp hx hy,
    eq_of_sameCycle (faceOf_rot_flipEnd hT hp hx hy)⟩
  vert_surjective := vert_surjective hT hx hy
  edge_surjective e := ⟨(e, false), rfl⟩
  face_surjective := faceOf_surjective hT hp

end Map

/-! ### Seymour's graph is connected -/

/-- Above the bottom of `R`, the bottom-left corner of a tile lies on the top edge of a tile. -/
lemma exists_below (hT : IsTiling R T) (hp : Proper T) (h : R.y₀ < (T i).y₀) :
    ∃ m, (T m).y₁ = (T i).y₀ ∧ (T m).x₀ ≤ (T i).x₀ ∧ (T i).x₀ < (T m).x₁ := by
  obtain ⟨m, ⟨⟨hm₀, hm₁⟩, hm₂, hm₃⟩, -⟩ := hT.existsUnique_cell false true
    (x := (T i).x₀) (y := (T i).y₀)
    ⟨⟨hT.le_tile_x₀ i, (hp i).1.trans_le (hT.tile_x₁_le i)⟩, h,
      (hp i).2.le.trans (hT.tile_y₁_le i)⟩
  refine ⟨m, le_antisymm (not_lt.mp fun h' ↦ ?_) hm₃, hm₀, hm₁⟩
  have him := hT.eq_of_mem_cell (sx := false) (sy := false)
    (⟨⟨le_rfl, (hp i).1⟩, le_rfl, (hp i).2⟩ : _ ∈ (T i).cell false false)
    (⟨⟨hm₀, hm₁⟩, hm₂.le, h'⟩ : _ ∈ (T m).cell false false)
  rw [← him] at hm₂
  exact lt_irrefl _ hm₂

section Connected

variable (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
include hT hp hx hy

/-- **Seymour's graph is connected**: every segment is joined to the bottom of `R`, going down
through the tiles below it. -/
theorem seymourMap_connected : (seymourMap hT hp hx hy).graph.Connected := by
  classical
  set M := seymourMap hT hp hx hy
  set b := vert hT hx hy (none, false)
  have hsymm : ∀ {x y}, Relation.ReflTransGen M.graph.Adj x y →
      Relation.ReflTransGen M.graph.Adj y x := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact .head hab.symm ih
  have hlink : ∀ d, Relation.ReflTransGen M.graph.Adj (vert hT hx hy d)
      (vert hT hx hy (flipEnd d)) := fun d ↦ .single ⟨d.1, M.graph_isLink_dart d⟩
  have hbot : ∀ i, Relation.ReflTransGen M.graph.Adj b (vert hT hx hy (some i, false)) := by
    suffices key : ∀ n i, (Finset.univ.filter fun j ↦ (T j).y₀ < (T i).y₀).card = n →
        Relation.ReflTransGen M.graph.Adj b (vert hT hx hy (some i, false)) from
      fun i ↦ key _ i rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hn
      rcases (hT.le_tile_y₀ i).lt_or_eq with hlt | heq
      · obtain ⟨m, hm₁, hm₀, hm₀'⟩ := exists_below hT hp hlt
        have hvm : vert hT hx hy (some m, true) = vert hT hx hy (some i, false) := by
          refine (vert_eq_vert_iff hT hx hy).mpr ?_
          change SegStep T ((T m).x₀, (T m).y₁) ((T i).x₀, (T i).y₀)
          rw [← hm₁]
          exact segStep_of_memTop ⟨rfl, le_rfl, (T m).hx⟩ ⟨rfl, hm₀, hm₀'.le⟩
        rw [← hvm]
        refine (ih _ ?_ m rfl).trans (hlink (some m, false))
        rw [← hn]
        refine Finset.card_lt_card ⟨fun k hk ↦ ?_, fun hsub ↦ ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          linarith [(hp m).2]
        · have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ m, by linarith [(hp m).2]⟩)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact lt_irrefl _ this
      · have : vert hT hx hy (some i, false) = b := by
          refine (vert_eq_vert_iff hT hx hy).mpr ?_
          change SegStep T ((T i).x₀, (T i).y₀) (R.x₀, R.y₀)
          rw [← heq]
          exact segStep_bot hT hx hy ⟨hT.le_tile_x₀ i, (hp i).1.le.trans (hT.tile_x₁_le i)⟩
            ⟨le_rfl, hx.le⟩
        rw [this]
  have hall : ∀ d, Relation.ReflTransGen M.graph.Adj b (vert hT hx hy d) := by
    rintro ⟨_ | i, _ | _⟩
    · exact .refl
    · exact hlink (none, false)
    · exact hbot i
    · exact (hbot i).trans (hlink (some i, false))
  refine ⟨⟨b, trivial⟩, fun x _ y _ ↦ ?_⟩
  obtain ⟨d, rfl⟩ := vert_surjective hT hx hy x
  obtain ⟨d', rfl⟩ := vert_surjective hT hx hy y
  exact (hsymm (hall d)).trans (hall d')

end Connected

/-! ### Seymour's graph is planar -/

omit [Fintype ι] in
/-- A segment move restricts to any point between its ends. -/
lemma SegStep.left_of_le {a b c y : ℝ} (h : SegStep T ((a, y) : ℝ × ℝ) (b, y)) (hac : a ≤ c)
    (hcb : c ≤ b) : SegStep T ((a, y) : ℝ × ℝ) (c, y) :=
  ⟨rfl, fun z hz ↦ h.2 z (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc.mpr (.inl ⟨hac, hcb⟩)) hz)⟩

omit [Fintype ι] in
/-- A segment move restricts to any point between its ends. -/
lemma SegStep.right_of_le {a b c y : ℝ} (h : SegStep T ((a, y) : ℝ × ℝ) (b, y)) (hac : a ≤ c)
    (hcb : c ≤ b) : SegStep T ((c, y) : ℝ × ℝ) (b, y) :=
  ⟨rfl, fun z hz ↦ h.2 z (uIcc_subset_uIcc (mem_uIcc.mpr (.inl ⟨hac, hcb⟩)) right_mem_uIcc hz)⟩

omit [Fintype ι] in
/-- **A point strictly inside a segment is blocked**: horizontal edges reach it from both sides. -/
lemma blocked_of_segStep [Finite ι] {x x' c y : ℝ} (h : SegStep T ((x, y) : ℝ × ℝ) (x', y))
    (hxc : x < c) (hcx : c ≤ x')
    (hright : ∃ t, (T t).x₀ ≤ x' ∧ x' < (T t).x₁ ∧ ((T t).y₀ = y ∨ (T t).y₁ = y)) :
    Blocked T c y := by
  refine .inr ⟨exists_edge_left (h.left_of_le hxc.le hcx) hxc, ?_⟩
  rcases hcx.lt_or_eq with hlt | rfl
  · exact exists_edge_right (h.right_of_le hxc.le hlt.le) hlt
  · exact hright

/-- The left point of every dart is the left end of a horizontal edge. -/
lemma exists_edge_right_dartPt (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
    (hp : Proper T) (d : Dart ι) :
    ∃ t, (T t).x₀ ≤ (dartPt R T d).1 ∧ (dartPt R T d).1 < (T t).x₁ ∧
      ((T t).y₀ = (dartPt R T d).2 ∨ (T t).y₁ = (dartPt R T d).2) := by
  rcases d with ⟨_ | i, _ | _⟩
  · obtain ⟨k, hk₀, hk₁⟩ := exists_bot_left hT hx hy
    refine ⟨k, hk₀.le, ?_, .inl hk₁⟩
    change R.x₀ < (T k).x₁
    rw [← hk₀]
    exact (hp k).1
  · obtain ⟨k, hk₀, hk₁⟩ := exists_top_left hT hx hy
    refine ⟨k, hk₀.le, ?_, .inr hk₁⟩
    change R.x₀ < (T k).x₁
    rw [← hk₀]
    exact (hp k).1
  · exact ⟨i, le_rfl, (hp i).1, .inl rfl⟩
  · exact ⟨i, le_rfl, (hp i).1, .inr rfl⟩

lemma le_dartPt (hT : IsTiling R T) (d : Dart ι) : R.x₀ ≤ (dartPt R T d).1 := by
  rcases d with ⟨_ | i, _ | _⟩ <;> first | exact le_rfl | exact hT.le_tile_x₀ i

open scoped Classical in
variable (T) in
/-- **The column parity**: the number of tiles of `C` stacked under the point `(x, y)` in the
column just right of `x`, mod 2. -/
noncomputable def colSum (C : Set (Option ι)) (x y : ℝ) : ZMod 2 :=
  ∑ i, if some i ∈ C ∧ (T i).y₁ ≤ y then (if (T i).x₀ ≤ x ∧ x < (T i).x₁ then 1 else 0) else 0

omit [Fintype ι] in
private lemma ind_Ico {a b t : ℝ} (hab : a < b) :
    (if a ≤ t ∧ t < b then (1 : ZMod 2) else 0) =
      (if a ≤ t then 1 else 0) + if b ≤ t then 1 else 0 := by
  rcases lt_or_ge t a with h₁ | h₁
  · rw [ite_eq_right fun h ↦ (not_le.mpr h₁) h.1, ite_eq_right (not_le.mpr h₁),
      ite_eq_right (not_le.mpr (h₁.trans hab)), add_zero]
  · rcases lt_or_ge t b with h₂ | h₂
    · rw [ite_eq_left ⟨h₁, h₂⟩, ite_eq_left h₁, ite_eq_right (not_le.mpr h₂), add_zero]
    · rw [ite_eq_right fun h ↦ (not_lt.mpr h₂) h.2, ite_eq_left h₁, ite_eq_left h₂]
      decide

omit [Fintype ι] in
private lemma ind_le_add {a x x' : ℝ} (hxx' : x ≤ x') :
    (if a ≤ x' then (1 : ZMod 2) else 0) + (if a ≤ x then 1 else 0) =
      if x < a ∧ a ≤ x' then 1 else 0 := by
  rcases le_or_gt a x with h₁ | h₁
  · rw [ite_eq_left (h₁.trans hxx'), ite_eq_left h₁, ite_eq_right fun h ↦ (not_lt.mpr h₁) h.1]
    decide
  · rcases le_or_gt a x' with h₂ | h₂
    · rw [ite_eq_left h₂, ite_eq_right (not_le.mpr h₁), ite_eq_left ⟨h₁, h₂⟩, add_zero]
    · rw [ite_eq_right (not_le.mpr h₂), ite_eq_right (not_le.mpr h₁),
        ite_eq_right fun h ↦ (not_le.mpr h₂) h.2, add_zero]

section Planar

variable (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
include hT hp

/-- The faces met by a column moving from `x` to `x'` at the height of a segment: the V-links
between, entirely below the segment. -/
def MovedFace (x x' y : ℝ) (F : Face R T) : Prop :=
  ∃ l, F = .link l ∧ x < l.c ∧ l.c ≤ x' ∧ l.hi ≤ y

/-- Moving a column across the left edge of a tile below a segment crosses the face of that edge,
a V-link that the segment bounds from above. -/
lemma movedFace_leftFace_iff {x x' y : ℝ} (h : SegStep T ((x, y) : ℝ × ℝ) (x', y))
    (hxR : R.x₀ ≤ x)
    (hright : ∃ t, (T t).x₀ ≤ x' ∧ x' < (T t).x₁ ∧ ((T t).y₀ = y ∨ (T t).y₁ = y)) :
    MovedFace x x' y (leftFace hT hp i) ↔ (x < (T i).x₀ ∧ (T i).x₀ ≤ x') ∧ (T i).y₁ ≤ y := by
  constructor
  · rintro ⟨l, hl, hxl, hlx, hly⟩
    have hil := (leftFace_eq_link_iff hT hp).mp hl
    rw [← hil.1] at hxl hlx
    exact ⟨⟨hxl, hlx⟩, hil.2.2.trans hly⟩
  · rintro ⟨⟨hxi, hix⟩, hiy⟩
    have hL : (T i).x₀ ≠ R.x₀ := fun h' ↦ by linarith
    obtain ⟨l, hl⟩ : ∃ l, leftFace hT hp i = .link l :=
      ⟨_, by simp only [leftFace, dite_eq_right hL]; rfl⟩
    have hil := (leftFace_eq_link_iff hT hp).mp hl
    refine ⟨l, hl, hil.1 ▸ hxi, hil.1 ▸ hix, not_lt.mp fun hlt ↦ ?_⟩
    have hb := blocked_of_segStep h hxi hix hright
    rw [hil.1] at hb
    exact l.free y (hil.2.1.trans_lt ((hp i).2.trans_le hiy)) hlt hb

/-- Moving a column across the right edge of a tile below a segment crosses the face of that
edge. -/
lemma movedFace_rightFace_iff {x x' y : ℝ} (h : SegStep T ((x, y) : ℝ × ℝ) (x', y))
    (hright : ∃ t, (T t).x₀ ≤ x' ∧ x' < (T t).x₁ ∧ ((T t).y₀ = y ∨ (T t).y₁ = y)) :
    MovedFace x x' y (rightFace hT hp i) ↔ (x < (T i).x₁ ∧ (T i).x₁ ≤ x') ∧ (T i).y₁ ≤ y := by
  constructor
  · rintro ⟨l, hl, hxl, hlx, hly⟩
    have hil := (rightFace_eq_link_iff hT hp).mp hl
    rw [← hil.1] at hxl hlx
    exact ⟨⟨hxl, hlx⟩, hil.2.2.trans hly⟩
  · rintro ⟨⟨hxi, hix⟩, hiy⟩
    obtain ⟨t, ht₀, ht, ht₂⟩ := hright
    have hR : (T i).x₁ ≠ R.x₁ := fun h' ↦ by linarith [hT.tile_x₁_le t]
    obtain ⟨l, hl⟩ : ∃ l, rightFace hT hp i = .link l :=
      ⟨_, by simp only [rightFace, dite_eq_right hR]; rfl⟩
    have hil := (rightFace_eq_link_iff hT hp).mp hl
    refine ⟨l, hl, hil.1 ▸ hxi, hil.1 ▸ hix, not_lt.mp fun hlt ↦ ?_⟩
    have hb := blocked_of_segStep h hxi hix ⟨t, ht₀, ht, ht₂⟩
    rw [hil.1] at hb
    exact l.free y (hil.2.1.trans_lt ((hp i).2.trans_le hiy)) hlt hb

include hx hy

/-- **A column moved along a segment keeps its parity**, for an edge set meeting every face of
Seymour's graph evenly: the tiles it gains and loses abut the V-links it crosses below the
segment, and the tiles abutting a V-link are counted an even number of times. -/
lemma colSum_eq {C : Set (Option ι)}
    (hC : (seymourMap hT hp hx hy).IsEven (seymourMap hT hp hx hy).face C) {x x' y : ℝ}
    (h : SegStep T ((x, y) : ℝ × ℝ) (x', y)) (hxR : R.x₀ ≤ x) (hxx' : x < x')
    (hright : ∃ t, (T t).x₀ ≤ x' ∧ x' < (T t).x₁ ∧ ((T t).y₀ = y ∨ (T t).y₁ = y)) :
    colSum T C x y = colSum T C x' y := by
  classical
  rw [CombinatorialMap.isEven_iff] at hC
  -- The parity change is the number of darts on V-links crossed below the segment...
  have hchange : colSum T C x' y + colSum T C x y = ∑ d : Dart ι,
      if d.1 ∈ C ∧ MovedFace x x' y (faceOf hT hp d) then 1 else 0 := by
    rw [colSum, colSum, ← Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_option]
    simp only [Fintype.sum_bool]
    rw [show (MovedFace x x' y (faceOf hT hp (none, true)) ↔ False) from
        ⟨fun ⟨_, h, _⟩ ↦ (by change Face.right = _ at h; cases h), False.elim⟩,
      show (MovedFace x x' y (faceOf hT hp (none, false)) ↔ False) from
        ⟨fun ⟨_, h, _⟩ ↦ (by change Face.left = _ at h; cases h), False.elim⟩]
    simp only [and_false, ite_false, add_zero, zero_add]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change _ = (if some i ∈ C ∧ MovedFace x x' y (leftFace hT hp i) then 1 else 0) +
      if some i ∈ C ∧ MovedFace x x' y (rightFace hT hp i) then 1 else 0
    rw [movedFace_leftFace_iff hT hp h hxR hright, movedFace_rightFace_iff hT hp h hright]
    by_cases hA : some i ∈ C ∧ (T i).y₁ ≤ y
    · rw [ite_eq_left hA, ite_eq_left hA, ind_Ico (hp i).1, ind_Ico (hp i).1,
        add_add_add_comm, ind_le_add hxx'.le, ind_le_add hxx'.le]
      simp only [hA.1, hA.2, true_and, and_true]
    · rw [ite_eq_right hA, ite_eq_right hA, add_zero]
      rw [ite_eq_right fun h' ↦ hA ⟨h'.1, h'.2.2⟩, ite_eq_right fun h' ↦ hA ⟨h'.1, h'.2.2⟩,
        add_zero]
  -- ...and each V-link crossed is met an even number of times.
  have hzero : ∑ d : Dart ι, (if d.1 ∈ C ∧ MovedFace x x' y (faceOf hT hp d) then
      (1 : ZMod 2) else 0) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := faceOf hT hp)
      (t := Finset.univ.image (faceOf hT hp)) fun d _ ↦
        Finset.mem_image_of_mem _ (Finset.mem_univ d)]
    refine Finset.sum_eq_zero fun F _ ↦ ?_
    by_cases hF : MovedFace x x' y F
    · refine (Finset.sum_congr rfl fun d hd ↦ ?_).trans (hC F)
      have hdF : faceOf hT hp d = F := (Finset.mem_filter.mp hd).2
      rw [hdF]
      simp only [hF, and_true, Set.indicator_apply, Pi.one_apply]
      rfl
    · exact Finset.sum_eq_zero fun d hd ↦
        ite_eq_right fun h' ↦ hF ((Finset.mem_filter.mp hd).2 ▸ h'.2)
  rw [hzero] at hchange
  exact ((by decide : ∀ a b : ZMod 2, a + b = 0 → b = a) _ _ hchange)

/-- **Seymour's graph satisfies the Jordan curve property**: an edge set meeting every face evenly
is an edge cut. The segments are coloured by the parity of the tiles of the set stacked under
them; crossing a tile changes the colour exactly when the tile is in the set, and crossing the
exterior edge exactly when it is, by the parity at the left outer face. -/
theorem seymourMap_isEdgeCut_of_isEven {C : Set (Option ι)}
    (hC : (seymourMap hT hp hx hy).IsEven (seymourMap hT hp hx hy).face C) :
    (seymourMap hT hp hx hy).graph.IsEdgeCut C := by
  classical
  set M := seymourMap hT hp hx hy
  set χD : Dart ι → ZMod 2 := fun d ↦ colSum T C (dartPt R T d).1 (dartPt R T d).2 with hχD
  -- The colour is well defined on segments.
  have hwd : ∀ d d', vert hT hx hy d = vert hT hx hy d' → χD d = χD d' := by
    have key : ∀ d d', vert hT hx hy d = vert hT hx hy d' →
        (dartPt R T d).1 < (dartPt R T d').1 → χD d = χD d' := by
      intro d d' h hlt
      have hs := (vert_eq_vert_iff hT hx hy).mp h
      obtain ⟨t, ht₀, ht₁, ht₂⟩ := exists_edge_right_dartPt hT hx hy hp d'
      simp only [hχD]
      rw [← hs.1] at ht₂ ⊢
      exact colSum_eq hT hp hx hy hC ⟨rfl, hs.2⟩ (le_dartPt hT d) hlt ⟨t, ht₀, ht₁, ht₂⟩
    intro d d' h
    rcases lt_trichotomy (dartPt R T d).1 (dartPt R T d').1 with hlt | heq | hgt
    · exact key d d' h hlt
    · simp only [hχD]
      rw [heq, ((vert_eq_vert_iff hT hx hy).mp h).1]
    · exact (key d' d h.symm hgt).symm
  set χ : Seg T → ZMod 2 := fun s ↦ χD (Function.surjInv (vert_surjective hT hx hy) s)
  have hχ : ∀ d, χ (vert hT hx hy d) = χD d := fun d ↦
    hwd _ _ (Function.surjInv_eq (vert_surjective hT hx hy) _)
  -- Crossing an edge changes the colour exactly when the edge is in `C`.
  have hcross : ∀ e, χD (e, false) + χD (e, true) = if e ∈ C then 1 else 0 := by
    rintro (_ | i)
    · -- the exterior edge: the column at the left edge of `R`, read against the left outer face
      have hbot : χD (none, false) = 0 := by
        simp only [hχD, dartPt, colSum]
        exact Finset.sum_eq_zero fun j _ ↦
          ite_eq_right fun h' ↦ by linarith [h'.2, (hp j).2, hT.le_tile_y₀ j]
      have hleft := (CombinatorialMap.isEven_iff _ _ _).mp hC Face.left
      rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_option] at hleft
      simp only [Fintype.sum_bool] at hleft
      change (if Face.right = Face.left then _ else 0) + (if Face.left = Face.left then _ else 0) +
        ∑ j, ((if leftFace hT hp j = Face.left then _ else 0) +
          if rightFace hT hp j = Face.left then _ else 0) = 0 at hleft
      simp only [reduceCtorEq, ite_false, ite_true, zero_add, rightFace_ne_left hT hp, add_zero,
        leftFace_eq_left_iff hT hp] at hleft
      rw [hbot, zero_add]
      change ∑ j, (if some j ∈ C ∧ (T j).y₁ ≤ R.y₁ then
        (if (T j).x₀ ≤ R.x₀ ∧ R.x₀ < (T j).x₁ then (1 : ZMod 2) else 0) else 0) = _
      have hterm : ∀ j, (if some j ∈ C ∧ (T j).y₁ ≤ R.y₁ then
          (if (T j).x₀ ≤ R.x₀ ∧ R.x₀ < (T j).x₁ then (1 : ZMod 2) else 0) else 0) =
          if (T j).x₀ = R.x₀ then C.indicator 1 (some j) else 0 := by
        intro j
        by_cases hj : (T j).x₀ = R.x₀
        · rw [ite_eq_left hj, Set.indicator_apply]
          by_cases hjC : some j ∈ C
          · rw [ite_eq_left ⟨hjC, hT.tile_y₁_le j⟩, ite_eq_left ⟨hj.le, hj ▸ (hp j).1⟩,
              ite_eq_left hjC,
              Pi.one_apply]
          · rw [ite_eq_right fun h' ↦ hjC h'.1, ite_eq_right hjC]
        · rw [ite_eq_right hj]
          by_cases hA : some j ∈ C ∧ (T j).y₁ ≤ R.y₁
          · rw [ite_eq_left hA, ite_eq_right fun h' ↦ hj (le_antisymm h'.1 (hT.le_tile_x₀ j))]
          · rw [ite_eq_right hA]
      simp_rw [hterm]
      rw [Set.indicator_apply] at hleft
      exact (by decide : ∀ a b : ZMod 2, a + b = 0 → b = a) _ _ hleft
    · -- a tile: the column at its left edge gains exactly the tile itself
      change colSum T C (T i).x₀ (T i).y₀ + colSum T C (T i).x₀ (T i).y₁ = _
      rw [colSum, colSum, ← Finset.sum_add_distrib, Fintype.sum_eq_single i]
      · by_cases hiC : some i ∈ C
        · rw [ite_eq_right fun h' ↦ by linarith [h'.2, (hp i).2], zero_add,
            ite_eq_left ⟨hiC, le_rfl⟩, ite_eq_left ⟨le_rfl, (hp i).1⟩, ite_eq_left hiC]
        · rw [ite_eq_right fun h' ↦ hiC h'.1, ite_eq_right fun h' ↦ hiC h'.1, ite_eq_right hiC,
            add_zero]
      · intro j hji
        by_cases hjx : (T j).x₀ ≤ (T i).x₀ ∧ (T i).x₀ < (T j).x₁
        · by_cases hA : some j ∈ C ∧ (T j).y₁ ≤ (T i).y₁
          · by_cases hB : (T j).y₁ ≤ (T i).y₀
            · rw [ite_eq_left ⟨hA.1, hB⟩, ite_eq_left hA, ite_eq_left hjx]
              decide
            · exfalso
              refine hji (hT.eq_of_mem_cell (sx := false) (sy := true) (x := (T i).x₀)
                (y := (T j).y₁) ⟨hjx, (hp j).2, le_rfl⟩ ⟨⟨le_rfl, (hp i).1⟩, ?_, hA.2⟩)
              exact not_le.mp hB
          · rw [ite_eq_right fun h' ↦ hA ⟨h'.1, h'.2.trans (hp i).2.le⟩, ite_eq_right hA, add_zero]
        · simp only [hjx, ite_false, ite_self, add_zero]
  -- The colouring cuts out `C`.
  have hcut : M.graph.edgeCut {s | χ s = 1} = C := by
    ext e
    have hl : M.graph.IsLink e (vert hT hx hy (e, false)) (vert hT hx hy (e, true)) :=
      M.graph_isLink_dart (e, false)
    rw [hl.mem_edgeCut_iff]
    change ((χ (vert hT hx hy (e, false)) = 1 ∧ ¬ χ (vert hT hx hy (e, true)) = 1) ∨
      (χ (vert hT hx hy (e, true)) = 1 ∧ ¬ χ (vert hT hx hy (e, false)) = 1)) ↔ e ∈ C
    rw [hχ, hχ]
    have := hcross e
    by_cases he : e ∈ C
    · rw [ite_eq_left he] at this
      refine iff_of_true ?_ he
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (χD (e, false)) with h0 | h1
      · rw [h0, zero_add] at this
        exact .inr ⟨this, by rw [h0]; decide⟩
      · rw [h1] at this
        exact .inl ⟨h1, fun h' ↦ by rw [h'] at this; exact absurd this (by decide)⟩
    · rw [ite_eq_right he] at this
      refine iff_of_false ?_ he
      have heq := (by decide : ∀ a b : ZMod 2, a + b = 0 → b = a) _ _ this
      rw [heq]
      tauto
  rw [← hcut]
  exact M.graph.isEdgeCut_edgeCut _

/-- **Seymour's graph, embedded by the tiling, is planar**: its Euler characteristic is `2`. -/
theorem seymourMap_isPlanar : (seymourMap hT hp hx hy).IsPlanar :=
  CombinatorialMap.isPlanar_of_forall_isEdgeCut (seymourMap_connected hT hp hx hy)
    fun _ hC ↦ seymourMap_isEdgeCut_of_isEven hT hp hx hy hC

end Planar

/-! ### Seymour's dichotomy -/

section Endgame

variable (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
include hT hp hx hy

/-- **First alternative: a path of V-tiles.** A vertex reached from the bottom of `R` in Seymour's
graph with the edges of `S` deleted, `S` containing the exterior edge and every tile of
non-integer height, sits an integer distance above the bottom of `R`: each step crosses a tile of
integer height. -/
lemma int_sub_y₀_of_reflTransGen {S : Set (Option ι)}
    (hS : ∀ i, some i ∉ S → ∃ m : ℤ, (T i).height = m) (hnone : none ∈ S) {s : Seg T}
    (h : Relation.ReflTransGen ((seymourMap hT hp hx hy).graph.deleteEdges S).Adj
      (vert hT hx hy (none, false)) s) :
    ∃ m : ℤ, s.y - R.y₀ = m := by
  induction h with
  | refl => exact ⟨0, by simp [vert, dartPt]⟩
  | tail _ hxy ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨e, ⟨d, rfl, rfl, rfl⟩, he⟩ := hxy
    rcases d with ⟨_ | i, _ | _⟩
    · exact absurd hnone he
    · exact absurd hnone he
    · obtain ⟨n, hn⟩ := hS i he
      rw [Rectangle.height] at hn
      refine ⟨m + n, ?_⟩
      change (T i).y₀ - R.y₀ = m at hm
      change (T i).y₁ - R.y₀ = _
      push_cast
      linarith
    · obtain ⟨n, hn⟩ := hS i he
      rw [Rectangle.height] at hn
      refine ⟨m - n, ?_⟩
      change (T i).y₁ - R.y₀ = m at hm
      change (T i).y₀ - R.y₀ = _
      push_cast
      linarith

/-- **Second alternative: a dual path of H-tiles.** When the bottom of `R` is cut off from its top
in Seymour's graph with the edges of `S` deleted, `S` containing the exterior edge and the tiles
of non-integer height only, a minimal `S' ⊆ S` cutting them off is a bond, which by planar duality
is a cycle of the dual graph. The cycle passes through the exterior edge, since that edge alone
joins the bottom to the top, and the rest of it is a path from the left outer face to the right
one across H-tiles, each step moving the abscissa by the integer width of the tile crossed. -/
lemma intWidth_of_not_reflTransGen (hsides : ∀ i, (T i).HasIntegerSide) {S : Set (Option ι)}
    (hS : ∀ i, some i ∈ S → ¬ ∃ m : ℤ, (T i).height = m)
    (h : ¬ Relation.ReflTransGen ((seymourMap hT hp hx hy).graph.deleteEdges S).Adj
      (vert hT hx hy (none, false)) (vert hT hx hy (none, true))) :
    ∃ m : ℤ, R.width = m := by
  classical
  set M := seymourMap hT hp hx hy
  -- A minimal `S' ⊆ S` cutting the bottom off from the top: a bond.
  obtain ⟨S', hS'S, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun F ↦ ¬ Relation.ReflTransGen (M.graph.deleteEdges F).Adj (vert hT hx hy (none, false))
      (vert hT hx hy (none, true))) S h
  have hbond : M.graph.IsBond S' :=
    Graph.isBond_of_minimal (.single ⟨none, M.graph_isLink_dart (none, false)⟩) hmin
  -- By planar duality it is a cycle of the dual graph...
  obtain ⟨n, v, e, -, he, hl, hrange⟩ := (seymourMap_isPlanar hT hp hx hy).isCycle_of_isBond hbond
  -- ...through the exterior edge.
  have hnone : none ∈ S' := by
    by_contra hnS
    exact hmin.prop (.single ⟨none, M.graph_isLink_dart (none, false), hnS⟩)
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, e k₀ = none := by
    rw [← hrange] at hnone
    exact hnone
  -- Each other step of the cycle crosses an H-tile, moving the abscissa by an integer.
  have hstep : ∀ k, k ≠ k₀ → ∃ m : ℤ, (v (k + 1)).c - (v k).c = m := by
    intro k hk
    obtain ⟨d, hd, hdv, hdv'⟩ := hl k
    have hek : e k ∈ S' := hrange ▸ ⟨k, rfl⟩
    rcases d with ⟨_ | i, _ | _⟩
    · exact absurd (he (hd.symm.trans hk₀.symm)) hk
    · exact absurd (he (hd.symm.trans hk₀.symm)) hk
    · rw [← show some i = e k from hd] at hek
      obtain ⟨w, hw⟩ := (hsides i).resolve_right (hS i (hS'S hek))
      rw [Rectangle.width] at hw
      refine ⟨-w, ?_⟩
      rw [← hdv, ← hdv']
      change (leftFace hT hp i).c - (rightFace hT hp i).c = _
      rw [c_leftFace, c_rightFace]
      push_cast
      linarith
    · rw [← show some i = e k from hd] at hek
      obtain ⟨w, hw⟩ := (hsides i).resolve_right (hS i (hS'S hek))
      rw [Rectangle.width] at hw
      refine ⟨w, ?_⟩
      rw [← hdv, ← hdv']
      change (rightFace hT hp i).c - (leftFace hT hp i).c = _
      rw [c_leftFace, c_rightFace]
      exact hw
  -- The exterior edge joins the two outer faces.
  have hstep₀ : (v (k₀ + 1)).c - (v k₀).c = R.x₁ - R.x₀ ∨
      (v (k₀ + 1)).c - (v k₀).c = R.x₀ - R.x₁ := by
    obtain ⟨d, hd, hdv, hdv'⟩ := hl k₀
    rcases d with ⟨_ | i, _ | _⟩
    · exact .inl (by rw [← hdv, ← hdv']; rfl)
    · exact .inr (by rw [← hdv, ← hdv']; rfl)
    · exact absurd (hd.trans hk₀) nofun
    · exact absurd (hd.trans hk₀) nofun
  -- Round the cycle the abscissa comes back.
  have htel : ∑ k, ((v (k + 1)).c - (v k).c) = 0 := by
    rw [Finset.sum_sub_distrib, Fintype.sum_equiv (Equiv.addRight 1) (fun k ↦ (v (k + 1)).c)
      (fun k ↦ (v k).c) fun _ ↦ rfl, sub_self]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)] at htel
  choose! m hm using hstep
  have hsum : ∑ k ∈ Finset.univ.erase k₀, ((v (k + 1)).c - (v k).c) =
      ((∑ k ∈ Finset.univ.erase k₀, m k : ℤ) : ℝ) := by
    push_cast
    exact Finset.sum_congr rfl fun k hk ↦ hm k (Finset.ne_of_mem_erase hk)
  rw [hsum] at htel
  push_cast at htel
  rcases hstep₀ with h₀ | h₀
  · exact ⟨-(∑ k ∈ Finset.univ.erase k₀, m k), by rw [Rectangle.width]; push_cast; linarith⟩
  · exact ⟨∑ k ∈ Finset.univ.erase k₀, m k, by rw [Rectangle.width]; push_cast; linarith⟩

end Endgame

end CutSet

end IntegerRectangle

open IntegerRectangle IntegerRectangle.CutSet in
/-- **Minimal cut-set proof** (Seymour) of the integer-rectangle tiling theorem. In Seymour's graph
of the nondegenerate tiles, delete the exterior edge and the tiles of non-integer height: either
the top of `R` stays reachable from the bottom, across tiles of integer height, and the height of
`R` is an integer; or a minimal set of deleted edges cutting it off is a bond, whose dual is a
cycle through the exterior edge, and the rest of that cycle crosses `R` from left to right over
tiles of integer width. -/
theorem IntegerRectangleTheorem_CutSet : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  classical
  rcases eq_or_lt_of_le R.hx with hx | hx
  · exact .inl ⟨0, by simp [Rectangle.width, ← hx]⟩
  rcases eq_or_lt_of_le R.hy with hy | hy
  · exact .inr ⟨0, by simp [Rectangle.height, ← hy]⟩
  have hT' := hT.proper hx hy
  have hp' := proper_properTiles T
  set S : Set (Option {i // (T i).Nondegenerate}) :=
    {e | ∀ i, e = some i → ¬ ∃ m : ℤ, (properTiles T i).height = m}
  by_cases hreach : Relation.ReflTransGen
      ((seymourMap hT' hp' hx hy).graph.deleteEdges S).Adj (vert hT' hx hy (none, false))
      (vert hT' hx hy (none, true))
  · obtain ⟨m, hm⟩ := int_sub_y₀_of_reflTransGen hT' hp' hx hy (S := S)
      (fun i hi ↦ by
        by_contra hcon
        exact hi fun j hj ↦ Option.some_injective _ hj ▸ hcon)
      (fun i h ↦ absurd h nofun) hreach
    exact .inr ⟨m, by simpa [Rectangle.height, vert, dartPt] using hm⟩
  · exact .inl (intWidth_of_not_reflTransGen hT' hp' hx hy (fun j ↦ hsides j.1) (S := S)
      (fun i hi ↦ hi i rfl) hreach)
