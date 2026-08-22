module

public import DifferentProofs.IntegerRectangle.Grid
public import DifferentProofsForMathlib.Combinatorics.Sperner.Basic

/-!
# The integer-rectangle tiling theorem, via Sperner's lemma

Wagon's fourteenth proof, due to James Schmerl. Suppose the conclusion fails. Triangulate the
tiling by drawing a diagonal in each tile, and label every vertex `(x, y)` by `A` if `x` is an
integer, by `B` if `x` is not but `y` is, and by `C` if neither is. A variation of Sperner's
lemma makes the number of triangles labelled `ABC` odd; but a tile with an integer side has no
such triangle, a contradiction.

Following the rest of this development the lattice is based at the corner of `R` rather than at
the origin, so that "integer" means "differing from the corner of `R` by an integer"
(`Sperner.label`) and the tiling never has to be translated.

## The variation of Sperner's lemma

Drawing one diagonal per tile does *not* give a triangulation in the usual sense: a corner of one
tile may sit in the interior of an edge of another, so a side of a triangle is subdivided by the
vertices lying on it, and the count of doors along a side is not determined by its endpoints. It
is determined *modulo 2*, which is all the argument needs, and this is what makes the labelling
geometric rather than arbitrary:

* a *door* is a segment whose endpoints are labelled `A` and `B`;
* along a vertical segment the abscissa is constant, so either every point is labelled `A` or
  none is, and a vertical side carries no doors at all (`door_label_vertical`);
* along a horizontal segment the labels are `A`/`B` at an integer height and `A`/`C` otherwise,
  so a door records a change in the integrality of the abscissa (`door_label_horizontal`), and
  the number of changes along a subdivided side has the parity of its endpoints'.

So the door count of a side may be replaced by a function of its two endpoints, T-vertices and
all, and the classical local count survives: a triangle carries an odd number of doors exactly
when its three vertices carry all three labels.

The two parts of that which are Sperner's lemma rather than this application — the count along a
subdivided segment and the local count for a triangle — are stated on their own in
`DifferentProofsForMathlib.Combinatorics.Sperner.Basic`, whose `Sperner.Color` and `Sperner.door`
this file uses. What is left here is Schmerl's labelling, the reading of it that kills the two
kinds of side, and the double count over the grid of the tiling.
-/

@[expose] public section

open Finset Set Sperner

namespace IntegerRectangle.Sperner

/-! ### The labelling -/

/-- The Sperner label of a point `p` in the unit lattice based at `o`: `A` if the abscissa of `p`
differs from that of `o` by an integer, `B` if it does not but the ordinate does, and `C` if
neither does. This is Schmerl's labelling, based at the corner `o` of the tiled rectangle instead
of at the origin. -/
noncomputable def label (o p : ℝ × ℝ) : Color :=
  if Int.fract p.1 = Int.fract o.1 then .A
  else if Int.fract p.2 = Int.fract o.2 then .B
  else .C

variable {o : ℝ × ℝ} {x x' y y' : ℝ}

/-- Points whose abscissae differ by an integer, at a common height, get the same label. -/
theorem label_congr_fst (h : Int.fract x = Int.fract x') : label o (x, y) = label o (x', y) := by
  simp only [label, h]

/-- Points whose ordinates differ by an integer, on a common vertical line, get the same
label. -/
theorem label_congr_snd (h : Int.fract y = Int.fract y') : label o (x, y) = label o (x, y') := by
  simp only [label, h]

/-- **A vertical segment is never a door.** Its two endpoints share an abscissa, so they are both
labelled `A` or neither is, and a door needs exactly one `A`. -/
theorem door_label_vertical (o : ℝ × ℝ) (x y y' : ℝ) :
    door (label o (x, y)) (label o (x, y')) = 0 := by
  simp only [label]
  split_ifs <;> rfl

/-- `1` when `x` differs from the abscissa of `o` by an integer, `0` otherwise. -/
noncomputable def onX (o : ℝ × ℝ) (x : ℝ) : ZMod 2 :=
  if Int.fract x = Int.fract o.1 then 1 else 0

/-- `1` when `y` differs from the ordinate of `o` by an integer, `0` otherwise. -/
noncomputable def onY (o : ℝ × ℝ) (y : ℝ) : ZMod 2 :=
  if Int.fract y = Int.fract o.2 then 1 else 0

/-- **A horizontal segment is a door exactly when it lies at an integer height and the
integrality of the abscissa changes across it.** This is the formula that makes the door count
along a subdivided side telescope. -/
theorem door_label_horizontal (o : ℝ × ℝ) (x x' y : ℝ) :
    door (label o (x, y)) (label o (x', y)) = onY o y * (onX o x + onX o x') := by
  simp only [label, onX, onY]
  split_ifs <;> rfl

/-! ### Doors along the grid -/

open Grid

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- The base point of the lattice: the lower-left corner of the tiled rectangle. Basing the
labelling here is what replaces Wagon's "place `R` in standard position"; the tiling is never
translated. -/
def corner (R : Rectangle) : ℝ × ℝ := (R.x₀, R.y₀)

@[simp] lemma corner_fst (R : Rectangle) : (corner R).1 = R.x₀ := rfl

@[simp] lemma corner_snd (R : Rectangle) : (corner R).2 = R.y₀ := rfl

/-- The door indicator of the `j`-th segment of the `k`-th horizontal grid line: the segment from
`(x j, y k)` to `(x (j + 1), y k)`, where `x` and `y` enumerate the grid lines of the tiling. -/
noncomputable def segDoor (R : Rectangle) (T : ι → Rectangle) (j k : ℕ) : ZMod 2 :=
  door (label (corner R) (nth (gridX R T) j, nth (gridY R T) k))
    (label (corner R) (nth (gridX R T) (j + 1), nth (gridY R T) k))

/-- **The doors along a subdivided horizontal side are counted, modulo `2`, by its endpoints.**
This is the variation of Sperner's lemma that Schmerl's proof needs: one diagonal per tile is not
a triangulation in the usual sense, since a corner of one tile may lie inside an edge of another,
so a side of a triangle carries however many vertices its neighbours put there. Along a
horizontal line the labels record the integrality of the abscissa, so the doors on the side count
the changes of that integrality — and the parity of the number of changes is fixed by the two
ends. -/
theorem sum_segDoor (R : Rectangle) (T : ι → Rectangle) {p q : ℕ} (h : p ≤ q) (k : ℕ) :
    ∑ j ∈ Ico p q, segDoor R T j k =
      door (label (corner R) (nth (gridX R T) p, nth (gridY R T) k))
        (label (corner R) (nth (gridX R T) q, nth (gridY R T) k)) := by
  simp only [segDoor, door_label_horizontal, ← Finset.mul_sum]
  rw [sum_Ico_add_succ h fun j ↦ onX (corner R) (nth (gridX R T) j)]

/-! ### The two triangles of a tile -/

/-- The doors on the three sides of the *lower* triangle of `S`, the one below the diagonal from
its lower-left to its upper-right corner. -/
noncomputable def lowerDoors (o : ℝ × ℝ) (S : Rectangle) : ZMod 2 :=
  door (label o (S.x₀, S.y₀)) (label o (S.x₁, S.y₀))
    + door (label o (S.x₁, S.y₀)) (label o (S.x₁, S.y₁))
    + door (label o (S.x₁, S.y₁)) (label o (S.x₀, S.y₀))

/-- The doors on the three sides of the *upper* triangle of `S`. -/
noncomputable def upperDoors (o : ℝ × ℝ) (S : Rectangle) : ZMod 2 :=
  door (label o (S.x₀, S.y₀)) (label o (S.x₀, S.y₁))
    + door (label o (S.x₀, S.y₁)) (label o (S.x₁, S.y₁))
    + door (label o (S.x₁, S.y₁)) (label o (S.x₀, S.y₀))

/-- **A tile with an integer side has no rainbow triangle.** If the width is an integer the two
ends of each horizontal side agree in the integrality of their abscissa, hence in their label; if
the height is an integer the two ends of each vertical side do. Either way each of the tile's two
triangles has two vertices with the same label, so it carries an even number of doors. -/
theorem doors_eq_zero (o : ℝ × ℝ) {S : Rectangle} (hS : S.HasIntegerSide) :
    lowerDoors o S = 0 ∧ upperDoors o S = 0 := by
  rcases hS with ⟨n, hn⟩ | ⟨n, hn⟩
  · have h : Int.fract S.x₀ = Int.fract S.x₁ :=
      (Int.fract_eq_fract.mpr ⟨n, by simpa only [Rectangle.width] using hn⟩).symm
    exact ⟨door_add_door_add_door_eq_zero fun hd ↦ hd.1 (label_congr_fst h),
      door_add_door_add_door_eq_zero fun hd ↦ hd.2.1 (label_congr_fst h)⟩
  · have h : Int.fract S.y₀ = Int.fract S.y₁ :=
      (Int.fract_eq_fract.mpr ⟨n, by simpa only [Rectangle.height] using hn⟩).symm
    exact ⟨door_add_door_add_door_eq_zero fun hd ↦ hd.2.1 (label_congr_snd h),
      door_add_door_add_door_eq_zero fun hd ↦ hd.1 (label_congr_snd h)⟩

/-- **The doors of a tile's two triangles are the doors on its bottom and top edges.** The
diagonal is a side of both triangles, so it is counted twice and cancels; the vertical sides
carry no doors at all. -/
theorem lowerDoors_add_upperDoors (i : ι) :
    lowerDoors (corner R) (T i) + upperDoors (corner R) (T i) =
      ∑ j ∈ Ico (idxL R T i) (idxR R T i),
        (segDoor R T j (idxB R T i) + segDoor R T j (idxT R T i)) := by
  have hle : idxL R T i ≤ idxR R T i :=
    le_of_nth_le_nth (idxL_lt i) (((nth_idxL i).le.trans (T i).hx).trans (nth_idxR i).ge)
  rw [Finset.sum_add_distrib, sum_segDoor R T hle, sum_segDoor R T hle, nth_idxL, nth_idxR,
    nth_idxB, nth_idxT]
  simp only [lowerDoors, upperDoors, door_label_vertical, add_zero, zero_add]
  rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

/-! ### The double count -/

/-- **The column double count.** Summing over the tiles met by the `j`-th column of grid cells
the doors on their bottom and top edges there leaves only the two ends of the column: an interior
horizontal grid segment is either interior to a tile, and counted by neither of its triangles, or
the top edge of one tile and the bottom edge of another, and counted twice. -/
theorem sum_column (hT : IsTiling R T) {j N : ℕ} (hj : j + 1 < (gridX R T).sort.length)
    (hN : (gridY R T).sort.length = N + 2) :
    ∑ i, (if idxL R T i ≤ j ∧ j < idxR R T i then
        segDoor R T j (idxB R T i) + segDoor R T j (idxT R T i) else 0) =
      segDoor R T j 0 + segDoor R T j (N + 1) := by
  have hcell : ∀ i, ∀ k < N + 1, (cellTile hT (j, k) = i ↔
      (idxL R T i ≤ j ∧ j < idxR R T i) ∧ idxB R T i ≤ k ∧ k < idxT R T i) :=
    fun i k hk ↦ cellTile_eq_iff hT (p := (j, k)) hj (by lia)
  have key : ∀ i, (if idxL R T i ≤ j ∧ j < idxR R T i then
        segDoor R T j (idxB R T i) + segDoor R T j (idxT R T i) else 0)
      = ∑ k ∈ range (N + 1), if (idxL R T i ≤ j ∧ j < idxR R T i) ∧ idxB R T i ≤ k ∧
        k < idxT R T i then segDoor R T j k + segDoor R T j (k + 1) else 0 := fun i ↦ by
    rw [← Finset.sum_filter]
    by_cases hP : idxL R T i ≤ j ∧ j < idxR R T i
    · have := idxT_lt (R := R) (T := T) i
      rw [if_pos hP, ← sum_Ico_add_succ (le_of_nth_le_nth (idxB_lt i)
        (((nth_idxB i).le.trans (T i).hy).trans (nth_idxT i).ge)) fun k ↦ segDoor R T j k]
      refine Finset.sum_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, hP, true_and]
      lia
    · rw [if_neg hP, Finset.filter_false_of_mem fun k _ hk ↦ hP hk.1, Finset.sum_empty]
  rw [Finset.sum_congr rfl fun i _ ↦ key i, Finset.sum_comm, Finset.range_eq_Ico,
    ← sum_Ico_add_succ (Nat.zero_le (N + 1)) fun k ↦ segDoor R T j k]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < N + 1 := (Finset.mem_Ico.mp hk).2
  rw [Finset.sum_eq_single_of_mem _ (Finset.mem_univ (cellTile hT (j, k)))
    fun i _ hi ↦ if_neg fun hc ↦ hi ((hcell i k hk').mpr hc).symm, if_pos ((hcell _ k hk').mp rfl)]

/-- **The doors of all the triangles are the doors on the bottom and top edges of `R`.** The
column count, summed over the columns of the grid. -/
theorem sum_tile_edges (hT : IsTiling R T) {N : ℕ} (hN : (gridY R T).sort.length = N + 2) :
    ∑ i, ∑ j ∈ Finset.Ico (idxL R T i) (idxR R T i),
        (segDoor R T j (idxB R T i) + segDoor R T j (idxT R T i))
      = ∑ j ∈ range ((gridX R T).sort.length - 1),
          (segDoor R T j 0 + segDoor R T j (N + 1)) := by
  have hIco : ∀ i, Finset.Ico (idxL R T i) (idxR R T i)
      = (range ((gridX R T).sort.length - 1)).filter
        (fun j ↦ idxL R T i ≤ j ∧ j < idxR R T i) := fun i ↦ by
    ext j
    have := idxR_lt (R := R) (T := T) i
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    lia
  simp only [hIco, Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j hj ↦ sum_column hT (by have := Finset.mem_range.mp hj; lia) hN

end IntegerRectangle.Sperner

open IntegerRectangle IntegerRectangle.Sperner Grid in
/-- **Sperner's lemma proof** (Schmerl) of the integer-rectangle tiling theorem. Suppose neither
side of `R` is an integer. Cut each tile in two along a diagonal and label every vertex by
Schmerl's rule; a tile with an integer side then has two vertices of the same label in each of
its triangles, so each carries an even number of doors (`doors_eq_zero`) and the total over all
triangles is even. On the other hand the doors of a tile's two triangles are those on its bottom
and top edges (`lowerDoors_add_upperDoors`), the interior horizontal segments pair off
(`sum_tile_edges`), and what survives is the bottom edge of `R` — one door, since the corner of
`R` is labelled `A` and its lower-right corner `B` — together with its top edge, which carries
none because the height of `R` is not an integer. So the total is odd. -/
theorem IntegerRectangleTheorem_Sperner : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  by_contra hR
  rw [Rectangle.HasIntegerSide, not_or] at hR
  obtain ⟨hw, hh⟩ := hR
  have hxne : Int.fract R.x₁ ≠ Int.fract R.x₀ := fun h ↦ hw <|
    (Int.fract_eq_fract.mp h).imp fun n hn ↦ by simpa only [Rectangle.width] using hn
  have hyne : Int.fract R.y₁ ≠ Int.fract R.y₀ := fun h ↦ hh <|
    (Int.fract_eq_fract.mp h).imp fun n hn ↦ by simpa only [Rectangle.height] using hn
  have hcard : 1 < (gridY R T).card := Finset.one_lt_card.mpr
    ⟨R.y₀, bot_mem_gridY, R.y₁, top_mem_gridY, fun h ↦ hyne (congrArg Int.fract h.symm)⟩
  obtain ⟨N, hNc⟩ : ∃ N, (gridY R T).card = N + 2 := ⟨(gridY R T).card - 2, by lia⟩
  have hN : (gridY R T).sort.length = N + 2 := by rw [Finset.length_sort, hNc]
  have hlast : nth (gridY R T) (N + 1) = R.y₁ := by rw [← nth_gridY_last hT, hN, Nat.succ_sub_one]
  have hA : label (corner R) (R.x₀, R.y₀) = Color.A := by simp only [label, corner_fst, ↓reduceIte]
  have hB : label (corner R) (R.x₁, R.y₀) = Color.B := by
    simp only [label, corner_fst, hxne, ↓reduceIte, corner_snd]
  have hTop : door (label (corner R) (R.x₀, R.y₁)) (label (corner R) (R.x₁, R.y₁)) = 0 := by
    rw [door_label_horizontal, onY, corner_snd, if_neg hyne, zero_mul]
  have hzero : ∑ i, ∑ j ∈ Finset.Ico (idxL R T i) (idxR R T i),
      (segDoor R T j (idxB R T i) + segDoor R T j (idxT R T i)) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by
      obtain ⟨h1, h2⟩ := doors_eq_zero (corner R) (hsides i)
      rw [← lowerDoors_add_upperDoors i, h1, h2, add_zero]
  have key := sum_tile_edges hT hN
  rw [hzero, Finset.sum_add_distrib, Finset.range_eq_Ico,
    sum_segDoor R T (Nat.zero_le _), sum_segDoor R T (Nat.zero_le _), nth_gridX_zero hT,
    nth_gridX_last hT, nth_gridY_zero hT, hlast, hA, hB, hTop, add_zero] at key
  exact absurd key (by decide)
