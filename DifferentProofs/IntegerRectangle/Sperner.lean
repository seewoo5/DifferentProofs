module

public import DifferentProofs.IntegerRectangle.Grid
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.DeriveFintype

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

Following Mead, whose lemma the argument rests on, an edge is *complete* when its endpoints carry
the first two labels `A` and `B`, and a triangle is complete when its vertices carry all three —
Wagon's triangle labelled `ABC`.

## The variation of Sperner's lemma

Drawing one diagonal per tile does *not* give a triangulation in the usual sense: a corner of one
tile may sit in the interior of an edge of another, so a side of a triangle is subdivided by the
vertices lying on it, and its number of complete edges is not determined by its endpoints. It is
determined *modulo 2*, which is all the argument needs, and this is what makes the labelling
geometric rather than arbitrary:

* along a vertical segment the abscissa is constant, so either every point is labelled `A` or
  none is, and a vertical side carries no complete edge at all
  (`completeEdge_label_vertical`);
* along a horizontal segment the labels are `A`/`B` at an integer height and `A`/`C` otherwise,
  so a complete edge records a change in the integrality of the abscissa
  (`completeEdge_label_horizontal`), and the number of changes along a subdivided side has the
  parity of its endpoints'.

So the count on a side may be replaced by a function of its two endpoints, T-vertices and all,
and the classical local count survives: a triangle carries an odd number of complete edges
exactly when it is itself complete.

## The counting core

The two ingredients that are Sperner's lemma rather than this application are proved first, and
have no geometry in them:

* `odd_card_completeEdges_iff`: **Sperner's lemma in dimension one.** A two-colouring of the
  points subdividing a segment has an odd number of complete edges exactly when the two ends of
  the segment are coloured differently. `sum_Ico_add_succ` is the same fact in the telescoped
  form the rest of the file uses.
* `completeEdge_sum_eq_one_iff`: **the local count in dimension two.** The three sides of a
  triangle carry an odd number of complete edges exactly when the triangle is complete. This is
  the step that turns a parity count of edges into a count of triangles.

Both are stated over `ZMod 2`, since the whole argument is a parity count and nothing is gained
by carrying a cardinality that is only ever used modulo `2`.

What the rest of the file adds is Schmerl's labelling, the reading of it that kills the two kinds
of side, the double count over the grid of the tiling, and finally
`odd_card_completeTriangles`: the number of complete triangles is odd. Wagon's proof then ends in
one line, since no tile with an integer side has one.

## Provenance

Those two are the low-dimensional cases of D. G. Mead, *Dissection of the hypercube into
simplexes*, Proc. Amer. Math. Soc. **76** (1979) 302–304, whose Lemma 1 is Sperner's lemma for a
*simplicial* decomposition of an `n`-polytope — one meeting face to face — in the parity form
used here: the number of simplices carrying all `n + 1` labels is odd exactly when the number of
boundary faces carrying all `n` of the first labels is odd. Its proof is the double count above,
together with the observation that a fully labelled simplex has exactly one fully labelled facet
while any other has none or two; for `n = 2` that observation is
`completeEdge_sum_eq_one_iff`, and for `n = 1` the lemma itself is
`odd_card_completeEdges_iff`.

Mead's Lemma 2 drops the face-to-face hypothesis, allowing a vertex of one simplex to lie in the
interior of a face of its neighbour, at the cost of a condition on the labelling: a
`k`-dimensional affine subspace carrying the first `k + 1` labels carries none of the later ones.
It is proved by induction on the dimension — the two subdivisions an interior hyperplane inherits
from the simplices above and below it need not agree, but they share a boundary, so the lemma one
dimension down gives them the same parity and they cancel regardless. The labelling condition is
what puts that hyperplane in the scope of the lower-dimensional lemma.

That is the version Wagon cites here, and the one geometric applications generally need, since a
subdivision assembled from independently chosen pieces is rarely face to face. This file does not
prove it; `sum_segComplete` below supplies what it would have given, for Schmerl's labelling only.
Mead's own application is to Monsky's theorem on equidissections, where the labelling comes from
a `p`-adic valuation — the same device, and the reason this lemma grew up in the dissection
literature rather than in the Sperner literature.

## Relation to mathlib

Mathlib has Sperner's *theorem* on antichains (`IsAntichain.sperner`) but not Sperner's *lemma*;
leanprover-community/mathlib4#25231 tracks the general statement, which needs a notion of
triangulation that mathlib also lacks. So the counting core cannot be cited and is proved here.

## Why not the general lemma

The obvious alternative is to formalize Mead's Lemma 2 in general dimension and recover both
counting statements by specializing to `n = 1` and `n = 2`. That was considered and rejected; the
reasons are worth recording, since the alternative looks strictly better until one prices it.

There is nothing to build on. Mathlib has no polytopes, and its `SimplicialComplex` is face to
face by construction — down-closed, and the intersection of two faces is a face — which is the
hypothesis Lemma 2 exists to drop. There is no pseudomanifold notion either, so the observation
that an interior facet lies in exactly two `n`-simplices, which Mead disposes of in a line, is
itself a theorem about triangulated polytopes that would have to be proved first.

It would not subsume the two statements in any case. `completeEdge_sum_eq_one_iff` is not
Lemma 1 at `n = 2`; it is an ingredient inside Lemma 1's proof, and would survive unchanged. And
`odd_card_completeEdges_iff` is indexed by `ℕ` because that is the form its applications produce,
so deriving it from a statement about segments in a real affine space would cost more glue than
the proof it replaced.

The specialization to `n = 2` would moreover be blocked. Mead's labelling condition, read
literally, fails for the labelling used here: the points `(0, 0)`, `(1/4, 1/2)` and `(1/2, 1)`
are collinear and carry the three labels in the order `A`, `C`, `B`, and nothing in the
hypothesis that every tile has an integer side stops a tiling from having corners there. Mead's
*proof* only ever applies the condition to the affine hulls of interior faces, where it does
hold — so a faithfully stated general lemma could not be applied here without first weakening its
hypothesis to the form the proof actually uses.

What would pay, if the counting core is ever generalized, is to keep the parity and drop the
geometry: cells, facets, each interior facet lying in exactly two cells and each boundary facet
in one, concluding that the facet values summed over the cells agree modulo `2` with their sum
over the boundary. That is dimension-free, needs nothing mathlib lacks, and is the content the
two statements share. It is also the direction taken by
leanprover-community/mathlib4#42788, which builds a facet-ridge incidence interface and
explicitly declines to claim the geometric lemma.

The same reasoning is why the counting core sits here rather than under
`DifferentProofsForMathlib`: what mathlib would want is the general lemma, and what this proof
needs is two special cases of it, so the special cases are not upstream material and are kept
beside their use.
-/

@[expose] public section

open Finset Set

namespace IntegerRectangle.Sperner

/-! ### The counting core in dimension one -/

section Dim1

variable {p q : ℕ}

/-- Two elements of `ZMod 2` are different exactly when they sum to `1`. -/
theorem add_eq_one_iff_ne (a b : ZMod 2) : a + b = 1 ↔ a ≠ b := by decide +revert

/-- The complete edges of a two-colouring `c` of the points subdividing the segment `[p, q]`:
those `j` in `[p, q)` whose edge to `j + 1` changes colour. With only two labels in play, an edge
is complete exactly when it is bichromatic. -/
def completeEdges (c : ℕ → ZMod 2) (p q : ℕ) : Finset ℕ :=
  (Finset.Ico p q).filter fun j ↦ c j ≠ c (j + 1)

/-- **The one-dimensional count**, telescoped: the increments of a two-colouring along a
subdivided segment sum to the sum of its two ends, because consecutive terms cancel modulo `2`.
This is the form in which an application meets `odd_card_completeEdges_iff`, and the reason a
labelling constant in one direction has its count read off the endpoints of a side, however many
vertices subdivide it. -/
theorem sum_Ico_add_succ (h : p ≤ q) (c : ℕ → ZMod 2) :
    ∑ j ∈ Finset.Ico p q, (c j + c (j + 1)) = c p + c q := by
  simpa only [CharTwo.sub_eq_add, add_comm] using Finset.sum_Ico_sub c h

/-- **Sperner's lemma in dimension one.** A two-colouring of the points subdividing a segment has
an odd number of complete edges exactly when its two ends are coloured differently — however
many points subdivide it. -/
theorem odd_card_completeEdges_iff (h : p ≤ q) (c : ℕ → ZMod 2) :
    Odd (completeEdges c p q).card ↔ c p ≠ c q := by
  have hite : ∀ a b : ZMod 2, (if a ≠ b then (1 : ZMod 2) else 0) = a + b := by decide +revert
  have hcard : ((completeEdges c p q).card : ZMod 2) = c p + c q := by
    simpa only [completeEdges, ← Finset.sum_boole, hite] using sum_Ico_add_succ h c
  rw [← ZMod.natCast_eq_one_iff_odd, hcard, add_eq_one_iff_ne]

end Dim1

/-! ### The counting core in dimension two -/

/-- The three labels of Sperner's lemma in dimension two. Following Mead, an edge is *complete*
when its endpoints carry the first two labels, and a triangle is complete when its vertices carry
all three — Wagon's triangle labelled `ABC`. -/
inductive Color
  /-- The first label. -/
  | A
  /-- The second label. -/
  | B
  /-- The third label. -/
  | C
  deriving DecidableEq, Fintype

/-- The indicator of a *complete edge*, read off the labels of its two endpoints: `1` when they
are `A` and `B` in some order, and `0` otherwise. -/
def completeEdge : Color → Color → ZMod 2
  | .A, .B => 1
  | .B, .A => 1
  | _, _ => 0

/-- An edge is complete in either direction. -/
theorem completeEdge_comm (x y : Color) : completeEdge x y = completeEdge y x := by
  cases x <;> cases y <;> rfl

/-- A triple of labels is *complete* when its three entries are all different. -/
def IsCompleteTriple (x y z : Color) : Prop := x ≠ y ∧ y ≠ z ∧ x ≠ z

instance (x y z : Color) : Decidable (IsCompleteTriple x y z) := by
  unfold IsCompleteTriple
  infer_instance

/-- **The local count of Sperner's lemma in dimension two.** The three sides of a triangle carry
an odd number of complete edges exactly when the triangle itself is complete. This is the step
that turns a parity count of edges into a count of completely labelled triangles. -/
theorem completeEdge_sum_eq_one_iff (x y z : Color) :
    completeEdge x y + completeEdge y z + completeEdge z x = 1 ↔ IsCompleteTriple x y z := by
  unfold IsCompleteTriple
  decide +revert

/-- Over `ZMod 2` there is no room between "not one" and "zero". -/
private lemma eq_ite_of_eq_one_iff {w : ZMod 2} {P : Prop} [Decidable P] (h : w = 1 ↔ P) :
    w = if P then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP, h.mpr hP]
  · rw [if_neg hP]
    have hw : w ≠ 1 := fun hw ↦ hP (h.mp hw)
    revert hw
    generalize w = v
    revert v
    decide

/-- The parity count of a triangle's three sides, as the indicator of its being complete. -/
theorem completeEdge_sum_eq_ite (x y z : Color) :
    completeEdge x y + completeEdge y z + completeEdge z x
      = if IsCompleteTriple x y z then 1 else 0 :=
  eq_ite_of_eq_one_iff (completeEdge_sum_eq_one_iff x y z)


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

/-- **A vertical segment is never a complete edge.** Its two endpoints share an abscissa, so
they are both labelled `A` or neither is, and a complete edge needs exactly one `A`. -/
theorem completeEdge_label_vertical (o : ℝ × ℝ) (x y y' : ℝ) :
    completeEdge (label o (x, y)) (label o (x, y')) = 0 := by
  simp only [label]
  split_ifs <;> rfl

/-- `1` when `x` differs from the abscissa of `o` by an integer, `0` otherwise. -/
noncomputable def onX (o : ℝ × ℝ) (x : ℝ) : ZMod 2 :=
  if Int.fract x = Int.fract o.1 then 1 else 0

/-- `1` when `y` differs from the ordinate of `o` by an integer, `0` otherwise. -/
noncomputable def onY (o : ℝ × ℝ) (y : ℝ) : ZMod 2 :=
  if Int.fract y = Int.fract o.2 then 1 else 0

/-- **A horizontal segment is a complete edge exactly when it lies at an integer height and the
integrality of the abscissa changes across it.** This is the formula that makes the count along a
subdivided side telescope. -/
theorem completeEdge_label_horizontal (o : ℝ × ℝ) (x x' y : ℝ) :
    completeEdge (label o (x, y)) (label o (x', y)) = onY o y * (onX o x + onX o x') := by
  simp only [label, onX, onY]
  split_ifs <;> rfl

/-! ### Complete edges along the grid -/

open Grid

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- The base point of the lattice: the lower-left corner of the tiled rectangle. Basing the
labelling here is what replaces Wagon's "place `R` in standard position"; the tiling is never
translated. -/
def corner (R : Rectangle) : ℝ × ℝ := (R.x₀, R.y₀)

@[simp] lemma corner_fst (R : Rectangle) : (corner R).1 = R.x₀ := rfl

@[simp] lemma corner_snd (R : Rectangle) : (corner R).2 = R.y₀ := rfl

/-- The complete-edge indicator of the `j`-th segment of the `k`-th horizontal grid line: the
segment from `(x j, y k)` to `(x (j + 1), y k)`, where `x` and `y` enumerate the grid lines. -/
noncomputable def segComplete (R : Rectangle) (T : ι → Rectangle) (j k : ℕ) : ZMod 2 :=
  completeEdge (label (corner R) (nth (gridX R T) j, nth (gridY R T) k))
    (label (corner R) (nth (gridX R T) (j + 1), nth (gridY R T) k))

/-- **The complete edges along a subdivided horizontal side are counted, modulo `2`, by its
endpoints.**
This is the variation of Sperner's lemma that Schmerl's proof needs: one diagonal per tile is not
a triangulation in the usual sense, since a corner of one tile may lie inside an edge of another,
so a side of a triangle carries however many vertices its neighbours put there. Along a
horizontal line the labels record the integrality of the abscissa, so the complete edges on the
side count the changes of that integrality — and the parity of the number of changes is fixed by
the two ends. -/
theorem sum_segComplete (R : Rectangle) (T : ι → Rectangle) {p q : ℕ} (h : p ≤ q) (k : ℕ) :
    ∑ j ∈ Ico p q, segComplete R T j k =
      completeEdge (label (corner R) (nth (gridX R T) p, nth (gridY R T) k))
        (label (corner R) (nth (gridX R T) q, nth (gridY R T) k)) := by
  simp only [segComplete, completeEdge_label_horizontal, ← Finset.mul_sum]
  rw [sum_Ico_add_succ h fun j ↦ onX (corner R) (nth (gridX R T) j)]

/-! ### The two triangles of a tile -/

/-- The three vertices, in cyclic order, of one of the two triangles into which the diagonal from
`S`'s lower-left to its upper-right corner cuts it: `false` is the triangle below the diagonal,
`true` the one above. -/
def triangle (S : Rectangle) : Bool → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)
  | false => ((S.x₀, S.y₀), (S.x₁, S.y₀), (S.x₁, S.y₁))
  | true => ((S.x₀, S.y₀), (S.x₀, S.y₁), (S.x₁, S.y₁))

/-- A triangle of `S` is *complete* when its three vertices carry three different labels. This is
Wagon's triangle labelled `ABC`, and the object his variation of Sperner's lemma counts. -/
def IsCompleteTriangle (o : ℝ × ℝ) (S : Rectangle) (b : Bool) : Prop :=
  IsCompleteTriple (label o (triangle S b).1) (label o (triangle S b).2.1)
    (label o (triangle S b).2.2)

noncomputable instance (o : ℝ × ℝ) (S : Rectangle) (b : Bool) :
    Decidable (IsCompleteTriangle o S b) := by
  unfold IsCompleteTriangle
  infer_instance

/-- The number of complete edges on the three sides of a triangle of `S`, modulo `2`. -/
noncomputable def sideCount (o : ℝ × ℝ) (S : Rectangle) (b : Bool) : ZMod 2 :=
  completeEdge (label o (triangle S b).1) (label o (triangle S b).2.1)
    + completeEdge (label o (triangle S b).2.1) (label o (triangle S b).2.2)
    + completeEdge (label o (triangle S b).2.2) (label o (triangle S b).1)

/-- **A triangle carries an odd number of complete edges exactly when it is complete**, the local
count of Sperner's lemma read on the triangles of a tile. -/
theorem sideCount_eq_ite (o : ℝ × ℝ) (S : Rectangle) (b : Bool) :
    sideCount o S b = if IsCompleteTriangle o S b then 1 else 0 :=
  completeEdge_sum_eq_ite _ _ _

/-- **A tile with an integer side has no complete triangle.** If the width is an integer the two
ends of each horizontal side agree in the integrality of their abscissa, hence in their label; if
the height is an integer the two ends of each vertical side do. Either way both triangles of the
tile have two vertices carrying the same label. -/
theorem not_isCompleteTriangle (o : ℝ × ℝ) {S : Rectangle} (hS : S.HasIntegerSide) (b : Bool) :
    ¬ IsCompleteTriangle o S b := by
  rcases hS with ⟨n, hn⟩ | ⟨n, hn⟩
  · have h : Int.fract S.x₀ = Int.fract S.x₁ :=
      (Int.fract_eq_fract.mpr ⟨n, by simpa only [Rectangle.width] using hn⟩).symm
    cases b
    · exact fun hd ↦ hd.1 (label_congr_fst h)
    · exact fun hd ↦ hd.2.1 (label_congr_fst h)
  · have h : Int.fract S.y₀ = Int.fract S.y₁ :=
      (Int.fract_eq_fract.mpr ⟨n, by simpa only [Rectangle.height] using hn⟩).symm
    cases b
    · exact fun hd ↦ hd.2.1 (label_congr_snd h)
    · exact fun hd ↦ hd.1 (label_congr_snd h)

/-- **The complete edges of a tile's two triangles are those on its bottom and top edges.** The
diagonal is a side of both triangles, so it is counted twice and cancels; the vertical sides
carry no complete edges at all. -/
theorem sum_sideCount (i : ι) :
    ∑ b, sideCount (corner R) (T i) b =
      ∑ j ∈ Ico (idxL R T i) (idxR R T i),
        (segComplete R T j (idxB R T i) + segComplete R T j (idxT R T i)) := by
  have hle : idxL R T i ≤ idxR R T i :=
    le_of_nth_le_nth (idxL_lt i) (((nth_idxL i).le.trans (T i).hx).trans (nth_idxR i).ge)
  rw [Finset.sum_add_distrib, sum_segComplete R T hle, sum_segComplete R T hle, nth_idxL,
    nth_idxR, nth_idxB, nth_idxT, Fintype.sum_bool]
  simp only [sideCount, triangle, completeEdge_label_vertical, add_zero, zero_add]
  rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero, add_comm]


/-! ### The double count -/

/-- **The column double count.** Summing over the tiles met by the `j`-th column of grid cells
the complete edges on their bottom and top edges leaves only the two ends of the column: an
interior
horizontal grid segment is either interior to a tile, and counted by neither of its triangles, or
the top edge of one tile and the bottom edge of another, and counted twice. -/
theorem sum_column (hT : IsTiling R T) {j N : ℕ} (hj : j + 1 < (gridX R T).sort.length)
    (hN : (gridY R T).sort.length = N + 2) :
    ∑ i, (if idxL R T i ≤ j ∧ j < idxR R T i then
        segComplete R T j (idxB R T i) + segComplete R T j (idxT R T i) else 0) =
      segComplete R T j 0 + segComplete R T j (N + 1) := by
  have hcell : ∀ i, ∀ k < N + 1, (cellTile hT (j, k) = i ↔
      (idxL R T i ≤ j ∧ j < idxR R T i) ∧ idxB R T i ≤ k ∧ k < idxT R T i) :=
    fun i k hk ↦ cellTile_eq_iff hT (p := (j, k)) hj (by lia)
  have key : ∀ i, (if idxL R T i ≤ j ∧ j < idxR R T i then
        segComplete R T j (idxB R T i) + segComplete R T j (idxT R T i) else 0)
      = ∑ k ∈ range (N + 1), if (idxL R T i ≤ j ∧ j < idxR R T i) ∧ idxB R T i ≤ k ∧
        k < idxT R T i then segComplete R T j k + segComplete R T j (k + 1) else 0 := fun i ↦ by
    rw [← Finset.sum_filter]
    by_cases hP : idxL R T i ≤ j ∧ j < idxR R T i
    · have := idxT_lt (R := R) (T := T) i
      rw [if_pos hP, ← sum_Ico_add_succ (le_of_nth_le_nth (idxB_lt i)
        (((nth_idxB i).le.trans (T i).hy).trans (nth_idxT i).ge)) fun k ↦ segComplete R T j k]
      refine Finset.sum_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, hP, true_and]
      lia
    · rw [if_neg hP, Finset.filter_false_of_mem fun k _ hk ↦ hP hk.1, Finset.sum_empty]
  rw [Finset.sum_congr rfl fun i _ ↦ key i, Finset.sum_comm, Finset.range_eq_Ico,
    ← sum_Ico_add_succ (Nat.zero_le (N + 1)) fun k ↦ segComplete R T j k]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < N + 1 := (Finset.mem_Ico.mp hk).2
  rw [Finset.sum_eq_single_of_mem _ (Finset.mem_univ (cellTile hT (j, k)))
    fun i _ hi ↦ if_neg fun hc ↦ hi ((hcell i k hk').mpr hc).symm, if_pos ((hcell _ k hk').mp rfl)]

/-- **The complete edges of all the triangles are those on the bottom and top edges of `R`.** The
column count, summed over the columns of the grid. -/
theorem sum_tile_edges (hT : IsTiling R T) {N : ℕ} (hN : (gridY R T).sort.length = N + 2) :
    ∑ i, ∑ j ∈ Finset.Ico (idxL R T i) (idxR R T i),
        (segComplete R T j (idxB R T i) + segComplete R T j (idxT R T i))
      = ∑ j ∈ range ((gridX R T).sort.length - 1),
          (segComplete R T j 0 + segComplete R T j (N + 1)) := by
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

open scoped Classical in
/-- **The number of completely labelled triangles is odd**, when neither side of `R` is an
integer. This is the conclusion Wagon draws from his variation of Sperner's lemma, and the whole
weight of the proof: each triangle contributes its parity of complete edges
(`sideCount_eq_ite`), the tiles' contributions are the complete edges on their bottom and top
edges (`sum_sideCount`), the interior horizontal segments pair off (`sum_tile_edges`), and what
survives is the bottom edge of `R` — a single complete edge, since the corner of `R` is labelled
`A` and its lower-right corner `B` — together with its top edge, which carries none because the
height of `R` is not an integer. -/
theorem odd_card_completeTriangles (hT : IsTiling R T) (hw : ¬∃ n : ℤ, R.width = n)
    (hh : ¬∃ n : ℤ, R.height = n) :
    Odd (Finset.univ.filter fun t : ι × Bool ↦
      IsCompleteTriangle (corner R) (T t.1) t.2).card := by
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
  have hTop : completeEdge (label (corner R) (R.x₀, R.y₁))
      (label (corner R) (R.x₁, R.y₁)) = 0 := by
    rw [completeEdge_label_horizontal, onY, corner_snd, if_neg hyne, zero_mul]
  have key := sum_tile_edges hT hN
  rw [Finset.sum_add_distrib, Finset.range_eq_Ico, sum_segComplete R T (Nat.zero_le _),
    sum_segComplete R T (Nat.zero_le _), nth_gridX_zero hT, nth_gridX_last hT,
    nth_gridY_zero hT, hlast, hA, hB, hTop, add_zero] at key
  rw [← ZMod.natCast_eq_one_iff_odd, ← Finset.sum_boole]
  calc ∑ t : ι × Bool, (if IsCompleteTriangle (corner R) (T t.1) t.2 then (1 : ZMod 2) else 0)
      = ∑ t : ι × Bool, sideCount (corner R) (T t.1) t.2 :=
        Finset.sum_congr rfl fun t _ ↦ (sideCount_eq_ite _ _ _).symm
    _ = ∑ i, ∑ b, sideCount (corner R) (T i) b := Fintype.sum_prod_type _
    _ = ∑ i, ∑ j ∈ Ico (idxL R T i) (idxR R T i),
          (segComplete R T j (idxB R T i) + segComplete R T j (idxT R T i)) :=
        Finset.sum_congr rfl fun i _ ↦ sum_sideCount i
    _ = 1 := key

end IntegerRectangle.Sperner

open IntegerRectangle IntegerRectangle.Sperner in
/-- **Sperner's lemma proof** (Schmerl) of the integer-rectangle tiling theorem, in the two steps
Wagon states it: if neither side of `R` were an integer, the number of triangles labelled `ABC`
would be odd (`odd_card_completeTriangles`), and in particular there would be one; but every tile
has an integer side, so no triangle is so labelled (`not_isCompleteTriangle`). -/
theorem IntegerRectangleTheorem_Sperner : IntegerRectangleTheorem := by
  classical
  intro ι _ R T hT hsides
  by_contra hR
  rw [Rectangle.HasIntegerSide, not_or] at hR
  obtain ⟨hw, hh⟩ := hR
  have hodd := odd_card_completeTriangles hT hw hh
  rw [Finset.filter_false_of_mem fun t _ ↦
    not_isCompleteTriangle (corner R) (hsides t.1) t.2, Finset.card_empty] at hodd
  exact absurd hodd (by decide)
