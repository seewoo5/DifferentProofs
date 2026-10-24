module

public import DifferentProofs.IntegerRectangle.CornerCount
public import DifferentProofsForMathlib.Algebra.Order.Floor.Ring
public import DifferentProofsForMathlib.Combinatorics.Graph.HalfEdgePairing

/-!
# The integer-rectangle theorem by an Eulerian path

Wagon's seventh proof, due to Michael S. Paterson. Let `Γ` be the graph whose vertices are the
corners of the tiles, two of them joined whenever they are the two ends of a horizontal side of an
H-tile, a tile of integer width, or of a vertical side of a V-tile, a tile of integer height. A
tile having a vertex as a corner contributes exactly one edge there, so the degree of a vertex is
the number of tiles having it as a corner: `2` or `4` away from the corners of `R`, by the local
picture of how tiles fit together, and `1` at a corner of `R`. A walk that starts at a corner of
`R` and repeats no edge can therefore not stop before it reaches another corner of `R`. Every
edge of `Γ` is a segment of integer length parallel to an axis, so the ends of the walk differ by
a vector with integer entries, and that is an integer side of `R`.

`Γ` is built as a multigraph (`patersonGraph`), through its half-edges, or darts (`patersonDarts`):
a dart is a tile together with one of its four corners, and the two darts of an edge are the two
ends of a side of a tile. Each tile contributes two opposite sides, its horizontal ones if it is an
H-tile and its vertical ones otherwise, so that a tile with both sides integral counts as an H-tile,
as in the staircase and reducible-link proofs. Labelling each dart by its corner point gives `Γ`
(`HalfEdgePairing.labelGraph`). It is not a simple graph: two H-tiles of the same width stacked on
each other share a side, which is a double edge of `Γ`. Its vertices are all the points of the
plane, those that are not corners of tiles being isolated.

The degree of a vertex is the number of darts at it, which is the number of corners the tiles have
there (`card_darts_eq`), and only its parity is used. That is the corner parity of `CornerCount`,
which replaces Wagon's local picture: the vertices of odd degree are exactly the corners of `R`
(`odd_card_darts_iff`), each of which lies on exactly one tile.

Paterson walks a trail from a corner of `R` until it gets stuck. Mathlib's multigraphs have no
walks yet, so the handshake lemma stands in for the trail: a vertex of odd degree is joined by a
chain of edges to another vertex of odd degree (`HalfEdgePairing.exists_ne_reflTransGen_of_odd`).
For the lower-left corner of `R` that is another corner of `R` (`exists_reachable_corner`). A chain
of edges of `Γ` preserves the pair of fractional parts of a point (`fracts_eq_of_reachable`), which
is the integrality of the edges.

## Main result

- `IntegerRectangleTheorem_EulerianPath`: Paterson's Eulerian-path proof of the integer-rectangle
  theorem.
-/

@[expose] public section

open Finset

namespace IntegerRectangle.EulerianPath

variable {ι : Type}

/-! ### Paterson's graph -/

/-- The corner of the tile `T d.1` named by `d.2`: on its right side if `d.2.1`, on its top side
if `d.2.2`. -/
def corner (T : ι → Rectangle) (d : ι × Bool × Bool) : ℝ × ℝ :=
  (if d.2.1 then (T d.1).x₁ else (T d.1).x₀, if d.2.2 then (T d.1).y₁ else (T d.1).y₀)

open scoped Classical in
/-- The other end of the side that the tile `T d.1` contributes to `Γ` at its corner `d.2`: the
corner across its width if it is an H-tile, across its height otherwise. -/
noncomputable def otherEnd (T : ι → Rectangle) (d : ι × Bool × Bool) : ι × Bool × Bool :=
  if (T d.1).IsHTile then (d.1, !d.2.1, d.2.2) else (d.1, d.2.1, !d.2.2)

lemma otherEnd_involutive (T : ι → Rectangle) : Function.Involutive (otherEnd T) := by
  rintro ⟨i, a, b⟩
  by_cases h : (T i).IsHTile <;> simp only [otherEnd, h, ↓reduceIte, Bool.not_not]

lemma otherEnd_ne (T : ι → Rectangle) (d : ι × Bool × Bool) : otherEnd T d ≠ d := by
  grind [otherEnd]

open scoped Classical in
/-- **The darts of Paterson's graph**: the pairs of a tile and one of its four corners. The edge
`(i, b)` is the bottom or top side of `T i`, according to `b`, if `T i` is an H-tile, and its left
or right side otherwise; its two darts are its two ends. -/
noncomputable def patersonDarts (T : ι → Rectangle) :
    HalfEdgePairing (ι × Bool) (ι × Bool × Bool) where
  edgePerm := (otherEnd_involutive T).toPerm
  edge d := (d.1, if (T d.1).IsHTile then d.2.2 else d.2.1)
  edgePerm_edgePerm := otherEnd_involutive T
  edgePerm_ne := otherEnd_ne T
  edge_eq_edge_iff := by
    simp only [Prod.ext_iff, eq_ite_iff, Function.Involutive.coe_toPerm, otherEnd, Bool.eq_not_iff]
    grind
  edge_surjective e := ⟨(e.1, e.2, e.2), congrArg _ (ite_self _)⟩

/-- **Paterson's graph** `Γ`: the darts of `patersonDarts` labelled by their corners, so that each
side a tile contributes joins its two ends. -/
noncomputable def patersonGraph (T : ι → Rectangle) : Graph (ℝ × ℝ) (ι × Bool) :=
  (patersonDarts T).labelGraph (corner T)

/-! ### The edges of `Γ` have integer length -/

/-- The pair of fractional parts of a point of the plane. Two points share it exactly when they
differ by a vector with integer entries. -/
noncomputable def fracts (p : ℝ × ℝ) : ℝ × ℝ := (Int.fract p.1, Int.fract p.2)

variable {T : ι → Rectangle} {p q : ℝ × ℝ}

private lemma fracts_eq_of_adj (hsides : ∀ i, (T i).HasIntegerSide)
    (h : (patersonGraph T).Adj p q) : fracts p = fracts q := by
  obtain ⟨-, d, -, rfl, rfl⟩ := h
  have hx : (T d.1).IsHTile → _ := Int.fract_eq_fract'.mpr
  have hy := Int.fract_eq_fract'.mpr ∘ (hsides d.1).isVTile_of_not_isHTile
  grind [fracts, corner, patersonDarts]

/-- **A walk in `Γ` moves by a vector with integer entries.** Each of its edges is a side of a
tile whose length is an integer, and which is parallel to an axis. -/
theorem fracts_eq_of_reachable (hsides : ∀ i, (T i).HasIntegerSide)
    (h : Relation.ReflTransGen (patersonGraph T).Adj p q) : fracts p = fracts q :=
  Relation.reflTransGen_le_of_equivalence_of_le (r := fun p q ↦ fracts p = fracts q)
    ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩ (fun _ _ ↦ fracts_eq_of_adj hsides) p q h

/-! ### The degrees of `Γ` -/

variable [Fintype ι] {R : Rectangle}

/-- **The degree of a point in `Γ`**, the number of darts at it, is the number of corners the
tiles have there. -/
theorem card_darts_eq (p : ℝ × ℝ) :
    Nat.card {d // corner T d = p} = ∑ i, cornerCount (T i) p.1 p.2 := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter, Fintype.sum_prod_type]
  exact sum_congr rfl (by simp only [corner, Fintype.sum_bool, cornerCount, xCount, yCount]; grind)

/-- **The vertices of odd degree in `Γ` are the corners of `R`**: by corner parity, the tiles
have an odd number of corners at a point exactly when `R` does. -/
theorem odd_card_darts_iff (hT : IsTiling R T) (p : ℝ × ℝ) :
    Odd (Nat.card {d // corner T d = p}) ↔ Odd (cornerCount R p.1 p.2) := by
  rw [card_darts_eq, ← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd,
    hT.sum_cornerCount_mod_two]

/-! ### The proof -/

/-- **The walk of Paterson's proof.** A walk in `Γ` leads from the lower-left corner of `R` to
another of its corners: the lower-left corner is a vertex of odd degree, so the handshake lemma
joins it to another vertex of odd degree, and that is a corner of `R`. -/
theorem exists_reachable_corner (hT : IsTiling R T) :
    Relation.ReflTransGen (patersonGraph T).Adj (R.x₀, R.y₀) (R.x₁, R.y₀) ∨
      Relation.ReflTransGen (patersonGraph T).Adj (R.x₀, R.y₀) (R.x₀, R.y₁) ∨
      Relation.ReflTransGen (patersonGraph T).Adj (R.x₀, R.y₀) (R.x₁, R.y₁) := by
  have := (patersonDarts T).exists_ne_reflTransGen_of_odd (corner T) (x := (R.x₀, R.y₀))
  simp only [odd_card_darts_iff hT] at this
  grind [patersonGraph, cornerCount, xCount, yCount]

end IntegerRectangle.EulerianPath

open IntegerRectangle.EulerianPath in
/-- **Eulerian-path proof** (Paterson) of the integer-rectangle tiling theorem. A walk in `Γ`
joins the lower-left corner of `R` to another of its corners, and moves by a vector with integer
entries; whichever corner it reaches, that is an integer side of `R`. -/
theorem IntegerRectangleTheorem_EulerianPath : IntegerRectangleTheorem := by
  refine fun _ _ hT hsides ↦ .imp Int.fract_eq_fract'.mp Int.fract_eq_fract'.mp ?_
  grind [exists_reachable_corner hT, → fracts_eq_of_reachable hsides, fracts]
