/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# The counting core of Sperner's lemma

Sperner's lemma is a parity count. A subdivided region carries a labelling of its vertices, and
the number of edges whose endpoints carry a designated pair of labels is determined, modulo `2`,
by the labels on the boundary alone, because every interior edge is shared by exactly two cells
and cancels. This file has the two purely combinatorial ingredients of that argument, with no
geometry: the count in dimension one, stated for two colours and bichromatic edges, and the
local count in dimension two, stated for three labels and *doors* — the name an `A`–`B` edge
carries in the classical "rooms and doors" exposition of the lemma.

## Main statements

* `Sperner.odd_card_colorChanges_iff`: **Sperner's lemma in dimension one.** A two-colouring of
  the points subdividing a segment has an odd number of bichromatic edges exactly when the two
  ends of the segment are coloured differently. `Sperner.sum_Ico_add_succ` is the same fact in
  the telescoped form an application usually wants.
* `Sperner.door_add_door_add_door_eq_one_iff`: **the local count in dimension two.** A triangle
  carries an odd number of doors on its three sides exactly when its three vertices carry three
  different labels. This is the step that turns "the door count is odd" into "some triangle is
  rainbow".

Both are stated over `ZMod 2`, since the whole argument is a parity count and nothing is gained
by carrying a cardinality that is only ever used modulo `2`.

## Provenance

Both statements are the low-dimensional cases of D. G. Mead, *Dissection of the hypercube into
simplexes*, Proc. Amer. Math. Soc. **76** (1979) 302–304, whose Lemma 1 is Sperner's lemma for a
*simplicial* decomposition of an `n`-polytope — one meeting face to face — in the parity form
used here: the number of simplices carrying all `n + 1` labels is odd exactly when the number of
boundary faces carrying all `n` of the first labels is odd. Its proof is the double count above,
together with the observation that a fully labelled simplex has exactly one fully labelled facet
while any other has none or two; for `n = 2` that observation is
`door_add_door_add_door_eq_one_iff`, and for `n = 1` the lemma itself is
`odd_card_colorChanges_iff`.

Mead's Lemma 2 drops the face-to-face hypothesis, allowing a vertex of one simplex to lie in the
interior of a face of its neighbour, at the cost of a condition on the labelling: a
`k`-dimensional affine subspace carrying the first `k + 1` labels carries none of the later ones.
It is proved by induction on the dimension — the two subdivisions an interior hyperplane inherits
from the simplices above and below it need not agree, but they share a boundary, so the lemma one
dimension down gives them the same parity and they cancel regardless. The labelling condition is
what puts that hyperplane in the scope of the lower-dimensional lemma.

That version is the one geometric applications actually need, since a subdivision assembled from
independently chosen pieces is rarely face to face; it is what Wagon cites for Schmerl's proof of
the integer-rectangle tiling theorem in `DifferentProofs.IntegerRectangle.Sperner`, which supplies
the missing hypothesis for that labelling directly rather than in Mead's general form. Mead's own
application is to Monsky's theorem on equidissections, where the labelling comes from a `p`-adic
valuation — the same device, and the reason this lemma grew up in the dissection literature
rather than in the Sperner literature.

## Relation to mathlib

Mathlib has Sperner's *theorem* on antichains (`IsAntichain.sperner`) but not Sperner's *lemma*;
leanprover-community/mathlib4#25231 tracks the general statement, which needs a notion of
triangulation that mathlib also lacks. This file is deliberately less than that: it is the
labelling arithmetic, which is what an application has to redo if it cannot cite the lemma. Its
natural home would be `Mathlib/Combinatorics/Sperner/Basic.lean`.
-/

@[expose] public section

namespace Sperner

/-! ### Dimension one -/

section Dim1

variable {p q : ℕ}

/-- Two elements of `ZMod 2` are different exactly when they sum to `1`. -/
theorem add_eq_one_iff_ne (a b : ZMod 2) : a + b = 1 ↔ a ≠ b := by decide +revert

/-- The bichromatic edges of a two-colouring `c` of the points subdividing the segment
`[p, q]`: those `j` in `[p, q)` whose edge to `j + 1` changes colour. -/
def colorChanges (c : ℕ → ZMod 2) (p q : ℕ) : Finset ℕ :=
  (Finset.Ico p q).filter fun j ↦ c j ≠ c (j + 1)

/-- **The one-dimensional door count**, telescoped: the increments of a two-colouring along a
subdivided segment sum to the sum of its two ends, because consecutive terms cancel modulo `2`.
This is the form in which an application meets `odd_card_colorChanges_iff`, and the reason a
labelling that is constant in one direction can have its door count read off the endpoints of a
side however many vertices subdivide it. -/
theorem sum_Ico_add_succ (h : p ≤ q) (c : ℕ → ZMod 2) :
    ∑ j ∈ Finset.Ico p q, (c j + c (j + 1)) = c p + c q := by
  simpa only [CharTwo.sub_eq_add, add_comm] using Finset.sum_Ico_sub c h

/-- **Sperner's lemma in dimension one.** A two-colouring of the points subdividing a segment has
an odd number of bichromatic edges exactly when its two ends are coloured differently — however
many points subdivide it. -/
theorem odd_card_colorChanges_iff (h : p ≤ q) (c : ℕ → ZMod 2) :
    Odd (colorChanges c p q).card ↔ c p ≠ c q := by
  have hite : ∀ a b : ZMod 2, (if a ≠ b then (1 : ZMod 2) else 0) = a + b := by decide +revert
  have hcard : ((colorChanges c p q).card : ZMod 2) = c p + c q := by
    simpa only [colorChanges, ← Finset.sum_boole, hite] using sum_Ico_add_succ h c
  rw [← ZMod.natCast_eq_one_iff_odd, hcard, add_eq_one_iff_ne]

end Dim1

/-! ### Dimension two -/

/-- The three labels of Sperner's lemma in dimension two. The doors are the edges labelled
`A`–`B`; `C` is the label that closes off a side. -/
inductive Color
  /-- The first of the two labels an edge needs to be a door. -/
  | A
  /-- The second of the two labels an edge needs to be a door. -/
  | B
  /-- The third label. -/
  | C
  deriving DecidableEq, Fintype

/-- The *door indicator* of an edge, read off the labels of its two endpoints: `1` when they are
`A` and `B` in some order, and `0` otherwise. -/
def door : Color → Color → ZMod 2
  | .A, .B => 1
  | .B, .A => 1
  | _, _ => 0

/-- A door is a door in either direction. -/
theorem door_comm (x y : Color) : door x y = door y x := by cases x <;> cases y <;> rfl

/-- **The local count of Sperner's lemma in dimension two.** A triangle carries an odd number of
doors on its three sides exactly when its three vertices carry three different labels. -/
theorem door_add_door_add_door_eq_one_iff (x y z : Color) :
    door x y + door y z + door z x = 1 ↔ x ≠ y ∧ y ≠ z ∧ x ≠ z := by decide +revert

/-- A triangle two of whose vertices share a label carries an even number of doors: over `ZMod 2`
there is no room between "not odd" and "even". -/
theorem door_add_door_add_door_eq_zero {x y z : Color} (h : ¬(x ≠ y ∧ y ≠ z ∧ x ≠ z)) :
    door x y + door y z + door z x = 0 := by decide +revert

end Sperner
