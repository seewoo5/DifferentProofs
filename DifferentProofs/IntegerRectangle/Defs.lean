module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Set.Prod

/-!
# The integer-rectangle tiling theorem: statement

We formalize the result of Stan Wagon, *Fourteen Proofs of a Result About Tiling a Rectangle*
(Amer. Math. Monthly **94** (1987), 601–617):

> Whenever a rectangle is tiled by rectangles each of which has at least one integer side, then
> the tiled rectangle has at least one integer side.

Following Wagon, a *tiling* of a rectangle is a covering by finitely many axis-parallel
rectangles with pairwise-disjoint interiors. We model an axis-parallel rectangle by its
lower-left and upper-right corners (`Rectangle`), read off its planar point set (`Rectangle.toSet`),
and record the tiling hypothesis in `IsTiling`. The theorem to be proved is
`IntegerRectangleTheorem`.
-/

@[expose] public section

namespace IntegerRectangle

/-- An axis-parallel closed rectangle `[x₀, x₁] × [y₀, y₁]` in the plane, encoded by its
lower-left corner `(x₀, y₀)` and upper-right corner `(x₁, y₁)`. -/
structure Rectangle where
  /-- Left edge. -/
  x₀ : ℝ
  /-- Right edge. -/
  x₁ : ℝ
  /-- Bottom edge. -/
  y₀ : ℝ
  /-- Top edge. -/
  y₁ : ℝ
  /-- The left edge is not to the right of the right edge. -/
  hx : x₀ ≤ x₁
  /-- The bottom edge is not above the top edge. -/
  hy : y₀ ≤ y₁

namespace Rectangle

/-- The set of points of the plane covered by the rectangle. -/
def toSet (R : Rectangle) : Set (ℝ × ℝ) := Set.Icc R.x₀ R.x₁ ×ˢ Set.Icc R.y₀ R.y₁

/-- The horizontal dimension of the rectangle. -/
def width (R : Rectangle) : ℝ := R.x₁ - R.x₀

/-- The vertical dimension of the rectangle. -/
def height (R : Rectangle) : ℝ := R.y₁ - R.y₀

/-- A rectangle *has an integer side* when its width or its height is an integer. -/
def HasIntegerSide (R : Rectangle) : Prop :=
  (∃ n : ℤ, R.width = n) ∨ (∃ n : ℤ, R.height = n)

end Rectangle

/-- `IsTiling R T` says that the finite family of rectangles `T` tiles the rectangle `R`: the
tiles cover `R` and have pairwise-disjoint interiors. This is Wagon's notion of a tiling, "a
covering with interior pairwise-disjoint sets". -/
structure IsTiling {ι : Type*} [Fintype ι] (R : Rectangle) (T : ι → Rectangle) : Prop where
  /-- The tiles cover the ambient rectangle exactly. -/
  cover : R.toSet = ⋃ i, (T i).toSet
  /-- Distinct tiles have disjoint interiors. -/
  interiorDisjoint :
    Pairwise fun i j ↦ Disjoint (interior (T i).toSet) (interior (T j).toSet)

/-- **The integer-rectangle tiling theorem** (Wagon). If a rectangle is tiled by finitely many
rectangles, each having at least one integer side, then the tiled rectangle has at least one
integer side. -/
def IntegerRectangleTheorem : Prop :=
  ∀ {ι : Type*} [Fintype ι] (R : Rectangle) (T : ι → Rectangle),
    IsTiling R T → (∀ i, (T i).HasIntegerSide) → R.HasIntegerSide

end IntegerRectangle
