module

public import DifferentProofs.IntegerRectangle.GridRefinement

/-!
# The integer-rectangle theorem by a minimal cut-set

Wagon's eleventh proof, due to Paul Seymour. Call a tile an *H-tile* when its width is an integer
and a *V-tile* when its height is one; by hypothesis every tile is at least one of the two.
Seymour forms a graph `Γ` whose vertices are the horizontal segments of the tiling and whose edges
are the tiles, each joining the segment carrying its bottom edge to the one carrying its top edge,
together with one extra edge running around the outside of `R` from its base to its top. Let `S`
be the set of edges of `Γ` coming from H-tiles, together with that outer edge. Either `S` fails to
separate the base of `R` from its top — and then a path avoiding `S` runs from base to top across
V-tiles alone, whose heights are integers and telescope to the height of `R` — or it separates
them, and Seymour takes a *minimal* cut `S' ⊆ S`. The dual of a minimal cut in a planar graph is a
cycle; that cycle has to use the dual of the outer edge, so deleting it leaves a path across the
dual graph from the left edge of `R` to its right edge whose steps are widths of H-tiles, and
those telescope to the width of `R`.

Planar duality is what carries the second half of that argument, and mathlib has none of it. This
formalization keeps the cut and drops the duality.

A vertex is recorded by its height alone: `VReach` is the set of heights reachable from the base
of `R` by stepping across a V-tile, in either direction. This merges horizontal segments sitting
at a common height, which can only make the base and the top easier to connect, so the dichotomy
proved below is weaker than Seymour's — and still enough. The dual half is its mirror image,
`HReach`, the abscissae reachable from the left edge of `R` across H-tiles; transposing the plane
exchanges the two, so nothing horizontal is defined or proved separately.

What replaces the theorem on planar duality is the fg-area (`IsTiling.sum_fgArea`), the
bookkeeping identity this file shares with the step-function proof. Give the horizontal axis the
indicator of `HReach` and the vertical axis the indicator of `VReach`. Both vertical edges of an
H-tile are reachable or neither is, so its horizontal increment vanishes; both horizontal edges of
a V-tile are reachable or neither is, so its vertical increment vanishes; every tile is an H-tile
or a V-tile, so every tile has fg-area `0`. Were the top of `R` unreachable and its right edge
unreachable too, `R` itself would have fg-area `(0 - 1)(0 - 1) = 1`, contradicting additivity.
Hence one of the two is reachable — and reachability proceeds by integer steps.
-/

@[expose] public section

namespace IntegerRectangle.CutSet

variable {ι : Type} {R : Rectangle} {T : ι → Rectangle} {i : ι}

/-! ### Reachability across the tiles designated by their integer height -/

/-- A **V-step** joins the two heights of a tile of integer height, in either direction. These are
the edges of Seymour's graph `Γ` that survive the removal of the cut `S`, recorded by the heights
of their endpoints rather than by the horizontal segments sitting at those heights. -/
def VStep (T : ι → Rectangle) (a b : ℝ) : Prop :=
  ∃ i, (∃ m : ℤ, (T i).height = m) ∧
    (((T i).y₀ = a ∧ (T i).y₁ = b) ∨ ((T i).y₀ = b ∧ (T i).y₁ = a))

/-- The heights reachable from the base of `R` by V-steps: the vertices of `Γ` left on the base's
side once the cut `S` is removed. -/
def VReach (R : Rectangle) (T : ι → Rectangle) : Set ℝ :=
  {y | Relation.ReflTransGen (VStep T) R.y₀ y}

/-- The abscissae reachable from the left edge of `R` across tiles of integer width — the mirror
image of `VReach` in the diagonal, and the trace of Seymour's dual path. -/
def HReach (R : Rectangle) (T : ι → Rectangle) : Set ℝ :=
  VReach R.transpose fun i ↦ (T i).transpose

/-- The base of `R` is reachable from itself. -/
lemma y₀_mem_VReach : R.y₀ ∈ VReach R T := Relation.ReflTransGen.refl

/-- The left edge of `R` is reachable from itself. -/
lemma x₀_mem_HReach : R.x₀ ∈ HReach R T := y₀_mem_VReach

/-- **Reachability proceeds by integer steps.** A height reachable from the base of `R` sits an
integer distance above it, because each V-step crosses a tile of integer height. -/
lemma int_sub_y₀_of_mem_VReach {y : ℝ} (h : y ∈ VReach R T) : ∃ m : ℤ, y - R.y₀ = m := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | tail _ hstep ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨i, ⟨n, hn⟩, hcase⟩ := hstep
    rw [Rectangle.height] at hn
    rcases hcase with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · exact ⟨m + n, by push_cast; linarith⟩
    · exact ⟨m - n, by push_cast; linarith⟩

/-- An abscissa reachable from the left edge of `R` sits an integer distance to its right. -/
lemma int_sub_x₀_of_mem_HReach {x : ℝ} (h : x ∈ HReach R T) : ∃ m : ℤ, x - R.x₀ = m :=
  int_sub_y₀_of_mem_VReach h

/-- **A tile of integer height does not straddle the cut.** Its two heights are joined by a
V-step, so each is reachable exactly when the other is. -/
lemma mem_VReach_iff_of_intHeight (h : ∃ m : ℤ, (T i).height = m) :
    (T i).y₀ ∈ VReach R T ↔ (T i).y₁ ∈ VReach R T :=
  ⟨fun hy ↦ hy.tail ⟨i, h, .inl ⟨rfl, rfl⟩⟩, fun hy ↦ hy.tail ⟨i, h, .inr ⟨rfl, rfl⟩⟩⟩

/-- A tile of integer width has each of its vertical edges reachable exactly when the other is. -/
lemma mem_HReach_iff_of_intWidth (h : ∃ m : ℤ, (T i).width = m) :
    (T i).x₀ ∈ HReach R T ↔ (T i).x₁ ∈ HReach R T :=
  mem_VReach_iff_of_intHeight (T := fun i ↦ (T i).transpose) (R := R.transpose) h

/-! ### The cut-set dichotomy -/

/-- The indicator of a set of reals. The indicators of `HReach` and of `VReach` are the two
functions fed to the fg-area below: `HReach` and `VReach` play the role of Seymour's cut and of
its dual, and a set that no tile straddles has constant indicator across that tile. -/
private noncomputable def ind (S : Set ℝ) : ℝ → ℝ := S.indicator fun _ ↦ 1

private lemma ind_of_mem {S : Set ℝ} {a : ℝ} (h : a ∈ S) : ind S a = 1 :=
  Set.indicator_of_mem h _

private lemma ind_of_notMem {S : Set ℝ} {a : ℝ} (h : a ∉ S) : ind S a = 0 :=
  Set.indicator_of_notMem h _

/-- A set that contains one of two reals exactly when it contains the other has vanishing
indicator increment across them. -/
private lemma ind_sub_eq_zero {S : Set ℝ} {a b : ℝ} (h : a ∈ S ↔ b ∈ S) :
    ind S b - ind S a = 0 := by
  by_cases hb : b ∈ S
  · rw [ind_of_mem hb, ind_of_mem (h.mpr hb), sub_self]
  · rw [ind_of_notMem hb, ind_of_notMem (h.not.mpr hb), sub_self]

variable [Fintype ι]

/-- **Seymour's dichotomy.** Either the top of `R` is reachable from its base across tiles of
integer height, or the right edge of `R` is reachable from its left edge across tiles of integer
width. Seymour reads the second alternative off the first by planar duality; here it is the
fg-area of the pair of indicators that does the bookkeeping. Every tile has fg-area `0`, since a
tile of integer width has constant `HReach`-indicator across its width and a tile of integer
height has constant `VReach`-indicator across its height; so `R` has fg-area `0` too, whereas
failure of both alternatives would give it fg-area `(0 - 1)(0 - 1) = 1`. -/
theorem y₁_mem_VReach_or_x₁_mem_HReach (hT : IsTiling R T)
    (hsides : ∀ i, (T i).HasIntegerSide) : R.y₁ ∈ VReach R T ∨ R.x₁ ∈ HReach R T := by
  by_contra hcon
  push Not at hcon
  have key : fgArea (ind (HReach R T)) (ind (VReach R T)) R = 0 :=
    (hT.sum_fgArea _ _).symm.trans <| Finset.sum_eq_zero fun i _ ↦ mul_eq_zero.mpr <|
      (hsides i).imp (fun h ↦ ind_sub_eq_zero (mem_HReach_iff_of_intWidth h))
        fun h ↦ ind_sub_eq_zero (mem_VReach_iff_of_intHeight h)
  rw [fgArea, ind_of_notMem hcon.2, ind_of_mem x₀_mem_HReach, ind_of_notMem hcon.1,
    ind_of_mem y₀_mem_VReach] at key
  norm_num at key

end IntegerRectangle.CutSet

open IntegerRectangle IntegerRectangle.CutSet in
/-- **Minimal cut-set proof** (Seymour) of the integer-rectangle tiling theorem: the tiles of
integer height either connect the base of `R` to its top, or are cut off from the top by a set of
tiles of integer width that connects the left edge of `R` to its right edge. -/
theorem IntegerRectangleTheorem_CutSet : IntegerRectangleTheorem := fun _ _ hT hsides ↦
  (y₁_mem_VReach_or_x₁_mem_HReach hT hsides).symm.imp int_sub_x₀_of_mem_HReach
    int_sub_y₀_of_mem_VReach
