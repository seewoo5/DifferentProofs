module

public import DifferentProofs.IntegerRectangle.GridRefinement

/-!
# The integer-rectangle theorem via polynomials

Wagon's fifth proof, due to Adrien Douady. Fix the lattices through the lower-left corner of the
tiled rectangle. For a real parameter `t`, move every grid coordinate that lies off its lattice
by `t`, leaving lattice coordinates fixed. Algebraically, the perturbed coordinate is

```
φₜ(x) = x + t ε(x),
```

where `ε` is `0` on the lattice and `1` off it. The perturbed area of a rectangle is its f-area
for these two coordinate functions. If a tile has an integer side, the two endpoints of that side
have the same lattice status, so one factor of its perturbed area is constant in `t`; its area is
therefore affine in `t`. The f-area additivity theorem (`IsTiling.sum_fgArea`) says that the sum of
these affine functions equals the perturbed area of the tiled rectangle.

If neither side of the tiled rectangle is an integer, its lower endpoints lie on their lattices
and its upper endpoints lie off them. Its perturbed area is consequently

```
(width + t) * (height + t),
```

which is genuinely quadratic. Taking the second finite difference at `0`, `1`, and `2` gives `0`
for every tile but `2` for the tiled rectangle, a contradiction. This algebraic use of f-area
additivity encodes Wagon's auxiliary tiling while avoiding a separate proof that sufficiently
small movements of its grid lines preserve the tiling.

## Main result

- `IntegerRectangleTheorem_Polynomials`: Douady's polynomial proof of the integer-rectangle
  theorem.
-/

@[expose] public section

namespace IntegerRectangle.Polynomials

/-- The indicator of coordinates off the translate `a + ℤ` of the integer lattice. -/
private noncomputable def nonLatticeIndicator (a x : ℝ) : ℝ :=
  if Int.fract (x - a) = 0 then 0 else 1

/-- Move a coordinate off `a + ℤ` by `t`, while leaving lattice coordinates fixed. -/
private noncomputable def perturb (a t x : ℝ) : ℝ := x + t * nonLatticeIndicator a x

/-- Integer-separated coordinates have the same status with respect to every translate of `ℤ`. -/
private lemma nonLatticeIndicator_eq_of_sub_int (s : ℝ) {a b : ℝ} {n : ℤ}
    (h : b - a = n) : nonLatticeIndicator s b = nonLatticeIndicator s a := by
  have hfract : Int.fract (b - s) = Int.fract (a - s) :=
    Int.fract_eq_fract.mpr ⟨n, by
      calc
        (b - s) - (a - s) = b - a := by ring
        _ = n := h⟩
  simp only [nonLatticeIndicator, hfract]

/-- The second finite difference `F(2) - 2 F(1) + F(0)`. -/
private def secondDiff (F : ℝ → ℝ) : ℝ := F 2 - 2 * F 1 + F 0

/-- Second finite differences commute with finite sums. -/
private lemma secondDiff_sum {ι : Type*} [Fintype ι] (F : ι → ℝ → ℝ) :
    secondDiff (fun t ↦ ∑ i, F i t) = ∑ i, secondDiff (F i) := by
  classical
  simp [secondDiff, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- **Polynomial proof** (Douady) of the integer-rectangle tiling theorem. Perturb all grid lines
off the coordinate lattices by a parameter `t`. Every tile's perturbed area is affine in `t`,
whereas if the tiled rectangle had no integer side its perturbed area would have quadratic
coefficient `1`; their second finite differences cannot agree. -/
theorem IntegerRectangleTheorem_Polynomials : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  by_contra hcon
  rw [Rectangle.HasIntegerSide, not_or] at hcon
  have htile (i : ι) :
      secondDiff (fun t ↦ fgArea (perturb R.x₀ t) (perturb R.y₀ t) (T i)) = 0 := by
    rcases hsides i with ⟨n, hw⟩ | ⟨n, hh⟩
    · have hbump := nonLatticeIndicator_eq_of_sub_int R.x₀ (n := n)
        (by simpa [Rectangle.width] using hw)
      simp only [secondDiff, fgArea, perturb, hbump]
      ring
    · have hbump := nonLatticeIndicator_eq_of_sub_int R.y₀ (n := n)
        (by simpa [Rectangle.height] using hh)
      simp only [secondDiff, fgArea, perturb, hbump]
      ring
  have hadd :
      (fun t ↦ ∑ i, fgArea (perturb R.x₀ t) (perturb R.y₀ t) (T i)) =
        fun t ↦ fgArea (perturb R.x₀ t) (perturb R.y₀ t) R :=
    funext fun t ↦ hT.sum_fgArea (perturb R.x₀ t) (perturb R.y₀ t)
  have hsecond := congrArg secondDiff hadd
  rw [secondDiff_sum, Finset.sum_eq_zero fun i _ ↦ htile i] at hsecond
  have hx : Int.fract (R.x₁ - R.x₀) ≠ 0 := by
    intro hx
    have hfract : Int.fract (R.x₁ - R.x₀) = Int.fract 0 := by simpa using hx
    obtain ⟨n, hn⟩ := Int.fract_eq_fract.mp hfract
    exact hcon.1 ⟨n, by simpa [Rectangle.width] using hn⟩
  have hy : Int.fract (R.y₁ - R.y₀) ≠ 0 := by
    intro hy
    have hfract : Int.fract (R.y₁ - R.y₀) = Int.fract 0 := by simpa using hy
    obtain ⟨n, hn⟩ := Int.fract_eq_fract.mp hfract
    exact hcon.2 ⟨n, by simpa [Rectangle.height] using hn⟩
  simp [secondDiff, fgArea, perturb, nonLatticeIndicator, hx, hy] at hsecond
  nlinarith

end IntegerRectangle.Polynomials
