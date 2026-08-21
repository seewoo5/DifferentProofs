module

public import DifferentProofs.IntegerRectangle.GridRefinement
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The integer-rectangle theorem via polynomials

Wagon's fifth proof, due to Adrien Douady. Fix the lattices through the lower-left corner of the
tiled rectangle. For a real parameter `t`, move every grid coordinate that lies off its lattice
by `t`, leaving lattice coordinates fixed. Algebraically, the perturbed coordinate is

```
φₜ(x) = x + t ε(x),
```

where `ε` is `0` on the lattice and `1` off it. The perturbed area of a rectangle is its fg-area
for these two coordinate functions, and as a function of `t` it is a genuine polynomial

```
areaPoly S = ((ε x₁ - ε x₀) X + (x₁ - x₀)) * ((ε y₁ - ε y₀) X + (y₁ - y₀))
```

whose quadratic coefficient is the fg-area of the indicator pair (`areaPoly_coeff_two`). If a
tile has an integer side, the two endpoints of that side have the same lattice status, so the
corresponding factor is constant and the quadratic coefficient vanishes: the tile's perturbed
area is linear or constant in `t`, exactly as in Wagon's text. The fg-area additivity theorem
(`IsTiling.sum_fgArea`) equates the sum of the tile polynomials with the polynomial of the tiled
rectangle at every real `t` — Wagon confines `t` to a small interval `[0, ε]` so that the moved
segments still bound a genuine tiling, but the algebraic identity needs no such restriction —
and `Polynomial.funext` upgrades the evaluation identity to an identity of polynomials. If
neither side of the tiled rectangle is an integer, its lower endpoints lie on their lattices and
its upper endpoints off them, so its quadratic coefficient is `1`; comparing `X ^ 2`-coefficients
yields `0 = 1`. This algebraic use of fg-area additivity encodes Wagon's auxiliary tiling while
avoiding a separate proof that sufficiently small movements of its grid lines preserve the
tiling.

A polynomial-free finitary shortcut, recorded here for reference after serving as this file's
original proof: each tile's perturbed area is affine in `t`, so its second finite difference
`F 2 - 2 * F 1 + F 0` vanishes, while a tiled rectangle with no integer side has perturbed area
`(width + t) * (height + t)`, whose second finite difference is `2`; applying the second finite
difference to the additivity identity evaluated at `t = 0, 1, 2` yields `0 = 2` with no
`Polynomial` API. Both routes extract the same number — the second finite difference is twice
the quadratic coefficient, namely `2 * fgArea ε ε S` — so either way the argument specializes to
the fg-area dichotomy (`StepFunction.dichotomy`) at the indicator pair; the parameter `t` is
Douady's geometric packaging of that instance.

For the record, the shortcut shared `nonLatticeIndicator`, `perturb`, and
`nonLatticeIndicator_eq_of_sub_int` with the present proof, and the rest of it read:

```
/-- The second finite difference `F(2) - 2 F(1) + F(0)`. -/
private def secondDiff (F : ℝ → ℝ) : ℝ := F 2 - 2 * F 1 + F 0

/-- Second finite differences commute with finite sums. -/
private lemma secondDiff_sum {ι : Type*} [Fintype ι] (F : ι → ℝ → ℝ) :
    secondDiff (fun t ↦ ∑ i, F i t) = ∑ i, secondDiff (F i) := by
  simp [secondDiff, Finset.sum_add_distrib, Finset.mul_sum]

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
  have hsecond :=
    congrArg secondDiff (funext fun t ↦ hT.sum_fgArea (perturb R.x₀ t) (perturb R.y₀ t))
  rw [secondDiff_sum, Finset.sum_eq_zero fun i _ ↦ htile i] at hsecond
  have hx : Int.fract (R.x₁ - R.x₀) ≠ 0 := fun h ↦
    hcon.1 ((Int.fract_eq_zero_iff.mp h).imp fun n hn ↦ hn.symm)
  have hy : Int.fract (R.y₁ - R.y₀) ≠ 0 := fun h ↦
    hcon.2 ((Int.fract_eq_zero_iff.mp h).imp fun n hn ↦ hn.symm)
  simp only [secondDiff, fgArea, perturb, nonLatticeIndicator, hx, ↓reduceIte, mul_one, sub_self,
    Int.fract_zero, mul_zero, add_zero, hy] at hsecond
  linarith
```

## Main result

- `IntegerRectangleTheorem_Polynomials`: Douady's polynomial proof of the integer-rectangle
  theorem.
-/

@[expose] public section

open Polynomial

namespace IntegerRectangle.Polynomials

/-- The indicator of coordinates off the translate `a + ℤ` of the integer lattice. -/
private noncomputable def nonLatticeIndicator (a x : ℝ) : ℝ :=
  if Int.fract (x - a) = 0 then 0 else 1

/-- Move a coordinate off `a + ℤ` by `t`, while leaving lattice coordinates fixed. -/
private noncomputable def perturb (a t x : ℝ) : ℝ := x + t * nonLatticeIndicator a x

/-- Integer-separated coordinates have the same status with respect to every translate of `ℤ`. -/
private lemma nonLatticeIndicator_eq_of_sub_int (s : ℝ) {a b : ℝ} {n : ℤ}
    (h : b - a = n) : nonLatticeIndicator s b = nonLatticeIndicator s a :=
  congrArg (fun r ↦ if r = 0 then (0 : ℝ) else 1) (Int.fract_eq_fract.mpr ⟨n, by linarith⟩)

/-- The perturbed increment of a coordinate across `[u, v]`, as a polynomial in the perturbation
parameter: `(ε(v) - ε(u)) X + (v - u)`. -/
private noncomputable def incPoly (a u v : ℝ) : ℝ[X] :=
  C (nonLatticeIndicator a v - nonLatticeIndicator a u) * X + C (v - u)

/-- The perturbed area of a rectangle, as a polynomial in the perturbation parameter. -/
private noncomputable def areaPoly (a b : ℝ) (S : Rectangle) : ℝ[X] :=
  incPoly a S.x₀ S.x₁ * incPoly b S.y₀ S.y₁

/-- Evaluating the perturbed-area polynomial at `t` recovers the fg-area of the perturbed
coordinates. -/
private lemma eval_areaPoly (a b t : ℝ) (S : Rectangle) :
    (areaPoly a b S).eval t = fgArea (perturb a t) (perturb b t) S := by
  simp only [areaPoly, incPoly, fgArea, perturb, eval_mul, eval_add, eval_C, eval_X]
  ring

/-- The quadratic coefficient of the perturbed-area polynomial is the fg-area of the pair of
off-lattice indicators. -/
private lemma areaPoly_coeff_two (a b : ℝ) (S : Rectangle) :
    (areaPoly a b S).coeff 2 = fgArea (nonLatticeIndicator a) (nonLatticeIndicator b) S := by
  have hexp : areaPoly a b S =
      C (fgArea (nonLatticeIndicator a) (nonLatticeIndicator b) S) * X ^ 2 +
        (C ((nonLatticeIndicator a S.x₁ - nonLatticeIndicator a S.x₀) * (S.y₁ - S.y₀) +
            (S.x₁ - S.x₀) * (nonLatticeIndicator b S.y₁ - nonLatticeIndicator b S.y₀)) * X +
          C ((S.x₁ - S.x₀) * (S.y₁ - S.y₀))) := by
    simp only [areaPoly, incPoly, fgArea, map_mul, map_add, map_sub]
    ring
  rw [hexp]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

end IntegerRectangle.Polynomials

open IntegerRectangle IntegerRectangle.Polynomials in
/-- **Polynomial proof** (Douady) of the integer-rectangle tiling theorem. The perturbed area of
each tile is a polynomial that is linear or constant in the perturbation parameter, while a
tiled rectangle with no integer side would have a genuinely quadratic one; comparing `X ^ 2`
coefficients in the polynomial identity supplied by fg-area additivity gives `0 = 1`. -/
theorem IntegerRectangleTheorem_Polynomials : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  by_contra hcon
  rw [Rectangle.HasIntegerSide, not_or] at hcon
  have htile (i : ι) : (areaPoly R.x₀ R.y₀ (T i)).coeff 2 = 0 := by
    rw [areaPoly_coeff_two, fgArea]
    rcases hsides i with ⟨n, hw⟩ | ⟨n, hh⟩
    · have hbump := nonLatticeIndicator_eq_of_sub_int R.x₀ (n := n)
        (by simpa [Rectangle.width] using hw)
      rw [hbump, sub_self, zero_mul]
    · have hbump := nonLatticeIndicator_eq_of_sub_int R.y₀ (n := n)
        (by simpa [Rectangle.height] using hh)
      rw [hbump, sub_self, mul_zero]
  have hsum : ∑ i, areaPoly R.x₀ R.y₀ (T i) = areaPoly R.x₀ R.y₀ R :=
    Polynomial.funext fun t ↦ by
      simpa only [eval_finsetSum, eval_areaPoly] using
        hT.sum_fgArea (perturb R.x₀ t) (perturb R.y₀ t)
  have hx : Int.fract (R.x₁ - R.x₀) ≠ 0 := fun h ↦
    hcon.1 ((Int.fract_eq_zero_iff.mp h).imp fun n hn ↦ hn.symm)
  have hy : Int.fract (R.y₁ - R.y₀) ≠ 0 := fun h ↦
    hcon.2 ((Int.fract_eq_zero_iff.mp h).imp fun n hn ↦ hn.symm)
  have h2 : (0 : ℝ) = fgArea (nonLatticeIndicator R.x₀) (nonLatticeIndicator R.y₀) R := by
    rw [← areaPoly_coeff_two, ← hsum, finsetSum_coeff]
    exact (Finset.sum_eq_zero fun i _ ↦ htile i).symm
  simp [fgArea, nonLatticeIndicator, hx, hy] at h2
