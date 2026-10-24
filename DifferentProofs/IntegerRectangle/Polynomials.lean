module

public import DifferentProofs.IntegerRectangle.Tiling.Image
public import Mathlib.Algebra.Order.Field.Pi
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The integer-rectangle theorem via polynomials

Wagon's fifth proof, due to Adrien Douady. Place `R` in standard position and build an auxiliary
tiling in a way similar to the preceding proof, now with a parameter `t`: translate only the
lines of the tiling having a noninteger coordinate, the vertical ones from `x = a` to `x = a + t`
and the horizontal ones from `y = b` to `y = b + t`. For `t` in a sufficiently small interval
`[0, ε]` this gives a tiling of a rectangle `R'`, with as many tiles as `R`. If neither side of
`R` is an integer, `R'` is an `(a + t) × (b + t)` rectangle, so its area is a quadratic
polynomial in `t`. But a `w × h` tile with an integer side becomes a tile of one of the forms
`w × (h ± t)`, `(w ± t) × h` or `w × h`, whose area is a linear or constant function of `t`, and
hence so is the area of `R'`. Since `t` can take any value in an interval, this contradicts the
quadratic representation of the area.

The lattice is the one through the lower-left corner of `R` instead of the integer lattice, which
replaces the standard position, and the translation is `perturb a t`, which moves `x` by `t` when
`x - a` is not an integer. While `t` is smaller than the least gap between the lines of the
tiling, the translation keeps their order (`exists_strictMonoOn_perturb`), so the translated tiles
tile `R'` (`IsTiling.image`) and their areas add up to that of `R'` (`IsTiling.sum_area_image`).
The area of a translated rectangle is the value at `t` of the polynomial `areaPoly`
(`eval_areaPoly`), whose quadratic coefficient vanishes for a tile with an integer side
(`areaPoly_coeff_two_eq_zero`), and two polynomials agreeing on an interval are equal
(`sum_areaPoly`).

## Main result

- `IntegerRectangleTheorem_Polynomials`: Douady's polynomial proof of the integer-rectangle
  theorem.
-/

@[expose] public section

open Finset Polynomial

namespace IntegerRectangle.Polynomials

/-! ### Translating the lines of the tiling -/

/-- The indicator of the coordinates off the translate `a + ℤ` of the integer lattice. -/
noncomputable def nonLatticeIndicator (a x : ℝ) : ℝ := if Int.fract (x - a) = 0 then 0 else 1

/-- The translation of the lines of the tiling by `t`: a coordinate off `a + ℤ` moves by `t`, and a
coordinate on it stays put. -/
noncomputable def perturb (a t x : ℝ) : ℝ := x + t * nonLatticeIndicator a x

/-- Integer-separated coordinates have the same status with respect to every translate of `ℤ`. -/
private lemma nonLatticeIndicator_eq_of_sub_int (s : ℝ) {a b : ℝ} {n : ℤ} (h : b - a = n) :
    nonLatticeIndicator s b = nonLatticeIndicator s a :=
  congrArg (fun r ↦ if r = 0 then (0 : ℝ) else 1) (Int.fract_eq_fract.mpr ⟨n, by linarith⟩)

/-- **Small translations keep the order of the lines.** Below the least gap between the
coordinates of a finite set, translating some of them by `t` keeps them in strictly increasing
order, so that no tile collapses — Wagon's tiling "with the same number of tiles as in `R`": the
pairs `g < g'` of the set, finitely many, have a common `δ > 0` with `g + δ < g'`, and every
coordinate moves right by `0` or by `t < δ`. -/
theorem exists_strictMonoOn_perturb (s : Finset ℝ) (a : ℝ) :
    ∃ δ > 0, ∀ t, 0 ≤ t → t < δ → StrictMonoOn (perturb a t) s := by
  obtain ⟨δ, hδ, hgap⟩ := Pi.exists_forall_pos_add_lt fun p : {p : s × s // (p.1 : ℝ) < p.2} ↦ p.2
  refine ⟨δ, hδ, fun t ht₀ ht₁ g hg g' hg' h ↦ ?_⟩
  unfold perturb nonLatticeIndicator
  split_ifs <;> linarith [hgap ⟨(⟨g, hg⟩, ⟨g', hg'⟩), h⟩]

/-! ### The areas as polynomials -/

/-- The increment of a translated coordinate across `[u, v]`, as a polynomial in `t`:
`(ε(v) - ε(u)) X + (v - u)`. -/
noncomputable def incPoly (a u v : ℝ) : ℝ[X] :=
  C (nonLatticeIndicator a v - nonLatticeIndicator a u) * X + C (v - u)

/-- The area of a translated rectangle, as a polynomial in `t`. -/
noncomputable def areaPoly (a b : ℝ) (S : Rectangle) : ℝ[X] :=
  incPoly a S.x₀ S.x₁ * incPoly b S.y₀ S.y₁

/-- Evaluating the area polynomial at `t` gives the area of the rectangle translated by `t`. -/
lemma eval_areaPoly (a b t : ℝ) (S : Rectangle) :
    (areaPoly a b S).eval t =
      (perturb a t S.x₁ - perturb a t S.x₀) * (perturb b t S.y₁ - perturb b t S.y₀) := by
  simp only [areaPoly, incPoly, perturb, eval_mul, eval_add, eval_C, eval_X]
  ring

/-- The quadratic coefficient of the area polynomial is the product of the increments of the
indicators across the two sides, the leading coefficients of its two linear factors. -/
lemma areaPoly_coeff_two (a b : ℝ) (S : Rectangle) :
    (areaPoly a b S).coeff 2 = (nonLatticeIndicator a S.x₁ - nonLatticeIndicator a S.x₀) *
      (nonLatticeIndicator b S.y₁ - nonLatticeIndicator b S.y₀) :=
  (coeff_mul_add_eq_of_natDegree_le natDegree_linear_le natDegree_linear_le).trans <| by
    simp only [coeff_add, coeff_mul_X, coeff_C_zero, coeff_C_succ, add_zero]

/-- **A tile with an integer side has an area linear or constant in `t`**: the two ends of a side
of integer length are translated together or not at all, so that side keeps its length. -/
lemma areaPoly_coeff_two_eq_zero (a b : ℝ) {S : Rectangle} (h : S.HasIntegerSide) :
    (areaPoly a b S).coeff 2 = 0 := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> simp only [areaPoly_coeff_two,
    nonLatticeIndicator_eq_of_sub_int _ h, sub_self, zero_mul, mul_zero]

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **The area of `R'` is the sum of the areas of its tiles, as polynomials.** For every `t` in an
interval `[0, δ)` the translated tiles tile the translated rectangle, whose area is therefore the
sum of theirs (`IsTiling.sum_area_image`), and two polynomials agreeing at infinitely many points
are equal. -/
theorem sum_areaPoly (hT : IsTiling R T) :
    ∑ i, areaPoly R.x₀ R.y₀ (T i) = areaPoly R.x₀ R.y₀ R := by
  obtain ⟨δx, hδx, hmx⟩ := exists_strictMonoOn_perturb (Grid.gridX R T) R.x₀
  obtain ⟨δy, hδy, hmy⟩ := exists_strictMonoOn_perturb (Grid.gridY R T) R.y₀
  refine eq_of_infinite_eval_eq _ _ <| (Set.Ico_infinite (lt_min hδx hδy)).mono fun t ht ↦ ?_
  have hx := hmx t ht.1 (lt_min_iff.1 ht.2).1
  have hy := hmy t ht.1 (lt_min_iff.1 ht.2).2
  simpa only [eval_finsetSum, eval_areaPoly, Set.mem_ofPred_eq] using hT.sum_area_image
    hx.monotoneOn hy.monotoneOn (hx Grid.left_mem_gridX Grid.right_mem_gridX hT.x₀_lt_x₁)
    (hy Grid.bot_mem_gridY Grid.top_mem_gridY hT.y₀_lt_y₁)

end IntegerRectangle.Polynomials

open IntegerRectangle IntegerRectangle.Polynomials in
/-- **Polynomial proof** (Douady) of the integer-rectangle tiling theorem. The area of each
translated tile is linear or constant in the parameter `t`, while a tiled rectangle with no
integer side would have a genuinely quadratic one; comparing `X ^ 2` coefficients in the
polynomial identity given by the additivity of area gives `0 = 1`. -/
theorem IntegerRectangleTheorem_Polynomials : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  by_contra h
  simp only [Rectangle.HasIntegerSide, Rectangle.width, Rectangle.height, not_or, not_exists] at h
  simpa only [finsetSum_coeff, areaPoly_coeff_two_eq_zero _ _ (hsides _), sum_const_zero,
    areaPoly_coeff_two, nonLatticeIndicator, Int.fract_eq_iff, Std.le_refl, zero_lt_one, sub_zero,
    h, exists_const, and_false, ↓reduceIte, sub_self, Int.fract_zero, mul_one, zero_ne_one] using
    congrArg (coeff · 2) (sum_areaPoly hT)
