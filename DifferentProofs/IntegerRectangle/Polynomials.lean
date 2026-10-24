module

public import DifferentProofs.IntegerRectangle.Tiling.Image
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
tiling, the translation keeps their order (`exists_monotoneOn_perturb`), so the translated tiles
tile `R'` (`IsTiling.image`) and their areas add up to that of `R'` (`IsTiling.sum_area_image`).
The area of a translated rectangle is the value at `t` of the polynomial `areaPoly`, whose
quadratic coefficient vanishes for a tile with an integer side (`areaPoly_coeff_two`), and two
polynomials agreeing on an interval are equal.

## Main result

- `IntegerRectangleTheorem_Polynomials`: Douady's polynomial proof of the integer-rectangle
  theorem.
-/

@[expose] public section

open Finset Polynomial

namespace IntegerRectangle.Polynomials

/-! ### Translating the lines of the tiling -/

/-- The indicator of the coordinates off the translate `a + ℤ` of the integer lattice. -/
noncomputable def nonLatticeIndicator (a x : ℝ) : ℝ :=
  if Int.fract (x - a) = 0 then 0 else 1

/-- The translation of the lines of the tiling by `t`: a coordinate off `a + ℤ` moves by `t`, and a
coordinate on it stays put. -/
noncomputable def perturb (a t x : ℝ) : ℝ := x + t * nonLatticeIndicator a x

private lemma nonLatticeIndicator_mem (a x : ℝ) :
    nonLatticeIndicator a x = 0 ∨ nonLatticeIndicator a x = 1 := by
  unfold nonLatticeIndicator
  split_ifs <;> simp

private lemma nonLatticeIndicator_self (a : ℝ) : nonLatticeIndicator a a = 0 := by
  simp [nonLatticeIndicator]

/-- Integer-separated coordinates have the same status with respect to every translate of `ℤ`. -/
private lemma nonLatticeIndicator_eq_of_sub_int (s : ℝ) {a b : ℝ} {n : ℤ}
    (h : b - a = n) : nonLatticeIndicator s b = nonLatticeIndicator s a :=
  congrArg (fun r ↦ if r = 0 then (0 : ℝ) else 1) (Int.fract_eq_fract.mpr ⟨n, by linarith⟩)

/-- A finite set of reals has a least gap between distinct elements. -/
private lemma exists_le_sub (s : Finset ℝ) : ∃ δ > 0, ∀ g ∈ s, ∀ g' ∈ s, g < g' → δ ≤ g' - g := by
  classical
  set D := ((s ×ˢ s).filter fun p ↦ p.1 < p.2).image fun p ↦ p.2 - p.1
  have hD {g g' : ℝ} (hg : g ∈ s) (hg' : g' ∈ s) (h : g < g') : g' - g ∈ D :=
    mem_image.mpr ⟨(g, g'), mem_filter.mpr ⟨mem_product.mpr ⟨hg, hg'⟩, h⟩, rfl⟩
  rcases D.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun g hg g' hg' h ↦ absurd (hD hg hg' h) (he ▸ notMem_empty _)⟩
  · refine ⟨D.min' hne, ?_, fun g hg g' hg' h ↦ D.min'_le _ (hD hg hg' h)⟩
    obtain ⟨p, hp, hpe⟩ := mem_image.mp (D.min'_mem hne)
    exact hpe ▸ sub_pos.mpr (mem_filter.mp hp).2

/-- **Small translations keep the order of the lines.** Below the least gap between the
coordinates of a finite set, translating some of them by `t` does not change their order. -/
theorem exists_monotoneOn_perturb (s : Finset ℝ) (a : ℝ) :
    ∃ δ > 0, ∀ t, 0 ≤ t → t < δ → MonotoneOn (perturb a t) s := by
  obtain ⟨δ, hδ, hgap⟩ := exists_le_sub s
  refine ⟨δ, hδ, fun t ht₀ ht₁ g hg g' hg' h ↦ ?_⟩
  rcases h.lt_or_eq with h | rfl
  · have := hgap g hg g' hg' h
    rcases nonLatticeIndicator_mem a g with e | e <;>
      rcases nonLatticeIndicator_mem a g' with e' | e' <;> simp only [perturb, e, e'] <;> nlinarith
  · exact le_rfl

/-- The translation keeps the points to the right of the base point to its right. -/
private lemma perturb_lt {a x t : ℝ} (h : a < x) (ht : 0 ≤ t) : perturb a t a < perturb a t x := by
  rw [perturb, perturb, nonLatticeIndicator_self, mul_zero, add_zero]
  rcases nonLatticeIndicator_mem a x with e | e <;> rw [e] <;> nlinarith

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
indicators across the two sides. -/
lemma areaPoly_coeff_two (a b : ℝ) (S : Rectangle) :
    (areaPoly a b S).coeff 2 = (nonLatticeIndicator a S.x₁ - nonLatticeIndicator a S.x₀) *
      (nonLatticeIndicator b S.y₁ - nonLatticeIndicator b S.y₀) := by
  have hexp : areaPoly a b S =
      C ((nonLatticeIndicator a S.x₁ - nonLatticeIndicator a S.x₀) *
          (nonLatticeIndicator b S.y₁ - nonLatticeIndicator b S.y₀)) * X ^ 2 +
        (C ((nonLatticeIndicator a S.x₁ - nonLatticeIndicator a S.x₀) * (S.y₁ - S.y₀) +
            (S.x₁ - S.x₀) * (nonLatticeIndicator b S.y₁ - nonLatticeIndicator b S.y₀)) * X +
          C ((S.x₁ - S.x₀) * (S.y₁ - S.y₀))) := by
    simp only [areaPoly, incPoly, map_mul, map_add, map_sub]
    ring
  rw [hexp]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

/-- **A tile with an integer side has an area linear or constant in `t`**: the two ends of a side
of integer length are translated together or not at all, so that side keeps its length. -/
lemma areaPoly_coeff_two_eq_zero (a b : ℝ) {S : Rectangle} (h : S.HasIntegerSide) :
    (areaPoly a b S).coeff 2 = 0 := by
  rw [areaPoly_coeff_two]
  rcases h with ⟨n, hw⟩ | ⟨n, hh⟩
  · rw [nonLatticeIndicator_eq_of_sub_int a (n := n) hw, sub_self, zero_mul]
  · rw [nonLatticeIndicator_eq_of_sub_int b (n := n) hh, sub_self, mul_zero]

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **The area of `R'` is the sum of the areas of its tiles, as polynomials.** For every `t` in an
interval `[0, δ)` the translated tiles tile the translated rectangle, whose area is therefore the
sum of theirs (`IsTiling.sum_area_image`), and two polynomials agreeing at infinitely many points
are equal. -/
theorem sum_areaPoly (hT : IsTiling R T) :
    ∑ i, areaPoly R.x₀ R.y₀ (T i) = areaPoly R.x₀ R.y₀ R := by
  obtain ⟨δx, hδx, hmx⟩ := exists_monotoneOn_perturb (Grid.gridX R T) R.x₀
  obtain ⟨δy, hδy, hmy⟩ := exists_monotoneOn_perturb (Grid.gridY R T) R.y₀
  have hsub : Set.Ico 0 (min δx δy) ⊆
      {t | (∑ i, areaPoly R.x₀ R.y₀ (T i)).eval t = (areaPoly R.x₀ R.y₀ R).eval t} := by
    rintro t ⟨ht₀, ht₁⟩
    simp only [Set.mem_ofPred_eq, eval_finsetSum, eval_areaPoly]
    exact hT.sum_area_image (hmx t ht₀ (ht₁.trans_le (min_le_left _ _)))
      (hmy t ht₀ (ht₁.trans_le (min_le_right _ _))) (perturb_lt hT.x₀_lt_x₁ ht₀)
      (perturb_lt hT.y₀_lt_y₁ ht₀)
  exact Polynomial.eq_of_infinite_eval_eq _ _ ((Set.Ico_infinite (lt_min hδx hδy)).mono hsub)

end IntegerRectangle.Polynomials

open IntegerRectangle IntegerRectangle.Polynomials in
/-- **Polynomial proof** (Douady) of the integer-rectangle tiling theorem. The area of each
translated tile is linear or constant in the parameter `t`, while a tiled rectangle with no
integer side would have a genuinely quadratic one; comparing `X ^ 2` coefficients in the
polynomial identity given by the additivity of area gives `0 = 1`. -/
theorem IntegerRectangleTheorem_Polynomials : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  by_contra hcon
  rw [Rectangle.HasIntegerSide, not_or] at hcon
  have hx : Int.fract (R.x₁ - R.x₀) ≠ 0 := fun h ↦
    hcon.1 ((Int.fract_eq_zero_iff.mp h).imp fun n hn ↦ hn.symm)
  have hy : Int.fract (R.y₁ - R.y₀) ≠ 0 := fun h ↦
    hcon.2 ((Int.fract_eq_zero_iff.mp h).imp fun n hn ↦ hn.symm)
  have h2 := congrArg (coeff · 2) (sum_areaPoly hT)
  simp only [finsetSum_coeff, areaPoly_coeff_two_eq_zero _ _ (hsides _), sum_const_zero,
    areaPoly_coeff_two] at h2
  simp [nonLatticeIndicator, hx, hy] at h2
