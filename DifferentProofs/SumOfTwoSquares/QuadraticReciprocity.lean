module

public import DifferentProofs.SumOfTwoSquares.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Sum of two squares via quadratic reciprocity

The first supplement to quadratic reciprocity (equivalently, Euler's criterion applied to the
quartic character `χ₄`) says that `-1` is a square modulo an odd prime `p` exactly when
`p ≢ 3 (mod 4)`. For `p ≡ 1 (mod 4)` this hypothesis holds, and the shared descent
`sq_add_sq_of_isSquare_neg_one` turns it into a representation `p = a² + b²`.
-/

@[expose] public section

theorem FermatSumOfTwoSquares_QuadraticReciprocity : FermatSumOfTwoSquares := by
  intro p hp hp4
  have : Fact p.Prime := ⟨hp⟩
  refine sq_add_sq_of_isSquare_neg_one hp ?_
  rw [ZMod.exists_sq_eq_neg_one_iff]
  omega
