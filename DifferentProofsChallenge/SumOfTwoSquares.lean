module

public import Mathlib.Data.Nat.Prime.Defs

/-!
# Comparator challenge: Fermat's theorem on sums of two squares

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.SumOfTwoSquares.*` is required to prove. See `README.md` for what the Comparator
check guarantees and how to run it.

This file imports only Mathlib, so that it can be read on its own: the definition below is restated
from `DifferentProofs.SumOfTwoSquares.Defs`, and Comparator checks that the proofs use an identical
one.
-/

@[expose] public section

/-- **Fermat's theorem on sums of two squares**: Every prime `p` congruent to `1` modulo `4`
is a sum of two squares of natural numbers. -/
def FermatSumOfTwoSquares : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p

theorem FermatSumOfTwoSquares_QuadraticReciprocity : FermatSumOfTwoSquares := sorry

theorem FermatSumOfTwoSquares_Wilson : FermatSumOfTwoSquares := sorry

theorem FermatSumOfTwoSquares_Zagier : FermatSumOfTwoSquares := sorry

theorem FermatSumOfTwoSquares_Jacobi : FermatSumOfTwoSquares := sorry
