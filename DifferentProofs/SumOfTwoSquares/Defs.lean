module

public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

/-- **Fermat's theorem on sums of two squares** (Fermat's Christmas theorem): every prime
`p` congruent to `1` modulo `4` is a sum of two squares of natural numbers. -/
def FermatSumOfTwoSquares : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p
