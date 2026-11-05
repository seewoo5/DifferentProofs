module

public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

open Finset

/-- The hockey-stick identity for binomial coefficients. -/
def HockeyStickIdentity : Prop :=
  ∀ n k : ℕ, ∑ i ∈ range (n + 1), (i + k).choose k = (n + k + 1).choose (k + 1)
