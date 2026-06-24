module

public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

open Finset

/-- Pascal's identity for binomial coefficients. -/
def PascalIdentity : Prop :=
  ∀ n k : ℕ, n.choose k + n.choose (k + 1) = (n + 1).choose (k + 1)

/-- The hockey-stick identity for binomial coefficients. -/
def HockeyStickIdentity : Prop :=
  ∀ n k : ℕ, ∑ i ∈ range (n + 1), (i + k).choose k = (n + k + 1).choose (k + 1)
