module

public import Mathlib.Data.Nat.Choose.Sum

/-!
# Comparator challenge: combinatorial identities

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.CombinatorialIdentities.*` is required to prove. See `README.md` for what the
Comparator check guarantees and how to run it.
-/

@[expose] public section

open Finset

/-- The hockey-stick identity for binomial coefficients. -/
def HockeyStickIdentity : Prop :=
  ∀ n k : ℕ, ∑ i ∈ range (n + 1), (i + k).choose k = (n + k + 1).choose (k + 1)

theorem HockeyStickIdentity_doubleCounting : HockeyStickIdentity := sorry

theorem HockeyStickIdentity_induction : HockeyStickIdentity := sorry
