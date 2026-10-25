module

public import Mathlib.Data.Nat.Choose.Sum

/-!
# Comparator challenge: combinatorial identities

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.CombinatorialIdentities.*` is required to prove. See `README.md` for what the
Comparator check guarantees and how to run it.

This file imports only Mathlib, so that it can be read on its own: the definitions below are
restated from `DifferentProofs.CombinatorialIdentities.Defs`, and Comparator checks that the proofs
use identical ones.
-/

@[expose] public section

open Finset

/-- Pascal's identity for binomial coefficients. -/
def PascalIdentity : Prop :=
  ∀ n k : ℕ, n.choose k + n.choose (k + 1) = (n + 1).choose (k + 1)

/-- The hockey-stick identity for binomial coefficients. -/
def HockeyStickIdentity : Prop :=
  ∀ n k : ℕ, ∑ i ∈ range (n + 1), (i + k).choose k = (n + k + 1).choose (k + 1)

theorem PascalIdentity_counting : PascalIdentity := sorry

theorem PascalIdentity_binomial : PascalIdentity := sorry

theorem HockeyStickIdentity_doubleCounting : HockeyStickIdentity := sorry

theorem HockeyStickIdentity_induction : HockeyStickIdentity := sorry
