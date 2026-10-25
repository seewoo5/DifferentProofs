module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Comparator challenge: Fermat's little theorem

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.FermatLittleTheorem.*` is required to prove. See `README.md` for what the
Comparator check guarantees and how to run it.

This file imports only Mathlib, so that it can be read on its own: the definition below is restated
from `DifferentProofs.FermatLittleTheorem.Defs`, and Comparator checks that the proofs use an
identical one.
-/

@[expose] public section

def FermatLittleTheorem : Prop := ∀ p : ℕ, ∀ a : ℤ, p.Prime → a ^ p ≡ a [ZMOD p]

theorem FermatLittleTheorem_Binomial : FermatLittleTheorem := sorry

theorem FermatLittleTheorem_Alkauskas : FermatLittleTheorem := sorry

theorem FermatLittleTheorem_Lagrange : FermatLittleTheorem := sorry

theorem FermatLittleTheorem_Dynamical : FermatLittleTheorem := sorry
