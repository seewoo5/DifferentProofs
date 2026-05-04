module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

def FermatLittleTheorem : Prop := ∀ p : ℕ, ∀ a : ℤ, p.Prime → a ^ p ≡ a [ZMOD p]

def FermatLittleTheoremNat : Prop := ∀ p : ℕ, ∀ a : ℕ, p.Prime → a ^ p ≡ a [MOD p]
