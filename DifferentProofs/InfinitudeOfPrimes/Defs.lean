module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

def InfinitudeOfPrimes : Prop := {p : ℕ | p.Prime}.Infinite

def InfinitudeOfPrimes' : Prop := ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n
