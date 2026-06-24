module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs

@[expose] public section

def InfinitudeOfPrimes : Prop := {p : ℕ | p.Prime}.Infinite

def InfinitudeOfPrimes' : Prop := ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n

/-- Infinitely many primes in a congruence class -/
def InfinitudeOfPrimes_cong (a b : ℕ) : Prop := {p : ℕ | p.Prime ∧ p ≡ a [MOD b]}.Infinite

def InfinitudeOfPrimes_cong' (a b : ℕ) : Prop := ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD b] ∧ p > n
