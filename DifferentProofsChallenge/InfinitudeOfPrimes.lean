module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs

/-!
# Comparator challenge: infinitude of primes

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.InfinitudeOfPrimes.*` is required to prove. See `README.md` for what the Comparator
check guarantees and how to run it.

This file imports only Mathlib, so that it can be read on its own: the definitions below are
restated from `DifferentProofs.InfinitudeOfPrimes.Defs`, and Comparator checks that the proofs use
identical ones.
-/

@[expose] public section

def InfinitudeOfPrimes : Prop := {p : ℕ | p.Prime}.Infinite

/-- Infinitely many primes in a congruence class -/
def InfinitudeOfPrimes_cong (a b : ℕ) : Prop := {p : ℕ | p.Prime ∧ p ≡ a [MOD b]}.Infinite

theorem InfinitudeOfPrimes_Euclid : InfinitudeOfPrimes := sorry

theorem InfinitudeOfPrimes_Euclid' : InfinitudeOfPrimes := sorry

theorem InfinitudeOfPrimes_Goldbach : InfinitudeOfPrimes := sorry

theorem InfinitudeOfPrimes_Euler : InfinitudeOfPrimes := sorry

theorem InfinitudeOfPrimes_Saidak : InfinitudeOfPrimes := sorry

theorem InfinitudeOfPrimes_Wunderlich : InfinitudeOfPrimes := sorry

theorem InfinitudeOfPrimes_cong_one_four : InfinitudeOfPrimes_cong 1 4 := sorry

theorem InfinitudeOfPrimes_from_one_four : InfinitudeOfPrimes := sorry

theorem InfinitudeOfPrimes_cong_three_four : InfinitudeOfPrimes_cong 3 4 := sorry

theorem InfinitudeOfPrimes_from_three_four : InfinitudeOfPrimes := sorry

theorem InfinitudeOfPrimes_Zeta : InfinitudeOfPrimes := sorry
