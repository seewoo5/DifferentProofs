module

import Architect
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

@[blueprint
  "def:inf-primes"
  (statement := /-- There are infinitely many prime numbers. -/)
  (title := "Infinitude of primes")
  (latexEnv := "definition")]
def InfinitudeOfPrimes : Prop := {p : ℕ | p.Prime}.Infinite

@[blueprint
  "def:inf-primes-large"
  (statement := /-- For any $n \in \mathbb{N}$, there exists a prime number greater than $n$. -/)
  (title := "Infinitude of primes")
  (latexEnv := "definition")]
def InfinitudeOfPrimes' : Prop := ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n
