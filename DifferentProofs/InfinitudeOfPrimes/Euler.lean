module

import Architect
public import DifferentProofs.InfinitudeOfPrimes.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Harmonic.Defs

@[expose] public section


@[blueprint
  "thm:harmonic-unbounded"
  (statement := /-- The harmonic series is unbounded. -/)
  (hasProof := true)
  (proof := /-- Use the inequality $\log(n + 1) \le H_n$ (`log_add_one_le_harmonic`). -/)
  (title := "Harmonic series is unbounded")
  (latexEnv := "theorem")]
theorem harmonic_unbounded : ∀ M : ℝ, ∃ n : ℕ, harmonic n > M := by
  sorry

@[blueprint
  "thm:euler-prod-ge-harmonic"
  (statement := /-- The producto $\prod_{p \le n} (1 - 1 / p)^{-1}$ over primes at most n
    is greater than or equal to the n-th harmonic number. -/)
  (hasProof := true)
  (proof := /-- Use the geometric expansion of $(1 - 1/p)^{-1}$ for each prime $p$.
    Then the product is equal to the sum of inverses of the integers whose primes factors
    are all at most $n$, and the sum is greater than or equal to the n-th harmonic number. -/)
  (title := "Euler's product and the Harmonic number")
  (latexEnv := "theorem")]
theorem prod_of_inv_of_one_sub_inv_prime_ge_harmonic (n : ℕ) :
    ∏ p ∈ Finset.range (n + 1), 1 / (1 - 1 / p : ℚ) ≥ harmonic n := by
  sorry

@[blueprint
  "thm:inf-primes-euler"
  (statement := /-- The set of prime numbers is infinite. -/)
  (hasProof := true)
  (proof := /-- Assume that there are only finitely many primes.
    Then the product of $(1 - 1/p)^{-1}$ over all primes $p$ is finite.
    But by the previous theorem, this product is greater than the harmonic series,
    which is unbounded. This is a contradiction. -/)
  (title := "Infinitude of primes (Euler, via Euler product)")
  (latexEnv := "theorem")]
theorem InfinitudeOfPrimes_Euler : InfinitudeOfPrimes := by
  sorry
