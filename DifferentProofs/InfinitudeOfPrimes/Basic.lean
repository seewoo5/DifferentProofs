module

import Architect
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import DifferentProofs.InfinitudeOfPrimes.Defs

@[expose] public section

@[blueprint
  "thm:inf-primes-iff"
  (statement := /-- The two formulations of the infinitude of primes are equivalent: the set of
    primes is infinite if and only if for every $n \in \mathbb{N}$ there exists a prime $p > n$. -/)
  (hasProof := true)
  (proof := /-- Both directions follow from the general fact that, in a nonempty linear order with
    a locally finite bottom, a set is infinite iff for every $a$ some element of the set exceeds
    $a$ (\texttt{Set.infinite\_iff\_exists\_gt}). Specializing to $\mathbb{N}$ and the set
    $\{p : \mathbb{N} \mid p \text{ is prime}\}$ gives the claim. -/)
  (title := "Equivalence of the two formulations of the infinitude of primes")
  (latexEnv := "theorem")]
theorem InfinitudeOfPrimes_iff_InfinitudeOfPrimes' : InfinitudeOfPrimes ↔ InfinitudeOfPrimes' := by
  simp only [InfinitudeOfPrimes, InfinitudeOfPrimes', Set.infinite_iff_exists_gt,
    Set.mem_setOf_eq, and_comm]
