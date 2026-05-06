module

import Architect
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Ring
public import DifferentProofs.InfinitudeOfPrimes.Defs

@[expose] public section


@[blueprint
  "def:saidak-sequence"
  (statement := /-- The sequence defined by $a_0 = 2$ and $a_{n+1} = a_n(a_n + 1)$
    for all $n \ge 0$. Note that any $a_n \ge 2$ works for the proof. -/)
  (title := "Saidak's sequence")
  (latexEnv := "definition")]
def a : ℕ → ℕ
  | 0 => 2
  | n + 1 => a n * (a n + 1)

@[blueprint
  "lem:saidak-ge-two"
  (statement := /-- For all $n \in \mathbb{N}$, $a_n \ge 2$. -/)
  (hasProof := true)
  (proof := /-- By induction. The base case is $a_0 = 2$. For the inductive step,
    if $a_n \ge 2$ then $a_{n+1} = a_n (a_n + 1) \ge 2 \cdot 1 = 2$. -/)
  (title := "Saidak's sequence is at least two")
  (latexEnv := "lemma")]
lemma a_ge_two : ∀ n, 2 ≤ a n
  | 0 => le_rfl
  | n + 1 => (Nat.mul_le_mul (a_ge_two n) (by lia : 1 ≤ a n + 1)).trans_eq' rfl

@[blueprint
  "lem:saidak-primeFactors-card"
  (statement := /-- For all $n \in \mathbb{N}$, $a_n$ has at least $n + 1$ distinct
    prime divisors. -/)
  (hasProof := true)
  (proof := /-- By induction on $n$. The base case is that $a_0 = 2$ has the prime divisor $2$.
    For the inductive step, since $a_n$ and $a_n + 1$ are consecutive they are coprime,
    so their prime factors are disjoint and the prime factors of
    $a_{n+1} = a_n (a_n + 1)$ split as a disjoint union. By induction $a_n$ has at least $n + 1$
    prime divisors, and since $a_n + 1 \ge 3$ it has at least one prime divisor. So $a_{n+1}$ has
    at least $n + 2$ distinct prime divisors. -/)
  (title := "Saidak's sequence has many prime divisors")
  (latexEnv := "lemma")]
lemma a_primeFactors_card_ge (n : ℕ) : n + 1 ≤ (a n).primeFactors.card := by
  induction n with
  | zero => simp [a, Nat.Prime.primeFactors Nat.prime_two]
  | succ n ih =>
    have h2 := a_ge_two n
    have hpos : 1 ≤ (a n + 1).primeFactors.card :=
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by lia))
    have hco : Nat.Coprime (a n) (a n + 1) := by simp [Nat.Coprime]
    rw [show a (n + 1) = a n * (a n + 1) from rfl, Nat.primeFactors_mul (by lia) (by lia),
      Finset.card_union_of_disjoint hco.disjoint_primeFactors]
    lia

@[blueprint
  "thm:inf-primes-saidak"
  (statement := /-- The set of prime numbers is infinite. -/)
  (hasProof := true)
  (proof := /-- By \cref{lem:saidak-primeFactors-card}, for every $n$ the integer $a_n$ has at
    least $n + 1$ distinct prime divisors. If the set of primes were finite, then for every $n$
    these prime divisors would be a subset of the finite set of all primes, bounding $n + 1$
    above by a fixed constant — a contradiction. -/)
  (title := "Infinitude of primes (Saidak)")
  (latexEnv := "theorem")]
theorem InfinitudeOfPrimes_Saidak : InfinitudeOfPrimes := fun hfin => by
  have h1 : (a hfin.toFinset.card).primeFactors.card ≤ hfin.toFinset.card :=
    Finset.card_le_card fun _ hp => hfin.mem_toFinset.mpr (Nat.prime_of_mem_primeFactors hp)
  have h2 := a_primeFactors_card_ge hfin.toFinset.card
  lia
