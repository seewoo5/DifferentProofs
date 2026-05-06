module

import Architect
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import DifferentProofs.InfinitudeOfPrimes.Defs
public import Mathlib.Data.Nat.Fib.Basic

@[expose] public section


@[blueprint
  "lem:fib-37-factorization"
  (statement := /-- $F_{37} = 73 \cdot 149 \cdot 2221$. -/)
  (hasProof := true)
  (proof := /-- By direct computation. -/)
  (title := "Factorization of the 37-th Fibonacci number")
  (latexEnv := "lemma")]
lemma fib_37 : Nat.fib 37 = 73 * 149 * 2221 := by simp [Nat.fib]

@[blueprint
  "lem:fib-prime-ge-two"
  (statement := /-- For any odd prime $p$, $F_p \ge 2$. -/)
  (hasProof := true)
  (proof := /-- Since $p \ge 3$ and $F$ is monotone, $F_p \ge F_3 = 2$. -/)
  (title := "Fibonacci numbers at odd primes are at least two")
  (latexEnv := "lemma")]
lemma fib_prime_ge_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 2 ≤ Nat.fib p :=
  calc 2 = Nat.fib 3 := by decide
    _ ≤ Nat.fib p := Nat.fib_mono (hp.two_le.lt_or_eq.resolve_right (Ne.symm hp2))

@[blueprint
  "lem:fib-coprime-distinct-primes"
  (statement := /-- If $p$ and $q$ are distinct primes, then $F_p$ and $F_q$ are coprime. -/)
  (hasProof := true)
  (proof := /-- Distinct primes are coprime, so $\gcd(p, q) = 1$.
    Since $\gcd(F_m, F_n) = F_{\gcd(m, n)}$, we have
    $\gcd(F_p, F_q) = F_1 = 1$. -/)
  (title := "Fibonacci numbers at distinct primes are coprime")
  (latexEnv := "lemma")]
lemma fib_coprime_of_distinct_primes {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime (Nat.fib p) (Nat.fib q) := by
  rw [Nat.Coprime, ← Nat.fib_gcd, (Nat.coprime_primes hp hq).mpr hpq]; rfl

@[blueprint
  "thm:inf-primes-wunderlich"
  (statement := /-- The set of prime numbers is infinite. -/)
  (hasProof := true)
  (proof := /-- Assume that there are only finitely many prime numbers,
    $\{p_1 = 2, p_2 = 3, \ldots, p_n\}$. Consider the corresponding Fibonacci numbers
    $F_{p_2}, \ldots, F_{p_n}$ (except for $F_{p_1} = F_2 = 1$).
    By $\gcd(F_m, F_n) = F_{\gcd(m, n)}$, these are pairwise coprime.
    Since we have $n$ primes and $n - 1$ Fibonacci numbers, each of the Fibonacci numbers
    can have at most two prime factors. However, this is not possible since
    $F_{37} = 73 \cdot 149 \cdot 2221$ is a product of three distinct primes. -/)
  (title := "Infinitude of primes (Wunderlich, using Fibonacci numbers)")
  (latexEnv := "theorem")]
theorem InfinitudeOfPrimes_Wunderlich : InfinitudeOfPrimes := fun hfin => by
  set S := hfin.toFinset
  have h2S : 2 ∈ S := hfin.mem_toFinset.mpr Nat.prime_two
  have h37S : 37 ∈ S := hfin.mem_toFinset.mpr (by decide)
  set T := S.erase 2
  have h37T : 37 ∈ T := Finset.mem_erase.mpr ⟨by decide, h37S⟩
  have hT_prime : ∀ p ∈ T, p.Prime := fun _ hp =>
    hfin.mem_toFinset.mp (Finset.mem_of_mem_erase hp)
  have hf37 : 3 ≤ (Nat.fib 37).primeFactors.card := by
    have : (Nat.fib 37).primeFactors = {73, 149, 2221} := by
      rw [fib_37, Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.Prime.primeFactors (by norm_num : (73 : ℕ).Prime),
          Nat.Prime.primeFactors (by norm_num : (149 : ℕ).Prime),
          Nat.Prime.primeFactors (by norm_num : (2221 : ℕ).Prime)]
      rfl
    rw [this]; decide
  have hpwd : (T : Set ℕ).PairwiseDisjoint (fun p => (Nat.fib p).primeFactors) :=
    fun p hp q hq hpq => Nat.Coprime.disjoint_primeFactors
      (fib_coprime_of_distinct_primes (hT_prime p hp) (hT_prime q hq) hpq)
  have hsum_le : ∑ p ∈ T, (Nat.fib p).primeFactors.card ≤ S.card := by
    rw [← Finset.card_biUnion hpwd]
    exact Finset.card_le_card fun q hq =>
      let ⟨p, _, hqp⟩ := Finset.mem_biUnion.mp hq
      hfin.mem_toFinset.mpr (Nat.prime_of_mem_primeFactors hqp)
  have hsplit := (Finset.add_sum_erase T (fun p => (Nat.fib p).primeFactors.card) h37T).symm
  have hge_others : (T.erase 37).card ≤ ∑ p ∈ T.erase 37, (Nat.fib p).primeFactors.card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun p hp =>
      have hpT := Finset.mem_of_mem_erase hp
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr
        (fib_prime_ge_two (hT_prime p hpT) (Finset.mem_erase.mp hpT).1))
  have hT_card := Finset.card_erase_of_mem h2S
  have hT37_card := Finset.card_erase_of_mem h37T
  have h2_pos : 1 ≤ S.card := Finset.one_le_card.mpr ⟨2, h2S⟩
  have h37_pos : 1 ≤ T.card := Finset.one_le_card.mpr ⟨37, h37T⟩
  lia
