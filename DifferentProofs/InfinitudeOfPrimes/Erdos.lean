module

public import DifferentProofs.InfinitudeOfPrimes.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Erdős' proof of the infinitude of primes

This file formalizes the proof of the infinitude of primes given in Section 4.5 of
Lindsey Harrison, *From Euclid to Present: A Collection of Proofs regarding the Infinitude of
Primes* (2013). The argument is Paul Erdős': count the integers up to `n`.

The two ingredients are:

* **Lemma 3.** Every integer `n ≥ 1` is the product of a squarefree integer and a perfect
  square. This is `Nat.sq_mul_squarefree_of_pos` in mathlib.
* The counting bound. A squarefree number is a product of distinct primes, so there are at
  most `2 ^ π(n)` squarefree numbers at most `n`, where `π(n)` is the number of primes at most
  `n`; and there are at most `√n` perfect squares at most `n`. Writing every `m ≤ n` as
  `a * b ^ 2` with `a` squarefree therefore gives `n ≤ 2 ^ π(n) * √n`, hence
  `π(n) ≥ log₂(n) / 2`, which is unbounded in `n`.

Since `π(n)` is unbounded, there are infinitely many primes.

The counting bound `le_two_pow_primeCounting_mul_sqrt` counts both factors at once: every
`m ∈ [1, n]` is `b ^ 2 * ∏ p ∈ s, p` for a set `s` of primes at most `n` and a `b ∈ [1, √n]`, and
there are `2 ^ π(n) * √n` such pairs `(s, b)`. The lower bound `le_four_pow_primeCounting` is the
log-free form `n ≤ 4 ^ π(n)` of `π(n) ≥ log₂(n) / 2`.
-/

@[expose] public section

open Finset Nat
open scoped Nat.Prime

namespace InfinitudeOfPrimes.Erdos

/-- **The counting bound** `n ≤ 2 ^ π(n) * √n`: every `m ∈ [1, n]` is `b ^ 2 * ∏ p ∈ s, p`
for a set `s` of primes at most `n` and some `b ∈ [1, √n]`. -/
theorem le_two_pow_primeCounting_mul_sqrt (n : ℕ) : n ≤ 2 ^ π n * n.sqrt := by
  have := card_le_card_of_surjOn (fun (s, b) ↦ b ^ 2 * ∏ p ∈ s, p)
    (s := (primesLE n).powerset ×ˢ Icc 1 n.sqrt) (t := Icc 1 n) fun m hm ↦ ?_
  · simpa only [ge_iff_le, card_Icc, add_tsub_cancel_right, card_product, card_powerset,
      primesLE_card_eq_primeCounting] using this
  obtain ⟨hm_pos, hmn⟩ := mem_Icc.1 hm
  obtain ⟨a, b, ha, hb, rfl, hsq⟩ := sq_mul_squarefree_of_pos hm_pos
  have ha_le : a ≤ n := (Nat.le_mul_of_pos_left a (pow_pos hb 2)).trans hmn
  have hs : a.primeFactors ⊆ primesLE n := fun p hp ↦
    mem_primesLE.2 ⟨(le_of_mem_primeFactors hp).trans ha_le, prime_of_mem_primeFactors hp⟩
  have hb_le : b ≤ n.sqrt := le_sqrt'.2 ((Nat.le_mul_of_pos_right _ ha).trans hmn)
  refine ⟨(a.primeFactors, b), mem_product.2 ⟨mem_powerset.2 hs, mem_Icc.2 ⟨hb, hb_le⟩⟩, ?_⟩
  simp only [prod_primeFactors_of_squarefree hsq]

/-- The lower bound `π(n) ≥ log₂(n) / 2`, in the form `n ≤ 4 ^ π(n)`. -/
theorem le_four_pow_primeCounting (n : ℕ) : n ≤ 4 ^ π n := by
  rw [show 4 = 2 * 2 from rfl, mul_pow]
  nlinarith [le_two_pow_primeCounting_mul_sqrt n, sqrt_le n]

end InfinitudeOfPrimes.Erdos

open InfinitudeOfPrimes.Erdos in
/-- **The infinitude of primes**, since `π(n) ≥ log₂(n) / 2` is unbounded. -/
theorem InfinitudeOfPrimes_Erdos : InfinitudeOfPrimes := fun hfin ↦ by
  set k := #hfin.toFinset
  have hπ (n : ℕ) : π n ≤ k := by
    rw [← primesLE_card_eq_primeCounting]
    exact card_le_card fun p hp ↦ hfin.mem_toFinset.2 (prime_of_mem_primesLE hp)
  have hlower := le_four_pow_primeCounting (4 ^ k + 1)
  have hupper := Nat.pow_le_pow_right four_pos (hπ (4 ^ k + 1))
  lia
