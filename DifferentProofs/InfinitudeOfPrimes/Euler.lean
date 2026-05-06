module

import Architect
public import DifferentProofs.InfinitudeOfPrimes.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Finset

@[blueprint
  "thm:harmonic-unbounded"
  (statement := /-- The harmonic series is unbounded. -/)
  (hasProof := true)
  (proof := /-- Use the inequality $\log(n + 1) \le H_n$. -/)
  (title := "Harmonic series is unbounded")
  (latexEnv := "theorem")]
theorem harmonic_unbounded : ∀ M : ℝ, ∃ n : ℕ, harmonic n > M := fun M ↦
  let ⟨n, hn⟩ := ((Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop.comp <|
    Filter.tendsto_add_atTop_nat 1).eventually_gt_atTop M).exists
  ⟨n, hn.trans_le <| mod_cast log_add_one_le_harmonic n⟩

@[blueprint
  "thm:euler-prod-ge-harmonic"
  (statement := /-- The product $\prod_{p \le n} p / (p - 1)$ over primes at most n
    is greater than or equal to the n-th harmonic number. -/)
  (hasProof := true)
  (proof := /-- Use the geometric expansion of $p / (p - 1) = (1 - 1/p)^{-1}$ for each prime $p$.
    Then the product is equal to the sum of inverses of the integers whose primes factors
    are all at most $n$, and the sum is greater than or equal to the n-th harmonic number. -/)
  (title := "Euler's product and the Harmonic number")
  (latexEnv := "theorem")]
theorem prod_prime_div_prime_sub_one_ge_harmonic (n : ℕ) :
    ∏ p ∈ (range (n + 1)).filter Nat.Prime, (p : ℚ) / (p - 1) ≥ harmonic n := by
  have h_prod_ge_sum :
      (∏ p ∈ filter Nat.Prime (range (n + 1)), (∑ i ∈ range (Nat.log p n + 1),
        (1 / p : ℚ) ^ i)) ≥ (∑ i ∈ range n, (1 / (i + 1) : ℚ)) := by
    have h_factorization : ∀ k ∈ range n, ∃ f : ℕ → ℕ, (∀ p, Nat.Prime p → f p ≤ Nat.log p n) ∧
        (∏ p ∈ filter Nat.Prime (range (n + 1)), p ^ f p) = k + 1 := by
      intro k hk
      refine ⟨fun p ↦ Nat.factorization (k + 1) p, fun p pp ↦ Nat.le_log_of_pow_le pp.one_lt <|
        Nat.le_trans (Nat.le_of_dvd (Nat.succ_pos _) <|
          Nat.ordProj_dvd _ _) <| Nat.succ_le_of_lt <| mem_range.mp hk, ?_⟩
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self (by positivity : (k + 1) ≠ 0)]
      rw [Finsupp.prod_of_support_subset] <;> norm_num
      exact fun p hp ↦ mem_filter.mpr
        ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_mem_primeFactors hp)
          (by linarith [mem_range.mp hk]))), Nat.prime_of_mem_primeFactors hp⟩
    choose! f hf₁ hf₂ using h_factorization
    have h_sum_rewrite : ∑ k ∈ range n, (1 / (k + 1) : ℚ) =
        ∑ k ∈ range n, (∏ p ∈ filter Nat.Prime (range (n + 1)), (1 / p : ℚ) ^ f k p) :=
      sum_congr rfl fun k hk ↦ by
        simp only [one_div, inv_pow, prod_inv_distrib, inv_inj]
        exact_mod_cast (hf₂ k hk).symm
    rw [h_sum_rewrite, prod_sum]
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg
      (s := image (fun k ↦ fun p _ ↦ f k p) (range n)) (by grind)
      fun _ _ _ ↦ prod_nonneg fun _ _ ↦ pow_nonneg (by positivity) _)
    rw [sum_image]
    · exact sum_le_sum fun _ _ ↦ by rw [← prod_attach]
    · intro k hk l hl hkl
      simp only [funext_iff] at hkl
      have : k + 1 = l + 1 := by
        rw [← hf₂ k hk, ← hf₂ l hl]
        exact prod_congr rfl fun p hp ↦ by rw [hkl p hp]
      omega
  refine le_trans ?_ (h_prod_ge_sum.trans ?_)
  · norm_num [harmonic]
  · refine prod_le_prod ?_ ?_ <;> norm_num
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ by positivity
    · intro i hi hi'
      have := geom_sum_mul (i : ℚ)⁻¹ (Nat.log i n + 1)
      simp_all [div_eq_mul_inv, mul_comm]
      rcases i with (_ | _ | i) <;> norm_num at *
      nlinarith [inv_pos.mpr (by positivity : 0 < (i : ℚ) + 1 + 1),
        inv_pos.mpr (by positivity : 0 < (i : ℚ) + 1),
        mul_inv_cancel₀ (by positivity : (i : ℚ) + 1 + 1 ≠ 0),
        mul_inv_cancel₀ (by positivity : (i : ℚ) + 1 ≠ 0),
        pow_pos (by positivity : 0 < (i : ℚ) + 1 + 1) (Nat.log (i + 1 + 1) n + 1),
        inv_pos.mpr (pow_pos (by positivity : 0 < (i : ℚ) + 1 + 1) (Nat.log (i + 1 + 1) n + 1))]

@[blueprint
  "thm:inf-primes-euler"
  (statement := /-- The set of prime numbers is infinite. -/)
  (hasProof := true)
  (proof := /-- Assume that there are only finitely many primes.
    Then the product of $(1 - 1/p)^{-1}$ over all primes $p$ is finite.
    But by \cref{thm:euler-prod-ge-harmonic}, this product is greater than the harmonic series,
    which is unbounded (\cref{thm:harmonic-unbounded}), a contradiction. -/)
  (title := "Infinitude of primes (Euler, via Euler product)")
  (latexEnv := "theorem")]
theorem InfinitudeOfPrimes_Euler : InfinitudeOfPrimes := by
  intro hfin
  obtain ⟨N, hN⟩ : ∃ N, ∀ p, Nat.Prime p → p ≤ N :=
    ⟨hfin.toFinset.sup id, fun p hp ↦ le_sup (f := id) (hfin.mem_toFinset.mpr hp)⟩
  obtain ⟨n, hn⟩ := harmonic_unbounded
    (↑(∏ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℚ) / (p - 1)))
  have h1 := prod_prime_div_prime_sub_one_ge_harmonic (max n N)
  have hprod_eq : (range (max n N + 1)).filter Nat.Prime = (range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_range]
    exact ⟨fun ⟨_, hp⟩ ↦ ⟨Nat.lt_succ_of_le (hN p hp), hp⟩, fun ⟨_, hp⟩ ↦ ⟨by omega, hp⟩⟩
  rw [hprod_eq] at h1
  have h2 : harmonic n ≤ harmonic (max n N) :=
    sum_le_sum_of_subset_of_nonneg (range_mono (le_max_left n N)) fun _ _ _ ↦ by positivity
  exact absurd hn (not_lt.mpr (by exact_mod_cast h2.trans h1))
