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
  (proof := /-- Use the inequality $\log(n + 1) \le H_n$ (`log_add_one_le_harmonic`). -/)
  (title := "Harmonic series is unbounded")
  (latexEnv := "theorem")]
theorem harmonic_unbounded : ∀ M : ℝ, ∃ n : ℕ, harmonic n > M := by
  intro M
  have h_log_diverges : Filter.Tendsto (fun n : ℕ ↦ Real.log ↑(n + 1)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp <|
      tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_add_atTop_nat 1
  exact Filter.Eventually.exists (h_log_diverges.eventually_gt_atTop M) |>
    fun ⟨n, hn⟩ => ⟨n, hn.trans_le <| mod_cast log_add_one_le_harmonic n⟩

@[blueprint
  "thm:euler-prod-ge-harmonic"
  (statement := /-- The product $\prod_{p \le n} p / (p - 1)$ over primes at most n
    is greater than or equal to the n-th harmonic number. -/)
  (hasProof := true)
  (proof := /-- Use the geometric expansion of $(1 - 1/p)^{-1}$ for each prime $p$.
    Then the product is equal to the sum of inverses of the integers whose primes factors
    are all at most $n$, and the sum is greater than or equal to the n-th harmonic number. -/)
  (title := "Euler's product and the Harmonic number")
  (latexEnv := "theorem")]
theorem prod_of_inv_of_one_sub_inv_prime_ge_harmonic (n : ℕ) :
    ∏ p ∈ (range (n + 1)).filter Nat.Prime, (p : ℚ) / (p - 1) ≥ harmonic n := by
  -- By definition of harmonic, we know that
  -- $\prod_{p \le n, p \text{ prime}} (1 - 1 / p)^{-1} \geq \sum_{k=1}^{n} \frac{1}{k}$.
  have h_prod_ge_sum :
      (∏ p ∈ filter Nat.Prime (range (n + 1)), (∑ i ∈ range (Nat.log p n + 1),
        (1 / p : ℚ) ^ i)) ≥ (∑ i ∈ range n, (1 / (i + 1) : ℚ)) := by
    -- Every integer $k$ in the range $1$ to $n$ can be written as a product of prime powers $p^e$
    -- where $p$ is a prime and $e$ is a non-negative integer.
    have h_factorization : ∀ k ∈ range n, ∃ f : ℕ → ℕ, (∀ p, Nat.Prime p → f p ≤ Nat.log p n) ∧
        (∏ p ∈ filter Nat.Prime (range (n + 1)), p ^ f p) = k + 1 := by
      intro k hk
      use fun p => Nat.factorization (k + 1) p;
      refine ⟨fun p pp => Nat.le_log_of_pow_le pp.one_lt <|
        Nat.le_trans (Nat.le_of_dvd (Nat.succ_pos _) <|
          Nat.ordProj_dvd _ _) <| Nat.succ_le_of_lt <| mem_range.mp hk, ?_ ⟩
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self (by positivity : (k + 1) ≠ 0)]
      rw [Finsupp.prod_of_support_subset] <;> norm_num
      exact fun p hp ↦
        mem_filter.mpr
          ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_mem_primeFactors hp)
            (by linarith [mem_range.mp hk]))), Nat.prime_of_mem_primeFactors hp⟩
    choose! f hf₁ hf₂ using h_factorization
    -- By definition of $f$, we can rewrite the sum $\sum_{k=1}^{n} \frac{1}{k}$ as
    -- $\sum_{k=1}^{n} \prod_{p \le n, p \text{ prime}} \frac{1}{p^{f(k, p)}}$.
    have h_sum_rewrite : ∑ k ∈ range n, (1 / (k + 1) : ℚ) =
        ∑ k ∈ range n, (∏ p ∈ filter Nat.Prime (range (n + 1)), (1 / p : ℚ) ^ f k p) := by
      refine sum_congr rfl fun k hk ↦ ?_
      simp at *
      exact_mod_cast hf₂ k hk |> Eq.symm
    rw [h_sum_rewrite, prod_sum]
    refine' le_trans _ (sum_le_sum_of_subset_of_nonneg _ fun _ _ _ ↦
      prod_nonneg fun _ _ ↦ pow_nonneg (by positivity) ?_)
    rotate_left
    · exact image (fun k ↦ fun p hp ↦ f k p) (range n)
    · grind
    · rw [sum_image]
      · exact sum_le_sum fun _ _ => by rw [← prod_attach]
      · intro k hk l hl hkl
        have := hf₂ k hk
        have := hf₂ l hl
        simp_all [funext_iff]
        have := hf₂ k hk
        have := hf₂ l hl
        simp_all [prod_congr rfl fun p hp ↦ show p ^ f k p = p ^ f l p by
          rw [hkl p (mem_range_succ_iff.mp (mem_filter.mp hp |>.1)) (mem_filter.mp hp |>.2)]]
  refine le_trans ?_ (h_prod_ge_sum.trans ?_)
  · norm_num [harmonic]
  · refine prod_le_prod ?_ ?_ <;> norm_num
    · exact fun _ _ _ => sum_nonneg fun _ _ => by positivity
    · intro i hi hi'
      have := geom_sum_mul (i : ℚ)⁻¹ (Nat.log i n + 1)
      simp_all [div_eq_mul_inv, mul_comm]
      rcases i with (_ | _ | i) <;> norm_num at *
      nlinarith [inv_pos.mpr (by positivity : 0 < (i : ℚ) + 1 + 1),
        inv_pos.mpr (by positivity : 0 < (i : ℚ) + 1),
        mul_inv_cancel₀ (by positivity : (i : ℚ) + 1 + 1 ≠ 0),
        mul_inv_cancel₀ (by positivity : (i : ℚ) + 1 ≠ 0 ),
        pow_pos (by positivity : 0 < (i : ℚ) + 1 + 1) (Nat.log (i + 1 + 1) n + 1),
        inv_pos.mpr (pow_pos (by positivity : 0 < (i : ℚ) + 1 + 1) (Nat.log (i + 1 + 1) n + 1))]

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
  unfold InfinitudeOfPrimes
  intro hfin
  -- There exists N bounding all primes.
  obtain ⟨N, hN⟩ : ∃ N, ∀ p, Nat.Prime p → p ≤ N :=
    ⟨hfin.toFinset.sup id, fun p hp ↦ Finset.le_sup (f := id) (hfin.mem_toFinset.mpr hp)⟩
  -- By harmonic_unbounded, pick n with harmonic n > the product over primes ≤ N.
  obtain ⟨n, hn⟩ := harmonic_unbounded
    (↑(∏ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℚ) / (p - 1)))
  -- The product over primes ≤ max(n,N) ≥ harmonic(max(n,N))
  have h1 := prod_of_inv_of_one_sub_inv_prime_ge_harmonic (max n N)
  -- The product over primes ≤ max(n,N) = product over primes ≤ N
  have hprod_eq : (range (max n N + 1)).filter Nat.Prime = (range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_range]
    exact ⟨fun ⟨_, hp⟩ => ⟨Nat.lt_succ_of_le (hN p hp), hp⟩, fun ⟨hle, hp⟩ ↦ ⟨by omega, hp⟩⟩
  rw [hprod_eq] at h1
  -- harmonic is monotone
  have h2 : harmonic n ≤ harmonic (max n N) :=
    sum_le_sum_of_subset_of_nonneg (range_mono (le_max_left n N)) (fun _ _ _ ↦ by positivity)
  -- Contradiction: harmonic n > product ≥ harmonic(max n N) ≥ harmonic n
  exact absurd hn (not_lt.mpr (by exact_mod_cast le_trans h2 h1))
