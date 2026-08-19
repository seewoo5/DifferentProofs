module

public import DifferentProofs.InfinitudeOfPrimes.Defs
public import DifferentProofsForMathlib.Analysis.Real.Pi.Irrational
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Infinitude of primes from the irrationality of `π ^ 2`

Euler's product formula reads `ζ(2) = ∏ p prime, (1 - p⁻²)⁻¹`, the product being the limit of the
partial products over the primes below `n`. Were there only finitely many primes, those partial
products would be constant from some point on, exhibiting `ζ(2)` as a finite product of rational
numbers and hence as a rational number. But `ζ(2) = π ^ 2 / 6` and `π ^ 2` is irrational
(`irrational_pi_sq`), a contradiction.
-/

@[expose] public section

open Filter Finset
open scoped Topology

/-- **The infinitude of primes**, from the irrationality of `π ^ 2` and the Euler product for the
Riemann zeta function. -/
theorem InfinitudeOfPrimes_Zeta : InfinitudeOfPrimes := by
  intro hfin
  obtain ⟨N, hN⟩ : ∃ N, ∀ p, Nat.Prime p → p < N :=
    ⟨hfin.toFinset.sup id + 1, fun p hp ↦
      Nat.lt_succ_of_le (le_sup (f := id) (hfin.mem_toFinset.mpr hp))⟩
  -- With every prime below `N`, the partial Euler products are constant from `N` on.
  have hconst : ∀ n, N ≤ n → Nat.primesBelow n = Nat.primesBelow N := fun n hn ↦ by
    ext p
    simp only [Nat.primesBelow, mem_filter, mem_range]
    exact ⟨fun ⟨_, hp⟩ ↦ ⟨hN p hp, hp⟩, fun ⟨hpN, hp⟩ ↦ ⟨hpN.trans_le hn, hp⟩⟩
  -- Hence Euler's product formula makes `ζ(2)` the rational number `q`.
  set q : ℚ := ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℚ) ^ 2)⁻¹)⁻¹ with hq
  have hzeta : riemannZeta 2 = (q : ℂ) := by
    refine tendsto_nhds_unique (riemannZeta_eulerProduct (by norm_num)) ?_
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [hconst n hn, hq]
    push_cast
    exact prod_congr rfl fun p _ ↦ by rw [Complex.cpow_neg]; norm_num
  -- But `ζ(2) = π ^ 2 / 6`, so `π ^ 2` would be the rational number `6 * q`.
  rw [riemannZeta_two] at hzeta
  refine irrational_pi_sq ⟨6 * q, ?_⟩
  have h : ((Real.pi ^ 2 / 6 : ℝ) : ℂ) = ((q : ℝ) : ℂ) := by push_cast [hzeta]; ring
  have := Complex.ofReal_inj.mp h
  push_cast
  linarith
