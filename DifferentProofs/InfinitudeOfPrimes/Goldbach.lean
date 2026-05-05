module

import Architect
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Ring
public import DifferentProofs.InfinitudeOfPrimes.Defs

@[expose] public section


@[blueprint
  "def:fermat-number"
  (statement := /-- The $n$-th Fermat number is defined as $F_n := 2^{2^n} + 1$. -/)
  (title := "Fermat number")
  (latexEnv := "definition")]
def Fermat (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

@[blueprint
  "lem:fermat-ge-two"
  (statement := /-- For all $n \in \mathbb{N}$, $F_n \ge 2$. -/)
  (hasProof := true)
  (proof := /-- Since $2^{2^n} \ge 1$, we have $F_n = 2^{2^n} + 1 \ge 2$. -/)
  (title := "Fermat numbers are at least two")
  (latexEnv := "lemma")]
lemma Fermat_gt_two (n : ℕ) : Fermat n ≥ 2 := by
  have : 1 ≤ 2 ^ (2 ^ n) := Nat.one_le_two_pow
  unfold Fermat; lia

@[blueprint
  "lem:fermat-odd"
  (statement := /-- For all $n \in \mathbb{N}$, $F_n$ is odd. -/)
  (hasProof := true)
  (proof := /-- Since $2^n \ge 1$, $2^{2^n}$ is even, so $F_n = 2^{2^n} + 1$ is odd. -/)
  (title := "Fermat numbers are odd")
  (latexEnv := "lemma")]
lemma Fermat_odd (n : ℕ) : Odd (Fermat n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.two_pow_pos n).ne'
  exact ⟨2 ^ k, by unfold Fermat; rw [hk, pow_succ]; ring⟩

@[blueprint
  "lem:fermat-recurrence"
  (statement := /-- For all $n \in \mathbb{N}$,
    $F_{n+1} = \prod_{k=0}^{n} F_k + 2$. -/)
  (hasProof := true)
  (proof := /-- We prove by induction that $\prod_{k=0}^{n-1} F_k = F_n - 2$.
    The base case $n = 0$ is trivial since the empty product is $1 = 3 - 2 = F_0 - 2$.
    For the inductive step, assuming $\prod_{k<n} F_k = F_n - 2$:
    $\prod_{k<n+1} F_k = (F_n - 2) F_n = (2^{2^n} + 1)(2^{2^n} - 1)
    = 2^{2^{n+1}} - 1 = F_{n+1} - 2$.
    Adding $2$ to both sides and using $F_{n+1} \ge 2$ gives the claim. -/)
  (title := "Fermat number recurrence")
  (latexEnv := "lemma")]
lemma Fermat_recurrence (n : ℕ) :
    Fermat (n + 1) = ∏ k ∈ Finset.range (n + 1), Fermat k + 2 := by
  have hprod : ∀ m, ∏ k ∈ Finset.range m, Fermat k = Fermat m - 2 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Finset.prod_range_succ, ih, Fermat, Fermat, mul_comm,
          (show 2 ^ 2 ^ m + 1 - 2 = 2 ^ 2 ^ m - 1 by lia), ← Nat.sq_sub_sq]
      ring_nf
      lia
  rw [hprod, Nat.sub_add_cancel (Fermat_gt_two _)]

@[blueprint
  "lem:fermat-coprime"
  (statement := /-- For all $n \in \mathbb{N}$, $F_{n+1}$ is coprime with
    $\prod_{k=0}^{n} F_k$. -/)
  (hasProof := true)
  (proof := /-- By Lemma \cref{lem:fermat-recurrence},
    $F_{n+1} = \prod_{k=0}^{n} F_k + 2$, so $\gcd(F_{n+1}, \prod_{k=0}^{n} F_k) =
    \gcd(2, \prod_{k=0}^{n} F_k)$. Since each $F_k$ is odd by
    Lemma \cref{lem:fermat-odd}, the product is odd, hence the gcd is $1$. -/)
  (title := "Coprimality of Fermat numbers")
  (latexEnv := "lemma")]
lemma Fermat_coprime (n : ℕ) :
    (Fermat (n + 1)).Coprime (∏ k ∈ Finset.range (n + 1), Fermat k) := by
  rw [Fermat_recurrence n, add_comm, Nat.coprime_add_self_left, Nat.coprime_two_left]
  exact Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
    (fun k _ => Fermat_odd k)

@[blueprint
  "lem:fermat-pairwise-coprime"
  (statement := /-- For all distinct $m, n \in \mathbb{N}$, $F_m$ and $F_n$ are coprime. -/)
  (hasProof := true)
  (proof := /-- WLOG $m < n$. Write $n = k + 1$. Then $m \in \{0, \dots, k\}$, so
    $F_m \mid \prod_{k'=0}^{k} F_{k'}$. By Lemma \cref{lem:fermat-coprime},
    $\gcd(F_n, \prod F_{k'}) = 1$, so $\gcd(F_n, F_m) = 1$. -/)
  (title := "Pairwise coprimality of Fermat numbers")
  (latexEnv := "lemma")]
lemma Fermat_pairwise_coprime : Pairwise (fun m n => (Fermat m).Coprime (Fermat n)) := by
  intro m n hmn
  wlog h : m < n with H
  · exact (H hmn.symm (by lia)).symm
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by lia⟩
  exact (Fermat_coprime k).symm.coprime_dvd_left
    (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by lia)))

@[blueprint
  "thm:inf-primes-goldbach"
  (statement := /-- The set of prime numbers is infinite. -/)
  (hasProof := true)
  (proof := /-- For each $n \in \mathbb{N}$, $F_n \ge 2$ has a smallest prime factor $p_n$.
    By Lemma \cref{lem:fermat-pairwise-coprime}, the Fermat numbers are pairwise coprime,
    so the map $n \mapsto p_n$ is injective. Hence there are infinitely many primes. -/)
  (title := "Infinitude of primes (Goldbach, via Fermat numbers)")
  (latexEnv := "theorem")]
theorem InfinitudeOfPrimes_Goldbach : InfinitudeOfPrimes := by
  apply Set.infinite_of_injective_forall_mem (f := fun n => (Fermat n).minFac)
  · intro m n (h : (Fermat m).minFac = (Fermat n).minFac)
    by_contra hmn
    have hp : (Fermat m).minFac.Prime :=
      Nat.minFac_prime (by have := Fermat_gt_two m; lia)
    exact hp.not_dvd_one <| Fermat_pairwise_coprime hmn ▸
      Nat.dvd_gcd (Nat.minFac_dvd _) (h.symm ▸ Nat.minFac_dvd _)
  · exact fun n => Nat.minFac_prime (by have := Fermat_gt_two n; lia)
