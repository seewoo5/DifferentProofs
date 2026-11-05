module

public import DifferentProofs.InfinitudeOfPrimes.Defs
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Infinitude of primes using only `propext`

This is the variant of Euclid's proof in `InfinitudeOfPrimes_Euclid`: a prime factor of `n ! + 1`
does not divide `n !`, so it is bigger than `n`. That proof depends on all three standard axioms.
This one depends only on `propext`, which the statement `InfinitudeOfPrimes` already forces, so no
proof of it can use fewer axioms. The `#guard_msgs` at the end of this file fail the build
otherwise, and `comparator/InfinitudeOfPrimesConstructive.json` has Comparator check in CI that it
avoids `Classical.choice`.

The argument is the same as in `InfinitudeOfPrimes_Euclid`. What changes is that three mathlib
lemmas used there, which reach `Classical.choice`, are replaced:

* `Nat.exists_prime_and_dvd` by `InfinitudeOfPrimes.Constructive.exists_prime_dvd`, which searches
  the numbers below `m` for a divisor other than `1`;
* `Nat.Prime.dvd_factorial` by `Nat.dvd_factorial`;
* `Set.Finite.bddAbove` by `InfinitudeOfPrimes.Constructive.exists_bound`, which bounds a function
  on `Fin n`.

For the same reason the file avoids `lia`. It also avoids `omega` and the coercion of an `Equiv` to
a function, which reach `Quot.sound`, and uses the fields `toFun` and `invFun` of the `Equiv`
directly.
-/

@[expose] public section

namespace InfinitudeOfPrimes.Constructive

/-- Search the numbers below `k`: either the only one that divides `m` is `1`, or there is another
one. -/
theorem forall_or_exists_dvd (m k : ℕ) :
    (∀ d < k, d ∣ m → d = 1) ∨ ∃ d < k, d ∣ m ∧ d ≠ 1 := by
  induction k with
  | zero => exact .inl fun d hd => absurd hd (Nat.not_lt_zero d)
  | succ k ih =>
    rcases ih with ih | ⟨d, hd, h⟩
    · rcases Decidable.em (k ∣ m ∧ k ≠ 1) with hk | hk
      · exact .inr ⟨k, Nat.lt_succ_self k, hk⟩
      · refine .inl fun d hd hdm => ?_
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hlt | rfl
        · exact ih d hlt hdm
        · exact Decidable.byContradiction fun h1 => hk ⟨hdm, h1⟩
    · exact .inr ⟨d, Nat.lt_succ_of_lt hd, h⟩

/-- Every `m ≥ 2` has a prime factor: `m` itself if the search finds no divisor other than `1`, and
a prime factor of the divisor otherwise. -/
theorem exists_prime_dvd (m : ℕ) (hm : 2 ≤ m) : ∃ p, p.Prime ∧ p ∣ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases forall_or_exists_dvd m m with h | ⟨d, hd, hdm, hd1⟩
    · exact ⟨m, Nat.prime_def_lt.mpr ⟨hm, h⟩, Nat.dvd_refl m⟩
    · match d, hd, hdm, hd1 with
      | 0, _, h0, _ =>
        rw [Nat.eq_zero_of_zero_dvd h0] at hm
        exact absurd hm (by decide)
      | 1, _, _, h1 => exact absurd rfl h1
      | d + 2, hd, hdm, _ =>
        obtain ⟨p, hp, hpd⟩ := ih (d + 2) hd (Nat.le_add_left 2 d)
        exact ⟨p, hp, Nat.dvd_trans hpd hdm⟩

/-- **Euclid's argument**: a prime factor of `n ! + 1` is bigger than `n`, as otherwise it would
divide both `n !` and `n ! + 1`. This is the statement `InfinitudeOfPrimes'`. -/
theorem exists_prime_gt (n : ℕ) : ∃ p : ℕ, p.Prime ∧ p > n := by
  obtain ⟨p, hp, hd⟩ :=
    exists_prime_dvd (n.factorial + 1) (Nat.add_le_add_right (Nat.factorial_pos n) 1)
  have h2 := hp.two_le
  refine ⟨p, hp, Nat.lt_of_not_ge fun hle => ?_⟩
  have h1 : p ∣ n.factorial := Nat.dvd_factorial (Nat.lt_of_lt_of_le Nat.two_pos h2) hle
  have h3 := Nat.le_of_dvd Nat.one_pos ((Nat.dvd_add_right h1).mp hd)
  exact absurd (Nat.le_trans h2 h3) (by decide)

/-- A function on `Fin n` is bounded on the indices below `k`. -/
theorem exists_bound {n : ℕ} (f : Fin n → ℕ) (k : ℕ) :
    ∃ M, ∀ i : Fin n, i.val < k → f i ≤ M := by
  induction k with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨M, hM⟩ := ih
    rcases Nat.lt_or_ge k n with hk | hk
    · refine ⟨M + f ⟨k, hk⟩, fun i hi => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
      · exact Nat.le_trans (hM i h) (Nat.le_add_right _ _)
      · rw [show i = ⟨k, hk⟩ from Fin.ext h]
        exact Nat.le_add_left _ _
    · exact ⟨M, fun i _ => hM i (Nat.lt_of_lt_of_le i.isLt hk)⟩

end InfinitudeOfPrimes.Constructive

open InfinitudeOfPrimes.Constructive in
/-- **The infinitude of primes**, by Euclid's argument. A finite set of primes is bounded, by way of
its equivalence with some `Fin n`, and `exists_prime_gt` gives a prime above the bound. -/
theorem InfinitudeOfPrimes_Constructive : InfinitudeOfPrimes := fun hfin => by
  obtain @⟨n, e⟩ : Finite {p : ℕ | p.Prime} := hfin
  obtain ⟨M, hM⟩ := exists_bound (fun i => (e.invFun i).val) n
  obtain ⟨p, hp, hpM⟩ := exists_prime_gt M
  have h := hM (e.toFun ⟨p, hp⟩) (e.toFun ⟨p, hp⟩).isLt
  simp only [e.left_inv ⟨p, hp⟩] at h
  exact Nat.not_le_of_gt hpM h

/-- info: 'InfinitudeOfPrimes_Constructive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InfinitudeOfPrimes_Constructive

/--
info: 'InfinitudeOfPrimes.Constructive.exists_prime_gt' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InfinitudeOfPrimes.Constructive.exists_prime_gt
