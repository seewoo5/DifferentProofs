module

public import DifferentProofs.FermatLittleTheorem.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring

/-!
# Fermat's little theorem using only `propext`

This is a variant of the proof in `FermatLittleTheorem_Binomial`: the binomial theorem gives the
freshman's dream, `(a + 1) ^ p ≡ a ^ p + 1` modulo `p`, and induction on `a` gives the theorem. That
proof depends on all three standard axioms. This one depends only on `propext`, which the statement
`FermatLittleTheorem` already forces, so no proof of it can use fewer axioms. The `#guard_msgs` at
the end of this file fail the build otherwise, and `comparator/FermatLittleTheoremConstructive.json`
has Comparator check in CI that it avoids `Classical.choice`.

The argument is the same as in `FermatLittleTheorem_Binomial`, but what that proof takes from
mathlib is proved here:

* The statement of `add_pow` uses `Finset.range`, which depends on `Classical.choice`, so the
  expansion of `(a + 1) ^ n` is written as a recursion on the upper limit of the sum, `binomialSum`,
  and the binomial theorem is `add_one_pow`.
* `Nat.Prime.dvd_choose_self` reaches `Classical.choice`, so `p ∣ p.choose k` is `prime_dvd_choose`.
  It needs Euclid's lemma for a factor below `p`, `dvd_of_dvd_mul`, which is proved by descent,
  since `Nat.Coprime.dvd_of_dvd_mul_right` reaches `Quot.sound`.
* `ZMod.intCast_eq_intCast_iff` reaches `Classical.choice`, so the file works with divisibility in
  `ℤ` instead of in `ZMod p`.

For the same reason the file avoids `lia` and `omega`.
-/

@[expose] public section

namespace FermatLittleTheorem.Constructive

/-- Euclid's lemma for a factor below `p`, by descent on the factor: if `p ∣ c * k`, then
`p ∣ c * (p % k)`, because `p = k * (p / k) + p % k`. -/
theorem dvd_of_dvd_mul {p : ℕ} (hp : p.Prime) {c : ℕ} (k : ℕ) (h0 : 0 < k) (hk : k < p)
    (hd : p ∣ c * k) : p ∣ c := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos (p % k) with hr | hr
    · rcases hp.eq_one_or_self_of_dvd k (Nat.dvd_of_mod_eq_zero hr) with rfl | rfl
      · rwa [Nat.mul_one] at hd
      · exact absurd hk (Nat.lt_irrefl _)
    · have e : c * p = c * k * (p / k) + c * (p % k) :=
        calc c * p = c * (k * (p / k) + p % k) := by rw [Nat.div_add_mod]
          _ = c * k * (p / k) + c * (p % k) := by ring
      have hr' : p ∣ c * (p % k) :=
        (Nat.dvd_add_right (Nat.dvd_trans hd (Nat.dvd_mul_right _ _))).mp
          (e ▸ Nat.dvd_mul_left p c)
      exact ih (p % k) (Nat.mod_lt p h0) hr (Nat.lt_trans (Nat.mod_lt p h0) hk) hr'

/-- `p` divides `p.choose k` for `0 < k < p`, because `p * (p - 1).choose (k - 1)` is
`p.choose k * k`. -/
theorem prime_dvd_choose {p k : ℕ} (hp : p.Prime) (h0 : 0 < k) (hk : k < p) : p ∣ p.choose k := by
  obtain ⟨p', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt (Nat.lt_trans h0 hk))
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt h0)
  exact dvd_of_dvd_mul hp (k' + 1) h0 hk ⟨_, (Nat.add_one_mul_choose_eq p' k').symm⟩

theorem choose_self : ∀ n : ℕ, n.choose n = 1
  | 0 => rfl
  | n + 1 => by
    rw [Nat.choose_succ_succ, choose_self n, Nat.choose_succ_self]

/-- `binomialSum a n k` is `∑ i < k, n.choose i * a ^ i`, the partial sums of the binomial expansion
of `(a + 1) ^ n`, as a recursion on `k`. -/
def binomialSum (a : ℤ) (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => binomialSum a n k + (n.choose k : ℤ) * a ^ k

theorem binomialSum_one (a : ℤ) (n : ℕ) : binomialSum a n 1 = 1 := by
  simp only [binomialSum, Nat.choose_zero_right, Nat.cast_one, pow_zero]
  ring

/-- Pascal's rule, summed over the terms below `k + 1`. -/
theorem binomialSum_succ (a : ℤ) (n : ℕ) :
    ∀ k, binomialSum a (n + 1) (k + 1) = binomialSum a n (k + 1) + a * binomialSum a n k
  | 0 => by
    rw [binomialSum_one, binomialSum_one]
    simp only [binomialSum]
    ring
  | k + 1 => by
    have ih := binomialSum_succ a n k
    rw [binomialSum, ih, Nat.choose_succ_succ]
    simp only [binomialSum]
    push_cast
    ring

/-- **The binomial theorem** for `(a + 1) ^ n`. -/
theorem add_one_pow (a : ℤ) : ∀ n, (a + 1) ^ n = binomialSum a n (n + 1)
  | 0 => by
    rw [binomialSum_one]
    ring
  | n + 1 => by
    have h1 : binomialSum a n (n + 1 + 1) = binomialSum a n (n + 1) := by
      rw [binomialSum, Nat.choose_succ_self]
      push_cast
      ring
    rw [binomialSum_succ, h1, ← add_one_pow a n]
    ring

/-- All the terms of the expansion of `(a + 1) ^ p` from `i = 1` to `i = k`, for `k < p`, are
divisible by `p`. -/
theorem dvd_binomialSum_sub_one {p : ℕ} (hp : p.Prime) (a : ℤ) :
    ∀ k, k < p → (p : ℤ) ∣ binomialSum a p (k + 1) - 1
  | 0, _ => by
    rw [binomialSum_one, Int.sub_self]
    exact Int.dvd_zero _
  | k + 1, hk => by
    obtain ⟨c, hc⟩ := prime_dvd_choose hp (Nat.succ_pos k) hk
    have h : (p : ℤ) ∣ (p.choose (k + 1) : ℤ) := ⟨c, by rw [hc]; push_cast; rfl⟩
    have e : binomialSum a p (k + 1 + 1) - 1
        = (binomialSum a p (k + 1) - 1) + (p.choose (k + 1) : ℤ) * a ^ (k + 1) := by
      rw [binomialSum]
      ring
    rw [e]
    exact Int.dvd_add (dvd_binomialSum_sub_one hp a k (Nat.lt_of_succ_lt hk))
      (Int.dvd_trans h (Int.dvd_mul_right _ _))

/-- **The freshman's dream**: `(a + 1) ^ p ≡ a ^ p + 1` modulo `p`. -/
theorem dvd_add_one_pow {p : ℕ} (hp : p.Prime) (a : ℤ) : (p : ℤ) ∣ (a + 1) ^ p - a ^ p - 1 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.two_pos hp.two_le))
  have e : (a + 1) ^ (q + 1) - a ^ (q + 1) - 1 = binomialSum a (q + 1) (q + 1) - 1 := by
    rw [add_one_pow a (q + 1), binomialSum, choose_self]
    push_cast
    ring
  rw [e]
  exact dvd_binomialSum_sub_one hp a q (Nat.lt_succ_self q)

/-- By the freshman's dream, the theorem holds for `x + 1` if and only if it holds for `x`. -/
theorem dvd_succ_iff {p : ℕ} (hp : p.Prime) (x : ℤ) :
    (p : ℤ) ∣ (x + 1) ^ p - (x + 1) ↔ (p : ℤ) ∣ x ^ p - x := by
  have e : (x + 1) ^ p - (x + 1) = ((x + 1) ^ p - x ^ p - 1) + (x ^ p - x) := by ring
  rw [e]
  exact Int.dvd_add_right (dvd_add_one_pow hp x)

theorem dvd_zero_pow {p : ℕ} (hp : p.Prime) : (p : ℤ) ∣ (0 : ℤ) ^ p - 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.two_pos hp.two_le))
  have : (0 : ℤ) ^ (q + 1) - 0 = 0 := by ring
  rw [this]
  exact Int.dvd_zero _

theorem dvd_natCast {p : ℕ} (hp : p.Prime) : ∀ n : ℕ, (p : ℤ) ∣ (n : ℤ) ^ p - n
  | 0 => dvd_zero_pow hp
  | n + 1 => by
    rw [Nat.cast_succ]
    exact (dvd_succ_iff hp n).mpr (dvd_natCast hp n)

theorem dvd_neg_natCast {p : ℕ} (hp : p.Prime) : ∀ n : ℕ, (p : ℤ) ∣ (-(n : ℤ)) ^ p - -(n : ℤ)
  | 0 => by
    have : -((0 : ℕ) : ℤ) = 0 := by
      push_cast
    rw [this]
    exact dvd_zero_pow hp
  | n + 1 => by
    have h := dvd_neg_natCast hp n
    have e : -(n : ℤ) = -((n + 1 : ℕ) : ℤ) + 1 := by
      push_cast
      ring
    rw [e] at h
    exact (dvd_succ_iff hp _).mp h

end FermatLittleTheorem.Constructive

open FermatLittleTheorem.Constructive in
/-- **Fermat's little theorem**, by the binomial theorem and induction on `a` in both directions. -/
theorem FermatLittleTheorem_Constructive : FermatLittleTheorem := fun p a hp => by
  have h : (p : ℤ) ∣ a ^ p - a := by
    rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
    · exact dvd_natCast hp n
    · exact dvd_neg_natCast hp n
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)

/-- info: 'FermatLittleTheorem_Constructive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FermatLittleTheorem_Constructive
