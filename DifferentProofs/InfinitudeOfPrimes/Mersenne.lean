module

public import DifferentProofs.InfinitudeOfPrimes.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace InfinitudeOfPrimes.Mersenne

/-- If `q` is prime and divides `2 ^ p - 1` for a prime `p`, then `p < q`. -/
lemma lt_of_prime_dvd_mersenne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : q ∣ 2 ^ p - 1) : p < q := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : 2 ≤ q := hq.two_le
  have h1le : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hpow : (2 : ZMod q) ^ p = 1 := by
    have h : ((2 ^ p : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact (Nat.modEq_iff_dvd' h1le).mpr hdvd |>.symm
    simpa using h
  have h2_ne_zero : (2 : ZMod q) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hpow
    exact zero_ne_one hpow
  have h2_ne_one : (2 : ZMod q) ≠ 1 := by
    intro h
    have h1 : (2 : ZMod q) - 1 = 0 := by rw [h, sub_self]
    norm_num at h1
  have horder : orderOf (2 : ZMod q) = p := orderOf_eq_prime hpow h2_ne_one
  have hpdvd : p ∣ q - 1 := by
    have h := ZMod.orderOf_dvd_card_sub_one (p := q) (a := 2) h2_ne_zero
    rwa [horder] at h
  have hple : p ≤ q - 1 := Nat.le_of_dvd (by lia) hpdvd
  lia

end InfinitudeOfPrimes.Mersenne

open InfinitudeOfPrimes.Mersenne in
/-- The Mersenne-number proof: the largest prime has a larger prime divisor of `2 ^ p - 1`. -/
theorem InfinitudeOfPrimes_Mersenne : InfinitudeOfPrimes := by
  intro hfin
  classical
  let p := hfin.toFinset.max' ⟨2, hfin.mem_toFinset.mpr Nat.prime_two⟩
  have hpprime : p.Prime := hfin.mem_toFinset.mp (Finset.max'_mem _ _)
  have hpmax : ∀ r : ℕ, r.Prime → r ≤ p := fun r hr =>
    Finset.le_max' _ _ (hfin.mem_toFinset.mpr hr)
  have h4 : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hpprime.two_le
  have hMne : 2 ^ p - 1 ≠ 1 := by lia
  obtain ⟨q, hqprime, hq_dvd⟩ := Nat.exists_prime_and_dvd hMne
  exact (lt_of_prime_dvd_mersenne hpprime hqprime hq_dvd).not_ge (hpmax q hqprime)
