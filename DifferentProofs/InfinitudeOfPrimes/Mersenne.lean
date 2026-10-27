module

public import DifferentProofs.InfinitudeOfPrimes.Defs
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Infinitude of primes via Mersenne numbers

The proof follows the answer by user9413 at
<https://math.stackexchange.com/a/50020/350772>, which attributes it to Aigner and Ziegler,
*Proofs from the Book*; see also Ribenboim, *The Little Book of Bigger Primes*.

Suppose that `p` is the largest prime and consider the Mersenne number `2 ^ p - 1`. It has a
prime divisor `q`, and `q ∣ 2 ^ p - 1` gives `2 ^ p = 1` in `ZMod q`. Since `2 ≠ 1` in `ZMod q`,
the multiplicative order of `2` is `p`. The unit group of `ZMod q` has `q - 1` elements, so by
Lagrange's theorem `p ∣ q - 1`, hence `p < q`. This contradicts the maximality of `p`.

`lt_of_prime_dvd_mersenne` proves the key step, and `InfinitudeOfPrimes_Mersenne` derives the
infinitude of the primes from it.
-/

@[expose] public section

namespace InfinitudeOfPrimes.Mersenne

/-- If `q` is prime and divides `2 ^ p - 1` for a prime `p`, then `p < q`. -/
lemma lt_of_prime_dvd_mersenne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : q ∣ 2 ^ p - 1) : p < q := by
  have := Fact.mk hp
  have := Fact.mk hq
  have hpow : (2 : ZMod q) ^ p = 1 := by
    simpa only [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      sub_eq_zero] using (ZMod.natCast_eq_zero_iff _ q).2 hdvd
  have horder : orderOf (2 : ZMod q) = p := orderOf_eq_prime hpow (sub_ne_zero.1 (by norm_num))
  have hpq : p ∣ q - 1 :=
    horder ▸ ZMod.orderOf_dvd_card_sub_one (IsUnit.of_pow_eq_one hpow hp.ne_zero).ne_zero
  exact Nat.lt_of_le_sub_one hq.pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hq.one_lt) hpq)

end InfinitudeOfPrimes.Mersenne

open InfinitudeOfPrimes.Mersenne in
/-- **The infinitude of primes**, since every prime divisor of `2 ^ p - 1` is larger than `p`. -/
theorem InfinitudeOfPrimes_Mersenne : InfinitudeOfPrimes := fun hfin ↦ by
  obtain ⟨p, hp, hmax⟩ := Set.exists_max_image _ id hfin ⟨2, Nat.prime_two⟩
  have h2p : 2 < 2 ^ p := hp.two_le.trans_lt Nat.lt_two_pow_self
  obtain ⟨q, hq, hdvd⟩ := Nat.exists_prime_and_dvd (show 2 ^ p - 1 ≠ 1 by lia)
  exact (lt_of_prime_dvd_mersenne hp hq hdvd).not_ge (hmax q hq)
