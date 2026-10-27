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
  have h1le : 1 ≤ 2 ^ p := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero p two_ne_zero)
  have hodd : Odd (2 ^ p - 1) := by
    have hEven : Even (2 ^ p) := Even.pow_of_ne_zero (by norm_num : Even (2 : ℕ)) hp.ne_zero
    exact Nat.Even.sub_odd h1le hEven (by norm_num : Odd (1 : ℕ))
  have hq_ne_two : q ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdvd)
  have hq_not_dvd_two : ¬ q ∣ 2 := by
    intro hqdvd
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hqdvd
    omega
  have h2_ne_zero : ((2 : ℕ) : ZMod q) ≠ 0 := by
    intro h
    exact hq_not_dvd_two ((ZMod.natCast_eq_zero_iff 2 q).mp h)
  have hpow : ((2 : ℕ) : ZMod q) ^ p = 1 := by
    have h1 : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hdvd
    rw [Nat.cast_sub h1le, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, sub_eq_zero] at h1
    exact h1
  have h2_ne_one : ((2 : ℕ) : ZMod q) ≠ 1 := by
    intro h
    have h' : ((2 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by simpa using h
    have hmod : (2 : ℕ) ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff 2 1 q).mp h'
    have hq_dvd_one : q ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp hmod.symm
    exact hq.not_dvd_one hq_dvd_one
  have horder : orderOf ((2 : ℕ) : ZMod q) = p := orderOf_eq_prime hpow h2_ne_one
  have hpdvd : p ∣ q - 1 := by
    have h := ZMod.orderOf_dvd_card_sub_one (p := q) (a := ((2 : ℕ) : ZMod q)) h2_ne_zero
    rwa [horder] at h
  have hq1 : 0 < q - 1 := by omega
  have hple : p ≤ q - 1 := Nat.le_of_dvd hq1 hpdvd
  omega

end InfinitudeOfPrimes.Mersenne

open InfinitudeOfPrimes.Mersenne in
/-- The Mersenne-number proof: the largest prime has a larger prime divisor of `2 ^ p - 1`. -/
theorem InfinitudeOfPrimes_Mersenne : InfinitudeOfPrimes := by
  intro hfin
  classical
  have h2mem : (2 : ℕ) ∈ hfin.toFinset := hfin.mem_toFinset.mpr Nat.prime_two
  set p := hfin.toFinset.max' ⟨2, h2mem⟩ with hp_def
  have hp_mem : p ∈ hfin.toFinset := Finset.max'_mem _ _
  have hpprime : p.Prime := hfin.mem_toFinset.mp hp_mem
  have hpmax : ∀ r : ℕ, r.Prime → r ≤ p := by
    intro r hr
    exact Finset.le_max' _ _ (hfin.mem_toFinset.mpr hr)
  have hp2 : 2 ≤ p := hpprime.two_le
  have h4 : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
  have hMne : 2 ^ p - 1 ≠ 1 := by omega
  obtain ⟨q, hqprime, hq_dvd⟩ := Nat.exists_prime_and_dvd hMne
  have hpq : p < q := lt_of_prime_dvd_mersenne hpprime hqprime hq_dvd
  exact absurd (hpmax q hqprime) (by omega)
