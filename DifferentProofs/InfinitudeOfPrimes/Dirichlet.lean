module

public import DifferentProofs.InfinitudeOfPrimes.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic

@[expose] public section

/-- **Infinitely many primes are congruent to `1` mod `4`**, because `-1` is a square modulo every
prime factor of `4 * M ^ 2 + 1`. -/
theorem InfinitudeOfPrimes_cong_one_four : InfinitudeOfPrimes_cong 1 4 := by
  intro hfin
  set M := hfin.toFinset.prod id
  have hM : 0 < M ^ 2 := pow_pos (Finset.prod_pos fun q hq ↦ (hfin.mem_toFinset.mp hq).1.pos) 2
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := 4 * M ^ 2 + 1) (by lia)
  have : Fact p.Prime := ⟨hp⟩
  have hpmod : p ≡ 1 [MOD 4] := by
    have h0 := (ZMod.natCast_eq_zero_iff (4 * M ^ 2 + 1) p).mpr hpdvd
    push_cast at h0
    have h4 : p % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp ⟨2 * M, by linear_combination -h0⟩
    unfold Nat.ModEq
    rcases hp.eq_two_or_odd with rfl | h2 <;> lia
  have hpM : p ∣ M := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr ⟨hp, hpmod⟩)
  exact hp.not_dvd_one <| (Nat.dvd_add_right ((hpM.pow two_ne_zero).mul_left 4)).mp hpdvd

theorem InfinitudeOfPrimes_from_one_four : InfinitudeOfPrimes :=
  InfinitudeOfPrimes_cong_impl_InfinitudeOfPrimes InfinitudeOfPrimes_cong_one_four

namespace InfinitudeOfPrimes.Dirichlet

/-- A natural number congruent to `3` mod `4` has a prime factor congruent to `3` mod `4`: it is
odd, and a product of primes that are all `1` mod `4` is again `1` mod `4`. -/
lemma nat_three_mod_four_div_of_prime_three_mod_four (n : ℕ) (hn : n ≡ 3 [MOD 4]) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 3 [MOD 4] ∧ p ∣ n := by
  unfold Nat.ModEq at hn ⊢
  induction n using induction_on_primes with
  | zero => lia
  | one => lia
  | prime_mul p a hp ih =>
    rcases eq_or_ne (p % 4) 3 with h3 | h3
    · exact ⟨p, hp, h3, dvd_mul_right p a⟩
    · have hp4 : p % 4 = 1 := by rcases hp.eq_two_or_odd with rfl | h2 <;> lia
      rw [Nat.mul_mod, hp4, one_mul] at hn
      obtain ⟨q, hq, hq3, hqd⟩ := ih (by lia)
      exact ⟨q, hq, hq3, hqd.mul_left p⟩

end InfinitudeOfPrimes.Dirichlet

open InfinitudeOfPrimes.Dirichlet in
/-- **Infinitely many primes are congruent to `3` mod `4`**, because `4 * M - 1` is congruent to
`3` mod `4` and so has a prime factor congruent to `3` mod `4`. -/
theorem InfinitudeOfPrimes_cong_three_four : InfinitudeOfPrimes_cong 3 4 := by
  intro hfin
  set M := hfin.toFinset.prod id
  have hM : 0 < M := Finset.prod_pos fun q hq ↦ (hfin.mem_toFinset.mp hq).1.pos
  obtain ⟨p, hp, hpmod, hpdvd⟩ :=
    nat_three_mod_four_div_of_prime_three_mod_four (4 * M - 1) (by unfold Nat.ModEq; lia)
  have hpM : p ∣ M := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr ⟨hp, hpmod⟩)
  refine hp.not_dvd_one <| (Nat.dvd_add_right hpdvd).mp ?_
  rw [Nat.sub_add_cancel (by lia)]
  exact hpM.mul_left 4

theorem InfinitudeOfPrimes_from_three_four : InfinitudeOfPrimes :=
  InfinitudeOfPrimes_cong_impl_InfinitudeOfPrimes InfinitudeOfPrimes_cong_three_four
