module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import DifferentProofs.InfinitudeOfPrimes.Basic
public import DifferentProofs.InfinitudeOfPrimes.Defs

@[expose] public section

theorem InfinitudeOfPrimes_cong_one_four : InfinitudeOfPrimes_cong 1 4 := by
  sorry

theorem InfinitudeOfPrimes_from_one_four : InfinitudeOfPrimes := by
  exact InfinitudeOfPrimes_cong_impl_InfinitudeOfPrimes (InfinitudeOfPrimes_cong_one_four)

theorem InfinitudeOfPrimes_cong_three_four : InfinitudeOfPrimes_cong 3 4 := by
  sorry

theorem InfinitudeOfPrimes_from_three_four : InfinitudeOfPrimes := by
  exact InfinitudeOfPrimes_cong_impl_InfinitudeOfPrimes (InfinitudeOfPrimes_cong_three_four)
