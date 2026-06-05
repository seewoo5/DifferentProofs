module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import DifferentProofs.InfinitudeOfPrimes.Defs

@[expose] public section

theorem InfinitudeOfPrimes_iff_InfinitudeOfPrimes' : InfinitudeOfPrimes ↔ InfinitudeOfPrimes' := by
  simp only [InfinitudeOfPrimes, InfinitudeOfPrimes', Set.infinite_iff_exists_gt,
    Set.mem_setOf_eq, and_comm]
