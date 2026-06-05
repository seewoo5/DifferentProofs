module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.Set.Finite.Lattice
public import DifferentProofs.InfinitudeOfPrimes.Defs

@[expose] public section


theorem InfinitudeOfPrimes_Euclid : InfinitudeOfPrimes := by
  intro hfin
  obtain ⟨n, hn⟩ := hfin.bddAbove
  have hne : n.factorial + 1 ≠ 1 := by
    intro h; exact Nat.factorial_ne_zero n (by lia)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  exact hp.not_dvd_one <| by
    have hpnfac : p ∣ n.factorial := (Nat.Prime.dvd_factorial hp).2 (hn hp)
    simpa using Nat.dvd_sub hpdvd hpnfac


theorem InfinitudeOfPrimes_Euclid' : InfinitudeOfPrimes := by
  intro hfin
  have hne : hfin.toFinset.prod id + 1 ≠ 1 := by
    have : 0 < hfin.toFinset.prod id := Finset.prod_pos fun i hi ↦ (hfin.mem_toFinset.mp hi).pos
    lia
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpS : p ∣ hfin.toFinset.prod id := Finset.dvd_prod_of_mem id (hfin.mem_toFinset.mpr hp)
  exact hp.not_dvd_one (by simpa using Nat.dvd_sub hpdvd hpS)
