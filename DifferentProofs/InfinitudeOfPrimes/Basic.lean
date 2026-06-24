module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import DifferentProofs.InfinitudeOfPrimes.Defs

@[expose] public section

theorem InfinitudeOfPrimes_iff_InfinitudeOfPrimes' : InfinitudeOfPrimes ↔ InfinitudeOfPrimes' := by
  simp only [InfinitudeOfPrimes, InfinitudeOfPrimes', Set.infinite_iff_exists_gt,
    Set.mem_setOf_eq, and_comm]

theorem InfinitudeOfPrimes_cong_iff_InfinitudeOfPrimes_cong' {a b : ℕ} :
    InfinitudeOfPrimes_cong a b ↔ InfinitudeOfPrimes_cong' a b := by
  simp only [InfinitudeOfPrimes_cong, InfinitudeOfPrimes_cong', Set.infinite_iff_exists_gt,
    Set.mem_setOf_eq]
  constructor
  · intro h n
    obtain ⟨p, ⟨hp, hcong⟩, hpn⟩ := h n
    exact ⟨p, hp, hcong, hpn⟩
  · intro h n
    obtain ⟨p, hp, hcong, hpn⟩ := h n
    exact ⟨p, ⟨hp, hcong⟩, hpn⟩

theorem InfinitudeOfPrimes_cong_impl_InfinitudeOfPrimes {a b : ℕ} :
    InfinitudeOfPrimes_cong a b → InfinitudeOfPrimes := by
  rw [InfinitudeOfPrimes_cong_iff_InfinitudeOfPrimes_cong',
    InfinitudeOfPrimes_iff_InfinitudeOfPrimes']
  intro h n
  obtain ⟨p, hp, _, hpn⟩ := h n
  exact ⟨p, hp, hpn⟩
