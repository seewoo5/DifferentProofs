module

public import DifferentProofs.IrrationalSqrtTwo.Basic
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

lemma IrrationalSqrtTwoNat_Descent : IrrationalSqrtTwoNat := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro q hpq
    rcases Nat.eq_zero_or_pos q with hq | hq
    · exact hq
    obtain ⟨r, rfl⟩ : 2 ∣ p :=
      Nat.prime_two.dvd_of_dvd_pow (hpq ▸ Dvd.intro _ rfl)
    have hqr : q ^ 2 = 2 * r ^ 2 := by ring_nf at hpq ⊢; lia
    have hlt : q < 2 * r := (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _)
      two_ne_zero).mp (by have := pow_pos hq 2; lia)
    simpa [ih q hlt r hqr] using hqr

theorem IrrationalSqrtTwo_Descent : IrrationalSqrtTwo :=
  IrrationalSqrtTwoNat_impl_IrrationalSqrtTwo IrrationalSqrtTwoNat_Descent
