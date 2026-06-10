module

public import DifferentProofs.IrrationalSqrtTwo.Basic
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

lemma IrrationalSqrtTwoNat_Valuation : IrrationalSqrtTwoNat := by
  intro p q hpq
  by_contra hq
  have := congrArg (fun n => n.factorization 2) hpq
  simp [Nat.factorization_mul two_ne_zero (pow_ne_zero 2 hq), Nat.factorization_pow,
    Nat.Prime.factorization_self Nat.prime_two] at this
  lia

theorem IrrationalSqrtTwo_Valuation : IrrationalSqrtTwo :=
  IrrationalSqrtTwoNat_impl_IrrationalSqrtTwo IrrationalSqrtTwoNat_Valuation
