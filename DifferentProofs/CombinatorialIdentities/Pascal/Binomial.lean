module

public import DifferentProofs.CombinatorialIdentities.Defs
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

open Polynomial

/-- **Pascal's rule**, by comparing coefficients in `(1 + X) ^ (n + 1) = (1 + X) * (1 + X) ^ n`.
The binomial theorem identifies the coefficient of `X ^ k` in `(1 + X) ^ n` as `n.choose k`
(`Polynomial.coeff_one_add_X_pow`, which mathlib proves by induction on `n`); multiplying by
`1 + X` shifts a copy of those coefficients by one, so the coefficient of `X ^ (k + 1)` on the
right is `n.choose (k + 1) + n.choose k`, and on the left it is `(n + 1).choose (k + 1)`. -/
theorem PascalIdentity_binomial : PascalIdentity := by
  rw [PascalIdentity]
  intro n k
  calc n.choose k + n.choose (k + 1)
      = ((1 + X) * (1 + X) ^ n).coeff (k + 1) := by
        rw [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
          Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one_add_X_pow]
        simp [Nat.add_comm]
    _ = ((1 + X) ^ (n + 1)).coeff (k + 1) := by rw [pow_succ']
    _ = (n + 1).choose (k + 1) := Polynomial.coeff_one_add_X_pow ℕ (n + 1) (k + 1)
