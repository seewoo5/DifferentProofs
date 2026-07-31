/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Summing a separated summand over a product of finite sets

`Finset.sum_mul_sum` expands a product of two sums into a double sum. Read backwards over a
product finset it says that a summand which separates into one factor per coordinate sums to the
product of the two one-coordinate sums — the finite Fubini identity `Finset.sum_product_mul`.

This is intended for `Mathlib/Algebra/BigOperators/Ring/Finset.lean`, next to
`Finset.sum_mul_sum`; that file would pick up the import providing `Finset.sum_product'`.
-/

@[expose] public section

namespace Finset

variable {ι κ R : Type*} [NonUnitalNonAssocSemiring R]

/-- Summing `f p.1 * g p.2` over `s ×ˢ t` gives the product of the sum of `f` over `s` and the
sum of `g` over `t`. -/
theorem sum_product_mul (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
    ∑ p ∈ s ×ˢ t, f p.1 * g p.2 = (∑ i ∈ s, f i) * ∑ j ∈ t, g j :=
  (sum_product' ..).trans (sum_mul_sum ..).symm

end Finset
