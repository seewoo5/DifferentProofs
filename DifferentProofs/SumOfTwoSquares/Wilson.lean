module

public import DifferentProofs.SumOfTwoSquares.Basic
public import Mathlib.NumberTheory.Wilson

/-!
# Sum of two squares via Wilson's theorem

Wilson's theorem gives `(p-1)! ≡ -1 (mod p)`. Pairing `k` with `p - k` rewrites the factorial as
`(-1)^{(p-1)/2} · ((p-1)/2)!²`. When `p ≡ 1 (mod 4)` the exponent `(p-1)/2` is even, so
`((p-1)/2)!² ≡ -1 (mod p)`, exhibiting `-1` as a square. The shared descent
`sq_add_sq_of_isSquare_neg_one` then yields `p = a² + b²`.
-/

@[expose] public section

open SumOfTwoSquares ZMod in
open scoped Nat in
/-- Fermat's theorem on sums of two squares, via Wilson's theorem: pairing `k` with `p - k` in
`(p-1)! ≡ -1 (mod p)` shows that `((p-1)/2)!` is a square root of `-1` when `p ≡ 1 (mod 4)`. -/
theorem FermatSumOfTwoSquares_Wilson : FermatSumOfTwoSquares := by
  intro p hp hp4
  have : Fact p.Prime := ⟨hp⟩
  -- pairing: `(p-1)! = (-1)^((p-1)/2) · ((p-1)/2)!²`
  have h := factorial_eq_neg_one_pow_mul_half_factorial_sq (p := p) (Nat.odd_iff.mpr (by lia))
  rw [wilsons_lemma, (Nat.even_iff.mpr (by lia : (p - 1) / 2 % 2 = 0)).neg_one_pow, one_mul] at h
  exact sq_add_sq_of_isSquare_neg_one hp ⟨_, h.trans (sq _)⟩
