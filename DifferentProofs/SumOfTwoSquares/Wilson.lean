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

open SumOfTwoSquares Finset in
open scoped Nat in
/-- Fermat's theorem on sums of two squares, via Wilson's theorem: pairing `k` with `p - k` in
`(p-1)! ≡ -1 (mod p)` shows that `(p/2)!` is a square root of `-1` when `p ≡ 1 (mod 4)`. -/
theorem FermatSumOfTwoSquares_Wilson : FermatSumOfTwoSquares := by
  intro p hp hp4
  have : Fact p.Prime := ⟨hp⟩
  set w := p / 2 with hw -- w = (p - 1) / 2
  refine sq_add_sq_of_isSquare_neg_one hp ⟨(w ! : ZMod p), ?_⟩
  have hfac : ∀ j ∈ Ico 1 (w + 1), ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := fun j hj ↦ by
    rw [Nat.cast_sub ((mem_Ico.mp hj).2.le.trans (by lia)), ZMod.natCast_self, zero_sub]
  have hB : ∏ k ∈ Ico (w + 1) p, (k : ZMod p) = (-1) ^ w * (w ! : ZMod p) := by
    rw [(by congr 1; lia : Ico (w + 1) p = Ico (p + 1 - (w + 1)) (p + 1 - 1)),
      ← prod_Ico_reflect (fun j ↦ (j : ZMod p)) 1 (by lia : w + 1 ≤ p + 1),
      prod_congr rfl hfac, prod_neg, Nat.card_Ico, Nat.add_sub_cancel,
      ← prod_natCast, prod_Ico_id_eq_factorial]
  rw [← ZMod.prod_Ico_one_prime p,
    ← prod_Ico_consecutive (fun k ↦ (k : ZMod p)) (by lia : 1 ≤ w + 1) (by lia : w + 1 ≤ p),
    ← prod_natCast, prod_Ico_id_eq_factorial, hB,
    (Nat.even_iff.mpr (by lia : w % 2 = 0)).neg_one_pow, one_mul]
