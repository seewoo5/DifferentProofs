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

open Finset in
open scoped Nat in
theorem FermatSumOfTwoSquares_Wilson : FermatSumOfTwoSquares := by
  intro p hp hp4
  haveI : Fact p.Prime := ⟨hp⟩
  refine sq_add_sq_of_isSquare_neg_one hp ?_
  -- Let `w = (p-1)/2 = p/2`. We show `(w! : ZMod p)² = -1`.
  set w := p / 2 with hw
  have hwp : w + 1 ≤ p := by omega
  -- Part A: `∏_{k=1}^{w} k = w!`.
  have hA : ∏ k ∈ Ico 1 (w + 1), (k : ZMod p) = (w ! : ZMod p) := by
    rw [← Finset.prod_natCast, Finset.prod_Ico_id_eq_factorial]
  -- Part B: `∏_{k=w+1}^{p-1} k ≡ (-1)^w · w!`, by reflecting `k ↦ p - k`.
  have hB : ∏ k ∈ Ico (w + 1) p, (k : ZMod p) = (-1) ^ w * (w ! : ZMod p) := by
    have hset : Ico (w + 1) p = Ico (p - 1 + 1 - w) (p - 1 + 1 - 0) := by
      congr 1 <;> omega
    rw [hset, ← Finset.prod_Ico_reflect (fun j => ((j : ℕ) : ZMod p)) 0 (by omega : w ≤ p - 1 + 1)]
    -- goal: `∏_{j ∈ Ico 0 w} ↑(p-1-j) = (-1)^w · w!`
    have hfac : ∀ j ∈ Ico 0 w, ((p - 1 - j : ℕ) : ZMod p) = (-1) * ((j + 1 : ℕ) : ZMod p) := by
      intro j hj
      rw [mem_Ico] at hj
      rw [(by omega : p - 1 - j = p - (j + 1)), Nat.cast_sub (by omega), ZMod.natCast_self]
      ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico,
      Nat.sub_zero, ← Finset.range_eq_Ico, ← Finset.prod_natCast,
      Finset.prod_range_add_one_eq_factorial]
  -- Combine via Wilson: `∏_{k=1}^{p-1} k = -1`.
  have hprod := ZMod.prod_Ico_one_prime p
  rw [← Finset.prod_Ico_consecutive (fun k => ((k : ℕ) : ZMod p)) (by omega : 1 ≤ w + 1) hwp,
    hA, hB] at hprod
  -- `p ≡ 1 mod 4` makes `w` even, so `(-1)^w = 1`.
  have hwe : Even w := Nat.even_iff.mpr (by omega)
  rw [hwe.neg_one_pow, one_mul] at hprod
  exact ⟨(w ! : ZMod p), hprod.symm⟩
