module

public import DifferentProofs.IrrationalSqrtTwo.Defs
public import Mathlib.Tactic.Ring

/-!
# Irrationality of `√2` without `Classical.choice`

This is the constructive proof in the section "Constructive proof" of the Wikipedia article
<https://en.wikipedia.org/wiki/Square_root_of_2#Constructive_proof>, as quoted in the Math
StackExchange question <https://math.stackexchange.com/q/1589603>. For positive integers `a` and
`b`, the `2`-adic valuation of `2 * b ^ 2` is odd and that of `a ^ 2` is even, so
`|2 * b ^ 2 - a ^ 2| ≥ 1`, and then

```
|√2 - a / b| = |2 * b ^ 2 - a ^ 2| / (b ^ 2 * (√2 + a / b))
             ≥ 1 / (b ^ 2 * (√2 + a / b)) ≥ 1 / (3 * b ^ 2).
```

So `√2` is not merely different from every rational: it is apart from it by an explicit amount.

## What is free of `Classical.choice`

The statement `IrrationalSqrtTwo` cannot be, whatever the proof: `Irrational (Real.sqrt 2)` itself
depends on `Classical.choice`, because mathlib's `Real` and `Real.sqrt` do. The argument never needs
`ℝ`, though, only a nonnegative square root of `2` in an ordered field. So:

* `IrrationalSqrtTwoNat_Constructive`, that `p ^ 2 = 2 * q ^ 2` forces `q = 0`, and
  `IrrationalSqrtTwo.Constructive.apart_of_sq_eq_two`, the estimate in a partially ordered field,
  depend only on `propext` and `Quot.sound`. The `#guard_msgs` at the end of this file fail the
  build otherwise, and `comparator/IrrationalSqrtTwoConstructive.json` has Comparator check the
  first of them in CI.
* `IrrationalSqrtTwo.Constructive.one_div_le_abs_sqrt_two_sub` and `IrrationalSqrtTwo_Constructive`
  instantiate the estimate at `K = ℝ` and `s = √2`, and report `Classical.choice` because `ℝ` does.

Avoiding the axiom takes some care. Mathlib's `padicValNat` and `Nat.factorization` depend on it,
which is why `IsTwoAdicVal` is defined below. So do many of its order lemmas, most often through
`lt_or_eq_of_le` on a partial order and the instance `IsStrictOrderedRing.toIsOrderedRing`, which is
why a few of them are proved below from the fields of `IsStrictOrderedRing`. On goals like the ones
in this file, the proofs found by `grind`, `lia`, `linarith`, `nlinarith`, `positivity`, `norm_num`,
`field_simp` and `linear_combination` reach it as well, and those found by `omega`, `ring` and
`push_cast` do not. So `omega` takes the place of the project's usual `lia` below.

## Differences from the source

* The source's case distinction is on the size of `a / b`. The older revision of the article quoted
  in the question compares it to the real number `3 - √2`, a comparison that a constructive proof
  cannot decide in general; the current revision assumes `1 < a / b < 3 / 2`. We split on
  `2 * a ≤ 3 * b`, which is a question about natural numbers, as the lower bound on `a / b` is not
  needed. Since the order on `K` is not assumed to be total or decidable, the absence of
  `Classical.choice` means that the proof cannot split on elements of `K`.
* The source calls the case `3 / 2 < a / b` trivial. Here it is `3 * b + 1 ≤ 2 * a` and `2 * s < 3`,
  which together give `1 / (3 * b ^ 2) < a / b - s` (`apart_of_mul_eq`).
* We clear the denominators in the chain of inequalities (`lt_of_mul_eq_natCast`). Division by
  `√2 + a / b`, which the question asks about, becomes the hypothesis `PosMulReflectLT K` applied to
  the positive element `s + a / b`.
* The inequality comes out strict, since `s + a / b < 3` is. That suits `IsStrictOrderedRing`, whose
  fields multiply `<` but not `≤`.
-/

@[expose] public section

namespace IrrationalSqrtTwo.Constructive

/-! ### The valuations -/

/-- `k` is the `2`-adic valuation of `n`, that is, `n` is `2 ^ k` times an odd number. -/
def IsTwoAdicVal (k n : ℕ) : Prop := ∃ m, n = 2 ^ k * (2 * m + 1)

/-- Every positive integer has a `2`-adic valuation, by repeatedly halving it. -/
theorem exists_isTwoAdicVal (n : ℕ) (hn : 0 < n) : ∃ k, IsTwoAdicVal k n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · obtain ⟨k, m, hm⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨k + 1, m, ?_⟩
      rw [pow_succ', mul_assoc, ← hm]
      omega
    · exact ⟨0, n / 2, by rw [pow_zero, one_mul]; omega⟩

/-- The `2`-adic valuation of a number is unique. -/
theorem IsTwoAdicVal.unique : ∀ {k l n : ℕ}, IsTwoAdicVal k n → IsTwoAdicVal l n → k = l
  | 0, 0, _, _, _ => rfl
  | 0, l + 1, n, ⟨m, hm⟩, ⟨m', hm'⟩ | l + 1, 0, n, ⟨m', hm'⟩, ⟨m, hm⟩ => by
    rw [pow_zero, one_mul] at hm
    rw [pow_succ', mul_assoc] at hm'
    omega
  | k + 1, l + 1, n, ⟨m, hm⟩, ⟨m', hm'⟩ => by
    rw [pow_succ', mul_assoc] at hm hm'
    exact congrArg (· + 1) (IsTwoAdicVal.unique (n := 2 ^ k * (2 * m + 1)) ⟨m, rfl⟩ ⟨m', by omega⟩)

theorem IsTwoAdicVal.two_mul {k n : ℕ} : IsTwoAdicVal k n → IsTwoAdicVal (k + 1) (2 * n)
  | ⟨m, hm⟩ => ⟨m, by rw [hm, pow_succ', mul_assoc]⟩

theorem IsTwoAdicVal.sq {k n : ℕ} : IsTwoAdicVal k n → IsTwoAdicVal (2 * k) (n ^ 2)
  | ⟨m, hm⟩ => ⟨2 * m ^ 2 + 2 * m, by rw [hm]; ring⟩

/-- The valuation of `a ^ 2` is even and that of `2 * b ^ 2` is odd, so they are different. -/
theorem sq_ne_two_mul_sq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : a ^ 2 ≠ 2 * b ^ 2 := fun h => by
  obtain ⟨k, hk⟩ := exists_isTwoAdicVal a ha
  obtain ⟨l, hl⟩ := exists_isTwoAdicVal b hb
  have := hk.sq.unique (h ▸ hl.sq.two_mul)
  omega

/-- `|2 * b ^ 2 - a ^ 2| ≥ 1`, in a form that says which of the two numbers is the larger. -/
theorem exists_sq_eq_add {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (∃ n, 0 < n ∧ 2 * b ^ 2 = a ^ 2 + n) ∨ ∃ n, 0 < n ∧ a ^ 2 = 2 * b ^ 2 + n := by
  rcases Nat.lt_or_gt_of_ne (sq_ne_two_mul_sq ha hb) with h | h
  · exact .inl ⟨2 * b ^ 2 - a ^ 2, by omega, by omega⟩
  · exact .inr ⟨a ^ 2 - 2 * b ^ 2, by omega, by omega⟩

/-- If `3 * b < 2 * a`, then `9 * b ^ 2 + 2 ≤ 6 * a * b`. -/
theorem exists_six_mul_eq {a b : ℕ} (hb : 0 < b) (h : 3 * b < 2 * a) :
    ∃ m, 6 * a * b = 9 * b ^ 2 + 2 + m := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt h
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt hb)
  refine ⟨3 * (b' + 1) * j + 3 * b' + 1, ?_⟩
  have : 6 * a * (b' + 1) = 3 * (b' + 1) * (2 * a) := by ring
  rw [this, hj]
  ring

/-! ### The estimate -/

section Estimate

variable {K : Type*} [Field K]

/-- Unlike `div_mul_cancel₀`, this does not go through `GroupWithZero.toDivisionMonoid`, which
depends on `Classical.choice`. -/
theorem div_mul_cancel {a b : K} (hb : b ≠ 0) : a / b * b = a := by
  rw [DivInvMonoid.div_eq_mul_inv, mul_assoc, mul_comm _ b, DivisionRing.mul_inv_cancel b hb,
    mul_one]

/-- The identity of the source, `(s - x) * (b ^ 2 * (s + x)) = 2 * b ^ 2 - a ^ 2`, for a square root
`s` of `2` and `x = a / b`. -/
theorem sub_mul_eq {s x a b : K} (hs2 : s ^ 2 = 2) (hx : x * b = a) :
    (s - x) * (b ^ 2 * (s + x)) = 2 * b ^ 2 - a ^ 2 :=
  calc (s - x) * (b ^ 2 * (s + x)) = s ^ 2 * b ^ 2 - (x * b) ^ 2 := by ring
    _ = 2 * b ^ 2 - a ^ 2 := by rw [hs2, hx]

variable [PartialOrder K]

/-- We can divide by a positive element. This is the only use of `PosMulReflectLT K`, which takes
the place of the fact that the inverse of a positive element is positive. -/
theorem pos_of_mul_pos [PosMulReflectLT K] {y Q : K} (hQ : 0 < Q) (h : 0 < y * Q) : 0 < y :=
  lt_of_mul_lt_mul_left (a := Q) (by rwa [mul_zero, mul_comm]) hQ.le

variable [IsStrictOrderedRing K]

/-- A field of `IsOrderedAddMonoid`. The instance is spelled out because the one Lean finds by
itself goes through `IsStrictOrderedRing.toIsOrderedRing`, which depends on `Classical.choice`. -/
theorem add_le_add_const {x y : K} (h : x ≤ y) (z : K) : x + z ≤ y + z :=
  @IsOrderedAddMonoid.add_le_add_left K _ _ IsOrderedCancelAddMonoid.toIsOrderedAddMonoid x y h z

theorem add_pos_of_nonneg {x y : K} (hx : 0 ≤ x) (hy : 0 < y) : 0 < x + y := by
  have := add_le_add_const hx y
  rw [zero_add] at this
  exact lt_of_lt_of_le hy this

theorem lt_of_sub_pos {x y : K} (h : 0 < y - x) : x < y := by
  refine lt_of_le_not_ge ?_ fun hyx => h.not_ge ?_
  · have := add_le_add_const h.le x
    rwa [zero_add, sub_add_cancel] at this
  · have := add_le_add_const hyx (-x)
    rwa [← sub_eq_add_neg, add_neg_cancel] at this

theorem zero_lt_one : (0 : K) < 1 :=
  -- Lean would otherwise find this through `CharZero`, which depends on `Classical.choice`
  have : NeZero (1 : K) := @NeZero.one K _ IsStrictOrderedRing.toNontrivial
  lt_of_le_of_ne zero_le_one zero_ne_one

theorem natCast_nonneg (n : ℕ) : (0 : K) ≤ n := by
  induction n with
  | zero => rw [Nat.cast_zero]
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (add_pos_of_nonneg ih zero_lt_one).le

theorem natCast_pos {n : ℕ} (hn : 0 < n) : (0 : K) < n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt hn)
  rw [Nat.cast_succ]
  exact add_pos_of_nonneg (natCast_nonneg m) zero_lt_one

theorem two_pos : (0 : K) < 2 := by
  have := natCast_pos (K := K) (n := 2) (by decide)
  rwa [Nat.cast_ofNat] at this

theorem three_pos : (0 : K) < 3 := by
  have := natCast_pos (K := K) (n := 3) (by decide)
  rwa [Nat.cast_ofNat] at this

variable [PosMulReflectLT K]

/-- The chain of inequalities of the source, with the denominators cleared. If `P = s + a / b` and
`y = n / (b ^ 2 * P)` for a positive integer `n`, and `0 < P < 3`, then
`y ≥ 1 / (b ^ 2 * P) ≥ 1 / (3 * b ^ 2)`. Indeed, for `c = 1 / (3 * b ^ 2)` we have
`(y - c) * (3 * b ^ 2 * P) = 3 * n - P > 0`. -/
theorem lt_of_mul_eq_natCast {y P c b : K} {n : ℕ} (hb : 0 < b) (hP : 0 < P) (hP3 : 0 < 3 - P)
    (hc : c * (3 * b ^ 2) = 1) (hn : 0 < n) (h : y * (b ^ 2 * P) = n) : c < y := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt hn)
  refine lt_of_sub_pos (pos_of_mul_pos (mul_pos (mul_pos three_pos (pow_pos hb 2)) hP) ?_)
  have key : (y - c) * (3 * b ^ 2 * P) = ((3 * m : ℕ) : K) + (3 - P) :=
    calc (y - c) * (3 * b ^ 2 * P) = 3 * (y * (b ^ 2 * P)) - c * (3 * b ^ 2) * P := by ring
      _ = ((3 * m : ℕ) : K) + (3 - P) := by
        rw [h, hc]
        push_cast
        ring
  rw [key]
  exact add_pos_of_nonneg (natCast_nonneg _) hP3

/-- The estimate in terms of `x = a / b` and `c = 1 / (3 * b ^ 2)`. Keeping these as variables means
that `ring` does not have to see a division. -/
theorem apart_of_mul_eq {s x c : K} {a b : ℕ} (hs : 0 ≤ s) (hs2 : s ^ 2 = 2) (ha : 0 < a)
    (hb : 0 < b) (hx : x * b = a) (hc : c * (3 * (b : K) ^ 2) = 1) : c < s - x ∨ c < x - s := by
  have hb' : (0 : K) < b := natCast_pos hb
  have h3b : (0 : K) < 3 * (b : K) ^ 2 := mul_pos three_pos (pow_pos hb' 2)
  -- `s + x` is positive, which is why we can divide by it
  have hP : 0 < s + x :=
    add_pos_of_nonneg hs (pos_of_mul_pos hb' (by rw [hx]; exact natCast_pos ha))
  -- `s < 3 / 2`, as `(3 - 2 * s) * (3 + 2 * s) = 1`
  have h3s : 0 < 3 - 2 * s := by
    refine pos_of_mul_pos (Q := s + (s + 3))
      (add_pos_of_nonneg hs (add_pos_of_nonneg hs three_pos)) ?_
    have : (3 - 2 * s) * (s + (s + 3)) = 9 - 4 * s ^ 2 := by ring
    rw [this, hs2, show (9 : K) - 4 * 2 = 1 by ring]
    exact zero_lt_one
  rcases Nat.lt_or_ge (3 * b) (2 * a) with h | h
  · -- `3 / 2 < a / b`: the case that the source calls trivial
    obtain ⟨m, hm⟩ := exists_six_mul_eq hb h
    -- `exact_mod_cast` would go through `Nat.cast_inj`, whose `CharZero` depends on the axiom
    have hm' : 6 * (a : K) * b = 9 * (b : K) ^ 2 + 2 + m := by
      have := congrArg (Nat.cast (R := K)) hm
      push_cast at this
      exact this
    refine .inr (lt_of_sub_pos (pos_of_mul_pos (mul_pos two_pos h3b) ?_))
    have key : (x - s - c) * (2 * (3 * (b : K) ^ 2)) = m + (3 - 2 * s) * (3 * (b : K) ^ 2) :=
      calc (x - s - c) * (2 * (3 * (b : K) ^ 2))
          = 6 * (x * b) * b - 6 * s * (b : K) ^ 2 - 2 * (c * (3 * (b : K) ^ 2)) := by ring
        _ = m + (3 - 2 * s) * (3 * (b : K) ^ 2) := by
          rw [hx, hc, hm']
          ring
    rw [key]
    exact add_pos_of_nonneg (natCast_nonneg m) (mul_pos h3s h3b)
  · -- `a / b ≤ 3 / 2`, so that `s + a / b < 3`
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le h
    have hj' : 3 * (b : K) = 2 * a + j := by
      have := congrArg (Nat.cast (R := K)) hj
      push_cast at this
      exact this
    have hP3 : 0 < 3 - (s + x) := by
      refine pos_of_mul_pos (mul_pos two_pos hb') ?_
      have key : (3 - (s + x)) * (2 * (b : K)) = j + (3 - 2 * s) * b :=
        calc (3 - (s + x)) * (2 * (b : K)) = (3 - 2 * s) * b + (3 * b - 2 * (x * b)) := by ring
          _ = j + (3 - 2 * s) * b := by
            rw [hx, hj']
            ring
      rw [key]
      exact add_pos_of_nonneg (natCast_nonneg j) (mul_pos h3s hb')
    rcases exists_sq_eq_add ha hb with ⟨n, hn, h⟩ | ⟨n, hn, h⟩
    · have h' : 2 * (b : K) ^ 2 = (a : K) ^ 2 + n := by
        have := congrArg (Nat.cast (R := K)) h
        push_cast at this
        exact this
      refine .inl (lt_of_mul_eq_natCast hb' hP hP3 hc hn ?_)
      rw [sub_mul_eq hs2 hx, h']
      ring
    · have h' : (a : K) ^ 2 = 2 * (b : K) ^ 2 + n := by
        have := congrArg (Nat.cast (R := K)) h
        push_cast at this
        exact this
      refine .inr (lt_of_mul_eq_natCast hb' hP hP3 hc hn ?_)
      have : (x - s) * ((b : K) ^ 2 * (s + x)) = -((s - x) * ((b : K) ^ 2 * (s + x))) := by ring
      rw [this, sub_mul_eq hs2 hx, h']
      ring

/-- **Quantitative apartness of `√2` from every positive rational, without `Classical.choice`.** Let
`K` be a partially ordered field in which we can divide by positive elements, and let `s` be a
nonnegative square root of `2` in `K`. Then every `a / b` with `a` and `b` positive integers is
at distance more than `1 / (3 * b ^ 2)` from `s`, on a side determined by `a` and `b`.

The order on `K` need not be total or decidable, so this is stated as a disjunction rather than with
an absolute value. Its proof splits only on natural numbers. -/
theorem apart_of_sq_eq_two {s : K} (hs : 0 ≤ s) (hs2 : s ^ 2 = 2) {a b : ℕ} (ha : 0 < a)
    (hb : 0 < b) : 1 / (3 * (b : K) ^ 2) < s - a / b ∨ 1 / (3 * (b : K) ^ 2) < a / b - s :=
  apart_of_mul_eq hs hs2 ha hb (div_mul_cancel (natCast_pos hb).ne')
    (div_mul_cancel (mul_pos three_pos (pow_pos (natCast_pos hb) 2)).ne')

end Estimate

/-! ### The real numbers -/

/-- The estimate of the source, `|√2 - a / b| ≥ 1 / (3 * b ^ 2)`. -/
theorem one_div_le_abs_sqrt_two_sub {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    1 / (3 * (b : ℝ) ^ 2) ≤ |√2 - a / b| := by
  rcases apart_of_sq_eq_two (Real.sqrt_nonneg 2) (Real.sq_sqrt zero_le_two) ha hb with h | h
  · exact h.le.trans (le_abs_self _)
  · rw [abs_sub_comm]
    exact h.le.trans (le_abs_self _)

end IrrationalSqrtTwo.Constructive

open IrrationalSqrtTwo.Constructive in
/-- **The irrationality of `√2`**, in the natural-number form, from the parity of the `2`-adic
valuations alone. This depends only on `propext` and `Quot.sound`. -/
theorem IrrationalSqrtTwoNat_Constructive : IrrationalSqrtTwoNat := fun p q h => by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · exact hq
  · rcases Nat.eq_zero_or_pos p with rfl | hp
    · have := Nat.pow_pos (n := 2) hq
      omega
    · exact absurd h (sq_ne_two_mul_sq hp hq)

open IrrationalSqrtTwo.Constructive in
/-- **The irrationality of `√2`**: a positive rational `a / b` is at distance at least
`1 / (3 * b ^ 2)` from `√2`, so it is not `√2`. This depends on `Classical.choice`, since the
statement `IrrationalSqrtTwo` does. -/
theorem IrrationalSqrtTwo_Constructive : IrrationalSqrtTwo := by
  rintro ⟨r, hr⟩
  have hr0 : 0 < r := by exact_mod_cast hr ▸ Real.sqrt_pos.mpr zero_lt_two
  have hnum : 0 < r.num := Rat.num_pos.mpr hr0
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hnum.le
  have hab : √2 = a / r.den := by
    rw [← hr, Rat.cast_def, ha, Int.cast_natCast]
  have := one_div_le_abs_sqrt_two_sub (a := a) (by omega) r.den_pos
  rw [hab, sub_self, abs_zero] at this
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  exact absurd this (not_le.mpr (by positivity))

/-! ### The axioms -/

/-- info: 'IrrationalSqrtTwoNat_Constructive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms IrrationalSqrtTwoNat_Constructive

/--
info: 'IrrationalSqrtTwo.Constructive.apart_of_sq_eq_two' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms IrrationalSqrtTwo.Constructive.apart_of_sq_eq_two
