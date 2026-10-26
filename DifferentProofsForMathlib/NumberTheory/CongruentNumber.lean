/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# `1` is not a congruent number

A positive rational number is a *congruent number* if it is the area of a right triangle whose
sides are all rational (`IsCongruentNumber`). The main result of this file is Fermat's theorem of
1640 that `1` is not a congruent number (`not_isCongruentNumber_one`).

The proof is Fermat's method of descent, as presented in the proof of Theorem 2.1 of Keith
Conrad's notes *The congruent number problem*
(<https://kconrad.math.uconn.edu/blurbs/ugradnumthy/congnumber.pdf>).

* Writing the sides of a rational right triangle of area `1` as `a / d`, `b / d` and `c / d`
  gives natural numbers with `a ^ 2 + b ^ 2 = c ^ 2` and `a * b = 2 * d ^ 2`, where `d ≠ 0`.
* The greatest common divisor `g` of `a` and `b` also divides `c` and `d`, and dividing by it
  gives a solution with `a` and `b` coprime (`no_solution`).
* Then one of `a` and `b` is even, say `a = 2 * k ^ 2` and `b = l ^ 2` with `l` odd. The
  coprime numbers `(c + b) / 2` and `(c - b) / 2` multiply to `k ^ 4`, so they are `r ^ 4` and
  `s ^ 4`, and `l ^ 2 = r ^ 4 - s ^ 4 = (r ^ 2 + s ^ 2) * (r ^ 2 - s ^ 2)` with coprime factors.
  So `r ^ 2 + s ^ 2 = t ^ 2` and `r ^ 2 - s ^ 2 = u ^ 2`, where `u` is odd, and modulo `4` this
  forces `r` to be odd and `s` to be even. Now `((t + u) / 2, (t - u) / 2, r, s / 2)` is another
  coprime solution, and `r < c`. By strong induction on `c` there is no coprime solution
  (`descent`).

Natural-number subtraction truncates, so the formalization names the differences instead:
`c = b + 2 * m`, `r ^ 2 = s ^ 2 + w` and `t = u + 2 * b'`. Conrad gives a separate reason for each
of the three coprimality claims. Here each one is reduced, using `gcd (x + y) y = gcd x y`, to a
pair whose members divide `a ^ 2` and `b` respectively, which are coprime.
-/

@[expose] public section

/-- A positive rational number `n` is a **congruent number** if it is the area of a right triangle
whose sides are all rational. -/
def IsCongruentNumber (n : ℚ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n

/-- Two coprime natural numbers whose product is a `k`-th power are both `k`-th powers. -/
private lemma exists_pow_of_coprime {m n c k : ℕ} (h : m.Coprime n) (hmn : m * n = c ^ k) :
    (∃ r, m = r ^ k) ∧ ∃ s, n = s ^ k :=
  ⟨exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) hmn,
    exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h.symm) ((mul_comm n m).trans hmn)⟩

/-- Even squares are `0` and odd squares are `1` modulo `4`. -/
private lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = n % 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩ <;> lia

/-- If `g ^ 2` divides `2 * d ^ 2`, then `g` divides `d`. -/
private lemma dvd_of_sq_dvd_two_mul_sq {g d : ℕ} (hd : d ≠ 0) (h : g ^ 2 ∣ 2 * d ^ 2) : g ∣ d := by
  obtain ⟨e, g, d, he, hco, rfl, rfl⟩ := Nat.exists_coprime' (by positivity : 0 < Nat.gcd g d)
  rw [mul_pow, mul_pow, ← mul_assoc, Nat.mul_dvd_mul_iff_right (by positivity)] at h
  exact mul_dvd_mul_right (Nat.squarefree_two g (sq g ▸ (hco.pow 2 2).dvd_of_dvd_mul_right h)).dvd e

/-- **Fermat's descent**: there are no natural numbers `a, b, c, d` with `d ≠ 0`, `a` and `b`
coprime, `a ^ 2 + b ^ 2 = c ^ 2` and `a * b = 2 * d ^ 2`. From such a solution the proof builds
another one with a smaller `c`. -/
private theorem descent {a b c d : ℕ} (hd : d ≠ 0) (hab : a.Coprime b)
    (h₁ : a ^ 2 + b ^ 2 = c ^ 2) (h₂ : a * b = 2 * d ^ 2) : False := by
  induction c using Nat.strong_induction_on generalizing a b d with | _ c ih => ?_
  -- one of `a` and `b` is even, say `a`
  wlog ha : 2 ∣ a generalizing a b with H
  · exact H hab.symm (by rwa [add_comm]) (by rwa [mul_comm])
      ((Nat.prime_two.dvd_mul.mp ⟨_, h₂⟩).resolve_left ha)
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (by rw [h₂]; positivity)
  have hlc : b < c := lt_of_pow_lt_pow_left₀ 2 c.zero_le (h₁ ▸ lt_add_of_pos_left _ (by positivity))
  -- `a = 2 * k ^ 2` and `b = l ^ 2`
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨⟨k, rfl⟩, l, rfl⟩ := exists_pow_of_coprime hab.coprime_mul_left (by lia : a * b = d ^ 2)
  -- `c` and `b` have the same parity and `c > b`; write `c = b + 2 * m`, so that
  -- `(c + b) / 2 = b + m` and `(c - b) / 2 = m`, whose product is `k ^ 4`
  have := sq_mod_four c; have := sq_mod_four (l ^ 2)
  obtain ⟨m, rfl⟩ : ∃ m, c = l ^ 2 + 2 * m := ⟨(c - l ^ 2) / 2, by lia⟩
  have hm : (l ^ 2 + m) * m = k ^ 4 := by linarith
  -- these two factors are coprime (`m` divides `a ^ 2`, which is coprime to `b`), so
  -- `(c + b) / 2 = r ^ 4` and `(c - b) / 2 = s ^ 4`
  obtain ⟨⟨r, hr⟩, s, rfl⟩ := exists_pow_of_coprime (Nat.coprime_add_self_left.mpr
    ((hab.pow_left 2).coprime_dvd_left ⟨4 * (l ^ 2 + m), by linarith⟩).symm) hm
  have hrc : r < l ^ 2 + 2 * s ^ 4 := (Nat.le_self_pow four_ne_zero r).trans_lt (by lia)
  -- `l ^ 2 = r ^ 4 - s ^ 4 = (r ^ 2 + s ^ 2) * w` with `w = r ^ 2 - s ^ 2`, and these two
  -- factors are coprime: `2 * s ^ 2` divides `a ^ 2` and `w` divides `b`
  obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le
    ((Nat.pow_le_pow_iff_left two_ne_zero).mp (by lia) : s ^ 2 ≤ r ^ 2)
  have hl2 : (2 * s ^ 2 + w) * w = l ^ 2 := by linear_combination -hr - (r ^ 2 + s ^ 2 + w) * hw
  have hsw : (2 * s ^ 2).Coprime w := ((hab.pow_left 2).coprime_dvd_left
    ⟨2 * s ^ 2 * (l ^ 2 + s ^ 4), by linarith⟩).coprime_dvd_right (Dvd.intro_left _ hl2)
  -- so `r ^ 2 + s ^ 2 = t ^ 2` and `r ^ 2 - s ^ 2 = u ^ 2`
  obtain ⟨⟨t, ht⟩, u, rfl⟩ := exists_pow_of_coprime (Nat.coprime_add_self_left.mpr hsw) hl2
  -- `u` is odd, so modulo `4` `r` is odd and `s` is even, and then `t` is odd
  have := Nat.odd_iff.mp (Nat.coprime_two_left.mp hsw.coprime_mul_right)
  have := sq_mod_four r; have := sq_mod_four s; have := sq_mod_four t; have := sq_mod_four u
  have hut : u ≤ t := (Nat.pow_le_pow_iff_left two_ne_zero).mp (by lia)
  -- the smaller solution `((t + u) / 2, (t - u) / 2, r, s / 2)`, coprime as `u` and `s` are
  obtain ⟨b', rfl⟩ : ∃ b', t = u + 2 * b' := ⟨(t - u) / 2, by lia⟩
  obtain ⟨d', rfl⟩ : ∃ d', s = 2 * d' := ⟨s / 2, by lia⟩
  exact ih r hrc (a := u + b') (b := b') (d := d') (by lia) (Nat.coprime_add_self_left.mpr
    ((hsw.coprime_dvd_left ⟨4 * (u + b'), by linarith⟩).coprime_dvd_right
      (dvd_pow_self u two_ne_zero)).symm) (by linarith) (by linarith)

/-- There are no natural numbers `a, b, c, d` with `d ≠ 0`, `a ^ 2 + b ^ 2 = c ^ 2` and
`a * b = 2 * d ^ 2`: the greatest common divisor of `a` and `b` divides `c` and `d`, and dividing
by it gives such a solution with `a` and `b` coprime, which `descent` rules out. -/
private theorem no_solution {a b c d : ℕ} (hd : d ≠ 0) (h₁ : a ^ 2 + b ^ 2 = c ^ 2)
    (h₂ : a * b = 2 * d ^ 2) : False := by
  have ha : a ≠ 0 := left_ne_zero_of_mul (by rw [h₂]; positivity)
  obtain ⟨g, a, b, hg, hab, rfl, rfl⟩ := Nat.exists_coprime' (by positivity : 0 < Nat.gcd a b)
  obtain ⟨c, rfl⟩ : g ∣ c := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨a ^ 2 + b ^ 2, h₁ ▸ by ring⟩
  obtain ⟨d, rfl⟩ : g ∣ d := dvd_of_sq_dvd_two_mul_sq hd ⟨a * b, h₂ ▸ by ring⟩
  exact descent (c := c) (right_ne_zero_of_mul hd) hab
    (Nat.eq_of_mul_eq_mul_left (pow_pos hg 2) (by linear_combination h₁))
    (Nat.eq_of_mul_eq_mul_left (pow_pos hg 2) (by linear_combination h₂))

/-- A nonnegative rational number times a multiple of its denominator is a natural number. -/
private lemma exists_natCast_eq_mul {x : ℚ} (hx : 0 ≤ x) {n : ℕ} (h : x.den ∣ n) :
    ∃ a : ℕ, (a : ℚ) = x * n := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨x.num.toNat * k, by rw [Nat.cast_mul, Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num,
    ← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx)]⟩

/-- **Fermat's theorem**: `1` is not a congruent number, that is, no right triangle with rational
sides has area `1`. -/
theorem not_isCongruentNumber_one : ¬ IsCongruentNumber 1 := by
  rintro ⟨x, y, z, hx, hy, hz, h₁, h₂⟩
  -- write the sides as `a / d`, `b / d` and `c / d` with natural numbers `a, b, c, d`
  obtain ⟨d, hd, hxd, hyd, hzd⟩ : ∃ d : ℕ, d ≠ 0 ∧ x.den ∣ d ∧ y.den ∣ d ∧ z.den ∣ d :=
    ⟨_, by positivity, ⟨_, mul_assoc _ _ _⟩, (dvd_mul_left _ _).mul_right _, dvd_mul_left _ _⟩
  obtain ⟨a, ha⟩ := exists_natCast_eq_mul hx.le hxd
  obtain ⟨b, hb⟩ := exists_natCast_eq_mul hy.le hyd
  obtain ⟨c, hc⟩ := exists_natCast_eq_mul hz.le hzd
  have h₁' : (a : ℚ) ^ 2 + b ^ 2 = c ^ 2 := by rw [ha, hb, hc]; linear_combination (d : ℚ) ^ 2 * h₁
  have h₂' : (a : ℚ) * b = 2 * d ^ 2 := by rw [ha, hb]; linear_combination 2 * (d : ℚ) ^ 2 * h₂
  exact no_solution hd (mod_cast h₁') (mod_cast h₂')
